/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module

public meta import Mathlib.Tactic.Linter.Lint

/-!
# Operator-fidelity linter

This file provides a declaration-aware audit for dependencies on retired operators.  The audit
normalizes aliases and projection-selected instance operations, but does not reject an imported
constant merely because its implementation graph contains a forbidden operator.

Statement and non-proof data dependencies are actionable.  Proof dependencies are collected
separately, together with the ownership of the declaration containing the proof, so a migration can
distinguish removable project proofs from unavoidable official-toolchain internals.
-/

public meta section

open Lean Meta Batteries.Tactic.Lint
open Lean Elab Command

namespace Mathlib.Linter.OperatorFidelity

universe u

/-- The part of a declaration in which an operator dependency occurs. -/
public inductive DependencyKind
  | statement
  | data
  | proof
  deriving BEq, DecidableEq, Inhabited, Repr

/-- Source ownership used when reporting proof dependencies. -/
public inductive SourceOwnership
  | project
  | generatedProject
  | officialToolchain
  | external
  deriving BEq, DecidableEq, Inhabited, Repr

/-- A forbidden root reached from a proof, with the ownership of the declaration being audited. -/
public structure ProofUse where
  /-- The name of the retired operator reached from the proof. -/
  root : Name
  /-- The source ownership associated with this proof dependency. -/
  ownership : SourceOwnership
  deriving BEq, DecidableEq, Inhabited, Repr

/-- Semantic operator dependencies found in one declaration. -/
public structure AuditResult where
  /-- Retired operators reached in the declaration statement or a predicate body. -/
  statementRoots : Array Name := #[]
  /-- Retired operators reached in non-proof declaration values. -/
  dataRoots : Array Name := #[]
  /-- Retired operators reached from proofs, with their source ownership. -/
  proofUses : Array ProofUse := #[]
  /-- Whether exhausted resources, failed reduction, or unavailable declarations prevented a full
  traversal. -/
  incomplete : Bool := false
  /-- The first recorded reason for an incomplete traversal, if available. -/
  incompleteReason : Option String := none
  /-- Callees already visited during the proof-dependency traversal. -/
  visitedConstants : NameSet := {}
  /-- Constants certified to have no path to a retired operator under the current coverage rules. -/
  graphAbsent : NameSet := {}
  /-- Declarations scheduled for their own proof checks in this audit scope. -/
  coveredProofs : NameSet := {}
  /-- Constant names reached by the scan whose declarations were unavailable. -/
  unavailableConstants : NameSet := {}
  deriving Inhabited

/-- Whether the declaration has a statement or non-proof data dependency on a retired operator. -/
public def AuditResult.hasActionableFinding (result : AuditResult) : Bool :=
  result.incomplete || !result.statementRoots.isEmpty || !result.dataRoots.isEmpty

/-- Core rational operations whose invalid-domain behavior is retired by the inverse migration. -/
public def forbiddenRoots : Array Name := #[
  ``Rat.inv,
  ``Rat.div,
  ``Rat.zpow,
  ``mkRat,
  ``Rat.divInt
]

/--
Verified semantic boundaries that must not be unfolded while normalizing operator applications.

The list is intentionally narrow.  In particular, generic `Inv.inv` is absent because inversion of
groups and units is lawful; projection reduction determines whether a concrete use selects a
retired rational inverse.
-/
public def lawfulBoundaries : Array Name := #[
  ``Rat.normalize,
  ``Rat.ofInt,
  ``Rat.add,
  ``Rat.sub,
  ``Rat.neg,
  ``Rat.mul,
  ``Rat.pow
]

private def pushNew {α : Type u} [BEq α] (xs : Array α) (x : α) : Array α :=
  if xs.contains x then xs else xs.push x

private def moduleOwnership (env : Environment) (declName : Name) : SourceOwnership :=
  let isGenerated := env.isAutoDecl declName
  match env.getModuleIdxFor? declName with
  | none => if isGenerated then .generatedProject else .project
  | some moduleIdx =>
      let moduleName := env.header.moduleNames[moduleIdx]!
      if #[`Init, `Lean, `Std].any (·.isPrefixOf moduleName) then
        .officialToolchain
      else if #[`Mathlib, `MathlibTest, `Archive, `Counterexamples, `Wanted].any
          (·.isPrefixOf moduleName) then
        if isGenerated then .generatedProject else .project
      else
        .external

private def addRoot (kind : DependencyKind) (root : Name) (ownership : SourceOwnership) :
    StateT AuditResult MetaM Unit :=
  modify fun result => match kind with
    | .statement => { result with statementRoots := pushNew result.statementRoots root }
    | .data => { result with dataRoots := pushNew result.dataRoots root }
    | .proof =>
        { result with proofUses := pushNew result.proofUses { root, ownership } }

private def isPredicateType (type : Expr) : MetaM Bool :=
  forallTelescope type fun _ body => do
    -- The codomain of a proposition or predicate *definition* is `Prop` itself.  Do not WHNF an
    -- arbitrary proposition here: unfolding `True`, for example, would misclassify a definition
    -- whose value is a proof of `True` as the definition of a proposition.
    return body.consumeMData == .sort .zero

private def isProofType (type : Expr) : MetaM Bool := do
  return (← whnf (← inferType type)).consumeMData == .sort .zero

private def isTheorem (env : Environment) (name : Name) : Bool :=
  env.find? name |>.any fun
    | .thmInfo _ => true
    | _ => false

private def reduceProjectionCore? (expr : Expr) : MetaM (Option Expr) := do
  let .const name _ := expr.getAppFn | return none
  let some info ← getProjectionFnInfo? name | return none
  let args := expr.getAppArgs
  let some structureArg := args[info.numParams]? | return none
  unless structureArg.getAppFn.isConstOf info.ctorName do return none
  let fields := structureArg.getAppArgs
  let index := info.numParams + info.i
  let some selected := fields[index]? | return none
  return some selected

private def expressionConstants (expr : Expr) : NameSet :=
  expr.getUsedConstantsAsSet

private def expressionMayReachForbidden (expr : Expr) : StateT AuditResult MetaM Bool := do
  let env ← getEnv
  let mut pending := #[]
  for name in expressionConstants expr do pending := pending.push name
  let mut seen : NameSet := {}
  let mut budget := 100000
  let mut complete : Bool := true
  while let some name := pending.back? do
    pending := pending.pop
    if forbiddenRoots.contains name then return true
    if lawfulBoundaries.contains name || seen.contains name || (← get).graphAbsent.contains name then
      continue
    if budget == 0 then
      modify fun result => { result with
        incomplete := true
        incompleteReason := result.incompleteReason <|> some "constant budget exhausted" }
      return false
    budget := budget - 1
    seen := seen.insert name
    let some info := env.find? name | do
      complete := false
      modify fun result => { result with
        incomplete := true
        unavailableConstants := result.unavailableConstants.insert name }
      continue
    for dependency in expressionConstants info.type do pending := pending.push dependency
    let covered := (← get).coveredProofs.contains name
    let checkValue : Bool := match info with
      | .thmInfo _ =>
        let owner := moduleOwnership env name
        !covered && (owner == .project || owner == .generatedProject)
      | _ => true
    if checkValue then
      if let some value := info.value? (allowOpaque := true) then
        for dependency in expressionConstants value do pending := pending.push dependency
  if complete then
    let mut absent := (← get).graphAbsent
    for name in seen do absent := absent.insert name
    modify fun result => { result with graphAbsent := absent }
  return false

private partial def auditExpr (ownership : SourceOwnership) (kind : DependencyKind)
    (expr : Expr) (fuel : Nat := 128) : StateT AuditResult MetaM Unit := do
  let expr := expr.consumeMData
  -- A free variable can stand for a local let value with additional dependencies.
  if !expr.hasFVar && !expr.hasMVar then
    unless ← expressionMayReachForbidden expr do return
  if fuel == 0 then
    modify fun result => { result with
      incomplete := true
      incompleteReason := result.incompleteReason <|> some "expression depth exhausted" }
    return
  let kind ← if kind == .data then
      try
        if ← liftM <| isProof expr then
          auditExpr ownership .proof (← liftM <| inferType expr) (fuel - 1)
          pure .proof
        else
          pure kind
      catch _ => pure kind
    else
      pure kind
  let typeKind := if kind == .proof then DependencyKind.proof else .statement
  match expr with
  | .forallE name domain body binderInfo =>
      auditExpr ownership typeKind domain (fuel - 1)
      let state ← get
      let (_, state) ← liftM <| withLocalDecl name binderInfo domain fun localVar =>
        (auditExpr ownership kind (body.instantiate1 localVar) (fuel - 1)).run state
      set state
  | .lam name domain body binderInfo =>
      auditExpr ownership typeKind domain (fuel - 1)
      let state ← get
      let (_, state) ← liftM <| withLocalDecl name binderInfo domain fun localVar =>
        (auditExpr ownership kind (body.instantiate1 localVar) (fuel - 1)).run state
      set state
  | .letE name type value body nonDep =>
      auditExpr ownership typeKind type (fuel - 1)
      auditExpr ownership kind value (fuel - 1)
      let state ← get
      let (_, state) ← liftM <| withLetDecl name type value (nondep := nonDep) fun localVar =>
        (auditExpr ownership kind (body.instantiate1 localVar) (fuel - 1)).run state
      set state
  | _ =>
      let function := expr.getAppFn
      let arguments := expr.getAppArgs
      let env ← getEnv
      let projectionInfo? := function.constName?.bind env.getProjectionFnInfo?
      let visibleArguments := match projectionInfo? with
        | none => arguments
        | some info =>
            -- Do not audit the bundled structure argument. Reducing the projection below exposes
            -- only the selected field, while later arguments remain genuine inputs to that field.
            arguments.extract 0 info.numParams ++
              arguments.extract (info.numParams + 1) arguments.size
      if let some name := function.constName? then
        if forbiddenRoots.contains name then
          addRoot kind name ownership
          for argument in visibleArguments do
            auditExpr ownership kind argument (fuel - 1)
          return
        if lawfulBoundaries.contains name then
          for argument in visibleArguments do
            auditExpr ownership kind argument (fuel - 1)
          return
        -- Projection heads must first reduce against the selected instance.  Treating `Inv.inv`
        -- itself as an ordinary proof callee would skip that reduction and hide `Rat.inv`.
        if projectionInfo?.isNone && (kind == .proof || isTheorem env name) then
          let state ← get
          let seen := state.visitedConstants.contains name || state.graphAbsent.contains name
          unless seen do
            modify fun result =>
              { result with visitedConstants := result.visitedConstants.insert name }
          if !seen then
            if let some info := env.find? name then
              let calleeOwnership := moduleOwnership env name
              if ← expressionMayReachForbidden info.type then
                auditExpr calleeOwnership .proof info.type (fuel - 1)
              let covered := isTheorem env name && (← get).coveredProofs.contains name
              if !covered &&
                  (calleeOwnership == .project || calleeOwnership == .generatedProject) then
                if let some value := info.value? (allowOpaque := true) then
                  if ← expressionMayReachForbidden value then
                    auditExpr calleeOwnership .proof value (fuel - 1)
          for argument in visibleArguments do
            auditExpr ownership kind argument (fuel - 1)
          return
      -- Inspect arguments before reduction: beta/iota reduction may erase proof arguments whose
      -- dependencies still belong in the ownership report.
      for argument in visibleArguments do
        auditExpr ownership kind argument (fuel - 1)
      -- The arguments above account for dependencies passed to a root-free constant.
      if projectionInfo?.isNone && function.isConst then
        unless ← expressionMayReachForbidden function do return
      let normalized ← try
          liftM <| (match projectionInfo? with
            | some info => do
                match arguments[info.numParams]? with
                | none => pure expr
                | some structureArg =>
                  let unfoldedStructure ← (do
                    let structureFn := structureArg.getAppFn
                    if let some structureName := structureFn.constName? then
                      if let some structureInfo := env.find? structureName then
                        if structureInfo.hasValue (allowOpaque := true) then do
                          let value ← instantiateValueLevelParams structureInfo
                            structureFn.constLevels! (allowOpaque := true)
                          pure <| mkAppN value structureArg.getAppArgs
                        else
                          withTransparency .instances <| whnf structureArg
                      else
                        pure structureArg
                    else
                      withTransparency .instances <| whnf structureArg : MetaM Expr)
                  let projectionCore := mkAppN function <|
                    (arguments.extract 0 info.numParams).push unfoldedStructure
                  match ← reduceProjectionCore? projectionCore with
                  | some selected =>
                      pure <| mkAppN selected <|
                        arguments.extract (info.numParams + 1) arguments.size
                  | none => pure expr
            | none =>
                if let some name := function.constName? then
                  if let some info := env.find? name then
                    if info.hasValue (allowOpaque := true) then do
                      let value ← instantiateValueLevelParams info function.constLevels!
                        (allowOpaque := true)
                      pure <| mkAppN value arguments
                    else
                      pure expr
                  else
                    pure expr
                else
                  withTransparency .reducible <| whnf expr : MetaM Expr)
        catch _ =>
          modify fun result => { result with
            incomplete := true
            incompleteReason := result.incompleteReason <|> some "operator reduction failed" }
          pure expr
      if normalized != expr then
        auditExpr ownership kind normalized (fuel - 1)
      else
        match expr with
        | .app .. => auditExpr ownership kind function (fuel - 1)
        | .proj _ _ payload => auditExpr ownership kind payload (fuel - 1)
        | .mdata _ body => auditExpr ownership kind body (fuel - 1)
        | _ => pure ()

private def auditDeclarationWith (declName : Name) (graphAbsent coveredProofs : NameSet) :
    MetaM AuditResult := do
  let env ← getEnv
  let some info := env.find? declName | return { graphAbsent, coveredProofs, incomplete := true }
  let ownership := moduleOwnership env declName
  let fuel := 512
  let action : StateT AuditResult MetaM Unit := do
    if ← expressionMayReachForbidden info.type then
      auditExpr ownership .statement info.type fuel
    if let some value := info.value? (allowOpaque := true) then
      let valueKind ← if ← liftM <| isProofType info.type then
          pure .proof
        else
          match info with
          | .thmInfo _ => pure .proof
          | .defnInfo _ | .opaqueInfo _ =>
              if ← liftM <| isPredicateType info.type then pure .statement else pure .data
          | _ => pure .data
      if ← expressionMayReachForbidden value then
        auditExpr ownership valueKind value fuel
  return (← action.run { graphAbsent, coveredProofs }).2

/-- Audit one declaration for semantic and proof dependencies on retired operators. -/
public def auditDeclaration (declName : Name) : MetaM AuditResult :=
  auditDeclarationWith declName {} {}

/-- Audit a standalone elaborated expression. Primarily useful for regression tests and tooling. -/
public def auditExpression (expr : Expr) (kind := DependencyKind.data) : MetaM AuditResult :=
  let action : StateT AuditResult MetaM Unit := do
    if ← expressionMayReachForbidden expr then
      auditExpr .project kind expr
  return (← action.run {}).2

private def rootsMessage (label : String) (roots : Array Name) : MessageData :=
  m!"{label}: {", ".intercalate (roots.map toString).toList}"

/-- Actionable linter for statement and non-proof data dependencies on retired operators. -/
@[env_linter disabled]
public def operatorFidelity : Batteries.Tactic.Lint.Linter where
  noErrorsFound := "No maintained declarations depend semantically on retired operators."
  errorsFound := "DECLARATIONS DEPEND SEMANTICALLY ON RETIRED OPERATORS:"
  test declName := do
    let env ← getEnv
    if moduleOwnership env declName matches .officialToolchain | .external then
      return none
    let result ← auditDeclaration declName
    unless result.hasActionableFinding do
      return none
    let mut parts : Array MessageData := #[]
    if result.incomplete then
      parts := parts.push "audit traversal was incomplete; refusing to report a clean declaration"
    unless result.statementRoots.isEmpty do
      parts := parts.push (rootsMessage "statement dependencies" result.statementRoots)
    unless result.dataRoots.isEmpty do
      parts := parts.push (rootsMessage "non-proof data dependencies" result.dataRoots)
    return MessageData.joinSep parts.toList Format.line

/-- Companion linter for proof dependencies, separated by source ownership. -/
@[env_linter disabled]
public def operatorFidelityProof : Batteries.Tactic.Lint.Linter where
  noErrorsFound := "No proof dependencies on retired operators were found."
  errorsFound := "PROOF DEPENDENCIES ON RETIRED OPERATORS REQUIRE OWNERSHIP REVIEW:"
  test declName := do
    let result ← auditDeclaration declName
    if result.incomplete then
      return "proof audit traversal was incomplete; refusing to report a clean declaration"
    if result.proofUses.isEmpty then
      return none
    let lines := result.proofUses.map fun use =>
      m!"{.ofConstName use.root} ({repr use.ownership})"
    return MessageData.joinSep lines.toList Format.line

/-- A proof dependency together with the declaration that contains it. -/
public structure DeclarationProofUse extends ProofUse where
  /-- The declaration whose audit produced this proof dependency. -/
  declaration : Name
  deriving BEq, DecidableEq, Inhabited, Repr

-- A package audit visits the selected theorem bodies at their own declarations.
private def coverProofs (declarations : Array Name) : NameSet :=
  declarations.foldl (init := {}) fun names name => names.insert name

private def collectProofAudit (declarations : Array Name) (coveredProofs : NameSet := {}) :
    MetaM (Array DeclarationProofUse × Bool) := do
  let mut uses := #[]
  let mut incomplete := false
  let mut graphAbsent : NameSet := {}
  for declaration in declarations do
    let result ← auditDeclarationWith declaration graphAbsent coveredProofs
    graphAbsent := result.graphAbsent
    incomplete := incomplete || result.incomplete
    for use in result.proofUses do
      uses := uses.push { declaration, root := use.root, ownership := use.ownership }
  return (uses, incomplete)

/-- Collect the proof-only findings for a set of declarations without turning them into errors. -/
public def collectProofUses (declarations : Array Name) : MetaM (Array DeclarationProofUse) := do
  return (← collectProofAudit declarations).1

private def logProofUses (uses : Array DeclarationProofUse) (incomplete : Bool) :
    CommandElabM Unit := do
  unless uses.isEmpty do
    let lines := uses.map fun use =>
      m!"{.ofConstName use.declaration}: {.ofConstName use.root} ({repr use.ownership})"
    logInfo <| MessageData.joinSep lines.toList Format.line
  if !incomplete && uses.isEmpty then
    logInfo "No proof dependencies on retired operators were found."

private def reportProofUses (declarations : Array Name) (coveredProofs : NameSet := {}) :
    CommandElabM Unit := do
  let (uses, incomplete) ← liftTermElabM <| collectProofAudit declarations coveredProofs
  logProofUses uses incomplete
  if incomplete then
    throwError "Proof dependency report is incomplete."

private def enforceSemanticAudit (declarations : Array Name) (reportProofs : Bool := false) :
    CommandElabM Unit := do
  let mut failures : Array MessageData := #[]
  let mut uses : Array DeclarationProofUse := #[]
  let mut incomplete := false
  let mut graphAbsent : NameSet := {}
  let coveredProofs := coverProofs declarations
  for declaration in declarations do
    let result ← liftTermElabM <| auditDeclarationWith declaration graphAbsent coveredProofs
    graphAbsent := result.graphAbsent
    if reportProofs then
      incomplete := incomplete || result.incomplete
      for use in result.proofUses do
        uses := uses.push { declaration, root := use.root, ownership := use.ownership }
    if result.hasActionableFinding then
      let mut parts : Array MessageData := #[m!"{.ofConstName declaration}"]
      if result.incomplete then
        parts := parts.push (match result.incompleteReason with
          | some reason => m!"incomplete traversal ({reason})"
          | none => "incomplete traversal")
      let mut unavailable : Array Name := #[]
      for name in result.unavailableConstants do
        unavailable := unavailable.push name
        if unavailable.size == 5 then break
      unless unavailable.isEmpty do
        parts := parts.push (rootsMessage "unavailable declarations" unavailable)
      unless result.statementRoots.isEmpty do
        parts := parts.push (rootsMessage "statement" result.statementRoots)
      unless result.dataRoots.isEmpty do
        parts := parts.push (rootsMessage "data" result.dataRoots)
      failures := failures.push <| MessageData.joinSep parts.toList ": "
  if reportProofs then
    logProofUses uses incomplete
  unless failures.isEmpty do
    throwError m!"Operator-fidelity semantic audit failed:{Format.line}
      {MessageData.joinSep failures.toList Format.line}"

/-- Report proof-only operator dependencies in the current module. -/
syntax (name := operatorFidelityProofReport) "#operator_fidelity_proofs" : command

/-- Report proof-only operator dependencies in a package, or in the full environment with `all`.
The report checks each selected theorem body at its own declaration. -/
syntax (name := operatorFidelityProofReportIn)
  "#operator_fidelity_proofs" " in " ident : command

/-- Run the failing semantic gate over a package, or the full environment with `all`. -/
syntax (name := operatorFidelitySemanticReportIn)
  "#operator_fidelity" " in " ident : command

/-- Check semantic dependencies and report proof dependencies in one traversal of a package. -/
syntax (name := operatorFidelityWithProofsIn)
  "#operator_fidelity" " with_proofs " "in " ident : command

private def getScopeDeclarations (project : Name) : CoreM (Array Name) :=
  if project == `all then Batteries.Tactic.Lint.getAllDecls
  else Batteries.Tactic.Lint.getDeclsInPackage project

elab_rules : command
  | `(#operator_fidelity_proofs) => do
      reportProofUses (← liftCoreM Batteries.Tactic.Lint.getDeclsInCurrModule)
  | `(#operator_fidelity_proofs in $project) => do
      let declarations ← liftCoreM <| getScopeDeclarations project.getId.eraseMacroScopes
      reportProofUses declarations (coverProofs declarations)
  | `(#operator_fidelity in $project) => do
      let declarations ← liftCoreM <| getScopeDeclarations project.getId.eraseMacroScopes
      enforceSemanticAudit declarations
  | `(#operator_fidelity with_proofs in $project) => do
      let declarations ← liftCoreM <| getScopeDeclarations project.getId.eraseMacroScopes
      enforceSemanticAudit declarations (reportProofs := true)

end Mathlib.Linter.OperatorFidelity
