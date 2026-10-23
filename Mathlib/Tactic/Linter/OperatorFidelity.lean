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
  root : Name
  ownership : SourceOwnership
  deriving BEq, DecidableEq, Inhabited, Repr

/-- Semantic operator dependencies found in one declaration. -/
public structure AuditResult where
  statementRoots : Array Name := #[]
  dataRoots : Array Name := #[]
  proofUses : Array ProofUse := #[]
  incomplete : Bool := false
  visitedConstants : NameSet := {}
  graphAbsent : NameSet := {}
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
      if (`Init).isPrefixOf moduleName || (`Lean).isPrefixOf moduleName then
        .officialToolchain
      else if (`Mathlib).isPrefixOf moduleName || (`MathlibTest).isPrefixOf moduleName then
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

private partial def expressionConstants (expr : Expr) (names : NameSet := {}) : NameSet :=
  match expr.consumeMData with
  | .const name _ => names.insert name
  | .app fn arg => expressionConstants arg (expressionConstants fn names)
  | .lam _ domain body _ | .forallE _ domain body _ =>
      expressionConstants body (expressionConstants domain names)
  | .letE _ type value body _ =>
      expressionConstants body (expressionConstants value (expressionConstants type names))
  | .proj name _ payload => expressionConstants payload (names.insert name)
  | .mdata _ body => expressionConstants body names
  | _ => names

private def expressionMayReachForbidden (expr : Expr) : StateT AuditResult MetaM Bool := do
  let env ← getEnv
  let mut pending := #[]
  for name in expressionConstants expr do pending := pending.push name
  let mut seen : NameSet := {}
  let mut budget := 100000
  while let some name := pending.back? do
    pending := pending.pop
    if budget == 0 then
      modify fun result => { result with incomplete := true }
      return true
    budget := budget - 1
    if forbiddenRoots.contains name then return true
    if lawfulBoundaries.contains name || seen.contains name || (← get).graphAbsent.contains name then
      continue
    seen := seen.insert name
    if let some info := env.find? name then
      for dependency in expressionConstants info.type do pending := pending.push dependency
      if let some value := info.value? then
        for dependency in expressionConstants value do pending := pending.push dependency
  let mut absent := (← get).graphAbsent
  for name in seen do absent := absent.insert name
  modify fun result => { result with graphAbsent := absent }
  return false

private partial def auditExpr (ownership : SourceOwnership) (kind : DependencyKind)
    (expr : Expr) (fuel : Nat := 128) : StateT AuditResult MetaM Unit := do
  if fuel == 0 then
    modify fun result => { result with incomplete := true }
    return
  let expr := expr.consumeMData
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
          let seen := (← get).visitedConstants.contains name
          unless seen do
            modify fun result =>
              { result with visitedConstants := result.visitedConstants.insert name }
          if !seen then
            if let some info := env.find? name then
              let calleeOwnership := moduleOwnership env name
              auditExpr calleeOwnership .proof info.type (fuel - 1)
              if calleeOwnership == SourceOwnership.project ||
                  calleeOwnership == SourceOwnership.generatedProject then
                if let some value := info.value? then
                  auditExpr calleeOwnership .proof value (fuel - 1)
          for argument in visibleArguments do
            auditExpr ownership kind argument (fuel - 1)
          return
      -- Inspect arguments before reduction: beta/iota reduction may erase proof arguments whose
      -- dependencies still belong in the ownership report.
      for argument in visibleArguments do
        auditExpr ownership kind argument (fuel - 1)
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
          modify fun result => { result with incomplete := true }
          pure expr
      if normalized != expr then
        auditExpr ownership kind normalized (fuel - 1)
      else
        match expr with
        | .app .. => auditExpr ownership kind function (fuel - 1)
        | .proj _ _ payload => auditExpr ownership kind payload (fuel - 1)
        | .mdata _ body => auditExpr ownership kind body (fuel - 1)
        | _ => pure ()

/-- Audit one declaration for semantic and proof dependencies on retired operators. -/
public def auditDeclaration (declName : Name) : MetaM AuditResult := do
  let env ← getEnv
  let some info := env.find? declName | return {}
  let ownership := moduleOwnership env declName
  let action : StateT AuditResult MetaM Unit := do
    if ← expressionMayReachForbidden info.type then
      auditExpr ownership .statement info.type
    if let some value := info.value? then
      let valueKind ← if ← liftM <| isProofType info.type then
          pure .proof
        else
          match info with
          | .thmInfo _ => pure .proof
          | .defnInfo _ | .opaqueInfo _ =>
              if ← liftM <| isPredicateType info.type then pure .statement else pure .data
          | _ => pure .data
      if ← expressionMayReachForbidden value then
        auditExpr ownership valueKind value
  return (← action.run {}).2

/-- Audit a standalone elaborated expression. Primarily useful for regression tests and tooling. -/
public def auditExpression (expr : Expr) (kind := DependencyKind.data) : MetaM AuditResult :=
  let action : StateT AuditResult MetaM Unit := do
    if ← expressionMayReachForbidden expr then
      auditExpr .project kind expr
  return (← action.run {}).2

private def rootsMessage (label : String) (roots : Array Name) : MessageData :=
  m!"{label}: {", ".intercalate (roots.map toString).toList}"

/-- Actionable linter for statement and non-proof data dependencies on retired operators. -/
@[env_linter]
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
  declaration : Name
  deriving BEq, DecidableEq, Inhabited, Repr

/-- Collect the proof-only findings for a set of declarations without turning them into errors. -/
public def collectProofUses (declarations : Array Name) : MetaM (Array DeclarationProofUse) := do
  let mut uses := #[]
  for declaration in declarations do
    let result ← auditDeclaration declaration
    for use in result.proofUses do
      uses := uses.push { declaration, root := use.root, ownership := use.ownership }
  return uses

private def reportProofUses (declarations : Array Name) : CommandElabM Unit := do
  let uses ← liftTermElabM <| collectProofUses declarations
  let incomplete ← liftTermElabM <| declarations.anyM fun declaration => do
    return (← auditDeclaration declaration).incomplete
  if incomplete then
    logWarning "Proof dependency report is incomplete; refusing to report a clean audit."
  else if uses.isEmpty then
    logInfo "No proof dependencies on retired operators were found."
  else
    let lines := uses.map fun use =>
      m!"{.ofConstName use.declaration}: {.ofConstName use.root} ({repr use.ownership})"
    logInfo <| MessageData.joinSep lines.toList Format.line

private def enforceSemanticAudit (declarations : Array Name) : CommandElabM Unit := do
  let mut failures : Array MessageData := #[]
  for declaration in declarations do
    let result ← liftTermElabM <| auditDeclaration declaration
    if result.hasActionableFinding then
      let mut parts : Array MessageData := #[m!"{.ofConstName declaration}"]
      if result.incomplete then
        parts := parts.push "incomplete traversal"
      unless result.statementRoots.isEmpty do
        parts := parts.push (rootsMessage "statement" result.statementRoots)
      unless result.dataRoots.isEmpty do
        parts := parts.push (rootsMessage "data" result.dataRoots)
      failures := failures.push <| MessageData.joinSep parts.toList ": "
  unless failures.isEmpty do
    throwError m!"Operator-fidelity semantic audit failed:{Format.line}
      {MessageData.joinSep failures.toList Format.line}"

/-- Report proof-only operator dependencies in the current module without failing elaboration. -/
syntax (name := operatorFidelityProofReport) "#operator_fidelity_proofs" : command

/-- Report proof-only operator dependencies in a package, or in the full environment with `all`. -/
syntax (name := operatorFidelityProofReportIn)
  "#operator_fidelity_proofs" " in " ident : command

/-- Run the failing semantic gate over a package, or the full environment with `all`. -/
syntax (name := operatorFidelitySemanticReportIn)
  "#operator_fidelity" " in " ident : command

elab_rules : command
  | `(#operator_fidelity_proofs) => do
      reportProofUses (← liftCoreM Batteries.Tactic.Lint.getDeclsInCurrModule)
  | `(#operator_fidelity_proofs in $project) => do
      let projectName := project.getId.eraseMacroScopes
      let declarations ← liftCoreM <| if projectName == `all then
        Batteries.Tactic.Lint.getAllDecls
      else
        Batteries.Tactic.Lint.getDeclsInPackage projectName
      reportProofUses declarations
  | `(#operator_fidelity in $project) => do
      let projectName := project.getId.eraseMacroScopes
      let declarations ← liftCoreM <| if projectName == `all then
        Batteries.Tactic.Lint.getAllDecls
      else
        Batteries.Tactic.Lint.getDeclsInPackage projectName
      enforceSemanticAudit declarations

end Mathlib.Linter.OperatorFidelity
