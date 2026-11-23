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
  /-- The declaration whose proof or signature supplied this use, or anonymous for a bare term. -/
  sourceDeclaration : Name
  /-- The source ownership associated with this proof dependency. -/
  ownership : SourceOwnership
  deriving BEq, DecidableEq, Inhabited, Repr

/-- Syntactic reachability in a fixed environment and proof coverage scope. -/
public structure DependencyCache where
  /-- Constants with a path to a retired root. -/
  reachable : NameSet := {}
  /-- Constants whose transitive dependencies were checked without finding a path. -/
  unreachable : NameSet := {}
  /-- Direct edges already read in the semantic search. -/
  dependencies : NameMap (Array Name) := {}
  /-- Dependencies already inspected by the package's proof-source report. -/
  proofSourcesChecked : NameSet := {}
  deriving Inhabited

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
  /-- Cached graph search results, used only to decide which expressions to inspect. -/
  dependencyCache : DependencyCache := {}
  /-- Theorems whose signatures and bodies are checked separately in this audit. -/
  coveredProofs : NameSet := {}
  /-- Definitions whose mathematical signatures and bodies are checked elsewhere in this audit. -/
  coveredDefinitions : NameSet := {}
  /-- Whether proof dependencies contribute to a shared package report. -/
  shareProofSources : Bool := false
  /-- Proof bodies deferred by the semantic search and visited by the proof-source report. -/
  deferredProofs : NameSet := {}
  /-- Constant names reached by the scan whose declarations were unavailable. -/
  unavailableConstants : NameSet := {}
  deriving Inhabited

/-- Whether the declaration has a statement or non-proof data dependency on a retired operator. -/
public def AuditResult.hasActionableFinding (result : AuditResult) : Bool :=
  result.incomplete || !result.statementRoots.isEmpty || !result.dataRoots.isEmpty

/-- Core operators whose unrestricted mathematical semantics have been retired. -/
public def forbiddenRoots : Array Name := #[
  ``Rat.inv,
  ``Rat.div,
  ``Rat.zpow,
  ``mkRat,
  ``Rat.divInt,
  ``Nat.div,
  ``Int.ediv
]

/--
Verified semantic boundaries that must not be unfolded while normalizing operator applications.

The list is intentionally narrow.  In particular, generic `Inv.inv` is absent because inversion of
groups and units is lawful; projection reduction determines whether a concrete use selects a
retired rational inverse. `Rat.le_floor_iff` and `Rat.ceil_le_iff` specify floor and ceiling.
Their native quotient uses the positive denominator carried by `Rat`. `Nat.lcm` is
characterized on *all* inputs by `Nat.lcm_dvd_iff`
and divisibility antisymmetry, including at `(0, 0)`. Its core implementation uses division
by the gcd. `Nat.eq_sqrt'` characterizes the integer square root on every input, including
`Nat.sqrt_zero`. `Nat.bitwise` recurses on low bits until an input is zero, when it either
returns the other input or clears its remaining bits. `Nat.testBit_bitwise` gives the pointwise
specification for zero-preserving Boolean functions. `Nat.testBit_shiftRight` specifies right
shift. Both implementations halve with divisor `2`.
`Nat.log2` gives the binary length minus one with natural subtraction, as follows from
`Nat.log2_eq_iff`, `Nat.log2_zero`, `Nat.lt_size`, and `Nat.size_le`. It halves with divisor `2`.
`Nat.repr` renders decimal numerals using the fixed base `10`.
`List.mergeSort` preserves the input permutation and is stable by
`List.mergeSort_perm` and `List.mergeSort_zipIdx`. `List.pairwise_mergeSort` specifies sortedness
with a total transitive comparator. Its recursive split always halves a length with divisor `2`.
`Array.binSearchAux` narrows a nonempty inclusive interval using its midpoint.
`Array.qsort` swaps and partitions elements within the selected interval by the comparator.
The only quotient in either algorithm selects an index by halving the sum of bounds.
`String.utf8EncodeChar_eq_utf8EncodeCharFast` specifies the UTF-8 byte calculation by bit operations.
`Char.quoteCore` escapes control characters by rendering their two hexadecimal digits,
using the fixed radix `16` when the code point is at most `31` or equals `127`.
`Int.trailingZeros_zero` gives the zero convention. `Int.two_pow_trailingZeros_dvd` and
`Int.shiftRight_trailingZeros_mod_two` specify the extracted power of two on nonzero inputs.
The auxiliary loop halves only even integers, using divisor `2`.
The standard generator's seed conversion `mkStdGen` divides by `2147483562`.
Its state update `stdNext` uses fixed divisors `53668` and `52774`.
`randNat` samples between its ordered endpoints using a positive generator-range size
`genHi - genLo + 1`. Its remainder also has a positive modulus `hi' - lo' + 1`.
The hash-table bucket calculation chooses the greatest `k` with `3 * k ≤ 4 * capacity`.
`Lean.PersistentArray.tooBig` is the addressable-size threshold in groups of eight,
and `Lean.Core.throwMaxHeartbeat` displays the budget in thousands of heartbeats.
The floating model's `ExtendedMantissa.shiftRightOne` shifts a bit into the rounding position
and combines the previous residual bits. `UnpackedFloat.div` handles zero and nonfinite
arguments explicitly. Only its finite branch divides the mantissas, whose denominator is nonzero.
`UnpackedFloat.sqrtCore` halves signed exponents with fixed divisor `2` before the mantissa square
root and rounding-accuracy calculation.
`WellFounded.Nat.fix_eq` specifies the fixpoint, and
`WellFounded.Nat.fix.go_congr` proves independence of the internal fuel. The fixpoint's motive,
measure, recursive body, and input are still audited. `Nat.euclideanDiv_mul_add_mod` and
`Nat.euclideanDiv_eq_of_remainder` characterize the guarded natural quotient. The maximum-power
decomposition is specified by `Nat.maxPowDvdDiv_spec` and `Nat.maxPowDvdDiv_of_pow_mul_eq`.
These fork definitions' bodies are checked at their own declarations. The guarded worker
`Nat.div.go` and native remainders require no exemption.
-/
public def lawfulBoundaries : Array Name := #[
  ``Rat.normalize,
  ``Rat.ofInt,
  ``Rat.add,
  ``Rat.sub,
  ``Rat.neg,
  ``Rat.mul,
  ``Rat.pow,
  ``Rat.floor,
  ``Rat.ceil,
  ``Nat.lcm,
  ``Nat.sqrt,
  ``Nat.log2,
  ``Nat.bitwise,
  ``Nat.shiftRight,
  ``Nat.repr,
  ``List.mergeSort,
  ``Array.binSearchAux,
  ``Array.qsort,
  ``String.utf8EncodeChar,
  ``Char.quoteCore,
  `Int.trailingZeros,
  `mkStdGen,
  `stdNext,
  `randNat,
  mkPrivateNameCore `Std.Data.DHashMap.Internal.Defs `Std.DHashMap.Internal.numBucketsForCapacity,
  `Lean.PersistentArray.tooBig,
  `Lean.Core.throwMaxHeartbeat,
  `Float.Model.UnpackedFloat.ExtendedMantissa.shiftRightOne,
  `Float.Model.UnpackedFloat.div,
  `Float.Model.UnpackedFloat.sqrtCore,
  ``WellFounded.Nat.fix,
  `Nat.euclideanDiv,
  `Nat.maxPowDvdDiv
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

private def addRoot (kind : DependencyKind) (root sourceDeclaration : Name)
    (ownership : SourceOwnership) : StateT AuditResult MetaM Unit :=
  modify fun result => match kind with
    | .statement => { result with statementRoots := pushNew result.statementRoots root }
    | .data => { result with dataRoots := pushNew result.dataRoots root }
    | .proof =>
        { result with proofUses := pushNew result.proofUses { root, sourceDeclaration, ownership } }

private def isPredicateType (type : Expr) : MetaM Bool :=
  forallTelescope type fun _ body => do
    -- The codomain of a proposition or predicate *definition* is `Prop` itself.  Do not WHNF an
    -- arbitrary proposition here: unfolding `True`, for example, would misclassify a definition
    -- whose value is a proof of `True` as the definition of a proposition.
    return body.consumeMData == .sort .zero

private def isProofType (type : Expr) : MetaM Bool := do
  return (← whnf (← inferType type)).consumeMData == .sort .zero

private def elaborationCallbacks : Array Name := #[
  `Lean.Elab.Tactic.Tactic, `Lean.Elab.Term.TermElab, `Lean.Elab.Command.CommandElab,
  `Lean.Elab.Command.Linter, `Lean.Elab.ConfigEval.EvalConfigItem, `Lean.Elab.ConfigEval.EvalExpr,
  `Lean.Elab.ConfigEval.EvalTerm, ``Lean.Macro, `Lean.PrettyPrinter.Delaborator.Delab,
  `Lean.PrettyPrinter.Parenthesizer, `Lean.PrettyPrinter.Formatter, `Lean.Meta.Simp.Simproc,
  `Lean.Meta.Simp.Methods, `Lean.Parser.Parser, `Lean.Parser.ParserFn, `Lean.Elab.DerivingHandler,
  `Aesop.RuleTac, `Lean.Server.RpcProcedure, `Mathlib.TacticAnalysis.Config,
  `Mathlib.Tactic.Linarith.Preprocessor, `Mathlib.Tactic.Linarith.GlobalBranchingPreprocessor]

private def elaborationEffects : Array Name := #[
  ``Lean.Elab.Tactic.TacticM, ``Lean.Elab.Term.TermElabM, ``Lean.Elab.Command.CommandElabM,
  ``Lean.Core.CoreM, ``Lean.Meta.MetaM, ``Lean.PrettyPrinter.Delaborator.DelabM,
  `Lean.PrettyPrinter.ParenthesizerM, `Lean.PrettyPrinter.FormatterM, `Lean.Meta.Simp.SimpM,
  `Lean.Server.RequestM, `Mathlib.Tactic.AtomM, `Mathlib.Tactic.AtomM.RecurseM]

private def elaborationStateTypes : Array Name := #[
  ``Syntax, ``TSyntax, ``Expr, ``Level, ``MVarId, ``FVarId, ``Name, ``MessageData,
  ``Lean.Meta.Simp.Result, `Lean.Meta.Simp.Stats, `Lean.Meta.SimpExtension,
  `Lean.Meta.Simp.SimprocExtension,
  `Lean.LocalContext, `Lean.Meta.Grind.Extension,
  `Qq.Quoted, `Lean.Environment, `Lean.AttributeImpl, `Lean.TagAttribute, `Lean.ParametricAttribute,
  `Lean.Syntax.Term, `Lean.Syntax.Ident, `Lean.Syntax.Range, `Lean.NameSet, `Std.Format,
  `Lean.Exception, `IO.Error, `Lean.Server.RequestError, `ProofWidgets.Html,
  `Mathlib.Tactic.AtomM.Context, `Mathlib.Tactic.AtomM.Recurse.Context,
  `Mathlib.Tactic.Linarith.LinarithConfig, `Mathlib.Tactic.Order.AtomicFact,
  `Mathlib.Tactic.CancelDenoms.CancelResult,
  mkPrivateNameCore `Mathlib.Tactic.FieldSimp `Mathlib.Tactic.FieldSimp.Factors]

/-- Recognize elaboration state in containers and internal records. A product or record must
carry elaboration state in every field. Atom actions also carry indices of their stored expressions. -/
private def hasElaborationPayload (env : Environment) (origin : Option ModuleIdx)
    (allowPrivateRecords atomIndices : Bool) (payload : Expr) : Nat → Bool
  | 0 => false
  | fuel + 1 => Id.run do
    let payload := payload.consumeMData.headBeta.getForallBody.consumeMData
    let hasState (field : Expr) :=
      hasElaborationPayload env origin allowPrivateRecords atomIndices field fuel
    if let .letE _ _ value body _ := payload then
      return hasState (body.instantiate1 value)
    let some name := payload.getAppFn.constName? | return false
    if elaborationStateTypes.contains name || name == ``Unit || name == ``PUnit then return true
    let args := payload.getAppArgs
    if #[``Option, ``Array, ``List, ``IO.Ref, ``Lean.Option, `Lean.Server.RequestTask].contains name ||
        elaborationEffects.contains name then
      return args.size == 1 && hasState payload.appArg!
    if name == `Mathlib.Tactic.ClickSuggestions.Result ||
        name == `Mathlib.Tactic.ClickSuggestions.SectionState then
      return args.size == 1 && (payload.appArg!.isBVar || hasState payload.appArg!)
    if name == `Std.HashMap then
      let #[key, value, _, _] := args | return false
      return (hasState key || (atomIndices && key.isConstOf ``Nat)) && hasState value
    if #[``Prod, ``PProd, ``Except].contains name then
      let #[left, right] := args | return false
      if name == ``Prod && left.isConstOf ``Name && right.isConstOf ``String then return true
      return (hasState left || (name == ``Prod && atomIndices && left.isConstOf ``Nat)) && hasState right
    if #[``Sigma, ``PSigma].contains name then
      let #[first, .lam _ _ second _] := args | return false
      return hasState first && hasState second
    if #[`Mathlib.Tactic.Ring.Common.ExSum, `Mathlib.Tactic.Ring.Common.RingCompute].contains name then
      return args[2]?.any fun base => base.isAppOf `Mathlib.Tactic.Algebra.BaseType
    unless allowPrivateRecords && payload.isConst && isPrivateName name &&
        env.getModuleIdxFor? name == origin do
      return false
    let some (.inductInfo info) := env.find? name | return false
    unless !info.isRec && info.numParams == 0 && info.numIndices == 0 do return false
    let mut hasField := false
    for ctor in info.ctors do
      let some (.ctorInfo ctorInfo) := env.find? ctor | return false
      let mut fields := ctorInfo.type
      for _ in [:ctorInfo.numFields] do
        let .forallE _ domain body _ := fields.consumeMData | return false
        unless hasState domain do return false
        fields := body
        hasField := true
    return hasField

/-- Match the result after instantiating aliases. An alias may change its apparent result type or
introduce an additional result field, as `StateT` does. -/
private def elaborationActionResult? (env : Environment) (isMeta : Bool) (type : Expr) :
    Nat → Option Expr
  | 0 => none
  | fuel + 1 => do
    let result := type.getForallBody.consumeMData
    let .const name levels := result.getAppFn | none
    let args := result.getAppArgs
    if args.size == 1 &&
        (elaborationEffects.contains name || (isMeta && #[``IO, ``BaseIO].contains name)) then
      return result.appArg!
    if isMeta && name == ``EIO && args.size == 2 &&
        args[0]!.getAppFn.constName?.any elaborationStateTypes.contains then
      return result.appArg!
    let some (.defnInfo info) := env.find? name | none
    if info.hints.isAbbrev || #[``ReaderT, ``StateT, ``ExceptT, ``OptionT].contains name then
      let unfolded := (info.value.instantiateLevelParamsNoCache info.levelParams levels).beta args
      elaborationActionResult? env isMeta unfolded fuel
    else none

private def hasMetaMCapabilities (type result : Expr) : Bool := Id.run do
  let .bvar index := result.getAppFn | return false
  unless result.isApp do return false
  let hasExpr := type.getUsedConstants.contains ``Expr
  let isDiagnostic := result.appArg!.isConstOf ``Unit &&
    type.getUsedConstants.any elaborationStateTypes.contains
  unless (hasExpr && result.appArg!.isBVar) || isDiagnostic do return false
  let mut domains := #[]
  let mut remaining := type
  while let .forallE _ domain body _ := remaining.consumeMData do
    domains := domains.push domain
    remaining := body
  let monadBinder := domains.size - (index + 1)
  let mut lifts := false
  let mut controls := false
  let mut liftsCore := false
  for i in [monadBinder + 1:domains.size] do
    let domain := domains[i]!
    let #[src, dest] := domain.getAppArgs | continue
    if dest == mkBVar (i - monadBinder - 1) then
      if src.isConstOf ``Lean.Meta.MetaM then
        lifts := lifts || domain.isAppOf ``MonadLiftT
        controls := controls || domain.isAppOf ``MonadControlT
      if src.isConstOf ``Lean.Core.CoreM then
        liftsCore := liftsCore || domain.isAppOf ``MonadLiftT
  return (hasExpr && result.appArg!.isBVar && lifts && controls) ||
    (isDiagnostic && liftsCore)

/-- Recognize compiler callbacks and meta code that returns elaboration or presentation state. -/
private def isElaborationImplementation (env : Environment) (declName : Name) (type : Expr) :
    Bool := Id.run do
  let result := type.getForallBody.consumeMData
  let head := result.getAppFn.constName?.getD .anonymous
  if elaborationCallbacks.contains head || isIOUnitInitFn env declName then return true
  if result.isAppOfArity ``List 1 &&
      result.appArg!.getAppFn.constName?.any elaborationCallbacks.contains then return true
  if hasMetaMCapabilities type result then return true
  -- The compiler emits partial recursive implementations with the owner's type and fresh
  -- modifiers. Recover meta phase only for that generated implementation and its exact owner.
  let isMeta := isMarkedMeta env declName ||
    (env.isAutoDecl declName && (env.find? declName).any (·.isPartial) &&
      (Compiler.isUnsafeRecName? declName).any fun owner =>
        isMarkedMeta env owner && (env.find? owner).any (·.type == type))
  let actionResult := elaborationActionResult? env isMeta result 8
  let effect := actionResult.isSome
  let payload := actionResult.getD result
  -- `derive` returns the scale from `findCancelFactor` together with its proof term.
  -- The factor computation is also audited at `findCancelFactor`'s own declaration.
  if isMeta && declName == `Mathlib.Tactic.CancelDenoms.derive && effect &&
      payload.isAppOfArity ``Prod 2 && payload.appFn!.appArg!.isConstOf ``Nat &&
      payload.appArg!.isConstOf ``Expr then return true
  if effect && payload.isConstOf ``Unit then return true
  if (effect || isMeta) && payload.isConstOf ``Bool &&
      type.getUsedConstants.any elaborationStateTypes.contains
    then return true
  if isMeta && effect && payload.isBVar && type.getUsedConstants.any elaborationStateTypes.contains
    then return true
  let atomIndices := head == `Mathlib.Tactic.AtomM || head == `Mathlib.Tactic.AtomM.RecurseM
  return (effect || isMeta) &&
    hasElaborationPayload env (env.getModuleIdxFor? declName) (isMeta && effect) atomIndices payload 8

private def isElaborationEquation (env : Environment) (declName : Name) : Bool :=
  env.isAutoDecl declName && (env.find? declName.getPrefix).any fun parent =>
    isElaborationImplementation env parent.name parent.type

/-- Equations generated from a verified toolchain implementation expose the implementation
to proofs. The mathematical operation itself has its own independent specification. -/
private def isToolchainBoundaryEquation (declName : Name) : MetaM Bool := do
  let env ← getEnv
  let isBoundary (name : Name) :=
    lawfulBoundaries.contains name && moduleOwnership env name == .officialToolchain
  if let some owner ← isEqnThm? declName then return isBoundary owner
  -- Imported equations can predate the reverse lookup in the current environment.
  let some (owner, suffix) := declFromEqLikeName env declName | return false
  unless isBoundary owner do return false
  let origin := (env.getModuleIdxFor? declName).map fun index => env.header.moduleNames[index]!
  if isPrivateName declName then
    -- A legacy import exposes definition bodies, even when a module importer generated a
    -- private equation. Compare the canonical private name and the existing toolchain equation.
    let some origin := origin | return false
    let canonical := Name.str owner suffix
    unless declName == mkPrivateNameCore origin canonical do return false
    unless suffix == unfoldThmSuffix || isEqnReservedNameSuffix suffix do return false
    let some (.thmInfo info) := env.find? declName | return false
    let matchesReference (name : Name) := match env.find? name with
      | some (.thmInfo reference) =>
        moduleOwnership env name == .officialToolchain &&
          info.levelParams == reference.levelParams && info.type == reference.type
      | _ => false
    return matchesReference canonical || env.header.moduleNames.any fun moduleName =>
      matchesReference (mkPrivateNameCore moduleName canonical)
  let equationEnv := env.setMainModule (origin.getD env.mainModule)
  unless mkEqLikeNameFor equationEnv owner suffix == declName do
    return false
  withEnv equationEnv do
    if suffix == unfoldThmSuffix && equationEnv.contains declName then
      return (← getUnfoldEqnFor? owner) == some declName
    unless isEqnReservedNameSuffix suffix &&
        equationEnv.contains (mkEqLikeNameFor equationEnv owner eqn1ThmSuffix) do return false
    let equations ← withoutModifyingEnv <| getEqnsFor? owner
    return equations.any (·.contains declName)

private def isTheorem (env : Environment) (name : Name) : Bool :=
  env.find? name |>.any fun
    | .thmInfo _ => true
    | _ => false

/-- Recognize declarations with a proposition as their codomain using their kernel types.
An unknown codomain still requires type inference at the use site. -/
private def isKnownProof (env : Environment) (info : ConstantInfo) : Bool := Id.run do
  if let .thmInfo _ := info then return true
  let result := info.type.getForallBody.consumeMData
  let some head := result.getAppFn.constName? | return false
  let some family := env.find? head | return false
  let mut type := family.type
  for _ in [:result.getAppNumArgs] do
    let .forallE _ _ body _ := type.consumeMData | return false
    type := body
  return type.consumeMData == .sort .zero

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

/-- Distribute a stuck projection over the alternatives of a conditional structure. Keep the
condition and its decision procedure, since changing the selected branch may change the result. -/
private def conditionalProjection? (fn : Expr) (args : Array Expr) (index : Nat) (choice : Expr) :
    MetaM (Option (Array Expr)) := do
  unless choice.isAppOfArity ``ite 5 || choice.isAppOfArity ``dite 5 do return none
  let project (branch : Expr) := mkAppN fn <| args.set! index branch
  let #[_, condition, decision, yes, no] := choice.getAppArgs | return none
  if choice.isAppOf ``ite then return some #[condition, decision, project yes, project no]
  let projectBranch (branch : Expr) (hypothesis : Expr) :=
    withLocalDeclD `h hypothesis fun h => mkLambdaFVars #[h] (project (mkApp branch h))
  return some #[condition, decision, ← projectBranch yes condition,
    ← projectBranch no (mkNot condition)]

private def canExposeOperatorData (config : Config) (info : ConstantInfo) : CoreM Bool := do
  if forbiddenRoots.contains info.name || lawfulBoundaries.contains info.name ||
      info.name == ``ite || info.name == ``dite then return false
  canUnfoldDefault config info

/-- Expose a constructor or conditional without evaluating a choice before auditing it. -/
private def exposeProjectionPayload (payload : Expr) : MetaM Expr := do
  let stop (expr : Expr) := expr.isAppOf ``ite || expr.isAppOf ``dite ||
    expr.getAppFn.constName?.any fun name =>
      forbiddenRoots.contains name || lawfulBoundaries.contains name
  let env ← getEnv
  let head := payload.getAppFn
  let payload ← if !stop payload then
    if let some (.opaqueInfo info) := head.constName?.bind env.find? then
      let value ← instantiateValueLevelParams (.opaqueInfo info) head.constLevels!
        (allowOpaque := true)
      pure <| mkAppN value payload.getAppArgs
    else pure payload
  else pure payload
  withOptions (fun opts => smartUnfolding.set opts false) <|
    withConfig (fun config => { config with iota := false }) <|
      withCanUnfoldPred canExposeOperatorData <|
        withTransparency .all <| whnfHeadPred payload fun expr => pure (!stop expr)

private def expressionConstants (env : Environment) (expr : Expr) : NameSet :=
  let constants := expr.getUsedConstantsAsSet
  if (expr.find? (·.isProj)).isNone then constants else runST fun world => do
    let names ← (ST.mkRef constants : ST world (ST.Ref world NameSet))
    expr.forEach (m := ST world) (ω := world) fun
      | .proj typeName index _ => do
        -- The field's own type can carry dependencies through a kernel projection.
        let projection := do
          let info ← getStructureInfo? env typeName
          let field ← info.fieldNames[index]?
          getProjFnForField? env typeName field
        names.modify fun names =>
          match projection, env.find? typeName with
          | some field, _ => names.insert field
          | none, some (.inductInfo info) => info.ctors.foldl (·.insert ·) names
          | none, _ => names
      | _ => pure ()
    names.get

private def declarationTypesAndRules (info : ConstantInfo) : List Expr :=
  info.type :: match info with
    | .recInfo recursor => recursor.rules.map (·.rhs)
    | _ => []

private def constantDependencies (env : Environment) (info : ConstantInfo)
    (includeValue := true) : Array Name := Id.run do
  let mut expressions := declarationTypesAndRules info
  let checkValue : Bool := match info with
    | .thmInfo _ =>
      let owner := moduleOwnership env info.name
      owner == .project || owner == .generatedProject
    | _ => true
  if includeValue && checkValue then
    if let some value := info.value? (allowOpaque := true) then
      expressions := expressions ++ [value]
  let mut names := #[]
  for expr in expressions do
    for name in expressionConstants env expr do names := names.push name
  return names

private def semanticEdges (env : Environment) (name : Name) :
    StateT AuditResult MetaM (Option (Array Name)) := do
  let state ← get
  if let some edges := state.dependencyCache.dependencies.find? name then return some edges
  let some info := env.find? name | return none
  -- An imported proof's type is still examined. Its value contributes proof-source edges.
  let deferred := state.shareProofSources && isKnownProof env info
  let edges := constantDependencies env info (includeValue := !deferred)
  set { state with
    dependencyCache := { state.dependencyCache with
      dependencies := state.dependencyCache.dependencies.insert name edges }
    deferredProofs := if deferred then state.deferredProofs.insert name else state.deferredProofs }
  return some edges

private def expressionMayReachForbidden (expr : Expr) : StateT AuditResult MetaM Bool := do
  let env ← getEnv
  let state ← get
  let reachable := state.dependencyCache.reachable
  let unreachable := state.dependencyCache.unreachable
  let reaches := fun name => forbiddenRoots.contains name || reachable.contains name
  let boundary := fun name =>
    lawfulBoundaries.contains name || elaborationCallbacks.contains name ||
      elaborationEffects.contains name || unreachable.contains name ||
      state.coveredProofs.contains name || state.coveredDefinitions.contains name
  let names := expressionConstants env expr
  let mut pending : Array (Name × Name) := #[]
  for name in names do
    if reaches name then return true
    unless boundary name do pending := pending.push (name, .anonymous)
  let mut seen : NameSet := {}
  let mut parents : NameMap (List Name) := {}
  let mut sources : Array Name := #[]
  let mut processed := 0
  let mut complete : Bool := true
  while let some (name, parent) := pending.back? do
    pending := pending.pop
    let live := reaches name
    if !live && boundary name then
      continue
    unless parent.isAnonymous do
      parents := parents.insert name (parent :: (parents.find? name).getD [])
    if seen.contains name then continue
    seen := seen.insert name
    if live then
      sources := sources.push name
      continue
    processed := processed + 1
    if processed % 1024 == 0 then
      Core.checkSystem "operator fidelity dependency search"
    let some edges ← semanticEdges env name | do
      complete := false
      modify fun result => { result with
        incomplete := true
        unavailableConstants := result.unavailableConstants.insert name }
      continue
    for dependency in edges do pending := pending.push (dependency, name)
  -- Propagate reachability backward through this search's edges. Exploring each unknown
  -- node's outgoing edges makes the negative results valid even in cyclic components.
  let found := !sources.isEmpty
  let mut live : NameSet := {}
  while let some name := sources.back? do
    sources := sources.pop
    if live.contains name then continue
    live := live.insert name
    for parent in (parents.find? name).getD [] do sources := sources.push parent
  let mut absent := unreachable
  if complete then
    for name in seen do
      unless live.contains name do absent := absent.insert name
  modify fun result => { result with dependencyCache := {
    result.dependencyCache with reachable := reachable ++ live, unreachable := absent } }
  return found

private def rootFree (expressions : Array Expr) : StateT AuditResult MetaM Bool := do
  let state ← get
  if state.incomplete then return false
  let check := expressions.anyM fun e =>
    if e.hasMVar then pure true else expressionMayReachForbidden e
  let (mayReach, updated) ← liftM <| check.run state
  if updated.incomplete then return false
  set updated
  return !mayReach

/-- Record proof dependencies conservatively by following the constants in the expression.
Mathematical statements and data, including emitted declarations, undergo the semantic audit. -/
private def auditProofNames (source : Name) (names : NameSet) (shareSources : Bool) :
    StateT AuditResult MetaM Unit := do
  let env ← getEnv
  let state ← get
  let mut pending := #[]
  for name in names do pending := pending.push (name, source)
  -- The package report is a union of sources. A declaration-indexed query starts with a
  -- fresh visitation set so it can attribute a shared dependency to each caller.
  let mut checked := if shareSources then state.dependencyCache.proofSourcesChecked else {}
  let mut complete := true
  let mut budget := 100000
  while let some (name, origin) := pending.back? do
    pending := pending.pop
    if forbiddenRoots.contains name then
      addRoot .proof name origin (moduleOwnership env origin)
      continue
    if checked.contains name || lawfulBoundaries.contains name || state.coveredProofs.contains name then
      continue
    if budget == 0 then
      modify fun result => { result with
        incomplete := true
        incompleteReason := result.incompleteReason <|> some "proof dependency budget exhausted" }
      return
    if budget % 1024 == 0 then
      Core.checkSystem "operator fidelity proof dependencies"
    budget := budget - 1
    checked := checked.insert name
    let some info := env.find? name | do
      complete := false
      modify fun result => { result with
        incomplete := true
        unavailableConstants := result.unavailableConstants.insert name }
      continue
    let cached := if state.shareProofSources && isKnownProof env info then none
      else state.dependencyCache.dependencies.find? name
    let edges := match cached with
      | some edges => edges
      | none => constantDependencies env info
    for dependency in edges do pending := pending.push (dependency, name)
  if complete && shareSources then
    modify fun result => { result with
      dependencyCache := { result.dependencyCache with proofSourcesChecked := checked } }

private def auditProofDependencies (source : Name) (expr : Expr) (shareSources : Bool) :
    StateT AuditResult MetaM Unit := do
  auditProofNames source (expressionConstants (← getEnv) expr) shareSources

private partial def auditExpr (sourceDeclaration : Name) (ownership : SourceOwnership)
    (kind : DependencyKind) (expr : Expr) (fuel : Nat := 128) (proofOnly := false) :
    StateT AuditResult MetaM Unit := do
  let expr := (← instantiateMVars expr).consumeMData
  -- Binder types and local let values are audited where they are introduced.
  if !expr.hasMVar then
    unless ← expressionMayReachForbidden expr do return
  if fuel == 0 then
    modify fun result => { result with
      incomplete := true
      incompleteReason := result.incompleteReason <|> some "expression depth exhausted" }
    return
  -- The declared type and supplied arguments already give the proof dependencies of a
  -- known proof application. This also covers proof-valued instances stored as definitions.
  if (← get).shareProofSources && !expr.hasMVar then
    let env ← getEnv
    let proofHead := expr.getAppFn.constName?.any fun name =>
      (env.find? name).any (isKnownProof env)
    if kind == .proof || proofHead then
      auditProofDependencies sourceDeclaration expr true
      return
  let proofType? ← if kind == .proof then pure none else
    try
      if ← liftM <| isProof expr then some <$> liftM (inferType expr) else pure none
    catch ex =>
      if ex.isInterrupt then throw ex
      modify fun result => { result with
        incomplete := true
        incompleteReason := result.incompleteReason <|> some "failed to classify a proof subterm" }
      pure none
  let kind ← match proofType? with
    | some type =>
        auditExpr sourceDeclaration ownership .proof type (fuel - 1)
        pure .proof
    | none => pure kind
  let proofOnly := proofOnly && kind != .proof
  let typeKind := if kind == .proof then DependencyKind.proof else .statement
  match expr with
  | .mvar _ =>
      modify fun result => { result with
        incomplete := true
        incompleteReason := result.incompleteReason <|> some "unassigned metavariable" }
  | .forallE name domain body binderInfo =>
      auditExpr sourceDeclaration ownership typeKind domain (fuel - 1) proofOnly
      let state ← get
      let (_, state) ← liftM <| withLocalDecl name binderInfo domain fun localVar =>
        let body := body.instantiate1 localVar
        (auditExpr sourceDeclaration ownership kind body (fuel - 1) proofOnly).run state
      set state
  | .lam name domain body binderInfo =>
      auditExpr sourceDeclaration ownership typeKind domain (fuel - 1) proofOnly
      let state ← get
      let (_, state) ← liftM <| withLocalDecl name binderInfo domain fun localVar =>
        let body := body.instantiate1 localVar
        (auditExpr sourceDeclaration ownership kind body (fuel - 1) proofOnly).run state
      set state
  | .letE name type value body nonDep =>
      auditExpr sourceDeclaration ownership typeKind type (fuel - 1) proofOnly
      auditExpr sourceDeclaration ownership kind value (fuel - 1) proofOnly
      let state ← get
      let (_, state) ← liftM <| withLetDecl name type value (nondep := nonDep) fun localVar =>
        let body := body.instantiate1 localVar
        (auditExpr sourceDeclaration ownership kind body (fuel - 1) proofOnly).run state
      set state
  | _ =>
      let function := expr.getAppFn
      let arguments := expr.getAppArgs
      if proofOnly then
        -- Inspect proofs in the original syntax of discarded fields without evaluating their data.
        for argument in arguments do
          auditExpr sourceDeclaration ownership kind argument (fuel - 1) true
        match function with
        | .proj _ _ payload => auditExpr sourceDeclaration ownership kind payload (fuel - 1) true
        | _ =>
          if function != expr then
            auditExpr sourceDeclaration ownership kind function (fuel - 1) true
        return
      let env ← getEnv
      -- Kernel projections and named projections select the same field.
      if let .proj structureName idx payload := function then
        let field? := (getStructureInfo? env structureName).bind fun info => info.fieldNames[idx]?
        if let some field := field? then
          let projected ← liftM <| mkProjection payload field
          auditExpr sourceDeclaration ownership kind (mkAppN projected arguments) (fuel - 1)
          return
      let projectionInfo? := function.constName?.bind env.getProjectionFnInfo?
      let visibleArguments := match projectionInfo? with
        | none => arguments
        | some info =>
            -- Do not audit the bundled structure argument. Reducing the projection below exposes
            -- only the selected field, while later arguments remain genuine inputs to that field.
            arguments.extract 0 info.numParams ++
              arguments.extract (info.numParams + 1) arguments.size
      -- A projection out of a proof can be audited by examining that proof and its type.
      if kind == .proof then
        if let some info := projectionInfo? then
          if let some payload := arguments[info.numParams]? then
            if ← liftM <| isProof payload then
              auditExpr sourceDeclaration ownership .proof (← liftM <| inferType payload) (fuel - 1)
              auditExpr sourceDeclaration ownership .proof payload (fuel - 1)
              for argument in visibleArguments do
                auditExpr sourceDeclaration ownership .proof argument (fuel - 1)
              return
      if let some name := function.constName? then
        if forbiddenRoots.contains name then
          addRoot kind name sourceDeclaration ownership
          for argument in visibleArguments do
            auditExpr sourceDeclaration ownership kind argument (fuel - 1)
          return
        if lawfulBoundaries.contains name || elaborationCallbacks.contains name ||
            elaborationEffects.contains name || (kind != .proof && projectionInfo?.isNone &&
            (← get).coveredDefinitions.contains name) then
          for argument in visibleArguments do
            auditExpr sourceDeclaration ownership kind argument (fuel - 1)
          return
        -- Projection heads must first reduce against the selected instance.  Treating `Inv.inv`
        -- itself as an ordinary proof callee would skip that reduction and hide `Rat.inv`.
        if projectionInfo?.isNone && (kind == .proof || isTheorem env name) then
          let state ← get
          let seen := state.visitedConstants.contains name || state.coveredProofs.contains name ||
            state.dependencyCache.unreachable.contains name
          unless seen do
            modify fun result =>
              { result with visitedConstants := result.visitedConstants.insert name }
          if !seen then
            if let some info := env.find? name then
              let calleeOwnership := moduleOwnership env name
              if ← expressionMayReachForbidden info.type then
                auditExpr name calleeOwnership .proof info.type (fuel - 1)
              let projectOwned := calleeOwnership == .project || calleeOwnership == .generatedProject
              if projectOwned || !(← liftM <| isProofType info.type) then
                if let some value := info.value? (allowOpaque := true) then
                  if ← expressionMayReachForbidden value then
                    auditExpr name calleeOwnership .proof value (fuel - 1)
          for argument in visibleArguments do
            auditExpr sourceDeclaration ownership kind argument (fuel - 1)
          return
      -- Inspect arguments before reduction: beta/iota reduction may erase proof arguments whose
      -- dependencies still belong in the ownership report.
      for argument in visibleArguments do
        auditExpr sourceDeclaration ownership kind argument (fuel - 1)
      if let some info := projectionInfo? then
        if let some payload := arguments[info.numParams]? then
          -- Proof arguments contribute audit evidence even if the producer or projection
          -- discards them. The selected-field audit handles the data fields.
          for argument in payload.getAppArgs do
            auditExpr sourceDeclaration ownership kind argument (fuel - 1) (proofOnly := true)
      -- The arguments above account for dependencies passed to a root-free constant.
      if projectionInfo?.isNone && function.isConst then
        unless ← expressionMayReachForbidden function do return
      if kind != .proof then
        if let some info := projectionInfo? then
          if let some payload := arguments[info.numParams]? then
            -- Selection can expose a dependency in the receiver or projected field's type.
            if let some declaration := function.constName?.bind env.find? then
              if ← rootFree #[payload, declaration.type] then return
      let (normalized, projectionPayload?) ← try
          match projectionInfo? with
            | some info => do
                match arguments[info.numParams]? with
                | none => pure (expr, none)
                | some structureArg =>
                  let structureValue ← liftM <| exposeProjectionPayload structureArg
                  let projectionCore := mkAppN function <|
                    (arguments.extract 0 info.numParams).push structureValue
                  let selected? ← liftM <| reduceProjectionCore? projectionCore
                  let selected := selected?.map fun field =>
                    mkAppN field (arguments.extract (info.numParams + 1) arguments.size)
                  pure (selected.getD expr, some structureValue)
            | none =>
                if let some name := function.constName? then
                  if let some info := env.find? name then
                    if info.hasValue (allowOpaque := true) then do
                      let value ← liftM <| instantiateValueLevelParams info function.constLevels!
                        (allowOpaque := true)
                      pure (mkAppN value arguments, none)
                    else
                      pure (expr, none)
                  else
                    pure (expr, none)
                else if function.isLambda then
                  pure (function.beta arguments, none)
                else do
                  let value ← liftM <| withCanUnfoldPred canExposeOperatorData <|
                    withTransparency .reducible <| whnf expr
                  pure (value, none)
        catch ex =>
          if ex.isInterrupt then throw ex
          modify fun result => { result with
            incomplete := true
            incompleteReason := result.incompleteReason <|> some "operator reduction failed" }
          pure (expr, none)
      if normalized != expr then
        auditExpr sourceDeclaration ownership kind normalized (fuel - 1)
      else
        if let some info := projectionInfo? then
          if let some payload := arguments[info.numParams]? then
            let exposed := projectionPayload?.getD payload
            let parts? ← liftM <| conditionalProjection? function arguments info.numParams exposed
            if let some parts := parts? then
              for part in parts do
                auditExpr sourceDeclaration ownership kind part (fuel - 1)
            else if kind == .proof then
              -- The unresolved bundle is an input to a proof. Its dependencies are
              -- proof uses even if a data field would require reduction to select.
              auditExpr sourceDeclaration ownership .proof payload (fuel - 1)
            else if ← expressionMayReachForbidden exposed then
              modify fun result => { result with
                incomplete := true
                incompleteReason := result.incompleteReason <|>
                  some s!"cannot select a field of the argument to {function.constName!}" }
            return
        match expr with
        | .app .. => auditExpr sourceDeclaration ownership kind function (fuel - 1)
        | .proj _ _ payload => auditExpr sourceDeclaration ownership kind payload (fuel - 1)
        | .mdata _ body => auditExpr sourceDeclaration ownership kind body (fuel - 1)
        | _ => pure ()

private def auditDeclarationWith (declName : Name) (dependencyCache : DependencyCache)
    (coveredProofs : NameSet) (shareProofSources := false) (coveredDefinitions : NameSet := {}) :
    MetaM AuditResult := do
  let env ← getEnv
  let some info := env.find? declName | return { dependencyCache, coveredProofs, incomplete := true }
  let ownership := moduleOwnership env declName
  let fuel := 512
  let elaboration := isElaborationImplementation env declName info.type
  let implementationEquation ← if isTheorem env declName then
      if isElaborationEquation env declName then pure true else isToolchainBoundaryEquation declName
    else pure false
  -- A callback's defaults are elaboration code. Its parameter and result types are still checked.
  let signature := if elaboration then info.type.replace fun e =>
      if e.isAppOfArity ``optParam 2 || e.isAppOfArity ``autoParam 2 then some e.appFn!.appArg!
      else none
    else info.type
  let action : StateT AuditResult MetaM Unit := do
    unless implementationEquation do
      auditExpr declName ownership .statement signature fuel
    -- Proof dependencies in a signature include the proof arguments and binder types that
    -- can be erased while reducing that signature to its mathematical statement.
    if implementationEquation || coveredProofs.contains declName || signature != info.type then
      auditProofDependencies declName info.type shareProofSources
    if let some value := info.value? (allowOpaque := true) then
      if elaboration || (shareProofSources && isKnownProof env info) then
        auditProofDependencies declName value shareProofSources
        return
      unless ← expressionMayReachForbidden value do return
      let valueKind ← if ← liftM <| isProofType info.type then
          pure .proof
        else
          match info with
          | .thmInfo _ => pure .proof
          | .defnInfo _ | .opaqueInfo _ =>
              if ← liftM <| isPredicateType info.type then pure .statement else pure .data
          | _ => pure .data
      auditExpr declName ownership valueKind value fuel
  let (_, result) ← action.run { dependencyCache, coveredProofs, coveredDefinitions, shareProofSources }
  if result.deferredProofs.isEmpty then return result
  return (← (auditProofNames declName result.deferredProofs true).run result).2

/-- Audit one declaration for semantic and proof dependencies on retired operators. -/
public def auditDeclaration (declName : Name) : MetaM AuditResult :=
  auditDeclarationWith declName {} {}

/-- Audit a standalone elaborated expression. Primarily useful for regression tests and tooling. -/
public def auditExpression (expr : Expr) (kind := DependencyKind.data) : MetaM AuditResult := do
  -- A standalone query can refer to lets introduced by its caller.
  let lets ← (← getLCtx).getFVarIds.filterM fun id => return (← id.getDecl).isLet
  let expr ← mkLetFVars (lets.map mkFVar) expr (generalizeNondepLet := false)
  return (← (auditExpr .anonymous .project kind expr).run {}).2

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
      m!"{.ofConstName use.root} from {.ofConstName use.sourceDeclaration} ({repr use.ownership})"
    return MessageData.joinSep lines.toList Format.line

/-- A proof dependency together with the declaration that contains it. -/
public structure DeclarationProofUse extends ProofUse where
  /-- The declaration whose audit produced this proof dependency. -/
  declaration : Name
  deriving BEq, DecidableEq, Inhabited, Repr

-- A package audit checks selected theorem signatures and bodies at their own declarations.
-- Calls still contribute their actual arguments, including proofs supplied at the use site.
private def coverProofs (env : Environment) (declarations : Array Name) : NameSet :=
  declarations.foldl (init := {}) fun names name =>
    if (env.find? name).any (isKnownProof env) then names.insert name else names

private def coverDefinitions (env : Environment) (declarations : Array Name) : NameSet :=
  declarations.foldl (init := {}) fun names name =>
    match env.find? name with
    | some info =>
      if !isMarkedMeta env name && !isKnownProof env info && info.hasValue (allowOpaque := true) &&
          !isElaborationImplementation env name info.type then names.insert name
      else names
    | none => names

private def collectProofAudit (declarations : Array Name) (coveredProofs : NameSet := {})
    (shareProofSources := false) :
    MetaM (Array DeclarationProofUse × Bool) := do
  let mut uses := #[]
  let mut incomplete := false
  let mut dependencyCache : DependencyCache := {}
  for declaration in declarations do
    let result ← withFreshCache <|
      auditDeclarationWith declaration dependencyCache coveredProofs shareProofSources
    dependencyCache := result.dependencyCache
    incomplete := incomplete || result.incomplete
    for use in result.proofUses do
      uses := uses.push { use with declaration }
  return (uses, incomplete)

/-- Collect proof-only findings. Incomplete traversal prevents returning a complete report. -/
public def collectProofUses (declarations : Array Name) : MetaM (Array DeclarationProofUse) := do
  let (uses, incomplete) ← collectProofAudit declarations
  if incomplete then throwError "Proof dependency report is incomplete."
  return uses

private def logProofUses (uses : Array DeclarationProofUse) (incomplete : Bool) :
    CommandElabM Unit := do
  unless uses.isEmpty do
    let lines := uses.map fun use =>
      m!"{.ofConstName use.declaration}: {.ofConstName use.root} from \
        {.ofConstName use.sourceDeclaration} ({repr use.ownership})"
    logInfo <| MessageData.joinSep lines.toList Format.line
  if !incomplete && uses.isEmpty then
    logInfo "No proof dependencies on retired operators were found."

private def reportProofUses (declarations : Array Name) (coveredProofs : NameSet := {}) :
    CommandElabM Unit := do
  let (uses, incomplete) ← liftTermElabM <| collectProofAudit declarations coveredProofs true
  logProofUses uses incomplete
  if incomplete then
    throwError "Proof dependency report is incomplete."

private structure ScopeAuditReport where
  failures : Array MessageData
  uses : Array DeclarationProofUse
  incomplete : Bool

private def auditBlock (declarations : Array Name) (coveredProofs coveredDefinitions : NameSet)
    (reportProofs : Bool) : MetaM ScopeAuditReport := do
  let mut failures : Array MessageData := #[]
  let mut uses : Array DeclarationProofUse := #[]
  let mut incomplete := false
  let mut dependencyCache : DependencyCache := {}
  for declaration in declarations do
    let result ← withFreshCache <|
      auditDeclarationWith declaration dependencyCache coveredProofs true coveredDefinitions
    dependencyCache := result.dependencyCache
    if reportProofs then
      incomplete := incomplete || result.incomplete
      for use in result.proofUses do
        uses := uses.push { use with declaration }
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
  return { failures, uses, incomplete }

private def enforceSemanticAudit (declarations : Array Name) (reportProofs : Bool := false) :
    CommandElabM Unit := do
  let env ← getEnv
  let coveredProofs := coverProofs env declarations
  let coveredDefinitions := coverDefinitions env declarations
  -- Each block gets its own Meta state and dependency cache. All blocks share the
  -- full coverage sets so that auditing a definition never depends on partition order.
  let reports ← if declarations.size < 2048 then
      let result ← liftTermElabM <| auditBlock declarations coveredProofs coveredDefinitions reportProofs
      pure #[result]
    else do
      let blockSize := Nat.shiftRight (declarations.size + 7) 3
      let tasks ← (Array.range 8).mapM fun index => do
        let start := index * blockSize
        let declarations := declarations.extract start (start + blockSize)
        let run ← Command.wrapAsync (fun () =>
          liftTermElabM <| auditBlock declarations coveredProofs coveredDefinitions reportProofs)
            (← read).cancelTk?
        EIO.asTask (run ())
      tasks.mapM fun task => MonadExcept.ofExcept task.get
  if reportProofs then
    logProofUses (reports.flatMap (·.uses)) (reports.any (·.incomplete))
  let failures := reports.flatMap (·.failures)
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
      let declarations ← liftCoreM Batteries.Tactic.Lint.getDeclsInCurrModule
      reportProofUses declarations (coverProofs (← getEnv) declarations)
  | `(#operator_fidelity_proofs in $project) => do
      let declarations ← liftCoreM <| getScopeDeclarations project.getId.eraseMacroScopes
      reportProofUses declarations (coverProofs (← getEnv) declarations)
  | `(#operator_fidelity in $project) => do
      let declarations ← liftCoreM <| getScopeDeclarations project.getId.eraseMacroScopes
      enforceSemanticAudit declarations
  | `(#operator_fidelity with_proofs in $project) => do
      let declarations ← liftCoreM <| getScopeDeclarations project.getId.eraseMacroScopes
      enforceSemanticAudit declarations (reportProofs := true)

end Mathlib.Linter.OperatorFidelity
