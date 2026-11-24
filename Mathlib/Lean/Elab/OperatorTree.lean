/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Gabriel Ebner, Yi-Jing Tseng
-/
module

public meta import Lean.Elab.Extra
public meta import Lean.PrettyPrinter.Delaborator.Builtins
import Mathlib.Tactic.Linter.Header

/-!
# Elaboration of operator trees with checked division

Slash admits installed division operations outside the native natural and integer carriers.
Exact division retains its unit witness. Euclidean quotients use their named operations.
The enclosing tree can supply a type for ambiguous numerals.
Other operators retain their ordinary coercion behavior.
The tree and its coercion analysis follow the official Lean elaborator in `Lean.Elab.Extra`.
-/

public meta section

namespace Mathlib.Elab.OperatorTree

open Lean Meta Elab Term

/-- Additional rules for unary operations and powers, installed by the algebraic notation module. -/
structure Rules where
  /-- Select a binary operation using the tree's common type and its elaborated operands. -/
  binOp? : Option Expr → Expr → Expr → Expr → TermElabM (Option Expr) := fun _ _ _ _ => pure none
  /-- Select a unary operation using the tree's common type and its elaborated operand. -/
  unOp? : Option Expr → Expr → Expr → TermElabM (Option Expr) := fun _ _ _ => pure none

/-- The native quotient carriers cannot be operands of slash, including through type aliases. -/
private def isNativeDivisionOperand (carrier : Expr) : MetaM Bool := do
  let carrier ← withTransparency .all <| whnf carrier
  return carrier.isConstOf ``Nat || carrier.isConstOf ``Int

/-- A metavariable can still change a carrier whose head is stuck on a reduction.
The parameters of an inductive carrier such as `Fin ?n` do not change its head. -/
private def divisionCarrierStuck (carrier : Expr) : MetaM Bool := do
  let carrier ← withTransparency .all <| whnf carrier
  unless carrier.hasExprMVar do return false
  match carrier.getAppFn with
  | .fvar _ | .forallE .. | .sort _ => return false
  | .const name _ =>
    match ← getConstInfo name with
    | .inductInfo _ | .opaqueInfo _ | .axiomInfo _ | .quotInfo _ => return false
    | _ => return true
  | _ => return true

/-- These carriers use the exact quotient with an invertibility witness, also for pointwise
functions. On a Euclidean domain this keeps the Euclidean quotient at its named operation. -/
private partial def usesCheckedExactDivision (carrier : Expr) : MetaM Bool := do
  let env ← getEnv
  for className in #[`GroupWithZero, `EuclideanDomain] do
    if env.contains className then
      if let .some _ ← trySynthInstance (← mkAppM className #[carrier]) then
        return true
  let reduced ← whnf carrier
  if reduced.isConstOf ``Rat then return true
  match reduced with
  | .forallE name domain body bi =>
    withLocalDecl name bi domain fun x => usesCheckedExactDivision (body.instantiate1 x)
  | _ => return false

private def checkedDivisionOp? (carrier : Expr) : MetaM (Option Expr) := do
  unless (← getEnv).contains `Checked.div do return none
  let .some monoid ← trySynthInstance (← mkAppM `Monoid #[carrier]) | return none
  return some (← mkAppOptM `Checked.div #[some carrier, some monoid])

private def ambientDivisionOp? (lhsType rhsType : Expr) : MetaM (Option Expr) := do
  let resultLevel ← mkFreshLevelMVar
  let levels := [← getDecLevel lhsType, ← getDecLevel rhsType, resultLevel]
  let resultType ← mkFreshExprMVar (mkSort (.succ resultLevel))
  let type := mkApp3 (mkConst ``HDiv levels) lhsType rhsType resultType
  let .some division ← trySynthInstance type | return none
  return some (mkApp4 (mkConst ``HDiv.hDiv levels) lhsType rhsType resultType division)

/-- Select a division on resolved operand types. Checked domains take precedence over ordinary
instance search. Otherwise a monoid can divide by a proved unit when it has no ambient division. -/
private def divisionOp? (lhsType rhsType : Expr) : MetaM (Option Expr) := do
  let homogeneous ← withNewMCtxDepth <| isDefEqGuarded lhsType rhsType
  if homogeneous && (← getEnv).contains `EReal.div then
    if ← withNewMCtxDepth <| isDefEqGuarded lhsType (mkConst `EReal) then
      return some (mkConst `EReal.div)
  if homogeneous && (← usesCheckedExactDivision lhsType) then
    return ← checkedDivisionOp? lhsType
  if let some op ← ambientDivisionOp? lhsType rhsType then return some op
  if homogeneous then checkedDivisionOp? lhsType else pure none

open Lean.PrettyPrinter.Delaborator SubExpr

private def withDivisionInstances {α : Type} (k : DelabM α) : DelabM α :=
  withNewMCtxDepth do
    -- A section term can retain its local declarations without registered local instances.
    let lctx ← getLCtx
    withLCtx lctx #[] <| withLocalInstances (lctx.decls.toList.filterMap id) k

/-- The printer spends at most 2,000 Lean heartbeats on speculative unit synthesis.
`Core.Context.maxHeartbeats` uses the unscaled allocation count. -/
private def divisionPrintHeartbeatLimit : Nat := 2_000_000

/-- Check that slash can reconstruct the omitted proof of the denominator's domain. -/
private def divisionProofAvailable (op lhs rhs : Expr) : MetaM Bool := do
  let ctx ← readThe Core.Context
  let spent := (← IO.getNumHeartbeats) - ctx.initHeartbeats
  let limit := spent + divisionPrintHeartbeatLimit
  -- Leave enough of a finite caller budget for rendering the named operation on failure.
  if ctx.maxHeartbeats != 0 && ctx.maxHeartbeats < limit + divisionPrintHeartbeatLimit then
    return false
  withoutModifyingState <| withTheReader Core.Context ({ · with maxHeartbeats := limit }) <|
      withOptions (fun opts => pp.notation.set opts false) do
    try
      TermElabM.run' <| withoutErrToSorry do
        let app ← elabAppArgs op #[] #[Arg.expr lhs, Arg.expr rhs] none
          (explicit := false) (ellipsis := false) (resultIsOutParamSupport := false)
        synthesizeSyntheticMVarsNoPostponing
        let some proof := (← instantiateMVars app).getAppArgs.back? | return false
        return !proof.hasMVar && !proof.hasSorry
    catch ex =>
      if ex.isInterrupt then throw ex
      return false

/-- Display checked exact division when slash reconstructs the same operation and domain. -/
@[delab app.Checked.div] def delabDiv : Delab :=
  whenNotPPOption getPPExplicit <| whenPPOption getPPNotation <| withOverApp 5 do
  let #[carrier, monoid, lhs, rhs, _] := (← getExpr).getAppArgs | failure
  guard (← withDivisionInstances do
    if ← isNativeDivisionOperand carrier then return false
    let some selected ← divisionOp? carrier carrier | return false
    unless selected.getAppFn.isConstOf `Checked.div do return false
    unless ← withTransparency .instances <| isDefEqGuarded monoid selected.getAppArgs[1]! do
      return false
    divisionProofAvailable selected lhs rhs)
  `($(← withNaryArg 2 delab) / $(← withNaryArg 3 delab))

/-- Display extended-real division when slash can reconstruct its domain witness. -/
@[delab app.EReal.div] def delabERealDiv : Delab :=
  whenNotPPOption getPPExplicit <| whenPPOption getPPNotation <| withOverApp 3 do
    let #[lhs, rhs, _] := (← getExpr).getAppArgs | failure
    guard (← withDivisionInstances do
      let some selected ← divisionOp? (← inferType lhs) (← inferType rhs) | return false
      unless selected.isConstOf `EReal.div do return false
      divisionProofAvailable selected lhs rhs)
    `($(← withNaryArg 0 delab) / $(← withNaryArg 1 delab))

/-- Display an ambient quotient with slash when instance inference selects it. -/
@[app_delab HDiv.hDiv] def delabHDiv : Delab :=
  (whenNotPPOption getPPExplicit <| whenPPOption getPPNotation <| withOverApp 6 do
    let #[lhsType, rhsType, _, inst, _, _] := (← getExpr).getAppArgs | failure
    guard (← withDivisionInstances do
      if (← isNativeDivisionOperand lhsType) || (← isNativeDivisionOperand rhsType) then
        return false
      let some selected ← divisionOp? lhsType rhsType | return false
      unless selected.getAppFn.isConstOf ``HDiv.hDiv do return false
      withTransparency .instances <| isDefEqGuarded inst selected.getAppArgs[3]!)
    `($(← withNaryArg 4 delab) / $(← withNaryArg 5 delab)))
  <|> (withOptionAtCurrPos `pp.notation false <| withOptionAtCurrPos `pp.fieldNotation false delabApp)

/-- Internal elaboration target for a slash at a boundary of a coercion tree. -/
syntax (name := checkedDiv) "checked_div% " term:max term:max : term

private def rejectNativeDivision (lhsType rhsType : Expr) : TermElabM Unit := do
  if (← isNativeDivisionOperand lhsType) || (← isNativeDivisionOperand rhsType) then
    throwError "division notation is unavailable for Nat or Int operands"

private def applyDivisionOp (op lhs rhs : Expr) : TermElabM Expr :=
  elabAppArgs op #[] #[Arg.expr lhs, Arg.expr rhs] none
    (explicit := false) (ellipsis := false) (resultIsOutParamSupport := false)

/-- Elaborate slash on the original operand types first. When they have no division together,
try the ordinary coercions to a common nonnative carrier. -/
@[term_elab checkedDiv]
def elabCheckedDiv : TermElab := fun stx expectedType? => withSynthesizeLight do
  let lhs ← elabTerm stx[1] none
  let rhs ← elabTerm stx[2] none
  let lhsType ← inferType lhs
  let rhsType ← inferType rhs
  rejectNativeDivision lhsType rhsType
  let expectedType? ← expectedType?.mapM instantiateMVars
  let lhsUnknown ← isMVarApp lhsType
  let rhsUnknown ← isMVarApp rhsType
  if lhsUnknown && rhsUnknown then
    discard <| isDefEqGuarded lhsType rhsType
    if let some expectedType := expectedType? then
      unless ← isMVarApp expectedType do
        discard <| isDefEqGuarded lhsType expectedType
    if ← isMVarApp lhsType then tryPostpone
  else if (lhsUnknown && lhs.isFVar) || (rhsUnknown && rhs.isFVar) then
    tryPostpone
  if (← isMVarApp lhsType) || (← isMVarApp rhsType) then
    discard <| isDefEqGuarded lhsType rhsType
  if (← isMVarApp lhsType) || (← isMVarApp rhsType) then
    synthesizeSyntheticMVarsUsingDefault
  let lhsType ← instantiateMVars lhsType
  let rhsType ← instantiateMVars rhsType
  rejectNativeDivision lhsType rhsType
  if (← divisionCarrierStuck lhsType) || (← divisionCarrierStuck rhsType) then
    tryPostpone
    throwError "cannot infer the operand types for division"
  if let some op ← divisionOp? lhsType rhsType then
    rejectNativeDivision lhsType rhsType
    return ← applyDivisionOp op lhs rhs
  if lhsType.hasExprMVar || rhsType.hasExprMVar then tryPostpone
  let candidates := expectedType?.toArray ++ #[lhsType, rhsType]
  for carrier in candidates do
    if (← divisionCarrierStuck carrier) || (← isNativeDivisionOperand carrier) then continue
    if let some (op, lhs, rhs) ← observing? <| withoutErrToSorry do
      let lhs ← ensureHasType (some carrier) lhs
      let rhs ← ensureHasType (some carrier) rhs
      let some op ← divisionOp? carrier carrier | throwUnsupportedSyntax
      pure (op, lhs, rhs)
    then
      rejectNativeDivision (← inferType lhs) (← inferType rhs)
      return ← applyDivisionOp op lhs rhs
  throwError "division notation has no operation for {lhsType} and {rhsType}"

private inductive BinOpKind where
  | regular   -- `binop%`
  | lazy      -- `binop_lazy%`
  | leftact   -- `leftact%`
  | rightact  -- `rightact%`
deriving BEq

private inductive Tree where
  /--
  Leaf of the tree.
  We store the `infoTrees` generated when elaborating `val`. These trees become
  subtrees of the infotree nodes generated for `op` nodes.
  -/
  | term (ref : Syntax) (infoTrees : PersistentArray InfoTree) (val : Expr)
  /--
  `ref` is the original syntax that expanded into `binop%/...`.
  -/
  | binop (ref : Syntax) (kind : BinOpKind) (f : Expr) (lhs rhs : Tree)
  /--
  `ref` is the original syntax that expanded into `unop%`.
  -/
  | unop (ref : Syntax) (f : Expr) (arg : Tree)
  /--
  Used for assembling the info tree. We store this information
  to make sure "go to definition" behaves similarly to notation defined without using `binop%`
  helper elaborator.
  -/
  | macroExpansion (macroName : Name) (stx stx' : Syntax) (nested : Tree)


private partial def toTree (s : Syntax) : TermElabM Tree := do
  /-
  Remark: we used to use `expandMacros` here, but this is a bad idiom
  because we do not record the macro expansion information in the info tree.
  We now manually expand the notation in the `go` function, and save
  the macro declaration names in the `op` nodes.
  -/
  let result ← go s
  synthesizeSyntheticMVars (postpone := .yes)
  return result
where
  go (s : Syntax) := do
    match s with
    | `(binop% $f $lhs $rhs) => processBinOp s .regular f lhs rhs
    | `(binop_lazy% $f $lhs $rhs) => processBinOp s .lazy f lhs rhs
    | `(unop% $f $arg) => processUnOp s f arg
    | `(leftact% $f $lhs $rhs) => processBinOp s .leftact f lhs rhs
    | `(rightact% $f $lhs $rhs) => processBinOp s .rightact f lhs rhs
    | `(($h:hygieneInfo $e)) =>
      if hasCDot e h.getHygieneInfo then
        processLeaf s
      else
        go e
    | _ =>
      withRef s do
        match (← liftMacroM <| expandMacroImpl? (← getEnv) s) with
        | some (macroName, s?) =>
          let s' ← liftMacroM <| liftExcept s?
          withPushMacroExpansionStack s s' do
            return .macroExpansion macroName s s' (← go s')
        | none => processLeaf s
  -- Binary operators keep both operand trees, except the acted-on side of an action.
  processBinOp (ref : Syntax) (kind : BinOpKind) (f lhs rhs : Syntax) := do
    let some f ← resolveId? f | throwUnknownConstantAt f f.getId
    if f.isConstOf ``HDiv.hDiv then
      let term ← withRef ref <| elabTerm (← `(checked_div% $(⟨lhs⟩) $(⟨rhs⟩))) none
      return .term ref (← getResetInfoTrees) term
    -- treat corresponding argument as leaf for `leftact/rightact`
    let lhs ← if kind == .leftact then processLeaf lhs else go lhs
    let rhs ← if kind == .rightact then processLeaf rhs else go rhs
    return .binop ref kind f lhs rhs
  -- Unary operators keep their operand tree.
  processUnOp (ref : Syntax) (f arg : Syntax) := do
    let some f ← resolveId? f | throwUnknownConstantAt f f.getId
    return .unop ref f (← go arg)
  -- Leaves are elaborated without an expected type, as in the official elaborator.
  processLeaf (s : Syntax) := do
    let e ← elabTerm s none
    let info ← getResetInfoTrees
    return .term s info e

-- Auxiliary function used at `analyze`
private def hasCoe (fromType toType : Expr) : TermElabM Bool := do
  if (← getEnv).contains ``CoeT then
    withLocalDeclD `x fromType fun x => do
    match ← coerceSimple? x toType with
    | .some _ => return true
    | .none   => return false
    | .undef  => return false -- TODO: should we do something smarter here?
  else
    return false

private structure AnalyzeResult where
  max?            : Option Expr := none
  /-- `true` if there are two types `α` and `β` where we don't have coercions in any direction. -/
  hasUncomparable : Bool := false
  /-- `true` if there are any leaf terms with an unknown type (according to `isUnknown`). -/
  hasUnknown      : Bool := false

private def isUnknown : Expr → Bool
  | .mvar ..        => true
  | .app f _        => isUnknown f
  | .letE _ _ _ b _ => isUnknown b
  | .mdata _ b      => isUnknown b
  | _               => false

private def analyze (t : Tree) (expectedType? : Option Expr) : TermElabM AnalyzeResult := do
  let max? ←
    match expectedType? with
    | none => pure none
    | some expectedType =>
      let expectedType := (← instantiateMVars expectedType).cleanupAnnotations
      if isUnknown expectedType then pure none else pure (some expectedType)
  (go t *> get).run' { max? }
where
   go (t : Tree) : StateRefT AnalyzeResult TermElabM Unit := do
     unless (← get).hasUncomparable do
       match t with
       | .macroExpansion _ _ _ nested => go nested
       | .binop _ .leftact  _ _ rhs => go rhs
       | .binop _ .rightact _ lhs _ => go lhs
       | .binop _ _ _ lhs rhs => go lhs; go rhs
       | .unop _ _ arg => go arg
       | .term _ _ val =>
         let type := (← instantiateMVars (← inferType val)).cleanupAnnotations
         if isUnknown type then
           modify fun s => { s with hasUnknown := true }
         else
           match (← get).max? with
           | none     => modify fun s => { s with max? := type }
           | some max =>
             /-
             Prevent assignment of metavariables in the candidate types. Abort on stuck
             constraints before unfolding, as in the pinned Lean operator elaborator.
             This preserves coercions such as Nat → Int and Name → Option ?m without
             expensive unfolding or premature default-instance assignments.
             -/
             unless (← withNewMCtxDepth <|
                 withConfig (fun config => { config with isDefEqStuckEx := true }) <|
                   isDefEqGuarded max type) do
               if (← hasCoe type max) then
                 return ()
               else if (← hasCoe max type) then
                 modify fun s => { s with max? := type }
               else
                 trace[Elab.binop] "uncomparable types: {max}, {type}"
                 modify fun s => { s with hasUncomparable := true }


/-- Apply an operation to elaborated operands, allowing its default proof arguments to run. -/
def checkedApp (name : Name) (args : Array Expr) : TermElabM Expr := do
  elabAppArgs (← mkConstWithFreshMVarLevels name) #[] (args.map Arg.expr)
    none (explicit := false) (ellipsis := false) (resultIsOutParamSupport := false)

private def mkBinOp (rules : Rules) (maxType? : Option Expr) (lazy : Bool)
    (f lhs rhs : Expr) : TermElabM Expr := do
  if let some result ← rules.binOp? maxType? f lhs rhs then return result
  let rhs ← if lazy then mkFunUnit rhs else pure rhs
  elabAppArgs f #[] #[Arg.expr lhs, Arg.expr rhs] none
    (explicit := false) (ellipsis := false) (resultIsOutParamSupport := false)

private def mkUnOp (rules : Rules) (maxType? : Option Expr) (f arg : Expr) : TermElabM Expr := do
  if let some result ← rules.unOp? maxType? f arg then return result
  elabAppArgs f #[] #[Arg.expr arg] none
    (explicit := false) (ellipsis := false) (resultIsOutParamSupport := false)

/-- Construct the expression of an operator tree. `maxType?` is the uniform type of the tree,
when the analysis determined one; it resolves pending operand types of checked operations. -/
private def toExprCore (rules : Rules) (t : Tree) (maxType? : Option Expr) : TermElabM Expr := do
  match t with
  | .term _ trees e =>
    modifyInfoState (fun s => { s with trees := s.trees ++ trees }); return e
  | .binop ref kind f lhs rhs =>
    withRef ref <|
      withTermInfoContext' .anonymous ref do
        mkBinOp rules maxType? (kind == .lazy) f (← toExprCore rules lhs maxType?)
          (← toExprCore rules rhs maxType?)
  | .unop ref f arg =>
    withRef ref <|
      withTermInfoContext' .anonymous ref do
        mkUnOp rules maxType? f (← toExprCore rules arg maxType?)
  | .macroExpansion macroName stx stx' nested =>
    withRef stx <|
      withTermInfoContext' macroName stx <|
        withMacroExpansion stx stx' <|
          toExprCore rules nested maxType?

/--
Auxiliary function to decide whether we should coerce `f`'s argument to `maxType` or not.
- `f` is a binary operator.
- `lhs == true` (`lhs == false`) if are trying to coerce the left-argument (right-argument).
This function assumes `f` is a heterogeneous operator (e.g., `HAdd.hAdd`, `HMul.hMul`, etc).
It returns true IF
- `f` is a constant of the form `Cls.op` where `Cls` is a class name, and
- `maxType` is of the form `C ...` where `C` is a constant, and
- There are more than one default instance. That is, it assumes the class `Cls` for the
heterogeneous operator `f`, and
  always has the monomorphic instance. (e.g., for `HAdd`, we have `instance [Add α] : HAdd α α α`),
  and
- If `lhs == true`, then there is a default instance of the form `Cls _ (C ..) _`, and
- If `lhs == false`, then there is a default instance of the form `Cls (C ..) _ _`.

The motivation is to support default instances such as
```
@[default_instance high]
instance [Mul α] : HMul α (Array α) (Array α) where
  hMul a as := as.map (a * ·)

#eval 2 * #[3, 4, 5]
```
If the type of an argument is unknown we should not coerce it to `maxType` because it would prevent
the default instance above from being even tried.
-/
private def hasHeterogeneousDefaultInstances (f : Expr) (maxType : Expr)
    (lhs : Bool) : MetaM Bool := do
  let .const fName .. := f | return false
  let .const typeName .. := maxType.getAppFn | return false
  let className := fName.getPrefix
  let defInstances ← getDefaultInstances className
  if defInstances.length ≤ 1 then return false
  for (instName, _) in defInstances do
    if let .app (.app (.app _heteroClass lhsType) rhsType) _resultType :=
        (← getConstInfo instName).type.getForallBody then
      if  lhs && rhsType.isAppOf typeName then return true
      if !lhs && lhsType.isAppOf typeName then return true
  return false

/--
Return `true` if polymorphic function `f` has a homogeneous instance of `maxType`.
The coercions to `maxType` only makes sense if such instance exists.

For example, suppose `maxType` is `Int`, and `f` is `HPow.hPow`. Then,
adding coercions to `maxType` only make sense if we have an instance `HPow Int Int Int`.
-/
private def hasHomogeneousInstance (f maxType : Expr) : TermElabM Bool := do
  let .const fName .. := f | return false
  let className := fName.getPrefix
  try
    let inst ← mkAppM className #[maxType, maxType, maxType]
    return (← trySynthInstance inst) matches .some _
  catch _ =>
    return false

mutual
  /--
  Try to coerce elements in the `t` to `maxType` when needed.
  If the type of an element in `t` is unknown we only coerce it to `maxType` if `maxType` does not
  have heterogeneous
  default instances. This extra check is approximated by `hasHeterogeneousDefaultInstances`.

  Remark: If `maxType` does not implement heterogeneous default instances, we do want to assign
  unknown types `?m` to
  `maxType` because it produces better type information propagation. Our test suite has many tests
  that would break if
  we don't do this. For example, consider the term
  ```
  eq_of_isEqvAux a b hsz (i+1) (Nat.succ_le_of_lt h) heqv.2
  ```
  `Nat.succ_le_of_lt h` type depends on `i+1`, but `i+1` only reduces to `Nat.succ i` if we know
  that `1` is a `Nat`.
  There are several other examples like that in our test suite, and one can find them by just
  replacing the
  `← hasHeterogeneousDefaultInstances f maxType lhs` test with `true`


  Remark: if `hasHeterogeneousDefaultInstances` implementation is not good enough we should refine
  it in the future.
-/
  private partial def applyCoe (rules : Rules) (t : Tree) (maxType : Expr) (isPred : Bool) :
      TermElabM Tree := do
    go t none false isPred
  where
    go (t : Tree) (f? : Option Expr) (lhs : Bool) (isPred : Bool) : TermElabM Tree := do
      match t with
      | .binop ref .leftact f lhs rhs =>
        return .binop ref .leftact f lhs (← go rhs none false false)
      | .binop ref .rightact f lhs rhs =>
        return .binop ref .rightact f (← go lhs none false false) rhs
      | .binop ref kind f lhs rhs =>
        /-
          We only keep applying coercions to `maxType` if `f` is predicate or
          `f` has a homogeneous instance with `maxType`. See `hasHomogeneousInstance` for additional
          details.

          Remark: We assume `binrel%` elaborator is only used with homogeneous predicates.
        -/
        if (← pure isPred <||> hasHomogeneousInstance f maxType) then
          return .binop ref kind f (← go lhs f true false) (← go rhs f false false)
        else
          let r ← withRef ref do
            mkBinOp rules none (kind == .lazy) f (← toExpr rules lhs none) (← toExpr rules rhs none)
          let infoTrees ← getResetInfoTrees
          return .term ref infoTrees r
      | .unop ref f arg =>
        return .unop ref f (← go arg none false false)
      | .term ref trees e =>
        let type := (← instantiateMVars (← inferType e)).cleanupAnnotations
        trace[Elab.binop] "visiting {e} : {type} =?= {maxType}"
        if isUnknown type then
          if let some f := f? then
            if (← hasHeterogeneousDefaultInstances f maxType lhs) then
              -- See comment at `hasHeterogeneousDefaultInstances`
              return t
        if (← isDefEqGuarded maxType type) then
          return t
        else
          trace[Elab.binop] "added coercion: {e} : {type} => {maxType}"
          withRef ref <| return .term ref trees (← mkCoe maxType e)
      | .macroExpansion macroName stx stx' nested =>
        withRef stx <| withPushMacroExpansionStack stx stx' do
          return .macroExpansion macroName stx stx' (← go nested f? lhs isPred)

  private partial def toExpr (rules : Rules) (tree : Tree) (expectedType? : Option Expr) :
      TermElabM Expr := do
    let r ← analyze tree expectedType?
    trace[Elab.binop] "hasUncomparable: {r.hasUncomparable}, \
      hasUnknown: {r.hasUnknown}, maxType: {r.max?}"
    if r.hasUncomparable || r.max?.isNone then
      let result ← toExprCore rules tree none
      ensureHasType expectedType? result
    else
      let result ← toExprCore rules (← applyCoe rules tree r.max?.get! (isPred := false)) r.max?
      unless r.hasUnknown do
        -- Record the resulting maxType calculation.
        -- We can do this when all the types are known, since in this case `hasUncomparable` is
        -- valid.
        -- If they're not known, recording maxType like this can lead to heterogeneous operations
        -- failing to elaborate.
        discard <| isDefEqGuarded (← inferType result) r.max?.get!
      trace[Elab.binop] "result: {result}"
      ensureHasType expectedType? result

end

/-- Elaborate an operator tree, using the expected type to guide coercions. -/
def elabOp (rules : Rules) : TermElab := fun stx expectedType? => withSynthesizeLight do
  toExpr rules (← toTree stx) expectedType?

/-- Elaborate the ordinary binary operator notation `binop%`. -/
@[term_elab Lean.Parser.Term.binop] def elabBinOp : TermElab := elabOp {}

/-- Elaborate `binop_lazy%`, passing the right operand as a thunk. -/
@[term_elab Lean.Parser.Term.binop_lazy] def elabBinOpLazy : TermElab := elabOp {}

/-- Elaborate `leftact%`, where the left operand acts on the right operand. -/
@[term_elab Lean.Parser.Term.leftact] def elabLeftact : TermElab := elabOp {}

/-- Elaborate `rightact%`, where the right operand acts on the left operand. -/
@[term_elab Lean.Parser.Term.rightact] def elabRightact : TermElab := elabOp {}

/-- Elaborate unary operators through the common operator tree. -/
@[term_elab Lean.Parser.Term.unop] def elabUnOp : TermElab := elabOp {}

/--
Elaboration functions for `binrel%` and `binrel_no_prop%` notations.
We use the infrastructure for `binop%` to make sure we propagate information between the left and
right hand sides
of a binary relation.

- `binrel% R x y` elaborates `R x y` using the `binop%/...` expression trees in both `x` and `y`.
  It is similar to how `binop% R x y` elaborates but with a significant difference:
  it does not use the expected type when computing the types of the operands.
- `binrel_no_prop% R x y` elaborates `R x y` like `binrel% R x y`, but if the resulting type for `x`
and `y`
  is `Prop` they are coerced to `Bool`.
  This is used for relations such as `==` which do not support `Prop`, but we still want
  to be able to write `(5 > 2) == (2 > 1)` for example.
-/
def elabBinRelCore (rules : Rules) (noProp : Bool) (stx : Syntax)
    (expectedType? : Option Expr) : TermElabM Expr := do
  match (← resolveId? stx[1]) with
  | some f => withSynthesizeLight do
    /-
    We used to use `withSynthesize (mayPostpone := true)` here instead of `withSynthesizeLight`
    here.
    It seems too much to apply default instances at binary relations. For example, we cannot
    elaborate
    ```
    def as : List Int := [-1, 2, 0, -3, 4]
    #eval as.map fun a => ite (a ≥ 0) [a] []
    ```
    The problem is that when elaborating `a ≥ 0` we don't know yet that `a` is an `Int`.
    Then, by applying default instances, we apply the default instance to `0` that forces it to
    become an `Int`,
    and Lean infers that `a` has type `Nat`.
    Then, later we get a type error because `as` is `List Int` instead of `List Nat`.
    This behavior is quite counterintuitive since if we avoid this elaborator by writing
    ```
    def as : List Int := [-1, 2, 0, -3, 4]
    #eval as.map fun a => ite (GE.ge a 0) [a] []
    ```
    everything works.
    However, there is a drawback of using `withSynthesizeLight` instead of `withSynthesize
    (mayPostpone := true)`.
    The following cannot be elaborated
    ```
    have : (0 == 1) = false := rfl
    ```
    We get a type error at `rfl`. `0 == 1` only reduces to `false` after we have applied the default
    instances that force
    the numeral to be `Nat`. We claim this is defensible behavior because the same happens if we do
    not use this elaborator.
    ```
    have : (BEq.beq 0 1) = false := rfl
    ```
    We can improve this failure in the future by applying default instances before reporting a type
    mismatch.
    -/
    let lhsStx := stx[2]
    let rhsStx := stx[3]
    let lhs ← withRef lhsStx <| toTree lhsStx
    let rhs ← withRef rhsStx <| toTree rhsStx
    let tree := .binop stx .regular f lhs rhs
    let r ← analyze tree none
    trace[Elab.binrel] "hasUncomparable: {r.hasUncomparable}, \
      hasUnknown: {r.hasUnknown}, maxType: {r.max?}"
    if r.hasUncomparable || r.max?.isNone then
      -- Use default elaboration strategy + `toBoolIfNecessary`
      let lhs ← toExprCore rules lhs none
      let rhs ← toExprCore rules rhs none
      let lhs ← withRef lhsStx <| toBoolIfNecessary lhs
      let rhs ← withRef rhsStx <| toBoolIfNecessary rhs
      let lhsType ← inferType lhs
      let rhs ← withRef rhsStx <| ensureHasType lhsType rhs
      elabAppArgs f #[] #[Arg.expr lhs, Arg.expr rhs] expectedType?
        (explicit := false) (ellipsis := false) (resultIsOutParamSupport := false)
    else
      let mut maxType := r.max?.get!
      -- Coerce `Prop` to `Bool` for `binrel_no_prop%`; see `toBoolIfNecessary`.
      if noProp then
        if (← withNewMCtxDepth <| isDefEq maxType (mkSort Level.zero)) then
          maxType := Lean.mkConst ``Bool
      let result ← toExprCore rules (← applyCoe rules tree maxType (isPred := true)) (some maxType)
      trace[Elab.binrel] "result: {result}"
      return result
  | none   => throwUnknownConstantAt stx[1] stx[1].getId
where
  /-- If `noProp == true` and `e` has type `Prop`, then coerce it to `Bool`. -/
  toBoolIfNecessary (e : Expr) : TermElabM Expr := do
    if noProp then
      -- We use `withNewMCtxDepth` to make sure metavariables are not assigned
      if (← withNewMCtxDepth <| isDefEq (← inferType e) (mkSort Level.zero)) then
        return (← ensureHasType (Lean.mkConst ``Bool) e)
    return e

/-- Elaborate `binrel%` by coordinating coercions between the operands. -/
@[term_elab Lean.Parser.Term.binrel] def elabBinRel : TermElab := elabBinRelCore {} false

/-- Elaborate `binrel_no_prop%`, coercing propositional operands to `Bool`. -/
@[term_elab Lean.Parser.Term.binrel_no_prop] def elabBinRelNoProp : TermElab :=
  elabBinRelCore {} true

end Mathlib.Elab.OperatorTree
