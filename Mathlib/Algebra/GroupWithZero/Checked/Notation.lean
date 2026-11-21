/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Gabriel Ebner, Yi-Jing Tseng
-/
module

public meta import Lean.Elab.Extra
public import Mathlib.Algebra.GroupWithZero.Checked
public import Mathlib.Data.Rat.Init

/-!
# Ordinary notation for inversion and division by invertible elements

In a monoid without an ambient inverse, such as a group with zero or a field, `a⁻¹`, `a / b` and
`a ^ n` for an integer `n` elaborate to the operations of `Mathlib.Algebra.GroupWithZero.Checked`,
with invertibility evidence found by `checked_unit`. The same operations are displayed with this
ordinary notation.

On a Euclidean domain, `a / b` uses the Euclidean quotient with nonzero divisor, except where
exact division is already selected or the carrier has Lean's native natural or integer division.

The operator-tree algorithm follows the pinned official Lean elaborator in Lean/Elab/Extra.lean.
Coercions are chosen for the complete expression before inverse, division, or integer-power
applications are constructed. Selected operations use a unit or nonzero obligation.
Genuine group operations and natural powers retain their ordinary elaborated heads.
-/

public meta section

namespace Checked.Elab.Op

open Lean Meta Elab Term

private partial def selectedCarrier (carrier : Expr) : TermElabM Bool := do
  let carrier ← instantiateMVars carrier
  -- Preserve named carriers while looking up instances registered on those names. The query may
  -- fail, for example when `GroupWithZero` is not visible from a public declaration; the carrier
  -- is then not selected.
  if !carrier.hasExprMVar then
    let selected ← try
        pure (← synthInstance? (← mkAppM ``GroupWithZero #[carrier])).isSome
      catch _ => pure false
    if selected then return true
  let reduced ← whnf carrier
  if reduced.isConstOf ``Rat then return true
  match reduced with
  | .forallE name domain body bi =>
    withLocalDecl name bi domain fun x => selectedCarrier (body.instantiate1 x)
  | _ => return false

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
  Remark: ew used to use `expandMacros` here, but this is a bad idiom
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


private def checkedApp (name : Name) (args : Array Expr) : TermElabM Expr := do
  elabAppArgs (← mkConstWithFreshMVarLevels name) #[] (args.map Arg.expr)
    none (explicit := false) (ellipsis := false) (resultIsOutParamSupport := false)

/-- Whether an instance exists. A query that is stuck on metavariables counts as absent; it must
not escape as an internal exception. -/
private def hasInstance (name : Name) (args : Array Expr) : TermElabM Bool := do
  try
    return (← synthInstance? (← mkAppM name args)).isSome
  catch _ =>
    return false

/-- Euclidean domains are defined downstream. Look up the class in the elaboration environment
so foundational imports continue to work without it. Lean's integer and natural division use
their native operations. -/
private def usesEuclideanQuotient (carrier : Expr) : TermElabM Bool := do
  unless (← getEnv).contains `EuclideanDomain do return false
  if carrier.isConstOf ``Int || carrier.isConstOf ``Nat then return false
  hasInstance `EuclideanDomain #[carrier]

/-- The type of an operand of a checked operation can still be a metavariable, for instance the
output type of a power whose exponent type is pending a default instance. When the operator tree
has a known uniform type that is a checked carrier, the operand has that type, as the homogeneous
instance would eventually require. -/
private def alignOperandType (maxType? : Option Expr) (type : Expr) (division := false) :
    TermElabM Expr := do
  let type ← instantiateMVars type
  unless type.hasExprMVar do return type
  let some maxType := maxType? | return type
  let maxType ← instantiateMVars maxType
  if maxType.hasExprMVar then return type
  unless (← selectedCarrier maxType) || (division && (← usesEuclideanQuotient maxType)) do
    return type
  if ← isDefEqGuarded type maxType then instantiateMVars type else return type

/-- Recover supplied unit data after coercion insertion. Every recovered value is checked
against the original expression, including the monoid instance used by its operations. -/
private partial def recoverUnit? (value : Expr) : TermElabM (Option Expr) := do
  let value ← instantiateMVars value
  let accept (u : Expr) : TermElabM (Option Expr) := do
    let v ← mkAppM ``Units.val #[u]
    if ← isDefEqGuarded v value then return some u else return none
  let recover (e : Expr) : TermElabM (Option Expr) := do
    if e.isAppOf ``Units.val then
      return ← accept e.getAppArgs.back!
    if let .proj ``Units 0 u := e then
      return ← accept u
    if e.isAppOf ``HMul.hMul || e.isAppOf ``Mul.mul then
      let args := e.getAppArgs
      let some u ← recoverUnit? args[args.size - 2]! | return none
      let some v ← recoverUnit? args.back! | return none
      return ← accept (← mkAppM ``HMul.hMul #[u, v])
    if e.isAppOf ``HPow.hPow || e.isAppOf ``Pow.pow then
      let args := e.getAppArgs
      let n := args.back!
      unless (← whnf (← inferType n)).isConstOf ``Nat do return none
      let some u ← recoverUnit? args[args.size - 2]! | return none
      return ← accept (← mkAppM ``HPow.hPow #[u, n])
    return none
  if let some u ← recover value then return some u
  let reduced ← withReducible <| whnf value
  if reduced != value then recover reduced else return none

private def mkBinOp (maxType? : Option Expr) (lazy : Bool) (f : Expr) (lhs rhs : Expr) :
    TermElabM Expr := do
  let mut lhsType ← instantiateMVars (← inferType lhs)
  let mut rhsType ← instantiateMVars (← inferType rhs)
  if f.isConstOf ``HDiv.hDiv then
    lhsType ← alignOperandType maxType? lhsType (division := true)
    rhsType ← alignOperandType maxType? rhsType (division := true)
    -- An operand type with its own division, such as `ℕ`, `ℤ` or a group whose type still has a
    -- placeholder, decides the operation, so a pending type need not postpone the quotient.
    let ambient (type : Expr) : TermElabM Bool := do
      return !(← selectedCarrier type) && !(← usesEuclideanQuotient type) &&
        (← hasInstance ``HDiv #[type, type, type])
    if (lhsType.hasExprMVar || rhsType.hasExprMVar) && !(← ambient lhsType) &&
        !(← ambient rhsType) then
      tryPostpone
    if ← isDefEqGuarded lhsType rhsType then
      let exact ← selectedCarrier rhsType
      if !exact && (← usesEuclideanQuotient rhsType) then
        return ← checkedApp `EuclideanDomain.quotient #[lhs, rhs]
      if exact ||
          (!(← hasInstance ``HDiv #[lhsType, rhsType, lhsType]) &&
            (← hasInstance ``Monoid #[rhsType])) then
        if let some u ← recoverUnit? rhs then
          return ← mkAppM ``divp #[lhs, u]
        return ← checkedApp ``Checked.div #[lhs, rhs]
  if f.isConstOf ``HPow.hPow && (← whnf rhsType).isConstOf ``Int then
    lhsType ← alignOperandType maxType? lhsType
    -- A base type with a placeholder postpones the power unless it already has its own integer
    -- powers, as a group of permutations of a pending subtype has.
    if lhsType.hasExprMVar && !(← hasInstance ``Pow #[lhsType, rhsType]) then tryPostpone
    if (← selectedCarrier lhsType) ||
        (!(← hasInstance ``Pow #[lhsType, rhsType]) &&
          (← hasInstance ``Monoid #[lhsType])) then
      if let some u ← recoverUnit? lhs then
        return ← mkAppM ``Units.val #[← mkAppM ``HPow.hPow #[u, rhs]]
      return ← checkedApp ``Checked.zpow #[lhs, rhs]
  let mut rhs := rhs
  if lazy then
    rhs ← mkFunUnit rhs
  elabAppArgs f #[] #[Arg.expr lhs, Arg.expr rhs] none
    (explicit := false) (ellipsis := false) (resultIsOutParamSupport := false)

private def mkUnOp (maxType? : Option Expr) (f : Expr) (arg : Expr) : TermElabM Expr := do
  if f.isConstOf ``Inv.inv then
    let carrier ← alignOperandType maxType? (← inferType arg)
    if carrier.hasExprMVar && !(← hasInstance ``Inv #[carrier]) then tryPostpone
    if (← selectedCarrier carrier) ||
        (!(← hasInstance ``Inv #[carrier]) && (← hasInstance ``Monoid #[carrier])) then
      if let some u ← recoverUnit? arg then
        return ← mkAppM ``Units.val #[← mkAppM ``Inv.inv #[u]]
      return ← checkedApp ``Checked.inv #[arg]
  elabAppArgs f #[] #[Arg.expr arg] none
    (explicit := false) (ellipsis := false) (resultIsOutParamSupport := false)

/-- Construct the expression of an operator tree. `maxType?` is the uniform type of the tree,
when the analysis determined one; it resolves pending operand types of checked operations. -/
private def toExprCore (t : Tree) (maxType? : Option Expr) : TermElabM Expr := do
  match t with
  | .term _ trees e =>
    modifyInfoState (fun s => { s with trees := s.trees ++ trees }); return e
  | .binop ref kind f lhs rhs =>
    withRef ref <|
      withTermInfoContext' .anonymous ref do
        mkBinOp maxType? (kind == .lazy) f (← toExprCore lhs maxType?)
          (← toExprCore rhs maxType?)
  | .unop ref f arg =>
    withRef ref <|
      withTermInfoContext' .anonymous ref do
        mkUnOp maxType? f (← toExprCore arg maxType?)
  | .macroExpansion macroName stx stx' nested =>
    withRef stx <|
      withTermInfoContext' macroName stx <|
        withMacroExpansion stx stx' <|
          toExprCore nested maxType?

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
private def hasHomogeneousInstance (f : Expr) (maxType : Expr) : TermElabM Bool := do
  if f.isConstOf ``HDiv.hDiv then
    if (← selectedCarrier maxType) || (← hasInstance ``Monoid #[maxType]) then
      return true
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
  private partial def applyCoe (t : Tree) (maxType : Expr) (isPred : Bool) : TermElabM Tree := do
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
            mkBinOp none (kind == .lazy) f (← toExpr lhs none) (← toExpr rhs none)
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

  private partial def toExpr (tree : Tree) (expectedType? : Option Expr) : TermElabM Expr := do
    let r ← analyze tree expectedType?
    trace[Elab.binop] "hasUncomparable: {r.hasUncomparable}, \
      hasUnknown: {r.hasUnknown}, maxType: {r.max?}"
    if r.hasUncomparable || r.max?.isNone then
      let result ← toExprCore tree none
      ensureHasType expectedType? result
    else
      let result ← toExprCore (← applyCoe tree r.max?.get! (isPred := false)) r.max?
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
def elabOp : TermElab := fun stx expectedType? => do
  toExpr (← toTree stx) expectedType?

/-- Elaborate the ordinary binary operator notation `binop%`. -/
@[term_elab Lean.Parser.Term.binop] def elabBinOp : TermElab := elabOp

/-- Elaborate `binop_lazy%`, passing the right operand as a thunk. -/
@[term_elab Lean.Parser.Term.binop_lazy] def elabBinOpLazy : TermElab := elabOp

/-- Elaborate `leftact%`, where the left operand acts on the right operand. -/
@[term_elab Lean.Parser.Term.leftact] def elabLeftact : TermElab := elabOp

/-- Elaborate `rightact%`, where the right operand acts on the left operand. -/
@[term_elab Lean.Parser.Term.rightact] def elabRightact : TermElab := elabOp

/-- Elaborate unary operators through the common operator tree. -/
@[term_elab Lean.Parser.Term.unop] def elabUnOp : TermElab := elabOp

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
def elabBinRelCore (noProp : Bool) (stx : Syntax)
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
      let lhs ← toExprCore lhs none
      let rhs ← toExprCore rhs none
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
      let result ← toExprCore (← applyCoe tree maxType (isPred := true)) (some maxType)
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
@[term_elab Lean.Parser.Term.binrel] def elabBinRel : TermElab := elabBinRelCore false

/-- Elaborate `binrel_no_prop%`, coercing propositional operands to `Bool`. -/
@[term_elab Lean.Parser.Term.binrel_no_prop] def elabBinRelNoProp : TermElab := elabBinRelCore true

/-- The elaboration target of `a⁻¹`. It is a leaf of any surrounding operator tree, as in the
official elaborator, where `⁻¹` is ordinary notation for `Inv.inv`. -/
syntax (name := checkedInv) "checked_inv% " term:max : term

macro_rules
  | `($a⁻¹) => `(checked_inv% $a)

/-- Elaborate `a⁻¹`. The operand is elaborated against the expected type, as for
`Inv.inv : α → α`. The checked inverse is used exactly when the operand's type is a checked
carrier or a monoid without an ambient inverse; supplied unit data gives the inverse unit. -/
@[term_elab checkedInv] def elabCheckedInv : TermElab := fun stx expectedType? => do
  match stx with
  | `(checked_inv% $a) =>
    let expected? ← match expectedType? with
      | some type => do
        let type ← instantiateMVars type
        pure (if type.hasExprMVar then none else some type)
      | none => pure none
    let arg ← match expected? with
      | some type => elabTermEnsuringType a type
      | none => elabTerm a none
    -- A known expected type is the carrier: the operand was checked against it, and its own
    -- inferred type may only unfold to it, as for a type defined by `def`.
    let carrier ← match expected? with
      | some type => pure type
      | none => instantiateMVars (← inferType arg)
    if carrier.hasExprMVar && !(← hasInstance ``Inv #[carrier]) then tryPostpone
    if !carrier.hasExprMVar then
      if (← selectedCarrier carrier) ||
          (!(← hasInstance ``Inv #[carrier]) && (← hasInstance ``Monoid #[carrier])) then
        if let some u ← recoverUnit? arg then
          return ← mkAppM ``Units.val #[← mkAppM ``Inv.inv #[u]]
        return ← elabAppArgs (mkApp (← mkConstWithFreshMVarLevels ``Checked.inv) carrier) #[]
          #[Arg.expr arg] none (explicit := false) (ellipsis := false)
          (resultIsOutParamSupport := false)
      return ← elabAppArgs (mkApp (← mkConstWithFreshMVarLevels ``Inv.inv) carrier) #[]
        #[Arg.expr arg] expectedType? (explicit := false) (ellipsis := false)
        (resultIsOutParamSupport := false)
    elabAppArgs (← mkConstWithFreshMVarLevels ``Inv.inv) #[] #[Arg.expr arg] expectedType?
      (explicit := false) (ellipsis := false) (resultIsOutParamSupport := false)
  | _ => throwUnsupportedSyntax

end Checked.Elab.Op

namespace Checked.Delab

/-- Display a checked inverse as `a⁻¹`. -/
@[app_unexpander Checked.inv] def unexpandInv : Lean.PrettyPrinter.Unexpander
  | `($_ $a $_) => `($a⁻¹)
  | _ => throw ()

/-- Display checked division as `a / b`. -/
@[app_unexpander Checked.div] def unexpandDiv : Lean.PrettyPrinter.Unexpander
  | `($_ $a $b $_) => `($a / $b)
  | _ => throw ()

/-- Display a checked integer power as `a ^ n`. -/
@[app_unexpander Checked.zpow] def unexpandZPow : Lean.PrettyPrinter.Unexpander
  | `($_ $a $n $_) => `($a ^ $n)
  | _ => throw ()

end Checked.Delab
