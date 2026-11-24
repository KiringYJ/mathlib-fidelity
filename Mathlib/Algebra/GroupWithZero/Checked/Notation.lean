/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Gabriel Ebner, Yi-Jing Tseng
-/
module

public meta import Mathlib.Lean.Elab.OperatorTree
public import Mathlib.Algebra.GroupWithZero.Checked
public import Mathlib.Data.Rat.Init

/-!
# Ordinary notation for inversion and division by invertible elements

Ordinary `a / b` uses the installed division, including heterogeneous division, or checked exact
division by a unit. For operands in a field, slash uses checked division even with a local
`Div` instance or an explicit `Field.toEuclideanDomain` instance. Nonzero evidence supplies
the unit requirement. Use `divp` to divide by a bundled unit in a monoid. In a monoid without
an ambient inverse, `a⁻¹` and `a ^ n` for integer `n` use the checked operations. The
`checked_unit` tactic can find invertibility evidence where required. Nonnegative exponents
have the full monoid domain.

## Choosing a quotient

Exact right division by a unit solves `q * b = a`. Under a multiplicative embedding into a
carrier in which the image of `b` is a unit, this equation says that the image of `q` is the
exact quotient of the images. An integer-valued exact quotient needs both a nonzero divisor and
divisibility, as in `Int.exactQuotient`.

Use `EuclideanDomain.quotient` for division with remainder. It takes a nonzero divisor, which
can be a nonunit. For example, `Int.euclideanDiv 3 2` is `1`, while `(3 : ℚ) / (2 : ℚ)` is
the exact rational quotient. See `Mathlib.Lean.Elab.NativeDivision` for the quotient laws and
the remainder at zero, and `Field.quotient_eq_div` for agreement on fields with the explicit
Euclidean structure. Ordinals and binary numerals use their named Euclidean operations too.

Slash rejects a natural or integer operand, including a definitionally equal type. Use a named
operation or explicitly cast the operands to a carrier supporting the intended quotient.
When an installed operation has a different mathematical specification, follow its own laws.
For instance, `ENNReal.div_eq_sInf` describes the current quotient on extended nonnegative
reals.

## Implementation notes

The operator-tree algorithm follows the pinned official Lean elaborator in Lean/Elab/Extra.lean.
Division checks its operands before the surrounding operators insert coercions.
Ambient division, genuine group operations and natural powers retain their ordinary
elaborated heads. The delaborator displays slash when it can reconstruct the selected operation
and any required evidence.
-/

public meta section

namespace Checked.Elab.Op

open Lean Meta Elab Term Mathlib.Elab.OperatorTree

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

/-- Whether an instance exists. A query that is stuck on metavariables counts as absent; it must
not escape as an internal exception. -/
private def hasInstance (name : Name) (args : Array Expr) : TermElabM Bool := do
  try
    return (← synthInstance? (← mkAppM name args)).isSome
  catch _ =>
    return false

/-- The type of an operand of a checked operation can still be a metavariable, for instance the
output type of a power whose exponent type is pending a default instance. When the operator tree
has a known uniform type that is a checked carrier, the operand has that type, as the homogeneous
instance would eventually require. -/
private def alignOperandType (maxType? : Option Expr) (type : Expr) :
    TermElabM Expr := do
  let type ← instantiateMVars type
  unless type.hasExprMVar do return type
  let some maxType := maxType? | return type
  let maxType ← instantiateMVars maxType
  if maxType.hasExprMVar then return type
  unless ← selectedCarrier maxType do
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

private def algebraBinOp? (maxType? : Option Expr) (f lhs rhs : Expr) :
    TermElabM (Option Expr) := do
  let mut lhsType ← instantiateMVars (← inferType lhs)
  let rhsType ← instantiateMVars (← inferType rhs)
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
  return none

private def algebraUnOp? (maxType? : Option Expr) (f arg : Expr) : TermElabM (Option Expr) := do
  if f.isConstOf ``Inv.inv then
    let carrier ← alignOperandType maxType? (← inferType arg)
    if carrier.hasExprMVar && !(← hasInstance ``Inv #[carrier]) then tryPostpone
    if (← selectedCarrier carrier) ||
        (!(← hasInstance ``Inv #[carrier]) && (← hasInstance ``Monoid #[carrier])) then
      if let some u ← recoverUnit? arg then
        return ← mkAppM ``Units.val #[← mkAppM ``Inv.inv #[u]]
      return ← checkedApp ``Checked.inv #[arg]
  return none

private def algebraRules : Rules where
  binOp? := algebraBinOp?
  unOp? := algebraUnOp?

/-- Elaborate the ordinary binary operator notation `binop%`. -/
@[term_elab Lean.Parser.Term.binop] def elabBinOp : TermElab := elabOp algebraRules

/-- Elaborate `binop_lazy%`, passing the right operand as a thunk. -/
@[term_elab Lean.Parser.Term.binop_lazy] def elabBinOpLazy : TermElab := elabOp algebraRules

/-- Elaborate `leftact%`, where the left operand acts on the right operand. -/
@[term_elab Lean.Parser.Term.leftact] def elabLeftact : TermElab := elabOp algebraRules

/-- Elaborate `rightact%`, where the right operand acts on the left operand. -/
@[term_elab Lean.Parser.Term.rightact] def elabRightact : TermElab := elabOp algebraRules

/-- Elaborate unary operators through the common operator tree. -/
@[term_elab Lean.Parser.Term.unop] def elabUnOp : TermElab := elabOp algebraRules

/-- Elaborate `binrel%` by coordinating coercions between the operands. -/
@[term_elab Lean.Parser.Term.binrel] def elabBinRel : TermElab := elabBinRelCore algebraRules false

/-- Elaborate `binrel_no_prop%`, coercing propositional operands to `Bool`. -/
@[term_elab Lean.Parser.Term.binrel_no_prop] def elabBinRelNoProp : TermElab :=
  elabBinRelCore algebraRules true

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

/-- Display a checked integer power as `a ^ n`. -/
@[app_unexpander Checked.zpow] def unexpandZPow : Lean.PrettyPrinter.Unexpander
  | `($_ $a $n $_) => `($a ^ $n)
  | _ => throw ()

end Checked.Delab
