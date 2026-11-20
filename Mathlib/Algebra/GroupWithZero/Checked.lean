/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module

public meta import Lean.Elab.App
public meta import Lean.Elab.BuiltinNotation
public meta import Lean.Elab.Tactic.Omega
public import Mathlib.Algebra.GroupWithZero.NeZero

/-!
# Inversion and division with explicit invertibility

This file implements the inverse, division and integer power of an element of a monoid
together with evidence that the element is invertible. The operations use the group of units:
there is no ambient inverse operation and no value at an invalid denominator. An integer power
requires invertibility only for a negative exponent.

These declarations implement the ordinary notation `a⁻¹`, `a / b` and `a ^ n` for monoids
without an ambient inverse, such as groups with zero and fields; see
`Mathlib.Algebra.GroupWithZero.Checked.Notation`. Their theorems use the ordinary notation and
the established names, beginning in `Mathlib.Algebra.GroupWithZero.Inverse`.

The default evidence tactics use local hypotheses, unit and nonzero closure, and simplification.
A local hypothesis may also be applied: a pointwise hypothesis `∀ x, f x ≠ 0` or
`∀ x ∈ s, IsUnit (f x)` gives the evidence at each point, and a function is invertible when all
its values are. A difference `b - a` is nonzero when `a ≠ b`, `b ≠ a`, `a < b` or `b < a` is a
hypothesis, a comparison with zero may come from a `Fact` instance, and an `Invertible` instance
gives invertibility.
The properties carried by local subtype values are made available to the same rules, including
nonzeroness transported through a norm by simplification.
Every alternative must close the goal (`solve`), and alternatives that compare the goal with a
constant (`1`, a unit coercion) match only up to reducible and instance unfolding, so that a large
closed term such as `↑(Finset.range 3000).card` is not evaluated and the evidence found has
exactly the type of the goal.
In characteristic zero, a natural or integer cast is nonzero when `omega` proves the number
nonzero from the hypotheses, and a rational cast is nonzero when the rational number is. The
rational rule applies only to a syntactic cast, so it does not loop on `ℚ` or `ℚ≥0`, whose casts
are the identity. The tactics never assume that an arbitrary sum or a numeral in arbitrary
characteristic is nonzero.
Elaboration may already have assigned the evidence by unification with a term of the same
proposition, as `convert` does; the tactics then succeed without further search.
-/

@[expose] public section

open Lean Meta Elab Tactic in
/-- Make the properties of local subtype values available without repeatedly adding them during
recursive evidence search. This is a single pass over the local context, not recursive search
through arbitrary structures. -/
meta def Checked.addSubtypeFacts : TacticM Unit := withMainContext do
  let mut goal ← getMainGoal
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let type ← withReducible <| whnf decl.type
    unless type.isAppOfArity ``Subtype 2 do continue
    let proof ← mkAppM ``Subtype.property #[decl.toExpr]
    let property ← inferType proof
    let alreadyDeclared ← goal.withContext do
      (← getLCtx).findDeclM? fun localDecl => do
        if ← withNewMCtxDepth <| withReducible <| isDefEq localDecl.type property then
          return some ()
        return none
    if alreadyDeclared.isSome then continue
    let (_, next) ← goal.note (← mkFreshUserName `h_carried) proof
    goal := next
  replaceMainGoal [goal]

open Lean Meta Elab Tactic in
/-- Simplify the evidence goal with local facts. An equality such as `q = f q` cannot
serve as a left-to-right rewrite rule. Use its converse so that the fact remains available. -/
meta def Checked.simpEvidence : TacticM Unit := withMainContext do
  let { ctx, simprocs, .. } ← mkSimpContext (← `(tactic| simp_all))
    (eraseLocal := true) (kind := .simpAll) (ignoreStarArg := true)
  let mut thms := ctx.simpTheorems
  for h in ← getPropHyps do
    let some (_, lhs, rhs) := (← h.getType).getForallBody.eq? | continue
    if lhs != rhs && lhs.occurs rhs then
      thms := thms.eraseTheorem (.fvar h)
      thms ← thms.modifyM 0 fun set ↦ do
        set.add (.other (← mkFreshId)) #[] (mkFVar h) (inv := true) (config := ctx.indexConfig)
  let (remaining, _) ← simpAll (← getMainGoal) (ctx.setSimpTheorems thms) (simprocs := simprocs)
  replaceMainGoal remaining.toList

/-- Find a nonzero proof from the local context and standard closure facts. -/
syntax (name := checkedNonzero) "checked_nonzero" : tactic

macro_rules
  | `(tactic| checked_nonzero) => `(tactic|
      first
      | done
      | ((run_tac Checked.addSubtypeFacts); solve
        | assumption
        | ((with_reducible apply_assumption) <;> assumption)
        | (apply $(Lean.mkIdent `IsUnit.ne_zero); assumption)
        | exact NeZero.ne _
        | (with_reducible_and_instances exact one_ne_zero)
        | exact $(Lean.mkIdent `Nat.cast_add_one_ne_zero) _
        | ((with_reducible apply $(Lean.mkIdent `neg_ne_zero.mpr)); checked_nonzero)
        | (with_reducible_and_instances exact $(Lean.mkIdent `Units.ne_zero) _)
        | (apply $(Lean.mkIdent `ne_of_gt);
            first
            | assumption
            | exact $(Lean.mkIdent `Fact.out)
            | ((with_reducible apply_assumption) <;> assumption))
        | (apply $(Lean.mkIdent `ne_of_lt);
            first
            | assumption
            | exact $(Lean.mkIdent `Fact.out)
            | ((with_reducible apply_assumption) <;> assumption))
        | ((with_reducible apply $(Lean.mkIdent `sub_ne_zero_of_ne));
            first
            | assumption
            | exact Ne.symm ‹_›
            | exact $(Lean.mkIdent `ne_of_gt) ‹_›
            | exact $(Lean.mkIdent `ne_of_lt) ‹_›)
        | ((with_reducible apply $(Lean.mkIdent `pow_ne_zero)) <;> checked_nonzero)
        | ((with_reducible apply $(Lean.mkIdent `mul_ne_zero)) <;> checked_nonzero)
        | (apply $(Lean.mkIdent `Nat.cast_ne_zero).mpr; omega)
        | (apply $(Lean.mkIdent `Int.cast_ne_zero).mpr; omega)
        | ((with_reducible apply $(Lean.mkIdent `Rat.cast_ne_zero).mpr); checked_nonzero)
        | ((with_reducible apply $(Lean.mkIdent `NNRat.cast_ne_zero).mpr); checked_nonzero)
        | ((run_tac Checked.simpEvidence); done)
        | decide
        | fail "a nonzero denominator proof is required"))

/-- Find invertibility without installing an ambient inverse operation.

Besides local hypotheses and nonzero evidence in a group with zero, this uses closure under
products, natural powers, inverses, quotients, multiplicative actions and submonoid coercions.
The evidence carried by an inverse or a quotient is reused. Invertibility of a factor is recovered
from a product or a quotient in a local hypothesis, and invertibility of a value `f i` from that of
a function `f`.
The closure rules match the goal reducibly: a power `x ^ 2` is not unfolded into a product, whose
evidence would type-check only after unfolding the power. -/
syntax (name := checkedUnit) "checked_unit" : tactic

macro_rules
  | `(tactic| checked_unit) => `(tactic|
      first
      | done
      | ((run_tac Checked.addSubtypeFacts); solve
        | assumption
        | ((with_reducible apply_assumption) <;> assumption)
        | ((with_reducible apply $(Lean.mkIdent `IsUnit.inv₀)); done)
        | ((with_reducible apply $(Lean.mkIdent `IsUnit.div₀)) <;> checked_unit)
        | (with_reducible_and_instances exact $(Lean.mkIdent `Units.isUnit) _)
        | (with_reducible_and_instances exact $(Lean.mkIdent `isUnit_one))
        | ((with_reducible apply $(Lean.mkIdent `IsUnit.pow)) <;> checked_unit)
        | ((with_reducible apply $(Lean.mkIdent `IsUnit.mul)) <;> checked_unit)
        | ((with_reducible apply $(Lean.mkIdent `IsUnit.zpow₀)); checked_unit)
        | ((with_reducible apply $(Lean.mkIdent `IsUnit.smul')); checked_unit)
        | (refine $(Lean.mkIdent `IsUnit.map) ($(Lean.mkIdent `SubmonoidClass.subtype) _) ?_;
            checked_unit)
        | (apply $(Lean.mkIdent `isUnit_of_mul_isUnit_left); assumption)
        | (apply $(Lean.mkIdent `isUnit_of_mul_isUnit_right); assumption)
        | (apply $(Lean.mkIdent `IsUnit.of_div₀); assumption)
        | (apply $(Lean.mkIdent `IsUnit.apply); assumption)
        | (with_reducible_and_instances exact $(Lean.mkIdent `isUnit_of_invertible) _)
        | ((with_reducible apply $(Lean.mkIdent `Pi.isUnit_iff).2); intro; checked_unit)
        | (apply GroupWithZero.isUnit_of_ne_zero; checked_nonzero)
        | fail "an invertibility proof is required"))

/-- Invertibility is needed only on the negative-exponent branch. A local hypothesis of exactly
this form is used directly, so that theorems can take it as evidence unified from the term. On
that branch, local hypotheses of the form `n < 0 → IsUnit x` are specialized before searching. -/
syntax (name := checkedPower) "checked_power" : tactic

macro_rules
  | `(tactic| checked_power) => `(tactic|
      first
      | done
      | (solve
        | assumption
        | (intro h; solve
            | omega
            | checked_unit
            | (simp only [h, true_implies] at *; checked_unit)
            | ((run_tac Checked.simpEvidence); done))))

namespace Checked

variable {M : Type*} [Monoid M]

/-- The inverse of an ambient element, with its exact invertibility obligation.
Write it as `a⁻¹`. -/
noncomputable def inv (a : M) (ha : IsUnit a := by checked_unit) : M :=
  ↑ha.unit⁻¹

/-- Divide an arbitrary numerator by a denominator known to be a unit. Write it as `a / b`. -/
noncomputable def div (a b : M) (hb : IsUnit b := by checked_unit) : M :=
  a /ₚ hb.unit

/-- Integer powers of an ambient element; only negative exponents require a unit.
Write it as `a ^ n`. -/
noncomputable def zpow (a : M) (n : Int)
    (ha : n < 0 → IsUnit a := by checked_power) : M :=
  match n with
  | .ofNat k => a ^ k
  | .negSucc k => ↑((ha (Int.negSucc_lt_zero k)).unit ^ (Int.negSucc k))

end Checked
