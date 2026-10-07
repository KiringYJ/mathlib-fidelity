/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Ashvni Narayanan
-/
module

public import Mathlib.FieldTheory.RatFunc.Degree

/-!
# Valuations on F(t)

This file defines the valuation at infinity on the field of rational functions `F(t)`.

## Main definitions

- `RatFunc.inftyValuation` : The place at infinity on `F(t)` is the nonarchimedean
  valuation on `F(t)` with uniformizer `1/t`.
- `RatFunc.CompletionAtInfty` : The completion `F((t⁻¹))` of `F(t)` with respect to the
  valuation at infinity.

## References
* [D. Marcus, *Number Fields*][marcus1977number]
* [J.W.S. Cassels, A. Fröhlich, *Algebraic Number Theory*][cassels1967algebraic]
* [P. Samuel, *Algebraic Theory of Numbers*][samuel1967]

## Tags
function field, ring of integers
-/

@[expose] public section


public noncomputable section

namespace RatFunc

variable (F : Type*) [Field F]

/-! ### The place at infinity on F(t) -/

section InftyValuation

open Multiplicative WithZero Polynomial

variable [DecidableEq (RatFunc F)]

/-- The valuation at infinity is the nonarchimedean valuation on `F(t)` with uniformizer `1/t`.
Explicitly, if `f/g ∈ F(t)` is a nonzero quotient of polynomials, its valuation at infinity is
`exp (degree(f) - degree(g))`. -/
def inftyValuationDef (r : RatFunc F) : ℤᵐ⁰ :=
  if hr : r = 0 then 0 else exp (r.intDegree hr)

theorem InftyValuation.map_zero' : inftyValuationDef F 0 = 0 :=
  dite_eq_left rfl

theorem InftyValuation.map_one' : inftyValuationDef F 1 = 1 :=
  (dite_eq_right one_ne_zero).trans <| by simp

@[simp]
theorem inftyValuation_of_nonzero {x : RatFunc F} (hx : x ≠ 0) :
    inftyValuationDef F x = exp (x.intDegree hx) := by
  rw [inftyValuationDef, dite_eq_right hx]

theorem InftyValuation.map_mul' (x y : RatFunc F) :
    inftyValuationDef F (x * y) = inftyValuationDef F x * inftyValuationDef F y := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [inftyValuationDef]
  rcases eq_or_ne y 0 with rfl | hy
  · simp [inftyValuationDef]
  rw [inftyValuation_of_nonzero F hx, inftyValuation_of_nonzero F hy,
    inftyValuation_of_nonzero F (mul_ne_zero hx hy), RatFunc.intDegree_mul hx hy, exp_add]

theorem InftyValuation.map_add_le_max' (x y : RatFunc F) :
    inftyValuationDef F (x + y) ≤ max (inftyValuationDef F x) (inftyValuationDef F y) := by
  rcases eq_or_ne (x + y) 0 with hxy | hxy
  · simp [inftyValuationDef, hxy]
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  rw [inftyValuation_of_nonzero F hx, inftyValuation_of_nonzero F hy,
    inftyValuation_of_nonzero F hxy, le_max_iff, exp_le_exp, exp_le_exp, ← le_max_iff]
  exact RatFunc.intDegree_add_le hx hy hxy

/-- The valuation at infinity on `F(t)`. -/
def inftyValuation : Valuation (RatFunc F) ℤᵐ⁰ where
  toFun := inftyValuationDef F
  map_zero' := InftyValuation.map_zero' F
  map_one' := InftyValuation.map_one' F
  map_mul' := InftyValuation.map_mul' F
  map_add_le_max' := InftyValuation.map_add_le_max' F

theorem inftyValuation_apply {x : RatFunc F} : inftyValuation F x = inftyValuationDef F x :=
  rfl

@[simp]
theorem inftyValuation.C {k : F} (hk : k ≠ 0) :
    inftyValuation F (RatFunc.C k) = 1 := by
  simp [inftyValuation_apply, hk]

@[simp]
theorem inftyValuation.X : inftyValuation F RatFunc.X = exp 1 := by
  rw [inftyValuation_apply, inftyValuation_of_nonzero F RatFunc.X_ne_zero, RatFunc.intDegree_X]

lemma inftyValuation.X_zpow (m : ℤ) : inftyValuation F (RatFunc.X ^ m) = exp m := by simp

theorem inftyValuation.X_inv : inftyValuation F (1 / RatFunc.X) = exp (-1) := by
  rw [one_div, ← zpow_neg_one, inftyValuation.X_zpow]

-- Dropped attribute `@[simp]` due to issue described here:
-- https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/.60synthInstance.2EmaxHeartbeats.60.20error.20but.20only.20in.20.60simpNF.60
theorem inftyValuation.polynomial {p : F[X]} (hp : p ≠ 0) :
    inftyValuationDef F (algebraMap F[X] (RatFunc F) p) = exp (p.natDegree : ℤ) := by
  rw [inftyValuation_of_nonzero F (RatFunc.algebraMap_ne_zero hp),
    RatFunc.intDegree_polynomial hp]

instance : Valuation.IsNontrivial (inftyValuation F) := ⟨RatFunc.X, by simp⟩

instance : Valuation.IsTrivialOn F (inftyValuation F) :=
  ⟨fun _ hx ↦ by simp [inftyValuation.C _ hx]⟩

/-- The valued field `F(t)` with the valuation at infinity. -/
@[instance_reducible]
def inftyValued : Valued (RatFunc F) ℤᵐ⁰ :=
  Valued.mk' <| inftyValuation F

theorem inftyValued.def {x : RatFunc F} :
    (inftyValued F).v x = inftyValuationDef F x :=
  rfl

namespace CompletionAtInfty

/- We temporarily disable the existing valued instance coming from the ideal `X` to avoid diamonds
with the uniform space structure coming from the valuation at infinity. -/
attribute [-instance] RatFunc.valuedRatFunc

/- Locally add the uniform space structure coming from the valuation at infinity. This instance
is scoped in the `CompletionAtInfty` namescape in case it is needed in the future. -/
/-- The uniform space structure on `RatFunc F` coming from the valuation at infinity. -/
scoped instance : UniformSpace (RatFunc F) := (inftyValued F).toUniformSpace

/-- The completion `F((t⁻¹))` of `F(t)` with respect to the valuation at infinity. -/
def _root_.RatFunc.CompletionAtInfty := UniformSpace.Completion (RatFunc F)
deriving Field, Algebra (RatFunc F), Coe (RatFunc F), Inhabited

/-- The valuation at infinity on `k(t)` extends to a valuation on `CompletionAtInfty`. -/
instance : Valued (CompletionAtInfty F) ℤᵐ⁰ :=
  inferInstanceAs <| Valued (UniformSpace.Completion (RatFunc F)) ℤᵐ⁰

end CompletionAtInfty

theorem valuedCompletionAtInfty.def {x : CompletionAtInfty F} :
  Valued.v x = (inftyValued F).extensionValuation x := rfl

end InftyValuation

end RatFunc
