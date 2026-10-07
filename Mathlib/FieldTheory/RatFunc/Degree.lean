/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# The degree of rational functions

## Main definitions
We define the degree of a rational function, with values in `ℤ`:
- `intDegree` is the degree of a rational function, defined as the difference between the
  `natDegree` of its numerator and the `natDegree` of its denominator. In particular,
  `intDegree 0 = 0`.
-/

@[expose] public section


noncomputable section

universe u

variable {K : Type u}

namespace RatFunc

section IntDegree

open Polynomial

variable [Field K]

set_option linter.unusedVariables false in
/-- `intDegree x hx` is the degree of a nonzero rational function `x`, the difference between the
`natDegree` of its numerator and the `natDegree` of its denominator. The zero rational function has
no integer degree, as the zero polynomial has degree `⊥`. The proof `hx` can be omitted when it is
a hypothesis. -/
@[nolint unusedArguments]
def intDegree (x : K⟮X⟯) (hx : x ≠ 0 := by assumption) : ℤ :=
  natDegree x.num - natDegree x.denom

@[simp]
theorem intDegree_one : intDegree (1 : K⟮X⟯) one_ne_zero = 0 := by
  rw [intDegree, num_one, denom_one, sub_self]

@[simp]
theorem intDegree_C {k : K} (hk : k ≠ 0) : intDegree (C k) ((_root_.map_ne_zero C).2 hk) = 0 := by
  rw [intDegree, num_C, natDegree_C, denom_C, natDegree_one, sub_self]

@[simp]
theorem intDegree_X : intDegree (X : K⟮X⟯) X_ne_zero = 1 := by
  rw [intDegree, num_X, Polynomial.natDegree_X, denom_X, Polynomial.natDegree_one,
    Int.ofNat_one, Int.ofNat_zero, sub_zero]

@[simp]
theorem intDegree_polynomial {p : K[X]} (hp : p ≠ 0) :
    intDegree (algebraMap K[X] K⟮X⟯ p) (algebraMap_ne_zero hp) = natDegree p := by
  rw [intDegree, RatFunc.num_algebraMap, RatFunc.denom_algebraMap, Polynomial.natDegree_one,
    Int.ofNat_zero, sub_zero]

theorem intDegree_mul {x y : K⟮X⟯} (hx : x ≠ 0) (hy : y ≠ 0) :
    intDegree (x * y) (mul_ne_zero hx hy) = intDegree x + intDegree y := by
  simp only [intDegree, add_sub, sub_add, sub_sub_eq_add_sub, sub_sub, sub_eq_sub_iff_add_eq_add]
  norm_cast
  rw [← Polynomial.natDegree_mul x.denom_ne_zero y.denom_ne_zero, ←
    Polynomial.natDegree_mul (RatFunc.num_ne_zero (mul_ne_zero hx hy))
      (mul_ne_zero x.denom_ne_zero y.denom_ne_zero),
    ← Polynomial.natDegree_mul (RatFunc.num_ne_zero hx) (RatFunc.num_ne_zero hy), ←
    Polynomial.natDegree_mul (mul_ne_zero (RatFunc.num_ne_zero hx) (RatFunc.num_ne_zero hy))
      (x * y).denom_ne_zero,
    RatFunc.num_denom_mul]

@[simp]
theorem intDegree_inv {x : K⟮X⟯} (hx : x ≠ 0) :
    intDegree x⁻¹ (inv_ne_zero hx) = - intDegree x := by
  have := intDegree_mul (inv_ne_zero hx) hx
  simp only [inv_mul_cancel₀ hx, intDegree_one] at this
  lia

lemma intDegree_div {x y : RatFunc K} (hx : x ≠ 0) (hy : y ≠ 0) :
    (x / y).intDegree (div_ne_zero hx hy) = x.intDegree - y.intDegree := by
  have := intDegree_mul hx (inv_ne_zero hy)
  simp only [← div_eq_mul_inv, intDegree_inv hy] at this
  rw [this, sub_eq_add_neg]

@[simp]
theorem intDegree_neg {x : K⟮X⟯} (hx : x ≠ 0) :
    intDegree (-x) (neg_ne_zero.2 hx) = intDegree x := by
  rw [intDegree, intDegree, ← natDegree_neg x.num]
  exact
    natDegree_sub_eq_of_prod_eq (num_ne_zero (neg_ne_zero.mpr hx)) (denom_ne_zero (-x))
      (neg_ne_zero.mpr (num_ne_zero hx)) (denom_ne_zero x) (num_denom_neg x)

theorem intDegree_add {x y : K⟮X⟯} (hxy : x + y ≠ 0) :
    (x + y).intDegree =
      (x.num * y.denom + x.denom * y.num).natDegree - (x.denom * y.denom).natDegree :=
  natDegree_sub_eq_of_prod_eq (num_ne_zero hxy) (x + y).denom_ne_zero
    (num_mul_denom_add_denom_mul_num_ne_zero hxy) (mul_ne_zero x.denom_ne_zero y.denom_ne_zero)
    (num_denom_add x y)

theorem natDegree_num_mul_right_sub_natDegree_denom_mul_left_eq_intDegree {x : K⟮X⟯}
    (hx : x ≠ 0) {s : K[X]} (hs : s ≠ 0) :
    ((x.num * s).natDegree : ℤ) - (s * x.denom).natDegree = x.intDegree := by
  apply natDegree_sub_eq_of_prod_eq (mul_ne_zero (num_ne_zero hx) hs)
    (mul_ne_zero hs x.denom_ne_zero) (num_ne_zero hx) x.denom_ne_zero
  rw [mul_assoc]

theorem intDegree_add_le {x y : K⟮X⟯} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0) :
    intDegree (x + y) ≤ max (intDegree x) (intDegree y) := by
  rw [intDegree_add hxy, ←
    natDegree_num_mul_right_sub_natDegree_denom_mul_left_eq_intDegree hx y.denom_ne_zero,
    mul_comm y.denom, ←
    natDegree_num_mul_right_sub_natDegree_denom_mul_left_eq_intDegree hy x.denom_ne_zero,
    le_max_iff, sub_le_sub_iff_right, Int.ofNat_le, sub_le_sub_iff_right, Int.ofNat_le, ←
    le_max_iff, mul_comm y.num]
  exact natDegree_add_le _ _

end IntDegree

end RatFunc
