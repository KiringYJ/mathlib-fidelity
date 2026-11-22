/-
Copyright (c) 2024 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
module

public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.FieldTheory.Minpoly.Finite
public import Mathlib.RingTheory.Valuation.Basic

/-!
# Minimal polynomials.

We prove some results about valuations of zero coefficients of minimal polynomials.

Let `K` be a field with a valuation `v` and let `L` be a field extension of `K`.

## Main statements

* `coeff_zero_minpoly` : for `x ∈ K` the valuation of the zeroth coefficient of the minimal
  polynomial of `algebraMap K L x` over `K` is equal to the valuation of `x`.
* `pow_coeff_zero_ne_zero_of_unit` : for any unit `x : Lˣ`, we prove that a certain power of the
  valuation of zeroth coefficient of the minimal polynomial of `x` over `K` is nonzero. This lemma
  is helpful for defining the valuation on `L` inducing `v`.
-/

public section

open Module minpoly Polynomial

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation K Γ₀) (L : Type*) [Field L] [Algebra K L]

namespace Valuation

/-- For `x ∈ K` the valuation of the zeroth coefficient of the minimal polynomial
of `algebraMap K L x` over `K` is equal to the valuation of `x`. -/
@[simp]
theorem coeff_zero_minpoly (x : K) : v ((minpoly K (algebraMap K L x)).coeff 0) = v x := by
  rw [minpoly.eq_X_sub_C, coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub, Valuation.map_neg]

variable {L}

/-- For any unit `x : Lˣ`, we prove that a certain power of the valuation of zeroth coefficient of
the minimal polynomial of `x` over `K` is nonzero. This lemma is helpful for defining the valuation
on `L` inducing `v`. -/
theorem pow_coeff_zero_ne_zero_of_unit [FiniteDimensional K L] (x : L) (hx : IsUnit x) :
    v ((minpoly K x).coeff 0) ^ Nat.euclideanDiv (finrank K L) (minpoly K x).natDegree
      (natDegree_pos (Algebra.IsIntegral.isIntegral x)).ne' ≠ (0 : Γ₀) := by
  apply pow_ne_zero
  simpa only [ne_eq, Valuation.zero_iff] using
    coeff_zero_ne_zero (Algebra.IsIntegral.isIntegral x) hx.ne_zero

end Valuation
