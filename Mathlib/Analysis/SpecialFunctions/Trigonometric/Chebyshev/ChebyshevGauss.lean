/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuval Filmus
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality
public import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Topology.Algebra.Polynomial

/-!
# Chebyshev polynomials over the reals: Chebyshev–Gauss

The Chebyshev–Gauss property calculates an integral of a polynomial of degree `< 2 * n`
with respect to the weight function `√(1 - x ^ 2)⁻¹` supported on `[-1, 1]` by a sum
over appropriate evaluations of the polynomial.

## Main statements

* integral_eq_sumZeroes: The integral of a polynomial of degree `< 2 * n` with respect to the weight
  function `√(1 - x ^ 2)⁻¹` supported on `[-1, 1]` is equal to `π` times the average of its values
  on the points `cos ((2 * i + 1) / (2 * n) * π)` for `0 ≤ i < n`.

## Implementation

For Chebyshev polynomials the sum reduces to cosines at equally spaced angles.
Multiplication by the sine of the half-step makes the sum telescope. The result for arbitrary
polynomials follows by linearity.
-/
public section

namespace Polynomial.Chebyshev

open Real Polynomial Finset
/-- Weighted sum of `P (x)` where `x` goes over `cos ((2 * i + 1) / (2 * n) * π)` for
  `0 ≤ i < n`. -/
noncomputable def sumZeroes (n : ℕ) (P : ℝ[X]) (hn : n ≠ 0) : ℝ :=
  (π / (n : ℝ)) * ∑ i ∈ range n, P.eval (cos ((2 * (i : ℝ) + 1) / (2 * (n : ℝ)) * π))

@[simp]
theorem sumZeroes_sum (n : ℕ) {ι : Type*} (s : Finset ι) (P : ι → ℝ[X]) {hn : n ≠ 0} :
    sumZeroes n (∑ i ∈ s, P i) hn = ∑ i ∈ s, sumZeroes n (P i) hn := by
  simp_rw [sumZeroes, eval_finsetSum]
  rw [sum_comm, mul_sum]

@[simp]
theorem sumZeroes_smul (n : ℕ) (c : ℝ) (P : ℝ[X]) {hn : n ≠ 0} :
    sumZeroes n (c • P) hn = c * sumZeroes n P hn := by
  simp_rw [sumZeroes, eval_smul, ← smul_sum, smul_eq_mul]; ring

theorem sumZeroes_T_zero {n : ℕ} (hn : n ≠ 0) : sumZeroes n (T ℝ 0) hn = π := by
  simp [sumZeroes, div_mul_cancel₀]

theorem sumZeroes_T_of_not_dvd {n : ℕ} {k : ℤ} {hn : n ≠ 0} (hk : ¬ (2 * n : ℤ) ∣ k) :
    sumZeroes n (T ℝ k) hn = 0 := by
  let θ : ℝ := k * π / (2 * (n : ℝ))
  have hθ : θ * (2 * n) = k * π := div_mul_cancel₀ _
  have hsin : sin θ ≠ 0 := by
    intro hz
    obtain ⟨m, hm⟩ := sin_eq_zero_iff.mp hz
    apply hk
    refine ⟨m, Int.cast_injective (α := ℝ) ?_⟩
    push_cast
    apply mul_right_cancel₀ pi_ne_zero
    rw [← hθ, ← hm]
    ring
  have hangle (i : ℕ) :
      (k : ℝ) * ((2 * (i : ℝ) + 1) / (2 * (n : ℝ)) * π) = (2 * i + 1) * θ := by
    simp only [θ, div_eq_mul_inv₀]
    ring
  let f (i : ℕ) := sin (2 * i * θ)
  have hstep (i : ℕ) : 2 * sin θ * cos ((2 * i + 1) * θ) = f (i + 1) - f i := by
    rw [two_mul_sin_mul_cos]
    have hsub : θ - (2 * i + 1) * θ = -(2 * i * θ) := by ring
    have hadd : θ + (2 * i + 1) * θ = 2 * ((i + 1 : ℕ) : ℝ) * θ := by push_cast; ring
    rw [hsub, hadd, sin_neg]
    simp only [f]
    ring
  have hsum : 2 * sin θ * ∑ i ∈ range n, cos ((2 * i + 1) * θ) = 0 := by
    rw [mul_sum]
    simp_rw [hstep]
    rw [sum_range_sub]
    simp [f, mul_comm (2 * (n : ℝ)) θ, hθ, sin_int_mul_pi]
  simp only [sumZeroes, T_real_cos, hangle,
    (mul_eq_zero.mp hsum).resolve_left (mul_ne_zero two_ne_zero hsin), mul_zero]

/-- The integral of a polynomial of degree `< 2 * n` with respect to the weight function
  `√(1 - x ^ 2)⁻¹` supported on `[-1, 1]` is equal to `π` times the average of its values
  on the points `cos ((2 * i + 1) / (2 * n) * π)` for `0 ≤ i < n`. -/
theorem integral_eq_sumZeroes {n : ℕ} {P : ℝ[X]} (hn : n ≠ 0) (hP : P.degree < 2 * n) :
    ∫ x, P.eval x ∂measureT = sumZeroes n P hn := by
  have hmem : P ∈ degreeLT ℝ (2 * n) := by rwa [mem_degreeLT]
  rw [← Sequence.span_degreeLT (chebyshevTsequence ℝ) (by simp),
    show Set.Iio (2 * n) = Finset.range (2 * n) by simp,
    Submodule.mem_span_image_finset_iff_exists_fun'] at hmem
  obtain ⟨c, rfl⟩ := hmem
  simp_rw [eval_finsetSum, eval_smul]
  rw [MeasureTheory.integral_finsetSum, sumZeroes_sum]
  · simp_rw [sumZeroes_smul, smul_eq_mul, MeasureTheory.integral_const_mul]
    congr! with i hrange
    simp_rw [chebyshevTsequence]
    by_cases i = 0
    case pos hi => rw [hi, Nat.cast_zero, integral_eval_T_real_measureT_zero, sumZeroes_T_zero hn]
    case neg hi =>
      have : ¬ (2 * n : ℤ) ∣ i := by
        refine (Int.not_dvd_iff_lt_mul_succ _ (by grind)).mpr ⟨0, ⟨by grind, ?_⟩⟩
        rw_mod_cast [zero_add, mul_one]
        exact mem_range.mp hrange
      rw [integral_eval_T_real_measureT_of_ne_zero (by grind), sumZeroes_T_of_not_dvd this]
  · simp_rw [← eval_smul]
    exact fun i hi => integrable_measureT (by fun_prop)

end Polynomial.Chebyshev
