/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module

public import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric

/-! Raw coefficient domains and natural-order convergence of the Gauss series. -/

open Filter
open scoped Nat Topology

noncomputable section

-- A coefficient does not require the denominators at later indices to exist.
example {K : Type*} [Field K] :
    ordinaryHypergeometricCoefficient (0 : K) 1 0 0 = 1 := by
  simp [ordinaryHypergeometricCoefficient]

example {K : Type*} [Field K] :
    ordinaryHypergeometricCoefficient (0 : K) 1 1 1 = 0 := by
  simp [ordinaryHypergeometricCoefficient]

-- The first upper factor is zero, and the lower Pochhammer denominator is still required.
/--
error: could not synthesize default value for parameter 'hc' using tactics
---
error: a nonzero denominator proof is required
⊢ Polynomial.eval 0 (ascPochhammer ℝ 1) ≠ 0
-/
#guard_msgs in
example : ℝ := ordinaryHypergeometricCoefficient (0 : ℝ) 1 0 1

-- Characteristic two already prevents the second factorial denominator.
example {K : Type*} [Field K] (h2 : (2 : K) = 0) :
    ¬ ∀ n : ℕ, (n ! : K) ≠ 0 := by
  intro h
  exact h 2 (by simpa only [Nat.factorial_two, Nat.cast_ofNat] using h2)

-- The whole coefficient sequence has exactly the characteristic-zero factorial domain.
example {K : Type*} [Field K] (h : ∀ n : ℕ, (n ! : K) ≠ 0) : CharZero K :=
  ordinaryHypergeometric_factorial_domain_iff.mp h

-- The lower parameter condition is necessary as well as sufficient, even in arbitrary
-- characteristic. In particular, cancelling a matching upper parameter does not enlarge it.
example {K : Type*} [Field K] (c : K) :
    (∀ n : ℕ, (ascPochhammer K n).eval c ≠ 0) ↔ ∀ k : ℕ, c ≠ -k :=
  ordinaryHypergeometric_pochhammer_domain_iff c

-- Even a terminating upper parameter cannot supply the missing lower denominator.
example {K : Type*} [Field K] :
    ¬ ∀ n : ℕ, (ascPochhammer K n).eval 0 ≠ 0 := by
  intro h
  simpa using h 1

private theorem factorial_ne_zero (n : ℕ) : (n ! : ℝ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)

private theorem pochhammer_one_ne_zero (n : ℕ) : (ascPochhammer ℝ n).eval 1 ≠ 0 := by
  simpa using factorial_ne_zero n

-- Termination of an upper parameter still gives infinite radius on the actual series domain.
example : (ordinaryHypergeometricSeries ℝ (-2) 1 1 factorial_ne_zero
    pochhammer_one_ne_zero).radius = ⊤ := by
  simpa using ordinaryHypergeometric_radius_top_of_neg_nat₁ ℝ (1 : ℝ) 1
    factorial_ne_zero pochhammer_one_ne_zero (k := 2)

example : (ordinaryHypergeometricSeries ℝ 1 1 1 factorial_ne_zero
    pochhammer_one_ne_zero).radius = 1 := by
  apply ordinaryHypergeometricSeries_radius_eq_one
  intro k
  constructor <;> norm_cast

example : ₂F₁ (1 : ℝ) 1 1 factorial_ne_zero pochhammer_one_ne_zero (0 : ℝ)
    (ordinaryHypergeometric_summable_zero 1 1 1 factorial_ne_zero pochhammer_one_ne_zero) = 1 :=
  ordinaryHypergeometric_zero 1 1 1 factorial_ne_zero pochhammer_one_ne_zero

-- At z = 1 this valid coefficient sequence is constantly one, and no value is available.
example : ¬ Summable (fun n => ordinaryHypergeometricSeries ℝ 1 1 1 factorial_ne_zero
    pochhammer_one_ne_zero n (fun _ => 1)) (SummationFilter.conditional ℕ) := by
  rintro ⟨l, hl⟩
  have hterm (n : ℕ) : ordinaryHypergeometricSeries ℝ 1 1 1 factorial_ne_zero
      pochhammer_one_ne_zero n (fun _ => 1) = (1 : ℝ) := by
    rw [ordinaryHypergeometricSeries_apply_eq]
    simp only [ordinaryHypergeometricCoefficient, ascPochhammer_eval_one, one_pow,
      smul_eq_mul, inv_mul_cancel₀, one_mul, mul_inv_cancel₀]
  have hpart : Tendsto (fun n : ℕ => (n : ℝ)) atTop (𝓝 l) := by
    simpa only [HasSum, SummationFilter.conditional_filter_eq_map_range, tendsto_map'_iff,
      Function.comp_def, hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_one] using hl
  exact not_tendsto_nhds_of_tendsto_atTop tendsto_natCast_atTop_atTop l hpart

private theorem pochhammer_two (n : ℕ) :
    (ascPochhammer ℝ n).eval 2 = ((n + 1)! : ℝ) := by
  have h := factorial_mul_ascPochhammer ℝ 1 n
  norm_num only [Nat.factorial_one, Nat.cast_one, one_mul] at h
  simpa only [add_comm] using h

private theorem pochhammer_two_ne_zero (n : ℕ) : (ascPochhammer ℝ n).eval 2 ≠ 0 := by
  rw [pochhammer_two]
  exact factorial_ne_zero (n + 1)

private theorem boundary_term (n : ℕ) :
    ordinaryHypergeometricSeries ℝ 1 1 2 factorial_ne_zero pochhammer_two_ne_zero n
      (fun _ => -1) = (-1 : ℝ) ^ n * (1 / (n + 1)) := by
  rw [ordinaryHypergeometricSeries_apply_eq]
  simp only [ordinaryHypergeometricCoefficient, ascPochhammer_eval_one, pochhammer_two,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, smul_eq_mul]
  field_simp

-- F(1,1;2;-1) is the alternating harmonic series. Natural-order convergence suffices,
-- including at this boundary point where absolute convergence is unavailable.
private theorem boundary_summable :
    Summable (fun n => ordinaryHypergeometricSeries ℝ 1 1 2 factorial_ne_zero
      pochhammer_two_ne_zero n (fun _ => -1)) (SummationFilter.conditional ℕ) := by
  have hanti : Antitone (fun n : ℕ => 1 / ((n : ℝ) + 1)) := by
    intro m n hmn
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hmn 1)
  obtain ⟨l, hl⟩ := hanti.tendsto_alternating_series_of_tendsto_zero
    tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨l, ?_⟩
  simpa only [HasSum, SummationFilter.conditional_filter_eq_map_range,
    tendsto_map'_iff, Function.comp_def, boundary_term] using hl

example : HasSum (fun n : ℕ => (-1 : ℝ) ^ n * (1 / (n + 1)))
    (₂F₁ (1 : ℝ) 1 2 factorial_ne_zero pochhammer_two_ne_zero (-1) boundary_summable)
      (SummationFilter.conditional ℕ) := by
  simpa only [boundary_term] using ordinaryHypergeometric_hasSum (1 : ℝ) 1 2
    factorial_ne_zero pochhammer_two_ne_zero (-1 : ℝ) boundary_summable

example : Tendsto (fun N => ∑ n ∈ Finset.range N, (-1 : ℝ) ^ n * (1 / (n + 1)))
    atTop (𝓝 (₂F₁ (1 : ℝ) 1 2 factorial_ne_zero pochhammer_two_ne_zero (-1)
      boundary_summable)) := by
  simpa only [boundary_term] using ordinaryHypergeometric_tendsto_sum_range (1 : ℝ) 1 2
    factorial_ne_zero pochhammer_two_ne_zero (-1 : ℝ) boundary_summable

end
