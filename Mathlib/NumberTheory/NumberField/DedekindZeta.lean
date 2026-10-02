/-
Copyright (c) 2025 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Nat
public import Mathlib.NumberTheory.LSeries.SumCoeff
public import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics

/-!
# The Dedekind zeta function of a number field

In this file, we define and prove results about the Dedekind zeta function of a number field.

## Main definitions and results

* `NumberField.dedekindZeta`: the Dedekind zeta function.
* `NumberField.dedekindZetaResidue`: the value of the residue at `s = 1` of the Dedekind
  zeta function.
* `NumberField.LSeriesSummable_dedekindZeta`: the defining series converges for `1 < re s`.
* `NumberField.summable_absNorm_rpow`: the sum of inverse norm powers over nonzero ideals
  converges for real `s > 1`.
* `NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT`: **Dirichlet class number formula**
  computation of the residue of the Dedekind zeta function at `s = 1`, see Chap. 7 of
  [D. Marcus, *Number Fields*][marcus1977number]

## TODO

Generalize the construction of the Dedekind zeta function.
-/

@[expose] public section

variable (K : Type*) [Field K] [NumberField K]

noncomputable section

open Filter Ideal NumberField.InfinitePlace NumberField.Units nonZeroDivisors

open scoped Topology

namespace NumberField

open scoped Real

/--
The Dedekind zeta function of a number field. It is defined as the `L`-series with coefficients
the number of integral ideals of norm `n`.
-/
def dedekindZeta (s : ℂ) :=
  LSeries (fun n ↦ Nat.card {I : Ideal (𝓞 K) // absNorm I = n}) s

/--
The value of the residue at `s = 1` of the Dedekind zeta function, see
`NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT`.
-/
def dedekindZetaResidue : ℝ :=
  (2 ^ nrRealPlaces K * (2 * π) ^ nrComplexPlaces K * regulator K * classNumber K) /
    (torsionOrder K * Real.sqrt |discr K|)

theorem dedekindZetaResidue_def :
    dedekindZetaResidue K =
      (2 ^ nrRealPlaces K * (2 * π) ^ nrComplexPlaces K * regulator K * classNumber K) /
      (torsionOrder K * Real.sqrt |discr K|) := rfl

theorem dedekindZetaResidue_pos : 0 < dedekindZetaResidue K := by
  refine div_pos ?_ ?_
  · exact mul_pos (mul_pos (by positivity) (regulator_pos K)) (Nat.cast_pos.mpr (classNumber_pos K))
  · exact mul_pos (Nat.cast_pos.mpr (torsionOrder_pos K)) <|
      Real.sqrt_pos_of_pos <| abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K))

theorem dedekindZetaResidue_ne_zero : dedekindZetaResidue K ≠ 0 :=
  (dedekindZetaResidue_pos K).ne'

private theorem tendsto_sum_dedekindZeta_coeff_div :
    Tendsto (fun n : ℕ ↦
      (∑ k ∈ Finset.Icc 1 n, (Nat.card {I : Ideal (𝓞 K) // absNorm I = k} : ℝ)) / n)
      atTop (𝓝 (dedekindZetaResidue K)) := by
  refine ((Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop).congr fun n ↦ ?_
  simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
  congr
  rw [← add_left_inj 1, ← card_norm_le_eq_card_norm_le_add_one,
    show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
    show 1 = Nat.card {I : Ideal (𝓞 K) // absNorm I = 0} by simp [Ideal.absNorm_eq_zero_iff],
    Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
    ← Finset.card_preimage_eq_sum_card_image_eq (fun k _ ↦ finite_setOfPred_absNorm_eq k)]
  simp [Set.coe_eq_subtype]

/-- The series defining the Dedekind zeta function converges absolutely for `1 < re s`. -/
theorem LSeriesSummable_dedekindZeta {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n ↦ Nat.card {I : Ideal (𝓞 K) // absNorm I = n}) s := by
  refine LSeriesSummable_of_sum_norm_bigO_and_nonneg ?_ (fun _ ↦ Nat.cast_nonneg _)
    zero_le_one hs
  exact Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow
    (by simpa using tendsto_sum_dedekindZeta_coeff_div K)

/-- The sum of inverse norm powers over nonzero integral ideals converges for real `s > 1`. -/
theorem summable_absNorm_rpow {s : ℝ} (hs : 1 < s) :
    Summable (fun I : (Ideal (𝓞 K))⁰ ↦ (absNorm (I : Ideal (𝓞 K)) : ℝ) ^ (-s)) := by
  suffices hI : Summable (fun I : Ideal (𝓞 K) ↦ (absNorm I : ℝ) ^ (-s)) from
    hI.subtype _
  have h := (LSeriesSummable_dedekindZeta K (s := (s : ℂ)) hs).norm
  have hneg : -s ≠ 0 := neg_ne_zero.mpr (zero_lt_one.trans hs).ne'
  have hterm (n : ℕ) :
      ‖LSeries.term (fun n ↦ Nat.card {I : Ideal (𝓞 K) // absNorm I = n}) (s : ℂ) n‖ =
      (Nat.card {I : Ideal (𝓞 K) // absNorm I = n} : ℝ) * (n : ℝ) ^ (-s) := by
    by_cases hn : n = 0
    · simp [hn, hneg]
    · simp [hn, Real.rpow_neg, div_eq_mul_inv]
  replace h := h.congr hterm
  refine (summable_partition (fun I ↦ by positivity)
    (s := fun n : ℕ ↦ {I : Ideal (𝓞 K) | absNorm I = n})
    (fun I ↦ ⟨absNorm I, rfl, fun n hn ↦ hn.symm⟩)).2 ⟨?_, ?_⟩
  · intro n
    have := (finite_setOfPred_absNorm_eq (S := 𝓞 K) n).to_subtype
    exact Summable.of_finite
  · refine h.congr fun n ↦ ?_
    have := (finite_setOfPred_absNorm_eq (S := 𝓞 K) n).to_subtype
    simp_rw [show ∀ I : {I : Ideal (𝓞 K) // absNorm I = n}, absNorm I.1 = n from
      fun I ↦ I.property]
    simp only [tsum_const, nsmul_eq_mul]
    rfl

/--
**Dirichlet class number formula**
-/
theorem tendsto_sub_one_mul_dedekindZeta_nhdsGT :
    Tendsto (fun s : ℝ ↦ (s - 1) * dedekindZeta K s) (𝓝[>] 1) (𝓝 (dedekindZetaResidue K)) :=
  LSeries_tendsto_sub_mul_nhds_one_of_tendsto_sum_div_and_nonneg _
    (tendsto_sum_dedekindZeta_coeff_div K) (fun _ ↦ Nat.cast_nonneg _)

end NumberField
