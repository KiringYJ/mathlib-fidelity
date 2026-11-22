/-
Copyright (c) 2024 Thomas Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Zhu, Etienne Marion
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.Independence.CharacteristicFunction

/-!
# Central limit theorem

We prove the central limit theorem in dimension 1.

## Main statement

* `tendstoInDistribution_inv_sqrt_mul_sum_sub`: Given a sequence of random variables
  `X : ℕ → Ω → ℝ` that are independent, identically distributed with mean `μ` and variance `v`,
  and a random variable `Y : Ω' → ℝ` following `gaussianReal 0 v`, the sequence
  `n ↦ (√n)⁻¹ * (∑ k ∈ Finset.range n, X k ω - n * μ)` over positive sample sizes converges
  to `Y` in distribution.

## Tags

central limit theorem
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Complex Filter
open scoped Real Topology

namespace ProbabilityTheory

variable {Ω Ω' : Type*} {mΩ : SigmaAlgebra Ω} {mΩ' : SigmaAlgebra Ω'}
  {P : Measure Ω} {P' : Measure Ω'} {X : ℕ → Ω → ℝ} {Y : Ω' → ℝ}

local notation "PositiveNat" => {n : ℕ // n ≠ 0}
local notation "atTopPositiveNat" => comap (Subtype.val : PositiveNat → ℕ) atTop

private lemma sampleSize_pos (n : PositiveNat) : 0 < ((n : ℕ) : ℝ) := by
  exact_mod_cast Nat.pos_of_ne_zero n.2

/-- The real square root of a positive sample size is invertible. -/
lemma isUnit_sqrt_sampleSize (n : PositiveNat) : IsUnit (√((n : ℕ) : ℝ)) :=
  (Real.sqrt_pos.2 (sampleSize_pos n)).ne'.isUnit

local notation "invSqrt(" n ")" => Checked.inv (√((n : ℕ) : ℝ)) (isUnit_sqrt_sampleSize n)

lemma charFun_inv_sqrt_mul_sum (hindep : iIndepFun X P)
    (hident : ∀ (i : ℕ), IdentDistrib (X i) (X 0) P P) {n : PositiveNat} {t : ℝ} :
    charFun (P.map (fun ω ↦ invSqrt(n) * ∑ k ∈ Finset.range n, X k ω)
      ((Finset.aemeasurable_fun_sum _ fun k _ ↦ (hident k).aemeasurable_fst).const_mul _)) t =
      (charFun (P.map (X 0) (hident 0).aemeasurable_fst) (invSqrt(n) * t)) ^ (n : ℕ) := by
  have mX n := (hident n).aemeasurable_fst
  rw [charFun_map_mul_comp, (hindep.restrict _).charFun_map_fun_finsetSum_eq_prod (fun _ _ ↦ mX _)]
  · simp [fun i ↦ (hident i).map_eq]
  · exact Finset.aemeasurable_fun_sum _ fun _ _ ↦ mX _

variable [IsProbabilityMeasure P]

lemma tendsto_charFun_inv_sqrt_mul_pow {X : Ω → ℝ}
    (hX : AEMeasurable X P) (h0 : ∫ ω, X ω ∂P = 0) (h1 : ∫ ω, (X ^ 2) ω ∂P = 1) (t : ℝ) :
    Tendsto (fun (n : PositiveNat) ↦ (charFun (P.map X hX) (invSqrt(n) * t)) ^ (n : ℕ))
      atTopPositiveNat (𝓝 (exp (- t ^ 2 / 2))) := by
  apply tendsto_pow_exp_of_isLittleO_sub_add_div
  have hsq (n : PositiveNat) : (invSqrt(n) * t) ^ 2 = t ^ 2 / ((n : ℕ) : ℝ) := by
    have hn := sampleSize_pos n
    have hinv : Checked.inv ((√((n : ℕ) : ℝ)) ^ 2) ((isUnit_sqrt_sampleSize n).pow 2) =
        (((n : ℕ) : ℝ))⁻¹ := by
      apply inv_eq_of_mul_eq_one_right₀
      rw [Real.sq_sqrt hn.le, mul_inv_cancel₀]
    rw [mul_pow, inv_pow₀, hinv, div_eq_inv_mul₀]
  suffices (fun (n : PositiveNat) ↦ charFun (Measure.map X P hX) (invSqrt(n) * t) -
      (1 + (-((invSqrt(n) * t) ^ 2 / 2) : ℂ))) =o[atTopPositiveNat] fun n ↦ (invSqrt(n) * t) ^ 2 by
    have aux : (fun (n : PositiveNat) ↦ ‖1 / ((n : ℕ) : ℂ)‖) =
        fun n : PositiveNat ↦ ‖1 / ((n : ℕ) : ℝ)‖ := by
      funext n
      simp
    rw [← Asymptotics.isLittleO_norm_right, aux, Asymptotics.isLittleO_norm_right]
    refine .of_const_mul_right (c := t ^ 2) ?_
    convert! this using 4 with n <;> norm_cast <;>
      simp only [hsq, ne_eq, div_eq_mul_inv₀, one_mul]
    push_cast
    ring
  have : Tendsto (fun (n : PositiveNat) ↦ invSqrt(n) * t) atTopPositiveNat (𝓝 0) := by
    rw [← zero_mul t]
    have h_sqrt : Tendsto (fun n : PositiveNat ↦ √((n : ℕ) : ℝ)) atTopPositiveNat atTop :=
      Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp tendsto_comap)
    exact .mul_const t (h_sqrt.fun_inv_tendsto_atTop (h0 := isUnit_sqrt_sampleSize))
  convert! (taylor_charFun_two hX h0 h1).comp_tendsto this using 2

variable [IsProbabilityMeasure P']

/-- **Central Limit Theorem:** Given a sequence of random variables `X : ℕ → Ω → ℝ` that are
independent, identically distributed, centered and with variance `1` and a random variable
`Y : Ω' → ℝ` following `gaussianReal 0 1`, the sequence
`n ↦ (√n)⁻¹ * ∑ k ∈ Finset.range n, X k` over positive sample sizes converges to `Y`
in distribution. -/
theorem tendstoInDistribution_inv_sqrt_mul_sum (hY : HasLaw Y (gaussianReal 0 1) P')
    (h0 : ∫ ω, X 0 ω ∂P = 0) (h1 : ∫ ω, (X 0 ^ 2) ω ∂P = 1) (hindep : iIndepFun X P)
    (hident : ∀ (i : ℕ), IdentDistrib (X i) (X 0) P P) :
    TendstoInDistribution (fun (n : PositiveNat) ω ↦ invSqrt(n) * ∑ k ∈ Finset.range n, X k ω)
      atTopPositiveNat Y
      (fun _ ↦ P) P' where
  forall_aemeasurable n :=
    .const_mul (Finset.aemeasurable_fun_sum _ fun _ _ ↦ (hident _).aemeasurable_fst) _
  tendsto := by
    let Q (n : PositiveNat) : ProbabilityMeasure ℝ :=
      ⟨P.map (fun ω ↦ invSqrt(n) * ∑ k ∈ Finset.range n, X k ω)
        ((Finset.aemeasurable_fun_sum _ fun k _ ↦ (hident k).aemeasurable_fst).const_mul _),
        inferInstance⟩
    let Q₀ : ProbabilityMeasure ℝ := ⟨P'.map Y hY.aemeasurable, inferInstance⟩
    change Tendsto Q atTopPositiveNat (𝓝 Q₀)
    let succIndex (n : ℕ) : PositiveNat := ⟨n + 1, n.succ_ne_zero⟩
    have h_succ : Tendsto succIndex atTop atTopPositiveNat :=
      tendsto_comap_iff.2 (tendsto_add_atTop_nat 1)
    have h_pred : Tendsto (fun n : PositiveNat ↦ (n : ℕ) - 1) atTopPositiveNat atTop :=
      (tendsto_sub_atTop_nat 1).comp tendsto_comap
    have h_Q : Tendsto (Q ∘ succIndex) atTop (𝓝 Q₀) := by
      refine (ProbabilityMeasure.tendsto_iff_tendsto_charFun (E := ℝ)).2 fun t ↦ ?_
      have h_char : Tendsto (fun n : PositiveNat ↦ charFun (Q n : Measure ℝ) t)
          atTopPositiveNat (𝓝 (charFun (Q₀ : Measure ℝ) t)) := by
        have hmap : (Q₀ : Measure ℝ) = gaussianReal 0 1 := hY.map_eq
        rw [hmap]
        simpa [Q, charFun_inv_sqrt_mul_sum hindep hident, charFun_gaussianReal, neg_div₀] using
          tendsto_charFun_inv_sqrt_mul_pow (hident 0).aemeasurable_fst h0 h1 t
      exact h_char.comp h_succ
    have h_index (n : PositiveNat) : succIndex ((n : ℕ) - 1) = n :=
      Subtype.ext (Nat.sub_add_cancel (Nat.pos_of_ne_zero n.property))
    simpa only [Function.comp_def, h_index] using h_Q.comp h_pred

omit [IsProbabilityMeasure P] in
private lemma isUnit_sqrt_variance (h : Var[X 0; P] ≠ 0) : IsUnit (√Var[X 0; P]) :=
  (Real.sqrt_pos.2 (lt_of_le_of_ne (variance_nonneg _ _) h.symm)).ne'.isUnit

/-- **Central Limit Theorem:** Given a sequence of random variables `X : ℕ → Ω → ℝ` that are
independent, identically distributed with mean `μ` and non-zero variance `v`, and a random variable
`Y : Ω' → ℝ` following `gaussianReal 0 1`, the sequence
`n ↦ (√n)⁻¹ * (√v)⁻¹ * (∑ k ∈ Finset.range n, X k ω - n * μ)` over positive sample sizes
converges to `Y` in distribution. -/
private theorem tendstoInDistribution_inv_sqrt_mul_var_mul_sum_sub
    (hY : HasLaw Y (gaussianReal 0 1) P')
    (hX : Var[X 0; P] ≠ 0) (hindep : iIndepFun X P)
    (hident : ∀ (i : ℕ), IdentDistrib (X i) (X 0) P P) :
    TendstoInDistribution
      (fun (n : PositiveNat) ω ↦ invSqrt(n) * Checked.inv (√Var[X 0; P]) (isUnit_sqrt_variance hX) *
        (∑ k ∈ Finset.range n, X k ω - (n : ℕ) * ∫ x, X 0 x ∂P))
      atTopPositiveNat Y (fun _ ↦ P) P' := by
  have mX0 := (hident 0).aemeasurable_fst
  have hσ := isUnit_sqrt_variance hX
  have intX0 : Integrable (X 0) P := memLp_one_iff_integrable.1 <|
    (memLp_two_of_variance_ne_zero mX0.aestronglyMeasurable hX).mono_exponent (by simp)
  have (n : PositiveNat) ω : invSqrt(n) * (√Var[X 0; P])⁻¹ *
      (∑ k ∈ Finset.range n, X k ω - (n : ℕ) * ∫ x, X 0 x ∂P) =
      invSqrt(n) * ∑ k ∈ Finset.range n, (X k ω - ∫ x, X 0 x ∂P) / √Var[X 0; P] := by
    rw [← Finset.sum_div, Finset.sum_sub_distrib, div_eq_mul_inv₀]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  simp_rw [this]
  convert! tendstoInDistribution_inv_sqrt_mul_sum hY ?_ ?_ ?_ ?_
  · rw [integral_div, integral_sub intX0 (by simp)]
    simp
  · simp only [Pi.pow_apply, div_pow₀]
    rw [integral_div, ← variance_eq_integral mX0]
    apply div_eq_iff.2
    rw [one_mul, Real.sq_sqrt (variance_nonneg _ _)]
  · exact hindep.comp (fun _ x ↦ (x - ∫ ω, X 0 ω ∂P) / √Var[X 0; P]) (by fun_prop)
  · convert! fun n ↦ (hident n).comp (u := fun x ↦ (x - ∫ ω, X 0 ω ∂P) / √Var[X 0; P]) (by fun_prop)

/-- **Central Limit Theorem:** Given a sequence of random variables `X : ℕ → Ω → ℝ` that are
independent, identically distributed with mean `μ` and variance `v`, and a random variable
`Y : Ω' → ℝ` following `gaussianReal 0 v`, the sequence
`n ↦ (√n)⁻¹ * (∑ k ∈ Finset.range n, X k ω - n * μ)` over positive sample sizes
converges to `Y` in distribution. -/
@[wikidata Q190391]
theorem tendstoInDistribution_inv_sqrt_mul_sum_sub
    (hY : HasLaw Y (gaussianReal 0 Var[X 0; P].toNNReal) P')
    (hX : MemLp (X 0) 2 P) (hindep : iIndepFun X P)
    (hident : ∀ (i : ℕ), IdentDistrib (X i) (X 0) P P) :
    TendstoInDistribution
      (fun (n : PositiveNat) ω ↦ invSqrt(n) * (∑ k ∈ Finset.range n, X k ω -
        (n : ℕ) * ∫ x, X 0 x ∂P)) atTopPositiveNat Y (fun _ ↦ P) P' := by
  obtain h | h := eq_or_ne Var[X 0; P] 0
  · have : ∀ᵐ ω ∂P, ∀ n, X n ω = ∫ x, X 0 x ∂P := by
      refine ae_all_iff.2 fun n ↦ ?_
      convert! (ae_eq_integral_of_variance_eq_zero ((hident n).memLp_iff.2 hX)) ?_ using 3
      · rw [(hident n).integral_eq]
      · rwa [(hident n).variance_eq]
    have mX (n : ℕ) := (hident n).aemeasurable_fst
    refine tendstoInDistribution_of_identDistrib ⟨1, one_ne_zero⟩ (fun n ↦ ?_) ?_
    · refine ⟨by fun_prop, by fun_prop, Measure.map_congr ?_ (by fun_prop)⟩
      filter_upwards [this] with ω hω
      simp [hω]
    · refine ⟨by fun_prop, by fun_prop, ?_⟩
      rw [hY.map_eq]
      have hzero : (fun ω ↦ (√(1 : ℝ))⁻¹ *
          (X 0 ω - ∫ x, X 0 x ∂P)) =ᵐ[P] fun _ ↦ 0 := by
        filter_upwards [this] with ω hω using by simp [hω]
      simp only [Finset.sum_range_one, Nat.cast_one, one_mul]
      rw [Measure.map_congr hzero (by fun_prop)]
      simp [h]
  have hσ := isUnit_sqrt_variance h
  have : HasLaw (fun ω ↦ Y ω / √Var[X 0; P]) (gaussianReal 0 1) P' := by
    convert! gaussianReal_div_const hY _ (hc := hσ)
    · simp
    · symm
      apply div_eq_iff.2
      apply NNReal.coe_injective
      change (Var[X 0; P].toNNReal : ℝ) = 1 * √Var[X 0; P] ^ 2
      simp [Real.sq_sqrt (variance_nonneg _ _)]
  convert
    (tendstoInDistribution_inv_sqrt_mul_var_mul_sum_sub this h hindep hident).continuous_comp (g :=
      (√Var[X 0; P] * ·)) (by fun_prop) using 1
  · ext n ω
    simp only [Function.comp_apply]
    rw [← mul_assoc (√Var[X 0; P]), mul_left_comm (√Var[X 0; P]), mul_inv_cancel₀, mul_one]
  · ext ω
    exact (mul_div_cancel₀ _).symm

end ProbabilityTheory
