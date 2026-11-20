/-
Copyright (c) 2025 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The logarithm as a limit of powers

This file shows that the logarithm can be expressed as a limit of powers, namely that
`p⁻¹ * (x ^ p - 1)` tends to `log x` as positive `p` tends to zero for positive `x`.

## Main declarations

* `Real.tendstoLocallyUniformlyOn_rpow_sub_one_log`: `p⁻¹ * (x ^ p - 1)` tends uniformly to
  `log x` on compact subsets of `Ioi 0` as `p` tends to zero
* `tendsto_rpow_sub_one_log`: `p⁻¹ * (x ^ p - 1)`: the analogous statement for pointwise
  convergence.
-/

public section

open scoped Topology
open Real Filter Set

lemma Real.norm_inv_mul_rpow_sub_one_sub_log_le {p x : ℝ} (p_pos : 0 < p) (x_pos : 0 < x)
    (hx : ‖p * log x‖ ≤ 1) : ‖p⁻¹ * (x ^ p - 1) - log x‖ ≤ p * ‖log x‖ ^ 2 := by
  have pinv_nonneg : 0 ≤ p⁻¹ := inv_nonneg.mpr p_pos.le
  calc
    _ = ‖p⁻¹ * ((x ^ p - 1) - p * log x)‖ := by
      rw [mul_sub p⁻¹ (x ^ p - 1) (p * log x), ← mul_assoc, inv_mul_cancel₀, one_mul]
    _ = p⁻¹ * ‖(rexp (p * log x) - 1) - p * log x‖ := by
      rw [norm_mul, Real.norm_of_nonneg pinv_nonneg, Real.rpow_def_of_pos x_pos, mul_comm (log x) p]
    _ ≤ p⁻¹ * ‖p * log x‖ ^ 2 :=
      mul_le_mul_of_nonneg_left (Real.norm_exp_sub_one_sub_id_le hx) pinv_nonneg
    _ = p * ‖log x‖ ^ 2 := by
      rw [norm_mul, Real.norm_of_nonneg p_pos.le, mul_pow, ← mul_assoc, pow_two p,
        ← mul_assoc p⁻¹ p p, inv_mul_cancel₀, one_mul]

lemma Real.tendstoLocallyUniformlyOn_rpow_sub_one_log :
    TendstoLocallyUniformlyOn
      (fun (p : Ioi (0 : ℝ)) (x : ℝ) ↦
        Checked.inv (p : ℝ) p.property.ne'.isUnit * (x ^ (p : ℝ) - 1))
      log (comap Subtype.val (𝓝 0)) (Ioi 0) := by
  refine (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_Ioi).mpr ?_
  intro s hs hs'
  rw [Metric.uniformity_basis_dist_le.tendstoUniformlyOn_iff_of_uniformity]
  intro ε hε
  have hcont : ContinuousOn (fun x : ℝ ↦ ‖log x‖) s :=
    (continuousOn_log.mono fun x hx ↦ (hs hx).ne').norm
  obtain ⟨M, hM⟩ := (hs'.image_of_continuousOn hcont).bddAbove
  let B := max M 1
  have hB : 0 < B := zero_lt_one.trans_le (le_max_right _ _)
  have hlog (x : ℝ) (hx : x ∈ s) : ‖log x‖ ≤ B :=
    (hM (mem_image_of_mem (fun x : ℝ ↦ ‖log x‖) hx)).trans (le_max_left _ _)
  have hδ : 0 < min (1 / B) (ε / B ^ 2) :=
    lt_min (div_pos zero_lt_one hB) (div_pos hε (pow_pos hB _))
  have hp : ∀ᶠ p : Ioi (0 : ℝ) in comap Subtype.val (𝓝 0),
      (p : ℝ) ≤ min (1 / B) (ε / B ^ 2) :=
    tendsto_comap.eventually (eventually_le_nhds hδ)
  filter_upwards [hp] with p hp
  intro x hx
  have hx' : ‖(p : ℝ) * log x‖ ≤ 1 := calc
    _ = (p : ℝ) * ‖log x‖ := by rw [norm_mul, Real.norm_of_nonneg p.property.le]
    _ ≤ (p : ℝ) * B := mul_le_mul_of_nonneg_left (hlog x hx) p.property.le
    _ ≤ 1 := (le_div_iff₀ hB).mp (hp.trans (min_le_left _ _))
  rw [dist_eq_norm']
  calc
    _ ≤ (p : ℝ) * ‖log x‖ ^ 2 := Real.norm_inv_mul_rpow_sub_one_sub_log_le p.property (hs hx) hx'
    _ ≤ (p : ℝ) * B ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hlog x hx) 2) p.property.le
    _ ≤ ε := (le_div_iff₀ (pow_pos hB 2)).mp (hp.trans (min_le_right _ _))

lemma tendsto_rpow_sub_one_log {x : ℝ} (hx : 0 < x) :
    Tendsto (fun p : Ioi (0 : ℝ) ↦ Checked.inv (p : ℝ) p.property.ne'.isUnit * (x ^ (p : ℝ) - 1))
      (comap Subtype.val (𝓝 0)) (𝓝 (log x)) :=
  TendstoLocallyUniformlyOn.tendsto_at
    tendstoLocallyUniformlyOn_rpow_sub_one_log (Set.mem_Ioi.mpr hx)
