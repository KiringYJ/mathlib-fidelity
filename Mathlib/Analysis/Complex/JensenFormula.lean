/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Complex.Harmonic.Poisson
public import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage


/-!
# Jensen's Formula of Complex Analysis

If a function `g : ℂ → ℂ` is analytic without zero on the closed ball with center `c` and radius
`R`, then `log ‖g ·‖` is harmonic, and the mean value theorem of harmonic functions asserts that the
circle average `circleAverage (log ‖g ·‖) c R` equals `log ‖g c‖`.  Note that `g c` equals
`meromorphicTrailingCoeffAt g c` and see `AnalyticOnNhd.circleAverage_log_norm_of_ne_zero` for the
precise statement.

Jensen's Formula, formulated in `MeromorphicOn.circleAverage_log_norm` below, generalizes this to
the setting where `g` is merely meromorphic and has finite order at every point of the ball
(equivalently, since the ball is connected, at `c`). In that case, the
`circleAverage (log ‖g ·‖) c R` equals the logarithm of the norm of the trailing coefficient
`meromorphicTrailingCoeffAt g c` plus a correction term that accounts for the zeros and poles of `g`
within the ball.
-/

public section

open Filter MeromorphicAt MeasureTheory MeromorphicOn Metric Real Set Topology
open scoped ComplexConjugate


/-!
## Preparatory Material

In preparation to the proof of Jensen's formula, compute several circle averages and reformulate
some of the terms that appear in the formula and its proof.
-/

private noncomputable def herglotzLogIntegrand (w ρ : ℂ) (z : ({w}ᶜ : Set ℂ)) : ℝ :=
  (herglotzRieszKernel 0 w z).re * Real.log ‖z.val - ρ‖

private lemma continuousAt_herglotzLogIntegrand {w ρ : ℂ} {z : ({w}ᶜ : Set ℂ)}
    (hz : z.val ≠ ρ) : ContinuousAt (herglotzLogIntegrand w ρ) z := by
  have hn : ‖z.val - ρ‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hz)
  have hc : ContinuousAt (fun x : ({w}ᶜ : Set ℂ) ↦ ‖x.val - ρ‖) z := by fun_prop
  have hl : ContinuousAt (fun x : ({w}ᶜ : Set ℂ) ↦ log ‖x.val - ρ‖) z := hc.log hn
  exact ((Complex.continuous_re.comp (continuous_herglotzRieszKernel 0 w)).continuousAt).mul hl

private noncomputable def circleMapAvoidingPole (w : ℂ) (r : Ioi ‖w‖) (θ : ℝ) :
    ({w}ᶜ : Set ℂ) :=
  ⟨circleMap 0 r.val θ, mem_compl_singleton_iff.mpr <| ne_of_apply_ne norm <| by
    have hr : 0 < r.val := (norm_nonneg _).trans_lt (mem_Ioi.mp r.2)
    simpa only [norm_circleMap_zero, abs_of_pos hr] using (mem_Ioi.mp r.2).ne'⟩

private lemma continuous_herglotzLogIntegrand_circle {w ρ : ℂ} {R : ℝ} (hρ : ‖ρ‖ = R)
    (r : Ioi ‖w‖) (hr : r.val < R) :
    Continuous (fun θ ↦ herglotzLogIntegrand w ρ (circleMapAvoidingPole w r θ)) := by
  have hpos : 0 < r.val := (norm_nonneg _).trans_lt (mem_Ioi.mp r.2)
  have hmap : Continuous (circleMapAvoidingPole w r) := (continuous_circleMap 0 r.val).subtype_mk _
  refine continuous_iff_continuousAt.2 fun θ ↦ ?_
  have hne : (circleMapAvoidingPole w r θ).val ≠ ρ := by
    apply ne_of_apply_ne norm
    simpa only [circleMapAvoidingPole, norm_circleMap_zero, abs_of_pos hpos, hρ] using hr.ne
  exact (continuousAt_herglotzLogIntegrand hne).comp hmap.continuousAt

open Complex in
private lemma const_mul_norm_sub_circleMap_le_norm_sub_circleMap {r₀ r R : ℝ} {ρ : ℂ}
    (hρ : ‖ρ‖ = R) (hr₀ : 0 < r₀) (hR : 0 < R) (hr₀r : r₀ ≤ r) (hrR : r ≤ R) (θ : ℝ) :
    sqrt (r₀ / R) * ‖circleMap 0 R θ - ρ‖ ≤ ‖circleMap 0 r θ - ρ‖ := by
  have h_cos_law (r₁ : ℝ) :
      ‖circleMap 0 r₁ θ - ρ‖ ^ 2 = r₁ ^ 2 + R ^ 2 - 2 * r₁ * R * Real.cos (θ - Complex.arg ρ) := by
    rw [← ofReal_inj, ← normSq_eq_norm_sq, normSq_sub]
    suffices (circleMap 0 r₁ θ * (conj) ρ).re = r₁ * ‖ρ‖ * Real.cos (θ - ρ.arg) by
      simp [normSq_eq_norm_sq, hρ, -mul_re, this, mul_assoc]
    conv_lhs => rw [← norm_mul_exp_arg_mul_I ρ, ← circleMap_zero, conj_circleMap_zero,
      circleMap_zero_mul, circleMap_zero_re, ← sub_eq_add_neg]
  have hsq : (r₀ / R) * ‖circleMap 0 R θ - ρ‖ ^ 2 ≤ ‖circleMap 0 r θ - ρ‖ ^ 2 := by
    rw [div_mul_eq_mul_div₀, div_le_iff₀ hR]
    nlinarith [h_cos_law r, h_cos_law R, mul_le_mul_of_nonneg_left hr₀r hR.le,
      mul_le_mul_of_nonneg_left hrR hR.le, neg_one_le_cos, cos_le_one]
  grw [← sqrt_sq (norm_nonneg _), ← sqrt_mul (by positivity), hsq, sqrt_sq (norm_nonneg _)]

private lemma norm_herglotzLogIntegrand_circleMap_le {w ρ : ℂ} {R r₀ : ℝ} (hR : 0 < R)
    (hρ : ‖ρ‖ = R) (hr₀ : ‖w‖ < r₀) (r : Ioi ‖w‖) (hr₀r : r₀ ≤ r.val) (hrR : r.val ≤ R)
    (θ : ℝ) (hdR : 0 < ‖circleMap 0 R θ - ρ‖) :
    ‖herglotzLogIntegrand w ρ (circleMapAvoidingPole w r θ)‖ ≤
      ((R + ‖w‖) / (r₀ - ‖w‖)) *
        (|log (2 * R)| + |log (sqrt (r₀ / R))| + |log ‖circleMap 0 R θ - ρ‖|) := by
  have hrw : ‖w‖ < r.val := mem_Ioi.mp r.2
  have hpos : 0 < r.val := (norm_nonneg _).trans_lt hrw
  have h₀ : 0 < r₀ := (norm_nonneg _).trans_lt hr₀
  have hden : 0 < r₀ - ‖w‖ := sub_pos.mpr hr₀
  let z : ℂ := circleMap 0 r.val θ
  have hz : z ∈ sphere 0 r.val := circleMap_mem_sphere 0 hpos.le θ
  have hw : w ∈ ball 0 r.val := by simpa only [mem_ball_iff_norm, sub_zero] using hrw
  have hker₀ : 0 ≤ (herglotzRieszKernel 0 w (circleMapAvoidingPole w r θ)).re := by
    apply le_trans _ (le_re_herglotzRieszKernel hz hw)
    exact div_nonneg (sub_nonneg.mpr (mem_ball_iff_norm.mp hw).le) (by positivity)
  have hker : |(herglotzRieszKernel 0 w (circleMapAvoidingPole w r θ)).re| ≤
      (R + ‖w‖) / (r₀ - ‖w‖) := by
    rw [abs_of_nonneg hker₀]
    calc
      _ ≤ (r.val + ‖w‖) / (r.val - ‖w‖) := by
        simpa only [z, circleMapAvoidingPole, sub_zero] using re_herglotzRieszKernel_le hz hw
      _ ≤ _ := div_le_div₀ (by positivity) (by linarith) hden
        (sub_le_sub_right hr₀r _)
  have hmin := const_mul_norm_sub_circleMap_le_norm_sub_circleMap hρ h₀ hR hr₀r hrR θ
  have hzρ : 0 < ‖z - ρ‖ := (mul_pos (sqrt_pos_of_pos (div_pos h₀ hR)) hdR).trans_le hmin
  have hlog₁ : log (sqrt (r₀ / R)) + log ‖circleMap 0 R θ - ρ‖ ≤ log ‖z - ρ‖ := by
    rw [← log_mul (by positivity) hdR.ne']
    exact log_le_log (by positivity) hmin
  have hlog₂ : log ‖z - ρ‖ ≤ log (2 * R) := by
    apply log_le_log hzρ
    refine (norm_sub_le z ρ).trans ?_
    simp only [z, norm_circleMap_zero, abs_of_pos hpos, hρ, two_mul]
    linarith
  have hlog : |log ‖z - ρ‖| ≤ |log (2 * R)| + |log (sqrt (r₀ / R))| +
      |log ‖circleMap 0 R θ - ρ‖| := by
    apply abs_le.mpr
    constructor
    · linarith [neg_abs_le (log (sqrt (r₀ / R))), neg_abs_le (log ‖circleMap 0 R θ - ρ‖),
        abs_nonneg (log (2 * R))]
    · linarith [le_abs_self (log (2 * R)), abs_nonneg (log (sqrt (r₀ / R))),
        abs_nonneg (log ‖circleMap 0 R θ - ρ‖)]
  simp only [herglotzLogIntegrand, Real.norm_eq_abs, abs_mul]
  exact mul_le_mul hker hlog (abs_nonneg _) (by positivity)

private noncomputable def herglotzLogAverage (w ρ : ℂ) (r : Ioi ‖w‖) : ℝ :=
  Real.circleAverageOn (fun z : sphere (0 : ℂ) |r.val| ↦
    herglotzLogIntegrand w ρ ⟨z.val, mem_compl_singleton_iff.mpr <| sub_ne_zero.mp
      (isUnit_sub_of_mem_sphere_of_mem_ball
        (mem_ball_iff_norm.mpr (by simpa only [sub_zero] using mem_Ioi.mp r.2)) z).ne_zero⟩)

private lemma herglotzLogAverage_eq (w ρ : ℂ) (r : Ioi ‖w‖) :
    herglotzLogAverage w ρ r =
      (2 * π)⁻¹ • ∫ θ : ℝ in 0..2 * π, herglotzLogIntegrand w ρ (circleMapAvoidingPole w r θ) := by
  have hr : 0 < r.val := (norm_nonneg _).trans_lt (mem_Ioi.mp r.2)
  simp only [herglotzLogAverage, Real.circleAverageOn, circleMapAvoidingPole, abs_of_pos hr]

private theorem herglotzLogAverage_tendsto {ρ w : ℂ} {R : ℝ} (hR : 0 < R)
    (hρ : ‖ρ‖ = R) (hw : ‖w‖ < R) {r : ℕ → Ioo ‖w‖ R}
    (hr : Tendsto (fun n ↦ (r n).val) atTop (nhds R)) :
    Tendsto (fun n ↦ herglotzLogAverage w ρ ⟨(r n).val, (r n).2.1⟩) atTop
      (nhds (herglotzLogAverage w ρ ⟨R, hw⟩)) := by
  let r₀ := (R + ‖w‖) / 2
  have h₀w : ‖w‖ < r₀ := by dsimp [r₀]; linarith
  have h₀R : r₀ < R := by dsimp [r₀]; linarith
  have h₀ : 0 < r₀ := (norm_nonneg _).trans_lt h₀w
  have hden : 0 < r₀ - ‖w‖ := sub_pos.mpr h₀w
  let bound (θ : ℝ) := ((R + ‖w‖) / (r₀ - ‖w‖)) *
    (|log (2 * R)| + |log (sqrt (r₀ / R))| + |log ‖circleMap 0 R θ - ρ‖|)
  have hnull : volume {θ : ℝ | circleMap 0 R θ = ρ} = 0 :=
    ((countable_singleton ρ).preimage_circleMap 0 hR.ne').measure_zero _
  have hAE : ∀ᵐ θ : ℝ, circleMap 0 R θ ≠ ρ := measure_eq_zero_iff_ae_notMem.mp hnull
  simp_rw [herglotzLogAverage_eq]
  apply Tendsto.smul tendsto_const_nhds
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence bound
  · exact Eventually.of_forall fun n ↦
      (continuous_herglotzLogIntegrand_circle hρ
        ⟨(r n).val, (r n).2.1⟩ (r n).2.2).aestronglyMeasurable
  · filter_upwards [hr.eventually (le_mem_nhds h₀R)] with n hn
    filter_upwards [hAE] with θ hθ _
    exact norm_herglotzLogIntegrand_circleMap_le hR hρ h₀w ⟨(r n).val, (r n).2.1⟩ hn
      (r n).2.2.le θ (norm_pos_iff.mpr (sub_ne_zero.mpr hθ))
  · apply (IntervalIntegrable.add (by simp) (by simp)).add ?_ |>.const_mul
    exact .abs <| MeromorphicOn.circleIntegrable_log_norm (f := fun z ↦ z - ρ) (by fun_prop)
  · filter_upwards [hAE] with θ hθ _
    have hcont : Continuous (fun a : Ioi ‖w‖ ↦ circleMapAvoidingPole w a θ) := by
      unfold circleMapAvoidingPole
      apply Continuous.subtype_mk
      unfold circleMap
      fun_prop
    have ht : Tendsto (fun n ↦ (⟨(r n).val, (r n).2.1⟩ : Ioi ‖w‖)) atTop
        (nhds (⟨R, hw⟩ : Ioi ‖w‖)) := tendsto_subtype_rng.mpr hr
    exact (continuousAt_herglotzLogIntegrand hθ).tendsto.comp (hcont.continuousAt.tendsto.comp ht)

/-- The logarithmic Poisson formula at the origin for a pole on the boundary. -/
theorem circleAverage_re_herglotzRieszKernel_mul_log₀ {w ρ : ℂ} {R : ℝ} (hρ : ρ ∈ sphere 0 R)
    (hw : w ∈ ball 0 R) :
    Real.circleAverageOn (fun z : sphere (0 : ℂ) |R| ↦
      (herglotzRieszKernel 0 w ⟨z.val, mem_compl_singleton_iff.mpr
        (sub_ne_zero.mp (isUnit_sub_of_mem_sphere_of_mem_ball hw z).ne_zero)⟩).re *
        Real.log ‖z.val - ρ‖) =
      log ‖w - ρ‖ := by
  have hR : 0 < R := pos_of_mem_ball hw
  have hρ' : ‖ρ‖ = R := by simpa only [sub_zero] using mem_sphere_iff_norm.mp hρ
  have hw' : ‖w‖ < R := by simpa only [sub_zero] using mem_ball_iff_norm.mp hw
  let r (n : ℕ) : ℝ := R - (R - ‖w‖) / ((n : ℝ) + 2)
  have hr_lt (n : ℕ) : r n < R := sub_lt_self _ (div_pos (sub_pos.mpr hw') (by positivity))
  have hwr (n : ℕ) : ‖w‖ < r n := by
    dsimp only [r]
    rw [lt_sub_iff_add_lt]
    have h : (R - ‖w‖) / ((n : ℝ) + 2) < R - ‖w‖ := by
      refine (div_lt_iff₀ (by positivity)).2 ?_
      exact lt_mul_of_one_lt_right (sub_pos.mpr hw')
        (by linarith [Nat.cast_nonneg (α := ℝ) n])
    linarith
  let p (n : ℕ) : Ioo ‖w‖ R := ⟨r n, hwr n, hr_lt n⟩
  have hr : Tendsto (fun n ↦ (p n).val) atTop (nhds R) := by
    have ht : Tendsto (fun n : ℕ ↦ (n : ℝ) + 2) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    have hdiv : Tendsto (fun n : ℕ ↦ (R - ‖w‖) / ((n : ℝ) + 2)) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop ht
    simpa only [p, r, sub_zero] using (tendsto_const_nhds (x := R)).sub hdiv
  have hmean (n : ℕ) : herglotzLogAverage w ρ ⟨(p n).val, (p n).2.1⟩ = log ‖w - ρ‖ := by
    have hwr' : w ∈ ball 0 (r n) := mem_ball_iff_norm.mpr (by simpa only [sub_zero] using hwr n)
    unfold herglotzLogAverage
    simpa only [herglotzLogIntegrand, smul_eq_mul] using
      (InnerProductSpace.HarmonicContOnCl.circleAverage_re_herglotzRieszKernel_smul
        (f := fun z ↦ log ‖z - ρ‖)
        (by
          refine ⟨fun z hz ↦ ?_, fun z hz ↦ ?_⟩
          · exact AnalyticAt.harmonicAt_log_norm (by fun_prop)
              (by grind [mem_ball, dist_zero_right, hr_lt n])
          · have key := mem_closedBall_iff_norm.mp (closure_ball_subset_closedBall hz)
            have hne : ‖z - ρ‖ ≠ 0 := by
              apply norm_ne_zero_iff.mpr
              rw [sub_ne_zero]
              grind [sub_zero, hr_lt n]
            fun_prop)
        hwr')
  have hlim := herglotzLogAverage_tendsto hR hρ' hw' hr
  have hconst : Tendsto (fun n ↦ herglotzLogAverage w ρ ⟨(p n).val, (p n).2.1⟩) atTop
      (nhds (log ‖w - ρ‖)) := by simp only [hmean, tendsto_const_nhds]
  change herglotzLogAverage w ρ ⟨R, hw'⟩ = log ‖w - ρ‖
  exact tendsto_nhds_unique hlim hconst

/-- The logarithmic Poisson formula for a boundary pole on a disk. -/
theorem circleAverage_re_herglotzRieszKernel_mul_log {w ρ c : ℂ} {R : ℝ} (hρ : ρ ∈ sphere c R)
    (hw : w ∈ ball c R) :
    Real.circleAverageOn (fun z : sphere c |R| ↦
      (herglotzRieszKernel c w ⟨z.val, mem_compl_singleton_iff.mpr
        (sub_ne_zero.mp (isUnit_sub_of_mem_sphere_of_mem_ball hw z).ne_zero)⟩).re *
        Real.log ‖z.val - ρ‖) = log ‖w - ρ‖ := by
  have hρ' : ρ - c ∈ sphere 0 R := by
    simpa only [mem_sphere_iff_norm, sub_zero] using hρ
  have hw' : w - c ∈ ball 0 R := by
    simpa only [mem_ball_iff_norm, sub_zero] using hw
  calc
    _ = Real.circleAverageOn (fun z : sphere (0 : ℂ) |R| ↦
        herglotzLogIntegrand (w - c) (ρ - c) ⟨z.val, mem_compl_singleton_iff.mpr
          (sub_ne_zero.mp (isUnit_sub_of_mem_sphere_of_mem_ball hw' z).ne_zero)⟩) := by
      unfold Real.circleAverageOn
      congr 2
      funext θ
      have hcircle : circleMap c |R| θ = circleMap 0 |R| θ + c :=
        eq_add_of_sub_eq (circleMap_sub_center c |R| θ)
      have hz : circleMap 0 |R| θ ∈ ({w - c}ᶜ : Set ℂ) := mem_compl_singleton_iff.mpr <|
        sub_ne_zero.mp (isUnit_sub_of_mem_sphere_of_mem_ball hw'
          ⟨circleMap 0 |R| θ, circleMap_mem_sphere 0 (abs_nonneg R) θ⟩).ne_zero
      have hker := herglotzRieszKernel_add_const c w ⟨circleMap 0 |R| θ, hz⟩
      have hlog : circleMap 0 |R| θ + c - ρ = circleMap 0 |R| θ - (ρ - c) := by abel
      simp only [herglotzLogIntegrand, hlog, hcircle, hker]
    _ = _ := by
      simpa only [herglotzLogIntegrand, sub_sub_sub_cancel_right] using
        circleAverage_re_herglotzRieszKernel_mul_log₀ hρ' hw'


/--
Let `D : ℂ → ℤ` be a function with locally finite support within the closed ball with center `c` and
radius `R`, such as the zero- and pole divisor of a meromorphic function.  Then, the circle average
of the function `∑ᶠ u, (D u * log ‖· - u‖)` over the boundary of the ball equals
`∑ᶠ u, D u * log R`.
-/
@[simp]
lemma circleAverage_log_norm_factorizedRational {R : ℝ} {c : ℂ}
    (D : Function.locallyFinsuppWithin (closedBall c |R|) ℤ) :
    circleAverage (∑ᶠ u, (D u * log ‖· - u‖)) c R = ∑ᶠ u, D u * log R := by
  have h := D.finiteSupport (isCompact_closedBall c |R|)
  calc circleAverage (∑ᶠ u, (D u * log ‖· - u‖)) c R
  _ = circleAverage (∑ u ∈ h.toFinset, (D u * log ‖· - u‖)) c R := by
    rw [finsum_eq_sum_of_support_subset]
    intro u
    contrapose
    aesop
  _ = ∑ i ∈ h.toFinset, circleAverage (fun x ↦ D i * log ‖x - i‖) c R := by
    rw [circleAverage_sum]
    intro u hu
    apply IntervalIntegrable.const_mul
    apply (analyticOnNhd_id.sub analyticOnNhd_const).meromorphicOn.circleIntegrable_log_norm
  _ = ∑ u ∈ h.toFinset, D u * log R := by
    apply Finset.sum_congr rfl
    intro u hu
    simp_rw [← smul_eq_mul, circleAverage_fun_smul]
    congr
    rw [circleAverage_log_norm_sub_const_of_mem_closedBall]
    apply D.supportWithinDomain
    simp_all
  _ = ∑ᶠ u, D u * log R := by
    rw [finsum_eq_sum_of_support_subset]
    intro u
    aesop

/--
If  `g : ℂ → ℂ` is analytic without zero on the closed ball with center `c` and radius `R`, then the
circle average `circleAverage (log ‖g ·‖) c R` equals `log ‖g c‖`.
-/
@[simp]
lemma AnalyticOnNhd.circleAverage_log_norm_of_ne_zero {R : ℝ} {c : ℂ} {g : ℂ → ℂ}
    (h₁g : AnalyticOnNhd ℂ g (closedBall c |R|)) (h₂g : ∀ u ∈ closedBall c |R|, g u ≠ 0) :
    circleAverage (Real.log ‖g ·‖) c R = Real.log ‖g c‖ :=
  InnerProductSpace.HarmonicOnNhd.circleAverage_eq
    (fun x hx ↦ (h₁g x hx).harmonicAt_log_norm (h₂g x hx))

/-!
## Jensen's Formula
-/

/--
**Jensen's Formula**: If `f : ℂ → ℂ` is meromorphic on the closed ball with center `c` and radius
`R` and has finite order at every point of the ball, then the `circleAverage (log ‖f ·‖) c R` equals
the logarithm of the norm of the trailing coefficient `meromorphicTrailingCoeffAt f c` plus a
correction term that accounts for the zeros and poles of `f` within the ball. Since the closed ball
is connected, finite order at one point of the ball gives finite order at every point
(`MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected`).

See `Function.locallyFinsuppWithin.logCounting_divisor_eq_circleAverage_sub_const` for a
reformulation in terms of the logarithmic counting function of Value Distribution Theory.
-/
theorem MeromorphicOn.circleAverage_log_norm {c : ℂ} {R : ℝ} {f : ℂ → ℂ} (hR : R ≠ 0)
    (h₁f : MeromorphicOn f (closedBall c |R|))
    (h₂f : ∀ u (hu : u ∈ closedBall c |R|), meromorphicOrderAt f u (h₁f u hu) ≠ ⊤) :
    circleAverage (log ‖f ·‖) c R
      = ∑ᶠ u, divisor f (closedBall c |R|) h₂f u * (log R - log ‖c - u‖)
        + log ‖meromorphicTrailingCoeffAt f c (h₂f c (mem_closedBall_self (abs_nonneg R)))‖ := by
  -- Shorthand notation to keep line size in check
  let CB := closedBall c |R|
  have t₀ : c ∈ CB := mem_closedBall_self (abs_nonneg R)
  have h₄f := (divisor f CB h₂f).finiteSupport (isCompact_closedBall c |R|)
  -- Extract zeros & poles and compute
  obtain ⟨g, h₁g, h₂g, h₃g⟩ := h₁f.extract_zeros_poles h₂f h₄f
  calc circleAverage (log ‖f ·‖) c R
  _ = circleAverage ((∑ᶠ u, (divisor f CB h₂f u * log ‖· - u‖)) + (log ‖g ·‖)) c R := by
    have h₄g := extract_zeros_poles_log h₂g h₃g
    rw [circleAverage_congr_codiscreteWithin (codiscreteWithin_mono sphere_subset_closedBall h₄g)
      hR]
  _ = circleAverage (∑ᶠ u, (divisor f CB h₂f u * log ‖· - u‖)) c R
      + circleAverage (log ‖g ·‖) c R :=
    circleAverage_add (circleIntegrable_log_norm_factorizedRational (divisor f CB h₂f))
      ((h₁g.mono sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm)
  _ = ∑ᶠ u, divisor f CB h₂f u * log R + log ‖g c‖ := by
    simp only [circleAverage_log_norm_factorizedRational, add_right_inj]
    rw [h₁g.circleAverage_log_norm_of_ne_zero]
    exact fun u hu ↦ h₂g ⟨u, hu⟩
  _ = ∑ᶠ u, divisor f CB h₂f u * log R
    + (log ‖meromorphicTrailingCoeffAt f c (h₂f c t₀)‖
      - ∑ᶠ u, divisor f CB h₂f u * log ‖c - u‖) := by
    have t₁ : AccPt c (𝓟 CB) := by
      apply accPt_iff_frequently_nhdsNE.mpr
      apply compl_notMem
      apply mem_nhdsWithin.mpr
      use ball c |R|
      simpa [hR] using! fun _ ⟨h, _⟩ ↦ ball_subset_closedBall h
    simp [MeromorphicOn.log_norm_meromorphicTrailingCoeffAt_extract_zeros_poles h₄f t₀ t₁
      (h₁f c t₀) (h₁g c t₀) (h₂g ⟨c, t₀⟩) h₃g]
  _ = ∑ᶠ u, divisor f CB h₂f u * log R - ∑ᶠ u, divisor f CB h₂f u * log ‖c - u‖
    + log ‖meromorphicTrailingCoeffAt f c (h₂f c t₀)‖ := by
    ring
  _ = (∑ᶠ u, divisor f CB h₂f u * (log R - log ‖c - u‖))
    + log ‖meromorphicTrailingCoeffAt f c (h₂f c t₀)‖ := by
    rw [← finsum_sub_distrib]
    · simp_rw [← mul_sub]
    repeat apply h₄f.subset (fun _ ↦ (by simp_all))

/--
A function that is analytic on a neighborhood of a closed ball and does not vanish at its center has
finite order at every point of the ball.
-/
lemma AnalyticOnNhd.meromorphicOrderAt_ne_top_closedBall {c : ℂ} {r : ℝ} {f : ℂ → ℂ}
    (h₁f : AnalyticOnNhd ℂ f (closedBall c |r|)) (h₂f : f c ≠ 0) :
    ∀ z (hz : z ∈ closedBall c |r|), meromorphicOrderAt f z (h₁f.meromorphicOn z hz) ≠ ⊤ :=
  h₁f.meromorphicOrderAt_ne_top_of_ne_zero (convex_closedBall c |r|).isPreconnected
    (mem_closedBall_self (abs_nonneg r)) h₂f

/-- **Jensen's Formula** specialized to the case that `f` is analytic and `f c ≠ 0`. -/
theorem AnalyticOnNhd.circleAverage_log_norm {c : ℂ} {R : ℝ} {f : ℂ → ℂ} (hR : R ≠ 0)
    (h₁f : AnalyticOnNhd ℂ f (closedBall c |R|))
    (h₂f : f c ≠ 0) :
    circleAverage (Real.log ‖f ·‖) c R
      = ∑ᶠ u, divisor f (closedBall c |R|) (h₁f.meromorphicOrderAt_ne_top_closedBall h₂f) u *
        (Real.log R - Real.log ‖c - u‖) + Real.log ‖f c‖ := by
  have hc := mem_closedBall_self (x := c) (abs_nonneg R)
  have hfin := h₁f.meromorphicOrderAt_ne_top_closedBall h₂f
  rw [h₁f.meromorphicOn.circleAverage_log_norm hR hfin,
    (h₁f c hc).meromorphicTrailingCoeffAt_of_ne_zero h₂f]

/--
**Jensen's Inequality**: Estimates the number of zeros of `f` in a ball of radius `r`
given that `f` is analytic and bounded by `M` on a larger ball of radius `R`.
-/
theorem AnalyticOnNhd.sum_divisor_le {c : ℂ} {r R M : ℝ} {f : ℂ → ℂ} (r_pos : 0 < |r|)
    (r_lt_R : |r| < |R|) (hM : 1 ≤ M) (h₁f : AnalyticOnNhd ℂ f (closedBall c |R|))
    (h₂f : f c ≠ 0)
    (f_bound : ∀ z ∈ sphere c |R|, ‖f z‖ ≤ M) :
    ∑ᶠ u, divisor f (closedBall c |r|)
        ((h₁f.mono (closedBall_subset_closedBall r_lt_R.le)).meromorphicOrderAt_ne_top_closedBall
          h₂f) u ≤
      Checked.div (Real.log M - Real.log ‖f c‖) (Real.log |R| - Real.log |r|)
        (sub_pos.mpr (Real.log_lt_log r_pos r_lt_R)).ne'.isUnit := by
  have hr :=
    (h₁f.mono (closedBall_subset_closedBall r_lt_R.le)).meromorphicOrderAt_ne_top_closedBall h₂f
  have hR' := h₁f.meromorphicOrderAt_ne_top_closedBall h₂f
  have hDnonneg (u : ℂ) : 0 ≤ divisor f (closedBall c |R|) hR' u := h₁f.divisor_nonneg (h := hR') u
  -- Push the coercion inside the sum
  trans ∑ᶠ u, (divisor f (closedBall c |r|) hr u : ℝ)
  · exact map_finsum (Int.castRingHom ℝ)
      ((divisor _ _ hr).finiteSupport <| isCompact_closedBall ..) |>.le
  -- Rearrange: move `log R/r` to the LHS and inside the sum.
  have hgap : 0 < Real.log |R| - Real.log |r| := sub_pos.mpr (Real.log_lt_log r_pos r_lt_R)
  apply (le_div_iff₀ hgap).mpr
  rw [finsum_mul]
  have jensen := h₁f.circleAverage_log_norm (abs_ne_zero.mp (by linarith)) h₂f
  -- Estimate the circleAverage using the bound on f
  have integral_bound : circleAverage (fun x ↦ Real.log ‖f x‖) c R ≤ Real.log M := by
    apply circleAverage_mono_on_of_le_circle
    · exact (h₁f.mono sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm
    · gconvert f_bound using 2 with z hz
      obtain (h | h) := eq_zero_or_norm_pos (f z)
      · simpa [h] using log_nonneg hM
      · gcongr
  calc
  -- Bound by the sum from Jensen's formula
  _ ≤ ∑ᶠ u, ((divisor f (closedBall c |R|) hR') u) * (Real.log R - Real.log ‖c - u‖) := by
    refine finsum_le_finsum ?_ ?_ fun u ↦ ?_
    · exact (divisor f (closedBall c |r|) hr).finiteSupport (isCompact_closedBall ..) |>.subset
        fun _ _ ↦ (by simp_all)
    · exact (divisor f (closedBall c |R|) hR').finiteSupport (isCompact_closedBall ..) |>.subset
        fun _ _ ↦ (by simp_all)
    · -- Core bound: estimate the summand by splitting on which ball u is in
      by_cases h1 : u ∈ closedBall c |R|
      · by_cases h2 : u ∈ closedBall c |r|
        · --In the smaller ball: the divisors agree and we bound the log factor
          have e : divisor f (closedBall c |r|) hr u = divisor f (closedBall c |R|) hR' u := by
            exact_mod_cast (MeromorphicOn.coe_divisor_apply _ h2).trans
              (MeromorphicOn.coe_divisor_apply _ h1).symm
          rw [e]
          by_cases! h3 : u = c --Need to use the divisor is 0 at c rather than comparing the logs
          · subst h3
            have h₀ : divisor f (closedBall u |R|) hR' u = 0 := divisor_apply_eq_zero
              ((h₁f u h1).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.2 h₂f)
            simp [h₀]
          apply mul_le_mul_of_nonneg_left _ (Int.cast_nonneg (hDnonneg u))
          rw [Real.log_abs]
          apply sub_le_sub_left
          exact Real.log_le_log (norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm h3))) (by
            simpa [mem_closedBall, dist_eq_norm'] using h2)
        · simp only [h2, not_false_eq_true, Function.locallyFinsuppWithin.apply_eq_zero_of_notMem,
            Int.cast_zero, zero_mul]
          apply mul_nonneg (Int.cast_nonneg (hDnonneg u))
          rw [← Real.log_abs R]
          apply sub_nonneg.mpr
          have hn : 0 < ‖c - u‖ := r_pos.trans (lt_of_not_ge (by
            simpa [mem_closedBall, dist_eq_norm'] using h2))
          exact Real.log_le_log hn (by simpa [mem_closedBall, dist_eq_norm'] using h1)
      · --Outside the larger ball so both sides are 0
        have : u ∉ closedBall c |r| := by
          simp_all
          linarith
        simp [h1, this]
  _ ≤ Real.log M - Real.log ‖f c‖ := by linarith --Uses jensen and integral_bound
