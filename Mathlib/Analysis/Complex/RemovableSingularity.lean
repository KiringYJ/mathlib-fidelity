/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Removable singularity theorem

In this file we prove Riemann's removable singularity theorem: if `f : ℂ → E` is complex
differentiable in a punctured neighborhood of a point `c` and is bounded in a punctured neighborhood
of `c` (or, more generally, $f(z) - f(c)=o((z-c)^{-1})$), then it has a limit at `c` and the
function `update f c (limUnder (𝓝[≠] c) f)` is complex differentiable in a neighborhood of `c`.
-/

public section


open TopologicalSpace Metric Set Filter Asymptotics Function MeasureTheory

open scoped Topology Filter NNReal Real Interval

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

namespace Complex

/-- **Removable singularity** theorem, weak version. If `f : ℂ → E` is differentiable in a punctured
neighborhood of a point and is continuous at this point, then it is analytic at this point. -/
theorem analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt {f : ℂ → E} {c : ℂ}
    (hd : ∀ᶠ z in 𝓝[≠] c, DifferentiableAt ℂ f z) (hc : ContinuousAt f c) : AnalyticAt ℂ f c := by
  rcases (nhdsWithin_hasBasis nhds_basis_closedBall _).mem_iff.1 hd with ⟨R, hR0, hRs⟩
  lift R to ℝ≥0 using hR0.le
  replace hc : ContinuousOn f (closedBall c R) := by
    refine fun z hz => ContinuousAt.continuousWithinAt ?_
    rcases eq_or_ne z c with (rfl | hne)
    exacts [hc, (hRs ⟨hz, hne⟩).continuousAt]
  exact (hasFPowerSeriesOnBall_of_differentiable_off_countable (countable_singleton c) hc
    (fun z hz => hRs (sdiff_subset_sdiff_left ball_subset_closedBall hz)) hR0).analyticAt

theorem differentiableOn_compl_singleton_and_continuousAt_iff {f : ℂ → E} {s : Set ℂ} {c : ℂ}
    (hs : s ∈ 𝓝 c) :
    DifferentiableOn ℂ f (s \ {c}) ∧ ContinuousAt f c ↔ DifferentiableOn ℂ f s := by
  refine ⟨?_, fun hd => ⟨hd.mono sdiff_subset, (hd.differentiableAt hs).continuousAt⟩⟩
  rintro ⟨hd, hc⟩ x hx
  rcases eq_or_ne x c with (rfl | hne)
  · refine (analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
      ?_ hc).differentiableAt.differentiableWithinAt
    refine eventually_nhdsWithin_iff.2 ((eventually_mem_nhds_iff.2 hs).mono fun z hz hzx => ?_)
    exact hd.differentiableAt (inter_mem hz (isOpen_ne.mem_nhds hzx))
  · simpa only [DifferentiableWithinAt, HasFDerivWithinAt, hne.nhdsWithin_sdiff_singleton] using
      hd x ⟨hx, hne⟩

theorem differentiableOn_dslope {f : ℂ → E} {s : Set ℂ} {c : ℂ} (hc : s ∈ 𝓝 c) :
    DifferentiableOn ℂ (dslope f c) s ↔ DifferentiableOn ℂ f s :=
  ⟨fun h => h.of_dslope, fun h =>
    (differentiableOn_compl_singleton_and_continuousAt_iff hc).mp <|
      ⟨Iff.mpr (differentiableOn_dslope_of_notMem fun h => h.2 rfl) (h.mono sdiff_subset),
        continuousAt_dslope_same.2 <| h.differentiableAt hc⟩⟩

/-- **Removable singularity** theorem: if `s` is a neighborhood of `c : ℂ`, a function `f : ℂ → E`
is complex differentiable on `s \ {c}`, and $f(z) - f(c)=o((z-c)^{-1})$, then `f` redefined to be
equal to `limUnder (𝓝[≠] c) f` at `c` is complex differentiable on `s`. -/
theorem differentiableOn_update_limUnder_of_isLittleO {f : ℂ → E} {s : Set ℂ} {c : ℂ} (hc : s ∈ 𝓝 c)
    (hd : DifferentiableOn ℂ f (s \ {c}))
    (ho : (fun z : ({c}ᶜ : Set ℂ) ↦ f z.val - f c) =o[comap Subtype.val (𝓝[≠] c)]
      (fun z ↦ Checked.inv (z.val - c) (sub_ne_zero.mpr z.2).isUnit)) :
    DifferentiableOn ℂ (update f c (limUnder (𝓝[≠] c) f)) s := by
  set F : ℂ → E := fun z => (z - c) • f z
  suffices DifferentiableOn ℂ F (s \ {c}) ∧ ContinuousAt F c by
    rw [differentiableOn_compl_singleton_and_continuousAt_iff hc, ← differentiableOn_dslope hc,
      dslope_sub_smul] at this
    have hc : Tendsto f (𝓝[≠] c) (𝓝 (deriv F c)) :=
      continuousAt_update_same.mp (this.continuousOn.continuousAt hc)
    rwa [hc.limUnder_eq]
  refine ⟨(differentiableOn_id.sub_const _).smul hd, ?_⟩
  rw [← continuousWithinAt_compl_self]
  have H : Tendsto (fun z ↦ (z - c) • (f z - f c)) (𝓝[≠] c) (𝓝 0) := by
    refine (tendsto_comap'_iff (i := (Subtype.val : ({c}ᶜ : Set ℂ) → ℂ)) ?_).mp ?_
    · rw [Subtype.range_val]
      exact self_mem_nhdsWithin
    · simpa only [Function.comp_def, inv_inv₀] using
        ho.tendsto_inv_smul_nhds_zero
          (hg := fun z ↦ (sub_ne_zero.mpr z.2).isUnit.inv₀)
  have H' : Tendsto (fun z => (z - c) • f c) (𝓝[≠] c) (𝓝 (F c)) :=
    (continuousWithinAt_id.tendsto.sub tendsto_const_nhds).smul tendsto_const_nhds
  simpa [← smul_add, ContinuousWithinAt] using H.add H'

/-- **Removable singularity** theorem: if `s` is a punctured neighborhood of `c : ℂ`, a function
`f : ℂ → E` is complex differentiable on `s`, and $f(z) - f(c)=o((z-c)^{-1})$, then `f` redefined to
be equal to `limUnder (𝓝[≠] c) f` at `c` is complex differentiable on `{c} ∪ s`. -/
theorem differentiableOn_update_limUnder_insert_of_isLittleO {f : ℂ → E} {s : Set ℂ} {c : ℂ}
    (hc : s ∈ 𝓝[≠] c) (hd : DifferentiableOn ℂ f s)
    (ho : (fun z : ({c}ᶜ : Set ℂ) ↦ f z.val - f c) =o[comap Subtype.val (𝓝[≠] c)]
      (fun z ↦ Checked.inv (z.val - c) (sub_ne_zero.mpr z.2).isUnit)) :
    DifferentiableOn ℂ (update f c (limUnder (𝓝[≠] c) f)) (insert c s) :=
  differentiableOn_update_limUnder_of_isLittleO (insert_mem_nhds_iff.2 hc)
    (hd.mono fun _ hz => hz.1.resolve_left hz.2) ho

/-- **Removable singularity** theorem: if `s` is a neighborhood of `c : ℂ`, a function `f : ℂ → E`
is complex differentiable and is bounded on `s \ {c}`, then `f` redefined to be equal to
`limUnder (𝓝[≠] c) f` at `c` is complex differentiable on `s`. -/
theorem differentiableOn_update_limUnder_of_bddAbove {f : ℂ → E} {s : Set ℂ} {c : ℂ} (hc : s ∈ 𝓝 c)
    (hd : DifferentiableOn ℂ f (s \ {c})) (hb : BddAbove (norm ∘ f '' (s \ {c}))) :
    DifferentiableOn ℂ (update f c (limUnder (𝓝[≠] c) f)) s := by
  apply differentiableOn_update_limUnder_of_isLittleO hc hd
  apply IsBoundedUnder.isLittleO_sub_self_inv (x := Subtype.val) _ tendsto_comap
  obtain ⟨C, hC⟩ := hb
  have hbnd : ∀ᶠ z in 𝓝[≠] c, ‖f z - f c‖ ≤ C + ‖f c‖ :=
    mem_nhdsWithin_iff_exists_mem_nhds_inter.2
      ⟨s, hc, fun _ hz => norm_sub_le_of_le (hC <| mem_image_of_mem _ hz) le_rfl⟩
  have hsub : Tendsto (Subtype.val : ({c}ᶜ : Set ℂ) → ℂ)
      (comap Subtype.val (𝓝[≠] c)) (𝓝[≠] c) := tendsto_comap
  exact ⟨C + ‖f c‖, eventually_map.2 (hsub.eventually hbnd)⟩

/-- **Removable singularity** theorem: if a function `f : ℂ → E` is complex differentiable on a
punctured neighborhood of `c` and $f(z) - f(c)=o((z-c)^{-1})$, then `f` has a limit at `c`. -/
theorem tendsto_limUnder_of_differentiable_on_punctured_nhds_of_isLittleO {f : ℂ → E} {c : ℂ}
    (hd : ∀ᶠ z in 𝓝[≠] c, DifferentiableAt ℂ f z)
    (ho : (fun z : ({c}ᶜ : Set ℂ) ↦ f z.val - f c) =o[comap Subtype.val (𝓝[≠] c)]
      (fun z ↦ Checked.inv (z.val - c) (sub_ne_zero.mpr z.2).isUnit)) :
    Tendsto f (𝓝[≠] c) (𝓝 <| limUnder (𝓝[≠] c) f) := by
  rw [eventually_nhdsWithin_iff] at hd
  have : DifferentiableOn ℂ f ({z | z ≠ c → DifferentiableAt ℂ f z} \ {c}) := fun z hz =>
    (hz.1 hz.2).differentiableWithinAt
  have H := differentiableOn_update_limUnder_of_isLittleO hd this ho
  exact continuousAt_update_same.1 (H.differentiableAt hd).continuousAt

/-- **Removable singularity** theorem: if a function `f : ℂ → E` is complex differentiable and
bounded on a punctured neighborhood of `c`, then `f` has a limit at `c`. -/
theorem tendsto_limUnder_of_differentiable_on_punctured_nhds_of_bounded_under {f : ℂ → E} {c : ℂ}
    (hd : ∀ᶠ z in 𝓝[≠] c, DifferentiableAt ℂ f z)
    (hb : IsBoundedUnder (· ≤ ·) (𝓝[≠] c) fun z => ‖f z - f c‖) :
    Tendsto f (𝓝[≠] c) (𝓝 <| limUnder (𝓝[≠] c) f) := by
  apply tendsto_limUnder_of_differentiable_on_punctured_nhds_of_isLittleO hd
  apply IsBoundedUnder.isLittleO_sub_self_inv (x := Subtype.val) _ tendsto_comap
  obtain ⟨C, hC⟩ := hb
  exact ⟨C, eventually_map.2 (tendsto_comap.eventually (eventually_map.1 hC))⟩

/-- The Cauchy formula for the derivative of a holomorphic function. -/
theorem two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable {U : Set ℂ}
    (hU : IsOpen U) {c w₀ : ℂ} {R : ℝ} {f : ℂ → E} (hc : closedBall c R ⊆ U)
    (hf : DifferentiableOn ℂ f U) (hw₀ : w₀ ∈ ball c R) :
    (2 * π * I : ℂ)⁻¹ • circleIntegralOn (fun z : sphere c |R| ↦ Checked.inv ((z.val - w₀) ^ 2)
      ((isUnit_sub_of_mem_sphere_of_mem_ball hw₀ z).pow 2) • f z.val) c R = deriv f w₀ := by
  -- We apply the removable singularity theorem and the Cauchy formula to `dslope f w₀`
  have hf' : DifferentiableOn ℂ (dslope f w₀) U :=
    (differentiableOn_dslope (hU.mem_nhds ((ball_subset_closedBall.trans hc) hw₀))).mpr hf
  have h0 := (hf'.diffContOnCl_ball hc).two_pi_i_inv_smul_circleIntegral_sub_inv_smul hw₀
  rw [← dslope_same, ← h0]
  congr 1
  simp only [circleIntegralOn_sphere]
  let u (θ : ℝ) : IsUnit (circleMap c R θ - w₀) :=
    isUnit_sub_of_mem_sphere_of_mem_ball hw₀ ⟨circleMap c R θ, circleMap_mem_sphere' c R θ⟩
  let k (θ : ℝ) : ℂ := Checked.inv ((circleMap c R θ - w₀) ^ 2) ((u θ).pow 2)
  have hD : Continuous (deriv (circleMap c R)) := by
    rw [funext (deriv_circleMap c R)]
    fun_prop
  have hk : Continuous k :=
    (((continuous_circleMap c R).sub continuous_const).pow 2).fun_inv₀
  have hcf : ContinuousOn (fun θ : ℝ ↦ f (circleMap c R θ)) [[0, 2 * π]] :=
    hf.continuousOn.comp (continuous_circleMap c R).continuousOn fun θ _ ↦
      hc (sphere_subset_closedBall (circleMap_mem_sphere c (pos_of_mem_ball hw₀).le θ))
  have hInt : IntervalIntegrable
      (fun θ : ℝ ↦ deriv (circleMap c R) θ • k θ • f (circleMap c R θ)) volume 0 (2 * π) :=
    (hD.continuousOn.smul (hk.continuousOn.smul hcf)).intervalIntegrable
  have hInt' : IntervalIntegrable
      (fun θ : ℝ ↦ deriv (circleMap c R) θ • k θ • f w₀) volume 0 (2 * π) :=
    (hD.smul (hk.smul continuous_const)).intervalIntegrable _ _
  have hne (θ : ℝ) : circleMap c R θ ≠ w₀ := sub_ne_zero.mp (u θ).ne_zero
  have hzero : (∫ θ in 0..2 * π, deriv (circleMap c R) θ • k θ) = 0 := by
    have hz := circleIntegral.integral_sub_zpow_of_ne (by decide : (-2 : ℤ) ≠ -1) c w₀ R
    have hmap (θ : ℝ) : circleMap c R θ ∈ {z : ℂ | (-2 : ℤ) < 0 → z ≠ w₀} :=
      fun _ ↦ hne θ
    rw [circleIntegralOn_eq_intervalIntegral _ hmap] at hz
    have hk_eq (θ : ℝ) :
        Checked.zpow (circleMap c R θ - w₀) (-2) (fun _ ↦ u θ) = k θ := by
      simpa only [k, zpow_ofNat₀] using zpow_neg₀ (u θ).ne_zero (2 : ℤ)
    simpa only [hk_eq] using hz
  have heq (θ : ℝ) :
      Checked.inv (circleMap c R θ - w₀) (u θ) • dslope f w₀ (circleMap c R θ) =
        k θ • f (circleMap c R θ) - k θ • f w₀ := by
    rw [dslope_of_ne f (hne θ)]
    simp only [slope, vsub_eq_sub, k, sq, mul_inv_rev₀, smul_smul, smul_sub]
  change (∫ θ in 0..2 * π, deriv (circleMap c R) θ • k θ • f (circleMap c R θ)) = _
  simp only [heq, smul_sub, intervalIntegral.integral_sub hInt hInt']
  simp only [← smul_assoc, intervalIntegral.integral_smul_const, hzero, zero_smul, sub_zero]

end Complex
