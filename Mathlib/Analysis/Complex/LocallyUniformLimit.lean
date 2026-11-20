/-
Copyright (c) 2022 Vincent Beffara. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Beffara
-/
module

public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Locally uniform limits of holomorphic functions

This file gathers some results about locally uniform limits of holomorphic functions on an open
subset of the complex plane.

## Main results

* `TendstoLocallyUniformlyOn.differentiableOn`: A locally uniform limit of holomorphic functions
  is holomorphic.
* `TendstoLocallyUniformlyOn.deriv`: Locally uniform convergence implies locally uniform
  convergence of the derivatives to the derivative of the limit.
-/

@[expose] public section


open Set Metric Filter Complex MeasureTheory

open scoped Real Topology Interval

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {U K : Set ℂ}
  {z : ℂ} {M r δ : ℝ} {φ : Filter ι} {F : ι → ℂ → E} {f g : ℂ → E}

namespace Complex

section Cderiv

/-- A circle integral which coincides with `deriv f z` whenever one can apply the Cauchy formula for
the derivative. It is useful in the proof that locally uniform limits of holomorphic functions are
holomorphic, because it depends continuously on `f` for the uniform topology. -/
noncomputable def cderiv (r : ℝ) (f : ℂ → E) (z : ℂ) {hr : IsUnit r} : E :=
  (2 * π * I : ℂ)⁻¹ • circleIntegralOn (fun w : sphere z |r| ↦ Checked.inv ((w.val - z) ^ 2)
    ((isUnit_sub_center_of_mem_sphere hr w).pow 2) • f w.val) z r

theorem cderiv_eq_deriv [CompleteSpace E] (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hr : 0 < r)
    (hzr : closedBall z r ⊆ U) : cderiv r f z (hr := hr.ne'.isUnit) = deriv f z :=
  two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable hU hzr hf (mem_ball_self hr)

theorem norm_cderiv_le (hr : 0 < r) (hf : ∀ w ∈ sphere z r, ‖f w‖ ≤ M) :
    ‖cderiv r f z (hr := hr.ne'.isUnit)‖ ≤ M / r := by
  have hM : 0 ≤ M := by
    obtain ⟨w, hw⟩ : (sphere z r).Nonempty := NormedSpace.sphere_nonempty.mpr hr.le
    exact (norm_nonneg _).trans (hf w hw)
  let u (θ : ℝ) : IsUnit (circleMap z r θ - z) :=
    isUnit_sub_center_of_mem_sphere hr.ne'.isUnit ⟨circleMap z r θ, circleMap_mem_sphere' z r θ⟩
  let k (θ : ℝ) := Checked.inv ((circleMap z r θ - z) ^ 2) ((u θ).pow 2)
  have h1 (θ : ℝ) : ‖deriv (circleMap z r) θ • k θ • f (circleMap z r θ)‖ ≤
      r * (M / r ^ 2) := by
    have hw := circleMap_mem_sphere z hr.le θ
    have hnorm : ‖circleMap z r θ - z‖ = r := mem_sphere_iff_norm.mp hw
    simp only [norm_smul, deriv_circleMap, norm_mul, norm_circleMap_zero, abs_of_pos hr, norm_I,
      mul_one, k, norm_inv, norm_pow, hnorm, inv_mul_eq_div₀]
    exact mul_le_mul_of_nonneg_left (div_le_div₀ hM (hf _ hw) (sq_pos_of_pos hr) le_rfl) hr.le
  have h2 := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 2 * π)
    (fun θ _ ↦ h1 θ)
  simp only [cderiv, circleIntegralOn_sphere, norm_smul]
  refine (mul_le_mul le_rfl h2 (norm_nonneg _) (norm_nonneg _)).trans (le_of_eq ?_)
  simp [norm_inv, abs_of_pos Real.two_pi_pos, field]

theorem cderiv_sub (hr : 0 < r) (hf : ContinuousOn f (sphere z r))
    (hg : ContinuousOn g (sphere z r)) :
    cderiv r (f - g) z (hr := hr.ne'.isUnit) =
      cderiv r f z (hr := hr.ne'.isUnit) - cderiv r g z (hr := hr.ne'.isUnit) := by
  let u (θ : ℝ) : IsUnit (circleMap z r θ - z) :=
    isUnit_sub_center_of_mem_sphere hr.ne'.isUnit ⟨circleMap z r θ, circleMap_mem_sphere' z r θ⟩
  let k (θ : ℝ) := Checked.inv ((circleMap z r θ - z) ^ 2) ((u θ).pow 2)
  have hk : Continuous k :=
    (((continuous_circleMap z r).sub continuous_const).pow 2).fun_inv₀
  have hd : Continuous (deriv (circleMap z r)) := by
    rw [funext (deriv_circleMap z r)]
    fun_prop
  have hint (h : ℂ → E) (hh : ContinuousOn h (sphere z r)) :
      IntervalIntegrable (fun θ : ℝ ↦ deriv (circleMap z r) θ • k θ • h (circleMap z r θ))
        volume 0 (2 * π) :=
    (hd.continuousOn.smul (hk.continuousOn.smul (hh.comp (continuous_circleMap z r).continuousOn
      fun θ _ ↦ circleMap_mem_sphere z hr.le θ))).intervalIntegrable
  simp only [cderiv, circleIntegralOn_sphere, ← smul_sub]
  congr 1
  simpa only [k, Pi.sub_apply, smul_sub] using intervalIntegral.integral_sub (hint f hf) (hint g hg)

theorem norm_cderiv_lt (hr : 0 < r) (hfM : ∀ w ∈ sphere z r, ‖f w‖ < M)
    (hf : ContinuousOn f (sphere z r)) : ‖cderiv r f z (hr := hr.ne'.isUnit)‖ < M / r := by
  obtain ⟨L, hL1, hL2⟩ : ∃ L < M, ∀ w ∈ sphere z r, ‖f w‖ ≤ L := by
    have e1 : (sphere z r).Nonempty := NormedSpace.sphere_nonempty.mpr hr.le
    have e2 : ContinuousOn (fun w => ‖f w‖) (sphere z r) := continuous_norm.comp_continuousOn hf
    obtain ⟨x, hx, hx'⟩ := (isCompact_sphere z r).exists_isMaxOn e1 e2
    exact ⟨‖f x‖, hfM x hx, hx'⟩
  exact (norm_cderiv_le hr hL2).trans_lt ((div_lt_div_iff_of_pos_right hr).mpr hL1)

theorem norm_cderiv_sub_lt (hr : 0 < r) (hfg : ∀ w ∈ sphere z r, ‖f w - g w‖ < M)
    (hf : ContinuousOn f (sphere z r)) (hg : ContinuousOn g (sphere z r)) :
    ‖cderiv r f z (hr := hr.ne'.isUnit) - cderiv r g z (hr := hr.ne'.isUnit)‖ < M / r :=
  cderiv_sub hr hf hg ▸ norm_cderiv_lt hr hfg (hf.sub hg)

theorem _root_.TendstoUniformlyOn.cderiv (hF : TendstoUniformlyOn F f φ (cthickening δ K))
    (hδ : 0 < δ) (hFn : ∀ᶠ n in φ, ContinuousOn (F n) (cthickening δ K)) :
    TendstoUniformlyOn (fun i ↦ cderiv δ (F i) (hr := hδ.ne'.isUnit))
      (cderiv δ f (hr := hδ.ne'.isUnit)) φ K := by
  rcases φ.eq_or_neBot with rfl | hne
  · simp only [TendstoUniformlyOn, eventually_bot, imp_true_iff]
  have e1 : ContinuousOn f (cthickening δ K) := TendstoUniformlyOn.continuousOn hF hFn.frequently
  rw [tendstoUniformlyOn_iff] at hF ⊢
  rintro ε hε
  filter_upwards [hF (ε * δ) (mul_pos hε hδ), hFn] with n h h' z hz
  simp_rw [dist_eq_norm] at h ⊢
  have e2 : ∀ w ∈ sphere z δ, ‖f w - F n w‖ < ε * δ := fun w hw1 =>
    h w (closedBall_subset_cthickening hz δ (sphere_subset_closedBall hw1))
  have e3 := sphere_subset_closedBall.trans (closedBall_subset_cthickening hz δ)
  have hf : ContinuousOn f (sphere z δ) :=
    e1.mono (sphere_subset_closedBall.trans (closedBall_subset_cthickening hz δ))
  simpa only [mul_div_cancel_right₀] using norm_cderiv_sub_lt hδ e2 hf (h'.mono e3)

end Cderiv

variable [CompleteSpace E]

section Weierstrass

theorem tendstoUniformlyOn_deriv_of_cthickening_subset (hf : TendstoLocallyUniformlyOn F f φ U)
    (hF : ∀ᶠ n in φ, DifferentiableOn ℂ (F n) U) {δ : ℝ} (hδ : 0 < δ) (hK : IsCompact K)
    (hU : IsOpen U) (hKU : cthickening δ K ⊆ U) :
    TendstoUniformlyOn (deriv ∘ F) (cderiv δ f (hr := hδ.ne'.isUnit)) φ K := by
  have h1 : ∀ᶠ n in φ, ContinuousOn (F n) (cthickening δ K) := by
    filter_upwards [hF] with n h using h.continuousOn.mono hKU
  have h2 : IsCompact (cthickening δ K) := hK.cthickening
  have h3 : TendstoUniformlyOn F f φ (cthickening δ K) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp hf (cthickening δ K) hKU h2
  apply (h3.cderiv hδ h1).congr
  filter_upwards [hF] with n h z hz
  exact cderiv_eq_deriv hU h hδ ((closedBall_subset_cthickening hz δ).trans hKU)

theorem exists_cthickening_tendstoUniformlyOn (hf : TendstoLocallyUniformlyOn F f φ U)
    (hF : ∀ᶠ n in φ, DifferentiableOn ℂ (F n) U) (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ δ, ∃ hδ : 0 < δ, cthickening δ K ⊆ U ∧
      TendstoUniformlyOn (deriv ∘ F) (cderiv δ f (hr := hδ.ne'.isUnit)) φ K := by
  obtain ⟨δ, hδ, hKδ⟩ := hK.exists_cthickening_subset_open hU hKU
  exact ⟨δ, hδ, hKδ, tendstoUniformlyOn_deriv_of_cthickening_subset hf hF hδ hK hU hKδ⟩

/-- A locally uniform limit of holomorphic functions on an open domain of the complex plane is
holomorphic (the derivatives converge locally uniformly to that of the limit, which is proved
as `TendstoLocallyUniformlyOn.deriv`). -/
theorem _root_.TendstoLocallyUniformlyOn.differentiableOn [φ.NeBot]
    (hf : TendstoLocallyUniformlyOn F f φ U) (hF : ∀ᶠ n in φ, DifferentiableOn ℂ (F n) U)
    (hU : IsOpen U) : DifferentiableOn ℂ f U := by
  rintro x hx
  obtain ⟨K, ⟨hKx, hK⟩, hKU⟩ := (compact_basis_nhds x).mem_iff.mp (hU.mem_nhds hx)
  obtain ⟨δ, hδ, _, h1⟩ := exists_cthickening_tendstoUniformlyOn hf hF hK hU hKU
  have h2 : interior K ⊆ U := interior_subset.trans hKU
  have h3 : ∀ᶠ n in φ, DifferentiableOn ℂ (F n) (interior K) := by
    filter_upwards [hF] with n h using h.mono h2
  have h4 : TendstoLocallyUniformlyOn F f φ (interior K) := hf.mono h2
  have h5 : TendstoLocallyUniformlyOn (deriv ∘ F) (cderiv δ f (hr := hδ.ne'.isUnit))
      φ (interior K) :=
    h1.tendstoLocallyUniformlyOn.mono interior_subset
  have h6 : ∀ x ∈ interior K, HasDerivAt f (cderiv δ f x (hr := hδ.ne'.isUnit)) x := fun x h =>
    hasDerivAt_of_tendsto_locally_uniformly_on' isOpen_interior h5 h3 (fun _ => h4.tendsto_at) h
  have h7 : DifferentiableOn ℂ f (interior K) := fun x hx =>
    (h6 x hx).differentiableAt.differentiableWithinAt
  exact (h7.differentiableAt (interior_mem_nhds.mpr hKx)).differentiableWithinAt

theorem _root_.TendstoLocallyUniformlyOn.deriv (hf : TendstoLocallyUniformlyOn F f φ U)
    (hF : ∀ᶠ n in φ, DifferentiableOn ℂ (F n) U) (hU : IsOpen U) :
    TendstoLocallyUniformlyOn (deriv ∘ F) (deriv f) φ U := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU]
  rcases φ.eq_or_neBot with rfl | hne
  · simp only [TendstoUniformlyOn, eventually_bot, imp_true_iff]
  rintro K hKU hK
  obtain ⟨δ, hδ, hK4, h⟩ := exists_cthickening_tendstoUniformlyOn hf hF hK hU hKU
  refine h.congr_right fun z hz => cderiv_eq_deriv hU (hf.differentiableOn hF hU) hδ ?_
  exact (closedBall_subset_cthickening hz δ).trans hK4

end Weierstrass

section Tsums

/-- If the terms in the sum `∑' (i : ι), F i` are uniformly bounded on `U` by a
summable function, and each term in the sum is differentiable on `U`, then so is the sum. -/
theorem differentiableOn_tsum_of_summable_norm {u : ι → ℝ} (hu : Summable u)
    (hf : ∀ i : ι, DifferentiableOn ℂ (F i) U) (hU : IsOpen U)
    (hF_le : ∀ (i : ι) (w : ℂ), w ∈ U → ‖F i w‖ ≤ u i) :
    DifferentiableOn ℂ (fun w : ℂ => ∑' i : ι, F i w) U := by
  have hc := (tendstoUniformlyOn_tsum hu hF_le).tendstoLocallyUniformlyOn
  refine hc.differentiableOn (Eventually.of_forall fun s => ?_) hU
  exact DifferentiableOn.fun_sum fun i _ => hf i

/-- If the terms in the sum `∑' (i : ι), F i` are uniformly bounded on `U` by a
summable function, then the sum of `deriv F i` at a point in `U` is the derivative of the
sum. -/
theorem hasSum_deriv_of_summable_norm {u : ι → ℝ} (hu : Summable u)
    (hf : ∀ i : ι, DifferentiableOn ℂ (F i) U) (hU : IsOpen U)
    (hF_le : ∀ (i : ι) (w : ℂ), w ∈ U → ‖F i w‖ ≤ u i) (hz : z ∈ U) :
    HasSum (fun i : ι => deriv (F i) z) (deriv (fun w : ℂ => ∑' i : ι, F i w) z) := by
  rw [HasSum]
  have hc := (tendstoUniformlyOn_tsum hu hF_le).tendstoLocallyUniformlyOn
  convert!
    (hc.deriv (Eventually.of_forall fun s => DifferentiableOn.fun_sum fun i _ => hf i)
          hU).tendsto_at
      hz using 1
  ext1 s
  exact (deriv_fun_sum fun i _ => (hf i).differentiableAt (hU.mem_nhds hz)).symm

end Tsums

section LogDeriv

/-- The logarithmic derivatives of a locally uniformly convergent family tend to the
logarithmic derivative of its limit on the indices where they exist. -/
theorem logDeriv_tendsto {ι : Type*} {p : Filter ι} {f : ι → ℂ → ℂ} {g : ℂ → ℂ}
    {s : Set ℂ} (hs : IsOpen s) {x : ℂ} (hx : x ∈ s) (hF : TendstoLocallyUniformlyOn f g p s)
    (hf : ∀ᶠ n in p, DifferentiableOn ℂ (f n) s)
    {hgd : ∃! d, HasDerivAt g d x} {hg : IsUnit (g x)} :
    Tendsto (fun n : {n : ι // DifferentiableAt ℂ (f n) x ∧ IsUnit (f n x)} ↦
      logDeriv (f n) x id n.2.1.existsUnique_hasDerivAt n.2.2)
      (comap Subtype.val p) (𝓝 (logDeriv g x id hgd hg)) := by
  let D := {n : ι // DifferentiableAt ℂ (f n) x ∧ IsUnit (f n x)}
  have hval : Tendsto (Subtype.val : D → ι) (comap Subtype.val p) p := tendsto_comap
  have hd := ((hF.deriv hf hs).tendsto_at hx).comp hval
  have h := hd.div₀ ((hF.tendsto_at hx).comp hval) (h₀ := fun n ↦ n.2.2) (hb := hg)
  simpa only [logDeriv_apply, Function.comp_def] using h

end LogDeriv

end Complex
