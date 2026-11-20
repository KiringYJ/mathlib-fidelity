/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.LocallyConvex.SeparatingDual

/-!
# Derivatives of integrals depending on parameters

A parametric integral is a function with shape `f = fun x : H ↦ ∫ a : α, F x a ∂μ` for some
`F : H → α → E`, where `H` and `E` are normed spaces and `α` is a measured space with measure `μ`.

We already know from `continuous_of_dominated`
in `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean` how
to guarantee that `f` is continuous using the dominated convergence theorem. In this file,
we want to express the derivative of `f` as the integral of the derivative of `F` with respect
to `x`.


## Main results

As explained above, all results express the derivative of a parametric integral as the integral of
a derivative. The variations come from the assumptions and from the different ways of expressing
derivative, especially Fréchet derivatives vs elementary derivative of function of one real
variable.

* `hasFDerivAt_integral_of_dominated_loc_of_lip`: this version assumes that
  - `F x` is ae-measurable for x near `x₀`,
  - `F x₀` is integrable,
  - `fun x ↦ F x a` has derivative `F' a : H →L[ℝ] E` at `x₀` which is ae-measurable,
  - `fun x ↦ F x a` is locally Lipschitz near `x₀` for almost every `a`,
    with a Lipschitz bound which is integrable with respect to `a`.

  A subtle point is that the "near x₀" in the last condition has to be uniform in `a`. This is
  controlled by a positive number `ε`.

* `hasFDerivAt_integral_of_dominated_of_fderiv_le`: this version assumes `fun x ↦ F x a` has
  derivative `F' x a` for `x` near `x₀` and `F' x` is bounded by an integrable function independent
  from `x` near `x₀`.

`hasDerivAt_integral_of_dominated_loc_of_lip` and
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` are versions of the above two results that
assume `H = ℝ` or `H = ℂ` and use the high-school derivative `deriv` instead of Fréchet derivative
`fderiv`.

We also provide versions of these theorems for set integrals.

## Tags
integral, derivative
-/

public section


noncomputable section

open TopologicalSpace MeasureTheory Filter Metric

open scoped Topology Filter

variable {α : Type*} [SigmaAlgebra α] {μ : Measure α} {𝕜 : Type*} [RCLike 𝕜] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E] {H : Type*}
  [NormedAddCommGroup H] [NormedSpace 𝕜 H]

variable {F : H → α → E} {x₀ : H} {bound : α → ℝ} {s : Set H}

/-- Differentiation under integral of `x ↦ ∫ F x a` at a given point `x₀`, assuming `F x₀` is
integrable, `‖F x a - F x₀ a‖ ≤ bound a * ‖x - x₀‖` for `x` in a neighborhood of `x₀` for ae `a`
integrable Lipschitz bound `bound` (with a neighborhood independent of `a`), and `F x` is
ae-measurable for `x` in the same ball. See `hasFDerivAt_integral_of_dominated_loc_of_lip` for a
slightly less general but usually more useful version. -/
theorem hasFDerivAt_integral_of_dominated_loc_of_lip' {F' : α → H →L[𝕜] E} (hs : s ∈ 𝓝 x₀)
    (hF_meas : ∀ x ∈ s, AEStronglyMeasurable (F x) μ) (hF_int : Integrable (F x₀) μ)
    (hF'_meas : AEStronglyMeasurable F' μ)
    (h_lipsch : ∀ᵐ a ∂μ, ∀ x ∈ s, ‖F x a - F x₀ a‖ ≤ bound a * ‖x - x₀‖)
    (bound_integrable : Integrable (bound : α → ℝ) μ)
    (h_diff : ∀ᵐ a ∂μ, HasFDerivAt (F · a) (F' a) x₀) :
    Integrable F' μ ∧ HasFDerivAt (fun x ↦ ∫ a, F x a ∂μ) (∫ a, F' a ∂μ) x₀ := by
  obtain ⟨ε, ε_pos, hε⟩ := Metric.mem_nhds_iff.1 hs
  have x₀_in : x₀ ∈ ball x₀ ε := mem_ball_self ε_pos
  set b : α → ℝ := fun a ↦ |bound a|
  have b_int : Integrable b μ := bound_integrable.norm
  have b_nonneg : ∀ a, 0 ≤ b a := fun a ↦ abs_nonneg _
  replace h_lipsch : ∀ᵐ a ∂μ, ∀ x ∈ ball x₀ ε, ‖F x a - F x₀ a‖ ≤ b a * ‖x - x₀‖ :=
    h_lipsch.mono fun a ha x hx ↦
      (ha x (hε hx)).trans <| mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
  have hF_int' : ∀ x ∈ ball x₀ ε, Integrable (F x) μ := fun x x_in ↦ by
    have : ∀ᵐ a ∂μ, ‖F x₀ a - F x a‖ ≤ ε * b a := by
      simp only [norm_sub_rev (F x₀ _)]
      refine h_lipsch.mono fun a ha ↦ (ha x x_in).trans ?_
      rw [mul_comm ε]
      rw [mem_ball, dist_eq_norm] at x_in
      gcongr
    exact integrable_of_norm_sub_le (hF_meas x (hε x_in)) hF_int
      (bound_integrable.norm.const_mul ε) this
  have hF'_int : Integrable F' μ :=
    have : ∀ᵐ a ∂μ, ‖F' a‖ ≤ b a := by
      apply (h_diff.and h_lipsch).mono
      rintro a ⟨ha_diff, ha_lip⟩
      exact ha_diff.le_of_lip' (b_nonneg a) (mem_of_superset (ball_mem_nhds _ ε_pos) <| ha_lip)
    b_int.mono' hF'_meas this
  refine ⟨hF'_int, ?_⟩
  /- Discard the trivial case where `E` is not complete, as all integrals vanish. -/
  by_cases hE : CompleteSpace E; swap
  · rcases subsingleton_or_nontrivial H with hH | hH
    · have : Subsingleton (H →L[𝕜] E) := inferInstance
      convert! hasFDerivAt_of_subsingleton _ x₀
    · have : ¬(CompleteSpace (H →L[𝕜] E)) := by
        simpa [SeparatingDual.completeSpace_continuousLinearMap_iff] using hE
      simp only [integral, hE, ↓reduceDIte, this]
      exact hasFDerivAt_const 0 x₀
  let D := {x : H // x - x₀ ≠ 0}
  let L : Filter D := comap Subtype.val (𝓝 x₀)
  let d (x : D) := ‖x.val - x₀‖
  have hdu (x : D) : IsUnit (d x) := (norm_ne_zero_iff.mpr x.2).isUnit
  have hnonneg (x : D) : 0 ≤ Checked.inv (d x) (hdu x) := inv_nonneg.mpr (norm_nonneg _)
  let G (x : D) (a : α) :=
    Checked.inv (d x) (hdu x) • (F x.val a - F x₀ a - F' a (x.val - x₀))
  have hball : ∀ᶠ x : D in L, x.val ∈ ball x₀ ε :=
    tendsto_comap.eventually (ball_mem_nhds x₀ ε_pos)
  have hnorm : ∀ᶠ x : D in L,
      Checked.div
        ‖((∫ a, F x.val a ∂μ) - ∫ a, F x₀ a ∂μ) - (∫ a, F' a ∂μ) (x.val - x₀)‖
        (d x) (hdu x) = ‖∫ a, G x a ∂μ‖ := by
    filter_upwards [hball] with x hx
    simp only [G]
    rw [div_eq_inv_mul₀, ← norm_smul_of_nonneg (hnonneg x), integral_smul, integral_sub,
      integral_sub, ← ContinuousLinearMap.integral_apply hF'_int]
    exacts [hF_int' x.val hx, hF_int, (hF_int' x.val hx).sub hF_int,
      hF'_int.apply_continuousLinearMap _]
  refine (hasFDerivAt_iff_tendsto (coord := id)
    (Eventually.of_forall fun y hy ↦ congrArg (fun z ↦ ∫ a, F z a ∂μ) hy)).mpr ?_
  suffices Tendsto (fun x : D ↦ ∫ a, G x a ∂μ) L (𝓝 0) from
    (tendsto_congr' hnorm).mpr (tendsto_zero_iff_norm_tendsto_zero.mp this)
  rw [← show (∫ _ : α, (0 : E) ∂μ) = 0 by simp]
  refine tendsto_integral_filter_of_dominated_convergence (fun a ↦ b a + ‖F' a‖) ?_ ?_
    (b_int.add hF'_int.norm) ?_
  · filter_upwards [hball] with x hx
    exact (((hF_meas x.val (hε hx)).sub (hF_meas _ (hε x₀_in))).sub
      (hF'_meas.apply_continuousLinearMap _)).const_smul _
  · filter_upwards [hball] with x hx
    refine h_lipsch.mono fun a ha ↦ ?_
    simp only [G]
    rw [norm_smul_of_nonneg (hnonneg x), ← div_eq_inv_mul₀,
      div_le_iff₀ (norm_pos_iff.mpr x.2), add_mul]
    exact (norm_sub_le _ _).trans <| add_le_add (ha x.val hx) ((F' a).le_opNorm _)
  · refine h_diff.mono fun a ha ↦ ?_
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hG (x : D) : ‖G x a‖ =
        Checked.div ‖F x.val a - F x₀ a - F' a (x.val - x₀)‖ (d x) (hdu x) := by
      simp only [G, norm_smul_of_nonneg (hnonneg x), div_eq_inv_mul₀]
    simpa only [hG, id_eq] using (hasFDerivAt_iff_tendsto (coord := id)
      (Eventually.of_forall fun y hy ↦ congrArg (F · a) hy)).mp ha

/-- Differentiation under integral of `x ↦ ∫ F x a` at a given point `x₀`, assuming
`F x₀` is integrable, `x ↦ F x a` is locally Lipschitz in a neighborhood of `x₀` for ae `a`
(with a neighborhood independent of `a`) with integrable Lipschitz bound, and `F x` is ae-measurable
for `x` in a possibly smaller neighborhood of `x₀`. -/
theorem hasFDerivAt_integral_of_dominated_loc_of_lip {F' : α → H →L[𝕜] E}
    (hs : s ∈ 𝓝 x₀) (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) μ)
    (hF_int : Integrable (F x₀) μ) (hF'_meas : AEStronglyMeasurable F' μ)
    (h_lip : ∀ᵐ a ∂μ, LipschitzOnWith (Real.nnabs <| bound a) (F · a) s)
    (bound_integrable : Integrable (bound : α → ℝ) μ)
    (h_diff : ∀ᵐ a ∂μ, HasFDerivAt (F · a) (F' a) x₀) :
    Integrable F' μ ∧ HasFDerivAt (fun x ↦ ∫ a, F x a ∂μ) (∫ a, F' a ∂μ) x₀ := by
  obtain ⟨δ, δ_pos, hδ⟩ : ∃ δ > 0, ∀ x ∈ ball x₀ δ, AEStronglyMeasurable (F x) μ ∧ x ∈ s :=
    eventually_nhds_iff_ball.mp (hF_meas.and hs)
  choose hδ_meas hδε using hδ
  replace h_lip : ∀ᵐ a : α ∂μ, ∀ x ∈ ball x₀ δ, ‖F x a - F x₀ a‖ ≤ |bound a| * ‖x - x₀‖ :=
    h_lip.mono fun a lip x hx ↦ lip.norm_sub_le (hδε x hx) (mem_of_mem_nhds hs)
  replace bound_integrable := bound_integrable.norm
  apply hasFDerivAt_integral_of_dominated_loc_of_lip' (ball_mem_nhds x₀ δ_pos) <;> assumption

open scoped Interval in
/-- Differentiation under integral of `x ↦ ∫ x in a..b, F x t` at a given point `x₀ ∈ (a,b)`,
assuming `F x₀` is integrable on `(a,b)`, that `x ↦ F x t` is Lipschitz on a neighborhood of `x₀`
for almost every `t` (with a neighborhood independent of `t`) with integrable Lipschitz bound,
and `F x` is a.e.-measurable for `x` in a possibly smaller neighborhood of `x₀`. -/
theorem hasFDerivAt_integral_of_dominated_loc_of_lip_interval [NormedSpace ℝ H] {μ : Measure ℝ}
    {F : H → ℝ → E} {F' : ℝ → H →L[ℝ] E} {a b : ℝ} {bound : ℝ → ℝ} (hs : s ∈ 𝓝 x₀)
    (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) <| μ.restrict (Ι a b))
    (hF_int : IntervalIntegrable (F x₀) μ a b)
    (hF'_meas : AEStronglyMeasurable F' <| μ.restrict (Ι a b))
    (h_lip : ∀ᵐ t ∂μ.restrict (Ι a b),
      LipschitzOnWith (Real.nnabs <| bound t) (F · t) s)
    (bound_integrable : IntervalIntegrable bound μ a b)
    (h_diff : ∀ᵐ t ∂μ.restrict (Ι a b), HasFDerivAt (F · t) (F' t) x₀) :
    IntervalIntegrable F' μ a b ∧
      HasFDerivAt (fun x ↦ ∫ t in a..b, F x t ∂μ) (∫ t in a..b, F' t ∂μ) x₀ := by
  simp_rw [AEStronglyMeasurable.aestronglyMeasurable_uIoc_iff, eventually_and] at hF_meas hF'_meas
  rw [ae_restrict_uIoc_iff] at h_lip h_diff
  have H₁ :=
    hasFDerivAt_integral_of_dominated_loc_of_lip hs hF_meas.1 hF_int.1 hF'_meas.1 h_lip.1
      bound_integrable.1 h_diff.1
  have H₂ :=
    hasFDerivAt_integral_of_dominated_loc_of_lip hs hF_meas.2 hF_int.2 hF'_meas.2 h_lip.2
      bound_integrable.2 h_diff.2
  exact ⟨⟨H₁.1, H₂.1⟩, H₁.2.sub H₂.2⟩

/-- Differentiation under integral of `x ↦ ∫ F x a` at a given point `x₀`, assuming
`F x₀` is integrable, `x ↦ F x a` is differentiable on a neighborhood of `x₀` for ae `a` with
derivative norm uniformly bounded by an integrable function (the neighborhood is independent
of `a`), and `F x` is ae-measurable for `x` in a possibly smaller neighborhood of `x₀`. -/
theorem hasFDerivAt_integral_of_dominated_of_fderiv_le {F' : H → α → H →L[𝕜] E} (hs : s ∈ 𝓝 x₀)
    (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) μ) (hF_int : Integrable (F x₀) μ)
    (hF'_meas : AEStronglyMeasurable (F' x₀) μ)
    (h_bound : ∀ᵐ a ∂μ, ∀ x ∈ s, ‖F' x a‖ ≤ bound a)
    (bound_integrable : Integrable (bound : α → ℝ) μ)
    (h_diff : ∀ᵐ a ∂μ, ∀ x ∈ s, HasFDerivAt (F · a) (F' x a) x) :
    HasFDerivAt (fun x ↦ ∫ a, F x a ∂μ) (∫ a, F' x₀ a ∂μ) x₀ := by
  let : NormedSpace ℝ H := NormedSpace.restrictScalars ℝ 𝕜 H
  rcases Metric.mem_nhds_iff.1 hs with ⟨ε, ε_pos, hε⟩
  have x₀_in : x₀ ∈ ball x₀ ε := mem_ball_self ε_pos
  have diff_x₀ : ∀ᵐ a ∂μ, HasFDerivAt (F · a) (F' x₀ a) x₀ :=
    h_diff.mono fun a ha ↦ ha x₀ (hε x₀_in)
  have : ∀ᵐ a ∂μ, LipschitzOnWith (Real.nnabs (bound a)) (F · a) (ball x₀ ε) := by
    apply (h_diff.and h_bound).mono
    rintro a ⟨ha_deriv, ha_bound⟩
    refine (convex_ball _ _).lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
      (fun x x_in ↦ (ha_deriv x (hε x_in)).hasFDerivWithinAt) fun x x_in ↦ ?_
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_nnabs]
    exact (ha_bound x (hε x_in)).trans (le_abs_self _)
  apply (hasFDerivAt_integral_of_dominated_loc_of_lip (ball_mem_nhds x₀ ε_pos)
    hF_meas hF_int hF'_meas this bound_integrable diff_x₀).2

open scoped Interval in
/-- Differentiation under integral of `x ↦ ∫ x in a..b, F x a` at a given point `x₀`, assuming
`F x₀` is integrable on `(a,b)`, `x ↦ F x a` is differentiable on a neighborhood of `x₀` for ae `a`
with derivative norm uniformly bounded by an integrable function (the neighborhood is independent
of `a`), and `F x` is ae-measurable for `x` in a possibly smaller neighborhood of `x₀`. -/
theorem hasFDerivAt_integral_of_dominated_of_fderiv_le'' [NormedSpace ℝ H] {μ : Measure ℝ}
    {F : H → ℝ → E} {F' : H → ℝ → H →L[ℝ] E} {a b : ℝ} {bound : ℝ → ℝ} (hs : s ∈ 𝓝 x₀)
    (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) <| μ.restrict (Ι a b))
    (hF_int : IntervalIntegrable (F x₀) μ a b)
    (hF'_meas : AEStronglyMeasurable (F' x₀) <| μ.restrict (Ι a b))
    (h_bound : ∀ᵐ t ∂μ.restrict (Ι a b), ∀ x ∈ s, ‖F' x t‖ ≤ bound t)
    (bound_integrable : IntervalIntegrable bound μ a b)
    (h_diff : ∀ᵐ t ∂μ.restrict (Ι a b), ∀ x ∈ s, HasFDerivAt (F · t) (F' x t) x) :
    HasFDerivAt (fun x ↦ ∫ t in a..b, F x t ∂μ) (∫ t in a..b, F' x₀ t ∂μ) x₀ := by
  rw [ae_restrict_uIoc_iff] at h_diff h_bound
  simp_rw [AEStronglyMeasurable.aestronglyMeasurable_uIoc_iff, eventually_and] at hF_meas hF'_meas
  exact
    (hasFDerivAt_integral_of_dominated_of_fderiv_le hs hF_meas.1 hF_int.1 hF'_meas.1 h_bound.1
          bound_integrable.1 h_diff.1).sub
      (hasFDerivAt_integral_of_dominated_of_fderiv_le hs hF_meas.2 hF_int.2 hF'_meas.2 h_bound.2
        bound_integrable.2 h_diff.2)

section

variable {F : 𝕜 → α → E} {x₀ : 𝕜} {s : Set 𝕜}

/-- Derivative under integral of `x ↦ ∫ F x a` at a given point `x₀ : 𝕜`, `𝕜 = ℝ` or `𝕜 = ℂ`,
assuming `F x₀` is integrable, `x ↦ F x a` is locally Lipschitz on a neighborhood of `x₀` for ae `a`
(with a neighborhood independent of `a`) with integrable Lipschitz bound, and `F x` is
ae-measurable for `x` in a possibly smaller neighborhood of `x₀`. -/
theorem hasDerivAt_integral_of_dominated_loc_of_lip {F' : α → E} (hs : s ∈ 𝓝 x₀)
    (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) μ) (hF_int : Integrable (F x₀) μ)
    (hF'_meas : AEStronglyMeasurable F' μ)
    (h_lipsch : ∀ᵐ a ∂μ, LipschitzOnWith (Real.nnabs <| bound a) (F · a) s)
    (bound_integrable : Integrable (bound : α → ℝ) μ)
    (h_diff : ∀ᵐ a ∂μ, HasDerivAt (F · a) (F' a) x₀) :
    Integrable F' μ ∧ HasDerivAt (fun x ↦ ∫ a, F x a ∂μ) (∫ a, F' a ∂μ) x₀ := by
  set L : E →L[𝕜] 𝕜 →L[𝕜] E := ContinuousLinearMap.smulRightL 𝕜 𝕜 E 1
  replace h_diff : ∀ᵐ a ∂μ, HasFDerivAt (F · a) (L (F' a)) x₀ :=
    h_diff.mono fun x hx ↦ hx.hasFDerivAt
  have hm : AEStronglyMeasurable (L ∘ F') μ := L.continuous.comp_aestronglyMeasurable hF'_meas
  obtain ⟨hF'_int, key⟩ := hasFDerivAt_integral_of_dominated_loc_of_lip
    hs hF_meas hF_int hm h_lipsch bound_integrable h_diff
  replace hF'_int : Integrable F' μ := by
    rw [← integrable_norm_iff hm] at hF'_int
    simpa [L, (· ∘ ·), integrable_norm_iff hF'_meas] using! hF'_int
  refine ⟨hF'_int, ?_⟩
  by_cases hE : CompleteSpace E; swap
  · simpa [integral, hE] using! hasDerivAt_const x₀ 0
  simp_rw [hasDerivAt_iff_hasFDerivAt] at h_diff ⊢
  simpa only [(· ∘ ·), ContinuousLinearMap.integral_comp_comm _ hF'_int] using! key

private theorem hasDerivAt_integral_of_dominated_loc_of_deriv_le_aux (hs : s ∈ 𝓝 x₀)
    (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) μ) (hF_int : Integrable (F x₀) μ)
    {F' : 𝕜 → α → E} (hF'_meas : AEStronglyMeasurable (F' x₀) μ)
    (h_bound : ∀ᵐ a ∂μ, ∀ x ∈ s, ‖F' x a‖ ≤ bound a) (bound_integrable : Integrable bound μ)
    (h_diff : ∀ᵐ a ∂μ, ∀ x ∈ s, HasDerivAt (F · a) (F' x a) x) :
    Integrable (F' x₀) μ ∧ HasDerivAt (fun n ↦ ∫ a, F n a ∂μ) (∫ a, F' x₀ a ∂μ) x₀ := by
  rcases Metric.mem_nhds_iff.1 hs with ⟨ε, ε_pos, hε⟩
  have x₀_in : x₀ ∈ ball x₀ ε := mem_ball_self ε_pos
  have diff_x₀ : ∀ᵐ a ∂μ, HasDerivAt (F · a) (F' x₀ a) x₀ :=
    h_diff.mono fun a ha ↦ ha x₀ (hε x₀_in)
  have : ∀ᵐ a ∂μ, LipschitzOnWith (Real.nnabs (bound a)) (fun x : 𝕜 ↦ F x a) (ball x₀ ε) := by
    apply (h_diff.and h_bound).mono
    rintro a ⟨ha_deriv, ha_bound⟩
    refine (convex_ball _ _).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun x x_in ↦ (ha_deriv x (hε x_in)).hasDerivWithinAt) fun x x_in ↦ ?_
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_nnabs]
    exact (ha_bound x (hε x_in)).trans (le_abs_self _)
  exact hasDerivAt_integral_of_dominated_loc_of_lip (ball_mem_nhds x₀ ε_pos) hF_meas hF_int
    hF'_meas this bound_integrable diff_x₀

end

/-- Differentiate a parametric integral on an open coordinate domain when its pointwise
derivative is bounded on a common neighborhood by an integrable function. -/
theorem hasDerivAt_integral_of_dominated_loc_of_deriv_le {D : Type*} [TopologicalSpace D]
    {coord : D → 𝕜} {F F' : D → α → E} {x₀ : D} {s : Set D} (hs : s ∈ 𝓝 x₀)
    (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) μ) (hF_int : Integrable (F x₀) μ)
    (hF'_meas : AEStronglyMeasurable (F' x₀) μ)
    (h_bound : ∀ᵐ a ∂μ, ∀ x ∈ s, ‖F' x a‖ ≤ bound a) (bound_integrable : Integrable bound μ)
    (h_diff : ∀ᵐ a ∂μ, ∀ x ∈ s, HasDerivAt (F · a) (F' x a) x coord)
    (hcoord : Topology.IsOpenEmbedding coord := by exact Topology.IsOpenEmbedding.id) :
    Integrable (F' x₀) μ ∧
      HasDerivAt (fun x ↦ ∫ a, F x a ∂μ) (∫ a, F' x₀ a ∂μ) x₀ coord := by
  let G := Function.extend coord F 0
  let G' := Function.extend coord F' 0
  have hG (x : D) : G (coord x) = F x := hcoord.injective.extend_apply _ _ _
  have hG' (x : D) : G' (coord x) = F' x := hcoord.injective.extend_apply _ _ _
  have hmap (x : D) := hcoord.map_nhds_eq x
  have hs' : coord '' s ∈ 𝓝 (coord x₀) :=
    hmap x₀ ▸ image_mem_map hs
  have h_meas : ∀ᶠ y in 𝓝 (coord x₀), AEStronglyMeasurable (G y) μ := by
    rw [← hmap x₀, eventually_map]
    simpa only [hG] using hF_meas
  have h_bound' : ∀ᵐ a ∂μ, ∀ y ∈ coord '' s, ‖G' y a‖ ≤ bound a := by
    filter_upwards [h_bound] with a ha y hy
    obtain ⟨x, hx, rfl⟩ := hy
    simpa only [hG'] using ha x hx
  have h_diff' : ∀ᵐ a ∂μ, ∀ y ∈ coord '' s, HasDerivAt (G · a) (G' y a) y := by
    filter_upwards [h_diff] with a ha y hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [hasDerivAt_iff_hasFDerivAt, hasFDerivAt_iff_isLittleOTVS, ← hmap x,
      Asymptotics.isLittleOTVS_map]
    simpa only [Function.comp_def, id_eq, hG, hG'] using (ha x hx).hasFDerivAt.isLittleOTVS
  obtain ⟨hi, hd⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le_aux hs' h_meas
    (by simpa only [hG] using hF_int) (by simpa only [hG'] using hF'_meas)
    h_bound' bound_integrable h_diff'
  refine ⟨by simpa only [hG'] using hi, ?_⟩
  apply hasDerivAt_iff_hasFDerivAt.mpr
  simpa only [HasFDerivAt, Function.comp_def, id_eq, hG, hG'] using
    hd.hasFDerivAt.comp_tendsto coord
      ((hcoord.continuous.continuousAt : ContinuousAt coord x₀).tendsto.prodMap
        (Filter.tendsto_pure_pure ..))
