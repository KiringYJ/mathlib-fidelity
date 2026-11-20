/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Non-integrable functions

In this file we prove that the derivative of a function that tends to infinity is not interval
integrable, see `not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_filter` and
`not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_punctured`. Then we apply the
latter lemma to prove that the function `fun x => x⁻¹` is integrable on `a..b` if and only if
`a = b` or `0 ∉ [a, b]`.

## Main results

* `not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_punctured`: if `f` tends to infinity
  along `𝓝[≠] c` and `f' = O(g)` along the same filter, then `g` is not interval integrable on any
  nontrivial integral `a..b`, `c ∈ [a, b]`.

* `not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_filter`: a version of
  `not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_punctured` that works for one-sided
  neighborhoods;

* `not_intervalIntegrable_of_sub_inv_isBigO_punctured`: if `1 / (x - c) = O(f)` as `x → c`, `x ≠ c`,
  then `f` is not interval integrable on any nontrivial interval `a..b`, `c ∈ [a, b]`;

* `intervalIntegrable_sub_inv_iff` and `intervalIntegrable_inv_iff`: integrability conditions
  for reciprocals on the punctured interval, with measure pulled back along its inclusion.

## Tags

integrable function
-/

public section


open scoped MeasureTheory Topology Interval NNReal ENNReal

open MeasureTheory TopologicalSpace Set Filter Asymptotics intervalIntegral

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]

/-- If `f` is eventually differentiable along a nontrivial filter `l : Filter ℝ` that is generated
by convex sets, the norm of `f` tends to infinity along `l`, and `f' = O(g)` along `l`, where `f'`
is the derivative of `f`, then `g` is not integrable on any set `k` belonging to `l`.
Auxiliary version assuming that `E` is complete. -/
theorem not_integrableOn_of_tendsto_norm_atTop_of_deriv_isBigO_filter_aux
    [CompleteSpace E] {f : ℝ → E} {g : ℝ → F}
    {k : Set ℝ} (l : Filter ℝ) [NeBot l] [TendstoIxxClass Icc l l]
    (hl : k ∈ l) (hd : ∀ᶠ x in l, DifferentiableAt ℝ f x) (hf : Tendsto (fun x => ‖f x‖) l atTop)
    (hfg : deriv f =O[l] g) : ¬IntegrableOn g k := by
  intro hgi
  obtain ⟨C, hC₀, s, hsl, hsub, hfd, hg⟩ :
    ∃ (C : ℝ) (_ : 0 ≤ C), ∃ s ∈ l, (∀ x ∈ s, ∀ y ∈ s, [[x, y]] ⊆ k) ∧
      (∀ x ∈ s, ∀ y ∈ s, ∀ z ∈ [[x, y]], DifferentiableAt ℝ f z) ∧
        ∀ x ∈ s, ∀ y ∈ s, ∀ z ∈ [[x, y]], ‖deriv f z‖ ≤ C * ‖g z‖ := by
    rcases hfg.exists_nonneg with ⟨C, C₀, hC⟩
    have h : ∀ᶠ x : ℝ × ℝ in l ×ˢ l,
        ∀ y ∈ [[x.1, x.2]], (DifferentiableAt ℝ f y ∧ ‖deriv f y‖ ≤ C * ‖g y‖) ∧ y ∈ k :=
      (tendsto_fst.uIcc tendsto_snd).eventually ((hd.and hC.bound).and hl).smallSets
    rcases mem_prod_self_iff.1 h with ⟨s, hsl, hs⟩
    simp only [prod_subset_iff, mem_ofPred_eq] at hs
    exact ⟨C, C₀, s, hsl, fun x hx y hy z hz => (hs x hx y hy z hz).2, fun x hx y hy z hz =>
      (hs x hx y hy z hz).1.1, fun x hx y hy z hz => (hs x hx y hy z hz).1.2⟩
  replace hgi : IntegrableOn (fun x ↦ C * ‖g x‖) k := by exact hgi.norm.smul C
  obtain ⟨c, hc, d, hd, hlt⟩ : ∃ c ∈ s, ∃ d ∈ s, (‖f c‖ + ∫ y in k, C * ‖g y‖) < ‖f d‖ := by
    rcases Filter.nonempty_of_mem hsl with ⟨c, hc⟩
    have : ∀ᶠ x in l, (‖f c‖ + ∫ y in k, C * ‖g y‖) < ‖f x‖ :=
      hf.eventually (eventually_gt_atTop _)
    exact ⟨c, hc, (this.and hsl).exists.imp fun d hd => ⟨hd.2, hd.1⟩⟩
  specialize hsub c hc d hd; specialize hfd c hc d hd
  replace hg : ∀ x ∈ Ι c d, ‖deriv f x‖ ≤ C * ‖g x‖ :=
    fun z hz => hg c hc d hd z ⟨hz.1.le, hz.2⟩
  have hg_ae : ∀ᵐ x ∂volume.restrict (Ι c d), ‖deriv f x‖ ≤ C * ‖g x‖ :=
    (ae_restrict_mem measurableSet_uIoc).mono hg
  have hsub' : Ι c d ⊆ k := Subset.trans Ioc_subset_Icc_self hsub
  have hfi : IntervalIntegrable (deriv f) volume c d := by
    rw [intervalIntegrable_iff]
    have : IntegrableOn (fun x ↦ C * ‖g x‖) (Ι c d) := IntegrableOn.mono hgi hsub' le_rfl
    exact Integrable.mono' this (aestronglyMeasurable_deriv _ _) hg_ae
  refine hlt.not_ge (sub_le_iff_le_add'.1 ?_)
  calc
    ‖f d‖ - ‖f c‖ ≤ ‖f d - f c‖ := norm_sub_norm_le _ _
    _ = ‖∫ x in c..d, deriv f x‖ := congr_arg _ (integral_deriv_eq_sub hfd hfi).symm
    _ = ‖∫ x in Ι c d, deriv f x‖ := norm_integral_eq_norm_integral_uIoc _
    _ ≤ ∫ x in Ι c d, ‖deriv f x‖ := MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ x in Ι c d, C * ‖g x‖ :=
      setIntegral_mono_on hfi.norm.def' (hgi.mono_set hsub') measurableSet_uIoc hg
    _ ≤ ∫ x in k, C * ‖g x‖ := by
      apply setIntegral_mono_set hgi
        (ae_of_all _ fun x => mul_nonneg hC₀ (norm_nonneg _)) hsub'.eventuallySubset

theorem not_integrableOn_of_tendsto_norm_atTop_of_deriv_isBigO_filter
    {f : ℝ → E} {g : ℝ → F}
    {k : Set ℝ} (l : Filter ℝ) [NeBot l] [TendstoIxxClass Icc l l]
    (hl : k ∈ l) (hd : ∀ᶠ x in l, DifferentiableAt ℝ f x) (hf : Tendsto (fun x => ‖f x‖) l atTop)
    (hfg : deriv f =O[l] g) : ¬IntegrableOn g k := by
  let a : E →ₗᵢ[ℝ] UniformSpace.Completion E := UniformSpace.Completion.toComplₗᵢ
  let f' := a ∘ f
  have hder (x : ℝ) (hx : DifferentiableAt ℝ f x) :
      HasDerivAt f' (a (deriv f x)) x :=
    a.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt x hx.hasDerivAt
  have h'd : ∀ᶠ x in l, DifferentiableAt ℝ f' x :=
    hd.mono fun x hx ↦ (hder x hx).differentiableAt
  have h'f : Tendsto (fun x => ‖f' x‖) l atTop := hf.congr (fun x ↦ by simp [f'])
  have h'fg : deriv f' =O[l] g := by
    apply IsBigO.trans _ hfg
    rw [← isBigO_norm_norm]
    suffices (fun x ↦ ‖deriv f' x‖) =ᶠ[l] (fun x ↦ ‖deriv f x‖) by exact this.isBigO
    filter_upwards [hd] with x hx
    simp [(hder x hx).deriv]
  exact not_integrableOn_of_tendsto_norm_atTop_of_deriv_isBigO_filter_aux l hl h'd h'f h'fg

/-- If `f` is eventually differentiable along a nontrivial filter `l : Filter ℝ` that is generated
by convex sets, the norm of `f` tends to infinity along `l`, and `f' = O(g)` along `l`, where `f'`
is the derivative of `f`, then `g` is not integrable on any interval `a..b` such that
`[a, b] ∈ l`. -/
theorem not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_filter {f : ℝ → E} {g : ℝ → F}
    {a b : ℝ} (l : Filter ℝ) [NeBot l] [TendstoIxxClass Icc l l] (hl : [[a, b]] ∈ l)
    (hd : ∀ᶠ x in l, DifferentiableAt ℝ f x) (hf : Tendsto (fun x => ‖f x‖) l atTop)
    (hfg : deriv f =O[l] g) : ¬IntervalIntegrable g volume a b := by
  rw [intervalIntegrable_iff']
  exact not_integrableOn_of_tendsto_norm_atTop_of_deriv_isBigO_filter _ hl hd hf hfg

/-- If `a ≠ b`, `c ∈ [a, b]`, `f` is differentiable in the neighborhood of `c` within
`[a, b] \ {c}`, `‖f x‖ → ∞` as `x → c` within `[a, b] \ {c}`, and `f' = O(g)` along
`𝓝[[a, b] \ {c}] c`, where `f'` is the derivative of `f`, then `g` is not interval integrable on
`a..b`. -/
theorem not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_within_sdiff_singleton
    {f : ℝ → E} {g : ℝ → F} {a b c : ℝ} (hne : a ≠ b) (hc : c ∈ [[a, b]])
    (h_deriv : ∀ᶠ x in 𝓝[[[a, b]] \ {c}] c, DifferentiableAt ℝ f x)
    (h_infty : Tendsto (fun x => ‖f x‖) (𝓝[[[a, b]] \ {c}] c) atTop)
    (hg : deriv f =O[𝓝[[[a, b]] \ {c}] c] g) : ¬IntervalIntegrable g volume a b := by
  obtain ⟨l, hl, hl', hle, hmem⟩ :
    ∃ l : Filter ℝ, TendstoIxxClass Icc l l ∧ l.NeBot ∧ l ≤ 𝓝 c ∧ [[a, b]] \ {c} ∈ l := by
    rcases (min_lt_max.2 hne).gt_or_lt c with hlt | hlt
    · refine ⟨𝓝[<] c, inferInstance, inferInstance, inf_le_left, ?_⟩
      rw [← Iic_sdiff_right]
      exact sdiff_mem_nhdsWithin_sdiff (Icc_mem_nhdsLE_of_mem ⟨hlt, hc.2⟩) _
    · refine ⟨𝓝[>] c, inferInstance, inferInstance, inf_le_left, ?_⟩
      rw [← Ici_sdiff_left]
      exact sdiff_mem_nhdsWithin_sdiff (Icc_mem_nhdsGE_of_mem ⟨hc.1, hlt⟩) _
  have : l ≤ 𝓝[[[a, b]] \ {c}] c := le_inf hle (le_principal_iff.2 hmem)
  exact not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_filter l
    (mem_of_superset hmem sdiff_subset) (h_deriv.filter_mono this) (h_infty.mono_left this)
    (hg.mono this)

/-- If `f` is differentiable in a punctured neighborhood of `c`, `‖f x‖ → ∞` as `x → c` (more
formally, along the filter `𝓝[≠] c`), and `f' = O(g)` along `𝓝[≠] c`, where `f'` is the derivative
of `f`, then `g` is not interval integrable on any nontrivial interval `a..b` such that
`c ∈ [a, b]`. -/
theorem not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_punctured {f : ℝ → E}
    {g : ℝ → F} {a b c : ℝ} (h_deriv : ∀ᶠ x in 𝓝[≠] c, DifferentiableAt ℝ f x)
    (h_infty : Tendsto (fun x => ‖f x‖) (𝓝[≠] c) atTop) (hg : deriv f =O[𝓝[≠] c] g) (hne : a ≠ b)
    (hc : c ∈ [[a, b]]) : ¬IntervalIntegrable g volume a b :=
  have : 𝓝[[[a, b]] \ {c}] c ≤ 𝓝[≠] c := nhdsWithin_mono _ inter_subset_right
  not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_within_sdiff_singleton hne hc
    (h_deriv.filter_mono this) (h_infty.mono_left this) (hg.mono this)

private theorem hasDerivAt_log_sub (c x : ℝ) (hx : x ≠ c) :
    HasDerivAt (fun y : ℝ ↦ Real.log (y - c)) (Checked.inv (x - c) (sub_ne_zero.mpr hx).isUnit)
      x := by
  simpa only [id_eq, one_div₀] using
    ((hasDerivAt_id x).sub_const c).log (hx := (sub_ne_zero.mpr hx).isUnit)

/-- If `f` grows in the punctured neighborhood of `c : ℝ` at least as fast as `1 / (x - c)`,
then it is not interval integrable on any nontrivial interval `a..b`, `c ∈ [a, b]`. -/
theorem not_intervalIntegrable_of_sub_inv_isBigO_punctured {f : ℝ → F} {a b c : ℝ}
    (hf : (fun x : {x : ℝ // x ≠ c} ↦ Checked.inv (x.val - c) (sub_ne_zero.mpr x.2).isUnit)
      =O[comap Subtype.val (𝓝[≠] c)] (f ∘ Subtype.val))
    (hne : a ≠ b) (hc : c ∈ [[a, b]]) :
    ¬IntervalIntegrable f volume a b := by
  have hd : ∀ᶠ x in 𝓝[≠] c, DifferentiableAt ℝ (fun x ↦ Real.log (x - c)) x :=
    eventually_of_mem self_mem_nhdsWithin fun x hx ↦ (hasDerivAt_log_sub c x hx).differentiableAt
  have hnorm : Tendsto (fun x => ‖Real.log (x - c)‖) (𝓝[≠] c) atTop := by
    refine tendsto_abs_atBot_atTop.comp (Real.tendsto_log_nhdsNE_zero.comp ?_)
    rw [← sub_self c]
    exact ((hasDerivAt_id c).sub_const c).tendsto_nhdsNE one_ne_zero
  refine not_intervalIntegrable_of_tendsto_norm_atTop_of_deriv_isBigO_punctured hd hnorm ?_ hne hc
  obtain ⟨C, hC⟩ := hf.isBigOWith
  refine IsBigO.of_bound C ?_
  filter_upwards [self_mem_nhdsWithin, eventually_comap.mp hC.bound] with x hx h
  rw [(hasDerivAt_log_sub c x hx).deriv]
  exact h ⟨x, hx⟩ rfl

/-- The function `fun x => (x - c)⁻¹` is integrable on `a..b` if and only if
`a = b` or `c ∉ [a, b]`. -/
@[simp]
theorem intervalIntegrable_sub_inv_iff {a b c : ℝ} :
    Integrable (fun x : ↥([[a, b]] \ {c}) ↦
      Checked.inv (x.val - c) (sub_ne_zero.mpr x.2.2).isUnit)
      (volume.comap Subtype.val) ↔ a = b ∨ c ∉ [[a, b]] := by
  have hrestrict : volume.restrict ([[a, b]] \ {c}) = volume.restrict [[a, b]] := by
    apply Measure.restrict_congr_set
    filter_upwards [volume.ae_ne c] with x hx
    simp [hx]
  have hiff : Integrable (fun x : ↥([[a, b]] \ {c}) ↦
      Checked.inv (x.val - c) (sub_ne_zero.mpr x.2.2).isUnit) (volume.comap Subtype.val)
      ↔ IntervalIntegrable (deriv fun x : ℝ ↦ Real.log (x - c)) volume a b := by
    rw [intervalIntegrable_iff', IntegrableOn, ← hrestrict, ← IntegrableOn,
      integrableOn_iff_comap_subtypeVal (measurableSet_uIcc.diff (measurableSet_singleton c))]
    exact integrable_congr (Eventually.of_forall fun x ↦ (hasDerivAt_log_sub c x x.2.2).deriv.symm)
  rw [hiff]
  constructor
  · refine fun h ↦ or_iff_not_imp_left.2 fun hne hc ↦ ?_
    apply not_intervalIntegrable_of_sub_inv_isBigO_punctured _ hne hc h
    refine (isBigO_refl _ _).congr_left ?_
    intro x
    exact (hasDerivAt_log_sub c x x.2).deriv
  · rintro (rfl | h₀)
    · exact IntervalIntegrable.refl
    apply ContinuousOn.intervalIntegrable
    rw [continuousOn_iff_continuous_domRestrict]
    have hx (x : [[a, b]]) : x.val ≠ c := ne_of_mem_of_not_mem x.2 h₀
    change Continuous (fun x : [[a, b]] ↦ deriv (fun y ↦ Real.log (y - c)) x.val)
    simp_rw [fun x : [[a, b]] ↦ (hasDerivAt_log_sub c x (hx x)).deriv]
    exact (continuous_subtype_val.sub continuous_const).fun_inv₀

/-- The function `fun x => x⁻¹` is integrable on `a..b` if and only if
`a = b` or `0 ∉ [a, b]`. -/
@[simp]
theorem intervalIntegrable_inv_iff {a b : ℝ} :
    Integrable (fun x : ↥([[a, b]] \ {0}) ↦ Checked.inv x.val (Ne.isUnit x.2.2))
      (volume.comap Subtype.val) ↔ a = b ∨ (0 : ℝ) ∉ [[a, b]] := by
  simpa only [sub_zero] using (intervalIntegrable_sub_inv_iff (a := a) (b := b) (c := 0))

private theorem not_integrableOn_inv_of_mem_atTop {s : Set ℝ} (hs : MeasurableSet s)
    (ht : s ∈ (atTop : Filter ℝ)) (h₀ : ∀ x ∈ s, x ≠ 0) :
    ¬ Integrable (fun x : s ↦ Checked.inv x.val (h₀ x x.2).isUnit) (volume.comap Subtype.val) := by
  intro hi
  have hd : ∀ᶠ x in atTop, DifferentiableAt ℝ Real.log x :=
    eventually_of_mem (Ioi_mem_atTop (0 : ℝ)) fun _ hx ↦
      Real.differentiableAt_log (mem_Ioi.mp hx).ne'
  have hnorm : Tendsto (fun x => ‖Real.log x‖) atTop atTop :=
    tendsto_norm_atTop_atTop.comp Real.tendsto_log_atTop
  apply not_integrableOn_of_tendsto_norm_atTop_of_deriv_isBigO_filter atTop ht hd hnorm
    (isBigO_refl _ _)
  apply (integrableOn_iff_comap_subtypeVal hs).mpr
  exact hi.congr (Eventually.of_forall fun x ↦ (Real.deriv_log x (hx := (h₀ x x.2).isUnit)).symm)

/-- The function `fun x ↦ x⁻¹` is not integrable on any interval `[a, +∞)`. -/
theorem not_integrableOn_Ici_inv {a : ℝ} :
    ¬ Integrable (fun x : ↥(Ici a \ {0}) ↦ Checked.inv x.val (Ne.isUnit x.2.2))
      (volume.comap Subtype.val) := by
  refine not_integrableOn_inv_of_mem_atTop
    (measurableSet_Ici.diff (measurableSet_singleton 0)) ?_ (fun _ hx ↦ hx.2)
  exact mem_of_superset (inter_mem (Ici_mem_atTop a) (Ioi_mem_atTop (0 : ℝ)))
    fun x hx ↦ ⟨hx.1, (mem_Ioi.mp hx.2).ne'⟩

/-- The function `fun x ↦ x⁻¹` is not integrable on any interval `(a, +∞)`. -/
theorem not_integrableOn_Ioi_inv {a : ℝ} :
    ¬ Integrable (fun x : ↥(Ioi a \ {0}) ↦ Checked.inv x.val (Ne.isUnit x.2.2))
      (volume.comap Subtype.val) := by
  refine not_integrableOn_inv_of_mem_atTop
    (measurableSet_Ioi.diff (measurableSet_singleton 0)) ?_ (fun _ hx ↦ hx.2)
  exact mem_of_superset (inter_mem (Ioi_mem_atTop a) (Ioi_mem_atTop (0 : ℝ)))
    fun x hx ↦ ⟨hx.1, (mem_Ioi.mp hx.2).ne'⟩
