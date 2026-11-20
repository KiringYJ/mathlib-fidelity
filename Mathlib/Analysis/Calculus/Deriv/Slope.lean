/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.LinearAlgebra.AffineSpace.Slope
public import Mathlib.Topology.Algebra.Module.PerfectSpace

/-!
# Derivative as the limit of the slope

In this file we relate the derivative of a function with its definition from a standard
undergraduate course as the limit of the slope `(f y - f x) / (y - x)` as `y` tends to `x`.
Since we are talking about functions taking values in a normed space instead of the base field, we
use `slope f x y hxy = (y - x)⁻¹ • (f y - f x)` instead of division. The slope exists only at the
points `y ≠ x`, so the limit is taken on a subtype of such points, along the neighborhood filter of
`x` pulled back by the inclusion; its image under the inclusion is the punctured neighborhood
filter.

We also prove some estimates on the upper/lower limits of the slope in terms of the derivative.

For a more detailed overview of one-dimensional derivatives in mathlib, see the module docstring of
`Mathlib/Analysis/Calculus/Deriv/Basic.lean`.

## Keywords

derivative, slope
-/

public section

universe u v

open scoped Topology

open Filter TopologicalSpace Set

section NormedField

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {f : 𝕜 → F}
variable {f' : F}
variable {x : 𝕜}
variable {s : Set 𝕜}

/-- The derivative along a filter `L` is the limit of the slope on a set `t` of points other than
`x` that eventually contains every point of `L` other than `x`. -/
private theorem hasDerivAtFilter_iff_tendsto_slope_of_eventually {L : Filter 𝕜} {t : Set 𝕜}
    (htx : x ∉ t) (hLt : ∀ᶠ y in L, y ≠ x → y ∈ t) :
    HasDerivAtFilter f f' (L ×ˢ pure x) ↔
      Tendsto (fun y : t ↦ slope f x y (ne_of_mem_of_not_mem y.2 htx).symm) (comap (↑) L)
        (𝓝 f') := by
  rw [← tendsto_sub_nhds_zero_iff, ← Asymptotics.isLittleO_one_iff ℝ, Asymptotics.isLittleO_iff,
    hasDerivAtFilter_iff_isLittleO, prod_pure, Asymptotics.isLittleO_map,
    Asymptotics.isLittleO_iff]
  refine forall₂_congr fun c _ ↦ ?_
  simp only [Function.comp_def, norm_one, mul_one, eventually_comap, Subtype.forall]
  refine eventually_congr (hLt.mono fun y hy ↦ ?_)
  rcases eq_or_ne y x with rfl | hyx
  · refine iff_of_true (by simp) ?_
    rintro a ha rfl
    exact absurd ha htx
  have hpos : 0 < ‖y - x‖ := norm_pos_iff.2 (sub_ne_zero.2 hyx)
  have key : ‖f y - f x - (y - x) • f'‖ = ‖y - x‖ * ‖slope f x y hyx.symm - f'‖ := by
    rw [← norm_smul, smul_sub, sub_smul_slope, vsub_eq_sub]
  rw [key, mul_comm c, mul_le_mul_iff_right₀ hpos]
  constructor
  · rintro h a ha rfl
    exact h
  · intro h
    exact h y (hy hyx) rfl

/-- On a subset `t` of `s`, the neighborhoods of `x` within `s` and in the whole field have the same
pullback. -/
private theorem comap_coe_nhdsWithin_of_subset {t : Set 𝕜} (hts : t ⊆ s) :
    comap ((↑) : t → 𝕜) (𝓝[s] x) = comap (↑) (𝓝 x) := by
  have : ((↑) : t → 𝕜) ⁻¹' s = univ := eq_univ_of_forall fun y ↦ hts y.2
  rw [nhdsWithin, comap_inf, comap_principal, this, principal_univ, inf_top_eq]

/-- If the domain has dimension one, then Fréchet derivative is equivalent to the classical
definition with a limit. The slope at `y` exists only for `y ≠ x`, so the limit is taken on the
subtype `{x}ᶜ`, along `L` pulled back to it. -/
theorem hasDerivAtFilter_iff_tendsto_slope {x : 𝕜} {L : Filter 𝕜} :
    HasDerivAtFilter f f' (L ×ˢ pure x) ↔
      Tendsto (fun y : ↥({x}ᶜ : Set 𝕜) ↦ slope f x y (Ne.symm y.2)) (comap (↑) L) (𝓝 f') :=
  hasDerivAtFilter_iff_tendsto_slope_of_eventually (notMem_compl_iff.2 (mem_singleton x))
    (.of_forall fun _ h ↦ h)

theorem hasDerivWithinAt_iff_tendsto_slope :
    HasDerivWithinAt f f' s x ↔
      Tendsto (fun y : ↥(s \ {x}) ↦ slope f x y fun h ↦ y.2.2 h.symm) (comap (↑) (𝓝 x))
        (𝓝 f') := by
  rw [← comap_coe_nhdsWithin_of_subset sdiff_subset]
  exact hasDerivAtFilter_iff_tendsto_slope_of_eventually (L := 𝓝[s] x) (t := s \ {x})
    (fun h ↦ h.2 (mem_singleton x)) (eventually_nhdsWithin_of_forall fun _ hy hyx ↦ ⟨hy, hyx⟩)

/-- If `x ∉ s`, then the derivative within `s` is the limit of the slope on `s` itself. -/
theorem hasDerivWithinAt_iff_tendsto_slope' (hs : x ∉ s) :
    HasDerivWithinAt f f' s x ↔
      Tendsto (fun y : ↥s ↦ slope f x y (ne_of_mem_of_not_mem y.2 hs).symm) (comap (↑) (𝓝 x))
        (𝓝 f') := by
  rw [← comap_coe_nhdsWithin_of_subset subset_rfl]
  exact hasDerivAtFilter_iff_tendsto_slope_of_eventually (L := 𝓝[s] x) hs
    (eventually_nhdsWithin_of_forall fun _ hy _ ↦ hy)

theorem hasDerivAt_iff_tendsto_slope :
    HasDerivAt f f' x ↔
      Tendsto (fun y : ↥({x}ᶜ : Set 𝕜) ↦ slope f x y (Ne.symm y.2)) (comap (↑) (𝓝 x)) (𝓝 f') :=
  hasDerivAtFilter_iff_tendsto_slope

alias ⟨HasDerivAt.tendsto_slope, _⟩ := hasDerivAt_iff_tendsto_slope

theorem hasDerivAt_iff_tendsto_slope_left_right [LinearOrder 𝕜] : HasDerivAt f f' x ↔
    Tendsto (fun y : ↥(Iio x) ↦ slope f x y y.2.ne') (comap (↑) (𝓝 x)) (𝓝 f') ∧
      Tendsto (fun y : ↥(Ioi x) ↦ slope f x y y.2.ne) (comap (↑) (𝓝 x)) (𝓝 f') := by
  rw [← hasDerivWithinAt_iff_tendsto_slope' self_notMem_Iio,
    ← hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi, ← hasDerivWithinAt_univ,
    ← hasDerivWithinAt_sdiff_singleton, ← compl_eq_univ_sdiff, ← Iio_union_Ioi]
  exact ⟨fun h ↦ ⟨h.mono subset_union_left, h.mono subset_union_right⟩, fun h ↦ h.1.union h.2⟩

/-- The derivative is the limit of the slope `t⁻¹ • (f (x + (t : 𝕜)) - f x)` over the increments
`t ≠ 0`. -/
theorem hasDerivAt_iff_tendsto_slope_zero :
    HasDerivAt f f' x ↔
      Tendsto (fun t : ↥({0}ᶜ : Set 𝕜) ↦
        Checked.inv (t : 𝕜) (Ne.isUnit t.2) • (f (x + (t : 𝕜)) - f x))
        (comap (↑) (𝓝 (0 : 𝕜))) (𝓝 f') := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hσ : Tendsto (fun y : ↥({x}ᶜ : Set 𝕜) ↦ (⟨(y : 𝕜) - x, sub_ne_zero.2 y.2⟩ : ↥({0}ᶜ : Set 𝕜)))
      (comap (↑) (𝓝 x)) (comap (↑) (𝓝 (0 : 𝕜))) := by
    refine tendsto_comap_iff.2 ?_
    exact ((continuous_sub_right x).tendsto' x 0 (sub_self x)).comp tendsto_comap
  have hτ : Tendsto
      (fun t : ↥({0}ᶜ : Set 𝕜) ↦ (⟨x + (t : 𝕜), fun h ↦ t.2 (add_eq_left.1 h)⟩ : ↥({x}ᶜ : Set 𝕜)))
      (comap (↑) (𝓝 (0 : 𝕜))) (comap (↑) (𝓝 x)) := by
    refine tendsto_comap_iff.2 ?_
    exact ((continuous_const.add continuous_id : Continuous (fun t : 𝕜 ↦ x + t)).tendsto'
      0 x (add_zero x)).comp tendsto_comap
  constructor
  · intro h
    refine (h.comp hτ).congr fun t ↦ ?_
    simp only [Function.comp_apply, slope_def_module, add_sub_cancel_left]
  · intro h
    refine (h.comp hσ).congr fun y ↦ ?_
    simp only [Function.comp_apply, slope_def_module, add_sub_cancel]

alias ⟨HasDerivAt.tendsto_slope_zero, _⟩ := hasDerivAt_iff_tendsto_slope_zero

theorem HasDerivAt.tendsto_slope_zero_right [Preorder 𝕜] (h : HasDerivAt f f' x) :
    Tendsto (fun t : ↥(Ioi (0 : 𝕜)) ↦ Checked.inv (t : 𝕜) t.2.ne'.isUnit • (f (x + (t : 𝕜)) - f x))
      (comap (↑) (𝓝 (0 : 𝕜))) (𝓝 f') :=
  h.tendsto_slope_zero.comp <| (tendsto_comap_iff (f := fun t : ↥(Ioi (0 : 𝕜)) ↦
    (⟨t, t.2.ne'⟩ : ↥({0}ᶜ : Set 𝕜)))).2 tendsto_comap

theorem HasDerivAt.tendsto_slope_zero_left [Preorder 𝕜] (h : HasDerivAt f f' x) :
    Tendsto (fun t : ↥(Iio (0 : 𝕜)) ↦ Checked.inv (t : 𝕜) t.2.ne.isUnit • (f (x + (t : 𝕜)) - f x))
      (comap (↑) (𝓝 (0 : 𝕜))) (𝓝 f') :=
  h.tendsto_slope_zero.comp <| (tendsto_comap_iff (f := fun t : ↥(Iio (0 : 𝕜)) ↦
    (⟨t, t.2.ne⟩ : ↥({0}ᶜ : Set 𝕜)))).2 tendsto_comap

/-- Given a set `t` such that `s ∩ t` is dense in `s`, then the range of `derivWithin f s` is
contained in the closure of the submodule spanned by the image of `t`. -/
theorem range_derivWithin_subset_closure_span_image
    (f : 𝕜 → F) {s t : Set 𝕜} (h : s ⊆ closure (s ∩ t)) :
    range (derivWithin f s) ⊆ closure (Submodule.span 𝕜 (f '' t)) := by
  rintro - ⟨x, rfl⟩
  change derivWithin f s x ∈ closure (Submodule.span 𝕜 (f '' t))
  by_cases H : UniqueDiffWithinAt 𝕜 s x; swap
  · simpa [derivWithin_zero_of_not_uniqueDiffWithinAt H] using subset_closure (zero_mem _)
  by_cases H' : DifferentiableWithinAt 𝕜 f s x; swap
  · rw [derivWithin_zero_of_not_differentiableWithinAt H']
    exact subset_closure (zero_mem _)
  have I : (𝓝[(s ∩ t) \ {x}] x).NeBot := by
    rw [← accPt_principal_iff_nhdsWithin, ← uniqueDiffWithinAt_iff_accPt]
    exact H.mono_closure h
  have : (comap ((↑) : ↥((s ∩ t) \ {x}) → 𝕜) (𝓝 x)).NeBot :=
    mem_closure_iff_comap_neBot.1 (mem_closure_iff_nhdsWithin_neBot.2 I)
  have : Tendsto (fun y : ↥((s ∩ t) \ {x}) ↦ slope f x y fun h ↦ y.2.2 h.symm)
      (comap (↑) (𝓝 x)) (𝓝 (derivWithin f s x)) :=
    hasDerivWithinAt_iff_tendsto_slope.1 (H'.hasDerivWithinAt.mono inter_subset_left)
  rw [← closure_closure, ← Submodule.topologicalClosure_coe]
  apply mem_closure_of_tendsto this
  refine Eventually.of_forall fun y ↦ ?_
  simp only [slope_def_module, SetLike.mem_coe]
  refine Submodule.smul_mem _ _ (Submodule.sub_mem _ ?_ ?_)
  · apply Submodule.le_topologicalClosure
    apply Submodule.subset_span
    exact mem_image_of_mem _ y.2.1.2
  · apply Submodule.closure_subset_topologicalClosure_span
    suffices A : f x ∈ closure (f '' (s ∩ t)) from
      closure_mono (image_mono inter_subset_right) A
    apply ContinuousWithinAt.mem_closure_image
    · apply H'.continuousWithinAt.mono inter_subset_left
    rw [mem_closure_iff_nhdsWithin_neBot]
    exact I.mono (nhdsWithin_mono _ sdiff_subset)

/-- Given a dense set `t`, then the range of `deriv f` is contained in the closure of the submodule
spanned by the image of `t`. -/
theorem range_deriv_subset_closure_span_image
    (f : 𝕜 → F) {t : Set 𝕜} (h : Dense t) :
    range (deriv f) ⊆ closure (Submodule.span 𝕜 (f '' t)) := by
  rw [← derivWithin_univ]
  apply range_derivWithin_subset_closure_span_image
  simp [dense_iff_closure_eq.1 h]

theorem isSeparable_range_derivWithin [SeparableSpace 𝕜] (f : 𝕜 → F) (s : Set 𝕜) :
    IsSeparable (range (derivWithin f s)) := by
  obtain ⟨t, ts, t_count, ht⟩ : ∃ t, t ⊆ s ∧ Set.Countable t ∧ s ⊆ closure t :=
    (IsSeparable.of_separableSpace s).exists_countable_dense_subset
  have : s ⊆ closure (s ∩ t) := by rwa [inter_eq_self_of_subset_right ts]
  apply IsSeparable.mono _ (range_derivWithin_subset_closure_span_image f this)
  exact (Countable.image t_count f).isSeparable.span.closure

theorem isSeparable_range_deriv [SeparableSpace 𝕜] (f : 𝕜 → F) :
    IsSeparable (range (deriv f)) := by
  rw [← derivWithin_univ]
  exact isSeparable_range_derivWithin _ _

/-- The difference quotient of `f` at `c`, completed at `c` by the derivative `a` of `f` at `c`, is
continuous at `c`. -/
lemma HasDerivAt.continuousAt_div [DecidableEq 𝕜] {f : 𝕜 → 𝕜} {c a : 𝕜} (hf : HasDerivAt f a c) :
    ContinuousAt (fun x ↦ if hx : x = c then a else (f x - f c) / (x - c)) c := by
  have hc : 𝓝[{c}ᶜ] c = map ((↑) : ↥({c}ᶜ : Set 𝕜) → 𝕜) (comap (↑) (𝓝 c)) := by
    rw [map_comap, Subtype.range_coe]
    rfl
  refine continuousWithinAt_compl_self.1 ?_
  rw [ContinuousWithinAt, dite_eq_left rfl, hc, tendsto_map'_iff]
  refine (hasDerivAt_iff_tendsto_slope.1 hf).congr fun y ↦ ?_
  simp only [Function.comp_apply, dite_eq_right (show (y : 𝕜) ≠ c from y.2), slope_def_field]

section Order

variable [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [OrderTopology 𝕜] {g : 𝕜 → 𝕜} {g' : 𝕜}

/-- If a monotone function has a derivative within a set at a non-isolated point, then this
derivative is nonnegative. -/
lemma HasDerivWithinAt.nonneg_of_monotoneOn (hx : AccPt x (𝓟 s))
    (hd : HasDerivWithinAt g g' s x) (hg : MonotoneOn g s) : 0 ≤ g' := by
  have : (𝓝[s \ {x}] x).NeBot := accPt_principal_iff_nhdsWithin.mp hx
  have : (comap ((↑) : ↥(s \ {x}) → 𝕜) (𝓝 x)).NeBot :=
    mem_closure_iff_comap_neBot.1 (mem_closure_iff_nhdsWithin_neBot.2 this)
  have h'g : MonotoneOn g (insert x s) :=
    hg.insert_of_continuousWithinAt hx.clusterPt hd.continuousWithinAt
  refine ge_of_tendsto (hasDerivWithinAt_iff_tendsto_slope.mp hd) (Eventually.of_forall fun y ↦ ?_)
  exact h'g.slope_nonneg (mem_insert x s) (mem_insert_of_mem x y.2.1)

/-- The derivative within a set of a monotone function is nonnegative. -/
lemma MonotoneOn.derivWithin_nonneg (hg : MonotoneOn g s) :
    0 ≤ derivWithin g s x := by
  by_cases hd : DifferentiableWithinAt 𝕜 g s x; swap
  · simp [derivWithin_zero_of_not_differentiableWithinAt hd]
  by_cases hx : AccPt x (𝓟 s); swap
  · simp [derivWithin_zero_of_not_accPt hx]
  exact hd.hasDerivWithinAt.nonneg_of_monotoneOn hx hg

/-- If a monotone function has a derivative, then this derivative is nonnegative. -/
lemma HasDerivAt.nonneg_of_monotone (hd : HasDerivAt g g' x) (hg : Monotone g) : 0 ≤ g' := by
  rw [← hasDerivWithinAt_univ] at hd
  apply hd.nonneg_of_monotoneOn _ (hg.monotoneOn _)
  exact PerfectSpace.univ_preperfect _ (mem_univ _)

/-- The derivative of a monotone function is nonnegative. -/
lemma Monotone.deriv_nonneg (hg : Monotone g) : 0 ≤ deriv g x := by
  rw [← congrFun derivWithin_univ x]
  exact (hg.monotoneOn univ).derivWithin_nonneg

/-- If an antitone function has a derivative within a set at a non-isolated point, then this
derivative is nonpositive. -/
lemma HasDerivWithinAt.nonpos_of_antitoneOn (hx : AccPt x (𝓟 s))
    (hd : HasDerivWithinAt g g' s x) (hg : AntitoneOn g s) : g' ≤ 0 := by
  have : MonotoneOn (-g) s := fun x hx y hy hxy ↦ by simpa using hg hx hy hxy
  simpa using hd.neg.nonneg_of_monotoneOn hx this

/-- The derivative within a set of an antitone function is nonpositive. -/
lemma AntitoneOn.derivWithin_nonpos (hg : AntitoneOn g s) :
    derivWithin g s x ≤ 0 := by
  have h := hg.neg.derivWithin_nonneg (x := x)
  change 0 ≤ derivWithin (-g) s x at h
  simpa only [derivWithin.neg, neg_nonneg] using h

/-- If an antitone function has a derivative, then this derivative is nonpositive. -/
lemma HasDerivAt.nonpos_of_antitone (hd : HasDerivAt g g' x) (hg : Antitone g) : g' ≤ 0 := by
  rw [← hasDerivWithinAt_univ] at hd
  apply hd.nonpos_of_antitoneOn _ (hg.antitoneOn _)
  exact PerfectSpace.univ_preperfect _ (mem_univ _)

/-- The derivative of an antitone function is nonpositive. -/
lemma Antitone.deriv_nonpos (hg : Antitone g) : deriv g x ≤ 0 := by
  rw [← congrFun derivWithin_univ x]
  exact (hg.antitoneOn univ).derivWithin_nonpos

end Order

end NormedField

/-! ### Upper estimates on liminf and limsup

The slope at `z` and the ratios below exist only for `z ≠ x`, so the estimates are stated on a
subtype of such points, along the neighborhood filter of `x` pulled back by the inclusion. -/

section Real

variable {f : ℝ → ℝ} {f' : ℝ} {s : Set ℝ} {x : ℝ} {r : ℝ}

theorem HasDerivWithinAt.limsup_slope_le (hf : HasDerivWithinAt f f' s x) (hr : f' < r) :
    ∀ᶠ (z : ↥(s \ {x})) in comap ((↑) : ↥(s \ {x}) → ℝ) (𝓝 x),
      slope f x z (fun h ↦ z.2.2 h.symm) < r :=
  hasDerivWithinAt_iff_tendsto_slope.1 hf (IsOpen.mem_nhds isOpen_Iio hr)

theorem HasDerivWithinAt.limsup_slope_le' (hf : HasDerivWithinAt f f' s x) (hs : x ∉ s)
    (hr : f' < r) :
    ∀ᶠ (z : ↥s) in comap ((↑) : ↥s → ℝ) (𝓝 x), slope f x z (ne_of_mem_of_not_mem z.2 hs).symm < r :=
  (hasDerivWithinAt_iff_tendsto_slope' hs).1 hf (IsOpen.mem_nhds isOpen_Iio hr)

theorem HasDerivWithinAt.liminf_right_slope_le (hf : HasDerivWithinAt f f' (Ici x) x)
    (hr : f' < r) : ∃ᶠ (z : ↥(Ioi x)) in comap ((↑) : ↥(Ioi x) → ℝ) (𝓝 x), slope f x z z.2.ne < r :=
  have : (comap ((↑) : ↥(Ioi x) → ℝ) (𝓝 x)).NeBot := mem_closure_iff_comap_neBot.1 (by simp)
  (hf.Ioi_of_Ici.limsup_slope_le' (lt_irrefl x) hr).frequently

end Real

section RealSpace

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E} {f' : E} {s : Set ℝ}
  {x r : ℝ}

/-- If `f` has derivative `f'` within `s` at `x`, then for any `r > ‖f'‖` the ratio
`‖f z - f x‖ / ‖z - x‖` is less than `r` at the points `z ≠ x` of `s` near `x`.
In other words, the limit superior of this ratio as `z` tends to `x` along `s`
is less than or equal to `‖f'‖`. -/
theorem HasDerivWithinAt.limsup_norm_slope_le (hf : HasDerivWithinAt f f' s x) (hr : ‖f'‖ < r) :
    ∀ᶠ (z : ↥(s \ {x})) in comap ((↑) : ↥(s \ {x}) → ℝ) (𝓝 x),
      Checked.inv ‖(z : ℝ) - x‖ (norm_ne_zero_iff.2 (sub_ne_zero.2 fun h ↦ z.2.2 h)).isUnit *
        ‖f z - f x‖ < r := by
  filter_upwards [(hasDerivWithinAt_iff_tendsto_slope.1 hf).norm (IsOpen.mem_nhds isOpen_Iio hr)]
    with z hz
  simpa only [mem_preimage, mem_Iio, slope_def_module, norm_smul, norm_inv] using hz

/-- If `f` has derivative `f'` within `s` at `x`, then for any `r > ‖f'‖` the ratio
`(‖f z‖ - ‖f x‖) / ‖z - x‖` is less than `r` at the points `z ≠ x` of `s` near `x`.
In other words, the limit superior of this ratio as `z` tends to `x` along `s`
is less than or equal to `‖f'‖`.

This lemma is a weaker version of `HasDerivWithinAt.limsup_norm_slope_le`
where `‖f z‖ - ‖f x‖` is replaced by `‖f z - f x‖`. -/
theorem HasDerivWithinAt.limsup_slope_norm_le (hf : HasDerivWithinAt f f' s x) (hr : ‖f'‖ < r) :
    ∀ᶠ (z : ↥(s \ {x})) in comap ((↑) : ↥(s \ {x}) → ℝ) (𝓝 x),
      Checked.inv ‖(z : ℝ) - x‖ (norm_ne_zero_iff.2 (sub_ne_zero.2 fun h ↦ z.2.2 h)).isUnit *
        (‖f z‖ - ‖f x‖) < r := by
  refine (hf.limsup_norm_slope_le hr).mono fun z hz ↦ ?_
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (norm_sub_norm_le _ _) (by positivity)) hz

/-- If `f` has derivative `f'` within `(x, +∞)` at `x`, then for any `r > ‖f'‖` the ratio
`‖f z - f x‖ / ‖z - x‖` is frequently less than `r` as `z → x+0`.
In other words, the limit inferior of this ratio as `z` tends to `x+0`
is less than or equal to `‖f'‖`. See also `HasDerivWithinAt.limsup_norm_slope_le`
for a stronger version using limit superior and any set `s`. -/
theorem HasDerivWithinAt.liminf_right_norm_slope_le (hf : HasDerivWithinAt f f' (Ici x) x)
    (hr : ‖f'‖ < r) :
    ∃ᶠ (z : ↥(Ioi x)) in comap ((↑) : ↥(Ioi x) → ℝ) (𝓝 x),
      Checked.inv ‖(z : ℝ) - x‖ (norm_ne_zero_iff.2 (sub_ne_zero.2 z.2.ne')).isUnit *
        ‖f z - f x‖ < r := by
  have : (comap ((↑) : ↥(Ioi x) → ℝ) (𝓝 x)).NeBot := mem_closure_iff_comap_neBot.1 (by simp)
  refine Eventually.frequently ?_
  filter_upwards [((hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi).1 hf.Ioi_of_Ici).norm
    (IsOpen.mem_nhds isOpen_Iio hr)] with z hz
  simpa only [mem_preimage, mem_Iio, slope_def_module, norm_smul, norm_inv] using hz

/-- If `f` has derivative `f'` within `(x, +∞)` at `x`, then for any `r > ‖f'‖` the ratio
`(‖f z‖ - ‖f x‖) / (z - x)` is frequently less than `r` as `z → x+0`.
In other words, the limit inferior of this ratio as `z` tends to `x+0`
is less than or equal to `‖f'‖`.

See also

* `HasDerivWithinAt.limsup_norm_slope_le` for a stronger version using
  limit superior and any set `s`;
* `HasDerivWithinAt.liminf_right_norm_slope_le` for a stronger version using
  `‖f z - f xp‖` instead of `‖f z‖ - ‖f x‖`. -/
theorem HasDerivWithinAt.liminf_right_slope_norm_le (hf : HasDerivWithinAt f f' (Ici x) x)
    (hr : ‖f'‖ < r) :
    ∃ᶠ (z : ↥(Ioi x)) in comap ((↑) : ↥(Ioi x) → ℝ) (𝓝 x),
      Checked.inv ((z : ℝ) - x) (sub_ne_zero.2 z.2.ne').isUnit * (‖f z‖ - ‖f x‖) < r := by
  refine (hf.liminf_right_norm_slope_le hr).mono fun z hz ↦ ?_
  have hxz : 0 ≤ (z : ℝ) - x := (sub_pos.2 z.2).le
  simp only [Real.norm_of_nonneg hxz] at hz
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (norm_sub_norm_le _ _)
    (inv_pos_of_pos (sub_pos.2 z.2)).le) hz

end RealSpace
