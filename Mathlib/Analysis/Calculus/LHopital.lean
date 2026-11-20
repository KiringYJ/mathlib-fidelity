/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# L'Hôpital's rule for 0/0 indeterminate forms

In this file, we prove several forms of "L'Hôpital's rule" for computing 0/0
indeterminate forms. The proof of `HasDerivAt.lhopital_zero_right_on_Ioo`
uses Cauchy's mean value theorem. For the limit at infinity we apply Rolle's theorem on
a ray to `q * g - f`, where `q` is a value of the quotient. Each quotient is taken on the
subtype where its denominator is invertible, with the filter induced by the original limit.

Note that the filter `f'/g'` tends to isn't required to be one of `𝓝 a`,
`atTop` or `atBot`. In fact, we give a slightly stronger statement by
allowing it to be any filter on `ℝ`.

Each statement is available in a `HasDerivAt` form and a `deriv` form, which
is denoted by each statement being in either the `HasDerivAt` or the `deriv`
namespace.

## Tags

L'Hôpital's rule, L'Hopital's rule
-/

public section


open Filter Set

open scoped Filter Topology Pointwise

variable {a b : ℝ} {l : Filter ℝ} {f f' g g' : ℝ → ℝ}

/-!
## Interval-based versions

We start by proving statements where all conditions (derivability, `g' ≠ 0`) have
to be satisfied on an explicitly-provided interval.
-/


/-- Express a quotient limit using its graph. This lets us use mean-value identities before
forming a quotient, including when the point lies in a smaller interval. -/
private theorem tendsto_divp_iff {F : Filter ℝ} :
    Tendsto (fun x : {x : ℝ // IsUnit (g x)} ↦ f x /ₚ x.property.unit)
      (comap Subtype.val F) l ↔
    ∀ s ∈ l, ∀ᶠ x in F, ∀ q, g x ≠ 0 → q * g x = f x → q ∈ s := by
  constructor
  · intro h s hs
    have hmem := eventually_comap.mp (h hs)
    filter_upwards [hmem] with x hx q hg hq
    let u := hg.isUnit
    have heq : q = f x /ₚ u.unit := eq_divp_iff_mul_eq.mpr (by simpa using hq)
    exact heq ▸ hx ⟨x, u⟩ rfl
  · intro h s hs
    apply eventually_comap.mpr
    filter_upwards [h s hs] with x hx y hy
    subst x
    exact hx _ y.property.ne_zero (by simpa using divp_mul_cancel (f y) y.property.unit)

namespace HasDerivAt

theorem lhopital_zero_right_on_Ioo (hab : a < b) (hff' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hgg' : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x) (hg' : ∀ x ∈ Ioo a b, g' x ≠ 0)
    (hfa : Tendsto f (𝓝[>] a) (𝓝 0)) (hga : Tendsto g (𝓝[>] a) (𝓝 0))
    (hdiv : Tendsto (fun x : {x : ℝ // IsUnit (g' x)} ↦ f' x /ₚ x.property.unit)
      (comap Subtype.val (𝓝[>] a)) l) :
    Tendsto (fun x : {x : ℝ // IsUnit (g x)} ↦ f x /ₚ x.property.unit)
      (comap Subtype.val (𝓝[>] a)) l := by
  have sub : ∀ x ∈ Ioo a b, Ioo a x ⊆ Ioo a b := fun x hx =>
    Ioo_subset_Ioo (le_refl a) (le_of_lt hx.2)
  have : ∀ x ∈ Ioo a b, ∃ c ∈ Ioo a x, f x * g' c = g x * f' c := by
    intro x hx
    rw [← sub_zero (f x), ← sub_zero (g x)]
    exact exists_ratio_hasDerivAt_eq_ratio_slope' g g' hx.1 f f' (fun y hy => hgg' y <| sub x hx hy)
      (fun y hy => hff' y <| sub x hx hy) hga hfa
      (tendsto_nhdsWithin_of_tendsto_nhds (hgg' x hx).continuousAt.tendsto)
      (tendsto_nhdsWithin_of_tendsto_nhds (hff' x hx).continuousAt.tendsto)
  intro s hs
  apply eventually_comap.mpr
  obtain ⟨d, had, hd⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp ((tendsto_divp_iff.mp hdiv) s hs)
  filter_upwards [Ioo_mem_nhdsGT (lt_min hab had)] with x hx y hy
  subst x
  obtain ⟨c, hc, heq⟩ := this y ⟨hx.1, hx.2.trans_le (min_le_left ..)⟩
  have hcb : c < b := hc.2.trans (hx.2.trans_le (min_le_left ..))
  have hcd : c < d := hc.2.trans (hx.2.trans_le (min_le_right ..))
  apply hd ⟨hc.1, hcd⟩ _ (hg' c ⟨hc.1, hcb⟩)
  have hq : f y /ₚ y.property.unit * g y = f y := by
    simpa using divp_mul_cancel (f y) y.property.unit
  exact mul_right_cancel₀ y.property.ne_zero (by linear_combination (g' c) * hq + heq)

theorem lhopital_zero_right_on_Ico (hab : a < b) (hff' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hgg' : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x) (hcf : ContinuousOn f (Ico a b))
    (hcg : ContinuousOn g (Ico a b)) (hg' : ∀ x ∈ Ioo a b, g' x ≠ 0) (hfa : f a = 0) (hga : g a = 0)
    (hdiv : Tendsto (fun x : {x : ℝ // IsUnit (g' x)} ↦ f' x /ₚ x.property.unit)
      (comap Subtype.val (𝓝[>] a)) l) :
    Tendsto (fun x : {x : ℝ // IsUnit (g x)} ↦ f x /ₚ x.property.unit)
      (comap Subtype.val (𝓝[>] a)) l := by
  refine lhopital_zero_right_on_Ioo hab hff' hgg' hg' ?_ ?_ hdiv
  · rw [← hfa, ← nhdsWithin_Ioo_eq_nhdsGT hab]
    exact ((hcf a <| left_mem_Ico.mpr hab).mono Ioo_subset_Ico_self).tendsto
  · rw [← hga, ← nhdsWithin_Ioo_eq_nhdsGT hab]
    exact ((hcg a <| left_mem_Ico.mpr hab).mono Ioo_subset_Ico_self).tendsto

theorem lhopital_zero_left_on_Ioo (hab : a < b) (hff' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hgg' : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x) (hg' : ∀ x ∈ Ioo a b, g' x ≠ 0)
    (hfb : Tendsto f (𝓝[<] b) (𝓝 0)) (hgb : Tendsto g (𝓝[<] b) (𝓝 0))
    (hdiv : Tendsto (fun x : {x : ℝ // IsUnit (g' x)} ↦ f' x /ₚ x.property.unit)
      (comap Subtype.val (𝓝[<] b)) l) :
    Tendsto (fun x : {x : ℝ // IsUnit (g x)} ↦ f x /ₚ x.property.unit)
      (comap Subtype.val (𝓝[<] b)) l := by
  -- Here, we essentially compose by `Neg.neg`. The following is mostly technical details.
  have hdnf : ∀ x ∈ -Ioo a b, HasDerivAt (f ∘ Neg.neg) (f' (-x) * -1) x := fun x hx =>
    comp x (hff' (-x) hx) (hasDerivAt_neg x)
  have hdng : ∀ x ∈ -Ioo a b, HasDerivAt (g ∘ Neg.neg) (g' (-x) * -1) x := fun x hx =>
    comp x (hgg' (-x) hx) (hasDerivAt_neg x)
  rw [neg_Ioo] at hdnf hdng
  have := lhopital_zero_right_on_Ioo (neg_lt_neg hab) hdnf hdng (by grind)
    (hfb.comp tendsto_neg_nhdsGT_neg) (hgb.comp tendsto_neg_nhdsGT_neg)
    (by
      apply (tendsto_divp_iff (f := fun x ↦ f' (-x) * -1) (g := fun x ↦ g' (-x) * -1) (l := l)).mpr
      intro s hs
      filter_upwards [tendsto_neg_nhdsGT_neg.eventually ((tendsto_divp_iff.mp hdiv) s hs)]
        with x hx q hg hq
      exact hx q (by simpa using hg) (by simpa using hq))
  apply tendsto_divp_iff.mpr
  intro s hs
  simpa only [Function.comp_apply, neg_neg] using
    tendsto_neg_nhdsLT.eventually
      ((tendsto_divp_iff (f := f ∘ Neg.neg) (g := g ∘ Neg.neg)).mp this s hs)

theorem lhopital_zero_left_on_Ioc (hab : a < b) (hff' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hgg' : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x) (hcf : ContinuousOn f (Ioc a b))
    (hcg : ContinuousOn g (Ioc a b)) (hg' : ∀ x ∈ Ioo a b, g' x ≠ 0) (hfb : f b = 0) (hgb : g b = 0)
    (hdiv : Tendsto (fun x : {x : ℝ // IsUnit (g' x)} ↦ f' x /ₚ x.property.unit)
      (comap Subtype.val (𝓝[<] b)) l) :
    Tendsto (fun x : {x : ℝ // IsUnit (g x)} ↦ f x /ₚ x.property.unit)
      (comap Subtype.val (𝓝[<] b)) l := by
  refine lhopital_zero_left_on_Ioo hab hff' hgg' hg' ?_ ?_ hdiv
  · rw [← hfb, ← nhdsWithin_Ioo_eq_nhdsLT hab]
    exact ((hcf b <| right_mem_Ioc.mpr hab).mono Ioo_subset_Ioc_self).tendsto
  · rw [← hgb, ← nhdsWithin_Ioo_eq_nhdsLT hab]
    exact ((hcg b <| right_mem_Ioc.mpr hab).mono Ioo_subset_Ioc_self).tendsto

/-- Rolle's theorem on a closed ray when the value at the endpoint and the limit at infinity
are both zero. -/
private theorem exists_hasDerivAt_eq_zero_atTop {h h' : ℝ → ℝ} {x : ℝ}
    (hd : ∀ t ∈ Ici x, HasDerivAt h (h' t) t) (hx : h x = 0)
    (ht : Tendsto h atTop (𝓝 0)) : ∃ c, x < c ∧ h' c = 0 := by
  obtain ⟨y, hxy⟩ := exists_gt x
  have hc {z : ℝ} : ContinuousOn h (Icc x z) :=
    fun t ht ↦ (hd t ht.1).continuousAt.continuousWithinAt
  by_cases hy : h y = 0
  · obtain ⟨c, hc, heq⟩ := exists_hasDerivAt_eq_zero hxy hc (hx.trans hy.symm)
      (fun t ht ↦ hd t ht.1.le)
    exact ⟨c, hc.1, heq⟩
  · have hpos : 0 < h y ^ 2 := sq_pos_of_ne_zero hy
    have ht₂ : Tendsto (fun t ↦ h t ^ 2) atTop (𝓝 0) := by simpa using ht.pow 2
    obtain ⟨z, hyz, hz⟩ := ((eventually_gt_atTop y).and (ht₂.eventually_lt_const hpos)).exists
    obtain ⟨c, hc', hmax⟩ := isCompact_Icc.exists_isMaxOn
      (nonempty_Icc.mpr (hxy.trans hyz).le) (hc.pow 2)
    have hyc : h y ^ 2 ≤ h c ^ 2 := hmax (show y ∈ Icc x z from ⟨hxy.le, hyz.le⟩)
    have hne : h c ≠ 0 := by
      rintro heq
      rw [heq] at hyc
      linarith
    have hxc : x < c := lt_of_le_of_ne hc'.1 (fun e ↦ hne (e ▸ hx))
    have hcz : c < z := lt_of_le_of_ne hc'.2 (by rintro rfl; exact hz.not_ge hyc)
    rw [pow_two] at hmax
    have heq := (hmax.isLocalMax (Icc_mem_nhds hxc hcz)).hasDerivAt_eq_zero
      ((hd c hxc.le).mul (hd c hxc.le))
    have hprod : h' c * h c = 0 := by linarith [mul_comm (h c) (h' c)]
    exact ⟨c, hxc, (mul_eq_zero.mp hprod).resolve_right hne⟩

theorem lhopital_zero_atTop_on_Ioi (hff' : ∀ x ∈ Ioi a, HasDerivAt f (f' x) x)
    (hgg' : ∀ x ∈ Ioi a, HasDerivAt g (g' x) x) (hg' : ∀ x ∈ Ioi a, g' x ≠ 0)
    (hftop : Tendsto f atTop (𝓝 0)) (hgtop : Tendsto g atTop (𝓝 0))
    (hdiv : Tendsto (fun x : {x : ℝ // IsUnit (g' x)} ↦ f' x /ₚ x.property.unit)
      (comap Subtype.val atTop) l) :
    Tendsto (fun x : {x : ℝ // IsUnit (g x)} ↦ f x /ₚ x.property.unit)
      (comap Subtype.val atTop) l := by
  apply tendsto_divp_iff.mpr
  intro s hs
  obtain ⟨b, hb⟩ := eventually_atTop.1 ((tendsto_divp_iff.mp hdiv) s hs)
  filter_upwards [eventually_gt_atTop (max a b)] with x hx q _ hq
  have hax : a < x := (le_max_left ..).trans_lt hx
  have hbx : b < x := (le_max_right ..).trans_lt hx
  obtain ⟨c, hxc, hc⟩ := exists_hasDerivAt_eq_zero_atTop
    (h := fun t ↦ q * g t - f t) (h' := fun t ↦ q * g' t - f' t)
    (x := x) (fun t ht ↦ ((hgg' t (hax.trans_le ht)).const_mul q).sub (hff' t (hax.trans_le ht)))
    (sub_eq_zero.mpr hq) (by simpa using (hgtop.const_mul q).sub hftop)
  exact hb c (hbx.trans hxc).le q (hg' c (hax.trans hxc)) (sub_eq_zero.mp hc)

theorem lhopital_zero_atBot_on_Iio (hff' : ∀ x ∈ Iio a, HasDerivAt f (f' x) x)
    (hgg' : ∀ x ∈ Iio a, HasDerivAt g (g' x) x) (hg' : ∀ x ∈ Iio a, g' x ≠ 0)
    (hfbot : Tendsto f atBot (𝓝 0)) (hgbot : Tendsto g atBot (𝓝 0))
    (hdiv : Tendsto (fun x : {x : ℝ // IsUnit (g' x)} ↦ f' x /ₚ x.property.unit)
      (comap Subtype.val atBot) l) :
    Tendsto (fun x : {x : ℝ // IsUnit (g x)} ↦ f x /ₚ x.property.unit)
      (comap Subtype.val atBot) l := by
  -- Here, we essentially compose by `Neg.neg`. The following is mostly technical details.
  have hdnf : ∀ x ∈ -Iio a, HasDerivAt (f ∘ Neg.neg) (f' (-x) * -1) x := fun x hx =>
    comp x (hff' (-x) hx) (hasDerivAt_neg x)
  have hdng : ∀ x ∈ -Iio a, HasDerivAt (g ∘ Neg.neg) (g' (-x) * -1) x := fun x hx =>
    comp x (hgg' (-x) hx) (hasDerivAt_neg x)
  rw [neg_Iio] at hdnf hdng
  have := lhopital_zero_atTop_on_Ioi hdnf hdng (by grind)
    (hfbot.comp tendsto_neg_atTop_atBot) (hgbot.comp tendsto_neg_atTop_atBot)
    (by
      apply (tendsto_divp_iff (f := fun x ↦ f' (-x) * -1) (g := fun x ↦ g' (-x) * -1) (l := l)).mpr
      intro s hs
      filter_upwards [tendsto_neg_atTop_atBot.eventually ((tendsto_divp_iff.mp hdiv) s hs)]
        with x hx q hg hq
      exact hx q (by simpa using hg) (by simpa using hq))
  apply tendsto_divp_iff.mpr
  intro s hs
  simpa only [Function.comp_apply, neg_neg] using
    tendsto_neg_atBot_atTop.eventually
      ((tendsto_divp_iff (f := f ∘ Neg.neg) (g := g ∘ Neg.neg)).mp this s hs)

end HasDerivAt

namespace deriv

theorem lhopital_zero_right_on_Ioo (hab : a < b) (hdf : DifferentiableOn ℝ f (Ioo a b))
    (hg' : ∀ x ∈ Ioo a b, deriv g x ≠ 0) (hfa : Tendsto f (𝓝[>] a) (𝓝 0))
    (hga : Tendsto g (𝓝[>] a) (𝓝 0))
    (hdiv : Tendsto (fun x : {x : ℝ // IsUnit (deriv g x)} ↦ deriv f x /ₚ x.property.unit)
      (comap Subtype.val (𝓝[>] a)) l) :
    Tendsto (fun x : {x : ℝ // IsUnit (g x)} ↦ f x /ₚ x.property.unit)
      (comap Subtype.val (𝓝[>] a)) l := by
  have hdf : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x := fun x hx =>
    (hdf x hx).differentiableAt (Ioo_mem_nhds hx.1 hx.2)
  have hdg : ∀ x ∈ Ioo a b, DifferentiableAt ℝ g x := fun x hx =>
    by_contradiction fun h => hg' x hx (deriv_zero_of_not_differentiableAt h)
  exact HasDerivAt.lhopital_zero_right_on_Ioo hab (fun x hx => (hdf x hx).hasDerivAt)
    (fun x hx => (hdg x hx).hasDerivAt) hg' hfa hga hdiv

theorem lhopital_zero_right_on_Ico (hab : a < b) (hdf : DifferentiableOn ℝ f (Ioo a b))
    (hcf : ContinuousOn f (Ico a b)) (hcg : ContinuousOn g (Ico a b))
    (hg' : ∀ x ∈ Ioo a b, (deriv g) x ≠ 0) (hfa : f a = 0) (hga : g a = 0)
    (hdiv : Tendsto (fun x : {x : ℝ // IsUnit (deriv g x)} ↦ deriv f x /ₚ x.property.unit)
      (comap Subtype.val (𝓝[>] a)) l) :
    Tendsto (fun x : {x : ℝ // IsUnit (g x)} ↦ f x /ₚ x.property.unit)
      (comap Subtype.val (𝓝[>] a)) l := by
  refine lhopital_zero_right_on_Ioo hab hdf hg' ?_ ?_ hdiv
  · rw [← hfa, ← nhdsWithin_Ioo_eq_nhdsGT hab]
    exact ((hcf a <| left_mem_Ico.mpr hab).mono Ioo_subset_Ico_self).tendsto
  · rw [← hga, ← nhdsWithin_Ioo_eq_nhdsGT hab]
    exact ((hcg a <| left_mem_Ico.mpr hab).mono Ioo_subset_Ico_self).tendsto

theorem lhopital_zero_left_on_Ioo (hab : a < b) (hdf : DifferentiableOn ℝ f (Ioo a b))
    (hg' : ∀ x ∈ Ioo a b, (deriv g) x ≠ 0) (hfb : Tendsto f (𝓝[<] b) (𝓝 0))
    (hgb : Tendsto g (𝓝[<] b) (𝓝 0))
    (hdiv : Tendsto (fun x : {x : ℝ // IsUnit (deriv g x)} ↦ deriv f x /ₚ x.property.unit)
      (comap Subtype.val (𝓝[<] b)) l) :
    Tendsto (fun x : {x : ℝ // IsUnit (g x)} ↦ f x /ₚ x.property.unit)
      (comap Subtype.val (𝓝[<] b)) l := by
  have hdf : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x := fun x hx =>
    (hdf x hx).differentiableAt (Ioo_mem_nhds hx.1 hx.2)
  have hdg : ∀ x ∈ Ioo a b, DifferentiableAt ℝ g x := fun x hx =>
    by_contradiction fun h => hg' x hx (deriv_zero_of_not_differentiableAt h)
  exact HasDerivAt.lhopital_zero_left_on_Ioo hab (fun x hx => (hdf x hx).hasDerivAt)
    (fun x hx => (hdg x hx).hasDerivAt) hg' hfb hgb hdiv

theorem lhopital_zero_atTop_on_Ioi (hdf : DifferentiableOn ℝ f (Ioi a))
    (hg' : ∀ x ∈ Ioi a, (deriv g) x ≠ 0) (hftop : Tendsto f atTop (𝓝 0))
    (hgtop : Tendsto g atTop (𝓝 0))
    (hdiv : Tendsto (fun x : {x : ℝ // IsUnit (deriv g x)} ↦ deriv f x /ₚ x.property.unit)
      (comap Subtype.val atTop) l) :
    Tendsto (fun x : {x : ℝ // IsUnit (g x)} ↦ f x /ₚ x.property.unit)
      (comap Subtype.val atTop) l := by
  have hdf : ∀ x ∈ Ioi a, DifferentiableAt ℝ f x := fun x hx =>
    (hdf x hx).differentiableAt (Ioi_mem_nhds hx)
  have hdg : ∀ x ∈ Ioi a, DifferentiableAt ℝ g x := fun x hx =>
    by_contradiction fun h => hg' x hx (deriv_zero_of_not_differentiableAt h)
  exact HasDerivAt.lhopital_zero_atTop_on_Ioi (fun x hx => (hdf x hx).hasDerivAt)
    (fun x hx => (hdg x hx).hasDerivAt) hg' hftop hgtop hdiv

theorem lhopital_zero_atBot_on_Iio (hdf : DifferentiableOn ℝ f (Iio a))
    (hg' : ∀ x ∈ Iio a, (deriv g) x ≠ 0) (hfbot : Tendsto f atBot (𝓝 0))
    (hgbot : Tendsto g atBot (𝓝 0))
    (hdiv : Tendsto (fun x : {x : ℝ // IsUnit (deriv g x)} ↦ deriv f x /ₚ x.property.unit)
      (comap Subtype.val atBot) l) :
    Tendsto (fun x : {x : ℝ // IsUnit (g x)} ↦ f x /ₚ x.property.unit)
      (comap Subtype.val atBot) l := by
  have hdf : ∀ x ∈ Iio a, DifferentiableAt ℝ f x := fun x hx =>
    (hdf x hx).differentiableAt (Iio_mem_nhds hx)
  have hdg : ∀ x ∈ Iio a, DifferentiableAt ℝ g x := fun x hx =>
    by_contradiction fun h => hg' x hx (deriv_zero_of_not_differentiableAt h)
  exact HasDerivAt.lhopital_zero_atBot_on_Iio (fun x hx => (hdf x hx).hasDerivAt)
    (fun x hx => (hdg x hx).hasDerivAt) hg' hfbot hgbot hdiv

end deriv

/-!
## Generic versions

The following statements no longer any explicit interval, as they only require
conditions holding eventually.
-/


namespace HasDerivAt

/-- L'Hôpital's rule for approaching a real from the right, `HasDerivAt` version -/
theorem lhopital_zero_nhdsGT (hff' : ∀ᶠ x in 𝓝[>] a, HasDerivAt f (f' x) x)
    (hgg' : ∀ᶠ x in 𝓝[>] a, HasDerivAt g (g' x) x) (hg' : ∀ᶠ x in 𝓝[>] a, g' x ≠ 0)
    (hfa : Tendsto f (𝓝[>] a) (𝓝 0)) (hga : Tendsto g (𝓝[>] a) (𝓝 0))
    (hdiv : Tendsto (fun x : {x : ℝ // IsUnit (g' x)} ↦ f' x /ₚ x.property.unit)
      (comap Subtype.val (𝓝[>] a)) l) :
    Tendsto (fun x : {x : ℝ // IsUnit (g x)} ↦ f x /ₚ x.property.unit)
      (comap Subtype.val (𝓝[>] a)) l := by
  rw [eventually_iff_exists_mem] at *
  rcases hff' with ⟨s₁, hs₁, hff'⟩
  rcases hgg' with ⟨s₂, hs₂, hgg'⟩
  rcases hg' with ⟨s₃, hs₃, hg'⟩
  let s := s₁ ∩ s₂ ∩ s₃
  have hs : s ∈ 𝓝[>] a := inter_mem (inter_mem hs₁ hs₂) hs₃
  rw [mem_nhdsGT_iff_exists_Ioo_subset] at hs
  rcases hs with ⟨u, hau, hu⟩
  refine lhopital_zero_right_on_Ioo hau ?_ ?_ ?_ hfa hga hdiv <;> grind

/-- L'Hôpital's rule for approaching a real from the left, `HasDerivAt` version -/
theorem lhopital_zero_nhdsLT (hff' : ∀ᶠ x in 𝓝[<] a, HasDerivAt f (f' x) x)
    (hgg' : ∀ᶠ x in 𝓝[<] a, HasDerivAt g (g' x) x) (hg' : ∀ᶠ x in 𝓝[<] a, g' x ≠ 0)
    (hfa : Tendsto f (𝓝[<] a) (𝓝 0)) (hga : Tendsto g (𝓝[<] a) (𝓝 0))
    (hdiv : Tendsto (fun x : {x : ℝ // IsUnit (g' x)} ↦ f' x /ₚ x.property.unit)
      (comap Subtype.val (𝓝[<] a)) l) :
    Tendsto (fun x : {x : ℝ // IsUnit (g x)} ↦ f x /ₚ x.property.unit)
      (comap Subtype.val (𝓝[<] a)) l := by
  rw [eventually_iff_exists_mem] at *
  rcases hff' with ⟨s₁, hs₁, hff'⟩
  rcases hgg' with ⟨s₂, hs₂, hgg'⟩
  rcases hg' with ⟨s₃, hs₃, hg'⟩
  let s := s₁ ∩ s₂ ∩ s₃
  have hs : s ∈ 𝓝[<] a := inter_mem (inter_mem hs₁ hs₂) hs₃
  rw [mem_nhdsLT_iff_exists_Ioo_subset] at hs
  rcases hs with ⟨l, hal, hl⟩
  refine lhopital_zero_left_on_Ioo hal ?_ ?_ ?_ hfa hga hdiv <;> grind

/-- L'Hôpital's rule for approaching a real, `HasDerivAt` version. This
  does not require anything about the situation at `a` -/
theorem lhopital_zero_nhdsNE (hff' : ∀ᶠ x in 𝓝[≠] a, HasDerivAt f (f' x) x)
    (hgg' : ∀ᶠ x in 𝓝[≠] a, HasDerivAt g (g' x) x) (hg' : ∀ᶠ x in 𝓝[≠] a, g' x ≠ 0)
    (hfa : Tendsto f (𝓝[≠] a) (𝓝 0)) (hga : Tendsto g (𝓝[≠] a) (𝓝 0))
    (hdiv : Tendsto (fun x : {x : ℝ // IsUnit (g' x)} ↦ f' x /ₚ x.property.unit)
      (comap Subtype.val (𝓝[≠] a)) l) :
    Tendsto (fun x : {x : ℝ // IsUnit (g x)} ↦ f x /ₚ x.property.unit)
      (comap Subtype.val (𝓝[≠] a)) l := by
  simp only [← Iio_union_Ioi, nhdsWithin_union, comap_sup, tendsto_sup, eventually_sup] at *
  exact ⟨lhopital_zero_nhdsLT hff'.1 hgg'.1 hg'.1 hfa.1 hga.1 hdiv.1,
    lhopital_zero_nhdsGT hff'.2 hgg'.2 hg'.2 hfa.2 hga.2 hdiv.2⟩

/-- L'Hôpital's rule for approaching a real from within a convex set, `HasDerivWithinAt` version.
  This does not require anything about the situation at `a` -/
theorem _root_.HasDerivWithinAt.lhopital_zero_nhdsWithin_convex {s : Set ℝ} (hs : Convex ℝ s)
    (hff' : ∀ᶠ x in 𝓝[s \ {a}] a, HasDerivWithinAt f (f' x) (s \ {a}) x)
    (hgg' : ∀ᶠ x in 𝓝[s \ {a}] a, HasDerivWithinAt g (g' x) (s \ {a}) x)
    (hg' : ∀ᶠ x in 𝓝[s \ {a}] a, g' x ≠ 0)
    (hfa : Tendsto f (𝓝[s \ {a}] a) (𝓝 0)) (hga : Tendsto g (𝓝[s \ {a}] a) (𝓝 0))
    (hdiv : Tendsto (fun x : {x : ℝ // IsUnit (g' x)} ↦ f' x /ₚ x.property.unit)
      (comap Subtype.val (𝓝[s \ {a}] a)) l) :
    Tendsto (fun x : {x : ℝ // IsUnit (g x)} ↦ f x /ₚ x.property.unit)
      (comap Subtype.val (𝓝[s \ {a}] a)) l := by
  by_cases has : (𝓝[s \ {a}] a).NeBot
  swap
  · simp [not_neBot.mp has]
  replace has := closure_mono sdiff_subset (mem_closure_iff_nhdsWithin_neBot.2 has)
  have h := hs.sdiff_singleton_eventually_mem_nhds a
  replace hff' := h.mp <| hff'.mono fun _ h ↦ h.hasDerivAt
  replace hgg' := h.mp <| hgg'.mono fun _ h ↦ h.hasDerivAt
  rcases eq_empty_or_nonempty (s ∩ Iio a) with hs_Iio | hs_Iio
    <;> rcases eq_empty_or_nonempty (s ∩ Ioi a) with hs_Ioi | hs_Ioi
  · simp [sdiff_eq, ← Iio_union_Ioi, inter_union_distrib_left, hs_Iio, hs_Ioi]
  · simp_rw [hs.nhdsWithin_sdiff_eq_nhdsGT has hs_Iio hs_Ioi] at *
    exact lhopital_zero_nhdsGT hff' hgg' hg' hfa hga hdiv
  · simp_rw [hs.nhdsWithin_sdiff_eq_nhdsLT has hs_Iio hs_Ioi] at *
    exact lhopital_zero_nhdsLT hff' hgg' hg' hfa hga hdiv
  · simp_rw [hs.nhdsWithin_sdiff_eq_nhdsNE has hs_Iio hs_Ioi] at *
    exact lhopital_zero_nhdsNE hff' hgg' hg' hfa hga hdiv

/-- **L'Hôpital's rule** for approaching a real, `HasDerivAt` version -/
theorem lhopital_zero_nhds (hff' : ∀ᶠ x in 𝓝 a, HasDerivAt f (f' x) x)
    (hgg' : ∀ᶠ x in 𝓝 a, HasDerivAt g (g' x) x) (hg' : ∀ᶠ x in 𝓝 a, g' x ≠ 0)
    (hfa : Tendsto f (𝓝 a) (𝓝 0)) (hga : Tendsto g (𝓝 a) (𝓝 0))
    (hdiv : Tendsto (fun x : {x : ℝ // IsUnit (g' x)} ↦ f' x /ₚ x.property.unit)
      (comap Subtype.val (𝓝 a)) l) :
    Tendsto (fun x : {x : ℝ // IsUnit (g x)} ↦ f x /ₚ x.property.unit)
      (comap Subtype.val (𝓝[≠] a)) l := by
  apply @lhopital_zero_nhdsNE _ _ _ f' _ g' <;>
    (first | apply eventually_nhdsWithin_of_eventually_nhds |
      apply tendsto_nhdsWithin_of_tendsto_nhds |
      exact hdiv.mono_left (comap_mono nhdsWithin_le_nhds)) <;> assumption

/-- L'Hôpital's rule for approaching +∞, `HasDerivAt` version -/
theorem lhopital_zero_atTop (hff' : ∀ᶠ x in atTop, HasDerivAt f (f' x) x)
    (hgg' : ∀ᶠ x in atTop, HasDerivAt g (g' x) x) (hg' : ∀ᶠ x in atTop, g' x ≠ 0)
    (hftop : Tendsto f atTop (𝓝 0)) (hgtop : Tendsto g atTop (𝓝 0))
    (hdiv : Tendsto (fun x : {x : ℝ // IsUnit (g' x)} ↦ f' x /ₚ x.property.unit)
      (comap Subtype.val atTop) l) :
    Tendsto (fun x : {x : ℝ // IsUnit (g x)} ↦ f x /ₚ x.property.unit)
      (comap Subtype.val atTop) l := by
  rw [eventually_iff_exists_mem] at *
  rcases hff' with ⟨s₁, hs₁, hff'⟩
  rcases hgg' with ⟨s₂, hs₂, hgg'⟩
  rcases hg' with ⟨s₃, hs₃, hg'⟩
  let s := s₁ ∩ s₂ ∩ s₃
  have hs : s ∈ atTop := inter_mem (inter_mem hs₁ hs₂) hs₃
  rw [mem_atTop_sets] at hs
  rcases hs with ⟨l, hl⟩
  have hl' : Ioi l ⊆ s := fun x hx => hl x (le_of_lt hx)
  refine lhopital_zero_atTop_on_Ioi ?_ ?_ (fun x hx ↦ hg' x (hl' hx).2) hftop hgtop hdiv <;> grind

/-- L'Hôpital's rule for approaching -∞, `HasDerivAt` version -/
theorem lhopital_zero_atBot (hff' : ∀ᶠ x in atBot, HasDerivAt f (f' x) x)
    (hgg' : ∀ᶠ x in atBot, HasDerivAt g (g' x) x) (hg' : ∀ᶠ x in atBot, g' x ≠ 0)
    (hfbot : Tendsto f atBot (𝓝 0)) (hgbot : Tendsto g atBot (𝓝 0))
    (hdiv : Tendsto (fun x : {x : ℝ // IsUnit (g' x)} ↦ f' x /ₚ x.property.unit)
      (comap Subtype.val atBot) l) :
    Tendsto (fun x : {x : ℝ // IsUnit (g x)} ↦ f x /ₚ x.property.unit)
      (comap Subtype.val atBot) l := by
  rw [eventually_iff_exists_mem] at *
  rcases hff' with ⟨s₁, hs₁, hff'⟩
  rcases hgg' with ⟨s₂, hs₂, hgg'⟩
  rcases hg' with ⟨s₃, hs₃, hg'⟩
  let s := s₁ ∩ s₂ ∩ s₃
  have hs : s ∈ atBot := inter_mem (inter_mem hs₁ hs₂) hs₃
  rw [mem_atBot_sets] at hs
  rcases hs with ⟨l, hl⟩
  have hl' : Iio l ⊆ s := fun x hx => hl x (le_of_lt hx)
  refine lhopital_zero_atBot_on_Iio ?_ ?_ (fun x hx ↦ hg' x (hl' hx).2) hfbot hgbot hdiv <;> grind

end HasDerivAt

namespace derivWithin

/-- **L'Hôpital's rule** for approaching a real from within a convex set, `derivWithin` version -/
theorem lhopital_zero_nhdsWithin_convex {s : Set ℝ} (hs : Convex ℝ s)
    (hdf : ∀ᶠ x in 𝓝[s \ {a}] a, DifferentiableWithinAt ℝ f (s \ {a}) x)
    (hg' : ∀ᶠ x in 𝓝[s \ {a}] a, derivWithin g (s \ {a}) x ≠ 0)
    (hfa : Tendsto f (𝓝[s \ {a}] a) (𝓝 0)) (hga : Tendsto g (𝓝[s \ {a}] a) (𝓝 0))
    (hdiv : Tendsto (fun x : {x : ℝ // IsUnit (derivWithin g (s \ {a}) x)} ↦
      derivWithin f (s \ {a}) x /ₚ x.property.unit)
      (comap Subtype.val (𝓝[s \ {a}] a)) l) :
    Tendsto (fun x : {x : ℝ // IsUnit (g x)} ↦ f x /ₚ x.property.unit)
      (comap Subtype.val (𝓝[s \ {a}] a)) l := by
  have hdg : ∀ᶠ x in 𝓝[s \ {a}] a, DifferentiableWithinAt ℝ g (s \ {a}) x :=
    hg'.mp (Eventually.of_forall fun _ hg' =>
      by_contradiction fun h => hg' (derivWithin_zero_of_not_differentiableWithinAt h))
  have hdf' : ∀ᶠ x in 𝓝[s \ {a}] a, HasDerivWithinAt f (derivWithin f (s \ {a}) x) (s \ {a}) x :=
    hdf.mp (Eventually.of_forall fun _ h ↦ h.hasDerivWithinAt)
  have hdg' : ∀ᶠ x in 𝓝[s \ {a}] a, HasDerivWithinAt g (derivWithin g (s \ {a}) x) (s \ {a}) x :=
    hdg.mp (Eventually.of_forall fun _ h => h.hasDerivWithinAt)
  exact HasDerivWithinAt.lhopital_zero_nhdsWithin_convex hs hdf' hdg' hg' hfa hga hdiv

end derivWithin

namespace deriv

/-- **L'Hôpital's rule** for approaching a real from within a convex set, `deriv` version -/
theorem lhopital_zero_nhdsWithin_convex {s : Set ℝ} (hs : Convex ℝ s)
    (hdf : ∀ᶠ x in 𝓝[s \ {a}] a, DifferentiableAt ℝ f x) (hg' : ∀ᶠ x in 𝓝[s \ {a}] a, deriv g x ≠ 0)
    (hfa : Tendsto f (𝓝[s \ {a}] a) (𝓝 0)) (hga : Tendsto g (𝓝[s \ {a}] a) (𝓝 0))
    (hdiv : Tendsto (fun x : {x : ℝ // IsUnit (deriv g x)} ↦ deriv f x /ₚ x.property.unit)
      (comap Subtype.val (𝓝[s \ {a}] a)) l) :
    Tendsto (fun x : {x : ℝ // IsUnit (g x)} ↦ f x /ₚ x.property.unit)
      (comap Subtype.val (𝓝[s \ {a}] a)) l := by
  refine derivWithin.lhopital_zero_nhdsWithin_convex hs
    (hdf.mono fun _ h ↦ h.differentiableWithinAt) ?_ hfa hga ?_
  · filter_upwards [hg', hs.sdiff_singleton_eventually_mem_nhds a] with x hg hx
    simpa only [derivWithin_of_mem_nhds hx] using hg
  · apply (tendsto_divp_iff (f := fun x ↦ derivWithin f (s \ {a}) x id)
      (g := fun x ↦ derivWithin g (s \ {a}) x id)).mpr
    intro t ht
    have hq := (tendsto_divp_iff (f := fun x ↦ deriv f x id)
      (g := fun x ↦ deriv g x id)).mp hdiv t ht
    filter_upwards [hs.sdiff_singleton_eventually_mem_nhds a, hq]
      with x hx hq
    simpa only [derivWithin_of_mem_nhds hx] using hq

/-- **L'Hôpital's rule** for approaching a real from the right, `deriv` version -/
theorem lhopital_zero_nhdsGT (hdf : ∀ᶠ x in 𝓝[>] a, DifferentiableAt ℝ f x)
    (hg' : ∀ᶠ x in 𝓝[>] a, deriv g x ≠ 0) (hfa : Tendsto f (𝓝[>] a) (𝓝 0))
    (hga : Tendsto g (𝓝[>] a) (𝓝 0))
    (hdiv : Tendsto (fun x : {x : ℝ // IsUnit (deriv g x)} ↦ deriv f x /ₚ x.property.unit)
      (comap Subtype.val (𝓝[>] a)) l) :
    Tendsto (fun x : {x : ℝ // IsUnit (g x)} ↦ f x /ₚ x.property.unit)
      (comap Subtype.val (𝓝[>] a)) l := by
  rw [← Ici_sdiff_left] at *
  exact lhopital_zero_nhdsWithin_convex (convex_Ici a) hdf hg' hfa hga hdiv

/-- **L'Hôpital's rule** for approaching a real from the left, `deriv` version -/
theorem lhopital_zero_nhdsLT (hdf : ∀ᶠ x in 𝓝[<] a, DifferentiableAt ℝ f x)
    (hg' : ∀ᶠ x in 𝓝[<] a, deriv g x ≠ 0) (hfa : Tendsto f (𝓝[<] a) (𝓝 0))
    (hga : Tendsto g (𝓝[<] a) (𝓝 0))
    (hdiv : Tendsto (fun x : {x : ℝ // IsUnit (deriv g x)} ↦ deriv f x /ₚ x.property.unit)
      (comap Subtype.val (𝓝[<] a)) l) :
    Tendsto (fun x : {x : ℝ // IsUnit (g x)} ↦ f x /ₚ x.property.unit)
      (comap Subtype.val (𝓝[<] a)) l := by
  rw [← Iic_sdiff_right] at *
  exact lhopital_zero_nhdsWithin_convex (convex_Iic a) hdf hg' hfa hga hdiv

/-- **L'Hôpital's rule** for approaching a real, `deriv` version. This
  does not require anything about the situation at `a` -/
theorem lhopital_zero_nhdsNE (hdf : ∀ᶠ x in 𝓝[≠] a, DifferentiableAt ℝ f x)
    (hg' : ∀ᶠ x in 𝓝[≠] a, deriv g x ≠ 0) (hfa : Tendsto f (𝓝[≠] a) (𝓝 0))
    (hga : Tendsto g (𝓝[≠] a) (𝓝 0))
    (hdiv : Tendsto (fun x : {x : ℝ // IsUnit (deriv g x)} ↦ deriv f x /ₚ x.property.unit)
      (comap Subtype.val (𝓝[≠] a)) l) :
    Tendsto (fun x : {x : ℝ // IsUnit (g x)} ↦ f x /ₚ x.property.unit)
      (comap Subtype.val (𝓝[≠] a)) l := by
  rw [compl_eq_univ_sdiff] at *
  exact lhopital_zero_nhdsWithin_convex convex_univ hdf hg' hfa hga hdiv

/-- **L'Hôpital's rule** for approaching a real, `deriv` version -/
theorem lhopital_zero_nhds (hdf : ∀ᶠ x in 𝓝 a, DifferentiableAt ℝ f x)
    (hg' : ∀ᶠ x in 𝓝 a, deriv g x ≠ 0) (hfa : Tendsto f (𝓝 a) (𝓝 0)) (hga : Tendsto g (𝓝 a) (𝓝 0))
    (hdiv : Tendsto (fun x : {x : ℝ // IsUnit (deriv g x)} ↦ deriv f x /ₚ x.property.unit)
      (comap Subtype.val (𝓝 a)) l) :
    Tendsto (fun x : {x : ℝ // IsUnit (g x)} ↦ f x /ₚ x.property.unit)
      (comap Subtype.val (𝓝[≠] a)) l := by
  apply lhopital_zero_nhdsNE <;>
    (first | apply eventually_nhdsWithin_of_eventually_nhds |
      apply tendsto_nhdsWithin_of_tendsto_nhds |
      exact hdiv.mono_left (comap_mono nhdsWithin_le_nhds)) <;> assumption

/-- **L'Hôpital's rule** for approaching +∞, `deriv` version -/
theorem lhopital_zero_atTop (hdf : ∀ᶠ x : ℝ in atTop, DifferentiableAt ℝ f x)
    (hg' : ∀ᶠ x : ℝ in atTop, deriv g x ≠ 0) (hftop : Tendsto f atTop (𝓝 0))
    (hgtop : Tendsto g atTop (𝓝 0))
    (hdiv : Tendsto (fun x : {x : ℝ // IsUnit (deriv g x)} ↦ deriv f x /ₚ x.property.unit)
      (comap Subtype.val atTop) l) :
    Tendsto (fun x : {x : ℝ // IsUnit (g x)} ↦ f x /ₚ x.property.unit)
      (comap Subtype.val atTop) l := by
  have hdg : ∀ᶠ x in atTop, DifferentiableAt ℝ g x := hg'.mp
    (Eventually.of_forall fun _ hg' =>
      by_contradiction fun h => hg' (deriv_zero_of_not_differentiableAt h))
  have hdf' : ∀ᶠ x in atTop, HasDerivAt f (deriv f x) x :=
    hdf.mono fun _ => DifferentiableAt.hasDerivAt
  have hdg' : ∀ᶠ x in atTop, HasDerivAt g (deriv g x) x :=
    hdg.mono fun _ => DifferentiableAt.hasDerivAt
  exact HasDerivAt.lhopital_zero_atTop hdf' hdg' hg' hftop hgtop hdiv

/-- **L'Hôpital's rule** for approaching -∞, `deriv` version -/
theorem lhopital_zero_atBot (hdf : ∀ᶠ x : ℝ in atBot, DifferentiableAt ℝ f x)
    (hg' : ∀ᶠ x : ℝ in atBot, deriv g x ≠ 0) (hfbot : Tendsto f atBot (𝓝 0))
    (hgbot : Tendsto g atBot (𝓝 0))
    (hdiv : Tendsto (fun x : {x : ℝ // IsUnit (deriv g x)} ↦ deriv f x /ₚ x.property.unit)
      (comap Subtype.val atBot) l) :
    Tendsto (fun x : {x : ℝ // IsUnit (g x)} ↦ f x /ₚ x.property.unit)
      (comap Subtype.val atBot) l := by
  have hdg : ∀ᶠ x in atBot, DifferentiableAt ℝ g x :=
    hg'.mono fun _ hg' => by_contradiction fun h => hg' (deriv_zero_of_not_differentiableAt h)
  have hdf' : ∀ᶠ x in atBot, HasDerivAt f (deriv f x) x :=
    hdf.mono fun _ => DifferentiableAt.hasDerivAt
  have hdg' : ∀ᶠ x in atBot, HasDerivAt g (deriv g x) x :=
    hdg.mono fun _ => DifferentiableAt.hasDerivAt
  exact HasDerivAt.lhopital_zero_atBot hdf' hdg' hg' hfbot hgbot hdiv

end deriv
