/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.MeasureTheory.Covering.OneDim
public import Mathlib.Order.Monotone.Extension

/-!
# Differentiability of monotone functions

We show that a monotone function `f : ℝ → ℝ` is differentiable almost everywhere, in
`Monotone.ae_differentiableAt`. (We also give a version for a function monotone on a set, in
`MonotoneOn.ae_differentiableWithinAt`.)

If the function `f` is continuous, this follows directly from general differentiation of measure
theorems. Let `μ` be the Stieltjes measure associated to `f`. Then, almost everywhere,
`μ [x, y] / Leb [x, y]` (resp. `μ [y, x] / Leb [y, x]`) converges to the Radon-Nikodym derivative
of `μ` with respect to Lebesgue when `y` tends to `x` in `(x, +∞)` (resp. `(-∞, x)`), by
`VitaliFamily.ae_tendsto_rnDeriv`. As `μ [x, y] = f y - f x` and `Leb [x, y] = y - x`, this
gives differentiability right away.

When `f` is only monotone, the same argument works up to small adjustments, as the associated
Stieltjes measure satisfies `μ [x, y] = f (y^+) - f (x^-)` (the right and left limits of `f` at `y`
and `x` respectively). One argues that `f (x^-) = f x` almost everywhere (in fact away from a
countable set), and moreover `f ((y - (y-x)^2)^+) ≤ f y ≤ f (y^+)`. This is enough to deduce the
limit of `(f y - f x) / (y - x)` by a lower and upper approximation argument from the known
behavior of `μ [x, y]`.
-/

public section


open Set Filter Function Metric MeasureTheory MeasureTheory.Measure IsUnifLocDoublingMeasure

open scoped Topology

/-- If `(f y - f x) / (y - x)` converges to a limit as `y` tends to `x`, then the same goes if
`y` is shifted a little bit, i.e., `f (y + (y-x)^2) - f x) / (y - x)` converges to the same limit.
This lemma contains a slightly more general version of this statement (where one considers
convergence along some subfilter, typically `𝓝[<] x` or `𝓝[>] x`) tailored to the application
to almost everywhere differentiability of monotone functions. -/
theorem tendsto_apply_add_mul_sq_div_sub {f : ℝ → ℝ} {x a c d : ℝ} {l : Filter ℝ}
    (hl : l ≤ 𝓝[≠] x)
    (hf : Tendsto (fun y : ↥({x}ᶜ : Set ℝ) ↦
      Checked.div (f y - d) ((y : ℝ) - x) (sub_ne_zero.2 y.property).isUnit)
      (comap (↑) l) (𝓝 a))
    (h' : Tendsto (fun y : ℝ ↦ y + c * (y - x) ^ 2) l l) :
    Tendsto (fun y : ↥({x}ᶜ : Set ℝ) ↦
      Checked.div (f ((y : ℝ) + c * ((y : ℝ) - x) ^ 2) - d) ((y : ℝ) - x)
        (sub_ne_zero.2 y.property).isUnit) (comap (↑) l) (𝓝 a) := by
  let D := ↥({x}ᶜ : Set ℝ)
  let k : Filter D := comap (↑) l
  let φ (y : ℝ) := y + c * (y - x) ^ 2
  have hval : Tendsto (Subtype.val : D → ℝ) k l := tendsto_comap
  have hv := hval.mono_right (hl.trans nhdsWithin_le_nhds)
  have L : Tendsto (fun y : D ↦ Checked.div (φ y - x) ((y : ℝ) - x)
      (sub_ne_zero.2 y.property).isUnit) k (𝓝 1) := by
    have h : Tendsto (fun y : D ↦ 1 + c * ((y : ℝ) - x)) k (𝓝 1) := by
      simpa only [sub_self, mul_zero, add_zero] using ((hv.sub_const x).const_mul c).const_add 1
    refine h.congr' (Eventually.of_forall fun y ↦ ?_)
    dsimp only [φ]
    field [sub_ne_zero.2 y.property]
  have hφ : Tendsto (fun y : D ↦ φ y) k l := h'.comp hval
  have hdom : ∀ᶠ y : D in k, φ y ≠ x := (hφ.mono_right hl).eventually self_mem_nhdsWithin
  let D' := {y : D // φ y ≠ x}
  let i : D' → D := Subtype.val
  let q : D' → D := fun y ↦ ⟨φ y.val, y.property⟩
  have hq : Tendsto q (comap i k) k := tendsto_comap_iff.2 (hφ.comp tendsto_comap)
  have hL : Tendsto ((fun y : D ↦ Checked.div (φ y - x) ((y : ℝ) - x)
      (sub_ne_zero.2 y.property).isUnit) ∘ i) (comap i k) (𝓝 1) := L.comp tendsto_comap
  have hlim := (hf.comp hq).mul hL
  rw [mul_one] at hlim
  have hrange : range i ∈ k := by
    filter_upwards [hdom] with y hy
    exact ⟨⟨y, hy⟩, rfl⟩
  apply (tendsto_comap'_iff hrange).mp
  refine hlim.congr' (Eventually.of_forall fun y ↦ ?_)
  dsimp only [Function.comp_def, q, i, φ]
  field_simp [sub_ne_zero.2 y.val.property, sub_ne_zero.2 y.property]

private theorem comap_nhds_compl_singleton (x : ℝ) :
    comap (Subtype.val : ↥({x}ᶜ : Set ℝ) → ℝ) (𝓝 x) =
      comap (↑) (𝓝[<] x) ⊔ comap (↑) (𝓝[>] x) := by
  have h : comap (Subtype.val : ↥({x}ᶜ : Set ℝ) → ℝ) (𝓝[≠] x) = comap (↑) (𝓝 x) := by
    rw [nhdsWithin, comap_inf, comap_principal]
    have ht : Subtype.val ⁻¹' ({x}ᶜ : Set ℝ) = (univ : Set ↥({x}ᶜ : Set ℝ)) :=
      eq_univ_of_forall fun y ↦ y.property
    rw [ht, principal_univ, inf_top_eq]
  rw [← h, ← nhdsLT_sup_nhdsGT, comap_sup]

private theorem tendsto_add_mul_sq_nhdsWithin_sides (x c : ℝ) :
    Tendsto (fun y ↦ y + c * (y - x) ^ 2) (𝓝[<] x) (𝓝[<] x) ∧
      Tendsto (fun y ↦ y + c * (y - x) ^ 2) (𝓝[>] x) (𝓝[>] x) := by
  have hid : Tendsto (fun y : ℝ ↦ y) (𝓝 x) (𝓝 x) := tendsto_id
  have h : Tendsto (fun y ↦ y + c * (y - x) ^ 2) (𝓝 x) (𝓝 x) := by
    simpa only [sub_self, zero_pow two_ne_zero, mul_zero, add_zero] using
      hid.add (((hid.sub_const x).pow 2).const_mul c)
  have hfac : Tendsto (fun y ↦ 1 + c * (y - x)) (𝓝 x) (𝓝 1) := by
    simpa only [sub_self, mul_zero, add_zero] using ((hid.sub_const x).const_mul c).const_add 1
  have he : ∀ᶠ y in 𝓝 x, 0 < 1 + c * (y - x) := hfac.eventually (Ioi_mem_nhds zero_lt_one)
  constructor
  · apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (h.mono_left nhdsWithin_le_nhds)
    filter_upwards [he.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with y h1 h2
    change y + c * (y - x) ^ 2 < x
    have hy : y < x := h2
    nlinarith only [mul_neg_of_neg_of_pos (sub_neg.2 hy) h1]
  · apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (h.mono_left nhdsWithin_le_nhds)
    filter_upwards [he.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with y h1 h2
    change x < y + c * (y - x) ^ 2
    have hy : x < y := h2
    nlinarith only [mul_pos (sub_pos.2 hy) h1]

/-- A Stieltjes function is almost everywhere differentiable, with derivative equal to the
Radon-Nikodym derivative of the associated Stieltjes measure with respect to Lebesgue. -/
theorem StieltjesFunction.ae_hasDerivAt (f : StieltjesFunction ℝ) :
    ∀ᵐ x, HasDerivAt f (rnDeriv f.measure volume x).toReal x := by
  /- Denote by `μ` the Stieltjes measure associated to `f`.
    The general theorem `VitaliFamily.ae_tendsto_rnDeriv` ensures that `μ [x, y] / (y - x)` tends
    to the Radon-Nikodym derivative as `y` tends to `x` from the right. As `μ [x,y] = f y - f (x^-)`
    and `f (x^-) = f x` almost everywhere, this gives differentiability on the right.
    On the left, `μ [y, x] / (x - y)` again tends to the Radon-Nikodym derivative.
    As `μ [y, x] = f x - f (y^-)`, this is not exactly the right result, so one uses a sandwiching
    argument to deduce the convergence for `(f x - f y) / (x - y)`. -/
  filter_upwards [VitaliFamily.ae_tendsto_rnDeriv (vitaliFamily (volume : Measure ℝ) 1) f.measure,
    rnDeriv_lt_top f.measure volume, f.countable_leftLim_ne.ae_notMem volume] with x hx h'x h''x
  let D := ↥({x}ᶜ : Set ℝ)
  let kR : Filter D := comap (↑) (𝓝[>] x)
  let kL : Filter D := comap (↑) (𝓝[<] x)
  let q (g : ℝ → ℝ) (d : ℝ) (y : D) : ℝ :=
    Checked.div (g y - d) ((y : ℝ) - x) (sub_ne_zero.2 y.property).isUnit
  have hR : Tendsto (Subtype.val : D → ℝ) kR (𝓝[>] x) := tendsto_comap
  have hL : Tendsto (Subtype.val : D → ℝ) kL (𝓝[<] x) := tendsto_comap
  have hright : ∀ᶠ y : D in kR, x < (y : ℝ) := hR.eventually self_mem_nhdsWithin
  have hleft : ∀ᶠ y : D in kL, (y : ℝ) < x := hL.eventually self_mem_nhdsWithin
  let a := (rnDeriv f.measure volume x).toReal
  have L1 : Tendsto (q f (f x)) kR (𝓝 a) := by
    apply Tendsto.congr' _
      ((ENNReal.tendsto_toReal h'x.ne).comp
        (hx.comp (Real.tendsto_Icc_vitaliFamily_right x)) |>.comp hR)
    filter_upwards [hright] with y hxy
    change (ENNReal.div (f.measure (Icc x y)) (volume (Icc x y))).toReal = q f (f x) y
    simp only [StieltjesFunction.measure_Icc, Real.volume_Icc,
      Classical.not_not.1 h''x]
    rw [← ENNReal.ofReal_div_of_pos (sub_pos.2 hxy), ENNReal.toReal_ofReal]
    exact div_nonneg (sub_nonneg.2 (f.mono hxy.le)) (sub_pos.2 hxy).le
  have L2 : Tendsto (q (leftLim f) (f x)) kL (𝓝 a) := by
    apply Tendsto.congr' _
      ((ENNReal.tendsto_toReal h'x.ne).comp
        (hx.comp (Real.tendsto_Icc_vitaliFamily_left x)) |>.comp hL)
    filter_upwards [hleft] with y hxy
    change (ENNReal.div (f.measure (Icc (y : ℝ) x)) (volume (Icc (y : ℝ) x))).toReal =
      q (leftLim f) (f x) y
    simp only [q, StieltjesFunction.measure_Icc, Real.volume_Icc]
    rw [← ENNReal.ofReal_div_of_pos (sub_pos.2 hxy), ENNReal.toReal_ofReal
      (div_nonneg (sub_nonneg.2 (f.mono.leftLim_le hxy.le)) (sub_pos.2 hxy).le)]
    field_simp [(sub_pos.2 hxy).ne', (sub_neg.2 hxy).ne]
    ring
  have L3 : Tendsto (q (fun y ↦ leftLim f (y + 1 * (y - x) ^ 2)) (f x)) kL (𝓝 a) :=
    tendsto_apply_add_mul_sq_div_sub (nhdsLT_le_nhdsNE x) L2
      (tendsto_add_mul_sq_nhdsWithin_sides x 1).1
  have L4 : Tendsto (q f (f x)) kL (𝓝 a) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' L3 L2
    · filter_upwards [hleft] with y hy
      dsimp [q]
      refine div_le_div_of_nonpos_of_le (sub_nonpos.2 hy.le) ((sub_le_sub_iff_right _).2 ?_)
      apply f.mono.le_leftLim
      have hsq : 0 < ((y : ℝ) - x) ^ 2 := sq_pos_of_neg (sub_neg.2 hy)
      linarith
    · filter_upwards [hleft] with y hy
      dsimp [q]
      refine div_le_div_of_nonpos_of_le (sub_nonpos.2 hy.le) ((sub_le_sub_iff_right _).2 ?_)
      exact f.mono.leftLim_le le_rfl
  rw [hasDerivAt_iff_tendsto_slope, slope_fun_def_field, comap_nhds_compl_singleton, tendsto_sup]
  exact ⟨L4, L1⟩

/-- A monotone function is almost everywhere differentiable, with derivative equal to the
Radon-Nikodym derivative of the associated Stieltjes measure with respect to Lebesgue. -/
theorem Monotone.ae_hasDerivAt {f : ℝ → ℝ} (hf : Monotone f) :
    ∀ᵐ x, HasDerivAt f (rnDeriv hf.stieltjesFunction.measure volume x).toReal x := by
  /- We already know that the Stieltjes function associated to `f` (i.e., `g : x ↦ f (x^+)`) is
    differentiable almost everywhere. We reduce to this statement by sandwiching values of `f` with
    values of `g`, by shifting with `(y - x)^2` (which has no influence on the relevant
    scale `y - x`.) -/
  filter_upwards [hf.stieltjesFunction.ae_hasDerivAt,
    hf.countable_not_continuousAt.ae_notMem volume] with x hx h'x
  have A : hf.stieltjesFunction x = f x := by
    rw [Classical.not_not, hf.continuousAt_iff_leftLim_eq_rightLim] at h'x
    apply le_antisymm _ (hf.le_rightLim (le_refl _))
    rw [← h'x]
    exact hf.leftLim_le (le_refl _)
  rw [hasDerivAt_iff_tendsto_slope, slope_fun_def_field, comap_nhds_compl_singleton, tendsto_sup,
    A] at hx
  let D := ↥({x}ᶜ : Set ℝ)
  let kR : Filter D := comap (↑) (𝓝[>] x)
  let kL : Filter D := comap (↑) (𝓝[<] x)
  let q (g : ℝ → ℝ) (y : D) : ℝ :=
    Checked.div (g y - f x) ((y : ℝ) - x) (sub_ne_zero.2 y.property).isUnit
  let g : ℝ → ℝ := hf.stieltjesFunction
  let a := (rnDeriv hf.stieltjesFunction.measure volume x).toReal
  have hR : Tendsto (Subtype.val : D → ℝ) kR (𝓝[>] x) := tendsto_comap
  have hL : Tendsto (Subtype.val : D → ℝ) kL (𝓝[<] x) := tendsto_comap
  have hright : ∀ᶠ y : D in kR, x < (y : ℝ) := hR.eventually self_mem_nhdsWithin
  have hleft : ∀ᶠ y : D in kL, (y : ℝ) < x := hL.eventually self_mem_nhdsWithin
  have L1 : Tendsto (q f) kR (𝓝 a) := by
    have hshift : Tendsto (q (fun y ↦ g (y + (-1) * (y - x) ^ 2))) kR (𝓝 a) :=
      tendsto_apply_add_mul_sq_div_sub (nhdsGT_le_nhdsNE x) hx.2
        (tendsto_add_mul_sq_nhdsWithin_sides x (-1)).2
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hshift hx.2
    · filter_upwards [hright] with y hy
      dsimp [q]
      refine div_le_div_of_nonneg_right ?_ (sub_nonneg.2 hy.le)
      apply sub_le_sub_right
      have hsq : 0 < ((y : ℝ) - x) ^ 2 := sq_pos_of_pos (sub_pos.2 hy)
      exact hf.rightLim_le (by linarith)
    · filter_upwards [hright] with y hy
      dsimp [q]
      exact div_le_div_of_nonneg_right (sub_le_sub_right (hf.le_rightLim le_rfl) _)
        (sub_nonneg.2 hy.le)
  have L2 : Tendsto (q f) kL (𝓝 a) := by
    have hshift : Tendsto (q (fun y ↦ g (y + (-1) * (y - x) ^ 2))) kL (𝓝 a) :=
      tendsto_apply_add_mul_sq_div_sub (nhdsLT_le_nhdsNE x) hx.1
        (tendsto_add_mul_sq_nhdsWithin_sides x (-1)).1
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hx.1 hshift
    · filter_upwards [hleft] with y hy
      dsimp [q]
      exact div_le_div_of_nonpos_of_le (sub_nonpos.2 hy.le)
        (sub_le_sub_right (hf.le_rightLim le_rfl) _)
    · filter_upwards [hleft] with y hy
      dsimp [q]
      refine div_le_div_of_nonpos_of_le (sub_nonpos.2 hy.le) (sub_le_sub_right ?_ _)
      have hsq : 0 < ((y : ℝ) - x) ^ 2 := sq_pos_of_neg (sub_neg.2 hy)
      exact hf.rightLim_le (by linarith)
  rw [hasDerivAt_iff_tendsto_slope, slope_fun_def_field, comap_nhds_compl_singleton, tendsto_sup]
  exact ⟨L2, L1⟩

/-- A monotone real function is differentiable Lebesgue-almost everywhere. -/
theorem Monotone.ae_differentiableAt {f : ℝ → ℝ} (hf : Monotone f) :
    ∀ᵐ x, DifferentiableAt ℝ f x := by
  filter_upwards [hf.ae_hasDerivAt] with x hx using hx.differentiableAt

/-- A real function which is monotone on a set is differentiable Lebesgue-almost everywhere on
this set. This version does not assume that `s` is measurable. For a formulation with
`volume.restrict s` assuming that `s` is measurable, see `MonotoneOn.ae_differentiableWithinAt`.
-/
theorem MonotoneOn.ae_differentiableWithinAt_of_mem {f : ℝ → ℝ} {s : Set ℝ} (hf : MonotoneOn f s) :
    ∀ᵐ x, x ∈ s → DifferentiableWithinAt ℝ f s x := by
  /- We use a global monotone extension of `f`, and argue that this extension is differentiable
    almost everywhere. Such an extension need not exist (think of `1/x` on `(0, +∞)`), but it exists
    if one restricts first the function to a compact interval `[a, b]`. -/
  apply ae_of_mem_of_ae_of_mem_inter_Ioo
  intro a b as bs _
  obtain ⟨g, hg, gf⟩ : ∃ g : ℝ → ℝ, Monotone g ∧ EqOn f g (s ∩ Icc a b) :=
    (hf.mono inter_subset_left).exists_monotone_extension
      (hf.map_bddBelow inter_subset_left ⟨a, fun x hx => hx.2.1, as⟩)
      (hf.map_bddAbove inter_subset_left ⟨b, fun x hx => hx.2.2, bs⟩)
  filter_upwards [hg.ae_differentiableAt] with x hx
  intro h'x
  apply hx.differentiableWithinAt.congr_of_eventuallyEq _ (gf ⟨h'x.1, h'x.2.1.le, h'x.2.2.le⟩)
  have : Ioo a b ∈ 𝓝[s] x := nhdsWithin_le_nhds (Ioo_mem_nhds h'x.2.1 h'x.2.2)
  filter_upwards [self_mem_nhdsWithin, this] with y hy h'y
  exact gf ⟨hy, h'y.1.le, h'y.2.le⟩

/-- A real function which is monotone on a set is differentiable Lebesgue-almost everywhere on
this set. This version assumes that `s` is measurable and uses `volume.restrict s`.
For a formulation without measurability assumption,
see `MonotoneOn.ae_differentiableWithinAt_of_mem`. -/
theorem MonotoneOn.ae_differentiableWithinAt {f : ℝ → ℝ} {s : Set ℝ} (hf : MonotoneOn f s)
    (hs : MeasurableSet s) : ∀ᵐ x ∂volume.restrict s, DifferentiableWithinAt ℝ f s x := by
  rw [ae_restrict_iff' hs]
  exact hf.ae_differentiableWithinAt_of_mem
