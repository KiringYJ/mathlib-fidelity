/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.LogDeriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Tactic.AdaptationNote

/-!
# Derivative and series expansion of real logarithm

In this file we prove that `Real.log` is infinitely smooth at all nonzero `x : ℝ`. We also prove
that the series `∑' n : ℕ, x ^ (n + 1) / (n + 1)` converges to `(-Real.log (1 - x))` for all
`x : ℝ`, `|x| < 1`.

## Tags

logarithm, derivative
-/

public section


open Filter Finset Set

open scoped Topology ContDiff

namespace Real

variable {x : ℝ}

theorem hasStrictDerivAt_log_of_pos (hx : 0 < x) : HasStrictDerivAt log x⁻¹ x := by
  have : HasStrictDerivAt log (exp <| log x)⁻¹ x :=
    (hasStrictDerivAt_exp <| log x).of_local_left_inverse (continuousAt_log hx.ne')
        (ne_of_gt <| exp_pos _) <|
      Eventually.mono (lt_mem_nhds hx) @exp_log
  simpa only [exp_log hx] using this

theorem hasStrictDerivAt_log {hx : IsUnit x} : HasStrictDerivAt log x⁻¹ x := by
  rcases hx.ne_zero.lt_or_gt with hx | hx
  · convert! (hasStrictDerivAt_log_of_pos (neg_pos.mpr hx)).comp x (hasStrictDerivAt_neg x) using 1
    · ext y; exact (log_neg_eq_log y).symm
    · ring
  · exact hasStrictDerivAt_log_of_pos hx

theorem hasDerivAt_log {hx : IsUnit x} : HasDerivAt log x⁻¹ x :=
  (hasStrictDerivAt_log (hx := hx)).hasDerivAt

@[fun_prop] theorem differentiableAt_log (hx : x ≠ 0) : DifferentiableAt ℝ log x :=
  (hasDerivAt_log (hx := hx.isUnit)).differentiableAt

theorem differentiableOn_log : DifferentiableOn ℝ log {0}ᶜ := fun _x hx =>
  (differentiableAt_log hx).differentiableWithinAt

@[simp]
theorem differentiableAt_log_iff : DifferentiableAt ℝ log x ↔ x ≠ 0 :=
  ⟨fun h => continuousAt_log_iff.1 h.continuousAt, differentiableAt_log⟩

theorem deriv_log (x : ℝ) {hx : IsUnit x} : deriv log x = x⁻¹ :=
  (hasDerivAt_log (hx := hx)).deriv

theorem deriv_log' :
    (fun x : ↥({0}ᶜ : Set ℝ) ↦ deriv log (x : ℝ)) =
      fun x : ↥({0}ᶜ : Set ℝ) ↦ Checked.inv (x : ℝ) (Ne.isUnit x.2) :=
  funext fun x ↦ deriv_log x (hx := Ne.isUnit x.2)

theorem contDiffAt_log {n : ℕ∞ω} {x : ℝ} : ContDiffAt ℝ n log x ↔ x ≠ 0 := by
  refine ⟨fun h ↦ continuousAt_log_iff.1 h.continuousAt, fun hx ↦ ?_⟩
  have A y (hy : 0 < y) : ContDiffAt ℝ n log y := by
    apply expPartialHomeomorph.contDiffAt_symm_deriv (f₀' := y) hy.ne' (by simpa)
    · convert! hasDerivAt_exp (log y)
      rw [exp_log hy]
    · exact analyticAt_rexp.contDiffAt
  rcases hx.lt_or_gt with hx | hx
  · have : ContDiffAt ℝ n (log ∘ (fun y ↦ -y)) x := by
      apply ContDiffAt.comp
      · apply A _ (Left.neg_pos_iff.mpr hx)
      apply contDiffAt_id.neg
    convert! this
    ext x
    simp
  · exact A x hx

@[fun_prop]
theorem contDiffOn_log {n : ℕ∞ω} : ContDiffOn ℝ n log {0}ᶜ := by
  intro x hx
  push _ ∈ _ at hx
  exact (contDiffAt_log.2 hx).contDiffWithinAt

end Real

section LogDifferentiable

open Real

section deriv

variable {f : ℝ → ℝ} {x f' : ℝ} {s : Set ℝ}

section Domain

variable {D : Type*} [TopologicalSpace D] {f : D → ℝ} {coord : D → ℝ}
  {x : D} {s : Set D}

theorem HasDerivWithinAt.log (hf : HasDerivWithinAt f f' s x coord) {hx : IsUnit (f x)}
    (hcoord : ContinuousWithinAt coord s x := by exact continuousWithinAt_id) :
    HasDerivWithinAt (fun y => log (f y)) (f' / f x) s x coord := by
  rw [div_eq_inv_mul₀]
  exact (hasDerivAt_log (hx := hx)).comp_hasDerivWithinAt (coord' := id) x hf hcoord

theorem HasDerivAt.log (hf : HasDerivAt f f' x coord) {hx : IsUnit (f x)}
    (hcoord : ContinuousAt coord x := by exact continuousAt_id) :
    HasDerivAt (fun y => log (f y)) (f' / f x) x coord := by
  rw [div_eq_inv_mul₀]
  exact (hasDerivAt_log (hx := hx)).comp (coord' := id) x hf hcoord

theorem HasStrictDerivAt.log (hf : HasStrictDerivAt f f' x coord) {hx : IsUnit (f x)}
    (hcoord : ContinuousAt coord x := by exact continuousAt_id) :
    HasStrictDerivAt (fun y => log (f y)) (f' / f x) x coord := by
  rw [div_eq_inv_mul₀]
  exact (hasStrictDerivAt_log (hx := hx)).comp (coord' := id) x hf hcoord

end Domain

theorem derivWithin.log (hf : DifferentiableWithinAt ℝ f s x) {hx : IsUnit (f x)}
    (hxs : UniqueDiffWithinAt ℝ s x) :
    derivWithin (fun x => log (f x)) s x = derivWithin f s x / f x :=
  (hf.hasDerivWithinAt.log (hx := hx)).derivWithin hxs

@[simp]
theorem deriv.log (hf : DifferentiableAt ℝ f x) {hx : f x ≠ 0} :
    deriv (fun x => log (f x)) x = Checked.div (deriv f x) (f x) hx.isUnit :=
  (hf.hasDerivAt.log (hx := hx.isUnit)).deriv

/-- The derivative of `log ∘ f` is the logarithmic derivative provided `f` is differentiable and
`f x  ≠ 0`. -/
lemma Real.deriv_log_comp_eq_logDeriv {f : ℝ → ℝ} {x : ℝ} (h₁ : DifferentiableAt ℝ f x)
    (h₂ : f x ≠ 0) :
    deriv (log ∘ f) x = logDeriv f x id h₁.existsUnique_hasDerivAt h₂.isUnit := by
  rw [logDeriv_apply]
  simpa only [Function.comp_def] using (deriv.log h₁ (hx := h₂))

end deriv

section fderiv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {x : E}
  {f' : StrongDual ℝ E} {s : Set E}

private theorem toSpanSingleton_comp_eq_smul (r : ℝ) (L : StrongDual ℝ E) :
    (ContinuousLinearMap.toSpanSingleton ℝ r).comp L = r • L := by
  apply ContinuousLinearMap.ext
  intro v
  change L v * r = r * L v
  exact mul_comm _ _

section Domain

variable {D : Type*} [TopologicalSpace D] {f : D → ℝ} {coord : D → E}
  {x : D} {s : Set D}

theorem HasFDerivWithinAt.log (hf : HasFDerivWithinAt f f' s x coord) {hx : IsUnit (f x)}
    (hcoord : ContinuousWithinAt coord s x := by exact continuousWithinAt_id) :
    HasFDerivWithinAt (fun x => log (f x)) ((f x)⁻¹ • f') s x coord := by
  rw [← toSpanSingleton_comp_eq_smul]
  exact (hasDerivAt_log (hx := hx)).hasFDerivAt.comp_hasFDerivWithinAt (coord' := id) x hf hcoord

theorem HasFDerivAt.log (hf : HasFDerivAt f f' x coord) {hx : IsUnit (f x)}
    (hcoord : ContinuousAt coord x := by exact continuousAt_id) :
    HasFDerivAt (fun x => log (f x)) ((f x)⁻¹ • f') x coord := by
  rw [← toSpanSingleton_comp_eq_smul]
  exact (hasDerivAt_log (hx := hx)).hasFDerivAt.comp (coord' := id) x hf hcoord

theorem HasStrictFDerivAt.log (hf : HasStrictFDerivAt f f' x coord) {hx : IsUnit (f x)}
    (hcoord : ContinuousAt coord x := by exact continuousAt_id) :
    HasStrictFDerivAt (fun x => log (f x)) ((f x)⁻¹ • f') x coord := by
  rw [← toSpanSingleton_comp_eq_smul]
  exact (hasStrictDerivAt_log (hx := hx)).hasStrictFDerivAt.comp (coord' := id) x hf hcoord

theorem DifferentiableWithinAt.log (hf : DifferentiableWithinAt ℝ f s x coord)
    (hx : f x ≠ 0)
    (hcoord : ContinuousWithinAt coord s x := by exact continuousWithinAt_id) :
    DifferentiableWithinAt ℝ (fun x => log (f x)) s x coord :=
  (hf.hasFDerivWithinAt.log (hx := hx.isUnit) hcoord).differentiableWithinAt

@[simp, fun_prop]
theorem DifferentiableAt.log (hf : DifferentiableAt ℝ f x coord) (hx : f x ≠ 0)
    (hcoord : ContinuousAt coord x := by exact continuousAt_id) :
    DifferentiableAt ℝ (fun x => log (f x)) x coord :=
  (hf.hasFDerivAt.log (hx := hx.isUnit) hcoord).differentiableAt

@[fun_prop]
theorem DifferentiableOn.log (hf : DifferentiableOn ℝ f s coord) (hx : ∀ x ∈ s, f x ≠ 0)
    (hcoord : ContinuousOn coord s := by exact continuousOn_id) :
    DifferentiableOn ℝ (fun x => log (f x)) s coord :=
  fun x h => (hf x h).log (hx x h) (hcoord x h)

@[simp, fun_prop]
theorem Differentiable.log (hf : Differentiable ℝ f coord) (hx : ∀ x, f x ≠ 0)
    (hcoord : Continuous coord := by exact continuous_id) :
    Differentiable ℝ (fun x => log (f x)) coord := fun x => (hf x).log (hx x) hcoord.continuousAt

end Domain

@[fun_prop]
theorem ContDiffAt.log {n} (hf : ContDiffAt ℝ n f x) (hx : f x ≠ 0) :
    ContDiffAt ℝ n (fun x => log (f x)) x :=
  (contDiffAt_log.2 hx).comp x hf

@[fun_prop]
theorem ContDiffWithinAt.log {n} (hf : ContDiffWithinAt ℝ n f s x) (hx : f x ≠ 0) :
    ContDiffWithinAt ℝ n (fun x => log (f x)) s x :=
  (contDiffAt_log.2 hx).comp_contDiffWithinAt x hf

@[fun_prop]
theorem ContDiffOn.log {n} (hf : ContDiffOn ℝ n f s) (hs : ∀ x ∈ s, f x ≠ 0) :
    ContDiffOn ℝ n (fun x => log (f x)) s := fun x hx => (hf x hx).log (hs x hx)

@[fun_prop]
theorem ContDiff.log {n} (hf : ContDiff ℝ n f) (h : ∀ x, f x ≠ 0) :
    ContDiff ℝ n fun x => log (f x) :=
  contDiff_iff_contDiffAt.2 fun x => hf.contDiffAt.log (h x)


theorem fderivWithin.log (hf : DifferentiableWithinAt ℝ f s x) {hx : IsUnit (f x)}
    (hxs : UniqueDiffWithinAt ℝ s x) :
    fderivWithin ℝ (fun x => log (f x)) s x = (f x)⁻¹ • fderivWithin ℝ f s x :=
  (hf.hasFDerivWithinAt.log (hx := hx)).fderivWithin hxs

@[simp]
theorem fderiv.log (hf : DifferentiableAt ℝ f x) {hx : f x ≠ 0} :
    fderiv ℝ (fun x => log (f x)) x = Checked.inv (f x) hx.isUnit • fderiv ℝ f x :=
  (hf.hasFDerivAt.log (hx := hx.isUnit)).fderiv

end fderiv

end LogDifferentiable

namespace Real

-- see https://github.com/leanprover-community/mathlib4/issues/29041
set_option linter.unusedSimpArgs false in
/-- A crude lemma estimating the difference between `log (1-x)` and its Taylor series at `0`,
where the main point of the bound is that it tends to `0`. The goal is to deduce the series
expansion of the logarithm, in `hasSum_pow_div_log_of_abs_lt_1`.

TODO: use one of generic theorems about Taylor's series to prove this estimate.
-/
theorem abs_log_sub_add_sum_range_le {x : ℝ} (h : |x| < 1) (n : ℕ) :
    |(∑ i ∈ range n, x ^ (i + 1) / ((i : ℝ) + 1)) + log (1 - x)| ≤ |x| ^ (n + 1) / (1 - |x|) := by
  let I := Ioo (-1 : ℝ) 1
  let F : ℝ → ℝ := fun y => (∑ i ∈ range n, y ^ (i + 1) / ((i : ℝ) + 1)) + log (1 - y)
  let F' : I → ℝ := fun y ↦ Checked.div (-(y : ℝ) ^ n) (1 - y)
    (sub_pos.mpr y.2.2).ne'.isUnit
  have hI : Icc (-|x|) |x| ⊆ I := Icc_subset_Ioo (neg_lt_neg h) h
  have A : ∀ y : I, HasDerivAt F (F' y) (y : ℝ) := by
    intro y
    have hy : -1 < (y : ℝ) ∧ (y : ℝ) < 1 := y.2
    have hden : IsUnit (1 - (y : ℝ)) := (sub_pos.mpr hy.2).ne'.isUnit
    have hd : HasDerivAt F
        ((∑ i ∈ range n, ↑(i + 1) * (y : ℝ) ^ i / ((i : ℝ) + 1)) + (-1) / (1 - (y : ℝ))) y :=
      .add (.fun_sum fun i _ ↦
          (hasDerivAt_pow (i + 1) (y : ℝ)).div_const ((i : ℝ) + 1))
        (((hasDerivAt_id (y : ℝ)).const_sub 1).log (hx := hden))
    convert! hd using 1
    calc
      -(y : ℝ) ^ n / (1 - (y : ℝ)) = ∑ i ∈ range n, (y : ℝ) ^ i + -1 / (1 - (y : ℝ)) := by
        apply (div_eq_iff (hb := hden)).mpr
        rw [add_mul, geom_sum_mul_neg, div_mul_cancel₀]
        ring
      _ = ∑ i ∈ range n, ↑(i + 1) * (y : ℝ) ^ i / ((i : ℝ) + 1) + -1 / (1 - (y : ℝ)) := by
        congr with i
        rw [Nat.cast_succ, mul_div_cancel_left₀]
  have B : ∀ y : I, (y : ℝ) ∈ Icc (-|x|) |x| → |F' y| ≤ |x| ^ n / (1 - |x|) := by
    intro y hy
    have hypos : 0 < 1 - (y : ℝ) := sub_pos.mpr y.2.2
    calc
      |F' y| = |(y : ℝ)| ^ n / (1 - (y : ℝ)) := by
        simp only [F', abs_div, abs_neg, abs_pow, abs_of_pos hypos]
      _ ≤ |x| ^ n / (1 - |x|) := by
        have : |(y : ℝ)| ≤ |x| := abs_le.2 hy
        have : 1 - |x| ≤ 1 - (y : ℝ) := sub_le_sub_left hy.2 1
        gcongr
  let p : I := ⟨x, abs_lt.mp h⟩
  let z : I := ⟨0, by constructor <;> norm_num⟩
  have C : ‖F x - F 0‖ ≤ |x| ^ n / (1 - |x|) * ‖x - 0‖ := by
    refine Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (coord := fun y : I ↦ (y : ℝ)) (f := fun y : I ↦ F y) (f' := F') (x := z) (y := p)
      (fun y _ ↦ ?_) (fun y hy ↦ ?_) (convex_Icc _ _) ?_ ?_
      Topology.IsEmbedding.subtypeVal (fun y hy ↦ ⟨⟨y, hI hy⟩, rfl⟩)
    · exact HasFDerivAtFilter.comp_tendsto (A y) Subtype.val
        (Filter.Tendsto.prodMap continuous_subtype_val.continuousWithinAt (tendsto_pure_pure ..))
    · simpa only [Real.norm_eq_abs] using B y hy
    · simp [z]
    · simp [p, le_abs_self x, neg_le.mp (neg_le_abs x)]
  simpa [F, div_mul_eq_mul_div₀, pow_succ] using C

/--
Compute the derivative of the difference between $\frac{1}{2} * \log(\frac{1+x}{1-x})$ and its
Taylor series at `0` up to order `n`. This is an auxiliary lemma for
`sum_range_sub_log_div_le` and `sum_range_le_log_div`.
Note that thanks to the geometric series, the derivative has a particularly simple form, and means
that it is more convenient to avoid Taylor's theorem.
-/
lemma hasDerivAt_half_log_one_add_div_one_sub_sub_sum_range
    {y : ℝ} (n : ℕ) (hy₁ : -1 < y) (hy₂ : y < 1) :
    HasDerivAt
      (fun x : Ioo (-1 : ℝ) 1 ↦
        1 / 2 * log (Checked.div (1 + (x : ℝ)) (1 - x) (sub_pos.mpr x.2.2).ne'.isUnit) -
          ∑ i ∈ range n, (x : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1))
      (Checked.div ((y ^ 2) ^ n) (1 - y ^ 2)
        (sub_pos.mpr ((sq_lt_one_iff_abs_lt_one y).mpr (abs_lt.mpr ⟨hy₁, hy₂⟩))).ne'.isUnit)
      ⟨y, hy₁, hy₂⟩ (fun x ↦ (x : ℝ)) := by
  let I := Ioo (-1 : ℝ) 1
  let p : I := ⟨y, hy₁, hy₂⟩
  let P : ℝ → ℝ := fun x ↦ ∑ i ∈ range n, x ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℝ)
  let F : ℝ → ℝ := fun x ↦ 1 / 2 * (log (1 + x) - log (1 - x)) - P x
  have hden : IsUnit (1 - y) := (sub_pos.mpr hy₂).ne'.isUnit
  have hplus : IsUnit (1 + y) := (show 0 < 1 + y by linarith).ne'.isUnit
  have hsquare : IsUnit (1 - y ^ 2) :=
    (sub_pos.mpr ((sq_lt_one_iff_abs_lt_one y).mpr (abs_lt.mpr ⟨hy₁, hy₂⟩))).ne'.isUnit
  let dP : ℝ := ∑ i ∈ range n,
    ((2 * i + 1 : ℕ) : ℝ) * y ^ (2 * i) / ((2 * i + 1 : ℕ) : ℝ)
  have hP : HasDerivAt P dP y := by
    refine HasDerivAt.fun_sum fun i _ ↦ ?_
    simpa only [Nat.add_sub_cancel] using
      (hasDerivAt_pow (2 * i + 1) y).div_const (((2 * i + 1 : ℕ) : ℝ))
  let dF : ℝ := 1 / 2 * (1 / (1 + y) - (-1) / (1 - (y : ℝ))) - dP
  have hF : HasDerivAt F dF y := by
    have h₁ := ((hasDerivAt_id y).const_add 1).log (hx := hplus)
    have h₂ := ((hasDerivAt_id y).const_sub 1).log (hx := hden)
    convert! (((h₁.fun_sub h₂).const_mul (1 / 2)).fun_sub hP) using 1
  have hsum : dP = ∑ i ∈ range n, (y ^ 2) ^ i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_div_cancel_left₀, pow_mul]
  have hcoef : dF = (y ^ 2) ^ n / (1 - y ^ 2) := by
    simp only [dF, hsum]
    calc
      _ = 1 / (1 - y ^ 2) - ∑ i ∈ range n, (y ^ 2) ^ i := by
        congr 1
        field
      _ = _ := by
        apply (eq_div_iff (hb := hsquare)).mpr
        rw [sub_mul, div_mul_cancel₀, geom_sum_mul_neg]
        ring
  rw [hcoef] at hF
  have hf : (fun x : I ↦
      1 / 2 * log (Checked.div (1 + (x : ℝ)) (1 - x) (sub_pos.mpr x.2.2).ne'.isUnit) -
        ∑ i ∈ range n, (x : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) = fun x : I ↦ F x := by
    funext x
    have hnum : 1 + (x : ℝ) ≠ 0 := (show 0 < 1 + (x : ℝ) by linarith [x.2.1]).ne'
    rw [log_div hnum]
    simp only [F, P, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
  rw [hf]
  exact HasFDerivAtFilter.comp_tendsto hF Subtype.val
    (Filter.Tendsto.prodMap (continuous_subtype_val.tendsto p) (tendsto_pure_pure ..))

/-- A lemma estimating the difference between $\frac{1}{2} * \log(\frac{1+x}{1-x})$ and its
Taylor series at `0`, where the bound tends to `0`. This bound is particularly useful for explicit
estimates of logarithms.

Note that thanks to the geometric series, the derivative has a particularly simple form, and means
that it is more convenient to avoid Taylor's theorem for this proof.
-/
lemma sum_range_sub_log_div_le {x : ℝ} (h : |x| < 1) (n : ℕ) :
    |1 / 2 * log (Checked.div (1 + x) (1 - x) (sub_pos.mpr (abs_lt.mp h).2).ne'.isUnit) -
        ∑ i ∈ range n, x ^ (2 * i + 1) / (2 * (i : ℝ) + 1)| ≤
      Checked.div (|x| ^ (2 * n + 1)) (1 - x ^ 2)
        (sub_pos.mpr ((sq_lt_one_iff_abs_lt_one x).mpr h)).ne'.isUnit := by
  let I := Ioo (-1 : ℝ) 1
  let F : I → ℝ := fun y ↦
    1 / 2 * log (Checked.div (1 + (y : ℝ)) (1 - y) (sub_pos.mpr y.2.2).ne'.isUnit) -
      ∑ i ∈ range n, (y : ℝ) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)
  let F' : I → ℝ := fun y ↦ Checked.div (((y : ℝ) ^ 2) ^ n) (1 - (y : ℝ) ^ 2)
    (sub_pos.mpr ((sq_lt_one_iff_abs_lt_one (y : ℝ)).mpr (abs_lt.mpr y.2))).ne'.isUnit
  have hI : Icc (-|x|) |x| ⊆ I := Icc_subset_Ioo (neg_lt_neg h) h
  have hxpos : 0 < 1 - x ^ 2 := sub_pos.mpr ((sq_lt_one_iff_abs_lt_one x).mpr h)
  have A : ∀ y : I, HasDerivAt F (F' y) y (fun z ↦ (z : ℝ)) := by
    intro y
    simpa only [F, F'] using
      hasDerivAt_half_log_one_add_div_one_sub_sub_sum_range n y.2.1 y.2.2
  have B : ∀ y : I, (y : ℝ) ∈ Icc (-|x|) |x| → ‖F' y‖ ≤ |x| ^ (2 * n) / (1 - x ^ 2) := by
    intro y hy
    have hypos : 0 < 1 - (y : ℝ) ^ 2 :=
      sub_pos.mpr ((sq_lt_one_iff_abs_lt_one (y : ℝ)).mpr (abs_lt.mpr y.2))
    have hysq : (y : ℝ) ^ 2 ≤ x ^ 2 := by
      rw [← sq_abs (y : ℝ), ← sq_abs x]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_le.2 hy) 2
    calc
      ‖F' y‖ = ((y : ℝ) ^ 2) ^ n / (1 - (y : ℝ) ^ 2) := by
        simp only [F', norm_eq_abs, abs_div, abs_of_pos hypos,
          abs_of_nonneg (pow_nonneg (sq_nonneg (y : ℝ)) n)]
      _ ≤ (x ^ 2) ^ n / (1 - x ^ 2) := by gcongr
      _ = |x| ^ (2 * n) / (1 - x ^ 2) := by simp only [pow_mul, sq_abs]
  let p : I := ⟨x, abs_lt.mp h⟩
  let z : I := ⟨0, by constructor <;> norm_num⟩
  have C : ‖F p - F z‖ ≤ |x| ^ (2 * n) / (1 - x ^ 2) * ‖x - 0‖ := by
    refine Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (coord := fun y : I ↦ (y : ℝ)) (f := F) (f' := F') (x := z) (y := p)
      (fun y _ ↦ ?_) B (convex_Icc _ _) ?_ ?_
      Topology.IsEmbedding.subtypeVal (fun y hy ↦ ⟨⟨y, hI hy⟩, rfl⟩)
    · exact HasFDerivAtFilter.mono (A y) (Filter.prod_mono nhdsWithin_le_nhds le_rfl)
    · simp [z]
    · simp [p, le_abs_self, neg_le, neg_le_abs x]
  have hFz : F z = 0 := by simp [F, z]
  rw [hFz, sub_zero] at C
  simpa only [F, p, norm_eq_abs, sub_zero, div_mul_eq_mul_div₀, ← pow_succ] using C

/-- Power series expansion of the logarithm around `1`. -/
theorem hasSum_pow_div_log_of_abs_lt_one {x : ℝ} (h : |x| < 1) :
    HasSum (fun n : ℕ => x ^ (n + 1) / ((n : ℝ) + 1)) (-log (1 - x)) := by
  rw [Summable.hasSum_iff_tendsto_nat]
  · change Tendsto (fun n : ℕ => ∑ i ∈ range n, x ^ (i + 1) / ((i : ℝ) + 1))
      atTop (𝓝 (-log (1 - x)))
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [norm_eq_abs, sub_neg_eq_add]
    refine squeeze_zero (fun n => abs_nonneg _) (abs_log_sub_add_sum_range_le h) ?_
    have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg x) h
    have hmul := (tendsto_const_nhds (x := |x|)).mul hpow
    simpa only [pow_succ', mul_zero, zero_div] using
      hmul.div_const₀ (1 - |x|) (hy := (sub_pos.mpr h).ne'.isUnit)
  change Summable fun n : ℕ => x ^ (n + 1) / ((n : ℝ) + 1)
  refine .of_norm_bounded (summable_geometric_of_lt_one (abs_nonneg _) h) fun i => ?_
  calc
    ‖x ^ (i + 1) / ((i : ℝ) + 1)‖ = |x| ^ (i + 1) / ((i : ℝ) + 1) := by
      have : (0 : ℝ) ≤ i + 1 := le_of_lt (Nat.cast_add_one_pos i)
      simp only [norm_eq_abs, abs_div, ← pow_abs, abs_of_nonneg this]
    _ ≤ |x| ^ (i + 1) / (0 + 1) := by
      gcongr
      positivity
    _ ≤ |x| ^ i := by
      simpa [pow_succ] using mul_le_of_le_one_right (by positivity) h.le

/-- Power series expansion of `log(1 + x) - log(1 - x)` for `|x| < 1`. -/
theorem hasSum_log_sub_log_of_abs_lt_one {x : ℝ} (h : |x| < 1) :
    HasSum (fun k : ℕ => (2 : ℝ) * (1 / (2 * (k : ℝ) + 1)) * x ^ (2 * k + 1))
      (log (1 + x) - log (1 - x)) := by
  set term := fun n : ℕ => -1 * ((-x) ^ (n + 1) / ((n : ℝ) + 1)) + x ^ (n + 1) / ((n : ℝ) + 1)
  have h_term_eq_goal :
      term ∘ (2 * ·) = fun k : ℕ => 2 * (1 / (2 * (k : ℝ) + 1)) * x ^ (2 * k + 1) := by
    ext n
    dsimp only [term, (· ∘ ·)]
    rw [Odd.neg_pow (⟨n, rfl⟩ : Odd (2 * n + 1)) x]
    push_cast
    ring_nf
  rw [← h_term_eq_goal, (mul_right_injective₀ (two_ne_zero' ℕ)).hasSum_iff]
  · have h₁ := (hasSum_pow_div_log_of_abs_lt_one (Eq.trans_lt (abs_neg x) h)).mul_left (-1)
    convert! h₁.add (hasSum_pow_div_log_of_abs_lt_one h) using 1
    ring_nf
  · intro m hm
    rw [range_two_mul, Set.mem_ofPred_eq, ← Nat.even_add_one] at hm
    dsimp [term]
    rw [Even.neg_pow hm, neg_one_mul, neg_add_cancel]

/-- Expansion of `log (1 + a⁻¹)` as a series in powers of `1 / (2 * a + 1)`. -/
theorem hasSum_log_one_add_inv {a : ℝ} (h : 0 < a) :
    HasSum (fun k : ℕ => (2 : ℝ) * (1 / (2 * (k : ℝ) + 1)) * (1 / (2 * a + 1)) ^ (2 * k + 1))
      (log (1 + a⁻¹)) := by
  have h₁ : |1 / (2 * a + 1)| < 1 := by
    rw [abs_of_pos, div_lt_one]
    · linarith
    · linarith
    · exact div_pos one_pos (by linarith)
  convert! hasSum_log_sub_log_of_abs_lt_one h₁ using 1
  have h₂ : (2 : ℝ) * a + 1 ≠ 0 := by linarith
  have h₃ := h.ne'
  rw [← log_div]
  · congr
    simp [field]
    ring
  · field_simp
    positivity
  · simp [field, h₃]

/-- Expansion of `log (1 + a)` as a series in powers of `a / (a + 2)`. -/
theorem hasSum_log_one_add {a : ℝ} (h : 0 ≤ a) :
    HasSum (fun k : ℕ => (2 : ℝ) * (1 / (2 * (k : ℝ) + 1)) * (a / (a + 2)) ^ (2 * k + 1))
      (log (1 + a)) := by
  obtain (rfl | ha0) := eq_or_ne a 0
  · simp [hasSum_zero]
  · have ha : 0 < a := lt_of_le_of_ne h ha0.symm
    have hinv : 0 < a⁻¹ := (inv_pos (ha := ha0.isUnit)).mpr ha
    have hq : 1 / (2 * a⁻¹ + 1) = a / (a + 2) := by field
    simpa only [hq, inv_inv₀] using hasSum_log_one_add_inv hinv

/--
For `0 ≤ x < 1`, the partial sums of the series expansion of $\frac{1}{2} * \log(\frac{1+x}{1-x})$
at `0` form a lower bound for it. This shows that the absolute value in `sum_range_sub_log_div_le`
can be dropped, and gives explicit lower bounds for logarithms.
-/
lemma sum_range_le_log_div {x : ℝ} (h₀ : 0 ≤ x) (h : x < 1) (n : ℕ) :
    ∑ i ∈ range n, x ^ (2 * i + 1) / (2 * (i : ℝ) + 1) ≤ 1 / 2 * log ((1 + x) / (1 - x)) := by
  have hx : |x| < 1 := by simpa only [abs_of_nonneg h₀] using h
  have hnum : 0 < 1 + x := by linarith
  have hden : 0 < 1 - x := sub_pos.mpr h
  have hsum : HasSum (fun k : ℕ ↦ x ^ (2 * k + 1) / (2 * (k : ℝ) + 1))
      (1 / 2 * log ((1 + x) / (1 - x))) := by
    convert (hasSum_log_sub_log_of_abs_lt_one hx).mul_left (1 / 2) using 1
    · funext k
      field_simp
    · rw [log_div hnum.ne']
  calc
    _ ≤ ∑' k : ℕ, x ^ (2 * k + 1) / (2 * (k : ℝ) + 1) :=
      hsum.summable.sum_le_tsum (range n) (fun k _ ↦ by positivity)
    _ = _ := hsum.tsum_eq

lemma log_div_le_sum_range_add {x : ℝ} (h₀ : 0 ≤ x) (h : x < 1) (n : ℕ) :
    1 / 2 * log ((1 + x) / (1 - x)) ≤
      (∑ i ∈ range n, x ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) +
        Checked.div (x ^ (2 * n + 1)) (1 - x ^ 2)
          (sub_pos.mpr ((sq_lt_one_iff_abs_lt_one x).mpr
            (by simpa only [abs_of_nonneg h₀] using h))).ne'.isUnit := by
  have hx : |x| < 1 := by simpa only [abs_of_nonneg h₀] using h
  have habs := sum_range_sub_log_div_le hx n
  simp only [abs_of_nonneg (sub_nonneg.mpr (sum_range_le_log_div h₀ h n)), abs_of_nonneg h₀]
    at habs
  exact sub_le_iff_le_add'.mp habs


end Real
