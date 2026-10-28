/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov, David Loeffler
-/
module

public import Mathlib.Analysis.Convex.Slope
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Convexity of functions and derivatives

Here we relate convexity of functions `ℝ → ℝ` to properties of their derivatives.

## Main results

* `MonotoneOn.convexOn_of_deriv`, `convexOn_of_deriv2_nonneg` : if the derivative of a function
  is increasing or its second derivative is nonnegative, then the original function is convex.
* `ConvexOn.monotoneOn_deriv`: if a function is convex and differentiable, then its derivative is
  monotone.
-/

public section

open Set Filter
open scoped Topology NNReal

/-!
## Monotonicity of `f'` implies convexity of `f`
-/

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ`, is differentiable on its interior,
and `f'` is monotone on the interior, then `f` is convex on `D`. -/
theorem MonotoneOn.convexOn_of_deriv {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : DifferentiableOn ℝ f (interior D))
    (hf'_mono : MonotoneOn (deriv f) (interior D)) : ConvexOn ℝ D f :=
  convexOn_of_slope_mono_adjacent hD
    (by
      intro x y z hx hz hxy hyz
      -- First we prove some trivial inclusions
      have hxzD : Icc x z ⊆ D := hD.ordConnected.out hx hz
      have hxyD : Icc x y ⊆ D := (Icc_subset_Icc_right hyz.le).trans hxzD
      have hxyD' : Ioo x y ⊆ interior D :=
        subset_sUnion_of_mem ⟨isOpen_Ioo, Ioo_subset_Icc_self.trans hxyD⟩
      have hyzD : Icc y z ⊆ D := (Icc_subset_Icc_left hxy.le).trans hxzD
      have hyzD' : Ioo y z ⊆ interior D :=
        subset_sUnion_of_mem ⟨isOpen_Ioo, Ioo_subset_Icc_self.trans hyzD⟩
      -- Then we apply MVT to both `[x, y]` and `[y, z]`
      obtain ⟨a, ⟨hxa, hay⟩, ha⟩ : ∃ a ∈ Ioo x y, deriv f a = (f y - f x) / (y - x) :=
        exists_deriv_eq_slope f hxy (hf.mono hxyD) (hf'.mono hxyD')
      obtain ⟨b, ⟨hyb, hbz⟩, hb⟩ : ∃ b ∈ Ioo y z, deriv f b = (f z - f y) / (z - y) :=
        exists_deriv_eq_slope f hyz (hf.mono hyzD) (hf'.mono hyzD')
      rw [← ha, ← hb]
      exact hf'_mono (hxyD' ⟨hxa, hay⟩) (hyzD' ⟨hyb, hbz⟩) (hay.trans hyb).le)

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ`, is differentiable on its interior,
and `f'` is antitone on the interior, then `f` is concave on `D`. -/
theorem AntitoneOn.concaveOn_of_deriv {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : DifferentiableOn ℝ f (interior D))
    (h_anti : AntitoneOn (deriv f) (interior D)) : ConcaveOn ℝ D f :=
  haveI : MonotoneOn (deriv (-f)) (interior D) := by
    simpa only [← deriv.neg] using h_anti.neg
  neg_convexOn_iff.mp (this.convexOn_of_deriv hD hf.neg hf'.neg)

theorem StrictMonoOn.exists_slope_lt_deriv_aux {x y : ℝ} {f : ℝ → ℝ} (hf : ContinuousOn f (Icc x y))
    (hxy : x < y) (hf'_mono : StrictMonoOn (deriv f) (Ioo x y)) (h : ∀ w ∈ Ioo x y, deriv f w ≠ 0) :
    ∃ a ∈ Ioo x y, (f y - f x) / (y - x) < deriv f a := by
  have A : DifferentiableOn ℝ f (Ioo x y) := fun w wmem =>
    (differentiableAt_of_deriv_ne_zero (h w wmem)).differentiableWithinAt
  obtain ⟨a, ⟨hxa, hay⟩, ha⟩ : ∃ a ∈ Ioo x y, deriv f a = (f y - f x) / (y - x) :=
    exists_deriv_eq_slope f hxy hf A
  rcases nonempty_Ioo.2 hay with ⟨b, ⟨hab, hby⟩⟩
  refine ⟨b, ⟨hxa.trans hab, hby⟩, ?_⟩
  rw [← ha]
  exact hf'_mono ⟨hxa, hay⟩ ⟨hxa.trans hab, hby⟩ hab

theorem StrictMonoOn.exists_slope_lt_deriv {x y : ℝ} {f : ℝ → ℝ} (hf : ContinuousOn f (Icc x y))
    (hxy : x < y) (hf'_mono : StrictMonoOn (deriv f) (Ioo x y)) :
    ∃ a ∈ Ioo x y, (f y - f x) / (y - x) < deriv f a := by
  by_cases! h : ∀ w ∈ Ioo x y, deriv f w ≠ 0
  · apply StrictMonoOn.exists_slope_lt_deriv_aux hf hxy hf'_mono h
  · rcases h with ⟨w, ⟨hxw, hwy⟩, hw⟩
    obtain ⟨a, ⟨hxa, haw⟩, ha⟩ : ∃ a ∈ Ioo x w, (f w - f x) / (w - x) < deriv f a := by
      apply StrictMonoOn.exists_slope_lt_deriv_aux _ hxw _ _
      · exact hf.mono (Icc_subset_Icc le_rfl hwy.le)
      · exact hf'_mono.mono (Ioo_subset_Ioo le_rfl hwy.le)
      · intro z hz
        rw [← hw]
        apply ne_of_lt
        exact hf'_mono ⟨hz.1, hz.2.trans hwy⟩ ⟨hxw, hwy⟩ hz.2
    obtain ⟨b, ⟨hwb, hby⟩, hb⟩ : ∃ b ∈ Ioo w y, (f y - f w) / (y - w) < deriv f b := by
      apply StrictMonoOn.exists_slope_lt_deriv_aux _ hwy _ _
      · refine hf.mono (Icc_subset_Icc hxw.le le_rfl)
      · exact hf'_mono.mono (Ioo_subset_Ioo hxw.le le_rfl)
      · intro z hz
        rw [← hw]
        apply ne_of_gt
        exact hf'_mono ⟨hxw, hwy⟩ ⟨hxw.trans hz.1, hz.2⟩ hz.1
    refine ⟨b, ⟨hxw.trans hwb, hby⟩, ?_⟩
    simp only [div_lt_iff₀, hxy, hxw, hwy, sub_pos] at ha hb ⊢
    have : deriv f a * (w - x) < deriv f b * (w - x) := by
      apply mul_lt_mul _ le_rfl (sub_pos.2 hxw) _
      · exact hf'_mono ⟨hxa, haw.trans hwy⟩ ⟨hxw.trans hwb, hby⟩ (haw.trans hwb)
      · rw [← hw]
        exact (hf'_mono ⟨hxw, hwy⟩ ⟨hxw.trans hwb, hby⟩ hwb).le
    linarith

theorem StrictMonoOn.exists_deriv_lt_slope_aux {x y : ℝ} {f : ℝ → ℝ} (hf : ContinuousOn f (Icc x y))
    (hxy : x < y) (hf'_mono : StrictMonoOn (deriv f) (Ioo x y)) (h : ∀ w ∈ Ioo x y, deriv f w ≠ 0) :
    ∃ a ∈ Ioo x y, deriv f a < (f y - f x) / (y - x) := by
  have A : DifferentiableOn ℝ f (Ioo x y) := fun w wmem =>
    (differentiableAt_of_deriv_ne_zero (h w wmem)).differentiableWithinAt
  obtain ⟨a, ⟨hxa, hay⟩, ha⟩ : ∃ a ∈ Ioo x y, deriv f a = (f y - f x) / (y - x) :=
    exists_deriv_eq_slope f hxy hf A
  rcases nonempty_Ioo.2 hxa with ⟨b, ⟨hxb, hba⟩⟩
  refine ⟨b, ⟨hxb, hba.trans hay⟩, ?_⟩
  rw [← ha]
  exact hf'_mono ⟨hxb, hba.trans hay⟩ ⟨hxa, hay⟩ hba

theorem StrictMonoOn.exists_deriv_lt_slope {x y : ℝ} {f : ℝ → ℝ} (hf : ContinuousOn f (Icc x y))
    (hxy : x < y) (hf'_mono : StrictMonoOn (deriv f) (Ioo x y)) :
    ∃ a ∈ Ioo x y, deriv f a < (f y - f x) / (y - x) := by
  by_cases! h : ∀ w ∈ Ioo x y, deriv f w ≠ 0
  · apply StrictMonoOn.exists_deriv_lt_slope_aux hf hxy hf'_mono h
  · rcases h with ⟨w, ⟨hxw, hwy⟩, hw⟩
    obtain ⟨a, ⟨hxa, haw⟩, ha⟩ : ∃ a ∈ Ioo x w, deriv f a < (f w - f x) / (w - x) := by
      apply StrictMonoOn.exists_deriv_lt_slope_aux _ hxw _ _
      · exact hf.mono (Icc_subset_Icc le_rfl hwy.le)
      · exact hf'_mono.mono (Ioo_subset_Ioo le_rfl hwy.le)
      · intro z hz
        rw [← hw]
        apply ne_of_lt
        exact hf'_mono ⟨hz.1, hz.2.trans hwy⟩ ⟨hxw, hwy⟩ hz.2
    obtain ⟨b, ⟨hwb, hby⟩, hb⟩ : ∃ b ∈ Ioo w y, deriv f b < (f y - f w) / (y - w) := by
      apply StrictMonoOn.exists_deriv_lt_slope_aux _ hwy _ _
      · refine hf.mono (Icc_subset_Icc hxw.le le_rfl)
      · exact hf'_mono.mono (Ioo_subset_Ioo hxw.le le_rfl)
      · intro z hz
        rw [← hw]
        apply ne_of_gt
        exact hf'_mono ⟨hxw, hwy⟩ ⟨hxw.trans hz.1, hz.2⟩ hz.1
    refine ⟨a, ⟨hxa, haw.trans hwy⟩, ?_⟩
    simp only [lt_div_iff₀, hxy, hxw, hwy, sub_pos] at ha hb ⊢
    have : deriv f a * (y - w) < deriv f b * (y - w) := by
      apply mul_lt_mul _ le_rfl (sub_pos.2 hwy) _
      · exact hf'_mono ⟨hxa, haw.trans hwy⟩ ⟨hxw.trans hwb, hby⟩ (haw.trans hwb)
      · rw [← hw]
        exact (hf'_mono ⟨hxw, hwy⟩ ⟨hxw.trans hwb, hby⟩ hwb).le
    linarith

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ`, and `f'` is strictly monotone on the
interior, then `f` is strictly convex on `D`.
Note that we don't require differentiability, since it is guaranteed at all but at most
one point by the strict monotonicity of `f'`. -/
theorem StrictMonoOn.strictConvexOn_of_deriv {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : StrictMonoOn (deriv f) (interior D)) : StrictConvexOn ℝ D f :=
  strictConvexOn_of_slope_strict_mono_adjacent hD fun {x y z} hx hz hxy hyz => by
    -- First we prove some trivial inclusions
    have hxzD : Icc x z ⊆ D := hD.ordConnected.out hx hz
    have hxyD : Icc x y ⊆ D := (Icc_subset_Icc_right hyz.le).trans hxzD
    have hxyD' : Ioo x y ⊆ interior D :=
      subset_sUnion_of_mem ⟨isOpen_Ioo, Ioo_subset_Icc_self.trans hxyD⟩
    have hyzD : Icc y z ⊆ D := (Icc_subset_Icc_left hxy.le).trans hxzD
    have hyzD' : Ioo y z ⊆ interior D :=
      subset_sUnion_of_mem ⟨isOpen_Ioo, Ioo_subset_Icc_self.trans hyzD⟩
    -- Then we get points `a` and `b` in each interval `[x, y]` and `[y, z]` where the derivatives
    -- can be compared to the slopes between `x, y` and `y, z` respectively.
    obtain ⟨a, ⟨hxa, hay⟩, ha⟩ : ∃ a ∈ Ioo x y, (f y - f x) / (y - x) < deriv f a :=
      StrictMonoOn.exists_slope_lt_deriv (hf.mono hxyD) hxy (hf'.mono hxyD')
    obtain ⟨b, ⟨hyb, hbz⟩, hb⟩ : ∃ b ∈ Ioo y z, deriv f b < (f z - f y) / (z - y) :=
      StrictMonoOn.exists_deriv_lt_slope (hf.mono hyzD) hyz (hf'.mono hyzD')
    apply ha.trans (lt_trans _ hb)
    exact hf' (hxyD' ⟨hxa, hay⟩) (hyzD' ⟨hyb, hbz⟩) (hay.trans hyb)

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ` and `f'` is strictly antitone on the
interior, then `f` is strictly concave on `D`.
Note that we don't require differentiability, since it is guaranteed at all but at most
one point by the strict antitonicity of `f'`. -/
theorem StrictAntiOn.strictConcaveOn_of_deriv {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (h_anti : StrictAntiOn (deriv f) (interior D)) :
    StrictConcaveOn ℝ D f :=
  have : StrictMonoOn (deriv (-f)) (interior D) := by simpa only [← deriv.neg] using h_anti.neg
  neg_neg f ▸ (this.strictConvexOn_of_deriv hD hf.neg).neg

/-- If a function `f` is differentiable and `f'` is monotone on `ℝ` then `f` is convex. -/
theorem Monotone.convexOn_univ_of_deriv {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (hf'_mono : Monotone (deriv f)) : ConvexOn ℝ univ f :=
  (hf'_mono.monotoneOn _).convexOn_of_deriv convex_univ hf.continuous.continuousOn
    hf.differentiableOn

/-- If a function `f` is differentiable and `f'` is antitone on `ℝ` then `f` is concave. -/
theorem Antitone.concaveOn_univ_of_deriv {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (hf'_anti : Antitone (deriv f)) : ConcaveOn ℝ univ f :=
  (hf'_anti.antitoneOn _).concaveOn_of_deriv convex_univ hf.continuous.continuousOn
    hf.differentiableOn

/-- If a function `f` is continuous and `f'` is strictly monotone on `ℝ` then `f` is strictly
convex. Note that we don't require differentiability, since it is guaranteed at all but at most
one point by the strict monotonicity of `f'`. -/
theorem StrictMono.strictConvexOn_univ_of_deriv {f : ℝ → ℝ} (hf : Continuous f)
    (hf'_mono : StrictMono (deriv f)) : StrictConvexOn ℝ univ f :=
  (hf'_mono.strictMonoOn _).strictConvexOn_of_deriv convex_univ hf.continuousOn

/-- If a function `f` is continuous and `f'` is strictly antitone on `ℝ` then `f` is strictly
concave. Note that we don't require differentiability, since it is guaranteed at all but at most
one point by the strict antitonicity of `f'`. -/
theorem StrictAnti.strictConcaveOn_univ_of_deriv {f : ℝ → ℝ} (hf : Continuous f)
    (hf'_anti : StrictAnti (deriv f)) : StrictConcaveOn ℝ univ f :=
  (hf'_anti.strictAntiOn _).strictConcaveOn_of_deriv convex_univ hf.continuousOn

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ`, is twice differentiable on its
interior, and `f''` is nonnegative on the interior, then `f` is convex on `D`. -/
theorem convexOn_of_deriv2_nonneg {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ} (hf : ContinuousOn f D)
    (hf' : DifferentiableOn ℝ f (interior D)) (hf'' : DifferentiableOn ℝ (deriv f) (interior D))
    (hf''_nonneg : ∀ x ∈ interior D, 0 ≤ deriv^[2] f x) : ConvexOn ℝ D f :=
  (monotoneOn_of_deriv_nonneg hD.interior hf''.continuousOn (by rwa [interior_interior]) <| by
        rwa [interior_interior]).convexOn_of_deriv
    hD hf hf'

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ`, is twice differentiable on its
interior, and `f''` is nonpositive on the interior, then `f` is concave on `D`. -/
theorem concaveOn_of_deriv2_nonpos {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ} (hf : ContinuousOn f D)
    (hf' : DifferentiableOn ℝ f (interior D)) (hf'' : DifferentiableOn ℝ (deriv f) (interior D))
    (hf''_nonpos : ∀ x ∈ interior D, deriv^[2] f x ≤ 0) : ConcaveOn ℝ D f :=
  (antitoneOn_of_deriv_nonpos hD.interior hf''.continuousOn (by rwa [interior_interior]) <| by
        rwa [interior_interior]).concaveOn_of_deriv
    hD hf hf'

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ`, is twice differentiable on its
interior, and `f''` is nonnegative on the interior, then `f` is convex on `D`. -/
lemma convexOn_of_hasDerivWithinAt2_nonneg {D : Set ℝ} (hD : Convex ℝ D) {f f' f'' : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : ∀ x ∈ interior D, HasDerivWithinAt f (f' x) (interior D) x)
    (hf'' : ∀ x ∈ interior D, HasDerivWithinAt f' (f'' x) (interior D) x)
    (hf''₀ : ∀ x ∈ interior D, 0 ≤ f'' x) : ConvexOn ℝ D f := by
  have : (interior D).EqOn (deriv f) f' := deriv_eqOn isOpen_interior hf'
  refine convexOn_of_deriv2_nonneg hD hf (fun x hx ↦ (hf' _ hx).differentiableWithinAt) ?_ ?_
  · rw [differentiableOn_congr this]
    exact fun x hx ↦ (hf'' _ hx).differentiableWithinAt
  · rintro x hx
    convert hf''₀ _ hx
    dsimp
    rw [deriv_eqOn isOpen_interior (fun y hy ↦ ?_) hx]
    exact (hf'' _ hy).congr this <| by rw [this hy]

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ`, is twice differentiable on its
interior, and `f''` is nonpositive on the interior, then `f` is concave on `D`. -/
lemma concaveOn_of_hasDerivWithinAt2_nonpos {D : Set ℝ} (hD : Convex ℝ D) {f f' f'' : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : ∀ x ∈ interior D, HasDerivWithinAt f (f' x) (interior D) x)
    (hf'' : ∀ x ∈ interior D, HasDerivWithinAt f' (f'' x) (interior D) x)
    (hf''₀ : ∀ x ∈ interior D, f'' x ≤ 0) : ConcaveOn ℝ D f := by
  have : (interior D).EqOn (deriv f) f' := deriv_eqOn isOpen_interior hf'
  refine concaveOn_of_deriv2_nonpos hD hf (fun x hx ↦ (hf' _ hx).differentiableWithinAt) ?_ ?_
  · rw [differentiableOn_congr this]
    exact fun x hx ↦ (hf'' _ hx).differentiableWithinAt
  · rintro x hx
    convert hf''₀ _ hx
    dsimp
    rw [deriv_eqOn isOpen_interior (fun y hy ↦ ?_) hx]
    exact (hf'' _ hy).congr this <| by rw [this hy]

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ` and `f''` is strictly positive on the
interior, then `f` is strictly convex on `D`.
Note that we don't require twice differentiability explicitly as it is already implied by the second
derivative being strictly positive, except at at most one point. -/
theorem strictConvexOn_of_deriv2_pos {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf'' : ∀ x ∈ interior D, 0 < (deriv^[2] f) x) :
    StrictConvexOn ℝ D f :=
  ((strictMonoOn_of_deriv_pos hD.interior fun z hz =>
          (differentiableAt_of_deriv_ne_zero
                (hf'' z hz).ne').differentiableWithinAt.continuousWithinAt) <|
        by rwa [interior_interior]).strictConvexOn_of_deriv
    hD hf

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ` and `f''` is strictly negative on the
interior, then `f` is strictly concave on `D`.
Note that we don't require twice differentiability explicitly as it already implied by the second
derivative being strictly negative, except at at most one point. -/
theorem strictConcaveOn_of_deriv2_neg {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf'' : ∀ x ∈ interior D, deriv^[2] f x < 0) :
    StrictConcaveOn ℝ D f :=
  ((strictAntiOn_of_deriv_neg hD.interior fun z hz =>
          (differentiableAt_of_deriv_ne_zero
                (hf'' z hz).ne).differentiableWithinAt.continuousWithinAt) <|
        by rwa [interior_interior]).strictConcaveOn_of_deriv
    hD hf

/-- If a function `f` is twice differentiable on an open convex set `D ⊆ ℝ` and
`f''` is nonnegative on `D`, then `f` is convex on `D`. -/
theorem convexOn_of_deriv2_nonneg' {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf' : DifferentiableOn ℝ f D) (hf'' : DifferentiableOn ℝ (deriv f) D)
    (hf''_nonneg : ∀ x ∈ D, 0 ≤ (deriv^[2] f) x) : ConvexOn ℝ D f :=
  convexOn_of_deriv2_nonneg hD hf'.continuousOn (hf'.mono interior_subset)
    (hf''.mono interior_subset) fun x hx => hf''_nonneg x (interior_subset hx)

/-- If a function `f` is twice differentiable on an open convex set `D ⊆ ℝ` and
`f''` is nonpositive on `D`, then `f` is concave on `D`. -/
theorem concaveOn_of_deriv2_nonpos' {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf' : DifferentiableOn ℝ f D) (hf'' : DifferentiableOn ℝ (deriv f) D)
    (hf''_nonpos : ∀ x ∈ D, deriv^[2] f x ≤ 0) : ConcaveOn ℝ D f :=
  concaveOn_of_deriv2_nonpos hD hf'.continuousOn (hf'.mono interior_subset)
    (hf''.mono interior_subset) fun x hx => hf''_nonpos x (interior_subset hx)

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ` and `f''` is strictly positive on `D`,
then `f` is strictly convex on `D`.
Note that we don't require twice differentiability explicitly as it is already implied by the second
derivative being strictly positive, except at at most one point. -/
theorem strictConvexOn_of_deriv2_pos' {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf'' : ∀ x ∈ D, 0 < (deriv^[2] f) x) : StrictConvexOn ℝ D f :=
  strictConvexOn_of_deriv2_pos hD hf fun x hx => hf'' x (interior_subset hx)

/-- If a function `f` is continuous on a convex set `D ⊆ ℝ` and `f''` is strictly negative on `D`,
then `f` is strictly concave on `D`.
Note that we don't require twice differentiability explicitly as it is already implied by the second
derivative being strictly negative, except at at most one point. -/
theorem strictConcaveOn_of_deriv2_neg' {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf'' : ∀ x ∈ D, deriv^[2] f x < 0) : StrictConcaveOn ℝ D f :=
  strictConcaveOn_of_deriv2_neg hD hf fun x hx => hf'' x (interior_subset hx)

/-- If a function `f` is twice differentiable on `ℝ`, and `f''` is nonnegative on `ℝ`,
then `f` is convex on `ℝ`. -/
theorem convexOn_univ_of_deriv2_nonneg {f : ℝ → ℝ} (hf' : Differentiable ℝ f)
    (hf'' : Differentiable ℝ (deriv f)) (hf''_nonneg : ∀ x, 0 ≤ (deriv^[2] f) x) :
    ConvexOn ℝ univ f :=
  convexOn_of_deriv2_nonneg' convex_univ hf'.differentiableOn hf''.differentiableOn fun x _ =>
    hf''_nonneg x

/-- If a function `f` is twice differentiable on `ℝ`, and `f''` is nonpositive on `ℝ`,
then `f` is concave on `ℝ`. -/
theorem concaveOn_univ_of_deriv2_nonpos {f : ℝ → ℝ} (hf' : Differentiable ℝ f)
    (hf'' : Differentiable ℝ (deriv f)) (hf''_nonpos : ∀ x, deriv^[2] f x ≤ 0) :
    ConcaveOn ℝ univ f :=
  concaveOn_of_deriv2_nonpos' convex_univ hf'.differentiableOn hf''.differentiableOn fun x _ =>
    hf''_nonpos x

/-- If a function `f` is continuous on `ℝ`, and `f''` is strictly positive on `ℝ`,
then `f` is strictly convex on `ℝ`.
Note that we don't require twice differentiability explicitly as it is already implied by the second
derivative being strictly positive, except at at most one point. -/
theorem strictConvexOn_univ_of_deriv2_pos {f : ℝ → ℝ} (hf : Continuous f)
    (hf'' : ∀ x, 0 < (deriv^[2] f) x) : StrictConvexOn ℝ univ f :=
  strictConvexOn_of_deriv2_pos' convex_univ hf.continuousOn fun x _ => hf'' x

/-- If a function `f` is continuous on `ℝ`, and `f''` is strictly negative on `ℝ`,
then `f` is strictly concave on `ℝ`.
Note that we don't require twice differentiability explicitly as it is already implied by the second
derivative being strictly negative, except at at most one point. -/
theorem strictConcaveOn_univ_of_deriv2_neg {f : ℝ → ℝ} (hf : Continuous f)
    (hf'' : ∀ x, deriv^[2] f x < 0) : StrictConcaveOn ℝ univ f :=
  strictConcaveOn_of_deriv2_neg' convex_univ hf.continuousOn fun x _ => hf'' x

/-!
## Convexity of `f` implies monotonicity of `f'`

In this section we prove inequalities relating derivatives of convex functions to slopes of secant
lines, and deduce that if `f` is convex then its derivative is monotone (and similarly for strict
convexity / strict monotonicity). The slope through `x` exists at the points `y ≠ x`, so its
monotonicity is stated for the slope as a function on such points of the domain.
-/

section slope

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  {s : Set 𝕜} {f : 𝕜 → 𝕜} {x : 𝕜}

/-- If `f : 𝕜 → 𝕜` is convex on `s`, then for any point `x ∈ s` the slope of the secant line of `f`
through `x` is monotone on `s \ {x}`, as a function on `s \ {x}`. -/
lemma ConvexOn.slope_mono (hfc : ConvexOn 𝕜 s f) (hx : x ∈ s) :
    Monotone fun y : ↥(s \ {x}) ↦ slope f x y fun h ↦ y.2.2 h.symm := by
  rintro ⟨y, hy⟩ ⟨z, hz⟩ hyz
  simp only [slope_def_field]
  exact hfc.secant_mono hx hy.1 hz.1 hy.2 hz.2 hyz

lemma ConvexOn.monotoneOn_slope_gt (hfc : ConvexOn 𝕜 s f) (hxs : x ∈ s) :
    Monotone fun y : ↥{y ∈ s | x < y} ↦ slope f x y y.2.2.ne := fun y z hyz ↦
  hfc.slope_mono hxs (show (⟨y, y.2.1, y.2.2.ne'⟩ : ↥(s \ {x})) ≤ ⟨z, z.2.1, z.2.2.ne'⟩ from hyz)

lemma ConvexOn.monotoneOn_slope_lt (hfc : ConvexOn 𝕜 s f) (hxs : x ∈ s) :
    Monotone fun y : ↥{y ∈ s | y < x} ↦ slope f x y y.2.2.ne' := fun y z hyz ↦
  hfc.slope_mono hxs (show (⟨y, y.2.1, y.2.2.ne⟩ : ↥(s \ {x})) ≤ ⟨z, z.2.1, z.2.2.ne⟩ from hyz)

/-- If `f : 𝕜 → 𝕜` is concave on `s`, then for any point `x ∈ s` the slope of the secant line of `f`
through `x` is antitone on `s \ {x}`, as a function on `s \ {x}`. -/
lemma ConcaveOn.slope_anti (hfc : ConcaveOn 𝕜 s f) (hx : x ∈ s) :
    Antitone fun y : ↥(s \ {x}) ↦ slope f x y fun h ↦ y.2.2 h.symm := fun y z hyz ↦ by
  simpa only [Pi.neg_def, slope_neg, neg_le_neg_iff] using hfc.neg.slope_mono hx hyz

lemma ConcaveOn.antitoneOn_slope_gt (hfc : ConcaveOn 𝕜 s f) (hxs : x ∈ s) :
    Antitone fun y : ↥{y ∈ s | x < y} ↦ slope f x y y.2.2.ne := fun y z hyz ↦
  hfc.slope_anti hxs (show (⟨y, y.2.1, y.2.2.ne'⟩ : ↥(s \ {x})) ≤ ⟨z, z.2.1, z.2.2.ne'⟩ from hyz)

lemma ConcaveOn.antitoneOn_slope_lt (hfc : ConcaveOn 𝕜 s f) (hxs : x ∈ s) :
    Antitone fun y : ↥{y ∈ s | y < x} ↦ slope f x y y.2.2.ne' := fun y z hyz ↦
  hfc.slope_anti hxs (show (⟨y, y.2.1, y.2.2.ne⟩ : ↥(s \ {x})) ≤ ⟨z, z.2.1, z.2.2.ne⟩ from hyz)

variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]

lemma bddBelow_slope_lt_of_mem_interior (hfc : ConvexOn 𝕜 s f) (hxs : x ∈ interior s) :
    BddBelow (range fun y : ↥{y ∈ s | x < y} ↦ slope f x y y.2.2.ne) := by
  obtain ⟨y, hyx, hys⟩ : ∃ y, y < x ∧ y ∈ s :=
    Eventually.exists_lt (mem_interior_iff_mem_nhds.mp hxs)
  refine ⟨slope f x y hyx.ne', ?_⟩
  rintro _ ⟨z, rfl⟩
  exact hfc.slope_mono (interior_subset hxs)
    (show (⟨y, hys, hyx.ne⟩ : ↥(s \ {x})) ≤ ⟨z, z.2.1, z.2.2.ne'⟩ from (hyx.trans z.2.2).le)

lemma bddAbove_slope_gt_of_mem_interior (hfc : ConvexOn 𝕜 s f) (hxs : x ∈ interior s) :
    BddAbove (range fun y : ↥{y ∈ s | y < x} ↦ slope f x y y.2.2.ne') := by
  obtain ⟨y, hyx, hys⟩ : ∃ y, x < y ∧ y ∈ s :=
    Eventually.exists_gt (mem_interior_iff_mem_nhds.mp hxs)
  refine ⟨slope f x y hyx.ne, ?_⟩
  rintro _ ⟨z, rfl⟩
  exact hfc.slope_mono (interior_subset hxs)
    (show (⟨z, z.2.1, z.2.2.ne⟩ : ↥(s \ {x})) ≤ ⟨y, hys, hyx.ne'⟩ from (z.2.2.trans hyx).le)

end slope

namespace ConvexOn

variable {S : Set ℝ} {f : ℝ → ℝ} {x y f' : ℝ}

section Interior

/-!
### Left and right derivative of a convex function in the interior of the set
-/

/-- A point of the interior of `S` has points of `S` to its right. -/
private lemma nonempty_gt_of_mem_interior (hxs : x ∈ interior S) :
    Nonempty ↥{y ∈ S | x < y} :=
  let ⟨y, hxy, hyS⟩ := Eventually.exists_gt (mem_interior_iff_mem_nhds.1 hxs)
  ⟨⟨y, hyS, hxy⟩⟩

/-- A point of the interior of `S` has points of `S` to its left. -/
private lemma nonempty_lt_of_mem_interior (hxs : x ∈ interior S) :
    Nonempty ↥{y ∈ S | y < x} :=
  let ⟨y, hyx, hyS⟩ := Eventually.exists_lt (mem_interior_iff_mem_nhds.1 hxs)
  ⟨⟨y, hyS, hyx⟩⟩

lemma hasDerivWithinAt_sInf_slope_of_mem_interior (hfc : ConvexOn ℝ S f) (hxs : x ∈ interior S) :
    HasDerivWithinAt f (⨅ y : ↥{y ∈ S | x < y}, slope f x y y.2.2.ne) (Ioi x) x := by
  obtain ⟨a, b, hxab, habs⟩ :=
    mem_nhds_iff_exists_Ioo_subset.1 (mem_interior_iff_mem_nhds.1 hxs)
  have := nonempty_gt_of_mem_interior hxs
  rw [hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi]
  refine tendsto_order.2 ⟨fun c hc ↦ ?_, fun c hc ↦ ?_⟩
  · -- every slope at a point of `(x, b)` is at least the infimum
    filter_upwards [tendsto_comap.eventually (Iio_mem_nhds hxab.2)] with y hy
    exact hc.trans_le <| ciInf_le (bddBelow_slope_lt_of_mem_interior hfc hxs)
      ⟨y, habs ⟨hxab.1.trans y.2, hy⟩, y.2⟩
  · -- some slope is below `c`, and so are the slopes at the points between `x` and it
    obtain ⟨⟨z, hzS, hxz⟩, hz⟩ := exists_lt_of_ciInf_lt hc
    filter_upwards [tendsto_comap.eventually (Iio_mem_nhds hxz)] with y hy
    have hyS : (y : ℝ) ∈ S :=
      hfc.convex.ordConnected.out (interior_subset hxs) hzS ⟨y.2.le, hy.le⟩
    exact lt_of_le_of_lt (hfc.monotoneOn_slope_gt (interior_subset hxs)
      (show (⟨y, hyS, y.2⟩ : ↥{y ∈ S | x < y}) ≤ ⟨z, hzS, hxz⟩ from hy.le)) hz

lemma hasDerivWithinAt_sSup_slope_of_mem_interior (hfc : ConvexOn ℝ S f) (hxs : x ∈ interior S) :
    HasDerivWithinAt f (⨆ y : ↥{y ∈ S | y < x}, slope f x y y.2.2.ne') (Iio x) x := by
  obtain ⟨a, b, hxab, habs⟩ :=
    mem_nhds_iff_exists_Ioo_subset.1 (mem_interior_iff_mem_nhds.1 hxs)
  have := nonempty_lt_of_mem_interior hxs
  rw [hasDerivWithinAt_iff_tendsto_slope' self_notMem_Iio]
  refine tendsto_order.2 ⟨fun c hc ↦ ?_, fun c hc ↦ ?_⟩
  · -- some slope is above `c`, and so are the slopes at the points between it and `x`
    obtain ⟨⟨z, hzS, hzx⟩, hz⟩ := exists_lt_of_lt_ciSup hc
    filter_upwards [tendsto_comap.eventually (Ioi_mem_nhds hzx)] with y hy
    have hyS : (y : ℝ) ∈ S :=
      hfc.convex.ordConnected.out hzS (interior_subset hxs) ⟨hy.le, y.2.le⟩
    exact lt_of_lt_of_le hz (hfc.monotoneOn_slope_lt (interior_subset hxs)
      (show (⟨z, hzS, hzx⟩ : ↥{y ∈ S | y < x}) ≤ ⟨y, hyS, y.2⟩ from hy.le))
  · -- every slope at a point of `(a, x)` is at most the supremum
    filter_upwards [tendsto_comap.eventually (Ioi_mem_nhds hxab.1)] with y hy
    exact (le_ciSup (bddAbove_slope_gt_of_mem_interior hfc hxs)
      ⟨y, habs ⟨hy, y.2.trans hxab.2⟩, y.2⟩).trans_lt hc

lemma differentiableWithinAt_Ioi_of_mem_interior (hfc : ConvexOn ℝ S f) (hxs : x ∈ interior S) :
    DifferentiableWithinAt ℝ f (Ioi x) x :=
  (hfc.hasDerivWithinAt_sInf_slope_of_mem_interior hxs).differentiableWithinAt

lemma differentiableWithinAt_Iio_of_mem_interior (hfc : ConvexOn ℝ S f) (hxs : x ∈ interior S) :
    DifferentiableWithinAt ℝ f (Iio x) x :=
  (hfc.hasDerivWithinAt_sSup_slope_of_mem_interior hxs).differentiableWithinAt

lemma hasDerivWithinAt_rightDeriv_of_mem_interior (hfc : ConvexOn ℝ S f) (hxs : x ∈ interior S) :
    HasDerivWithinAt f (derivWithin f (Ioi x) x) (Ioi x) x :=
  (hfc.differentiableWithinAt_Ioi_of_mem_interior hxs).hasDerivWithinAt

lemma hasDerivWithinAt_leftDeriv_of_mem_interior (hfc : ConvexOn ℝ S f) (hxs : x ∈ interior S) :
    HasDerivWithinAt f (derivWithin f (Iio x) x) (Iio x) x :=
  (hfc.differentiableWithinAt_Iio_of_mem_interior hxs).hasDerivWithinAt

lemma rightDeriv_eq_sInf_slope_of_mem_interior (hfc : ConvexOn ℝ S f) (hxs : x ∈ interior S) :
    derivWithin f (Ioi x) x = ⨅ y : ↥{y ∈ S | x < y}, slope f x y y.2.2.ne :=
  (hfc.hasDerivWithinAt_sInf_slope_of_mem_interior hxs).derivWithin (uniqueDiffWithinAt_Ioi x)

lemma leftDeriv_eq_sSup_slope_of_mem_interior (hfc : ConvexOn ℝ S f) (hxs : x ∈ interior S) :
    derivWithin f (Iio x) x = ⨆ y : ↥{y ∈ S | y < x}, slope f x y y.2.2.ne' :=
  (hfc.hasDerivWithinAt_sSup_slope_of_mem_interior hxs).derivWithin (uniqueDiffWithinAt_Iio x)

lemma monotoneOn_rightDeriv (hfc : ConvexOn ℝ S f) :
    MonotoneOn (fun x ↦ derivWithin f (Ioi x) x) (interior S) := by
  intro x hxs y hys hxy
  rcases eq_or_lt_of_le hxy with rfl | hxy; · rfl
  have := nonempty_gt_of_mem_interior hys
  simp_rw [hfc.rightDeriv_eq_sInf_slope_of_mem_interior hxs,
    hfc.rightDeriv_eq_sInf_slope_of_mem_interior hys]
  refine (ciInf_le (bddBelow_slope_lt_of_mem_interior hfc hxs)
    ⟨y, interior_subset hys, hxy⟩).trans (le_ciInf fun z ↦ ?_)
  rw [slope_comm f x]
  exact hfc.slope_mono (interior_subset hys)
    (show (⟨x, interior_subset hxs, hxy.ne⟩ : ↥(S \ {y})) ≤ ⟨z, z.2.1, z.2.2.ne'⟩ from
      (hxy.trans z.2.2).le)

lemma monotoneOn_leftDeriv (hfc : ConvexOn ℝ S f) :
    MonotoneOn (fun x ↦ derivWithin f (Iio x) x) (interior S) := by
  intro x hxs y hys hxy
  rcases eq_or_lt_of_le hxy with rfl | hxy; · rfl
  have := nonempty_lt_of_mem_interior hxs
  simp_rw [hfc.leftDeriv_eq_sSup_slope_of_mem_interior hxs,
    hfc.leftDeriv_eq_sSup_slope_of_mem_interior hys]
  refine (ciSup_le fun z ↦ ?_).trans (le_ciSup (bddAbove_slope_gt_of_mem_interior hfc hys)
    ⟨x, interior_subset hxs, hxy⟩)
  rw [slope_comm f y]
  exact hfc.slope_mono (interior_subset hxs)
    (show (⟨z, z.2.1, z.2.2.ne⟩ : ↥(S \ {x})) ≤ ⟨y, interior_subset hys, hxy.ne'⟩ from
      (z.2.2.trans hxy).le)

lemma leftDeriv_le_rightDeriv_of_mem_interior (hfc : ConvexOn ℝ S f) (hxs : x ∈ interior S) :
    derivWithin f (Iio x) x ≤ derivWithin f (Ioi x) x := by
  have := nonempty_lt_of_mem_interior hxs
  have := nonempty_gt_of_mem_interior hxs
  rw [hfc.rightDeriv_eq_sInf_slope_of_mem_interior hxs,
    hfc.leftDeriv_eq_sSup_slope_of_mem_interior hxs]
  refine ciSup_le fun z ↦ le_ciInf fun y ↦ ?_
  exact hfc.slope_mono (interior_subset hxs)
    (show (⟨z, z.2.1, z.2.2.ne⟩ : ↥(S \ {x})) ≤ ⟨y, y.2.1, y.2.2.ne'⟩ from (z.2.2.trans y.2.2).le)

end Interior

/-- The neighborhoods of `x` pulled back to `(x, +∞)` form a proper filter. -/
private lemma neBot_comap_coe_Ioi (x : ℝ) : (comap ((↑) : ↥(Ioi x) → ℝ) (𝓝 x)).NeBot :=
  mem_closure_iff_comap_neBot.1 (by simp)

/-- The neighborhoods of `x` pulled back to `(-∞, x)` form a proper filter. -/
private lemma neBot_comap_coe_Iio (x : ℝ) : (comap ((↑) : ↥(Iio x) → ℝ) (𝓝 x)).NeBot :=
  mem_closure_iff_comap_neBot.1 (by simp)

section left
/-!
### Convex functions, derivative at left endpoint of secant
-/

/-- If `f : ℝ → ℝ` is convex on `S` and right-differentiable at `x ∈ S`, then the slope of any
secant line with left endpoint at `x` is bounded below by the right derivative of `f` at `x`. -/
lemma le_slope_of_hasDerivWithinAt_Ioi (hfc : ConvexOn ℝ S f)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) (hf' : HasDerivWithinAt f f' (Ioi x) x) :
    f' ≤ slope f x y hxy.ne := by
  have := neBot_comap_coe_Ioi x
  apply le_of_tendsto <| (hasDerivWithinAt_iff_tendsto_slope' self_notMem_Ioi).mp hf'
  filter_upwards [tendsto_comap.eventually (Iio_mem_nhds hxy)] with t ht
  have htS : (t : ℝ) ∈ S := hfc.convex.ordConnected.out hx hy ⟨t.2.le, ht.le⟩
  exact hfc.slope_mono hx (show (⟨t, htS, t.2.ne'⟩ : ↥(S \ {x})) ≤ ⟨y, hy, hxy.ne'⟩ from ht.le)

/-- Reformulation of `ConvexOn.le_slope_of_hasDerivWithinAt_Ioi` using `derivWithin`. -/
lemma rightDeriv_le_slope (hfc : ConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableWithinAt ℝ f (Ioi x) x) :
    derivWithin f (Ioi x) x ≤ slope f x y hxy.ne :=
  le_slope_of_hasDerivWithinAt_Ioi hfc hx hy hxy hfd.hasDerivWithinAt

lemma rightDeriv_le_slope_of_mem_interior (hfc : ConvexOn ℝ S f)
    {y : ℝ} (hxs : x ∈ interior S) (hys : y ∈ S) (hxy : x < y) :
    derivWithin f (Ioi x) x ≤ slope f x y hxy.ne :=
  rightDeriv_le_slope hfc (interior_subset hxs) hys hxy
    (differentiableWithinAt_Ioi_of_mem_interior hfc hxs)

/-- If `f : ℝ → ℝ` is convex on `S` and differentiable within `S` at `x`, then the slope of any
secant line with left endpoint at `x` is bounded below by the derivative of `f` within `S` at `x`.

This is fractionally weaker than `ConvexOn.le_slope_of_hasDerivWithinAt_Ioi` but simpler to apply
under a `DifferentiableOn S` hypothesis. -/
lemma le_slope_of_hasDerivWithinAt (hfc : ConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hf' : HasDerivWithinAt f f' S x) :
    f' ≤ slope f x y hxy.ne :=
  hfc.le_slope_of_hasDerivWithinAt_Ioi hx hy hxy <|
    hf'.mono_of_mem_nhdsWithin <| hfc.convex.ordConnected.mem_nhdsGT hx hy hxy

/-- Reformulation of `ConvexOn.le_slope_of_hasDerivWithinAt` using `derivWithin`. -/
lemma derivWithin_le_slope (hfc : ConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableWithinAt ℝ f S x) :
    derivWithin f S x ≤ slope f x y hxy.ne :=
  le_slope_of_hasDerivWithinAt hfc hx hy hxy hfd.hasDerivWithinAt

/-- If `f : ℝ → ℝ` is convex on `S` and differentiable at `x ∈ S`, then the slope of any secant
line with left endpoint at `x` is bounded below by the derivative of `f` at `x`. -/
lemma le_slope_of_hasDerivAt (hfc : ConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (ha : HasDerivAt f f' x) :
    f' ≤ slope f x y hxy.ne :=
  hfc.le_slope_of_hasDerivWithinAt_Ioi hx hy hxy ha.hasDerivWithinAt

/-- Reformulation of `ConvexOn.le_slope_of_hasDerivAt` using `deriv` -/
lemma deriv_le_slope (hfc : ConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableAt ℝ f x) :
    deriv f x ≤ slope f x y hxy.ne :=
  le_slope_of_hasDerivAt hfc hx hy hxy hfd.hasDerivAt

end left

section right
/-!
### Convex functions, derivative at right endpoint of secant
-/

/-- If `f : ℝ → ℝ` is convex on `S` and left-differentiable at `y ∈ S`, then the slope of any secant
line with right endpoint at `y` is bounded above by the left derivative of `f` at `y`. -/
lemma slope_le_of_hasDerivWithinAt_Iio (hfc : ConvexOn ℝ S f)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) (hf' : HasDerivWithinAt f f' (Iio y) y) :
    slope f x y hxy.ne ≤ f' := by
  have := neBot_comap_coe_Iio y
  apply ge_of_tendsto <| (hasDerivWithinAt_iff_tendsto_slope' self_notMem_Iio).mp hf'
  filter_upwards [tendsto_comap.eventually (Ioi_mem_nhds hxy)] with t ht
  have htS : (t : ℝ) ∈ S := hfc.convex.ordConnected.out hx hy ⟨ht.le, t.2.le⟩
  rw [slope_comm f x]
  exact hfc.slope_mono hy (show (⟨x, hx, hxy.ne⟩ : ↥(S \ {y})) ≤ ⟨t, htS, t.2.ne⟩ from ht.le)

/-- Reformulation of `ConvexOn.slope_le_of_hasDerivWithinAt_Iio` using `derivWithin`. -/
lemma slope_le_leftDeriv (hfc : ConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableWithinAt ℝ f (Iio y) y) :
    slope f x y hxy.ne ≤ derivWithin f (Iio y) y :=
  hfc.slope_le_of_hasDerivWithinAt_Iio hx hy hxy hfd.hasDerivWithinAt

lemma slope_le_leftDeriv_of_mem_interior (hfc : ConvexOn ℝ S f)
    (hys : x ∈ S) (hxs : y ∈ interior S) (hxy : x < y) :
    slope f x y hxy.ne ≤ derivWithin f (Iio y) y :=
  slope_le_leftDeriv hfc hys (interior_subset hxs) hxy
    (differentiableWithinAt_Iio_of_mem_interior hfc hxs)

/-- If `f : ℝ → ℝ` is convex on `S` and differentiable within `S` at `y`, then the slope of any
secant line with right endpoint at `y` is bounded above by the derivative of `f` within `S` at `y`.

This is fractionally weaker than `ConvexOn.slope_le_of_hasDerivWithinAt_Iio` but simpler to apply
under a `DifferentiableOn S` hypothesis. -/
lemma slope_le_of_hasDerivWithinAt (hfc : ConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hf' : HasDerivWithinAt f f' S y) :
    slope f x y hxy.ne ≤ f' :=
  hfc.slope_le_of_hasDerivWithinAt_Iio hx hy hxy <|
    hf'.mono_of_mem_nhdsWithin <| hfc.convex.ordConnected.mem_nhdsLT hx hy hxy

/-- Reformulation of `ConvexOn.slope_le_of_hasDerivWithinAt` using `derivWithin`. -/
lemma slope_le_derivWithin (hfc : ConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableWithinAt ℝ f S y) :
    slope f x y hxy.ne ≤ derivWithin f S y :=
  hfc.slope_le_of_hasDerivWithinAt hx hy hxy hfd.hasDerivWithinAt

/-- If `f : ℝ → ℝ` is convex on `S` and differentiable at `y ∈ S`, then the slope of any secant
line with right endpoint at `y` is bounded above by the derivative of `f` at `y`. -/
lemma slope_le_of_hasDerivAt (hfc : ConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hf' : HasDerivAt f f' y) :
    slope f x y hxy.ne ≤ f' :=
  hfc.slope_le_of_hasDerivWithinAt_Iio hx hy hxy hf'.hasDerivWithinAt

/-- Reformulation of `ConvexOn.slope_le_of_hasDerivAt` using `deriv`. -/
lemma slope_le_deriv (hfc : ConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableAt ℝ f y) :
    slope f x y hxy.ne ≤ deriv f y :=
  hfc.slope_le_of_hasDerivAt hx hy hxy hfd.hasDerivAt

end right
/-!
### Convex functions, monotonicity of derivative
-/

/-- If `f` is convex on `S` and differentiable on `S`, then its derivative within `S` is monotone
on `S`. -/
lemma monotoneOn_derivWithin (hfc : ConvexOn ℝ S f) (hfd : DifferentiableOn ℝ f S) :
    MonotoneOn (derivWithin f S) S := by
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hxy with rfl | hxy'
  · rfl
  exact (hfc.derivWithin_le_slope hx hy hxy' (hfd x hx)).trans
    (hfc.slope_le_derivWithin hx hy hxy' (hfd y hy))

/-- If `f` is convex on `S` and differentiable at all points of `S`, then its derivative is monotone
on `S`. -/
theorem monotoneOn_deriv (hfc : ConvexOn ℝ S f) (hfd : ∀ x ∈ S, DifferentiableAt ℝ f x) :
    MonotoneOn (deriv f) S := by
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hxy with rfl | hxy'
  · rfl
  exact (hfc.deriv_le_slope hx hy hxy' (hfd x hx)).trans (hfc.slope_le_deriv hx hy hxy' (hfd y hy))

lemma isMinOn_of_leftDeriv_nonpos_of_rightDeriv_nonneg (hf : ConvexOn ℝ S f) (hx : x ∈ interior S)
    (hf_ld : derivWithin f (Iio x) x ≤ 0) (hf_rd : 0 ≤ derivWithin f (Ioi x) x) :
    IsMinOn f S x := by
  intro y hy
  rcases lt_trichotomy x y with hxy | h_eq | hyx
  · exact (slope_nonneg_iff_of_le hxy.le).1 <|
      hf_rd.trans <| rightDeriv_le_slope_of_mem_interior hf hx hy hxy
  · simp [h_eq]
  · exact (slope_nonpos_iff_of_le hyx.le).1 <|
      (slope_le_leftDeriv_of_mem_interior hf hy hx hyx).trans hf_ld

lemma isMinOn_of_rightDeriv_eq_zero (hf : ConvexOn ℝ S f) (hx : x ∈ interior S)
    (hf_rd : derivWithin f (Ioi x) x = 0) :
    IsMinOn f S x := by
  refine hf.isMinOn_of_leftDeriv_nonpos_of_rightDeriv_nonneg hx ?_ hf_rd.symm.le
  exact (hf.leftDeriv_le_rightDeriv_of_mem_interior hx).trans_eq hf_rd

lemma isMinOn_of_leftDeriv_eq_zero (hf : ConvexOn ℝ S f) (hx : x ∈ interior S)
    (hf_ld : derivWithin f (Iio x) x = 0) :
    IsMinOn f S x := by
  refine hf.isMinOn_of_leftDeriv_nonpos_of_rightDeriv_nonneg hx hf_ld.le ?_
  exact hf_ld.symm.le.trans (hf.leftDeriv_le_rightDeriv_of_mem_interior hx)

end ConvexOn

namespace StrictConvexOn

variable {S : Set ℝ} {f : ℝ → ℝ} {x y f' : ℝ}

section left
/-!
### Strict convex functions, derivative at left endpoint of secant
-/

/-- If `f : ℝ → ℝ` is strictly convex on `S` and right-differentiable at `x ∈ S`, then the slope of
any secant line with left endpoint at `x` is strictly greater than the right derivative of `f` at
`x`. -/
lemma lt_slope_of_hasDerivWithinAt_Ioi (hfc : StrictConvexOn ℝ S f)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) (hf' : HasDerivWithinAt f f' (Ioi x) x) :
    f' < slope f x y hxy.ne := by
  obtain ⟨u, hxu, huy⟩ := exists_between hxy
  have hu : u ∈ S := hfc.convex.ordConnected.out hx hy ⟨hxu.le, huy.le⟩
  have h₁ := hfc.convexOn.le_slope_of_hasDerivWithinAt_Ioi hx hu hxu hf'
  rw [slope_def_field] at h₁ ⊢
  exact h₁.trans_lt (hfc.secant_strict_mono hx hu hy hxu.ne' hxy.ne' huy)

lemma rightDeriv_lt_slope (hfc : StrictConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableWithinAt ℝ f (Ioi x) x) :
    derivWithin f (Ioi x) x < slope f x y hxy.ne :=
  hfc.lt_slope_of_hasDerivWithinAt_Ioi hx hy hxy hfd.hasDerivWithinAt

/-- If `f : ℝ → ℝ` is strictly convex on `S` and differentiable within `S` at `x ∈ S`, then the
slope of any secant line with left endpoint at `x` is strictly greater than the derivative of `f`
within `S` at `x`.

This is fractionally weaker than `StrictConvexOn.lt_slope_of_hasDerivWithinAt_Ioi` but simpler to
apply under a `DifferentiableOn S` hypothesis. -/
lemma lt_slope_of_hasDerivWithinAt (hfc : StrictConvexOn ℝ S f)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) (hf' : HasDerivWithinAt f f' S x) :
    f' < slope f x y hxy.ne :=
  hfc.lt_slope_of_hasDerivWithinAt_Ioi hx hy hxy <|
    hf'.mono_of_mem_nhdsWithin <| hfc.convex.ordConnected.mem_nhdsGT hx hy hxy

lemma derivWithin_lt_slope (hfc : StrictConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableWithinAt ℝ f S x) :
    derivWithin f S x < slope f x y hxy.ne :=
  hfc.lt_slope_of_hasDerivWithinAt hx hy hxy hfd.hasDerivWithinAt

/-- If `f : ℝ → ℝ` is strictly convex on `S` and differentiable at `x ∈ S`, then the slope of any
secant line with left endpoint at `x` is strictly greater than the derivative of `f` at `x`. -/
lemma lt_slope_of_hasDerivAt (hfc : StrictConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hf' : HasDerivAt f f' x) :
    f' < slope f x y hxy.ne :=
  hfc.lt_slope_of_hasDerivWithinAt_Ioi hx hy hxy hf'.hasDerivWithinAt

lemma deriv_lt_slope (hfc : StrictConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableAt ℝ f x) :
    deriv f x < slope f x y hxy.ne :=
  hfc.lt_slope_of_hasDerivAt hx hy hxy hfd.hasDerivAt

end left

section right
/-!
### Strict convex functions, derivative at right endpoint of secant
-/

/-- If `f : ℝ → ℝ` is strictly convex on `S` and differentiable at `y ∈ S`, then the slope of any
secant line with right endpoint at `y` is strictly less than the left derivative at `y`. -/
lemma slope_lt_of_hasDerivWithinAt_Iio (hfc : StrictConvexOn ℝ S f)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) (hf' : HasDerivWithinAt f f' (Iio y) y) :
    slope f x y hxy.ne < f' := by
  obtain ⟨u, hxu, huy⟩ := exists_between hxy
  have hu : u ∈ S := hfc.convex.ordConnected.out hx hy ⟨hxu.le, huy.le⟩
  have h₁ := hfc.convexOn.slope_le_of_hasDerivWithinAt_Iio hu hy huy hf'
  rw [slope_comm f u, slope_def_field] at h₁
  rw [slope_comm f x, slope_def_field]
  exact (hfc.secant_strict_mono hy hx hu hxy.ne huy.ne hxu).trans_le h₁

lemma slope_lt_leftDeriv (hfc : StrictConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableWithinAt ℝ f (Iio y) y) :
    slope f x y hxy.ne < derivWithin f (Iio y) y :=
  hfc.slope_lt_of_hasDerivWithinAt_Iio hx hy hxy hfd.hasDerivWithinAt

/-- If `f : ℝ → ℝ` is strictly convex on `S` and differentiable within `S` at `y ∈ S`, then the
slope of any secant line with right endpoint at `y` is strictly less than the derivative of `f`
within `S` at `y`.

This is fractionally weaker than `StrictConvexOn.slope_lt_of_hasDerivWithinAt_Iio` but simpler to
apply under a `DifferentiableOn S` hypothesis. -/
lemma slope_lt_of_hasDerivWithinAt (hfc : StrictConvexOn ℝ S f)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) (hf' : HasDerivWithinAt f f' S y) :
    slope f x y hxy.ne < f' :=
  hfc.slope_lt_of_hasDerivWithinAt_Iio hx hy hxy <|
    hf'.mono_of_mem_nhdsWithin <| hfc.convex.ordConnected.mem_nhdsLT hx hy hxy

lemma slope_lt_derivWithin (hfc : StrictConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableWithinAt ℝ f S y) :
    slope f x y hxy.ne < derivWithin f S y :=
  hfc.slope_lt_of_hasDerivWithinAt hx hy hxy hfd.hasDerivWithinAt

/-- If `f : ℝ → ℝ` is strictly convex on `S` and differentiable at `y ∈ S`, then the slope of any
secant line with right endpoint at `y` is strictly less than the derivative of `f` at `y`. -/
lemma slope_lt_of_hasDerivAt (hfc : StrictConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hf' : HasDerivAt f f' y) :
    slope f x y hxy.ne < f' :=
  hfc.slope_lt_of_hasDerivWithinAt_Iio hx hy hxy hf'.hasDerivWithinAt

lemma slope_lt_deriv (hfc : StrictConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableAt ℝ f y) :
    slope f x y hxy.ne < deriv f y :=
  hfc.slope_lt_of_hasDerivAt hx hy hxy hfd.hasDerivAt

end right

/-!
### Strict convex functions, strict monotonicity of derivative
-/

/-- If `f` is convex on `S` and differentiable on `S`, then its derivative within `S` is monotone
on `S`. -/
lemma strictMonoOn_derivWithin (hfc : StrictConvexOn ℝ S f) (hfd : DifferentiableOn ℝ f S) :
    StrictMonoOn (derivWithin f S) S := by
  intro x hx y hy hxy
  exact (hfc.derivWithin_lt_slope hx hy hxy (hfd x hx)).trans
    (hfc.slope_lt_derivWithin hx hy hxy (hfd y hy))

/-- If `f` is convex on `S` and differentiable at all points of `S`, then its derivative is monotone
on `S`. -/
lemma strictMonoOn_deriv (hfc : StrictConvexOn ℝ S f) (hfd : ∀ x ∈ S, DifferentiableAt ℝ f x) :
    StrictMonoOn (deriv f) S := by
  intro x hx y hy hxy
  exact (hfc.deriv_lt_slope hx hy hxy (hfd x hx)).trans (hfc.slope_lt_deriv hx hy hxy (hfd y hy))

end StrictConvexOn

section MirrorImage

variable {S : Set ℝ} {f : ℝ → ℝ} {x y f' : ℝ}

namespace ConcaveOn

section left
/-!
### Concave functions, derivative at left endpoint of secant
-/

lemma slope_le_of_hasDerivWithinAt_Ioi (hfc : ConcaveOn ℝ S f)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) (hf' : HasDerivWithinAt f f' (Ioi x) x) :
    slope f x y hxy.ne ≤ f' := by
  simpa only [Pi.neg_def, slope_neg, neg_neg] using
    neg_le_neg (hfc.neg.le_slope_of_hasDerivWithinAt_Ioi hx hy hxy hf'.neg)

lemma slope_le_rightDeriv (hfc : ConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableWithinAt ℝ f (Ioi x) x) :
    slope f x y hxy.ne ≤ derivWithin f (Ioi x) x :=
  hfc.slope_le_of_hasDerivWithinAt_Ioi hx hy hxy hfd.hasDerivWithinAt

lemma slope_le_of_hasDerivWithinAt (hfc : ConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : HasDerivWithinAt f f' S x) :
    slope f x y hxy.ne ≤ f' :=
  hfc.slope_le_of_hasDerivWithinAt_Ioi hx hy hxy <|
    hfd.mono_of_mem_nhdsWithin <| hfc.convex.ordConnected.mem_nhdsGT hx hy hxy

lemma slope_le_derivWithin (hfc : ConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableWithinAt ℝ f S x) :
    slope f x y hxy.ne ≤ derivWithin f S x :=
  hfc.slope_le_of_hasDerivWithinAt hx hy hxy hfd.hasDerivWithinAt

lemma slope_le_of_hasDerivAt (hfc : ConcaveOn ℝ S f)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) (hf' : HasDerivAt f f' x) :
    slope f x y hxy.ne ≤ f' :=
  hfc.slope_le_of_hasDerivWithinAt_Ioi hx hy hxy hf'.hasDerivWithinAt

lemma slope_le_deriv (hfc : ConcaveOn ℝ S f)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) (hfd : DifferentiableAt ℝ f x) :
    slope f x y hxy.ne ≤ deriv f x :=
  hfc.slope_le_of_hasDerivAt hx hy hxy hfd.hasDerivAt

end left

section right
/-!
### Concave functions, derivative at right endpoint of secant
-/

lemma le_slope_of_hasDerivWithinAt_Iio (hfc : ConcaveOn ℝ S f)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) (hf' : HasDerivWithinAt f f' (Iio y) y) :
    f' ≤ slope f x y hxy.ne := by
  simpa only [neg_neg, Pi.neg_def, slope_neg] using
    neg_le_neg (hfc.neg.slope_le_of_hasDerivWithinAt_Iio hx hy hxy hf'.neg)

lemma leftDeriv_le_slope (hfc : ConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableWithinAt ℝ f (Iio y) y) :
    derivWithin f (Iio y) y ≤ slope f x y hxy.ne :=
  hfc.le_slope_of_hasDerivWithinAt_Iio hx hy hxy hfd.hasDerivWithinAt

lemma le_slope_of_hasDerivWithinAt (hfc : ConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hf' : HasDerivWithinAt f f' S y) :
    f' ≤ slope f x y hxy.ne :=
  hfc.le_slope_of_hasDerivWithinAt_Iio hx hy hxy <|
    hf'.mono_of_mem_nhdsWithin <| hfc.convex.ordConnected.mem_nhdsLT hx hy hxy

lemma derivWithin_le_slope (hfc : ConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableWithinAt ℝ f S y) :
    derivWithin f S y ≤ slope f x y hxy.ne :=
  hfc.le_slope_of_hasDerivWithinAt hx hy hxy hfd.hasDerivWithinAt

lemma le_slope_of_hasDerivAt (hfc : ConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hf' : HasDerivAt f f' y) :
    f' ≤ slope f x y hxy.ne :=
  hfc.le_slope_of_hasDerivWithinAt_Iio hx hy hxy hf'.hasDerivWithinAt

lemma deriv_le_slope (hfc : ConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableAt ℝ f y) :
    deriv f y ≤ slope f x y hxy.ne :=
  hfc.le_slope_of_hasDerivAt hx hy hxy hfd.hasDerivAt

end right
/-!
### Concave functions, anti-monotonicity of derivative
-/

lemma antitoneOn_derivWithin (hfc : ConcaveOn ℝ S f) (hfd : DifferentiableOn ℝ f S) :
    AntitoneOn (derivWithin f S) S := by
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hxy with rfl | hxy'
  · rfl
  exact (hfc.derivWithin_le_slope hx hy hxy' (hfd y hy)).trans
    (hfc.slope_le_derivWithin hx hy hxy' (hfd x hx))

/-- If `f` is concave on `S` and differentiable at all points of `S`, then its derivative is
antitone (monotone decreasing) on `S`. -/
theorem antitoneOn_deriv (hfc : ConcaveOn ℝ S f) (hfd : ∀ x ∈ S, DifferentiableAt ℝ f x) :
    AntitoneOn (deriv f) S := by
  simpa using (hfc.neg.monotoneOn_deriv (fun x hx ↦ (hfd x hx).neg)).neg

end ConcaveOn

namespace StrictConcaveOn

section left
/-!
### Strict concave functions, derivative at left endpoint of secant
-/

lemma slope_lt_of_hasDerivWithinAt_Ioi (hfc : StrictConcaveOn ℝ S f)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) (hf' : HasDerivWithinAt f f' (Ioi x) x) :
    slope f x y hxy.ne < f' := by
  simpa only [Pi.neg_def, slope_neg, neg_neg] using
    neg_lt_neg (hfc.neg.lt_slope_of_hasDerivWithinAt_Ioi hx hy hxy hf'.neg)

lemma slope_lt_rightDeriv (hfc : StrictConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableWithinAt ℝ f (Ioi x) x) :
    slope f x y hxy.ne < derivWithin f (Ioi x) x :=
  hfc.slope_lt_of_hasDerivWithinAt_Ioi hx hy hxy hfd.hasDerivWithinAt

lemma slope_lt_of_hasDerivWithinAt (hfc : StrictConcaveOn ℝ S f)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) (hfd : HasDerivWithinAt f f' S x) :
    slope f x y hxy.ne < f' := by
  simpa only [Pi.neg_def, slope_neg, neg_neg] using
    neg_lt_neg (hfc.neg.lt_slope_of_hasDerivWithinAt hx hy hxy hfd.neg)

lemma slope_lt_derivWithin (hfc : StrictConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableWithinAt ℝ f S x) :
    slope f x y hxy.ne < derivWithin f S x :=
  hfc.slope_lt_of_hasDerivWithinAt hx hy hxy hfd.hasDerivWithinAt

lemma slope_lt_of_hasDerivAt (hfc : StrictConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : HasDerivAt f f' x) :
    slope f x y hxy.ne < f' := by
  simpa only [Pi.neg_def, slope_neg, neg_neg] using
    neg_lt_neg (hfc.neg.lt_slope_of_hasDerivAt hx hy hxy hfd.neg)

lemma slope_lt_deriv (hfc : StrictConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableAt ℝ f x) :
    slope f x y hxy.ne < deriv f x :=
  hfc.slope_lt_of_hasDerivAt hx hy hxy hfd.hasDerivAt

end left

section right
/-!
### Strict concave functions, derivative at right endpoint of secant
-/

lemma lt_slope_of_hasDerivWithinAt_Iio (hfc : StrictConcaveOn ℝ S f)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) (hf' : HasDerivWithinAt f f' (Iio y) y) :
    f' < slope f x y hxy.ne := by
  simpa only [Pi.neg_def, slope_neg, neg_neg] using
    neg_lt_neg (hfc.neg.slope_lt_of_hasDerivWithinAt_Iio hx hy hxy hf'.neg)

lemma leftDeriv_lt_slope (hfc : StrictConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableWithinAt ℝ f (Iio y) y) :
    derivWithin f (Iio y) y < slope f x y hxy.ne :=
  hfc.lt_slope_of_hasDerivWithinAt_Iio hx hy hxy hfd.hasDerivWithinAt

lemma lt_slope_of_hasDerivWithinAt (hfc : StrictConcaveOn ℝ S f)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) (hf' : HasDerivWithinAt f f' S y) :
    f' < slope f x y hxy.ne := by
  simpa only [neg_neg, Pi.neg_def, slope_neg] using
    neg_lt_neg (hfc.neg.slope_lt_of_hasDerivWithinAt hx hy hxy hf'.neg)

lemma derivWithin_lt_slope (hfc : StrictConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableWithinAt ℝ f S y) :
    derivWithin f S y < slope f x y hxy.ne :=
  hfc.lt_slope_of_hasDerivWithinAt hx hy hxy hfd.hasDerivWithinAt

lemma lt_slope_of_hasDerivAt (hfc : StrictConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hf' : HasDerivAt f f' y) :
    f' < slope f x y hxy.ne :=
  hfc.lt_slope_of_hasDerivWithinAt_Iio hx hy hxy hf'.hasDerivWithinAt

lemma deriv_lt_slope (hfc : StrictConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y)
    (hfd : DifferentiableAt ℝ f y) :
    deriv f y < slope f x y hxy.ne :=
  hfc.lt_slope_of_hasDerivAt hx hy hxy hfd.hasDerivAt

end right
/-!
### Strict concave functions, anti-monotonicity of derivative
-/

lemma strictAntiOn_derivWithin (hfc : StrictConcaveOn ℝ S f) (hfd : DifferentiableOn ℝ f S) :
    StrictAntiOn (derivWithin f S) S := by
  intro x hx y hy hxy
  exact (hfc.derivWithin_lt_slope hx hy hxy (hfd y hy)).trans
    (hfc.slope_lt_derivWithin hx hy hxy (hfd x hx))

theorem strictAntiOn_deriv (hfc : StrictConcaveOn ℝ S f) (hfd : ∀ x ∈ S, DifferentiableAt ℝ f x) :
    StrictAntiOn (deriv f) S := by
  simpa using (hfc.neg.strictMonoOn_deriv (fun x hx ↦ (hfd x hx).neg)).neg

end StrictConcaveOn

end MirrorImage
