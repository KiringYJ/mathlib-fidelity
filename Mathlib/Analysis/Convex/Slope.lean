/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Malo Jaffré
-/
module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Tactic.AdaptationNote
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

/-!
# Slopes of convex functions

This file relates convexity/concavity of functions in a linearly ordered field and the monotonicity
of their slopes.

The main use is to show convexity/concavity from monotonicity of the derivative.
-/

public section

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] {s : Set 𝕜} {f : 𝕜 → 𝕜}

/-- The combination `(z - y) / (z - x) • x + (y - x) / (z - x) • z` of the endpoints of `[x, z]`
is `y`. -/
private lemma combo_eq_of_lt {x y z : 𝕜} (hxz : x < z) :
    haveI : 0 < z - x := sub_pos.2 hxz
    (z - y) / (z - x) * x + (y - x) / (z - x) * z = y := by
  have : z - x ≠ 0 := (sub_pos.2 hxz).ne'
  field_simp
  ring

/-- The weights `(z - y) / (z - x)` and `(y - x) / (z - x)` sum to one. -/
private lemma weights_add_eq_one_of_lt {x y z : 𝕜} (hxz : x < z) :
    haveI : 0 < z - x := sub_pos.2 hxz
    (z - y) / (z - x) + (y - x) / (z - x) = 1 := by
  rw [← add_div, sub_add_sub_cancel, div_self]

theorem ConvexOn.secant_mono_aux1 (hf : ConvexOn 𝕜 s f) {x y z : 𝕜} (hx : x ∈ s) (hz : z ∈ s)
    (hxy : x < y) (hyz : y < z) : (z - x) * f y ≤ (z - y) * f x + (y - x) * f z := by
  have hxz' : 0 < z - x := sub_pos.2 (hxy.trans hyz)
  have ha : 0 ≤ (z - y) / (z - x) := div_nonneg (sub_pos.2 hyz).le hxz'.le
  have hb : 0 ≤ (y - x) / (z - x) := div_nonneg (sub_pos.2 hxy).le hxz'.le
  have key := hf.map_combo_le hx hz ha hb (weights_add_eq_one_of_lt (hxy.trans hyz))
  simp only [smul_eq_mul, combo_eq_of_lt (hxy.trans hyz)] at key
  calc (z - x) * f y ≤ (z - x) * ((z - y) / (z - x) * f x + (y - x) / (z - x) * f z) :=
        mul_le_mul_of_nonneg_left key hxz'.le
    _ = (z - y) * f x + (y - x) * f z := by
        rw [mul_add, ← mul_assoc, ← mul_assoc, mul_div_cancel₀, mul_div_cancel₀]

theorem StrictConvexOn.secant_strict_mono_aux1 (hf : StrictConvexOn 𝕜 s f) {x y z : 𝕜} (hx : x ∈ s)
    (hz : z ∈ s) (hxy : x < y) (hyz : y < z) : (z - x) * f y < (z - y) * f x + (y - x) * f z := by
  have hxz' : 0 < z - x := sub_pos.2 (hxy.trans hyz)
  have ha : 0 < (z - y) / (z - x) := div_pos (sub_pos.2 hyz) hxz'
  have hb : 0 < (y - x) / (z - x) := div_pos (sub_pos.2 hxy) hxz'
  have key := hf.map_combo_lt hx hz (hxy.trans hyz).ne ha hb
    (weights_add_eq_one_of_lt (hxy.trans hyz))
  simp only [smul_eq_mul, combo_eq_of_lt (hxy.trans hyz)] at key
  calc (z - x) * f y < (z - x) * ((z - y) / (z - x) * f x + (y - x) / (z - x) * f z) :=
        mul_lt_mul_of_pos_left key hxz'
    _ = (z - y) * f x + (y - x) * f z := by
        rw [mul_add, ← mul_assoc, ← mul_assoc, mul_div_cancel₀, mul_div_cancel₀]

/-- If `f : 𝕜 → 𝕜` is convex, then for any three points `x < y < z` the slope of the secant line of
`f` on `[x, y]` is less than the slope of the secant line of `f` on `[y, z]`. -/
theorem ConvexOn.slope_mono_adjacent (hf : ConvexOn 𝕜 s f) {x y z : 𝕜} (hx : x ∈ s) (hz : z ∈ s)
    (hxy : x < y) (hyz : y < z) : (f y - f x) / (y - x) ≤ (f z - f y) / (z - y) := by
  rw [div_le_div_iff₀ (sub_pos.2 hxy) (sub_pos.2 hyz)]
  linear_combination hf.secant_mono_aux1 hx hz hxy hyz

/-- If `f : 𝕜 → 𝕜` is concave, then for any three points `x < y < z` the slope of the secant line of
`f` on `[x, y]` is greater than the slope of the secant line of `f` on `[y, z]`. -/
theorem ConcaveOn.slope_anti_adjacent (hf : ConcaveOn 𝕜 s f) {x y z : 𝕜} (hx : x ∈ s) (hz : z ∈ s)
    (hxy : x < y) (hyz : y < z) : (f z - f y) / (z - y) ≤ (f y - f x) / (y - x) := by
  have := ConvexOn.slope_mono_adjacent hf.neg hx hz hxy hyz
  simp only [Pi.neg_apply] at this
  linear_combination this

/-- If `f : 𝕜 → 𝕜` is strictly convex, then for any three points `x < y < z` the slope of the
secant line of `f` on `[x, y]` is strictly less than the slope of the secant line of `f` on
`[y, z]`. -/
theorem StrictConvexOn.slope_strict_mono_adjacent (hf : StrictConvexOn 𝕜 s f) {x y z : 𝕜}
    (hx : x ∈ s) (hz : z ∈ s) (hxy : x < y) (hyz : y < z) :
    (f y - f x) / (y - x) < (f z - f y) / (z - y) := by
  rw [div_lt_div_iff₀ (sub_pos.2 hxy) (sub_pos.2 hyz)]
  linear_combination hf.secant_strict_mono_aux1 hx hz hxy hyz

/-- If `f : 𝕜 → 𝕜` is strictly concave, then for any three points `x < y < z` the slope of the
secant line of `f` on `[x, y]` is strictly greater than the slope of the secant line of `f` on
`[y, z]`. -/
theorem StrictConcaveOn.slope_anti_adjacent (hf : StrictConcaveOn 𝕜 s f) {x y z : 𝕜} (hx : x ∈ s)
    (hz : z ∈ s) (hxy : x < y) (hyz : y < z) : (f z - f y) / (z - y) < (f y - f x) / (y - x) := by
  have := StrictConvexOn.slope_strict_mono_adjacent hf.neg hx hz hxy hyz
  simp only [Pi.neg_apply] at this
  linear_combination this

/-- If for any three points `x < y < z`, the slope of the secant line of `f : 𝕜 → 𝕜` on `[x, y]` is
less than the slope of the secant line of `f` on `[y, z]`, then `f` is convex. -/
theorem convexOn_of_slope_mono_adjacent (hs : Convex 𝕜 s)
    (hf :
      ∀ {x y z : 𝕜}, x ∈ s → z ∈ s → ∀ (_ : x < y) (_ : y < z),
        (f y - f x) / (y - x) ≤ (f z - f y) / (z - y)) :
    ConvexOn 𝕜 s f :=
  LinearOrder.convexOn_of_lt hs fun x hx z hz hxz a b ha hb hab => by
    simp only [smul_eq_mul]
    have hxy : x < a * x + b * z := by linear_combination b * hxz - x * hab
    have hyz : a * x + b * z < z := by linear_combination a * hxz + z * hab
    have key := hf hx hz hxy hyz
    field_simp [sub_pos.2 hxy, sub_pos.2 hyz] at key
    apply le_of_mul_le_mul_left ?_ (sub_pos.2 hxz)
    linear_combination key + (- f x * z + x * f z) * hab

/-- If for any three points `x < y < z`, the slope of the secant line of `f : 𝕜 → 𝕜` on `[x, y]` is
greater than the slope of the secant line of `f` on `[y, z]`, then `f` is concave. -/
theorem concaveOn_of_slope_anti_adjacent (hs : Convex 𝕜 s)
    (hf :
      ∀ {x y z : 𝕜}, x ∈ s → z ∈ s → ∀ (_ : x < y) (_ : y < z),
        (f z - f y) / (z - y) ≤ (f y - f x) / (y - x)) :
    ConcaveOn 𝕜 s f := by
  rw [← neg_convexOn_iff]
  refine convexOn_of_slope_mono_adjacent hs fun hx hz hxy hyz => ?_
  simp only [Pi.neg_apply]
  linear_combination hf hx hz hxy hyz

/-- If for any three points `x < y < z`, the slope of the secant line of `f : 𝕜 → 𝕜` on `[x, y]` is
strictly less than the slope of the secant line of `f` on `[y, z]`, then `f` is strictly convex. -/
theorem strictConvexOn_of_slope_strict_mono_adjacent (hs : Convex 𝕜 s)
    (hf :
      ∀ {x y z : 𝕜}, x ∈ s → z ∈ s → ∀ (_ : x < y) (_ : y < z),
        (f y - f x) / (y - x) < (f z - f y) / (z - y)) :
    StrictConvexOn 𝕜 s f :=
  LinearOrder.strictConvexOn_of_lt hs fun x hx z hz hxz a b ha hb hab => by
    simp only [smul_eq_mul]
    have hxy : x < a * x + b * z := by linear_combination b * hxz - x * hab
    have hyz : a * x + b * z < z := by linear_combination a * hxz + z * hab
    have key := hf hx hz hxy hyz
    field_simp [sub_pos.2 hxy, sub_pos.2 hyz] at key
    apply lt_of_mul_lt_mul_left ?_ (sub_pos.2 hxz).le
    linear_combination key + (- f x * z + x * f z) * hab

/-- If for any three points `x < y < z`, the slope of the secant line of `f : 𝕜 → 𝕜` on `[x, y]` is
strictly greater than the slope of the secant line of `f` on `[y, z]`, then `f` is strictly concave.
-/
theorem strictConcaveOn_of_slope_strict_anti_adjacent (hs : Convex 𝕜 s)
    (hf :
      ∀ {x y z : 𝕜}, x ∈ s → z ∈ s → ∀ (_ : x < y) (_ : y < z),
        (f z - f y) / (z - y) < (f y - f x) / (y - x)) :
    StrictConcaveOn 𝕜 s f := by
  rw [← neg_strictConvexOn_iff]
  refine strictConvexOn_of_slope_strict_mono_adjacent hs fun hx hz hxy hyz => ?_
  simp only [Pi.neg_apply]
  linear_combination hf hx hz hxy hyz

/-- A function `f : 𝕜 → 𝕜` is convex iff for any three points `x < y < z` the slope of the secant
line of `f` on `[x, y]` is less than the slope of the secant line of `f` on `[y, z]`. -/
theorem convexOn_iff_slope_mono_adjacent :
    ConvexOn 𝕜 s f ↔
      Convex 𝕜 s ∧ ∀ ⦃x y z : 𝕜⦄, x ∈ s → z ∈ s → ∀ (_ : x < y) (_ : y < z),
        (f y - f x) / (y - x) ≤ (f z - f y) / (z - y) :=
  ⟨fun h => ⟨h.convex, fun _ _ _ => h.slope_mono_adjacent⟩, fun h =>
    convexOn_of_slope_mono_adjacent h.1 (@fun _ _ _ hx hy => h.2 hx hy)⟩

/-- A function `f : 𝕜 → 𝕜` is concave iff for any three points `x < y < z` the slope of the secant
line of `f` on `[x, y]` is greater than the slope of the secant line of `f` on `[y, z]`. -/
theorem concaveOn_iff_slope_anti_adjacent :
    ConcaveOn 𝕜 s f ↔
      Convex 𝕜 s ∧
        ∀ ⦃x y z : 𝕜⦄, x ∈ s → z ∈ s → ∀ (_ : x < y) (_ : y < z),
          (f z - f y) / (z - y) ≤ (f y - f x) / (y - x) :=
  ⟨fun h => ⟨h.convex, fun _ _ _ => h.slope_anti_adjacent⟩, fun h =>
    concaveOn_of_slope_anti_adjacent h.1 (@fun _ _ _ hx hy => h.2 hx hy)⟩

/-- A function `f : 𝕜 → 𝕜` is strictly convex iff for any three points `x < y < z` the slope of
the secant line of `f` on `[x, y]` is strictly less than the slope of the secant line of `f` on
`[y, z]`. -/
theorem strictConvexOn_iff_slope_strict_mono_adjacent :
    StrictConvexOn 𝕜 s f ↔
      Convex 𝕜 s ∧
        ∀ ⦃x y z : 𝕜⦄, x ∈ s → z ∈ s → ∀ (_ : x < y) (_ : y < z),
          (f y - f x) / (y - x) < (f z - f y) / (z - y) :=
  ⟨fun h => ⟨h.convex, fun _ _ _ => h.slope_strict_mono_adjacent⟩, fun h =>
    strictConvexOn_of_slope_strict_mono_adjacent h.1 (@fun _ _ _ hx hy => h.2 hx hy)⟩

/-- A function `f : 𝕜 → 𝕜` is strictly concave iff for any three points `x < y < z` the slope of
the secant line of `f` on `[x, y]` is strictly greater than the slope of the secant line of `f` on
`[y, z]`. -/
theorem strictConcaveOn_iff_slope_strict_anti_adjacent :
    StrictConcaveOn 𝕜 s f ↔
      Convex 𝕜 s ∧
        ∀ ⦃x y z : 𝕜⦄, x ∈ s → z ∈ s → ∀ (_ : x < y) (_ : y < z),
          (f z - f y) / (z - y) < (f y - f x) / (y - x) :=
  ⟨fun h => ⟨h.convex, fun _ _ _ => h.slope_anti_adjacent⟩, fun h =>
    strictConcaveOn_of_slope_strict_anti_adjacent h.1 (@fun _ _ _ hx hy => h.2 hx hy)⟩

theorem ConvexOn.secant_mono_aux2 (hf : ConvexOn 𝕜 s f) {x y z : 𝕜} (hx : x ∈ s) (hz : z ∈ s)
    (hxy : x < y) (hyz : y < z) :
    haveI : x < z := hxy.trans hyz
    (f y - f x) / (y - x) ≤ (f z - f x) / (z - x) := by
  rw [div_le_div_iff₀ (sub_pos.2 hxy) (sub_pos.2 (hxy.trans hyz))]
  linear_combination hf.secant_mono_aux1 hx hz hxy hyz

theorem ConvexOn.secant_mono_aux3 (hf : ConvexOn 𝕜 s f) {x y z : 𝕜} (hx : x ∈ s) (hz : z ∈ s)
    (hxy : x < y) (hyz : y < z) :
    haveI : x < z := hxy.trans hyz
    (f z - f x) / (z - x) ≤ (f z - f y) / (z - y) := by
  rw [div_le_div_iff₀ (sub_pos.2 (hxy.trans hyz)) (sub_pos.2 hyz)]
  linear_combination hf.secant_mono_aux1 hx hz hxy hyz

/-- If `f : 𝕜 → 𝕜` is convex, then for any point `a` the slope of the secant line of `f` through `a`
and `b ≠ a` is monotone with respect to `b`. -/
theorem ConvexOn.secant_mono (hf : ConvexOn 𝕜 s f) {a x y : 𝕜} (ha : a ∈ s) (hx : x ∈ s)
    (hy : y ∈ s) (hxa : x ≠ a) (hya : y ≠ a) (hxy : x ≤ y) :
    (f x - f a) / (x - a) ≤ (f y - f a) / (y - a) := by
  rcases eq_or_lt_of_le hxy with (rfl | hxy)
  · simp
  rcases lt_or_gt_of_ne hxa with hxa | hxa
  · rcases lt_or_gt_of_ne hya with hya | hya
    · convert! hf.secant_mono_aux3 hx ha hxy hya using 1 <;> rw [div_eq_div_iff] <;> ring
    · convert! hf.slope_mono_adjacent hx hy hxa hya using 1
      rw [div_eq_div_iff]; ring
  · exact hf.secant_mono_aux2 ha hy hxa hxy

theorem StrictConvexOn.secant_strict_mono_aux2 (hf : StrictConvexOn 𝕜 s f) {x y z : 𝕜} (hx : x ∈ s)
    (hz : z ∈ s) (hxy : x < y) (hyz : y < z) :
    haveI : x < z := hxy.trans hyz
    (f y - f x) / (y - x) < (f z - f x) / (z - x) := by
  rw [div_lt_div_iff₀ (sub_pos.2 hxy) (sub_pos.2 (hxy.trans hyz))]
  linear_combination hf.secant_strict_mono_aux1 hx hz hxy hyz

theorem StrictConvexOn.secant_strict_mono_aux3 (hf : StrictConvexOn 𝕜 s f) {x y z : 𝕜} (hx : x ∈ s)
    (hz : z ∈ s) (hxy : x < y) (hyz : y < z) :
    haveI : x < z := hxy.trans hyz
    (f z - f x) / (z - x) < (f z - f y) / (z - y) := by
  rw [div_lt_div_iff₀ (sub_pos.2 (hxy.trans hyz)) (sub_pos.2 hyz)]
  linear_combination hf.secant_strict_mono_aux1 hx hz hxy hyz

/-- If `f : 𝕜 → 𝕜` is strictly convex, then for any point `a` the slope of the secant line of `f`
through `a` and `b` is strictly monotone with respect to `b`. -/
theorem StrictConvexOn.secant_strict_mono (hf : StrictConvexOn 𝕜 s f) {a x y : 𝕜} (ha : a ∈ s)
    (hx : x ∈ s) (hy : y ∈ s) (hxa : x ≠ a) (hya : y ≠ a) (hxy : x < y) :
    (f x - f a) / (x - a) < (f y - f a) / (y - a) := by
  rcases lt_or_gt_of_ne hxa with hxa | hxa
  · rcases lt_or_gt_of_ne hya with hya | hya
    · convert! hf.secant_strict_mono_aux3 hx ha hxy hya using 1 <;> rw [div_eq_div_iff] <;>
        ring
    · convert! hf.slope_strict_mono_adjacent hx hy hxa hya using 1
      rw [div_eq_div_iff]; ring
  · exact hf.secant_strict_mono_aux2 ha hy hxa hxy

/-- If `f : 𝕜 → 𝕜` is strictly concave, then for any point `a` the slope of the secant line of `f`
through `a` and `b` is strictly antitone with respect to `b`. -/
theorem StrictConcaveOn.secant_strict_mono (hf : StrictConcaveOn 𝕜 s f) {a x y : 𝕜} (ha : a ∈ s)
    (hx : x ∈ s) (hy : y ∈ s) (hxa : x ≠ a) (hya : y ≠ a) (hxy : x < y) :
    (f y - f a) / (y - a) < (f x - f a) / (x - a) := by
  have key := hf.neg.secant_strict_mono ha hx hy hxa hya hxy
  simp only [Pi.neg_apply] at key
  linear_combination key

/-- If `f` is convex on a set `s` in a linearly ordered field, and `f x < f y` for two points
`x < y` in `s`, then `f` is strictly monotone on `s ∩ [y, ∞)`. -/
theorem ConvexOn.strictMonoOn (hf : ConvexOn 𝕜 s f) {x y : 𝕜} (hx : x ∈ s) (hxy : x < y)
    (hxy' : f x < f y) : StrictMonoOn f (s ∩ Set.Ici y) := by
  intro u hu v hv huv
  have step1 : ∀ {z : 𝕜}, z ∈ s ∩ Set.Ioi y → f y < f z := by
    intro z hz
    refine hf.lt_right_of_left_lt hx hz.1 ?_ hxy'
    rw [openSegment_eq_Ioo (hxy.trans hz.2)]
    exact ⟨hxy, hz.2⟩
  rcases eq_or_lt_of_le hu.2 with (rfl | hu2)
  · exact step1 ⟨hv.1, huv⟩
  · refine hf.lt_right_of_left_lt ?_ hv.1 ?_ (step1 ⟨hu.1, hu2⟩)
    · apply hf.convex.segment_subset hx hu.1
      rw [segment_eq_Icc (hxy.le.trans hu.2)]
      exact ⟨hxy.le, hu.2⟩
    · rw [openSegment_eq_Ioo (hu2.trans huv)]
      exact ⟨hu2, huv⟩

/-- If `f` is convex on a set `s` in a linearly ordered field, and `f y < f x` for two points
`x < y` in `s`, then `f` is strictly antitone on `s ∩ (∞, x]`. -/
theorem ConvexOn.strictAntiOn (hf : ConvexOn 𝕜 s f) {x y : 𝕜} (hy : y ∈ s) (hxy : x < y)
    (hxy' : f y < f x) : StrictAntiOn f (s ∩ .Iic x) := by
  have := hf.comp_affineMap (-.id ..) |>.strictMonoOn (by simpa) (neg_lt_neg hxy) (by simpa)
  simpa [Function.comp_def] using this.comp_strictAntiOn strictMonoOn_id.neg fun _ _ ↦ by simpa

/-- If `f` is concave on a set `s` in a linearly ordered field, and `f x < f y` for two points
`x < y` in `s`, then `f` is strictly monotone on `s ∩ (∞, x]`. -/
theorem ConcaveOn.strictMonoOn (hf : ConcaveOn 𝕜 s f) {x y : 𝕜} (hy : y ∈ s) (hxy : x < y)
    (hxy' : f x < f y) : StrictMonoOn f (s ∩ .Iic x) := by
  simpa using (neg_convexOn_iff.mpr hf |>.strictAntiOn hy hxy <| neg_lt_neg hxy').neg

/-- If `f` is concave on a set `s` in a linearly ordered field, and `f y < f x` for two points
`x < y` in `s`, then `f` is strictly antitone on `s ∩ [y, ∞)`. -/
theorem ConcaveOn.strictAntiOn (hf : ConcaveOn 𝕜 s f) {x y : 𝕜} (hx : x ∈ s) (hxy : x < y)
    (hxy' : f y < f x) : StrictAntiOn f (s ∩ .Ici y) := by
  simpa using (neg_convexOn_iff.mpr hf |>.strictMonoOn hx hxy <| neg_lt_neg hxy').neg
