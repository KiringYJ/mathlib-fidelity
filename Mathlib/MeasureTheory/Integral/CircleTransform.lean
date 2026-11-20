/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Circle integral transform

In this file we define the circle integral transform of a function `f` with complex domain. This is
defined as $(2πi)^{-1}\frac{f(x)}{x-w}$ where `x` moves along a circle. We then prove some basic
facts about these functions.

These results are useful for proving that the uniform limit of a sequence of holomorphic functions
is holomorphic.

-/

@[expose] public section


open Set MeasureTheory Metric Function

open scoped Interval Real

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (R : ℝ) (z w : ℂ)

namespace Complex

/-- The Cauchy kernel denominator is invertible at every angle for a pole off the circle. -/
theorem isUnit_circleMap_sub (hw : w ∉ sphere z |R|) (θ : ℝ) :
    IsUnit (circleMap z R θ - w) :=
  (sub_ne_zero.mpr (ne_of_mem_of_not_mem (circleMap_mem_sphere' z R θ) hw)).isUnit

/-- An interior point avoids the contour parameterized by `circleMap`. -/
theorem notMem_circle_of_mem_ball {R : ℝ} {z w : ℂ} (hw : w ∈ ball z R) :
    w ∉ sphere z |R| :=
  fun hs ↦ ((mem_ball.mp hw).trans_le (le_abs_self R)).ne (mem_sphere.mp hs)

/-- Given a function `f : ℂ → E`, `circleTransform R z w f` is the function mapping `θ` to
`(2 * ↑π * I)⁻¹ • deriv (circleMap z R) θ • ((circleMap z R θ) - w)⁻¹ • f (circleMap z R θ)`.
The pole `w` must lie off the contour.

If `f` is differentiable and `w` is in the interior of the ball, then the integral from `0` to
`2 * π` of this gives the value `f(w)`. -/
def circleTransform (hw : w ∉ sphere z |R|) (f : ℂ → E) (θ : ℝ) : E :=
  (2 * ↑π * I)⁻¹ • deriv (circleMap z R) θ •
    Checked.inv (circleMap z R θ - w) (isUnit_circleMap_sub R z w hw θ) • f (circleMap z R θ)

/-- The derivative of `circleTransform` w.r.t. `w`. -/
def circleTransformDeriv (hw : w ∉ sphere z |R|) (f : ℂ → E) (θ : ℝ) : E :=
  (2 * ↑π * I)⁻¹ • deriv (circleMap z R) θ •
    (Checked.inv (circleMap z R θ - w) (isUnit_circleMap_sub R z w hw θ)) ^ 2 •
      f (circleMap z R θ)

theorem circleTransformDeriv_periodic (hw : w ∉ sphere z |R|) (f : ℂ → E) :
    Periodic (circleTransformDeriv R z w hw f) (2 * π) := by
  intro θ
  simp only [circleTransformDeriv, deriv_circleMap, periodic_circleMap z R θ,
    periodic_circleMap 0 R θ]

theorem circleTransformDeriv_eq (hw : w ∉ sphere z |R|) (f : ℂ → E) :
    circleTransformDeriv R z w hw f =
      fun θ ↦ Checked.inv (circleMap z R θ - w) (isUnit_circleMap_sub R z w hw θ) •
        circleTransform R z w hw f θ := by
  funext θ
  simp only [circleTransformDeriv, circleTransform, pow_two, ← mul_smul]
  congr 1
  ac_rfl

theorem integral_circleTransform (hw : w ∉ sphere z |R|) (f : ℂ → E) :
    (∫ θ : ℝ in 0..2 * π, circleTransform R z w hw f θ) =
      (2 * ↑π * I)⁻¹ • circleIntegralOn (fun x : sphere z |R| ↦
        Checked.inv (x.val - w) (sub_ne_zero.mpr (ne_of_mem_of_not_mem x.property hw)).isUnit •
          f x.val) z R := by
  simp only [circleTransform, circleIntegralOn_sphere, intervalIntegral.integral_smul]

theorem continuous_circleTransform {R : ℝ} (hR : 0 < R) {f : ℂ → E} {z w : ℂ}
    (hf : ContinuousOn f <| sphere z R) (hw : w ∈ ball z R) :
    Continuous (circleTransform R z w (notMem_circle_of_mem_ball hw) f) := by
  apply_rules [Continuous.smul, continuous_const]
  · rw [funext <| deriv_circleMap _ _]
    fun_prop
  · exact continuous_circleMap_inv hw
  · apply ContinuousOn.comp_continuous hf (continuous_circleMap z R)
    exact fun _ => (circleMap_mem_sphere _ hR.le) _

theorem continuous_circleTransformDeriv {R : ℝ} (hR : 0 < R) {f : ℂ → E} {z w : ℂ}
    (hf : ContinuousOn f (sphere z R)) (hw : w ∈ ball z R) :
    Continuous (circleTransformDeriv R z w (notMem_circle_of_mem_ball hw) f) := by
  rw [circleTransformDeriv_eq]
  exact (continuous_circleMap_inv hw).smul (continuous_circleTransform hR hf hw)

/-- A useful bound for circle integrals (with complex codomain). -/
def circleTransformBoundingFunction (R : ℝ) (z : ℂ)
    (w : ((sphere z |R|)ᶜ : Set ℂ) × ℝ) : ℂ :=
  circleTransformDeriv R z w.1 w.1.property (fun _ ↦ 1) w.2

theorem continuous_prod_circle_transform_function (R : ℝ) (z : ℂ) :
    Continuous (fun w : ((sphere z |R|)ᶜ : Set ℂ) × ℝ ↦
      (Checked.inv (circleMap z R w.2 - w.1) (isUnit_circleMap_sub R z w.1 w.1.property w.2)) ^
        2) := by
  exact (((continuous_circleMap z R).comp continuous_snd).sub
    (continuous_subtype_val.comp continuous_fst)).fun_inv₀.pow 2

theorem continuous_norm_circleTransformBoundingFunction (R : ℝ) (z : ℂ) :
    Continuous ((‖·‖) ∘ circleTransformBoundingFunction R z) := by
  have h_eq : circleTransformBoundingFunction R z = fun w ↦
    (2 * ↑π * I)⁻¹ * ((circleMap 0 R w.2 * I) *
      (Checked.inv (circleMap z R w.2 - w.1)
        (isUnit_circleMap_sub R z w.1 w.1.property w.2)) ^ 2) := by
    funext w
    unfold circleTransformBoundingFunction circleTransformDeriv
    rw [deriv_circleMap]
    simp only [smul_eq_mul, mul_one]
  rw [h_eq]
  exact (continuous_const.mul ((((continuous_circleMap 0 R).comp continuous_snd).mul
    continuous_const).mul (continuous_prod_circle_transform_function R z))).norm

/-- A point in the smaller closed disk and angular interval is admissible for the Cauchy kernel. -/
def circleTransformBoundingPoint {R r : ℝ} (hr : r < R) {z : ℂ}
    (p : closedBall z r ×ˢ [[0, 2 * π]]) : ((sphere z |R|)ᶜ : Set ℂ) × ℝ :=
  (⟨p.val.1, notMem_circle_of_mem_ball (closedBall_subset_ball hr p.property.1)⟩, p.val.2)

theorem norm_circleTransformBoundingFunction_le {R r : ℝ} (hr : r < R) (hr' : 0 ≤ r) (z : ℂ) :
    ∃ x : closedBall z r ×ˢ [[0, 2 * π]], ∀ y : closedBall z r ×ˢ [[0, 2 * π]],
    ‖circleTransformBoundingFunction R z (circleTransformBoundingPoint hr y)‖ ≤
      ‖circleTransformBoundingFunction R z (circleTransformBoundingPoint hr x)‖ := by
  have hc := (isCompact_closedBall z r).prod (isCompact_uIcc (a := 0) (b := 2 * π))
  have : CompactSpace (closedBall z r ×ˢ [[0, 2 * π]]) := isCompact_iff_compactSpace.mp hc
  have hne : (closedBall z r ×ˢ [[0, 2 * π]]).Nonempty :=
    (nonempty_closedBall.2 hr').prod nonempty_uIcc
  have : Nonempty (closedBall z r ×ˢ [[0, 2 * π]]) := hne.to_subtype
  have hct : Continuous (circleTransformBoundingPoint hr (z := z)) := by
    exact ((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
      (continuous_snd.comp continuous_subtype_val)
  obtain ⟨x, -, hx⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty
    ((continuous_norm_circleTransformBoundingFunction R z).comp hct).continuousOn
  exact ⟨x, fun y ↦ hx (Set.mem_univ y)⟩

/-- The derivative of a `circleTransform` is locally bounded. -/
theorem circleTransformDeriv_bound {R : ℝ} (hR : 0 < R) {z x : ℂ} {f : ℂ → ℂ} (hx : x ∈ ball z R)
    (hf : ContinuousOn f (sphere z R)) : ∃ B ε : ℝ, 0 < ε ∧
      ∃ h : ball x ε ⊆ ball z R, ∀ (t : ℝ), ∀ y (hy : y ∈ ball x ε),
        ‖circleTransformDeriv R z y (notMem_circle_of_mem_ball (h hy)) f t‖ ≤ B := by
  obtain ⟨r, hr, hrx⟩ := exists_lt_mem_ball_of_mem_ball hx
  obtain ⟨ε', hε', H⟩ := exists_ball_subset_ball hrx
  obtain ⟨⟨⟨a, b⟩, ⟨ha, hb⟩⟩, hab⟩ :=
    norm_circleTransformBoundingFunction_le hr (pos_of_mem_ball hrx).le z
  have ha' := notMem_circle_of_mem_ball (closedBall_subset_ball hr ha)
  obtain ⟨X, -, HX2⟩ := (isCompact_sphere z R).exists_isMaxOn
    (NormedSpace.sphere_nonempty.2 hR.le) hf.norm
  refine ⟨‖circleTransformDeriv R z a ha' (fun _ ↦ (1 : ℂ)) b‖ * ‖f X‖, ε', hε',
    H.trans (ball_subset_ball hr.le), fun y v hv ↦ ?_⟩
  have hv' := notMem_circle_of_mem_ball (H.trans (ball_subset_ball hr.le) hv)
  obtain ⟨y1, hy1, hfun⟩ :=
    Periodic.exists_mem_Ico₀ (circleTransformDeriv_periodic R z v hv' f) Real.two_pi_pos y
  have hy2 : y1 ∈ [[0, 2 * π]] := Icc_subset_uIcc <| Ico_subset_Icc_self hy1
  simp only [isMaxOn_iff, mem_sphere_iff_norm] at HX2
  have := mul_le_mul (hab ⟨⟨v, y1⟩, ⟨ball_subset_closedBall (H hv), hy2⟩⟩)
    (HX2 (circleMap z R y1) (mem_sphere_iff_norm.1 (circleMap_mem_sphere z hR.le y1)))
    (norm_nonneg _) (norm_nonneg _)
  rw [hfun]
  simpa [circleTransformBoundingPoint, circleTransformBoundingFunction, circleTransformDeriv,
    mul_assoc] using this

end Complex
