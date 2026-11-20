/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Oliver Nash
-/
module

public import Mathlib.Topology.OpenPartialHomeomorph.Composition
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.Module

/-!
# (Local) homeomorphism between a normed space and a ball

In this file we show that a real (semi)normed vector space is homeomorphic to the unit ball.

We formalize it in two ways:

- as a `Homeomorph`, see `Homeomorph.unitBall`;
- as an `OpenPartialHomeomorph` with `source = Set.univ` and `target = Metric.ball (0 : E) 1`.

The inverse formula is defined on the open unit ball. The ambient inverse field required by
`OpenPartialHomeomorph` extends it anonymously outside that target; the homeomorphism laws
and continuity statements use only its genuine target domain.

We also show that the unit ball `Metric.ball (0 : E) 1` is homeomorphic
to a ball of positive radius in an affine space over `E`, see `OpenPartialHomeomorph.unitBallBall`.

## Tags

homeomorphism, ball
-/

@[expose] public section

open Set Metric
variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable section

open scoped Classical in
/-- Local homeomorphism between a real (semi)normed space and the unit ball.
See also `Homeomorph.unitBall`. -/
def OpenPartialHomeomorph.univUnitBall : OpenPartialHomeomorph E E where
  toFun x := (√(1 + ‖x‖ ^ 2))⁻¹ • x
  invFun y := if hy : y ∈ ball (0 : E) 1 then
    Checked.inv (√(1 - ‖y‖ ^ 2)) (by
      apply Ne.isUnit
      apply Real.sqrt_ne_zero'.mpr
      nlinarith [norm_nonneg y, mem_ball_zero_iff.mp hy]) • y else 0
  source := univ
  target := ball 0 1
  map_source' x _ := by
    have : 0 < 1 + ‖x‖ ^ 2 := by positivity
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_inv, ← _root_.div_eq_inv_mul₀,
      div_lt_one (abs_pos.mpr <| Real.sqrt_ne_zero'.mpr this), ← abs_norm x, ← sq_lt_sq,
      abs_norm, Real.sq_sqrt this.le]
    exact lt_one_add _
  map_target' _ _ := trivial
  left_inv' x _ := by
    have hball : (√(1 + ‖x‖ ^ 2))⁻¹ • x ∈ ball (0 : E) 1 := by
      have hpos : 0 < 1 + ‖x‖ ^ 2 := by positivity
      rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_inv, ← div_eq_inv_mul₀,
        div_lt_one (abs_pos.mpr <| Real.sqrt_ne_zero'.mpr hpos), ← abs_norm x, ← sq_lt_sq,
        abs_norm, Real.sq_sqrt hpos.le]
      exact lt_one_add _
    rw [dite_eq_left hball]
    match_scalars
    simp [norm_smul]
    field_simp
    have hpos : 0 < 1 + ‖x‖ ^ 2 := zero_lt_one_add_norm_sq x
    rw [← Real.sqrt_mul' _ hpos.le]
    conv_lhs => rw [← Real.sqrt_one]
    congr 1
    simp only [sq_abs, Real.sq_sqrt hpos.le]
    field_simp
    ring
  right_inv' y hy := by
    rw [dite_eq_left hy]
    have : 0 < 1 - ‖y‖ ^ 2 := by nlinarith [norm_nonneg y, mem_ball_zero_iff.1 hy]
    match_scalars
    simp [norm_smul]
    field_simp
    rw [← Real.sqrt_mul' _ this.le]
    conv_lhs => rw [← Real.sqrt_one]
    congr 1
    simp only [sq_abs, Real.sq_sqrt this.le]
    field_simp
    ring
  open_source := isOpen_univ
  open_target := isOpen_ball
  continuousOn_toFun := by
    suffices Continuous fun (x : E) => (√(1 + ‖x‖ ^ 2))⁻¹ by fun_prop
    exact Continuous.fun_inv₀ (h0 := fun x ↦
      (Real.sqrt_ne_zero'.mpr (show 0 < 1 + ‖x‖ ^ 2 by positivity)).isUnit) (by fun_prop)
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    have h0 : ∀ y : ball (0 : E) 1, IsUnit (√(1 - ‖(y : E)‖ ^ 2)) := by
      intro y
      apply Ne.isUnit
      apply Real.sqrt_ne_zero'.mpr
      nlinarith [norm_nonneg (y : E), mem_ball_zero_iff.mp y.prop]
    have hc : Continuous (fun y : ball (0 : E) 1 ↦ √(1 - ‖(y : E)‖ ^ 2)) := by fun_prop
    exact ((hc.fun_inv₀ (h0 := h0)).smul continuous_subtype_val).congr
      (fun y ↦ by
        dsimp only [Set.domRestrict, Pi.smul_apply]
        rw [dite_eq_left y.prop]
        rfl)

theorem OpenPartialHomeomorph.univUnitBall_apply (x : E) :
    univUnitBall x = (√(1 + ‖x‖ ^ 2))⁻¹ • x := rfl

/-- The inverse formula is evaluated only on the unit-ball target. -/
theorem OpenPartialHomeomorph.univUnitBall_symm_apply {y : E} (hy : y ∈ ball (0 : E) 1) :
    univUnitBall.symm y = Checked.inv (√(1 - ‖y‖ ^ 2)) (by
      apply Ne.isUnit
      apply Real.sqrt_ne_zero'.mpr
      nlinarith [norm_nonneg y, mem_ball_zero_iff.mp hy]) • y :=
  dite_eq_left hy

theorem OpenPartialHomeomorph.univUnitBall_source : (univUnitBall (E := E)).source = univ := rfl

theorem OpenPartialHomeomorph.univUnitBall_target :
    (univUnitBall (E := E)).target = ball (0 : E) 1 := rfl

@[simp]
theorem OpenPartialHomeomorph.univUnitBall_apply_zero : univUnitBall (0 : E) = 0 := by
  simp [OpenPartialHomeomorph.univUnitBall_apply]

@[simp]
theorem OpenPartialHomeomorph.univUnitBall_symm_apply_zero : univUnitBall.symm (0 : E) = 0 := by
  rw [OpenPartialHomeomorph.univUnitBall_symm_apply (by simp)]
  simp

/-- A (semi) normed real vector space is homeomorphic to the unit ball in the same space.
This homeomorphism sends `x : E` to `(1 + ‖x‖²)^(- ½) • x`.

In many cases the actual implementation is not important, so we don't mark the projection lemmas
`Homeomorph.unitBall_apply_coe` and `Homeomorph.unitBall_symm_apply` as `@[simp]`.

See also `Homeomorph.contDiff_unitBall` and `OpenPartialHomeomorph.contDiffOn_unitBall_symm`
for smoothness properties that hold when `E` is an inner-product space. -/
@[simps! -isSimp]
def Homeomorph.unitBall : E ≃ₜ ball (0 : E) 1 :=
  (Homeomorph.Set.univ _).symm.trans OpenPartialHomeomorph.univUnitBall.toHomeomorphSourceTarget

@[simp]
theorem Homeomorph.coe_unitBall_apply_zero :
    (Homeomorph.unitBall (0 : E) : E) = 0 :=
  OpenPartialHomeomorph.univUnitBall_apply_zero

variable {P : Type*} [PseudoMetricSpace P] [NormedAddTorsor E P]

namespace OpenPartialHomeomorph

/-- Affine homeomorphism `(r • · +ᵥ c)` between a normed space and an add torsor over this space,
interpreted as an `OpenPartialHomeomorph` between `Metric.ball 0 1` and `Metric.ball c r`. -/
@[simps!]
def unitBallBall (c : P) (r : ℝ) (hr : 0 < r) : OpenPartialHomeomorph E P :=
  ((Homeomorph.smulOfNeZero r hr.ne').trans
      (IsometryEquiv.vaddConst c).toHomeomorph).toOpenPartialHomeomorphOfImageEq
      (ball 0 1) isOpen_ball (ball c r) <| by
    change (IsometryEquiv.vaddConst c) ∘ (r • ·) '' ball (0 : E) 1 = ball c r
    rw [image_comp, image_smul, smul_unitBall hr.ne', IsometryEquiv.image_ball]
    simp [abs_of_pos hr]

/-- If `r > 0`, then `OpenPartialHomeomorph.univBall c r` is a smooth open partial homeomorphism
with `source = Set.univ` and `target = Metric.ball c r`.
Otherwise, it is the translation by `c`.
Thus in all cases, it sends `0` to `c`, see `OpenPartialHomeomorph.univBall_apply_zero`. -/
def univBall (c : P) (r : ℝ) : OpenPartialHomeomorph E P :=
  if h : 0 < r then univUnitBall.trans' (unitBallBall c r h) rfl
  else (IsometryEquiv.vaddConst c).toHomeomorph.toOpenPartialHomeomorph

@[simp]
theorem univBall_source (c : P) (r : ℝ) : (univBall c r).source = univ := by
  unfold univBall; split_ifs <;> rfl

theorem univBall_target (c : P) {r : ℝ} (hr : 0 < r) : (univBall c r).target = ball c r := by
  rw [univBall, dite_eq_left hr]; rfl

theorem ball_subset_univBall_target (c : P) (r : ℝ) : ball c r ⊆ (univBall c r).target := by
  by_cases hr : 0 < r
  · rw [univBall_target c hr]
  · rw [univBall, dite_eq_right hr]
    exact subset_univ _

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem univBall_apply_zero (c : P) (r : ℝ) : univBall c r 0 = c := by
  unfold univBall; split_ifs <;> simp

@[simp]
theorem univBall_symm_apply_center (c : P) (r : ℝ) : (univBall c r).symm c = 0 := by
  have : 0 ∈ (univBall c r).source := by simp
  simpa only [univBall_apply_zero] using (univBall c r).left_inv this

@[continuity]
theorem continuous_univBall (c : P) (r : ℝ) : Continuous (univBall c r) := by
  simpa [continuousOn_univ] using (univBall c r).continuousOn

theorem continuousOn_univBall_symm (c : P) (r : ℝ) : ContinuousOn (univBall c r).symm (ball c r) :=
  (univBall c r).symm.continuousOn.mono <| ball_subset_univBall_target c r

end OpenPartialHomeomorph
