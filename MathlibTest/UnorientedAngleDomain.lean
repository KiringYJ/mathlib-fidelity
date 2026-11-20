/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine

open InnerProductGeometry
open scoped EuclideanGeometry

example (x : {x : ℝ // x ≠ 0}) : ‖NormedSpace.normalize (x : ℝ)‖ = 1 :=
  NormedSpace.norm_normalize _

example (x y : ℝ) (hx hx' : x ≠ 0) (hy hy' : y ≠ 0) :
    angle x y hx hy = angle x y hx' hy' := rfl

example (x : ℝ) {hx : x ≠ 0} : angle x x = 0 := angle_self

example (x y : ℝ) {hx : x ≠ 0} {hy : y ≠ 0} :
    Real.cos (angle x y) * (‖x‖ * ‖y‖) = inner ℝ x y :=
  cos_angle_mul_norm_mul_norm x y

example (x : {p : ℝ × ℝ // p.1 ≠ 0 ∧ p.2 ≠ 0}) :
    ContinuousAt (fun y : {p : ℝ × ℝ // p.1 ≠ 0 ∧ p.2 ≠ 0} ↦
      angle y.1.1 y.1.2 y.2.1 y.2.2) x :=
  continuousAt_angle

-- The affine notation discharges its obligations after elaborating the three points.
example (p q : ℝ) (h : p ≠ q) : ∠ p q p = 0 :=
  EuclideanGeometry.angle_self_of_ne (h := h)

/--
error: could not synthesize default value for parameter 'hx' using tactics
---
error: unsolved goals
⊢ False
-/
#guard_msgs in
noncomputable example : ℝ := angle (0 : ℝ) 1

/--
error: could not synthesize default value for parameter 'hy' using tactics
---
error: unsolved goals
⊢ False
-/
#guard_msgs in
noncomputable example : ℝ := angle (1 : ℝ) 0

/--
error: could not synthesize default value for parameter 'hx' using tactics
---
error: unsolved goals
⊢ False
-/
#guard_msgs in
noncomputable example : ℝ := NormedSpace.normalize (0 : ℝ)
