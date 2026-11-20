/-
Copyright (c) 2021 Yourong Zang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yourong Zang
-/
module

public import Mathlib.Analysis.Calculus.Conformal.NormedSpace
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

/-!
# Angles and conformal maps

This file proves that conformal maps preserve angles.

-/

public section


namespace InnerProductGeometry

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedAddCommGroup F]
variable [InnerProductSpace ℝ E] [InnerProductSpace ℝ F]

theorem IsConformalMap.preserves_angle {f' : E →L[ℝ] F} (h : IsConformalMap f') (u v : E)
    {hu : u ≠ 0} {hv : v ≠ 0} :
    angle (f' u) (f' v) (by simpa only [map_zero] using h.injective.ne hu)
      (by simpa only [map_zero] using h.injective.ne hv) = angle u v := by
  obtain ⟨c, hc, li, rfl⟩ := h
  have hu' : li u ≠ 0 := by simpa only [map_zero] using li.injective.ne hu
  have hv' : li v ≠ 0 := by simpa only [map_zero] using li.injective.ne hv
  exact (angle_smul_smul hc _ _ (hx := hu') (hy := hv')).trans (li.angle_map u v)

private theorem isConformalMap_of_conformalAt {f : E → F} {x : E} {f' : E →L[ℝ] F}
    (h : HasFDerivAt f f' x) (H : ConformalAt f x) : IsConformalMap f' :=
  let ⟨_, h₁, c⟩ := H
  h₁.unique h ▸ c

/-- If a real differentiable map `f` is conformal at a point `x`,
then it preserves the angles at that point. -/
theorem ConformalAt.preserves_angle {f : E → F} {x : E} {f' : E →L[ℝ] F} (h : HasFDerivAt f f' x)
    (H : ConformalAt f x) (u v : E) {hu : u ≠ 0} {hv : v ≠ 0} :
    angle (f' u) (f' v)
      (by simpa only [map_zero] using (isConformalMap_of_conformalAt h H).injective.ne hu)
      (by simpa only [map_zero] using (isConformalMap_of_conformalAt h H).injective.ne hv) =
      angle u v :=
  IsConformalMap.preserves_angle (isConformalMap_of_conformalAt h H) u v

end InnerProductGeometry
