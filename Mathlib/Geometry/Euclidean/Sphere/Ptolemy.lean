/-
Copyright (c) 2021 Manuel Candales. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Candales, Benjamin Davidson
-/
module

public import Mathlib.Geometry.Euclidean.Sphere.Power
public import Mathlib.Geometry.Euclidean.Triangle

/-!
# Ptolemy's theorem

This file proves Ptolemy's theorem on the lengths of the diagonals and sides of a cyclic
quadrilateral.

## Main theorems

* `mul_dist_add_mul_dist_eq_mul_dist_of_cospherical`: Ptolemy’s Theorem (Freek No. 95).

TODO: The current statement of Ptolemy’s theorem works around the lack of a "cyclic polygon" concept
in mathlib, which is what the theorem statement would naturally use (or two such concepts, since
both a strict version, where all vertices must be distinct, and a weak version, where consecutive
vertices may be equal, would be useful; Ptolemy's theorem should then use the weak one).

An API needs to be built around that concept, which would include:
- strict cyclic implies weak cyclic,
- weak cyclic and consecutive points distinct implies strict cyclic,
- weak/strict cyclic implies weak/strict cyclic for any subsequence,
- any three points on a sphere are weakly or strictly cyclic according to whether they are distinct,
- any number of points on a sphere intersected with a two-dimensional affine subspace are cyclic in
  some order,
- a list of points is cyclic if and only if its reversal is,
- a list of points is cyclic if and only if any cyclic permutation is, while other permutations
  are not when the points are distinct,
- a point P where the diagonals of a cyclic polygon cross exists (and is unique) with weak/strict
  betweenness depending on weak/strict cyclicity,
- four points on a sphere with such a point P are cyclic in the appropriate order,

and so on.
-/

public section


open Real

open scoped EuclideanGeometry RealInnerProductSpace Real

namespace EuclideanGeometry

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {P : Type*} [MetricSpace P] [NormedAddTorsor V P]

/-- **Ptolemy's theorem** for cospherical points whose diagonals intersect strictly. -/
theorem mul_dist_add_mul_dist_eq_mul_dist_of_cospherical {a b c d p : P}
    {hap : a ≠ p} {hbp : b ≠ p} {hcp : c ≠ p} {hdp : d ≠ p}
    (h : Cospherical ({a, b, c, d} : Set P)) (hapc : angle a p c hap hcp = π)
    (hbpd : angle b p d hbp hdp = π) :
    dist a b * dist c d + dist b c * dist d a = dist a c * dist b d := by
  have h' : Cospherical ({a, c, b, d} : Set P) := by rwa [Set.insert_comm c b {d}]
  have hmul := mul_dist_eq_mul_dist_of_cospherical_of_angle_eq_pi h' hapc hbpd
  have hbp' := dist_ne_zero.mpr hbp
  have h₁ : dist c d = dist c p / dist b p * dist a b := by
    rw [dist_comm a b]
    apply dist_mul_of_eq_angle_of_dist_mul b p a c p d _ (hab₀ := hbp) (hcb₀ := hap)
      (hab₀' := hcp) (hcb₀' := hdp)
    · exact (angle_comm c p d).trans
        (angle_eq_angle_of_angle_eq_pi_of_angle_eq_pi hbpd hapc).symm
    · exact (div_mul_cancel₀ _).symm
    · rw [div_mul_eq_mul_div₀, eq_div_iff]
      simpa only [mul_comm] using hmul.symm
  have h₂ : dist d a = dist a p / dist b p * dist b c := by
    rw [dist_comm b c]
    apply dist_mul_of_eq_angle_of_dist_mul c p b d p a _ (hab₀ := hcp) (hcb₀ := hbp)
      (hab₀' := hdp) (hcb₀' := hap)
    · exact (angle_eq_angle_of_angle_eq_pi_of_angle_eq_pi hbpd
        ((angle_comm c p a).trans hapc)).symm.trans (angle_comm b p c)
    · rw [div_mul_eq_mul_div₀, eq_div_iff]
      simpa only [mul_comm] using hmul.symm
    · exact (div_mul_cancel₀ _).symm
  have hs := dist_sq_mul_dist_add_dist_sq_mul_dist b a c p hapc
  rw [dist_comm b a] at hs
  rw [h₁, h₂, dist_eq_add_dist_of_angle_eq_pi hbpd]
  simp only [div_mul_eq_mul_div₀, ← mul_div_assoc₀, ← add_div, div_eq_iff]
  linear_combination hs + (dist a c) * hmul

/-- Ptolemy's identity also holds when the diagonals meet at an endpoint. -/
theorem mul_dist_add_mul_dist_eq_mul_dist_of_cospherical_of_wbtw {a b c d p : P}
    (h : Cospherical ({a, b, c, d} : Set P)) (hapc : Wbtw ℝ a p c) (hbpd : Wbtw ℝ b p d) :
    dist a b * dist c d + dist b c * dist d a = dist a c * dist b d := by
  have h' : Cospherical ({a, c, b, d} : Set P) := by rwa [Set.insert_comm c b {d}]
  have hm := mul_dist_eq_mul_dist_of_cospherical h' hapc.mem_affineSpan hbpd.mem_affineSpan
  by_cases h₀ : a = p ∨ b = p ∨ c = p ∨ d = p
  · rcases h₀ with rfl | rfl | rfl | rfl <;>
      simp only [dist_self, zero_mul, mul_zero, zero_eq_mul, mul_eq_zero, dist_eq_zero] at hm <;>
      rcases hm with e | e <;> subst_vars <;> simp [dist_comm, mul_comm]
  push Not at h₀
  obtain ⟨ha, hb, hc, hd⟩ := h₀
  exact mul_dist_add_mul_dist_eq_mul_dist_of_cospherical h
    (Sbtw.angle₁₂₃_eq_pi ⟨hapc, ha.symm, hc.symm⟩)
    (Sbtw.angle₁₂₃_eq_pi ⟨hbpd, hb.symm, hd.symm⟩)

end EuclideanGeometry
