/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Group.AddTorsor

/-!
# Inversion in an affine space

Inversion in an affine space sends `x ≠ c` to the point `y` such that
`y -ᵥ c = (R / dist x c) ^ 2 • (x -ᵥ c)`, where `c` and `R` are the center and radius of the sphere.

Currently, we prove only a few basic lemmas needed to prove Ptolemy's inequality, see
`EuclideanGeometry.mul_dist_le_mul_dist_add_mul_dist`.
-/

@[expose] public section

noncomputable section

open Metric Function AffineMap Set
open scoped Topology

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

namespace EuclideanGeometry

variable {c x y : P} {R : ℝ}

/-- Inversion in a sphere in an affine space, defined away from its center. -/
def inversion (c : P) (R : ℝ) (x : P) (hx : x ≠ c := by aesop) : P :=
  (R / dist x c) ^ 2 • (x -ᵥ c) +ᵥ c

theorem inversion_def (c : P) (R : ℝ) (x : P) {hx : x ≠ c} :
    inversion c R x hx = (R / dist x c) ^ 2 • (x -ᵥ c) +ᵥ c :=
  rfl

/-!
### Basic properties

For nonzero radius, inversion is involutive on the complement of its center. It fixes every point
of the sphere in its domain, and the distance from an image point to the center is
`R ^ 2 / dist x c`.
-/

theorem inversion_eq_lineMap (c : P) (R : ℝ) (x : P) {hx : x ≠ c} :
    inversion c R x hx = lineMap c x ((R / dist x c) ^ 2) :=
  rfl

theorem inversion_vsub_center (c : P) (R : ℝ) (x : P) {hx : x ≠ c} :
    inversion c R x hx -ᵥ c = (R / dist x c) ^ 2 • (x -ᵥ c) :=
  vadd_vsub _ _

@[simp]
theorem inversion_zero_radius (c x : P) {hx : x ≠ c} : inversion c 0 x hx = c := by
  simp [inversion, div_eq_mul_inv₀]

theorem inversion_mul (c : P) (a R : ℝ) (x : P) {hx : x ≠ c} :
    inversion c (a * R) x hx = homothety c (a ^ 2) (inversion c R x hx) := by
  simp only [inversion_eq_lineMap, ← homothety_eq_lineMap, ← homothety_mul_apply, mul_div_assoc₀,
    mul_pow]

@[simp]
theorem inversion_dist_center (c x : P) {hx : x ≠ c} : inversion c (dist x c) x hx = x := by
  rw [inversion, div_self, one_pow, one_smul, vsub_vadd]

@[simp]
theorem inversion_dist_center' (c x : P) {hx : x ≠ c} : inversion c (dist c x) x hx = x := by
  rw [dist_comm, inversion_dist_center]

theorem inversion_of_mem_sphere {hx : x ≠ c} (h : x ∈ Metric.sphere c R) :
    inversion c R x hx = x :=
  h.out ▸ inversion_dist_center c x (hx := hx)

/-- Distance from the image of a point under inversion to the center. -/
theorem dist_inversion_center (c x : P) (R : ℝ) {hx : x ≠ c} :
    dist (inversion c R x hx) c = R ^ 2 / dist x c := by
  have hd : dist x c ≠ 0 := dist_ne_zero.2 hx
  rw [inversion, dist_vadd_left, norm_smul, Real.norm_of_nonneg (sq_nonneg _),
    ← dist_eq_norm_vsub]
  field

/-- Distance from the center of an inversion to the image of a point under the inversion. -/
theorem dist_center_inversion (c x : P) (R : ℝ) {hx : x ≠ c} :
    dist c (inversion c R x hx) = R ^ 2 / dist x c := by
  rw [dist_comm c, dist_inversion_center]

@[simp]
theorem inversion_eq_center {hx : x ≠ c} : inversion c R x hx = c ↔ R = 0 := by
  rw [← dist_eq_zero, dist_inversion_center, div_eq_zero_iff, pow_eq_zero_iff two_ne_zero]

theorem inversion_ne_center {hx : x ≠ c} (hR : R ≠ 0) : inversion c R x hx ≠ c :=
  fun h ↦ hR ((inversion_eq_center (hx := hx)).mp h)

@[simp]
theorem center_eq_inversion {hx : x ≠ c} : c = inversion c R x hx ↔ R = 0 :=
  eq_comm.trans (inversion_eq_center (hx := hx))

@[simp]
theorem inversion_inversion (c : P) {R : ℝ} (hR : R ≠ 0) (x : P) {hx : x ≠ c} :
    inversion c R (inversion c R x hx) (inversion_ne_center (hx := hx) hR) = x := by
  have hd : dist x c ≠ 0 := dist_ne_zero.2 hx
  have hdi : dist (inversion c R x hx) c ≠ 0 :=
    dist_ne_zero.2 (inversion_ne_center (hx := hx) hR)
  have hprod : dist (inversion c R x) c * dist x c = R ^ 2 :=
    (div_eq_iff.mp (dist_inversion_center c x R (hx := hx)).symm).symm
  have hscale : R / dist (inversion c R x) c * (R / dist x c) = 1 := by
    rw [div_mul_div_comm₀, div_eq_iff, one_mul]
    exact (hprod.trans (sq R)).symm
  rw [inversion_def, inversion_vsub_center, smul_smul, ← mul_pow, hscale, one_pow, one_smul,
    vsub_vadd]

/-- Inversion of nonzero radius as an equivalence of the punctured affine space. -/
def inversionEquiv (c : P) {R : ℝ} (hR : R ≠ 0) : {x : P // x ≠ c} ≃ {x : P // x ≠ c} :=
  let f := fun (x : {x : P // x ≠ c}) ↦
    (⟨inversion c R x x.2, inversion_ne_center (hx := x.2) hR⟩ : {x : P // x ≠ c})
  let hf : Involutive f := fun x ↦ Subtype.ext (inversion_inversion c hR x (hx := x.2))
  ⟨f, f, hf, hf⟩

@[simp]
theorem inversionEquiv_symm (c : P) {R : ℝ} (hR : R ≠ 0) :
    (inversionEquiv c hR).symm = inversionEquiv c hR := rfl

@[simp]
theorem coe_inversionEquiv_apply (c : P) {R : ℝ} (hR : R ≠ 0) (x : {x : P // x ≠ c}) :
    (inversionEquiv c hR x : P) = inversion c R x x.2 := rfl

theorem inversion_involutive (c : P) {R : ℝ} (hR : R ≠ 0) : Involutive (inversionEquiv c hR) :=
  (inversionEquiv c hR).left_inv

theorem inversion_surjective (c : P) {R : ℝ} (hR : R ≠ 0) :
    Surjective (inversionEquiv c hR) :=
  (inversionEquiv c hR).surjective

theorem inversion_injective (c : P) {R : ℝ} (hR : R ≠ 0) :
    Injective (fun x : {x : P // x ≠ c} ↦ inversion c R x x.2) :=
  Subtype.val_injective.comp (inversion_involutive c hR).injective

theorem inversion_bijective (c : P) {R : ℝ} (hR : R ≠ 0) :
    Bijective (inversionEquiv c hR) :=
  (inversionEquiv c hR).bijective

/-!
### Similarity of triangles

If inversion with center `O` sends `A` to `A'` and `B` to `B'`, then the triangle `OB'A'` is similar
to the triangle `OAB` with coefficient `R ^ 2 / (|OA|*|OB|)` and the triangle `OA'B` is similar to
the triangle `OAB'` with coefficient `|OB|/|OA|`. We formulate these statements in terms of ratios
of the lengths of their sides.
-/

/-- Distance between the images of two points under an inversion. -/
theorem dist_inversion_inversion (hx : x ≠ c) (hy : y ≠ c) (R : ℝ) :
    dist (inversion c R x) (inversion c R y) = R ^ 2 / (dist x c * dist y c) * dist x y := by
  dsimp only [inversion]
  simp_rw [dist_vadd_cancel_right, dist_eq_norm_vsub V _ c]
  simpa only [dist_vsub_cancel_right] using
    dist_div_norm_sq_smul (vsub_ne_zero.2 hx) (vsub_ne_zero.2 hy) R

theorem dist_inversion_mul_dist_center_eq (hx : x ≠ c) (hy : y ≠ c) :
    dist (inversion c R x) y * dist x c = dist x (inversion c R y) * dist y c := by
  rcases eq_or_ne R 0 with rfl | hR
  · simp [dist_comm, mul_comm]
  have hy' := inversion_ne_center (hx := hy) hR
  have hd : dist x c ≠ 0 := dist_ne_zero.2 hx
  have hdy : dist (inversion c R y) c ≠ 0 := dist_ne_zero.2 hy'
  have hq : R ^ 2 / dist (inversion c R y) c = dist y c := by
    rw [← dist_inversion_center c (inversion c R y) R (hx := hy'),
      inversion_inversion c hR y (hx := hy)]
  calc
    dist (inversion c R x) y * dist x c =
        dist (inversion c R x) (inversion c R (inversion c R y) hy') * dist x c := by
      rw [inversion_inversion c hR y (hx := hy)]
    _ = R ^ 2 / dist (inversion c R y) c * dist x (inversion c R y) := by
      rw [dist_inversion_inversion hx hy']
      field
    _ = dist x (inversion c R y) * dist y c := by rw [hq, mul_comm]

/-!
### Ptolemy's inequality
-/

include V in
/-- **Ptolemy's inequality**: in a quadrangle `ABCD`, `|AC| * |BD| ≤ |AB| * |CD| + |BC| * |AD|`. If
`ABCD` is a convex cyclic polygon, then this inequality becomes an equality, see
`EuclideanGeometry.mul_dist_add_mul_dist_eq_mul_dist_of_cospherical`. -/
theorem mul_dist_le_mul_dist_add_mul_dist (a b c d : P) :
    dist a c * dist b d ≤ dist a b * dist c d + dist b c * dist a d := by
  -- If one of the points `b`, `c`, `d` is equal to `a`, then the inequality is trivial.
  rcases eq_or_ne b a with (rfl | hb)
  · rw [dist_self, zero_mul, zero_add]
  rcases eq_or_ne c a with (rfl | hc)
  · rw [dist_self, zero_mul]
    positivity
  rcases eq_or_ne d a with (rfl | hd)
  · rw [dist_self, mul_zero, add_zero, dist_comm d, dist_comm d, mul_comm]
  /- Otherwise, we apply the triangle inequality to `EuclideanGeometry.inversion a 1 b`,
    `EuclideanGeometry.inversion a 1 c`, and `EuclideanGeometry.inversion a 1 d`. -/
  have H := dist_triangle (inversion a 1 b) (inversion a 1 c) (inversion a 1 d)
  rw [dist_inversion_inversion hb hd, dist_inversion_inversion hb hc,
    dist_inversion_inversion hc hd, one_pow] at H
  rw [← dist_pos] at hb hc hd
  rw [← div_le_div_iff_of_pos_right (mul_pos hb (mul_pos hc hd))]
  convert! H using 1 <;> simp [field, dist_comm a, add_comm]

end EuclideanGeometry

open EuclideanGeometry

/-!
### Continuity of inversion
-/

protected theorem Filter.Tendsto.inversion {α : Type*} {x c : P} {R : ℝ} {l : Filter α}
    {fc fx : α → P} {fR : α → ℝ} {hne' : ∀ a, fx a ≠ fc a}
    (hc : Tendsto fc l (𝓝 c)) (hR : Tendsto fR l (𝓝 R))
    (hx : Tendsto fx l (𝓝 x)) (hne : x ≠ c) :
    Tendsto (fun a ↦ inversion (fc a) (fR a) (fx a) (hne' a)) l (𝓝 (inversion c R x)) :=
  (((hR.div₀ (hx.dist hc) (h₀ := fun a ↦ (dist_ne_zero.2 (hne' a)).isUnit)
    (hb := (dist_ne_zero.2 hne).isUnit)).pow 2).smul (hx.vsub hc)).vadd hc

variable {X : Type*} [TopologicalSpace X] {c x : X → P} {R : X → ℝ} {a₀ : X} {s : Set X}
  {hne : ∀ a, x a ≠ c a}

protected nonrec theorem ContinuousWithinAt.inversion (hc : ContinuousWithinAt c s a₀)
    (hR : ContinuousWithinAt R s a₀) (hx : ContinuousWithinAt x s a₀) :
    ContinuousWithinAt (fun a ↦ inversion (c a) (R a) (x a) (hne a)) s a₀ :=
  hc.inversion hR hx (hne a₀)

protected nonrec theorem ContinuousAt.inversion (hc : ContinuousAt c a₀) (hR : ContinuousAt R a₀)
    (hx : ContinuousAt x a₀) :
    ContinuousAt (fun a ↦ inversion (c a) (R a) (x a) (hne a)) a₀ :=
  hc.inversion hR hx (hne a₀)

protected theorem ContinuousOn.inversion (hc : ContinuousOn c s) (hR : ContinuousOn R s)
    (hx : ContinuousOn x s) :
    ContinuousOn (fun a ↦ inversion (c a) (R a) (x a) (hne a)) s := fun a ha ↦
  (hc a ha).inversion (hR a ha) (hx a ha)

protected theorem Continuous.inversion (hc : Continuous c) (hR : Continuous R) (hx : Continuous x) :
    Continuous (fun a ↦ inversion (c a) (R a) (x a) (hne a)) :=
  continuous_iff_continuousAt.2 fun _ ↦
    hc.continuousAt.inversion hR.continuousAt hx.continuousAt

namespace EuclideanGeometry

open Filter in
/-- The inversion of a point tends to infinity as it approaches the center of an inversion. -/
theorem tendsto_inversion_nhdsNE_center_cobounded {c : P} {R : ℝ} (hR : R ≠ 0) :
    Tendsto (fun x : {x : P // x ≠ c} ↦ inversion c R x x.2)
      (comap Subtype.val (𝓝 c)) (Bornology.cobounded P) := by
  rw [← tendsto_dist_left_atTop_iff c]
  have hdist : Tendsto (fun x : {x : P // x ≠ c} ↦ dist (x : P) c)
      (comap Subtype.val (𝓝 c)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have h : Tendsto (fun x : P ↦ dist x c) (𝓝 c) (𝓝 (dist c c)) :=
        continuousAt_id.dist continuousAt_const
      simpa only [Function.comp_def, dist_self] using h.comp tendsto_comap
    · exact .of_forall fun x ↦ dist_pos.2 x.2
  simpa only [Function.comp_def, dist_center_inversion, div_eq_mul_inv₀] using
    (hdist.fun_inv_tendsto_nhdsGT_zero
      (h0 := fun x ↦ (dist_ne_zero.2 x.2).isUnit)).const_mul_atTop (sq_pos_of_ne_zero hR)

end EuclideanGeometry
