/-
Copyright (c) 2026 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo
import Mathlib.Algebra.QuadraticDiscriminant

/-!
# Fixed points of isometries of the upper half-plane

In this file we show that the scalar multiplication by an element `g : GL (Fin 2) ℝ`
has the following set of fixed points, depending on `g`.

- if `g` preserves orientation (i.e., has positive determinant) and is an elliptic matrix,
  then `z ↦ g • z` has a unique fixed point;
- if `g` is a scalar matrix, then it acts by the identity map (proved upstream of this file);
- if `g` preserves orientation, and is a parabolic or a hyperbolic matrix,
  then it has no fixed points;
- if `g` reverses orientation and has zero trace, then it has a geodesic line of fixed points;
  - if `g 1 0 = 0`, then this is the vertical line `re z = g 0 1 / (2 * g 1 1)`;
  - otherwise, it's a half-circle with its center on the real axis;
- if `g` reverses orientation and has nonzero trace, then it has no fixed points.

As a corollary of this classification, we conclude that `PSL(2, ℝ)` acts faithfully
on the upper half-plane.
-/

open Matrix
open scoped MatrixGroups ComplexConjugate

public noncomputable section

namespace UpperHalfPlane

section GLAction

variable {g : GL (Fin 2) ℝ} {z w : ℍ}

theorem gl_smul_eq_iff_num_eq :
    g • z = w ↔ num g z = σ g w * denom g z := by
  rw [← (σ g).injective.eq_iff]
  simp [UpperHalfPlane.ext_iff, coe_smul, div_eq_iff]

/-- The lower-right entry of an invertible upper triangular matrix is nonzero. -/
theorem gl_d_ne_zero_of_c_eq_zero (hc : g 1 0 = 0) : g 1 1 ≠ 0 := by
  intro hd
  simpa [Matrix.det_fin_two, hc, hd] using g.det_ne_zero

/-- If `g` is an upper triangular matrix with trace zero,
then `g` fixes the vertical line `re z = b / (2 * d)`. -/
theorem gl_smul_eq_self_iff_re_eq (htrace : g.val.trace = 0) (hc : g 1 0 = 0) :
    g • z = z ↔ z.re = Checked.div (g 0 1) (2 * g 1 1)
      (mul_ne_zero two_ne_zero (gl_d_ne_zero_of_c_eq_zero hc)).isUnit := by
  rw [Matrix.trace_fin_two, add_eq_zero_iff_eq_neg] at htrace
  have h₀ := gl_d_ne_zero_of_c_eq_zero hc
  have h : g.val.det < 0 := by simp [Matrix.det_fin_two, *]
  simp [gl_smul_eq_iff_num_eq, Complex.ext_iff, htrace, hc, num, denom, σ, h.not_gt, mul_comm,
    eq_div_iff]
  grind

/-- If `g` is an orientation reversing matrix with trace zero and `c ≠ 0`,
then its action on the upper half plane has a half-circle of fixed points.
In the hyperbolic geometry, this half-circle is a line.
If `c = 0`, then this line is a vertical half-line in the usual geometry,
see `gl_smul_eq_self_iff_re_eq`. -/
theorem gl_smul_eq_self_iff_dist_sq_eq (h : g.val.det < 0) (htrace : g.val.trace = 0)
    (hc : g 1 0 ≠ 0) :
    g • z = z ↔ dist (z : ℂ) (-g 1 1 / g 1 0) ^ 2 = (-g.val.det) / g 1 0 ^ 2 := by
  rw [Matrix.trace_fin_two, ← eq_neg_iff_add_eq_zero] at htrace
  rw [eq_div_iff, dist_eq_norm, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    gl_smul_eq_iff_num_eq, σ, g.val_det_apply, ite_eq_right h.not_gt]
  simp only [num, Fin.isValue, htrace, Complex.ofReal_neg, neg_mul, Complex.conjCAE_apply, denom,
    Complex.ext_iff, Complex.add_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_re, coe_re,
    Complex.ofReal_im, coe_im, zero_mul, sub_zero, Complex.conj_re, Complex.conj_im, Complex.add_im,
    Complex.mul_im, add_zero, sub_neg_eq_add, Complex.neg_im, Complex.sub_re, Complex.sub_im,
    pow_two, det_fin_two, neg_sub, fieldEq]
  constructor
  · rintro ⟨hr, _⟩
    linear_combination -g 1 0 * hr
  · intro hr
    constructor
    · apply mul_right_injective₀ hc
      linear_combination -hr
    · ring

/-- If `g` is an orientation reversing matrix with trace zero and `c ≠ 0`,
then its action on the upper half plane has a half-circle of fixed points.
In the hyperbolic geometry, this half-circle is a line. -/
theorem gl_smul_eq_self_iff_dist_eq (h : g.val.det < 0) (htrace : g.val.trace = 0)
    (hc : g 1 0 ≠ 0) :
    g • z = z ↔ dist (z : ℂ) (-g 1 1 / g 1 0) = √(-g.val.det) / |g 1 0| := by
  rw [gl_smul_eq_self_iff_dist_sq_eq h htrace hc, eq_comm, ← Real.sqrt_eq_iff_eq_sq, eq_comm,
    Real.sqrt_div _ (sq_pos_of_ne_zero hc)]
  · simp only [Real.sqrt_sq_eq_abs]
  · positivity [neg_pos.mpr h]
  · exact dist_nonneg

/-- An orientation-reversing isometry of the hyperbolic plane has a fixed point
iff the corresponding matrix has zero trace. -/
theorem exists_gl_smul_eq_self_iff_trace_eq_zero (h : g.val.det < 0) :
    (∃ z : ℍ, g • z = z) ↔ g.val.trace = 0 := by
  constructor
  · rintro ⟨z, hz⟩
    have him := congrArg Complex.im (gl_smul_eq_iff_num_eq.mp hz)
    simp [σ, h.not_gt, num, denom] at him
    rw [Matrix.trace_fin_two]
    apply (mul_eq_zero.mp ?_).resolve_right z.im_ne_zero
    linear_combination him
  · intro hadd
    by_cases hc : g 1 0 = 0
    · have hd := gl_d_ne_zero_of_c_eq_zero hc
      use ⟨⟨g 0 1 / (2 * g 1 1), 1⟩, one_pos⟩
      simp [gl_smul_eq_self_iff_re_eq, *]
    · have hc' : g 1 0 ≠ 0 := hc
      use ⟨⟨Checked.div (-g 1 1) (g 1 0) hc'.isUnit, √(-g.val.det) / |g 1 0|⟩, by
        exact div_pos (Real.sqrt_pos_of_pos (neg_pos.mpr h)) (abs_pos.mpr hc)⟩
      simp [gl_smul_eq_self_iff_dist_sq_eq, *, dist_eq_norm, ← Complex.normSq_eq_norm_sq,
        Complex.normSq_apply, ← pow_two, h.le]

/-- If `g` is an orientation-preserving map,
then the fixed points of its action on the upper half-plane
can be found from a quadratic equation.

If `c ≠ 0`, then this equation has a unique solution in the upper half-plane
given by `UpperHalfPlane.fixedPt`.
If `c = 0`, then the equation degenerates to a linear equation,
which has no solutions in the upper half-plane unless `g` is a scalar matrix.

See also `Matrix.GeneralLinearGroup.fixpointPolynomial_aeval_eq_zero_iff`
for a similar lemma about the action on the projective line,
encoded as `OnePoint R`, where `R` is the ring of coefficients.
-/
theorem gl_smul_eq_self_iff_quadratic (h : 0 < g.val.det) :
    g • z = z ↔ (g 1 0 * (z * z) + (g 1 1 - g 0 0) * z + -g 0 1 : ℂ) = 0 := by
  simp [gl_smul_eq_iff_num_eq, σ, h, num, denom]
  grind

/-- If `g` is a non-scalar orientation preserving matrix with a fixed point in `ℍ`,
then it's an elliptic matrix. -/
theorem isElliptic_of_exists_smul_eq_self (h : 0 < g.val.det) (hgc : g ∉ Subgroup.center _)
    (hfix : ∃ z : ℍ, g • z = z) : g.IsElliptic := by
  rcases hfix with ⟨z, hz⟩
  have hc : g 1 0 ≠ 0 := by
    intro hc
    simp [GeneralLinearGroup.mem_center_iff_val_mem_range_scalar, ← Matrix.ext_iff, hc] at hgc
    simp [gl_smul_eq_iff_num_eq, Complex.ext_iff, σ, h, num, denom, hc, mul_comm, z.im_ne_zero]
      at hz
    grind
  refine lt_of_not_ge fun hge ↦ ?_
  have hd : discrim (g 1 0 : ℂ) (g 1 1 - g 0 0) (-g 0 1) = √g.val.discr * √g.val.discr := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hge]
    simp [discrim, Matrix.discr_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two]
    ring
  rw [gl_smul_eq_self_iff_quadratic h, quadratic_eq_zero_iff (mod_cast hc) hd] at hz
  simp only [← Complex.ofReal_neg, ← Complex.ofReal_sub, ← Complex.ofReal_add,
    ← Complex.ofReal_ofNat, ← Complex.ofReal_mul] at hz
  rcases hz with hz | hz <;>
    exact z.im_ne_zero (by simpa [Complex.div_im] using congrArg Complex.im hz)

/-- The unique fixed point of an orientation-preserving elliptic matrix acting on `ℍ`. -/
def fixedPt (g : GL (Fin 2) ℝ) (hell : g.IsElliptic) : ℍ :=
  have hc := hell.c_ne_zero
  ⟨⟨(g 0 0 - g 1 1) / (2 * g 1 0), √(-g.val.discr) / (2 * |g 1 0|)⟩, by
    exact div_pos (Real.sqrt_pos_of_pos (neg_pos.mpr hell)) (mul_pos two_pos (abs_pos.mpr hc))⟩

@[simp]
theorem fixedPt_neg (hg : (-g).IsElliptic) :
    fixedPt (-g) hg = fixedPt g (isElliptic_neg_iff.mp hg) := by
  apply ext_re_im
  · simp only [fixedPt, Fin.isValue, Units.val_neg, Matrix.neg_apply, sub_neg_eq_add, mul_neg,
      div_neg₀, abs_neg, mk_re]
    rw [← neg_div₀]
    congr 1
    ring
  · simp [fixedPt, Matrix.discr_fin_two, Matrix.det_neg]

/-- The action of an elliptic orientation preserving matrix on `ℍ`
has a unique fixed point given by `fixedPt`. -/
theorem gl_smul_eq_self_iff_eq_fixedPt (hpos : 0 < g.val.det) (hell : g.IsElliptic) :
    g • z = z ↔ z = fixedPt g hell := by
  wlog hc : 0 < g 1 0 generalizing g
  · replace hc := hell.c_ne_zero.lt_or_gt.resolve_right hc
    simpa using @this (-g) (by simpa [Matrix.det_neg]) hell.neg (by simpa)
  have hd : discrim (g 1 0 : ℂ) (g 1 1 - g 0 0) (-g 0 1) = (.I * √(-g.val.discr)) ^ 2 := by
    rw [mul_pow, ← Complex.ofReal_pow, Real.sq_sqrt]
    · simp [discrim, Matrix.discr_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two]
      grind
    · simpa using hell.le
  rw [gl_smul_eq_self_iff_quadratic hpos, quadratic_eq_zero_iff (mod_cast hell.c_ne_zero)
    (hd.trans (pow_two _))]
  rw [or_iff_left]
  · have he : (fixedPt g hell : ℂ) =
        ((g 0 0 : ℂ) - g 1 1 + .I * √(-g.val.discr)) / (2 * (g 1 0 : ℂ)) := by
      have hcu : IsUnit (2 * (g 1 0 : ℂ)) :=
        (mul_ne_zero two_ne_zero (by exact_mod_cast hc.ne')).isUnit
      rw [eq_div_iff]
      apply Complex.ext <;> simp [fixedPt, abs_of_pos hc]
    simp [UpperHalfPlane.ext_iff, he, neg_sub]
  · intro h
    refine z.im_pos.not_ge ?_
    rw [← coe_im, h]
    simp [Complex.div_im, div_nonpos_iff, hc.le, mul_nonneg]

theorem gl_smul_I_eq_I_iff_of_pos {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val) :
    g • I = I ↔ g 0 0 = g 1 1 ∧ g 0 1 = -g 1 0 := by
  rw [gl_smul_eq_iff_num_eq, σ, ite_eq_left hg]
  simp [Complex.ext_iff, num, denom, and_comm]

theorem gl_smul_I_eq_I_iff_of_neg {g : GL (Fin 2) ℝ} (hg : g.det.val < 0) :
    g • I = I ↔ g 0 0 = -g 1 1 ∧ g 0 1 = g 1 0 := by
  rw [gl_smul_eq_iff_num_eq, σ, ite_eq_right (not_lt_of_gt hg)]
  simp [num, denom, Complex.ext_iff, and_comm]

/-- A matrix acts trivially on `ℍ` iff it belongs to the center of `GL(2, ℝ)`,
i.e., it's a diagonal matrix. -/
theorem forall_smul_eq_self_iff_mem_center {g : GL (Fin 2) ℝ} :
    (∀ z : ℍ, g • z = z) ↔ g ∈ Subgroup.center _ := by
  constructor
  · intro hg
    by_contra! hgc
    rcases g.det_ne_zero.lt_or_gt with hlt | hgt
    · obtain ⟨ha, hb⟩ := (gl_smul_I_eq_I_iff_of_neg hlt).mp (hg _)
      rw [eq_neg_iff_add_eq_zero, ← Matrix.trace_fin_two] at ha
      rcases eq_or_ne (g 1 0) 0 with hc | hc
      · specialize hg ⟨1 + .I, by simp⟩
        rw [gl_smul_eq_self_iff_re_eq ha hc] at hg
        simp_all
      · have : 0 < 1 + √(-g.val.det) / |g 1 0| := by simp [add_pos, *]
        specialize hg ⟨⟨Checked.div (-g 1 1) (g 1 0) hc.isUnit, 1 + √(-g.val.det) / |g 1 0|⟩,
          this⟩
        simp [gl_smul_eq_self_iff_dist_eq hlt ha hc, Complex.dist_eq_re_im, Real.sqrt_sq this.le]
          at hg
    · have := isElliptic_of_exists_smul_eq_self hgt hgc ⟨.I, hg _⟩
      contrapose! hg
      simp [gl_smul_eq_self_iff_eq_fixedPt hgt this, exists_ne]
  · aesop (add simp GeneralLinearGroup.center_eq_range_scalar)

end GLAction

instance : FaithfulSMul PGL(2, ℝ) ℍ := by
  rw [faithfulSMul_iff]
  intro g
  cases g
  simp [forall_smul_eq_self_iff_mem_center]

end UpperHalfPlane
