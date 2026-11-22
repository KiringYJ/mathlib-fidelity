/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Calculus.DiffContOnCl
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.Complex.ReImTopology
public import Mathlib.Analysis.Real.Cardinality
public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Cauchy integral formula

In this file we prove the Cauchy-Goursat theorem and the Cauchy integral formula for integrals over
circles. Most results are formulated for a function `f : ℂ → E` that takes values in a complex
Banach space with second countable topology.

## Main statements

In the following theorems, if the name ends with `off_countable`, then the actual theorem assumes
differentiability at all but countably many points of the set mentioned below.

### Rectangle integrals

* `Complex.integral_boundary_rect_of_hasFDerivAt_real_off_countable`: If a function
  `f : ℂ → E` is continuous on a closed rectangle and *real* differentiable on its interior, then
  its integral over the boundary of this rectangle is equal to the integral of
  `I • f' (x + y * I) 1 - f' (x + y * I) I` over the rectangle, where `f' z w : E` is the derivative
  of `f` at `z` in the direction `w` and `I = Complex.I` is the imaginary unit.

* `Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable`: If a function
  `f : ℂ → E` is continuous on a closed rectangle and is *complex* differentiable on its interior,
  then its integral over the boundary of this rectangle is equal to zero.

### Annuli and circles

* `Complex.circleIntegral_sub_center_inv_smul_eq_of_differentiable_on_annulus_off_countable`: If a
  function `f : ℂ → E` is continuous on a closed annulus `{z | r ≤ |z - c| ≤ R}` and is complex
  differentiable on its interior `{z | r < |z - c| < R}`, then the integrals of `(z - c)⁻¹ • f z`
  over the outer boundary and over the inner boundary are equal.

* `Complex.circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable_of_tendsto`,
  `Complex.circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable`:
  If a function `f : ℂ → E` is continuous on a punctured closed disc `{z | |z - c| ≤ R ∧ z ≠ c}`, is
  complex differentiable on the corresponding punctured open disc, and tends to `y` as `z → c`,
  `z ≠ c`, then the integral of `(z - c)⁻¹ • f z` over the circle `|z - c| = R` is equal to
  `2πiy`. In particular, if `f` is continuous on the whole closed disc and is complex differentiable
  on the corresponding open disc, then this integral is equal to `2πif(c)`.

* `Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable`,
  `Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable`
  **Cauchy integral formula**: if `f : ℂ → E` is continuous on a closed disc of radius `R` and is
  complex differentiable on the corresponding open disc, then for any `w` in the corresponding open
  disc the integral of `(z - w)⁻¹ • f z` over the boundary of the disc is equal to `2πif(w)`.
  Two versions of the lemma put the multiplier `2πi` at the different sides of the equality.

### Analyticity

* `Complex.hasFPowerSeriesOnBall_of_differentiable_off_countable`: If `f : ℂ → E` is continuous
  on a closed disc of positive radius and is complex differentiable on the corresponding open disc,
  then it is analytic on the corresponding open disc, and the coefficients of the power series are
  given by Cauchy integral formulas.

* `DifferentiableOn.hasFPowerSeriesOnBall`: If `f : ℂ → E` is complex differentiable on a
  closed disc of positive radius, then it is analytic on the corresponding open disc, and the
  coefficients of the power series are given by Cauchy integral formulas.

* `DifferentiableOn.exists_hasFPowerSeriesOnBall`: If `f : D → E` is complex differentiable
  in embedded coordinates on a closed disc covered by the coordinate image, it admits a power
  series on the corresponding open disc.

* `DifferentiableOn.analyticAt`, `Differentiable.analyticAt`: If `f : ℂ → E` is differentiable
  on a neighborhood of a point, then it is analytic at this point. In particular, if `f : ℂ → E`
  is differentiable on the whole `ℂ`, then it is analytic at every point `z : ℂ`.

* `Differentiable.hasFPowerSeriesOnBall`: If `f : ℂ → E` is differentiable everywhere then the
  `cauchyPowerSeries f z R` is a formal power series representing `f` at `z` with infinite
  radius of convergence (this holds for any choice of `0 < R`).

### Higher derivatives

* `Complex.circleIntegral_one_div_sub_center_pow_smul_of_differentiable_on_off_countable`
  **Cauchy integral formula for derivatives**: formula for the higher derivatives of `f` at the
  centre `c` of a disc in terms of circle integrals of `f w / (w - c) ^ (n + 1)` around the
  boundary circle.

## Implementation details

The proof of the Cauchy integral formula in this file is based on a very general version of the
divergence theorem, see `MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable`
(a version for functions defined on `Fin (n + 1) → ℝ`),
`MeasureTheory.integral_divergence_prod_Icc_of_hasFDerivWithinAt_off_countable_of_le`, and
`MeasureTheory.integral2_divergence_prod_of_hasFDerivWithinAt_off_countable` (versions for
functions defined on `ℝ × ℝ`).

Usually, the divergence theorem is formulated for a $C^1$ smooth function. The theorems formulated
above deal with a function that is

* continuous on a closed box/rectangle;
* differentiable at all but countably many points of its interior;
* have divergence integrable over the closed box/rectangle.

First, we reformulate the theorem for a *real*-differentiable map `ℂ → E`, and relate the integral
of `f` over the boundary of a rectangle in `ℂ` to the integral of the derivative
$\frac{\partial f}{\partial \bar z}$ over the interior of this box. In particular, for a *complex*
differentiable function, the latter derivative is zero, hence the integral over the boundary of a
rectangle is zero. Thus we get the Cauchy-Goursat theorem for a rectangle in `ℂ`.

Next, we apply this theorem to the function $F(z)=f(c+e^{z})$ on the rectangle
$[\ln r, \ln R]\times [0, 2\pi]$ to prove that
$$
  \oint_{|z-c|=r}\frac{f(z)\,dz}{z-c}=\oint_{|z-c|=R}\frac{f(z)\,dz}{z-c}
$$
provided that `f` is continuous on the closed annulus `r ≤ |z - c| ≤ R` and is complex
differentiable on its interior `r < |z - c| < R` (possibly, at all but countably many points).

Here and below, we write $\frac{f(z)}{z-c}$ in the documentation while the actual lemmas use
`(z - c)⁻¹ • f z` because `f z` belongs to some Banach space over `ℂ` and `f z / (z - c)` is
undefined.

Taking the limit of this equality as `r` tends to `𝓝[>] 0`, we prove
$$
  \oint_{|z-c|=R}\frac{f(z)\,dz}{z-c}=2\pi if(c)
$$
provided that `f` is continuous on the closed disc `|z - c| ≤ R` and is differentiable at all but
countably many points of its interior. This is the Cauchy integral formula for the center of a
circle. In particular, if we apply this function to `F z = (z - c) • f z`, then we get
$$
  \oint_{|z-c|=R} f(z)\,dz=0.
$$

In order to deduce the Cauchy integral formula for any point `w`, `|w - c| < R`, we consider the
slope function `g : ℂ → E` given by `g z = (z - w)⁻¹ • (f z - f w)` if `z ≠ w` and `g w = f' w`.
This function satisfies assumptions of the previous theorem, so we have
$$
  \oint_{|z-c|=R} \frac{f(z)\,dz}{z-w}=\oint_{|z-c|=R} \frac{f(w)\,dz}{z-w}=
  \left(\oint_{|z-c|=R} \frac{dz}{z-w}\right)f(w).
$$
The latter integral was computed in `circleIntegral.integral_sub_inv_of_mem_ball` and is equal to
`2 * π * Complex.I`.

There is one more step in the actual proof. Since we allow `f` to be non-differentiable on a
countable set `s`, we cannot immediately claim that `g` is continuous at `w` if `w ∈ s`. So, we use
the proof outlined in the previous paragraph for `w ∉ s` (see
`Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable_aux`), then use continuity
of both sides of the formula and density of `sᶜ` to prove the formula for all points of the open
ball, see `Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable`.

Finally, we use the properties of the Cauchy integrals established elsewhere (see
`hasFPowerSeriesOn_cauchy_integral`) and Cauchy integral formula to prove that the original
function is analytic on the open ball.

## Tags

Cauchy-Goursat theorem, Cauchy integral formula
-/

public section

open TopologicalSpace Set MeasureTheory intervalIntegral Metric Filter Function

open scoped Interval Real NNReal ENNReal Topology

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]

namespace Complex

section rectangle
/-!
## Functions on rectangles
-/

/-- Suppose that a function `f : ℂ → E` is continuous on a closed rectangle with opposite corners at
`z w : ℂ`, is *real* differentiable at all but countably many points of the corresponding open
rectangle, and $\frac{\partial f}{\partial \bar z}$ is integrable on this rectangle. Then the
integral of `f` over the boundary of the rectangle is equal to the integral of
$2i\frac{\partial f}{\partial \bar z}=i\frac{\partial f}{\partial x}-\frac{\partial f}{\partial y}$
over the rectangle. -/
theorem integral_boundary_rect_of_hasFDerivAt_real_off_countable (f : ℂ → E) (f' : ℂ → ℂ →L[ℝ] E)
    (z w : ℂ) (s : Set ℂ) (hs : s.Countable)
    (Hc : ContinuousOn f ([[z.re, w.re]] ×ℂ [[z.im, w.im]]))
    (Hd : ∀ x ∈ Ioo (min z.re w.re) (max z.re w.re) ×ℂ Ioo (min z.im w.im) (max z.im w.im) \ s,
      HasFDerivAt f (f' x) x)
    (Hi : IntegrableOn (fun z => I • f' z 1 - f' z I) ([[z.re, w.re]] ×ℂ [[z.im, w.im]])) :
    (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
      I • (∫ y : ℝ in z.im..w.im, f (re w + y * I)) -
      I • ∫ y : ℝ in z.im..w.im, f (re z + y * I) =
      ∫ x : ℝ in z.re..w.re, ∫ y : ℝ in z.im..w.im, I • f' (x + y * I) 1 - f' (x + y * I) I := by
  set e : (ℝ × ℝ) ≃L[ℝ] ℂ := equivRealProdCLM.symm
  have he : ∀ x y : ℝ, ↑x + ↑y * I = e (x, y) := fun x y => (mk_eq_add_mul_I x y).symm
  have he₁ : e (1, 0) = 1 := rfl; have he₂ : e (0, 1) = I := rfl
  simp only [he] at *
  set F : ℝ × ℝ → E := f ∘ e
  set F' : ℝ × ℝ → ℝ × ℝ →L[ℝ] E := fun p => (f' (e p)).comp (e : ℝ × ℝ →L[ℝ] ℂ)
  have hF' : ∀ p : ℝ × ℝ, (-(I • F' p)) (1, 0) + F' p (0, 1) = -(I • f' (e p) 1 - f' (e p) I) := by
    rintro ⟨x, y⟩
    simp only [F', neg_apply, smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, he₁, he₂, neg_add_eq_sub, neg_sub]
  set R : Set (ℝ × ℝ) := [[z.re, w.re]] ×ˢ [[w.im, z.im]]
  set t : Set (ℝ × ℝ) := e ⁻¹' s
  rw [uIcc_comm z.im] at Hc Hi; rw [min_comm z.im, max_comm z.im] at Hd
  have hR : e ⁻¹' ([[z.re, w.re]] ×ℂ [[w.im, z.im]]) = R := rfl
  have htc : ContinuousOn F R := Hc.comp e.continuousOn hR.ge
  have htd :
    ∀ p ∈ Ioo (min z.re w.re) (max z.re w.re) ×ˢ Ioo (min w.im z.im) (max w.im z.im) \ t,
      HasFDerivAt F (F' p) p :=
    fun p hp => (Hd (e p) hp).comp p e.hasFDerivAt
  simp_rw [← intervalIntegral.integral_smul, intervalIntegral.integral_symm w.im z.im, ←
    intervalIntegral.integral_neg, ← hF']
  refine (integral2_divergence_prod_of_hasFDerivAt_off_countable (fun p => -(I • F p)) F
    (fun p => -(I • F' p)) F' z.re w.im w.re z.im t (hs.preimage e.injective)
    (htc.const_smul _).neg htc (fun p hp => ((htd p hp).const_smul I).neg) htd ?_).symm
  rw [← (volume_preserving_equiv_real_prod.symm _).integrableOn_comp_preimage
    (MeasurableEquiv.measurableEmbedding _)] at Hi
  simpa only [hF'] using! Hi.neg

/-- Suppose that a function `f : ℂ → E` is continuous on a closed rectangle with opposite corners at
`z w : ℂ`, is *real* differentiable on the corresponding open rectangle, and
$\frac{\partial f}{\partial \bar z}$ is integrable on this rectangle. Then the integral of `f` over
the boundary of the rectangle is equal to the integral of
$2i\frac{\partial f}{\partial \bar z}=i\frac{\partial f}{\partial x}-\frac{\partial f}{\partial y}$
over the rectangle. -/
theorem integral_boundary_rect_of_continuousOn_of_hasFDerivAt_real (f : ℂ → E) (f' : ℂ → ℂ →L[ℝ] E)
    (z w : ℂ) (Hc : ContinuousOn f ([[z.re, w.re]] ×ℂ [[z.im, w.im]]))
    (Hd : ∀ x ∈ Ioo (min z.re w.re) (max z.re w.re) ×ℂ Ioo (min z.im w.im) (max z.im w.im),
      HasFDerivAt f (f' x) x)
    (Hi : IntegrableOn (fun z => I • f' z 1 - f' z I) ([[z.re, w.re]] ×ℂ [[z.im, w.im]])) :
    (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
      I • (∫ y : ℝ in z.im..w.im, f (re w + y * I)) -
      I • (∫ y : ℝ in z.im..w.im, f (re z + y * I)) =
      ∫ x : ℝ in z.re..w.re, ∫ y : ℝ in z.im..w.im, I • f' (x + y * I) 1 - f' (x + y * I) I :=
  integral_boundary_rect_of_hasFDerivAt_real_off_countable f f' z w ∅ countable_empty Hc
    (fun x hx => Hd x hx.1) Hi

/-- Suppose that a function `f : ℂ → E` is *real* differentiable on a closed rectangle with opposite
corners at `z w : ℂ` and $\frac{\partial f}{\partial \bar z}$ is integrable on this rectangle. Then
the integral of `f` over the boundary of the rectangle is equal to the integral of
$2i\frac{\partial f}{\partial \bar z}=i\frac{\partial f}{\partial x}-\frac{\partial f}{\partial y}$
over the rectangle. -/
theorem integral_boundary_rect_of_differentiableOn_real (f : ℂ → E) (z w : ℂ)
    (Hd : DifferentiableOn ℝ f ([[z.re, w.re]] ×ℂ [[z.im, w.im]]))
    (Hi : IntegrableOn (fun z => I • fderiv ℝ f z id 1 - fderiv ℝ f z id I)
      ([[z.re, w.re]] ×ℂ [[z.im, w.im]])) :
    (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
      I • (∫ y : ℝ in z.im..w.im, f (re w + y * I)) -
      I • (∫ y : ℝ in z.im..w.im, f (re z + y * I)) =
      ∫ x : ℝ in z.re..w.re, ∫ y : ℝ in z.im..w.im,
        I • fderiv ℝ f (x + y * I) id 1 - fderiv ℝ f (x + y * I) id I :=
  integral_boundary_rect_of_hasFDerivAt_real_off_countable f (fun x ↦ fderiv ℝ f x id)
    z w ∅ countable_empty
    Hd.continuousOn
    (fun x hx => Hd.hasFDerivAt <| by
      simpa only [← mem_interior_iff_mem_nhds, interior_reProdIm, uIcc, interior_Icc] using hx.1)
    Hi

/-- **Cauchy-Goursat theorem** for a rectangle: the integral of a complex differentiable function
over the boundary of a rectangle equals zero. More precisely, if `f` is continuous on a closed
rectangle and is complex differentiable at all but countably many points of the corresponding open
rectangle, then its integral over the boundary of the rectangle equals zero. -/
theorem integral_boundary_rect_eq_zero_of_differentiable_on_off_countable (f : ℂ → E) (z w : ℂ)
    (s : Set ℂ) (hs : s.Countable) (Hc : ContinuousOn f ([[z.re, w.re]] ×ℂ [[z.im, w.im]]))
    (Hd : ∀ x ∈ Ioo (min z.re w.re) (max z.re w.re) ×ℂ Ioo (min z.im w.im) (max z.im w.im) \ s,
      DifferentiableAt ℂ f x) :
    (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
      I • (∫ y : ℝ in z.im..w.im, f (re w + y * I)) -
      I • (∫ y : ℝ in z.im..w.im, f (re z + y * I)) = 0 := by
  refine (integral_boundary_rect_of_hasFDerivAt_real_off_countable f
    (fun z => (fderiv ℂ f z id).restrictScalars ℝ) z w s hs Hc
    (fun x hx => (Hd x hx).hasFDerivAt.restrictScalars ℝ) ?_).trans ?_ <;>
      simp

/-- **Cauchy-Goursat theorem for a rectangle**: the integral of a complex differentiable function
over the boundary of a rectangle equals zero. More precisely, if `f` is continuous on a closed
rectangle and is complex differentiable on the corresponding open rectangle, then its integral over
the boundary of the rectangle equals zero. -/
theorem integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn (f : ℂ → E) (z w : ℂ)
    (Hc : ContinuousOn f ([[z.re, w.re]] ×ℂ [[z.im, w.im]]))
    (Hd : DifferentiableOn ℂ f
      (Ioo (min z.re w.re) (max z.re w.re) ×ℂ Ioo (min z.im w.im) (max z.im w.im))) :
    (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
      I • (∫ y : ℝ in z.im..w.im, f (re w + y * I)) -
      I • (∫ y : ℝ in z.im..w.im, f (re z + y * I)) = 0 :=
  integral_boundary_rect_eq_zero_of_differentiable_on_off_countable f z w ∅ countable_empty Hc
    fun _x hx => Hd.differentiableAt <| (isOpen_Ioo.reProdIm isOpen_Ioo).mem_nhds hx.1

/-- **Cauchy-Goursat theorem** for a rectangle: the integral of a complex differentiable function
over the boundary of a rectangle equals zero. More precisely, if `f` is complex differentiable on a
closed rectangle, then its integral over the boundary of the rectangle equals zero. -/
theorem integral_boundary_rect_eq_zero_of_differentiableOn (f : ℂ → E) (z w : ℂ)
    (H : DifferentiableOn ℂ f ([[z.re, w.re]] ×ℂ [[z.im, w.im]])) :
    (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
      I • (∫ y : ℝ in z.im..w.im, f (re w + y * I)) -
      I • (∫ y : ℝ in z.im..w.im, f (re z + y * I)) = 0 :=
  integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn f z w H.continuousOn <|
    H.mono <|
      inter_subset_inter (preimage_mono Ioo_subset_Icc_self) (preimage_mono Ioo_subset_Icc_self)

end rectangle

section annulus
/-!
## Functions on annuli
-/

private theorem circleIntegralOn_sub_center_inv_smul_eq_intervalIntegral
    {c : ℂ} {R : ℝ} (hR : R ≠ 0) (f : ℂ → E) :
    circleIntegralOn (fun z : sphere c |R| ↦
      Checked.inv (z.val - c) (isUnit_sub_center_of_mem_sphere hR.isUnit z) • f z.val) c R =
      ∫ θ in 0..2 * π, I • f (circleMap c R θ) := by
  rw [circleIntegralOn_sphere]
  congr 1
  funext θ
  rw [deriv_circleMap, ← circleMap_sub_center c R θ, smul_smul,
    mul_comm _ I, mul_assoc, mul_inv_cancel₀, mul_one]

/-- If `f : ℂ → E` is continuous on the closed annulus `r ≤ ‖z - c‖ ≤ R`, `0 < r ≤ R`,
and is complex differentiable at all but countably many points of its interior,
then the integrals of `f z / (z - c)` (formally, `(z - c)⁻¹ • f z`)
over the circles `‖z - c‖ = r` and `‖z - c‖ = R` are equal to each other. -/
theorem circleIntegral_sub_center_inv_smul_eq_of_differentiable_on_annulus_off_countable {c : ℂ}
    {r R : ℝ} (h0 : 0 < r) (hle : r ≤ R) {f : ℂ → E} {s : Set ℂ} (hs : s.Countable)
    (hc : ContinuousOn f (closedBall c R \ ball c r))
    (hd : ∀ z ∈ (ball c R \ closedBall c r) \ s, DifferentiableAt ℂ f z) :
    circleIntegralOn (fun z : sphere c |R| ↦ Checked.inv (z.val - c)
      (isUnit_sub_center_of_mem_sphere (h0.trans_le hle).ne'.isUnit z) • f z.val) c R =
    circleIntegralOn (fun z : sphere c |r| ↦ Checked.inv (z.val - c)
      (isUnit_sub_center_of_mem_sphere h0.ne'.isUnit z) • f z.val) c r := by
  rw [circleIntegralOn_sub_center_inv_smul_eq_intervalIntegral (h0.trans_le hle).ne',
    circleIntegralOn_sub_center_inv_smul_eq_intervalIntegral h0.ne']
  /- We apply the previous lemma to `fun z ↦ f (c + exp z)` on the rectangle
    `[log r, log R] × [0, 2 * π]`. -/
  set A := closedBall c R \ ball c r
  obtain ⟨a, rfl⟩ : ∃ a, Real.exp a = r := ⟨Real.log r, Real.exp_log h0⟩
  obtain ⟨b, rfl⟩ : ∃ b, Real.exp b = R := ⟨Real.log R, Real.exp_log (h0.trans_le hle)⟩
  rw [Real.exp_le_exp] at hle
  set R := [[a, b]] ×ℂ [[0, 2 * π]]
  set g : ℂ → ℂ := (c + exp ·)
  have hdg : Differentiable ℂ g := differentiable_exp.const_add _
  replace hs : (g ⁻¹' s).Countable := (hs.preimage (add_right_injective c)).preimage_cexp
  have h_maps : MapsTo g R A := by
    rintro z ⟨h, -⟩; simpa [g, A, dist_eq, norm_exp, hle] using h.symm
  replace hc : ContinuousOn (f ∘ g) R := hc.comp hdg.continuous.continuousOn h_maps
  replace hd : ∀ z ∈ Ioo (min a b) (max a b) ×ℂ Ioo (min 0 (2 * π)) (max 0 (2 * π)) \ g ⁻¹' s,
      DifferentiableAt ℂ (f ∘ g) z := by
    refine fun z hz => (hd (g z) ⟨?_, hz.2⟩).comp z (hdg _)
    simpa [g, dist_eq, norm_exp, hle, and_comm] using hz.1.1
  simpa [g, circleMap, exp_periodic _, sub_eq_zero, ← exp_add] using
    integral_boundary_rect_eq_zero_of_differentiable_on_off_countable _ ⟨a, 0⟩ ⟨b, 2 * π⟩ _ hs hc hd

/-- **Cauchy-Goursat theorem** for an annulus. If `f : ℂ → E` is continuous on the closed annulus
`r ≤ ‖z - c‖ ≤ R`, `0 < r ≤ R`, and is complex differentiable at all but countably many points of
its interior, then the integrals of `f` over the circles `‖z - c‖ = r` and `‖z - c‖ = R` are equal
to each other. -/
theorem circleIntegral_eq_of_differentiable_on_annulus_off_countable {c : ℂ} {r R : ℝ} (h0 : 0 < r)
    (hle : r ≤ R) {f : ℂ → E} {s : Set ℂ} (hs : s.Countable)
    (hc : ContinuousOn f (closedBall c R \ ball c r))
    (hd : ∀ z ∈ (ball c R \ closedBall c r) \ s, DifferentiableAt ℂ f z) :
    (∮ z in C(c, R), f z) = ∮ z in C(c, r), f z := by
  have hcont : Continuous (fun z : ℂ ↦ z - c) := continuous_id.sub continuous_const
  simpa only [inv_smul_smul₀, circleIntegralOn_sphere, circleIntegral] using
    (circleIntegral_sub_center_inv_smul_eq_of_differentiable_on_annulus_off_countable
      (f := fun z ↦ (z - c) • f z) h0 hle hs (hcont.continuousOn.fun_smul hc) fun z hz =>
      (differentiableAt_id.sub_const c).smul (hd z hz))

end annulus

variable [CompleteSpace E]

section circle
/-!
## Circle integrals
-/

/-- **Cauchy integral formula** for the value at the center of a disc. If `f` is continuous on a
punctured closed disc of radius `R`, is differentiable at all but countably many points of the
interior of this disc, and has a limit `y` at the center of the disc, then the integral
$\oint_{‖z-c‖=R} \frac{f(z)}{z-c}\,dz$ is equal to `2πiy`. -/
theorem circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable_of_tendsto {c : ℂ}
    {R : ℝ} (h0 : 0 < R) {f : ℂ → E} {y : E} {s : Set ℂ} (hs : s.Countable)
    (hc : ContinuousOn f (closedBall c R \ {c}))
    (hd : ∀ z ∈ (ball c R \ {c}) \ s, DifferentiableAt ℂ f z) (hy : Tendsto f (𝓝[{c}ᶜ] c) (𝓝 y)) :
    circleIntegralOn (fun z : sphere c |R| ↦ Checked.inv (z.val - c)
      (isUnit_sub_center_of_mem_sphere h0.ne'.isUnit z) • f z.val) c R =
      (2 * π * I : ℂ) • y := by
  rw [← sub_eq_zero, ← norm_le_zero_iff]
  refine le_of_forall_gt_imp_ge_of_dense fun ε ε0 => ?_
  obtain ⟨δ, δ0, hδ⟩ : ∃ δ > (0 : ℝ), ∀ z ∈ closedBall c δ \ {c}, dist (f z) y < ε / (2 * π) :=
    ((nhdsWithin_hasBasis nhds_basis_closedBall _).tendsto_iff nhds_basis_ball).1 hy _
      (div_pos ε0 Real.two_pi_pos)
  obtain ⟨r, hr0, hrδ, hrR⟩ : ∃ r, 0 < r ∧ r ≤ δ ∧ r ≤ R :=
    ⟨min δ R, lt_min δ0 h0, min_le_left _ _, min_le_right _ _⟩
  have hsub : closedBall c R \ ball c r ⊆ closedBall c R \ {c} :=
    sdiff_subset_sdiff_right (singleton_subset_iff.2 <| mem_ball_self hr0)
  have hsub' : ball c R \ closedBall c r ⊆ ball c R \ {c} :=
    sdiff_subset_sdiff_right (singleton_subset_iff.2 <| mem_closedBall_self hr0.le)
  rw [circleIntegral_sub_center_inv_smul_eq_of_differentiable_on_annulus_off_countable hr0
    hrR hs (hc.mono hsub) (fun z hz ↦ hd z ⟨hsub' hz.1, hz.2⟩),
    circleIntegralOn_sub_center_inv_smul_eq_intervalIntegral hr0.ne']
  have hz (θ : ℝ) : circleMap c r θ ∈ closedBall c r \ {c} :=
    ⟨sphere_subset_closedBall (circleMap_mem_sphere c hr0.le θ), circleMap_ne_center hr0.ne'⟩
  have hcont : ContinuousOn (fun θ ↦ I • f (circleMap c r θ)) [[0, 2 * π]] :=
    continuousOn_const.smul <|
      hc.comp (continuous_circleMap c r).continuousOn fun θ _ ↦
        ⟨closedBall_subset_closedBall hrR (hz θ).1, (hz θ).2⟩
  have hconst : (∫ _ : ℝ in 0..2 * π, I • y) = (2 * π * I : ℂ) • y := by
    rw [intervalIntegral.integral_const, sub_zero, ← coe_smul, smul_smul, ofReal_mul,
      ofReal_ofNat]
  rw [← hconst, ← intervalIntegral.integral_sub hcont.intervalIntegrable
    intervalIntegrable_const]
  calc
    _ ≤ (ε / (2 * π)) * |2 * π - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro θ _
      rw [← smul_sub, norm_smul, norm_I, one_mul, ← dist_eq_norm]
      exact (hδ _ ⟨closedBall_subset_closedBall hrδ (hz θ).1, (hz θ).2⟩).le
    _ = ε := by rw [sub_zero, abs_of_pos Real.two_pi_pos, div_mul_cancel₀]

/--
**Cauchy integral formula** for the value at the center of a disc. If `f : ℂ → E` is continuous on a
closed disc of radius `R` and center `c`, and is complex differentiable at all but countably many
points of its interior, then the integral $\oint_{|z-c|=R} \frac{f(z)}{z-c}\,dz$ is equal to
`2πi • f c`.
-/
theorem circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable {R : ℝ} (h0 : 0 < R)
    {f : ℂ → E} {c : ℂ} {s : Set ℂ} (hs : s.Countable) (hc : ContinuousOn f (closedBall c R))
    (hd : ∀ z ∈ ball c R \ s, DifferentiableAt ℂ f z) :
    circleIntegralOn (fun z : sphere c |R| ↦ Checked.inv (z.val - c)
      (isUnit_sub_center_of_mem_sphere h0.ne'.isUnit z) • f z.val) c R =
      (2 * π * I : ℂ) • f c :=
  circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable_of_tendsto h0 hs
    (hc.mono sdiff_subset) (fun z hz => hd z ⟨hz.1.1, hz.2⟩)
    (hc.continuousAt <| closedBall_mem_nhds _ h0).continuousWithinAt

omit [CompleteSpace E] in
/-- **Cauchy-Goursat theorem** for a disk: if `f : ℂ → E` is continuous on a closed disk
`{z | ‖z - c‖ ≤ R}` and is complex differentiable at all but countably many points of its interior,
then the integral $\oint_{|z-c|=R}f(z)\,dz$ equals zero. -/
theorem circleIntegral_eq_zero_of_differentiable_on_off_countable {R : ℝ} (h0 : 0 ≤ R) {f : ℂ → E}
    {c : ℂ} {s : Set ℂ} (hs : s.Countable) (hc : ContinuousOn f (closedBall c R))
    (hd : ∀ z ∈ ball c R \ s, DifferentiableAt ℂ f z) : (∮ z in C(c, R), f z) = 0 := by
  wlog hE : CompleteSpace E generalizing
  · simp [circleIntegral, intervalIntegral, integral, hE]
  rcases h0.eq_or_lt with (rfl | h0); · apply circleIntegral.integral_radius_zero
  have hcont : Continuous (fun z : ℂ ↦ z - c) := continuous_id.sub continuous_const
  simpa only [inv_smul_smul₀, circleIntegralOn_sphere, circleIntegral,
    sub_self, zero_smul, smul_zero] using
    (circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable
      (f := fun z ↦ (z - c) • f z) h0 hs (hcont.continuousOn.fun_smul hc) fun z hz =>
      (differentiableAt_id.sub_const c).smul (hd z hz))

omit [CompleteSpace E] in
/-- **Cauchy-Goursat theorem** for a disk: if `f : ℂ → E` is continuous on a closed disk
`{z | ‖z - c‖ ≤ R}` and is complex differentiable on the open disk,
then the integral $\oint_{|z-c|=R}f(z)\,dz$ equals zero. -/
theorem _root_.DiffContOnCl.circleIntegral_eq_zero {R : ℝ} (h0 : 0 ≤ R) {f : ℂ → E}
    {c : ℂ} (hc : DiffContOnCl ℂ f (ball c R)) : ∮ z in C(c, R), f z = 0 :=
  circleIntegral_eq_zero_of_differentiable_on_off_countable h0 countable_empty
    hc.continuousOn_ball fun _z hz ↦ hc.differentiableAt isOpen_ball hz.1

/-- An auxiliary lemma for
`Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable`. This lemma assumes
`w ∉ s` while the main lemma drops this assumption. -/
theorem circleIntegral_sub_inv_smul_of_differentiable_on_off_countable_aux {R : ℝ} {c w : ℂ}
    {f : ℂ → E} {s : Set ℂ} (hs : s.Countable) (hw : w ∈ ball c R \ s)
    (hc : ContinuousOn f (closedBall c R)) (hd : ∀ x ∈ ball c R \ s, DifferentiableAt ℂ f x) :
    circleIntegralOn (fun z : sphere c |R| ↦ Checked.inv (z.val - w)
      (isUnit_sub_of_mem_sphere_of_mem_ball hw.1 z) • f z.val) c R =
      (2 * π * I : ℂ) • f w := by
  have hR : 0 < R := dist_nonneg.trans_lt hw.1
  set F : ℂ → E := dslope f w
  have hws : (insert w s).Countable := hs.insert w
  have hcF : ContinuousOn F (closedBall c R) :=
    (continuousOn_dslope <| closedBall_mem_nhds_of_mem hw.1).2 ⟨hc, hd _ hw⟩
  have hdF : ∀ z ∈ ball (c : ℂ) R \ insert w s, DifferentiableAt ℂ F z := fun z hz =>
    (differentiableAt_dslope_of_ne (ne_of_mem_of_not_mem (mem_insert _ _) hz.2).symm).2
      (hd _ (sdiff_subset_sdiff_right (subset_insert _ _) hz))
  have HI := circleIntegral_eq_zero_of_differentiable_on_off_countable hR.le hws hcF hdF
  let u (θ : ℝ) : IsUnit (circleMap c R θ - w) :=
    isUnit_sub_of_mem_sphere_of_mem_ball hw.1 ⟨circleMap c R θ, circleMap_mem_sphere' c R θ⟩
  let k (θ : ℝ) := Checked.inv (circleMap c R θ - w) (u θ)
  have hk : Continuous k := ((continuous_circleMap c R).sub continuous_const).fun_inv₀
  have hd' : Continuous (deriv (circleMap c R)) := by
    rw [funext (deriv_circleMap c R)]
    fun_prop
  have hcf : ContinuousOn (fun θ : ℝ ↦ f (circleMap c R θ)) [[0, 2 * π]] :=
    hc.comp (continuous_circleMap c R).continuousOn fun θ _ ↦
      sphere_subset_closedBall (circleMap_mem_sphere c hR.le θ)
  have hint : IntervalIntegrable
      (fun θ : ℝ ↦ deriv (circleMap c R) θ • k θ • f (circleMap c R θ)) volume 0 (2 * π) :=
    (hd'.continuousOn.smul (hk.continuousOn.smul hcf)).intervalIntegrable
  have hint' : IntervalIntegrable
      (fun θ : ℝ ↦ deriv (circleMap c R) θ • k θ • f w) volume 0 (2 * π) :=
    (hd'.smul (hk.smul continuous_const)).intervalIntegrable _ _
  have heq (θ : ℝ) : F (circleMap c R θ) = k θ • f (circleMap c R θ) - k θ • f w := by
    have hne : circleMap c R θ ≠ w := sub_ne_zero.mp (u θ).ne_zero
    dsimp only [F]
    rw [dslope_of_ne f hne]
    exact smul_sub _ _ _
  have hkernel : (∫ θ in 0..2 * π, deriv (circleMap c R) θ • k θ) = 2 * π * I := by
    simpa only [circleIntegralOn_sphere, k] using circleIntegral.integral_sub_inv_of_mem_ball hw.1
  simp only [circleIntegral, heq, smul_sub] at HI
  rw [intervalIntegral.integral_sub hint hint'] at HI
  simp only [← smul_assoc, intervalIntegral.integral_smul_const, hkernel] at HI
  simpa only [circleIntegralOn_sphere, k, smul_assoc] using (sub_eq_zero.mp HI)

/-- **Cauchy integral formula**: if `f : ℂ → E` is continuous on a closed disc of radius `R` and is
complex differentiable at all but countably many points of its interior, then for any `w` in this
interior we have $\frac{1}{2πi}\oint_{|z-c|=R}(z-w)^{-1}f(z)\,dz=f(w)$.
-/
theorem two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable {R : ℝ}
    {c w : ℂ} {f : ℂ → E} {s : Set ℂ} (hs : s.Countable) (hw : w ∈ ball c R)
    (hc : ContinuousOn f (closedBall c R)) (hd : ∀ x ∈ ball c R \ s, DifferentiableAt ℂ f x) :
    (2 * π * I : ℂ)⁻¹ • circleIntegralOn (fun z : sphere c |R| ↦ Checked.inv (z.val - w)
      (isUnit_sub_of_mem_sphere_of_mem_ball hw z) • f z.val) c R = f w := by
  have hR : 0 < R := dist_nonneg.trans_lt hw
  suffices w ∈ closure (ball c R \ s) by
    lift R to ℝ≥0 using hR.le
    let w' : ball c (R : ℝ) := ⟨w, hw⟩
    let G (w : ball c (R : ℝ)) : E := (2 * π * I : ℂ)⁻¹ •
      circleIntegralOn (fun z : sphere c |(R : ℝ)| ↦ Checked.inv (z.val - w.val)
        (isUnit_sub_of_mem_sphere_of_mem_ball w.2 z) • f z.val) c R
    have A : ContinuousAt G w' := by
      have hseries := hasFPowerSeriesOn_cauchy_integral
        ((hc.mono sphere_subset_closedBall).circleIntegrable R.coe_nonneg) hR
      have hmem : w' ∈ Subtype.val ⁻¹' Metric.eball c (R : ℝ≥0∞) := by
        simpa only [Set.mem_preimage, Metric.eball_coe] using hw
      exact (hseries.continuousOn continuous_subtype_val).continuousAt
        ((Metric.isOpen_eball.preimage continuous_subtype_val).mem_nhds hmem)
    have B : ContinuousAt (f ∘ Subtype.val) w' :=
      (hc.continuousAt (closedBall_mem_nhds_of_mem hw)).comp continuous_subtype_val.continuousAt
    have hfreq := mem_closure_iff_frequently.1 this
    rw [← (isOpen_ball.isOpenEmbedding_subtypeVal.map_nhds_eq w'), frequently_map] at hfreq
    apply tendsto_nhds_unique_of_frequently_eq A B
    exact hfreq.mono fun z hz ↦
      (show G z = f z.val by
        dsimp only [G]
        rw [circleIntegral_sub_inv_smul_of_differentiable_on_off_countable_aux hs hz hc hd,
          inv_smul_smul₀])
  refine mem_closure_iff_nhds.2 fun t ht => ?_
  -- TODO: generalize to any vector space over `ℝ`
  set g : ℝ → ℂ := fun x => w + ofReal x
  have : Tendsto g (𝓝 0) (𝓝 w) := Continuous.tendsto' (by fun_prop) 0 w (add_zero _)
  rcases mem_nhds_iff_exists_Ioo_subset.1 (this <| inter_mem ht <| isOpen_ball.mem_nhds hw) with
    ⟨l, u, hlu₀, hlu_sub⟩
  obtain ⟨x, hx⟩ : (Ioo l u \ g ⁻¹' s).Nonempty := by
    refine sdiff_nonempty.2 fun hsub => ?_
    have : (Ioo l u).Countable :=
      (hs.preimage ((add_right_injective w).comp ofReal_injective)).mono hsub
    rw [← Cardinal.le_aleph0_iff_set_countable, Cardinal.mk_Ioo_real (hlu₀.1.trans hlu₀.2)] at this
    exact this.not_gt Cardinal.aleph0_lt_continuum
  exact ⟨g x, (hlu_sub hx.1).1, (hlu_sub hx.1).2, hx.2⟩

/-- **Cauchy integral formula**: if `f : ℂ → E` is continuous on a closed disc of radius `R` and is
complex differentiable at all but countably many points of its interior, then for any `w` in this
interior we have $\oint_{|z-c|=R}(z-w)^{-1}f(z)\,dz=2πif(w)$.
-/
theorem circleIntegral_sub_inv_smul_of_differentiable_on_off_countable {R : ℝ} {c w : ℂ} {f : ℂ → E}
    {s : Set ℂ} (hs : s.Countable) (hw : w ∈ ball c R) (hc : ContinuousOn f (closedBall c R))
    (hd : ∀ x ∈ ball c R \ s, DifferentiableAt ℂ f x) :
    circleIntegralOn (fun z : sphere c |R| ↦ Checked.inv (z.val - w)
      (isUnit_sub_of_mem_sphere_of_mem_ball hw z) • f z.val) c R =
      (2 * π * I : ℂ) • f w := by
  rw [← two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
    hs hw hc hd, smul_inv_smul₀]

/-- **Cauchy integral formula**: if `f : ℂ → E` is complex differentiable on an open disc and is
continuous on its closure, then for any `w` in this open ball we have
$\oint_{|z-c|=R}(z-w)^{-1}f(z)\,dz=2πif(w)$. -/
theorem _root_.DiffContOnCl.circleIntegral_sub_inv_smul {R : ℝ} {c w : ℂ} {f : ℂ → E}
    (h : DiffContOnCl ℂ f (ball c R)) (hw : w ∈ ball c R) :
    circleIntegralOn (fun z : sphere c |R| ↦ Checked.inv (z.val - w)
      (isUnit_sub_of_mem_sphere_of_mem_ball hw z) • f z.val) c R = (2 * π * I : ℂ) • f w :=
  circleIntegral_sub_inv_smul_of_differentiable_on_off_countable countable_empty hw
    h.continuousOn_ball fun _x hx => h.differentiableAt isOpen_ball hx.1

/-- **Cauchy integral formula**: if `f : ℂ → E` is complex differentiable on an open disc and is
continuous on its closure, then for any `w` in this open ball we have
$\frac{1}{2πi}\oint_{|z-c|=R}(z-w)^{-1}f(z)\,dz=f(w)$. -/
theorem _root_.DiffContOnCl.two_pi_i_inv_smul_circleIntegral_sub_inv_smul {R : ℝ} {c w : ℂ}
    {f : ℂ → E} (hf : DiffContOnCl ℂ f (ball c R)) (hw : w ∈ ball c R) :
    (2 * π * I : ℂ)⁻¹ • circleIntegralOn (fun z : sphere c |R| ↦ Checked.inv (z.val - w)
      (isUnit_sub_of_mem_sphere_of_mem_ball hw z) • f z.val) c R = f w := by
  have hR : 0 < R := not_le.mp (ball_eq_empty.not.mp (Set.nonempty_of_mem hw).ne_empty)
  refine two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
    countable_empty hw ?_ ?_
  · simpa only [closure_ball c hR.ne.symm] using hf.continuousOn
  · simpa only [sdiff_empty] using fun z hz => hf.differentiableAt isOpen_ball hz

/-- **Cauchy integral formula**: if `f : ℂ → E` is complex differentiable on a closed disc of radius
`R`, then for any `w` in its interior we have $\oint_{|z-c|=R}(z-w)^{-1}f(z)\,dz=2πif(w)$. -/
theorem _root_.DifferentiableOn.circleIntegral_sub_inv_smul {R : ℝ} {c w : ℂ} {f : ℂ → E}
    (hd : DifferentiableOn ℂ f (closedBall c R)) (hw : w ∈ ball c R) :
    circleIntegralOn (fun z : sphere c |R| ↦ Checked.inv (z.val - w)
      (isUnit_sub_of_mem_sphere_of_mem_ball hw z) • f z.val) c R = (2 * π * I : ℂ) • f w :=
  (hd.mono closure_ball_subset_closedBall).diffContOnCl.circleIntegral_sub_inv_smul hw

/-- **Cauchy integral formula**: if `f : ℂ → ℂ` is continuous on a closed disc of radius `R` and is
complex differentiable at all but countably many points of its interior, then for any `w` in this
interior we have $\oint_{|z-c|=R}\frac{f(z)}{z-w}dz=2\pi i\,f(w)$.
-/
theorem circleIntegral_div_sub_of_differentiable_on_off_countable {R : ℝ} {c w : ℂ} {s : Set ℂ}
    (hs : s.Countable) (hw : w ∈ ball c R) {f : ℂ → ℂ} (hc : ContinuousOn f (closedBall c R))
    (hd : ∀ z ∈ ball c R \ s, DifferentiableAt ℂ f z) :
    circleIntegralOn (fun z : sphere c |R| ↦ Checked.div (f z.val) (z.val - w)
      (isUnit_sub_of_mem_sphere_of_mem_ball hw z)) c R = 2 * π * I * f w := by
  simpa only [smul_eq_mul, div_eq_inv_mul₀] using
    circleIntegral_sub_inv_smul_of_differentiable_on_off_countable hs hw hc hd

omit [CompleteSpace E] in
/--
**Derivative of Cauchy-type integrals**: if `f` is circle integrable and `w` does not lie on the
circle, then for every `n : ℤ` the Cauchy-type integral
`fun w ↦ ∮ z in C(c, R), (z - w) ^ n • f z` has derivative
`-n • ∮ z in C(c, R), (z - w) ^ (n - 1) • f z` at `w`.
-/
theorem hasDerivAt_circleIntegral_sub_zpow_smul {f : ℂ → E} {R : ℝ} {c w : ℂ} {n : ℤ}
    (hf : CircleIntegrable f c R) (hw : w ∉ sphere c |R|) :
    HasDerivAt (fun x : ((sphere c |R|)ᶜ : Set ℂ) ↦
      circleIntegralOn (fun z : sphere c |R| ↦ Checked.zpow (z.val - x.val) n
        (fun _ ↦ (sub_ne_zero.mpr (ne_of_mem_of_not_mem z.2 x.2)).isUnit) • f z.val) c R)
      ((-n : ℂ) • circleIntegralOn (fun z : sphere c |R| ↦ Checked.zpow (z.val - w) (n - 1)
        (fun _ ↦ (sub_ne_zero.mpr (ne_of_mem_of_not_mem z.2 hw)).isUnit) • f z.val) c R)
      ⟨w, hw⟩ Subtype.val := by
  obtain ⟨d, hd, hdist⟩ := exists_ball_forall_le_norm_circleMap_sub hw
  let D : Set ℂ := (sphere c |R|)ᶜ
  let x₀ : D := ⟨w, hw⟩
  let u (x : D) (θ : ℝ) : IsUnit (circleMap c R θ - x.val) :=
    (sub_ne_zero.mpr (ne_of_mem_of_not_mem (circleMap_mem_sphere' c R θ) x.2)).isUnit
  let k (m : ℤ) (x : D) (θ : ℝ) := Checked.zpow (circleMap c R θ - x.val) m (fun _ ↦ u x θ)
  let F (x : D) (θ : ℝ) := (circleMap 0 R θ * I) • k n x θ • f (circleMap c R θ)
  let F' (x : D) (θ : ℝ) := (-n : ℂ) • (circleMap 0 R θ * I) •
    k (n - 1) x θ • f (circleMap c R θ)
  have hD : IsOpen D := isClosed_sphere.isOpen_compl
  have hK (m : ℤ) (x : D) : Continuous (k m x) :=
    ((continuous_circleMap c R).sub continuous_const).zpow₀ m
  have hθ : Continuous (fun θ : ℝ ↦ circleMap 0 R θ * I) :=
    (continuous_circleMap 0 R).mul continuous_const
  have hfi : IntervalIntegrable (fun θ ↦ f (circleMap c R θ)) volume 0 (2 * π) := hf
  have hfm : AEStronglyMeasurable (fun θ ↦ f (circleMap c R θ))
      (volume.restrict (uIoc 0 (2 * π))) := (intervalIntegrable_iff.1 hfi).aestronglyMeasurable
  have hupper : 0 < |R| + dist c w + d :=
    add_pos_of_nonneg_of_pos (add_nonneg (abs_nonneg _) dist_nonneg) hd
  let M := |(n : ℝ)| * |R| * max
    (Checked.zpow d (n - 1) (fun _ ↦ hd.ne'.isUnit))
    (Checked.zpow (|R| + dist c w + d) (n - 1) (fun _ ↦ hupper.ne'.isUnit))
  have hdiff : HasDerivAt (fun x : D ↦ ∫ θ in 0..2 * π, F x θ)
      (∫ θ in 0..2 * π, F' x₀ θ) x₀ Subtype.val := by
    refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F' := F') (bound := fun θ ↦ M * ‖f (circleMap c R θ)‖)
      (continuous_subtype_val.continuousAt.preimage_mem_nhds (ball_mem_nhds w hd))
      ?_ ?_ ?_ ?_ (hfi.norm.const_mul M) ?_ hD.isOpenEmbedding_subtypeVal).2
    · -- Measurability of the integrand for parameters close to the evaluation point.
      filter_upwards with x
      exact hθ.aestronglyMeasurable.smul ((hK n x).aestronglyMeasurable.smul hfm)
    · -- Integrability of the integrand at the evaluation point.
      exact (hfi.continuousOn_smul (hK n x₀).continuousOn).continuousOn_smul hθ.continuousOn
    · -- Measurability of the differentiated integrand.
      exact (hθ.aestronglyMeasurable.smul
        ((hK (n - 1) x₀).aestronglyMeasurable.smul hfm)).const_smul _
    · -- Uniform bound for the differentiated integrand.
      filter_upwards with θ _ x hx
      have hlb : d ≤ ‖circleMap c R θ - x.val‖ := hdist x.val hx θ
      have hpos := hd.trans_le hlb
      have hub : ‖circleMap c R θ - x.val‖ ≤ |R| + dist c w + d := by
        have := mem_ball.1 hx
        linarith [norm_circleMap_sub_le c R θ x.val, dist_triangle_right c x.val w]
      have key : ‖circleMap c R θ - x.val‖ ^ (n - 1) ≤
          max (d ^ (n - 1)) ((|R| + dist c w + d) ^ (n - 1)) := by
        rcases le_or_gt 0 (n - 1) with h | h
        · exact le_max_of_le_right (zpow_le_zpow_left₀ h (norm_nonneg _) hub)
        · refine le_max_of_le_left ?_
          simp only [show n - 1 = -(1 - n) by ring, zpow_neg₀ hpos.ne', zpow_neg₀ hd.ne']
          exact inv_anti₀ (zpow_pos hd _) (zpow_le_zpow_left₀ (by omega) hd.le hlb)
      have hnorm : ‖F' x θ‖ = |(n : ℝ)| * |R| *
          ‖circleMap c R θ - x.val‖ ^ (n - 1) * ‖f (circleMap c R θ)‖ := by
        simp only [F', k, norm_smul, norm_neg, Complex.norm_intCast, norm_zpow, norm_mul,
          Complex.norm_I, mul_one, norm_circleMap_zero]
        ring
      rw [hnorm]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left key (by positivity))
        (norm_nonneg _)
    · -- Differentiate the kernel in the open coordinate domain.
      filter_upwards with θ _ x _
      let q (x : D) : {y : ℂ // n < 0 → IsUnit y} := ⟨circleMap c R θ - x.val, fun _ ↦ u x θ⟩
      have he : HasFDerivAt (fun y : D ↦ circleMap c R θ - y.val)
          (ContinuousLinearMap.toSpanSingleton ℂ (-1 : ℂ)) x Subtype.val := by
        simpa only [HasFDerivAt, Function.comp_def, id_eq] using
          ((hasDerivAt_id x.val).const_sub (circleMap c R θ)).hasFDerivAt.comp_tendsto
            Subtype.val (continuous_subtype_val.continuousAt.tendsto.prodMap (tendsto_pure_pure ..))
      have hp := (hasDerivAt_zpow n (q x)).hasFDerivAt.comp x (f := q)
        (by simpa only [q, Function.comp_def] using he)
        continuous_subtype_val.continuousAt Topology.IsEmbedding.subtypeVal
      let A : ℂ →L[ℂ] E := (circleMap 0 R θ * I) •
        ContinuousLinearMap.toSpanSingleton ℂ (f (circleMap c R θ))
      have hA := A.hasFDerivAt.comp x hp continuous_subtype_val.continuousAt Topology.IsEmbedding.id
      convert hA.hasDerivAt using 1
      · rfl
      · simp only [F', A, k, q, ContinuousLinearMap.comp_apply, smul_apply,
          ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, mul_neg, mul_one]
        split_ifs with hn
        · simp [hn]
        · module
  simpa only [circleIntegralOn_sphere, deriv_circleMap, F, F', k, x₀,
    intervalIntegral.integral_smul] using hdiff

omit [CompleteSpace E] in
/--
**Derivative of the Cauchy integral**: if `f` is circle integrable and `w` does not lie on the
circle, then the Cauchy-type integral `fun w ↦ ∮ z in C(c, R), (z - w)⁻¹ • f z` has derivative
`∮ z in C(c, R), (z - w) ^ (-2) • f z` at `w`.
-/
theorem hasDerivAt_circleIntegral_sub_inv_smul {f : ℂ → E} {R : ℝ} {c w : ℂ}
    (hf : CircleIntegrable f c R) (hw : w ∉ sphere c |R|) :
    HasDerivAt (fun x : ((sphere c |R|)ᶜ : Set ℂ) ↦ circleIntegralOn (fun z : sphere c |R| ↦
      Checked.inv (z.val - x.val) (sub_ne_zero.mpr (ne_of_mem_of_not_mem z.2 x.2)).isUnit •
        f z.val) c R)
      (circleIntegralOn (fun z : sphere c |R| ↦ Checked.zpow (z.val - w) (-2)
        (fun _ ↦ (sub_ne_zero.mpr (ne_of_mem_of_not_mem z.2 hw)).isUnit) • f z.val) c R)
      ⟨w, hw⟩ Subtype.val := by
  simpa only [show (-1 : ℤ) - 1 = -2 by norm_num, zpow_neg_one₀, Int.cast_neg, Int.cast_one,
    neg_neg, one_smul]
    using hasDerivAt_circleIntegral_sub_zpow_smul (n := -1) hf hw

end circle

section analyticity
/-!
## Applications to analyticity
-/

/-- If `f : ℂ → E` is continuous on a closed ball of positive radius and is differentiable at all
but countably many points of the corresponding open ball, then it is analytic on the open ball with
coefficients of the power series given by Cauchy integral formulas. -/
theorem hasFPowerSeriesOnBall_of_differentiable_off_countable {R : ℝ≥0} {c : ℂ} {f : ℂ → E}
    {s : Set ℂ} (hs : s.Countable) (hc : ContinuousOn f (closedBall c R))
    (hd : ∀ z ∈ ball c R \ s, DifferentiableAt ℂ f z) (hR : 0 < R) :
    HasFPowerSeriesOnBall f
      (cauchyPowerSeries f c R (hR := (show 0 < (R : ℝ) from hR).ne'.isUnit)) c R where
  r_le := le_radius_cauchyPowerSeries _ _ _ (hR := (show 0 < (R : ℝ) from hR).ne'.isUnit)
  r_pos := ENNReal.coe_pos.2 hR
  hasSum := fun {w} hw => by
    have hw' : w ∈ ball c R := by
      simpa only [id_eq, mem_ball_iff_norm, ← coe_nnnorm, mem_eball_zero_iff,
        NNReal.coe_lt_coe, enorm_lt_coe] using hw
    rw [← two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
      hs hw' hc hd]
    exact (hasFPowerSeriesOn_cauchy_integral
      ((hc.mono sphere_subset_closedBall).circleIntegrable R.2) hR).hasSum
        (y := (⟨w, hw'⟩ : ball c (R : ℝ))) hw

/-- If `f : ℂ → E` is complex differentiable on an open disc of positive radius and is continuous
on its closure, then it is analytic on the open disc with coefficients of the power series given by
Cauchy integral formulas. -/
theorem _root_.DiffContOnCl.hasFPowerSeriesOnBall {R : ℝ≥0} {c : ℂ} {f : ℂ → E}
    (hf : DiffContOnCl ℂ f (ball c R)) (hR : 0 < R) :
    HasFPowerSeriesOnBall f
      (cauchyPowerSeries f c R (hR := (show 0 < (R : ℝ) from hR).ne'.isUnit)) c R :=
  hasFPowerSeriesOnBall_of_differentiable_off_countable countable_empty hf.continuousOn_ball
    (fun _z hz => hf.differentiableAt isOpen_ball hz.1) hR

/-- If `f : ℂ → E` is complex differentiable on a closed disc of positive radius, then it is
analytic on the corresponding open disc, and the coefficients of the power series are given by
Cauchy integral formulas. See also
`Complex.hasFPowerSeriesOnBall_of_differentiable_off_countable` for a version of this lemma with
weaker assumptions. -/
protected theorem _root_.DifferentiableOn.hasFPowerSeriesOnBall {R : ℝ≥0} {c : ℂ} {f : ℂ → E}
    (hd : DifferentiableOn ℂ f (closedBall c R)) (hR : 0 < R) :
    HasFPowerSeriesOnBall f
      (cauchyPowerSeries f c R (hR := (show 0 < (R : ℝ) from hR).ne'.isUnit)) c R :=
  (hd.mono closure_ball_subset_closedBall).diffContOnCl.hasFPowerSeriesOnBall hR

/-- A complex differentiable function in embedded coordinates admits a power series on an open
disc when the coordinate image covers the closed disc and the function is differentiable there. -/
protected theorem _root_.DifferentiableOn.exists_hasFPowerSeriesOnBall
    {D : Type*} [TopologicalSpace D] {f : D → E} {coord : D → ℂ} {c : D} {r : ℝ≥0}
    (hd : DifferentiableOn ℂ f (coord ⁻¹' closedBall (coord c) r) coord)
    (hr : 0 < r) (hcoord : Topology.IsEmbedding coord)
    (hD : closedBall (coord c) r ⊆ Set.range coord) :
    ∃ p : FormalMultilinearSeries ℂ ℂ E, HasFPowerSeriesOnBall f p c r coord := by
  -- Radial projection fixes every point where the ambient Cauchy theorem is used.
  have hr' : 0 < (r : ℝ) := hr
  let R (z : ℂ) := max (r : ℝ) ‖z - coord c‖
  have hR (z : ℂ) : 0 < R z := hr'.trans_le (le_max_left _ _)
  let proj (z : ℂ) := coord c + Checked.div (r : ℝ) (R z) (hR z).ne'.isUnit • (z - coord c)
  have hmem (z : ℂ) : proj z ∈ closedBall (coord c) r := by
    rw [mem_closedBall_iff_norm]
    simp only [proj, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg (div_nonneg hr'.le (hR z).le), div_mul_eq_mul_div₀, div_le_iff₀ (hR z)]
    exact mul_le_mul_of_nonneg_left (le_max_right _ _) hr'.le
  have hfix {z : ℂ} (hz : z ∈ closedBall (coord c) r) : proj z = z := by
    simp only [proj, R, max_eq_left (mem_closedBall_iff_norm.mp hz), div_self, one_smul,
      add_sub_cancel]
  let lift (z : ℂ) : D := Classical.choose (hD (hmem z))
  have hlift (z : ℂ) : coord (lift z) = proj z := Classical.choose_spec (hD (hmem z))
  have hlift_mem (z : ℂ) : lift z ∈ coord ⁻¹' closedBall (coord c) r := by
    simpa only [mem_preimage, hlift] using hmem z
  have hdiff : DifferentiableOn ℂ (f ∘ lift) (closedBall (coord c) r) := by
    intro z hz
    have hproj : HasFDerivWithinAt (coord ∘ lift) (.id ℂ ℂ) (closedBall (coord c) r) z :=
      (hasFDerivWithinAt_id _ _).congr' (fun w hw ↦ (hlift w).trans (hfix hw)) hz
    exact ((hd (lift z) (hlift_mem z)).hasFDerivWithinAt.comp z hproj (fun w _ ↦ hlift_mem w)
      continuousWithinAt_id hcoord).differentiableWithinAt
  have hseries := hdiff.hasFPowerSeriesOnBall hr
  refine ⟨_, hseries.r_le, hseries.r_pos, fun {y} hy ↦ ?_⟩
  have hy' : coord y ∈ closedBall (coord c) r := by
    rw [Metric.eball_coe, mem_ball_zero_iff] at hy
    exact mem_closedBall_iff_norm.mpr hy.le
  have heq : lift (coord y) = y := hcoord.injective ((hlift _).trans (hfix hy'))
  simpa only [Function.comp_apply, heq, id_eq] using hseries.hasSum (y := coord y) hy

/-- If `f : ℂ → E` is complex differentiable on some set `s`, then it is analytic at any point `z`
such that `s ∈ 𝓝 z` (equivalently, `z ∈ interior s`). -/
protected theorem _root_.DifferentiableOn.analyticAt {s : Set ℂ} {f : ℂ → E} {z : ℂ}
    (hd : DifferentiableOn ℂ f s) (hz : s ∈ 𝓝 z) : AnalyticAt ℂ f z := by
  rcases nhds_basis_closedBall.mem_iff.1 hz with ⟨R, hR0, hRs⟩
  lift R to ℝ≥0 using hR0.le
  exact ((hd.mono hRs).hasFPowerSeriesOnBall hR0).analyticAt

theorem _root_.DifferentiableOn.analyticOnNhd {s : Set ℂ} {f : ℂ → E} (hd : DifferentiableOn ℂ f s)
    (hs : IsOpen s) : AnalyticOnNhd ℂ f s := fun _z hz => hd.analyticAt (hs.mem_nhds hz)

theorem _root_.DifferentiableOn.analyticOn {s : Set ℂ} {f : ℂ → E} (hd : DifferentiableOn ℂ f s)
    (hs : IsOpen s) : AnalyticOn ℂ f s :=
  (hd.analyticOnNhd hs).analyticOn

/-- If `f : ℂ → E` is complex differentiable on some open set `s`, then it is continuously
differentiable on `s`. -/
protected theorem _root_.DifferentiableOn.contDiffOn {s : Set ℂ} {f : ℂ → E} {n : WithTop ℕ∞}
    (hd : DifferentiableOn ℂ f s) (hs : IsOpen s) : ContDiffOn ℂ n f s :=
  (hd.analyticOnNhd hs).contDiffOn_of_completeSpace

theorem _root_.DifferentiableOn.deriv {s : Set ℂ} {f : ℂ → E} (hd : DifferentiableOn ℂ f s)
    (hs : IsOpen s) : DifferentiableOn ℂ (deriv f) s :=
  (hd.analyticOnNhd hs).deriv.differentiableOn

/-- A complex differentiable function `f : ℂ → E` is analytic at every point. -/
protected theorem _root_.Differentiable.analyticAt {f : ℂ → E} (hf : Differentiable ℂ f) (z : ℂ) :
    AnalyticAt ℂ f z :=
  hf.differentiableOn.analyticAt univ_mem

/-- A complex differentiable function `f : ℂ → E` is continuously differentiable at every point. -/
protected theorem _root_.Differentiable.contDiff
    {f : ℂ → E} (hf : Differentiable ℂ f) {n : WithTop ℕ∞} :
    ContDiff ℂ n f :=
  contDiff_iff_contDiffAt.mpr fun z ↦ (hf.analyticAt z).contDiffAt

@[fun_prop]
theorem _root_.Differentiable.deriv {f : ℂ → E} (hf : Differentiable ℂ f) :
    Differentiable ℂ (deriv f) :=
  hf.contDiff.differentiable_deriv_two

/-- When `f : ℂ → E` is differentiable, the `cauchyPowerSeries f z R` represents `f` as a power
series centered at `z` in the entirety of `ℂ`, regardless of `R : ℝ≥0`, with `0 < R`. -/
protected theorem _root_.Differentiable.hasFPowerSeriesOnBall {f : ℂ → E} (h : Differentiable ℂ f)
    (z : ℂ) {R : ℝ≥0} (hR : 0 < R) :
    HasFPowerSeriesOnBall f
      (cauchyPowerSeries f z R (hR := (show 0 < (R : ℝ) from hR).ne'.isUnit)) z ∞ :=
  (h.differentiableOn.hasFPowerSeriesOnBall hR).r_eq_top_of_exists fun _r hr =>
    ⟨_, h.differentiableOn.hasFPowerSeriesOnBall hr⟩

/-- On an open set, `f : ℂ → E` is analytic iff it is differentiable -/
theorem analyticOnNhd_iff_differentiableOn {f : ℂ → E} {s : Set ℂ} (o : IsOpen s) :
    AnalyticOnNhd ℂ f s ↔ DifferentiableOn ℂ f s :=
  ⟨AnalyticOnNhd.differentiableOn, fun d _ zs ↦ d.analyticAt (o.mem_nhds zs)⟩

/-- On an open set, `f : ℂ → E` is analytic iff it is differentiable -/
theorem analyticOn_iff_differentiableOn {f : ℂ → E} {s : Set ℂ} (o : IsOpen s) :
    AnalyticOn ℂ f s ↔ DifferentiableOn ℂ f s := by
  rw [o.analyticOn_iff_analyticOnNhd]
  exact analyticOnNhd_iff_differentiableOn o

/-- `f : ℂ → E` is entire iff it's differentiable -/
theorem analyticOnNhd_univ_iff_differentiable {f : ℂ → E} :
    AnalyticOnNhd ℂ f univ ↔ Differentiable ℂ f := by
  simp only [← differentiableOn_univ]
  exact analyticOnNhd_iff_differentiableOn isOpen_univ

theorem analyticOn_univ_iff_differentiable {f : ℂ → E} :
    AnalyticOn ℂ f univ ↔ Differentiable ℂ f := by
  rw [analyticOn_univ]
  exact analyticOnNhd_univ_iff_differentiable

/-- `f : ℂ → E` is analytic at `z` iff it's differentiable near `z` -/
theorem analyticAt_iff_eventually_differentiableAt {f : ℂ → E} {c : ℂ} :
    AnalyticAt ℂ f c ↔ ∀ᶠ z in 𝓝 c, DifferentiableAt ℂ f z := by
  constructor
  · intro fa
    filter_upwards [fa.eventually_analyticAt] with _ ha
    exact ha.differentiableAt
  · intro d
    rcases _root_.eventually_nhds_iff.mp d with ⟨s, d, o, m⟩
    have h : AnalyticOnNhd ℂ f s := by
      refine DifferentiableOn.analyticOnNhd ?_ o
      intro z m
      exact (d z m).differentiableWithinAt
    exact h _ m

end analyticity

section derivatives
/-!
## Circle integrals for higher derivatives

TODO: add a version for `w ∈ Metric.ball c R`.
-/

variable {R : ℝ} {f : ℂ → E} {c : ℂ} {s : Set ℂ}

/-- **Cauchy integral formula for derivatives**, assuming `f` is continuous on a closed ball and
differentiable on its interior away from a countable set. -/
lemma circleIntegral_one_div_sub_center_pow_smul_of_differentiable_on_off_countable
    (h0 : 0 < R) (n : ℕ) (hs : s.Countable)
    (hc : ContinuousOn f (closedBall c R)) (hd : ∀ z ∈ ball c R \ s, DifferentiableAt ℂ f z) :
    circleIntegralOn (fun z : sphere c |R| ↦ Checked.div 1 ((z.val - c) ^ (n + 1))
      ((isUnit_sub_center_of_mem_sphere h0.ne'.isUnit z).pow _) • f z.val) c R =
      (2 * π * I / (n.factorial : ℂ)) • iteratedDeriv n f c := by
  have := hasFPowerSeriesOnBall_of_differentiable_off_countable (R := .mk R h0.le) hs hc hd h0
      |>.factorial_smul 1 n
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, Finset.prod_const_one, one_smul] at this
  rw [← this, cauchyPowerSeries_apply, ← Nat.cast_smul_eq_nsmul ℂ, ← mul_smul, ← mul_smul,
    div_mul_cancel₀, mul_inv_cancel₀, one_smul]
  simp only [div_eq_mul_inv₀, one_mul, inv_pow₀, pow_succ, mul_inv_rev₀, smul_smul]
  congr 1
  funext z
  rw [mul_comm]

/-- **Cauchy integral formula for the first order derivative**, assuming `f` is continuous on a
closed ball and differentiable on its interior away from a countable set. -/
lemma differentiable_on_off_countable_deriv_eq_smul_circleIntegral
    (h0 : 0 < R) (hs : s.Countable) (hc : ContinuousOn f (closedBall c R))
    (hd : ∀ z ∈ ball c R \ s, DifferentiableAt ℂ f z) :
    circleIntegralOn (fun z : sphere c |R| ↦ Checked.div 1 ((z.val - c) ^ 2)
      ((isUnit_sub_center_of_mem_sphere h0.ne'.isUnit z).pow 2) • f z.val) c R =
      (2 * π * I) • deriv f c := by
  simpa using circleIntegral_one_div_sub_center_pow_smul_of_differentiable_on_off_countable
    h0 1 hs hc hd

/-- **Cauchy integral formula for derivatives**, assuming `f` is continuous on a closed ball and
differentiable on its interior. -/
lemma _root_.DiffContOnCl.circleIntegral_one_div_sub_center_pow_smul
    (h0 : 0 < R) (n : ℕ) (hc : DiffContOnCl ℂ f (ball c R)) :
    circleIntegralOn (fun z : sphere c |R| ↦ Checked.div 1 ((z.val - c) ^ (n + 1))
      ((isUnit_sub_center_of_mem_sphere h0.ne'.isUnit z).pow _) • f z.val) c R =
      (2 * π * I / (n.factorial : ℂ)) • iteratedDeriv n f c :=
  c.circleIntegral_one_div_sub_center_pow_smul_of_differentiable_on_off_countable h0 n
    Set.countable_empty hc.continuousOn_ball fun _ hx ↦ hc.differentiableAt isOpen_ball hx.1

/-- **Cauchy integral formula for the first order derivative**, assuming `f` is continuous on a
closed ball and differentiable on its interior. -/
lemma _root_.DiffContOnCl.deriv_eq_smul_circleIntegral (h0 : 0 < R)
    (hc : DiffContOnCl ℂ f (ball c R)) :
    circleIntegralOn (fun z : sphere c |R| ↦ Checked.div 1 ((z.val - c) ^ 2)
      ((isUnit_sub_center_of_mem_sphere h0.ne'.isUnit z).pow 2) • f z.val) c R =
      (2 * π * I) • deriv f c := by
  simpa using DiffContOnCl.circleIntegral_one_div_sub_center_pow_smul h0 1 hc

/-- **Cauchy integral formula for derivatives**, assuming `f` is differentiable on a closed ball. -/
lemma _root_.DifferentiableOn.circleIntegral_one_div_sub_center_pow_smul (h0 : 0 < R) (n : ℕ)
    (hc : DifferentiableOn ℂ f (closedBall c R)) :
    circleIntegralOn (fun z : sphere c |R| ↦ Checked.div 1 ((z.val - c) ^ (n + 1))
      ((isUnit_sub_center_of_mem_sphere h0.ne'.isUnit z).pow _) • f z.val) c R =
      (2 * π * I / (n.factorial : ℂ)) • iteratedDeriv n f c :=
  (hc.mono closure_ball_subset_closedBall).diffContOnCl
    |>.circleIntegral_one_div_sub_center_pow_smul h0 n

/-- **Cauchy integral formula for the first order derivative**, assuming `f` is differentiable on
a closed ball. -/
lemma _root_.DifferentiableOn.deriv_eq_smul_circleIntegral (h0 : 0 < R)
    (hc : DifferentiableOn ℂ f (closedBall c R)) :
    circleIntegralOn (fun z : sphere c |R| ↦ Checked.div 1 ((z.val - c) ^ 2)
      ((isUnit_sub_center_of_mem_sphere h0.ne'.isUnit z).pow 2) • f z.val) c R =
      (2 * π * I) • deriv f c := by
  simpa using DifferentiableOn.circleIntegral_one_div_sub_center_pow_smul h0 1 hc

end derivatives

end Complex
