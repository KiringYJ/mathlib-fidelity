/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Smoothness of `Real.sqrt`

In this file we prove that `Real.sqrt` is infinitely smooth at all points `x ≠ 0` and provide some
dot-notation lemmas.

## Tags

sqrt, differentiable
-/

@[expose] public section


open Set

open scoped Topology

namespace Real

/-- Local homeomorph between `(0, +∞)` and `(0, +∞)` with `toFun = (· ^ 2)` and
`invFun = Real.sqrt`. -/
noncomputable def sqPartialHomeomorph : OpenPartialHomeomorph ℝ ℝ where
  toFun x := x ^ 2
  invFun := (√·)
  source := Ioi 0
  target := Ioi 0
  map_source' _ h := mem_Ioi.2 (pow_pos (mem_Ioi.1 h) _)
  map_target' _ h := mem_Ioi.2 (sqrt_pos.2 h)
  left_inv' _ h := sqrt_sq (le_of_lt h)
  right_inv' _ h := sq_sqrt (le_of_lt h)
  open_source := isOpen_Ioi
  open_target := isOpen_Ioi
  continuousOn_toFun := (continuous_pow 2).continuousOn
  continuousOn_invFun := continuousOn_id.sqrt

theorem isUnit_two_mul_sqrt {x : ℝ} (hx : 0 < x) : IsUnit (2 * √x) :=
  (mul_pos two_pos (sqrt_pos.2 hx)).ne'.isUnit

theorem deriv_sqrt_aux {x : ℝ} (hx : x ≠ 0) :
    HasStrictDerivAt (√·) (if h : 0 < x then Checked.div 1 (2 * √x) (isUnit_two_mul_sqrt h)
      else 0) x ∧ ∀ n, ContDiffAt ℝ n (√·) x := by
  rcases hx.lt_or_gt with hx | hx
  · rw [dite_eq_right (not_lt_of_gt hx)]
    have : (√·) =ᶠ[𝓝 x] fun _ => 0 := (gt_mem_nhds hx).mono fun x hx => sqrt_eq_zero_of_nonpos hx.le
    exact
      ⟨(hasStrictDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq this.symm, fun n =>
        contDiffAt_const.congr_of_eventuallyEq this⟩
  · have hunit := isUnit_two_mul_sqrt hx
    have hpow : HasStrictDerivAt (fun y : ℝ ↦ y ^ 2) (2 * √x) (√x) := by
      simpa using hasStrictDerivAt_pow 2 (√x)
    constructor
    · rw [dite_eq_left hx, one_div₀]
      exact sqPartialHomeomorph.hasStrictDerivAt_symm hx hunit.ne_zero hpow
    · exact fun n => sqPartialHomeomorph.contDiffAt_symm_deriv hunit.ne_zero hx hpow.hasDerivAt
        (contDiffAt_id.pow 2)

theorem hasStrictDerivAt_sqrt {x : ℝ} (hx : x ≠ 0) :
    HasStrictDerivAt (√·) (if h : 0 < x then Checked.div 1 (2 * √x) (isUnit_two_mul_sqrt h)
      else 0) x :=
  (deriv_sqrt_aux hx).1

@[fun_prop]
theorem contDiffAt_sqrt {x : ℝ} {n : WithTop ℕ∞} (hx : x ≠ 0) : ContDiffAt ℝ n (√·) x :=
  (deriv_sqrt_aux hx).2 n

theorem hasDerivAt_sqrt {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (√·) (if h : 0 < x then Checked.div 1 (2 * √x) (isUnit_two_mul_sqrt h) else 0) x :=
  (hasStrictDerivAt_sqrt hx).hasDerivAt

end Real

open Real

section deriv

variable {f : ℝ → ℝ} {s : Set ℝ} {f' x : ℝ}

theorem HasDerivWithinAt.sqrt (hf : HasDerivWithinAt f f' s x) (hx : f x ≠ 0) :
    HasDerivWithinAt (fun y => √(f y))
      ((if h : 0 < f x then Checked.div 1 (2 * √(f x)) (isUnit_two_mul_sqrt h) else 0) * f') s x :=
  (hasDerivAt_sqrt hx).comp_hasDerivWithinAt (coord' := id) x hf

theorem HasDerivAt.sqrt (hf : HasDerivAt f f' x) (hx : f x ≠ 0) :
    HasDerivAt (fun y => √(f y))
      ((if h : 0 < f x then Checked.div 1 (2 * √(f x)) (isUnit_two_mul_sqrt h) else 0) * f') x :=
  (hasDerivAt_sqrt hx).comp (coord' := id) x hf

theorem HasStrictDerivAt.sqrt (hf : HasStrictDerivAt f f' x) (hx : f x ≠ 0) :
    HasStrictDerivAt (fun t => √(f t))
      ((if h : 0 < f x then Checked.div 1 (2 * √(f x)) (isUnit_two_mul_sqrt h) else 0) * f') x :=
  (hasStrictDerivAt_sqrt hx).comp (coord' := id) x hf

theorem derivWithin_sqrt (hf : DifferentiableWithinAt ℝ f s x) (hx : f x ≠ 0)
    (hxs : UniqueDiffWithinAt ℝ s x) :
    derivWithin (fun x => √(f x)) s x =
      (if h : 0 < f x then Checked.div 1 (2 * √(f x)) (isUnit_two_mul_sqrt h) else 0) *
        derivWithin f s x :=
  (hf.hasDerivWithinAt.sqrt hx).derivWithin hxs

@[simp]
theorem deriv_sqrt (hf : DifferentiableAt ℝ f x) (hx : f x ≠ 0) :
    deriv (fun x => √(f x)) x =
      (if h : 0 < f x then Checked.div 1 (2 * √(f x)) (isUnit_two_mul_sqrt h) else 0) * deriv f x :=
  (hf.hasDerivAt.sqrt hx).deriv

end deriv

section fderiv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {n : WithTop ℕ∞}
  {s : Set E} {x : E} {f' : StrongDual ℝ E}

theorem HasFDerivAt.sqrt (hf : HasFDerivAt f f' x) (hx : f x ≠ 0) :
    HasFDerivAt (fun y => √(f y))
      ((if h : 0 < f x then Checked.div 1 (2 * √(f x)) (isUnit_two_mul_sqrt h) else 0) • f') x :=
  (hasDerivAt_sqrt hx).comp_hasFDerivAt x hf

theorem HasStrictFDerivAt.sqrt (hf : HasStrictFDerivAt f f' x) (hx : f x ≠ 0) :
    HasStrictFDerivAt (fun y => √(f y))
      ((if h : 0 < f x then Checked.div 1 (2 * √(f x)) (isUnit_two_mul_sqrt h) else 0) • f') x :=
  (hasStrictDerivAt_sqrt hx).comp_hasStrictFDerivAt x hf

theorem HasFDerivWithinAt.sqrt (hf : HasFDerivWithinAt f f' s x) (hx : f x ≠ 0) :
    HasFDerivWithinAt (fun y => √(f y))
      ((if h : 0 < f x then Checked.div 1 (2 * √(f x)) (isUnit_two_mul_sqrt h) else 0) • f') s x :=
  (hasDerivAt_sqrt hx).comp_hasFDerivWithinAt x hf

@[fun_prop]
theorem DifferentiableWithinAt.sqrt (hf : DifferentiableWithinAt ℝ f s x) (hx : f x ≠ 0) :
    DifferentiableWithinAt ℝ (fun y => √(f y)) s x :=
  (hf.hasFDerivWithinAt.sqrt hx).differentiableWithinAt

@[fun_prop]
theorem DifferentiableAt.sqrt (hf : DifferentiableAt ℝ f x) (hx : f x ≠ 0) :
    DifferentiableAt ℝ (fun y => √(f y)) x :=
  (hf.hasFDerivAt.sqrt hx).differentiableAt

@[fun_prop]
theorem DifferentiableOn.sqrt (hf : DifferentiableOn ℝ f s) (hs : ∀ x ∈ s, f x ≠ 0) :
    DifferentiableOn ℝ (fun y => √(f y)) s := fun x hx => (hf x hx).sqrt (hs x hx)

@[fun_prop]
theorem Differentiable.sqrt (hf : Differentiable ℝ f) (hs : ∀ x, f x ≠ 0) :
    Differentiable ℝ fun y => √(f y) := fun x => (hf x).sqrt (hs x)

theorem fderivWithin_sqrt (hf : DifferentiableWithinAt ℝ f s x) (hx : f x ≠ 0)
    (hxs : UniqueDiffWithinAt ℝ s x) :
    fderivWithin ℝ (fun x => √(f x)) s x =
      (if h : 0 < f x then Checked.div 1 (2 * √(f x)) (isUnit_two_mul_sqrt h) else 0) •
        fderivWithin ℝ f s x :=
  (hf.hasFDerivWithinAt.sqrt hx).fderivWithin hxs

@[simp]
theorem fderiv_sqrt (hf : DifferentiableAt ℝ f x) (hx : f x ≠ 0) :
    fderiv ℝ (fun x => √(f x)) x =
      (if h : 0 < f x then Checked.div 1 (2 * √(f x)) (isUnit_two_mul_sqrt h) else 0) •
        fderiv ℝ f x :=
  (hf.hasFDerivAt.sqrt hx).fderiv

@[fun_prop]
theorem ContDiffAt.sqrt (hf : ContDiffAt ℝ n f x) (hx : f x ≠ 0) :
    ContDiffAt ℝ n (fun y => √(f y)) x :=
  (contDiffAt_sqrt hx).comp x hf

@[fun_prop]
theorem ContDiffWithinAt.sqrt (hf : ContDiffWithinAt ℝ n f s x) (hx : f x ≠ 0) :
    ContDiffWithinAt ℝ n (fun y => √(f y)) s x :=
  (contDiffAt_sqrt hx).comp_contDiffWithinAt x hf

@[fun_prop]
theorem ContDiffOn.sqrt (hf : ContDiffOn ℝ n f s) (hs : ∀ x ∈ s, f x ≠ 0) :
    ContDiffOn ℝ n (fun y => √(f y)) s := fun x hx => (hf x hx).sqrt (hs x hx)

@[fun_prop]
theorem ContDiff.sqrt (hf : ContDiff ℝ n f) (h : ∀ x, f x ≠ 0) : ContDiff ℝ n fun y => √(f y) :=
  contDiff_iff_contDiffAt.2 fun x => hf.contDiffAt.sqrt (h x)

end fderiv
