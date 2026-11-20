/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.MeasureTheory.Integral.CircleAverage

/-!
# The Mean Value Property of Complex Differentiable Functions

This file established the classic mean value properties of complex differentiable functions,
computing the value of a function at the center of a circle as a circle average. It also provides
generalized versions that computing the value of a function at arbitrary points of a disk as circle
averages over suitable weighted functions.
-/

public section

open Complex Metric Real Set

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {f : ℂ → E} {R : ℝ} {c w : ℂ} {s : Set ℂ}

/-!
## Generalized Mean Value Properties

For a complex differentiable function `f`, the theorems in this section compute values of `f` in the
interior of a disk as circle averages of a weighted function.
-/

/--
The **Generalized Mean Value Property** of complex differentiable functions: If `f : ℂ → E` is
continuous on a closed disc of radius `R` and center `c`, and is complex differentiable at all but
countably many points of its interior, then for every point `w` in the disk, the circle average
`circleAverage (fun z ↦ ((z - c) * (z - w)⁻¹) • f z) c R` equals `f w`.
-/
theorem circleAverage_sub_sub_inv_smul_of_differentiable_on_off_countable (hs : s.Countable)
    (h₁f : ContinuousOn f (closedBall c |R|)) (h₂f : ∀ z ∈ ball c |R| \ s, DifferentiableAt ℂ f z)
    (hw : w ∈ ball c |R|) :
    circleAverageOn (fun z : sphere c |R| ↦ Checked.div (z.val - c) (z.val - w)
      (isUnit_sub_of_mem_sphere_of_mem_ball hw ⟨z.val, by simpa only [abs_abs] using z.2⟩) •
        f z.val) = f w := by
  have hR : R ≠ 0 := abs_pos.mp (dist_nonneg.trans_lt hw)
  rw [circleAverageOn_eq_circleIntegralOn hR]
  simpa only [div_eq_mul_inv₀, mul_smul, inv_smul_smul₀] using
    two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
      hs hw h₁f h₂f

/--
The **Generalized Mean Value Property** of complex differentiable functions: If `f : ℂ → E` is
complex differentiable at all points of a closed disc of radius `R` and center `c`, then for every
point `w` in the disk, the circle average `circleAverage (fun z ↦ ((z - c) * (z - w)⁻¹) • f z) c R`
equals `f w`.
-/
theorem DiffContOnCl.circleAverage_smul_div (hf : DiffContOnCl ℂ f (ball c |R|))
    (hw : w ∈ ball c |R|) :
    circleAverageOn (fun z : sphere c |R| ↦ Checked.div (z.val - c) (z.val - w)
      (isUnit_sub_of_mem_sphere_of_mem_ball hw ⟨z.val, by simpa only [abs_abs] using z.2⟩) •
        f z.val) = f w := by
  have hR : 0 < |R| := dist_nonneg.trans_lt hw
  apply circleAverage_sub_sub_inv_smul_of_differentiable_on_off_countable countable_empty _ _ hw
  · simpa [← closure_ball _ hR.ne'] using hf.2
  · intro z hz
    rw [sdiff_empty] at hz
    apply (hf.1 z hz).differentiableAt (isOpen_ball.mem_nhds hz)

/-!
## Classic Mean Value Properties

For a complex differentiable function `f`, the theorems in this section compute value of `f` at the
center of a circle as a circle average of the function. This specializes the generalized mean value
properties discussed in the previous section.
-/

/--
The **Mean Value Property** of complex differentiable functions: If `f : ℂ → E` is continuous on a
closed disc of radius `R` and center `c`, and is complex differentiable at all but countably many
points of its interior, then the circle average `circleAverage f c R` equals `f c`.
-/
theorem circleAverage_of_differentiable_on_off_countable (hs : s.Countable)
    (h₁f : ContinuousOn f (closedBall c |R|)) (h₂f : ∀ z ∈ ball c |R| \ s, DifferentiableAt ℂ f z) :
    circleAverage f c R = f c := by
  by_cases hR : R = 0
  · simp [hR]
  · simpa only [div_self, one_smul, circleAverageOn_restrict] using
      circleAverage_sub_sub_inv_smul_of_differentiable_on_off_countable hs h₁f h₂f
        (mem_ball_self (abs_pos.mpr hR))

/--
The **Mean Value Property** of complex differentiable functions: If `f : ℂ → E` is complex
differentiable at all points of a closed disc of radius `R` and center `c`, then the circle average
`circleAverage f c R` equals `f c`.
-/
theorem DiffContOnCl.circleAverage (hf : DiffContOnCl ℂ f (ball c |R|)) :
    circleAverage f c R = f c := by
  by_cases hR : R = 0
  · simp [hR]
  · simpa only [div_self, one_smul, circleAverageOn_restrict] using
      hf.circleAverage_smul_div (mem_ball_self (abs_pos.mpr hR))
