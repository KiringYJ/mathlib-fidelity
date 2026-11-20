/-
Copyright (c) 2021 James Arthur, Benjamin Davidson, Andrew Souther. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Arthur, Benjamin Davidson, Andrew Souther
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# Freek № 9: The Area of a Circle

In this file we show that the area of a disc with nonnegative radius `r` is `π * r^2`. The main
tools are `volume_regionBetween_eq_integral` for the disc and `integral_sqrt_one_sub_sq`
for the rescaled interval integral.

We begin by defining `disc` in `ℝ × ℝ`, then show that `disc` can be represented as the
`regionBetween` two functions.

Though not necessary for the main proof, we nonetheless choose to include a proof of the
measurability of the disc in order to convince the reader that the set whose volume we will be
calculating is indeed measurable and our result is therefore meaningful.

In the main proof, `area_disc`, we use `volume_regionBetween_eq_integral` followed by
`intervalIntegral.integral_of_le` to reduce our goal to a single `intervalIntegral`:
  `∫ (x : ℝ) in -r..r, 2 * sqrt (r ^ 2 - x ^ 2) = π * r ^ 2`.
The change of variables `x = r * t` reduces this integral to a constant
multiple of the integral of `sqrt (1 - t ^ 2)` on `[-1, 1]`. The scaled integral
identity also covers radius zero.

Note that we choose to define `disc` as a set of points in `ℝ × ℝ`. This is admittedly not ideal; it
would be more natural to define `disc` as a `Metric.ball` in `EuclideanSpace ℝ (Fin 2)` (as well as
to provide a more general proof in higher dimensions). However, our proof indirectly relies on a
number of theorems (particularly `MeasureTheory.Measure.prod_apply`) which do not yet exist for
Euclidean space, thus forcing us to use this less-preferable definition. As `MeasureTheory.pi`
continues to develop, it should eventually become possible to redefine `disc` and extend our proof
to the n-ball.
-/

@[expose] public section

open Set Real MeasureTheory intervalIntegral

open scoped Real NNReal

namespace Theorems100

/-- A disc of radius `r` is defined as the collection of points `(p.1, p.2)` in `ℝ × ℝ` such that
  `p.1 ^ 2 + p.2 ^ 2 < r ^ 2`.
  Note that this definition is not equivalent to `Metric.ball (0 : ℝ × ℝ) r`. This was done
  intentionally because `dist` in `ℝ × ℝ` is defined as the uniform norm, making the `Metric.ball`
  in `ℝ × ℝ` a square, not a disc.
  See the module docstring for an explanation of why we don't define the disc in Euclidean space. -/
def disc (r : ℝ) :=
  {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < r ^ 2}

variable (r : ℝ≥0)

/-- A disc of radius `r` can be represented as the region between the two curves
  `fun x => - sqrt (r ^ 2 - x ^ 2)` and `fun x => sqrt (r ^ 2 - x ^ 2)`. -/
theorem disc_eq_regionBetween :
    disc r =
      regionBetween
        (fun x => -sqrt (r ^ 2 - x ^ 2)) (fun x => sqrt (r ^ 2 - x ^ 2)) (Ioc (-r) r) := by
  ext p
  simp only [disc, regionBetween, mem_ofPred_eq, mem_Ioo, mem_Ioc]
  constructor <;> intro h
  · cases abs_lt_of_sq_lt_sq' (lt_of_add_lt_of_nonneg_left h (sq_nonneg p.2)) r.2 with
    | intro left right =>
      rw [add_comm, ← lt_sub_iff_add_lt] at h
      exact ⟨⟨left, right.le⟩, sq_lt.mp h⟩
  · rw [add_comm, ← lt_sub_iff_add_lt]
    exact sq_lt.mpr h.2

/-- The disc is a `MeasurableSet`. -/
theorem measurableSet_disc : MeasurableSet (disc r) := by
  apply measurableSet_lt <;> fun_prop

/-- **Area of a Circle**: The area of a disc with radius `r` is `π * r ^ 2`. -/
theorem area_disc : volume (disc r) = NNReal.pi * r ^ 2 := by
  let f x := sqrt (r ^ 2 - x ^ 2)
  have hf : Continuous f := by fun_prop
  suffices ∫ x in -r..r, 2 * f x = NNReal.pi * r ^ 2 by
    have h : IntegrableOn f (Ioc (-r) r) := hf.integrableOn_Icc.mono_set Ioc_subset_Icc_self
    calc
      volume (disc r) = volume (regionBetween (fun x => -f x) f (Ioc (-r) r)) := by
        rw [disc_eq_regionBetween]
      _ = ENNReal.ofReal (∫ x in Ioc (-r : ℝ) r, (f - Neg.neg ∘ f) x) := by
        simpa only [Measure.prod_eq_productBySections (volume : Measure ℝ) (volume : Measure ℝ),
          ← Measure.volume_eq_productBySections ℝ ℝ, Function.comp_def, Pi.neg_def]
          using (volume_regionBetween_eq_integral h.neg h measurableSet_Ioc fun x _ =>
            neg_le_self (sqrt_nonneg _))
      _ = ENNReal.ofReal (∫ x in (-r : ℝ)..r, 2 * f x) := by
        rw [integral_of_le] <;> simp [two_mul]
      _ = NNReal.pi * r ^ 2 := by rw_mod_cast [this, ← ENNReal.coe_nnreal_eq]
  have hf_mul (x : ℝ) : f ((r : ℝ) * x) = r * sqrt (1 - x ^ 2) := by
    change sqrt ((r : ℝ) ^ 2 - ((r : ℝ) * x) ^ 2) = r * sqrt (1 - x ^ 2)
    rw [show (r : ℝ) ^ 2 - ((r : ℝ) * x) ^ 2 = (r : ℝ) ^ 2 * (1 - x ^ 2) by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq r.coe_nonneg]
  calc
    ∫ x in -r..r, 2 * f x =
        (r : ℝ) * ∫ x in (-1 : ℝ)..1, 2 * f ((r : ℝ) * x) := by
      simpa only [mul_neg, mul_one, smul_eq_mul] using
        (smul_integral_comp_mul_left (a := (-1 : ℝ)) (b := 1) (fun x ↦ 2 * f x) (r : ℝ)).symm
    _ = (r : ℝ) * ((2 * (r : ℝ)) * (π / 2)) := by
      congr 1
      simp_rw [hf_mul, ← mul_assoc]
      rw [intervalIntegral.integral_const_mul, integral_sqrt_one_sub_sq]
    _ = NNReal.pi * r ^ 2 := by
      have hπ : (NNReal.pi : ℝ) = π := rfl
      rw [hπ]
      ring


end Theorems100
