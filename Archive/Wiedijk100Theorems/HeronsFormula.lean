/-
Copyright (c) 2021 Matt Kempster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matt Kempster
-/
module

public import Mathlib.Geometry.Euclidean.Triangle

/-!
# Freek № 57: Heron's Formula

This file proves Theorem 57 from the [100 Theorems List](https://www.cs.ru.nl/~freek/100/),
also known as Heron's formula, which gives the area of a triangle based only on its three sides'
lengths.

## References

* https://en.wikipedia.org/wiki/Herons_formula

-/

open Real EuclideanGeometry

namespace Theorems100

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-- **Heron's formula**: The area of a triangle with side lengths `a`, `b`, and `c` is
  `√(s * (s - a) * (s - b) * (s - c))` where `s = (a + b + c) / 2` is the semiperimeter.
  We show this by equating this formula to `a * b * sin γ`, where `γ` is the angle opposite
  the side `c`.
-/
public theorem heron {p₁ p₂ p₃ : P} (h1 : p₁ ≠ p₂) (h2 : p₃ ≠ p₂) :
    let a := dist p₁ p₂
    let b := dist p₃ p₂
    let c := dist p₁ p₃
    let s := (a + b + c) / 2
    1 / 2 * a * b * sin (∠ p₁ p₂ p₃) = √(s * (s - a) * (s - b) * (s - c)) := by
  intro a b c s
  let γ := ∠ p₁ p₂ p₃
  have hc : 2 * a * b * cos γ = a ^ 2 + b ^ 2 - c ^ 2 := by
    have h := dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle p₁ p₂ p₃
      (hp₁ := h1) (hp₃ := h2)
    dsimp only [a, b, c, γ]
    nlinarith only [h]
  have hs : 0 ≤ sin γ := Real.sin_nonneg_of_nonneg_of_le_pi (angle_nonneg ..) (angle_le_pi ..)
  have ha : 0 ≤ a := dist_nonneg
  have hb : 0 ≤ b := dist_nonneg
  have harea : 0 ≤ 1 / 2 * a * b * sin γ := by positivity
  have ht : sin γ ^ 2 = 1 - cos γ ^ 2 := by linarith only [sin_sq_add_cos_sq γ]
  calc
    1 / 2 * a * b * sin γ = √((1 / 2 * a * b * sin γ) ^ 2) := (sqrt_sq harea).symm
    _ = √(s * (s - a) * (s - b) * (s - c)) := by
      apply congrArg Real.sqrt
      calc
        (1 / 2 * a * b * sin γ) ^ 2 =
            (1 / 16 : ℝ) * ((2 * a * b) ^ 2 - (2 * a * b * cos γ) ^ 2) := by
          rw [mul_pow, ht]
          ring
        _ = s * (s - a) * (s - b) * (s - c) := by rw [hc]; dsimp only [s]; ring

end Theorems100
