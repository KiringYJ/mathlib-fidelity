/-
Copyright (c) 2021 Manuel Candales. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Candales
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.NNReal.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# IMO 2008 Q4

Find all functions `f : (0,∞) → (0,∞)` (so, `f` is a function from the positive real
numbers to the positive real numbers) such that
      ```
      (f(w)^2 + f(x)^2)/(f(y^2) + f(z^2)) = (w^2 + x^2)/(y^2 + z^2)
      ```
for all positive real numbers `w`, `x`, `y`, `z`, satisfying `wx = yz`.

## Solution
The desired theorem is that either `f = fun x => x` or `f = fun x => 1/x`
-/

public section

open Real

namespace Imo2008Q4

theorem abs_eq_one_of_pow_eq_one (x : ℝ) (n : ℕ) (hn : n ≠ 0) (h : x ^ n = 1) : |x| = 1 := by
  rw [← pow_left_inj₀ (abs_nonneg x) zero_le_one hn, one_pow, pow_abs, h, abs_one]

end Imo2008Q4

open Imo2008Q4

theorem imo2008_q4 (f : ℝ → ℝ) (H₁ : ∀ x > 0, 0 < f x) :
    (∀ (w x y z : ℝ) (_hw : 0 < w) (_hx : 0 < x) (hy : 0 < y) (hz : 0 < z),
      w * x = y * z →
      Checked.div (f w ^ 2 + f x ^ 2) (f (y ^ 2) + f (z ^ 2))
          (add_pos (H₁ _ (pow_pos hy 2)) (H₁ _ (pow_pos hz 2))).ne'.isUnit =
        Checked.div (w ^ 2 + x ^ 2) (y ^ 2 + z ^ 2)
          (add_pos (pow_pos hy 2) (pow_pos hz 2)).ne'.isUnit) ↔
    (∀ x > 0, f x = x) ∨
      ∀ (x : ℝ) (hx : 0 < x), f x = Checked.div 1 x hx.ne'.isUnit := by
  simp only [div_eq_div_iff]
  simp only [eq_div_iff]
  constructor
  · intro H
    have h1 : f 1 = 1 := by
      have e := H 1 1 1 1 zero_lt_one zero_lt_one zero_lt_one zero_lt_one rfl
      simp only [one_pow] at e
      have m : f 1 * (f 1 - 1) = 0 := by nlinarith only [e]
      exact sub_eq_zero.mp ((mul_eq_zero.mp m).resolve_left (H₁ 1 zero_lt_one).ne')
    have point : ∀ x > 0, f x = x ∨ f x * x = 1 := by
      intro x hx
      have e := H 1 x (sqrt x) (sqrt x) zero_lt_one hx (sqrt_pos.mpr hx) (sqrt_pos.mpr hx)
        (by simpa only [one_mul] using (mul_self_sqrt hx.le).symm)
      rw [sq_sqrt hx.le, h1] at e
      have m : (f x - x) * (f x * x - 1) = 0 := by nlinarith only [e]
      exact (mul_eq_zero.mp m).imp sub_eq_zero.mp sub_eq_zero.mp
    by_contra! ⟨⟨b, hb, nb⟩, ⟨a, ha, na⟩⟩
    have fa := (point a ha).resolve_right na
    have fb := (point b hb).resolve_left nb
    have hp := mul_pos ha hb
    have e := H a b (sqrt (a * b)) (sqrt (a * b)) ha hb
      (sqrt_pos.mpr hp) (sqrt_pos.mpr hp) (mul_self_sqrt hp.le).symm
    rw [sq_sqrt hp.le, fa] at e
    have k : (a ^ 2 + f b ^ 2) * (a * b) = (a ^ 2 + b ^ 2) * f (a * b) := by
      nlinarith only [e]
    rcases point (a * b) hp with idp | invp
    · rw [idp] at k
      have m : (f b - b) * ((f b + b) * (a * b)) = 0 := by nlinarith only [k]
      exact nb (sub_eq_zero.mp ((mul_eq_zero.mp m).resolve_right
        (mul_pos (add_pos (H₁ b hb) hb) hp).ne'))
    · have d : (a ^ 2 + f b ^ 2) * (a * b) ^ 2 = a ^ 2 + b ^ 2 := by
        calc
          _ = ((a ^ 2 + f b ^ 2) * (a * b)) * (a * b) := by ring
          _ = _ := by rw [k, mul_assoc, invp, mul_one]
      have bb : (f b * b) ^ 2 = 1 := by rw [fb, one_pow]
      have m : (a * a - 1) * ((a ^ 2 + 1) * b ^ 2) = 0 := by
        linear_combination d - a ^ 2 * bb
      apply na
      rw [fa]
      exact sub_eq_zero.mp ((mul_eq_zero.mp m).resolve_right
        (mul_pos (add_pos (pow_pos ha 2) zero_lt_one) (pow_pos hb 2)).ne')
  · rintro (h | h) w x y z hw hx hy hz hp
    · rw [h w hw, h x hx, h (y ^ 2) (pow_pos hy 2), h (z ^ 2) (pow_pos hz 2)]
    · apply mul_right_cancel₀ (pow_ne_zero 2 (mul_ne_zero hw.ne' hx.ne'))
      calc
        _ = ((f w * w) ^ 2 * x ^ 2 + (f x * x) ^ 2 * w ^ 2) *
            (y ^ 2 + z ^ 2) := by ring
        _ = (w ^ 2 + x ^ 2) * (y ^ 2 + z ^ 2) := by rw [h w hw, h x hx]; ring
        _ = (w ^ 2 + x ^ 2) * ((f (y ^ 2) * y ^ 2) * z ^ 2 +
            (f (z ^ 2) * z ^ 2) * y ^ 2) := by
              rw [h (y ^ 2) (pow_pos hy 2), h (z ^ 2) (pow_pos hz 2)]
              ring
        _ = _ := by rw [hp]; ring
