/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Data.Int.SuccPred

/-!
# Pentagonal numbers

This file introduces (generalized) pentagonal numbers $k(3k-1)/2$ for integer $k$.

Some sources, such as A001318 in the OEIS, order generalized pentagonal numbers by indices
$k = 0, 1, -1, 2, -2, \cdots$ to form a strictly monotone sequence. This file doesn't follow this
convention, but implicitly shows the monotonicity in `pentagonal_lt_pentagonal_neg` and
`pentagonal_neg_lt_pentagonal_add_one`.

## Main definitions

* `pentagonal`: pentagonal numbers as a function `ℤ → ℕ`.

## References

* https://en.wikipedia.org/wiki/Pentagonal_number
-/

public section

/-- Pentagonal numbers $k(3k-1)/2$ for integer $k$. -/
def pentagonal (k : ℤ) : ℕ :=
  (Int.exactQuotient (k * (3 * k - 1)) 2 (even_iff_two_dvd.mp (by grind))).toNat

theorem pentagonal_def (k : ℤ) :
    pentagonal k =
      (Int.exactQuotient (k * (3 * k - 1)) 2 (even_iff_two_dvd.mp (by grind))).toNat := by rfl

theorem pentagonal_neg (k : ℤ) :
    pentagonal (-k) =
      (Int.exactQuotient (k * (3 * k + 1)) 2 (even_iff_two_dvd.mp (by grind))).toNat := by
  simp only [pentagonal_def, Int.exactQuotient, Int.euclideanDiv_eq_core]
  grind

theorem natCast_pentagonal (k : ℤ) :
    (pentagonal k : ℤ) =
      Int.exactQuotient (k * (3 * k - 1)) 2 (even_iff_two_dvd.mp (by grind)) := by
  simp only [pentagonal_def, Int.exactQuotient, Int.euclideanDiv_eq_core]
  rcases k with (_ | _) | _ <;> grind

theorem two_mul_natCast_pentagonal (k : ℤ) : 2 * (pentagonal k : ℤ) = k * (3 * k - 1) := by
  rw [natCast_pentagonal, Int.mul_exactQuotient]

theorem two_mul_natCast_pentagonal_neg (k : ℤ) : 2 * (pentagonal (-k) : ℤ) = k * (3 * k + 1) := by
  grind [two_mul_natCast_pentagonal]

theorem pentagonal_injective : Function.Injective pentagonal := by
  intro x y h
  replace h : (3 * (x + y) - 1) * (x - y) = 0 := by grind [two_mul_natCast_pentagonal]
  cases mul_eq_zero.mp h <;> grind

@[simp]
theorem pentagonal_inj {x y : ℤ} : pentagonal x = pentagonal y ↔ x = y :=
  pentagonal_injective.eq_iff

theorem pentagonal_lt_pentagonal_neg {k : ℤ} (h : 0 < k) : pentagonal k < pentagonal (-k) := by
  grind [two_mul_natCast_pentagonal]

theorem pentagonal_neg_lt_pentagonal_add_one {k : ℤ} (h : 0 ≤ k) :
    pentagonal (-k) < pentagonal (k + 1) := by
  grind [two_mul_natCast_pentagonal]

theorem pentagonal_strictMonoOn : StrictMonoOn pentagonal (Set.Ici 0) := by
  apply strictMonoOn_of_lt_add_one Set.ordConnected_Ici
  grind [two_mul_natCast_pentagonal]

theorem pentagonal_strictAntiOn : StrictAntiOn pentagonal (Set.Iic 0) := by
  apply strictAntiOn_of_add_one_lt Set.ordConnected_Iic
  grind [two_mul_natCast_pentagonal]
