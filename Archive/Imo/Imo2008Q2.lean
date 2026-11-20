/-
Copyright (c) 2021 Manuel Candales. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Manuel Candales
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Field
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# IMO 2008 Q2

(a) Prove that
          ```
          x^2 / (x-1)^2 + y^2 / (y-1)^2 + z^2 / (z-1)^2 ≥ 1
          ```
for all real numbers `x`,`y`, `z`, each different from 1, and satisfying `xyz = 1`.

(b) Prove that equality holds above for infinitely many triples of rational numbers `x`, `y`, `z`,
each different from 1, and satisfying `xyz = 1`.

## Solution
(a) Multiply the difference between the left-hand side and `1` by the positive square
`((x - 1) * (y - 1) * (z - 1)) ^ 2`. The product is `(3 - (x * y + y * z + z * x)) ^ 2`.

(b) A family of rational triples satisfies `x * y + y * z + z * x = 3`, so the same identity
shows that equality holds. The third coordinates of the family have unbounded magnitude.
-/

@[expose] public section

namespace Imo2008Q2

theorem subst_abc {x y z : ℝ} (h : x * y * z = 1) :
    ∃ (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0),
      x = Checked.div a b (hb := isUnit_iff_ne_zero.mpr hb) ∧
      y = Checked.div b c (hb := isUnit_iff_ne_zero.mpr hc) ∧
      z = Checked.div c a (hb := isUnit_iff_ne_zero.mpr ha) := by
  have hxy : x * y ≠ 0 := by
    intro e
    simp [e] at h
  have hy : y ≠ 0 := fun e => hxy (by rw [e, mul_zero])
  refine ⟨x * y, y, 1, hxy, hy, one_ne_zero, ?_, ?_, ?_⟩
  · exact (mul_div_cancel_right₀ (hb := isUnit_iff_ne_zero.mpr hy) x).symm
  · exact (div_one₀ y).symm
  · exact eq_one_div_of_mul_eq_one_right₀ (ha := isUnit_iff_ne_zero.mpr hxy) h

theorem sub_one_sq_isUnit {K : Type*} [Field K] {x : K} (hx : x ≠ 1) :
    IsUnit ((x - 1) ^ 2) :=
  isUnit_iff_ne_zero.mpr (pow_ne_zero 2 (sub_ne_zero.mpr hx))

private theorem squareCert {K : Type*} [Field K] {x y z : K}
    (h : x * y * z = 1) (hx : IsUnit ((x - 1) ^ 2))
    (hy : IsUnit ((y - 1) ^ 2)) (hz : IsUnit ((z - 1) ^ 2)) :
    (x ^ 2 / (x - 1) ^ 2 + y ^ 2 / (y - 1) ^ 2 + z ^ 2 / (z - 1) ^ 2 - 1) *
        ((x - 1) * (y - 1) * (z - 1)) ^ 2 =
      (3 - (x * y + y * z + z * x)) ^ 2 := by
  calc
    _ = (x ^ 2 / (x - 1) ^ 2 * (x - 1) ^ 2) * ((y - 1) * (z - 1)) ^ 2 +
        (y ^ 2 / (y - 1) ^ 2 * (y - 1) ^ 2) * ((z - 1) * (x - 1)) ^ 2 +
        (z ^ 2 / (z - 1) ^ 2 * (z - 1) ^ 2) * ((x - 1) * (y - 1)) ^ 2 -
        ((x - 1) * (y - 1) * (z - 1)) ^ 2 := by ring
    _ = (2 * (x * y * z) + 1 - (x * y + y * z + z * x)) ^ 2 -
        2 * (x * y * z - 1) * ((x - 1) * (y - 1) * (z - 1)) := by
          simp only [div_mul_cancel₀]
          ring
    _ = _ := by
      rw [h]
      ring

theorem imo2008_q2a (x y z : ℝ) (h : x * y * z = 1)
    (hx : x ≠ 1) (hy : y ≠ 1) (hz : z ≠ 1) :
    Checked.div (x ^ 2) ((x - 1) ^ 2) (hb := sub_one_sq_isUnit hx) +
    Checked.div (y ^ 2) ((y - 1) ^ 2) (hb := sub_one_sq_isUnit hy) +
    Checked.div (z ^ 2) ((z - 1) ^ 2) (hb := sub_one_sq_isUnit hz) ≥ 1 := by
  have e := squareCert h (sub_one_sq_isUnit hx) (sub_one_sq_isUnit hy) (sub_one_sq_isUnit hz)
  have hd := mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hx) (sub_ne_zero.mpr hy))
    (sub_ne_zero.mpr hz)
  rw [ge_iff_le, ← sub_nonneg]
  apply (mul_nonneg_iff_of_pos_right (sq_pos_of_ne_zero hd)).mp
  rw [e]
  exact sq_nonneg _

def rationalSolutions :=
  {s : ℚ × ℚ × ℚ | ∃ x y z : ℚ, s = (x, y, z) ∧
    ∃ (hx : x ≠ 1) (hy : y ≠ 1) (hz : z ≠ 1), x * y * z = 1 ∧
      Checked.div (x ^ 2) ((x - 1) ^ 2) (hb := sub_one_sq_isUnit hx) +
      Checked.div (y ^ 2) ((y - 1) ^ 2) (hb := sub_one_sq_isUnit hy) +
      Checked.div (z ^ 2) ((z - 1) ^ 2) (hb := sub_one_sq_isUnit hz) = 1}

theorem imo2008_q2b : Set.Infinite rationalSolutions := by
  let g : ℚ × ℚ × ℚ → ℚ := fun s => -s.2.2
  have unb : ¬ BddAbove (g '' rationalSolutions) := by
    rw [not_bddAbove_iff]
    intro q
    let t : ℚ := max (q + 1) 1
    have hq : q + 1 ≤ t := le_max_left _ _
    have ht : 0 < t := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    have hu : 0 < t + 1 := by linarith
    have dt := pow_ne_zero 2 ht.ne'
    have du := pow_ne_zero 2 hu.ne'
    let x := Checked.div (-(t + 1)) (t ^ 2) (hb := isUnit_iff_ne_zero.mpr dt)
    let y := Checked.div t ((t + 1) ^ 2) (hb := isUnit_iff_ne_zero.mpr du)
    let z := -t * (t + 1)
    have ex : x * t ^ 2 = -(t + 1) := div_mul_cancel₀ (hb := isUnit_iff_ne_zero.mpr dt) _
    have ey : y * (t + 1) ^ 2 = t := div_mul_cancel₀ (hb := isUnit_iff_ne_zero.mpr du) _
    have hx : x ≠ 1 := by
      intro e
      rw [e, one_mul] at ex
      nlinarith only [ex, ht, sq_nonneg t]
    have hy : y ≠ 1 := by
      intro e
      rw [e, one_mul] at ey
      nlinarith only [ey, ht, sq_nonneg t]
    have hz : z ≠ 1 :=
      ne_of_lt ((mul_neg_of_neg_of_pos (neg_lt_zero.mpr ht) hu).trans zero_lt_one)
    have prod : x * y * z = 1 := by
      apply mul_right_cancel₀ (mul_ne_zero dt du)
      calc
        _ = (x * t ^ 2) * (y * (t + 1) ^ 2) * z := by ring
        _ = _ := by rw [ex, ey]; dsimp only [z]; ring
    have sum : x * y + y * z + z * x = 3 := by
      apply mul_right_cancel₀ (mul_ne_zero dt du)
      calc
        _ = (x * t ^ 2) * (y * (t + 1) ^ 2) +
            (y * (t + 1) ^ 2) * z * t ^ 2 + z * (x * t ^ 2) * (t + 1) ^ 2 := by ring
        _ = _ := by rw [ex, ey]; dsimp only [z]; ring
    have e := squareCert prod (sub_one_sq_isUnit hx) (sub_one_sq_isUnit hy) (sub_one_sq_isUnit hz)
    rw [sum, sub_self, zero_pow (by decide : 2 ≠ 0)] at e
    have hd := mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hx) (sub_ne_zero.mpr hy))
      (sub_ne_zero.mpr hz)
    refine ⟨t * (t + 1), ⟨(x, y, z), ?_, ?_⟩, ?_⟩
    · exact ⟨x, y, z, rfl, hx, hy, hz, prod,
        sub_eq_zero.mp ((mul_eq_zero.mp e).resolve_right (pow_ne_zero 2 hd))⟩
    · change -(-t * (t + 1)) = _
      ring
    · nlinarith only [hq, sq_nonneg t]
  intro hfin
  exact unb (hfin.image g).bddAbove

end Imo2008Q2
