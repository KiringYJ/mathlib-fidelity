/-
Copyright (c) 2026 Seewoo Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seewoo Lee
-/
module

public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Results about big operators with values in floor rings

This file proves the classical Hermite identity for the floor function: for every
element `x` of a linearly ordered floor field and every natural number `n`,
$$ \sum_{i=0}^{n-1} \left\lfloor x + \frac{i}{n} \right\rfloor = \lfloor n x \rfloor. $$

## Main statements

* `Int.sum_floor_add_div`: Hermite's identity, `∑ i ∈ Finset.range n, ⌊x + i / n⌋ = ⌊n * x⌋`.

-/

namespace Int

/-- The discrete (integer) form of Hermite's identity: the sum of `(m + i) / n` over a
complete block `0 ≤ i < n` of consecutive shifts equals `m`, with Euclidean quotients. -/
public theorem sum_range_add_ediv (m : ℤ) {n : ℕ} (hn : 0 < n) :
    ∑ i ∈ Finset.range n, Int.euclideanDiv (m + i) n (Int.ofNat_ne_zero.2 hn.ne') = m := by
  have hn' : (0 : ℤ) < n := Int.natCast_pos.mpr hn
  have hb : (n : ℤ) ≠ 0 := Int.ofNat_ne_zero.2 hn.ne'
  lift m % (n : ℤ) to ℕ using (Int.emod_nonneg m hb) with t ht
  have htn : t < n := by
    exact_mod_cast (show (t : ℤ) < (n : ℤ) from ht ▸ Int.emod_lt_of_pos m hn')
  have hnabs : ((n : ℤ).natAbs : ℤ) = (n : ℤ) := by simp
  let q := Int.euclideanDiv m n hb
  have hrec : (n : ℤ) * q + (t : ℤ) = m := by
    rw [ht]
    exact Int.euclideanDiv_mul_add_mod m (n : ℤ) hb
  calc
    _ = ∑ i ∈ Finset.range n, (q + if n - t ≤ i then 1 else 0) :=
      Finset.sum_congr rfl fun i hi ↦ by
        have hi' : i < n := Finset.mem_range.mp hi
        by_cases h : n - t ≤ i
        · rw [ite_eq_left h]
          refine Int.euclideanDiv_eq_of_remainder (r := (t : ℤ) + i - n) hb ?_ ?_ ?_
          · rw [mul_add, mul_one]
            omega
          · omega
          · rw [hnabs]
            omega
        · simp only [ite_eq_right h, add_zero]
          refine Int.euclideanDiv_eq_of_remainder (r := (t : ℤ) + i) hb ?_ ?_ ?_
          · omega
          · omega
          · rw [hnabs]
            omega
    _ = n * q + (Finset.Ico (n - t) n).card := by
      simp [Finset.sum_add_distrib, -tsub_le_iff_right, -Nat.sub_le_iff_le_add,
        ← Nat.Ico_zero_eq_range]
    _ = m := by
      have hcard : (Finset.Ico (n - t) n).card = t := by
        rw [Nat.card_Ico]
        omega
      rw [hcard]
      exact hrec

/-- **Hermite's identity** for the floor function: for every `x` in a linearly ordered
floor field and every `n : ℕ`, `∑ i ∈ Finset.range n, ⌊x + i / n⌋ = ⌊n * x⌋`. -/
public theorem sum_floor_add_div
    {α : Type*} [Field α] [LinearOrder α] [IsOrderedRing α] [FloorRing α] (x : α) (n : ℕ)
    {hn : IsUnit (n : α)} :
    ∑ i ∈ Finset.range n, ⌊x + (i : α) / (n : α)⌋ = ⌊n * x⌋ := by
  have hn₀ : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
  calc
    _ = ∑ i ∈ Finset.range n,
        Int.euclideanDiv (⌊(n : α) * x⌋ + (i : ℤ)) n (Int.ofNat_ne_zero.2 hn₀.ne') :=
        Finset.sum_congr rfl fun i _ ↦ by
          rw [← floor_add_natCast, ← floor_div_natCast (hn := hn), add_div, mul_div_cancel_left₀]
    _ = ⌊(n : α) * x⌋ := sum_range_add_ediv _ hn₀

end Int
