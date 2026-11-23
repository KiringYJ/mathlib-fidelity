/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.GeomSum

/-!
# Partial sums of geometric series in an ordered ring

This file upper- and lower-bounds the values of the geometric series $\sum_{i=0}^{n-1} x^i$ and
$\sum_{i=0}^{n-1} x^i y^{n-1-i}$ and variants thereof. We also provide some bounds on the
"geometric" sum of `a/b^i` where `a b : ℕ`.
-/

public section

assert_not_exists Field

open Finset

variable {R : Type*}

section Semiring
variable [Semiring R] [PartialOrder R] [IsStrictOrderedRing R] {n : ℕ} {x : R}

lemma geom_sum_pos (hx : 0 ≤ x) (hn : n ≠ 0) : 0 < ∑ i ∈ range n, x ^ i :=
  sum_pos' (fun _ _ => pow_nonneg hx _) ⟨0, mem_range.2 hn.bot_lt, by simp⟩

end Semiring

section Ring
variable [Ring R]

section PartialOrder
variable [PartialOrder R]

section IsOrderedRing
variable [IsOrderedRing R] {x : R}

lemma geom_sum_alternating_of_le_neg_one (hx : x + 1 ≤ 0) (n : ℕ) :
    if Even n then (∑ i ∈ range n, x ^ i) ≤ 0 else 1 ≤ ∑ i ∈ range n, x ^ i := by
  have hx0 : x ≤ 0 := (le_add_of_nonneg_right zero_le_one).trans hx
  induction n with
  | zero => simp only [range_zero, sum_empty, le_refl, ite_true, Even.zero]
  | succ n ih =>
    simp only [Nat.even_add_one, geom_sum_succ]
    split_ifs at ih ⊢ with h
    · rw [le_add_iff_nonneg_left]
      exact mul_nonneg_of_nonpos_of_nonpos hx0 ih
    · grw [← hx]
      gcongr
      simpa only [mul_one] using mul_le_mul_of_nonpos_left ih hx0

end IsOrderedRing

section IsStrictOrderedRing
variable [IsStrictOrderedRing R] {n : ℕ} {x : R}

lemma geom_sum_pos_and_lt_one (hx : x < 0) (hx' : 0 < x + 1) (hn : 1 < n) :
    0 < ∑ i ∈ range n, x ^ i ∧ ∑ i ∈ range n, x ^ i < 1 := by
  refine Nat.le_induction ?_ ?_ n (show 2 ≤ n from hn)
  · rw [geom_sum_two]
    exact ⟨hx', (add_lt_iff_neg_right _).2 hx⟩
  clear hn
  intro n _ ihn
  rw [geom_sum_succ, add_lt_iff_neg_right, ← neg_lt_iff_pos_add', neg_mul_eq_neg_mul]
  exact
    ⟨by grw [ihn.2, mul_one, neg_le_iff_add_nonneg', hx']; exact neg_pos.2 hx,
      mul_neg_of_neg_of_pos hx ihn.1⟩

lemma geom_sum_alternating_of_lt_neg_one (hx : x + 1 < 0) (hn : 1 < n) :
    if Even n then ∑ i ∈ range n, x ^ i < 0 else 1 < ∑ i ∈ range n, x ^ i := by
  have hx0 : x < 0 := (le_add_of_nonneg_right zero_le_one).trans_lt hx
  refine Nat.le_induction ?_ ?_ n (show 2 ≤ n from hn)
  · simp only [geom_sum_two, lt_add_iff_pos_left, ite_true, hx, even_two]
  clear hn
  intro n _ ihn
  simp only [Nat.even_add_one, geom_sum_succ]
  split_ifs at ihn ⊢ with hn'
  · rw [lt_add_iff_pos_left]
    exact mul_pos_of_neg_of_neg hx0 ihn
  · grw [← hx.le]
    gcongr
    simpa only [mul_one] using mul_lt_mul_of_neg_left ihn hx0

end IsStrictOrderedRing
end PartialOrder

section LinearOrder
variable [LinearOrder R] [IsStrictOrderedRing R] {n : ℕ} {x : R}

lemma geom_sum_pos' (hx : 0 < x + 1) (hn : n ≠ 0) : 0 < ∑ i ∈ range n, x ^ i := by
  obtain _ | _ | n := n
  · cases hn rfl
  · simp only [zero_add, range_one, sum_singleton, pow_zero, zero_lt_one]
  obtain hx' | hx' := lt_or_ge x 0
  · exact (geom_sum_pos_and_lt_one hx' hx n.one_lt_succ_succ).1
  · exact geom_sum_pos hx' (by simp)

lemma Odd.geom_sum_pos (h : Odd n) : 0 < ∑ i ∈ range n, x ^ i := by
  rcases n with (_ | _ | k)
  · exact (Nat.not_odd_zero h).elim
  · simp only [zero_add, range_one, sum_singleton, pow_zero, zero_lt_one]
  rw [← Nat.not_even_iff_odd] at h
  rcases lt_trichotomy (x + 1) 0 with (hx | hx | hx)
  · have := geom_sum_alternating_of_lt_neg_one hx k.one_lt_succ_succ
    simp only [h, ite_false] at this
    exact zero_lt_one.trans this
  · simp only [eq_neg_of_add_eq_zero_left hx, h, neg_one_geom_sum, ite_false, zero_lt_one]
  · exact geom_sum_pos' hx k.succ.succ_ne_zero

lemma geom_sum_pos_iff (hn : n ≠ 0) : 0 < ∑ i ∈ range n, x ^ i ↔ Odd n ∨ 0 < x + 1 := by
  refine ⟨fun h => ?_, ?_⟩
  · rw [or_iff_not_imp_left, ← not_le, Nat.not_odd_iff_even]
    refine fun hn hx => h.not_ge ?_
    simpa [ite_eq_left hn] using geom_sum_alternating_of_le_neg_one hx n
  · rintro (hn | hx')
    · exact hn.geom_sum_pos
    · exact geom_sum_pos' hx' hn

lemma geom_sum_ne_zero (hx : x ≠ -1) (hn : n ≠ 0) : ∑ i ∈ range n, x ^ i ≠ 0 := by
  obtain _ | _ | n := n
  · cases hn rfl
  · simp only [zero_add, range_one, sum_singleton, pow_zero, ne_eq, one_ne_zero, not_false_eq_true]
  rw [Ne, eq_neg_iff_add_eq_zero, ← Ne] at hx
  obtain h | h := hx.lt_or_gt
  · have := geom_sum_alternating_of_lt_neg_one h n.one_lt_succ_succ
    split_ifs at this
    · exact this.ne
    · exact (zero_lt_one.trans this).ne'
  · exact (geom_sum_pos' h n.succ.succ_ne_zero).ne'

lemma geom_sum_eq_zero_iff_neg_one (hn : n ≠ 0) : ∑ i ∈ range n, x ^ i = 0 ↔ x = -1 ∧ Even n := by
  refine ⟨fun h => ?_, @fun ⟨h, hn⟩ => by simp only [h, hn, neg_one_geom_sum, ite_true]⟩
  contrapose! h
  have hx := eq_or_ne x (-1)
  rcases hx with hx | hx
  · rw [hx, neg_one_geom_sum]
    simp only [h hx, ite_false, ne_eq, one_ne_zero, not_false_eq_true]
  · exact geom_sum_ne_zero hx hn

lemma geom_sum_neg_iff (hn : n ≠ 0) : ∑ i ∈ range n, x ^ i < 0 ↔ Even n ∧ x + 1 < 0 := by
  rw [← not_iff_not, not_lt, le_iff_lt_or_eq, eq_comm,
    or_congr (geom_sum_pos_iff hn) (geom_sum_eq_zero_iff_neg_one hn), ← Nat.not_even_iff_odd, ←
    add_eq_zero_iff_eq_neg, not_and, not_lt, le_iff_lt_or_eq, eq_comm, ← imp_iff_not_or, or_comm,
    and_comm, Decidable.and_or_imp, or_comm]

end LinearOrder
end Ring

/-! ### Geometric sum with `ℕ`-division -/

private lemma euclideanDiv_one (a : ℕ) : Nat.euclideanDiv a 1 Nat.one_ne_zero = a := by
  simpa only [Nat.one_mul] using Nat.euclideanDiv_mul_left_cancel a Nat.one_ne_zero

lemma Nat.pred_mul_geom_sum_le (a b n : ℕ) (hb : b ≠ 0 := by checked_native_nonzero) :
    (b - 1) * ∑ i ∈ range n.succ, Nat.euclideanDiv a (b ^ i) (pow_ne_zero _ hb) ≤
      a * b - Nat.euclideanDiv a (b ^ n) (pow_ne_zero _ hb) := by
  let q (i : ℕ) := Nat.euclideanDiv a (b ^ i) (pow_ne_zero _ hb)
  have hq0 : q 0 = a := by simpa only [q, pow_zero] using euclideanDiv_one a
  calc
    (b - 1) * ∑ i ∈ range n.succ, q i =
        (∑ i ∈ range n, q (i + 1) * b) + a * b - ((∑ i ∈ range n, q i) + q n) := by
      rw [Nat.sub_mul, mul_comm, sum_mul, one_mul, sum_range_succ', sum_range_succ, hq0]
    _ ≤ (∑ i ∈ range n, q i) + a * b - ((∑ i ∈ range n, q i) + q n) := by
      gcongr with i hi
      apply (Nat.le_euclideanDiv_iff_mul_le (a := a) (pow_ne_zero i hb)).2
      have h := (Nat.le_euclideanDiv_iff_mul_le (a := a) (pow_ne_zero (i + 1) hb)).1
        (le_refl (q (i + 1)))
      simpa only [pow_succ, Nat.mul_assoc, Nat.mul_comm b (q (i + 1))] using h
    _ = a * b - q n := add_tsub_add_eq_tsub_left _ _ _

lemma Nat.geom_sum_le {b : ℕ} (hb : 2 ≤ b) (a n : ℕ) :
    ∑ i ∈ range n, Nat.euclideanDiv a (b ^ i) (pow_ne_zero _ (by omega)) ≤
      Nat.euclideanDiv (a * b) (b - 1) (by omega) := by
  refine (Nat.le_euclideanDiv_iff_mul_le (by omega : b - 1 ≠ 0)).2 ?_
  rcases n with - | n
  · rw [sum_range_zero, mul_zero]
    exact Nat.zero_le _
  exact (Nat.pred_mul_geom_sum_le a b n (by omega)).trans tsub_le_self

lemma Nat.geom_sum_Ico_le {b : ℕ} (hb : 2 ≤ b) (a n : ℕ) :
    ∑ i ∈ Ico 1 n, Nat.euclideanDiv a (b ^ i) (pow_ne_zero _ (by omega)) ≤
      Nat.euclideanDiv a (b - 1) (by omega) := by
  rcases n with - | n
  · rw [Ico_eq_empty_of_le (by lia), sum_empty]
    exact Nat.zero_le _
  let q (i : ℕ) := Nat.euclideanDiv a (b ^ i) (pow_ne_zero _ (by omega))
  have hq0 : q 0 = a := by simpa only [q, pow_zero] using euclideanDiv_one a
  have hd : b - 1 ≠ 0 := by omega
  rw [← add_le_add_iff_left a]
  calc
    (a + ∑ i ∈ Ico 1 n.succ, q i) = q 0 + ∑ i ∈ Ico 1 n.succ, q i := by rw [hq0]
    _ = ∑ i ∈ range n.succ, q i := by
      rw [range_eq_Ico, ← Finset.insert_Ico_add_one_left_eq_Ico (Nat.succ_pos _), sum_insert] <;>
        simp
    _ ≤ Nat.euclideanDiv (a * b) (b - 1) hd := Nat.geom_sum_le hb a _
    _ = a + Nat.euclideanDiv a (b - 1) hd := by
      refine Nat.euclideanDiv_eq_of_remainder (r := a % (b - 1)) hd ?_
        (Nat.mod_lt _ (Nat.pos_of_ne_zero hd))
      calc
        a * b = ((b - 1) + 1) * a := by
          rw [Nat.sub_add_cancel (by omega : 1 ≤ b), Nat.mul_comm]
        _ = (b - 1) * a + a := by rw [Nat.add_mul, Nat.one_mul]
        _ = _ := by rw [Nat.mul_add, Nat.add_assoc, Nat.euclideanDiv_mul_add_mod]

variable {m n : ℕ} {s : Finset ℕ}

/-- If all the elements of a finset of naturals are less than `n`, then the sum of their powers of
`m ≥ 2` is less than `m ^ n`. -/
lemma Nat.geomSum_lt (hm : 2 ≤ m) (hs : ∀ k ∈ s, k < n) : ∑ k ∈ s, m ^ k < m ^ n :=
  calc
    ∑ k ∈ s, m ^ k ≤ ∑ k ∈ range n, m ^ k := sum_le_sum_of_subset fun _ hk ↦
      mem_range.2 <| hs _ hk
    _ ≤ (∑ k ∈ range n, m ^ k) * (m - 1) := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left _ (by omega : 1 ≤ m - 1)
    _ < m ^ n := by
      have h := geom_sum_mul_add (m - 1) n
      rw [Nat.sub_add_cancel (by omega : 1 ≤ m)] at h
      rw [← h]
      exact Nat.lt_succ_self _
