/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Init
public import Mathlib.Lean.Elab.NativeDivision

/-!
# Basic lemmas about division and modulo for integers

-/

public section

namespace Int

/-! ### Euclidean quotient -/

theorem mul_ediv_le_mul_ediv_assoc {a : Int} (ha : 0 ≤ a) (b : Int) {c : Int} (hc : 0 < c) :
    a * Int.euclideanDiv b c (Int.ne_of_gt hc) ≤ Int.euclideanDiv (a * b) c (Int.ne_of_gt hc) := by
  let q := Int.euclideanDiv b c (Int.ne_of_gt hc)
  let p := Int.euclideanDiv (a * b) c (Int.ne_of_gt hc)
  have hb : c * q ≤ b := by
    have hr := Int.emod_nonneg b (Int.ne_of_gt hc)
    have hq := Int.euclideanDiv_mul_add_mod b c (Int.ne_of_gt hc)
    change c * q + b % c = b at hq
    omega
  have hab := Int.mul_le_mul_of_nonneg_left hb ha
  rw [← Int.mul_assoc, Int.mul_comm a c, Int.mul_assoc] at hab
  change a * q ≤ p
  apply Int.le_of_not_gt
  intro h
  have hp := Int.euclideanDiv_mul_add_mod (a * b) c (Int.ne_of_gt hc)
  change c * p + (a * b) % c = a * b at hp
  have hr : (a * b) % c < c := by
    simpa [Int.natAbs_of_nonneg (Int.le_of_lt hc)] using
      Int.emod_lt (a * b) (Int.ne_of_gt hc)
  have hmul := Int.mul_le_mul_of_nonneg_left (show p + 1 ≤ a * q by omega) (Int.le_of_lt hc)
  rw [Int.mul_add, Int.mul_one] at hmul
  omega

/-- Taking two Euclidean quotients with positive divisors is division by their product. -/
theorem euclideanDiv_euclideanDiv_eq_euclideanDiv_mul (m : Int) {n k : Int}
    (hn : 0 < n) (hk : 0 < k) :
    Int.euclideanDiv (Int.euclideanDiv m n (Int.ne_of_gt hn)) k (Int.ne_of_gt hk) =
      Int.euclideanDiv m (n * k) (Int.ne_of_gt (Int.mul_pos hn hk)) := by
  let q := Int.euclideanDiv m n (Int.ne_of_gt hn)
  let p := q.euclideanDiv k (Int.ne_of_gt hk)
  let r := m % n
  let s := q % k
  have hmq : n * q + r = m := Int.euclideanDiv_mul_add_mod m n (Int.ne_of_gt hn)
  have hqp : k * p + s = q := Int.euclideanDiv_mul_add_mod q k (Int.ne_of_gt hk)
  have hr₀ : 0 ≤ r := Int.emod_nonneg _ (Int.ne_of_gt hn)
  have hs₀ : 0 ≤ s := Int.emod_nonneg _ (Int.ne_of_gt hk)
  have hnonneg : 0 ≤ n * s + r := Int.add_nonneg (Int.mul_nonneg (Int.le_of_lt hn) hs₀) hr₀
  have hr : r < n := by
    simpa [Int.natAbs_of_nonneg (Int.le_of_lt hn)] using Int.emod_lt m (Int.ne_of_gt hn)
  have hs : s < k := by
    simpa [Int.natAbs_of_nonneg (Int.le_of_lt hk)] using Int.emod_lt q (Int.ne_of_gt hk)
  have hmul := Int.mul_le_mul_of_nonneg_left (show s + 1 ≤ k by omega) (Int.le_of_lt hn)
  rw [Int.mul_add, Int.mul_one] at hmul
  have hbound : n * s + r < (n * k).natAbs := by
    rw [Int.natAbs_of_nonneg (Int.le_of_lt (Int.mul_pos hn hk))]
    omega
  change p = _
  symm
  apply Int.euclideanDiv_eq_of_remainder _ _ hnonneg hbound
  rw [← hmq, ← hqp, Int.mul_add, Int.mul_assoc, Int.add_assoc]

/-! ### `emod` -/

theorem emod_eq_sub_self_emod {a b : Int} : a % b = (a - b) % b :=
  (sub_emod_right a b).symm

end Int
