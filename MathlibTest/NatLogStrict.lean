import Mathlib.Data.Int.Log
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.NormNum.NatLog

/-!
# Natural and integer logarithms on their domains

These tests ensure that the floor logarithm `Nat.log b n` takes `1 < b` and `n ≠ 0`, the ceiling
logarithm `Nat.clog b n` takes `1 < b ∨ n ≤ 1`, and `Int.log b r` and `Int.clog b r` take `1 < b`
and `0 < r`, so that no logarithm receives the value `0` outside its domain.
-/

/-- info: Unknown constant `Nat.log_zero_right` -/
#guard_msgs in
#check_failure Nat.log_zero_right

/-- info: Unknown constant `Nat.log_of_left_le_one` -/
#guard_msgs in
#check_failure Nat.log_of_left_le_one

/-- info: Unknown constant `Nat.clog_of_left_le_one` -/
#guard_msgs in
#check_failure Nat.clog_of_left_le_one

/-- info: Unknown constant `Nat.log_monotone` -/
#guard_msgs in
#check_failure Nat.log_monotone

/-- info: Unknown constant `Int.log_zero_right` -/
#guard_msgs in
#check_failure Int.log_zero_right

/-! There is no largest `k` with `2 ^ k ≤ 0`, nor with `1 ^ k ≤ 5`. -/

/--
error: could not synthesize default value for parameter '_hn' using tactics
---
error: the floor logarithm `Nat.log b n` needs `1 < b` and `n ≠ 0`, and the ceiling logarithm `Nat.clog b n` needs `1 < b ∨ n ≤ 1`
⊢ 0 ≠ 0
-/
#guard_msgs in
example : ℕ := Nat.log 2 0

/--
error: could not synthesize default value for parameter '_hb' using tactics
---
error: the floor logarithm `Nat.log b n` needs `1 < b` and `n ≠ 0`, and the ceiling logarithm `Nat.clog b n` needs `1 < b ∨ n ≤ 1`
⊢ 1 < 1
-/
#guard_msgs in
example : ℕ := Nat.log 1 5

/-! There is no least `k` with `5 ≤ 1 ^ k`. -/

/--
error: could not synthesize default value for parameter '_h' using tactics
---
error: the floor logarithm `Nat.log b n` needs `1 < b` and `n ≠ 0`, and the ceiling logarithm `Nat.clog b n` needs `1 < b ∨ n ≤ 1`
⊢ 1 < 1 ∨ 5 ≤ 1
-/
#guard_msgs in
example : ℕ := Nat.clog 1 5

/-! The side conditions are found from the context, and the values are computed. -/

example : Nat.log 2 256 = 8 := by norm_num1

example : Nat.clog 2 257 = 9 := by norm_num1

example : Nat.clog 1 1 = 0 := Nat.clog_one_right 1

example (b n : ℕ) (hb : 2 ≤ b) (hn : 0 < n) : b ^ Nat.log b n ≤ n :=
  Nat.pow_log_le_self (by omega) (by omega)

example (b x y : ℕ) (hb : 1 < b) (hy : y ≠ 0) : x ≤ Nat.log b y ↔ b ^ x ≤ y :=
  Nat.le_log_iff_pow_le hb hy

example (b n : ℕ) (hb : 1 < b) : n ≤ b ^ Nat.clog b n := Nat.le_pow_clog hb n

/-! `Int.log` needs a positive argument. -/

/--
error: could not synthesize default value for parameter '_hr' using tactics
---
error: the logarithms `Int.log b r` and `Int.clog b r` need `1 < b` and `0 < r`
⊢ 0 < 0
-/
#guard_msgs in
example : ℤ := Int.log 2 (0 : ℚ)

example (r : ℚ) (hr : 0 < r) : (2 : ℚ) ^ Int.log 2 r ≤ r := Int.zpow_log_le_self (by norm_num) hr
