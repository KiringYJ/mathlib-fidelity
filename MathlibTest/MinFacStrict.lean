import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime

/-!
# The least prime factor needs `n ≠ 1`

These tests ensure that `Nat.minFac` takes a proof that its argument is not `1`, which has no prime
factor, while `0`, which every prime divides, keeps its least prime factor `2`.
-/

/-- info: Unknown constant `Nat.minFac_one` -/
#guard_msgs in
#check_failure Nat.minFac_one

/-- info: Unknown constant `Nat.minFac_eq_one_iff` -/
#guard_msgs in
#check_failure Nat.minFac_eq_one_iff

/-- info: Unknown constant `Nat.minFac_prime_iff` -/
#guard_msgs in
#check_failure Nat.minFac_prime_iff

/-! The number `1` has no least prime factor. -/

/--
error: could not synthesize default value for parameter '_hn' using tactics
---
error: `Nat.minFac n` needs a proof that `n ≠ 1`: the number `1` has no prime factor
⊢ 1 ≠ 1
-/
#guard_msgs in
example : ℕ := Nat.minFac 1

/-! The discharger never chooses the argument from a hypothesis. -/

/--
error: could not synthesize default value for parameter '_hn' using tactics
---
error: the argument of `Nat.minFac` is not determined; pass the proof that it is not `1` explicitly
-/
#guard_msgs in
example (k : ℕ) (hk : k ≠ 1) : Nat.minFac _ ∣ k := Nat.minFac_dvd k hk

/-! The least prime factor of `0` is `2`, and the side condition is found from local hypotheses,
by linear arithmetic, from primality, or by evaluation. -/

example : Nat.minFac 0 = 2 := Nat.minFac_zero

example : Nat.minFac 91 = 7 := by norm_num1

example : Nat.minFac (2 ^ 19 - 1) = 2 ^ 19 - 1 := by norm_num1

example (n : ℕ) (hn : n ≠ 1) : (Nat.minFac n).Prime := Nat.minFac_prime hn

example (n : ℕ) (hn : 2 ≤ n) : Nat.minFac n ≤ n := Nat.minFac_le hn

example (p : ℕ) (hp : p.Prime) : Nat.minFac p = p := hp.minFac_eq

example (n : ℕ) (hn : n ≠ 1) : Nat.minFac n = 2 ↔ 2 ∣ n := Nat.minFac_eq_two_iff

example (m n : ℕ) (hm : 2 ≤ m) (hmn : m ∣ n) :
    Nat.minFac n (Nat.ne_one_of_two_le_of_dvd hm hmn) ≤ m :=
  Nat.minFac_le_of_dvd hm hmn
