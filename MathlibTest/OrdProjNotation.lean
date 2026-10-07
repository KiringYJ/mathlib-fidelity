import Mathlib.Data.Nat.Factorization.Basic

/-!
# The `p`-part of a natural number is a declaration

`Nat.ordProj n p` is the factor at `p` of the prime factorization of `n`, and `Nat.ordCompl n p`
is the complementary part. They are declarations with the argument order of `n.factorization p`;
there are no bracket notations `ordProj[p] n` and `ordCompl[p] n`.
-/

open Nat

example (n p : ℕ) : n.ordProj p = p ^ n.factorization p := ordProj_def n p

example (n p : ℕ) : n.ordCompl p = n / n.ordProj p := ordCompl_def n p

example (n p : ℕ) : n.ordProj p * n.ordCompl p = n := ordProj_mul_ordCompl_eq_self n p

example (n p : ℕ) (hp : p.Prime) (hn : n ≠ 0) : ¬p ∣ n.ordCompl p := not_dvd_ordCompl hp hn

/-! The bracket forms are element lookups on the functions, not notation. -/

/--
error: failed to synthesize instance of type class
  GetElem (ℕ → ℕ → ℕ) ℕ ?_ ?_

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
---
error: Function expected at
  ordProj[2]
but this term has type
  ?_

Note: Expected a function because this term is being applied to the argument
  n
---
error: failed to prove index is valid, possible solutions:
  - Use `have`-expressions to prove the index is valid
  - Use `a[i]!` notation instead, runtime check is performed, and 'Panic' error message is produced if index is not valid
  - Use `a[i]?` notation instead, result is an `Option` type
  - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
n : ℕ
⊢ ?_ ordProj 2
-/
#guard_msgs in
example (n : ℕ) : ℕ := ordProj[2] n

/--
error: failed to synthesize instance of type class
  GetElem (ℕ → ℕ → ℕ) ℕ ?_ ?_

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
---
error: Function expected at
  ordCompl[2]
but this term has type
  ?_

Note: Expected a function because this term is being applied to the argument
  n
---
error: failed to prove index is valid, possible solutions:
  - Use `have`-expressions to prove the index is valid
  - Use `a[i]!` notation instead, runtime check is performed, and 'Panic' error message is produced if index is not valid
  - Use `a[i]?` notation instead, result is an `Option` type
  - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
n : ℕ
⊢ ?_ ordCompl 2
-/
#guard_msgs in
example (n : ℕ) : ℕ := ordCompl[2] n
