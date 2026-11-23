import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

/-!
# The finset of primitive roots of unity takes a nonzero order

`primitiveRoots k R` is the finset of primitive `k`-th roots of unity for `k ≠ 0`. The primitive
`0`-th roots of unity are the elements none of whose positive powers is `1`, which form no finite
set in general, so the order carries `[NeZero k]`, as does the modified cyclotomic polynomial
`cyclotomic' n R`, the product of `X - μ` over `primitiveRoots n R`.
-/

open Polynomial

/-! The former values at `0` are removed. -/

/-- info: Unknown identifier `primitiveRoots_zero` -/
#guard_msgs in
#check_failure primitiveRoots_zero

/-- info: Unknown constant `Polynomial.cyclotomic'_zero` -/
#guard_msgs in
#check_failure Polynomial.cyclotomic'_zero

/-- error: failed to synthesize instance of type class
  NeZero 0

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example : Finset ℂ := primitiveRoots 0 ℂ

/-! Membership needs no positivity argument. -/

example (k : ℕ) [NeZero k] (ζ : ℂ) : ζ ∈ primitiveRoots k ℂ ↔ IsPrimitiveRoot ζ k :=
  mem_primitiveRoots

example (k : ℕ) [NeZero k] : (primitiveRoots k ℂ).card = k.totient :=
  Complex.card_primitiveRoots k

/-! A product over the divisors of `n` ranges over nonzero orders. -/

example (n : ℕ) [NeZero n] :
    ∏ i ∈ n.divisors.attach, cyclotomic' i ℂ = X ^ n - 1 :=
  prod_cyclotomic'_eq_X_pow_sub_one (Complex.isPrimitiveRoot_exp n (NeZero.ne n))
