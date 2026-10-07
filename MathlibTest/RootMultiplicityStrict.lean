import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Data.ZMod.Defs

/-!
# The multiplicity of a root takes the nonvanishing of the polynomial

`rootMultiplicity a p hp` is the largest `n` such that `(X - C a) ^ n` divides `p`, for a nonzero
polynomial `p`; the proof `hp` is found by `nonzero_tac`. Every power of `X - C a` divides `0`, so
the zero polynomial has infinite multiplicity, which `emultiplicity` records.
-/

open Polynomial

/-! The lemmas that stated the value `0` at the zero polynomial are removed. -/

/-- info: Unknown identifier `rootMultiplicity_zero` -/
#guard_msgs in
#check_failure rootMultiplicity_zero

/-- info: Unknown identifier `rootMultiplicity_pos'` -/
#guard_msgs in
#check_failure rootMultiplicity_pos'

/-- info: Unknown identifier `rootMultiplicity_sub_one_le_derivative_rootMultiplicity` -/
#guard_msgs in
#check_failure rootMultiplicity_sub_one_le_derivative_rootMultiplicity

/-! The default discharger handles hypotheses, monic polynomials, products, and powers. -/

example (p : ℤ[X]) (hp : p ≠ 0) (a : ℤ) : (X - C a) ^ p.rootMultiplicity a ∣ p :=
  pow_rootMultiplicity_dvd p a hp

example (a b : ℤ) : rootMultiplicity a (X - C b) = if a = b then 1 else 0 :=
  rootMultiplicity_X_sub_C

example (a : ℤ) (n : ℕ) : rootMultiplicity a ((X - C a) ^ n) = n :=
  rootMultiplicity_X_sub_C_pow a n

example (p q : ℤ[X]) (hp : p ≠ 0) (hq : q ≠ 0) (a : ℤ) :
    rootMultiplicity a (p * q ^ 2) = rootMultiplicity a p + rootMultiplicity a (q ^ 2) :=
  rootMultiplicity_mul _

example (p : ℤ[X]) (hp : p ≠ 0) (a : ℤ) : 0 < p.rootMultiplicity a ↔ p.IsRoot a := by
  simp

/-! The multiplicity at the zero polynomial is infinite. -/

example (a : ℤ) : emultiplicity (X - C a) (0 : ℤ[X]) = ⊤ := emultiplicity_zero _

/-! Without a proof that the polynomial is nonzero, there is no multiplicity. -/

/--
error: could not synthesize default value for parameter 'hp' using tactics
---
error: the polynomial must be nonzero
p : ℤ[X]
a : ℤ
⊢ p ≠ 0
-/
#guard_msgs in
noncomputable example (p : ℤ[X]) (a : ℤ) : ℕ := rootMultiplicity a p

/-! Products are nonzero only over a ring without zero divisors. -/

/--
error: could not synthesize default value for parameter 'hp' using tactics
---
error: the polynomial must be nonzero
p q : (ZMod 4)[X]
hp : p ≠ 0
hq : q ≠ 0
a : ZMod 4
⊢ p * q ≠ 0
-/
#guard_msgs in
noncomputable example (p q : (ZMod 4)[X]) (hp : p ≠ 0) (hq : q ≠ 0) (a : ZMod 4) : ℕ :=
  rootMultiplicity a (p * q)

/-! The rules only unify at reducible and instance transparency, so that a hypothesis about another
concrete polynomial is rejected without unfolding powers. -/

/--
error: could not synthesize default value for parameter 'hp' using tactics
---
error: the polynomial must be nonzero
h : X ^ 1000 + 1 ≠ 0
a : ℤ
⊢ X ^ 1001 + 1 ≠ 0
-/
#guard_msgs in
noncomputable example (h : (X ^ 1000 + 1 : ℤ[X]) ≠ 0) (a : ℤ) : ℕ :=
  rootMultiplicity a (X ^ 1001 + 1)

/-! The discharger never chooses an undetermined polynomial. -/

/--
error: could not synthesize default value for parameter 'hp' using tactics
---
error: the polynomial is not determined; pass its nonvanishing explicitly
-/
#guard_msgs in
example (a : ℤ) : rootMultiplicity a _ = rootMultiplicity a X := rfl
