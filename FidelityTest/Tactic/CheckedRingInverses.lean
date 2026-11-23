import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

/-!
# `ring` with checked inverses of monomials

`ring` and `ring_nf` split the checked inverse of a monomial into the checked inverses of its
factors, using the invertibility evidence that the monomial carries. The evidence of a factor is
derived from the evidence of the monomial: a factor of a unit is a unit, and the base of a positive
power that is a unit is a unit. The base of a power with a variable exponent need not be a unit,
since the exponent may be `0`, so the inverse of such a power remains an atom.

The hypotheses of the examples are used only through the default evidence tactic.
-/

set_option linter.unusedVariables false

section Field

variable {K : Type*} [Field K] {a b c x y : K}

/-! ### Splitting the inverse of a monomial -/

example (ha : a ≠ 0) (hb : b ≠ 0) : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by ring

example (ha : a ≠ 0) (hb : b ≠ 0) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by ring

example (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) : (a * b * c)⁻¹ = a⁻¹ * b⁻¹ * c⁻¹ := by ring

example (ha : a ≠ 0) (hb : b ≠ 0) : (a ^ 2 * b)⁻¹ = (a⁻¹) ^ 2 * b⁻¹ := by ring

example (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    (a ^ 2 * b ^ 3 * c)⁻¹ * (a ^ 2 * b ^ 3 * c)⁻¹ = (a⁻¹) ^ 4 * (b⁻¹) ^ 6 * c⁻¹ ^ 2 := by
  ring

example (hx : x ≠ 0) : x⁻¹ ^ 2 = (x ^ 2)⁻¹ := by ring

example (hx : x ≠ 0) (hy : y ≠ 0) : (x ^ 2 * y)⁻¹ = (y * x ^ 2)⁻¹ := by ring

example (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) : a / (b * c) = a * b⁻¹ * c⁻¹ := by ring

example (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) : a / (b * c) = a / b / c := by ring

example (hx : x ≠ 0) (hy : y ≠ 0) : (x ^ 2)⁻¹ / y = (x⁻¹) ^ 2 * y⁻¹ := by ring

/-- `ring` does not cancel `a * a⁻¹`. -/
example (ha : a ≠ 0) (hb : b ≠ 0) : (a * b)⁻¹ * a = a * a⁻¹ * b⁻¹ := by ring

example (ha : a ≠ 0) (hb : b ≠ 0) : (a * b)⁻¹ * a = b⁻¹ := by
  fail_if_success ring1
  rw [mul_inv₀, mul_comm a⁻¹, mul_assoc, inv_mul_cancel₀, mul_one]

/-! ### Numeric coefficients -/

section CharZero

variable [CharZero K]

example (hb : b ≠ 0) : (2 * b)⁻¹ = 2⁻¹ * b⁻¹ := by ring

example (hb : b ≠ 0) : (2 * b)⁻¹ = b⁻¹ / 2 := by ring

example (hb : b ≠ 0) : (2 * b)⁻¹ * 2 = b⁻¹ := by ring

example (hb : b ≠ 0) : (-b)⁻¹ = -b⁻¹ := by ring

example (ha : a ≠ 0) (hb : b ≠ 0) : (6 * a * b)⁻¹ = (a⁻¹ * b⁻¹) / 6 := by ring

example (ha : a ≠ 0) (hb : b ≠ 0) : a / (2 * b) = a * b⁻¹ / 2 := by ring

end CharZero

/-- The evidence for a numeral comes from the evidence for the product. -/
example (h : IsUnit (2 * b)) : (2 * b)⁻¹ = 2⁻¹ * b⁻¹ := by ring

/-! ### Variable exponents give no evidence for the base -/

example (n : ℕ) (hx : x ≠ 0) (hy : y ≠ 0) : (x ^ n * y)⁻¹ = y⁻¹ * (x ^ n)⁻¹ := by ring

example (n m : ℕ) (hx : x ≠ 0) (hy : y ≠ 0) :
    (x ^ n * y ^ m)⁻¹ = (x ^ n)⁻¹ * (y ^ m)⁻¹ := by
  ring

/-- Only the evidence for `x ^ n` is available, not the evidence for `x`. -/
example (n : ℕ) (h : IsUnit (x ^ n)) (hy : IsUnit y) : (x ^ n * y)⁻¹ = y⁻¹ * (x ^ n)⁻¹ := by
  ring

example (n : ℕ) (hx : x ≠ 0) : (x ^ (n + 1))⁻¹ = x⁻¹ * (x ^ n)⁻¹ := by ring

example (n : ℕ) (hx : x ≠ 0) : y / x ^ n = y * (x ^ n)⁻¹ := by ring

example (n : ℕ) (hx : x ≠ 0) : (x ^ n)⁻¹ = (x⁻¹) ^ n := by
  fail_if_success ring1
  exact (inv_pow₀ n).symm

/-- A positive exponent that is not a numeral gives the evidence for the base. -/
example [CharZero K] (n k : ℕ) (ha : a ≠ 0) :
    ((2 * a) ^ ((n + 1) ^ k))⁻¹ = ((2 * a)⁻¹) ^ ((n + 1) ^ k) := by
  ring

/-! ### Sums are inverted as atoms -/

example (h1 : a + b ≠ 0) (h2 : b + a ≠ 0) : (a + b)⁻¹ = (b + a)⁻¹ := by ring

example (n k : ℕ) (hab : a + b ≠ 0) (hb : b ≠ 0) :
    (b * (a + b) ^ ((n + 1) ^ k))⁻¹ = b⁻¹ * ((a + b)⁻¹) ^ ((n + 1) ^ k) := by
  ring

end Field

section Semifield

variable {S : Type*} [Semifield S] {p q r : S}

example (hp : IsUnit p) (hq : IsUnit q) : (p * q)⁻¹ = p⁻¹ * q⁻¹ := by ring

example (hp : IsUnit p) (hq : IsUnit q) (hr : IsUnit r) : p / (q * r) = p * q⁻¹ * r⁻¹ := by ring

end Semifield

section Concrete

example (b : ℚ) (hb : b ≠ 0) : (b * 2)⁻¹ = b⁻¹ * (1 / 2) := by ring

example (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by ring

example (b : ℝ) (hb : b ≠ 0) : (2 * b)⁻¹ = 2⁻¹ * b⁻¹ := by ring

example (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) : (a ^ 2 * b)⁻¹ = (a⁻¹) ^ 2 * b⁻¹ := by ring

example (a b c : ℝ) (hb : b ≠ 0) (hc : c ≠ 0) : a / (b * c) = a * b⁻¹ * c⁻¹ := by ring

end Concrete

/-! ### `ring_nf` prints ordinary notation -/

section ring_nf

example (P : ℝ → Prop) (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : P ((2 * a * b)⁻¹ + b / (a * 4))) : P (b * a⁻¹ * (1 / 4) + a⁻¹ * b⁻¹ * (1 / 2)) := by
  ring_nf at h
  exact h

example {K : Type*} [Field K] (P : K → Prop) (n : ℕ) (x y : K) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : P ((x ^ n * y)⁻¹)) : P ((x ^ n)⁻¹ * y⁻¹) := by
  ring_nf at h
  exact h

end ring_nf
