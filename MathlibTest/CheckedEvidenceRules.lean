module

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Nonneg.Field
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Basic.NNReal.Defs
import Mathlib.Data.Nat.Cast.Field
import Mathlib.RingTheory.Localization.FractionRing

/-! Evidence rules of the checked operations: literal powers, specialized power hypotheses,
truncated differences, prime and irreducible elements, fraction-field embeddings, and values of
nonnegative and self-adjoint elements. -/

section powers

/-- The evidence of a quotient by a literal power is a power of the base's evidence, so rewriting
with a lemma about the quotient does not need to unfold the power. -/
example (x y : ℝ) (hy : y ≠ 0) : x / y ^ 2 = x * (y ^ 2)⁻¹ := by
  rw [div_eq_mul_inv₀]

example (x y : ℝ) (hy : y ≠ 0) : x / y ^ 2 * y ^ 2 = x := by
  rw [div_mul_cancel₀]

example {K : Type*} [Field K] (a : K) : a ^ (3 : ℤ) = a ^ 3 := by simp

end powers

section casts

example (m n : ℕ) (h : n ∣ m) (hn : (n : ℚ) ≠ 0) : ((m / n : ℕ) : ℚ) = m / n :=
  Nat.cast_div h hn

example (m n : ℕ) (h : n ∣ m) (hn : n ≠ 0) : ((m / n : ℕ) : ℚ) = m / n :=
  Nat.cast_div_charZero h hn

/-- The quotient by a natural quotient finds its evidence from the divisibility hypotheses. -/
example (d m n : ℕ) (hn : d ∣ n) (hm : d ∣ m) (hn0 : n ≠ 0) :
    ((m / d : ℕ) : ℚ) / ((n / d : ℕ) : ℚ) = m / n :=
  Nat.cast_div_div_div_cancel_right hn hm hn0

example (m n : ℤ) (h : n ∣ m) (hn : (n : ℚ) ≠ 0) : ((m / n : ℤ) : ℚ) = m / n :=
  Int.cast_div h hn

example {ι : Type*} (s : Finset ι) (f : ι → ℚ) (a : ℚ) (ha : a ≠ 0) :
    (∑ i ∈ s, f i) / a = ∑ i ∈ s, f i / a :=
  Finset.sum_div s f a

end casts

section rules

open scoped NNReal

/-- A truncated difference is invertible when a hypothesis orders its terms. -/
example (p : ℝ≥0) (hp : 1 < p) : (p - 1)⁻¹ * (p - 1) = 1 := inv_mul_cancel₀

/-- An irreducible or prime element of a domain is nonzero, and so is its image in the fraction
field. -/
example {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (p : R) (hp : Irreducible p) : (algebraMap R K p)⁻¹ * algebraMap R K p = 1 :=
  inv_mul_cancel₀

example {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (p : R) (hp : Prime p) : algebraMap R K p * (algebraMap R K p)⁻¹ = 1 :=
  mul_inv_cancel₀

/-- The values of invertible nonnegative and self-adjoint elements are invertible; on the
negative branch of an integer power, the hypothesis `n < 0 → IsUnit a` is specialized. -/
example {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α] (a : Nonneg α)
    (ha : IsUnit a) : ((a⁻¹ : Nonneg α) : α) = (a : α)⁻¹ :=
  Nonneg.coe_inv a

example {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α] (a : Nonneg α) (n : ℤ)
    (h : n < 0 → IsUnit a) : ((a ^ n : Nonneg α) : α) = (a : α) ^ n :=
  Nonneg.coe_zpow a n

example {R : Type*} [Field R] [StarRing R] (x : selfAdjoint R) (hx : IsUnit x) :
    ((x⁻¹ : selfAdjoint R) : R) = (x : R)⁻¹ :=
  selfAdjoint.val_inv x

end rules
