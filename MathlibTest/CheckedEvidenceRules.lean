module

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Nonneg.Field
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Analysis.Normed.Field.Basic
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

section carriedEvidence

-- Equal carried propositions must not accumulate, including on repeated solver invocation.
open Lean Meta Elab Tactic in
example (P : Prop) (x y : {_n : ℕ // P}) : (x : ℕ) = x ∧ (y : ℕ) = y ∧ P := by
  run_tac do
    Checked.addSubtypeFacts
    Checked.addSubtypeFacts
    withMainContext do
      let context ← getLCtx
      let some proposition := context.findFromUserName? `P
        | throwError "the proposition was not found in the local context"
      let count ← context.foldlM (init := 0) fun (count : Nat) declaration => do
        return if ← isDefEq declaration.type proposition.toExpr then count + 1 else count
      unless count == 1 do
        throwError "expected one carried proposition after repeated invocation, found {count}"
  exact ⟨rfl, rfl, by assumption⟩

-- The property is carried by the argument rather than named as a separate hypothesis.
example (x : {r : ℝ // r ≠ 0}) : (x : ℝ) ≠ 0 := by checked_nonzero

noncomputable example : {r : ℝ // r ≠ 0} → ℝ := fun x => (x : ℝ)⁻¹

noncomputable example : {r : ℝ // r ≠ 0} → ℝ :=
  (fun x : {r : ℝ // r ≠ 0} => (x : ℝ))⁻¹

example (x : {r : ℝ // r ≠ 0}) : (x : ℝ) / ‖(x : ℝ)‖ * ‖(x : ℝ)‖ = x :=
  div_mul_cancel₀ (x : ℝ)

example (x : {r : ℝ // 0 < r}) : (x : ℝ)⁻¹ * x = 1 := inv_mul_cancel₀

example {M : Type*} [Monoid M] (x : {r : M // IsUnit r}) :
    (x : M)⁻¹ * x = 1 := inv_mul_cancel₀

example (x y : {r : ℝ // r ≠ 0}) :
    ((x : ℝ) * y)⁻¹ * ((x : ℝ) * y) = 1 := inv_mul_cancel₀

example {K : Type*} [Field K] [CharZero K] : IsUnit (2 : K) := by checked_unit

/--
error: a nonzero denominator proof is required
x y : ℝ
hx : x ≠ 0
hy : y ≠ 0
⊢ x + y ≠ 0
-/
#guard_msgs in
example (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) : x + y ≠ 0 := by
  checked_nonzero

/--
error: a nonzero denominator proof is required
K : Type
inst✝ : Field K
⊢ 2 ≠ 0
-/
#guard_msgs in
example {K : Type} [Field K] : (2 : K) ≠ 0 := by
  checked_nonzero

/--
error: an invertibility proof is required
M : Type
inst✝ : Monoid M
x : M
⊢ IsUnit x
-/
#guard_msgs in
example {M : Type} [Monoid M] (x : M) : IsUnit x := by
  checked_unit

/--
error: could not synthesize default value for parameter 'ha' using tactics
---
error: an invertibility proof is required
x : { r // 0 ≤ r }
h_carried✝ : 0 ≤ ↑x
⊢ IsUnit ↑x
-/
#guard_msgs in
noncomputable example (x : {r : ℝ // 0 ≤ r}) : ℝ := (x : ℝ)⁻¹

end carriedEvidence
