module

import Mathlib.Algebra.Order.Nonneg.Field
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Quaternion
import Mathlib.Basic.NNReal.Defs
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.LinearAlgebra.Complex.Module

/-! # Rational data of division rings

A division ring of characteristic zero stores its embeddings of `ℚ≥0` and `ℚ` and their scalar
actions as data of its structure. A type with its own embedding or action stores that operation,
so the instances derived from the division ring unfold to it with instance transparency. -/

open scoped NNReal Quaternion

/-! ### Rational numbers -/

example (q : ℚ) : @RatCast.ratCast ℚ DivisionRing.toRatCast q = q := by
  with_reducible_and_instances rfl

example (q : ℚ≥0) : @NNRatCast.nnratCast ℚ≥0 DivisionSemiring.toNNRatCast q = q := by
  with_reducible_and_instances rfl

/-! ### Nonnegative cones and nonnegative reals -/

example {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α] (q : ℚ≥0) :
    @NNRatCast.nnratCast (Nonneg α) DivisionSemiring.toNNRatCast q = ⟨q, q.cast_nonneg⟩ := by
  with_reducible_and_instances rfl

example (q : ℚ≥0) :
    @NNRatCast.nnratCast ℝ≥0 DivisionSemiring.toNNRatCast q = ⟨q, q.cast_nonneg⟩ := by
  with_reducible_and_instances rfl

/-! ### Complex numbers -/

example (q : ℚ) : @RatCast.ratCast ℂ DivisionRing.toRatCast q = ((q : ℝ) : ℂ) := by
  with_reducible_and_instances rfl

example (q : ℚ≥0) : @NNRatCast.nnratCast ℂ DivisionSemiring.toNNRatCast q = ((q : ℝ) : ℂ) := by
  with_reducible_and_instances rfl

example : (Complex.SMul.instSMulRealComplex : SMul ℚ ℂ) = (DivisionRing.toQSMul : SMul ℚ ℂ) := by
  with_reducible_and_instances rfl

/-! ### Subfields and intermediate fields -/

example {L : Type*} [Field L] [CharZero L] (S : Subfield L) (q : ℚ) :
    ((q : S) : L) = q := by
  with_reducible_and_instances rfl

example {L : Type*} [Field L] [CharZero L] (S : Subfield L) (q : ℚ) (x : S) :
    ((q • x : S) : L) = q • (x : L) := by
  with_reducible_and_instances rfl

/-! ### Quaternions and quadratic algebras -/

/-- `ℍ[R]` has no `CharZero` instance of its own; whenever one is supplied, the division ring's
cast is the coefficientwise one. -/
example {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [CharZero ℍ[R]] (q : ℚ) :
    @RatCast.ratCast ℍ[R] DivisionRing.toRatCast q = Quaternion.coe (q : R) := by
  with_reducible_and_instances rfl

example {K : Type*} [Field K] [CharZero K] {a b : K} [Fact (∀ r : K, r ^ 2 ≠ a + b * r)]
    (q : ℚ) :
    @RatCast.ratCast (QuadraticAlgebra K a b) DivisionRing.toRatCast q = ⟨q, 0⟩ := by
  with_reducible_and_instances rfl
