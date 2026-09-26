import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# Root numbers of primitive Dirichlet characters

These tests ensure that the root number requires both a positive modulus and explicit primitivity
evidence, while the unique character modulo 1 remains in its domain.
-/

open DirichletCharacter

example {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : IsPrimitive χ) (s : ℂ) :
    completedLFunction χ (1 - s) =
      N ^ (s - 1 / 2) * rootNumber χ hχ * completedLFunction χ⁻¹ s :=
  hχ.completedLFunction_one_sub s

example (χ : DirichletCharacter ℂ 1) (hχ₁ hχ₂ : IsPrimitive χ) :
    rootNumber χ hχ₁ = rootNumber χ hχ₂ ∧ rootNumber χ hχ₁ = 1 := by
  simp

example : rootNumber (1 : DirichletCharacter ℂ 1) isPrimitive_one_level_one = 1 := by
  simp

set_option linter.unusedVariables false in
example {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : True := by
  fail_if_success
    let _ε : ℂ := rootNumber χ
  trivial

example : ¬ IsPrimitive (1 : DirichletCharacter ℂ 2) := by
  rw [isPrimitive_def, conductor_one]
  norm_num

example : True := by
  fail_if_success
    let _ε : ℂ := rootNumber (1 : DirichletCharacter ℂ 2)
  trivial

example : IsPrimitive (1 : DirichletCharacter ℂ 0) :=
  isPrimitive_one_level_zero

example : True := by
  fail_if_success
    let _ε : ℂ := rootNumber (1 : DirichletCharacter ℂ 0) isPrimitive_one_level_zero
  trivial
