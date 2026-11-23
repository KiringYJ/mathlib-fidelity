import Mathlib.Algebra.DualNumber

open DualNumber

/-! Inversion is available exactly for dual numbers with unit constant term. -/

example [Nontrivial R] [Ring R] : ¬IsUnit (ε : R[ε]) := by
  fail_if_success have : R[ε] := (ε : R[ε])⁻¹
  exact not_isUnit_eps

/--
error: failed to synthesize
  Inv ℤ[ε]

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth Inv ℤ[ε]

example {R M : Type*} [Semiring R] [AddCommGroup M] [Module Rᵐᵒᵖ M] [Module R M]
    (x : TrivSqZeroExt R M) (hx : IsUnit x.fst) : ∃ y, y * x = 1 := by
  fail_if_success have : TrivSqZeroExt R M := TrivSqZeroExt.inverse x hx
  exact ⟨_, TrivSqZeroExt.mul_left_eq_one _ x hx.val_inv_mul⟩

example : TrivSqZeroExt.inverse (1 + ε : ℤ[ε]) (by simp) = 1 - ε := by
  ext <;> simp
