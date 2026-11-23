import Mathlib.Algebra.Lie.Weights.RootSystem

/-!
# Lie algebra root chains need a nonzero direction

These tests ensure that the coefficients, ends, and length of the `α`-chain through a weight take
`α ≠ 0`, so that the zero direction, in which every chain is unbounded, no longer gives `0`.
-/

open LieModule LieAlgebra LieAlgebra.IsKilling

/-- info: Unknown constant `LieModule.chainTopCoeff_zero` -/
#guard_msgs in
#check_failure LieModule.chainTopCoeff_zero

/-- info: Unknown constant `LieModule.chainBotCoeff_zero` -/
#guard_msgs in
#check_failure LieModule.chainBotCoeff_zero

/-- info: Unknown constant `LieModule.chainTop_zero` -/
#guard_msgs in
#check_failure LieModule.chainTop_zero

/-- info: Unknown constant `LieAlgebra.IsKilling.chainLength_of_isZero` -/
#guard_msgs in
#check_failure LieAlgebra.IsKilling.chainLength_of_isZero

/-- info: Unknown constant `LieAlgebra.IsKilling.chainLength_zero` -/
#guard_msgs in
#check_failure LieAlgebra.IsKilling.chainLength_zero

section Module

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]
  [LieRingModule L M] [LieModule R L M] [LieRing.IsNilpotent L] [IsAddTorsionFree R] [IsDomain R]
  [Module.IsTorsionFree R M] [IsNoetherian R M]

/-! The chain coefficients need a nonzero direction; they were formerly `0` for `α = 0`. -/

/--
error: Type mismatch
  chainTopCoeff α β
has type
  α ≠ 0 → ℕ
but is expected to have type
  ℕ
-/
#guard_msgs in
noncomputable example (α : L → R) (β : Weight R L M) : ℕ := chainTopCoeff α β

/-- The weight after the top of the chain is not a weight. -/
example (α : L → R) (β : Weight R L M) (hα : α ≠ 0) :
    genWeightSpace M ((chainTopCoeff α β hα + 1) • α + β : L → R) = ⊥ :=
  genWeightSpace_chainTopCoeff_add_one_nsmul_add α β hα

end Module

section Killing

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [IsKilling K L]
  [FiniteDimensional K L] {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsTriangularizable K H L]

/-! The chain length is the sum of the chain coefficients for a nonzero root. -/

example (α β : Weight K H L) (hα : α.IsNonZero) :
    chainBotCoeff α β hα.coe_ne_zero + chainTopCoeff α β hα.coe_ne_zero = chainLength α β hα :=
  chainBotCoeff_add_chainTopCoeff α β hα

example (α β : Weight K H L) (hα : α.IsNonZero) :
    β (coroot α) = (chainBotCoeff α β hα.coe_ne_zero - chainTopCoeff α β hα.coe_ne_zero : ℤ) :=
  apply_coroot_eq_cast α β hα

end Killing
