import Mathlib.Analysis.Normed.Operator.Fredholm.Open

/-!
# Strict index of linear maps

These tests ensure that the index of a linear map is defined exactly for Fredholm maps between
vector spaces, those with finite-dimensional kernel and cokernel, so that an infinite-dimensional
kernel or cokernel no longer counts as zero.
-/

open Module

/-- info: Unknown constant `LinearMap.index_of_subsingleton` -/
#guard_msgs in
#check_failure LinearMap.index_of_subsingleton

/-- info: Unknown constant `ContinuousLinearMap.index_continuousOn_isFredholm` -/
#guard_msgs in
#check_failure ContinuousLinearMap.index_continuousOn_isFredholm

/-! The zero map from an infinite-dimensional space to `0` is not Fredholm: its kernel is
everything. Its former index was `0`. -/

example : ¬(0 : (ℕ →₀ ℚ) →ₗ[ℚ] Unit).IsFredholm := by
  rintro ⟨h, -⟩
  rw [LinearMap.ker_zero] at h
  have : FiniteDimensional ℚ (ℕ →₀ ℚ) := Submodule.topEquiv.finiteDimensional
  have := Module.Finite.finite_basis (Finsupp.basisSingleOne (R := ℚ) (ι := ℕ))
  exact not_finite ℕ

/-! Maps between finite-dimensional spaces are Fredholm, and their index is the difference of the
dimensions. -/

example (f : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 2 → ℚ)) :
    f.index (.of_finiteDimensional f) = 1 := by
  rw [LinearMap.index_eq_of_finiteDimensional]
  simp

/-- The index is additive under composition. -/
example {k M N P : Type*} [DivisionRing k] [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module k M] [Module k N] [Module k P] {f : M →ₗ[k] N} {g : N →ₗ[k] P}
    (hf : f.IsFredholm) (hg : g.IsFredholm) :
    (g ∘ₗ f).index (hg.comp hf) = g.index hg + f.index hf :=
  LinearMap.index_comp hg hf
