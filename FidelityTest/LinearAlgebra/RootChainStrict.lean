import Mathlib.LinearAlgebra.RootSystem.Chain

/-!
# Root chain coefficients by their extremal specification

These tests ensure that the chain coefficients of two roots are the largest `p` and `q` such that
`β + p • α` and `β - q • α` are roots, for every pair of roots, so that a linearly dependent pair no
longer receives the value `0`, and that the unbroken chain and the reflection identity hold where
they should.
-/

open RootPairing Set

variable {ι R M N : Type*} [Finite ι] [CommRing R] [CharZero R] [IsDomain R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) [P.IsCrystallographic]

/-- info: Unknown constant `RootPairing.chainTopCoeff_of_not_linearIndependent` -/
#guard_msgs in
#check_failure RootPairing.chainTopCoeff_of_not_linearIndependent

/-- info: Unknown constant `RootPairing.chainBotCoeff_of_not_linearIndependent` -/
#guard_msgs in
#check_failure RootPairing.chainBotCoeff_of_not_linearIndependent

/-! A root and itself are linearly dependent; `α - 2 • α = -α` is a root, so the bottom coefficient
is at least `2`. It was formerly `0`. -/

example (i : ι) : 2 ≤ P.chainBotCoeff i i := by
  apply P.le_chainBotCoeff_of_root_sub_nsmul_mem_range
  rw [two_smul, sub_add_cancel_left]
  exact ⟨P.reflectionPerm i i, by simp [root_reflectionPerm, reflection_apply_self]⟩

/-! The reflection identity `q - p = ⟨β, α^∨⟩` holds for every pair of roots. -/

example (i j : ι) : P.chainBotCoeff i j - P.chainTopCoeff i j = P.pairingIn ℤ j i :=
  P.chainBotCoeff_sub_chainTopCoeff

example (i : ι) : (P.chainBotCoeff i i : ℤ) - P.chainTopCoeff i i = 2 := by
  rw [P.chainBotCoeff_sub_chainTopCoeff, pairingIn_same]

/-! For linearly independent roots the chain is unbroken. -/

example (i j : ι) (h : LinearIndependent R ![P.root i, P.root j]) (z : ℤ) :
    P.root j + z • P.root i ∈ range P.root ↔
      z ∈ Icc (-P.chainBotCoeff i j : ℤ) (P.chainTopCoeff i j) :=
  P.root_add_zsmul_mem_range_iff h

/-! The top of the chain is a root, and its own top coefficient is `0`. -/

example (i j : ι) :
    P.root (P.chainTopIdx i j) = P.root j + P.chainTopCoeff i j • P.root i ∧
      P.chainTopCoeff i (P.chainTopIdx i j) = 0 :=
  ⟨P.root_chainTopIdx, P.chainTopCoeff_chainTopIdx⟩
