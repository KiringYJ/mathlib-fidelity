import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Strict limits of monotone sequences

These tests ensure that the limit of a monotone sequence and its index are defined exactly for the
eventually constant sequences, that well-foundedness only supplies that evidence, and that the
index of a generalized eigenspace likewise needs a finite exponent.
-/

/-- info: Unknown constant `WellFoundedGT.iSup_eq_monotonicSequenceLimit` -/
#guard_msgs in
#check_failure WellFoundedGT.iSup_eq_monotonicSequenceLimit

/-- info: Unknown constant `WellFoundedGT.ciSup_eq_monotonicSequenceLimit` -/
#guard_msgs in
#check_failure WellFoundedGT.ciSup_eq_monotonicSequenceLimit

/-! The identity of `ℕ` is not eventually constant, so it has no limit. -/

example : ¬∃ n, ∀ m, n ≤ m → (OrderHom.id : ℕ →o ℕ) n = OrderHom.id m :=
  fun ⟨n, hn⟩ ↦ by simpa using hn (n + 1) (by lia)

/--
error: Type mismatch
  monotonicSequenceLimit OrderHom.id
has type
  (∃ n, ∀ (m : ℕ), n ≤ m → OrderHom.id n = OrderHom.id m) → ℕ
but is expected to have type
  ℕ
-/
#guard_msgs in
noncomputable example : ℕ := monotonicSequenceLimit (OrderHom.id : ℕ →o ℕ)

/-! An eventually constant sequence has its limit and least index. -/

/-- The sequence `n ↦ min n 3`. -/
private def capped : ℕ →o ℕ := ⟨fun n ↦ min n 3, fun _ _ h ↦ min_le_min_right 3 h⟩

private lemma capped_eventually : ∃ n, ∀ m, n ≤ m → capped n = capped m :=
  ⟨3, fun m hm ↦ by change min 3 3 = min m 3; lia⟩

example : monotonicSequenceLimit capped capped_eventually = 3 := by
  have hle : monotonicSequenceLimitIndex capped capped_eventually ≤ 3 :=
    monotonicSequenceLimitIndex_le capped capped_eventually fun m hm ↦ by
      change min 3 3 = min m 3; lia
  rw [monotonicSequenceLimit_eq capped capped_eventually hle]
  rfl

example : iSup capped = monotonicSequenceLimit capped capped_eventually :=
  ciSup_eq_monotonicSequenceLimit capped capped_eventually

/-! Well-foundedness supplies the evidence. -/

example {α : Type*} [CompleteLattice α] [WellFoundedGT α] (a : ℕ →o α) :
    iSup a = monotonicSequenceLimit a (WellFoundedGT.monotone_chain_condition a) :=
  iSup_eq_monotonicSequenceLimit a _

/-! The index of a generalized eigenspace needs a finite exponent, which a Noetherian module
supplies. -/

open Module End in
example {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : End K V) (μ : K) :
    maxUnifEigenspaceIndex f μ (exists_genEigenspace_eq_top f μ) ≤ Module.finrank K V :=
  maxUnifEigenspaceIndex_le_finrank f μ _

open Module End in
example {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (f : End R M) (μ : R)
    (h : ∃ k : ℕ, f.genEigenspace μ k = f.genEigenspace μ ⊤) :
    f.maxGenEigenspace μ = f.genEigenspace μ (maxGenEigenspaceIndex f μ h) :=
  maxGenEigenspace_eq f μ h
