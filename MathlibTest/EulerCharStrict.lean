import Mathlib.Algebra.Homology.EulerCharacteristic

/-!
# Strict Euler characteristics

These tests ensure that the Euler characteristic of a graded module is defined exactly for graded
modules of finite rank, so that an infinite rank support or an object of infinite rank no longer
gives the value `0`, and that over a division ring the domain is finite total dimension.
-/

open CategoryTheory ComplexShape

/-- A graded vector space over `ℚ` with `ℚ²` in degree `0`, `ℚ` in degree `1`, and `0` elsewhere. -/
private noncomputable def X : GradedObject ℤ (ModuleCat.{0} ℚ) := fun i ↦
  ModuleCat.of ℚ (Fin (if i = 0 then 2 else if i = 1 then 1 else 0) → ℚ)

private lemma X_finrank (i : ℤ) :
    Module.finrank ℚ (X i) = if i = 0 then 2 else if i = 1 then 1 else 0 := by
  exact Module.finrank_fin_fun ℚ

private lemma X_hasFiniteRank : GradedObject.HasFiniteRank X := by
  rw [GradedObject.hasFiniteRank_iff_finiteDimensional]
  refine ⟨fun i ↦ by unfold X; infer_instance,
    (Set.toFinite ({0, 1} : Set ℤ)).subset fun i hi ↦ ?_⟩
  by_contra h
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at h
  simp only [Set.mem_ofPred_eq, X, h.1, h.2, ↓reduceIte] at hi
  exact not_nontrivial _ hi

example : GradedObject.eulerChar (up ℤ) X X_hasFiniteRank = 1 := by
  rw [GradedObject.eulerChar_eq_sum_finSet_of_finrankSupport_subset _ _ _ {0, 1}]
  · simp [X_finrank]
  · intro i hi
    simp only [GradedObject.finrankSupport, Function.mem_support, X_finrank] at hi
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    by_contra h
    simp [not_or.1 h] at hi

/-- `ℚ` in every degree has infinite rank support, so it has no Euler characteristic. Its former
Euler characteristic was `0`. -/
example : ¬GradedObject.HasFiniteRank (fun _ : ℤ ↦ ModuleCat.of ℚ ℚ) := by
  rintro ⟨-, h⟩
  apply Set.infinite_univ (α := ℤ)
  convert h
  ext i
  simp [GradedObject.finrankSupport]

/-- An object of infinite rank has no rank to add, so it has no Euler characteristic. -/
example : ¬GradedObject.HasFiniteRank (fun _ : Unit ↦ ModuleCat.of ℚ (ℕ →₀ ℚ)) := by
  rintro ⟨h, -⟩
  have := h ()
  simp at this
