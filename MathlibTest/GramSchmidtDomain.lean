/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

open InnerProductSpace Submodule Set

-- Normalization is available at every nonzero orthogonalized vector, even in a dependent family.
example (f : Fin 2 → ℝ) (i : Fin 2) (hi : gramSchmidt ℝ f i ≠ 0) :
    ‖gramSchmidtNormed ℝ f ⟨i, hi⟩‖ = 1 :=
  gramSchmidtNormed_unit_length' _

example (f : Fin 2 → ℝ) : Orthonormal ℝ (gramSchmidtNormed ℝ f) :=
  gramSchmidtNormed_orthonormal' f

example (f : Fin 2 → ℝ) (s : Set (Fin 2)) :
    span ℝ (gramSchmidtNormed ℝ f '' (Subtype.val ⁻¹' s)) = span ℝ (gramSchmidt ℝ f '' s) :=
  span_gramSchmidtNormed f s

example : IsEmpty {i : Fin 2 // gramSchmidt ℝ (0 : Fin 2 → ℝ) i ≠ 0} :=
  ⟨fun i ↦ i.2 (gramSchmidt_zero ℝ (i : Fin 2))⟩

-- Basis extension consumes the actual orthonormal subfamily without values outside its domain.
example {s : Set (Fin 2)} (v : s → EuclideanSpace ℝ (Fin 2)) (hv : Orthonormal ℝ v) :
    ∃ b : OrthonormalBasis (Fin 2) ℝ (EuclideanSpace ℝ (Fin 2)), ∀ i : s, b i = v i :=
  hv.exists_orthonormalBasis_extension_of_card_eq (by simp)

/--
error: Application type mismatch: The argument
  i
has type
  Fin 2
but is expected to have type
  { i // gramSchmidt ℝ 0 i ≠ 0 }
in the application
  gramSchmidtNormed ℝ 0 i
-/
#guard_msgs in
noncomputable example (i : Fin 2) : ℝ := gramSchmidtNormed ℝ (0 : Fin 2 → ℝ) i
