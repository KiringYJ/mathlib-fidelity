import Mathlib.MeasureTheory.SetAlgebra
import Mathlib.MeasureTheory.SigmaAlgebra.Constructions
import Mathlib.Order.BooleanAlgebra.AlmostEqualPairs
import Mathlib.Order.GeneralizedBooleanSubalgebra

/-!
# Simp normal forms of set systems

These tests check that `simp` still proves the facts whose dedicated simp lemmas were removed,
moved, or reprioritized so that every simp lemma's left-hand side is in simp normal form.
-/

open MeasureTheory

variable {α : Type*}

example (𝒜 : Set (Set α)) : 𝒜 ⊆ generateSetAlgebra 𝒜 := by
  simp

example (𝒜 : Set (Set α)) :
    SigmaAlgebra.generateFrom (generateSetAlgebra 𝒜) = SigmaAlgebra.generateFrom 𝒜 := by
  simp

example (m : SigmaAlgebra α) (x : α) : x ∈ m.indistinguishabilityClass x := by
  simp

example [GeneralizedBooleanAlgebra α] (L : GeneralizedBooleanSubalgebra α) (a : α) :
    a ∈ L.carrier ↔ a ∈ L := by
  simp

open BooleanSubalgebra.AlmostEqualPairs in
example {i k : ℕ} (h : i < k) : singletonLeft i ∈ stage k := by
  simpa using h
