import Mathlib.MeasureTheory.SigmaAlgebra.Constructions

/-!
# Simp normal forms of set systems

These tests check that `simp` still proves the facts whose dedicated simp lemmas were removed,
moved, or reprioritized so that every simp lemma's left-hand side is in simp normal form.
-/

variable {α : Type*}

example (m : SigmaAlgebra α) (x : α) : x ∈ m.indistinguishabilityClass x := by
  simp
