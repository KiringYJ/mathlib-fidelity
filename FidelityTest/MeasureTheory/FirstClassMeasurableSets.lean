/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.SigmaAlgebra.Basic

/-! Test the Boolean algebra and countable operations of first-class measurable sets. -/

variable {α : Type*}

variable (𝓐 : SigmaAlgebra α) (A B : 𝓐) (x : α)

example : (fun s : Set α ↦ s ∈ 𝓐) = MeasurableSet (𝓐 := 𝓐) := rfl

example : x ∈ A ↔ x ∈ (A : Set α) := Iff.rfl

example : ((Aᶜ : 𝓐) : Set α) = (A : Set α)ᶜ := rfl

example : ((A ∪ B : 𝓐) : Set α) = (A : Set α) ∪ (B : Set α) := rfl

example : ((A ∩ B : 𝓐) : Set α) = (A : Set α) ∩ (B : Set α) := rfl

example : ((A \ B : 𝓐) : Set α) = (A : Set α) \ (B : Set α) := rfl

example : A ⊔ Aᶜ = (⊤ : 𝓐) := sup_compl_eq_top

example {ι : Type*} [Countable ι] (C : ι → 𝓐) :
    (𝓐.countableUnion C : Set α) = ⋃ i, (C i : Set α) := rfl

example {ι : Type*} [Countable ι] (C : ι → 𝓐) :
    (𝓐.countableInter C : Set α) = ⋂ i, (C i : Set α) := rfl

example (s : Set α) (hs : s ∈ 𝓐) : MeasurableSet (𝓐 := 𝓐) s := hs
