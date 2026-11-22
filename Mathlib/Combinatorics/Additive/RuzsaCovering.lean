/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Action.Pointwise.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Preorder.Finite
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.Positivity.Finset

/-!
# Ruzsa's covering lemma

This file proves the Ruzsa covering lemma. This says that, for `A`, `B` finsets, we can cover `A`
with at most `#(A + B) / #B` copies of `B - B`.
-/

public section

open scoped Pointwise

variable {G : Type*} [Group G] {K : ℝ}

namespace Finset
variable [DecidableEq G] {A B : Finset G}

/-- **Ruzsa's covering lemma**. -/
@[to_additive ruzsa_covering_add_neg /-- **Ruzsa's covering lemma**, in additive form. -/]
theorem ruzsa_covering_mul (hB : B.Nonempty) (hK : #(A * B) ≤ K * #B) :
    ∃ F ⊆ A, #F ≤ K ∧ A ⊆ F * (B * B⁻¹) := by
  have : ∀ F, Decidable ((F : Set G).PairwiseDisjoint (· • B)) := fun F ↦ Classical.dec _
  set C := {F ∈ A.powerset | (SetLike.coe F).PairwiseDisjoint (· • B)}
  obtain ⟨F, hFmax⟩ := C.exists_maximal <| filter_nonempty_iff.2
    ⟨∅, empty_mem_powerset _, by simp [coe_empty]⟩
  simp only [C, mem_filter, mem_powerset] at hFmax
  obtain ⟨hFA, hF⟩ := hFmax.1
  refine ⟨F, hFA, le_of_mul_le_mul_right ?_ (by positivity : (0 : ℝ) < #B), fun a ha ↦ ?_⟩
  · calc
      (#F * #B : ℝ) = #(F * B) := by
        rw [card_mul_iff.2 <| pairwiseDisjoint_smul_iff.1 hF, Nat.cast_mul]
      _ ≤ #(A * B) := by gcongr
      _ ≤ K * #B := hK
  by_cases hau : a ∈ F
  · obtain ⟨b, hb⟩ := hB
    apply subset_mul_left _ _ hau
    simpa only [mul_inv_cancel] using mul_mem_mul hb (inv_mem_inv hb)
  by_cases! H : ∀ b ∈ F, Disjoint (a • B) (b • B)
  · refine (hFmax.not_gt ?_ <| ssubset_insert hau).elim
    rw [insert_subset_iff, coe_insert]
    exact ⟨⟨ha, hFA⟩, hF.insert fun _ hb _ ↦ H _ hb⟩
  simp_rw [not_disjoint_iff, ← inv_smul_mem_iff] at H
  obtain ⟨b, hb, c, hc₁, hc₂⟩ := H
  exact mem_mul.2 ⟨b, hb, b⁻¹ * a,
    mem_mul.2 ⟨_, hc₂, _, inv_mem_inv hc₁, by simp [mul_assoc]⟩, by simp⟩

/-- **Ruzsa's covering lemma** for the difference set. -/
theorem ruzsa_covering_add {H : Type*} [AddGroup H] [DecidableEq H] {A B : Finset H}
    (hB : B.Nonempty) (hK : #(A + B) ≤ K * #B) :
    ∃ F ⊆ A, #F ≤ K ∧ A ⊆ F + (B - B) := by
  simpa only [sub_eq_add_neg] using ruzsa_covering_add_neg hB hK

end Finset

namespace Set
variable {A B : Set G}

/-- **Ruzsa's covering lemma** for sets. See also `Finset.ruzsa_covering_mul`. -/
@[to_additive ruzsa_covering_add_neg /-- **Ruzsa's covering lemma** for additive sets. -/]
lemma ruzsa_covering_mul (hA : A.Finite) (hB : B.Finite) (hB₀ : B.Nonempty)
    (hK : Nat.card (A * B) ≤ K * Nat.card B) :
    ∃ F ⊆ A, Nat.card F ≤ K ∧ A ⊆ F * (B * B⁻¹) ∧ F.Finite := by
  lift A to Finset G using hA
  lift B to Finset G using hB
  classical
  obtain ⟨F, hFA, hF, hAF⟩ := Finset.ruzsa_covering_mul hB₀ (by simpa [← Finset.coe_mul] using hK)
  exact ⟨F, by norm_cast; simp [*]⟩

/-- **Ruzsa's covering lemma** for sets. See also `Finset.ruzsa_covering_add`. -/
lemma ruzsa_covering_add {H : Type*} [AddGroup H] {A B : Set H}
    (hA : A.Finite) (hB : B.Finite) (hB₀ : B.Nonempty) (hK : Nat.card (A + B) ≤ K * Nat.card B) :
    ∃ F ⊆ A, Nat.card F ≤ K ∧ A ⊆ F + (B - B) ∧ F.Finite := by
  simpa only [sub_eq_add_neg] using ruzsa_covering_add_neg hA hB hB₀ hK

end Set
