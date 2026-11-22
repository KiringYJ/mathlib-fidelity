/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Algebra.Order.Ring.NNRat
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.Tactic.Positivity.Basic

/-!
# Density of a finite set

This defines the density of a `Finset` and provides induction principles for finsets.

## Main declarations

* `Finset.dens s`: Density of `s : Finset α` in `α` as a nonnegative rational number.

## Implementation notes

There are many other ways to talk about the density of a finset and provide its API:
1. Use the uniform measure
2. Define finitely additive functions and generalise the `Finset.card` API to it. This could either
  be done with
  a. A structure `FinitelyAdditiveFun`
  b. A typeclass `IsFinitelyAdditiveFun`

Solution 1 would mean importing measure theory in simple files (not necessarily bad, but not
amazing), and every single API lemma would require the user to prove that all the sets they are
talking about are measurable in the trivial sigma-algebra (quite terrible user experience).

Solution 2 would mean that some API lemmas about density don't contain `dens` in their name because
they are general results about finitely additive functions. But not all lemmas would be like that
either since some really are `dens`-specific. Hence the user would need to think about whether the
lemma they are looking for is generally true for finitely additive measure or whether it is
`dens`-specific.

On top of this, solution 2.a would break dot notation on `Finset.dens` (possibly fixable by
introducing notation for `⇑Finset.dens`) and solution 2.b would run the risk of being bad
performance-wise.

These considerations more generally apply to `Finset.card` and `Finset.sum` and demonstrate that
overengineering basic definitions is likely to hinder user experience.
-/

@[expose] public section

-- TODO
-- assert_not_exists Ring

open Function Nat

variable {𝕜 α β : Type*} [Fintype α] [Nonempty α]

namespace Finset
variable {s t : Finset α} {a b : α}

/-- Density in a nonempty finite ambient type. The ambient cardinality is the
nonzero denominator; no density is assigned to an empty ambient type. -/
def dens (s : Finset α) : ℚ≥0 :=
  NNRat.divNat s.card (Fintype.card α) Fintype.card_ne_zero

lemma dens_card_cast_ne_zero : (Fintype.card α : ℚ≥0) ≠ 0 :=
  Nat.cast_ne_zero.mpr Fintype.card_ne_zero

private lemma card_cast_pos : (0 : ℚ≥0) < Fintype.card α :=
  Nat.cast_pos.mpr Fintype.card_pos

lemma dens_eq_card_div_card (s : Finset α) :
    dens s = (s.card : ℚ≥0) / (Fintype.card α : ℚ≥0) :=
  NNRat.divNat_eq_div _ _ _

@[simp] lemma dens_mul_card (s : Finset α) : s.dens * Fintype.card α = s.card :=
  NNRat.divNat_mul_den _ _ _

@[simp] lemma card_mul_dens (s : Finset α) : Fintype.card α * s.dens = s.card := by
  rw [mul_comm, dens_mul_card]

@[simp] lemma dens_empty : dens (∅ : Finset α) = 0 := by
  apply mul_right_cancel₀ (dens_card_cast_ne_zero (α := α))
  simp only [dens_mul_card, card_empty, Nat.cast_zero, zero_mul]

@[simp] lemma dens_singleton (a : α) : dens ({a} : Finset α) = (Fintype.card α : ℚ≥0)⁻¹ := by
  simp only [dens_eq_card_div_card, card_singleton, Nat.cast_one, one_div₀]

@[simp] lemma dens_cons (h : a ∉ s) : (s.cons a h).dens = dens s + (Fintype.card α : ℚ≥0)⁻¹ := by
  have he : (s.cons a h).dens = dens s + dens ({a} : Finset α) := by
    apply mul_right_cancel₀ (dens_card_cast_ne_zero (α := α))
    simp only [add_mul, dens_mul_card, card_cons, card_singleton, Nat.cast_add, Nat.cast_one]
  simpa only [dens_singleton] using he

@[simp] lemma dens_disjUnion (s t : Finset α) (h) :
    dens (s.disjUnion t h) = dens s + dens t := by
  apply mul_right_cancel₀ (dens_card_cast_ne_zero (α := α))
  simp only [add_mul, dens_mul_card, card_disjUnion, Nat.cast_add]

@[simp] lemma dens_eq_zero : dens s = 0 ↔ s = ∅ := by
  calc
    dens s = 0 ↔ dens s * (Fintype.card α : ℚ≥0) = 0 :=
      (mul_eq_zero_iff_right (dens_card_cast_ne_zero (α := α))).symm
    _ ↔ s = ∅ := by rw [dens_mul_card, Nat.cast_eq_zero, card_eq_zero]

lemma dens_ne_zero : dens s ≠ 0 ↔ s.Nonempty :=
  dens_eq_zero.not.trans nonempty_iff_ne_empty.symm

@[simp] lemma dens_pos : 0 < dens s ↔ s.Nonempty := pos_iff_ne_zero.trans dens_ne_zero

protected alias ⟨_, Nonempty.dens_pos⟩ := dens_pos
protected alias ⟨_, Nonempty.dens_ne_zero⟩ := dens_ne_zero

/-! The evidence search `checked_nonzero` uses that a nonempty finset has nonzero density, so that
`s.dens⁻¹` finds its evidence from a hypothesis `s.Nonempty`. -/

macro_rules | `(tactic| checked_nonzero) => `(tactic|
    solve
    | assumption
    | ((with_reducible apply Finset.Nonempty.dens_ne_zero); assumption))

@[gcongr] lemma dens_le_dens (h : s ⊆ t) : dens s ≤ dens t := by
  apply (mul_le_mul_iff_of_pos_right (card_cast_pos (α := α))).mp
  rw [dens_mul_card, dens_mul_card]
  exact_mod_cast card_mono h

@[gcongr] lemma dens_lt_dens (h : s ⊂ t) : dens s < dens t := by
  apply (mul_lt_mul_iff_of_pos_right (card_cast_pos (α := α))).mp
  rw [dens_mul_card, dens_mul_card]
  exact_mod_cast card_lt_card h

@[mono] lemma dens_mono : Monotone (dens : Finset α → ℚ≥0) := fun _ _ ↦ dens_le_dens
@[mono] lemma dens_strictMono : StrictMono (dens : Finset α → ℚ≥0) := fun _ _ ↦ dens_lt_dens

lemma dens_map_le [Fintype β] [Nonempty β] (f : α ↪ β) : dens (s.map f) ≤ dens s := by
  apply (mul_le_mul_iff_of_pos_right (card_cast_pos (α := β))).mp
  rw [dens_mul_card, card_map]
  apply (mul_le_mul_iff_of_pos_right (card_cast_pos (α := α))).mp
  rw [mul_right_comm (dens s), dens_mul_card]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact_mod_cast Fintype.card_le_of_injective _ f.2

@[simp] lemma dens_map_equiv [Fintype β] [Nonempty β] (e : α ≃ β) :
    (s.map e.toEmbedding).dens = s.dens := by
  simp only [dens, card_map, Fintype.card_congr e]

lemma dens_image [Fintype β] [Nonempty β] [DecidableEq β] {f : α → β}
    (hf : Bijective f) (s : Finset α) : (s.image f).dens = s.dens := by
  simpa [map_eq_image, -dens_map_equiv] using dens_map_equiv (.ofBijective f hf)

section Semifield
variable [Semifield 𝕜] [CharZero 𝕜]

@[simp] lemma natCast_card_mul_nnratCast_dens (s : Finset α) :
    (Fintype.card α * s.dens : 𝕜) = s.card := by
  have h := congrArg (fun q : ℚ≥0 => (q : 𝕜)) (card_mul_dens s)
  simpa only [NNRat.cast_mul, NNRat.cast_natCast] using h

@[simp] lemma nnratCast_dens_mul_natCast_card (s : Finset α) :
    (s.dens * Fintype.card α : 𝕜) = s.card := by
  have h := congrArg (fun q : ℚ≥0 => (q : 𝕜)) (dens_mul_card s)
  simpa only [NNRat.cast_mul, NNRat.cast_natCast] using h

@[norm_cast] lemma nnratCast_dens (s : Finset α) :
    (s.dens : 𝕜) = (s.card : 𝕜) / (Fintype.card α : 𝕜) :=
  eq_div_iff.mpr (nnratCast_dens_mul_natCast_card s)

end Semifield

@[simp] lemma dens_univ : dens (univ : Finset α) = 1 := by
  apply mul_right_cancel₀ (dens_card_cast_ne_zero (α := α))
  simp only [dens_mul_card, card_univ, one_mul]

@[simp] lemma dens_eq_one : dens s = 1 ↔ s = univ := by
  constructor
  · intro h
    apply (card_eq_iff_eq_univ s).mp
    apply Nat.cast_injective (R := ℚ≥0)
    simpa only [h, one_mul] using (dens_mul_card s).symm
  · rintro rfl
    exact dens_univ

lemma dens_ne_one : dens s ≠ 1 ↔ s ≠ univ := dens_eq_one.not

@[simp] lemma dens_le_one : s.dens ≤ 1 := by
  simpa only [dens_univ] using dens_le_dens s.subset_univ

section Lattice
variable [DecidableEq α]

lemma dens_union_add_dens_inter (s t : Finset α) :
    dens (s ∪ t) + dens (s ∩ t) = dens s + dens t := by
  apply mul_right_cancel₀ (dens_card_cast_ne_zero (α := α))
  simp only [add_mul, dens_mul_card]
  simpa only [Nat.cast_add] using
    congrArg (fun n : ℕ => (n : ℚ≥0)) (card_union_add_card_inter s t)

lemma dens_inter_add_dens_union (s t : Finset α) :
    dens (s ∩ t) + dens (s ∪ t) = dens s + dens t := by rw [add_comm, dens_union_add_dens_inter]

@[simp] lemma dens_union_of_disjoint (h : Disjoint s t) : dens (s ∪ t) = dens s + dens t := by
  rw [← disjUnion_eq_union s t h, dens_disjUnion]

lemma dens_sdiff_add_dens_eq_dens (h : s ⊆ t) : dens (t \ s) + dens s = dens t := by
  apply mul_right_cancel₀ (dens_card_cast_ne_zero (α := α))
  simp only [add_mul, dens_mul_card]
  simpa only [Nat.cast_add] using
    congrArg (fun n : ℕ => (n : ℚ≥0)) (card_sdiff_add_card_eq_card h)

lemma dens_sdiff_add_dens (s t : Finset α) : dens (s \ t) + dens t = (s ∪ t).dens := by
  rw [← dens_union_of_disjoint sdiff_disjoint, sdiff_union_self_eq_union]

lemma dens_sdiff_comm (h : card s = card t) : dens (s \ t) = dens (t \ s) :=
  add_left_injective (dens t) <| by
    simp_rw [dens_sdiff_add_dens, union_comm s, ← dens_sdiff_add_dens, dens, h]

@[simp]
lemma dens_sdiff_add_dens_inter (s t : Finset α) : dens (s \ t) + dens (s ∩ t) = dens s := by
  rw [← dens_union_of_disjoint (disjoint_sdiff_inter _ _), sdiff_union_inter]

@[simp]
lemma dens_inter_add_dens_sdiff (s t : Finset α) : dens (s ∩ t) + dens (s \ t) = dens s := by
  rw [add_comm, dens_sdiff_add_dens_inter]

lemma dens_filter_add_dens_filter_not_eq_dens {α : Type*} [Fintype α] [Nonempty α] {s : Finset α}
    (p : α → Prop) [DecidablePred p] [∀ x, Decidable (¬p x)] :
    dens {a ∈ s | p a} + dens {a ∈ s | ¬ p a} = dens s := by
  classical
  rw [← dens_union_of_disjoint (disjoint_filter_filter_not ..), filter_union_filter_not_eq]

lemma dens_union_le (s t : Finset α) : dens (s ∪ t) ≤ dens s + dens t :=
  dens_union_add_dens_inter s t ▸ le_add_of_nonneg_right zero_le

lemma dens_le_dens_sdiff_add_dens : dens s ≤ dens (s \ t) + dens t :=
  dens_sdiff_add_dens s _ ▸ dens_le_dens subset_union_left

lemma dens_sdiff (h : s ⊆ t) : dens (t \ s) = dens t - dens s :=
  eq_tsub_of_add_eq (dens_sdiff_add_dens_eq_dens h)

lemma le_dens_sdiff (s t : Finset α) : dens t - dens s ≤ dens (t \ s) :=
  tsub_le_iff_right.2 dens_le_dens_sdiff_add_dens

end Lattice
end Finset
