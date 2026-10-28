/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Mario Carneiro
-/
module

public import Mathlib.RingTheory.Ideal.Maximal
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas

/-!
# The set of non-invertible elements of a monoid

## Main definitions

* `nonunits` is the set of non-invertible elements of a monoid.

## Main results

* `exists_max_ideal_of_mem_nonunits`: every element of `nonunits` is contained in a maximal ideal
-/

@[expose] public section


variable {F α β : Type*} {a b : α}

/-- The set of non-invertible elements of a monoid. -/
def nonunits (α : Type*) [Monoid α] : Set α :=
  { a | ¬IsUnit a }

@[simp]
theorem mem_nonunits_iff [Monoid α] : a ∈ nonunits α ↔ ¬IsUnit a :=
  Iff.rfl

theorem mul_mem_nonunits_right [CommMonoid α] : b ∈ nonunits α → a * b ∈ nonunits α :=
  mt isUnit_of_mul_isUnit_right

theorem mul_mem_nonunits_left [CommMonoid α] : a ∈ nonunits α → a * b ∈ nonunits α :=
  mt isUnit_of_mul_isUnit_left

theorem zero_mem_nonunits [MonoidWithZero α] : 0 ∈ nonunits α ↔ (0 : α) ≠ 1 :=
  not_congr isUnit_zero_iff

@[simp high] -- High priority shortcut lemma
theorem one_notMem_nonunits [Monoid α] : (1 : α) ∉ nonunits α :=
  not_not_intro isUnit_one

@[simp high] -- High priority shortcut lemma
theorem map_mem_nonunits_iff [Monoid α] [Monoid β] [FunLike F α β] [MonoidHomClass F α β] (f : F)
    [IsLocalHom f] (a) : f a ∈ nonunits β ↔ a ∈ nonunits α :=
  ⟨fun h ha => h <| ha.map f, fun h ha => h <| ha.of_map⟩

theorem coe_subset_nonunits [Semiring α] {I : Ideal α} (h : I ≠ ⊤) : (I : Set α) ⊆ nonunits α :=
  fun _x hx hu => h <| I.eq_top_of_isUnit_mem hx hu

theorem exists_max_ideal_of_mem_nonunits [CommSemiring α] (h : a ∈ nonunits α) :
    ∃ I : Ideal α, I.IsMaximal ∧ a ∈ I := by
  have : Ideal.span ({a} : Set α) ≠ ⊤ := by
    intro H
    rw [Ideal.span_singleton_eq_top] at H
    contradiction
  rcases Ideal.exists_le_maximal _ this with ⟨I, Imax, H⟩
  use I, Imax
  apply H
  apply Ideal.subset_span
  exact Set.mem_singleton a

namespace Submonoid

variable {C : Type*} [SetLike C α]

theorem inv_mem_of_isUnit [DivisionMonoid α] [SubmonoidClass C α] {S : C} {a : S} (ha : IsUnit a) :
    (a : α)⁻¹ ∈ S := by
  obtain ⟨u, rfl⟩ := ha
  convert! u⁻¹.1.2
  exact (map_inv ((subtype <| ofClass S).comp <| Units.coeHom S) u).symm

section Group

variable [Group α] [SubmonoidClass C α] {S : C} {a : S}

theorem isUnit_iff : IsUnit a ↔ (a : α)⁻¹ ∈ S where
  mp := inv_mem_of_isUnit
  mpr h := ⟨⟨a, ⟨_, h⟩, Subtype.ext (mul_inv_cancel _), Subtype.ext (inv_mul_cancel _)⟩, rfl⟩

protected theorem mem_nonunits_iff : a ∈ nonunits S ↔ (a : α)⁻¹ ∉ S := by
  rw [mem_nonunits_iff, isUnit_iff]

end Group

section Monoid

variable [Monoid α] [SubmonoidClass C α] {S : C} {a : S}

theorem checked_inv_mem_of_isUnit (ha : IsUnit a) :
    Checked.inv (a : α) (show IsUnit (a : α) from ha.map (subtype <| ofClass S)) ∈ S := by
  convert (Checked.inv a ha).property using 1
  exact inv_eq_of_mul_eq_one_right₀ (map_mul_eq_one (subtype <| ofClass S) mul_inv_cancel₀)

theorem isUnit_iff_exists_inv_mem :
    IsUnit a ↔ ∃ ha : IsUnit (a : α), Checked.inv (a : α) ha ∈ S where
  mp h := ⟨h.map (subtype <| ofClass S), checked_inv_mem_of_isUnit h⟩
  mpr h := by
    obtain ⟨ha, hm⟩ := h
    exact ⟨⟨a, ⟨_, hm⟩, Subtype.ext (mul_inv_cancel₀ (ha := ha)),
      Subtype.ext (inv_mul_cancel₀ (ha := ha))⟩, rfl⟩

theorem isUnit_iff_of_isUnit (ha : IsUnit (a : α)) :
    IsUnit a ↔ Checked.inv (a : α) ha ∈ S := by
  rw [isUnit_iff_exists_inv_mem]
  exact ⟨fun ⟨_, hm⟩ => hm, fun hm => ⟨ha, hm⟩⟩

end Monoid

section GroupWithZero

variable [GroupWithZero α] [SubmonoidClass C α] {S : C} {a : S}

theorem isUnit_iff_of_ne_zero (ha : (a : α) ≠ 0) :
    IsUnit a ↔ Checked.inv (a : α) (GroupWithZero.isUnit_of_ne_zero ha) ∈ S :=
  isUnit_iff_of_isUnit (GroupWithZero.isUnit_of_ne_zero ha)

theorem mem_nonunits_iff_eq_zero_or_exists_inv_not_mem :
    a ∈ nonunits S ↔ (a : α) = 0 ∨
      ∃ ha : IsUnit (a : α), Checked.inv (a : α) ha ∉ S := by
  rw [mem_nonunits_iff, isUnit_iff_exists_inv_mem]
  constructor
  · intro h
    by_cases ha : (a : α) = 0
    · exact Or.inl ha
    · exact Or.inr ⟨GroupWithZero.isUnit_of_ne_zero ha, fun hm => h ⟨_, hm⟩⟩
  · rintro (ha | ⟨ha, hnot⟩) ⟨hu, hm⟩
    · exact hu.ne_zero ha
    · exact hnot hm

theorem mem_nonunits_iff_of_ne_zero (ha : (a : α) ≠ 0) :
    a ∈ nonunits S ↔ Checked.inv (a : α) (GroupWithZero.isUnit_of_ne_zero ha) ∉ S := by
  rw [mem_nonunits_iff, isUnit_iff_of_ne_zero ha]

end GroupWithZero

end Submonoid
