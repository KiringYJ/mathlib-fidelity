/-
Copyright (c) 2024 Ching-Tsun Chou, Chris Wong, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou, Chris Wong, Yaël Dillies
-/
module

public import Mathlib.Data.Finset.Density
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Nat.Choose.Basic

/-!
# The Katona circle method

This file provides tooling to use the Katona circle method, which is double-counting ways to order
`n` elements on a circle under some condition.
-/

@[expose] public section

open Fintype Finset Nat

variable {X : Type*} [Fintype X]

variable (X) in
/-- A numbering of a fintype `X` is a bijection between `X` and `Fin (card X)`. -/
abbrev Numbering : Type _ := X ≃ Fin (card X)

instance : Nonempty (Numbering X) := ⟨equivFin X⟩

@[simp] lemma Fintype.card_numbering [DecidableEq X] : card (Numbering X) = (card X)! :=
  card_equiv (equivFin _)

namespace Numbering
variable {f : Numbering X} {s t : Finset X}

/-- `IsPrefix f s` means that the elements of `s` precede the elements of `sᶜ`
in the numbering `f`. -/
def IsPrefix (f : Numbering X) (s : Finset X) := ∀ x, x ∈ s ↔ f x < #s

lemma IsPrefix.subset_of_card_le_card (hs : IsPrefix f s) (ht : IsPrefix f t) (hst : #s ≤ #t) :
    s ⊆ t := fun a ha ↦ (ht a).mpr <| ((hs a).mp ha).trans_le hst

variable [DecidableEq X]

instance : Decidable (IsPrefix f s) := inferInstanceAs <| Decidable (∀ _, _)

/-- The set of numberings of which `s` is a prefix. -/
def prefixed (s : Finset X) : Finset (Numbering X) := {f | IsPrefix f s}

@[simp] lemma mem_prefixed : f ∈ prefixed s ↔ IsPrefix f s := by simp [prefixed]

/-- Decompose a numbering of which `s` is a prefix into a numbering of `s` and a numbering on `sᶜ`.
-/
def prefixedEquiv (s : Finset X) : prefixed s ≃ Numbering s × Numbering ↑(sᶜ) where
  toFun f :=
    { fst.toFun x := ⟨f.1 x, by simp [← mem_prefixed.1 f.2 x]⟩
      fst.invFun n :=
        ⟨f.1.symm ⟨n, n.2.trans_le <| by simpa using s.card_le_univ⟩, by
          rw [mem_prefixed.1 f.2]; simpa using n.2⟩
      fst.left_inv x := by simp
      fst.right_inv n := by simp
      snd.toFun x := ⟨f.1 x - #s, by
        have := (mem_prefixed.1 f.2 x).not.1 (Finset.mem_compl.1 x.2)
        simp at this ⊢
        omega⟩
      snd.invFun n :=
        ⟨f.1.symm ⟨n + #s, Nat.add_lt_of_lt_sub <| by simpa using n.2⟩, by
          rw [s.mem_compl, mem_prefixed.1 f.2]; simp⟩
      snd.left_inv := by
        rintro ⟨x, hx⟩
        rw [s.mem_compl, mem_prefixed.1 f.2, not_lt] at hx
        simp [Nat.sub_add_cancel hx]
      snd.right_inv := by rintro ⟨n, hn⟩; simp }
  invFun := fun (g, g') ↦
    { val.toFun x :=
        if hx : x ∈ s then
          g ⟨x, hx⟩ |>.castLE (Fintype.card_subtype_le _)
        else
          g' ⟨x, by simpa⟩ |>.addNat #s |>.cast (by simp [card_le_univ])
      val.invFun n :=
        if hn : n < #s then
          g.symm ⟨n, by simpa using hn⟩
        else
          g'.symm ⟨n - #s, by simp; omega⟩
      val.left_inv x := by
        by_cases hx : x ∈ s
        · have : g ⟨x, hx⟩ < #s := by simpa using (g ⟨x, hx⟩).2
          simp [hx, this]
        · simp [hx]
      val.right_inv n := by
        obtain hns | hsn := lt_or_ge n.1 #s
        · simp [hns]
        · simp [hsn.not_gt, hsn, mem_compl.1 <| Subtype.prop _]
      property := mem_prefixed.2 fun x ↦ by
        constructor
        · intro hx
          simpa [hx, -Fin.is_lt] using (g _).is_lt
        · by_cases hx : x ∈ s <;> simp [hx] }
  left_inv f := by
    ext x
    by_cases hx : x ∈ s
    · simp [hx]
    · rw [mem_prefixed.1 f.2, not_lt] at hx
      simp [hx]
  right_inv g := by simp +contextual [Prod.ext_iff, DFunLike.ext_iff]

lemma card_prefixed (s : Finset X) : #(prefixed s) = (#s)! * (card X - #s)! := by
  simpa [-mem_prefixed] using Fintype.card_congr (prefixedEquiv s)

@[simp]
lemma dens_prefixed (s : Finset X) : (prefixed s).dens =
    (((Units.mk0 ((card X).choose #s : ℚ≥0)
      (Nat.cast_ne_zero.mpr (Nat.choose_pos s.card_le_univ).ne'))⁻¹ : ℚ≥0ˣ) : ℚ≥0) := by
  have hc : ((card X).choose #s : ℚ≥0) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos s.card_le_univ).ne'
  apply mul_left_cancel₀ hc
  have hi := (Units.mk0 ((card X).choose #s : ℚ≥0) hc).mul_inv
  change ((card X).choose #s : ℚ≥0) * (prefixed s).dens =
    ((card X).choose #s : ℚ≥0) * (((Units.mk0 _ hc)⁻¹ : ℚ≥0ˣ) : ℚ≥0)
  simp only [Units.val_mk0] at hi
  rw [hi]
  apply mul_right_cancel₀ (dens_card_cast_ne_zero (α := Numbering X))
  rw [mul_assoc, dens_mul_card, one_mul, card_prefixed, card_numbering]
  exact_mod_cast (by simpa only [Nat.mul_assoc] using
    Nat.choose_mul_factorial_mul_factorial s.card_le_univ :
    (card X).choose #s * ((#s)! * (card X - #s)!) = (card X)!)

-- TODO: This can be strengthened to an iff
lemma disjoint_prefixed_prefixed (hst : ¬ s ⊆ t) (hts : ¬ t ⊆ s) :
    Disjoint (prefixed s) (prefixed t) := by
  simp only [Finset.disjoint_left, mem_prefixed]
  intro f hs ht
  obtain hst' | hts' := Nat.le_total #s #t
  · exact hst <| hs.subset_of_card_le_card ht hst'
  · exact hts <| ht.subset_of_card_le_card hs hts'

end Numbering
