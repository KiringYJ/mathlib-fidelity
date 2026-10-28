/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.SimpleGraph.Density
public import Mathlib.Data.Rat.BigOperators
public import Mathlib.Data.Rat.Cast.Lemmas

/-!
# Energy of a partition

This file defines the energy of a partition.

The energy is the auxiliary quantity that drives the induction process in the proof of Szemerédi's
Regularity Lemma. As long as we do not have a suitable equipartition, we will find a new one that
has an energy greater than the previous one plus some fixed constant.

The energy divides by the square of the number of parts, so it exists only for a partition with a
part. It sums over the pairs of distinct parts, indexed by the finset of such pairs itself, and the
parts are nonempty, so the edge density between the two parts of a pair exists.

## References

[Yaël Dillies, Bhavik Mehta, *Formalising Szemerédi’s Regularity Lemma in Lean*][srl_itp]
-/

@[expose] public section


open Finset

variable {α : Type*} [DecidableEq α] {s : Finset α} (P : Finpartition s) (G : SimpleGraph α)
  [DecidableRel G.Adj]

namespace Finpartition

/-- The energy of a partition, also known as index. Auxiliary quantity for Szemerédi's regularity
lemma. It is the sum of the squared edge densities between distinct parts, divided by the square
of the number of parts, so it takes a proof that `P` has a part. -/
noncomputable def energy
    (hP : P.parts.Nonempty := by
      first
      | assumption
      | exact Finpartition.parts_nonempty _ Finset.univ_nonempty.ne_empty
      | fail "the energy needs a partition with a part") : ℚ :=
  (∑ uv : P.parts.offDiag, G.edgeDensity uv.1.1 uv.1.2
      (P.nonempty_of_mem_parts (mem_offDiag.1 uv.2).1)
      (P.nonempty_of_mem_parts (mem_offDiag.1 uv.2).2.1) ^ 2) / (#P.parts : ℚ) ^ 2

theorem energy_nonneg (hP : P.parts.Nonempty) : 0 ≤ P.energy G hP := by
  exact div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) <| sq_nonneg _

theorem energy_le_one (hP : P.parts.Nonempty) : P.energy G hP ≤ 1 := by
  rw [energy, div_le_one (by positivity)]
  calc
    _ ≤ #(univ : Finset P.parts.offDiag) • (1 : ℚ) :=
      sum_le_card_nsmul _ _ 1 fun _ _ =>
        (sq_le_one_iff₀ <| G.edgeDensity_nonneg _ _ _ _).2 <| G.edgeDensity_le_one _ _ _ _
    _ = #P.parts.offDiag := by rw [Nat.smul_one_eq_cast, card_univ, Fintype.card_coe]
    _ ≤ _ := by
      rw [offDiag_card]
      norm_cast
      rw [sq]
      exact tsub_le_self

@[simp, norm_cast]
theorem coe_energy {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (hP : P.parts.Nonempty) :
    (P.energy G hP : 𝕜) =
      (∑ uv : P.parts.offDiag, (G.edgeDensity uv.1.1 uv.1.2
        (P.nonempty_of_mem_parts (mem_offDiag.1 uv.2).1)
        (P.nonempty_of_mem_parts (mem_offDiag.1 uv.2).2.1) : 𝕜) ^ 2) / (#P.parts : 𝕜) ^ 2 := by
  rw [energy]; push_cast; rfl

end Finpartition
