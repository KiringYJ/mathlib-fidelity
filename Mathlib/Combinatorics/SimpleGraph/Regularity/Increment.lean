/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Regularity.Chunk
public import Mathlib.Combinatorics.SimpleGraph.Regularity.Energy

/-!
# Increment partition for Szemerédi Regularity Lemma

In the proof of Szemerédi Regularity Lemma, we need to partition each part of a starting partition
to increase the energy. This file defines the partition obtained by gluing the parts partitions
together (the *increment partition*) and shows that the energy globally increases.

This entire file is internal to the proof of Szemerédi Regularity Lemma.

## Main declarations

* `SzemerediRegularity.increment`: The increment partition.
* `SzemerediRegularity.card_increment`: The increment partition is much bigger than the original,
  but by a controlled amount.
* `SzemerediRegularity.energy_increment`: The increment partition has energy greater than the
  original by a known (small) fixed amount.

## Implementation notes

Edge densities exist only between nonempty finsets. The sums of squared edge densities over pairs
of parts are indexed by the finsets of pairs themselves, so that each pair carries the membership
from which the nonemptiness of its parts follows.

## TODO

Once ported to mathlib4, this file will be a great golfing ground for Heather's new tactic
`gcongr`.

## References

[Yaël Dillies, Bhavik Mehta, *Formalising Szemerédi’s Regularity Lemma in Lean*][srl_itp]
-/

@[expose] public section


open Finset Fintype SimpleGraph SzemerediRegularity

open scoped SzemerediRegularity.Positivity

variable {α : Type*} [Fintype α] [DecidableEq α] {P : Finpartition (univ : Finset α)}
  (hP : P.IsEquipartition) (G : SimpleGraph α) [DecidableRel G.Adj] (ε : ℝ)

local notation3 "m" => (card α / stepBound #P.parts : ℕ)

namespace SzemerediRegularity

/-- The **increment partition** in Szemerédi's Regularity Lemma.

If an equipartition is *not* uniform, then the increment partition is a (much bigger) equipartition
with a slightly higher energy. This is helpful since the energy is bounded by a constant (see
`Finpartition.energy_le_one`), so this process eventually terminates and yields a
not-too-big uniform equipartition. -/
noncomputable def increment : Finpartition (univ : Finset α) :=
  P.bind fun _ => chunk hP G ε

open Finpartition Finpartition.IsEquipartition

variable {hP G ε}

/-- The increment partition has a prescribed (very big) size in terms of the original partition. -/
theorem card_increment (hPα : #P.parts * 16 ^ #P.parts ≤ card α) (hPG : ¬P.IsUniform G ε) :
    #(increment hP G ε).parts = stepBound #P.parts := by
  have hPα' : stepBound #P.parts ≤ card α := by grw [← hPα, stepBound]; gcongr; simp
  have hPpos : 0 < stepBound #P.parts := stepBound_pos (nonempty_of_not_uniform hPG).card_pos
  rw [increment, card_bind]
  simp_rw [chunk, apply_dite Finpartition.parts, apply_dite card, sum_dite]
  rw [sum_const_nat, sum_const_nat, univ_eq_attach, univ_eq_attach, card_attach, card_attach]
  any_goals exact fun x hx => card_parts_equitabilise _ _ (Nat.div_pos hPα' hPpos).ne'
  rw [Nat.sub_add_cancel a_add_one_le_four_pow_parts_card,
    Nat.sub_add_cancel ((Nat.le_succ _).trans a_add_one_le_four_pow_parts_card), ← add_mul]
  congr
  rw [card_filter_add_card_filter_not, card_attach]

variable (hP G ε)

theorem increment_isEquipartition : (increment hP G ε).IsEquipartition := by
  simp_rw [IsEquipartition, Set.equitableOn_iff_exists_eq_eq_add_one]
  refine ⟨m, fun A hA => ?_⟩
  rw [mem_coe, increment, mem_bind] at hA
  obtain ⟨U, hU, hA⟩ := hA
  exact card_eq_of_mem_parts_chunk hA

set_option backward.privateInPublic true in
/-- The contribution to `Finpartition.energy` of a pair of distinct parts of a `Finpartition`. -/
private noncomputable def distinctPairs (x : {x // x ∈ P.parts.offDiag}) :
    Finset (Finset α × Finset α) :=
  (chunk hP G ε (mem_offDiag.1 x.2).1).parts ×ˢ (chunk hP G ε (mem_offDiag.1 x.2).2.1).parts

variable {hP G ε}

/-- The two finsets of a pair in `distinctPairs` are parts of chunks, hence nonempty. -/
private theorem nonempty_of_mem_distinctPairs {x : {x // x ∈ P.parts.offDiag}}
    {i : Finset α × Finset α} (hi : i ∈ distinctPairs hP G ε x) : i.1.Nonempty ∧ i.2.Nonempty := by
  rw [distinctPairs, mem_product] at hi
  exact ⟨Finpartition.nonempty_of_mem_parts _ hi.1, Finpartition.nonempty_of_mem_parts _ hi.2⟩

private theorem distinctPairs_increment :
    P.parts.offDiag.attach.biUnion (distinctPairs hP G ε) ⊆ (increment hP G ε).parts.offDiag := by
  rintro ⟨Ui, Vj⟩
  simp only [distinctPairs, increment, mem_offDiag, bind_parts, mem_biUnion, Prod.exists,
    mem_product, mem_attach, true_and, Subtype.exists, and_imp,
    mem_offDiag, forall_exists_index, Ne]
  refine fun U V hUV hUi hVj => ⟨⟨_, hUV.1, hUi⟩, ⟨_, hUV.2.1, hVj⟩, ?_⟩
  rintro rfl
  obtain ⟨i, hi⟩ := nonempty_of_mem_parts _ hUi
  exact hUV.2.2 (P.disjoint.elim_finset hUV.1 hUV.2.1 i (Finpartition.le _ hUi hi) <|
    Finpartition.le _ hVj hi)

private lemma pairwiseDisjoint_distinctPairs :
    (P.parts.offDiag.attach : Set {x // x ∈ P.parts.offDiag}).PairwiseDisjoint
      (distinctPairs hP G ε) := by
  simp +unfoldPartialApp only [distinctPairs, Set.PairwiseDisjoint,
    Function.onFun, Finset.disjoint_left, mem_product]
  rintro ⟨⟨s₁, s₂⟩, hs⟩ _ ⟨⟨t₁, t₂⟩, ht⟩ _ hst ⟨u, v⟩ huv₁ huv₂
  rw [mem_offDiag] at hs ht
  obtain ⟨a, ha⟩ := Finpartition.nonempty_of_mem_parts _ huv₁.1
  obtain ⟨b, hb⟩ := Finpartition.nonempty_of_mem_parts _ huv₁.2
  exact hst <| Subtype.ext <| Prod.ext
    (P.disjoint.elim_finset hs.1 ht.1 a (Finpartition.le _ huv₁.1 ha) <|
      Finpartition.le _ huv₂.1 ha) <|
        P.disjoint.elim_finset hs.2.1 ht.2.1 b (Finpartition.le _ huv₁.2 hb) <|
          Finpartition.le _ huv₂.2 hb

variable [Nonempty α]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
lemma le_sum_distinctPairs_edgeDensity_sq (x : {i // i ∈ P.parts.offDiag}) (hε₁ : ε ≤ 1)
    (hPα : #P.parts * 16 ^ #P.parts ≤ card α) (hPε : ↑100 ≤ ↑4 ^ #P.parts * ε ^ 5) :
    (G.edgeDensity x.1.1 x.1.2 (P.nonempty_of_mem_parts (mem_offDiag.1 x.2).1)
        (P.nonempty_of_mem_parts (mem_offDiag.1 x.2).2.1) : ℝ) ^ 2 +
      ((if G.IsUniform ε x.1.1 x.1.2 (P.nonempty_of_mem_parts (mem_offDiag.1 x.2).1)
          (P.nonempty_of_mem_parts (mem_offDiag.1 x.2).2.1) then 0 else ε ^ 4 / 3) - ε ^ 5 / 25) ≤
    (∑ i : ↥(distinctPairs hP G ε x), (G.edgeDensity i.1.1 i.1.2
      (Finpartition.nonempty_of_mem_parts _ (mem_product.1 i.2).1)
      (Finpartition.nonempty_of_mem_parts _ (mem_product.1 i.2).2) : ℝ) ^ 2) / 16 ^ #P.parts := by
  rw [← add_sub_assoc, add_sub_right_comm]
  split_ifs with h
  · rw [add_zero]
    exact edgeDensity_chunk_uniform hPα hPε _ _
  · exact edgeDensity_chunk_not_uniform hPα hPε hε₁ (mem_offDiag.1 x.2).2.2 h

/-- The increment partition has energy greater than the original one by a known fixed amount. -/
theorem energy_increment (hP : P.IsEquipartition) (hP₇ : 7 ≤ #P.parts)
    (hPε : 100 ≤ 4 ^ #P.parts * ε ^ 5) (hPα : #P.parts * 16 ^ #P.parts ≤ card α)
    (hPG : ¬P.IsUniform G ε) (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1) :
    ↑(P.energy G) + ε ^ 5 / 4 ≤ (increment hP G ε).energy G := by
  have hPne : P.parts.Nonempty := P.parts_nonempty univ_nonempty.ne_empty
  have hIne : (increment hP G ε).parts.Nonempty :=
    (increment hP G ε).parts_nonempty univ_nonempty.ne_empty
  have hcard := card_increment (hP := hP) hPα hPG
  have hk : (0 : ℝ) < #P.parts := by positivity
  have hk2 : IsUnit ((#P.parts : ℝ) ^ 2) := (pow_pos hk 2).ne'.isUnit
  have hm2 : IsUnit (((#P.parts : ℝ) * 4 ^ #P.parts) ^ 2) :=
    (pow_pos (mul_pos hk (by positivity)) 2).ne'.isUnit
  -- The pairs of parts of the chunks of distinct parts of `P` are distinct parts of the increment.
  have hinj : ∑ x : P.parts.offDiag, ∑ i : ↥(distinctPairs hP G ε x), (G.edgeDensity i.1.1 i.1.2
      (nonempty_of_mem_distinctPairs i.2).1 (nonempty_of_mem_distinctPairs i.2).2 : ℝ) ^ 2 ≤
      ∑ y : (increment hP G ε).parts.offDiag, (G.edgeDensity y.1.1 y.1.2
        ((increment hP G ε).nonempty_of_mem_parts (mem_offDiag.1 y.2).1)
        ((increment hP G ε).nonempty_of_mem_parts (mem_offDiag.1 y.2).2.1) : ℝ) ^ 2 := by
    rw [← Fintype.sum_sigma' fun (x : P.parts.offDiag) (i : ↥(distinctPairs hP G ε x)) ↦
      (G.edgeDensity i.1.1 i.1.2 (nonempty_of_mem_distinctPairs i.2).1
        (nonempty_of_mem_distinctPairs i.2).2 : ℝ) ^ 2]
    refine sum_le_sum_of_injOn
      (fun xi ↦ ⟨xi.2.1, distinctPairs_increment (mem_biUnion.2 ⟨xi.1, mem_attach _ _, xi.2.2⟩)⟩)
      ?_ (subset_univ _) (fun _ _ ↦ le_rfl) fun _ _ _ ↦ sq_nonneg _
    rintro ⟨x, i⟩ - ⟨x', i'⟩ - h
    have hii' : i.1 = i'.1 := congrArg Subtype.val h
    obtain rfl : x = x' := by
      by_contra hxx'
      have := pairwiseDisjoint_distinctPairs (G := G) (ε := ε) (hP := hP) (mem_attach _ x)
        (mem_attach _ x') hxx'
      exact Finset.disjoint_left.1 this i.2 (hii' ▸ i'.2)
    obtain rfl : i = i' := Subtype.ext hii'
    rfl
  -- The non-uniform pairs of parts of `P`, counted among the pairs of distinct parts.
  have hnon : #(univ.filter fun x : P.parts.offDiag ↦ ¬G.IsUniform ε x.1.1 x.1.2
      (P.nonempty_of_mem_parts (mem_offDiag.1 x.2).1)
      (P.nonempty_of_mem_parts (mem_offDiag.1 x.2).2.1)) = #(P.nonUniforms G ε) := by
    refine card_bij (fun x _ ↦ x.1) (fun x hx ↦ ?_) (fun _ _ _ _ ↦ Subtype.ext) fun y hy ↦ ?_
    · obtain ⟨hu, hv, huv⟩ := mem_offDiag.1 x.2
      exact (mk_mem_nonUniforms _ _).2 ⟨hu, hv, huv, (mem_filter.1 hx).2⟩
    · obtain ⟨u, v⟩ := y
      obtain ⟨hu, hv, huv, h⟩ := (mk_mem_nonUniforms _ _).1 hy
      exact ⟨⟨(u, v), mem_offDiag.2 ⟨hu, hv, huv⟩⟩, mem_filter.2 ⟨mem_univ _, h⟩, rfl⟩
  rw [Finpartition.IsUniform, not_le, mul_tsub, mul_one, ← offDiag_card] at hPG
  -- Each pair of distinct parts of `P` gains energy, and the non-uniform pairs gain more.
  have hsum : ∑ x : P.parts.offDiag, (G.edgeDensity x.1.1 x.1.2
        (P.nonempty_of_mem_parts (mem_offDiag.1 x.2).1)
        (P.nonempty_of_mem_parts (mem_offDiag.1 x.2).2.1) : ℝ) ^ 2 + #P.parts ^ 2 * (ε ^ 5 / 4) ≤
      ∑ x : P.parts.offDiag, (∑ i : ↥(distinctPairs hP G ε x), (G.edgeDensity i.1.1 i.1.2
        (nonempty_of_mem_distinctPairs i.2).1 (nonempty_of_mem_distinctPairs i.2).2 : ℝ) ^ 2) /
          16 ^ #P.parts := by
    calc
      _ ≤ ∑ x : P.parts.offDiag, (G.edgeDensity x.1.1 x.1.2
            (P.nonempty_of_mem_parts (mem_offDiag.1 x.2).1)
            (P.nonempty_of_mem_parts (mem_offDiag.1 x.2).2.1) : ℝ) ^ 2 +
          (#(P.nonUniforms G ε) * (ε ^ 4 / 3) - #P.parts.offDiag * (ε ^ 5 / 25)) := by
        gcongr
        calc
          _ = (6 / 7 * #P.parts ^ 2) * ε ^ 5 * (7 / 24) := by ring
          _ ≤ #P.parts.offDiag * ε ^ 5 * (22 / 75) := by
              gcongr ?_ * _ * ?_
              · rw [← mul_div_right_comm₀, div_le_iff₀ (by simp), offDiag_card]
                norm_cast
                rw [tsub_mul]
                refine le_tsub_of_add_le_left ?_
                nlinarith
              · norm_num
          _ = (#P.parts.offDiag * ε * (ε ^ 4 / 3) - #P.parts.offDiag * (ε ^ 5 / 25)) := by ring
          _ ≤ (#(P.nonUniforms G ε) * (ε ^ 4 / 3) - #P.parts.offDiag * (ε ^ 5 / 25)) := by
              gcongr
      _ = ∑ x : P.parts.offDiag, ((G.edgeDensity x.1.1 x.1.2
            (P.nonempty_of_mem_parts (mem_offDiag.1 x.2).1)
            (P.nonempty_of_mem_parts (mem_offDiag.1 x.2).2.1) : ℝ) ^ 2 +
          ((if G.IsUniform ε x.1.1 x.1.2 (P.nonempty_of_mem_parts (mem_offDiag.1 x.2).1)
            (P.nonempty_of_mem_parts (mem_offDiag.1 x.2).2.1) then (0 : ℝ) else ε ^ 4 / 3) -
              ε ^ 5 / 25)) := by
        rw [sum_add_distrib, sum_sub_distrib, sum_const, nsmul_eq_mul, sum_ite, sum_const_zero,
          zero_add, sum_const, nsmul_eq_mul, hnon, card_univ, Fintype.card_coe]
      _ ≤ _ := sum_le_sum fun i _ ↦ le_sum_distinctPairs_edgeDensity_sq i hε₁ hPα hPε
  rw [P.coe_energy G hPne, (increment hP G ε).coe_energy G hIne]
  calc
    _ = (∑ x : P.parts.offDiag, (G.edgeDensity x.1.1 x.1.2
          (P.nonempty_of_mem_parts (mem_offDiag.1 x.2).1)
          (P.nonempty_of_mem_parts (mem_offDiag.1 x.2).2.1) : ℝ) ^ 2 +
            #P.parts ^ 2 * (ε ^ 5 / 4)) / #P.parts ^ 2 := by
      rw [add_div, mul_div_cancel_left₀]
    _ ≤ (∑ x : P.parts.offDiag, (∑ i : ↥(distinctPairs hP G ε x), (G.edgeDensity i.1.1 i.1.2
          (nonempty_of_mem_distinctPairs i.2).1 (nonempty_of_mem_distinctPairs i.2).2 : ℝ) ^ 2) /
            16 ^ #P.parts) / #P.parts ^ 2 := by gcongr
    _ = (∑ x : P.parts.offDiag, ∑ i : ↥(distinctPairs hP G ε x), (G.edgeDensity i.1.1 i.1.2
          (nonempty_of_mem_distinctPairs i.2).1 (nonempty_of_mem_distinctPairs i.2).2 : ℝ) ^ 2) /
            (#P.parts * 4 ^ #P.parts) ^ 2 := by
      have h4 : ((#P.parts : ℝ) * 4 ^ #P.parts) ^ 2 = #P.parts ^ 2 * 16 ^ #P.parts := by
        rw [mul_pow, ← pow_mul, show (16 : ℝ) = 4 ^ 2 by norm_num, ← pow_mul]
        ring
      simp only [h4, div_eq_mul_inv₀, sum_mul, mul_inv_rev₀, mul_assoc]
    _ ≤ (∑ y : (increment hP G ε).parts.offDiag, (G.edgeDensity y.1.1 y.1.2
          ((increment hP G ε).nonempty_of_mem_parts (mem_offDiag.1 y.2).1)
          ((increment hP G ε).nonempty_of_mem_parts (mem_offDiag.1 y.2).2.1) : ℝ) ^ 2) /
            (#P.parts * 4 ^ #P.parts) ^ 2 := by gcongr
    _ = _ := by simp only [hcard, coe_stepBound]

end SzemerediRegularity
