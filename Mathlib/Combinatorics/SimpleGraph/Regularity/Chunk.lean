/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Regularity.Bound
public import Mathlib.Combinatorics.SimpleGraph.Regularity.Equitabilise
public import Mathlib.Combinatorics.SimpleGraph.Regularity.Uniform

/-!
# Chunk of the increment partition for Szemerédi Regularity Lemma

In the proof of Szemerédi Regularity Lemma, we need to partition each part of a starting partition
to increase the energy. This file defines those partitions of parts and shows that they locally
increase the energy.

This entire file is internal to the proof of Szemerédi Regularity Lemma.

## Main declarations

* `SzemerediRegularity.chunk`: The partition of a part of the starting partition.
* `SzemerediRegularity.edgeDensity_chunk_uniform`: `chunk` does not locally decrease the edge
  density between uniform parts too much.
* `SzemerediRegularity.edgeDensity_chunk_not_uniform`: `chunk` locally increases the edge density
  between non-uniform parts.

## Implementation notes

Edge densities exist only between nonempty finsets. Sums of edge densities over the pairs of a
finset of pairs of parts are indexed by that finset itself, so that each pair carries the
membership from which the nonemptiness of its parts follows.

## TODO

Once ported to mathlib4, this file will be a great golfing ground for Heather's new tactic
`gcongr`.

## References

[Yaël Dillies, Bhavik Mehta, *Formalising Szemerédi’s Regularity Lemma in Lean*][srl_itp]
-/

@[expose] public section


open Finpartition Finset Fintype Rel Nat
open scoped SzemerediRegularity.Positivity

namespace SzemerediRegularity

variable {α : Type*} [Fintype α] [DecidableEq α] {P : Finpartition (univ : Finset α)}
  (hP : P.IsEquipartition) (G : SimpleGraph α) [DecidableRel G.Adj] (ε : ℝ) {U : Finset α}
  (hU : U ∈ P.parts) (V : Finset α)

local notation3 (prettyPrint := false) "m" => chunkSize P

/-!
### Definitions

We define `chunk`, the partition of a part, and `star`, the sets of parts of `chunk` that are
contained in the corresponding witness of non-uniformity.
-/


/-- The portion of `SzemerediRegularity.increment` which partitions `U`. -/
noncomputable def chunk : Finpartition U :=
  if hUcard : #U = m * 4 ^ #P.parts +
      (Nat.euclideanDiv (card α) #P.parts (card_ne_zero_of_mem hU) - m * 4 ^ #P.parts) then
    (atomise U <| P.nonuniformWitnesses G ε U (P.nonempty_of_mem_parts hU)).equitabilise <|
      card_aux₁ ⟨U, hU⟩ hUcard
  else (atomise U <| P.nonuniformWitnesses G ε U (P.nonempty_of_mem_parts hU)).equitabilise <|
    card_aux₂ hP hU hUcard

-- `hP` and `hU` are used to get that `U` has size
-- `m * 4 ^ #P.parts + a or m * 4 ^ #P.parts + a + 1`
/-- The portion of `SzemerediRegularity.chunk` which is contained in the witness of non-uniformity
of `U` and `V`. The witness is defined for a nonempty `V`. -/
noncomputable def star (V : Finset α)
    (hV : V.Nonempty := by first | assumption | fail "uniformity needs a nonempty right set") :
    Finset (Finset α) :=
  {A ∈ (chunk hP G ε hU).parts | A ⊆ G.nonuniformWitness ε U V (P.nonempty_of_mem_parts hU) hV}

/-!
### Density estimates

We estimate the density between parts of `chunk`.
-/

variable {hU₀ : U.Nonempty} {hV₀ : V.Nonempty}

theorem biUnion_star_subset_nonuniformWitness :
    (star hP G ε hU V).biUnion id ⊆ G.nonuniformWitness ε U V (P.nonempty_of_mem_parts hU) :=
  biUnion_subset_iff_forall_subset.2 fun _ hA => (mem_filter.1 hA).2

variable {hP G ε hU V} {𝒜 : Finset (Finset α)} {s : Finset α}

theorem star_subset_chunk : star hP G ε hU V ⊆ (chunk hP G ε hU).parts :=
  filter_subset _ _

private theorem card_nonuniformWitness_sdiff_biUnion_star (hV : V ∈ P.parts) (hUV : U ≠ V)
    (h₂ : ¬G.IsUniform ε U V) :
    #(G.nonuniformWitness ε U V \ (star hP G ε hU V).biUnion id) ≤ 2 ^ (#P.parts - 1) * m := by
  have hX : G.nonuniformWitness ε U V ∈ P.nonuniformWitnesses G ε U :=
    nonuniformWitness_mem_nonuniformWitnesses h₂ hV hUV
  have q : G.nonuniformWitness ε U V \ (star hP G ε hU V).biUnion id ⊆
      {B ∈ (atomise U <| P.nonuniformWitnesses G ε U).parts |
        B ⊆ G.nonuniformWitness ε U V ∧ B.Nonempty}.biUnion
        fun B => B \ {A ∈ (chunk hP G ε hU).parts | A ⊆ B}.biUnion id := by
    intro x hx
    rw [← biUnion_filter_atomise hX (G.nonuniformWitness_subset h₂), star, mem_sdiff,
      mem_biUnion] at hx
    simp only [not_exists, mem_biUnion, and_imp, mem_filter,
      not_and, mem_sdiff, id, mem_sdiff] at hx ⊢
    obtain ⟨⟨B, hB₁, hB₂⟩, hx⟩ := hx
    exact ⟨B, hB₁, hB₂, fun A hA AB => hx A hA <| AB.trans hB₁.2.1⟩
  apply (card_le_card q).trans (card_biUnion_le.trans _)
  trans ∑ B ∈ (atomise U <| P.nonuniformWitnesses G ε U).parts with
    B ⊆ G.nonuniformWitness ε U V ∧ B.Nonempty, m
  · suffices ∀ B ∈ (atomise U <| P.nonuniformWitnesses G ε U).parts,
        #(B \ {A ∈ (chunk hP G ε hU).parts | A ⊆ B}.biUnion id) ≤ m by
      gcongr with B hB
      exact this B <| filter_subset _ _ hB
    intro B hB
    unfold chunk
    split_ifs with h₁
    · convert! card_parts_equitabilise_subset_le _ (card_aux₁ ⟨U, hU⟩ h₁) hB
    · convert! card_parts_equitabilise_subset_le _ (card_aux₂ hP hU h₁) hB
  grw [sum_const, smul_eq_mul, card_filter_atomise_le_two_pow (s := U) hX,
    Finpartition.card_nonuniformWitnesses_le, filter_subset, card_attach]

private theorem one_sub_eps_mul_card_nonuniformWitness_le_card_star (hV : V ∈ P.parts)
    (hUV : U ≠ V) (hunif : ¬G.IsUniform ε U V) (hPε : ↑100 ≤ ↑4 ^ #P.parts * ε ^ 5)
    (hε₁ : ε ≤ 1) :
    (1 - ε / 10) * #(G.nonuniformWitness ε U V) ≤ #((star hP G ε hU V).biUnion id) := by
  have hP₁ : 0 < #P.parts := Finset.card_pos.2 ⟨_, hU⟩
  have hε₀ : 0 < ε := eps_pos hPε
  have : (↑2 ^ #P.parts : ℝ) * m / (#U : ℝ) / ε ≤ ε / 10 := by
    rw [div_le_iff₀' hε₀]
    refine le_of_mul_le_mul_left ?_ (pow_pos zero_lt_two #P.parts)
    calc
      ↑2 ^ #P.parts * ((↑2 ^ #P.parts * m : ℝ) / (#U : ℝ)) =
          ((2 : ℝ) * 2) ^ #P.parts * m / (#U : ℝ) := by
        rw [mul_pow, ← mul_div_assoc₀, mul_assoc]
      _ = (4 : ℝ) ^ #P.parts * m / (#U : ℝ) := by norm_num
      _ ≤ 1 := div_le_one_of_le₀ (pow_mul_m_le_card_part hP hU) (cast_nonneg _)
      _ ≤ ↑2 ^ #P.parts * ε ^ 2 / 10 := by
        refine (one_le_sq_iff₀ <| by positivity).1 ?_
        rw [div_pow₀, mul_pow, pow_right_comm, ← pow_mul ε, one_le_div (by positivity)]
        calc
          (↑10 ^ 2) = 100 := by norm_num
          _ ≤ ↑4 ^ #P.parts * ε ^ 5 := hPε
          _ ≤ ↑4 ^ #P.parts * ε ^ 4 := by
            gcongr _ * ?_
            exact pow_le_pow_of_le_one (by sz_positivity) hε₁ (by decide)
          _ = (↑2 ^ 2) ^ #P.parts * ε ^ (2 * 2) := by norm_num
      _ = ↑2 ^ #P.parts * (ε * (ε / 10)) := by rw [mul_div_assoc₀, sq, mul_div_assoc₀]
  rw [div_div₀] at this
  calc
    (↑1 - ε / 10) * #(G.nonuniformWitness ε U V) ≤
        (↑1 - (2 : ℝ) ^ #P.parts * m / (#U * ε)) * #(G.nonuniformWitness ε U V) := by gcongr
    _ = #(G.nonuniformWitness ε U V) -
        (2 : ℝ) ^ #P.parts * m / (#U * ε) * #(G.nonuniformWitness ε U V) := by
      rw [sub_mul, one_mul]
    _ ≤ #(G.nonuniformWitness ε U V) - ↑2 ^ (#P.parts - 1) * m := by
      refine sub_le_sub_left ?_ _
      have : (2 : ℝ) ^ #P.parts = ↑2 ^ (#P.parts - 1) * 2 := by
        rw [← _root_.pow_succ, tsub_add_cancel_of_le (succ_le_iff.2 hP₁)]
      rw [← mul_div_right_comm₀, this, mul_right_comm _ (2 : ℝ), mul_assoc, le_div_iff₀]
      · gcongr _ * ?_
        exact (G.le_card_nonuniformWitness hunif).trans
          (le_mul_of_one_le_left (cast_nonneg _) one_le_two)
      have := Finset.card_pos.mpr (P.nonempty_of_mem_parts hU)
      sz_positivity
    _ ≤ #((star hP G ε hU V).biUnion id) := by
      rw [sub_le_comm, ←
        cast_sub (card_le_card <| biUnion_star_subset_nonuniformWitness hP G ε hU V), ←
        card_sdiff_of_subset (biUnion_star_subset_nonuniformWitness hP G ε hU V)]
      exact mod_cast card_nonuniformWitness_sdiff_biUnion_star hV hUV hunif

/-! ### `chunk` -/


theorem card_chunk (hm : m ≠ 0) : #(chunk hP G ε hU).parts = 4 ^ #P.parts := by
  unfold chunk
  split_ifs
  · rw [card_parts_equitabilise _ _ hm, tsub_add_cancel_of_le]
    exact le_of_lt (a_add_one_le_four_pow_parts_card ⟨U, hU⟩)
  · rw [card_parts_equitabilise _ _ hm,
      tsub_add_cancel_of_le (a_add_one_le_four_pow_parts_card ⟨U, hU⟩)]

theorem card_eq_of_mem_parts_chunk (hs : s ∈ (chunk hP G ε hU).parts) :
    #s = m ∨ #s = m + 1 := by
  unfold chunk at hs
  split_ifs at hs <;> exact card_eq_of_mem_parts_equitabilise hs

theorem m_le_card_of_mem_chunk_parts (hs : s ∈ (chunk hP G ε hU).parts) : m ≤ #s :=
  (card_eq_of_mem_parts_chunk hs).elim ge_of_eq fun i => by simp [i]

theorem card_le_m_add_one_of_mem_chunk_parts (hs : s ∈ (chunk hP G ε hU).parts) : #s ≤ m + 1 :=
  (card_eq_of_mem_parts_chunk hs).elim (fun i => by simp [i]) fun i => i.le

theorem card_biUnion_star_le_m_add_one_card_star_mul :
    (#((star hP G ε hU V).biUnion id) : ℝ) ≤ #(star hP G ε hU V) * (m + 1) :=
  mod_cast card_biUnion_le_card_mul _ _ _ fun _ hs =>
    card_le_m_add_one_of_mem_chunk_parts <| star_subset_chunk hs

/-- The stars of a non-uniform pair of parts are nonempty. -/
private theorem biUnion_star_nonempty (hV : V ∈ P.parts) (hUV : U ≠ V)
    (hunif : ¬G.IsUniform ε U V) (hPε : ↑100 ≤ ↑4 ^ #P.parts * ε ^ 5) (hε₁ : ε ≤ 1) :
    ((star hP G ε hU V).biUnion id).Nonempty := by
  have hε₀ : 0 < ε := eps_pos hPε
  have h := one_sub_eps_mul_card_nonuniformWitness_le_card_star (hP := hP) (hU := hU) hV hUV
    hunif hPε hε₁
  have hW : (0 : ℝ) < #(G.nonuniformWitness ε U V) :=
    Nat.cast_pos.2 (G.nonuniformWitness_nonempty hunif).card_pos
  rw [← card_pos, ← Nat.cast_pos (α := ℝ)]
  refine lt_of_lt_of_le (mul_pos ?_ hW) h
  linarith

private theorem star_nonempty (hV : V ∈ P.parts) (hUV : U ≠ V) (hunif : ¬G.IsUniform ε U V)
    (hPε : ↑100 ≤ ↑4 ^ #P.parts * ε ^ 5) (hε₁ : ε ≤ 1) : (star hP G ε hU V).Nonempty := by
  obtain ⟨A, hA, -⟩ := biUnion_nonempty.1 (biUnion_star_nonempty hV hUV hunif hPε hε₁)
  exact ⟨A, hA⟩

private theorem le_sum_card_subset_chunk_parts (h𝒜 : 𝒜 ⊆ (chunk hP G ε hU).parts) (hs : s ∈ 𝒜) :
    (#𝒜 : ℝ) * #s * ((m : ℝ) / (m + 1 : ℝ)) ≤ #(𝒜.sup id) := by
  rw [← mul_div_assoc₀, div_le_iff₀ coe_m_add_one_pos, mul_right_comm]
  gcongr
  · rw [← (ofSubset _ h𝒜 rfl).sum_card_parts, ofSubset_parts, ← cast_mul, cast_le]
    exact card_nsmul_le_sum _ _ _ fun x hx => m_le_card_of_mem_chunk_parts <| h𝒜 hx
  · exact mod_cast card_le_m_add_one_of_mem_chunk_parts (h𝒜 hs)

private theorem sum_card_subset_chunk_parts_le (m_pos : (0 : ℝ) < m)
    (h𝒜 : 𝒜 ⊆ (chunk hP G ε hU).parts) (hs : s ∈ 𝒜) :
    (#(𝒜.sup id) : ℝ) ≤ #𝒜 * #s * ((m + 1 : ℝ) / (m : ℝ)) := by
  rw [sup_eq_biUnion, ← mul_div_assoc₀, le_div_iff₀ m_pos, mul_right_comm]
  gcongr
  · norm_cast
    refine card_biUnion_le_card_mul _ _ _ fun x hx => ?_
    apply card_le_m_add_one_of_mem_chunk_parts (h𝒜 hx)
  · exact mod_cast m_le_card_of_mem_chunk_parts (h𝒜 hs)

private theorem one_sub_le_m_div_m_add_one_sq [Nonempty α]
    (hPα : #P.parts * 16 ^ #P.parts ≤ card α) (hPε : ↑100 ≤ ↑4 ^ #P.parts * ε ^ 5) :
    ↑1 - ε ^ 5 / ↑50 ≤ ((m : ℝ) / (m + 1 : ℝ)) ^ 2 := by
  have : (m : ℝ) / (m + 1 : ℝ) = 1 - 1 / (m + 1 : ℝ) := by
    rw [one_sub_div, add_sub_cancel_right]
  rw [this, sub_sq, one_pow, mul_one]
  refine le_trans ?_ (le_add_of_nonneg_right <| sq_nonneg _)
  rw [sub_le_sub_iff_left, ← le_div_iff₀' (show (0 : ℝ) < 2 by simp), div_div₀,
    one_div_le coe_m_add_one_pos, one_div_div₀]
  · refine le_trans ?_ (le_add_of_nonneg_right zero_le_one)
    norm_num
    apply hundred_div_ε_pow_five_le_m hPα hPε
  sz_positivity

private theorem m_add_one_div_m_le_one_add [Nonempty α]
    (hPα : #P.parts * 16 ^ #P.parts ≤ card α) (hPε : ↑100 ≤ ↑4 ^ #P.parts * ε ^ 5) (hε₁ : ε ≤ 1) :
    (Checked.div ((m : ℝ) + 1) m (Nat.cast_pos.2 (m_pos hPα)).ne'.isUnit) ^ 2 ≤
      ↑1 + ε ^ 5 / 49 := by
  have : 0 ≤ ε := by sz_positivity
  have hε₀ : 0 < ε := eps_pos hPε
  have hm₀ : (0 : ℝ) < m := Nat.cast_pos.2 (m_pos hPα)
  rw [same_add_div]
  calc
    _ ≤ (1 + ε ^ 5 / 100) ^ 2 := by
      have h : (1 : ℝ) / (m : ℝ) ≤ ε ^ 5 / 100 := calc
        (1 : ℝ) / (m : ℝ) ≤ 1 / (100 / ε ^ 5) :=
          one_div_le_one_div_of_le (by sz_positivity) (hundred_div_ε_pow_five_le_m hPα hPε)
        _ = ε ^ 5 / 100 := one_div_div₀
      have : (0 : ℝ) ≤ 1 / (m : ℝ) := by positivity
      gcongr
    _ = 1 + ε ^ 5 * (50⁻¹ + ε ^ 5 / 10000) := by ring
    _ ≤ 1 + ε ^ 5 * (50⁻¹ + 1 ^ 5 / 10000) := by gcongr
    _ ≤ 1 + ε ^ 5 * 49⁻¹ := by gcongr; norm_num
    _ = 1 + ε ^ 5 / 49 := by rw [div_eq_mul_inv₀]

/-- The union of a nonempty finset of parts of `chunk` is nonempty. -/
private theorem biUnion_nonempty_of_subset_chunk {A : Finset (Finset α)}
    (hA : A ⊆ (chunk hP G ε hU).parts) (hA' : A.Nonempty) : (A.biUnion id).Nonempty :=
  hA'.biUnion fun _ ha ↦ (chunk hP G ε hU).nonempty_of_mem_parts (hA ha)

/-- The number of edges between the unions of two finsets of parts of chunks is the sum of the
numbers of edges between their pairs of parts. -/
private theorem card_interedges_biUnion {hU : U ∈ P.parts} {hV : V ∈ P.parts}
    {A B : Finset (Finset α)} (hA : A ⊆ (chunk hP G ε hU).parts)
    (hB : B ⊆ (chunk hP G ε hV).parts) :
    (#(G.interedges (A.biUnion id) (B.biUnion id)) : ℝ) =
      ∑ ab : ↥(A ×ˢ B), (#(G.interedges ab.1.1 ab.1.2) : ℝ) := by
  rw [SimpleGraph.interedges, ← sup_eq_biUnion, ← sup_eq_biUnion,
    Rel.card_interedges_finpartition _ (ofSubset _ hA rfl) (ofSubset _ hB rfl), ofSubset_parts,
    ofSubset_parts, Nat.cast_sum, ← sum_coe_sort]
  rfl

private theorem density_sub_eps_le_sum_density_div_card [Nonempty α]
    (hPα : #P.parts * 16 ^ #P.parts ≤ card α) (hPε : ↑100 ≤ ↑4 ^ #P.parts * ε ^ 5)
    {hU : U ∈ P.parts} {hV : V ∈ P.parts} {A B : Finset (Finset α)}
    (hA : A ⊆ (chunk hP G ε hU).parts) (hB : B ⊆ (chunk hP G ε hV).parts) (hA' : A.Nonempty)
    (hB' : B.Nonempty) :
    (G.edgeDensity (A.biUnion id) (B.biUnion id) (biUnion_nonempty_of_subset_chunk hA hA')
      (biUnion_nonempty_of_subset_chunk hB hB') : ℝ) - ε ^ 5 / 50 ≤
    (∑ ab : ↥(A ×ˢ B), (G.edgeDensity ab.1.1 ab.1.2
      ((chunk hP G ε hU).nonempty_of_mem_parts (hA (mem_product.1 ab.2).1))
      ((chunk hP G ε hV).nonempty_of_mem_parts (hB (mem_product.1 ab.2).2)) : ℝ)) /
        ((#A : ℝ) * #B) := by
  have hAU := biUnion_nonempty_of_subset_chunk hA hA'
  have hBV := biUnion_nonempty_of_subset_chunk hB hB'
  have : ↑(G.edgeDensity (A.biUnion id) (B.biUnion id) hAU hBV) - ε ^ 5 / ↑50 ≤
      (↑1 - ε ^ 5 / 50) * G.edgeDensity (A.biUnion id) (B.biUnion id) hAU hBV := by
    rw [sub_mul, one_mul, sub_le_sub_iff_left]
    refine mul_le_of_le_one_right (by sz_positivity) ?_
    exact mod_cast G.edgeDensity_le_one _ _ _ _
  refine this.trans ?_
  have hc := one_sub_le_m_div_m_add_one_sq hPα hPε
  calc
    _ = ∑ ab : ↥(A ×ˢ B), (1 - ε ^ 5 / 50) * (#(G.interedges ab.1.1 ab.1.2) : ℝ) /
          ((#(A.biUnion id) : ℝ) * #(B.biUnion id)) := by
      rw [SimpleGraph.edgeDensity_def]
      push_cast
      rw [card_interedges_biUnion hA hB]
      simp only [div_eq_mul_inv₀, mul_sum, sum_mul, mul_assoc]
    _ ≤ ∑ ab : ↥(A ×ˢ B), (G.edgeDensity ab.1.1 ab.1.2
          ((chunk hP G ε hU).nonempty_of_mem_parts (hA (mem_product.1 ab.2).1))
          ((chunk hP G ε hV).nonempty_of_mem_parts (hB (mem_product.1 ab.2).2)) : ℝ) /
            ((#A : ℝ) * #B) := by
      refine sum_le_sum fun ab _ ↦ ?_
      obtain ⟨⟨x, y⟩, hxy⟩ := ab
      obtain ⟨hx, hy⟩ := mem_product.1 hxy
      have := (chunk hP G ε hU).nonempty_of_mem_parts (hA hx)
      have := (chunk hP G ε hV).nonempty_of_mem_parts (hB hy)
      have hxA := le_sum_card_subset_chunk_parts hA hx
      have hyB := le_sum_card_subset_chunk_parts hB hy
      rw [sup_eq_biUnion] at hxA hyB
      dsimp only
      rw [SimpleGraph.edgeDensity_def]
      push_cast
      rw [div_div₀, div_le_div_iff₀ (by positivity) (by positivity)]
      calc (1 - ε ^ 5 / 50) * (#(G.interedges x y) : ℝ) * (#x * #y * (#A * #B))
          = #(G.interedges x y) * ((1 - ε ^ 5 / 50) * (#A * #x * (#B * #y))) := by ring
        _ ≤ #(G.interedges x y) * (((m : ℝ) / (m + 1 : ℝ)) ^ 2 * (#A * #x * (#B * #y))) := by gcongr
        _ = #(G.interedges x y) *
            ((#A * #x * ((m : ℝ) / (m + 1 : ℝ))) * (#B * #y * ((m : ℝ) / (m + 1 : ℝ)))) := by
          ring
        _ ≤ #(G.interedges x y) * ((#(A.biUnion id) : ℝ) * #(B.biUnion id)) := by gcongr
    _ = _ := by simp only [div_eq_mul_inv₀, sum_mul]

private theorem sum_density_div_card_le_density_add_eps [Nonempty α]
    (hPα : #P.parts * 16 ^ #P.parts ≤ card α) (hPε : ↑100 ≤ ↑4 ^ #P.parts * ε ^ 5)
    (hε₁ : ε ≤ 1) {hU : U ∈ P.parts} {hV : V ∈ P.parts} {A B : Finset (Finset α)}
    (hA : A ⊆ (chunk hP G ε hU).parts) (hB : B ⊆ (chunk hP G ε hV).parts) (hA' : A.Nonempty)
    (hB' : B.Nonempty) :
    (∑ ab : ↥(A ×ˢ B), (G.edgeDensity ab.1.1 ab.1.2
      ((chunk hP G ε hU).nonempty_of_mem_parts (hA (mem_product.1 ab.2).1))
      ((chunk hP G ε hV).nonempty_of_mem_parts (hB (mem_product.1 ab.2).2)) : ℝ)) /
        ((#A : ℝ) * #B) ≤
    G.edgeDensity (A.biUnion id) (B.biUnion id) (biUnion_nonempty_of_subset_chunk hA hA')
      (biUnion_nonempty_of_subset_chunk hB hB') + ε ^ 5 / 49 := by
  have hAU := biUnion_nonempty_of_subset_chunk hA hA'
  have hBV := biUnion_nonempty_of_subset_chunk hB hB'
  have : (↑1 + ε ^ 5 / ↑49) * G.edgeDensity (A.biUnion id) (B.biUnion id) hAU hBV ≤
      G.edgeDensity (A.biUnion id) (B.biUnion id) hAU hBV + ε ^ 5 / 49 := by
    rw [add_mul, one_mul, add_le_add_iff_left]
    refine mul_le_of_le_one_right (by sz_positivity) ?_
    exact mod_cast G.edgeDensity_le_one _ _ _ _
  refine le_trans ?_ this
  have hm : (0 : ℝ) < m := by sz_positivity
  have hc := m_add_one_div_m_le_one_add hPα hPε hε₁
  calc
    _ = ∑ ab : ↥(A ×ˢ B), (G.edgeDensity ab.1.1 ab.1.2
          ((chunk hP G ε hU).nonempty_of_mem_parts (hA (mem_product.1 ab.2).1))
          ((chunk hP G ε hV).nonempty_of_mem_parts (hB (mem_product.1 ab.2).2)) : ℝ) /
            ((#A : ℝ) * #B) := by simp only [div_eq_mul_inv₀, sum_mul]
    _ ≤ ∑ ab : ↥(A ×ˢ B), (1 + ε ^ 5 / 49) * (#(G.interedges ab.1.1 ab.1.2) : ℝ) /
          ((#(A.biUnion id) : ℝ) * #(B.biUnion id)) := by
      refine sum_le_sum fun ab _ ↦ ?_
      obtain ⟨⟨x, y⟩, hxy⟩ := ab
      obtain ⟨hx, hy⟩ := mem_product.1 hxy
      have := (chunk hP G ε hU).nonempty_of_mem_parts (hA hx)
      have := (chunk hP G ε hV).nonempty_of_mem_parts (hB hy)
      have hxA := sum_card_subset_chunk_parts_le hm hA hx
      have hyB := sum_card_subset_chunk_parts_le hm hB hy
      rw [sup_eq_biUnion] at hxA hyB
      dsimp only
      rw [SimpleGraph.edgeDensity_def]
      push_cast
      rw [div_div₀, div_le_div_iff₀ (by positivity) (by positivity)]
      calc (#(G.interedges x y) : ℝ) * (#(A.biUnion id) * #(B.biUnion id))
          ≤ #(G.interedges x y) *
            ((#A * #x * ((m + 1 : ℝ) / (m : ℝ))) * (#B * #y * ((m + 1 : ℝ) / (m : ℝ)))) := by
            gcongr
        _ = #(G.interedges x y) * (((m + 1 : ℝ) / (m : ℝ)) ^ 2 * (#A * #x * (#B * #y))) := by ring
        _ ≤ #(G.interedges x y) * ((1 + ε ^ 5 / 49) * (#A * #x * (#B * #y))) := by gcongr
        _ = (1 + ε ^ 5 / 49) * #(G.interedges x y) * (#x * #y * (#A * #B)) := by ring
    _ = _ := by
      rw [SimpleGraph.edgeDensity_def]
      push_cast
      rw [card_interedges_biUnion hA hB]
      simp only [div_eq_mul_inv₀, mul_sum, sum_mul, mul_assoc]

private theorem average_density_near_total_density [Nonempty α]
    (hPα : #P.parts * 16 ^ #P.parts ≤ card α) (hPε : ↑100 ≤ ↑4 ^ #P.parts * ε ^ 5)
    (hε₁ : ε ≤ 1) {hU : U ∈ P.parts} {hV : V ∈ P.parts} {A B : Finset (Finset α)}
    (hA : A ⊆ (chunk hP G ε hU).parts) (hB : B ⊆ (chunk hP G ε hV).parts) (hA' : A.Nonempty)
    (hB' : B.Nonempty) :
    |(∑ ab : ↥(A ×ˢ B), (G.edgeDensity ab.1.1 ab.1.2
      ((chunk hP G ε hU).nonempty_of_mem_parts (hA (mem_product.1 ab.2).1))
      ((chunk hP G ε hV).nonempty_of_mem_parts (hB (mem_product.1 ab.2).2)) : ℝ)) /
        ((#A : ℝ) * #B) -
      G.edgeDensity (A.biUnion id) (B.biUnion id) (biUnion_nonempty_of_subset_chunk hA hA')
        (biUnion_nonempty_of_subset_chunk hB hB')| ≤ ε ^ 5 / 49 := by
  rw [abs_sub_le_iff]
  constructor
  · rw [sub_le_iff_le_add']
    exact sum_density_div_card_le_density_add_eps hPα hPε hε₁ hA hB hA' hB'
  suffices (G.edgeDensity (A.biUnion id) (B.biUnion id) (biUnion_nonempty_of_subset_chunk hA hA')
      (biUnion_nonempty_of_subset_chunk hB hB') : ℝ) -
      (∑ ab : ↥(A ×ˢ B), (G.edgeDensity ab.1.1 ab.1.2
        ((chunk hP G ε hU).nonempty_of_mem_parts (hA (mem_product.1 ab.2).1))
        ((chunk hP G ε hV).nonempty_of_mem_parts (hB (mem_product.1 ab.2).2)) : ℝ)) /
          ((#A : ℝ) * #B) ≤ ε ^ 5 / 50 by
    apply this.trans
    gcongr <;> [sz_positivity; norm_num]
  rw [sub_le_iff_le_add, ← sub_le_iff_le_add']
  apply density_sub_eps_le_sum_density_div_card hPα hPε hA hB hA' hB'

/-- The parts of `chunk` form a nonempty finset. -/
private theorem chunk_parts_nonempty : (chunk hP G ε hU).parts.Nonempty :=
  (chunk hP G ε hU).parts_nonempty (P.nonempty_of_mem_parts hU).ne_empty

/-- The product of the parts of two chunks has `16 ^ #P.parts` elements. -/
private theorem card_chunk_mul_card_chunk [Nonempty α] (hPα : #P.parts * 16 ^ #P.parts ≤ card α)
    {hU : U ∈ P.parts} {hV : V ∈ P.parts} :
    (#(chunk hP G ε hU).parts * #(chunk hP G ε hV).parts : ℝ) = 16 ^ #P.parts := by
  rw [card_chunk (m_pos hPα).ne', card_chunk (m_pos hPα).ne']
  push_cast
  rw [← mul_pow]
  norm_num

private theorem edgeDensity_chunk_aux [Nonempty α] (hP)
    (hPα : #P.parts * 16 ^ #P.parts ≤ card α) (hPε : ↑100 ≤ ↑4 ^ #P.parts * ε ^ 5)
    (hU : U ∈ P.parts) (hV : V ∈ P.parts) :
    (G.edgeDensity U V : ℝ) ^ 2 - ε ^ 5 / ↑25 ≤
    ((∑ ab : ↥((chunk hP G ε hU).parts ×ˢ (chunk hP G ε hV).parts), (G.edgeDensity ab.1.1 ab.1.2
      ((chunk hP G ε hU).nonempty_of_mem_parts (mem_product.1 ab.2).1)
      ((chunk hP G ε hV).nonempty_of_mem_parts (mem_product.1 ab.2).2) : ℝ)) /
        ↑16 ^ #P.parts) ^ 2 := by
  obtain hGε | hGε := le_total (G.edgeDensity U V : ℝ) (ε ^ 5 / 50)
  · refine (sub_nonpos_of_le <| (sq_le ?_ ?_).trans <| hGε.trans ?_).trans (sq_nonneg _)
    · exact mod_cast G.edgeDensity_nonneg _ _ _ _
    · exact mod_cast G.edgeDensity_le_one _ _ _ _
    · exact div_le_div_of_nonneg_left (by sz_positivity) (by simp) (by norm_num)
  rw [← sub_nonneg] at hGε
  have : 0 ≤ ε := by sz_positivity
  calc
    _ = (G.edgeDensity U V : ℝ) ^ 2 - 1 * ε ^ 5 / 25 + (0 : ℝ) ^ 10 / 2500 := by ring
    _ ≤ (G.edgeDensity U V : ℝ) ^ 2 - G.edgeDensity U V * ε ^ 5 / 25 + ε ^ 10 / 2500 := by
      gcongr; exact mod_cast G.edgeDensity_le_one ..
    _ = (G.edgeDensity U V - ε ^ 5 / 50) ^ 2 := by ring
    _ ≤ _ := by
      gcongr
      have h := density_sub_eps_le_sum_density_div_card hPα hPε
        (Subset.refl (chunk hP G ε hU).parts) (Subset.refl (chunk hP G ε hV).parts)
        chunk_parts_nonempty chunk_parts_nonempty
      simp only [biUnion_parts, card_chunk_mul_card_chunk hPα] at h
      exact h

private theorem abs_density_star_sub_density_le_eps (hPε : ↑100 ≤ ↑4 ^ #P.parts * ε ^ 5)
    (hε₁ : ε ≤ 1) {hU : U ∈ P.parts} {hV : V ∈ P.parts} (hUV' : U ≠ V)
    (hUV : ¬G.IsUniform ε U V) :
    |(G.edgeDensity ((star hP G ε hU V).biUnion id) ((star hP G ε hV U).biUnion id)
      (biUnion_star_nonempty hV hUV' hUV hPε hε₁)
      (biUnion_star_nonempty hU hUV'.symm (fun hVU => hUV hVU.symm) hPε hε₁) : ℝ) -
      G.edgeDensity (G.nonuniformWitness ε U V) (G.nonuniformWitness ε V U)
        (G.nonuniformWitness_nonempty hUV) (G.nonuniformWitness_nonempty fun h => hUV h.symm)| ≤
      ε / 5 := by
  convert!
    abs_edgeDensity_sub_edgeDensity_le_two_mul G.Adj
      (biUnion_star_subset_nonuniformWitness hP G ε hU V)
      (biUnion_star_subset_nonuniformWitness hP G ε hV U)
      (one_sub_eps_mul_card_nonuniformWitness_le_card_star hV hUV' hUV hPε hε₁)
      (one_sub_eps_mul_card_nonuniformWitness_le_card_star hU hUV'.symm (fun hVU => hUV hVU.symm)
        hPε hε₁)
      (biUnion_star_nonempty hV hUV' hUV hPε hε₁)
      (biUnion_star_nonempty hU hUV'.symm (fun hVU => hUV hVU.symm) hPε hε₁) using 1
  linarith

private theorem eps_le_card_star_div [Nonempty α] (hPα : #P.parts * 16 ^ #P.parts ≤ card α)
    (hPε : ↑100 ≤ ↑4 ^ #P.parts * ε ^ 5) (hε₁ : ε ≤ 1) (hU : U ∈ P.parts) (hV : V ∈ P.parts)
    (hUV : U ≠ V) (hunif : ¬G.IsUniform ε U V) :
    ↑4 / ↑5 * ε ≤ (#(star hP G ε hU V) : ℝ) / ↑4 ^ #P.parts := by
  have hm₀ : (0 : ℝ) < m := by sz_positivity
  have hm : (0 : ℝ) ≤ 1 - (m : ℝ)⁻¹ := sub_nonneg_of_le (inv_le_one_of_one_le₀ <| one_le_m_coe hPα)
  have hε : 0 ≤ 1 - ε / 10 :=
    sub_nonneg_of_le (div_le_one_of_le₀ (hε₁.trans <| by simp) <| by norm_num)
  have hε₀ : 0 < ε := by sz_positivity
  calc
    4 / 5 * ε = (1 - 1 / 10) * (1 - 9⁻¹) * ε := by norm_num
    _ ≤ (1 - ε / 10) * (1 - (m : ℝ)⁻¹) * ((#(G.nonuniformWitness ε U V) : ℝ) / (#U : ℝ)) := by
        gcongr
        exacts [mod_cast (show 9 ≤ 100 by simp).trans (hundred_le_m hPα hPε hε₁),
          (le_div_iff₀' <| cast_pos.2 (P.nonempty_of_mem_parts hU).card_pos).2 <|
           G.le_card_nonuniformWitness hunif]
    _ = (1 - ε / 10) * #(G.nonuniformWitness ε U V) * ((1 - (m : ℝ)⁻¹) / (#U : ℝ)) := by
      rw [mul_assoc, mul_assoc, mul_div_left_comm₀]
    _ ≤ #((star hP G ε hU V).biUnion id) * ((1 - (m : ℝ)⁻¹) / (#U : ℝ)) := by
      gcongr
      exact one_sub_eps_mul_card_nonuniformWitness_le_card_star hV hUV hunif hPε hε₁
    _ ≤ #(star hP G ε hU V) * (m + 1) * ((1 - (m : ℝ)⁻¹) / (#U : ℝ)) := by
      gcongr
      exact card_biUnion_star_le_m_add_one_card_star_mul
    _ ≤ #(star hP G ε hU V) * (m + ↑1) * ((↑1 - (m : ℝ)⁻¹) / ((4 : ℝ) ^ #P.parts * m)) := by
      gcongr
      exact pow_mul_m_le_card_part hP hU
    _ = (#(star hP G ε hU V) : ℝ) / ↑4 ^ #P.parts *
        ((m + 1 : ℝ) * (1 - (m : ℝ)⁻¹) / (m : ℝ)) := by
      field_simp
    _ ≤ (#(star hP G ε hU V) : ℝ) / ↑4 ^ #P.parts * 1 := by
      gcongr
      rw [div_le_one hm₀]
      have hinv : (m : ℝ) * (m : ℝ)⁻¹ = 1 := mul_inv_cancel₀
      nlinarith [inv_pos_of_pos hm₀]
    _ = _ := mul_one _

/-- The product of the cardinalities of the stars of a non-uniform pair of parts is positive. -/
private theorem card_star_mul_card_star_pos (hPε : ↑100 ≤ ↑4 ^ #P.parts * ε ^ 5) (hε₁ : ε ≤ 1)
    {hU : U ∈ P.parts} {hV : V ∈ P.parts} (hUVne : U ≠ V) (hUV : ¬G.IsUniform ε U V) :
    (0 : ℝ) < #(star hP G ε hU V) * #(star hP G ε hV U) := by
  have := star_nonempty (hP := hP) (hU := hU) hV hUVne hUV hPε hε₁
  have := star_nonempty (hP := hP) (hU := hV) hU hUVne.symm (fun h => hUV h.symm) hPε hε₁
  positivity

/-!
### Final bounds

Those inequalities are the end result of all this hard work.
-/


/-- Lower bound on the edge densities between non-uniform parts of `SzemerediRegularity.star`. -/
private theorem edgeDensity_star_not_uniform [Nonempty α]
    (hPα : #P.parts * 16 ^ #P.parts ≤ card α) (hPε : ↑100 ≤ ↑4 ^ #P.parts * ε ^ 5)
    (hε₁ : ε ≤ 1) {hU : U ∈ P.parts} {hV : V ∈ P.parts} (hUVne : U ≠ V)
    (hUV : ¬G.IsUniform ε U V) :
    ↑3 / ↑4 * ε ≤
    |Checked.div (∑ ab : ↥((star hP G ε hU V) ×ˢ (star hP G ε hV U)), (G.edgeDensity ab.1.1 ab.1.2
        ((chunk hP G ε hU).nonempty_of_mem_parts (star_subset_chunk (mem_product.1 ab.2).1))
        ((chunk hP G ε hV).nonempty_of_mem_parts (star_subset_chunk (mem_product.1 ab.2).2)) :
          ℝ))
      (#(star hP G ε hU V) * #(star hP G ε hV U))
      (card_star_mul_card_star_pos hPε hε₁ hUVne hUV).ne'.isUnit -
        (∑ ab : ↥((chunk hP G ε hU).parts ×ˢ (chunk hP G ε hV).parts),
          (G.edgeDensity ab.1.1 ab.1.2
            ((chunk hP G ε hU).nonempty_of_mem_parts (mem_product.1 ab.2).1)
            ((chunk hP G ε hV).nonempty_of_mem_parts (mem_product.1 ab.2).2) : ℝ)) /
              (16 : ℝ) ^ #P.parts| := by
  have hrs := abs_density_star_sub_density_le_eps (hP := hP) (hU := hU) (hV := hV) hPε hε₁ hUVne hUV
  have hst := G.nonuniformWitness_spec hUVne hUV
  have hpr := average_density_near_total_density (hP := hP) (hU := hU) (hV := hV) hPα hPε hε₁
    star_subset_chunk star_subset_chunk (star_nonempty (hP := hP) (hU := hU) hV hUVne hUV hPε hε₁)
    (star_nonempty (hP := hP) (hU := hV) hU hUVne.symm (fun h => hUV h.symm) hPε hε₁)
  have hqt := average_density_near_total_density (hP := hP) (hU := hU) (hV := hV) hPα hPε hε₁
    (Subset.refl (chunk hP G ε hU).parts) (Subset.refl (chunk hP G ε hV).parts)
    chunk_parts_nonempty chunk_parts_nonempty
  simp only [biUnion_parts, card_chunk_mul_card_chunk hPα] at hqt
  have hε' : ε ^ 5 ≤ ε := by
    simpa using pow_le_pow_of_le_one (by sz_positivity) hε₁ (show 1 ≤ 5 by simp)
  rw [Rat.cast_abs, Rat.cast_sub] at hst
  obtain ⟨hrs₁, hrs₂⟩ := abs_le.1 hrs
  obtain ⟨hpr₁, hpr₂⟩ := abs_le.1 hpr
  obtain ⟨hqt₁, hqt₂⟩ := abs_le.1 hqt
  rcases le_abs.1 hst with h | h
  · exact le_abs.2 (Or.inl (by linarith))
  · exact le_abs.2 (Or.inr (by linarith))

/-- Lower bound on the edge densities between non-uniform parts of `SzemerediRegularity.increment`.
-/
theorem edgeDensity_chunk_not_uniform [Nonempty α] (hPα : #P.parts * 16 ^ #P.parts ≤ card α)
    (hPε : ↑100 ≤ ↑4 ^ #P.parts * ε ^ 5) (hε₁ : ε ≤ 1) {hU : U ∈ P.parts} {hV : V ∈ P.parts}
    (hUVne : U ≠ V)
    (hUV : ¬G.IsUniform ε U V (P.nonempty_of_mem_parts hU) (P.nonempty_of_mem_parts hV)) :
    (G.edgeDensity U V (P.nonempty_of_mem_parts hU) (P.nonempty_of_mem_parts hV) : ℝ) ^ 2 -
      ε ^ 5 / ↑25 + ε ^ 4 / ↑3 ≤
    (∑ ab : ↥((chunk hP G ε hU).parts ×ˢ (chunk hP G ε hV).parts), (G.edgeDensity ab.1.1 ab.1.2
      ((chunk hP G ε hU).nonempty_of_mem_parts (mem_product.1 ab.2).1)
      ((chunk hP G ε hV).nonempty_of_mem_parts (mem_product.1 ab.2).2) : ℝ) ^ 2) /
        ↑16 ^ #P.parts := by
  have hU₀ := P.nonempty_of_mem_parts hU
  have hV₀ := P.nonempty_of_mem_parts hV
  have hε₀ : 0 < ε := by sz_positivity
  have hST : ∀ ab, ab ∈ (star hP G ε hU V) ×ˢ (star hP G ε hV U) →
      ab ∈ (chunk hP G ε hU).parts ×ˢ (chunk hP G ε hV).parts :=
    fun _ h ↦ product_subset_product star_subset_chunk star_subset_chunk h
  have hs : (#((univ : Finset ↥((star hP G ε hU V) ×ˢ (star hP G ε hV U))).map
      (Subtype.impEmbedding _ _ hST)) : ℝ) = #(star hP G ε hU V) * #(star hP G ε hV U) := by
    rw [card_map, Finset.card_univ, Fintype.card_coe, card_product, cast_mul]
  have ht : (#(univ : Finset ↥((chunk hP G ε hU).parts ×ˢ (chunk hP G ε hV).parts)) : ℝ) =
      16 ^ #P.parts := by
    rw [Finset.card_univ, Fintype.card_coe, card_product, cast_mul, card_chunk_mul_card_chunk hPα]
  have hpos := card_star_mul_card_star_pos (hP := hP) (hU := hU) (hV := hV) hPε hε₁ hUVne hUV
  have h16 : (0 : ℝ) < 16 ^ #P.parts := by positivity
  have key := add_div_le_sum_sq_div_card
    (s := (univ : Finset ↥((star hP G ε hU V) ×ˢ (star hP G ε hV U))).map
      (Subtype.impEmbedding _ _ hST)) (t := univ)
    (hsUnit := by rw [hs]; exact hpos.ne'.isUnit) (htUnit := by rw [ht]; exact h16.ne'.isUnit)
    (subset_univ _)
    (fun ab : ↥((chunk hP G ε hU).parts ×ˢ (chunk hP G ε hV).parts) ↦ (G.edgeDensity ab.1.1 ab.1.2
      ((chunk hP G ε hU).nonempty_of_mem_parts (mem_product.1 ab.2).1)
      ((chunk hP G ε hV).nonempty_of_mem_parts (mem_product.1 ab.2).2) : ℝ))
    ((G.edgeDensity U V : ℝ) ^ 2 - ε ^ 5 / 25) (x := 3 / 4 * ε) (by positivity) ?_ ?_
  · simp only [hs, ht] at key
    refine le_trans (add_le_add le_rfl ?_) key
    have Ul := eps_le_card_star_div (hP := hP) hPα hPε hε₁ hU hV hUVne hUV
    have Vl := eps_le_card_star_div (hP := hP) hPα hPε hε₁ hV hU hUVne.symm fun h => hUV h.symm
    have h16' : (#(star hP G ε hU V) : ℝ) * (#(star hP G ε hV U) : ℝ) / 16 ^ #P.parts =
        (#(star hP G ε hU V) : ℝ) / 4 ^ #P.parts * ((#(star hP G ε hV U) : ℝ) / 4 ^ #P.parts) := by
      rw [div_mul_div_comm₀]
      congr 1
      rw [← mul_pow]
      norm_num
    rw [h16']
    calc ε ^ 4 / 3 ≤ 4 / 5 * ε * (4 / 5 * ε) * (3 / 4 * ε) ^ 2 := by
          have : 0 ≤ ε ^ 4 := by positivity
          linarith
      _ ≤ _ := by gcongr
  · rw [sum_map]
    simp only [hs, ht]
    exact edgeDensity_star_not_uniform hPα hPε hε₁ hUVne hUV
  · simp only [ht]
    exact edgeDensity_chunk_aux hP hPα hPε hU hV

/-- Lower bound on the edge densities between parts of `SzemerediRegularity.increment`. This is the
blanket lower bound used the uniform parts. -/
theorem edgeDensity_chunk_uniform [Nonempty α] (hPα : #P.parts * 16 ^ #P.parts ≤ card α)
    (hPε : ↑100 ≤ ↑4 ^ #P.parts * ε ^ 5) (hU : U ∈ P.parts) (hV : V ∈ P.parts) :
    (G.edgeDensity U V (P.nonempty_of_mem_parts hU) (P.nonempty_of_mem_parts hV) : ℝ) ^ 2 -
      ε ^ 5 / ↑25 ≤
    (∑ ab : ↥((chunk hP G ε hU).parts ×ˢ (chunk hP G ε hV).parts), (G.edgeDensity ab.1.1 ab.1.2
      ((chunk hP G ε hU).nonempty_of_mem_parts (mem_product.1 ab.2).1)
      ((chunk hP G ε hV).nonempty_of_mem_parts (mem_product.1 ab.2).2) : ℝ) ^ 2) /
        ↑16 ^ #P.parts := by
  apply (edgeDensity_chunk_aux (hP := hP) hPα hPε hU hV).trans
  have ht : (#(univ : Finset ↥((chunk hP G ε hU).parts ×ˢ (chunk hP G ε hV).parts)) : ℝ) =
      16 ^ #P.parts := by
    rw [Finset.card_univ, Fintype.card_coe, card_product, cast_mul, card_chunk_mul_card_chunk hPα]
  have h16 : (0 : ℝ) < 16 ^ #P.parts := by positivity
  have := mul_sq_le_sum_sq (s := univ) (t := univ) (hsUnit := by rw [ht]; exact h16.ne'.isUnit)
    subset_rfl (fun ab : ↥((chunk hP G ε hU).parts ×ˢ (chunk hP G ε hV).parts) ↦
      (G.edgeDensity ab.1.1 ab.1.2
        ((chunk hP G ε hU).nonempty_of_mem_parts (mem_product.1 ab.2).1)
        ((chunk hP G ε hV).nonempty_of_mem_parts (mem_product.1 ab.2).2) : ℝ)) le_rfl
  simp only [ht] at this
  rw [le_div_iff₀ h16]
  linarith

end SzemerediRegularity
