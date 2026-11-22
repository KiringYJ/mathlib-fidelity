/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Combinatorics.SimpleGraph.Density
public import Mathlib.Data.Nat.Cast.Order.Field
public import Mathlib.Order.Partition.Equipartition
public import Mathlib.SetTheory.Cardinal.Order

/-!
# Graph uniformity and uniform partitions

In this file we define uniformity of a pair of vertices in a graph and uniformity of a partition of
vertices of a graph. Both are also known as ε-regularity.

Nonempty finsets of vertices `s` and `t` are `ε`-uniform in a graph `G` if their edge density is at
most `ε`-far from the density of any big enough nonempty `s'` and `t'` where `s' ⊆ s`, `t' ⊆ t`.
The definition is pretty technical, but it amounts to the edges between `s` and `t` being "random"
The literature contains several definitions which are equivalent up to scaling `ε` by some constant
when the partition is equitable.

A partition `P` of the vertices is `ε`-uniform if the proportion of `ε`-uniform pairs of parts is
greater than `(1 - ε)`.

Edge densities exist only between nonempty finsets. Uniformity of a pair therefore takes the
nonemptiness of both finsets, and the parts of a partition supply it by their membership.

## Main declarations

* `SimpleGraph.IsUniform`: Graph uniformity of a pair of nonempty finsets of vertices.
* `SimpleGraph.nonuniformWitness`: `G.nonuniformWitness ε s t` and `G.nonuniformWitness ε t s`
  together witness the non-uniformity of `s` and `t`.
* `Finpartition.nonUniforms`: Nonuniform pairs of parts of a partition.
* `Finpartition.IsUniform`: Uniformity of a partition.
* `Finpartition.nonuniformWitnesses`: For each non-uniform pair of parts of a partition, pick
  witnesses of non-uniformity and dump them all together.

## References

[Yaël Dillies, Bhavik Mehta, *Formalising Szemerédi’s Regularity Lemma in Lean*][srl_itp]
-/

@[expose] public section


open Finset

variable {α 𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-! ### Graph uniformity -/


namespace SimpleGraph

variable (G : SimpleGraph α) [DecidableRel G.Adj] (ε : 𝕜) {s t : Finset α} {a b : α}

/-- A pair of nonempty finsets of vertices is `ε`-uniform (aka `ε`-regular) iff their edge density
is close to the density of any big enough pair of nonempty subsets. Intuitively, the edges between
them are random-like.

Edge densities exist only between nonempty finsets, so the definition takes the nonemptiness of `s`
and `t`, found in the local context by default, and compares the densities of nonempty subsets
only. When `0 < ε`, the cardinality conditions already force the subsets to be nonempty. -/
def IsUniform (s t : Finset α)
    (hs : s.Nonempty := by first | assumption | fail "uniformity needs a nonempty left set")
    (ht : t.Nonempty := by first | assumption | fail "uniformity needs a nonempty right set") :
    Prop :=
  ∀ ⦃s'⦄, s' ⊆ s → ∀ ⦃t'⦄, t' ⊆ t → (#s : 𝕜) * ε ≤ #s' → (#t : 𝕜) * ε ≤ #t' →
    ∀ (hs' : s'.Nonempty) (ht' : t'.Nonempty),
      |(G.edgeDensity s' t' : 𝕜) - (G.edgeDensity s t : 𝕜)| < ε

noncomputable instance (s t : Finset α) (hs : s.Nonempty) (ht : t.Nonempty) :
    Decidable (G.IsUniform ε s t hs ht) := by
  unfold IsUniform; infer_instance

variable {G ε} {hs : s.Nonempty} {ht : t.Nonempty}

theorem IsUniform.mono {ε' : 𝕜} (h : ε ≤ ε') (hε : IsUniform G ε s t) : IsUniform G ε' s t :=
  fun s' hs' t' ht' hs ht hs'' ht'' => by
  refine (hε hs' ht' (le_trans ?_ hs) (le_trans ?_ ht) hs'' ht'').trans_le h <;> gcongr

theorem IsUniform.symm (h : IsUniform G ε s t) : IsUniform G ε t s :=
  fun t' ht' s' hs' ht hs ht'' hs'' => by
  rw [edgeDensity_comm _ t', edgeDensity_comm _ t]
  exact h hs' ht' hs ht hs'' ht''

variable (G)

theorem isUniform_comm : IsUniform G ε s t ↔ IsUniform G ε t s :=
  ⟨IsUniform.symm, IsUniform.symm⟩

lemma isUniform_one : G.IsUniform (1 : 𝕜) s t := by
  intro s' hs' t' ht' hs ht hs'' ht''
  rw [mul_one] at hs ht
  obtain rfl := eq_of_subset_of_card_le hs' (Nat.cast_le.1 hs)
  obtain rfl := eq_of_subset_of_card_le ht' (Nat.cast_le.1 ht)
  rw [sub_self, abs_zero]
  exact zero_lt_one

variable {G}

lemma IsUniform.pos (hG : G.IsUniform ε s t) : 0 < ε :=
  not_le.1 fun hε ↦ (hε.trans <| abs_nonneg _).not_gt <| hG subset_rfl subset_rfl
    (mul_le_of_le_one_right (Nat.cast_nonneg _) <| hε.trans zero_le_one)
    (mul_le_of_le_one_right (Nat.cast_nonneg _) <| hε.trans zero_le_one) hs ht

@[simp] lemma isUniform_singleton :
    G.IsUniform ε {a} {b} (singleton_nonempty a) (singleton_nonempty b) ↔ 0 < ε := by
  refine ⟨IsUniform.pos, fun hε s' hs' t' ht' _ _ hs'' ht'' ↦ ?_⟩
  obtain rfl := hs''.subset_singleton_iff.1 hs'
  obtain rfl := ht''.subset_singleton_iff.1 ht'
  rwa [sub_self, abs_zero]

theorem not_isUniform_zero : ¬G.IsUniform (0 : 𝕜) s t := fun h =>
  (abs_nonneg _).not_gt <| h subset_rfl subset_rfl (by simp) (by simp) hs ht

theorem not_isUniform_iff :
    ¬G.IsUniform ε s t ↔ ∃ s', s' ⊆ s ∧ ∃ t', t' ⊆ t ∧ #s * ε ≤ #s' ∧ #t * ε ≤ #t' ∧
      ∃ (hs' : s'.Nonempty) (ht' : t'.Nonempty), ε ≤ |G.edgeDensity s' t' - G.edgeDensity s t| := by
  unfold IsUniform
  simp only [not_forall, not_lt, exists_prop, Rat.cast_abs, Rat.cast_sub]

variable (G)

/-- An arbitrary pair of subsets witnessing the non-uniformity of `(s, t)`. If `(s, t)` is uniform,
returns `(s, t)`. Witnesses for `(s, t)` and `(t, s)` don't necessarily match. See
`SimpleGraph.nonuniformWitness`. -/
noncomputable def nonuniformWitnesses (ε : 𝕜) (s t : Finset α)
    (hs : s.Nonempty := by first | assumption | fail "uniformity needs a nonempty left set")
    (ht : t.Nonempty := by first | assumption | fail "uniformity needs a nonempty right set") :
    Finset α × Finset α :=
  if h : ¬G.IsUniform ε s t then
    ((not_isUniform_iff.1 h).choose, (not_isUniform_iff.1 h).choose_spec.2.choose)
  else (s, t)

/-- The witnesses of the non-uniformity of `(s, t)` satisfy all the defining conditions. -/
private theorem nonuniformWitnesses_mem (h : ¬G.IsUniform ε s t) :
    (G.nonuniformWitnesses ε s t).1 ⊆ s ∧ (G.nonuniformWitnesses ε s t).2 ⊆ t ∧
      #s * ε ≤ #(G.nonuniformWitnesses ε s t).1 ∧ #t * ε ≤ #(G.nonuniformWitnesses ε s t).2 ∧
      ∃ (hs' : (G.nonuniformWitnesses ε s t).1.Nonempty)
        (ht' : (G.nonuniformWitnesses ε s t).2.Nonempty),
        ε ≤ |G.edgeDensity (G.nonuniformWitnesses ε s t).1 (G.nonuniformWitnesses ε s t).2 -
          G.edgeDensity s t| := by
  rw [nonuniformWitnesses, dite_eq_left h]
  obtain ⟨h₁, h₂⟩ := (not_isUniform_iff.1 h).choose_spec
  obtain ⟨h₃, h₄⟩ := h₂.choose_spec
  exact ⟨h₁, h₃, h₄⟩

theorem left_nonuniformWitnesses_subset (h : ¬G.IsUniform ε s t) :
    (G.nonuniformWitnesses ε s t).1 ⊆ s :=
  (G.nonuniformWitnesses_mem h).1

theorem left_nonuniformWitnesses_card (h : ¬G.IsUniform ε s t) :
    #s * ε ≤ #(G.nonuniformWitnesses ε s t).1 :=
  (G.nonuniformWitnesses_mem h).2.2.1

theorem left_nonuniformWitnesses_nonempty (h : ¬G.IsUniform ε s t) :
    (G.nonuniformWitnesses ε s t).1.Nonempty :=
  (G.nonuniformWitnesses_mem h).2.2.2.2.fst

theorem right_nonuniformWitnesses_subset (h : ¬G.IsUniform ε s t) :
    (G.nonuniformWitnesses ε s t).2 ⊆ t :=
  (G.nonuniformWitnesses_mem h).2.1

theorem right_nonuniformWitnesses_card (h : ¬G.IsUniform ε s t) :
    #t * ε ≤ #(G.nonuniformWitnesses ε s t).2 :=
  (G.nonuniformWitnesses_mem h).2.2.2.1

theorem right_nonuniformWitnesses_nonempty (h : ¬G.IsUniform ε s t) :
    (G.nonuniformWitnesses ε s t).2.Nonempty :=
  (G.nonuniformWitnesses_mem h).2.2.2.2.snd.fst

theorem nonuniformWitnesses_spec (h : ¬G.IsUniform ε s t) :
    ε ≤ |G.edgeDensity (G.nonuniformWitnesses ε s t).1 (G.nonuniformWitnesses ε s t).2
          (G.left_nonuniformWitnesses_nonempty h) (G.right_nonuniformWitnesses_nonempty h) -
        G.edgeDensity s t| :=
  (G.nonuniformWitnesses_mem h).2.2.2.2.snd.snd

open scoped Classical in
/-- Arbitrary witness of non-uniformity. `G.nonuniformWitness ε s t` and
`G.nonuniformWitness ε t s` form a pair of subsets witnessing the non-uniformity of `(s, t)`. If
`(s, t)` is uniform, returns `s`. -/
noncomputable def nonuniformWitness (ε : 𝕜) (s t : Finset α)
    (hs : s.Nonempty := by first | assumption | fail "uniformity needs a nonempty left set")
    (ht : t.Nonempty := by first | assumption | fail "uniformity needs a nonempty right set") :
    Finset α :=
  if WellOrderingRel s t then (G.nonuniformWitnesses ε s t).1 else (G.nonuniformWitnesses ε t s).2

theorem nonuniformWitness_subset (h : ¬G.IsUniform ε s t) : G.nonuniformWitness ε s t ⊆ s := by
  unfold nonuniformWitness
  split_ifs
  · exact G.left_nonuniformWitnesses_subset h
  · exact G.right_nonuniformWitnesses_subset fun i => h i.symm

theorem le_card_nonuniformWitness (h : ¬G.IsUniform ε s t) :
    #s * ε ≤ #(G.nonuniformWitness ε s t) := by
  unfold nonuniformWitness
  split_ifs
  · exact G.left_nonuniformWitnesses_card h
  · exact G.right_nonuniformWitnesses_card fun i => h i.symm

theorem nonuniformWitness_nonempty (h : ¬G.IsUniform ε s t) :
    (G.nonuniformWitness ε s t).Nonempty := by
  unfold nonuniformWitness
  split_ifs
  · exact G.left_nonuniformWitnesses_nonempty h
  · exact G.right_nonuniformWitnesses_nonempty fun i => h i.symm

theorem nonuniformWitness_spec (h₁ : s ≠ t) (h₂ : ¬G.IsUniform ε s t) : ε ≤ |G.edgeDensity
    (G.nonuniformWitness ε s t) (G.nonuniformWitness ε t s) (G.nonuniformWitness_nonempty h₂)
    (G.nonuniformWitness_nonempty fun i => h₂ i.symm) - G.edgeDensity s t| := by
  suffices ∀ (hst : (G.nonuniformWitness ε s t).Nonempty)
      (hts : (G.nonuniformWitness ε t s).Nonempty), ε ≤ |G.edgeDensity (G.nonuniformWitness ε s t)
        (G.nonuniformWitness ε t s) hst hts - G.edgeDensity s t| from this _ _
  unfold nonuniformWitness
  rcases trichotomous_of WellOrderingRel s t with (lt | rfl | gt)
  · rw [ite_eq_left lt, ite_eq_right (asymm lt)]
    exact fun _ _ ↦ G.nonuniformWitnesses_spec h₂
  · cases h₁ rfl
  · rw [ite_eq_right (asymm gt), ite_eq_left gt]
    intro _ _
    rw [edgeDensity_comm, edgeDensity_comm _ s]
    apply G.nonuniformWitnesses_spec fun i => h₂ i.symm

end SimpleGraph

/-! ### Uniform partitions -/


variable [DecidableEq α] {A : Finset α} (P : Finpartition A) (G : SimpleGraph α)
  [DecidableRel G.Adj] {ε δ : 𝕜} {u v : Finset α}

namespace Finpartition

/-- The pairs of parts of a partition `P` which are not `ε`-dense in a graph `G`. Note that we
dismiss the diagonal. We do not care whether `s` is `ε`-dense with itself. The parts of `P` are
nonempty, so the edge density between two of them exists. -/
noncomputable def sparsePairs (ε : 𝕜) : Finset (Finset α × Finset α) :=
  P.parts.offDiag.filter fun uv ↦ ∃ (hu : uv.1 ∈ P.parts) (hv : uv.2 ∈ P.parts),
    G.edgeDensity uv.1 uv.2 (P.nonempty_of_mem_parts hu) (P.nonempty_of_mem_parts hv) < ε

@[simp]
lemma mk_mem_sparsePairs (u v : Finset α) (ε : 𝕜) :
    (u, v) ∈ P.sparsePairs G ε ↔ ∃ (hu : u ∈ P.parts) (hv : v ∈ P.parts), u ≠ v ∧
      G.edgeDensity u v (P.nonempty_of_mem_parts hu) (P.nonempty_of_mem_parts hv) < ε := by
  rw [sparsePairs, mem_filter, mem_offDiag]
  exact ⟨fun ⟨⟨_, _, huv⟩, hu, hv, h⟩ ↦ ⟨hu, hv, huv, h⟩,
    fun ⟨hu, hv, huv, h⟩ ↦ ⟨⟨hu, hv, huv⟩, hu, hv, h⟩⟩

lemma sparsePairs_mono {ε ε' : 𝕜} (h : ε ≤ ε') : P.sparsePairs G ε ⊆ P.sparsePairs G ε' :=
  monotone_filter_right _ fun _ _ ⟨hu, hv, huv⟩ ↦ ⟨hu, hv, huv.trans_le h⟩

/-- The pairs of parts of a partition `P` which are not `ε`-uniform in a graph `G`. Note that we
dismiss the diagonal. We do not care whether `s` is `ε`-uniform with itself. The parts of `P` are
nonempty, so the uniformity of two of them is defined. -/
noncomputable def nonUniforms (ε : 𝕜) : Finset (Finset α × Finset α) :=
  P.parts.offDiag.filter fun uv ↦ ∃ (hu : uv.1 ∈ P.parts) (hv : uv.2 ∈ P.parts),
    ¬G.IsUniform ε uv.1 uv.2 (P.nonempty_of_mem_parts hu) (P.nonempty_of_mem_parts hv)

@[simp] lemma mk_mem_nonUniforms :
    (u, v) ∈ P.nonUniforms G ε ↔ ∃ (hu : u ∈ P.parts) (hv : v ∈ P.parts), u ≠ v ∧
      ¬G.IsUniform ε u v (P.nonempty_of_mem_parts hu) (P.nonempty_of_mem_parts hv) := by
  rw [nonUniforms, mem_filter, mem_offDiag]
  exact ⟨fun ⟨⟨_, _, huv⟩, hu, hv, h⟩ ↦ ⟨hu, hv, huv, h⟩,
    fun ⟨hu, hv, huv, h⟩ ↦ ⟨⟨hu, hv, huv⟩, hu, hv, h⟩⟩

theorem nonUniforms_mono {ε ε' : 𝕜} (h : ε ≤ ε') : P.nonUniforms G ε' ⊆ P.nonUniforms G ε :=
  monotone_filter_right _ fun _ _ ⟨hu, hv, huv⟩ ↦
    ⟨hu, hv, mt (SimpleGraph.IsUniform.mono h) huv⟩

theorem nonUniforms_bot (hε : 0 < ε) : (⊥ : Finpartition A).nonUniforms G ε = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  rintro ⟨u, v⟩ huv
  obtain ⟨hu, hv, -, h⟩ := (mk_mem_nonUniforms _ _).1 huv
  rw [parts_bot, mem_map] at hu hv
  obtain ⟨x, -, rfl⟩ := hu
  obtain ⟨y, -, rfl⟩ := hv
  exact h (SimpleGraph.isUniform_singleton.2 hε)

/-- A finpartition of a graph's vertex set is `ε`-uniform (aka `ε`-regular) iff the proportion of
its pairs of parts that are not `ε`-uniform is at most `ε`. -/
def IsUniform (ε : 𝕜) : Prop :=
  (#(P.nonUniforms G ε) : 𝕜) ≤ (#P.parts * (#P.parts - 1) : ℕ) * ε

lemma bot_isUniform (hε : 0 < ε) : (⊥ : Finpartition A).IsUniform G ε := by
  rw [Finpartition.IsUniform, Finpartition.card_bot, nonUniforms_bot _ hε, Finset.card_empty,
    Nat.cast_zero]
  positivity

lemma isUniform_one : P.IsUniform G (1 : 𝕜) := by
  rw [IsUniform, mul_one, Nat.cast_le]
  refine (card_filter_le _ _).trans ?_
  rw [offDiag_card, Nat.mul_sub_left_distrib, mul_one]

variable {P G}

theorem IsUniform.mono {ε ε' : 𝕜} (hP : P.IsUniform G ε) (h : ε ≤ ε') : P.IsUniform G ε' :=
  ((Nat.cast_le.2 <| card_le_card <| P.nonUniforms_mono G h).trans hP).trans <| by gcongr

theorem isUniformOfEmpty (hP : P.parts = ∅) : P.IsUniform G ε := by
  simp [IsUniform, hP, nonUniforms]

theorem nonempty_of_not_uniform (h : ¬P.IsUniform G ε) : P.parts.Nonempty :=
  nonempty_of_ne_empty fun h₁ => h <| isUniformOfEmpty h₁

variable (P G ε) (s : Finset α)

/-- A choice of witnesses of non-uniformity among the parts of a finpartition. -/
noncomputable def nonuniformWitnesses
    (hs : s.Nonempty := by first | assumption | fail "uniformity needs a nonempty left set") :
    Finset (Finset α) :=
  {t ∈ P.parts.attach | s ≠ t.1 ∧ ¬G.IsUniform ε s t.1 hs (P.nonempty_of_mem_parts t.2)}.image
    fun t ↦ G.nonuniformWitness ε s t.1 hs (P.nonempty_of_mem_parts t.2)

variable {P G ε s} {hs : s.Nonempty} {t : Finset α}

lemma card_nonuniformWitnesses_le :
    #(P.nonuniformWitnesses G ε s hs) ≤
      #{t ∈ P.parts.attach | s ≠ t.1 ∧ ¬G.IsUniform ε s t.1 hs (P.nonempty_of_mem_parts t.2)} :=
  card_image_le

theorem nonuniformWitness_mem_nonuniformWitnesses {ht' : t.Nonempty} (h : ¬G.IsUniform ε s t)
    (ht : t ∈ P.parts) (hst : s ≠ t) :
    G.nonuniformWitness ε s t ∈ P.nonuniformWitnesses G ε s :=
  mem_image.2 ⟨⟨t, ht⟩, mem_filter.2 ⟨mem_attach _ _, hst, h⟩, rfl⟩

/-! ### Equipartitions -/

open SimpleGraph in
lemma IsEquipartition.card_interedges_sparsePairs_le' (hP : P.IsEquipartition)
    (hε : 0 ≤ ε) :
    #((P.sparsePairs G ε).biUnion fun (U, V) ↦ G.interedges U V) ≤ ε * (#A + #P.parts) ^ 2 := by
  calc
    _ ≤ ∑ UV ∈ P.sparsePairs G ε, (#(G.interedges UV.1 UV.2) : 𝕜) := mod_cast card_biUnion_le
    _ ≤ ∑ UV ∈ P.sparsePairs G ε, ε * (#UV.1 * #UV.2) := ?_
    _ ≤ ∑ UV ∈ P.parts.offDiag, ε * (#UV.1 * #UV.2) := by gcongr; apply filter_subset
    _ = ε * ∑ UV ∈ P.parts.offDiag, (#UV.1 * #UV.2 : 𝕜) := (mul_sum _ _ _).symm
    _ ≤ _ := ?_
  · gcongr with ⟨U, V⟩ hUV
    obtain ⟨hU, hV, -, hUV⟩ := (P.mk_mem_sparsePairs G U V ε).1 hUV
    rw [edgeDensity_def] at hUV
    push_cast at hUV
    refine ((div_lt_iff₀ ?_).1 hUV).le
    exact mul_pos (Nat.cast_pos.2 (P.nonempty_of_mem_parts hU).card_pos)
      (Nat.cast_pos.2 (P.nonempty_of_mem_parts hV).card_pos)
  norm_cast
  gcongr
  by_cases hk : #P.parts = 0
  · simp [card_eq_zero.mp hk]
  let q := Nat.euclideanDiv #A #P.parts hk
  calc
    (_ : ℕ) ≤ _ := sum_le_card_nsmul P.parts.offDiag (fun i ↦ #i.1 * #i.2)
            ((q + 1) ^ 2 : ℕ) ?_
    _ ≤ (#P.parts * (q) + #P.parts) ^ 2 := ?_
    _ ≤ _ := by
      gcongr
      simpa only [q, Nat.euclideanDiv_eq_core] using Nat.mul_div_le #A #P.parts
  · simp only [Prod.forall, and_imp, mem_offDiag, sq]
    rintro U V hU hV -
    exact_mod_cast Nat.mul_le_mul (hP.card_part_le_average_add_one hU)
      (hP.card_part_le_average_add_one hV)
  · rw [smul_eq_mul, offDiag_card, Nat.mul_sub_right_distrib, ← sq, ← mul_pow, mul_add_one (α := ℕ)]
    exact Nat.sub_le _ _

lemma IsEquipartition.card_interedges_sparsePairs_le (hP : P.IsEquipartition) (hε : 0 ≤ ε) :
    #((P.sparsePairs G ε).biUnion fun (U, V) ↦ G.interedges U V) ≤ 4 * ε * #A ^ 2 := by
  calc
    _ ≤ _ := hP.card_interedges_sparsePairs_le' hε
    _ ≤ ε * (#A + #A) ^ 2 := by gcongr; exact P.card_parts_le_card
    _ = _ := by ring

private lemma aux {i j : ℕ} (hj : 0 < j) :
    j * (j - 1) * (Nat.euclideanDiv i j hj.ne' + 1) ^ 2 < (i + j) ^ 2 := by
  rw [Nat.euclideanDiv_eq_core]
  have : j * (j - 1) < j ^ 2 := by
    rw [sq]; exact Nat.mul_lt_mul_of_pos_left (Nat.sub_lt hj zero_lt_one) hj
  apply (Nat.mul_lt_mul_of_pos_right this <| pow_pos Nat.succ_pos' _).trans_le
  rw [← mul_pow, Nat.mul_succ]
  gcongr
  apply Nat.mul_div_le

lemma IsEquipartition.card_biUnion_offDiag_le' {hPUnit : IsUnit (#P.parts : 𝕜)}
    (hP : P.IsEquipartition) :
    (#(P.parts.biUnion offDiag) : 𝕜) ≤ (#A : 𝕜) * (#A + #P.parts) / (#P.parts : 𝕜) := by
  let q := Nat.euclideanDiv #A #P.parts (Nat.cast_ne_zero.mp hPUnit.ne_zero)
  have hq : #P.parts * q ≤ #A := by
    simpa only [q, Nat.euclideanDiv_eq_core] using Nat.mul_div_le #A #P.parts
  calc
    _ ≤ (#P.parts : 𝕜) * ((q : 𝕜) * ↑(q + 1)) :=
        mod_cast card_biUnion_le_card_mul _ _ _ fun U hU ↦ ?_
    _ = #P.parts * (q : 𝕜) * ↑(q + 1) := by rw [mul_assoc]
    _ ≤ (#A : 𝕜) * ((#A : 𝕜) / (#P.parts : 𝕜) + 1) :=
        mul_le_mul (mod_cast hq) ?_ (by positivity) (by positivity)
    _ = _ := by rw [← div_add_same, mul_div_assoc₀]
  · simpa [q] using (Nat.cast_div_le (m := #A) (n := #P.parts) (hn := hPUnit))
  suffices (#U - 1) * #U ≤ q * (q + 1) by
    rwa [Nat.mul_sub_right_distrib, one_mul, ← offDiag_card] at this
  have := hP.card_part_le_average_add_one hU
  refine Nat.mul_le_mul ((Nat.sub_le_sub_right this 1).trans ?_) this
  simp [q]

lemma IsEquipartition.card_biUnion_offDiag_le (hε : 0 < ε) (hP : P.IsEquipartition)
    (hP' : 4 / ε ≤ #P.parts) : #(P.parts.biUnion offDiag) ≤ ε / 2 * #A ^ 2 := by
  obtain rfl | hA : A = ⊥ ∨ _ := A.eq_empty_or_nonempty
  · simp [Subsingleton.elim P ⊥]
  have hPpos : (0 : 𝕜) < #P.parts := Nat.cast_pos.2 (P.parts_nonempty hA.ne_empty).card_pos
  apply (hP.card_biUnion_offDiag_le' (hPUnit := hPpos.ne'.isUnit)).trans
  rw [div_le_iff₀ hPpos]
  have : (#A : 𝕜) + #P.parts ≤ 2 * #A := by
    rw [two_mul]; gcongr; exact P.card_parts_le_card
  refine (mul_le_mul_of_nonneg_left this <| by positivity).trans ?_
  suffices 1 ≤ ε / 4 * #P.parts by
    rw [mul_left_comm, ← sq]
    convert! mul_le_mul_of_nonneg_left this (mul_nonneg zero_le_two <| sq_nonneg (#A : 𝕜)) using 1
      <;> ring
  rwa [← div_le_iff₀', one_div_div₀]
  positivity

lemma IsEquipartition.sum_nonUniforms_lt' (hA : A.Nonempty) (hε : 0 < ε) (hP : P.IsEquipartition)
    (hG : P.IsUniform G ε) :
    ∑ i ∈ P.nonUniforms G ε, (#i.1 * #i.2 : 𝕜) < ε * (#A + #P.parts) ^ 2 := by
  let q := Nat.euclideanDiv #A #P.parts (P.parts_nonempty hA.ne_empty).card_pos.ne'
  calc
    _ ≤ #(P.nonUniforms G ε) • (↑(q + 1) : 𝕜) ^ 2 :=
      sum_le_card_nsmul _ _ _ ?_
    _ = _ := nsmul_eq_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right hG <| by positivity
    _ < _ := ?_
  · simp only [Prod.forall, Finpartition.mk_mem_nonUniforms, forall_exists_index, and_imp]
    rintro U V hU hV - -
    rw [sq, ← Nat.cast_mul, ← Nat.cast_mul, Nat.cast_le]
    exact Nat.mul_le_mul (hP.card_part_le_average_add_one hU)
      (hP.card_part_le_average_add_one hV)
  · rw [mul_right_comm _ ε, mul_comm ε]
    gcongr
    norm_cast
    exact aux (P.parts_nonempty hA.ne_empty).card_pos

lemma IsEquipartition.sum_nonUniforms_lt (hA : A.Nonempty) (hε : 0 < ε) (hP : P.IsEquipartition)
    (hG : P.IsUniform G ε) :
    #((P.nonUniforms G ε).biUnion fun (U, V) ↦ U ×ˢ V) < 4 * ε * #A ^ 2 := by
  calc
    _ ≤ ∑ i ∈ P.nonUniforms G ε, (#i.1 * #i.2 : 𝕜) := by
        norm_cast; simp_rw [← card_product]; exact card_biUnion_le
    _ < _ := hP.sum_nonUniforms_lt' hA hε hG
    _ ≤ ε * (#A + #A) ^ 2 := by gcongr; exact P.card_parts_le_card
    _ = _ := by ring

end Finpartition

/-! ### Reduced graph -/

namespace SimpleGraph

/-- The reduction of the graph `G` along partition `P` has edges between `ε`-uniform pairs of parts
that have edge density at least `δ`. -/
@[simps] def regularityReduced (ε δ : 𝕜) : SimpleGraph α where
  Adj a b := G.Adj a b ∧ ∃ U, ∃ hU : U ∈ P.parts, ∃ V, ∃ hV : V ∈ P.parts, a ∈ U ∧ b ∈ V ∧
    U ≠ V ∧ G.IsUniform ε U V (P.nonempty_of_mem_parts hU) (P.nonempty_of_mem_parts hV) ∧
    δ ≤ G.edgeDensity U V (P.nonempty_of_mem_parts hU) (P.nonempty_of_mem_parts hV)
  symm.symm a b := by
    rintro ⟨ab, U, UP, V, VP, xU, yV, UV, GUV, εUV⟩
    refine ⟨ab.symm, V, VP, U, UP, yV, xU, UV.symm, GUV.symm, ?_⟩
    rwa [edgeDensity_comm]

noncomputable instance regularityReduced.instDecidableRel_adj :
    DecidableRel (G.regularityReduced P ε δ).Adj :=
  inferInstanceAs <| DecidableRel (mk _ _).Adj

variable {G P}

lemma regularityReduced_le : G.regularityReduced P ε δ ≤ G := fun _ _ ↦ And.left

lemma regularityReduced_mono {ε₁ ε₂ : 𝕜} (hε : ε₁ ≤ ε₂) :
    G.regularityReduced P ε₁ δ ≤ G.regularityReduced P ε₂ δ :=
  fun _a _b ⟨hab, U, hU, V, hV, ha, hb, hUV, hGε, hGδ⟩ ↦
    ⟨hab, U, hU, V, hV, ha, hb, hUV, hGε.mono hε, hGδ⟩

lemma regularityReduced_anti {δ₁ δ₂ : 𝕜} (hδ : δ₁ ≤ δ₂) :
    G.regularityReduced P ε δ₂ ≤ G.regularityReduced P ε δ₁ :=
  fun _a _b ⟨hab, U, hU, V, hV, ha, hb, hUV, hUVε, hUVδ⟩ ↦
    ⟨hab, U, hU, V, hV, ha, hb, hUV, hUVε, hδ.trans hUVδ⟩

lemma unreduced_edges_subset :
    (A ×ˢ A).filter (fun (x, y) ↦ G.Adj x y ∧ ¬ (G.regularityReduced P (ε / 8) (ε / 4)).Adj x y) ⊆
      (P.nonUniforms G (ε / 8)).biUnion (fun (U, V) ↦ U ×ˢ V) ∪ P.parts.biUnion offDiag ∪
        (P.sparsePairs G (ε / 4)).biUnion fun (U, V) ↦ G.interedges U V := by
  rintro ⟨x, y⟩
  simp only [mem_filter, regularityReduced_adj, not_and, not_exists,
    not_le, mem_biUnion, mem_union, mem_product, Prod.exists, mem_offDiag, and_imp,
    or_assoc, and_assoc, P.mk_mem_nonUniforms, Finpartition.mk_mem_sparsePairs, mem_interedges_iff]
  intro hx hy h h'
  replace h' := h' h
  obtain ⟨U, hU, hx⟩ := P.exists_mem hx
  obtain ⟨V, hV, hy⟩ := P.exists_mem hy
  obtain rfl | hUV := eq_or_ne U V
  · exact Or.inr (Or.inl ⟨U, hU, hx, hy, G.ne_of_adj h⟩)
  by_cases h₂ : G.IsUniform (ε / 8) U V (P.nonempty_of_mem_parts hU) (P.nonempty_of_mem_parts hV)
  · exact Or.inr <| Or.inr ⟨U, V, ⟨hU, hV, hUV, h' _ hU _ hV hx hy hUV h₂⟩, hx, hy, h⟩
  · exact Or.inl ⟨U, V, ⟨hU, hV, hUV, h₂⟩, hx, hy⟩

end SimpleGraph
