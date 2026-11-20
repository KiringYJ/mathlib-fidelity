/-
Copyright (c) 2025 Mitchell Horner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Horner
-/
module

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
public import Mathlib.Data.Nat.Choose.Cast

import Mathlib.Tactic.Bound
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Turán density

This file defines the **Turán density** of a simple graph.

## Main definitions

* `SimpleGraph.turanDensity H` is the **Turán density** of the simple graph `H`, defined as the
  infimum of `extremalNumber n H / n.choose 2` over vertex counts `n ≥ 2`.

* `SimpleGraph.tendsto_turanDensity` proves that the extremal edge ratios converge to the density.

* `SimpleGraph.isEquivalent_extremalNumber` is the proof that `extremalNumber n H` is
  asymptotically equivalent to `turanDensity H * n.choose 2` as `n` approaches `∞`.

* `SimpleGraph.isContained_of_card_edgeFinset`: for positive `ε` and sufficiently large `n`,
  graphs on `n` vertices with at least `(turanDensity H + ε) * n.choose 2` edges contain `H`.
-/

@[expose] public section


open Asymptotics Filter Finset Fintype

open scoped Topology

namespace SimpleGraph

variable {W : Type*}

local notation "VertexCounts" => Subtype (fun n : ℕ ↦ n ∈ Set.Ici 2)

lemma turanRatio_denominator_pos (n : VertexCounts) : 0 < (n.val.choose 2 : ℝ) := by
  exact_mod_cast Nat.choose_pos n.property

/-- The extremal edge ratio on vertex counts with positive denominator. -/
noncomputable def turanRatio (H : SimpleGraph W) (n : VertexCounts) : ℝ :=
  Checked.div (extremalNumber n.val H : ℝ) (n.val.choose 2 : ℝ)
    (turanRatio_denominator_pos n).ne'.isUnit

private lemma turanRatio_nonneg (H : SimpleGraph W) (n : VertexCounts) : 0 ≤ turanRatio H n :=
  div_nonneg (Nat.cast_nonneg _) (turanRatio_denominator_pos n).le

private lemma turanRatio_mul (H : SimpleGraph W) (n : VertexCounts) :
    turanRatio H n * (n.val.choose 2 : ℝ) = (extremalNumber n.val H : ℝ) :=
  div_mul_cancel₀ _

private lemma turan_edge_count {H : SimpleGraph W} {n : ℕ}
    (G : SimpleGraph (Fin (n + 1))) [DecidableRel G.Adj] (hf : H.Free G) :
    (n - 1) * #G.edgeFinset ≤ (n + 1) * extremalNumber n H := by
  conv_rhs => rw [← Fintype.card_fin (n + 1), ← card_univ]
  rw [mul_comm (n - 1)]
  -- Count the incidences of a vertex outside an edge.
  apply card_nsmul_le_card_nsmul' (r := fun v e ↦ v ∉ e)
  · intro e he
    simp_rw [← Sym2.mem_toFinset, bipartiteBelow, filter_not, filter_mem_eq_inter, univ_inter,
      ← compl_eq_univ_sdiff, card_compl, Fintype.card_fin, card_toFinset_mem_edgeFinset ⟨e, he⟩,
      Nat.cast_id, Nat.reduceSubDiff, le_refl]
  · intro v _
    simpa [edgeFinset_deleteIncidenceSet_eq_filter]
      using! card_edgeFinset_deleteIncidenceSet_le_extremalNumber hf v

private lemma turanRatio_step (H : SimpleGraph W) (k : ℕ) :
    turanRatio H ⟨k + 3, by change 2 ≤ k + 3; omega⟩ ≤
      turanRatio H ⟨k + 2, by change 2 ≤ k + 2; omega⟩ := by
  let i : VertexCounts := ⟨k + 2, by change 2 ≤ k + 2; omega⟩
  let j : VertexCounts := ⟨k + 3, by change 2 ≤ k + 3; omega⟩
  change turanRatio H j ≤ turanRatio H i
  apply (div_le_iff₀ (turanRatio_denominator_pos j)).2
  change (extremalNumber (k + 3) H : ℝ) ≤ turanRatio H i * ((k + 3).choose 2 : ℝ)
  conv_lhs => rw [← Fintype.card_fin (k + 3)]
  rw [extremalNumber_le_iff_of_nonneg H (mul_nonneg (turanRatio_nonneg H i) (by positivity))]
  intro G _ hf
  have hc := turan_edge_count (n := k + 2) G hf
  rw [show k + 2 - 1 = k + 1 by omega] at hc
  have he : ((k : ℝ) + 1) * (#G.edgeFinset : ℝ) ≤
      ((k : ℝ) + 3) * (extremalNumber (k + 2) H : ℝ) := by
    exact_mod_cast hc
  have hs : ((k : ℝ) + 1) * ((k + 3).choose 2 : ℝ) =
      ((k : ℝ) + 3) * ((k + 2).choose 2 : ℝ) := by
    simp only [Nat.cast_choose_two, Nat.cast_add, Nat.cast_ofNat, div_eq_mul_inv₀]
    ring
  have hr : turanRatio H i * ((k + 2).choose 2 : ℝ) = (extremalNumber (k + 2) H : ℝ) :=
    turanRatio_mul H i
  apply (mul_le_mul_iff_right₀ (show 0 < (k : ℝ) + 1 by positivity)).mp
  calc
    ((k : ℝ) + 1) * (#G.edgeFinset : ℝ) ≤
        ((k : ℝ) + 3) * (extremalNumber (k + 2) H : ℝ) := he
    _ = turanRatio H i * (((k : ℝ) + 3) * ((k + 2).choose 2 : ℝ)) := by rw [← hr]; ring
    _ = ((k : ℝ) + 1) * (turanRatio H i * ((k + 3).choose 2 : ℝ)) := by rw [← hs]; ring

lemma antitone_turanRatio (H : SimpleGraph W) : Antitone (turanRatio H) := by
  have hs : Antitone (fun k : ℕ ↦ turanRatio H ⟨k + 2, by change 2 ≤ k + 2; omega⟩) :=
    antitone_nat_of_succ_le (fun k ↦ turanRatio_step H k)
  rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
  change 2 ≤ a at ha
  change 2 ≤ b at hb
  change a ≤ b at hab
  obtain ⟨u, rfl⟩ : ∃ u, a = u + 2 := ⟨a - 2, by omega⟩
  obtain ⟨v, rfl⟩ : ∃ v, b = v + 2 := ⟨b - 2, by omega⟩
  exact hs (show u ≤ v by omega)

private lemma turanRatio_bddBelow (H : SimpleGraph W) : BddBelow (Set.range (turanRatio H)) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact turanRatio_nonneg H n

/-- The **Turán density** of a simple graph `H` is the limit of its extremal edge ratios as the
number of vertices tends to infinity. -/
noncomputable def turanDensity (H : SimpleGraph W) := sInf (Set.range (turanRatio H))

theorem turanDensity_eq_csInf (H : SimpleGraph W) :
    turanDensity H = sInf (Set.range (turanRatio H)) := rfl

theorem isGLB_turanDensity (H : SimpleGraph W) :
    IsGLB (Set.range (turanRatio H)) (turanDensity H) := by
  let : Nonempty VertexCounts := ⟨⟨2, Set.mem_Ici.mpr le_rfl⟩⟩
  exact isGLB_csInf (Set.range_nonempty (turanRatio H)) (turanRatio_bddBelow H)

/-- The extremal edge ratios converge to the Turán density. -/
theorem tendsto_turanDensity (H : SimpleGraph W) :
    Tendsto (turanRatio H) atTop (𝓝 (turanDensity H)) := by
  rw [turanDensity, sInf_range]
  exact tendsto_atTop_ciInf (antitone_turanRatio H) (turanRatio_bddBelow H)

/-- The extremal edge count is asymptotic to the Turán density times `n.choose 2`. -/
theorem isEquivalent_extremalNumber {H : SimpleGraph W} (h : turanDensity H ≠ 0) :
    (fun n ↦ (extremalNumber n H : ℝ)) ~[atTop] (fun n ↦ (turanDensity H * n.choose 2 : ℝ)) := by
  rw [← map_val_Ici_atTop (2 : ℕ), isEquivalent_map]
  apply isLittleO_iff.mpr
  intro c hc
  have ht := (Metric.tendsto_nhds.mp (tendsto_turanDensity H))
    (c * |turanDensity H|) (mul_pos hc (abs_pos.mpr h))
  filter_upwards [ht] with n hn
  change ‖(extremalNumber n.val H : ℝ) - turanDensity H * (n.val.choose 2 : ℝ)‖ ≤
    c * ‖turanDensity H * (n.val.choose 2 : ℝ)‖
  rw [← turanRatio_mul H n, ← sub_mul]
  simpa only [Real.dist_eq, Real.norm_eq_abs, abs_mul, mul_assoc] using
    mul_le_mul_of_nonneg_right hn.le (abs_nonneg (n.val.choose 2 : ℝ))

/-- For every positive `ε`, a graph with edge density at least `turanDensity H + ε`
contains `H` once its number of vertices is sufficiently large. -/
theorem eventually_isContained_of_card_edgeFinset (H : SimpleGraph W) {ε : ℝ} (hε_pos : 0 < ε) :
    ∀ᶠ n in atTop, ∀ {G : SimpleGraph (Fin n)} [DecidableRel G.Adj],
      #G.edgeFinset ≥ (turanDensity H + ε) * n.choose 2 → H ⊑ G := by
  have ht := (tendsto_order.mp (tendsto_turanDensity H)).2
    (turanDensity H + ε) (lt_add_of_pos_right _ hε_pos)
  obtain ⟨N, hN⟩ := eventually_atTop.mp ht
  filter_upwards [eventually_ge_atTop N.val] with n hn
  intro G _ hG
  by_contra hfree
  have hf : H.Free G := hfree
  let i : VertexCounts := ⟨n, N.property.trans hn⟩
  have hlt := mul_lt_mul_of_pos_right (hN i hn) (turanRatio_denominator_pos i)
  rw [turanRatio_mul H i] at hlt
  have hedges : #G.edgeFinset ≤ extremalNumber n H := by
    simpa only [Fintype.card_fin] using card_edgeFinset_le_extremalNumber hf
  have hedgesR : (#G.edgeFinset : ℝ) ≤ (extremalNumber n H : ℝ) := by
    exact_mod_cast hedges
  exact (not_lt_of_ge (hG.trans hedgesR)) hlt

open scoped Classical in
/-- A vertex count beyond which every graph with edge density at least `turanDensity H + ε`
contains `H`. -/
noncomputable abbrev turanDensityConst (H : SimpleGraph W) (ε : ℝ) (hε : 0 < ε) : ℕ :=
  Nat.find (eventually_atTop.mp (eventually_isContained_of_card_edgeFinset H hε))

/-- Simple graphs above the vertex threshold and with edge density at least `turanDensity H + ε`
contain `H`. -/
theorem isContained_of_card_edgeFinset (H : SimpleGraph W) {ε : ℝ} (hε_pos : 0 < ε)
    {V : Type*} [Fintype V] (h_verts : card V ≥ turanDensityConst H ε hε_pos)
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    #G.edgeFinset ≥ (turanDensity H + ε) * (card V).choose 2 → H ⊑ G := by
  classical
  rw [(G.overFinIso rfl).card_edgeFinset_eq, isContained_congr Iso.refl (G.overFinIso rfl)]
  exact Nat.find_spec (eventually_atTop.mp (eventually_isContained_of_card_edgeFinset H hε_pos))
    (card V) h_verts

end SimpleGraph
