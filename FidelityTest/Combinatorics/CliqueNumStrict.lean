import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

/-!
# Strict clique and independence numbers

These tests ensure that the clique number and the independence number are suprema in `ℕ∞` of the
sizes of the finite cliques and independent sets, so that a graph with arbitrarily large finite
cliques has clique number `⊤` rather than the value `0` of an unbounded natural supremum.
-/

open Finset

namespace SimpleGraph

/-! The former statements that held through the fallback are removed or renamed. -/

/-- info: Unknown constant `SimpleGraph.exists_isNClique_cliqueNum` -/
#guard_msgs in
#check_failure SimpleGraph.exists_isNClique_cliqueNum

/-- info: Unknown constant `SimpleGraph.cliqueNum_ne_zero_of_finite` -/
#guard_msgs in
#check_failure SimpleGraph.cliqueNum_ne_zero_of_finite

/-- info: Unknown constant `SimpleGraph.exists_isNIndepSet_indepNum` -/
#guard_msgs in
#check_failure SimpleGraph.exists_isNIndepSet_indepNum

/-! The complete graph on `ℕ` has arbitrarily large finite cliques. -/

example : (⊤ : SimpleGraph ℕ).cliqueNum = ⊤ := by simp

example : (⊤ : SimpleGraph ℕ).cliqueNum ≠ 0 := by simp

example : (⊥ : SimpleGraph ℕ).indepNum = ⊤ := by
  rw [← cliqueNum_compl, compl_bot, cliqueNum_top, ENat.card_eq_top_of_infinite]

/-- The complete graph on `ℕ` with the edge between `0` and `1` removed. -/
private def nearlyComplete : SimpleGraph ℕ := ⊤ \ fromEdgeSet {s(0, 1)}

private lemma nearlyComplete_cliqueNum : nearlyComplete.cliqueNum = ⊤ := by
  rw [cliqueNum_eq_top_iff]
  intro n hn
  refine hn ((range n).map (addLeftEmbedding 2)) ⟨?_, by simp⟩
  intro a ha b hb hab
  simp only [coe_map, Set.mem_image, mem_coe, mem_range, addLeftEmbedding_apply] at ha hb
  obtain ⟨a, -, rfl⟩ := ha
  obtain ⟨b, -, rfl⟩ := hb
  simp only [nearlyComplete, sdiff_adj, top_adj, fromEdgeSet_adj, Set.mem_singleton_iff,
    Sym2.eq_iff]
  lia

/-- Without finitely many vertices, a clique number at least the number of vertices does not make
the graph complete. -/
example : ENat.card ℕ ≤ nearlyComplete.cliqueNum ∧ nearlyComplete ≠ ⊤ := by
  refine ⟨by simp [nearlyComplete_cliqueNum], fun h ↦ ?_⟩
  have : nearlyComplete.Adj 0 1 := by rw [h]; simp
  simp [nearlyComplete] at this

/-! Finite graphs have finite clique numbers, which are attained. -/

example (G : SimpleGraph (Fin 5)) : G.cliqueNum ≠ ⊤ := G.cliqueNum_ne_top

example {α : Type*} {G : SimpleGraph α} {n : ℕ} (h : G.cliqueNum = n) : ∃ s, G.IsNClique n s :=
  exists_isNClique_of_cliqueNum_eq h

example : (⊥ : SimpleGraph ℕ).cliqueNum = 1 := by simp

example : (⊤ : SimpleGraph (Fin 4)).cliqueNum = 4 := by simp

example {α : Type*} {G : SimpleGraph α} {n : ℕ} (h : G.indepNum = n) :
    ∃ s, G.IsNIndepSet n s :=
  exists_isNIndepSet_of_indepNum_eq h

example {α : Type*} (G : SimpleGraph α) : G.cliqueNum ≤ G.chromaticNumber :=
  G.cliqueNum_le_chromaticNumber

end SimpleGraph
