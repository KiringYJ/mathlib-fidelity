import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Combinatorics.SimpleGraph.Girth

/-!
# Strict graph distance, diameter, and girth

These tests ensure that the natural-valued distance, diameter, and girth of a simple graph are
defined exactly where the extended invariants are finite, so that unreachable pairs, disconnected
or unbounded graphs, and acyclic graphs no longer receive the value `0`.
-/

open SimpleGraph

/-- info: Unknown constant `SimpleGraph.dist_eq_zero_of_not_reachable` -/
#guard_msgs in
#check_failure SimpleGraph.dist_eq_zero_of_not_reachable

/-- info: Unknown constant `SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable` -/
#guard_msgs in
#check_failure SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable

/-- info: Unknown constant `SimpleGraph.Reachable.dist_triangle_left` -/
#guard_msgs in
#check_failure SimpleGraph.Reachable.dist_triangle_left

/-- info: Unknown constant `SimpleGraph.girth_eq_zero` -/
#guard_msgs in
#check_failure SimpleGraph.girth_eq_zero

/-- info: Unknown constant `SimpleGraph.diam_eq_zero_of_not_connected` -/
#guard_msgs in
#check_failure SimpleGraph.diam_eq_zero_of_not_connected

/-- info: Unknown constant `SimpleGraph.connected_iff_diam_ne_zero` -/
#guard_msgs in
#check_failure SimpleGraph.connected_iff_diam_ne_zero

/-! The natural-valued invariants need their finiteness evidence. -/

/--
error: Type mismatch
  G.dist u v
has type
  G.Reachable u v → ℕ
but is expected to have type
  ℕ
-/
#guard_msgs in
noncomputable example (G : SimpleGraph ℕ) (u v : ℕ) : ℕ := G.dist u v

/--
error: Type mismatch
  G.girth
has type
  ¬G.IsAcyclic → ℕ
but is expected to have type
  ℕ
-/
#guard_msgs in
noncomputable example (G : SimpleGraph ℕ) : ℕ := G.girth

/--
error: Type mismatch
  G.diam
has type
  G.ediam ≠ ⊤ → ℕ
but is expected to have type
  ℕ
-/
#guard_msgs in
noncomputable example (G : SimpleGraph ℕ) : ℕ := G.diam

/-! Two vertices of the empty graph on two vertices are not reachable from each other: their
extended distance is `⊤`, and the graph has extended diameter `⊤`. Their former distance and the
former diameter were `0`, as for a single vertex. -/

example : ¬(⊥ : SimpleGraph (Fin 2)).Reachable 0 1 := by
  simp [reachable_bot]

example : (⊥ : SimpleGraph (Fin 2)).edist 0 1 = ⊤ :=
  edist_bot_of_ne (by decide)

example : (⊥ : SimpleGraph (Fin 2)).ediam = ⊤ := ediam_bot

/-! An acyclic graph has extended girth `⊤`; its former girth was `0`. -/

example : (⊥ : SimpleGraph ℕ).egirth = ⊤ := egirth_bot

example : (⊥ : SimpleGraph ℕ).IsAcyclic := isAcyclic_bot

/-! On their domains, the invariants take their expected values. -/

example (h : (⊤ : SimpleGraph (Fin 3)).Reachable 0 1) :
    (⊤ : SimpleGraph (Fin 3)).dist 0 1 h = 1 := by
  simp

example (h : (⊤ : SimpleGraph (Fin 3)).ediam ≠ ⊤) : (⊤ : SimpleGraph (Fin 3)).diam h = 1 := by
  simp

example (h : ¬(⊤ : SimpleGraph (Fin 3)).IsAcyclic) : (⊤ : SimpleGraph (Fin 3)).girth h = 3 :=
  girth_top (by simp) h

/-! The triangle inequality takes both reachabilities. -/

example {V : Type*} (G : SimpleGraph V) {u v w : V} (huv : G.Reachable u v)
    (hvw : G.Reachable v w) :
    G.dist u w (huv.trans hvw) ≤ G.dist u v huv + G.dist v w hvw :=
  dist_triangle huv hvw

/-! A tree is still two-colored by the parity of the distance to a vertex. -/

example {V : Type*} (G : SimpleGraph V) (hG : G.IsTree) : G.IsBipartite := hG.isBipartite
