/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Vincent Beffara, Rida Hamadani, Nelson Spence
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.ENat.Lattice

/-!
# Graph metric

This module defines the `SimpleGraph.edist` function, which takes pairs of vertices to the length of
the shortest walk between them, or `⊤` if they are disconnected. It also defines `SimpleGraph.dist`,
the `ℕ`-valued distance between vertices that are reachable from each other, and
`SimpleGraph.ball`, the open ball in the graph extended metric.

## Main definitions

- `SimpleGraph.edist` is the graph extended metric.
- `SimpleGraph.dist` is the graph metric on pairs of vertices reachable from each other.
- `SimpleGraph.ball` is the open ball of a given radius around a vertex.

## TODO

- Provide an additional computable version of `SimpleGraph.dist`
  for when `G` is connected.

- When directed graphs exist, a directed notion of distance,
  likely `ENat`-valued.

## Tags

graph metric, distance, ball

-/

@[expose] public section

assert_not_exists Field

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-! ## Metric -/

section edist

/--
The extended distance between two vertices is the length of the shortest walk between them.
It is `⊤` if no such walk exists.
-/
noncomputable def edist (u v : V) : ℕ∞ :=
  ⨅ w : G.Walk u v, w.length

variable {G} {u v w : V}

theorem edist_eq_sInf : G.edist u v = sInf (Set.range fun w : G.Walk u v ↦ (w.length : ℕ∞)) := rfl

protected theorem Reachable.exists_walk_length_eq_edist (hr : G.Reachable u v) :
    ∃ p : G.Walk u v, p.length = G.edist u v :=
  csInf_mem <| Set.range_nonempty_iff_nonempty.mpr hr

protected theorem Connected.exists_walk_length_eq_edist (hconn : G.Connected) (u v : V) :
    ∃ p : G.Walk u v, p.length = G.edist u v :=
  (hconn u v).exists_walk_length_eq_edist

theorem edist_le (p : G.Walk u v) :
    G.edist u v ≤ p.length :=
  sInf_le ⟨p, rfl⟩
protected alias Walk.edist_le := edist_le

@[simp]
theorem edist_eq_zero_iff : G.edist u v = 0 ↔ u = v := by
  simp [edist]

@[simp]
theorem edist_self : edist G v v = 0 :=
  edist_eq_zero_iff.mpr rfl

theorem edist_pos_of_ne (hne : u ≠ v) :
    0 < G.edist u v :=
  pos_iff_ne_zero.mpr <| edist_eq_zero_iff.ne.mpr hne

lemma edist_eq_top_of_not_reachable (h : ¬G.Reachable u v) :
    G.edist u v = ⊤ := by
  simp [edist, not_reachable_iff_isEmpty_walk.mp h]

theorem reachable_of_edist_ne_top (h : G.edist u v ≠ ⊤) :
    G.Reachable u v :=
  not_not.mp <| edist_eq_top_of_not_reachable.mt h

lemma exists_walk_of_edist_ne_top (h : G.edist u v ≠ ⊤) :
    ∃ p : G.Walk u v, p.length = G.edist u v :=
  (reachable_of_edist_ne_top h).exists_walk_length_eq_edist

protected theorem edist_triangle : G.edist u w ≤ G.edist u v + G.edist v w := by
  cases eq_or_ne (G.edist u v) ⊤ with
  | inl huv => simp [huv]
  | inr huv =>
    cases eq_or_ne (G.edist v w) ⊤ with
    | inl hvw => simp [hvw]
    | inr hvw =>
      obtain ⟨p, hp⟩ := exists_walk_of_edist_ne_top huv
      obtain ⟨q, hq⟩ := exists_walk_of_edist_ne_top hvw
      rw [← hp, ← hq, ← Nat.cast_add, ← Walk.length_append]
      exact edist_le _

theorem edist_comm : G.edist u v = G.edist v u := by
  rw [edist_eq_sInf, ← Set.image_univ, ← Set.image_univ_of_surjective Walk.reverse_surjective,
    ← Set.image_comp, Set.image_univ, Function.comp_def]
  simp_rw [Walk.length_reverse, ← edist_eq_sInf]

lemma exists_walk_of_edist_eq_coe {k : ℕ} (h : G.edist u v = k) :
    ∃ p : G.Walk u v, p.length = k :=
  have : G.edist u v ≠ ⊤ := by rw [h]; exact ENat.natCast_ne_top _
  have ⟨p, hp⟩ := exists_walk_of_edist_ne_top this
  ⟨p, Nat.cast_injective (hp.trans h)⟩

lemma edist_ne_top_iff_reachable : G.edist u v ≠ ⊤ ↔ G.Reachable u v := by
  refine ⟨reachable_of_edist_ne_top, fun h ↦ ?_⟩
  by_contra hx
  simp only [edist, iInf_eq_top, ENat.natCast_ne_top] at hx
  exact h.elim hx

/--
The extended distance between vertices is equal to `1` if and only if these vertices are adjacent.
-/
@[simp]
theorem edist_eq_one_iff_adj : G.edist u v = 1 ↔ G.Adj u v := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨w, hw⟩ := exists_walk_of_edist_ne_top <| by rw [h]; simp
    exact w.adj_of_length_eq_one <| Nat.cast_eq_one.mp <| h ▸ hw
  · exact le_antisymm (edist_le h.toWalk) (Order.one_le_iff_pos.mpr <| edist_pos_of_ne h.ne)

lemma edist_le_one_iff_adj_or_eq : G.edist u v ≤ 1 ↔ G.Adj u v ∨ u = v := by
  by_cases huv : u = v
  · simp [huv]
  · simp only [huv, or_false]
    have h : 0 < G.edist u v := edist_pos_of_ne huv
    rw [(Order.one_le_iff_pos.mpr h).ge_iff_eq']
    exact edist_eq_one_iff_adj

lemma edist_eq_two_iff {u v : V} :
    G.edist u v = 2 ↔ u ≠ v ∧ ¬ G.Adj u v ∧ (G.commonNeighbors u v).Nonempty := by
  refine ⟨fun h ↦ ⟨?_, ?_, ?_⟩, fun h ↦ le_antisymm ?_ ?_⟩
  · simp +decide [← G.edist_eq_zero_iff.not (b := u = v), h]
  · simp +decide [← edist_eq_one_iff_adj, h]
  · obtain ⟨w, hw⟩ := exists_walk_of_edist_eq_coe h
    use w.getVert 1
    suffices w.getVert 1 ∈ G.commonNeighbors (w.getVert 0) (w.getVert w.length) by simpa
    refine hw ▸ G.mem_commonNeighbors.mp ?_
    exact ⟨w.adj_getVert_succ (by simp [hw]), (w.adj_getVert_succ (by simp [hw])).symm⟩
  · obtain ⟨w, hw⟩ := h.2.2
    rw [mem_commonNeighbors] at hw
    have := (Walk.cons hw.1 <| .cons hw.2.symm .nil).edist_le
    simp_all
  · by_contra
    simp_all [Order.le_one_iff]

lemma two_lt_edist_iff {u v : V} :
    2 < G.edist u v ↔ u ≠ v ∧ ¬ G.Adj u v ∧ (G.commonNeighbors u v) = ∅ := by
  refine ⟨fun h ↦ ?_, fun h ↦ lt_of_le_of_ne ?_ (Ne.symm ?_)⟩
  · have hn : u ≠ v := fun hc ↦ by simp [hc] at h
    have : ¬ G.Adj u v := fun hc ↦ by simp +decide [edist_eq_one_iff_adj.mpr hc] at h
    use hn, this
    by_contra! hc
    simp [edist_eq_two_iff.mpr ⟨hn, this, hc⟩] at h
  · rw [← one_add_one_eq_two]
    refine Order.add_one_le_of_lt <| lt_of_le_of_ne ?_ ?_
    <;> grind [Order.one_le_iff_pos, pos_iff_ne_zero, edist_eq_zero_iff, edist_eq_one_iff_adj]
  · simp_all [edist_eq_two_iff]

lemma edist_bot_of_ne (h : u ≠ v) : (⊥ : SimpleGraph V).edist u v = ⊤ := by
  rwa [ne_eq, ← reachable_bot.not, ← edist_ne_top_iff_reachable.not, not_not] at h

lemma edist_bot [DecidableEq V] : (⊥ : SimpleGraph V).edist u v = (if u = v then 0 else ⊤) := by
  by_cases h : u = v <;> simp [h, edist_bot_of_ne]

lemma edist_top_of_ne (h : u ≠ v) : (⊤ : SimpleGraph V).edist u v = 1 := by
  simp [h]

lemma edist_top [DecidableEq V] : (⊤ : SimpleGraph V).edist u v = (if u = v then 0 else 1) := by
  by_cases h : u = v <;> simp [h]

/-- Supergraphs have smaller or equal extended distances to their subgraphs. -/
@[gcongr]
theorem edist_anti {G' : SimpleGraph V} (h : G ≤ G') :
    G'.edist u v ≤ G.edist u v := by
  by_cases hr : G.Reachable u v
  · obtain ⟨_, hw⟩ := hr.exists_walk_length_eq_edist
    rw [← hw, ← Walk.length_map (.ofLE h)]
    apply edist_le
  · exact edist_eq_top_of_not_reachable hr ▸ le_top

end edist

section dist

/--
The distance between two vertices that are reachable from each other is the length of the shortest
walk between them. It is defined when `u` and `v` are reachable from each other, which `h` states;
`SimpleGraph.edist` is the distance in `ℕ∞` of every pair of vertices, `⊤` for unreachable ones.
-/
@[nolint unusedArguments]
noncomputable def dist (u v : V) (_h : G.Reachable u v) : ℕ :=
  (G.edist u v).toNat

variable {G} {u v w : V}

theorem dist_eq_sInf (h : G.Reachable u v) :
    G.dist u v h = sInf (Set.range (Walk.length : G.Walk u v → ℕ)) :=
  ENat.iInf_toNat

@[grind =]
lemma Reachable.coe_dist_eq_edist (h : G.Reachable u v) : (G.dist u v h : ℕ∞) = G.edist u v :=
  ENat.natCast_toNat <| edist_ne_top_iff_reachable.mpr h

protected theorem Reachable.exists_walk_length_eq_dist (hr : G.Reachable u v) :
    ∃ p : G.Walk u v, p.length = G.dist u v hr :=
  dist_eq_sInf hr ▸ Nat.sInf_mem (Set.range_nonempty_iff_nonempty.mpr hr)

protected theorem Connected.exists_walk_length_eq_dist (hconn : G.Connected) (u v : V) :
    ∃ p : G.Walk u v, p.length = G.dist u v (hconn u v) :=
  (hconn u v).exists_walk_length_eq_dist

theorem dist_le (p : G.Walk u v) : G.dist u v p.reachable ≤ p.length :=
  dist_eq_sInf p.reachable ▸ Nat.sInf_le ⟨p, rfl⟩

@[simp]
theorem dist_eq_zero_iff (h : G.Reachable u v) : G.dist u v h = 0 ↔ u = v := by
  rw [← Nat.cast_inj (R := ℕ∞), h.coe_dist_eq_edist, Nat.cast_zero, edist_eq_zero_iff]

@[simp, grind =]
theorem dist_self : G.dist v v (Reachable.refl v) = 0 := by simp

protected theorem Reachable.pos_dist_of_ne (h : G.Reachable u v) (hne : u ≠ v) :
    0 < G.dist u v h :=
  Nat.pos_of_ne_zero (by simp [hne])

protected theorem Reachable.one_lt_dist_of_ne_of_not_adj (h : G.Reachable u v) (hne : u ≠ v)
    (hnadj : ¬G.Adj u v) : 1 < G.dist u v h :=
  Nat.lt_of_le_of_ne (h.pos_dist_of_ne hne) (by
    by_contra hc
    obtain ⟨p, hp⟩ := h.exists_walk_length_eq_dist
    exact hnadj (Walk.exists_length_eq_one_iff.mp ⟨p, hc ▸ hp⟩))

protected theorem Connected.dist_eq_zero_iff (hconn : G.Connected) :
    G.dist u v (hconn u v) = 0 ↔ u = v :=
  dist_eq_zero_iff _

protected theorem Connected.pos_dist_of_ne (hconn : G.Connected) (hne : u ≠ v) :
    0 < G.dist u v (hconn u v) :=
  (hconn u v).pos_dist_of_ne hne

protected theorem Connected.one_lt_dist_of_ne_of_not_adj (h : G.Connected) (hne : u ≠ v)
    (hnadj : ¬G.Adj u v) : 1 < G.dist u v (h u v) :=
  (h u v).one_lt_dist_of_ne_of_not_adj hne hnadj

theorem dist_triangle (huv : G.Reachable u v) (hvw : G.Reachable v w) :
    G.dist u w (huv.trans hvw) ≤ G.dist u v huv + G.dist v w hvw := by
  obtain ⟨p, hp⟩ := huv.exists_walk_length_eq_dist
  obtain ⟨q, hq⟩ := hvw.exists_walk_length_eq_dist
  rw [← hp, ← hq, ← Walk.length_append]
  apply dist_le

protected theorem Connected.dist_triangle (hconn : G.Connected) :
    G.dist u w (hconn u w) ≤ G.dist u v (hconn u v) + G.dist v w (hconn v w) :=
  dist_triangle _ _

theorem dist_comm (h : G.Reachable u v) : G.dist u v h = G.dist v u h.symm := by
  rw [dist, dist, edist_comm]

/--
The distance between vertices is equal to `1` if and only if these vertices are adjacent.
-/
@[simp]
theorem dist_eq_one_iff_adj (h : G.Reachable u v) : G.dist u v h = 1 ↔ G.Adj u v := by
  rw [dist, ENat.toNat_eq_iff one_ne_zero, ENat.natCast_one, edist_eq_one_iff_adj]

theorem Adj.diff_dist_adj (hadj : G.Adj v w) (huv : G.Reachable u v) :
    G.dist u w (huv.trans hadj.reachable) = G.dist u v huv ∨
      G.dist u w (huv.trans hadj.reachable) = G.dist u v huv + 1 ∨
      G.dist u w (huv.trans hadj.reachable) = G.dist u v huv - 1 := by
  have : G.dist v w hadj.reachable = 1 := (dist_eq_one_iff_adj _).mpr hadj
  have : G.dist w v hadj.reachable.symm = 1 := (dist_eq_one_iff_adj _).mpr hadj.symm
  have := dist_triangle huv hadj.reachable
  have := dist_triangle (huv.trans hadj.reachable) hadj.reachable.symm
  lia

theorem Walk.isPath_of_length_eq_dist (p : G.Walk u v) (hp : p.length = G.dist u v p.reachable) :
    p.IsPath := by
  classical
  have : p.bypass = p := by
    rw [← length_le_bypass_length_iff]
    calc p.length
      _ = G.dist u v p.reachable := hp
      _ ≤ p.bypass.length := dist_le p.bypass
  rw [← this]
  apply Walk.bypass_isPath

lemma Reachable.exists_path_of_dist (hr : G.Reachable u v) :
    ∃ (p : G.Walk u v), p.IsPath ∧ p.length = G.dist u v hr := by
  obtain ⟨p, h⟩ := hr.exists_walk_length_eq_dist
  exact ⟨p, p.isPath_of_length_eq_dist h, h⟩

lemma Connected.exists_path_of_dist (hconn : G.Connected) (u v : V) :
    ∃ (p : G.Walk u v), p.IsPath ∧ p.length = G.dist u v (hconn u v) :=
  (hconn u v).exists_path_of_dist

lemma dist_top_of_ne (h : u ≠ v) (hr : (⊤ : SimpleGraph V).Reachable u v) :
    (⊤ : SimpleGraph V).dist u v hr = 1 := by
  simp [h]

lemma dist_top [DecidableEq V] (hr : (⊤ : SimpleGraph V).Reachable u v) :
    (⊤ : SimpleGraph V).dist u v hr = (if u = v then 0 else 1) := by
  by_cases h : u = v <;> simp [h]

lemma length_eq_dist_of_subwalk {u' v' : V} {p₁ : G.Walk u v} {p₂ : G.Walk u' v'}
    (h₁ : p₁.length = G.dist u v p₁.reachable) (h₂ : p₂.IsSubwalk p₁) :
    p₂.length = G.dist u' v' p₂.reachable := by
  refine (dist_le _).eq_of_not_lt' fun hh ↦ ?_
  obtain ⟨ru, rv, h⟩ := h₂
  obtain ⟨s, _⟩ := p₂.reachable.exists_path_of_dist
  let r := ru.append s |>.append rv
  have : p₁.length = ru.length + p₂.length + rv.length := by simp [h]
  have : r.length = ru.length + s.length + rv.length := by simp [r]
  have := dist_le r
  lia

/-- Supergraphs have smaller or equal distances to their subgraphs. -/
protected theorem Reachable.dist_anti {G' : SimpleGraph V} (h : G ≤ G') (hr : G.Reachable u v) :
    G'.dist u v (hr.mono h) ≤ G.dist u v hr := by
  obtain ⟨_, hw⟩ := hr.exists_walk_length_eq_dist
  rw [← hw, ← Walk.length_map (.ofLE h)]
  apply dist_le

/-- This bundles and abstracts some facts about the first three vertices of a shortest walk
of length at least two: the first and third nodes are different and not connected. -/
lemma Walk.exists_adj_adj_not_adj_ne {p : G.Walk v w} (hp : p.length = G.dist v w p.reachable)
    (hl : 1 < G.dist v w p.reachable) :
    ∃ (x a b : V), G.Adj x a ∧ G.Adj a b ∧ ¬ G.Adj x b ∧ x ≠ b := by
  use v, p.getVert 1, p.getVert 2
  have hnp : ¬p.Nil := by grind [Nil.length_eq_zero]
  have : p.tail.tail.length < p.tail.length := by
    rw [← p.tail.length_tail_add_one (by
      simp only [not_nil_iff_lt_length, ← p.length_tail_add_one hnp] at hp ⊢
      lia)]
    lia
  have : p.tail.length < p.length := by rw [← p.length_tail_add_one hnp]; lia
  by_cases hv : v = p.getVert 2
  · have : G.dist v w p.reachable ≤ p.tail.tail.length := by
      simpa [hv, p.getVert_tail] using dist_le p.tail.tail
    lia
  by_cases hadj : G.Adj v (p.getVert 2)
  · have : G.dist v w p.reachable ≤ p.tail.tail.length + 1 :=
      dist_le <| p.tail.tail.cons <| p.getVert_tail ▸ hadj
    lia
  exact ⟨p.adj_snd hnp, p.adj_getVert_succ (hp ▸ hl), hadj, hv⟩

end dist

/-! ## Ball -/

section ball

/-- The open ball of radius `r` centered at the vertex `c` in the graph extended metric. -/
def ball (c : V) (r : ℕ∞) : Set V :=
  {v | G.edist v c < r}

variable {G} {c v : V} {r r₁ r₂ : ℕ∞}

@[simp]
theorem mem_ball : v ∈ G.ball c r ↔ G.edist v c < r := .rfl

/-- The ball of radius zero is empty. -/
@[simp]
theorem ball_zero : G.ball c 0 = ∅ := by simp [ball]

/-- The ball of radius one consists of just the center. -/
@[simp]
theorem ball_one : G.ball c 1 = {c} := by
  simp [ball]

/-- The ball of radius two consists of the center and its neighbors. -/
@[simp]
theorem ball_two : G.ball c 2 = insert c (G.neighborSet c) := by
  ext v
  simp [one_add_one_eq_two.symm, ENat.lt_add_one_iff ENat.one_ne_top,
    edist_le_one_iff_adj_or_eq, adj_comm, or_comm]

/-- The ball of radius `⊤` is the connected component of the center. -/
theorem ball_top :
    G.ball c ⊤ = (G.connectedComponentMk c).supp := by
  simp [Set.ext_iff, lt_top_iff_ne_top, edist_ne_top_iff_reachable]

/-- A vertex is in the ball of radius `⊤` iff it is reachable from the center. -/
theorem mem_ball_top : v ∈ G.ball c ⊤ ↔ G.Reachable v c := by
  simp [lt_top_iff_ne_top, edist_ne_top_iff_reachable]

/-- Balls are monotone in the radius. -/
@[gcongr]
theorem ball_mono (h : r₁ ≤ r₂) : G.ball c r₁ ⊆ G.ball c r₂ :=
  fun _ hv ↦ lt_of_lt_of_le hv h

/-- The center vertex belongs to any ball of positive radius. -/
theorem mem_ball_self (hr : 0 < r) : c ∈ G.ball c r := by
  simp [ball, hr]

/-- Ball membership is symmetric in center and point. -/
theorem mem_ball_comm : v ∈ G.ball c r ↔ c ∈ G.ball v r := by
  simp [ball, edist_comm]

end ball

end SimpleGraph
