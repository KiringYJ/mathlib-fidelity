/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Diam

/-!
# Girth of a simple graph

This file defines the girth and the extended girth of a simple graph as the length of its smallest
cycle. The extended girth of an acyclic graph is `∞`, and the girth in `ℕ` is defined only for a
graph that is not acyclic.

-/

@[expose] public section

namespace SimpleGraph
variable {α β : Type*} {G : SimpleGraph α} {G' : SimpleGraph β}

section egirth


/--
The extended girth of a simple graph is the length of its smallest cycle, or `∞` if the graph is
acyclic.
-/
noncomputable def egirth (G : SimpleGraph α) : ℕ∞ :=
  ⨅ a, ⨅ w : G.Walk a a, ⨅ _ : w.IsCycle, w.length

@[simp]
lemma le_egirth {n : ℕ∞} : n ≤ G.egirth ↔ ∀ a (w : G.Walk a a), w.IsCycle → n ≤ w.length := by
  simp [egirth]

lemma Walk.IsCycle.egirth_le_length {a} {w : G.Walk a a} (h : w.IsCycle) : G.egirth ≤ w.length :=
  le_egirth.mp le_rfl a w h

@[deprecated (since := "2026-07-05")] alias egirth_le_length := Walk.IsCycle.egirth_le_length

lemma Walk.IsCircuit.egirth_le_length {a} {w : G.Walk a a} (hwc : w.IsCircuit) :
    G.egirth ≤ w.length := by
  classical
  by_contra! hlg
  let w' : G.Walk a a := w.cycleBypass
  have hwc' : w'.IsCycle := hwc.isCycle_cycleBypass
  have hwlg' : w'.length < G.egirth := by
    grw [w.length_cycleBypass_le_length]
    exact hlg
  exact not_le_of_gt hwlg' hwc'.egirth_le_length

@[simp]
lemma egirth_eq_top : G.egirth = ⊤ ↔ G.IsAcyclic := by simp [egirth, IsAcyclic]

protected alias ⟨_, IsAcyclic.egirth_eq_top⟩ := egirth_eq_top

lemma egirth_anti : Antitone (egirth : SimpleGraph α → ℕ∞) :=
  fun G H h ↦ iInf_mono fun a ↦ iInf₂_mono' fun w hw ↦ ⟨w.mapLe h, hw.mapLe _, by simp⟩

lemma exists_egirth_eq_length :
    (∃ (a : α) (w : G.Walk a a), w.IsCycle ∧ G.egirth = w.length) ↔ ¬ G.IsAcyclic := by
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨a, w, hw, _⟩ hG
    exact hG _ hw
  · simp_rw [← egirth_eq_top, ← Ne.eq_def, egirth, iInf_subtype', iInf_sigma',
      ENat.iInf_natCast_ne_top, ← exists_prop, Subtype.exists', Sigma.exists', eq_comm] at h ⊢
    exact ciInf_mem _

lemma three_le_egirth : 3 ≤ G.egirth := by
  simpa using fun _ _ h ↦ h.three_le_length

@[simp] lemma egirth_bot : egirth (⊥ : SimpleGraph α) = ⊤ := by simp

theorem egirth_top (h : 3 ≤ ENat.card α) : egirth (⊤ : SimpleGraph α) = 3 := by
  classical
  refine le_antisymm ?_ three_le_egirth
  obtain ⟨s, hcard⟩ := Cardinal.exists_finset_eq_card <| Cardinal.ofNat_le_toENat.mp h
  obtain ⟨x, y, z, hxy, hxz, hyz, -⟩ := s.card_eq_three.mp hcard.symm
  set w : Walk ⊤ x x := .cons hxy <| .cons hyz <| .cons hxz.symm .nil with hw
  have : w.IsCycle :=
    { edges_nodup := by aesop
      ne_nil := by aesop
      support_nodup := by aesop }
  grw [this.egirth_le_length]
  simp [hw]

open Walk in
lemma egirth_le_two_mul_ediam_add_one (h : ¬ G.IsAcyclic) : G.egirth ≤ 2 * G.ediam + 1 := by
  obtain ⟨u, w, hw, hwl⟩ := exists_egirth_eq_length.mpr h
  let q := Nat.euclideanDiv w.length 2 two_ne_zero
  have hrec : 2 * q + w.length % 2 = w.length :=
    Nat.euclideanDiv_mul_add_mod w.length 2 two_ne_zero
  have hrem : w.length % 2 < 2 := Nat.mod_lt _ (by decide)
  have hq : q < w.length := by
    have := hw.three_le_length
    omega
  have hr := (w.take q).reachable
  obtain ⟨p, hp, hplen⟩ := hr.exists_path_of_dist
  have htake : (w.take q).length = q := by rw [take_length, inf_eq_left.mpr hq.le]
  have hdist : q ≤ G.dist u (w.getVert q) hr := by
    by_contra! hlt
    have hne : p ≠ w.take q := by
      intro he
      have hlength := congrArg Walk.length he
      omega
    obtain ⟨_, _, _, c, hc, hcl⟩ := hp.exists_isCycle_length_le_add_of_ne (hw.isPath_take hq) hne
    have hmin : w.length ≤ c.length := by
      apply ENat.natCast_le_natCast.mp
      rw [← hwl]
      exact hc.egirth_le_length
    omega
  have hbound : (w.length : ℕ∞) ≤ 2 * (q : ℕ∞) + 1 := by
    have : w.length ≤ 2 * q + 1 := by omega
    exact_mod_cast this
  have hdiam : (q : ℕ∞) ≤ G.ediam := calc
    (q : ℕ∞) ≤ (G.dist u (w.getVert q) hr : ℕ∞) := ENat.natCast_le_natCast.mpr hdist
    _ = G.edist u (w.getVert q) := hr.coe_dist_eq_edist
    _ ≤ G.ediam := edist_le_ediam
  grw [hwl, hbound, hdiam]

@[gcongr only]
lemma IsContained.egirth_le (h : G ⊑ G') : G'.egirth ≤ G.egirth := by
  by_cases hacyc : G.IsAcyclic
  · simp [hacyc.egirth_eq_top]
  obtain ⟨a, w, hw, hwl⟩ := exists_egirth_eq_length.mpr hacyc
  rw [hwl, ← w.length_map h.some.toHom]
  exact hw.map h.some.injective |>.egirth_le_length

@[gcongr only]
lemma Iso.egirth_eq (f : G ≃g G') : G.egirth = G'.egirth :=
  le_antisymm f.isContained'.egirth_le f.isContained.egirth_le

end egirth

section girth

/--
The girth of a simple graph that has a cycle is the length of its smallest cycle. It is defined
when the graph is not acyclic, which `h` states; `SimpleGraph.egirth` is the girth in `ℕ∞` of every
graph, `⊤` for an acyclic one.
-/
@[nolint unusedArguments]
noncomputable def girth (G : SimpleGraph α) (_h : ¬G.IsAcyclic) : ℕ :=
  G.egirth.toNat

lemma coe_girth (h : ¬G.IsAcyclic) : (G.girth h : ℕ∞) = G.egirth :=
  ENat.natCast_toNat <| egirth_eq_top.not.mpr h

lemma Walk.IsCycle.girth_le_length {a} {w : G.Walk a a} (h : w.IsCycle) :
    G.girth (fun hG ↦ hG _ h) ≤ w.length :=
  ENat.natCast_le_natCast.mp <| G.egirth.natCast_toNat_le_self.trans h.egirth_le_length

@[deprecated (since := "2026-07-05")] alias girth_le_length := Walk.IsCycle.girth_le_length

lemma three_le_girth (hG : ¬G.IsAcyclic) : 3 ≤ G.girth hG :=
  ENat.toNat_le_toNat three_le_egirth <| egirth_eq_top.not.mpr hG

lemma girth_anti {G' : SimpleGraph α} (hab : G ≤ G') (h : ¬G.IsAcyclic) :
    G'.girth (mt (IsAcyclic.anti hab) h) ≤ G.girth h :=
  ENat.toNat_le_toNat (egirth_anti hab) <| egirth_eq_top.not.mpr h

lemma Walk.IsCircuit.girth_le_length {a} {w : G.Walk a a} (hwc : w.IsCircuit)
    (h : ¬G.IsAcyclic) : G.girth h ≤ w.length :=
  ENat.natCast_le_natCast.mp <| G.egirth.natCast_toNat_le_self.trans <| hwc.egirth_le_length

lemma exists_girth_eq_length (h : ¬G.IsAcyclic) :
    ∃ (a : α) (w : G.Walk a a), w.IsCycle ∧ G.girth h = w.length := by
  obtain ⟨a, w, hw, hl⟩ := exists_egirth_eq_length.mpr h
  exact ⟨a, w, hw, by rw [girth, hl, ENat.toNat_natCast]⟩

lemma girth_le_two_mul_ediam_add_one (h : ¬G.IsAcyclic) :
    (G.girth h : ℕ∞) ≤ 2 * G.ediam + 1 := by
  rw [coe_girth]
  exact egirth_le_two_mul_ediam_add_one h

lemma girth_le_two_mul_diam_add_one (h : ¬G.IsAcyclic) (hdiam : G.ediam ≠ ⊤) :
    G.girth h ≤ 2 * G.diam hdiam + 1 := by
  have hb := girth_le_two_mul_ediam_add_one h
  rw [← coe_diam hdiam] at hb
  exact_mod_cast hb

theorem girth_top (h : 3 ≤ ENat.card α) (hG : ¬(⊤ : SimpleGraph α).IsAcyclic) :
    girth (⊤ : SimpleGraph α) hG = 3 := by
  simp [girth, egirth_top h]

lemma IsContained.girth_le (h : G ⊑ G') (hG : ¬G.IsAcyclic) :
    G'.girth (mt (IsAcyclic.comap h.some.toHom h.some.injective) hG) ≤ G.girth hG :=
  ENat.toNat_le_toNat h.egirth_le <| egirth_eq_top.not.mpr hG

lemma Iso.girth_eq (f : G ≃g G') (h : ¬G.IsAcyclic) :
    G.girth h = G'.girth (f.isAcyclic_iff.not.mp h) := by
  simp [girth, f.egirth_eq]

end girth

end SimpleGraph
