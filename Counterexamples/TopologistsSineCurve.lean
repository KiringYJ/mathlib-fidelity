/-
Copyright (c) 2025 Daniele Bolla. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Bolla, David Loeffler
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Topology.Connected.PathConnected

/-!
# The "topologist's sine curve" is connected but not path-connected

We give an example of a closed subset `T` of `ℝ × ℝ` which is connected but not path-connected: the
closure of the set `{ (x, sin x⁻¹) | x ∈ Ioi 0 }`.

## Main results

* `TopologistsSineCurve.isConnected_T`: the set `T` is connected.
* `TopologistsSineCurve.not_isPathConnected_T`: the set `T` is not path-connected.

This formalization is part of the UniDistance Switzerland bachelor thesis of Daniele Bolla. A
similar result has also been independently formalized by Vlad Tsyrklevich
(https://leanprover.zulipchat.com/#narrow/channel/113489-new-members/topic/golf.20request.3A.20Topologist's.20sine.20curve).
-/

@[expose] public section

open Topology Filter Set Real

namespace TopologistsSineCurve

/-- The ordinate of the sine curve at a positive abscissa. -/
noncomputable def ordinate (x : Ioi (0 : ℝ)) : ℝ :=
  sin (Checked.inv (x : ℝ) (show 0 < (x : ℝ) from x.property).ne'.isUnit)

private lemma continuous_ordinate : Continuous ordinate :=
  continuous_sin.comp <| continuous_subtype_val.fun_inv₀ (h0 := fun (x : Ioi (0 : ℝ)) ↦
    (show 0 < (x : ℝ) from x.property).ne'.isUnit)

/-- The positive branch of the topologist's sine curve. -/
noncomputable def S : Set (ℝ × ℝ) :=
  range (fun x : Ioi (0 : ℝ) ↦ ((x : ℝ), ordinate x))

/-- The vertical line segment `{ (0, y) | -1 ≤ y ≤ 1 }`, which is the set of limit points of `S`
not contained in `S` itself. -/
def Z : Set (ℝ × ℝ) := (fun y ↦ (0, y)) '' Icc (-1) 1

/-- The union of `S` and `Z` (which we will show is the closure of `S`). -/
noncomputable def T : Set (ℝ × ℝ) := S ∪ Z

/-- The sine phase at height `y` after `k + 1` full periods. -/
noncomputable def phase (y : ℝ) (k : ℕ) : ℝ :=
  arcsin y + ((k : ℝ) + 1) * (2 * π)

private lemma phase_pos (y : ℝ) (k : ℕ) : 0 < phase y k := by
  unfold phase
  nlinarith [pi_pos, neg_pi_div_two_le_arcsin y,
    mul_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) pi_pos.le]

/-- A sequence of abscissae tending to zero with the prescribed ordinate. -/
noncomputable def xSeq (y : ℝ) (k : ℕ) : ℝ :=
  Checked.inv (phase y k) (by exact (phase_pos y k).ne'.isUnit)

lemma xSeq_pos (y : ℝ) (k : ℕ) : 0 < xSeq y k := inv_pos.mpr (phase_pos y k)

lemma sin_inv_xSeq {y : ℝ} (hy : y ∈ Icc (-1) 1) (k : ℕ) :
    ordinate ⟨xSeq y k, xSeq_pos y k⟩ = y := by
  simpa [ordinate, xSeq, phase, -Nat.cast_add, ← Nat.cast_succ] using sin_arcsin' hy

lemma xSeq_tendsto (y : ℝ) : Tendsto (xSeq y) atTop (𝓝 0) := by
  have hd : Tendsto (phase y) atTop atTop :=
    tendsto_atTop_add_const_left _ _ <|
      (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop).atTop_mul_const
        (show 0 < 2 * π by positivity)
  unfold xSeq
  exact hd.fun_inv_tendsto_atTop (h0 := fun k ↦ (phase_pos y k).ne'.isUnit)

/-!
## `T` is closed
-/

/-- The closure of the topologist's sine curve `S` is the set `T`. -/
lemma closure_S : closure S = T := by
  ext ⟨x, y⟩
  simp only [mem_closure_iff_seq_limit, Prod.tendsto_iff]
  constructor
  · rintro ⟨f, hf_mem, hf_lim⟩
    change ∀ n, ∃ u : Ioi (0 : ℝ), ((u : ℝ), ordinate u) = f n at hf_mem
    choose u hu using hf_mem
    have h₁ : Tendsto (fun n ↦ (u n : ℝ)) atTop (𝓝 x) := by
      simpa only [Function.comp_def, ← hu] using hf_lim.1
    have h₂ : Tendsto (fun n ↦ ordinate (u n)) atTop (𝓝 y) := by
      simpa only [Function.comp_def, ← hu] using hf_lim.2
    have hx : 0 ≤ x :=
      isClosed_Ici.mem_of_tendsto h₁ (.of_forall fun n ↦ (show 0 < (u n : ℝ) from (u n).2).le)
    rcases hx.eq_or_lt with rfl | hx
    · right
      exact ⟨y, isClosed_Icc.mem_of_tendsto h₂ (.of_forall fun _ ↦ sin_mem_Icc _), rfl⟩
    · left
      let v : Ioi (0 : ℝ) := ⟨x, mem_Ioi.mpr hx⟩
      have huv : Tendsto u atTop (𝓝 v) := tendsto_subtype_rng.mpr h₁
      refine ⟨v, Prod.ext rfl ?_⟩
      exact tendsto_nhds_unique (continuous_ordinate.continuousAt.tendsto.comp huv) h₂
  · rintro (hz | ⟨z, hz⟩)
    · exact ⟨_, fun _ ↦ hz, tendsto_const_nhds, tendsto_const_nhds⟩
    · simp only [Prod.mk.injEq] at hz
      rcases hz with ⟨hz, ⟨rfl, rfl⟩⟩
      refine ⟨fun n ↦ (xSeq z n, z), fun n ↦ ?_, xSeq_tendsto z, tendsto_const_nhds⟩
      exact ⟨⟨xSeq z n, xSeq_pos z n⟩, Prod.ext rfl (sin_inv_xSeq hz n)⟩

lemma isClosed_T : IsClosed T := by simpa only [← closure_S] using isClosed_closure

/-!
## `T` is connected
-/

/-- `T` is connected, being the closure of the set `S` (which is obviously connected since it
is a continuous image of the positive real line). -/
theorem isConnected_T : IsConnected T := by
  rw [← closure_S]
  have : ConnectedSpace (Ioi (0 : ℝ)) := isConnected_iff_connectedSpace.mp isConnected_Ioi
  exact (isConnected_range (continuous_subtype_val.prodMk continuous_ordinate)).closure

/-!
## `T` is not path-connected
-/

lemma zero_mem_T : (0, 0) ∈ T := by
  refine .inr ⟨0, ⟨?_, ?_⟩, rfl⟩ <;>
  linarith

/-- A point in the `body` of the topologist's sine curve. -/
noncomputable def w : ℝ × ℝ := (1, sin 1⁻¹)

lemma w_mem_T : w ∈ T := .inl ⟨⟨1, mem_Ioi.2 zero_lt_one⟩, rfl⟩

private lemma norm_ge_abs_snd {a b : ℝ} : |b| ≤ ‖(a, b)‖ := by simp

private lemma exists_unitInterval_gt {t₀ : unitInterval} (ht₀ : t₀ < 1) {δ : ℝ} (hδ : 0 < δ) :
    ∃ t₁, t₀ < t₁ ∧ dist t₀ t₁ < δ := by
  let s₀ := (t₀ : ℝ) -- t₀ is in unitInterval
  let s₁ := min (s₀ + δ / 2) 1
  have h_s₀_delta_pos : 0 ≤ s₀ + δ / 2 := add_nonneg t₀.2.1 (by positivity)
  have hs₁ : 0 ≤ s₁ := le_min h_s₀_delta_pos zero_le_one
  have hs₁' : s₁ ≤ 1 := min_le_right ..
  refine ⟨⟨s₁, hs₁, hs₁'⟩, lt_min ((lt_add_iff_pos_right _).mpr (half_pos hδ)) ht₀, ?_⟩
  have h_le : s₁ ≤ s₀ + δ / 2 := min_le_left _ _
  have h_ge : s₀ ≤ s₁ := le_min (by linarith) t₀.2.2
  rw [Subtype.dist_eq, dist_comm, dist_eq, abs_of_nonneg (by linarith)]
  linarith

private lemma mem_S_of_x_pos {p : ℝ × ℝ} (hx : 0 < p.1) (hT : p ∈ T) :
    p.2 = ordinate ⟨p.1, hx⟩ := by
  rcases hT with ⟨u, rfl⟩ | ⟨y, _, rfl⟩
  · rfl
  · exact (lt_irrefl (0 : ℝ) hx).elim

/-- Every height in the segment occurs at an abscissa in `Ioc 0 a`. -/
lemma exists_mem_Ioc_of_y {y : ℝ} (hy : y ∈ Icc (-1) 1) {a : ℝ} (ha : 0 < a) :
    ∃ (x : ℝ) (hx : x ∈ Ioc 0 a), ordinate ⟨x, hx.1⟩ = y := by
  obtain ⟨N, h_dist⟩ := (Metric.tendsto_nhds.mp (xSeq_tendsto y) (a / 2) (by positivity)).exists
  refine ⟨xSeq y N, ⟨xSeq_pos y N, ?_⟩, sin_inv_xSeq hy N⟩
  rw [dist_eq, sub_zero, abs_of_pos (xSeq_pos _ N)] at h_dist
  linarith

/-- The set `T` is not path-connected. -/
theorem not_isPathConnected_T : ¬ IsPathConnected T := by
  -- **Step 1**:
  -- Assume for contradiction we have a path from `z = (0, 0)` to `w = (1, sin 1)`.
  -- Let t₀ be the last time the path is on the y-axis. By continuity of the path, we
  -- can find a `δ > 0` such that for all `t ∈ [t₀, t₀ + δ]`, we have `‖p(t) - p(t₀)‖ < 1`.
  intro h_pathConn
  replace h_pathConn := h_pathConn.joinedIn (0, 0) zero_mem_T w w_mem_T
  let p := h_pathConn.somePath
  have xcoord_pathContinuous : Continuous fun t ↦ (p t).1 := continuous_fst.comp p.continuous
  let t₀ : unitInterval := sSup {t | (p t).1 = 0}
  have h_pt₀_x : (p t₀).1 = 0 :=
    (isClosed_singleton.preimage xcoord_pathContinuous).sSup_mem ⟨0, by aesop⟩
  obtain ⟨δ, hδ, ht⟩ : ∃ δ, 0 < δ ∧ ∀ t, dist t t₀ < δ → dist (p t) (p t₀) < 1 :=
    Metric.eventually_nhds_iff.mp <| Metric.tendsto_nhds.mp (p.continuousAt t₀) _ one_pos
  -- **Step 2**:
  -- Choose a time t₁ in (t₀, t₀ + δ) and let `a = x(p(t₁))`. Using the fact that every
  -- connected subset of `ℝ` is an interval, we have `[0, a] ⊂ x(p([t0, t1]))`.
  obtain ⟨t₁, ht₁⟩ : ∃ t₁, t₀ < t₁ ∧ dist t₀ t₁ < δ := by
    refine exists_unitInterval_gt (lt_of_le_of_ne (unitInterval.le_one t₀) fun ht₀' ↦ ?_) hδ
    have w_x_path : (p 1).1 = 1 := by rw [Path.target p, w]
    have x_eq_zero : (p 1).1 = 0 := by rwa [ht₀'] at h_pt₀_x
    linarith
  let a := (p t₁).1
  have ha : 0 < a := by
    obtain ⟨x, hx_eq⟩ : p t₁ ∈ S := by
      refine (h_pathConn.somePath_mem t₁).elim id fun ⟨y, hy⟩ ↦ ?_
      have : (p t₁).1 = 0 := by simp only [p, ← hy.2]
      exact ((show t₁ ≤ t₀ from le_sSup this).not_gt ht₁.1).elim
    have he : (x : ℝ) = a := congrArg Prod.fst hx_eq
    exact he ▸ (show 0 < (x : ℝ) from x.property)
  have intervalAZeroSubOfT₀T₁Xcoord : Icc 0 a ⊆ (fun t ↦ (p t).1) '' Icc t₀ t₁ :=
    (isPreconnected_Icc.image _ <| xcoord_pathContinuous.continuousOn).Icc_subset
      (show 0 ∈ (fun t ↦ (p t).1) '' Icc t₀ t₁ from ⟨t₀, ⟨le_rfl, ht₁.1.le⟩, ‹_›⟩)
      (show a ∈ (fun t ↦ (p t).1) '' Icc t₀ t₁ from ⟨t₁, ⟨ht₁.1.le, le_rfl⟩, rfl⟩)
  -- **Step 3**: For every `y ∈ [-1, 1]`, there exists a `t` with `p t = y` and `dist t₀ t < δ`.
  have exists_close {y : ℝ} (hy : y ∈ Icc (-1) 1) : ∃ t, dist t t₀ < δ ∧ (p t).2 = y := by
    -- first find a `t ∈ [t₀, t₁]` with this property
    obtain ⟨x, hx, hx'⟩ := exists_mem_Ioc_of_y hy ha
    obtain ⟨t, ht⟩ : ∃ t ∈ Icc t₀ t₁, (p t).1 = x := intervalAZeroSubOfT₀T₁Xcoord ⟨hx.1.le, hx.2⟩
    have hpos : 0 < (p t).1 := by simpa only [ht.2] using hx.1
    have e : (⟨(p t).1, hpos⟩ : Ioi (0 : ℝ)) = ⟨x, hx.1⟩ := Subtype.ext ht.2
    refine ⟨t, ?_, (mem_S_of_x_pos hpos (h_pathConn.somePath_mem t)).trans
      ((congrArg ordinate e).trans hx')⟩
    calc -- now show `t ∈ Icc t₀ t₁` implies `dist t t₀ < δ`
    dist t t₀ ≤ dist t₁ t₀ := dist_right_le_of_mem_uIcc (Icc_subset_uIcc' ht.1)
    _ = dist t₀ t₁ := by rw [dist_comm]
    _ < δ := ht₁.2
  -- **Step 4**:
  -- Now the final contradiction: there are times within `δ` of `t₀` with `p t = 1`, and with
  -- `p t = -1`; but both must have distance `< 1` from `p t₀`, contradicting the triangle
  -- inequality.
  obtain ⟨x₁, hx₁, h_pathx₁⟩ : ∃ x₁, dist x₁ t₀ < δ ∧ (p x₁).2 = 1 := exists_close (by simp)
  obtain ⟨x₂, hx₂, h_pathx₂⟩ : ∃ x₂, dist x₂ t₀ < δ ∧ (p x₂).2 = -1 := exists_close (by simp)
  have : dist (p x₁) (p x₂) < 2 := by
    refine (dist_triangle_right _ _ (p t₀)).trans_lt ?_
    exact (add_lt_add (ht _ hx₁) (ht _ hx₂)).trans_eq (by norm_num)
  have := norm_ge_abs_snd.trans_lt this
  rw [h_pathx₁, h_pathx₂, abs_of_nonneg (by norm_num)] at this
  linarith

end TopologistsSineCurve
