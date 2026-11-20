/-
Copyright (c) 2019 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Tactic.FieldSimp

/-!
# Jensen's inequality and maximum principle for convex functions

In this file, we prove the finite Jensen inequality and the finite maximum principle for convex
functions. The integral versions are to be found in `Analysis.Convex.Integral`.

## Main declarations

Jensen's inequalities:
* `ConvexOn.map_centerMass_le`, `ConvexOn.map_sum_le`: Convex Jensen's inequality. The image of a
  convex combination of points under a convex function is less than the convex combination of the
  images.
* `ConcaveOn.le_map_centerMass`, `ConcaveOn.le_map_sum`: Concave Jensen's inequality.
* `StrictConvexOn.map_sum_lt`: Convex strict Jensen inequality.
* `StrictConcaveOn.lt_map_sum`: Concave strict Jensen inequality.

As corollaries, we get:
* `StrictConvexOn.map_sum_eq_iff`: Equality case of the convex Jensen inequality.
* `StrictConcaveOn.map_sum_eq_iff`: Equality case of the concave Jensen inequality.
* `ConvexOn.exists_ge_of_mem_convexHull`: Maximum principle for convex functions.
* `ConcaveOn.exists_le_of_mem_convexHull`: Minimum principle for concave functions.
-/

public section


open Finset Set Convex

variable {𝕜 E β ι : Type*}

/-! ### Jensen's inequality -/


section Jensen

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup E] [AddCommGroup β]
  [PartialOrder β] [IsOrderedAddMonoid β] [Module 𝕜 E] [Module 𝕜 β] [IsStrictOrderedModule 𝕜 β]
  {s : Set E} {f : E → β} {t : Finset ι} {w : ι → 𝕜} {p : ι → E} {v : 𝕜} {q : E}

/-- Convex **Jensen's inequality**, `Finset.centerMass` version. The output is a point of the
genuine function domain whose coordinates are the weighted center of the input coordinates. -/
theorem ConvexOn.map_centerMass_le {D : Type*} {s : Set D} {f : D → β} {coord : D → E}
    {p : ι → D} {q : D} (hf : ConvexOn 𝕜 s f coord) (h₀ : ∀ i ∈ t, 0 ≤ w i)
    (h₁ : 0 < ∑ i ∈ t, w i) (hmem : ∀ i ∈ t, p i ∈ s) (hq : q ∈ s)
    (hcoord : coord q = t.centerMass w (coord ∘ p) h₁.ne' := by rfl) :
    f q ≤ t.centerMass w (f ∘ p) h₁.ne' := by
  let C : Set (E × β) := {v | ∃ z ∈ s, coord z = v.1 ∧ f z ≤ v.2}
  have hC : Convex 𝕜 C := by
    rintro a ⟨x, hx, hax, hfx⟩ b ⟨y, hy, hby, hfy⟩ u v hu hv huv
    obtain ⟨z, hz, hcz⟩ := hf.1 ⟨x, hx, hax⟩ ⟨y, hy, hby⟩ hu hv huv
    refine ⟨z, hz, hcz, ?_⟩
    exact (hf.2 hx hy hu hv huv hz (by simpa only [hax, hby] using hcz)).trans
      (add_le_add (smul_le_smul_of_nonneg_left hfx hu) (smul_le_smul_of_nonneg_left hfy hv))
  have hpoints : ∀ i ∈ t, (coord (p i), f (p i)) ∈ C :=
    fun i hi => ⟨p i, hmem i hi, rfl, le_rfl⟩
  obtain ⟨z, hz, hcz, hfz⟩ := hC.centerMass_mem h₀ h₁ hpoints
  have hcz' : coord z = t.centerMass w (coord ∘ p) h₁.ne' := by
    simpa only [centerMass, Function.comp_apply, Prod.smul_fst, Prod.fst_sum] using hcz
  have hfz' : f z ≤ t.centerMass w (f ∘ p) h₁.ne' := by
    simpa only [centerMass, Function.comp_apply, Prod.smul_snd, Prod.snd_sum] using hfz
  have hfq : f q ≤ f z := by
    have hqz : coord q = (1 : 𝕜) • coord z + (0 : 𝕜) • coord z := by
      simpa only [one_smul, zero_smul, add_zero] using hcoord.trans hcz'.symm
    simpa only [one_smul, zero_smul, add_zero] using
      hf.2 hz hz zero_le_one le_rfl (by simp) hq hqz
  exact hfq.trans hfz'

/-- Concave **Jensen's inequality**, `Finset.centerMass` version. -/
theorem ConcaveOn.le_map_centerMass {D : Type*} {s : Set D} {f : D → β} {coord : D → E}
    {p : ι → D} {q : D} (hf : ConcaveOn 𝕜 s f coord) (h₀ : ∀ i ∈ t, 0 ≤ w i)
    (h₁ : 0 < ∑ i ∈ t, w i) (hmem : ∀ i ∈ t, p i ∈ s) (hq : q ∈ s)
    (hcoord : coord q = t.centerMass w (coord ∘ p) h₁.ne' := by rfl) :
    t.centerMass w (f ∘ p) h₁.ne' ≤ f q :=
  ConvexOn.map_centerMass_le (β := βᵒᵈ) hf h₀ h₁ hmem hq hcoord

/-- Convex **Jensen's inequality**, `Finset.sum` version. -/
theorem ConvexOn.map_sum_le {D : Type*} {s : Set D} {f : D → β} {coord : D → E}
    {p : ι → D} {q : D} (hf : ConvexOn 𝕜 s f coord) (h₀ : ∀ i ∈ t, 0 ≤ w i)
    (h₁ : ∑ i ∈ t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) (hq : q ∈ s)
    (hcoord : coord q = ∑ i ∈ t, w i • coord (p i) := by rfl) :
    f q ≤ ∑ i ∈ t, w i • f (p i) := by
  have hpos : 0 < ∑ i ∈ t, w i := h₁.symm ▸ zero_lt_one
  have hcoord' : coord q = t.centerMass w (coord ∘ p) hpos.ne' := by
    rw [t.centerMass_eq_of_sum_1 (coord ∘ p) h₁]
    exact hcoord
  have h := hf.map_centerMass_le h₀ hpos hmem hq hcoord'
  simpa only [t.centerMass_eq_of_sum_1 (f ∘ p) h₁, Function.comp_apply] using h

/-- Concave **Jensen's inequality**, `Finset.sum` version. -/
theorem ConcaveOn.le_map_sum {D : Type*} {s : Set D} {f : D → β} {coord : D → E}
    {p : ι → D} {q : D} (hf : ConcaveOn 𝕜 s f coord) (h₀ : ∀ i ∈ t, 0 ≤ w i)
    (h₁ : ∑ i ∈ t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) (hq : q ∈ s)
    (hcoord : coord q = ∑ i ∈ t, w i • coord (p i) := by rfl) :
    (∑ i ∈ t, w i • f (p i)) ≤ f q :=
  ConvexOn.map_sum_le (β := βᵒᵈ) hf h₀ h₁ hmem hq hcoord

/-- Convex **Jensen's inequality** where an element plays a distinguished role. -/
lemma ConvexOn.map_add_sum_le (hf : ConvexOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 ≤ w i)
    (h₁ : v + ∑ i ∈ t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) (hv : 0 ≤ v) (hq : q ∈ s) :
    f (v • q + ∑ i ∈ t, w i • p i) ≤ v • f q + ∑ i ∈ t, w i • f (p i) := by
  let W j := Option.elim j v w
  let P j := Option.elim j q p
  have hW : ∀ j ∈ insertNone t, 0 ≤ W j := forall_mem_insertNone.2 ⟨hv, h₀⟩
  have hsum : ∑ j ∈ insertNone t, W j = 1 := by simpa using! h₁
  have hP : ∀ j ∈ insertNone t, P j ∈ s := forall_mem_insertNone.2 ⟨hq, hmem⟩
  have : f (∑ j ∈ insertNone t, W j • P j) ≤ ∑ j ∈ insertNone t, W j • f (P j) :=
    hf.map_sum_le hW hsum hP (hf.convex.sum_mem hW hsum hP)
  simpa using! this

/-- Concave **Jensen's inequality** where an element plays a distinguished role. -/
lemma ConcaveOn.map_add_sum_le (hf : ConcaveOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 ≤ w i)
    (h₁ : v + ∑ i ∈ t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) (hv : 0 ≤ v) (hq : q ∈ s) :
    v • f q + ∑ i ∈ t, w i • f (p i) ≤ f (v • q + ∑ i ∈ t, w i • p i) :=
  hf.dual.map_add_sum_le h₀ h₁ hmem hv hq

/-! ### Strict Jensen inequality -/

/-- Convex **strict Jensen inequality**.

If the function is strictly convex, the weights are strictly positive and the indexed family of
points is non-constant, then Jensen's inequality is strict.

See also `StrictConvexOn.map_sum_eq_iff`. -/
lemma StrictConvexOn.map_sum_lt (hf : StrictConvexOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 < w i)
    (h₁ : ∑ i ∈ t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) (hp : ∃ j ∈ t, ∃ k ∈ t, p j ≠ p k) :
    f (∑ i ∈ t, w i • p i) < ∑ i ∈ t, w i • f (p i) := by
  classical
  obtain ⟨j, hj, k, hk, hjk⟩ := hp
  -- We replace `t` by `t \ {j, k}`
  have : k ∈ t.erase j := mem_erase.2 ⟨ne_of_apply_ne _ hjk.symm, hk⟩
  let u := (t.erase j).erase k
  have hj : j ∉ u := by simp [u]
  have hk : k ∉ u := by simp [u]
  have ht :
      t = (u.cons k hk).cons j (mem_cons.not.2 <| not_or_intro (ne_of_apply_ne _ hjk) hj) := by
    simp [u, insert_erase this, insert_erase ‹j ∈ t›, *]
  clear_value u
  subst ht
  simp only [sum_cons]
  have hjpos := h₀ j <| by simp
  have hkpos := h₀ k <| by simp
  let c := w j + w k
  have hcpos : 0 < c := add_pos hjpos hkpos
  have hc : w j / c + w k / c = 1 := by
    rw [← add_div]
    exact div_self
  have hcancel (x : 𝕜) : c * (x / c) = x := mul_div_cancel₀ x
  calc f (w j • p j + (w k • p k + ∑ x ∈ u, w x • p x))
    _ = f (c • ((w j / c) • p j + (w k / c) • p k) + ∑ x ∈ u, w x • p x) := by
      congrm f ?_
      match_scalars <;> simp only [hcancel]
    _ ≤ c • f ((w j / c) • p j + (w k / c) • p k) + ∑ x ∈ u, w x • f (p x) :=
      -- apply the usual Jensen's inequality w.r.t. the weighted average of the two distinguished
      -- points and all the other points
        hf.convexOn.map_add_sum_le (fun i hi ↦ (h₀ _ <| by simp [hi]).le)
          (by simpa [-cons_eq_insert, ← add_assoc] using h₁)
          (forall_of_forall_cons <| forall_of_forall_cons hmem) (by positivity) <| by
           exact hf.convex (hmem _ <| by simp) (hmem _ <| by simp)
             (div_pos hjpos hcpos).le (div_pos hkpos hcpos).le hc
    _ < c • ((w j / c) • f (p j) + (w k / c) • f (p k)) + ∑ x ∈ u, w x • f (p x) := by
      -- then apply the definition of strict convexity for the two distinguished points
      gcongr
      exact hf.map_combo_lt (hmem _ <| by simp) (hmem _ <| by simp) hjk
        (div_pos hjpos hcpos) (div_pos hkpos hcpos) hc
    _ = (w j • f (p j) + w k • f (p k)) + ∑ x ∈ u, w x • f (p x) := by
      match_scalars <;> simp only [hcancel]
    _ = w j • f (p j) + (w k • f (p k) + ∑ x ∈ u, w x • f (p x)) := by abel_nf

/-- Concave **strict Jensen inequality**.

If the function is strictly concave, the weights are strictly positive and the indexed family of
points is non-constant, then Jensen's inequality is strict.

See also `StrictConcaveOn.map_sum_eq_iff`. -/
lemma StrictConcaveOn.lt_map_sum (hf : StrictConcaveOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 < w i)
    (h₁ : ∑ i ∈ t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) (hp : ∃ j ∈ t, ∃ k ∈ t, p j ≠ p k) :
    ∑ i ∈ t, w i • f (p i) < f (∑ i ∈ t, w i • p i) := hf.dual.map_sum_lt h₀ h₁ hmem hp

/-! ### Equality case of Jensen's inequality -/

/-- A form of the **equality case of Jensen's equality**.

For a strictly convex function `f` and positive weights `w`, if
`f (∑ i ∈ t, w i • p i) = ∑ i ∈ t, w i • f (p i)`, then the points `p` are all equal.

See also `StrictConvexOn.map_sum_eq_iff`. -/
lemma StrictConvexOn.eq_of_le_map_sum (hf : StrictConvexOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 < w i)
    (h₁ : ∑ i ∈ t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s)
    (h_eq : ∑ i ∈ t, w i • f (p i) ≤ f (∑ i ∈ t, w i • p i)) :
    ∀ ⦃j⦄, j ∈ t → ∀ ⦃k⦄, k ∈ t → p j = p k := by
  by_contra!; exact h_eq.not_gt <| hf.map_sum_lt h₀ h₁ hmem this

/-- A form of the **equality case of Jensen's equality**.

For a strictly concave function `f` and positive weights `w`, if
`f (∑ i ∈ t, w i • p i) = ∑ i ∈ t, w i • f (p i)`, then the points `p` are all equal.

See also `StrictConcaveOn.map_sum_eq_iff`. -/
lemma StrictConcaveOn.eq_of_map_sum_eq (hf : StrictConcaveOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 < w i)
    (h₁ : ∑ i ∈ t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s)
    (h_eq : f (∑ i ∈ t, w i • p i) ≤ ∑ i ∈ t, w i • f (p i)) :
    ∀ ⦃j⦄, j ∈ t → ∀ ⦃k⦄, k ∈ t → p j = p k :=
  hf.dual.eq_of_le_map_sum h₀ h₁ hmem h_eq

/-- A form of the **equality case of Jensen's equality** for the case of strict convex and positive
weights. -/
theorem StrictConvexOn.map_sum_eq_iff_of_pos (hf : StrictConvexOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 < w i)
    (h₁ : ∑ i ∈ t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) :
    f (∑ i ∈ t, w i • p i) = ∑ i ∈ t, w i • f (p i) ↔ ∀ ⦃j⦄, j ∈ t → ∀ ⦃k⦄, k ∈ t → p j = p k := by
  refine ⟨fun h j hj k hk ↦ hf.eq_of_le_map_sum h₀ h₁ hmem h.ge hj hk, fun h ↦ ?_⟩
  rcases t.eq_empty_or_nonempty with (rfl | ⟨i, hi⟩)
  · simp at h₁
  · suffices f (∑ k ∈ t, w k • p i) = ∑ k ∈ t, w k • f (p i) by convert this using 3 <;> grind
    simp [← sum_smul, h₁]

/-- A form of the **equality case of Jensen's equality** for the case of strict concave and positive
weights. -/
theorem StrictConcaveOn.map_sum_eq_iff_of_pos (hf : StrictConcaveOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 < w i)
    (h₁ : ∑ i ∈ t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) :
    f (∑ i ∈ t, w i • p i) = ∑ i ∈ t, w i • f (p i) ↔ ∀ ⦃j⦄, j ∈ t → ∀ ⦃k⦄, k ∈ t → p j = p k :=
  hf.dual.map_sum_eq_iff_of_pos h₀ h₁ hmem

/-- A form of the **equality case of Jensen's equality** for the case of strict convex and
non-negative weights. -/
theorem StrictConvexOn.map_sum_eq_iff_of_nonneg (hf : StrictConvexOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 ≤ w i)
    (h₁ : ∑ i ∈ t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) :
    f (∑ i ∈ t, w i • p i) = ∑ i ∈ t, w i • f (p i) ↔
      ∀ ⦃j⦄, j ∈ t → w j ≠ 0 → ∀ ⦃k⦄, k ∈ t → w k ≠ 0 → p j = p k := by
  have :
      f (∑ i ∈ t with w i ≠ 0, w i • p i) = ∑ i ∈ t with w i ≠ 0, w i • f (p i) ↔
        ∀ ⦃j : ι⦄, j ∈ {x ∈ t | w x ≠ 0} → ∀ ⦃k : ι⦄, k ∈ {x ∈ t | w x ≠ 0} → p j = p k :=
    hf.map_sum_eq_iff_of_pos (by grind)
      (sum_filter_ne_zero _ |>.trans h₁) (hmem _ <| mem_of_mem_filter · ·)
  grind [sum_filter_of_ne, left_ne_zero_of_smul]

/-- A form of the **equality case of Jensen's equality** for the case of strict concave and
non-negative weights. -/
theorem StrictConcaveOn.map_sum_eq_iff_of_nonneg (hf : StrictConcaveOn 𝕜 s f)
    (h₀ : ∀ i ∈ t, 0 ≤ w i) (h₁ : ∑ i ∈ t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) :
    f (∑ i ∈ t, w i • p i) = ∑ i ∈ t, w i • f (p i) ↔
      ∀ ⦃j⦄, j ∈ t → w j ≠ 0 → ∀ ⦃k⦄, k ∈ t → w k ≠ 0 → p j = p k :=
  hf.dual.map_sum_eq_iff_of_nonneg h₀ h₁ hmem

theorem StrictConvexOn.map_sum_lt_iff_of_pos (hf : StrictConvexOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 < w i)
    (h₁ : ∑ i ∈ t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) :
    f (∑ i ∈ t, w i • p i) < ∑ i ∈ t, w i • f (p i) ↔ ∃ j ∈ t, ∃ k ∈ t, p j ≠ p k := by
  refine ⟨fun h ↦ ?_, hf.map_sum_lt h₀ h₁ hmem⟩
  contrapose! h
  exact hf.map_sum_eq_iff_of_pos h₀ h₁ hmem |>.mpr h |>.not_lt

theorem StrictConcaveOn.lt_map_sum_iff_of_pos (hf : StrictConcaveOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 < w i)
    (h₁ : ∑ i ∈ t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) :
    ∑ i ∈ t, w i • f (p i) < f (∑ i ∈ t, w i • p i) ↔ ∃ j ∈ t, ∃ k ∈ t, p j ≠ p k :=
  hf.dual.map_sum_lt_iff_of_pos h₀ h₁ hmem

theorem StrictConvexOn.map_sum_lt_iff_of_nonneg (hf : StrictConvexOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 ≤ w i)
    (h₁ : ∑ i ∈ t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) :
    f (∑ i ∈ t, w i • p i) < ∑ i ∈ t, w i • f (p i) ↔
      ∃ j ∈ t, ∃ k ∈ t, w j ≠ 0 ∧ w k ≠ 0 ∧ p j ≠ p k := by
  grind [hf.convexOn.map_sum_le h₀ h₁ hmem (hf.convex.sum_mem h₀ h₁ hmem) |>.not_lt_iff_eq,
    hf.map_sum_eq_iff_of_nonneg h₀ h₁ hmem]

theorem StrictConcaveOn.lt_map_sum_iff_of_nonneg (hf : StrictConcaveOn 𝕜 s f)
    (h₀ : ∀ i ∈ t, 0 ≤ w i) (h₁ : ∑ i ∈ t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) :
    ∑ i ∈ t, w i • f (p i) < f (∑ i ∈ t, w i • p i) ↔
      ∃ j ∈ t, ∃ k ∈ t, w j ≠ 0 ∧ w k ≠ 0 ∧ p j ≠ p k :=
  hf.dual.map_sum_lt_iff_of_nonneg h₀ h₁ hmem

/-- Canonical form of the **equality case of Jensen's equality**.

For a strictly convex function `f` and positive weights `w`, we have
`f (∑ i ∈ t, w i • p i) = ∑ i ∈ t, w i • f (p i)` if and only if the points `p` are all equal
(and in fact all equal to their center of mass w.r.t. `w`). -/
lemma StrictConvexOn.map_sum_eq_iff {w : ι → 𝕜} {p : ι → E} (hf : StrictConvexOn 𝕜 s f)
    (h₀ : ∀ i ∈ t, 0 < w i) (h₁ : ∑ i ∈ t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) :
    f (∑ i ∈ t, w i • p i) = ∑ i ∈ t, w i • f (p i) ↔ ∀ j ∈ t, p j = ∑ i ∈ t, w i • p i := by
  refine ⟨?_, fun h ↦ ?_⟩
  · obtain rfl | ⟨i₀, hi₀⟩ := t.eq_empty_or_nonempty
    · simp
    intro h_eq i hi
    have H (j) (hj : j ∈ t) : p j = p i₀ := hf.eq_of_le_map_sum h₀ h₁ hmem h_eq.ge hj hi₀
    calc p i = p i₀ := by rw [H _ hi]
      _ = (1 : 𝕜) • p i₀ := by simp
      _ = (∑ j ∈ t, w j) • p i₀ := by rw [h₁]
      _ = ∑ j ∈ t, (w j • p i₀) := by rw [sum_smul]
      _ = ∑ j ∈ t, (w j • p j) := by congr! 2 with j hj; rw [← H _ hj]
  · grind [hf.map_sum_eq_iff_of_pos h₀ h₁ hmem]

/-- Canonical form of the **equality case of Jensen's equality**.

For a strictly concave function `f` and positive weights `w`, we have
`f (∑ i ∈ t, w i • p i) = ∑ i ∈ t, w i • f (p i)` if and only if the points `p` are all equal
(and in fact all equal to their center of mass w.r.t. `w`). -/
lemma StrictConcaveOn.map_sum_eq_iff (hf : StrictConcaveOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 < w i)
    (h₁ : ∑ i ∈ t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) :
    f (∑ i ∈ t, w i • p i) = ∑ i ∈ t, w i • f (p i) ↔ ∀ j ∈ t, p j = ∑ i ∈ t, w i • p i :=
  hf.dual.map_sum_eq_iff h₀ h₁ hmem

/-- Canonical form of the **equality case of Jensen's equality**.

For a strictly convex function `f` and nonnegative weights `w`, we have
`f (∑ i ∈ t, w i • p i) = ∑ i ∈ t, w i • f (p i)` if and only if the points `p` with nonzero
weight are all equal (and in fact all equal to their center of mass w.r.t. `w`). -/
lemma StrictConvexOn.map_sum_eq_iff' (hf : StrictConvexOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 ≤ w i)
    (h₁ : ∑ i ∈ t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) :
    f (∑ i ∈ t, w i • p i) = ∑ i ∈ t, w i • f (p i) ↔
      ∀ j ∈ t, w j ≠ 0 → p j = ∑ i ∈ t, w i • p i := by
  have hw (i) (_ : i ∈ t) : w i • p i ≠ 0 → w i ≠ 0 := by simp_all
  have hw' (i) (_ : i ∈ t) : w i • f (p i) ≠ 0 → w i ≠ 0 := by simp_all
  rw [← sum_filter_of_ne hw, ← sum_filter_of_ne hw', hf.map_sum_eq_iff]
  · simp
  · simp +contextual [(h₀ _ _).lt_iff_ne']
  · rwa [sum_filter_ne_zero]
  · simp +contextual [hmem _ _]

/-- Canonical form of the **equality case of Jensen's equality**.

For a strictly concave function `f` and nonnegative weights `w`, we have
`f (∑ i ∈ t, w i • p i) = ∑ i ∈ t, w i • f (p i)` if and only if the points `p` with nonzero
weight are all equal (and in fact all equal to their center of mass w.r.t. `w`). -/
lemma StrictConcaveOn.map_sum_eq_iff' (hf : StrictConcaveOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 ≤ w i)
    (h₁ : ∑ i ∈ t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) :
    f (∑ i ∈ t, w i • p i) = ∑ i ∈ t, w i • f (p i) ↔
      ∀ j ∈ t, w j ≠ 0 → p j = ∑ i ∈ t, w i • p i := hf.dual.map_sum_eq_iff' h₀ h₁ hmem

/-- Canonical form of the **strict Jensen's inequality**. -/
theorem StrictConvexOn.map_sum_lt_iff_of_pos' (hf : StrictConvexOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 < w i)
    (h₁ : ∑ i ∈ t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) :
    f (∑ i ∈ t, w i • p i) < ∑ i ∈ t, w i • f (p i) ↔ ∃ j ∈ t, p j ≠ ∑ i ∈ t, w i • p i := by
  apply hf.convexOn.map_sum_le (h₀ · · |>.le) h₁ hmem
    (hf.convex.sum_mem (h₀ · · |>.le) h₁ hmem) |>.lt_iff_ne.trans
  contrapose!
  exact hf.map_sum_eq_iff h₀ h₁ hmem

/-- Canonical form of the **strict Jensen's inequality**. -/
theorem StrictConcaveOn.lt_map_sum_iff_of_pos' (hf : StrictConcaveOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 < w i)
    (h₁ : ∑ i ∈ t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) :
    ∑ i ∈ t, w i • f (p i) < f (∑ i ∈ t, w i • p i) ↔ ∃ j ∈ t, p j ≠ ∑ i ∈ t, w i • p i :=
  hf.dual.map_sum_lt_iff_of_pos' h₀ h₁ hmem

/-- Canonical form of the **strict Jensen's inequality**. -/
theorem StrictConvexOn.map_sum_lt_iff_of_nonneg' (hf : StrictConvexOn 𝕜 s f) (h₀ : ∀ i ∈ t, 0 ≤ w i)
    (h₁ : ∑ i ∈ t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) :
    f (∑ i ∈ t, w i • p i) < ∑ i ∈ t, w i • f (p i) ↔
      ∃ j ∈ t, w j ≠ 0 ∧ p j ≠ ∑ i ∈ t, w i • p i := by
  have :
      f (∑ i ∈ t with w i ≠ 0, w i • p i) < ∑ i ∈ t with w i ≠ 0, w i • f (p i) ↔
        ∃ j ∈ {x ∈ t | w x ≠ 0}, p j ≠ ∑ i ∈ t with w i ≠ 0, w i • p i :=
    hf.map_sum_lt_iff_of_pos' (by grind)
      (sum_filter_ne_zero _ |>.trans h₁) (hmem _ <| mem_of_mem_filter · ·)
  grind [sum_filter_of_ne, left_ne_zero_of_smul]

/-- Canonical form of the **strict Jensen's inequality**. -/
theorem StrictConcaveOn.lt_map_sum_iff_of_nonneg' (hf : StrictConcaveOn 𝕜 s f)
    (h₀ : ∀ i ∈ t, 0 ≤ w i) (h₁ : ∑ i ∈ t, w i = 1) (hmem : ∀ i ∈ t, p i ∈ s) :
    ∑ i ∈ t, w i • f (p i) < f (∑ i ∈ t, w i • p i) ↔ ∃ j ∈ t, w j ≠ 0 ∧ p j ≠ ∑ i ∈ t, w i • p i :=
  hf.dual.map_sum_lt_iff_of_nonneg' h₀ h₁ hmem

end Jensen

/-! ### Maximum principle -/


section MaximumPrinciple

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup E]
  [AddCommGroup β] [LinearOrder β] [IsOrderedAddMonoid β] [Module 𝕜 E]
  [Module 𝕜 β] [IsStrictOrderedModule 𝕜 β] {s : Set E} {f : E → β} {w : ι → 𝕜} {p : ι → E}
  {x y z : E}

theorem ConvexOn.le_sup_of_mem_convexHull {t : Finset E} (hf : ConvexOn 𝕜 s f) (hts : ↑t ⊆ s)
    (hx : x ∈ convexHull 𝕜 (t : Set E)) :
    f x ≤ t.sup' (coe_nonempty.1 <| convexHull_nonempty_iff.1 ⟨x, hx⟩) f := by
  obtain ⟨w, hw₀, hw₁, rfl⟩ := mem_convexHull.1 hx
  have hpos : 0 < ∑ i ∈ t, w i := by positivity
  exact (hf.map_centerMass_le hw₀ hpos hts (hf.convex.centerMass_mem hw₀ hpos hts)).trans
    (centerMass_le_sup hw₀ <| by positivity)

theorem ConvexOn.inf_le_of_mem_convexHull {t : Finset E} (hf : ConcaveOn 𝕜 s f) (hts : ↑t ⊆ s)
    (hx : x ∈ convexHull 𝕜 (t : Set E)) :
    t.inf' (coe_nonempty.1 <| convexHull_nonempty_iff.1 ⟨x, hx⟩) f ≤ f x :=
  hf.dual.le_sup_of_mem_convexHull hts hx

/-- If a function `f` is convex on `s`, then the value it takes at some center of mass of points of
`s` is less than the value it takes on one of those points. -/
lemma ConvexOn.exists_ge_of_centerMass {t : Finset ι} (h : ConvexOn 𝕜 s f)
    (hw₀ : ∀ i ∈ t, 0 ≤ w i) (hw₁ : 0 < ∑ i ∈ t, w i) (hp : ∀ i ∈ t, p i ∈ s) :
    ∃ i ∈ t, f (t.centerMass w p hw₁.ne') ≤ f (p i) := by
  set y := t.centerMass w p hw₁.ne'
  -- TODO: can `rsuffices` be used to write the `exact` first, then the proof of this obtain?
  obtain ⟨i, hi, hfi⟩ : ∃ i ∈ {i ∈ t | w i ≠ 0}, w i • f y ≤ w i • (f ∘ p) i := by
    have hw' : (0 : 𝕜) < ∑ i ∈ t with w i ≠ 0, w i := by rwa [sum_filter_ne_zero]
    refine exists_le_of_sum_le (nonempty_of_sum_ne_zero hw'.ne') ?_
    have hle := h.map_centerMass_le
      (t := {i ∈ t | w i ≠ 0}) (w := w) (p := p)
      (fun i hi ↦ hw₀ i (mem_filter.mp hi).1) hw'
      (fun i hi ↦ hp i (mem_filter.mp hi).1)
      (h.convex.centerMass_mem (fun i hi ↦ hw₀ i (mem_filter.mp hi).1) hw'
        (fun i hi ↦ hp i (mem_filter.mp hi).1))
    rw [centerMass_filter_ne_zero] at hle
    have hs := smul_le_smul_of_nonneg_left hle hw'.le
    simp only [centerMass, smul_inv_smul₀] at hs
    rw [← sum_smul]
    exact hs
  rw [mem_filter] at hi
  exact ⟨i, hi.1, (smul_le_smul_iff_of_pos_left <| (hw₀ i hi.1).lt_of_ne hi.2.symm).1 hfi⟩

/-- If a function `f` is concave on `s`, then the value it takes at some center of mass of points of
`s` is greater than the value it takes on one of those points. -/
lemma ConcaveOn.exists_le_of_centerMass {t : Finset ι} (h : ConcaveOn 𝕜 s f)
    (hw₀ : ∀ i ∈ t, 0 ≤ w i) (hw₁ : 0 < ∑ i ∈ t, w i) (hp : ∀ i ∈ t, p i ∈ s) :
    ∃ i ∈ t, f (p i) ≤ f (t.centerMass w p hw₁.ne') :=
  h.dual.exists_ge_of_centerMass hw₀ hw₁ hp

/-- **Maximum principle** for convex functions. If a function `f` is convex on the convex hull of
`s`, then the eventual maximum of `f` on `convexHull 𝕜 s` lies in `s`. -/
lemma ConvexOn.exists_ge_of_mem_convexHull {t : Set E} (hf : ConvexOn 𝕜 s f) (hts : t ⊆ s)
    (hx : x ∈ convexHull 𝕜 t) : ∃ y ∈ t, f x ≤ f y := by
  rw [_root_.convexHull_eq] at hx
  obtain ⟨α, t, w, p, hw₀, hw₁, hp, rfl⟩ := hx
  obtain ⟨i, hit, Hi⟩ := hf.exists_ge_of_centerMass hw₀ (hw₁.symm ▸ zero_lt_one)
    fun i hi ↦ hts (hp i hi)
  exact ⟨p i, hp i hit, Hi⟩

/-- **Minimum principle** for concave functions. If a function `f` is concave on the convex hull of
`s`, then the eventual minimum of `f` on `convexHull 𝕜 s` lies in `s`. -/
lemma ConcaveOn.exists_le_of_mem_convexHull {t : Set E} (hf : ConcaveOn 𝕜 s f) (hts : t ⊆ s)
    (hx : x ∈ convexHull 𝕜 t) : ∃ y ∈ t, f y ≤ f x := hf.dual.exists_ge_of_mem_convexHull hts hx

/-- **Maximum principle** for convex functions on a segment. If a function `f` is convex on the
segment `[x, y]`, then the eventual maximum of `f` on `[x, y]` is at `x` or `y`. -/
lemma ConvexOn.le_max_of_mem_segment (hf : ConvexOn 𝕜 s f) (hx : x ∈ s) (hy : y ∈ s)
    (hz : z ∈ [x -[𝕜] y]) : f z ≤ max (f x) (f y) := by
  rw [← convexHull_pair] at hz; simpa using hf.exists_ge_of_mem_convexHull (pair_subset hx hy) hz

/-- **Minimum principle** for concave functions on a segment. If a function `f` is concave on the
segment `[x, y]`, then the eventual minimum of `f` on `[x, y]` is at `x` or `y`. -/
lemma ConcaveOn.min_le_of_mem_segment (hf : ConcaveOn 𝕜 s f) (hx : x ∈ s) (hy : y ∈ s)
    (hz : z ∈ [x -[𝕜] y]) : min (f x) (f y) ≤ f z := hf.dual.le_max_of_mem_segment hx hy hz

/-- **Maximum principle** for convex functions on an interval. If a function `f` is convex on the
interval `[x, y]`, then the eventual maximum of `f` on `[x, y]` is at `x` or `y`. -/
lemma ConvexOn.le_max_of_mem_Icc {s : Set 𝕜} {f : 𝕜 → β} {x y z : 𝕜} (hf : ConvexOn 𝕜 s f)
    (hx : x ∈ s) (hy : y ∈ s) (hz : z ∈ Icc x y) : f z ≤ max (f x) (f y) := by
  rw [← segment_eq_Icc (hz.1.trans hz.2)] at hz; exact hf.le_max_of_mem_segment hx hy hz

/-- **Minimum principle** for concave functions on an interval. If a function `f` is concave on the
interval `[x, y]`, then the eventual minimum of `f` on `[x, y]` is at `x` or `y`. -/
lemma ConcaveOn.min_le_of_mem_Icc {s : Set 𝕜} {f : 𝕜 → β} {x y z : 𝕜} (hf : ConcaveOn 𝕜 s f)
    (hx : x ∈ s) (hy : y ∈ s) (hz : z ∈ Icc x y) : min (f x) (f y) ≤ f z :=
  hf.dual.le_max_of_mem_Icc hx hy hz

lemma ConvexOn.bddAbove_convexHull {s t : Set E} (hst : s ⊆ t) (hf : ConvexOn 𝕜 t f) :
    BddAbove (f '' s) → BddAbove (f '' convexHull 𝕜 s) := by
  rintro ⟨b, hb⟩
  refine ⟨b, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, hy, hxy⟩ := hf.exists_ge_of_mem_convexHull hst hx
  exact hxy.trans <| hb <| mem_image_of_mem _ hy

lemma ConcaveOn.bddBelow_convexHull {s t : Set E} (hst : s ⊆ t) (hf : ConcaveOn 𝕜 t f) :
    BddBelow (f '' s) → BddBelow (f '' convexHull 𝕜 s) := hf.dual.bddAbove_convexHull hst

end MaximumPrinciple
