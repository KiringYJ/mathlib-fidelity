/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Topology.Separation.GDelta
public import Mathlib.Topology.UrysohnsLemma

/-!
# Perfectly normal topological spaces.

This file proves some properties of a perfectly normal space.

## TODO

Prove that the product of a perfectly normal space and a metric space is perfectly normal.

-/

public section

open Set Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A topological space is perfectly normal iff every closed set is the zero set of a continuous
function taking values in the unit interval. -/
theorem perfectlyNormalSpace_iff_forall_isClosed_preimage_zero :
    PerfectlyNormalSpace X ↔ ∀ s, IsClosed s → ∃ f : C(X, ℝ), s = f ⁻¹' {0} ∧
      ∀ x, f x ∈ Icc (0 : ℝ) 1 where
  mp h s hs := by
    -- write `s` as the intersection of a sequence of open sets `U n`
    obtain ⟨U, ho, hu⟩ := isGδ_iff_eq_iInter_nat.1 hs.isGδ
    have (n : ℕ) : Disjoint s (U n)ᶜ := by
      apply LE.le.disjoint_compl_right
      grw [hu, iInter_subset]
    -- for each `n`, construct a continuous function `f n` that separates `s` from `(U n)ᶜ`
    choose f hfs hfu hfr using fun n =>
      exists_continuous_zero_one_of_isClosed hs (ho n).isClosed_compl (this n)
    let w (n : ℕ) : ℝ := 1 / 2 / 2 ^ n
    have hw (n : ℕ) : 0 < w n := by dsimp [w]; positivity
    have hsw : Summable w := summable_geometric_two' 1
    have hsb (x : X) (n : ℕ) : ‖f n x * w n‖ ≤ w n := by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hfr n x).1, abs_of_nonneg (hw n).le]
      exact mul_le_of_le_one_left (hw n).le (hfr n x).2
    have hsx (x : X) : Summable fun n => f n x * w n :=
      hsw.of_norm_bounded fun n => hsb x n
    -- consider the infinite sum of `f n x * (1 / 2 / 2 ^ n)`, which is uniformly convergent and
    -- thus continuous because it is dominated by a geometric series
    let h : C(X, ℝ) :=
      { toFun x := ∑' n, f n x * w n
        continuous_toFun :=
          continuous_tsum (fun n => by fun_prop) hsw fun n x => hsb x n }
    refine ⟨h, ?_, fun x => ⟨?_, ?_⟩⟩
    · ext x
      refine ⟨fun hp => ?_, fun hp => ?_⟩
      · suffices ∀ n, f n x = 0 from by simp [h, this]
        exact fun n => hfs n hp
      · contrapose h
        simp only [preimage, notMem_ofPred_iff, ContinuousMap.coe_mk, mem_singleton_iff]
        apply ne_of_gt
        obtain ⟨i, hi⟩ := mem_iUnion.1 <| compl_iInter _ ▸ mem_compl (hu ▸ h)
        calc
        0 < w i := hw i
        _ = f i x * w i := by simp [hfu i hi]
        _ ≤ _ := (hsx x).le_tsum i fun j _ => mul_nonneg (hfr j x).1 (hw j).le
    · exact tsum_nonneg fun n => mul_nonneg (hfr n x).1 (hw n).le
    · calc
      h x = ∑' n, f n x * w n := rfl
      _ ≤ ∑' n, w n :=
        (hsx x).tsum_le_tsum (fun n => mul_le_of_le_one_left (hw n).le (hfr n x).2) hsw
      _ = 1 := tsum_geometric_two' 1
  mpr h :=
    { normal s t hs ht hst := by
        -- pick `f, g` such that `s = f ⁻¹' {0}` and `t = g ⁻¹' {0}`, and then the function
        -- `f / (f  + g)` separates `s` and `t`.
        obtain ⟨f, hf, hfr⟩ := h s hs
        obtain ⟨g, hg, hgr⟩ := h t ht
        have hsn : SeparatedNhds {(0 : ℝ)} {1} :=
          SeparatedNhds.of_finite (finite_singleton _) (finite_singleton _)
          (disjoint_singleton.2 zero_ne_one)
        have hfg (x : X) : f x + g x ≠ 0 := by
          simp_all only [preimage, mem_singleton_iff]
          by_cases! hfx : f x = 0
          · simpa [hfx] using hst.notMem_of_mem_left hfx
          · positivity [(hgr x).1, (hfr x).1]
        let k (x : X) : ℝ := Checked.div (f x) (f x + g x) (hfg x).isUnit
        have hp : s = k ⁻¹' {0} := by rw [hf]; ext x; simp [k]
        have hq : t = k ⁻¹' {1} := by rw [hg]; ext x; simp [k, div_eq_one_iff_eq]
        rw [hp, hq]
        exact hsn.preimage (f.continuous.div₀ (f.continuous.add g.continuous)
          (h₀ := fun x ↦ (hfg x).isUnit))
      closed_gdelta s hs := by
        by_cases! hse : s = ∅
        · simp_all
        -- pick `f` such that `s = f ⁻¹' {0} = ⋂ n, f ⁻¹' (Iio (1 / ((n : ℝ) + 1)))`
        obtain ⟨f, hf, hfr⟩ := h s hs
        refine isGδ_iff_eq_iInter_nat.2 ⟨fun n => f ⁻¹' (Iio (1 / ((n : ℝ) + 1))),
          fun n => ?_, ?_⟩
        · exact f.continuous.isOpen_preimage _ isOpen_Iio
        · simp only [hf, ← preimage_iInter,
            ← preimage_range_inter (s := ⋂ (n : ℕ), Iio (1 / ((n : ℝ) + 1))), inter_iInter]
          congr
          rw [eq_comm, eq_singleton_iff_unique_mem]
          refine ⟨mem_iInter_of_mem fun n => ?_, fun x h => ?_⟩
          · exact ⟨(hf ▸ hse : (f ⁻¹' {0}).Nonempty), show 0 < 1 / ((n : ℝ) + 1) by positivity⟩
          · apply le_antisymm
            · simp only [mem_iInter, mem_inter_iff, mem_Iio] at h
              exact ge_of_tendsto' tendsto_one_div_add_atTop_nhds_zero_nat (fun n => (h n).2.le)
            · rcases (mem_iInter.1 h 0).1 with ⟨x, rfl⟩
              exact (hfr x).1 }

@[deprecated (since := "2026-06-03")]
alias Topology.IsEmbedding.perfectlyNormalSpace := Topology.IsInducing.perfectlyNormalSpace
