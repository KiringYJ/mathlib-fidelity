/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Smooth bump functions in inner product spaces

In this file we prove that a real inner product space has smooth bump functions,
see `hasContDiffBump_of_innerProductSpace`.

## Keywords

smooth function, bump function, inner product space
-/

@[expose] public section

open Filter Function Real
open scoped Topology ContDiff

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A base bump function in an inner product space. This construction works in any space with a
norm smooth away from zero but we do not have a typeclass for this. -/
noncomputable def ContDiffBumpBase.ofInnerProductSpace : ContDiffBumpBase E where
  toFun R x := if hR : R ≠ 1 then
    smoothTransition (Checked.div (R - ‖x‖) (R - 1) (sub_ne_zero.mpr hR).isUnit) else 0
  mem_Icc _ _ := by
    split_ifs
    · exact ⟨smoothTransition.nonneg _, smoothTransition.le_one _⟩
    · exact ⟨le_rfl, zero_le_one⟩
  symmetric _ _ := by simp only [norm_neg]
  smooth := by
    rintro ⟨R, x⟩ ⟨hR : 1 < R, -⟩
    apply ContDiffAt.contDiffWithinAt
    have hR' : ∀ᶠ p : ℝ × E in 𝓝 (R, x), 1 < p.1 :=
      continuous_fst.continuousAt.eventually (Ioi_mem_nhds hR)
    rcases eq_or_ne x 0 with rfl | hx
    · have hnorm : ∀ᶠ p : ℝ × E in 𝓝 (R, (0 : E)), ‖p.2‖ < 1 :=
        (continuous_norm.comp continuous_snd).continuousAt.eventually
          (Iio_mem_nhds (by simp : ‖(0 : E)‖ < 1))
      apply (contDiffAt_const (c := 1)).congr_of_eventuallyEq
      filter_upwards [hR', hnorm] with p hp hpn
      simpa only [Function.uncurry, dite_eq_left hp.ne'] using
        (smoothTransition.one_of_one_le ((one_le_div (sub_pos.mpr hp)).mpr
          (sub_le_sub_left hpn.le p.1)))
    · let q (p : ℝ × E) : ℝ := if hp : 1 < p.1 then
        Checked.div (p.1 - ‖p.2‖) (p.1 - 1) (sub_pos.mpr hp).ne'.isUnit else 0
      have hq : ContDiffAt ℝ ∞ q (R, x) := by
        have hd : ContDiffAt ℝ ∞ (fun p : ℝ × E ↦ p.1 - 1) (R, x) :=
          contDiffAt_fst.sub contDiffAt_const
        apply (contDiffAt_fst.sub (contDiffAt_snd.norm ℝ hx)).div hd
        exact hR'.mono fun p hp ↦ ⟨(sub_pos.mpr hp).ne'.isUnit, dite_eq_left hp⟩
      apply (smoothTransition.contDiffAt.comp _ hq).congr_of_eventuallyEq
      filter_upwards [hR'] with p hp
      simp only [Function.comp_apply, Function.uncurry, q, dite_eq_left hp, dite_eq_left hp.ne']
  eq_one R hR x hx := by
    simp only [dite_eq_left hR.ne']
    exact smoothTransition.one_of_one_le <| (one_le_div <| sub_pos.mpr hR).mpr <|
      sub_le_sub_left hx R
  support R hR := by
    ext x
    rw [mem_support, dite_eq_left hR.ne', Ne, smoothTransition.zero_iff_nonpos, not_le,
      div_pos_iff_of_pos_right (sub_pos.mpr hR), sub_pos, mem_ball_zero_iff]

/-- Any inner product space has smooth bump functions. -/
instance (priority := 100) hasContDiffBump_of_innerProductSpace : HasContDiffBump E :=
  ⟨⟨.ofInnerProductSpace E⟩⟩
