/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
import Mathlib.Analysis.Calculus.Deriv.Basic

open scoped Topology

-- Defaults must not depend on an opened namespace or on the caller using the names f, f', x.
example (g : ℝ → ℝ) (d z : ℝ) (hg : HasDerivAt g d z) : deriv g z = d :=
  hg.deriv

example (g : ℝ → ℝ) (d z : ℝ) :
    HasDerivAt g d z ↔
      Filter.Tendsto (fun y : {y : ℝ // y - z ≠ 0} ↦
        Checked.div ‖g y - g z - ((y : ℝ) - z) • d‖ ‖(y : ℝ) - z‖
          (norm_ne_zero_iff.mpr y.2).isUnit)
        (Filter.comap Subtype.val (𝓝 z)) (𝓝 0) :=
  hasDerivAt_iff_tendsto

example (g : ℝ → ℝ) (d z : ℝ) (s : Set ℝ) :
    HasDerivWithinAt g d s z ↔
      Filter.Tendsto (fun y : {y : ℝ // y - z ≠ 0} ↦
        Checked.div ‖g y - g z - ((y : ℝ) - z) • d‖ ‖(y : ℝ) - z‖
          (norm_ne_zero_iff.mpr y.2).isUnit)
        (Filter.comap Subtype.val (𝓝[s] z)) (𝓝 0) :=
  hasDerivWithinAt_iff_tendsto

example (g : ℝ → ℝ) (d : ℝ) (L : Filter (ℝ × ℝ)) :
    HasDerivAtFilter g d L ↔
      Filter.Tendsto (fun p : {p : ℝ × ℝ // p.1 - p.2 ≠ 0} ↦
        Checked.div ‖g p.1.1 - g p.1.2 - (p.1.1 - p.1.2) • d‖
          ‖p.1.1 - p.1.2‖ (norm_ne_zero_iff.mpr p.2).isUnit)
        (Filter.comap Subtype.val L) (𝓝 0) :=
  hasDerivAtFilter_iff_tendsto

-- Unit coordinates have no ambient additive structure, but retain the scalar tangent space.
example (g : ℝˣ → ℝ) (d : ℝ) (z : ℝˣ) :
    HasDerivAt g d z (fun y ↦ (y : ℝ)) ↔
      Filter.Tendsto (fun y : {y : ℝˣ // (y : ℝ) - (z : ℝ) ≠ 0} ↦
        Checked.div ‖g y - g z - (((y : ℝˣ) : ℝ) - (z : ℝ)) • d‖
          ‖((y : ℝˣ) : ℝ) - (z : ℝ)‖ (norm_ne_zero_iff.mpr y.2).isUnit)
        (Filter.comap Subtype.val (𝓝 z)) (𝓝 0) :=
  hasDerivAt_iff_tendsto (Filter.Eventually.of_forall fun _ h ↦ congrArg g (Units.ext h))

-- Differentiation of the coordinate map needs no addition operation on its unit domain.
example (z : ℝˣ) :
    HasDerivAt (fun y : ℝˣ ↦ (y : ℝ)) (1 : ℝ) z (fun y ↦ (y : ℝ)) := by
  apply (hasDerivAt_iff_tendsto (Filter.Eventually.of_forall fun _ h ↦ h)).mpr
  simpa only [smul_eq_mul, mul_one, sub_self, norm_zero, zero_div] using
    (_root_.tendsto_const_nhds (x := (0 : ℝ)) :
      Filter.Tendsto (fun _ : {y : ℝˣ // (y : ℝ) - (z : ℝ) ≠ 0} ↦ (0 : ℝ))
        (Filter.comap Subtype.val (𝓝 z)) (𝓝 0))

-- A nonzero change along a collapsed coordinate fiber is not a derivative.
example : ¬ HasDerivAtFilter (fun b : Bool ↦ if b then (1 : ℝ) else 0) (7 : ℝ)
    (pure (true, false)) (fun _ ↦ (0 : ℝ)) := by
  unfold HasDerivAtFilter
  rw [hasFDerivAtFilter_iff_isLittleO, Asymptotics.isLittleO_pure]
  simp

-- A compatible fiber may have an empty quotient domain without requiring a nonzero coordinate.
example : HasDerivAtFilter (fun _ : Bool ↦ (3 : ℝ)) (7 : ℝ)
    (pure (true, false)) (fun _ ↦ (0 : ℝ)) := by
  let : IsEmpty {p : Bool × Bool // (0 : ℝ) - 0 ≠ 0} := ⟨fun p ↦ p.2 (sub_self _)⟩
  exact (hasDerivAtFilter_iff_tendsto (Filter.Eventually.of_forall fun _ _ ↦ rfl)).mpr
    Filter.tendsto_of_isEmpty
