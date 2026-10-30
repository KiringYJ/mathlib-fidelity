/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
import Mathlib.Analysis.Calculus.FDeriv.Basic

open scoped Topology

-- Default identity-coordinate uniqueness also works without opening the Topology namespace.
example (f : ℝ → ℝ) (d : ℝ →L[ℝ] ℝ) (x : ℝ) (h : HasFDerivAt f d x) :
    fderiv ℝ f x = d := h.fderiv

-- The identity-coordinate continuity default uses the available filter inclusion.
example (g : ℝ → ℝ) (d : ℝ →L[ℝ] ℝ) (z : ℝ) (L : Filter ℝ)
    (hL : L ≤ 𝓝 z) (h : HasFDerivAtFilter g d (L ×ˢ pure z)) :
    Filter.Tendsto g L (𝓝 (g z)) := h.tendsto_nhds hL

-- Identity coordinates discharge the zero-displacement compatibility condition automatically.
example (g : ℝ → ℝ) (d : ℝ →L[ℝ] ℝ) (z : ℝ) :
    HasFDerivAt g d z ↔
      Filter.Tendsto (fun y : {y : ℝ // y - z ≠ 0} ↦
        Checked.div ‖g y - g z - d ((y : ℝ) - z)‖ ‖(y : ℝ) - z‖
          (norm_ne_zero_iff.mpr y.2).isUnit)
        (Filter.comap Subtype.val (𝓝 z)) (𝓝 0) :=
  hasFDerivAt_iff_tendsto

example (g : ℝ → ℝ) (d : ℝ →L[ℝ] ℝ) (s : Set ℝ) (z : ℝ) :
    HasFDerivWithinAt g d s z ↔
      Filter.Tendsto (fun y : {y : ℝ // y - z ≠ 0} ↦
        Checked.div ‖g y - g z - d ((y : ℝ) - z)‖ ‖(y : ℝ) - z‖
          (norm_ne_zero_iff.mpr y.2).isUnit)
        (Filter.comap Subtype.val (𝓝[s] z)) (𝓝 0) :=
  hasFDerivWithinAt_iff_tendsto

example (g : ℝ → ℝ) (d : ℝ →L[ℝ] ℝ) (L : Filter (ℝ × ℝ)) :
    HasFDerivAtFilter g d L ↔
      Filter.Tendsto (fun p : {p : ℝ × ℝ // p.1 - p.2 ≠ 0} ↦
        Checked.div ‖g p.1.1 - g p.1.2 - d (p.1.1 - p.1.2)‖
          ‖p.1.1 - p.1.2‖ (norm_ne_zero_iff.mpr p.2).isUnit)
        (Filter.comap Subtype.val L) (𝓝 0) :=
  hasFDerivAtFilter_iff_tendsto

open Asymptotics Filter Set

-- On a coordinate fiber, a nonzero error is not a derivative, even though the quotient domain
-- is empty. The next two examples ensure that a vacuous ratio limit cannot erase this information.
example : ¬ HasFDerivAtFilter (fun b : Bool ↦ if b then (1 : ℝ) else 0)
    (0 : ℝ →L[ℝ] ℝ) (pure (true, false)) (fun _ ↦ (0 : ℝ)) := by
  rw [hasFDerivAtFilter_iff_isLittleO, isLittleO_pure]
  simp

example : Tendsto
    (fun p : {_p : Bool × Bool // (0 : ℝ) - 0 ≠ 0} ↦
      Checked.div ‖(if p.1.1 then (1 : ℝ) else 0) - (if p.1.2 then 1 else 0)‖
        ‖(0 : ℝ) - 0‖ (norm_ne_zero_iff.mpr p.2).isUnit)
    (comap Subtype.val (pure (true, false))) (𝓝 0) := by
  let : IsEmpty {p : Bool × Bool // (0 : ℝ) - 0 ≠ 0} := ⟨fun p ↦ p.2 (sub_self _)⟩
  exact tendsto_of_isEmpty

-- A compatible constant function has a derivative on that same coordinate fiber.
example : HasFDerivAtFilter (fun _ : Bool ↦ (3 : ℝ)) (ContinuousLinearMap.id ℝ ℝ)
    (pure (true, false)) (fun _ ↦ (0 : ℝ)) := by
  let : IsEmpty {p : Bool × Bool // (0 : ℝ) - 0 ≠ 0} := ⟨fun p ↦ p.2 (sub_self _)⟩
  exact (hasFDerivAtFilter_iff_tendsto (Eventually.of_forall fun _ _ ↦ rfl)).mpr
    tendsto_of_isEmpty

-- Restriction transport also works on a domain without an ambient additive structure.
example (f : ℝˣ → ℝ) (d : ℝ →L[ℝ] ℝ) (s : Set ℝˣ) (x : s)
    (hs : s ∈ 𝓝 (x : ℝˣ))
    (h : HasFDerivAt (fun y : s ↦ f y) d x (fun y ↦ ((y : ℝˣ) : ℝ))) :
    HasFDerivAt f d (x : ℝˣ) (fun y ↦ (y : ℝ)) :=
  h.of_restrict hs

-- The scaling sequence may start at zero: inversion occurs only at its nonzero indices.
example (f : ℝ → ℝ) (d : ℝ →L[ℝ] ℝ) (x v : ℝ) (h : HasFDerivAt f d x) :
    Tendsto (fun n : {n : ℕ // (n : ℝ) ≠ 0} ↦
      (n : ℕ) • (f (x + Checked.inv ((n : ℕ) : ℝ) n.2.isUnit • v) - f x))
      (comap Subtype.val atTop) (𝓝 (d v)) := by
  simpa only [Nat.cast_smul_eq_nsmul] using h.lim v
    (show Tendsto (fun n : ℕ ↦ ‖(n : ℝ)‖) atTop atTop by
      simpa using (tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop))

-- A zero exponent remains defined at zero.
example : (0 : ℝ) ^ (0 : ℤ) = 1 := by simp
