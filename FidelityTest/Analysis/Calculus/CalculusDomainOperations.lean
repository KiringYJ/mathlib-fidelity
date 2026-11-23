/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul

open Filter Asymptotics
open scoped Topology InnerProductSpace

-- Filter rules need neither addition nor a topology on the actual domain.
example {D : Type*} (coord : D → ℝ) (f g : D → ℝ) (d e : ℝ →L[ℝ] ℝ)
    (L : Filter (D × D)) (hf : HasFDerivAtFilter f d L coord)
    (hg : HasFDerivAtFilter g e L coord) :
    HasFDerivAtFilter (fun x ↦ (3 : ℝ) • f x - g x) ((3 : ℝ) • d - e) L coord :=
  (hf.const_smul (3 : ℝ)).sub hg

example {D : Type*} (coord : D → ℝ) (f g : D → ℝ) (d e : ℝ →L[ℝ] ℝ)
    (L : Filter (D × D)) (hf : HasFDerivAtFilter f d L coord)
    (hg : HasFDerivAtFilter g e L coord) :
    HasFDerivAtFilter (fun x ↦ (f x, g x).1)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (d.prod e)) L coord :=
  (hf.prodMk hg).fst

example {D : Type*} (coord : D → ℂ) (f : D → ℂ) (d : ℂ →L[ℂ] ℂ)
    (L : Filter (D × D)) (hf : HasFDerivAtFilter f d L coord) :
    HasFDerivAtFilter f (d.restrictScalars ℝ) L coord :=
  hf.restrictScalars ℝ

-- Finite sums and product formation keep unit domains and their ambient tangent space.
example (f : Fin 3 → ℝˣ → ℝ) (d : Fin 3 → ℝ →L[ℝ] ℝ) (x : ℝˣ)
    (h : ∀ i, HasFDerivAt (f i) (d i) x (fun y ↦ (y : ℝ))) :
    HasFDerivAt (fun y ↦ ∑ i, f i y) (∑ i, d i) x (fun y ↦ (y : ℝ)) :=
  HasFDerivAt.fun_sum fun i _ ↦ h i

example (f g : ℝˣ → ℝ) (x : ℝˣ)
    (hf : DifferentiableAt ℝ f x (fun y ↦ (y : ℝ)))
    (hg : DifferentiableAt ℝ g x (fun y ↦ (y : ℝ))) :
    DifferentiableAt ℝ (fun y ↦ (f y - g y, 3 - f y)) x (fun y ↦ (y : ℝ)) :=
  (hf.sub hg).prodMk (hf.const_sub 3)

-- Bilinear composition needs coordinate continuity, but no embedding hypothesis.
example {D : Type*} [TopologicalSpace D] (coord : D → ℝ) (f g : D → ℝ)
    (d e : ℝ →L[ℝ] ℝ) (B : ℝ →L[ℝ] ℝ →L[ℝ] ℝ) (x : D)
    (hf : HasFDerivAt f d x coord) (hg : HasFDerivAt g e x coord)
    (hc : ContinuousAt coord x) :
    HasFDerivAt (fun y ↦ B (f y) (g y))
      (B.precompR ℝ (f x) e + B.precompL ℝ d (g x)) x coord :=
  B.hasFDerivAt_of_bilinear hf hg hc

-- The gradient bridge and normalized error use the same genuine domain.
example (f : ℝˣ → ℝ) (d : ℝ) (x : ℝˣ)
    (h : HasGradientAt f d x (fun y ↦ (y : ℝ))) :
    HasFDerivAt f (InnerProductSpace.toDual ℝ ℝ d) x (fun y ↦ (y : ℝ)) :=
  h.hasFDerivAt

example (g : ℝ → ℝ) (d z : ℝ) (L : Filter ℝ) (hL : L ≤ 𝓝 z)
    (h : HasGradientAtFilter g d z L) : Tendsto g L (𝓝 (g z)) :=
  h.tendsto_nhds hL

example (f : ℝˣ → ℝ) (d : ℝ) (x : ℝˣ) :
    HasGradientAt f d x (fun y ↦ (y : ℝ)) ↔
      Tendsto (fun y : {y : ℝˣ // (y : ℝ) - (x : ℝ) ≠ 0} ↦
        Checked.div ‖f y - f x - ⟪d, ((y : ℝˣ) : ℝ) - (x : ℝ)⟫_ℝ‖
          ‖((y : ℝˣ) : ℝ) - (x : ℝ)‖ (norm_ne_zero_iff.mpr y.2).isUnit)
        (comap Subtype.val (𝓝 x)) (𝓝 0) :=
  hasGradientAt_iff_tendsto (Eventually.of_forall fun _ h ↦ congrArg f (Units.ext h))

-- Collapsed coordinate fibers do not discard a nonzero function increment.
example : ¬ HasGradientAtFilter (fun b : Bool ↦ if b then (1 : ℝ) else 0)
    (7 : ℝ) false (pure true) (fun _ ↦ (0 : ℝ)) := by
  rw [hasGradientAtFilter_iff_isLittleO, isLittleO_pure]
  simp

example : HasGradientAtFilter (fun _ : Bool ↦ (3 : ℝ)) (7 : ℝ) false (pure true)
    (fun _ ↦ (0 : ℝ)) := by
  rw [hasGradientAtFilter_iff_isLittleO, isLittleO_pure]
  simp

-- A constant quotient retains its denominator evidence in the derivative statement.
example (c : ℝ → ℝ) (c' x d : ℝ) {hd : IsUnit d} (hc : HasDerivAt c c' x) :
    HasDerivAt (fun y ↦ c y / d) (c' / d) x :=
  hc.div_const d

example (c : ℝ → ℝ) (x d : ℝ) {hd : IsUnit d} :
    deriv (fun y ↦ c y / d) x = deriv c x / d :=
  deriv_div_const d

-- First-order error bounds do not assume coordinate continuity or an ambient vector domain.
example {D : Type*} [TopologicalSpace D] (coord : D → ℝ) (f : D → ℝ) (x : D) (d : ℝ)
    (hf : HasDerivAt f d x coord) :
    (fun y ↦ f y - f x) =O[𝓝 x] (fun y ↦ coord y - coord x) :=
  hf.isBigO_sub

example {D : Type*} [TopologicalSpace D] (coord : D → ℝ) (f : D → ℝ) (x : D) (d q : ℝ)
    {hq : IsUnit q} (hf : HasDerivAt f d x coord) :
    HasDerivAt (fun y ↦ f y / q) (d / q) x coord :=
  hf.div_const q

example {D : Type*} [TopologicalSpace D] (coord : D → ℝ) (f : D → ℝ) (x : D) (q : ℝ)
    (hf : DifferentiableAt ℝ f x coord) :
    DifferentiableAt ℝ (fun y ↦ f y * q) x coord :=
  hf.mul_const q

example {D : Type*} [TopologicalSpace D] (coord : D → ℝ) (f g : D → ℝ) (x : D)
    (hf : DifferentiableAt ℝ f x coord) (hg : DifferentiableAt ℝ g x coord)
    (hcoord : ContinuousAt coord x) : DifferentiableAt ℝ (f * g) x coord :=
  hf.mul hg hcoord
