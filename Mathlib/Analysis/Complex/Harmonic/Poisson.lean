/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mihai Iancu, Stefan Kebekus, Sebastian Schleissinger
-/
module

public import Mathlib.Analysis.Complex.Poisson
public import Mathlib.Analysis.Complex.Harmonic.Analytic
public import Mathlib.Analysis.InnerProductSpace.Harmonic.HarmonicContOnCl

/-!
# Poisson Integral Formula

This file establishes several versions of the **Poisson Integral Formula** for harmonic functions on
arbitrary disks in the complex plane, formulated with the real part of the Herglotz–Riesz kernel of
integration and with the Poisson kernel, respectively.

TODO: Extend this formula to vector-valued harmonic functions
-/

public section

open Complex InnerProductSpace Metric Real Set MeasureTheory

open scoped Topology

variable
  {f : ℂ → ℝ} {c w : ℂ} {R : ℝ}

namespace InnerProductSpace

/-- The Poisson integral formula for harmonic functions on a neighborhood of the closed disk. -/
theorem HarmonicOnNhd.circleAverage_re_herglotzRieszKernel_smul
    (hf : HarmonicOnNhd f (closedBall c R)) (hw : w ∈ ball c R) :
    Real.circleAverageOn (fun z : sphere c |R| ↦
      (herglotzRieszKernel c w ⟨z.val, mem_compl_singleton_iff.mpr
        (sub_ne_zero.mp (isUnit_sub_of_mem_sphere_of_mem_ball hw z).ne_zero)⟩).re •
        f z.val) = f w := by
  have hR : 0 < R := pos_of_mem_ball hw
  obtain ⟨e, he, h'⟩ := (isCompact_closedBall c R).exists_thickening_subset_open
    (isOpen_setOfPred_harmonicAt f) (by aesop)
  rw [thickening_closedBall he hR.le] at h'
  obtain ⟨F, hF, hre⟩ := HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq h'
  have hF' : DifferentiableOn ℂ F (closure (ball c R)) := by
    intro x hx
    apply (hF x _).differentiableWithinAt
    grind [mem_ball, mem_closedBall.1 (closure_ball_subset_closedBall hx)]
  let S := sphere c |R|
  let p (z : S) : ({w}ᶜ : Set ℂ) := ⟨z.val, mem_compl_singleton_iff.mpr
    (sub_ne_zero.mp (isUnit_sub_of_mem_sphere_of_mem_ball hw z).ne_zero)⟩
  let k (z : S) : ℝ := (herglotzRieszKernel c w (p z)).re
  have hk : Continuous k :=
    (continuous_re.comp (continuous_herglotzRieszKernel c w)).comp
      (continuous_subtype_val.subtype_mk _)
  have hS (z : S) : z.val ∈ ball c (e + R) := by
    apply sphere_subset_ball (lt_add_of_pos_left R he)
    simpa only [S, abs_of_pos hR] using z.2
  let Z (θ : ℝ) : S := ⟨circleMap c |R| θ, circleMap_mem_sphere c (abs_nonneg R) θ⟩
  have hZ : Continuous Z := (continuous_circleMap c |R|).subtype_mk _
  have hFZ : Continuous (fun θ : ℝ ↦ F (Z θ).val) := by
    refine continuous_iff_continuousAt.2 fun θ ↦ ?_
    change ContinuousAt (F ∘ circleMap c |R|) θ
    have hFc : ContinuousAt F (circleMap c |R| θ) := (hF _ (hS (Z θ))).continuousAt
    exact hFc.comp (continuous_circleMap c |R|).continuousAt
  have hi : IntervalIntegrable (fun θ : ℝ ↦ k (Z θ) • F (Z θ).val) volume 0 (2 * π) :=
    ((hk.comp hZ).smul hFZ).intervalIntegrable _ _
  have hAvg : Real.circleAverageOn (fun z : S ↦ k z • F z.val) = F w :=
    hF'.diffContOnCl.circleAverage_re_herglotzRieszKernel_smul hw
  have hpoint (z : S) : k z • f z.val = Complex.reCLM (k z • F z.val) := by
    have hz : (F z.val).re = f z.val := hre (hS z)
    rw [map_smul, Complex.reCLM_apply, hz]
  have hFw : (F w).re = f w := hre (ball_subset_ball (lt_add_of_pos_left R he).le hw)
  have hAvgRe := congrArg Complex.reCLM hAvg
  simp only [Real.circleAverageOn, map_smul] at hAvgRe
  rw [← Complex.reCLM.intervalIntegral_comp_comm hi] at hAvgRe
  change Real.circleAverageOn (fun z : S ↦ k z • f z.val) = f w
  simp only [hpoint, Real.circleAverageOn]
  simpa only [Function.comp_apply, Complex.reCLM_apply, hFw] using hAvgRe

/-- The Poisson integral formula for harmonic functions continuous on the closed disk. -/
theorem HarmonicContOnCl.circleAverage_re_herglotzRieszKernel_smul
    (hf : HarmonicContOnCl f (ball c R)) (hw : w ∈ ball c R) :
    Real.circleAverageOn (fun z : sphere c |R| ↦
      (herglotzRieszKernel c w ⟨z.val, mem_compl_singleton_iff.mpr
        (sub_ne_zero.mp (isUnit_sub_of_mem_sphere_of_mem_ball hw z).ne_zero)⟩).re •
        f z.val) = f w := by
  let U : Set ℂ := {w}ᶜ
  let G : ℂ → ℝ := Function.extend (Subtype.val : U → ℂ)
    (fun z : U ↦ (herglotzRieszKernel c w z).re • f z.val) 0
  have hG (z : U) : G z.val = (herglotzRieszKernel c w z).re • f z.val :=
    Subtype.val_injective.extend_apply _ _ z
  have hrepr {r : ℝ} (hwr : w ∈ ball c r) :
      Real.circleAverage G c r = Real.circleAverageOn (fun z : sphere c |r| ↦
        (herglotzRieszKernel c w ⟨z.val, mem_compl_singleton_iff.mpr
          (sub_ne_zero.mp (isUnit_sub_of_mem_sphere_of_mem_ball hwr z).ne_zero)⟩).re •
          f z.val) := by
    rw [← Real.circleAverageOn_restrict (f := G)]
    congr 1
    funext z
    exact hG ⟨z.val, mem_compl_singleton_iff.mpr
      (sub_ne_zero.mp (isUnit_sub_of_mem_sphere_of_mem_ball hwr z).ne_zero)⟩
  rw [← hrepr hw]
  apply ContinuousOn.eq_of_eqOn_Ioo (r := ‖w - c‖)
  · apply ContinuousOn.circleAverage
    · let s : Set ℂ := {z : ℂ | ‖z - c‖ ∈ Ioc ‖w - c‖ R}
      have hsub (z : s) : z.val ∈ U :=
        mem_compl_singleton_iff.mpr (ne_of_apply_ne (fun y ↦ ‖y - c‖) z.2.1.ne')
      let p (z : s) : U := ⟨z.val, hsub z⟩
      have hp : Continuous p := continuous_subtype_val.subtype_mk _
      have hf' : Continuous (fun z : s ↦ f z.val) := by
        apply continuousOn_iff_continuous_domRestrict.mp
        apply hf.2.mono
        rw [closure_ball c (pos_of_mem_ball hw).ne']
        exact fun z hz ↦ mem_closedBall_iff_norm.mpr hz.2
      have hc : Continuous (fun z : s ↦ (herglotzRieszKernel c w (p z)).re • f z.val) :=
        ((continuous_re.comp (continuous_herglotzRieszKernel c w)).comp hp).smul hf'
      apply continuousOn_iff_continuous_domRestrict.mpr
      have heq : (fun z : s ↦ G z.val) = fun z : s ↦
          (herglotzRieszKernel c w (p z)).re • f z.val := funext fun z ↦ hG (p z)
      rw [show s.domRestrict G = (fun z : s ↦ G z.val) from rfl, heq]
      exact hc
    · exact fun _ hr ↦ (norm_nonneg _).trans hr.1.le
  · exact mem_ball_iff_norm.mp hw
  · intro r hr
    have hw' : w ∈ ball c r := mem_ball_iff_norm.mpr hr.1
    rw [hrepr hw']
    exact (hf.1.mono (closedBall_subset_ball hr.2)).circleAverage_re_herglotzRieszKernel_smul hw'

/-- The Poisson-kernel formula for harmonic functions on a neighborhood of the closed disk. -/
theorem HarmonicOnNhd.circleAverage_poissonKernel_smul
    (hf : HarmonicOnNhd f (closedBall c R)) (hw : w ∈ ball c R) :
    Real.circleAverageOn (fun z : sphere c |R| ↦
      poissonKernel c w ⟨z.val, mem_compl_singleton_iff.mpr
        (sub_ne_zero.mp (isUnit_sub_of_mem_sphere_of_mem_ball hw z).ne_zero)⟩ • f z.val) = f w := by
  simpa only [poissonKernel_eq_re_herglotzRieszKernel, Function.comp_apply] using
    hf.circleAverage_re_herglotzRieszKernel_smul hw

/-- The Poisson-kernel formula for harmonic functions continuous on the closed disk. -/
theorem HarmonicContOnCl.circleAverage_poissonKernel_smul
    (hf : HarmonicContOnCl f (ball c R)) (hw : w ∈ ball c R) :
    Real.circleAverageOn (fun z : sphere c |R| ↦
      poissonKernel c w ⟨z.val, mem_compl_singleton_iff.mpr
        (sub_ne_zero.mp (isUnit_sub_of_mem_sphere_of_mem_ball hw z).ne_zero)⟩ • f z.val) = f w := by
  simpa only [poissonKernel_eq_re_herglotzRieszKernel, Function.comp_apply] using
    hf.circleAverage_re_herglotzRieszKernel_smul hw


end InnerProductSpace
