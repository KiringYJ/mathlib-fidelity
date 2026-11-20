/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Analysis.Normed.Module.Basic

/-! # A lemma about measurability with density under scalar multiplication in normed spaces -/

public section


open MeasureTheory Filter ENNReal Set

open NNReal ENNReal

variable {α : Type*} {m : SigmaAlgebra α} {μ : MeasureTheory.Measure α}

theorem aemeasurable_withDensity_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [SecondCountableTopology E] [SigmaAlgebra E] [BorelSpace E] {f : α → ℝ≥0}
    (hf : Measurable f) {g : α → E} :
    AEMeasurable g (μ.withDensity fun x => (f x : ℝ≥0∞)) ↔
      AEMeasurable (fun x => (f x : ℝ) • g x) μ := by
  constructor
  · rintro ⟨g', g'meas, hg'⟩
    have A : MeasurableSet { x : α | f x ≠ 0 } :=
      MeasurableSet.compl (hf (measurableSet_singleton 0))
    refine ⟨fun x => (f x : ℝ) • g' x, hf.coe_nnreal_real.smul g'meas, ?_⟩
    apply @ae_of_ae_restrict_of_ae_restrict_compl _ _ _ { x | f x ≠ 0 }
    · rw [EventuallyEq, ae_withDensity_iff hf.coe_nnreal_ennreal] at hg'
      rw [ae_restrict_iff' A]
      filter_upwards [hg']
      intro a ha h'a
      have : (f a : ℝ≥0∞) ≠ 0 := by simpa only [Ne, ENNReal.coe_eq_zero] using h'a
      rw [ha this]
    · filter_upwards [ae_restrict_mem A.compl]
      intro x hx
      simp only [Classical.not_not, mem_ofPred_eq, mem_compl_iff] at hx
      simp [hx]
  · rintro ⟨g', g'meas, hg'⟩
    refine ⟨fun x => ((f x : ℝ≥0∞)⁻¹).toReal • g' x,
      hf.coe_nnreal_ennreal.inv.ennreal_toReal.smul g'meas, ?_⟩
    rw [EventuallyEq, ae_withDensity_iff hf.coe_nnreal_ennreal]
    filter_upwards [hg']
    intro x hx h'x
    have hu : IsUnit (f x : ℝ) := (NNReal.coe_ne_zero.2 (ENNReal.coe_ne_zero.1 h'x)).isUnit
    rw [ENNReal.toReal_inv (f x : ℝ≥0∞) (ha := by simpa only [ENNReal.coe_toReal] using hu)]
    change g x = Checked.inv (f x : ℝ) hu • g' x
    rw [← hx, smul_smul, inv_mul_cancel₀, one_smul]
