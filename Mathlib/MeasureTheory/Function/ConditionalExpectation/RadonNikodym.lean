/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalLExpectation
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv
import Mathlib.MeasureTheory.Function.ConditionalExpectation.LebesgueBochner
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# Radon-Nikodym derivatives and conditional expectations

We express the Radon-Nikodym derivative of the pushforward of measures in terms of the conditional
expectation of the Radon-Nikodym derivative of the original measures.

## Main statements

In all statements, `μ` and `ν` are measures with `μ ≪ ν`, and `μ` is s-finite for `condLExp` and
finite for `condExp`.

* `isCondLExp_rnDeriv_map`: the Radon-Nikodym derivative `∂(μ.map g)/∂(ν.map g)` of the pushforward
  of measures by a function `g : 𝓧 → 𝓨`, evaluated at `g x`, is a conditional expectation of
  `∂μ/∂ν` given the comap by `g` of the σ-algebra on `𝓨`.
* `isCondLExp_rnDeriv_trim`: the Radon-Nikodym derivative `∂(μ.trim hm)/∂(ν.trim hm)` of the
  trimmed measures (for `hm : m ≤ m0` stating that `m` is a sub-σ-algebra of `m0`) is a conditional
  expectation of `∂μ/∂ν` given the σ-algebra `m`.

Each statement has a version for the conditional expectation `condLExp` built from the Lebesgue
integral, and one for the conversions of the derivatives to `ℝ` by `ENNReal.toReal` and the
conditional expectation `condExp` built from the Bochner integral. The Radon-Nikodym derivatives on
the coarser σ-algebra are measurable for it, so they are versions of the conditional expectations
that are measurable, not only almost everywhere measurable, for the coarser σ-algebra.

-/

public section

open scoped ENNReal

namespace MeasureTheory

variable {𝓧 𝓨 : Type*} {m m𝓧 : SigmaAlgebra 𝓧} {m𝓨 : SigmaAlgebra 𝓨} {μ ν : Measure 𝓧}

/-- The Radon-Nikodym derivative `∂(μ.map g)/∂(ν.map g)` of the pushforward of measures by
a function `g : 𝓧 → 𝓨`, evaluated at `g x`, is a conditional (Lebesgue) expectation of `∂μ/∂ν`
given the comap by `g` of the σ-algebra on `𝓨`. -/
lemma isCondLExp_rnDeriv_map [SFinite μ] (hμν : μ ≪ ν)
    {g : 𝓧 → 𝓨} (hg : Measurable g) [hσ : SigmaFinite (ν.map g hg.aemeasurable)] :
    IsCondLExp (m𝓨.comap g) ν (μ.rnDeriv ν) fun a ↦
      (μ.map g hg.aemeasurable).rnDeriv (ν.map g hg.aemeasurable) (g a) := by
  have : SigmaFinite ν := SigmaFinite.of_map _ hg.aemeasurable hσ
  refine ⟨((Measure.measurable_rnDeriv _ _).comp
    (comap_measurable g)).stronglyMeasurable.aestronglyMeasurable, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  rw [← setLIntegral_map ht (Measure.measurable_rnDeriv _ _) hg,
    Measure.setLIntegral_rnDeriv' (hμν.map hg) ht, Measure.setLIntegral_rnDeriv' hμν (hg ht),
    Measure.map_apply ht hg.aemeasurable]

/-- The Radon-Nikodym derivative `∂(μ.map g)/∂(ν.map g)` of the pushforward of measures by a
function `g : 𝓧 → 𝓨`, evaluated at `g x` and converted to `ℝ` by `ENNReal.toReal`, is a
conditional expectation of `∂μ/∂ν` converted to `ℝ` given the comap by `g` of the σ-algebra on
`𝓨`. -/
lemma isCondExp_toReal_rnDeriv_map [IsFiniteMeasure μ] (hμν : μ ≪ ν)
    {g : 𝓧 → 𝓨} (hg : Measurable g) [hσ : SigmaFinite (ν.map g hg.aemeasurable)] :
    IsCondExp (m𝓨.comap g) ν (fun a ↦ (μ.rnDeriv ν a).toReal) fun a ↦
      ((μ.map g hg.aemeasurable).rnDeriv (ν.map g hg.aemeasurable) (g a)).toReal := by
  have : SigmaFinite ν := SigmaFinite.of_map _ hg.aemeasurable hσ
  exact (isCondLExp_rnDeriv_map hμν hg).toReal hg.comap_le
    (Measure.measurable_rnDeriv _ _).aemeasurable (by simp [Measure.lintegral_rnDeriv hμν])

/-- The Radon-Nikodym derivative `∂(μ.trim hm)/∂(ν.trim hm)` of the trimmed measures (for
`hm : m ≤ m0` stating that `m` is a sub-σ-algebra of `m0`) is a conditional (Lebesgue) expectation
of `∂μ/∂ν` given the σ-algebra `m`. -/
lemma isCondLExp_rnDeriv_trim (hm : m ≤ m𝓧) [SFinite μ] [SigmaFinite (ν.trim hm)]
    (hμν : μ ≪ ν) : IsCondLExp m ν (μ.rnDeriv ν) ((μ.trim hm).rnDeriv (ν.trim hm)) := by
  have : SigmaFinite ν := SigmaFinite.of_trim hm
  refine ⟨(Measure.measurable_rnDeriv _ _).stronglyMeasurable.aestronglyMeasurable, fun s hs ↦ ?_⟩
  rw [← setLIntegral_trim hm (Measure.measurable_rnDeriv _ _) hs,
    Measure.setLIntegral_rnDeriv' (hμν.trim hm) hs, trim_measurableSet_eq hm hs,
    Measure.setLIntegral_rnDeriv' hμν (hm hs)]

/-- The Radon-Nikodym derivative `∂(μ.trim hm)/∂(ν.trim hm)` of the trimmed measures (for
`hm : m ≤ m0` stating that `m` is a sub-σ-algebra of `m0`), converted to `ℝ` by `ENNReal.toReal`,
is a conditional expectation of `∂μ/∂ν` converted to `ℝ` given the σ-algebra `m`. -/
lemma isCondExp_toReal_rnDeriv_trim (hm : m ≤ m𝓧) [IsFiniteMeasure μ] [SigmaFinite (ν.trim hm)]
    (hμν : μ ≪ ν) :
    IsCondExp m ν (fun x ↦ (μ.rnDeriv ν x).toReal)
      fun x ↦ ((μ.trim hm).rnDeriv (ν.trim hm) x).toReal := by
  have : SigmaFinite ν := SigmaFinite.of_trim hm
  exact (isCondLExp_rnDeriv_trim hm hμν).toReal hm (Measure.measurable_rnDeriv _ _).aemeasurable
    (by simp [Measure.lintegral_rnDeriv hμν])

end MeasureTheory
