/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.Probability.Kernel.Composition.MeasureComp

import Mathlib.Analysis.Convex.Approximation
import Mathlib.Analysis.Convex.Deriv
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.ConditionalExpectation.RadonNikodym
public import Mathlib.Probability.Notation

/-!
# Data processing inequality for the Kullback-Leibler divergence

The data processing inequality is a way to express the intuition that applying a (possibly random)
transformation to random variables cannot increase the information they contain.

## Main statements

We prove three versions of the data processing inequality for the Kullback-Leibler divergence, for
measurable maps, restrictions to sub-sigma-algebras, and composition with Markov kernels.
Let `μ, ν` be finite measures on `𝓧`, with sigma-algebra `m𝓧`.

* `klDiv_map_le`: `klDiv (μ.map g) (ν.map g) ≤ klDiv μ ν` for a measurable function `g`.
* `klDiv_trim_le`: `klDiv (μ.trim hm) (ν.trim hm) ≤ klDiv μ ν` for a sub-sigma-algebra `m` of `m𝓧`
  (with `hm : m ≤ m𝓧`).
* `klDiv_comp_right_le`: `klDiv (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ klDiv μ ν` for a Markov kernel `κ`.

-/

public section

open Real MeasureTheory Set ProbabilityTheory
open scoped ENNReal

namespace ConvexOn

variable {𝓧 𝓨 : Type*} {m m𝓧 : SigmaAlgebra 𝓧} {m𝓨 : SigmaAlgebra 𝓨}
  {μ ν : Measure 𝓧} [IsFiniteMeasure μ] [IsFiniteMeasure ν] {f : ℝ → ℝ} {g : 𝓧 → 𝓨}

omit [IsFiniteMeasure ν] in
/-- **Conditional Jensen inequality** for the Radon-Nikodym derivative: for a function `f` convex on
`[0, ∞)` and continuous at `0`, `f` of a conditional expectation of `(∂μ/∂ν).toReal` given `m` is
almost everywhere at most a conditional expectation of `f ∘ (∂μ/∂ν).toReal`. -/
lemma map_isCondExp_rnDeriv_le (hm : m ≤ m𝓧) (hf_cvx : ConvexOn ℝ (Ici 0) f)
    (hf_cont_at : ContinuousWithinAt f (Ici 0) 0)
    (h_int : Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal) ν) {G k : 𝓧 → ℝ}
    (hG : IsCondExp m ν (fun x ↦ (μ.rnDeriv ν x).toReal) G)
    (hk : IsCondExp m ν (fun x ↦ f (μ.rnDeriv ν x).toReal) k) :
    (fun x ↦ f (G x)) ≤ᵐ[ν] k :=
  hf_cvx.map_condExp_le hm (hf_cvx.continuousOn_Ici hf_cont_at).lowerSemicontinuousOn
    (ae_of_all _ fun _ ↦ ENNReal.toReal_nonneg) isClosed_Ici Measure.integrable_toReal_rnDeriv h_int
    hG hk

/-- For a function `f` convex on `[0, ∞)` and continuous at `0`, `f` of the Radon-Nikodym derivative
of the pushforward measures by `g`, evaluated at `g x`, is almost everywhere at most a conditional
expectation of `f ∘ (∂μ/∂ν).toReal` given `g`. -/
lemma comp_rnDeriv_map_le (hμν : μ ≪ ν) (hg : Measurable g) (hf_cvx : ConvexOn ℝ (Ici 0) f)
    (hf_cont_at : ContinuousWithinAt f (Ici 0) 0)
    (h_int : Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal) ν) {k : 𝓧 → ℝ}
    (hk : IsCondExp (m𝓨.comap g) ν (fun x ↦ f (μ.rnDeriv ν x).toReal) k) :
    (fun x ↦ f ((μ.map g).rnDeriv (ν.map g) (g x)).toReal) ≤ᵐ[ν] k :=
  hf_cvx.map_isCondExp_rnDeriv_le hg.comap_le hf_cont_at h_int
    (isCondExp_toReal_rnDeriv_map hμν hg) hk

lemma integrable_comp_rnDeriv_map (hμν : μ ≪ ν) (hg : Measurable g) (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont_at : ContinuousWithinAt f (Ici 0) 0)
    (h_int : Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal) ν) :
    Integrable (fun x ↦ f ((μ.map g).rnDeriv (ν.map g) x).toReal) (ν.map g) := by
  have hf_cont : ContinuousOn f (Ici 0) := hf_cvx.continuousOn_Ici hf_cont_at
  obtain ⟨c, c', h⟩ : ∃ c c', ∀ x, 0 ≤ x → c * x + c' ≤ f x :=
    hf_cvx.exists_affine_le_real isClosed_Ici hf_cont.lowerSemicontinuousOn
  obtain ⟨k, -, hk⟩ := exists_stronglyMeasurable_isCondExp hg.comap_le h_int
  rw [integrable_map_measure hg.aemeasurable
    (StronglyMeasurable.aestronglyMeasurable (by fun_prop))]
  refine integrable_of_le_of_le (f := fun x ↦ f ((∂μ.map g/∂ν.map g) (g x)).toReal)
    (g₁ := fun x ↦ c * ((∂μ.map g/∂ν.map g) (g x)).toReal + c') (g₂ := k)
    ?_ ?_ ?_ ?_ (hk.integrable h_int)
  · exact StronglyMeasurable.aestronglyMeasurable (by fun_prop)
  · exact ae_of_all _ (fun x ↦ h _ ENNReal.toReal_nonneg)
  · exact hf_cvx.comp_rnDeriv_map_le hμν hg hf_cont_at h_int hk
  · exact (Integrable.const_mul ((isCondExp_toReal_rnDeriv_map hμν hg).integrable
      Measure.integrable_toReal_rnDeriv) _).add (integrable_const _)

/-- For a function `f` convex on `[0, ∞)` and continuous at `0`, `f` of the Radon-Nikodym derivative
of the trimmed measures is almost everywhere at most a conditional expectation of
`f ∘ (∂μ/∂ν).toReal` given `m`. -/
lemma comp_rnDeriv_trim_le (hm : m ≤ m𝓧) (hμν : μ ≪ ν) (hf_cvx : ConvexOn ℝ (Ici 0) f)
    (hf_cont_at : ContinuousWithinAt f (Ici 0) 0)
    (h_int : Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal) ν) {k : 𝓧 → ℝ}
    (hk : IsCondExp m ν (fun x ↦ f (μ.rnDeriv ν x).toReal) k) :
    (fun x ↦ f ((∂μ.trim hm/∂ν.trim hm) x).toReal) ≤ᵐ[ν] k :=
  hf_cvx.map_isCondExp_rnDeriv_le hm hf_cont_at h_int (isCondExp_toReal_rnDeriv_trim hm hμν) hk

lemma integrable_comp_rnDeriv_trim (hm : m ≤ m𝓧) (hμν : μ ≪ ν) (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont_at : ContinuousWithinAt f (Ici 0) 0)
    (h_int : Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal) ν) :
    Integrable (fun x ↦ f ((μ.trim hm).rnDeriv (ν.trim hm) x).toReal) (ν.trim hm) := by
  simpa only [trim_eq_map hm] using
    hf_cvx.integrable_comp_rnDeriv_map hμν (measurable_id'' hm) hf hf_cont_at h_int

/-- For a function `f` convex on `[0, ∞)` and continuous at `0`, `f` of a conditional expectation of
`(∂μ/∂ν).toReal` given `m` is integrable. -/
lemma integrable_comp_isCondExp_rnDeriv (hm : m ≤ m𝓧) (hμν : μ ≪ ν) (hf : StronglyMeasurable f)
    (hf_cvx : ConvexOn ℝ (Ici 0) f) (hf_cont_at : ContinuousWithinAt f (Ici 0) 0)
    (h_int : Integrable (fun x ↦ f (μ.rnDeriv ν x).toReal) ν) {G : 𝓧 → ℝ}
    (hG : IsCondExp m ν (fun x ↦ (μ.rnDeriv ν x).toReal) G) :
    Integrable (fun x ↦ f (G x)) ν := by
  have h := integrable_of_integrable_trim hm
    (integrable_comp_rnDeriv_trim hm hμν hf hf_cvx hf_cont_at h_int)
  refine (integrable_congr ?_).mp h
  filter_upwards [(isCondExp_toReal_rnDeriv_trim hm hμν).ae_eq hm
    Measure.integrable_toReal_rnDeriv hG] with a ha
  rw [ha]

end ConvexOn

namespace InformationTheory

variable {𝓧 𝓨 : Type*} {m m𝓧 : SigmaAlgebra 𝓧} {m𝓨 : SigmaAlgebra 𝓨} {μ ν : Measure 𝓧}
  [IsFiniteMeasure μ] [IsFiniteMeasure ν] {g : 𝓧 → 𝓨}

lemma integrable_llr_map (hμν : μ ≪ ν) (hg : Measurable g)
    (h_int : Integrable (llr μ ν) μ) :
    Integrable (llr (μ.map g) (ν.map g)) (μ.map g) := by
  rw [← integrable_klFun_rnDeriv_iff (hμν.map hg)]
  refine convexOn_klFun.integrable_comp_rnDeriv_map hμν hg (by fun_prop) (by fun_prop) ?_
  rwa [integrable_klFun_rnDeriv_iff hμν]

lemma toReal_klDiv_map_of_ac (hμν : μ ≪ ν) (hg : Measurable g) :
    (klDiv (μ.map g) (ν.map g)).toReal =
      ∫ x, klFun ((μ.map g).rnDeriv (ν.map g) (g x)).toReal ∂ν := by
  rw [toReal_klDiv_eq_integral_klFun (hμν.map hg), integral_map hg.aemeasurable
      (StronglyMeasurable.aestronglyMeasurable (by fun_prop))]

lemma klDiv_map_of_ac (hμν : μ ≪ ν) (hg : Measurable g) (h_int : Integrable (llr μ ν) μ) :
    klDiv (μ.map g) (ν.map g) =
      ENNReal.ofReal (∫ x, klFun ((μ.map g).rnDeriv (ν.map g) (g x)).toReal ∂ν) := by
  rw [klDiv_eq_integral_klFun, ite_eq_left ⟨hμν.map hg, integrable_llr_map hμν hg h_int⟩]
  congr
  rw [← toReal_klDiv_eq_integral_klFun (hμν.map hg), toReal_klDiv_map_of_ac hμν hg]

lemma toReal_klDiv_trim_of_ac (hm : m ≤ m𝓧) (hμν : μ ≪ ν) :
    (klDiv (μ.trim hm) (ν.trim hm)).toReal =
      ∫ x, klFun ((μ.trim hm).rnDeriv (ν.trim hm) x).toReal ∂ν := by
  simp [trim_eq_map, toReal_klDiv_map_of_ac hμν (measurable_id'' hm)]

variable (μ ν) in
/-- **Data processing inequality** for the Kullback-Leibler divergence and measurable functions. -/
theorem klDiv_map_le (hg : Measurable g) : klDiv (μ.map g) (ν.map g) ≤ klDiv μ ν := by
  by_cases hμν : μ ≪ ν
  swap; · simp [hμν]
  by_cases h_int : Integrable (llr μ ν) μ
  swap; · simp [klDiv_of_not_integrable h_int]
  rw [klDiv_map_of_ac hμν hg h_int, klDiv_eq_integral_klFun]
  simp only [hμν, h_int, and_self, ↓reduceIte]
  have hf : StronglyMeasurable klFun := by fun_prop
  have hf_cont : ContinuousWithinAt klFun (Ici 0) 0 := by fun_prop
  have h_int' : Integrable (fun x ↦ klFun (μ.rnDeriv ν x).toReal) ν := by
    rwa [integrable_klFun_rnDeriv_iff hμν]
  -- a conditional expectation of `klFun ∘ (∂μ/∂ν).toReal` given `g` has its integral
  obtain ⟨k, -, hk⟩ := exists_stronglyMeasurable_isCondExp hg.comap_le h_int'
  conv_rhs => rw [← hk.integral_eq h_int']
  gcongr 1
  refine integral_mono_ae ?_ (hk.integrable h_int') ?_
  · exact (convexOn_klFun.integrable_comp_rnDeriv_map hμν hg hf hf_cont h_int').comp_measurable hg
  · exact convexOn_klFun.comp_rnDeriv_map_le hμν hg hf_cont h_int' hk

variable (μ ν) in
/-- **Data processing inequality** for the Kullback-Leibler divergence and sub-sigma-algebras. -/
theorem klDiv_trim_le (hm : m ≤ m𝓧) : klDiv (μ.trim hm) (ν.trim hm) ≤ klDiv μ ν := by
  simp_rw [trim_eq_map]
  exact klDiv_map_le μ ν (measurable_id'' hm)

variable (μ ν) in
/-- The **Data Processing Inequality** for the Kullback-Leibler divergence and a Markov kernel. -/
theorem klDiv_comp_right_le (κ : Kernel 𝓧 𝓨) [IsMarkovKernel κ] :
    klDiv (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ klDiv μ ν :=
  calc klDiv (κ ∘ₘ μ) (κ ∘ₘ ν)
  _ ≤ klDiv (μ ⊗ₘ κ) (ν ⊗ₘ κ) := by
    simp only [← Measure.snd_compProd]
    exact klDiv_map_le _ _ measurable_snd
  _ = klDiv μ ν := klDiv_compProd_left μ ν κ

end InformationTheory
