/-
Copyright (c) 2025 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue
public import Mathlib.Order.Filter.Germ.Representative

import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Probability.Notation
public import Mathlib.Probability.Notation

/-! # Conditional Lebesgue expectation

Given a measure `P` on a σ-algebra `m₀` and a σ-algebra `m`, a function `G : Ω → ℝ≥0∞` is a
conditional (Lebesgue) expectation of `X : Ω → ℝ≥0∞` given `m`, written `IsCondLExp m P X G`, when
`G` is almost everywhere `m`-measurable and `∫⁻ ω in s, G ω ∂P = ∫⁻ ω in s, X ω ∂P` for all
`s ∈ m`. Unlike the Bochner conditional expectation, no integrability is needed.

A conditional expectation is determined only up to almost everywhere equality. The conditional
expectation `P⁻[X | m] = condLExp m P X` is therefore the almost everywhere class of the conditional
expectations of `X`, a germ along `ae P`; `G ∈ P⁻[X | m]` exactly when `IsCondLExp m P X G`.

## Domain

`condLExp m P X` takes a proof of `HasUniqueCondLExp m P X`: the sets of `m` are null-measurable for
`P`, so that the restricted measures in the defining identity do not follow the outer-measure
convention of `Measure.restrict`; the lower integral `∫⁻` of `X` over each set of `m` is also its
upper integral, so that the identity does not depend on the convention for the integral of a
function that is not measurable; a conditional expectation exists; and any two agree almost
everywhere. On the inputs where the defining identity is independent of these conventions, this is
the exact domain of the conditional expectation. The tactic `has_unique_cond_lexp` finds it from a
hypothesis or from the sufficient condition `HasUniqueCondLExp.of_aemeasurable`: an almost
everywhere measurable `X` and a sub-σ-algebra `hm : m ≤ m₀` on which `P` is σ-finite.

## Main definitions

* `MeasureTheory.IsCondLExp m P X G`: `G` is a conditional (Lebesgue) expectation of `X` given `m`.
* `MeasureTheory.HasUniqueCondLExp m P X`: `X` has a conditional (Lebesgue) expectation given
  `m`, unique almost everywhere.
* `MeasureTheory.condLExp m P X`, with notation `P⁻[X | m]`: the almost everywhere class of the
  conditional (Lebesgue) expectations of `X`.

## Main results

* `MeasureTheory.exists_measurable_isCondLExp`: given a sub-σ-algebra on which `P` is σ-finite,
  every function has an `m`-measurable conditional (Lebesgue) expectation, a Radon-Nikodym
  derivative.
* `MeasureTheory.IsCondLExp.ae_eq`: conditional (Lebesgue) expectations given a σ-finite
  sub-σ-algebra agree almost everywhere.

## To do

* Prove the pullout property
* Prove a dominated convergence theorem.

-/

public section

open MeasureTheory Measure Filter

open scoped ProbabilityTheory

open scoped ENNReal

namespace MeasureTheory

variable {Ω : Type*} {m m₀ : SigmaAlgebra Ω} {P : Measure[m₀] Ω} {X Y G H K : Ω → ℝ≥0∞}

section Definitions

/-- A function `G` is a conditional (Lebesgue) expectation of `X` given the σ-algebra `m` with
respect to the measure `P`: `G` is almost everywhere `m`-measurable and has the same Lebesgue
integral as `X` over each set of `m`. See `MeasureTheory.HasUniqueCondLExp` for the functions whose
conditional expectation is unique. -/
structure IsCondLExp (m : SigmaAlgebra Ω) {m₀ : SigmaAlgebra Ω} (P : Measure[m₀] Ω)
    (X G : Ω → ℝ≥0∞) : Prop where
  /-- A conditional expectation given `m` is almost everywhere equal to an `m`-measurable
  function. -/
  aestronglyMeasurable : AEStronglyMeasurable[m] G P
  /-- A conditional expectation has the integral of `X` over each set of `m`. -/
  setLIntegral_eq : ∀ s ∈ m, ∫⁻ ω in s, G ω ∂P = ∫⁻ ω in s, X ω ∂P

/-- The function `X` has a conditional (Lebesgue) expectation given `m` with respect to `P` that is
unique almost everywhere: the sets of `m` are null-measurable, the lower integral of `X` over each
set of `m` is its upper integral, the infimum of the integrals of its measurable majorants, a
conditional expectation exists, and any two agree almost everywhere.

The first two conditions exclude the inputs on which the defining identity depends on the
outer-measure convention of `Measure.restrict` or on the convention for the lower integral of a
function that is not measurable. With them, this is the exact domain of `MeasureTheory.condLExp`.
The tactic `has_unique_cond_lexp` derives it from the sufficient condition
`MeasureTheory.HasUniqueCondLExp.of_aemeasurable`. -/
structure HasUniqueCondLExp (m : SigmaAlgebra Ω) {m₀ : SigmaAlgebra Ω} (P : Measure[m₀] Ω)
    (X : Ω → ℝ≥0∞) : Prop where
  /-- The sets of `m` are null-measurable. -/
  le_eventuallySigmaAlgebra : m ≤ eventuallySigmaAlgebra m₀ (ae P)
  /-- The lower integral of `X` over each set of `m` is its upper integral. -/
  setLIntegral_eq_iInf : ∀ s ∈ m, ∫⁻ ω in s, X ω ∂P =
    ⨅ (Y : Ω → ℝ≥0∞) (_ : Measurable Y) (_ : X ≤ Y), ∫⁻ ω in s, Y ω ∂P
  /-- A conditional expectation exists. -/
  exists_isCondLExp : ∃ G, IsCondLExp m P X G
  /-- Two conditional expectations agree almost everywhere. -/
  ae_eq_of_isCondLExp ⦃G₁ G₂ : Ω → ℝ≥0∞⦄ :
    IsCondLExp m P X G₁ → IsCondLExp m P X G₂ → G₁ =ᵐ[P] G₂

end Definitions

/-- A function almost everywhere equal to an `m`-measurable function into `ℝ≥0∞` is almost
everywhere `m`-strongly measurable, for a measure on another σ-algebra. -/
private theorem aestronglyMeasurable_of_ae_eq {G' : Ω → ℝ≥0∞} (hG' : Measurable[m] G')
    (h : G =ᵐ[P] G') : AEStronglyMeasurable[m] G P :=
  ⟨G', hG'.stronglyMeasurable, h⟩

/-- The lower integral of an almost everywhere measurable function over any set is its upper
integral. -/
theorem setLIntegral_eq_iInf_of_aemeasurable (hX : AEMeasurable[m₀] X P) (s : Set Ω) :
    ∫⁻ ω in s, X ω ∂P = ⨅ (Y : Ω → ℝ≥0∞) (_ : Measurable Y) (_ : X ≤ Y), ∫⁻ ω in s, Y ω ∂P := by
  refine le_antisymm (le_iInf₂ fun Y _ ↦ le_iInf fun hXY ↦ lintegral_mono hXY) ?_
  obtain ⟨N, hNs, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hX.ae_eq_mk)
  classical
  let Y : Ω → ℝ≥0∞ := N.piecewise (fun _ ↦ ∞) (hX.mk X)
  have hYm : Measurable Y := Measurable.piecewise hNm measurable_const hX.measurable_mk
  have hXY : X ≤ Y := fun ω ↦ by
    by_cases hω : ω ∈ N
    · simp [Y, hω]
    · have : X ω = hX.mk X ω := by
        by_contra h
        exact hω (hNs h)
      simp [Y, hω, this]
  have hYX : Y =ᵐ[P] X := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0, hX.ae_eq_mk] with ω hω hω'
    simp [Y, hω, hω']
  exact (iInf₂_le Y hYm).trans ((iInf_le _ hXY).trans
    (lintegral_congr_ae (ae_restrict_of_ae hYX)).le)

/-! ### Conditional expectations as a relation -/

namespace IsCondLExp

theorem congr_left (h : IsCondLExp m P X G) (hXY : X =ᵐ[P] Y) : IsCondLExp m P Y G where
  aestronglyMeasurable := h.aestronglyMeasurable
  setLIntegral_eq s hs := by
    rw [h.setLIntegral_eq s hs]
    exact lintegral_congr_ae (ae_restrict_of_ae hXY)

theorem congr_right (h : IsCondLExp m P X G) (hGH : G =ᵐ[P] H) : IsCondLExp m P X H where
  aestronglyMeasurable := h.aestronglyMeasurable.congr hGH
  setLIntegral_eq s hs := by
    rw [← h.setLIntegral_eq s hs]
    exact lintegral_congr_ae (ae_restrict_of_ae hGH.symm)

theorem lintegral_eq (h : IsCondLExp m P X G) : ∫⁻ ω, G ω ∂P = ∫⁻ ω, X ω ∂P := by
  simpa only [setLIntegral_univ] using h.setLIntegral_eq _ m.univ_mem

/-- A conditional expectation of `X` given `m` has an `m`-measurable version. -/
theorem exists_measurable (h : IsCondLExp m P X G) :
    ∃ G', Measurable[m] G' ∧ G =ᵐ[P] G' ∧ IsCondLExp m P X G' :=
  ⟨h.aestronglyMeasurable.mk G, h.aestronglyMeasurable.stronglyMeasurable_mk.measurable,
    h.aestronglyMeasurable.ae_eq_mk, h.congr_right h.aestronglyMeasurable.ae_eq_mk⟩

/-- A conditional expectation given a sub-σ-algebra is almost everywhere measurable. -/
theorem aemeasurable' (hm : m ≤ m₀) (h : IsCondLExp m P X G) : AEMeasurable[m₀] G P :=
  let ⟨_, hG'm, hGG', _⟩ := h.exists_measurable
  (hG'm.mono hm le_rfl).aemeasurable.congr hGG'.symm

/-- Two conditional expectations given a σ-finite sub-σ-algebra agree almost everywhere. -/
theorem ae_eq (hm : m ≤ m₀) [SigmaFinite (P.trim hm)] (h₁ : IsCondLExp m P X G)
    (h₂ : IsCondLExp m P X H) : G =ᵐ[P] H := by
  obtain ⟨G', hG'm, hGG', h₁'⟩ := h₁.exists_measurable
  obtain ⟨H', hH'm, hHH', h₂'⟩ := h₂.exists_measurable
  refine hGG'.trans (EventuallyEq.trans ?_ hHH'.symm)
  refine ae_eq_of_ae_eq_trim (ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite₀ hG'm.aemeasurable
    hH'm.aemeasurable fun s hs _ ↦ ?_)
  have hs' : s ∈ m := measurableSet_iff_mem.mp hs
  rw [setLIntegral_trim hm hG'm hs', setLIntegral_trim hm hH'm hs', h₁'.setLIntegral_eq s hs',
    h₂'.setLIntegral_eq s hs']

/-- Conditional expectations given a σ-finite sub-σ-algebra are monotone. -/
theorem mono (hm : m ≤ m₀) [SigmaFinite (P.trim hm)] (h : IsCondLExp m P X G)
    (h' : IsCondLExp m P Y H) (hXY : X ≤ᵐ[P] Y) : G ≤ᵐ[P] H := by
  obtain ⟨G', hG'm, hGG', hG'⟩ := h.exists_measurable
  obtain ⟨H', hH'm, hHH', hH'⟩ := h'.exists_measurable
  refine hGG'.trans_le (EventuallyLE.trans ?_ hHH'.symm.le)
  refine ae_le_of_ae_le_trim (ae_le_of_forall_setLIntegral_le_of_sigmaFinite hG'm
    fun s hs _ ↦ ?_)
  have hs' : s ∈ m := measurableSet_iff_mem.mp hs
  rw [setLIntegral_trim hm hG'm hs', setLIntegral_trim hm hH'm hs', hG'.setLIntegral_eq s hs',
    hH'.setLIntegral_eq s hs']
  exact setLIntegral_mono_ae' (hm hs') (hXY.mono fun _ h _ ↦ h)

/-- If `G` and `H` are conditional expectations of `X` and `Y` and `X` is almost everywhere
measurable, then `G + H` is a conditional expectation of `X + Y`. -/
theorem add_left (hm : m ≤ m₀) (h : IsCondLExp m P X G) (h' : IsCondLExp m P Y H)
    (hX : AEMeasurable[m₀] X P) : IsCondLExp m P (X + Y) (G + H) where
  aestronglyMeasurable := h.aestronglyMeasurable.add h'.aestronglyMeasurable
  setLIntegral_eq s hs := by
    simp only [Pi.add_apply]
    rw [lintegral_add_left' (h.aemeasurable' hm).restrict, lintegral_add_left' hX.restrict,
      h.setLIntegral_eq s hs, h'.setLIntegral_eq s hs]

theorem add_right (hm : m ≤ m₀) (h : IsCondLExp m P X G) (h' : IsCondLExp m P Y H)
    (hY : AEMeasurable[m₀] Y P) : IsCondLExp m P (X + Y) (G + H) := by
  simpa only [add_comm] using h'.add_left hm h hY

/-- Conditional expectations are superadditive: for any `X` and `Y`, the sum of conditional
expectations of `X` and `Y` is almost everywhere below one of `X + Y`. -/
theorem add_le (hm : m ≤ m₀) [SigmaFinite (P.trim hm)] (h : IsCondLExp m P X G)
    (h' : IsCondLExp m P Y H) (h'' : IsCondLExp m P (X + Y) K) : G + H ≤ᵐ[P] K := by
  obtain ⟨G', hG'm, hGG', hG'⟩ := h.exists_measurable
  obtain ⟨H', hH'm, hHH', hH'⟩ := h'.exists_measurable
  obtain ⟨K', hK'm, hKK', hK'⟩ := h''.exists_measurable
  refine (hGG'.add hHH').trans_le (EventuallyLE.trans ?_ hKK'.symm.le)
  refine ae_le_of_ae_le_trim (ae_le_of_forall_setLIntegral_le_of_sigmaFinite
    (hG'm.add hH'm) fun s hs _ ↦ ?_)
  have hs' : s ∈ m := measurableSet_iff_mem.mp hs
  rw [setLIntegral_trim hm (hG'm.add hH'm) hs', setLIntegral_trim hm hK'm hs']
  simp only [Pi.add_apply]
  rw [lintegral_add_left ((hG'm.mono hm le_rfl)), hG'.setLIntegral_eq s hs',
    hH'.setLIntegral_eq s hs', hK'.setLIntegral_eq s hs']
  exact le_lintegral_add _ _

/-- A finite multiple of a conditional expectation of `X` is one of the multiple of `X`. -/
theorem const_smul (h : IsCondLExp m P X G) {c : ℝ≥0∞} (hc : c ≠ ∞) :
    IsCondLExp m P (c • X) (c • G) where
  aestronglyMeasurable :=
    let ⟨_, hG'm, hGG', _⟩ := h.exists_measurable
    aestronglyMeasurable_of_ae_eq (hG'm.const_smul c) (hGG'.const_smul c)
  setLIntegral_eq s hs := by
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [lintegral_const_mul' _ _ hc, lintegral_const_mul' _ _ hc, h.setLIntegral_eq s hs]

/-- A multiple of a conditional expectation of an almost everywhere measurable `X` is one of the
multiple of `X`. -/
theorem const_smul_of_aemeasurable (hm : m ≤ m₀) (h : IsCondLExp m P X G)
    (hX : AEMeasurable[m₀] X P) (c : ℝ≥0∞) : IsCondLExp m P (c • X) (c • G) where
  aestronglyMeasurable :=
    let ⟨_, hG'm, hGG', _⟩ := h.exists_measurable
    aestronglyMeasurable_of_ae_eq (hG'm.const_smul c) (hGG'.const_smul c)
  setLIntegral_eq s hs := by
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [lintegral_const_mul'' _ (h.aemeasurable' hm).restrict, lintegral_const_mul'' _ hX.restrict,
      h.setLIntegral_eq s hs]

/-- A multiple of a conditional expectation of `X` is almost everywhere below one of the multiple
of `X`. -/
theorem const_smul_le (hm : m ≤ m₀) [SigmaFinite (P.trim hm)] (h : IsCondLExp m P X G) {c : ℝ≥0∞}
    (h' : IsCondLExp m P (c • X) H) : c • G ≤ᵐ[P] H := by
  obtain ⟨G', hG'm, hGG', hG'⟩ := h.exists_measurable
  obtain ⟨H', hH'm, hHH', hH'⟩ := h'.exists_measurable
  refine (hGG'.const_smul c).trans_le (EventuallyLE.trans ?_ hHH'.symm.le)
  refine ae_le_of_ae_le_trim (ae_le_of_forall_setLIntegral_le_of_sigmaFinite
    (hG'm.const_smul c) fun s hs _ ↦ ?_)
  have hs' : s ∈ m := measurableSet_iff_mem.mp hs
  rw [setLIntegral_trim hm (hG'm.const_smul c) hs', setLIntegral_trim hm hH'm hs',
    hH'.setLIntegral_eq s hs']
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [lintegral_const_mul _ (hG'm.mono hm le_rfl), hG'.setLIntegral_eq s hs']
  exact lintegral_const_mul_le _ _

/-- Countable additivity for almost everywhere measurable functions. -/
theorem tsum {ι : Type*} [Countable ι] (hm : m ≤ m₀) {X G : ι → Ω → ℝ≥0∞}
    (h : ∀ i, IsCondLExp m P (X i) (G i)) (hX : ∀ i, AEMeasurable[m₀] (X i) P) :
    IsCondLExp m P (∑' i, X i) (∑' i, G i) where
  aestronglyMeasurable := by
    choose G' hG'm hGG' _ using fun i ↦ (h i).exists_measurable
    have hm' : Measurable[m] fun ω ↦ ∑' i, G' i ω := by
      simp_rw [ENNReal.tsum_eq_iSup_sum]
      exact .iSup fun t ↦ t.measurable_fun_sum fun i _ ↦ hG'm i
    refine aestronglyMeasurable_of_ae_eq hm' ?_
    filter_upwards [ae_all_iff.2 hGG'] with ω hω
    simp only [ENNReal.tsum_apply, hω]
  setLIntegral_eq s hs := by
    simp only [ENNReal.tsum_apply]
    rw [lintegral_tsum fun i ↦ ((h i).aemeasurable' hm).restrict,
      lintegral_tsum fun i ↦ (hX i).restrict]
    exact tsum_congr fun i ↦ (h i).setLIntegral_eq s hs

theorem finsetSum {ι : Type*} (hm : m ≤ m₀) (t : Finset ι) {X G : ι → Ω → ℝ≥0∞}
    (h : ∀ i ∈ t, IsCondLExp m P (X i) (G i)) (hX : ∀ i ∈ t, AEMeasurable[m₀] (X i) P) :
    IsCondLExp m P (∑ i ∈ t, X i) (∑ i ∈ t, G i) where
  aestronglyMeasurable := by
    classical
    choose! G' hG'm hGG' _ using fun i (hi : i ∈ t) ↦ (h i hi).exists_measurable
    refine aestronglyMeasurable_of_ae_eq (Finset.measurable_sum t fun i hi ↦ hG'm i hi) ?_
    have : ∀ᵐ ω ∂P, ∀ i ∈ t, G i ω = G' i ω := (eventually_all_finset t).2 hGG'
    filter_upwards [this] with ω hω
    simp only [Finset.sum_apply]
    exact Finset.sum_congr rfl hω
  setLIntegral_eq s hs := by
    simp only [Finset.sum_apply]
    rw [lintegral_finsetSum' t fun i hi ↦ ((h i hi).aemeasurable' hm).restrict,
      lintegral_finsetSum' t fun i hi ↦ (hX i hi).restrict]
    exact Finset.sum_congr rfl fun i hi ↦ (h i hi).setLIntegral_eq s hs

/-- A conditional expectation of a function with finite integral is almost everywhere finite. -/
theorem ae_lt_top (hm : m ≤ m₀) (h : IsCondLExp m P X G) (hX : ∫⁻ ω, X ω ∂P ≠ ∞) :
    ∀ᵐ ω ∂P, G ω < ∞ :=
  ae_lt_top' (h.aemeasurable' hm) (by rwa [h.lintegral_eq])

theorem ae_ne_top (hm : m ≤ m₀) (h : IsCondLExp m P X G) (hX : ∫⁻ ω, X ω ∂P ≠ ∞) :
    ∀ᵐ ω ∂P, G ω ≠ ∞ := by
  filter_upwards [h.ae_lt_top hm hX] with ω hω using hω.ne

end IsCondLExp

/-- An almost everywhere `m`-measurable function is a conditional expectation of itself given
`m`. -/
theorem isCondLExp_self (hX : AEStronglyMeasurable[m] X P) : IsCondLExp m P X X :=
  ⟨hX, fun _ _ ↦ rfl⟩

theorem isCondLExp_const (c : ℝ≥0∞) : IsCondLExp m P (fun _ ↦ c) fun _ ↦ c :=
  isCondLExp_self aestronglyMeasurable_const

/-- Given the trivial σ-algebra and a finite measure, the conditional expectation of a function is
the constant function equal to its mean. -/
theorem isCondLExp_bot [IsFiniteMeasure P] (X : Ω → ℝ≥0∞) :
    IsCondLExp ⊥ P X fun _ ↦ (P Set.univ)⁻¹ * ∫⁻ ω, X ω ∂P := by
  refine ⟨aestronglyMeasurable_const, fun s hs ↦ ?_⟩
  rcases SigmaAlgebra.mem_bot_iff.mp hs with rfl | rfl
  · simp
  rw [setLIntegral_univ, setLIntegral_univ, lintegral_const]
  rcases eq_zero_or_neZero P with rfl | hP
  · simp
  rw [mul_comm, ← mul_assoc, ENNReal.mul_inv_cancel (NeZero.ne _) (measure_ne_top _ _), one_mul]

/-- Given a sub-σ-algebra `m` on which `P` is σ-finite, every function has an `m`-measurable
conditional (Lebesgue) expectation: the Radon-Nikodym derivative of the restriction to `m` of
`P.withDensity X` with respect to that of `P`. -/
theorem exists_measurable_isCondLExp (hm : m ≤ m₀) [SigmaFinite (P.trim hm)] (X : Ω → ℝ≥0∞) :
    ∃ G, Measurable[m] G ∧ IsCondLExp m P X G := by
  have h := AbsolutelyContinuous.trim (withDensity_absolutelyContinuous P X) hm
  have : SFinite ((P.withDensity X).trim hm) := sFinite_of_absolutelyContinuous h
  refine ⟨((P.withDensity X).trim hm).rnDeriv (P.trim hm), measurable_rnDeriv _ _,
    (measurable_rnDeriv _ _).stronglyMeasurable.aestronglyMeasurable, fun s hs ↦ ?_⟩
  rw [← setLIntegral_trim hm (measurable_rnDeriv _ _) hs, setLIntegral_rnDeriv' h hs,
    trim_measurableSet_eq hm hs, withDensity_apply _ (hm hs)]

/-! ### The domain -/

namespace HasUniqueCondLExp

/-- A function whose lower integral over each set of a σ-finite sub-σ-algebra `m` is its upper
integral has a unique conditional (Lebesgue) expectation given `m`. -/
theorem of_sigmaFinite (hm : m ≤ m₀) [SigmaFinite (P.trim hm)]
    (hX : ∀ s ∈ m, ∫⁻ ω in s, X ω ∂P =
      ⨅ (Y : Ω → ℝ≥0∞) (_ : Measurable Y) (_ : X ≤ Y), ∫⁻ ω in s, Y ω ∂P) :
    HasUniqueCondLExp m P X where
  le_eventuallySigmaAlgebra := hm.trans _root_.le_eventuallySigmaAlgebra
  setLIntegral_eq_iInf := hX
  exists_isCondLExp := let ⟨G, _, hG⟩ := exists_measurable_isCondLExp hm X; ⟨G, hG⟩
  ae_eq_of_isCondLExp _ _ h₁ h₂ := h₁.ae_eq hm h₂

/-- An almost everywhere measurable function has a unique conditional (Lebesgue) expectation given
a sub-σ-algebra on which the measure is σ-finite. -/
theorem of_aemeasurable (hm : m ≤ m₀) [SigmaFinite (P.trim hm)] (hX : AEMeasurable[m₀] X P) :
    HasUniqueCondLExp m P X :=
  of_sigmaFinite hm fun s _ ↦ setLIntegral_eq_iInf_of_aemeasurable hX s

end HasUniqueCondLExp

/-- `has_unique_cond_lexp` proves `HasUniqueCondLExp m P X`, the domain of the conditional
(Lebesgue) expectation `P⁻[X | m]`: it tries a hypothesis, then
`HasUniqueCondLExp.of_aemeasurable`, whose sub-σ-algebra hypothesis it proves with
`sub_sigma_algebra`, whose σ-finiteness it finds by instance search and whose measurability
hypothesis it proves with `fun_prop`. Later files extend it with `macro_rules`. -/
syntax (name := hasUniqueCondLExp) "has_unique_cond_lexp" : tactic

macro_rules
  | `(tactic| has_unique_cond_lexp) => `(tactic| first
    | done
    | assumption
    | exact MeasureTheory.HasUniqueCondLExp.of_aemeasurable (by sub_sigma_algebra)
        (by first | assumption | fun_prop)
    | fail "this function needs a proof `HasUniqueCondLExp m P X` that it has a conditional \
        expectation given `m`, unique almost everywhere, for example from its measurability and \
        the σ-finiteness of `P` on `m`")

/-! ### The conditional expectation as an almost everywhere class -/

theorem exists_germ_isCondLExp (h : HasUniqueCondLExp m P X) :
    ∃ φ : (ae P).Germ ℝ≥0∞, ∃ G, IsCondLExp m P X G ∧ G ∈ φ :=
  let ⟨G, hG⟩ := h.exists_isCondLExp
  ⟨G, G, hG, Germ.coe_mem G⟩

variable (m) in
/-- The conditional (Lebesgue) expectation of `X` given the σ-algebra `m` with respect to `P`, with
notation `P⁻[X | m]`: the almost everywhere class of the conditional (Lebesgue) expectations of
`X`, as a germ along `ae P`. A function `G` represents it exactly when it is a conditional
expectation of `X` (`MeasureTheory.mem_condLExp_iff`).

It takes a proof of `HasUniqueCondLExp m P X`, its exact domain, which the tactic
`has_unique_cond_lexp` finds for an almost everywhere measurable `X` and a sub-σ-algebra on which
`P` is σ-finite. -/
noncomputable def condLExp (P : Measure[m₀] Ω) (X : Ω → ℝ≥0∞)
    (h : HasUniqueCondLExp m P X := by has_unique_cond_lexp) : (ae P).Germ ℝ≥0∞ :=
  (exists_germ_isCondLExp h).choose

@[inherit_doc MeasureTheory.condLExp]
scoped macro:max P:term noWs "⁻[" X:term " | " m:term "]" : term =>
  `(MeasureTheory.condLExp $m $P $X)

/-- Unexpander for `P⁻[X | m]` notation. -/
@[app_unexpander MeasureTheory.condLExp]
meta def condLExpUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $m $P $X $_) => `($P⁻[$X|$m])
  | _ => throw ()

/-- info: fun h ↦ P⁻[X | m] : HasUniqueCondLExp m P X → (ae P).Germ ℝ≥0∞ -/
#guard_msgs in
#check fun h : HasUniqueCondLExp m P X ↦ P⁻[X | m]

/-- Every conditional (Lebesgue) expectation of `X` represents `P⁻[X | m]`. -/
theorem IsCondLExp.mem_condLExp (h : HasUniqueCondLExp m P X) (hG : IsCondLExp m P X G) :
    G ∈ condLExp m P X h := by
  obtain ⟨G', hG', hG'_mem⟩ := (exists_germ_isCondLExp h).choose_spec
  exact Germ.mem_of_eventuallyEq hG'_mem (h.ae_eq_of_isCondLExp hG' hG)

/-- Every representative of `P⁻[X | m]` is a conditional (Lebesgue) expectation of `X`. -/
theorem isCondLExp_of_mem_condLExp (h : HasUniqueCondLExp m P X) (hG : G ∈ condLExp m P X h) :
    IsCondLExp m P X G := by
  obtain ⟨G', hG', hG'_mem⟩ := (exists_germ_isCondLExp h).choose_spec
  exact hG'.congr_right (Germ.eventuallyEq_of_mem hG'_mem hG)

/-- The representatives of `P⁻[X | m]` are the conditional (Lebesgue) expectations of `X`. -/
theorem mem_condLExp_iff (h : HasUniqueCondLExp m P X) :
    G ∈ condLExp m P X h ↔ IsCondLExp m P X G :=
  ⟨isCondLExp_of_mem_condLExp h, fun hG ↦ hG.mem_condLExp h⟩

/-- `P⁻[X | m]` is the class of any conditional (Lebesgue) expectation of `X`. -/
theorem IsCondLExp.condLExp_eq (h : HasUniqueCondLExp m P X) (hG : IsCondLExp m P X G) :
    condLExp m P X h = G :=
  Germ.eq_coe_of_mem (hG.mem_condLExp h)

/-- The conditional (Lebesgue) expectation of an almost everywhere `m`-measurable function is its
class. -/
theorem condLExp_of_aestronglyMeasurable (h : HasUniqueCondLExp m P X)
    (hX : AEStronglyMeasurable[m] X P) :
    condLExp m P X h = X :=
  (isCondLExp_self hX).condLExp_eq h

end MeasureTheory
