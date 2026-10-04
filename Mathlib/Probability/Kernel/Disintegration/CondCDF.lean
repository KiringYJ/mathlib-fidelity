/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Probability.Kernel.Disintegration.CDFToKernel

/-!
# Conditional cumulative distribution function

Let `ρ : Measure (α × ℝ)`. A *conditional cumulative distribution function* (conditional cdf) of
`ρ` is a family `F : α → StieltjesFunction ℝ` such that

* for every `a : α`, `F a` tends to `0` at `-∞` and to `1` at `+∞`;
* for every `x : ℝ`, the function `a ↦ F a x` is measurable;
* for every `x : ℝ` and every measurable set `s : Set α`,
  `∫⁻ a in s, ENNReal.ofReal (F a x) ∂ρ.fst = ρ (s ×ˢ Iic x)`.

The last identity says that `a ↦ ENNReal.ofReal (F a x)` is a density of the measure `ρ.IicSnd x`
with respect to the first marginal `ρ.fst`. It is required at every real `x`.

In general a conditional cdf is not canonical: a family that is measurable in `a`, consists of
probability cdfs, and agrees `ρ.fst`-almost everywhere with a conditional cdf is again one
(`ProbabilityTheory.IsCondCDF.congr`). The class `ProbabilityTheory.HasUniqueCondCDF ρ` says that a
conditional cdf of `ρ` exists and that any two of them agree `ρ.fst`-almost everywhere, so that a
conditional cdf is determined up to such modifications. It is the exact domain of
`ProbabilityTheory.condCDF ρ`, which chooses one conditional cdf.

Instance search derives `HasUniqueCondCDF ρ` from `SigmaFinite ρ.fst`
(`ProbabilityTheory.hasUniqueCondCDF_of_sigmaFinite_fst`), which it finds for a finite measure `ρ`;
otherwise that instance can be supplied locally. The domain includes infinite measures: the first
marginal of `volume.prod (gaussianReal 0 1)` is Lebesgue measure, which is σ-finite, and the
conditional cdf of this measure is almost everywhere the cdf of `gaussianReal 0 1`. The
σ-finiteness of `ρ` itself is not enough. Planar Lebesgue measure is σ-finite, but its first
marginal is infinity times Lebesgue measure, and every probability cdf that is positive everywhere,
taken as a constant family, is a conditional cdf of it. Two different such families do not agree
almost everywhere, so `HasUniqueCondCDF` fails for planar Lebesgue measure. Conversely, the class is
strictly larger than the measures with a σ-finite first marginal: it contains the image of counting
measure on `ℝ` under `fun a ↦ (a, 0)`, whose first marginal, counting measure, is not σ-finite.
This is why the domain is a class rather than the hypothesis `SigmaFinite ρ.fst`. See
`Counterexamples/CondCDF.lean` for both examples.

## Main definitions

* `ProbabilityTheory.IsCondCDF ρ F`: the family `F : α → StieltjesFunction ℝ` is a conditional cdf
  of `ρ : Measure (α × ℝ)`. A `StieltjesFunction ℝ` is a function `ℝ → ℝ` which is monotone and
  right-continuous.
* `ProbabilityTheory.HasUniqueCondCDF ρ`: a conditional cdf of `ρ` exists, and any two of them agree
  `ρ.fst`-almost everywhere. This is the exact domain of `condCDF`.
* `ProbabilityTheory.condCDF ρ : α → StieltjesFunction ℝ`: a conditional cdf of a measure `ρ` such
  that `HasUniqueCondCDF ρ`.

## Main statements

* `ProbabilityTheory.hasUniqueCondCDF_of_sigmaFinite_fst`: if `ρ.fst` is σ-finite, then
  `HasUniqueCondCDF ρ` holds.
* `ProbabilityTheory.isCondCDF_condCDF`: `condCDF ρ` is a conditional cdf of `ρ`.
* `ProbabilityTheory.IsCondCDF.ae_eq_condCDF`: every conditional cdf of `ρ` agrees
  `ρ.fst`-almost everywhere with `condCDF ρ`.
* `ProbabilityTheory.IsCondCDF.congr`: a measurable family of probability cdfs that agrees
  `ρ.fst`-almost everywhere with a conditional cdf is a conditional cdf.
* `ProbabilityTheory.setLIntegral_condCDF`: for all `x : ℝ` and all measurable sets `s`,
  `∫⁻ a in s, ENNReal.ofReal (condCDF ρ a x) ∂ρ.fst = ρ (s ×ˢ Iic x)`.
* `ProbabilityTheory.IsCondCDF.ofReal_ae_eq_rnDeriv`: if `ρ.fst` is σ-finite, every conditional cdf
  `F` is a version of the Radon-Nikodym derivative of `ρ.IicSnd x` with respect to `ρ.fst`:
  `ENNReal.ofReal (F a x) = (ρ.IicSnd x).rnDeriv ρ.fst a` for `ρ.fst`-almost every `a`.
* `ProbabilityTheory.IsCondCDF.integrable`, `ProbabilityTheory.IsCondCDF.setIntegral`,
  `ProbabilityTheory.IsCondCDF.integral` and `ProbabilityTheory.IsCondCDF.isCondKernelCDF`: the
  statements about Bochner integrals and kernels hold for every conditional cdf of a finite measure.
  `ProbabilityTheory.integrable_condCDF`, `ProbabilityTheory.setIntegral_condCDF`,
  `ProbabilityTheory.integral_condCDF` and `ProbabilityTheory.isCondKernelCDF_condCDF` are their
  specializations to `condCDF ρ`. They assume `IsFiniteMeasure ρ`.

## Implementation notes

`HasUniqueCondCDF ρ` is a class, so that `condCDF ρ a x` keeps its form as a function of `a` and
`x` and the evidence is found by instance search. It is a proposition, so `condCDF ρ` does not
depend on the proof of the evidence.

The existence of a conditional cdf is proved with the more general tools about kernel CDFs
developed in the file `Mathlib/Probability/Kernel/Disintegration/CDFToKernel.lean`. In that file, we
build a function `α × β → StieltjesFunction ℝ` (which is `α × β → ℝ → ℝ` with additional
properties) from a function `α × β → ℚ → ℝ`. The restriction to `ℚ` allows to prove some
properties like measurability more easily. Here we apply that construction to the case `β = Unit`
and then drop `β`. The function on `ℚ` is given by the Radon-Nikodym derivatives
`(ρ.IicSnd r).rnDeriv ρ.fst` at rational `r`, and `stieltjesOfMeasurableRat` extends it to a family
of Stieltjes functions. These tools require a finite measure. For a measure `ρ` with a σ-finite
first marginal, we choose a measurable function `w : α → ℝ≥0` that is positive and satisfies
`∫⁻ a, w a ∂ρ.fst < 1`, and we apply them to the finite measure
`ρ' := ρ.withDensity fun p ↦ w p.1`, using the Radon-Nikodym derivatives of `ρ` itself, which are
also densities of the rays of `ρ'` with respect to `ρ'.fst`. The weight `w` is then divided out of
the identity for the rays.

Uniqueness follows from `MeasureTheory.ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite` at rational
points and the right continuity of Stieltjes functions.

This construction is not canonical. Radon-Nikodym derivatives are determined only almost
everywhere, and `stieltjesOfMeasurableRat` replaces the derivatives by a default function at the
points where they do not form a Stieltjes function on `ℚ`. The declarations of the construction are
private and only serve to prove that a conditional cdf exists. The specification `IsCondCDF` and the
evidence `HasUniqueCondCDF` do not depend on these choices.

Chang and Pollard [chang_pollard1997] disintegrate a σ-finite measure with respect to a σ-finite
mixing measure (Definition 1, p. 292). For such a measure that has a disintegration, they show that
the disintegrating measures can be taken to be probability measures exactly when the image measure
is σ-finite and serves as the mixing measure (p. 292 and Theorem 2, p. 294); for the projection onto
`α`, the image measure is `ρ.fst`. This file proves that the σ-finiteness of `ρ.fst` is sufficient
for `HasUniqueCondCDF ρ`; it is not necessary.

## References

* [J. T. Chang and D. Pollard, *Conditioning as disintegration*][chang_pollard1997]
-/

@[expose] public section

open MeasureTheory Set Filter TopologicalSpace

open scoped NNReal ENNReal MeasureTheory Topology

namespace MeasureTheory.Measure

variable {α : Type*} {mα : SigmaAlgebra α} (ρ : Measure (α × ℝ))

/-- Measure on `α` such that for a measurable set `s`, `ρ.IicSnd r s = ρ (s ×ˢ Iic r)`. -/
noncomputable def IicSnd (r : ℝ) : Measure α :=
  (ρ.restrict (univ ×ˢ Iic r)).fst

theorem IicSnd_apply (r : ℝ) {s : Set α} (hs : MeasurableSet s) :
    ρ.IicSnd r s = ρ (s ×ˢ Iic r) := by
  rw [IicSnd, fst_apply hs, restrict_apply' (MeasurableSet.univ.prod measurableSet_Iic),
    univ_prod, Set.prod_eq]

theorem IicSnd_univ (r : ℝ) : ρ.IicSnd r univ = ρ (univ ×ˢ Iic r) :=
  IicSnd_apply ρ r MeasurableSet.univ

@[gcongr]
theorem IicSnd_mono {r r' : ℝ} (h_le : r ≤ r') : ρ.IicSnd r ≤ ρ.IicSnd r' := by
  unfold IicSnd; gcongr

theorem IicSnd_le_fst (r : ℝ) : ρ.IicSnd r ≤ ρ.fst :=
  fst_mono restrict_le_self

theorem IicSnd_ac_fst (r : ℝ) : ρ.IicSnd r ≪ ρ.fst :=
  Measure.absolutelyContinuous_of_le (IicSnd_le_fst ρ r)

theorem IsFiniteMeasure.IicSnd {ρ : Measure (α × ℝ)} [IsFiniteMeasure ρ] (r : ℝ) :
    IsFiniteMeasure (ρ.IicSnd r) :=
  isFiniteMeasure_of_le _ (IicSnd_le_fst ρ _)

/-- Every `ρ.IicSnd r` is σ-finite as soon as the marginal `ρ.fst` is. -/
theorem SigmaFinite.IicSnd {ρ : Measure (α × ℝ)} [SigmaFinite ρ.fst] (r : ℝ) :
    SigmaFinite (ρ.IicSnd r) :=
  sigmaFinite_of_le ρ.fst (IicSnd_le_fst ρ r)

theorem iInf_IicSnd_gt (t : ℚ) {s : Set α} (hs : MeasurableSet s) [IsFiniteMeasure ρ] :
    ⨅ r : { r' : ℚ // t < r' }, ρ.IicSnd r s = ρ.IicSnd t s := by
  simp_rw [ρ.IicSnd_apply _ hs, Measure.iInf_rat_gt_prod_Iic hs]

theorem tendsto_IicSnd_atTop {s : Set α} (hs : MeasurableSet s) :
    Tendsto (fun r : ℚ ↦ ρ.IicSnd r s) atTop (𝓝 (ρ.fst s)) := by
  simp_rw [ρ.IicSnd_apply _ hs, fst_apply hs, ← prod_univ]
  rw [← Real.iUnion_Iic_rat, prod_iUnion]
  apply tendsto_measure_iUnion_atTop
  exact monotone_const.set_prod Rat.cast_mono.Iic

theorem tendsto_IicSnd_atBot [IsFiniteMeasure ρ] {s : Set α} (hs : MeasurableSet s) :
    Tendsto (fun r : ℚ ↦ ρ.IicSnd r s) atBot (𝓝 0) := by
  simp_rw [ρ.IicSnd_apply _ hs]
  have h_empty : ρ (s ×ˢ ∅) = 0 := by simp only [prod_empty, measure_empty]
  rw [← h_empty, ← Real.iInter_Iic_rat, prod_iInter]
  suffices h_neg :
      Tendsto (fun r : ℚ ↦ ρ (s ×ˢ Iic ↑(-r))) atTop (𝓝 (ρ (⋂ r : ℚ, s ×ˢ Iic ↑(-r)))) by
    have h_inter_eq : ⋂ r : ℚ, s ×ˢ Iic ↑(-r) = ⋂ r : ℚ, s ×ˢ Iic (r : ℝ) := by
      ext1 x
      push _ ∈ _
      refine ⟨fun h i ↦ ⟨(h i).1, ?_⟩, fun h i ↦ ⟨(h i).1, ?_⟩⟩ <;> have h' := h (-i)
      · rw [neg_neg] at h'; exact h'.2
      · exact h'.2
    rw [h_inter_eq] at h_neg
    exact tendsto_comp_neg_atTop_iff.mp h_neg
  refine tendsto_measure_iInter_atTop (fun q ↦ (hs.prod measurableSet_Iic).nullMeasurableSet)
    ?_ ⟨0, measure_ne_top ρ _⟩
  refine fun q r hqr ↦ Set.prod_mono subset_rfl fun x hx ↦ ?_
  simp only [Rat.cast_neg, mem_Iic] at hx ⊢
  refine hx.trans (neg_le_neg ?_)
  exact mod_cast hqr

end MeasureTheory.Measure

open MeasureTheory

namespace ProbabilityTheory

variable {α : Type*} {mα : SigmaAlgebra α}

/-! ### The specification of a conditional cdf -/

/-- A family `F : α → StieltjesFunction ℝ` is a conditional cumulative distribution function
(conditional cdf) of `ρ : Measure (α × ℝ)` if every `F a` tends to `0` at `-∞` and to `1` at `+∞`,
if `a ↦ F a x` is measurable for every `x : ℝ`, and if for every `x : ℝ` and every measurable set
`s`, `∫⁻ a in s, ENNReal.ofReal (F a x) ∂ρ.fst = ρ (s ×ˢ Iic x)`.

A conditional cdf can be modified on a `ρ.fst`-null set of `a`, provided the result stays
measurable in `a` and consists of probability cdfs (`ProbabilityTheory.IsCondCDF.congr`), so in
general it is not canonical. See `ProbabilityTheory.HasUniqueCondCDF` for the measures whose
conditional cdf is unique almost everywhere. -/
structure IsCondCDF (ρ : Measure (α × ℝ)) (F : α → StieltjesFunction ℝ) : Prop where
  measurable (x : ℝ) : Measurable fun a ↦ F a x
  tendsto_atBot_zero (a : α) : Tendsto (F a) atBot (𝓝 0)
  tendsto_atTop_one (a : α) : Tendsto (F a) atTop (𝓝 1)
  setLIntegral (x : ℝ) {s : Set α} (hs : MeasurableSet s) :
    ∫⁻ a in s, ENNReal.ofReal (F a x) ∂ρ.fst = ρ (s ×ˢ Iic x)

namespace IsCondCDF

variable {ρ : Measure (α × ℝ)} {F : α → StieltjesFunction ℝ}

/-- A conditional cdf is non-negative. -/
lemma nonneg (hF : IsCondCDF ρ F) (a : α) (x : ℝ) : 0 ≤ F a x :=
  Monotone.le_of_tendsto (F a).mono (hF.tendsto_atBot_zero a) x

/-- A conditional cdf is bounded by 1. -/
lemma le_one (hF : IsCondCDF ρ F) (a : α) (x : ℝ) : F a x ≤ 1 :=
  Monotone.ge_of_tendsto (F a).mono (hF.tendsto_atTop_one a) x

/-- A conditional cdf is a density of `ρ.IicSnd x` with respect to the first marginal of `ρ`. -/
lemma withDensity_eq (hF : IsCondCDF ρ F) (x : ℝ) :
    ρ.fst.withDensity (fun a ↦ ENNReal.ofReal (F a x)) = ρ.IicSnd x := by
  ext s hs
  rw [withDensity_apply _ hs, hF.setLIntegral x hs, Measure.IicSnd_apply ρ x hs]

/-- The identity `∫⁻ a, ENNReal.ofReal (F a x) ∂ρ.fst = ρ (univ ×ˢ Iic x)` for a conditional cdf
`F`, which is the case `s = univ` of the identity for the rays. -/
lemma lintegral (hF : IsCondCDF ρ F) (x : ℝ) :
    ∫⁻ a, ENNReal.ofReal (F a x) ∂ρ.fst = ρ (univ ×ˢ Iic x) := by
  rw [← setLIntegral_univ, hF.setLIntegral x MeasurableSet.univ]

/-- A conditional cdf can be modified on a `ρ.fst`-null set of `a`: a family `G` that is
measurable in `a`, tends to `0` at `-∞` and to `1` at `+∞` for every `a`, and agrees
`ρ.fst`-almost everywhere with a conditional cdf `F` of `ρ` is again a conditional cdf of `ρ`. -/
lemma congr {G : α → StieltjesFunction ℝ} (hF : IsCondCDF ρ F)
    (hG : ∀ x, Measurable fun a ↦ G a x) (hG_atBot : ∀ a, Tendsto (G a) atBot (𝓝 0))
    (hG_atTop : ∀ a, Tendsto (G a) atTop (𝓝 1)) (h : ∀ᵐ a ∂ρ.fst, F a = G a) :
    IsCondCDF ρ G where
  measurable := hG
  tendsto_atBot_zero := hG_atBot
  tendsto_atTop_one := hG_atTop
  setLIntegral x s hs := by
    rw [← hF.setLIntegral x hs]
    refine lintegral_congr_ae (ae_restrict_of_ae ?_)
    filter_upwards [h] with a ha
    rw [ha]

/-- A conditional cdf of a finite measure is integrable at each `x : ℝ`. -/
lemma integrable [IsFiniteMeasure ρ] (hF : IsCondCDF ρ F) (x : ℝ) :
    Integrable (fun a ↦ F a x) ρ.fst :=
  Integrable.of_bound (hF.measurable x).aestronglyMeasurable 1
    (ae_of_all _ fun a ↦ by
      rw [Real.norm_of_nonneg (hF.nonneg a x)]
      exact hF.le_one a x)

/-- The real-valued version of `IsCondCDF.setLIntegral`, for a finite measure. -/
lemma setIntegral [IsFiniteMeasure ρ] (hF : IsCondCDF ρ F) (x : ℝ) {s : Set α}
    (hs : MeasurableSet s) : ∫ a in s, F a x ∂ρ.fst = ρ.real (s ×ˢ Iic x) := by
  rw [← ENNReal.ofReal_eq_ofReal_iff (setIntegral_nonneg hs fun a _ ↦ hF.nonneg a x)
    measureReal_nonneg, ofReal_integral_eq_lintegral_ofReal (hF.integrable x).restrict
    (ae_of_all _ fun a ↦ hF.nonneg a x), hF.setLIntegral x hs, ofReal_measureReal]

/-- The real-valued version of `IsCondCDF.lintegral`, for a finite measure. -/
lemma integral [IsFiniteMeasure ρ] (hF : IsCondCDF ρ F) (x : ℝ) :
    ∫ a, F a x ∂ρ.fst = ρ.real (univ ×ˢ Iic x) := by
  rw [← setIntegral_univ, hF.setIntegral x MeasurableSet.univ]

/-- A conditional cdf of a finite measure `ρ` is a conditional kernel CDF of the constant kernel
with value `ρ` with respect to the constant kernel with value `ρ.fst`. -/
lemma isCondKernelCDF [IsFiniteMeasure ρ] (hF : IsCondCDF ρ F) :
    IsCondKernelCDF (fun p : Unit × α ↦ F p.2) (Kernel.const Unit ρ) (Kernel.const Unit ρ.fst) where
  measurable x := (hF.measurable x).comp measurable_snd
  integrable _ x := hF.integrable x
  tendsto_atTop_one p := hF.tendsto_atTop_one p.2
  tendsto_atBot_zero p := hF.tendsto_atBot_zero p.2
  setIntegral _ _ hs x := hF.setIntegral x hs

/-- If `ρ.fst` is σ-finite, a conditional cdf is a version of the Radon-Nikodym derivative of
`ρ.IicSnd x` with respect to `ρ.fst`, at every real `x`. -/
lemma ofReal_ae_eq_rnDeriv [SigmaFinite ρ.fst] (hF : IsCondCDF ρ F) (x : ℝ) :
    (fun a ↦ ENNReal.ofReal (F a x)) =ᵐ[ρ.fst] (ρ.IicSnd x).rnDeriv ρ.fst := by
  rw [← hF.withDensity_eq x]
  exact (Measure.rnDeriv_withDensity ρ.fst (hF.measurable x).ennreal_ofReal).symm

end IsCondCDF

/-- A measure `ρ` on `α × ℝ` has a conditional cdf that is unique almost everywhere: a conditional
cdf of `ρ` exists, and any two conditional cdfs of `ρ` agree `ρ.fst`-almost everywhere.

This is the exact domain of `ProbabilityTheory.condCDF`. Instance search derives it from
`SigmaFinite ρ.fst` (`ProbabilityTheory.hasUniqueCondCDF_of_sigmaFinite_fst`), which it finds for a
finite measure `ρ`; otherwise that instance can be supplied locally. The σ-finiteness of `ρ` itself
is not enough, and the σ-finiteness of `ρ.fst` is not necessary: see
`Counterexamples/CondCDF.lean`. -/
class HasUniqueCondCDF (ρ : Measure (α × ℝ)) : Prop where
  /-- A conditional cdf of `ρ` exists. -/
  exists_isCondCDF : ∃ F : α → StieltjesFunction ℝ, IsCondCDF ρ F
  /-- Two conditional cdfs of `ρ` agree `ρ.fst`-almost everywhere. -/
  ae_eq_of_isCondCDF ⦃F G : α → StieltjesFunction ℝ⦄ :
    IsCondCDF ρ F → IsCondCDF ρ G → ∀ᵐ a ∂ρ.fst, F a = G a

/-! ### Existence and uniqueness for a σ-finite marginal -/

section Construction

attribute [local instance] MeasureTheory.Measure.IsFiniteMeasure.IicSnd
  MeasureTheory.Measure.SigmaFinite.IicSnd

/-- The Radon-Nikodym derivative of `ρ.IicSnd r` with respect to `ρ.fst`. When `ρ.fst` is σ-finite,
it is a density of `ρ.IicSnd r`, so its real part is a version of the conditional cdf at the
rational `r`. It is determined only `ρ.fst`-almost everywhere, and `rnDeriv` takes a fallback value
without a Lebesgue decomposition. Without σ-finiteness it has no such meaning: for planar Lebesgue
measure, `ρ.IicSnd r = ρ.fst` for every `r`, so it does not depend on `r`. This declaration is
private: it is used only to construct a conditional cdf. -/
private noncomputable def preCDF (ρ : Measure (α × ℝ)) (r : ℚ) : α → ℝ≥0∞ :=
  Measure.rnDeriv (ρ.IicSnd r) ρ.fst

private lemma measurable_preCDF {ρ : Measure (α × ℝ)} {r : ℚ} : Measurable (preCDF ρ r) :=
  Measure.measurable_rnDeriv _ _

private lemma measurable_preCDF' {ρ : Measure (α × ℝ)} :
    Measurable fun a r ↦ (preCDF ρ r a).toReal := by
  rw [measurable_pi_iff]
  exact fun _ ↦ measurable_preCDF.ennreal_toReal

private lemma withDensity_preCDF (ρ : Measure (α × ℝ)) (r : ℚ) [SigmaFinite ρ.fst] :
    ρ.fst.withDensity (preCDF ρ r) = ρ.IicSnd r :=
  Measure.absolutelyContinuous_iff_withDensity_rnDeriv_eq.mp (Measure.IicSnd_ac_fst ρ r)

private lemma setLIntegral_preCDF_fst (ρ : Measure (α × ℝ)) (r : ℚ) {s : Set α}
    (hs : MeasurableSet s) [SigmaFinite ρ.fst] :
    ∫⁻ x in s, preCDF ρ r x ∂ρ.fst = ρ.IicSnd r s := by
  rw [← withDensity_apply _ hs, withDensity_preCDF ρ r]

private lemma monotone_preCDF (ρ : Measure (α × ℝ)) [SigmaFinite ρ.fst] :
    ∀ᵐ a ∂ρ.fst, Monotone fun r ↦ preCDF ρ r a := by
  simp_rw [Monotone, ae_all_iff]
  refine fun r r' hrr' ↦ ae_le_of_forall_setLIntegral_le_of_sigmaFinite measurable_preCDF
    fun s hs _ ↦ ?_
  rw [setLIntegral_preCDF_fst ρ r hs, setLIntegral_preCDF_fst ρ r' hs]
  exact Measure.IicSnd_mono ρ (mod_cast hrr') s

private lemma preCDF_le_one (ρ : Measure (α × ℝ)) [SigmaFinite ρ.fst] :
    ∀ᵐ a ∂ρ.fst, ∀ r, preCDF ρ r a ≤ 1 := by
  rw [ae_all_iff]
  refine fun r ↦ ae_le_of_forall_setLIntegral_le_of_sigmaFinite measurable_preCDF fun s hs _ ↦ ?_
  rw [setLIntegral_preCDF_fst ρ r hs]
  simp only [lintegral_one, Measure.restrict_apply, MeasurableSet.univ, univ_inter]
  exact Measure.IicSnd_le_fst ρ r s

/-- The family of Stieltjes functions built from the Radon-Nikodym derivatives `preCDF`. It is a
conditional cdf whenever `ρ.fst` is σ-finite. -/
private noncomputable def condCDFAux (ρ : Measure (α × ℝ)) : α → StieltjesFunction ℝ :=
  stieltjesOfMeasurableRat (fun a r ↦ (preCDF ρ r a).toReal) measurable_preCDF'

/-! #### Reweighting by a function of the first coordinate

A conditional cdf of `ρ` is built from the finite case by reweighting `ρ` with a positive function
of the first coordinate that is integrable for `ρ.fst`. -/

section Reweight

variable {ρ : Measure (α × ℝ)} {w : α → ℝ≥0∞}

private lemma fst_withDensity_fst (hw : Measurable w) :
    (ρ.withDensity fun p ↦ w p.1).fst = ρ.fst.withDensity w := by
  ext s hs
  rw [Measure.fst_apply hs, withDensity_apply _ (measurable_fst hs), withDensity_apply _ hs,
    Measure.fst, setLIntegral_map hs hw measurable_fst]

private lemma IicSnd_withDensity_fst (hw : Measurable w) (x : ℝ) :
    (ρ.withDensity fun p ↦ w p.1).IicSnd x = (ρ.IicSnd x).withDensity w := by
  rw [Measure.IicSnd, Measure.IicSnd,
    restrict_withDensity (MeasurableSet.univ.prod measurableSet_Iic), fst_withDensity_fst hw]

/-- A positive finite weight can be divided out of an identity between weighted measures. -/
private lemma eq_of_withDensity_weight {μ ν : Measure α} {g : α → ℝ≥0∞} (hw : Measurable w)
    (hg : Measurable g) (hw₀ : ∀ a, w a ≠ 0) (hw_top : ∀ a, w a ≠ ∞)
    (h : (μ.withDensity w).withDensity g = ν.withDensity w) : μ.withDensity g = ν := by
  have h_inv : (ν.withDensity w).withDensity (fun a ↦ (w a)⁻¹) = ν :=
    withDensity_inv_same hw (ae_of_all _ hw₀) (ae_of_all _ hw_top)
  rw [← h_inv, ← h, ← withDensity_mul _ hw hg, ← withDensity_mul _ (hw.mul hg) hw.fun_inv]
  congr 1
  ext a
  simp only [Pi.mul_apply]
  rw [mul_comm (w a) (g a), mul_assoc, ENNReal.mul_inv_cancel (hw₀ a) (hw_top a), mul_one]

/-- The family `condCDFAux ρ` is a conditional cdf of `ρ`, if `ρ.fst` is σ-finite and `w` is a
positive finite measurable function that is `ρ.fst`-integrable. The proof applies the construction
for finite measures to the finite measure `ρ.withDensity fun p ↦ w p.1`. -/
private lemma isCondCDF_condCDFAux_of_weight [SigmaFinite ρ.fst] (hw : Measurable w)
    (hw₀ : ∀ a, w a ≠ 0) (hw_top : ∀ a, w a ≠ ∞) (hw_int : ∫⁻ a, w a ∂ρ.fst ≠ ∞) :
    IsCondCDF ρ (condCDFAux ρ) := by
  set ρ' : Measure (α × ℝ) := ρ.withDensity fun p ↦ w p.1
  have h_fst : ρ'.fst = ρ.fst.withDensity w := fst_withDensity_fst hw
  have h_Iic (x : ℝ) : ρ'.IicSnd x = (ρ.IicSnd x).withDensity w := IicSnd_withDensity_fst hw x
  have h_ac : ρ'.fst ≪ ρ.fst := h_fst ▸ withDensity_absolutelyContinuous _ _
  have : IsFiniteMeasure ρ' := by
    refine ⟨?_⟩
    rw [← Measure.fst_univ, h_fst, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact hw_int.lt_top
  -- `preCDF ρ q` is also a density of `ρ'.IicSnd q` with respect to `ρ'.fst`.
  have h_pre (q : ℚ) : ρ'.fst.withDensity (preCDF ρ q) = ρ'.IicSnd q := by
    rw [h_fst, h_Iic, ← withDensity_mul _ hw measurable_preCDF, mul_comm,
      withDensity_mul _ measurable_preCDF hw, withDensity_preCDF]
  have h_setLIntegral (q : ℚ) {s : Set α} (hs : MeasurableSet s) :
      ∫⁻ c in s, preCDF ρ q c ∂ρ'.fst = ρ'.IicSnd q s := by
    rw [← withDensity_apply _ hs, h_pre]
  have h_setIntegral (q : ℚ) {s : Set α} (hs : MeasurableSet s) :
      ∫ c in s, (preCDF ρ q c).toReal ∂ρ'.fst = (ρ'.IicSnd q).real s := by
    rw [integral_toReal measurable_preCDF.aemeasurable, h_setLIntegral q hs, measureReal_def]
    exact ae_lt_top measurable_preCDF (by rw [h_setLIntegral q hs]; exact measure_ne_top _ _)
  have h_integral (q : ℚ) : ∫ c, (preCDF ρ q c).toReal ∂ρ'.fst = (ρ'.IicSnd q).real univ := by
    rw [← setIntegral_univ, h_setIntegral q MeasurableSet.univ]
  have h_aux : IsRatCondKernelCDFAux (fun (p : Unit × α) r ↦ (preCDF ρ r p.2).toReal)
      (Kernel.const Unit ρ') (Kernel.const Unit ρ'.fst) :=
    { measurable := measurable_preCDF'.comp measurable_snd
      mono' := fun _ _ _ hqr ↦ by
        simp only [Kernel.const_apply]
        filter_upwards [h_ac.ae_le (monotone_preCDF ρ), h_ac.ae_le (preCDF_le_one ρ)]
          with c h₁ h₂
        exact ENNReal.toReal_mono ((h₂ _).trans_lt ENNReal.one_lt_top).ne (h₁ hqr)
      nonneg' := fun _ q ↦ by simp
      le_one' := fun _ q ↦ by
        simp only [Kernel.const_apply]
        filter_upwards [h_ac.ae_le (preCDF_le_one ρ)] with c hc
        refine ENNReal.toReal_le_of_le_ofReal zero_le_one ?_
        simp [hc q]
      tendsto_integral_of_antitone := fun _ seq _ hseq ↦ by
        simp_rw [Kernel.const_apply, h_integral]
        have h := ρ'.tendsto_IicSnd_atBot MeasurableSet.univ
        rw [← ENNReal.toReal_zero]
        have h0 : Tendsto ENNReal.toReal (𝓝 0) (𝓝 0) :=
          ENNReal.continuousAt_toReal ENNReal.zero_ne_top
        exact h0.comp (h.comp hseq)
      tendsto_integral_of_monotone := fun _ seq _ hseq ↦ by
        simp_rw [Kernel.const_apply, h_integral]
        have h := ρ'.tendsto_IicSnd_atTop MeasurableSet.univ
        have h0 : Tendsto ENNReal.toReal (𝓝 (ρ'.fst univ)) (𝓝 (ρ'.fst.real univ)) :=
          ENNReal.continuousAt_toReal (measure_ne_top _ _)
        exact h0.comp (h.comp hseq)
      integrable := fun _ q ↦ by
        simp only [Kernel.const_apply]
        refine integrable_toReal_of_lintegral_ne_top measurable_preCDF.aemeasurable ?_
        rw [← setLIntegral_univ, h_setLIntegral q MeasurableSet.univ]
        exact measure_ne_top _ _
      setIntegral := fun _ s hs q ↦ by
        simp only [Kernel.const_apply]
        rw [h_setIntegral q hs, measureReal_def, measureReal_def, Measure.IicSnd_apply _ _ hs] }
  have h_rat := h_aux.isRatCondKernelCDF
  have h_cdf := isCondKernelCDF_stieltjesOfMeasurableRat h_rat
  -- `condCDFAux ρ a` is the Stieltjes function of the kernel construction at `((), a)`.
  have h_eq (a : α) : condCDFAux ρ a = stieltjesOfMeasurableRat
      (fun (p : Unit × α) r ↦ (preCDF ρ r p.2).toReal) h_rat.measurable ((), a) :=
    (stieltjesOfMeasurableRat_unit_prod measurable_preCDF' a).symm
  have h_density (x : ℝ) :
      ρ'.fst.withDensity (fun a ↦ ENNReal.ofReal (condCDFAux ρ a x)) = ρ'.IicSnd x := by
    ext t ht
    rw [withDensity_apply _ ht, Measure.IicSnd_apply _ _ ht]
    simpa only [Kernel.const_apply, ← h_eq] using h_cdf.setLIntegral () ht x
  refine ⟨measurable_stieltjesOfMeasurableRat measurable_preCDF',
    tendsto_stieltjesOfMeasurableRat_atBot measurable_preCDF',
    tendsto_stieltjesOfMeasurableRat_atTop measurable_preCDF', fun x s hs ↦ ?_⟩
  -- Divide the weight out of the identity for `ρ'`.
  have h_density' : ρ.fst.withDensity (fun a ↦ ENNReal.ofReal (condCDFAux ρ a x)) = ρ.IicSnd x := by
    refine eq_of_withDensity_weight hw ?_ hw₀ hw_top ?_
    · exact (measurable_stieltjesOfMeasurableRat measurable_preCDF' x).ennreal_ofReal
    · rw [← h_fst, ← h_Iic]
      exact h_density x
  rw [← withDensity_apply _ hs, h_density', Measure.IicSnd_apply _ _ hs]

end Reweight

/-- The family `condCDFAux ρ` is a conditional cdf of `ρ` whenever `ρ.fst` is σ-finite. -/
private lemma isCondCDF_condCDFAux (ρ : Measure (α × ℝ)) [SigmaFinite ρ.fst] :
    IsCondCDF ρ (condCDFAux ρ) := by
  obtain ⟨w, hw_pos, hw_meas, hw_lt⟩ := exists_pos_lintegral_lt_of_sigmaFinite ρ.fst one_ne_zero
  exact isCondCDF_condCDFAux_of_weight (w := fun a ↦ (w a : ℝ≥0∞)) hw_meas.coe_nnreal_ennreal
    (fun a ↦ ENNReal.coe_ne_zero.2 (hw_pos a).ne') (fun _ ↦ ENNReal.coe_ne_top)
    (hw_lt.trans ENNReal.one_lt_top).ne

/-- Two conditional cdfs of a measure with σ-finite first marginal agree almost everywhere. -/
private lemma ae_eq_of_isCondCDF_of_sigmaFinite (ρ : Measure (α × ℝ)) [SigmaFinite ρ.fst]
    {F G : α → StieltjesFunction ℝ} (hF : IsCondCDF ρ F) (hG : IsCondCDF ρ G) :
    ∀ᵐ a ∂ρ.fst, F a = G a := by
  have h_rat (q : ℚ) : ∀ᵐ a ∂ρ.fst, F a q = G a q := by
    have h := ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite (μ := ρ.fst)
      (hF.measurable q).ennreal_ofReal (hG.measurable q).ennreal_ofReal
      fun s hs _ ↦ by rw [hF.setLIntegral q hs, hG.setLIntegral q hs]
    filter_upwards [h] with a ha
    exact (ENNReal.ofReal_eq_ofReal_iff (hF.nonneg a q) (hG.nonneg a q)).1 ha
  filter_upwards [ae_all_iff.2 h_rat] with a ha
  ext x
  rw [← StieltjesFunction.iInf_rat_gt_eq (F a) x, ← StieltjesFunction.iInf_rat_gt_eq (G a) x]
  exact iInf_congr fun r ↦ ha r

/-- If the first marginal `ρ.fst` is σ-finite, a conditional cdf of `ρ` exists and is unique
`ρ.fst`-almost everywhere. The measure `ρ` itself can be infinite. -/
-- see Note [lower instance priority]
instance (priority := 100) hasUniqueCondCDF_of_sigmaFinite_fst (ρ : Measure (α × ℝ))
    [SigmaFinite ρ.fst] : HasUniqueCondCDF ρ where
  exists_isCondCDF := ⟨condCDFAux ρ, isCondCDF_condCDFAux ρ⟩
  ae_eq_of_isCondCDF := fun _ _ hF hG ↦ ae_eq_of_isCondCDF_of_sigmaFinite ρ hF hG

end Construction

/-! ### Conditional cdf -/

/-- A conditional cdf of the measure `ρ : Measure (α × ℝ)`, as a family of Stieltjes functions
`a ↦ condCDF ρ a`, for a measure `ρ` such that `HasUniqueCondCDF ρ`.

It is a conditional cdf in the sense of `IsCondCDF` (`ProbabilityTheory.isCondCDF_condCDF`) and
every conditional cdf of `ρ` agrees with it `ρ.fst`-almost everywhere
(`ProbabilityTheory.IsCondCDF.ae_eq_condCDF`). Only this almost-everywhere class is determined by
`ρ`: a measurable modification of `condCDF ρ` on a `ρ.fst`-null set that still consists of
probability cdfs is another conditional cdf, so the values of `condCDF ρ` on a `ρ.fst`-null set
are a choice. -/
noncomputable def condCDF (ρ : Measure (α × ℝ)) [h : HasUniqueCondCDF ρ] :
    α → StieltjesFunction ℝ :=
  h.exists_isCondCDF.choose

/-- `condCDF ρ` is a conditional cdf of `ρ`. -/
lemma isCondCDF_condCDF (ρ : Measure (α × ℝ)) [h : HasUniqueCondCDF ρ] :
    IsCondCDF ρ (condCDF ρ) :=
  h.exists_isCondCDF.choose_spec

/-- Every conditional cdf of `ρ` agrees `ρ.fst`-almost everywhere with `condCDF ρ`. -/
lemma IsCondCDF.ae_eq_condCDF {ρ : Measure (α × ℝ)} [HasUniqueCondCDF ρ]
    {F : α → StieltjesFunction ℝ} (hF : IsCondCDF ρ F) :
    ∀ᵐ a ∂ρ.fst, F a = condCDF ρ a :=
  HasUniqueCondCDF.ae_eq_of_isCondCDF hF (isCondCDF_condCDF ρ)

/-- The conditional cdf is non-negative for all `a : α`. -/
theorem condCDF_nonneg (ρ : Measure (α × ℝ)) [HasUniqueCondCDF ρ] (a : α) (r : ℝ) :
    0 ≤ condCDF ρ a r :=
  (isCondCDF_condCDF ρ).nonneg a r

/-- The conditional cdf is lower or equal to 1 for all `a : α`. -/
theorem condCDF_le_one (ρ : Measure (α × ℝ)) [HasUniqueCondCDF ρ] (a : α) (x : ℝ) :
    condCDF ρ a x ≤ 1 :=
  (isCondCDF_condCDF ρ).le_one a x

/-- The conditional cdf tends to 0 at -∞ for all `a : α`. -/
theorem tendsto_condCDF_atBot (ρ : Measure (α × ℝ)) [HasUniqueCondCDF ρ] (a : α) :
    Tendsto (condCDF ρ a) atBot (𝓝 0) :=
  (isCondCDF_condCDF ρ).tendsto_atBot_zero a

/-- The conditional cdf tends to 1 at +∞ for all `a : α`. -/
theorem tendsto_condCDF_atTop (ρ : Measure (α × ℝ)) [HasUniqueCondCDF ρ] (a : α) :
    Tendsto (condCDF ρ a) atTop (𝓝 1) :=
  (isCondCDF_condCDF ρ).tendsto_atTop_one a

/-- The conditional cdf is a measurable function of `a : α` for all `x : ℝ`. -/
theorem measurable_condCDF (ρ : Measure (α × ℝ)) [HasUniqueCondCDF ρ] (x : ℝ) :
    Measurable fun a ↦ condCDF ρ a x :=
  (isCondCDF_condCDF ρ).measurable x

/-- The conditional cdf is a strongly measurable function of `a : α` for all `x : ℝ`. -/
theorem stronglyMeasurable_condCDF (ρ : Measure (α × ℝ)) [HasUniqueCondCDF ρ] (x : ℝ) :
    StronglyMeasurable fun a ↦ condCDF ρ a x :=
  (measurable_condCDF ρ x).stronglyMeasurable

/-- The identity `∫⁻ a in s, ENNReal.ofReal (condCDF ρ a x) ∂ρ.fst = ρ (s ×ˢ Iic x)` for a
measurable set `s`, which holds at every real `x`. -/
theorem setLIntegral_condCDF (ρ : Measure (α × ℝ)) [HasUniqueCondCDF ρ] (x : ℝ) {s : Set α}
    (hs : MeasurableSet s) :
    ∫⁻ a in s, ENNReal.ofReal (condCDF ρ a x) ∂ρ.fst = ρ (s ×ˢ Iic x) :=
  (isCondCDF_condCDF ρ).setLIntegral x hs

/-- The identity of `setLIntegral_condCDF` for the whole space. -/
theorem lintegral_condCDF (ρ : Measure (α × ℝ)) [HasUniqueCondCDF ρ] (x : ℝ) :
    ∫⁻ a, ENNReal.ofReal (condCDF ρ a x) ∂ρ.fst = ρ (univ ×ˢ Iic x) :=
  (isCondCDF_condCDF ρ).lintegral x

/-- For a finite measure, the conditional cdf is integrable at each `x : ℝ`. -/
theorem integrable_condCDF (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] (x : ℝ) :
    Integrable (fun a ↦ condCDF ρ a x) ρ.fst :=
  (isCondCDF_condCDF ρ).integrable x

/-- The real-valued version of `setLIntegral_condCDF`, for a finite measure. -/
theorem setIntegral_condCDF (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] (x : ℝ) {s : Set α}
    (hs : MeasurableSet s) : ∫ a in s, condCDF ρ a x ∂ρ.fst = ρ.real (s ×ˢ Iic x) :=
  (isCondCDF_condCDF ρ).setIntegral x hs

/-- The real-valued version of `lintegral_condCDF`, for a finite measure. -/
theorem integral_condCDF (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] (x : ℝ) :
    ∫ a, condCDF ρ a x ∂ρ.fst = ρ.real (univ ×ˢ Iic x) :=
  (isCondCDF_condCDF ρ).integral x

/-- For a finite measure `ρ`, `condCDF ρ` is a conditional kernel CDF of the constant kernel with
value `ρ` with respect to the constant kernel with value `ρ.fst`. -/
lemma isCondKernelCDF_condCDF (ρ : Measure (α × ℝ)) [IsFiniteMeasure ρ] :
    IsCondKernelCDF (fun p : Unit × α ↦ condCDF ρ p.2) (Kernel.const Unit ρ)
      (Kernel.const Unit ρ.fst) :=
  (isCondCDF_condCDF ρ).isCondKernelCDF

section Measure

/-- The measure associated to the conditional cdf gives the mass `condCDF ρ a x` to `Iic x`. -/
theorem measure_condCDF_Iic (ρ : Measure (α × ℝ)) [HasUniqueCondCDF ρ] (a : α) (x : ℝ) :
    (condCDF ρ a).measure (Iic x) = ENNReal.ofReal (condCDF ρ a x) := by
  rw [← sub_zero (condCDF ρ a x)]
  exact (condCDF ρ a).measure_Iic (tendsto_condCDF_atBot ρ a) _

/-- The measure associated to the conditional cdf is a probability measure. -/
theorem measure_condCDF_univ (ρ : Measure (α × ℝ)) [HasUniqueCondCDF ρ] (a : α) :
    (condCDF ρ a).measure univ = 1 := by
  rw [← ENNReal.ofReal_one, ← sub_zero (1 : ℝ)]
  exact StieltjesFunction.measure_univ _ (tendsto_condCDF_atBot ρ a) (tendsto_condCDF_atTop ρ a)

instance instIsProbabilityMeasureCondCDF (ρ : Measure (α × ℝ)) [HasUniqueCondCDF ρ] (a : α) :
    IsProbabilityMeasure (condCDF ρ a).measure :=
  ⟨measure_condCDF_univ ρ a⟩

/-- The function `a ↦ (condCDF ρ a).measure` is measurable. -/
theorem measurable_measure_condCDF (ρ : Measure (α × ℝ)) [HasUniqueCondCDF ρ] :
    Measurable fun a => (condCDF ρ a).measure :=
  .measure_of_isPiSystem_of_isProbabilityMeasure (borel_eq_generateFrom_Iic ℝ) isPiSystem_Iic <| by
    simp_rw [forall_mem_range, measure_condCDF_Iic]
    exact fun u ↦ (measurable_condCDF ρ u).ennreal_ofReal

end Measure

end ProbabilityTheory
