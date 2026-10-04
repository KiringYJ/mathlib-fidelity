/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module

public import Mathlib.Analysis.Real.Cardinality
public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Probability.CDF
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Kernel.Disintegration.CondCDF

/-!
# σ-finiteness and conditional cdfs that are unique almost everywhere

A conditional cumulative distribution function of a measure `ρ` on `ℝ × ℝ` is a measurable family
of probability distribution functions `F a` such that, for every real `x` and measurable set `s`,
`∫⁻ a in s, ENNReal.ofReal (F a x) ∂ρ.fst = ρ (s ×ˢ Iic x)` (`ProbabilityTheory.IsCondCDF`).
The class `ProbabilityTheory.HasUniqueCondCDF ρ` says that one exists and that any two agree
`ρ.fst`-almost everywhere. It holds if the first marginal `ρ.fst` is σ-finite
(`ProbabilityTheory.hasUniqueCondCDF_of_sigmaFinite_fst`). We show that the σ-finiteness of `ρ`
itself is not sufficient, and that the σ-finiteness of `ρ.fst` is not necessary.

## Planar Lebesgue measure: σ-finiteness of `ρ` is not sufficient

Planar Lebesgue measure `volume` on `ℝ × ℝ` is σ-finite. Its first marginal is infinity times
Lebesgue measure on `ℝ`, which gives infinite mass to every set that is not null, so it is not
σ-finite (`Counterexample.CondCDF.not_sigmaFinite_fst_volume`).

Let `γ` be a probability measure on `ℝ` whose cdf is positive everywhere, that is, every ray `Iic x`
has positive `γ`-measure. A Gaussian distribution with positive variance is an example, because
`volume ≪ γ` and every ray has infinite Lebesgue measure. For the constant family `fun _ ↦ cdf γ`,
both sides of the identity for the rays are `volume s * ∞`, so that this family is a conditional
cdf of `volume` (`Counterexample.CondCDF.isCondCDF_volume`). Two Gaussian distributions with
different means have different cdfs, so the corresponding constant families are two conditional
cdfs of `volume` that differ at every point. Two families that agree almost everywhere with respect
to the nonzero measure `volume.fst` agree at some point. Consequently,
`ProbabilityTheory.HasUniqueCondCDF volume` fails
(`Counterexample.CondCDF.not_hasUniqueCondCDF_volume`), and `ProbabilityTheory.condCDF volume` is
not defined. Moreover, every `volume.IicSnd r` equals `volume.fst`
(`Counterexample.CondCDF.IicSnd_volume`), so the Radon-Nikodym derivatives of the rays with respect
to `volume.fst` carry no information about `r`.

Chang and Pollard [chang_pollard1997], Example 2 (p. 293), observe for planar Lebesgue measure and a
coordinate projection that the image measure is not σ-finite and that no disintegration into
probability measures exists. The result for planar Lebesgue measure proved here is the analogue for
conditional cdfs.

## Counting measure on an axis: σ-finiteness of `ρ.fst` is not necessary

Let `ρ` be the image of counting measure on `ℝ` under `a ↦ (a, 0)`
(`Counterexample.CondCDF.countOnAxis`). Its first marginal is counting measure, which is not
s-finite, hence not σ-finite, because `ℝ` is uncountable and an s-finite measure has only countably
many atoms (`Counterexample.CondCDF.not_sFinite_count`). Neither is `ρ` s-finite, since the first
marginal of an s-finite measure is s-finite (`Counterexample.CondCDF.not_sFinite_countOnAxis`).

The constant family `fun _ ↦ cdf (dirac 0)` is a conditional cdf of `ρ`
(`Counterexample.CondCDF.isCondCDF_countOnAxis`). Testing the identity for the rays against a
singleton `{a}`, which has counting measure `1`, shows that every conditional cdf `F` of `ρ`
satisfies `ENNReal.ofReal (F a x) = ρ ({a} ×ˢ Iic x)` for all `a` and `x`. Hence any two conditional
cdfs of `ρ` agree at every point, and `ProbabilityTheory.HasUniqueCondCDF ρ` holds although `ρ.fst`
is not σ-finite (`Counterexample.CondCDF.hasUniqueCondCDF_countOnAxis`). This is why the domain of
`ProbabilityTheory.condCDF` is the class `HasUniqueCondCDF` rather than the hypothesis
`SigmaFinite ρ.fst`.

## References

* [J. T. Chang and D. Pollard, *Conditioning as disintegration*][chang_pollard1997]
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Counterexample.CondCDF

/-! ### Planar Lebesgue measure -/

/-- The first marginal of planar Lebesgue measure is infinity times Lebesgue measure. -/
lemma fst_volume : (volume : Measure (ℝ × ℝ)).fst = ∞ • (volume : Measure ℝ) := by
  rw [Measure.fst, Measure.volume_eq_prod, Measure.map_fst_prod]
  simp

/-- Every `IicSnd` of planar Lebesgue measure is its first marginal, so the Radon-Nikodym
derivatives `(volume.IicSnd r).rnDeriv volume.fst` do not depend on `r`. -/
lemma IicSnd_volume (r : ℝ) :
    (volume : Measure (ℝ × ℝ)).IicSnd r = (volume : Measure (ℝ × ℝ)).fst := by
  ext s hs
  rw [Measure.IicSnd_apply _ r hs, Measure.fst_apply hs, ← prod_univ, Measure.volume_eq_prod,
    Measure.prod_prod s (Iic r) hs measurableSet_Iic, Measure.prod_prod s univ hs
    MeasurableSet.univ, Real.volume_Iic, Real.volume_univ]

/-- The first marginal of planar Lebesgue measure is not σ-finite, although planar Lebesgue measure
is. -/
lemma not_sigmaFinite_fst_volume : ¬ SigmaFinite (volume : Measure (ℝ × ℝ)).fst := by
  intro h
  rw [fst_volume] at h
  -- A set of finite measure for `∞ • volume` is `volume`-null, and `ℝ` is not.
  have h_null (n : ℕ) : volume (spanningSets (∞ • (volume : Measure ℝ)) n) = 0 := by
    by_contra hn
    have h_lt := measure_spanningSets_lt_top (∞ • (volume : Measure ℝ)) n
    rw [Measure.smul_apply, smul_eq_mul, ENNReal.top_mul hn] at h_lt
    exact lt_irrefl _ h_lt
  have h_univ := measure_iUnion_null h_null
  rw [iUnion_spanningSets, Real.volume_univ] at h_univ
  exact ENNReal.top_ne_zero h_univ

/-- If every ray has positive `γ`-measure, the constant family `fun _ ↦ cdf γ` is a conditional cdf
of planar Lebesgue measure. -/
lemma isCondCDF_volume (γ : Measure ℝ) [IsProbabilityMeasure γ] (hγ : ∀ x, γ (Iic x) ≠ 0) :
    IsCondCDF (volume : Measure (ℝ × ℝ)) fun _ ↦ cdf γ where
  measurable _ := measurable_const
  tendsto_atBot_zero _ := tendsto_cdf_atBot γ
  tendsto_atTop_one _ := tendsto_cdf_atTop γ
  setLIntegral x s hs := by
    rw [setLIntegral_const, ofReal_cdf, fst_volume, Measure.smul_apply, smul_eq_mul,
      Measure.volume_eq_prod, Measure.prod_prod s (Iic x) hs measurableSet_Iic, Real.volume_Iic]
    by_cases hs₀ : volume s = 0 <;> simp [hs₀, hγ x]

/-- A σ-finite measure need not have a conditional cdf that is unique almost everywhere: this
fails for planar Lebesgue measure. -/
theorem not_hasUniqueCondCDF_volume : ¬ HasUniqueCondCDF (volume : Measure (ℝ × ℝ)) := by
  intro h
  -- Every ray has infinite Lebesgue measure, hence positive Gaussian measure.
  have h_pos (m : ℝ) (x : ℝ) : gaussianReal m 1 (Iic x) ≠ 0 := fun h ↦ by
    simpa using gaussianReal_absolutelyContinuous' m one_ne_zero h
  have h₀ := isCondCDF_volume (gaussianReal 0 1) (h_pos 0)
  have h₁ := isCondCDF_volume (gaussianReal 1 1) (h_pos 1)
  have h_ne : cdf (gaussianReal 0 1) ≠ cdf (gaussianReal 1 1) := fun h_eq ↦
    zero_ne_one (gaussianReal_ext_iff.1 (Measure.eq_of_cdf _ _ h_eq)).1
  -- Two conditional cdfs that differ at every point cannot agree almost everywhere.
  have h_ae := h.ae_eq_of_isCondCDF h₀ h₁
  simp only [h_ne, Filter.eventually_false_iff_eq_bot, ae_eq_bot, fst_volume] at h_ae
  simpa [Real.volume_univ] using congrArg (fun μ : Measure ℝ ↦ μ univ) h_ae

example : SigmaFinite (volume : Measure (ℝ × ℝ)) := inferInstance

/-! ### Counting measure on an axis -/

/-- Counting measure on `ℝ` is not s-finite, hence not σ-finite: in an s-finite measure space only
countably many disjoint measurable sets have positive measure, but all singletons of `ℝ` have
counting measure `1`. -/
lemma not_sFinite_count : ¬ SFinite (Measure.count : Measure ℝ) := by
  intro h
  have h_countable := Measure.countable_meas_pos_of_disjoint_iUnion
    (μ := (Measure.count : Measure ℝ)) (As := fun a : ℝ ↦ ({a} : Set ℝ))
    (fun a ↦ measurableSet_singleton a) (fun a b hab ↦ Set.disjoint_singleton.2 hab)
  have h_eq : {a : ℝ | 0 < (Measure.count : Measure ℝ) {a}} = univ := by
    ext a
    simp
  rw [h_eq] at h_countable
  exact Cardinal.not_countable_real h_countable

/-- Counting measure on `ℝ` is not σ-finite. -/
lemma not_sigmaFinite_count : ¬ SigmaFinite (Measure.count : Measure ℝ) := fun _ ↦
  not_sFinite_count inferInstance

/-- Counting measure on `ℝ`, pushed forward to the horizontal axis `ℝ × {0}` of the plane. -/
def countOnAxis : Measure (ℝ × ℝ) :=
  (Measure.count : Measure ℝ).map (fun a : ℝ ↦ (a, (0 : ℝ)))

/-- The first marginal of `countOnAxis` is counting measure. -/
lemma fst_countOnAxis : countOnAxis.fst = (Measure.count : Measure ℝ) := by
  rw [countOnAxis, Measure.fst_map_prodMk (X := fun a : ℝ ↦ a) (Y := fun _ : ℝ ↦ (0 : ℝ))
    measurable_id' measurable_const]
  exact Measure.map_id'

/-- `countOnAxis` is not s-finite, since its first marginal, counting measure, is not. -/
lemma not_sFinite_countOnAxis : ¬ SFinite countOnAxis := by
  intro h
  refine not_sFinite_count ?_
  rw [← fst_countOnAxis]
  infer_instance

/-- The constant family `fun _ ↦ cdf (dirac 0)` is a conditional cdf of `countOnAxis`. -/
lemma isCondCDF_countOnAxis : IsCondCDF countOnAxis fun _ ↦ cdf (Measure.dirac (0 : ℝ)) where
  measurable _ := measurable_const
  tendsto_atBot_zero _ := tendsto_cdf_atBot _
  tendsto_atTop_one _ := tendsto_cdf_atTop _
  setLIntegral x s hs := by
    rw [fst_countOnAxis, setLIntegral_const, ofReal_cdf, Measure.dirac_apply' _ measurableSet_Iic,
      countOnAxis, Measure.map_apply (hs.prod measurableSet_Iic), mk_preimage_prod_left_eq_if]
    by_cases hx : (0 : ℝ) ≤ x <;> simp [hx]

/-- `countOnAxis` has a conditional cdf that is unique almost everywhere, even though its first
marginal is not σ-finite. -/
theorem hasUniqueCondCDF_countOnAxis : HasUniqueCondCDF countOnAxis where
  exists_isCondCDF := ⟨_, isCondCDF_countOnAxis⟩
  ae_eq_of_isCondCDF F G hF hG := by
    -- Testing against singletons, which have counting measure `1`, determines every value.
    have h_apply {H : ℝ → StieltjesFunction ℝ} (hH : IsCondCDF countOnAxis H) (a x : ℝ) :
        ENNReal.ofReal (H a x) = countOnAxis ({a} ×ˢ Iic x) := by
      have := hH.setLIntegral x (measurableSet_singleton a)
      rwa [fst_countOnAxis, lintegral_singleton, Measure.count_singleton, mul_one] at this
    refine ae_of_all _ fun a ↦ ?_
    ext x
    exact (ENNReal.ofReal_eq_ofReal_iff (hF.nonneg a x) (hG.nonneg a x)).1
      ((h_apply hF a x).trans (h_apply hG a x).symm)

end Counterexample.CondCDF
