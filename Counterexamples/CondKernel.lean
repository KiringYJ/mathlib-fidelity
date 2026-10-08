/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module

public import Counterexamples.CondCDF
public import Mathlib.Probability.Kernel.Disintegration.Unique

/-!
# σ-finiteness and conditional kernels that are unique almost everywhere

A Markov kernel `η` disintegrates a measure `ρ` on `α × Ω` if `ρ.fst ⊗ₘ η = ρ`
(`MeasureTheory.Measure.IsCondKernel`), and `ρ` has a unique conditional kernel
(`MeasureTheory.Measure.HasUniqueCondKernel`) if such a kernel exists and any two agree
`ρ.fst`-almost everywhere. For a nonempty standard Borel space `Ω`, this holds if the first marginal
`ρ.fst` is σ-finite (`MeasureTheory.Measure.hasUniqueCondKernel_of_sigmaFinite_fst`), and for a
σ-finite `ρ` this condition is necessary
(`MeasureTheory.Measure.hasUniqueCondKernel_iff_sigmaFinite_fst`). We show that it is not necessary
in general, that without it a disintegration need not be unique or exist, and that a finite kernel
that disintegrates a measure with a unique conditional kernel need not represent it. We also show
that the measures with a unique conditional kernel and those with a unique conditional cdf
(`ProbabilityTheory.HasUniqueCondCDF`) are incomparable.

## An infinite point mass: σ-finiteness of `ρ.fst` is not necessary

The first marginal of `∞ • dirac ((), 0)` on `Unit × ℝ` is `∞ • dirac ()`, which is not σ-finite
(`Counterexample.CondKernel.not_sigmaFinite_fst_infDirac`). The constant kernel `dirac 0`
disintegrates it, and every Markov kernel that does is this kernel, since the set `univ ×ˢ {0}ᶜ`
is null. So the measure has a unique conditional kernel
(`Counterexample.CondKernel.hasUniqueCondKernel_infDirac`). The finite kernel `2 • dirac 0`, which
is not Markov, also disintegrates it, since infinity times a measure depends only on its null sets,
but it does not represent the conditional kernel
(`Counterexample.CondKernel.const_two_smul_dirac_not_mem_condKernel_infDirac`): a representative
must be a probability measure almost everywhere
(`MeasureTheory.Measure.mem_condKernel_iff_isCondKernel_and_ae_isProbabilityMeasure`), and
`2 • dirac 0` has mass `2` at the only point, which has infinite mass. It has no unique conditional
cdf: the constant cdfs of `dirac 0` and of `2⁻¹ • (dirac 0 + dirac 1)` are both conditional cdfs,
since infinity times a probability vanishes or not with the probability
(`Counterexample.CondKernel.not_hasUniqueCondCDF_infDirac`).

## A Gaussian fiber of infinite mass: a disintegration need not be unique

The constant kernels of all Gaussian distributions with positive variance disintegrate
`(∞ • dirac ()) ⊗ₘ Kernel.const Unit (gaussianReal 0 1)`, because these distributions have the same
null sets as Lebesgue measure, and infinity times a measure depends only on its null sets. Two
of them differ at the only point `()`, which has infinite mass, so the measure has no unique
conditional kernel (`Counterexample.CondKernel.not_hasUniqueCondKernel_infGaussian`).

## Planar Lebesgue measure: a disintegration need not exist

The first marginal of planar Lebesgue measure is infinity times Lebesgue measure
(`Counterexample.CondCDF.fst_volume`), so every integral against it is `0` or `∞`. Planar Lebesgue
measure gives the unit square mass `1`, so no kernel, Markov or not, disintegrates it
(`Counterexample.CondKernel.not_isCondKernel_volume`), and it has no unique conditional kernel
(`Counterexample.CondKernel.not_hasUniqueCondKernel_volume`). Chang and Pollard
[chang_pollard1997], Example 2 (p. 293), observe for planar Lebesgue measure and a coordinate
projection that no disintegration into probability measures exists; see also
`Counterexamples/CondCDF.lean`.

## Gaussian fibers over counting measure plus a segment: a unique conditional cdf, no disintegration

Let `ρ` be the sum of the composition-product of counting measure on `ℝ` with the constant kernel
`gaussianReal 0 1` and the image of Lebesgue measure on `[0, 1]` under `a ↦ (a, 0)`
(`Counterexample.CondKernel.countGaussianAddSegment`). Its first marginal is counting measure plus
Lebesgue measure on `[0, 1]`, which gives every singleton mass `1`. Testing against singletons
determines a conditional cdf everywhere, and the constant cdf of `gaussianReal 0 1` is one, so `ρ`
has a unique conditional cdf (`Counterexample.CondKernel.hasUniqueCondCDF_countGaussianAddSegment`).
Testing a disintegration `η` against `{a} ×ˢ {0}` gives `η a {0} = 0` for every `a`, because the
Gaussian fibers have no atoms; then `ρ.fst ⊗ₘ η` gives `univ ×ˢ {0}` mass `0`, while `ρ` gives it
mass `1`. So no kernel disintegrates `ρ`
(`Counterexample.CondKernel.not_isCondKernel_countGaussianAddSegment`), and `ρ` has no unique
conditional kernel (`Counterexample.CondKernel.not_hasUniqueCondKernel_countGaussianAddSegment`).

## References

* [J. T. Chang and D. Pollard, *Conditioning as disintegration*][chang_pollard1997]
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Counterexample.CondKernel

open Counterexample.CondCDF

/-- Infinity times the Dirac measure on `Unit` is not σ-finite, since a σ-finite measure gives a
point finite mass. -/
lemma not_sigmaFinite_top_smul_dirac_unit : ¬ SigmaFinite (∞ • Measure.dirac ()) := fun _ ↦ by
  simpa using measure_singleton_lt_top (μ := ∞ • Measure.dirac ()) (a := ())

/-- Infinity times a probability measure on `Unit` gives `()` infinite mass, so it is not zero. -/
lemma top_smul_dirac_unit_ne_zero : (∞ • Measure.dirac ()) ≠ 0 := fun h ↦ by
  simpa using congrArg (fun μ : Measure Unit ↦ μ univ) h

/-! ### An infinite point mass -/

/-- The infinite point mass `∞ • dirac ((), 0)` on `Unit × ℝ`. -/
def infDirac : Measure (Unit × ℝ) := ∞ • Measure.dirac ((), (0 : ℝ))

lemma fst_infDirac : infDirac.fst = ∞ • Measure.dirac () := by
  ext s hs
  rw [Measure.fst_apply hs, infDirac, Measure.smul_apply, Measure.smul_apply,
    Measure.dirac_apply' _ (measurable_fst hs), Measure.dirac_apply' _ hs]
  rfl

/-- The first marginal of `infDirac` is not σ-finite. -/
lemma not_sigmaFinite_fst_infDirac : ¬ SigmaFinite infDirac.fst := by
  rw [fst_infDirac]
  exact not_sigmaFinite_top_smul_dirac_unit

/-- The constant kernel `dirac 0` disintegrates `infDirac`. -/
lemma isCondKernel_infDirac :
    infDirac.IsCondKernel (Kernel.const Unit (Measure.dirac (0 : ℝ))) := by
  refine ⟨inferInstance, ?_⟩
  ext s hs
  rw [Measure.compProd_apply hs, fst_infDirac, lintegral_smul_measure, lintegral_dirac,
    Kernel.const_apply, infDirac, Measure.smul_apply, Measure.dirac_apply' _ hs,
    Measure.dirac_apply' _ (measurable_prodMk_left hs)]
  rfl

/-- Every Markov kernel that disintegrates `infDirac` is the constant kernel `dirac 0`: the set
`univ ×ˢ {0}ᶜ` is `infDirac`-null, so its fiber `{0}ᶜ` is null for the kernel. -/
lemma eq_dirac_of_isCondKernel_infDirac (η : Kernel Unit ℝ) [IsMarkovKernel η]
    [infDirac.IsCondKernel η] : η () = Measure.dirac 0 := by
  have hs : MeasurableSet ((univ : Set Unit) ×ˢ ({(0 : ℝ)}ᶜ : Set ℝ)) :=
    MeasurableSet.univ.prod (measurableSet_singleton 0).compl
  have h := congrArg (fun ν : Measure (Unit × ℝ) ↦ ν (univ ×ˢ {(0 : ℝ)}ᶜ))
    (infDirac.disintegrate η)
  rw [Measure.compProd_apply hs, fst_infDirac, lintegral_smul_measure, lintegral_dirac,
    mk_preimage_prod_right (mem_univ ()), infDirac, Measure.smul_apply,
    Measure.dirac_apply' _ hs] at h
  have h0 : η () {(0 : ℝ)}ᶜ = 0 := by
    simpa using h
  ext t ht
  rw [Measure.dirac_apply' _ ht]
  by_cases h0t : (0 : ℝ) ∈ t
  · rw [indicator_of_mem h0t, Pi.one_apply, ← prob_compl_eq_zero_iff ht]
    exact measure_mono_null (compl_subset_compl.2 (singleton_subset_iff.2 h0t)) h0
  · rw [indicator_of_notMem h0t]
    exact measure_mono_null (subset_compl_singleton_iff.2 h0t) h0

/-- `infDirac` has a unique conditional kernel, although its first marginal is not σ-finite. -/
instance hasUniqueCondKernel_infDirac : infDirac.HasUniqueCondKernel where
  exists_isMarkovKernel_isCondKernel := ⟨_, inferInstance, isCondKernel_infDirac⟩
  ae_eq_of_isCondKernel η η' _ _ _ _ := ae_of_all _ fun a ↦ by
    rw [Subsingleton.elim a (), eq_dirac_of_isCondKernel_infDirac η,
      eq_dirac_of_isCondKernel_infDirac η']

/-- The finite kernel `2 • dirac 0`, which is not Markov, also disintegrates `infDirac`: infinity
times a measure depends only on its null sets. -/
lemma isCondKernel_two_smul_infDirac :
    infDirac.IsCondKernel (Kernel.const Unit ((2 : ℝ≥0∞) • Measure.dirac (0 : ℝ))) := by
  refine ⟨inferInstance, ?_⟩
  ext s hs
  rw [Measure.compProd_apply hs, fst_infDirac, lintegral_smul_measure, lintegral_dirac,
    Kernel.const_apply, infDirac, Measure.smul_apply, Measure.smul_apply,
    Measure.dirac_apply' _ hs, Measure.dirac_apply' _ (measurable_prodMk_left hs)]
  by_cases h : ((), (0 : ℝ)) ∈ s
  · have h' : (0 : ℝ) ∈ Prod.mk () ⁻¹' s := h
    simp [indicator_of_mem h, indicator_of_mem h', smul_eq_mul, ENNReal.top_mul]
  · have h' : (0 : ℝ) ∉ Prod.mk () ⁻¹' s := h
    simp [indicator_of_notMem h, indicator_of_notMem h', smul_eq_mul]

/-- The finite kernel `2 • dirac 0` disintegrates `infDirac` but does not represent its conditional
kernel, which is the class of `dirac 0`: the two kernels differ at the only point, which has
infinite mass. So for a measure with a unique conditional kernel alone, a finite kernel that
disintegrates it need not represent its conditional kernel. -/
theorem const_two_smul_dirac_not_mem_condKernel_infDirac :
    Kernel.const Unit ((2 : ℝ≥0∞) • Measure.dirac (0 : ℝ)) ∉ infDirac.condKernel := by
  intro h
  have h₀ : Kernel.const Unit (Measure.dirac (0 : ℝ)) ∈ infDirac.condKernel :=
    Measure.mem_condKernel_iff_of_isMarkovKernel.2 isCondKernel_infDirac
  have h_ae := Kernel.AEClass.eventuallyEq_of_mem h h₀
  have h_ne : (2 : ℝ≥0∞) • Measure.dirac (0 : ℝ) ≠ Measure.dirac 0 := fun h_eq ↦ by
    have := congrArg (fun μ : Measure ℝ ↦ μ univ) h_eq
    simp at this
  simp only [Filter.EventuallyEq, Kernel.const_apply, h_ne, Filter.eventually_false_iff_eq_bot,
    ae_eq_bot, fst_infDirac] at h_ae
  exact top_smul_dirac_unit_ne_zero h_ae

/-- If a probability measure `γ` gives a ray `Iic x` positive mass exactly when `0 ≤ x`, the
constant family `fun _ ↦ cdf γ` is a conditional cdf of `infDirac`. -/
lemma isCondCDF_infDirac (γ : Measure ℝ) [IsProbabilityMeasure γ]
    (hγ : ∀ x, γ (Iic x) = 0 ↔ x < 0) : IsCondCDF infDirac fun _ ↦ cdf γ where
  measurable _ := measurable_const
  tendsto_atBot_zero _ := tendsto_cdf_atBot γ
  tendsto_atTop_one _ := tendsto_cdf_atTop γ
  setLIntegral x s hs := by
    rw [setLIntegral_const, ofReal_cdf, fst_infDirac, Measure.smul_apply, infDirac,
      Measure.smul_apply, Measure.dirac_apply' _ hs,
      Measure.dirac_apply' _ (hs.prod measurableSet_Iic)]
    by_cases hs₀ : () ∈ s <;> by_cases hx : x < 0
    · simp [hs₀, hx, (hγ x).2 hx]
    · have hx' : γ (Iic x) ≠ 0 := fun h ↦ hx ((hγ x).1 h)
      simp [hs₀, not_lt.1 hx, hx']
    · simp [hs₀]
    · simp [hs₀]

/-- The probability measure `2⁻¹ • (dirac 0 + dirac 1)` on `ℝ`. -/
def halfDiracZeroOne : Measure ℝ := (2⁻¹ : ℝ≥0∞) • (Measure.dirac 0 + Measure.dirac 1)

instance : IsProbabilityMeasure halfDiracZeroOne :=
  ⟨by simp [halfDiracZeroOne, ENNReal.inv_two_add_inv_two]⟩

/-- `infDirac` has no unique conditional cdf, although it has a unique conditional kernel. -/
theorem not_hasUniqueCondCDF_infDirac : ¬ HasUniqueCondCDF infDirac := by
  intro h
  have h₀ := isCondCDF_infDirac (Measure.dirac 0) fun x ↦ by
    by_cases hx : x < 0 <;> simp [Measure.dirac_apply' _ measurableSet_Iic, hx, not_lt.1]
  have h₁ := isCondCDF_infDirac halfDiracZeroOne fun x ↦ by
    by_cases hx : x < 0
    · have hx1 : ¬ (1 : ℝ) ≤ x := fun h ↦ by linarith
      simp [halfDiracZeroOne, Measure.dirac_apply' _ measurableSet_Iic, hx, hx1, not_le.2 hx]
    · simp [halfDiracZeroOne, Measure.dirac_apply' _ measurableSet_Iic, hx, not_lt.1 hx]
  have h_ne : cdf (Measure.dirac (0 : ℝ)) ≠ cdf halfDiracZeroOne := fun h_eq ↦ by
    have h1 := congrArg (fun ν : Measure ℝ ↦ ν {1}) (Measure.eq_of_cdf _ _ h_eq)
    simp [halfDiracZeroOne] at h1
    exact ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top h1.symm
  have h_ae := h.ae_eq_of_isCondCDF h₀ h₁
  simp only [h_ne, Filter.eventually_false_iff_eq_bot, ae_eq_bot, fst_infDirac] at h_ae
  exact top_smul_dirac_unit_ne_zero h_ae

/-! ### A Gaussian fiber of infinite mass -/

/-- The composition-product of the infinite point mass `∞ • dirac ()` with the constant kernel
`gaussianReal 0 1`. -/
def infGaussian : Measure (Unit × ℝ) :=
  (∞ • Measure.dirac ()) ⊗ₘ Kernel.const Unit (gaussianReal 0 1)

/-- A Gaussian distribution with positive variance has the same null sets as Lebesgue measure. -/
lemma gaussianReal_eq_zero_iff (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) {t : Set ℝ} :
    gaussianReal m v t = 0 ↔ volume t = 0 :=
  ⟨fun h ↦ gaussianReal_absolutelyContinuous' m hv h,
    fun h ↦ gaussianReal_absolutelyContinuous m hv h⟩

/-- The constant kernel of every Gaussian distribution with positive variance disintegrates
`infGaussian`. -/
lemma isCondKernel_infGaussian (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    infGaussian.IsCondKernel (Kernel.const Unit (gaussianReal m v)) := by
  refine ⟨inferInstance, ?_⟩
  rw [infGaussian, Measure.fst_compProd]
  ext s hs
  rw [Measure.compProd_apply hs, Measure.compProd_apply hs, lintegral_smul_measure,
    lintegral_smul_measure, lintegral_dirac, lintegral_dirac, Kernel.const_apply,
    Kernel.const_apply, smul_eq_mul, smul_eq_mul]
  by_cases h : volume (Prod.mk () ⁻¹' s) = 0
  · rw [(gaussianReal_eq_zero_iff m hv).2 h, (gaussianReal_eq_zero_iff 0 one_ne_zero).2 h]
  · rw [ENNReal.top_mul (mt (gaussianReal_eq_zero_iff m hv).1 h),
      ENNReal.top_mul (mt (gaussianReal_eq_zero_iff 0 one_ne_zero).1 h)]

/-- `infGaussian` has no unique conditional kernel: the constant kernels of `gaussianReal 0 1` and
`gaussianReal 1 1` disintegrate it and differ at `()`, which has infinite mass. -/
theorem not_hasUniqueCondKernel_infGaussian : ¬ infGaussian.HasUniqueCondKernel := by
  intro h
  have := isCondKernel_infGaussian 0 one_ne_zero
  have := isCondKernel_infGaussian 1 one_ne_zero
  have h_ae := h.ae_eq_of_isCondKernel (Kernel.const Unit (gaussianReal 0 1))
    (Kernel.const Unit (gaussianReal 1 1))
  have h_ne : gaussianReal 0 1 ≠ gaussianReal 1 1 := fun h_eq ↦
    zero_ne_one (gaussianReal_ext_iff.1 h_eq).1
  simp only [Kernel.const_apply, h_ne, Filter.eventually_false_iff_eq_bot, ae_eq_bot,
    infGaussian, Measure.fst_compProd] at h_ae
  exact top_smul_dirac_unit_ne_zero h_ae

/-- The first marginal of `infGaussian` is not σ-finite. -/
lemma not_sigmaFinite_fst_infGaussian : ¬ SigmaFinite infGaussian.fst := by
  rw [infGaussian, Measure.fst_compProd]
  exact not_sigmaFinite_top_smul_dirac_unit

/-! ### Planar Lebesgue measure -/

/-- No kernel disintegrates planar Lebesgue measure: every integral against its first marginal,
infinity times Lebesgue measure, is `0` or `∞`, while the unit square has mass `1`. -/
theorem not_isCondKernel_volume (η : Kernel ℝ ℝ) :
    ¬ (volume : Measure (ℝ × ℝ)).IsCondKernel η := by
  intro h
  have hs : MeasurableSet (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :=
    measurableSet_Icc.prod measurableSet_Icc
  have h1 : ((volume : Measure (ℝ × ℝ)).fst ⊗ₘ η) (Icc 0 1 ×ˢ Icc 0 1) = 1 := by
    rw [Measure.disintegrate, Measure.volume_eq_prod, Measure.prod_prod _ _ measurableSet_Icc
      measurableSet_Icc, Real.volume_Icc]
    simp
  rw [Measure.compProd_apply hs, fst_volume, lintegral_smul_measure, smul_eq_mul] at h1
  rcases eq_or_ne (∫⁻ a, η a (Prod.mk a ⁻¹' (Icc 0 1 ×ˢ Icc 0 1)) ∂volume) 0 with h0 | h0
  · rw [h0, mul_zero] at h1
    exact zero_ne_one h1
  · rw [ENNReal.top_mul h0] at h1
    exact ENNReal.top_ne_one h1

/-- Planar Lebesgue measure has no unique conditional kernel, since no kernel disintegrates it. -/
theorem not_hasUniqueCondKernel_volume : ¬ (volume : Measure (ℝ × ℝ)).HasUniqueCondKernel :=
  fun h ↦ let ⟨η, _, hη⟩ := h.exists_isMarkovKernel_isCondKernel
    not_isCondKernel_volume η hη

/-! ### Gaussian fibers over counting measure and a segment -/

/-- The composition-product of counting measure on `ℝ` with the constant kernel `gaussianReal 0 1`,
plus the image of Lebesgue measure on `[0, 1]` under `a ↦ (a, 0)`. -/
def countGaussianAddSegment : Measure (ℝ × ℝ) :=
  (Measure.count : Measure ℝ) ⊗ₘ Kernel.const ℝ (gaussianReal 0 1) +
    (volume.restrict (Icc (0 : ℝ) 1)).map (fun a : ℝ ↦ (a, (0 : ℝ)))

lemma fst_countGaussianAddSegment :
    countGaussianAddSegment.fst = Measure.count + volume.restrict (Icc (0 : ℝ) 1) := by
  rw [countGaussianAddSegment, Measure.fst_add, Measure.fst_compProd,
    Measure.fst_map_prodMk (X := fun a : ℝ ↦ a) (Y := fun _ : ℝ ↦ (0 : ℝ)) measurable_id'
      measurable_const, Measure.map_id']

/-- Every singleton has mass `1` for the first marginal of `countGaussianAddSegment`. -/
lemma fst_countGaussianAddSegment_singleton (a : ℝ) :
    countGaussianAddSegment.fst {a} = 1 := by
  rw [fst_countGaussianAddSegment, Measure.add_apply, Measure.count_singleton,
    Measure.restrict_apply (measurableSet_singleton a),
    measure_mono_null inter_subset_left (measure_singleton a), add_zero]

/-- The constant family `fun _ ↦ cdf (gaussianReal 0 1)` is a conditional cdf of
`countGaussianAddSegment`. On a finite set the segment contributes nothing, and an infinite set
has infinite counting measure. -/
lemma isCondCDF_countGaussianAddSegment :
    IsCondCDF countGaussianAddSegment fun _ ↦ cdf (gaussianReal 0 1) where
  measurable _ := measurable_const
  tendsto_atBot_zero _ := tendsto_cdf_atBot _
  tendsto_atTop_one _ := tendsto_cdf_atTop _
  setLIntegral x s hs := by
    have hγ : gaussianReal 0 1 (Iic x) ≠ 0 := fun h ↦ by
      simpa using gaussianReal_absolutelyContinuous' 0 one_ne_zero h
    rw [setLIntegral_const, ofReal_cdf, fst_countGaussianAddSegment, countGaussianAddSegment,
      Measure.add_apply, Measure.add_apply, Measure.compProd_apply_prod hs measurableSet_Iic,
      Measure.map_apply (hs.prod measurableSet_Iic), mk_preimage_prod_left_eq_if,
      Measure.restrict_apply hs]
    simp only [Kernel.const_apply, setLIntegral_const]
    rcases s.finite_or_infinite with hfin | hinf
    · have h0 : volume (s ∩ Icc (0 : ℝ) 1) = 0 :=
        measure_mono_null inter_subset_left (hfin.measure_zero volume)
      split_ifs <;> simp [h0]
    · simp [Measure.count_apply_infinite hinf, ENNReal.mul_top hγ]

/-- `countGaussianAddSegment` has a conditional cdf that is unique almost everywhere: every
singleton has mass `1` for the first marginal, so testing against singletons determines every
value. -/
theorem hasUniqueCondCDF_countGaussianAddSegment : HasUniqueCondCDF countGaussianAddSegment where
  exists_isCondCDF := ⟨_, isCondCDF_countGaussianAddSegment⟩
  ae_eq_of_isCondCDF F G hF hG := by
    have h_apply {H : ℝ → StieltjesFunction ℝ} (hH : IsCondCDF countGaussianAddSegment H)
        (a x : ℝ) : ENNReal.ofReal (H a x) = countGaussianAddSegment ({a} ×ˢ Iic x) := by
      have := hH.setLIntegral x (measurableSet_singleton a)
      rwa [lintegral_singleton, fst_countGaussianAddSegment_singleton, mul_one] at this
    refine ae_of_all _ fun a ↦ ?_
    ext x
    exact (ENNReal.ofReal_eq_ofReal_iff (hF.nonneg a x) (hG.nonneg a x)).1
      ((h_apply hF a x).trans (h_apply hG a x).symm)

/-- No kernel disintegrates `countGaussianAddSegment`, although it has a unique conditional cdf.
Testing a disintegration against `{a} ×ˢ {0}`, which is null because the Gaussian fibers have no
atoms, gives the kernel no mass at `0`, but the axis `univ ×ˢ {0}` has mass `1`. -/
theorem not_isCondKernel_countGaussianAddSegment (η : Kernel ℝ ℝ) :
    ¬ countGaussianAddSegment.IsCondKernel η := by
  intro h
  have hγ0 : gaussianReal 0 1 {0} = 0 :=
    gaussianReal_absolutelyContinuous 0 one_ne_zero (Real.volume_singleton)
  have h_point (a : ℝ) : countGaussianAddSegment ({a} ×ˢ {0}) = 0 := by
    rw [countGaussianAddSegment, Measure.add_apply,
      Measure.compProd_apply_prod (measurableSet_singleton a) (measurableSet_singleton 0),
      Measure.map_apply ((measurableSet_singleton a).prod (measurableSet_singleton 0)),
      mk_preimage_prod_left_eq_if]
    simp [Kernel.const_apply, hγ0, measure_mono_null inter_subset_left (measure_singleton a),
      Measure.restrict_apply (measurableSet_singleton a)]
  have h_kernel (a : ℝ) : η a {0} = 0 := by
    have h_eq := congrArg (fun ν : Measure (ℝ × ℝ) ↦ ν ({a} ×ˢ {0}))
      (countGaussianAddSegment.disintegrate η)
    rwa [h_point, Measure.compProd_apply_prod (measurableSet_singleton a)
      (measurableSet_singleton 0), lintegral_singleton, fst_countGaussianAddSegment_singleton,
      mul_one] at h_eq
  have h_axis := congrArg (fun ν : Measure (ℝ × ℝ) ↦ ν (univ ×ˢ {0}))
    (countGaussianAddSegment.disintegrate η)
  rw [Measure.compProd_apply_prod MeasurableSet.univ (measurableSet_singleton 0),
    Measure.restrict_univ] at h_axis
  simp only [h_kernel, lintegral_zero] at h_axis
  have h_seg : ((volume.restrict (Icc (0 : ℝ) 1)).map fun a : ℝ ↦ (a, (0 : ℝ)))
      (univ ×ˢ {0}) = 1 := by
    rw [Measure.map_apply (MeasurableSet.univ.prod (measurableSet_singleton 0)),
      mk_preimage_prod_left_eq_if]
    simp [Real.volume_Icc]
  have h_ne : countGaussianAddSegment (univ ×ˢ {0}) ≠ 0 := by
    rw [countGaussianAddSegment, Measure.add_apply, h_seg]
    simp
  exact h_ne h_axis.symm

/-- `countGaussianAddSegment` has no unique conditional kernel, although it has a unique
conditional cdf; with `infDirac`, which has a unique conditional kernel but no unique conditional
cdf, this shows that the two classes are incomparable. -/
theorem not_hasUniqueCondKernel_countGaussianAddSegment :
    ¬ countGaussianAddSegment.HasUniqueCondKernel :=
  fun h ↦ let ⟨η, _, hη⟩ := h.exists_isMarkovKernel_isCondKernel
    not_isCondKernel_countGaussianAddSegment η hη

end Counterexample.CondKernel
