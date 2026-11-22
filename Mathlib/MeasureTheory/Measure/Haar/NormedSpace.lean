/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Basic properties of Haar measures on real vector spaces

-/

public section

noncomputable section

open Function Filter Inv MeasureTheory.Measure Module Set TopologicalSpace
open scoped NNReal ENNReal Pointwise Topology

namespace MeasureTheory

namespace Measure

/-- The instance `MeasureTheory.Measure.IsAddHaarMeasure.nullSingletonClass` applies in particular
to show that an additive Haar measure on a nontrivial finite-dimensional real vector space has no
atom. -/
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E] [FiniteDimensional ℝ E]
    [SigmaAlgebra E] [BorelSpace E] (μ : Measure E) [IsAddHaarMeasure μ] :
    NullSingletonClass μ := by
  infer_instance

section LinearEquiv

variable {𝕜 G H : Type*} [SigmaAlgebra G] [SigmaAlgebra H] [NontriviallyNormedField 𝕜]
  [TopologicalSpace G] [TopologicalSpace H] [AddCommGroup G] [AddCommGroup H]
  [IsTopologicalAddGroup G] [IsTopologicalAddGroup H] [Module 𝕜 G] [Module 𝕜 H] (μ : Measure G)
  [IsAddHaarMeasure μ] [BorelSpace G] [BorelSpace H]
  [CompleteSpace 𝕜] [T2Space G] [FiniteDimensional 𝕜 G] [ContinuousSMul 𝕜 G]
  [ContinuousSMul 𝕜 H] [T2Space H]

instance MapLinearEquiv.isAddHaarMeasure (e : G ≃ₗ[𝕜] H) :
    IsAddHaarMeasure (μ.map e e.toContinuousLinearEquiv.continuous.measurable.aemeasurable) :=
  e.toContinuousLinearEquiv.isAddHaarMeasure_map _

end LinearEquiv

section SeminormedGroup
variable {G H : Type*} [SigmaAlgebra G] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [BorelSpace G] [LocallyCompactSpace G]
  [SigmaAlgebra H] [SeminormedGroup H] [OpensSigmaAlgebra H]

-- TODO: This could be streamlined by proving that inner regular measures always exist
open Metric Bornology in
@[to_additive]
lemma _root_.MonoidHom.exists_nhds_isBounded (f : G →* H) (hf : Measurable f) (x : G) :
    ∃ s ∈ 𝓝 x, IsBounded (f '' s) := by
  let K : PositiveCompacts G := Classical.arbitrary _
  obtain ⟨n, hn⟩ : ∃ n : ℕ, 0 < haar (interior K ∩ f ⁻¹' ball 1 n) := by
    by_contra!
    simp_rw [nonpos_iff_eq_zero, ← measure_iUnion_null_iff, ← inter_iUnion, ← preimage_iUnion,
      iUnion_ball_nat, preimage_univ, inter_univ] at this
    exact this.not_gt <| isOpen_interior.measure_pos _ K.interior_nonempty
  rw [← mul_one x, ← smul_eq_mul]
  refine ⟨_, smul_mem_nhds_smul _ <| div_mem_nhds_one_of_haar_pos_ne_top haar _
    (isOpen_interior.measurableSet.inter <| hf measurableSet_ball) hn <|
      mt (measure_mono_top <| inter_subset_left.trans interior_subset) K.isCompact.measure_ne_top,
    ?_⟩
  have : Bornology.IsBounded (f '' (interior K ∩ f ⁻¹' ball 1 n)) :=
    isBounded_ball.subset <| (image_mono inter_subset_right).trans <| image_preimage_subset _ _
  rw [image_smul_distrib, image_mul, image_inv]
  exact (this.mul this.inv).smul _

end SeminormedGroup

/-- A Borel-measurable group hom from a locally compact normed group to a real normed space is
continuous. -/
lemma AddMonoidHom.continuous_of_measurable {G H : Type*}
    [SeminormedAddCommGroup G] [SigmaAlgebra G] [BorelSpace G] [LocallyCompactSpace G]
    [SeminormedAddCommGroup H] [SigmaAlgebra H] [OpensSigmaAlgebra H] [NormedSpace ℝ H]
    (f : G →+ H) (hf : Measurable f) : Continuous f :=
  let ⟨_s, hs, hbdd⟩ := f.exists_nhds_isBounded hf 0; f.continuous_of_isBounded_nhds_zero hs hbdd

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [SigmaAlgebra E] [BorelSpace E]
  [FiniteDimensional ℝ E] (μ : Measure E) [IsAddHaarMeasure μ] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- The integral of `f (R • x)` with respect to an additive Haar measure is a multiple of the
integral of `f` whenever the scaling determinant is invertible. This includes every scalar
in dimension zero. -/
theorem integral_comp_smul (f : E → F) (R : ℝ) {hR : IsUnit (R ^ finrank ℝ E)} :
    ∫ x, f (R • x) ∂μ = |(R ^ finrank ℝ E)⁻¹| • ∫ x, f x ∂μ := by
  by_cases hF : CompleteSpace F; swap
  · simp [integral, hF]
  rcases eq_or_ne R 0 with (rfl | hR₀)
  · have hE : finrank ℝ E = 0 := by
      by_contra h
      exact hR.ne_zero (zero_pow h)
    have : Subsingleton E := finrank_zero_iff.1 hE
    have hf : (fun x : E ↦ f ((0 : ℝ) • x)) = f := by
      funext x
      exact congrArg f (Subsingleton.elim _ _)
    have hinv : ((0 : ℝ) ^ finrank ℝ E)⁻¹ = 1 := by
      apply inv_eq_of_mul_eq_one_right₀
      simp only [hE, pow_zero, mul_one]
    rw [hf, hinv, abs_one, one_smul]
  · calc
      (∫ x, f (R • x) ∂μ) = ∫ y, f y ∂Measure.map (fun x => R • x) μ :=
        (integral_map_equiv (Homeomorph.smul hR₀.isUnit.unit).toMeasurableEquiv
            f).symm
      _ = |(R ^ finrank ℝ E)⁻¹| • ∫ x, f x ∂μ := by
        simp only [map_addHaar_smul μ hR₀, integral_smul_measure, ENNReal.toReal_ofReal, abs_nonneg]

/-- Scaling by a nonnegative real with invertible determinant multiplies a Haar integral
by the reciprocal determinant. -/
theorem integral_comp_smul_of_nonneg (f : E → F) (R : ℝ)
    {hR : IsUnit (R ^ finrank ℝ E)} {hR₀ : 0 ≤ R} :
    ∫ x, f (R • x) ∂μ = (R ^ finrank ℝ E)⁻¹ • ∫ x, f x ∂μ := by
  rw [integral_comp_smul μ f R (hR := hR), abs_of_nonneg (inv_nonneg.2 (pow_nonneg hR₀ _))]

/-- The integral of `f (R⁻¹ • x)` with respect to an additive Haar measure is a multiple of the
integral of `f` for an invertible scalar `R`. -/
theorem integral_comp_inv_smul (f : E → F) (R : ℝ) {hR : IsUnit R} :
    ∫ x, f (R⁻¹ • x) ∂μ = |R ^ finrank ℝ E| • ∫ x, f x ∂μ := by
  have he : (R⁻¹ ^ finrank ℝ E)⁻¹ = R ^ finrank ℝ E := by
    apply inv_eq_of_mul_eq_one_right₀
    rw [inv_pow₀, inv_mul_cancel₀]
  rw [integral_comp_smul μ f R⁻¹ (hR := hR.inv₀.pow _), he]

/-- Scaling by the reciprocal of a nonnegative unit multiplies a Haar integral by the
determinant of the original scaling. -/
theorem integral_comp_inv_smul_of_nonneg (f : E → F) {R : ℝ}
    {hR : IsUnit R} (hR₀ : 0 ≤ R) :
    ∫ x, f (R⁻¹ • x) ∂μ = R ^ finrank ℝ E • ∫ x, f x ∂μ := by
  rw [integral_comp_inv_smul μ f R (hR := hR), abs_of_nonneg (pow_nonneg hR₀ _)]

theorem setIntegral_comp_smul (f : E → F) {R : ℝ} (s : Set E) (hR : R ≠ 0) :
    ∫ x in s, f (R • x) ∂μ = |(R ^ finrank ℝ E)⁻¹| • ∫ x in R • s, f x ∂μ := by
  let e : E ≃ᵐ E := (Homeomorph.smul (Units.mk0 R hR)).toMeasurableEquiv
  calc
  ∫ x in s, f (R • x) ∂μ
    = ∫ x in e ⁻¹' e.symm ⁻¹' s, f (e x) ∂μ := by simp [← preimage_comp]; rfl
  _ = ∫ y in e.symm ⁻¹' s, f y ∂map (fun x ↦ R • x) μ := (setIntegral_map_equiv _ _ _).symm
  _ = |(R ^ finrank ℝ E)⁻¹| • ∫ y in e.symm ⁻¹' s, f y ∂μ := by
    simp [map_addHaar_smul μ hR, integral_smul_measure, ENNReal.toReal_ofReal, abs_nonneg]
  _ = |(R ^ finrank ℝ E)⁻¹| • ∫ x in R • s, f x ∂μ := by
    congr 3
    ext y
    rw [mem_smul_set_iff_inv_smul_mem₀ hR]
    rfl

theorem setIntegral_comp_smul_of_pos (f : E → F) {R : ℝ} (s : Set E) (hR : 0 < R) :
    ∫ x in s, f (R • x) ∂μ = (R ^ finrank ℝ E)⁻¹ • ∫ x in R • s, f x ∂μ := by
  rw [setIntegral_comp_smul μ f s hR.ne', abs_of_nonneg (inv_nonneg.2 (pow_nonneg hR.le _))]

theorem integral_comp_mul_left (g : ℝ → F) (a : ℝ) {ha : IsUnit a} :
    (∫ x : ℝ, g (a * x)) = |a⁻¹| • ∫ y : ℝ, g y := by
  simpa only [smul_eq_mul, finrank_self, pow_one] using
    integral_comp_smul volume g a (hR := ha.pow _)

theorem integral_comp_inv_mul_left (g : ℝ → F) (a : ℝ) {ha : IsUnit a} :
    (∫ x : ℝ, g (a⁻¹ * x)) = |a| • ∫ y : ℝ, g y := by
  simpa only [smul_eq_mul, finrank_self, pow_one] using
    integral_comp_inv_smul volume g a (hR := ha)

theorem integral_comp_mul_right (g : ℝ → F) (a : ℝ) {ha : IsUnit a} :
    (∫ x : ℝ, g (x * a)) = |a⁻¹| • ∫ y : ℝ, g y := by
  simpa only [mul_comm] using integral_comp_mul_left g a (ha := ha)

theorem integral_comp_inv_mul_right (g : ℝ → F) (a : ℝ) {ha : IsUnit a} :
    (∫ x : ℝ, g (x * a⁻¹)) = |a| • ∫ y : ℝ, g y := by
  simpa only [mul_comm] using integral_comp_inv_mul_left g a (ha := ha)

theorem integral_comp_div (g : ℝ → F) (a : ℝ) {ha : IsUnit a} :
    (∫ x : ℝ, g (x / a)) = |a| • ∫ y : ℝ, g y := by
  simpa only [div_eq_mul_inv₀] using integral_comp_inv_mul_right g a (ha := ha)

end Measure

variable {F : Type*} [NormedAddCommGroup F]

theorem integrable_comp_smul_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [SigmaAlgebra E] [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measure E) [IsAddHaarMeasure μ]
    (f : E → F) {R : ℝ} (hR : R ≠ 0) : Integrable (fun x => f (R • x)) μ ↔ Integrable f μ := by
  -- reduce to one-way implication
  suffices
    ∀ {g : E → F} (_ : Integrable g μ) {S : ℝ} (_ : S ≠ 0), Integrable (fun x => g (S • x)) μ by
    refine ⟨fun hf => ?_, fun hf => this hf hR⟩
    convert! this hf (inv_ne_zero (ha := hR.isUnit))
    rw [← mul_smul, mul_inv_cancel₀, one_smul]
  -- now prove
  intro g hg S hS
  let t := ((Homeomorph.smul (isUnit_iff_ne_zero.2 hS).unit).toMeasurableEquiv : E ≃ᵐ E)
  refine (integrable_map_equiv t g).mp (?_ : Integrable g (map (S • ·) μ))
  rwa [map_addHaar_smul μ hS, integrable_smul_measure _ ENNReal.ofReal_ne_top]
  simpa only [Ne, ENNReal.ofReal_eq_zero, not_le, abs_pos] using
    (inv_ne_zero (ha := hS.isUnit.pow (finrank ℝ E)))

theorem Integrable.comp_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [SigmaAlgebra E] [BorelSpace E] [FiniteDimensional ℝ E] {μ : Measure E} [IsAddHaarMeasure μ]
    {f : E → F} (hf : Integrable f μ) {R : ℝ} (hR : R ≠ 0) : Integrable (fun x => f (R • x)) μ :=
  (integrable_comp_smul_iff μ f hR).2 hf

theorem integrable_comp_mul_left_iff (g : ℝ → F) {R : ℝ} (hR : R ≠ 0) :
    (Integrable fun x => g (R * x)) ↔ Integrable g := by
  simpa only [smul_eq_mul] using integrable_comp_smul_iff volume g hR

theorem Integrable.comp_mul_left' {g : ℝ → F} (hg : Integrable g) {R : ℝ} (hR : R ≠ 0) :
    Integrable fun x => g (R * x) :=
  (integrable_comp_mul_left_iff g hR).2 hg

theorem integrable_comp_mul_right_iff (g : ℝ → F) {R : ℝ} (hR : R ≠ 0) :
    (Integrable fun x => g (x * R)) ↔ Integrable g := by
  simpa only [mul_comm] using integrable_comp_mul_left_iff g hR

theorem Integrable.comp_mul_right' {g : ℝ → F} (hg : Integrable g) {R : ℝ} (hR : R ≠ 0) :
    Integrable fun x => g (x * R) :=
  (integrable_comp_mul_right_iff g hR).2 hg

theorem integrable_comp_div_iff (g : ℝ → F) {R : ℝ} {hR : IsUnit R} :
    (Integrable fun x => g (x / R)) ↔ Integrable g := by
  simpa only [div_eq_mul_inv₀] using
    integrable_comp_mul_right_iff g (inv_ne_zero (ha := hR))

theorem Integrable.comp_div {g : ℝ → F} (hg : Integrable g) {R : ℝ} {hR : IsUnit R} :
    Integrable fun x => g (x / R) :=
  (integrable_comp_div_iff g (hR := hR)).2 hg

section InnerProductSpace

variable {E' F' A : Type*}
variable [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
  [SigmaAlgebra E'] [BorelSpace E']
variable [NormedAddCommGroup F'] [InnerProductSpace ℝ F'] [FiniteDimensional ℝ F']
  [SigmaAlgebra F'] [BorelSpace F']

variable (f : E' ≃ₗᵢ[ℝ] F')
variable [NormedAddCommGroup A]

theorem integrable_comp (g : F' → A) : Integrable (g ∘ f) ↔ Integrable g :=
  f.measurePreserving.integrable_comp_emb f.toMeasurableEquiv.measurableEmbedding

theorem integral_comp [NormedSpace ℝ A] (g : F' → A) : ∫ (x : E'), g (f x) = ∫ (y : F'), g y :=
  f.measurePreserving.integral_comp' (f := f.toMeasurableEquiv) g

end InnerProductSpace

end MeasureTheory
