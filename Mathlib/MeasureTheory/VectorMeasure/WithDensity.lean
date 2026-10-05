/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
public import Mathlib.MeasureTheory.VectorMeasure.Relations

/-!

# Vector measure defined by an integral

Given a measure `μ` and an integrable function `f : α → E`, we can define a vector measure `v` such
that for all measurable sets `s`, `v s = ∫ x in s, f x ∂μ`. This definition is useful for
the Radon-Nikodym theorem for signed measures.

## Main definitions

* `MeasureTheory.Measure.withDensityᵥ`: the vector measure formed by integrating an integrable
  function `f` with respect to a measure `μ` on measurable sets.

-/

@[expose] public section


noncomputable section

open scoped MeasureTheory NNReal ENNReal

variable {α : Type*} {m : SigmaAlgebra α}

namespace MeasureTheory

open TopologicalSpace

variable {μ : Measure α}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open scoped Classical in
/-- Given a measure `μ` and an integrable function `f`, `μ.withDensityᵥ f hf` is the vector measure
which maps a measurable set `s` to `∫ x in s, f x ∂μ`. It is defined when `f` is integrable, which
`hf` states: integrability is exactly the condition for the integral to be defined on every
measurable set, since it is integrability on the whole space. -/
def Measure.withDensityᵥ {m : SigmaAlgebra α} (μ : Measure α) (f : α → E) (hf : Integrable f μ) :
    VectorMeasure α E where
  measureOf' := fun s => if MeasurableSet s then ∫ x in s, f x ∂μ else 0
  empty' := by simp
  not_measurable' := fun _ hs => ite_eq_right hs
  m_iUnion' := fun s hs₁ hs₂ => by
    convert! hasSum_integral_iUnion hs₁ hs₂ hf.integrableOn with n
    · rw [ite_eq_left (hs₁ n)]
    · rw [ite_eq_left (MeasurableSet.iUnion hs₁)]

open Measure

variable {f g : α → E}

theorem withDensityᵥ_apply (hf : Integrable f μ) {s : Set α} (hs : MeasurableSet s) :
    μ.withDensityᵥ f hf s = ∫ x in s, f x ∂μ :=
  ite_eq_left hs

@[simp]
theorem withDensityᵥ_zero : μ.withDensityᵥ (0 : α → E) (integrable_zero α E μ) = 0 := by
  ext1 s hs
  rw [withDensityᵥ_apply (integrable_zero α E μ) hs]
  simp

@[simp]
theorem withDensityᵥ_neg (hf : Integrable f μ) :
    μ.withDensityᵥ (-f) hf.neg = -μ.withDensityᵥ f hf := by
  ext1 i hi
  rw [_root_.neg_apply, withDensityᵥ_apply hf hi, ← integral_neg, withDensityᵥ_apply hf.neg hi]
  simp only [Pi.neg_apply]

theorem withDensityᵥ_neg' (hf : Integrable f μ) :
    (μ.withDensityᵥ (fun x => -f x) hf.neg) = -μ.withDensityᵥ f hf :=
  withDensityᵥ_neg hf

@[simp]
theorem withDensityᵥ_add (hf : Integrable f μ) (hg : Integrable g μ) :
    μ.withDensityᵥ (f + g) (hf.add hg) = μ.withDensityᵥ f hf + μ.withDensityᵥ g hg := by
  ext1 i hi
  rw [withDensityᵥ_apply (hf.add hg) hi, _root_.add_apply, withDensityᵥ_apply hf hi,
    withDensityᵥ_apply hg hi]
  simp_rw [Pi.add_apply]
  rw [integral_add]
  · exact hf.integrableOn
  · exact hg.integrableOn

theorem withDensityᵥ_add' (hf : Integrable f μ) (hg : Integrable g μ) :
    (μ.withDensityᵥ (fun x => f x + g x) (hf.add hg)) =
      μ.withDensityᵥ f hf + μ.withDensityᵥ g hg :=
  withDensityᵥ_add hf hg

@[simp]
theorem withDensityᵥ_sub (hf : Integrable f μ) (hg : Integrable g μ) :
    μ.withDensityᵥ (f - g) (hf.sub hg) = μ.withDensityᵥ f hf - μ.withDensityᵥ g hg := by
  ext1 i hi
  rw [withDensityᵥ_apply (hf.sub hg) hi, _root_.sub_apply, withDensityᵥ_apply hf hi,
    withDensityᵥ_apply hg hi]
  simp_rw [Pi.sub_apply]
  exact integral_sub hf.integrableOn hg.integrableOn

theorem withDensityᵥ_sub' (hf : Integrable f μ) (hg : Integrable g μ) :
    (μ.withDensityᵥ (fun x => f x - g x) (hf.sub hg)) =
      μ.withDensityᵥ f hf - μ.withDensityᵥ g hg :=
  withDensityᵥ_sub hf hg

@[simp]
theorem withDensityᵥ_smul {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]
    [SMulCommClass ℝ 𝕜 E] (hf : Integrable f μ) (r : 𝕜) :
    μ.withDensityᵥ (r • f) (hf.smul r) = r • μ.withDensityᵥ f hf := by
  ext1 i hi
  rw [withDensityᵥ_apply (hf.smul r) hi, _root_.smul_apply, withDensityᵥ_apply hf hi, ←
    integral_smul r f]
  simp only [Pi.smul_apply]

theorem withDensityᵥ_smul' {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]
    [SMulCommClass ℝ 𝕜 E] (hf : Integrable f μ) (r : 𝕜) :
    (μ.withDensityᵥ (fun x => r • f x) (hf.smul r)) = r • μ.withDensityᵥ f hf :=
  withDensityᵥ_smul hf r

theorem withDensityᵥ_smul_eq_withDensityᵥ_withDensity {f : α → ℝ≥0} {g : α → E}
    (hf : AEMeasurable f μ) (hfg : Integrable (f • g) μ) :
    μ.withDensityᵥ (f • g) hfg = (μ.withDensity (fun x ↦ f x)).withDensityᵥ g
      ((integrable_withDensity_iff_integrable_smul₀ hf).mpr hfg) := by
  ext s hs
  rw [withDensityᵥ_apply hfg hs, withDensityᵥ_apply _ hs,
    setIntegral_withDensity_eq_setIntegral_smul₀ hf.restrict _ hs]
  simp only [Pi.smul_apply']

theorem withDensityᵥ_smul_eq_withDensityᵥ_withDensity' {f : α → ℝ≥0∞} {g : α → E}
    (hf : AEMeasurable f μ) (hflt : ∀ᵐ x ∂μ, f x < ∞)
    (hfg : Integrable (fun x ↦ (f x).toReal • g x) μ) :
    μ.withDensityᵥ (fun x ↦ (f x).toReal • g x) hfg = (μ.withDensity f).withDensityᵥ g
      ((integrable_withDensity_iff_integrable_smul₀' hf hflt).mpr hfg) := by
  ext s hs
  rw [withDensityᵥ_apply hfg hs, withDensityᵥ_apply _ hs,
    setIntegral_withDensity_eq_setIntegral_toReal_smul₀ hf.restrict
      (ae_restrict_of_ae hflt) _ hs]

theorem Measure.withDensityᵥ_absolutelyContinuous (μ : Measure α) {f : α → ℝ}
    (hf : Integrable f μ) : μ.withDensityᵥ f hf ≪ᵥ μ.toENNRealVectorMeasure := by
  refine VectorMeasure.AbsolutelyContinuous.mk fun i hi₁ hi₂ => ?_
  rw [toENNRealVectorMeasure_apply_measurable hi₁] at hi₂
  rw [withDensityᵥ_apply hf hi₁, Measure.restrict_zero_set hi₂, integral_zero_measure]

/-- Having the same density implies the underlying functions are equal almost everywhere. -/
theorem Integrable.ae_eq_of_withDensityᵥ_eq [CompleteSpace E] {f g : α → E} (hf : Integrable f μ)
    (hg : Integrable g μ) (hfg : μ.withDensityᵥ f hf = μ.withDensityᵥ g hg) : f =ᵐ[μ] g := by
  refine hf.ae_eq_of_forall_setIntegral_eq f g hg fun i hi _ => ?_
  rw [← withDensityᵥ_apply hf hi, hfg, withDensityᵥ_apply hg hi]

theorem WithDensityᵥEq.congr_ae {f g : α → E} (hf : Integrable f μ) (h : f =ᵐ[μ] g) :
    μ.withDensityᵥ f hf = μ.withDensityᵥ g (hf.congr h) := by
  ext i hi
  rw [withDensityᵥ_apply hf hi, withDensityᵥ_apply (hf.congr h) hi]
  exact integral_congr_ae (ae_restrict_of_ae h)

theorem Integrable.withDensityᵥ_eq_iff [CompleteSpace E]
    {f g : α → E} (hf : Integrable f μ) (hg : Integrable g μ) :
    μ.withDensityᵥ f hf = μ.withDensityᵥ g hg ↔ f =ᵐ[μ] g :=
  ⟨fun hfg => hf.ae_eq_of_withDensityᵥ_eq hg hfg, fun h => WithDensityᵥEq.congr_ae hf h⟩

section SignedMeasure

theorem withDensityᵥ_toReal {f : α → ℝ≥0∞} (hfm : AEMeasurable f μ) (hf : (∫⁻ x, f x ∂μ) ≠ ∞) :
    (μ.withDensityᵥ (fun x => (f x).toReal) (integrable_toReal_of_lintegral_ne_top hfm hf)) =
      @toSignedMeasure α _ (μ.withDensity f) (isFiniteMeasure_withDensity hf) := by
  have hfi := integrable_toReal_of_lintegral_ne_top hfm hf
  have := isFiniteMeasure_withDensity hf
  ext i hi
  rw [withDensityᵥ_apply hfi hi, toSignedMeasure_apply_measurable hi, measureReal_def,
    withDensity_apply _ hi, integral_toReal hfm.restrict]
  refine ae_lt_top' hfm.restrict (ne_top_of_le_ne_top hf ?_)
  conv_rhs => rw [← setLIntegral_univ]
  exact lintegral_mono_set (Set.subset_univ _)

theorem withDensityᵥ_eq_withDensity_pos_part_sub_withDensity_neg_part {f : α → ℝ}
    (hfi : Integrable f μ) :
    μ.withDensityᵥ f hfi =
      @toSignedMeasure α _ (μ.withDensity fun x => ENNReal.ofReal <| f x)
          (isFiniteMeasure_withDensity_ofReal hfi.2) -
        @toSignedMeasure α _ (μ.withDensity fun x => ENNReal.ofReal <| -f x)
          (isFiniteMeasure_withDensity_ofReal hfi.neg.2) := by
  have := isFiniteMeasure_withDensity_ofReal hfi.2
  have := isFiniteMeasure_withDensity_ofReal hfi.neg.2
  ext i hi
  rw [withDensityᵥ_apply hfi hi,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hfi.integrableOn,
    _root_.sub_apply, toSignedMeasure_apply_measurable hi,
    toSignedMeasure_apply_measurable hi, measureReal_def, measureReal_def,
    withDensity_apply _ hi, withDensity_apply _ hi]

theorem Integrable.withDensityᵥ_trim_eq_integral {𝓐 𝓑 : SigmaAlgebra α} {μ : Measure α}
    (h𝓐𝓑 : 𝓐 ≤ 𝓑) {f : α → ℝ} (hf : Integrable f μ) {i : Set α} (hi : i ∈ 𝓐) :
    (μ.withDensityᵥ f hf).trim h𝓐𝓑 i = ∫ x in i, f x ∂μ := by
  rw [VectorMeasure.trim_measurableSet_eq h𝓐𝓑 hi, withDensityᵥ_apply hf (h𝓐𝓑 hi)]

theorem Integrable.withDensityᵥ_trim_absolutelyContinuous {𝓐 𝓑 : SigmaAlgebra α} {μ : Measure α}
    (h𝓐𝓑 : 𝓐 ≤ 𝓑) (hfi : Integrable f μ) :
    (μ.withDensityᵥ f hfi).trim h𝓐𝓑 ≪ᵥ (μ.trim h𝓐𝓑).toENNRealVectorMeasure := by
  refine VectorMeasure.AbsolutelyContinuous.mk fun j hj₁ hj₂ => ?_
  rw [Measure.toENNRealVectorMeasure_apply_measurable hj₁,
    trim_measurableSet_eq h𝓐𝓑 hj₁] at hj₂
  rw [VectorMeasure.trim_measurableSet_eq h𝓐𝓑 hj₁, withDensityᵥ_apply hfi (h𝓐𝓑 hj₁)]
  simp only [Measure.restrict_eq_zero.mpr hj₂, integral_zero_measure]

end SignedMeasure

end MeasureTheory
