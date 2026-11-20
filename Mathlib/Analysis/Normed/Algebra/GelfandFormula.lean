/-
Copyright (c) 2021 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Analytic.RadiusLiminf

/-!
# Gelfand's formula and other results on the spectrum in complex Banach algebras

This file contains results on the spectrum of elements in a complex Banach algebra, including
**Gelfand's formula** and the **Gelfand-Mazur theorem** and the fact that every element in a
complex Banach algebra has nonempty spectrum.

## Main results

* `spectrum.hasDerivAt_resolvent_const_left`: the resolvent function is differentiable on the
  resolvent set.
* `spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius`: Gelfand's formula for the
  spectral radius in Banach algebras over `ℂ`.
* `spectrum.nonempty`: the spectrum of any element in a complex Banach algebra is nonempty.
* `NormedRing.algEquivComplexOfComplete`: **Gelfand-Mazur theorem** For a complex
  Banach division algebra, the natural `algebraMap ℂ A` is an algebra isomorphism whose inverse
  is given by selecting the (unique) element of `spectrum ℂ a`

## Implementation notes

Note that it is important here that the complex analysis files are privately imported, since the
material proven here gets used in contexts that have nothing to do with complex analysis
(i.e. C⋆-algebras, etc).

-/

@[expose] public section

variable {𝕜 A : Type*}

open scoped NNReal Topology Ring
open Filter ENNReal Topology Bornology

namespace spectrum

section NonTriviallyNormedField

variable [NontriviallyNormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A]

theorem hasDerivAt_resolvent_const_left {a : A} (k : resolventSet 𝕜 a) :
    HasDerivAt (resolvent a) (-resolvent a k ^ 2) k Subtype.val := by
  have H₂ : HasDerivAt (fun k => algebraMap 𝕜 A k - a) 1 k.val := by
    simpa using (Algebra.linearMap 𝕜 A).hasDerivAt.sub_const a
  simpa [resolventSet, resolvent, sq] using! (H₂.hasFDerivAt.inv k.property).hasDerivAt

@[deprecated (since := "2026-03-26")]
alias hasDerivAt_resolvent := hasDerivAt_resolvent_const_left

theorem hasFDerivAt_resolvent {a : A} {k : 𝕜} (hk : k ∈ resolventSet 𝕜 a) :
    HasFDerivAt
      (fun b : {b : A | k ∈ resolventSet 𝕜 b} ↦ resolvent b.val ⟨k, b.property⟩)
      (((ContinuousLinearMap.mulLeftRight 𝕜 A) (resolvent a ⟨k, hk⟩)) (resolvent a ⟨k, hk⟩))
      ⟨a, hk⟩ Subtype.val := by
  have H₂ : HasFDerivAt (fun a => algebraMap 𝕜 A k - a) (- .id 𝕜 A) a := by
    simpa only [Pi.sub_def, id_eq, zero_sub] using! (hasFDerivAt_const _ a).sub (hasFDerivAt_id a)
  simpa [resolventSet, resolvent] using! H₂.inv hk

end NonTriviallyNormedField

theorem hasDerivAt_resolvent_const_right [NontriviallyNormedField 𝕜] [NontriviallyNormedField A]
    [NormedAlgebra 𝕜 A] {a : A} {k : 𝕜} (hk : k ∈ resolventSet 𝕜 a) :
    HasDerivAt
      (fun b : {b : A | k ∈ resolventSet 𝕜 b} ↦ resolvent b.val ⟨k, b.property⟩)
      (resolvent a ⟨k, hk⟩ ^ 2) ⟨a, hk⟩ Subtype.val := by
  have hd : HasDerivAt (fun b : A ↦ algebraMap 𝕜 A k - b) (-1) a := by
    simpa only [zero_sub, id_eq] using! (hasDerivAt_id a).const_sub (algebraMap 𝕜 A k)
  simpa [resolventSet, resolvent, pow_two] using! (hd.hasFDerivAt.inv hk).hasDerivAt

private theorem isUnit_one_sub_smul_of_mem_closedBall [NontriviallyNormedField 𝕜] [NormedRing A]
    [NormedAlgebra 𝕜 A] {a : A} {r : ℝ≥0} {z : 𝕜}
    (hr : (r : ℝ≥0∞) < (spectralRadius 𝕜 a)⁻¹) (hz : z ∈ Metric.closedBall 0 r) :
    IsUnit (1 - z • a) := by
  refine isUnit_one_sub_smul_of_lt_inv_radius (lt_of_le_of_lt (coe_mono ?_) hr)
  exact_mod_cast mem_closedBall_zero_iff.mp hz

open ENNReal in
/-- In a Banach algebra `A` over `𝕜`, for `a : A` the function `fun z ↦ (1 - z • a)⁻¹` is
differentiable on any closed ball centered at zero of radius `r < (spectralRadius 𝕜 a)⁻¹`. -/
theorem differentiableOn_inverse_one_sub_smul [NontriviallyNormedField 𝕜] [NormedRing A]
    [NormedAlgebra 𝕜 A] [CompleteSpace A] {a : A} {r : ℝ≥0}
    (hr : (r : ℝ≥0∞) < (spectralRadius 𝕜 a)⁻¹) :
    DifferentiableOn 𝕜
      (fun z : {z : 𝕜 | IsUnit (1 - z • a)} ↦ (↑z.property.unit⁻¹ : A))
      (Subtype.val ⁻¹' Metric.closedBall 0 r) Subtype.val := by
  have hd : Differentiable 𝕜 fun w : 𝕜 ↦ 1 - w • a := (differentiable_id.smul_const a).const_sub 1
  exact fun _ hz ↦ hd.differentiableAt.differentiableWithinAt.inv
    (isUnit_one_sub_smul_of_mem_closedBall hr hz)

section Complex

variable [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

open ContinuousMultilinearMap in
/-- The `limsup` relationship for the spectral radius used to prove `spectrum.gelfand_formula`. -/
theorem limsup_pow_nnnorm_pow_one_div_le_spectralRadius (a : A) :
    limsup (fun n : {n : ℕ // n ≠ 0} ↦
      (‖a ^ (n : ℕ)‖₊ : ℝ≥0∞) ^ (1 / (n : ℕ) : ℝ))
      (comap Subtype.val atTop) ≤ spectralRadius ℂ a := by
  refine ENNReal.inv_le_inv.mp (le_of_forall_pos_nnreal_lt fun r r_pos r_lt => ?_)
  simp_rw [inv_limsup]
  let p : FormalMultilinearSeries ℂ ℂ A := fun n =>
    ContinuousMultilinearMap.mkPiRing ℂ (Fin n) (a ^ n)
  suffices h : (r : ℝ≥0∞) ≤ p.radius by
    simpa only [p.radius_eq_liminf, p, ← norm_toNNReal, norm_mkPiRing] using h
  let c : {z : ℂ | IsUnit (1 - z • a)} := ⟨0, by simp⟩
  have hD : Metric.closedBall (0 : ℂ) r ⊆ {z | IsUnit (1 - z • a)} :=
    fun _ hz ↦ isUnit_one_sub_smul_of_mem_closedBall r_lt hz
  obtain ⟨q, hq⟩ := (differentiableOn_inverse_one_sub_smul r_lt).exists_hasFPowerSeriesOnBall
    (c := c) r_pos IsEmbedding.subtypeVal (fun z hz ↦ ⟨⟨z, hD hz⟩, rfl⟩)
  apply ((hasFPowerSeriesOnBall_inverse_one_sub_smul ℂ a).exchange_radius hq ?_).r_le
  filter_upwards [Metric.closedBall_mem_nhds (0 : ℂ) (show 0 < (r : ℝ) from r_pos)] with z hz
  exact ⟨⟨z, hD hz⟩, rfl⟩

/-- **Gelfand's formula**: Given an element `a : A` of a complex Banach algebra, the
`spectralRadius` of `a` is the limit of the sequence `‖a ^ n‖₊ ^ (1 / n)`. -/
theorem pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius (a : A) :
    Tendsto (fun n : {n : ℕ // n ≠ 0} ↦
      (‖a ^ (n : ℕ)‖₊ : ℝ≥0∞) ^ (1 / (n : ℕ) : ℝ))
      (comap Subtype.val atTop) (𝓝 (spectralRadius ℂ a)) :=
  tendsto_of_le_liminf_of_limsup_le (spectralRadius_le_liminf_pow_nnnorm_pow_one_div ℂ a)
    (limsup_pow_nnnorm_pow_one_div_le_spectralRadius a)

alias gelfand_formula := pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius

/- This is the same as `pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius` but for `norm`
instead of `nnnorm`. -/
/-- **Gelfand's formula**: Given an element `a : A` of a complex Banach algebra, the
`spectralRadius` of `a` is the limit of the sequence `‖a ^ n‖₊ ^ (1 / n)`. -/
theorem pow_norm_pow_one_div_tendsto_nhds_spectralRadius (a : A) :
    Tendsto (fun n : {n : ℕ // n ≠ 0} ↦ ENNReal.ofReal (‖a ^ (n : ℕ)‖ ^ (1 / (n : ℕ) : ℝ)))
      (comap Subtype.val atTop)
      (𝓝 (spectralRadius ℂ a)) := by
  convert! pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius a using 1
  ext1
  rw [← ofReal_rpow_of_nonneg (norm_nonneg _) _, ← coe_nnnorm, coe_nnreal_eq]
  simp

section Nontrivial

variable [Nontrivial A]

/-- In a (nontrivial) complex Banach algebra, every element has nonempty spectrum. -/
protected theorem nonempty (a : A) : (spectrum ℂ a).Nonempty := by
  /- Suppose `σ a = ∅`, then resolvent set is `ℂ`, any `(z • 1 - a)` is a unit, and `resolvent a`
    is differentiable on `ℂ`. -/
  by_contra! h
  have H₀ : resolventSet ℂ a = Set.univ := by rwa [spectrum, Set.compl_empty_iff] at h
  let lift : ℂ → resolventSet ℂ a := fun z ↦ ⟨z, H₀.symm ▸ Set.mem_univ z⟩
  have H₁ : Differentiable ℂ (resolvent a ∘ lift) := by
    intro z
    exact ((hasDerivAt_resolvent_const_left (lift z)).hasFDerivAt.comp z
      (hasFDerivAt_id z) continuousAt_id IsEmbedding.subtypeVal).differentiableAt
  /- The lift exists on all scalars only under the empty-spectrum assumption. Liouville's
    theorem therefore applies to an everywhere-defined, genuinely invertible resolvent. -/
  have H₂ : Tendsto lift (cobounded ℂ)
      (comap (Subtype.val : resolventSet ℂ a → ℂ) (cobounded ℂ)) :=
    tendsto_comap_iff.mpr tendsto_id
  have H₃ := H₁.apply_eq_of_tendsto_cocompact 0 <| by
    simpa [Metric.cobounded_eq_cocompact] using
      (resolvent_tendsto_cobounded a (𝕜 := ℂ)).comp H₂
  exact (isUnit_resolvent (lift 0)).ne_zero H₃

/-- In a complex Banach algebra, the spectral radius is always attained by some element of the
spectrum. -/
theorem exists_nnnorm_eq_spectralRadius (a : A) :
    ∃ z ∈ spectrum ℂ a, (‖z‖₊ : ℝ≥0∞) = spectralRadius ℂ a :=
  exists_nnnorm_eq_spectralRadius_of_nonempty (spectrum.nonempty a)

/-- In a complex Banach algebra, if every element of the spectrum has norm strictly less than
`r : ℝ≥0`, then the spectral radius is also strictly less than `r`. -/
theorem spectralRadius_lt_of_forall_lt (a : A) {r : ℝ≥0}
    (hr : ∀ z ∈ spectrum ℂ a, ‖z‖₊ < r) : spectralRadius ℂ a < r :=
  spectralRadius_lt_of_forall_lt_of_nonempty (spectrum.nonempty a) hr


open Polynomial in
/-- The **spectral mapping theorem** for polynomials in a Banach algebra over `ℂ`. -/
theorem map_polynomial_aeval (a : A) (p : ℂ[X]) :
    spectrum ℂ (aeval a p) = (fun k => eval k p) '' spectrum ℂ a :=
  map_polynomial_aeval_of_nonempty a p (spectrum.nonempty a)

open Polynomial in
/-- A specialization of the spectral mapping theorem for polynomials in a Banach algebra over `ℂ`
to monic monomials. -/
protected theorem map_pow (a : A) (n : ℕ) :
    spectrum ℂ (a ^ n) = (· ^ n) '' spectrum ℂ a := by
  simpa only [aeval_X_pow, eval_X_pow] using map_polynomial_aeval a (X ^ n)

end Nontrivial

omit [CompleteSpace A] in
theorem algebraMap_eq_of_mem (hA : ∀ {a : A}, IsUnit a ↔ a ≠ 0) {a : A} {z : ℂ}
    (h : z ∈ spectrum ℂ a) : algebraMap ℂ A z = a := by
  rwa [mem_iff, hA, Classical.not_not, sub_eq_zero] at h

/-- **Gelfand-Mazur theorem**: For a complex Banach division algebra, the natural `algebraMap ℂ A`
is an algebra isomorphism whose inverse is given by selecting the (unique) element of
`spectrum ℂ a`. In addition, `algebraMap_isometry` guarantees this map is an isometry.

Note: because `NormedDivisionRing` requires the field `norm_mul : ∀ a b, ‖a * b‖ = ‖a‖ * ‖b‖`, we
don't use this type class and instead opt for a `NormedRing` in which the nonzero elements are
precisely the units. This allows for the application of this isomorphism in broader contexts, e.g.,
to the quotient of a complex Banach algebra by a maximal ideal. In the case when `A` is actually a
`NormedDivisionRing`, one may fill in the argument `hA` with the lemma `isUnit_iff_ne_zero`. -/
@[simps]
noncomputable def _root_.NormedRing.algEquivComplexOfComplete (hA : ∀ {a : A}, IsUnit a ↔ a ≠ 0) :
    ℂ ≃ₐ[ℂ] A :=
  let nt : Nontrivial A := ⟨⟨1, 0, hA.mp ⟨⟨1, 1, mul_one _, mul_one _⟩, rfl⟩⟩⟩
  { Algebra.ofId ℂ A with
    toFun := algebraMap ℂ A
    invFun := fun a => (@spectrum.nonempty _ _ _ _ nt a).some
    left_inv := fun z => by
      simpa only [@scalar_eq _ _ _ _ _ nt _] using!
        (@spectrum.nonempty _ _ _ _ nt <| algebraMap ℂ A z).some_mem
    right_inv := fun a => algebraMap_eq_of_mem (@hA) (@spectrum.nonempty _ _ _ _ nt a).some_mem }

end Complex

end spectrum
