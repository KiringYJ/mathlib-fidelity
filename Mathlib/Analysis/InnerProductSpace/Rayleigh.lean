/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Frédéric Dupuis
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.Analysis.Calculus.LagrangeMultipliers
public import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# The Rayleigh quotient

The Rayleigh quotient of a self-adjoint operator `T` on an inner product space `E` is
`re ⟪T x, x⟫ / ‖x‖ ^ 2` for nonzero vectors `x`.

The main results of this file are `IsSelfAdjoint.hasEigenvector_of_isMaxOn` and
`IsSelfAdjoint.hasEigenvector_of_isMinOn`, which state that if `E` is complete, and if the
Rayleigh quotient attains its global maximum/minimum over some sphere at the point `x₀`, then `x₀`
is an eigenvector of `T`, and the `iSup`/`iInf` of `fun x ↦ ⟪T x, x⟫ / ‖x‖ ^ 2` is the corresponding
eigenvalue.

The corollaries `LinearMap.IsSymmetric.hasEigenvalue_iSup_of_finiteDimensional` and
`LinearMap.IsSymmetric.hasEigenvalue_iSup_of_finiteDimensional` state that if `E` is
finite-dimensional and nontrivial, then `T` has some (nonzero) eigenvectors with eigenvalue the
`iSup`/`iInf` of `fun x ↦ ⟪T x, x⟫ / ‖x‖ ^ 2`.

## TODO

A slightly more elaborate corollary is that if `E` is complete and `T` is a compact operator, then
`T` has some (nonzero) eigenvector with eigenvalue either `⨆ x, ⟪T x, x⟫ / ‖x‖ ^ 2` or
`⨅ x, ⟪T x, x⟫ / ‖x‖ ^ 2` (not necessarily both).

-/

public section

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

open scoped NNReal

open Module.End Metric RCLike InnerProductSpace

namespace ContinuousLinearMap

variable (T : E →L[𝕜] E)

/-- The *Rayleigh quotient* of a continuous linear map `T` (over `ℝ` or `ℂ`) at a nonzero vector
`x` is the quantity `re ⟪T x, x⟫ / ‖x‖ ^ 2`. -/
noncomputable abbrev rayleighQuotient (x : {x : E // x ≠ 0}) : ℝ :=
  Checked.div (T.reApplyInnerSelf x) (‖(x : E)‖ ^ 2)
    ((norm_ne_zero_iff.mpr x.property).isUnit.pow 2)

theorem rayleigh_smul (x : {x : E // x ≠ 0}) {c : 𝕜} (hc : c ≠ 0) :
    T.rayleighQuotient ⟨c • (x : E), smul_ne_zero hc x.property⟩ = T.rayleighQuotient x := by
  have hx := x.property
  simp only [rayleighQuotient, norm_smul, mul_pow, T.reApplyInnerSelf_smul, mul_div_mul_left]

theorem rayleighQuotient_add (S : E →L[𝕜] E) {x : {x : E // x ≠ 0}} :
    (T + S).rayleighQuotient x = T.rayleighQuotient x + S.rayleighQuotient x := by
  simp [rayleighQuotient, reApplyInnerSelf_apply, inner_add_left, add_div]

@[simp]
theorem rayleighQuotient_zero_apply (x : {x : E // x ≠ 0}) :
    rayleighQuotient (0 : E →L[𝕜] E) x = 0 := by
  simp [reApplyInnerSelf_apply]

@[simp]
theorem rayleighQuotient_neg_apply (x : {x : E // x ≠ 0}) :
    rayleighQuotient (-T) x = -rayleighQuotient T x := by
  simp [rayleighQuotient, reApplyInnerSelf_apply, neg_div₀]

@[simp]
theorem rayleighQuotient_apply_neg (x : {x : E // x ≠ 0}) :
    T.rayleighQuotient ⟨-(x : E), neg_ne_zero.mpr x.property⟩ = T.rayleighQuotient x := by
  simp [rayleighQuotient, reApplyInnerSelf_apply]

theorem range_rayleigh_eq_image_rayleigh_sphere {r : ℝ} (hr : 0 < r) :
    Set.range T.rayleighQuotient = T.rayleighQuotient '' (Subtype.val ⁻¹' sphere 0 r) := by
  ext a
  constructor
  · rintro ⟨x, hxT⟩
    have hx := x.property
    let c : 𝕜 := ((r / ‖(x : E)‖ : ℝ) : 𝕜)
    have hpos : 0 < r / ‖(x : E)‖ := div_pos hr (norm_pos_iff.mpr hx)
    have hc : c ≠ 0 := by simpa [c] using hpos.ne'
    refine ⟨⟨c • (x : E), smul_ne_zero hc hx⟩, ?_, (T.rayleigh_smul x hc).trans hxT⟩
    change c • (x : E) ∈ sphere 0 r
    rw [mem_sphere_zero_iff_norm, norm_smul, RCLike.norm_ofReal, abs_of_pos hpos, div_mul_cancel₀]
  · rintro ⟨x, hx, hxT⟩
    exact ⟨x, hxT⟩

theorem iSup_rayleigh_eq_iSup_rayleigh_sphere {r : ℝ} (hr : 0 < r) :
    ⨆ x : { x : E // x ≠ 0 }, rayleighQuotient T x =
      ⨆ x : ((Subtype.val : {x : E // x ≠ 0} → E) ⁻¹' sphere 0 r), T.rayleighQuotient x.val := by
  rw [← sSup_range, T.range_rayleigh_eq_image_rayleigh_sphere hr, sSup_image']

theorem iInf_rayleigh_eq_iInf_rayleigh_sphere {r : ℝ} (hr : 0 < r) :
    ⨅ x : { x : E // x ≠ 0 }, rayleighQuotient T x =
      ⨅ x : ((Subtype.val : {x : E // x ≠ 0} → E) ⁻¹' sphere 0 r), T.rayleighQuotient x.val := by
  rw [← sInf_range, T.range_rayleigh_eq_image_rayleigh_sphere hr, sInf_image']

theorem rayleighQuotient_le_norm (x : {x : E // x ≠ 0}) : |T.rayleighQuotient x| ≤ ‖T‖ := by
  have hpos : 0 < ‖(x : E)‖ ^ 2 := pow_pos (norm_pos_iff.mpr x.property) 2
  simp only [rayleighQuotient, reApplyInnerSelf_apply, abs_div, abs_of_pos hpos]
  rw [div_le_iff₀ hpos]
  calc
    |re ⟪T x, x⟫| ≤ ‖⟪T x, x⟫‖ := abs_re_le_norm _
    _ ≤ ‖T x‖ * ‖(x : E)‖ := norm_inner_le_norm _ _
    _ ≤ (‖T‖ * ‖(x : E)‖) * ‖(x : E)‖ :=
      mul_le_mul_of_nonneg_right (T.le_opNorm x) (norm_nonneg _)
    _ = ‖T‖ * ‖(x : E)‖ ^ 2 := by ring

theorem bddAbove_rayleighQuotient : BddAbove (Set.range fun x ↦ |T.rayleighQuotient x|) :=
  ⟨‖T‖, fun _ ⟨y, h⟩ ↦ h ▸ T.rayleighQuotient_le_norm y⟩

theorem norm_eq_iSup_rayleighQuotient (hT : T.IsSymmetric) :
    ‖T‖ = ⨆ x, |T.rayleighQuotient x| := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · have : IsEmpty {x : E // x ≠ 0} := ⟨fun x ↦ x.property (Subsingleton.elim _ _)⟩
    simp [show T = 0 from Subsingleton.elim _ _]
  obtain ⟨x₀, hx₀⟩ := exists_ne (0 : E)
  have : Nonempty {x : E // x ≠ 0} := ⟨⟨x₀, hx₀⟩⟩
  set M := ⨆ x, |T.rayleighQuotient x|
  have nonneg : 0 ≤ M := le_ciSup_of_le T.bddAbove_rayleighQuotient ⟨x₀, hx₀⟩ (abs_nonneg _)
  have hM x : |re ⟪T x, x⟫| ≤ M * ‖x‖ ^ 2 := by
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    have hpos : 0 < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hx) 2
    have hMx : |T.rayleighQuotient ⟨x, hx⟩| ≤ M := le_ciSup T.bddAbove_rayleighQuotient ⟨x, hx⟩
    simp only [rayleighQuotient, reApplyInnerSelf_apply, abs_div, abs_of_pos hpos] at hMx
    exact (div_le_iff₀ hpos).1 hMx
  refine le_antisymm ?_ (ciSup_le T.rayleighQuotient_le_norm)
  refine opNorm_le_of_re_inner_le nonneg fun x y hx hy ↦ ?_
  transitivity M * (‖x + y‖ ^ 2 + ‖x - y‖ ^ 2) / 4
  · have hsym : re ⟪T y, x⟫ = re ⟪T x, y⟫ :=
      (inner_re_symm (T y) x).trans (congrArg re (hT x y)).symm
    have hpolar : 4 * re ⟪T x, y⟫ =
        re ⟪T (x + y), x + y⟫ - re ⟪T (x - y), x - y⟫ := by
      simp only [map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left,
        inner_sub_right, hsym]
      ring
    have hplus := (le_abs_self (re ⟪T (x + y), x + y⟫)).trans (hM (x + y))
    have hminus := (neg_le_abs (re ⟪T (x - y), x - y⟫)).trans (hM (x - y))
    rw [le_div_iff₀ (by norm_num : 0 < (4 : ℝ))]
    nlinarith only [hpolar, hplus, hminus]
  · apply le_of_eq
    rw [parallelogram_law_with_norm 𝕜 x y, hx, hy]
    field_simp
    ring

private theorem rayleighQuotient_le_of_mem_resolventSet
    (t : ℝ) (ht : 0 < t) (hT' : (algebraMap ℝ 𝕜) t ∈ resolventSet 𝕜 T) :
    ∃ c > 0, ∀ x, T.rayleighQuotient x ≤ (t ^ 2 + ‖T‖ ^ 2) / (2 * t) - c := by
  by_cases hT0 : T = 0
  · exact ⟨t ^ 2 / (2 * t), by positivity, by simp [hT0]⟩
  obtain ⟨c, hc0, hc⟩ := antilipschitzWith_iff_exists_mul_le_norm.mp
    (antilipschitz_of_isEmbedding _ (isHomeomorph_of_isUnit hT').isEmbedding)
  refine ⟨c ^ 2 / (2 * t), by positivity, fun x ↦ ?_⟩
  have hx := x.property
  rw [rayleighQuotient, reApplyInnerSelf_apply]
  specialize hc x.val
  rw [← sq_le_sq₀ (by positivity) (by positivity), sub_apply, algebraMap_apply,
    norm_sub_sq (𝕜 := 𝕜), inner_re_symm] at hc
  grw [le_opNorm] at hc
  simp only [ne_eq, norm_smul, norm_algebraMap', Real.norm_eq_abs, abs_of_pos ht,
    inner_smul_right, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero] at hc
  have hpos : 0 < 2 * t := mul_pos zero_lt_two ht
  have hnorm : 0 < ‖(x : E)‖ ^ 2 := pow_pos (norm_pos_iff.mpr hx) 2
  rw [div_le_iff₀ hnorm, ← sub_div, div_mul_eq_mul_div₀, le_div_iff₀ hpos]
  nlinarith only [hc]

/-- If `‖T‖` is not in the spectrum, then `T.rayleighQuotient x` don't reach `‖T‖`. -/
theorem rayleighQuotient_le_of_norm_mem_resolventSet [Nontrivial E]
    (hT' : algebraMap ℝ 𝕜 ‖T‖ ∈ resolventSet 𝕜 T) :
    ∃ ε > 0, ∀ x, T.rayleighQuotient x ≤ ‖T‖ - ε := by
  by_cases hT0 : T = 0
  · simp [hT0, spectrum.mem_resolventSet_iff] at hT'
  obtain ⟨ε, hε0, hε⟩ := T.rayleighQuotient_le_of_mem_resolventSet ‖T‖ (by positivity) hT'
  refine ⟨ε, hε0, fun x ↦ ?_⟩
  grw [hε]
  field_simp
  grind

/-- If `±‖T‖` are not in the spectrum, then `|T.rayleighQuotient x|` doesn't reach `‖T‖`. -/
theorem abs_rayleighQuotient_le_of_norm_mem_resolventSet [Nontrivial E]
    (hT' : algebraMap ℝ 𝕜 ‖T‖ ∈ resolventSet 𝕜 T) (hT'' : -algebraMap ℝ 𝕜 ‖T‖ ∈ resolventSet 𝕜 T) :
    ∃ ε > 0, ∀ x, |T.rayleighQuotient x| ≤ ‖T‖ - ε := by
  obtain ⟨ε, hε0, hε⟩ := T.rayleighQuotient_le_of_norm_mem_resolventSet hT'
  obtain ⟨ε', hε'0, hε'⟩ := (-T).rayleighQuotient_le_of_norm_mem_resolventSet <| by
    simpa [resolventSet_neg]
  exact ⟨min ε ε', by grind, fun x ↦ by grind [rayleighQuotient_neg_apply, norm_neg]⟩

-- TODO: Prove this from `IsSelfAdjoint.toReal_spectralRadius_eq_norm` using complexification.
/-- The spectral radius of a self-adjoint operator on a complete space equals the norm. -/
theorem spectralRadius_eq_nnnorm [CompleteSpace E] (hT : IsSelfAdjoint T) :
    spectralRadius 𝕜 T = ‖T‖₊ := by
  nontriviality E
  apply le_antisymm (spectralRadius_le_nnnorm T)
  suffices h : algebraMap ℝ 𝕜 ‖T‖ ∈ spectrum 𝕜 T ∨ algebraMap ℝ 𝕜 (-‖T‖) ∈ spectrum 𝕜 T by
    rcases h with h | h <;>
      exact le_trans (by simp) (le_biSup _ (spectrum_subset_quasispectrum 𝕜 T h))
  simp_rw [spectrum, Set.mem_compl_iff, map_neg]
  by_contra! h
  obtain ⟨c, hc0, hc⟩ := T.abs_rayleighQuotient_le_of_norm_mem_resolventSet h.1 h.2
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  have : Nonempty {x : E // x ≠ 0} := ⟨⟨x, hx⟩⟩
  have hbound : (⨆ x, |T.rayleighQuotient x|) ≤ ‖T‖ - c := ciSup_le hc
  rw [← norm_eq_iSup_rayleighQuotient T hT.isSymmetric] at hbound
  linarith only [hc0, hbound]

end ContinuousLinearMap

namespace IsSelfAdjoint

section Real

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem _root_.LinearMap.IsSymmetric.hasStrictFDerivAt_reApplyInnerSelf {T : F →L[ℝ] F}
    (hT : (T : F →ₗ[ℝ] F).IsSymmetric) (x₀ : F) :
    HasStrictFDerivAt T.reApplyInnerSelf (2 • (innerSL ℝ (T x₀))) x₀ := by
  convert! T.hasStrictFDerivAt.inner ℝ (hasStrictFDerivAt_id x₀) using 1
  ext y
  rw [smul_apply, ContinuousLinearMap.comp_apply, fderivInnerCLM_apply,
    ContinuousLinearMap.prod_apply, innerSL_apply_apply, id, ContinuousLinearMap.id_apply,
    hT.apply_clm x₀ y, real_inner_comm _ x₀, two_smul]

variable [CompleteSpace F] {T : F →L[ℝ] F}

theorem linearly_dependent_of_isLocalExtrOn (hT : IsSelfAdjoint T) {x₀ : F}
    (hextr : IsLocalExtrOn T.reApplyInnerSelf (sphere (0 : F) ‖x₀‖) x₀) :
    ∃ a b : ℝ, (a, b) ≠ 0 ∧ a • x₀ + b • T x₀ = 0 := by
  have H : IsLocalExtrOn T.reApplyInnerSelf {x : F | ‖x‖ ^ 2 = ‖x₀‖ ^ 2} x₀ := by
    convert! hextr
    ext x
    simp
  -- find Lagrange multipliers for the function `T.re_apply_inner_self` and the
  -- hypersurface-defining function `fun x ↦ ‖x‖ ^ 2`
  obtain ⟨a, b, h₁, h₂⟩ :=
    IsLocalExtrOn.exists_multipliers_of_hasStrictFDerivAt_1d H (hasStrictFDerivAt_norm_sq x₀)
      (hT.isSymmetric.hasStrictFDerivAt_reApplyInnerSelf x₀)
  refine ⟨a, b, h₁, ?_⟩
  apply (InnerProductSpace.toDualMap ℝ F).injective
  simp only [LinearIsometry.map_add, LinearIsometry.map_zero]
  -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 changed `map_smulₛₗ` into `map_smulₛₗ _`
  simp only [map_smulₛₗ _, RCLike.conj_to_real]
  change a • innerSL ℝ x₀ + b • innerSL ℝ (T x₀) = 0
  apply smul_right_injective (F →L[ℝ] ℝ) (two_ne_zero : (2 : ℝ) ≠ 0)
  simpa only [two_smul, smul_add, add_smul, add_zero] using h₂

open scoped InnerProductSpace in
theorem eq_smul_self_of_isLocalExtrOn_real (hT : IsSelfAdjoint T) {x₀ : F} (hx₀ : x₀ ≠ 0)
    (hextr : IsLocalExtrOn T.reApplyInnerSelf (sphere (0 : F) ‖x₀‖) x₀) :
    T x₀ = T.rayleighQuotient ⟨x₀, hx₀⟩ • x₀ := by
  obtain ⟨a, b, h₁, h₂⟩ := hT.linearly_dependent_of_isLocalExtrOn hextr
  by_cases hb : b = 0
  · have : a ≠ 0 := by simpa [hb] using! h₁
    refine absurd ?_ hx₀
    apply smul_right_injective F this
    simpa [hb] using! h₂
  have hc : T x₀ = (-b⁻¹ * a) • x₀ := by
    linear_combination (norm := match_scalars <;> field) b⁻¹ • h₂
  set c : ℝ := -b⁻¹ * a
  have hinner : ⟪T x₀, x₀⟫_ℝ = c * ‖x₀‖ ^ 2 := by
    rw [hc, real_inner_smul_left, real_inner_self_eq_norm_sq]
  have hq : T.rayleighQuotient ⟨x₀, hx₀⟩ = c := by
    rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply,
      RCLike.re_to_real, hinner, mul_div_cancel_right₀]
  rw [hq]
  exact hc

end Real

section CompleteSpace

variable [CompleteSpace E] {T : E →L[𝕜] E}

theorem eq_smul_self_of_isLocalExtrOn (hT : IsSelfAdjoint T) {x₀ : E} (hx₀ : x₀ ≠ 0)
    (hextr : IsLocalExtrOn T.reApplyInnerSelf (sphere (0 : E) ‖x₀‖) x₀) :
    T x₀ = (T.rayleighQuotient ⟨x₀, hx₀⟩ : 𝕜) • x₀ := by
  let := InnerProductSpace.rclikeToReal 𝕜 E
  let hSA := hT.isSymmetric.restrictScalars.toSelfAdjoint.prop
  exact hSA.eq_smul_self_of_isLocalExtrOn_real hx₀ hextr

/-- For a self-adjoint operator `T`, a local extremum of the Rayleigh quotient of `T` on a sphere
centred at the origin is an eigenvector of `T`. -/
theorem hasEigenvector_of_isLocalExtrOn (hT : IsSelfAdjoint T) {x₀ : E} (hx₀ : x₀ ≠ 0)
    (hextr : IsLocalExtrOn T.reApplyInnerSelf (sphere (0 : E) ‖x₀‖) x₀) :
    HasEigenvector (T : E →ₗ[𝕜] E) (T.rayleighQuotient ⟨x₀, hx₀⟩) x₀ := by
  refine ⟨?_, hx₀⟩
  rw [Module.End.mem_eigenspace_iff]
  exact hT.eq_smul_self_of_isLocalExtrOn hx₀ hextr

/-- For a self-adjoint operator `T`, a maximum of the Rayleigh quotient of `T` on a sphere centred
at the origin is an eigenvector of `T`, with eigenvalue the global supremum of the Rayleigh
quotient. -/
theorem hasEigenvector_of_isMaxOn (hT : IsSelfAdjoint T) {x₀ : E} (hx₀ : x₀ ≠ 0)
    (hextr : IsMaxOn T.reApplyInnerSelf (sphere (0 : E) ‖x₀‖) x₀) :
    HasEigenvector (T : E →ₗ[𝕜] E) (⨆ x : { x : E // x ≠ 0 }, T.rayleighQuotient x : ℝ) x₀ := by
  convert! hT.hasEigenvector_of_isLocalExtrOn hx₀ (Or.inr hextr.isLocalMaxOn)
  have hx₀' : 0 < ‖x₀‖ := norm_pos_iff.mpr hx₀
  have hx₀'' : (⟨x₀, hx₀⟩ : {x : E // x ≠ 0}) ∈ Subtype.val ⁻¹' sphere (0 : E) ‖x₀‖ := by simp
  rw [T.iSup_rayleigh_eq_iSup_rayleigh_sphere hx₀']
  refine IsMaxOn.iSup_eq hx₀'' ?_
  intro x hx
  have hnorm : ‖(x : E)‖ = ‖x₀‖ := mem_sphere_zero_iff_norm.mp hx
  have hu : IsUnit (‖x₀‖ ^ 2) := (norm_ne_zero_iff.mpr hx₀).isUnit.pow 2
  have hd := div_le_div_of_nonneg_right (hcUnit := hu) (hextr hx) (sq_nonneg ‖x₀‖)
  simpa only [Set.mem_ofPred_eq, ContinuousLinearMap.rayleighQuotient, hnorm] using hd

/-- For a self-adjoint operator `T`, a minimum of the Rayleigh quotient of `T` on a sphere centred
at the origin is an eigenvector of `T`, with eigenvalue the global infimum of the Rayleigh
quotient. -/
theorem hasEigenvector_of_isMinOn (hT : IsSelfAdjoint T) {x₀ : E} (hx₀ : x₀ ≠ 0)
    (hextr : IsMinOn T.reApplyInnerSelf (sphere (0 : E) ‖x₀‖) x₀) :
    HasEigenvector (T : E →ₗ[𝕜] E) (⨅ x : { x : E // x ≠ 0 }, T.rayleighQuotient x : ℝ) x₀ := by
  convert! hT.hasEigenvector_of_isLocalExtrOn hx₀ (Or.inl hextr.isLocalMinOn)
  have hx₀' : 0 < ‖x₀‖ := norm_pos_iff.mpr hx₀
  have hx₀'' : (⟨x₀, hx₀⟩ : {x : E // x ≠ 0}) ∈ Subtype.val ⁻¹' sphere (0 : E) ‖x₀‖ := by simp
  rw [T.iInf_rayleigh_eq_iInf_rayleigh_sphere hx₀']
  refine IsMinOn.iInf_eq hx₀'' ?_
  intro x hx
  have hnorm : ‖(x : E)‖ = ‖x₀‖ := mem_sphere_zero_iff_norm.mp hx
  have hu : IsUnit (‖x₀‖ ^ 2) := (norm_ne_zero_iff.mpr hx₀).isUnit.pow 2
  have hd := div_le_div_of_nonneg_right (hcUnit := hu) (hextr hx) (sq_nonneg ‖x₀‖)
  simpa only [Set.mem_ofPred_eq, ContinuousLinearMap.rayleighQuotient, hnorm] using hd

end CompleteSpace

end IsSelfAdjoint

section FiniteDimensional

variable [FiniteDimensional 𝕜 E] {T : E →ₗ[𝕜] E}

namespace LinearMap

namespace IsSymmetric

/-- The supremum of the Rayleigh quotient of a symmetric operator `T` on a nontrivial
finite-dimensional vector space is an eigenvalue for that operator. -/
theorem hasEigenvalue_iSup_of_finiteDimensional [Nontrivial E] (hT : T.IsSymmetric) :
    HasEigenvalue T (⨆ x : { x : E // x ≠ 0 }, RCLike.re ⟪T x, x⟫ / ‖(x : E)‖ ^ 2 : ℝ) := by
  have := FiniteDimensional.proper_rclike 𝕜 E
  let T' := hT.toSelfAdjoint
  obtain ⟨x, hx⟩ : ∃ x : E, x ≠ 0 := exists_ne 0
  have H₁ : IsCompact (sphere (0 : E) ‖x‖) := isCompact_sphere _ _
  have H₂ : (sphere (0 : E) ‖x‖).Nonempty := ⟨x, by simp⟩
  -- key point: in finite dimension, a continuous function on the sphere has a max
  obtain ⟨x₀, hx₀', hTx₀⟩ :=
    H₁.exists_isMaxOn H₂ T'.val.reApplyInnerSelf_continuous.continuousOn
  have hx₀ : ‖x₀‖ = ‖x‖ := by simpa using hx₀'
  have : IsMaxOn T'.val.reApplyInnerSelf (sphere 0 ‖x₀‖) x₀ := by simpa only [← hx₀] using hTx₀
  have hx₀_ne : x₀ ≠ 0 := by
    have : ‖x₀‖ ≠ 0 := by simp only [hx₀, norm_eq_zero, hx, Ne, not_false_iff]
    simpa [← norm_eq_zero, Ne]
  exact hasEigenvalue_of_hasEigenvector (T'.prop.hasEigenvector_of_isMaxOn hx₀_ne this)

/-- The infimum of the Rayleigh quotient of a symmetric operator `T` on a nontrivial
finite-dimensional vector space is an eigenvalue for that operator. -/
theorem hasEigenvalue_iInf_of_finiteDimensional [Nontrivial E] (hT : T.IsSymmetric) :
    HasEigenvalue T (⨅ x : { x : E // x ≠ 0 }, RCLike.re ⟪T x, x⟫ / ‖(x : E)‖ ^ 2 : ℝ) := by
  have := FiniteDimensional.proper_rclike 𝕜 E
  let T' := hT.toSelfAdjoint
  obtain ⟨x, hx⟩ : ∃ x : E, x ≠ 0 := exists_ne 0
  have H₁ : IsCompact (sphere (0 : E) ‖x‖) := isCompact_sphere _ _
  have H₂ : (sphere (0 : E) ‖x‖).Nonempty := ⟨x, by simp⟩
  -- key point: in finite dimension, a continuous function on the sphere has a min
  obtain ⟨x₀, hx₀', hTx₀⟩ :=
    H₁.exists_isMinOn H₂ T'.val.reApplyInnerSelf_continuous.continuousOn
  have hx₀ : ‖x₀‖ = ‖x‖ := by simpa using hx₀'
  have : IsMinOn T'.val.reApplyInnerSelf (sphere 0 ‖x₀‖) x₀ := by simpa only [← hx₀] using hTx₀
  have hx₀_ne : x₀ ≠ 0 := by
    have : ‖x₀‖ ≠ 0 := by simp only [hx₀, norm_eq_zero, hx, Ne, not_false_iff]
    simpa [← norm_eq_zero, Ne]
  exact hasEigenvalue_of_hasEigenvector (T'.prop.hasEigenvector_of_isMinOn hx₀_ne this)

theorem subsingleton_of_no_eigenvalue_finiteDimensional (hT : T.IsSymmetric)
    (hT' : ∀ μ : 𝕜, Module.End.eigenspace (T : E →ₗ[𝕜] E) μ = ⊥) : Subsingleton E :=
  (subsingleton_or_nontrivial E).resolve_right fun _h =>
    absurd (hT' _) hT.hasEigenvalue_iSup_of_finiteDimensional

end IsSymmetric

end LinearMap

end FiniteDimensional
