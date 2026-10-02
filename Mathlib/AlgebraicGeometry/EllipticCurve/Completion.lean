/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

/-!
# Completion and reduction of Weierstrass equations

A minimal Weierstrass equation over a discrete valuation ring remains minimal over its completion.
The proof uses density: a change of variables yielding an integral equation over the completed
fraction field can be approximated by one over the original fraction field, with the same
discriminant valuation.

## Main results

* `WeierstrassCurve.isMinimal_baseChange_adicCompletion`: minimality survives completion.
* `WeierstrassCurve.reduction_baseChange_adicCompletion`: the reductions agree through the
  canonical residue-field isomorphism.
* `WeierstrassCurve.hasGoodReduction_baseChange_adicCompletion_iff`,
  `WeierstrassCurve.hasMultiplicativeReduction_baseChange_adicCompletion_iff`, and
  `WeierstrassCurve.hasSplitMultiplicativeReduction_baseChange_adicCompletion_iff`: completion
  preserves and reflects the reduction type.
-/

@[expose] public section

open IsDedekindDomain.HeightOneSpectrum IsDiscreteValuationRing
open scoped WithZero

namespace WeierstrassCurve

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

local notation "v" => IsDiscreteValuationRing.maximalIdeal R
local notation "K̂" => adicCompletion K (IsDiscreteValuationRing.maximalIdeal R)
local notation "R̂" => adicCompletionIntegers K (IsDiscreteValuationRing.maximalIdeal R)

private lemma completion_valuation_isEquiv :
    ((IsDiscreteValuationRing.maximalIdeal R̂).valuation K̂).IsEquiv
      (Valued.v : Valuation K̂ ℤᵐ⁰) := by
  apply Valuation.isEquiv_of_val_le_one
  intro x
  constructor
  · intro hx
    obtain ⟨a, rfl⟩ := IsDiscreteValuationRing.exists_lift_of_le_one hx
    exact a.2
  · intro hx
    exact valuation_le_one (IsDiscreteValuationRing.maximalIdeal R̂) (⟨x, hx⟩ : R̂)

private lemma isIntegral_iff_valuation_le_one (W : WeierstrassCurve K) :
    IsIntegral R W ↔ (v).valuation K W.a₁ ≤ 1 ∧ (v).valuation K W.a₂ ≤ 1 ∧
      (v).valuation K W.a₃ ≤ 1 ∧ (v).valuation K W.a₄ ≤ 1 ∧ (v).valuation K W.a₆ ≤ 1 := by
  constructor
  · intro h
    obtain ⟨W₀, rfl⟩ := h.integral
    exact ⟨valuation_le_one _ _, valuation_le_one _ _, valuation_le_one _ _,
      valuation_le_one _ _, valuation_le_one _ _⟩
  · rintro ⟨h₁, h₂, h₃, h₄, h₆⟩
    exact isIntegral_of_exists_lift R (exists_lift_of_le_one h₁) (exists_lift_of_le_one h₂)
      (exists_lift_of_le_one h₃) (exists_lift_of_le_one h₄) (exists_lift_of_le_one h₆)

private lemma isIntegral_completion_iff (W : WeierstrassCurve K̂) :
    IsIntegral R̂ W ↔ Valued.v W.a₁ ≤ 1 ∧ Valued.v W.a₂ ≤ 1 ∧
      Valued.v W.a₃ ≤ 1 ∧ Valued.v W.a₄ ≤ 1 ∧ Valued.v W.a₆ ≤ 1 := by
  rw [isIntegral_iff_valuation_le_one]
  simp only [(completion_valuation_isEquiv R).le_one_iff_le_one]

/-- Integrality of a Weierstrass equation is preserved and reflected by completion. -/
theorem isIntegral_baseChange_adicCompletion_iff (W : WeierstrassCurve K) :
    IsIntegral R̂ (W.baseChange K̂) ↔ IsIntegral R W := by
  rw [isIntegral_completion_iff, isIntegral_iff_valuation_le_one]
  simp only [baseChange, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆,
    algebraMap_adicCompletion, Function.comp_apply, Algebra.algebraMap_self, RingHom.id_apply,
    valuedAdicCompletion_eq_valuation']

/-- An integral equation remains integral over the completed valuation ring. -/
instance isIntegral_baseChange_adicCompletion (W : WeierstrassCurve K) [IsIntegral R W] :
    IsIntegral R̂ (W.baseChange K̂) :=
  (isIntegral_baseChange_adicCompletion_iff R W).2 inferInstance

private lemma exists_integral_variableChange_of_completion (W : WeierstrassCurve K)
    (C : VariableChange K̂) (hC : IsIntegral R̂ (C • W.baseChange K̂)) :
    ∃ D : VariableChange K, IsIntegral R (D • W) ∧
      (v).valuation K (D.u : K) = Valued.v (C.u : K̂) := by
  obtain ⟨u, hu⟩ := (v).valuation_surjective K (Valued.v (C.u : K̂))
  have hu₀ : u ≠ 0 := by
    intro h
    have : Valued.v (C.u : K̂) = 0 := by simpa [h] using hu.symm
    exact (Valuation.ne_zero_iff _).2 C.u.ne_zero this
  let u₀ : Kˣ := Units.mk0 u hu₀
  let u₁ : K̂ˣ := Units.map (algebraMap K K̂) u₀
  have hu₁ : Valued.v (u₁ : K̂) = Valued.v (C.u : K̂) := by
    simpa [u₁, u₀, algebraMap_adicCompletion, valuedAdicCompletion_eq_valuation'] using hu
  let F (x : Fin 3 → K̂) : WeierstrassCurve K̂ :=
    (⟨u₁, x 0, x 1, x 2⟩ : VariableChange K̂) • W.baseChange K̂
  have hF : IsIntegral R̂ (F ![C.r, C.s, C.t]) := by
    rw [isIntegral_completion_iff] at hC ⊢
    simpa [F, variableChange_def, map_mul, map_pow, Units.val_inv_eq_inv_val,
      map_inv₀, hu₁] using hC
  have hopen : IsOpen {x : Fin 3 → K̂ | IsIntegral R̂ (F x)} := by
    simp only [isIntegral_completion_iff]
    apply IsOpen.inter _ (IsOpen.inter _ (IsOpen.inter _ (IsOpen.inter _ _)))
    all_goals
      exact (Valued.isOpen_valuationSubring K̂).preimage (by
        dsimp [F, variableChange_def]
        fun_prop)
  obtain ⟨x, hx⟩ :=
    (DenseRange.piMap fun _ : Fin 3 ↦ denseRange_algebraMap K v).exists_mem_open hopen
      ⟨![C.r, C.s, C.t], hF⟩
  refine ⟨⟨u₀, x 0, x 1, x 2⟩, ?_, hu⟩
  apply (isIntegral_baseChange_adicCompletion_iff R _).1
  simpa only [F, baseChange, ← map_variableChange, VariableChange.map, u₁,
    Set.mem_ofPred_eq, Pi.map_apply] using hx

/-- A minimal Weierstrass equation remains minimal over the completed valuation ring. -/
instance isMinimal_baseChange_adicCompletion (W : WeierstrassCurve K) [IsMinimal R W] :
    IsMinimal R̂ (W.baseChange K̂) where
  val_Δ_maximal := by
    refine ⟨by simpa only [one_smul] using
      (inferInstance : IsIntegral R̂ (W.baseChange K̂)), fun C hC _ ↦ ?_⟩
    have := hC
    obtain ⟨D, hD, hu⟩ := exists_integral_variableChange_of_completion R W C hC
    have := hD
    have hDle : discriminantValuationAux R (D • W) ≤ discriminantValuationAux R W := by
      have hm := (IsMinimal.val_Δ_maximal (R := R) (W := W)).2 hD
      simp only [one_smul] at hm
      exact (le_total _ _).elim id hm
    change (discriminantValuationAux R̂ (C • W.baseChange K̂)).val ≤
      (discriminantValuationAux R̂ (1 • W.baseChange K̂)).val
    rw [one_smul, discriminantValuationAux_eq_of_isIntegral,
      discriminantValuationAux_eq_of_isIntegral]
    apply (completion_valuation_isEquiv R).le_iff_le.mpr
    change (discriminantValuationAux R (D • W)).val ≤ (discriminantValuationAux R W).val at hDle
    rw [discriminantValuationAux_eq_of_isIntegral,
      discriminantValuationAux_eq_of_isIntegral] at hDle
    simpa only [variableChange_Δ, baseChange, map_Δ, map_mul, map_pow,
      Units.val_inv_eq_inv_val, map_inv₀, hu, algebraMap_adicCompletion, Function.comp_apply,
      Algebra.algebraMap_self, RingHom.id_apply, valuedAdicCompletion_eq_valuation'] using hDle

/-- The integral model over the completed ring is obtained by extending coefficients. -/
theorem integralModel_baseChange_adicCompletion (W : WeierstrassCurve K) [IsIntegral R W] :
    (W.baseChange K̂).integralModel R̂ = (W.integralModel R).baseChange R̂ := by
  apply map_injective (IsFractionRing.injective R̂ K̂)
  change ((W.baseChange K̂).integralModel R̂).baseChange K̂ =
    ((W.integralModel R).baseChange R̂).baseChange K̂
  rw [baseChange_integralModel_eq]
  simp only [baseChange, map_map, ← IsScalarTower.algebraMap_eq]
  simpa only [baseChange, map_map, ← IsScalarTower.algebraMap_eq] using
    congrArg (fun V : WeierstrassCurve K ↦ V.baseChange K̂)
      (baseChange_integralModel_eq R W).symm

/-- The reduction over the completed ring is the original reduction transported through the
canonical residue-field isomorphism. -/
theorem reduction_baseChange_adicCompletion (W : WeierstrassCurve K) [IsMinimal R W] :
    (W.baseChange K̂).reduction R̂ = (W.reduction R).map
      (residueFieldEquivAdicCompletion R (K := K)).toRingEquiv.toRingHom := by
  rw [reduction, reduction, integralModel_baseChange_adicCompletion, baseChange, map_map, map_map]
  congr 1

/-- Good reduction is preserved and reflected by completion. -/
theorem hasGoodReduction_baseChange_adicCompletion_iff (W : WeierstrassCurve K) [IsMinimal R W] :
    (W.baseChange K̂).HasGoodReduction R̂ ↔ W.HasGoodReduction R := by
  simp only [hasGoodReduction_iff,
    (completion_valuation_isEquiv R).eq_one_iff_eq_one,
    baseChange, map_Δ, algebraMap_adicCompletion, Function.comp_apply,
    Algebra.algebraMap_self, RingHom.id_apply, valuedAdicCompletion_eq_valuation']
  exact and_congr_left fun _ ↦ iff_of_true (isMinimal_baseChange_adicCompletion R W) inferInstance

/-- Multiplicative reduction is preserved and reflected by completion. -/
theorem hasMultiplicativeReduction_baseChange_adicCompletion_iff
    (W : WeierstrassCurve K) [IsMinimal R W] :
    (W.baseChange K̂).HasMultiplicativeReduction R̂ ↔ W.HasMultiplicativeReduction R := by
  simp only [hasMultiplicativeReduction_iff,
    (completion_valuation_isEquiv R).eq_one_iff_eq_one,
    (completion_valuation_isEquiv R).lt_one_iff_lt_one,
    baseChange, map_Δ, map_c₄, algebraMap_adicCompletion, Function.comp_apply,
    Algebra.algebraMap_self, RingHom.id_apply, valuedAdicCompletion_eq_valuation']
  exact and_congr_left fun _ ↦ iff_of_true (isMinimal_baseChange_adicCompletion R W) inferInstance

/-- Additive reduction is preserved and reflected by completion. -/
theorem hasAdditiveReduction_baseChange_adicCompletion_iff
    (W : WeierstrassCurve K) [IsMinimal R W] :
    (W.baseChange K̂).HasAdditiveReduction R̂ ↔ W.HasAdditiveReduction R := by
  simp only [hasAdditiveReduction_iff,
    (completion_valuation_isEquiv R).lt_one_iff_lt_one,
    baseChange, map_Δ, map_c₄, algebraMap_adicCompletion, Function.comp_apply,
    Algebra.algebraMap_self, RingHom.id_apply, valuedAdicCompletion_eq_valuation']
  exact and_congr_left fun _ ↦ iff_of_true (isMinimal_baseChange_adicCompletion R W) inferInstance

/-- Split multiplicative reduction is preserved and reflected by completion. -/
theorem hasSplitMultiplicativeReduction_baseChange_adicCompletion_iff
    (W : WeierstrassCurve K) [IsMinimal R W] :
    (W.baseChange K̂).HasSplitMultiplicativeReduction R̂ ↔
      W.HasSplitMultiplicativeReduction R := by
  let e := residueFieldEquivAdicCompletion R (K := K)
  have hmap : ((W.baseChange K̂).integralModel R̂).nodePolynomial.map
      (algebraMap R̂ (IsLocalRing.ResidueField R̂)) =
      (((W.integralModel R).nodePolynomial.map
        (algebraMap R (IsLocalRing.ResidueField R))).map e.toRingHom) := by
    simpa only [reduction, map_nodePolynomial, IsLocalRing.ResidueField.algebraMap_eq] using
      congrArg nodePolynomial (reduction_baseChange_adicCompletion R W)
  have hm := hasMultiplicativeReduction_baseChange_adicCompletion_iff R W
  constructor
  · intro h
    have := hm.mp h.toHasMultiplicativeReduction
    refine ⟨?_⟩
    have hh := h.splitMultiplicativeReduction
    rw [hmap] at hh
    have hh' := hh.map e.symm.toRingHom
    have hid (p : Polynomial (IsLocalRing.ResidueField R)) :
        (p.map e.toRingHom).map e.symm.toRingHom = p := by
      ext n
      simp only [Polynomial.coeff_map]
      exact e.symm_apply_apply (p.coeff n)
    rwa [hid] at hh'
  · intro h
    have := hm.mpr h.toHasMultiplicativeReduction
    refine ⟨?_⟩
    rw [hmap]
    exact h.splitMultiplicativeReduction.map e.toRingHom

end WeierstrassCurve
