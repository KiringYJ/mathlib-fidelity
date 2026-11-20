/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/

module

public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.NumberTheory.NumberField.ProductFormula
public import Mathlib.Algebra.FiniteSupport.Basic

/-!
# The finite adele ring of a number field

This file concerns the finite adele ring of a Dedekind domain `R` and its field of
fractions under the assumption that `Ring.HasFiniteQuotients R` and `Infinite R`.
Later, these results are applied to the case where `K` is a number field and `R` is `𝓞 K`.

## Main definitions

- `NumberField.FiniteAdeleRing.instNormFiniteAdeleRing` : the norm on the finite adele ring.

## Tags
adele ring, number field
-/

@[expose] public section

namespace NumberField

open IsDedekindDomain FiniteAdeleRing

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Ring.HasFiniteQuotients R] [Infinite R]
  [Field K] [Algebra R K] [IsFractionRing R K]

namespace AdeleRing

/-- `𝔸ᶠ[K]` is notation for `IsDedekindDomain.FiniteAdeleRing (𝓞 K) K`. -/
scoped notation:max "𝔸ᶠ[" K "]" => FiniteAdeleRing (𝓞 K) K

end AdeleRing

namespace FiniteAdeleRing

open scoped AdeleRing

theorem hasFiniteMulSupport_norm (x : 𝔸ᶠ[R, K]ˣ) : (fun v ↦ ‖x.1 v‖).HasFiniteMulSupport :=
  (FiniteAdeleRing.hasFiniteMulSupport_valued x).of_eq_one_iff
    fun _ ↦ Valued.toNormedField.norm_eq_one_iff.symm

private theorem hasProd_subset_valued_one_lt (x : 𝔸ᶠ[R, K]) :
    HasProd (fun v : {v | 1 < Valued.v (x v)} ↦ ‖x v‖)
      (∏ᶠ v : {v | 1 < Valued.v (x v)}, ‖x v‖) := by
  let : Fintype _ := (finite_valued_one_lt x).fintype
  rw [finprod_eq_prod_of_fintype]
  exact hasProd_fintype _

open Filter HeightOneSpectrum Valued in
private theorem hasProd_zero_subset_lt_one_valued {x : 𝔸ᶠ[R, K]} (hx : ¬IsUnit x)
    (hx₀ : ∀ v, x v ≠ 0) : HasProd (fun v : {v | Valued.v (x v) < 1} ↦ ‖x v‖) 0 := by
  have hx := infinite_valued_ne_one_of_not_isUnit (by simpa using hx₀) hx
  have hx_prop : {v | 1 < Valued.v (x v)}.Finite := finite_valued_one_lt x
  have hx_inf : {v | Valued.v (x v) < 1}.Infinite := (hx.sdiff hx_prop).mono (by grind)
  let : Infinite {v | Valued.v (x v) < 1} := hx_inf.to_subtype
  have hnorm (v : {v | Valued.v (x v) < 1}) : ‖x v‖ ≤ (2 : ℝ)⁻¹ := by
    have htwo : 2 ≤ ‖(x v)⁻¹‖ := by
      apply FinitePlace.two_le_norm_of_one_lt_norm
      grind [toNormedField.one_lt_norm_iff, map_inv₀, one_lt_inv₀ (Valued.v.pos_iff.2 (hx₀ v))]
    rw [norm_inv] at htwo
    simpa only [inv_inv₀] using inv_anti₀ (by norm_num : (0 : ℝ) < 2) htwo
  have hprod (s : Finset {v | Valued.v (x v) < 1}) :
      ∏ v ∈ s, ‖x v‖ ≤ ((2 : ℝ)⁻¹) ^ s.card := by
    simpa only [Finset.prod_const] using
      Finset.prod_le_prod₀ (s := s) (fun v _ ↦ norm_nonneg (x v)) (fun v _ ↦ hnorm v)
  have hlim := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
    (by norm_num)).comp (tendsto_card_atTop_atTop (α := {v | Valued.v (x v) < 1}))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ ↦ Finset.prod_nonneg fun _ _ ↦ norm_nonneg _) hprod

theorem hasProd_zero_of_not_isUnit {x : 𝔸ᶠ[R, K]} (hx : ¬IsUnit x) :
    HasProd (fun v ↦ ‖x v‖) 0 := by
  by_cases hx₀ : ∃ v, x v = 0
  · exact hasProd_zero_of_exists_eq_zero (by simpa using hx₀)
  have hT := hasProd_zero_subset_lt_one_valued hx (by simpa using hx₀)
  have h : HasProd (fun v : {v | Valued.v (x v) = 1} ↦ ‖x.1 v‖) 1 := by
    convert hasProd_one; aesop (add simp [Valued.toNormedField.norm_eq_one_iff])
  have := HasProd.mul_disjoint (by grind) (hasProd_subset_valued_one_lt x) h (f := fun v ↦ ‖x v‖)
  simpa using this.mul_isCompl ⟨by grind, fun _ _ _ ↦ by grind⟩ hT

theorem tprod_norm_eq_finprod_of_isUnit {x : 𝔸ᶠ[R, K]} (hx : IsUnit x) :
    ∏' v, ‖x v‖ = ∏ᶠ v, ‖x v‖ := by
  rw [tprod_eq_finprod]
  exact hasFiniteMulSupport_norm hx.unit

theorem tprod_norm_eq_finprod_of_unit (x : 𝔸ᶠ[R, K]ˣ) :
    ∏' v, ‖(x : 𝔸ᶠ[R, K]) v‖ = ∏ᶠ v, ‖(x : 𝔸ᶠ[R, K]) v‖ :=
  tprod_norm_eq_finprod_of_isUnit x.isUnit

theorem tprod_eq_zero_of_not_isUnit {x : 𝔸ᶠ[R, K]} (hx : ¬ IsUnit x) :
    ∏' v, ‖x v‖ = 0 := by
  rw [HasProd.tprod_eq]
  exact hasProd_zero_of_not_isUnit hx

/-- The norm on the finite adele ring is the product of all the local norms. If a finite adele is
a unit, then this is a finite product in disguise. Otherwise, it is zero (and not the junk
`tprod` value of `1`). -/
noncomputable instance : Norm 𝔸ᶠ[R, K] where norm x := ∏' v, ‖x v‖

theorem norm_def (x : 𝔸ᶠ[R, K]) : ‖x‖ = ∏' v, ‖x v‖ := rfl

theorem norm_eq_finprod_of_unit (x : 𝔸ᶠ[R, K]ˣ) : ‖(x : 𝔸ᶠ[R, K])‖ = ∏ᶠ v, ‖(x : 𝔸ᶠ[R, K]) v‖ :=
  tprod_norm_eq_finprod_of_unit x

theorem norm_eq_zero_of_not_isUnit {x : 𝔸ᶠ[R, K]} (hx : ¬IsUnit x) : ‖x‖ = 0 :=
  tprod_eq_zero_of_not_isUnit hx

variable [NumberField K]

theorem unitEmbedding_norm_apply (x : Kˣ) :
    ‖(unitEmbedding (𝓞 K) K x : 𝔸ᶠ[𝓞 K, K])‖ = ∏ᶠ v, FinitePlace.mk v (x : K) :=
      norm_eq_finprod_of_unit _

theorem unitEmbedding_norm_apply_eq_finprod_finitePlace (x : Kˣ) :
    ‖(unitEmbedding (𝓞 K) K x : 𝔸ᶠ[𝓞 K, K])‖ = ∏ᶠ v : FinitePlace K, v x := by
  rw [unitEmbedding_norm_apply, ← finprod_comp FinitePlace.equivHeightOneSpectrum.invFun
    FinitePlace.equivHeightOneSpectrum.symm.bijective]
  exact finprod_congr fun _ ↦ rfl

theorem unitEmbedding_norm_eq_inv_abs_norm (x : Kˣ) :
    ‖(unitEmbedding (𝓞 K) K x : 𝔸ᶠ[𝓞 K, K])‖ = (Checked.inv |Algebra.norm ℚ (x : K)|
      (abs_ne_zero.mpr (Algebra.norm_ne_zero_iff.mpr x.ne_zero)).isUnit : ℚ) := by
  rw [← FinitePlace.prod_eq_inv_abs_norm x.ne_zero, unitEmbedding_norm_apply_eq_finprod_finitePlace]

theorem coe_norm_eq_inv_abs_norm {x : K} (hx : x ≠ 0) :
    ‖algebraMap K 𝔸ᶠ[K] x‖ = (Checked.inv |Algebra.norm ℚ x|
      (abs_ne_zero.mpr (Algebra.norm_ne_zero_iff.mpr hx)).isUnit : ℚ) :=
  unitEmbedding_norm_eq_inv_abs_norm (.mk0 x hx)

end NumberField.FiniteAdeleRing
