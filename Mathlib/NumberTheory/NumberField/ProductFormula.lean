/-
Copyright (c) 2024 Fabrizio Barroero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero
-/
module

public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.RingTheory.Flat.TorsionFree

/-!
# The Product Formula for number fields

In this file we prove the Product Formula for number fields: for any non-zero element `x` of a
number field `K`, we have `∏ |x|ᵥ=1` where the product runs over the equivalence classes of absolute
values of `K`. The `|⬝|ᵥ` are normalized as follows:
- for the infinite places, `|⬝|ᵥ` is the absolute value on `K` induced by the corresponding field
  embedding in `ℂ` and the usual absolute value on `ℂ`;
- for the finite places and a non-zero `x`, `|x|ᵥ` is equal to the norm of the corresponding maximal
  ideal of `𝓞 K` raised to the power of the `v`-adic valuation of `x`.

## Main Results

* `NumberField.FinitePlace.prod_eq_inv_abs_norm`: for any non-zero element `x` of a number field
  `K`, the product `∏ |x|ᵥ` of the absolute values of `x` associated to the finite places of `K` is
  equal to the inverse of the norm of `x`.
* `NumberField.prod_abs_eq_one`: for any non-zero element `x` of a number field `K`, we have
  `∏ |x|ᵥ=1`, where the product runs over the equivalence classes of absolute values of `K`.

## Tags
number field, embeddings, places, infinite places, finite places, product formula
-/

public section

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

open Algebra

open Function Ideal IsDedekindDomain HeightOneSpectrum in
/-- For any non-zero `x` in `𝓞 K`, the product of `w x`, where `w` runs over `FinitePlace K`, is
equal to the inverse of the absolute value of `Algebra.norm ℤ x`. -/
theorem FinitePlace.prod_eq_inv_abs_norm_int {x : 𝓞 K} (h_x_nezero : x ≠ 0) :
    ∏ᶠ w : FinitePlace K, w x = Checked.inv (|norm ℤ x| : ℝ)
      (abs_ne_zero.mpr
        (Int.cast_ne_zero.mpr (Algebra.norm_ne_zero_iff.mpr h_x_nezero))).isUnit := by
  simp only [← finprod_comp_equiv equivHeightOneSpectrum.symm, equivHeightOneSpectrum_symm_apply]
  refine (inv_eq_of_mul_eq_one_left₀ ?_).symm
  norm_cast
  have h_span_nezero : span {x} ≠ 0 := by simp [h_x_nezero]
  rw [Int.abs_eq_natAbs, ← absNorm_span_singleton,
    ← finprod_heightOneSpectrum_factorization h_span_nezero, Int.cast_natCast]
  let t₀ := {v : HeightOneSpectrum (𝓞 K) | x ∈ v.asIdeal}
  have h_fin₀ : t₀.Finite := by simp only [← dvd_span_singleton, finite_factors h_span_nezero, t₀]
  let t₁ := (fun v : HeightOneSpectrum (𝓞 K) ↦ ‖embedding v (x : K)‖).mulSupport
  let t₂ :=
    (fun v : HeightOneSpectrum (𝓞 K) ↦ (absNorm (v.maxPowDividing (span {x})) : ℝ)).mulSupport
  have h_fin₁ : t₁.Finite := h_fin₀.subset <| by simp [norm_eq_one_iff_notMem, t₁, t₀]
  have h_fin₂ : t₂.Finite := by
    refine h_fin₀.subset ?_
    simp only [mulSupport_subset_iff, Set.mem_ofPred_eq, t₂, t₀,
      maxPowDividing, ← dvd_span_singleton]
    intro v hv
    simp only [map_pow, Nat.cast_pow, ← pow_zero (absNorm v.asIdeal : ℝ)] at hv
    refine (Associates.count_ne_zero_iff_dvd h_span_nezero (irreducible v)).1 <| fun h ↦ hv ?_
    congr
  have h_prod : (absNorm (∏ᶠ (v : HeightOneSpectrum (𝓞 K)), v.maxPowDividing (span {x})) : ℝ) =
      ∏ᶠ (v : HeightOneSpectrum (𝓞 K)), (absNorm (v.maxPowDividing (span {x})) : ℝ) :=
    ((Nat.castRingHom ℝ).toMonoidHom.comp absNorm.toMonoidHom).map_finprod_of_preimage_one
      (by simp) _
  rw [h_prod, ← finprod_mul_distrib h_fin₁ h_fin₂]
  exact finprod_eq_one_of_forall_eq_one fun v ↦ embedding_mul_absNorm _ v h_x_nezero

/-- For any non-zero `x` in `K`, the product of `w x`, where `w` runs over `FinitePlace K`, is
equal to the inverse of the absolute value of `Algebra.norm ℚ x`. -/
theorem FinitePlace.prod_eq_inv_abs_norm {x : K} (h_x_nezero : x ≠ 0) :
    ∏ᶠ w : FinitePlace K, w x = (Checked.inv |(Algebra.norm ℚ) x|
      (abs_ne_zero.mpr (Algebra.norm_ne_zero_iff.mpr h_x_nezero)).isUnit : ℚ) := by
  obtain ⟨a, b, hb, hfrac⟩ := IsFractionRing.div_surjective (𝓞 K) x
  have hb₀ := nonZeroDivisors.ne_zero hb
  have hmul : x * (b : K) = (a : K) := eq_div_iff.mp hfrac.symm
  have ha : a ≠ 0 := fun ha ↦
    mul_ne_zero h_x_nezero (RingOfIntegers.coe_ne_zero_iff.mpr hb₀) (by simpa [ha] using hmul)
  have hnorm : |(norm ℚ x : ℝ)| * (|norm ℤ b| : ℝ) = (|norm ℤ a| : ℝ) := by
    have coe_norm (c : 𝓞 K) : (norm ℤ c : ℝ) = (norm ℚ (c : K) : ℝ) := by
      rw [← Rat.cast_intCast, coe_norm_int]
    rw [coe_norm a, coe_norm b, ← abs_mul, ← Rat.cast_mul, ← map_mul, hmul]
  have hprod := finprod_mul_distrib (hasFiniteMulSupport h_x_nezero) (hasFiniteMulSupport_int hb₀)
  simp only [← map_mul, hmul, prod_eq_inv_abs_norm_int ha, prod_eq_inv_abs_norm_int hb₀,
    ← hnorm, mul_inv₀] at hprod
  simp only [Rat.cast_inv, Rat.cast_abs]
  have hb_norm : (|norm ℤ b| : ℝ) ≠ 0 :=
    abs_ne_zero.mpr (Int.cast_ne_zero.mpr (Algebra.norm_ne_zero_iff.mpr hb₀))
  exact mul_right_cancel₀ (inv_ne_zero (ha := hb_norm.isUnit)) hprod.symm

open FinitePlace in
/-- The Product Formula for the Number Field `K`. -/
theorem prod_abs_eq_one {x : K} (h_x_nezero : x ≠ 0) :
    (∏ w : InfinitePlace K, w x ^ w.mult) * ∏ᶠ w : FinitePlace K, w x = 1 := by
  simp [prod_eq_inv_abs_norm, InfinitePlace.prod_eq_abs_norm, h_x_nezero]

end NumberField
