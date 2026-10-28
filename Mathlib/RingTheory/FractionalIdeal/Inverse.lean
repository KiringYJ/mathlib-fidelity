/-
Copyright (c) 2020 Kenji Nakagawa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenji Nakagawa, Anne Baanen, Filippo A. E. Nuccio
-/
module

public import Mathlib.RingTheory.FractionalIdeal.Operations

/-!
# Inverses of fractional ideals

The inverse `I⁻¹` of an invertible fractional ideal `I` is its inverse in the monoid of fractional
ideals. It is the colon `colon 1 I _ = {x | x I ⊆ 1}` (`FractionalIdeal.inv_eq_colon`).
For a nonzero fractional ideal `I` that is not known to be invertible, the colon `colon 1 I hI`
takes the place of an inverse: `I * colon 1 I hI = 1` exactly when `I` is invertible
(`FractionalIdeal.mul_colon_self_cancel_iff_isUnit`).
The theorem that all nonzero fractional ideals are invertible in a Dedekind domain can be found in
`Mathlib/RingTheory/DedekindDomain/Ideal/Basic.lean`.

## Main results

- `FractionalIdeal.inv_eq_colon`: the inverse of an invertible fractional ideal is a colon.
- `FractionalIdeal.isUnit_spanSingleton_iff`: a principal fractional ideal `spanSingleton x` is
  invertible exactly when `x ≠ 0`; `checked_unit` uses it to find the invertibility of
  `spanSingleton x` from `x ≠ 0`.
- `FractionalIdeal.invertible_of_principal`: nonzero principal fractional ideals are invertible.

## References

* [D. Marcus, *Number Fields*][marcus1977number]
* [J.W.S. Cassels, A. Fröhlich, *Algebraic Number Theory*][cassels1967algebraic]
* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992]

## Tags

fractional ideal, invertible ideal
-/

public section

assert_not_exists IsDedekindDomain

variable (K : Type*) [Field K]

open scoped nonZeroDivisors Polynomial

namespace FractionalIdeal

variable {R₁ : Type*} [CommRing R₁] [IsDomain R₁] [Algebra R₁ K] [IsFractionRing R₁ K]
variable {I J : FractionalIdeal R₁⁰ K}

variable {K}

/-- The inverse of an invertible fractional ideal `I` is the colon `{x | x I ⊆ 1}`. -/
theorem inv_eq_colon (I : FractionalIdeal R₁⁰ K) {hI : IsUnit I} :
    I⁻¹ = colon 1 I hI.ne_zero := by
  rw [← one_div₀, div_eq_colon]

theorem coe_one_colon {J : FractionalIdeal R₁⁰ K} {hJ : J ≠ 0} :
    (colon 1 J hJ : Submodule R₁ K) = IsLocalization.coeSubmodule K ⊤ / (J : Submodule R₁ K) := by
  rw [coe_colon, coe_one, IsLocalization.coeSubmodule_top]

theorem mem_inv_iff {hI : IsUnit I} {x : K} :
    x ∈ I⁻¹ ↔ ∀ y ∈ I, x * y ∈ (1 : FractionalIdeal R₁⁰ K) := by
  rw [inv_eq_colon, mem_colon_iff]

variable (K) in
theorem coe_ideal_le_self_mul_one_colon (I : Ideal R₁) {hI : (I : FractionalIdeal R₁⁰ K) ≠ 0} :
    (I : FractionalIdeal R₁⁰ K) ≤ I * colon 1 (I : FractionalIdeal R₁⁰ K) hI :=
  le_self_mul_one_colon coeIdeal_le_one

/-- A nonzero fractional ideal `I` is invertible exactly when `I` times the colon
`{x | x I ⊆ 1}` is `1`. -/
theorem mul_colon_self_cancel_iff_isUnit {I : FractionalIdeal R₁⁰ K} {hI : I ≠ 0} :
    I * colon 1 I hI = 1 ↔ IsUnit I :=
  mul_colon_self_cancel_iff.trans isUnit_iff_exists_inv.symm

variable {K' : Type*} [Field K'] [Algebra R₁ K'] [IsFractionRing R₁ K']

omit [IsDomain R₁] [IsFractionRing R₁ K] [IsFractionRing R₁ K'] in
@[simp]
protected theorem map_inv (I : FractionalIdeal R₁⁰ K) {hI : IsUnit I} (h : K ≃ₐ[R₁] K') :
    I⁻¹.map (h : K →ₐ[R₁] K') =
      Checked.inv (I.map (h : K →ₐ[R₁] K')) (hI.map (mapEquiv h)) :=
  Eq.symm <| inv_eq_of_mul_eq_one_right₀ <| map_mul_eq_one (mapEquiv h) mul_inv_cancel₀

open Submodule Submodule.IsPrincipal

omit [IsDomain R₁] in
/-- A principal fractional ideal `spanSingleton x` is invertible exactly when `x ≠ 0`. -/
@[simp]
theorem isUnit_spanSingleton_iff {x : K} : IsUnit (spanSingleton R₁⁰ x) ↔ x ≠ 0 := by
  refine ⟨fun h hx ↦ ?_, fun hx ↦ IsUnit.of_mul_eq_one (spanSingleton R₁⁰ x⁻¹) ?_⟩
  · rw [hx, spanSingleton_zero] at h
    exact not_isUnit_zero h
  · rw [spanSingleton_mul_spanSingleton, mul_inv_cancel₀, spanSingleton_one]

omit [IsDomain R₁] in
theorem isUnit_coeIdeal_span_singleton_iff {x : R₁} :
    IsUnit ((Ideal.span {x} : Ideal R₁) : FractionalIdeal R₁⁰ K) ↔ x ≠ 0 := by
  rw [coeIdeal_span_singleton, isUnit_spanSingleton_iff,
    map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R₁ K)]

/-! The rule below extends `checked_unit`, so that `(spanSingleton R₁⁰ x)⁻¹` and
`(Ideal.span {x} : FractionalIdeal R₁⁰ K)⁻¹` find their evidence from `x ≠ 0`. A local hypothesis
is used first, so that a theorem's evidence binder appears verbatim in its statement. -/

macro_rules | `(tactic| checked_unit) => `(tactic|
    solve
    | assumption
    | ((with_reducible apply FractionalIdeal.isUnit_spanSingleton_iff.mpr); checked_nonzero)
    | ((with_reducible apply FractionalIdeal.isUnit_coeIdeal_span_singleton_iff.mpr);
        checked_nonzero))

@[simp]
theorem spanSingleton_inv (x : K) {h : IsUnit (spanSingleton R₁⁰ x)} :
    (spanSingleton R₁⁰ x)⁻¹ = spanSingleton R₁⁰ x⁻¹ := by
  rw [inv_eq_colon, one_colon_spanSingleton]

theorem spanSingleton_div_spanSingleton (x y : K) {h : IsUnit (spanSingleton R₁⁰ y)} :
    spanSingleton R₁⁰ x / spanSingleton R₁⁰ y = spanSingleton R₁⁰ (x / y) := by
  rw [div_eq_mul_inv₀, spanSingleton_inv, spanSingleton_mul_spanSingleton, div_eq_mul_inv₀]

theorem generator_ne_zero {R₁ : Type*} [CommRing R₁] [Algebra R₁ K] [IsLocalization R₁⁰ K]
    {I : FractionalIdeal R₁⁰ K} [Submodule.IsPrincipal (I : Submodule R₁ K)] (h : I ≠ 0) :
    generator (I : Submodule R₁ K) ≠ 0 := by
  intro generator_I_eq_zero
  apply h
  rw [eq_spanSingleton_of_principal I, generator_I_eq_zero, spanSingleton_zero]

theorem mul_generator_self_inv {R₁ : Type*} [CommRing R₁] [Algebra R₁ K] [IsLocalization R₁⁰ K]
    (I : FractionalIdeal R₁⁰ K) [Submodule.IsPrincipal (I : Submodule R₁ K)] (h : I ≠ 0) :
    I * spanSingleton _ (Checked.inv (generator (I : Submodule R₁ K))
      (generator_ne_zero h).isUnit) = 1 := by
  -- Rewrite only the `I` that appears alone.
  conv_lhs => congr; rw [eq_spanSingleton_of_principal I]
  rw [spanSingleton_mul_spanSingleton, mul_inv_cancel₀, spanSingleton_one]

omit [IsDomain R₁] in
theorem invertible_of_principal (I : FractionalIdeal R₁⁰ K)
    [Submodule.IsPrincipal (I : Submodule R₁ K)] (h : I ≠ 0) : IsUnit I :=
  IsUnit.of_mul_eq_one _ (mul_generator_self_inv I h)

omit [IsDomain R₁] in
theorem invertible_iff_generator_nonzero (I : FractionalIdeal R₁⁰ K)
    [Submodule.IsPrincipal (I : Submodule R₁ K)] :
    IsUnit I ↔ generator (I : Submodule R₁ K) ≠ 0 := by
  constructor
  · intro hI hg
    apply hI.ne_zero
    rw [eq_spanSingleton_of_principal I, hg, spanSingleton_zero]
  · intro hg
    apply invertible_of_principal
    rw [eq_spanSingleton_of_principal I]
    intro hI
    have := mem_spanSingleton_self R₁⁰ (generator (I : Submodule R₁ K))
    rw [hI, mem_zero_iff] at this
    contradiction

omit [IsDomain R₁] in
theorem isPrincipal_inv (I : FractionalIdeal R₁⁰ K) [Submodule.IsPrincipal (I : Submodule R₁ K)]
    {hI : IsUnit I} : Submodule.IsPrincipal I⁻¹.1 := by
  have h : I ≠ 0 := hI.ne_zero
  rw [val_eq_coe, isPrincipal_iff]
  exact ⟨Checked.inv (generator (I : Submodule R₁ K)) (generator_ne_zero h).isUnit,
    (eq_inv_of_mul_eq_one_right₀ (mul_generator_self_inv I h)).symm⟩

lemma den_mem_one_colon {I : FractionalIdeal R₁⁰ K} {hI : I ≠ 0} :
    algebraMap R₁ K (I.den : R₁) ∈ colon 1 I hI := by
  rw [mem_colon_iff]
  intro i hi
  rw [← Algebra.smul_def (I.den : R₁) i, ← mem_coe, coe_one]
  suffices Submodule.map (Algebra.linearMap R₁ K) I.num ≤ 1 from
    this <| (den_mul_self_eq_num I).symm ▸ smul_mem_pointwise_smul i I.den I.coeToSubmodule hi
  apply le_trans <| map_mono (show I.num ≤ 1 by simp only [Ideal.one_eq_top, le_top])
  rw [Ideal.one_eq_top, Submodule.map_top, one_eq_range]

lemma num_le_mul_one_colon (I : FractionalIdeal R₁⁰ K) {hI : I ≠ 0} :
    I.num ≤ I * colon 1 I hI := by
  rw [mul_comm, ← den_mul_self_eq_num']
  gcongr
  exact spanSingleton_le_iff_mem.2 den_mem_one_colon

lemma bot_lt_mul_one_colon {I : FractionalIdeal R₁⁰ K} {hI : I ≠ 0} : ⊥ < I * colon 1 I hI :=
  lt_of_lt_of_le (coeIdeal_ne_zero.2 (hI ∘ num_eq_zero_iff.1)).bot_lt I.num_le_mul_one_colon

end FractionalIdeal
