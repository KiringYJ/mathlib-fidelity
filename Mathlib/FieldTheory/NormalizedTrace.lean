/-
Copyright (c) 2025 Michal Staromiejski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michal Staromiejski
-/
module

public import Mathlib.RingTheory.Trace.Basic

/-!

# Normalized trace

This file defines the *normalized trace* map; that is, an `F`-linear map from the algebraic closure
of `F` to `F` defined as the trace of an element from its adjoin extension divided by its degree.

To avoid heavy imports, we define it here as a map from an arbitrary algebraic (equivalently
integral) extension of `F`.

## Main definitions

- `normalizedTrace`: the trace of an element from the simple adjoin divided by the degree;
  it is a non-trivial `F`-linear map from an arbitrary algebraic extension `K` to `F`.

## Main results

- `normalizedTrace_intermediateField`: for a tower `K / E / F` of algebraic extensions,
  `normalizedTrace F E` agrees with `normalizedTrace F K` on `E`.
- `normalizedTrace_trans`: for a tower `K / E / F` of algebraic extensions, the normalized trace
  from `K` to `E` composed with the normalized trace from `E` to `F` equals the normalized trace
  from `K` to `F`.
- `normalizedTrace_self`: `normalizedTrace F F` is the identity map.

-/

@[expose] public section

namespace Algebra

variable (F K : Type*) [Field F] [Field K] [Algebra F K]

open IntermediateField

private theorem isUnit_finrank [CharZero F] [FiniteDimensional F K] :
    IsUnit (Module.finrank F K : F) :=
  (Nat.cast_ne_zero.mpr (Module.finrank_pos (R := F) (M := K)).ne').isUnit

variable [CharZero F] [Algebra.IsIntegral F K]

private theorem isUnit_finrank_adjoin (a : K) : IsUnit (Module.finrank F F⟮a⟯ : F) := by
  have : FiniteDimensional F F⟮a⟯ := adjoin.finiteDimensional (IsIntegral.isIntegral a)
  exact isUnit_finrank F F⟮a⟯

set_option backward.privateInPublic true in
/- The normalized trace of an element is its trace from its simple extension scaled by the
reciprocal of the extension degree. -/
private noncomputable def normalizedTraceAux (a : K) : F :=
  Checked.inv (Module.finrank F F⟮a⟯ : F) (isUnit_finrank_adjoin F K a) •
    trace F F⟮a⟯ (AdjoinSimple.gen F a)

private theorem normalizedTraceAux_def (a : K) : normalizedTraceAux F K a =
    Checked.inv (Module.finrank F F⟮a⟯ : F) (isUnit_finrank_adjoin F K a) •
      trace F F⟮a⟯ (AdjoinSimple.gen F a) := rfl

private theorem normalizedTraceAux_map {E : Type*} [Field E] [Algebra F E] [Algebra.IsIntegral F E]
    (f : E →ₐ[F] K) (a : E) :
    normalizedTraceAux F K (f a) = normalizedTraceAux F E a := by
  let e := (F⟮a⟯.equivMap f).trans (equivOfEq <| Set.image_singleton ▸ adjoin_map F {a} f)
  have hunit : (isUnit_finrank_adjoin F K (f a)).unit = (isUnit_finrank_adjoin F E a).unit := by
    apply Units.ext
    simpa only [IsUnit.unit_spec] using
      congrArg (fun n : ℕ ↦ (n : F)) (LinearEquiv.finrank_eq e.toLinearEquiv).symm
  rw [normalizedTraceAux_def, normalizedTraceAux_def]
  change (↑((isUnit_finrank_adjoin F K (f a)).unit⁻¹) : F) • _ =
    (↑((isUnit_finrank_adjoin F E a).unit⁻¹) : F) • _
  rw [hunit]
  congr 1
  exact trace_eq_of_algEquiv e (AdjoinSimple.gen F a)

private theorem normalizedTraceAux_intermediateField {E : IntermediateField F K} (a : E) :
    normalizedTraceAux F K a = normalizedTraceAux F E a :=
  normalizedTraceAux_map F K E.val a

variable {K} in
private theorem normalizedTraceAux_eq_of_finiteDimensional [FiniteDimensional F K] (a : K) :
    normalizedTraceAux F K a =
      Checked.inv (Module.finrank F K : F) (isUnit_finrank F K) • trace F K a := by
  simp only [normalizedTraceAux_def, smul_eq_mul, ← div_eq_inv_mul₀]
  apply eq_div_iff.mpr
  rw [← Module.finrank_mul_finrank F F⟮a⟯ K, Nat.cast_mul, ← mul_assoc, div_mul_cancel₀]
  rw [trace_eq_trace_adjoin F a, nsmul_eq_mul, mul_comm]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The normalized trace map from an algebraic extension `K` to the base field `F`. -/
noncomputable def normalizedTrace : K →ₗ[F] F where
  toFun := normalizedTraceAux F K
  map_add' a b := by
    let E := F⟮a⟯ ⊔ F⟮b⟯
    have : FiniteDimensional F F⟮a⟯ := adjoin.finiteDimensional (IsIntegral.isIntegral a)
    have : FiniteDimensional F F⟮b⟯ := adjoin.finiteDimensional (IsIntegral.isIntegral b)
    have ha : a ∈ E := (le_sup_left : F⟮a⟯ ≤ E) <| mem_adjoin_simple_self F a
    have hb : b ∈ E := (le_sup_right : F⟮b⟯ ≤ E) <| mem_adjoin_simple_self F b
    have hab : a + b ∈ E := IntermediateField.add_mem E ha hb
    let a' : E := ⟨a, ha⟩
    let b' : E := ⟨b, hb⟩
    let ab' : E := ⟨a + b, hab⟩
    rw [normalizedTraceAux_intermediateField F K a',
      normalizedTraceAux_intermediateField F K b',
      normalizedTraceAux_intermediateField F K ab',
      normalizedTraceAux_eq_of_finiteDimensional F a',
      normalizedTraceAux_eq_of_finiteDimensional F b',
      normalizedTraceAux_eq_of_finiteDimensional F ab',
      ← smul_add, ← map_add, AddMemClass.mk_add_mk]
  map_smul' m a := by
    dsimp only [AddHom.toFun_eq_coe, AddHom.coe_mk, RingHom.id_apply]
    let E := F⟮a⟯
    have : FiniteDimensional F F⟮a⟯ := adjoin.finiteDimensional (IsIntegral.isIntegral a)
    have ha : a ∈ E := mem_adjoin_simple_self F a
    have hma : m • a ∈ E := smul_mem E ha
    let a' : E := ⟨a, ha⟩
    let ma' : E := ⟨m • a, hma⟩
    rw [normalizedTraceAux_intermediateField F K a',
      normalizedTraceAux_intermediateField F K ma',
      normalizedTraceAux_eq_of_finiteDimensional F a',
      normalizedTraceAux_eq_of_finiteDimensional F ma',
      smul_comm, ← map_smul _ m, SetLike.mk_smul_mk]

theorem normalizedTrace_def (a : K) : normalizedTrace F K a =
    Checked.inv (Module.finrank F F⟮a⟯ : F) (by exact isUnit_finrank_adjoin F K a) •
      trace F F⟮a⟯ (AdjoinSimple.gen F a) :=
  rfl

variable {K} in
/-- Normalized trace defined purely in terms of the degree and the next coefficient of the minimal
polynomial. Could be an alternative definition but it is harder to work with linearity. -/
theorem normalizedTrace_minpoly (a : K) :
    normalizedTrace F K a = Checked.inv ((minpoly F a).natDegree : F) (by
      rw [← adjoin.finrank (IsIntegral.isIntegral a)]
      exact isUnit_finrank_adjoin F K a) • -(minpoly F a).nextCoeff := by
  have ha : IsIntegral F a := IsIntegral.isIntegral a
  rw [normalizedTrace_def, trace_adjoinSimpleGen ha]
  congr 1
  let d : {x : F // IsUnit x} := ⟨(Module.finrank F F⟮a⟯ : F), isUnit_finrank_adjoin F K a⟩
  let e : {x : F // IsUnit x} := ⟨((minpoly F a).natDegree : F), by
    rw [← adjoin.finrank ha]
    exact isUnit_finrank_adjoin F K a⟩
  have h : d = e := Subtype.ext (congrArg (fun n : ℕ ↦ (n : F)) (adjoin.finrank ha))
  exact congrArg (fun d : {x : F // IsUnit x} ↦ Checked.inv d.val d.property) h

variable {F} in
theorem normalizedTrace_self_apply (a : F) : normalizedTrace F F a = a := by
  dsimp [normalizedTrace]
  rw [normalizedTraceAux_eq_of_finiteDimensional F a, trace_self_apply]
  simp [Module.finrank_self]

@[simp]
theorem normalizedTrace_self : normalizedTrace F F = LinearMap.id :=
  LinearMap.ext normalizedTrace_self_apply

variable {K} in
theorem normalizedTrace_eq_of_finiteDimensional_apply [FiniteDimensional F K] (a : K) :
    normalizedTrace F K a =
      Checked.inv (Module.finrank F K : F) (by exact isUnit_finrank F K) • trace F K a :=
  normalizedTraceAux_eq_of_finiteDimensional F a

theorem normalizedTrace_eq_of_finiteDimensional [FiniteDimensional F K] :
    normalizedTrace F K =
      Checked.inv (Module.finrank F K : F) (by exact isUnit_finrank F K) • trace F K :=
  LinearMap.ext <| normalizedTrace_eq_of_finiteDimensional_apply F

/-- The normalized trace transfers via (injective) maps. -/
@[simp]
theorem normalizedTrace_map {E : Type*} [Field E] [Algebra F E] [Algebra.IsIntegral F E]
    (f : E →ₐ[F] K) (a : E) : normalizedTrace F K (f a) = normalizedTrace F E a :=
  normalizedTraceAux_map F K f a

/-- The normalized trace transfers via restriction to a subextension. -/
theorem normalizedTrace_intermediateField {E : IntermediateField F K} (a : E) :
    normalizedTrace F K a = normalizedTrace F E a :=
  normalizedTraceAux_intermediateField F K a

section IsScalarTower

variable (F E K : Type*) [Field F] [Field E] [Field K]
variable [Algebra F E] [Algebra E K] [Algebra F K] [IsScalarTower F E K]
variable [Algebra.IsIntegral F E] [Algebra.IsIntegral F K]
variable [CharZero F]

@[simp]
theorem normalizedTrace_algebraMap_apply (a : E) :
    normalizedTrace F K (algebraMap E K a) = normalizedTrace F E a :=
  normalizedTrace_map F K (IsScalarTower.toAlgHom F E K) a

@[simp]
theorem normalizedTrace_algebraMap :
    normalizedTrace F K ∘ₗ Algebra.linearMap E K = normalizedTrace F E :=
  LinearMap.ext <| normalizedTrace_algebraMap_apply F E K

omit [Algebra.IsIntegral F E] in
/-- If all the coefficients of `minpoly E a` are in `F`, then the normalized trace of `a` from `K`
to `E` equals the normalized trace of `a` from `K` to `F`. -/
theorem normalizedTrace_algebraMap_of_lifts [CharZero E] [Algebra.IsIntegral E K] (a : K)
    (h : minpoly E a ∈ Polynomial.lifts (algebraMap F E)) :
    algebraMap F E (normalizedTrace F K a) = normalizedTrace E K a := by
  have ha : IsIntegral F a := IsIntegral.isIntegral a
  simp [normalizedTrace_minpoly F a, normalizedTrace_minpoly E a, ← minpoly.map_algebraMap ha h,
    (minpoly F a).nextCoeff_map_eq, map_mul, map_neg]

set_option backward.isDefEq.respectTransparency false in
/- An auxiliary result to prove `normalizedTrace_trans_apply`. It differs from
`normalizedTrace_trans_apply` only by the extra assumption about finiteness of `E` over `F`. -/
private theorem normalizedTrace_trans_apply_aux [FiniteDimensional F E] [Algebra.IsIntegral E K]
    [CharZero E] (a : K) :
    normalizedTrace F E (normalizedTrace E K a) = normalizedTrace F K a := by
  have : FiniteDimensional E E⟮a⟯ :=
    IntermediateField.adjoin.finiteDimensional (IsIntegral.isIntegral a)
  let E' := E⟮a⟯.restrictScalars F
  have : FiniteDimensional F E' := Module.Finite.trans E E⟮a⟯
  let a' : E' := AdjoinSimple.gen E a
  let d : F := Module.finrank E E⟮a⟯
  let e : F := Module.finrank F E
  have hd : IsUnit d :=
    (Nat.cast_ne_zero.mpr (Module.finrank_pos (R := E) (M := E⟮a⟯)).ne').isUnit
  have he : IsUnit e := isUnit_finrank F E
  have hdegree : (Module.finrank F E' : F) = d * e := by
    change (Module.finrank F E⟮a⟯ : F) = (Module.finrank E E⟮a⟯ : F) * (Module.finrank F E : F)
    rw [mul_comm, ← Nat.cast_mul, Module.finrank_mul_finrank F E E⟮a⟯]
  have hcoeff : d⁻¹ * e⁻¹ = Checked.inv (Module.finrank F E' : F) (isUnit_finrank F E') := by
    apply mul_right_cancel₀ (isUnit_finrank F E').ne_zero
    rw [inv_mul_cancel₀, hdegree]
    calc
      _ = (d⁻¹ * d) * (e⁻¹ * e) := by ring
      _ = 1 := by simp only [inv_mul_cancel₀, one_mul]
  rw [normalizedTrace_def E K, inv_natCast_smul_eq (R := E) (S := F), map_smul,
    normalizedTrace_eq_of_finiteDimensional F E, LinearMap.smul_apply, ← smul_assoc]
  conv_lhs => arg 1; rw [smul_eq_mul]
  change (d⁻¹ * e⁻¹) • trace F E (trace E E⟮a⟯ (AdjoinSimple.gen E a)) = _
  rw [hcoeff, trace_trace]
  change Checked.inv (Module.finrank F E' : F) (isUnit_finrank F E') • trace F E' a' =
    normalizedTrace F K (a' : K)
  rw [← normalizedTrace_eq_of_finiteDimensional_apply F,
    ← normalizedTrace_intermediateField F K a']

/-- For a tower `K / E / F` of algebraic extensions, the normalized trace from `K` to `E` composed
with the normalized trace from `E` to `F` equals the normalized trace from `K` to `F`. -/
theorem normalizedTrace_trans_apply [Algebra.IsIntegral E K] [CharZero E] (a : K) :
    normalizedTrace F E (normalizedTrace E K a) = normalizedTrace F K a :=
  let S : Set E := (minpoly E a).coeffs
  let E₀ := IntermediateField.adjoin F S
  have : FiniteDimensional F E₀ := IntermediateField.finiteDimensional_adjoin
    fun x _ ↦ Algebra.IsIntegral.isIntegral x
  have : Algebra.IsIntegral E₀ E := IsIntegral.tower_top F
  have : Algebra.IsIntegral E₀ K := IsIntegral.trans E
  have hsub : S ⊆ (algebraMap E₀ E).range :=
    Subalgebra.range_algebraMap E₀.toSubalgebra ▸ IntermediateField.subset_adjoin F S
  have hlifts := (Polynomial.lifts_iff_coeffs_subset_range _).mpr hsub
  (normalizedTrace_trans_apply_aux F E₀ K _ ▸
    normalizedTrace_algebraMap_apply F E₀ E _ ▸
    congrArg (normalizedTrace F E) (normalizedTrace_algebraMap_of_lifts E₀ E K a hlifts)).symm

@[simp]
theorem normalizedTrace_trans [Algebra.IsIntegral E K] [CharZero E] :
    normalizedTrace F E ∘ₗ normalizedTrace E K = normalizedTrace F K :=
  LinearMap.ext <| normalizedTrace_trans_apply F E K

end IsScalarTower

theorem normalizedTrace_algebraMap_apply_eq_self (a : F) :
    normalizedTrace F K (algebraMap F K a) = a := by simp

/-- The normalized trace map is a left inverse of the algebra map. -/
theorem normalizedTrace_algebraMap_eq_id :
    normalizedTrace F K ∘ₗ Algebra.linearMap F K = LinearMap.id :=
  LinearMap.ext <| normalizedTrace_algebraMap_apply_eq_self F K

/-- The normalized trace commutes with (injective) maps. -/
@[simp]
theorem normalizedTrace_comp_algHom {E : Type*} [Field E] [Algebra F E] [Algebra.IsIntegral F E]
    (f : E →ₐ[F] K) : normalizedTrace F K ∘ₗ f = normalizedTrace F E :=
  LinearMap.ext <| normalizedTrace_map F K f

theorem normalizedTrace_surjective : Function.Surjective (normalizedTrace F K) :=
  fun a ↦ ⟨algebraMap F K a, normalizedTrace_algebraMap_apply_eq_self F K a⟩

/-- The normalized trace map is non-trivial. -/
theorem normalizedTrace_ne_zero : normalizedTrace F K ≠ 0 :=
  let ⟨a, ha⟩ := normalizedTrace_surjective F K 1
  DFunLike.ne_iff.mpr <| ⟨a, ha ▸ one_ne_zero⟩

end Algebra
