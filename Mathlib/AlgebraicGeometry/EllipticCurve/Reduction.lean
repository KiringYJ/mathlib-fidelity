/-
Copyright (c) 2025 Bryan Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Wang
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
public import Mathlib.GroupTheory.ArchimedeanDensely

/-!
# Reduction of Weierstrass curves over local fields

This file defines reduction of Weierstrass curves over local fields, or more generally,
fraction fields of discrete valuation rings.

## Main definitions

* `IsIntegral`: a predicate expressing that a given Weierstrass equation
  has integral coefficients.
* `IsMinimal`: a predicate expressing that a given Weierstrass equation
  has minimal valuation of discriminant among all isomorphic integral Weierstrass equations.
* `reduction`: the reduction of a Weierstrass curve given by a minimal Weierstrass equation,
  which is a Weierstrass curve over the residue field.
* `IsGoodReduction`: a predicate expressing that a given minimal Weierstrass equation
  has valuation of its discriminant equal to zero.
* `nodePolynomial`: the polynomial whose splitting over the residue field defines split
  multiplicative reduction.

## Main statements

* `exists_isIntegral`: any Weierstrass curve is isomorphic to one given by
  an integral Weierstrass equation.
* `exists_isMinimal`: any Weierstrass curve is isomorphic to one given by
  a minimal Weierstrass equation.
* `variableChange_integral_of_isMinimal`: the minimal Weierstrass equations of an elliptic curve
  differ by changes of variables with coefficients in the valuation ring and `u` a unit.
* `reduction_variableChange_baseChange`, `hasGoodReduction_iff_of_isMinimal`,
  `hasSplitMultiplicativeReduction_iff_of_isMinimal`: the reduction and its type do not depend on
  the choice of minimal Weierstrass equation.

## References

* [J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, weierstrass equation, minimal weierstrass equation, reduction
-/

@[expose] public section

namespace WeierstrassCurve

section Integral

variable (R : Type*) [CommRing R]
variable {K : Type*} [Field K] [Algebra R K]

/-- A Weierstrass equation over the fraction field `K` is integral if
it has coefficients in the ring `R`. -/
@[mk_iff]
class IsIntegral (W : WeierstrassCurve K) : Prop where
  integral : ∃ W_int : WeierstrassCurve R, W = W_int⁄K

/-- An integral model of an integral Weierstrass curve. -/
noncomputable def integralModel (W : WeierstrassCurve K) [hW : IsIntegral R W] :
    WeierstrassCurve R :=
  hW.integral.choose

variable (W : WeierstrassCurve K) [hW : IsIntegral R W]

lemma baseChange_integralModel_eq (W : WeierstrassCurve K) [hW : IsIntegral R W] :
    (integralModel R W)⁄K = W :=
  hW.integral.choose_spec.symm

lemma isIntegral_of_exists_lift {W : WeierstrassCurve K}
    (h₁ : ∃ r₁, (algebraMap R K) r₁ = W.a₁)
    (h₂ : ∃ r₂, (algebraMap R K) r₂ = W.a₂)
    (h₃ : ∃ r₃, (algebraMap R K) r₃ = W.a₃)
    (h₄ : ∃ r₄, (algebraMap R K) r₄ = W.a₄)
    (h₆ : ∃ r₆, (algebraMap R K) r₆ = W.a₆) :
    IsIntegral R W := by
  use ⟨h₁.choose, h₂.choose, h₃.choose, h₄.choose, h₆.choose⟩
  ext
  all_goals simp only [baseChange, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆]
  · apply h₁.choose_spec.symm
  · apply h₂.choose_spec.symm
  · apply h₃.choose_spec.symm
  · apply h₄.choose_spec.symm
  · apply h₆.choose_spec.symm

lemma Δ_integral_of_isIntegral (W : WeierstrassCurve K) [IsIntegral R W] :
    ∃ r : R, algebraMap R K r = W.Δ := by
  obtain ⟨W_int, hW_int⟩ : ∃ W_int : WeierstrassCurve R, W = W_int⁄K :=
    IsIntegral.integral
  use W_int.Δ
  rw [hW_int, baseChange, map_Δ]

lemma integralModel_a₁_eq (W : WeierstrassCurve K) [hW : IsIntegral R W] :
    algebraMap R K (integralModel R W).a₁ = W.a₁ := by
  conv_rhs => rw [← baseChange_integralModel_eq R W]
  simp [baseChange]

lemma integralModel_a₂_eq (W : WeierstrassCurve K) [hW : IsIntegral R W] :
    algebraMap R K (integralModel R W).a₂ = W.a₂ := by
  conv_rhs => rw [← baseChange_integralModel_eq R W]
  simp [baseChange]

lemma integralModel_a₃_eq (W : WeierstrassCurve K) [hW : IsIntegral R W] :
    algebraMap R K (integralModel R W).a₃ = W.a₃ := by
  conv_rhs => rw [← baseChange_integralModel_eq R W]
  simp [baseChange]

lemma integralModel_a₄_eq (W : WeierstrassCurve K) [hW : IsIntegral R W] :
    algebraMap R K (integralModel R W).a₄ = W.a₄ := by
  conv_rhs => rw [← baseChange_integralModel_eq R W]
  simp [baseChange]

lemma integralModel_a₆_eq (W : WeierstrassCurve K) [hW : IsIntegral R W] :
    algebraMap R K (integralModel R W).a₆ = W.a₆ := by
  conv_rhs => rw [← baseChange_integralModel_eq R W]
  simp [baseChange]

lemma integralModel_b₂_eq (W : WeierstrassCurve K) [hW : IsIntegral R W] :
    algebraMap R K (integralModel R W).b₂ = W.b₂ := by
  conv_rhs => rw [← baseChange_integralModel_eq R W]
  simp [baseChange]

lemma integralModel_b₄_eq (W : WeierstrassCurve K) [hW : IsIntegral R W] :
    algebraMap R K (integralModel R W).b₄ = W.b₄ := by
  conv_rhs => rw [← baseChange_integralModel_eq R W]
  simp [baseChange]

lemma integralModel_b₆_eq (W : WeierstrassCurve K) [hW : IsIntegral R W] :
    algebraMap R K (integralModel R W).b₆ = W.b₆ := by
  conv_rhs => rw [← baseChange_integralModel_eq R W]
  simp [baseChange]

lemma integralModel_b₈_eq (W : WeierstrassCurve K) [hW : IsIntegral R W] :
    algebraMap R K (integralModel R W).b₈ = W.b₈ := by
  conv_rhs => rw [← baseChange_integralModel_eq R W]
  simp [baseChange]

lemma integralModel_c₄_eq (W : WeierstrassCurve K) [hW : IsIntegral R W] :
    algebraMap R K (integralModel R W).c₄ = W.c₄ := by
  conv_rhs => rw [← baseChange_integralModel_eq R W]
  simp [baseChange]

lemma integralModel_c₆_eq (W : WeierstrassCurve K) [hW : IsIntegral R W] :
    algebraMap R K (integralModel R W).c₆ = W.c₆ := by
  conv_rhs => rw [← baseChange_integralModel_eq R W]
  simp [baseChange]

lemma integralModel_Δ_eq (W : WeierstrassCurve K) [hW : IsIntegral R W] :
    algebraMap R K (integralModel R W).Δ = W.Δ := by
  conv_rhs => rw [← baseChange_integralModel_eq R W]
  simp [baseChange]

/-- A change of variables with coefficients in `R` preserves integrality. -/
instance isIntegral_variableChange_baseChange (W : WeierstrassCurve K) [IsIntegral R W]
    (CR : VariableChange R) : IsIntegral R (CR.baseChange K • W) :=
  ⟨CR • integralModel R W, by
    conv_lhs => rw [← baseChange_integralModel_eq R W]
    exact map_variableChange (integralModel R W) CR (algebraMap R K)⟩

/-- The integral model of a Weierstrass equation after a change of variables with coefficients
in `R` is the corresponding change of variables of its integral model. -/
lemma integralModel_variableChange_baseChange [FaithfulSMul R K] (W : WeierstrassCurve K)
    [IsIntegral R W] (CR : VariableChange R) :
    integralModel R (CR.baseChange K • W) = CR • integralModel R W := by
  refine map_injective (FaithfulSMul.algebraMap_injective R K) ?_
  change (integralModel R (CR.baseChange K • W))⁄K = (CR • integralModel R W).map (algebraMap R K)
  rw [baseChange_integralModel_eq, ← map_variableChange]
  exact congrArg (CR.baseChange K • ·) (baseChange_integralModel_eq R W).symm

variable [IsDomain R] [ValuationRing R] [IsFractionRing R K]

open ValuationRing

theorem exists_isIntegral (W : WeierstrassCurve K) :
    ∃ C : VariableChange K, IsIntegral R (C • W) := by
  let l₀ := [W.a₁, W.a₂, W.a₃, W.a₄, W.a₆]
  let l := l₀.map (fun a ↦ valuation R K a)
  let lmax : ValueGroup R K :=
    l.maximum_of_length_pos (by simp [l₀, l])
  have hlmax_mem : lmax ∈ l :=
    List.maximum_of_length_pos_mem (by simp [l₀, l])
  have hlmax : ∀ v ∈ l, v ≤ lmax := fun v hv ↦
    List.le_maximum_of_length_pos_of_mem hv (by simp [l₀, l])
  by_cases hlmax_le_1 : lmax ≤ 1
  · use ⟨1, 0, 0, 0⟩
    apply isIntegral_of_exists_lift R
    all_goals simpa [← mem_integer_iff, variableChange_def, Valuation.mem_integer_iff]
      using (hlmax _ (by simp [l₀, l])).trans hlmax_le_1
  · have hlmax_ge_1 : lmax ≥ 1 := le_of_not_ge hlmax_le_1
    have h : ∃ a : K, valuation R K a = lmax := by
      let i : ℕ := l.idxOf lmax
      have hi : i < l.length := List.idxOf_lt_length_of_mem hlmax_mem
      use l₀[i]
      have hi₁ : (valuation R K) l₀[i] = l[i] := by simp [l]
      simpa only [hi₁] using (List.getElem_idxOf hi)
    choose a ha using h
    have ha₀ : a ≠ 0 := by
      by_contra ha₀; simp only [ha₀, map_zero] at ha
      exact (ha ▸ hlmax_le_1) zero_le_one
    use ⟨Units.mk0 a ha₀, 0, 0, 0⟩
    apply isIntegral_of_exists_lift R
    all_goals
      apply (mem_integer_iff _ _ _).mp
      simp only [variableChange_def, Units.val_inv_eq_inv_val, Units.val_mk0, mul_zero, add_zero,
        inv_pow, zero_mul, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      apply (Valuation.mem_integer_iff _ _).mpr
      simp only [map_mul, map_inv₀, map_pow, ha]
      refine inv_mul_le_one_of_le₀ ?_ zero_le
      refine (hlmax _ (by simp [l₀, l])).trans ?_
    any_goals
      apply le_self_pow hlmax_ge_1.le
      linarith
    rfl

end Integral

section UIntegral

open Polynomial

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {K : Type*} [Field K]
  [Algebra R K] [IsFractionRing R K] {W W' : WeierstrassCurve K} [IsIntegral R W] [IsIntegral R W']
  {CK : VariableChange K} (hCK : CK • W = W') {u : Rˣ} (hu : algebraMap R K u = CK.u)

include hCK hu

lemma r_integral_of_u_integral : ∃ r : R, algebraMap R K r = CK.r := by
  refine IsIntegrallyClosed.isIntegral_iff.mp ⟨X ^ 4 - C (integralModel R W).b₄ * X ^ 2 -
    C (u ^ 6 * (integralModel R W').b₆ + 2 * (integralModel R W).b₆) * X -
    C ((integralModel R W).b₈ - u ^ 8 * (integralModel R W').b₈), by monicity!, ?_⟩
  simp [map_ofNat, hu, ← hCK, integralModel_b₄_eq, integralModel_b₆_eq,
    integralModel_b₈_eq, variableChange_b₆, variableChange_b₈]
  ring1

lemma s_integral_of_u_integral : ∃ s : R, algebraMap R K s = CK.s := by
  rcases r_integral_of_u_integral hCK hu with ⟨r, hr⟩
  refine IsIntegrallyClosed.isIntegral_iff.mp ⟨X ^ 2 + C (integralModel R W).a₁ * X +
    C (u ^ 2 * (integralModel R W').a₂ - (integralModel R W).a₂ - 3 * r), by monicity!, ?_⟩
  simp [map_ofNat, hu, hr, ← hCK, integralModel_a₁_eq, integralModel_a₂_eq,
    variableChange_a₂]
  ring1

lemma t_integral_of_u_integral : ∃ t : R, algebraMap R K t = CK.t := by
  rcases r_integral_of_u_integral hCK hu with ⟨r, hr⟩
  refine IsIntegrallyClosed.isIntegral_iff.mp ⟨X ^ 2 +
    C ((integralModel R W).a₃ + r * (integralModel R W).a₁) * X +
    C (u ^ 6 * (integralModel R W').a₆ - (integralModel R W).a₆ - r * (integralModel R W).a₄
      - r ^ 2 * (integralModel R W).a₂ - r ^ 3), by monicity!, ?_⟩
  simp [hu, hr, ← hCK, integralModel_a₁_eq, integralModel_a₂_eq, integralModel_a₃_eq,
    integralModel_a₄_eq, integralModel_a₆_eq, variableChange_a₆]
  ring1

/-- A variable change over the fraction field between integral Weierstrass equations descends to the
base ring if its `u` coefficient descends to a unit of the base ring. -/
theorem variableChange_integral_of_u_integral : ∃ CR : VariableChange R, CR.baseChange K = CK := by
  rcases r_integral_of_u_integral hCK hu, s_integral_of_u_integral hCK hu,
    t_integral_of_u_integral hCK hu with ⟨⟨r, hr⟩, ⟨s, hs⟩, ⟨t, ht⟩⟩
  exact ⟨⟨u, r, s, t⟩, by ext <;> simpa⟩

end UIntegral

section NodePolynomial

open Polynomial

variable {R : Type*} [CommRing R]

/-- The polynomial `c₄ T ^ 2 + a₁ c₄ T - (54 b₆ - 3 b₂ b₄ + a₂ c₄)` of a Weierstrass curve.
A minimal Weierstrass equation with multiplicative reduction has split multiplicative reduction if
and only if this polynomial of its integral model splits over the residue field.

To see how this expression arises, note that a singular point `(x₀, y₀)` has second order Taylor
expansion `(Y - y₀)^2 + a_1(X - x₀)(Y - y₀) - (3x₀ + a_2)(X - x₀)^2`, where
`c₄ x₀ = 18 b₆ - b₂ b₄`. When `c₄` is invertible, the singular point is a node, and the roots of
this polynomial are the slopes of the tangent lines there. -/
noncomputable def nodePolynomial (W : WeierstrassCurve R) : R[X] :=
  C W.c₄ * X ^ 2 + C (W.a₁ * W.c₄) * X - C (54 * W.b₆ - 3 * W.b₂ * W.b₄ + W.a₂ * W.c₄)

variable (D : VariableChange R) (W : WeierstrassCurve R)

/-- Under a change of variables `(u, r, s, t)`, the polynomial `nodePolynomial` transforms by the
substitution `T ↦ uT + s` up to the factor `u ^ 6`. -/
lemma variableChange_nodePolynomial :
    C ((D.u : R) ^ 6) * (D • W).nodePolynomial =
      W.nodePolynomial.comp (C (D.u : R) * X + C D.s) := by
  have h₂ : (D.u : R) ^ 6 * (D • W).c₄ = W.c₄ * D.u ^ 2 := by
    rw [variableChange_c₄]
    linear_combination (D.u : R) ^ 2 * W.c₄ * pow_mul_pow_eq_one 4 D.u.mul_inv
  have h₁ : (D.u : R) ^ 6 * ((D • W).a₁ * (D • W).c₄) = (W.a₁ + 2 * D.s) * W.c₄ * D.u := by
    rw [variableChange_a₁, variableChange_c₄]
    linear_combination (W.a₁ + 2 * D.s) * W.c₄ * D.u * pow_mul_pow_eq_one 5 D.u.mul_inv
  have h₀ : (D.u : R) ^ 6 *
      (54 * (D • W).b₆ - 3 * (D • W).b₂ * (D • W).b₄ + (D • W).a₂ * (D • W).c₄) =
        54 * W.b₆ - 3 * W.b₂ * W.b₄ + W.a₂ * W.c₄ - D.s * W.a₁ * W.c₄ - D.s ^ 2 * W.c₄ := by
    rw [variableChange_b₆, variableChange_b₂, variableChange_b₄, variableChange_a₂,
      variableChange_c₄, c₄]
    linear_combination (54 * (W.b₆ + 2 * D.r * W.b₄ + D.r ^ 2 * W.b₂ + 4 * D.r ^ 3) -
      3 * (W.b₂ + 12 * D.r) * (W.b₄ + D.r * W.b₂ + 6 * D.r ^ 2) +
        (W.a₂ - D.s * W.a₁ + 3 * D.r - D.s ^ 2) * (W.b₂ ^ 2 - 24 * W.b₄)) *
          pow_mul_pow_eq_one 6 D.u.mul_inv
  rw [nodePolynomial, nodePolynomial, mul_sub, mul_add, ← mul_assoc, ← mul_assoc, ← C_mul,
    ← C_mul, ← C_mul, h₂, h₁, h₀]
  simp only [sub_comp, add_comp, mul_comp, C_comp, X_comp, pow_comp, ofNat_comp, map_mul, map_add,
    map_sub, map_pow, map_ofNat]
  ring1

/-- Whether `nodePolynomial` splits over a field is invariant under a change of variables. -/
lemma splits_map_nodePolynomial_variableChange_iff {k : Type*} [Field k] (φ : R →+* k) :
    ((D • W).nodePolynomial.map φ).Splits ↔ (W.nodePolynomial.map φ).Splits := by
  have hu : φ D.u ≠ 0 := (D.u.isUnit.map φ).ne_zero
  rw [← splits_mul_iff_right (C_ne_zero.mpr (pow_ne_zero 6 hu)) (Splits.C _), ← map_pow,
    ← map_C φ, ← Polynomial.map_mul, variableChange_nodePolynomial, Polynomial.map_comp,
    Polynomial.map_add, Polynomial.map_mul, map_C, map_X, map_C,
    ← splits_iff_comp_splits_of_degree_eq_one (degree_linear hu)]

end NodePolynomial

section Minimal

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

open WithZero Multiplicative
open IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum

open scoped Classical in
/-- The valuation of the discriminant of a Weierstrass curve `W`,
which is at most 1 if `W` is integral. Zero otherwise. -/
noncomputable def valuation_Δ_aux (W : WeierstrassCurve K) :
    { v : ℤᵐ⁰ // v ≤ 1 } :=
  if h : IsIntegral R W then
    ⟨valuation K (maximalIdeal R) W.Δ, by
      choose r hr using Δ_integral_of_isIntegral R W
      rw [← hr]
      exact valuation_le_one (maximalIdeal R) r⟩
  else ⟨⊥, bot_le⟩

lemma valuation_Δ_aux_eq_of_isIntegral (W : WeierstrassCurve K) [hW : IsIntegral R W] :
    valuation_Δ_aux R W = valuation K (maximalIdeal R) W.Δ := by
  simp [valuation_Δ_aux, hW]

/-- A Weierstrass equation over the fraction field `K` is minimal if the (multiplicative) valuation
of its discriminant is maximal among all isomorphic integral Weierstrass equations.
We still use 'minimal' for the naming, so as to standardize the naming with Silverman's book. -/
@[mk_iff]
class IsMinimal (W : WeierstrassCurve K) : Prop where
  val_Δ_maximal :
    MaximalFor
      (fun (C : VariableChange K) ↦ IsIntegral R (C • W))
      (fun (C : VariableChange K) ↦ valuation_Δ_aux R (C • W))
      (1 : VariableChange K)

omit [IsFractionRing R K] in
instance {W : WeierstrassCurve K} [IsMinimal R W] :
    IsIntegral R W := by simpa using IsMinimal.val_Δ_maximal.1

theorem exists_isMinimal (W : WeierstrassCurve K) :
    ∃ C : VariableChange K, IsMinimal R (C • W) := by
  obtain ⟨C, hC⟩ := exists_maximalFor_of_wellFoundedGT
    (fun (C : VariableChange K) ↦ IsIntegral R (C • W))
    (fun (C : VariableChange K) ↦ valuation_Δ_aux R (C • W))
    (exists_isIntegral R W)
  refine ⟨C, ⟨⟨by simp only [one_smul, hC.1], ?_⟩⟩⟩
  intro j hj; rw [← smul_assoc] at hj
  let h := hC.2 hj
  simp_all only [one_smul]
  rw [← smul_assoc]
  exact h

/-- A minimal Weierstrass equation for a given Weierstrass curve over `K`. -/
noncomputable def minimal (W : WeierstrassCurve K) : WeierstrassCurve K :=
  (W.exists_isMinimal R).choose • W

instance {W : WeierstrassCurve K} :
    IsMinimal R (W.minimal R) := (W.exists_isMinimal R).choose_spec

instance (W : WeierstrassCurve K) [W.IsElliptic] : (W.minimal R).IsElliptic :=
  inferInstanceAs ((W.exists_isMinimal R).choose • W).IsElliptic

/-- A change of variables with coefficients in `R` does not change the valuation of the
discriminant. -/
lemma valuation_Δ_aux_variableChange_baseChange (W : WeierstrassCurve K) [IsIntegral R W]
    (CR : VariableChange R) :
    valuation_Δ_aux R (CR.baseChange K • W) = valuation_Δ_aux R W := by
  apply Subtype.ext
  rw [valuation_Δ_aux_eq_of_isIntegral, valuation_Δ_aux_eq_of_isIntegral, variableChange_Δ,
    map_mul, map_pow, Units.val_inv_eq_inv_val, map_inv₀]
  have : valuation K (maximalIdeal R) (algebraMap R K CR.u) = 1 :=
    ((maximalIdeal R).valuation_eq_one_iff_notMem (K := K)).mpr
      (IsLocalRing.notMem_maximalIdeal.mpr CR.u.isUnit)
  simp [VariableChange.baseChange, VariableChange.map, this]

/-- A change of variables with coefficients in `R` preserves minimality. -/
instance isMinimal_variableChange_baseChange (W : WeierstrassCurve K) [IsMinimal R W]
    (CR : VariableChange R) : IsMinimal R (CR.baseChange K • W) where
  val_Δ_maximal := by
    refine ⟨by simp only [one_smul]; infer_instance, fun j hj hle ↦ ?_⟩
    have hj' : IsIntegral R ((j * CR.baseChange K) • W) := by rwa [mul_smul]
    have key := (IsMinimal.val_Δ_maximal (R := R) (W := W)).2 hj'
    simp only [one_smul, mul_smul, valuation_Δ_aux_variableChange_baseChange] at hle key ⊢
    exact key hle

section VariableChange

/-! ### Uniqueness of minimal Weierstrass equations -/

variable {W W' : WeierstrassCurve K} [IsMinimal R W] [IsMinimal R W'] {C : VariableChange K}
  (hC : C • W = W')

include hC

/-- Two minimal Weierstrass equations for the same curve have discriminants of the same
valuation. -/
lemma valuation_Δ_eq_of_isMinimal :
    valuation K (maximalIdeal R) W'.Δ = valuation K (maximalIdeal R) W.Δ := by
  have h₁ := (IsMinimal.val_Δ_maximal (R := R) (W := W)).2
    (show IsIntegral R (C • W) by rw [hC]; infer_instance)
  have h₂ := (IsMinimal.val_Δ_maximal (R := R) (W := W')).2
    (show IsIntegral R (C⁻¹ • W') by rw [← hC, inv_smul_smul]; infer_instance)
  simp only [one_smul, hC] at h₁
  simp only [one_smul] at h₂
  rw [← hC, inv_smul_smul, hC] at h₂
  have key : valuation_Δ_aux R W' = valuation_Δ_aux R W :=
    (le_total _ _).elim (fun h ↦ le_antisymm h (h₂ h)) fun h ↦ le_antisymm (h₁ h) h
  have := congrArg Subtype.val key
  rwa [valuation_Δ_aux_eq_of_isIntegral, valuation_Δ_aux_eq_of_isIntegral] at this

/-- The `u` coefficient of a change of variables between two minimal Weierstrass equations of an
elliptic curve has valuation one. -/
lemma valuation_u_eq_one_of_isMinimal [W.IsElliptic] : valuation K (maximalIdeal R) C.u = 1 := by
  have h := valuation_Δ_eq_of_isMinimal R hC
  rw [← hC, variableChange_Δ, map_mul, map_pow, Units.val_inv_eq_inv_val, map_inv₀,
    mul_eq_right₀ ((Valuation.ne_zero_iff _).mpr W.isUnit_Δ.ne_zero), inv_pow, inv_eq_one] at h
  exact (pow_eq_one_iff_of_nonneg zero_le (by norm_num)).mp h

/-- The `u` coefficient of a change of variables between two minimal Weierstrass equations of an
elliptic curve is the image of a unit of the valuation ring. -/
lemma exists_algebraMap_eq_u_of_isMinimal [W.IsElliptic] : ∃ u : Rˣ, algebraMap R K u = C.u := by
  obtain ⟨u, hu⟩ := associated_of_valuation_eq (A := R) (1 : K) (C.u : K)
    (by rw [map_one, valuation_u_eq_one_of_isMinimal R hC])
  exact ⟨u, by simpa [Units.smul_def, Algebra.smul_def] using hu⟩

/-- A change of variables between two minimal Weierstrass equations of an elliptic curve has
coefficients in the valuation ring, with `u` a unit: minimal Weierstrass equations are unique up
to such changes of variables. -/
theorem variableChange_integral_of_isMinimal [W.IsElliptic] :
    ∃ CR : VariableChange R, CR.baseChange K = C :=
  have ⟨_, hu⟩ := exists_algebraMap_eq_u_of_isMinimal R hC
  variableChange_integral_of_u_integral hC hu

/-- Two minimal Weierstrass equations for the same elliptic curve have `c₄` invariants of the same
valuation. -/
lemma valuation_c₄_eq_of_isMinimal [W.IsElliptic] :
    valuation K (maximalIdeal R) W'.c₄ = valuation K (maximalIdeal R) W.c₄ := by
  rw [← hC, variableChange_c₄, map_mul, map_pow, Units.val_inv_eq_inv_val, map_inv₀,
    valuation_u_eq_one_of_isMinimal R hC, inv_one, one_pow, one_mul]

end VariableChange

end Minimal

section Reduction

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

open IsDiscreteValuationRing IsLocalRing IsDedekindDomain.HeightOneSpectrum

/-- The reduction of a Weierstrass curve over `K` given by a minimal Weierstrass equation,
which is a Weierstrass curve over the residue field of `R`. -/
noncomputable def reduction (W : WeierstrassCurve K) [IsMinimal R W] :
    WeierstrassCurve (ResidueField R) :=
  (integralModel R W).map (residue R)

/-- A minimal Weierstrass equation has good reduction if and only if
the valuation of its discriminant is 1. -/
@[mk_iff]
class HasGoodReduction (W : WeierstrassCurve K) : Prop extends IsMinimal R W where
  goodReduction : valuation K (maximalIdeal R) W.Δ = 1

@[deprecated (since := "2026-03-04")] alias IsGoodReduction := HasGoodReduction

lemma hasGoodReduction_iff_isElliptic_reduction {W : WeierstrassCurve K} [hW : IsMinimal R W] :
    HasGoodReduction R W ↔ (W.reduction R).IsElliptic := by
  refine Iff.trans ?_ (W.reduction R).isElliptic_iff.symm
  simp only [reduction, map_Δ, isUnit_iff_ne_zero, ne_eq, residue_eq_zero_iff]
  have h :
      ¬(valuation K (maximalIdeal R) (algebraMap R K (integralModel R W).Δ) < 1)
      ↔ (integralModel R W).Δ ∉ IsLocalRing.maximalIdeal R :=
    not_iff_not.mpr <| valuation_lt_one_iff_mem _ _
  refine ((integralModel_Δ_eq R W ▸ hasGoodReduction_iff _ _).trans ?_).trans h
  simpa [hW] using (valuation_le_one (R := R) (K := K) _ _).ge_iff_eq.symm

@[deprecated (since := "2026-03-04")] alias isGoodReduction_iff_isElliptic_reduction :=
  hasGoodReduction_iff_isElliptic_reduction

/-- A minimal Weierstrass equation has multiplicative reduction if and only if
the valuation of its discriminant is less than 1 and the valuation of `a₄` equals 1. -/
@[mk_iff]
class HasMultiplicativeReduction (W : WeierstrassCurve K) : Prop extends IsMinimal R W where
  badReduction : valuation K (maximalIdeal R) W.Δ < 1
  multiplicativeReduction : valuation K (maximalIdeal R) W.c₄ = 1

/-- A minimal Weierstrass equation has additive reduction if and only if
the valuation of its discriminant is less than 1 and the valuation of `a₄` is less than 1. -/
@[mk_iff]
class HasAdditiveReduction (W : WeierstrassCurve K) : Prop extends IsMinimal R W where
  badReduction : valuation K (maximalIdeal R) W.Δ < 1
  additiveReduction : valuation K (maximalIdeal R) W.c₄ < 1

-- TODO: add characterization in terms of the discriminant when the characteristic is not 2
/-- A minimal Weierstrass equation has split multiplicative reduction if and only if
the polynomial `nodePolynomial`, that is `c₄ T ^ 2 + a₁ c₄ T - (54 b₆ - 3 b₂ b₄ + a₂ c₄)`, of its
integral model splits in the residue field. -/
@[mk_iff]
class HasSplitMultiplicativeReduction (W : WeierstrassCurve K) : Prop
    extends W.HasMultiplicativeReduction R where
  splitMultiplicativeReduction :
    ((W.integralModel R).nodePolynomial.map (algebraMap R (ResidueField R))).Splits

variable {W : WeierstrassCurve K}

theorem hasGoodReduction_or_hasMultiplicativeReduction_or_hasAdditiveReduction [IsMinimal R W] :
    W.HasGoodReduction R ∨ W.HasMultiplicativeReduction R ∨ W.HasAdditiveReduction R := by
  rw [hasGoodReduction_iff, hasMultiplicativeReduction_iff, hasAdditiveReduction_iff,
    ← integralModel_Δ_eq R W, ← integralModel_c₄_eq R W]
  grind [valuation_le_one]

theorem HasGoodReduction.not_hasMultiplicativeReduction (hW : W.HasGoodReduction R) :
    ¬ W.HasMultiplicativeReduction R :=
  fun h ↦ h.badReduction.ne hW.goodReduction

theorem HasGoodReduction.not_hasAdditiveReduction (hW : W.HasGoodReduction R) :
    ¬ W.HasAdditiveReduction R :=
  fun h ↦ h.badReduction.ne hW.goodReduction

theorem HasMultiplicativeReduction.not_hasGoodReduction (hW : W.HasMultiplicativeReduction R) :
    ¬ W.HasGoodReduction R :=
  fun h ↦ hW.badReduction.ne h.goodReduction

theorem HasAdditiveReduction.not_hasGoodReduction (hW : W.HasAdditiveReduction R) :
    ¬ W.HasGoodReduction R :=
  fun h ↦ hW.badReduction.ne h.goodReduction

theorem HasMultiplicativeReduction.not_hasAdditiveReduction (hW : W.HasMultiplicativeReduction R) :
    ¬ W.HasAdditiveReduction R :=
  fun h ↦ h.additiveReduction.ne hW.multiplicativeReduction

theorem HasAdditiveReduction.not_hasMultiplicativeReduction (hW : W.HasAdditiveReduction R) :
    ¬ W.HasMultiplicativeReduction R :=
  fun h ↦ hW.additiveReduction.ne h.multiplicativeReduction

section VariableChange

/-! ### Independence of the reduction from the minimal Weierstrass equation -/

/-- The reduction of a minimal Weierstrass equation after a change of variables with coefficients
in `R` is the reduction of the original equation after the reduced change of variables. -/
lemma reduction_variableChange_baseChange (W : WeierstrassCurve K) [IsMinimal R W]
    (CR : VariableChange R) :
    (CR.baseChange K • W).reduction R = CR.map (residue R) • W.reduction R := by
  rw [reduction, reduction, integralModel_variableChange_baseChange, map_variableChange]

variable {W W' : WeierstrassCurve K} [IsMinimal R W] [IsMinimal R W'] {C : VariableChange K}
  (hC : C • W = W')

include hC

/-- Good reduction does not depend on the choice of minimal Weierstrass equation. -/
lemma hasGoodReduction_iff_of_isMinimal : W'.HasGoodReduction R ↔ W.HasGoodReduction R := by
  rw [hasGoodReduction_iff, hasGoodReduction_iff, valuation_Δ_eq_of_isMinimal R hC]
  exact and_congr_left fun _ ↦ ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩

/-- Multiplicative reduction of an elliptic curve does not depend on the choice of minimal
Weierstrass equation. -/
lemma hasMultiplicativeReduction_iff_of_isMinimal [W.IsElliptic] :
    W'.HasMultiplicativeReduction R ↔ W.HasMultiplicativeReduction R := by
  rw [hasMultiplicativeReduction_iff, hasMultiplicativeReduction_iff,
    valuation_Δ_eq_of_isMinimal R hC, valuation_c₄_eq_of_isMinimal R hC]
  exact and_congr_left fun _ ↦ ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩

/-- Additive reduction of an elliptic curve does not depend on the choice of minimal Weierstrass
equation. -/
lemma hasAdditiveReduction_iff_of_isMinimal [W.IsElliptic] :
    W'.HasAdditiveReduction R ↔ W.HasAdditiveReduction R := by
  rw [hasAdditiveReduction_iff, hasAdditiveReduction_iff,
    valuation_Δ_eq_of_isMinimal R hC, valuation_c₄_eq_of_isMinimal R hC]
  exact and_congr_left fun _ ↦ ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩

/-- Split multiplicative reduction of an elliptic curve does not depend on the choice of minimal
Weierstrass equation. -/
lemma hasSplitMultiplicativeReduction_iff_of_isMinimal [W.IsElliptic] :
    W'.HasSplitMultiplicativeReduction R ↔ W.HasSplitMultiplicativeReduction R := by
  obtain ⟨CR, rfl⟩ := variableChange_integral_of_isMinimal R hC
  subst hC
  have key := splits_map_nodePolynomial_variableChange_iff CR (integralModel R W)
    (algebraMap R (ResidueField R))
  rw [← integralModel_variableChange_baseChange R W CR] at key
  have hm : (CR.baseChange K • W).HasMultiplicativeReduction R ↔ W.HasMultiplicativeReduction R :=
    hasMultiplicativeReduction_iff_of_isMinimal R rfl
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have := hm.mp h.toHasMultiplicativeReduction
    exact ⟨key.mp h.splitMultiplicativeReduction⟩
  · have := hm.mpr h.toHasMultiplicativeReduction
    exact ⟨key.mpr h.splitMultiplicativeReduction⟩

end VariableChange

end Reduction

end WeierstrassCurve
