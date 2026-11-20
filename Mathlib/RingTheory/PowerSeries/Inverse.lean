/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kenny Lau, María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
module

public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
public import Mathlib.Data.ENat.Lattice

/-! # Formal power series - Inverses

If the constant coefficient of a formal (univariate) power series is invertible,
then this formal power series is invertible.
(See the discussion in `Mathlib/RingTheory/MvPowerSeries/Inverse.lean` for
the construction.) The inverse `φ⁻¹` of an invertible power series is its inverse in the group of
units; `PowerSeries.coeff_inv` computes its coefficients. A power series whose constant coefficient
is not invertible has no inverse.

Formal (univariate) power series over a local ring form a local ring.

Formal (univariate) power series over a field form a discrete valuation ring, and a normalization
monoid. The definition `residueFieldOfPowerSeries` provides the isomorphism between the residue
field of `k⟦X⟧` and `k`, when `k` is a field.

-/

@[expose] public section


noncomputable section

open Polynomial

open Finset (antidiagonal mem_antidiagonal)

namespace PowerSeries

open Finsupp (single)

variable {R : Type*}


section Ring

variable [Ring R]

/-- Auxiliary function used for computing inverse of a power series -/
protected def inv.aux : R → R⟦X⟧ → R⟦X⟧ :=
  MvPowerSeries.inv.aux

theorem coeff_inv_aux (n : ℕ) (a : R) (φ : R⟦X⟧) :
    coeff n (inv.aux a φ) =
      if n = 0 then a
      else
        -a *
          ∑ x ∈ antidiagonal n,
            if x.2 < n then coeff x.1 φ * coeff x.2 (inv.aux a φ) else 0 := by
  rw [coeff, inv.aux, MvPowerSeries.coeff_inv_aux]
  simp only [Finsupp.single_eq_zero]
  split_ifs; · rfl
  congr 1
  symm
  apply Finset.sum_nbij' (fun (a, b) ↦ (single () a, single () b))
    fun (f, g) ↦ (f (), g ())
  · aesop
  · aesop
  · aesop
  · aesop
  · rintro ⟨i, j⟩ _hij
    obtain H | H := le_or_gt n j
    · aesop
    rw [ite_eq_left H, ite_eq_left]
    · rfl
    refine ⟨?_, fun hh ↦ H.not_ge ?_⟩
    · rintro ⟨⟩
      simpa [Finsupp.single_eq_same] using le_of_lt H
    · simpa [Finsupp.single_eq_same] using hh ()

/-- A formal power series is invertible if the constant coefficient is invertible. -/
def invOfUnit (φ : R⟦X⟧) (u : Rˣ) : R⟦X⟧ :=
  MvPowerSeries.invOfUnit φ u

theorem coeff_invOfUnit (n : ℕ) (φ : R⟦X⟧) (u : Rˣ) :
    coeff n (invOfUnit φ u) =
      if n = 0 then ↑u⁻¹
      else
        -↑u⁻¹ *
          ∑ x ∈ antidiagonal n,
            if x.2 < n then coeff x.1 φ * coeff x.2 (invOfUnit φ u) else 0 :=
  coeff_inv_aux n (↑u⁻¹ : R) φ

@[simp]
theorem constantCoeff_invOfUnit (φ : R⟦X⟧) (u : Rˣ) :
    constantCoeff (invOfUnit φ u) = ↑u⁻¹ := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_invOfUnit, ite_eq_left rfl]

theorem mul_invOfUnit (φ : R⟦X⟧) (u : Rˣ) (h : constantCoeff φ = u) :
    φ * invOfUnit φ u = 1 :=
  MvPowerSeries.mul_invOfUnit φ u <| h

theorem invOfUnit_mul (φ : R⟦X⟧) (u : Rˣ) (h : constantCoeff φ = u) :
    invOfUnit φ u * φ = 1 :=
  MvPowerSeries.invOfUnit_mul φ u h

theorem isUnit_iff_constantCoeff {φ : R⟦X⟧} :
    IsUnit φ ↔ IsUnit (constantCoeff φ) :=
  MvPowerSeries.isUnit_iff_constantCoeff

/-- Two ways of removing the constant coefficient of a power series are the same. -/
theorem sub_const_eq_shift_mul_X (φ : R⟦X⟧) :
    φ - C (constantCoeff φ) = (mk fun p ↦ coeff (p + 1) φ) * X :=
  sub_eq_iff_eq_add.mpr (eq_shift_mul_X_add_const φ)

theorem sub_const_eq_X_mul_shift (φ : R⟦X⟧) :
    φ - C (constantCoeff φ) = X * mk fun p ↦ coeff (p + 1) φ :=
  sub_eq_iff_eq_add.mpr (eq_X_mul_shift_add_const φ)

/-! ### The inverse of an invertible power series

A power series is invertible exactly when its constant coefficient is
(`PowerSeries.isUnit_iff_constantCoeff`), so over a field exactly when its constant coefficient is
nonzero. Its inverse `φ⁻¹` is its inverse in the group of units of the ring of power series:
`PowerSeries.invOfUnit_eq'` identifies it with `invOfUnit`, and `PowerSeries.coeff_inv` computes
its coefficients. The rule below extends `checked_unit`, so that `φ⁻¹` finds its evidence from the
invertibility of the constant coefficient, for example from `constantCoeff φ ≠ 0` over a field. A
local hypothesis is used first, so that a theorem's evidence binder appears verbatim in its
statement. -/

macro_rules | `(tactic| checked_unit) => `(tactic|
    solve
    | assumption
    | ((with_reducible apply PowerSeries.isUnit_iff_constantCoeff.mpr); checked_unit))

/-- The power series `invOfUnit φ u` is the inverse of `φ` when `u` is its constant coefficient. -/
@[simp]
theorem invOfUnit_eq' (φ : R⟦X⟧) (u : Rˣ) (h : constantCoeff φ = u) :
    invOfUnit φ u = Checked.inv φ (isUnit_iff_constantCoeff.mpr (h ▸ u.isUnit)) :=
  (inv_eq_of_mul_eq_one_right₀ (mul_invOfUnit φ u h)).symm

theorem inv_eq_inv_aux (φ : R⟦X⟧) {hφ : IsUnit φ} :
    φ⁻¹ = inv.aux (Checked.inv (constantCoeff φ) (isUnit_constantCoeff φ hφ)) φ :=
  (invOfUnit_eq' φ (isUnit_constantCoeff φ hφ).unit
    (isUnit_constantCoeff φ hφ).unit_spec.symm).symm

theorem coeff_inv (n : ℕ) (φ : R⟦X⟧) {hφ : IsUnit φ} :
    coeff n φ⁻¹ =
      if n = 0 then Checked.inv (constantCoeff φ) (isUnit_constantCoeff φ hφ)
      else
        -Checked.inv (constantCoeff φ) (isUnit_constantCoeff φ hφ) *
          ∑ x ∈ antidiagonal n,
            if x.2 < n then coeff x.1 φ * coeff x.2 φ⁻¹ else 0 := by
  rw [inv_eq_inv_aux, coeff_inv_aux n]

@[simp]
theorem constantCoeff_inv (φ : R⟦X⟧) {hφ : IsUnit φ} :
    constantCoeff φ⁻¹ = Checked.inv (constantCoeff φ) (isUnit_constantCoeff φ hφ) :=
  Eq.symm <| inv_eq_of_mul_eq_one_right₀ <| map_mul_eq_one constantCoeff mul_inv_cancel₀

@[simp]
theorem C_inv (r : R) {h : IsUnit (C r)} :
    (C r)⁻¹ = C (Checked.inv r (constantCoeff_C r ▸ isUnit_constantCoeff (C r) h)) :=
  inv_eq_of_mul_eq_one_right₀ (by rw [← map_mul, mul_inv_cancel₀, map_one])

end Ring

section CommRing

variable [CommRing R]

theorem smul_inv (r : R) (φ : R⟦X⟧) {h : IsUnit (r • φ)} :
    (r • φ)⁻¹ = Checked.inv r (MvPowerSeries.isUnit_smul_iff.mp h).1 •
      Checked.inv φ (MvPowerSeries.isUnit_smul_iff.mp h).2 :=
  MvPowerSeries.smul_inv r φ

end CommRing

section Field

variable {k : Type*} [Field k]

@[simp]
theorem invOfUnit_eq (φ : k⟦X⟧) (h : constantCoeff φ ≠ 0) :
    invOfUnit φ (Units.mk0 _ h) = φ⁻¹ :=
  invOfUnit_eq' φ _ rfl

/-- `firstUnitCoeff` is the non-zero coefficient whose index is `f.order`, seen as a unit of the
  field. It is obtained using `divided_by_X_pow_order`, defined in `PowerSeries.Order`. -/
def firstUnitCoeff {f : k⟦X⟧} (hf : f ≠ 0) : kˣ :=
  have : Invertible (constantCoeff (divXPowOrder f)) := by
    apply invertibleOfNonzero
    simpa [constantCoeff_divXPowOrder_eq_zero_iff.not]
  unitOfInvertible (constantCoeff (divXPowOrder f))

/-- `Inv_divided_by_X_pow_order` is the inverse of the element obtained by diving a non-zero power
series by the largest power of `X` dividing it. Useful to create a term of type `Units`, done in
`Unit_divided_by_X_pow_order` -/
def Inv_divided_by_X_pow_order {f : k⟦X⟧} (hf : f ≠ 0) : k⟦X⟧ :=
  invOfUnit (divXPowOrder f) (firstUnitCoeff hf)

@[simp]
theorem Inv_divided_by_X_pow_order_rightInv {f : k⟦X⟧} (hf : f ≠ 0) :
    divXPowOrder f * Inv_divided_by_X_pow_order hf = 1 :=
  mul_invOfUnit (divXPowOrder f) (firstUnitCoeff hf) rfl

@[simp]
theorem Inv_divided_by_X_pow_order_leftInv {f : k⟦X⟧} (hf : f ≠ 0) :
    Inv_divided_by_X_pow_order hf * divXPowOrder f = 1 := by
  rw [mul_comm]
  exact mul_invOfUnit (divXPowOrder f) (firstUnitCoeff hf) rfl

open scoped Classical in
/-- `Unit_of_divided_by_X_pow_order` is the unit power series obtained by dividing a non-zero
power series by the largest power of `X` that divides it. -/
def Unit_of_divided_by_X_pow_order (f : k⟦X⟧) : k⟦X⟧ˣ :=
  if hf : f = 0 then 1
  else
    { val := divXPowOrder f
      inv := Inv_divided_by_X_pow_order hf
      val_inv := Inv_divided_by_X_pow_order_rightInv hf
      inv_val := Inv_divided_by_X_pow_order_leftInv hf }

theorem isUnit_divided_by_X_pow_order {f : k⟦X⟧} (hf : f ≠ 0) :
    IsUnit (divXPowOrder f) :=
  ⟨Unit_of_divided_by_X_pow_order f,
    by simp only [Unit_of_divided_by_X_pow_order, dite_eq_right hf, Units.val_mk]⟩

theorem Unit_of_divided_by_X_pow_order_nonzero {f : k⟦X⟧} (hf : f ≠ 0) :
    ↑(Unit_of_divided_by_X_pow_order f) = divXPowOrder f := by
  simp only [Unit_of_divided_by_X_pow_order, dite_eq_right hf, Units.val_mk]

@[simp]
theorem Unit_of_divided_by_X_pow_order_zero : Unit_of_divided_by_X_pow_order (0 : k⟦X⟧) = 1 := by
  simp only [Unit_of_divided_by_X_pow_order, dite_eq_left]

theorem eq_divided_by_X_pow_order_Iff_Unit {f : k⟦X⟧} (hf : f ≠ 0) :
    f = divXPowOrder f ↔ IsUnit f :=
  ⟨fun h ↦ by rw [h]; exact isUnit_divided_by_X_pow_order hf, fun h ↦ by
    have : f.order = 0 := by
      simp [order_zero_of_isUnit h]
    conv_lhs => rw [← X_pow_order_mul_divXPowOrder (f := f), this, ENat.toNat_zero,
      pow_zero, one_mul]⟩

end Field

section IsLocalRing

variable {S : Type*} [CommRing R] [CommRing S] (f : R →+* S) [IsLocalHom f]

@[instance]
theorem map.isLocalHom : IsLocalHom (map f) :=
  MvPowerSeries.map.isLocalHom f

end IsLocalRing

section IsDiscreteValuationRing

variable {k : Type*} [Field k]

open IsDiscreteValuationRing

theorem hasUnitMulPowIrreducibleFactorization :
    HasUnitMulPowIrreducibleFactorization k⟦X⟧ :=
  ⟨X, And.intro X_irreducible
      (by
        intro f hf
        use f.order.toNat
        use Unit_of_divided_by_X_pow_order f
        simp only [Unit_of_divided_by_X_pow_order_nonzero hf]
        exact X_pow_order_mul_divXPowOrder)⟩

instance : UniqueFactorizationMonoid k⟦X⟧ :=
  hasUnitMulPowIrreducibleFactorization.toUniqueFactorizationMonoid

instance : IsDiscreteValuationRing k⟦X⟧ :=
  ofHasUnitMulPowIrreducibleFactorization hasUnitMulPowIrreducibleFactorization

example : IsNoetherianRing k⟦X⟧ := inferInstance

/-- The maximal ideal of `k⟦X⟧` is generated by `X`. -/
theorem maximalIdeal_eq_span_X : IsLocalRing.maximalIdeal (k⟦X⟧) = Ideal.span {X} := by
  have hX : (Ideal.span {(X : k⟦X⟧)}).IsMaximal := by
    rw [Ideal.isMaximal_iff]
    constructor
    · rw [Ideal.mem_span_singleton]
      exact Prime.not_dvd_one X_prime
    · intro I f hI hfX hfI
      rw [Ideal.mem_span_singleton, X_dvd_iff] at hfX
      have hfI0 : C (f 0) ∈ I := by
        have : C (f 0) = f - (f - C (f 0)) := by rw [sub_sub_cancel]
        rw [this]
        apply Ideal.sub_mem I hfI
        apply hI
        rw [Ideal.mem_span_singleton, X_dvd_iff, map_sub, constantCoeff_C, ←
          coeff_zero_eq_constantCoeff_apply, sub_eq_zero, coeff_zero_eq_constantCoeff]
        rfl
      rw [← Ideal.eq_top_iff_one]
      apply Ideal.eq_top_of_isUnit_mem I hfI0 (IsUnit.map C (Ne.isUnit hfX))
  rw [IsLocalRing.eq_maximalIdeal hX]

instance : StrongNormalizationMonoid k⟦X⟧ where
  normUnit f := (Unit_of_divided_by_X_pow_order f)⁻¹
  normUnit_zero := by simp only [Unit_of_divided_by_X_pow_order_zero, inv_one]
  normUnit_mul hf hg := by
    simp only [← mul_inv, inv_inj]
    simp only [Unit_of_divided_by_X_pow_order_nonzero (mul_ne_zero hf hg),
      Unit_of_divided_by_X_pow_order_nonzero hf, Unit_of_divided_by_X_pow_order_nonzero hg,
      Units.ext_iff, Units.val_mul, ← divXPowOrder_mul]
  normUnit_coe_units u := by
    set u₀ := u.1 with hu
    have h₀ : IsUnit u₀ := ⟨u, hu.symm⟩
    rw [inv_inj, Units.ext_iff, ← hu, Unit_of_divided_by_X_pow_order_nonzero h₀.ne_zero]
    exact ((eq_divided_by_X_pow_order_Iff_Unit h₀.ne_zero).mpr h₀).symm

theorem normUnit_X : normUnit (X : k⟦X⟧) = 1 := by
  simp [normUnit, ← Units.val_eq_one, Unit_of_divided_by_X_pow_order_nonzero]

theorem X_eq_normalizeX : (X : k⟦X⟧) = normalize X := by
  simp only [normalize_apply, normUnit_X, Units.val_one, mul_one]

open UniqueFactorizationMonoid

open scoped Classical in
theorem normalized_count_X_eq_of_coe {P : k[X]} (hP : P ≠ 0) :
    Multiset.count PowerSeries.X (normalizedFactors (P : k⟦X⟧)) =
      Multiset.count Polynomial.X (normalizedFactors P) := by
  apply eq_of_forall_le_iff
  simp only [← Nat.cast_le (α := ℕ∞)]
  rw [X_eq_normalize, PowerSeries.X_eq_normalizeX, ← emultiplicity_eq_count_normalizedFactors
    irreducible_X hP, ← emultiplicity_eq_count_normalizedFactors X_irreducible] <;>
  simp only [← pow_dvd_iff_le_emultiplicity, Polynomial.X_pow_dvd_iff,
    PowerSeries.X_pow_dvd_iff, Polynomial.coeff_coe P, implies_true, ne_eq, coe_eq_zero_iff, hP,
    not_false_eq_true]

open IsLocalRing

theorem ker_coeff_eq_max_ideal : RingHom.ker (constantCoeff (R := k)) = maximalIdeal _ :=
  Ideal.ext fun _ ↦ by
    rw [RingHom.mem_ker, maximalIdeal_eq_span_X, Ideal.mem_span_singleton, X_dvd_iff]

/-- The ring isomorphism between the residue field of the ring of power series valued in a field `K`
and `K` itself. -/
def residueFieldOfPowerSeries : ResidueField k⟦X⟧ ≃+* k :=
  Ideal.quotEquivOfEq (ker_coeff_eq_max_ideal).symm |>.trans
    (RingHom.quotientKerEquivOfSurjective constantCoeff_surj)

instance [Finite k] : Finite (ResidueField k⟦X⟧) :=
  .of_equiv _ residueFieldOfPowerSeries.symm.toEquiv

/-- The residue field of the ring of power series over a field `k` has as many elements as `k`. -/
theorem natCard_residueField : Nat.card (ResidueField k⟦X⟧) = Nat.card k :=
  Nat.card_congr residueFieldOfPowerSeries.toEquiv

end IsDiscreteValuationRing


end PowerSeries

end
