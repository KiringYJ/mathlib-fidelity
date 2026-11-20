/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kenny Lau
-/
module

public import Mathlib.Algebra.Group.Units.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
public import Mathlib.RingTheory.LocalRing.Basic

/-!
# Formal (multivariate) power series - Inverses

This file defines multivariate formal power series and develops the basic
properties of these objects, when it comes about multiplicative inverses.

For `φ : MvPowerSeries σ R` and `u : Rˣ` is the constant coefficient of `φ`,
`MvPowerSeries.invOfUnit φ u` is a formal power series such,
and `MvPowerSeries.mul_invOfUnit` proves that `φ * invOfUnit φ u = 1`.
The construction of the power series `invOfUnit` is done by writing that
relation and solving and for its coefficients by induction.

A power series is invertible exactly when its constant coefficient is
(`MvPowerSeries.isUnit_iff_constantCoeff`); over a field, exactly when its constant coefficient
is nonzero. The inverse `φ⁻¹` of an invertible power series is its inverse as a unit, with the
general inverse lemmas such as `mul_inv_cancel₀`; `MvPowerSeries.invOfUnit_eq'` identifies it with
`invOfUnit` and `MvPowerSeries.coeff_inv` computes its coefficients. A power series whose constant
coefficient is not invertible has no inverse.

Instances are defined:

* Formal power series over a local ring form a local ring.
* The morphism `MvPowerSeries.map σ f : MvPowerSeries σ A →* MvPowerSeries σ B`
  induced by a local morphism `f : A →+* B` (`IsLocalHom f`)
  of commutative rings is a *local* morphism.

-/

@[expose] public section


noncomputable section

open Finset (antidiagonal mem_antidiagonal)

namespace MvPowerSeries

open Finsupp

variable {σ R : Type*}

section Ring

variable [Ring R]

/-
The inverse of a multivariate formal power series is defined by
well-founded recursion on the coefficients of the inverse.
-/
/-- Auxiliary definition for `invOfUnit`: the power series with constant coefficient `a` whose
higher coefficients satisfy the recursion of an inverse of `φ` with constant coefficient `a`. -/
protected noncomputable def inv.aux (a : R) (φ : MvPowerSeries σ R) : MvPowerSeries σ R
  | n =>
    letI := Classical.decEq σ
    if n = 0 then a
    else
      -a *
        ∑ x ∈ antidiagonal n, if _ : x.2 < n then coeff x.1 φ * inv.aux a φ x.2 else 0
termination_by n => n

theorem coeff_inv_aux [DecidableEq σ] (n : σ →₀ ℕ) (a : R) (φ : MvPowerSeries σ R) :
    coeff n (inv.aux a φ) =
      if n = 0 then a
      else
        -a *
          ∑ x ∈ antidiagonal n, if x.2 < n then coeff x.1 φ * coeff x.2 (inv.aux a φ) else 0 :=
  show inv.aux a φ n = _ by
    cases Subsingleton.elim ‹DecidableEq σ› (Classical.decEq σ)
    rw [inv.aux]
    rfl

/-- A multivariate formal power series is invertible if the constant coefficient is invertible. -/
def invOfUnit (φ : MvPowerSeries σ R) (u : Rˣ) : MvPowerSeries σ R :=
  inv.aux (↑u⁻¹) φ

theorem coeff_invOfUnit [DecidableEq σ] (n : σ →₀ ℕ) (φ : MvPowerSeries σ R) (u : Rˣ) :
    coeff n (invOfUnit φ u) =
      if n = 0 then ↑u⁻¹
      else
        -↑u⁻¹ *
          ∑ x ∈ antidiagonal n,
            if x.2 < n then coeff x.1 φ * coeff x.2 (invOfUnit φ u) else 0 := by
  convert! coeff_inv_aux n (↑u⁻¹) φ

@[simp]
theorem constantCoeff_invOfUnit (φ : MvPowerSeries σ R) (u : Rˣ) :
    constantCoeff (invOfUnit φ u) = ↑u⁻¹ := by
  classical
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_invOfUnit, ite_eq_left rfl]

theorem mul_invOfUnit (φ : MvPowerSeries σ R) (u : Rˣ) (h : constantCoeff φ = u) :
    φ * invOfUnit φ u = 1 :=
  ext fun n =>
    letI := Classical.decEq (σ →₀ ℕ)
    if H : n = 0 then by
      rw [H]
      simp [h]
    else by
      classical
      have : ((0 : σ →₀ ℕ), n) ∈ antidiagonal n := by rw [mem_antidiagonal, zero_add]
      rw [coeff_one, ite_eq_right H, coeff_mul, ← Finset.insert_erase this,
        Finset.sum_insert (Finset.notMem_erase _ _), coeff_zero_eq_constantCoeff_apply, h,
        coeff_invOfUnit, ite_eq_right H, neg_mul, mul_neg, Units.mul_inv_cancel_left, ←
        Finset.insert_erase this, Finset.sum_insert (Finset.notMem_erase _ _),
        Finset.insert_erase this, ite_eq_right (not_lt_of_ge <| le_rfl), zero_add, add_comm, ←
        sub_eq_add_neg, sub_eq_zero, Finset.sum_congr rfl]
      rintro ⟨i, j⟩ hij
      rw [Finset.mem_erase, mem_antidiagonal] at hij
      obtain ⟨h₁, rfl⟩ := hij
      rw [ite_eq_left]
      refine lt_add_of_pos_left _ <| pos_iff_ne_zero.2 ?_
      rintro rfl
      simp at h₁

-- TODO : can one prove equivalence?
theorem invOfUnit_mul (φ : MvPowerSeries σ R) (u : Rˣ) (h : constantCoeff φ = u) :
    invOfUnit φ u * φ = 1 := by
  rw [← mul_cancel_right_mem_nonZeroDivisors (r := φ.invOfUnit u), mul_assoc, one_mul,
    mul_invOfUnit _ _ h, mul_one]
  apply mem_nonZeroDivisors_of_constantCoeff
  simp only [constantCoeff_invOfUnit, IsUnit.mem_nonZeroDivisors (Units.isUnit u⁻¹)]

theorem isUnit_iff_constantCoeff {φ : MvPowerSeries σ R} :
    IsUnit φ ↔ IsUnit (constantCoeff φ) := by
  constructor
  · exact IsUnit.map _
  · intro ⟨u, hu⟩
    exact ⟨⟨_, φ.invOfUnit u, mul_invOfUnit φ u hu.symm, invOfUnit_mul φ u hu.symm⟩, rfl⟩

end Ring

section CommRing

variable [CommRing R]

/-- Multivariate formal power series over a local ring form a local ring. -/
instance [IsLocalRing R] : IsLocalRing (MvPowerSeries σ R) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self <| by
    intro φ
    obtain ⟨u, h⟩ | ⟨u, h⟩ := IsLocalRing.isUnit_or_isUnit_one_sub_self (constantCoeff φ) <;>
        [left; right] <;>
      · refine .of_mul_eq_one _ (mul_invOfUnit _ u ?_)
        simpa using h.symm

-- TODO(jmc): once adic topology lands, show that this is complete
end CommRing

section IsLocalRing

variable {S : Type*} [CommRing R] [CommRing S] (f : R →+* S) [IsLocalHom f]

-- Thanks to the linter for informing us that this instance does
-- not actually need R and S to be local rings!
/-- The map between multivariate formal power series over the same indexing set
induced by a local ring hom `A → B` is local -/
@[instance]
theorem map.isLocalHom : IsLocalHom (map (σ := σ) f) :=
  ⟨by
    rintro φ ⟨ψ, h⟩
    replace h := congr_arg constantCoeff h
    rw [constantCoeff_map] at h
    have : IsUnit (constantCoeff ψ.val) := isUnit_constantCoeff _ ψ.isUnit
    rw [h] at this
    rcases isUnit_of_map_unit f _ this with ⟨c, hc⟩
    exact .of_mul_eq_one (invOfUnit φ c) (mul_invOfUnit φ c hc.symm)⟩

end IsLocalRing

section Inverse

/-! ### The inverse of an invertible power series

A power series is invertible exactly when its constant coefficient is
(`MvPowerSeries.isUnit_iff_constantCoeff`), so over a field exactly when its constant coefficient
is nonzero. Its inverse `φ⁻¹` is its inverse in the group of units of the ring of power series:
`MvPowerSeries.invOfUnit_eq'` identifies it with `invOfUnit`, and `MvPowerSeries.coeff_inv`
computes its coefficients. The rule below extends `checked_unit`, so that `φ⁻¹` finds its evidence
from the invertibility of the constant coefficient, for example from `constantCoeff φ ≠ 0` over a
field. -/

macro_rules | `(tactic| checked_unit) => `(tactic|
    solve
    | assumption
    | ((with_reducible apply MvPowerSeries.isUnit_iff_constantCoeff.mpr); checked_unit))

section Ring

variable [Ring R]

/-- The power series `invOfUnit φ u` is the inverse of `φ` when `u` is its constant coefficient. -/
@[simp]
theorem invOfUnit_eq' (φ : MvPowerSeries σ R) (u : Rˣ) (h : constantCoeff φ = u) :
    invOfUnit φ u = Checked.inv φ (isUnit_iff_constantCoeff.mpr (h ▸ u.isUnit)) :=
  (inv_eq_of_mul_eq_one_right₀ (mul_invOfUnit φ u h)).symm

theorem coeff_inv [DecidableEq σ] (n : σ →₀ ℕ) (φ : MvPowerSeries σ R) {hφ : IsUnit φ} :
    coeff n φ⁻¹ =
      if n = 0 then Checked.inv (constantCoeff φ) (isUnit_constantCoeff φ hφ)
      else
        -Checked.inv (constantCoeff φ) (isUnit_constantCoeff φ hφ) *
          ∑ x ∈ antidiagonal n, if x.2 < n then coeff x.1 φ * coeff x.2 φ⁻¹ else 0 := by
  rw [← invOfUnit_eq' φ (isUnit_constantCoeff φ hφ).unit
    (isUnit_constantCoeff φ hφ).unit_spec.symm]
  exact coeff_invOfUnit n φ _

end Ring

section CommRing

variable [CommRing R]

/-- A scalar multiple `r • φ` of a power series is invertible exactly when `r` and `φ` are. -/
theorem isUnit_smul_iff {r : R} {φ : MvPowerSeries σ R} :
    IsUnit (r • φ) ↔ IsUnit r ∧ IsUnit φ := by
  rw [isUnit_iff_constantCoeff, isUnit_iff_constantCoeff (φ := φ), constantCoeff_smul,
    smul_eq_mul, IsUnit.mul_iff]

@[simp]
theorem smul_inv (r : R) (φ : MvPowerSeries σ R) {h : IsUnit (r • φ)} :
    (r • φ)⁻¹ =
      Checked.inv r (isUnit_smul_iff.mp h).1 • Checked.inv φ (isUnit_smul_iff.mp h).2 := by
  refine inv_eq_of_mul_eq_one_left₀ ?_
  rw [smul_mul_smul_comm, inv_mul_cancel₀, inv_mul_cancel₀, one_smul]

end CommRing

section Field

variable {k : Type*} [Field k]

@[simp]
theorem invOfUnit_eq (φ : MvPowerSeries σ k) (h : constantCoeff φ ≠ 0) :
    invOfUnit φ (Units.mk0 _ h) = φ⁻¹ :=
  invOfUnit_eq' φ _ rfl

end Field

end Inverse

end MvPowerSeries

end
