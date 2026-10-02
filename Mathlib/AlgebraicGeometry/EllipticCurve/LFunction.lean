/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.Completion
public import Mathlib.NumberTheory.ArithmeticFunction.LFunction
public import Mathlib.NumberTheory.LSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# The L-function of an elliptic curve

In this file, we define the L-function of an elliptic curve given by a Weierstrass equation.

## Main definitions

* `WeierstrassCurve.LFunction`: the L-function of an elliptic curve over a number field.

## Main statements

* `WeierstrassCurve.localPolynomial_eq_of_isMinimal`: the local polynomial can be computed from any
  minimal Weierstrass equation.
* `WeierstrassCurve.variableChange_localPolynomial`, `WeierstrassCurve.variableChange_LFunction`:
  the local polynomial and the L-function are invariant under a change of variables.
* `WeierstrassCurve.localPolynomial_baseChange_adicCompletion`: completing the discrete valuation
  ring does not change the local polynomial.

## Implementation notes

The local factors are defined for an elliptic curve at a discrete valuation ring `R` with finite
residue field. The local polynomial is `det(1 - πT)` on the inertia invariants, where the
geometric Frobenius `π` is the inverse of the canonical Frobenius generator, which is defined when
the residue field is finite ([serre1970], §2.2, (13)). The Euler factor substitutes `q⁻ˢ`, where
`q` is the size of the residue field ([serre1970], §1.2). The ring `R` need not be complete:
`localPolynomial_baseChange_adicCompletion` proves agreement with the polynomial over its
completion.

The local polynomial applies its formula to a chosen minimal model. For a singular curve this
choice is not determined by the curve: the nodal cubic `y² + xy = x³` and its rescaling by a
uniformizer are both minimal, with multiplicative and additive reduction respectively. For an
elliptic curve the minimal models differ by changes of variables with coefficients in `R` and `u`
a unit (`WeierstrassCurve.variableChange_integral_of_isMinimal`), which preserve the reduction
type and the number of points of the reduction, so the choice does not matter.

## References

* [J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]
* [J.-P. Serre, *Facteurs locaux des fonctions zêta des variétés algébriques*][serre1970]
-/

@[expose] public section

namespace WeierstrassCurve

section LocalField

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {K : Type*}
  [Field K] [Algebra R K] [IsFractionRing R K] (W : WeierstrassCurve K)

open Classical Polynomial in
/-- The local polynomial associated to an elliptic curve `W` over the fraction field of a
discrete valuation ring `R` with finite residue field `κ`. In the case of good reduction it is
given by `1 - a T + q T ^ 2`, where `q` is the cardinality of `κ`, `a = q + 1 - N`, and `N` is the
number of points over `κ` of the reduction of a minimal model; it is `1 - T`, `1 + T`, and `1` for
split multiplicative, nonsplit multiplicative, and additive reduction ([serre1970], §2.4). -/
@[nolint unusedArguments]
noncomputable def localPolynomial [W.IsElliptic] [Finite (IsLocalRing.ResidueField R)] : ℤ[X] :=
  letI W' := W.minimal R
  letI q : ℤ := Nat.card (IsLocalRing.ResidueField R)
  letI a : ℤ := q + 1 - (Nat.card (W'.reduction R).toAffine.Point)
  if W'.HasGoodReduction R then 1 - C a * X + C q * X ^ 2
  else if W'.HasSplitMultiplicativeReduction R then 1 - X
  else if W'.HasMultiplicativeReduction R then 1 + X
  else 1

/-- The local power series associated to an elliptic curve over the fraction field of a discrete
valuation ring with finite residue field. -/
noncomputable def localPowerSeries [W.IsElliptic] [Finite (IsLocalRing.ResidueField R)] :
    PowerSeries ℤ :=
  PowerSeries.invOfUnit (W.localPolynomial R) 1

/-- The local Euler factor associated to an elliptic curve over the fraction field of a discrete
valuation ring with finite residue field. -/
noncomputable def localEulerFactor [W.IsElliptic] [Finite (IsLocalRing.ResidueField R)] :
    ArithmeticFunction ℤ :=
  .ofPowerSeries (Nat.card (IsLocalRing.ResidueField R)) Finite.one_lt_card (W.localPowerSeries R)

/-! ### Independence of the minimal model -/

/-- Two minimal Weierstrass equations of an elliptic curve have reductions with the same number
of points over the residue field. -/
lemma natCard_point_reduction_eq_of_isMinimal {W W' : WeierstrassCurve K} [W.IsElliptic]
    [IsMinimal R W] [IsMinimal R W'] {C : VariableChange K} (hC : C • W = W') :
    Nat.card (W'.reduction R).toAffine.Point = Nat.card (W.reduction R).toAffine.Point := by
  obtain ⟨CR, rfl⟩ := variableChange_integral_of_isMinimal R hC
  subst hC
  rw [reduction_variableChange_baseChange]
  exact Affine.Point.natCard_variableChange _

variable [W.IsElliptic] [Finite (IsLocalRing.ResidueField R)]

open Classical Polynomial in
/-- The local polynomial of an elliptic curve given by a minimal Weierstrass equation is computed
by that equation. -/
theorem localPolynomial_eq_of_isMinimal [IsMinimal R W] :
    W.localPolynomial R =
      letI q : ℤ := Nat.card (IsLocalRing.ResidueField R)
      letI a : ℤ := q + 1 - (Nat.card (W.reduction R).toAffine.Point)
      if W.HasGoodReduction R then 1 - C a * X + C q * X ^ 2
      else if W.HasSplitMultiplicativeReduction R then 1 - X
      else if W.HasMultiplicativeReduction R then 1 + X
      else 1 := by
  have hC : (W.exists_isMinimal R).choose • W = W.minimal R := rfl
  simp only [localPolynomial, hasGoodReduction_iff_of_isMinimal R hC,
    hasSplitMultiplicativeReduction_iff_of_isMinimal R hC,
    hasMultiplicativeReduction_iff_of_isMinimal R hC, natCard_point_reduction_eq_of_isMinimal R hC]

open Classical in
/-- The local polynomial of an elliptic curve is invariant under a change of variables. -/
@[simp]
theorem variableChange_localPolynomial (C : VariableChange K) :
    (C • W).localPolynomial R = W.localPolynomial R := by
  have hC : (((C • W).exists_isMinimal R).choose * C * (W.exists_isMinimal R).choose⁻¹) •
      W.minimal R = (C • W).minimal R := by
    simp only [minimal, smul_smul, inv_mul_cancel_right]
  simp only [localPolynomial, hasGoodReduction_iff_of_isMinimal R hC,
    hasSplitMultiplicativeReduction_iff_of_isMinimal R hC,
    hasMultiplicativeReduction_iff_of_isMinimal R hC, natCard_point_reduction_eq_of_isMinimal R hC]

/-- The local power series of an elliptic curve is invariant under a change of variables. -/
@[simp]
theorem variableChange_localPowerSeries (C : VariableChange K) :
    (C • W).localPowerSeries R = W.localPowerSeries R := by
  simp only [localPowerSeries, variableChange_localPolynomial]

/-- The local Euler factor of an elliptic curve is invariant under a change of variables. -/
@[simp]
theorem variableChange_localEulerFactor (C : VariableChange K) :
    (C • W).localEulerFactor R = W.localEulerFactor R := by
  simp only [localEulerFactor, variableChange_localPowerSeries]

open Polynomial in
/-- The local polynomial of an elliptic curve with good reduction, given by a minimal Weierstrass
equation, is `1 - a T + q T ^ 2`, where `q` is the size of the residue field and `a = q + 1 - N`
for the number `N` of points of the reduction. -/
theorem localPolynomial_of_hasGoodReduction [h : W.HasGoodReduction R] :
    W.localPolynomial R = 1 - C ((Nat.card (IsLocalRing.ResidueField R) : ℤ) + 1 -
      Nat.card (W.reduction R).toAffine.Point) * X +
        C (Nat.card (IsLocalRing.ResidueField R) : ℤ) * X ^ 2 := by
  rw [localPolynomial_eq_of_isMinimal, ite_eq_left h]

open Polynomial in
/-- The local polynomial of an elliptic curve with split multiplicative reduction is `1 - T`. -/
theorem localPolynomial_of_hasSplitMultiplicativeReduction
    [h : W.HasSplitMultiplicativeReduction R] : W.localPolynomial R = 1 - X := by
  rw [localPolynomial_eq_of_isMinimal, ite_eq_right h.not_hasGoodReduction, ite_eq_left h]

open Polynomial in
/-- The local polynomial of an elliptic curve with nonsplit multiplicative reduction is `1 + T`. -/
theorem localPolynomial_of_not_hasSplitMultiplicativeReduction
    [h : W.HasMultiplicativeReduction R] (h' : ¬ W.HasSplitMultiplicativeReduction R) :
    W.localPolynomial R = 1 + X := by
  rw [localPolynomial_eq_of_isMinimal, ite_eq_right h.not_hasGoodReduction, ite_eq_right h',
    ite_eq_left h]

/-- The local polynomial of an elliptic curve with additive reduction is `1`. -/
theorem localPolynomial_of_hasAdditiveReduction [h : W.HasAdditiveReduction R] :
    W.localPolynomial R = 1 := by
  rw [localPolynomial_eq_of_isMinimal, ite_eq_right h.not_hasGoodReduction,
    ite_eq_right fun h' ↦ HasAdditiveReduction.not_hasMultiplicativeReduction R h
      h'.toHasMultiplicativeReduction,
    ite_eq_right h.not_hasMultiplicativeReduction]

end LocalField

section Completion

open IsDedekindDomain.HeightOneSpectrum IsDiscreteValuationRing

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  (W : WeierstrassCurve K) [W.IsElliptic] [Finite (IsLocalRing.ResidueField R)]

local notation "K̂" => adicCompletion K (IsDiscreteValuationRing.maximalIdeal R)
local notation "R̂" => adicCompletionIntegers K (IsDiscreteValuationRing.maximalIdeal R)

private lemma localPolynomial_baseChange_adicCompletion_of_isMinimal [IsMinimal R W] :
    (W.baseChange K̂).localPolynomial R̂ = W.localPolynomial R := by
  let e := residueFieldEquivAdicCompletion R (K := K)
  have hq : Nat.card (IsLocalRing.ResidueField R̂) =
      Nat.card (IsLocalRing.ResidueField R) := Nat.card_congr e.toEquiv.symm
  have hN : Nat.card ((W.baseChange K̂).reduction R̂).toAffine.Point =
      Nat.card (W.reduction R).toAffine.Point := by
    rw [reduction_baseChange_adicCompletion]
    exact Affine.Point.natCard_map_equiv e.toRingEquiv
  simp only [localPolynomial_eq_of_isMinimal, hq, hN]
  rw [hasGoodReduction_baseChange_adicCompletion_iff R W,
    hasSplitMultiplicativeReduction_baseChange_adicCompletion_iff R W,
    hasMultiplicativeReduction_baseChange_adicCompletion_iff R W]

/-- The local polynomial of an elliptic curve is unchanged by completing the discrete valuation
ring. In particular, its definition over an incomplete ring agrees with the convention of
[serre1970], §1.2. -/
theorem localPolynomial_baseChange_adicCompletion :
    (W.baseChange K̂).localPolynomial R̂ = W.localPolynomial R := by
  calc
    (W.baseChange K̂).localPolynomial R̂ =
        ((W.minimal R).baseChange K̂).localPolynomial R̂ := by
      simp only [minimal, baseChange, ← map_variableChange, variableChange_localPolynomial]
    _ = (W.minimal R).localPolynomial R :=
      localPolynomial_baseChange_adicCompletion_of_isMinimal R (W.minimal R)
    _ = W.localPolynomial R := by simp only [minimal, variableChange_localPolynomial]

/-- The local power series of an elliptic curve is unchanged by completion. -/
theorem localPowerSeries_baseChange_adicCompletion :
    (W.baseChange K̂).localPowerSeries R̂ = W.localPowerSeries R := by
  simp only [localPowerSeries, localPolynomial_baseChange_adicCompletion]

/-- The local Euler factor of an elliptic curve is unchanged by completion. -/
theorem localEulerFactor_baseChange_adicCompletion :
    (W.baseChange K̂).localEulerFactor R̂ = W.localEulerFactor R := by
  have hq : Nat.card (IsLocalRing.ResidueField R̂) =
      Nat.card (IsLocalRing.ResidueField R) :=
    Nat.card_congr (residueFieldEquivAdicCompletion R (K := K)).toEquiv.symm
  simp only [localEulerFactor, localPowerSeries_baseChange_adicCompletion, hq]

end Completion

section NumberField

open ArithmeticFunction IsDedekindDomain NumberField

variable {K : Type*} [Field K] [NumberField K] (W : WeierstrassCurve K) [W.IsElliptic]

/-- The L-function of an elliptic curve `W` over a number field `K` as a formal Dirichlet series.

For each prime ideal `p` of the ring of integers of `K` with norm `‖p‖` residue field `κ_p`,
we define the local polynomial `fₚ(T)` as:
* `fₚ = 1 - aₚ T + ‖p‖ T ^ 2` where `aₚ = ‖p‖ + 1 - |W(κ_p)|` if `W` has good reduction at `p`,
* `fₚ = 1 - T` if `W` has split multiplicative reduction at `p`,
* `fₚ = 1 + T` if `W` has nonsplit multiplicative reduction at `p`,
* `fₚ = 1` if `W` has additive reduction at `p`.
Then the L-function of `W` is the formal Dirichlet series defined as the product of `1 / fₚ(‖p‖⁻ˢ)`
as `p` ranges over all prime ideals of the ring of integers of `K`.
-/
noncomputable def LFunction : ArithmeticFunction ℤ :=
  eulerProduct fun p : HeightOneSpectrum (𝓞 K) ↦
      (W.baseChange (p.adicCompletion K)).localEulerFactor (p.adicCompletionIntegers K)

/-- The L-series of an elliptic curve over a number field. -/
protected noncomputable def LSeries (s : ℂ) :=
  LSeries ((↑) ∘ W.LFunction) s

/-- The L-function of an elliptic curve is invariant under a change of variables. -/
@[simp]
theorem variableChange_LFunction (C : VariableChange K) : (C • W).LFunction = W.LFunction := by
  simp only [LFunction, baseChange, ← map_variableChange, variableChange_localEulerFactor]

/-- The L-series of an elliptic curve is invariant under a change of variables. -/
@[simp]
theorem variableChange_LSeries (C : VariableChange K) (s : ℂ) :
    (C • W).LSeries s = W.LSeries s := by
  rw [WeierstrassCurve.LSeries, WeierstrassCurve.LSeries, variableChange_LFunction]

end NumberField

end WeierstrassCurve
