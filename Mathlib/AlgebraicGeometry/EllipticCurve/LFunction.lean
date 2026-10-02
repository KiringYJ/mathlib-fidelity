/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
public import Mathlib.NumberTheory.ArithmeticFunction.LFunction
public import Mathlib.NumberTheory.LSeries.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# The L-function of a Weierstrass curve

In this file, we define the L-function of a Weierstrass curve.

## Main definitions

* `WeierstrassCurve.LFunction`: the L-function of a Weierstrass equation.

## Implementation notes

The local factors are defined at a discrete valuation ring `R` with finite residue field. The
local polynomial is `det(1 - πT)` on the inertia invariants, where the geometric Frobenius `π` is
the inverse of the canonical Frobenius generator, which is defined when the residue field is
finite ([serre1970], §2.2, (13)). The Euler factor substitutes `q⁻ˢ`, where `q` is the size of the
residue field ([serre1970], §1.2). The ring `R` need not be complete.

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
/-- The local polynomial associated to a Weierstrass curve `W` over the fraction field of a
discrete valuation ring `R` with finite residue field `κ`. In the case of good reduction it is
given by `1 - a T + q T ^ 2`, where `q` is the cardinality of `κ`, `a = q + 1 - N`, and `N` is the
number of points over `κ` of the reduction of a minimal model; it is `1 - T`, `1 + T`, and `1` for
split multiplicative, nonsplit multiplicative, and additive reduction ([serre1970], §2.4). -/
@[nolint unusedArguments]
noncomputable def localPolynomial [Finite (IsLocalRing.ResidueField R)] : ℤ[X] :=
  letI W' := W.minimal R
  letI q : ℤ := Nat.card (IsLocalRing.ResidueField R)
  letI a : ℤ := q + 1 - (Nat.card (W'.reduction R).toAffine.Point)
  if W'.HasGoodReduction R then 1 - C a * X + C q * X ^ 2
  else if W'.HasSplitMultiplicativeReduction R then 1 - X
  else if W'.HasMultiplicativeReduction R then 1 + X
  else 1

/-- The local power series associated to a Weierstrass curve over the fraction field of a discrete
valuation ring with finite residue field. -/
noncomputable def localPowerSeries [Finite (IsLocalRing.ResidueField R)] : PowerSeries ℤ :=
  PowerSeries.invOfUnit (W.localPolynomial R) 1

/-- The local Euler factor associated to a Weierstrass curve over the fraction field of a discrete
valuation ring with finite residue field. -/
noncomputable def localEulerFactor [Finite (IsLocalRing.ResidueField R)] : ArithmeticFunction ℤ :=
  .ofPowerSeries (Nat.card (IsLocalRing.ResidueField R)) Finite.one_lt_card (W.localPowerSeries R)

end LocalField

section NumberField

open ArithmeticFunction IsDedekindDomain NumberField

variable {K : Type*} [Field K] [NumberField K] (W : WeierstrassCurve K)

/-- The L-function of a Weierstrass curve `W` over a number field `K` as a formal Dirichlet series.

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

/-- The L-series of a Weierstrass curve over a number field. -/
protected noncomputable def LSeries (W : WeierstrassCurve K) (s : ℂ) :=
  LSeries ((↑) ∘ W.LFunction) s

end NumberField

end WeierstrassCurve
