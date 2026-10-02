import Mathlib.AlgebraicGeometry.EllipticCurve.LFunction

/-!
# Strict local Euler factors

These tests ensure that `ArithmeticFunction.ofPowerSeries` takes a base `q` with `1 < q`, that the
local factors of a Weierstrass curve require an elliptic curve and a finite residue field, and that
this evidence is supplied automatically at the finite places of a number field, where the residue
field size is the absolute norm.
-/

open ArithmeticFunction IsDedekindDomain IsLocalRing NumberField PowerSeries

noncomputable section

/-! ### `ofPowerSeries` takes evidence that `1 < q` -/

/--
error: Application type mismatch: The argument
  f
has type
  ℤ⟦X⟧
of sort `Type` but is expected to have type
  1 < q
of sort `Prop` in the application
  ofPowerSeries q f
-/
#guard_msgs in
example (q : ℕ) (f : PowerSeries ℤ) : ArithmeticFunction ℤ := ofPowerSeries q f

/--
error: Tactic `decide` proved that the proposition
  1 < 1
is false
-/
#guard_msgs in
example (f : PowerSeries ℤ) : ArithmeticFunction ℤ := ofPowerSeries 1 (by decide) f

/--
error: Tactic `decide` proved that the proposition
  1 < 0
is false
-/
#guard_msgs in
example (f : PowerSeries ℤ) : ArithmeticFunction ℤ := ofPowerSeries 0 (by decide) f

/-! ### Values -/

example (f : PowerSeries ℤ) : ofPowerSeries 2 (by norm_num) f 1 = f.constantCoeff := by simp

-- A composite base that is not a prime power is admissible.
example (f : PowerSeries ℤ) : ofPowerSeries 6 (by norm_num) f (6 ^ 2) = f.coeff 2 :=
  ofPowerSeries_apply_pow _ f 2

example (f : PowerSeries ℤ) : ofPowerSeries 2 (by norm_num) f 3 = 0 := by
  rw [ofPowerSeries_apply, Function.extend_apply', Pi.zero_apply]
  rintro ⟨k, hk⟩
  have h2 : 2 ∣ 3 := by
    rcases k with _ | k
    · simp at hk
    · exact hk ▸ dvd_pow_self 2 k.succ_ne_zero
  omega

example (p : ℕ) (hp : p.Prime) (f : PowerSeries ℤ) (hf : f.constantCoeff = 1) :
    IsMultiplicative (ofPowerSeries p hp.one_lt f) :=
  isMultiplicative_ofPowerSeries_of_isPrimePow hp.isPrimePow f hf

/-! ### Proof independence and rewriting -/

example (q : ℕ) (h₁ h₂ : 1 < q) :
    (ofPowerSeries q h₁ : PowerSeries ℤ →ₐ[ℤ] ArithmeticFunction ℤ) = ofPowerSeries q h₂ :=
  rfl

example (q : ℕ) (h₁ h₂ : 1 < q) (f : PowerSeries ℤ) (k : ℕ) :
    ofPowerSeries q h₁ f (q ^ k) = f.coeff k := by
  rw [ofPowerSeries_apply_pow h₂]

example (q : ℕ) (hq : 1 < q) (hq₂ : 1 < q ^ 2) (f : PowerSeries ℤ) :
    ofPowerSeries (q ^ 2) hq₂ f = ofPowerSeries q hq (f.subst (PowerSeries.X ^ 2)) := by
  rw [ofPowerSeries_pow hq two_ne_zero]

/-! ### Euler products of families -/

example {ι : Type*} (q : ι → ℕ) (hq : ∀ i, 1 < q i) [Northcott q] (f : ι → PowerSeries ℤ)
    (hf : ∀ i, (f i).constantCoeff = 1) (n : ℕ) :
    ∀ᶠ s in Filter.atTop, (∏ i ∈ s, ofPowerSeries (q i) (hq i) (f i)) n =
      eulerProduct (fun i ↦ ofPowerSeries (q i) (hq i) (f i)) n :=
  tendsTo_eulerProduct_ofPowerSeries q hq f hf n

/-! ### Residue fields of the completions at finite places -/

section ResidueField

variable {A : Type*} [CommRing A] [IsDedekindDomain A] {K : Type*} [Field K] [Algebra A K]
  [IsFractionRing A K] (v : HeightOneSpectrum A)

example (a : A) :
    HeightOneSpectrum.adicCompletionIntegers.quotientAlgEquivResidueField K v
      (Ideal.Quotient.mk v.asIdeal a) =
        algebraMap A (ResidueField (v.adicCompletionIntegers K)) a :=
  (HeightOneSpectrum.adicCompletionIntegers.quotientAlgEquivResidueField K v).commutes a

example (K : Type*) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    Finite (ResidueField (v.adicCompletionIntegers K)) :=
  inferInstance

example (K : Type*) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    Nat.card (ResidueField (v.adicCompletionIntegers K)) = Ideal.absNorm v.asIdeal :=
  HeightOneSpectrum.adicCompletionIntegers.natCard_residueField_eq_absNorm K v

-- Without finite quotients there is no ambient evidence: the residue fields of `ℚ[X]` are infinite.
/--
error: failed to synthesize instance of type class
  Finite (ResidueField ↥(HeightOneSpectrum.adicCompletionIntegers (FractionRing (Polynomial ℚ)) w))

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example (w : HeightOneSpectrum (Polynomial ℚ)) :
    Finite (ResidueField (w.adicCompletionIntegers (FractionRing (Polynomial ℚ)))) :=
  inferInstance

end ResidueField

/-! ### Points over finite rings -/

example (S : Type*) [CommRing S] [Finite S] (E : WeierstrassCurve S) : Finite E.toAffine.Point :=
  inferInstance

example (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {L : Type*} [Field L]
    [Algebra R L] [IsFractionRing R L] (E : WeierstrassCurve L) [Finite (ResidueField R)] :
    Finite ((E.minimal R).reduction R).toAffine.Point :=
  inferInstance

/-! ### Local factors need an elliptic curve and a finite residue field -/

section LocalFactor

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {K : Type*} [Field K]
  [Algebra R K] [IsFractionRing R K] (W : WeierstrassCurve K)

/--
error: failed to synthesize instance of type class
  Finite (ResidueField R)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example [W.IsElliptic] : ArithmeticFunction ℤ := W.localEulerFactor R

/--
error: failed to synthesize instance of type class
  W.IsElliptic

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example [Finite (ResidueField R)] : ArithmeticFunction ℤ := W.localEulerFactor R

example [W.IsElliptic] [Finite (ResidueField R)] : W.localEulerFactor R 1 = 1 := by
  simp [WeierstrassCurve.localEulerFactor, WeierstrassCurve.localPowerSeries,
    PowerSeries.constantCoeff_invOfUnit]

-- The nodal cubic `y² + xy = x³` is singular, and its minimal models over `R` have different
-- reduction types, so it has no local polynomial.
example : ¬ (⟨1, 0, 0, 0, 0⟩ : WeierstrassCurve K).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  simp [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]

/--
error: failed to synthesize instance of type class
  { a₁ := 1, a₂ := 0, a₃ := 0, a₄ := 0, a₆ := 0 }.IsElliptic

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example [Finite (ResidueField R)] : Polynomial ℤ :=
  (⟨1, 0, 0, 0, 0⟩ : WeierstrassCurve K).localPolynomial R

-- At the finite places of a number field the evidence is found automatically.
example (K : Type*) [Field K] [NumberField K] (W : WeierstrassCurve K) [W.IsElliptic]
    (p : HeightOneSpectrum (𝓞 K)) : ArithmeticFunction ℤ :=
  (W.baseChange (p.adicCompletion K)).localEulerFactor (p.adicCompletionIntegers K)

end LocalFactor

/-! ### The global L-function and L-series need an elliptic curve -/

section Global

variable (K : Type*) [Field K] [NumberField K] (W : WeierstrassCurve K)

/--
error: failed to synthesize instance of type class
  W.IsElliptic

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example : ArithmeticFunction ℤ := W.LFunction

/--
error: failed to synthesize instance of type class
  W.IsElliptic

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example (s : ℂ) : ℂ := W.LSeries s

example [W.IsElliptic] : ArithmeticFunction ℤ := W.LFunction

example [W.IsElliptic] (s : ℂ) : ℂ := W.LSeries s

end Global

end
