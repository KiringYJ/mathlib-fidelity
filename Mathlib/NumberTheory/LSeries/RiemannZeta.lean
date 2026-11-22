/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.NumberTheory.LSeries.HurwitzZeta
public import Mathlib.Analysis.PSeriesComplex
public import Mathlib.Tactic.CrossRefAttribute

import Mathlib.Tactic.LinearCombination

/-!
# Definition of the Riemann zeta function

## Main definitions:

* `riemannZeta`: the Riemann zeta function on `ℂ \ {1}`.
* `completedRiemannZeta`: the completed zeta function `Λ : ℂ \ {0, 1} → ℂ`, which satisfies
  `Λ(s) = π ^ (-s / 2) Γ(s / 2) ζ(s)` (away from the poles of `Γ(s / 2)`).
* `completedRiemannZeta₀`: the entire function `Λ₀` satisfying
  `Λ₀(s) = Λ(s) + 1 / s - 1 / (s - 1)` wherever the RHS is defined.

The pole exclusions of `ζ` and `Λ` are carried by their evaluation arguments.
The entire function `Λ₀` has defined values at both points.

## Main results:

* `differentiable_completedZeta₀` : the function `Λ₀(s)` is entire.
* `differentiableAt_completedZeta` : the function `Λ(s)` is differentiable away from `s = 0` and
  `s = 1`.
* `differentiableAt_riemannZeta` : the function `ζ(s)` is differentiable away from `s = 1`.
* `zeta_eq_tsum_one_div_nat_add_one_cpow` : for `1 < re s`, we have
  `ζ(s) = ∑' (n : ℕ), 1 / (n + 1) ^ s`.
* `completedRiemannZeta₀_one_sub`, `completedRiemannZeta_one_sub`, and `riemannZeta_one_sub` :
  functional equation relating values at `s` and `1 - s`

For special-value formulae expressing `ζ (2 * k)` and `ζ (1 - 2 * k)` in terms of Bernoulli numbers
see `Mathlib/NumberTheory/LSeries/HurwitzZetaValues.lean`. For computation of the constant term as
`s → 1`, see `Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean`.

## Outline of proofs:

These results are mostly special cases of more general results for even Hurwitz zeta functions
proved in `Mathlib/NumberTheory/LSeries/HurwitzZetaEven.lean`.
-/

@[expose] public section


open CharZero Set Filter HurwitzZeta

open Complex hiding exp continuous_exp

open scoped Topology Real

noncomputable section

/-!
## Definition of the completed Riemann zeta
-/

/-- The completed Riemann zeta function with its poles removed, `Λ(s) + 1 / s - 1 / (s - 1)`. -/
def completedRiemannZeta₀ (s : ℂ) : ℂ := completedHurwitzZetaEven₀ 0 s

/-- The completed Riemann zeta function on its exact domain, excluding zero and one. -/
def completedRiemannZeta (s : ℂ) (hs0 : s ≠ 0 := by checked_nonzero)
    (hs1 : s ≠ 1 := by checked_nonzero) : ℂ :=
  completedHurwitzZetaEven 0 s (hs := ⟨hs1, Or.inl hs0⟩)

lemma HurwitzZeta.completedHurwitzZetaEven_zero (s : ℂ)
    {hs0 : s ≠ 0} {hs1 : s ≠ 1} :
    completedHurwitzZetaEven 0 s (hs := ⟨hs1, Or.inl hs0⟩) = completedRiemannZeta s := rfl

lemma HurwitzZeta.completedHurwitzZetaEven₀_zero (s : ℂ) :
    completedHurwitzZetaEven₀ 0 s = completedRiemannZeta₀ s := rfl

lemma HurwitzZeta.completedCosZeta_zero (s : ℂ)
    {hs0 : s ≠ 0} {hs1 : s ≠ 1} :
    completedCosZeta 0 s (hs := ⟨hs0, Or.inl hs1⟩) = completedRiemannZeta s := by
  simp only [completedRiemannZeta, completedCosZeta_eq, completedHurwitzZetaEven_eq,
    completedCosZeta₀, completedHurwitzZetaEven₀, hurwitzEvenFEPair_zero_symm, ↓reduceDIte]

lemma HurwitzZeta.completedCosZeta₀_zero (s : ℂ) :
    completedCosZeta₀ 0 s = completedRiemannZeta₀ s := by
  rw [completedRiemannZeta₀, completedHurwitzZetaEven₀, completedCosZeta₀,
    hurwitzEvenFEPair_zero_symm]

lemma completedRiemannZeta_eq (s : ℂ)
    {hs0 : s ≠ 0} {hs1 : s ≠ 1} :
    completedRiemannZeta s = completedRiemannZeta₀ s - 1 / s - 1 / (1 - s) := by
  simpa only [completedRiemannZeta, completedRiemannZeta₀, dite_eq_left rfl, ↓reduceDIte] using
    completedHurwitzZetaEven_eq 0 s (hs := ⟨hs1, Or.inl hs0⟩)

/-- The modified completed Riemann zeta function `Λ(s) + 1 / s + 1 / (1 - s)` is entire. -/
theorem differentiable_completedZeta₀ : Differentiable ℂ completedRiemannZeta₀ :=
  differentiable_completedHurwitzZetaEven₀ 0

/-- The completed zeta function is differentiable on its actual domain. -/
theorem differentiableAt_completedZeta {s : ℂ} (hs : s ≠ 0) (hs' : s ≠ 1) :
    DifferentiableAt ℂ
      (fun z : {z : ℂ // z ≠ 0 ∧ z ≠ 1} ↦
        completedRiemannZeta z (hs0 := z.2.1) (hs1 := z.2.2))
      ⟨s, hs, hs'⟩ (fun z ↦ (z : ℂ)) := by
  let φ : {z : ℂ // z ≠ 0 ∧ z ≠ 1} →
      {z : ℂ // z ≠ 1 ∧ (z ≠ 0 ∨ (0 : UnitAddCircle) ≠ 0)} :=
    fun z ↦ ⟨z, z.2.2, Or.inl z.2.1⟩
  obtain ⟨d, hd⟩ := differentiableAt_completedHurwitzZetaEven 0 (Or.inl hs) hs'
  refine ⟨d, HasFDerivAtFilter.comp_tendsto hd φ ?_⟩
  exact (((continuous_subtype_val.subtype_mk _) : Continuous φ).tendsto ⟨s, hs, hs'⟩).prodMap
    (tendsto_pure_pure ..)

/-- Riemann zeta functional equation, formulated for `Λ₀`: for any complex `s` we have
`Λ₀(1 - s) = Λ₀ s`. -/
theorem completedRiemannZeta₀_one_sub (s : ℂ) :
    completedRiemannZeta₀ (1 - s) = completedRiemannZeta₀ s := by
  rw [← completedHurwitzZetaEven₀_zero, ← completedCosZeta₀_zero, completedHurwitzZetaEven₀_one_sub]

/-- Riemann zeta functional equation, formulated for `Λ`: for any complex `s` we have
`Λ (1 - s) = Λ s`. -/
theorem completedRiemannZeta_one_sub (s : ℂ)
    {hs0 : s ≠ 0} {hs1 : s ≠ 1} :
    completedRiemannZeta (1 - s) (hs0 := sub_ne_zero.mpr hs1.symm)
      (hs1 := by intro h; apply hs0; linear_combination -h) = completedRiemannZeta s := by
  rw [← completedHurwitzZetaEven_zero, ← completedCosZeta_zero, completedHurwitzZetaEven_one_sub]

/-- The residue of `Λ(s)` at `s = 1` is equal to `1`. -/
lemma completedRiemannZeta_residue_one :
    Tendsto (fun s : {s : ℂ // s ≠ 0 ∧ s ≠ 1} ↦
      ((s : ℂ) - 1) * completedRiemannZeta s (hs0 := s.2.1) (hs1 := s.2.2))
      (comap Subtype.val (𝓝 1)) (𝓝 1) := by
  let φ : {z : ℂ // z ≠ 0 ∧ z ≠ 1} →
      {z : ℂ // z ≠ 1 ∧ (z ≠ 0 ∨ (0 : UnitAddCircle) ≠ 0)} :=
    fun z ↦ ⟨z, z.2.2, Or.inl z.2.1⟩
  have hφ : Tendsto φ (comap Subtype.val (𝓝 1)) (comap Subtype.val (𝓝 1)) :=
    tendsto_comap_iff.mpr tendsto_comap
  exact (completedHurwitzZetaEven_residue_one 0).comp hφ

/-!
## The un-completed Riemann zeta function
-/

/-- The Riemann zeta function `ζ(s)`. -/
@[wikidata Q187235]
def riemannZeta (s : ℂ) (hs : s ≠ 1 := by checked_nonzero) : ℂ :=
  hurwitzZetaEven 0 s (hs := hs)

lemma HurwitzZeta.hurwitzZetaEven_zero (s : ℂ) {hs : s ≠ 1} :
    hurwitzZetaEven 0 s = riemannZeta s := rfl

lemma HurwitzZeta.cosZeta_zero (s : ℂ) {hs : s ≠ 1} :
    cosZeta 0 s (hs := Or.inl hs) = riemannZeta s := by
  simp only [cosZeta, cosZetaRegularPart, riemannZeta, hurwitzZetaEven,
    hurwitzZetaEvenRegularPart, completedHurwitzZetaEven₀_zero, completedCosZeta₀_zero,
    ↓reduceDIte, ite_true, one_mul]

lemma HurwitzZeta.hurwitzZeta_zero (s : ℂ) {hs : s ≠ 1} :
    hurwitzZeta 0 s = riemannZeta s := by
  simpa [hurwitzZeta, hurwitzZetaEven_zero] using hurwitzZetaOdd_neg 0 s

lemma HurwitzZeta.expZeta_zero (s : ℂ) {hs : s ≠ 1} :
    expZeta 0 s (hs := Or.inl hs) = riemannZeta s := by
  rw [expZeta, cosZeta_zero _ (hs := hs), add_eq_left, mul_eq_zero,
    eq_false_intro I_ne_zero, false_or, ← eq_neg_self_iff, ← sinZeta_neg, neg_zero]

/-- The Riemann zeta function is differentiable on its actual domain. -/
theorem differentiableAt_riemannZeta {s : ℂ} (hs' : s ≠ 1) :
    DifferentiableAt ℂ
      (fun z : {z : ℂ // z ≠ 1} ↦ riemannZeta z (hs := z.2))
      ⟨s, hs'⟩ (fun z ↦ (z : ℂ)) :=
  differentiableAt_hurwitzZetaEven 0 hs'

lemma differentiableOn_riemannZeta :
    DifferentiableOn ℂ (fun z : {z : ℂ // z ≠ 1} ↦ riemannZeta z (hs := z.2))
      Set.univ (fun z ↦ (z : ℂ)) :=
  fun z _ ↦ differentiableWithinAt_univ.mpr (differentiableAt_riemannZeta z.2)

lemma analyticOn_riemannZeta :
    AnalyticOnNhd ℂ (fun z : {z : ℂ // z ≠ 1} ↦ riemannZeta z (hs := z.2))
      Set.univ (fun z ↦ (z : ℂ)) := by
  intro z _
  have hR := ((differentiable_hurwitzZetaEvenRegularPart 0).analyticAt (z : ℂ)).comp_domain
    (g := (Subtype.val : {z : ℂ // z ≠ 1} → ℂ)) (x := z)
  have hq := (differentiable_reciprocalGammaℝ.analyticAt (z : ℂ)).div
    (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr z.2).isUnit
  let φ : {z : ℂ // z ≠ 1} → {z : ℂ // IsUnit (z - 1)} :=
    fun z ↦ ⟨z, (sub_ne_zero.mpr z.2).isUnit⟩
  exact hR.add (hq.comp_domain (g := φ) (x := z))

/-- We have `ζ(0) = -1 / 2`. -/
theorem riemannZeta_zero : riemannZeta 0 = -1 / 2 := by
  simpa [riemannZeta] using hurwitzZetaEven_apply_zero (0 : UnitAddCircle)

lemma riemannZeta_def_of_ne_zero {s : ℂ} (hs : s ≠ 0) {hs1 : s ≠ 1} :
    riemannZeta s = completedRiemannZeta s * reciprocalGammaℝ s := by
  exact hurwitzZetaEven_def_of_ne_or_ne (Or.inr hs)

/-- Definition of zeta using the entire completed zeta and reciprocal Gamma. -/
lemma riemannZeta_eq_completedRiemannZeta₀ {s : ℂ} (hs : s ≠ 0)
    {hs1 : s ≠ 1} :
    riemannZeta s = (completedRiemannZeta₀ s - 1 / s - 1 / (1 - s)) * reciprocalGammaℝ s := by
  rw [riemannZeta_def_of_ne_zero hs, completedRiemannZeta_eq]

/-- A reciprocal-Gamma formula for zeta valid at zero as well. -/
lemma riemannZeta_eq_mul_completedRiemannZeta₀ (s : ℂ)
    {hs : s ≠ 1} :
    riemannZeta s = (s * completedRiemannZeta₀ s - 1 - s / (1 - s)) *
      (π : ℂ) ^ (s / 2) * reciprocalGamma (s / 2 + 1) / 2 := by
  have hp : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  calc
    riemannZeta s = (s * completedRiemannZeta₀ s - 1 - s / (1 - s)) *
        reciprocalGammaℝ (s + 2) / 2 / (π : ℂ) := by
      rw [riemannZeta, hurwitzZetaEven, hurwitzZetaEvenRegularPart,
        reciprocalGammaℝ_eq_self_mul_reciprocalGammaℝ_add_two s]
      simp only [ite_true, one_mul, completedHurwitzZetaEven₀_zero]
      field
    _ = _ := by
      rw [reciprocalGammaℝ, show (s + 2) / 2 = s / 2 + 1 by ring,
        cpow_add _ _ hp, cpow_one]
      field

/-- The trivial zeroes of the zeta function. -/
theorem riemannZeta_neg_two_mul_nat_add_one (n : ℕ) :
    riemannZeta (-2 * (n + 1))
      (hs := by
        intro h
        have hRe := congrArg re h
        norm_num at hRe
        nlinarith [Nat.cast_nonneg (α := ℝ) n]) = 0 :=
  hurwitzZetaEven_neg_two_mul_nat_add_one 0 n

/-- The Riemann zeta functional equation in its cosine form, on the common domain
of the two zeta evaluations and the Gamma factor. -/
theorem riemannZeta_one_sub {s : ℂ} (hs : ∀ n : ℕ, s ≠ -n) (hs' : s ≠ 1) :
    riemannZeta (1 - s) (hs := by simpa using hs 0) =
      2 * (2 * π) ^ (-s) * Gamma s * cos (π * s / 2) * riemannZeta s := by
  rw [riemannZeta, hurwitzZetaEven_one_sub 0 hs (Or.inr hs'), cosZeta_zero _ (hs := hs')]

/-- A formal statement of the **Riemann hypothesis** – constructing a term of this type is worth a
million dollars. -/
@[wikidata Q205966]
def RiemannHypothesis : Prop :=
  ∀ (s : ℂ) (hs : s ≠ 1), riemannZeta s (hs := hs) = 0 →
    (¬∃ n : ℕ, s = -2 * (n + 1)) → s.re = 1 / 2

/-!
## Relating the Mellin transform to the Dirichlet series
-/

theorem completedZeta_eq_tsum_of_one_lt_re {s : ℂ} (hs : 1 < re s) :
    completedRiemannZeta s (hs0 := Complex.ne_zero_of_one_lt_re hs)
      (hs1 := by rintro rfl; simp at hs) =
      (π : ℂ) ^ (-s / 2) * Gamma (s / 2) * ∑' n : ℕ+, 1 / ((n : ℕ) : ℂ) ^ s := by
  have hs1 : s ≠ 1 := by rintro rfl; simp at hs
  have h := (hasSum_nat_completedCosZeta 0 hs).tsum_eq.symm
  simpa only [QuotientAddGroup.mk_zero,
    completedCosZeta_zero _ (hs0 := Complex.ne_zero_of_one_lt_re hs) (hs1 := hs1), Gammaℝ_def,
    mul_zero, zero_mul, Real.cos_zero, ofReal_one, mul_one, mul_one_div₀,
    ← tsum_mul_left] using h

/-- In its half-plane of convergence, zeta is the Dirichlet series over positive integers. -/
theorem zeta_eq_tsum_one_div_nat_cpow {s : ℂ} (hs : 1 < re s) :
    riemannZeta s (hs := by rintro rfl; simp at hs) =
      ∑' n : ℕ+, 1 / ((n : ℕ) : ℂ) ^ s := by
  have hs1 : s ≠ 1 := by rintro rfl; simp at hs
  simpa only [QuotientAddGroup.mk_zero, cosZeta_zero _ (hs := hs1), mul_zero, zero_mul,
    Real.cos_zero, ofReal_one] using (hasSum_nat_cosZeta 0 hs).tsum_eq.symm

/-- The positive-integer Dirichlet series indexed by successors of natural numbers. -/
theorem zeta_eq_tsum_one_div_nat_add_one_cpow {s : ℂ} (hs : 1 < re s) :
    riemannZeta s (hs := by rintro rfl; simp at hs) =
      ∑' n : ℕ, Checked.div 1 ((n + 1 : ℂ) ^ s)
        (cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_add_one_ne_zero n))).isUnit := by
  rw [zeta_eq_tsum_one_div_nat_cpow hs]
  simpa only [Equiv.pnatEquivNat, Equiv.coe_fn_symm_mk, Nat.succPNat_coe, Nat.cast_succ] using
    (Equiv.pnatEquivNat.symm.tsum_eq (fun n ↦ (1 / ((n : ℕ) : ℂ) ^ s))).symm

/-- Special case of `zeta_eq_tsum_one_div_nat_cpow` when the argument is in `ℕ`, so the power
function can be expressed using naïve `pow` rather than `cpow`. -/
theorem zeta_nat_eq_tsum_of_gt_one {k : ℕ} (hk : 1 < k) :
    riemannZeta k (hs := by exact_mod_cast hk.ne') = ∑' n : ℕ+, 1 / ((n : ℕ) : ℂ) ^ k := by
  simp only [zeta_eq_tsum_one_div_nat_cpow
      (by rwa [← ofReal_natCast, ofReal_re, ← Nat.cast_one, Nat.cast_lt] : 1 < re k),
    cpow_natCast]

lemma two_mul_riemannZeta_eq_tsum_int_inv_pow_of_even {k : ℕ} (hk : 2 ≤ k) (hk2 : Even k) :
    2 * riemannZeta k (hs := by exact_mod_cast (show k ≠ 1 by omega)) =
      ∑' n : {n : ℤ // n ≠ 0}, (((n : ℤ) : ℂ) ^ k)⁻¹ := by
  have hk' : 1 < k := by omega
  have hkk : 1 < (k : ℂ).re := by simpa using hk'
  have h := (hasSum_int_cosZeta 0 hkk).mul_left (2 : ℂ)
  have hk1 : (k : ℂ) ≠ 1 := by exact_mod_cast hk'.ne'
  rw [QuotientAddGroup.mk_zero, cosZeta_zero _ (hs := hk1)] at h
  apply Eq.symm
  apply HasSum.tsum_eq
  apply h.congr_fun
  intro n
  have hpow : ((↑|(n : ℤ)| : ℂ) ^ k) = ((n : ℤ) : ℂ) ^ k := by
    rcases abs_choice (n : ℤ) with hn | hn
    · rw [hn]
    · rw [hn, Int.cast_neg, hk2.neg_pow]
  have hinv : (((↑|(n : ℤ)| : ℂ) ^ k))⁻¹ = (((n : ℤ) : ℂ) ^ k)⁻¹ := by
    apply inv_eq_of_mul_eq_one_right₀
    rw [hpow, mul_inv_cancel₀]
  simp only [ofReal_zero, mul_zero, zero_mul, exp_zero, div_eq_mul_inv₀, one_mul, cpow_natCast,
    hinv]
  field

/-- The residue of `ζ(s)` at `s = 1` is equal to 1. -/
lemma riemannZeta_residue_one :
    Tendsto (fun s : {s : ℂ // s ≠ 1} ↦
      ((s : ℂ) - 1) * riemannZeta s (hs := s.2))
      (comap Subtype.val (𝓝 1)) (𝓝 1) :=
  hurwitzZetaEven_residue_one 0

/-- The residue of `ζ(s)` at one, expressed by its convergent Dirichlet series. -/
theorem tendsto_sub_mul_tsum_nat_cpow :
    Tendsto (fun s : {s : ℂ // 1 < re s} ↦
      ((s : ℂ) - 1) * ∑' n : ℕ+, 1 / ((n : ℕ) : ℂ) ^ (s : ℂ))
      (comap Subtype.val (𝓝 1)) (𝓝 1) := by
  let φ : {s : ℂ // 1 < re s} → {s : ℂ // s ≠ 1} :=
    fun s ↦ ⟨s, by intro h; simpa [h] using s.2⟩
  have hφ : Tendsto φ (comap Subtype.val (𝓝 1)) (comap Subtype.val (𝓝 1)) :=
    tendsto_comap_iff.mpr tendsto_comap
  apply (riemannZeta_residue_one.comp hφ).congr
  intro s
  exact congrArg (((s : ℂ) - 1) * ·) (zeta_eq_tsum_one_div_nat_cpow s.2)

/-- The residue of `ζ(s)` at one, for a real variable and the positive-integer series. -/
theorem tendsto_sub_mul_tsum_nat_rpow :
    Tendsto (fun s : {s : ℝ // 1 < s} ↦
      ((s : ℝ) - 1) * ∑' n : ℕ+, 1 / ((n : ℕ) : ℝ) ^ (s : ℝ))
      (comap Subtype.val (𝓝 1)) (𝓝 1) := by
  rw [← tendsto_ofReal_iff, ofReal_one]
  let φ : {s : ℝ // 1 < s} → {s : ℂ // 1 < re s} := fun s ↦ ⟨s, by simpa using s.2⟩
  have hφ : Tendsto φ (comap Subtype.val (𝓝 1)) (comap Subtype.val (𝓝 1)) :=
    tendsto_comap_iff.mpr ((continuous_ofReal.tendsto 1).comp tendsto_comap)
  apply (tendsto_sub_mul_tsum_nat_cpow.comp hφ).congr
  intro s
  simp only [φ, one_div₀, Function.comp_apply, ofReal_mul, ofReal_sub, ofReal_one,
    ofReal_tsum, ofReal_inv, ofReal_cpow (Nat.cast_nonneg _), ofReal_natCast]
