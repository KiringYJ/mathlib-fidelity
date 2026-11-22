/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.NumberTheory.LSeries.AbstractFuncEq
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
public import Mathlib.NumberTheory.LSeries.Basic
public import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Even Hurwitz zeta functions

In this file we study the functions on `ℂ` which are the meromorphic continuation of the following
series (convergent for `1 < re s`), where `a ∈ ℝ` is a parameter:

`hurwitzZetaEven a s = 1 / 2 * ∑' n : ℤ, 1 / |n + a| ^ s`

and

`cosZeta a s = ∑' n : ℕ, cos (2 * π * a * n) / |n| ^ s`.

Note that the term for `n = -a` in the first sum is omitted if `a` is an integer, and the term for
`n = 0` is omitted in the second sum (always).

Of course, we cannot *define* these functions by the above formulae (since existence of the
meromorphic continuation is not at all obvious); we in fact construct them as Mellin transforms of
various versions of the Jacobi theta function.

We also define completed versions of these functions with nicer functional equations (satisfying
`completedHurwitzZetaEven a s = Gammaℝ s * hurwitzZetaEven a s`, and similarly for `cosZeta`); and
modified versions with a subscript `0`, which are entire functions differing from the above by
multiples of `1 / s` and `1 / (1 - s)`.

## Main definitions and theorems
* `hurwitzZetaEven` and `cosZeta`: the zeta functions
* `completedHurwitzZetaEven` and `completedCosZeta`: completed variants
* `differentiableAt_hurwitzZetaEven` and `differentiableAt_cosZeta`:
  differentiability away from `s = 1`
* `completedHurwitzZetaEven_one_sub`: the functional equation
  `completedHurwitzZetaEven a (1 - s) = completedCosZeta a s`
* `hasSum_int_hurwitzZetaEven` and `hasSum_nat_cosZeta`: relation between the zeta functions and
  the corresponding Dirichlet series for `1 < re s`.
-/

@[expose] public section
noncomputable section

open Complex Filter Asymptotics Real Set MeasureTheory

open scoped Topology

namespace HurwitzZeta

section kernel_defs
/-!
## Definitions and elementary properties of kernels
-/

/-- Even Hurwitz zeta kernel (function whose Mellin transform will be the even part of the
completed Hurwitz zeta function). See `evenKernel_def` for the defining formula, and
`hasSum_int_evenKernel` for an expression as a sum over `ℤ`. -/
@[irreducible] def evenKernel (a : UnitAddCircle) (x : ℝ) : ℝ :=
  (show Function.Periodic
    (fun ξ : ℝ ↦ rexp (-π * ξ ^ 2 * x) * re (jacobiTheta₂ (ξ * I * x) (I * x))) 1 by
      intro ξ
      simp only [ofReal_add, ofReal_one, add_mul, one_mul, jacobiTheta₂_add_left']
      have : cexp (-↑π * I * ((I * ↑x) + 2 * (↑ξ * I * ↑x))) = rexp (π * (x + 2 * ξ * x)) := by
        ring_nf
        simp [I_sq]
      rw [this, re_ofReal_mul, ← mul_assoc, ← Real.exp_add]
      congr
      ring).lift a

lemma evenKernel_def (a x : ℝ) :
    ↑(evenKernel ↑a x) = cexp (-π * a ^ 2 * x) * jacobiTheta₂ (a * I * x) (I * x) := by
  simp [evenKernel, re_eq_add_conj, jacobiTheta₂_conj, ← mul_two,
    mul_div_cancel_right₀ _ (hb := (two_ne_zero' ℂ).isUnit)]

/-- For `x ≤ 0` the defining sum diverges, so the kernel is 0. -/
lemma evenKernel_undef (a : UnitAddCircle) {x : ℝ} (hx : x ≤ 0) : evenKernel a x = 0 := by
  induction a using QuotientAddGroup.induction_on with
  | H a' => simp [← ofReal_inj, evenKernel_def, jacobiTheta₂_undef _ (by simpa : (I * ↑x).im ≤ 0)]

/-- Cosine Hurwitz zeta kernel. See `cosKernel_def` for the defining formula, and
`hasSum_int_cosKernel` for expression as a sum. -/
@[irreducible] def cosKernel (a : UnitAddCircle) (x : ℝ) : ℝ :=
  (show Function.Periodic (fun ξ : ℝ ↦ re (jacobiTheta₂ ξ (I * x))) 1 by
    intro ξ; simp [jacobiTheta₂_add_left]).lift a

lemma cosKernel_def (a x : ℝ) : ↑(cosKernel ↑a x) = jacobiTheta₂ a (I * x) := by
  simp [cosKernel, re_eq_add_conj, jacobiTheta₂_conj, ← mul_two,
    mul_div_cancel_right₀ _ (hb := (two_ne_zero' ℂ).isUnit)]

lemma cosKernel_undef (a : UnitAddCircle) {x : ℝ} (hx : x ≤ 0) : cosKernel a x = 0 := by
  induction a using QuotientAddGroup.induction_on with
  | H => simp [← ofReal_inj, cosKernel_def, jacobiTheta₂_undef _ (by simpa : (I * ↑x).im ≤ 0)]

/-- For `a = 0`, both kernels agree. -/
lemma evenKernel_eq_cosKernel_of_zero : evenKernel 0 = cosKernel 0 := by
  ext1 x
  simp [← QuotientAddGroup.mk_zero, ← ofReal_inj, evenKernel_def, cosKernel_def]

@[simp]
lemma evenKernel_neg (a : UnitAddCircle) (x : ℝ) : evenKernel (-a) x = evenKernel a x := by
  induction a using QuotientAddGroup.induction_on with
  | H => simp [← QuotientAddGroup.mk_neg, ← ofReal_inj, evenKernel_def, jacobiTheta₂_neg_left]

@[simp]
lemma cosKernel_neg (a : UnitAddCircle) (x : ℝ) : cosKernel (-a) x = cosKernel a x := by
  induction a using QuotientAddGroup.induction_on with
  | H => simp [← QuotientAddGroup.mk_neg, ← ofReal_inj, cosKernel_def]

lemma continuousOn_evenKernel (a : UnitAddCircle) : ContinuousOn (evenKernel a) (Ioi 0) := by
  induction a using QuotientAddGroup.induction_on with | H a' =>
  apply continuous_re.comp_continuousOn (f := fun x ↦ (evenKernel a' x : ℂ))
  simp only [evenKernel_def]
  refine continuousOn_of_forall_continuousAt (fun x hx ↦ .mul (by fun_prop) ?_)
  exact (continuousAt_jacobiTheta₂ (a' * I * x) <| by simpa).comp
    (f := fun u : ℝ ↦ (a' * I * u, I * u)) (by fun_prop)

lemma continuousOn_cosKernel (a : UnitAddCircle) : ContinuousOn (cosKernel a) (Ioi 0) := by
  induction a using QuotientAddGroup.induction_on with | H a' =>
  apply continuous_re.comp_continuousOn (f := fun x ↦ (cosKernel a' x : ℂ))
  simp only [cosKernel_def]
  refine continuousOn_of_forall_continuousAt (fun x hx ↦ ?_)
  exact (continuousAt_jacobiTheta₂ a' <| by simpa).comp
    (f := fun u : ℝ ↦ ((a' : ℂ), I * u)) (by fun_prop)

lemma evenKernel_functional_equation (a : UnitAddCircle) (x : ℝ) (hx : 0 < x) :
    evenKernel a x = Checked.div 1 (x ^ (1 / 2 : ℝ))
      (Real.rpow_ne_zero_of_pos hx _).isUnit * cosKernel a (1 / x) := by
  induction a using QuotientAddGroup.induction_on with | H a =>
  have hx' : I * x ≠ 0 := mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr hx.ne')
  have hbase : IsUnit (-I * (I * x)) := (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hx').isUnit
  have h1 : I * ↑(1 / x) = -1 / (I * x) := by
    apply eq_div_iff.mpr
    rw [mul_mul_mul_comm, I_mul_I, ← ofReal_mul, div_mul_cancel₀, ofReal_one, mul_one]
  have h2 : a * I * x / (I * x) = a := by
    rw [div_eq_iff]
    ring
  have h3 : 1 / (-I * (I * x)) ^ (1 / 2 : ℂ) = 1 / ↑(x ^ (1 / 2 : ℝ)) := by
    simp only [one_div₀]
    apply inv_inj₀.mpr
    rw [neg_mul, ← mul_assoc, I_mul_I, neg_one_mul, neg_neg, ofReal_cpow hx.le]
    congr 1
    rw [ofReal_inv]
    exact inv_inj₀.mpr (ofReal_ofNat 2).symm
  have h4 : -π * I * (a * I * x) ^ 2 / (I * x) = - (-π * a ^ 2 * x) := by
    rw [mul_pow, mul_pow, I_sq, div_eq_iff]
    ring
  rw [← ofReal_inj, ofReal_mul, evenKernel_def, cosKernel_def,
    jacobiTheta₂_functional_equation _ _ (by rw [I_mul_im, ofReal_re]; exact hx),
    h1, h2, h3, h4, ← mul_assoc, mul_comm (cexp _), mul_assoc _ (cexp _) (cexp _),
    ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one, ofReal_div, ofReal_one]

end kernel_defs

section asymp

/-!
## Formulae for the kernels as sums
-/

lemma hasSum_int_evenKernel (a : ℝ) {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℤ ↦ rexp (-π * (n + a) ^ 2 * t)) (evenKernel a t) := by
  rw [← hasSum_ofReal, evenKernel_def]
  have (n : ℤ) : cexp (-(π * (n + a) ^ 2 * t)) = cexp (-(π * a ^ 2 * t)) *
      jacobiTheta₂_term n (a * I * t) (I * t) := by
    rw [jacobiTheta₂_term, ← Complex.exp_add]
    grind [I_sq]
  simpa [this] using (hasSum_jacobiTheta₂_term _ (by simpa)).mul_left _

lemma hasSum_int_cosKernel (a : ℝ) {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℤ ↦ cexp (2 * π * I * a * n) * rexp (-π * n ^ 2 * t)) ↑(cosKernel a t) := by
  rw [cosKernel_def a t]
  have (n : ℤ) : cexp (2 * π * I * a * n) * cexp (-(π * n ^ 2 * t)) =
      jacobiTheta₂_term n a (I * ↑t) := by
    rw [jacobiTheta₂_term, ← Complex.exp_add]
    ring_nf
    simp [sub_eq_add_neg]
  simpa [this] using hasSum_jacobiTheta₂_term _ (by simpa)

/-- Modified version of `hasSum_int_evenKernel` omitting the constant term at `∞`. -/
lemma hasSum_int_evenKernel₀ (a : ℝ) {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℤ ↦ if n + a = 0 then 0 else rexp (-π * (n + a) ^ 2 * t))
    (evenKernel a t - if (a : UnitAddCircle) = 0 then 1 else 0) := by
  have := Classical.propDecidable -- speed up instance search for `if / then / else`
  simp_rw [AddCircle.coe_eq_zero_iff, zsmul_one]
  split_ifs with h
  · obtain ⟨k, rfl⟩ := h
    simpa [← Int.cast_add, add_eq_zero_iff_eq_neg]
      using hasSum_ite_sub_hasSum (hasSum_int_evenKernel (k : ℝ) ht) (-k)
  · suffices ∀ (n : ℤ), n + a ≠ 0 by simpa [this] using hasSum_int_evenKernel a ht
    contrapose! h
    let ⟨n, hn⟩ := h
    exact ⟨-n, by simpa [neg_eq_iff_add_eq_zero]⟩

lemma hasSum_int_cosKernel₀ (a : ℝ) {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℤ ↦ if n = 0 then 0 else cexp (2 * π * I * a * n) * rexp (-π * n ^ 2 * t))
    (↑(cosKernel a t) - 1) := by
  simpa using hasSum_ite_sub_hasSum (hasSum_int_cosKernel a ht) 0

lemma hasSum_nat_cosKernel₀ (a : ℝ) {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ ↦ 2 * Real.cos (2 * π * a * (n + 1)) * rexp (-π * (n + 1) ^ 2 * t))
    (cosKernel a t - 1) := by
  rw [← hasSum_ofReal, ofReal_sub, ofReal_one]
  have := (hasSum_int_cosKernel a ht).nat_add_neg
  rw [← hasSum_nat_add_iff' 1] at this
  simp_rw [Finset.sum_range_one, Nat.cast_zero, neg_zero, Int.cast_zero, zero_pow two_ne_zero,
    mul_zero, zero_mul, Complex.exp_zero, Real.exp_zero, ofReal_one, mul_one, Int.cast_neg,
    Int.cast_natCast, neg_sq, ← add_mul, add_sub_assoc, ← sub_sub, sub_self, zero_sub,
    ← sub_eq_add_neg, mul_neg] at this
  refine this.congr_fun fun n ↦ ?_
  push_cast
  rw [Complex.cos, mul_div_cancel₀ _ (hb := two_ne_zero.isUnit)]
  congr 3 <;> ring

/-!
## Asymptotics of the kernels as `t → ∞`
-/

/-- The function `evenKernel a - L` has exponential decay at `+∞`, where `L = 1` if
`a = 0` and `L = 0` otherwise. -/
lemma isBigO_atTop_evenKernel_sub (a : UnitAddCircle) : ∃ p : ℝ, 0 < p ∧
    (evenKernel a · - (if a = 0 then 1 else 0)) =O[atTop] (rexp <| -p * ·) := by
  induction a using QuotientAddGroup.induction_on with | H b =>
  obtain ⟨p, hp, hp'⟩ := HurwitzKernelBounds.isBigO_atTop_F_int_zero_sub b
  refine ⟨p, hp, (EventuallyEq.isBigO ?_).trans hp'⟩
  filter_upwards [eventually_gt_atTop 0] with t h
  simp [← (hasSum_int_evenKernel b h).tsum_eq, HurwitzKernelBounds.F_int, HurwitzKernelBounds.f_int]

/-- The function `cosKernel a - 1` has exponential decay at `+∞`, for any `a`. -/
lemma isBigO_atTop_cosKernel_sub (a : UnitAddCircle) :
    ∃ p, 0 < p ∧ IsBigO atTop (cosKernel a · - 1) (fun x ↦ Real.exp (-p * x)) := by
  induction a using QuotientAddGroup.induction_on with | H a =>
  obtain ⟨p, hp, hp'⟩ := HurwitzKernelBounds.isBigO_atTop_F_nat_zero_sub zero_le_one
  refine ⟨p, hp, (Eventually.isBigO ?_).trans (hp'.const_mul_left 2)⟩
  filter_upwards [eventually_gt_atTop 0] with t ht
  simp only [eq_false_intro one_ne_zero, ite_false, sub_zero,
    ← (hasSum_nat_cosKernel₀ a ht).tsum_eq, HurwitzKernelBounds.F_nat]
  apply tsum_of_norm_bounded ((HurwitzKernelBounds.summable_f_nat 0 1 ht).hasSum.mul_left 2)
  intro n
  rw [norm_mul, norm_mul, norm_two, mul_assoc, mul_le_mul_iff_of_pos_left two_pos,
    norm_of_nonneg (exp_pos _).le, HurwitzKernelBounds.f_nat, pow_zero, one_mul, Real.norm_eq_abs]
  exact mul_le_of_le_one_left (exp_pos _).le (abs_cos_le_one _)

end asymp

section FEPair
/-!
## Construction of an FE-pair
-/

/-- A `WeakFEPair` structure with `f = evenKernel a` and `g = cosKernel a`. -/
def hurwitzEvenFEPair (a : UnitAddCircle) : WeakFEPair ℂ where
  f := ofReal ∘ evenKernel a
  g := ofReal ∘ cosKernel a
  hf_int := (continuous_ofReal.comp_continuousOn (continuousOn_evenKernel a)).locallyIntegrableOn
    measurableSet_Ioi
  hg_int := (continuous_ofReal.comp_continuousOn (continuousOn_cosKernel a)).locallyIntegrableOn
    measurableSet_Ioi
  k := 1 / 2
  hk := one_half_pos
  ε := 1
  hε := one_ne_zero
  f₀ := if a = 0 then 1 else 0
  hf_top r := by
    let ⟨v, hv, hv'⟩ := isBigO_atTop_evenKernel_sub a
    rw [← isBigO_norm_left] at hv' ⊢
    conv at hv' =>
      enter [2, x]; rw [← norm_real, ofReal_sub, apply_ite ((↑) : ℝ → ℂ), ofReal_one, ofReal_zero]
    exact hv'.trans (isLittleO_exp_neg_mul_rpow_atTop hv _).isBigO
  g₀ := 1
  hg_top r := by
    obtain ⟨p, hp, hp'⟩ := isBigO_atTop_cosKernel_sub a
    simpa using isBigO_ofReal_left.mpr <| hp'.trans (isLittleO_exp_neg_mul_rpow_atTop hp r).isBigO
  h_feq x hx := by
    have heq := evenKernel_functional_equation a (1 / x) (one_div_pos.mpr hx)
    simpa only [one_div₀, inv_inv₀, inv_rpow hx.le, ofReal_mul, Function.comp_apply,
      smul_eq_mul, one_mul] using congrArg ofReal heq

@[simp]
lemma hurwitzEvenFEPair_zero_symm :
    (hurwitzEvenFEPair 0).symm = hurwitzEvenFEPair 0 := by
  unfold hurwitzEvenFEPair WeakFEPair.symm
  congr 1 <;> simp [evenKernel_eq_cosKernel_of_zero]

@[simp]
lemma hurwitzEvenFEPair_neg (a : UnitAddCircle) : hurwitzEvenFEPair (-a) = hurwitzEvenFEPair a := by
  unfold hurwitzEvenFEPair
  congr 1 <;> simp [Function.comp_def]

/-!
## Definition of the completed even Hurwitz zeta function
-/

/--
The meromorphic function of `s` which agrees with
`1 / 2 * Gamma (s / 2) * π ^ (-s / 2) * ∑' (n : ℤ), 1 / |n + a| ^ s` for `1 < re s`.
-/
def completedHurwitzZetaEven (a : UnitAddCircle) (s : ℂ)
    (hs : s ≠ 1 ∧ (s ≠ 0 ∨ a ≠ 0) := by assumption) : ℂ :=
  ((hurwitzEvenFEPair a).Λ ⟨s / 2, by
    constructor
    · rcases hs.2 with h | h
      · exact Or.inl (div_ne_zero h)
      · exact Or.inr (by simp [hurwitzEvenFEPair, h])
    · left
      change s / 2 ≠ ↑(1 / 2 : ℝ)
      intro h
      apply hs.1
      push_cast at h
      linear_combination 2 * h⟩) / 2

/-- The entire function differing from `completedHurwitzZetaEven a s` by a linear combination of
`1 / s` and `1 / (1 - s)`. -/
def completedHurwitzZetaEven₀ (a : UnitAddCircle) (s : ℂ) : ℂ :=
  ((hurwitzEvenFEPair a).Λ₀ (s / 2)) / 2

lemma completedHurwitzZetaEven_eq (a : UnitAddCircle) (s : ℂ)
    {hs : s ≠ 1 ∧ (s ≠ 0 ∨ a ≠ 0)} :
    completedHurwitzZetaEven a s = completedHurwitzZetaEven₀ a s -
      (if ha : a = 0 then Checked.div 1 s
        (hs.2.resolve_right (fun h ↦ h ha)).isUnit
        else 0) - Checked.div 1 (1 - s) (sub_ne_zero.mpr hs.1.symm).isUnit := by
  classical
  by_cases ha : a = 0
  · have hs0 : s ≠ 0 := hs.2.resolve_right (fun h ↦ h ha)
    simp [completedHurwitzZetaEven, completedHurwitzZetaEven₀, WeakFEPair.Λ,
      hurwitzEvenFEPair, ha]
    field
  · simp [completedHurwitzZetaEven, completedHurwitzZetaEven₀, WeakFEPair.Λ,
      hurwitzEvenFEPair, ha]
    field

/--
The meromorphic function of `s` which agrees with
`Gamma (s / 2) * π ^ (-s / 2) * ∑' n : ℕ, cos (2 * π * a * n) / n ^ s` for `1 < re s`.
-/
def completedCosZeta (a : UnitAddCircle) (s : ℂ)
    (hs : s ≠ 0 ∧ (s ≠ 1 ∨ a ≠ 0) := by assumption) : ℂ :=
  ((hurwitzEvenFEPair a).symm.Λ ⟨s / 2, by
    constructor
    · exact Or.inl (div_ne_zero hs.1)
    · rcases hs.2 with h | h
      · left
        change s / 2 ≠ ↑(1 / 2 : ℝ)
        intro h'
        apply h
        push_cast at h'
        linear_combination 2 * h'
      · exact Or.inr (by simp [WeakFEPair.symm, hurwitzEvenFEPair, h])⟩) / 2

/-- The entire function differing from `completedCosZeta a s` by a linear combination of
`1 / s` and `1 / (1 - s)`. -/
def completedCosZeta₀ (a : UnitAddCircle) (s : ℂ) : ℂ :=
  ((hurwitzEvenFEPair a).symm.Λ₀ (s / 2)) / 2

lemma completedCosZeta_eq (a : UnitAddCircle) (s : ℂ)
    {hs : s ≠ 0 ∧ (s ≠ 1 ∨ a ≠ 0)} :
    completedCosZeta a s = completedCosZeta₀ a s - Checked.div 1 s hs.1.isUnit -
      (if ha : a = 0 then Checked.div 1 (1 - s)
        (sub_ne_zero.mpr (hs.2.resolve_right (fun h ↦ h ha)).symm).isUnit else 0) := by
  classical
  by_cases ha : a = 0
  · have hs1 : s ≠ 1 := hs.2.resolve_right (fun h ↦ h ha)
    simp [completedCosZeta, completedCosZeta₀, WeakFEPair.Λ, WeakFEPair.symm,
      hurwitzEvenFEPair, ha]
    field
  · simp [completedCosZeta, completedCosZeta₀, WeakFEPair.Λ, WeakFEPair.symm,
      hurwitzEvenFEPair, ha]
    field

/-!
## Parity and functional equations
-/

@[simp]
lemma completedHurwitzZetaEven_neg (a : UnitAddCircle) (s : ℂ)
    {hs : s ≠ 1 ∧ (s ≠ 0 ∨ a ≠ 0)} :
    completedHurwitzZetaEven (-a) s
      (hs := ⟨hs.1, hs.2.imp_right (fun h ↦ neg_ne_zero.mpr h)⟩) =
        completedHurwitzZetaEven a s := by
  simp only [completedHurwitzZetaEven_eq, completedHurwitzZetaEven₀, hurwitzEvenFEPair_neg,
    neg_eq_zero]

@[simp]
lemma completedHurwitzZetaEven₀_neg (a : UnitAddCircle) (s : ℂ) :
    completedHurwitzZetaEven₀ (-a) s = completedHurwitzZetaEven₀ a s := by
  simp [completedHurwitzZetaEven₀]

@[simp]
lemma completedCosZeta_neg (a : UnitAddCircle) (s : ℂ)
    {hs : s ≠ 0 ∧ (s ≠ 1 ∨ a ≠ 0)} :
    completedCosZeta (-a) s
      (hs := ⟨hs.1, hs.2.imp_right (fun h ↦ neg_ne_zero.mpr h)⟩) = completedCosZeta a s := by
  simp only [completedCosZeta_eq, completedCosZeta₀, hurwitzEvenFEPair_neg, neg_eq_zero]

@[simp]
lemma completedCosZeta₀_neg (a : UnitAddCircle) (s : ℂ) :
    completedCosZeta₀ (-a) s = completedCosZeta₀ a s := by
  simp [completedCosZeta₀]

/-- Functional equation for the even Hurwitz zeta function with poles removed. -/
lemma completedHurwitzZetaEven₀_one_sub (a : UnitAddCircle) (s : ℂ) :
    completedHurwitzZetaEven₀ a (1 - s) = completedCosZeta₀ a s := by
  rw [completedHurwitzZetaEven₀, completedCosZeta₀, sub_div,
    (by simp : (1 / 2 : ℂ) = ↑(1 / 2 : ℝ)),
    (by rfl : (1 / 2 : ℝ) = (hurwitzEvenFEPair a).k),
    (hurwitzEvenFEPair a).functional_equation₀ (s / 2),
    (by rfl : (hurwitzEvenFEPair a).ε = 1), one_smul]

/-- Functional equation with poles removed, in the reverse direction. -/
lemma completedCosZeta₀_one_sub (a : UnitAddCircle) (s : ℂ) :
    completedCosZeta₀ a (1 - s) = completedHurwitzZetaEven₀ a s := by
  rw [← completedHurwitzZetaEven₀_one_sub, sub_sub_cancel]

/-- Functional equation for completed even Hurwitz zeta on its regular domain. -/
lemma completedHurwitzZetaEven_one_sub (a : UnitAddCircle) (s : ℂ)
    {hs : s ≠ 0 ∧ (s ≠ 1 ∨ a ≠ 0)} :
    completedHurwitzZetaEven a (1 - s)
      (hs := ⟨by intro h; apply hs.1; linear_combination -h,
        hs.2.imp_left (fun h ↦ sub_ne_zero.mpr h.symm)⟩) = completedCosZeta a s := by
  rw [completedHurwitzZetaEven_eq, completedCosZeta_eq, completedHurwitzZetaEven₀_one_sub]
  split_ifs <;> field

/-- The completed functional equation in the reverse direction, on its regular domain. -/
lemma completedCosZeta_one_sub (a : UnitAddCircle) (s : ℂ)
    {hs : s ≠ 1 ∧ (s ≠ 0 ∨ a ≠ 0)} :
    completedCosZeta a (1 - s)
      (hs := ⟨sub_ne_zero.mpr hs.1.symm,
        hs.2.imp_left (by intro h heq; apply h; linear_combination -heq)⟩) =
      completedHurwitzZetaEven a s := by
  rw [completedCosZeta_eq, completedHurwitzZetaEven_eq, completedCosZeta₀_one_sub]
  split_ifs <;> field

end FEPair

/-!
## Differentiability and residues
-/

section FEPair

/--
The even Hurwitz completed zeta is differentiable away from `s = 0` and `s = 1` (and also at
`s = 0` if `a ≠ 0`)
-/
lemma differentiableAt_completedHurwitzZetaEven
    (a : UnitAddCircle) {s : ℂ} (hs : s ≠ 0 ∨ a ≠ 0) (hs' : s ≠ 1) :
    DifferentiableAt ℂ
      (fun z : {z : ℂ // z ≠ 1 ∧ (z ≠ 0 ∨ a ≠ 0)} ↦
        completedHurwitzZetaEven a z (hs := z.2))
      ⟨s, hs', hs⟩ Subtype.val := by
  let P := hurwitzEvenFEPair a
  let D := {z : ℂ // z ≠ 1 ∧ (z ≠ 0 ∨ a ≠ 0)}
  let φ : D → {z : ℂ // (z ≠ 0 ∨ P.f₀ = 0) ∧ (z ≠ P.k ∨ P.ε • P.g₀ = 0)} :=
    fun z ↦ ⟨(z : ℂ) / 2, by
      constructor
      · rcases z.2.2 with h | h
        · exact Or.inl (div_ne_zero h)
        · exact Or.inr (by simp [P, hurwitzEvenFEPair, h])
      · left
        change (z : ℂ) / 2 ≠ ↑(1 / 2 : ℝ)
        intro h
        apply z.2.1
        push_cast at h
        linear_combination 2 * h⟩
  obtain ⟨f', hf'⟩ :=
    (show DifferentiableAt ℂ (fun z : ℂ ↦ z / 2) s from
      differentiableAt_id.div_const 2 (hd := two_ne_zero.isUnit))
  have hφ : HasFDerivAt (fun z : D ↦ (z : ℂ) / 2) f' ⟨s, hs', hs⟩ Subtype.val :=
    hf'.comp_tendsto Subtype.val
      ((continuous_subtype_val.tendsto ⟨s, hs', hs⟩).prodMap (tendsto_pure_pure ..))
  obtain ⟨g', hg'⟩ := P.differentiableAt_Λ (φ ⟨s, hs', hs⟩)
  have hcomp := hg'.comp ⟨s, hs', hs⟩ hφ
    continuous_subtype_val.continuousAt Topology.IsEmbedding.subtypeVal
  obtain ⟨l', hl'⟩ := (show DifferentiableAt ℂ (fun w : ℂ ↦ w / 2)
      (P.Λ (φ ⟨s, hs', hs⟩)) from differentiableAt_id.div_const 2 (hd := two_ne_zero.isUnit))
  exact
    (hl'.comp ⟨s, hs', hs⟩ hcomp continuous_subtype_val.continuousAt
      Topology.IsEmbedding.id).differentiableAt

lemma differentiable_completedHurwitzZetaEven₀ (a : UnitAddCircle) :
    Differentiable ℂ (completedHurwitzZetaEven₀ a) :=
  ((hurwitzEvenFEPair a).differentiable_Λ₀.comp (differentiable_id.div_const _)).div_const _

/-- Removing the common pole at one from a difference of completed even Hurwitz zeta
functions gives a differentiable local function. Its formula is evaluated on the nonzero
neighborhood of one, where the remaining pole terms have their actual domains. -/
lemma differentiableAt_one_completedHurwitzZetaEvenRegularPart_sub (a b : UnitAddCircle) :
    DifferentiableAt ℂ
      (fun s : {s : ℂ // s ≠ 0} ↦ completedHurwitzZetaEven₀ a s -
        completedHurwitzZetaEven₀ b s -
        ((if a = 0 then 1 else 0) - (if b = 0 then 1 else 0)) / (s : ℂ))
      ⟨1, one_ne_zero⟩ Subtype.val := by
  let c : ℂ := (if a = 0 then 1 else 0) - (if b = 0 then 1 else 0)
  have hR := (differentiable_completedHurwitzZetaEven₀ a 1).sub
    (differentiable_completedHurwitzZetaEven₀ b 1)
  obtain ⟨r', hr'⟩ := hR
  have hR' : DifferentiableAt ℂ
      (fun s : {s : ℂ // s ≠ 0} ↦ completedHurwitzZetaEven₀ a s - completedHurwitzZetaEven₀ b s)
      ⟨1, one_ne_zero⟩ Subtype.val :=
    ⟨r', hr'.comp_tendsto Subtype.val
      ((continuous_subtype_val.tendsto ⟨1, one_ne_zero⟩).prodMap (tendsto_pure_pure ..))⟩
  have hq := (differentiableAt_const c).div differentiableAt_id isUnit_one
  let φ : {s : ℂ // s ≠ 0} → {s : ℂ // IsUnit s} := fun s ↦ ⟨s, s.2.isUnit⟩
  have hφ : Continuous φ := continuous_subtype_val.subtype_mk _
  obtain ⟨q', hq'⟩ := hq
  have hq'' : DifferentiableAt ℂ (fun s : {s : ℂ // s ≠ 0} ↦ c / (s : ℂ))
      ⟨1, one_ne_zero⟩ Subtype.val :=
    ⟨q', hq'.comp_tendsto φ
      ((hφ.tendsto ⟨1, one_ne_zero⟩).prodMap (tendsto_pure_pure ..))⟩
  exact hR'.sub hq''

lemma differentiableAt_completedCosZeta
    (a : UnitAddCircle) {s : ℂ} (hs : s ≠ 0) (hs' : s ≠ 1 ∨ a ≠ 0) :
    DifferentiableAt ℂ
      (fun z : {z : ℂ // z ≠ 0 ∧ (z ≠ 1 ∨ a ≠ 0)} ↦ completedCosZeta a z (hs := z.2))
      ⟨s, hs, hs'⟩ Subtype.val := by
  let P := (hurwitzEvenFEPair a).symm
  let D := {z : ℂ // z ≠ 0 ∧ (z ≠ 1 ∨ a ≠ 0)}
  let φ : D → {z : ℂ // (z ≠ 0 ∨ P.f₀ = 0) ∧ (z ≠ P.k ∨ P.ε • P.g₀ = 0)} :=
    fun z ↦ ⟨(z : ℂ) / 2, by
      constructor
      · exact Or.inl (div_ne_zero z.2.1)
      · rcases z.2.2 with h | h
        · left
          change (z : ℂ) / 2 ≠ ↑(1 / 2 : ℝ)
          intro h'
          apply h
          push_cast at h'
          linear_combination 2 * h'
        · exact Or.inr (by simp [P, WeakFEPair.symm, hurwitzEvenFEPair, h])⟩
  obtain ⟨f', hf'⟩ :=
    (show DifferentiableAt ℂ (fun z : ℂ ↦ z / 2) s from
      differentiableAt_id.div_const 2 (hd := two_ne_zero.isUnit))
  have hφ : HasFDerivAt (fun z : D ↦ (z : ℂ) / 2) f' ⟨s, hs, hs'⟩ Subtype.val :=
    hf'.comp_tendsto Subtype.val
      ((continuous_subtype_val.tendsto ⟨s, hs, hs'⟩).prodMap (tendsto_pure_pure ..))
  obtain ⟨g', hg'⟩ := P.differentiableAt_Λ (φ ⟨s, hs, hs'⟩)
  have hcomp := hg'.comp ⟨s, hs, hs'⟩ hφ
    continuous_subtype_val.continuousAt Topology.IsEmbedding.subtypeVal
  obtain ⟨l', hl'⟩ := (show DifferentiableAt ℂ (fun w : ℂ ↦ w / 2)
      (P.Λ (φ ⟨s, hs, hs'⟩)) from differentiableAt_id.div_const 2 (hd := two_ne_zero.isUnit))
  exact
    (hl'.comp ⟨s, hs, hs'⟩ hcomp continuous_subtype_val.continuousAt
      Topology.IsEmbedding.id).differentiableAt

lemma differentiable_completedCosZeta₀ (a : UnitAddCircle) :
    Differentiable ℂ (completedCosZeta₀ a) :=
  ((hurwitzEvenFEPair a).symm.differentiable_Λ₀.comp (differentiable_id.div_const _)).div_const _

/-- The residue of completed even Hurwitz zeta at one, evaluated on its actual domain. -/
lemma completedHurwitzZetaEven_residue_one (a : UnitAddCircle) :
    Tendsto (fun s : {s : ℂ // s ≠ 1 ∧ (s ≠ 0 ∨ a ≠ 0)} ↦
      ((s : ℂ) - 1) * completedHurwitzZetaEven a s (hs := s.2))
      (comap Subtype.val (𝓝 1)) (𝓝 1) := by
  let D := {s : ℂ // s ≠ 1 ∧ (s ≠ 0 ∨ a ≠ 0)}
  have hz : Tendsto (Subtype.val : D → ℂ) (comap Subtype.val (𝓝 1)) (𝓝 1) :=
    tendsto_comap
  have hR := ((differentiable_completedHurwitzZetaEven₀ a).continuous.tendsto 1).comp hz
  by_cases ha : a = 0
  · have hu (z : D) : IsUnit (z : ℂ) :=
      (z.2.2.resolve_right (fun h ↦ h ha)).isUnit
    have hrecip := (tendsto_const_nhds (x := (1 : ℂ))).div₀ hz
      (h₀ := hu) (hb := isUnit_one)
    have hlim := ((hz.sub_const 1).mul (hR.sub hrecip)).add_const 1
    simp only [sub_self, zero_mul, zero_add] at hlim
    apply hlim.congr
    intro z
    rw [completedHurwitzZetaEven_eq]
    simp only [dite_eq_left ha]
    simp only [Function.comp_apply]
    field
  · have hlim := ((hz.sub_const 1).mul hR).add_const 1
    simp only [sub_self, zero_mul, zero_add] at hlim
    apply hlim.congr
    intro z
    rw [completedHurwitzZetaEven_eq]
    simp only [dite_eq_right ha, sub_zero]
    simp only [Function.comp_apply]
    field

/-- The residue of completed even Hurwitz zeta at zero is `-1` for `a = 0`, and zero otherwise. -/
lemma completedHurwitzZetaEven_residue_zero (a : UnitAddCircle) :
    Tendsto (fun s : {s : ℂ // s ≠ 1 ∧ (s ≠ 0 ∨ a ≠ 0)} ↦
      (s : ℂ) * completedHurwitzZetaEven a s (hs := s.2))
      (comap Subtype.val (𝓝 0)) (𝓝 (if a = 0 then -1 else 0)) := by
  let D := {s : ℂ // s ≠ 1 ∧ (s ≠ 0 ∨ a ≠ 0)}
  have hz : Tendsto (Subtype.val : D → ℂ) (comap Subtype.val (𝓝 0)) (𝓝 0) :=
    tendsto_comap
  have hR := ((differentiable_completedHurwitzZetaEven₀ a).continuous.tendsto 0).comp hz
  have hu (z : D) : IsUnit (1 - (z : ℂ)) := (sub_ne_zero.mpr z.2.1.symm).isUnit
  have hfrac := hz.div₀ (tendsto_const_nhds.sub hz) (h₀ := hu) (hb := by simp)
  let c : ℂ := if a = 0 then 1 else 0
  have hlim := ((hz.mul hR).sub hfrac).sub_const c
  simp only [zero_mul, zero_div, sub_zero, zero_sub] at hlim
  have hc : -c = if a = 0 then -1 else 0 := by dsimp [c]; split_ifs <;> simp
  rw [hc] at hlim
  apply hlim.congr
  intro z
  rw [completedHurwitzZetaEven_eq]
  dsimp only [c]
  split_ifs with ha
  · have hz0 : (z : ℂ) ≠ 0 := z.2.2.resolve_right (fun h ↦ h ha)
    simp only [Function.comp_apply]
    field
  · simp only [Function.comp_apply]
    field

/-- The residue of completed cosine zeta at zero, on its actual domain. -/
lemma completedCosZeta_residue_zero (a : UnitAddCircle) :
    Tendsto (fun s : {s : ℂ // s ≠ 0 ∧ (s ≠ 1 ∨ a ≠ 0)} ↦
      (s : ℂ) * completedCosZeta a s (hs := s.2))
      (comap Subtype.val (𝓝 0)) (𝓝 (-1)) := by
  let D := {s : ℂ // s ≠ 0 ∧ (s ≠ 1 ∨ a ≠ 0)}
  have hz : Tendsto (Subtype.val : D → ℂ) (comap Subtype.val (𝓝 0)) (𝓝 0) :=
    tendsto_comap
  have hR := ((differentiable_completedCosZeta₀ a).continuous.tendsto 0).comp hz
  by_cases ha : a = 0
  · have hu (z : D) : IsUnit (1 - (z : ℂ)) :=
      (sub_ne_zero.mpr (z.2.2.resolve_right (fun h ↦ h ha)).symm).isUnit
    have hfrac := hz.div₀ (tendsto_const_nhds.sub hz) (h₀ := hu) (hb := by simp)
    have hlim := ((hz.mul hR).sub hfrac).sub_const 1
    simp only [zero_mul, zero_div, sub_zero, zero_sub] at hlim
    apply hlim.congr
    intro z
    rw [completedCosZeta_eq]
    simp only [dite_eq_left ha]
    simp only [Function.comp_apply]
    field
  · have hlim := (hz.mul hR).sub_const 1
    simp only [zero_mul, zero_sub] at hlim
    apply hlim.congr
    intro z
    rw [completedCosZeta_eq]
    simp only [dite_eq_right ha, sub_zero]
    simp only [Function.comp_apply]
    field

end FEPair

/-!
## Relation to the Dirichlet series for `1 < re s`
-/

/-- The completed cosine zeta series, indexed by the nonzero integers. -/
lemma hasSum_int_completedCosZeta (a : ℝ) {s : ℂ} (hs : 1 < re s) :
    HasSum (fun n : {n : ℤ // n ≠ 0} ↦
      Checked.div (Gammaℝ s * cexp (2 * π * I * a * (n : ℤ))) ((↑|(n : ℤ)| : ℂ) ^ s)
        (cpow_ne_zero_iff.mpr (Or.inl (Int.cast_ne_zero.mpr (abs_ne_zero.mpr n.2)))).isUnit / 2)
      (completedCosZeta a s (hs := ⟨ne_zero_of_one_lt_re hs,
        Or.inl (by rintro rfl; simp at hs)⟩)) := by
  let c (n : ℤ) : ℂ := cexp (2 * π * I * a * n) / 2
  have hF t (ht : 0 < t) : HasSum (fun n : ℤ ↦ if n = 0 then 0 else c n * rexp (-π * n ^ 2 * t))
      (((cosKernel a t : ℂ) - 1) / 2) := by
    refine ((hasSum_int_cosKernel₀ a ht).div_const 2).congr_fun fun n ↦ ?_
    split_ifs <;> simp [c, div_mul_eq_mul_div₀]
  simp only [← Int.cast_eq_zero (α := ℝ)] at hF
  let P := (hurwitzEvenFEPair (a : UnitAddCircle)).symm
  have hs0 := ne_zero_of_one_lt_re hs
  have hs1 : s ≠ 1 := by rintro rfl; simp at hs
  let u : {z : ℂ // (z ≠ 0 ∨ P.f₀ = 0) ∧ (z ≠ P.k ∨ P.ε • P.g₀ = 0)} :=
    ⟨s / 2, Or.inl (div_ne_zero hs0), Or.inl (by
      change s / 2 ≠ ↑(1 / 2 : ℝ)
      intro h
      apply hs1
      push_cast at h
      linear_combination 2 * h)⟩
  have hM := (P.hasMellin (s := u) (by
    change (1 / 2 : ℝ) < (s / 2).re
    rwa [div_ofNat_re, div_lt_div_iff_of_pos_right two_pos])).2
  have hEq : completedCosZeta a s (hs := ⟨hs0, Or.inl hs1⟩) =
      mellin (fun t : Ioi (0 : ℝ) ↦ (cosKernel a t - 1 : ℂ) / 2) (s / 2) := by
    rw [mellin_div_const]
    change P.Λ u / 2 = mellin (fun t : Ioi (0 : ℝ) ↦ P.f t - P.f₀) (s / 2) / 2
    exact congrArg (fun z : ℂ ↦ z / 2) hM.symm
  rw [hEq]
  have hseries : Summable (fun n : {n : ℤ // (n : ℝ) ≠ 0} ↦
      Checked.div ‖c n‖ (|(n : ℝ)| ^ s.re)
        (Real.rpow_ne_zero_of_pos (abs_pos.mpr n.2) s.re).isUnit) := by
    have hreal := (summable_one_div_int_add_rpow 0 s.re).mpr hs
    let e := Equiv.subtypeEquivRight (fun n : ℤ ↦
      (show ((n : ℝ) ≠ 0) ↔ (n : ℝ) + 0 ≠ 0 by rw [add_zero]))
    apply (e.summable_iff.mpr (hreal.div_const 2 (hb := two_ne_zero.isUnit))).congr
    intro n
    change 1 / |(n : ℝ) + 0| ^ s.re / 2 = ‖c n‖ / |(n : ℝ)| ^ s.re
    simp only [add_zero, c, norm_div, Complex.norm_two,
      (by push_cast; ring : 2 * π * I * a * (n : ℤ) = ↑(2 * π * a * (n : ℤ)) * I),
      norm_exp_ofReal_mul_I]
    exact div_right_comm₀
  have hbase := hasSum_mellin_pi_mul_sq (zero_lt_one.trans hs)
    (fun t ↦ hF t.val t.property) hseries
  let e : {n : ℤ // n ≠ 0} ≃ {n : ℤ // (n : ℝ) ≠ 0} :=
    Equiv.subtypeEquivRight (fun n ↦ by simp only [Int.cast_ne_zero])
  apply (e.hasSum_iff.mpr hbase).congr_fun
  intro n
  simp only [c, e, Function.comp_def, Equiv.subtypeEquivRight_apply, ← Int.cast_abs, ofReal_intCast]
  field

/-- The completed cosine zeta series, indexed by the positive integers. -/
lemma hasSum_nat_completedCosZeta (a : ℝ) {s : ℂ} (hs : 1 < re s) :
    HasSum (fun n : ℕ+ ↦
      Checked.div (Gammaℝ s * Real.cos (2 * π * a * (n : ℕ))) (((n : ℕ) : ℂ) ^ s)
        (cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr (ne_of_gt n.pos)))).isUnit)
      (completedCosZeta a s (hs := ⟨ne_zero_of_one_lt_re hs,
        Or.inl (by rintro rfl; simp at hs)⟩)) := by
  refine (hasSum_int_completedCosZeta a hs).int_pos_add_neg.congr_fun fun n ↦ ?_
  simp only [ofReal_cos, ofReal_mul, ofReal_ofNat, ofReal_natCast, Complex.cos,
    Int.cast_natCast, Int.cast_neg, abs_neg, Nat.abs_cast, mul_neg]
  rw [show -(2 * π * a * (n : ℕ)) * I = -(2 * π * I * a * (n : ℕ)) by ring,
    show 2 * π * a * (n : ℕ) * I = 2 * π * I * a * (n : ℕ) by ring]
  field

/-- The completed even Hurwitz zeta series, omitting its zero frequencies. -/
lemma hasSum_int_completedHurwitzZetaEven (a : ℝ) {s : ℂ} (hs : 1 < re s) :
    HasSum (fun n : {n : ℤ // (n : ℝ) + a ≠ 0} ↦
      Checked.div (Gammaℝ s) ((↑|(n : ℝ) + a| : ℂ) ^ s)
        (cpow_ne_zero_iff.mpr (Or.inl (ofReal_ne_zero.mpr (abs_ne_zero.mpr n.2)))).isUnit / 2)
      (completedHurwitzZetaEven a s (hs := ⟨by rintro rfl; simp at hs,
        Or.inl (ne_zero_of_one_lt_re hs)⟩)) := by
  have hF (t : ℝ) (ht : 0 < t) : HasSum (fun n : ℤ ↦ if n + a = 0 then 0
      else (1 / 2 : ℂ) * rexp (-π * (n + a) ^ 2 * t))
      (((evenKernel a t : ℂ) - ↑(if (a : UnitAddCircle) = 0 then 1 else 0 : ℝ)) / 2) := by
    refine (ofReal_sub .. ▸ (hasSum_ofReal.mpr (hasSum_int_evenKernel₀ a ht)).div_const
      2).congr_fun fun n ↦ ?_
    split_ifs
    · rw [ofReal_zero, zero_div]
    · rw [mul_comm, mul_one_div₀]
  let P := hurwitzEvenFEPair (a : UnitAddCircle)
  have hs0 := ne_zero_of_one_lt_re hs
  have hs1 : s ≠ 1 := by rintro rfl; simp at hs
  let u : {z : ℂ // (z ≠ 0 ∨ P.f₀ = 0) ∧ (z ≠ P.k ∨ P.ε • P.g₀ = 0)} :=
    ⟨s / 2, Or.inl (div_ne_zero hs0), Or.inl (by
      change s / 2 ≠ ↑(1 / 2 : ℝ)
      intro h
      apply hs1
      push_cast at h
      linear_combination 2 * h)⟩
  have hM := (P.hasMellin (s := u) (by
    change (1 / 2 : ℝ) < (s / 2).re
    rwa [div_ofNat_re, div_lt_div_iff_of_pos_right two_pos])).2
  have hEq : completedHurwitzZetaEven a s (hs := ⟨hs1, Or.inl hs0⟩) =
      mellin (fun t : Ioi (0 : ℝ) ↦
        ((evenKernel (a : UnitAddCircle) t : ℂ) -
          (if (a : UnitAddCircle) = 0 then 1 else 0)) / 2) (s / 2) := by
    rw [mellin_div_const]
    change P.Λ u / 2 = mellin (fun t : Ioi (0 : ℝ) ↦ P.f t - P.f₀) (s / 2) / 2
    exact congrArg (fun z : ℂ ↦ z / 2) hM.symm
  rw [hEq]
  have hseries : Summable (fun n : {n : ℤ // (n : ℝ) + a ≠ 0} ↦
      Checked.div ‖(1 / 2 : ℂ)‖ (|(n : ℝ) + a| ^ s.re)
        (Real.rpow_ne_zero_of_pos (abs_pos.mpr n.2) s.re).isUnit) := by
    apply (((summable_one_div_int_add_rpow a s.re).mpr hs).div_const 2
      (hb := two_ne_zero.isUnit)).congr
    intro n
    simp only [norm_div, norm_one, Complex.norm_two]
    exact div_right_comm₀
  have hbase := hasSum_mellin_pi_mul_sq (r := fun n : ℤ ↦ (n : ℝ) + a) (a := fun _ ↦ (1 / 2 : ℂ))
    (zero_lt_one.trans hs) (fun t ↦ hF t.val t.property) hseries
  simp only [apply_ite ofReal, ofReal_one, ofReal_zero] at hbase
  apply hbase.congr_fun
  intro n
  field
/-!
## The un-completed even Hurwitz zeta
-/

/-- Technical lemma which will give us differentiability of Hurwitz zeta at `s = 0`. -/
lemma differentiableAt_update_of_residue
    {Λ : ℂ → ℂ} (hf : ∀ (s : ℂ) (_ : s ≠ 0) (_ : s ≠ 1), DifferentiableAt ℂ Λ s)
    {L : ℂ} (h_lim : Tendsto (fun s ↦ s * Λ s) (𝓝[≠] 0) (𝓝 L)) (s : ℂ) (hs' : s ≠ 1) :
    DifferentiableAt ℂ (Function.update (fun s ↦ Λ s * reciprocalGammaℝ s) 0 (L / 2)) s := by
  have claim (t) (ht : t ≠ 0) (ht' : t ≠ 1) :
      DifferentiableAt ℂ (fun u : ℂ ↦ Λ u * reciprocalGammaℝ u) t :=
    (hf t ht ht').mul differentiable_reciprocalGammaℝ.differentiableAt
  have claim2 : Tendsto (fun s : ℂ ↦ Λ s * reciprocalGammaℝ s) (𝓝[≠] 0) (𝓝 <| L / 2) := by
    have hp : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    have hcontinuous : Continuous (fun s : ℂ ↦ reciprocalGammaℝ (s + 2) / 2 / (π : ℂ)) :=
      ((differentiable_reciprocalGammaℝ.continuous.comp
        (continuous_add_const 2)).div_const₀ 2).div_const₀ π
    have h := h_lim.mul ((hcontinuous.tendsto 0).mono_left nhdsWithin_le_nhds)
    convert h using 1
    · ext z
      rw [reciprocalGammaℝ_eq_self_mul_reciprocalGammaℝ_add_two]
      ring
    · simp only [zero_add, reciprocalGammaℝ_two]
      congr 1
      field
  rcases ne_or_eq s 0 with hs | rfl
  · -- Easy case : `s ≠ 0`
    refine (claim s hs hs').congr_of_eventuallyEq ?_
    filter_upwards [isOpen_compl_singleton.mem_nhds hs] with x hx
    simp [Function.update_of_ne hx]
  · -- Hard case : `s = 0`
    have S_nhds : {(1 : ℂ)}ᶜ ∈ 𝓝 (0 : ℂ) := isOpen_compl_singleton.mem_nhds hs'
    apply ((Complex.differentiableOn_compl_singleton_and_continuousAt_iff S_nhds).mp
      ⟨?_, continuousAt_update_same.mpr claim2⟩).differentiableAt S_nhds
    intro t ht
    apply DifferentiableAt.differentiableWithinAt
    apply (claim t ht.2 ht.1).congr_of_eventuallyEq
    filter_upwards [isOpen_compl_singleton.mem_nhds ht.2] with z hz
    exact Function.update_of_ne hz ..

/-- The entire regular part of even Hurwitz zeta after removing
`reciprocalGammaℝ s / (s - 1)`. The reciprocal Gamma recurrence also removes the apparent
singularity at zero, so this formula never evaluates a quotient at either pole. -/
def hurwitzZetaEvenRegularPart (a : UnitAddCircle) (s : ℂ) : ℂ :=
  completedHurwitzZetaEven₀ a s * reciprocalGammaℝ s -
    (if a = 0 then 1 else 0) * reciprocalGammaℝ (s + 2) / 2 / (π : ℂ)

lemma differentiable_hurwitzZetaEvenRegularPart (a : UnitAddCircle) :
    Differentiable ℂ (hurwitzZetaEvenRegularPart a) := by
  unfold hurwitzZetaEvenRegularPart
  have hp : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have h := (differentiable_reciprocalGammaℝ.comp (differentiable_id.add_const 2)).const_mul
    (if a = 0 then 1 else 0)
  exact ((differentiable_completedHurwitzZetaEven₀ a).mul
    differentiable_reciprocalGammaℝ).sub ((h.div_const 2).div_const π)

/-- The even Hurwitz zeta function, evaluated away from its pole at one. -/
noncomputable def hurwitzZetaEven (a : UnitAddCircle) (s : ℂ)
    (hs : s ≠ 1 := by checked_nonzero) : ℂ :=
  hurwitzZetaEvenRegularPart a s +
    Checked.div (reciprocalGammaℝ s) (s - 1) (sub_ne_zero.mpr hs).isUnit

/-- The principal-part decomposition of even Hurwitz zeta, on its regular domain. -/
lemma hurwitzZetaEven_eq_regularPart_add {a : UnitAddCircle} {s : ℂ} (hs : s ≠ 1) :
    hurwitzZetaEven a s = hurwitzZetaEvenRegularPart a s + reciprocalGammaℝ s / (s - 1) := rfl

lemma hurwitzZetaEven_apply_zero (a : UnitAddCircle) :
    hurwitzZetaEven a 0 = if a = 0 then -1 / 2 else 0 := by
  have hp : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  simp only [hurwitzZetaEven, hurwitzZetaEvenRegularPart,
    (reciprocalGammaℝ_eq_zero_iff (s := 0)).mpr ⟨0, by simp⟩, mul_zero, zero_add,
    reciprocalGammaℝ_two, zero_sub, zero_div, add_zero]
  split_ifs <;> field

lemma hurwitzZetaEven_def_of_ne_or_ne {a : UnitAddCircle} {s : ℂ}
    {hs : s ≠ 1} (h : a ≠ 0 ∨ s ≠ 0) :
    hurwitzZetaEven a s = completedHurwitzZetaEven a s
      (hs := ⟨hs, h.elim Or.inr Or.inl⟩) * reciprocalGammaℝ s := by
  have hp : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  by_cases hs0 : s = 0
  · subst s
    have ha : a ≠ 0 := h.resolve_right (by simp)
    simp [hurwitzZetaEven_apply_zero, ha, reciprocalGammaℝ]
  · have hsub : 1 - s ≠ 0 := sub_ne_zero.mpr hs.symm
    have hsub' : s - 1 ≠ 0 := sub_ne_zero.mpr hs
    rw [hurwitzZetaEven, completedHurwitzZetaEven_eq, hurwitzZetaEvenRegularPart,
      reciprocalGammaℝ_eq_self_mul_reciprocalGammaℝ_add_two s]
    split_ifs <;> field

lemma hurwitzZetaEven_neg (a : UnitAddCircle) (s : ℂ) {hs : s ≠ 1} :
    hurwitzZetaEven (-a) s = hurwitzZetaEven a s := by
  simp [hurwitzZetaEven, hurwitzZetaEvenRegularPart]

/-- The trivial zeroes of the even Hurwitz zeta function. -/
theorem hurwitzZetaEven_neg_two_mul_nat_add_one (a : UnitAddCircle) (n : ℕ) :
    hurwitzZetaEven a (-2 * (n + 1))
      (hs := by
        intro h
        have hre := congrArg re h
        norm_num at hre
        nlinarith [Nat.cast_nonneg (α := ℝ) n]) = 0 := by
  have hzero : (-2 : ℂ) * (n + 1) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr two_ne_zero) (Nat.cast_add_one_ne_zero n)
  rw [hurwitzZetaEven_def_of_ne_or_ne (Or.inr hzero),
    reciprocalGammaℝ_eq_zero_iff.mpr ⟨n + 1, by simp⟩, mul_zero]

/-- Even Hurwitz zeta is differentiable on its actual domain, including zero. -/
lemma differentiableAt_hurwitzZetaEven (a : UnitAddCircle) {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ
      (fun z : {z : ℂ // z ≠ 1} ↦ hurwitzZetaEven a z (hs := z.2))
      ⟨s, hs⟩ (fun z ↦ (z : ℂ)) := by
  have hR : DifferentiableAt ℂ
      (fun z : {z : ℂ // z ≠ 1} ↦ hurwitzZetaEvenRegularPart a z)
      ⟨s, hs⟩ (fun z ↦ (z : ℂ)) := by
    obtain ⟨d, hd⟩ := differentiable_hurwitzZetaEvenRegularPart a s
    exact ⟨d, HasFDerivAtFilter.comp_tendsto hd Subtype.val
      ((continuous_subtype_val.tendsto ⟨s, hs⟩).prodMap (tendsto_pure_pure ..))⟩
  have hu : IsUnit (s - 1) := (sub_ne_zero.mpr hs).isUnit
  have hq := (differentiable_reciprocalGammaℝ s).div
    (differentiableAt_id.sub_const 1) hu
  let φ : {z : ℂ // z ≠ 1} → {z : ℂ // IsUnit (z - 1)} :=
    fun z ↦ ⟨z, (sub_ne_zero.mpr z.2).isUnit⟩
  have hφ : Continuous φ := continuous_subtype_val.subtype_mk _
  have hq' : DifferentiableAt ℂ
      (fun z : {z : ℂ // z ≠ 1} ↦ reciprocalGammaℝ z / ((z : ℂ) - 1))
      ⟨s, hs⟩ (fun z ↦ (z : ℂ)) := by
    obtain ⟨d, hd⟩ := hq
    exact ⟨d, HasFDerivAtFilter.comp_tendsto hd φ
      ((hφ.tendsto ⟨s, hs⟩).prodMap (tendsto_pure_pure ..))⟩
  exact hR.add hq'

lemma hurwitzZetaEven_residue_one (a : UnitAddCircle) :
    Tendsto (fun s : {s : ℂ // s ≠ 1} ↦
      ((s : ℂ) - 1) * hurwitzZetaEven a s (hs := s.2))
      (comap Subtype.val (𝓝 1)) (𝓝 1) := by
  have hz : Tendsto (Subtype.val : {s : ℂ // s ≠ 1} → ℂ) (comap Subtype.val (𝓝 1)) (𝓝 1) :=
    tendsto_comap
  have hR := ((continuous_id.sub (continuous_const (y := (1 : ℂ)))).mul
    (differentiable_hurwitzZetaEvenRegularPart a).continuous).continuousAt.tendsto.comp hz
  have hG := (differentiable_reciprocalGammaℝ.continuous.tendsto 1).comp hz
  have hlim := hR.add hG
  simp only [Pi.mul_apply, Pi.sub_apply, id_eq, sub_self, zero_mul, reciprocalGammaℝ_one,
    zero_add] at hlim
  apply hlim.congr
  intro s
  simp only [Function.comp_apply, Pi.mul_apply, Pi.sub_apply, id_eq, hurwitzZetaEven]
  field

/-- Removing the principal part has a finite limit at one. The quotient is evaluated only
on its actual domain; the limit is the value of the entire regular part. -/
lemma tendsto_hurwitzZetaEven_sub_principalPart_nhds_one (a : UnitAddCircle) :
    Tendsto (fun s : {s : ℂ // s ≠ 1} ↦
      hurwitzZetaEven a s (hs := s.2) - reciprocalGammaℝ s / ((s : ℂ) - 1))
      (comap Subtype.val (𝓝 1)) (𝓝 (hurwitzZetaEvenRegularPart a 1)) := by
  apply (((differentiable_hurwitzZetaEvenRegularPart a).continuous.tendsto 1).comp
    tendsto_comap).congr
  intro s
  simp only [Function.comp_def, hurwitzZetaEven_eq_regularPart_add s.2, add_sub_cancel_right]

/-- The entire continuation of a difference of two even Hurwitz zeta functions is the
difference of their regular parts, since their principal parts agree. -/
lemma hurwitzZetaEven_sub_eq_regularPart_sub {a b : UnitAddCircle} {s : ℂ} (hs : s ≠ 1) :
    hurwitzZetaEven a s - hurwitzZetaEven b s =
      hurwitzZetaEvenRegularPart a s - hurwitzZetaEvenRegularPart b s := by
  rw [hurwitzZetaEven_eq_regularPart_add hs, hurwitzZetaEven_eq_regularPart_add hs]
  abel

lemma differentiable_hurwitzZetaEvenRegularPart_sub (a b : UnitAddCircle) :
    Differentiable ℂ (fun s ↦ hurwitzZetaEvenRegularPart a s - hurwitzZetaEvenRegularPart b s) :=
  (differentiable_hurwitzZetaEvenRegularPart a).sub (differentiable_hurwitzZetaEvenRegularPart b)

/-- The even Hurwitz zeta series, omitting zero frequencies before taking reciprocals. -/
lemma hasSum_int_hurwitzZetaEven (a : ℝ) {s : ℂ} (hs : 1 < re s) :
    HasSum (fun n : {n : ℤ // (n : ℝ) + a ≠ 0} ↦
      Checked.div 1 ((↑|(n : ℝ) + a| : ℂ) ^ s)
        (cpow_ne_zero_iff.mpr (Or.inl (ofReal_ne_zero.mpr (abs_ne_zero.mpr n.2)))).isUnit / 2)
      (hurwitzZetaEven a s (hs := by rintro rfl; simp at hs)) := by
  rw [hurwitzZetaEven_def_of_ne_or_ne (Or.inr (ne_zero_of_one_lt_re hs))]
  have hreg : ∀ n : ℕ, s ≠ -(2 * n) := by
    intro n hn
    have hr := congrArg re hn
    norm_num at hr
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hG : IsUnit (Gammaℝ s) := (Gammaℝ_ne_zero_of_re_pos (zero_lt_one.trans hs)).isUnit
  apply ((hasSum_int_completedHurwitzZetaEven a hs).mul_right (reciprocalGammaℝ s)).congr_fun
  intro n
  rw [reciprocalGammaℝ_eq_inv hreg]
  field

/-- Splitting the integer Hurwitz series at zero gives two independent denominator domains.
In particular, when an endpoint term is omitted from one branch, the other branch survives. -/
lemma hasSum_nat_hurwitzZetaEven (a : ℝ) {s : ℂ} (hs : 1 < re s) :
    HasSum (Sum.elim
      (fun n : {n : ℕ // (n : ℝ) + a ≠ 0} ↦
        Checked.div 1 ((↑|(n : ℝ) + a| : ℂ) ^ s)
          (cpow_ne_zero_iff.mpr (Or.inl (ofReal_ne_zero.mpr (abs_ne_zero.mpr n.2)))).isUnit / 2)
      (fun n : {n : ℕ // (n : ℝ) + 1 - a ≠ 0} ↦
        Checked.div 1 ((↑|(n : ℝ) + 1 - a| : ℂ) ^ s)
          (cpow_ne_zero_iff.mpr (Or.inl (ofReal_ne_zero.mpr (abs_ne_zero.mpr n.2)))).isUnit / 2))
      (hurwitzZetaEven a s (hs := by rintro rfl; simp at hs)) := by
  let e : {n : ℤ // (n : ℝ) + a ≠ 0} ≃
      {n : ℕ // (n : ℝ) + a ≠ 0} ⊕ {n : ℕ // (n : ℝ) + 1 - a ≠ 0} :=
    { toFun := fun n ↦ match n with
        | ⟨Int.ofNat m, hm⟩ => Sum.inl ⟨m, by
            simpa only [Int.ofNat_eq_natCast, Int.cast_natCast] using hm⟩
        | ⟨Int.negSucc m, hm⟩ => Sum.inr ⟨m, by
            intro h
            apply hm
            push_cast
            linear_combination -h⟩
      invFun := fun n ↦ match n with
        | Sum.inl m => ⟨Int.ofNat m, by
            simpa only [Int.ofNat_eq_natCast, Int.cast_natCast] using m.2⟩
        | Sum.inr m => ⟨Int.negSucc m, by
            intro h
            apply m.2
            push_cast at h
            linear_combination -h⟩
      left_inv := by rintro ⟨n, hn⟩; cases n <;> rfl
      right_inv := by rintro (⟨n, hn⟩ | ⟨n, hn⟩) <;> rfl }
  have hneg (n : ℕ) : |(Int.negSucc n : ℝ) + a| = |(n : ℝ) + 1 - a| := by
    rw [Int.cast_negSucc, Nat.cast_add, Nat.cast_one,
      show -((n : ℝ) + 1) + a = -((n : ℝ) + 1 - a) by ring, abs_neg]
  apply (e.symm.hasSum_iff.mpr (hasSum_int_hurwitzZetaEven a hs)).congr_fun
  rintro (n | n)
  · simp [e, Int.ofNat_eq_natCast]
  · dsimp only [Function.comp_apply, e, Equiv.coe_fn_symm_mk, Sum.elim_inr]
    simp only [hneg]

/-- The natural Hurwitz series without absolute values, on the exact two component domains. -/
lemma hasSum_nat_hurwitzZetaEven_of_mem_Icc {a : ℝ} (ha : a ∈ Icc 0 1) {s : ℂ} (hs : 1 < re s) :
    HasSum (Sum.elim
      (fun n : {n : ℕ // (n : ℝ) + a ≠ 0} ↦
        Checked.div 1 ((((n : ℕ) : ℂ) + a) ^ s)
          (cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast n.2))).isUnit / 2)
      (fun n : {n : ℕ // (n : ℝ) + 1 - a ≠ 0} ↦
        Checked.div 1 ((((n : ℕ) : ℂ) + 1 - a) ^ s)
          (cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast n.2))).isUnit / 2))
      (hurwitzZetaEven a s (hs := by rintro rfl; simp at hs)) := by
  apply (hasSum_nat_hurwitzZetaEven a hs).congr_fun
  rintro (n | n)
  · have hnonneg : (0 : ℝ) ≤ (n : ℕ) + a := add_nonneg (Nat.cast_nonneg _) ha.1
    simp only [Sum.elim_inl, abs_of_nonneg hnonneg, ofReal_add, ofReal_natCast]
  · have hnonneg : (0 : ℝ) ≤ (n : ℕ) + 1 - a := by linarith [Nat.cast_nonneg (α := ℝ) (n : ℕ), ha.2]
    simp only [Sum.elim_inr, abs_of_nonneg hnonneg, ofReal_sub, ofReal_add, ofReal_natCast,
      ofReal_one]
/-!
## The un-completed cosine zeta
-/

/-- The entire regular part of cosine zeta after removing the possible principal part
at one. The reciprocal Gamma recurrence removes the apparent pole at zero. -/
def cosZetaRegularPart (a : UnitAddCircle) (s : ℂ) : ℂ :=
  completedCosZeta₀ a s * reciprocalGammaℝ s - reciprocalGammaℝ (s + 2) / 2 / (π : ℂ)

lemma differentiable_cosZetaRegularPart (a : UnitAddCircle) :
    Differentiable ℂ (cosZetaRegularPart a) := by
  have hp : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  exact ((differentiable_completedCosZeta₀ a).mul differentiable_reciprocalGammaℝ).sub
    (((differentiable_reciprocalGammaℝ.comp
      (differentiable_id.add_const 2)).div_const 2).div_const π)

/-- Cosine zeta on its exact domain. It has a pole at one precisely when `a = 0`. -/
noncomputable def cosZeta (a : UnitAddCircle) (s : ℂ)
    (hs : s ≠ 1 ∨ a ≠ 0 := by assumption) : ℂ :=
  cosZetaRegularPart a s + if ha : a = 0 then
    Checked.div (reciprocalGammaℝ s) (s - 1)
      (sub_ne_zero.mpr (hs.resolve_right (fun h ↦ h ha))).isUnit else 0

lemma cosZeta_apply_zero (a : UnitAddCircle) :
    cosZeta a 0 (hs := Or.inl zero_ne_one) = -1 / 2 := by
  have hp : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  simp only [cosZeta, cosZetaRegularPart,
    (reciprocalGammaℝ_eq_zero_iff (s := 0)).mpr ⟨0, by simp⟩, mul_zero, zero_add,
    reciprocalGammaℝ_two, zero_sub]
  split_ifs <;> field

lemma cosZeta_def {a : UnitAddCircle} {s : ℂ}
    {hs : s ≠ 1 ∨ a ≠ 0} (hs0 : s ≠ 0) :
    cosZeta a s = completedCosZeta a s (hs := ⟨hs0, hs⟩) * reciprocalGammaℝ s := by
  have hp : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [cosZeta, completedCosZeta_eq, cosZetaRegularPart,
    reciprocalGammaℝ_eq_self_mul_reciprocalGammaℝ_add_two s]
  split_ifs with ha
  · have hs1 : s ≠ 1 := hs.resolve_right (fun h ↦ h ha)
    field
  · field

lemma cosZeta_neg (a : UnitAddCircle) (s : ℂ)
    {hs : s ≠ 1 ∨ a ≠ 0} :
    cosZeta (-a) s (hs := hs.imp_right (fun h ↦ neg_ne_zero.mpr h)) = cosZeta a s := by
  simp [cosZeta, cosZetaRegularPart]

/-- The trivial zeroes of the cosine zeta function. -/
theorem cosZeta_neg_two_mul_nat_add_one (a : UnitAddCircle) (n : ℕ) :
    cosZeta a (-2 * (n + 1))
      (hs := Or.inl (by
        intro h
        have hre := congrArg re h
        norm_num at hre
        nlinarith [Nat.cast_nonneg (α := ℝ) n])) = 0 := by
  have hzero : (-2 : ℂ) * (n + 1) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr two_ne_zero) (Nat.cast_add_one_ne_zero n)
  rw [cosZeta_def hzero,
    reciprocalGammaℝ_eq_zero_iff.mpr ⟨n + 1, by rw [neg_mul, Nat.cast_add_one]⟩, mul_zero]

/-- Cosine zeta is differentiable on its actual domain, including one when `a ≠ 0`. -/
lemma differentiableAt_cosZeta (a : UnitAddCircle) {s : ℂ} (hs : s ≠ 1 ∨ a ≠ 0) :
    DifferentiableAt ℂ
      (fun z : {z : ℂ // z ≠ 1 ∨ a ≠ 0} ↦ cosZeta a z (hs := z.2))
      ⟨s, hs⟩ (fun z ↦ (z : ℂ)) := by
  let D := {z : ℂ // z ≠ 1 ∨ a ≠ 0}
  have hR : DifferentiableAt ℂ (fun z : D ↦ cosZetaRegularPart a z)
      ⟨s, hs⟩ (fun z ↦ (z : ℂ)) := by
    obtain ⟨d, hd⟩ := differentiable_cosZetaRegularPart a s
    exact ⟨d, HasFDerivAtFilter.comp_tendsto hd Subtype.val
      ((continuous_subtype_val.tendsto ⟨s, hs⟩).prodMap (tendsto_pure_pure ..))⟩
  by_cases ha : a = 0
  · have hs1 : s ≠ 1 := hs.resolve_right (fun h ↦ h ha)
    have hq := (differentiable_reciprocalGammaℝ s).div
      (differentiableAt_id.sub_const 1) (sub_ne_zero.mpr hs1).isUnit
    let φ : D → {z : ℂ // IsUnit (z - 1)} :=
      fun z ↦ ⟨z, (sub_ne_zero.mpr (z.2.resolve_right (fun h ↦ h ha))).isUnit⟩
    have hφ : Continuous φ := continuous_subtype_val.subtype_mk _
    have hq' : DifferentiableAt ℂ
        (fun z : D ↦ Checked.div (reciprocalGammaℝ z) ((z : ℂ) - 1) (φ z).2)
        ⟨s, hs⟩ (fun z ↦ (z : ℂ)) := by
      obtain ⟨d, hd⟩ := hq
      exact ⟨d, HasFDerivAtFilter.comp_tendsto hd φ
        ((hφ.tendsto ⟨s, hs⟩).prodMap (tendsto_pure_pure ..))⟩
    simpa only [cosZeta, dite_eq_left ha, Pi.add_def] using! hR.add hq'
  · simpa only [cosZeta, dite_eq_right ha, add_zero] using hR

/-- If `a ≠ 0`, cosine zeta is entire. -/
lemma differentiable_cosZeta_of_ne_zero {a : UnitAddCircle} (ha : a ≠ 0) :
    Differentiable ℂ (fun s ↦ cosZeta a s (hs := Or.inr ha)) := by
  simpa only [cosZeta, dite_eq_right ha, add_zero] using differentiable_cosZetaRegularPart a

/-- The cosine zeta series on the nonzero integers. -/
lemma hasSum_int_cosZeta (a : ℝ) {s : ℂ} (hs : 1 < re s) :
    HasSum (fun n : {n : ℤ // n ≠ 0} ↦
      Checked.div (cexp (2 * π * I * a * (n : ℤ))) ((↑|(n : ℤ)| : ℂ) ^ s)
        (cpow_ne_zero_iff.mpr (Or.inl (Int.cast_ne_zero.mpr (abs_ne_zero.mpr n.2)))).isUnit / 2)
      (cosZeta a s (hs := Or.inl (by rintro rfl; simp at hs))) := by
  rw [cosZeta_def (ne_zero_of_one_lt_re hs)]
  have hreg : ∀ n : ℕ, s ≠ -(2 * n) := by
    intro n hn
    have hr := congrArg re hn
    norm_num at hr
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hG : IsUnit (Gammaℝ s) := (Gammaℝ_ne_zero_of_re_pos (zero_lt_one.trans hs)).isUnit
  apply ((hasSum_int_completedCosZeta a hs).mul_right (reciprocalGammaℝ s)).congr_fun
  intro n
  rw [reciprocalGammaℝ_eq_inv hreg]
  field

/-- The cosine zeta series on the positive integers. -/
lemma hasSum_nat_cosZeta (a : ℝ) {s : ℂ} (hs : 1 < re s) :
    HasSum (fun n : ℕ+ ↦
      Checked.div (Real.cos (2 * π * a * (n : ℕ)) : ℂ) (((n : ℕ) : ℂ) ^ s)
        (cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr (ne_of_gt n.pos)))).isUnit)
      (cosZeta a s (hs := Or.inl (by rintro rfl; simp at hs))) := by
  refine (hasSum_int_cosZeta a hs).int_pos_add_neg.congr_fun fun n ↦ ?_
  simp only [ofReal_cos, ofReal_mul, ofReal_ofNat, ofReal_natCast, Complex.cos,
    Int.cast_natCast, Int.cast_neg, abs_neg, Nat.abs_cast, mul_neg]
  rw [show -(2 * π * a * (n : ℕ)) * I = -(2 * π * I * a * (n : ℕ)) by ring,
    show 2 * π * a * (n : ℕ) * I = 2 * π * I * a * (n : ℕ) by ring]
  field

/-- The cosine zeta Dirichlet series. -/
lemma LSeriesHasSum_cos (a : ℝ) {s : ℂ} (hs : 1 < re s) :
    LSeriesHasSum (Real.cos <| 2 * π * a * ·) s
      (cosZeta a s (hs := Or.inl (by rintro rfl; simp at hs))) :=
  LSeriesHasSum_iff_hasSum_pnat.mpr (hasSum_nat_cosZeta a hs)
/-!
## Functional equations for the un-completed zetas
-/

/-- The even Hurwitz functional equation on the domains of both scalar evaluations. -/
lemma hurwitzZetaEven_one_sub (a : UnitAddCircle) {s : ℂ}
    (hs : ∀ n : ℕ, s ≠ -n) (hs' : a ≠ 0 ∨ s ≠ 1) :
    hurwitzZetaEven a (1 - s) (hs := by
      intro h
      apply hs 0
      linear_combination -h) =
      2 * (2 * π) ^ (-s) * Gamma s * cos (π * s / 2) *
        cosZeta a s (hs := hs'.symm) := by
  have hs0 : s ≠ 0 := by simpa using hs 0
  have hsL : 1 - s ≠ 1 := by intro h; apply hs0; linear_combination -h
  rw [hurwitzZetaEven_def_of_ne_or_ne (hs := hsL)
      (hs'.imp_right (fun h ↦ sub_ne_zero.mpr h.symm)),
    completedHurwitzZetaEven_one_sub (hs := ⟨hs0, hs'.symm⟩),
    reciprocalGammaℝ_one_sub hs, cosZeta_def hs0, ← Gammaℂ]
  ring

/-- The cosine functional equation, excluding the nonpositive integers of the Gamma factor
and the scalar poles appearing in its two zeta evaluations. -/
lemma cosZeta_one_sub (a : UnitAddCircle) {s : ℂ} (hs : ∀ n : ℕ, s ≠ 1 - n) :
    cosZeta a (1 - s) (hs := Or.inl (by
      intro h
      apply hs 1
      linear_combination -h)) =
      2 * (2 * π) ^ (-s) * Gamma s * cos (π * s / 2) *
        hurwitzZetaEven a s (hs := by simpa using hs 0) := by
  have hs1 : s ≠ 1 := by simpa using hs 0
  have hs0 : s ≠ 0 := by simpa using hs 1
  have hreg : ∀ n : ℕ, s ≠ -n := fun n ↦ by simpa using hs (n + 1)
  rw [cosZeta_def (sub_ne_zero.mpr hs1.symm),
    completedCosZeta_one_sub (hs := ⟨hs1, Or.inl hs0⟩), reciprocalGammaℝ_one_sub hreg,
    hurwitzZetaEven_def_of_ne_or_ne (Or.inr hs0), ← Gammaℂ]
  ring

end HurwitzZeta
