/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.NumberTheory.LSeries.AbstractFuncEq
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.Bounds
public import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
public import Mathlib.NumberTheory.LSeries.Basic

/-!
# Odd Hurwitz zeta functions

In this file we study the functions on `ℂ` which are the analytic continuation of the following
series (convergent for `1 < re s`), where `a ∈ ℝ` is a parameter:

`hurwitzZetaOdd a s = 1 / 2 * ∑' n : ℤ, sgn (n + a) / |n + a| ^ s`

and

`sinZeta a s = ∑' n : ℕ, sin (2 * π * a * n) / n ^ s`.

The zero frequency `n = -a` is omitted from the first sum if `a` is an integer. The second
sum is indexed by the positive integers. Note that these functions are differentiable everywhere,
unlike their even counterparts which have poles.

Of course, we cannot *define* these functions by the above formulae (since existence of the
analytic continuation is not at all obvious); we in fact construct them as Mellin transforms of
various versions of the Jacobi theta function.

## Main definitions and theorems

* `completedHurwitzZetaOdd`: the completed Hurwitz zeta function
* `completedSinZeta`: the completed sine zeta function
* `differentiable_completedHurwitzZetaOdd` and `differentiable_completedSinZeta`:
  differentiability on `ℂ`
* `completedHurwitzZetaOdd_one_sub`: the functional equation
  `completedHurwitzZetaOdd a (1 - s) = completedSinZeta a s`
* `hasSum_int_hurwitzZetaOdd` and `hasSum_nat_sinZeta`: relation between
  the zeta functions and corresponding Dirichlet series for `1 < re s`
-/

@[expose] public section

noncomputable section

open Complex
open CharZero Filter Topology Asymptotics Real Set MeasureTheory
open scoped ComplexConjugate

namespace HurwitzZeta

section kernel_defs
/-!
## Definitions and elementary properties of kernels
-/

/-- Variant of `jacobiTheta₂'` which we introduce to simplify some formulae. -/
def jacobiTheta₂'' (z τ : ℂ) : ℂ :=
  cexp (π * I * z ^ 2 * τ) * (jacobiTheta₂' (z * τ) τ / (2 * π * I) + z * jacobiTheta₂ (z * τ) τ)

lemma jacobiTheta₂''_conj (z τ : ℂ) :
    conj (jacobiTheta₂'' z τ) = jacobiTheta₂'' (conj z) (-conj τ) := by
  simp [jacobiTheta₂'', jacobiTheta₂'_conj, jacobiTheta₂_conj, ← exp_conj, map_ofNat, div_neg₀,
    neg_div₀, jacobiTheta₂'_neg_left]

/-- Restatement of `jacobiTheta₂'_add_left'`: the function `jacobiTheta₂''` is 1-periodic in `z`. -/
lemma jacobiTheta₂''_add_left (z τ : ℂ) : jacobiTheta₂'' (z + 1) τ = jacobiTheta₂'' z τ := by
  simp only [jacobiTheta₂'', add_mul z 1, one_mul, jacobiTheta₂'_add_left', jacobiTheta₂_add_left']
  generalize jacobiTheta₂ (z * τ) τ = J
  generalize jacobiTheta₂' (z * τ) τ = J'
  -- clear denominator
  simp_rw [div_add' _ _ _ (hc := two_pi_I_ne_zero.isUnit), ← mul_div_assoc₀]
  refine congr_arg (· / (2 * π * I)) ?_
  -- get all exponential terms to left
  rw [mul_left_comm _ (cexp _), ← mul_add, mul_assoc (cexp _), ← mul_add, ← mul_assoc (cexp _),
    ← Complex.exp_add]
  congrm (cexp ?_ * ?_) <;> ring

lemma jacobiTheta₂''_neg_left (z τ : ℂ) : jacobiTheta₂'' (-z) τ = -jacobiTheta₂'' z τ := by
  simp [jacobiTheta₂'', jacobiTheta₂'_neg_left, neg_div₀, -neg_add_rev, ← neg_add]

lemma jacobiTheta₂'_functional_equation' (z τ : ℂ) (hτ : 0 < τ.im) :
    jacobiTheta₂' z τ =
      Checked.div (-2 * π : ℂ) ((-I * τ) ^ (3 / 2 : ℂ))
        (cpow_ne_zero_iff.mpr (Or.inl (mul_ne_zero (neg_ne_zero.mpr I_ne_zero)
          (ne_of_apply_ne im (zero_im.symm ▸ ne_of_gt hτ))))).isUnit *
      jacobiTheta₂'' z (Checked.div (-1) τ
        (ne_of_apply_ne im (zero_im.symm ▸ ne_of_gt hτ)).isUnit) := by
  have hτ0 : τ ≠ 0 := ne_of_apply_ne im (zero_im.symm ▸ ne_of_gt hτ)
  have hpow : IsUnit ((-I * τ) ^ (3 / 2 : ℂ)) :=
    (cpow_ne_zero_iff.mpr (Or.inl (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hτ0))).isUnit
  have hz : z * (-1 / τ) = -(z / τ) := by
    simp only [div_eq_mul_inv₀, neg_one_mul, mul_neg]
  have he : π * I * z ^ 2 * (-1 / τ) = -π * I * z ^ 2 / τ := by
    simp only [div_eq_mul_inv₀]; ring
  have hp : (-I * τ) ^ (3 / 2 : ℂ) = (-I * τ) ^ (1 / 2 : ℂ) * (-I * τ) := by
    rw [show (3 / 2 : ℂ) = 1 / 2 + 1 by norm_num,
      cpow_add _ _ (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hτ0), cpow_one]
  rw [jacobiTheta₂'_functional_equation z τ hτ, jacobiTheta₂'', he, hz,
    jacobiTheta₂_neg_left, jacobiTheta₂'_neg_left]
  field_simp
  rw [mul_comm τ (-I), hp]
  ring_nf
  simp [I_sq]
  ac_rfl

/-- Odd Hurwitz zeta kernel (function whose Mellin transform will be the odd part of the completed
Hurwitz zeta function). See `oddKernel_def` for the defining formula, and `hasSum_int_oddKernel`
for an expression as a sum over `ℤ`.
-/
@[irreducible] def oddKernel (a : UnitAddCircle) (x : ℝ) : ℝ :=
  (show Function.Periodic (fun a : ℝ ↦ re (jacobiTheta₂'' a (I * x))) 1 by
    simp [jacobiTheta₂''_add_left]).lift a

lemma oddKernel_def (a x : ℝ) : ↑(oddKernel a x) = jacobiTheta₂'' a (I * x) := by
  simp [oddKernel, ← conj_eq_iff_re, jacobiTheta₂''_conj]

lemma oddKernel_def' (a x : ℝ) : ↑(oddKernel ↑a x) = cexp (-π * a ^ 2 * x) *
    (jacobiTheta₂' (a * I * x) (I * x) / (2 * π * I) + a * jacobiTheta₂ (a * I * x) (I * x)) := by
  rw [oddKernel_def, jacobiTheta₂'', ← mul_assoc ↑a I x,
    (by ring : ↑π * I * ↑a ^ 2 * (I * ↑x) = I ^ 2 * ↑π * ↑a ^ 2 * x), I_sq, neg_one_mul]

lemma oddKernel_undef (a : UnitAddCircle) {x : ℝ} (hx : x ≤ 0) : oddKernel a x = 0 := by
  induction a using QuotientAddGroup.induction_on with | H a' =>
  rw [← ofReal_eq_zero, oddKernel_def', jacobiTheta₂_undef, jacobiTheta₂'_undef, zero_div, zero_add,
    mul_zero, mul_zero] <;>
  simpa

/-- Auxiliary function appearing in the functional equation for the odd Hurwitz zeta kernel, equal
to `∑ (n : ℕ), 2 * n * sin (2 * π * n * a) * exp (-π * n ^ 2 * x)`. See `hasSum_nat_sinKernel`
for the defining sum. -/
@[irreducible] def sinKernel (a : UnitAddCircle) (x : ℝ) : ℝ :=
  (show Function.Periodic (fun ξ : ℝ ↦ re (jacobiTheta₂' ξ (I * x) / (-2 * π))) 1 by
    simp [jacobiTheta₂'_add_left]).lift a

lemma sinKernel_def (a x : ℝ) : ↑(sinKernel ↑a x) = jacobiTheta₂' a (I * x) / (-2 * π) := by
  simp [sinKernel, re_eq_add_conj, jacobiTheta₂'_conj, map_ofNat]

lemma sinKernel_undef (a : UnitAddCircle) {x : ℝ} (hx : x ≤ 0) : sinKernel a x = 0 := by
  induction a using QuotientAddGroup.induction_on with
  | H a => rw [← ofReal_eq_zero, sinKernel_def, jacobiTheta₂'_undef _ (by simpa), zero_div]

lemma oddKernel_neg (a : UnitAddCircle) (x : ℝ) : oddKernel (-a) x = -oddKernel a x := by
  induction a using QuotientAddGroup.induction_on with
  | H a => simp [← ofReal_inj, ← QuotientAddGroup.mk_neg, oddKernel_def, jacobiTheta₂''_neg_left]

@[simp] lemma oddKernel_zero (x : ℝ) : oddKernel 0 x = 0 := by
  simpa using oddKernel_neg 0 x

lemma sinKernel_neg (a : UnitAddCircle) (x : ℝ) :
    sinKernel (-a) x = -sinKernel a x := by
  induction a using QuotientAddGroup.induction_on with
  | H a => simp [← ofReal_inj, ← QuotientAddGroup.mk_neg, sinKernel_def, jacobiTheta₂'_neg_left,
      neg_div₀]

@[simp] lemma sinKernel_zero (x : ℝ) : sinKernel 0 x = 0 := by
  simpa using sinKernel_neg 0 x

/-- The odd kernel is continuous on `Ioi 0`. -/
lemma continuousOn_oddKernel (a : UnitAddCircle) : ContinuousOn (oddKernel a) (Ioi 0) := by
  induction a using QuotientAddGroup.induction_on with | H a =>
  suffices ContinuousOn (fun x ↦ (oddKernel a x : ℂ)) (Ioi 0) from
    (continuous_re.comp_continuousOn this).congr fun a _ ↦ (ofReal_re _).symm
  simp_rw [oddKernel_def' a]
  refine fun x hx ↦ ((Continuous.continuousAt ?_).mul ?_).continuousWithinAt
  · fun_prop
  · have hf : Continuous fun u : ℝ ↦ (a * I * u, I * u) := by fun_prop
    apply ContinuousAt.add
    · exact ((continuousAt_jacobiTheta₂' (a * I * x) (by rwa [I_mul_im, ofReal_re])).comp
        (f := fun u : ℝ ↦ (a * I * u, I * u)) hf.continuousAt).div_const₀ _
    · exact continuousAt_const.mul <| (continuousAt_jacobiTheta₂ (a * I * x)
        (by rwa [I_mul_im, ofReal_re])).comp (f := fun u : ℝ ↦ (a * I * u, I * u)) hf.continuousAt

lemma continuousOn_sinKernel (a : UnitAddCircle) : ContinuousOn (sinKernel a) (Ioi 0) := by
  induction a using QuotientAddGroup.induction_on with | H a =>
  suffices ContinuousOn (fun x ↦ (sinKernel a x : ℂ)) (Ioi 0) from
    (continuous_re.comp_continuousOn this).congr fun a _ ↦ (ofReal_re _).symm
  simp_rw [sinKernel_def]
  apply (continuousOn_of_forall_continuousAt (fun x hx ↦ ?_)).div_const₀ _
  have h := continuousAt_jacobiTheta₂' a (by rwa [I_mul_im, ofReal_re])
  fun_prop

lemma oddKernel_functional_equation (a : UnitAddCircle) (x : ℝ) (hx : 0 < x) :
    oddKernel a x = Checked.div 1 (x ^ (3 / 2 : ℝ))
      (Real.rpow_ne_zero_of_pos hx _).isUnit * sinKernel a (1 / x) := by
  induction a using QuotientAddGroup.induction_on with | H a =>
  have hxi : IsUnit (↑(1 / x : ℝ) : ℂ) :=
    (ofReal_ne_zero.mpr (one_div_pos.mpr hx).ne').isUnit
  have h1 : -1 / (I * ↑(1 / x : ℝ)) = I * x := by
    apply div_eq_iff.mpr
    rw [mul_mul_mul_comm, I_mul_I, ← ofReal_mul, mul_one_div_cancel (ha := hx.ne'.isUnit),
      ofReal_one, mul_one]
  have h2 : (-I * (I * ↑(1 / x))) = 1 / x := by
    rw [← mul_assoc, neg_mul, I_mul_I, neg_neg, one_mul, ofReal_div, ofReal_one]
  have h3 : (x : ℂ) ^ (3 / 2 : ℂ) ≠ 0 := by
    simp only [Ne, cpow_eq_zero_iff, ofReal_eq_zero, hx.ne', false_and, not_false_eq_true]
  have h4 : arg x ≠ π := by rw [arg_ofReal_of_nonneg hx.le]; exact pi_ne_zero.symm
  have hp : (-I * (I * ↑(1 / x : ℝ))) ^ (3 / 2 : ℂ) = Checked.inv _ h3.isUnit := by
    rw [h2, one_div₀, inv_cpow _ _ h4]
  have hpow : IsUnit ((-I * (I * ↑(1 / x : ℝ))) ^ (3 / 2 : ℂ)) :=
    (cpow_ne_zero_iff.mpr (Or.inl (mul_ne_zero (neg_ne_zero.mpr I_ne_zero)
      (mul_ne_zero I_ne_zero hxi.ne_zero)))).isUnit
  have hi := (inv_inj₀ (ha := hpow) (hb := (inv_ne_zero (ha := h3.isUnit)).isUnit)).mpr hp
  have hquot : (-2 * π : ℂ) / (-I * (I * ↑(1 / x : ℝ))) ^ (3 / 2 : ℂ) =
      (-2 * π : ℂ) * (x : ℂ) ^ (3 / 2 : ℂ) := by
    rw [div_eq_mul_inv₀, hi, inv_inv₀]
  have hcast : (↑(x ^ (3 / 2 : ℝ)) : ℂ) = (x : ℂ) ^ (3 / 2 : ℂ) := by
    rw [ofReal_cpow hx.le]
    congr 1
    apply eq_div_iff.mpr
    rw [← ofReal_ofNat 2, ← ofReal_mul]
    norm_num
  rw [← ofReal_inj, oddKernel_def, ofReal_mul, sinKernel_def,
    jacobiTheta₂'_functional_equation' _ _
      (by rw [I_mul_im, ofReal_re]; exact one_div_pos.mpr hx), h1]
  rw [hquot, ← hcast, ofReal_div, ofReal_one]
  field

end kernel_defs

section sum_formulas

/-!
## Formulae for the kernels as sums
-/

lemma hasSum_int_oddKernel (a : ℝ) {x : ℝ} (hx : 0 < x) :
    HasSum (fun n : ℤ ↦ (n + a) * rexp (-π * (n + a) ^ 2 * x)) (oddKernel ↑a x) := by
  rw [← hasSum_ofReal, oddKernel_def' a x]
  have h1 := hasSum_jacobiTheta₂_term (a * I * x) (by rwa [I_mul_im, ofReal_re])
  have h2 := hasSum_jacobiTheta₂'_term (a * I * x) (by rwa [I_mul_im, ofReal_re])
  refine (((h2.div_const (2 * π * I)).add (h1.mul_left ↑a)).mul_left
    (cexp (-π * a ^ 2 * x))).congr_fun (fun n ↦ ?_)
  rw [jacobiTheta₂'_term, mul_assoc (2 * π * I),
    mul_div_cancel_left₀ _ (ha := two_pi_I_ne_zero.isUnit), ← add_mul, mul_left_comm,
    jacobiTheta₂_term, ← Complex.exp_add]
  push_cast
  simp only [← mul_assoc, ← add_mul]
  congrm _ * cexp (?_ * x)
  simp only [mul_right_comm _ I, add_mul, mul_assoc _ I, I_mul_I]
  ring_nf

lemma hasSum_int_sinKernel (a : ℝ) {t : ℝ} (ht : 0 < t) : HasSum
    (fun n : ℤ ↦ -I * n * cexp (2 * π * I * a * n) * rexp (-π * n ^ 2 * t)) ↑(sinKernel a t) := by
  have h : -2 * (π : ℂ) ≠ (0 : ℂ) := by
    simp only [neg_mul, ne_eq, neg_eq_zero, mul_eq_zero,
      OfNat.ofNat_ne_zero, ofReal_eq_zero, pi_ne_zero, or_self, not_false_eq_true]
  rw [sinKernel_def]
  refine ((hasSum_jacobiTheta₂'_term a
    (by rwa [I_mul_im, ofReal_re])).div_const _).congr_fun fun n ↦ ?_
  rw [jacobiTheta₂'_term, jacobiTheta₂_term, ofReal_exp, mul_assoc (-I * n), ← Complex.exp_add,
    eq_div_iff (hb := h.isUnit), ofReal_mul, ofReal_mul, ofReal_pow, ofReal_neg, ofReal_intCast,
    mul_comm _ (-2 * π : ℂ), ← mul_assoc]
  congrm ?_ * cexp (?_ + ?_)
  · simp [mul_assoc]
  · exact mul_right_comm (2 * π * I) a n
  · simp [← mul_assoc, mul_comm _ I]

lemma hasSum_nat_sinKernel (a : ℝ) {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ ↦ 2 * n * Real.sin (2 * π * a * n) * rexp (-π * n ^ 2 * t))
    (sinKernel ↑a t) := by
  rw [← hasSum_ofReal]
  have := (hasSum_int_sinKernel a ht).nat_add_neg
  simp only [Int.cast_zero, zero_mul, mul_zero, add_zero] at this
  refine this.congr_fun fun n ↦ ?_
  simp_rw [Int.cast_neg, neg_sq, mul_neg, ofReal_mul, Int.cast_natCast, ofReal_natCast,
      ofReal_ofNat, ← add_mul, ofReal_sin, Complex.sin]
  push_cast
  congr 1
  rw [← mul_div_assoc₀, ← div_mul_eq_mul_div₀, ← div_mul_eq_mul_div₀,
    div_self (ha := two_ne_zero.isUnit), one_mul, neg_mul, neg_mul, neg_neg, mul_comm _ I,
    ← mul_assoc, mul_comm _ I, neg_mul, ← sub_eq_neg_add, mul_sub]
  congr 3 <;> ring

end sum_formulas

section asymp
/-!
## Asymptotics of the kernels as `t → ∞`
-/

/-- The function `oddKernel a` has exponential decay at `+∞`, for any `a`. -/
lemma isBigO_atTop_oddKernel (a : UnitAddCircle) :
    ∃ p, 0 < p ∧ IsBigO atTop (oddKernel a) (fun x ↦ Real.exp (-p * x)) := by
  induction a using QuotientAddGroup.induction_on with | H b =>
  obtain ⟨p, hp, hp'⟩ := HurwitzKernelBounds.isBigO_atTop_F_int_one b
  refine ⟨p, hp, (Eventually.isBigO ?_).trans hp'⟩
  filter_upwards [eventually_gt_atTop 0] with t ht
  simpa [← (hasSum_int_oddKernel b ht).tsum_eq, HurwitzKernelBounds.F_int,
    HurwitzKernelBounds.f_int, abs_of_nonneg (exp_pos _).le] using
    norm_tsum_le_tsum_norm (hasSum_int_oddKernel b ht).summable.norm

/-- The function `sinKernel a` has exponential decay at `+∞`, for any `a`. -/
lemma isBigO_atTop_sinKernel (a : UnitAddCircle) :
    ∃ p, 0 < p ∧ IsBigO atTop (sinKernel a) (fun x ↦ Real.exp (-p * x)) := by
  induction a using QuotientAddGroup.induction_on with | H a =>
  obtain ⟨p, hp, hp'⟩ := HurwitzKernelBounds.isBigO_atTop_F_nat_one (le_refl 0)
  refine ⟨p, hp, (Eventually.isBigO ?_).trans (hp'.const_mul_left 2)⟩
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [HurwitzKernelBounds.F_nat, ← (hasSum_nat_sinKernel a ht).tsum_eq]
  apply tsum_of_norm_bounded (g := fun n ↦ 2 * HurwitzKernelBounds.f_nat 1 0 t n)
  · exact (HurwitzKernelBounds.summable_f_nat 1 0 ht).hasSum.mul_left _
  · intro n
    rw [norm_mul, norm_mul, norm_mul, norm_two, mul_assoc, mul_assoc,
      mul_le_mul_iff_of_pos_left two_pos, HurwitzKernelBounds.f_nat, pow_one, add_zero,
      norm_of_nonneg (exp_pos _).le, Real.norm_eq_abs, Nat.abs_cast, ← mul_assoc,
      mul_le_mul_iff_of_pos_right (exp_pos _)]
    exact mul_le_of_le_one_right (Nat.cast_nonneg _) (abs_sin_le_one _)

end asymp

section FEPair
/-!
## Construction of an FE-pair
-/

/-- A `StrongFEPair` structure with `f = oddKernel a` and `g = sinKernel a`. -/
@[simps]
def hurwitzOddFEPair (a : UnitAddCircle) : WeakFEPair ℂ where
  f := ofReal ∘ oddKernel a
  g := ofReal ∘ sinKernel a
  hf_int := (continuous_ofReal.comp_continuousOn (continuousOn_oddKernel a)).locallyIntegrableOn
    measurableSet_Ioi
  hg_int := (continuous_ofReal.comp_continuousOn (continuousOn_sinKernel a)).locallyIntegrableOn
    measurableSet_Ioi
  k := 3 / 2
  hk := by norm_num
  ε := 1
  hε := one_ne_zero
  f₀ := 0
  g₀ := 0
  hf_top r := by
    let ⟨v, hv, hv'⟩ := isBigO_atTop_oddKernel a
    rw [← isBigO_norm_left] at hv' ⊢
    simpa using hv'.trans (isLittleO_exp_neg_mul_rpow_atTop hv _).isBigO
  hg_top r := by
    let ⟨v, hv, hv'⟩ := isBigO_atTop_sinKernel a
    rw [← isBigO_norm_left] at hv' ⊢
    simpa using hv'.trans (isLittleO_exp_neg_mul_rpow_atTop hv _).isBigO
  h_feq x hx := by
    have heq := oddKernel_functional_equation a (1 / x) (one_div_pos.mpr hx)
    simpa only [one_div₀, inv_inv₀, inv_rpow hx.le, ofReal_mul, one_mul,
      ofReal_one, Function.comp_apply, smul_eq_mul, one_mul] using congrArg ofReal heq

lemma isStrong_hurwitzOddFEPair (a : UnitAddCircle) : IsStrongFEPair (hurwitzOddFEPair a) where
  hf₀ := rfl
  hg₀ := rfl

end FEPair

/-!
## Definition of the completed odd Hurwitz zeta function
-/

/-- The entire function of `s` which agrees with
`1 / 2 * Gamma ((s + 1) / 2) * π ^ (-(s + 1) / 2) * ∑' (n : ℤ), sgn (n + a) / |n + a| ^ s`
for `1 < re s`.
-/
def completedHurwitzZetaOdd (a : UnitAddCircle) (s : ℂ) : ℂ :=
  ((hurwitzOddFEPair a).Λ₀ ((s + 1) / 2)) / 2

lemma differentiable_completedHurwitzZetaOdd (a : UnitAddCircle) :
    Differentiable ℂ (completedHurwitzZetaOdd a) :=
  ((hurwitzOddFEPair a).differentiable_Λ₀.comp
    ((differentiable_id.add_const 1).div_const 2)).div_const 2

/-- The entire function of `s` which agrees with
` Gamma ((s + 1) / 2) * π ^ (-(s + 1) / 2) * ∑' (n : ℕ), sin (2 * π * a * n) / n ^ s`
for `1 < re s`.
-/
def completedSinZeta (a : UnitAddCircle) (s : ℂ) : ℂ :=
  ((hurwitzOddFEPair a).symm.Λ₀ ((s + 1) / 2)) / 2

lemma differentiable_completedSinZeta (a : UnitAddCircle) :
    Differentiable ℂ (completedSinZeta a) :=
  ((hurwitzOddFEPair a).symm.differentiable_Λ₀.comp
    ((differentiable_id.add_const 1).div_const 2)).div_const 2

/-!
## Parity and functional equations
-/

lemma completedHurwitzZetaOdd_neg (a : UnitAddCircle) (s : ℂ) :
    completedHurwitzZetaOdd (-a) s = -completedHurwitzZetaOdd a s := by
  simp [completedHurwitzZetaOdd, (isStrong_hurwitzOddFEPair _).Λ₀_eq, mellin,
    oddKernel_neg, integral_neg, neg_div₀]

lemma completedSinZeta_neg (a : UnitAddCircle) (s : ℂ) :
    completedSinZeta (-a) s = -completedSinZeta a s := by
  simp [completedSinZeta, (isStrong_hurwitzOddFEPair _).symm_Λ₀_eq, mellin, sinKernel_neg,
    integral_neg, neg_div₀]

/-- Functional equation for the odd Hurwitz zeta function. -/
theorem completedHurwitzZetaOdd_one_sub (a : UnitAddCircle) (s : ℂ) :
    completedHurwitzZetaOdd a (1 - s) = completedSinZeta a s := by
  rw [completedHurwitzZetaOdd, completedSinZeta,
    (by { push_cast; ring } : (1 - s + 1) / 2 = ↑(3 / 2 : ℝ) - (s + 1) / 2),
    ← hurwitzOddFEPair_k, (hurwitzOddFEPair a).functional_equation₀ ((s + 1) / 2),
    hurwitzOddFEPair_ε, one_smul]

/-- Functional equation for the odd Hurwitz zeta function (alternative form). -/
lemma completedSinZeta_one_sub (a : UnitAddCircle) (s : ℂ) :
    completedSinZeta a (1 - s) = completedHurwitzZetaOdd a s := by
  simp [← completedHurwitzZetaOdd_one_sub]

/-!
## Relation to the Dirichlet series for `1 < re s`
-/

/-- The completed sine zeta series on the nonzero integers. -/
lemma hasSum_int_completedSinZeta (a : ℝ) {s : ℂ} (hs : 1 < re s) :
    HasSum (fun n : {n : ℤ // n ≠ 0} ↦
      Checked.div (Gammaℝ (s + 1) * (-I) * Int.sign (n : ℤ) *
        cexp (2 * π * I * a * (n : ℤ))) ((↑|(n : ℤ)| : ℂ) ^ s)
        (cpow_ne_zero_iff.mpr (Or.inl (Int.cast_ne_zero.mpr (abs_ne_zero.mpr n.2)))).isUnit / 2)
      (completedSinZeta a s) := by
  let c (n : ℤ) : ℂ := -I * cexp (2 * π * I * a * n) / 2
  have hc (n : ℤ) : ‖c n‖ = 1 / 2 := by
    simp only [c, (by push_cast; ring : 2 * π * I * a * n = ↑(2 * π * a * n) * I),
      norm_div, Complex.norm_two, norm_mul, norm_neg, norm_I, one_mul, norm_exp_ofReal_mul_I]
  have hF t (ht : 0 < t) : HasSum (fun n : ℤ ↦ c n * n * rexp (-π * n ^ 2 * t))
      ((sinKernel a t : ℂ) / 2) := by
    refine ((hasSum_int_sinKernel a ht).div_const 2).congr_fun fun n ↦ ?_
    rw [div_mul_eq_mul_div₀, div_mul_eq_mul_div₀, mul_right_comm (-I)]
  have hseries : Summable (fun n : {n : ℤ // (n : ℝ) ≠ 0} ↦
      Checked.div ‖c n‖ (|(n : ℝ)| ^ s.re)
        (Real.rpow_ne_zero_of_pos (abs_pos.mpr n.2) s.re).isUnit) := by
    have hreal := (summable_one_div_int_add_rpow 0 s.re).mpr hs
    let e := Equiv.subtypeEquivRight (fun n : ℤ ↦
      (show ((n : ℝ) ≠ 0) ↔ (n : ℝ) + 0 ≠ 0 by rw [add_zero]))
    have hsum := e.summable_iff.mpr (hreal.div_const 2 (hb := two_ne_zero.isUnit))
    apply hsum.congr
    intro n
    change 1 / |(n : ℝ) + 0| ^ s.re / 2 = ‖c n‖ / |(n : ℝ)| ^ s.re
    simp only [add_zero, hc]
    exact div_right_comm₀
  have hbase := hasSum_mellin_pi_mul_sq' (zero_lt_one.trans hs)
    (fun t ↦ by simpa only [ofReal_intCast] using hF t.val t.property) hseries
  rw [mellin_div_const] at hbase
  rw [completedSinZeta, (isStrong_hurwitzOddFEPair _).symm_Λ₀_eq]
  let e : {n : ℤ // n ≠ 0} ≃ {n : ℤ // (n : ℝ) ≠ 0} :=
    Equiv.subtypeEquivRight (fun n ↦ by simp only [Int.cast_ne_zero])
  apply (e.hasSum_iff.mpr hbase).congr_fun
  intro n
  simp only [e, c, Function.comp_def, Equiv.subtypeEquivRight_apply, Int.sign_eq_sign,
    SignType.intCast_cast, sign_intCast, ← Int.cast_abs, ofReal_intCast]
  field

/-- The completed sine zeta series on the positive integers. -/
lemma hasSum_nat_completedSinZeta (a : ℝ) {s : ℂ} (hs : 1 < re s) :
    HasSum (fun n : ℕ+ ↦
      Checked.div (Gammaℝ (s + 1) * Real.sin (2 * π * a * (n : ℕ))) (((n : ℕ) : ℂ) ^ s)
        (cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr (ne_of_gt n.pos)))).isUnit)
      (completedSinZeta a s) := by
  refine (hasSum_int_completedSinZeta a hs).int_pos_add_neg.congr_fun fun n ↦ ?_
  simp only [abs_neg, Int.sign_neg, Int.cast_neg, Int.cast_natCast, Nat.abs_cast,
    Int.sign_natCast_of_ne_zero (ne_of_gt n.pos), Int.cast_one, ofReal_sin, Complex.sin,
    ofReal_mul, ofReal_ofNat, ofReal_natCast, mul_neg]
  rw [show -(2 * π * a * (n : ℕ)) * I = -(2 * π * I * a * (n : ℕ)) by ring,
    show 2 * π * a * (n : ℕ) * I = 2 * π * I * a * (n : ℕ) by ring]
  field

/-- The completed odd Hurwitz zeta series with zero frequencies omitted. -/
lemma hasSum_int_completedHurwitzZetaOdd (a : ℝ) {s : ℂ} (hs : 1 < re s) :
    HasSum (fun n : {n : ℤ // (n : ℝ) + a ≠ 0} ↦
      Checked.div (Gammaℝ (s + 1) * SignType.sign ((n : ℝ) + a))
        ((↑|(n : ℝ) + a| : ℂ) ^ s)
        (cpow_ne_zero_iff.mpr (Or.inl (ofReal_ne_zero.mpr (abs_ne_zero.mpr n.2)))).isUnit / 2)
      (completedHurwitzZetaOdd a s) := by
  let r (n : ℤ) : ℝ := n + a
  let c (n : ℤ) : ℂ := 1 / 2
  have hF t (ht : 0 < t) : HasSum (fun n : ℤ ↦ c n * r n * rexp (-π * (r n) ^ 2 * t))
      ((oddKernel a t : ℂ) / 2) := by
    refine ((hasSum_ofReal.mpr (hasSum_int_oddKernel a ht)).div_const 2).congr_fun fun n ↦ ?_
    simp only [r, c, ofReal_mul, ofReal_add, ofReal_intCast, div_eq_mul_inv₀, one_mul]
    ring
  have hseries : Summable (fun n : {n : ℤ // r n ≠ 0} ↦
      Checked.div ‖c n‖ (|r n| ^ s.re)
        (Real.rpow_ne_zero_of_pos (abs_pos.mpr n.2) s.re).isUnit) := by
    apply (((summable_one_div_int_add_rpow a s.re).mpr hs).div_const 2
      (hb := two_ne_zero.isUnit)).congr
    intro n
    simp only [r, c, norm_div, norm_one, Complex.norm_two]
    exact div_right_comm₀
  have hbase := hasSum_mellin_pi_mul_sq' (zero_lt_one.trans hs)
    (fun t ↦ hF t.val t.property) hseries
  rw [mellin_div_const] at hbase
  rw [completedHurwitzZetaOdd, (isStrong_hurwitzOddFEPair _).Λ₀_eq]
  apply hbase.congr_fun
  intro n
  simp only [r, c]
  field
/-!
## Non-completed zeta functions
-/

/-- The odd part of the Hurwitz zeta function, i.e. the meromorphic function of `s` which agrees
with `1 / 2 * ∑' (n : ℤ), sign (n + a) / |n + a| ^ s` for `1 < re s` -/
noncomputable def hurwitzZetaOdd (a : UnitAddCircle) (s : ℂ) :=
  completedHurwitzZetaOdd a s * reciprocalGammaℝ (s + 1)

lemma hurwitzZetaOdd_neg (a : UnitAddCircle) (s : ℂ) :
    hurwitzZetaOdd (-a) s = -hurwitzZetaOdd a s := by
  simp_rw [hurwitzZetaOdd, completedHurwitzZetaOdd_neg, neg_mul]

/-- The odd Hurwitz zeta function is differentiable everywhere. -/
lemma differentiable_hurwitzZetaOdd (a : UnitAddCircle) :
    Differentiable ℂ (hurwitzZetaOdd a) :=
  (differentiable_completedHurwitzZetaOdd a).mul <| differentiable_reciprocalGammaℝ.comp <|
    differentiable_id.add <| differentiable_const _

/-- The sine zeta function, i.e. the meromorphic function of `s` which agrees
with `∑' (n : ℕ), sin (2 * π * a * n) / n ^ s` for `1 < re s`. -/
noncomputable def sinZeta (a : UnitAddCircle) (s : ℂ) :=
  completedSinZeta a s * reciprocalGammaℝ (s + 1)

lemma sinZeta_neg (a : UnitAddCircle) (s : ℂ) :
    sinZeta (-a) s = -sinZeta a s := by
  simp_rw [sinZeta, completedSinZeta_neg, neg_mul]

/-- The sine zeta function is differentiable everywhere. -/
lemma differentiableAt_sinZeta (a : UnitAddCircle) :
    Differentiable ℂ (sinZeta a) :=
  (differentiable_completedSinZeta a).mul <| differentiable_reciprocalGammaℝ.comp <|
    differentiable_id.add <| differentiable_const _

/-- The odd Hurwitz zeta series with zero frequencies omitted. -/
theorem hasSum_int_hurwitzZetaOdd (a : ℝ) {s : ℂ} (hs : 1 < re s) :
    HasSum (fun n : {n : ℤ // (n : ℝ) + a ≠ 0} ↦
      Checked.div (SignType.sign ((n : ℝ) + a) : ℂ) ((↑|(n : ℝ) + a| : ℂ) ^ s)
        (cpow_ne_zero_iff.mpr (Or.inl (ofReal_ne_zero.mpr (abs_ne_zero.mpr n.2)))).isUnit / 2)
      (hurwitzZetaOdd a s) := by
  rw [hurwitzZetaOdd]
  have hpos : 0 < (s + 1).re := by rw [add_re, one_re]; linarith
  have hreg : ∀ n : ℕ, s + 1 ≠ -(2 * n) := by
    intro n hn
    have hr := congrArg re hn
    norm_num at hr
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hG : IsUnit (Gammaℝ (s + 1)) := (Gammaℝ_ne_zero_of_re_pos hpos).isUnit
  apply ((hasSum_int_completedHurwitzZetaOdd a hs).mul_right
    (reciprocalGammaℝ (s + 1))).congr_fun
  intro n
  rw [reciprocalGammaℝ_eq_inv hreg]
  field

/-- Splitting the odd Hurwitz series gives two independent denominator domains; the
reflected branch carries a minus sign. -/
lemma hasSum_nat_hurwitzZetaOdd (a : ℝ) {s : ℂ} (hs : 1 < re s) :
    HasSum (Sum.elim
      (fun n : {n : ℕ // (n : ℝ) + a ≠ 0} ↦
        Checked.div (SignType.sign ((n : ℝ) + a) : ℂ) ((↑|(n : ℝ) + a| : ℂ) ^ s)
          (cpow_ne_zero_iff.mpr (Or.inl (ofReal_ne_zero.mpr (abs_ne_zero.mpr n.2)))).isUnit / 2)
      (fun n : {n : ℕ // (n : ℝ) + 1 - a ≠ 0} ↦
        -(Checked.div (SignType.sign ((n : ℝ) + 1 - a) : ℂ) ((↑|(n : ℝ) + 1 - a| : ℂ) ^ s)
          (cpow_ne_zero_iff.mpr (Or.inl (ofReal_ne_zero.mpr (abs_ne_zero.mpr n.2)))).isUnit / 2)))
      (hurwitzZetaOdd a s) := by
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
  have hneg (n : ℕ) : (Int.negSucc n : ℝ) + a = -((n : ℝ) + 1 - a) := by
    push_cast
    ring
  apply (e.symm.hasSum_iff.mpr (hasSum_int_hurwitzZetaOdd a hs)).congr_fun
  rintro (n | n)
  · simp [e, Int.ofNat_eq_natCast]
  · dsimp only [Function.comp_apply, e, Equiv.coe_fn_symm_mk, Sum.elim_inr]
    simp only [hneg, abs_neg, Left.sign_neg, SignType.coe_neg, neg_div₀]

/-- The odd natural Hurwitz series without absolute values, on the exact component domains. -/
lemma hasSum_nat_hurwitzZetaOdd_of_mem_Icc {a : ℝ} (ha : a ∈ Icc 0 1) {s : ℂ} (hs : 1 < re s) :
    HasSum (Sum.elim
      (fun n : {n : ℕ // (n : ℝ) + a ≠ 0} ↦
        Checked.div 1 ((((n : ℕ) : ℂ) + a) ^ s)
          (cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast n.2))).isUnit / 2)
      (fun n : {n : ℕ // (n : ℝ) + 1 - a ≠ 0} ↦
        -(Checked.div 1 ((((n : ℕ) : ℂ) + 1 - a) ^ s)
          (cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast n.2))).isUnit / 2)))
      (hurwitzZetaOdd a s) := by
  apply (hasSum_nat_hurwitzZetaOdd a hs).congr_fun
  rintro (n | n)
  · have hpos : (0 : ℝ) < (n : ℕ) + a :=
      lt_of_le_of_ne (add_nonneg (Nat.cast_nonneg _) ha.1) n.2.symm
    simp [sign_pos hpos, abs_of_pos hpos]
  · have hnonneg : (0 : ℝ) ≤ (n : ℕ) + 1 - a := by
      linarith [Nat.cast_nonneg (α := ℝ) (n : ℕ), ha.2]
    have hpos : (0 : ℝ) < (n : ℕ) + 1 - a := lt_of_le_of_ne hnonneg n.2.symm
    simp [sign_pos hpos, abs_of_pos hpos]

/-- The sine zeta series on the nonzero integers. -/
theorem hasSum_int_sinZeta (a : ℝ) {s : ℂ} (hs : 1 < re s) :
    HasSum (fun n : {n : ℤ // n ≠ 0} ↦
      Checked.div (-I * Int.sign (n : ℤ) * cexp (2 * π * I * a * (n : ℤ)))
        ((↑|(n : ℤ)| : ℂ) ^ s)
        (cpow_ne_zero_iff.mpr (Or.inl (Int.cast_ne_zero.mpr (abs_ne_zero.mpr n.2)))).isUnit / 2)
      (sinZeta a s) := by
  rw [sinZeta]
  have hpos : 0 < (s + 1).re := by rw [add_re, one_re]; linarith
  have hreg : ∀ n : ℕ, s + 1 ≠ -(2 * n) := by
    intro n hn
    have hr := congrArg re hn
    norm_num at hr
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hG : IsUnit (Gammaℝ (s + 1)) := (Gammaℝ_ne_zero_of_re_pos hpos).isUnit
  apply ((hasSum_int_completedSinZeta a hs).mul_right
    (reciprocalGammaℝ (s + 1))).congr_fun
  intro n
  rw [reciprocalGammaℝ_eq_inv hreg]
  field

/-- The sine zeta series on the positive integers. -/
lemma hasSum_nat_sinZeta (a : ℝ) {s : ℂ} (hs : 1 < re s) :
    HasSum (fun n : ℕ+ ↦
      Checked.div (Real.sin (2 * π * a * (n : ℕ)) : ℂ) (((n : ℕ) : ℂ) ^ s)
        (cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr (ne_of_gt n.pos)))).isUnit)
      (sinZeta a s) := by
  refine (hasSum_int_sinZeta a hs).int_pos_add_neg.congr_fun fun n ↦ ?_
  simp only [abs_neg, Int.sign_neg, Int.cast_neg, Int.cast_natCast, Nat.abs_cast,
    Int.sign_natCast_of_ne_zero (ne_of_gt n.pos), Int.cast_one, ofReal_sin, Complex.sin,
    ofReal_mul, ofReal_ofNat, ofReal_natCast, mul_neg]
  rw [show -(2 * π * a * (n : ℕ)) * I = -(2 * π * I * a * (n : ℕ)) by ring,
    show 2 * π * a * (n : ℕ) * I = 2 * π * I * a * (n : ℕ) by ring]
  field

/-- The sine zeta Dirichlet series. -/
lemma LSeriesHasSum_sin (a : ℝ) {s : ℂ} (hs : 1 < re s) :
    LSeriesHasSum (Real.sin <| 2 * π * a * ·) s (sinZeta a s) :=
  LSeriesHasSum_iff_hasSum_pnat.mpr (hasSum_nat_sinZeta a hs)

/-- The trivial zeroes of the odd Hurwitz zeta function. -/
theorem hurwitzZetaOdd_neg_two_mul_nat_sub_one (a : UnitAddCircle) (n : ℕ) :
    hurwitzZetaOdd a (-2 * n - 1) = 0 := by
  rw [hurwitzZetaOdd,
    reciprocalGammaℝ_eq_zero_iff.mpr ⟨n, by rw [neg_mul, sub_add_cancel]⟩, mul_zero]

/-- The trivial zeroes of the sine zeta function. -/
theorem sinZeta_neg_two_mul_nat_sub_one (a : UnitAddCircle) (n : ℕ) :
    sinZeta a (-2 * n - 1) = 0 := by
  rw [sinZeta, reciprocalGammaℝ_eq_zero_iff.mpr ⟨n, by rw [neg_mul, sub_add_cancel]⟩, mul_zero]

/-- If `s` is not in `-ℕ`, then `hurwitzZetaOdd a (1 - s)` is an explicit multiple of
`sinZeta s`. -/
lemma hurwitzZetaOdd_one_sub (a : UnitAddCircle) {s : ℂ} (hs : ∀ (n : ℕ), s ≠ -n) :
    hurwitzZetaOdd a (1 - s) = 2 * (2 * π) ^ (-s) * Gamma s * sin (π * s / 2) * sinZeta a s := by
  rw [← Gammaℂ, hurwitzZetaOdd, (by ring : 1 - s + 1 = 2 - s),
    reciprocalGammaℝ_two_sub hs, completedHurwitzZetaOdd_one_sub, sinZeta]
  ring

/-- If `s` is not in `-ℕ`, then `sinZeta a (1 - s)` is an explicit multiple of
`hurwitzZetaOdd s`. -/
lemma sinZeta_one_sub (a : UnitAddCircle) {s : ℂ} (hs : ∀ (n : ℕ), s ≠ -n) :
    sinZeta a (1 - s) = 2 * (2 * π) ^ (-s) * Gamma s * sin (π * s / 2) * hurwitzZetaOdd a s := by
  rw [← Gammaℂ, sinZeta, (by ring : 1 - s + 1 = 2 - s), reciprocalGammaℝ_two_sub hs,
    completedSinZeta_one_sub, hurwitzZetaOdd]
  ring

end HurwitzZeta
