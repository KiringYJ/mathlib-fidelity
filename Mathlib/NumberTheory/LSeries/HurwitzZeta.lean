/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
public import Mathlib.NumberTheory.LSeries.HurwitzZetaOdd
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# The Hurwitz zeta function

This file gives the definition and properties of the following two functions:

* The **Hurwitz zeta function**, which is the meromorphic continuation to all `s ∈ ℂ` of the
  function defined for `1 < re s` by the series

  `∑' n, 1 / (n + a) ^ s`

  for a parameter `a ∈ ℝ`, with the sum taken over all `n` such that `n + a > 0`;

* the related sum, which we call the "**exponential zeta function**" (does it have a standard name?)

  `∑' n : ℕ+, exp (2 * π * I * n * a) / n ^ s`.

## Main definitions and results

* `hurwitzZeta`: the Hurwitz zeta function (defined to be periodic in `a` with period 1)
* `expZeta`: the exponential zeta function
* `hasSum_hurwitzZeta_of_one_lt_re` and `hasSum_expZeta_of_one_lt_re`:
  relation to Dirichlet series for `1 < re s`
* ` hurwitzZeta_residue_one` shows that the residue at `s = 1` equals `1`
* `differentiableAt_hurwitzZeta` and `differentiableAt_expZeta`: analyticity away from `s = 1`
* `hurwitzZeta_one_sub` and `expZeta_one_sub`: functional equations `s ↔ 1 - s`.
-/

@[expose] public section

open Set Real Complex Filter

open scoped Topology

namespace HurwitzZeta

/-!
## The Hurwitz zeta function
-/

/-- The Hurwitz zeta function, which is the meromorphic continuation of
`∑ (n : ℕ), 1 / (n + a) ^ s` if `0 ≤ a ≤ 1`. See `hasSum_hurwitzZeta_of_one_lt_re` for the relation
to the Dirichlet series in the convergence range. -/
noncomputable def hurwitzZeta (a : UnitAddCircle) (s : ℂ)
    (hs : s ≠ 1 := by checked_nonzero) :=
  hurwitzZetaEven a s (hs := hs) + hurwitzZetaOdd a s

lemma hurwitzZetaEven_eq (a : UnitAddCircle) (s : ℂ)
    {hs : s ≠ 1} :
    hurwitzZetaEven a s = (hurwitzZeta a s + hurwitzZeta (-a) s) / 2 := by
  simp only [hurwitzZeta, hurwitzZetaEven_neg, hurwitzZetaOdd_neg]
  ring_nf

lemma hurwitzZetaOdd_eq (a : UnitAddCircle) (s : ℂ)
    {hs : s ≠ 1} :
    hurwitzZetaOdd a s = (hurwitzZeta a s - hurwitzZeta (-a) s) / 2 := by
  simp only [hurwitzZeta, hurwitzZetaEven_neg, hurwitzZetaOdd_neg]
  ring_nf

/-- The Hurwitz zeta function is differentiable away from `s = 1`. -/
lemma differentiableAt_hurwitzZeta (a : UnitAddCircle) {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ
      (fun z : {z : ℂ // z ≠ 1} ↦ hurwitzZeta a z (hs := z.2))
      ⟨s, hs⟩ (fun z ↦ (z : ℂ)) := by
  apply (differentiableAt_hurwitzZetaEven a hs).add
  obtain ⟨d, hd⟩ := differentiable_hurwitzZetaOdd a s
  exact ⟨d, HasFDerivAtFilter.comp_tendsto hd Subtype.val
    ((continuous_subtype_val.tendsto ⟨s, hs⟩).prodMap (tendsto_pure_pure ..))⟩

/-- The Hurwitz zeta Dirichlet series for `a ∈ Icc 0 1`, indexed by the nonzero denominators. -/
lemma hasSum_hurwitzZeta_of_one_lt_re {a : ℝ} (ha : a ∈ Icc 0 1) {s : ℂ} (hs : 1 < re s) :
    HasSum (fun n : {n : ℕ // (n : ℝ) + a ≠ 0} ↦
      Checked.div 1 ((((n : ℕ) : ℂ) + a) ^ s)
        (cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast n.2))).isUnit)
      (hurwitzZeta a s (by rintro rfl; simp at hs)) := by
  let j : {n : ℕ // (n : ℝ) + a ≠ 0} →
      {n : ℕ // (n : ℝ) + a ≠ 0} ⊕ {n : ℕ // (n : ℝ) + 1 - a ≠ 0} := Sum.inl
  have hj : Function.Injective j := Sum.inl_injective
  rw [← hasSum_extend_zero hj]
  apply ((hasSum_nat_hurwitzZetaEven_of_mem_Icc ha hs).add
    (hasSum_nat_hurwitzZetaOdd_of_mem_Icc ha hs)).congr_fun
  rintro (n | n)
  · rw [show Sum.inl n = j n from rfl, hj.extend_apply]
    simp only [j, Sum.elim_inl]
    ring
  · rw [Function.extend_apply' _ _ _ (by simp [j])]
    simp only [Pi.zero_apply, Sum.elim_inr, add_neg_cancel]

/-- The residue of the Hurwitz zeta function at `s = 1` is `1`. -/
lemma hurwitzZeta_residue_one (a : UnitAddCircle) :
    Tendsto (fun s : {s : ℂ // s ≠ 1} ↦
      ((s : ℂ) - 1) * hurwitzZeta a s (hs := s.2))
      (comap Subtype.val (𝓝 1)) (𝓝 1) := by
  have hz : Tendsto (Subtype.val : {s : ℂ // s ≠ 1} → ℂ) (comap Subtype.val (𝓝 1)) (𝓝 1) :=
    tendsto_comap
  have hodd := ((continuous_id.sub (continuous_const (y := (1 : ℂ)))).mul
    (differentiable_hurwitzZetaOdd a).continuous).continuousAt.tendsto.comp hz
  simpa only [hurwitzZeta, Function.comp_apply, Pi.mul_apply, Pi.sub_apply, id_eq, mul_add,
    sub_self, zero_mul, add_zero] using
    (hurwitzZetaEven_residue_one a).add hodd

/-- The entire regular part of Hurwitz zeta after removing its Gamma-weighted principal part. -/
noncomputable def hurwitzZetaRegularPart (a : UnitAddCircle) (s : ℂ) : ℂ :=
  hurwitzZetaEvenRegularPart a s + hurwitzZetaOdd a s

lemma differentiable_hurwitzZetaRegularPart (a : UnitAddCircle) :
    Differentiable ℂ (hurwitzZetaRegularPart a) :=
  (differentiable_hurwitzZetaEvenRegularPart a).add (differentiable_hurwitzZetaOdd a)

lemma hurwitzZeta_eq_regularPart_add {a : UnitAddCircle} {s : ℂ} (hs : s ≠ 1) :
    hurwitzZeta a s = hurwitzZetaRegularPart a s + reciprocalGammaℝ s / (s - 1) := by
  rw [hurwitzZeta, hurwitzZetaEven_eq_regularPart_add hs, hurwitzZetaRegularPart]
  abel

/-- Removing the principal part has the finite value of the entire regular part as its limit. -/
lemma tendsto_hurwitzZeta_sub_principalPart_nhds_one (a : UnitAddCircle) :
    Tendsto (fun s : {s : ℂ // s ≠ 1} ↦
      hurwitzZeta a s (hs := s.2) - reciprocalGammaℝ s / ((s : ℂ) - 1))
      (comap Subtype.val (𝓝 1)) (𝓝 (hurwitzZetaRegularPart a 1)) := by
  apply (((differentiable_hurwitzZetaRegularPart a).continuous.tendsto 1).comp
    tendsto_comap).congr
  intro s
  simp only [Function.comp_def, hurwitzZeta_eq_regularPart_add s.2, add_sub_cancel_right]

/-- The difference of regular parts is the entire continuation of a Hurwitz-zeta difference. -/
lemma hurwitzZeta_sub_eq_regularPart_sub {a b : UnitAddCircle} {s : ℂ} (hs : s ≠ 1) :
    hurwitzZeta a s - hurwitzZeta b s =
      hurwitzZetaRegularPart a s - hurwitzZetaRegularPart b s := by
  rw [hurwitzZeta_eq_regularPart_add hs, hurwitzZeta_eq_regularPart_add hs]
  abel

lemma differentiable_hurwitzZetaRegularPart_sub (a b : UnitAddCircle) :
    Differentiable ℂ (fun s ↦ hurwitzZetaRegularPart a s - hurwitzZetaRegularPart b s) :=
  (differentiable_hurwitzZetaRegularPart a).sub (differentiable_hurwitzZetaRegularPart b)

/-!
## The exponential zeta function
-/

/-- Meromorphic continuation of `∑' n : ℕ+, exp (2 * π * I * a * n) / n ^ s`, evaluated
on its regular domain. For `a = 0` the point `s = 1` is a pole. -/
noncomputable def expZeta (a : UnitAddCircle) (s : ℂ)
    (hs : s ≠ 1 ∨ a ≠ 0 := by assumption) : ℂ :=
  cosZeta a s hs + I * sinZeta a s

lemma cosZeta_eq (a : UnitAddCircle) (s : ℂ) {hs : s ≠ 1 ∨ a ≠ 0} :
    cosZeta a s hs = (expZeta a s hs +
      expZeta (-a) s (hs.imp_right (fun h ↦ by simpa only [neg_ne_zero] using h))) / 2 := by
  simp only [expZeta, cosZeta_neg (hs := hs), sinZeta_neg]
  ring_nf

lemma sinZeta_eq (a : UnitAddCircle) (s : ℂ) (hs : s ≠ 1 ∨ a ≠ 0) :
    sinZeta a s = (expZeta a s hs -
      expZeta (-a) s (hs.imp_right (fun h ↦ by simpa only [neg_ne_zero] using h))) / (2 * I) := by
  simp only [expZeta, cosZeta_neg (hs := hs), sinZeta_neg]
  field

lemma hasSum_expZeta_of_one_lt_re (a : ℝ) {s : ℂ} (hs : 1 < re s) :
    HasSum (fun n : ℕ+ ↦ cexp (2 * π * I * a * (n : ℕ)) / (n : ℂ) ^ s)
      (expZeta a s (Or.inl (by rintro rfl; simp at hs))) := by
  apply ((hasSum_nat_cosZeta a hs).add ((hasSum_nat_sinZeta a hs).mul_left I)).congr_fun
  intro n
  symm
  change (Real.cos (2 * π * a * (n : ℕ)) : ℂ) / (n : ℂ) ^ s +
      I * ((Real.sin (2 * π * a * (n : ℕ)) : ℂ) / (n : ℂ) ^ s) = _
  rw [← mul_div_assoc₀, ← add_div, mul_comm I, ofReal_cos, ofReal_sin, cos_add_sin_I]
  congr 2
  push_cast
  ring

lemma differentiableAt_expZeta (a : UnitAddCircle) (s : ℂ) (hs : s ≠ 1 ∨ a ≠ 0) :
    DifferentiableAt ℂ
      (fun z : {z : ℂ // z ≠ 1 ∨ a ≠ 0} ↦ expZeta a z z.2)
      ⟨s, hs⟩ (fun z ↦ (z : ℂ)) := by
  apply (differentiableAt_cosZeta a hs).add
  obtain ⟨d, hd⟩ := (differentiableAt_sinZeta a s).const_mul I
  exact ⟨d, HasFDerivAtFilter.comp_tendsto hd Subtype.val
    ((continuous_subtype_val.tendsto ⟨s, hs⟩).prodMap (tendsto_pure_pure ..))⟩

/-- If `a ≠ 0` then the exponential zeta function is analytic everywhere. -/
lemma differentiable_expZeta_of_ne_zero {a : UnitAddCircle} (ha : a ≠ 0) :
    Differentiable ℂ (fun s ↦ expZeta a s (Or.inr ha)) :=
  (differentiable_cosZeta_of_ne_zero ha).add ((differentiableAt_sinZeta a).const_mul I)

/-- Reformulation of `hasSum_expZeta_of_one_lt_re` using `LSeriesHasSum`. -/
lemma LSeriesHasSum_exp (a : ℝ) {s : ℂ} (hs : 1 < re s) :
    LSeriesHasSum (cexp <| 2 * π * I * a * ·) s
      (expZeta a s (Or.inl (by rintro rfl; simp at hs))) :=
  LSeriesHasSum_iff_hasSum_pnat.mpr (hasSum_expZeta_of_one_lt_re a hs)

/-!
## The functional equation
-/

lemma hurwitzZeta_one_sub (a : UnitAddCircle) {s : ℂ}
    (hs : ∀ (n : ℕ), s ≠ -n) (hs' : a ≠ 0 ∨ s ≠ 1) :
    hurwitzZeta a (1 - s) (hs := by intro h; apply hs 0; push_cast; linear_combination -h) =
      (2 * π) ^ (-s) * Gamma s *
        (exp (-π * I * s / 2) * expZeta a s hs'.symm +
          exp (π * I * s / 2) *
            expZeta (-a) s (hs'.symm.imp_right (fun h ↦ by simpa only [neg_ne_zero] using h))) := by
  rw [hurwitzZeta, hurwitzZetaEven_one_sub a hs hs', hurwitzZetaOdd_one_sub a hs,
    expZeta, expZeta, Complex.cos, Complex.sin, sinZeta_neg, cosZeta_neg (hs := hs'.symm)]
  rw [show ↑π * I * s / 2 = ↑π * s / 2 * I by ring,
    show -↑π * I * s / 2 = -(↑π * s / 2) * I by ring]
  -- these `generalize` commands are not strictly needed for the `ring_nf` call to succeed, but
  -- make it run faster:
  generalize (2 * π : ℂ) ^ (-s) = x
  generalize (↑π * s / 2 * I).exp = y
  generalize (-(↑π * s / 2) * I).exp = z
  ring_nf

/-- Functional equation for the exponential zeta function. -/
lemma expZeta_one_sub (a : UnitAddCircle) {s : ℂ} (hs : ∀ (n : ℕ), s ≠ 1 - n) :
    expZeta a (1 - s) (Or.inl (by intro h; apply hs 1; norm_num; linear_combination -h)) =
      (2 * π) ^ (-s) * Gamma s *
        (exp (π * I * s / 2) * hurwitzZeta a s (by simpa using hs 0) +
          exp (-π * I * s / 2) * hurwitzZeta (-a) s (by simpa using hs 0)) := by
  have hs' (n : ℕ) : s ≠ -↑n := by
    convert! hs (n + 1) using 1
    push_cast
    ring
  rw [expZeta, cosZeta_one_sub a hs, sinZeta_one_sub a hs', hurwitzZeta, hurwitzZeta,
    hurwitzZetaEven_neg, hurwitzZetaOdd_neg, Complex.cos, Complex.sin]
  rw [show ↑π * I * s / 2 = ↑π * s / 2 * I by ring,
    show -↑π * I * s / 2 = -(↑π * s / 2) * I by ring]
  -- these `generalize` commands are not strictly needed for the `ring_nf` call to succeed, but
  -- make it run faster:
  generalize (2 * π : ℂ) ^ (-s) = x
  generalize (↑π * s / 2 * I).exp = y
  generalize (-(↑π * s / 2) * I).exp = z
  ring_nf
  rw [I_sq]
  ring_nf

end HurwitzZeta
