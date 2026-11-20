/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, David Loeffler
-/
module

public import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Complex.UpperHalfPlane.QParam
public import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Summable
public import Mathlib.NumberTheory.TsumDivisorsAntidiagonal

/-!
# Dedekind eta function

## Main definitions

* We define the Dedekind eta function as the infinite product
  `η(z) = q ^ 1/24 * ∏' (1 - q ^ (n + 1))` where `q = e ^ (2πiz)` and `z` is in the upper
  half-plane. The product is taken over all non-negative integers `n`. We then show it is
  non-vanishing and differentiable on the upper half-plane. Lastly, we compute its logarithmic
  derivative and show that it is a multiple of the Eisenstein series `E2`.

## References
* [F. Diamond and J. Shurman, *A First Course in Modular Forms*][diamondshurman2005], section 1.2
-/

@[expose] public section

open Set Function Complex
open UpperHalfPlane hiding I
open scoped Real ArithmeticFunction.sigma

local notation "ℍₒ" => upperHalfPlaneSet

namespace ModularForm

/-- The q term inside the product defining the eta function. It is defined as
`eta_q n z = e ^ (2 π i (n + 1) z)`. -/
noncomputable abbrev eta_q (n : ℕ) (z : ℂ) := (Periodic.qParam 1 z one_ne_zero) ^ (n + 1)

lemma eta_q_eq_cexp (n : ℕ) (z : ℂ) : eta_q n z = cexp (2 * π * I * (n + 1) * z) := by
  simp [eta_q, Periodic.qParam, ← Complex.exp_nsmul]
  ring_nf

lemma eta_q_eq_pow (n : ℕ) (z : ℂ) : eta_q n z = cexp (2 * π * I * z) ^ (n + 1) := by
  simp [eta_q, Periodic.qParam]

lemma one_sub_eta_q_ne_zero (n : ℕ) {z : ℂ} (hz : z ∈ ℍₒ) : 1 - eta_q n z ≠ 0 := by
  rw [eta_q_eq_cexp, sub_ne_zero]
  intro h
  simpa [← mul_assoc, ← h] using norm_exp_two_pi_I_lt_one ⟨(n + 1) • z, by
    simpa [(show 0 < (n + 1 : ℝ) by positivity)] using hz⟩

/-- The eta function, whose value at z is `q^ 1 / 24 * ∏' 1 - q ^ (n + 1)` for `q = e ^ 2 π i z`. -/
noncomputable def eta (z : ℂ) := Periodic.qParam 24 z (by norm_num) * ∏' n, (1 - eta_q n z)

/-- Notation for the Dedekind eta function. -/
scoped[ModularForm] notation "η" => eta

/-- For `‖q‖ < 1`, the infinite product `∏ (1 - q^(n+1))` is multipliable. -/
lemma multipliable_one_sub_pow {q : ℂ} (hq : ‖q‖ < 1) :
    Multipliable fun n : ℕ ↦ 1 - q ^ (n + 1) := by
  apply multipliable_one_add_of_summable (f := fun n ↦ -q ^ (n + 1))
  simpa using (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (norm_nonneg _) hq)

/-- The infinite product `∏ (1 - q^(n+1))` converges locally uniformly on the open unit disc,
with limit `q ↦ ∏' n, (1 - q^(n+1))`. -/
lemma multipliableLocallyUniformlyOn_one_sub_pow :
    MultipliableLocallyUniformlyOn (fun n q ↦ 1 - q ^ (n + 1)) (Metric.ball (0 : ℂ) 1) := by
  use fun q ↦ ∏' n, (1 - q ^ (n + 1))
  simp_rw [sub_eq_add_neg]
  apply hasProdLocallyUniformlyOn_of_forall_compact Metric.isOpen_ball
  intro K hK hcK
  rcases K.eq_empty_or_nonempty with hN | hN
  · simpa [hasProdUniformlyOn_iff_tendstoUniformlyOn, hN] using tendstoUniformlyOn_empty
  · obtain ⟨q₀, hq₀, _, HB⟩ := hcK.exists_sSup_image_eq_and_ge hN
      (show ContinuousOn (fun q : ℂ ↦ ‖q‖) K by fun_prop)
    refine ((summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (norm_nonneg _)
      (by simpa [Metric.mem_ball, dist_zero_right] using hK hq₀))).hasProdUniformlyOn_nat_one_add
      hcK (.of_forall fun n x hx ↦ ?_) (fun _ ↦ by fun_prop)
    simpa using pow_le_pow_left₀ (norm_nonneg _) (HB x hx) (n + 1)

/-- The infinite product `q ↦ ∏' n, (1 - q^(n+1))` is differentiable on the open unit disc. -/
lemma differentiableOn_tprod_one_sub_pow :
    DifferentiableOn ℂ (fun q ↦ ∏' n, (1 - q ^ (n + 1))) (Metric.ball (0 : ℂ) 1) :=
  multipliableLocallyUniformlyOn_one_sub_pow.hasProdLocallyUniformlyOn.differentiableOn
    (.of_forall fun _ ↦ by simpa [Finset.prod_fn] using
      DifferentiableOn.finsetProd (fun _ _ ↦ by fun_prop)) Metric.isOpen_ball

/-- For any `k`, the function `q ↦ ∏' n, (1 - q^(n+1))^k` is differentiable on the
open unit disc. -/
lemma differentiableOn_tprod_one_sub_pow_pow (k : ℕ) :
    DifferentiableOn ℂ (fun q ↦ ∏' n, (1 - q ^ (n + 1)) ^ k) (Metric.ball (0 : ℂ) 1) :=
  (differentiableOn_tprod_one_sub_pow.fun_pow k).congr fun _ hq ↦
    (multipliable_one_sub_pow (by simpa using hq)).tprod_pow k

theorem summable_eta_q (z : ℍ) : Summable fun n ↦ ‖-eta_q n z‖ := by
  have hq := Periodic.norm_qParam_lt_one (h := 1) one_pos z.2
  simpa only [eta_q, norm_neg, norm_pow] using
    (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (norm_nonneg _) hq)

lemma multipliableLocallyUniformlyOn_eta :
    MultipliableLocallyUniformlyOn (fun n a ↦ 1 - eta_q n a) ℍₒ :=
  multipliableLocallyUniformlyOn_one_sub_pow.comp (fun z ↦ Periodic.qParam 1 z one_ne_zero)
    (fun z hz ↦ by simpa using Periodic.norm_qParam_lt_one (h := 1) one_pos hz)
    (Periodic.continuous_qParam one_ne_zero).continuousOn

lemma eta_tprod_ne_zero {z : ℂ} (hz : z ∈ ℍₒ) : ∏' n, (1 - eta_q n z) ≠ 0 := by
  refine tprod_one_add_ne_zero_of_summable (f := fun n ↦ -eta_q n z) ?_ ?_
  · exact fun i ↦ by simpa using! one_sub_eta_q_ne_zero i hz
  · simpa [eta_q, ← summable_norm_iff] using! summable_eta_q ⟨z, hz⟩

/-- Eta is non-vanishing on the upper half plane. -/
lemma eta_ne_zero {z : ℂ} (hz : z ∈ ℍₒ) : η z ≠ 0 :=
  mul_ne_zero (Periodic.qParam_ne_zero (h := 24) z (by norm_num)) (eta_tprod_ne_zero hz)

private lemma hasDerivAt_one_sub_cexp (r z : ℂ) :
    HasDerivAt (fun w ↦ 1 - r * cexp w) (-(r * cexp z)) z :=
  ((Complex.hasDerivAt_exp z).const_mul r).const_sub 1

lemma logDeriv_one_sub_cexp (r z : ℂ) {hd : ∃! d, HasDerivAt (fun w ↦ 1 - r * cexp w) d z}
    {hu : IsUnit (1 - r * cexp z)} :
    logDeriv (fun w ↦ 1 - r * cexp w) z id hd hu =
      Checked.div (-(r * cexp z)) (1 - r * cexp z) hu :=
  logDeriv_eq (hasDerivAt_one_sub_cexp r z)

lemma logDeriv_one_sub_mul_cexp_comp (r : ℂ) {g : ℂ → ℂ} {z : ℂ}
    (hg : DifferentiableAt ℂ g z)
    {hd : ∃! d, HasDerivAt ((fun w ↦ 1 - r * cexp w) ∘ g) d z}
    {hu : IsUnit (1 - r * cexp (g z))} :
    logDeriv ((fun w ↦ 1 - r * cexp w) ∘ g) z id hd hu =
      Checked.div (-r * deriv g z * cexp (g z)) (1 - r * cexp (g z)) hu := by
  apply logDeriv_eq
  convert (hasDerivAt_one_sub_cexp r (g z)).comp z hg.hasDerivAt using 1
  ring

/-- The derivative of the `n`-th Euler factor of the eta product. -/
lemma hasDerivAt_one_sub_eta_q (n : ℕ) (z : ℂ) :
    HasDerivAt (fun w ↦ 1 - eta_q n w) (-(2 * π * I) * ((n + 1) * eta_q n z)) z := by
  let c : ℂ := 2 * π * I * (n + 1)
  have h := (hasDerivAt_one_sub_cexp 1 (c * z)).comp z ((hasDerivAt_id z).const_mul c)
  have he : (fun w ↦ 1 - eta_q n w) = (fun w ↦ 1 - 1 * cexp w) ∘ (c * ·) := by
    funext w
    simp [c, eta_q_eq_cexp]
  rw [he, eta_q_eq_cexp]
  convert h using 1
  simp only [c, one_mul, mul_one]
  ring

private theorem one_sub_eta_logDeriv_eq {z : ℂ} (hz : z ∈ ℍₒ) (n : ℕ)
    {hd : ∃! d, HasDerivAt (fun w ↦ 1 - eta_q n w) d z} :
    logDeriv (fun w ↦ 1 - eta_q n w) z id hd (one_sub_eta_q_ne_zero n hz).isUnit =
      -(2 * π * I) * Checked.div ((n + 1) * eta_q n z) (1 - eta_q n z)
        (one_sub_eta_q_ne_zero n hz).isUnit := by
  rw [logDeriv_eq (hasDerivAt_one_sub_eta_q n z), mul_div_assoc₀]

lemma tsum_logDeriv_eta_q (z : ℍ) :
    (∑' n, logDeriv (fun x ↦ 1 - eta_q n x) (z : ℂ) id
      (hasDerivAt_one_sub_eta_q n z).existsUnique_hasDerivAt (one_sub_eta_q_ne_zero n z.2).isUnit) =
      -(2 * π * I) * ∑' n, Checked.div ((n + 1) * eta_q n z) (1 - eta_q n z)
        (one_sub_eta_q_ne_zero n z.2).isUnit := by
  simp only [one_sub_eta_logDeriv_eq z.2, tsum_mul_left]

lemma differentiableAt_eta_tprod {z : ℂ} (hz : z ∈ ℍₒ) :
    DifferentiableAt ℂ (fun x ↦ ∏' n, (1 - eta_q n x)) z := by
  have hq : Periodic.qParam 1 z one_ne_zero ∈ Metric.ball 0 1 := by
    simpa using Periodic.norm_qParam_lt_one (h := 1) one_pos hz
  exact (differentiableOn_tprod_one_sub_pow.differentiableAt
    (Metric.isOpen_ball.mem_nhds hq)).comp z (Periodic.differentiable_qParam one_ne_zero z)

theorem differentiableAt_eta_of_mem_upperHalfPlaneSet {z : ℂ} (hz : z ∈ ℍₒ) :
    DifferentiableAt ℂ eta z :=
  .mul (Periodic.differentiable_qParam (by norm_num : (24 : ℝ) ≠ 0) z)
    (differentiableAt_eta_tprod hz)

lemma logDeriv_qParam (h : ℝ) (hh : h ≠ 0) (z : ℂ) :
    logDeriv (fun w ↦ Periodic.qParam h w hh) z id
      (Periodic.hasStrictDerivAt_qParam hh z).hasDerivAt.existsUnique_hasDerivAt
      (Periodic.qParam_ne_zero z hh).isUnit =
      Checked.div (2 * π * I) (h : ℂ) (ofReal_ne_zero.mpr hh).isUnit := by
  rw [logDeriv_eq (Periodic.hasStrictDerivAt_qParam hh z).hasDerivAt,
    mul_comm, mul_div_cancel_right₀]

lemma summable_logDeriv_one_sub_eta_q {z : ℂ} (hz : z ∈ ℍₒ) :
    Summable fun n ↦ logDeriv (fun x ↦ 1 - eta_q n x) z id
      (hasDerivAt_one_sub_eta_q n z).existsUnique_hasDerivAt
      (one_sub_eta_q_ne_zero n hz).isUnit := by
  have hq := norm_exp_two_pi_I_lt_one ⟨z, hz⟩
  have hs := summable_norm_pow_mul_geometric_div_one_sub 1 hq
  refine (((Equiv.pnatEquivNat.symm.summable_iff).mpr hs).mul_left (-(2 * π * I))).congr ?_
  intro n
  refine Eq.trans ?_ (one_sub_eta_logDeriv_eq hz n).symm
  simp only [Function.comp_def, Equiv.pnatEquivNat_symm_apply,
    Nat.succPNat_coe, Nat.cast_succ, pow_one, eta_q_eq_pow]

open EisensteinSeries in
lemma logDeriv_eta_eq_E2 (z : ℍ) :
    logDeriv eta (z : ℂ) id
      (differentiableAt_eta_of_mem_upperHalfPlaneSet z.2).existsUnique_hasDerivAt
      (eta_ne_zero z.2).isUnit = (π * I / 12) * E2 z := by
  have h24 : (24 : ℝ) ≠ 0 := by norm_num
  have hq := Periodic.hasStrictDerivAt_qParam h24 (z : ℂ)
  have hp := differentiableAt_eta_tprod z.2
  have hmul := logDeriv_fun_mul (z : ℂ) (hf := (Periodic.qParam_ne_zero z h24).isUnit)
    (hg := (eta_tprod_ne_zero z.2).isUnit) hq.hasDerivAt.differentiableAt hp
  have hprod := logDeriv_tprod_eq_tsum isOpen_upperHalfPlaneSet z.2
    (fun i ↦ one_sub_eta_q_ne_zero i z.2)
    (fun i x _ ↦ (hasDerivAt_one_sub_eta_q i x).differentiableAt.differentiableWithinAt)
    (summable_logDeriv_one_sub_eta_q z.2) multipliableLocallyUniformlyOn_eta
    (hnez := (eta_tprod_ne_zero z.2).isUnit) (hderiv := hp.existsUnique_hasDerivAt)
  have hsum :
      (∑' n : ℕ, Checked.div ((n + 1) * eta_q n z) (1 - eta_q n z)
        (one_sub_eta_q_ne_zero n z.2).isUnit) =
      ∑' n : ℕ+, σ 1 n * cexp (2 * π * I * z) ^ (n : ℕ) := by
    have hqnorm := norm_exp_two_pi_I_lt_one z
    let f (n : ℕ+) := Checked.div ((n : ℂ) * cexp (2 * π * I * z) ^ (n : ℕ))
      (1 - cexp (2 * π * I * z) ^ (n : ℕ))
      (one_sub_pow_pnat_ne_zero_of_norm_lt_one hqnorm n).isUnit
    calc
      _ = ∑' n : ℕ, f (Equiv.pnatEquivNat.symm n) := by
        apply tsum_congr
        intro n
        simp only [f, Equiv.pnatEquivNat_symm_apply, Nat.succPNat_coe,
          Nat.cast_succ, eta_q_eq_pow]
      _ = ∑' n : ℕ+, f n := Equiv.pnatEquivNat.symm.tsum_eq f
      _ = _ := by simpa only [f, pow_one] using tsum_pow_div_one_sub_eq_tsum_sigma hqnorm 1
  refine hmul.trans ?_
  refine (congrArg₂ (· + ·) (logDeriv_qParam 24 h24 (z : ℂ))
    (hprod.trans (tsum_logDeriv_eta_q z))).trans ?_
  rw [hsum, E2_eq_tsum_cexp]
  generalize (∑' n : ℕ+, σ 1 n * cexp (2 * π * I * z) ^ (n : ℕ)) = S
  norm_num
  ring

end ModularForm
