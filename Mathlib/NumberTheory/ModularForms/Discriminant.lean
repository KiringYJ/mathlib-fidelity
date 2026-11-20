/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Complex.SqrtDeriv
public import Mathlib.Analysis.Normed.Ring.InfiniteProd
public import Mathlib.NumberTheory.ModularForms.DedekindEta
public import Mathlib.NumberTheory.ModularForms.Basic
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Transform
public import Mathlib.NumberTheory.ModularForms.LevelOne.Basic
public import Mathlib.NumberTheory.ModularForms.QExpansion

/-!
# The modular discriminant Δ

This file defines the modular discriminant `Δ(z) = η(z) ^ 24`, where `η` is the Dedekind eta
function, and proves its key properties including invariance under the generators of `SL(2, ℤ)`.

## Main definitions

* `ModularForm.discriminant`: The modular discriminant function `Δ(z) = η(z) ^ 24`, which can also
  be expressed as `q * ∏' (1 - q ^ (n + 1)) ^ 24` where `q = e ^ (2πiz)`.

## Main results

* `ModularForm.discriminant_ne_zero`: The discriminant is non-vanishing on the upper half-plane.
* `ModularForm.discriminant_T_invariant`: Invariance under the translation `T : z ↦ z + 1`.
* `ModularForm.discriminant_S_invariant`: Invariance under the inversion `S : z ↦ -1 / z`,
  showing `Δ(-1 / z) = z ^ 12 · Δ(z)`.

## References

* [F. Diamond and J. Shurman, *A First Course in Modular Forms*][diamondshurman2005], section 1.2
-/

open Function Complex SlashInvariantForm Filter

open scoped MatrixGroups

open UpperHalfPlane hiding I

open scoped Real Topology

noncomputable section

namespace ModularForm

/-- The modular discriminant `Δ(z) = η(z) ^ 24`, where `η` is the Dedekind eta function. -/
@[expose] public def discriminant (z : ℍ) := (eta z) ^ 24

local notation "Δ" => discriminant


section auxiliary

lemma csqrt_pow_24_eq {z : ℂ} (hz : z ≠ 0) : sqrt z ^ 24 = z ^ 12 := by
  rw [sqrt_eq_exp hz, ← exp_nat_mul]
  ring_nf
  rw [show (log z * 12) = (12 : ℕ) * log z by ring, exp_nat_mul, exp_log hz]

lemma csqrt_I_pow_24 : sqrt I ^ 24 = 1 := by
  rw [csqrt_pow_24_eq I_ne_zero, show 12 = 4 * 3 by lia, pow_mul, I_pow_four, one_pow]

private def etaS (z : ℍ) : ℂ := η ((ModularGroup.S • z : ℍ) : ℂ)

private lemma etaS_ne_zero (z : ℍ) : etaS z ≠ 0 := eta_ne_zero (ModularGroup.S • z).2

private def sqrtMulEta (z : ℍ) : ℂ := sqrt z * η z

private lemma hasDerivAt_coe (z : ℍ) :
    HasDerivAt ((↑) : ℍ → ℂ) (1 : ℂ) z ((↑) : ℍ → ℂ) := by
  have h := (hasDerivAt_id (z : ℂ)).hasFDerivAt.comp_tendsto ((↑) : ℍ → ℂ)
    (continuous_coe.continuousAt.tendsto.prodMap (tendsto_pure_pure ..))
  simpa only [Function.id_comp, ContinuousLinearMap.toSpanSingleton_apply, one_smul]
    using! hasFDerivAt_iff_hasDerivAt.mp h

private lemma hasDerivAt_coe_S (z : ℍ) :
    HasDerivAt (fun w : ℍ ↦ (↑(ModularGroup.S • w) : ℂ))
      (Checked.inv ((z : ℂ) ^ 2) (z.ne_zero.isUnit.pow 2)) z ((↑) : ℍ → ℂ) := by
  let g : GL (Fin 2) ℝ := ModularGroup.S
  have hdet : g.val.det = 1 :=
    (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) ModularGroup.S).property
  have hg : 0 < g.val.det := hdet ▸ one_pos
  have h := (hasStrictDerivAt_smul hg z).hasDerivAt.comp z (hasDerivAt_coe z)
    continuous_coe.continuousAt
  simpa only [Function.comp_def, ofComplex_apply, mul_one, hdet, Complex.ofReal_one, g,
    ModularGroup.denom_S, one_div₀] using! h

private lemma hasDerivAt_etaS (z : ℍ) :
    HasDerivAt etaS
      (deriv η (↑(ModularGroup.S • z) : ℂ) *
        Checked.inv ((z : ℂ) ^ 2) (z.ne_zero.isUnit.pow 2)) z ((↑) : ℍ → ℂ) :=
  (differentiableAt_eta_of_mem_upperHalfPlaneSet (ModularGroup.S • z).2).hasDerivAt.comp
    (coord' := id) (h := fun w : ℍ ↦ (↑(ModularGroup.S • w) : ℂ)) z
    (hasDerivAt_coe_S z) continuous_coe.continuousAt

private lemma csqrt_sq_eq (z : ℂ) : sqrt z ^ 2 = z := by
  by_cases hz : z = 0
  · simp [hz]
  rw [sqrt_eq_exp hz, ← exp_nat_mul, show (2 : ℕ) * (log z / 2) = log z by
    push_cast
    field_simp, exp_log hz]

private lemma csqrt_ne_zero (z : ℍ) : sqrt z ≠ 0 := by
  intro h
  exact z.ne_zero (by simpa only [h, zero_pow (by decide : 2 ≠ 0)] using (csqrt_sq_eq z).symm)

private lemma sqrtMulEta_ne_zero (z : ℍ) : sqrtMulEta z ≠ 0 :=
  mul_ne_zero (csqrt_ne_zero z) (eta_ne_zero z.2)

private lemma hasDerivAt_sqrtMulEta (z : ℍ) :
    HasDerivAt sqrtMulEta (deriv sqrt (z : ℂ) * η z + sqrt z * deriv η (z : ℂ)) z
      ((↑) : ℍ → ℂ) := by
  have h := ((differentiableAt_sqrt (mem_slitPlane z)).hasDerivAt.mul
    (differentiableAt_eta_of_mem_upperHalfPlaneSet z.2).hasDerivAt).comp z
      (hasDerivAt_coe z) continuous_coe.continuousAt
  simpa only [sqrtMulEta, Function.comp_def, Pi.mul_apply, mul_one] using! h

lemma logDeriv_eta_comp_div_eq (z : ℍ) :
    logDeriv etaS z ((↑) : ℍ → ℂ)
      ((hasDerivAt_etaS z).existsUnique_hasDerivAt isOpenEmbedding_coe)
      (etaS_ne_zero z).isUnit =
      Checked.inv ((z : ℂ) ^ 2) (z.ne_zero.isUnit.pow 2) *
        logDeriv η (↑(ModularGroup.S • z) : ℂ) id
          (differentiableAt_eta_of_mem_upperHalfPlaneSet
            (ModularGroup.S • z).2).existsUnique_hasDerivAt
          (eta_ne_zero (ModularGroup.S • z).2).isUnit := by
  rw [logDeriv_eq (hasDerivAt_etaS z), logDeriv_apply]
  simp only [etaS, div_eq_mul_inv₀]
  ring

private lemma logDeriv_sqrt_eq (z : ℍ) :
    logDeriv sqrt (z : ℂ) id (differentiableAt_sqrt (mem_slitPlane z)).existsUnique_hasDerivAt
      (csqrt_ne_zero z).isUnit = Checked.div 1 (2 * (z : ℂ))
        ((by norm_num : (2 : ℂ) ≠ 0).isUnit.mul z.ne_zero.isUnit) := by
  have h := ((differentiableAt_sqrt (mem_slitPlane z)).hasDerivAt.pow 2)
  have he : sqrt ^ 2 = id := funext csqrt_sq_eq
  rw [he] at h
  have hd : 2 * sqrt z * deriv sqrt (z : ℂ) = 1 := by
    simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one] using h.deriv.symm.trans
      (hasDerivAt_id (z : ℂ)).deriv
  rw [logDeriv_apply]
  apply div_eq_div_iff.mpr
  rw [show 2 * (z : ℂ) = 2 * sqrt z ^ 2 by rw [csqrt_sq_eq]]
  linear_combination sqrt z * hd

private lemma logDeriv_sqrtMulEta_eq (z : ℍ) :
    logDeriv sqrtMulEta z ((↑) : ℍ → ℂ)
      ((hasDerivAt_sqrtMulEta z).existsUnique_hasDerivAt isOpenEmbedding_coe)
      (sqrtMulEta_ne_zero z).isUnit =
      Checked.div 1 (2 * (z : ℂ))
        ((by norm_num : (2 : ℂ) ≠ 0).isUnit.mul z.ne_zero.isUnit) +
      (π * I / 12) * EisensteinSeries.E2 z := by
  have hs := differentiableAt_sqrt (mem_slitPlane z)
  have hη := differentiableAt_eta_of_mem_upperHalfPlaneSet z.2
  have h := logDeriv_mul (z : ℂ) (hf := (csqrt_ne_zero z).isUnit)
    (hg := (eta_ne_zero z.2).isUnit) hs hη
  calc
    _ = logDeriv (sqrt * η) (z : ℂ) id (hs.hasDerivAt.mul hη.hasDerivAt).existsUnique_hasDerivAt
          ((csqrt_ne_zero z).isUnit.mul (eta_ne_zero z.2).isUnit) :=
      (logDeriv_eq (hasDerivAt_sqrtMulEta z)).trans
        (logDeriv_eq (hs.hasDerivAt.mul hη.hasDerivAt)).symm
    _ = _ := h.trans (congrArg₂ (· + ·) (logDeriv_sqrt_eq z) (logDeriv_eta_eq_E2 z))

open EisensteinSeries in
lemma logDeriv_eta_comp_eq_logDeriv_csqrt_eta (z : ℍ) :
    logDeriv etaS z ((↑) : ℍ → ℂ)
      ((hasDerivAt_etaS z).existsUnique_hasDerivAt isOpenEmbedding_coe)
      (etaS_ne_zero z).isUnit =
    logDeriv sqrtMulEta z ((↑) : ℍ → ℂ)
      ((hasDerivAt_sqrtMulEta z).existsUnique_hasDerivAt isOpenEmbedding_coe)
      (sqrtMulEta_ne_zero z).isUnit := by
  have hζ := isUnit_two_mul_riemannZeta_two
  have hz := z.ne_zero.isUnit
  have hE2 : E2 (ModularGroup.S • z) * ((z : ℂ) ^ 2)⁻¹ =
      E2 z - (1 / (2 * riemannZeta 2)) * (2 * π * I / (z : ℂ)) := by
    simpa only [SL_slash_apply, ModularGroup.denom_S, Int.reduceNeg, zpow_neg₀ z.ne_zero,
      zpow_ofNat₀, D2_S, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using
      congrFun (E2_slash_action ModularGroup.S) z
  have hp : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have htwo : IsUnit (2 * (z : ℂ)) := (by norm_num : (2 : ℂ) ≠ 0).isUnit.mul hz
  have hcor : (π * I / 12) * ((1 / (2 * riemannZeta 2)) * (2 * π * I / (z : ℂ))) =
      -Checked.div 1 (2 * (z : ℂ)) htwo := by
    simp only [riemannZeta_two]
    field_simp
    ring_nf
    simp [I_sq]
  rw [logDeriv_eta_comp_div_eq, logDeriv_eta_eq_E2, logDeriv_sqrtMulEta_eq]
  calc
    _ = (π * I / 12) * (E2 (ModularGroup.S • z) * ((z : ℂ) ^ 2)⁻¹) := by ac_rfl
    _ = _ := by rw [hE2, mul_sub, hcor, sub_neg_eq_add, add_comm]

private lemma eta_comp_eq_const_mul_csqrt_eta :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ z : ℍ, etaS z = c * sqrtMulEta z := by
  let q (z : ℍ) : ℂ := Checked.div (etaS z) (sqrtMulEta z) (sqrtMulEta_ne_zero z).isUnit
  let u (z : ℍ) : ℂˣ := (sqrtMulEta_ne_zero z).isUnit.unit
  have hu : ((↑) : ℂˣ → ℂ) ∘ u = sqrtMulEta :=
    funext fun z ↦ (sqrtMulEta_ne_zero z).isUnit.unit_spec
  have hq (z : ℍ) : HasDerivAt q 0 z ((↑) : ℍ → ℂ) := by
    let a := deriv η (↑(ModularGroup.S • z) : ℂ) *
      Checked.inv ((z : ℂ) ^ 2) (z.ne_zero.isUnit.pow 2)
    let b := deriv sqrt (z : ℂ) * η z + sqrt z * deriv η (z : ℂ)
    have ha : HasDerivAt etaS a z ((↑) : ℍ → ℂ) := hasDerivAt_etaS z
    have hb : HasDerivAt sqrtMulEta b z ((↑) : ℍ → ℂ) := hasDerivAt_sqrtMulEta z
    have hbu : HasDerivAt (((↑) : ℂˣ → ℂ) ∘ u) b z ((↑) : ℍ → ℂ) := hu.symm ▸ hb
    have hi := (hasDerivAt_inv (u z)).comp z hbu continuous_coe.continuousAt
      Units.isOpenEmbedding_val.isEmbedding
    have h := ha.mul hi continuous_coe.continuousAt
    have hLog := logDeriv_eta_comp_eq_logDeriv_csqrt_eta z
    rw [logDeriv_eq ha, logDeriv_eq hb] at hLog
    have hcross : a * sqrtMulEta z = etaS z * b :=
      (div_eq_div_iff.mp hLog).trans (mul_comm _ _)
    have hu₀ : IsUnit (sqrtMulEta z) := (sqrtMulEta_ne_zero z).isUnit
    have hzero : a * (↑(u z)⁻¹ : ℂ) + etaS z * (-(↑(u z)⁻¹ : ℂ) ^ 2 * b) = 0 := by
      change a * (sqrtMulEta z)⁻¹ + etaS z * (-(sqrtMulEta z)⁻¹ ^ 2 * b) = 0
      calc
        _ = (a * sqrtMulEta z - etaS z * b) * (sqrtMulEta z)⁻¹ ^ 2 := by
          field_simp
          ring
        _ = _ := by rw [hcross, sub_self, zero_mul]
    exact hzero ▸ h
  have hconn : IsPreconnected (Set.univ : Set ℍ) := by
    apply isOpenEmbedding_coe.isEmbedding.isInducing.isPreconnected_image.mp
    simpa only [Set.image_univ, range_coe] using (convex_halfSpace_im_gt (0 : ℝ)).isPreconnected
  obtain ⟨c, hc⟩ := isOpen_univ.exists_is_const_of_deriv_eq_zero hconn
    (fun z _ ↦ (hq z).hasFDerivAt.hasFDerivWithinAt.differentiableWithinAt)
    (fun z _ ↦ (hq z).deriv isOpenEmbedding_coe) isOpenEmbedding_coe
  let i : ℍ := ⟨I, by simp⟩
  have hi : IsUnit (q i) :=
    (eta_ne_zero (ModularGroup.S • i).2).isUnit.div₀ (sqrtMulEta_ne_zero i).isUnit
  refine ⟨c, hc i (Set.mem_univ _) ▸ hi.ne_zero, fun z ↦ ?_⟩
  exact div_eq_iff.mp (hc z (Set.mem_univ _))

end auxiliary

public section

/-- The discriminant expressed as a q-expansion: `Δ(z) = q * ∏' (1 - q ^ (n + 1)) ^ 24`. -/
lemma discriminant_eq_q_prod (z : ℍ) :
    Δ z = Function.Periodic.qParam 1 z * ∏' n, (1 - eta_q n z) ^ 24 := by
  simp only [discriminant, eta, mul_pow]
  congr
  · simp [Periodic.qParam, ← exp_nsmul, nsmul_eq_mul, Nat.cast_ofNat]
    congr 1
    field_simp
  · exact ((multipliableLocallyUniformlyOn_eta.multipliable z.2).tprod_pow _).symm

/-- The modular discriminant is non-vanishing on the upper half-plane. -/
lemma discriminant_ne_zero (z : ℍ) : Δ z ≠ 0 := by
  simpa [discriminant] using eta_ne_zero z.2

set_option backward.isDefEq.respectTransparency.types false in
/-- The discriminant is invariant under `T : z ↦ z + 1`, i.e., `Δ(z + 1) = Δ(z)`. -/
lemma discriminant_T_invariant : (Δ ∣[(12 : ℤ)] ModularGroup.T) = Δ := by
  ext z
  rw [SL_slash_apply, modular_T_smul]
  simp only [ModularGroup.denom_apply, ModularGroup.T]
  simp [discriminant_eq_q_prod, eta_q, Periodic.qParam, ← exp_periodic (2 * π * I * z)]
  ring_nf

/-- The transformation formula for `η` under `S : z ↦ -1 / z`: we have
`η(-1 / z) = (√I)⁻¹ · √z · η(z)` on the upper half-plane. -/
lemma eta_comp_eq_csqrt_I_inv (z : ℍ) : η ((ModularGroup.S • z : ℍ) : ℂ) =
    Checked.inv (sqrt I) (by rw [sqrt_eq_exp I_ne_zero]; exact (exp_ne_zero _).isUnit) *
      (sqrt z * η z) := by
  obtain ⟨c, _, hc⟩ := eta_comp_eq_const_mul_csqrt_eta
  let i : ℍ := ⟨I, by simp⟩
  have hi : ModularGroup.S • i = i := by
    rw [modular_S_smul i]
    apply UpperHalfPlane.ext
    simp [i, inv_neg₀, inv_I]
  have hci : c * sqrt I = 1 := by
    apply mul_right_cancel₀ (eta_ne_zero i.2)
    simpa only [etaS, sqrtMulEta, hi, i, mul_assoc, one_mul] using (hc i).symm
  have hc' : c = Checked.inv (sqrt I) (csqrt_ne_zero i).isUnit :=
    (inv_eq_of_mul_eq_one_left₀ hci).symm
  exact (hc z).trans (congrArg (· * sqrtMulEta z) hc')

set_option backward.isDefEq.respectTransparency.types false in
/-- The discriminant satisfies the modular transformation for `S : z ↦ -1 / z`:
we have `Δ(-1 / z) = z ^ 12 · Δ(z)`. -/
lemma discriminant_S_invariant : (Δ ∣[(12 : ℤ)] ModularGroup.S) = Δ := by
  ext z
  simp only [SL_slash_apply, ModularGroup.denom_S, zpow_neg₀ z.ne_zero, zpow_ofNat₀]
  simp only [discriminant, eta_comp_eq_csqrt_I_inv z, mul_pow, inv_pow₀, csqrt_I_pow_24,
    inv_one₀, one_mul, csqrt_pow_24_eq z.ne_zero]
  rw [mul_comm ((z : ℂ) ^ 12), mul_assoc, mul_inv_cancel₀, mul_one]

lemma tendsto_atImInfty_tprod_one_sub_eta_q_pow :
    Tendsto (fun x : ℍ ↦ ∏' (n : ℕ), (1 - eta_q n x) ^ 24) atImInfty (𝓝 1) := by
  have htprod : Tendsto (fun q : ℂ ↦ ∏' (n : ℕ), (1 - q ^ (n + 1))) (𝓝 0) (𝓝 1) := by
    have := tendsto_tprod_one_add_of_dominated_convergence (𝓕 := 𝓝 0) (g := 0)
      (f := fun (q : ℂ) (n : ℕ) ↦ -q ^ (n + 1)) (bound := fun n ↦ (1 / 2 : ℝ) ^ (n + 1))
    simp only [Pi.zero_apply, norm_neg, norm_pow, add_zero, tprod_one] at this
    simp_rw [sub_eq_add_neg]
    refine this
      (by simpa only [pow_succ'] using (summable_geometric_of_abs_lt_one (by norm_num)).mul_left _)
      (fun k ↦ by simpa using ((continuous_pow (M := ℂ) (k + 1)).tendsto 0).neg) ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2)] with q hq k
    exact pow_le_pow_left₀ (norm_nonneg _) (mem_ball_zero_iff.mp hq).le _
  have := (htprod.comp (UpperHalfPlane.qParam_tendsto_atImInfty zero_lt_one)).pow 24
  simp only [Periodic.qParam, ofReal_one, comp_apply, one_pow, eta_q] at *
  convert! this using 2 with τ
  rw [Multipliable.tprod_pow]
  apply (multipliableLocallyUniformlyOn_eta.multipliable τ.2).congr
  simp [eta_q, Periodic.qParam, ← exp_nat_mul]

@[deprecated (since := "2026-04-30")]
alias discriminant_bounded_factor := tendsto_atImInfty_tprod_one_sub_eta_q_pow

lemma discriminant_isZeroAtImInfty : IsZeroAtImInfty Δ := by
  apply Tendsto.congr (fun z ↦ (discriminant_eq_q_prod z).symm)
  rw [show (0 : ℂ) = 0 * 1 by ring]
  exact (qParam_tendsto_atImInfty zero_lt_one).mul
    (tendsto_atImInfty_tprod_one_sub_eta_q_pow.congr fun z ↦ by congr 1)

lemma exp_isBigO_discriminant : (fun τ ↦ Real.exp (-2 * π * τ.im)) =O[atImInfty] Δ := by
  refine .of_bound 2 ?_
  have hprod := tendsto_atImInfty_tprod_one_sub_eta_q_pow.eventually
    (Metric.ball_mem_nhds 1 (by norm_num : (0 : ℝ) < 1/2))
  filter_upwards [hprod] with τ hτ
  rw [discriminant_eq_q_prod, norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
  have hq_norm : ‖Function.Periodic.qParam 1 τ‖ = Real.exp (-2 * π * τ.im) := by
    simp [Periodic.qParam, Complex.norm_exp]
  rw [← hq_norm]
  have hprod_bound : 1 / 2 ≤ ‖∏' n, (1 - eta_q n τ) ^ 24‖ := by
    have hsub : ‖∏' n, (1 - eta_q n τ) ^ 24 - 1‖ < 1 / 2 := by rwa [Complex.dist_eq] at hτ
    have h1 := norm_sub_norm_le 1 (∏' n, (1 - eta_q n τ) ^ 24)
    rw [norm_one, norm_sub_rev] at h1
    linarith
  linarith [norm_nonneg (Function.Periodic.qParam 1 τ),
    mul_le_mul_of_nonneg_left hprod_bound (norm_nonneg (Function.Periodic.qParam 1 τ))]

/-- The cusp function of the discriminant equals `q * ∏' n, (1 - q^(n+1))^24`
on the open unit disc. -/
lemma discriminant_cuspFunction_eqOn : Set.EqOn (cuspFunction 1 Δ)
    (fun q ↦ q * ∏' i, (1 - q ^ (i + 1)) ^ 24) (Metric.ball 0 1) := by
  intro q hq
  by_cases hq0 : q = 0
  · simpa [hq0] using! Periodic.cuspFunction_zero_of_zero_at_inf one_pos
      discriminant_isZeroAtImInfty.zero_at_infty_comp_ofComplex
  · have him := Periodic.im_invQParam_pos_of_norm_lt_one one_pos
      (by simpa [dist_zero_right] using hq) hq0
    simp [cuspFunction, Periodic.cuspFunction_eq_of_nonzero 1 _ one_ne_zero hq0,
      ofComplex_apply_of_im_pos him, discriminant_eq_q_prod ⟨_, him⟩,
      Periodic.qParam_right_inv one_ne_zero hq0, eta_q]

/-- The first q-expansion coefficient of the modular discriminant is 1. -/
lemma discriminant_qExpansion_coeff_one : (qExpansion 1 Δ).coeff 1 = 1 := by
  have hmem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := Metric.mem_ball_self one_pos
  calc (qExpansion 1 Δ).coeff 1
      = derivWithin (cuspFunction 1 Δ) (Metric.ball 0 1) 0 := by
        simp [qExpansion_coeff, ← derivWithin_of_isOpen Metric.isOpen_ball hmem]
    _ = derivWithin (fun q ↦ q * ∏' i, (1 - q ^ (i + 1)) ^ 24) (Metric.ball 0 1) 0 :=
        derivWithin_congr discriminant_cuspFunction_eqOn (discriminant_cuspFunction_eqOn hmem)
    _ = 1 := by
        simp [derivWithin_fun_mul differentiableWithinAt_fun_id
          (differentiableOn_tprod_one_sub_pow_pow 24 _ hmem),
          derivWithin_id' _ _ (Metric.isOpen_ball.uniqueDiffWithinAt hmem)]

end

end ModularForm

public section

namespace CuspForm

open ModularForm

local notation "Δ" => ModularForm.discriminant

/-- The modular discriminant `Δ` as a cusp form of weight 12 and level 1. -/
@[expose] def discriminant : CuspForm 𝒮ℒ 12 where
  toFun := Δ
  slash_action_eq' A hA := by
    obtain ⟨A, rfl⟩ := hA
    exact slash_action_generators_SL2Z discriminant_S_invariant discriminant_T_invariant A
  holo' := by
    rw [UpperHalfPlane.mdifferentiable_iff]
    refine .congr (fun z hz ↦ (differentiableAt_eta_of_mem_upperHalfPlaneSet hz).pow
      24 |>.differentiableWithinAt) fun z hz ↦ ?_
    simp [ModularForm.discriminant, ofComplex_apply_of_im_pos hz]
  zero_at_cusps' hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
    intro γ _
    rw [slash_action_generators_SL2Z discriminant_S_invariant discriminant_T_invariant]
    exact discriminant_isZeroAtImInfty

@[simp]
lemma coe_discriminant : discriminant = Δ := rfl

variable {k : ℤ}

/-- Any cusp form for `𝒮ℒ` is `O(Δ)` at the cusp `i∞`. -/
lemma exp_decay_isBigO_discriminant (f : CuspForm 𝒮ℒ k) :
    f =O[atImInfty] ModularForm.discriminant :=
  (CuspFormClass.exp_decay_atImInfty (h := 1) f one_pos one_mem_strictPeriods_SL).trans
    (by simpa using exp_isBigO_discriminant)

end CuspForm

@[deprecated CuspForm.discriminant (since := "2026-04-30")]
alias ModularForm.discriminantCuspForm := CuspForm.discriminant

end
