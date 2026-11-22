/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.NumberTheory.ModularForms.Bounds
public import Mathlib.NumberTheory.LSeries.AbstractFuncEq
public import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
public import Mathlib.Analysis.PSeries

/-!
# The `L`-function of a modular form
-/

@[expose] public section

open UpperHalfPlane hiding I
open scoped Real
open Filter Complex Asymptotics

variable {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
  {k : ℤ} (hk : 0 < k) {F : Type*} [FunLike F ℍ ℂ] (f : F) {s : ℂ}

local notation "cuspWidth" => Subgroup.strictWidthInfty

open ConjAct Pointwise in
private local instance :
    Subgroup.IsArithmetic (toConjAct (ModularGroup.S : GL (Fin 2) ℝ)⁻¹ • Γ) := by
  convert Subgroup.IsArithmetic.conj Γ ↑(ModularGroup.S⁻¹)
  simp only [ModularGroup.S_inv, ← map_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ModularGroup.S]

namespace ModularForm

variable [ModularFormClass F Γ k]

section asymptotics -- private lemmas about aymptotics along `I * ℝ`

private lemma tendsto_ofComplex_I_mul_atTop_atImInfty :
    Tendsto (fun t : ℝ ↦ ofComplex (I * t)) atTop atImInfty := by
  rw [atImInfty, tendsto_comap_iff]
  refine tendsto_id.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  simp [ofComplex_apply_of_im_pos, ht, ← coe_im]

include F k Γ in -- conclusion doesn't explicitly refer these
private lemma isBigO_comp_ofComplex_I_mul_sub_valueAtInfty (r : ℝ) :
    (fun t : ℝ ↦ f (ofComplex (I * t)) - valueAtInfty f) =O[atTop] (fun t ↦ t ^ r) := by
  obtain ⟨C, hCpos, hCO⟩ := ModularFormClass.exp_decay_sub_atImInfty' f
  refine (hCO.comp_tendsto tendsto_ofComplex_I_mul_atTop_atImInfty).trans ?_
  refine (EventuallyEq.isBigO ?_).trans (isLittleO_exp_neg_mul_rpow_atTop hCpos r).isBigO
  filter_upwards [eventually_gt_atTop 0] with t ht
  simp [ht, ofComplex_apply_of_im_pos, ← coe_im]

end asymptotics

/-- A `WeakFEPair` structure associated to a modular form. -/
@[simps] noncomputable def weakFEPair : WeakFEPair ℂ where
  f t := f (ofComplex (I * t))
  g t := translate f ModularGroup.S (ofComplex (I * t))
  k := k
  hk := mod_cast hk
  ε := I ^ k
  hε := zpow_ne_zero _ I_ne_zero
  f₀ := valueAtInfty f
  g₀ := valueAtInfty (translate f ModularGroup.S)
  hf_int := ContinuousOn.locallyIntegrableOn (by fun_prop) measurableSet_Ioi
  hg_int := ContinuousOn.locallyIntegrableOn (by fun_prop) measurableSet_Ioi
  h_feq t (ht : 0 < t) := by
    let τ := ofComplex (I * (t : ℂ))
    have hτ : (τ : ℂ) = I * (t : ℂ) := by simp [τ, ofComplex_apply_of_im_pos, ht, coe_mk]
    have ht' : 0 < (1 : ℝ) / t := one_div_pos.mpr ht
    have hu : 0 < (I * ((1 / t : ℝ) : ℂ)).im := by simpa only [I_mul_im, ofReal_re] using ht'
    have hR : (ofComplex (I * ((1 / t : ℝ) : ℂ)) : ℂ) = I * ((1 / t : ℝ) : ℂ) := by
      rw [ofComplex_apply_of_im_pos hu, coe_mk]
    have hS : ModularGroup.S • τ = ofComplex (I * ((1 / t : ℝ) : ℂ)) := by
      apply UpperHalfPlane.ext
      simp only [modular_S_smul, coe_mk, hτ, hR]
      simp only [inv_neg₀, mul_inv₀, inv_I, neg_mul, neg_neg, one_div₀, ofReal_inv]
    have hweight : I ^ k * ((t ^ (k : ℝ) : ℝ) : ℂ) = (τ : ℂ) ^ k := by
      simp only [hτ, mul_zpow₀, Real.rpow_intCast (h := fun _ ↦ ht.ne'), ofReal_zpow]
    have hden : (τ : ℂ) ^ k * Checked.zpow (denom ModularGroup.S τ) (-k)
        (fun _ ↦ isUnit_denom (ModularGroup.S : GL (Fin 2) ℝ) τ) = 1 := by
      simp only [ModularGroup.denom_S, zpow_neg₀ τ.ne_zero, mul_inv_cancel₀]
    change f (ofComplex (I * ((1 / t : ℝ) : ℂ))) =
      (I ^ k * ((t ^ (k : ℝ) : ℝ) : ℂ)) • (translate f ModularGroup.S) τ
    rw [coe_translate, ← ModularForm.SL_slash (f : ℍ → ℂ) ModularGroup.S,
      ModularForm.SL_slash_apply,
      smul_eq_mul, hweight, ← mul_assoc, mul_right_comm, hden, one_mul, hS]
  hf_top r := by -- `by exact` to hide use of private lemma in @[expose]'d declaration
    exact isBigO_comp_ofComplex_I_mul_sub_valueAtInfty f r
  hg_top r := by -- `by exact` to hide use of private lemma in @[expose]'d declaration
    exact isBigO_comp_ofComplex_I_mul_sub_valueAtInfty (translate f ModularGroup.S) r

/-- The `L`-series of a modular form (including its Archimedean `Γ`-factor). -/
noncomputable def Λ (s : {s : ℂ // (s ≠ 0 ∨ (weakFEPair hk f).f₀ = 0) ∧
    (s ≠ ((weakFEPair hk f).k : ℂ) ∨ (weakFEPair hk f).ε • (weakFEPair hk f).g₀ = 0)}) : ℂ :=
  (weakFEPair hk f).Λ s

/-- The `L`-series of a modular form with the archimedean factor removed. The reciprocal Gamma
factor cancels the possible pole of the completed series at zero. -/
noncomputable def L (s : {s : ℂ //
    s ≠ ((weakFEPair hk f).k : ℂ) ∨ (weakFEPair hk f).ε • (weakFEPair hk f).g₀ = 0}) : ℂ :=
  let P := weakFEPair hk f
  let γ := 2 * reciprocalGammaℂ s.val
  γ * P.Λ₀ s.val - ((2 * π) ^ s.val * reciprocalGamma (s.val + 1)) * P.f₀ +
    γ * (if hg : P.ε • P.g₀ = 0 then 0 else
      Checked.inv (s.val - P.k) (sub_ne_zero.mpr (s.property.resolve_right hg)).isUnit •
        (P.ε • P.g₀))

/-- The value at zero is the negative of the constant term of the `q`-expansion. -/
lemma L_zero : L hk f ⟨0, Or.inl (by exact_mod_cast (weakFEPair hk f).hk.ne)⟩ =
    -(weakFEPair hk f).f₀ := by
  simp [L, reciprocalGammaℂ]

/-- The frequency in the Mellin transform of the `n`-th term of the `q`-expansion. -/
noncomputable def mellinFrequency (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.IsArithmetic] (n : ℕ) : ℝ :=
  Checked.div (2 * n) (cuspWidth Γ) Γ.strictWidthInfty_pos.ne'.isUnit

@[simp]
lemma mellinFrequency_pos (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.IsArithmetic] (n : ℕ) :
    0 < mellinFrequency Γ n ↔ 0 < n := by
  rw [mellinFrequency, lt_div_iff₀ Γ.strictWidthInfty_pos, zero_mul,
    mul_pos_iff_of_pos_left two_pos, Nat.cast_pos]

/-- A positive Mellin frequency has nonzero complex powers. -/
lemma mellinFrequency_cpow_isUnit (Γ : Subgroup (GL (Fin 2) ℝ)) [Γ.IsArithmetic]
    (n : ℕ+) (s : ℂ) : IsUnit ((mellinFrequency Γ n : ℂ) ^ s) :=
  (cpow_ne_zero_iff.mpr (.inl (ofReal_ne_zero.mpr ((mellinFrequency_pos Γ n).2 n.pos).ne'))).isUnit

/-- To the right of the weight, neither possible pole of the completed function occurs. -/
lemma regular_of_weight_lt_re (hs : (k : ℝ) < s.re) :
    (s ≠ 0 ∨ (weakFEPair hk f).f₀ = 0) ∧
      (s ≠ ((weakFEPair hk f).k : ℂ) ∨ (weakFEPair hk f).ε • (weakFEPair hk f).g₀ = 0) := by
  have hpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hk' : ((weakFEPair hk f).k : ℂ) = k := by simp [weakFEPair]
  rw [hk']
  exact ⟨Or.inl (ne_of_apply_ne Complex.re (by simpa using (hpos.trans hs).ne')),
    Or.inl (ne_of_apply_ne Complex.re (by simpa using hs.ne'))⟩

/-- Shared Dirichlet-series summability argument for modular and cusp forms. -/
private lemma hasSum_Λ_of_qExpansion_isBigO {r : ℝ}
    (hpos : 0 < s.re) (hs : r + 1 < s.re)
    (hsΛ : (s ≠ 0 ∨ (weakFEPair hk f).f₀ = 0) ∧
      (s ≠ ((weakFEPair hk f).k : ℂ) ∨ (weakFEPair hk f).ε • (weakFEPair hk f).g₀ = 0))
    (hΛ : Λ hk f ⟨s, hsΛ⟩ = mellin (fun t : Set.Ioi (0 : ℝ) ↦
      (weakFEPair hk f).f t.val - (weakFEPair hk f).f₀) s)
    (hcoeff : (fun n ↦ (qExpansion (cuspWidth Γ) f Γ.strictWidthInfty_pos.ne').coeff n)
      =O[atTop] fun n ↦ (n : ℝ) ^ r) :
    HasSum (fun n : ℕ+ ↦ Checked.div
      (π ^ (-s) * Gamma s * (qExpansion (cuspWidth Γ) f Γ.strictWidthInfty_pos.ne').coeff n)
      ((mellinFrequency Γ n : ℂ) ^ s) (mellinFrequency_cpow_isUnit Γ n s))
      (Λ hk f ⟨s, hsΛ⟩) := by
  rw [hΛ]
  have hh := Γ.strictWidthInfty_pos
  have hΓ := Γ.strictWidthInfty_mem_strictPeriods
  let p := mellinFrequency Γ
  have hp (n : ℕ) : 0 < p n ↔ 0 < n := mellinFrequency_pos Γ n
  let e : ℕ+ ≃ {n // 0 < p n} := Equiv.subtypeEquiv (Equiv.refl ℕ) (fun n ↦ (hp n).symm)
  let c (n : ℕ) := (qExpansion (cuspWidth Γ) f hh.ne').coeff n
  have hp₀ (n : ℕ) : 0 ≤ p n := by
    dsimp only [p, mellinFrequency]
    positivity
  -- The `q`-expansion converges to `f` on the positive imaginary axis.
  have hseries : ∀ t : Set.Ioi (0 : ℝ),
      HasSum (fun n ↦ if p n = 0 then 0 else c n * rexp (-π * p n * t.val))
        ((weakFEPair hk f).f t.val - (weakFEPair hk f).f₀) := by
    rintro ⟨t, ht⟩
    change 0 < t at ht
    have ht' : 0 < (I * (t : ℂ)).im := by simpa only [I_mul_im, ofReal_re] using ht
    have ht_coe : (ofComplex (I * (t : ℂ)) : ℂ) = I * t := by
      rw [ofComplex_apply_of_im_pos ht', coe_mk]
    have hi : (2 : ℂ) * π * I * (I * t) = -(2 * π * t) := by
      calc
        _ = 2 * π * I ^ 2 * t := by ring
        _ = _ := by rw [I_sq]; ring
    have hq : Function.Periodic.qParam (cuspWidth Γ) (ofComplex (I * t)) hh.ne' =
        cexp (-((2 : ℂ) * π * t) / (cuspWidth Γ : ℂ)) := by
      rw [Function.Periodic.qParam, ht_coe, hi]
    have := hasSum_qExpansion f hh hΓ (ofComplex (I * t))
    convert! hasSum_ite_sub_hasSum this 0 using 2 with n
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [p, mellinFrequency]
      · have hp' := ((hp n).2 hn).ne'
        simp only [ite_eq_right hp', ite_eq_right hn.ne', c, hq, ← exp_nat_mul, ofReal_exp]
        congr 2
        simp only [p, mellinFrequency, ofReal_neg, ofReal_mul, ofReal_ofNat,
          ofReal_natCast, div_eq_mul_inv₀, ofReal_inv]
        ring
    · simp only [weakFEPair]
      rw [qExpansion_coeff_zero hh, pow_zero, mul_one]
      · exact ModularFormClass.analyticAt_cuspFunction_zero f hh hΓ
      · exact SlashInvariantFormClass.periodic_comp_ofComplex f hΓ
  have hsummable : Summable (fun n : {n // 0 < p n} ↦ Checked.div ‖c n‖ (p n ^ s.re)
      (Real.rpow_ne_zero_of_pos n.2 s.re).isUnit) := by
    apply e.summable_iff.mp
    have hp_factor (n : ℕ+) : p n = (n : ℝ) * (2 / cuspWidth Γ) := by
      simp only [p, mellinFrequency, div_eq_mul_inv₀]
      ring
    change Summable fun n : ℕ+ ↦ ‖c n‖ / p n ^ s.re
    let C := ((2 : ℝ) / cuspWidth Γ) ^ s.re
    have hh2 : 0 < (2 : ℝ) / cuspWidth Γ := div_pos two_pos hh
    have hc_unit : IsUnit C := (Real.rpow_ne_zero_of_pos hh2 s.re).isUnit
    have hdiv (n : ℕ+) : ‖c n‖ / p n ^ s.re =
        Checked.div (‖c n‖ / (n : ℝ) ^ s.re) C hc_unit := by
      rw [div_div₀, div_eq_div_iff, hp_factor, Real.mul_rpow (Nat.cast_nonneg _) hh2.le]
    simp_rw [hdiv]
    apply Summable.div_const
    apply Equiv.pnatEquivNat.symm.summable_iff.mp
    change Summable (fun n : ℕ ↦ ‖c (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ s.re)
    apply summable_of_isBigO_nat ((summable_nat_add_iff 1).2
      (Real.summable_nat_rpow.mpr (by linarith : r - s.re < -1)))
    have hc := hcoeff.norm_left.comp_tendsto (tendsto_add_atTop_nat 1)
    have hn (n : ℕ) : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
    simp_rw [Real.rpow_sub (hn _), div_eq_mul_inv₀]
    exact hc.mul (isBigO_refl _ _)
  exact e.hasSum_iff.mpr (hasSum_mellin_pi_mul₀ hp₀ hpos hseries hsummable)

lemma hasSum_Λ (hs : k + 1 < s.re) :
    HasSum (fun n : ℕ+ ↦ Checked.div
      (π ^ (-s) * Gamma s * (qExpansion (cuspWidth Γ) f Γ.strictWidthInfty_pos.ne').coeff n)
      ((mellinFrequency Γ n : ℂ) ^ s) (mellinFrequency_cpow_isUnit Γ n s))
      (Λ hk f ⟨s, regular_of_weight_lt_re hk f (by linarith)⟩) := by
  refine hasSum_Λ_of_qExpansion_isBigO hk f (r := k)
    (by linarith [show (0 : ℝ) < k from mod_cast hk]) hs _ ?_ ?_
  · have hlarge : (weakFEPair hk f).k < s.re := by change (k : ℝ) < s.re; linarith
    exact ((weakFEPair hk f).hasMellin hlarge).2.symm
  · simpa only [Real.rpow_intCast (h := fun hkneg ↦ (not_lt_of_ge hk.le hkneg).elim)] using
      ModularFormClass.qExpansion_isBigO hk.le f

/-- Away from zero, removing the archimedean factor is multiplication by its reciprocal. -/
lemma L_eq_Λ_mul_reciprocalGammaℂ
    (s : {s : ℂ // s ≠ ((weakFEPair hk f).k : ℂ) ∨ (weakFEPair hk f).ε • (weakFEPair hk f).g₀ = 0})
    (hs : s.val ≠ 0) :
    L hk f s = Λ hk f ⟨s.val, Or.inl hs, s.property⟩ * (2 * reciprocalGammaℂ s.val) := by
  have hγ : 2 * reciprocalGammaℂ s.val =
      s.val * ((2 * π) ^ s.val * reciprocalGamma (s.val + 1)) := by
    rw [reciprocalGammaℂ, mul_div_cancel₀, reciprocalGamma_eq_self_mul_reciprocalGamma_add_one]
    ring
  have hcancel : 2 * reciprocalGammaℂ s.val * (Checked.inv s.val hs.isUnit) =
      (2 * π) ^ s.val * reciprocalGamma (s.val + 1) := by
    rw [hγ, mul_right_comm, mul_inv_cancel₀, one_mul]
  by_cases hf : (weakFEPair hk f).f₀ = 0
  · simp only [L, Λ, WeakFEPair.Λ, hf, dite_true, mul_zero, sub_zero]
    ring
  · simp only [L, Λ, WeakFEPair.Λ, dite_eq_right hf, smul_eq_mul]
    linear_combination hcancel * (weakFEPair hk f).f₀

/-- A positive natural number raised to a complex power is a unit. -/
lemma isUnit_pnat_cpow (n : ℕ+) (s : ℂ) : IsUnit (((n : ℕ) : ℂ) ^ s) :=
  (cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr n.ne_zero))).isUnit

/-- Shared conversion from the completed `Λ`-series to the ordinary `L`-series. -/
private lemma hasSum_L_of_hasSum_Λ (hs : 0 < s.re)
    (hsΛ : (s ≠ 0 ∨ (weakFEPair hk f).f₀ = 0) ∧
      (s ≠ ((weakFEPair hk f).k : ℂ) ∨ (weakFEPair hk f).ε • (weakFEPair hk f).g₀ = 0))
    (hΛ : HasSum (fun n : ℕ+ ↦ Checked.div
      (π ^ (-s) * Gamma s * (qExpansion (cuspWidth Γ) f Γ.strictWidthInfty_pos.ne').coeff n)
      ((mellinFrequency Γ n : ℂ) ^ s) (mellinFrequency_cpow_isUnit Γ n s))
      (Λ hk f ⟨s, hsΛ⟩)) :
    HasSum (fun n : ℕ+ ↦ Checked.div
      ((qExpansion (cuspWidth Γ) f Γ.strictWidthInfty_pos.ne').coeff n) (((n : ℕ) : ℂ) ^ s)
      (isUnit_pnat_cpow n s)) ((cuspWidth Γ : ℂ) ^ (-s) * L hk f ⟨s, hsΛ.2⟩) := by
  have hs₀ : s ≠ 0 := ne_of_apply_ne Complex.re (by simpa using hs.ne')
  have hreg (n : ℕ) : s ≠ -n := by
    intro he
    have hre := congrArg Complex.re he
    simp at hre
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hγ : Gamma s * (2 * reciprocalGammaℂ s) = (2 * π : ℂ) ^ s := by
    rw [reciprocalGammaℂ, mul_div_cancel₀, mul_left_comm, mul_comm (Gamma s),
      reciprocalGamma_mul_Gamma hreg, mul_one]
  have hπ : IsUnit ((π : ℂ) ^ s) :=
    (cpow_ne_zero_iff.mpr (.inl (ofReal_ne_zero.mpr Real.pi_ne_zero))).isUnit
  have hwidth : IsUnit ((cuspWidth Γ : ℂ) ^ s) :=
    (cpow_ne_zero_iff.mpr (.inl (ofReal_ne_zero.mpr Γ.strictWidthInfty_pos.ne'))).isUnit
  have h2 : IsUnit ((2 : ℂ) ^ s) := (cpow_ne_zero_iff.mpr (.inl two_ne_zero)).isUnit
  have hπ_mul : (π : ℂ) ^ (-s) * (2 * π : ℂ) ^ s = (2 : ℂ) ^ s := by
    rw [cpow_neg _ _ (hxy := hπ), ← ofReal_ofNat,
      mul_cpow_ofReal_nonneg two_pos.le Real.pi_pos.le, mul_left_comm, inv_mul_cancel₀, mul_one]
  have hsL := L_eq_Λ_mul_reciprocalGammaℂ hk f ⟨s, hsΛ.2⟩ hs₀
  have hright : Λ hk f ⟨s, hsΛ⟩ * (2 * reciprocalGammaℂ s * (cuspWidth Γ : ℂ) ^ (-s)) =
      (cuspWidth Γ : ℂ) ^ (-s) * L hk f ⟨s, hsΛ.2⟩ := by
    rw [hsL]
    ring
  rw [← hright]
  apply (hΛ.mul_right (2 * reciprocalGammaℂ s * (cuspWidth Γ : ℂ) ^ (-s))).congr_fun
  intro n
  have hn := isUnit_pnat_cpow n s
  have hfreq : (mellinFrequency Γ n : ℂ) ^ s =
      (2 : ℂ) ^ s * ((n : ℕ) : ℂ) ^ s / (cuspWidth Γ : ℂ) ^ s := by
    rw [mellinFrequency, ofReal_div,
      div_cpow_ofReal_nonneg (by positivity) Γ.strictWidthInfty_pos.le s
        (hb₀ := Γ.strictWidthInfty_pos.ne'.isUnit),
      ofReal_mul, mul_cpow_ofReal_nonneg zero_le_two (Nat.cast_nonneg _),
      ofReal_ofNat, ofReal_natCast]
  let c := (qExpansion (cuspWidth Γ) f Γ.strictWidthInfty_pos.ne').coeff n
  symm
  calc
    _ = (((π : ℂ) ^ (-s) * (Gamma s * (2 * reciprocalGammaℂ s))) *
        (cuspWidth Γ : ℂ) ^ (-s) * c) / ((mellinFrequency Γ n : ℂ) ^ s) := by
      rw [div_mul_eq_mul_div₀]
      ring
    _ = _ := by
      rw [hγ, hπ_mul, div_eq_div_iff, hfreq, cpow_neg _ _ (hxy := hwidth)]
      field_simp
      rfl

theorem hasSum_L (hs : k + 1 < s.re) :
    HasSum (fun n : ℕ+ ↦ Checked.div
      ((qExpansion (cuspWidth Γ) f Γ.strictWidthInfty_pos.ne').coeff n) (((n : ℕ) : ℂ) ^ s)
      (isUnit_pnat_cpow n s))
      ((cuspWidth Γ : ℂ) ^ (-s) * L hk f ⟨s, (regular_of_weight_lt_re hk f (by linarith)).2⟩) :=
  hasSum_L_of_hasSum_Λ hk f (by linarith [show (0 : ℝ) < k from mod_cast hk]) _ (hasSum_Λ hk f hs)

end ModularForm

open ModularForm

namespace CuspForm

variable [CuspFormClass F Γ k]

/-- For cusp forms the FE-pair is a strong FE-pair. -/
lemma isStrongFEPair : IsStrongFEPair (weakFEPair hk f) where
  hf₀ := (CuspFormClass.zero_at_infty f).valueAtInfty_eq_zero
  hg₀ := (CuspFormClass.zero_at_infty <| translate f ModularGroup.S).valueAtInfty_eq_zero

/-- A cusp form has no residue corrections, so its entire completed series is defined everywhere. -/
lemma regular (s : ℂ) : (s ≠ 0 ∨ (weakFEPair hk f).f₀ = 0) ∧
    (s ≠ ((weakFEPair hk f).k : ℂ) ∨ (weakFEPair hk f).ε • (weakFEPair hk f).g₀ = 0) :=
  ⟨Or.inr (isStrongFEPair hk f).hf₀, Or.inr (by rw [(isStrongFEPair hk f).hg₀, smul_zero])⟩

@[fun_prop]
lemma differentiable_Λ : Differentiable ℂ (fun s ↦ Λ hk f ⟨s, regular hk f s⟩) :=
  (isStrongFEPair hk f).differentiable_Λ

lemma Λ_eq_mellin : (fun s ↦ Λ hk f ⟨s, regular hk f s⟩) =
    mellin (fun t : Set.Ioi (0 : ℝ) ↦ f (ofComplex (I * (t : ℝ)))) := by
  funext s
  exact (isStrongFEPair hk f).Λ_eq ⟨s, regular hk f s⟩

lemma hasSum_Λ (hk : 0 < k) (hs : (k : ℝ) / 2 + 1 < s.re) :
    HasSum (fun n : ℕ+ ↦ Checked.div
      (π ^ (-s) * Gamma s * (qExpansion (cuspWidth Γ) f Γ.strictWidthInfty_pos.ne').coeff n)
      ((mellinFrequency Γ n : ℂ) ^ s) (mellinFrequency_cpow_isUnit Γ n s))
      (Λ hk f ⟨s, regular hk f s⟩) := by
  refine hasSum_Λ_of_qExpansion_isBigO hk f (r := (k : ℝ) / 2)
    (by linarith [show (0 : ℝ) < k from mod_cast hk]) hs _ ?_ ?_
  · simpa only [ModularForm.Λ, (isStrongFEPair hk f).hf₀, sub_zero] using
      (isStrongFEPair hk f).Λ_eq ⟨s, regular hk f s⟩
  · exact CuspFormClass.qExpansion_isBigO f

@[fun_prop]
lemma differentiable_L : Differentiable ℂ (fun s ↦ L hk f ⟨s, (regular hk f s).2⟩) := by
  have hP := isStrongFEPair hk f
  have hL : (fun s ↦ L hk f ⟨s, (regular hk f s).2⟩) =
      fun s ↦ (2 * reciprocalGammaℂ s) * (weakFEPair hk f).Λ₀ s := by
    funext s
    simp only [L, hP.hf₀, hP.hg₀, smul_zero, dite_true, mul_zero, sub_zero, add_zero]
  rw [hL]
  exact (differentiable_reciprocalGammaℂ.const_mul _).mul (weakFEPair hk f).differentiable_Λ₀

theorem hasSum_L (hs : (k : ℝ) / 2 + 1 < s.re) :
    HasSum (fun n : ℕ+ ↦ Checked.div
      ((qExpansion (cuspWidth Γ) f Γ.strictWidthInfty_pos.ne').coeff n) (((n : ℕ) : ℂ) ^ s)
      (isUnit_pnat_cpow n s)) ((cuspWidth Γ : ℂ) ^ (-s) * L hk f ⟨s, (regular hk f s).2⟩) :=
  hasSum_L_of_hasSum_Λ hk f (by linarith [show (0 : ℝ) < k from mod_cast hk]) _ (hasSum_Λ f hk hs)

end CuspForm
