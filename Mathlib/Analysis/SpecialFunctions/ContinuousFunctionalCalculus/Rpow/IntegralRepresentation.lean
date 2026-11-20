/-
Copyright (c) 2025 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Integral
public import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.RingInverseOrder

/-!
# Integral representations of `rpow`

This file contains integral representations of the `rpow` function. The integration parameter
belongs to `Ioi (0 : ℝ)` and the argument belongs to `ℝ≥0`; in particular, both reciprocals in
`rpowIntegrand₀₁ p t x := t ^ p * (t⁻¹ - (t + x)⁻¹)` have positive denominators.
The measures live on the positive parameter domain, with Lebesgue measure pulled back along its
inclusion. No value at the omitted endpoint is part of the integrand.

This representation is useful for showing that `rpow` is operator monotone and operator concave
in this range; that is, `cfc rpow` is monotone/concave. The integrand can be shown to be
operator monotone and concave through direct means, and this integral lifts these properties
to `rpow`. These results can be found in
`Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order`.

## Notes

Here we only compute the integral up to a constant, even though the actual constant can be
computed via contour integration. We chose to avoid this, as the constant is seldom if ever
relevant in applications, and would needlessly complicate the proof.

## Main declarations

+ `rpowIntegrand₀₁ p t x := t ^ p * (t⁻¹ - (t + x)⁻¹)`
+ `rpowIntegrand₁₂ p t x := t ^ (p - 1) * (x * t⁻¹ + t * (t + x)⁻¹ - 1)`
+ `exists_measure_rpow_eq_integral_rpowIntegrand₀₁` and
  `exists_measure_rpow_eq_integral_rpowIntegrand₁₂`: a measure on `Ioi (0 : ℝ)` satisfies
  `x ^ p = ∫ t, rpowIntegrand₀₁ p t x ∂μ` (resp `x ^ p = ∫ t, rpowIntegrand₁₂ p t x ∂μ`)
+ `CFC.exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₀₁` and
  `CFC.exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₁₂`: the corresponding statements where
  `x ^ p` is defined via the CFC.

## TODO

+ Give analogous representations for the range `Ioo (-1) 0`.

## References

+ [carlen2010] Eric A. Carlen, "Trace inequalities and quantum entropies: An introductory course"
  (see Lemma 2.8)
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped NNReal Topology

namespace NNReal

/-- The nonnegative integral kernel on positive integration parameters. -/
noncomputable def rpowIntegrand₀₁ (p : ℝ) (t : Ioi (0 : ℝ)) (x : ℝ≥0) : ℝ≥0 :=
  ⟨(t : ℝ) ^ p * (Checked.inv (t : ℝ) t.property.ne'.isUnit -
    Checked.inv ((t : ℝ) + x) (add_pos_of_pos_of_nonneg t.property x.property).ne'.isUnit), by
    apply mul_nonneg (Real.rpow_nonneg t.property.le p)
    apply sub_nonneg.mpr
    exact inv_anti₀ t.property (le_add_of_nonneg_right x.property)⟩

/-- The kernel for exponents between one and two, expressed through the nonnegative kernel. -/
noncomputable def rpowIntegrand₁₂ (p : ℝ) (t : Ioi (0 : ℝ)) (x : ℝ≥0) : ℝ≥0 :=
  x * rpowIntegrand₀₁ (p - 1) t x

end NNReal

namespace Real

/-- The real coercion of the nonnegative kernel, for Bochner integration. -/
noncomputable abbrev rpowIntegrand₀₁ (p : ℝ) (t : Ioi (0 : ℝ)) (x : ℝ≥0) : ℝ :=
  NNReal.rpowIntegrand₀₁ p t x

/-- The real coercion of the nonnegative kernel for exponents between one and two. -/
noncomputable abbrev rpowIntegrand₁₂ (p : ℝ) (t : Ioi (0 : ℝ)) (x : ℝ≥0) : ℝ :=
  NNReal.rpowIntegrand₁₂ p t x

section ZeroOne

variable {p : ℝ} {t : Ioi (0 : ℝ)} {x : ℝ≥0}

private lemma rpowIntegrand₀₁_def :
    rpowIntegrand₀₁ p t x = (t : ℝ) ^ p * (Checked.inv (t : ℝ) t.property.ne'.isUnit -
      Checked.inv ((t : ℝ) + x) (add_pos_of_pos_of_nonneg t.property x.property).ne'.isUnit) :=
  rfl

@[simp]
lemma rpowIntegrand₀₁_zero_right : rpowIntegrand₀₁ p t 0 = 0 := by
  simp only [rpowIntegrand₀₁_def, NNReal.coe_zero, add_zero, sub_self, mul_zero]

lemma rpowIntegrand₀₁_eq_sub (p : ℝ) (t : Ioi (0 : ℝ)) :
    rpowIntegrand₀₁ p t = fun x : ℝ≥0 ↦ (t : ℝ) ^ (p - 1) -
      (t : ℝ) ^ p * Checked.inv ((t : ℝ) + x)
        (add_pos_of_pos_of_nonneg t.property x.property).ne'.isUnit := by
  funext x
  rw [rpowIntegrand₀₁_def, mul_sub, ← div_eq_mul_inv₀, ← Real.rpow_sub_one t.property.ne' p]

lemma rpowIntegrand₀₁_nonneg : 0 ≤ rpowIntegrand₀₁ p t x :=
  (NNReal.rpowIntegrand₀₁ p t x).property

lemma rpowIntegrand₀₁_eq_pow_div :
    rpowIntegrand₀₁ p t x = Checked.div ((t : ℝ) ^ (p - 1) * x) ((t : ℝ) + x)
      (add_pos_of_pos_of_nonneg t.property x.property).ne'.isUnit := by
  have ht : (t : ℝ) ≠ 0 := t.property.ne'
  have htx : (t : ℝ) + x ≠ 0 := (add_pos_of_pos_of_nonneg t.property x.property).ne'
  rw [rpowIntegrand₀₁_def, inv_sub_inv' (ha := ht.isUnit) (hb := htx.isUnit),
    add_sub_cancel_left, Real.rpow_sub_one ht p]
  simp only [div_eq_mul_inv₀]
  ring

lemma rpowIntegrand₀₁_apply_mul (hx : 0 < (x : ℝ)) :
    rpowIntegrand₀₁ p ⟨(x : ℝ) * t, mul_pos hx t.property⟩ x =
      rpowIntegrand₀₁ p t 1 * (x : ℝ) ^ (p - 1) := by
  have ht : (t : ℝ) ≠ 0 := t.property.ne'
  have hx0 : (x : ℝ) ≠ 0 := hx.ne'
  have ht1 : (t : ℝ) + 1 ≠ 0 := (add_pos t.property zero_lt_one).ne'
  have hxt : (x : ℝ) * (t : ℝ) + x ≠ 0 := (add_pos (mul_pos hx t.property) hx).ne'
  rw [rpowIntegrand₀₁_eq_pow_div, rpowIntegrand₀₁_eq_pow_div]
  change ((x : ℝ) * (t : ℝ)) ^ (p - 1) * x / ((x : ℝ) * (t : ℝ) + x) =
    (t : ℝ) ^ (p - 1) * 1 / ((t : ℝ) + 1) * (x : ℝ) ^ (p - 1)
  have hmul : ((x : ℝ) * (t : ℝ)) ^ (p - 1) = (x : ℝ) ^ (p - 1) * (t : ℝ) ^ (p - 1) :=
    Real.mul_rpow x.property t.property.le
  rw [congrArg (fun v : ℝ ↦ v * x / ((x : ℝ) * (t : ℝ) + x)) hmul]
  field_simp

lemma rpowIntegrand₀₁_apply_mul' (hx : 0 < (x : ℝ)) :
    rpowIntegrand₀₁ p ⟨(x : ℝ) * t, mul_pos hx t.property⟩ x * x =
      rpowIntegrand₀₁ p t 1 * (x : ℝ) ^ p := by
  rw [rpowIntegrand₀₁_apply_mul hx, mul_assoc, ← Real.rpow_add_one hx.ne']
  simp only [sub_add_cancel]

@[fun_prop]
lemma continuous_rpowIntegrand₀₁ (p : ℝ) : Continuous (rpowIntegrand₀₁ p).uncurry := by
  have ht : Continuous (fun y : Ioi (0 : ℝ) × ℝ≥0 ↦ (y.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hx : Continuous (fun y : Ioi (0 : ℝ) × ℝ≥0 ↦ (y.2 : ℝ)) :=
    NNReal.continuous_coe.comp continuous_snd
  exact (ht.rpow_const fun y ↦ Or.inl y.1.property.ne').mul
    ((ht.fun_inv₀ (h0 := fun y ↦ y.1.property.ne'.isUnit)).sub
      ((ht.add hx).fun_inv₀ (h0 := fun y ↦
        (add_pos_of_pos_of_nonneg y.1.property y.2.property).ne'.isUnit)))

@[fun_prop]
lemma continuous_rpowIntegrand₀₁_left : Continuous (fun t : Ioi (0 : ℝ) ↦ rpowIntegrand₀₁ p t x) :=
  (continuous_rpowIntegrand₀₁ p).comp (continuous_id.prodMk continuous_const)

@[fun_prop]
lemma continuous_rpowIntegrand₀₁_right : Continuous (rpowIntegrand₀₁ p t) :=
  (continuous_rpowIntegrand₀₁ p).comp (continuous_const.prodMk continuous_id)

lemma aestronglyMeasurable_rpowIntegrand₀₁ :
    AEStronglyMeasurable (fun t : Ioi (0 : ℝ) ↦ rpowIntegrand₀₁ p t x)
      (volume.comap Subtype.val) :=
  continuous_rpowIntegrand₀₁_left.aestronglyMeasurable

lemma rpowIntegrand₀₁_monotone : Monotone (rpowIntegrand₀₁ p t) := by
  intro x y hxy
  unfold rpowIntegrand₀₁ NNReal.rpowIntegrand₀₁
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg t.property.le p)
  apply sub_le_sub_left
  have htx : 0 < (t : ℝ) + x := add_pos_of_pos_of_nonneg t.property x.property
  have hxy' : (t : ℝ) + x ≤ (t : ℝ) + y := by gcongr
  exact inv_anti₀ htx hxy'

lemma rpowIntegrand₀₁_le_rpow_sub_two_mul_self :
    rpowIntegrand₀₁ p t x ≤ (t : ℝ) ^ (p - 2) * x := by
  have ht : (t : ℝ) ≠ 0 := t.property.ne'
  have htx : (t : ℝ) + x ≠ 0 := (add_pos_of_pos_of_nonneg t.property x.property).ne'
  calc
    _ = ((t : ℝ) ^ (p - 1) * x) / ((t : ℝ) + x) := rpowIntegrand₀₁_eq_pow_div
    _ ≤ ((t : ℝ) ^ (p - 1) * x) / (t : ℝ) :=
      div_le_div_of_nonneg_left (mul_nonneg (Real.rpow_nonneg t.property.le _) x.property)
        t.property (le_add_of_nonneg_right x.property)
    _ = (t : ℝ) ^ (p - 2) * x := by
      rw [mul_div_right_comm₀, ← Real.rpow_sub_one ht]
      congr 2
      ring

lemma rpowIntegrand₀₁_le_rpow_sub_one : rpowIntegrand₀₁ p t x ≤ (t : ℝ) ^ (p - 1) := by
  rw [rpowIntegrand₀₁_eq_sub]
  exact sub_le_self _ (mul_nonneg (Real.rpow_nonneg t.property.le p)
    (inv_nonneg.mpr (add_pos_of_pos_of_nonneg t.property x.property).le))

lemma rpowIntegrand₀₁_one_ge_rpow_sub_two (ht : 1 ≤ (t : ℝ)) :
    (1 : ℝ) / 2 * (t : ℝ) ^ (p - 2) ≤ rpowIntegrand₀₁ p t 1 := by
  have ht0 : (t : ℝ) ≠ 0 := t.property.ne'
  have ht1 : (t : ℝ) + 1 ≠ 0 := (add_pos t.property zero_lt_one).ne'
  calc
    _ = (t : ℝ) ^ (p - 1) * ((1 / 2) * (1 / (t : ℝ))) := by
      rw [show p - 2 = p - 1 - 1 by ring, Real.rpow_sub_one ht0]
      ring
    _ ≤ (t : ℝ) ^ (p - 1) * (1 / ((t : ℝ) + 1)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg t.property.le _)
      rw [one_div_mul_one_div₀]
      apply one_div_le_one_div_of_le (by positivity)
      linarith
    _ = rpowIntegrand₀₁ p t 1 := by
      rw [rpowIntegrand₀₁_eq_pow_div]
      simp only [NNReal.coe_one, mul_one, mul_one_div₀]
lemma integrable_rpowIntegrand₀₁ (hp : p ∈ Ioo 0 1) (x : ℝ≥0) :
    Integrable (fun t : Ioi (0 : ℝ) ↦ rpowIntegrand₀₁ p t x) (volume.comap Subtype.val) := by
  let g : ℝ → ℝ := Function.extend Subtype.val (fun t : Ioi (0 : ℝ) ↦ rpowIntegrand₀₁ p t x) 0
  have hg (t : Ioi (0 : ℝ)) : g t = rpowIntegrand₀₁ p t x :=
    Subtype.val_injective.extend_apply _ _ _
  have hgcont : ContinuousOn g (Ioi 0) := by
    rw [continuousOn_iff_continuous_domRestrict,
      show (Ioi (0 : ℝ)).domRestrict g = _ from funext hg]
    exact continuous_rpowIntegrand₀₁_left
  have hnear : IntegrableOn g (Ioc 0 1) := by
    refine IntegrableOn.congr_set_ae (t := Ioo 0 1) ?_ (Filter.EventuallyEq.symm Ioo_ae_eq_Ioc)
    refine ⟨(hgcont.mono Ioo_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioo, ?_⟩
    refine HasFiniteIntegral.mono' (g := fun t : ℝ ↦ t ^ (p - 1)) ?_ ?_
    · apply Integrable.hasFiniteIntegral
      rw [← IntegrableOn, intervalIntegral.integrableOn_Ioo_rpow_iff]
      · linarith [hp.1]
      · exact zero_lt_one
    · refine ae_restrict_of_forall_mem measurableSet_Ioo fun t ht ↦ ?_
      rw [hg ⟨t, ht.1⟩, Real.norm_of_nonneg rpowIntegrand₀₁_nonneg]
      exact rpowIntegrand₀₁_le_rpow_sub_one
  have hfar : IntegrableOn g (Ioi 1) := by
    refine ⟨(hgcont.mono (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable measurableSet_Ioi, ?_⟩
    refine HasFiniteIntegral.mono' (g := fun t : ℝ ↦ t ^ (p - 2) * x) ?_ ?_
    · apply HasFiniteIntegral.mul_const
      apply Integrable.hasFiniteIntegral
      exact integrableOn_Ioi_rpow_of_lt (by linarith [hp.2]) zero_lt_one
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht ↦ ?_
      have ht0 : 0 < t := zero_lt_one.trans ht
      rw [hg ⟨t, ht0⟩, Real.norm_of_nonneg rpowIntegrand₀₁_nonneg]
      exact rpowIntegrand₀₁_le_rpow_sub_two_mul_self
  have hgint : IntegrableOn g (Ioi 0) := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi zero_le_one]
    exact hnear.union hfar
  have h := (integrableOn_iff_comap_subtypeVal measurableSet_Ioi).mp hgint
  simpa only [Function.comp_def, hg] using h

lemma integral_rpowIntegrand₀₁_eq_rpow_mul_const (hp : p ∈ Ioo 0 1) (x : ℝ≥0) :
    (∫ t : Ioi (0 : ℝ), rpowIntegrand₀₁ p t x ∂volume.comap Subtype.val) =
      (x : ℝ) ^ p * (∫ t : Ioi (0 : ℝ), rpowIntegrand₀₁ p t 1 ∂volume.comap Subtype.val) := by
  by_cases hx : x = 0
  · simp [hx, Real.zero_rpow hp.1.ne']
  have hxpos : 0 < (x : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hx)
  let g (y : ℝ≥0) : ℝ → ℝ :=
    Function.extend Subtype.val (fun t : Ioi (0 : ℝ) ↦ rpowIntegrand₀₁ p t y) 0
  have hg (y : ℝ≥0) (t : Ioi (0 : ℝ)) : g y t = rpowIntegrand₀₁ p t y :=
    Subtype.val_injective.extend_apply _ _ _
  have hI (y : ℝ≥0) :
      (∫ t : Ioi (0 : ℝ), rpowIntegrand₀₁ p t y ∂volume.comap Subtype.val) =
        ∫ t in Ioi 0, g y t := by
    rw [← integral_subtype_comap measurableSet_Ioi]
    exact integral_congr_ae (.of_forall fun t ↦ (hg y t).symm)
  rw [hI x, hI 1]
  have heq : EqOn (fun t : ℝ ↦ g x ((x : ℝ) * t) * x)
      (fun t ↦ g 1 t * (x : ℝ) ^ p) (Ioi 0) := by
    intro t ht
    let tx : Ioi (0 : ℝ) := ⟨(x : ℝ) * t, mul_pos hxpos ht⟩
    have hgx : g x ((x : ℝ) * t) = rpowIntegrand₀₁ p tx x := hg x tx
    have hg₁ : g 1 t = rpowIntegrand₀₁ p ⟨t, ht⟩ 1 := hg 1 ⟨t, ht⟩
    change g x ((x : ℝ) * t) * x = g 1 t * (x : ℝ) ^ p
    rw [hgx, hg₁]
    exact rpowIntegrand₀₁_apply_mul' (p := p) (t := ⟨t, ht⟩) hxpos
  have hcv : (∫ t in Ioi 0, g x ((x : ℝ) * t) * x) = ∫ t in Ioi 0, g x t := by
    rw [integral_mul_const, mul_comm]
    simpa only [smul_eq_mul, mul_zero] using integral_comp_mul_left_Ioi' (g x) 0 hxpos
  rw [← hcv, setIntegral_congr_fun measurableSet_Ioi heq, integral_mul_const, mul_comm]
lemma le_integral_rpowIntegrand₀₁_one (hp : p ∈ Ioo 0 1) :
    Checked.div (-1) (2 * (p - 1))
      (mul_ne_zero (by norm_num) (sub_ne_zero.mpr hp.2.ne)).isUnit ≤
        ∫ t : Ioi (0 : ℝ), rpowIntegrand₀₁ p t 1 ∂volume.comap Subtype.val := by
  have hpne : p - 1 ≠ 0 := sub_ne_zero.mpr hp.2.ne
  let g : ℝ → ℝ := Function.extend Subtype.val (fun t : Ioi (0 : ℝ) ↦ rpowIntegrand₀₁ p t 1) 0
  have hg (t : Ioi (0 : ℝ)) : g t = rpowIntegrand₀₁ p t 1 :=
    Subtype.val_injective.extend_apply _ _ _
  have hgint : IntegrableOn g (Ioi 0) := by
    rw [integrableOn_iff_comap_subtypeVal measurableSet_Ioi]
    simpa only [Function.comp_def, hg] using integrable_rpowIntegrand₀₁ hp 1
  have hI : (∫ t : Ioi (0 : ℝ), rpowIntegrand₀₁ p t 1 ∂volume.comap Subtype.val) =
      ∫ t in Ioi 0, g t := by
    rw [← integral_subtype_comap measurableSet_Ioi]
    exact integral_congr_ae (.of_forall fun t ↦ (hg t).symm)
  rw [hI]
  calc _ = (1 / 2) * -((1 : ℝ) ^ (p - 1)) / (p - 1) := by
        simp only [one_rpow]
        field_simp
    _ = ∫ t in Ioi 1, (1 / 2) * t ^ (p - 2) := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith [hp.2]) zero_lt_one]
      ring_nf
    _ ≤ ∫ t in Ioi 1, g t := by
      refine setIntegral_mono_on ?_ (hgint.mono_set (Ioi_subset_Ioi zero_le_one))
        measurableSet_Ioi ?_
      · exact (integrableOn_Ioi_rpow_of_lt (by linarith [hp.2]) zero_lt_one).const_mul _
      · intro t ht
        have ht' : 1 < t := ht
        let u : Ioi (0 : ℝ) := ⟨t, Set.mem_Ioi.mpr (zero_lt_one.trans ht')⟩
        have hgu : g t = rpowIntegrand₀₁ p u 1 := hg u
        rw [hgu]
        exact rpowIntegrand₀₁_one_ge_rpow_sub_two (t := u) ht'.le
    _ ≤ ∫ t in Ioi 0, g t := by
      refine setIntegral_mono_set hgint ?_ (.of_forall (Ioi_subset_Ioi zero_le_one))
      refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht ↦ ?_
      rw [hg ⟨t, ht⟩]
      exact rpowIntegrand₀₁_nonneg

lemma integral_rpowIntegrand₀₁_one_pos (hp : p ∈ Ioo 0 1) :
    0 < ∫ t : Ioi (0 : ℝ), rpowIntegrand₀₁ p t 1 ∂volume.comap Subtype.val := by
  apply lt_of_lt_of_le _ (le_integral_rpowIntegrand₀₁_one hp)
  exact div_pos_of_neg_of_neg (by norm_num)
    (mul_neg_of_pos_of_neg (by norm_num) (sub_neg.mpr hp.2))

/-- The integral representation for nonnegative arguments and exponents in `(0,1)`. -/
lemma rpow_eq_const_mul_integral (hp : p ∈ Ioo 0 1) (x : ℝ≥0) :
    (x : ℝ) ^ p = Checked.inv
      (∫ t : Ioi (0 : ℝ), rpowIntegrand₀₁ p t 1 ∂volume.comap Subtype.val)
      (integral_rpowIntegrand₀₁_one_pos hp).ne'.isUnit *
        ∫ t : Ioi (0 : ℝ), rpowIntegrand₀₁ p t x ∂volume.comap Subtype.val := by
  rw [integral_rpowIntegrand₀₁_eq_rpow_mul_const hp x, mul_left_comm, inv_mul_cancel₀, mul_one]

/-- A positive measure on the actual integration domain represents every nonnegative argument. -/
lemma exists_measure_rpow_eq_integral_rpowIntegrand₀₁ (hp : p ∈ Ioo 0 1) :
    ∃ μ : Measure (Ioi (0 : ℝ)), ∀ x : ℝ≥0,
      Integrable (fun t ↦ rpowIntegrand₀₁ p t x) μ ∧
        (x : ℝ) ^ p = ∫ t, rpowIntegrand₀₁ p t x ∂μ := by
  let C : ℝ≥0 := ⟨Checked.inv
    (∫ t : Ioi (0 : ℝ), rpowIntegrand₀₁ p t 1 ∂volume.comap Subtype.val)
    (integral_rpowIntegrand₀₁_one_pos hp).ne'.isUnit,
    inv_nonneg.mpr (integral_rpowIntegrand₀₁_one_pos hp).le⟩
  refine ⟨C • volume.comap Subtype.val, fun x ↦ ⟨?_, ?_⟩⟩
  · exact (integrable_rpowIntegrand₀₁ hp x).smul_measure_nnreal
  · rw [integral_smul_nnreal_measure]
    exact rpow_eq_const_mul_integral hp x
end ZeroOne

section OneTwo
/-
## `p ∈ (1,2)`
-/
variable {p : ℝ} {t : Ioi (0 : ℝ)} {x : ℝ≥0}

lemma rpowIntegrand₁₂_eq_mul_rpowIntegrand₀₁ :
    rpowIntegrand₁₂ p t x = (x : ℝ) * rpowIntegrand₀₁ (p - 1) t x := rfl

lemma rpowIntegrand₁₂_eq_formula :
    rpowIntegrand₁₂ p t x = (t : ℝ) ^ (p - 1) *
      (Checked.inv (t : ℝ) t.property.ne'.isUnit * x + (t : ℝ) *
        Checked.inv ((t : ℝ) + x)
          (add_pos_of_pos_of_nonneg t.property x.property).ne'.isUnit - 1) := by
  have ht : (t : ℝ) ≠ 0 := t.property.ne'
  have htx : (t : ℝ) + x ≠ 0 := (add_pos_of_pos_of_nonneg t.property x.property).ne'
  rw [rpowIntegrand₁₂_eq_mul_rpowIntegrand₀₁, rpowIntegrand₀₁_def]
  have hcancel : ((t : ℝ) + x) * Checked.inv ((t : ℝ) + x) htx.isUnit = 1 := mul_inv_cancel₀
  linear_combination -((t : ℝ) ^ (p - 1)) * hcancel
lemma rpowIntegrand₁₂_nonneg : 0 ≤ rpowIntegrand₁₂ p t x := by
  rw [rpowIntegrand₁₂_eq_mul_rpowIntegrand₀₁]
  exact mul_nonneg x.property rpowIntegrand₀₁_nonneg

@[simp]
lemma rpowIntegrand₁₂_zero : rpowIntegrand₁₂ p t 0 = 0 := by
  simp [rpowIntegrand₁₂_eq_mul_rpowIntegrand₀₁]

@[fun_prop]
lemma continuous_rpowIntegrand₁₂ (p : ℝ) : Continuous (rpowIntegrand₁₂ p).uncurry := by
  have he : (rpowIntegrand₁₂ p).uncurry = fun y : Ioi (0 : ℝ) × ℝ≥0 ↦
      (y.2 : ℝ) * rpowIntegrand₀₁ (p - 1) y.1 y.2 :=
    funext fun _ ↦ rpowIntegrand₁₂_eq_mul_rpowIntegrand₀₁
  rw [he]
  exact (NNReal.continuous_coe.comp continuous_snd).mul (continuous_rpowIntegrand₀₁ (p - 1))

lemma monotone_rpowIntegrand₁₂ : Monotone (rpowIntegrand₁₂ p t) := by
  intro x y hxy
  rw [rpowIntegrand₁₂_eq_mul_rpowIntegrand₀₁, rpowIntegrand₁₂_eq_mul_rpowIntegrand₀₁]
  exact mul_le_mul (show (x : ℝ) ≤ y from hxy) (rpowIntegrand₀₁_monotone hxy)
    rpowIntegrand₀₁_nonneg y.property

lemma integrable_rpowIntegrand₁₂ (hp : p ∈ Ioo 1 2) (x : ℝ≥0) :
    Integrable (fun t : Ioi (0 : ℝ) ↦ rpowIntegrand₁₂ p t x) (volume.comap Subtype.val) := by
  simpa only [rpowIntegrand₁₂_eq_mul_rpowIntegrand₀₁] using
    (integrable_rpowIntegrand₀₁ (p := p - 1) (by constructor <;> linarith [hp.1, hp.2]) x).const_mul
      (x : ℝ)

private lemma rpow_eq_mul_rpow_sub_one_of_one_lt (hp : 1 < p) (x : ℝ≥0) :
    (x : ℝ) ^ p = (x : ℝ) * (x : ℝ) ^ (p - 1) := by
  have he : 1 + (p - 1) = p := by ring
  calc
    _ = (x : ℝ) ^ (1 + (p - 1)) := congrArg (fun t : ℝ ↦ (x : ℝ) ^ t) he.symm
    _ = _ := Real.rpow_one_add' x.property (by rw [he]; exact (zero_lt_one.trans hp).ne')

/-- The integral representation for nonnegative arguments and exponents in `(1,2)`. -/
lemma rpow_eq_const_mul_integral_rpowIntegrand₁₂ (hp : p ∈ Ioo 1 2) (x : ℝ≥0) :
    (x : ℝ) ^ p = Checked.inv
      (∫ t : Ioi (0 : ℝ), rpowIntegrand₀₁ (p - 1) t 1 ∂volume.comap Subtype.val)
      (integral_rpowIntegrand₀₁_one_pos
        (show p - 1 ∈ Ioo 0 1 from by constructor <;> linarith [hp.1, hp.2])).ne'.isUnit *
      ∫ t : Ioi (0 : ℝ), rpowIntegrand₁₂ p t x ∂volume.comap Subtype.val := by
  have hp' : p - 1 ∈ Ioo 0 1 := by constructor <;> linarith [hp.1, hp.2]
  have hx := rpow_eq_mul_rpow_sub_one_of_one_lt hp.1 x
  simp_rw [rpowIntegrand₁₂_eq_mul_rpowIntegrand₀₁]
  rw [integral_const_mul, mul_left_comm, ← rpow_eq_const_mul_integral hp' x, ← hx]

/-- A measure on positive integration parameters represents exponents in `(1,2)`. -/
lemma exists_measure_rpow_eq_integral_rpowIntegrand₁₂ (hp : p ∈ Ioo 1 2) :
    ∃ μ : Measure (Ioi (0 : ℝ)), ∀ x : ℝ≥0,
      Integrable (fun t ↦ rpowIntegrand₁₂ p t x) μ ∧
        (x : ℝ) ^ p = ∫ t, rpowIntegrand₁₂ p t x ∂μ := by
  obtain ⟨μ, hμ⟩ := exists_measure_rpow_eq_integral_rpowIntegrand₀₁
    (show p - 1 ∈ Ioo 0 1 from by constructor <;> linarith [hp.1, hp.2])
  refine ⟨μ, fun x ↦ ⟨?_, ?_⟩⟩
  · simpa only [rpowIntegrand₁₂_eq_mul_rpowIntegrand₀₁] using (hμ x).1.const_mul (x : ℝ)
  · simp_rw [rpowIntegrand₁₂_eq_mul_rpowIntegrand₀₁]
    rw [integral_const_mul, ← (hμ x).2]
    exact rpow_eq_mul_rpow_sub_one_of_one_lt hp.1 x
end OneTwo

end Real

namespace NNReal

@[simp] lemma coe_rpowIntegrand₀₁ (p : ℝ) (t : Ioi (0 : ℝ)) (x : ℝ≥0) :
    (rpowIntegrand₀₁ p t x : ℝ) = Real.rpowIntegrand₀₁ p t x := rfl

@[simp] lemma coe_rpowIntegrand₁₂ (p : ℝ) (t : Ioi (0 : ℝ)) (x : ℝ≥0) :
    (rpowIntegrand₁₂ p t x : ℝ) = Real.rpowIntegrand₁₂ p t x := rfl

@[simp] lemma rpowIntegrand₀₁_zero (p : ℝ) (t : Ioi (0 : ℝ)) :
    rpowIntegrand₀₁ p t 0 = 0 := by ext; simp

@[simp] lemma rpowIntegrand₁₂_zero (p : ℝ) (t : Ioi (0 : ℝ)) :
    rpowIntegrand₁₂ p t 0 = 0 := by ext; simp

@[fun_prop] lemma continuous_rpowIntegrand₀₁ (p : ℝ) :
    Continuous (rpowIntegrand₀₁ p).uncurry :=
  (Real.continuous_rpowIntegrand₀₁ p).subtype_mk _

@[fun_prop] lemma continuous_rpowIntegrand₁₂ (p : ℝ) :
    Continuous (rpowIntegrand₁₂ p).uncurry :=
  (Real.continuous_rpowIntegrand₁₂ p).subtype_mk _

end NNReal

namespace CFC
open Real

section NonUnitalCFC

variable {A : Type*} [NonUnitalNormedRing A] [StarRing A] [NormedSpace ℝ A] [SMulCommClass ℝ A A]
  [IsScalarTower ℝ A A] [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass ℝ A]
  [NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

lemma cfcₙ_rpowIntegrand₀₁_eq_cfcₙ_rpowIntegrand₀₁_one (p : ℝ) (t : Ioi (0 : ℝ))
    (a : A) (ha : 0 ≤ a) :
    cfcₙ (NNReal.rpowIntegrand₀₁ p t) a = (t : ℝ) ^ (p - 1) •
      cfcₙ (NNReal.rpowIntegrand₀₁ p ⟨1, Set.mem_Ioi.mpr zero_lt_one⟩)
        (Checked.inv (t : ℝ) t.property.ne'.isUnit • a) := by
  let u : ℝ≥0 := ⟨t, t.property.le⟩
  have hu : IsUnit u := (show u ≠ 0 from fun h ↦
    t.property.ne' (congrArg (fun v : ℝ≥0 ↦ (v : ℝ)) h)).isUnit
  let ui : ℝ≥0 := Checked.inv u hu
  let c : ℝ≥0 := u ^ (p - 1)
  let f := NNReal.rpowIntegrand₀₁ p ⟨1, Set.mem_Ioi.mpr zero_lt_one⟩
  have hui : (ui : ℝ) = Checked.inv (t : ℝ) t.property.ne'.isUnit :=
    map_inv₀ NNReal.toRealHom u
  have hc : (c : ℝ) = (t : ℝ) ^ (p - 1) := NNReal.coe_rpow u _
  have hscalar : NNReal.rpowIntegrand₀₁ p t = fun x : ℝ≥0 ↦ c • f (ui • x) := by
    funext x
    apply NNReal.coe_injective
    have ht : (t : ℝ) ≠ 0 := t.property.ne'
    have htx : (t : ℝ) + x ≠ 0 := (add_pos_of_pos_of_nonneg t.property x.property).ne'
    have hx : ((ui • x : ℝ≥0) : ℝ) = (t : ℝ)⁻¹ * x := by
      rw [smul_eq_mul, NNReal.coe_mul, hui]
    have hden : 0 < (1 : ℝ) + (t : ℝ)⁻¹ * x :=
      add_pos_of_pos_of_nonneg zero_lt_one
        (mul_nonneg (_root_.inv_nonneg.mpr t.property.le) x.property)
    have hfrac : ((t : ℝ)⁻¹ * x) / (1 + (t : ℝ)⁻¹ * x) = (x : ℝ) / ((t : ℝ) + x) := by
      apply (div_eq_div_iff (hb := hden.ne'.isUnit) (hd := htx.isUnit)).mpr
      field_simp
    change Real.rpowIntegrand₀₁ p t x = (c : ℝ) *
      Real.rpowIntegrand₀₁ p ⟨1, Set.mem_Ioi.mpr zero_lt_one⟩ (ui • x)
    simp only [Real.rpowIntegrand₀₁_eq_pow_div, hc, hx]
    change ((t : ℝ) ^ (p - 1) * (x : ℝ)) / ((t : ℝ) + x) = (t : ℝ) ^ (p - 1) *
      (((1 : ℝ) ^ (p - 1) * ((t : ℝ)⁻¹ * x)) / (1 + (t : ℝ)⁻¹ * x))
    rw [Real.one_rpow, one_mul, hfrac, mul_div_assoc₀]
  have hf : Continuous f :=
    (NNReal.continuous_rpowIntegrand₀₁ p).comp (continuous_const.prodMk continuous_id)
  have hf₀ : f 0 = 0 := NNReal.rpowIntegrand₀₁_zero p _
  have hg : Continuous (fun x : ℝ≥0 ↦ f (ui • x)) := hf.comp (continuous_const_smul ui)
  have hg₀ : f (ui • 0) = 0 := by rwa [smul_zero]
  have h : cfcₙ (NNReal.rpowIntegrand₀₁ p t) a = c • cfcₙ f (ui • a) := by
    rw [hscalar, cfcₙ_smul c _ a hg.continuousOn hg₀,
      cfcₙ_comp_smul ui f a hf.continuousOn hf₀ ha]
  simpa only [NNReal.smul_def, hc, hui, f] using h
variable (A) in
/-- The operator integral representation over positive integration parameters for `p ∈ (0,1)`. -/
lemma exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₀₁ [CompleteSpace A] {p : ℝ≥0}
    (hp : p ∈ Ioo 0 1) :
    ∃ μ : Measure (Ioi (0 : ℝ)), ∀ a ∈ Ici (0 : A),
      Integrable (fun t ↦ cfcₙ (NNReal.rpowIntegrand₀₁ p t) a) μ ∧
        a ^ p = ∫ t, cfcₙ (NNReal.rpowIntegrand₀₁ p t) a ∂μ := by
  have hp' : (p : ℝ) ∈ Ioo 0 1 := by exact_mod_cast hp
  obtain ⟨μ, hμ⟩ := Real.exists_measure_rpow_eq_integral_rpowIntegrand₀₁ hp'
  refine ⟨μ, fun a (ha : 0 ≤ a) ↦ ?_⟩
  nontriviality A
  let f (t : Ioi (0 : ℝ)) (r : ℝ) := Real.rpowIntegrand₀₁ p t r.toNNReal
  let maxr := sSup (quasispectrum ℝ a)
  let bound (t : Ioi (0 : ℝ)) := ‖f t maxr‖
  have hf : Continuous (Function.uncurry f) :=
    (Real.continuous_rpowIntegrand₀₁ p).comp
      (continuous_fst.prodMk (continuous_real_toNNReal.comp continuous_snd))
  have hbound : ∀ᵐ t ∂μ, ∀ r ∈ quasispectrum ℝ a, ‖f t r‖ ≤ bound t := by
    apply Filter.Eventually.of_forall
    intro t r hr
    simp only [f, bound, Real.norm_of_nonneg Real.rpowIntegrand₀₁_nonneg]
    apply Real.rpowIntegrand₀₁_monotone
    exact Real.toNNReal_le_toNNReal (le_csSup (IsCompact.bddAbove (quasispectrum.isCompact _)) hr)
  have hfinite : HasFiniteIntegral bound μ := (hμ maxr.toNNReal).1.norm.hasFiniteIntegral
  have hzero : ∀ᵐ t ∂μ, f t 0 = 0 := .of_forall fun _ ↦ by simp [f]
  have hcfc (t : Ioi (0 : ℝ)) :
      cfcₙ (NNReal.rpowIntegrand₀₁ p t) a = cfcₙ (f t) a := by
    simpa only [f, NNReal.coe_rpowIntegrand₀₁] using
      cfcₙ_nnreal_eq_real (NNReal.rpowIntegrand₀₁ p t) a ha
  refine ⟨?_, ?_⟩
  · simpa only [← hcfc] using
      integrable_cfcₙ f bound a hf.continuousOn hzero hbound hfinite ha.isSelfAdjoint
  · calc
      a ^ p = cfcₙ (fun r ↦ ∫ t, f t r ∂μ) a := by
        rw [nnrpow_eq_cfcₙ_real _ _]
        apply cfcₙ_congr
        intro r hr
        have hr0 : 0 ≤ r := by grind
        simpa only [f, Real.coe_toNNReal r hr0] using (hμ r.toNNReal).2
      _ = ∫ t, cfcₙ (f t) a ∂μ :=
        cfcₙ_integral f bound a hf.continuousOn hzero hbound hfinite ha.isSelfAdjoint
      _ = ∫ t, cfcₙ (NNReal.rpowIntegrand₀₁ p t) a ∂μ :=
        integral_congr_ae (.of_forall fun t ↦ (hcfc t).symm)

variable (A) in
/-- The operator integral representation over positive integration parameters for `p ∈ (1,2)`. -/
lemma exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₁₂ [CompleteSpace A] {p : ℝ≥0}
    (hp : p ∈ Ioo 1 2) :
    ∃ μ : Measure (Ioi (0 : ℝ)), ∀ a ∈ Ici (0 : A),
      Integrable (fun t ↦ cfcₙ (NNReal.rpowIntegrand₁₂ p t) a) μ ∧
        a ^ p = ∫ t, cfcₙ (NNReal.rpowIntegrand₁₂ p t) a ∂μ := by
  have hp' : (p : ℝ) ∈ Ioo 1 2 := by exact_mod_cast hp
  obtain ⟨μ, hμ⟩ := Real.exists_measure_rpow_eq_integral_rpowIntegrand₁₂ hp'
  refine ⟨μ, fun a (ha : 0 ≤ a) ↦ ?_⟩
  nontriviality A
  let f (t : Ioi (0 : ℝ)) (r : ℝ) := Real.rpowIntegrand₁₂ p t r.toNNReal
  let maxr := sSup (quasispectrum ℝ a)
  let bound (t : Ioi (0 : ℝ)) := ‖f t maxr‖
  have hf : Continuous (Function.uncurry f) :=
    (Real.continuous_rpowIntegrand₁₂ p).comp
      (continuous_fst.prodMk (continuous_real_toNNReal.comp continuous_snd))
  have hbound : ∀ᵐ t ∂μ, ∀ r ∈ quasispectrum ℝ a, ‖f t r‖ ≤ bound t := by
    apply Filter.Eventually.of_forall
    intro t r hr
    simp only [f, bound, Real.norm_of_nonneg Real.rpowIntegrand₁₂_nonneg]
    apply Real.monotone_rpowIntegrand₁₂
    exact Real.toNNReal_le_toNNReal (le_csSup (IsCompact.bddAbove (quasispectrum.isCompact _)) hr)
  have hfinite : HasFiniteIntegral bound μ := (hμ maxr.toNNReal).1.norm.hasFiniteIntegral
  have hzero : ∀ᵐ t ∂μ, f t 0 = 0 := .of_forall fun _ ↦ by simp [f]
  have hcfc (t : Ioi (0 : ℝ)) :
      cfcₙ (NNReal.rpowIntegrand₁₂ p t) a = cfcₙ (f t) a := by
    simpa only [f, NNReal.coe_rpowIntegrand₁₂] using
      cfcₙ_nnreal_eq_real (NNReal.rpowIntegrand₁₂ p t) a ha
  refine ⟨?_, ?_⟩
  · simpa only [← hcfc] using
      integrable_cfcₙ f bound a hf.continuousOn hzero hbound hfinite ha.isSelfAdjoint
  · calc
      a ^ p = cfcₙ (fun r ↦ ∫ t, f t r ∂μ) a := by
        rw [nnrpow_eq_cfcₙ_real _ _]
        apply cfcₙ_congr
        intro r hr
        have hr0 : 0 ≤ r := by grind
        simpa only [f, Real.coe_toNNReal r hr0] using (hμ r.toNNReal).2
      _ = ∫ t, cfcₙ (f t) a ∂μ :=
        cfcₙ_integral f bound a hf.continuousOn hzero hbound hfinite ha.isSelfAdjoint
      _ = ∫ t, cfcₙ (NNReal.rpowIntegrand₁₂ p t) a ∂μ :=
        integral_congr_ae (.of_forall fun t ↦ (hcfc t).symm)
end NonUnitalCFC

section UnitalCStarAlgebra

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma cfc_rpowIntegrand₀₁_eq_sub (p : ℝ) (t : Ioi (0 : ℝ)) (a : Ici (0 : A)) :
    cfc (NNReal.rpowIntegrand₀₁ p t) (a : A) =
      algebraMap ℝ A ((t : ℝ) ^ (p - 1)) - (t : ℝ) ^ p •
        Checked.inv (algebraMap ℝ A (t : ℝ) + a)
          ((isStrictlyPositive_algebraMap t.property).add_nonneg a.property).isUnit := by
  have hapos : IsSelfAdjoint (a : A) := a.property.isSelfAdjoint
  have hshift : IsStrictlyPositive (algebraMap ℝ A (t : ℝ) + a) :=
    (isStrictlyPositive_algebraMap t.property).add_nonneg a.property
  have hpos (r : spectrum ℝ (a : A)) : 0 < (t : ℝ) + r := by
    have hr : 0 ≤ (r : ℝ) := by grind
    exact add_pos_of_pos_of_nonneg t.property hr
  let q : C(spectrum ℝ (a : A), ℝ) :=
    ContinuousMap.const _ (t : ℝ) + (ContinuousMap.id ℝ).restrict (spectrum ℝ (a : A))
  let qi : C(spectrum ℝ (a : A), ℝ) :=
    ⟨fun r ↦ Checked.inv ((t : ℝ) + r) (hpos r).ne'.isUnit,
      (continuous_const.add continuous_subtype_val).fun_inv₀
        (h0 := fun r ↦ (hpos r).ne'.isUnit)⟩
  have hq : cfcHom (R := ℝ) hapos q = algebraMap ℝ A (t : ℝ) + a := by
    change cfcHom (R := ℝ) hapos
      (algebraMap ℝ C(spectrum ℝ (a : A), ℝ) (t : ℝ) +
        (ContinuousMap.id ℝ).restrict (spectrum ℝ (a : A))) = _
    rw [map_add, cfcHom_id]
    congr 1
    exact (cfcHom (R := ℝ) hapos).commutes (t : ℝ)
  have hqi : cfcHom (R := ℝ) hapos qi =
      Checked.inv (algebraMap ℝ A (t : ℝ) + a) hshift.isUnit := by
    apply (inv_eq_of_mul_eq_one_right₀ ?_).symm
    rw [← hq, ← map_mul]
    have heq : q * qi = 1 := by ext r; exact mul_inv_cancel₀
    rw [heq, map_one]
  rw [cfc_nnreal_eq_real _ _ a.property]
  calc
    _ = cfcHom (R := ℝ) hapos
        (algebraMap ℝ C(spectrum ℝ (a : A), ℝ) ((t : ℝ) ^ (p - 1)) - (t : ℝ) ^ p • qi) := by
      apply cfc_apply_of_coe_eq _ _ _ hapos
      funext r
      have hr : 0 ≤ (r : ℝ) := by grind
      change (t : ℝ) ^ (p - 1) - (t : ℝ) ^ p *
        Checked.inv ((t : ℝ) + r) (hpos r).ne'.isUnit = Real.rpowIntegrand₀₁ p t (r : ℝ).toNNReal
      rw [congrFun (Real.rpowIntegrand₀₁_eq_sub p t) ((r : ℝ).toNNReal)]
      simp only [Real.coe_toNNReal _ hr]
    _ = _ := by
      rw [map_sub, map_smul, hqi]
      congr 1
      exact (cfcHom (R := ℝ) hapos).commutes _

/-- The operator integrand is concave on the nonnegative cone in its inclusion coordinates. -/
lemma concaveOn_cfc_rpowIntegrand₀₁ (p : ℝ) (t : Ioi (0 : ℝ)) :
    ConcaveOn ℝ Set.univ
      (fun a : Ici (0 : A) ↦ cfc (NNReal.rpowIntegrand₀₁ p t) (a : A)) Subtype.val := by
  refine ⟨?_, ?_⟩
  · simpa only [Set.image_univ, Subtype.range_coe] using convex_Ici (0 : A)
  intro x _ y _ a b ha hb hab z _ hz
  change a • cfc (NNReal.rpowIntegrand₀₁ p t) (x : A) +
    b • cfc (NNReal.rpowIntegrand₀₁ p t) (y : A) ≤ cfc (NNReal.rpowIntegrand₀₁ p t) (z : A)
  rw [cfc_rpowIntegrand₀₁_eq_sub, cfc_rpowIntegrand₀₁_eq_sub, cfc_rpowIntegrand₀₁_eq_sub]
  have hconv := (CStarAlgebra.convexOn_inv_algebraMap_add (A := A) t.property).2
    (x := x) (y := y) (by trivial) (by trivial) ha hb hab (z := z) (by trivial) hz
  calc
    _ = algebraMap ℝ A ((t : ℝ) ^ (p - 1)) - (t : ℝ) ^ p •
        (a • Checked.inv (algebraMap ℝ A (t : ℝ) + x)
          ((isStrictlyPositive_algebraMap t.property).add_nonneg x.property).isUnit +
         b • Checked.inv (algebraMap ℝ A (t : ℝ) + y)
          ((isStrictlyPositive_algebraMap t.property).add_nonneg y.property).isUnit) := by
      simp only [smul_sub, smul_add, smul_comm a ((t : ℝ) ^ p), smul_comm b ((t : ℝ) ^ p)]
      rw [sub_add_sub_comm, ← add_smul, hab, one_smul]
    _ ≤ _ := sub_le_sub_left (smul_le_smul_of_nonneg_left hconv
      (Real.rpow_nonneg t.property.le p)) _

lemma monotone_cfc_rpowIntegrand₀₁ (p : ℝ) (t : Ioi (0 : ℝ)) :
    Monotone (fun a : Ici (0 : A) ↦ cfc (NNReal.rpowIntegrand₀₁ p t) (a : A)) := by
  intro x y hxy
  have hx : IsStrictlyPositive (algebraMap ℝ A (t : ℝ) + x) :=
    (isStrictlyPositive_algebraMap t.property).add_nonneg x.property
  have hi := CStarAlgebra.ringInverse_le_ringInverse
    (add_le_add le_rfl (show (x : A) ≤ y from hxy)) hx
  change cfc (NNReal.rpowIntegrand₀₁ p t) (x : A) ≤ cfc (NNReal.rpowIntegrand₀₁ p t) (y : A)
  rw [cfc_rpowIntegrand₀₁_eq_sub, cfc_rpowIntegrand₀₁_eq_sub]
  exact sub_le_sub_left (smul_le_smul_of_nonneg_left hi (Real.rpow_nonneg t.property.le p)) _
end UnitalCStarAlgebra

section NonUnitalCStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The operator integrand is monotone on the actual nonnegative operator cone. -/
lemma monotone_cfcₙ_rpowIntegrand₀₁ (p : ℝ) (t : Ioi (0 : ℝ)) :
    Monotone (fun a : Ici (0 : A) ↦ cfcₙ (NNReal.rpowIntegrand₀₁ p t) (a : A)) := by
  intro x y hxy
  rw [← Unitization.inr_le_inr_iff,
    Unitization.nnreal_cfcₙ_eq_cfc_inr (hf₀ := NNReal.rpowIntegrand₀₁_zero p t),
    Unitization.nnreal_cfcₙ_eq_cfc_inr (hf₀ := NNReal.rpowIntegrand₀₁_zero p t)]
  exact monotone_cfc_rpowIntegrand₀₁ p t
    (a := ⟨(x : Unitization ℂ A), Unitization.inr_nonneg_iff.mpr x.property⟩)
    (b := ⟨(y : Unitization ℂ A), Unitization.inr_nonneg_iff.mpr y.property⟩)
    (Unitization.inr_le_inr_iff.mpr hxy)

/-- The operator integrand is concave on the nonnegative cone, with its inclusion coordinates. -/
lemma concaveOn_cfcₙ_rpowIntegrand₀₁ (p : ℝ) (t : Ioi (0 : ℝ)) :
    ConcaveOn ℝ Set.univ
      (fun a : Ici (0 : A) ↦ cfcₙ (NNReal.rpowIntegrand₀₁ p t) (a : A)) Subtype.val := by
  refine ⟨?_, ?_⟩
  · simpa only [Set.image_univ, Subtype.range_coe] using convex_Ici (0 : A)
  intro x _ y _ a b ha hb hab z _ hz
  rw [← Unitization.inr_le_inr_iff, Unitization.inr_add, Unitization.inr_smul,
    Unitization.inr_smul,
    Unitization.nnreal_cfcₙ_eq_cfc_inr (hf₀ := NNReal.rpowIntegrand₀₁_zero p t),
    Unitization.nnreal_cfcₙ_eq_cfc_inr (hf₀ := NNReal.rpowIntegrand₀₁_zero p t),
    Unitization.nnreal_cfcₙ_eq_cfc_inr (hf₀ := NNReal.rpowIntegrand₀₁_zero p t)]
  apply (concaveOn_cfc_rpowIntegrand₀₁ (A := Unitization ℂ A) p t).2
    (x := ⟨(x : Unitization ℂ A), Unitization.inr_nonneg_iff.mpr x.property⟩)
    (y := ⟨(y : Unitization ℂ A), Unitization.inr_nonneg_iff.mpr y.property⟩)
    (by trivial) (by trivial) ha hb hab
    (z := ⟨(z : Unitization ℂ A), Unitization.inr_nonneg_iff.mpr z.property⟩) (by trivial)
  simpa only [Unitization.inr_add, Unitization.inr_smul] using
    congrArg (fun v : A ↦ (v : Unitization ℂ A)) hz
end NonUnitalCStarAlgebra

end CFC
