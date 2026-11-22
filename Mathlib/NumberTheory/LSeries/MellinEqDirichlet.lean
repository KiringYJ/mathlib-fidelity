/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
/-!
# Dirichlet series as Mellin transforms

Here we prove general results of the form "the Mellin transform of a power series in exp (-t) is
a Dirichlet series".
-/

public section

open Real Set MeasureTheory
open Complex

variable {ι : Type*} [Countable ι]

private lemma isUnit_rpow_of_pos {r : ℝ} (hr : 0 < r) (s : ℝ) : IsUnit (r ^ s) :=
  (Real.rpow_ne_zero_of_pos hr s).isUnit

private lemma isUnit_cpow_ofReal_of_pos {r : ℝ} (hr : 0 < r) (s : ℂ) :
    IsUnit ((r : ℂ) ^ s) :=
  (cpow_ne_zero_iff.mpr (Or.inl (ofReal_ne_zero.mpr hr.ne'))).isUnit

/-- Most basic version of the "Mellin transform = Dirichlet series" argument. -/
lemma hasSum_mellin {a : ι → ℂ} {p : ι → ℝ} {F : Ioi (0 : ℝ) → ℂ} {s : ℂ}
    (hp : ∀ i, a i = 0 ∨ 0 < p i) (hs : 0 < s.re)
    (hF : ∀ t : Ioi (0 : ℝ), HasSum (fun i ↦ a i * rexp (-p i * t.val)) (F t))
    (h_sum : Summable fun i : {i // 0 < p i} ↦
      Checked.div ‖a i‖ (p i ^ s.re) (by exact isUnit_rpow_of_pos i.2 s.re)) :
    HasSum (fun i : {i // 0 < p i} ↦ Checked.div (Gamma s * a i) ((p i : ℂ) ^ s)
      (by exact isUnit_cpow_ofReal_of_pos i.2 s)) (mellin F s) := by
  have hF' (t : Ioi (0 : ℝ)) :
      HasSum (fun i : {i // 0 < p i} ↦ a i * rexp (-p i * t.val)) (F t) := by
    apply (hasSum_subtype_iff_of_support_subset ?_).mpr (hF t)
    intro i hi
    exact (hp i).resolve_left (fun h ↦ hi (by simp [h]))
  let kernel (i : {i // 0 < p i}) (t : ℝ) : ℂ :=
    (t : ℂ) ^ (s - 1) * (a i * rexp (-p i * t))
  have heq (t : Ioi (0 : ℝ)) : (t.val : ℂ) ^ (s - 1) • F t =
      ∑' i, kernel i t.val := by
    simp only [kernel, smul_eq_mul, tsum_mul_left, (hF' t).tsum_eq]
  simp_rw [mellin, heq]
  convert!
    hasSum_integral_of_summable_integral_norm (μ := volume.comap Subtype.val)
      (F := fun i (t : Ioi (0 : ℝ)) ↦ kernel i t.val)
      (fun i ↦ ?_) ?_ using
    2 with i
  · rw [integral_subtype_comap (s := Ioi (0 : ℝ)) measurableSet_Ioi (kernel i)]
    dsimp only [kernel]
    simp_rw [← mul_assoc, mul_comm _ (a _), mul_assoc (a _), mul_div_assoc₀, integral_const_mul]
    have hpi := i.property
    have := integral_cpow_mul_exp_neg_mul_Ioi hs hpi
    simp_rw [← ofReal_mul, ← ofReal_neg, ← ofReal_exp, ← neg_mul (p i)] at this
    have harg : arg (p i : ℂ) ≠ π := by
      rw [arg_ofReal_of_nonneg hpi.le]
      exact Real.pi_ne_zero.symm
    rw [this, one_div₀, inv_cpow _ _ harg, div_eq_inv_mul₀]
  · -- integrability of terms
    apply (integrableOn_iff_comap_subtypeVal (s := Ioi (0 : ℝ)) (f := kernel i)
      measurableSet_Ioi).mp
    dsimp only [kernel]
    have hpi := i.property
    have hpower := isUnit_cpow_ofReal_of_pos hpi (s - 1)
    simp_rw [← mul_assoc, mul_comm _ (a i), mul_assoc]
    have := Complex.GammaIntegral_convergent hs
    rw [← mul_zero (p i), ← integrableOn_Ioi_comp_mul_left_iff _ _ hpi] at this
    refine (IntegrableOn.congr_fun (this.const_mul (1 / (p i : ℂ) ^ (s - 1)))
      (fun t (ht : 0 < t) ↦ ?_) measurableSet_Ioi).const_mul _
    simp_rw [mul_comm (↑(rexp _) : ℂ), ← mul_assoc, neg_mul, ofReal_mul]
    rw [mul_cpow_ofReal_nonneg hpi.le ht.le, ← mul_assoc, one_div₀,
      inv_mul_cancel₀ (ha := hpower), one_mul]
  · -- summability of integrals of norms
    have hnorm : (fun i : {i // 0 < p i} ↦
        ∫ t : Ioi (0 : ℝ), ‖kernel i t.val‖ ∂(volume.comap Subtype.val)) =
          fun i ↦ ∫ t in Ioi (0 : ℝ), ‖kernel i t‖ :=
      funext fun i ↦ integral_subtype_comap (s := Ioi (0 : ℝ)) measurableSet_Ioi
        (fun t ↦ ‖kernel i t‖)
    rw [hnorm]
    dsimp only [kernel]
    apply Summable.of_norm
    convert! h_sum.mul_left (Real.Gamma s.re) using 2 with i
    simp_rw [← mul_assoc, mul_comm _ (a i), mul_assoc, norm_mul (a i), integral_const_mul]
    rw [← mul_div_assoc₀, mul_comm (Real.Gamma _), mul_div_assoc₀, norm_mul ‖a i‖, norm_norm]
    have hpi := i.property
    congr 1
    have := Real.integral_rpow_mul_exp_neg_mul_Ioi hs hpi
    simp_rw [← neg_mul (p i), one_div₀, inv_rpow hpi.le, ← div_eq_inv_mul₀] at this
    rw [norm_of_nonneg (integral_nonneg (fun _ ↦ norm_nonneg _)), ← this]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht ↦ ?_)
    rw [norm_mul, norm_real, Real.norm_eq_abs, Real.abs_exp,
      norm_cpow_eq_rpow_re_of_pos ht, sub_re, one_re]

/-- Shortcut version for `p i = π * q i`. Frequencies with `q i ≤ 0` have zero
coefficient and are omitted before forming the quotients. -/
lemma hasSum_mellin_pi_mul {a : ι → ℂ} {q : ι → ℝ} {F : Ioi (0 : ℝ) → ℂ} {s : ℂ}
    (hq : ∀ i, a i = 0 ∨ 0 < q i) (hs : 0 < s.re)
    (hF : ∀ t : Ioi (0 : ℝ), HasSum (fun i ↦ a i * rexp (-π * q i * t.val)) (F t))
    (h_sum : Summable fun i : {i // 0 < q i} ↦
      Checked.div ‖a i‖ (q i ^ s.re) (by exact isUnit_rpow_of_pos i.2 s.re)) :
    HasSum (fun i : {i // 0 < q i} ↦
      Checked.div (π ^ (-s) * Gamma s * a i) ((q i : ℂ) ^ s)
        (by exact isUnit_cpow_ofReal_of_pos i.2 s))
      (mellin F s) := by
  have hp i : a i = 0 ∨ 0 < π * q i := (hq i).imp_right (mul_pos pi_pos)
  let e : {i // 0 < π * q i} ≃ {i // 0 < q i} :=
    Equiv.subtypeEquivRight (fun _ ↦ mul_pos_iff_of_pos_left pi_pos)
  have hsum : Summable (fun i : {i // 0 < π * q i} ↦
      Checked.div ‖a i‖ ((π * q i) ^ s.re) (isUnit_rpow_of_pos i.2 s.re)) := by
    apply (e.symm.summable_iff).mp
    convert h_sum.mul_left (π ^ (-s.re)) using 1
    funext i
    have hpq := isUnit_rpow_of_pos (mul_pos pi_pos i.property) s.re
    have hq' := isUnit_rpow_of_pos i.property s.re
    have hπ := isUnit_rpow_of_pos pi_pos s.re
    change ‖a i‖ / (π * q i) ^ s.re = π ^ (-s.re) * (‖a i‖ / q i ^ s.re)
    simp only [mul_rpow pi_pos.le i.property.le]
    rw [rpow_neg pi_pos.le s.re (hxy := hπ)]
    field
  have hbase := hasSum_mellin hp hs (by simpa only [neg_mul] using hF) hsum
  apply (e.symm.hasSum_iff.mpr hbase).congr_fun
  intro i
  have hqpower := isUnit_cpow_ofReal_of_pos i.2 s
  have hpiqpower := isUnit_cpow_ofReal_of_pos (mul_pos pi_pos i.2) s
  have hπ := isUnit_cpow_ofReal_of_pos pi_pos s
  change π ^ (-s) * Gamma s * a i / (q i : ℂ) ^ s =
    Gamma s * a i / ((π * q i : ℝ) : ℂ) ^ s
  simp only [ofReal_mul, mul_cpow_ofReal_nonneg pi_pos.le i.property.le]
  rw [cpow_neg _ _ (hxy := hπ)]
  field

/-- Version allowing constant terms. They are omitted before taking any reciprocal. -/
lemma hasSum_mellin_pi_mul₀ {a : ι → ℂ} {p : ι → ℝ} {F : Ioi (0 : ℝ) → ℂ} {s : ℂ}
    (hp : ∀ i, 0 ≤ p i) (hs : 0 < s.re)
    (hF : ∀ t : Ioi (0 : ℝ),
      HasSum (fun i ↦ if p i = 0 then 0 else a i * rexp (-π * p i * t.val)) (F t))
    (h_sum : Summable fun i : {i // 0 < p i} ↦
      Checked.div ‖a i‖ (p i ^ s.re) (by exact isUnit_rpow_of_pos i.2 s.re)) :
    HasSum (fun i : {i // 0 < p i} ↦
      Checked.div (π ^ (-s) * Gamma s * a i) ((p i : ℂ) ^ s)
        (by exact isUnit_cpow_ofReal_of_pos i.2 s))
      (mellin F s) := by
  classical
  let a' i := if p i = 0 then 0 else a i
  have hp' i : a' i = 0 ∨ 0 < p i := by
    simp only [a']
    split_ifs with h
    · exact Or.inl rfl
    · exact Or.inr (lt_of_le_of_ne (hp i) (Ne.symm h))
  have hF' (t : Ioi (0 : ℝ)) :
      HasSum (fun i ↦ a' i * rexp (-π * p i * t.val)) (F t) := by
    exact (hF t).congr_fun fun i ↦ by simp only [a']; split_ifs <;> simp
  have hsum' : Summable (fun i : {i // 0 < p i} ↦
      Checked.div ‖a' i‖ (p i ^ s.re) (isUnit_rpow_of_pos i.2 s.re)) := by
    refine h_sum.congr fun i ↦ ?_
    simp only [a', ite_eq_right i.2.ne']
  exact (hasSum_mellin_pi_mul hp' hs hF' hsum').congr_fun fun i ↦ by
    simp only [a', ite_eq_right i.2.ne']

/-- Mellin transforms of even theta series, indexed by the nonzero frequencies. -/
lemma hasSum_mellin_pi_mul_sq {a : ι → ℂ} {r : ι → ℝ} {F : Ioi (0 : ℝ) → ℂ} {s : ℂ}
    (hs : 0 < s.re) (hF : ∀ t : Ioi (0 : ℝ),
      HasSum (fun i ↦ if r i = 0 then 0 else a i * rexp (-π * r i ^ 2 * t.val)) (F t))
    (h_sum : Summable fun i : {i // r i ≠ 0} ↦
      Checked.div ‖a i‖ (|r i| ^ s.re) (by exact isUnit_rpow_of_pos (abs_pos.mpr i.2) s.re)) :
    HasSum (fun i : {i // r i ≠ 0} ↦ Checked.div (Gammaℝ s * a i) (((|r i| : ℝ) : ℂ) ^ s)
      (by exact isUnit_cpow_ofReal_of_pos (abs_pos.mpr i.2) s))
      (mellin F (s / 2)) := by
  have hs' : 0 < (s / 2).re := by rw [div_ofNat_re]; positivity
  let e : {i // 0 < r i ^ 2} ≃ {i // r i ≠ 0} :=
    Equiv.subtypeEquivRight (fun _ ↦ sq_pos_iff)
  have hsum : Summable (fun i : {i // 0 < r i ^ 2} ↦
      Checked.div ‖a i‖ ((r i ^ 2) ^ (s / 2).re) (isUnit_rpow_of_pos i.2 _)) := by
    apply (e.symm.summable_iff).mp
    convert h_sum using 1
    funext i
    have hr := isUnit_rpow_of_pos (abs_pos.mpr i.property) s.re
    have hr' := isUnit_rpow_of_pos (sq_pos_iff.mpr i.property) (s / 2).re
    change ‖a i‖ / (r i ^ 2) ^ (s / 2).re = ‖a i‖ / |r i| ^ s.re
    simp only [← sq_abs (r i), ← rpow_natCast_mul (abs_nonneg (r i)), div_ofNat_re,
      Nat.cast_ofNat, mul_div_cancel₀]
  have hbase := hasSum_mellin_pi_mul₀ (fun i ↦ sq_nonneg (r i)) hs'
    (by simpa only [sq_eq_zero_iff] using hF) hsum
  apply (e.symm.hasSum_iff.mpr hbase).congr_fun
  intro i
  have hrpower := isUnit_cpow_ofReal_of_pos (abs_pos.mpr i.2) s
  have hsquarepower := isUnit_cpow_ofReal_of_pos (sq_pos_iff.mpr i.2) (s / 2)
  change Gammaℝ s * a i / ((↑|r i| : ℂ) ^ s) =
    π ^ (-(s / 2)) * Gamma (s / 2) * a i / (((r i ^ 2 : ℝ) : ℂ) ^ (s / 2))
  have hpow : ((r i ^ 2 : ℝ) : ℂ) ^ (s / 2) = (↑|r i| : ℂ) ^ s := by
    rw [← sq_abs (r i), ofReal_pow, ← cpow_nat_mul']
    · congr 1
      push_cast
      field
    all_goals rw [arg_ofReal_of_nonneg (abs_nonneg _)]; linarith [pi_pos]
  rw [div_eq_div_iff, hpow, Gammaℝ_def, neg_div₀]

/-- Mellin transforms of odd theta series, indexed by the nonzero frequencies. -/
lemma hasSum_mellin_pi_mul_sq' {a : ι → ℂ} {r : ι → ℝ} {F : Ioi (0 : ℝ) → ℂ} {s : ℂ}
    (hs : 0 < s.re) (hF : ∀ t : Ioi (0 : ℝ),
      HasSum (fun i ↦ a i * r i * rexp (-π * r i ^ 2 * t.val)) (F t))
    (h_sum : Summable fun i : {i // r i ≠ 0} ↦
      Checked.div ‖a i‖ (|r i| ^ s.re) (by exact isUnit_rpow_of_pos (abs_pos.mpr i.2) s.re)) :
    HasSum (fun i : {i // r i ≠ 0} ↦
      Checked.div (Gammaℝ (s + 1) * a i * SignType.sign (r i)) (((|r i| : ℝ) : ℂ) ^ s)
        (by exact isUnit_cpow_ofReal_of_pos (abs_pos.mpr i.2) s))
      (mellin F ((s + 1) / 2)) := by
  have hs₂ : 0 < (s + 1).re := by rw [add_re, one_re]; positivity
  have hF' (t : Ioi (0 : ℝ)) : HasSum (fun i ↦ if r i = 0 then 0
      else a i * r i * rexp (-π * r i ^ 2 * t.val)) (F t) := by
    exact (hF t).congr_fun fun i ↦ by split_ifs with h <;> simp [h]
  have hsum : Summable (fun i : {i // r i ≠ 0} ↦
      Checked.div ‖a i * r i‖ (|r i| ^ (s + 1).re)
        (isUnit_rpow_of_pos (abs_pos.mpr i.2) _)) := by
    convert h_sum using 1
    funext i
    have hpow : |r i| ^ (s + 1).re = |r i| ^ s.re * |r i| := by
      rw [add_re, one_re, rpow_add (abs_pos.mpr i.property), rpow_one]
    field_simp
    rw [norm_mul, norm_real, Real.norm_eq_abs, hpow]
    ring
  apply (hasSum_mellin_pi_mul_sq hs₂ hF' hsum).congr_fun
  intro i
  have hrpower := isUnit_cpow_ofReal_of_pos (abs_pos.mpr i.2) s
  have hrpower' := isUnit_cpow_ofReal_of_pos (abs_pos.mpr i.2) (s + 1)
  have hpow : (↑|r i| : ℂ) ^ (s + 1) = (↑|r i| : ℂ) ^ s * ↑|r i| := by
    rw [cpow_add _ _ (ofReal_ne_zero.mpr (abs_ne_zero.mpr i.property)), cpow_one]
  have hsign : (r i : ℂ) = (SignType.sign (r i) : ℂ) * ↑|r i| := by
    simpa only [← ofRealHom_eq_coe, map_mul, SignType.map_cast] using
      congrArg (fun x : ℝ ↦ (x : ℂ)) (sign_mul_abs (r i)).symm
  field_simp
  rw [hpow, hsign]
  ring
