/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mihai Iancu, Stefan Kebekus, Sebastian Schleissinger
-/
module

public import Mathlib.Analysis.Complex.MeanValue
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# Poisson Integral Formula

We present two versions of the **Poisson Integral Formula** for ℂ-differentiable functions on
arbitrary disks in the complex plane, formulated with the real part of the Herglotz–Riesz kernel of
integration and with the Poisson kernel, respectively.
-/

public section

open Complex MeasureTheory Metric Real Set Filter

open scoped Topology

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f : ℂ → E} {R : ℝ} {w c : ℂ} {s : Set ℂ}

/-!
## Kernels of Integration

For convenience, this preliminary section discussed the kernels on integration that appear in the
various versions of the Poisson Formula.
-/

/--
The Herglotz-Riesz kernel of integration.
-/
noncomputable def herglotzRieszKernel (c w : ℂ) (z : ({w}ᶜ : Set ℂ)) : ℂ :=
  Checked.div (z.val - c + (w - c)) (z.val - w)
    (sub_ne_zero.mpr (mem_compl_singleton_iff.mp z.2)).isUnit

lemma herglotzRieszKernel_def (c w : ℂ) (z : ({w}ᶜ : Set ℂ)) :
    herglotzRieszKernel c w z = (z.val - c + (w - c)) / (z.val - w) := by rw [herglotzRieszKernel]

lemma herglotzRieszKernel_add_const (c w : ℂ) (z : ({w - c}ᶜ : Set ℂ)) :
    herglotzRieszKernel c w ⟨z.val + c, by
      exact mem_compl_singleton_iff.mpr fun h ↦ z.2 (eq_sub_iff_add_eq.mpr h)⟩ =
        herglotzRieszKernel 0 (w - c) z := by
  have hdiff : z.val + c - w = z.val - (w - c) := by abel
  simp only [herglotzRieszKernel_def, add_sub_cancel_right, sub_zero, hdiff]

/-- The Poisson kernel on the complement of its pole. -/
noncomputable def poissonKernel (c w : ℂ) (z : ({w}ᶜ : Set ℂ)) : ℝ :=
  Checked.div (‖z.val - c‖ ^ 2 - ‖w - c‖ ^ 2) (‖z.val - w‖ ^ 2)
    ((norm_ne_zero_iff.mpr (sub_ne_zero.mpr (mem_compl_singleton_iff.mp z.2))).isUnit.pow 2)

lemma poissonKernel_def (c w : ℂ) (z : ({w}ᶜ : Set ℂ)) :
    poissonKernel c w z = (‖z.val - c‖ ^ 2 - ‖w - c‖ ^ 2) / ‖z.val - w‖ ^ 2 := by rw [poissonKernel]

private lemma poissonKernel_eq_re_herglotzRieszKernel_aux {a b : ℂ} (hab : a ≠ b) :
    ((a + b) / (a - b)).re = (‖a‖ ^ 2 - ‖b‖ ^ 2) / ‖a - b‖ ^ 2 := by
  rw [div_re, ← add_div, add_re, sub_re, add_im, sub_im]
  simp only [normSq_eq_norm_sq]
  congr 1
  simp only [← normSq_eq_norm_sq, normSq_apply]
  ring

/-- The real part of the Herglotz–Riesz kernel is the Poisson kernel. -/
lemma poissonKernel_eq_re_herglotzRieszKernel {c w : ℂ} :
    poissonKernel c w = Complex.re ∘ herglotzRieszKernel c w := by
  funext z
  have hz : z.val - c ≠ w - c := fun h ↦ z.2 (sub_left_inj.mp h)
  have hdiff : z.val - c - (w - c) = z.val - w := by abel
  simpa only [poissonKernel_def, herglotzRieszKernel_def, Function.comp_apply, hdiff] using
    (poissonKernel_eq_re_herglotzRieszKernel_aux hz).symm

/-- Upper estimate for the real part of the Herglotz–Riesz kernel. -/
theorem re_herglotzRieszKernel_le {c z : ℂ} (hz : z ∈ sphere c R) (hw : w ∈ ball c R) :
    (herglotzRieszKernel c w ⟨z, sphere_disjoint_ball.ne_of_mem hz hw⟩).re ≤
      Checked.div (R + ‖w - c‖) (R - ‖w - c‖)
        (sub_pos.mpr (mem_ball_iff_norm.mp hw)).ne'.isUnit := by
  have hr : ‖w - c‖ < R := mem_ball_iff_norm.mp hw
  have hR : 0 < R := (norm_nonneg _).trans_lt hr
  have hzR := mem_sphere_iff_norm.mp hz
  have hsub : z - c - (w - c) = z - w := by abel
  have hlow : R - ‖w - c‖ ≤ ‖z - w‖ := by
    simpa only [hzR, hsub] using norm_sub_norm_le (z - c) (w - c)
  have hpos : 0 < R - ‖w - c‖ := sub_pos.mpr hr
  have hnorm : 0 < ‖z - w‖ := hpos.trans_le hlow
  have hn : 0 ≤ R ^ 2 - ‖w - c‖ ^ 2 :=
    sub_nonneg.mpr (pow_le_pow_left₀ (norm_nonneg _) hr.le 2)
  let z' : ({w}ᶜ : Set ℂ) := ⟨z, sphere_disjoint_ball.ne_of_mem hz hw⟩
  have hker : poissonKernel c w z' = (herglotzRieszKernel c w z').re :=
    congrFun poissonKernel_eq_re_herglotzRieszKernel z'
  rw [← hker, poissonKernel_def]
  simp only [z', hzR]
  calc
    _ ≤ (R ^ 2 - ‖w - c‖ ^ 2) / (R - ‖w - c‖) ^ 2 :=
      (div_le_div_iff₀ (pow_pos hnorm 2) (pow_pos hpos 2)).2
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hpos.le hlow 2) hn)
    _ = _ := by field_simp; ring

/-- Lower estimate for the real part of the Herglotz–Riesz kernel. -/
theorem le_re_herglotzRieszKernel {c z : ℂ} (hz : z ∈ sphere c R) (hw : w ∈ ball c R) :
    Checked.div (R - ‖w - c‖) (R + ‖w - c‖)
        (add_pos_of_pos_of_nonneg ((norm_nonneg _).trans_lt (mem_ball_iff_norm.mp hw))
          (norm_nonneg _)).ne'.isUnit ≤
      (herglotzRieszKernel c w ⟨z, sphere_disjoint_ball.ne_of_mem hz hw⟩).re := by
  have hr : ‖w - c‖ < R := mem_ball_iff_norm.mp hw
  have hR : 0 < R := (norm_nonneg _).trans_lt hr
  have hzR := mem_sphere_iff_norm.mp hz
  have hsub : z - c - (w - c) = z - w := by abel
  have hhigh : ‖z - w‖ ≤ R + ‖w - c‖ := by
    simpa only [hzR, hsub] using norm_sub_le (z - c) (w - c)
  have hpos : 0 < R + ‖w - c‖ := add_pos_of_pos_of_nonneg hR (norm_nonneg _)
  have hnorm : 0 < ‖z - w‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (sphere_disjoint_ball.ne_of_mem hz hw))
  have hn : 0 ≤ R ^ 2 - ‖w - c‖ ^ 2 :=
    sub_nonneg.mpr (pow_le_pow_left₀ (norm_nonneg _) hr.le 2)
  let z' : ({w}ᶜ : Set ℂ) := ⟨z, sphere_disjoint_ball.ne_of_mem hz hw⟩
  have hker : poissonKernel c w z' = (herglotzRieszKernel c w z').re :=
    congrFun poissonKernel_eq_re_herglotzRieszKernel z'
  rw [← hker, poissonKernel_def]
  simp only [z', hzR]
  calc
    _ = (R ^ 2 - ‖w - c‖ ^ 2) / (R + ‖w - c‖) ^ 2 := by field_simp; ring
    _ ≤ _ := (div_le_div_iff₀ (pow_pos hpos 2) (pow_pos hnorm 2)).2
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hnorm.le hhigh 2) hn)

/-- The Herglotz–Riesz kernel is continuous away from its pole. -/
@[fun_prop]
lemma continuous_herglotzRieszKernel (c w : ℂ) : Continuous (herglotzRieszKernel c w) := by
  exact ((continuous_subtype_val.sub continuous_const).add continuous_const).div₀
    (continuous_subtype_val.sub continuous_const)
    (h₀ := fun z ↦ (sub_ne_zero.mpr (mem_compl_singleton_iff.mp z.2)).isUnit)

private theorem circleAverageOn_sub_center_smul {c : ℂ} {R : ℝ}
    (g : sphere c |R| → E) :
    Real.circleAverageOn (fun z : sphere c |R| ↦ (z.val - c) • g z) =
      (2 * π * I : ℂ)⁻¹ • circleIntegralOn
        (fun z : sphere c (abs |R|) ↦ g ⟨z.val, by simpa only [abs_abs] using z.2⟩) c |R| := by
  by_cases hR : R = 0
  · subst R
    rw [circleIntegralOn_sphere]
    simp only [deriv_circleMap]
    simp [circleAverageOn, circleMap_zero_radius, Function.const_apply]
  · simpa only [inv_smul_smul₀] using
      (Real.circleAverageOn_eq_circleIntegralOn
        (f := fun z : sphere c |R| ↦ (z.val - c) • g z) hR)

private theorem poisson_reflected_denominator {c w y : ℂ} {R : ℝ}
    (hw : w ∈ ball c R) (hy : y ∈ closedBall c R) :
    IsUnit ((R : ℂ) ^ 2 - (starRingEnd ℂ) (w - c) * (y - c)) := by
  have hω : ‖w - c‖ < R := mem_ball_iff_norm.mp hw
  have hR := (norm_nonneg _).trans_lt hω
  have hyR : ‖y - c‖ ≤ R := mem_closedBall_iff_norm.mp hy
  have hlt : ‖(starRingEnd ℂ) (w - c) * (y - c)‖ < ‖(R : ℂ) ^ 2‖ := by
    simp only [norm_mul, norm_conj, norm_pow, norm_real, Real.norm_eq_abs, abs_of_pos hR]
    calc
      ‖w - c‖ * ‖y - c‖ ≤ ‖w - c‖ * R := mul_le_mul_of_nonneg_left hyR (norm_nonneg _)
      _ < R ^ 2 := by simpa only [pow_two] using mul_lt_mul_of_pos_right hω hR
  exact (sub_ne_zero.mpr (ne_of_apply_ne norm hlt.ne')).isUnit

private theorem coe_re_herglotzRiesz_eq {a b : ℂ} {R : ℝ} (ha : ‖a‖ = R) (hab : a ≠ b)
    (hq : IsUnit ((R : ℂ) ^ 2 - (starRingEnd ℂ) b * a)) :
    ((((a + b) / (a - b)).re : ℝ) : ℂ) =
      a / (a - b) + (starRingEnd ℂ) b * a / ((R : ℂ) ^ 2 - (starRingEnd ℂ) b * a) := by
  have hbase : IsUnit (a - b) := (sub_ne_zero.mpr hab).isUnit
  have hconj : IsUnit ((starRingEnd ℂ) a - (starRingEnd ℂ) b) := by
    simpa only [map_sub] using hbase.map (starRingEnd ℂ)
  have hstar (x : ℂ) : ((‖x‖ ^ 2 : ℝ) : ℂ) = x * (starRingEnd ℂ) x := by
    simpa only [ofReal_pow] using (Complex.mul_conj' x).symm
  have hR : a * (starRingEnd ℂ) a = (R : ℂ) ^ 2 := by
    rw [← hstar, ha, ofReal_pow]
  have hfac : (R : ℂ) ^ 2 - (starRingEnd ℂ) b * a =
      a * ((starRingEnd ℂ) a - (starRingEnd ℂ) b) := by
    rw [← hR, mul_sub, mul_comm a ((starRingEnd ℂ) b)]
  have hunit : IsUnit a := isUnit_of_mul_isUnit_left (hfac ▸ hq)
  rw [poissonKernel_eq_re_herglotzRieszKernel_aux hab, ofReal_div, ofReal_sub]
  simp only [hstar, map_sub, hfac]
  field_simp [hbase, hconj, hunit]
  ring

private lemma intervalIntegrable_smul_on_sphere {c : ℂ} {R : ℝ} (hf : CircleIntegrable f c |R|)
    {k : sphere c |R| → ℂ} (hk : Continuous k) :
    IntervalIntegrable (fun θ : ℝ ↦
      k ⟨circleMap c |R| θ, circleMap_mem_sphere c (abs_nonneg R) θ⟩ • f (circleMap c |R| θ))
      volume 0 (2 * π) :=
  ((circleIntegrable_def _ _ _).mp hf).continuousOn_smul
    (hk.comp ((continuous_circleMap c |R|).subtype_mk _)).continuousOn

private lemma circleAverageOn_add {c : ℂ} {R : ℝ} {u v : sphere c |R| → E}
    (hu : IntervalIntegrable (fun θ : ℝ ↦
      u ⟨circleMap c |R| θ, circleMap_mem_sphere c (abs_nonneg R) θ⟩) volume 0 (2 * π))
    (hv : IntervalIntegrable (fun θ : ℝ ↦
      v ⟨circleMap c |R| θ, circleMap_mem_sphere c (abs_nonneg R) θ⟩) volume 0 (2 * π)) :
    Real.circleAverageOn (fun z ↦ u z + v z) =
      Real.circleAverageOn u + Real.circleAverageOn v := by
  simp only [circleAverageOn, intervalIntegral.integral_add hu hv, smul_add]

/-- The Poisson integral formula for the real part of the Herglotz–Riesz kernel. -/
theorem DiffContOnCl.circleAverage_re_herglotzRieszKernel_smul [CompleteSpace E] {c : ℂ}
    (hf : DiffContOnCl ℂ f (ball c R)) (hw : w ∈ ball c R) :
    Real.circleAverageOn (fun z : sphere c |R| ↦
      (herglotzRieszKernel c w
        ⟨z.val, mem_compl_singleton_iff.mpr
          (sub_ne_zero.mp (isUnit_sub_of_mem_sphere_of_mem_ball hw z).ne_zero)⟩).re •
        f z.val) = f w := by
  have hR : 0 < R := pos_of_mem_ball hw
  let q (z : ℂ) := (R : ℂ) ^ 2 - (starRingEnd ℂ) (w - c) * (z - c)
  let U : Set ℂ := {z | IsUnit (q z)}
  let u : ℂ → ℂ := Function.extend (Subtype.val : U → ℂ)
    (fun z : U ↦ Checked.inv (q z.val) z.2) 0
  have hu (z : ℂ) (hz : IsUnit (q z)) : u z = Checked.inv (q z) hz :=
    Subtype.val_injective.extend_apply _ _ (⟨z, hz⟩ : U)
  have hqd : Differentiable ℂ q := by
    dsimp only [q]
    fun_prop
  have hud (z : ℂ) (hz : IsUnit (q z)) : DifferentiableAt ℂ u z := by
    have hmem : U ∈ 𝓝 z :=
      (hqd.continuous.continuousAt.eventually_ne hz.ne_zero).mono fun _ hy ↦ hy.isUnit
    refine DifferentiableAt.of_restrict (s := U) (x := ⟨z, hz⟩) ?_ hmem
    have hfun : (fun x : U ↦ u x.val) = fun x : U ↦ Checked.inv (q x.val) x.2 :=
      funext fun x ↦ hu x.val x.2
    rw [hfun]
    exact (hqd z).inv hz
  let g (z : ℂ) := ((starRingEnd ℂ) (w - c) * u z) • f z
  have hgd : DiffContOnCl ℂ g (ball c R) := by
    have hcoef : DifferentiableOn ℂ (fun z ↦ (starRingEnd ℂ) (w - c) * u z) (closure (ball c R)) :=
      fun z hz ↦ by
        have hc : DifferentiableAt ℂ (fun _ : ℂ ↦ (starRingEnd ℂ) (w - c)) z := by fun_prop
        exact (hc.mul (hud z (poisson_reflected_denominator hw
          (closure_ball_subset_closedBall hz)))).differentiableWithinAt
    exact hcoef.diffContOnCl.smul hf
  let S := sphere c |R|
  let k (z : S) := Checked.div (z.val - c) (z.val - w)
    (isUnit_sub_of_mem_sphere_of_mem_ball hw z)
  let A (z : S) := k z • f z.val
  let B (z : S) := (z.val - c) • g z.val
  have hAc : Continuous k :=
    (continuous_subtype_val.sub continuous_const).div₀
      (continuous_subtype_val.sub continuous_const)
  have hAcircle : Real.circleAverageOn A = f w := by
    have hfAbs : DiffContOnCl ℂ f (ball c |R|) := by simpa only [abs_of_pos hR] using hf
    have hwAbs : w ∈ ball c |R| := by simpa only [abs_of_pos hR] using hw
    exact hfAbs.circleAverage_smul_div hwAbs
  have hBcircle : Real.circleAverageOn B = 0 := by
    rw [circleAverageOn_sub_center_smul (fun z : S ↦ g z.val), circleIntegralOn_sphere]
    change (2 * π * I : ℂ)⁻¹ • circleIntegral g c |R| = 0
    rw [abs_of_pos hR, hgd.circleIntegral_eq_zero hR.le, smul_zero]
  have hsub : sphere c (abs |R|) ⊆ closedBall c R := by
    rw [abs_abs, abs_of_pos hR]
    exact sphere_subset_closedBall
  have hfint : CircleIntegrable f c |R| := (hf.continuousOn_ball.mono hsub).circleIntegrable'
  have hAint := intervalIntegrable_smul_on_sphere hfint hAc
  have hBcont : ContinuousOn (fun z : ℂ ↦ (z - c) • g z) (sphere c (abs |R|)) :=
    ((continuous_id.sub continuous_const).continuousOn).smul (hgd.continuousOn_ball.mono hsub)
  have hBint : IntervalIntegrable
      (fun θ : ℝ ↦ B ⟨circleMap c |R| θ, circleMap_mem_sphere c (abs_nonneg R) θ⟩)
      volume 0 (2 * π) := by
    exact hBcont.circleIntegrable' (R := |R|)
  have hpoint (z : S) :
      (herglotzRieszKernel c w
        ⟨z.val, mem_compl_singleton_iff.mpr
          (sub_ne_zero.mp (isUnit_sub_of_mem_sphere_of_mem_ball hw z).ne_zero)⟩).re •
        f z.val = A z + B z := by
    have hz : z.val ∈ closedBall c R := sphere_subset_closedBall (by
      simpa only [S, abs_of_pos hR] using z.2)
    have hq : IsUnit (q z.val) := poisson_reflected_denominator hw hz
    have hne : z.val - c ≠ w - c := fun he ↦
      (isUnit_sub_of_mem_sphere_of_mem_ball hw z).ne_zero
        (sub_eq_zero.mpr (sub_left_inj.mp he))
    have hznorm : ‖z.val - c‖ = R := by
      simpa only [abs_of_pos hR] using mem_sphere_iff_norm.mp z.2
    have hdiff : z.val - c - (w - c) = z.val - w := by abel
    have halg := coe_re_herglotzRiesz_eq hznorm hne hq
    rw [← Complex.coe_smul]
    simp only [herglotzRieszKernel_def, hdiff] at halg ⊢
    rw [halg, add_smul]
    simp only [A, B, k, g, hu z.val hq, q, div_eq_mul_inv₀, smul_smul]
    congr 1
    rw [mul_assoc, mul_left_comm]
  simp_rw [hpoint]
  rw [circleAverageOn_add hAint hBint, hAcircle, hBcircle, add_zero]

/-- The Poisson integral formula with the Herglotz–Riesz kernel expanded. -/
theorem DiffContOnCl.circleAverage_re_herglotzRieszKernel_smul' [CompleteSpace E] {c : ℂ}
    (hf : DiffContOnCl ℂ f (ball c R)) (hw : w ∈ ball c R) :
    Real.circleAverageOn (fun z : sphere c |R| ↦
      (Checked.div (z.val - c + (w - c)) (z.val - w)
        (isUnit_sub_of_mem_sphere_of_mem_ball hw z)).re • f z.val) = f w := by
  simpa only [herglotzRieszKernel_def] using hf.circleAverage_re_herglotzRieszKernel_smul hw

/-- The Poisson integral formula for complex differentiable functions. -/
theorem DiffContOnCl.circleAverage_poissonKernel_smul [CompleteSpace E] {c : ℂ}
    (hf : DiffContOnCl ℂ f (ball c R)) (hw : w ∈ ball c R) :
    Real.circleAverageOn (fun z : sphere c |R| ↦
      poissonKernel c w ⟨z.val, mem_compl_singleton_iff.mpr
          (sub_ne_zero.mp (isUnit_sub_of_mem_sphere_of_mem_ball hw z).ne_zero)⟩ •
        f z.val) = f w := by
  simpa only [poissonKernel_eq_re_herglotzRieszKernel, Function.comp_apply] using
    hf.circleAverage_re_herglotzRieszKernel_smul hw

/-- The Poisson integral formula with the Poisson kernel expanded. -/
theorem DiffContOnCl.circleAverage_poissonKernel_smul' [CompleteSpace E] {c : ℂ}
    (hf : DiffContOnCl ℂ f (ball c R)) (hw : w ∈ ball c R) :
    Real.circleAverageOn (fun z : sphere c |R| ↦ Checked.div
      (‖z.val - c‖ ^ 2 - ‖w - c‖ ^ 2) (‖z.val - w‖ ^ 2)
      ((norm_ne_zero_iff.mpr (isUnit_sub_of_mem_sphere_of_mem_ball hw z).ne_zero).isUnit.pow 2)
        • f z.val) = f w := by
  simpa only [poissonKernel_def] using hf.circleAverage_poissonKernel_smul hw

/-- Taking real parts commutes with the Herglotz–Riesz average of a real-valued function. -/
theorem re_circleAverage_herglotzRieszKernel_smul {g : ℂ → ℝ}
    (hg : CircleIntegrable g 0 |R|) (hw : w ∉ sphere 0 |R|) :
    (Real.circleAverageOn (fun z : sphere (0 : ℂ) |R| ↦
      herglotzRieszKernel 0 w ⟨z.val,
        mem_compl_singleton_iff.mpr (ne_of_mem_of_not_mem z.2 hw)⟩ • (g z.val : ℂ))).re =
      Real.circleAverageOn (fun z : sphere (0 : ℂ) |R| ↦
        (herglotzRieszKernel 0 w ⟨z.val,
          mem_compl_singleton_iff.mpr (ne_of_mem_of_not_mem z.2 hw)⟩).re • g z.val) := by
  let k (z : sphere (0 : ℂ) |R|) :=
    herglotzRieszKernel 0 w ⟨z.val, mem_compl_singleton_iff.mpr (ne_of_mem_of_not_mem z.2 hw)⟩
  have hk : Continuous k := (continuous_herglotzRieszKernel 0 w).comp
    (continuous_subtype_val.subtype_mk _)
  have hg' : CircleIntegrable (fun z ↦ (g z : ℂ)) 0 |R| := by
    simp only [CircleIntegrable, intervalIntegrable_iff] at hg ⊢
    exact Complex.ofRealCLM.integrable_comp hg
  have hi := intervalIntegrable_smul_on_sphere hg' hk
  change Complex.reCLM (Real.circleAverageOn (fun z ↦ k z • (g z.val : ℂ))) =
    Real.circleAverageOn (fun z ↦ (k z).re • g z.val)
  simp only [Real.circleAverageOn, map_smul]
  rw [← Complex.reCLM.intervalIntegral_comp_comm hi]
  simp only [Complex.reCLM_apply, smul_eq_mul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

private lemma circleAverageOn_const_smul {c : ℂ} {R : ℝ}
    (a : ℂ) (g : sphere c |R| → E) :
    Real.circleAverageOn (fun z ↦ a • g z) = a • Real.circleAverageOn g := by
  simp only [Real.circleAverageOn, intervalIntegral.integral_smul]
  rw [smul_comm]

private lemma circleAverageOn_herglotzRieszKernel_smul_eq_integral_sub
    (hf : CircleIntegrable f 0 |R|) (hw : w ∉ sphere 0 |R|) :
    Real.circleAverageOn (fun z : sphere (0 : ℂ) |R| ↦
      herglotzRieszKernel 0 w ⟨z.val,
        mem_compl_singleton_iff.mpr (ne_of_mem_of_not_mem z.2 hw)⟩ • f z.val) =
    (2 * (2 * π * I)⁻¹ : ℂ) • circleIntegralOn (fun z : sphere (0 : ℂ) (abs |R|) ↦
      Checked.inv (z.val - w) (sub_ne_zero.mpr (ne_of_mem_of_not_mem
        (by simpa only [abs_abs] using z.2 : z.val ∈ sphere 0 |R|) hw)).isUnit • f z.val) 0 |R| -
      Real.circleAverage f 0 R := by
  let S := sphere (0 : ℂ) |R|
  let k (z : S) := Checked.inv (z.val - w)
    (sub_ne_zero.mpr (ne_of_mem_of_not_mem z.2 hw)).isUnit
  let A (z : S) := z.val • k z • f z.val
  have hkc : Continuous k := ((continuous_subtype_val.sub continuous_const)).fun_inv₀
  have hai : IntervalIntegrable (fun θ : ℝ ↦
      A ⟨circleMap 0 |R| θ, circleMap_mem_sphere 0 (abs_nonneg R) θ⟩)
      volume 0 (2 * π) := by
    simpa only [A, Pi.mul_apply, mul_smul] using
      intervalIntegrable_smul_on_sphere hf (continuous_subtype_val.mul hkc)
  have hH (z : S) : herglotzRieszKernel 0 w ⟨z.val,
    mem_compl_singleton_iff.mpr (ne_of_mem_of_not_mem z.2 hw)⟩ =
      Checked.div (2 * z.val) (z.val - w)
        (sub_ne_zero.mpr (ne_of_mem_of_not_mem z.2 hw)).isUnit - 1 := by
    have hunit : IsUnit (z.val - w) := (sub_ne_zero.mpr (ne_of_mem_of_not_mem z.2 hw)).isUnit
    simp only [herglotzRieszKernel_def, sub_zero]
    field_simp
    ring
  have hpoint (z : S) : herglotzRieszKernel 0 w ⟨z.val,
    mem_compl_singleton_iff.mpr (ne_of_mem_of_not_mem z.2 hw)⟩ • f z.val =
      (2 : ℂ) • A z - f z.val := by
    simp only [hH, A, k, div_eq_mul_inv₀, sub_smul, one_smul, mul_smul]
  have hsplit :
      Real.circleAverageOn (fun z : S ↦ (2 : ℂ) • A z - f z.val) =
        (2 : ℂ) • Real.circleAverageOn A - Real.circleAverage f 0 R := by
    have hbi : IntervalIntegrable (fun θ : ℝ ↦ (2 : ℂ) •
        A ⟨circleMap 0 |R| θ, circleMap_mem_sphere 0 (abs_nonneg R) θ⟩) volume 0 (2 * π) :=
      hai.smul (2 : ℂ)
    rw [← circleAverageOn_restrict (R := R) (c := 0)]
    simp only [circleAverageOn]
    rw [intervalIntegral.integral_sub hbi hf, smul_sub, intervalIntegral.integral_smul, smul_comm]
  have hfun : (fun z : S ↦ herglotzRieszKernel 0 w ⟨z.val,
    mem_compl_singleton_iff.mpr (ne_of_mem_of_not_mem z.2 hw)⟩ •
      f z.val) = fun z : S ↦ (2 : ℂ) • A z - f z.val := funext hpoint
  rw [hfun, hsplit]
  have hA := circleAverageOn_sub_center_smul (fun z : S ↦ k z • f z.val)
  simp only [sub_zero] at hA
  rw [hA, smul_smul]

/-- The derivative in the pole parameter is the circle average with the squared denominator. -/
theorem hasDerivAt_circleAverage_herglotzRieszKernel_smul (hf : CircleIntegrable f 0 |R|)
    (hw : w ∉ sphere 0 |R|) :
    HasDerivAt (fun x : ((sphere (0 : ℂ) |R|)ᶜ : Set ℂ) ↦
      Real.circleAverageOn (fun z : sphere (0 : ℂ) |R| ↦
        herglotzRieszKernel 0 x.val ⟨z.val,
          mem_compl_singleton_iff.mpr (ne_of_mem_of_not_mem z.2 x.2)⟩ • f z.val))
      (Real.circleAverageOn (fun z : sphere (0 : ℂ) |R| ↦ Checked.div
        (2 * z.val) ((z.val - w) ^ 2)
        ((sub_ne_zero.mpr (ne_of_mem_of_not_mem z.2 hw)).isUnit.pow 2) • f z.val))
      ⟨w, hw⟩ Subtype.val := by
  let D : Set ℂ := (sphere (0 : ℂ) |R|)ᶜ
  let D' : Set ℂ := (sphere (0 : ℂ) (abs |R|))ᶜ
  let p (x : D) : D' := ⟨x.val, by simpa only [D', abs_abs] using x.2⟩
  have hp : Continuous p := continuous_subtype_val.subtype_mk _
  let G (x : D) := circleIntegralOn (fun z : sphere (0 : ℂ) (abs |R|) ↦
    Checked.inv (z.val - x.val)
      (sub_ne_zero.mpr (ne_of_mem_of_not_mem z.2 (p x).2)).isUnit • f z.val) 0 |R|
  let L := circleIntegralOn (fun z : sphere (0 : ℂ) (abs |R|) ↦
    Checked.zpow (z.val - w) (-2)
      (fun _ ↦ (sub_ne_zero.mpr (ne_of_mem_of_not_mem z.2 (p ⟨w, hw⟩).2)).isUnit) • f z.val) 0 |R|
  have hd : HasDerivAt G L (⟨w, hw⟩ : D) Subtype.val := by
    have h := hasDerivAt_circleIntegral_sub_inv_smul hf (p ⟨w, hw⟩).2
    apply hasDerivAt_iff_hasFDerivAt.mpr
    simpa only [HasFDerivAt, G, L, p, Function.comp_def] using
      h.hasFDerivAt.comp_tendsto p
        (hp.continuousAt.tendsto.prodMap (Filter.tendsto_pure_pure ..))
  let β : ℂ := 2 * (2 * π * I)⁻¹
  have hG :
      (fun x : D ↦ Real.circleAverageOn (fun z : sphere (0 : ℂ) |R| ↦
        herglotzRieszKernel 0 x.val ⟨z.val,
          mem_compl_singleton_iff.mpr (ne_of_mem_of_not_mem z.2 x.2)⟩ • f z.val)) =
      fun x : D ↦ β • G x - Real.circleAverage f 0 R := by
    funext x
    exact circleAverageOn_herglotzRieszKernel_smul_eq_integral_sub hf x.2
  have hL :
      Real.circleAverageOn (fun z : sphere (0 : ℂ) |R| ↦ Checked.div
        (2 * z.val) ((z.val - w) ^ 2)
        ((sub_ne_zero.mpr (ne_of_mem_of_not_mem z.2 hw)).isUnit.pow 2) • f z.val) = β • L := by
    simp_rw [div_eq_mul_inv₀, mul_smul]
    rw [circleAverageOn_const_smul]
    have hcenter := circleAverageOn_sub_center_smul (fun z : sphere (0 : ℂ) |R| ↦
      Checked.inv ((z.val - w) ^ 2)
        ((sub_ne_zero.mpr (ne_of_mem_of_not_mem z.2 hw)).isUnit.pow 2) • f z.val)
    simp only [sub_zero] at hcenter
    rw [hcenter, smul_smul]
    dsimp only [β, L]
    congr 2
    funext z
    have hu : IsUnit (z.val - w) :=
      (sub_ne_zero.mpr (ne_of_mem_of_not_mem z.2 (p ⟨w, hw⟩).2)).isUnit
    have hz : Checked.zpow (z.val - w) (-2) (fun _ ↦ hu) =
        Checked.inv ((z.val - w) ^ 2) (hu.pow 2) := by
      simpa only [zpow_ofNat₀] using zpow_neg₀ hu.ne_zero (2 : ℤ)
    simp only [hz]
  rw [hG, hL]
  simpa only [Pi.smul_apply, Pi.sub_apply, smul_apply, ContinuousLinearMap.toSpanSingleton_apply,
    one_smul] using
    ((hd.hasFDerivAt.const_smul β).sub_const (Real.circleAverage f 0 R)).hasDerivAt

/-- The Herglotz–Riesz average is differentiable off the integration circle. -/
theorem differentiableOn_circleAverage_herglotzRieszKernel_smul (hf : CircleIntegrable f 0 |R|) :
    DifferentiableOn ℂ
      (fun x : ((sphere (0 : ℂ) |R|)ᶜ : Set ℂ) ↦
        Real.circleAverageOn (fun z : sphere (0 : ℂ) |R| ↦
          herglotzRieszKernel 0 x.val ⟨z.val,
            mem_compl_singleton_iff.mpr (ne_of_mem_of_not_mem z.2 x.2)⟩ • f z.val))
      univ Subtype.val :=
  fun x _ ↦ (hasDerivAt_circleAverage_herglotzRieszKernel_smul hf x.2).hasFDerivAt
    |>.hasFDerivWithinAt.differentiableWithinAt

/-- The Herglotz–Riesz average is analytic off the integration circle. -/
theorem analyticOnNhd_circleAverage_herglotzRieszKernel_smul [CompleteSpace E]
    (hf : CircleIntegrable f 0 |R|) :
    AnalyticOnNhd ℂ
      (fun x : ((sphere (0 : ℂ) |R|)ᶜ : Set ℂ) ↦
        Real.circleAverageOn (fun z : sphere (0 : ℂ) |R| ↦
          herglotzRieszKernel 0 x.val ⟨z.val,
            mem_compl_singleton_iff.mpr (ne_of_mem_of_not_mem z.2 x.2)⟩ • f z.val))
      univ Subtype.val := by
  let D : Set ℂ := (sphere (0 : ℂ) |R|)ᶜ
  let g (x : D) := Real.circleAverageOn (fun z : sphere (0 : ℂ) |R| ↦
    herglotzRieszKernel 0 x.val ⟨z.val,
      mem_compl_singleton_iff.mpr (ne_of_mem_of_not_mem z.2 x.2)⟩ • f z.val)
  let G : ℂ → E := Function.extend (Subtype.val : D → ℂ) g 0
  have heq : (fun x : D ↦ G x.val) = g :=
    funext fun x ↦ Subtype.val_injective.extend_apply _ _ x
  have hOpen : IsOpen D := isClosed_sphere.isOpen_compl
  have hG : DifferentiableOn ℂ G D := by
    intro x hx
    have h := (hasDerivAt_circleAverage_herglotzRieszKernel_smul (f := f) hf hx).differentiableAt
    simpa only [heq, id_eq] using
      (DifferentiableAt.of_restrict (s := D) (x := (⟨x, hx⟩ : D)) (by rw [heq]; exact h)
        (hOpen.mem_nhds hx)).differentiableWithinAt
  intro x _
  change AnalyticAt ℂ g x Subtype.val
  rw [← heq]
  exact (hG.analyticAt (hOpen.mem_nhds x.2)).comp_domain (g := Subtype.val) (x := x)


end
