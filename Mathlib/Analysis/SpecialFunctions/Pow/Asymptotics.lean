/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Sébastien Gouëzel,
  Rémy Degenne, David Loeffler
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Limits and asymptotics of power functions at `+∞`

This file contains results about the limiting behaviour of power functions at `+∞`. For convenience
some results on asymptotics as `x → 0` (those which are not just continuity statements) are also
located here.
-/

public section


noncomputable section

open Real NNReal ENNReal Filter Set

open scoped Topology

/-!
## Limits at `+∞`
-/


section Limits

open Real Filter

/-- The function `x ^ y` tends to `+∞` at `+∞` for any positive real `y`. -/
theorem tendsto_rpow_atTop {y : ℝ} (hy : 0 < y) : Tendsto (fun x : ℝ => x ^ y) atTop atTop := by
  refine (tendsto_exp_atTop.comp (tendsto_log_atTop.atTop_mul_const hy)).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact (Real.rpow_def_of_pos hx y).symm

theorem tendsto_rpow_neg_nhdsGT_zero {y : ℝ} (hr : y < 0) :
    Tendsto (fun (x : ℝ) ↦ x ^ y) (𝓝[>] 0) atTop := by
  refine (tendsto_exp_atTop.comp
    (tendsto_log_nhdsGT_zero.atBot_mul_const_of_neg hr)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (Real.rpow_def_of_pos hx y).symm

/-- The function `x ^ (-y)` tends to `0` at `+∞` for any positive real `y`. -/
theorem tendsto_rpow_neg_atTop {y : ℝ} (hy : 0 < y) :
    Tendsto (fun x : ℝ => x ^ (-y)) atTop (𝓝 0) := by
  refine (tendsto_exp_atBot.comp
    (tendsto_log_atTop.atTop_mul_const_of_neg (neg_neg_of_pos hy))).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact (Real.rpow_def_of_pos hx (-y)).symm

open Asymptotics in
lemma tendsto_rpow_atTop_of_base_lt_one (b : ℝ) (hb₀ : -1 < b) (hb₁ : b < 1) :
    Tendsto (b ^ · : ℝ → ℝ) atTop (𝓝 (0 : ℝ)) := by
  rcases lt_trichotomy b 0 with hb | rfl | hb
  case inl => -- b < 0
    simp_rw [Real.rpow_def_of_nonpos hb.le, hb.ne, ite_false]
    rw [← isLittleO_const_iff (c := (1 : ℝ)) one_ne_zero, (one_mul (1 : ℝ)).symm]
    refine IsLittleO.mul_isBigO ?exp ?cos
    case exp =>
      rw [isLittleO_const_iff one_ne_zero]
      refine tendsto_exp_atBot.comp <| (tendsto_const_mul_atBot_of_neg ?_).mpr tendsto_id
      rw [← log_neg_eq_log, log_neg_iff (by linarith)]
      linarith
    case cos =>
      rw [isBigO_iff]
      exact ⟨1, Eventually.of_forall fun x => by simp [Real.abs_cos_le_one]⟩
  case inr.inl => -- b = 0
    refine Tendsto.mono_right ?_ (Iff.mpr pure_le_nhds_iff rfl)
    rw [tendsto_pure]
    filter_upwards [eventually_ne_atTop 0] with _ hx
    simp [hx]
  case inr.inr => -- b > 0
    simp_rw [Real.rpow_def_of_pos hb]
    refine tendsto_exp_atBot.comp <| (tendsto_const_mul_atBot_of_neg ?_).mpr tendsto_id
    exact (log_neg_iff hb).mpr hb₁

lemma tendsto_rpow_atBot_of_base_lt_one (b : ℝ) (hb₀ : 0 < b) (hb₁ : b < 1) :
    Tendsto (b ^ · : ℝ → ℝ) atBot atTop := by
  simp_rw [Real.rpow_def_of_pos (by positivity : 0 < b)]
  refine tendsto_exp_atTop.comp <| (tendsto_const_mul_atTop_iff_neg <| tendsto_id (α := ℝ)).mpr ?_
  exact (log_neg_iff hb₀).mpr hb₁

lemma tendsto_rpow_atTop_of_base_gt_one (b : ℝ) (hb : 1 < b) :
    Tendsto (b ^ · : ℝ → ℝ) atTop atTop := by
  simp_rw [Real.rpow_def_of_pos (by positivity : 0 < b)]
  refine tendsto_exp_atTop.comp <| (tendsto_const_mul_atTop_iff_pos <| tendsto_id (α := ℝ)).mpr ?_
  exact log_pos hb

lemma tendsto_rpow_atBot_of_base_gt_one (b : ℝ) (hb : 1 < b) :
    Tendsto (b ^ · : ℝ → ℝ) atBot (𝓝 0) := by
  simp_rw [Real.rpow_def_of_pos (by positivity : 0 < b)]
  refine tendsto_exp_atBot.comp <| (tendsto_const_mul_atBot_of_pos ?_).mpr tendsto_id
  exact (log_pos_iff (by positivity)).mpr <| by aesop

/-- The function `x ^ (a / (b * x + c))` tends to `1` at `+∞`, for any real numbers `a`, `b`, and
`c` such that `b` is nonzero. -/
theorem tendsto_rpow_div_mul_add (a b c : ℝ) (hb : 0 ≠ b)
    {D : Type*} {l : Filter D} (x : D → ℝ) (hx : Tendsto x l atTop)
    {hden : ∀ t, IsUnit (b * x t + c)} :
    Tendsto (fun t ↦ x t ^ Checked.div a (b * x t + c) (hden t)) l (𝓝 1) := by
  have htheta : (fun t : ℝ ↦ b * t + c) =Θ[atTop] id :=
    ((Asymptotics.isTheta_refl id atTop).const_mul_left hb.symm).add_isLittleO
      (Asymptotics.isLittleO_const_id_atTop c)
  have hlog := (isLittleO_log_id_atTop.trans_isTheta htheta.symm).comp_tendsto hx
  have hquot := hlog.tendsto_div_nhds_zero (hg := hden)
  have hmul := (tendsto_const_nhds (x := a)).mul hquot
  simp only [mul_zero] at hmul
  have hlim := tendsto_exp_nhds_zero_nhds_one.comp hmul
  apply hlim.congr'
  filter_upwards [hx.eventually (eventually_gt_atTop (0 : ℝ))] with t ht
  rw [Real.rpow_def_of_pos ht]
  simp only [Function.comp_def, div_eq_mul_inv₀]
  congr 1
  ring

/-- The function `x ^ (1 / x)` tends to `1` at `+∞`. -/
theorem tendsto_rpow_div {D : Type*} {l : Filter D} (x : D → ℝ)
    (hx : Tendsto x l atTop) {hunit : ∀ t, IsUnit (x t)} :
    Tendsto (fun t ↦ x t ^ Checked.div 1 (x t) (hunit t)) l (𝓝 1) := by
  simpa only [one_mul, add_zero] using
    tendsto_rpow_div_mul_add 1 1 0 zero_ne_one x hx
      (hden := fun t ↦ by simpa only [one_mul, add_zero] using hunit t)

/-- The function `x ^ (-1 / x)` tends to `1` at `+∞`. -/
theorem tendsto_rpow_neg_div {D : Type*} {l : Filter D} (x : D → ℝ)
    (hx : Tendsto x l atTop) {hunit : ∀ t, IsUnit (x t)} :
    Tendsto (fun t ↦ x t ^ Checked.div (-1) (x t) (hunit t)) l (𝓝 1) := by
  simpa only [one_mul, add_zero] using
    tendsto_rpow_div_mul_add (-1) 1 0 zero_ne_one x hx
      (hden := fun t ↦ by simpa only [one_mul, add_zero] using hunit t)

private theorem tendsto_mul_sub_mul_log_atTop (s : ℝ) {b : ℝ} (hb : 0 < b) :
    Tendsto (fun x : ℝ ↦ b * x - s * log x) atTop atTop := by
  have hhalf : 0 < b / 2 := by positivity
  have hbound := (isLittleO_log_id_atTop.const_mul_left s).def hhalf
  refine tendsto_atTop_mono' atTop ?_
    ((tendsto_id : Tendsto (id : ℝ → ℝ) atTop atTop).const_mul_atTop hhalf)
  filter_upwards [hbound, eventually_ge_atTop (0 : ℝ)] with x hx hxpos
  simp only [id_eq, Real.norm_of_nonneg hxpos] at hx
  have := (le_abs_self (s * log x)).trans hx
  change b / 2 * x ≤ b * x - s * log x
  nlinarith

/-- The function `exp (b * x) / x ^ s` tends to `+∞` at `+∞`, on its actual
quotient domain, for any real `s` and `b > 0`. -/
theorem tendsto_exp_mul_div_rpow_atTop (s : ℝ) (b : ℝ) (hb : 0 < b)
    {D : Type*} {l : Filter D} (x : D → ℝ) (hx : Tendsto x l atTop)
    {hden : ∀ t, IsUnit (x t ^ s)} :
    Tendsto (fun t ↦ Checked.div (exp (b * x t)) (x t ^ s) (hden t)) l atTop := by
  refine (tendsto_exp_atTop.comp ((tendsto_mul_sub_mul_log_atTop s hb).comp hx)).congr' ?_
  filter_upwards [hx.eventually (eventually_gt_atTop (0 : ℝ))] with t ht
  simp only [Function.comp_def, Real.rpow_def_of_pos ht, Real.exp_sub, mul_comm s]

/-- The function `exp(x) / x ^ s` tends to `+∞` at `+∞` on its actual quotient domain. -/
theorem tendsto_exp_div_rpow_atTop (s : ℝ) {D : Type*} {l : Filter D}
    (x : D → ℝ) (hx : Tendsto x l atTop) {hden : ∀ t, IsUnit (x t ^ s)} :
    Tendsto (fun t ↦ Checked.div (exp (x t)) (x t ^ s) (hden t)) l atTop := by
  simpa only [one_mul] using tendsto_exp_mul_div_rpow_atTop s 1 one_pos x hx

/-- The function `x ^ s * exp (-b * x)` tends to `0` at `+∞`, for any real `s` and `b > 0`. -/
theorem tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (s : ℝ) (b : ℝ) (hb : 0 < b) :
    Tendsto (fun x : ℝ => x ^ s * exp (-b * x)) atTop (𝓝 0) := by
  have ht := tendsto_neg_atTop_atBot.comp (tendsto_mul_sub_mul_log_atTop s hb)
  refine (tendsto_exp_atBot.comp ht).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  simp only [Function.comp_def]
  rw [Real.rpow_def_of_pos hx, ← Real.exp_add]
  congr 1
  ring

nonrec theorem NNReal.tendsto_rpow_atTop {y : ℝ} (hy : 0 < y) :
    Tendsto (fun x : ℝ≥0 => x ^ y) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  obtain ⟨c, hc⟩ := tendsto_atTop_atTop.mp (tendsto_rpow_atTop hy) b
  use c.toNNReal
  intro a ha
  exact mod_cast hc a (Real.toNNReal_le_iff_le_coe.mp ha)

theorem ENNReal.tendsto_rpow_at_top {y : ℝ} (hy : 0 < y) :
    Tendsto (fun x : ℝ≥0∞ => x ^ y) (𝓝 ⊤) (𝓝 ⊤) := by
  rw [ENNReal.tendsto_nhds_top_iff_nnreal]
  intro x
  obtain ⟨c, _, hc⟩ :=
    (atTop_basis_Ioi.tendsto_iff atTop_basis_Ioi).mp (NNReal.tendsto_rpow_atTop hy) x trivial
  have hc' : Set.Ioi ↑c ∈ 𝓝 (⊤ : ℝ≥0∞) := Ioi_mem_nhds ENNReal.coe_lt_top
  filter_upwards [hc'] with a ha
  by_cases ha' : a = ⊤
  · simp [ha', hy]
  lift a to ℝ≥0 using ha'
  simp only [Set.mem_Ioi, coe_lt_coe] at ha hc
  rw [← ENNReal.coe_rpow_of_nonneg _ hy.le]
  exact mod_cast hc a ha

end Limits

/-!
## Asymptotic results: `IsBigO`, `IsLittleO` and `IsTheta`
-/


namespace Complex

section

variable {α : Type*} {l : Filter α} {f g : α → ℂ}

open Asymptotics

theorem isTheta_exp_arg_mul_im (hl : IsBoundedUnder (· ≤ ·) l fun x => |(g x).im|) :
    (fun x => Real.exp (arg (f x) * im (g x))) =Θ[l] fun _ => (1 : ℝ) := by
  rcases hl with ⟨b, hb⟩
  refine Real.isTheta_exp_comp_one.2 ⟨π * b, ?_⟩
  rw [eventually_map] at hb ⊢
  refine hb.mono fun x hx => ?_
  rw [abs_mul]
  exact mul_le_mul (abs_arg_le_pi _) hx (abs_nonneg _) Real.pi_pos.le

theorem isBigO_cpow_rpow (hl : IsBoundedUnder (· ≤ ·) l fun x => |(g x).im|) :
    (fun x => f x ^ g x) =O[l] fun x => ‖f x‖ ^ (g x).re :=
  calc
    (fun x => f x ^ g x) =O[l]
        (show α → ℝ from fun x => ‖f x‖ ^ (g x).re / Real.exp (arg (f x) * im (g x))) :=
      isBigO_of_le _ fun _ => (norm_cpow_le _ _).trans (le_abs_self _)
    _ =Θ[l] (show α → ℝ from fun x => ‖f x‖ ^ (g x).re / (1 : ℝ)) :=
      (isTheta_refl _ _).div (isTheta_exp_arg_mul_im hl)
        (hf₂ := fun x ↦ (Real.exp_ne_zero (arg (f x) * im (g x))).isUnit)
        (hg₂ := fun _ ↦ isUnit_one)
    _ =ᶠ[l] (show α → ℝ from fun x => ‖f x‖ ^ (g x).re) := by
      simp only [div_one₀, EventuallyEq.rfl]

theorem isTheta_cpow_rpow (hl_im : IsBoundedUnder (· ≤ ·) l fun x => |(g x).im|)
    (hl : ∀ᶠ x in l, f x = 0 → re (g x) = 0 → g x = 0) :
    (fun x => f x ^ g x) =Θ[l] fun x => ‖f x‖ ^ (g x).re :=
  calc
    (fun x => f x ^ g x) =Θ[l]
        (fun x => ‖f x‖ ^ (g x).re / Real.exp (arg (f x) * im (g x))) :=
      .of_norm_eventuallyEq <| hl.mono fun _ => norm_cpow_of_imp
    _ =Θ[l] fun x => ‖f x‖ ^ (g x).re / (1 : ℝ) :=
      (isTheta_refl _ _).div (isTheta_exp_arg_mul_im hl_im)
        (hf₂ := fun x ↦ (Real.exp_ne_zero (arg (f x) * im (g x))).isUnit)
        (hg₂ := fun _ ↦ isUnit_one)
    _ =ᶠ[l] (fun x => ‖f x‖ ^ (g x).re) := by
      simp only [div_one₀, EventuallyEq.rfl]

theorem isTheta_cpow_const_rpow {b : ℂ} (hl : b.re = 0 → b ≠ 0 → ∀ᶠ x in l, f x ≠ 0) :
    (fun x => f x ^ b) =Θ[l] fun x => ‖f x‖ ^ b.re :=
  isTheta_cpow_rpow isBoundedUnder_const <| by
    simpa only [eventually_imp_distrib_right, not_imp_not, Imp.swap (a := b.re = 0)] using hl

end

end Complex

open Real

namespace Asymptotics

variable {α : Type*} {r c : ℝ} {l : Filter α} {f g : α → ℝ}

theorem IsBigOWith.rpow (h : IsBigOWith c l f g) (hc : 0 ≤ c) (hr : 0 ≤ r) (hg : 0 ≤ᶠ[l] g) :
    IsBigOWith (c ^ r) l (fun x => f x ^ r) fun x => g x ^ r := by
  apply IsBigOWith.of_bound
  filter_upwards [hg, h.bound] with x hgx hx
  calc
    |f x ^ r| ≤ |f x| ^ r := abs_rpow_le_abs_rpow _ _
    _ ≤ (c * |g x|) ^ r := by gcongr; assumption
    _ = c ^ r * |g x ^ r| := by rw [mul_rpow hc (abs_nonneg _), abs_rpow_of_nonneg hgx]

theorem IsBigO.rpow (hr : 0 ≤ r) (hg : 0 ≤ᶠ[l] g) (h : f =O[l] g) :
    (fun x => f x ^ r) =O[l] fun x => g x ^ r :=
  let ⟨_, hc, h'⟩ := h.exists_nonneg
  (h'.rpow hc hr hg).isBigO

theorem IsTheta.rpow (hf : 0 ≤ᶠ[l] f) (hg : 0 ≤ᶠ[l] g) (h : f =Θ[l] g) :
    (fun x => f x ^ r) =Θ[l] fun x => g x ^ r := by
  by_cases hr : 0 ≤ r
  · exact ⟨h.1.rpow hr hg, h.2.rpow hr hf⟩
  have hr : r < 0 := lt_of_not_ge hr
  have reverse_bound {u v : α → ℝ} (hu : 0 ≤ᶠ[l] u) (hv : 0 ≤ᶠ[l] v)
      (huv : u =O[l] v) (hzero : ∀ᶠ x in l, u x = 0 ↔ v x = 0) :
      (fun x ↦ v x ^ r) =O[l] (fun x ↦ u x ^ r) := by
    obtain ⟨C, hC, hbound⟩ := huv.exists_pos
    refine IsBigO.of_bound (C ^ (-r)) ?_
    filter_upwards [hu, hv, hbound.bound, hzero] with x hux hvx hboundx hzerox
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hvx _),
      Real.norm_of_nonneg (Real.rpow_nonneg hux _)]
    by_cases hx : u x = 0
    · simp [hx, hzerox.mp hx, Real.zero_rpow hr.ne]
    have hup : 0 < u x := lt_of_le_of_ne hux (Ne.symm hx)
    rw [Real.norm_of_nonneg hux, Real.norm_of_nonneg hvx] at hboundx
    calc
      v x ^ r = C ^ (-r) * (C * v x) ^ r := by
        rw [Real.mul_rpow hC.le hvx, ← mul_assoc, ← Real.rpow_add hC]
        simp
      _ ≤ C ^ (-r) * u x ^ r :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hup hboundx hr.le)
          (Real.rpow_nonneg hC.le _)
  exact ⟨reverse_bound hg hf h.2 h.symm.eq_zero_iff,
    reverse_bound hf hg h.1 h.eq_zero_iff⟩

theorem IsLittleO.rpow (hr : 0 < r) (hg : 0 ≤ᶠ[l] g) (h : f =o[l] g) :
    (fun x => f x ^ r) =o[l] fun x => g x ^ r := by
  refine .of_isBigOWith fun c hc ↦ ?_
  have hC : 0 < c ^ r⁻¹ := Real.rpow_pos_of_pos hc _
  have hbound := (h.forall_isBigOWith hC).rpow hC.le hr.le hg
  rwa [← Real.rpow_mul hc.le, inv_mul_cancel₀, Real.rpow_one] at hbound

protected lemma IsBigO.sqrt (hfg : f =O[l] g) (hg : 0 ≤ᶠ[l] g) :
    (fun x ↦ √(f x)) =O[l] (fun x ↦ √(g x)) := by
  obtain ⟨C, hC, hbound⟩ := hfg.exists_nonneg
  refine IsBigO.of_bound √C ?_
  filter_upwards [hg, hbound.bound] with x hgx hx
  simp only [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  calc
    √(f x) ≤ √‖f x‖ := Real.sqrt_le_sqrt (le_abs_self _)
    _ ≤ √(C * ‖g x‖) := Real.sqrt_le_sqrt hx
    _ = √C * √(g x) := by rw [Real.sqrt_mul hC, Real.norm_of_nonneg hgx]

protected lemma IsLittleO.sqrt (hfg : f =o[l] g) (hg : 0 ≤ᶠ[l] g) :
    (fun x ↦ √(f x)) =o[l] (fun x ↦ √(g x)) := by
  refine .of_isBigOWith fun C hC ↦ .of_bound ?_
  filter_upwards [hg, hfg.def (sq_pos_of_pos hC)] with x hgx hx
  simp only [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  calc
    √(f x) ≤ √‖f x‖ := Real.sqrt_le_sqrt (le_abs_self _)
    _ ≤ √(C ^ 2 * ‖g x‖) := Real.sqrt_le_sqrt hx
    _ = C * √(g x) := by
      rw [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq hC.le, Real.norm_of_nonneg hgx]

protected lemma IsTheta.sqrt (hfg : f =Θ[l] g) (hf : 0 ≤ᶠ[l] f) (hg : 0 ≤ᶠ[l] g) :
    (Real.sqrt <| f ·) =Θ[l] (Real.sqrt <| g ·) :=
  ⟨hfg.1.sqrt hg, hfg.2.sqrt hf⟩

theorem isBigO_atTop_natCast_rpow_of_tendsto_div_rpow {𝕜 : Type*} [RCLike 𝕜] {g : ℕ → 𝕜}
    {a : 𝕜} {r : ℝ}
    (hlim : Tendsto (fun n : {n : ℕ // (n : ℝ) ^ r ≠ 0} ↦
      Checked.div (g n) ((n : ℝ) ^ r : ℝ)
        (n.2.isUnit.map (algebraMap ℝ 𝕜))) (comap Subtype.val atTop) (𝓝 a)) :
    g =O[atTop] fun n ↦ (n : ℝ) ^ r := by
  refine (isBigO_of_div_tendsto_nhds ?_ ‖a‖ ?_).of_norm_left
  · filter_upwards [eventually_ne_atTop 0] with _ h
    simp [Real.rpow_eq_zero_iff_of_nonneg, h]
  · exact hlim.norm.congr fun n ↦ by simp [abs_of_nonneg, show 0 ≤ (n : ℝ) ^ r by positivity]

variable {E : Type*} [SeminormedRing E] (a b c : ℝ)

theorem IsBigO.mul_atTop_rpow_of_isBigO_rpow {f g : ℝ → E}
    (hf : f =O[atTop] fun t ↦ (t : ℝ) ^ a) (hg : g =O[atTop] fun t ↦ (t : ℝ) ^ b)
    (h : a + b ≤ c) :
    (f * g) =O[atTop] fun t ↦ (t : ℝ) ^ c := by
  refine (hf.mul hg).trans (Eventually.isBigO ?_)
  filter_upwards [eventually_ge_atTop 1] with t ht
  rw [← Real.rpow_add (zero_lt_one.trans_le ht), Real.norm_of_nonneg (Real.rpow_nonneg
    (zero_le_one.trans ht) (a + b))]
  exact Real.rpow_le_rpow_of_exponent_le ht h

theorem IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow {f g : ℕ → E}
    (hf : f =O[atTop] fun n ↦ (n : ℝ) ^ a) (hg : g =O[atTop] fun n ↦ (n : ℝ) ^ b)
    (h : a + b ≤ c) :
    (f * g) =O[atTop] fun n ↦ (n : ℝ) ^ c := by
  refine (hf.mul hg).trans (Eventually.isBigO ?_)
  filter_upwards [eventually_ge_atTop 1] with t ht
  replace ht : 1 ≤ (t : ℝ) := Nat.one_le_cast.mpr ht
  rw [← Real.rpow_add (zero_lt_one.trans_le ht), Real.norm_of_nonneg (Real.rpow_nonneg
    (zero_le_one.trans ht) (a + b))]
  exact Real.rpow_le_rpow_of_exponent_le ht h

/-- If `a ≤ b`, then `x^b = O(x^a)` as `x → 0`, `x ≥ 0`, unless `b = 0` and `a ≠ 0`. -/
theorem IsBigO.rpow_rpow_nhdsGE_zero_of_le_of_imp {a b : ℝ} (h : a ≤ b) (himp : b = 0 → a = 0) :
    (· ^ b : ℝ → ℝ) =O[𝓝[≥] 0] (· ^ a) :=
  .of_bound' <| mem_of_superset (Icc_mem_nhdsGE one_pos) fun x hx ↦ by
    simpa [Real.abs_rpow_of_nonneg hx.1, abs_of_nonneg hx.1]
     using Real.rpow_le_rpow_of_exponent_ge_of_imp hx.1 hx.2 h fun _ ↦ himp

/-- If `a ≤ b`, `b ≠ 0`, then `x^b = O(x^a)` as `x → 0`, `x ≥ 0`. -/
theorem IsBigO.rpow_rpow_nhdsGE_zero_of_le {a b : ℝ} (h : a ≤ b) (hb : b ≠ 0) :
    (· ^ b : ℝ → ℝ) =O[𝓝[≥] 0] (· ^ a) :=
  .rpow_rpow_nhdsGE_zero_of_le_of_imp h (absurd · hb)

/-- If `a ≤ 1`, then `x = O(x ^ a)` as `x → 0`, `x ≥ 0`. -/
theorem IsBigO.id_rpow_of_le_one {a : ℝ} (ha : a ≤ 1) :
    (id : ℝ → ℝ) =O[𝓝[≥] 0] (· ^ a) := by
  simpa using! rpow_rpow_nhdsGE_zero_of_le ha (by simp)

end Asymptotics

open Asymptotics

/-- `x ^ s = o(exp(b * x))` as `x → ∞` for any real `s` and positive `b`. -/
theorem isLittleO_rpow_exp_pos_mul_atTop (s : ℝ) {b : ℝ} (hb : 0 < b) :
    (fun x : ℝ => x ^ s) =o[atTop] fun x => exp (b * x) :=
  isLittleO_of_tendsto (fun _ h => absurd h (exp_pos _).ne') <| by
    simpa only [Function.comp_def, div_eq_mul_inv₀, exp_neg, neg_mul] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero s b hb).comp tendsto_comap

/-- `x ^ k = o(exp(b * x))` as `x → ∞` for any integer `k` and positive `b`. -/
theorem isLittleO_zpow_exp_pos_mul_atTop (k : ℤ) {b : ℝ} (hb : 0 < b)
    {D : Type*} {l : Filter D} (x : D → ℝ) (hx : Tendsto x l atTop)
    {hpower : ∀ t, k < 0 → IsUnit (x t)} :
    (fun t ↦ Checked.zpow (x t) k (hpower t)) =o[l] fun t ↦ exp (b * x t) := by
  refine ((isLittleO_rpow_exp_pos_mul_atTop (k : ℝ) hb).comp_tendsto hx).congr' ?_ .rfl
  filter_upwards [hx.eventually (eventually_gt_atTop (0 : ℝ))] with t ht
  simp only [Function.comp_def]
  cases k with
  | ofNat n =>
    simp only [Int.ofNat_eq_natCast, Int.cast_natCast, Real.rpow_natCast, zpow_natCast₀]
  | negSucc n =>
    rw [zpow_negSucc₀]
    simp only [← Real.rpow_natCast, Real.rpow_def_of_pos ht, ← Real.exp_neg]
    congr 1
    push_cast
    ring

/-- `x ^ k = o(exp(b * x))` as `x → ∞` for any natural `k` and positive `b`. -/
theorem isLittleO_pow_exp_pos_mul_atTop (k : ℕ) {b : ℝ} (hb : 0 < b) :
    (fun x : ℝ => x ^ k) =o[atTop] fun x => exp (b * x) := by
  simpa only [Real.rpow_natCast] using isLittleO_rpow_exp_pos_mul_atTop (k : ℝ) hb

/-- `x ^ s = o(exp x)` as `x → ∞` for any real `s`. -/
theorem isLittleO_rpow_exp_atTop (s : ℝ) : (fun x : ℝ => x ^ s) =o[atTop] exp := by
  simpa only [one_mul] using isLittleO_rpow_exp_pos_mul_atTop s one_pos

/-- `exp (-a * x) = o(x ^ s)` as `x → ∞`, for any positive `a` and real `s`. -/
theorem isLittleO_exp_neg_mul_rpow_atTop {a : ℝ} (ha : 0 < a) (b : ℝ) :
    IsLittleO atTop (fun x : ℝ => exp (-a * x)) fun x : ℝ => x ^ b := by
  apply isLittleO_of_tendsto'
  · refine (eventually_gt_atTop 0).mono fun t ht h => ?_
    rw [rpow_eq_zero_iff_of_nonneg ht.le] at h
    exact (ht.ne' h.1).elim
  · refine ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (-b) a ha).comp
      tendsto_comap).congr' ?_
    filter_upwards [tendsto_comap.eventually (eventually_gt_atTop (0 : ℝ))] with t ht
    simp only [Function.comp_def, Real.rpow_def_of_pos ht, div_eq_mul_inv₀, ← Real.exp_neg]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring

theorem isLittleO_exp_mul_rpow_of_lt (k : ℝ) {a b : ℝ} (ha' : a < b) :
    (fun t ↦ Real.exp (a * t) * t ^ k) =o[atTop] fun t ↦ Real.exp (b * t) := by
  refine (isLittleO_of_tendsto (fun _ h ↦ (Real.exp_ne_zero _ h).elim) ?_)
  simp_rw [← div_mul_eq_mul_div₀, ← Real.exp_sub, ← sub_mul, ← neg_sub b a,
    mul_comm _ (_ ^ k)]
  exact (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero _ _ (sub_pos.mpr ha')).comp tendsto_comap

theorem isLittleO_log_rpow_atTop {r : ℝ} (hr : 0 < r) : log =o[atTop] fun x => x ^ r :=
  calc
    log =O[atTop] fun x => r * log x := isBigO_self_const_mul hr.ne' _ _
    _ =ᶠ[atTop] fun x => log (x ^ r) :=
      ((eventually_gt_atTop 0).mono fun _ hx => (log_rpow hx _).symm)
    _ =o[atTop] fun x => x ^ r := isLittleO_log_id_atTop.comp_tendsto (tendsto_rpow_atTop hr)

theorem isLittleO_log_rpow_rpow_atTop {s : ℝ} (r : ℝ) (hs : 0 < s) :
    (fun x => log x ^ r) =o[atTop] fun x => x ^ s :=
  let r' := max r 1
  have hr : 0 < r' := lt_max_iff.2 <| Or.inr one_pos
  have H : 0 < s / r' := div_pos hs hr
  calc
    (fun x => log x ^ r) =O[atTop] fun x => log x ^ r' :=
      .of_norm_eventuallyLE <| by
        filter_upwards [tendsto_log_atTop.eventually_ge_atTop 1] with x hx
        rw [Real.norm_of_nonneg (by positivity)]
        gcongr
        exact le_max_left _ _
    _ =o[atTop] fun x => (x ^ (s / r')) ^ r' :=
      ((isLittleO_log_rpow_atTop H).rpow hr <|
        (_root_.tendsto_rpow_atTop H).eventually <| eventually_ge_atTop 0)
    _ =ᶠ[atTop] fun x => x ^ s :=
      (eventually_ge_atTop 0).mono fun x hx ↦ by simp only [← rpow_mul hx, div_mul_cancel₀]

theorem isLittleO_abs_log_rpow_rpow_nhdsGT_zero {s : ℝ} (r : ℝ) (hs : s < 0) :
    (fun x => |log x| ^ r) =o[𝓝[>] 0] fun x => x ^ s := by
  have ht := tendsto_neg_atBot_atTop.comp tendsto_log_nhdsGT_zero
  refine ((isLittleO_rpow_exp_pos_mul_atTop r (neg_pos.2 hs)).comp_tendsto ht).congr' ?_ ?_
  · filter_upwards [Icc_mem_nhdsGT one_pos] with x hx
    simp only [Function.comp_def, abs_of_nonpos (log_nonpos hx.1 hx.2)]
  · filter_upwards [self_mem_nhdsWithin] with x hx
    rw [Real.rpow_def_of_pos hx]
    simp only [Function.comp_def]
    congr 1
    ring

theorem isLittleO_log_rpow_nhdsGT_zero {r : ℝ} (hr : r < 0) : log =o[𝓝[>] 0] fun x => x ^ r :=
  (isLittleO_abs_log_rpow_rpow_nhdsGT_zero 1 hr).neg_left.congr'
    (mem_of_superset (Icc_mem_nhdsGT one_pos) fun x hx => by
      simp [abs_of_nonpos (log_nonpos hx.1 hx.2)])
    .rfl

theorem tendsto_log_div_rpow_nhdsGT_zero {r : ℝ} (hr : r < 0) :
    Tendsto (fun x : {x : ℝ // x ^ r ≠ 0} ↦
      Checked.div (log x) ((x : ℝ) ^ r) x.2.isUnit)
      (comap Subtype.val (𝓝[>] 0)) (𝓝 0) :=
  ((isLittleO_log_rpow_nhdsGT_zero hr).comp_tendsto tendsto_comap).tendsto_div_nhds_zero

theorem tendsto_log_mul_rpow_nhdsGT_zero {r : ℝ} (hr : 0 < r) :
    Tendsto (fun x => log x * x ^ r) (𝓝[>] 0) (𝓝 0) := by
  have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 r hr).comp
    (tendsto_neg_atBot_atTop.comp tendsto_log_nhdsGT_zero)
  have hneg := ht.neg
  simp only [neg_zero] at hneg
  apply hneg.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [Real.rpow_def_of_pos hx]
  simp only [Function.comp_def, Real.rpow_one, neg_mul, neg_neg]
  rw [mul_comm r]
  congr 2; ring

lemma tendsto_log_mul_self_nhdsLT_zero : Filter.Tendsto (fun x ↦ log x * x) (𝓝[<] 0) (𝓝 0) := by
  have h := tendsto_log_mul_rpow_nhdsGT_zero zero_lt_one
  simp only [Real.rpow_one] at h
  have h_eq : ∀ x ∈ Set.Iio 0, (-(fun x ↦ log x * x) ∘ (fun x ↦ |x|)) x = log x * x := by
    simp only [Set.mem_Iio, Pi.neg_apply, Function.comp_apply, log_abs]
    intro x hx
    simp only [abs_of_nonpos hx.le, mul_neg, neg_neg]
  refine tendsto_nhdsWithin_congr h_eq ?_
  nth_rewrite 3 [← neg_zero]
  refine (h.comp (tendsto_abs_nhdsNE_zero.mono_left ?_)).neg
  refine nhdsWithin_mono 0 (fun x hx ↦ ?_)
  push _ ∈ _ at hx
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff, hx.ne, not_false_eq_true]
