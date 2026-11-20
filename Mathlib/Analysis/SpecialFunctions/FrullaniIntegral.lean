/-
Copyright (c) 2026 Louis (Yiyang) Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Louis (Yiyang) Liu
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Frullani's integral

This file proves **Frullani's integral**: if `f : ℝ → E` is locally integrable on `(0, ∞)` with
`f x → L` as `x → 0⁺` and `f x → R` as `x → +∞`, and `0 < a` and `0 < b`, then
`∫ x in Ioi 0, x⁻¹ • (f (a * x) - f (b * x)) = log (b / a) • (L - R)`
(`Frullani.integral_Ioi_eq`), provided the integrand is integrable on `(0, ∞)`.

We also prove a limit form `Frullani.tendsto_intervalIntegral`, which does not require global
integrability of the integrand.
-/

public section

open Real Set Filter MeasureTheory intervalIntegral Metric

open scoped Topology Interval

namespace Frullani

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E}
         {a b c : ℝ} {L R : E}

/-- The integral with weight `1 / x` on the nonzero part of the interval. -/
noncomputable def integralInvSMul (f : ℝ → E) (a b : ℝ) : E :=
  integralSubtypeOn (fun x : ({0}ᶜ : Set ℝ) ↦ Checked.inv x.val (Ne.isUnit x.2) • f x.val) a b

private theorem exists_inv_extension :
    ∃ g : ℝ → ℝ, ∀ x (hx : x ≠ 0), g x = Checked.inv x hx.isUnit := by
  let g : ({0}ᶜ : Set ℝ) → ℝ := fun x ↦ Checked.inv x.val (Ne.isUnit x.2)
  exact ⟨Function.extend Subtype.val g 0, fun x hx ↦
    Subtype.val_injective.extend_apply g 0 ⟨x, hx⟩⟩

private theorem integral_inv_smul_eq_integral (f : ℝ → E) {g : ℝ → ℝ}
    (hg : ∀ x (hx : x ≠ 0), g x = Checked.inv x hx.isUnit) (a b : ℝ) :
    integralInvSMul f a b = ∫ x in a..b, g x • f x := by
  unfold integralInvSMul
  have heq : (fun x : ({0}ᶜ : Set ℝ) ↦ Checked.inv x.val (Ne.isUnit x.2) • f x.val) =
      (fun x : ({0}ᶜ : Set ℝ) ↦ g x.val • f x.val) := funext fun x ↦ by rw [hg x.val x.2]
  rw [heq]
  exact integral_subtypeOn_eq_integral (measurableSet_singleton (0 : ℝ)).compl
    (fun x : ℝ ↦ g x • f x) ((volume.restrict [[a, b]]).ae_ne 0)

private theorem pos_of_mem_uIcc (ha : 0 < a) (hb : 0 < b) {x : ℝ} (hx : x ∈ [[a, b]]) :
    0 < x := (lt_min ha hb).trans_le hx.1

private theorem continuousOn_inv_extension {g : ℝ → ℝ}
    (hg : ∀ x (hx : x ≠ 0), g x = Checked.inv x hx.isUnit) (ha : 0 < a) (hb : 0 < b) :
    ContinuousOn g [[a, b]] := by
  rw [continuousOn_iff_continuous_domRestrict]
  have heq : (fun x : [[a, b]] ↦ g x.val) =
      fun x : [[a, b]] ↦ Checked.inv x.val (pos_of_mem_uIcc ha hb x.2).ne'.isUnit :=
    funext fun x ↦ hg x.val (pos_of_mem_uIcc ha hb x.2).ne'
  change Continuous (fun x : [[a, b]] ↦ g x.val)
  rw [heq]
  exact continuous_subtype_val.fun_inv₀

lemma intervalIntegrable_inv_smul (hf : LocallyIntegrableOn f (Ioi 0)) (ha : 0 < a)
    (hb : 0 < b) : Integrable (fun x : [[a, b]] ↦
      Checked.inv x.val ((lt_min ha hb).trans_le x.2.1).ne'.isUnit • f x.val)
      (volume.comap Subtype.val) := by
  obtain ⟨g, hg⟩ := exists_inv_extension
  have hsub : uIcc a b ⊆ Ioi 0 := by simp [uIcc, Icc_subset_Ioi_iff, ha, hb]
  have hf_int := hf.integrableOn_compact_subset hsub isCompact_uIcc
  have hi := hf_int.continuousOn_smul (continuousOn_inv_extension hg ha hb) isCompact_uIcc
  exact ((integrableOn_iff_comap_subtypeVal measurableSet_uIcc).mp hi).congr <|
    Eventually.of_forall fun x ↦ by
      simp only [Function.comp_apply, hg x.val (pos_of_mem_uIcc ha hb x.2).ne']

lemma intervalIntegrable_inv_smul_comp_mul (hf : LocallyIntegrableOn f (Ioi 0)) (ha : 0 < a)
    (hb : 0 < b) (hc : 0 < c) :
    Integrable (fun x : [[a, b]] ↦
      Checked.inv x.val ((lt_min ha hb).trans_le x.2.1).ne'.isUnit • f (c * x.val))
      (volume.comap Subtype.val) := by
  obtain ⟨g, hg⟩ := exists_inv_extension
  have hf_cint : IntervalIntegrable f volume (c * a) (c * b) :=
    intervalIntegrable_iff.mpr
      ((hf.integrableOn_compact_subset (by simp [uIcc, Icc_subset_Ioi_iff, mul_pos hc ha,
        mul_pos hc hb]) isCompact_uIcc).mono_set uIoc_subset_uIcc)
  have hf_comp : IntervalIntegrable (fun x ↦ f (c * x)) volume a b := by
    have h := hf_cint.comp_mul_left (c := c) (hc := hc.ne'.isUnit) (by finiteness) (by finiteness)
    simpa only [mul_div_cancel_left₀] using h
  have hi := hf_comp.continuousOn_smul (continuousOn_inv_extension hg ha hb)
  apply Integrable.congr ((integrableOn_iff_comap_subtypeVal measurableSet_uIcc).mp
    ((intervalIntegrable_iff' (h := by finiteness)).mp hi))
  exact Eventually.of_forall fun x ↦ by
    simp only [Function.comp_apply, hg x.val (pos_of_mem_uIcc ha hb x.2).ne']

lemma integral_comp_mul_inv_smul {ε r : ℝ} (hc : c ≠ 0) :
    integralInvSMul (fun x ↦ f (c * x)) ε r = integralInvSMul f (c * ε) (c * r) := by
  obtain ⟨g, hg⟩ := exists_inv_extension
  rw [integral_inv_smul_eq_integral _ hg, integral_inv_smul_eq_integral _ hg]
  conv_rhs => rw [← smul_integral_comp_mul_left _ c, ← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr_ae_restrict
  filter_upwards [(volume.restrict (uIoc ε r)).ae_ne (0 : ℝ)] with x hx
  rw [hg x hx, hg (c * x) (mul_ne_zero hc hx), smul_smul]
  congr 1
  field_simp

private theorem intervalIntegrable_inv_extension_smul {g : ℝ → ℝ}
    (hg : ∀ x (hx : x ≠ 0), g x = Checked.inv x hx.isUnit) (ha : 0 < a) (hb : 0 < b)
    (h : Integrable (fun x : [[a, b]] ↦
      Checked.inv x.val (pos_of_mem_uIcc ha hb x.2).ne'.isUnit • f x.val)
      (volume.comap Subtype.val)) :
    IntervalIntegrable (fun x ↦ g x • f x) volume a b := by
  rw [intervalIntegrable_iff' (h := by finiteness),
    integrableOn_iff_comap_subtypeVal measurableSet_uIcc]
  exact h.congr (Eventually.of_forall fun x ↦ by
    simp only [Function.comp_apply, hg x.val (pos_of_mem_uIcc ha hb x.2).ne'])

variable [CompleteSpace E]

lemma norm_integral_inv_smul_sub_le (hf : LocallyIntegrableOn f (Ioi 0)) (ha : 0 < a)
    (hb : 0 < b) {V : E} {δ : ℝ} (hδ : 0 ≤ δ) (h : ∀ x ∈ uIoc a b, ‖f x - V‖ ≤ δ) :
    ‖integralInvSMul f a b - log (b / a) • V‖ ≤ δ * |log (b / a)| := by
  obtain ⟨g, hg⟩ := exists_inv_extension
  have hgc := continuousOn_inv_extension hg ha hb
  have hlog : ∫ x in a..b, g x = log (b / a) := by
    rw [← integral_subtype_eq_integral g]
    have heq : (fun x : [[a, b]] ↦ g x.val) =
        fun x : [[a, b]] ↦ Checked.inv x.val
          (ne_of_mem_of_not_mem x.2 (notMem_uIcc_of_lt ha hb)).isUnit :=
      funext fun x ↦ hg x.val (pos_of_mem_uIcc ha hb x.2).ne'
    rw [heq, integral_inv_of_pos ha hb]
  have hint_f := intervalIntegrable_inv_extension_smul hg ha hb
    (intervalIntegrable_inv_smul hf ha hb)
  have hint_V : IntervalIntegrable (fun x ↦ g x • V) volume a b :=
    (hgc.smul continuousOn_const).intervalIntegrable
  have hint_inv : IntervalIntegrable (fun x : ℝ ↦ g x * δ) volume a b :=
    (hgc.mul continuousOn_const).intervalIntegrable
  rw [integral_inv_smul_eq_integral _ hg]
  calc ‖(∫ x in a..b, g x • f x) - log (b / a) • V‖
    _ = ‖∫ x in a..b, g x • (f x - V)‖ := by
        congr 1
        have : log (b / a) • V = ∫ x in a..b, g x • V := by
          rw [intervalIntegral.integral_smul_const (f := g) (c := V), hlog]
        rw [this, ← integral_sub hint_f hint_V]
        congr 1
        funext x
        exact (smul_sub _ _ _).symm
    _ ≤ |∫ x in a..b, g x * δ| := by
        apply norm_integral_le_abs_of_norm_le
        · exact (ae_restrict_mem measurableSet_uIoc).mono fun x hx ↦ by
            have hx_pos : 0 < x :=
              lt_of_lt_of_le (lt_min ha hb) (uIoc_subset_uIcc hx).1
            rw [hg x hx_pos.ne', norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hx_pos)]
            exact mul_le_mul_of_nonneg_left (h x hx) (inv_nonneg.2 hx_pos.le)
        · exact hint_inv
    _ = δ * |log (b / a)| := by
        simp_rw [mul_comm, intervalIntegral.integral_const_mul, hlog]
        exact (abs_mul δ (log (b / a))).trans (by rw [abs_of_nonneg hδ])

lemma tendsto_integral_inv_smul_of_tendsto_uniform (hf : LocallyIntegrableOn f (Ioi 0)) (ha : 0 < a)
    (hb : 0 < b) {F : Filter ℝ} (hpos : ∀ᶠ t in F, 0 < t) {V : E}
    (huni : ∀ δ > 0, ∀ᶠ t in F, ∀ x ∈ uIoc (a * t) (b * t), ‖f x - V‖ ≤ δ) :
    Tendsto (fun t ↦ integralInvSMul f (a * t) (b * t)) F (𝓝 (log (b / a) • V)) := by
  rw [Metric.tendsto_nhds]
  intro δ hδ
  set C := |log (b / a)| with hC_def
  set δ' := δ / (C + 1)
  filter_upwards [hpos, huni δ' (by positivity)] with t ht_pos hbound
  have hlog_eq : log (b * t / (a * t)) = log (b / a) := by
    congr 1
    field
  calc dist (integralInvSMul f (a * t) (b * t)) (log (b / a) • V)
    _ = ‖integralInvSMul f (a * t) (b * t) - log (b / a) • V‖ := dist_eq_norm _ _
    _ = ‖integralInvSMul f (a * t) (b * t) - log (b * t / (a * t)) • V‖ := by rw [hlog_eq]
    _ ≤ δ' * |log (b * t / (a * t))| :=
        norm_integral_inv_smul_sub_le hf (by positivity) (by positivity) (by positivity) hbound
    _ = δ' * C := by rw [hlog_eq]
    _ = δ * (C / (C + 1)) := by ring
    _ < δ * 1 := mul_lt_mul_of_pos_left ((div_lt_one (by positivity)).2 (lt_add_one C)) hδ
    _ = δ := mul_one δ

lemma tendsto_integral_inv_smul_nhdsWithin (hf : LocallyIntegrableOn f (Ioi 0)) (ha : 0 < a)
    (hb : 0 < b) (hL : Tendsto f (𝓝[>] 0) (𝓝 L)) :
    Tendsto (fun ε ↦ integralInvSMul f (a * ε) (b * ε)) (𝓝[>] 0)
      (𝓝 (log (b / a) • L)) := by
  apply tendsto_integral_inv_smul_of_tendsto_uniform hf ha hb self_mem_nhdsWithin
  intro δ hδ
  have hev : ∀ᶠ x in 𝓝[>] (0 : ℝ), dist (f x) L < δ :=
    hL.eventually (ball_mem_nhds L hδ)
  rw [Filter.Eventually, mem_nhdsWithin_iff] at hev
  obtain ⟨η, hη, hη_sub⟩ := hev
  set M := max a b with hM_def
  have hM : 0 < M := lt_max_of_lt_left ha
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds (div_pos hη hM))] with t ht_pos ht_bound
  intro x hx
  have hx_pos : 0 < x := (lt_min (by positivity) (by positivity)).trans_le (uIoc_subset_uIcc hx).1
  have hx_lt_η : dist x 0 < η := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hx_pos]
    calc x
      _ ≤ max (a * t) (b * t) := (uIoc_subset_uIcc hx).2
      _ = M * t := by rw [hM_def, max_mul_of_nonneg _ _ ht_pos.le]
      _ < M * (η / M) := mul_lt_mul_of_pos_left ht_bound hM
      _ = η := mul_div_cancel₀ η (hb := hM.ne'.isUnit)
  have := hη_sub ⟨mem_ball.2 hx_lt_η, hx_pos⟩
  rw [mem_ofPred_eq, dist_eq_norm] at this
  exact le_of_lt this

/-- If `f → R` as `x → +∞` and `f` is locally integrable on `(0, ∞)`, then the weighted integral
`∫ x in a*r..b*r, x⁻¹ • f x` converges to `log(b/a) • R` as `r → +∞`. -/
lemma tendsto_integral_inv_smul_atTop (hf : LocallyIntegrableOn f (Ioi 0)) (ha : 0 < a) (hb : 0 < b)
    (hR : Tendsto f atTop (𝓝 R)) :
    Tendsto (fun r ↦ integralInvSMul f (a * r) (b * r)) atTop (𝓝 (log (b / a) • R)) := by
  apply tendsto_integral_inv_smul_of_tendsto_uniform hf ha hb
    (eventually_atTop.2 ⟨1, fun r hr ↦ zero_lt_one.trans_le hr⟩)
  intro δ hδ
  have hev : ∀ᶠ x in atTop, dist (f x) R < δ :=
    hR.eventually (ball_mem_nhds R hδ)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  have hm : 0 < min a b := lt_min ha hb
  filter_upwards [eventually_atTop.2 ⟨max 1 (N / min a b), fun r hr ↦ hr⟩] with t ht
  intro x hx
  have ht_pos : 0 < t := lt_of_lt_of_le one_pos ((le_max_left 1 _).trans ht)
  have hNx : N ≤ x :=
    calc N
      _ = min a b * (N / min a b) := by rw [← mul_div_assoc₀, mul_div_cancel_left₀]
      _ ≤ min a b * t :=
        mul_le_mul_of_nonneg_left ((le_max_right _ _).trans ht) hm.le
      _ = min (a * t) (b * t) := by rw [min_mul_of_nonneg _ _ ht_pos.le]
      _ ≤ x := (uIoc_subset_uIcc hx).1
  have hdist := hN x hNx
  rw [dist_eq_norm] at hdist
  exact le_of_lt hdist

/-- **Frullani's integral**, limit form, for functions valued in a complete normed space.
If `f` is locally integrable on `(0, ∞)` with `f x → L` as `x → 0⁺` and `f x → R` as `x → +∞`,
and `0 < a` and `0 < b`, then `∫ x in ε..r, x⁻¹ • (f (a * x) - f (b * x)) → log (b / a) • (L - R)`
as `ε → 0⁺` and `r → +∞`. -/
theorem tendsto_intervalIntegral (hf : LocallyIntegrableOn f (Ioi 0)) (ha : 0 < a) (hb : 0 < b)
    (hL : Tendsto f (𝓝[>] 0) (𝓝 L)) (hR : Tendsto f atTop (𝓝 R)) :
    Tendsto (fun p : ℝ × ℝ ↦ integralInvSMul (fun x ↦ f (a * x) - f (b * x)) p.1 p.2)
      ((𝓝[>] 0) ×ˢ atTop) (𝓝 (log (b / a) • (L - R))) := by
  obtain ⟨g, hg⟩ := exists_inv_extension
  let u := fun x ↦ g x • f x
  have hint {p q : ℝ} (hp : 0 < p) (hq : 0 < q) : IntervalIntegrable u volume p q :=
    intervalIntegrable_inv_extension_smul hg hp hq (intervalIntegrable_inv_smul hf hp hq)
  have hsplit {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r) :
      integralInvSMul (fun x ↦ f (a * x) - f (b * x)) ε r =
        integralInvSMul f (a * ε) (b * ε) - integralInvSMul f (a * r) (b * r) := by
    calc
      _ = integralInvSMul (fun x ↦ f (a * x)) ε r -
          integralInvSMul (fun x ↦ f (b * x)) ε r := by
        simp_rw [integral_inv_smul_eq_integral _ hg, smul_sub]
        exact integral_sub
          (intervalIntegrable_inv_extension_smul hg hε hr
            (intervalIntegrable_inv_smul_comp_mul hf hε hr ha))
          (intervalIntegrable_inv_extension_smul hg hε hr
            (intervalIntegrable_inv_smul_comp_mul hf hε hr hb))
      _ = integralInvSMul f (a * ε) (a * r) - integralInvSMul f (b * ε) (b * r) := by
        rw [integral_comp_mul_inv_smul ha.ne', integral_comp_mul_inv_smul hb.ne']
      _ = _ := by
        simp_rw [integral_inv_smul_eq_integral _ hg]
        exact integral_interval_sub_interval_comm
                 (hint (mul_pos ha hε) (mul_pos ha hr))
                 (hint (mul_pos hb hε) (mul_pos hb hr))
                 (hint (mul_pos ha hε) (mul_pos hb hε))
  have h_ev : (fun p : ℝ × ℝ ↦ integralInvSMul (fun x ↦ f (a * x) - f (b * x)) p.1 p.2)
      =ᶠ[(𝓝[>] 0) ×ˢ atTop]
        fun p ↦ integralInvSMul f (a * p.1) (b * p.1) -
          integralInvSMul f (a * p.2) (b * p.2) := by
    filter_upwards [prod_mem_prod (eventually_nhdsWithin_of_forall fun _ h ↦ h)
      (eventually_atTop.2 ⟨1, fun _ h ↦ lt_of_lt_of_le one_pos h⟩)] with ⟨ε, r⟩ ⟨hε, hr⟩
    exact hsplit hε hr
  rw [tendsto_congr' h_ev, show log (b / a) • (L - R) =
    log (b / a) • L - log (b / a) • R from smul_sub _ _ _]
  exact ((tendsto_integral_inv_smul_nhdsWithin hf ha hb hL).comp tendsto_fst).sub
    ((tendsto_integral_inv_smul_atTop hf ha hb hR).comp tendsto_snd)

/-- **Frullani's integral** for functions valued in a complete normed space.
If `f` is locally integrable on `(0, ∞)` with `f x → L` as `x → 0⁺` and `f x → R` as `x → +∞`,
`0 < a` and `0 < b`, and `x ↦ x⁻¹ • (f (a * x) - f (b * x))` is integrable on `(0, ∞)`, then
`∫ x in Ioi 0, x⁻¹ • (f (a * x) - f (b * x)) = log (b / a) • (L - R)`. -/
theorem integral_Ioi_eq (hf : LocallyIntegrableOn f (Ioi 0)) (ha : 0 < a) (hb : 0 < b)
    (hL : Tendsto f (𝓝[>] 0) (𝓝 L)) (hR : Tendsto f atTop (𝓝 R))
    (hint : Integrable (fun x : Ioi (0 : ℝ) ↦
      Checked.inv x.val x.2.ne'.isUnit • (f (a * x.val) - f (b * x.val)))
      (volume.comap Subtype.val)) :
    (∫ x : Ioi (0 : ℝ), Checked.inv x.val x.2.ne'.isUnit • (f (a * x.val) - f (b * x.val))
      ∂(volume.comap Subtype.val)) = log (b / a) • (L - R) := by
  obtain ⟨u, hu⟩ := exists_inv_extension
  let g (x : ℝ) := u x • (f (a * x) - f (b * x))
  have hfun : (fun x : Ioi (0 : ℝ) ↦
      Checked.inv x.val x.2.ne'.isUnit • (f (a * x.val) - f (b * x.val))) =
      fun x : Ioi (0 : ℝ) ↦ g x.val := by
    funext x
    exact congrArg (fun v : ℝ ↦ v • (f (a * x.val) - f (b * x.val)))
      (hu x.val (mem_Ioi.mp x.2).ne').symm
  rw [hfun, integral_subtype_comap measurableSet_Ioi g]
  rw [hfun] at hint
  have hg : IntegrableOn g (Ioi 0) :=
    (integrableOn_iff_comap_subtypeVal (f := g) (μ := volume) measurableSet_Ioi).mpr hint
  have h_lim := (tendsto_intervalIntegral hf ha hb hL hR).mono_left curry_le_prod
  simp_rw [integral_inv_smul_eq_integral _ hu] at h_lim
  apply tendsto_nhds_unique
    (hg.continuousWithinAt_Ici_primitive_Ioi.mono_left (nhdsWithin_mono 0 Ioi_subset_Ici_self))
  rw [tendsto_nhdsWithin_nhds]
  intro ε hε
  rw [Metric.tendsto_nhds] at h_lim
  specialize h_lim (ε / 2) (by positivity)
  rw [eventually_curry_iff, Filter.Eventually, mem_nhdsWithin_iff] at h_lim
  obtain ⟨δ, hδ_pos, hδ⟩ := h_lim
  simp_rw [subset_def, mem_inter_iff, mem_ball] at hδ
  refine ⟨δ, hδ_pos, ?_⟩
  intro x hx hdist
  specialize hδ x ⟨hdist, hx⟩
  rw [mem_ofPred] at hδ
  have hint' : IntegrableOn g (Ioi x) := hg.mono (by grind) (by simp)
  have htends := intervalIntegral_tendsto_integral_Ioi x hint' tendsto_id
  have hle := le_of_tendsto (htends.dist tendsto_const_nhds) (hδ.mono (fun _ hy ↦ hy.le))
  linarith

end Frullani
