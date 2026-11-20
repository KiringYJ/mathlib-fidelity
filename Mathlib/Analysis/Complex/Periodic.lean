/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
public import Mathlib.Order.Filter.ZeroAndBoundedAtFilter

/-!
# Periodic holomorphic functions

We show that if `f : ℂ → ℂ` satisfies `f (z + h) = f z`, for some nonzero real `h`, then there is a
function `F` such that `f z = F (exp (2 * π * I * z / h))` for all `z`; and if `f` is holomorphic
at some `z`, then `F` is holomorphic at `exp (2 * π * I * z / h)`.

We also show (using Riemann's removable singularity theorem) that if `f` is holomorphic and bounded
for all sufficiently large `im z`, then `F` extends to a holomorphic function on a neighbourhood of
`0`. As a consequence, if `f` tends to zero as `im z → ∞`, then in fact it decays *exponentially*
to zero. These results are important in the theory of modular forms.
-/

@[expose] public section

open Complex Filter Asymptotics

open scoped Real Topology

noncomputable section

local notation "I∞" => comap im atTop

variable (h : ℝ)

namespace Function.Periodic

/-- The parameter for q-expansions with nonzero width `h`. -/
def qParam (z : ℂ) (hh : h ≠ 0 := by checked_nonzero) : ℂ :=
  exp (Checked.div (2 * π * I * z) (h : ℂ) (ofReal_ne_zero.mpr hh).isUnit)

/-- The logarithmic right inverse of `qParam h` on the nonzero complex numbers. -/
def invQParam (q : ℂ) (_hh : h ≠ 0 := by checked_nonzero)
    (_hq : q ≠ 0 := by checked_nonzero) : ℂ :=
  Checked.div (h : ℂ) (2 * π * I) two_pi_I_ne_zero.isUnit * log q

local notation "𝕢" => @qParam
local notation "𝓝₀" => (comap (Subtype.val : {q : ℂ // q ≠ 0} → ℂ) (𝓝 0))

private lemma map_cuspSubtype_nhds :
    Filter.map (Subtype.val : {q : ℂ // q ≠ 0} → ℂ) 𝓝₀ = 𝓝[≠] 0 := by
  change Filter.map (Subtype.val : ({0}ᶜ : Set ℂ) → ℂ)
      (comap Subtype.val (𝓝 0)) = 𝓝[≠] 0
  rw [map_comap_setCoe_val]
  rfl

private lemma tendsto_cuspSubtype_val :
    Tendsto (Subtype.val : {q : ℂ // q ≠ 0} → ℂ) 𝓝₀ (𝓝[≠] 0) :=
  map_cuspSubtype_nhds.le

lemma neBot_cuspSubtype_nhds : NeBot 𝓝₀ :=
  (map_neBot_iff (Subtype.val : {q : ℂ // q ≠ 0} → ℂ)).mp
    (map_cuspSubtype_nhds.symm ▸ inferInstance)

attribute [local instance] neBot_cuspSubtype_nhds

section qParam

theorem norm_qParam (z : ℂ) (hh : h ≠ 0 := by checked_nonzero) :
    ‖𝕢 h z hh‖ = Real.exp (Checked.div (-2 * π * im z) h hh.isUnit) := by
  simp only [qParam, norm_exp, div_ofReal_re, mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im,
    mul_zero, sub_zero, I_re, mul_im, zero_mul, add_zero, I_im, mul_one, sub_self, zero_sub,
    neg_mul]

theorem im_invQParam (q : ℂ) (hh : h ≠ 0 := by checked_nonzero) (hq : q ≠ 0 := by checked_nonzero) :
    im (invQParam h q hh hq) = -h / (2 * π) * Real.log ‖q‖ := by
  have hu : IsUnit (2 * π : ℝ) := Real.two_pi_pos.ne'.isUnit
  have huC : IsUnit (2 * π : ℂ) := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using
      (ofReal_ne_zero.mpr Real.two_pi_pos.ne').isUnit
  have hscale : Checked.div (h : ℂ) (2 * π * I) two_pi_I_ne_zero.isUnit =
      -((h / (2 * π) : ℝ) : ℂ) * I := by
    rw [← div_div₀ (hb := huC) (hc := I_ne_zero.isUnit), Complex.div_I]
    simp only [Complex.ofReal_div _ _ (hs := hu), Complex.ofReal_mul, Complex.ofReal_ofNat, neg_mul]
  simp only [invQParam, hscale, neg_div₀, neg_re, neg_im, mul_re, mul_im, ofReal_re, ofReal_im,
    I_re, I_im, mul_zero, neg_zero, zero_mul, mul_one, sub_zero, add_zero, zero_add, log_re]

variable {h}

theorem qParam_right_inv (hh : h ≠ 0) {q : ℂ} (hq : q ≠ 0) :
    𝕢 h (invQParam h q hh hq) hh = q := by
  have hu := (ofReal_ne_zero.mpr hh).isUnit
  unfold qParam invQParam
  rw [show (2 * π * I * ((h : ℂ) / (2 * π * I) * log q)) / h = log q by
    field_simp, exp_log hq]

theorem qParam_left_inv_mod_period (hh : h ≠ 0) (z : ℂ) :
    ∃ m : ℤ, invQParam h (𝕢 h z hh) hh (exp_ne_zero _) = z + m * h := by
  have hu := (ofReal_ne_zero.mpr hh).isUnit
  dsimp only [qParam, invQParam]
  obtain ⟨m, hm⟩ := log_exp_exists (2 * ↑π * I * z / ↑h)
  refine ⟨m, ?_⟩
  rw [hm]
  field_simp

theorem norm_qParam_lt_iff (hh : 0 < h) (A : ℝ) (z : ℂ) :
    ‖qParam h z hh.ne'‖ < Real.exp (Checked.div (-2 * π * A) h hh.ne'.isUnit) ↔ A < im z := by
  rw [norm_qParam h z hh.ne', Real.exp_lt_exp, div_lt_div_iff_of_pos_right hh,
    mul_lt_mul_left_of_neg]
  simpa using Real.pi_pos

theorem norm_qParam_lt_one (hh : 0 < h) {z : ℂ} (hz : 0 < im z) : ‖𝕢 h z hh.ne'‖ < 1 := by
  simpa using (norm_qParam_lt_iff hh 0 z).mpr hz

lemma qParam_ne_zero (z : ℂ) (hh : h ≠ 0 := by checked_nonzero) : 𝕢 h z hh ≠ 0 :=
  exp_ne_zero _

@[fun_prop]
lemma continuous_qParam (hh : h ≠ 0) : Continuous (fun z ↦ 𝕢 h z hh) := by
  unfold qParam
  fun_prop

@[fun_prop]
lemma differentiable_qParam (hh : h ≠ 0) : Differentiable ℂ (fun z ↦ 𝕢 h z hh) := by
  unfold qParam
  fun_prop

@[fun_prop]
lemma contDiff_qParam (m : WithTop ℕ∞) (hh : h ≠ 0) : ContDiff ℂ m (fun z ↦ 𝕢 h z hh) := by
  unfold qParam
  fun_prop

lemma hasStrictDerivAt_qParam (hh : h ≠ 0) (z : ℂ) :
    HasStrictDerivAt (fun w ↦ 𝕢 h w hh)
      (𝕢 h z hh * Checked.div (2 * π * I) (h : ℂ) (ofReal_ne_zero.mpr hh).isUnit) z := by
  simpa only [qParam, id_eq, mul_one] using
    (((hasStrictDerivAt_id z).const_mul (2 * π * I : ℂ)).div_const (h : ℂ)
      (hd := (ofReal_ne_zero.mpr hh).isUnit)).cexp

theorem qParam_tendsto (hh : 0 < h) : Tendsto (fun z ↦ qParam h z hh.ne') I∞ (𝓝[≠] 0) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
    (.of_forall fun z ↦ qParam_ne_zero z hh.ne')
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp only [norm_qParam]
  apply (tendsto_comap'_iff (m := fun y ↦ Real.exp (Checked.div (-2 * π * y) h hh.ne'.isUnit))
    (range_im ▸ univ_mem)).mpr
  refine Real.tendsto_exp_atBot.comp (.atBot_div_const hh (tendsto_id.const_mul_atTop_of_neg ?_))
  simpa using Real.pi_pos

theorem invQParam_tendsto (hh : 0 < h) :
    Tendsto (fun q : {q : ℂ // q ≠ 0} ↦ invQParam h q.val hh.ne' q.property) 𝓝₀ I∞ := by
  simp only [tendsto_comap_iff, comp_def, im_invQParam]
  apply Tendsto.const_mul_atBot_of_neg (div_neg_of_neg_of_pos (neg_lt_zero.mpr hh) Real.two_pi_pos)
  exact Real.tendsto_log_nhdsGT_zero.comp
    (tendsto_norm_nhdsNE_zero.comp tendsto_cuspSubtype_val)

end qParam

section PeriodicOnℂ

variable (h : ℝ) (f : ℂ → ℂ)

/-- The function `q ↦ f (invQParam h q)` on nonzero arguments, with its cusp value given by
the chosen limit along nonzero complex numbers. -/
def cuspFunction (hh : h ≠ 0 := by checked_nonzero) (q : ℂ) : ℂ :=
  if hq : q = 0 then
    limUnder 𝓝₀ (fun r : {r : ℂ // r ≠ 0} ↦ f (invQParam h r.val hh r.property))
  else f (invQParam h q hh hq)

theorem cuspFunction_eq_of_nonzero (hh : h ≠ 0) {q : ℂ} (hq : q ≠ 0) :
    cuspFunction h f hh q = f (invQParam h q hh hq) := by
  simp only [cuspFunction, dite_eq_right hq]

theorem cuspFunction_zero_eq_limUnder_nhds_ne (hh : h ≠ 0) :
    cuspFunction h f hh 0 = limUnder (𝓝[≠] 0) (cuspFunction h f hh) := by
  simp only [cuspFunction, dite_true, ← map_cuspSubtype_nhds, limUnder, Filter.map_map]
  refine congrArg lim (Filter.map_congr (.of_forall fun r ↦ ?_))
  exact (cuspFunction_eq_of_nonzero h f hh r.property).symm

variable {f h}

theorem eq_cuspFunction (hh : h ≠ 0) (hf : Periodic f h) (z : ℂ) :
    cuspFunction h f hh (𝕢 h z hh) = f z := by
  obtain ⟨m, hm⟩ := qParam_left_inv_mod_period hh z
  rw [cuspFunction_eq_of_nonzero h f hh (qParam_ne_zero z hh), hm]
  exact hf.int_mul m z

lemma tendsto_nhds_zero {f : ℂ → ℂ} {hh : h ≠ 0} (hcts : ContinuousAt (cuspFunction h f hh) 0) :
    Tendsto (fun x : {q : ℂ // q ≠ 0} ↦ f (invQParam h x.val hh x.property))
      𝓝₀ (𝓝 (cuspFunction h f hh 0)) := by
  refine ((tendsto_nhdsWithin_of_tendsto_nhds hcts.tendsto).comp
    tendsto_cuspSubtype_val).congr fun x ↦ ?_
  exact cuspFunction_eq_of_nonzero h f hh x.property

end PeriodicOnℂ

section HoloOnC

variable {h : ℝ} {f : ℂ → ℂ}

/-- The cusp function is differentiable at the q-parameters of differentiability points of
the periodic function. -/
theorem differentiableAt_cuspFunction (hh : h ≠ 0) (hf : Periodic f h)
    {z : ℂ} (hol_z : DifferentiableAt ℂ f z) :
    DifferentiableAt ℂ (cuspFunction h f hh) (𝕢 h z hh) := by
  let Q := fun w ↦ 𝕢 h w hh
  let q := Q z
  have hu := (ofReal_ne_zero.mpr hh).isUnit
  have qdiff : HasStrictDerivAt Q (q * (2 * π * I / h)) z := hasStrictDerivAt_qParam hh z
  have diff_ne : q * (2 * π * I / h) ≠ 0 :=
    mul_ne_zero (qParam_ne_zero z hh) (two_pi_I_ne_zero.isUnit.div₀ hu).ne_zero
  let L := (qdiff.localInverse Q _ z) diff_ne
  have diff_L : DifferentiableAt ℂ L q :=
    (qdiff.to_localInverse diff_ne).hasStrictFDerivAt.differentiableAt
  have hL : Q ∘ L =ᶠ[𝓝 q] (id : ℂ → ℂ) :=
    (qdiff.hasStrictFDerivAt_equiv diff_ne).eventually_right_inverse
  have hF := hL.fun_comp (cuspFunction h f hh)
  have : cuspFunction h f hh ∘ Q ∘ L = f ∘ L :=
    funext fun w ↦ eq_cuspFunction hh hf (L w)
  rw [this] at hF
  rw [← EventuallyEq.eq_of_nhds (qdiff.hasStrictFDerivAt_equiv diff_ne).eventually_left_inverse]
    at hol_z
  exact (hol_z.comp q diff_L).congr_of_eventuallyEq hF.symm

theorem eventually_differentiableAt_cuspFunction_nhds_ne_zero (hh : 0 < h) (hf : Periodic f h)
    (h_hol : ∀ᶠ z in I∞, DifferentiableAt ℂ f z) :
    ∀ᶠ q in 𝓝[≠] 0, DifferentiableAt ℂ (cuspFunction h f hh.ne') q := by
  rw [← map_cuspSubtype_nhds]
  change ∀ᶠ q : {q : ℂ // q ≠ 0} in 𝓝₀, DifferentiableAt ℂ (cuspFunction h f hh.ne') q.val
  filter_upwards [(invQParam_tendsto hh).eventually h_hol] with q hq
  rw [← qParam_right_inv hh.ne' q.property]
  exact differentiableAt_cuspFunction hh.ne' hf hq

end HoloOnC

section HoloAtInfC

variable {h : ℝ} {f : ℂ → ℂ}

theorem boundedAtFilter_cuspFunction (hh : 0 < h) (h_bd : BoundedAtFilter I∞ f) :
    BoundedAtFilter (𝓝[≠] 0) (cuspFunction h f hh.ne') := by
  have hs : BoundedAtFilter 𝓝₀ (cuspFunction h f hh.ne' ∘ Subtype.val) :=
    (h_bd.comp_tendsto (invQParam_tendsto hh)).congr'
      (.of_forall fun q ↦ (cuspFunction_eq_of_nonzero h f hh.ne' q.property).symm) (by simp)
  unfold BoundedAtFilter at hs ⊢
  rw [← map_cuspSubtype_nhds, isBigO_map]
  exact hs

theorem cuspFunction_zero_of_zero_at_inf (hh : 0 < h) (h_zer : ZeroAtFilter I∞ f) :
    cuspFunction h f hh.ne' 0 = 0 := by
  simpa only [cuspFunction, dite_true, Function.comp_def] using
    (h_zer.comp (invQParam_tendsto hh)).limUnder_eq

theorem differentiableAt_cuspFunction_zero (hh : 0 < h) (hf : Periodic f h)
    (h_hol : ∀ᶠ z in I∞, DifferentiableAt ℂ f z) (h_bd : BoundedAtFilter I∞ f) :
    DifferentiableAt ℂ (cuspFunction h f hh.ne') 0 := by
  obtain ⟨c, t⟩ := (boundedAtFilter_cuspFunction hh h_bd).bound
  replace t := (eventually_differentiableAt_cuspFunction_nhds_ne_zero hh hf h_hol).and t
  simp only [norm_one, Pi.one_apply, mul_one] at t
  obtain ⟨S, hS1, hS2, hS3⟩ := eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp t)
  have h_diff : DifferentiableOn ℂ (cuspFunction h f hh.ne') (S \ {0}) :=
    fun x hx ↦ (hS1 x hx.1 hx.2).1.differentiableWithinAt
  have hF_bd : BddAbove (norm ∘ cuspFunction h f hh.ne' '' (S \ {0})) := by
    use c
    simp only [mem_upperBounds, Set.mem_image, Set.mem_sdiff, forall_exists_index, and_imp]
    intro y q hq hq2 hy
    simpa only [← hy, norm_one, mul_one] using! (hS1 q hq hq2).2
  have hx := differentiableOn_update_limUnder_of_bddAbove (IsOpen.mem_nhds hS2 hS3) h_diff hF_bd
  rw [← cuspFunction_zero_eq_limUnder_nhds_ne h f hh.ne', update_eq_self] at hx
  exact hx.differentiableAt (IsOpen.mem_nhds hS2 hS3)

/-- A periodic function that is holomorphic and bounded near `I∞` tends to its cusp value. -/
theorem tendsto_at_I_inf (hh : 0 < h) (hf : Periodic f h)
    (h_hol : ∀ᶠ z in I∞, DifferentiableAt ℂ f z) (h_bd : BoundedAtFilter I∞ f) :
    Tendsto f I∞ (𝓝 (cuspFunction h f hh.ne' 0)) := by
  suffices Tendsto (cuspFunction h f hh.ne') (𝓝[≠] 0) (𝓝 (cuspFunction h f hh.ne' 0)) by
    exact (this.comp (qParam_tendsto hh)).congr (eq_cuspFunction hh.ne' hf)
  exact tendsto_nhdsWithin_of_tendsto_nhds
    (differentiableAt_cuspFunction_zero hh hf h_hol h_bd).continuousAt.tendsto

/-- A bounded holomorphic periodic function approaches its cusp value exponentially. -/
theorem exp_decay_sub_of_bounded_at_inf (hh : 0 < h) (hf : Periodic f h)
    (h_hol : ∀ᶠ z in I∞, DifferentiableAt ℂ f z) (h_bd : BoundedAtFilter I∞ f) :
    (fun z ↦ f z - cuspFunction h f hh.ne' 0) =O[I∞]
      (fun z ↦ Real.exp (Checked.div (-2 * π * im z) h hh.ne'.isUnit)) := by
  simpa [comp_def, eq_cuspFunction hh.ne' hf, norm_qParam] using
    differentiableAt_cuspFunction_zero hh hf h_hol h_bd |>.isBigO_sub.mono
      nhdsWithin_le_nhds |>.comp_tendsto (qParam_tendsto hh) |>.norm_right

/-- A holomorphic periodic function that tends to zero at `I∞` decays exponentially. -/
theorem exp_decay_of_zero_at_inf (hh : 0 < h) (hf : Periodic f h)
    (h_hol : ∀ᶠ z in I∞, DifferentiableAt ℂ f z) (h_zer : ZeroAtFilter I∞ f) :
    f =O[I∞] fun z ↦ Real.exp (Checked.div (-2 * π * im z) h hh.ne'.isUnit) := by
  simpa [cuspFunction_zero_of_zero_at_inf hh h_zer, sub_zero] using
    exp_decay_sub_of_bounded_at_inf hh hf h_hol h_zer.boundedAtFilter

end HoloAtInfC

section arithmetic

lemma cuspFunction_smul {h} {hh : h ≠ 0} {f : ℂ → ℂ}
    (hfcts : ContinuousAt (cuspFunction h f hh) 0) (a : ℂ) :
    cuspFunction h (a • f) hh = a • cuspFunction h f hh := by
  ext q
  by_cases hq : q = 0
  · subst q
    have h := (tendsto_nhds_zero hfcts).const_mul a
    simpa only [cuspFunction, dite_true, Pi.smul_apply, smul_eq_mul] using h.limUnder_eq
  · simp only [cuspFunction, dite_eq_right hq, Pi.smul_apply]

lemma cuspFunction_neg {h} {hh : h ≠ 0} {f : ℂ → ℂ}
    (hfcts : ContinuousAt (cuspFunction h f hh) 0) :
    cuspFunction h (-f) hh = -cuspFunction h f hh := by
  simpa using cuspFunction_smul hfcts (-1)

lemma cuspFunction_add {h} {hh : h ≠ 0} {f g : ℂ → ℂ}
    (hfcts : ContinuousAt (cuspFunction h f hh) 0) (hgcts : ContinuousAt (cuspFunction h g hh) 0) :
    cuspFunction h (f + g) hh = cuspFunction h f hh + cuspFunction h g hh := by
  ext q
  by_cases hq : q = 0
  · subst q
    have h := (tendsto_nhds_zero hfcts).add (tendsto_nhds_zero hgcts)
    simpa only [cuspFunction, dite_true, Pi.add_apply] using h.limUnder_eq
  · simp only [cuspFunction, dite_eq_right hq, Pi.add_apply]

lemma cuspFunction_sub {h} {hh : h ≠ 0} {f g : ℂ → ℂ}
    (hfcts : ContinuousAt (cuspFunction h f hh) 0) (hgcts : ContinuousAt (cuspFunction h g hh) 0) :
    cuspFunction h (f - g) hh = cuspFunction h f hh - cuspFunction h g hh := by
  simpa [sub_eq_add_neg, ← cuspFunction_neg hgcts]
    using cuspFunction_add hfcts (by simp [cuspFunction_neg, hgcts])

end arithmetic

end Function.Periodic
