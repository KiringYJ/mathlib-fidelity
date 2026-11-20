/-
Copyright (c) 2023 Adomas Baliuka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adomas Baliuka
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Properties of Shannon q-ary entropy and binary entropy functions

The [binary entropy function](https://en.wikipedia.org/wiki/Binary_entropy_function)
`binEntropy p := - p * log p - (1 - p) * log (1 - p)`
is the Shannon entropy of a Bernoulli random variable with success probability `p`.

More generally, the q-ary entropy function is the Shannon entropy of the random variable
with possible outcomes `{1, ..., q}`, where outcome `1` has probability `1 - p`
and all other outcomes are equally likely.

`qaryEntropy (q : ℕ) (p : ℝ) := p * log (q - 1) - p * log p - (1 - p) * log (1 - p)`

This file assumes that entropy is measured in Nats, hence the use of natural logarithms.
Most lemmas are also valid using a logarithm in a different base.

## Main declarations

* `Real.binEntropy`: the binary entropy function
* `Real.qaryEntropy`: the `q`-ary entropy function

## Main results

The functions are also defined outside the interval `Icc 0 1` due to `log x = log |x|`.

* They are continuous everywhere (`binEntropy_continuous` and `qaryEntropy_continuous`).
* They are differentiable everywhere except at points `0` or `1`
  (`hasDerivAt_binEntropy` and `hasDerivAt_qaryEntropy`).
  In addition, due to junk values, `deriv binEntropy p = log (1 - p) - log p`
  holds everywhere (`deriv_binEntropy`).
* they are strictly increasing on `Icc 0 (1 - 1/q))`
  (`qaryEntropy_strictMonoOn`, `binEntropy_strictMonoOn`)
  and strictly decreasing on `Icc (1 - 1/q) 1`
  (`binEntropy_strictAntiOn` and `qaryEntropy_strictAntiOn`).
* they are strictly concave on `Icc 0 1`
  (`strictConcaveOn_qaryEntropy` and `strictConcave_binEntropy`).

## Tags

entropy, Shannon, binary, nit, nepit
-/

public section

namespace Real
variable {q : ℕ} {p : ℝ}

/-! ### Binary entropy -/

/-- The [binary entropy function](https://en.wikipedia.org/wiki/Binary_entropy_function)
`binEntropy p := - p * log p - (1-p) * log (1 - p)`
is the Shannon entropy of a Bernoulli random variable with success probability `p`. -/
@[pp_nodot] noncomputable def binEntropy (p : ℝ) : ℝ := negMulLog p + negMulLog (1 - p)

@[simp] lemma binEntropy_zero : binEntropy 0 = 0 := by simp [binEntropy, negMulLog]

@[simp] lemma binEntropy_one : binEntropy 1 = 0 := by simp [binEntropy, negMulLog]

@[simp] lemma binEntropy_two_inv : binEntropy 2⁻¹ = log 2 := by
  unfold binEntropy negMulLog
  rw [show 1 - (2 : ℝ)⁻¹ = 2⁻¹ by norm_num, log_inv]
  ring

lemma binEntropy_eq_negMulLog_add_negMulLog_one_sub (p : ℝ) :
    binEntropy p = negMulLog p + negMulLog (1 - p) := by unfold binEntropy; rfl

lemma binEntropy_eq_negMulLog_add_negMulLog_one_sub' :
    binEntropy = fun p ↦ negMulLog p + negMulLog (1 - p) :=
  funext binEntropy_eq_negMulLog_add_negMulLog_one_sub

/-- `binEntropy` is symmetric about 1/2. -/
@[simp] lemma binEntropy_one_sub (p : ℝ) : binEntropy (1 - p) = binEntropy p := by
  simp [binEntropy, add_comm]

/-- `binEntropy` is symmetric about 1/2. -/
lemma binEntropy_two_inv_add (p : ℝ) : binEntropy (2⁻¹ + p) = binEntropy (2⁻¹ - p) := by
  rw [← binEntropy_one_sub]; ring_nf

lemma binEntropy_pos (hp₀ : 0 < p) (hp₁ : p < 1) : 0 < binEntropy p := by
  unfold binEntropy negMulLog
  exact add_pos (mul_pos_of_neg_of_neg (neg_neg_of_pos hp₀) (log_neg hp₀ hp₁))
    (mul_pos_of_neg_of_neg (neg_neg_of_pos (sub_pos.2 hp₁))
      (log_neg (sub_pos.2 hp₁) (sub_lt_self _ hp₀)))

lemma binEntropy_nonneg (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) : 0 ≤ binEntropy p := by
  obtain rfl | hp₀ := hp₀.eq_or_lt
  · simp
  obtain rfl | hp₁ := hp₁.eq_or_lt
  · simp
  exact (binEntropy_pos hp₀ hp₁).le

/-- Outside the usual range of `binEntropy`, it is negative. This is due to `log p = log |p|`. -/
lemma binEntropy_neg_of_neg (hp : p < 0) : binEntropy p < 0 := by
  unfold binEntropy negMulLog
  suffices -p * log p < (1 - p) * log (1 - p) by linarith
  by_cases hp' : p < -1
  · have : log p < log (1 - p) := by
      rw [← log_neg_eq_log]
      exact log_lt_log (Left.neg_pos_iff.mpr hp) (by linarith)
    nlinarith [log_pos_of_lt_neg_one hp']
  · have : -p * log p ≤ 0 := by
      wlog h : -1 < p
      · simp only [show p = -1 by linarith, log_neg_eq_log, log_one, le_refl, mul_zero]
      · nlinarith [log_neg_of_lt_zero hp h]
    nlinarith [(log_pos (by linarith) : 0 < log (1 - p))]

/-- Outside the usual range of `binEntropy`, it is negative. This is due to `log p = log |p|`. -/
lemma binEntropy_nonpos_of_nonpos (hp : p ≤ 0) : binEntropy p ≤ 0 := by
  obtain rfl | hp := hp.eq_or_lt
  · simp
  · exact (binEntropy_neg_of_neg hp).le

/-- Outside the usual range of `binEntropy`, it is negative. This is due to `log p = log |p|` -/
lemma binEntropy_neg_of_one_lt (hp : 1 < p) : binEntropy p < 0 := by
  rw [← binEntropy_one_sub]; exact binEntropy_neg_of_neg (sub_neg.2 hp)

/-- Outside the usual range of `binEntropy`, it is negative. This is due to `log p = log |p|` -/
lemma binEntropy_nonpos_of_one_le (hp : 1 ≤ p) : binEntropy p ≤ 0 := by
  rw [← binEntropy_one_sub]; exact binEntropy_nonpos_of_nonpos (sub_nonpos.2 hp)

lemma binEntropy_eq_zero : binEntropy p = 0 ↔ p = 0 ∨ p = 1 := by
  refine ⟨fun h ↦ ?_, by rintro (rfl | rfl) <;> simp⟩
  contrapose! h
  obtain hp₀ | hp₀ := h.1.lt_or_gt
  · exact (binEntropy_neg_of_neg hp₀).ne
  obtain hp₁ | hp₁ := h.2.lt_or_gt.symm
  · exact (binEntropy_neg_of_one_lt hp₁).ne
  · exact (binEntropy_pos hp₀ hp₁).ne'

/-- For probability `p ≠ 0.5`, `binEntropy p < log 2`. -/
lemma binEntropy_lt_log_two : binEntropy p < log 2 ↔ p ≠ 2⁻¹ := by
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro h rfl
    simp at h
  wlog hp : p < 2⁻¹
  · have hp : 1 - p < 2⁻¹ := by
      rw [sub_lt_comm]; norm_num at *; linarith +splitNe
    rw [← binEntropy_one_sub]
    exact this hp.ne hp
  obtain hp₀ | hp₀ := le_or_gt p 0
  · exact (binEntropy_nonpos_of_nonpos hp₀).trans_lt <| log_pos <| by simp
  have hp₁ : 0 < 1 - p := sub_pos.2 <| hp.trans <| by norm_num
  have hlt : p < 1 - p := by norm_num at hp; linarith
  have hne : p⁻¹ ≠ (1 - p)⁻¹ := ((inv_lt_inv₀ hp₁ hp₀).2 hlt).ne'
  have hbin : binEntropy p = p * log p⁻¹ + (1 - p) * log (1 - p)⁻¹ := by
    simp only [binEntropy, negMulLog, log_inv, mul_neg, neg_mul]
  rw [hbin]
  simpa only [smul_eq_mul] using strictConcaveOn_log_Ioi.2 (z := 2)
    (inv_pos.2 hp₀) (inv_pos.2 hp₁) hne hp₀ hp₁ (by ring) (by norm_num)
    (by simp only [id_eq, smul_eq_mul, mul_inv_cancel₀, one_add_one_eq_two])

lemma binEntropy_le_log_two : binEntropy p ≤ log 2 := by
  obtain rfl | hp := eq_or_ne p 2⁻¹
  · simp
  · exact (binEntropy_lt_log_two.2 hp).le

lemma binEntropy_eq_log_two : binEntropy p = log 2 ↔ p = 2⁻¹ := by
  rw [← binEntropy_le_log_two.not_lt_iff_eq, binEntropy_lt_log_two, not_ne_iff]

/-- Binary entropy is continuous everywhere.
This is due to definition of `Real.log` for negative numbers. -/
@[fun_prop] lemma binEntropy_continuous : Continuous binEntropy := by
  rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub']; fun_prop

@[fun_prop] lemma differentiableAt_binEntropy (hp₀ : p ≠ 0) (hp₁ : p ≠ 1) :
    DifferentiableAt ℝ binEntropy p := by
  rw [ne_comm, ← sub_ne_zero] at hp₁
  unfold binEntropy negMulLog
  fun_prop

lemma differentiableAt_binEntropy_iff_ne_zero_one :
    DifferentiableAt ℝ binEntropy p ↔ p ≠ 0 ∧ p ≠ 1 := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun h ↦ differentiableAt_binEntropy h.1 h.2⟩
    <;> rintro rfl <;> unfold binEntropy at h
  · rw [DifferentiableAt.fun_add_iff_left] at h
    · simp [differentiableAt_negMulLog_iff] at h
    · unfold negMulLog
      fun_prop (disch := simp)
  · rw [DifferentiableAt.fun_add_iff_right, differentiableAt_iff_comp_const_sub (b := 1)] at h
    · simp [differentiableAt_negMulLog_iff] at h
    · unfold negMulLog
      fun_prop (disch := simp)

/-- Binary entropy has derivative `log (1 - p) - log p`.
It's not differentiable at `0` or `1` but the junk values of `deriv` and `log` coincide there. -/
lemma deriv_binEntropy (p : ℝ) : deriv binEntropy p = log (1 - p) - log p := by
  by_cases hp : p ≠ 0 ∧ p ≠ 1
  · obtain ⟨hp₀, hp₁⟩ := hp
    rw [ne_comm, ← sub_ne_zero] at hp₁
    rw [binEntropy_eq_negMulLog_add_negMulLog_one_sub', deriv_fun_add, deriv_comp_const_sub,
      deriv_negMulLog hp₀, deriv_negMulLog hp₁]
    · ring
    all_goals fun_prop
  -- pathological case where `deriv = 0` since `binEntropy` is not differentiable there
  · rw [deriv_zero_of_not_differentiableAt (differentiableAt_binEntropy_iff_ne_zero_one.not.2 hp)]
    push +distrib Not at hp
    obtain rfl | rfl := hp <;> simp

/-! ### `q`-ary entropy -/

/-- Shannon q-ary Entropy function (measured in Nats, i.e., using natural logs).

It's the Shannon entropy of a random variable with possible outcomes `{1, ..., q}`
where outcome `1` has probability `1 - p` and all other outcomes are equally likely.

The usual domain of definition is `p ∈ [0,1]`, i.e., input is a probability.

This is a generalization of the binary entropy function `binEntropy`. -/
@[pp_nodot] noncomputable def qaryEntropy (q : ℕ) (p : ℝ) : ℝ := p * log (q - 1 : ℤ) + binEntropy p

@[simp] lemma qaryEntropy_zero (q : ℕ) : qaryEntropy q 0 = 0 := by simp [qaryEntropy]
@[simp] lemma qaryEntropy_one (q : ℕ) : qaryEntropy q 1 = log (q - 1 : ℤ) := by simp [qaryEntropy]
@[simp] lemma qaryEntropy_two : qaryEntropy 2 = binEntropy := by ext; simp [qaryEntropy]

lemma qaryEntropy_pos (hp₀ : 0 < p) (hp₁ : p < 1) : 0 < qaryEntropy q p := by
  unfold qaryEntropy
  positivity [binEntropy_pos hp₀ hp₁]

lemma qaryEntropy_nonneg (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) : 0 ≤ qaryEntropy q p := by
  obtain rfl | hp₀ := hp₀.eq_or_lt
  · simp
  obtain rfl | hp₁ := hp₁.eq_or_lt
  · simpa [qaryEntropy, -Int.cast_sub] using log_intCast_nonneg _
  exact (qaryEntropy_pos hp₀ hp₁).le

/-- Outside the usual range of `qaryEntropy`, it is negative. This is due to `log p = log |p|`. -/
lemma qaryEntropy_neg_of_neg (hp : p < 0) : qaryEntropy q p < 0 :=
  add_neg_of_nonpos_of_neg (mul_nonpos_of_nonpos_of_nonneg hp.le (log_intCast_nonneg _))
    (binEntropy_neg_of_neg hp)

/-- Outside the usual range of `qaryEntropy`, it is negative. This is due to `log p = log |p|`. -/
lemma qaryEntropy_nonpos_of_nonpos (hp : p ≤ 0) : qaryEntropy q p ≤ 0 :=
  add_nonpos (mul_nonpos_of_nonpos_of_nonneg hp (log_intCast_nonneg _))
    (binEntropy_nonpos_of_nonpos hp)

/-- The q-ary entropy function is continuous everywhere.
This is due to definition of `Real.log` for negative numbers. -/
@[fun_prop] lemma qaryEntropy_continuous : Continuous (qaryEntropy q) := by
  unfold qaryEntropy; fun_prop

@[fun_prop] lemma differentiableAt_qaryEntropy (hp₀ : p ≠ 0) (hp₁ : p ≠ 1) :
    DifferentiableAt ℝ (qaryEntropy q) p := by unfold qaryEntropy; fun_prop

lemma deriv_qaryEntropy (hp₀ : p ≠ 0) (hp₁ : p ≠ 1) :
    deriv (qaryEntropy q) p = log (q - 1) + log (1 - p) - log p := by
  have hd : HasDerivAt (fun y : ℝ ↦ y * log (q - 1 : ℤ)) (log (q - 1 : ℤ)) p := by
    simpa only [id_eq, one_mul] using (hasDerivAt_id p).mul_const (log (q - 1 : ℤ))
  unfold qaryEntropy
  rw [deriv_fun_add hd.differentiableAt (differentiableAt_binEntropy hp₀ hp₁),
    hd.deriv, deriv_binEntropy, add_sub_assoc]
  simp only [Int.cast_sub, Int.cast_natCast, Int.cast_one]

/-- Binary entropy has derivative `log (1 - p) - log p`. -/
lemma hasDerivAt_binEntropy (hp₀ : p ≠ 0) (hp₁ : p ≠ 1) :
    HasDerivAt binEntropy (log (1 - p) - log p) p :=
  deriv_binEntropy _ ▸ (differentiableAt_binEntropy hp₀ hp₁).hasDerivAt

lemma hasDerivAt_qaryEntropy (hp₀ : p ≠ 0) (hp₁ : p ≠ 1) :
    HasDerivAt (qaryEntropy q) (log (q - 1) + log (1 - p) - log p) p :=
  deriv_qaryEntropy hp₀ hp₁ ▸ (differentiableAt_qaryEntropy hp₀ hp₁).hasDerivAt

open Filter Set

open scoped Topology

private lemma tendsto_log_one_sub_sub_log_nhdsGT_atAtop :
    Tendsto (fun p ↦ log (1 - p) - log p) (𝓝[>] 0) atTop := by
  apply Filter.tendsto_atTop_add_left_of_le' (𝓝[>] 0) (log (1 / 2) : ℝ)
  · have h₁ : (0 : ℝ) < 1 / 2 := by simp
    filter_upwards [Ioc_mem_nhdsGT h₁] with p hx
    gcongr
    linarith [hx.2]
  · apply tendsto_neg_atTop_iff.mpr tendsto_log_nhdsGT_zero

private lemma tendsto_log_one_sub_sub_log_nhdsLT_one_atBot :
    Tendsto (fun p ↦ log (1 - p) - log p) (𝓝[<] 1) atBot := by
  apply Filter.tendsto_atBot_add_right_of_ge' (𝓝[<] 1) (-log (1 - 2⁻¹))
  · have : Tendsto log (𝓝[>] 0) atBot := Real.tendsto_log_nhdsGT_zero
    apply Tendsto.comp (f := (1 - ·)) (g := log) this
    have contF : Continuous ((1 : ℝ) - ·) := continuous_sub_left 1
    have : MapsTo ((1 : ℝ) - ·) (Iio 1) (Ioi 0) := by
      intro p hx
      simp_all only [mem_Iio, mem_Ioi, sub_pos]
    convert! ContinuousWithinAt.tendsto_nhdsWithin (x := (1 : ℝ)) contF.continuousWithinAt this
    exact Eq.symm (sub_eq_zero_of_eq rfl)
  · have h₁ : (1 : ℝ) - (2 : ℝ)⁻¹ < 1 := by norm_num
    filter_upwards [Ico_mem_nhdsLT h₁] with p hx
    gcongr
    exact hx.1

lemma not_continuousAt_deriv_qaryEntropy_one :
    ¬ContinuousAt (deriv (qaryEntropy q)) 1 := by
  have tendstoBot : Tendsto (fun p ↦ log (q - 1) + log (1 - p) - log p) (𝓝[<] 1) atBot := by
    have : (fun p ↦ log (q - 1) + log (1 - p) - log p)
      = (fun p ↦ log (q - 1) + (log (1 - p) - log p)) := by
      ext
      ring
    rw [this]
    apply tendsto_atBot_add_const_left
    exact tendsto_log_one_sub_sub_log_nhdsLT_one_atBot
  apply not_continuousAt_of_tendsto (Filter.Tendsto.congr' _ tendstoBot) nhdsWithin_le_nhds
  · simp only [disjoint_nhds_atBot_iff, not_isBot, not_false_eq_true]
  filter_upwards [Ioo_mem_nhdsLT (show 1 - 2⁻¹ < (1 : ℝ) by norm_num)]
  intros
  apply (deriv_qaryEntropy _ _).symm
  · simp_all only [mem_Ioo, ne_eq]
    linarith [show (1 : ℝ) = 2⁻¹ + 2⁻¹ by norm_num]
  · simp_all only [mem_Ioo, ne_eq]
    linarith [two_inv_lt_one (α := ℝ)]

lemma not_continuousAt_deriv_qaryEntropy_zero :
    ¬ContinuousAt (deriv (qaryEntropy q)) 0 := by
  have tendstoTop : Tendsto (fun p ↦ log (q - 1) + log (1 - p) - log p) (𝓝[>] 0) atTop := by
    have : (fun p ↦ log (q - 1) + log (1 - p) - log p)
        = (fun p ↦ log (q - 1) + (log (1 - p) - log p)) := by ext; ring
    rw [this]
    exact tendsto_atTop_add_const_left _ _ tendsto_log_one_sub_sub_log_nhdsGT_atAtop
  apply not_continuousAt_of_tendsto (Filter.Tendsto.congr' _ tendstoTop) nhdsWithin_le_nhds
  · simp only [disjoint_nhds_atTop_iff, not_isTop, not_false_eq_true]
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 2⁻¹ by norm_num)]
  intros
  apply (deriv_qaryEntropy _ _).symm
  · simp_all only [mem_Ioo, ne_eq]
    linarith
  · simp_all only [mem_Ioo, ne_eq]
    linarith [two_inv_lt_one (α := ℝ)]

/-- Second derivative of q-ary entropy. -/
lemma deriv2_qaryEntropy (hp₀ : p ≠ 0) (hp₁ : p ≠ 1) :
    deriv^[2] (qaryEntropy q) p =
      Checked.div (-1) (p * (1 - p)) (hp₀.isUnit.mul (sub_ne_zero.mpr hp₁.symm).isUnit) := by
  simp only [Function.iterate_succ, Function.iterate_zero, Function.id_comp, Function.comp_apply]
  have he : deriv (qaryEntropy q) =ᶠ[𝓝 p] fun y ↦ log (q - 1) + log (1 - y) - log y := by
    filter_upwards [eventually_ne_nhds hp₀, eventually_ne_nhds hp₁] with y hy₀ hy₁
    exact deriv_qaryEntropy hy₀ hy₁
  have hne : 1 - p ≠ 0 := sub_ne_zero.mpr hp₁.symm
  have hd₁ : HasDerivAt (fun y : ℝ ↦ log (1 - y)) (-(1 - p)⁻¹) p := by
    simpa only [Function.comp_def, id_eq, mul_neg, mul_one] using
      (hasDerivAt_log (x := 1 - p) (hx := hne.isUnit)).comp p ((hasDerivAt_id p).const_sub 1)
  have hd : HasDerivAt (fun y ↦ log ((q : ℝ) - 1) + log (1 - y) - log y)
      (-(1 - p)⁻¹ - p⁻¹) p :=
    (hd₁.const_add (log ((q : ℝ) - 1))).fun_sub (hasDerivAt_log (x := p) (hx := hp₀.isUnit))
  rw [Filter.EventuallyEq.deriv_eq he, hd.deriv]
  field_simp [hp₀, hne]
  ring

lemma deriv2_binEntropy (hp₀ : p ≠ 0) (hp₁ : p ≠ 1) :
    deriv^[2] binEntropy p =
      Checked.div (-1) (p * (1 - p)) (hp₀.isUnit.mul (sub_ne_zero.mpr hp₁.symm).isUnit) :=
  qaryEntropy_two ▸ deriv2_qaryEntropy hp₀ hp₁

/-! ### Strict monotonicity of entropy -/

/-- Qary entropy is strictly increasing in the interval [0, 1 - q⁻¹]. -/
lemma qaryEntropy_strictMonoOn (qLe2 : 2 ≤ q) :
    StrictMonoOn (qaryEntropy q) (Icc 0 (1 - 1 / q)) := by
  intro p1 hp1 p2 hp2 p1le2
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 (1 - 1 / (q : ℝ))) _ _ hp1 hp2 p1le2
  · exact qaryEntropy_continuous.continuousOn
  · intro p hp
    have hq₂ : 2 ≤ (q : ℝ) := Nat.ofNat_le_cast.mpr qLe2
    have hq : 0 < (q : ℝ) := by linarith
    have hq₁ : 0 < (q : ℝ) - 1 := by linarith
    simp only [interior_Icc, mem_Ioo] at hp
    have hp₁ : p < 1 := hp.2.trans (sub_lt_self _ (div_pos one_pos hq))
    have hmid : 1 - 1 / (q : ℝ) = ((q : ℝ) - 1) / q := by rw [sub_div', one_mul]
    have hcross := (lt_div_iff₀ hq).1 (hmid ▸ hp.2)
    rw [deriv_qaryEntropy hp.1.ne' hp₁.ne, ← log_mul (by linarith) (by linarith)]
    exact sub_pos.mpr (log_lt_log hp.1 (by nlinarith))

/-- Qary entropy is strictly decreasing in the interval [1 - q⁻¹, 1]. -/
lemma qaryEntropy_strictAntiOn (qLe2 : 2 ≤ q) :
    StrictAntiOn (qaryEntropy q) (Icc (1 - 1 / q) 1) := by
  intro p1 hp1 p2 hp2 p1le2
  apply strictAntiOn_of_deriv_neg (convex_Icc (1 - 1 / (q : ℝ)) 1) _ _ hp1 hp2 p1le2
  · exact qaryEntropy_continuous.continuousOn
  · intro p hp
    have hq₂ : 2 ≤ (q : ℝ) := Nat.ofNat_le_cast.mpr qLe2
    have hq : 0 < (q : ℝ) := by linarith
    have hq₁ : 0 < (q : ℝ) - 1 := by linarith
    simp only [interior_Icc, mem_Ioo] at hp
    have hmid : 1 - 1 / (q : ℝ) = ((q : ℝ) - 1) / q := by rw [sub_div', one_mul]
    have hp₀ : 0 < p := (div_pos hq₁ hq).trans (hmid ▸ hp.1)
    have hcross := (div_lt_iff₀ hq).1 (hmid ▸ hp.1)
    rw [deriv_qaryEntropy hp₀.ne' hp.2.ne, ← log_mul (by linarith) (by linarith)]
    exact sub_neg.mpr (log_lt_log (mul_pos hq₁ (sub_pos.mpr hp.2)) (by nlinarith))

/-- Binary entropy is strictly increasing in interval [0, 1/2]. -/
lemma binEntropy_strictMonoOn : StrictMonoOn binEntropy (Icc 0 2⁻¹) := by
  rw [show Icc (0 : ℝ) 2⁻¹ = Icc 0 (1 - 1 / 2) by norm_num, ← qaryEntropy_two]
  exact qaryEntropy_strictMonoOn (by rfl)

/-- Binary entropy is strictly decreasing in interval [1/2, 1]. -/
lemma binEntropy_strictAntiOn : StrictAntiOn binEntropy (Icc 2⁻¹ 1) := by
  rw [show (Icc (2⁻¹ : ℝ) 1) = Icc (1 / 2) 1 by norm_num, ← qaryEntropy_two]
  convert! qaryEntropy_strictAntiOn (by rfl) using 1
  norm_num

/-! ### Strict concavity of entropy -/

lemma strictConcaveOn_qaryEntropy : StrictConcaveOn ℝ (Icc 0 1) (qaryEntropy q) := by
  apply strictConcaveOn_of_deriv2_neg (convex_Icc 0 1) qaryEntropy_continuous.continuousOn
  intro p hp
  simp only [interior_Icc, mem_Ioo] at hp
  rw [deriv2_qaryEntropy hp.1.ne' hp.2.ne]
  exact div_neg_of_neg_of_pos (by norm_num) (mul_pos hp.1 (sub_pos.mpr hp.2))

lemma strictConcave_binEntropy : StrictConcaveOn ℝ (Icc 0 1) binEntropy :=
  qaryEntropy_two ▸ strictConcaveOn_qaryEntropy

end Real
