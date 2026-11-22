/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.PeakFunction

/-! # Euler's infinite product for the sine function

This file proves the infinite product formula

$$ \sin \pi z = \pi z \prod_{n = 1}^\infty \left(1 - \frac{z ^ 2}{n ^ 2}\right) $$

for any real or complex `z`. Our proof closely follows the article
[Salwinski, *Euler's Sine Product Formula: An Elementary Proof*][salwinski2018]: the basic strategy
is to prove a recurrence relation for the integrals `∫ x in 0..π/2, cos 2 z x * cos x ^ (2 * n)`,
generalising the arguments used to prove Wallis' limit formula for `π`.
-/

public section

open scoped Real Topology

open Real Set Filter intervalIntegral MeasureTheory.MeasureSpace

namespace EulerSine

section IntegralRecursion

/-! ## Recursion formula for the integral of `cos (2 * z * x) * cos x ^ n`

We evaluate the integral of `cos (2 * z * x) * cos x ^ n`, for any complex `z` and even integers
`n`, via repeated integration by parts. -/


variable {z : ℂ} {n : ℕ}

theorem antideriv_cos_comp_const_mul (hz : z ≠ 0) (x : ℝ) :
    HasDerivAt (fun y : ℝ => Complex.sin (2 * z * y) / (2 * z)) (Complex.cos (2 * z * x)) x := by
  have hu : IsUnit (2 * z) := (mul_ne_zero two_ne_zero hz).isUnit
  have hl : HasDerivAt (fun y : ℂ ↦ 2 * z * y) (2 * z) (x : ℂ) := hasDerivAt_const_mul _
  have h : HasDerivAt (fun y : ℝ ↦ Complex.sin (2 * z * y))
      (Complex.cos (2 * z * x) * (2 * z)) x := by
    simpa only [Function.comp_def] using ((Complex.hasDerivAt_sin _).comp (x : ℂ) hl).comp_ofReal
  have hcoef : Complex.cos (2 * z * x) * (2 * z) / (2 * z) = Complex.cos (2 * z * x) :=
    (div_eq_iff (hb := hu)).mpr rfl
  have h' := h.div_const (2 * z) (hd := hu)
  rwa [hcoef] at h'

theorem antideriv_sin_comp_const_mul (hz : z ≠ 0) (x : ℝ) :
    HasDerivAt (fun y : ℝ => -Complex.cos (2 * z * y) / (2 * z)) (Complex.sin (2 * z * x)) x := by
  have hu : IsUnit (2 * z) := (mul_ne_zero two_ne_zero hz).isUnit
  have hl : HasDerivAt (fun y : ℂ ↦ 2 * z * y) (2 * z) (x : ℂ) := hasDerivAt_const_mul _
  have h : HasDerivAt (fun y : ℝ ↦ Complex.cos (2 * z * y))
      (-Complex.sin (2 * z * x) * (2 * z)) x := by
    simpa only [Function.comp_def] using ((Complex.hasDerivAt_cos _).comp (x : ℂ) hl).comp_ofReal
  have hcoef : -(-Complex.sin (2 * z * x) * (2 * z)) / (2 * z) = Complex.sin (2 * z * x) := by
    rw [neg_mul, neg_neg]
    exact (div_eq_iff (hb := hu)).mpr rfl
  have h' := h.fun_neg.div_const (2 * z) (hd := hu)
  rwa [hcoef] at h'

theorem integral_cos_mul_cos_pow_aux (hn : 2 ≤ n) (hz : z ≠ 0) :
    (∫ x in (0 : ℝ)..π / 2, Complex.cos (2 * z * x) * (cos x : ℂ) ^ n) =
      (n : ℂ) / (2 * z) *
        ∫ x in (0 : ℝ)..π / 2, Complex.sin (2 * z * x) * sin x * (cos x : ℂ) ^ (n - 1) := by
  have der1 :
    ∀ x : ℝ,
      x ∈ uIcc 0 (π / 2) →
        HasDerivAt (fun y : ℝ => (cos y : ℂ) ^ n) (-n * sin x * (cos x : ℂ) ^ (n - 1)) x := by
    intro x _
    have b : HasDerivAt (fun y : ℝ => (cos y : ℂ)) (-sin x) x := by
      simpa using (hasDerivAt_cos x).ofReal_comp
    convert b.fun_pow n using 1
    · ring
    · rfl
  convert! (config := { sameFun := true })
    integral_mul_deriv_eq_deriv_mul der1 (fun x _ => antideriv_cos_comp_const_mul hz x) _ _ using 2
  · ext1 x; rw [mul_comm]
  · rw [Complex.ofReal_zero, mul_zero, Complex.sin_zero, zero_div, mul_zero, sub_zero,
      cos_pi_div_two, Complex.ofReal_zero, zero_pow (by positivity : n ≠ 0), zero_mul, zero_sub,
      ← integral_neg, ← integral_const_mul]
    refine integral_congr fun x _ => ?_
    ring
  · apply Continuous.intervalIntegrable (by fun_prop)
  · apply Continuous.intervalIntegrable <| by fun_prop

theorem integral_sin_mul_sin_mul_cos_pow_eq (hn : 2 ≤ n) (hz : z ≠ 0) :
    (∫ x in (0 : ℝ)..π / 2, Complex.sin (2 * z * x) * sin x * (cos x : ℂ) ^ (n - 1)) =
      ((n : ℂ) / (2 * z) * ∫ x in (0 : ℝ)..π / 2, Complex.cos (2 * z * x) * (cos x : ℂ) ^ n) -
        ((n : ℂ) - 1) / (2 * z) *
          ∫ x in (0 : ℝ)..π / 2, Complex.cos (2 * z * x) * (cos x : ℂ) ^ (n - 2) := by
  have der1 :
    ∀ x : ℝ,
      x ∈ uIcc 0 (π / 2) →
        HasDerivAt (fun y : ℝ => sin y * (cos y : ℂ) ^ (n - 1))
          ((cos x : ℂ) ^ n - (n - 1) * (sin x : ℂ) ^ 2 * (cos x : ℂ) ^ (n - 2)) x := by
    intro x _
    have hcos : HasDerivAt (fun y : ℝ ↦ (cos y : ℂ)) (-sin x) x := by
      simpa using (hasDerivAt_cos x).ofReal_comp
    have hsin : HasDerivAt (fun y : ℝ ↦ (sin y : ℂ)) (cos x) x := by
      simpa using (hasDerivAt_sin x).ofReal_comp
    have hpow : (cos x : ℂ) ^ n = (cos x : ℂ) ^ (n - 1) * cos x := by
      conv_lhs => rw [← Nat.sub_add_cancel (one_le_two.trans hn), pow_succ]
    convert hsin.fun_mul (hcos.fun_pow (n - 1)) using 1
    rw [hpow, Nat.sub_sub, Nat.cast_sub (one_le_two.trans hn), Nat.cast_one]
    ring
  convert!
    integral_mul_deriv_eq_deriv_mul der1 (fun x _ => antideriv_sin_comp_const_mul hz x) _ _ using 1
  · refine integral_congr fun x _ => ?_
    ring_nf
  · -- now a tedious rearrangement of terms
    -- gather into a single integral, and deal with continuity subgoals:
    rw [sin_zero, cos_pi_div_two, Complex.ofReal_zero, zero_pow, zero_mul,
      mul_zero, zero_mul, zero_mul, sub_zero, zero_sub, ←
      integral_neg, ← integral_const_mul, ← integral_const_mul, ← integral_sub]
    rotate_left
    · apply Continuous.intervalIntegrable <| by fun_prop
    · apply Continuous.intervalIntegrable <| by fun_prop
    · exact Nat.sub_ne_zero_of_lt hn
    refine integral_congr fun x _ => ?_
    -- get rid of real trig functions and divisions by 2 * z:
    rw [Complex.ofReal_cos, Complex.ofReal_sin, Complex.sin_sq]
    have : Complex.cos x ^ n = Complex.cos x ^ (n - 2) * Complex.cos x ^ 2 := by
      conv_lhs => rw [← Nat.sub_add_cancel hn, pow_add]
    rw [this]
    have h₂z : 2 * z ≠ 0 := mul_ne_zero two_ne_zero hz
    field_simp
    ring
  · apply Continuous.intervalIntegrable <| by fun_prop
  · apply Continuous.intervalIntegrable <| by fun_prop

/-- Note this also holds for `z = 0`, but we do not need this case for `sin_pi_mul_eq`. -/
theorem integral_cos_mul_cos_pow (hn : 2 ≤ n) (hz : z ≠ 0) :
    (((1 : ℂ) - (4 : ℂ) * z ^ 2 / (n : ℂ) ^ 2) *
      ∫ x in (0 : ℝ)..π / 2, Complex.cos (2 * z * x) * (cos x : ℂ) ^ n) =
      (n - 1 : ℂ) / (n : ℂ) *
        ∫ x in (0 : ℝ)..π / 2, Complex.cos (2 * z * x) * (cos x : ℂ) ^ (n - 2) := by
  have nne : (n : ℂ) ≠ 0 := by
    contrapose! hn; rw [Nat.cast_eq_zero] at hn; rw [hn]; exact zero_lt_two
  have := integral_cos_mul_cos_pow_aux hn hz
  rw [integral_sin_mul_sin_mul_cos_pow_eq hn hz, sub_eq_neg_add, mul_add, ← sub_eq_iff_eq_add]
    at this
  convert! congr_arg (fun u : ℂ => -u * (2 * z) ^ 2 / (n : ℂ) ^ 2) this using 1 <;> field

lemma two_mul_natCast_add_two_ne_zero (n : ℕ) : (2 * (n : ℂ) + 2) ≠ 0 := by
  exact_mod_cast (by omega : 2 * n + 2 ≠ 0)

/-- Note this also holds for `z = 0`, but we do not need this case for `sin_pi_mul_eq`. -/
theorem integral_cos_mul_cos_pow_even (n : ℕ) (hz : z ≠ 0) :
    (((1 : ℂ) - z ^ 2 / ((n : ℂ) + 1) ^ 2) *
        ∫ x in (0 : ℝ)..π / 2, Complex.cos (2 * z * x) * (cos x : ℂ) ^ (2 * n + 2)) =
      Checked.div (2 * n + 1 : ℂ) (2 * n + 2) (two_mul_natCast_add_two_ne_zero n).isUnit *
        ∫ x in (0 : ℝ)..π / 2, Complex.cos (2 * z * x) * (cos x : ℂ) ^ (2 * n) := by
  have hn := Nat.cast_add_one_ne_zero (R := ℂ) n
  have h₂n := two_mul_natCast_add_two_ne_zero n
  have hcoef : 4 * z ^ 2 / (2 * (n : ℂ) + 2) ^ 2 = z ^ 2 / ((n : ℂ) + 1) ^ 2 := by
    field_simp
    ring
  have hnum : (2 * (n : ℂ) + 2) - 1 = 2 * (n : ℂ) + 1 := by ring
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_two, show 2 * n + 2 - 2 = 2 * n by omega,
    hcoef, hnum] using integral_cos_mul_cos_pow (n := 2 * n + 2) (by omega) hz

/-- Relate the integral `cos x ^ n` over `[0, π/2]` to the integral of `sin x ^ n` over `[0, π]`,
which is studied in `Mathlib/Analysis/Real/Pi/Wallis.lean` and other places. -/
theorem integral_cos_pow_eq (n : ℕ) :
    (∫ x in (0 : ℝ)..π / 2, cos x ^ n) = 1 / 2 * ∫ x in (0 : ℝ)..π, sin x ^ n := by
  apply mul_right_cancel₀ (two_ne_zero : (2 : ℝ) ≠ 0)
  rw [mul_comm (1 / 2 : ℝ), mul_assoc, div_mul_cancel₀, mul_one, mul_two]
  have L : IntervalIntegrable _ volume 0 (π / 2) :=
    (continuous_sin.fun_pow n).intervalIntegrable _ _
  have R : IntervalIntegrable _ volume (π / 2) π :=
    (continuous_sin.fun_pow n).intervalIntegrable _ _
  rw [← integral_add_adjacent_intervals L R]
  congr 1
  · nth_rw 1 [(by ring : 0 = π / 2 - π / 2)]
    nth_rw 3 [(by ring : π / 2 = π / 2 - 0)]
    rw [← integral_comp_sub_left]
    refine integral_congr fun x _ => ?_
    rw [cos_pi_div_two_sub]
  · nth_rw 3 [(by ring : π = π / 2 + π / 2)]
    nth_rw 2 [(by ring : π / 2 = 0 + π / 2)]
    rw [← integral_comp_add_right]
    refine integral_congr fun x _ => ?_
    rw [sin_add_pi_div_two]

theorem integral_cos_pow_pos (n : ℕ) : 0 < ∫ x in (0 : ℝ)..π / 2, cos x ^ n :=
  (integral_cos_pow_eq n).symm ▸ mul_pos one_half_pos (integral_sin_pow_pos _)

lemma isUnit_integral_cos_pow (n : ℕ) :
    IsUnit ((∫ x in (0 : ℝ)..π / 2, cos x ^ n : ℝ) : ℂ) :=
  (Complex.ofReal_ne_zero.mpr (integral_cos_pow_pos n).ne').isUnit

/-- Finite form of Euler's sine product, with remainder term expressed as a ratio of cosine
integrals. -/
theorem sin_pi_mul_eq (z : ℂ) (n : ℕ) :
    Complex.sin (π * z) =
      Checked.div
        ((π * z * ∏ j ∈ Finset.range n, ((1 : ℂ) - z ^ 2 / ((j : ℂ) + 1) ^ 2)) *
          ∫ x in (0 : ℝ)..π / 2, Complex.cos (2 * z * x) * (cos x : ℂ) ^ (2 * n))
        ((∫ x in (0 : ℝ)..π / 2, cos x ^ (2 * n) : ℝ) : ℂ) (isUnit_integral_cos_pow (2 * n)) := by
  apply eq_div_iff.mpr
  rcases eq_or_ne z 0 with (rfl | hz)
  · simp
  let A (m : ℕ) : ℂ := π * z * ∏ j ∈ Finset.range m, ((1 : ℂ) - z ^ 2 / ((j : ℂ) + 1) ^ 2)
  let B (m : ℕ) : ℂ :=
    ∫ x in (0 : ℝ)..π / 2, Complex.cos (2 * z * x) * (cos x : ℂ) ^ (2 * m)
  let C (m : ℕ) : ℝ := ∫ x in (0 : ℝ)..π / 2, cos x ^ (2 * m)
  change Complex.sin (π * z) * (C n : ℂ) = A n * B n
  induction n with
  | zero =>
    simp only [A, B, C, Nat.mul_zero, pow_zero, mul_one, Finset.prod_range_zero,
      integral_one, sub_zero]
    rw [integral_cos_mul_complex (mul_ne_zero two_ne_zero hz), Complex.ofReal_zero,
      mul_zero, Complex.sin_zero, zero_div, sub_zero,
      (by push_cast; ring : 2 * z * ↑(π / 2) = π * z)]
    field_simp
    push_cast
    ring
  | succ n ih =>
    have hC : C (n + 1) = ((2 * n + 1 : ℝ) / (2 * (n : ℝ) + 2)) * C n := by
      dsimp only [C]
      rw [integral_cos_pow_eq (2 * (n + 1)), integral_cos_pow_eq (2 * n),
        show 2 * (n + 1) = 2 * n + 2 by omega, integral_sin_pow]
      simp only [sin_zero, sin_pi, pow_succ', zero_mul, sub_zero, zero_div, zero_add,
        Nat.cast_mul, Nat.cast_ofNat]
      ring
    have hA : A (n + 1) =
        A n * ((1 : ℂ) - z ^ 2 / ((n : ℂ) + 1) ^ 2) := by
      simp only [A, Finset.prod_range_succ, mul_assoc]
    have hB : ((1 : ℂ) - z ^ 2 / ((n : ℂ) + 1) ^ 2) * B (n + 1) =
        Checked.div (2 * n + 1 : ℂ) (2 * n + 2)
          (two_mul_natCast_add_two_ne_zero n).isUnit * B n := by
      simpa only [B, show 2 * (n + 1) = 2 * n + 2 by omega] using
        integral_cos_mul_cos_pow_even n hz
    rw [hC, Complex.ofReal_mul, Complex.ofReal_div, hA, mul_assoc (A n), hB]
    simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_ofNat,
      Complex.ofReal_one]
    rw [mul_left_comm, ih, mul_left_comm]

end IntegralRecursion

/-! ## Conclusion of the proof

The main theorem `Complex.tendsto_euler_sin_prod`, and its real variant
`Real.tendsto_euler_sin_prod`, now follow by combining `sin_pi_mul_eq` with a lemma
stating that the sequence of measures on `[0, π/2]` given by integration against `cos x ^ n`
(suitably normalised) tends to the Dirac measure at 0, as a special case of the general result
`tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_continuousOn`. -/


theorem tendsto_integral_cos_pow_mul_div {f : ℝ → ℂ} (hf : ContinuousOn f (Icc 0 (π / 2))) :
    Tendsto
      (fun n : ℕ ↦ Checked.div (∫ x in (0 : ℝ)..π / 2, (cos x : ℂ) ^ n * f x)
        ((∫ x in (0 : ℝ)..π / 2, cos x ^ n : ℝ) : ℂ) (isUnit_integral_cos_pow n))
      atTop (𝓝 <| f 0) := by
  have c_lt : ∀ y : ℝ, y ∈ Icc 0 (π / 2) → y ≠ 0 → cos y < cos 0 := fun y hy hy' =>
    cos_lt_cos_of_nonneg_of_le_pi_div_two (le_refl 0) hy.2 (lt_of_le_of_ne hy.1 hy'.symm)
  have c_nonneg : ∀ x : ℝ, x ∈ Icc 0 (π / 2) → 0 ≤ cos x := fun x hx =>
    cos_nonneg_of_mem_Icc ((Icc_subset_Icc_left (neg_nonpos_of_nonneg pi_div_two_pos.le)) hx)
  have c_zero_pos : 0 < cos 0 := by rw [cos_zero]; exact zero_lt_one
  have zero_mem : (0 : ℝ) ∈ closure (interior (Icc 0 (π / 2))) := by
    rw [interior_Icc, closure_Ioo pi_div_two_pos.ne, left_mem_Icc]
    exact pi_div_two_pos.le
  have h := tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_continuousOn
    (μ := volume) isCompact_Icc continuousOn_cos c_lt c_nonneg c_zero_pos zero_mem hf
  refine h.congr fun n ↦ ?_
  have hu := (integral_cos_pow_pos n).ne'.isUnit
  have hC : (∫ x in (0 : ℝ)..π / 2, cos x ^ n) = ∫ x in Icc 0 (π / 2), cos x ^ n := by
    rw [integral_of_le pi_div_two_pos.le, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  have hI : (∫ x in (0 : ℝ)..π / 2, (cos x : ℂ) ^ n * f x) =
      ∫ x in Icc 0 (π / 2), cos x ^ n • f x := by
    rw [integral_of_le pi_div_two_pos.le, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    apply MeasureTheory.integral_congr_ae
    exact Eventually.of_forall fun x ↦ by
      change (cos x : ℂ) ^ n * f x = cos x ^ n • f x
      rw [← Complex.ofReal_pow, ← Complex.real_smul]
  calc
    _ = Checked.inv (∫ x in (0 : ℝ)..π / 2, cos x ^ n) hu •
          ∫ x in (0 : ℝ)..π / 2, (cos x : ℂ) ^ n * f x := by simp only [hC, hI]
    _ = _ := by
      let a : ℝ := ∫ x in (0 : ℝ)..π / 2, cos x ^ n
      let b : ℂ := ∫ x in (0 : ℝ)..π / 2, (cos x : ℂ) ^ n * f x
      change Checked.inv a hu • b = Checked.div b (a : ℂ) (isUnit_integral_cos_pow n)
      rw [div_eq_inv_mul₀ b (a : ℂ), ← Complex.ofReal_inv a (hr := hu), ← Complex.real_smul]

/-- Euler's infinite product formula for the complex sine function. -/
theorem _root_.Complex.tendsto_euler_sin_prod (z : ℂ) :
    Tendsto (fun n : ℕ => π * z * ∏ j ∈ Finset.range n, ((1 : ℂ) - z ^ 2 / ((j : ℂ) + 1) ^ 2))
      atTop (𝓝 <| Complex.sin (π * z)) := by
  let R (n : ℕ) : ℂ := Checked.div
    (∫ x in (0 : ℝ)..π / 2, Complex.cos (2 * z * x) * (cos x : ℂ) ^ n)
    ((∫ x in (0 : ℝ)..π / 2, cos x ^ n : ℝ) : ℂ) (isUnit_integral_cos_pow n)
  have hR : Tendsto R atTop (𝓝 1) := by
    have hc : ContinuousOn (fun x : ℝ ↦ Complex.cos (2 * z * x)) (Icc 0 (π / 2)) := by fun_prop
    have h : Tendsto R atTop (𝓝 (Complex.cos (2 * z * (0 : ℂ)))) :=
      (tendsto_integral_cos_pow_mul_div hc).congr fun n ↦
        congrArg (fun u : ℂ ↦ Checked.div u _ (isUnit_integral_cos_pow n))
          (integral_congr fun x _ ↦ mul_comm _ _)
    simpa only [mul_zero, Complex.cos_zero] using h
  have hS := hR.comp (tendsto_id.const_mul_atTop' (zero_lt_two : 0 < (2 : ℕ)))
  have hAB : Tendsto (fun n : ℕ ↦
      (π * z * ∏ j ∈ Finset.range n, ((1 : ℂ) - z ^ 2 / ((j : ℂ) + 1) ^ 2)) * R (2 * n))
        atTop (𝓝 (Complex.sin (π * z) * 1)) := by
    rw [mul_one]
    refine tendsto_const_nhds.congr fun n ↦ ?_
    exact (sin_pi_mul_eq z n).trans (mul_div_assoc₀ _ _ _)
  exact (tendsto_mul_iff_of_ne_zero hS one_ne_zero).mp hAB

/-- Euler's infinite product formula for the real sine function. -/
theorem _root_.Real.tendsto_euler_sin_prod (x : ℝ) :
    Tendsto (fun n : ℕ => π * x * ∏ j ∈ Finset.range n, ((1 : ℝ) - x ^ 2 / ((j : ℝ) + 1) ^ 2))
      atTop (𝓝 <| sin (π * x)) := by
  convert! (Complex.continuous_re.tendsto _).comp (Complex.tendsto_euler_sin_prod x) using 1
  · ext1 n
    rw [Function.comp_apply, ← Complex.ofReal_mul, Complex.re_ofReal_mul]
    suffices
      (∏ j ∈ Finset.range n, (1 - (x : ℂ) ^ 2 / ((j : ℂ) + 1) ^ 2) : ℂ) =
        (∏ j ∈ Finset.range n, (1 - x ^ 2 / ((j : ℝ) + 1) ^ 2) : ℝ) by
      rw [this, Complex.ofReal_re]
    simp
  · rw [← Complex.ofReal_mul, ← Complex.ofReal_sin, Complex.ofReal_re]

end EulerSine
