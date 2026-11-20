/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.NumberTheory.NumberField.DedekindZeta.EulerProduct
public import Mathlib.NumberTheory.NumberField.DirichletDensity

/-!
# Logarithmic normalization of Dirichlet density

The prime-ideal Dirichlet series is asymptotic to `log (1 / (s - 1))` as `s` tends to `1`
from above. Consequently the prime-ideal normalization in `HasDirichletDensity` agrees with
the usual logarithmic normalization. The logarithmic quotient uses the interval `1 < s < 2`,
where its denominator is positive.

## Main results

* `NumberField.Set.tendsto_primeIdealZetaSum_div_log` proves the asymptotic for the full
  prime-ideal sum.
* `NumberField.Set.hasDirichletDensity_iff_tendsto_div_log` identifies the two normalizations.
* `NumberField.Set.hasDirichletDensity_of_finite` gives density zero for finite sets of
  prime ideals.
-/

public section

noncomputable section

open Filter IsDedekindDomain Set

open scoped Topology

namespace NumberField

/-- The logarithmic normalization for Dirichlet density on the interval `1 < s < 2`. -/
@[expose] def dirichletDensityLogDenominator (s : Ioo (1 : ℝ) 2) : ℝ :=
  Real.log (Checked.div 1 ((s : ℝ) - 1) (sub_pos.mpr s.2.1).ne'.isUnit)

theorem dirichletDensityLogDenominator_pos (s : Ioo (1 : ℝ) 2) :
    0 < dirichletDensityLogDenominator s := by
  apply Real.log_pos
  rw [lt_div_iff₀ (sub_pos.mpr s.2.1), one_mul]
  linarith [s.2.2]

variable (K : Type*) [Field K] [NumberField K]

private theorem abs_neg_log_one_sub_sub_le {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1 / 2) :
    |-Real.log (1 - x) - x| ≤ 2 * x ^ 2 := by
  have hlt : |x| < 1 := by rw [abs_of_nonneg hx]; linarith
  have hsub : 0 < 1 - x := by linarith
  have h : |x + Real.log (1 - x)| ≤ x ^ 2 / (1 - x) := by
    simpa [abs_of_nonneg hx] using Real.abs_log_sub_add_sum_range_le hlt 1
  calc
    |-Real.log (1 - x) - x| = |x + Real.log (1 - x)| := by
      rw [← abs_neg]
      congr 1
      ring
    _ ≤ x ^ 2 / (1 - x) := h
    _ ≤ 2 * x ^ 2 := (div_le_iff₀ hsub).2 (by
      nlinarith [mul_nonneg (sq_nonneg x) (show 0 ≤ 1 - 2 * x by linarith)])

private theorem absNorm_prime_ge_two (𝔭 : HeightOneSpectrum (𝓞 K)) :
    (2 : ℝ) ≤ 𝔭.asIdeal.absNorm := by
  have h0 : 𝔭.asIdeal.absNorm ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr 𝔭.ne_bot
  have h1 : 𝔭.asIdeal.absNorm ≠ 1 := Ideal.absNorm_eq_one_iff.not.mpr 𝔭.isPrime.ne_top
  exact_mod_cast (show 2 ≤ 𝔭.asIdeal.absNorm by omega)

private theorem abs_neg_log_one_sub_absNorm_rpow_sub_le
    (𝔭 : HeightOneSpectrum (𝓞 K)) {s : ℝ} (hs : 1 ≤ s) :
    |-Real.log (1 - (𝔭.asIdeal.absNorm : ℝ) ^ (-s)) -
      (𝔭.asIdeal.absNorm : ℝ) ^ (-s)| ≤ 2 * (𝔭.asIdeal.absNorm : ℝ) ^ (-2 : ℝ) := by
  have hN := absNorm_prime_ge_two K 𝔭
  have hx : 0 ≤ (𝔭.asIdeal.absNorm : ℝ) ^ (-s) := by positivity
  have hx' : (𝔭.asIdeal.absNorm : ℝ) ^ (-s) ≤ 1 / 2 := by
    calc
      (𝔭.asIdeal.absNorm : ℝ) ^ (-s) ≤ (𝔭.asIdeal.absNorm : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (neg_le_neg hs)
      _ = (𝔭.asIdeal.absNorm : ℝ)⁻¹ := Real.rpow_neg_one _
        (hx := (zero_lt_two.trans_le hN).ne'.isUnit)
      _ ≤ 1 / 2 := by
        simpa using (inv_le_inv₀ (by linarith) (by norm_num : (0 : ℝ) < 2)).2 hN
  refine (abs_neg_log_one_sub_sub_le hx hx').trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  apply Real.rpow_le_rpow_of_exponent_le (by linarith)
  norm_num only [Nat.cast_ofNat]
  linarith

/-- The logarithmic normalization diverges as `s` tends to `1` from above. -/
private theorem tendsto_log_one_div_sub_one_nhdsGT :
    Tendsto dirichletDensityLogDenominator (comap Subtype.val (𝓝[>] 1)) atTop := by
  have hsub : Tendsto (fun s : ℝ ↦ s - 1) (𝓝[>] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa using (tendsto_nhdsWithin_of_tendsto_nhds
        (tendsto_id.sub_const (1 : ℝ)) :
          Tendsto (fun s : ℝ ↦ s - 1) (𝓝[>] 1) (𝓝 (1 - 1)))
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact sub_pos.mpr (show 1 < s from hs)
  have hsub' : Tendsto (fun s : Ioo (1 : ℝ) 2 ↦ (s : ℝ) - 1)
      (comap Subtype.val (𝓝[>] 1)) (𝓝[>] 0) := hsub.comp tendsto_comap
  have hinv := hsub'.fun_inv_tendsto_nhdsGT_zero
    (h0 := fun s ↦ (sub_pos.mpr s.2.1).ne'.isUnit)
  unfold dirichletDensityLogDenominator
  simpa only [one_div₀, Function.comp_def] using
    Real.tendsto_log_atTop.comp hinv

/-- The simple pole of the Dedekind zeta function gives its logarithmic asymptotic. -/
theorem tendsto_log_dedekindZeta_div_log :
    Tendsto (fun s : Ioo (1 : ℝ) 2 ↦ Checked.div (Real.log (dedekindZeta K s).re)
      (dirichletDensityLogDenominator s) (dirichletDensityLogDenominator_pos s).ne'.isUnit)
      (comap Subtype.val (𝓝[>] 1)) (𝓝 1) := by
  have hresReal : Tendsto (fun s : ℝ ↦ (s - 1) * (dedekindZeta K s).re)
      (𝓝[>] 1) (𝓝 (dedekindZetaResidue K)) := by
    simpa [Function.comp_def, Complex.mul_re] using
      Complex.continuous_re.continuousAt.tendsto.comp
      (tendsto_sub_one_mul_dedekindZeta_nhdsGT K)
  have hres : Tendsto (fun s : Ioo (1 : ℝ) 2 ↦ ((s : ℝ) - 1) * (dedekindZeta K s).re)
      (comap Subtype.val (𝓝[>] 1)) (𝓝 (dedekindZetaResidue K)) := hresReal.comp tendsto_comap
  have hlog := (hres.log (dedekindZetaResidue_ne_zero K)).div_atTop
    (h₀ := fun s ↦ (dirichletDensityLogDenominator_pos s).ne'.isUnit)
    tendsto_log_one_div_sub_one_nhdsGT
  have hsum := hlog.add_const 1
  rw [zero_add] at hsum
  apply hsum.congr'
  filter_upwards [hres.eventually_ne (dedekindZetaResidue_ne_zero K)] with s hs
  have hL : dirichletDensityLogDenominator s = -Real.log ((s : ℝ) - 1) := by
    rw [dirichletDensityLogDenominator, one_div₀, Real.log_inv]
  apply eq_div_iff.mpr
  rw [add_mul, div_mul_cancel₀, one_mul, Real.log_mul (mul_ne_zero_iff.mp hs).1
    (mul_ne_zero_iff.mp hs).2, hL]
  ring

namespace Set

open NumberField

/-- The higher prime-power terms in the logarithmic Euler product are uniformly bounded for
`s > 1` by twice the convergent prime-ideal sum at exponent `2`. -/
theorem abs_log_dedekindZeta_sub_primeIdealZetaSum_le {s : ℝ} (hs : 1 < s) :
    |Real.log (dedekindZeta K s).re -
      primeIdealZetaSum (univ : Set (HeightOneSpectrum (𝓞 K))) s| ≤
      2 * primeIdealZetaSum (univ : Set (HeightOneSpectrum (𝓞 K))) 2 := by
  rw [log_dedekindZeta_eq_tsum K hs]
  have hbound (𝔭 : HeightOneSpectrum (𝓞 K)) :=
    abs_neg_log_one_sub_absNorm_rpow_sub_le K 𝔭 hs.le
  have hmajor := (summable_primeIdealZeta K (s := 2) (by norm_num)).mul_left 2
  simp only [primeIdealZetaSum_def]
  rw [tsum_univ (fun 𝔭 : HeightOneSpectrum (𝓞 K) ↦ (𝔭.asIdeal.absNorm : ℝ) ^ (-s)),
    tsum_univ (fun 𝔭 : HeightOneSpectrum (𝓞 K) ↦ (𝔭.asIdeal.absNorm : ℝ) ^ (-2 : ℝ))]
  rw [← (summable_neg_log_one_sub_absNorm_rpow K hs).tsum_sub (summable_primeIdealZeta K hs)]
  simpa only [Real.norm_eq_abs, tsum_mul_left] using
    ((summable_neg_log_one_sub_absNorm_rpow K hs).sub (summable_primeIdealZeta K hs)).hasSum
      |>.norm_le_of_bounded hmajor.hasSum (fun 𝔭 ↦ by
        simpa only [Real.norm_eq_abs] using hbound 𝔭)

/-- The prime-ideal Dirichlet series is asymptotic to `log (1 / (s - 1))` at `1` from above. -/
theorem tendsto_primeIdealZetaSum_div_log :
    Tendsto (fun s : Ioo (1 : ℝ) 2 ↦ Checked.div
      (primeIdealZetaSum (univ : Set (HeightOneSpectrum (𝓞 K))) s)
      (dirichletDensityLogDenominator s) (dirichletDensityLogDenominator_pos s).ne'.isUnit)
      (comap Subtype.val (𝓝[>] 1)) (𝓝 1) := by
  have hrem : Tendsto (fun s : Ioo (1 : ℝ) 2 ↦ Checked.div
      (Real.log (dedekindZeta K s).re - primeIdealZetaSum (univ : Set (HeightOneSpectrum (𝓞 K))) s)
      (dirichletDensityLogDenominator s) (dirichletDensityLogDenominator_pos s).ne'.isUnit)
      (comap Subtype.val (𝓝[>] 1)) (𝓝 0) := by
    refine squeeze_zero_norm' ?_
      (tendsto_log_one_div_sub_one_nhdsGT.const_div_atTop
        (h₀ := fun s ↦ (dirichletDensityLogDenominator_pos s).ne'.isUnit)
        (2 * primeIdealZetaSum (univ : Set (HeightOneSpectrum (𝓞 K))) 2))
    refine Eventually.of_forall fun s ↦ ?_
    have hL := dirichletDensityLogDenominator_pos s
    simp only [Real.norm_eq_abs, div_eq_mul_inv₀, abs_mul, abs_of_pos (inv_pos_of_pos hL)]
    exact mul_le_mul_of_nonneg_right
      (abs_log_dedekindZeta_sub_primeIdealZetaSum_le K s.2.1) (inv_pos_of_pos hL).le
  have h := (tendsto_log_dedekindZeta_div_log K).sub hrem
  rw [sub_zero] at h
  refine h.congr fun s ↦ ?_
  rw [← sub_div, sub_sub_cancel]

variable {K} {S : Set (HeightOneSpectrum (𝓞 K))} {δ : ℝ}

/-- The prime-ideal and logarithmic normalizations define the same Dirichlet density. -/
theorem hasDirichletDensity_iff_tendsto_div_log :
    S.HasDirichletDensity δ ↔
      Tendsto (fun s : Ioo (1 : ℝ) 2 ↦ Checked.div (S.primeIdealZetaSum s)
        (dirichletDensityLogDenominator s) (dirichletDensityLogDenominator_pos s).ne'.isUnit)
        (comap Subtype.val (𝓝[>] 1)) (𝓝 δ) := by
  let inclusion : Ioo (1 : ℝ) 2 → Ioi (1 : ℝ) := fun s ↦ ⟨s, s.2.1⟩
  have hrange : range inclusion ∈ comap (Subtype.val : Ioi (1 : ℝ) → ℝ) (𝓝[>] 1) := by
    refine ⟨Ioo (1 : ℝ) 2, Ioo_mem_nhdsGT (by norm_num), ?_⟩
    intro s hs
    exact ⟨⟨s, hs⟩, rfl⟩
  rw [HasDirichletDensity, ← tendsto_comap'_iff hrange, comap_comap]
  constructor
  · intro h
    have hmul := h.mul (tendsto_primeIdealZetaSum_div_log K)
    rw [mul_one] at hmul
    exact hmul.congr fun s ↦ div_mul_div_cancel₀
  · intro h
    have hdiv := h.div₀ (tendsto_primeIdealZetaSum_div_log K) (hb := isUnit_one)
      (h₀ := fun s ↦ (div_pos (primeIdealZetaSum_univ_pos K s.2.1)
        (dirichletDensityLogDenominator_pos s)).ne'.isUnit)
    rw [div_one₀] at hdiv
    exact hdiv.congr fun s ↦ div_div_div_cancel_right₀ _ _

/-- Every finite set of prime ideals has Dirichlet density zero. -/
theorem hasDirichletDensity_of_finite (hS : S.Finite) : S.HasDirichletDensity 0 := by
  apply hasDirichletDensity_iff_tendsto_div_log.mpr
  refine squeeze_zero_norm' ?_
    (tendsto_log_one_div_sub_one_nhdsGT.const_div_atTop
      (h₀ := fun s ↦ (dirichletDensityLogDenominator_pos s).ne'.isUnit) (S.ncard : ℝ))
  refine Eventually.of_forall fun s ↦ ?_
  have hL := dirichletDensityLogDenominator_pos s
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (primeIdealZetaSum_nonneg S s) hL.le)]
  exact div_le_div_of_nonneg_right
    (primeIdealZetaSum_le_card_of_finite hS (zero_lt_one.trans s.2.1).le) hL.le

end Set

end NumberField
