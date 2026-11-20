/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler, Terence Tao
-/
module

public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.Harmonic.GammaDeriv
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.Calculus.DSlope

import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Tactic.LinearCombination

/-!
# Asymptotics of `ζ s` as `s → 1` or `s → 0`

The goal of this file is to evaluate the limit of `ζ s - 1 / (s - 1)` as `s → 1`.

### Main results

* `tendsto_riemannZeta_sub_one_div`: the limit of `ζ s - 1 / (s - 1)`, at the filter of punctured
  neighbourhoods of 1 in `ℂ`, exists and is equal to the Euler-Mascheroni constant `γ`.
* `deriv_riemannZeta_zero`: `ζ'(0) = -log(2π) / 2`, which derives from the above.
* Representation of `riemannZeta s` as `(s-1)⁻¹ + riemannZeta₀ s` or `(s-1)⁻¹ * riemannZeta₁ s`
  for certain entire functions `riemannZeta₀` and `riemannZeta₁`.
* Asymptotics for `deriv riemannZeta s`, `log (riemannZeta s)`,
  `(deriv riemannZeta s) / (riemannZeta s)` and `(riemannZeta s)⁻¹` as `s → 1`.
* `riemannZeta_conj`: conjugation symmetry on the exact domain `s ≠ 1`.

### Outline of arguments

We consider the sum of the positive-interval kernels, parametrized on the actual unit interval
by `t / (n + 1 + t) ^ (s + 1)`. We show that its sum `F s` is continuous on `[1, ∞)`,
that `F 1 = 1 - γ`, and that `F s = 1 / (s - 1) - ζ s / s` for `1 < s`.

By combining these formulae, one deduces that the limit of `ζ s - 1 / (s - 1)` at `𝓝[>] (1 : ℝ)`
exists and is equal to `γ`. The decomposition into an entire Hurwitz regular part and the
slope of the entire reciprocal Gamma factor gives the complex limit on the pole-excluding domain.
-/

@[expose] public section

open Set MeasureTheory Filter

open scoped Topology

@[inherit_doc] local notation "γ" => Real.eulerMascheroniConstant

namespace ZetaAsymptotics

-- since the intermediate lemmas are of little interest in themselves we put them in a namespace

open Real

/-!
## Definitions
-/

private lemma term_base_pos (n : ℕ) (t : Icc (0 : ℝ) 1) :
    0 < (n : ℝ) + 1 + (t : ℝ) := by
  have ht := t.2.1
  positivity

/-- The integrand of the nth positive summand, on its actual compact parameter interval. -/
noncomputable def termIntegrand (n : ℕ) (s : ℝ) (t : Icc (0 : ℝ) 1) : ℝ :=
  Checked.div (t : ℝ) (((n : ℝ) + 1 + (t : ℝ)) ^ (s + 1))
    (by exact (rpow_pos_of_pos (term_base_pos n t) _).ne'.isUnit)

private lemma continuous_termIntegrand (n : ℕ) (s : ℝ) :
    Continuous (termIntegrand n s) := by
  apply Continuous.div₀
    (h₀ := fun t ↦ (rpow_pos_of_pos (term_base_pos n t) (s + 1)).ne'.isUnit)
    continuous_subtype_val
  exact (continuous_const.add continuous_subtype_val).rpow_const
    (fun t ↦ Or.inl (term_base_pos n t).ne')

/-- The nth positive summand in the integral representation used for zeta asymptotics.
The path `x = n + 1 + t` has endpoints `n + 1` and `n + 2`;
its unit-interval parametrization keeps every denominator in its exact positive domain. -/
noncomputable def term (n : ℕ) (s : ℝ) : ℝ :=
  ∫ t : Icc (0 : ℝ) 1, termIntegrand n s t ∂(volume.comap Subtype.val)

/-- The first `N` positive summands. -/
noncomputable def termSum (s : ℝ) (N : ℕ) : ℝ := ∑ n ∈ Finset.range N, term n s

/-- Topological sum of the positive summands. -/
noncomputable def termTSum (s : ℝ) : ℝ := ∑' n, term n s

private lemma termIntegrand_nonneg (n : ℕ) (s : ℝ) (t : Icc (0 : ℝ) 1) :
    0 ≤ termIntegrand n s t :=
  div_nonneg t.2.1 (rpow_pos_of_pos (term_base_pos n t) _).le

lemma term_nonneg (n : ℕ) (s : ℝ) : 0 ≤ term n s :=
  integral_nonneg (fun t ↦ termIntegrand_nonneg n s t)

lemma term_welldef (n : ℕ) (s : ℝ) :
    Integrable (termIntegrand n s) (volume.comap Subtype.val) := by
  let _ : IsFiniteMeasureOnCompacts
      (volume.comap (Subtype.val : Icc (0 : ℝ) 1 → ℝ)) :=
    IsFiniteMeasureOnCompacts.comap' volume continuous_subtype_val
      (MeasurableEmbedding.subtype_coe measurableSet_Icc)
  exact (continuous_termIntegrand n s).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

section s_eq_one

/-!
## Evaluation of the sum for `s = 1`
-/

lemma term_one (n : ℕ) :
    term n 1 = (log (n + 2) - log (n + 1)) - 1 / (n + 2) := by
  let F : Ioi (0 : ℝ) → ℝ := fun x ↦
    log (x : ℝ) + Checked.div ((n : ℝ) + 1) (x : ℝ) x.2.ne'.isUnit
  let path : Icc (0 : ℝ) 1 → Ioi (0 : ℝ) :=
    fun t ↦ ⟨(n : ℝ) + 1 + t, term_base_pos n t⟩
  have hpath : Continuous path :=
    (continuous_const.add continuous_subtype_val).subtype_mk _
  have hderiv (t : Icc (0 : ℝ) 1) :
      HasDerivAt F (termIntegrand n 1 t) (path t) (fun x ↦ (x : ℝ)) := by
    have hx : 0 < (path t : ℝ) := (path t).2
    have hlog : HasDerivAt (fun x : Ioi (0 : ℝ) ↦ log (x : ℝ))
        (path t : ℝ)⁻¹ (path t) (fun x ↦ (x : ℝ)) :=
      HasFDerivAtFilter.comp_tendsto (hasDerivAt_log (hx := hx.ne'.isUnit)).hasFDerivAt Subtype.val
        ((continuous_subtype_val.tendsto (path t)).prodMap (tendsto_pure_pure ..))
    let φ : Ioi (0 : ℝ) → {x : ℝ // IsUnit x} := fun x ↦ ⟨x, x.2.ne'.isUnit⟩
    have hu := hx.ne'.isUnit
    have hq := (hasDerivAt_const (path t : ℝ) ((n : ℝ) + 1)).div
      (hasDerivAt_id (path t : ℝ)) hu
    have hq' : HasDerivAt (fun x : Ioi (0 : ℝ) ↦
        Checked.div ((n : ℝ) + 1) (x : ℝ) x.2.ne'.isUnit)
        (Checked.div (-((n : ℝ) + 1)) ((path t : ℝ) ^ 2) (hu.pow 2)) (path t)
        (fun x ↦ (x : ℝ)) := by
      rw [hasDerivAt_iff_hasFDerivAt, Checked.div, hu.unit_pow 2]
      simpa only [HasFDerivAt, Function.comp_def, φ, Checked.div, zero_mul, mul_one, zero_sub] using
        HasFDerivAtFilter.comp_tendsto hq.hasFDerivAt φ
          ((((continuous_subtype_val.subtype_mk _) : Continuous φ).tendsto (path t)).prodMap
            (tendsto_pure_pure ..))
    let d := Checked.div (-((n : ℝ) + 1)) ((path t : ℝ) ^ 2) (hu.pow 2)
    have hd : termIntegrand n 1 t = (path t : ℝ)⁻¹ + d := by
      dsimp [termIntegrand, path, d]
      simp only [one_add_one_eq_two, Real.rpow_two]
      field_simp
      ring
    have hsum : ContinuousLinearMap.toSpanSingleton ℝ (termIntegrand n 1 t) =
        ContinuousLinearMap.toSpanSingleton ℝ (path t : ℝ)⁻¹ +
          ContinuousLinearMap.toSpanSingleton ℝ d := by
      rw [hd]
      ext
      simp only [ContinuousLinearMap.toSpanSingleton_apply, add_apply, smul_add]
    rw [hasDerivAt_iff_hasFDerivAt, hsum]
    exact hlog.hasFDerivAt.add hq'.hasFDerivAt
  have h := intervalIntegral.integral_unitInterval_deriv_eq_sub
    (f := F) (coord := fun x ↦ (x : ℝ)) («γ» := path)
    (z₀ := (n : ℝ) + 1) (z₁ := 1) (continuous_termIntegrand n 1) hderiv
    (hpath := hpath) (hcoord := by intro t; simp [path, smul_eq_mul])
  calc
    term n 1 = F (path ⟨1, zero_le_one, le_rfl⟩) - F (path ⟨0, le_rfl, zero_le_one⟩) := by
      change term n 1 = F (path 1) - F (path 0)
      simpa only [term, one_smul] using h
    _ = (log (n + 2) - log (n + 1)) - 1 / (n + 2) := by
      dsimp [F, path]
      have hn : (0 : ℝ) < n + 1 := by positivity
      have hn' : (0 : ℝ) < n + 2 := by positivity
      simp only [add_zero]
      have he : (n : ℝ) + 1 + 1 = n + 2 := by ring
      simp only [he, div_self]
      field

lemma termSum_one (N : ℕ) : termSum 1 N = log (N + 1) - harmonic (N + 1) + 1 := by
  induction N with
  | zero =>
    simp [termSum, harmonic_succ, harmonic_zero, inv_one₀]
  | succ N hN =>
    unfold termSum at hN ⊢
    rw [Finset.sum_range_succ, hN, harmonic_succ (N + 1),
      term_one N]
    push_cast
    ring_nf

@[deprecated (since := "2026-05-27")] alias term_sum_one := termSum_one

/-- The topological sum of `ZetaAsymptotics.term n 1` over all `n : ℕ` is `1 - γ`. This is
proved by directly evaluating the sum of the first `N` terms and using the limit definition of `γ`.
-/
lemma term_tsum_one : HasSum (fun n ↦ term n 1) (1 - γ) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun n ↦ term_nonneg n 1)]
  change Tendsto (fun N ↦ termSum 1 N) atTop _
  simp_rw [termSum_one, sub_eq_neg_add]
  refine Tendsto.add ?_ tendsto_const_nhds
  have := (tendsto_eulerMascheroniSeq'.comp (tendsto_add_atTop_nat 1)).neg
  refine this.congr' (Eventually.of_forall (fun n ↦ ?_))
  simp_rw [Function.comp_apply, eulerMascheroniSeq', reduceCtorEq, ite_false]
  push_cast
  abel

end s_eq_one

section s_gt_one

/-!
## Evaluation of the sum for `1 < s`
-/

lemma term_of_lt (n : ℕ) {s : ℝ} (hs : 1 < s) :
    term n s = 1 / (s - 1) * (1 / (n + 1 : ℝ) ^ (s - 1) - 1 / (n + 2 : ℝ) ^ (s - 1))
      - (n + 1) / s * (1 / (n + 1 : ℝ) ^ s - 1 / (n + 2 : ℝ) ^ s) := by
  have hs0 : 0 < s := zero_lt_one.trans hs
  let F : Ioi (0 : ℝ) → ℝ := fun x ↦
    -(1 / (s - 1)) * (x : ℝ) ^ (-(s - 1)) + ((n : ℝ) + 1) / s * (x : ℝ) ^ (-s)
  let path : Icc (0 : ℝ) 1 → Ioi (0 : ℝ) :=
    fun t ↦ ⟨(n : ℝ) + 1 + t, term_base_pos n t⟩
  have hpath : Continuous path :=
    (continuous_const.add continuous_subtype_val).subtype_mk _
  have hderiv (t : Icc (0 : ℝ) 1) :
      HasDerivAt F (termIntegrand n s t) (path t) (fun x ↦ (x : ℝ)) := by
    have hx : 0 < (path t : ℝ) := (path t).2
    have hF := ((hasDerivAt_rpow_const (x := (path t : ℝ)) (p := -(s - 1))
      (Or.inl hx.ne')).const_mul (-(1 / (s - 1)))).add
      ((hasDerivAt_rpow_const (x := (path t : ℝ)) (p := -s)
        (Or.inl hx.ne')).const_mul (((n : ℝ) + 1) / s))
    have hF' : HasDerivAt F _ (path t) (fun x ↦ (x : ℝ)) :=
      HasFDerivAtFilter.comp_tendsto hF.hasFDerivAt Subtype.val
        ((continuous_subtype_val.tendsto (path t)).prodMap (tendsto_pure_pure ..))
    convert hF' using 1
    dsimp [termIntegrand, path]
    have h₁ : -(s - 1) - 1 = -s := by ring
    have h₂ : -s - 1 = -(s + 1) := by ring
    rw [h₁, h₂, rpow_neg hx.le s (hxy := (rpow_pos_of_pos hx s).ne'.isUnit),
      rpow_neg hx.le (s + 1) (hxy := (rpow_pos_of_pos hx (s + 1)).ne'.isUnit)]
    simp only [path, rpow_add_one (term_base_pos n t).ne']
    field_simp
    ring
  have h := intervalIntegral.integral_unitInterval_deriv_eq_sub
    (f := F) (coord := fun x ↦ (x : ℝ)) («γ» := path)
    (z₀ := (n : ℝ) + 1) (z₁ := 1) (continuous_termIntegrand n s) hderiv
    (hpath := hpath) (hcoord := by intro t; simp [path, smul_eq_mul])
  calc
    term n s = F (path ⟨1, zero_le_one, le_rfl⟩) - F (path ⟨0, le_rfl, zero_le_one⟩) := by
      change term n s = F (path 1) - F (path 0)
      simpa only [term, one_smul] using h
    _ = _ := by
      dsimp [F, path]
      have h₁ : (0 : ℝ) < n + 1 := by positivity
      have h₂ : (0 : ℝ) < n + 1 + 1 := by positivity
      simp only [add_zero,
        rpow_neg h₁.le (s - 1) (hxy := (rpow_pos_of_pos h₁ (s - 1)).ne'.isUnit),
        rpow_neg h₁.le s (hxy := (rpow_pos_of_pos h₁ s).ne'.isUnit),
        rpow_neg h₂.le (s - 1) (hxy := (rpow_pos_of_pos h₂ (s - 1)).ne'.isUnit),
        rpow_neg h₂.le s (hxy := (rpow_pos_of_pos h₂ s).ne'.isUnit)]
      have he : (n : ℝ) + 1 + 1 = n + 2 := by ring
      simp only [he, one_div₀]
      ring

lemma termSum_of_lt (N : ℕ) {s : ℝ} (hs : 1 < s) :
    termSum s N = 1 / (s - 1) * (1 - 1 / (N + 1) ^ (s - 1))
    - 1 / s * ((∑ n ∈ Finset.range N, 1 / (n + 1 : ℝ) ^ s) - N / (N + 1) ^ s) := by
  have hs0 : 0 < s := zero_lt_one.trans hs
  simp only [termSum]
  conv => enter [1, 2, n]; rw [term_of_lt n hs]
  rw [Finset.sum_sub_distrib]
  congr 1
  · induction N with
    | zero => simp
    | succ N hN =>
      rw [Finset.sum_range_succ, hN]
      simp only [Nat.cast_add_one, add_assoc, one_add_one_eq_two]
      ring
  · have hmul (n : ℕ) (x : ℝ) : (n + 1) / s * x = 1 / s * ((n + 1) * x) := by
      rw [div_eq_inv_mul₀ _ s, one_div₀ s, mul_assoc]
    simp_rw [hmul, ← Finset.mul_sum]
    congr 1
    simp_rw [div_eq_mul_inv₀, one_mul]
    induction N with
    | zero => simp
    | succ N hN =>
      rw [Finset.sum_range_succ, hN, Finset.sum_range_succ]
      simp only [Nat.cast_add_one, add_assoc, one_add_one_eq_two]
      ring

@[deprecated (since := "2026-05-27")] alias term_sum_of_lt := termSum_of_lt

/-- For `1 < s`, the topological sum of `ZetaAsymptotics.term n s` over all `n : ℕ` is
`1 / (s - 1) - ζ s / s`.
-/
lemma termTSum_of_lt {s : ℝ} (hs : 1 < s) :
    termTSum s = (1 / (s - 1) - 1 / s * ∑' n : ℕ, 1 / (n + 1 : ℝ) ^ s) := by
  apply HasSum.tsum_eq
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun n ↦ term_nonneg n s)]
  change Tendsto (fun N ↦ termSum s N) atTop _
  simp_rw [termSum_of_lt _ hs]
  apply Tendsto.sub
  · rw [show 𝓝 (1 / (s - 1)) = 𝓝 (1 / (s - 1) - 1 / (s - 1) * 0) by simp]
    simp_rw [mul_sub, mul_one]
    refine tendsto_const_nhds.sub (Tendsto.const_mul _ ?_)
    refine tendsto_const_nhds.div_atTop <| (tendsto_rpow_atTop (by linarith)).comp ?_
    exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  · rw [← sub_zero (tsum _)]
    apply (((Summable.hasSum ?_).tendsto_sum_nat).sub ?_).const_mul
    · exact Real.summable_one_div_nat_add_one_rpow.mpr hs
    · apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
              (h := fun n : ℕ ↦ (1 / ↑(n + 1) : ℝ) ^ (s - 1))
      · rw [show 𝓝 (0 : ℝ) = 𝓝 (0 ^ (s - 1)) by rw [zero_rpow]; linarith]
        refine Tendsto.rpow_const ?_ (Or.inr <| by linarith)
        exact tendsto_const_nhds.div_atTop
          (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
      · intro n
        positivity
      · intro n
        dsimp only
        transitivity (n + 1) / (n + 1) ^ s
        · gcongr
          linarith
        · apply le_of_eq
          let a := (n : ℝ) + 1
          have ha : 0 < a := by dsimp [a]; positivity
          have ha_s : 0 < a ^ s := rpow_pos_of_pos ha _
          have ha_sub : 0 < a ^ (s - 1) := rpow_pos_of_pos ha _
          simp only [Nat.cast_add_one]
          change a / a ^ s = (1 / a) ^ (s - 1)
          calc
            _ = (a ^ (s - 1))⁻¹ := by
              apply eq_inv_of_mul_eq_one_right₀
              rw [← mul_div_assoc₀, rpow_sub_one ha.ne' s, div_mul_cancel₀, div_self]
            _ = _ := by rw [one_div₀, inv_rpow ha.le]

@[deprecated (since := "2026-05-27")] alias term_tsum_of_lt := termTSum_of_lt

/-- Reformulation of `ZetaAsymptotics.termTSum_of_lt` which is useful for some computations
below. -/
lemma zeta_limit_aux1 {s : ℝ} (hs : 1 < s) :
    (∑' n : ℕ, 1 / (n + 1 : ℝ) ^ s) - 1 / (s - 1) = 1 - s * termTSum s := by
  rw [termTSum_of_lt hs]
  generalize (∑' n : ℕ, 1 / (n + 1 : ℝ) ^ s) = Z
  field [(show s - 1 ≠ 0 by linarith)]

end s_gt_one

section continuity

/-!
## Continuity of the sum
-/

private lemma termIntegrand_le (n : ℕ) {s : ℝ} (hs : 1 ≤ s)
    (t : Icc (0 : ℝ) 1) : termIntegrand n s t ≤ termIntegrand n 1 t := by
  have hb : 1 ≤ (n : ℝ) + 1 + (t : ℝ) := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith [t.2.1]
  have he : (1 : ℝ) + 1 ≤ s + 1 := by linarith
  dsimp only [termIntegrand]
  exact div_le_div_of_nonneg_left t.2.1 (rpow_pos_of_pos (term_base_pos n t) _)
    (rpow_le_rpow_of_exponent_le hb he)

lemma continuousOn_term (n : ℕ) : ContinuousOn (term n) (Ici 1) := by
  unfold term
  apply continuousOn_of_dominated (bound := termIntegrand n 1)
  · exact fun s _ ↦ (term_welldef n s).aestronglyMeasurable
  · intro s hs
    filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_nonneg (termIntegrand_nonneg n s t)]
    exact termIntegrand_le n hs t
  · exact term_welldef n 1
  · filter_upwards with t
    apply Continuous.continuousOn
    apply Continuous.div₀
      (h₀ := fun s ↦ (rpow_pos_of_pos (term_base_pos n t) (s + 1)).ne'.isUnit)
      continuous_const
    exact continuous_const.rpow (continuous_id.add continuous_const)
      (fun _ ↦ Or.inl (term_base_pos n t).ne')

lemma continuousOn_termTSum : ContinuousOn termTSum (Ici 1) := by
  refine continuousOn_tsum (fun n ↦ continuousOn_term n) term_tsum_one.summable
    (fun n s hs ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (term_nonneg n s)]
  exact integral_mono (term_welldef n s) (term_welldef n 1) (termIntegrand_le n hs)

@[deprecated (since := "2026-05-27")] alias continuousOn_term_tsum := continuousOn_termTSum

/-- The zeta constant term along real arguments approaching one from above. -/
lemma tendsto_riemannZeta_sub_one_div_nhds_right :
    Tendsto (fun s : Ioi (1 : ℝ) ↦
      riemannZeta (s : ℝ) (hs := by exact_mod_cast (show 1 < (s : ℝ) from s.2).ne') -
        Checked.div 1 ((s : ℂ) - 1) (by
          exact (sub_ne_zero.mpr (by exact_mod_cast (show 1 < (s : ℝ) from s.2).ne')).isUnit))
      (comap Subtype.val (𝓝 1)) (𝓝 (γ : ℂ)) := by
  have hval : Tendsto (Subtype.val : Ioi (1 : ℝ) → ℝ)
      (comap Subtype.val (𝓝 1)) (𝓝[Ici 1] 1) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_comap, .of_forall (fun s ↦ by
      exact le_of_lt (show 1 < (s : ℝ) from s.2))⟩
  have ht : Tendsto termTSum (𝓝[Ici 1] 1) (𝓝 (termTSum 1)) :=
    continuousOn_termTSum.continuousWithinAt self_mem_Ici
  have hterm := ht.comp hval
  have hlim : Tendsto (fun s : Ioi (1 : ℝ) ↦ 1 - (s : ℝ) * termTSum s)
      (comap Subtype.val (𝓝 1)) (𝓝 (1 - 1 * termTSum 1)) :=
    tendsto_const_nhds.sub (tendsto_comap.mul hterm)
  have hγ : 1 - termTSum 1 = γ := by
    rw [termTSum, term_tsum_one.tsum_eq]
    ring
  have hlim' : Tendsto (fun s : Ioi (1 : ℝ) ↦ 1 - (s : ℝ) * termTSum s)
      (comap Subtype.val (𝓝 1)) (𝓝 γ) := by
    simpa only [one_mul, hγ] using hlim
  apply ((Complex.continuous_ofReal.tendsto γ).comp hlim').congr
  intro s
  rw [Function.comp_apply, ← zeta_limit_aux1 s.2]
  simp only [Complex.ofReal_sub, Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_tsum]
  have hs : 1 < ((s : ℝ) : ℂ).re := by
    rw [Complex.ofReal_re]
    exact s.2
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
  congr 1
  apply tsum_congr
  intro n
  have hcast : (((((n : ℝ) + 1) ^ (s : ℝ)) : ℝ) : ℂ) = ((n : ℂ) + 1) ^ (s : ℂ) := by
    rw [Complex.ofReal_cpow (by positivity), Complex.ofReal_add, Complex.ofReal_natCast,
      Complex.ofReal_one]
  apply (eq_div_iff).mpr
  rw [← hcast, div_mul_cancel₀]

open Complex

/-- The function `ζ s - 1 / (s - 1)` tends to `γ` on the actual pole-excluding domain. -/
theorem _root_.tendsto_riemannZeta_sub_one_div :
    Tendsto (fun s : {s : ℂ // s ≠ 1} ↦
      riemannZeta s (hs := s.2) - 1 / ((s : ℂ) - 1))
      (comap Subtype.val (𝓝 1)) (𝓝 (γ : ℂ)) := by
  let C : ℂ := HurwitzZeta.hurwitzZetaEvenRegularPart 0 1 + deriv reciprocalGammaℝ 1
  have hR := ((HurwitzZeta.differentiable_hurwitzZetaEvenRegularPart 0).continuous.tendsto 1).comp
    (tendsto_comap : Tendsto (Subtype.val : {s : ℂ // s ≠ 1} → ℂ) _ (𝓝 1))
  have hG := (differentiable_reciprocalGammaℝ 1).hasDerivAt.tendsto_slope
  have hfull : Tendsto (fun s : {s : ℂ // s ≠ 1} ↦
      riemannZeta s (hs := s.2) - 1 / ((s : ℂ) - 1))
      (comap Subtype.val (𝓝 1)) (𝓝 C) := by
    apply (hR.add hG).congr
    intro s
    simp only [Function.comp_def, slope_fun_def_field, reciprocalGammaℝ_one,
      riemannZeta, HurwitzZeta.hurwitzZetaEven_eq_regularPart_add s.2]
    field
  let φ : Ioi (1 : ℝ) → {s : ℂ // s ≠ 1} :=
    fun s ↦ ⟨(s : ℝ), by exact_mod_cast s.2.ne'⟩
  have hφ : Tendsto φ (comap Subtype.val (𝓝 1)) (comap Subtype.val (𝓝 1)) :=
    tendsto_comap_iff.mpr ((Complex.continuous_ofReal.tendsto 1).comp tendsto_comap)
  have : NeBot (comap (Subtype.val : Ioi (1 : ℝ) → ℝ) (𝓝 1)) :=
    mem_closure_iff_comap_neBot.mp (by simp)
  have hC : C = (γ : ℂ) :=
    tendsto_nhds_unique (hfull.comp hφ) tendsto_riemannZeta_sub_one_div_nhds_right
  exact hC ▸ hfull

lemma _root_.isBigO_riemannZeta_sub_one_div {F : Type*} [Norm F] [One F] [NormOneClass F] :
    (fun s : {s : ℂ // s ≠ 1} ↦ riemannZeta s (hs := s.2) - 1 / ((s : ℂ) - 1))
      =O[comap Subtype.val (𝓝 1)] (fun _ ↦ (1 : F)) :=
  tendsto_riemannZeta_sub_one_div.isBigO_one F

end continuity

section val_at_one

open Complex

lemma tendsto_Gamma_term_aux :
    Tendsto (fun s : {s : ℂ // s ≠ 1} ↦
      1 / ((s : ℂ) - 1) - reciprocalGammaℝ s / ((s : ℂ) - 1))
      (comap Subtype.val (𝓝 1)) (𝓝 (-(γ + Complex.log (4 * ↑π)) / 2)) := by
  have h := hasDerivAt_reciprocalGammaℝ_one.tendsto_slope.neg
  rw [← neg_div₀] at h
  apply h.congr
  intro s
  simp only [slope_fun_def_field, reciprocalGammaℝ_one]
  field

lemma tendsto_riemannZeta_sub_one_div_Gammaℝ :
    Tendsto (fun s : {s : ℂ // s ≠ 1} ↦
      riemannZeta s (hs := s.2) - reciprocalGammaℝ s / ((s : ℂ) - 1))
      (comap Subtype.val (𝓝 1)) (𝓝 ((γ - Complex.log (4 * ↑π)) / 2)) := by
  have h := tendsto_riemannZeta_sub_one_div.add tendsto_Gamma_term_aux
  convert h using 1
  · funext s
    ring
  · congr 1
    ring

end val_at_one

end ZetaAsymptotics

open Complex

open scoped Real ComplexConjugate

/-- The value at one of the entire completed zeta with its principal parts removed. -/
lemma completedRiemannZeta₀_one : completedRiemannZeta₀ 1 = (γ - log (4 * ↑π)) / 2 + 1 := by
  have : NeBot (comap (Subtype.val : {s : ℂ // s ≠ 1} → ℂ) (𝓝 1)) :=
    mem_closure_iff_comap_neBot.mp ((dense_compl_singleton (1 : ℂ)) 1)
  have hR := tendsto_nhds_unique
    (HurwitzZeta.tendsto_hurwitzZetaEven_sub_principalPart_nhds_one 0)
    ZetaAsymptotics.tendsto_riemannZeta_sub_one_div_Gammaℝ
  have hG : reciprocalGammaℝ (1 + 2) / 2 / π = 1 := by
    simpa only [reciprocalGammaℝ_one, one_mul] using
      (reciprocalGammaℝ_eq_self_mul_reciprocalGammaℝ_add_two 1).symm
  simp only [HurwitzZeta.hurwitzZetaEvenRegularPart, HurwitzZeta.completedHurwitzZetaEven₀_zero,
    ite_true, reciprocalGammaℝ_one, one_mul, mul_one, hG] at hR
  linear_combination hR

/-- The entire normalization `(s - 1) * ζ(s)`, including its residue value at one. -/
noncomputable def riemannZeta₁ (s : ℂ) : ℂ :=
  (s - 1) * HurwitzZeta.hurwitzZetaEvenRegularPart 0 s + reciprocalGammaℝ s

@[fun_prop]
lemma differentiable_riemannZeta₁ : Differentiable ℂ riemannZeta₁ :=
  ((differentiable_id.sub_const 1).mul
    (HurwitzZeta.differentiable_hurwitzZetaEvenRegularPart 0)).add
    differentiable_reciprocalGammaℝ

@[simp]
lemma riemannZeta₁_one : riemannZeta₁ 1 = 1 := by simp [riemannZeta₁]

lemma riemannZeta_eq_inv_sub_mul {s : ℂ} (hs : s ≠ 1) :
    riemannZeta s = (s - 1)⁻¹ * riemannZeta₁ s := by
  rw [riemannZeta, HurwitzZeta.hurwitzZetaEven_eq_regularPart_add hs, riemannZeta₁]
  field

@[simp]
lemma deriv_riemannZeta₁_one : deriv riemannZeta₁ 1 = γ := by
  have hG : reciprocalGammaℝ (1 + 2) / 2 / π = 1 := by
    simpa only [reciprocalGammaℝ_one, one_mul] using
      (reciprocalGammaℝ_eq_self_mul_reciprocalGammaℝ_add_two 1).symm
  have hR : HurwitzZeta.hurwitzZetaEvenRegularPart 0 1 = (γ - log (4 * π)) / 2 := by
    simp only [HurwitzZeta.hurwitzZetaEvenRegularPart, ite_true, one_mul,
      HurwitzZeta.completedHurwitzZetaEven₀_zero, reciprocalGammaℝ_one, mul_one,
      completedRiemannZeta₀_one, hG]
    ring
  have h := (((hasDerivAt_id' (1 : ℂ)).sub_const 1).fun_mul
    (HurwitzZeta.differentiable_hurwitzZetaEvenRegularPart 0 1).hasDerivAt).fun_add
    hasDerivAt_reciprocalGammaℝ_one
  calc
    deriv riemannZeta₁ 1 = HurwitzZeta.hurwitzZetaEvenRegularPart 0 1 +
        (γ + log (4 * π)) / 2 := by
      unfold riemannZeta₁
      exact h.deriv.trans (by simp)
    _ = γ := by rw [hR]; ring

/-- Conjugation symmetry on the exact domain of the Riemann zeta function. -/
@[simp]
theorem riemannZeta_conj (s : ℂ) {hs : s ≠ 1} :
    riemannZeta (conj s)
      (hs := (map_ne_one_iff _ (starRingEnd ℂ).injective).mpr hs) = conj (riemannZeta s) := by
  have hz₁ {z : ℂ} (hz : 1 < z.re) : z ≠ 1 := by
    rintro rfl
    simp at hz
  have hζ (z : ℂ) (hz : 1 < z.re) :
      conj (riemannZeta (conj z) (hz₁ (by rwa [conj_re]))) = riemannZeta z (hz₁ hz) := by
    rw [zeta_eq_tsum_one_div_nat_cpow (by rwa [conj_re]), conj_tsum,
      zeta_eq_tsum_one_div_nat_cpow hz]
    apply tsum_congr
    intro n
    have hp : conj (((n : ℕ) : ℂ) ^ conj z) = ((n : ℕ) : ℂ) ^ z := by
      rw [← conj_cpow _ _ (by rw [natCast_arg (n := (n : ℕ))]; positivity), conj_natCast]
    simp only [map_div₀, map_one, hp]
  have hnorm (z : ℂ) (hz : z ≠ 1) : riemannZeta₁ z = (z - 1) * riemannZeta z := by
    rw [riemannZeta_eq_inv_sub_mul hz]
    field
  have hg : Differentiable ℂ (fun z ↦ conj (riemannZeta₁ (conj z))) :=
    fun z ↦ differentiableAt_conj_conj_iff.mpr (differentiable_riemannZeta₁ (conj z))
  have hgz (z : ℂ) (hz : 1 < z.re) : conj (riemannZeta₁ (conj z)) = riemannZeta₁ z := by
    have hz1 : z ≠ 1 := hz₁ hz
    rw [hnorm z hz1, hnorm (conj z)
      ((map_ne_one_iff _ (starRingEnd ℂ).injective).mpr hz1), map_mul, map_sub, map_one,
      conj_conj, hζ z hz]
  have heq : EqOn (fun z ↦ conj (riemannZeta₁ (conj z))) riemannZeta₁ univ :=
    (hg.differentiableOn.analyticOnNhd isOpen_univ).eqOn_of_preconnected_of_eventuallyEq
      (differentiable_riemannZeta₁.differentiableOn.analyticOnNhd isOpen_univ)
      isPreconnected_univ (mem_univ (2 : ℂ))
      (eventuallyEq_of_mem
        ((isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num)) hgz)
  have hconj : riemannZeta₁ (conj s) = conj (riemannZeta₁ s) := by
    simpa using congrArg (starRingEnd ℂ) (heq (mem_univ s))
  rw [riemannZeta_eq_inv_sub_mul hs, riemannZeta_eq_inv_sub_mul
    ((map_ne_one_iff _ (starRingEnd ℂ).injective).mpr hs)]
  simp [hconj, map_inv₀]

lemma riemannZeta_eventually_ne_zero_nhds_one :
    ∀ᶠ s : {s : ℂ // s ≠ 1} in comap Subtype.val (𝓝 1), riemannZeta s (hs := s.2) ≠ 0 := by
  filter_upwards [riemannZeta_residue_one.eventually_ne one_ne_zero] with s hs
  exact (mul_ne_zero_iff.mp hs).2

lemma completedRiemannZeta₀_zero : completedRiemannZeta₀ 0 = (γ - Complex.log (4 * π)) / 2 + 1 := by
  rw [← completedRiemannZeta₀_one_sub]
  simp [completedRiemannZeta₀_one]

private lemma hasDerivAt_restrict_zetaDomain
    {f : ℂ → ℂ} {d : ℂ} {s : {z : ℂ // z ≠ 1}} (h : HasDerivAt f d (s : ℂ)) :
    HasDerivAt (fun z : {z : ℂ // z ≠ 1} ↦ f z) d s Subtype.val :=
  hasDerivAt_iff_hasFDerivAt.mpr <|
    h.hasFDerivAt.comp_tendsto Subtype.val
      ((continuous_subtype_val.tendsto s).prodMap (tendsto_pure_pure Subtype.val s))

/-- The derivative of zeta, on its actual domain, at zero is `-log(2π) / 2`. -/
theorem deriv_riemannZeta_zero :
    deriv (fun z : {z : ℂ // z ≠ 1} ↦ riemannZeta z (hs := z.2))
      ⟨0, zero_ne_one⟩ (fun z ↦ (z : ℂ)) = -log (2 * π) / 2 := by
  let D := {z : ℂ // z ≠ 1}
  let z₀ : D := ⟨0, zero_ne_one⟩
  let A : D → ℂ := fun z ↦
    (z : ℂ) * completedRiemannZeta₀ z - 1 - (z : ℂ) / (1 - (z : ℂ))
  let B : ℂ → ℂ := fun z ↦ (π : ℂ) ^ (z / 2) * reciprocalGamma (z / 2 + 1) / 2
  have hp : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hP : HasDerivAt (fun z : ℂ ↦ z * completedRiemannZeta₀ z - 1)
      (completedRiemannZeta₀ 0) 0 := by
    simpa only [id_eq, zero_mul, one_mul, add_zero] using
      (((hasDerivAt_id (0 : ℂ)).fun_mul (differentiable_completedZeta₀ 0).hasDerivAt).sub_const 1)
  have hP' : HasDerivAt (fun z : D ↦ (z : ℂ) * completedRiemannZeta₀ z - 1)
      (completedRiemannZeta₀ 0) z₀ Subtype.val := hasDerivAt_restrict_zetaDomain (s := z₀) hP
  let φ : D → {z : ℂ // IsUnit (1 - z)} :=
    fun z ↦ ⟨z, (sub_ne_zero.mpr z.2.symm).isUnit⟩
  have hQ := (hasDerivAt_id (0 : ℂ)).div
    ((hasDerivAt_const 0 (1 : ℂ)).sub (hasDerivAt_id 0)) (by simp)
  have hQ' : HasDerivAt (fun z : D ↦ (z : ℂ) / (1 - (z : ℂ))) 1 z₀
      (fun z ↦ (z : ℂ)) := by
    apply hasDerivAt_iff_hasFDerivAt.mpr
    change HasFDerivAtFilter _ _ (𝓝 z₀ ×ˢ pure z₀) Subtype.val
    simpa [Pi.sub_apply, Checked.div, Function.comp_def, φ, z₀] using
      HasFDerivAtFilter.comp_tendsto hQ.hasFDerivAt φ
        ((((continuous_subtype_val.subtype_mk _) : Continuous φ).tendsto z₀).prodMap
          (tendsto_pure_pure φ z₀))
  have hA : HasDerivAt A (completedRiemannZeta₀ 0 - 1) z₀ Subtype.val := by
    simpa only [sub_apply, ContinuousLinearMap.toSpanSingleton_apply_one]
      using (hP'.hasFDerivAt.fun_sub hQ'.hasFDerivAt).hasDerivAt
  have htwo : IsUnit (2 : ℂ) := (two_ne_zero : (2 : ℂ) ≠ 0).isUnit
  have hπ := ((hasDerivAt_id (0 : ℂ)).div_const 2 (hd := htwo)).const_cpow
    (c := (π : ℂ)) (Or.inl hp)
  have hTo : HasDerivAt (fun z : ℂ ↦ z / 2 + 1) (1 / 2) 0 :=
    ((hasDerivAt_id' (0 : ℂ)).div_const 2 (hd := htwo)).add_const 1
  have hΓ₀ : HasDerivAt reciprocalGamma (γ : ℂ) ((0 : ℂ) / 2 + 1) := by
    simpa only [zero_div, zero_add] using hasDerivAt_reciprocalGamma_one
  have hΓ := HasDerivAt.comp (h := fun z : ℂ ↦ z / 2 + 1) (coord' := id) 0 hΓ₀ hTo
  have hBraw : HasDerivAt B ((log π + γ) / 4) 0 := by
    convert (hπ.mul hΓ).div_const 2 (hd := htwo) using 1 <;>
      simp only [B, Function.comp_apply, Pi.mul_apply, id_eq, zero_div, zero_add, cpow_zero,
        reciprocalGamma_one, one_mul, mul_one]
    ring
  have hB : HasDerivAt (fun z : D ↦ B z) ((log π + γ) / 4) z₀ (fun z ↦ (z : ℂ)) :=
    hasDerivAt_restrict_zetaDomain (s := z₀) hBraw
  have heq : (fun z : D ↦ riemannZeta z (hs := z.2)) = fun z : D ↦ A z * B z := by
    funext z
    rw [riemannZeta_eq_mul_completedRiemannZeta₀ z]
    dsimp [A, B]
    ring
  rw [heq, (hA.fun_mul hB continuousAt_subtype_val).deriv
    isOpen_compl_singleton.isOpenEmbedding_subtypeVal]
  simp only [A, B, z₀, zero_mul, zero_sub, zero_div, sub_zero, zero_add, cpow_zero,
    reciprocalGamma_one, one_mul]
  rw [completedRiemannZeta₀_zero]
  suffices h : -(log (2 * π) * 2) = γ - log (2 * 2 * π) + (-log π + -γ) by
    norm_num only at h
    linear_combination -h / 4
  open ComplexOrder in
  repeat rw [log_mul (by positivity) (by positivity) (by simp [arg, LT.lt.le, Real.pi_pos])]
  ring

section near_one

/-!
## More asymptotics near `s = 1`

To facilitate the analysis of `riemannZeta` near `s = 1`, we write `riemannZeta s` additively as
`(s-1)⁻¹ + riemannZeta₀ s` and multiplicatively as `(s-1)⁻¹ * riemannZeta₁ s` for certain
entire functions `riemannZeta₀`, `riemannZeta₁`.
-/

open Asymptotics

/-- The entire constant-term regularization of zeta at one, as the divided difference
of its entire multiplicative normalization. -/
noncomputable def riemannZeta₀ (s : ℂ) : ℂ := dslope riemannZeta₁ 1 s

@[simp]
lemma riemannZeta₀_one : riemannZeta₀ 1 = γ := by
  simp [riemannZeta₀]

lemma riemannZeta_eq_inv_sub_add {s : ℂ} (hs : s ≠ 1) :
    riemannZeta s = (s - 1)⁻¹ + riemannZeta₀ s := by
  rw [riemannZeta_eq_inv_sub_mul hs, riemannZeta₀, dslope_of_ne _ hs,
    slope_fun_def_field, riemannZeta₁_one]
  field

@[fun_prop]
lemma differentiable_riemannZeta₀ : Differentiable ℂ riemannZeta₀ := by
  exact differentiableOn_univ.mp <|
    (Complex.differentiableOn_dslope (s := univ) (c := (1 : ℂ)) (by simp)).mpr
      differentiable_riemannZeta₁.differentiableOn

local notation "D" => {s : ℂ // s ≠ 1}
local notation "U" => {s : ℂ // IsUnit (riemannZeta₁ s)}
local notation "Z" => {s : D // IsUnit (riemannZeta s (Subtype.property s))}
local notation "ζ'" => (fun s : D ↦
  deriv (fun z : D ↦ riemannZeta z (Subtype.property z)) s (fun z ↦ (z : ℂ)))

lemma isUnit_riemannZeta₁ {s : ℂ} (hs : s ≠ 1) {hζ : IsUnit (riemannZeta s)} :
    IsUnit (riemannZeta₁ s) := by
  have h := hζ
  simp only [riemannZeta_eq_inv_sub_mul hs] at h
  exact (IsUnit.mul_iff.mp h).2

private lemma hasDerivAt_inv_sub_one (s : D) :
    HasDerivAt (fun z : D ↦ ((z : ℂ) - 1)⁻¹) (-(((s : ℂ) - 1)⁻¹) ^ 2)
      s (fun z ↦ (z : ℂ)) := by
  let φ : D → {z : ℂ // IsUnit (z - 1)} := fun z ↦ ⟨z, (sub_ne_zero.mpr z.2).isUnit⟩
  have h := ((hasDerivAt_id (s : ℂ)).sub_const 1).inv (sub_ne_zero.mpr s.2).isUnit
  have hd := HasFDerivAtFilter.comp_tendsto h.hasFDerivAt φ
    ((((continuous_subtype_val.subtype_mk _) : Continuous φ).tendsto s).prodMap
      (tendsto_pure_pure φ s))
  apply hasDerivAt_iff_hasFDerivAt.mpr
  change HasFDerivAtFilter _ _ (𝓝 s ×ˢ pure s) Subtype.val
  simpa only [Checked.inv, neg_mul, one_mul, Function.comp_def, φ] using hd

lemma deriv_riemannZeta_eq_neg_inv_sub_sq_add {s : ℂ} (hs : s ≠ 1) :
    ζ' ⟨s, hs⟩ = -((s - 1)⁻¹) ^ 2 + deriv riemannZeta₀ s := by
  have hR : HasDerivAt (fun z : D ↦ riemannZeta₀ z) (deriv riemannZeta₀ s)
      ⟨s, hs⟩ (fun z ↦ (z : ℂ)) :=
    hasDerivAt_restrict_zetaDomain (s := ⟨s, hs⟩) (differentiable_riemannZeta₀ s).hasDerivAt
  have heq : (fun z : D ↦ riemannZeta z (hs := z.2)) =
      fun z : D ↦ Checked.inv ((z : ℂ) - 1) (sub_ne_zero.mpr z.2).isUnit + riemannZeta₀ z :=
    funext (fun z ↦ riemannZeta_eq_inv_sub_add z.2)
  rw [heq]
  have hd := ((hasDerivAt_inv_sub_one ⟨s, hs⟩).hasFDerivAt.fun_add hR.hasFDerivAt).hasDerivAt
  simpa only [add_apply, ContinuousLinearMap.toSpanSingleton_apply_one] using
    hd.deriv (isOpen_compl_singleton (x := (1 : ℂ))).isOpenEmbedding_subtypeVal

lemma deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add {s : ℂ} (hs : s ≠ 1) :
    ζ' ⟨s, hs⟩ = -((s - 1)⁻¹) ^ 2 * riemannZeta₁ s +
      (s - 1)⁻¹ * deriv riemannZeta₁ s := by
  have hR : HasDerivAt (fun z : D ↦ riemannZeta₁ z) (deriv riemannZeta₁ s)
      ⟨s, hs⟩ (fun z ↦ (z : ℂ)) :=
    hasDerivAt_restrict_zetaDomain (s := ⟨s, hs⟩) (differentiable_riemannZeta₁ s).hasDerivAt
  have heq : (fun z : D ↦ riemannZeta z (hs := z.2)) =
      fun z : D ↦ Checked.inv ((z : ℂ) - 1) (sub_ne_zero.mpr z.2).isUnit * riemannZeta₁ z :=
    funext (fun z ↦ riemannZeta_eq_inv_sub_mul z.2)
  rw [heq]
  exact ((hasDerivAt_inv_sub_one ⟨s, hs⟩).fun_mul hR
    continuousAt_subtype_val).deriv
      isOpen_compl_singleton.isOpenEmbedding_subtypeVal

lemma deriv_riemannZeta_add_inv_sub_sq_bounded :
    (fun s : D ↦ ζ' s + (((s : ℂ) - 1)⁻¹) ^ 2)
      =O[comap Subtype.val (𝓝 1)] (fun _ ↦ (1 : ℂ)) := by
  have h := ((differentiable_riemannZeta₀.deriv.continuous.tendsto 1).comp
    (tendsto_comap : Tendsto (Subtype.val : D → ℂ) _ (𝓝 1))).isBigO_one ℂ
  apply h.congr' (.of_forall (fun s ↦ ?_)) .rfl
  rw [Function.comp_apply, deriv_riemannZeta_eq_neg_inv_sub_sq_add s.2]
  ring

lemma riemannZeta₁_ne_zero_of_near_one : ∀ᶠ s in 𝓝 1, riemannZeta₁ s ≠ 0 := by
  exact (differentiable_riemannZeta₁.continuous.tendsto 1).eventually_ne
    (by rw [riemannZeta₁_one]; exact one_ne_zero)

lemma log_riemannZeta_eq_neg_log_sub_add_ofReal {s : ℝ} (hs : s > 1) :
    (riemannZeta s (hs := by exact_mod_cast hs.ne')).re.log =
      -(s - 1).log + (riemannZeta₁ s).re.log := by
  have h₁ : (s : ℂ) ≠ 1 := by exact_mod_cast hs.ne'
  have hn := (sub_pos.mpr hs).ne'
  have hi : (((s - 1)⁻¹ : ℝ) : ℂ) =
      Checked.inv ((s : ℂ) - 1) (sub_ne_zero.mpr h₁).isUnit := by
    simp only [ofReal_inv, ofReal_sub, ofReal_one]
  have h : (riemannZeta s h₁).re = (s - 1)⁻¹ * (riemannZeta₁ s).re := by
    rw [riemannZeta_eq_inv_sub_mul h₁, ← hi, re_ofReal_mul]
  have hp := (riemannZeta_re_pos_of_one_lt hs).ne'
  rw [h] at hp
  rw [h, Real.log_mul inv_ne_zero (right_ne_zero_of_mul hp), Real.log_inv]

lemma log_riemannZeta_add_log_sub_isBigO_ofReal :
    (fun s : Ioi (1 : ℝ) ↦ (riemannZeta (s : ℝ)
      (hs := by exact_mod_cast s.2.ne')).re.log + ((s : ℝ) - 1).log)
      =O[comap Subtype.val (𝓝 1)] (fun s ↦ (s : ℝ) - 1) := by
  have hd : DifferentiableAt ℝ (fun s : ℝ ↦ (riemannZeta₁ s).re.log) 1 := by
    have h : Differentiable ℝ (fun s : ℝ ↦ (riemannZeta₁ s).re) :=
      reCLM.differentiable.comp
        ((differentiable_riemannZeta₁.restrictScalars ℝ).comp ofRealCLM.differentiable)
    exact (h 1).log (by simp)
  have h := hd.isBigO_sub.comp_tendsto
    (tendsto_comap : Tendsto (Subtype.val : Ioi (1 : ℝ) → ℝ) _ (𝓝 1))
  simp only [Function.comp_def, ofReal_one, riemannZeta₁_one, one_re, Real.log_one, sub_zero] at h
  apply h.congr' (.of_forall (fun s ↦ ?_)) .rfl
  rw [log_riemannZeta_eq_neg_log_sub_add_ofReal s.2]
  ring

lemma log_riemannZeta_add_log_sub_isLittleO_ofReal :
    (fun s : Ioi (1 : ℝ) ↦ (riemannZeta (s : ℝ)
      (hs := by exact_mod_cast s.2.ne')).re.log + ((s : ℝ) - 1).log)
      =o[comap Subtype.val (𝓝 1)] (fun _ ↦ (1 : ℝ)) :=
  log_riemannZeta_add_log_sub_isBigO_ofReal.trans_isLittleO
    (continuous_id.continuousAt.isLittleO.comp_tendsto tendsto_comap)

lemma log_deriv_riemannZeta_eq_neg_inv_sub_add_at {s : ℂ} (hs : s ≠ 1)
    {hζ : IsUnit (riemannZeta s hs)} :
    Checked.div (ζ' ⟨s, hs⟩) (riemannZeta s hs) hζ =
      -(s - 1)⁻¹ + Checked.div (deriv riemannZeta₁ s) (riemannZeta₁ s)
        (isUnit_riemannZeta₁ hs (hζ := hζ)) := by
  have hD := deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add hs
  have hV := riemannZeta_eq_inv_sub_mul hs
  simp only [hD, hV]
  field

lemma log_deriv_riemannZeta_eq_neg_inv_sub_add :
    ∀ᶠ s : Z in comap (fun s : Z ↦ (s : ℂ)) (𝓝 1),
      Checked.div (ζ' s.1) (riemannZeta s (hs := s.1.2)) s.2 =
        -Checked.inv ((s : ℂ) - 1) (sub_ne_zero.mpr s.1.2).isUnit +
          Checked.div (deriv riemannZeta₁ s) (riemannZeta₁ s)
          (isUnit_riemannZeta₁ s.1.2 (hζ := s.2)) :=
  Eventually.of_forall (fun s ↦ log_deriv_riemannZeta_eq_neg_inv_sub_add_at s.1.2 (hζ := s.2))

lemma log_deriv_riemannZeta_add_inv_sub_sub_isBigO :
    (fun s : Z ↦ Checked.div (ζ' s.1) (riemannZeta s (hs := s.1.2)) s.2 +
      Checked.inv ((s : ℂ) - 1) (sub_ne_zero.mpr s.1.2).isUnit - γ)
      =O[comap (fun s : Z ↦ (s : ℂ)) (𝓝 1)] (fun s ↦ (s : ℂ) - 1) := by
  let u₁ : U := ⟨1, by simp⟩
  let φ : Z → U := fun s ↦ ⟨s, isUnit_riemannZeta₁ s.1.2 (hζ := s.2)⟩
  have hφ : Tendsto φ (comap (fun s : Z ↦ (s : ℂ)) (𝓝 1)) (𝓝 u₁) := by
    exact tendsto_subtype_rng.mpr tendsto_comap
  have hq := (differentiable_riemannZeta₁.deriv 1).div
    (differentiable_riemannZeta₁ 1) (by simp : IsUnit (riemannZeta₁ 1))
  have h := hq.isBigO_sub.comp_tendsto hφ
  have he : Checked.div (deriv riemannZeta₁ 1) (riemannZeta₁ 1) (by simp) = γ := by simp
  change (fun s : Z ↦ Checked.div (deriv riemannZeta₁ s) (riemannZeta₁ s) (φ s).2 -
    Checked.div (deriv riemannZeta₁ 1) (riemannZeta₁ 1) u₁.2)
      =O[comap (fun s : Z ↦ (s : ℂ)) (𝓝 1)] (fun s ↦ (s : ℂ) - 1) at h
  rw [he] at h
  apply h.congr' ?_ .rfl
  filter_upwards [log_deriv_riemannZeta_eq_neg_inv_sub_add] with s hs
  rw [hs]
  ring

lemma log_deriv_riemannZeta_add_inv_sub_sub_isLittleO :
    (fun s : Z ↦ Checked.div (ζ' s.1) (riemannZeta s (hs := s.1.2)) s.2 +
      Checked.inv ((s : ℂ) - 1) (sub_ne_zero.mpr s.1.2).isUnit - γ)
      =o[comap (fun s : Z ↦ (s : ℂ)) (𝓝 1)] (fun _ ↦ (1 : ℂ)) :=
  log_deriv_riemannZeta_add_inv_sub_sub_isBigO.trans_isLittleO
    (continuous_id.continuousAt.isLittleO.comp_tendsto tendsto_comap)

lemma log_deriv_riemannZeta_add_inv_sub_bounded :
    (fun s : Z ↦ Checked.div (ζ' s.1) (riemannZeta s (hs := s.1.2)) s.2 +
      Checked.inv ((s : ℂ) - 1) (sub_ne_zero.mpr s.1.2).isUnit)
      =O[comap (fun s : Z ↦ (s : ℂ)) (𝓝 1)] (fun _ ↦ (1 : ℂ)) :=
  (isBigO_const_one ..).sub_iff_left.mp log_deriv_riemannZeta_add_inv_sub_sub_isLittleO.isBigO

lemma inv_riemannZeta_eq_sub_mul_of_ne_one {s : ℂ} (hs : s ≠ 1)
    {hζ : IsUnit (riemannZeta s)} :
    Checked.inv (riemannZeta s hs) hζ =
      (s - 1) * Checked.inv (riemannZeta₁ s) (isUnit_riemannZeta₁ hs (hζ := hζ)) := by
  simp only [riemannZeta_eq_inv_sub_mul hs, mul_inv₀, inv_inv₀]

lemma inv_riemannZeta_eq_sub_mul :
    ∀ᶠ s : Z in comap (fun s : Z ↦ (s : ℂ)) (𝓝 1),
      Checked.inv (riemannZeta s (hs := s.1.2)) s.2 =
        ((s : ℂ) - 1) * Checked.inv (riemannZeta₁ s)
          (isUnit_riemannZeta₁ s.1.2 (hζ := s.2)) :=
  .of_forall (fun s ↦ inv_riemannZeta_eq_sub_mul_of_ne_one s.1.2 (hζ := s.2))

lemma inv_riemannZeta_sub_sub_isBigO :
    (fun s : Z ↦ Checked.inv (riemannZeta s (hs := s.1.2)) s.2 - ((s : ℂ) - 1))
      =O[comap (fun s : Z ↦ (s : ℂ)) (𝓝 1)] (fun s ↦ ((s : ℂ) - 1) ^ 2) := by
  let u₁ : U := ⟨1, by simp⟩
  let φ : Z → U := fun s ↦ ⟨s, isUnit_riemannZeta₁ s.1.2 (hζ := s.2)⟩
  have hφ : Tendsto φ (comap (fun s : Z ↦ (s : ℂ)) (𝓝 1)) (𝓝 u₁) := by
    exact tendsto_subtype_rng.mpr tendsto_comap
  have hinv := (differentiable_riemannZeta₁ 1).inv (by simp : IsUnit (riemannZeta₁ 1))
  have h := hinv.isBigO_sub.comp_tendsto hφ
  have he : Checked.inv (riemannZeta₁ 1) (by simp) = 1 := by simp
  change (fun s : Z ↦ Checked.inv (riemannZeta₁ s) (φ s).2 -
    Checked.inv (riemannZeta₁ 1) u₁.2)
      =O[comap (fun s : Z ↦ (s : ℂ)) (𝓝 1)] (fun s ↦ (s : ℂ) - 1) at h
  rw [he] at h
  have hmul := (isBigO_refl (fun s : Z ↦ (s : ℂ) - 1) _).mul h
  refine hmul.congr' ?_ (.of_forall (fun s ↦ (pow_two ((s : ℂ) - 1)).symm))
  filter_upwards [inv_riemannZeta_eq_sub_mul] with s hs
  rw [hs]
  ring

lemma inv_riemannZeta_sub_sub_isLittleO :
    (fun s : Z ↦ Checked.inv (riemannZeta s (hs := s.1.2)) s.2 - ((s : ℂ) - 1))
      =o[comap (fun s : Z ↦ (s : ℂ)) (𝓝 1)] (fun s ↦ (s : ℂ) - 1) := by
  apply inv_riemannZeta_sub_sub_isBigO.trans_isLittleO
  have h : (fun s : Z ↦ (s : ℂ) - 1)
      =o[comap (fun s : Z ↦ (s : ℂ)) (𝓝 1)] (fun _ ↦ (1 : ℂ)) :=
    continuous_id.continuousAt.isLittleO.comp_tendsto tendsto_comap
  simpa [pow_two] using h.mul_isBigO (isBigO_refl (fun s : Z ↦ (s : ℂ) - 1) _)

lemma inv_riemannZeta_isBigO :
    (fun s : Z ↦ Checked.inv (riemannZeta s (hs := s.1.2)) s.2)
      =O[comap (fun s : Z ↦ (s : ℂ)) (𝓝 1)] (fun s ↦ (s : ℂ) - 1) :=
  (isBigO_refl ..).sub_iff_left.mp inv_riemannZeta_sub_sub_isLittleO.isBigO

end near_one
