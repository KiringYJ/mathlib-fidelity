/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# L-series of functions on `ZMod N`

We show that if `N` is a positive integer and `Φ : ZMod N → ℂ`, then the L-series of `Φ` has
analytic continuation (away from a pole at `s = 1` if `∑ j, Φ j ≠ 0`) and satisfies a functional
equation. We also define completed L-functions (given by multiplying the naive L-function by a
Gamma-factor), and prove analytic continuation and functional equations for these too, assuming `Φ`
is either even or odd.

The most familiar case is when `Φ` is a Dirichlet character, but the results here are valid
for general functions; for the specific case of Dirichlet characters see
`Mathlib/NumberTheory/LSeries/DirichletContinuation.lean`.

## Main definitions

* `ZMod.LFunction Φ s`: the meromorphic continuation of the Dirichlet series
  `∑ n : ℕ+, Φ n * n ^ (-s)`, evaluated on its regular domain.
* `ZMod.completedLFunction Φ s`: the completed L-function on its regular domain.

Note that `ZMod.completedLFunction Φ s` is only mathematically well-defined if `Φ` is either even
or odd. Here we extend it to all functions `Φ` by linearity (but the functional equation only holds
if `Φ` is either even or odd).

## Main theorems

Results for non-completed L-functions:

* `ZMod.LFunction_eq_LSeries`: if `1 < re s` then the `LFunction` coincides with the naive
  `LSeries`.
* `ZMod.differentiableAt_LFunction`: `ZMod.LFunction Φ` is differentiable at `s ∈ ℂ` if either
  `s ≠ 1` or `∑ j, Φ j = 0`.
* `ZMod.LFunction_one_sub`: the functional equation relating `LFunction Φ (1 - s)` to
  `LFunction (𝓕 Φ) s`, where `𝓕` is the Fourier transform.

Results for completed L-functions:

* `ZMod.LFunction_eq_completed_mul_reciprocalGammaℝ_even` and
  `ZMod.LFunction_eq_completed_mul_reciprocalGammaℝ_odd`: on the regular domain of the
  completion, the L-function is its product with the corresponding entire reciprocal Gamma
  factor.
* `ZMod.differentiableAt_completedLFunction`: `ZMod.completedLFunction Φ` is differentiable at
  `s ∈ ℂ`, unless `s = 1` and `∑ j, Φ j ≠ 0`, or `s = 0` and `Φ 0 ≠ 0`.
* `ZMod.completedLFunction_one_sub_even` and `ZMod.completedLFunction_one_sub_odd`:
  the functional equation relating `completedLFunction Φ (1 - s)` to `completedLFunction (𝓕 Φ) s`.
-/

@[expose] public section

open HurwitzZeta Complex ZMod Finset Filter Set

open scoped Topology

open scoped Real

namespace ZMod

variable {N : ℕ} [NeZero N]

/-- If `Φ` is a periodic function, then the L-series of `Φ` converges for `1 < re s`. -/
lemma LSeriesSummable_of_one_lt_re (Φ : ZMod N → ℂ) {s : ℂ} (hs : 1 < re s) :
    LSeriesSummable (Φ ·) s := by
  let c := max' _ <| univ_nonempty.image (norm ∘ Φ)
  refine LSeriesSummable_of_bounded_of_one_lt_re (fun n _ ↦ le_max' _ _ ?_) (m := c) hs
  exact mem_image_of_mem _ (mem_univ _)

/-- The entire regular part of the congruence L-function after its common
Gamma-weighted principal part has been removed. -/
noncomputable def LFunctionRegularPart (Φ : ZMod N → ℂ) (s : ℂ) : ℂ :=
  N ^ (-s) * ∑ j : ZMod N, Φ j * hurwitzZetaRegularPart (toAddCircle j) s

/-- The regular domain of the congruence L-function. -/
abbrev LFunctionDomain (Φ : ZMod N → ℂ) : Set ℂ :=
  {s | s ≠ 1 ∨ ∑ j, Φ j = 0}

/-- The congruence L-function, evaluated away from a genuine pole.
When the coefficient sum vanishes, the principal part cancels before any quotient is formed,
so evaluation at one is the value of its entire continuation. -/
noncomputable def LFunction (Φ : ZMod N → ℂ) (s : ℂ)
    (hs : s ≠ 1 ∨ ∑ j, Φ j = 0 := by
      first | assumption | exact Or.inl (by checked_nonzero) | exact Or.inr (by assumption)) : ℂ :=
  LFunctionRegularPart Φ s + if hΦ : ∑ j, Φ j = 0 then 0 else
    N ^ (-s) * Checked.div ((∑ j, Φ j) * reciprocalGammaℝ s) (s - 1)
      (sub_ne_zero.mpr (hs.resolve_right hΦ)).isUnit

/-- The congruence L-function as a function on its regular domain. -/
noncomputable abbrev LFunctionOn (Φ : ZMod N → ℂ) (s : LFunctionDomain Φ) : ℂ :=
  LFunction Φ s s.2

lemma LFunction_eq_hurwitzZeta_sum (Φ : ZMod N → ℂ) {s : ℂ} (hs : s ≠ 1) :
    LFunction Φ s (Or.inl hs) =
      N ^ (-s) * ∑ j : ZMod N, Φ j * hurwitzZeta (toAddCircle j) s hs := by
  simp only [hurwitzZeta_eq_regularPart_add hs, mul_add, sum_add_distrib]
  rw [← sum_mul]
  unfold LFunction LFunctionRegularPart
  split_ifs with hΦ
  · simp [hΦ]
  · rw [mul_div_assoc₀]

lemma LFunction_eq_regularPart_of_sum_zero {Φ : ZMod N → ℂ} (hΦ : ∑ j, Φ j = 0)
    (s : ℂ) : LFunction Φ s (Or.inr hΦ) = LFunctionRegularPart Φ s := by
  simp [LFunction, hΦ]

/-- The L-function of a function on `ZMod 1` is a scalar multiple of the Riemann zeta function. -/
lemma LFunction_modOne_eq (Φ : ZMod 1 → ℂ) (s : ℂ) (hs : s ≠ 1) :
    LFunction Φ s (Or.inl hs) = Φ 0 * riemannZeta s hs := by
  simp only [LFunction_eq_hurwitzZeta_sum _ hs, Nat.cast_one, one_cpow,
    ← singleton_eq_univ (0 : ZMod 1), sum_singleton,
    map_zero, hurwitzZeta_zero, one_mul]

private lemma ne_one_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : s ≠ 1 := by
  rintro rfl
  simp at hs

/-- For `1 < re s` the congruence L-function agrees with the sum of the Dirichlet series. -/
lemma LFunction_eq_LSeries (Φ : ZMod N → ℂ) {s : ℂ} (hs : 1 < re s) :
    LFunction Φ s (by exact Or.inl (ne_one_of_one_lt_re hs)) = LSeries (Φ ·) s := by
  rw [LFunction_eq_hurwitzZeta_sum _ (ne_one_of_one_lt_re hs), LSeries, mul_sum,
    Nat.sumByResidueClasses (LSeriesSummable_of_one_lt_re Φ hs) N]
  congr 1 with j
  have : ((j.val : ℝ) / (N : ℝ)) ∈ Set.Icc 0 1 := mem_Icc.mpr ⟨by positivity,
    (div_le_one (Nat.cast_pos.mpr <| NeZero.pos _)).mpr <| Nat.cast_le.mpr (val_lt j).le⟩
  rw [toAddCircle_apply, ← (hasSum_hurwitzZeta_of_one_lt_re this hs).tsum_eq, ← mul_assoc,
    ← tsum_mul_left]
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have harg (m : ℕ) : ↑(j.val + N * m : ℕ) =
      (N : ℂ) * ((m : ℂ) + ((j.val : ℝ) / (N : ℝ))) := by
    push_cast [ofReal_div]
    rw [mul_add, ← mul_div_assoc₀, mul_comm (N : ℂ) (j.val : ℂ),
      mul_div_cancel_right₀, add_comm]
  have hsupp : Function.support (fun m ↦ LSeries.term (Φ ·) s (j.val + N * m)) ⊆
      {m : ℕ | (m : ℝ) + (j.val : ℝ) / (N : ℝ) ≠ 0} := by
    intro m hm
    change (m : ℝ) + (j.val : ℝ) / (N : ℝ) ≠ 0
    intro hz
    have hz' := congrArg ofReal hz
    rw [ofReal_add, ofReal_natCast, ofReal_zero] at hz'
    have he : (↑(j.val + N * m : ℕ) : ℂ) = 0 := by rw [harg, hz', mul_zero]
    exact hm (by simp [Nat.cast_eq_zero.mp he])
  rw [← tsum_subtype_eq_of_support_subset hsupp]
  refine tsum_congr fun m ↦ ?_
  have hm : ((m : ℕ) : ℂ) + ((j.val : ℝ) / (N : ℝ)) ≠ 0 := by
    simpa only [ofReal_add, ofReal_natCast] using ofReal_ne_zero.mpr m.2
  have hm' : j.val + N * (m : ℕ) ≠ 0 :=
    Nat.cast_ne_zero.mp (harg m ▸ mul_ne_zero hN hm)
  have hp : (↑(j.val + N * (m : ℕ) : ℕ) : ℂ) ^ s =
      (N : ℂ) ^ s * (((m : ℕ) : ℂ) + ((j.val : ℝ) / (N : ℝ))) ^ s := by
    rw [harg]
    simpa only [ofReal_mul, ofReal_add, ofReal_natCast] using
      (mul_cpow_ofReal_nonneg (a := (N : ℝ)) (b := (m : ℕ) + (j.val : ℝ) / (N : ℝ))
        (by positivity) (by positivity) s)
  rw [LSeries.term_of_ne_zero hm', eq_div_iff, hp]
  have hNpow : IsUnit ((N : ℂ) ^ s) := (cpow_ne_zero_iff.mpr (Or.inl hN)).isUnit
  let b := (((m : ℕ) : ℂ) + ((j.val : ℝ) / (N : ℝ))) ^ s
  have hb : IsUnit b := (cpow_ne_zero_iff.mpr (Or.inl hm)).isUnit
  simp only [Nat.cast_add, Nat.cast_mul, natCast_zmod_val, natCast_self, zero_mul, add_zero]
  calc
    _ = Φ j * (((N : ℂ) ^ (-s) * N ^ s) * (Checked.div 1 b hb * b)) := by dsimp [b]; ring
    _ = Φ j := by
      rw [cpow_neg _ _ (hxy := hNpow), inv_mul_cancel₀, div_mul_cancel₀, mul_one, mul_one]

lemma differentiable_LFunctionRegularPart (Φ : ZMod N → ℂ) :
    Differentiable ℂ (LFunctionRegularPart Φ) :=
  (differentiable_id.neg.const_cpow (Or.inl (Nat.cast_ne_zero.mpr (NeZero.ne N)))).mul
    (.fun_sum fun j _ ↦ (differentiable_hurwitzZetaRegularPart (toAddCircle j)).const_mul (Φ j))

lemma differentiableAt_LFunction (Φ : ZMod N → ℂ) (s : ℂ) (hs : s ∈ LFunctionDomain Φ) :
    DifferentiableAt ℂ (LFunctionOn Φ) ⟨s, hs⟩ Subtype.val := by
  have hrestrict (f : ℂ → ℂ) (hf : DifferentiableAt ℂ f s) :
      DifferentiableAt ℂ (fun z : LFunctionDomain Φ ↦ f z) ⟨s, hs⟩ Subtype.val := by
    obtain ⟨d, hd⟩ := hf
    exact ⟨d, HasFDerivAtFilter.comp_tendsto hd Subtype.val
      ((continuous_subtype_val.tendsto ⟨s, hs⟩).prodMap (tendsto_pure_pure ..))⟩
  by_cases hΦ : ∑ j, Φ j = 0
  · change DifferentiableAt ℂ (fun z : LFunctionDomain Φ ↦ LFunction Φ z z.2)
      ⟨s, hs⟩ Subtype.val
    simpa only [LFunction_eq_regularPart_of_sum_zero hΦ] using
      hrestrict _ (differentiable_LFunctionRegularPart Φ s)
  · let f : LFunctionDomain Φ → {z : ℂ // IsUnit (z - 1)} :=
      fun z ↦ ⟨z, (sub_ne_zero.mpr (z.2.resolve_right hΦ)).isUnit⟩
    have hf : Continuous f := continuous_subtype_val.subtype_mk _
    obtain ⟨d, hd⟩ := ((differentiable_reciprocalGammaℝ s).const_mul (∑ j, Φ j)).div
      (differentiableAt_id.sub_const 1) (sub_ne_zero.mpr (hs.resolve_right hΦ)).isUnit
    have hdiv : DifferentiableAt ℂ
        (fun z : LFunctionDomain Φ ↦ Checked.div ((∑ j, Φ j) * reciprocalGammaℝ z)
          (z - 1) (f z).2) ⟨s, hs⟩ Subtype.val :=
      ⟨d, HasFDerivAtFilter.comp_tendsto hd f
        ((hf.tendsto ⟨s, hs⟩).prodMap (tendsto_pure_pure ..))⟩
    have hpow : DifferentiableAt ℂ (fun z : LFunctionDomain Φ ↦ (N : ℂ) ^ (-(z : ℂ)))
        ⟨s, hs⟩ Subtype.val :=
      hrestrict _ (differentiableAt_id.neg.const_cpow (Or.inl (Nat.cast_ne_zero.mpr (NeZero.ne N))))
    change DifferentiableAt ℂ (fun z : LFunctionDomain Φ ↦ LFunction Φ z z.2)
      ⟨s, hs⟩ Subtype.val
    simpa only [LFunction, dite_eq_right hΦ] using
      (hrestrict _ (differentiable_LFunctionRegularPart Φ s)).fun_add
        (hpow.fun_mul hdiv continuousAt_subtype_val)

lemma differentiable_LFunction_of_sum_zero {Φ : ZMod N → ℂ} (hΦ : ∑ j, Φ j = 0) :
    Differentiable ℂ (fun s ↦ LFunction Φ s (Or.inr hΦ)) := by
  simpa only [LFunction_eq_regularPart_of_sum_zero hΦ] using differentiable_LFunctionRegularPart Φ

/-- The L-function of `Φ` has a residue at `s = 1` equal to the average value of `Φ`. -/
lemma LFunction_residue_one (Φ : ZMod N → ℂ) :
    Tendsto (fun s : {z : ℂ // z ≠ 1} ↦ (s - 1) * LFunction Φ s (Or.inl s.2))
      (Filter.comap Subtype.val (𝓝 1)) (𝓝 (∑ j, Φ j / (N : ℂ))) := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have ht : Tendsto (fun s : {z : ℂ // z ≠ 1} ↦ (N : ℂ) ^ (-(s : ℂ)))
      (Filter.comap Subtype.val (𝓝 1)) (𝓝 ((N : ℂ) ^ (-(1 : ℂ)))) :=
    ((continuous_neg.const_cpow (Or.inl hN)).tendsto (1 : ℂ)).comp tendsto_comap
  have hp (j : ZMod N) : Tendsto
      (fun s : {z : ℂ // z ≠ 1} ↦ (N : ℂ) ^ (-(s : ℂ)) *
        (Φ j * ((s - 1) * hurwitzZeta (toAddCircle j) s s.2)))
      (Filter.comap Subtype.val (𝓝 1)) (𝓝 (Φ j / (N : ℂ))) := by
    rw [div_eq_mul_inv₀, mul_comm, ← cpow_neg_one]
    simpa only [mul_one] using
      ht.mul (tendsto_const_nhds.mul (hurwitzZeta_residue_one (toAddCircle j)))
  convert tendsto_finsetSum univ (fun j _ ↦ hp j) using 2 with s
  rw [LFunction_eq_hurwitzZeta_sum Φ s.2, mul_sum, mul_sum]
  exact sum_congr rfl fun j _ ↦ by ring

local notation "𝕖" => stdAddChar

/--
The `LFunction` of the function `x ↦ e (j * x)`, where `e : ZMod N → ℂ` is the standard additive
character, agrees with `expZeta (j / N)` on `1 < re s`. Private since it is a stepping-stone to
the more general result `LFunction_stdAddChar_eq_expZeta` below.
-/
private lemma LFunction_stdAddChar_eq_expZeta_of_one_lt_re (j : ZMod N) {s : ℂ} (hs : 1 < s.re) :
    LFunction (fun k ↦ 𝕖 (j * k)) s (Or.inl (ne_one_of_one_lt_re hs)) =
      expZeta (ZMod.toAddCircle j) s (Or.inl (ne_one_of_one_lt_re hs)) := by
  rw [toAddCircle_apply, LFunction_eq_LSeries _ hs]
  refine (LSeriesHasSum_iff_hasSum_pnat.mpr
    ((hasSum_expZeta_of_one_lt_re ((j.val : ℝ) / (N : ℝ)) hs).congr_fun fun n ↦ ?_)).tsum_eq
  congr 1
  have hc := stdAddChar_coe (N := N) ((j.val : ℤ) * (n : ℕ))
  rw [Int.cast_mul, Int.cast_natCast, Int.cast_natCast, natCast_zmod_val] at hc
  rw [hc]
  congr 1
  simp only [Int.cast_mul, Int.cast_natCast, ofReal_div, ofReal_natCast]
  field_simp

private lemma sum_stdAddChar_mul (j : ZMod N) :
    ∑ k : ZMod N, 𝕖 (j * k) = if j = 0 then (N : ℂ) else 0 := by
  simp only [mul_comm j, AddChar.sum_mulShift _ (isPrimitive_stdAddChar _), ZMod.card,
    Nat.cast_ite, Nat.cast_zero]

private lemma sum_dft_eq (Φ : ZMod N → ℂ) : ∑ j, (𝓕 Φ) j = N * Φ 0 := by
  rw [← dft_apply_zero, dft_dft]
  simp only [neg_zero, smul_eq_mul]

/--
The `LFunction` of the function `x ↦ e (j * x)`, where `e : ZMod N → ℂ` is the standard additive
character, is `expZeta (j / N)`.

Note this is not at all obvious from the definitions, and we prove it by analytic continuation
from the convergence range.
-/
lemma LFunction_stdAddChar_eq_expZeta (j : ZMod N) (s : ℂ) (hjs : j ≠ 0 ∨ s ≠ 1) :
    LFunction (fun k ↦ 𝕖 (j * k)) s (hjs.symm.imp_right (by
      intro hj
      rw [sum_stdAddChar_mul, ite_eq_right hj])) =
      expZeta (toAddCircle j) s (hjs.symm.imp_right toAddCircle_eq_zero.not.mpr) := by
  have h : {z : ℂ | 1 < z.re} ∈ 𝓝 (2 : ℂ) :=
    (continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by simp)
  by_cases hj : j = 0
  · have hs := hjs.resolve_left (fun hne ↦ hne hj)
    let f (z : ℂ) := (z - 1) * LFunctionRegularPart (fun k ↦ 𝕖 (j * k)) z +
      (N : ℂ) ^ (-z) * ((N : ℂ) * reciprocalGammaℝ z)
    let g (z : ℂ) := (z - 1) *
      (cosZetaRegularPart (toAddCircle j) z + I * sinZeta (toAddCircle j) z) +
      reciprocalGammaℝ z
    have hf : Differentiable ℂ f := ((differentiable_id.sub_const 1).mul
      (differentiable_LFunctionRegularPart _)).add
      ((differentiable_id.neg.const_cpow (Or.inl (Nat.cast_ne_zero.mpr (NeZero.ne N)))).mul
        (differentiable_reciprocalGammaℝ.const_mul _))
    have hg : Differentiable ℂ g := ((differentiable_id.sub_const 1).mul
      ((differentiable_cosZetaRegularPart _).add
        ((differentiableAt_sinZeta _).const_mul I))).add differentiable_reciprocalGammaℝ
    have hf' (z : ℂ) (hz : z ≠ 1) :
        f z = (z - 1) * LFunction (fun k ↦ 𝕖 (j * k)) z (Or.inl hz) := by
      have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
      simp only [f, LFunction, sum_stdAddChar_mul, ite_eq_left hj, dite_eq_right hN]
      have hq : Checked.div ((N : ℂ) * reciprocalGammaℝ z) (z - 1)
          (sub_ne_zero.mpr hz).isUnit * (z - 1) = (N : ℂ) * reciprocalGammaℝ z := div_mul_cancel₀ ..
      linear_combination -(N : ℂ) ^ (-z) * hq
    have hg' (z : ℂ) (hz : z ≠ 1) :
        g z = (z - 1) * expZeta (toAddCircle j) z (Or.inl hz) := by
      simp only [g, expZeta, cosZeta, dite_eq_left (toAddCircle_eq_zero.mpr hj)]
      have hq : Checked.div (reciprocalGammaℝ z) (z - 1)
          (sub_ne_zero.mpr hz).isUnit * (z - 1) = reciprocalGammaℝ z := div_mul_cancel₀ ..
      linear_combination -hq
    have he : f =ᶠ[𝓝 (2 : ℂ)] g := by
      filter_upwards [h] with z hz
      rw [hf' z (ne_one_of_one_lt_re hz), hg' z (ne_one_of_one_lt_re hz),
        LFunction_stdAddChar_eq_expZeta_of_one_lt_re j hz]
    have hev := congrFun
      ((hf.differentiableOn.analyticOnNhd isOpen_univ).eq_of_eventuallyEq
        (hg.differentiableOn.analyticOnNhd isOpen_univ) he) s
    rw [hf' s hs, hg' s hs] at hev
    exact mul_left_cancel₀ (sub_ne_zero.mpr hs) hev
  · have hz : ∑ k : ZMod N, 𝕖 (j * k) = 0 := by rw [sum_stdAddChar_mul, ite_eq_right hj]
    let f (z : ℂ) := LFunction (fun k ↦ 𝕖 (j * k)) z (Or.inr hz)
    let g (z : ℂ) := expZeta (toAddCircle j) z (Or.inr (toAddCircle_eq_zero.not.mpr hj))
    have hf : Differentiable ℂ f := differentiable_LFunction_of_sum_zero hz
    have hg : Differentiable ℂ g :=
      differentiable_expZeta_of_ne_zero (toAddCircle_eq_zero.not.mpr hj)
    have he : f =ᶠ[𝓝 (2 : ℂ)] g := by
      filter_upwards [h] with z hz
      exact LFunction_stdAddChar_eq_expZeta_of_one_lt_re j hz
    exact congrFun ((hf.differentiableOn.analyticOnNhd isOpen_univ).eq_of_eventuallyEq
      (hg.differentiableOn.analyticOnNhd isOpen_univ) he) s

private lemma mul_sum_dft (Φ f : ZMod N → ℂ) (c : ℂ) :
    c * (∑ k, (𝓕 Φ) k * f k) = ∑ j, Φ j * (c * ∑ k, 𝕖 (-j * k) * f k) := by
  simp only [dft_def, smul_eq_mul, mul_sum, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun j _ ↦ sum_congr rfl fun k _ ↦ ?_
  rw [← neg_mul]
  ring

/-- The Fourier transform interchanges the value at zero with the coefficient sum, up to
the order of the group. -/
lemma LFunctionDomain_dft (Φ : ZMod N → ℂ) {s : ℂ} (hs : Φ 0 = 0 ∨ s ≠ 1) :
    s ∈ LFunctionDomain (𝓕 Φ) :=
  hs.symm.imp_right fun h ↦ by rw [sum_dft_eq, h, mul_zero]

/-- The L-function of `𝓕 Φ` as a sum of exponential zeta values. At `s = 1` the trivial
frequency is omitted, since its coefficient vanishes by hypothesis. -/
lemma LFunction_dft (Φ : ZMod N → ℂ) {s : ℂ} (hs : Φ 0 = 0 ∨ s ≠ 1) :
    LFunction (𝓕 Φ) s (LFunctionDomain_dft Φ hs) =
      ∑ j : ZMod N, if h : j ≠ 0 ∨ s ≠ 1 then
        Φ j * expZeta (toAddCircle (-j)) s
          (h.symm.imp_right fun hj ↦ toAddCircle_eq_zero.not.mpr (neg_ne_zero.mpr hj)) else 0 := by
  by_cases h₁ : s = 1
  · have hΦ := hs.resolve_right (fun h ↦ h h₁)
    have hsum : ∑ j, (𝓕 Φ) j = 0 := by rw [sum_dft_eq, hΦ, mul_zero]
    rw [LFunction_eq_regularPart_of_sum_zero hsum, LFunctionRegularPart, mul_sum_dft]
    refine sum_congr rfl fun j _ ↦ ?_
    rcases eq_or_ne j 0 with rfl | hj
    · simp [hΦ, h₁]
    · have hchar : ∑ k : ZMod N, 𝕖 (-j * k) = 0 := by
        rw [sum_stdAddChar_mul, ite_eq_right (neg_ne_zero.mpr hj)]
      rw [dite_eq_left (Or.inl hj),
        ← LFunction_stdAddChar_eq_expZeta _ _ (Or.inl (neg_ne_zero.mpr hj)),
        LFunction_eq_regularPart_of_sum_zero hchar, LFunctionRegularPart]
  · rw [LFunction_eq_hurwitzZeta_sum _ h₁, mul_sum_dft]
    refine sum_congr rfl fun j _ ↦ ?_
    rw [dite_eq_left (Or.inr h₁), ← LFunction_stdAddChar_eq_expZeta _ _ (Or.inr h₁),
      LFunction_eq_hurwitzZeta_sum _ h₁]

private lemma LFunction_dft_of_ne_one (Φ : ZMod N → ℂ) {s : ℂ} (hs : s ≠ 1) :
    LFunction (𝓕 Φ) s (Or.inl hs) =
      ∑ j : ZMod N, Φ j * expZeta (toAddCircle (-j)) s (Or.inl hs) := by
  simpa only [dite_eq_left (Or.inr hs)] using LFunction_dft Φ (Or.inr hs)

private lemma one_sub_ne_one {s : ℂ} (hs : s ≠ 0) : 1 - s ≠ 1 := by
  intro h
  exact hs (by linear_combination -h)

/-- Functional equation for `ZMod` L-functions, in terms of discrete Fourier transform. -/
theorem LFunction_one_sub (Φ : ZMod N → ℂ) {s : ℂ}
    (hs : ∀ (n : ℕ), s ≠ -n) (hs' : Φ 0 = 0 ∨ s ≠ 1) :
    LFunction Φ (1 - s) (by exact Or.inl (one_sub_ne_one (by simpa using hs 0))) =
      N ^ (s - 1) * (2 * π) ^ (-s) * Gamma s *
        (cexp (π * I * s / 2) * LFunction (𝓕 Φ) s (LFunctionDomain_dft Φ hs') +
        cexp (-π * I * s / 2) * LFunction (𝓕 fun x ↦ Φ (-x)) s
          (LFunctionDomain_dft _ (hs'.imp_left (by simp)))) := by
  have hs₀ : 1 - s ≠ 1 := one_sub_ne_one (by simpa using hs 0)
  rw [LFunction_eq_hurwitzZeta_sum Φ hs₀, LFunction_dft Φ hs',
    LFunction_dft _ (hs'.imp_left (by simp))]
  let A (j : ZMod N) := if h : j ≠ 0 ∨ s ≠ 1 then
    Φ j * expZeta (toAddCircle j) s (h.symm.imp_right toAddCircle_eq_zero.not.mpr) else 0
  let B (j : ZMod N) := if h : j ≠ 0 ∨ s ≠ 1 then
    Φ j * expZeta (toAddCircle (-j)) s
      (h.symm.imp_right fun hj ↦ toAddCircle_eq_zero.not.mpr (neg_ne_zero.mpr hj)) else 0
  have hA : (∑ j : ZMod N, if h : j ≠ 0 ∨ s ≠ 1 then
        Φ (-j) * expZeta (toAddCircle (-j)) s
          (h.symm.imp_right fun hj ↦ toAddCircle_eq_zero.not.mpr (neg_ne_zero.mpr hj)) else 0) =
      ∑ j, A j := by
    refine Fintype.sum_equiv (.neg _) _ _ fun j ↦ ?_
    simp only [A, Equiv.neg_apply, neg_ne_zero]
  rw [hA]
  change _ = _ * (_ * (∑ j, B j) + _ * (∑ j, A j))
  rw [neg_sub, mul_sum, mul_sum _ B, mul_sum _ A, ← sum_add_distrib, mul_sum]
  refine sum_congr rfl fun j _ ↦ ?_
  by_cases hj : j ≠ 0 ∨ s ≠ 1
  · rw [hurwitzZeta_one_sub _ hs (hj.imp_left toAddCircle_eq_zero.not.mpr)]
    simp only [A, B, dite_eq_left hj, map_neg]
    ring
  · push Not at hj
    simp [A, B, hj.1, hj.2, hs'.resolve_right (fun h ↦ h hj.2)]

section signed

variable {Φ : ZMod N → ℂ}

lemma LFunction_def_even (hΦ : Φ.Even) (s : ℂ) (hs : s ≠ 1) :
    LFunction Φ s (Or.inl hs) =
      N ^ (-s) * ∑ j : ZMod N, Φ j * hurwitzZetaEven (toAddCircle j) s hs := by
  have hodd : ∑ j, Φ j * hurwitzZetaOdd (toAddCircle j) s = 0 :=
    (hΦ.mul_odd fun j ↦ by rw [map_neg, hurwitzZetaOdd_neg]).sum_eq_zero
  rw [LFunction_eq_hurwitzZeta_sum _ hs]
  simp only [hurwitzZeta, mul_add, sum_add_distrib, hodd, add_zero]

lemma LFunction_def_odd (hΦ : Φ.Odd) (s : ℂ) :
    LFunction Φ s (Or.inr hΦ.sum_eq_zero) =
      N ^ (-s) * ∑ j : ZMod N, Φ j * hurwitzZetaOdd (toAddCircle j) s := by
  have heven : ∑ j, Φ j * hurwitzZetaEvenRegularPart (toAddCircle j) s = 0 := by
    refine (hΦ.mul_even fun j ↦ ?_).sum_eq_zero
    rw [map_neg]
    simp [hurwitzZetaEvenRegularPart]
  rw [LFunction_eq_regularPart_of_sum_zero hΦ.sum_eq_zero, LFunctionRegularPart]
  simp only [hurwitzZetaRegularPart, mul_add, sum_add_distrib, heven, zero_add]

/-- Explicit formula for `LFunction Φ 0` when `Φ` is even. -/
@[simp] lemma LFunction_apply_zero_of_even (hΦ : Φ.Even) :
    LFunction Φ 0 (Or.inl zero_ne_one) = -Φ 0 / 2 := by
  simp only [LFunction_def_even hΦ 0 zero_ne_one, neg_zero, cpow_zero, hurwitzZetaEven_apply_zero,
    toAddCircle_eq_zero, mul_ite, mul_zero, sum_ite_eq', Finset.mem_univ, ↓reduceIte, one_mul]
  rw [← mul_div_assoc₀, mul_neg_one]

/-- The L-function of an even function vanishes at negative even integers. -/
@[simp] lemma LFunction_neg_two_mul_nat_add_one (hΦ : Φ.Even) (n : ℕ) :
    LFunction Φ (-(2 * (n + 1))) (Or.inl (by
      exact_mod_cast (show -(2 * (n + 1) : ℤ) ≠ 1 by omega))) = 0 := by
  rw [LFunction_def_even hΦ _ (by exact_mod_cast (show -(2 * (n + 1) : ℤ) ≠ 1 by omega))]
  simp only [← neg_mul, hurwitzZetaEven_neg_two_mul_nat_add_one, mul_zero,
    sum_const_zero]

/-- The L-function of an odd function vanishes at negative odd integers. -/
@[simp] lemma LFunction_neg_two_mul_nat_sub_one (hΦ : Φ.Odd) (n : ℕ) :
    LFunction Φ (-(2 * n) - 1) (Or.inr hΦ.sum_eq_zero) = 0 := by
  simp only [LFunction_def_odd hΦ, ← neg_mul, hurwitzZetaOdd_neg_two_mul_nat_sub_one, mul_zero,
    sum_const_zero]

/--
The entire part of the completed L-function of a function `ZMod N → ℂ`.
-/
noncomputable def completedLFunction₀ (Φ : ZMod N → ℂ) (s : ℂ) : ℂ :=
  N ^ (-s) * ∑ j : ZMod N, Φ j * completedHurwitzZetaEven₀ (toAddCircle j) s
  + N ^ (-s) * ∑ j : ZMod N, Φ j * completedHurwitzZetaOdd (toAddCircle j) s

/-- The function `completedLFunction₀ Φ` is differentiable. -/
lemma differentiable_completedLFunction₀ (Φ : ZMod N → ℂ) :
    Differentiable ℂ (completedLFunction₀ Φ) := by
  refine .add ?_ ?_ <;>
  refine .mul (by fun_prop) (.fun_sum fun i _ ↦ .const_mul ?_ _)
  exacts [differentiable_completedHurwitzZetaEven₀ _, differentiable_completedHurwitzZetaOdd _]

/-- The principal-part term `c / z`, continued by zero when the coefficient vanishes. -/
noncomputable def completedPoleTerm (c z : ℂ) (h : z ≠ 0 ∨ c = 0) : ℂ :=
  if hc : c = 0 then 0 else Checked.div c z (h.resolve_right hc).isUnit

private lemma completedPoleTerm_eq_div (c z : ℂ) {h : z ≠ 0 ∨ c = 0} (hz : z ≠ 0) :
    completedPoleTerm c z h = Checked.div c z hz.isUnit := by
  by_cases hc : c = 0 <;> simp [completedPoleTerm, hc]

private lemma completedPoleTerm_const_mul (a c z : ℂ) (h : z ≠ 0 ∨ c = 0) :
    completedPoleTerm (a * c) z (h.imp_right fun hc ↦ by simp [hc]) =
      a * completedPoleTerm c z h := by
  by_cases hz : z = 0
  · have hc := h.resolve_left (fun hne ↦ hne hz)
    simp [completedPoleTerm, hc]
  · rw [completedPoleTerm_eq_div _ _ hz, completedPoleTerm_eq_div _ _ hz, mul_div_assoc₀]

/-- The regular domain of the completed congruence L-function. -/
abbrev completedLFunctionDomain (Φ : ZMod N → ℂ) : Set ℂ :=
  {s | (s ≠ 0 ∨ Φ 0 = 0) ∧ (s ≠ 1 ∨ ∑ j, Φ j = 0)}

/-- The completed L-function, continued across each point where its residue vanishes. -/
noncomputable def completedLFunction (Φ : ZMod N → ℂ) (s : ℂ)
    (hs : (s ≠ 0 ∨ Φ 0 = 0) ∧ (s ≠ 1 ∨ ∑ j, Φ j = 0) := by assumption) : ℂ :=
  completedLFunction₀ Φ s - N ^ (-s) * completedPoleTerm (Φ 0) s hs.1 -
    N ^ (-s) * completedPoleTerm (∑ j, Φ j) (1 - s)
      (hs.2.imp_left fun h ↦ sub_ne_zero.mpr h.symm)

/-- The completed L-function as a function on its regular domain. -/
noncomputable abbrev completedLFunctionOn (Φ : ZMod N → ℂ) (s : completedLFunctionDomain Φ) : ℂ :=
  completedLFunction Φ s (hs := s.2)

lemma completedLFunction_congr {Φ Ψ : ZMod N → ℂ} (h : Φ = Ψ) (s : ℂ)
    (hs : s ∈ completedLFunctionDomain Φ) :
    completedLFunction Φ s (hs := hs) = completedLFunction Ψ s (hs := h ▸ hs) := by
  subst Ψ
  rfl

lemma isOpen_completedLFunctionDomain (Φ : ZMod N → ℂ) : IsOpen (completedLFunctionDomain Φ) := by
  exact (isOpen_compl_singleton.union isOpen_const).inter
    (isOpen_compl_singleton.union isOpen_const)

@[simp] lemma completedLFunction_zero (s : ℂ) :
    completedLFunction (0 : ZMod N → ℂ) s (hs := ⟨Or.inr rfl, Or.inr (by simp)⟩) = 0 := by
  simp [completedLFunction, completedLFunction₀, completedPoleTerm]

private lemma completedLFunction₀_const_mul (a : ℂ) (Φ : ZMod N → ℂ) (s : ℂ) :
    completedLFunction₀ (fun j ↦ a * Φ j) s = a * completedLFunction₀ Φ s := by
  simp only [completedLFunction₀, mul_add, mul_sum]
  congr with j <;> ring

lemma completedLFunction_const_mul (a : ℂ) (Φ : ZMod N → ℂ) (s : ℂ)
    (hs : s ∈ completedLFunctionDomain Φ) :
    completedLFunction (fun j ↦ a * Φ j) s (hs := ⟨
      hs.1.imp_right (fun h ↦ by simp [h]),
      hs.2.imp_right (fun h ↦ by rw [← mul_sum, h, mul_zero])⟩) =
      a * completedLFunction Φ s (hs := hs) := by
  unfold completedLFunction
  simp only [completedLFunction₀_const_mul, ← mul_sum]
  rw [completedPoleTerm_const_mul a (Φ 0) s hs.1,
    completedPoleTerm_const_mul a (∑ j, Φ j) (1 - s)
      (hs.2.imp_left fun h ↦ sub_ne_zero.mpr h.symm)]
  ring

lemma completedLFunction_eq (Φ : ZMod N → ℂ) (s : ℂ) (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) :
    completedLFunction Φ s (hs := ⟨Or.inl hs₀, Or.inl hs₁⟩) =
      completedLFunction₀ Φ s - N ^ (-s) * Φ 0 / s - N ^ (-s) * (∑ j, Φ j) / (1 - s) := by
  have h₁ : (1 - s : ℂ) ≠ 0 := sub_ne_zero.mpr hs₁.symm
  rw [completedLFunction, completedPoleTerm_eq_div _ _ hs₀,
    completedPoleTerm_eq_div _ _ h₁, mul_div_assoc₀, mul_div_assoc₀]

lemma completedLFunction_eq_sum (Φ : ZMod N → ℂ) (s : ℂ) (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) :
    completedLFunction Φ s (hs := ⟨Or.inl hs₀, Or.inl hs₁⟩) =
      N ^ (-s) * (∑ j, Φ j * completedHurwitzZetaEven (toAddCircle j) s (hs := ⟨hs₁, Or.inl hs₀⟩)) +
        N ^ (-s) * ∑ j, Φ j * completedHurwitzZetaOdd (toAddCircle j) s := by
  rw [completedLFunction_eq Φ s hs₀ hs₁]
  have h (j : ZMod N) :
      completedHurwitzZetaEven (toAddCircle j) s (hs := ⟨hs₁, Or.inl hs₀⟩) =
        completedHurwitzZetaEven₀ (toAddCircle j) s -
          (if j = 0 then Checked.div 1 s hs₀.isUnit else 0) -
          Checked.div 1 (1 - s) (sub_ne_zero.mpr hs₁.symm).isUnit := by
    rw [completedHurwitzZetaEven_eq]
    by_cases hj : j = 0 <;> simp [hj, toAddCircle_eq_zero]
  simp only [h, div_eq_mul_inv₀, one_mul, mul_sub, mul_ite, mul_zero, sum_sub_distrib, sum_ite_eq',
    ← sum_mul, completedLFunction₀, mul_assoc]
  rw [ite_eq_left (Finset.mem_univ (0 : ZMod N))]
  abel

lemma completedLFunction_def_even (hΦ : Φ.Even) (s : ℂ) (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) :
    completedLFunction Φ s (hs := ⟨Or.inl hs₀, Or.inl hs₁⟩) =
      N ^ (-s) * ∑ j, Φ j * completedHurwitzZetaEven (toAddCircle j) s
        (hs := ⟨hs₁, Or.inl hs₀⟩) := by
  have h : ∑ j, Φ j * completedHurwitzZetaOdd (toAddCircle j) s = 0 := by
    refine (hΦ.mul_odd fun j ↦ ?_).sum_eq_zero
    rw [map_neg, completedHurwitzZetaOdd_neg]
  rw [completedLFunction_eq_sum Φ s hs₀ hs₁, h, mul_zero, add_zero]

lemma completedLFunction_def_odd (hΦ : Φ.Odd) (s : ℂ) :
    completedLFunction Φ s (hs := ⟨Or.inr hΦ.map_zero, Or.inr hΦ.sum_eq_zero⟩) =
      N ^ (-s) * ∑ j, Φ j * completedHurwitzZetaOdd (toAddCircle j) s := by
  have h : ∑ j, Φ j * completedHurwitzZetaEven₀ (toAddCircle j) s = 0 := by
    refine (hΦ.mul_even fun j ↦ ?_).sum_eq_zero
    rw [map_neg, completedHurwitzZetaEven₀_neg]
  simp [completedLFunction, completedLFunction₀, completedPoleTerm, hΦ.map_zero, hΦ.sum_eq_zero, h]

/-- At regular points the completion at level one is a scalar multiple of completed zeta. -/
lemma completedLFunction_modOne_eq (Φ : ZMod 1 → ℂ) (s : ℂ) (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) :
    completedLFunction Φ s (hs := ⟨Or.inl hs₀, Or.inl hs₁⟩) =
      Φ 1 * completedRiemannZeta s hs₀ hs₁ := by
  rw [completedLFunction_def_even (show Φ.Even from fun _ ↦ congr_arg Φ (Subsingleton.elim ..))
    s hs₀ hs₁, Nat.cast_one, one_cpow, one_mul, ← singleton_eq_univ 0, sum_singleton, map_zero,
    completedHurwitzZetaEven_zero, Subsingleton.elim 0 1]

/--
The completed L-function of a function `ZMod N → ℂ` is differentiable, with the following
exceptions: at `s = 1` if `∑ j, Φ j ≠ 0`; and at `s = 0` if `Φ 0 ≠ 0`.
-/
lemma differentiableAt_completedLFunction (Φ : ZMod N → ℂ) (s : ℂ)
    (hs : s ∈ completedLFunctionDomain Φ) :
    DifferentiableAt ℂ (completedLFunctionOn Φ) ⟨s, hs⟩ Subtype.val := by
  let D := completedLFunctionDomain Φ
  let x : D := ⟨s, hs⟩
  have hrestrict (f : ℂ → ℂ) (hf : DifferentiableAt ℂ f s) :
      DifferentiableAt ℂ (fun z : D ↦ f z) x Subtype.val := by
    obtain ⟨d, hd⟩ := hf
    exact ⟨d, HasFDerivAtFilter.comp_tendsto hd Subtype.val
      ((continuous_subtype_val.tendsto x).prodMap (tendsto_pure_pure ..))⟩
  have hpow : DifferentiableAt ℂ (fun z : D ↦ (N : ℂ) ^ (-(z : ℂ))) x Subtype.val :=
    hrestrict _ (differentiableAt_id.neg.const_cpow (Or.inl (Nat.cast_ne_zero.mpr (NeZero.ne N))))
  have h₀ : DifferentiableAt ℂ (fun z : D ↦ completedPoleTerm (Φ 0) z z.2.1) x Subtype.val := by
    by_cases hΦ : Φ 0 = 0
    · simpa only [completedPoleTerm, dite_eq_left hΦ] using
        hrestrict (fun _ ↦ 0) (differentiableAt_const 0)
    · let φ : D → {z : ℂ // IsUnit z} := fun z ↦ ⟨z, (z.2.1.resolve_right hΦ).isUnit⟩
      have hφ : Continuous φ := continuous_subtype_val.subtype_mk _
      obtain ⟨d, hd⟩ := (differentiableAt_const (Φ 0)).div differentiableAt_id
        (hs.1.resolve_right hΦ).isUnit
      simp only [completedPoleTerm, dite_eq_right hΦ]
      exact ⟨d, HasFDerivAtFilter.comp_tendsto hd φ
        ((hφ.tendsto x).prodMap (tendsto_pure_pure ..))⟩
  have h₁ : DifferentiableAt ℂ (fun z : D ↦ completedPoleTerm (∑ j, Φ j) (1 - z)
      (z.2.2.imp_left fun h ↦ sub_ne_zero.mpr h.symm)) x Subtype.val := by
    by_cases hΦ : ∑ j, Φ j = 0
    · simpa only [completedPoleTerm, dite_eq_left hΦ] using
        hrestrict (fun _ ↦ 0) (differentiableAt_const 0)
    · let φ : D → {z : ℂ // IsUnit (1 - z)} := fun z ↦
        ⟨z, (sub_ne_zero.mpr (z.2.2.resolve_right hΦ).symm).isUnit⟩
      have hφ : Continuous φ := continuous_subtype_val.subtype_mk _
      obtain ⟨d, hd⟩ := (differentiableAt_const (∑ j, Φ j)).div
        (differentiableAt_id.const_sub 1) (sub_ne_zero.mpr (hs.2.resolve_right hΦ).symm).isUnit
      simp only [completedPoleTerm, dite_eq_right hΦ]
      exact ⟨d, HasFDerivAtFilter.comp_tendsto hd φ
        ((hφ.tendsto x).prodMap (tendsto_pure_pure ..))⟩
  exact ((hrestrict _ (differentiable_completedLFunction₀ Φ s)).sub
    (hpow.mul h₀ continuousAt_subtype_val)).sub (hpow.mul h₁ continuousAt_subtype_val)

/--
Special case of `differentiableAt_completedLFunction` asserting differentiability everywhere
under suitable hypotheses.
-/
lemma differentiable_completedLFunction (hΦ₂ : Φ 0 = 0) (hΦ₃ : ∑ j, Φ j = 0) :
    Differentiable ℂ (fun s ↦ completedLFunction Φ s (hs := ⟨Or.inr hΦ₂, Or.inr hΦ₃⟩)) := by
  simpa only [completedLFunction, completedPoleTerm, dite_eq_left hΦ₂, dite_eq_left hΦ₃,
    mul_zero, sub_zero] using differentiable_completedLFunction₀ Φ

lemma continuous_completedLFunctionOn (Φ : ZMod N → ℂ) : Continuous (completedLFunctionOn Φ) := by
  refine continuous_iff_continuousAt.mpr fun z ↦ ?_
  exact (differentiableAt_completedLFunction Φ z z.2).continuousAt continuousAt_subtype_val

private lemma eq_of_continuous_eq_away_from_zero_one {U : Set ℂ} (hU : IsOpen U)
    {f g : U → ℂ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ z : U, (z : ℂ) ≠ 0 → (z : ℂ) ≠ 1 → f z = g z) : f = g := by
  have hd : Dense ({(0 : ℂ), 1} : Set ℂ)ᶜ := Set.Countable.dense_compl ℂ (by simp)
  refine hf.ext_on (hd.preimage hU.isOpenEmbedding_subtypeVal.isOpenMap) hg fun z hz ↦ ?_
  have hz' : (z : ℂ) ≠ 0 ∧ (z : ℂ) ≠ 1 := by simpa using hz
  exact h z hz'.1 hz'.2

/-- The even L-function is the product of its completion and the entire reciprocal Gamma factor
on the regular domain of the completion. -/
lemma LFunction_eq_completed_mul_reciprocalGammaℝ_even (hΦ : Φ.Even) (s : ℂ)
    (hs : s ∈ completedLFunctionDomain Φ) :
    LFunction Φ s (hs := hs.2) = completedLFunction Φ s (hs := hs) * reciprocalGammaℝ s := by
  let D := completedLFunctionDomain Φ
  let V := {z : ℂ // z ≠ 1 ∨ ∑ j, Φ j = 0}
  let F (z : D) := LFunction Φ z (hs := z.2.2)
  let G (z : D) := completedLFunctionOn Φ z * reciprocalGammaℝ z
  have hF₀ : Continuous (fun z : V ↦ LFunction Φ z (hs := z.2)) := by
    refine continuous_iff_continuousAt.mpr fun z ↦ ?_
    exact (differentiableAt_LFunction Φ z z.2).continuousAt continuousAt_subtype_val
  have hF : Continuous F := hF₀.comp (continuous_subtype_val.subtype_mk fun z : D ↦ z.2.2)
  have hG : Continuous G := (continuous_completedLFunctionOn Φ).mul
    (differentiable_reciprocalGammaℝ.continuous.comp continuous_subtype_val)
  suffices h : F = G from congrFun h ⟨s, hs⟩
  refine eq_of_continuous_eq_away_from_zero_one (isOpen_completedLFunctionDomain Φ) hF hG ?_
  intro z hz₀ hz₁
  have hodd : ∑ j, Φ j * hurwitzZetaOdd (toAddCircle j) z = 0 := by
    refine (hΦ.mul_odd fun j ↦ ?_).sum_eq_zero
    rw [map_neg, hurwitzZetaOdd_neg]
  dsimp only [F, G, completedLFunctionOn]
  rw [LFunction_eq_hurwitzZeta_sum Φ hz₁, completedLFunction_def_even hΦ z hz₀ hz₁,
    mul_assoc, sum_mul]
  simp only [hurwitzZeta, mul_add, sum_add_distrib, hodd, add_zero]
  congr 1
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [hurwitzZetaEven_def_of_ne_or_ne (Or.inr hz₀), mul_assoc]

/-- The odd L-function is the product of its entire completion and reciprocal Gamma factor. -/
lemma LFunction_eq_completed_mul_reciprocalGammaℝ_odd (hΦ : Φ.Odd) (s : ℂ) :
    LFunction Φ s (hs := Or.inr hΦ.sum_eq_zero) =
      completedLFunction Φ s (hs := ⟨Or.inr hΦ.map_zero, Or.inr hΦ.sum_eq_zero⟩) *
        reciprocalGammaℝ (s + 1) := by
  have heven : ∑ j, Φ j * hurwitzZetaEvenRegularPart (toAddCircle j) s = 0 := by
    refine (hΦ.mul_even fun j ↦ ?_).sum_eq_zero
    rw [map_neg]
    simp [hurwitzZetaEvenRegularPart]
  rw [LFunction_eq_regularPart_of_sum_zero hΦ.sum_eq_zero, LFunctionRegularPart,
    completedLFunction_def_odd hΦ, mul_assoc, sum_mul]
  simp only [hurwitzZetaRegularPart, mul_add, sum_add_distrib, heven, zero_add,
    hurwitzZetaOdd, mul_assoc]

/--
First form of functional equation for completed L-functions (even case).

Private because it is superseded by `completedLFunction_one_sub_even` below, which is valid for a
much wider range of `s`.
-/
private lemma completedLFunction_one_sub_of_one_lt_even (hΦ : Φ.Even) {s : ℂ} (hs : 1 < re s) :
    completedLFunction Φ (1 - s) (hs := ⟨Or.inl (by
      intro h
      have he := congrArg re h
      simp [sub_re, one_re] at he
      linarith), Or.inl (by
      intro h
      have he := congrArg re h
      simp [sub_re, one_re] at he
      linarith)⟩) =
      N ^ (s - 1) * completedLFunction (𝓕 Φ) s (hs := ⟨
        Or.inl (ne_zero_of_one_lt_re hs), Or.inl (by intro h; simp [h] at hs)⟩) := by
  have hs₀ : s ≠ 0 := ne_zero_of_one_lt_re hs
  have hs₁ : s ≠ 1 := (lt_irrefl _ <| one_re ▸ · ▸ hs)
  have hleft₀ : (1 - s : ℂ) ≠ 0 := sub_ne_zero.mpr hs₁.symm
  have hleft₁ : (1 - s : ℂ) ≠ 1 := by intro h; exact hs₀ (by linear_combination -h)
  have hdom : s ∈ completedLFunctionDomain (𝓕 Φ) := ⟨Or.inl hs₀, Or.inl hs₁⟩
  suffices h : (∑ j, Φ j * completedCosZeta (toAddCircle j) s
      (hs := ⟨hs₀, Or.inl hs₁⟩)) = completedLFunction (𝓕 Φ) s (hs := hdom) by
    simp only [completedLFunction_def_even hΦ (1 - s) hleft₀ hleft₁, neg_sub,
      completedHurwitzZetaEven_one_sub (hs := ⟨hs₀, Or.inl hs₁⟩), h]
  have hΓ := Gammaℝ_ne_zero_of_re_pos (zero_lt_one.trans hs)
  have hR : reciprocalGammaℝ s ≠ 0 := by
    rw [reciprocalGammaℝ_eq_inv (fun n hn ↦ hΓ (Gammaℝ_eq_zero_iff.mpr ⟨n, hn⟩))]
    exact inv_ne_zero
  apply mul_right_cancel₀ hR
  rw [← LFunction_eq_completed_mul_reciprocalGammaℝ_even (dft_even_iff.mpr hΦ) s hdom,
    sum_mul]
  simp only [mul_assoc, ← cosZeta_def (hs := Or.inl hs₁) hs₀]
  simp only [cosZeta_eq, ← mul_div_assoc₀, mul_add, ← sum_div, sum_add_distrib,
    LFunction_dft_of_ne_one Φ hs₁, map_neg, div_eq_iff, mul_two, add_left_inj]
  exact Fintype.sum_equiv (.neg _) _ _ (by simp [hΦ _])

/--
First form of functional equation for completed L-functions (odd case).

Private because it is superseded by `completedLFunction_one_sub_odd` below, which is valid for a
much wider range of `s`.
-/
private lemma completedLFunction_one_sub_of_one_lt_odd (hΦ : Φ.Odd) {s : ℂ} (hs : 1 < re s) :
    completedLFunction Φ (1 - s) (hs := ⟨Or.inr hΦ.map_zero, Or.inr hΦ.sum_eq_zero⟩) =
      N ^ (s - 1) * I * completedLFunction (𝓕 Φ) s (hs := ⟨
        Or.inr (dft_odd_iff.mpr hΦ).map_zero, Or.inr (dft_odd_iff.mpr hΦ).sum_eq_zero⟩) := by
  have hF := dft_odd_iff.mpr hΦ
  have hs₁ : s ≠ 1 := (lt_irrefl _ <| one_re ▸ · ▸ hs)
  have hdom : s ∈ completedLFunctionDomain (𝓕 Φ) := ⟨Or.inr hF.map_zero, Or.inr hF.sum_eq_zero⟩
  suffices h : ∑ j, Φ j * completedSinZeta (toAddCircle j) s =
      I * completedLFunction (𝓕 Φ) s (hs := hdom) by
    simp only [completedLFunction_def_odd hΦ, neg_sub, completedHurwitzZetaOdd_one_sub,
      h, mul_assoc]
  have hs' : 0 < re (s + 1) := by simp only [add_re, one_re]; linarith
  have hΓ := Gammaℝ_ne_zero_of_re_pos hs'
  have hR : reciprocalGammaℝ (s + 1) ≠ 0 := by
    rw [reciprocalGammaℝ_eq_inv (fun n hn ↦ hΓ (Gammaℝ_eq_zero_iff.mpr ⟨n, hn⟩))]
    exact inv_ne_zero
  apply mul_right_cancel₀ hR
  rw [mul_assoc, ← LFunction_eq_completed_mul_reciprocalGammaℝ_odd hF s, sum_mul]
  simp only [mul_assoc]
  change (∑ j, Φ j * sinZeta (toAddCircle j) s) = _
  rw [LFunction_dft_of_ne_one Φ hs₁]
  have hsum : (∑ j, Φ j * expZeta (toAddCircle j) s (Or.inl hs₁)) =
      -(∑ j, Φ j * expZeta (toAddCircle (-j)) s (Or.inl hs₁)) := by
    calc
      _ = ∑ j, Φ (-j) * expZeta (toAddCircle (-j)) s (Or.inl hs₁) :=
        Fintype.sum_equiv (.neg _) _ _ (by simp)
      _ = _ := by simp only [hΦ _, neg_mul, sum_neg_distrib]
  simp_rw [sinZeta_eq _ _ (Or.inl hs₁), ← mul_div_assoc₀, mul_sub, ← sum_div,
    sum_sub_distrib, ← map_neg, hsum, div_eq_mul_inv₀, mul_inv₀, inv_I]
  ring

private lemma completedPoleTerm_mul (c z : ℂ) (h : z ≠ 0 ∨ c = 0) :
    completedPoleTerm c z h * z = c := by
  by_cases hc : c = 0
  · simp [completedPoleTerm, hc]
  · rw [completedPoleTerm_eq_div _ _ (h.resolve_right hc), div_mul_cancel₀]

private noncomputable def completedLFunction₁ (Φ : ZMod N → ℂ) (s : ℂ) : ℂ :=
  s * (1 - s) * completedLFunction₀ Φ s - N ^ (-s) * (1 - s) * Φ 0 -
    N ^ (-s) * s * (∑ j, Φ j)

private lemma differentiable_completedLFunction₁ (Φ : ZMod N → ℂ) :
    Differentiable ℂ (completedLFunction₁ Φ) := by
  have hp : Differentiable ℂ (fun s : ℂ ↦ (N : ℂ) ^ (-s)) :=
    differentiable_id.neg.const_cpow (Or.inl (Nat.cast_ne_zero.mpr (NeZero.ne N)))
  have hsub : Differentiable ℂ (fun s : ℂ ↦ 1 - s) := differentiable_id.const_sub 1
  exact (((differentiable_id.mul hsub).mul (differentiable_completedLFunction₀ Φ)).sub
    ((hp.mul hsub).mul_const _)).sub ((hp.mul differentiable_id).mul_const _)

private lemma completedLFunction₁_eq_mul (Φ : ZMod N → ℂ) (s : ℂ)
    (hs : s ∈ completedLFunctionDomain Φ) :
    completedLFunction₁ Φ s = s * (1 - s) * completedLFunction Φ s (hs := hs) := by
  have h₀ := completedPoleTerm_mul (Φ 0) s hs.1
  have h₁ := completedPoleTerm_mul (∑ j, Φ j) (1 - s)
    (hs.2.imp_left fun h ↦ sub_ne_zero.mpr h.symm)
  unfold completedLFunction₁ completedLFunction
  linear_combination ((N : ℂ) ^ (-s)) * (1 - s) * h₀ + ((N : ℂ) ^ (-s)) * s * h₁

private lemma completedLFunctionDomain_one_sub {s : ℂ} (hs₀ : s ≠ 0 ∨ ∑ j, Φ j = 0)
    (hs₁ : s ≠ 1 ∨ Φ 0 = 0) : 1 - s ∈ completedLFunctionDomain Φ :=
  ⟨hs₁.imp_left (sub_ne_zero.mpr ∘ Ne.symm), hs₀.imp_left fun h h' ↦
    h (by linear_combination -h')⟩

private lemma completedLFunctionDomain_dft {s : ℂ} (hs₀ : s ≠ 0 ∨ ∑ j, Φ j = 0)
    (hs₁ : s ≠ 1 ∨ Φ 0 = 0) : s ∈ completedLFunctionDomain (𝓕 Φ) :=
  ⟨hs₀.imp_right (fun h ↦ dft_apply_zero Φ ▸ h),
    hs₁.imp_right (fun h ↦ by simp only [← dft_apply_zero, dft_dft, neg_zero, h, smul_zero])⟩

private lemma completedLFunction₁_one_sub_even (hΦ : Φ.Even) :
    (fun s : ℂ ↦ completedLFunction₁ Φ (1 - s)) =
      fun s ↦ N ^ (s - 1) * completedLFunction₁ (𝓕 Φ) s := by
  have hF' : Differentiable ℂ (fun s : ℂ ↦ completedLFunction₁ Φ (1 - s)) :=
    (differentiable_completedLFunction₁ Φ).comp (differentiable_id.const_sub 1)
  have hF := hF'.differentiableOn.analyticOnNhd isOpen_univ
  have hp : Differentiable ℂ (fun s : ℂ ↦ (N : ℂ) ^ (s - 1)) :=
    (differentiable_id.sub_const 1).const_cpow (Or.inl (Nat.cast_ne_zero.mpr (NeZero.ne N)))
  have hG := (hp.mul (differentiable_completedLFunction₁ (𝓕 Φ))).differentiableOn.analyticOnNhd
    isOpen_univ
  refine AnalyticOnNhd.eq_of_frequently_eq (z₀ := (2 : ℂ)) hF hG ?_
  have h : {z : ℂ | 1 < z.re} ∈ 𝓝[≠] (2 : ℂ) := nhdsWithin_le_nhds
    ((continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by simp))
  apply (eventually_of_mem h fun z hz ↦ ?_).frequently
  have hz' : 1 < z.re := hz
  have hz₀ := ne_zero_of_one_lt_re hz'
  have hz₁ : z ≠ 1 := (lt_irrefl _ <| one_re ▸ · ▸ hz')
  rw [completedLFunction₁_eq_mul Φ (1 - z)
      (completedLFunctionDomain_one_sub (Or.inl hz₀) (Or.inl hz₁)),
    completedLFunction₁_eq_mul (𝓕 Φ) z ⟨Or.inl hz₀, Or.inl hz₁⟩,
    completedLFunction_one_sub_of_one_lt_even hΦ hz']
  ring

private lemma completedLFunction_one_sub_even_of_ne (hΦ : Φ.Even) (s : ℂ)
    (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) :
    completedLFunction Φ (1 - s)
      (hs := completedLFunctionDomain_one_sub (Or.inl hs₀) (Or.inl hs₁)) =
      N ^ (s - 1) * completedLFunction (𝓕 Φ) s (hs := ⟨Or.inl hs₀, Or.inl hs₁⟩) := by
  have h := congrFun (completedLFunction₁_one_sub_even hΦ) s
  rw [completedLFunction₁_eq_mul Φ _ (completedLFunctionDomain_one_sub (Or.inl hs₀) (Or.inl hs₁)),
    completedLFunction₁_eq_mul (𝓕 Φ) _ ⟨Or.inl hs₀, Or.inl hs₁⟩] at h
  have hprod : (1 - s) * (1 - (1 - s)) = s * (1 - s) := by ring
  rw [hprod, mul_left_comm ((N : ℂ) ^ (s - 1)) (s * (1 - s))] at h
  exact mul_left_cancel₀ (mul_ne_zero hs₀ (sub_ne_zero.mpr hs₁.symm)) h

/-- The even functional equation on the regular domains of both completions. -/
theorem completedLFunction_one_sub_even (hΦ : Φ.Even) (s : ℂ)
    (hs₀ : s ≠ 0 ∨ ∑ j, Φ j = 0) (hs₁ : s ≠ 1 ∨ Φ 0 = 0) :
    completedLFunction Φ (1 - s) (hs := by exact completedLFunctionDomain_one_sub hs₀ hs₁) =
      N ^ (s - 1) * completedLFunction (𝓕 Φ) s
        (hs := by exact completedLFunctionDomain_dft hs₀ hs₁) := by
  let U : Set ℂ := {z | (z ≠ 0 ∨ ∑ j, Φ j = 0) ∧ (z ≠ 1 ∨ Φ 0 = 0)}
  have hU : IsOpen U := (isOpen_compl_singleton.union isOpen_const).inter
    (isOpen_compl_singleton.union isOpen_const)
  let l (z : U) : completedLFunctionDomain Φ :=
    ⟨1 - z, completedLFunctionDomain_one_sub z.2.1 z.2.2⟩
  let r (z : U) : completedLFunctionDomain (𝓕 Φ) :=
    ⟨z, completedLFunctionDomain_dft z.2.1 z.2.2⟩
  have hl : Continuous l := (continuous_const.sub continuous_subtype_val).subtype_mk _
  have hr : Continuous r := continuous_subtype_val.subtype_mk _
  let F := completedLFunctionOn Φ ∘ l
  let G (z : U) := (N : ℂ) ^ ((z : ℂ) - 1) * (completedLFunctionOn (𝓕 Φ) ∘ r) z
  let x : U := ⟨s, hs₀, hs₁⟩
  change F x = G x
  have hF : Continuous F := (continuous_completedLFunctionOn Φ).comp hl
  have hsub : Continuous (fun z : U ↦ (z : ℂ) - 1) := continuous_subtype_val.sub continuous_const
  have hpow := hsub.const_cpow (Or.inl (Nat.cast_ne_zero.mpr (NeZero.ne N)))
  have hG : Continuous G := hpow.mul ((continuous_completedLFunctionOn (𝓕 Φ)).comp hr)
  have h : F = G := eq_of_continuous_eq_away_from_zero_one hU hF hG
    (fun z hz₀ hz₁ ↦ completedLFunction_one_sub_even_of_ne hΦ z hz₀ hz₁)
  exact congrFun h x

/-- Functional equation for completed L-functions (odd case), valid for all `s`. -/
theorem completedLFunction_one_sub_odd (hΦ : Φ.Odd) (s : ℂ) :
    completedLFunction Φ (1 - s) (hs := ⟨Or.inr hΦ.map_zero, Or.inr hΦ.sum_eq_zero⟩) =
      N ^ (s - 1) * I * completedLFunction (𝓕 Φ) s (hs := ⟨
        Or.inr (dft_odd_iff.mpr hΦ).map_zero, Or.inr (dft_odd_iff.mpr hΦ).sum_eq_zero⟩) := by
  have hD := dft_odd_iff.mpr hΦ
  let F (t : ℂ) := completedLFunction Φ (1 - t) (hs := ⟨Or.inr hΦ.map_zero, Or.inr hΦ.sum_eq_zero⟩)
  let G (t : ℂ) := (N : ℂ) ^ (t - 1) * I * completedLFunction (𝓕 Φ) t
    (hs := ⟨Or.inr hD.map_zero, Or.inr hD.sum_eq_zero⟩)
  have hF : Differentiable ℂ F := (differentiable_completedLFunction hΦ.map_zero
    hΦ.sum_eq_zero).comp (differentiable_id.const_sub 1)
  have hG : Differentiable ℂ G := by
    apply (((differentiable_id.sub_const 1).const_cpow (.inl (NeZero.ne _))).mul_const _).mul
    exact differentiable_completedLFunction hD.map_zero hD.sum_eq_zero
  -- set where we know equality
  have : {z | 1 < re z} ∈ 𝓝 2 := (continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds (by simp)
  have hFG : F =ᶠ[𝓝 2] G := by filter_upwards [this] with t ht
    using completedLFunction_one_sub_of_one_lt_odd hΦ ht
  -- now apply the big hammer to finish
  rw [← analyticOnNhd_univ_iff_differentiable] at hF hG
  exact congr_fun (hF.eq_of_eventuallyEq hG hFG) s

end signed

end ZMod
