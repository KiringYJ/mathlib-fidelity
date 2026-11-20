/-
Copyright (c) 2024 Lawrence Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lawrence Wu
-/
module

public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.MellinTransform

/-!
# Mellin inversion formula

We derive the Mellin inversion formula as a consequence of the Fourier inversion formula.

## Main results
- `mellinInv_mellin_eq`: Mellin inversion recovers the value of a function at a point of
  continuity in the positive half-line.
-/

public section

open Real Complex Set MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

open scoped FourierTransform

private noncomputable def expPositive (x : ℝ) : Ioi (0 : ℝ) :=
  ⟨rexp x, mem_Ioi.mpr (Real.exp_pos x)⟩

private theorem continuous_expPositive : Continuous expPositive :=
  Real.continuous_exp.subtype_mk _

private theorem rexp_neg_deriv_aux :
    ∀ x ∈ univ, HasDerivWithinAt (rexp ∘ Neg.neg) (-rexp (-x)) univ x :=
  fun x _ ↦ mul_neg_one (rexp (-x)) ▸
    ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).hasDerivWithinAt

private theorem rexp_neg_image_aux : rexp ∘ Neg.neg '' univ = Ioi 0 := by
  rw [Set.image_comp, Set.image_univ_of_surjective neg_surjective, Set.image_univ, Real.range_exp]

private theorem rexp_neg_injOn_aux : univ.InjOn (rexp ∘ Neg.neg) :=
  Real.exp_injective.injOn.comp neg_injective.injOn (univ.mapsTo_univ _)

private theorem rexp_cexp_aux (x : ℝ) (s : ℂ) (f : E) :
    rexp (-x) • cexp (-↑x) ^ (s - 1) • f = cexp (-s * ↑x) • f := by
  change (rexp (-x) : ℂ) • _ = _ • f
  rw [← smul_assoc, smul_eq_mul]
  push_cast
  conv in cexp _ * _ => lhs; rw [← cpow_one (cexp _)]
  rw [← cpow_add _ _ (Complex.exp_ne_zero _), cpow_def_of_ne_zero (Complex.exp_ne_zero _),
    Complex.log_exp (by simp [pi_pos]) (by simpa using pi_nonneg)]
  ring_nf

/-- In logarithmic coordinates, the Mellin transform is a Fourier transform. -/
theorem mellin_eq_fourier (f : Ioi (0 : ℝ) → E) {s : ℂ} :
    mellin f s = 𝓕 (fun u : ℝ ↦
      rexp (-s.re * u) • f ⟨rexp (-u), mem_Ioi.mpr (Real.exp_pos _)⟩)
      (s.im / (2 * π)) := by
  let f' : ℝ → E := Function.extend Subtype.val f 0
  have hf' (x : Ioi (0 : ℝ)) : f' x.val = f x :=
    Subtype.val_injective.extend_apply f _ x
  have hrestrict : (fun x : Ioi (0 : ℝ) ↦ f' x.val) = f := funext hf'
  calc
    mellin f s
      = ∫ (u : ℝ), Complex.exp (-s * u) • f ⟨rexp (-u), mem_Ioi.mpr (Real.exp_pos _)⟩ := by
      rw [← hrestrict, mellin_eq_integral f' s]
      conv_lhs => rw [← rexp_neg_image_aux]
      rw [integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ rexp_neg_deriv_aux
        rexp_neg_injOn_aux]
      simp [rexp_cexp_aux]
    _ = ∫ (u : ℝ), Complex.exp (↑(-2 * π * (u * (s.im / (2 * π)))) * I) •
        (rexp (-s.re * u) • f ⟨rexp (-u), mem_Ioi.mpr (Real.exp_pos _)⟩) := by
      congr
      ext u
      trans Complex.exp (-s.im * u * I) •
        (rexp (-s.re * u) • f ⟨rexp (-u), mem_Ioi.mpr (Real.exp_pos _)⟩)
      · conv => lhs; rw [← re_add_im s]
        rw [neg_add, add_mul, Complex.exp_add, mul_comm, ← smul_eq_mul, smul_assoc]
        norm_cast
        push_cast
        ring_nf
      congr
      simp [field]
    _ = _ := by
      simp [fourier_eq', mul_comm]

theorem mellinInv_eq_fourierInv (σ : ℝ) (f : ℂ → E) (x : Ioi (0 : ℝ)) :
    mellinInv σ f x =
    (x.val : ℂ) ^ (-σ : ℂ) •
      𝓕⁻ (fun (y : ℝ) ↦ f (σ + 2 * π * y * I)) (-Real.log x.val) := calc
  mellinInv σ f x
    = (x.val : ℂ) ^ (-σ : ℂ) •
      (∫ (y : ℝ), Complex.exp (2 * π * (y * (-Real.log x.val)) * I) •
        f (σ + 2 * π * y * I)) := by
    rw [mellinInv, one_div₀, ← abs_of_pos (show 0 < (2 * π)⁻¹ by positivity)]
    have hx0 : (x.val : ℂ) ≠ 0 := ofReal_ne_zero.mpr x.property.ne'
    simp_rw [neg_add, cpow_add _ _ hx0, mul_smul, integral_smul]
    rw [smul_comm, ← Measure.integral_comp_mul_left _ (2 * π)
      (ha := Real.two_pi_pos.ne'.isUnit)]
    congr! 3
    rw [cpow_def_of_ne_zero hx0, ← Complex.ofReal_log x.property.le]
    push_cast
    ring_nf
  _ = _ := by
    simp [fourierInv_eq', mul_comm (Real.log _)]

variable [CompleteSpace E]

/-- Mellin inversion recovers `f x` at each point of continuity on its positive source domain. -/
theorem mellinInv_mellin_eq (σ : ℝ) (f : Ioi (0 : ℝ) → E) {x : Ioi (0 : ℝ)}
    (hf : MellinConvergent f σ)
    (hFf : VerticalIntegrable (mellin f) σ) (hfx : ContinuousAt f x) :
    mellinInv σ (mellin f) x = f x := by
  let g := fun (u : ℝ) => rexp (-σ * u) • f (expPositive (-u))
  replace hf : Integrable g := by
    let f' : ℝ → E := Function.extend Subtype.val f 0
    have hf' (x : Ioi (0 : ℝ)) : f' x.val = f x :=
      Subtype.val_injective.extend_apply f _ x
    have hrestrict : (fun x : Ioi (0 : ℝ) ↦ f' x.val) = f := funext hf'
    rw [← hrestrict, mellinConvergent_iff_integrableOn (f := f'), ← rexp_neg_image_aux,
      integrableOn_image_iff_integrableOn_abs_deriv_smul
      MeasurableSet.univ rexp_neg_deriv_aux rexp_neg_injOn_aux] at hf
    replace hf : Integrable fun (x : ℝ) ↦ cexp (-↑σ * ↑x) • f' (rexp (-x)) := by
      simpa [rexp_cexp_aux] using hf
    change Integrable (fun t : ℝ ↦ cexp (-↑σ * ↑t) • f' (expPositive (-t)).val) at hf
    simp_rw [hf'] at hf
    norm_cast at hf
  replace hFf : Integrable (𝓕 g) := by
    have h2π : 2 * π ≠ 0 := by simp
    have : Integrable (𝓕 (fun u ↦ rexp (-(σ * u)) • f (expPositive (-u)))) := by
      simpa [Complex.VerticalIntegrable, mellin_eq_fourier, expPositive, mul_div_cancel_right₀]
        using hFf.comp_mul_right' h2π
    simp_rw [neg_mul_eq_neg_mul] at this
    exact this
  replace hfx : ContinuousAt g (-Real.log x.val) := by
    have hx : expPositive (- -Real.log x.val) = x :=
      Subtype.ext (by simp [expPositive, Real.exp_log x.property])
    refine ContinuousAt.fun_smul (by fun_prop) (ContinuousAt.comp (hx.symm ▸ hfx) ?_)
    exact continuous_expPositive.continuousAt.comp continuous_neg.continuousAt
  calc
    mellinInv σ (mellin f) x
      = mellinInv σ (fun s ↦ 𝓕 g (s.im / (2 * π))) x := by
      simp [g, expPositive, mellinInv, mellin_eq_fourier]
    _ = (x.val : ℂ) ^ (-σ : ℂ) • g (-Real.log x.val) := by
      rw [mellinInv_eq_fourierInv, ← hf.fourierInv_fourier_eq hFf hfx]
      simp [mul_div_cancel_left₀]
    _ = (x.val : ℂ) ^ (-σ : ℂ) • rexp (σ * Real.log x.val) • f x := by
      have hx : expPositive (Real.log x.val) = x :=
        Subtype.ext (Real.exp_log x.property)
      simp [g, hx]
    _ = f x := by
      norm_cast
      rw [mul_comm σ, ← rpow_def_of_pos x.property, ← Complex.ofReal_cpow x.property.le]
      norm_cast
      have hpow : IsUnit (x.val ^ σ) := (rpow_pos_of_pos x.property σ).ne'.isUnit
      rw [← smul_assoc, smul_eq_mul, Real.rpow_neg x.property.le (hxy := hpow),
        inv_mul_cancel₀, one_smul]
