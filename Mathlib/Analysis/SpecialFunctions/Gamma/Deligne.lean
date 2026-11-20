/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Deligne's archimedean Gamma-factors

In the theory of L-series one frequently encounters the following functions (of a complex variable
`s`) introduced in Deligne's landmark paper *Valeurs de fonctions L et périodes d'intégrales*:

$$ \Gamma_{\mathbb{R}}(s) = \pi ^ {-s / 2} \Gamma (s / 2) $$

and

$$ \Gamma_{\mathbb{C}}(s) = 2 (2 \pi) ^ {-s} \Gamma (s). $$

These are the factors that need to be included in the Dedekind zeta function of a number field
for each real, resp. complex, infinite place.

(Note that these are *not* the same as Mathlib's `Real.Gamma` vs. `Complex.Gamma`; Deligne's
functions both take a complex variable as input.)

This file defines these functions, and proves some elementary properties, including a reflection
formula which is an important input in functional equations of (un-completed) Dirichlet L-functions.
-/

@[expose] public section

open Filter Asymptotics Real Set MeasureTheory
open Complex

open scoped Topology

namespace Complex

/-- Deligne's archimedean Gamma factor for a real infinite place.

See "Valeurs de fonctions L et périodes d'intégrales" § 5.3. Note that this is not the same as
`Real.Gamma`; in particular it is a function `ℂ → ℂ`. -/
noncomputable def Gammaℝ (s : ℂ) := π ^ (-s / 2) * Gamma (s / 2)

lemma Gammaℝ_def (s : ℂ) : Gammaℝ s = π ^ (-s / 2) * Gamma (s / 2) := rfl

/-- Deligne's archimedean Gamma factor for a complex infinite place.

See "Valeurs de fonctions L et périodes d'intégrales" § 5.3. (Some authors omit the factor of 2).
Note that this is not the same as `Complex.Gamma`. -/
noncomputable def Gammaℂ (s : ℂ) := 2 * (2 * π) ^ (-s) * Gamma s

lemma Gammaℂ_def (s : ℂ) : Gammaℂ s = 2 * (2 * π) ^ (-s) * Gamma s := rfl

/-- The entire reciprocal of Deligne's Gamma factor for a real infinite place. -/
noncomputable def reciprocalGammaℝ (s : ℂ) := π ^ (s / 2) * reciprocalGamma (s / 2)

/-- The entire reciprocal of Deligne's Gamma factor for a complex infinite place. -/
noncomputable def reciprocalGammaℂ (s : ℂ) := (2 * π) ^ s * reciprocalGamma s / 2

lemma Gammaℝ_add_two {s : ℂ} (hs : s ≠ 0) : Gammaℝ (s + 2) = Gammaℝ s * s / 2 / π := by
  have hp : IsUnit (π : ℂ) := (ofReal_ne_zero.mpr pi_ne_zero).isUnit
  rw [Gammaℝ_def, Gammaℝ_def, neg_div₀, add_div, neg_add, div_self,
    Gamma_add_one _ (div_ne_zero hs), cpow_add _ _ hp.ne_zero, cpow_neg_one _ (hx := hp)]
  simp only [div_eq_mul_inv₀]
  ring

lemma Gammaℂ_add_one {s : ℂ} (hs : s ≠ 0) : Gammaℂ (s + 1) = Gammaℂ s * s / 2 / π := by
  have hp : IsUnit (2 * π : ℂ) := (mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr pi_ne_zero)).isUnit
  rw [Gammaℂ_def, Gammaℂ_def, Gamma_add_one _ hs, neg_add,
    cpow_add _ _ hp.ne_zero, cpow_neg_one _ (hx := hp), div_div₀]
  simp only [div_eq_mul_inv₀]
  ring

lemma Gammaℝ_ne_zero_of_re_pos {s : ℂ} (hs : 0 < re s) : Gammaℝ s ≠ 0 := by
  apply mul_ne_zero
  · simp [pi_ne_zero]
  · apply Gamma_ne_zero_of_re_pos
    rw [div_ofNat_re]
    exact div_pos hs two_pos

lemma Gammaℝ_eq_zero_iff {s : ℂ} : Gammaℝ s = 0 ↔ ∃ n : ℕ, s = -(2 * n) := by
  simp [Gammaℝ_def, Complex.Gamma_eq_zero_iff, pi_ne_zero, div_eq_iff, mul_comm]

lemma Gammaℝ_ne_zero {s : ℂ} (hs : ∀ n : ℕ, s ≠ -(2 * n)) : Gammaℝ s ≠ 0 := by
  rintro h
  obtain ⟨n, hn⟩ := Gammaℝ_eq_zero_iff.mp h
  exact hs n hn

lemma Gammaℂ_ne_zero {s : ℂ} (hs : ∀ n : ℕ, s ≠ -n) : Gammaℂ s ≠ 0 := by
  rw [Gammaℂ_def]
  exact mul_ne_zero (mul_ne_zero two_ne_zero (cpow_ne_zero_iff.mpr
    (Or.inl (mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr pi_ne_zero))))) (Gamma_ne_zero hs)

lemma reciprocalGammaℝ_mul_Gammaℝ {s : ℂ} (hs : ∀ n : ℕ, s ≠ -(2 * n)) :
    reciprocalGammaℝ s * Gammaℝ s = 1 := by
  have hp : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr pi_ne_zero
  have hhalf : ∀ n : ℕ, s / 2 ≠ -n := by
    intro n hn
    apply hs n
    have := div_eq_iff.mp hn
    linear_combination this
  have hpowers : (π : ℂ) ^ (s / 2) * (π : ℂ) ^ (-s / 2) = 1 := by
    rw [← cpow_add _ _ hp, show s / 2 + -s / 2 = 0 by ring, cpow_zero]
  rw [reciprocalGammaℝ, Gammaℝ_def, mul_mul_mul_comm, hpowers, reciprocalGamma_mul_Gamma hhalf,
    one_mul]

lemma reciprocalGammaℂ_mul_Gammaℂ {s : ℂ} (hs : ∀ n : ℕ, s ≠ -n) :
    reciprocalGammaℂ s * Gammaℂ s = 1 := by
  have hp : (2 * π : ℂ) ≠ 0 := mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr pi_ne_zero)
  have hpowers : (2 * π : ℂ) ^ s * (2 * π : ℂ) ^ (-s) = 1 := by
    rw [← cpow_add _ _ hp, add_neg_cancel, cpow_zero]
  rw [reciprocalGammaℂ, Gammaℂ_def, ← mul_assoc, ← mul_assoc, div_mul_cancel₀]
  rw [mul_assoc ((2 * π : ℂ) ^ s * reciprocalGamma s), mul_mul_mul_comm, hpowers,
    reciprocalGamma_mul_Gamma hs, one_mul]

lemma reciprocalGammaℝ_eq_inv {s : ℂ} (hs : ∀ n : ℕ, s ≠ -(2 * n)) :
    reciprocalGammaℝ s = Checked.inv (Gammaℝ s) (Gammaℝ_ne_zero hs).isUnit := by
  apply mul_right_cancel₀ (Gammaℝ_ne_zero hs)
  rw [reciprocalGammaℝ_mul_Gammaℝ hs, inv_mul_cancel₀]

lemma reciprocalGammaℂ_eq_inv {s : ℂ} (hs : ∀ n : ℕ, s ≠ -n) :
    reciprocalGammaℂ s = Checked.inv (Gammaℂ s) (Gammaℂ_ne_zero hs).isUnit := by
  apply mul_right_cancel₀ (Gammaℂ_ne_zero hs)
  rw [reciprocalGammaℂ_mul_Gammaℂ hs, inv_mul_cancel₀]

@[simp]
lemma reciprocalGammaℝ_eq_zero_iff {s : ℂ} :
    reciprocalGammaℝ s = 0 ↔ ∃ n : ℕ, s = -(2 * n) := by
  simp [reciprocalGammaℝ, reciprocalGamma_eq_zero_iff, pi_ne_zero,
    div_eq_iff, mul_comm]

@[simp]
lemma reciprocalGammaℂ_eq_zero_iff {s : ℂ} :
    reciprocalGammaℂ s = 0 ↔ ∃ n : ℕ, s = -n := by
  simp [reciprocalGammaℂ, reciprocalGamma_eq_zero_iff, pi_ne_zero]

@[simp]
lemma Gammaℝ_one : Gammaℝ 1 = 1 := by
  rw [Gammaℝ_def, Complex.Gamma_one_half_eq]
  simp [neg_div₀, cpow_neg, pi_ne_zero]

@[simp]
lemma Gammaℂ_one : Gammaℂ 1 = 1 / π := by
  have hp : IsUnit (2 * π : ℂ) := (mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr pi_ne_zero)).isUnit
  rw [Gammaℂ_def, cpow_neg_one _ (hx := hp), Complex.Gamma_one, mul_one]
  apply (eq_div_iff).mpr
  calc
    _ = Checked.inv (2 * π : ℂ) hp * (2 * π) := by ring
    _ = 1 := inv_mul_cancel₀ (ha := hp)

section analyticity

@[fun_prop]
lemma differentiable_reciprocalGammaℝ : Differentiable ℂ reciprocalGammaℝ := by
  unfold reciprocalGammaℝ
  refine Differentiable.mul ?_ ?_
  · exact (differentiable_id.div_const (2 : ℂ)).const_cpow
      (Or.inl (ofReal_ne_zero.mpr pi_ne_zero))
  · exact differentiable_reciprocalGamma.comp (differentiable_id.div_const _)

@[fun_prop]
lemma differentiable_reciprocalGammaℂ : Differentiable ℂ reciprocalGammaℂ := by
  unfold reciprocalGammaℂ
  refine (Differentiable.mul ?_ differentiable_reciprocalGamma).div_const _
  exact differentiable_id.const_cpow
    (Or.inl (mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr pi_ne_zero)))

@[simp]
lemma reciprocalGammaℝ_one : reciprocalGammaℝ 1 = 1 := by
  rw [reciprocalGammaℝ_eq_inv (by intro n; exact_mod_cast (by omega : (1 : ℤ) ≠ -(2 * n)))]
  simp

@[simp]
lemma reciprocalGammaℂ_one : reciprocalGammaℂ 1 = π := by
  simp [reciprocalGammaℂ]

@[simp]
lemma reciprocalGammaℝ_two : reciprocalGammaℝ 2 = π := by
  simp [reciprocalGammaℝ]

/-- The recurrence for the entire reciprocal real-place Gamma factor, including its zeros. -/
lemma reciprocalGammaℝ_eq_self_mul_reciprocalGammaℝ_add_two (s : ℂ) :
    reciprocalGammaℝ s = s * reciprocalGammaℝ (s + 2) / 2 / π := by
  have hp : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr pi_ne_zero
  rw [reciprocalGammaℝ, reciprocalGammaℝ,
    show (s + 2) / 2 = s / 2 + 1 by ring,
    reciprocalGamma_eq_self_mul_reciprocalGamma_add_one (s / 2), cpow_add _ _ hp, cpow_one]
  field

lemma Gammaℝ_residue_zero : Tendsto (fun s ↦ s * Gammaℝ s) (𝓝[≠] 0) (𝓝 2) := by
  have h : Tendsto (fun z : ℂ ↦ z / 2 * Gamma (z / 2)) (𝓝[≠] 0) (𝓝 1) := by
    refine tendsto_self_mul_Gamma_nhds_zero.comp ?_
    rw [tendsto_nhdsWithin_iff, (by simp : 𝓝 (0 : ℂ) = 𝓝 (0 / 2))]
    exact ⟨(tendsto_id.div_const₀ _).mono_left nhdsWithin_le_nhds,
      eventually_of_mem self_mem_nhdsWithin fun x hx ↦ div_ne_zero hx⟩
  have h' : Tendsto (fun s : ℂ ↦ 2 * (π : ℂ) ^ (-s / 2)) (𝓝[≠] 0) (𝓝 2) := by
    rw [(by simp : 𝓝 2 = 𝓝 (2 * (π : ℂ) ^ (-(0 : ℂ) / 2)))]
    refine Tendsto.mono_left (ContinuousAt.tendsto ?_) nhdsWithin_le_nhds
    exact continuousAt_const.mul ((continuousAt_const_cpow (ofReal_ne_zero.mpr pi_ne_zero)).comp
      (by fun_prop))
  convert! mul_one (2 : ℂ) ▸ (h'.mul h) using 2 with z
  rw [Gammaℝ]
  ring_nf

end analyticity

section reflection

private lemma ofReal_sqrt_pi_eq_cpow_half : (↑(√π) : ℂ) = (π : ℂ) ^ (1 / 2 : ℂ) := by
  have hhalf : (↑(1 / 2 : ℝ) : ℂ) = 1 / 2 := by
    apply (eq_div_iff).mpr
    rw [← ofReal_ofNat 2, ← ofReal_mul]
    norm_num
  rw [sqrt_eq_rpow, ofReal_cpow pi_pos.le, hhalf]

/-- Reformulation of the doubling formula in terms of `Gammaℝ`. -/
lemma Gammaℝ_mul_Gammaℝ_add_one (s : ℂ) : Gammaℝ s * Gammaℝ (s + 1) = Gammaℂ s := by
  simp only [Gammaℝ_def, Gammaℂ_def]
  calc
  _ = (π ^ (-s / 2) * π ^ (-(s + 1) / 2)) * (Gamma (s / 2) * Gamma (s / 2 + 1 / 2)) := by ring_nf
  _ = 2 ^ (1 - s) * (π ^ (-1 / 2 - s) * π ^ (1 / 2 : ℂ)) * Gamma s := by
    rw [← cpow_add _ _ (ofReal_ne_zero.mpr pi_ne_zero), Complex.Gamma_mul_Gamma_add_half,
      ofReal_sqrt_pi_eq_cpow_half]
    ring_nf
  _ = 2 * ((2 : ℝ) ^ (-s) * π ^ (-s)) * Gamma s := by
    rw [sub_eq_add_neg, cpow_add _ _ two_ne_zero, cpow_one,
      ← cpow_add _ _ (ofReal_ne_zero.mpr pi_ne_zero), ofReal_ofNat]
    ring_nf
  _ = 2 * (2 * π) ^ (-s) * Gamma s := by
    rw [← mul_cpow_ofReal_nonneg two_pos.le pi_pos.le, ofReal_ofNat]

/-- The duplication formula for the entire reciprocal completed Gamma factors. -/
lemma reciprocalGammaℝ_mul_reciprocalGammaℝ_add_one (s : ℂ) :
    reciprocalGammaℝ s * reciprocalGammaℝ (s + 1) = reciprocalGammaℂ s := by
  have hp : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr pi_ne_zero
  have hsq : (↑(√π) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr pi_pos)
  calc
    _ = π ^ (s + 1 / 2) *
        (reciprocalGamma (s / 2) * reciprocalGamma (s / 2 + 1 / 2)) := by
      simp only [reciprocalGammaℝ]
      rw [show (s + 1) / 2 = s / 2 + 1 / 2 by ring]
      rw [mul_mul_mul_comm, ← cpow_add _ _ hp]
      congr 2
      ring
    _ = π ^ (s + 1 / 2) * (reciprocalGamma s * (2 : ℂ) ^ (s - 1) / ↑(√π)) := by
      rw [reciprocalGamma_mul_reciprocalGamma_add_half]
      congr 2
      ring_nf
    _ = π ^ s * (2 : ℂ) ^ s * reciprocalGamma s / 2 := by
      have hpow : (2 : ℂ) ^ (s - 1) * 2 = (2 : ℂ) ^ s := by
        calc
          _ = (2 : ℂ) ^ (s - 1) * (2 : ℂ) ^ (1 : ℂ) := by rw [cpow_one]
          _ = _ := by rw [← cpow_add _ _ two_ne_zero, sub_add_cancel]
      rw [← mul_div_assoc₀, div_eq_div_iff, cpow_add _ _ hp, ofReal_sqrt_pi_eq_cpow_half]
      calc
        _ = (π ^ s * π ^ (1 / 2 : ℂ)) * reciprocalGamma s * ((2 : ℂ) ^ (s - 1) * 2) := by ring
        _ = _ := by rw [hpow]; ring
    _ = reciprocalGammaℂ s := by
      have hpow : (π : ℂ) ^ s * (2 : ℂ) ^ s = (2 * π) ^ s := by
        rw [mul_comm, ← ofReal_ofNat 2, ← mul_cpow_ofReal_nonneg two_pos.le pi_pos.le]
      rw [hpow, reciprocalGammaℂ]

/-- The reflection formula for the entire reciprocal completed Gamma factor. -/
lemma reciprocalGammaℝ_one_sub_mul_reciprocalGammaℝ_one_add (s : ℂ) :
    reciprocalGammaℝ (1 - s) * reciprocalGammaℝ (1 + s) = cos (π * s / 2) := by
  have hp : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr pi_ne_zero
  calc
    _ = π ^ (1 : ℂ) *
        (reciprocalGamma ((1 - s) / 2) * reciprocalGamma (1 - (1 - s) / 2)) := by
      simp only [reciprocalGammaℝ]
      rw [mul_mul_mul_comm, ← cpow_add _ _ hp]
      congr 2 <;> ring
    _ = π * (sin (π * ((1 - s) / 2)) / π) := by
      rw [cpow_one, reciprocalGamma_mul_reciprocalGamma_one_sub]
    _ = cos (π * s / 2) := by
      rw [mul_div_cancel₀, show π * ((1 - s) / 2) = π / 2 - π * s / 2 by ring,
        sin_pi_div_two_sub]

/-- Reformulation of the reflection formula in terms of `Gammaℝ`, away from its poles. -/
lemma Gammaℝ_one_sub_mul_Gammaℝ_one_add (s : ℂ) (hs : cos (π * s / 2) ≠ 0) :
    Gammaℝ (1 - s) * Gammaℝ (1 + s) = (cos (π * s / 2))⁻¹ := by
  have hreflect := reciprocalGammaℝ_one_sub_mul_reciprocalGammaℝ_one_add s
  have hreg {t : ℂ} (ht : reciprocalGammaℝ t ≠ 0) (n : ℕ) : t ≠ -(2 * n) :=
    fun hn ↦ ht (reciprocalGammaℝ_eq_zero_iff.mpr ⟨n, hn⟩)
  have hprod : reciprocalGammaℝ (1 - s) * reciprocalGammaℝ (1 + s) ≠ 0 := by
    rwa [hreflect]
  obtain ⟨h₁, h₂⟩ := mul_ne_zero_iff.mp hprod
  apply eq_inv_of_mul_eq_one_left₀
  rw [← hreflect, mul_mul_mul_comm, mul_comm (Gammaℝ (1 - s)),
    reciprocalGammaℝ_mul_Gammaℝ (hreg h₁), mul_comm (Gammaℝ (1 + s)),
    reciprocalGammaℝ_mul_Gammaℝ (hreg h₂), one_mul]

/-- Formulation of reflection formula tailored to functional equations of L-functions of even
Dirichlet characters (including Riemann zeta). -/
lemma reciprocalGammaℝ_one_sub {s : ℂ} (hs : ∀ (n : ℕ), s ≠ -n) :
    reciprocalGammaℝ (1 - s) = Gammaℂ s * cos (π * s / 2) * reciprocalGammaℝ s := by
  calc
    _ = Gammaℂ s * (reciprocalGammaℂ s * reciprocalGammaℝ (1 - s)) := by
      rw [← mul_assoc, mul_comm (Gammaℂ s), reciprocalGammaℂ_mul_Gammaℂ hs, one_mul]
    _ = Gammaℂ s *
        (reciprocalGammaℝ s * (reciprocalGammaℝ (1 - s) * reciprocalGammaℝ (1 + s))) := by
      rw [← reciprocalGammaℝ_mul_reciprocalGammaℝ_add_one]
      ring_nf
    _ = _ := by rw [reciprocalGammaℝ_one_sub_mul_reciprocalGammaℝ_one_add]; ring

/-- The quotient form of the reflection identity, on the domain of both Gamma factors. -/
lemma Gammaℝ_div_Gammaℝ_one_sub {s : ℂ} (hs : ∀ n : ℕ, s ≠ -n)
    (hsub : ∀ n : ℕ, 1 - s ≠ -(2 * n)) :
    Checked.div (Gammaℝ s) (Gammaℝ (1 - s))
      (Gammaℝ_ne_zero hsub).isUnit =
      Gammaℂ s * cos (π * s / 2) := by
  have heven : ∀ n : ℕ, s ≠ -(2 * n) := by
    intro n
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hs (2 * n)
  rw [div_eq_mul_inv₀, ← reciprocalGammaℝ_eq_inv hsub, reciprocalGammaℝ_one_sub hs]
  calc
    _ = (Gammaℂ s * cos (π * s / 2)) * (reciprocalGammaℝ s * Gammaℝ s) := by ring
    _ = _ := by rw [reciprocalGammaℝ_mul_Gammaℝ heven, mul_one]

/-- Formulation of reflection formula tailored to functional equations of L-functions of odd
Dirichlet characters. -/
lemma reciprocalGammaℝ_two_sub {s : ℂ} (hs : ∀ (n : ℕ), s ≠ -n) :
    reciprocalGammaℝ (2 - s) = Gammaℂ s * sin (π * s / 2) * reciprocalGammaℝ (s + 1) := by
  have hreflect : reciprocalGammaℝ (2 - s) * reciprocalGammaℝ s = sin (π * s / 2) := by
    convert reciprocalGammaℝ_one_sub_mul_reciprocalGammaℝ_one_add (s - 1) using 1
    · congr 2 <;> ring
    · rw [show π * (s - 1) / 2 = π * s / 2 - π / 2 by ring, cos_sub_pi_div_two]
  calc
    _ = Gammaℂ s * (reciprocalGammaℂ s * reciprocalGammaℝ (2 - s)) := by
      rw [← mul_assoc, mul_comm (Gammaℂ s), reciprocalGammaℂ_mul_Gammaℂ hs, one_mul]
    _ = Gammaℂ s *
        ((reciprocalGammaℝ (2 - s) * reciprocalGammaℝ s) * reciprocalGammaℝ (s + 1)) := by
      rw [← reciprocalGammaℝ_mul_reciprocalGammaℝ_add_one]
      ring
    _ = _ := by rw [hreflect]; ring

end reflection

end Complex
