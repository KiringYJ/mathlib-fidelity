/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Analytic.ConvergenceRadius
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Representation of `FormalMultilinearSeries.radius` as a `liminf`

In this file we prove that the radius of convergence of a `FormalMultilinearSeries` is equal to
$\liminf_{n\to\infty} \frac{1}{\sqrt[n]{‖p n‖}}$. This lemma can't go to `Analysis.Analytic.Basic`
because this would create a circular dependency once we redefine `exp` using
`FormalMultilinearSeries`.
-/

public section


variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

open scoped Topology NNReal ENNReal

open Filter Asymptotics

namespace FormalMultilinearSeries

variable (p : FormalMultilinearSeries 𝕜 E F)

/-- The radius of a formal multilinear series is equal to
$\liminf_{n\to\infty} \frac{1}{\sqrt[n]{‖p n‖}}$, indexed by positive degrees. The reciprocal
is taken in `ℝ≥0∞`, so a zero coefficient contributes `∞`. -/
theorem radius_eq_liminf :
    p.radius = liminf
      (fun n : {n : ℕ // n ≠ 0} ↦ ((‖p (n : ℕ)‖₊ : ℝ≥0∞) ^ (1 / ((n : ℕ) : ℝ)))⁻¹)
      (comap Subtype.val atTop) := by
  have hroot (r : ℝ≥0) (n : {n : ℕ // n ≠ 0}) :
      ((r : ℝ≥0∞) ≤ ((‖p (n : ℕ)‖₊ : ℝ≥0∞) ^ (1 / ((n : ℕ) : ℝ)))⁻¹ ↔
        ‖p (n : ℕ)‖₊ * r ^ (n : ℕ) ≤ 1) := by
    have hn : 0 < ((n : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.pos_iff_ne_zero.mpr n.2)
    conv_lhs =>
      rw [← ENNReal.coe_rpow_of_nonneg _ (one_div_nonneg.mpr hn.le),
        ENNReal.le_inv_iff_mul_le, ← ENNReal.coe_mul, ENNReal.coe_le_one_iff, one_div₀, ←
        NNReal.rpow_one r, ← mul_inv_cancel₀ (ha := hn.ne'.isUnit), NNReal.rpow_mul,
        ← NNReal.mul_rpow, ← NNReal.one_rpow (((n : ℕ) : ℝ)⁻¹),
        NNReal.rpow_le_rpow_iff (inv_pos.mpr hn), mul_comm,
        NNReal.rpow_natCast]
  apply le_antisymm <;> refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
  · have := ((TFAE_exists_lt_isLittleO_pow (fun n => ‖p n‖ * r ^ n) 1).out 2 8).1
      (p.isLittleO_of_lt_radius hr)
    obtain ⟨a, ha, H⟩ := this
    apply le_liminf_of_le
    · infer_param
    · change ∀ᶠ n : {n : ℕ // n ≠ 0} in comap Subtype.val atTop,
        (r : ℝ≥0∞) ≤ ((‖p (n : ℕ)‖₊ : ℝ≥0∞) ^ (1 / ((n : ℕ) : ℝ)))⁻¹
      filter_upwards [tendsto_comap.eventually H] with n hn
      apply (hroot r n).2 (NNReal.coe_le_coe.mp ?_)
      push_cast
      exact (le_abs_self _).trans (hn.trans (pow_le_one₀ ha.1.le ha.2.le))
  · refine p.le_radius_of_isBigO <| .of_norm_eventuallyLE ?_
    apply (eventually_comap_val_iff (eventually_ne_atTop 0)).mp
    filter_upwards [eventually_lt_of_lt_liminf hr] with n hn
    simpa using NNReal.coe_le_coe.mpr ((hroot r n).mp hn.le)

/-- The **Cauchy-Hadamard theorem** for formal multilinear series: The inverse of the radius
is equal to $\limsup_{n\to\infty} \sqrt[n]{‖p n‖}$. -/
theorem radius_inv_eq_limsup :
    p.radius⁻¹ = limsup
      (fun n : {n : ℕ // n ≠ 0} ↦ (‖p (n : ℕ)‖₊ : ℝ≥0∞) ^ (1 / ((n : ℕ) : ℝ)))
      (comap Subtype.val atTop) := by
  simpa [ENNReal.inv_liminf] using congr($(p.radius_eq_liminf)⁻¹)

end FormalMultilinearSeries
