/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Complex.Periodic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Exp

/-! # The q-parameter on the upper half-plane -/

public section

open Real Complex UpperHalfPlane Function

local notation "𝕢" => @Periodic.qParam

theorem Function.Periodic.im_invQParam_pos_of_norm_lt_one
    {h : ℝ} (hh : 0 < h) {q : ℂ} (hq : ‖q‖ < 1) (hq_ne : q ≠ 0) :
    0 < im (Periodic.invQParam h q hh.ne' hq_ne) :=
  im_invQParam h q hh.ne' hq_ne ▸ mul_pos_of_neg_of_neg
    (div_neg_of_neg_of_pos (neg_lt_zero.mpr hh) Real.two_pi_pos)
    ((Real.log_neg_iff (norm_pos_iff.mpr hq_ne)).mpr hq)

lemma Function.Periodic.norm_qParam_le_of_one_half_le_im {ξ : ℂ} (hξ : 1 / 2 ≤ ξ.im) :
    ‖𝕢 1 ξ one_ne_zero‖ ≤ rexp (-π) := by
  rw [Periodic.norm_qParam 1 ξ one_ne_zero, Real.exp_le_exp, div_one₀]
  linarith [mul_le_mul_of_nonneg_left hξ Real.two_pi_pos.le]

theorem UpperHalfPlane.norm_qParam_lt_one (n : ℕ) [NeZero n] (τ : ℍ) :
    ‖𝕢 n τ (Nat.cast_ne_zero.mpr (NeZero.ne n))‖ < 1 :=
  Periodic.norm_qParam_lt_one (Nat.cast_pos.mpr (NeZero.pos n)) τ.im_pos
