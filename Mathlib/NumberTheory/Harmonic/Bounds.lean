/-
Copyright (c) 2024 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.NumberTheory.Harmonic.Defs

/-!

This file proves $\log(n + 1) \le H_n \le 1 + \log(n)$ for all natural numbers $n$.

-/

public section

lemma harmonic_eq_sum_Icc {n : ℕ} :
    harmonic n = ∑ i ∈ (Finset.Icc 1 n).attach,
      Checked.inv (i.val : ℚ) ((Nat.cast_ne_zero.mpr
        (Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.mp i.property).1)).isUnit) := by
  unfold harmonic
  refine Finset.sum_bij
    (fun i hi ↦ (⟨i + 1, Finset.mem_Icc.mpr
      ⟨Nat.succ_pos i, Nat.succ_le_of_lt (Finset.mem_range.mp hi)⟩⟩ :
        {j : ℕ // j ∈ Finset.Icc 1 n})) ?_ ?_ ?_ ?_
  · intro i hi
    simp
  · intro i hi j hj hij
    exact Nat.succ.inj (congrArg Subtype.val hij)
  · intro j hj
    obtain ⟨hj₁, hj₂⟩ := Finset.mem_Icc.mp j.property
    refine ⟨j.val - 1, Finset.mem_range.mpr (by omega), Subtype.ext ?_⟩
    change j.val - 1 + 1 = j.val
    omega
  · intro i hi
    rfl

private lemma cast_harmonic_succ (n : ℕ) :
    (harmonic (n + 1) : ℝ) = harmonic n + ((n : ℝ) + 1)⁻¹ := by
  simp [Rat.cast_inv, Nat.cast_add]

private lemma log_add_one_sub_log_bounds {x : ℝ} (hx : 0 < x) :
    (x + 1)⁻¹ ≤ Real.log (x + 1) - Real.log x ∧
    Real.log (x + 1) - Real.log x ≤ x⁻¹ := by
  have hx' : 0 < x + 1 := by positivity
  have hquot := div_pos hx' hx
  have hupper := Real.log_le_sub_one_of_pos hquot
  have hlower := Real.one_sub_inv_le_log_of_pos hquot
  have h₁ : (x + 1) / x - 1 = x⁻¹ := by
    apply mul_right_cancel₀ hx.ne'
    rw [sub_mul, div_mul_cancel₀, inv_mul_cancel₀, one_mul, add_sub_cancel_left]
  have h₂ : 1 - x / (x + 1) = (x + 1)⁻¹ := by
    apply mul_right_cancel₀ hx'.ne'
    rw [sub_mul, div_mul_cancel₀, inv_mul_cancel₀, one_mul, add_sub_cancel_left]
  rw [Real.log_div hx'.ne', h₁] at hupper
  rw [Real.log_div hx'.ne', inv_div₀, h₂] at hlower
  exact ⟨hlower, hupper⟩

theorem log_add_one_le_harmonic (n : ℕ) :
    Real.log ↑(n + 1) ≤ harmonic n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [cast_harmonic_succ]
    push_cast at ih ⊢
    have h := (log_add_one_sub_log_bounds (show 0 < (n : ℝ) + 1 by positivity)).2
    linarith

theorem harmonic_le_one_add_log (n : ℕ) :
    harmonic n ≤ 1 + Real.log n := by
  induction n with
  | zero => simp
  | succ n ih =>
    by_cases hn : n = 0
    · subst n
      norm_num [harmonic]
    · rw [cast_harmonic_succ]
      push_cast
      have h := (log_add_one_sub_log_bounds (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))).1
      linarith

theorem log_le_harmonic_floor (y : ℝ) (hy : 0 ≤ y) :
    Real.log y ≤ harmonic ⌊y⌋₊ := by
  by_cases h0 : y = 0
  · simp [h0]
  · calc
      _ ≤ Real.log ↑(Nat.floor y + 1) := ?_
      _ ≤ _ := log_add_one_le_harmonic _
    gcongr
    apply (Nat.le_ceil y).trans
    norm_cast
    exact Nat.ceil_le_floor_add_one y

theorem harmonic_floor_le_one_add_log (y : ℝ) (hy : 1 ≤ y) :
    harmonic ⌊y⌋₊ ≤ 1 + Real.log y := by
  refine (harmonic_le_one_add_log _).trans ?_
  gcongr
  · exact_mod_cast Nat.floor_pos.mpr hy
  · exact Nat.floor_le <| zero_le_one.trans hy
