/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Alexey Soloyev, Junyan Xu, Kamila Szewczyk
-/
module

public import Mathlib.Algebra.EuclideanDomain.Basic
public import Mathlib.Algebra.LinearRecurrence
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Int.Fib.Basic
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.Prime

/-!
# The golden ratio and its conjugate

This file defines the golden ratio `φ := (1 + √5)/2` and its conjugate
`ψ := (1 - √5)/2`, which are the two real roots of `X² - X - 1`.

Along with various computational facts about them, we prove their
irrationality, and we link them to the Fibonacci sequence by proving
Binet's formula.
-/

@[expose] public section


noncomputable section

open Polynomial

namespace Real

/-- The golden ratio `φ := (1 + √5)/2`. -/
abbrev goldenRatio : ℝ := (1 + √5) / 2

/-- The conjugate of the golden ratio `ψ := (1 - √5)/2`. -/
abbrev goldenConj : ℝ := (1 - √5) / 2

@[inherit_doc] scoped[goldenRatio] notation "φ" => Real.goldenRatio
@[inherit_doc] scoped[goldenRatio] notation "ψ" => Real.goldenConj

open scoped goldenRatio

/-- The inverse of the golden ratio is the opposite of its conjugate. -/
theorem inv_goldenRatio : φ⁻¹ = -ψ := by
  refine inv_eq_of_mul_eq_one_right₀ ?_
  calc φ * -ψ = (√5 ^ 2 - 1) / 4 := by ring
    _ = 1 := by rw [sq_sqrt (by norm_num)]; norm_num

@[simp]
theorem goldenRatio_mul_goldenConj : φ * ψ = -1 := by
  calc φ * ψ = (1 - √5 ^ 2) / 4 := by ring
    _ = -1 := by rw [sq_sqrt (by norm_num)]; norm_num

@[simp]
theorem goldenConj_mul_goldenRatio : ψ * φ = -1 := by
  rw [mul_comm]
  exact goldenRatio_mul_goldenConj

@[simp]
theorem goldenRatio_add_goldenConj : φ + ψ = 1 := by
  rw [goldenRatio, goldenConj]
  ring

theorem one_sub_goldenConj : 1 - φ = ψ := by
  linarith [goldenRatio_add_goldenConj]

theorem one_sub_goldenRatio : 1 - ψ = φ := by
  linarith [goldenRatio_add_goldenConj]

@[simp]
theorem goldenRatio_sub_goldenConj : φ - ψ = √5 := by ring

@[simp 1200]
theorem goldenRatio_sq : φ ^ 2 = φ + 1 := by
  calc φ ^ 2 = (1 + 2 * √5 + √5 ^ 2) / 4 := by ring
    _ = φ + 1 := by rw [sq_sqrt (by norm_num)]; ring

@[simp 1200]
theorem goldenConj_sq : ψ ^ 2 = ψ + 1 := by
  calc ψ ^ 2 = (1 - 2 * √5 + √5 ^ 2) / 4 := by ring
    _ = ψ + 1 := by rw [sq_sqrt (by norm_num)]; ring

theorem goldenRatio_pow_sub_goldenRatio_pow (n : ℕ) : φ ^ (n + 2) - φ ^ (n + 1) = φ ^ n := by
  calc φ ^ (n + 2) - φ ^ (n + 1) = φ ^ n * (φ ^ 2 - φ) := by ring
    _ = φ ^ n := by rw [goldenRatio_sq]; ring

theorem goldenRatio_pos : 0 < φ :=
  mul_pos (by apply add_pos <;> norm_num) <| inv_pos.2 zero_lt_two

theorem goldenRatio_ne_zero : φ ≠ 0 :=
  ne_of_gt goldenRatio_pos

theorem one_lt_goldenRatio : 1 < φ := by
  refine lt_of_mul_lt_mul_left ?_ (le_of_lt goldenRatio_pos)
  simp [← sq, zero_lt_one]

theorem goldenRatio_lt_two : φ < 2 := by calc
  (1 + √5) / 2 < (1 + 3) / 2 := by gcongr; rw [sqrt_lt'] <;> norm_num
  _ = 2 := by norm_num

theorem goldenConj_neg : ψ < 0 := by
  linarith [one_sub_goldenConj, one_lt_goldenRatio]

theorem goldenConj_ne_zero : ψ ≠ 0 :=
  ne_of_lt goldenConj_neg

/-! The rule below extends `checked_nonzero`: the conjugate of the golden ratio is nonzero, so
`ψ⁻¹`, `x / ψ` and `ψ ^ n` with `n : ℤ` find their evidence. -/

macro_rules | `(tactic| checked_nonzero) => `(tactic|
    solve
    | assumption
    | exact Real.goldenConj_ne_zero)

/-- The opposite of the golden ratio is the inverse of its conjugate. -/
theorem inv_goldenConj : ψ⁻¹ = -φ := by
  refine inv_eq_of_mul_eq_one_right₀ ?_
  rw [mul_neg, goldenConj_mul_goldenRatio, neg_neg]

theorem neg_one_lt_goldenConj : -1 < ψ := by
  rw [neg_lt, ← inv_goldenRatio]
  exact inv_lt_one_of_one_lt₀ one_lt_goldenRatio

/-!
## Irrationality
-/


/-- The golden ratio is irrational. -/
theorem goldenRatio_irrational : Irrational φ := by
  have := Nat.Prime.irrational_sqrt (show Nat.Prime 5 by norm_num)
  have := (this.ratCast_add 1).div_natCast two_ne_zero
  convert! this using 1
  norm_num

/-- The conjugate of the golden ratio is irrational. -/
theorem goldenConj_irrational : Irrational ψ := by
  have := Nat.Prime.irrational_sqrt (show Nat.Prime 5 by norm_num)
  have := (this.ratCast_sub 1).div_natCast two_ne_zero
  convert! this using 1
  norm_num

/-!
## Links with Fibonacci sequence
-/

section Fibrec

variable {α : Type*} [CommSemiring α]

/-- The recurrence relation satisfied by the Fibonacci sequence. -/
def fibRec : LinearRecurrence α where
  order := 2
  coeffs := ![1, 1]

section Poly

open Polynomial

/-- The characteristic polynomial of `fibRec` is `X² - (X + 1)`. -/
theorem fibRec_charPoly_eq {β : Type*} [CommRing β] :
    fibRec.charPoly = X ^ 2 - (X + (1 : β[X])) := by
  rw [fibRec, LinearRecurrence.charPoly]
  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ', ← smul_X_eq_monomial]

end Poly

/-- As expected, the Fibonacci sequence is a solution of `fibRec`. -/
theorem fib_isSol_fibRec : fibRec.IsSolution (fun x => x.fib : ℕ → α) := by
  rw [fibRec]
  intro n
  simp only
  rw [Nat.fib_add_two, add_comm]
  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ']

/-- The geometric sequence `fun n ↦ φ^n` is a solution of `fibRec`. -/
theorem geom_goldenRatio_isSol_fibRec : fibRec.IsSolution (φ ^ ·) := by
  rw [fibRec.geom_sol_iff_root_charPoly, fibRec_charPoly_eq]
  simp

/-- The geometric sequence `fun n ↦ ψ^n` is a solution of `fibRec`. -/
theorem geom_goldenConj_isSol_fibRec : fibRec.IsSolution (ψ ^ ·) := by
  rw [fibRec.geom_sol_iff_root_charPoly, fibRec_charPoly_eq]
  simp

end Fibrec

/-- Binet's formula as a function equality. -/
theorem coe_fib_eq' :
    (fun n => Nat.fib n : ℕ → ℝ) = fun n => (φ ^ n - ψ ^ n) / √5 := by
  rw [fibRec.eq_iff_eqOn_range_order]
  · intro i hi
    norm_cast at hi
    fin_cases hi <;> simp
  · exact fib_isSol_fibRec
  · suffices LinearRecurrence.IsSolution fibRec
        ((fun n ↦ (√5)⁻¹ * φ ^ n) - (fun n ↦ (√5)⁻¹ * ψ ^ n)) by
      convert! this
      rw [Pi.sub_apply]
      ring
    apply (@fibRec ℝ _).solSpace.sub_mem
    · exact Submodule.smul_mem fibRec.solSpace (√5)⁻¹ geom_goldenRatio_isSol_fibRec
    · exact Submodule.smul_mem fibRec.solSpace (√5)⁻¹ geom_goldenConj_isSol_fibRec

/-- **Binet's formula** as a dependent equality. -/
theorem coe_fib_eq : ∀ n, (Nat.fib n : ℝ) = (φ ^ n - ψ ^ n) / √5 := by
  rw [← funext_iff, Real.coe_fib_eq']

/-- **Binet's formula** for integer values. -/
theorem coe_intFib_eq (n : ℤ) : (Int.fib n : ℝ) = (φ ^ n - ψ ^ n) / √5 := by
  obtain ⟨n, (rfl | rfl)⟩ := n.eq_nat_or_neg
  · exact coe_fib_eq n
  · have hφ : φ ^ (-(n : ℤ)) = (-ψ) ^ n := by
      rw [zpow_neg₀ goldenRatio_ne_zero]
      refine inv_eq_of_mul_eq_one_right₀ ?_
      rw [zpow_natCast₀, ← mul_pow, mul_neg, goldenRatio_mul_goldenConj, neg_neg, one_pow]
    have hψ : ψ ^ (-(n : ℤ)) = (-φ) ^ n := by
      rw [zpow_neg₀ goldenConj_ne_zero]
      refine inv_eq_of_mul_eq_one_right₀ ?_
      rw [zpow_natCast₀, ← mul_pow, mul_neg, goldenConj_mul_goldenRatio, neg_neg, one_pow]
    rw [hφ, hψ, Int.fib_neg_natCast]
    push_cast
    rw [coe_fib_eq, neg_pow ψ, neg_pow φ]
    ring

/-- Relationship between the Fibonacci Sequence, the golden ratio, and its conjugate's exponents. -/
theorem fib_succ_sub_goldenRatio_mul_fib (n : ℕ) : Nat.fib (n + 1) - φ * Nat.fib n = ψ ^ n := by
  rw [coe_fib_eq, coe_fib_eq, mul_div₀, div_sub_div_same, div_eq_iff,
    ← goldenRatio_sub_goldenConj]
  ring

/-- Relationship between the Fibonacci Sequence, the conjugate of the golden ratio,
and its exponents. -/
lemma goldenConj_mul_fib_succ_add_fib (n : ℕ) : ψ * Nat.fib (n + 1) + Nat.fib n = ψ ^ (n + 1) := by
  rw [show ψ * (Nat.fib (n + 1) : ℝ) + Nat.fib n =
      ψ * (Nat.fib (n + 1) - φ * Nat.fib n) + (φ * ψ + 1) * Nat.fib n by ring,
    fib_succ_sub_goldenRatio_mul_fib, goldenRatio_mul_goldenConj]
  ring

/-- Relationship between the Fibonacci Sequence, the golden ratio, and its exponents. -/
lemma goldenRatio_mul_fib_succ_add_fib (n : ℕ) : φ * Nat.fib (n + 1) + Nat.fib n = φ ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      _ = φ * (Nat.fib n) + φ ^ 2 * (Nat.fib (n + 1)) := by
        simp only [Nat.fib_add_one (Nat.succ_ne_zero n), Nat.succ_sub_succ_eq_sub,
          Nat.cast_add, goldenRatio_sq, Nat.sub_zero]; ring
      _ = φ * ((Nat.fib n) + φ * (Nat.fib (n + 1))) := by ring
      _ = φ ^ (n + 2) := by rw [add_comm, ih]; ring

/-- Relationship between the Fibonacci Sequence, exponents of the golden ratio,
and its conjugate. -/
theorem fib_succ_sub_goldenConj_mul_fib (n : ℕ) : Nat.fib (n + 1) - ψ * Nat.fib n = φ ^ n := by
  apply mul_left_cancel₀ goldenRatio_ne_zero
  rw [show φ * ((Nat.fib (n + 1) : ℝ) - ψ * Nat.fib n) =
      φ * Nat.fib (n + 1) + Nat.fib n - (φ * ψ + 1) * Nat.fib n by ring,
    goldenRatio_mul_fib_succ_add_fib, goldenRatio_mul_goldenConj]
  ring

end Real
