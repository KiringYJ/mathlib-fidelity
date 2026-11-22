/-
Copyright (c) 2021 David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Renshaw
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Ring

/-!
# IMO 2013 Q1

Prove that for any pair of positive integers k and n, there exist k positive integers
m₁, m₂, ..., mₖ (not necessarily different) such that

  1 + (2ᵏ - 1)/ n = (1 + 1/m₁) * (1 + 1/m₂) * ... * (1 + 1/mₖ).

## Solution

Adaptation of the solution found in https://www.imo-official.org/problems/IMO2013SL.pdf

We prove a slightly more general version where k does not need to be strictly positive.
-/

public section

namespace Imo2013Q1

theorem arith_lemma (k n : ℕ) : 0 < 2 * n + 2 ^ k.succ := by positivity

theorem prod_lemma (m : ℕ → ℕ+) (k : ℕ) (nm : ℕ+) :
    ∏ i ∈ Finset.range k, ((1 : ℚ) + 1 / ↑(if i < k then m i else nm)) =
      ∏ i ∈ Finset.range k, (1 + 1 / (m i : ℚ)) := by
  refine Finset.prod_congr rfl fun i hi ↦ ?_
  simp only [ite_eq_left (Finset.mem_range.1 hi)]

private theorem step_eq (n s d : ℕ+) {a b : ℚ}
    (h : ((n : ℚ) + a) * (s : ℚ) * (d : ℚ) =
      ((s : ℚ) + b) * ((d : ℚ) + 1) * (n : ℚ)) :
    1 + a / (n : ℚ) = (1 + b / (s : ℚ)) * (1 + 1 / (d : ℚ)) := by
  suffices h' : (1 + a / (n : ℚ)) * (n : ℚ) * (s : ℚ) * (d : ℚ) =
      ((1 + b / (s : ℚ)) * (1 + 1 / (d : ℚ))) * (n : ℚ) * (s : ℚ) * (d : ℚ) by
    simpa only [mul_div_cancel_right₀] using
      congrArg (fun z : ℚ => z / (d : ℚ) / (s : ℚ) / (n : ℚ)) h'
  calc
    _ = ((1 + b / (s : ℚ)) * (s : ℚ)) * ((1 + 1 / (d : ℚ)) * (d : ℚ)) * (n : ℚ) := by
      simpa only [add_mul, one_mul, div_mul_cancel₀] using h
    _ = _ := by ac_rfl

end Imo2013Q1

open Imo2013Q1

set_option backward.isDefEq.respectTransparency.types false in
theorem imo2013_q1 (n : ℕ+) (k : ℕ) :
    ∃ m : ℕ → ℕ+, 1 + ((2 : ℚ) ^ k - 1) / (n : ℚ) =
      ∏ i ∈ Finset.range k, (1 + 1 / (m i : ℚ)) := by
  induction k generalizing n with
  | zero => use fun (_ : ℕ) => (1 : ℕ+); simp -- For the base case, any m works.
  | succ pk hpk =>
  obtain ⟨t, ht : ↑n = t + t⟩ | ⟨t, ht : ↑n = 2 * t + 1⟩ := (n : ℕ).even_or_odd
  · -- even case
    rw [← two_mul] at ht
    -- Eliminate the zero case to simplify later calculations.
    obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero <| by
      rintro (rfl : t = 0)
      rw [Nat.mul_zero] at ht; exact PNat.ne_zero n ht
    -- Now we have ht : ↑n = 2 * (t + 1).
    let t_succ : ℕ+ := ⟨t + 1, t.succ_pos⟩
    obtain ⟨pm, hpm⟩ := hpk t_succ
    let m i := if i < pk then pm i else ⟨2 * t + 2 ^ pk.succ, arith_lemma pk t⟩
    use m
    have hmpk : (m pk : ℚ) = 2 * t + 2 ^ pk.succ := by
      have : m pk = ⟨2 * t + 2 ^ pk.succ, _⟩ := ite_eq_right (irrefl pk); simp [this]
    rw [Finset.prod_range_succ, prod_lemma, ← hpm]
    apply step_eq n t_succ (m pk)
    have hnq : (n : ℚ) = 2 * ((t : ℚ) + 1) := by exact_mod_cast ht
    have hsq : (t_succ : ℚ) = (t : ℚ) + 1 := by simp [t_succ, PNat.mk_coe]
    simp only [hnq, hsq, hmpk, pow_succ']
    ring
  · -- odd case
    let t_succ : ℕ+ := ⟨t + 1, t.succ_pos⟩
    obtain ⟨pm, hpm⟩ := hpk t_succ
    let m i := if i < pk then pm i else ⟨2 * t + 1, Nat.succ_pos _⟩
    use m
    have hmpk : (m pk : ℚ) = 2 * t + 1 := by
      have : m pk = ⟨2 * t + 1, _⟩ := ite_eq_right (irrefl pk)
      simp [this]
    rw [Finset.prod_range_succ, prod_lemma, ← hpm]
    apply step_eq n t_succ (m pk)
    have hnq : (n : ℚ) = 2 * (t : ℚ) + 1 := by exact_mod_cast ht
    have hsq : (t_succ : ℚ) = (t : ℚ) + 1 := by simp [t_succ, PNat.mk_coe]
    simp only [hnq, hsq, hmpk, pow_succ']
    ring
