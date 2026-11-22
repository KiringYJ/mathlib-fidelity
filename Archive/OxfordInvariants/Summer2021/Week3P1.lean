/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Nat.Cast.Field
public import Mathlib.Data.Nat.Cast.Order.Field
public import Mathlib.Tactic.Positivity

/-!
# The Oxford Invariants Puzzle Challenges - Summer 2021, Week 3, Problem 1

## Original statement

Let `n ≥ 3`, `a₁, ..., aₙ` be strictly positive integers such that `aᵢ ∣ aᵢ₋₁ + aᵢ₊₁` for
`i = 2, ..., n - 1`. Show that $\sum_{i=1}^{n-1}\dfrac{a_0a_n}{a_ia_{i+1}} ∈ \mathbb N$.

## Comments

Mathlib is based on type theory, so saying that a rational is a natural doesn't make sense. Instead,
we ask that there exists `b : ℕ` whose cast to `α` is the sum we want.

In mathlib, `ℕ` starts at `0`. To make the indexing cleaner, we use `a₀, ..., aₙ₋₁` instead of
`a₁, ..., aₙ`. Similarly, it's nicer to not use subtraction of naturals, so we replace
`aᵢ ∣ aᵢ₋₁ + aᵢ₊₁` by `aᵢ₊₁ ∣ aᵢ + aᵢ₊₂`.

We don't actually have to work in `ℚ` or `ℝ`. We can be even more general by stating the result for
any linearly ordered field.

Instead of having `n` naturals, we use a function `a : ℕ → ℕ`.

In the proof itself, we replace `n : ℕ, 1 ≤ n` by `n + 1`.

The statement is actually true for `n = 0, 1` (`n = 1, 2` before the reindexing) as the sum is
simply `0` and `1` respectively. So the version we prove is slightly more general.

Overall, the indexing is a bit of a mess to understand. But, trust Lean, it works.

## Formalised statement

Let `n : ℕ`, `a : ℕ → ℕ`, `∀ i ≤ n, 0 < a i`, `∀ i, i + 2 ≤ n → aᵢ₊₁ ∣ aᵢ + aᵢ₊₂` (read `→` as
"implies"). Then there exists `b : ℕ` such that `b` as an element of any linearly ordered field
equals $\sum_{i=0}^{n-1} (a_0 a_n) / (a_i a_{i+1})$.

## Proof outline

The case `n = 0` is trivial.

For `n + 1`, we prove the result by induction but by adding `aₙ₊₁ ∣ aₙ * b - a₀` to the induction
hypothesis, where `b` is the previous sum, $\sum_{i=0}^{n-1} (a_0 a_n) / (a_i a_{i+1})$, as a
natural.
* Base case:
  * $\sum_{i=0}^0 (a_0 a_{0+1}) / (a_0 a_{0+1})$ is a natural:
    $\sum_{i=0}^0 (a_0 a_{0+1}) / (a_0 a_{0+1}) = (a_0 a_1) / (a_0 a_1) = 1$.
  * Divisibility condition:
    `a₀ * 1 - a₀ = 0` is clearly divisible by `a₁`.
* Induction step:
  * $\sum_{i=0}^n (a_0 a_{n+1}) / (a_i a_{i+1})$ is a natural:
    $$\sum_{i=0}^{n+1} (a_0 a_{n+2}) / (a_i a_{i+1})
      = \sum_{i=0}^n\ (a_0 a_{n+2}) / (a_i a_{i+1}) + (a_0 a_{n+2}) / (a_{n+1} a_{n+2})
      = a_{n+2} / a_{n+1} × \sum_{i=0}^n (a_0 a_{n+1}) / (a_i a_{i+1}) + a_0 / a_{n+1}
      = a_{n+2} / a_{n+1} × b + a_0 / a_{n+1}
      = (a_n + a_{n+2}) / a_{n+1} × b - (a_n b - a_0)(a_{n+1})$$
    which is a natural because `(aₙ + aₙ₊₂)/aₙ₊₁`, `b` and `(aₙ * b - a₀)/aₙ₊₁` are (plus an
    annoying inequality, or the fact that the original sum is positive because its terms are).
  * Divisibility condition:
    `aₙ₊₁ * ((aₙ + aₙ₊₂)/aₙ₊₁ * b - (aₙ * b - a₀)/aₙ₊₁) - a₀ = aₙ₊₁aₙ₊₂b` is divisible by `aₙ₊₂`.
-/

public section

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

private noncomputable def week3Summand (a : ℕ → ℕ) {n : ℕ} (a_pos : ∀ i ≤ n, 0 < a i)
    (i : Fin n) : α :=
  Checked.div ((a 0 : α) * a n) ((a i : α) * a (i + 1))
    ((Nat.cast_ne_zero.mpr (a_pos i i.isLt.le).ne').isUnit.mul
      (Nat.cast_ne_zero.mpr (a_pos (i + 1) (Nat.succ_le_of_lt i.isLt)).ne').isUnit)

theorem OxfordInvariants.Week3P1 (n : ℕ) (a : ℕ → ℕ) (a_pos : ∀ i ≤ n, 0 < a i)
    (ha : ∀ i, i + 2 ≤ n → a (i + 1) ∣ a i + a (i + 2)) :
    ∃ b : ℕ, (b : α) = ∑ i : Fin n,
      Checked.div ((a 0 : α) * a n) ((a i : α) * a (i + 1))
        ((Nat.cast_ne_zero.mpr (a_pos i i.isLt.le).ne').isUnit.mul
          (Nat.cast_ne_zero.mpr (a_pos (i + 1) (Nat.succ_le_of_lt i.isLt)).ne').isUnit) := by
  change ∃ b : ℕ, (b : α) = ∑ i : Fin n, week3Summand a a_pos i
  rcases n with - | n
  · exact ⟨0, by simp⟩
  rsuffices ⟨b, hb, -⟩ :
    ∃ b : ℕ,
      (b : α) = ∑ i : Fin (n + 1), week3Summand a a_pos i ∧
        a (n + 1) ∣ a n * b - a 0
  · exact ⟨b, hb⟩
  induction n with
  | zero =>
    exact ⟨1, by simp [week3Summand], by simp⟩
  | succ n ih =>
    have a_prev (i : ℕ) (hi : i ≤ n + 1) : 0 < a i :=
      a_pos i (Nat.le_succ_of_le hi)
    obtain ⟨b, hb, han⟩ := ih (a_pos := a_prev) (ha := fun i hi ↦ ha i (Nat.le_succ_of_le hi))
    have hdiv : a (n + 1) ∣ a n + a (n + 2) := ha n le_rfl
    have hmid : (a (n + 1) : α) ≠ 0 := Nat.cast_ne_zero.mpr (a_prev _ le_rfl).ne'
    have hn : (0 : α) < a n := Nat.cast_pos.mpr (a_prev _ (Nat.le_succ _))
    have ha₀ : a 0 ≤ a n * b := by
      suffices h : (a 0 : α) ≤ (a n : α) * (b : α) by exact_mod_cast h
      apply (div_le_iff₀' hn).mp
      have hlast : (a 0 : α) / (a n : α) = week3Summand a a_prev (Fin.last n) := by
        exact (mul_div_mul_right _ _).symm
      rw [hlast, hb]
      exact Finset.single_le_sum
        (fun i _ ↦ div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
          (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))) (Finset.mem_univ (Fin.last n))
    have hden : a (n + 1) ≠ 0 := (a_prev _ le_rfl).ne'
    let q := Nat.euclideanDiv (a n + a (n + 2)) (a (n + 1)) hden
    let r := Nat.euclideanDiv (a n * b - a 0) (a (n + 1)) hden
    have hq : a (n + 1) * q = a n + a (n + 2) := by
      simpa only [q, Nat.mod_eq_zero_of_dvd hdiv, Nat.add_zero] using
        Nat.euclideanDiv_mul_add_mod (a n + a (n + 2)) (a (n + 1)) hden
    have hr : a (n + 1) * r = a n * b - a 0 := by
      simpa only [r, Nat.mod_eq_zero_of_dvd han, Nat.add_zero] using
        Nat.euclideanDiv_mul_add_mod (a n * b - a 0) (a (n + 1)) hden
    refine ⟨q * b - r, ?_, ?_⟩
    · calc
        ((q * b - r : ℕ) : α) =
            ((a n : α) + a (n + 2)) / (a (n + 1) : α) * b -
              (a n * (b : α) - a 0) / (a (n + 1) : α) := by
          have hle : r ≤ q * b := by
            change Nat.euclideanDiv (a n * b - a 0) (a (n + 1)) hden ≤ q * b
            rw [Nat.euclideanDiv_eq_core]
            apply Nat.div_le_of_le_mul
            rw [← mul_assoc, hq, add_mul]
            exact tsub_le_self.trans (Nat.le_add_right _ _)
          rw [Nat.cast_sub hle, Nat.cast_mul]
          dsimp only [q, r]
          rw [Nat.cast_div hdiv hmid, Nat.cast_div han hmid,
            Nat.cast_add, Nat.cast_sub ha₀, Nat.cast_mul]
        _ = (a (n + 2) : α) / (a (n + 1) : α) * b + (a 0 : α) / (a (n + 1) : α) := by
          rw [add_div, add_mul, sub_div, mul_div_right_comm₀, add_sub_sub_cancel]
        _ = ∑ i : Fin (n + 2), week3Summand a a_pos i := by
          rw [Fin.sum_univ_castSucc, hb, Finset.mul_sum]
          congr 1
          · apply Finset.sum_congr rfl
            intro i _
            simp only [week3Summand, Fin.val_castSucc]
            rw [← mul_div_assoc₀, ← mul_div_right_comm₀, ← mul_assoc, mul_div_cancel_right₀,
              mul_comm (a (n + 2) : α) (a 0 : α)]
          · exact (mul_div_mul_right _ _).symm
    · rw [Nat.mul_sub, ← mul_assoc, hq, add_mul, hr,
        add_tsub_tsub_cancel ha₀, add_tsub_cancel_right]
      exact dvd_mul_right _ _
