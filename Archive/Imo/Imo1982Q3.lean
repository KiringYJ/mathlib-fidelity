/-
Copyright (c) 2024 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Alex Brodbelt
-/
module

public import Mathlib.Algebra.Order.Field.GeomSum
public import Mathlib.Basic.NNReal.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset -- for `Finset.sq_sum_div_le_sum_sq_div`
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# IMO 1982 Q3

Consider infinite sequences $\{x_n\}$ of positive reals such that $x_0 = 1$ and
$x_0 \ge x_1 \ge x_2 \ge \ldots$

a) Prove that for every such sequence there is an $n \ge 1$ such that:

$$\frac{x_0^2}{x_1} + \ldots + \frac{x_{n-1}^2}{x_n} \ge 3.999$$

b) Find such a sequence such that for all $n$:

$$\frac{x_0^2}{x_1} + \ldots + \frac{x_{n-1}^2}{x_n} < 4$$

The solution is based on Solution 1 from the
[Art of Problem Solving](https://artofproblemsolving.com/wiki/index.php/1982_IMO_Problems/Problem_3)
website. For part a, we use Sedrakyan's lemma to show the sum is bounded below by
$\frac{4n}{n + 1}$, which can be made arbitrarily close to $4$ by taking large $n$. For part b,
the partial sum for $x_n = 2^{-n}$ is less than $4$ by exactly $4 \cdot 2^{-n}$.
-/

@[expose] public section

open Finset NNReal

variable {x : ℕ → ℝ} {n : ℕ} (hn : n ≠ 0) (hx : Antitone x)

namespace Imo1982Q3
include hn hx

/-- `x n` is at most the average of all previous terms in the sequence.

This is expressed here with `∑ k ∈ range n, x k` added to both sides. -/
lemma le_avg : ∑ k ∈ range (n + 1), x k ≤ (∑ k ∈ range n, x k) * (1 + 1 / n) := by
  rw [sum_range_succ, mul_one_add, add_le_add_iff_left, mul_one_div₀,
    le_div_iff₀ (mod_cast hn.bot_lt), mul_comm, ← nsmul_eq_mul]
  conv_lhs => rw [← card_range n, ← sum_const]
  gcongr with i hi
  refine hx <| le_of_lt ?_
  simpa using hi

/-- The main inequality used for part a. -/
lemma ineq (h0 : x 0 = 1) (hp : ∀ k, 0 < x k) :
    4 * n / (n + 1) ≤ ∑ k ∈ range (n + 1),
      Checked.div (x k ^ 2) (x (k + 1)) (hp (k + 1)).ne'.isUnit := by
  let s := ∑ k ∈ range n, x (k + 1)
  let t := ∑ k ∈ range (n + 1), x (k + 1)
  let u := ∑ k ∈ range (n + 1), x k
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have ht : 0 < t := sum_pos (fun k _ ↦ hp (k + 1)) nonempty_range_add_one
  have hnt : t * n ≤ s * (n + 1) := by
    have havg : t ≤ s * (1 + 1 / n) := le_avg hn (hx.comp_monotone @Nat.succ_le_succ)
    have h := mul_le_mul_of_nonneg_right havg hn'.le
    rwa [mul_assoc, add_mul, one_mul, div_mul_cancel₀] at h
  have hu : u = s + 1 := by
    change (∑ k ∈ range (n + 1), x k) = s + 1
    rw [sum_range_succ', h0]
  have hs : 4 * s ≤ u ^ 2 := by simpa only [hu, mul_one] using four_mul_le_sq_add s 1
  calc
    _ ≤ Checked.div (u ^ 2) t ht.ne'.isUnit := by
      apply (div_le_div_iff₀ (add_pos hn' zero_lt_one) ht).2
      calc
        _ = 4 * (t * (n : ℝ)) := by ring
        _ ≤ 4 * (s * (n + 1)) := mul_le_mul_of_nonneg_left hnt (by norm_num)
        _ = (4 * s) * (n + 1) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hs (add_pos hn' zero_lt_one).le
    _ ≤ _ := by
      rw [← sum_coe_sort (range (n + 1))
        (fun k ↦ Checked.div (x k ^ 2) (x (k + 1)) (hp (k + 1)).ne'.isUnit)]
      exact sq_sum_div_le_sum_sq_div (range (n + 1)) x (hgs := ht.ne'.isUnit) (fun k _ ↦ hp (k + 1))

end Imo1982Q3

/-- Part a of the problem is solved by `n = 4000`. -/
theorem imo1982_q3a (hx : Antitone x) (h0 : x 0 = 1) (hp : ∀ k, 0 < x k) :
    ∃ n : ℕ, 3.999 ≤ ∑ k ∈ range n,
      Checked.div (x k ^ 2) (x (k + 1)) (hp (k + 1)).ne'.isUnit := by
  use 4000
  convert! Imo1982Q3.ineq (Nat.succ_ne_zero 3998) hx h0 hp
  norm_num

/-- Part b of the problem is solved by `x k = (1 / 2) ^ k`. -/
theorem imo1982_q3b : ∃ x : ℕ → ℝ, Antitone x ∧ x 0 = 1 ∧
    ∃ hp : ∀ k, 0 < x k, ∀ n, (∑ k ∈ range n,
      Checked.div (x k ^ 2) (x (k + 1)) (hp (k + 1)).ne'.isUnit) < 4 := by
  let r : ℝ := 1 / 2
  have hr : 0 < r := by norm_num [r]
  have hr₂ : 2 * r = 1 := by norm_num [r]
  have hp (k : ℕ) : 0 < r ^ k := pow_pos hr _
  refine ⟨fun k ↦ r ^ k, (pow_right_strictAnti₀ hr (by norm_num [r])).antitone, pow_zero _, hp, ?_⟩
  intro n
  have term (k : ℕ) : (r ^ k) ^ 2 / r ^ (k + 1) = 2 * r ^ k := by
    apply (mul_left_inj' (hp (k + 1)).ne').mp
    rw [div_mul_cancel₀, pow_succ r k]
    calc
      _ = (r ^ k) ^ 2 * (2 * r) := by rw [hr₂, mul_one]
      _ = _ := by ring
  have hsum : (∑ k ∈ range n, 2 * r ^ k) + 4 * r ^ n = 4 := by
    rw [← mul_sum]
    have he := congrArg (fun z : ℝ ↦ z * ∑ k ∈ range n, r ^ k) hr₂
    nlinarith only [geom_sum_mul r n, he]
  simp only [term]
  linarith only [hsum, hp n]
