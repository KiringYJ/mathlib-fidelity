/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Order.Filter.AtTopBot.Archimedean
public import Mathlib.Order.Filter.AtTopBot.Finite
public import Mathlib.Order.Filter.AtTopBot.Prod
public import Mathlib.Topology.Algebra.Ring.Real

/-!
# Convergence of subadditive sequences

A subadditive sequence `u : ℕ → ℝ` is a sequence satisfying `u (m + n) ≤ u m + u n` for all `m, n`.
We define this notion as `Subadditive u`, and prove in `Subadditive.tendsto_lim` that, if `u n / n`
is bounded below, then it converges to a limit (that we denote by `Subadditive.lim` for
convenience). This result is known as Fekete's lemma in the literature.

The quotient `u n / n` is defined for `n ≥ 1`; as a sequence it is indexed by `n + 1`, as
`u (n + 1) / (n + 1)`.

## TODO

Define a bundled `SubadditiveHom`, use it.
-/

@[expose] public section

noncomputable section

open Set Filter

open scoped Topology

/-- A real-valued sequence is subadditive if it satisfies the inequality `u (m + n) ≤ u m + u n`
for all `m, n`. -/
def Subadditive (u : ℕ → ℝ) : Prop :=
  ∀ m n, u (m + n) ≤ u m + u n

namespace Subadditive

variable {u : ℕ → ℝ} (h : Subadditive u)

/-- The limit of a bounded-below subadditive sequence: the infimum of the quotients `u n / n`
over `n ≥ 1`. The fact that the sequence indeed tends to this limit is given in
`Subadditive.tendsto_lim` -/
@[nolint unusedArguments, irreducible]
protected def lim (_h : Subadditive u) :=
  sInf (range fun n : ℕ => u (n + 1) / (n + 1 : ℕ))

theorem lim_le_div (hbdd : BddBelow (range fun n : ℕ => u (n + 1) / (n + 1 : ℕ))) {n : ℕ}
    (hn : n ≠ 0) : h.lim ≤ u n / n := by
  rw [Subadditive.lim]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn
  exact csInf_le hbdd ⟨m, rfl⟩

include h in
theorem apply_mul_add_le (k n r) : u (k * n + r) ≤ k * u n + u r := by
  induction k with
  | zero => simp only [Nat.cast_zero, zero_mul, zero_add]; rfl
  | succ k IH =>
    calc
      u ((k + 1) * n + r) = u (n + (k * n + r)) := by congr 1; ring
      _ ≤ u n + u (k * n + r) := h _ _
      _ ≤ u n + (k * u n + u r) := by grw [IH]
      _ = (k + 1 : ℕ) * u n + u r := by simp; ring

include h in
theorem eventually_div_lt_of_div_lt {L : ℝ} {n : ℕ} (hn : n ≠ 0) (hL : u n / n < L) :
    ∀ᶠ p in atTop, u (p + 1) / (p + 1 : ℕ) < L := by
  /- It suffices to prove the statement for each arithmetic progression `(n * · + r)`. -/
  refine .atTop_of_arithmetic hn fun r _ => ?_
  /- Since `u n < L * n`, we have `k * u n + u (r + 1) < L * (k * n + r + 1)` for sufficiently
  large `k`. -/
  have hlt : u n - L * n < 0 := by
    rw [div_lt_iff₀ (Nat.cast_pos.2 (Nat.pos_of_ne_zero hn))] at hL
    linarith
  refine ((tendsto_natCast_atTop_atTop.atTop_mul_const_of_neg' hlt).eventually_lt_atBot
    (L * (r + 1) - u (r + 1))).mono fun k hk => ?_
  /- Finally, we use the upper estimate `u (k * n + (r + 1)) ≤ k * u n + u (r + 1)`. -/
  rw [div_lt_iff₀ (Nat.cast_pos.2 (Nat.succ_pos _))]
  calc
    u (n * k + r + 1) = u (k * n + (r + 1)) := by rw [mul_comm, add_assoc]
    _ ≤ k * u n + u (r + 1) := h.apply_mul_add_le k n (r + 1)
    _ < L * (n * k + r + 1 : ℕ) := by push_cast; linarith

/-- Fekete's lemma: a subadditive sequence `u` such that `u n / n` is bounded below satisfies
`u n / n → Subadditive.lim h`. -/
theorem tendsto_lim (hbdd : BddBelow (range fun n : ℕ => u (n + 1) / (n + 1 : ℕ))) :
    Tendsto (fun n : ℕ => u (n + 1) / (n + 1 : ℕ)) atTop (𝓝 h.lim) := by
  refine tendsto_order.2 ⟨fun l hl => ?_, fun L hL => ?_⟩
  · exact .of_forall fun n => hl.trans_le (h.lim_le_div hbdd n.add_one_ne_zero)
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, u (n + 1) / (n + 1 : ℕ) < L := by
      rw [Subadditive.lim] at hL
      rcases exists_lt_of_csInf_lt (range_nonempty _) hL with ⟨x, ⟨n, rfl⟩, xL⟩
      exact ⟨n, xL⟩
    exact h.eventually_div_lt_of_div_lt n.add_one_ne_zero hn

end Subadditive
