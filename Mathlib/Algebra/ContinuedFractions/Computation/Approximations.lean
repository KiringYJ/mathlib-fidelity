/-
Copyright (c) 2020 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
module

public import Mathlib.Algebra.ContinuedFractions.Determinant
public import Mathlib.Algebra.ContinuedFractions.Computation.CorrectnessTerminating
public import Mathlib.Algebra.Order.Ring.Basic
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Tactic.Monotonicity
public import Mathlib.Tactic.GCongr

/-!
# Approximations for Continued Fraction Computations (`GenContFract.of`)

## Summary

This file contains useful approximations for the values involved in the continued fractions
computation `GenContFract.of`. In particular, we show that the generalized continued fraction given
by `GenContFract.of` in fact is a (regular) continued fraction.

Moreover, we derive some upper bounds for the error term when computing a continued fraction up a
given position, i.e. bounds for the term
`|v - (GenContFract.of v).convs n|`. The derived bounds will show us that the error term indeed gets
smaller. As a corollary, we will be able to show that `(GenContFract.of v).convs` converges to `v`
in `Algebra.ContinuedFractions.Computation.ApproximationCorollaries`.

## Main Theorems

- `GenContFract.of_partNum_eq_one`: shows that all partial numerators `aᵢ` are
  equal to one.
- `GenContFract.exists_int_eq_of_partDen`: shows that all partial denominators
  `bᵢ` correspond to an integer.
- `GenContFract.of_one_le_get?_partDen`: shows that `1 ≤ bᵢ`.
- `ContFract.of` returns the regular continued fraction of a value.
- `GenContFract.succ_nth_fib_le_of_nthDen`: shows that the `n`th denominator
  `Bₙ` is greater than or equal to the `n + 1`th fibonacci number `Nat.fib (n + 1)`.
- `GenContFract.le_of_succ_get?_den`: shows that `bₙ * Bₙ ≤ Bₙ₊₁`, where `bₙ` is
  the `n`th partial denominator of the continued fraction.
- `GenContFract.abs_sub_convs_le`: shows that
  `|v - Aₙ / Bₙ| ≤ 1 / (Bₙ * Bₙ₊₁)`, where `Aₙ` is the `n`th partial numerator.

## References

- [*Hardy, GH and Wright, EM and Heath-Brown, Roger and Silverman, Joseph*][hardy2008introduction]

-/

@[expose] public section

open GenContFract

open GenContFract (of)

open Int

variable {K : Type*} {v : K} {n : ℕ} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

namespace GenContFract

namespace IntFractPair

/-!
We begin with some lemmas about the stream of `IntFractPair`s, which presumably are not
of great interest for the end user.
-/


/-- Shows that the fractional parts of the stream are in `[0,1)`. -/
theorem nth_stream_fr_nonneg_lt_one {ifp_n : IntFractPair K}
    (nth_stream_eq : IntFractPair.stream v n = some ifp_n) : 0 ≤ ifp_n.fr ∧ ifp_n.fr < 1 := by
  cases n with
  | zero =>
    obtain rfl : IntFractPair.of v = ifp_n := by injection nth_stream_eq
    exact ⟨fract_nonneg _, fract_lt_one _⟩
  | succ =>
    rcases succ_nth_stream_eq_some_iff.1 nth_stream_eq with ⟨_, _, _, rfl⟩
    exact ⟨fract_nonneg _, fract_lt_one _⟩

/-- Shows that the fractional parts of the stream are nonnegative. -/
theorem nth_stream_fr_nonneg {ifp_n : IntFractPair K}
    (nth_stream_eq : IntFractPair.stream v n = some ifp_n) : 0 ≤ ifp_n.fr :=
  (nth_stream_fr_nonneg_lt_one nth_stream_eq).left

/-- Shows that the fractional parts of the stream are smaller than one. -/
theorem nth_stream_fr_lt_one {ifp_n : IntFractPair K}
    (nth_stream_eq : IntFractPair.stream v n = some ifp_n) : ifp_n.fr < 1 :=
  (nth_stream_fr_nonneg_lt_one nth_stream_eq).right

/-- Shows that the integer parts of the stream are at least one. -/
theorem one_le_succ_nth_stream_b {ifp_succ_n : IntFractPair K}
    (succ_nth_stream_eq : IntFractPair.stream v (n + 1) = some ifp_succ_n) : 1 ≤ ifp_succ_n.b := by
  obtain ⟨ifp_n, nth_stream_eq, stream_nth_fr_ne_zero, ⟨-⟩⟩ :=
    succ_nth_stream_eq_some_iff.1 succ_nth_stream_eq
  rw [IntFractPair.of, le_floor, cast_one, one_le_inv₀
    ((nth_stream_fr_nonneg nth_stream_eq).lt_of_ne' stream_nth_fr_ne_zero)]
  exact (nth_stream_fr_lt_one nth_stream_eq).le

omit [IsStrictOrderedRing K] in
/--
Shows that the `n + 1`th integer part `bₙ₊₁` of the stream is smaller or equal than the inverse of
the `n`th fractional part `frₙ` of the stream, which is nonzero since the stream continues.
This result is straight-forward as `bₙ₊₁` is defined as the floor of `1 / frₙ`.
-/
theorem succ_nth_stream_b_le_nth_stream_fr_inv {ifp_n ifp_succ_n : IntFractPair K}
    (nth_stream_eq : IntFractPair.stream v n = some ifp_n)
    (succ_nth_stream_eq : IntFractPair.stream v (n + 1) = some ifp_succ_n) :
    (ifp_succ_n.b : K) ≤ Checked.inv ifp_n.fr
      (fr_ne_zero_of_succ_stream_eq_some nth_stream_eq succ_nth_stream_eq).isUnit := by
  obtain ⟨ifp_n', nth_stream_eq', hfr, rfl⟩ := succ_nth_stream_eq_some_iff.mp succ_nth_stream_eq
  obtain rfl : ifp_n = ifp_n' := by injection nth_stream_eq.symm.trans nth_stream_eq'
  exact floor_le ifp_n.fr⁻¹

end IntFractPair

/-!
Next we translate above results about the stream of `IntFractPair`s to the computed continued
fraction `GenContFract.of`.
-/


/-- Shows that the integer parts of the continued fraction are at least one. -/
theorem of_one_le_get?_partDen {b : K}
    (nth_partDen_eq : (of v).partDens.get? n = some b) : 1 ≤ b := by
  obtain ⟨gp_n, nth_s_eq, ⟨-⟩⟩ : ∃ gp_n, (of v).s.get? n = some gp_n ∧ gp_n.b = b :=
    exists_s_b_of_partDen nth_partDen_eq
  obtain ⟨ifp_n, succ_nth_stream_eq, ifp_n_b_eq_gp_n_b⟩ :
      ∃ ifp, IntFractPair.stream v (n + 1) = some ifp ∧ (ifp.b : K) = gp_n.b :=
    IntFractPair.exists_succ_get?_stream_of_gcf_of_get?_eq_some nth_s_eq
  rw [← ifp_n_b_eq_gp_n_b]
  exact mod_cast IntFractPair.one_le_succ_nth_stream_b succ_nth_stream_eq

omit [IsStrictOrderedRing K] in
/--
Shows that the partial numerators `aᵢ` of the continued fraction are equal to one and the partial
denominators `bᵢ` correspond to integers.
-/
theorem of_partNum_eq_one_and_exists_int_partDen_eq {gp : GenContFract.Pair K}
    (nth_s_eq : (of v).s.get? n = some gp) : gp.a = 1 ∧ ∃ z : ℤ, gp.b = (z : K) := by
  obtain ⟨ifp, stream_succ_nth_eq, -⟩ : ∃ ifp, IntFractPair.stream v (n + 1) = some ifp ∧ _ :=
    IntFractPair.exists_succ_get?_stream_of_gcf_of_get?_eq_some nth_s_eq
  have : gp = ⟨1, ifp.b⟩ := by
    have : (of v).s.get? n = some ⟨1, ifp.b⟩ :=
      get?_of_eq_some_of_succ_get?_intFractPair_stream stream_succ_nth_eq
    have : some gp = some ⟨1, ifp.b⟩ := by rwa [nth_s_eq] at this
    injection this
  simp [this]

omit [IsStrictOrderedRing K] in
/-- Shows that the partial numerators `aᵢ` are equal to one. -/
theorem of_partNum_eq_one {a : K} (nth_partNum_eq : (of v).partNums.get? n = some a) :
    a = 1 := by
  obtain ⟨gp, nth_s_eq, gp_a_eq_a_n⟩ : ∃ gp, (of v).s.get? n = some gp ∧ gp.a = a :=
    exists_s_a_of_partNum nth_partNum_eq
  have : gp.a = 1 := (of_partNum_eq_one_and_exists_int_partDen_eq nth_s_eq).left
  rwa [gp_a_eq_a_n] at this

omit [IsStrictOrderedRing K] in
/-- Shows that the partial denominators `bᵢ` correspond to an integer. -/
theorem exists_int_eq_of_partDen {b : K}
    (nth_partDen_eq : (of v).partDens.get? n = some b) : ∃ z : ℤ, b = (z : K) := by
  obtain ⟨_, nth_s_eq, rfl⟩ : ∃ gp, (of v).s.get? n = some gp ∧ gp.b = b :=
    exists_s_b_of_partDen nth_partDen_eq
  exact (of_partNum_eq_one_and_exists_int_partDen_eq nth_s_eq).right

end GenContFract

variable (v)

omit [IsStrictOrderedRing K] in
theorem GenContFract.of_isSimpContFract :
    (of v).IsSimpContFract := fun _ _ nth_partNum_eq =>
  of_partNum_eq_one nth_partNum_eq

/-- Creates the simple continued fraction of a value. -/
noncomputable def SimpContFract.of : SimpContFract K :=
  ⟨GenContFract.of v, GenContFract.of_isSimpContFract v⟩

theorem SimpContFract.of_isContFract :
    (SimpContFract.of v).IsContFract := fun _ _ nth_partDen_eq =>
  lt_of_lt_of_le zero_lt_one (of_one_le_get?_partDen nth_partDen_eq)

/-- Creates the continued fraction of a value. -/
noncomputable def ContFract.of : ContFract K :=
  ⟨SimpContFract.of v, SimpContFract.of_isContFract v⟩

variable {v}

namespace GenContFract

/-!
One of our next goals is to show that `bₙ * Bₙ ≤ Bₙ₊₁`. For this, we first show that the partial
denominators `Bₙ` are bounded from below by the fibonacci sequence `Nat.fib`. This then implies that
`0 ≤ Bₙ` and hence `Bₙ₊₂ = bₙ₊₁ * Bₙ₊₁ + Bₙ ≥ bₙ₊₁ * Bₙ₊₁ + 0 = bₙ₊₁ * Bₙ₊₁`.
-/


-- open `Nat` as we will make use of fibonacci numbers.
open Nat

theorem fib_le_of_contsAux_b :
    n ≤ 1 ∨ ¬(of v).TerminatedAt (n - 2) → (fib n : K) ≤ ((of v).contsAux n).b :=
  Nat.strong_induction_on n
    (by
      intro n IH hyp
      rcases n with (_ | _ | n)
      · simp [contsAux] -- case n = 0
      · simp -- case n = 1
      · let g := of v -- case 2 ≤ n
        have : ¬n + 2 ≤ 1 := by lia
        have not_terminatedAt_n : ¬g.TerminatedAt n := Or.resolve_left hyp this
        obtain ⟨gp, s_ppred_nth_eq⟩ : ∃ gp, g.s.get? n = some gp :=
          Option.ne_none_iff_exists'.mp not_terminatedAt_n
        set pconts := g.contsAux (n + 1) with pconts_eq
        set ppconts := g.contsAux n with ppconts_eq
        -- use the recurrence of `contsAux`
        simp only [Nat.add_assoc, Nat.reduceAdd]
        suffices (fib n : K) + fib (n + 1) ≤ gp.a * ppconts.b + gp.b * pconts.b by
          simpa [g, fib_add_two, add_comm, contsAux_recurrence s_ppred_nth_eq ppconts_eq pconts_eq]
        -- make use of the fact that `gp.a = 1`
        suffices (fib n : K) + fib (n + 1) ≤ ppconts.b + gp.b * pconts.b by
          simpa [of_partNum_eq_one <| partNum_eq_s_a s_ppred_nth_eq]
        have not_terminatedAt_pred_n : ¬g.TerminatedAt (n - 1) :=
          mt (terminated_stable <| Nat.sub_le n 1) not_terminatedAt_n
        have not_terminatedAt_ppred_n : ¬TerminatedAt g (n - 2) :=
          mt (terminated_stable <| Nat.sub_le n 2) not_terminatedAt_n
        -- use the IH to get the inequalities for `pconts` and `ppconts`
        have ppred_nth_fib_le_ppconts_B : (fib n : K) ≤ ppconts.b :=
          IH n (lt_trans (Nat.lt_add_one n) <| Nat.lt_add_one <| n + 1)
            (Or.inr not_terminatedAt_ppred_n)
        suffices (fib (n + 1) : K) ≤ gp.b * pconts.b by gcongr
        -- finally use the fact that `1 ≤ gp.b` to solve the goal
        suffices 1 * (fib (n + 1) : K) ≤ gp.b * pconts.b by rwa [one_mul] at this
        have one_le_gp_b : (1 : K) ≤ gp.b :=
          of_one_le_get?_partDen (partDen_eq_s_b s_ppred_nth_eq)
        gcongr
        grind)

/-- Shows that the `n`th denominator is greater than or equal to the `n + 1`th fibonacci number,
that is `Nat.fib (n + 1) ≤ Bₙ`. -/
theorem succ_nth_fib_le_of_nth_den (hyp : n = 0 ∨ ¬(of v).TerminatedAt (n - 1)) :
    (fib (n + 1) : K) ≤ (of v).dens n := by
  rw [den_eq_conts_b, nth_cont_eq_succ_nth_contAux]
  have : n + 1 ≤ 1 ∨ ¬(of v).TerminatedAt (n - 1) := by
    cases n with
    | zero => exact Or.inl <| le_refl 1
    | succ n => exact Or.inr (Or.resolve_left hyp n.succ_ne_zero)
  exact fib_le_of_contsAux_b this

/-! As a simple consequence, we can now derive that all denominators are nonnegative. -/


theorem zero_le_of_contsAux_b : 0 ≤ ((of v).contsAux n).b := by
  let g := of v
  induction n with
  | zero => rfl
  | succ n IH =>
    rcases Decidable.em <| g.TerminatedAt (n - 1) with terminated | not_terminated
    · -- terminating case
      rcases n with - | n
      · simp
      · have : g.contsAux (n + 2) = g.contsAux (n + 1) :=
          contsAux_stable_step_of_terminated terminated
        simp only [g, this, IH]
    · -- non-terminating case
      calc
        (0 : K) ≤ fib (n + 1) := mod_cast (n + 1).fib.zero_le
        _ ≤ ((of v).contsAux (n + 1)).b := fib_le_of_contsAux_b (Or.inr not_terminated)

/-- Shows that all denominators are nonnegative. -/
theorem zero_le_of_den : 0 ≤ (of v).dens n := by
  rw [den_eq_conts_b, nth_cont_eq_succ_nth_contAux]; exact zero_le_of_contsAux_b

theorem le_of_succ_succ_get?_contsAux_b {b : K}
    (nth_partDen_eq : (of v).partDens.get? n = some b) :
    b * ((of v).contsAux <| n + 1).b ≤ ((of v).contsAux <| n + 2).b := by
  obtain ⟨gp_n, nth_s_eq, rfl⟩ : ∃ gp_n, (of v).s.get? n = some gp_n ∧ gp_n.b = b :=
    exists_s_b_of_partDen nth_partDen_eq
  simp [of_partNum_eq_one (partNum_eq_s_a nth_s_eq), zero_le_of_contsAux_b,
    GenContFract.contsAux_recurrence nth_s_eq rfl rfl]

/-- Shows that `bₙ * Bₙ ≤ Bₙ₊₁`, where `bₙ` is the `n`th partial denominator and `Bₙ₊₁` and `Bₙ` are
the `n + 1`th and `n`th denominator of the continued fraction. -/
theorem le_of_succ_get?_den {b : K}
    (nth_partDenom_eq : (of v).partDens.get? n = some b) :
    b * (of v).dens n ≤ (of v).dens (n + 1) := by
  rw [den_eq_conts_b, nth_cont_eq_succ_nth_contAux]
  exact le_of_succ_succ_get?_contsAux_b nth_partDenom_eq

/-- Shows that the sequence of denominators is monotone, that is `Bₙ ≤ Bₙ₊₁`. -/
theorem of_den_mono : (of v).dens n ≤ (of v).dens (n + 1) := by
  let g := of v
  rcases Decidable.em <| g.partDens.TerminatedAt n with terminated | not_terminated
  · have : g.TerminatedAt n :=
      terminatedAt_iff_partDen_none.2 (by rwa [Stream'.Seq.TerminatedAt] at terminated)
    have : g.dens (n + 1) = g.dens n :=
      dens_stable_of_terminated n.le_succ this
    rw [this]
  · obtain ⟨b, nth_partDen_eq⟩ : ∃ b, g.partDens.get? n = some b :=
      Option.ne_none_iff_exists'.mp not_terminated
    have : 1 ≤ b := of_one_le_get?_partDen nth_partDen_eq
    calc
      g.dens n ≤ b * g.dens n := by
        simpa using mul_le_mul_of_nonneg_right this zero_le_of_den
      _ ≤ g.dens (n + 1) := le_of_succ_get?_den nth_partDen_eq

/-- Shows that all denominators are positive. -/
theorem zero_lt_of_den : 0 < (of v).dens n := by
  induction n with
  | zero => simp
  | succ n ih => exact ih.trans_le of_den_mono

/-- The denominators of `GenContFract.of v` are positive: the convergents of `GenContFract.of v`
and quotients by its denominators find their evidence. -/
macro_rules | `(tactic| checked_nonzero) => `(tactic|
    solve
    | assumption
    | exact (GenContFract.zero_lt_of_den).ne')

section ErrorTerm

/-!
### Approximation of Error Term

Next we derive some approximations for the error term when computing a continued fraction up a given
position, i.e. bounds for the term `|v - (GenContFract.of v).convs n|`.
-/


/-- This lemma follows from the finite correctness proof, the determinant equality, and
by simplifying the difference. The quotient on the right is taken where the fractional part is
nonzero; its denominator is then positive. -/
theorem sub_convs_eq {ifp : IntFractPair K}
    (stream_nth_eq : IntFractPair.stream v n = some ifp) :
    let g := of v
    let B := (g.contsAux (n + 1)).b
    let pB := (g.contsAux n).b
    v - g.convs n = if h : ifp.fr = 0 then 0 else
      Checked.div ((-1) ^ n) (B * (ifp.fr⁻¹ * B + pB)) (mul_pos zero_lt_of_den
        (add_pos_of_pos_of_nonneg (mul_pos (inv_pos_of_pos
          ((IntFractPair.nth_stream_fr_nonneg stream_nth_eq).lt_of_ne' h)) zero_lt_of_den)
          zero_le_of_contsAux_b)).ne'.isUnit := by
  dsimp only
  have g_finite_correctness := (compExactValue_correctness_of_stream_eq_some stream_nth_eq).symm
  by_cases ifp_fr_eq_zero : ifp.fr = 0
  · rw [dite_eq_left ifp_fr_eq_zero, sub_eq_zero]
    rw [ifp_fr_eq_zero, compExactValue_eq_some_iff_of_eq_zero] at g_finite_correctness
    obtain ⟨_, h⟩ := g_finite_correctness
    exact h.symm
  · rw [dite_eq_right ifp_fr_eq_zero]
    obtain ⟨hD, hv⟩ :=
      (compExactValue_eq_some_iff_of_ne_zero ifp_fr_eq_zero).1 g_finite_correctness
    -- To continue, we need use the determinant equality. So let's derive the needed hypothesis.
    have n_eq_zero_or_not_terminatedAt_pred_n : n = 0 ∨ ¬(of v).TerminatedAt (n - 1) := by
      rcases n with - | n'
      · simp
      · have : IntFractPair.stream v (n' + 1) ≠ none := by simp [stream_nth_eq]
        have : ¬(of v).TerminatedAt n' :=
          (not_congr of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none).2 this
        exact Or.inr this
    have determinant_eq : ((of v).contsAux n).a * ((of v).contsAux (n + 1)).b -
        ((of v).contsAux n).b * ((of v).contsAux (n + 1)).a = (-1) ^ n := by
      match hn : n with
      | 0 => subst n; simp
      | n' + 1 =>
        subst n
        simp only [succ_ne_zero, false_or] at n_eq_zero_or_not_terminatedAt_pred_n
        rw [add_tsub_cancel_right] at n_eq_zero_or_not_terminatedAt_pred_n
        exact (SimpContFract.of v).determinant n_eq_zero_or_not_terminatedAt_pred_n
    -- the remaining computation, stated for arbitrary values of the continuants
    have key : ∀ (A B pA pB r : K) {hB : IsUnit B} {hD : IsUnit (r * B + pB)}
        {hBD : IsUnit (B * (r * B + pB))}, pA * B - pB * A = (-1) ^ n →
          (r * A + pA) / (r * B + pB) - A / B = (-1) ^ n / (B * (r * B + pB)) := by
      intro A B pA pB r _ _ _ det
      rw [div_sub_div, div_eq_div_iff, ← det]
      ring
    calc v - (of v).convs n
        = (nextConts 1 ifp.fr⁻¹ ((of v).contsAux n) ((of v).contsAux (n + 1))).a /
            (nextConts 1 ifp.fr⁻¹ ((of v).contsAux n) ((of v).contsAux (n + 1))).b -
          (of v).convs n := by rw [hv]
      _ = _ := by
        simp only [nextConts, nextNum, nextDen, one_mul, conv_eq_conts_a_div_conts_b,
          nth_cont_eq_succ_nth_contAux]
        exact key _ _ _ _ _ determinant_eq

/-- Shows that `|v - Aₙ / Bₙ| ≤ 1 / (Bₙ * Bₙ₊₁)`. -/
theorem abs_sub_convs_le (not_terminatedAt_n : ¬(of v).TerminatedAt n) :
    |v - (of v).convs n| ≤ 1 / ((of v).dens n * ((of v).dens <| n + 1)) := by
  obtain ⟨gp, s_nth_eq⟩ : ∃ gp, (of v).s.get? n = some gp :=
    Option.ne_none_iff_exists'.1 not_terminatedAt_n
  have gp_a_eq_one : gp.a = 1 := of_partNum_eq_one (partNum_eq_s_a s_nth_eq)
  obtain ⟨ifp_succ_n, succ_nth_stream_eq, ifp_succ_n_b_eq_gp_b⟩ :
      ∃ ifp_succ_n, IntFractPair.stream v (n + 1) = some ifp_succ_n ∧ (ifp_succ_n.b : K) = gp.b :=
    IntFractPair.exists_succ_get?_stream_of_gcf_of_get?_eq_some s_nth_eq
  obtain ⟨ifp_n, stream_nth_eq, stream_nth_fr_ne_zero, -⟩ :=
    IntFractPair.succ_nth_stream_eq_some_iff.1 succ_nth_stream_eq
  -- unfold the recurrence relation for the next denominator
  have next_den_eq : (of v).dens (n + 1) =
      ((of v).contsAux n).b + gp.b * ((of v).contsAux (n + 1)).b := by
    simp only [den_eq_conts_b, nth_cont_eq_succ_nth_contAux, contsAux_recurrence s_nth_eq rfl rfl,
      gp_a_eq_one, one_mul]
    exact add_comm _ _
  -- now we can use `sub_convs_eq` to simplify our goal
  have h_sub := sub_convs_eq stream_nth_eq
  dsimp only at h_sub
  rw [dite_eq_right stream_nth_fr_ne_zero] at h_sub
  rw [h_sub]
  refine (abs_div _ _).trans_le ?_
  simp only [abs_neg_one_pow]
  -- derive some tedious inequalities that we need to compare the denominators
  have zero_lt_B : 0 < ((of v).contsAux (n + 1)).b := zero_lt_of_den (n := n)
  have zero_le_pB : 0 ≤ ((of v).contsAux n).b := zero_le_of_contsAux_b
  have zero_lt_fr : 0 < ifp_n.fr :=
    (IntFractPair.nth_stream_fr_nonneg stream_nth_eq).lt_of_ne' stream_nth_fr_ne_zero
  have zero_lt_den' : 0 < ((of v).contsAux (n + 1)).b *
      (ifp_n.fr⁻¹ * ((of v).contsAux (n + 1)).b + ((of v).contsAux n).b) := by
    have := inv_pos_of_pos zero_lt_fr
    positivity
  simp only [abs_of_pos zero_lt_den']
  refine div_le_div_of_nonneg_left zero_le_one
    (mul_pos zero_lt_of_den zero_lt_of_den) ?_
  -- we can cancel multiplication by `Bₙ` and addition with `Bₙ₋₁`
  rw [next_den_eq, add_comm (ifp_n.fr⁻¹ * _)]
  change ((of v).contsAux (n + 1)).b * _ ≤ ((of v).contsAux (n + 1)).b * _
  gcongr
  rw [← ifp_succ_n_b_eq_gp_b]
  exact IntFractPair.succ_nth_stream_b_le_nth_stream_fr_inv stream_nth_eq succ_nth_stream_eq

/-- Shows that `|v - Aₙ / Bₙ| ≤ 1 / (bₙ * Bₙ * Bₙ)`. This bound is worse than the one shown in
`GenContFract.abs_sub_convs_le`, but sometimes it is easier to apply and
sufficient for one's use case. The partial denominator `bₙ` is positive.
-/
theorem abs_sub_convergents_le' {b : K}
    (nth_partDen_eq : (of v).partDens.get? n = some b) :
    |v - (of v).convs n| ≤ Checked.div 1 (b * (of v).dens n * (of v).dens n)
      (mul_pos (mul_pos (zero_lt_one.trans_le (of_one_le_get?_partDen nth_partDen_eq))
        zero_lt_of_den) zero_lt_of_den).ne'.isUnit := by
  have not_terminatedAt_n : ¬(of v).TerminatedAt n := by
    simp [terminatedAt_iff_partDen_none, nth_partDen_eq]
  refine (abs_sub_convs_le not_terminatedAt_n).trans ?_
  have : 0 < b := zero_lt_one.trans_le (of_one_le_get?_partDen nth_partDen_eq)
  refine one_div_le_one_div_of_le (mul_pos (mul_pos this zero_lt_of_den) zero_lt_of_den) ?_
  have : 0 < (of v).dens n := zero_lt_of_den
  conv_rhs => rw [mul_comm]
  gcongr
  exact le_of_succ_get?_den nth_partDen_eq

end ErrorTerm

end GenContFract
