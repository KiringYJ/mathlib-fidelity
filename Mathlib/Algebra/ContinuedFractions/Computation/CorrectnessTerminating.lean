/-
Copyright (c) 2020 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
module

public import Mathlib.Algebra.ContinuedFractions.Computation.Translations
public import Mathlib.Algebra.ContinuedFractions.TerminatedStable
public import Mathlib.Algebra.ContinuedFractions.ContinuantsRecurrence
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Correctness of Terminating Continued Fraction Computations (`GenContFract.of`)

## Summary

We show the correctness of the algorithm computing continued fractions (`GenContFract.of`)
in case of termination in the following sense:

At every step `n : ℕ`, we can obtain the value `v` by adding a specific residual term to the last
denominator of the fraction described by `(GenContFract.of v).convs' n`.
The residual term will be zero exactly when the continued fraction terminated; otherwise, the
residual term will be given by the fractional part stored in `GenContFract.IntFractPair.stream v n`.

For an example, refer to
`GenContFract.compExactValue_correctness_of_stream_eq_some` and for more
information about the computation process, refer to `Algebra.ContinuedFractions.Computation.Basic`.

## Main definitions

- `GenContFract.compExactValue` can be used to compute the exact value approximated by the
  continued fraction `GenContFract.of v` by adding a residual term as described in the summary.

## Main Theorems

- `GenContFract.compExactValue_correctness_of_stream_eq_some` shows that
  `GenContFract.compExactValue` indeed returns the value `v` when given the convergent and
  fractional part as described in the summary.
- `GenContFract.of_correctness_of_terminatedAt` shows the equality
  `v = (GenContFract.of v).convs n` if `GenContFract.of v` terminated at position `n`.
-/

@[expose] public section

assert_not_exists Finset

namespace GenContFract

open GenContFract (of)

-- `compExactValue_correctness_of_stream_eq_some` does not trivially generalize to `DivisionRing`
variable {K : Type*} [Field K] [LinearOrder K] {v : K} {n : ℕ}

open scoped Classical in
/-- Given two continuants `pconts` and `conts` and a value `fr`, this function returns
- `conts.a / conts.b` if `fr = 0`
- `exactConts.a / exactConts.b` where `exactConts = nextConts 1 fr⁻¹ pconts conts`
  otherwise,

and `none` if the denominator of that quotient is not a unit.

This function can be used to compute the exact value approximated by a continued fraction
`GenContFract.of v` as described in lemma `compExactValue_correctness_of_stream_eq_some`.
-/
protected noncomputable def compExactValue (pconts conts : Pair K) (fr : K) : Option K :=
  -- if the fractional part is zero, we exactly approximated the value by the last continuants
  if hfr : fr = 0 then
    if hB : IsUnit conts.b then some (conts.a / conts.b) else none
  else -- otherwise, we have to include the fractional part in a final continuants step.
    letI exactConts := nextConts 1 fr⁻¹ pconts conts
    if hB : IsUnit exactConts.b then some (exactConts.a / exactConts.b) else none

open GenContFract (compExactValue) in
/-- `compExactValue` without a fractional part has a value exactly when the last denominator is a
unit, and then returns the last convergent. -/
theorem compExactValue_eq_some_iff_of_eq_zero {pconts conts : Pair K} {x : K} :
    compExactValue pconts conts 0 = some x ↔ ∃ hB : IsUnit conts.b, conts.a / conts.b = x := by
  unfold GenContFract.compExactValue
  rw [dite_eq_left rfl]
  by_cases hB : IsUnit conts.b
  · rw [dite_eq_left hB, Option.some_inj]
    exact ⟨fun h ↦ ⟨hB, h⟩, fun ⟨_, h⟩ ↦ h⟩
  · rw [dite_eq_right hB]
    exact ⟨fun h ↦ (Option.some_ne_none x h.symm).elim, fun ⟨h, _⟩ ↦ (hB h).elim⟩

open GenContFract (compExactValue) in
/-- `compExactValue` with a nonzero fractional part `fr` has a value exactly when the denominator
of the final continuants step is a unit, and then returns the corresponding quotient. -/
theorem compExactValue_eq_some_iff_of_ne_zero {pconts conts : Pair K} {fr x : K}
    (hfr : fr ≠ 0) : compExactValue pconts conts fr = some x ↔
      ∃ hB : IsUnit (nextConts 1 fr⁻¹ pconts conts).b,
        (nextConts 1 fr⁻¹ pconts conts).a / (nextConts 1 fr⁻¹ pconts conts).b = x := by
  unfold GenContFract.compExactValue
  rw [dite_eq_right hfr]
  by_cases hB : IsUnit (nextConts 1 fr⁻¹ pconts conts).b
  · rw [dite_eq_left hB, Option.some_inj]
    exact ⟨fun h ↦ ⟨hB, h⟩, fun ⟨_, h⟩ ↦ h⟩
  · rw [dite_eq_right hB]
    exact ⟨fun h ↦ (Option.some_ne_none x h.symm).elim, fun ⟨h, _⟩ ↦ (hB h).elim⟩

variable [FloorRing K]

/-- Just a computational lemma we need for the next main proof. -/
protected theorem compExactValue_correctness_of_stream_eq_some_aux_comp {a : K} (b c : K)
    (fract_a_ne_zero : Int.fract a ≠ 0) :
    ((⌊a⌋ : K) * b + c) / Int.fract a + b = (b * a + c) / Int.fract a := by
  field_simp
  rw [Int.fract]
  ring

open GenContFract
  (compExactValue compExactValue_correctness_of_stream_eq_some_aux_comp)

/-- Shows the correctness of `compExactValue` in case the continued fraction
`GenContFract.of v` did not terminate at position `n`. That is, we obtain the
value `v` if we pass the two successive (auxiliary) continuants at positions `n` and `n + 1` as well
as the fractional part at `IntFractPair.stream n` to `compExactValue`.

The correctness might be seen more readily if one uses `convs'` to evaluate the continued
fraction. Here is an example to illustrate the idea:

Let `(v : ℚ) := 3.4`. We have
- `GenContFract.IntFractPair.stream v 0 = some ⟨3, 0.4⟩`, and
- `GenContFract.IntFractPair.stream v 1 = some ⟨2, 0.5⟩`.

Now `(GenContFract.of v).convs' 1 = 3 + 1/2`, and our fractional term at position `2` is `0.5`.
We hence have `v = 3 + 1/(2 + 0.5) = 3 + 1/2.5 = 3.4`.
This computation corresponds exactly to the one using the recurrence equation in `compExactValue`.
-/
theorem compExactValue_correctness_of_stream_eq_some :
    ∀ {ifp_n : IntFractPair K}, IntFractPair.stream v n = some ifp_n →
      some v = compExactValue ((of v).contsAux n) ((of v).contsAux <| n + 1) ifp_n.fr := by
  let g := of v
  induction n with
  | zero =>
    intro ifp_zero stream_zero_eq
    obtain rfl : IntFractPair.of v = ifp_zero := by
      simpa only [IntFractPair.stream, Option.some.injEq] using stream_zero_eq
    cases eq_or_ne (Int.fract v) 0 with
    | inl fract_eq_zero =>
      -- Int.fract v = 0; we must then have `v = ⌊v⌋`
      have : v = ⌊v⌋ := by
        calc
          v = Int.fract v + ⌊v⌋ := by rw [Int.fract_add_floor]
          _ = ⌊v⌋ := by simp [fract_eq_zero]
      simp [compExactValue, IntFractPair.of, fract_eq_zero, ← this]
    | inr fract_ne_zero =>
      -- Int.fract v ≠ 0; the claim then easily follows by unfolding a single computation step
      rw [show (IntFractPair.of v).fr = Int.fract v from rfl, eq_comm,
        compExactValue_eq_some_iff_of_ne_zero fract_ne_zero]
      have hd : (nextConts 1 (Int.fract v)⁻¹ ((of v).contsAux 0) ((of v).contsAux (0 + 1))).b =
          (Int.fract v)⁻¹ := by
        simp [contsAux, nextConts, nextDen]
      refine ⟨by rw [hd]; exact IsUnit.inv₀ fract_ne_zero.isUnit, ?_⟩
      simp only [contsAux, nextConts, nextNum, nextDen, of_h_eq_floor]
      field_simp
      rw [Int.fract]
      ring
  | succ n IH =>
    intro ifp_succ_n succ_nth_stream_eq
    obtain ⟨ifp_n, nth_stream_eq, nth_fract_ne_zero, rfl⟩ :=
      IntFractPair.succ_nth_stream_eq_some_iff.1 succ_nth_stream_eq
    -- the continuants are units along the computation: the denominator of the final continuants
    -- step is multiplied by the inverse of the next fractional part
    have s_nth_eq : g.s.get? n = some ⟨1, ⌊ifp_n.fr⁻¹⌋⟩ :=
      get?_of_eq_some_of_get?_intFractPair_stream_fr_ne_zero nth_stream_eq nth_fract_ne_zero
    have IH' := (IH nth_stream_eq).symm
    have conts_eq : g.contsAux (n + 2) = nextConts 1 (⌊ifp_n.fr⁻¹⌋ : K) (g.contsAux n)
        (g.contsAux (n + 1)) := by
      rw [contsAux_recurrence s_nth_eq rfl rfl]; rfl
    change some v = compExactValue (g.contsAux (n + 1)) (g.contsAux (n + 2))
      (Int.fract ifp_n.fr⁻¹)
    rw [eq_comm, conts_eq]
    generalize g.contsAux n = ppconts at IH' ⊢
    generalize g.contsAux (n + 1) = pconts at IH' ⊢
    obtain ⟨ppA, ppB⟩ := ppconts
    obtain ⟨pA, pB⟩ := pconts
    rw [compExactValue_eq_some_iff_of_ne_zero nth_fract_ne_zero] at IH'
    simp only [nextConts, nextNum, nextDen, one_mul] at IH' ⊢
    generalize ifp_n.fr⁻¹ = r at IH' ⊢
    obtain ⟨hD, hv⟩ := IH'
    cases eq_or_ne (Int.fract r) 0 with
    | inl hf =>
      -- the next fractional part is zero, so `r` is an integer and the continuants are exact
      have hfl : (⌊r⌋ : K) = r := by
        have := Int.fract_add_floor r
        rwa [hf, zero_add] at this
      rw [hf, compExactValue_eq_some_iff_of_eq_zero]
      simp only [hfl]
      exact ⟨hD, hv⟩
    | inr hf =>
      rw [compExactValue_eq_some_iff_of_ne_zero hf]
      simp only [nextConts, nextNum, nextDen, one_mul]
      have hfl : (⌊r⌋ : K) = r - Int.fract r := by rw [Int.fract]; ring
      have hb : (Int.fract r)⁻¹ * (⌊r⌋ * pB + ppB) + pB = (Int.fract r)⁻¹ * (r * pB + ppB) := by
        rw [hfl]; field_simp; ring
      have ha : (Int.fract r)⁻¹ * (⌊r⌋ * pA + ppA) + pA = (Int.fract r)⁻¹ * (r * pA + ppA) := by
        rw [hfl]; field_simp; ring
      refine ⟨by rw [hb]; exact (IsUnit.inv₀ hf.isUnit).mul hD, ?_⟩
      simp only [ha, hb]
      rw [← hv, mul_div_mul_left]

open GenContFract (of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none)

/-- The denominator of `GenContFract.of v` at step `n - 1` is a unit and the convergent there is
exactly `v` if the `IntFractPair.stream` of the corresponding continued fraction terminated at
step `n`. -/
theorem of_correctness_of_nth_stream_eq_none (nth_stream_eq_none : IntFractPair.stream v n = none) :
    ∃ hB : IsUnit ((of v).dens (n - 1)), v = (of v).convs (n - 1) hB := by
  induction n with
  | zero => contradiction
  -- IntFractPair.stream v 0 ≠ none
  | succ n IH =>
    obtain ⟨nth_stream_eq_none⟩ | ⟨ifp_n, nth_stream_eq, nth_stream_fr_eq_zero⟩ :
      IntFractPair.stream v n = none ∨ ∃ ifp, IntFractPair.stream v n = some ifp ∧ ifp.fr = 0 :=
      IntFractPair.succ_nth_stream_eq_none_iff.1 nth_stream_eq_none
    · cases n with
      | zero => contradiction
      | succ n' =>
        -- IntFractPair.stream v 0 ≠ none
        have terminatedAt_n' : (of v).TerminatedAt n' :=
          of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none.2 nth_stream_eq_none
        obtain ⟨hB, h⟩ := IH nth_stream_eq_none
        have hd := dens_stable_of_terminated n'.le_succ terminatedAt_n'
        refine ⟨by rw [Nat.add_sub_cancel, hd]; exact hB, ?_⟩
        simp only [Nat.add_sub_cancel] at h ⊢
        rw [convs_stable_of_terminated n'.le_succ terminatedAt_n']
        exact h
    · have := (compExactValue_correctness_of_stream_eq_some nth_stream_eq).symm
      rw [nth_stream_fr_eq_zero, compExactValue_eq_some_iff_of_eq_zero] at this
      obtain ⟨hB, h⟩ := this
      exact ⟨hB, h.symm⟩

/-- The denominator of `GenContFract.of v` at a position where it terminated is a unit. -/
theorem isUnit_of_den_of_terminatedAt (terminatedAt_n : (of v).TerminatedAt n) :
    IsUnit ((of v).dens n) :=
  (of_correctness_of_nth_stream_eq_none (n := n + 1)
    (of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none.1 terminatedAt_n)).fst

/-- If `GenContFract.of v` terminated at step `n`, then the `n`th convergent is exactly `v`. -/
theorem of_correctness_of_terminatedAt (terminatedAt_n : (of v).TerminatedAt n) :
    v = (of v).convs n (isUnit_of_den_of_terminatedAt terminatedAt_n) :=
  (of_correctness_of_nth_stream_eq_none (n := n + 1)
    (of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none.1 terminatedAt_n)).snd

/-- If `GenContFract.of v` terminates, then there is `n : ℕ` such that the `n`th convergent is
exactly `v`.
-/
theorem of_correctness_of_terminates (terminates : (of v).Terminates) :
    ∃ (n : ℕ) (hB : IsUnit ((of v).dens n)), v = (of v).convs n hB :=
  Exists.elim terminates fun n terminatedAt_n =>
    ⟨n, _, of_correctness_of_terminatedAt terminatedAt_n⟩

open Filter

/-- If `GenContFract.of v` terminates, then its convergents will eventually always be `v`. -/
theorem of_correctness_atTop_of_terminates (terminates : (of v).Terminates) :
    ∀ᶠ n in atTop, ∃ hB : IsUnit ((of v).dens n), v = (of v).convs n hB := by
  rw [eventually_atTop]
  obtain ⟨n, terminatedAt_n⟩ : ∃ n, (of v).TerminatedAt n := terminates
  use n
  intro m m_geq_n
  exact ⟨_, of_correctness_of_terminatedAt (terminated_stable m_geq_n terminatedAt_n)⟩

end GenContFract
