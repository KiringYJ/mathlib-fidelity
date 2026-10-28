/-
Copyright (c) 2020 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
module

public import Mathlib.Algebra.ContinuedFractions.ContinuantsRecurrence
public import Mathlib.Algebra.ContinuedFractions.TerminatedStable
public import Mathlib.Algebra.Field.Basic

/-!
# Equivalence of Recursive and Direct Computations of Convergents of Generalized Continued Fractions

## Summary

We show the equivalence of two computations of convergents (recurrence relation (`convs`) vs.
direct evaluation (`convs'`)) for generalized continued fractions (`GenContFract`s) over fields:
where the direct evaluation is defined, the denominator of the convergent is a unit and both
computations agree. On linear ordered fields, both are defined when the partial numerators and
denominators are positive, in particular for regular continued fractions. We follow the proof from
[hardy2008introduction], Chapter 10. Here's a sketch:

Let `c` be a continued fraction `[h; (a₀, b₀), (a₁, b₁), (a₂, b₂),...]`, visually:
$$
  c = h + \dfrac{a_0}
                {b_0 + \dfrac{a_1}
                             {b_1 + \dfrac{a_2}
                                          {b_2 + \dfrac{a_3}
                                                       {b_3 + \dots}}}}
$$
One can compute the convergents of `c` in two ways:
1. Directly evaluating the fraction described by `c` up to a given `n` (`convs'`)
2. Using the recurrence (`convs`):
  - `A₋₁ = 1,  A₀ = h,  Aₙ = bₙ₋₁ * Aₙ₋₁ + aₙ₋₁ * Aₙ₋₂`, and
  - `B₋₁ = 0,  B₀ = 1,  Bₙ = bₙ₋₁ * Bₙ₋₁ + aₙ₋₁ * Bₙ₋₂`.

To show the equivalence of the computations in the main theorem of this file
`exists_convs_eq_of_convs'_eq_some`, we proceed by induction. The case `n = 0` is trivial.

For `n + 1`, the direct evaluation of `c` up to position `n + 1` divides by `bₙ`, so `bₙ` is a
unit. We then "squash" the `n + 1`th position of `c` into the `n`th position to obtain
another continued fraction
  `c' := [h; (a₀, b₀),..., (aₙ-₁, bₙ-₁ + aₙ / bₙ), (aₙ, bₙ),...]`.
This squashing process is formalised in section `Squash`. Note that directly evaluating `c` up to
position `n + 1` is equal to evaluating `c'` up to `n`. This is shown in lemma
`succ_nth_conv'_eq_squashGCF_nth_conv'`.

By the inductive hypothesis, the two computations for the `n`th convergent of `c'` coincide.
So all that is left to show is that the recurrence relation for `c` at `n + 1` and `c'` at
`n` coincide: their continuants differ by the factor `bₙ`, which is shown by another induction.
The corresponding lemma in this file is `succ_nth_conv_eq_squashGCF_nth_conv`.

## Main Theorems

- `GenContFract.exists_convs_eq_of_convs'_eq_some` shows that the direct evaluation, where it is
  defined, computes the convergent.
- `GenContFract.convs_eq_convs'` shows the equivalence under a strict positivity restriction
  on the sequence.
- `ContFract.convs_eq_convs'` shows the equivalence for regular continued fractions.

## References

- https://en.wikipedia.org/wiki/Generalized_continued_fraction
- [*Hardy, GH and Wright, EM and Heath-Brown, Roger and Silverman, Joseph*][hardy2008introduction]

## Tags

fractions, recurrence, equivalence
-/

@[expose] public section


variable {K : Type*} {n : ℕ}

namespace GenContFract

variable {g : GenContFract K} {s : Stream'.Seq <| Pair K}

section Squash

/-!
We will show the equivalence of the computations by induction. To make the induction work, we need
to be able to *squash* the nth and (n + 1)th value of a sequence. This squashing itself and the
lemmas about it are not very interesting. As a reader, you hence might want to skip this section.
-/


section WithDivisionRing

variable [DivisionRing K]

/-- Given a sequence of `GenContFract.Pair`s `s = [(a₀, b₀), (a₁, b₁), ...]`, `squashSeq s n hb`
combines `⟨aₙ, bₙ⟩` and `⟨aₙ₊₁, bₙ₊₁⟩` at position `n` to `⟨aₙ, bₙ + aₙ₊₁ / bₙ₊₁⟩`. For example,
`squashSeq s 0 hb = [(a₀, b₀ + a₁ / b₁), (a₁, b₁),...]`.
The quotient `aₙ₊₁ / bₙ₊₁` needs the partial denominator `bₙ₊₁` to be a unit, which `hb` asserts.
If `s.TerminatedAt (n + 1)`, then `squashSeq s n hb = s`.
-/
noncomputable def squashSeq (s : Stream'.Seq <| Pair K) (n : ℕ)
    (hb : ∀ gp : Pair K, s.get? (n + 1) = some gp → IsUnit gp.b) : Stream'.Seq (Pair K) :=
  match hs : s.get? (n + 1) with
  | some gp_succ_n =>
    Stream'.Seq.nats.zipWith
      -- return the squashed value at position `n`; otherwise, do nothing.
      (fun n' gp => if n' = n then
        ⟨gp.a, gp.b + Checked.div gp_succ_n.a gp_succ_n.b (hb gp_succ_n hs)⟩ else gp) s
  | none => s

/-! We now prove some simple lemmas about the squashed sequence -/

/-- The entries of a sequence squashed at a position that is followed by another entry. -/
theorem squashSeq_get?_of_succ_get?_eq_some
    {hb : ∀ gp : Pair K, s.get? (n + 1) = some gp → IsUnit gp.b} {gp_succ_n : Pair K}
    (s_succ_nth_eq : s.get? (n + 1) = some gp_succ_n) (m : ℕ) :
    (squashSeq s n hb).get? m = if m = n then
      (s.get? m).map fun gp ↦
        ⟨gp.a, gp.b + Checked.div gp_succ_n.a gp_succ_n.b (hb gp_succ_n s_succ_nth_eq)⟩
      else s.get? m := by
  unfold squashSeq
  split
  · rename_i gp' hs
    obtain rfl : gp' = gp_succ_n := Option.some_inj.mp (hs.symm.trans s_succ_nth_eq)
    rw [Stream'.Seq.get?_zipWith, Stream'.Seq.nats_get?]
    cases s.get? m <;> by_cases h : m = n <;> simp [h]
  · rename_i hs
    exact absurd (hs.symm.trans s_succ_nth_eq) nofun

/-- If the sequence already terminated at position `n + 1`, nothing gets squashed. -/
theorem squashSeq_eq_self_of_terminated
    {hb : ∀ gp : Pair K, s.get? (n + 1) = some gp → IsUnit gp.b}
    (terminatedAt_succ_n : s.TerminatedAt (n + 1)) : squashSeq s n hb = s := by
  change s.get? (n + 1) = none at terminatedAt_succ_n
  unfold squashSeq
  split
  · rename_i hs
    exact absurd (hs.symm.trans terminatedAt_succ_n) nofun
  · rfl

/-- If the sequence has not terminated before position `n + 1`, the value at `n + 1` gets
squashed into position `n`. -/
theorem squashSeq_nth_of_not_terminated
    {hb : ∀ gp : Pair K, s.get? (n + 1) = some gp → IsUnit gp.b} {gp_n gp_succ_n : Pair K}
    (s_nth_eq : s.get? n = some gp_n) (s_succ_nth_eq : s.get? (n + 1) = some gp_succ_n) :
    (squashSeq s n hb).get? n =
      some ⟨gp_n.a, gp_n.b + Checked.div gp_succ_n.a gp_succ_n.b (hb gp_succ_n s_succ_nth_eq)⟩ := by
  rw [squashSeq_get?_of_succ_get?_eq_some s_succ_nth_eq, ite_eq_left rfl, s_nth_eq,
    Option.map_some]

/-- The values before the squashed position stay the same. -/
theorem squashSeq_nth_of_lt {hb : ∀ gp : Pair K, s.get? (n + 1) = some gp → IsUnit gp.b}
    {m : ℕ} (m_lt_n : m < n) : (squashSeq s n hb).get? m = s.get? m := by
  cases s_succ_nth_eq : s.get? (n + 1) with
  | none => rw [squashSeq_eq_self_of_terminated s_succ_nth_eq]
  | some => rw [squashSeq_get?_of_succ_get?_eq_some s_succ_nth_eq, ite_eq_right m_lt_n.ne]

/-- Squashing at position `n + 1` and taking the tail is the same as squashing the tail of the
sequence at position `n`. -/
theorem squashSeq_succ_n_tail_eq_squashSeq_tail_n
    {hb : ∀ gp : Pair K, s.get? (n + 1 + 1) = some gp → IsUnit gp.b} :
    (squashSeq s (n + 1) hb).tail =
      squashSeq s.tail n fun gp h ↦ hb gp (by rwa [Stream'.Seq.get?_tail] at h) := by
  cases s_succ_succ_nth_eq : s.get? (n + 2) with
  | none =>
    have : s.tail.get? (n + 1) = none := by rwa [Stream'.Seq.get?_tail]
    rw [squashSeq_eq_self_of_terminated s_succ_succ_nth_eq, squashSeq_eq_self_of_terminated this]
  | some gp_succ_succ_n =>
    have : s.tail.get? (n + 1) = some gp_succ_succ_n := by rwa [Stream'.Seq.get?_tail]
    ext1 m
    rw [Stream'.Seq.get?_tail, squashSeq_get?_of_succ_get?_eq_some s_succ_succ_nth_eq,
      squashSeq_get?_of_succ_get?_eq_some this, Stream'.Seq.get?_tail]
    simp only [Nat.add_right_cancel_iff]

/-- The auxiliary function `convs'Aux` returns the same value for a sequence and the
corresponding squashed sequence at the squashed position. -/
theorem succ_succ_nth_conv'Aux_eq_succ_nth_conv'Aux_squashSeq
    (hb : ∀ gp : Pair K, s.get? (n + 1) = some gp → IsUnit gp.b) :
    convs'Aux s (n + 2) = convs'Aux (squashSeq s n hb) (n + 1) := by
  cases s_succ_nth_eq : s.get? <| n + 1 with
  | none =>
    rw [squashSeq_eq_self_of_terminated s_succ_nth_eq,
      convs'Aux_stable_step_of_terminated s_succ_nth_eq]
  | some gp_succ_n =>
    induction n generalizing s gp_succ_n with
    | zero =>
      classical
      obtain ⟨gp_head, s_head_eq⟩ : ∃ gp_head, s.head = some gp_head :=
        s.ge_stable zero_le_one s_succ_nth_eq
      have hb' : IsUnit gp_succ_n.b := hb gp_succ_n s_succ_nth_eq
      have h_tail_head : s.tail.head = some gp_succ_n := by
        rwa [Stream'.Seq.head, Stream'.Seq.get?_tail]
      have : (squashSeq s 0 hb).head =
          some ⟨gp_head.a, gp_head.b + Checked.div gp_succ_n.a gp_succ_n.b hb'⟩ :=
        squashSeq_nth_of_not_terminated s_head_eq s_succ_nth_eq
      rw [convs'Aux_succ_some s_head_eq, convs'Aux_succ_some h_tail_head,
        convs'Aux_succ_some this]
      simp only [zeroth_conv'Aux_eq_zero, Option.bind_some, add_zero, dite_eq_left hb']
    | succ m IH =>
      obtain ⟨gp_head, s_head_eq⟩ : ∃ gp_head, s.head = some gp_head :=
        s.ge_stable (m + 2).zero_le s_succ_nth_eq
      have : (squashSeq s (m + 1) hb).head = some gp_head :=
        (squashSeq_nth_of_lt m.succ_pos).trans s_head_eq
      rw [convs'Aux_succ_some s_head_eq, convs'Aux_succ_some this,
        squashSeq_succ_n_tail_eq_squashSeq_tail_n,
        IH (s := s.tail) (fun gp h ↦ hb gp (by rwa [Stream'.Seq.get?_tail] at h)) gp_succ_n
          (by rwa [Stream'.Seq.get?_tail])]

/-! Let us now lift the squashing operation to gcfs. -/


/-- Given a gcf `g = [h; (a₀, b₀), (a₁, b₁), ...]`, we have
- `squashGCF g 0 hb = ⟨h + a₀ / b₀, g.s⟩`, whose zeroth convergent is the first convergent of `g`,
- `squashGCF g (n + 1) hb = ⟨g.h, squashSeq g.s n hb⟩`.
The quotient by the partial denominator `bₙ` needs it to be a unit, which `hb` asserts.
-/
noncomputable def squashGCF (g : GenContFract K) :
    (n : ℕ) → (∀ gp : Pair K, g.s.get? n = some gp → IsUnit gp.b) → GenContFract K
  | 0, hb =>
    match hs : g.s.get? 0 with
    | none => g
    | some gp => ⟨g.h + Checked.div gp.a gp.b (hb gp hs), g.s⟩
  | n + 1, hb => ⟨g.h, squashSeq g.s n hb⟩

/-! Again, we derive some simple lemmas that are not really of interest. This time for the
squashed gcf. -/

/-- Squashing at position `0` adds `a₀ / b₀` to the head term. -/
theorem squashGCF_zero {hb : ∀ gp : Pair K, g.s.get? 0 = some gp → IsUnit gp.b} {gp : Pair K}
    (s_zeroth_eq : g.s.get? 0 = some gp) :
    squashGCF g 0 hb = ⟨g.h + Checked.div gp.a gp.b (hb gp s_zeroth_eq), g.s⟩ := by
  rw [squashGCF]
  split
  · rename_i hs
    exact absurd (hs.symm.trans s_zeroth_eq) nofun
  · rename_i gp' hs
    obtain rfl : gp' = gp := Option.some_inj.mp (hs.symm.trans s_zeroth_eq)
    rfl


/-- If the gcf already terminated at position `n`, nothing gets squashed. -/
theorem squashGCF_eq_self_of_terminated
    {hb : ∀ gp : Pair K, g.s.get? n = some gp → IsUnit gp.b} (terminatedAt_n : TerminatedAt g n) :
    squashGCF g n hb = g := by
  cases n with
  | zero =>
    change g.s.get? 0 = none at terminatedAt_n
    rw [squashGCF]
    split
    · rfl
    · rename_i hs
      exact absurd (hs.symm.trans terminatedAt_n) nofun
  | succ =>
    cases g
    simp only [squashGCF, mk.injEq, true_and]
    exact squashSeq_eq_self_of_terminated terminatedAt_n

/-- The values before the squashed position stay the same. -/
theorem squashGCF_nth_of_lt {hb : ∀ gp : Pair K, g.s.get? (n + 1) = some gp → IsUnit gp.b}
    {m : ℕ} (m_lt_n : m < n) : (squashGCF g (n + 1) hb).s.get? m = g.s.get? m := by
  simp only [squashGCF, squashSeq_nth_of_lt m_lt_n]

/-- `convs'` returns the same value for a gcf and the corresponding squashed gcf at the
squashed position. -/
theorem succ_nth_conv'_eq_squashGCF_nth_conv'
    (hb : ∀ gp : Pair K, g.s.get? n = some gp → IsUnit gp.b) :
    g.convs' (n + 1) = (squashGCF g n hb).convs' n := by
  cases n with
  | zero =>
    rcases g_s_head_eq : g.s.get? 0 with _ | gp
    · rw [squashGCF_eq_self_of_terminated g_s_head_eq,
        convs'_stable_of_terminated (Nat.zero_le 1) g_s_head_eq]
    · have hb' : IsUnit (gp.b + 0) := by rw [add_zero]; exact hb gp g_s_head_eq
      have h_head : g.s.head = some gp := g_s_head_eq
      rw [squashGCF_zero g_s_head_eq]
      simp only [convs', convs'Aux_succ_some h_head, zeroth_conv'Aux_eq_zero, Option.bind_some,
        dite_eq_left hb', Option.map_some, add_zero]
  | succ =>
    simp only [succ_succ_nth_conv'Aux_eq_succ_nth_conv'Aux_squashSeq hb, convs', squashGCF]

/-- The auxiliary continuants before the squashed position stay the same. -/
theorem contsAux_eq_contsAux_squashGCF_of_le
    (hb : ∀ gp : Pair K, g.s.get? n = some gp → IsUnit gp.b) {m : ℕ} :
    m ≤ n → contsAux g m = (squashGCF g n hb).contsAux m :=
  Nat.strong_induction_on m
    (by
      clear m
      intro m IH m_le_n
      rcases m with - | m'
      · rfl
      · rcases n with - | n'
        · exact (m'.not_succ_le_zero m_le_n).elim
        -- 1 ≰ 0
        · rcases m' with - | m''
          · rfl
          · -- get some inequalities to instantiate the IH for m'' and m'' + 1
            have m'_lt_n : m'' + 1 < n' + 1 := m_le_n
            have succ_m''th_contsAux_eq := IH (m'' + 1) (lt_add_one (m'' + 1)) m'_lt_n.le
            have : m'' < m'' + 2 := lt_add_of_pos_right m'' zero_lt_two
            have m''th_contsAux_eq := IH m'' this (le_trans this.le m_le_n)
            have : (squashGCF g (n' + 1) hb).s.get? m'' = g.s.get? m'' :=
              squashGCF_nth_of_lt (Nat.succ_lt_succ_iff.mp m'_lt_n)
            simp [contsAux, succ_m''th_contsAux_eq, m''th_contsAux_eq, this])

end WithDivisionRing

section WithField

variable [Field K]

/-- Where `g` has not terminated at position `n`, its continuants at position `n + 1` are those
of the gcf squashed at `n`, multiplied by the partial denominator `bₙ`. -/
theorem conts_succ_eq_mul_squashGCF_conts {gp : Pair K} (s_nth_eq : g.s.get? n = some gp)
    (hb : ∀ gp : Pair K, g.s.get? n = some gp → IsUnit gp.b) :
    g.conts (n + 1) =
      ⟨gp.b * (squashGCF g n hb).nums n, gp.b * (squashGCF g n hb).dens n⟩ := by
  have hb' : IsUnit gp.b := hb gp s_nth_eq
  cases n with
  | zero =>
    rw [squashGCF_zero s_nth_eq, first_cont_eq s_nth_eq, zeroth_num_eq_h, zeroth_den_eq_one,
      mul_add, mul_div_cancel₀, mul_one, mul_comm]
  | succ n' =>
    obtain ⟨⟨pa, pb⟩, s_n'th_eq⟩ : ∃ gp_n', g.s.get? n' = some gp_n' :=
      g.s.ge_stable n'.le_succ s_nth_eq
    set g' := squashGCF g (n' + 1) hb
    have g'_s_n'th_eq : g'.s.get? n' = some ⟨pa, pb + Checked.div gp.a gp.b hb'⟩ :=
      squashSeq_nth_of_not_terminated s_n'th_eq s_nth_eq
    have e1 : g'.contsAux (n' + 1) = g.contsAux (n' + 1) :=
      (contsAux_eq_contsAux_squashGCF_of_le hb (le_refl <| n' + 1)).symm
    have e0 : g'.contsAux n' = g.contsAux n' :=
      (contsAux_eq_contsAux_squashGCF_of_le hb n'.le_succ).symm
    have hg' : g'.conts (n' + 1) = ⟨(pb + Checked.div gp.a gp.b hb') * (g.contsAux (n' + 1)).a +
        pa * (g.contsAux n').a, (pb + Checked.div gp.a gp.b hb') * (g.contsAux (n' + 1)).b +
        pa * (g.contsAux n').b⟩ :=
      conts_recurrenceAux g'_s_n'th_eq e0 e1
    have hg2 : g.contsAux (n' + 2) = ⟨pb * (g.contsAux (n' + 1)).a + pa * (g.contsAux n').a,
        pb * (g.contsAux (n' + 1)).b + pa * (g.contsAux n').b⟩ :=
      contsAux_recurrence s_n'th_eq rfl rfl
    have hg : g.conts (n' + 2) = ⟨gp.b * (g.contsAux (n' + 2)).a + gp.a * (g.contsAux (n' + 1)).a,
        gp.b * (g.contsAux (n' + 2)).b + gp.a * (g.contsAux (n' + 1)).b⟩ :=
      conts_recurrenceAux s_nth_eq rfl rfl
    rw [hg, num_eq_conts_a, den_eq_conts_b, hg', hg2]
    simp only [Pair.mk.injEq]
    constructor <;>
    · rw [mul_add, mul_add, ← mul_assoc gp.b (pb + _), mul_add gp.b pb, mul_div_cancel₀]
      grind

/-- Where `g` has not terminated at position `n`, its numerator at position `n + 1` is the one
of the gcf squashed at `n`, multiplied by the partial denominator `bₙ`. -/
theorem nums_succ_eq_mul_squashGCF_nums {gp : Pair K} (s_nth_eq : g.s.get? n = some gp)
    (hb : ∀ gp : Pair K, g.s.get? n = some gp → IsUnit gp.b) :
    g.nums (n + 1) = gp.b * (squashGCF g n hb).nums n := by
  rw [num_eq_conts_a, conts_succ_eq_mul_squashGCF_conts s_nth_eq hb]

/-- Where `g` has not terminated at position `n`, its denominator at position `n + 1` is the one
of the gcf squashed at `n`, multiplied by the partial denominator `bₙ`. -/
theorem dens_succ_eq_mul_squashGCF_dens {gp : Pair K} (s_nth_eq : g.s.get? n = some gp)
    (hb : ∀ gp : Pair K, g.s.get? n = some gp → IsUnit gp.b) :
    g.dens (n + 1) = gp.b * (squashGCF g n hb).dens n := by
  rw [den_eq_conts_b, conts_succ_eq_mul_squashGCF_conts s_nth_eq hb]

/-- The denominator of the gcf squashed at position `n` is a unit when the denominator of `g` at
position `n + 1` is. -/
theorem isUnit_squashGCF_dens (hb : ∀ gp : Pair K, g.s.get? n = some gp → IsUnit gp.b)
    (hB : IsUnit (g.dens (n + 1))) : IsUnit ((squashGCF g n hb).dens n) := by
  rcases (g.s.get? n).eq_none_or_eq_some with s_nth_eq | ⟨gp, s_nth_eq⟩
  · rwa [squashGCF_eq_self_of_terminated s_nth_eq, ← dens_stable_of_terminated n.le_succ s_nth_eq]
  · rw [dens_succ_eq_mul_squashGCF_dens s_nth_eq hb] at hB
    exact isUnit_of_mul_isUnit_right hB

/-- The convergents coincide in the expected way at the squashed position if the partial denominator
at the squashed position is not zero. -/
theorem succ_nth_conv_eq_squashGCF_nth_conv {hB : IsUnit (g.dens (n + 1))}
    (nth_partDen_ne_zero : ∀ {b : K}, g.partDens.get? n = some b → b ≠ 0) :
    g.convs (n + 1) =
      (squashGCF g n fun _ h ↦ (nth_partDen_ne_zero (partDen_eq_s_b h)).isUnit).convs n
        (isUnit_squashGCF_dens _ hB) := by
  rcases (g.s.get? n).eq_none_or_eq_some with s_nth_eq | ⟨gp, s_nth_eq⟩
  · simp only [squashGCF_eq_self_of_terminated s_nth_eq,
      convs_stable_of_terminated n.le_succ s_nth_eq]
  · have hb : ∀ gp : Pair K, g.s.get? n = some gp → IsUnit gp.b :=
      fun _ h ↦ (nth_partDen_ne_zero (partDen_eq_s_b h)).isUnit
    rw [conv_eq_num_div_den, conv_eq_num_div_den]
    simp only [nums_succ_eq_mul_squashGCF_nums s_nth_eq hb,
      dens_succ_eq_mul_squashGCF_dens s_nth_eq hb]
    exact mul_div_mul_left _ _

/-- If the direct evaluation of `s` up to position `n + 1` is defined, then the partial
denominator `bₙ`, which is the innermost denominator of that evaluation, is a unit. -/
theorem isUnit_of_convs'Aux_succ_eq_some : ∀ {s : Stream'.Seq (Pair K)} {n : ℕ} {x : K}
    {gp : Pair K}, convs'Aux s (n + 1) = some x → s.get? n = some gp → IsUnit gp.b
  | s, 0, x, gp, hx, s_nth_eq => by
    obtain ⟨t, ht, hBt, -⟩ := (convs'Aux_succ_eq_some_iff s_nth_eq).mp hx
    obtain rfl : t = 0 := Option.some_inj.mp (ht.symm.trans zeroth_conv'Aux_eq_zero)
    rwa [add_zero] at hBt
  | s, n + 1, x, gp, hx, s_nth_eq => by
    obtain ⟨gp_head, s_head_eq⟩ : ∃ gp_head, s.head = some gp_head :=
      s.ge_stable (n + 1).zero_le s_nth_eq
    obtain ⟨t, ht, -⟩ := (convs'Aux_succ_eq_some_iff s_head_eq).mp hx
    exact isUnit_of_convs'Aux_succ_eq_some ht (by rwa [Stream'.Seq.get?_tail])

end WithField

end Squash

/-- Where the direct evaluation `g.convs' n` of a gcf over a field is defined, the denominator `Bₙ`
is a unit and the convergent `g.convs n` is the value of the direct evaluation. -/
theorem exists_convs_eq_of_convs'_eq_some [Field K] :
    ∀ {g : GenContFract K} {n : ℕ} {x : K}, g.convs' n = some x →
      ∃ hB : IsUnit (g.dens n), g.convs n hB = x
  | g, 0, x, hx => by
    simp only [zeroth_conv'_eq_h, Option.some_inj] at hx
    exact ⟨by simp, by simp [hx]⟩
  | g, n + 1, x, hx => by
    rcases s_nth_eq : g.s.get? n with _ | gp
    · obtain ⟨hB, h⟩ := exists_convs_eq_of_convs'_eq_some (g := g) (n := n)
        ((convs'_stable_of_terminated n.le_succ s_nth_eq).symm.trans hx)
      have hd := dens_stable_of_terminated n.le_succ s_nth_eq
      refine ⟨hd ▸ hB, ?_⟩
      rw [convs_stable_of_terminated n.le_succ s_nth_eq, h]
    · obtain ⟨y, hy, -⟩ := Option.map_eq_some_iff.mp hx
      have hb' : IsUnit gp.b := isUnit_of_convs'Aux_succ_eq_some hy s_nth_eq
      have hb : ∀ gp : Pair K, g.s.get? n = some gp → IsUnit gp.b := fun gp' h ↦
        (Option.some_inj.mp (h.symm.trans s_nth_eq)) ▸ hb'
      obtain ⟨hB', h⟩ := exists_convs_eq_of_convs'_eq_some (g := squashGCF g n hb) (n := n)
        ((succ_nth_conv'_eq_squashGCF_nth_conv' hb).symm.trans hx)
      have hB : IsUnit (g.dens (n + 1)) := by
        rw [dens_succ_eq_mul_squashGCF_dens s_nth_eq hb]
        exact hb'.mul hB'
      refine ⟨hB, ?_⟩
      rw [succ_nth_conv_eq_squashGCF_nth_conv fun hb ↦ ?_, ← h]
      obtain ⟨gp', s_nth_eq', rfl⟩ := exists_s_b_of_partDen hb
      exact ((Option.some_inj.mp (s_nth_eq'.symm.trans s_nth_eq)) ▸ hb').ne_zero

section Positivity

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The denominators of a gcf are positive where its partial numerators and denominators are. -/
theorem dens_pos_of_pos : ∀ {n : ℕ},
    (∀ {gp : Pair K} {m : ℕ}, m < n → g.s.get? m = some gp → 0 < gp.a ∧ 0 < gp.b) →
      0 < g.dens n
  | 0, _ => by simp
  | 1, s_pos => by
    rcases h0 : g.s.get? 0 with _ | p
    · rw [dens_stable_of_terminated (Nat.zero_le 1) h0]; simp
    · rw [first_den_eq h0]; exact (s_pos Nat.zero_lt_one h0).2
  | n + 2, s_pos => by
    have ih1 := dens_pos_of_pos (n := n + 1) fun hm hgp ↦ s_pos (by omega) hgp
    have ih0 := dens_pos_of_pos (n := n) fun hm hgp ↦ s_pos (by omega) hgp
    rcases h : g.s.get? (n + 1) with _ | p
    · rw [dens_stable_of_terminated (Nat.le_succ _) h]; exact ih1
    · have hp := s_pos (by omega) h
      rw [dens_recurrence h rfl rfl]
      exact add_pos (mul_pos hp.2 ih1) (mul_pos hp.1 ih0)

/-- The direct evaluation is defined, with a nonnegative value, where the partial numerators and
denominators are positive. -/
theorem exists_convs'Aux_eq_some_of_pos : ∀ {s : Stream'.Seq (Pair K)} {n : ℕ},
    (∀ {gp : Pair K} {m : ℕ}, m < n → s.get? m = some gp → 0 < gp.a ∧ 0 < gp.b) →
      ∃ t, convs'Aux s n = some t ∧ 0 ≤ t
  | s, 0, _ => ⟨0, rfl, le_rfl⟩
  | s, n + 1, s_pos => by
    rcases hs : s.head with _ | p
    · exact ⟨0, convs'Aux_succ_none hs n, le_rfl⟩
    · obtain ⟨t, ht, t_nonneg⟩ := exists_convs'Aux_eq_some_of_pos (s := s.tail) (n := n)
        fun {gp m} hm hgp ↦ s_pos (Nat.succ_lt_succ hm) (by rwa [Stream'.Seq.get?_tail] at hgp)
      have hp := s_pos (Nat.zero_lt_succ n) (show s.get? 0 = some p from hs)
      have hpos : 0 < p.b + t := add_pos_of_pos_of_nonneg hp.2 t_nonneg
      exact ⟨p.a / (p.b + t), (convs'Aux_succ_eq_some_iff hs).mpr ⟨t, ht, hpos.ne'.isUnit, rfl⟩,
        (div_pos hp.1 hpos).le⟩

/-- Shows that the recurrence relation (`convs`) and direct evaluation (`convs'`) of the
generalized continued fraction coincide at position `n` if the sequence of fractions contains
strictly positive values only.
Requiring positivity of all values is just one possible condition to obtain this result.
For example, the dual - sequences with strictly negative values only - would also work.

In practice, one most commonly deals with regular continued fractions, which satisfy the
positivity criterion required here. The analogous result for them
(see `ContFract.convs_eq_convs'`) hence follows directly from this theorem.
-/
theorem convs_eq_convs'
    (s_pos : ∀ {gp : Pair K} {m : ℕ}, m < n → g.s.get? m = some gp → 0 < gp.a ∧ 0 < gp.b) :
    g.convs' n = some (g.convs n (dens_pos_of_pos s_pos).ne'.isUnit) := by
  obtain ⟨t, ht, -⟩ := exists_convs'Aux_eq_some_of_pos s_pos
  have hx : g.convs' n = some (g.h + t) := by simp [convs', ht]
  obtain ⟨hB, hconv⟩ := exists_convs_eq_of_convs'_eq_some hx
  rw [hx, ← hconv]

end Positivity

end GenContFract

open GenContFract

namespace ContFract

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The partial numerators and denominators of a regular continued fraction are positive. -/
theorem pos_of_s_get?_eq_some {c : ContFract K} {gp : Pair K} {m : ℕ}
    (s_nth_eq : (↑c : GenContFract K).s.get? m = some gp) : 0 < gp.a ∧ 0 < gp.b :=
  ⟨zero_lt_one.trans_le ((c : SimpContFract K).property m gp.a
    (partNum_eq_s_a s_nth_eq)).symm.le, c.property m gp.b <| partDen_eq_s_b s_nth_eq⟩

/-- The denominators of a regular continued fraction are positive. -/
theorem zero_lt_dens (c : ContFract K) (n : ℕ) : 0 < (↑c : GenContFract K).dens n :=
  GenContFract.dens_pos_of_pos fun _ s_nth_eq ↦ pos_of_s_get?_eq_some s_nth_eq

/-- Shows that the recurrence relation (`convs`) and direct evaluation (`convs'`) of a
(regular) continued fraction coincide. -/
theorem convs_eq_convs' {c : ContFract K} (n : ℕ) :
    (↑c : GenContFract K).convs' n =
      some ((↑c : GenContFract K).convs n (c.zero_lt_dens n).ne'.isUnit) :=
  GenContFract.convs_eq_convs' fun _ s_nth_eq ↦ pos_of_s_get?_eq_some s_nth_eq

end ContFract

/-- The denominators of a regular continued fraction are positive: its convergents and quotients by
its denominators find their evidence. -/
macro_rules | `(tactic| checked_nonzero) => `(tactic|
    solve
    | assumption
    | exact (ContFract.zero_lt_dens _ _).ne')
