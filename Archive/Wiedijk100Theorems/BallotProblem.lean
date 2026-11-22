/-
Copyright (c) 2022 Bhavik Mehta, Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kexing Ying
-/
module

public import Mathlib.Probability.UniformOn

/-!
# Ballot problem

This file proves Theorem 30 from the [100 Theorems List](https://www.cs.ru.nl/~freek/100/).

The ballot problem asks, if in an election, candidate A receives `p` votes whereas candidate B
receives `q` votes where `p > q`, what is the probability that candidate A is strictly ahead
throughout the count. The probability of this is `(p - q) / (p + q)`.

## Main definitions

* `countedSequence`: given natural numbers `p` and `q`, `countedSequence p q` is the set of
  all lists containing `p` of `1`s and `q` of `-1`s representing the votes of candidate A and B
  respectively.
* `staysPositive`: the set of lists of integers whose nonempty suffixes have positive sum.
  Its intersection with `countedSequence` is the set of lists where candidate A is strictly ahead.

## Main result

* `ballot_problem`: the ballot problem.

-/

@[expose] public section

open Set ProbabilityTheory MeasureTheory
open scoped ENNReal

namespace Ballot

/-- The set of lists of integers whose nonempty suffixes have positive sum. -/
def staysPositive : Set (List ℤ) :=
  {l | ∀ l₂, l₂ ≠ [] → l₂ <:+ l → 0 < l₂.sum}

@[simp]
theorem staysPositive_nil : [] ∈ staysPositive :=
  fun _ hl hl₁ => (hl (List.eq_nil_of_suffix_nil hl₁)).elim

theorem staysPositive_suffix {l₁ l₂ : List ℤ} (hl₂ : l₂ ∈ staysPositive) (h : l₁ <:+ l₂) :
    l₁ ∈ staysPositive := fun l hne hl ↦ hl₂ l hne <| hl.trans h

theorem staysPositive_cons {x : ℤ} {l : List ℤ} :
    x::l ∈ staysPositive ↔ l ∈ staysPositive ∧ 0 < x + l.sum := by
  simp [staysPositive, List.suffix_cons_iff, or_imp, forall_and, @imp.swap _ (_ = _), and_comm]

theorem sum_nonneg_of_staysPositive : ∀ {l : List ℤ}, l ∈ staysPositive → 0 ≤ l.sum
  | [], _ => le_rfl
  | (_::_), h => (h _ (List.cons_ne_nil _ _) List.suffix_rfl).le

theorem staysPositive_cons_pos (x : ℤ) (hx : 0 < x) (l : List ℤ) :
    (x::l) ∈ staysPositive ↔ l ∈ staysPositive := by
  rw [staysPositive_cons, and_iff_left_iff_imp]
  intro h
  positivity [sum_nonneg_of_staysPositive h]

/-- `countedSequence p q` is the set of lists of integers for which every element is `+1` or `-1`,
there are `p` lots of `+1` and `q` lots of `-1`.

This represents vote sequences where candidate `+1` receives `p` votes and candidate `-1` receives
`q` votes.
-/
def countedSequence (p q : ℕ) : Set (List ℤ) :=
  {l | l.count 1 = p ∧ l.count (-1) = q ∧ ∀ x ∈ l, x = (1 : ℤ) ∨ x = -1}

open scoped List in
/-- An alternative definition of `countedSequence` that uses `List.Perm`. -/
theorem mem_countedSequence_iff_perm {p q l} :
    l ∈ countedSequence p q ↔ l ~ List.replicate p (1 : ℤ) ++ List.replicate q (-1) := by
  rw [List.perm_replicate_append_replicate]
  · simp only [countedSequence, List.subset_def, mem_ofPred_eq, List.mem_cons (b := (1 : ℤ)),
      List.mem_singleton]
  · norm_num1

@[simp]
theorem counted_right_zero (p : ℕ) : countedSequence p 0 = {List.replicate p 1} := by
  ext l; simp [mem_countedSequence_iff_perm]

@[simp]
theorem counted_left_zero (q : ℕ) : countedSequence 0 q = {List.replicate q (-1)} := by
  ext l; simp [mem_countedSequence_iff_perm]

theorem mem_of_mem_countedSequence {p q} {l} (hl : l ∈ countedSequence p q) {x : ℤ} (hx : x ∈ l) :
    x = 1 ∨ x = -1 :=
  hl.2.2 x hx

theorem length_of_mem_countedSequence {p q} {l : List ℤ} (hl : l ∈ countedSequence p q) :
    l.length = p + q := by simp [(mem_countedSequence_iff_perm.1 hl).length_eq]

theorem counted_eq_nil_iff {p q : ℕ} {l : List ℤ} (hl : l ∈ countedSequence p q) :
    l = [] ↔ p = 0 ∧ q = 0 :=
  List.length_eq_zero_iff.symm.trans <| by simp [length_of_mem_countedSequence hl]

theorem counted_ne_nil_left {p q : ℕ} (hp : p ≠ 0) {l : List ℤ} (hl : l ∈ countedSequence p q) :
    l ≠ [] := by simp [counted_eq_nil_iff hl, hp]

theorem counted_ne_nil_right {p q : ℕ} (hq : q ≠ 0) {l : List ℤ} (hl : l ∈ countedSequence p q) :
    l ≠ [] := by simp [counted_eq_nil_iff hl, hq]

theorem counted_succ_succ (p q : ℕ) :
    countedSequence (p + 1) (q + 1) =
      List.cons 1 '' countedSequence p (q + 1) ∪ List.cons (-1) '' countedSequence (p + 1) q := by
  ext l
  rw [countedSequence, countedSequence, countedSequence]
  constructor
  · intro hl
    have hlnil := counted_ne_nil_left (Nat.succ_ne_zero p) hl
    obtain ⟨hl₀, hl₁, hl₂⟩ := hl
    obtain hlast | hlast := hl₂ (l.head hlnil) (List.head_mem hlnil)
    · refine Or.inl ⟨l.tail, ⟨?_, ?_, ?_⟩, ?_⟩
      · rw [List.count_tail, hl₀, List.head?_eq_some_head hlnil, hlast, beq_self_eq_true,
          ite_eq_left rfl, Nat.add_sub_cancel]
      · rw [List.count_tail, hl₁, List.head?_eq_some_head hlnil, hlast, ite_eq_right (by decide),
          Nat.sub_zero]
      · exact fun x hx => hl₂ x (List.mem_of_mem_tail hx)
      · rw [← hlast, List.cons_head_tail]
    · refine Or.inr ⟨l.tail, ⟨?_, ?_, ?_⟩, ?_⟩
      · rw [List.count_tail, hl₀, List.head?_eq_some_head hlnil, hlast, ite_eq_right (by decide),
          Nat.sub_zero]
      · rw [List.count_tail, hl₁, List.head?_eq_some_head hlnil, hlast, beq_self_eq_true,
          ite_eq_left rfl, Nat.add_sub_cancel]
      · exact fun x hx => hl₂ x (List.mem_of_mem_tail hx)
      · rw [← hlast, List.cons_head_tail]
  · rintro (⟨t, ⟨ht₀, ht₁, ht₂⟩, rfl⟩ | ⟨t, ⟨ht₀, ht₁, ht₂⟩, rfl⟩)
    · refine ⟨?_, ?_, ?_⟩
      · rw [List.count_cons, beq_self_eq_true, ite_eq_left rfl, ht₀]
      · rw [List.count_cons, ite_eq_right, ht₁]
        norm_num
      · simpa
    · refine ⟨?_, ?_, ?_⟩
      · rw [List.count_cons, ite_eq_right, ht₀]
        norm_num
      · rw [List.count_cons, beq_self_eq_true, ite_eq_left rfl, ht₁]
      · simpa

theorem countedSequence_finite : ∀ p q : ℕ, (countedSequence p q).Finite
  | 0, q => by simp
  | p + 1, 0 => by simp
  | p + 1, q + 1 => by
    rw [counted_succ_succ, Set.finite_union, Set.finite_image_iff List.cons_injective.injOn,
      Set.finite_image_iff List.cons_injective.injOn]
    exact ⟨countedSequence_finite _ _, countedSequence_finite _ _⟩

theorem countedSequence_nonempty : ∀ p q : ℕ, (countedSequence p q).Nonempty
  | 0, q => by simp
  | p + 1, 0 => by simp
  | p + 1, q + 1 => by
    rw [counted_succ_succ, union_nonempty, image_nonempty]
    exact Or.inl (countedSequence_nonempty _ _)

theorem sum_of_mem_countedSequence {p q} {l : List ℤ} (hl : l ∈ countedSequence p q) :
    l.sum = p - q := by simp [(mem_countedSequence_iff_perm.1 hl).sum_eq, sub_eq_add_neg]

theorem disjoint_bits (p q : ℕ) :
    Disjoint (List.cons 1 '' countedSequence p (q + 1))
      (List.cons (-1) '' countedSequence (p + 1) q) := by
  simp_rw [disjoint_left, mem_image, not_exists, exists_imp]
  rintro _ _ ⟨_, rfl⟩ _ ⟨_, _, _⟩

open MeasureTheory.Measure

-- This instance needs to be public, for (public) theorem statements to make sense.
local instance sigmaAlgebra_list_int : SigmaAlgebra (List ℤ) := ⊤

private local instance measurableSingletonClass_list_int : MeasurableSingletonClass (List ℤ) :=
  { measurableSet_singleton := fun _ => trivial }

private theorem list_int_measurableSet {s : Set (List ℤ)} : MeasurableSet s := trivial

theorem count_countedSequence : ∀ p q : ℕ, count (countedSequence p q) = (p + q).choose p
  | p, 0 => by simp [counted_right_zero]
  | 0, q => by simp [counted_left_zero]
  | p + 1, q + 1 => by
    rw [counted_succ_succ, measure_union (disjoint_bits _ _) list_int_measurableSet,
      count_injective_image List.cons_injective, count_countedSequence _ _,
      count_injective_image List.cons_injective, count_countedSequence _ _]
    norm_cast
    rw [add_assoc, add_comm 1 q, ← Nat.choose_succ_succ, Nat.succ_eq_add_one, add_right_comm]

/-- The counting measure can be conditioned on the counted sequences. -/
theorem isConditionable_countedSequence (p q : ℕ) :
    IsConditionable count (countedSequence p q : Set (List ℤ)) :=
  .count_of_finite (countedSequence_finite p q) (countedSequence_nonempty p q)

theorem countedSequence_int_pos_counted_succ_succ (p q : ℕ) :
    countedSequence (p + 1) (q + 1) ∩ {l | l.headI = 1} =
      (countedSequence p (q + 1)).image (List.cons 1) := by
  rw [counted_succ_succ, union_inter_distrib_right,
      (_ : List.cons (-1) '' countedSequence (p + 1) q ∩ {l | l.headI = 1} = ∅), union_empty] <;>
    · ext
      simp only [mem_inter_iff, mem_image, mem_ofPred_eq, and_iff_left_iff_imp, mem_empty_iff_false,
        iff_false, not_and, forall_exists_index, and_imp]
      rintro y _ rfl
      norm_num

theorem countedSequence_int_neg_counted_succ_succ (p q : ℕ) :
    countedSequence (p + 1) (q + 1) ∩ {l | l.headI = 1}ᶜ =
      (countedSequence (p + 1) q).image (List.cons (-1)) := by
  rw [counted_succ_succ, union_inter_distrib_right,
      (_ : List.cons 1 '' countedSequence p (q + 1) ∩ {l : List ℤ | l.headI = 1}ᶜ = ∅),
      empty_union] <;>
    · ext
      simp only [mem_inter_iff, mem_image, and_iff_left_iff_imp, mem_empty_iff_false,
        iff_false, not_and, forall_exists_index, and_imp]
      rintro y _ rfl
      norm_num

/-- The counting measure can be conditioned on the counted sequences whose first vote is positive.
-/
theorem isConditionable_countedSequence_int_pos (p q : ℕ) :
    IsConditionable count (countedSequence (p + 1) (q + 1) ∩ {l | l.headI = 1}) := by
  rw [countedSequence_int_pos_counted_succ_succ]
  exact .count_of_finite ((countedSequence_finite _ _).image _)
    ((countedSequence_nonempty _ _).image _)

/-- The counting measure can be conditioned on the counted sequences whose first vote is negative.
-/
theorem isConditionable_countedSequence_int_neg (p q : ℕ) :
    IsConditionable count (countedSequence (p + 1) (q + 1) ∩ {l | l.headI = 1}ᶜ) := by
  rw [countedSequence_int_neg_counted_succ_succ]
  exact .count_of_finite ((countedSequence_finite _ _).image _)
    ((countedSequence_nonempty _ _).image _)

theorem ballot_total_isUnit (p q : ℕ) (h : 0 < p + q) : IsUnit ((p : ℝ≥0∞) + q) := by
  refine ENNReal.isUnit_iff.2 ⟨?_, by finiteness⟩
  exact_mod_cast h.ne'

theorem first_vote_pos :
    ∀ (p q : ℕ), 0 < p + q →
      uniformOn (countedSequence p q : Set (List ℤ)) (isConditionable_countedSequence p q)
        {l | l.headI = 1} = (p : ℝ≥0∞) / ((p : ℝ≥0∞) + q)
  | p + 1, 0, _ => by
    simp only [counted_right_zero]
    rw [uniformOn_singleton]
    simp [ENNReal.div_self, List.replicate_succ]
  | 0, q + 1, _ => by
    simp only [counted_left_zero]
    rw [uniformOn_singleton]
    simp [List.replicate]
  | p + 1, q + 1, _ => by
    rw [uniformOn, cond_apply (isConditionable_countedSequence _ _),
      countedSequence_int_pos_counted_succ_succ, count_injective_image List.cons_injective,
      count_countedSequence, count_countedSequence, Nat.cast_add, Nat.cast_one, mul_comm,
      ← ENNReal.div_eq_mul_inv, ENNReal.div_eq_div_iff]
    · norm_cast
      rw [mul_comm _ (p + 1), add_right_comm, Nat.add_one_mul_choose_eq, mul_comm]
    all_goals simp [(Nat.choose_pos <| le_add_of_nonneg_right zero_le).ne']

theorem headI_mem_of_nonempty {α : Type*} [Inhabited α] : ∀ {l : List α} (_ : l ≠ []), l.headI ∈ l
  | [], h => (h rfl).elim
  | _::_, _ => List.mem_cons_self

theorem first_vote_neg (p q : ℕ) (h : 0 < p + q) :
    uniformOn (countedSequence p q) (isConditionable_countedSequence p q) {l | l.headI = 1}ᶜ =
      (q : ℝ≥0∞) / ((p : ℝ≥0∞) + q) := by
  have h' : (p + q : ℝ≥0∞) ≠ 0 := mod_cast h.ne'
  have := uniformOn_compl {l : List ℤ | l.headI = 1}ᶜ (isConditionable_countedSequence p q)
  rw [compl_compl, first_vote_pos _ _ h] at this
  rw [ENNReal.eq_sub_of_add_eq _ this, ENNReal.eq_div_iff, ENNReal.mul_sub, mul_one,
    ENNReal.mul_div_cancel, ENNReal.add_sub_cancel_left]
  all_goals simp_all [ENNReal.div_eq_top]

theorem ballot_same (p : ℕ) :
    uniformOn (countedSequence (p + 1) (p + 1)) (isConditionable_countedSequence _ _)
      staysPositive = 0 := by
  rw [uniformOn_eq_zero_iff, eq_empty_iff_forall_notMem]
  rintro x ⟨hx, t⟩
  apply ne_of_gt (t x _ x.suffix_refl)
  · simpa using sum_of_mem_countedSequence hx
  · refine List.ne_nil_of_length_pos ?_
    rw [length_of_mem_countedSequence hx]
    exact Nat.add_pos_left (Nat.succ_pos _) _

theorem ballot_edge (p : ℕ) :
    uniformOn (countedSequence (p + 1) 0) (isConditionable_countedSequence _ _) staysPositive =
      1 := by
  refine uniformOn_eq_one_of _ ?_
  rw [counted_right_zero]
  refine singleton_subset_iff.2 fun l hl₁ hl₂ => List.sum_pos _ (fun x hx => ?_) hl₁
  rw [List.eq_of_mem_replicate (hl₂.mem hx)]
  norm_num

theorem ballot_pos (p q : ℕ) :
    uniformOn (countedSequence (p + 1) (q + 1) ∩ {l | l.headI = 1})
        (isConditionable_countedSequence_int_pos p q) staysPositive =
      uniformOn (countedSequence p (q + 1)) (isConditionable_countedSequence _ _)
        staysPositive := by
  rw [uniformOn, uniformOn, cond_apply (isConditionable_countedSequence_int_pos p q),
    cond_apply (isConditionable_countedSequence _ _), countedSequence_int_pos_counted_succ_succ,
    count_injective_image List.cons_injective]
  congr 1
  have : (1 :: ·) '' countedSequence p (q + 1) ∩ staysPositive =
      (1 :: ·) '' (countedSequence p (q + 1) ∩ staysPositive) := by
    simp only [image_inter List.cons_injective, Set.ext_iff, mem_inter_iff, and_congr_right_iff,
      forall_mem_image, List.cons_injective.mem_set_image, staysPositive_cons_pos _ one_pos]
    exact fun _ _ ↦ trivial
  rw [this, count_injective_image]
  exact List.cons_injective

theorem ballot_neg (p q : ℕ) (qp : q < p) :
    uniformOn (countedSequence (p + 1) (q + 1) ∩ {l | l.headI = 1}ᶜ)
        (isConditionable_countedSequence_int_neg p q) staysPositive =
      uniformOn (countedSequence (p + 1) q) (isConditionable_countedSequence _ _)
        staysPositive := by
  rw [uniformOn, uniformOn, cond_apply (isConditionable_countedSequence_int_neg p q),
    cond_apply (isConditionable_countedSequence _ _), countedSequence_int_neg_counted_succ_succ,
    count_injective_image List.cons_injective]
  congr 1
  have : List.cons (-1) '' countedSequence (p + 1) q ∩ staysPositive =
      List.cons (-1) '' (countedSequence (p + 1) q ∩ staysPositive) := by
    simp only [image_inter List.cons_injective, Set.ext_iff, mem_inter_iff, and_congr_right_iff,
      forall_mem_image, List.cons_injective.mem_set_image, staysPositive_cons, and_iff_left_iff_imp]
    intro l hl _
    simp [sum_of_mem_countedSequence hl, lt_sub_iff_add_lt', qp]
  rw [this, count_injective_image]
  exact List.cons_injective

/-- With no votes, the unique sequence satisfies the nonempty-suffix condition. -/
theorem ballot_empty :
    uniformOn (countedSequence 0 0) (isConditionable_countedSequence 0 0) staysPositive = 1 := by
  refine uniformOn_eq_one_of _ ?_
  rw [counted_right_zero]
  exact singleton_subset_iff.2 staysPositive_nil

private theorem ballot_den_unit (p q : ℕ) (h : 0 < p + q) : IsUnit ((p : ℝ) + q) := by
  apply isUnit_iff_ne_zero.2
  exact_mod_cast h.ne'

private theorem ballot_toReal_div (s : ℝ≥0∞) (p q : ℕ) (h : 0 < p + q) :
    (s / ((p : ℝ≥0∞) + q)).toReal =
      Checked.div s.toReal ((p : ℝ) + q) (ballot_den_unit p q h) := by
  have hd : ((p : ℝ≥0∞) + q).toReal = (p : ℝ) + q := by
    rw [← Nat.cast_add, ENNReal.toReal_natCast, Nat.cast_add]
  have hu : IsUnit (((p : ℝ≥0∞) + q).toReal) := hd.symm ▸ ballot_den_unit p q h
  rw [ENNReal.toReal_div _ _ (hb := hu)]
  exact div_eq_div_iff.mpr (congrArg (s.toReal * ·) hd.symm)

private theorem ballot_ratio_ind :
    ∀ q p : ℕ, q < p → ∀ u : IsUnit ((p : ℝ) + q),
      (uniformOn (countedSequence p q) (isConditionable_countedSequence p q)
        staysPositive).toReal = ((p : ℝ) - q) / ((p : ℝ) + q) := by
  apply Nat.diag_induction
  · intro p u
    rw [ballot_same]
    simp
  · intro p u
    simp only [ballot_edge, ENNReal.toReal_one, Nat.cast_zero, sub_zero, add_zero, div_self]
  · intro q p qp h₁ h₂ u
    have h₃ : 0 < p + 1 + (q + 1) := Nat.add_pos_left (Nat.succ_pos _) _
    have e₁ := h₁ (ballot_den_unit p (q + 1) (by omega))
    have e₂ := h₂ (ballot_den_unit (p + 1) q (by omega))
    rw [← uniformOn_add_compl_eq {l : List ℤ | l.headI = 1} _ (isConditionable_countedSequence _ _)
        (isConditionable_countedSequence_int_pos p q) (isConditionable_countedSequence_int_neg p q),
      first_vote_pos _ _ h₃, first_vote_neg _ _ h₃, ballot_pos, ballot_neg _ _ qp,
      ENNReal.toReal_add]
    · rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
        ballot_toReal_div (↑(p + 1)) _ _ h₃, ballot_toReal_div (↑(q + 1)) _ _ h₃, e₁, e₂]
      simp only [ENNReal.toReal_natCast]
      simp only [Nat.cast_add, Nat.cast_one]
      field
    all_goals
      exact ENNReal.mul_ne_top (by finiteness) (by simp [Ne, ENNReal.div_eq_top])

theorem ballot_problem' (q p : ℕ) (qp : q < p) :
    (uniformOn (countedSequence p q) (isConditionable_countedSequence p q) staysPositive).toReal =
      Checked.div ((p : ℝ) - q) ((p : ℝ) + q) (by
        apply isUnit_iff_ne_zero.2
        exact_mod_cast (show p + q ≠ 0 by omega)) :=
  ballot_ratio_ind q p qp (ballot_den_unit p q (by omega))

/-- The ballot problem. -/
theorem ballot_problem :
    ∀ (q p : ℕ), q < p →
      uniformOn (countedSequence p q) (isConditionable_countedSequence p q) staysPositive =
        ((p : ℝ≥0∞) - q) / ((p : ℝ≥0∞) + q) := by
  intro q p qp
  have hd : 0 < p + q := by omega
  have hs : ((p : ℝ≥0∞) - q).toReal = (p : ℝ) - q := by
    rw [ENNReal.toReal_sub_of_le, ENNReal.toReal_natCast, ENNReal.toReal_natCast]
    exacts [Nat.cast_le.2 qp.le, ENNReal.natCast_ne_top _]
  have he :
      (uniformOn (countedSequence p q) (isConditionable_countedSequence p q)
        staysPositive).toReal = (((p : ℝ≥0∞) - q) / ((p : ℝ≥0∞) + q)).toReal := by
    rw [ballot_toReal_div _ p q hd]
    simpa only [hs] using ballot_problem' q p qp
  have hzero : (p : ℝ≥0∞) + q ≠ 0 := by exact_mod_cast hd.ne'
  have hnum : (p : ℝ≥0∞) - q ≠ ⊤ :=
    (tsub_le_self.trans_lt (ENNReal.natCast_ne_top p).lt_top).ne
  exact (ENNReal.toReal_eq_toReal_iff' (measure_lt_top _ _).ne
    (ENNReal.div_ne_top hnum hzero)).mp he

end Ballot
