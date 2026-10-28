/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.GroupTheory.Abelianization.Finite
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Qify

/-!
# Commuting Probability

This file introduces the commuting probability of finite groups.

## Main definitions
* `commProb`: The commuting probability of a finite nonempty type with a multiplication operation.

## TODO
* Neumann's theorem.
-/

@[expose] public section

assert_not_exists Ideal TwoSidedIdeal

noncomputable section

open Fintype

variable (M : Type*) [Mul M] [Finite M] [Nonempty M]

/-- The commuting probability of a finite nonempty type with a multiplication operation: the
proportion of the pairs of elements that commute. -/
def commProb : ℚ :=
  Nat.card { p : M × M // Commute p.1 p.2 } / (Nat.card M : ℚ) ^ 2

theorem commProb_def :
    commProb M = Nat.card { p : M × M // Commute p.1 p.2 } / (Nat.card M : ℚ) ^ 2 :=
  rfl

theorem commProb_prod (M' : Type*) [Mul M'] [Finite M'] [Nonempty M'] :
    commProb (M × M') = commProb M * commProb M' := by
  simp_rw [commProb_def, div_mul_div_comm₀, Nat.card_prod, Nat.cast_mul, mul_pow, ← Nat.cast_mul,
    ← Nat.card_prod, Commute, SemiconjBy, Prod.ext_iff]
  congr 2
  exact Nat.card_congr ⟨fun x => ⟨⟨⟨x.1.1.1, x.1.2.1⟩, x.2.1⟩, ⟨⟨x.1.1.2, x.1.2.2⟩, x.2.2⟩⟩,
    fun x => ⟨⟨⟨x.1.1.1, x.2.1.1⟩, ⟨x.1.1.2, x.2.1.2⟩⟩, ⟨x.1.2, x.2.2⟩⟩, fun x => rfl, fun x => rfl⟩

theorem commProb_pi {α : Type*} (i : α → Type*) [Fintype α] [∀ a, Mul (i a)]
    [∀ a, Finite (i a)] [∀ a, Nonempty (i a)] :
    commProb (∀ a, i a) = ∏ a, commProb (i a) := by
  have hg (a : α) : IsUnit ((Nat.card (i a) : ℚ) ^ 2) :=
    (Nat.cast_ne_zero.mpr Finite.card_pos.ne').isUnit.pow 2
  simp_rw [commProb_def, Finset.prod_div_distrib₀ _ _ (hg := hg), Finset.prod_pow,
    ← Nat.cast_prod, ← Nat.card_pi, Commute, SemiconjBy, funext_iff]
  congr 2
  exact Nat.card_congr ⟨fun x a => ⟨⟨x.1.1 a, x.1.2 a⟩, x.2 a⟩, fun x => ⟨⟨fun a => (x a).1.1,
    fun a => (x a).1.2⟩, fun a => (x a).2⟩, fun x => rfl, fun x => rfl⟩

theorem commProb_function {α β : Type*} [Fintype α] [Mul β] [Finite β] [Nonempty β] :
    commProb (α → β) = (commProb β) ^ Fintype.card α := by
  rw [commProb_pi, Finset.prod_const, Finset.card_univ]

theorem commProb_pos : 0 < commProb M :=
  ‹Nonempty M›.elim fun x ↦
    div_pos (Nat.cast_pos.mpr (Finite.card_pos_iff.mpr ⟨⟨(x, x), rfl⟩⟩))
      (pow_pos (Nat.cast_pos.mpr Finite.card_pos) 2)

theorem commProb_le_one : commProb M ≤ 1 := by
  refine div_le_one_of_le₀ ?_ (sq_nonneg (Nat.card M : ℚ))
  norm_cast
  rw [sq, ← Nat.card_prod]
  apply Finite.card_subtype_le

variable {M}

theorem commProb_eq_one_iff : commProb M = 1 ↔ IsMulCommutative M := by
  classical
  have := Fintype.ofFinite M
  rw [commProb, div_eq_one_iff_eq, ← Set.coe_ofPred]
  simp only [Nat.card_eq_fintype_card]
  rw [← Nat.cast_pow, Nat.cast_inj, sq, ← card_prod, set_fintype_card_eq_univ_iff,
    Set.eq_univ_iff_forall]
  exact ⟨fun h ↦ ⟨⟨fun x y ↦ h (x, y)⟩⟩, fun h x ↦ mul_comm' ..⟩

theorem commProb_eq_one [IsMulCommutative M] : commProb M = 1 :=
  commProb_eq_one_iff.mpr ‹_›

variable (G : Type*) [Group G] [Finite G]

theorem commProb_def' : commProb G = Nat.card (ConjClasses G) / Nat.card G := by
  rw [commProb, card_comm_eq_card_conjClasses_mul_card, Nat.cast_mul]
  simp only [sq]
  exact mul_div_mul_right _ _

variable {G}
variable (H : Subgroup G)

theorem Subgroup.commProb_subgroup_le : commProb H ≤ commProb G * (H.index : ℚ) ^ 2 := by
  /- After rewriting with `commProb_def`, we reduce to showing that `G` has at least as many
      commuting pairs as `H`. -/
  rw [commProb_def, commProb_def, div_le_iff₀, mul_assoc, ← mul_pow, ← Nat.cast_mul,
    mul_comm H.index, H.card_mul_index, div_mul_cancel₀, Nat.cast_le]
  · refine Nat.card_le_card_of_injective (fun p ↦ ⟨⟨p.1.1, p.1.2⟩, Subtype.ext_iff.mp p.2⟩) ?_
    exact fun p q h ↦ by simpa only [Subtype.ext_iff, Prod.ext_iff] using h
  · exact pow_pos (Nat.cast_pos.mpr Finite.card_pos) 2

theorem Subgroup.commProb_quotient_le [H.Normal] : commProb (G ⧸ H) ≤ commProb G * Nat.card H := by
  /- After rewriting with `commProb_def'`, we reduce to showing that `G` has at least as many
      conjugacy classes as `G ⧸ H`. -/
  rw [commProb_def', commProb_def', div_le_iff₀, mul_assoc, ← Nat.cast_mul, ← Subgroup.index,
    H.card_mul_index, div_mul_cancel₀, Nat.cast_le]
  · apply Nat.card_le_card_of_surjective (f := ConjClasses.map (QuotientGroup.mk' H))
    exact ConjClasses.map_surjective Quotient.mk''_surjective
  · exact Nat.cast_pos.mpr Finite.card_pos

variable (G)

theorem inv_card_commutator_le_commProb : (↑(Nat.card (commutator G)))⁻¹ ≤ commProb G :=
  (inv_le_iff_one_le_mul₀ (Nat.cast_pos.mpr Finite.card_pos)).mpr
    (commProb_eq_one.ge.trans (commutator G).commProb_quotient_le)

-- Construction of group with commuting probability 1/n
namespace DihedralGroup

lemma commProb_odd {n : ℕ} [NeZero n] (hn : Odd n) :
    commProb (DihedralGroup n) = (n + 3) / (4 * n) := by
  have h2 : 2 ∣ n + 3 := by rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.odd_iff.mp hn]
  rw [commProb_def', DihedralGroup.card_conjClasses_odd hn, Nat.cast_div h2 two_ne_zero]
  simp only [nat_card]
  push_cast
  rw [div_div₀]
  congr 1
  ring

/-- A list of Dihedral groups whose product will have commuting probability `1 / n`, for
`n ≠ 0`. -/
def reciprocalFactors (n : ℕ) : List ℕ :=
  if _ : n = 0 then [0]
  else if _ : n = 1 then []
  else if Even n then
    3 :: reciprocalFactors (n / 2)
  else
    n % 4 * n :: reciprocalFactors (n / 4 + 1)

@[simp] lemma reciprocalFactors_zero : reciprocalFactors 0 = [0] := by
  unfold reciprocalFactors; rfl

@[simp] lemma reciprocalFactors_one : reciprocalFactors 1 = [] := by
  unfold reciprocalFactors; rfl

lemma reciprocalFactors_even {n : ℕ} (h0 : n ≠ 0) (h2 : Even n) :
    reciprocalFactors n = 3 :: reciprocalFactors (n / 2) := by
  have h1 : n ≠ 1 := by
    rintro rfl
    norm_num at h2
  rw [reciprocalFactors, dite_eq_right h0, dite_eq_right h1, ite_eq_left h2]

lemma reciprocalFactors_odd {n : ℕ} (h1 : n ≠ 1) (h2 : Odd n) :
    reciprocalFactors n = n % 4 * n :: reciprocalFactors (n / 4 + 1) := by
  have h0 : n ≠ 0 := by
    rintro rfl
    norm_num [← Nat.not_even_iff_odd] at h2
  rw [reciprocalFactors, dite_eq_right h0, dite_eq_right h1,
    ite_eq_right (Nat.not_even_iff_odd.2 h2)]

/-- A finite product of Dihedral groups. -/
abbrev Product (l : List ℕ) : Type :=
  ∀ i : Fin l.length, DihedralGroup l[i]

instance : Finite (Product []) :=
  inferInstanceAs (Finite (∀ i : Fin 0, DihedralGroup ([] : List ℕ)[i]))

/-- Adding a finite dihedral group to a finite product of dihedral groups gives a finite
product. -/
instance (n : ℕ) [NeZero n] (l : List ℕ) [Finite (Product l)] : Finite (Product (n :: l)) :=
  Finite.of_equiv (DihedralGroup n × Product l)
    (Fin.consEquiv fun i : Fin (l.length + 1) ↦ DihedralGroup (n :: l)[i])

/-- For `n ≠ 0`, the product of dihedral groups `Product (reciprocalFactors n)` is finite. -/
instance instFiniteProductReciprocalFactors (n : ℕ) [NeZero n] :
    Finite (Product (reciprocalFactors n)) := by
  by_cases h1 : n = 1
  · subst h1
    rw [reciprocalFactors_one]
    infer_instance
  rcases Nat.even_or_odd n with h2 | h2
  · have : NeZero (n / 2) := ⟨by have := NeZero.ne n; omega⟩
    have := instFiniteProductReciprocalFactors (n / 2)
    rw [reciprocalFactors_even (NeZero.ne n) h2]
    infer_instance
  · have : NeZero (n % 4 * n) :=
      ⟨Nat.mul_ne_zero (by have := Nat.odd_iff.mp h2; omega) (NeZero.ne n)⟩
    have : NeZero (n / 4 + 1) := ⟨by omega⟩
    have := instFiniteProductReciprocalFactors (n / 4 + 1)
    rw [reciprocalFactors_odd h1 h2]
    infer_instance
termination_by n
decreasing_by all_goals have := NeZero.ne n; omega

lemma commProb_nil : commProb (Product []) = 1 :=
  commProb_eq_one_iff.mpr ⟨⟨fun _ _ ↦ funext fun i ↦ Fin.elim0 i⟩⟩

/-- Rewrite the list of a product of dihedral groups inside `commProb`. -/
private lemma commProb_product_congr {l l' : List ℕ} (h : l = l') [Finite (Product l)]
    [Finite (Product l')] : commProb (Product l) = commProb (Product l') := by
  subst h
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma commProb_cons (n : ℕ) [NeZero n] (l : List ℕ) [Finite (Product l)] :
    commProb (Product (n :: l)) = commProb (DihedralGroup n) * commProb (Product l) := by
  have (i : Fin l.length) : Finite (DihedralGroup l[i]) :=
    Finite.of_surjective (fun f : Product l ↦ f i) (Function.surjective_eval i)
  have (i : Fin (n :: l).length) : Finite (DihedralGroup (n :: l)[i]) := by
    cases i using Fin.cases with
    | zero => exact inferInstanceAs (Finite (DihedralGroup n))
    | succ j => exact this j
  simp only [commProb_pi, Fin.prod_univ_succ, Fin.getElem_fin, Fin.val_succ, Fin.val_zero,
    List.getElem_cons_zero, List.length_cons, List.getElem_cons_succ]

/-- Construction of a group with commuting probability `1 / n`, for `n ≠ 0`. -/
theorem commProb_reciprocal (n : ℕ) [NeZero n] :
    commProb (Product (reciprocalFactors n)) = 1 / n := by
  have h0 : n ≠ 0 := NeZero.ne n
  by_cases h1 : n = 1
  · subst h1
    rw [commProb_product_congr reciprocalFactors_one, commProb_nil]
    simp
  rcases Nat.even_or_odd n with h2 | h2
  · have : NeZero (n / 2) := ⟨by omega⟩
    rw [commProb_product_congr (reciprocalFactors_even h0 h2), commProb_cons,
      commProb_reciprocal (n / 2), commProb_odd (by decide)]
    simp [field, h2.two_dvd]
    norm_num
  · have hn : Odd (n % 4) := by grind
    have : NeZero (n % 4 * n) := ⟨(hn.mul h2).pos.ne'⟩
    have : NeZero (n / 4 + 1) := ⟨by omega⟩
    rw [commProb_product_congr (reciprocalFactors_odd h1 h2), commProb_cons,
      commProb_reciprocal (n / 4 + 1), commProb_odd (hn.mul h2), div_mul_div_comm₀,
      div_eq_div_iff]
    norm_cast
    have h4 := Nat.div_add_mod n 4
    obtain hr | hr : n % 4 = 1 ∨ n % 4 = 3 := by have := Nat.odd_iff.mp h2; omega
    all_goals
      rw [hr] at h4 ⊢
      generalize n / 4 = q at h4 ⊢
      subst h4
      ring

end DihedralGroup
