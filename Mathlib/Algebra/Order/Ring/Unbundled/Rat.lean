/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Group.Unbundled.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Int
public import Mathlib.Data.Rat.Defs
public import Mathlib.Algebra.Ring.Int.Defs

/-!
# The rational numbers possess a linear order

This file constructs the order on `ℚ` and proves various facts relating the order to
ring structure on `ℚ`. This only uses unbundled type classes, e.g. `CovariantClass`,
relating the order structure and algebra structure on `ℚ`.
For the bundled `LinearOrderedCommRing` instance on `ℚ`, see `Algebra.Order.Ring.Rat`.

## Tags

rat, rationals, field, ℚ, numerator, denominator, num, denom, order, ordering
-/

@[expose] public section

assert_not_exists IsOrderedMonoid Field Finset Set.Icc GaloisConnection

namespace Rat

variable {a b c q : ℚ}

@[simp] lemma fraction_nonneg {a : ℤ} (ha : 0 ≤ a) (b : ℕ) (hb : b ≠ 0) :
    0 ≤ fraction a b hb := by
  apply Rat.num_nonneg.mp
  rw [fraction, Rat.num_normalize]
  exact Int.ediv_nonneg ha (Int.natCast_nonneg _)

theorem ofScientific_nonneg (m : ℕ) (s : Bool) (e : ℕ) : 0 ≤ Rat.ofScientific m s e := by
  rw [Rat.ofScientific]
  cases s
  · rw [ite_eq_right (by decide)]
    exact num_nonneg.mp <| Int.natCast_nonneg _
  · rw [ite_eq_left (by decide)]
    exact fraction_nonneg (Int.natCast_nonneg _) _ _

instance _root_.NNRatCast.toOfScientific {K} [NNRatCast K] : OfScientific K where
  ofScientific (m : ℕ) (b : Bool) (d : ℕ) :=
    NNRat.cast ⟨Rat.ofScientific m b d, ofScientific_nonneg m b d⟩

theorem _root_.NNRatCast.toOfScientific_def {K} [NNRatCast K] (m : ℕ) (b : Bool) (d : ℕ) :
    (OfScientific.ofScientific m b d : K) =
      NNRat.cast ⟨(OfScientific.ofScientific m b d : ℚ), ofScientific_nonneg m b d⟩ :=
  rfl

/-- Casting a scientific literal via `ℚ≥0` is the same as casting directly. -/
@[simp, norm_cast]
theorem _root_.NNRat.cast_ofScientific {K} [NNRatCast K] (m : ℕ) (s : Bool) (e : ℕ) :
    (OfScientific.ofScientific m s e : ℚ≥0) = (OfScientific.ofScientific m s e : K) :=
  rfl

protected lemma lt_iff_le_not_ge (a b : ℚ) : a < b ↔ a ≤ b ∧ ¬b ≤ a :=
  Std.LawfulOrderLT.lt_iff a b

instance linearOrder : LinearOrder ℚ where
  le_refl _ := Rat.le_refl
  le_trans _ _ _ := Rat.le_trans
  le_antisymm _ _ := Rat.le_antisymm
  le_total _ _ := Rat.le_total
  toDecidableEq := inferInstance
  toDecidableLE := inferInstance
  toDecidableLT := inferInstance
  lt_iff_le_not_ge := Rat.lt_iff_le_not_ge

theorem fraction_nonneg_iff (a : ℤ) (b : ℕ) (hb : b ≠ 0) :
    0 ≤ fraction a b hb ↔ 0 ≤ a := by
  rw [← Rat.num_nonneg]
  obtain ⟨g, hg, hn, _⟩ := Rat.normalize_num_den' a b hb
  have hgpos : 0 < (g : Int) := Int.natCast_pos.mpr (Nat.pos_of_ne_zero hg)
  simpa only [fraction, ← hn] using
    (Int.mul_nonneg_iff_of_pos_right (a := (normalize a b hb).num) hgpos).symm

@[simp] theorem fraction_eq_zero (a : ℤ) (b : ℕ) (hb : b ≠ 0) :
    fraction a b hb = 0 ↔ a = 0 := Rat.normalize_eq_zero hb

theorem fraction_pos_iff (a : ℤ) (b : ℕ) (hb : b ≠ 0) :
    0 < fraction a b hb ↔ 0 < a := by
  simp only [lt_iff_le_and_ne, ne_eq, eq_comm (a := (0 : ℚ)), eq_comm (a := (0 : ℤ)),
    fraction_eq_zero, fraction_nonneg_iff]

theorem fraction_pos {a : ℤ} (ha : 0 < a) (b : ℕ) (hb : b ≠ 0) :
    0 < fraction a b hb := (fraction_pos_iff a b hb).mpr ha

theorem fraction_nonpos_iff (a : ℤ) (b : ℕ) (hb : b ≠ 0) :
    fraction a b hb ≤ 0 ↔ a ≤ 0 := by
  rw [← not_lt, fraction_pos_iff, not_lt]

theorem fraction_nonpos {a : ℤ} (ha : a ≤ 0) (b : ℕ) (hb : b ≠ 0) :
    fraction a b hb ≤ 0 := (fraction_nonpos_iff a b hb).mpr ha

theorem fraction_neg_iff (a : ℤ) (b : ℕ) (hb : b ≠ 0) :
    fraction a b hb < 0 ↔ a < 0 := by
  rw [lt_iff_not_ge, fraction_nonneg_iff, ← lt_iff_not_ge]

theorem fraction_neg {a : ℤ} (ha : a < 0) (b : ℕ) (hb : b ≠ 0) :
    fraction a b hb < 0 := (fraction_neg_iff a b hb).mpr ha

/-!
### Extra instances to short-circuit type class resolution

These also prevent non-computable instances being used to construct these instances non-computably.
-/

instance instDistribLattice : DistribLattice ℚ := inferInstance
instance instLattice : Lattice ℚ := inferInstance
instance instSemilatticeInf : SemilatticeInf ℚ := inferInstance
instance instSemilatticeSup : SemilatticeSup ℚ := inferInstance
instance instInf : Min ℚ := inferInstance
instance instSup : Max ℚ := inferInstance
instance instPartialOrder : PartialOrder ℚ := inferInstance
instance instPreorder : Preorder ℚ := inferInstance

/-! ### Miscellaneous lemmas -/

instance : AddLeftMono ℚ where
  elim := fun _ _ _ h => Rat.add_le_add_left.2 h

@[simp] lemma num_nonpos {a : ℚ} : a.num ≤ 0 ↔ a ≤ 0 := by
  simp +instances [Int.le_iff_lt_or_eq, instLE, Rat.blt]
@[simp] lemma num_pos {a : ℚ} : 0 < a.num ↔ 0 < a := lt_iff_lt_of_le_iff_le num_nonpos
@[simp] lemma num_neg {a : ℚ} : a.num < 0 ↔ a < 0 := lt_iff_lt_of_le_iff_le num_nonneg

theorem num_le_denom_iff {q : ℚ} : q.num ≤ q.den ↔ q ≤ 1 := by simp [Rat.le_iff]

theorem num_lt_denom_iff {q : ℚ} : q.num < q.den ↔ q < 1 := by simp [Rat.lt_iff]

theorem abs_def (q : ℚ) : |q| = fraction q.num.natAbs q.den q.den_nz := by
  by_cases h : 0 ≤ q
  · rw [abs_of_nonneg h]
    simpa only [fraction, Int.natAbs_of_nonneg (Rat.num_nonneg.mpr h)] using
      (Rat.normalize_self q).symm
  · rw [abs_of_nonpos (le_of_not_ge h)]
    have hn : q.num ≤ 0 := Rat.num_nonpos.mpr (le_of_not_ge h)
    simpa only [fraction, Int.ofNat_natAbs_of_nonpos hn, Rat.neg_num, Rat.neg_den] using
      (Rat.normalize_self (-q)).symm

theorem abs_def' (q : ℚ) :
    |q| = ⟨|q.num|, q.den, q.den_ne_zero, q.num.abs_eq_natAbs ▸ q.reduced⟩ := by
  rw [abs_def]
  simpa only [fraction, Int.abs_eq_natAbs] using
    (Rat.mk_eq_normalize (num := q.num.natAbs) (den := q.den)
      (nz := q.den_ne_zero) (c := q.reduced)).symm

@[simp]
theorem num_abs_eq_abs_num (q : ℚ) : |q|.num = |q.num| := by
  rw [abs_def']

@[simp]
theorem den_abs_eq_den (q : ℚ) : |q|.den = q.den := by
  rw [abs_def']

end Rat
