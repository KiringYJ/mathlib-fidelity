/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Field.Opposite
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Data.Rat.Cast.CharZero

/-!
# \*-ring structure on `ℚ` and `ℚ≥0`.
-/

public section

instance Rat.instStarRing : StarRing ℚ := starRingOfComm
instance NNRat.instStarRing : StarRing ℚ≥0 := starRingOfComm
instance Rat.instTrivialStar : TrivialStar ℚ := ⟨fun _ ↦ rfl⟩
instance NNRat.instTrivialStar : TrivialStar ℚ≥0 := ⟨fun _ ↦ rfl⟩

variable {R : Type*}

open MulOpposite

/-- Star fixes any admissible nonnegative rational evaluation. -/
theorem star_nnratEval [DivisionSemiring R] [StarRing R] (q : ℚ≥0)
    (hd : (q.den : R) ≠ 0) : star (NNRat.eval q hd) = NNRat.eval q hd := by
  apply mul_right_cancel₀ hd
  rw [NNRat.eval_mul_den]
  have h := congrArg star (NNRat.eval_mul_den (α := R) q hd)
  simp only [star_mul, star_natCast] at h
  exact (Nat.cast_commute q.den (star (NNRat.eval q hd))).eq.symm.trans h

/-- Star fixes any admissible rational evaluation. -/
theorem star_ratEval [DivisionRing R] [StarRing R] (q : ℚ)
    (hd : (q.den : R) ≠ 0) : star (Rat.eval q hd) = Rat.eval q hd := by
  apply mul_right_cancel₀ hd
  rw [Rat.eval_mul_den]
  have h := congrArg star (Rat.eval_mul_den (α := R) q hd)
  simp only [star_mul, star_natCast, star_intCast] at h
  exact (Nat.cast_commute q.den (star (Rat.eval q hd))).eq.symm.trans h

@[simp, norm_cast]
lemma star_nnratCast [DivisionSemiring R] [CharZero R] [StarRing R] (q : ℚ≥0) :
    star (q : R) = q := by
  rw [NNRat.cast_eq_eval q (Nat.cast_ne_zero.mpr q.den_ne_zero)]
  exact star_nnratEval q _

@[simp, norm_cast]
theorem star_ratCast [DivisionRing R] [CharZero R] [StarRing R] (q : ℚ) :
    star (q : R) = q := by
  rw [Rat.cast_eq_eval q (Nat.cast_ne_zero.mpr q.den_nz)]
  exact star_ratEval q _
