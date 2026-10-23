/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yaël Dillies
-/
module

public import Mathlib.Data.Nat.Notation
public import Batteries.Classes.RatCast

/-!
# Basic definitions around the rational numbers

This file declares `ℚ` notation for the rationals and defines the nonnegative rationals `ℚ≥0`.

This file is eligible to upstreaming to Batteries.
-/

@[expose] public section

@[inherit_doc] notation "ℚ" => Rat

/-- Nonnegative rational numbers. -/
def NNRat := {q : ℚ // 0 ≤ q}

@[inherit_doc] notation "ℚ≥0" => NNRat

/-!
### Cast from `NNRat`

This section declares the notation class for a total embedding of `ℚ≥0`. The canonical
division-semiring instance is provided under characteristic zero in `Data.Rat.Cast.CharZero`.
-/

/-- Typeclass for the canonical homomorphism `ℚ≥0 → K`.

This is a notation typeclass. A division semiring alone does not supply this class:
a total rational embedding also requires its natural denominators to remain nonzero. -/
class NNRatCast (K : Type*) where
  /-- The canonical homomorphism `ℚ≥0 → K`.

  Do not use directly. Use the coercion instead. -/
  protected nnratCast : ℚ≥0 → K

instance NNRat.instNNRatCast : NNRatCast ℚ≥0 where nnratCast q := q

variable {K : Type*} [NNRatCast K]

/-- Cast a nonnegative rational using the supplied total rational embedding. -/
@[coe, reducible, match_pattern] protected def NNRat.cast : ℚ≥0 → K := NNRatCast.nnratCast

-- See note [coercion into rings]
instance NNRatCast.toCoeTail : CoeTail ℚ≥0 K where coe := NNRat.cast

-- See note [coercion into rings]
instance NNRatCast.toCoeHTCT : CoeHTCT ℚ≥0 K where coe := NNRat.cast

instance Rat.instNNRatCast : NNRatCast ℚ := ⟨Subtype.val⟩

/-! ### Numerator and denominator of a nonnegative rational -/

namespace NNRat

/-- The numerator of a nonnegative rational. -/
def num (q : ℚ≥0) : ℕ := (q : ℚ).num.natAbs

/-- The denominator of a nonnegative rational. -/
def den (q : ℚ≥0) : ℕ := (q : ℚ).den

@[simp] lemma num_mk (q : ℚ) (hq : 0 ≤ q) : num ⟨q, hq⟩ = q.num.natAbs := rfl
@[simp] lemma den_mk (q : ℚ) (hq : 0 ≤ q) : den ⟨q, hq⟩ = q.den := rfl

@[norm_cast] lemma cast_id (n : ℚ≥0) : NNRat.cast n = n := rfl
@[simp] lemma cast_eq_id : NNRat.cast = id := rfl

end NNRat

namespace Rat

/-- A fraction with an integer numerator and a nonzero natural denominator. -/
def fraction (n : Int) (d : ℕ) (hd : d ≠ 0) : ℚ := normalize n d hd

/-- A fraction with a nonzero integer denominator. Its sign is absorbed into the numerator. -/
def fractionInt (n d : Int) (hd : d ≠ 0) : ℚ :=
  normalize (d.sign * n) d.natAbs (Int.natAbs_ne_zero.mpr hd)

/-- The reciprocal of a nonzero rational, constructed directly from normalized integer data. -/
def reciprocal (q : ℚ) (hq : q ≠ 0) : ℚ :=
  fractionInt q.den q.num (fun h => hq (num_eq_zero.mp h))

/-- Divide an arbitrary rational by a nonzero rational. -/
def quotient (a b : ℚ) (hb : b ≠ 0) : ℚ := a * reciprocal b hb

@[simp] theorem mul_reciprocal (q : ℚ) (hq : q ≠ 0) : q * reciprocal q hq = 1 := by
  unfold reciprocal fractionInt
  conv => lhs; lhs; rw [← normalize_self q]
  rw [normalize_mul_normalize]
  change normalize _ _ _ = normalize 1 1 (by decide)
  rw [normalize_eq_iff]
  simp only [Int.natCast_one, Int.mul_one, Int.one_mul, Int.natCast_mul]
  rw [← Int.mul_assoc, Int.mul_sign_self, Int.mul_comm]

@[simp] theorem reciprocal_mul (q : ℚ) (hq : q ≠ 0) : reciprocal q hq * q = 1 := by
  rw [Rat.mul_comm, mul_reciprocal]

@[norm_cast] lemma cast_id (n : ℚ) : Rat.cast n = n := rfl
@[simp] lemma cast_eq_id : Rat.cast = id := rfl

end Rat

/-- `OfScientific.ofScientific` is the simp-normal form. -/
@[simp]
theorem Rat.ofScientific_eq_ofScientific (m : ℕ) (s : Bool) (e : ℕ) :
    Rat.ofScientific (OfNat.ofNat m) s (OfNat.ofNat e) = OfScientific.ofScientific m s e := rfl
