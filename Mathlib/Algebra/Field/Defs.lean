/-
Copyright (c) 2014 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Leonardo de Moura, Johannes Hölzl, Mario Carneiro, Yaël Dillies
-/
module

public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.GroupWithZero.Checked.Notation
public import Mathlib.Algebra.Ring.Defs

/-!
# Division (semi)rings and (semi)fields

This file introduces fields and division rings (also known as skewfields) and proves some basic
statements about them. For a more extensive theory of fields, see the `FieldTheory` folder.

## Main definitions

* `DivisionSemiring`: Nontrivial semiring with multiplicative inverses for nonzero elements.
* `DivisionRing`: Nontrivial ring with multiplicative inverses for nonzero elements.
* `Semifield`: Commutative division semiring.
* `Field`: Commutative division ring.
* `IsField`: Property that a given semiring is a field, defined in
  `Mathlib.Algebra.Field.IsField`.

## Implementation details

These structures assert that nonzero elements are units. Inversion, division and integer
powers are not operations on the whole ambient carrier `K`: the notation `a⁻¹`, `a / b` and
`a ^ n` for an integer `n` elaborates to the operations of
`Mathlib.Algebra.GroupWithZero.Checked`, which take evidence that the inverted element is a
unit (for an integer power, only when the exponent is negative). Mixed division uses an
ambient numerator and a unit denominator.

In characteristic zero every nonzero natural number is a unit, so every rational number `q`
has the value `q.num / q.den`. A division semiring records the embedding of `ℚ≥0` and its
scalar action as data guarded by a `CharZero` hypothesis; a division ring also records the
embedding of `ℚ` and its scalar action. The laws `q * q.den = q.num` and `q • a = q * a`
determine this data. A type overrides the default values only so that they agree
definitionally with a rational cast or scalar action that it already carries, as `ℚ` does.
The instances `DivisionSemiring.toNNRatCast`, `DivisionRing.toRatCast`,
`DivisionSemiring.toNNQSMul` and `DivisionRing.toQSMul` expose the data. In positive
characteristic a rational is evaluated only where its reduced denominator is nonzero
(`Mathlib.Data.Rat.Cast.Defs`).

A division ring or field is an example of a `GroupWithZero`. If you cannot find
a division ring / field lemma that does not involve `+`, you can try looking for
a `GroupWithZero` lemma instead.

## Tags

field, division ring, skew field, skew-field, skewfield
-/

@[expose] public section

assert_not_imported Mathlib.Tactic.Common

assert_not_exists MonoidHom

universe u

variable {K : Type*}

/-- A `DivisionSemiring` is a nontrivial semiring whose nonzero elements are units.

In characteristic zero it records the embedding of `ℚ≥0` and the scalar action of `ℚ≥0`. The
laws `nnratCastOfCharZero_mul_den` and `nnqsmulOfCharZero_eq_mul` determine both. -/
class DivisionSemiring (K : Type*) extends Semiring K, GroupWithZero K where
  /-- The embedding of `ℚ≥0` in characteristic zero. Use the coercion `(q : K)` instead. -/
  protected nnratCastOfCharZero : CharZero K → ℚ≥0 → K := fun _ q =>
    Checked.div (q.num : K) (q.den : K)
      (GroupWithZero.isUnit_of_ne_zero (Nat.cast_ne_zero.mpr (Rat.den_nz _)))
  /-- The embedding of `ℚ≥0` sends `q` to the quotient of its numerator by its denominator. -/
  protected nnratCastOfCharZero_mul_den (h : CharZero K) (q : ℚ≥0) :
      nnratCastOfCharZero h q * (q.den : K) = (q.num : K) := by
    intros; exact divp_mul_cancel ..
  /-- The action of `ℚ≥0` in characteristic zero. Use the notation `q • a` instead. -/
  protected nnqsmulOfCharZero : CharZero K → ℚ≥0 → K → K := fun h q a =>
    nnratCastOfCharZero h q * a
  /-- `ℚ≥0` acts by multiplication by the embedded scalar. -/
  protected nnqsmulOfCharZero_eq_mul (h : CharZero K) (q : ℚ≥0) (a : K) :
      nnqsmulOfCharZero h q a = nnratCastOfCharZero h q * a := by
    intros; rfl

attribute [instance 500] DivisionSemiring.toSemiring

/-- A `DivisionRing` is a nontrivial ring whose nonzero elements are units.

In characteristic zero it records the embeddings of `ℚ≥0` and `ℚ` and their scalar actions.
The laws `nnratCastOfCharZero_mul_den`, `ratCastOfCharZero_mul_den`, `nnqsmulOfCharZero_eq_mul`
and `qsmulOfCharZero_eq_mul` determine them. -/
class DivisionRing (K : Type*) extends Ring K, GroupWithZero K where
  /-- The embedding of `ℚ≥0` in characteristic zero. Use the coercion `(q : K)` instead. -/
  protected nnratCastOfCharZero : CharZero K → ℚ≥0 → K := fun _ q =>
    Checked.div (q.num : K) (q.den : K)
      (GroupWithZero.isUnit_of_ne_zero (Nat.cast_ne_zero.mpr (Rat.den_nz _)))
  /-- The embedding of `ℚ≥0` sends `q` to the quotient of its numerator by its denominator. -/
  protected nnratCastOfCharZero_mul_den (h : CharZero K) (q : ℚ≥0) :
      nnratCastOfCharZero h q * (q.den : K) = (q.num : K) := by
    intros; exact divp_mul_cancel ..
  /-- The action of `ℚ≥0` in characteristic zero. Use the notation `q • a` instead. -/
  protected nnqsmulOfCharZero : CharZero K → ℚ≥0 → K → K := fun h q a =>
    nnratCastOfCharZero h q * a
  /-- `ℚ≥0` acts by multiplication by the embedded scalar. -/
  protected nnqsmulOfCharZero_eq_mul (h : CharZero K) (q : ℚ≥0) (a : K) :
      nnqsmulOfCharZero h q a = nnratCastOfCharZero h q * a := by
    intros; rfl
  /-- The embedding of `ℚ` in characteristic zero. Use the coercion `(q : K)` instead. -/
  protected ratCastOfCharZero : CharZero K → ℚ → K := fun _ q =>
    Checked.div (q.num : K) (q.den : K)
      (GroupWithZero.isUnit_of_ne_zero (Nat.cast_ne_zero.mpr q.den_nz))
  /-- The embedding of `ℚ` sends `q` to the quotient of its numerator by its denominator. -/
  protected ratCastOfCharZero_mul_den (h : CharZero K) (q : ℚ) :
      ratCastOfCharZero h q * (q.den : K) = (q.num : K) := by
    intros; exact divp_mul_cancel ..
  /-- The action of `ℚ` in characteristic zero. Use the notation `q • a` instead. -/
  protected qsmulOfCharZero : CharZero K → ℚ → K → K := fun h q a => ratCastOfCharZero h q * a
  /-- `ℚ` acts by multiplication by the embedded scalar. -/
  protected qsmulOfCharZero_eq_mul (h : CharZero K) (q : ℚ) (a : K) :
      qsmulOfCharZero h q a = ratCastOfCharZero h q * a := by
    intros; rfl

-- see Note [lower instance priority]
instance (priority := 100) DivisionRing.toDivisionSemiring [DivisionRing K] : DivisionSemiring K :=
  { ‹DivisionRing K› with }

/-- A `Semifield` is a nontrivial commutative semiring whose nonzero elements are units. -/
class Semifield (K : Type*) extends CommSemiring K, DivisionSemiring K, CommGroupWithZero K

/-- A `Field` is a nontrivial commutative ring whose nonzero elements are units. -/
@[stacks 09FD "first part"]
class Field (K : Type u) extends CommRing K, DivisionRing K

-- see Note [lower instance priority]
instance (priority := 100) Field.toSemifield [Field K] : Semifield K := { ‹Field K› with }

/-! ### Rational embeddings in characteristic zero -/

/-- The embedding of `ℚ≥0` into a division semiring of characteristic zero. -/
instance (priority := 100) DivisionSemiring.toNNRatCast [DivisionSemiring K] [h : CharZero K] :
    NNRatCast K where
  nnratCast := DivisionSemiring.nnratCastOfCharZero h

/-- The action of `ℚ≥0` on a division semiring of characteristic zero. -/
instance (priority := 100) DivisionSemiring.toNNQSMul [DivisionSemiring K] [h : CharZero K] :
    SMul ℚ≥0 K where
  smul := DivisionSemiring.nnqsmulOfCharZero h

/-- The embedding of `ℚ` into a division ring of characteristic zero. -/
instance (priority := 100) DivisionRing.toRatCast [DivisionRing K] [h : CharZero K] :
    RatCast K where
  ratCast := DivisionRing.ratCastOfCharZero h

/-- The action of `ℚ` on a division ring of characteristic zero. -/
instance (priority := 100) DivisionRing.toQSMul [DivisionRing K] [h : CharZero K] : SMul ℚ K where
  smul := DivisionRing.qsmulOfCharZero h
