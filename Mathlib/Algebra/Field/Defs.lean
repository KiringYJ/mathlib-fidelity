/-
Copyright (c) 2014 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Leonardo de Moura, Johannes Hölzl, Mario Carneiro, Yaël Dillies
-/
module

public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Util.CheckedOperations

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
powers belong to `Units K`; they are not operations on the whole ambient carrier `K`.
Mixed division uses an ambient numerator and a unit denominator.

Rational casts and rational scalar multiplication require separate hypotheses on the
characteristic, or evidence that the denominator remains nonzero. They are not fields
of these structures.

A division ring or field is an example of a `GroupWithZero`. If you cannot find
a division ring / field lemma that does not involve `+`, you can try looking for
a `GroupWithZero` lemma instead.

## Tags

field, division ring, skew field, skew-field, skewfield
-/

@[expose] public section

assert_not_imported Mathlib.Tactic.Common

-- Checked operand elaboration uses `NeZero` evidence from the unit-construction API.

assert_not_exists MonoidHom

universe u

variable {K : Type*}

/-- A `DivisionSemiring` is a nontrivial semiring whose nonzero elements are units. -/
class DivisionSemiring (K : Type*) extends Semiring K, GroupWithZero K

attribute [instance 500] DivisionSemiring.toSemiring

/-- A `DivisionRing` is a nontrivial ring whose nonzero elements are units. -/
class DivisionRing (K : Type*) extends Ring K, GroupWithZero K

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
