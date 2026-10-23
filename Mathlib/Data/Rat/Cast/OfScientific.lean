/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.Data.Rat.Cast.Lemmas

/-!
# Scientific literals from characteristic-zero rational casts

The imported cast instances interpret scientific literals through normalized rational
numbers, whose powers-of-ten denominators are nonzero in characteristic zero.

The official `Lean.Grind.LawfulOfScientific` class presupposes the core totalized
field structure. Installing that bridge for the fork's field hierarchy would reopen
ambient inverse and division through its parent instances, so this module exposes
the characteristic-zero cast interface directly.
-/
