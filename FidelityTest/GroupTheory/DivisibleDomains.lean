/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
import Mathlib.GroupTheory.Divisible

/-! Root and division choices require a nonzero index. -/

example {K : Type*} [DivisionRing K] [CharZero K] (q : K) (n : Int) (hn : n ≠ 0) :
    n • DivisibleBy.div q n hn = q := DivisibleBy.div_cancel q hn

example {A : Type*} [Group A] [RootableBy A Int] (a : A) :
    RootableBy.root a (-1) (by decide) ^ (-1 : Int) = a :=
  RootableBy.root_cancel a (by decide)

/--
error: Type mismatch
  DivisibleBy.div a 0
has type
  0 ≠ 0 → A
but is expected to have type
  A
-/
#guard_msgs in
example {A : Type} [AddMonoid A] [DivisibleBy A Nat] (a : A) : A :=
  DivisibleBy.div a 0

/--
error: Type mismatch
  RootableBy.root a 0
has type
  0 ≠ 0 → A
but is expected to have type
  A
-/
#guard_msgs in
example {A : Type} [Monoid A] [RootableBy A Nat] (a : A) : A :=
  RootableBy.root a 0
