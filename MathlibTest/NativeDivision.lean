/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
import Mathlib.Algebra.Algebra.Operations
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.Rat

#guard Nat.euclideanDiv 7 3 = 2
#guard Int.euclideanDiv (-7) 3 = -3
#guard Int.euclideanDiv (-7) (-3) = 3

#guard (7 : Nat) % 0 = 7
#guard (-7 : Int) % 0 = -7

#guard Int.exactQuotient 6 3 (by decide) = 2
#guard Int.exactQuotient 6 (-3) (by decide) = -2

example (a b : Int) (h : b ∣ a) (hb : b ≠ 0) : b * Int.exactQuotient a b h hb = a :=
  Int.mul_exactQuotient a b h hb

example (a b q : Int) (h : b ∣ a) (hb : b ≠ 0) (hq : b * q = a) :
    Int.exactQuotient a b h hb = q :=
  (Int.exactQuotient_eq_iff h hb).2 hq

/--
error: could not synthesize default value for parameter 'hb' using tactics
---
error: a nonzero divisor proof is required
⊢ 0 ≠ 0
-/
#guard_msgs in
example : Nat := Nat.euclideanDiv 7 0

/--
error: could not synthesize default value for parameter 'hb' using tactics
---
error: a nonzero divisor proof is required
⊢ 0 ≠ 0
-/
#guard_msgs in
example : Int := Int.euclideanDiv 7 0

/--
error: could not synthesize default value for parameter 'hb' using tactics
---
error: a nonzero divisor proof is required
⊢ 0 ≠ 0
-/
#guard_msgs in
example : Int := Int.exactQuotient 0 0 (by decide)

/--
error: Tactic `decide` proved that the proposition
  3 ∣ 7
is false
-/
#guard_msgs in
example : Int := Int.exactQuotient 7 3 (by decide)

section DivisionNotation

universe u

section CommMonoid

variable {M : Type u} [CommMonoid M] (a b : M) (hb : IsUnit b)

example : a / b = Checked.div a b hb := rfl

/-- info: a / b : M -/
#guard_msgs in
#check (a / b)

end CommMonoid

section ExplicitWitness

variable {M : Type u} [CommMonoid M] (a b : M) (h : Nonempty (PLift (IsUnit b)))

/-- info: Checked.div a b ⋯ : M -/
#guard_msgs in
#check Checked.div a b (h.elim fun w ↦ w.down)

#check_failure a / b

end ExplicitWitness

section Group

variable {G : Type u} [Group G] (a b : G)

example : a / b * b = a := div_mul_cancel a b

/-- info: a / b : G -/
#guard_msgs in
#check (a / b)

local instance : Div G := ⟨fun x _ => x⟩

example : a / b * b = a := div_mul_cancel a b

end Group

example {D : Type u} [DivisionRing D] (a b : D) (hb : b ≠ 0) : a / b * b = a :=
  div_mul_cancel₀ a

variable {R : Type u} [CommRing R] (a b : R) (hb : IsUnit b)

example : a / b = Checked.div a b hb := rfl
example (h₂ : IsUnit (2 : R)) : (3 / 2 : R) = Checked.div 3 2 h₂ := rfl

example (c d : R) (hd : IsUnit d) :
    (a * d - b * c) / (b * d) = Checked.div (a * d - b * c) (b * d) (hb.mul hd) := rfl

example (n : ℕ) (hn : IsUnit (n : R)) : a / (n : R) = Checked.div a (n : R) hn := rfl

/-- error: division requires operands of the same type, found R and ℕ -/
#guard_msgs in
noncomputable example (n : ℕ) : R := a / n

end DivisionNotation

section QuotientSets

open scoped Pointwise

variable {G : Type*} [CommGroup G] (x : G)

example (s t : Set G) : x ∈ s / t ↔ ∃ a ∈ s, ∃ b ∈ t, a / b = x :=
  Set.mem_div

example [DecidableEq G] (s t : Finset G) : x ∈ s / t ↔ ∃ a ∈ s, ∃ b ∈ t, a / b = x :=
  Finset.mem_div

local instance : Div G := ⟨fun a _ => a⟩

example (s t : Set G) : s / t = s * t⁻¹ := rfl

example [DecidableEq G] (s t : Finset G) : s / t = s * t⁻¹ := rfl

end QuotientSets

section IntervalDivision

variable {G : Type*} [Preorder G] [CommGroup G] [MulLeftMono G]

example (s t : NonemptyInterval G) : (s / t).fst = s.fst / t.snd := rfl

local instance : Div (Interval G) := instDivInterval

example (s : Interval G) : s / ⊥ = ⊥ := Interval.div_bot s

end IntervalDivision

section SubmoduleResidual

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]

example (I J K : Submodule R A) : K ≤ I / J ↔ K * J ≤ I := Submodule.le_div_iff_mul_le

local instance : Div (Submodule R A) := Submodule.instDiv

example (I : Submodule R A) : I / ⊥ = ⊤ := Submodule.div_bot I

end SubmoduleResidual

example (a : ℕ) : a / (1 : ℕ) = Checked.div a 1 := rfl

/--
error: could not synthesize default value for parameter 'hb' using tactics
---
error: an invertibility proof is required
⊢ IsUnit 3
-/
#guard_msgs in
noncomputable example : ℕ := (7 : ℕ) / 3

/-- error: division notation has no documented operation on M -/
#guard_msgs in
noncomputable example {M : Type} [Monoid M] (x y : M) (_hy : IsUnit y) : M := x / y

example (n : ℕ) : n % 3 < 3 := by omega
example (n : ℤ) : n % 3 < 3 := by omega

/--
error: failed to synthesize
  Div ℕ

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth Div ℕ

/--
error: failed to synthesize
  Div ℤ

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth Div ℤ

example (a : ℤ) : a / (1 : ℤ) = Checked.div a 1 := rfl

example : ((7 : ℤ) : ℚ) / ((3 : ℤ) : ℚ) = Rat.fractionInt 7 3 (by decide) :=
  (Rat.fractionInt_eq_div 7 3 (by decide)).symm

/--
error: could not synthesize default value for parameter 'hb' using tactics
---
error: an invertibility proof is required
⊢ IsUnit 3
-/
#guard_msgs in
noncomputable example : ℤ := (6 : ℤ) / (3 : ℤ)

/-- error: division requires operands of the same type, found ℤ and ℚ -/
#guard_msgs in
noncomputable example (a : ℤ) (b : ℚ) : ℚ := a / b
