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
import Mathlib.Basic.ENNReal.Inv
import Mathlib.Data.Num.Basic
import Mathlib.SetTheory.Ordinal.Arithmetic

#guard Nat.euclideanDiv 7 3 = 2

example : Nat.euclideanDiv 17 5 (hb := by decide) = 3 := rfl
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

example (a b c : Nat) (hb : b ≠ 0) (hc : c ≠ 0) :
    Nat.euclideanDiv a (b * c) = Nat.euclideanDiv a (b * c) (Nat.mul_ne_zero hb hc) := rfl

example (a b c d : Int) (hb : b ≠ 0) (hc : c < 0) (hd : d ≠ 0) (h : b * c * d ∣ a) :
    Int.exactQuotient a (b * c * d) h =
      Int.exactQuotient a (b * c * d) h
        (Int.mul_ne_zero (Int.mul_ne_zero hb (Int.ne_of_lt hc)) hd) :=
  rfl

/--
error: could not synthesize default value for parameter 'hb' using tactics
---
error: a nonzero divisor proof is required
a b c : ℤ
hb : b ≠ 0
hc : c ≠ 0
⊢ b + c ≠ 0
-/
#guard_msgs in
example (a b c : Int) (hb : b ≠ 0) (hc : c ≠ 0) : Int := Int.euclideanDiv a (b + c)

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

section NativeQuotientPrinting

variable (a b : Nat) (hb : b ≠ 0)

/-- info: a.euclideanDiv b hb : ℕ -/
#guard_msgs in
#check Nat.euclideanDiv a b

/-- info: HDiv.hDiv a b : ℕ -/
#guard_msgs in
#check @HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) a b

end NativeQuotientPrinting

section IntegerQuotientPrinting

variable (a b : Int) (hb : b ≠ 0) (hd : b ∣ a)

/-- info: a.euclideanDiv b hb : ℤ -/
#guard_msgs in
#check Int.euclideanDiv a b

/-- info: a.exactQuotient b hd hb : ℤ -/
#guard_msgs in
#check Int.exactQuotient a b hd

/-- info: HDiv.hDiv a b : ℤ -/
#guard_msgs in
#check @HDiv.hDiv Int Int Int (@instHDiv Int Int.instDiv) a b

/-- info: ↑a / ↑b : ℚ -/
#guard_msgs in
#check (a : Rat) / (b : Rat)

end IntegerQuotientPrinting

section DivisionNotation

universe u

section Monoid

variable {M : Type u} [Monoid M] (a b : M) (hb : IsUnit b)

example : a / b = Checked.div a b hb := rfl

/-- info: a / b : M -/
#guard_msgs in
#check (a / b)

end Monoid

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

example : a / b = a := rfl

end Group

example {D : Type u} [Div D] (a b : D) : a / b = Div.div a b := rfl

example {A : Type*} {B : Type*} {C : Type*} [HDiv A B C] (a : A) (b : B) :
    (a / b : C) = HDiv.hDiv a b := rfl

section Heterogeneous

local instance : HDiv Bool String (List String) :=
  ⟨fun keep text => if keep then [text] else []⟩

example : true / "a" = ["a"] := rfl

end Heterogeneous

example {D : Type u} [DivisionRing D] (a b : D) (hb : b ≠ 0) : a / b * b = a :=
  div_mul_cancel₀ a

variable {R : Type u} [CommRing R] (a b : R) (hb : IsUnit b)

example : a / b = Checked.div a b hb := rfl
example (h₂ : IsUnit (2 : R)) : (3 / 2 : R) = Checked.div 3 2 h₂ := rfl

example (c d : R) (hd : IsUnit d) :
    (a * d - b * c) / (b * d) = Checked.div (a * d - b * c) (b * d) (hb.mul hd) := rfl

example (n : ℕ) (hn : IsUnit (n : R)) : a / (n : R) = Checked.div a (n : R) hn := rfl

/-- error: division notation is unavailable for Nat or Int operands -/
#guard_msgs in
noncomputable example (n : ℕ) : R := a / n

end DivisionNotation

section QuotientSets

open scoped Pointwise

example {D : Type*} [Div D] (x y : D) : ({x} : Set D) / {y} = {x / y} :=
  Set.singleton_div_singleton

example {D : Type*} [DecidableEq D] [Div D] (x y : D) :
    ({x} : Finset D) / {y} = {x / y} :=
  Finset.singleton_div_singleton x y

variable {G : Type*} [CommGroup G] (x : G)

example (s t : Set G) : x ∈ s / t ↔ ∃ a ∈ s, ∃ b ∈ t, a / b = x :=
  Set.mem_div

example [DecidableEq G] (s t : Finset G) : x ∈ s / t ↔ ∃ a ∈ s, ∃ b ∈ t, a / b = x :=
  Finset.mem_div

example (s t : Set G) : s / t = s * t⁻¹ := div_eq_mul_inv s t

example [DecidableEq G] (s t : Finset G) : s / t = s * t⁻¹ := div_eq_mul_inv s t

local instance : Div (Set G) := ⟨fun s _ => s⟩
local instance [DecidableEq G] : Div (Finset G) := ⟨fun s _ => s⟩

example (s t : Set G) : s / t = s := rfl
example [DecidableEq G] (s t : Finset G) : s / t = s := rfl

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

example (a : ENNReal) (ha : a ≠ 0) :
    ENNReal.extendedDiv a 0 ⟨Or.inl ha, Or.inr ENNReal.zero_ne_top⟩ = ⊤ := by
  simp [ENNReal.extendedDiv, ha]

example (a b : Ordinal) (hb : b ≠ 0) :
    b * Ordinal.quotient a b hb + a % b = a :=
  Ordinal.div_add_mod a b hb

example : Num.quotient (.pos (.bit1 (.bit1 .one))) (.pos (.bit1 .one)) (by decide) =
    Num.pos (.bit0 .one) := by decide

example : ZNum.quotient (.neg (.bit1 (.bit1 .one))) (.pos (.bit1 .one)) (by decide) =
    ZNum.neg (.bit1 .one) := by decide

#check_failure (fun (a b : Ordinal) (_hb : b ≠ 0) => (a / b : Ordinal))
#check_failure (fun (a b : Num) (_hb : b ≠ 0) => (a / b : Num))
#check_failure (fun (a b : ZNum) (_hb : b ≠ 0) => (a / b : ZNum))

/-- error: division notation is unavailable for Nat or Int operands -/
#guard_msgs in
noncomputable example : ℕ := (7 : ℕ) / 3

/-- error: division notation is unavailable for Nat or Int operands -/
#guard_msgs in
noncomputable example (a : ℕ) : ℕ := a / 1

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

/-- error: division notation is unavailable for Nat or Int operands -/
#guard_msgs in
noncomputable example (a : ℤ) : ℤ := a / 1

example : ((7 : ℤ) : ℚ) / ((3 : ℤ) : ℚ) = Rat.fractionInt 7 3 (by decide) :=
  (Rat.fractionInt_eq_div 7 3 (by decide)).symm

example : ((7 : ℕ) : ℚ) / ((3 : ℕ) : ℚ) = Rat.fraction 7 3 (by decide) :=
  (Rat.fraction_eq_div 7 3 (by decide)).symm

example (a : ℚ) : (3 / 2 + a : ℚ) = Checked.div 3 2 + a := rfl

/-- error: division notation is unavailable for Nat or Int operands -/
#guard_msgs in
noncomputable example : ℤ := (6 : ℤ) / (3 : ℤ)

/-- error: division notation is unavailable for Nat or Int operands -/
#guard_msgs in
noncomputable example (a : ℤ) (b : ℚ) : ℚ := a / b

section LocalNativeInstances

local instance : Div Nat := ⟨fun a _ => a⟩
local instance : HDiv Bool Int Bool := ⟨fun a _ => a⟩

/-- error: division notation is unavailable for Nat or Int operands -/
#guard_msgs in
example (a b : Nat) : Nat := 1 + (a / b)

/-- error: division notation is unavailable for Nat or Int operands -/
#guard_msgs in
def delayedNativeDivision := fun a b => (a / b, (a : Nat), (b : Nat))

/-- error: division notation is unavailable for Nat or Int operands -/
#guard_msgs in
example (b : Int) : Bool := true / b

end LocalNativeInstances

section NativeAliases

private def NaturalAlias : Type := Nat
private abbrev IntegerAlias : Type := Int

local instance : Div NaturalAlias := ⟨fun a _ => a⟩
local instance : Div IntegerAlias := ⟨fun a _ => a⟩

/-- error: division notation is unavailable for Nat or Int operands -/
#guard_msgs in
example (a b : NaturalAlias) : NaturalAlias := a / b

/-- error: division notation is unavailable for Nat or Int operands -/
#guard_msgs in
example (a b : IntegerAlias) : IntegerAlias := a / b

end NativeAliases

section DelayedOperandType

private def Indexed (native : Bool) : Type := if native then Nat else Bool

private def value {native : Bool} : Indexed native := by
  cases native
  · exact false
  · exact (7 : Nat)

local instance {native : Bool} : Div (Indexed native) := ⟨fun a _ => a⟩

example : Indexed true × Indexed true :=
  let a := value (native := _)
  (a, (show Indexed true from a))

/-- error: division notation is unavailable for Nat or Int operands -/
#guard_msgs in
example : Indexed true × Indexed true :=
  let a := value (native := _)
  (a / a, (show Indexed true from a))

end DelayedOperandType
