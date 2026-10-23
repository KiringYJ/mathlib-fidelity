/-
Copyright (c) 2014 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Leonardo de Moura, Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.Rat.Init
public import Mathlib.Algebra.Group.SelfInv
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Ring.GrindInstances
public import Mathlib.Algebra.Ring.Commute
public import Mathlib.Order.OrderDual
public import Mathlib.Order.Lex
public import Mathlib.Algebra.Order.Ring.Synonym

/-!
# Lemmas about division (semi)rings and (semi)fields

Fractions use unit denominators. Their generic additive identities are provided by
`Mathlib.Algebra.Ring.Units`; only characteristic-sensitive halves, field properties,
and structure transport remain here.

-/

public section

open Function OrderDual

universe u

variable {K L : Type*}

namespace Checked
section Ring
variable [Ring K]

@[simp] theorem inv_neg (a : K) (ha : IsUnit a) {hneg : IsUnit (-a)} :
    inv (-a) hneg = -inv a ha := by
  have hu : hneg.unit = -ha.unit := Units.ext rfl
  change (↑hneg.unit⁻¹ : K) = -(↑ha.unit⁻¹ : K)
  rw [hu, _root_.inv_neg, Units.val_neg]

@[simp] theorem neg_div (a b : K) (hb : IsUnit b) : div (-a) b hb = -div a b hb :=
  (Units.neg_divp a hb.unit).symm

@[simp] theorem div_neg (a b : K) (hb : IsUnit b) {hneg : IsUnit (-b)} :
    div a (-b) hneg = -div a b hb := by
  change a * inv (-b) hneg = -(a * inv b hb)
  rw [inv_neg b hb, mul_neg]

end Ring
end Checked

section DivisionSemiring

variable [DivisionSemiring K] [NeZero (2 : K)]

@[simp] lemma add_self_div_two (a : K) : Checked.div (a + a) 2 = a := by
  change (a + a) /ₚ Units.mk0 2 two_ne_zero = a
  rw [← mul_two]
  exact mul_divp_cancel a (Units.mk0 2 two_ne_zero)

@[simp] lemma add_halves (a : K) : Checked.div a 2 + Checked.div a 2 = a := by
  change a /ₚ Units.mk0 2 two_ne_zero + a /ₚ Units.mk0 2 two_ne_zero = a
  rw [Units.divp_add_divp_same]
  exact add_self_div_two a

end DivisionSemiring

section DivisionRing

variable [DivisionRing K]

-- see Note [lower instance priority]
instance (priority := 100) DivisionRing.isDomain : IsDomain K :=
  NoZeroDivisors.to_isDomain _

/-- The self-inverse units of a division ring are exactly `1` and `-1`. -/
theorem Units.isSelfInv_iff_eq_neg_one_or_eq_one (u : Kˣ) :
    IsSelfInv u ↔ u = -1 ∨ u = 1 := by
  rw [isSelfInv_iff, ← Units.val_inj, ← Units.mul_eq_one_iff_inv_eq,
    ← pow_two, sq_eq_one_iff, or_comm]
  simp only [Units.val_eq_neg_one, Units.val_eq_one]

variable [NeZero (2 : K)]

lemma sub_half (a : K) : a - Checked.div a 2 = Checked.div a 2 := by
  rw [sub_eq_iff_eq_add, add_halves]

lemma half_sub (a : K) : Checked.div a 2 - a = -(Checked.div a 2) := by
  rw [← neg_sub, sub_half]

end DivisionRing

section Field

variable [Field K]

-- see Note [lower instance priority]
instance (priority := 100) Field.isDomain : IsDomain K :=
  { DivisionRing.isDomain with }

end Field

section Constructors

variable {R : Type*} [Nontrivial R]

/-- Constructs a `DivisionRing` structure on a `Ring` consisting only of units and 0. -/
-- See note [reducible non-instances]
abbrev DivisionRing.ofIsUnitOrEqZero [Ring R] (h : ∀ a : R, IsUnit a ∨ a = 0) :
    DivisionRing R where
  toRing := ‹Ring R›
  __ := groupWithZeroOfIsUnitOrEqZero h

/-- Constructs a `Field` structure on a `CommRing` consisting only of units and 0. -/
-- See note [reducible non-instances]
abbrev Field.ofIsUnitOrEqZero [CommRing R] (h : ∀ a : R, IsUnit a ∨ a = 0) :
    Field R where
  toCommRing := ‹CommRing R›
  __ := DivisionRing.ofIsUnitOrEqZero h

end Constructors

namespace Function.Injective
variable [Zero K] [Add K] [Neg K] [Sub K] [One K] [Mul K] [SMul ℕ K] [SMul ℤ K]
  [Pow K ℕ] [NatCast K] [IntCast K] (f : K → L) (hf : Injective f)

/-- Pull back a division semiring along an injective map whose image is closed under inverses. -/
protected abbrev divisionSemiring [DivisionSemiring L] (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (natCast : ∀ n : ℕ, f n = n)
    (inverse_closed : ∀ a : K, f a ≠ 0 → ∃ b : K, f a * f b = 1 ∧ f b * f a = 1) :
    DivisionSemiring K where
  toSemiring := hf.semiring f zero one add mul nsmul npow natCast
  __ := hf.groupWithZero f zero one mul npow inverse_closed

/-- Pull back a division ring along an injective map whose image is closed under inverses. -/
protected abbrev divisionRing [DivisionRing L] (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (natCast : ∀ n : ℕ, f n = n) (intCast : ∀ n : ℤ, f n = n)
    (inverse_closed : ∀ a : K, f a ≠ 0 → ∃ b : K, f a * f b = 1 ∧ f b * f a = 1) :
    DivisionRing K where
  toRing := hf.ring f zero one add mul neg sub nsmul zsmul npow natCast intCast
  __ := hf.divisionSemiring f zero one add mul nsmul npow natCast inverse_closed

/-- Pull back a semifield along an injective map whose image is closed under inverses. -/
protected abbrev semifield [Semifield L] (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (natCast : ∀ n : ℕ, f n = n)
    (inverse_closed : ∀ a : K, f a ≠ 0 → ∃ b : K, f a * f b = 1 ∧ f b * f a = 1) :
    Semifield K where
  toCommSemiring := hf.commSemiring f zero one add mul nsmul npow natCast
  __ := hf.divisionSemiring f zero one add mul nsmul npow natCast inverse_closed

/-- Pull back a field along an injective map whose image is closed under inverses. -/
protected abbrev field [Field L] (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (natCast : ∀ n : ℕ, f n = n) (intCast : ∀ n : ℤ, f n = n)
    (inverse_closed : ∀ a : K, f a ≠ 0 → ∃ b : K, f a * f b = 1 ∧ f b * f a = 1) :
    Field K where
  toCommRing := hf.commRing f zero one add mul neg sub nsmul zsmul npow natCast intCast
  __ := hf.divisionRing f zero one add mul neg sub nsmul zsmul npow natCast intCast inverse_closed

end Function.Injective

/-! ### Order dual -/

namespace OrderDual

instance [RatCast K] : RatCast Kᵒᵈ := inferInstanceAs <| RatCast K
instance [NNRatCast K] : NNRatCast Kᵒᵈ := inferInstanceAs <| NNRatCast K
instance [DivisionSemiring K] : DivisionSemiring Kᵒᵈ := inferInstanceAs <| DivisionSemiring K
instance [DivisionRing K] : DivisionRing Kᵒᵈ := inferInstanceAs <| DivisionRing K
instance [Semifield K] : Semifield Kᵒᵈ := inferInstanceAs <| Semifield K
instance [Field K] : Field Kᵒᵈ := inferInstanceAs <| Field K

end OrderDual

@[simp] lemma toDual_ratCast [RatCast K] (n : ℚ) : toDual (n : K) = n := rfl

@[simp] lemma ofDual_ratCast [RatCast K] (n : ℚ) : (ofDual n : K) = n := rfl

/-! ### Lexicographic order -/

namespace Lex

instance [RatCast K] : RatCast (Lex K) := inferInstanceAs <| RatCast K
instance [DivisionSemiring K] : DivisionSemiring (Lex K) := inferInstanceAs <| DivisionSemiring K
instance [DivisionRing K] : DivisionRing (Lex K) := inferInstanceAs <| DivisionRing K
instance [Semifield K] : Semifield (Lex K) := inferInstanceAs <| Semifield K
instance [Field K] : Field (Lex K) := inferInstanceAs <| Field K

end Lex

@[simp] lemma toLex_ratCast [RatCast K] (n : ℚ) : toLex (n : K) = n := rfl

@[simp] lemma ofLex_ratCast [RatCast K] (n : ℚ) : (ofLex n : K) = n := rfl
