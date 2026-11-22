/-
Copyright (c) 2014 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Leonardo de Moura, Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.SelfInv
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Order.Ring.Synonym
public import Mathlib.Algebra.Ring.Commute
public import Mathlib.Algebra.Ring.GrindInstances
public import Mathlib.Algebra.Ring.Invertible
public import Mathlib.Data.Rat.Init
public import Mathlib.Order.Lex
public import Mathlib.Order.OrderDual
import Mathlib.Tactic.Tauto

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

/-! ### Negation

Invertibility of `-a` and of `a` determine each other. The rules below extend `checked_unit`
accordingly, so that the evidence of a quotient by `-a` also supplies the evidence of a quotient
by `a`. -/

macro_rules | `(tactic| checked_unit) => `(tactic|
    solve
    | assumption
    | ((with_reducible apply IsUnit.neg); checked_unit)
    | (apply (IsUnit.neg_iff _).mp; assumption))

section HasDistribNeg
variable [Monoid K] [HasDistribNeg K] {a b : K}

@[simp] theorem inv_neg₀ {ha : IsUnit (-a)} : (-a)⁻¹ = -a⁻¹ := by
  have ha' : IsUnit a := (IsUnit.neg_iff a).mp ha
  refine inv_eq_of_mul_eq_one_right₀ ?_
  rw [neg_mul_neg, mul_inv_cancel₀]

theorem neg_inv₀ {ha : IsUnit a} : -a⁻¹ = (-a)⁻¹ := (inv_neg₀ (ha := ha.neg)).symm

theorem inv_neg_one₀ : (-1 : K)⁻¹ = -1 := by
  rw [inv_neg₀, inv_one₀]

theorem neg_div₀ (a b : K) {ha : IsUnit a} : Checked.div (-b) a = -(Checked.div b a) := by
  rw [div_eq_mul_inv₀, div_eq_mul_inv₀, neg_mul]

theorem neg_div₀' (a b : K) {ha : IsUnit a} :
    -(Checked.div b a) = Checked.div (-b) a := (neg_div₀ a b).symm

theorem div_neg_eq_neg_div₀ (a b : K) {ha : IsUnit (-a)} :
    Checked.div b (-a) = -(Checked.div b a) := by
  rw [div_eq_mul_inv₀, div_eq_mul_inv₀, inv_neg₀, mul_neg]

theorem div_neg₀ (a : K) {hb : IsUnit (-b)} :
    Checked.div a (-b) = -(Checked.div a b) := div_neg_eq_neg_div₀ b a

theorem div_neg_eq_neg_div₀' (a : K) {hb : IsUnit (-b)} :
    Checked.div a (-b) = Checked.div (-a) b := by
  rw [div_neg₀, neg_div₀]

theorem neg_div_neg_eq₀ (a b : K) {hb : IsUnit (-b)} : Checked.div (-a) (-b) = Checked.div a b := by
  rw [div_neg₀, neg_div₀, neg_neg]

theorem one_div_neg_one_eq_neg_one₀ : Checked.div (1 : K) (-1) = -1 := by
  rw [div_neg₀, div_one₀]

theorem one_div_neg_eq_neg_one_div₀ (a : K) {ha : IsUnit (-a)} :
    Checked.div 1 (-a) = -(Checked.div 1 a) :=
  div_neg₀ 1

end HasDistribNeg

/-! ### Fractions with common and distinct denominators -/

section Semiring
variable [Semiring K] {a b c d : K}

theorem add_div (a b c : K) {hc : IsUnit c} :
    Checked.div (a + b) c = Checked.div a c + Checked.div b c := by
  simp only [div_eq_mul_inv₀, add_mul]

theorem same_add_div {hb : IsUnit b} : Checked.div (b + a) b = 1 + Checked.div a b := by
  rw [add_div, div_self]

theorem div_add_same {hb : IsUnit b} : Checked.div (a + b) b = Checked.div a b + 1 := by
  rw [add_div, div_self]

theorem one_add_div {hb : IsUnit b} :
    1 + Checked.div a b = Checked.div (b + a) b := same_add_div.symm

theorem div_add_one {hb : IsUnit b} :
    Checked.div a b + 1 = Checked.div (a + b) b := div_add_same.symm

/-- See `inv_add_inv` for the more convenient version when `K` is commutative. -/
theorem inv_add_inv' {ha : IsUnit a} {hb : IsUnit b} :
    a⁻¹ + b⁻¹ = a⁻¹ * (a + b) * b⁻¹ := by
  rw [mul_add, add_mul, inv_mul_cancel₀, one_mul, mul_assoc, mul_inv_cancel₀, mul_one,
    add_comm]

theorem one_div_mul_add_mul_one_div_eq_one_div_add_one_div {ha : IsUnit a} {hb : IsUnit b} :
    Checked.div 1 a * (a + b) * Checked.div 1 b = Checked.div 1 a + Checked.div 1 b := by
  simp only [one_div₀]
  exact inv_add_inv'.symm

theorem add_div_eq_mul_add_div (a b : K) {hc : IsUnit c} :
    a + Checked.div b c = Checked.div (a * c + b) c :=
  eq_div_iff_mul_eq.2 <| by rw [add_mul, div_mul_cancel₀]

theorem add_div' (a b c : K) {hc : IsUnit c} : b + Checked.div a c = Checked.div (b * c + a) c := by
  rw [add_div, mul_div_cancel_right₀]

theorem div_add' (a b c : K) {hc : IsUnit c} : Checked.div a c + b = Checked.div (a + b * c) c := by
  rw [add_div, mul_div_cancel_right₀]

protected theorem Commute.div_add_div (hbc : Commute b c) (hbd : Commute b d) {hb : IsUnit b}
    {hd : IsUnit d} : Checked.div a b + Checked.div c d = Checked.div (a * d + b * c) (b * d) := by
  refine eq_div_iff_mul_eq.2 ?_
  rw [add_mul, ← mul_assoc, div_mul_cancel₀, hbd.eq, ← mul_assoc, div_mul_cancel₀, hbc.eq]

protected theorem Commute.one_div_add_one_div (hab : Commute a b) {ha : IsUnit a}
    {hb : IsUnit b} : Checked.div 1 a + Checked.div 1 b = Checked.div (a + b) (a * b) := by
  rw [(Commute.one_right a).div_add_div hab, one_mul, mul_one, add_comm]

protected theorem Commute.inv_add_inv (hab : Commute a b) {ha : IsUnit a} {hb : IsUnit b} :
    a⁻¹ + b⁻¹ = Checked.div (a + b) (a * b) := by
  rw [inv_eq_one_div₀ a, inv_eq_one_div₀ b, hab.one_div_add_one_div]

end Semiring

section DivisionSemiring

variable [DivisionSemiring K] [NeZero (2 : K)]

@[simp] lemma add_self_div_two (a : K) : Checked.div (a + a) 2 = a := by
  rw [← mul_two, mul_div_cancel_right₀]

@[simp] lemma add_halves (a : K) :
    Checked.div a 2 + Checked.div a 2 = a := by rw [← add_div, add_self_div_two]

end DivisionSemiring

section Ring
variable [Ring K] {a b c d : K}

@[simp] theorem div_neg_self {ha : IsUnit (-a)} : Checked.div a (-a) = -1 := by
  rw [div_neg₀, div_self]

@[simp] theorem neg_div_self {ha : IsUnit a} : Checked.div (-a) a = -1 := by
  rw [neg_div₀, div_self]

theorem div_sub_div_same (a b c : K) {hc : IsUnit c} :
    Checked.div a c - Checked.div b c = Checked.div (a - b) c := by
  simp only [div_eq_mul_inv₀, sub_mul]

theorem sub_div (a b c : K) {hc : IsUnit c} :
    Checked.div (a - b) c = Checked.div a c - Checked.div b c :=
  (div_sub_div_same _ _ _).symm

theorem same_sub_div {hb : IsUnit b} : Checked.div (b - a) b = 1 - Checked.div a b := by
  rw [sub_div, div_self]

theorem one_sub_div {hb : IsUnit b} :
    1 - Checked.div a b = Checked.div (b - a) b := same_sub_div.symm

theorem div_sub_same {hb : IsUnit b} : Checked.div (a - b) b = Checked.div a b - 1 := by
  rw [sub_div, div_self]

theorem div_sub_one {hb : IsUnit b} :
    Checked.div a b - 1 = Checked.div (a - b) b := div_sub_same.symm

/-- See `inv_sub_inv` for the more convenient version when `K` is commutative. -/
theorem inv_sub_inv' {ha : IsUnit a} {hb : IsUnit b} : a⁻¹ - b⁻¹ = a⁻¹ * (b - a) * b⁻¹ := by
  rw [mul_sub, sub_mul, inv_mul_cancel₀, one_mul, mul_assoc, mul_inv_cancel₀, mul_one]

theorem one_div_mul_sub_mul_one_div_eq_one_div_add_one_div {ha : IsUnit a} {hb : IsUnit b} :
    Checked.div 1 a * (b - a) * Checked.div 1 b = Checked.div 1 a - Checked.div 1 b := by
  simp only [one_div₀]
  exact inv_sub_inv'.symm

protected theorem Commute.div_sub_div (hbc : Commute b c) (hbd : Commute b d) {hb : IsUnit b}
    {hd : IsUnit d} : Checked.div a b - Checked.div c d = Checked.div (a * d - b * c) (b * d) := by
  refine eq_div_iff_mul_eq.2 ?_
  rw [sub_mul, ← mul_assoc, div_mul_cancel₀, hbd.eq, ← mul_assoc, div_mul_cancel₀, hbc.eq]

protected theorem Commute.inv_sub_inv (hab : Commute a b) {ha : IsUnit a} {hb : IsUnit b} :
    a⁻¹ - b⁻¹ = Checked.div (b - a) (a * b) := by
  simp only [inv_eq_one_div₀, (Commute.one_right a).div_sub_div hab, one_mul, mul_one]

theorem inv_eq_self₀ [NoZeroDivisors K] {ha : IsUnit a} : a⁻¹ = a ↔ a = -1 ∨ a = 1 := by
  rw [inv_eq_iff_eq_inv₀ (hb := ha), ← mul_eq_one_iff_eq_inv₀, ← pow_two, sq_eq_one_iff, or_comm]

theorem self_eq_inv₀ [NoZeroDivisors K] {ha : IsUnit a} : a = a⁻¹ ↔ a = -1 ∨ a = 1 := by
  rw [eq_comm, inv_eq_self₀]

end Ring

section CommSemiring
variable [CommSemiring K] {a b c d : K}

theorem div_add_div (a : K) (c : K) {hb : IsUnit b} {hd : IsUnit d} :
    Checked.div a b + Checked.div c d = Checked.div (a * d + b * c) (b * d) :=
  (Commute.all b _).div_add_div (Commute.all _ _)

theorem one_div_add_one_div {ha : IsUnit a} {hb : IsUnit b} :
    Checked.div 1 a + Checked.div 1 b = Checked.div (a + b) (a * b) :=
  (Commute.all a _).one_div_add_one_div

theorem inv_add_inv {ha : IsUnit a} {hb : IsUnit b} : a⁻¹ + b⁻¹ = Checked.div (a + b) (a * b) :=
  (Commute.all a _).inv_add_inv

end CommSemiring

section CommRing
variable [CommRing K] {a b c d : K}

theorem div_sub_div (a : K) {b : K} (c : K) {d : K} {hb : IsUnit b} {hd : IsUnit d} :
    a / b - c / d = (a * d - b * c) / (b * d) :=
  (Commute.all b _).div_sub_div (Commute.all _ _)

theorem inv_sub_inv {ha : IsUnit a} {hb : IsUnit b} : a⁻¹ - b⁻¹ = (b - a) / (a * b) :=
  (Commute.all a _).inv_sub_inv

theorem sub_div' {hc : IsUnit c} : b - a / c = (b * c - a) / c := by
  rw [eq_div_iff_mul_eq, sub_mul, div_mul_cancel₀]

theorem div_sub' {hc : IsUnit c} : a / c - b = (a - c * b) / c := by
  rw [eq_div_iff_mul_eq, sub_mul, div_mul_cancel₀, mul_comm c]

end CommRing

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
noncomputable abbrev DivisionRing.ofIsUnitOrEqZero [Ring R] (h : ∀ a : R, IsUnit a ∨ a = 0) :
    DivisionRing R where
  toRing := ‹Ring R›
  __ := groupWithZeroOfIsUnitOrEqZero h

/-- Constructs a `Field` structure on a `CommRing` consisting only of units and 0. -/
-- See note [reducible non-instances]
noncomputable abbrev Field.ofIsUnitOrEqZero [CommRing R] (h : ∀ a : R, IsUnit a ∨ a = 0) :
    Field R where
  toCommRing := ‹CommRing R›
  __ := DivisionRing.ofIsUnitOrEqZero h

end Constructors

namespace Function.Injective
variable [Zero K] [Add K] [Neg K] [Sub K] [One K] [Mul K] [SMul ℕ K] [SMul ℤ K]
  [Pow K ℕ] [NatCast K] [IntCast K] (f : K → L) (hf : Injective f)

/-- Pull back a division semiring along an injective map whose image is closed under inverses.
In characteristic zero, the embedding of `ℚ≥0` and its action are the given ones, which `f`
preserves. -/
protected abbrev divisionSemiring [DivisionSemiring L] [NNRatCast K] [SMul ℚ≥0 K]
    (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (natCast : ∀ n : ℕ, f n = n)
    (nnratCast : ∀ [CharZero L] (q : ℚ≥0), f q = q)
    (nnqsmul : ∀ [CharZero L] (q : ℚ≥0) (x : K), f (q • x) = q • f x)
    (inverse_closed : ∀ a : K, f a ≠ 0 → ∃ b : K, f a * f b = 1 ∧ f b * f a = 1) :
    DivisionSemiring K where
  toSemiring := hf.semiring f zero one add mul nsmul npow natCast
  __ := hf.groupWithZero f zero one mul npow inverse_closed
  nnratCastOfCharZero _ q := q
  nnratCastOfCharZero_mul_den h q := by
    have : CharZero L := ⟨fun m n hmn => h.cast_injective (hf (by rw [natCast, natCast, hmn]))⟩
    apply hf
    rw [mul, nnratCast, natCast, natCast]
    exact DivisionSemiring.nnratCastOfCharZero_mul_den _ q
  nnqsmulOfCharZero _ q x := q • x
  nnqsmulOfCharZero_eq_mul h q x := by
    have : CharZero L := ⟨fun m n hmn => h.cast_injective (hf (by rw [natCast, natCast, hmn]))⟩
    apply hf
    rw [nnqsmul, mul, nnratCast]
    exact DivisionSemiring.nnqsmulOfCharZero_eq_mul _ q (f x)

/-- Pull back a division ring along an injective map whose image is closed under inverses.
In characteristic zero, the embeddings of `ℚ≥0` and `ℚ` and their actions are the given ones,
which `f` preserves. -/
protected abbrev divisionRing [DivisionRing L] [NNRatCast K] [RatCast K] [SMul ℚ≥0 K] [SMul ℚ K]
    (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (natCast : ∀ n : ℕ, f n = n) (intCast : ∀ n : ℤ, f n = n)
    (nnratCast : ∀ [CharZero L] (q : ℚ≥0), f q = q) (ratCast : ∀ [CharZero L] (q : ℚ), f q = q)
    (nnqsmul : ∀ [CharZero L] (q : ℚ≥0) (x : K), f (q • x) = q • f x)
    (qsmul : ∀ [CharZero L] (q : ℚ) (x : K), f (q • x) = q • f x)
    (inverse_closed : ∀ a : K, f a ≠ 0 → ∃ b : K, f a * f b = 1 ∧ f b * f a = 1) :
    DivisionRing K where
  toRing := hf.ring f zero one add mul neg sub nsmul zsmul npow natCast intCast
  __ := hf.divisionSemiring f zero one add mul nsmul npow natCast nnratCast nnqsmul
    inverse_closed
  ratCastOfCharZero _ q := q
  ratCastOfCharZero_mul_den h q := by
    have : CharZero L := ⟨fun m n hmn => h.cast_injective (hf (by rw [natCast, natCast, hmn]))⟩
    apply hf
    rw [mul, ratCast, natCast, intCast]
    exact DivisionRing.ratCastOfCharZero_mul_den _ q
  qsmulOfCharZero _ q x := q • x
  qsmulOfCharZero_eq_mul h q x := by
    have : CharZero L := ⟨fun m n hmn => h.cast_injective (hf (by rw [natCast, natCast, hmn]))⟩
    apply hf
    rw [qsmul, mul, ratCast]
    exact DivisionRing.qsmulOfCharZero_eq_mul _ q (f x)

/-- Pull back a semifield along an injective map whose image is closed under inverses.
In characteristic zero, the embedding of `ℚ≥0` and its action are the given ones, which `f`
preserves. -/
protected abbrev semifield [Semifield L] [NNRatCast K] [SMul ℚ≥0 K]
    (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (natCast : ∀ n : ℕ, f n = n)
    (nnratCast : ∀ [CharZero L] (q : ℚ≥0), f q = q)
    (nnqsmul : ∀ [CharZero L] (q : ℚ≥0) (x : K), f (q • x) = q • f x)
    (inverse_closed : ∀ a : K, f a ≠ 0 → ∃ b : K, f a * f b = 1 ∧ f b * f a = 1) :
    Semifield K where
  toCommSemiring := hf.commSemiring f zero one add mul nsmul npow natCast
  __ := hf.divisionSemiring f zero one add mul nsmul npow natCast nnratCast nnqsmul
    inverse_closed

/-- Pull back a field along an injective map whose image is closed under inverses.
In characteristic zero, the embeddings of `ℚ≥0` and `ℚ` and their actions are the given ones,
which `f` preserves. -/
protected abbrev field [Field L] [NNRatCast K] [RatCast K] [SMul ℚ≥0 K] [SMul ℚ K]
    (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (natCast : ∀ n : ℕ, f n = n) (intCast : ∀ n : ℤ, f n = n)
    (nnratCast : ∀ [CharZero L] (q : ℚ≥0), f q = q) (ratCast : ∀ [CharZero L] (q : ℚ), f q = q)
    (nnqsmul : ∀ [CharZero L] (q : ℚ≥0) (x : K), f (q • x) = q • f x)
    (qsmul : ∀ [CharZero L] (q : ℚ) (x : K), f (q • x) = q • f x)
    (inverse_closed : ∀ a : K, f a ≠ 0 → ∃ b : K, f a * f b = 1 ∧ f b * f a = 1) :
    Field K where
  toCommRing := hf.commRing f zero one add mul neg sub nsmul zsmul npow natCast intCast
  __ := hf.divisionRing f zero one add mul neg sub nsmul zsmul npow natCast intCast nnratCast
    ratCast nnqsmul qsmul inverse_closed

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
