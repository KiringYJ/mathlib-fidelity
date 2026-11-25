/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
module

public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Algebra.Order.Monoid.WithTop
public import Mathlib.Algebra.Regular.Basic


/-!
# Linearly ordered commutative additive groups and monoids with a top element adjoined

This file sets up a special class of linearly ordered commutative additive monoids
that show up as the target of so-called “valuations” in algebraic number theory.

Usually, in the informal literature, these objects are constructed
by taking a linearly ordered commutative additive group Γ and formally adjoining a
top element: `Γ ∪ {⊤}`.

The disadvantage is that a type such as `ENNReal` is not of that form,
whereas it is a very common target for valuations.
The classes distinguish ordered monoids with an absorbing top from those in which every
non-top element is an additive unit. The checked operations `Checked.neg`, `Checked.sub`, and
`Checked.zsmul` use additive units. Subtraction requires only the subtrahend to be a unit, and
integer scaling requires the element to be a unit only for negative scalars.
-/

public section

variable {G α : Type*}

namespace Checked

variable {M : Type*} [AddMonoid M] {a b c : M}

/-- The additive inverse of an element known to be an additive unit. -/
@[expose] noncomputable def neg (a : M) (ha : IsAddUnit a) : M :=
  ↑(-ha.addUnit)

/-- Subtract an additive unit from an arbitrary element of an additive monoid. -/
@[expose] noncomputable def sub (a b : M) (hb : IsAddUnit b) : M :=
  a + neg b hb

/-- Integer scaling of an element of an additive monoid. A negative scalar requires the element
to be an additive unit. -/
@[expose] noncomputable def zsmul (n : ℤ) (a : M) (ha : n < 0 → IsAddUnit a) : M :=
  match n with
  | .ofNat k => k • a
  | .negSucc k => (k + 1) • neg a (ha (Int.negSucc_lt_zero k))

@[simp] theorem neg_add_cancel (ha : IsAddUnit a) : neg a ha + a = 0 :=
  ha.val_neg_add

@[simp] theorem add_neg_cancel (ha : IsAddUnit a) : a + neg a ha = 0 :=
  ha.add_val_neg

theorem neg_eq_of_add_eq_zero (ha : IsAddUnit a) (h : a + b = 0) : neg a ha = b :=
  ha.isAddRegular.1 ((add_neg_cancel ha).trans h.symm)

theorem isAddUnit_neg (ha : IsAddUnit a) : IsAddUnit (neg a ha) :=
  (-ha.addUnit).isAddUnit

theorem sub_eq_add_neg (a : M) (hb : IsAddUnit b) : sub a b hb = a + neg b hb :=
  rfl

@[simp] theorem sub_add_cancel (a : M) (hb : IsAddUnit b) : sub a b hb + b = a := by
  rw [sub_eq_add_neg, add_assoc, neg_add_cancel, add_zero]

theorem sub_eq_iff_eq_add (hb : IsAddUnit b) : sub a b hb = c ↔ a = c + b := by
  constructor
  · intro h
    rw [← h, sub_add_cancel]
  · intro h
    rw [h, sub_eq_add_neg, add_assoc, add_neg_cancel, add_zero]

@[simp] theorem zsmul_ofNat (n : ℕ) (a : M) (ha : (n : ℤ) < 0 → IsAddUnit a) :
    zsmul (n : ℤ) a ha = n • a :=
  rfl

theorem zsmul_negSucc (n : ℕ) (a : M) (ha : Int.negSucc n < 0 → IsAddUnit a) :
    zsmul (Int.negSucc n) a ha = (n + 1) • neg a (ha (Int.negSucc_lt_zero n)) :=
  rfl

end Checked


/-- A linearly ordered commutative monoid with an additively absorbing `⊤` element.
  Instances should include number systems with an infinite element adjoined. -/
class LinearOrderedAddCommMonoidWithTop (α : Type*) extends
    AddCommMonoid α, LinearOrder α, IsOrderedAddMonoid α, OrderTop α where
  /-- In a `LinearOrderedAddCommMonoidWithTop`, the `⊤` element is invariant under addition. -/
  protected top_add' : ∀ x : α, ⊤ + x = ⊤
  protected isAddLeftRegular_of_ne_top ⦃x : α⦄ : x ≠ ⊤ → IsAddLeftRegular x

/-- A linearly ordered commutative additive monoid with an absorbing `⊤`, in which each
non-top element is an additive unit. -/
-- We do not extend `LinearOrderedAddCommMonoidWithTop` as that would bring in the unnecessary
-- `isAddLeftRegular_of_ne_top` field.
class LinearOrderedAddCommGroupWithTop (α : Type*)
    extends AddCommMonoid α, LinearOrder α, IsOrderedAddMonoid α, OrderTop α, Nontrivial α where
  /-- The top element is invariant under addition. -/
  protected top_add' (x : α) : ⊤ + x = ⊤
  /-- A finite element belongs to the group of additive units. -/
  protected isAddUnit_of_ne_top ⦃x : α⦄ : x ≠ ⊤ → IsAddUnit x

section LinearOrderedAddCommMonoidWithTop
variable [LinearOrderedAddCommMonoidWithTop α] {a b c : α}

@[simp]
theorem top_add (a : α) : ⊤ + a = ⊤ :=
  LinearOrderedAddCommMonoidWithTop.top_add' a

@[simp]
theorem add_top (a : α) : a + ⊤ = ⊤ :=
  Trans.trans (add_comm _ _) (top_add _)

@[simp] lemma IsAddRegular.of_ne_top (ha : a ≠ ⊤) : IsAddRegular a := by
  simpa using LinearOrderedAddCommMonoidWithTop.isAddLeftRegular_of_ne_top ha

lemma add_left_injective_of_ne_top (b : α) (h : b ≠ ⊤) : Function.Injective (fun x ↦ x + b) :=
  (IsAddRegular.of_ne_top h).2

lemma add_right_injective_of_ne_top (b : α) (h : b ≠ ⊤) : Function.Injective (fun x ↦ b + x) :=
  (IsAddRegular.of_ne_top h).1

@[simp]
lemma add_left_inj_of_ne_top (h : a ≠ ⊤) : b + a = c + a ↔ b = c :=
  (add_left_injective_of_ne_top _ h).eq_iff

@[simp]
lemma add_right_inj_of_ne_top (h : a ≠ ⊤) : a + b = a + c ↔ b = c :=
  (add_right_injective_of_ne_top _ h).eq_iff

lemma add_left_strictMono_of_ne_top (h : b ≠ ⊤) : StrictMono (fun x ↦ x + b) :=
  add_left_mono.strictMono_of_injective <| add_left_injective_of_ne_top _ h

lemma add_right_strictMono_of_ne_top (h : b ≠ ⊤) : StrictMono (fun x ↦ b + x) :=
  add_right_mono.strictMono_of_injective <| add_right_injective_of_ne_top _ h

@[simp]
lemma add_le_add_iff_left_of_ne_top (h : a ≠ ⊤) : b + a ≤ c + a ↔ b ≤ c :=
  (add_left_strictMono_of_ne_top h).le_iff_le

@[simp]
lemma add_le_add_iff_right_of_ne_top (h : a ≠ ⊤) : a + b ≤ a + c ↔ b ≤ c :=
  (add_right_strictMono_of_ne_top h).le_iff_le

@[simp]
lemma add_lt_add_iff_left_of_ne_top (h : a ≠ ⊤) : b + a < c + a ↔ b < c :=
  (add_left_strictMono_of_ne_top h).lt_iff_lt

@[simp]
lemma add_lt_add_iff_right_of_ne_top (h : a ≠ ⊤) : a + b < a + c ↔ b < c :=
  (add_right_strictMono_of_ne_top h).lt_iff_lt

end LinearOrderedAddCommMonoidWithTop

namespace LinearOrderedAddCommGroupWithTop

variable [LinearOrderedAddCommGroupWithTop α] {a b c : α}

@[simp] lemma top_ne_zero : (⊤ : α) ≠ 0 := by
  intro h
  obtain ⟨a, ha⟩ := exists_ne (0 : α)
  rw [← zero_add a] at ha
  simp [LinearOrderedAddCommGroupWithTop.top_add', -zero_add, ← h] at ha

@[simp] lemma zero_ne_top : 0 ≠ (⊤ : α) := top_ne_zero.symm

@[simp] lemma top_pos : (0 : α) < ⊤ := lt_top_iff_ne_top.2 top_ne_zero.symm

@[simp] lemma isAddUnit_iff : IsAddUnit a ↔ a ≠ ⊤ where
  mp := by rintro ⟨⟨b, c, hbc, -⟩, rfl⟩ rfl; simp [LinearOrderedAddCommGroupWithTop.top_add'] at hbc
  mpr ha := LinearOrderedAddCommGroupWithTop.isAddUnit_of_ne_top ha

instance : LinearOrderedAddCommMonoidWithTop α where
  top_add' := LinearOrderedAddCommGroupWithTop.top_add'
  isAddLeftRegular_of_ne_top _a ha := (isAddUnit_iff.2 ha).isAddRegular.1

lemma add_ne_top : a + b ≠ ⊤ ↔ a ≠ ⊤ ∧ b ≠ ⊤ := by simp [← isAddUnit_iff]

@[simp] lemma add_eq_top : a + b = ⊤ ↔ a = ⊤ ∨ b = ⊤ := by
  rw [← not_iff_not, not_or]; exact add_ne_top

@[simp] lemma add_lt_top : a + b < ⊤ ↔ a < ⊤ ∧ b < ⊤ := by simp [lt_top_iff_ne_top]

@[simp] lemma checked_sub_eq_top_iff (hb : IsAddUnit b) :
    Checked.sub a b hb = ⊤ ↔ a = ⊤ := by
  simp [Checked.sub_eq_add_neg, (isAddUnit_iff.mp (Checked.isAddUnit_neg hb))]

end LinearOrderedAddCommGroupWithTop

namespace WithTop

instance linearOrderedAddCommMonoidWithTop [AddCancelCommMonoid α] [LinearOrder α]
    [IsOrderedAddMonoid α] : LinearOrderedAddCommMonoidWithTop (WithTop α) where
  top_add' := WithTop.top_add
  isAddLeftRegular_of_ne_top _a ha _b _c := WithTop.add_left_cancel ha

variable [AddCommGroup G]

@[simp] theorem isAddUnit_coe (a : G) : IsAddUnit (a : WithTop G) :=
  .of_add_eq_zero (↑(-a) : WithTop G) (by rw [← coe_add, add_neg_cancel, coe_zero])

@[simp] theorem checked_neg_coe (a : G) (ha : IsAddUnit (a : WithTop G)) :
    Checked.neg (a : WithTop G) ha = (↑(-a) : WithTop G) := by
  apply Checked.neg_eq_of_add_eq_zero
  rw [← coe_add, add_neg_cancel, coe_zero]

@[simp] theorem checked_sub_coe (a b : G) (hb : IsAddUnit (b : WithTop G)) :
    Checked.sub (a : WithTop G) (b : WithTop G) hb = (↑(a - b) : WithTop G) := by
  rw [Checked.sub_eq_add_neg, checked_neg_coe, ← coe_add, sub_eq_add_neg]

@[simp] theorem checked_zsmul_coe (n : ℤ) (a : G) (ha : n < 0 → IsAddUnit (a : WithTop G)) :
    Checked.zsmul n (a : WithTop G) ha = (↑(n • a) : WithTop G) := by
  cases n with
  | ofNat n =>
    change n • (a : WithTop G) = (↑((n : ℤ) • a) : WithTop G)
    rw [natCast_zsmul, coe_nsmul]
  | negSucc n => rw [Checked.zsmul_negSucc, checked_neg_coe, ← coe_nsmul, negSucc_zsmul, neg_nsmul]

instance linearOrderedAddCommGroupWithTop [LinearOrder G] [IsOrderedAddMonoid G] :
    LinearOrderedAddCommGroupWithTop (WithTop G) where
  top_add' := WithTop.top_add
  isAddUnit_of_ne_top _ ha := by
    obtain ⟨a, rfl⟩ := WithTop.ne_top_iff_exists.mp ha
    exact WithTop.isAddUnit_coe a

end WithTop
