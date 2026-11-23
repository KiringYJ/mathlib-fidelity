/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.Module.Defs
public import Mathlib.Algebra.Order.Sub.Basic
public import Mathlib.Data.Finsupp.SMulWithZero
public import Mathlib.Lean.Elab.NativeDivision
public import Mathlib.Order.Preorder.Finsupp

/-!
# Flooring, ceiling division

This file defines division rounded up and down.

The setup is an ordered monoid `α` acting on an ordered monoid `β`. If `0 < a` in `α` and `b : β`,
we would like to "divide" `b` by `a`, namely find `c : β` such that `a • c = b`.
This is of course not always possible, but in some cases at least there is a least `c` such that
`b ≤ a • c` and a greatest `c` such that `a • c ≤ b`. We call the first one the "ceiling division
of `b` by `a`" and the second one the "flooring division of `b` by `a`"

If `α` and `β` are both `ℕ`, then one can check that our flooring and ceiling divisions really are
the floor and ceil of the exact division.
If `α` is `ℕ` and `β` is the functions `ι → ℕ`, then the flooring and ceiling divisions are taken
pointwise.

In order theory terms, those operations are respectively the right and left adjoints to the map
`b ↦ a • b`.

## Main declarations

* `FloorDiv`: Typeclass for the existence of a flooring division, denoted `b ⌊/⌋ a`.
* `CeilDiv`: Typeclass for the existence of a ceiling division, denoted `b ⌈/⌉ a`.

Both operations require a positive denominator. When positive scalar multiplication reflects
the order, the adjunctions imply that dividing zero gives zero.

## Notation

* `b ⌊/⌋ a` for the flooring division of `b` by `a`
* `b ⌈/⌉ a` for the ceiling division of `b` by `a`

## TODO

* `norm_num` extension
* Relate `a ⌈/⌉ b` to the ceiling of the rational ratio of `a` and `b` for positive `b : ℕ`.
-/

public section

variable {ι α β : Type*}

section OrderedAddCommMonoid
variable (α β) [AddCommMonoid α] [PartialOrder α] [AddCommMonoid β] [PartialOrder β]
  [SMulZeroClass α β]

/-- Typeclass for division rounded down. For each `a > 0`, this asserts the existence of a right
adjoint to the map `b ↦ a • b : β → β`. -/
class FloorDiv where
  /-- Flooring division. If `a > 0`, then `b ⌊/⌋ a` is the greatest `c` such that `a • c ≤ b`. -/
  floorDiv (b : β) (a : α) (ha : 0 < a := by first | assumption | exact zero_lt_one' _ | decide) : β
  /-- Do not use this. Use `gc_floorDiv_smul` or `gc_floorDiv_mul` instead. -/
  protected floorDiv_gc ⦃a⦄ (ha : 0 < a) : GaloisConnection (a • ·) (floorDiv · a ha)

/-- Typeclass for division rounded up. For each `a > 0`, this asserts the existence of a left
adjoint to the map `b ↦ a • b : β → β`. -/
class CeilDiv where
  /-- Ceiling division. If `a > 0`, then `b ⌈/⌉ a` is the least `c` such that `b ≤ a • c`. -/
  ceilDiv (b : β) (a : α) (ha : 0 < a := by first | assumption | exact zero_lt_one' _ | decide) : β
  /-- Do not use this. Use `gc_smul_ceilDiv` or `gc_mul_ceilDiv` instead. -/
  protected ceilDiv_gc ⦃a⦄ (ha : 0 < a) : GaloisConnection (ceilDiv · a ha) (a • ·)

@[inherit_doc] infixl:70 " ⌊/⌋ " => FloorDiv.floorDiv
@[inherit_doc] infixl:70 " ⌈/⌉ " => CeilDiv.ceilDiv

variable {α β}

section FloorDiv
variable [FloorDiv α β] {a : α} {b c : β}

lemma gc_floorDiv_smul (ha : 0 < a) : GaloisConnection (a • · : β → β) (· ⌊/⌋ a) :=
  FloorDiv.floorDiv_gc ha

@[simp] lemma le_floorDiv_iff_smul_le (ha : 0 < a) : c ≤ b ⌊/⌋ a ↔ a • c ≤ b :=
  (gc_floorDiv_smul ha _ _).symm

@[simp] lemma zero_floorDiv [PosSMulReflectLE α β] (a : α) (ha : 0 < a) :
    (0 : β) ⌊/⌋ a = 0 :=
  le_antisymm
    (le_of_smul_le_smul_left (by
      simpa only [smul_zero] using (gc_floorDiv_smul (β := β) ha).l_u_le 0) ha)
    ((le_floorDiv_iff_smul_le ha).2 (by simp))

lemma smul_floorDiv_le (ha : 0 < a) : a • (b ⌊/⌋ a) ≤ b := (le_floorDiv_iff_smul_le ha).1 le_rfl

end FloorDiv

section CeilDiv
variable [CeilDiv α β] {a : α} {b c : β}

lemma gc_smul_ceilDiv (ha : 0 < a) : GaloisConnection (· ⌈/⌉ a) (a • · : β → β) :=
  CeilDiv.ceilDiv_gc ha

@[simp]
lemma ceilDiv_le_iff_le_smul (ha : 0 < a) : b ⌈/⌉ a ≤ c ↔ b ≤ a • c := gc_smul_ceilDiv ha _ _

@[simp] lemma zero_ceilDiv [PosSMulReflectLE α β] (a : α) (ha : 0 < a) :
    (0 : β) ⌈/⌉ a = 0 :=
  le_antisymm ((ceilDiv_le_iff_le_smul ha).2 (by simp))
    (le_of_smul_le_smul_left (by simpa only [smul_zero] using
      (gc_smul_ceilDiv (β := β) ha).le_u_l 0) ha)

lemma le_smul_ceilDiv (ha : 0 < a) : b ≤ a • (b ⌈/⌉ a) := (ceilDiv_le_iff_le_smul ha).1 le_rfl

end CeilDiv
end OrderedAddCommMonoid

section
variable [AddCommMonoid α] [PartialOrder α] [AddCommMonoid β] [PartialOrder β] [SMulZeroClass α β]
  [PosSMulReflectLE α β] [FloorDiv α β] [CeilDiv α β] {a : α} {b : β}

lemma floorDiv_le_ceilDiv (ha : 0 < a) : b ⌊/⌋ a ≤ b ⌈/⌉ a :=
  le_of_smul_le_smul_left ((smul_floorDiv_le ha).trans <| le_smul_ceilDiv ha) ha

end

section OrderedSemiring
variable [Semiring α] [PartialOrder α] [AddCommMonoid β] [PartialOrder β] [MulActionWithZero α β]

section FloorDiv
variable [FloorDiv α β] {a : α}

@[simp] lemma floorDiv_one [IsOrderedRing α] [Nontrivial α] (b : β) : b ⌊/⌋ (1 : α) = b :=
  eq_of_forall_le_iff <| fun c ↦ by simp

@[simp] lemma smul_floorDiv [PosSMulMono α β] [PosSMulReflectLE α β] (ha : 0 < a) (b : β) :
    a • b ⌊/⌋ a = b :=
  eq_of_forall_le_iff <| by simp [smul_le_smul_iff_of_pos_left, ha]

end FloorDiv

section CeilDiv
variable [CeilDiv α β] {a : α}

@[simp] lemma ceilDiv_one [IsOrderedRing α] [Nontrivial α] (b : β) : b ⌈/⌉ (1 : α) = b :=
  eq_of_forall_ge_iff <| fun c ↦ by simp

@[simp] lemma smul_ceilDiv [PosSMulMono α β] [PosSMulReflectLE α β] (ha : 0 < a) (b : β) :
    a • b ⌈/⌉ a = b :=
  eq_of_forall_ge_iff <| by simp [smul_le_smul_iff_of_pos_left, ha]

end CeilDiv

section FloorDiv
variable [FloorDiv α α] {a b c : α}

lemma gc_floorDiv_mul (ha : 0 < a) : GaloisConnection (a * ·) (· ⌊/⌋ a) := gc_floorDiv_smul ha
lemma le_floorDiv_iff_mul_le (ha : 0 < a) : c ≤ b ⌊/⌋ a ↔ a • c ≤ b := le_floorDiv_iff_smul_le ha

end FloorDiv

section CeilDiv
variable [CeilDiv α α] {a b c : α}

lemma gc_mul_ceilDiv (ha : 0 < a) : GaloisConnection (· ⌈/⌉ a) (a * ·) := gc_smul_ceilDiv ha
lemma ceilDiv_le_iff_le_mul (ha : 0 < a) : b ⌈/⌉ a ≤ c ↔ b ≤ a * c := ceilDiv_le_iff_le_smul ha

end CeilDiv
end OrderedSemiring

namespace Nat

instance instFloorDiv : FloorDiv ℕ ℕ where
  floorDiv b a ha := Nat.euclideanDiv b a ha.ne'
  floorDiv_gc a ha x y := by
    simpa only [smul_eq_mul, Nat.mul_comm] using
      (Nat.le_euclideanDiv_iff_mul_le (a := y) (k := x) ha.ne').symm

instance instCeilDiv : CeilDiv ℕ ℕ where
  ceilDiv a b hb := Nat.euclideanDiv (a + b - 1) b hb.ne'
  ceilDiv_gc a ha b c := by
    change Nat.euclideanDiv (b + a - 1) a ha.ne' ≤ c ↔ b ≤ a * c
    rw [← Nat.not_lt, ← Nat.succ_le_iff, Nat.le_euclideanDiv_iff_mul_le ha.ne', Nat.mul_add_one]
    omega

@[simp] lemma floorDiv_eq_div (a b : ℕ) (hb : 0 < b) : a ⌊/⌋ b = Nat.euclideanDiv a b hb.ne' := rfl
lemma ceilDiv_eq_add_pred_div (a b : ℕ) (hb : 0 < b) :
    a ⌈/⌉ b = Nat.euclideanDiv (a + b - 1) b hb.ne' := rfl

end Nat

namespace Pi
variable {π : ι → Type*} [AddCommMonoid α] [PartialOrder α]
  [∀ i, AddCommMonoid (π i)] [∀ i, PartialOrder (π i)]
  [∀ i, SMulZeroClass α (π i)]

section FloorDiv
variable [∀ i, FloorDiv α (π i)]

instance instFloorDiv : FloorDiv α (∀ i, π i) where
  floorDiv f a ha i := f i ⌊/⌋ a
  floorDiv_gc _a ha _f _g := forall_congr' fun _i ↦ gc_floorDiv_smul ha _ _

@[push ←]
lemma floorDiv_def (f : ∀ i, π i) (a : α) (ha : 0 < a) : f ⌊/⌋ a = fun i ↦ f i ⌊/⌋ a := rfl
@[simp] lemma floorDiv_apply (f : ∀ i, π i) (a : α) (ha : 0 < a) (i : ι) :
    (f ⌊/⌋ a) i = f i ⌊/⌋ a := rfl

end FloorDiv

section CeilDiv
variable [∀ i, CeilDiv α (π i)]

instance instCeilDiv : CeilDiv α (∀ i, π i) where
  ceilDiv f a ha i := f i ⌈/⌉ a
  ceilDiv_gc _a ha _f _g := forall_congr' fun _i ↦ gc_smul_ceilDiv ha _ _

lemma ceilDiv_def (f : ∀ i, π i) (a : α) (ha : 0 < a) : f ⌈/⌉ a = fun i ↦ f i ⌈/⌉ a := rfl
@[simp] lemma ceilDiv_apply (f : ∀ i, π i) (a : α) (ha : 0 < a) (i : ι) :
    (f ⌈/⌉ a) i = f i ⌈/⌉ a := rfl

end CeilDiv
end Pi

namespace Finsupp
variable [AddCommMonoid α] [PartialOrder α]
  [AddCommMonoid β] [PartialOrder β] [SMulZeroClass α β] [PosSMulReflectLE α β]

section FloorDiv
variable [FloorDiv α β] {f : ι →₀ β} {a : α}

noncomputable instance instFloorDiv : FloorDiv α (ι →₀ β) where
  floorDiv f a ha := f.mapRange (· ⌊/⌋ a) <| zero_floorDiv _ ha
  floorDiv_gc _a ha f _g := forall_congr' fun i ↦ by
    simpa only [coe_smul, Pi.smul_apply, mapRange_apply] using gc_floorDiv_smul ha (f i) _

lemma floorDiv_def (f : ι →₀ β) (a : α) (ha : 0 < a) :
    f ⌊/⌋ a = f.mapRange (· ⌊/⌋ a) (zero_floorDiv _ ha) := rfl
set_option warning.simp.otherHead false in
@[norm_cast] lemma coe_floorDiv (f : ι →₀ β) (a : α) (ha : 0 < a) :
    f ⌊/⌋ a = fun i ↦ f i ⌊/⌋ a := rfl
@[simp] lemma floorDiv_apply (f : ι →₀ β) (a : α) (ha : 0 < a) (i : ι) :
    (f ⌊/⌋ a) i = f i ⌊/⌋ a := rfl

lemma support_floorDiv_subset (ha : 0 < a) : (f ⌊/⌋ a).support ⊆ f.support := by
  simp +contextual [Finset.subset_iff, not_imp_not]

end FloorDiv

section CeilDiv
variable [CeilDiv α β] {f : ι →₀ β} {a : α}

noncomputable instance instCeilDiv : CeilDiv α (ι →₀ β) where
  ceilDiv f a ha := f.mapRange (· ⌈/⌉ a) <| zero_ceilDiv _ ha
  ceilDiv_gc _a ha f _g := forall_congr' fun i ↦ by
    simpa only [coe_smul, Pi.smul_apply, mapRange_apply] using gc_smul_ceilDiv ha (f i) _

lemma ceilDiv_def (f : ι →₀ β) (a : α) (ha : 0 < a) :
    f ⌈/⌉ a = f.mapRange (· ⌈/⌉ a) (zero_ceilDiv _ ha) := rfl
set_option warning.simp.otherHead false in
@[norm_cast] lemma coe_ceilDiv_def (f : ι →₀ β) (a : α) (ha : 0 < a) :
    f ⌈/⌉ a = fun i ↦ f i ⌈/⌉ a := rfl
@[simp] lemma ceilDiv_apply (f : ι →₀ β) (a : α) (ha : 0 < a) (i : ι) :
    (f ⌈/⌉ a) i = f i ⌈/⌉ a := rfl

lemma support_ceilDiv_subset (ha : 0 < a) : (f ⌈/⌉ a).support ⊆ f.support := by
  simp +contextual [Finset.subset_iff, not_imp_not]

end CeilDiv
end Finsupp

/-- This is the motivating example. -/
noncomputable example : FloorDiv ℕ (ℕ →₀ ℕ) := inferInstance
