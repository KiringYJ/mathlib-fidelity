/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Data.Rat.Cast.Defs

/-!
# Casts of rational numbers into characteristic zero fields (or division rings).
-/

@[expose] public section

variable {α : Type*}

/-- A total rational cast exists in characteristic zero. -/
noncomputable instance (priority := 100) DivisionRing.toRatCast [DivisionRing α] [CharZero α] :
    RatCast α where
  ratCast q := Rat.eval q (Nat.cast_ne_zero.mpr q.den_nz)

namespace Rat
variable [DivisionRing α] [CharZero α] {p q : ℚ}

lemma cast_def (q : ℚ) : (q : α) = eval q (Nat.cast_ne_zero.mpr q.den_nz) := rfl

@[simp] theorem cast_mul_den (q : ℚ) : (q : α) * (q.den : α) = (q.num : α) :=
  eval_mul_den _ _

@[simp, norm_cast] theorem cast_natCast (n : ℕ) : ((n : ℚ) : α) = n := eval_natCast _ _
@[simp, norm_cast] theorem cast_intCast (n : ℤ) : ((n : ℚ) : α) = n := eval_intCast _ _
@[simp, norm_cast] theorem cast_zero : ((0 : ℚ) : α) = 0 := by
  simpa only [Nat.cast_zero] using (cast_natCast (α := α) 0)
@[simp, norm_cast] theorem cast_one : ((1 : ℚ) : α) = 1 := by
  simpa only [Nat.cast_one] using (cast_natCast (α := α) 1)

@[simp, norm_cast] theorem cast_add (p q : ℚ) : ((p + q : ℚ) : α) = (p : α) + q :=
  eval_add _ _ _ _ _

@[simp, norm_cast] theorem cast_mul (p q : ℚ) : ((p * q : ℚ) : α) = (p : α) * q :=
  eval_mul _ _ _ _ _

@[simp, norm_cast] theorem cast_neg (q : ℚ) : ((-q : ℚ) : α) = -(q : α) := eval_neg _ _

@[simp, norm_cast] theorem cast_sub (p q : ℚ) : ((p-q : ℚ) : α) = (p : α) - q := by
  simp only [sub_eq_add_neg, cast_add, cast_neg]

@[simp, norm_cast] theorem cast_ofNat (n : ℕ) [n.AtLeastTwo] :
    ((ofNat(n) : ℚ) : α) = ofNat(n) := cast_natCast n

@[stacks 09FR "Characteristic zero case."]
lemma cast_injective : Function.Injective ((↑) : ℚ → α) := by
  intro p q h
  have hp := eval_mul_den (α := α) p (Nat.cast_ne_zero.mpr p.den_nz)
  have hq := eval_mul_den (α := α) q (Nat.cast_ne_zero.mpr q.den_nz)
  change (p : α) * (p.den : α) = (p.num : α) at hp
  change (q : α) * (q.den : α) = (q.num : α) at hq
  have he : (p.num : α) * (q.den : α) = (q.num : α) * (p.den : α) := by
    rw [← hp, h, mul_assoc, (Nat.cast_commute p.den (q.den : α)).eq,
      ← mul_assoc, hq]
  have hn : p.num * q.den = q.num * p.den := by
    apply Int.cast_injective (α := α)
    simpa only [Int.cast_mul, Int.cast_natCast] using he
  exact (Rat.normalize_self p).symm.trans
    (((Rat.normalize_eq_iff p.den_nz q.den_nz).mpr hn).trans (Rat.normalize_self q))

@[simp, norm_cast] lemma cast_inj : (p : α) = q ↔ p = q := cast_injective.eq_iff
@[simp, norm_cast] lemma cast_eq_zero : (p : α) = 0 ↔ p = 0 :=
  cast_injective.eq_iff' cast_zero
lemma cast_ne_zero : (p : α) ≠ 0 ↔ p ≠ 0 := cast_eq_zero.ne

variable (α) in
/-- The characteristic-zero rational embedding as a ring homomorphism. -/
noncomputable def castHom : ℚ →+* α where
  toFun := (↑)
  map_one' := cast_one
  map_mul' := cast_mul
  map_zero' := cast_zero
  map_add' := cast_add

@[simp] lemma coe_castHom : ⇑(castHom α) = ((↑) : ℚ → α) := rfl

theorem cast_commute (q : ℚ) (a : α) : Commute (q : α) a := by
  change (q : α) * a = a * (q : α)
  apply mul_right_cancel₀ (Nat.cast_ne_zero.mpr q.den_nz : (q.den : α) ≠ 0)
  rw [mul_assoc, ← (Nat.cast_commute q.den a).eq, ← mul_assoc, cast_mul_den,
    mul_assoc, cast_mul_den]
  exact (Int.cast_commute q.num a).eq

theorem commute_cast (a : α) (q : ℚ) : Commute a (q : α) := (cast_commute q a).symm

theorem cast_comm (q : ℚ) (a : α) : (q : α) * a = a * (q : α) := (cast_commute q a).eq

end Rat

/-- A total nonnegative rational cast exists in characteristic zero. -/
noncomputable instance (priority := 100) DivisionSemiring.toNNRatCast
    [DivisionSemiring α] [CharZero α] : NNRatCast α where
  nnratCast q := NNRat.eval q (Nat.cast_ne_zero.mpr q.den_ne_zero)

namespace NNRat
variable [DivisionSemiring α] [CharZero α] {p q : ℚ≥0}

lemma cast_def (q : ℚ≥0) : (q : α) = eval q (Nat.cast_ne_zero.mpr q.den_ne_zero) := rfl

@[simp] theorem cast_mul_den (q : ℚ≥0) : (q : α) * (q.den : α) = (q.num : α) :=
  eval_mul_den _ _

@[simp, norm_cast] theorem cast_natCast (n : ℕ) : ((n : ℚ≥0) : α) = n := eval_natCast _ _
@[simp, norm_cast] theorem cast_zero : ((0 : ℚ≥0) : α) = 0 := by
  simpa only [Nat.cast_zero] using (cast_natCast (α := α) 0)
@[simp, norm_cast] theorem cast_one : ((1 : ℚ≥0) : α) = 1 := by
  simpa only [Nat.cast_one] using (cast_natCast (α := α) 1)
@[simp, norm_cast] theorem cast_ofNat (n : ℕ) [n.AtLeastTwo] :
    ((ofNat(n) : ℚ≥0) : α) = ofNat(n) := cast_natCast n

@[simp, norm_cast] theorem cast_add (p q : ℚ≥0) : ((p + q : ℚ≥0) : α) = (p : α) + q :=
  eval_add _ _ _ _ _
@[simp, norm_cast] theorem cast_mul (p q : ℚ≥0) : ((p * q : ℚ≥0) : α) = (p : α) * q :=
  eval_mul _ _ _ _ _

lemma cast_injective : Function.Injective ((↑) : ℚ≥0 → α) := by
  intro p q h
  have he : (p.num : α) * (q.den : α) = (q.num : α) * (p.den : α) := by
    rw [← cast_mul_den p, h, mul_assoc, (Nat.cast_commute p.den (q.den : α)).eq,
      ← mul_assoc, cast_mul_den]
  have hn : p.num * q.den = q.num * p.den := by
    apply Nat.cast_injective (R := α)
    simpa only [Nat.cast_mul] using he
  calc
    p = divNat p.num p.den p.den_ne_zero := p.num_divNat_den.symm
    _ = divNat q.num q.den q.den_ne_zero :=
      (divNat_inj p.den_ne_zero q.den_ne_zero).mpr hn
    _ = q := q.num_divNat_den

@[simp, norm_cast] lemma cast_inj : (p : α) = q ↔ p = q := cast_injective.eq_iff
@[simp, norm_cast] lemma cast_eq_zero : (p : α) = 0 ↔ p = 0 :=
  cast_injective.eq_iff' cast_zero
lemma cast_ne_zero : (p : α) ≠ 0 ↔ p ≠ 0 := cast_eq_zero.ne

variable (α) in
/-- The characteristic-zero nonnegative rational embedding. -/
noncomputable def castHom : ℚ≥0 →+* α where
  toFun := (↑)
  map_one' := cast_one
  map_mul' := cast_mul
  map_zero' := cast_zero
  map_add' := cast_add

@[simp] lemma coe_castHom : ⇑(castHom α) = ((↑) : ℚ≥0 → α) := rfl

theorem cast_commute (q : ℚ≥0) (a : α) : Commute (q : α) a := by
  change (q : α) * a = a * (q : α)
  apply mul_right_cancel₀ (Nat.cast_ne_zero.mpr q.den_ne_zero : (q.den : α) ≠ 0)
  rw [mul_assoc, ← (Nat.cast_commute q.den a).eq, ← mul_assoc, cast_mul_den,
    mul_assoc, cast_mul_den]
  exact (Nat.cast_commute q.num a).eq

theorem commute_cast (a : α) (q : ℚ≥0) : Commute a (q : α) := (cast_commute q a).symm

theorem cast_comm (q : ℚ≥0) (a : α) : (q : α) * a = a * (q : α) := (cast_commute q a).eq

end NNRat

/-- Rational scalars act by multiplication through the characteristic-zero embedding. -/
noncomputable instance (priority := 100) DivisionRing.toRatSMul [DivisionRing α] [CharZero α] :
    SMul ℚ α := ⟨fun q x => (q : α) * x⟩

/-- Nonnegative rational scalars act through the characteristic-zero embedding. -/
noncomputable instance (priority := 100) DivisionSemiring.toNNRatSMul
    [DivisionSemiring α] [CharZero α] : SMul ℚ≥0 α := ⟨fun q x => (q : α) * x⟩

lemma Rat.smul_def [DivisionRing α] [CharZero α] (q : ℚ) (x : α) : q • x = (q : α) * x := rfl
lemma NNRat.smul_def [DivisionSemiring α] [CharZero α] (q : ℚ≥0) (x : α) :
    q • x = (q : α) * x := rfl

section MapCasts
variable {F β : Type*}

@[simp] theorem map_ratCast [DivisionRing α] [CharZero α] [DivisionRing β] [CharZero β]
    [FunLike F α β] [RingHomClass F α β] (f : F) (q : ℚ) : f (q : α) = (q : β) := by
  apply mul_right_cancel₀ (Nat.cast_ne_zero.mpr q.den_nz : (q.den : β) ≠ 0)
  rw [Rat.cast_mul_den]
  have h := congrArg f (Rat.cast_mul_den (α := α) q)
  simpa only [map_mul, map_natCast, map_intCast] using h

@[simp] lemma eq_ratCast [DivisionRing α] [CharZero α]
    [FunLike F ℚ α] [RingHomClass F ℚ α] (f : F) (q : ℚ) : f q = (q : α) := by
  have h := map_ratCast f q
  simpa only [Rat.cast_def, Rat.eval_rat] using h

@[simp] theorem map_nnratCast [DivisionSemiring α] [CharZero α]
    [DivisionSemiring β] [CharZero β] [FunLike F α β] [RingHomClass F α β]
    (f : F) (q : ℚ≥0) : f (q : α) = (q : β) := by
  apply mul_right_cancel₀ (Nat.cast_ne_zero.mpr q.den_ne_zero : (q.den : β) ≠ 0)
  rw [NNRat.cast_mul_den]
  have h := congrArg f (NNRat.cast_mul_den (α := α) q)
  simpa only [map_mul, map_natCast] using h

@[simp] lemma eq_nnratCast [DivisionSemiring α] [CharZero α]
    [FunLike F ℚ≥0 α] [RingHomClass F ℚ≥0 α] (f : F) (q : ℚ≥0) : f q = (q : α) := by
  have h := map_nnratCast f q
  simpa only [NNRat.cast_def, NNRat.eval_nnrat] using h

end MapCasts
