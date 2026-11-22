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

In characteristic zero, a division ring records embeddings `ℚ≥0 → α` and `ℚ → α`
(`Mathlib.Algebra.Field.Defs`). Their laws identify them with the evaluation of
`Mathlib.Data.Rat.Cast.Defs`, so they are ring homomorphisms. The casts commute with inversion,
division and integer powers; the invertibility evidence of the cast operands is derived from
that of the rational operands through `Rat.cast_ne_zero`.
-/

@[expose] public section

variable {α : Type*}

namespace Rat
variable [DivisionRing α] [CharZero α] {p q : ℚ}

private theorem cast_eq_eval_den (q : ℚ) :
    (q : α) = eval q (Nat.cast_ne_zero.mpr q.den_nz) :=
  cast_eq_eval q _

lemma cast_def (q : ℚ) :
    (q : α) = Checked.div (q.num : α) (q.den : α) (Nat.cast_ne_zero.mpr q.den_nz).isUnit :=
  cast_eq_eval_den q

lemma cast_mk' (a b h1 h2) :
    ((⟨a, b, h1, h2⟩ : ℚ) : α) = Checked.div (a : α) (b : α) (Nat.cast_ne_zero.mpr h1).isUnit :=
  cast_def _

@[simp, norm_cast] theorem cast_natCast (n : ℕ) : ((n : ℚ) : α) = n :=
  (cast_eq_eval_den _).trans (eval_natCast _ _)
@[simp, norm_cast] theorem cast_intCast (n : ℤ) : ((n : ℚ) : α) = n :=
  (cast_eq_eval_den _).trans (eval_intCast _ _)
@[simp, norm_cast] theorem cast_zero : ((0 : ℚ) : α) = 0 := by
  simpa only [Nat.cast_zero] using (cast_natCast (α := α) 0)
@[simp, norm_cast] theorem cast_one : ((1 : ℚ) : α) = 1 := by
  simpa only [Nat.cast_one] using (cast_natCast (α := α) 1)

@[simp, norm_cast] theorem cast_add (p q : ℚ) : ((p + q : ℚ) : α) = (p : α) + q := by
  simp only [cast_eq_eval_den]
  exact eval_add _ _ _ _ _

@[simp, norm_cast] theorem cast_mul (p q : ℚ) : ((p * q : ℚ) : α) = (p : α) * q := by
  simp only [cast_eq_eval_den]
  exact eval_mul _ _ _ _ _

@[simp, norm_cast] theorem cast_neg (q : ℚ) : ((-q : ℚ) : α) = -(q : α) := by
  simp only [cast_eq_eval_den]
  exact eval_neg _ _

@[simp, norm_cast] theorem cast_sub (p q : ℚ) : ((p-q : ℚ) : α) = (p : α) - q := by
  simp only [sub_eq_add_neg, cast_add, cast_neg]

@[simp, norm_cast] theorem cast_ofNat (n : ℕ) [n.AtLeastTwo] :
    ((ofNat(n) : ℚ) : α) = ofNat(n) := cast_natCast n

@[stacks 09FR "Characteristic zero case."]
lemma cast_injective : Function.Injective ((↑) : ℚ → α) := by
  intro p q h
  have he : (p.num : α) * (q.den : α) = (q.num : α) * (p.den : α) := by
    rw [← cast_mul_den p, h, mul_assoc, (Nat.cast_commute p.den (q.den : α)).eq,
      ← mul_assoc, cast_mul_den]
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
@[implicit_reducible]
def castHom : ℚ →+* α where
  toFun := (↑)
  map_one' := cast_one
  map_mul' := cast_mul
  map_zero' := cast_zero
  map_add' := cast_add

@[simp] lemma coe_castHom : ⇑(castHom α) = ((↑) : ℚ → α) := rfl

@[simp, norm_cast] lemma cast_inv (p : ℚ) {hp : IsUnit p} : ((p⁻¹ : ℚ) : α) = (p : α)⁻¹ :=
  map_inv₀ (castHom α) _

@[simp, norm_cast] lemma cast_div (p q : ℚ) {hq : IsUnit q} :
    ((p / q : ℚ) : α) = ((p : α) / (q : α)) :=
  map_div₀ (castHom α) ..

@[norm_cast]
theorem cast_fractionInt (n d : ℤ) (hd : d ≠ 0) :
    (fractionInt n d hd : α) = Checked.div (n : α) (d : α) (Int.cast_ne_zero.mpr hd).isUnit :=
  (cast_eq_eval_den _).trans (eval_fractionInt n d hd (Int.cast_ne_zero.mpr hd))

@[simp, norm_cast]
lemma cast_zpow (p : ℚ) (n : ℤ) {h : n < 0 → IsUnit p} :
    ((p ^ n : ℚ) : α) =
      Checked.zpow (p : α) n fun hn => (cast_ne_zero.mpr (h hn).ne_zero).isUnit :=
  map_zpow₀ (castHom α) ..

theorem cast_commute (q : ℚ) (a : α) : Commute (q : α) a := by
  change (q : α) * a = a * (q : α)
  apply mul_right_cancel₀ (Nat.cast_ne_zero.mpr q.den_nz : (q.den : α) ≠ 0)
  rw [mul_assoc, ← (Nat.cast_commute q.den a).eq, ← mul_assoc, cast_mul_den,
    mul_assoc, cast_mul_den]
  exact (Int.cast_commute q.num a).eq

theorem commute_cast (a : α) (q : ℚ) : Commute a (q : α) := (cast_commute q a).symm

theorem cast_comm (q : ℚ) (a : α) : (q : α) * a = a * (q : α) := (cast_commute q a).eq

end Rat

namespace NNRat
variable [DivisionSemiring α] [CharZero α] {p q : ℚ≥0}

private theorem cast_eq_eval_den (q : ℚ≥0) :
    (q : α) = eval q (Nat.cast_ne_zero.mpr q.den_ne_zero) :=
  cast_eq_eval q _

lemma cast_def (q : ℚ≥0) :
    (q : α) = Checked.div (q.num : α) (q.den : α) (Nat.cast_ne_zero.mpr q.den_ne_zero).isUnit :=
  cast_eq_eval_den q

@[simp, norm_cast] theorem cast_natCast (n : ℕ) : ((n : ℚ≥0) : α) = n :=
  (cast_eq_eval_den _).trans (eval_natCast _ _)
@[simp, norm_cast] theorem cast_zero : ((0 : ℚ≥0) : α) = 0 := by
  simpa only [Nat.cast_zero] using (cast_natCast (α := α) 0)
@[simp, norm_cast] theorem cast_one : ((1 : ℚ≥0) : α) = 1 := by
  simpa only [Nat.cast_one] using (cast_natCast (α := α) 1)
@[simp, norm_cast] theorem cast_ofNat (n : ℕ) [n.AtLeastTwo] :
    ((ofNat(n) : ℚ≥0) : α) = ofNat(n) := cast_natCast n

@[simp, norm_cast] theorem cast_add (p q : ℚ≥0) : ((p + q : ℚ≥0) : α) = (p : α) + q := by
  simp only [cast_eq_eval_den]
  exact eval_add _ _ _ _ _
@[simp, norm_cast] theorem cast_mul (p q : ℚ≥0) : ((p * q : ℚ≥0) : α) = (p : α) * q := by
  simp only [cast_eq_eval_den]
  exact eval_mul _ _ _ _ _

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
def castHom : ℚ≥0 →+* α where
  toFun := (↑)
  map_one' := cast_one
  map_mul' := cast_mul
  map_zero' := cast_zero
  map_add' := cast_add

@[simp, norm_cast] lemma coe_castHom : ⇑(castHom α) = ((↑) : ℚ≥0 → α) := rfl

@[simp, norm_cast] lemma cast_inv (p : ℚ≥0) {hp : IsUnit p} : ((p⁻¹ : ℚ≥0) : α) = (p : α)⁻¹ :=
  map_inv₀ (castHom α) _

@[simp, norm_cast] lemma cast_div (p q : ℚ≥0) {hq : IsUnit q} :
    ((p / q : ℚ≥0) : α) = ((p : α) / (q : α)) :=
  map_div₀ (castHom α) ..

@[simp, norm_cast]
lemma cast_zpow (q : ℚ≥0) (p : ℤ) {h : p < 0 → IsUnit q} :
    ((q ^ p : ℚ≥0) : α) =
      Checked.zpow (q : α) p fun hp => (cast_ne_zero.mpr (h hp).ne_zero).isUnit :=
  map_zpow₀ (castHom α) ..

@[simp]
lemma cast_divNat (a b : ℕ) (hb : b ≠ 0) :
    (divNat a b hb : α) = Checked.div (a : α) (b : α) (Nat.cast_ne_zero.mpr hb).isUnit := by
  apply eq_div_of_mul_eq
  rw [← cast_natCast b, ← cast_mul, divNat_mul_den, cast_natCast]

theorem cast_commute (q : ℚ≥0) (a : α) : Commute (q : α) a := by
  change (q : α) * a = a * (q : α)
  apply mul_right_cancel₀ (Nat.cast_ne_zero.mpr q.den_ne_zero : (q.den : α) ≠ 0)
  rw [mul_assoc, ← (Nat.cast_commute q.den a).eq, ← mul_assoc, cast_mul_den,
    mul_assoc, cast_mul_den]
  exact (Nat.cast_commute q.num a).eq

theorem commute_cast (a : α) (q : ℚ≥0) : Commute a (q : α) := (cast_commute q a).symm

theorem cast_comm (q : ℚ≥0) (a : α) : (q : α) * a = a * (q : α) := (cast_commute q a).eq

end NNRat

lemma Rat.smul_def [DivisionRing α] [CharZero α] (q : ℚ) (x : α) : q • x = (q : α) * x :=
  DivisionRing.qsmulOfCharZero_eq_mul _ q x
lemma NNRat.smul_def [DivisionSemiring α] [CharZero α] (q : ℚ≥0) (x : α) :
    q • x = (q : α) * x :=
  DivisionSemiring.nnqsmulOfCharZero_eq_mul _ q x

@[simp]
theorem Rat.smul_one_eq_cast (A : Type*) [DivisionRing A] [CharZero A] (m : ℚ) :
    m • (1 : A) = ↑m := by
  rw [Rat.smul_def, mul_one]

@[simp]
lemma NNRat.smul_one_eq_cast (K : Type*) [DivisionSemiring K] [CharZero K] (q : ℚ≥0) :
    q • (1 : K) = q := by
  rw [NNRat.smul_def, mul_one]

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
  apply mul_right_cancel₀ (Nat.cast_ne_zero.mpr q.den_nz : (q.den : α) ≠ 0)
  rw [Rat.cast_mul_den, ← map_natCast f, ← map_mul, Rat.mul_den_eq_num, map_intCast]

@[simp] theorem map_nnratCast [DivisionSemiring α] [CharZero α]
    [DivisionSemiring β] [CharZero β] [FunLike F α β] [RingHomClass F α β]
    (f : F) (q : ℚ≥0) : f (q : α) = (q : β) := by
  apply mul_right_cancel₀ (Nat.cast_ne_zero.mpr q.den_ne_zero : (q.den : β) ≠ 0)
  rw [NNRat.cast_mul_den]
  have h := congrArg f (NNRat.cast_mul_den (α := α) q)
  simpa only [map_mul, map_natCast] using h

@[simp] lemma eq_nnratCast [DivisionSemiring α] [CharZero α]
    [FunLike F ℚ≥0 α] [RingHomClass F ℚ≥0 α] (f : F) (q : ℚ≥0) : f q = (q : α) := by
  apply mul_right_cancel₀ (Nat.cast_ne_zero.mpr q.den_ne_zero : (q.den : α) ≠ 0)
  rw [NNRat.cast_mul_den, ← map_natCast f, ← map_mul, NNRat.mul_den_eq_num, map_natCast]

end MapCasts
