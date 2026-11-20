/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Commute.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Order.Nat

/-!
# Evaluation of rational numbers on their exact domain

A rational can be evaluated in a division ring when its reduced denominator is nonzero there.
These definitions also apply in positive characteristic. In characteristic zero, the rational
embeddings recorded by a division ring agree with evaluation (`Rat.cast_eq_eval`); their theory
is in `Mathlib.Data.Rat.Cast.CharZero`.
-/

@[expose] public section

namespace Rat

variable {α : Type*} [DivisionRing α]

/-- Evaluate a rational as the quotient of its numerator by its denominator, which must be
nonzero in `α`. -/
noncomputable def eval (q : ℚ) (hd : (q.den : α) ≠ 0) : α :=
  (q.num : α) / (q.den : α)

@[simp] theorem eval_mul_den (q : ℚ) (hd : (q.den : α) ≠ 0) :
    eval q hd * (q.den : α) = (q.num : α) :=
  div_mul_cancel₀ _

/-- Normalization preserves the nonvanishing of the original denominator. -/
theorem normalize_den_ne_zero {R : Type*} [Semiring R] (n : ℤ) (d : ℕ)
    (hd : d ≠ 0) (h : (d : R) ≠ 0) :
    ((normalize n d hd).den : R) ≠ 0 := by
  obtain ⟨g, _, _, he⟩ := normalize_num_den' n d hd
  intro hz
  apply h
  rw [he, Nat.cast_mul, hz, zero_mul]

private theorem eval_normalize_mul (n : ℤ) (d : ℕ) (hd : d ≠ 0)
    (hq : ((normalize n d hd).den : α) ≠ 0) :
    eval (normalize n d hd) hq * (d : α) = (n : α) := by
  obtain ⟨g, _, hn, hd'⟩ := normalize_num_den' n d hd
  have hdcast := congrArg (fun x : ℕ => (x : α)) hd'
  have hncast := congrArg (fun x : ℤ => (x : α)) hn
  simp only [Nat.cast_mul] at hdcast
  simp only [Int.cast_mul, Int.cast_natCast] at hncast
  calc
    _ = eval (normalize n d hd) hq * ((normalize n d hd).den : α) * (g : α) := by
      conv => lhs; rhs; rw [hdcast]
      rw [mul_assoc]
    _ = (n : α) := by rw [eval_mul_den]; exact hncast.symm

/-- Evaluating a natural-denominator fraction gives the checked quotient of its original terms. -/
theorem eval_fraction (n : ℤ) (d : ℕ) (hd : d ≠ 0) (h : (d : α) ≠ 0) :
    eval (fraction n d hd) (normalize_den_ne_zero n d hd h) = (n : α) / (d : α) :=
  eq_div_of_mul_eq (eval_normalize_mul n d hd (normalize_den_ne_zero n d hd h))

private theorem sign_natAbs_cast_ne_zero (d : ℤ) (h : (d : α) ≠ 0) :
    (d.sign : α) ≠ 0 ∧ (d.natAbs : α) ≠ 0 :=
  mul_ne_zero_iff.mp (by rwa [← Int.cast_natCast, ← Int.cast_mul, Int.sign_mul_natAbs])

/-- Normalizing a signed fraction preserves nonvanishing of its denominator in the target. -/
theorem fractionInt_den_ne_zero (n d : ℤ) (hd : d ≠ 0) (h : (d : α) ≠ 0) :
    ((fractionInt n d hd).den : α) ≠ 0 :=
  normalize_den_ne_zero _ _ _ (sign_natAbs_cast_ne_zero d h).2

/-- Evaluating a signed fraction gives the checked quotient of its original terms. -/
theorem eval_fractionInt (n d : ℤ) (hd : d ≠ 0) (h : (d : α) ≠ 0) :
    eval (fractionInt n d hd) (fractionInt_den_ne_zero n d hd h) = (n : α) / (d : α) := by
  apply eq_div_of_mul_eq
  apply mul_right_cancel₀ (sign_natAbs_cast_ne_zero d h).1
  have hsign : (d : α) * (d.sign : α) = (d.natAbs : α) := by
    rw [← Int.cast_mul, Int.mul_comm d d.sign, Int.sign_mul_self_eq_natAbs, Int.cast_natCast]
  rw [mul_assoc, hsign, ← Int.cast_mul, Int.mul_comm n d.sign]
  exact eval_normalize_mul (d.sign * n) d.natAbs _ (fractionInt_den_ne_zero n d hd h)

theorem add_den_ne_zero (a b : ℚ) (ha : (a.den : α) ≠ 0) (hb : (b.den : α) ≠ 0) :
    ((a + b).den : α) ≠ 0 := by
  rw [Rat.add_def]
  apply normalize_den_ne_zero
  simpa only [Nat.cast_mul] using mul_ne_zero ha hb

theorem mul_den_ne_zero (a b : ℚ) (ha : (a.den : α) ≠ 0) (hb : (b.den : α) ≠ 0) :
    ((a * b).den : α) ≠ 0 := by
  rw [Rat.mul_def]
  apply normalize_den_ne_zero
  simpa only [Nat.cast_mul] using mul_ne_zero ha hb

theorem eval_add (a b : ℚ) (ha : (a.den : α) ≠ 0) (hb : (b.den : α) ≠ 0)
    (hc : ((a + b).den : α) ≠ 0) : eval (a + b) hc = eval a ha + eval b hb := by
  apply mul_right_cancel₀ (mul_ne_zero ha hb)
  have h := eval_normalize_mul (α := α)
    (a.num * b.den + b.num * a.den) (a.den * b.den)
    (Nat.mul_ne_zero a.den_nz b.den_nz)
    (by simpa only [← Rat.add_def] using hc)
  simp only [← Rat.add_def, Nat.cast_mul, Int.cast_add, Int.cast_mul, Int.cast_natCast] at h
  rw [h, add_mul, ← mul_assoc, eval_mul_den]
  rw [(Nat.cast_commute a.den (b.den : α)).eq, ← mul_assoc, eval_mul_den]

theorem eval_mul (a b : ℚ) (ha : (a.den : α) ≠ 0) (hb : (b.den : α) ≠ 0)
    (hc : ((a * b).den : α) ≠ 0) : eval (a * b) hc = eval a ha * eval b hb := by
  apply mul_right_cancel₀ (mul_ne_zero ha hb)
  have h := eval_normalize_mul (α := α) (a.num * b.num) (a.den * b.den)
    (Nat.mul_ne_zero a.den_nz b.den_nz)
    (by simpa only [← Rat.mul_def] using hc)
  simp only [← Rat.mul_def, Nat.cast_mul, Int.cast_mul] at h
  rw [h, mul_assoc, ← mul_assoc (eval b hb),
    ← (Nat.cast_commute a.den (eval b hb)).eq, mul_assoc,
    eval_mul_den, ← mul_assoc, eval_mul_den]

theorem eval_neg (a : ℚ) (ha : (a.den : α) ≠ 0) : eval (-a) ha = -eval a ha := by
  apply mul_right_cancel₀ ha
  change eval (-a) ha * ((-a).den : α) = _
  rw [eval_mul_den, Rat.neg_num, Int.cast_neg, neg_mul, eval_mul_den]

theorem sub_den_ne_zero (a b : ℚ) (ha : (a.den : α) ≠ 0) (hb : (b.den : α) ≠ 0) :
    ((a - b).den : α) ≠ 0 := by
  simpa only [Rat.sub_eq_add_neg] using add_den_ne_zero a (-b) ha hb

theorem eval_sub (a b : ℚ) (ha : (a.den : α) ≠ 0) (hb : (b.den : α) ≠ 0)
    (hc : ((a - b).den : α) ≠ 0) : eval (a - b) hc = eval a ha - eval b hb := by
  have he := eval_add a (-b) ha hb (by simpa only [← Rat.sub_eq_add_neg] using hc)
  simpa only [Rat.sub_eq_add_neg, eval_neg b hb, sub_eq_add_neg] using he

theorem eval_natCast (n : ℕ) (h : ((n : ℚ).den : α) ≠ 0) : eval n h = (n : α) := by
  have he := eval_mul_den (α := α) (n : ℚ) h
  simpa only [Rat.num_natCast, Rat.den_natCast, Nat.cast_one, mul_one,
    Int.cast_natCast] using he

theorem eval_intCast (n : ℤ) (h : ((n : ℚ).den : α) ≠ 0) : eval n h = (n : α) := by
  have he := eval_mul_den (α := α) (n : ℚ) h
  simpa only [Rat.num_intCast, Rat.den_intCast, Nat.cast_one, mul_one] using he

theorem pow_den_ne_zero (q : ℚ) (hq : (q.den : α) ≠ 0) (n : ℕ) :
    ((q ^ n).den : α) ≠ 0 := by
  rw [Rat.den_pow, Nat.cast_pow]
  exact pow_ne_zero n hq

theorem eval_pow (q : ℚ) (hq : (q.den : α) ≠ 0) (n : ℕ)
    (hp : ((q ^ n).den : α) ≠ 0) : eval (q ^ n) hp = eval q hq ^ n := by
  induction n with
  | zero =>
    simp only [pow_zero]
    exact (eval_natCast (α := α) 1 _).trans Nat.cast_one
  | succ n ih =>
    simp only [Rat.pow_succ] at hp ⊢
    rw [eval_mul _ _ (pow_den_ne_zero q hq n) hq, ih, pow_succ]

/-- The reduced denominator of a reciprocal is the absolute value of the original numerator. -/
theorem den_reciprocal (q : ℚ) (hq : q ≠ 0) : (reciprocal q hq).den = q.num.natAbs := by
  rw [← inv_eq_of_mul_eq_one_left₀ (hb := hq.isUnit) (Rat.reciprocal_mul q hq),
    Rat.den_inv_of_ne_zero]

theorem reciprocal_den_ne_zero (q : ℚ) (hq : q ≠ 0) (hd : (q.den : α) ≠ 0)
    (hv : eval q hd ≠ 0) : ((reciprocal q hq).den : α) ≠ 0 := by
  have hnum : (q.num : α) ≠ 0 := by
    rw [← eval_mul_den q hd]
    exact mul_ne_zero hv hd
  rw [den_reciprocal]
  by_cases h : 0 ≤ q.num
  · rw [← Int.cast_natCast, Int.natAbs_of_nonneg h]
    exact hnum
  · rw [← Int.cast_natCast, Int.ofNat_natAbs_of_nonpos (le_of_not_ge h), Int.cast_neg]
    exact neg_ne_zero.mpr hnum

/-- The evaluations of a reciprocal and its operand multiply to one on their common domain. -/
theorem eval_reciprocal_mul (q : ℚ) (hq : q ≠ 0) (hd : (q.den : α) ≠ 0)
    (hi : ((reciprocal q hq).den : α) ≠ 0) : eval (reciprocal q hq) hi * eval q hd = 1 := by
  have he := eval_mul (reciprocal q hq) q hi hd (mul_den_ne_zero _ _ hi hd)
  simp only [Rat.reciprocal_mul] at he
  exact he.symm.trans ((eval_natCast (α := α) 1 _).trans Nat.cast_one)

/-- Evaluation commutes with reciprocal when both reduced denominators remain nonzero. -/
theorem eval_reciprocal (q : ℚ) (hq : q ≠ 0) (hd : (q.den : α) ≠ 0)
    (hi : ((reciprocal q hq).den : α) ≠ 0) :
    eval (reciprocal q hq) hi =
      Checked.inv (eval q hd)
        (right_ne_zero_of_mul_eq_one (eval_reciprocal_mul q hq hd hi)).isUnit :=
  (inv_eq_of_mul_eq_one_left₀ (eval_reciprocal_mul q hq hd hi)).symm

theorem quotient_den_ne_zero (a b : ℚ) (hb : b ≠ 0)
    (ha : (a.den : α) ≠ 0) (hd : (b.den : α) ≠ 0) (hv : eval b hd ≠ 0) :
    ((quotient a b hb).den : α) ≠ 0 :=
  mul_den_ne_zero a (reciprocal b hb) ha (reciprocal_den_ne_zero b hb hd hv)

theorem eval_quotient (a b : ℚ) (hb : b ≠ 0)
    (ha : (a.den : α) ≠ 0) (hd : (b.den : α) ≠ 0)
    (hr : ((quotient a b hb).den : α) ≠ 0) (hv : eval b hd ≠ 0) :
    eval (quotient a b hb) hr = eval a ha / eval b hd := by
  change ((a * reciprocal b hb).den : α) ≠ 0 at hr
  change eval (a * reciprocal b hb) hr = _
  rw [eval_mul _ _ ha (reciprocal_den_ne_zero b hb hd hv),
    eval_reciprocal b hb hd (reciprocal_den_ne_zero b hb hd hv), div_eq_mul_inv₀]

@[simp] theorem eval_rat (q : ℚ) (hd : (q.den : ℚ) ≠ 0) : eval q hd = q := by
  apply mul_right_cancel₀ hd
  rw [eval_mul_den, Rat.mul_den_eq_num]

section CharZero
variable [CharZero α]

@[simp] theorem cast_mul_den (q : ℚ) : (q : α) * (q.den : α) = (q.num : α) :=
  DivisionRing.ratCastOfCharZero_mul_den _ q

/-- In characteristic zero, the rational embedding agrees with evaluation. -/
theorem cast_eq_eval (q : ℚ) (hd : (q.den : α) ≠ 0) : (q : α) = eval q hd :=
  mul_right_cancel₀ hd ((cast_mul_den q).trans (eval_mul_den q hd).symm)

end CharZero

end Rat

namespace NNRat

variable {α : Type*} [DivisionSemiring α]

/-- Evaluate a nonnegative rational as the quotient of its numerator by its denominator, which
must be nonzero in `α`. -/
noncomputable def eval (q : ℚ≥0) (hd : (q.den : α) ≠ 0) : α :=
  (q.num : α) / (q.den : α)

@[simp] theorem eval_mul_den (q : ℚ≥0) (hd : (q.den : α) ≠ 0) :
    eval q hd * (q.den : α) = (q.num : α) := div_mul_cancel₀ _

private theorem eval_divNat_mul (n d : ℕ) (hd : d ≠ 0)
    (hq : ((divNat n d hd).den : α) ≠ 0) :
    eval (divNat n d hd) hq * (d : α) = (n : α) := by
  obtain ⟨g, _, hn, hd'⟩ := Rat.normalize_num_den' (n : Int) d hd
  have hn' := congrArg Int.natAbs hn
  simp only [Int.natAbs_natCast, Int.natAbs_mul] at hn'
  change n = (divNat n d hd).num * g at hn'
  change d = (divNat n d hd).den * g at hd'
  have hdcast := congrArg (fun x : ℕ => (x : α)) hd'
  have hncast := congrArg (fun x : ℕ => (x : α)) hn'
  simp only [Nat.cast_mul] at hdcast hncast
  calc
    _ = eval (divNat n d hd) hq * ((divNat n d hd).den : α) * (g : α) := by
      conv => lhs; rhs; rw [hdcast]
      rw [mul_assoc]
    _ = (n : α) := by rw [eval_mul_den]; exact hncast.symm

theorem add_den_ne_zero (a b : ℚ≥0) (ha : (a.den : α) ≠ 0) (hb : (b.den : α) ≠ 0) :
    ((a + b).den : α) ≠ 0 := by
  rw [NNRat.add_def]
  apply Rat.normalize_den_ne_zero (R := α) _ _ (Nat.mul_ne_zero a.den_ne_zero b.den_ne_zero)
  simpa only [Nat.cast_mul] using mul_ne_zero ha hb

theorem mul_den_ne_zero (a b : ℚ≥0) (ha : (a.den : α) ≠ 0) (hb : (b.den : α) ≠ 0) :
    ((a * b).den : α) ≠ 0 := by
  rw [NNRat.mul_def]
  apply Rat.normalize_den_ne_zero (R := α) _ _ (Nat.mul_ne_zero a.den_ne_zero b.den_ne_zero)
  simpa only [Nat.cast_mul] using mul_ne_zero ha hb

theorem eval_add (a b : ℚ≥0) (ha : (a.den : α) ≠ 0) (hb : (b.den : α) ≠ 0)
    (hc : ((a + b).den : α) ≠ 0) : eval (a + b) hc = eval a ha + eval b hb := by
  apply mul_right_cancel₀ (mul_ne_zero ha hb)
  have h := eval_divNat_mul (α := α) (a.num * b.den + b.num * a.den) (a.den * b.den)
    (Nat.mul_ne_zero a.den_ne_zero b.den_ne_zero)
    (by simpa only [← NNRat.add_def] using hc)
  simp only [← NNRat.add_def, Nat.cast_mul, Nat.cast_add] at h
  rw [h, add_mul, ← mul_assoc, eval_mul_den]
  rw [(Nat.cast_commute a.den (b.den : α)).eq, ← mul_assoc, eval_mul_den]

theorem eval_mul (a b : ℚ≥0) (ha : (a.den : α) ≠ 0) (hb : (b.den : α) ≠ 0)
    (hc : ((a * b).den : α) ≠ 0) : eval (a * b) hc = eval a ha * eval b hb := by
  apply mul_right_cancel₀ (mul_ne_zero ha hb)
  have h := eval_divNat_mul (α := α) (a.num * b.num) (a.den * b.den)
    (Nat.mul_ne_zero a.den_ne_zero b.den_ne_zero)
    (by simpa only [← NNRat.mul_def] using hc)
  simp only [← NNRat.mul_def, Nat.cast_mul] at h
  rw [h, mul_assoc, ← mul_assoc (eval b hb),
    ← (Nat.cast_commute a.den (eval b hb)).eq, mul_assoc,
    eval_mul_den, ← mul_assoc, eval_mul_den]

theorem eval_natCast (n : ℕ) (h : ((n : ℚ≥0).den : α) ≠ 0) : eval n h = (n : α) := by
  have he := eval_mul_den (α := α) (n : ℚ≥0) h
  simpa only [NNRat.num_natCast, NNRat.den_natCast, Nat.cast_one, mul_one] using he

theorem pow_den_ne_zero (q : ℚ≥0) (hq : (q.den : α) ≠ 0) (n : ℕ) :
    ((q ^ n).den : α) ≠ 0 := by
  rw [NNRat.den_pow, Nat.cast_pow]
  exact pow_ne_zero n hq

theorem eval_pow (q : ℚ≥0) (hq : (q.den : α) ≠ 0) (n : ℕ)
    (hp : ((q ^ n).den : α) ≠ 0) : eval (q ^ n) hp = eval q hq ^ n := by
  induction n with
  | zero =>
    simp only [pow_zero]
    exact (eval_natCast (α := α) 1 _).trans Nat.cast_one
  | succ n ih =>
    simp only [pow_succ] at hp ⊢
    rw [eval_mul _ _ (pow_den_ne_zero q hq n) hq, ih]

/-- The evaluations of an inverse and its operand multiply to one on their common domain. -/
theorem eval_inv_mul (q : ℚ≥0) {hq : IsUnit q} (hd : (q.den : α) ≠ 0)
    (hi : ((q⁻¹).den : α) ≠ 0) : eval q⁻¹ hi * eval q hd = 1 := by
  have he := eval_mul q⁻¹ q hi hd (mul_den_ne_zero _ _ hi hd)
  simp only [inv_mul_cancel₀] at he
  exact he.symm.trans ((eval_natCast (α := α) 1 _).trans Nat.cast_one)

/-- Evaluation commutes with inverse when both reduced denominators remain nonzero. -/
theorem eval_inv (q : ℚ≥0) {hq : IsUnit q} (hd : (q.den : α) ≠ 0)
    (hi : ((q⁻¹).den : α) ≠ 0) :
    eval q⁻¹ hi =
      Checked.inv (eval q hd) (right_ne_zero_of_mul_eq_one (eval_inv_mul q hd hi)).isUnit :=
  (inv_eq_of_mul_eq_one_left₀ (eval_inv_mul q hd hi)).symm

@[simp] theorem eval_nnrat (q : ℚ≥0) (hd : (q.den : ℚ≥0) ≠ 0) : eval q hd = q := by
  apply mul_right_cancel₀ hd
  rw [eval_mul_den, NNRat.mul_den_eq_num]

section CharZero
variable [CharZero α]

@[simp] theorem cast_mul_den (q : ℚ≥0) : (q : α) * (q.den : α) = (q.num : α) :=
  DivisionSemiring.nnratCastOfCharZero_mul_den _ q

/-- In characteristic zero, the nonnegative rational embedding agrees with evaluation. -/
theorem cast_eq_eval (q : ℚ≥0) (hd : (q.den : α) ≠ 0) : (q : α) = eval q hd :=
  mul_right_cancel₀ hd ((cast_mul_den q).trans (eval_mul_den q hd).symm)

end CharZero

end NNRat

namespace MonoidWithZeroHomClass

variable {F M : Type*} [MonoidWithZero M]

/-- Maps from nonnegative rationals are determined by their values on natural numbers. -/
lemma ext_nnrat' [FunLike F ℚ≥0 M] [MonoidWithZeroHomClass F ℚ≥0 M] {f g : F}
    (h : ∀ n : ℕ, f n = g n) : f = g := by
  apply DFunLike.ext f g
  intro q
  let u := (Units.mk0 (q.den : ℚ≥0) (Nat.cast_ne_zero.mpr q.den_ne_zero)).map
    (MonoidWithZeroHom.ofClass f).toMonoidHom
  apply (Units.mul_left_inj u).mp
  change f q * f (q.den : ℚ≥0) = g q * f (q.den : ℚ≥0)
  rw [← map_mul, NNRat.mul_den_eq_num, h q.num, h q.den, ← map_mul, NNRat.mul_den_eq_num]

/-- Maps from rationals are determined by their values on integers. -/
theorem ext_rat' [FunLike F ℚ M] [MonoidWithZeroHomClass F ℚ M] {f g : F}
    (h : ∀ n : ℤ, f n = g n) : f = g := by
  apply DFunLike.ext f g
  intro q
  let u := (Units.mk0 (q.den : ℚ) (Nat.cast_ne_zero.mpr q.den_nz)).map
    (MonoidWithZeroHom.ofClass f).toMonoidHom
  apply (Units.mul_left_inj u).mp
  change f q * f (q.den : ℚ) = g q * f (q.den : ℚ)
  have hd : f (q.den : ℚ) = g (q.den : ℚ) := by
    simpa only [Int.cast_natCast] using h (q.den : ℤ)
  rw [← map_mul, Rat.mul_den_eq_num, h q.num, hd, ← map_mul, Rat.mul_den_eq_num]

/-- If monoid with zero homs `f` and `g` from `ℚ≥0` agree on the naturals then they are equal.

See note [partially-applied ext lemmas] for why `comp` is used here. -/
@[ext] lemma ext_nnrat {f g : ℚ≥0 →*₀ M}
    (h : f.comp (.ofClass (Nat.castRingHom ℚ≥0)) =
      g.comp (.ofClass (Nat.castRingHom ℚ≥0))) : f = g :=
  ext_nnrat' <| DFunLike.congr_fun h

/-- If monoid with zero homs `f` and `g` from `ℚ` agree on the integers then they are equal.

See note [partially-applied ext lemmas] for why `comp` is used here. -/
@[ext] theorem ext_rat {f g : ℚ →*₀ M}
    (h : f.comp (.ofClass (Int.castRingHom ℚ)) =
      g.comp (.ofClass (Int.castRingHom ℚ))) : f = g :=
  ext_rat' <| DFunLike.congr_fun h

/-- If monoid with zero homs `f` and `g` from `ℚ≥0` agree on the positive naturals then they are
equal. -/
lemma ext_nnrat_on_pnat [FunLike F ℚ≥0 M] [MonoidWithZeroHomClass F ℚ≥0 M] {f g : F}
    (same_on_pnat : ∀ n : ℕ, 0 < n → f n = g n) : f = g :=
  ext_nnrat' <| DFunLike.congr_fun <| ext_nat''
    ((.ofClass f : ℚ≥0 →*₀ M).comp (.ofClass (Nat.castRingHom ℚ≥0)))
    ((.ofClass g : ℚ≥0 →*₀ M).comp (.ofClass (Nat.castRingHom ℚ≥0))) (by simpa)

/-- If monoid with zero homs `f` and `g` from `ℚ` agree on the positive naturals and `-1` then
they are equal. -/
theorem ext_rat_on_pnat [FunLike F ℚ M] [MonoidWithZeroHomClass F ℚ M] {f g : F}
    (same_on_neg_one : f (-1) = g (-1))
    (same_on_pnat : ∀ n : ℕ, 0 < n → f n = g n) : f = g :=
  ext_rat' <| DFunLike.congr_fun <|
    show (.ofClass f : ℚ →*₀ M).comp (.ofClass (Int.castRingHom ℚ)) =
      (.ofClass g : ℚ →*₀ M).comp (.ofClass (Int.castRingHom ℚ)) from
      ext_int' (by simpa) (by simpa)

end MonoidWithZeroHomClass

/-- Ring homomorphisms out of the rationals are unique, without a characteristic assumption
on the target ring. The image of each denominator is already a unit. -/
theorem RingHom.ext_rat {R F : Type*} [Semiring R] [FunLike F ℚ R] [RingHomClass F ℚ R]
    (f g : F) : f = g :=
  MonoidWithZeroHomClass.ext_rat' <| RingHom.congr_fun <|
    ((f : ℚ →+* R).comp (Int.castRingHom ℚ)).ext_int
      ((g : ℚ →+* R).comp (Int.castRingHom ℚ))

instance NNRat.subsingleton_ringHom {R : Type*} [Semiring R] : Subsingleton (ℚ≥0 →+* R) where
  allEq _ _ := MonoidWithZeroHomClass.ext_nnrat' fun _ => by simp only [map_natCast]

instance Rat.subsingleton_ringHom {R : Type*} [Semiring R] : Subsingleton (ℚ →+* R) :=
  ⟨RingHom.ext_rat⟩
