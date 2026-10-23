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
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Order.Nat

/-!
# Evaluation of rational numbers on their exact domain

A rational can be evaluated in a division ring when its reduced denominator is nonzero there.
These definitions also apply in positive characteristic. A total rational cast is installed
separately, under characteristic zero, in `Mathlib.Data.Rat.Cast.CharZero`.
-/

@[expose] public section

namespace Rat

variable {α : Type*} [DivisionRing α]

/-- Evaluate a rational using its denominator as a unit. -/
noncomputable def eval (q : ℚ) (hd : (q.den : α) ≠ 0) : α :=
  (q.num : α) /ₚ Units.mk0 (q.den : α) hd

@[simp] theorem eval_mul_den (q : ℚ) (hd : (q.den : α) ≠ 0) :
    eval q hd * (q.den : α) = (q.num : α) :=
  divp_mul_cancel _ _

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

theorem reciprocal_den_ne_zero (q : ℚ) (hq : q ≠ 0) (hd : (q.den : α) ≠ 0)
    (hv : eval q hd ≠ 0) : ((reciprocal q hq).den : α) ≠ 0 := by
  have hnum : (q.num : α) ≠ 0 := by
    rw [← eval_mul_den q hd]
    exact mul_ne_zero hv hd
  unfold reciprocal fractionInt
  apply normalize_den_ne_zero
  by_cases h : 0 ≤ q.num
  · rw [← Int.cast_natCast, Int.natAbs_of_nonneg h]
    exact hnum
  · rw [← Int.cast_natCast, Int.ofNat_natAbs_of_nonpos (le_of_not_ge h), Int.cast_neg]
    exact neg_ne_zero.mpr hnum

/-- Evaluation commutes with reciprocal only on the domain of the original operand. -/
theorem eval_reciprocal (q : ℚ) (hq : q ≠ 0) (hd : (q.den : α) ≠ 0)
    (hi : ((reciprocal q hq).den : α) ≠ 0) (hv : eval q hd ≠ 0) :
    eval (reciprocal q hq) hi = ↑((Units.mk0 (eval q hd) hv)⁻¹) := by
  have he := eval_mul (reciprocal q hq) q hi hd (mul_den_ne_zero _ _ hi hd)
  simp only [Rat.reciprocal_mul] at he
  have he' : eval (reciprocal q hq) hi * eval q hd = 1 :=
    he.symm.trans ((eval_natCast (α := α) 1 _).trans Nat.cast_one)
  apply mul_right_cancel₀ hv
  exact he'.trans (Units.inv_mul (Units.mk0 (eval q hd) hv)).symm

theorem quotient_den_ne_zero (a b : ℚ) (hb : b ≠ 0)
    (ha : (a.den : α) ≠ 0) (hd : (b.den : α) ≠ 0) (hv : eval b hd ≠ 0) :
    ((quotient a b hb).den : α) ≠ 0 :=
  mul_den_ne_zero a (reciprocal b hb) ha (reciprocal_den_ne_zero b hb hd hv)

theorem eval_quotient (a b : ℚ) (hb : b ≠ 0)
    (ha : (a.den : α) ≠ 0) (hd : (b.den : α) ≠ 0)
    (hr : ((quotient a b hb).den : α) ≠ 0) (hv : eval b hd ≠ 0) :
    eval (quotient a b hb) hr = eval a ha /ₚ Units.mk0 (eval b hd) hv := by
  change ((a * reciprocal b hb).den : α) ≠ 0 at hr
  change eval (a * reciprocal b hb) hr = _
  rw [eval_mul _ _ ha (reciprocal_den_ne_zero b hb hd hv),
    eval_reciprocal b hb hd (reciprocal_den_ne_zero b hb hd hv) hv]
  rfl

@[simp] theorem eval_rat (q : ℚ) (hd : (q.den : ℚ) ≠ 0) : eval q hd = q := by
  apply mul_right_cancel₀ hd
  rw [eval_mul_den, Rat.mul_den_eq_num]

end Rat

namespace NNRat

variable {α : Type*} [DivisionSemiring α]

/-- Evaluate a nonnegative rational using its denominator as a unit. -/
noncomputable def eval (q : ℚ≥0) (hd : (q.den : α) ≠ 0) : α :=
  (q.num : α) /ₚ Units.mk0 (q.den : α) hd

@[simp] theorem eval_mul_den (q : ℚ≥0) (hd : (q.den : α) ≠ 0) :
    eval q hd * (q.den : α) = (q.num : α) := divp_mul_cancel _ _

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

/-- Evaluate a unit inverse only when the original unit's image is nonzero. -/
theorem eval_inv (u : (ℚ≥0)ˣ) (hu : ((u : ℚ≥0).den : α) ≠ 0)
    (hi : ((↑(u⁻¹) : ℚ≥0).den : α) ≠ 0) (hv : eval (u : ℚ≥0) hu ≠ 0) :
    eval (↑(u⁻¹) : ℚ≥0) hi = ↑((Units.mk0 (eval (u : ℚ≥0) hu) hv)⁻¹) := by
  have he := eval_mul (↑(u⁻¹) : ℚ≥0) (u : ℚ≥0) hi hu (mul_den_ne_zero _ _ hi hu)
  simp only [Units.inv_mul] at he
  have he' : eval (↑(u⁻¹) : ℚ≥0) hi * eval (u : ℚ≥0) hu = 1 :=
    he.symm.trans ((eval_natCast (α := α) 1 _).trans Nat.cast_one)
  apply mul_right_cancel₀ hv
  exact he'.trans (Units.inv_mul (Units.mk0 (eval (u : ℚ≥0) hu) hv)).symm

@[simp] theorem eval_nnrat (q : ℚ≥0) (hd : (q.den : ℚ≥0) ≠ 0) : eval q hd = q := by
  apply mul_right_cancel₀ hd
  rw [eval_mul_den, NNRat.mul_den_eq_num]

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

@[ext] lemma ext_nnrat {f g : ℚ≥0 →*₀ M}
    (h : f.comp (.ofClass (Nat.castRingHom ℚ≥0)) =
      g.comp (.ofClass (Nat.castRingHom ℚ≥0))) : f = g :=
  ext_nnrat' <| DFunLike.congr_fun h

@[ext] theorem ext_rat {f g : ℚ →*₀ M}
    (h : f.comp (.ofClass (Int.castRingHom ℚ)) =
      g.comp (.ofClass (Int.castRingHom ℚ))) : f = g :=
  ext_rat' <| DFunLike.congr_fun h

lemma ext_nnrat_on_pnat [FunLike F ℚ≥0 M] [MonoidWithZeroHomClass F ℚ≥0 M] {f g : F}
    (same_on_pnat : ∀ n : ℕ, 0 < n → f n = g n) : f = g :=
  ext_nnrat' <| DFunLike.congr_fun <| ext_nat''
    ((.ofClass f : ℚ≥0 →*₀ M).comp (.ofClass (Nat.castRingHom ℚ≥0)))
    ((.ofClass g : ℚ≥0 →*₀ M).comp (.ofClass (Nat.castRingHom ℚ≥0))) (by simpa)

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
