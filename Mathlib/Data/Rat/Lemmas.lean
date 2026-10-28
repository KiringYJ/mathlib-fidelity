/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Algebra.GroupWithZero.Divisibility
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Ring.Int.Parity
public import Mathlib.Data.PNat.Defs

/-!
# Further lemmas for the Rational Numbers

-/

@[expose] public section


namespace Rat

-- TODO: move this to Lean
attribute [norm_cast] num_intCast den_intCast

theorem num_dvd (n : ℤ) (d : ℕ) (hd : d ≠ 0) : (fraction n d hd).num ∣ n := by
  obtain ⟨g, _, hn, _⟩ := normalize_num_den' n d hd
  exact ⟨g, hn⟩

theorem den_dvd (n : ℤ) (d : ℕ) (hd : d ≠ 0) : (fraction n d hd).den ∣ d := by
  obtain ⟨g, _, _, he⟩ := normalize_num_den' n d hd
  exact ⟨g, he⟩

theorem num_den_mk {q : ℚ} {n : ℤ} {d : ℕ} (hd : d ≠ 0)
    (qdf : q = fraction n d hd) : ∃ c : ℕ, n = q.num * c ∧ d = q.den * c := by
  obtain ⟨c, _, hn, he⟩ := normalize_num_den' n d hd
  exact ⟨c, qdf ▸ hn, qdf ▸ he⟩

theorem add_den_dvd_lcm (q₁ q₂ : ℚ) : (q₁ + q₂).den ∣ q₁.den.lcm q₂.den := by
  rw [add_def, normalize_eq, Nat.div_dvd_iff_dvd_mul (Nat.gcd_dvd_right _ _)
    (Nat.gcd_pos_of_pos_right _ (by simp [Nat.pos_iff_ne_zero])), ← Nat.gcd_mul_lcm,
    mul_dvd_mul_iff_right (Nat.lcm_ne_zero (by simp) (by simp)), Nat.dvd_gcd_iff]
  refine ⟨?_, dvd_mul_right _ _⟩
  rw [← Int.natCast_dvd_natCast, Int.dvd_natAbs]
  apply Int.dvd_add
    <;> apply dvd_mul_of_dvd_right <;> rw [Int.natCast_dvd_natCast]
    <;> [exact Nat.gcd_dvd_right _ _; exact Nat.gcd_dvd_left _ _]

theorem sub_den_dvd_lcm (q₁ q₂ : ℚ) : (q₁ - q₂).den ∣ q₁.den.lcm q₂.den := by
  simpa only [sub_eq_add_neg, neg_den] using add_den_dvd_lcm q₁ (-q₂)

theorem add_den_dvd (q₁ q₂ : ℚ) : (q₁ + q₂).den ∣ q₁.den * q₂.den :=
  (add_den_dvd_lcm _ _).trans (Nat.lcm_dvd_mul _ _)

theorem sub_den_dvd (q₁ q₂ : ℚ) : (q₁ - q₂).den ∣ q₁.den * q₂.den :=
  (sub_den_dvd_lcm _ _).trans (Nat.lcm_dvd_mul _ _)

theorem mul_den_dvd (q₁ q₂ : ℚ) : (q₁ * q₂).den ∣ q₁.den * q₂.den := by
  rw [mul_def, normalize_eq]
  apply Nat.div_dvd_of_dvd
  apply Nat.gcd_dvd_right

theorem mul_num (q₁ q₂ : ℚ) :
    (q₁ * q₂).num = q₁.num * q₂.num / Nat.gcd (q₁.num * q₂.num).natAbs (q₁.den * q₂.den) := by
  rw [mul_def, normalize_eq]

theorem mul_den (q₁ q₂ : ℚ) :
    (q₁ * q₂).den =
      q₁.den * q₂.den / Nat.gcd (q₁.num * q₂.num).natAbs (q₁.den * q₂.den) := by
  rw [mul_def, normalize_eq]

@[simp]
theorem add_intCast_den (q : ℚ) (n : ℤ) : (q + n).den = q.den := by
  apply Nat.dvd_antisymm
  · simpa using add_den_dvd q n
  · simpa using add_den_dvd (q + n) (-n)

@[simp]
theorem intCast_add_den (n : ℤ) (q : ℚ) : (n + q).den = q.den := by
  rw [add_comm, add_intCast_den]

@[simp]
theorem sub_intCast_den (q : ℚ) (n : ℤ) : (q - n).den = q.den := by
  rw [sub_eq_add_neg, ← Int.cast_neg, add_intCast_den]

@[simp]
theorem intCast_sub_den (n : ℤ) (q : ℚ) : (n - q).den = q.den := by
  rw [sub_eq_add_neg, intCast_add_den, neg_den]

@[simp]
theorem add_natCast_den (q : ℚ) (n : ℕ) : (q + n).den = q.den := mod_cast add_intCast_den q n

@[simp]
theorem natCast_add_den (n : ℕ) (q : ℚ) : (n + q).den = q.den := mod_cast intCast_add_den n q

@[simp]
theorem sub_natCast_den (q : ℚ) (n : ℕ) : (q - n).den = q.den := mod_cast sub_intCast_den q n

@[simp]
theorem natCast_sub_den (n : ℕ) (q : ℚ) : (n - q).den = q.den := mod_cast intCast_sub_den n q

@[simp] theorem add_ofNat_den (q : ℚ) (n : ℕ) : (q + ofNat(n)).den = q.den := add_natCast_den q n
@[simp] theorem ofNat_add_den (n : ℕ) (q : ℚ) : (ofNat(n) + q).den = q.den := natCast_add_den n q
@[simp] theorem sub_ofNat_den (q : ℚ) (n : ℕ) : (q - ofNat(n)).den = q.den := sub_natCast_den ..
@[simp] theorem ofNat_sub_den (n : ℕ) (q : ℚ) : (ofNat(n) - q).den = q.den := natCast_sub_den ..

/-- A version of `Rat.mul_den` without division. -/
theorem den_mul_den_eq_den_mul_gcd (q₁ q₂ : ℚ) :
    q₁.den * q₂.den = (q₁ * q₂).den * ((q₁.num * q₂.num).natAbs.gcd (q₁.den * q₂.den)) := by
  rw [mul_den]
  exact ((Nat.dvd_iff_div_mul_eq _ _).mp (Nat.gcd_dvd_right _ _)).symm

/-- A version of `Rat.mul_num` without division. -/
theorem num_mul_num_eq_num_mul_gcd (q₁ q₂ : ℚ) :
    q₁.num * q₂.num = (q₁ * q₂).num * ((q₁.num * q₂.num).natAbs.gcd (q₁.den * q₂.den)) := by
  rw [mul_num]
  refine (Int.ediv_mul_cancel ?_).symm
  rw [← Int.dvd_natAbs]
  exact Int.ofNat_dvd.mpr (Nat.gcd_dvd_left _ _)

theorem mul_self_num (q : ℚ) : (q * q).num = q.num * q.num := by
  rw [mul_num, Int.natAbs_mul, Nat.Coprime.gcd_eq_one, Int.ofNat_one, Int.ediv_one]
  exact (q.reduced.mul_right q.reduced).mul_left (q.reduced.mul_right q.reduced)

theorem mul_self_den (q : ℚ) : (q * q).den = q.den * q.den := by
  rw [Rat.mul_den, Int.natAbs_mul, Nat.Coprime.gcd_eq_one, Nat.div_one]
  exact (q.reduced.mul_right q.reduced).mul_left (q.reduced.mul_right q.reduced)

theorem add_num_den (q r : ℚ) : q + r =
    fraction (q.num * r.den + r.num * q.den) (q.den * r.den)
      (Nat.mul_ne_zero q.den_nz r.den_nz) := Rat.add_def _ _

theorem isSquare_iff {q : ℚ} : IsSquare q ↔ IsSquare q.num ∧ IsSquare q.den := by
  constructor
  · rintro ⟨qr, rfl⟩
    rw [Rat.mul_self_num, mul_self_den]
    simp only [IsSquare.mul_self, and_self]
  · rintro ⟨⟨nr, hnr⟩, ⟨dr, hdr⟩⟩
    have hd : dr ≠ 0 := by
      intro h
      exact q.den_nz (hdr.trans (by simp [h]))
    refine ⟨fraction nr dr hd, ?_⟩
    simp only [fraction, Rat.normalize_mul_normalize, ← hnr, ← hdr, Rat.normalize_self]

@[norm_cast, simp]
theorem isSquare_natCast_iff {n : ℕ} : IsSquare (n : ℚ) ↔ IsSquare n := by
  simp_rw [isSquare_iff, num_natCast, den_natCast, IsSquare.one, and_true,
    Int.isSquare_natCast_iff]

@[norm_cast, simp]
theorem isSquare_intCast_iff {z : ℤ} : IsSquare (z : ℚ) ↔ IsSquare z := by
  simp_rw [isSquare_iff, num_intCast, den_intCast, IsSquare.one, and_true]

@[simp] theorem isSquare_ofNat_iff {n : ℕ} :
    IsSquare (ofNat(n) : ℚ) ↔ IsSquare (OfNat.ofNat n : ℕ) := isSquare_natCast_iff

theorem exists_eq_mul_div_num_and_eq_mul_div_den (n : ℤ) {d : ℤ} {hd : IsUnit (d : ℚ)} :
    ∃ c : ℤ, n = c * ((n : ℚ) / d).num ∧ (d : ℤ) = c * ((n : ℚ) / d).den := by
  have hq : (n : ℚ) / d * d = n := div_mul_cancel₀ _
  generalize (n : ℚ) / d = q at hq ⊢
  have key : q.num * d = n * q.den := by
    have h : (q.num : ℚ) * d = n * q.den := by
      rw [← hq, ← mul_den_eq_num q, mul_right_comm]
    exact_mod_cast h
  have hden : (q.den : ℤ) ∣ d := by
    rw [Int.ofNat_dvd_left]
    apply Nat.Coprime.dvd_of_dvd_mul_left q.reduced.symm
    rw [← Int.natAbs_mul, key, Int.natAbs_mul, Int.natAbs_natCast]
    exact Nat.dvd_mul_left _ _
  obtain ⟨c, hc⟩ := hden
  refine ⟨c, ?_, by rw [hc, Int.mul_comm]⟩
  rw [hc, Int.mul_left_comm, Int.mul_comm n] at key
  rw [Int.mul_comm]
  exact (Int.eq_of_mul_eq_mul_left (mod_cast q.den_nz) key).symm

private theorem normalize_cross (n : ℤ) (d : ℕ) (hd : d ≠ 0) :
    (normalize n d hd).num * d = n * (normalize n d hd).den := by
  obtain ⟨g, _, hn, he⟩ := normalize_num_den' n d hd
  have hn' := hn
  have he' := congrArg (fun x : ℕ => (x : ℤ)) he
  rw [Int.natCast_mul] at he'
  conv => lhs; rhs; rw [he']
  conv => rhs; lhs; rw [hn']
  simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]

theorem mul_num_den' (q r : ℚ) :
    (q * r).num * q.den * r.den = q.num * r.num * (q * r).den := by
  simpa only [Rat.mul_def, Int.natCast_mul, Int.mul_assoc] using
    normalize_cross (q.num * r.num) (q.den * r.den) (Nat.mul_ne_zero q.den_nz r.den_nz)

theorem add_num_den' (q r : ℚ) :
    (q + r).num * q.den * r.den = (q.num * r.den + r.num * q.den) * (q + r).den := by
  simpa only [Rat.add_def, Int.natCast_mul, Int.mul_assoc] using
    normalize_cross (q.num * r.den + r.num * q.den) (q.den * r.den)
      (Nat.mul_ne_zero q.den_nz r.den_nz)

theorem substr_num_den' (q r : ℚ) :
    (q-r).num * q.den * r.den = (q.num * r.den-r.num * q.den) * (q-r).den := by
  rw [sub_eq_add_neg, sub_eq_add_neg, ← neg_mul, ← num_neg_eq_neg_num, ← den_neg_eq_den r,
    add_num_den' q (-r)]

protected theorem inv_neg (q : ℚ) {hq : IsUnit (-q)} : (-q)⁻¹ = -q⁻¹ := by
  refine inv_eq_of_mul_eq_one_right₀ ?_
  rw [neg_mul_neg, mul_inv_cancel₀]

/-- The inverse of a rational in reduced form: the sign moves to the numerator. -/
private theorem inv_eq_mk' (q : ℚ) {hq : IsUnit q} :
    q⁻¹ = ⟨q.num.sign * q.den, q.num.natAbs,
      Int.natAbs_ne_zero.mpr (num_ne_zero.mpr hq.ne_zero), by
        rw [Int.natAbs_mul, Int.natAbs_sign_of_ne_zero (num_ne_zero.mpr hq.ne_zero),
          Int.natAbs_natCast, Nat.one_mul]
        exact q.reduced.symm⟩ := by
  rw [inv_eq_of_mul_eq_one_right₀ (mul_reciprocal q hq.ne_zero)]
  exact normalize_eq_mk' _ _ _ _

private theorem num_inv_eq (q : ℚ) {hq : IsUnit q} : q⁻¹.num = q.num.sign * q.den := by
  rw [inv_eq_mk']

theorem den_inv_of_ne_zero {q : ℚ} {hq : IsUnit q} : (q⁻¹).den = q.num.natAbs := by
  rw [inv_eq_mk']

/-- A quotient of coprime integers by a positive denominator is in reduced form. -/
private theorem intCast_div_natCast_eq_mk' {a : ℤ} {n : ℕ} (hn : n ≠ 0) (h : a.natAbs.Coprime n)
    {hb : IsUnit ((n : ℤ) : ℚ)} : (a : ℚ) / ((n : ℤ) : ℚ) = ⟨a, n, hn, h⟩ :=
  div_eq_iff.mpr <| by rw [Int.cast_natCast]; exact (mul_den_eq_num ⟨a, n, hn, h⟩).symm

theorem num_div_eq_of_coprime {a b : ℤ} (hb0 : 0 < b) (h : Nat.Coprime a.natAbs b.natAbs) :
    (Checked.div (a : ℚ) b (Ne.isUnit (num_ne_zero.mp hb0.ne'))).num = a := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hb0.le
  rw [Int.natAbs_natCast] at h
  rw [intCast_div_natCast_eq_mk' (Int.natCast_pos.mp hb0).ne' h]

theorem den_div_eq_of_coprime {a b : ℤ} (hb0 : 0 < b) (h : Nat.Coprime a.natAbs b.natAbs) :
    ((Checked.div (a : ℚ) b (Ne.isUnit (num_ne_zero.mp hb0.ne'))).den : ℤ) = b := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hb0.le
  rw [Int.natAbs_natCast] at h
  rw [intCast_div_natCast_eq_mk' (Int.natCast_pos.mp hb0).ne' h]

theorem div_int_inj {a b c d : ℤ} (hb0 : 0 < b) (hd0 : 0 < d) (h1 : Nat.Coprime a.natAbs b.natAbs)
    (h2 : Nat.Coprime c.natAbs d.natAbs)
    (h : Checked.div (a : ℚ) b (Ne.isUnit (num_ne_zero.mp hb0.ne')) =
      Checked.div (c : ℚ) d (Ne.isUnit (num_ne_zero.mp hd0.ne'))) : a = c ∧ b = d := by
  apply And.intro
  · rw [← num_div_eq_of_coprime hb0 h1, h, num_div_eq_of_coprime hd0 h2]
  · rw [← den_div_eq_of_coprime hb0 h1, h, den_div_eq_of_coprime hd0 h2]

@[norm_cast]
theorem intCast_div_self (n : ℤ) {hn : IsUnit (n : ℚ)} : ((n / n : ℤ) : ℚ) = n / n := by
  have h : n ≠ 0 := fun h ↦ hn.ne_zero (by simp [h])
  rw [Int.ediv_self h, Int.cast_one, div_self]

@[norm_cast]
theorem natCast_div_self (n : ℕ) {hn : IsUnit (n : ℚ)} : ((n / n : ℕ) : ℚ) = n / n := by
  have h : n ≠ 0 := fun h ↦ hn.ne_zero (by simp [h])
  rw [Nat.div_self (Nat.pos_of_ne_zero h), Nat.cast_one, div_self]

theorem intCast_div (a b : ℤ) {hb : IsUnit (b : ℚ)} (h : b ∣ a) : ((a / b : ℤ) : ℚ) = a / b := by
  obtain ⟨c, rfl⟩ := h
  have hb' : b ≠ 0 := fun h ↦ hb.ne_zero (by simp [h])
  rw [Int.mul_ediv_cancel_left c hb', Int.cast_mul, mul_div_cancel_left₀]

theorem natCast_div (a b : ℕ) {hb : IsUnit (b : ℚ)} (h : b ∣ a) : ((a / b : ℕ) : ℚ) = a / b := by
  obtain ⟨c, rfl⟩ := h
  have hb' : b ≠ 0 := fun h ↦ hb.ne_zero (by simp [h])
  rw [Nat.mul_div_cancel_left c (Nat.pos_of_ne_zero hb'), Nat.cast_mul, mul_div_cancel_left₀]

theorem den_div_intCast_eq_one_iff (m n : ℤ) {hn : IsUnit (n : ℚ)} :
    ((m : ℚ) / n).den = 1 ↔ n ∣ m := by
  constructor
  · rw [Rat.den_eq_one_iff, eq_div_iff]
    exact mod_cast (Dvd.intro_left _)
  · intro h
    rw [← intCast_div m n h]
    exact den_intCast _

theorem den_div_natCast_eq_one_iff (m n : ℕ) {hn : IsUnit (n : ℚ)} :
    ((m : ℚ) / n).den = 1 ↔ n ∣ m :=
  (den_div_intCast_eq_one_iff m n (hn := hn)).trans Int.ofNat_dvd

theorem inv_intCast_num_of_pos {a : ℤ} (ha0 : 0 < a) :
    (Checked.inv (a : ℚ) (Ne.isUnit (num_ne_zero.mp ha0.ne'))).num = 1 := by
  rw [num_inv_eq]
  simp [Int.sign_eq_one_of_pos ha0]

theorem inv_natCast_num_of_pos {a : ℕ} (ha0 : 0 < a) :
    (Checked.inv (a : ℚ) (Nat.cast_ne_zero.mpr ha0.ne').isUnit).num = 1 := by
  rw [num_inv_eq]
  simp [Int.sign_eq_one_of_pos (Int.natCast_pos.mpr ha0)]

theorem inv_intCast_den_of_pos {a : ℤ} (ha0 : 0 < a) :
    ((Checked.inv (a : ℚ) (Ne.isUnit (num_ne_zero.mp ha0.ne'))).den : ℤ) = a := by
  rw [den_inv_of_ne_zero, num_intCast, Int.natAbs_of_nonneg ha0.le]

theorem inv_natCast_den_of_pos {a : ℕ} (ha0 : 0 < a) :
    (Checked.inv (a : ℚ) (Nat.cast_ne_zero.mpr ha0.ne').isUnit).den = a := by
  rw [den_inv_of_ne_zero, num_natCast, Int.natAbs_natCast]

theorem inv_intCast_num (a : ℤ) {ha : IsUnit (a : ℚ)} : (a : ℚ)⁻¹.num = Int.sign a := by
  rw [num_inv_eq]
  simp

theorem inv_natCast_num (a : ℕ) {ha : IsUnit (a : ℚ)} : (a : ℚ)⁻¹.num = Int.sign a := by
  rw [num_inv_eq]
  simp

theorem inv_ofNat_num (a : ℕ) [a.AtLeastTwo] : (ofNat(a) : ℚ)⁻¹.num = 1 := by
  have : 2 ≤ a := Nat.AtLeastTwo.prop
  rw [num_inv_eq]
  simp only [num_ofNat, den_ofNat, Nat.cast_one, Int.mul_one, Int.sign_eq_one_iff_pos]
  change 0 < (a : ℤ)
  lia

theorem inv_intCast_den (a : ℤ) {ha : IsUnit (a : ℚ)} : (a : ℚ)⁻¹.den = a.natAbs := by
  rw [den_inv_of_ne_zero, num_intCast]

theorem inv_natCast_den (a : ℕ) {ha : IsUnit (a : ℚ)} : (a : ℚ)⁻¹.den = a := by
  rw [den_inv_of_ne_zero, num_natCast, Int.natAbs_natCast]

theorem inv_ofNat_den (a : ℕ) [a.AtLeastTwo] : (ofNat(a) : ℚ)⁻¹.den = OfNat.ofNat a := by
  rw [den_inv_of_ne_zero, num_ofNat]
  rfl

protected theorem «forall» {p : ℚ → Prop} :
    (∀ r, p r) ↔ ∀ (a b : ℤ) (hb : b ≠ 0), p (a / b) where
  mp h _ _ _ := h _
  mpr h q := by
    have key : (q.num : ℚ) / ((q.den : ℤ) : ℚ) = q := by
      rw [div_eq_iff, Int.cast_natCast]
      exact (mul_den_eq_num q).symm
    simpa only [key] using h q.num q.den (mod_cast q.den_ne_zero)

protected theorem «exists» {p : ℚ → Prop} :
    (∃ r, p r) ↔ ∃ (a b : ℤ) (hb : b ≠ 0), p (a / b) := by
  simpa using Rat.forall (p := (¬ p ·)).not

/-!
### Denominator as `ℕ+`
-/


section PNatDen

/-- Denominator as `ℕ+`. -/
def pnatDen (x : ℚ) : ℕ+ :=
  ⟨x.den, x.pos⟩

@[simp]
theorem coe_pnatDen (x : ℚ) : (x.pnatDen : ℕ) = x.den :=
  rfl

theorem pnatDen_eq_iff_den_eq {x : ℚ} {n : ℕ+} : x.pnatDen = n ↔ x.den = ↑n :=
  Subtype.ext_iff

@[simp]
theorem pnatDen_one : (1 : ℚ).pnatDen = 1 :=
  rfl

@[simp]
theorem pnatDen_zero : (0 : ℚ).pnatDen = 1 :=
  rfl

end PNatDen

end Rat
