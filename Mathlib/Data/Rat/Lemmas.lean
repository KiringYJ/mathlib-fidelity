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
