/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify

/-! # `norm_num` extension for `Irrational`

This module defines a `norm_num` extension for `Irrational x ^ y` for rational `x` and `y`. It also
supports `Irrational √x` expressions.

## Implementation details
To prove that `(a / b) ^ (p / q)` is irrational, we reduce the problem to showing that `(a / b) ^ p`
is not a `q`-th power of any rational number. This, in turn, reduces to proving that either `a` or
`b` is not a `q`-th power of a natural number, assuming `p` and `q` are coprime.
To show that a given `n : ℕ` is not a `q`-th power, we find a natural number `k`
such that `k ^ q < n < (k + 1) ^ q`, using binary search.

## TODO
Disprove `Irrational x` for rational `x`.

-/

public meta section

namespace Mathlib.Meta

namespace NormNum

open Qq Lean Elab.Tactic Mathlib.Meta.NormNum

section lemmas

private theorem irrational_rpow_rat_of_not_power {q : ℚ} {a b : ℕ}
    (h : ∀ p : ℚ, q ^ a ≠ p ^ b) (hb : 0 < b) (hq : 0 ≤ q) :
    Irrational (Real.rpow q (Rat.fraction a b hb.ne' : ℚ)) := by
  simp only [Rat.fraction_eq_div, Int.cast_natCast, Irrational, Rat.cast_div, Rat.cast_natCast,
    Real.rpow_eq_pow, Set.mem_range, not_exists]
  intro x hx
  absurd h x
  rify
  rw [hx, ← Real.rpow_mul_natCast (by simpa), div_mul_cancel₀]; simp

private theorem not_power_nat_pow {n p q : ℕ} (h_coprime : p.Coprime q) (hq : 0 < q)
    (h : ∀ m, n ≠ m ^ q) (m : ℕ) : n ^ p ≠ m ^ q := by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simpa [hq.ne'] using h 0
  contrapose! h
  let f := n.factorization.mapRange (fun e ↦ Nat.euclideanDiv e q hq.ne') <| by
    simp [Nat.euclideanDiv_eq_core]
  suffices hf : n.factorization = q • f by
    have hf0 : f 0 = 0 := by simpa [hq.ne'] using congr($hf 0)
    refine ⟨f.prod (· ^ ·), Nat.factorization_inj hn (by simp [hf0]) ?_⟩
    rwa [Nat.factorization_pow, n.factorization_prod_pow_eq_self_of_le_factorization ?_]
    exact hf ▸ le_self_nsmul zero_le (by lia)
  ext z
  rw [Finsupp.smul_apply, smul_eq_mul, Finsupp.mapRange_apply, Nat.euclideanDiv_eq_core,
    Nat.mul_div_cancel']
  simpa using h_coprime.symm.dvd_of_dvd_mul_left ⟨_, by simpa using congr(Nat.factorization $h z)⟩

private theorem not_power_nat_of_bounds {n k d : ℕ}
    (h_left : k ^ d < n) (h_right : n < (k + 1) ^ d) {m : ℕ} :
    n ≠ m ^ d := by
  intro h
  rw [h] at h_left h_right
  have : k < m := lt_of_pow_lt_pow_left' d h_left
  have : m < k + 1 := lt_of_pow_lt_pow_left' d h_right
  lia

private theorem not_power_nat_pow_of_bounds {n k p q : ℕ}
    (hq : 0 < q) (h_coprime : p.Coprime q) (h_left : k ^ q < n) (h_right : n < (k + 1) ^ q)
    (m : ℕ) :
    n ^ p ≠ m ^ q := by
  apply not_power_nat_pow h_coprime hq
  intro m
  apply not_power_nat_of_bounds h_left h_right

private lemma eq_of_mul_eq_mul_of_coprime_aux {a b x y : ℕ} (hab : a.Coprime b)
    (h : a * x = b * y) : a ∣ y := Nat.Coprime.dvd_of_dvd_mul_left hab (Dvd.intro x h)

private lemma eq_of_mul_eq_mul_of_coprime {a b x y : ℕ} (hab : a.Coprime b) (hxy : x.Coprime y)
    (h : a * x = b * y) : a = y := by
  apply Nat.dvd_antisymm
  · exact eq_of_mul_eq_mul_of_coprime_aux hab h
  · exact eq_of_mul_eq_mul_of_coprime_aux (x := b) hxy.symm (by rw [mul_comm, ← h, mul_comm])

private theorem fraction_power_parts {a b p d : ℕ} (hb : b ≠ 0)
    (hab : a.Coprime b) {r : ℚ} (h : Rat.fraction a b hb ^ p = r ^ d) :
    a ^ p = r.num.natAbs ^ d ∧ b ^ p = r.den ^ d := by
  have ha := congrArg (fun x : ℚ ↦ x ^ p) (Rat.fraction_mul_den (a : ℤ) b hb)
  have hr := congrArg (fun x : ℚ ↦ x ^ d) (Rat.mul_den_eq_num r)
  simp only [Int.cast_natCast, mul_pow] at ha hr
  have hc : (a : ℚ) ^ p * (r.den : ℚ) ^ d = (b : ℚ) ^ p * (r.num : ℚ) ^ d := by
    rw [← ha, ← hr, h]
    ring
  have hZ : (a : ℤ) ^ p * (r.den : ℤ) ^ d = (b : ℤ) ^ p * r.num ^ d := by
    exact_mod_cast hc
  have hN : a ^ p * r.den ^ d = b ^ p * r.num.natAbs ^ d := by
    simpa [Int.natAbs_mul, Int.natAbs_pow] using congrArg Int.natAbs hZ
  have h₁ : (a ^ p).Coprime (b ^ p) := Nat.Coprime.pow _ _ hab
  have h₂ : (r.den ^ d).Coprime (r.num.natAbs ^ d) := Nat.Coprime.pow _ _ (Rat.reduced r).symm
  exact ⟨eq_of_mul_eq_mul_of_coprime h₁ h₂ hN,
    eq_of_mul_eq_mul_of_coprime h₁.symm h₂.symm hN.symm⟩

private theorem irrational_rpow_of_bad_part {x y : ℝ} {a b p d : ℕ}
    (hx : IsNNRat x a b) (hy : IsNNRat y p d) (hab : a.Coprime b)
    (bad : 0 < d → (∀ m : ℕ, a ^ p ≠ m ^ d) ∨ (∀ m : ℕ, b ^ p ≠ m ^ d)) :
    Irrational (x ^ y) := by
  have hb : b ≠ 0 := Nat.cast_ne_zero.mp hx.den_nz
  have hd : d ≠ 0 := Nat.cast_ne_zero.mp hy.den_nz
  have hdpos := Nat.pos_of_ne_zero hd
  rw [hx.eq_cast_fraction x a b hb, hy.eq_cast_fraction y p d hd]
  refine irrational_rpow_rat_of_not_power (q := Rat.fraction a b hb) ?_ hdpos
    (Rat.fraction_nonneg (Int.natCast_nonneg _) _ hb)
  intro r hr
  obtain ⟨hnum, hden⟩ := fraction_power_parts hb hab hr
  rcases bad hdpos with hn | hn
  · exact hn _ hnum
  · exact hn _ hden

theorem irrational_rpow_rat_rat_of_num {x y : ℝ} {x_num x_den y_num y_den k_num : ℕ}
    (hx_isNNRat : IsNNRat x x_num x_den)
    (hy_isNNRat : IsNNRat y y_num y_den)
    (hx_coprime : Nat.Coprime x_num x_den)
    (hy_coprime : Nat.Coprime y_num y_den)
    (hn1 : k_num ^ y_den < x_num)
    (hn2 : x_num < (k_num + 1) ^ y_den) :
    Irrational (x ^ y) := by
  apply irrational_rpow_of_bad_part hx_isNNRat hy_isNNRat hx_coprime
  intro hd
  exact Or.inl (not_power_nat_pow_of_bounds hd hy_coprime hn1 hn2)

theorem irrational_rpow_rat_rat_of_den {x y : ℝ} {x_num x_den y_num y_den k_den : ℕ}
    (hx_isNNRat : IsNNRat x x_num x_den)
    (hy_isNNRat : IsNNRat y y_num y_den)
    (hx_coprime : Nat.Coprime x_num x_den)
    (hy_coprime : Nat.Coprime y_num y_den)
    (hd1 : k_den ^ y_den < x_den)
    (hd2 : x_den < (k_den + 1) ^ y_den) :
    Irrational (x ^ y) := by
  apply irrational_rpow_of_bad_part hx_isNNRat hy_isNNRat hx_coprime
  intro hd
  exact Or.inr (not_power_nat_pow_of_bounds hd hy_coprime hd1 hd2)

theorem irrational_rpow_nat_rat {x y : ℝ} {x_num y_num y_den k : ℕ}
    (hx_isNat : IsNat x x_num)
    (hy_isNNRat : IsNNRat y y_num y_den)
    (hy_coprime : Nat.Coprime y_num y_den)
    (hn1 : k ^ y_den < x_num)
    (hn2 : x_num < (k + 1) ^ y_den) :
    Irrational (x ^ y) :=
  irrational_rpow_rat_rat_of_num hx_isNat.to_isNNRat hy_isNNRat (by simp) hy_coprime hn1 hn2

theorem irrational_sqrt_rat_of_num {x : ℝ} {num den num_k : ℕ}
    (hx_isNNRat : IsNNRat x num den)
    (hx_coprime : Nat.Coprime num den)
    (hn1 : num_k ^ 2 < num)
    (hn2 : num < (num_k + 1) ^ 2) :
    Irrational (Real.sqrt x) := by
  rw [Real.sqrt_eq_rpow]
  apply irrational_rpow_rat_rat_of_num hx_isNNRat (y_num := 1) (y_den := 2) _ hx_coprime (by simp)
    hn1 hn2
  exact ⟨Invertible.mk (1/2) (by simp) (by simp), by simp⟩

theorem irrational_sqrt_rat_of_den {x : ℝ} {num den den_k : ℕ}
    (hx_isNNRat : IsNNRat x num den)
    (hx_coprime : Nat.Coprime num den)
    (hd1 : den_k ^ 2 < den)
    (hd2 : den < (den_k + 1) ^ 2) :
    Irrational (Real.sqrt x) := by
  rw [Real.sqrt_eq_rpow]
  apply irrational_rpow_rat_rat_of_den hx_isNNRat (y_num := 1) (y_den := 2) _ hx_coprime (by simp)
    hd1 hd2
  exact ⟨Invertible.mk (1/2) (by simp) (by simp), by simp⟩

theorem irrational_sqrt_nat {x : ℝ} {n k : ℕ}
    (hx_isNat : IsNat x n)
    (hn1 : k ^ 2 < n)
    (hn2 : n < (k + 1) ^ 2) :
    Irrational (Real.sqrt x) :=
  irrational_sqrt_rat_of_num hx_isNat.to_isNNRat (by simp) hn1 hn2

end lemmas

/-- To prove that `m` is not `n`-power (and thus `m ^ (1/n)` is irrational), we find `k` such that
`k ^ n < m < (k + 1) ^ n`. -/
structure NotPowerCertificate (m n : Q(ℕ)) where
  /-- Natural `k` such that `k ^ n < m < (k + 1) ^ n`. -/
  k : Q(ℕ)
  /-- Proof of `k ^ n < m`. -/
  pf_left : Q($k ^ $n < $m)
  /-- Proof of `m < (k + 1) ^ n`. -/
  pf_right : Q($m < ($k + 1) ^ $n)

/-- Finds `k` such that `k ^ n < m < (k + 1) ^ n` using bisection method. It assumes `n > 0`. -/
def findNotPowerCertificateCore (m n : ℕ) : Option ℕ := Id.run do
  let mut left := 0
  let mut right := m + 1
  while right - left > 1 do
    let middle := Nat.euclideanDiv (left + right) 2
    if middle ^ n ≤ m then
      left := middle
    else
      right := middle
  if left ^ n < m then
    return some left
  return none

/-- Finds `NotPowerCertificate` showing that `m` is not `n`-power. -/
def findNotPowerCertificate (m n : Q(ℕ)) : MetaM (NotPowerCertificate m n) := do
  let .isNat (_ : Q(AddMonoidWithOne ℕ)) m _ ← derive m | failure
  let .isNat (_ : Q(AddMonoidWithOne ℕ)) n _ ← derive n | failure
  let mVal := m.natLit!
  let nVal := n.natLit!
  let some k := findNotPowerCertificateCore mVal nVal | failure
  let .isBool true pf_left ← derive q($k ^ $n < $m) | failure
  let .isBool true pf_right ← derive q($m < ($k + 1) ^ $n) | failure
  return ⟨q($k), pf_left, pf_right⟩

/-- `norm_num` extension that proves `Irrational x ^ y` for rational `y`. `x` may be
natural or rational. -/
@[norm_num Irrational (_ ^ (_ : ℝ))]
def evalIrrationalRpow : NormNumExt where eval {u α} e :=
  match u, α, e with
  | 0, ~q(Prop), ~q(Irrational (($x : ℝ) ^ ($y : ℝ))) => do
    let .isNNRat sℝ _ y_num y_den y_isNNRat ← derive y | failure
    let ⟨gy, hy_coprime⟩ := proveNatGCD y_num y_den
    if gy.natLit! != 1 then failure
    let _ : $gy =Q 1 := ⟨⟩
    match ← derive x with
    | .isNat sℝ ex x_isNat =>
      let cert ← findNotPowerCertificate q($ex) y_den
      assumeInstancesCommute
      return .isTrue q(irrational_rpow_nat_rat $x_isNat $y_isNNRat $hy_coprime
        $cert.pf_left $cert.pf_right)
    | .isNNRat sℝ _ x_num x_den x_isNNRat =>
      let ⟨gx, hx_coprime⟩ := proveNatGCD x_num x_den
      if gx.natLit! != 1 then failure
      let _ : $gx =Q 1 := ⟨⟩
      let hx_isNNRat' : Q(IsNNRat $x $x_num $x_den) := x_isNNRat
      let hy_isNNRat' : Q(IsNNRat $y $y_num $y_den) := y_isNNRat
      try
        let numCert ← findNotPowerCertificate q($x_num) y_den
        assumeInstancesCommute
        return Result.isTrue q(irrational_rpow_rat_rat_of_num $hx_isNNRat' $hy_isNNRat'
          $hx_coprime $hy_coprime $numCert.pf_left $numCert.pf_right)
      catch _ =>
        let denCert ← findNotPowerCertificate q($x_den) y_den
        assumeInstancesCommute
        return Result.isTrue q(irrational_rpow_rat_rat_of_den $hx_isNNRat' $hy_isNNRat'
          $hx_coprime $hy_coprime $denCert.pf_left $denCert.pf_right)
    | _ => failure
  | _, _, _ => failure

/-- `norm_num` extension that proves `Irrational √x` for rational `x`. -/
@[norm_num Irrational (Real.sqrt _)]
def evalIrrationalSqrt : NormNumExt where eval {u α} e := do
  match u, α, e with
  | 0, ~q(Prop), ~q(Irrational (√$x)) => do
    match ← derive x with
    | .isNat sℝ ex pf =>
      let cert ← findNotPowerCertificate ex q(nat_lit 2)
      assumeInstancesCommute
      return .isTrue q(irrational_sqrt_nat $pf $cert.pf_left $cert.pf_right)
    | .isNNRat sℝ eq en ed pf =>
      let ⟨g, pf_coprime⟩ := proveNatGCD en ed
      if g.natLit! != 1 then failure
      let _ : $g =Q 1 := ⟨⟩
      try
        let numCert ← findNotPowerCertificate en q(nat_lit 2)
        assumeInstancesCommute
        return Result.isTrue
          q(irrational_sqrt_rat_of_num $pf $pf_coprime $numCert.pf_left $numCert.pf_right)
      catch _ =>
        let denCert ← findNotPowerCertificate ed q(nat_lit 2)
        assumeInstancesCommute
        return Result.isTrue
          q(irrational_sqrt_rat_of_den $pf $pf_coprime $denCert.pf_left $denCert.pf_right)
    | _ => failure
  | _, _, _ => failure

end NormNum

end Mathlib.Meta
