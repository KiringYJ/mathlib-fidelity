/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Snir Broshi
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.RingTheory.Int.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Qify

/-!
# Complex roots of unity

In this file we show that the `n`-th complex roots of unity
are exactly the complex numbers `exp (2 * π * I * (i / n))` for `i ∈ Finset.range n`.

## Main declarations

* `Complex.mem_rootsOfUnity`: the complex `n`-th roots of unity are exactly the
  complex numbers of the form `exp (2 * π * I * (i / n))` for some `i < n`.
* `Complex.card_rootsOfUnity`: the number of `n`-th roots of unity is exactly `n`.
* `Complex.norm_rootOfUnity_eq_one`: A complex root of unity has norm `1`.

-/

public section


namespace Complex

open Polynomial Real

open scoped Nat Real

theorem isPrimitiveRoot_I : IsPrimitiveRoot I 4 :=
  .mk_of_lt I zero_lt_four I_pow_four fun l hl0 hl4 ↦ by
    interval_cases l <;> norm_num [Complex.ext_iff]

theorem isPrimitiveRoot_neg_I : IsPrimitiveRoot (-I) 4 := by
  have h := IsPrimitiveRoot.coe_units_iff.mpr
    (IsPrimitiveRoot.isUnit_unit (by decide) isPrimitiveRoot_I).inv
  simpa only [Units.val_inv_eq_inv_val₀, IsUnit.unit_spec, inv_I] using h

theorem isPrimitiveRoot_exp_of_isCoprime (i : ℤ) (n : ℕ) (h0 : n ≠ 0) (hi : IsCoprime i n) :
    IsPrimitiveRoot (exp (2 * π * I * ((i : ℂ) / (n : ℂ)))) n := by
  rw [IsPrimitiveRoot.iff_def]
  simp only [← exp_nat_mul, exp_eq_one_iff]
  constructor
  · use i
    simp (discharger := norm_cast) [field]
  · simp only [forall_exists_index]
    have hn0 : (n : ℂ) ≠ 0 := mod_cast h0
    rintro l k hk
    field_simp at hk
    have hmul : i * (l : ℤ) = (n : ℤ) * k := by exact_mod_cast hk
    have hdvd : (n : ℤ) ∣ (l : ℤ) * i := ⟨k, (mul_comm _ _).trans hmul⟩
    exact Int.natCast_dvd_natCast.mp (hi.symm.dvd_of_dvd_mul_right hdvd)

theorem isPrimitiveRoot_exp_of_coprime (i n : ℕ) (h0 : n ≠ 0) (hi : i.Coprime n) :
    IsPrimitiveRoot (exp (2 * π * I * ((i : ℂ) / (n : ℂ)))) n :=
  isPrimitiveRoot_exp_of_isCoprime _ _ h0 hi.isCoprime

theorem isPrimitiveRoot_exp_rat (q : ℚ) : IsPrimitiveRoot (exp (2 * π * I * q)) q.den := by
  convert!
    isPrimitiveRoot_exp_of_isCoprime _ _ q.den_nz <| Int.isCoprime_iff_nat_coprime.mpr q.reduced
  nth_rw 1 [← Rat.num_div_den q]
  simp

theorem isPrimitiveRoot_exp_rat_of_even_num (q : ℚ) (h : Even q.num) :
    IsPrimitiveRoot (exp (π * I * q)) q.den := by
  have ⟨n, hn⟩ := even_iff_exists_two_nsmul _ |>.mp h
  convert! isPrimitiveRoot_exp_rat ((n : ℚ) / (q.den : ℚ)) using 1
  · nth_rw 1 [← q.num_div_den, hn, Int.nsmul_eq_mul]
    push_cast
    ring_nf
  · have hred : n.natAbs.Coprime q.den := by
      apply Nat.Coprime.coprime_mul_left (k := 2)
      convert! q.reduced
      grind
    rw [← Rat.fraction_eq_div n q.den q.den_nz]
    change q.den = (Rat.normalize n q.den q.den_nz).den
    rw [Rat.normalize_eq_mk' _ _ _ hred]

theorem isPrimitiveRoot_exp_rat_of_odd_num (q : ℚ) (h : Odd q.num) :
    IsPrimitiveRoot (exp (π * I * q)) (2 * q.den) := by
  convert! isPrimitiveRoot_exp_rat (q / 2) using 1
  · push_cast
    ring_nf
  · have hd : q.den * 2 ≠ 0 := Nat.mul_ne_zero q.den_nz two_ne_zero
    have hred := Nat.Coprime.mul_right q.reduced h.natAbs.coprime_two_right
    have hq : q / 2 = Rat.fraction q.num (q.den * 2) hd := by
      rw [Rat.fraction_eq_div]
      simpa only [Nat.cast_mul, Nat.cast_ofNat, div_div₀] using
        congrArg (fun x : ℚ ↦ x / 2) q.num_div_den.symm
    rw [mul_comm, hq]
    change q.den * 2 = (Rat.normalize q.num (q.den * 2) hd).den
    rw [Rat.normalize_eq_mk' _ _ _ hred]

theorem isPrimitiveRoot_exp (n : ℕ) (h0 : n ≠ 0) :
    IsPrimitiveRoot (exp (2 * π * I / (n : ℂ))) n := by
  simpa only [Nat.cast_one, mul_one_div₀] using!
    isPrimitiveRoot_exp_of_coprime 1 n h0 n.coprime_one_left

theorem isPrimitiveRoot_iff (ζ : ℂ) (n : ℕ) (hn : n ≠ 0) :
    IsPrimitiveRoot ζ n ↔
      ∃ i < n, ∃ _ : i.Coprime n, exp (2 * π * I * ((i : ℂ) / (n : ℂ))) = ζ := by
  have hn0 : (n : ℂ) ≠ 0 := mod_cast hn
  constructor; swap
  · rintro ⟨i, -, hi, rfl⟩; exact isPrimitiveRoot_exp_of_coprime i n hn hi
  intro h
  have : NeZero n := ⟨hn⟩
  obtain ⟨i, hi, rfl⟩ :=
    (isPrimitiveRoot_exp n hn).eq_pow_of_pow_eq_one h.pow_eq_one
  refine ⟨i, hi, ((isPrimitiveRoot_exp n hn).pow_iff_coprime (Nat.pos_of_ne_zero hn) i).mp h, ?_⟩
  rw [← exp_nat_mul]
  congr 1
  ring

/-- The complex `n`-th roots of unity are exactly the
complex numbers of the form `exp (2 * Real.pi * Complex.I * (i / n))` for some `i < n`. -/
nonrec theorem mem_rootsOfUnity (n : ℕ) [NeZero n] (x : Units ℂ) :
    x ∈ rootsOfUnity n ℂ ↔ ∃ i < n, exp (2 * π * I * ((i : ℂ) / (n : ℂ))) = x := by
  rw [mem_rootsOfUnity, Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one]
  have hn0 : (n : ℂ) ≠ 0 := mod_cast NeZero.out
  constructor
  · intro h
    obtain ⟨i, hi, H⟩ : ∃ i < (n : ℕ), exp (2 * π * I / (n : ℂ)) ^ i = x :=
      (isPrimitiveRoot_exp n NeZero.out).eq_pow_of_pow_eq_one h
    refine ⟨i, hi, ?_⟩
    rw [← H, ← exp_nat_mul]
    congr 1
    ring
  · rintro ⟨i, _, H⟩
    rw [← H, ← exp_nat_mul, exp_eq_one_iff]
    use i
    simp [field]

theorem card_rootsOfUnity (n : ℕ) [NeZero n] : Nat.card (rootsOfUnity n ℂ) = n :=
  (isPrimitiveRoot_exp n NeZero.out).card_rootsOfUnity

theorem card_primitiveRoots (k : ℕ) [NeZero k] : (primitiveRoots k ℂ).card = φ k :=
  (isPrimitiveRoot_exp k NeZero.out).card_primitiveRoots

end Complex

theorem IsPrimitiveRoot.norm'_eq_one {ζ : ℂ} {n : ℕ} (h : IsPrimitiveRoot ζ n) (hn : n ≠ 0) :
    ‖ζ‖ = 1 :=
  Complex.norm_eq_one_of_pow_eq_one h.pow_eq_one hn

theorem IsPrimitiveRoot.nnnorm_eq_one {ζ : ℂ} {n : ℕ} (h : IsPrimitiveRoot ζ n) (hn : n ≠ 0) :
    ‖ζ‖₊ = 1 :=
  Subtype.ext <| h.norm'_eq_one hn

theorem IsPrimitiveRoot.arg_ext {n m : ℕ} {ζ μ : ℂ} (hζ : IsPrimitiveRoot ζ n)
    (hμ : IsPrimitiveRoot μ m) (hn : n ≠ 0) (hm : m ≠ 0) (h : ζ.arg = μ.arg) : ζ = μ :=
  Complex.ext_norm_arg ((hζ.norm'_eq_one hn).trans (hμ.norm'_eq_one hm).symm) h

theorem IsPrimitiveRoot.arg_eq_zero_iff {n : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n) (hn : n ≠ 0) :
    ζ.arg = 0 ↔ ζ = 1 :=
  ⟨fun h => hζ.arg_ext IsPrimitiveRoot.one hn one_ne_zero (h.trans Complex.arg_one.symm), fun h =>
    h.symm ▸ Complex.arg_one⟩

theorem IsPrimitiveRoot.arg_eq_pi_iff {n : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n) (hn : n ≠ 0) :
    ζ.arg = Real.pi ↔ ζ = -1 :=
  ⟨fun h =>
    hζ.arg_ext (IsPrimitiveRoot.neg_one 0 two_ne_zero.symm) hn two_ne_zero
      (h.trans Complex.arg_neg_one.symm),
    fun h => h.symm ▸ Complex.arg_neg_one⟩

theorem IsPrimitiveRoot.arg {n : ℕ} {ζ : ℂ} (h : IsPrimitiveRoot ζ n) (hn : n ≠ 0) :
    ∃ i : ℤ, ζ.arg = (i : ℝ) / (n : ℝ) * (2 * Real.pi) ∧
      IsCoprime i n ∧ i.natAbs < n := by
  rw [Complex.isPrimitiveRoot_iff _ _ hn] at h
  obtain ⟨i, h, hin, rfl⟩ := h
  rw [mul_comm, ← mul_assoc, Complex.exp_mul_I]
  refine ⟨if i * 2 ≤ n then i else i - n, ?_, ?isCoprime, by lia⟩
  case isCoprime =>
    replace hin := Nat.isCoprime_iff_coprime.mpr hin
    split_ifs
    · exact hin
    · convert! hin.add_mul_left_left (-1) using 1
      rw [mul_neg_one, sub_eq_add_neg]
  split_ifs with h₂
  · convert! Complex.arg_cos_add_sin_mul_I _
    · push_cast; rfl
    · push_cast; rfl
    simp only [Int.cast_natCast, Set.mem_Ioc]
    refine ⟨(neg_lt_neg Real.pi_pos).trans_le ?_, ?_⟩
    · rw [neg_zero]
      positivity
    refine Eq.trans_le (b := Real.pi * ((i : ℝ) * 2 / (n : ℝ))) (by ring) ?_
    rw [← mul_one n] at h₂
    exact mul_le_of_le_one_right Real.pi_pos.le
      ((div_le_iff₀' <| mod_cast pos_of_gt h).mpr <| mod_cast h₂)
  rw [← Complex.cos_sub_two_pi, ← Complex.sin_sub_two_pi]
  convert! Complex.arg_cos_add_sin_mul_I _
  · push_cast
    rw [← sub_one_mul, sub_div, div_self]
  · push_cast
    rw [← sub_one_mul, sub_div, div_self]
  simp only [Int.cast_sub, Int.cast_natCast, Set.mem_Ioc]
  have hn' : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hi₁ : (n : ℝ) < (i : ℝ) * 2 := by exact_mod_cast Nat.lt_of_not_ge h₂
  have hi₂ : (i : ℝ) < (n : ℝ) := by exact_mod_cast h
  have hl : -(1 / 2 : ℝ) < ((i : ℝ) - n) / (n : ℝ) :=
    (lt_div_iff₀' hn').2 (by linarith)
  have hu : ((i : ℝ) - n) / (n : ℝ) ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hi₂.le) hn'.le
  constructor
  · have hmul := mul_lt_mul_of_pos_right hl (by positivity : 0 < 2 * Real.pi)
    have heq : -(1 / 2 : ℝ) * (2 * Real.pi) = -Real.pi := by ring
    rwa [heq] at hmul
  · exact (mul_nonpos_of_nonpos_of_nonneg hu (by positivity)).trans Real.pi_nonneg

lemma Complex.norm_eq_one_of_mem_rootsOfUnity {ζ : ℂˣ} {n : ℕ} [NeZero n]
    (hζ : ζ ∈ rootsOfUnity n ℂ) :
    ‖(ζ : ℂ)‖ = 1 := by
  refine norm_eq_one_of_pow_eq_one ?_ <| NeZero.ne n
  norm_cast
  rw [_root_.mem_rootsOfUnity] at hζ
  rw [hζ, Units.val_one]

theorem Complex.conj_rootsOfUnity {ζ : ℂˣ} {n : ℕ} [NeZero n] (hζ : ζ ∈ rootsOfUnity n ℂ) :
    (starRingEnd ℂ) ζ = ζ⁻¹ := by
  rw [← Units.mul_eq_one_iff_eq_inv, conj_mul', norm_eq_one_of_mem_rootsOfUnity hζ, ofReal_one,
    one_pow]
