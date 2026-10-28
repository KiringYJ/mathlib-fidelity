/-
Copyright (c) 2024 Daniel Weber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Weber
-/
module

public import Mathlib.Algebra.Order.Field.GeomSum
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Analysis.Normed.Field.Basic

/-!
# Cauchy's bound on polynomial roots.

The bound is given by `Polynomial.cauchyBound`, which for a nonzero polynomial
`a_n x^n + a_(n-1) x^(n - 1) + ⋯ + a_0` with `a_n ≠ 0` is `1 + max_(0 ≤ i < n) a_i / a_n`.
The leading coefficient of the zero polynomial is `0` and every element is a root of it, so the
bound is defined for nonzero polynomials only.

The theorem that this gives a bound to polynomial roots is `Polynomial.IsRoot.norm_lt_cauchyBound`.
-/

@[expose] public section

variable {K : Type*} [NormedDivisionRing K]

namespace Polynomial

open Finset NNReal

/--
Cauchy's bound on the roots of a nonzero polynomial `p`: one more than the largest quotient of the
norm of a lower coefficient by the norm of the leading coefficient, which does not vanish since
`p ≠ 0`.
See `IsRoot.norm_lt_cauchyBound` for the proof that the roots satisfy this bound.
-/
noncomputable def cauchyBound (p : K[X]) (hp : p ≠ 0) : ℝ≥0 :=
  haveI : ‖p.leadingCoeff‖₊ ≠ 0 := nnnorm_ne_zero_iff.mpr (leadingCoeff_ne_zero.mpr hp)
  sup (range p.natDegree) (‖p.coeff ·‖₊) / ‖p.leadingCoeff‖₊ + 1

@[simp]
lemma one_le_cauchyBound (p : K[X]) {hp : p ≠ 0} : 1 ≤ cauchyBound p hp := by
  simp [cauchyBound]

@[simp]
lemma cauchyBound_C (x : K) {hp : C x ≠ 0} : cauchyBound (C x) hp = 1 := by
  simp [cauchyBound]

@[simp]
lemma cauchyBound_one {hp : (1 : K[X]) ≠ 0} : cauchyBound 1 hp = 1 := cauchyBound_C 1

@[simp]
lemma cauchyBound_X {hp : (X : K[X]) ≠ 0} : cauchyBound X hp = 1 := by
  simp [cauchyBound]

@[simp]
lemma cauchyBound_X_add_C (x : K) {hp : X + C x ≠ 0} : cauchyBound (X + C x) hp = ‖x‖₊ + 1 := by
  simp [cauchyBound]

@[simp]
lemma cauchyBound_X_sub_C (x : K) {hp : X - C x ≠ 0} : cauchyBound (X - C x) hp = ‖x‖₊ + 1 := by
  simp [cauchyBound]

@[simp]
lemma cauchyBound_smul {x : K} (p : K[X]) {hxp : x • p ≠ 0} :
    cauchyBound (x • p) hxp = cauchyBound p (right_ne_zero_of_smul hxp) := by
  have hx : x ≠ 0 := left_ne_zero_of_smul hxp
  simp only [cauchyBound, (IsRegular.of_ne_zero hx).left.isSMulRegular,
    natDegree_smul_of_smul_regular, coeff_smul, smul_eq_mul, nnnorm_mul, ← mul_finset_sup,
    leadingCoeff_smul_of_smul_regular, add_left_inj]
  apply mul_div_mul_left

/--
`cauchyBound` is a bound on the norm of polynomial roots.
-/
theorem IsRoot.norm_lt_cauchyBound {p : K[X]} (hp : p ≠ 0) {a : K} (h : p.IsRoot a) :
    ‖a‖₊ < cauchyBound p hp := by
  rw [IsRoot.def, eval_eq_sum_range, range_add_one] at h
  simp only [mem_range, lt_self_iff_false, not_false_eq_true, sum_insert, coeff_natDegree,
    add_eq_zero_iff_eq_neg] at h
  apply_fun nnnorm at h
  simp only [nnnorm_mul, nnnorm_pow, nnnorm_neg] at h
  have pld : 0 < ‖p.leadingCoeff‖₊ := pos_iff_ne_zero.mpr (by simpa)
  -- Clear the leading coefficient: `‖a‖₊ ^ n ≤ (cauchyBound p hp - 1) * ∑ i < n, ‖a‖₊ ^ i`.
  have key : ‖a‖₊ ^ p.natDegree ≤ (cauchyBound p hp - 1) * ∑ i ∈ range p.natDegree, ‖a‖₊ ^ i := by
    rw [cauchyBound, add_tsub_cancel_right, div_mul_eq_mul_div₀, le_div_iff₀' pld, h, mul_sum]
    refine (nnnorm_sum_le _ _).trans (sum_le_sum fun i hi ↦ ?_)
    rw [nnnorm_mul, nnnorm_pow]
    gcongr
    exact le_sup (f := (‖p.coeff ·‖₊)) hi
  -- If `cauchyBound p hp ≤ ‖a‖₊`, the geometric sum gives `‖a‖₊ ^ n ≤ ‖a‖₊ ^ n - 1`.
  refine not_le.mp fun hle ↦ ?_
  have h1 : 1 ≤ ‖a‖₊ := (one_le_cauchyBound p).trans hle
  have h2 : ‖a‖₊ ^ p.natDegree ≤ ‖a‖₊ ^ p.natDegree - 1 :=
    calc ‖a‖₊ ^ p.natDegree
      _ ≤ (cauchyBound p hp - 1) * ∑ i ∈ range p.natDegree, ‖a‖₊ ^ i := key
      _ ≤ (‖a‖₊ - 1) * ∑ i ∈ range p.natDegree, ‖a‖₊ ^ i := by gcongr
      _ = ‖a‖₊ ^ p.natDegree - 1 := by rw [mul_comm (‖a‖₊ - 1), geom_sum_mul_of_one_le h1]
  exact (tsub_lt_self (pow_pos (zero_lt_one.trans_le h1) _) zero_lt_one).not_ge h2

end Polynomial
