/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
module

public import Mathlib.Algebra.Polynomial.Identities
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Topology.MetricSpace.CauSeqFilter

/-!
# Hensel's lemma on `ℤ_p`

This file proves Hensel's lemma on `ℤ_p`, roughly following Keith Conrad's writeup:
<http://www.math.uconn.edu/~kconrad/blurbs/gradnumthy/hensel.pdf>

Hensel's lemma gives a simple condition for the existence of a root of a polynomial.

The proof and motivation are described in the paper
[R. Y. Lewis, *A formal proof of Hensel's lemma over the p-adic integers*][lewis2019].

## References

* <http://www.math.uconn.edu/~kconrad/blurbs/gradnumthy/hensel.pdf>
* [R. Y. Lewis, *A formal proof of Hensel's lemma over the p-adic integers*][lewis2019]
* <https://en.wikipedia.org/wiki/Hensel%27s_lemma>

## Tags

p-adic, p adic, padic, p-adic integer
-/

public section


noncomputable section

open scoped Topology

-- We begin with some general lemmas that are used below in the computation.
theorem padic_polynomial_dist {p : ℕ} [Fact p.Prime] {R : Type*} [CommSemiring R] [Algebra R ℤ_[p]]
    (F : Polynomial R) (x y : ℤ_[p]) :
    ‖F.aeval x - F.aeval y‖ ≤ ‖x - y‖ := by
  let ⟨z, hz⟩ := (F.map (algebraMap R ℤ_[p])).evalSubFactor x y
  simp only [Polynomial.eval_map_algebraMap] at hz
  calc
    ‖F.aeval x - F.aeval y‖ = ‖z‖ * ‖x - y‖ := by simp [hz]
    _ ≤ 1 * ‖x - y‖ := by gcongr; apply PadicInt.norm_le_one
    _ = ‖x - y‖ := by simp

open Filter

private theorem comp_tendsto_lim {p : ℕ} [Fact p.Prime] {F : Polynomial ℤ_[p]}
    (ncs : CauSeq ℤ_[p] norm) : Tendsto (fun i => F.eval (ncs i)) atTop (𝓝 (F.eval ncs.lim)) :=
  Filter.Tendsto.comp (@Polynomial.continuousAt _ _ _ _ F _) ncs.tendsto_limit

section

variable {p : ℕ} [Fact p.Prime] {R : Type*} [CommSemiring R] [Algebra R ℤ_[p]]
  {ncs : CauSeq ℤ_[p] norm} {F : Polynomial R}
  {a : ℤ_[p]} (ncs_der_val : ∀ n, ‖F.derivative.aeval (ncs n)‖ = ‖F.derivative.aeval a‖)

private theorem ncs_tendsto_lim :
    Tendsto (fun i => ‖F.derivative.aeval (ncs i)‖) atTop (𝓝 ‖F.derivative.aeval ncs.lim‖) := by
  refine Tendsto.comp (continuous_iff_continuousAt.1 continuous_norm _) ?_
  rw [← Polynomial.eval_map_algebraMap]
  refine (comp_tendsto_lim ncs).congr ?_
  simp

include ncs_der_val

private theorem ncs_tendsto_const :
    Tendsto (fun i => ‖F.derivative.aeval (ncs i)‖) atTop (𝓝 ‖F.derivative.aeval a‖) := by
  convert! @tendsto_const_nhds ℝ _ ℕ _ _; rw [ncs_der_val]

private theorem norm_deriv_eq : ‖F.derivative.aeval ncs.lim‖ = ‖F.derivative.aeval a‖ :=
  tendsto_nhds_unique ncs_tendsto_lim (ncs_tendsto_const ncs_der_val)

end

section


variable {p : ℕ} [Fact p.Prime] {R : Type*} [CommSemiring R] [Algebra R ℤ_[p]]
  {ncs : CauSeq ℤ_[p] norm} {F : Polynomial R}
  (hnorm : Tendsto (fun i => ‖F.aeval (ncs i)‖) atTop (𝓝 0))
include hnorm

private theorem tendsto_zero_of_norm_tendsto_zero :
    Tendsto (fun i => F.aeval (ncs i)) atTop (𝓝 0) :=
  tendsto_iff_norm_sub_tendsto_zero.2 (by simpa using hnorm)

theorem limit_zero_of_norm_tendsto_zero : F.aeval ncs.lim = 0 := by
  refine tendsto_nhds_unique ?_ (tendsto_zero_of_norm_tendsto_zero hnorm)
  rw [← Polynomial.eval_map_algebraMap]
  refine (comp_tendsto_lim ncs).congr ?_
  simp

end

private theorem a_soln_is_unique {p : ℕ} [Fact p.Prime] {R : Type*} [CommSemiring R]
    [Algebra R ℤ_[p]] {F : Polynomial R} {a : ℤ_[p]} (ha : F.aeval a = 0) (z' : ℤ_[p])
    (hz' : F.aeval z' = 0) (hnormz' : ‖z' - a‖ < ‖F.derivative.aeval a‖) : z' = a := by
  let h := z' - a
  let ⟨q, hq⟩ := (F.map (algebraMap R ℤ_[p])).binomExpansion a h
  simp only [Polynomial.eval_map_algebraMap, Polynomial.derivative_map] at hq
  have : (F.derivative.aeval a + q * h) * h = 0 := by calc
    _ = F.aeval (a + h) := by rw [hq, ha, zero_add, sq, right_distrib, mul_assoc]
    _ = _ := show F.aeval (a + (z' - a)) = 0 by simp [hz']
  have : h = 0 := by_contra fun hne ↦
    have : F.derivative.aeval a + q * h = 0 :=
      (eq_zero_or_eq_zero_of_mul_eq_zero this).resolve_right hne
    have : F.derivative.aeval a = -q * h := by simpa using eq_neg_of_add_eq_zero_left this
    lt_irrefl ‖F.derivative.aeval a‖
      (calc
        ‖F.derivative.aeval a‖ = ‖q‖ * ‖h‖ := by simp [this]
        _ ≤ 1 * ‖h‖ := by gcongr; apply PadicInt.norm_le_one
        _ < ‖F.derivative.aeval a‖ := by simpa)
  exact eq_of_sub_eq_zero (by rw [← this])

section Hensel

open Nat

variable {p : ℕ} [Fact p.Prime] {R : Type*} [CommSemiring R] [Algebra R ℤ_[p]]
  {F : Polynomial R} {a : ℤ_[p]}

variable (hnorm : ‖F.aeval a‖ < ‖F.derivative.aeval a‖ ^ 2)
include hnorm

private theorem deriv_sq_norm_pos : 0 < ‖F.derivative.aeval a‖ ^ 2 :=
  lt_of_le_of_lt (norm_nonneg _) hnorm

private theorem deriv_sq_norm_ne_zero : ‖F.derivative.aeval a‖ ^ 2 ≠ 0 :=
  ne_of_gt (deriv_sq_norm_pos hnorm)

private theorem deriv_norm_ne_zero : ‖F.derivative.aeval a‖ ≠ 0 := fun h =>
  deriv_sq_norm_ne_zero hnorm (by simp [*, sq])

private theorem deriv_norm_pos : 0 < ‖F.derivative.aeval a‖ :=
  lt_of_le_of_ne (norm_nonneg _) (Ne.symm (deriv_norm_ne_zero hnorm))

private theorem deriv_ne_zero : F.derivative.aeval a ≠ 0 :=
  mt norm_eq_zero.2 (deriv_norm_ne_zero hnorm)

omit hnorm in
/-- `T` controls the Newton iteration. Its denominator is positive under the Hensel hypothesis. -/
private def T_gen (h : ‖F.derivative.aeval a‖ ^ 2 ≠ 0) : ℝ :=
  Checked.div ‖F.aeval a‖ (‖F.derivative.aeval a‖ ^ 2) h.isUnit

local notation "T" => T_gen (deriv_sq_norm_ne_zero hnorm)

local notation "residualNorm" => fun z : ℤ_[p] ↦
  Checked.div ‖F.aeval z‖ ‖F.derivative.aeval a‖ (Ne.isUnit (deriv_norm_ne_zero hnorm))

private theorem T_nonneg : 0 ≤ T := div_nonneg (norm_nonneg _) (sq_nonneg _)

private theorem T_pow_nonneg (n : ℕ) : 0 ≤ T ^ n := pow_nonneg (T_nonneg hnorm) _

private theorem T_lt_one : T < 1 := (div_lt_one (deriv_sq_norm_pos hnorm)).2 hnorm

private theorem T_pow {n : ℕ} (hn : n ≠ 0) : T ^ n < 1 :=
  pow_lt_one₀ (T_nonneg hnorm) (T_lt_one hnorm) hn

private theorem T_pow' (n : ℕ) : T ^ 2 ^ n < 1 := T_pow hnorm (pow_ne_zero _ two_ne_zero)

/-- We will construct a sequence of elements of `ℤ_p` satisfying successive values of `ih`. -/
local notation "ih" => fun n : ℕ ↦ fun z : ℤ_[p] ↦
  ‖F.derivative.aeval z‖ = ‖F.derivative.aeval a‖ ∧ ‖F.aeval z‖ ≤
    ‖F.derivative.aeval a‖ ^ 2 * T ^ 2 ^ n

private theorem ih_0 : ih 0 a :=
  ⟨rfl, by simp only [pow_zero, pow_one, T_gen, mul_div_cancel₀, le_refl]⟩

private theorem residualNorm_le {n : ℕ} {z : ℤ_[p]} (hz : ih n z) :
    residualNorm z ≤ ‖F.derivative.aeval a‖ * T ^ 2 ^ n := by
  have hd := deriv_norm_ne_zero hnorm
  calc
    _ ≤ ‖F.derivative.aeval a‖ ^ 2 * T ^ 2 ^ n / ‖F.derivative.aeval a‖ :=
      (div_le_div_iff_of_pos_right (deriv_norm_pos hnorm)).2 hz.2
    _ = ‖F.derivative.aeval a‖ * T ^ 2 ^ n := div_sq_cancel _ _

private theorem deriv_ne_zero_of_ih {n : ℕ} {z : ℤ_[p]} (hz : ih n z) :
    F.derivative.aeval z ≠ 0 :=
  norm_ne_zero_iff.mp (hz.1.trans_ne (deriv_norm_ne_zero hnorm))

omit hnorm in
private def newtonQuotient {z : ℤ_[p]} (hz : F.derivative.aeval z ≠ 0) : ℚ_[p] :=
  Checked.div (↑(F.aeval z) : ℚ_[p]) (↑(F.derivative.aeval z) : ℚ_[p])
    (PadicInt.coe_ne_zero.2 hz).isUnit

private theorem norm_newtonQuotient {n : ℕ} {z : ℤ_[p]} (hz : ih n z) :
    ‖newtonQuotient (deriv_ne_zero_of_ih hnorm hz)‖ = residualNorm z := by
  simp only [newtonQuotient, norm_div, PadicInt.padic_norm_e_of_padicInt, hz.1]

private def newtonCorrection {n : ℕ} {z : ℤ_[p]} (hz : ih n z) : ℤ_[p] :=
  ⟨newtonQuotient (deriv_ne_zero_of_ih hnorm hz), (norm_newtonQuotient hnorm hz).trans_le <|
    (residualNorm_le hnorm hz).trans <| by
      calc
        _ ≤ 1 * T ^ 2 ^ n :=
          mul_le_mul_of_nonneg_right (PadicInt.norm_le_one _) (T_pow_nonneg hnorm _)
        _ ≤ 1 := by simpa only [one_mul] using (T_pow' hnorm n).le⟩

private theorem norm_newtonCorrection {n : ℕ} {z : ℤ_[p]} (hz : ih n z) :
    ‖newtonCorrection hnorm hz‖ = residualNorm z :=
  norm_newtonQuotient hnorm hz

private theorem calc_deriv_dist {z z' : ℤ_[p]} {n} (hz : ih n z)
    (hz' : z' = z - newtonCorrection hnorm hz) :
    ‖F.derivative.aeval z' - F.derivative.aeval z‖ < ‖F.derivative.aeval a‖ :=
  calc
    ‖F.derivative.aeval z' - F.derivative.aeval z‖ ≤ ‖z' - z‖ := padic_polynomial_dist _ _ _
    _ = ‖newtonCorrection hnorm hz‖ := by
      simp only [sub_eq_add_neg, add_assoc, hz', add_add_neg_cancel'_right, norm_neg]
    _ = residualNorm z := norm_newtonCorrection hnorm hz
    _ ≤ ‖F.derivative.aeval a‖ * T ^ 2 ^ n := residualNorm_le hnorm hz
    _ < ‖F.derivative.aeval a‖ :=
      (mul_lt_iff_lt_one_right (deriv_norm_pos hnorm)).2 (T_pow' hnorm _)

set_option backward.isDefEq.respectTransparency false in
private def calc_eval_z' {z z' : ℤ_[p]} {n} (hz : ih n z)
    (hz' : z' = z - newtonCorrection hnorm hz) :
    { q : ℤ_[p] // F.aeval z' = q * newtonCorrection hnorm hz ^ 2 } := by
  let z1 := newtonCorrection hnorm hz
  obtain ⟨q, hq⟩ := (F.map (algebraMap R ℤ_[p])).binomExpansion z (-z1)
  have hcancel : F.derivative.aeval z * z1 = F.aeval z := by
    apply PadicInt.ext
    change (↑(F.derivative.aeval z) : ℚ_[p]) *
      newtonQuotient (deriv_ne_zero_of_ih hnorm hz) = _
    rw [newtonQuotient, mul_comm, div_mul_cancel₀]
  have hcancel_neg : F.derivative.aeval z * -z1 = -F.aeval z := by rw [mul_neg, hcancel]
  refine ⟨q, ?_⟩
  change F.aeval z' = q * z1 ^ 2
  rw [show z' = z - z1 from hz']
  simpa [sub_eq_add_neg, neg_mul_eq_mul_neg, hcancel_neg] using hq

private theorem calc_eval_z'_norm {z z' : ℤ_[p]} {n} (hz : ih n z) {q}
    (heq : F.aeval z' = q * newtonCorrection hnorm hz ^ 2) :
    ‖F.aeval z'‖ ≤ ‖F.derivative.aeval a‖ ^ 2 * T ^ 2 ^ (n + 1) := by
  have hd := deriv_norm_ne_zero hnorm
  calc
    ‖F.aeval z'‖ = ‖q‖ * ‖newtonCorrection hnorm hz‖ ^ 2 := by simp [heq]
    _ ≤ 1 * ‖newtonCorrection hnorm hz‖ ^ 2 := by gcongr; apply PadicInt.norm_le_one
    _ = ‖F.aeval z‖ ^ 2 / ‖F.derivative.aeval a‖ ^ 2 := by
      rw [norm_newtonCorrection, div_pow₀, one_mul]
    _ ≤ (‖F.derivative.aeval a‖ ^ 2 * T ^ 2 ^ n) ^ 2 / ‖F.derivative.aeval a‖ ^ 2 := by
      gcongr
      exact hz.2
    _ = (‖F.derivative.aeval a‖ ^ 2) ^ 2 * (T ^ 2 ^ n) ^ 2 / ‖F.derivative.aeval a‖ ^ 2 := by
      simp only [mul_pow]
    _ = ‖F.derivative.aeval a‖ ^ 2 * (T ^ 2 ^ n) ^ 2 := div_sq_cancel _ _
    _ = ‖F.derivative.aeval a‖ ^ 2 * T ^ 2 ^ (n + 1) := by rw [← pow_mul, pow_succ 2]


/-- Given `z : ℤ_[p]` satisfying `ih n z`, construct `z' : ℤ_[p]` satisfying `ih (n+1) z'`. We need
the hypothesis `ih n z`, since otherwise `z'` is not necessarily an integer. -/
private def ih_n {n : ℕ} {z : ℤ_[p]} (hz : ih n z) : { z' : ℤ_[p] // ih (n + 1) z' } :=
  let z' : ℤ_[p] := z - newtonCorrection hnorm hz
  ⟨z',
    have hdist : ‖F.derivative.aeval z' - F.derivative.aeval z‖ < ‖F.derivative.aeval a‖ :=
      calc_deriv_dist hnorm hz rfl
    have hfeq : ‖F.derivative.aeval z'‖ = ‖F.derivative.aeval a‖ := by
      rw [sub_eq_add_neg, ← hz.1, ← norm_neg (F.derivative.aeval z)] at hdist
      have := PadicInt.norm_eq_of_norm_add_lt_right hdist
      rwa [norm_neg, hz.1] at this
    let ⟨_, heq⟩ := calc_eval_z' hnorm hz rfl
    have hnle : ‖F.aeval z'‖ ≤ ‖F.derivative.aeval a‖ ^ 2 * T ^ 2 ^ (n + 1) :=
      calc_eval_z'_norm hnorm hz heq
    ⟨hfeq, hnle⟩⟩

private def newton_seq_aux : ∀ n : ℕ, { z : ℤ_[p] // ih n z }
  | 0 => ⟨a, ih_0 hnorm⟩
  | k + 1 => ih_n hnorm (newton_seq_aux k).2

private def newton_seq_gen (n : ℕ) : ℤ_[p] :=
  (newton_seq_aux hnorm n).1

local notation "newton_seq" => newton_seq_gen hnorm

private theorem newton_seq_deriv_norm (n : ℕ) :
    ‖F.derivative.aeval (newton_seq n)‖ = ‖F.derivative.aeval a‖ :=
  (newton_seq_aux hnorm n).2.1

private theorem newton_seq_norm_le (n : ℕ) :
    ‖F.aeval (newton_seq n)‖ ≤ ‖F.derivative.aeval a‖ ^ 2 * T ^ 2 ^ n :=
  (newton_seq_aux hnorm n).2.2

set_option backward.isDefEq.respectTransparency false in
private theorem newton_seq_norm_eq (n : ℕ) :
    ‖newton_seq (n + 1) - newton_seq n‖ = residualNorm (newton_seq n) := by
  rw [newton_seq_gen, newton_seq_gen, newton_seq_aux, ih_n]
  simp [sub_eq_add_neg, add_comm, norm_newtonCorrection]

private theorem newton_seq_succ_dist (n : ℕ) :
    ‖newton_seq (n + 1) - newton_seq n‖ ≤ ‖F.derivative.aeval a‖ * T ^ 2 ^ n := by
  rw [newton_seq_norm_eq]
  exact residualNorm_le hnorm (newton_seq_aux hnorm n).2

private theorem newton_seq_dist_aux (n : ℕ) :
    ∀ k : ℕ, ‖newton_seq (n + k) - newton_seq n‖ ≤ ‖F.derivative.aeval a‖ * T ^ 2 ^ n
  | 0 => by
    rw [add_zero, sub_self, norm_zero]
    exact mul_nonneg (norm_nonneg _) (T_pow_nonneg hnorm _)
  | k + 1 =>
    have : 2 ^ n ≤ 2 ^ (n + k) := by
      apply pow_right_mono₀
      · simp
      · apply Nat.le_add_right
    calc
      ‖newton_seq (n + (k + 1)) - newton_seq n‖ = ‖newton_seq (n + k + 1) - newton_seq n‖ := by
        rw [add_assoc]
      _ = ‖newton_seq (n + k + 1) - newton_seq (n + k) + (newton_seq (n + k) - newton_seq n)‖ := by
        rw [← sub_add_sub_cancel]
      _ ≤ max ‖newton_seq (n + k + 1) - newton_seq (n + k)‖ ‖newton_seq (n + k) - newton_seq n‖ :=
        (PadicInt.nonarchimedean _ _)
      _ ≤ max (‖F.derivative.aeval a‖ * T ^ 2 ^ (n + k)) (‖F.derivative.aeval a‖ * T ^ 2 ^ n) :=
        (max_le_max (newton_seq_succ_dist _ _) (newton_seq_dist_aux _ _))
      _ = ‖F.derivative.aeval a‖ * T ^ 2 ^ n :=
        max_eq_right <|
          mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (T_nonneg hnorm)
            (le_of_lt (T_lt_one hnorm)) this) (norm_nonneg _)

private theorem newton_seq_dist {n k : ℕ} (hnk : n ≤ k) :
    ‖newton_seq k - newton_seq n‖ ≤ ‖F.derivative.aeval a‖ * T ^ 2 ^ n := by
  have hex : ∃ m, k = n + m := Nat.exists_eq_add_of_le hnk
  let ⟨_, hex'⟩ := hex
  rw [hex']; apply newton_seq_dist_aux

private theorem bound' : Tendsto (fun n : ℕ => ‖F.derivative.aeval a‖ * T ^ 2 ^ n) atTop (𝓝 0) := by
  rw [← mul_zero ‖F.derivative.aeval a‖]
  exact
    tendsto_const_nhds.mul
      (Tendsto.comp (tendsto_pow_atTop_nhds_zero_of_lt_one (T_nonneg hnorm) (T_lt_one hnorm))
        (tendsto_pow_atTop_atTop_of_one_lt (by simp)))

private theorem bound :
    ∀ {ε}, ε > 0 → ∃ N : ℕ, ∀ {n}, n ≥ N → ‖F.derivative.aeval a‖ * T ^ 2 ^ n < ε := fun hε ↦
  eventually_atTop.1 <| (bound' hnorm).eventually <| gt_mem_nhds hε

private theorem bound'_sq :
    Tendsto (fun n : ℕ => ‖F.derivative.aeval a‖ ^ 2 * T ^ 2 ^ n) atTop (𝓝 0) := by
  rw [← mul_zero ‖F.derivative.aeval a‖, sq]
  simp only [mul_assoc]
  apply Tendsto.mul
  · apply tendsto_const_nhds
  · apply bound'
    assumption

private theorem newton_seq_is_cauchy : IsCauSeq norm newton_seq := fun _ε hε ↦
  (bound hnorm hε).imp fun _N hN _j hj ↦ (newton_seq_dist hnorm hj).trans_lt <| hN le_rfl

private def newton_cau_seq : CauSeq ℤ_[p] norm := ⟨_, newton_seq_is_cauchy hnorm⟩

private def soln_gen : ℤ_[p] := (newton_cau_seq hnorm).lim

local notation "soln" => soln_gen hnorm

private theorem soln_spec {ε : ℝ} (hε : ε > 0) :
    ∃ N : ℕ, ∀ {i : ℕ}, i ≥ N → ‖soln - newton_cau_seq hnorm i‖ < ε :=
  Setoid.symm (CauSeq.equiv_lim (newton_cau_seq hnorm)) _ hε

private theorem soln_deriv_norm : ‖F.derivative.aeval soln‖ = ‖F.derivative.aeval a‖ :=
  norm_deriv_eq (newton_seq_deriv_norm hnorm)

private theorem newton_seq_norm_tendsto_zero :
    Tendsto (fun i => ‖F.aeval (newton_cau_seq hnorm i)‖) atTop (𝓝 0) :=
  squeeze_zero (fun _ => norm_nonneg _) (newton_seq_norm_le hnorm) (bound'_sq hnorm)

private theorem newton_seq_dist_tendsto' :
    Tendsto (fun n => ‖newton_cau_seq hnorm n - a‖) atTop (𝓝 ‖soln - a‖) :=
  (continuous_norm.tendsto _).comp ((newton_cau_seq hnorm).tendsto_limit.sub tendsto_const_nhds)

private theorem eval_soln : F.aeval soln = 0 :=
  limit_zero_of_norm_tendsto_zero (newton_seq_norm_tendsto_zero hnorm)

variable (hnsol : F.aeval a ≠ 0)
include hnsol

private theorem T_pos : T > 0 :=
  div_pos (norm_pos_iff.2 hnsol) (deriv_sq_norm_pos hnorm)

private theorem newton_seq_succ_dist_weak (n : ℕ) :
    ‖newton_seq (n + 2) - newton_seq (n + 1)‖ < residualNorm a :=
  have : 2 ≤ 2 ^ (n + 1) := by
    have := pow_right_mono₀ (by simp : 1 ≤ 2) (Nat.le_add_left _ _ : 1 ≤ n + 1)
    simpa using this
  calc
    ‖newton_seq (n + 2) - newton_seq (n + 1)‖ ≤ ‖F.derivative.aeval a‖ * T ^ 2 ^ (n + 1) :=
      newton_seq_succ_dist hnorm _
    _ ≤ ‖F.derivative.aeval a‖ * T ^ 2 :=
      (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (T_nonneg hnorm)
        (le_of_lt (T_lt_one hnorm)) this) (norm_nonneg _))
    _ < ‖F.derivative.aeval a‖ * T ^ 1 :=
      (mul_lt_mul_of_pos_left (pow_lt_pow_right_of_lt_one₀ (T_pos hnorm hnsol)
        (T_lt_one hnorm) (by norm_num)) (deriv_norm_pos hnorm))
    _ = residualNorm a := by
      simp only [pow_one, T_gen, ← mul_div_assoc₀, pow_two, mul_div_mul_left]

set_option backward.isDefEq.respectTransparency false in
private theorem newton_seq_dist_to_a :
    ∀ n : ℕ, 0 < n → ‖newton_seq n - a‖ = residualNorm a
  | 1, _h => newton_seq_norm_eq hnorm 0
  | k + 2, _h =>
    have hlt : ‖newton_seq (k + 2) - newton_seq (k + 1)‖ < ‖newton_seq (k + 1) - a‖ := by
      rw [newton_seq_dist_to_a (k + 1) (succ_pos _)]; apply newton_seq_succ_dist_weak
      assumption
    have hne' : ‖newton_seq (k + 2) - newton_seq (k + 1)‖ ≠ ‖newton_seq (k + 1) - a‖ := ne_of_lt hlt
    calc
      ‖newton_seq (k + 2) - a‖ =
          ‖newton_seq (k + 2) - newton_seq (k + 1) + (newton_seq (k + 1) - a)‖ := by
        rw [← sub_add_sub_cancel]
      _ = max ‖newton_seq (k + 2) - newton_seq (k + 1)‖ ‖newton_seq (k + 1) - a‖ :=
        (PadicInt.norm_add_eq_max_of_ne hne')
      _ = ‖newton_seq (k + 1) - a‖ := max_eq_right_of_lt hlt
      _ = residualNorm a := newton_seq_dist_to_a (k + 1) (succ_pos _)

private theorem newton_seq_dist_tendsto :
    Tendsto (fun n => ‖newton_cau_seq hnorm n - a‖)
    atTop (𝓝 (residualNorm a)) :=
  tendsto_const_nhds.congr' (eventually_atTop.2
    ⟨1, fun _ hx => (newton_seq_dist_to_a hnorm hnsol _ hx).symm⟩)

private theorem soln_dist_to_a : ‖soln - a‖ = residualNorm a :=
  tendsto_nhds_unique (newton_seq_dist_tendsto' hnorm) (newton_seq_dist_tendsto hnorm hnsol)

private theorem soln_dist_to_a_lt_deriv : ‖soln - a‖ < ‖F.derivative.aeval a‖ := by
  rw [soln_dist_to_a hnorm hnsol]
  exact (div_lt_iff₀ (deriv_norm_pos hnorm)).2 (by simpa only [pow_two] using hnorm)

private theorem soln_unique (z : ℤ_[p]) (hev : F.aeval z = 0)
    (hnlt : ‖z - a‖ < ‖F.derivative.aeval a‖) : z = soln := by
  have hsoln : ‖z - soln‖ < ‖F.derivative.aeval soln‖ := by
    rw [soln_deriv_norm]
    calc
      ‖z - soln‖ = ‖z - a + (a - soln)‖ := by rw [sub_add_sub_cancel]
      _ ≤ max ‖z - a‖ ‖a - soln‖ := PadicInt.nonarchimedean _ _
      _ < ‖F.derivative.aeval a‖ :=
        max_lt hnlt ((norm_sub_rev soln a ▸ (soln_dist_to_a_lt_deriv hnorm)) hnsol)
  exact a_soln_is_unique (eval_soln hnorm) z hev hsoln

end Hensel

variable {p : ℕ} [Fact p.Prime] {R : Type*} [CommSemiring R] [Algebra R ℤ_[p]]
  {F : Polynomial R} {a : ℤ_[p]}

variable (hnorm : ‖F.aeval a‖ < ‖F.derivative.aeval a‖ ^ 2)
include hnorm

private theorem a_is_soln (ha : F.aeval a = 0) :
    F.aeval a = 0 ∧
      ‖a - a‖ < ‖F.derivative.aeval a‖ ∧
        ‖F.derivative.aeval a‖ = ‖F.derivative.aeval a‖ ∧
          ∀ z', F.aeval z' = 0 → ‖z' - a‖ < ‖F.derivative.aeval a‖ → z' = a :=
  ⟨ha, by simp [deriv_ne_zero hnorm], rfl, a_soln_is_unique ha⟩

theorem hensels_lemma :
    ∃ z : ℤ_[p],
      F.aeval z = 0 ∧
        ‖z - a‖ < ‖F.derivative.aeval a‖ ∧
          ‖F.derivative.aeval z‖ = ‖F.derivative.aeval a‖ ∧
            ∀ z', F.aeval z' = 0 → ‖z' - a‖ < ‖F.derivative.aeval a‖ → z' = z := by
  classical
  exact if ha : F.aeval a = 0 then ⟨a, a_is_soln hnorm ha⟩
  else by
    exact ⟨soln_gen hnorm, eval_soln hnorm,
      soln_dist_to_a_lt_deriv hnorm ha, soln_deriv_norm hnorm, fun z => soln_unique hnorm ha z⟩
