/-
Copyright (c) 2022 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Int.Log

/-!
# Real logarithm base `b`

In this file we define `Real.logb` to be the logarithm of a real number in a given base `b`. We
define this as the division of the natural logarithms of the argument and the base, so that we have
a function on nonzero arguments and nonzero bases with `log b ≠ 0`. On this domain
`logb b (-x) = logb b x` and `logb (-b) x = logb b x`.

We prove some basic properties of this function and its relation to `rpow`.

## Tags

logarithm, continuity
-/

@[expose] public section


open Set Filter Function

open scoped Topology

noncomputable section

namespace Real

variable {b x y : ℝ}

/-! Nonvanishing of a logarithm follows from its exact zero characterization, or from a
positive argument distinct from one. These rules discharge routine logarithmic denominators. -/
macro_rules | `(tactic| checked_nonzero) => `(tactic|
  solve
  | assumption
  | ((with_reducible apply Real.log_ne_zero_of_pos_of_ne_one) <;>
      first | assumption | positivity | (intro h; linarith) | (norm_cast; omega) | norm_num)
  | ((with_reducible apply Real.log_ne_zero.mpr);
      refine ⟨?_, ?_, ?_⟩ <;> first | assumption | (intro h; linarith) | norm_num)
  | ((first | rw [Real.log_abs] | rw [Real.log_neg_eq_log] | rw [Real.log_inv]); checked_nonzero))

/-- Discharge the genuine nonzero-input condition for the base logarithm. -/
syntax (name := logbNonzero) "logb_nonzero" : tactic
macro_rules | `(tactic| logb_nonzero) => `(tactic|
  first
  | checked_nonzero
  | (intro h; linarith)
  | (norm_cast; omega)
  | fail "a nonzero logarithm input proof is required")

/-- The absolute-value logarithm in a base: both inputs are nonzero, and the
logarithm of the base must be nonzero. Negative nonzero inputs use their absolute values. -/
@[pp_nodot]
noncomputable def logb (b x : ℝ) (hb0 : b ≠ 0 := by logb_nonzero)
    (hx : x ≠ 0 := by logb_nonzero) (hb : IsUnit (Real.log b) := by checked_unit) : ℝ :=
  Checked.div (expOrderIso.symm ⟨|x|, abs_pos.mpr hx⟩)
    (expOrderIso.symm ⟨|b|, abs_pos.mpr hb0⟩) ((log_of_ne_zero hb0) ▸ hb)

theorem log_div_log {hb0 : b ≠ 0} {hx : x ≠ 0} {hb : IsUnit (Real.log b)} :
    log x / log b = logb b x := by
  unfold logb
  simp only [← log_of_ne_zero hx, ← log_of_ne_zero hb0]

lemma logb_ne_zero_iff {hb0 : b ≠ 0} {hx : x ≠ 0} {hb : IsUnit (Real.log b)} :
    logb b x ≠ 0 ↔ log x ≠ 0 := by
  rw [← log_div_log, div_ne_zero_iff]

macro_rules | `(tactic| checked_nonzero) => `(tactic|
  solve
  | assumption
  | ((with_reducible apply Real.logb_ne_zero_iff.mpr); checked_nonzero))

section BaseDomain

variable {hb0 : b ≠ 0} {hb : IsUnit (Real.log b)}

@[simp] theorem logb_one : logb b 1 = 0 := by simp [← log_div_log]

@[simp] lemma logb_self_eq_one : logb b b = 1 := by rw [← log_div_log, div_self]

lemma logb_self_eq_one_iff : logb b b = 1 ↔ b ≠ 0 ∧ b ≠ 1 ∧ b ≠ -1 := by
  exact ⟨fun _ => log_ne_zero.mp hb.ne_zero, fun _ => logb_self_eq_one⟩

@[simp]
theorem logb_abs_base (b x : ℝ) {hx : x ≠ 0} {hb0 : |b| ≠ 0}
    {hb : IsUnit (Real.log |b|)} :
    logb |b| x = logb b x (hb0 := abs_ne_zero.mp hb0)
      (hb := by simpa only [log_abs] using hb) := by
  simp only [← log_div_log, log_abs]

@[simp]
theorem logb_abs (b x : ℝ) {habs : |x| ≠ 0} {hb0 : b ≠ 0} {hb : IsUnit (Real.log b)} :
    logb b |x| = logb b x (hx := abs_ne_zero.mp habs) := by
  simp only [← log_div_log, log_abs]

@[simp]
theorem logb_neg_base_eq_logb (b x : ℝ) {hx : x ≠ 0} {hb0 : -b ≠ 0}
    {hb : IsUnit (Real.log (-b))} :
    logb (-b) x = logb b x (hb0 := neg_ne_zero.mp hb0)
      (hb := by simpa only [log_neg_eq_log] using hb) := by
  simp only [← log_div_log, log_neg_eq_log]

@[simp]
theorem logb_neg_eq_logb (b x : ℝ) {hneg : -x ≠ 0} {hb0 : b ≠ 0}
    {hb : IsUnit (Real.log b)} :
    logb b (-x) = logb b x (hx := neg_ne_zero.mp hneg) := by
  simp only [← log_div_log, log_neg_eq_log]

theorem logb_mul (hx : x ≠ 0) (hy : y ≠ 0) : logb b (x * y) = logb b x + logb b y := by
  simp only [← log_div_log, log_mul hx hy, add_div]

theorem logb_div (hx : x ≠ 0) {hy : IsUnit y} : logb b (x / y) = logb b x - logb b y := by
  simp only [← log_div_log, log_div hx, sub_div]

@[simp]
theorem logb_inv (b x : ℝ) {hb0 : b ≠ 0} {hb : IsUnit (Real.log b)} {hx : IsUnit x} :
    logb b x⁻¹ = -logb b x := by simp only [← log_div_log, log_inv, neg_div₀]

@[simp]
theorem logb_inv_base (b x : ℝ) {hx : x ≠ 0} {hb : b ≠ 0 ∧ b ≠ 1 ∧ b ≠ -1} :
    logb (Checked.inv b hb.1.isUnit) x (hb0 := inv_ne_zero)
      (hb := by rw [log_inv]; exact (neg_ne_zero.mpr (log_ne_zero.mpr hb)).isUnit) =
      -logb b x (hb0 := hb.1) (hb := (log_ne_zero.mpr hb).isUnit) := by
  simp only [← log_div_log, log_inv, div_neg₀]

theorem inv_logb (a b : ℝ) {hb0 : b ≠ 0}
    {ha0 : a ≠ 0} {ha : IsUnit (log a)} {hab : IsUnit (logb a b)} :
    (logb a b)⁻¹ = logb b (hb := (logb_ne_zero_iff.mp hab.ne_zero).isUnit) a := by
  have hb : IsUnit (Real.log b) := (logb_ne_zero_iff.mp hab.ne_zero).isUnit
  simp only [← log_div_log, inv_div₀]

theorem inv_logb_mul_base {a b : ℝ} (c : ℝ) {hc0 : c ≠ 0}
    {ha0 : a ≠ 0} {ha : IsUnit (log a)}
    {hb0 : b ≠ 0} {hb : IsUnit (Real.log b)} {hab : IsUnit (log (a * b))}
    {hca : IsUnit (logb a c)} {hcb : IsUnit (logb b c)}
    {hcab : IsUnit (logb (a * b) c)} :
    (logb (a * b) c)⁻¹ = (logb a c)⁻¹ + (logb b c)⁻¹ := by
  simp only [inv_logb]
  exact logb_mul (log_ne_zero.mp ha.ne_zero).1 (log_ne_zero.mp hb.ne_zero).1

theorem inv_logb_div_base {a b : ℝ} (c : ℝ) {hc0 : c ≠ 0}
    {ha0 : a ≠ 0} {ha : IsUnit (log a)}
    {hb0 : b ≠ 0} {hb : IsUnit (Real.log b)} {hab : IsUnit (log (a / b))}
    {hca : IsUnit (logb a c)} {hcb : IsUnit (logb b c)}
    {hcab : IsUnit (logb (a / b) c)} :
    (logb (a / b) c)⁻¹ = (logb a c)⁻¹ - (logb b c)⁻¹ := by
  simp only [inv_logb]
  exact logb_div (log_ne_zero.mp ha.ne_zero).1

theorem logb_mul_base {a b : ℝ} (c : ℝ) {hc0 : c ≠ 0}
    {ha0 : a ≠ 0} {ha : IsUnit (log a)}
    {hb0 : b ≠ 0} {hb : IsUnit (Real.log b)} {hab : IsUnit (log (a * b))}
    {hca : IsUnit (logb a c)} {hcb : IsUnit (logb b c)}
    {hsum : IsUnit ((logb a c)⁻¹ + (logb b c)⁻¹)} :
    logb (a * b) c = ((logb a c)⁻¹ + (logb b c)⁻¹)⁻¹ := by
  have hc : IsUnit (log c) := (logb_ne_zero_iff.mp hca.ne_zero).isUnit
  have hcab : IsUnit (logb (a * b) c) := by
    simpa only [← log_div_log] using hc.div₀ hab
  apply (inv_inj₀ (ha := hcab) (hb := hsum.inv₀)).mp
  simpa only [inv_inv₀] using (inv_logb_mul_base c)

theorem logb_div_base {a b : ℝ} (c : ℝ) {hc0 : c ≠ 0}
    {ha0 : a ≠ 0} {ha : IsUnit (log a)}
    {hb0 : b ≠ 0} {hb : IsUnit (Real.log b)} {hab : IsUnit (log (a / b))}
    {hca : IsUnit (logb a c)} {hcb : IsUnit (logb b c)}
    {hdiff : IsUnit ((logb a c)⁻¹ - (logb b c)⁻¹)} :
    logb (a / b) c = ((logb a c)⁻¹ - (logb b c)⁻¹)⁻¹ := by
  have hc : IsUnit (log c) := (logb_ne_zero_iff.mp hca.ne_zero).isUnit
  have hcab : IsUnit (logb (a / b) c) := by
    simpa only [← log_div_log] using hc.div₀ hab
  apply (inv_inj₀ (ha := hcab) (hb := hdiff.inv₀)).mp
  simpa only [inv_inv₀] using (inv_logb_div_base c)

theorem mul_logb {a b c : ℝ} {hc0 : c ≠ 0} {ha0 : a ≠ 0} {ha : IsUnit (log a)}
    {hb0 : b ≠ 0} {hb : IsUnit (Real.log b)} :
    logb a b * logb b c = logb a c := by
  simp only [← log_div_log]
  rw [mul_comm, div_mul_div_cancel₀]

theorem div_logb {a b c : ℝ} {hc0 : c ≠ 0} {ha0 : a ≠ 0} {ha : IsUnit (log a)}
    {hb0 : b ≠ 0} {hb : IsUnit (Real.log b)}
    {hc : IsUnit (logb b c)} : logb a c / logb b c = logb a b := by
  simp only [← log_div_log]
  exact div_div_div_cancel_left' _ _

theorem logb_rpow_eq_mul_logb_of_pos (hx : 0 < x) : logb b (x ^ y) = y * logb b x := by
  simp only [← log_div_log, log_rpow hx, mul_div_assoc₀]

theorem logb_pow (b x : ℝ) (k : ℕ) {hx : x ≠ 0} {hb0 : b ≠ 0}
    {hb : IsUnit (Real.log b)} :
    logb b (x ^ k) = k * logb b x := by
  simp only [← log_div_log, log_pow, mul_div_assoc₀]

end BaseDomain

section BPosAndNeOne

variable (b_pos : 0 < b) (b_ne_one : b ≠ 1)
include b_pos b_ne_one

@[simp]
theorem logb_rpow : logb b (b ^ x) = x := by
  rw [← log_div_log, div_eq_iff, log_rpow b_pos]

theorem rpow_logb_eq_abs (hx : x ≠ 0) : b ^ logb b x = |x| := by
  apply log_injOn_pos
  · simp only [Set.mem_Ioi]
    apply rpow_pos_of_pos b_pos
  · simp only [abs_pos, mem_Ioi, Ne, hx, not_false_iff]
  rw [log_rpow b_pos, ← log_div_log, log_abs]
  rw [div_mul_cancel₀]

@[simp]
theorem rpow_logb (hx : 0 < x) : b ^ logb b x = x := by
  rw [rpow_logb_eq_abs b_pos b_ne_one hx.ne']
  exact abs_of_pos hx

theorem rpow_logb_of_neg (hx : x < 0) : b ^ logb b x = -x := by
  rw [rpow_logb_eq_abs b_pos b_ne_one (ne_of_lt hx)]
  exact abs_of_neg hx

theorem logb_eq_iff_rpow_eq (hy : 0 < y) : logb b y = x ↔ b ^ x = y := by
  constructor <;> rintro rfl
  · exact rpow_logb b_pos b_ne_one hy
  · exact logb_rpow b_pos b_ne_one

omit b_pos b_ne_one in
theorem surjOn_logb {hb0 : b ≠ 0} {hb : IsUnit (Real.log b)} :
    SurjOn (fun x : {x : ℝ // x ≠ 0} => logb b x.1 (hx := x.2))
      {x | 0 < x.1} univ := by
  intro x _
  refine ⟨⟨exp (x * log b), (exp_pos _).ne'⟩, exp_pos _, ?_⟩
  simp only [← log_div_log, log_exp, mul_div_cancel_right₀]

omit b_pos b_ne_one in
theorem logb_surjective {hb0 : b ≠ 0} {hb : IsUnit (Real.log b)} :
    Surjective (fun x : {x : ℝ // x ≠ 0} => logb b x.1 (hx := x.2)) := by
  intro x
  refine ⟨⟨exp (x * log b), (exp_pos _).ne'⟩, ?_⟩
  simp only [← log_div_log, log_exp, mul_div_cancel_right₀]

omit b_pos b_ne_one in
@[simp]
theorem range_logb {hb0 : b ≠ 0} {hb : IsUnit (Real.log b)} :
    range (fun x : {x : ℝ // x ≠ 0} => logb b x.1 (hx := x.2)) = univ :=
  (logb_surjective (b := b)).range_eq

omit b_pos b_ne_one in
theorem surjOn_logb' {hb0 : b ≠ 0} {hb : IsUnit (Real.log b)} :
    SurjOn (fun x : {x : ℝ // x ≠ 0} => logb b x.1 (hx := x.2))
      {x | x.1 < 0} univ := by
  intro x _
  refine ⟨⟨-exp (x * log b), neg_ne_zero.mpr (exp_pos _).ne'⟩,
    neg_lt_zero.mpr (exp_pos _), ?_⟩
  simp only [← log_div_log, log_neg_eq_log, log_exp, mul_div_cancel_right₀]

end BPosAndNeOne

section OneLtB

variable (hb : 1 < b)
include hb

private theorem b_pos : 0 < b := by linarith

-- Name has a prime added to avoid clashing with `b_ne_one` further down the file
private theorem b_ne_one' : b ≠ 1 := by linarith

@[simp]
theorem logb_le_logb (h : 0 < x) (h₁ : 0 < y) : logb b x ≤ logb b y ↔ x ≤ y := by
  rw [← log_div_log, ← log_div_log, div_le_div_iff_of_pos_right (log_pos hb), log_le_log_iff h h₁]

@[gcongr]
theorem logb_le_logb_of_le (h : 0 < x) (hxy : x ≤ y) : logb b x ≤ logb b y :=
  (logb_le_logb hb h (by linarith)).mpr hxy

@[gcongr]
theorem logb_lt_logb (hx : 0 < x) (hxy : x < y) : logb b x < logb b y := by
  rw [← log_div_log, ← log_div_log, div_lt_div_iff_of_pos_right (log_pos hb)]
  exact log_lt_log hx hxy

@[simp]
theorem logb_lt_logb_iff (hx : 0 < x) (hy : 0 < y) : logb b x < logb b y ↔ x < y := by
  rw [← log_div_log, ← log_div_log, div_lt_div_iff_of_pos_right (log_pos hb)]
  exact log_lt_log_iff hx hy

theorem logb_le_iff_le_rpow (hx : 0 < x) : logb b x ≤ y ↔ x ≤ b ^ y := by
  rw [← rpow_le_rpow_left_iff hb, rpow_logb (b_pos hb) (b_ne_one' hb) hx]

theorem logb_lt_iff_lt_rpow (hx : 0 < x) : logb b x < y ↔ x < b ^ y := by
  rw [← rpow_lt_rpow_left_iff hb, rpow_logb (b_pos hb) (b_ne_one' hb) hx]

theorem le_logb_iff_rpow_le (hy : 0 < y) : x ≤ logb b y ↔ b ^ x ≤ y := by
  rw [← rpow_le_rpow_left_iff hb, rpow_logb (b_pos hb) (b_ne_one' hb) hy]

theorem lt_logb_iff_rpow_lt (hy : 0 < y) : x < logb b y ↔ b ^ x < y := by
  rw [← rpow_lt_rpow_left_iff hb, rpow_logb (b_pos hb) (b_ne_one' hb) hy]

theorem logb_pos_iff (hx : 0 < x) : 0 < logb b x ↔ 1 < x := by
  rw [← logb_one (b := b) (hb0 := (zero_lt_one.trans hb).ne') (hb := (log_pos hb).ne'.isUnit)]
  rw [logb_lt_logb_iff hb zero_lt_one hx]

theorem logb_pos (hx : 1 < x) : 0 < logb b x := by
  rw [logb_pos_iff hb (lt_trans zero_lt_one hx)]
  exact hx

theorem logb_neg_iff (h : 0 < x) : logb b x < 0 ↔ x < 1 := by
  rw [← logb_one (b := b) (hb0 := (zero_lt_one.trans hb).ne') (hb := (log_pos hb).ne'.isUnit)]
  exact logb_lt_logb_iff hb h zero_lt_one

theorem logb_neg (h0 : 0 < x) (h1 : x < 1) : logb b x < 0 :=
  (logb_neg_iff hb h0).2 h1

theorem logb_nonneg_iff (hx : 0 < x) : 0 ≤ logb b x ↔ 1 ≤ x := by
  rw [← not_lt, logb_neg_iff hb hx, not_lt]

theorem logb_nonneg (hx : 1 ≤ x) : 0 ≤ logb b x :=
  (logb_nonneg_iff hb (zero_lt_one.trans_le hx)).2 hx

theorem logb_nonpos_iff (hx : 0 < x) : logb b x ≤ 0 ↔ x ≤ 1 := by
  rw [← not_lt, logb_pos_iff hb hx, not_lt]

theorem logb_nonpos_iff' {hx0 : x ≠ 0} (hx : 0 ≤ x) : logb b x ≤ 0 ↔ x ≤ 1 := by
  exact logb_nonpos_iff hb (lt_of_le_of_ne hx (Ne.symm hx0))

theorem logb_nonpos {hx0 : x ≠ 0} (hx : 0 ≤ x) (h'x : x ≤ 1) : logb b x ≤ 0 :=
  (logb_nonpos_iff' hb hx).2 h'x

theorem strictMonoOn_logb :
    StrictMonoOn (fun x : {x : ℝ // x ≠ 0} => logb b x.1 (hx := x.2))
      {x | 0 < x.1} := fun _ hx _ _ hxy =>
  logb_lt_logb hb hx hxy

theorem strictAntiOn_logb :
    StrictAntiOn (fun x : {x : ℝ // x ≠ 0} => logb b x.1 (hx := x.2))
      {x | x.1 < 0} := by
  rintro ⟨x, hx0⟩ (hx : x < 0) ⟨y, hy0⟩ (hy : y < 0) hxy
  change logb b y < logb b x
  rw [← logb_abs b y (habs := abs_ne_zero.mpr hy0),
    ← logb_abs b x (habs := abs_ne_zero.mpr hx0)]
  refine logb_lt_logb hb (abs_pos.2 hy.ne) ?_
  rwa [abs_of_neg hy, abs_of_neg hx, neg_lt_neg_iff]

theorem logb_injOn_pos :
    Set.InjOn (fun x : {x : ℝ // x ≠ 0} => logb b x.1 (hx := x.2))
      {x | 0 < x.1} :=
  (strictMonoOn_logb hb).injOn

theorem eq_one_of_pos_of_logb_eq_zero (h₁ : 0 < x) (h₂ : logb b x = 0) : x = 1 := by
  apply Real.eq_one_of_pos_of_log_eq_zero h₁
  exact div_eq_zero_iff.mp (by simpa only [← log_div_log] using h₂)

theorem logb_ne_zero_of_pos_of_ne_one (hx_pos : 0 < x) (hx : x ≠ 1) : logb b x ≠ 0 :=
  mt (eq_one_of_pos_of_logb_eq_zero hb hx_pos) hx

theorem tendsto_logb_atTop :
    Tendsto (fun x : {x : ℝ // x ≠ 0} => logb b x.1 (hx := x.2))
      (comap Subtype.val atTop) atTop := by
  simpa only [← log_div_log, Function.comp_def] using
    (tendsto_log_atTop.comp tendsto_comap).atTop_div_const (log_pos hb)

end OneLtB

section BPosAndBLtOne

variable (b_pos : 0 < b) (b_lt_one : b < 1)
include b_lt_one

private theorem b_ne_one : b ≠ 1 := by linarith

include b_pos

@[simp]
theorem logb_le_logb_of_base_lt_one (h : 0 < x) (h₁ : 0 < y) : logb b x ≤ logb b y ↔ y ≤ x := by
  rw [← log_div_log, ← log_div_log, div_le_div_right_of_neg (log_neg b_pos b_lt_one),
    log_le_log_iff h₁ h]

theorem logb_lt_logb_of_base_lt_one (hx : 0 < x) (hxy : x < y) : logb b y < logb b x := by
  rw [← log_div_log, ← log_div_log, div_lt_div_right_of_neg (log_neg b_pos b_lt_one)]
  exact log_lt_log hx hxy

@[simp]
theorem logb_lt_logb_iff_of_base_lt_one (hx : 0 < x) (hy : 0 < y) :
    logb b x < logb b y ↔ y < x := by
  rw [← log_div_log, ← log_div_log, div_lt_div_right_of_neg (log_neg b_pos b_lt_one)]
  exact log_lt_log_iff hy hx

theorem logb_le_iff_le_rpow_of_base_lt_one (hx : 0 < x) : logb b x ≤ y ↔ b ^ y ≤ x := by
  rw [← rpow_le_rpow_left_iff_of_base_lt_one b_pos b_lt_one, rpow_logb b_pos (b_ne_one b_lt_one) hx]

theorem logb_lt_iff_lt_rpow_of_base_lt_one (hx : 0 < x) : logb b x < y ↔ b ^ y < x := by
  rw [← rpow_lt_rpow_left_iff_of_base_lt_one b_pos b_lt_one, rpow_logb b_pos (b_ne_one b_lt_one) hx]

theorem le_logb_iff_rpow_le_of_base_lt_one (hy : 0 < y) : x ≤ logb b y ↔ y ≤ b ^ x := by
  rw [← rpow_le_rpow_left_iff_of_base_lt_one b_pos b_lt_one, rpow_logb b_pos (b_ne_one b_lt_one) hy]

theorem lt_logb_iff_rpow_lt_of_base_lt_one (hy : 0 < y) : x < logb b y ↔ y < b ^ x := by
  rw [← rpow_lt_rpow_left_iff_of_base_lt_one b_pos b_lt_one, rpow_logb b_pos (b_ne_one b_lt_one) hy]

theorem logb_pos_iff_of_base_lt_one (hx : 0 < x) : 0 < logb b x ↔ x < 1 := by
  rw [← logb_one (b := b) (hb0 := b_pos.ne') (hb := (log_neg b_pos b_lt_one).ne.isUnit),
    logb_lt_logb_iff_of_base_lt_one b_pos b_lt_one zero_lt_one hx]

theorem logb_pos_of_base_lt_one (hx : 0 < x) (hx' : x < 1) : 0 < logb b x := by
  rw [logb_pos_iff_of_base_lt_one b_pos b_lt_one hx]
  exact hx'

theorem logb_neg_iff_of_base_lt_one (h : 0 < x) : logb b x < 0 ↔ 1 < x := by
  rw [← logb_one (b := b) (hb0 := b_pos.ne') (hb := (log_neg b_pos b_lt_one).ne.isUnit),
    logb_lt_logb_iff_of_base_lt_one b_pos b_lt_one h zero_lt_one]

theorem logb_neg_of_base_lt_one (h1 : 1 < x) : logb b x < 0 :=
  (logb_neg_iff_of_base_lt_one b_pos b_lt_one (lt_trans zero_lt_one h1)).2 h1

theorem logb_nonneg_iff_of_base_lt_one (hx : 0 < x) : 0 ≤ logb b x ↔ x ≤ 1 := by
  rw [← not_lt, logb_neg_iff_of_base_lt_one b_pos b_lt_one hx, not_lt]

theorem logb_nonneg_of_base_lt_one (hx : 0 < x) (hx' : x ≤ 1) : 0 ≤ logb b x := by
  rw [logb_nonneg_iff_of_base_lt_one b_pos b_lt_one hx]
  exact hx'

theorem logb_nonpos_iff_of_base_lt_one (hx : 0 < x) : logb b x ≤ 0 ↔ 1 ≤ x := by
  rw [← not_lt, logb_pos_iff_of_base_lt_one b_pos b_lt_one hx, not_lt]

theorem strictAntiOn_logb_of_base_lt_one :
    StrictAntiOn (fun x : {x : ℝ // x ≠ 0} => logb b x.1 (hx := x.2))
      {x | 0 < x.1} := fun _ hx _ _ hxy =>
  logb_lt_logb_of_base_lt_one b_pos b_lt_one hx hxy

theorem strictMonoOn_logb_of_base_lt_one :
    StrictMonoOn (fun x : {x : ℝ // x ≠ 0} => logb b x.1 (hx := x.2))
      {x | x.1 < 0} := by
  rintro ⟨x, hx0⟩ (hx : x < 0) ⟨y, hy0⟩ (hy : y < 0) hxy
  change logb b x < logb b y
  rw [← logb_abs b y (habs := abs_ne_zero.mpr hy0),
    ← logb_abs b x (habs := abs_ne_zero.mpr hx0)]
  refine logb_lt_logb_of_base_lt_one b_pos b_lt_one (abs_pos.2 hy.ne) ?_
  rwa [abs_of_neg hy, abs_of_neg hx, neg_lt_neg_iff]

theorem logb_injOn_pos_of_base_lt_one :
    Set.InjOn (fun x : {x : ℝ // x ≠ 0} => logb b x.1 (hx := x.2))
      {x | 0 < x.1} :=
  (strictAntiOn_logb_of_base_lt_one b_pos b_lt_one).injOn

theorem eq_one_of_pos_of_logb_eq_zero_of_base_lt_one
    (h₁ : 0 < x) (h₂ : logb b x = 0) : x = 1 := by
  apply Real.eq_one_of_pos_of_log_eq_zero h₁
  exact div_eq_zero_iff.mp (by simpa only [← log_div_log] using h₂)

theorem logb_ne_zero_of_pos_of_ne_one_of_base_lt_one (hx_pos : 0 < x) (hx : x ≠ 1) : logb b x ≠ 0 :=
  mt (eq_one_of_pos_of_logb_eq_zero_of_base_lt_one b_pos b_lt_one hx_pos) hx

theorem tendsto_logb_atTop_of_base_lt_one :
    Tendsto (fun x : {x : ℝ // x ≠ 0} => logb b x.1 (hx := x.2))
      (comap Subtype.val atTop) atBot := by
  simpa only [← log_div_log, div_eq_mul_inv₀, Function.comp_def] using
    (tendsto_log_atTop.comp tendsto_comap).atTop_mul_const_of_neg
      (inv_lt_zero.mpr (log_neg b_pos b_lt_one))

end BPosAndBLtOne

@[norm_cast]
theorem floor_logb_natCast {b : ℕ} (hb : 1 < b) {r : ℝ} (hr : 0 < r) :
    ⌊logb b r⌋ = Int.log b r := by
  have hb1' : 1 < (b : ℝ) := Nat.one_lt_cast.mpr hb
  have hb0 : (b : ℝ) ≠ 0 := (zero_lt_one.trans hb1').ne'
  apply le_antisymm
  · rw [← Int.zpow_le_iff_le_log hb hr, ← rpow_intCast b (h := fun _ => hb0)]
    refine le_of_le_of_eq ?_ (rpow_logb (zero_lt_one.trans hb1') hb1'.ne' hr)
    exact rpow_le_rpow_of_exponent_le hb1'.le (Int.floor_le _)
  · rw [Int.le_floor, le_logb_iff_rpow_le hb1' hr, rpow_intCast (h := fun _ => hb0)]
    exact Int.zpow_log_le_self hb hr

@[norm_cast]
theorem ceil_logb_natCast {b : ℕ} (hb : 1 < b) {r : ℝ} (hr : 0 < r) :
    ⌈logb b r⌉ = Int.clog b r := by
  have hb1' : 1 < (b : ℝ) := Nat.one_lt_cast.mpr hb
  have hb0 : (b : ℝ) ≠ 0 := (zero_lt_one.trans hb1').ne'
  apply le_antisymm
  · rw [Int.ceil_le, logb_le_iff_le_rpow hb1' hr, rpow_intCast (h := fun _ => hb0)]
    exact Int.self_le_zpow_clog hb hr
  · rw [← Int.le_zpow_iff_clog_le hb hr, ← rpow_intCast b (h := fun _ => hb0)]
    refine (rpow_logb (zero_lt_one.trans hb1') hb1'.ne' hr).symm.trans_le ?_
    exact rpow_le_rpow_of_exponent_le hb1'.le (Int.le_ceil _)

@[norm_cast]
theorem natFloor_logb_natCast {b : ℕ} (hb : 1 < b) {n : ℕ} (hn : n ≠ 0) :
    ⌊logb b n⌋₊ = Nat.log b n := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  rw [← Nat.cast_inj (R := ℤ), Int.natCast_floor_eq_floor, floor_logb_natCast hb hn',
    Int.log_natCast hb hn]
  exact logb_nonneg (Nat.one_lt_cast.2 hb) (Nat.one_le_cast.2 (Nat.pos_of_ne_zero hn))

@[norm_cast]
theorem natCeil_logb_natCast {b : ℕ} (hb : 1 < b) {n : ℕ} (hn : n ≠ 0) :
    ⌈logb b n⌉₊ = Nat.clog b n := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  rw [← Nat.cast_inj (R := ℤ), Int.natCast_ceil_eq_ceil, ceil_logb_natCast hb hn',
    Int.clog_natCast hb hn]
  exact logb_nonneg (Nat.one_lt_cast.2 hb) (Nat.one_le_cast.2 (Nat.pos_of_ne_zero hn))

lemma natLog_le_logb {a b : ℕ} (hb : 1 < b) (ha : a ≠ 0) : Nat.log b a ≤ Real.logb b a := by
  apply le_trans _ (Int.floor_le ((b : ℝ).logb a))
  rw [Real.floor_logb_natCast hb (Nat.cast_pos.2 (Nat.pos_of_ne_zero ha)), Int.log_natCast hb ha,
    Int.cast_natCast]

lemma log2_le_logb (n : ℕ) {hn : n ≠ 0} : Nat.log2 n ≤ Real.logb 2 n := by
  calc (Nat.log2 n : ℝ) = Nat.log 2 n := mod_cast Nat.log2_eq_log_two hn
  _ ≤ Real.logb 2 n := natLog_le_logb Nat.one_lt_two hn

@[simp]
theorem logb_eq_zero {hx : x ≠ 0} {hb0 : b ≠ 0} {hb : IsUnit (Real.log b)} :
    logb b x = 0 ↔ x = 1 ∨ x = -1 := by
  simp only [← log_div_log, div_eq_zero_iff, log_eq_zero, hx, false_or]

theorem tendsto_logb_nhdsNE_zero (hb : 1 < b) :
    Tendsto (fun x : {x : ℝ // x ≠ 0} => logb b x.1 (hx := x.2))
      (comap Subtype.val (𝓝[≠] 0)) atBot := by
  simpa only [← log_div_log, Function.comp_def] using
    (tendsto_log_nhdsNE_zero.comp tendsto_comap).atBot_div_const (log_pos hb)

theorem tendsto_logb_nhdsNE_zero_of_base_lt_one (hb₀ : 0 < b) (hb : b < 1) :
    Tendsto (fun x : {x : ℝ // x ≠ 0} => logb b x.1 (hx := x.2))
      (comap Subtype.val (𝓝[≠] 0)) atTop := by
  simpa only [← log_div_log, Function.comp_def, div_eq_mul_inv₀] using
    (tendsto_log_nhdsNE_zero.comp tendsto_comap).atBot_mul_const_of_neg
      (inv_lt_zero.2 (log_neg hb₀ hb))

lemma tendsto_logb_nhdsGT_zero (hb : 1 < b) :
    Tendsto (fun x : {x : ℝ // x ≠ 0} => logb b x.1 (hx := x.2))
      (comap Subtype.val (𝓝[>] 0)) atBot := by
  simpa only [← log_div_log, Function.comp_def] using
    (tendsto_log_nhdsGT_zero.comp tendsto_comap).atBot_div_const (log_pos hb)

lemma tendsto_logb_nhdsGT_zero_of_base_lt_one (hb₀ : 0 < b) (hb : b < 1) :
    Tendsto (fun x : {x : ℝ // x ≠ 0} => logb b x.1 (hx := x.2))
      (comap Subtype.val (𝓝[>] 0)) atTop := by
  simpa only [← log_div_log, Function.comp_def, div_eq_mul_inv₀] using
    (tendsto_log_nhdsGT_zero.comp tendsto_comap).atBot_mul_const_of_neg
      (inv_lt_zero.2 (log_neg hb₀ hb))

/--
The function `|logb b x|` tends to `+∞` as `x` tendsto `+∞`.
See also `tendsto_logb_atTop` and `tendsto_logb_atTop_of_base_lt_one`.
-/
lemma tendsto_abs_logb_atTop {hb0 : b ≠ 0} {hb : IsUnit (Real.log b)} :
    Tendsto (fun x : {x : ℝ // x ≠ 0} => |logb b x.1 (hx := x.2)|)
      (comap Subtype.val atTop) atTop := by
  simpa only [← log_div_log, abs_div, Function.comp_def] using
    (tendsto_abs_atTop_atTop.comp (tendsto_log_atTop.comp tendsto_comap)).atTop_div_const
      (abs_pos.mpr hb.ne_zero)

/-- The base logarithm is continuous on its nonzero input domain. -/
@[fun_prop]
theorem continuous_logb {hb0 : b ≠ 0} {hb : IsUnit (Real.log b)} :
    Continuous (fun x : {x : ℝ // x ≠ 0} => logb b x.1 (hx := x.2)) := by
  simpa only [← log_div_log] using continuous_log.div_const₀ (Real.log b) (hy := hb)

theorem continuousOn_logb {hb0 : b ≠ 0} {hb : IsUnit (Real.log b)} :
    ContinuousOn (fun x : {x : ℝ // x ≠ 0} => logb b x.1 (hx := x.2)) univ :=
  continuous_logb.continuousOn

/-- Restriction of the base logarithm to positive inputs is continuous. -/
@[fun_prop]
theorem continuous_logb' {hb0 : b ≠ 0} {hb : IsUnit (Real.log b)} :
    Continuous (fun x : {x : ℝ // 0 < x} => logb b x.1 (hx := x.2.ne')) := by
  simpa only [← log_div_log] using continuous_log'.div_const₀ (Real.log b) (hy := hb)

theorem continuousAt_logb {hb0 : b ≠ 0} {hb : IsUnit (Real.log b)} (hx : x ≠ 0) :
    ContinuousAt (fun x : {x : ℝ // x ≠ 0} => logb b x.1 (hx := x.2)) ⟨x, hx⟩ :=
  continuous_logb.continuousAt

theorem logb_prod {hb0 : b ≠ 0} {hb : IsUnit (Real.log b)} {α : Type*} (s : Finset α)
    (f : α → ℝ) (hf : ∀ x ∈ s, f x ≠ 0) :
    logb b (∏ i ∈ s, f i) (hx := by classical exact Finset.prod_ne_zero_iff.mpr hf) =
      ∑ i : s, logb b (f i) (hx := hf i i.2) := by
  simp only [← log_div_log, log_prod hf, Finset.sum_div]
  exact (Finset.sum_coe_sort s (fun i => log (f i) / log b)).symm

protected theorem _root_.Finsupp.logb_prod {hb0 : b ≠ 0} {hb : IsUnit (Real.log b)}
    {α β : Type*} [Zero β] (f : α →₀ β) (g : α → β → ℝ)
    (hg : ∀ a, g a (f a) = 0 → f a = 0) :
    logb b (f.prod g) (hx := by
      classical
      exact Finset.prod_ne_zero_iff.mpr fun a ha hz => Finsupp.mem_support_iff.mp ha (hg a hz)) =
    ∑ a : f.support, logb b (g a (f a))
      (hx := fun hz => Finsupp.mem_support_iff.mp a.2 (hg a hz)) := by
  exact logb_prod f.support (fun a => g a (f a))
    (fun a ha hz => Finsupp.mem_support_iff.mp ha (hg a hz))

theorem logb_nat_eq_sum_factorization {hb0 : b ≠ 0}
    {hb : IsUnit (Real.log b)} (n : ℕ) {hn : n ≠ 0} :
    logb b n = ∑ p : n.factorization.support, (n.factorization p : ℝ) *
      logb b (p : ℕ) (hx := by
        apply Nat.cast_ne_zero.mpr
        intro hzero
        have hp := Finsupp.mem_support_iff.mp p.2
        simp [hzero] at hp) := by
  simp only [← log_div_log, log_nat_eq_sum_factorization n, Finsupp.sum,
    Finset.sum_div, mul_div_assoc₀]
  exact (Finset.sum_coe_sort n.factorization.support
    (fun p => (n.factorization p : ℝ) * (log p / log b))).symm

theorem tendsto_pow_logb_div_mul_add_atTop {hb0 : b ≠ 0} {hb : IsUnit (Real.log b)}
    (a c : ℝ) (n : ℕ) (ha : a ≠ 0) :
    Tendsto (fun x : {x : ℝ // x ≠ 0 ∧ a * x + c ≠ 0} =>
      Checked.div (logb b x.1 (hx := x.2.1) ^ n) (a * x.1 + c) x.2.2.isUnit)
      (comap Subtype.val atTop) (𝓝 0) := by
  have ht : Tendsto
      (fun x : {x : ℝ // x ≠ 0 ∧ a * x + c ≠ 0} =>
        (⟨x.1, x.2.2⟩ : {x : ℝ // a * x + c ≠ 0}))
      (comap Subtype.val atTop) (comap Subtype.val atTop) :=
    tendsto_comap_iff.mpr tendsto_comap
  simpa only [← log_div_log, Function.comp_def, div_pow₀, div_div₀, mul_comm, zero_div] using
    ((tendsto_pow_log_div_mul_add_atTop a c n ha).comp ht).div_const₀
      (log b ^ n) (hy := hb.pow n)

theorem isLittleO_pow_logb_id_atTop {hb0 : b ≠ 0} {hb : IsUnit (Real.log b)} {n : ℕ} :
    (fun x : {x : ℝ // x ≠ 0} => logb b x.1 (hx := x.2) ^ n) =o[comap Subtype.val atTop]
      (fun x => x.1) := by
  have h : (fun x : {x : ℝ // x ≠ 0} => log x.1 ^ n) =o[comap Subtype.val atTop]
      (fun x => x.1) := isLittleO_pow_log_id_atTop.comp_tendsto tendsto_comap
  refine (h.const_mul_left ((log b ^ n)⁻¹)).congr_left fun x => ?_
  simp only [← log_div_log, div_eq_mul_inv₀, mul_pow, inv_pow₀]
  ring

theorem isLittleO_logb_id_atTop {hb0 : b ≠ 0} {hb : IsUnit (Real.log b)} :
    (fun x : {x : ℝ // x ≠ 0} => logb b x.1 (hx := x.2)) =o[comap Subtype.val atTop]
      (fun x => x.1) :=
  isLittleO_pow_logb_id_atTop.congr_left fun _ => pow_one _

theorem isLittleO_const_logb_atTop {hb0 : b ≠ 0} {hb : IsUnit (Real.log b)} {c : ℝ} :
    (fun _ : {x : ℝ // x ≠ 0} => c) =o[comap Subtype.val atTop]
      (fun x => logb b x.1 (hx := x.2)) := by
  rw [Asymptotics.isLittleO_const_left, or_iff_not_imp_left]
  intro hc
  exact tendsto_abs_logb_atTop

theorem isBigO_logb_log {hb0 : b ≠ 0} {hb : IsUnit (Real.log b)} :
    (fun x : {x : ℝ // x ≠ 0} => logb b x.1 (hx := x.2)) =O[⊤] (fun x => log x.1) := by
  simpa only [← log_div_log, div_eq_mul_inv₀, mul_comm] using
    (Asymptotics.isBigO_refl (fun x : {x : ℝ // x ≠ 0} => log x.1) ⊤).const_mul_left (log b)⁻¹

theorem isBigO_log_const_mul_log_atTop (c : ℝ) : (fun x ↦ log (c * x)) =O[atTop] log := by
  obtain rfl | hc := eq_or_ne c 0
  · simpa using isLittleO_const_log_atTop.isBigO
  · calc (fun x ↦ log (c * x))
      =ᶠ[atTop] (fun x => log c + log x) := by
          filter_upwards [eventually_gt_atTop 0] with a ha using log_mul hc ha.ne'
      _ =O[atTop] log :=
          isLittleO_const_log_atTop.isBigO.add (Asymptotics.isBigO_refl ..)

theorem isBigO_log_mul_const_log_atTop (c : ℝ) : (fun x ↦ log (x * c)) =O[atTop] log := by
  simpa [mul_comm] using isBigO_log_const_mul_log_atTop c

theorem isBigO_logb_const_mul_log_atTop {hb0 : b ≠ 0} {hb : IsUnit (Real.log b)} (c : ℝ) :
    (fun x : {x : ℝ // c * x ≠ 0} => logb b (c * x.1) (hx := x.2))
      =O[comap Subtype.val atTop] (fun x => log x.1) := by
  simpa only [← log_div_log, div_eq_mul_inv₀, mul_comm, Function.comp_def] using
    ((isBigO_log_const_mul_log_atTop c).comp_tendsto tendsto_comap).const_mul_left (log b)⁻¹

theorem isBigO_logb_mul_const_log_atTop {hb0 : b ≠ 0} {hb : IsUnit (Real.log b)} (c : ℝ) :
    (fun x : {x : ℝ // x * c ≠ 0} => logb b (x.1 * c) (hx := x.2))
      =O[comap Subtype.val atTop] (fun x => log x.1) := by
  simpa only [← log_div_log, div_eq_mul_inv₀, mul_comm, Function.comp_def] using
    ((isBigO_log_mul_const_log_atTop c).comp_tendsto tendsto_comap).const_mul_left (log b)⁻¹

end Real

section Continuity

open Real

variable {α : Type*}
variable {b : ℝ} {hb0 : b ≠ 0} {hb : IsUnit (Real.log b)}

theorem Filter.Tendsto.logb {f : α → ℝ} {l : Filter α} {x : ℝ}
    (h : Tendsto f l (𝓝 x)) (hx : x ≠ 0) :
    Tendsto (fun y : {y : α // f y ≠ 0} => logb b (f y.1) (hx := y.2))
      (comap Subtype.val l) (𝓝 (logb b x)) := by
  simpa only [← log_div_log, Function.comp_def] using
    ((h.comp tendsto_comap).log hx).div_const₀ (Real.log b) (hy := hb)

variable [TopologicalSpace α] {f : α → ℝ} {s : Set α} {a : α}

@[fun_prop]
theorem Continuous.logb (hf : Continuous f) (h₀ : ∀ x, f x ≠ 0) :
    Continuous (fun x => logb b (f x) (hx := h₀ x)) := by
  simpa only [← log_div_log] using (hf.log h₀).div_const₀ (Real.log b) (hy := hb)

@[fun_prop]
nonrec theorem ContinuousAt.logb (hf : ContinuousAt f a) (h₀ : f a ≠ 0) :
    ContinuousAt (fun x : {x : α // f x ≠ 0} => logb b (f x.1) (hx := x.2)) ⟨a, h₀⟩ := by
  have hv : ContinuousAt (Subtype.val : {x : α // f x ≠ 0} → α) ⟨a, h₀⟩ :=
    continuous_subtype_val.continuousAt
  simpa only [← log_div_log, Function.comp_def] using
    ((hf.log h₀).comp hv).div_const₀ (Real.log b) (hy := hb)

nonrec theorem ContinuousWithinAt.logb (hf : ContinuousWithinAt f s a) (h₀ : f a ≠ 0) :
    ContinuousWithinAt (fun x : {x : α // f x ≠ 0} => logb b (f x.1) (hx := x.2))
      (Subtype.val ⁻¹' s) ⟨a, h₀⟩ := by
  have hv : ContinuousWithinAt (Subtype.val : {x : α // f x ≠ 0} → α)
      (Subtype.val ⁻¹' s) ⟨a, h₀⟩ := continuous_subtype_val.continuousWithinAt
  simpa only [← log_div_log, Function.comp_def] using
    ((hf.log h₀).comp hv (fun x hx => hx)).div_const₀ (Real.log b) (hy := hb)

@[fun_prop]
theorem ContinuousOn.logb (hf : ContinuousOn f s) (h₀ : ∀ x ∈ s, f x ≠ 0) :
    Continuous (fun x : s => logb b (f x.1) (hx := h₀ x.1 x.2)) := by
  simpa only [← log_div_log, Set.domRestrict] using
    ((continuousOn_iff_continuous_domRestrict).mp (hf.log h₀)).div_const₀ (Real.log b) (hy := hb)

end Continuity

section TendstoCompAddSub

open Filter

namespace Real

variable {b : ℝ} {hb0 : b ≠ 0} {hb : IsUnit (Real.log b)}

theorem tendsto_logb_comp_add_sub_logb (y : ℝ) :
    Tendsto (fun x : {x : ℝ // x ≠ 0 ∧ x + y ≠ 0} =>
      logb b (x.1 + y) (hx := x.2.2) - logb b x.1 (hx := x.2.1))
      (comap Subtype.val atTop) (𝓝 0) := by
  simpa only [← log_div_log, sub_div, zero_div, Function.comp_def] using
    ((tendsto_log_comp_add_sub_log y).comp tendsto_comap).div_const₀ (Real.log b) (hy := hb)

theorem tendsto_logb_nat_add_one_sub_logb :
    Tendsto (fun k : {k : ℕ // k ≠ 0} =>
      logb b (k.1 + 1 : ℕ) - logb b k.1 (hx := Nat.cast_ne_zero.mpr k.2))
      (comap Subtype.val atTop) (𝓝 0) := by
  have ht : Tendsto (fun k : {k : ℕ // k ≠ 0} =>
      (⟨(k.1 : ℝ), Nat.cast_ne_zero.mpr k.2, by positivity⟩ :
        {x : ℝ // x ≠ 0 ∧ x + 1 ≠ 0}))
      (comap Subtype.val atTop) (comap Subtype.val atTop) :=
    tendsto_comap_iff.mpr (tendsto_natCast_atTop_atTop.comp tendsto_comap)
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
    (tendsto_logb_comp_add_sub_logb (b := b) 1).comp ht

end Real

end TendstoCompAddSub

section Induction

/-- Induction principle for intervals of real numbers: if a proposition `P` is true
on `[x₀, r * x₀)` and if `P` for `[x₀, r^n * x₀)` implies `P` for `[r^n * x₀, r^(n+1) * x₀)`,
then `P` is true for all `x ≥ x₀`. -/
lemma Real.induction_Ico_mul {P : ℝ → Prop} (x₀ r : ℝ) (hr : 1 < r) (hx₀ : 0 < x₀)
    (base : ∀ x ∈ Set.Ico x₀ (r * x₀), P x)
    (step : ∀ n : ℕ, n ≥ 1 → (∀ z ∈ Set.Ico x₀ (r ^ n * x₀), P z) →
      (∀ z ∈ Set.Ico (r ^ n * x₀) (r ^ (n + 1) * x₀), P z)) :
    ∀ x ≥ x₀, P x := by
  suffices ∀ n : ℕ, ∀ x ∈ Set.Ico x₀ (r ^ (n + 1) * x₀), P x by
    intro x hx
    have hx' : 0 < x / x₀ := div_pos (hx₀.trans_le hx) hx₀
    refine this ⌊logb r (x / x₀)⌋₊ x ?_
    rw [mem_Ico, ← div_lt_iff₀ hx₀, ← rpow_natCast, ← logb_lt_iff_lt_rpow hr hx', Nat.cast_add,
      Nat.cast_one]
    exact ⟨hx, Nat.lt_floor_add_one _⟩
  intro n
  induction n with
  | zero => simpa using base
  | succ n ih =>
    exact fun x hx => (Ico_subset_Ico_union_Ico hx).elim (ih x) (step (n + 1) (by simp) ih _)

end Induction
