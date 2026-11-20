/-
Copyright (c) 2025 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuval Filmus
-/
module

public import Mathlib.RingTheory.Polynomial.Chebyshev
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Tactic.Positivity

/-!
# Chebyshev polynomials over the reals: some extremal properties

* Chebyshev polynomials have largest leading coefficient,
following proof in https://math.stackexchange.com/a/978145/1277
* Chebyshev polynomials maximize iterated derivatives at 1 and beyond

## Main statements

* leadingCoeff_le_of_forall_abs_le_one: If `P` is a real polynomial of degree at most `n` and
  `|P (x)| ≤ 1` for all `x ∈ [-1, 1]` then the leading coefficient of `P` is at most `2 ^ (n - 1)`
* leadingCoeff_eq_iff_of_forall_abs_le_one: When `n ≥ 2`, equality holds iff `P = T_n`
* eval_iterate_derivative_le_of_forall_abs_le_one: If `P` is a real polynomial of degree at most `n`
  and `|P (x)| ≤ 1` for all `x ∈ [-1, 1]` then for all `x ≥ 1`, `P ^ (k) (x) ≤ T_n ^ (k)(x)`
* eval_iterate_derivative_eq_iff_of_forall_abs_le_one: If `0 < k ≤ n` then equality holds iff
  `P = T_n`

## Implementation

We describe the proof for the leading coefficient; the proof for iterated derivatives uses a
similar approach.

By monotonicity of `2 ^ (n - 1)`, we can assume that `P` has degree exactly `n`.
Using Lagrange interpolation, we can give a formula for the leading coefficient of `P`
as a linear combination of the values of `P` on the Chebyshev nodes (sumNodes_eq_coeff).
The Chebyshev polynomial `T_n` has value `±1` on the nodes, with the same signs as the
coefficients of the linear combination (negOnePow_mul_leadingCoeffC_pos).
Since `|P (x)| ≤ 1` on the nodes, this implies that the leading coefficient of `P` is bounded
by that of `T_n`, which is known to equal `2 ^ (n - 1)`.
Moreover, equality holds iff `P` and `T_n` agree on the nodes, which implies that they coincide.
-/
@[expose] public section
namespace Polynomial.Chebyshev

open Polynomial Real

/-- The Chebyshev node at angle `i * π / n`. The degree-zero interpolation grid consists
of the single right endpoint, indexed by zero. -/
noncomputable def node (n i : ℕ) (h : n ≠ 0 ∨ i = 0 := by omega) : ℝ :=
  match i with
  | 0 => 1
  | i + 1 => cos (Checked.div ((i + 1 : ℕ) * π) n
      (Nat.cast_ne_zero.mpr (h.resolve_right (by omega))).isUnit)

lemma node_eq_one {n : ℕ} : node n 0 = 1 := rfl

private lemma node_of_ne_zero {n : ℕ} (hn : n ≠ 0) (i : ℕ) :
    node n i = cos (i * π / n) := by
  cases i <;> simp [node]

lemma node_eq_neg_one {n : ℕ} (hn : n ≠ 0) : node n n = -1 := by
  have h : (n : ℝ) * π / n = π := div_eq_iff.mpr (mul_comm ..)
  rw [node_of_ne_zero hn, h, cos_pi]

lemma node_mem_Icc {n i : ℕ} {h : n ≠ 0 ∨ i = 0} : node n i h ∈ Set.Icc (-1) 1 := by
  rcases h with hn | rfl
  · rw [node_of_ne_zero hn]
    exact ⟨neg_one_le_cos _, cos_le_one _⟩
  · simp [node_eq_one]

lemma eval_T_real_node {n i : ℕ} (hi : i ∈ Finset.Iic n) :
    (T ℝ n).eval (node n i (by have := Finset.mem_Iic.mp hi; omega)) = (-1) ^ i := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [show i = 0 by simpa using Finset.mem_Iic.mp hi]
  have h : (n : ℤ) * (i * π / n) = i * π := by norm_cast; field
  rw [node_of_ne_zero hn, T_real_cos, h, cos_nat_mul_pi]

/-- The grid of the `n + 1` interpolation nodes. -/
noncomputable def gridNode (n : ℕ) (i : Fin (n + 1)) : ℝ :=
  node n i (by have := i.isLt; omega)

lemma strictAntiOn_node (n : ℕ) : StrictAnti (gridNode n) := by
  intro i j hij
  have hn : n ≠ 0 := by have := j.isLt; have := i.isLt; have : i.val < j.val := hij; omega
  have hn' : 0 < (n : ℝ) := by positivity
  have hmem (k : Fin (n + 1)) : (k.val * π / (n : ℝ)) ∈ Set.Icc 0 π := by
    refine ⟨by positivity, (div_le_iff₀ hn').mpr ?_⟩
    rw [mul_comm π]
    gcongr
    exact_mod_cast Nat.le_of_lt_succ k.isLt
  simp only [gridNode, node_of_ne_zero hn]
  apply strictAntiOn_cos (hmem i) (hmem j)
  exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_right (by exact_mod_cast hij) pi_pos) hn'

lemma node_lt {n i j : ℕ} (hj : j ≤ n) (hij : i < j) :
    node n j < node n i :=
  @strictAntiOn_node n ⟨i, by omega⟩ ⟨j, by omega⟩ hij

lemma zero_lt_prod_node_sub_node {n : ℕ} (i : Fin (n + 1)) :
    0 < (-1) ^ i.val * ∏ j ∈ Finset.univ.erase i, (gridNode n i - gridNode n j) := by
  have h₁ : 0 < ∏ j ∈ Finset.Iio i, ((-1) * (gridNode n i - gridNode n j)) :=
    Finset.prod_pos fun j hj ↦ mul_pos_of_neg_of_neg neg_one_lt_zero
      (sub_neg.mpr (strictAntiOn_node n (Finset.mem_Iio.mp hj)))
  rw [Finset.prod_mul_distrib, Finset.prod_const, Fin.card_Iio] at h₁
  have h₂ : 0 < ∏ j ∈ Finset.Ioi i, (gridNode n i - gridNode n j) :=
    Finset.prod_pos fun j hj ↦ sub_pos.mpr (strictAntiOn_node n (Finset.mem_Ioi.mp hj))
  have hu : Finset.univ.erase i = Finset.Iio i ∪ Finset.Ioi i := by
    ext j
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_union, Finset.mem_Iio,
      Finset.mem_Ioi, ne_iff_lt_or_gt]
  have hd : Disjoint (Finset.Iio i) (Finset.Ioi i) :=
    Finset.disjoint_left.mpr fun j hj hj' ↦ (Finset.mem_Iio.mp hj).not_gt (Finset.mem_Ioi.mp hj')
  rw [hu, Finset.prod_union hd, ← mul_assoc]
  exact mul_pos h₁ h₂

private lemma negOnePow_mul_le {α : ℝ} {i : ℕ} (hα : |α| ≤ 1) : (-1) ^ i * α ≤ 1 := by
  apply le_of_abs_le
  rwa [abs_mul, abs_neg_one_pow, one_mul]

private lemma negOnePow_mul_negOnePow_mul_cancel {α β : ℝ} {i : ℕ} :
    ((-1) ^ i * α) * ((-1) ^ i * β) = α * β := calc
  _ = ((-1) ^ i * (-1) ^ i) * α * β := by ring
  _ = α * β := by simp [← mul_pow]

/-- For a polynomial `P` and coefficient function `c`, `sumNodes n c P` is a linear combination
of `P` evaluated at the `n`'th order Chebyshev nodes, with coefficients taken from `c`. -/
noncomputable def sumNodes (n : ℕ) (c : Fin (n + 1) → ℝ) (P : ℝ[X]) :=
  ∑ i, P.eval (gridNode n i) * c i

private theorem eval_T_gridNode {n : ℕ} (i : Fin (n + 1)) :
    (T ℝ n).eval (gridNode n i) = (-1) ^ i.val :=
  eval_T_real_node (Finset.mem_Iic.mpr (Nat.le_of_lt_succ i.isLt))

private theorem eval_node_mul_le {n : ℕ} {c : Fin (n + 1) → ℝ}
    (hc : ∀ i, 0 ≤ (-1) ^ i.val * c i) {P : ℝ[X]}
    (hp : ∀ x ∈ Set.Icc (-1) 1, |P.eval x| ≤ 1) (i : Fin (n + 1)) :
    P.eval (gridNode n i) * c i ≤ (T ℝ n).eval (gridNode n i) * c i := calc
  _ = ((-1) ^ i.val * P.eval (gridNode n i)) * ((-1) ^ i.val * c i) :=
    negOnePow_mul_negOnePow_mul_cancel.symm
  _ ≤ 1 * ((-1) ^ i.val * c i) :=
    mul_le_mul_of_nonneg_right (negOnePow_mul_le (hp _ node_mem_Icc)) (hc i)
  _ = _ := by rw [one_mul, eval_T_gridNode]

theorem sumNodes_le_sumNodes_T {n : ℕ} {c : Fin (n + 1) → ℝ}
    (hc : ∀ i, 0 ≤ (-1) ^ i.val * c i)
    {P : ℝ[X]} (hPbnd : ∀ x ∈ Set.Icc (-1) 1, |P.eval x| ≤ 1) :
    sumNodes n c P ≤ sumNodes n c (T ℝ n) :=
  Finset.sum_le_sum fun i _ ↦ eval_node_mul_le hc hPbnd i

theorem sumNodes_eq_sumNodes_T_iff {n : ℕ} {c : Fin (n + 1) → ℝ}
    (hc : ∀ i, 0 < (-1) ^ i.val * c i)
    {P : ℝ[X]} (hPdeg : P.degree ≤ n) (hPbnd : ∀ x ∈ Set.Icc (-1) 1, |P.eval x| ≤ 1) :
    (sumNodes n c P = sumNodes n c (T ℝ n)) ↔ P = T ℝ n := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ rfl⟩
  apply eq_of_degrees_lt_of_eval_finset_eq (Finset.univ.image (gridNode n))
  · simpa [Finset.card_image_of_injective _ (strictAntiOn_node n).injective] using
      (hPdeg.trans_lt (by exact_mod_cast Nat.lt_succ_self n))
  · rw [Finset.card_image_of_injective _ (strictAntiOn_node n).injective, Finset.card_univ,
      Fintype.card_fin, degree_T, Int.natAbs_natCast]
    exact_mod_cast Nat.lt_succ_self n
  intro x hx
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
  have hterms := (Finset.sum_eq_sum_iff_of_le
    (fun j (_ : j ∈ Finset.univ) ↦ eval_node_mul_le (fun t ↦ (hc t).le) hPbnd j)).mp h
  have hci : c i ≠ 0 := fun hz ↦ (hc i).ne' (by rw [hz, mul_zero])
  exact mul_right_cancel₀ hci (hterms i (Finset.mem_univ _))

/-- The contribution of a node to the leading coefficient in Lagrange interpolation. -/
private noncomputable def leadingCoeffC (n : ℕ) (i : Fin (n + 1)) : ℝ :=
  Checked.inv (∏ j ∈ Finset.univ.erase i, (gridNode n i - gridNode n j))
    (Lagrange.isUnit_prod_sub (fun _ _ h ↦ (strictAntiOn_node n).injective h))

private theorem sumNodes_eq_coeff {n : ℕ} {P : ℝ[X]} (hP : P.degree ≤ n) :
    sumNodes n (leadingCoeffC n) P = P.coeff n := by
  have hdeg : P.degree < (Finset.univ : Finset (Fin (n + 1))).card := by
    simpa using hP.trans_lt (by exact_mod_cast Nat.lt_succ_self n)
  have h := Lagrange.coeff_eq_sum (s := Finset.univ) (strictAntiOn_node n).injective.injOn hdeg
  simpa [sumNodes, leadingCoeffC, div_eq_mul_inv₀, Finset.sum_subtype] using h.symm

private theorem sumNodes_T_eq (n : ℕ) :
    sumNodes n (leadingCoeffC n) (T ℝ n) = 2 ^ (n - 1) := by
  rw [sumNodes_eq_coeff (by simp)]
  trans (T ℝ n).leadingCoeff
  · simp [leadingCoeff]
  · simp

private theorem negOnePow_mul_leadingCoeffC_pos {n : ℕ} (i : Fin (n + 1)) :
    0 < (-1) ^ i.val * leadingCoeffC n i := by
  let p := ∏ j ∈ Finset.univ.erase i, (gridNode n i - gridNode n j)
  have hp : IsUnit p := Lagrange.isUnit_prod_sub fun _ _ h ↦ (strictAntiOn_node n).injective h
  have hsign : 0 < (-1) ^ i.val * p := zero_lt_prod_node_sub_node i
  have h : 0 < ((-1) ^ i.val * p)⁻¹ := inv_pos.mpr hsign
  simpa [leadingCoeffC, p, mul_inv₀, ← inv_pow₀, inv_neg_one₀, mul_comm] using h

theorem coeff_le_of_forall_abs_le_one {n : ℕ} {P : ℝ[X]}
    (hPdeg : P.degree ≤ n) (hPbnd : ∀ x ∈ Set.Icc (-1) 1, |P.eval x| ≤ 1) :
    P.coeff n ≤ 2 ^ (n - 1) := by
  convert! sumNodes_le_sumNodes_T (fun i => le_of_lt <| negOnePow_mul_leadingCoeffC_pos i) hPbnd
  · rw [sumNodes_eq_coeff hPdeg]
  · rw [sumNodes_T_eq]

theorem leadingCoeff_le_of_forall_abs_le_one {n : ℕ} {P : ℝ[X]}
    (hPdeg : P.degree ≤ n) (hPbnd : ∀ x ∈ Set.Icc (-1) 1, |P.eval x| ≤ 1) :
    P.leadingCoeff ≤ 2 ^ (n - 1) := by
  by_cases P = 0
  case pos hP => simp [hP]
  case neg hP =>
    lift P.degree to ℕ using degree_ne_bot.mpr hP with d hd
    replace hPdeg : d ≤ n := (WithBot.coe_le rfl).mp hPdeg
    rw [leadingCoeff, natDegree_eq_of_degree_eq_some hd.symm]
    grw [coeff_le_of_forall_abs_le_one (le_of_eq hd.symm) hPbnd, hPdeg]
    norm_num

theorem coeff_eq_iff_of_forall_abs_le_one {n : ℕ} {P : ℝ[X]}
    (hPdeg : P.degree ≤ n) (hPbnd : ∀ x ∈ Set.Icc (-1) 1, |P.eval x| ≤ 1) :
    P.coeff n = 2 ^ (n - 1) ↔ P = T ℝ n := by
  convert! sumNodes_eq_sumNodes_T_iff (fun i => negOnePow_mul_leadingCoeffC_pos i) hPdeg hPbnd
  · rw [sumNodes_eq_coeff hPdeg]
  · rw [sumNodes_T_eq]

theorem leadingCoeff_eq_iff_of_forall_abs_le_one {n : ℕ} {P : ℝ[X]} (hn : 2 ≤ n)
    (hPdeg : P.degree ≤ n) (hPbnd : ∀ x ∈ Set.Icc (-1) 1, |P.eval x| ≤ 1) :
    P.leadingCoeff = 2 ^ (n - 1) ↔ P = T ℝ n := by
  refine ⟨fun hP => ?_, fun hP => by simp [hP]⟩
  apply (coeff_eq_iff_of_forall_abs_le_one hPdeg hPbnd).mp
  suffices hPdeg' : n ≤ P.degree by
    replace hPdeg' : P.degree = n := eq_of_le_of_ge hPdeg hPdeg'
    rwa [leadingCoeff, natDegree_eq_of_degree_eq_some hPdeg'] at hP
  lift P.degree to ℕ with d hd
  · contrapose! hP
    rw [degree_eq_bot.mp hP, leadingCoeff_zero]
    positivity
  replace hP := ge_of_eq hP
  contrapose! hP
  have : d - 1 < n - 1 := by grind [Nat.cast_withBot, WithBot.coe_le_coe, WithBot.coe_lt_coe]
  calc P.leadingCoeff ≤ 2 ^ (d - 1) := leadingCoeff_le_of_forall_abs_le_one (le_of_eq hd.symm) hPbnd
  _ < 2 ^ (n - 1) := by gcongr; norm_num

/-- Coefficients used to compute the iterated derivative of a polynomial given its values on the
Chebyshev nodes. -/
private noncomputable def iterateDerivativeC (n k : ℕ) (x : ℝ) (i : Fin (n + 1)) :=
  k.factorial * leadingCoeffC n i *
    ∑ t ∈ (Finset.univ.erase i).powersetCard (n - k), ∏ a ∈ t, (x - gridNode n a)

private theorem sumNodes_eq_eval_iterate_derivative {n k : ℕ} (hk : k ≤ n) (x : ℝ)
    {P : ℝ[X]} (hP : P.degree ≤ n) :
    sumNodes n (iterateDerivativeC n k x) P = (derivative^[k] P).eval x := by
  have hdeg : P.degree < (Finset.univ : Finset (Fin (n + 1))).card := by
    simpa using hP.trans_lt (by exact_mod_cast Nat.lt_succ_self n)
  have h := Lagrange.eval_iterate_derivative_eq_sum (s := Finset.univ) (k := k) (P := P)
    (strictAntiOn_node n).injective.injOn hdeg (by simpa using Nat.lt_succ_of_le hk) x
  rw [h, Finset.mul_sum]
  simp only [sumNodes, iterateDerivativeC, leadingCoeffC, div_eq_mul_inv₀,
    Finset.card_univ, Fintype.card_fin, Nat.add_sub_add_right]
  let e : Fin (n + 1) ≃ (Finset.univ : Finset (Fin (n + 1))) :=
    ⟨fun i ↦ ⟨i, Finset.mem_univ _⟩, Subtype.val, fun _ ↦ rfl, fun _ ↦ rfl⟩
  refine Fintype.sum_equiv e _ _ fun i ↦ ?_
  dsimp [e]
  ring

private theorem negOnePow_mul_iterateDerivativeC_nonneg {n k : ℕ} (i : Fin (n + 1))
    {x : ℝ} (hx : 1 ≤ x) :
    0 ≤ (-1) ^ i.val * iterateDerivativeC n k x i := by
  rw [iterateDerivativeC, ← mul_assoc, mul_left_comm ((-1) ^ i.val)]
  refine mul_nonneg (mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos k))
    (negOnePow_mul_leadingCoeffC_pos i)).le (Finset.sum_nonneg fun t _ ↦ ?_)
  exact Finset.prod_nonneg fun a _ ↦ sub_nonneg.mpr (node_mem_Icc.2.trans hx)

private theorem negOnePow_mul_iterateDerivativeC_pos {n k : ℕ} (hk₁ : 0 < k) (hk₂ : k ≤ n)
    (i : Fin (n + 1)) {x : ℝ} (hx : 1 ≤ x) :
    0 < (-1) ^ i.val * iterateDerivativeC n k x i := by
  rw [iterateDerivativeC, ← mul_assoc, mul_left_comm ((-1) ^ i.val)]
  apply mul_pos (mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos k))
    (negOnePow_mul_leadingCoeffC_pos i))
  refine Finset.sum_pos' (fun t _ ↦ Finset.prod_nonneg fun a _ ↦
    sub_nonneg.mpr (node_mem_Icc.2.trans hx)) ?_
  have hc : n - k ≤ ((Finset.univ.erase i).erase (0 : Fin (n + 1))).card := by
    have h := Finset.pred_card_le_card_erase (s := Finset.univ.erase i) (a := (0 : Fin (n + 1)))
    simp only [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin,
      Nat.add_sub_cancel] at h
    omega
  obtain ⟨t, ht, hcard⟩ := Finset.exists_subset_card_eq hc
  refine ⟨t, Finset.mem_powersetCard.mpr ⟨fun a ha ↦ Finset.mem_of_mem_erase (ht ha), hcard⟩,
    Finset.prod_pos fun a ha ↦ ?_⟩
  have ha0 : 0 < a := Fin.pos_iff_ne_zero.mpr (Finset.ne_of_mem_erase (ht ha))
  exact sub_pos.mpr ((strictAntiOn_node n ha0).trans_le (by simpa [gridNode, node_eq_one] using hx))

theorem eval_iterate_derivative_le_of_forall_abs_le_one {n : ℕ} {P : ℝ[X]}
    {k : ℕ} {x : ℝ} (hx : 1 ≤ x)
    (hPdeg : P.degree ≤ n) (hPbnd : ∀ x ∈ Set.Icc (-1) 1, |P.eval x| ≤ 1) :
    (derivative^[k] P).eval x ≤ (derivative^[k] (T ℝ n)).eval x := by
  by_cases! hk : n < k
  · rw [iterate_derivative_eq_zero_of_degree_lt (by grw [hPdeg]; simpa),
      iterate_derivative_eq_zero_of_degree_lt (by simp [hk])]
  convert!
    sumNodes_le_sumNodes_T (fun i => negOnePow_mul_iterateDerivativeC_nonneg i hx) hPbnd using 1
  · rw [sumNodes_eq_eval_iterate_derivative hk x hPdeg]
  · rw [sumNodes_eq_eval_iterate_derivative hk x (le_of_eq (degree_T ℝ n))]

theorem eval_iterate_derivative_eq_iff_of_bounded {n : ℕ} {P : ℝ[X]}
    {k : ℕ} (hk₁ : 0 < k) (hk₂ : k ≤ n) {x : ℝ} (hx : 1 ≤ x)
    (hPdeg : P.degree ≤ n) (hPbnd : ∀ x ∈ Set.Icc (-1) 1, |P.eval x| ≤ 1) :
    (derivative^[k] P).eval x = (derivative^[k] (T ℝ n)).eval x ↔ P = T ℝ n := by
  convert!
    sumNodes_eq_sumNodes_T_iff (fun i => negOnePow_mul_iterateDerivativeC_pos hk₁ hk₂ i hx)
      hPdeg hPbnd using 2
  · rw [sumNodes_eq_eval_iterate_derivative hk₂ x hPdeg]
  · rw [sumNodes_eq_eval_iterate_derivative hk₂ x (le_of_eq (degree_T ℝ n))]

end Polynomial.Chebyshev
