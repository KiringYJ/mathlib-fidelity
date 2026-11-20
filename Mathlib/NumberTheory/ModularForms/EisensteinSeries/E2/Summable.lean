/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, David Loeffler
-/

module

public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Defs
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion

/-!
# Summability of E2

We collect here lemmas about the summability of the Eisenstein series `E2` that will be used to
prove how it transforms under the slash action.

## Main Results

The key results concern the difference between two different orders of summation for the
telescoping series `∑_{m,n} (1/(mz + n) - 1/(mz + n + 1))`:

1. **`tsum_symmetricIco_tsum_sub_eq`**: Summing first over `n` (in symmetric intervals), then `m`:
   `∑'[symmetricIco] n : ℤ, ∑' m : ℤ, (1/(mz+n) - 1/(mz+n+1)) = -2πi/z`

2. **`tsum_tsum_symmetricIco_sub_eq`**: Summing first over `m`, then `n` (in symmetric intervals):
   `∑' m : ℤ, ∑'[symmetricIco] n : ℤ, (1/(mz+n) - 1/(mz+n+1)) = 0`

The difference `-2πi/z` between these two orderings is precisely the correction term
`D2` that appears in the transformation formula for `G2` under the action of `S`.

## Proof Strategy

1. For fixed `m ≠ 0`, the inner sum over `n` telescopes to zero (each term cancels with its
   neighbor), establishing the first identity.

2. For fixed `n`, the inner sum over `m` can be computed using the cotangent series expansion.
   As `n → ±∞` in symmetric intervals, these sums contribute `-2πi/z`.

-/

open UpperHalfPlane hiding I σ

open Filter Complex Finset SummationFilter

open scoped Interval Real Topology Nat ArithmeticFunction.sigma

public noncomputable section

namespace EisensteinSeries

variable (z : ℍ)

local notation "𝕢" z:100 => cexp (2 * π * I * z)

private lemma e2Summand_pos_row (m : ℕ+) :
    e2Summand m z = -4 * π ^ 2 * ∑' n : ℕ+, n * cexp (2 * π * I * z) ^ (m * n : ℕ) := by
  let e : {n : ℤ // ![(m : ℤ), n] ≠ 0} ≃ ℤ :=
    Equiv.subtypeUnivEquiv fun n ↦ eisensteinPair_ne_zero (.inl (by exact_mod_cast m.pos.ne'))
  let w : ℍ := ⟨m * z, by simpa using z.2⟩
  have hs := qExpansion_identity_pnat (k := 1) le_rfl w
  simp only [Nat.reduceAdd, Nat.factorial_one, Nat.cast_one, div_one₀, pow_one, one_div₀] at hs
  have hrow : e2Summand m z = ∑' n : ℤ, Checked.inv (((w : ℂ) + n) ^ 2)
      ((integerComplement_add_ne_zero w.coe_mem_integerComplement n).isUnit.pow 2) := by
    rw [e2Summand, ← e.tsum_eq]
    refine tsum_congr fun n ↦ ?_
    refine (eisSummand_nat_eq 2 n.2 z).trans ?_
    change Checked.inv (((((m : ℕ) : ℤ) : ℂ) * z + (n.val : ℂ)) ^ 2) _ = _
    simp only [w, Int.cast_natCast, e, Equiv.subtypeUnivEquiv, Equiv.coe_fn_mk]
  rw [hrow, hs]
  have hc : (-2 * (π : ℂ) * I) ^ 2 = -4 * π ^ 2 := by
    rw [mul_pow, I_sq]
    ring
  rw [hc]
  congr 1
  refine tsum_congr fun n ↦ ?_
  simp only [w, ← Complex.exp_nat_mul]
  congr 2
  push_cast
  ring

private lemma G2_partial_sum_eq (N : ℕ) : ∑ m ∈ Icc (-N : ℤ) N, e2Summand m z =
    2 * riemannZeta 2 + ∑ m ∈ range N, -8 * π ^ 2 *
      ∑' n : ℕ+, n * 𝕢 z ^ ((m + 1) * n) := by
  rw [sum_Icc_of_even_eq_range (e2Summand_even z), Finset.sum_range_succ', smul_add,
    nsmul_eq_mul, Nat.cast_zero, e2Summand_zero_eq_two_riemannZeta_two]
  simp only [nsmul_eq_mul, Nat.cast_ofNat, mul_sum]
  have hs (m : ℕ) : 2 * e2Summand ((m + 1 : ℕ) : ℤ) z = -8 * π ^ 2 *
      ∑' n : ℕ+, n * cexp (2 * π * I * z) ^ ((m + 1) * n) := by
    rw [show e2Summand ((m + 1 : ℕ) : ℤ) z = _ from e2Summand_pos_row z ⟨m + 1, by omega⟩]
    simp only [PNat.mk_coe]
    ring
  simp_rw [hs]
  ring

private lemma aux_G2_tendsto : Tendsto
    (fun N ↦ ∑ m ∈ range N, -8 * π ^ 2 * ∑' n : ℕ+, n * 𝕢 z ^ ((m + 1) * n)) atTop
    (𝓝 (-8 * π ^ 2 * ∑' n : ℕ+, σ 1 n * 𝕢 z ^ (n : ℕ))) := by
  have : -8 * π ^ 2 * ∑' n : ℕ+, σ 1 n * 𝕢 z ^ (n : ℕ) =
      ∑' m : ℕ, (-8 * π ^ 2 * ∑' n : ℕ+, n * 𝕢 z ^ ((m + 1) * n)) := by
    have := tsum_prod_pow_eq_tsum_sigma 1 (norm_exp_two_pi_I_lt_one z)
    rw [tsum_pnat_eq_tsum_succ (f := fun d ↦ ∑' c : ℕ+, c ^ 1 * 𝕢 z ^ (d * c : ℕ))] at this
    simp [← tsum_mul_left, ← this]
  rw [this]
  refine (Summable.mul_left _ ?_).hasSum.comp tendsto_finset_range
  rw [← summable_pnat_iff_summable_succ (f := fun b ↦ ∑' c : ℕ+, c * 𝕢 z ^ (b * c : ℕ))]
  apply (summable_prod_mul_pow 1 (norm_exp_two_pi_I_lt_one z)).prod.congr
  simp [← exp_nsmul]

lemma hasSum_e2Summand_symmetricIcc : HasSum (e2Summand · z)
    (2 * riemannZeta 2 - 8 * π ^ 2 * ∑' n : ℕ+, σ 1 n * 𝕢 z ^ (n : ℕ)) (symmetricIcc ℤ) := by
  simpa [HasSum, -symmetricIcc_filter, symmetricIcc_eq_map_Icc_nat, Function.comp_def,
    G2_partial_sum_eq] using! (aux_G2_tendsto z).const_add _

lemma summable_e2Summand_symmetricIcc : Summable (e2Summand · z) (symmetricIcc ℤ) :=
  (hasSum_e2Summand_symmetricIcc z).summable

lemma G2_eq_tsum_cexp : G2 z = 2 * riemannZeta 2 - 8 * π ^ 2 * ∑' n : ℕ+, σ 1 n * 𝕢 z ^ (n : ℕ) :=
  (hasSum_e2Summand_symmetricIcc z).tsum_eq

/-- The q-expansion of the normalised weight-2 Eisenstein series:
`E₂(z) = 1 - 24 ∑_{n≥1} σ₁(n) qⁿ`. -/
lemma E2_eq_tsum_cexp : E2 z = 1 - 24 * ∑' n : ℕ+, σ 1 n * 𝕢 z ^ (n : ℕ) := by
  simp [E2, G2_eq_tsum_cexp, riemannZeta_two]
  field

/-- The `q`-expansion of `E2` as a `HasSum` over `ℕ`. -/
theorem hasSum_qExpansion_E2 :
    HasSum (fun m : ℕ ↦ (if m = 0 then 1 else -24 * σ 1 m : ℂ) • 𝕢 z ^ m) (E2 z) := by
  have hS : Summable fun n : ℕ ↦ σ 1 (n + 1) * 𝕢 z ^ (n + 1) :=
    (summable_nat_add_iff 1).mpr (summable_sigma_mul_cexp_pow (k := 2) (one_le_two) z)
  rw [← hasSum_nat_add_iff' 1]
  convert! (hS.mul_left (-24)).hasSum using 1
  · ext : 1
    simp [mul_assoc]
  · rw [E2_eq_tsum_cexp, tsum_pnat_eq_tsum_succ (f := fun n ↦ σ 1 n * 𝕢 z ^ n), tsum_mul_left]
    simp

/-- `E2` tends to `1` at `i∞`. -/
theorem tendsto_E2_atImInfty : Tendsto E2 atImInfty (𝓝 1) := by
  let c (m : ℕ) : ℂ := if m = 0 then 1 else -24 * σ 1 m
  have hc : c 0 = 1 := ite_eq_left rfl
  rw [← hc]
  refine tendsto_atImInfty_of_hasSum_qExpansion (h := 1) (c := c) one_pos fun z ↦ ?_
  simpa only [c, Function.Periodic.qParam, ofReal_one, div_one₀] using hasSum_qExpansion_E2 (z := z)

/-- `E2` is bounded at `i∞`. -/
theorem isBoundedAtImInfty_E2 : IsBoundedAtImInfty E2 :=
  tendsto_E2_atImInfty.isBigO_one ℝ

lemma tendsto_e2Summand_atTop_nhds_zero : Tendsto (e2Summand · z) atTop (𝓝 0) :=
  (summable_e2Summand_symmetricIcc z).tendsto_zero_of_even_summable_symmetricIcc (e2Summand_even _)

lemma hasSum_e2Summand_symmetricIco : HasSum (e2Summand · z)
    (2 * riemannZeta 2 - 8 * π ^ 2 * ∑' n : ℕ+, σ 1 n * 𝕢 z ^ (n : ℕ)) (symmetricIco ℤ) := by
  apply (hasSum_e2Summand_symmetricIcc z).hasSum_symmetricIco_of_hasSum_symmetricIcc
  simpa using! (tendsto_e2Summand_atTop_nhds_zero z).neg.comp tendsto_natCast_atTop_atTop

lemma summable_e2Summand_symmetricIco : Summable (e2Summand · z) (symmetricIco ℤ) :=
  (hasSum_e2Summand_symmetricIco z).summable

lemma G2_eq_tsum_symmetricIco : G2 z = ∑'[symmetricIco ℤ] m, e2Summand m z := by
  rw [G2, tsum_symmetricIcc_eq_tsum_symmetricIco (summable_e2Summand_symmetricIcc z)]
  simpa using! (tendsto_e2Summand_atTop_nhds_zero z).neg.comp tendsto_natCast_atTop_atTop

section Auxiliary

open ModularGroup Matrix

variable (z : ℍ)

lemma shiftedLinear_ne_zero (z : ℍ) {m : Fin 2 → ℤ} (hm : m ≠ ![0, -1]) :
    (m 0 : ℂ) * z + m 1 + 1 ≠ 0 := by
  have hv : (![m 0, m 1 + 1] : Fin 2 → ℤ) ≠ 0 := by
    intro h
    apply hm
    have h₀ : m 0 = 0 := by simpa using congrFun h (0 : Fin 2)
    have h₁ : m 1 + 1 = 0 := by simpa using congrFun h (1 : Fin 2)
    ext i
    fin_cases i <;> simp [h₀, show m 1 = -1 by omega]
  simpa [add_assoc] using eisSummand_base_ne_zero hv z

private lemma one_div_linear_sub_one_div_linear_eq (z : ℍ) (a b m : ℤ)
    (ha : IsUnit ((m : ℂ) * z + a)) (hb : IsUnit ((m : ℂ) * z + b)) :
    Checked.inv ((m : ℂ) * z + a) ha - Checked.inv ((m : ℂ) * z + b) hb =
      ((b : ℂ) - a) * Checked.inv (((m : ℂ) * z + a) * ((m : ℂ) * z + b)) (ha.mul hb) := by
  rw [inv_sub_inv, div_eq_mul_inv₀, add_sub_add_left_eq_sub]

lemma summable_left_one_div_linear_sub_one_div_linear (z : ℍ) (a b : ℤ) {D : Type*}
    (m : D → ℤ) (hm : Function.Injective m)
    {ha : ∀ x, IsUnit ((m x : ℂ) * z + a)} {hb : ∀ x, IsUnit ((m x : ℂ) * z + b)} :
    Summable fun x ↦ Checked.inv ((m x : ℂ) * z + a) (ha x) -
      Checked.inv ((m x : ℂ) * z + b) (hb x) := by
  have h := summable_linear_left_mul_linear_left z.ne_zero a b m hm
    (hprod := fun x ↦ (ha x).mul (hb x))
  exact (h.mul_left (b - a : ℂ)).congr fun x ↦
    (one_div_linear_sub_one_div_linear_eq z a b (m x) (ha x) (hb x)).symm

lemma summable_right_one_div_linear_sub_one_div_linear_succ (z : ℍ) (m : ℤ) {D : Type*}
    (n : D → ℤ) (hn : Function.Injective n)
    {ha : ∀ x, IsUnit ((m : ℂ) * z + n x)} {hb : ∀ x, IsUnit ((m : ℂ) * z + n x + 1)} :
    Summable fun x ↦ Checked.inv ((m : ℂ) * z + n x) (ha x) -
      Checked.inv ((m : ℂ) * z + n x + 1) (hb x) := by
  have h := summable_linear_right_add_one_mul_linear_right z m m n hn
    (hprod := fun x ↦ (hb x).mul (ha x))
  refine h.congr fun x ↦ ?_
  rw [inv_sub_inv, add_sub_cancel_left, one_div₀]
  simp only [mul_inv₀, mul_comm]

private lemma eisensteinPair_ne_shift {m n : ℤ} (hm : m ≠ 0 ∨ n ≠ -1) :
    (![m, n] : Fin 2 → ℤ) ≠ ![0, -1] := by
  rintro h
  rcases hm with hm | hn
  · exact hm (by simpa using congrFun h 0)
  · exact hn (by simpa using congrFun h 1)

/-- The horizontal difference of the weight-one lattice terms, including the two
jumps on either side of the omitted origin. -/
@[expose]
def e2HorizontalDifference (z : ℍ) (m n : ℤ) : ℂ :=
  if h₀ : (![m, n] : Fin 2 → ℤ) = 0 then -1 else
  if h₁ : (![m, n] : Fin 2 → ℤ) = ![0, -1] then -1 else
    Checked.inv (((m : ℂ) * z + n + 1) * ((m : ℂ) * z + n))
      ((shiftedLinear_ne_zero z h₁).isUnit.mul (eisSummand_base_ne_zero h₀ z).isUnit)

lemma summable_left_e2HorizontalDifference (z : ℍ) (n : ℤ) :
    Summable fun m : ℤ ↦ e2HorizontalDifference z m n := by
  apply (Set.finite_singleton (0 : ℤ)).summable_compl_iff.mp
  let D := {m : ℤ // m ≠ 0}
  have h₀ (m : D) := eisensteinPair_ne_zero (b := n) (.inl m.2)
  have h₁ (m : D) := eisensteinPair_ne_shift (n := n) (.inl m.2)
  have hA (m : D) : IsUnit ((m.val : ℂ) * z + n) := (eisSummand_base_ne_zero (h₀ m) z).isUnit
  have hB (m : D) : IsUnit ((m.val : ℂ) * z + (n + 1 : ℤ)) := by
    simpa only [Int.cast_add, Int.cast_one, ← add_assoc, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one] using! (shiftedLinear_ne_zero z (h₁ m)).isUnit
  have h := summable_linear_left_mul_linear_left z.ne_zero (n + 1) n (fun x : D ↦ x.val)
    Subtype.coe_injective (hprod := fun x ↦ (hB x).mul (hA x))
  refine h.congr fun x ↦ ?_
  simp only [Function.comp_def, e2HorizontalDifference, dite_eq_right (h₀ x), dite_eq_right (h₁ x),
    Int.cast_add, Int.cast_one, ← add_assoc]
lemma summable_right_e2HorizontalDifference (z : ℍ) (m : ℤ) :
    Summable (e2HorizontalDifference z m) := by
  let s : Set ℤ := {0, -1}
  have hs : s.Finite := (Set.finite_singleton _).insert _
  apply hs.summable_compl_iff.mp
  let D := {n : ℤ // n ∉ s}
  have h₀ (n : D) :=
    eisensteinPair_ne_zero (a := m) (b := n.val) (.inr (fun h ↦ n.2 (by simp [s, h])))
  have h₁ (n : D) :=
    eisensteinPair_ne_shift (m := m) (n := n.val) (.inr (fun h ↦ n.2 (by simp [s, h])))
  have h := summable_linear_right_add_one_mul_linear_right z m m (fun n : D ↦ n.val)
    Subtype.coe_injective (hprod := fun n ↦ (shiftedLinear_ne_zero z (h₁ n)).isUnit.mul
      (eisSummand_base_ne_zero (h₀ n) z).isUnit)
  refine h.congr fun n ↦ ?_
  simp only [Function.comp_def, e2HorizontalDifference, dite_eq_right (h₀ n), dite_eq_right (h₁ n)]

/-- The column of the weight-two lattice sum with the origin omitted. -/
@[expose]
def e2Column (n : ℤ) (z : ℍ) : ℂ :=
  ∑' m : {m : ℤ // ![m, n] ≠ 0}, eisSummand 2 ![(m : ℤ), n] z (fun _ ↦ m.2)

private lemma e2Column_eq (z : ℍ) (n : ℤ) :
    e2Column n z = Checked.inv ((z : ℂ) ^ 2) (z.ne_zero.isUnit.pow 2) * e2Summand n (S • z) := by
  let e : {m : ℤ // ![-n, m] ≠ 0} ≃ {m : ℤ // ![m, n] ≠ 0} :=
    Equiv.subtypeEquiv (Equiv.refl ℤ) fun m ↦ by
      apply not_congr
      constructor <;> intro h
      · have hn : -n = 0 := by simpa using congrFun h 0
        have hm : m = 0 := by simpa using congrFun h 1
        ext i; fin_cases i <;> simp [hm, neg_eq_zero.mp hn]
      · have hm : m = 0 := by simpa using congrFun h 0
        have hn : n = 0 := by simpa using congrFun h 1
        ext i; fin_cases i <;> simp [hm, hn]
  have hv (m : ℤ) : ![-n, m] ᵥ* (S : Matrix (Fin 2) (Fin 2) ℤ) = ![m, n] := by
    ext i
    fin_cases i <;> simp [vecMul, S]
  have heq : e2Summand (-n) (S • z) = e2Summand n (S • z) := e2Summand_even _ n
  rw [← heq, e2Summand, e2Column, ← e.tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun m ↦ ?_
  have h := eisSummand_SL2_apply 2 ![-n, (m : ℤ)] S z (hi := fun _ ↦ m.2)
    (hiA := fun _ ↦ hv m ▸ (e m).2)
  simp only [denom_S, zpow_ofNat₀, hv] at h
  rw [h, ← mul_assoc, inv_mul_cancel₀, one_mul]
  rfl
private lemma sum_e2Column (z : ℍ) (s : Finset ℤ) :
    (∑ n ∈ s, e2Column n z) = ∑' m : ℤ,
      ∑ n ∈ s.preimage (Subtype.val : {n : ℤ // ![m, n] ≠ 0} → ℤ) Subtype.coe_injective.injOn,
        eisSummand 2 ![m, n.val] z (fun _ ↦ n.2) := by
  classical
  let W (m n : ℤ) := if h : (![m, n] : Fin 2 → ℤ) ≠ 0 then eisSummand 2 ![m, n] z (fun _ ↦ h) else 0
  have hsupp (n : ℤ) : Function.support (W · n) ⊆ {m | (![m, n] : Fin 2 → ℤ) ≠ 0} := by
    intro m hm h
    exact hm (dite_eq_right (not_not_intro h))
  have hcol (n : ℤ) : e2Column n z = ∑' m : ℤ, W m n := by
    rw [← tsum_subtype_eq_of_support_subset (hsupp n), e2Column]
    refine tsum_congr fun m ↦ ?_
    simp only [W, dite_eq_left m.2]
  have hrow (m : ℤ) : (∑ n ∈ s, W m n) = _ := (Finset.sum_preimage
    (Subtype.val : {n : ℤ // ![m, n] ≠ 0} → ℤ) s Subtype.coe_injective.injOn (W m)
    (fun n _ hn ↦ by
      have h : ¬(![m, n] : Fin 2 → ℤ) ≠ 0 := fun h ↦ hn ⟨⟨n, h⟩, rfl⟩
      simp only [W, dite_eq_right h])).symm
  have hs (n : ℤ) : Summable (W · n) := by
    have hpow (m : {m : ℤ // ![m, n] ≠ 0}) : IsUnit (((m.val : ℂ) * z + n) ^ (2 : ℤ)) := by
      simpa only [zpow_ofNat₀, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one] using! (eisSummand_base_ne_zero m.2 z).isUnit.pow 2
    have hlin := linear_left_summable z.ne_zero n (k := 2) le_rfl
      (fun m : {m : ℤ // ![m, n] ≠ 0} ↦ m.val) Subtype.coe_injective (hpower := hpow)
    suffices h : Summable (fun m : {m : ℤ // ![m, n] ≠ 0} ↦ W m.val n) from
      ((hasSum_subtype_iff_of_support_subset (hsupp n)).mp h.hasSum).summable
    refine hlin.congr fun m ↦ ?_
    simp only [W, dite_eq_left m.2]
    refine Eq.trans ?_ (eisSummand_nat_eq 2 m.2 z).symm
    simp only [zpow_ofNat₀, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  simp_rw [hcol]
  rw [← Summable.tsum_finsetSum (fun n _ ↦ hs n)]
  refine tsum_congr fun m ↦ (hrow m).trans ?_
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  exact dite_eq_left n.2
private lemma hasSum_e2Column (z : ℍ) : HasSum (e2Column · z)
    (Checked.inv ((z : ℂ) ^ 2) (z.ne_zero.isUnit.pow 2) * G2 (S • z)) (symmetricIco ℤ) := by
  have hs : HasSum (e2Summand · (S • z)) (G2 (S • z)) (symmetricIco ℤ) := by
    rw [G2_eq_tsum_symmetricIco]
    exact (summable_e2Summand_symmetricIco _).hasSum
  simpa only [e2Column_eq z] using! hs.mul_left
    (Checked.inv ((z : ℂ) ^ 2) (z.ne_zero.isUnit.pow 2))

lemma tendsto_double_sum_S_act (z : ℍ) :
    Tendsto (fun N : ℕ ↦ ∑' m : ℤ,
      ∑ n ∈ (Finset.Ico (-N : ℤ) N).preimage (Subtype.val : {n : ℤ // ![m, n] ≠ 0} → ℤ)
        Subtype.coe_injective.injOn, eisSummand 2 ![m, n.val] z (fun _ ↦ n.2)) atTop
      (𝓝 (Checked.inv ((z : ℂ) ^ 2) (z.ne_zero.isUnit.pow 2) * G2 (S • z))) := by
  simpa only [← sum_e2Column] using! hasSum_symmetricIco_int_iff.mp (hasSum_e2Column z)

lemma tsum_symmetricIco_tsum_eq_S_act (z : ℍ) : ∑'[symmetricIco ℤ] n, e2Column n z =
    Checked.inv ((z : ℂ) ^ 2) (z.ne_zero.isUnit.pow 2) * G2 (S • z) :=
  (hasSum_e2Column z).tsum_eq

private lemma boundaryUnit (z : ℍ) (m n : ℤ) (hn : n ≠ 0) :
    IsUnit ((m : ℂ) * z + n) :=
  (eisSummand_base_ne_zero (eisensteinPair_ne_zero (.inr hn)) z).isUnit

private def boundaryTerm (z : ℍ) (d : ℕ+) (m : ℤ) : ℂ :=
  Checked.inv ((m : ℂ) * z + (-(d : ℤ) : ℤ))
      (boundaryUnit z m _ (neg_ne_zero.mpr (by exact_mod_cast d.pos.ne'))) -
  Checked.inv ((m : ℂ) * z + (d : ℤ)) (boundaryUnit z m _ (by exact_mod_cast d.pos.ne'))

private lemma telescope_aux (z : ℍ) (m : ℤ) (b : ℕ+) :
    ∑ n ∈ Ico (-(b : ℤ)) b, e2HorizontalDifference z m n = boundaryTerm z b m := by
  let F (n : ℤ) : ℂ := if h : (![m, n] : Fin 2 → ℤ) = 0 then 0 else
    Checked.inv ((m : ℂ) * z + n) (eisSummand_base_ne_zero h z).isUnit
  have hdiff (n : ℤ) : e2HorizontalDifference z m n = F n - F (n + 1) := by
    by_cases h₀ : (![m, n] : Fin 2 → ℤ) = 0
    · have hm : m = 0 := by simpa using congrFun h₀ 0
      have hn : n = 0 := by simpa using congrFun h₀ 1
      subst m n
      norm_num [e2HorizontalDifference, F, show (![0, 0] : Fin 2 → ℤ) = 0 by decide,
        show (![0, 1] : Fin 2 → ℤ) ≠ 0 by decide]
      rw [dite_eq_left (Subsingleton.elim (![] : Fin 0 → ℤ) 0)]
      norm_num
    by_cases h₁ : (![m, n] : Fin 2 → ℤ) = ![0, -1]
    · have hm : m = 0 := by simpa using congrFun h₁ 0
      have hn : n = -1 := by simpa using congrFun h₁ 1
      subst m n
      norm_num [e2HorizontalDifference, F, show (![0, -1] : Fin 2 → ℤ) ≠ 0 by decide,
        show (![0, 0] : Fin 2 → ℤ) = 0 by decide]
      rw [dite_eq_left (Subsingleton.elim (![] : Fin 0 → ℤ) 0)]
      norm_num
    have h₂ : (![m, n + 1] : Fin 2 → ℤ) ≠ 0 := by
      intro h
      have hm : m = 0 := by simpa using congrFun h 0
      have hn : n + 1 = 0 := by simpa using congrFun h 1
      exact h₁ (by rw [hm, show n = -1 by omega])
    have ha : IsUnit ((m : ℂ) * z + n) := (eisSummand_base_ne_zero h₀ z).isUnit
    have hb : IsUnit ((m : ℂ) * z + n + 1) := (shiftedLinear_ne_zero z h₁).isUnit
    simp only [e2HorizontalDifference, F, dite_eq_right h₀, dite_eq_right h₁, dite_eq_right h₂,
      Int.cast_add, Int.cast_one, ← add_assoc]
    rw [inv_sub_inv (ha := ha) (hb := hb), add_sub_cancel_left, one_div₀]
    simp only [mul_inv₀, mul_comm]
  simp_rw [hdiff]
  rw [sum_Ico_int_sub]
  have hp : (b : ℤ) ≠ 0 := by exact_mod_cast b.pos.ne'
  simp only [boundaryTerm, F, dite_eq_right (eisensteinPair_ne_zero (a := m) (.inr hp)),
    dite_eq_right (eisensteinPair_ne_zero (a := m) (.inr (neg_ne_zero.mpr hp)))]

lemma tsum_symmetricIco_linear_sub_linear_add_one_eq_zero (z : ℍ) (m : ℤ) :
    ∑'[symmetricIco ℤ] n : ℤ, e2HorizontalDifference z m n = 0 := by
  apply HasSum.tsum_eq
  rw [hasSum_symmetricIco_int_iff, ← PNat.tendsto_comp_val_iff]
  have hp (b : ℕ+) : (b : ℤ) ≠ 0 := by exact_mod_cast b.pos.ne'
  have hA (b : ℕ+) : IsUnit ((m : ℂ) * z + (b : ℕ)) := by
    simpa using boundaryUnit z m _ (hp b)
  have hB (b : ℕ+) : IsUnit ((m : ℂ) * z - (b : ℕ)) := by
    simpa [sub_eq_add_neg] using
      boundaryUnit z m _ (neg_ne_zero.mpr (hp b))
  have ht : Tendsto (fun b : ℕ+ ↦ (b : ℕ)) atTop atTop := PNat.tendsto_comp_val_iff.mpr tendsto_id
  simp_rw [telescope_aux z m]
  simpa only [boundaryTerm, one_div₀, sub_eq_add_neg, Int.cast_neg, Int.cast_natCast, neg_zero,
    add_zero]
    using! (tendsto_zero_inv_linear_sub z m _ ht (hlinear := hB)).sub
      (tendsto_zero_inv_linear z m _ ht (hlinear := hA))

private lemma boundaryTerm_even (z : ℍ) (d : ℕ+) : (boundaryTerm z d).Even := by
  intro m
  simp only [boundaryTerm, Int.cast_neg, Int.cast_natCast, neg_mul, ← neg_add]
  have he : -((m : ℂ) * z) + d = -((m : ℂ) * z + -(d : ℂ)) := by ring
  simp only [he, inv_neg₀]
  ring

private lemma boundaryTerm_summable (z : ℍ) (d : ℕ+) : Summable (boundaryTerm z d) := by
  let h₀ (m : ℤ) := boundaryUnit z m (-(d : ℤ)) (neg_ne_zero.mpr (by exact_mod_cast d.pos.ne'))
  let h₁ (m : ℤ) := boundaryUnit z m (d : ℤ) (by exact_mod_cast d.pos.ne')
  have hp := summable_linear_left_mul_linear_left z.ne_zero (-(d : ℤ)) (d : ℤ) id
    Function.injective_id
    (hprod := fun m ↦ (h₀ m).mul (h₁ m))
  refine (hp.mul_left ((d : ℂ) - (-d : ℤ))).congr fun m ↦ ?_
  change _ = Checked.inv _ (h₀ m) - Checked.inv _ (h₁ m)
  rw [inv_sub_inv, div_eq_mul_inv₀, add_sub_add_left_eq_sub]
  rfl

private lemma boundaryTerm_zero (z : ℍ) (d : ℕ+) :
    boundaryTerm z d 0 = Checked.div (-2) (d : ℂ) (Nat.cast_ne_zero.mpr d.pos.ne').isUnit := by
  simp only [boundaryTerm, Int.cast_zero, zero_mul, zero_add, Int.cast_neg, Int.cast_natCast,
    inv_neg₀, div_eq_mul_inv₀]
  ring
private def cotPoint (z : ℍ) (d : ℕ+) : ℍ :=
  ⟨Checked.div (-(d : ℂ)) z z.ne_zero.isUnit, im_pnat_div_pos d z⟩

private lemma boundaryTerm_pos (z : ℍ) (d m : ℕ+) :
    let w := cotPoint z d
    let hw := w.coe_mem_integerComplement
    boundaryTerm z d m = Checked.inv (z : ℂ) z.ne_zero.isUnit *
      (Checked.div 1 ((w : ℂ) - m) (by
        simpa only [sub_eq_add_neg, Int.cast_neg, Int.cast_natCast] using
          (integerComplement_add_ne_zero hw (-((m : ℕ) : ℤ))).isUnit) + 1 / ((w : ℂ) + m)) := by
  dsimp only
  let w := cotPoint z d
  have hwz : (w : ℂ) * z = -(d : ℂ) := div_mul_cancel₀ _
  have ha : ((m : ℂ) * z + -(d : ℂ)) = ((w : ℂ) + m) * z := by rw [add_mul, hwz]; ring
  have hb : ((m : ℂ) * z + (d : ℂ)) = -(((w : ℂ) - m) * z) := by rw [sub_mul, hwz]; ring
  simp only [boundaryTerm, Int.cast_natCast, Int.cast_neg, ha, hb, one_div₀, inv_neg₀, mul_inv₀]
  ring
private lemma tsum_boundaryTerm (z : ℍ) (d : ℕ+) :
    ∑' m : ℤ, boundaryTerm z d m = Checked.div 2 (z : ℂ) z.ne_zero.isUnit *
      (π * cot (π * (cotPoint z d : ℂ))
        (sin_pi_mul_ne_zero (cotPoint z d).coe_mem_integerComplement)) := by
  let w := cotPoint z d
  have hw := w.coe_mem_integerComplement
  have hz := z.ne_zero.isUnit
  have hd : IsUnit (d : ℂ) := (Nat.cast_ne_zero.mpr d.pos.ne').isUnit
  have hwz : (w : ℂ) * z = -(d : ℂ) := div_mul_cancel₀ _
  have h := cot_series_rep hw
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat (boundaryTerm_even z d) (boundaryTerm_summable z d),
    boundaryTerm_zero]
  simp_rw [boundaryTerm_pos z d]
  rw [tsum_mul_left, eq_sub_of_add_eq' h.symm]
  simp only [div_eq_mul_inv₀, nsmul_eq_mul, Nat.cast_ofNat]
  have hi : Checked.inv (w : ℂ) w.ne_zero.isUnit = -(z : ℂ) * Checked.inv (d : ℂ) hd := by
    simp only [w, cotPoint, div_eq_mul_inv₀, mul_inv₀, inv_neg₀, inv_inv₀, neg_mul, mul_comm]
  rw [hi]
  field_simp [z.ne_zero, hd.ne_zero]
  ring
private lemma tendsto_boundaryTerm (z : ℍ) :
    Tendsto (fun d : ℕ+ ↦ ∑' m : ℤ, boundaryTerm z d m) atTop
      (𝓝 (Checked.div (-2 * π * I) (z : ℂ) z.ne_zero.isUnit)) := by
  let r := cexp (2 * π * I * (cotPoint z 1 : ℂ))
  have hr : ‖r‖ < 1 := norm_exp_two_pi_I_lt_one (cotPoint z 1)
  have hx (d : ℕ+) : cexp (2 * π * I * (cotPoint z d : ℂ)) = r ^ (d : ℕ) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    simp only [cotPoint, PNat.val_ofNat, Nat.cast_one, div_eq_mul_inv₀]
    ring
  have hrow (d : ℕ+) : (∑' m : ℤ, boundaryTerm z d m) =
      Checked.div 2 (z : ℂ) z.ne_zero.isUnit *
        (-(π * I) - (2 * π * I) * ∑' n : ℕ+, r ^ (n * d : ℕ)) := by
    let u := cexp (2 * π * I * (cotPoint z d : ℂ))
    have hu : ‖u‖ < 1 := norm_exp_two_pi_I_lt_one (cotPoint z d)
    have hp := tsum_zero_pnat_eq_tsum_nat (f := fun n : ℕ ↦ u ^ n)
      (summable_geometric_of_norm_lt_one hu)
    rw [tsum_boundaryTerm, pi_mul_cot_pi_q_exp]
    change _ * (π * I - 2 * π * I * ∑' n : ℕ, u ^ n) = _
    rw [← hp]
    simp only [pow_zero, show u = r ^ (d : ℕ) from hx d, ← pow_mul]
    have hpow (n : ℕ+) : r ^ (d * n : ℕ) = r ^ (n * d : ℕ) := by rw [Nat.mul_comm]
    simp_rw [hpow]
    ring
  simp_rw [hrow]
  have hlim := ((tendsto_zero_geometric_tsum_pnat hr).const_mul (2 * π * I)).const_sub (-(π * I))
  have hc : Checked.div 2 (z : ℂ) z.ne_zero.isUnit * (-(π * I)) =
      Checked.div (-2 * π * I) (z : ℂ) z.ne_zero.isUnit := by simp only [div_eq_mul_inv₀]; ring
  rw [← hc]
  simpa only [mul_zero, sub_zero] using!
    (hlim.const_mul (Checked.div 2 (z : ℂ) z.ne_zero.isUnit))

/-- Summing the lattice difference first down columns gives the correction at infinity. -/
lemma tendsto_tsum_one_div_linear_sub_succ_eq :
    Tendsto (fun N : ℕ+ ↦ ∑ n ∈ Ico (-N : ℤ) N, ∑' m : ℤ, e2HorizontalDifference z m n)
      atTop (𝓝 (Checked.div (-2 * π * I) (z : ℂ) z.ne_zero.isUnit)) := by
  apply (tendsto_boundaryTerm z).congr
  intro N
  rw [← Summable.tsum_finsetSum (fun n _ ↦ summable_left_e2HorizontalDifference z n)]
  exact tsum_congr fun m ↦ (telescope_aux z m N).symm

lemma hasSum_tsum_horizontalDifference :
    HasSum (fun n : ℤ ↦ ∑' m : ℤ, e2HorizontalDifference z m n)
      (Checked.div (-2 * π * I) (z : ℂ) z.ne_zero.isUnit) (symmetricIco ℤ) :=
  hasSum_symmetricIco_int_iff.mpr
    (PNat.tendsto_comp_val_iff.mp (tendsto_tsum_one_div_linear_sub_succ_eq z))

/- These are the two key lemmas, which show that swapping the order of summation gives
results differing by the term `-2 * π * I / z`. -/
lemma tsum_symmetricIco_tsum_sub_eq :
    ∑'[symmetricIco ℤ] n : ℤ, ∑' m : ℤ, e2HorizontalDifference z m n =
      Checked.div (-2 * π * I) (z : ℂ) z.ne_zero.isUnit :=
  (hasSum_tsum_horizontalDifference z).tsum_eq

lemma tsum_tsum_symmetricIco_sub_eq :
    ∑' m : ℤ, ∑'[symmetricIco ℤ] n : ℤ, e2HorizontalDifference z m n = 0 := by
  simp only [tsum_symmetricIco_linear_sub_linear_add_one_eq_zero, tsum_zero]

end Auxiliary

end EisensteinSeries
