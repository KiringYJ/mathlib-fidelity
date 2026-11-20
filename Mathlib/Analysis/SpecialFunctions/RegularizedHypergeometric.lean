/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-! # Generalized hypergeometric function

In this file we define the generalized hypergeometric function as well as the Gaussian
hypergeometric function.

The hypergeometric function is a function with parameters `a : Fin p → ℂ` and `b : Fin q → ℂ`.

Note that in this file, we use the *regularized* version of the hypergeometric function: its
coefficients use the entire reciprocal Gamma function, giving in the case of the Gaussian
hypergeometric function the series representation
$$\sum_j \frac{(a)^n (b)^n}{\Gamma(c + n) n!} z^ n,$$
where `(a)^n` denotes the rising Pochhammer symbol.

These coefficients are defined for all lower parameters, as in the scaled generalized
hypergeometric series [DLMF (16.2.5)](https://dlmf.nist.gov/16.2.E5). In the Gaussian case this is
Olver's series [DLMF (15.2.2)](https://dlmf.nist.gov/15.2.E2), including `c = -k` for `k : ℕ`.
The ordinary hypergeometric function generally has a pole at those parameter values.
Away from the poles of the lower Gamma factors, multiplying by `∏ i, Gamma (b i)` recovers
the usual hypergeometric function.

## Definitions
For the general case we have
* `Complex.regularizedHGFunCoeff`: the coefficients
* `Complex.regularizedHGFunSeries`: the formal multilinear series
* `Complex.regularizedHGFun`: the function

For the Gaussian case (`p = 2` and `q = 1`), we define
* `Complex.regularizedGaussHGFunSeries`: the formal multilinear series
* `Complex.regularizedGaussHGFun`: the function

## Results

Convergence:
* `radius_regularizedHGFunSeries_eq_top_of_finite`: in the case that the series reduces to a
  polynomial, the radius of convergence is infinite.
* `radius_regularizedHGFunSeries_eq_top`: if `p < q + 1`, then the series has infinite convergence
  radius.
* `radius_regularizedHGFunSeries_eq_one`: if `p = q + 1`, then the series has convergence radius
  `1`.
* `Complex.radius_regularizedGaussHGFunSeries_eq_one`: the Gaussian hypergeometric series has
  convergence radius `1`.

-/

@[expose] public noncomputable section

namespace Complex

open Filter

open scoped Nat Real Topology

variable {p q : ℕ}

variable {a : Multiset ℂ} {b : Multiset ℂ} {n m : ℕ} {j k : ℂ}

/-- The coefficients of the regularized hypergeometric series. -/
def regularizedHGFunCoeff (a : Multiset ℂ) (b : Multiset ℂ) (n : ℕ) : ℂ :=
  (a.map (ascPochhammer ℂ n).eval).prod * (b.map (reciprocalGamma <| · + n)).prod / n !

attribute [grind .] Nat.factorial_ne_zero

@[grind =]
theorem regularizedHGFunCoeff_eq_zero_iff :
    regularizedHGFunCoeff a b n = 0 ↔
    (∃ j ∈ a, ∃ k < n, j = -k) ∨ ∃ j ∈ b, ∃ (m : ℕ), j + n = -m := by
  unfold regularizedHGFunCoeff
  simp
  grind

variable (a b n m) in
theorem regularizedHGFunCoeff_eq_zero_right (hb : -(n : ℂ) - m ∈ b := by grind) :
    regularizedHGFunCoeff a b n = 0 := by grind

variable (a b n m) in
theorem regularizedHGFunCoeff_eq_zero_left (ha : -(m : ℂ) ∈ a := by grind)
    (hm : m < n := by grind) :
  regularizedHGFunCoeff a b n = 0 := by grind

/-- The product of the shifted lower parameters is nonzero when no parameter equals `-n`. -/
theorem prod_add_natCast_ne_zero (hb : ∀ k ∈ b, k ≠ -n) :
    (b.map (· + (n : ℂ))).prod ≠ 0 := by
  apply Multiset.prod_ne_zero
  intro h
  obtain ⟨k, hk, hk0⟩ := Multiset.mem_map.mp h
  exact hb k hk (eq_neg_iff_add_eq_zero.mpr hk0)

theorem regularizedHGFunCoeff_ne_zero_lower (h : regularizedHGFunCoeff a b n ≠ 0) :
    ∀ k ∈ b, k ≠ -n := by
  intro k hk heq
  apply h
  apply regularizedHGFunCoeff_eq_zero_iff.mpr
  exact Or.inr ⟨k, hk, 0, by simp [heq]⟩

/-- The coefficient recurrence after clearing the lower-parameter factors. This identity also
holds when a lower parameter is a nonpositive integer. -/
theorem regularizedHGFunCoeff_mul_add_one :
    regularizedHGFunCoeff a b (n + 1) * (n + 1) * (b.map (· + (n : ℂ))).prod =
      regularizedHGFunCoeff a b n * (a.map (· + (n : ℂ))).prod := by
  have hA : (a.map (ascPochhammer ℂ (n + 1)).eval).prod =
      (a.map (ascPochhammer ℂ n).eval).prod * (a.map (· + (n : ℂ))).prod := by
    simp [ascPochhammer_succ_right, Multiset.prod_map_mul]
  have hB : (b.map (fun j ↦ reciprocalGamma (j + (n + 1)))).prod *
      (b.map (· + (n : ℂ))).prod = (b.map (fun j ↦ reciprocalGamma (j + n))).prod := by
    rw [← Multiset.prod_map_mul]
    congr 1
    refine Multiset.map_congr rfl fun j _ ↦ ?_
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc, mul_comm] using
      (reciprocalGamma_eq_self_mul_reciprocalGamma_add_one (j + n)).symm
  have clearFac (i : ℕ) : regularizedHGFunCoeff a b i * (i ! : ℂ) =
      (a.map (ascPochhammer ℂ i).eval).prod * (b.map (fun j ↦ reciprocalGamma (j + i))).prod := by
    unfold regularizedHGFunCoeff
    exact div_mul_cancel₀ _
  have hfac : ((n + 1)! : ℂ) = ((n : ℂ) + 1) * (n ! : ℂ) := by
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
  apply mul_right_cancel₀ (show (n ! : ℂ) ≠ 0 from Nat.cast_ne_zero.mpr n.factorial_ne_zero)
  calc
    _ = (regularizedHGFunCoeff a b (n + 1) * ((n + 1)! : ℂ)) *
          (b.map (· + (n : ℂ))).prod := by rw [hfac]; ring
    _ = (regularizedHGFunCoeff a b n * (n ! : ℂ)) * (a.map (· + (n : ℂ))).prod := by
      rw [clearFac (n + 1), clearFac n, hA, Nat.cast_succ, ← hB]
      ring
    _ = _ := by ring

/-- Recursion formula for the coefficients of the hypergeometric series.

This is mainly used to calculate the convergence radius. -/
theorem regularizedHGFunCoeff_add_one (hb : ∀ k ∈ b, k ≠ -n) :
    regularizedHGFunCoeff a b (n + 1) = regularizedHGFunCoeff a b n *
      Checked.div ((a.map (· + (n : ℂ))).prod)
        ((b.map (· + (n : ℂ))).prod * (n + 1))
        ((prod_add_natCast_ne_zero hb).isUnit.mul (Nat.cast_add_one_ne_zero n).isUnit) := by
  rw [← mul_div_assoc₀, eq_div_iff]
  simpa only [mul_assoc, mul_comm, mul_left_comm] using
    (regularizedHGFunCoeff_mul_add_one (a := a) (b := b) (n := n))

/-- Recursion formula for the coefficients of the hypergeometric series.

This is mainly used to calculate the convergence radius. -/
theorem regularizedHGFunCoeff_add_one_div_self (h : regularizedHGFunCoeff a b n ≠ 0) :
    regularizedHGFunCoeff a b (n + 1) / regularizedHGFunCoeff a b n =
      Checked.div ((a.map (· + (n : ℂ))).prod)
        ((b.map (· + (n : ℂ))).prod * (n + 1))
        ((prod_add_natCast_ne_zero (regularizedHGFunCoeff_ne_zero_lower h)).isUnit.mul
          (Nat.cast_add_one_ne_zero n).isUnit) := by
  rw [regularizedHGFunCoeff_add_one (regularizedHGFunCoeff_ne_zero_lower h),
    mul_div_cancel_left₀]

private theorem multiset_prod_eq_pow_mul_multiset_prod (a : Multiset ℂ) (hn : n ≠ 0) :
    (a.map (· + (n : ℂ))).prod = n ^ a.card * (a.map (· / (n : ℂ) + 1)).prod := calc
  _ = (a.map (fun j ↦ n * (j / (n : ℂ) + 1))).prod := by
    congr; ext; field_simp
  _ = _ := by
    simp [Multiset.prod_map_mul]

private theorem normalized_lower_ne_zero (b : Multiset ℂ) (hn : n ≠ 0)
    (hb : ∀ k ∈ b, k ≠ -n) :
    (b.map (· / (n : ℂ) + 1)).prod * (1 + (n : ℂ)⁻¹) ≠ 0 := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  apply mul_ne_zero
  · intro hzero
    apply prod_add_natCast_ne_zero hb
    rw [multiset_prod_eq_pow_mul_multiset_prod b hn, hzero, mul_zero]
  · intro hzero
    have h := congrArg (fun z : ℂ ↦ z * n) hzero
    simp only [add_mul, one_mul, inv_mul_cancel₀, zero_mul] at h
    exact Nat.cast_add_one_ne_zero n (by simpa only [add_comm] using h)

private theorem multiset_prod_div_multiset_prod_mul (a : Multiset ℂ) (b : Multiset ℂ)
    (hn : n ≠ 0) (hb : ∀ k ∈ b, k ≠ -n) :
    Checked.div (a.map (· + (n : ℂ))).prod
        ((b.map (· + (n : ℂ))).prod * (n + 1))
        ((prod_add_natCast_ne_zero hb).isUnit.mul (Nat.cast_add_one_ne_zero n).isUnit) =
      Checked.div (((n : ℂ) ^ a.card / (n : ℂ) ^ (b.card + 1)) *
        (a.map (· / (n : ℂ) + 1)).prod)
        ((b.map (· / (n : ℂ) + 1)).prod * (1 + (n : ℂ)⁻¹))
        (normalized_lower_ne_zero b hn hb).isUnit := by
  have ht : (n : ℂ) * (1 + (n : ℂ)⁻¹) = (n : ℂ) + 1 := by
    rw [mul_add, mul_one, mul_inv_cancel₀]
  have hscale : (b.map (· + (n : ℂ))).prod * ((n : ℂ) + 1) = (n : ℂ) ^ (b.card + 1) *
      ((b.map (· / (n : ℂ) + 1)).prod * (1 + (n : ℂ)⁻¹)) := by
    rw [multiset_prod_eq_pow_mul_multiset_prod b hn, ← ht, pow_succ]
    ring
  have hcancel : (n : ℂ) ^ a.card / (n : ℂ) ^ (b.card + 1) * (n : ℂ) ^ (b.card + 1) =
      (n : ℂ) ^ a.card := div_mul_cancel₀ _
  rw [div_eq_div_iff, multiset_prod_eq_pow_mul_multiset_prod a hn, hscale]
  linear_combination -hcancel * (a.map (· / (n : ℂ) + 1)).prod *
    ((b.map (· / (n : ℂ) + 1)).prod * (1 + (n : ℂ)⁻¹))

variable (a b) in
/-- The regularized hypergeometric series. -/
def regularizedHGFunSeries : FormalMultilinearSeries ℂ ℂ ℂ :=
  .ofScalars ℂ (regularizedHGFunCoeff a b)

@[simp]
theorem regularizedHGFunSeries_coeff :
    (regularizedHGFunSeries a b).coeff = regularizedHGFunCoeff a b := by
  unfold regularizedHGFunSeries
  ext; simp

@[simp, grind =]
theorem regularizedHGFunSeries_eq_zero :
    regularizedHGFunSeries a b n = 0 ↔ regularizedHGFunCoeff a b n = 0 := by
  apply FormalMultilinearSeries.ofScalars_eq_zero

variable (a b) in
/-- The regularized hypergeometric function on the exact domain where its ordered series
converges. This includes conditionally convergent boundary values. -/
def regularizedHGFun (z : ℂ)
    (_hz : Summable (fun n ↦ regularizedHGFunSeries a b n (fun _ ↦ z))
      (SummationFilter.conditional ℕ)) : ℂ :=
  ∑'[SummationFilter.conditional ℕ] n, regularizedHGFunSeries a b n (fun _ ↦ z)

theorem regularizedHGFun_hasSum (z : ℂ)
    (hz : Summable (fun n ↦ regularizedHGFunSeries a b n (fun _ ↦ z))
      (SummationFilter.conditional ℕ)) :
    HasSum (fun n ↦ regularizedHGFunSeries a b n (fun _ ↦ z)) (regularizedHGFun a b z hz)
      (SummationFilter.conditional ℕ) :=
  hz.hasSum

/-- If there exists `j` and `k : ℕ`, such that `a j = -k`, then the hypergeometric series is finite
and has convergence radius `∞`. -/
theorem radius_regularizedHGFunSeries_eq_top_of_finite (ha : j ∈ a) (hj : j = -n) :
    (regularizedHGFunSeries a b).radius = ⊤ := by
  apply FormalMultilinearSeries.radius_eq_top_of_eventually_eq_zero
  apply eventually_atTop.mpr
  use n + 1
  grind

variable (b) in
/-- If for all `j` and `k : ℕ`, `a j ≠ -k`, then the coefficients of the hypergeometric series
are eventually non-vanishing. -/
theorem eventually_atTop_regularizedHGFunCoeff_ne_zero (h : ∀ j ∈ a, ∀ (k : ℕ), j ≠ -↑k) :
    ∀ᶠ (n : ℕ) in atTop, regularizedHGFunCoeff a b n ≠ 0 := by
  rw [Filter.eventually_atTop]
  use b.toFinset.sup (⌈-re ·⌉₊) + 1
  intro n hn h'
  rw [regularizedHGFunCoeff_eq_zero_iff] at h'
  rcases h' with (h' | ⟨j, hj, m, h'⟩)
  · grind
  · suffices (m : ℝ) < 0 by grind
    suffices -j.re < n by
      have h : j = -m - n := by grind
      simpa [h] using this
    calc
      -j.re ≤ ⌈-j.re⌉₊ := Nat.le_ceil (-j.re)
      _ ≤ b.toFinset.sup (⌈-re ·⌉₊) := mod_cast Finset.le_sup (by grind) (f := (⌈-re ·⌉₊))
      _ < n := by norm_cast

variable (a) in
private theorem tendsto_multiset_prod_div_add_one :
    Tendsto (fun n : {n : ℕ // n ≠ 0} ↦ (a.map (· / ((n : ℕ) : ℂ) + 1)).prod)
      (comap Subtype.val atTop) (𝓝 1) := by
  suffices ∀ i ∈ a, Tendsto (fun n : {n : ℕ // n ≠ 0} ↦ (i / ((n : ℕ) : ℂ) + 1))
      (comap Subtype.val atTop) (𝓝 <| (fun _ : _ ↦ 1) i) by
    simpa using tendsto_multiset_prod _ this
  intro i hi
  simpa using (tendsto_const_div_atTop_nhds_zero_nat i).add_const 1

variable (a b) in
private theorem tendsto_multiset_prod_div_multiset_prod_mul :
    Tendsto (fun n : {n : ℕ // n ≠ 0 ∧ regularizedHGFunCoeff a b n ≠ 0} ↦
      Checked.div (a.map (· / ((n : ℕ) : ℂ) + 1)).prod
        ((b.map (· / ((n : ℕ) : ℂ) + 1)).prod * (1 + ((n : ℕ) : ℂ)⁻¹))
        (normalized_lower_ne_zero b n.2.1
          (regularizedHGFunCoeff_ne_zero_lower n.2.2)).isUnit)
      (comap Subtype.val atTop) (𝓝 1) := by
  let toNonzero : {n : ℕ // n ≠ 0 ∧ regularizedHGFunCoeff a b n ≠ 0} → {n : ℕ // n ≠ 0} :=
    fun n ↦ ⟨n, n.2.1⟩
  have hto : Tendsto toNonzero (comap Subtype.val atTop) (comap Subtype.val atTop) :=
    tendsto_comap_iff.mpr tendsto_comap
  have h := (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℂ)).comp hto
  have hden := ((tendsto_multiset_prod_div_add_one b).comp hto).mul (h.const_add 1)
  have hlim := ((tendsto_multiset_prod_div_add_one a).comp hto).div₀ hden
    (h₀ := fun n ↦ (normalized_lower_ne_zero b n.2.1
      (regularizedHGFunCoeff_ne_zero_lower n.2.2)).isUnit)
    (hb := by simp)
  simpa only [toNonzero, Function.comp_def, add_zero, mul_one, div_one₀] using hlim

private theorem eventually_index_ne_zero (c : ℕ → ℂ) :
    ∀ᶠ n : {n : ℕ // ‖c n‖ ≠ 0} in comap Subtype.val atTop, (n : ℕ) ≠ 0 :=
  (tendsto_comap : Tendsto (Subtype.val : {n : ℕ // ‖c n‖ ≠ 0} → ℕ)
    (comap Subtype.val atTop) atTop).eventually (eventually_ne_atTop (0 : ℕ))

private theorem tendsto_index_of_nonzero_subtype (p : ℕ → Prop) :
    Tendsto (fun n : {n : Subtype p // (n : ℕ) ≠ 0} ↦ (n.1 : ℕ))
      (comap Subtype.val (comap Subtype.val atTop)) atTop :=
  (tendsto_comap : Tendsto (Subtype.val : Subtype p → ℕ)
    (comap Subtype.val atTop) atTop).comp tendsto_comap

/-- If `a.card ≤ b.card`, then the hypergeometric series has infinite convergence radius. -/
@[grind =]
theorem radius_regularizedHGFunSeries_eq_top (h : a.card ≤ b.card) :
    (regularizedHGFunSeries a b).radius = ⊤ := by
  by_cases! ha : ∃ j ∈ a, ∃ k : ℕ, j = -k
  · obtain ⟨j, hj, k, ha⟩ := ha
    apply radius_regularizedHGFunSeries_eq_top_of_finite hj ha
  apply FormalMultilinearSeries.ofScalars_radius_eq_top_of_tendsto
  · apply eventually_atTop_regularizedHGFunCoeff_ne_zero b ha
  · simp only [Nat.succ_eq_add_one]
    let D := {n : ℕ // n ≠ 0 ∧ regularizedHGFunCoeff a b n ≠ 0}
    let ψ : D → {n : ℕ // n ≠ 0} := fun n ↦ ⟨n, n.2.1⟩
    have hψ : Tendsto ψ (comap Subtype.val atTop) (comap Subtype.val atTop) :=
      tendsto_comap_iff.mpr tendsto_comap
    have h₁ : Tendsto (fun n : D ↦ ((n : ℕ) : ℂ) ^ a.card / ((n : ℕ) : ℂ) ^ (b.card + 1))
        (comap Subtype.val atTop) (𝓝 0) := by
      let k := b.card + 1 - a.card
      have hk : k ≠ 0 := by dsimp [k]; omega
      have hk' : a.card + k = b.card + 1 := by dsimp [k]; omega
      have hlim := ((tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℂ)).comp hψ).pow k
      rw [zero_pow hk] at hlim
      apply hlim.congr
      intro n
      dsimp only [ψ, Function.comp_def]
      have hpow : ((n : ℕ) : ℂ) ^ (b.card + 1) =
          ((n : ℕ) : ℂ) ^ a.card * ((n : ℕ) : ℂ) ^ k := by rw [← pow_add, hk']
      rw [eq_div_iff, inv_pow₀, hpow, mul_left_comm, inv_mul_cancel₀, mul_one]
    have := (h₁.mul (tendsto_multiset_prod_div_multiset_prod_mul a b)).norm
    simp only [mul_one, norm_zero] at this
    apply (tendsto_comap_val_iff
      (p := fun n : {n : ℕ // ‖regularizedHGFunCoeff a b n‖ ≠ 0} ↦ (n : ℕ) ≠ 0)
      (eventually_index_ne_zero (regularizedHGFunCoeff a b))).mp
    let toRatio : {n : {n : ℕ // ‖regularizedHGFunCoeff a b n‖ ≠ 0} // (n : ℕ) ≠ 0} → D :=
      fun n ↦ ⟨n.1, n.2, norm_ne_zero_iff.mp n.1.2⟩
    have hto : Tendsto toRatio (comap Subtype.val (comap Subtype.val atTop))
        (comap Subtype.val atTop) :=
      tendsto_comap_iff.mpr (tendsto_index_of_nonzero_subtype _)
    apply (this.comp hto).congr'
    filter_upwards [] with n
    dsimp only [toRatio, Function.comp_def]
    have hn₁ := norm_ne_zero_iff.mp n.1.2
    rw [← Complex.norm_div (hw := hn₁.isUnit), regularizedHGFunCoeff_add_one_div_self hn₁,
      multiset_prod_div_multiset_prod_mul a b n.2
        (regularizedHGFunCoeff_ne_zero_lower hn₁), mul_div₀]

/-- If `a.card = b.card + 1`, then the hypergeometric series has convergence radius `1`, unless it
is a polynomial. -/
@[grind =]
theorem radius_regularizedHGFunSeries_eq_one (h : a.card = b.card + 1)
    (h' : ∀ j ∈ a, ∀ k : ℕ, j ≠ -k) :
    (regularizedHGFunSeries a b).radius = 1 := by
  have h_ne := eventually_atTop_regularizedHGFunCoeff_ne_zero b h'
  have hlim : Tendsto (fun n : {n : ℕ // ‖regularizedHGFunCoeff a b n‖ ≠ 0} ↦
      Checked.div ‖regularizedHGFunCoeff a b n.1.succ‖ ‖regularizedHGFunCoeff a b n.1‖
        n.2.isUnit) (comap Subtype.val atTop) (𝓝 (1 : ℝ)) := by
    have := (tendsto_multiset_prod_div_multiset_prod_mul a b).norm
    simp only [norm_one] at this
    apply (tendsto_comap_val_iff
      (p := fun n : {n : ℕ // ‖regularizedHGFunCoeff a b n‖ ≠ 0} ↦ (n : ℕ) ≠ 0)
      (eventually_index_ne_zero (regularizedHGFunCoeff a b))).mp
    let toRatio : {n : {n : ℕ // ‖regularizedHGFunCoeff a b n‖ ≠ 0} // (n : ℕ) ≠ 0} →
        {n : ℕ // n ≠ 0 ∧ regularizedHGFunCoeff a b n ≠ 0} :=
      fun n ↦ ⟨n.1, n.2, norm_ne_zero_iff.mp n.1.2⟩
    have hto : Tendsto toRatio (comap Subtype.val (comap Subtype.val atTop))
        (comap Subtype.val atTop) :=
      tendsto_comap_iff.mpr (tendsto_index_of_nonzero_subtype _)
    apply (this.comp hto).congr'
    filter_upwards [] with n
    dsimp only [toRatio, Function.comp_def]
    have hn₁ := norm_ne_zero_iff.mp n.1.2
    rw [Nat.succ_eq_add_one, ← Complex.norm_div (hw := hn₁.isUnit),
      regularizedHGFunCoeff_add_one_div_self hn₁,
      multiset_prod_div_multiset_prod_mul a b n.2
        (regularizedHGFunCoeff_ne_zero_lower hn₁)]
    simp only [h, div_self, one_mul]
  have := FormalMultilinearSeries.ofScalars_radius_eq_inv_of_tendsto (r := 1) ℂ _
    (by simp) h_ne.frequently hlim
  simpa

/-- If `a.card = b.card + 1`, then the hypergeometric series has convergence radius greater or equal
to `1`. -/
theorem radius_regularizedHGFunSeries_ge_one (h : a.card = b.card + 1) :
    1 ≤ (regularizedHGFunSeries a b).radius := by
  by_cases! h' : ∀ j ∈ a, ∀ k : ℕ, j ≠ -k
  · grind
  · obtain ⟨j, hj, k, h'⟩ := h'
    rw [radius_regularizedHGFunSeries_eq_top_of_finite hj h']
    simp

section ZeroZero

/-- The regularized hypergeometric series with `a = b = 0` is exponential series. -/
@[simp, grind =]
theorem regularizedHGFunSeries_zero_zero :
    regularizedHGFunSeries 0 0 = NormedSpace.expSeries ℂ ℂ := by
  ext n
  simp [regularizedHGFunCoeff, NormedSpace.expSeries]

/-- The regularized hypergeometric function `₀F₀` is the complex exponential. -/
@[simp, grind =]
theorem regularizedHGFun_zero_zero (z : ℂ)
    (hz : Summable (fun n ↦ regularizedHGFunSeries 0 0 n (fun _ ↦ z))
      (SummationFilter.conditional ℕ)) : regularizedHGFun 0 0 z hz = exp z := by
  unfold regularizedHGFun
  rw [regularizedHGFunSeries_zero_zero]
  have h := (NormedSpace.expSeries_hasSum_exp (𝕂 := ℂ) z).mono_left
    (SummationFilter.conditional ℕ).le_atTop
  simpa only [exp_eq_exp_ℂ] using HasSum.tsum_eq h

end ZeroZero

section Gaussian

/-- The regularized Gaussian hypergeometric function. -/
def regularizedGaussHGFunSeries (a b c : ℂ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  regularizedHGFunSeries {a, b} {c}

/-- The regularized Gaussian hypergeometric function, defined by its convergent ordered series. -/
def regularizedGaussHGFun (a b c z : ℂ)
    (hz : Summable (fun n ↦ regularizedGaussHGFunSeries a b c n (fun _ ↦ z))
      (SummationFilter.conditional ℕ)) : ℂ :=
  regularizedHGFun {a, b} {c} z hz

variable {a b c z : ℂ}

variable (a b c) in
theorem regularizedGaussHGFunSeries_symm :
    regularizedGaussHGFunSeries a b c = regularizedGaussHGFunSeries b a c := by
  unfold regularizedGaussHGFunSeries
  rw [Multiset.pair_comm]

theorem regularizedGaussHGFun_symm
    (hz : Summable (fun n ↦ regularizedGaussHGFunSeries a b c n (fun _ ↦ z))
      (SummationFilter.conditional ℕ)) :
    regularizedGaussHGFun a b c z hz = regularizedGaussHGFun b a c z
      (by simpa only [regularizedGaussHGFunSeries_symm a b c] using hz) := by
  unfold regularizedGaussHGFun regularizedHGFun
  rw [Multiset.pair_comm]

theorem coeff_regularizedGaussHGFunSeries :
    (a.regularizedGaussHGFunSeries b c).coeff n =
    (ascPochhammer ℂ n).eval a * (ascPochhammer ℂ n).eval b * reciprocalGamma (c + n) / n ! := by
  simp [regularizedGaussHGFunSeries, regularizedHGFunCoeff]

theorem reciprocalGamma_mul_ordinaryHypergeometricSeries_eq (hc : ∀ k : ℕ, c ≠ -k) {n : ℕ} :
    reciprocalGamma c * (ordinaryHypergeometricSeries ℂ a b c
      (fun n ↦ Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))
      (ordinaryHypergeometricSeries_pochhammer_ne_zero hc)).coeff n =
      (a.regularizedGaussHGFunSeries b c).coeff n := by
  have hcn : ∀ k : ℕ, c + n ≠ -k := by
    intro k hk
    apply hc (k + n)
    push_cast
    linear_combination hk
  have hG : Gamma c ≠ 0 := Gamma_ne_zero hc
  have hGn : Gamma (c + n) ≠ 0 := Gamma_ne_zero hcn
  have hGamma : (ascPochhammer ℂ n).eval c * Gamma c = Gamma (c + n) :=
    (div_eq_iff.mp (Gamma_add_nat_div_Gamma_eq c hc)).symm
  rw [coeff_regularizedGaussHGFunSeries, ordinaryHypergeometricSeries,
    FormalMultilinearSeries.coeff_ofScalars, ordinaryHypergeometricCoefficient,
    reciprocalGamma_eq_inv hc, reciprocalGamma_eq_inv hcn]
  simp only [← hGamma, mul_inv₀, div_eq_mul_inv₀]
  ring

theorem reciprocalGamma_smul_ordinaryHypergeometricSeries (hc : ∀ k : ℕ, c ≠ -k) :
    reciprocalGamma c • ordinaryHypergeometricSeries ℂ a b c
      (fun n ↦ Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))
      (ordinaryHypergeometricSeries_pochhammer_ne_zero hc) = regularizedGaussHGFunSeries a b c := by
  ext n
  simpa using reciprocalGamma_mul_ordinaryHypergeometricSeries_eq (a := a) (b := b) hc (n := n)

theorem summable_regularizedGaussHGFunSeries_of_ordinary (hc : ∀ k : ℕ, c ≠ -k)
    (hz : Summable (fun n ↦ ordinaryHypergeometricSeries ℂ a b c
      (fun n ↦ Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))
      (ordinaryHypergeometricSeries_pochhammer_ne_zero hc) n (fun _ ↦ z))
      (SummationFilter.conditional ℕ)) :
    Summable (fun n ↦ regularizedGaussHGFunSeries a b c n (fun _ ↦ z))
      (SummationFilter.conditional ℕ) := by
  apply (hz.mul_left (reciprocalGamma c)).congr
  intro n
  simpa [regularizedGaussHGFunSeries] using
    congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ ↦ p n (fun _ ↦ z))
    (reciprocalGamma_smul_ordinaryHypergeometricSeries (a := a) (b := b) hc)

theorem ordinaryHypergeometric_div_Gamma_eq (hc : ∀ k : ℕ, c ≠ -k)
    (hz : Summable (fun n ↦ ordinaryHypergeometricSeries ℂ a b c
      (fun n ↦ Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))
      (ordinaryHypergeometricSeries_pochhammer_ne_zero hc) n (fun _ ↦ z))
      (SummationFilter.conditional ℕ)) :
    Checked.div (ordinaryHypergeometric a b c
      (fun n ↦ Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))
      (ordinaryHypergeometricSeries_pochhammer_ne_zero hc) z hz)
      (Gamma c) (Gamma_ne_zero hc).isUnit = regularizedGaussHGFun a b c z
        (summable_regularizedGaussHGFunSeries_of_ordinary hc hz) := by
  rw [← (ordinaryHypergeometric_hasSum a b c _ _ z hz).tsum_eq]
  unfold regularizedGaussHGFun regularizedHGFun
  rw [div_eq_inv_mul₀, ← reciprocalGamma_eq_inv hc, ← tsum_mul_left]
  apply tsum_congr
  intro n
  simpa [regularizedGaussHGFunSeries] using
    congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ ↦ p n (fun _ ↦ z))
    (reciprocalGamma_smul_ordinaryHypergeometricSeries (a := a) (b := b) hc)

variable (b c) in
@[simp]
theorem radius_regularizedGaussHGFunSeries_eq_top_of_left (k : ℕ) :
    (regularizedGaussHGFunSeries (-k) b c).radius = ⊤ :=
  radius_regularizedHGFunSeries_eq_top_of_finite (j := -(k : ℂ)) (by simp) rfl

variable (a c) in
@[simp]
theorem radius_regularizedGaussHGFunSeries_eq_top_of_right (k : ℕ) :
    (regularizedGaussHGFunSeries a (-k) c).radius = ⊤ :=
  radius_regularizedHGFunSeries_eq_top_of_finite (j := -(k : ℂ)) (by simp) rfl

variable (c) in
@[grind =]
theorem radius_regularizedGaussHGFunSeries_eq_one (h : ∀ k : ℕ, a ≠ -k ∧ b ≠ -k) :
    (regularizedGaussHGFunSeries a b c).radius = 1 :=
  radius_regularizedHGFunSeries_eq_one rfl (by simp; grind)

variable (a b c) in
theorem radius_regularizedGaussHGFunSeries_ge_one :
    1 ≤ (regularizedGaussHGFunSeries a b c).radius :=
  radius_regularizedHGFunSeries_ge_one rfl

end Gaussian

end Complex
