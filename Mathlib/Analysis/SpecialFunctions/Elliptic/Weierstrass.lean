/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Module.ZLattice.Summable
public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Meromorphic.GermOrder
public import Mathlib.Analysis.Meromorphic.Section
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Tactic.NormNum.NatFactorial
public import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
public import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas

/-!

# Weierstrass `℘` functions

## Main definitions and results
- `PeriodPair.weierstrassP`: The Weierstrass `℘`-function associated to a pair of periods.
- `PeriodPair.hasSumLocallyUniformly_weierstrassP`:
  The summands of `℘` sums to `℘` locally uniformly.
- `PeriodPair.differentiableOn_weierstrassP`: `℘` is differentiable away from the lattice points.
- `PeriodPair.weierstrassP_add_coe`: The Weierstrass `℘`-function is periodic.
- `PeriodPair.weierstrassP_neg`: The Weierstrass `℘`-function is even.

- `PeriodPair.derivWeierstrassP`:
  The derivative of the Weierstrass `℘`-function associated to a pair of periods.
- `PeriodPair.hasSumLocallyUniformly_derivWeierstrassP`:
  The summands of `℘'` sums to `℘'` locally uniformly.
- `PeriodPair.differentiableOn_derivWeierstrassP`:
  `℘'` is differentiable away from the lattice points.
- `PeriodPair.derivWeierstrassP_add_coe`: `℘'` is periodic.
- `PeriodPair.derivWeierstrassP_neg`: `℘'` is odd.
- `PeriodPair.deriv_weierstrassP`: `deriv ℘ = ℘'` on the complement of the period lattice.
- `PeriodPair.analyticOnNhd_weierstrassP`: `℘` is analytic away from the lattice points.
- `PeriodPair.meromorphicWeierstrassP`: `℘` is meromorphic on the whole plane.
- `PeriodPair.order_weierstrassP`: `℘` has a pole of order 2 at each of the lattice points.
- `PeriodPair.order_derivWeierstrassP`: `℘'` has a pole of order 3 at each of the lattice points.
- `PeriodPair.derivWeierstrassP_sq` : `℘'(z)² = 4 ℘(z)³ - g₂ ℘(z) - g₃`

The complex-valued functions `℘[L]` and `℘'[L]` have the complement of the period lattice
as their domain. Their meromorphic sections include the lattice points as poles.

## tags

Weierstrass p-functions, Weierstrass p functions

-/

@[expose] public section

set_option linter.style.longFile 2000

open Module Filter TopologicalSpace
open scoped Topology Nat

noncomputable section

/-- A pair of `ℝ`-linearly independent complex numbers.
They span the period lattice in `lattice`,
and are the periods of the elliptic functions we shall construct. -/
structure PeriodPair : Type where
  /-- The first period in a `PeriodPair`. -/
  ω₁ : ℂ
  /-- The second period in a `PeriodPair`. -/
  ω₂ : ℂ
  indep : LinearIndependent ℝ ![ω₁, ω₂]

variable {M : Type*} [AddCommMonoid M] [TopologicalSpace M] (L : PeriodPair)

namespace PeriodPair

/-- The `ℝ`-basis of `ℂ` determined by a pair of periods. -/
protected def basis : Basis (Fin 2) ℝ ℂ :=
  basisOfLinearIndependentOfCardEqFinrank L.indep (by simp)

@[simp] lemma basis_zero : L.basis 0 = L.ω₁ := by simp [PeriodPair.basis]
@[simp] lemma basis_one : L.basis 1 = L.ω₂ := by simp [PeriodPair.basis]

/-- The lattice spanned by a pair of periods. -/
def lattice : Submodule ℤ ℂ := Submodule.span ℤ {L.ω₁, L.ω₂}

lemma mem_lattice {L : PeriodPair} {x : ℂ} :
    x ∈ L.lattice ↔ ∃ m n : ℤ, m * L.ω₁ + n * L.ω₂ = x := by
  simp only [lattice, Submodule.mem_span_pair, zsmul_eq_mul]

lemma ω₁_mem_lattice : L.ω₁ ∈ L.lattice := Submodule.subset_span (by simp)
lemma ω₂_mem_lattice : L.ω₂ ∈ L.lattice := Submodule.subset_span (by simp)

lemma mul_ω₁_add_mul_ω₂_mem_lattice {L : PeriodPair} {α β : ℚ} :
    α * L.ω₁ + β * L.ω₂ ∈ L.lattice ↔ α.den = 1 ∧ β.den = 1 := by
  refine ⟨fun H ↦ ?_, fun ⟨h₁, h₂⟩ ↦ ?_⟩
  · obtain ⟨m, n, e⟩ := mem_lattice.mp H
    have := LinearIndependent.pair_iff.mp L.indep (m - α) (n - β)
      (by simp; linear_combination e)
    simp only [sub_eq_zero] at this
    norm_cast at this
    aesop
  · lift α to ℤ using h₁
    lift β to ℤ using h₂
    simp only [Rat.cast_intCast, ← zsmul_eq_mul]
    exact add_mem (Submodule.smul_mem _ _ L.ω₁_mem_lattice)
      (Submodule.smul_mem _ _ L.ω₂_mem_lattice)

lemma ω₁_div_two_notMem_lattice : L.ω₁ / 2 ∉ L.lattice := by
  simpa [one_div₀, inv_mul_eq_div₀] using
    (L.mul_ω₁_add_mul_ω₂_mem_lattice (α := 1 / 2) (β := 0)).not.mpr (by norm_num)

lemma ω₂_div_two_notMem_lattice : L.ω₂ / 2 ∉ L.lattice := by
  simpa [one_div₀, inv_mul_eq_div₀] using
    (L.mul_ω₁_add_mul_ω₂_mem_lattice (α := 0) (β := 1 / 2)).not.mpr (by norm_num)

-- helper lemma to connect to the ZLattice API
lemma lattice_eq_span_range_basis :
    L.lattice = Submodule.span ℤ (Set.range L.basis) := by
  have : Finset.univ (α := Fin 2) = {0, 1} := rfl
  rw [lattice, ← Set.image_univ, ← Finset.coe_univ, this]
  simp

instance : DiscreteTopology L.lattice := L.lattice_eq_span_range_basis ▸ inferInstance

instance : IsZLattice ℝ L.lattice := by
  simp_rw [L.lattice_eq_span_range_basis]
  infer_instance

lemma isClosed_lattice : IsClosed (X := ℂ) L.lattice :=
  @AddSubgroup.isClosed_of_discreteTopology _ _ _ _ _ L.lattice.toAddSubgroup
    (inferInstanceAs (DiscreteTopology L.lattice))

lemma isClosed_of_subset_lattice {s : Set ℂ} (hs : s ⊆ L.lattice) : IsClosed s := by
  convert!
    L.isClosed_lattice.isClosedMap_subtype_val _ (isClosed_discrete (α := L.lattice) ((↑) ⁻¹' s))
  convert! Set.image_preimage_eq_inter_range.symm using 1
  simpa

lemma isOpen_compl_lattice_sdiff {s : Set ℂ} : IsOpen ((L.lattice : Set ℂ) \ s)ᶜ :=
  (L.isClosed_of_subset_lattice Set.sdiff_subset).isOpen_compl

@[simp]
lemma mem_lattice_imp_neg_eq_iff (l₀ z : ℂ) :
    (z ∈ L.lattice → -z = l₀) ↔ (z ∈ L.lattice → z = -l₀) := by
  simp only [neg_eq_iff_eq_neg]

lemma neg_notMem_lattice_sdiff (l₀ z : ℂ) :
    -z ∉ (L.lattice : Set ℂ) \ {l₀} ↔ z ∉ (L.lattice : Set ℂ) \ {-l₀} := by
  simpa only [Set.mem_sdiff, Set.mem_singleton_iff, SetLike.mem_coe, neg_mem_iff,
    not_and, Decidable.not_not] using L.mem_lattice_imp_neg_eq_iff l₀ z

@[simp]
lemma add_coe_mem_lattice_imp_eq_iff (l₀ z : ℂ) (l : L.lattice) :
    (z + l ∈ L.lattice → z + l = l₀) ↔ (z ∈ L.lattice → z = l₀ - l) := by
  have hmem : z + l ∈ L.lattice ↔ z ∈ L.lattice := by
    constructor
    · intro hz
      simpa only [add_sub_cancel_right] using sub_mem hz l.2
    · exact fun hz => add_mem hz l.2
  simp only [hmem, ← eq_sub_iff_add_eq]

lemma add_coe_notMem_lattice_sdiff (l₀ z : ℂ) (l : L.lattice) :
    z + l ∉ (L.lattice : Set ℂ) \ {l₀} ↔ z ∉ (L.lattice : Set ℂ) \ {l₀ - l} := by
  simpa only [Set.mem_sdiff, Set.mem_singleton_iff, SetLike.mem_coe, not_and, Decidable.not_not]
    using L.add_coe_mem_lattice_imp_eq_iff l₀ z l

@[deprecated (since := "2026-06-03")] alias isOpen_compl_lattice_diff := isOpen_compl_lattice_sdiff

open scoped Topology in
lemma compl_lattice_sdiff_singleton_mem_nhds (x : ℂ) : (↑L.lattice \ {x})ᶜ ∈ 𝓝 x :=
  L.isOpen_compl_lattice_sdiff.mem_nhds (by simp)

@[deprecated (since := "2026-06-03")]
alias compl_lattice_diff_singleton_mem_nhds := compl_lattice_sdiff_singleton_mem_nhds

instance : ProperSpace L.lattice := .of_isClosed L.isClosed_lattice

/-- The `ℤ`-basis of the lattice determined by a pair of periods. -/
def latticeBasis : Basis (Fin 2) ℤ L.lattice :=
  (Basis.span (v := ![L.ω₁, L.ω₂]) (L.indep.restrict_scalars' _)).map
    (.ofEq _ _ (by simp [lattice, Set.pair_comm L.ω₂ L.ω₁]))

@[simp] lemma latticeBasis_zero : L.latticeBasis 0 = L.ω₁ := by simp [latticeBasis]
@[simp] lemma latticeBasis_one : L.latticeBasis 1 = L.ω₂ := by simp [latticeBasis]

@[simp] lemma finrank_lattice : finrank ℤ L.lattice = 2 := finrank_eq_card_basis L.latticeBasis

/-- The equivalence from the lattice generated by a pair of periods to `ℤ × ℤ`. -/
def latticeEquivProd : L.lattice ≃ₗ[ℤ] ℤ × ℤ :=
  L.latticeBasis.repr ≪≫ₗ Finsupp.linearEquivFunOnFinite _ _ _ ≪≫ₗ .finTwoArrow ℤ ℤ

lemma latticeEquiv_symm_apply (x : ℤ × ℤ) :
    (L.latticeEquivProd.symm x).1 = x.1 * L.ω₁ + x.2 * L.ω₂ := by
  simp [latticeEquivProd, Finsupp.linearCombination]

-- The exceptional index is outside the tail where this comparison sequence is used.
private def latticeRpowMajorant (x : ℂ) : L.lattice → ℝ :=
  {l : L.lattice | (l : ℂ) ≠ x}.indicator (fun l ↦ ‖(l : ℂ) - x‖ ^ (-3 : ℝ))

private lemma latticeRpowMajorant_of_ne {x : ℂ} {l : L.lattice} (h : (l : ℂ) ≠ x) :
    L.latticeRpowMajorant x l = ‖(l : ℂ) - x‖ ^ (-3 : ℝ) :=
  Set.indicator_of_mem h _

private lemma latticeRpowMajorant_nonneg (x : ℂ) (l : L.lattice) :
    0 ≤ L.latticeRpowMajorant x l := by
  by_cases h : (l : ℂ) = x
  · exact le_of_eq (Set.indicator_of_notMem (show l ∉ {l : L.lattice | (l : ℂ) ≠ x}
      from not_not_intro h) _).symm
  · rw [L.latticeRpowMajorant_of_ne h]
    positivity

private lemma summable_latticeRpowMajorant (x : ℂ) : Summable (L.latticeRpowMajorant x) :=
  (summable_subtype_iff_indicator (s := {l : L.lattice | (l : ℂ) ≠ x})).mp
    (ZLattice.summable_norm_sub_rpow L.lattice (-3) (by norm_num) x)

lemma hasSumLocallyUniformly_aux {D : Type*} [TopologicalSpace D] (f : L.lattice → D → ℂ)
    (u : ℝ → L.lattice → ℝ) (hu : ∀ r > 0, Summable (u r))
    (coord : D → ℂ := by exact id) (hcoord : Continuous coord := by fun_prop)
    (hf : ∀ r > 0, ∀ᶠ R in atTop, ∀ x, ‖coord x‖ < r →
      ∀ l : L.lattice, ‖l.1‖ = R → ‖f l x‖ ≤ u r l) :
    HasSumLocallyUniformly f (∑' j, f j ·) := by
  rw [hasSumLocallyUniformly_iff_tendstoLocallyUniformly, tendstoLocallyUniformly_iff_filter]
  intro x
  obtain ⟨r, hr, hr'⟩ : ∃ r, 0 < r ∧ 𝓝 x ≤ 𝓟 {y : D | ‖coord y‖ < r} :=
    ⟨‖coord x‖ + 1, by positivity, Filter.le_principal_iff.mpr
      ((isOpen_lt (continuous_norm.comp hcoord) continuous_const).mem_nhds (by simp))⟩
  refine .mono_right ?_ hr'
  rw [← tendstoUniformlyOn_iff_tendstoUniformlyOnFilter]
  refine tendstoUniformlyOn_tsum_of_cofinite_eventually (hu r hr) ?_
  obtain ⟨R, hR⟩ := eventually_atTop.mp (hf r hr)
  refine (isCompact_iff_finite.mp (isCompact_closedBall (0 : L.lattice) R)).subset ?_
  intros l hl
  obtain ⟨s, hs, hs'⟩ : ∃ x, ‖coord x‖ < r ∧ u r l < ‖f l x‖ := by simpa using hl
  simp only [Metric.mem_closedBall, dist_zero_right]
  contrapose! hs'
  exact hR _ hs'.le _ hs _ rfl

-- Only the asymptotics matter and `10` is just a convenient constant to pick.
lemma weierstrassP_bound (r : ℝ) (hr : 0 < r) (s : ℂ) (hs : ‖s‖ < r) (l : ℂ)
    (h : 2 * r ≤ ‖l‖)
    (hl : l ≠ 0 := by intro he; have : ‖l‖ = 0 := by simp [he]; linarith)
    (hsl : s - l ≠ 0 := by
      intro he
      have he' : s = l := sub_eq_zero.mp he
      subst s
      linarith) :
    ‖1 / (s - l) ^ 2 - 1 / l ^ 2‖ ≤ 10 * r * ‖l‖ ^ (-3 : ℝ) := by
  have : s ≠ l := by rintro rfl; linarith
  have hlpos : 0 < ‖l‖ := by linarith
  calc
    _ = ‖(l ^ 2 - (s - l) ^ 2) / ((s - l) ^ 2 * l ^ 2)‖ := by
      rw [div_sub_div, one_mul, mul_one]
    _ = ‖l ^ 2 - (s - l) ^ 2‖ / (‖s - l‖ ^ 2 * ‖l‖ ^ 2) := by simp
    _ ≤ ‖l ^ 2 - (s - l) ^ 2‖ / ((‖l‖ / 2) ^ 2 * ‖l‖ ^ 2) := by
      gcongr
      rw [norm_sub_rev]
      exact .trans (by linarith) (norm_sub_norm_le l s)
    _ = ‖s * (2 * l - s)‖ / (‖l‖ ^ 4 / 4) := by
      congr 1
      · rw [sq_sub_sq]; simp [← sub_add, two_mul, sub_add_eq_add_sub]
      · ring
    _ = (‖s‖ * ‖2 * l - s‖) / (‖l‖ ^ 4 / 4) := by simp
    _ = (4 * ‖s‖ * ‖2 * l - s‖) / ‖l‖ ^ 4 := by field
    _ ≤ (4 * r * ((5 / 2) * ‖l‖)) / ‖l‖ ^ 4 := by
      gcongr (4 * ?_ * ?_) / ‖l‖ ^ 4
      refine (norm_sub_le _ _).trans ?_
      simp only [Complex.norm_mul, Complex.norm_ofNat]
      linarith
    _ = 10 * r / ‖l‖ ^ 3 := by field_simp; ring
    _ = _ := by
      have hp := Real.rpow_neg hlpos.le (3 : ℝ)
        (hxy := (Real.rpow_pos_of_pos hlpos _).ne'.isUnit)
      simp only [hp, Real.rpow_ofNat, div_eq_mul_inv₀]

section weierstrassPExcept

/-- The coefficient of a lattice summand in the expansion at an admissible point, with the
`l₀`-th summand omitted. The zero-lattice term has no renormalizing constant. -/
def weierstrassPExceptSummand (l₀ : ℂ) (x : {x : ℂ // x ∉ (L.lattice : Set ℂ) \ {l₀}})
    (i : ℕ) (l : L.lattice) : ℂ :=
  if hl : l.1 = l₀ then 0 else
    have hlx : l.1 - x.1 ≠ 0 := by
      intro h
      apply x.2
      have hx : x.1 = l.1 := (sub_eq_zero.mp h).symm
      exact ⟨hx.symm ▸ l.2, by simpa only [Set.mem_singleton_iff, hx] using hl⟩
    (i + 1) * (l.1 - x.1) ^ (- ↑(i + 2) : ℤ) -
      if i = 0 then (if hl₀ : l.1 = 0 then 0 else l.1 ^ (-2 : ℤ)) else 0

/-- The Weierstrass `℘` function with the `l₀`-term missing.
This is mainly a tool for calculations where one would want to omit a diverging term.
This has the notation `℘[L - l₀]` in the namespace `PeriodPair`. -/
def weierstrassPExcept (l₀ : ℂ) (z : {z : ℂ // z ∉ (L.lattice : Set ℂ) \ {l₀}}) : ℂ :=
  ∑' l : L.lattice, L.weierstrassPExceptSummand l₀ z 0 l

@[inherit_doc weierstrassPExcept]
scoped notation3 "℘[" L:max " - " l₀ "]" => weierstrassPExcept L l₀

lemma hasSumLocallyUniformly_weierstrassPExcept (l₀ : ℂ) :
    HasSumLocallyUniformly
      (fun (l : L.lattice) (z : {z : ℂ // z ∉ (L.lattice : Set ℂ) \ {l₀}}) ↦
        L.weierstrassPExceptSummand l₀ z 0 l)
      ℘[L - l₀] := by
  refine L.hasSumLocallyUniformly_aux (u := fun r l ↦ (10 * r) * L.latticeRpowMajorant 0 l)
    (coord := Subtype.val) (hcoord := continuous_subtype_val) _
    (fun r _ ↦ (L.summable_latticeRpowMajorant 0).mul_left (10 * r)) fun r hr ↦
    Filter.eventually_atTop.mpr ⟨2 * r, ?_⟩
  rintro _ h s hs l rfl
  have hl₀ : (l : ℂ) ≠ 0 := by
    intro he
    have : ‖(l : ℂ)‖ = 0 := by simp [he]
    linarith
  rw [L.latticeRpowMajorant_of_ne hl₀, sub_zero]
  by_cases hll₀ : (l : ℂ) = l₀
  · simp only [weierstrassPExceptSummand, dite_eq_left hll₀, norm_zero]
    positivity
  · have hls : (l : ℂ) - s.1 ≠ 0 := by
      intro he
      apply s.2
      have hs' : s.1 = (l : ℂ) := (sub_eq_zero.mp he).symm
      exact ⟨hs'.symm ▸ l.2, by simpa only [Set.mem_singleton_iff, hs'] using hll₀⟩
    have hsl : s.1 - (l : ℂ) ≠ 0 := sub_ne_zero.mpr (sub_ne_zero.mp hls).symm
    simpa [weierstrassPExceptSummand, hll₀, hl₀, zpow_neg₀ hls, zpow_neg₀ hl₀,
      sub_sq_comm, one_div₀, Submodule.norm_coe] using
      weierstrassP_bound r hr s.1 hs l h hl₀ hsl

lemma hasSum_weierstrassPExcept (l₀ : ℂ) (z : {z : ℂ // z ∉ (L.lattice : Set ℂ) \ {l₀}}) :
    HasSum (fun l : L.lattice ↦ L.weierstrassPExceptSummand l₀ z 0 l)
      (℘[L - l₀] z) :=
  (L.hasSumLocallyUniformly_weierstrassPExcept l₀).hasSum

lemma weierstrassPExcept_neg (l₀ : ℂ) (z : {z : ℂ // z ∉ (L.lattice : Set ℂ) \ {-l₀}}) :
    ℘[L - l₀] ⟨-z.1, (L.neg_notMem_lattice_sdiff l₀ z.1).mpr z.2⟩ = ℘[L - -l₀] z := by
  simp only [weierstrassPExcept]
  rw [← (Equiv.neg L.lattice).tsum_eq (L.weierstrassPExceptSummand l₀
    ⟨-z.1, (L.neg_notMem_lattice_sdiff l₀ z.1).mpr z.2⟩ 0)]
  apply tsum_congr
  intro l
  simp only [weierstrassPExceptSummand, Equiv.neg_apply, NegMemClass.coe_neg]
  by_cases hl : (l : ℂ) = -l₀
  · simp [hl]
  · have hl' : -(l : ℂ) ≠ l₀ := fun h ↦ hl (by simpa only [neg_neg] using congrArg Neg.neg h)
    simp only [dite_eq_right hl, dite_eq_right hl', Nat.cast_zero, zero_add, one_mul,
      ite_true]
    have hlz : (l : ℂ) - z.1 ≠ 0 := by
      intro he
      apply z.2
      have hz : z.1 = (l : ℂ) := (sub_eq_zero.mp he).symm
      exact ⟨hz.symm ▸ l.2, by simpa only [Set.mem_singleton_iff, hz] using hl⟩
    have hneg : -(l : ℂ) - (-z.1) ≠ 0 := by
      simpa only [neg_sub, neg_sub_neg] using neg_ne_zero.mpr hlz
    congr 1
    · rw [zpow_neg₀ hneg, zpow_neg₀ hlz]
      apply inv_inj₀.mpr
      change (-(l : ℂ) - (-z.1)) ^ (2 : ℕ) = ((l : ℂ) - z.1) ^ (2 : ℕ)
      rw [show -(l : ℂ) - (-z.1) = -((l : ℂ) - z.1) by abel, neg_sq]
    · by_cases hzero : (l : ℂ) = 0
      · simp [hzero]
      · simp only [dite_eq_right hzero, dite_eq_right (neg_ne_zero.mpr hzero)]
        rw [zpow_neg₀ (neg_ne_zero.mpr hzero), zpow_neg₀ hzero]
        exact inv_inj₀.mpr (neg_sq _)

@[simp] lemma weierstrassPExcept_zero :
    ℘[L - 0] ⟨0, by simp⟩ = 0 := by
  rw [weierstrassPExcept]
  trans ∑' _ : L.lattice, (0 : ℂ)
  · apply tsum_congr
    intro l
    by_cases hl : (l : ℂ) = 0 <;> simp [weierstrassPExceptSummand, hl]
  · exact tsum_zero

end weierstrassPExcept

section weierstrassP

/-- A coefficient of a lattice summand in the expansion at a non-lattice point.
The renormalizing constant is present only in degree zero and only at a nonzero lattice point. -/
def weierstrassPSummand (x : {x : ℂ // x ∉ L.lattice}) (i : ℕ) (l : L.lattice) : ℂ :=
  have hlx : l.1 - x.1 ≠ 0 := by
    intro h
    exact x.2 (sub_eq_zero.mp h ▸ l.2)
  (i + 1) * (l.1 - x.1) ^ (- ↑(i + 2) : ℤ) -
    if i = 0 then (if hl₀ : l.1 = 0 then 0 else l.1 ^ (-2 : ℤ)) else 0

lemma weierstrassPExceptSummand_of_notMem (l₀ : ℂ) (hl₀ : l₀ ∉ L.lattice)
    (x : {x : ℂ // x ∉ L.lattice}) (i : ℕ) (l : L.lattice) :
    L.weierstrassPExceptSummand l₀ ⟨x.1, fun h => x.2 h.1⟩ i l =
      L.weierstrassPSummand x i l := by
  have hl : (l : ℂ) ≠ l₀ := fun h => hl₀ (h ▸ l.2)
  simp only [weierstrassPExceptSummand, weierstrassPSummand, dite_eq_right hl]

/-- The Weierstrass `℘` function. This has the notation `℘[L]` in the namespace `PeriodPair`. -/
def weierstrassP (z : {z : ℂ // z ∉ L.lattice}) : ℂ :=
  have hz : z.1 ≠ 0 := by
    intro h
    exact z.2 (h.symm ▸ L.lattice.zero_mem)
  1 / z.1 ^ 2 + ∑' l : {l : L.lattice // l.1 ≠ 0},
    have hzl : z.1 - l.1.1 ≠ 0 := by
      intro h
      exact z.2 ((sub_eq_zero.mp h).symm ▸ l.1.2)
    1 / (z.1 - l.1.1) ^ 2 - 1 / l.1.1 ^ 2

@[inherit_doc weierstrassP] scoped notation3 "℘[" L "]" => weierstrassP L

/-- The usual initial term `1 / z²` and sum over nonzero lattice points equal the sum of
the degree-zero lattice coefficients, including the genuine initial term at the zero index. -/
lemma weierstrassP_eq_tsum (z : {z : ℂ // z ∉ L.lattice}) :
    ℘[L] z = ∑' l : L.lattice, L.weierstrassPSummand z 0 l := by
  have hz : z.1 ≠ 0 := by
    intro h
    exact z.2 (h.symm ▸ L.lattice.zero_mem)
  have hs : Summable (fun l : L.lattice => L.weierstrassPSummand z 0 l) := by
    simpa only [L.weierstrassPExceptSummand_of_notMem
      (L.ω₁ / 2) L.ω₁_div_two_notMem_lattice z 0] using
      (L.hasSum_weierstrassPExcept (L.ω₁ / 2) ⟨z.1, fun h => z.2 h.1⟩).summable
  have hzero : L.weierstrassPSummand z 0 0 = 1 / z.1 ^ 2 := by
    simp [weierstrassPSummand, zpow_neg₀ (neg_ne_zero.mpr hz), one_div₀]
  have hindex : (∑' l : {l : L.lattice // (l : ℂ) ≠ 0}, L.weierstrassPSummand z 0 l.1) =
      ∑' l : L.lattice, if l = 0 then 0 else L.weierstrassPSummand z 0 l := by
    let f (l : L.lattice) : ℂ := if l = 0 then 0 else L.weierstrassPSummand z 0 l
    have hsupport : Function.support f ⊆ {l : L.lattice | (l : ℂ) ≠ 0} := by
      intro l h he
      have hl : l = 0 := Subtype.ext (by simpa using he)
      exact h (by simp only [f, ite_eq_left hl])
    calc
      _ = ∑' l : {l : L.lattice // (l : ℂ) ≠ 0}, f l.1 := by
        apply tsum_congr
        intro l
        have hl : l.1 ≠ 0 := fun he ↦ l.2 (congrArg Subtype.val he)
        simp only [f, ite_eq_right hl]
      _ = _ := tsum_subtype_eq_of_support_subset hsupport
  symm
  calc
    (∑' l : L.lattice, L.weierstrassPSummand z 0 l) =
        L.weierstrassPSummand z 0 0 +
          ∑' l : L.lattice, if l = 0 then 0 else L.weierstrassPSummand z 0 l :=
      hs.tsum_eq_add_tsum_ite 0
    _ = 1 / z.1 ^ 2 +
        ∑' l : {l : L.lattice // (l : ℂ) ≠ 0}, L.weierstrassPSummand z 0 l.1 := by
      rw [hzero, ← hindex]
    _ = ℘[L] z := by
      rw [weierstrassP]
      congr 1
      apply tsum_congr
      intro l
      have hlz : (l.1 : ℂ) - z.1 ≠ 0 := by
        intro h
        exact z.2 (sub_eq_zero.mp h ▸ l.1.2)
      simp only [weierstrassPSummand, Nat.cast_zero, zero_add, one_mul, ite_true,
        dite_eq_right l.2, zpow_neg₀ hlz, zpow_neg₀ l.2, zpow_natCast₀, one_div₀]
      congr 1
      exact inv_inj₀.mpr (sub_sq_comm _ _)

lemma weierstrassPExcept_add (l₀ : L.lattice) (z : {z : ℂ // z ∉ L.lattice}) :
    ℘[L - l₀] ⟨z.1, fun h => z.2 h.1⟩ + L.weierstrassPSummand z 0 l₀ = ℘[L] z := by
  trans ℘[L - l₀] ⟨z.1, fun h => z.2 h.1⟩ +
    ∑' i : L.lattice, if i = l₀ then L.weierstrassPSummand z 0 l₀ else 0
  · simp
  rw [weierstrassPExcept, weierstrassP_eq_tsum, ← Summable.tsum_add]
  · apply tsum_congr
    intro l
    by_cases hl : l = l₀
    · simp [hl, weierstrassPExceptSummand]
    · have hll₀ : (l : ℂ) ≠ (l₀ : ℂ) := fun he => hl (Subtype.ext he)
      simp only [weierstrassPExceptSummand, weierstrassPSummand, dite_eq_right hll₀,
        ite_eq_right hl, add_zero]
  · exact ⟨_, L.hasSum_weierstrassPExcept _ _⟩
  · exact summable_of_hasFiniteSupport ((Set.finite_singleton l₀).subset (by simp))

lemma weierstrassPExcept_def (l₀ : L.lattice) (z : {z : ℂ // z ∉ L.lattice}) :
    ℘[L - l₀] ⟨z.1, fun h => z.2 h.1⟩ = ℘[L] z - L.weierstrassPSummand z 0 l₀ := by
  rw [← L.weierstrassPExcept_add l₀ z]
  abel

lemma weierstrassPExcept_of_notMem (l₀ : ℂ) (hl : l₀ ∉ L.lattice)
    (z : {z : ℂ // z ∉ L.lattice}) :
    ℘[L - l₀] ⟨z.1, fun h => z.2 h.1⟩ = ℘[L] z := by
  rw [weierstrassPExcept, weierstrassP_eq_tsum]
  apply tsum_congr
  exact L.weierstrassPExceptSummand_of_notMem l₀ hl z 0

lemma hasSumLocallyUniformly_weierstrassP :
    HasSumLocallyUniformly (fun l z ↦ L.weierstrassPSummand z 0 l) ℘[L] := by
  let lift (z : {z : ℂ // z ∉ L.lattice}) : {z : ℂ // z ∉ (L.lattice : Set ℂ) \ {L.ω₁ / 2}} :=
    ⟨z.1, fun h ↦ z.2 h.1⟩
  have hlift : Continuous lift := continuous_subtype_val.subtype_mk _
  have h := (L.hasSumLocallyUniformly_weierstrassPExcept (L.ω₁ / 2)).comp lift hlift
  simpa only [HasSumLocallyUniformly, lift, Function.comp_def,
    L.weierstrassPExceptSummand_of_notMem _ L.ω₁_div_two_notMem_lattice,
    L.weierstrassPExcept_of_notMem _ L.ω₁_div_two_notMem_lattice] using h

lemma hasSum_weierstrassP (z : {z : ℂ // z ∉ L.lattice}) :
    HasSum (fun l ↦ L.weierstrassPSummand z 0 l) (℘[L] z) :=
  L.hasSumLocallyUniformly_weierstrassP.hasSum

@[simp]
lemma weierstrassP_neg (z : {z : ℂ // z ∉ L.lattice}) :
    ℘[L] ⟨-z.1, fun h ↦ z.2 (neg_mem_iff.mp h)⟩ = ℘[L] z := by
  let w : {z : ℂ // z ∉ L.lattice} := ⟨-z.1, fun h ↦ z.2 (neg_mem_iff.mp h)⟩
  let l : ℂ := L.ω₁ / 2
  have hl : l ∉ L.lattice := L.ω₁_div_two_notMem_lattice
  have hn : -l ∉ L.lattice := fun h ↦ hl (neg_mem_iff.mp h)
  let z' : {x : ℂ // x ∉ (L.lattice : Set ℂ) \ {-l}} := ⟨z.1, fun h ↦ z.2 h.1⟩
  exact (L.weierstrassPExcept_of_notMem l hl w).symm.trans
    ((L.weierstrassPExcept_neg l z').trans (L.weierstrassPExcept_of_notMem (-l) hn z))

end weierstrassP

section derivWeierstrassPExcept

/-- The derivative of Weierstrass `℘` function with the `l₀`-term missing.
This is mainly a tool for calculations where one would want to omit a diverging term.
This has the notation `℘'[L - l₀]` in the namespace `PeriodPair`. -/
def derivWeierstrassPExcept (l₀ : ℂ) (z : {z : ℂ // z ∉ (L.lattice : Set ℂ) \ {l₀}}) : ℂ :=
  ∑' l : L.lattice, L.weierstrassPExceptSummand l₀ z 1 l

@[inherit_doc derivWeierstrassPExcept]
scoped notation3 "℘'[" L:max " - " l₀ "]" => derivWeierstrassPExcept L l₀

lemma hasSumLocallyUniformly_derivWeierstrassPExcept (l₀ : ℂ) :
    HasSumLocallyUniformly
      (fun (l : L.lattice) (z : {z : ℂ // z ∉ (L.lattice : Set ℂ) \ {l₀}}) ↦
        L.weierstrassPExceptSummand l₀ z 1 l)
      ℘'[L - l₀] := by
  refine L.hasSumLocallyUniformly_aux (u := fun _ l ↦ 16 * L.latticeRpowMajorant 0 l)
    (coord := Subtype.val) (hcoord := continuous_subtype_val) _
    (fun _ _ ↦ (L.summable_latticeRpowMajorant 0).mul_left 16) fun r hr ↦
    Filter.eventually_atTop.mpr ⟨2 * r, ?_⟩
  rintro _ h s hs l rfl
  have hl₀ : (l : ℂ) ≠ 0 := by
    intro he
    have : ‖(l : ℂ)‖ = 0 := by simp [he]
    linarith
  rw [L.latticeRpowMajorant_of_ne hl₀, sub_zero]
  by_cases hll₀ : (l : ℂ) = l₀
  · simp only [weierstrassPExceptSummand, dite_eq_left hll₀, norm_zero]
    exact mul_nonneg (by norm_num) (Real.rpow_nonneg (norm_nonneg _) _)
  have hls : (l : ℂ) - s.1 ≠ 0 := by
    intro he
    apply s.2
    have hs' : s.1 = (l : ℂ) := (sub_eq_zero.mp he).symm
    exact ⟨hs'.symm ▸ l.2, by simpa only [Set.mem_singleton_iff, hs'] using hll₀⟩
  have hlpos : 0 < ‖l.1‖ := norm_pos_iff.mpr hl₀
  have hlspos : 0 < ‖l.1 - s.1‖ := norm_pos_iff.mpr hls
  have hbound : ‖l.1‖ ≤ 2 * ‖l.1 - s.1‖ := by
    linarith [norm_sub_norm_le l.1 s.1]
  have heq : L.weierstrassPExceptSummand l₀ s 1 l = (2 : ℂ) / (l.1 - s.1) ^ 3 := by
    simp [weierstrassPExceptSummand, hll₀, zpow_neg₀ hls, div_eq_mul_inv₀, one_add_one_eq_two]
  calc
    _ = (2 : ℝ) / ‖l.1 - s.1‖ ^ 3 := by
      rw [heq]
      calc
        _ = ‖(2 : ℂ)‖ / ‖(l.1 - s.1) ^ 3‖ := norm_div _ _
        _ = _ := by
          simp only [Complex.norm_ofNat, div_eq_mul_inv₀]
          congr 1
          exact inv_inj₀.mpr (norm_pow _ _)
    _ ≤ 16 / ‖l.1‖ ^ 3 := by
      apply (div_le_div_iff₀ (pow_pos hlspos 3) (pow_pos hlpos 3)).mpr
      have hp := pow_le_pow_left₀ (norm_nonneg l.1) hbound 3
      nlinarith only [hp]
    _ = _ := by
      have hp := Real.rpow_neg hlpos.le (3 : ℝ)
        (hxy := (Real.rpow_pos_of_pos hlpos _).ne'.isUnit)
      simp only [hp, Real.rpow_ofNat, div_eq_mul_inv₀]

lemma hasSum_derivWeierstrassPExcept (l₀ : ℂ) (z : {z : ℂ // z ∉ (L.lattice : Set ℂ) \ {l₀}}) :
    HasSum (fun l : L.lattice ↦ L.weierstrassPExceptSummand l₀ z 1 l) (℘'[L - l₀] z) :=
  (L.hasSumLocallyUniformly_derivWeierstrassPExcept l₀).hasSum

lemma derivWeierstrassPExcept_neg (l₀ : ℂ) (z : {z : ℂ // z ∉ (L.lattice : Set ℂ) \ {-l₀}}) :
    ℘'[L - l₀] ⟨-z.1, (L.neg_notMem_lattice_sdiff l₀ z.1).mpr z.2⟩ = -℘'[L - -l₀] z := by
  simp only [derivWeierstrassPExcept, ← tsum_neg]
  rw [← (Equiv.neg L.lattice).tsum_eq (L.weierstrassPExceptSummand l₀
    ⟨-z.1, (L.neg_notMem_lattice_sdiff l₀ z.1).mpr z.2⟩ 1)]
  apply tsum_congr
  intro l
  simp only [weierstrassPExceptSummand, Equiv.neg_apply, NegMemClass.coe_neg]
  by_cases hl : (l : ℂ) = -l₀
  · simp [hl]
  · have hl' : -(l : ℂ) ≠ l₀ := fun h ↦ hl (by simpa only [neg_neg] using congrArg Neg.neg h)
    have hlz : (l : ℂ) - z.1 ≠ 0 := by
      intro he
      apply z.2
      have hz : z.1 = (l : ℂ) := (sub_eq_zero.mp he).symm
      exact ⟨hz.symm ▸ l.2, by simpa only [Set.mem_singleton_iff, hz] using hl⟩
    have hneg : -(l : ℂ) - (-z.1) ≠ 0 := by
      simpa only [neg_sub, neg_sub_neg] using neg_ne_zero.mpr hlz
    simp only [dite_eq_right hl, dite_eq_right hl', Nat.cast_one, Nat.reduceAdd, one_add_one_eq_two,
      Nat.one_ne_zero, ite_false, sub_zero, zpow_neg₀ hneg, zpow_neg₀ hlz, zpow_natCast₀]
    have hcube : (-(l : ℂ) - (-z.1)) ^ 3 = -(((l : ℂ) - z.1) ^ 3) := by
      rw [show -(l : ℂ) - (-z.1) = -((l : ℂ) - z.1) by abel]
      exact (show Odd 3 by decide).neg_pow _
    have hunit : IsUnit (-(((l : ℂ) - z.1) ^ 3)) :=
      (neg_ne_zero.mpr (pow_ne_zero 3 hlz)).isUnit
    rw [← mul_neg, ← inv_neg₀ (ha := hunit)]
    congr 1
    exact inv_inj₀.mpr hcube

@[simp]
lemma derivWeierstrassPExcept_zero_zero : ℘'[L - (0 : ℂ)] ⟨0, by simp⟩ = 0 := by
  let f (x : ℂ) := ℘'[L - x] ⟨x, by simp⟩
  have h : f 0 = -f (-(0 : ℂ)) := calc
    f 0 = ℘'[L - (0 : ℂ)] ⟨-(-(0 : ℂ)), by simp⟩ :=
      congrArg (derivWeierstrassPExcept L 0) (Subtype.ext (neg_neg _).symm)
    _ = _ := L.derivWeierstrassPExcept_neg (0 : ℂ) ⟨-(0 : ℂ), by simp⟩
  rw [neg_zero] at h
  exact CharZero.eq_neg_self_iff.mp h

lemma derivWeierstrassPExcept_add_coe (l₀ : ℂ) (l : L.lattice)
    (z : {z : ℂ // z ∉ (L.lattice : Set ℂ) \ {l₀ - l}}) :
    ℘'[L - l₀] ⟨z.1 + l, (L.add_coe_notMem_lattice_sdiff l₀ z.1 l).mpr z.2⟩ =
      ℘'[L - (l₀ - l)] z := by
  simp only [derivWeierstrassPExcept]
  rw [← (Equiv.addRight l).tsum_eq]
  apply tsum_congr
  intro w
  have heq : (((Equiv.addRight l) w : L.lattice) : ℂ) - (z.1 + l) = w.1 - z.1 := by
    simp only [Equiv.coe_addRight, Submodule.coe_add, add_sub_add_right_eq_sub]
  have hindex : (((Equiv.addRight l) w : L.lattice) : ℂ) = l₀ ↔ (w : ℂ) = l₀ - l := by
    simp only [Equiv.coe_addRight, Submodule.coe_add, eq_sub_iff_add_eq]
  unfold weierstrassPExceptSummand
  by_cases hw : (w : ℂ) = l₀ - l
  · simp only [dite_eq_left hw, dite_eq_left (hindex.mpr hw)]
  · have hn : (w : ℂ) - z.1 ≠ 0 := by
      intro h
      apply z.2
      have hz : (w : ℂ) = z.1 := sub_eq_zero.mp h
      exact ⟨hz ▸ w.2, by simpa only [Set.mem_singleton_iff, ← hz] using hw⟩
    have hn' : (((Equiv.addRight l) w : L.lattice) : ℂ) - (z.1 + l) ≠ 0 := heq ▸ hn
    simp only [dite_eq_right hw, dite_eq_right (hindex.not.mpr hw), Nat.one_ne_zero, ite_false,
      sub_zero, zpow_neg₀ hn, zpow_neg₀ hn', zpow_natCast₀]
    congr 1
    exact inv_inj₀.mpr (congrArg (fun a : ℂ ↦ a ^ 3) heq)

end derivWeierstrassPExcept

section derivWeierstrassP

/-- The derivative of Weierstrass `℘` function on the complement of the period lattice. -/
def derivWeierstrassP (z : {z : ℂ // z ∉ L.lattice}) : ℂ :=
  ∑' l : L.lattice, L.weierstrassPSummand z 1 l

@[inherit_doc derivWeierstrassP] scoped notation3 "℘'[" L "]" => derivWeierstrassP L

lemma derivWeierstrassPExcept_of_notMem (l₀ : ℂ) (hl : l₀ ∉ L.lattice)
    (z : {z : ℂ // z ∉ L.lattice}) :
    ℘'[L - l₀] ⟨z.1, fun h ↦ z.2 h.1⟩ = ℘'[L] z := by
  rw [derivWeierstrassPExcept, derivWeierstrassP]
  exact tsum_congr (L.weierstrassPExceptSummand_of_notMem l₀ hl z 1)

lemma hasSumLocallyUniformly_derivWeierstrassP :
    HasSumLocallyUniformly (fun l z ↦ L.weierstrassPSummand z 1 l) ℘'[L] := by
  let lift (z : {z : ℂ // z ∉ L.lattice}) : {z : ℂ // z ∉ (L.lattice : Set ℂ) \ {L.ω₁ / 2}} :=
    ⟨z.1, fun h ↦ z.2 h.1⟩
  have hlift : Continuous lift := continuous_subtype_val.subtype_mk _
  have h := (L.hasSumLocallyUniformly_derivWeierstrassPExcept (L.ω₁ / 2)).comp lift hlift
  simpa only [HasSumLocallyUniformly, lift, Function.comp_def,
    L.weierstrassPExceptSummand_of_notMem _ L.ω₁_div_two_notMem_lattice,
    L.derivWeierstrassPExcept_of_notMem _ L.ω₁_div_two_notMem_lattice] using h

lemma hasSum_derivWeierstrassP (z : {z : ℂ // z ∉ L.lattice}) :
    HasSum (fun l ↦ L.weierstrassPSummand z 1 l) (℘'[L] z) :=
  L.hasSumLocallyUniformly_derivWeierstrassP.hasSum

lemma derivWeierstrassPExcept_sub (l₀ : L.lattice) (z : {z : ℂ // z ∉ L.lattice}) :
    ℘'[L - l₀] ⟨z.1, fun h ↦ z.2 h.1⟩ + L.weierstrassPSummand z 1 l₀ = ℘'[L] z := by
  trans ℘'[L - l₀] ⟨z.1, fun h ↦ z.2 h.1⟩ +
    ∑' i : L.lattice, if i = l₀ then L.weierstrassPSummand z 1 l₀ else 0
  · simp
  rw [derivWeierstrassPExcept, derivWeierstrassP, ← Summable.tsum_add]
  · apply tsum_congr
    intro l
    by_cases hl : l = l₀
    · simp [hl, weierstrassPExceptSummand]
    · have hll₀ : (l : ℂ) ≠ (l₀ : ℂ) := fun he ↦ hl (Subtype.ext he)
      simp only [weierstrassPExceptSummand, weierstrassPSummand, dite_eq_right hll₀,
        ite_eq_right hl, add_zero]
  · exact (L.hasSum_derivWeierstrassPExcept _ _).summable
  · exact summable_of_hasFiniteSupport ((Set.finite_singleton l₀).subset (by simp))

lemma derivWeierstrassPExcept_def (l₀ : L.lattice) (z : {z : ℂ // z ∉ L.lattice}) :
    ℘'[L - l₀] ⟨z.1, fun h ↦ z.2 h.1⟩ = ℘'[L] z - L.weierstrassPSummand z 1 l₀ := by
  rw [← L.derivWeierstrassPExcept_sub l₀ z]
  abel

@[simp]
lemma derivWeierstrassP_neg (z : {z : ℂ // z ∉ L.lattice}) :
    ℘'[L] ⟨-z.1, fun h ↦ z.2 (neg_mem_iff.mp h)⟩ = -℘'[L] z := by
  let w : {z : ℂ // z ∉ L.lattice} := ⟨-z.1, fun h ↦ z.2 (neg_mem_iff.mp h)⟩
  let l : ℂ := L.ω₁ / 2
  have hl : l ∉ L.lattice := L.ω₁_div_two_notMem_lattice
  have hn : -l ∉ L.lattice := fun h ↦ hl (neg_mem_iff.mp h)
  let z' : {x : ℂ // x ∉ (L.lattice : Set ℂ) \ {-l}} := ⟨z.1, fun h ↦ z.2 h.1⟩
  exact (L.derivWeierstrassPExcept_of_notMem l hl w).symm.trans
    ((L.derivWeierstrassPExcept_neg l z').trans
      (congrArg Neg.neg (L.derivWeierstrassPExcept_of_notMem (-l) hn z)))

lemma add_coe_notMem_lattice_iff (z : ℂ) (l : L.lattice) :
    z + l ∉ L.lattice ↔ z ∉ L.lattice := by
  constructor
  · intro h hz
    exact h (add_mem hz l.2)
  · intro h hz
    exact h (by simpa only [add_sub_cancel_right] using sub_mem hz l.2)

/-- Translation by a period on the actual domain of the Weierstrass function. -/
def translate (l : L.lattice) (z : {z : ℂ // z ∉ L.lattice}) : {z : ℂ // z ∉ L.lattice} :=
  ⟨z.1 + l, (L.add_coe_notMem_lattice_iff z.1 l).mpr z.2⟩

@[simp]
lemma derivWeierstrassP_add_coe (z : {z : ℂ // z ∉ L.lattice}) (l : L.lattice) :
    ℘'[L] (L.translate l z) = ℘'[L] z := by
  let w : ℂ := L.ω₁ / 2
  have h₀ : w ∉ L.lattice := L.ω₁_div_two_notMem_lattice
  have h₁ : w - l ∉ L.lattice := fun h ↦ h₀ (by
    simpa only [sub_add_cancel] using add_mem h l.2)
  let z' : {x : ℂ // x ∉ (L.lattice : Set ℂ) \ {w - l}} := ⟨z.1, fun h ↦ z.2 h.1⟩
  exact (L.derivWeierstrassPExcept_of_notMem w h₀ (L.translate l z)).symm.trans
    ((L.derivWeierstrassPExcept_add_coe w l z').trans
      (L.derivWeierstrassPExcept_of_notMem (w - l) h₁ z))

lemma periodic_derivWeierstrassP (l : L.lattice) : ℘'[L] ∘ L.translate l = ℘'[L] :=
  funext (L.derivWeierstrassP_add_coe · l)

lemma derivWeierstrassP_sub_coe (z : {z : ℂ // z ∉ L.lattice}) (l : L.lattice) :
    ℘'[L] (L.translate (-l) z) = ℘'[L] z :=
  L.derivWeierstrassP_add_coe z (-l)

end derivWeierstrassP

/-- The constant subtracted from the summand at a nonzero lattice point. At the origin the
initial term of the Weierstrass series needs no such subtraction. -/
def latticeRenormalization (l : L.lattice) : ℂ :=
  if hl : (l : ℂ) = 0 then 0 else 1 / (l : ℂ) ^ 2

section AnalyticWeierstrassPExcept

/-- Reciprocal powers of nonzero lattice displacements are summable in degree greater than two. -/
lemma summable_sumInvPow (x : ℂ) {r : ℕ} (hr : 2 < r) :
    Summable (fun l : {l : L.lattice // (l : ℂ) ≠ x} ↦ (((l.1 : ℂ) - x) ^ r)⁻¹) := by
  have hdim : Module.finrank ℤ L.lattice = 2 := L.finrank_lattice
  refine Summable.of_norm_bounded (ZLattice.summable_norm_sub_zpow L.lattice
    (-r) (by rw [hdim]; omega) x) fun l ↦ le_of_eq ?_
  have hl : (l.1 : ℂ) - x ≠ 0 := sub_ne_zero.mpr l.2
  calc
    _ = ‖((l.1 : ℂ) - x) ^ (-(r : ℤ))‖ := (congrArg norm (zpow_neg₀ hl (r : ℤ))).symm
    _ = _ := norm_zpow _ _

/-- The lattice reciprocal-power sum, omitting a zero displacement if `x` lies in the lattice.
The domain is convergence of the resulting unordered sum. Degree greater than two is a routine
sufficient condition; it is not built into the definition's domain. -/
def sumInvPow (x : ℂ) (r : ℕ)
    (_hs : Summable (fun l : {l : L.lattice // (l : ℂ) ≠ x} ↦
      (((l.1 : ℂ) - x) ^ r)⁻¹) := by apply summable_sumInvPow; omega) : ℂ :=
  ∑' l : {l : L.lattice // (l : ℂ) ≠ x}, (((l.1 : ℂ) - x) ^ r)⁻¹

lemma hasSum_sumInvPow (x : ℂ) (r : ℕ)
    (hs : Summable (fun l : {l : L.lattice // (l : ℂ) ≠ x} ↦
      (((l.1 : ℂ) - x) ^ r)⁻¹) := by apply summable_sumInvPow; omega) :
    HasSum (fun l : {l : L.lattice // (l : ℂ) ≠ x} ↦ (((l.1 : ℂ) - x) ^ r)⁻¹)
      (L.sumInvPow x r hs) := hs.hasSum

/-- A reciprocal-power lattice sum may also be written on the whole lattice with the
singular index explicitly omitted. No reciprocal is formed at that index. -/
lemma sumInvPow_eq_tsum (x : ℂ) (r : ℕ)
    (hs : Summable (fun l : {l : L.lattice // (l : ℂ) ≠ x} ↦
      (((l.1 : ℂ) - x) ^ r)⁻¹) := by apply summable_sumInvPow; omega) :
    L.sumInvPow x r hs = ∑' l : L.lattice,
      if hl : (l : ℂ) = x then 0 else (((l : ℂ) - x) ^ r)⁻¹ := by
  let g (l : L.lattice) : ℂ :=
    if hl : (l : ℂ) = x then 0 else (((l : ℂ) - x) ^ r)⁻¹
  have hsupport : Function.support g ⊆ {l : L.lattice | (l : ℂ) ≠ x} := by
    intro l hl he
    exact hl (by simp only [g, dite_eq_left he])
  rw [sumInvPow]
  calc
    (∑' l : {l : L.lattice // (l : ℂ) ≠ x}, (((l.1 : ℂ) - x) ^ r)⁻¹) =
        ∑' l : {l : L.lattice // (l : ℂ) ≠ x}, g l.1 := by
      apply tsum_congr
      intro l
      simp only [g, dite_eq_right l.2]
    _ = ∑' l : L.lattice, g l := tsum_subtype_eq_of_support_subset hsupport

/-- The power series expansion of `℘[L - l₀]` at `x`.
See `PeriodPair.hasFPowerSeriesOnBall_weierstrassPExcept`. -/
def weierstrassPExceptSeries (l₀ : ℂ) (x : {x : ℂ // x ∉ (L.lattice : Set ℂ) \ {l₀}}) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  .ofScalars _ fun i ↦ ∑' l : L.lattice, L.weierstrassPExceptSummand l₀ x i l

lemma coeff_weierstrassPExceptSeries (l₀ : ℂ)
    (x : {x : ℂ // x ∉ (L.lattice : Set ℂ) \ {l₀}}) (i : ℕ) :
    (L.weierstrassPExceptSeries l₀ x).coeff i =
      ∑' l : L.lattice, L.weierstrassPExceptSummand l₀ x i l :=
  FormalMultilinearSeries.coeff_ofScalars

lemma coeff_weierstrassPExceptSeries_self (l₀ : ℂ) (i : ℕ) :
    (L.weierstrassPExceptSeries l₀ ⟨l₀, by simp⟩).coeff i =
      if hi : i = 0 then ℘[L - l₀] ⟨l₀, by simp⟩ else (i + 1) * L.sumInvPow l₀ (i + 2) := by
  rw [coeff_weierstrassPExceptSeries]
  cases i with
  | zero => rfl
  | succ i =>
    have hs := L.summable_sumInvPow l₀ (r := i.succ + 2) (by omega)
    rw [dite_eq_right (Nat.succ_ne_zero i), L.sumInvPow_eq_tsum l₀ (i.succ + 2) hs,
      ← tsum_mul_left]
    apply tsum_congr
    intro l
    by_cases hl : (l : ℂ) = l₀
    · simp only [weierstrassPExceptSummand, dite_eq_left hl, mul_zero]
    · simp only [weierstrassPExceptSummand, dite_eq_right hl, Nat.add_one_ne_zero, ite_false,
        sub_zero, zpow_neg₀ (sub_ne_zero.mpr hl), zpow_natCast₀]

set_option backward.isDefEq.respectTransparency.types false in
/--
In the power series expansion of `℘(z) = ∑ᵢ aᵢ (z - x)ⁱ` at some `x ∉ L`,
each `aᵢ` can be written as a sum over `l ∈ L`, i.e.
`aᵢ = ∑ₗ, (i + 1) * (l - x)⁻ⁱ⁻²` for `i ≠ 0` and `a₀ = ∑ₗ, (l - x)⁻² - l⁻²`.

We show that the double sum converges if `z` falls in a ball centered at `x` that doesn't touch `L`.
-/
-- We should be able to skip this computation via some general complex-analytic machinery but
-- they are missing at the moment.
-- Consider refactoring once we have developed more of the missing API.
lemma summable_weierstrassPExceptSummand (l₀ : ℂ)
    (z x : {z : ℂ // z ∉ (L.lattice : Set ℂ) \ {l₀}})
    (hx : ∀ l : L.lattice, l.1 ≠ l₀ → ‖z.1 - x.1‖ < ‖(l : ℂ) - x.1‖) :
    Summable (Function.uncurry fun b c ↦
      L.weierstrassPExceptSummand l₀ x b c * (z.1 - x.1) ^ b) := by
  rcases z with ⟨z, hz₀⟩
  rcases x with ⟨x, hx₀⟩
  -- We first find a `κ > 1`,
  -- such that the ball centered at `x` with radius `κ * ‖z - x‖` does not touch `L`.
  obtain ⟨κ, hκ, hκ'⟩ : ∃ κ : ℝ, 1 < κ ∧ ∀ l : L.lattice, l.1 ≠ l₀ → ‖z - x‖ * κ < ‖l - x‖ := by
    obtain ⟨κ, hκ, hκ'⟩ := Metric.isOpen_iff.mp ((continuous_mul_const ‖z - x‖).isOpen_preimage _
      (isClosedMap_dist x _
      (L.isClosed_of_subset_lattice (Set.sdiff_subset (t := {l₀})))).upperClosure.isOpen_compl) 1
      (by simpa [Complex.dist_eq, @forall_comm ℝ, norm_sub_rev x] using hx)
    refine ⟨κ / 2 + 1, by simpa, fun l hl ↦ ?_⟩
    have : ∀ l ∈ L.lattice, l ≠ l₀ → (κ / 2 + 1) * ‖z - x‖ < dist x l := by
      simpa using @hκ' (κ / 2 + 1) (by simp [div_lt_iff₀, abs_eq_self.mpr hκ.le, hκ])
    simpa only [Complex.dist_eq, norm_sub_rev x, mul_comm] using this _ l.2 hl
  have hκ₀ : 0 < κ := zero_lt_one.trans hκ
  -- We single out the degree zero term via this equiv.
  let e : ℕ × L.lattice ≃ L.lattice ⊕ (ℕ × L.lattice) :=
    { toFun := fun
        | (0, l) => .inl l
        | (i + 1, l) => .inr (i, l)
      invFun := fun
        | .inl l => (0, l)
        | .inr (i, l) => (i + 1, l)
      left_inv := by rintro ⟨_ | _, _⟩ <;> rfl
      right_inv := by rintro (_ | ⟨_, _⟩) <;> rfl }
  rw [← e.symm.summable_iff]
  apply Summable.sum
  · -- for the degree zero term, this is the usual summability of the definition of `℘`.
    simpa [e, Function.comp_def, Function.uncurry] using!
      (L.hasSum_weierstrassPExcept l₀ ⟨x, hx₀⟩).summable
  · -- Positive degrees are dominated by a product of a geometric and a lattice sequence.
    dsimp [e, Function.comp_def, Function.uncurry_def, weierstrassPExceptSummand]
    let q := κ⁻¹
    have hq : 0 < q := inv_pos_of_pos hκ₀
    have hqnorm : ‖q‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_pos hq]
      exact inv_lt_one_of_one_lt₀ hκ
    have H₁ : Summable (fun i : ℕ ↦ ((i : ℝ) + 2) * q ^ i) := by
      refine ((summable_pow_mul_geometric_of_norm_lt_one 1 hqnorm).add
        ((summable_geometric_of_norm_lt_one hqnorm).mul_left 2)).congr ?_
      intro i
      simp only [pow_one, add_mul]
    have H₂ : Summable fun l : L.lattice ↦ L.latticeRpowMajorant x l * ‖z - x‖ :=
      (L.summable_latticeRpowMajorant x).mul_right _
    have h₂ (l : L.lattice) : 0 ≤ L.latticeRpowMajorant x l * ‖z - x‖ :=
      mul_nonneg (L.latticeRpowMajorant_nonneg x l) (norm_nonneg _)
    refine Summable.of_norm_bounded (H₁.mul_of_nonneg H₂
      (fun _ ↦ mul_nonneg (by positivity) (pow_nonneg hq.le _)) h₂) ?_
    intro p
    split_ifs with hp
    · simp only [zero_mul, norm_zero]
      exact mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hq.le _)) (h₂ p.2)
    have hpx : (p.2 : ℂ) - x ≠ 0 := by
      intro h
      have he : (p.2 : ℂ) = x := sub_eq_zero.mp h
      exact hx₀ ⟨he ▸ p.2.2, by simpa only [Set.mem_singleton_iff, ← he] using hp⟩
    let u := ‖(p.2 : ℂ) - x‖
    let v := ‖z - x‖
    have hu : 0 < u := norm_pos_iff.mpr hpx
    have hv : 0 ≤ v := norm_nonneg _
    have hratio : v / u ≤ q := by
      apply (div_le_iff₀ hu).mpr
      exact (le_inv_mul_iff₀ hκ₀).mpr (by simpa only [mul_comm] using (hκ' p.2 hp).le)
    have hcoef : ‖((p.1 + 1 : ℕ) : ℂ) + 1‖ = (p.1 : ℝ) + 2 := by
      rw [show ((p.1 + 1 : ℕ) : ℂ) + 1 = ((p.1 + 2 : ℕ) : ℂ) by push_cast; ring]
      rw [Complex.norm_natCast]
      push_cast
      rfl
    have hexponent : (p.1 : ℤ) + 1 + 2 = (↑(p.1 + 3) : ℤ) := by omega
    have hnorm : ‖((p.2 : ℂ) - x) ^ ((p.1 : ℤ) + 1 + 2)‖ = u ^ (p.1 + 3) := by
      let power (n : ℤ) := Checked.zpow ((p.2 : ℂ) - x) n (fun _ ↦ hpx.isUnit)
      calc ‖power ((p.1 : ℤ) + 1 + 2)‖ = ‖power (↑(p.1 + 3) : ℤ)‖ :=
            congrArg (fun n ↦ ‖power n‖) hexponent
        _ = _ := by
          dsimp only [power]
          rw [zpow_natCast₀, norm_pow]
    calc
      _ = (p.1 + 2) * u⁻¹ ^ (p.1 + 3) * v ^ (p.1 + 1) := by
        simp only [sub_zero, norm_mul, norm_pow, zpow_neg₀ hpx, norm_inv, hcoef, hnorm, v,
          inv_pow₀ (ha := hu.ne'.isUnit)]
      _ = (p.1 + 2) * (v / u) ^ p.1 * (u⁻¹ ^ 3 * v) := by
        rw [pow_add u⁻¹ p.1 3, pow_succ v p.1, div_eq_mul_inv₀, mul_pow]
        ring
      _ ≤ (p.1 + 2) * q ^ p.1 * (u⁻¹ ^ 3 * v) := by
        have hu' : 0 ≤ u⁻¹ := (inv_pos_of_pos hu).le
        gcongr
      _ = _ := by
        rw [L.latticeRpowMajorant_of_ne (sub_ne_zero.mp hpx),
          Real.rpow_neg_eq_inv_rpow u (3 : ℝ) (hx := hu.ne'.isUnit), Real.rpow_ofNat]

private lemma weierstrassPExceptSummand_of_ne (l₀ : ℂ)
    (x : {x : ℂ // x ∉ (L.lattice : Set ℂ) \ {l₀}}) (i : ℕ) (l : L.lattice)
    (hl : (l : ℂ) ≠ l₀) {hx : (l : ℂ) - x.1 ≠ 0} :
    L.weierstrassPExceptSummand l₀ x i l =
      (i + 1) * Checked.inv (((l : ℂ) - x.1) ^ (i + 2)) (pow_ne_zero _ hx).isUnit -
        if i = 0 then L.latticeRenormalization l else 0 := by
  have hc : (if hl₀ : (l : ℂ) = 0 then 0 else (l : ℂ) ^ (-2 : ℤ)) =
      L.latticeRenormalization l := by
    by_cases h : (l : ℂ) = 0
    · simp [latticeRenormalization, h]
    · simp [latticeRenormalization, h, zpow_neg₀ h, one_div₀]
  simp only [weierstrassPExceptSummand, dite_eq_right hl, zpow_neg₀ hx, zpow_natCast₀, hc]

lemma weierstrassPExcept_eq_tsum (l₀ : ℂ)
    (z x : {z : ℂ // z ∉ (L.lattice : Set ℂ) \ {l₀}})
    (hx : ∀ l : L.lattice, l.1 ≠ l₀ → ‖z.1 - x.1‖ < ‖(l : ℂ) - x.1‖) :
    ℘[L - l₀] z = ∑' i : ℕ, (L.weierstrassPExceptSeries l₀ x).coeff i * (z.1 - x.1) ^ i := by
  trans ∑' (l : L.lattice) (i : ℕ), L.weierstrassPExceptSummand l₀ x i l * (z.1 - x.1) ^ i
  · rw [weierstrassPExcept]
    apply tsum_congr
    intro l
    by_cases hl : (l : ℂ) = l₀
    · simp only [weierstrassPExceptSummand, dite_eq_left hl, zero_mul, tsum_zero]
    have hnonzero (u : {w : ℂ // w ∉ (L.lattice : Set ℂ) \ {l₀}}) : (l : ℂ) - u.1 ≠ 0 := by
      intro he
      have h := sub_eq_zero.mp he
      exact u.2 ⟨h ▸ l.2, by simpa only [Set.mem_singleton_iff, ← h] using hl⟩
    have hlx := hnonzero x
    have hlz := hnonzero z
    have heq : ((l : ℂ) - x.1) - (z.1 - x.1) = l.1 - z.1 := by abel
    have hy : ((l : ℂ) - x.1) - (z.1 - x.1) ≠ 0 := heq.symm ▸ hlz
    have hvalue : 1 / (((l : ℂ) - x.1) - (z.1 - x.1)) ^ 2 =
        (((l : ℂ) - z.1) ^ 2)⁻¹ := by
      rw [one_div₀]
      exact inv_inj₀.mpr (congrArg (· ^ 2) heq)
    have hs : HasSum
        (fun i : ℕ ↦ (i + 1) * (((l : ℂ) - x.1) ^ (i + 2))⁻¹ * (z.1 - x.1) ^ i)
        (((l : ℂ) - z.1) ^ 2)⁻¹ := by
      have h := (Complex.one_div_sub_sq_hasFPowerSeriesOnBall_zero hlx).hasSum
        (y := ⟨z.1 - x.1, hy⟩) (by simpa [enorm_eq_nnnorm] using hx l hl)
      simpa only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, sub_zero, hvalue,
        mul_comm] using h
    have hc : HasSum (fun i : ℕ ↦ if i = 0 then L.latticeRenormalization l else 0)
        (L.latticeRenormalization l) := by
      simpa only [ite_true, eq_self] using
        (hasSum_single (f := fun i : ℕ ↦ if i = 0 then L.latticeRenormalization l else 0) 0
          (fun i hi ↦ ite_eq_right hi))
    have hs' : HasSum (fun i ↦ L.weierstrassPExceptSummand l₀ x i l * (z.1 - x.1) ^ i)
        ((((l : ℂ) - z.1) ^ 2)⁻¹ - L.latticeRenormalization l) := by
      convert hs.sub hc using 1
      funext i
      rw [L.weierstrassPExceptSummand_of_ne l₀ x i l hl (hx := hlx), sub_mul]
      by_cases hi : i = 0 <;> simp [hi]
    rw [L.weierstrassPExceptSummand_of_ne l₀ z 0 l hl (hx := hlz)]
    simpa using hs'.tsum_eq.symm
  · simp_rw [coeff_weierstrassPExceptSeries, ← tsum_mul_right]
    exact (L.summable_weierstrassPExceptSummand l₀ z x hx).tsum_comm

lemma weierstrassPExceptSeries_hasSum (l₀ : ℂ)
    (z x : {z : ℂ // z ∉ (L.lattice : Set ℂ) \ {l₀}})
    (hx : ∀ l : L.lattice, l.1 ≠ l₀ → ‖z.1 - x.1‖ < ‖(l : ℂ) - x.1‖) :
    HasSum (fun i ↦ (L.weierstrassPExceptSeries l₀ x).coeff i * (z.1 - x.1) ^ i)
      (℘[L - l₀] z) := by
  refine (Summable.hasSum_iff ?_).mpr (L.weierstrassPExcept_eq_tsum l₀ z x hx).symm
  simp_rw [coeff_weierstrassPExceptSeries, ← tsum_mul_right]
  exact (L.summable_weierstrassPExceptSummand l₀ z x hx).prod

lemma hasFPowerSeriesOnBall_weierstrassPExcept (l₀ : ℂ)
    (x : {x : ℂ // x ∉ (L.lattice : Set ℂ) \ {l₀}}) (r : NNReal) (hr0 : 0 < r)
    (hr : Metric.closedBall x.1 r ⊆ ((L.lattice : Set ℂ) \ {l₀})ᶜ) :
    HasFPowerSeriesOnBall ℘[L - l₀] (L.weierstrassPExceptSeries l₀ x) x r Subtype.val := by
  have hdist (l : L.lattice) (hl : (l : ℂ) ≠ l₀) : (r : ℝ) < ‖(l : ℂ) - x.1‖ := by
    by_contra h
    have hlball : (l : ℂ) ∈ Metric.closedBall x.1 r := by
      simpa only [mem_closedBall_iff_norm] using le_of_not_gt h
    exact (hr hlball) ⟨l.2, hl⟩
  have hy : x.1 + (r : ℂ) ∉ (L.lattice : Set ℂ) \ {l₀} :=
    hr (by simp [Metric.mem_closedBall, dist_eq_norm])
  constructor
  · apply FormalMultilinearSeries.le_radius_of_tendsto (l := 0)
    convert!
      tendsto_norm.comp
        (L.weierstrassPExceptSeries_hasSum l₀ ⟨x.1 + (r : ℂ), hy⟩ x
          (fun l hl => by simpa using hdist l hl)).summable.tendsto_atTop_zero using
      2 with i
    · simp [weierstrassPExceptSeries]
    · simp
  · exact ENNReal.coe_pos.mpr hr0
  · intro z hz
    have hz' : ‖z.1 - x.1‖ < r := by simpa using hz
    simpa only [weierstrassPExceptSeries, FormalMultilinearSeries.ofScalars_apply_eq,
      FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul] using
      L.weierstrassPExceptSeries_hasSum l₀ z x (fun l hl => hz'.trans (hdist l hl))

lemma hasFPowerSeriesAt_weierstrassPExcept (l : ℂ) :
    HasFPowerSeriesAt ℘[L - l] (.ofScalars (𝕜 := ℂ) ℂ fun i : ℕ ↦
      if hi : i = 0 then ℘[L - l] ⟨l, by simp⟩ else (i + 1) * L.sumInvPow l (i + 2))
      ⟨l, by simp⟩ Subtype.val := by
  obtain ⟨r, h₁, h₂⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (L.compl_lattice_sdiff_singleton_mem_nhds l)
  lift r to NNReal using h₁.le
  have hseries : L.weierstrassPExceptSeries l ⟨l, by simp⟩ =
      .ofScalars (𝕜 := ℂ) ℂ (fun i : ℕ =>
        if hi : i = 0 then ℘[L - l] ⟨l, by simp⟩ else (i + 1) * L.sumInvPow l (i + 2)) := by
    rw [weierstrassPExceptSeries, FormalMultilinearSeries.ofScalars_series_eq_iff]
    funext i
    simpa only [weierstrassPExceptSeries, FormalMultilinearSeries.coeff_ofScalars] using
      L.coeff_weierstrassPExceptSeries_self l i
  rw [← hseries]
  exact (L.hasFPowerSeriesOnBall_weierstrassPExcept l ⟨l, by simp⟩ r h₁ h₂).hasFPowerSeriesAt

lemma analyticOnNhd_weierstrassPExcept (l₀ : ℂ) :
    AnalyticOnNhd ℂ ℘[L - l₀] Set.univ Subtype.val := by
  intro x _
  obtain ⟨r, hr₀, hr⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (L.isOpen_compl_lattice_sdiff.mem_nhds x.2)
  exact (L.hasFPowerSeriesOnBall_weierstrassPExcept l₀ x ⟨r, hr₀.le⟩ hr₀ hr).analyticAt

@[fun_prop]
lemma analyticAt_weierstrassPExcept (l₀ : ℂ) :
    AnalyticAt ℂ ℘[L - l₀] ⟨l₀, by simp⟩ Subtype.val :=
  L.analyticOnNhd_weierstrassPExcept _ _ (by simp)

/-- `weierstrassPExcept l₀` is differentiable at every point of its actual open domain. -/
lemma differentiableOn_weierstrassPExcept (l₀ : ℂ) :
    DifferentiableOn ℂ ℘[L - l₀] Set.univ Subtype.val := by
  intro x _
  exact differentiableWithinAt_univ.mpr
    ((L.analyticOnNhd_weierstrassPExcept l₀ x (by simp)).differentiableAt
      continuous_subtype_val.continuousAt)

lemma hasDerivAt_weierstrassPExcept (l₀ : ℂ) (x : {x : ℂ // x ∉ (L.lattice : Set ℂ) \ {l₀}}) :
    HasDerivAt ℘[L - l₀] (℘'[L - l₀] x) x Subtype.val := by
  obtain ⟨r, hr₀, hr⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (L.isOpen_compl_lattice_sdiff.mem_nhds x.2)
  have h := (L.hasFPowerSeriesOnBall_weierstrassPExcept l₀ x ⟨r, hr₀.le⟩ hr₀ hr)
    |>.hasFPowerSeriesAt.hasIteratedDerivAt_coeff continuous_subtype_val 1
  simpa only [HasIteratedDerivAt.one, Nat.factorial_one, one_smul, coeff_weierstrassPExceptSeries,
    derivWeierstrassPExcept] using h

lemma deriv_weierstrassPExcept_same (l : ℂ) :
    HasDerivAt ℘[L - l] (℘'[L - l] ⟨l, by simp⟩) ⟨l, by simp⟩ Subtype.val :=
  L.hasDerivAt_weierstrassPExcept l ⟨l, by simp⟩

lemma iteratedDeriv_weierstrassPExcept_self (l : ℂ) (n : ℕ) :
    HasIteratedDerivAt n ℘[L - l]
      (if hn : n = 0 then ℘[L - l] ⟨l, by simp⟩ else (n + 1)! * L.sumInvPow l (n + 2))
      ⟨l, by simp⟩ Subtype.val := by
  have h := (L.hasFPowerSeriesAt_weierstrassPExcept l)
    |>.hasIteratedDerivAt_coeff continuous_subtype_val n
  cases n with
  | zero => simp [HasIteratedDerivAt.zero]
  | succ n =>
      have heq : n.succ.factorial • ((n.succ + 1 : ℂ) * L.sumInvPow l (n.succ + 2)) =
          (n.succ + 1)! * L.sumInvPow l (n.succ + 2) := by
        rw [← Nat.cast_smul_eq_nsmul ℂ, smul_eq_mul, Nat.factorial_succ n.succ,
          Nat.cast_mul, Nat.cast_add, Nat.cast_one]
        ring
      simpa only [Nat.succ_ne_zero, dite_false, FormalMultilinearSeries.coeff_ofScalars, heq]
        using h

end AnalyticWeierstrassPExcept

section AnalyticderivWeierstrassPExcept

/-- The power series expansion of `℘'[L - l₀]` at `x`.
See `PeriodPair.hasFPowerSeriesOnBall_derivWeierstrassPExcept`. -/
def derivWeierstrassPExceptSeries (l₀ : ℂ) (x : {x : ℂ // x ∉ (L.lattice : Set ℂ) \ {l₀}}) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  .ofScalars _ fun i ↦ ∑' l : L.lattice, if hl : l.1 = l₀ then 0 else
    have hlx : l.1 - x.1 ≠ 0 := by
      intro h
      apply x.2
      have hx : x.1 = l.1 := (sub_eq_zero.mp h).symm
      exact ⟨hx.symm ▸ l.2, by simpa only [Set.mem_singleton_iff, hx] using hl⟩
    (i + 1) * (i + 2) * (l.1 - x.1) ^ (- ↑(i + 3) : ℤ)

lemma hasFPowerSeriesOnBall_derivWeierstrassPExcept (l₀ : ℂ)
    (x : {x : ℂ // x ∉ (L.lattice : Set ℂ) \ {l₀}}) (r : NNReal) (hr0 : 0 < r)
    (hr : Metric.closedBall x.1 r ⊆ ((L.lattice : Set ℂ) \ {l₀})ᶜ) :
    HasFPowerSeriesOnBall ℘'[L - l₀] (L.derivWeierstrassPExceptSeries l₀ x) x r Subtype.val := by
  obtain ⟨g, hg, hd⟩ := (L.hasFPowerSeriesOnBall_weierstrassPExcept l₀ x r hr0 hr)
    |>.exists_hasFPowerSeriesOnBall_deriv continuous_subtype_val
  have hseries : (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).compFormalMultilinearSeries
      (L.weierstrassPExceptSeries l₀ x).derivSeries = L.derivWeierstrassPExceptSeries l₀ x := by
    refine FormalMultilinearSeries.ext fun n ↦ ?_
    rw [← ContinuousMultilinearMap.mkPiRing_apply_one_eq_self
      ((ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).compFormalMultilinearSeries
        (L.weierstrassPExceptSeries l₀ x).derivSeries n),
      ← ContinuousMultilinearMap.mkPiRing_apply_one_eq_self
        (L.derivWeierstrassPExceptSeries l₀ x n)]
    congr 1
    change (L.weierstrassPExceptSeries l₀ x).derivSeries.coeff n 1 =
      (L.derivWeierstrassPExceptSeries l₀ x).coeff n
    rw [FormalMultilinearSeries.derivSeries_coeff_one, coeff_weierstrassPExceptSeries,
      derivWeierstrassPExceptSeries, FormalMultilinearSeries.coeff_ofScalars,
      ← Nat.cast_smul_eq_nsmul ℂ, smul_eq_mul, ← tsum_mul_left]
    apply tsum_congr
    intro w
    by_cases hw : w.1 = l₀
    · simp only [weierstrassPExceptSummand, dite_eq_left hw, mul_zero]
    · simp only [weierstrassPExceptSummand, dite_eq_right hw, Nat.add_one_ne_zero, ite_false,
        sub_zero,
        Nat.cast_add, Nat.cast_one, mul_assoc]
      ring_nf
  rw [hseries] at hg
  refine ⟨hg.r_le, hg.r_pos, fun {y} hy ↦ ?_⟩
  have heq : g y = ℘'[L - l₀] y := by
    rw [← (hd y hy).deriv L.isOpen_compl_lattice_sdiff.isOpenEmbedding_subtypeVal,
      (L.hasDerivAt_weierstrassPExcept l₀ y).deriv
        L.isOpen_compl_lattice_sdiff.isOpenEmbedding_subtypeVal]
  simpa only [heq] using hg.hasSum (y := y) hy

lemma hasFPowerSeriesAt_derivWeierstrassPExcept (l : ℂ) :
    HasFPowerSeriesAt ℘'[L - l]
      (.ofScalars ℂ fun i ↦ (i + 1) * (i + 2) * L.sumInvPow l (i + 3))
      ⟨l, by simp⟩ Subtype.val := by
  obtain ⟨r, h₁, h₂⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (L.compl_lattice_sdiff_singleton_mem_nhds l)
  have hseries : L.derivWeierstrassPExceptSeries l ⟨l, by simp⟩ =
      .ofScalars ℂ (fun i ↦ (i + 1) * (i + 2) * L.sumInvPow l (i + 3)) := by
    rw [derivWeierstrassPExceptSeries, FormalMultilinearSeries.ofScalars_series_eq_iff]
    funext i
    have hs := L.summable_sumInvPow l (r := i + 3) (by omega)
    rw [L.sumInvPow_eq_tsum l (i + 3) hs, ← tsum_mul_left]
    apply tsum_congr
    intro w
    by_cases hw : w.1 = l
    · simp only [dite_eq_left hw, mul_zero]
    · simp only [dite_eq_right hw, zpow_neg₀ (sub_ne_zero.mpr hw), zpow_natCast₀]
  rw [← hseries]
  exact (L.hasFPowerSeriesOnBall_derivWeierstrassPExcept l ⟨l, by simp⟩
    ⟨r, h₁.le⟩ h₁ h₂).hasFPowerSeriesAt

lemma analyticOnNhd_derivWeierstrassPExcept (l₀ : ℂ) :
    AnalyticOnNhd ℂ ℘'[L - l₀] Set.univ Subtype.val := by
  intro x _
  obtain ⟨r, hr₀, hr⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (L.isOpen_compl_lattice_sdiff.mem_nhds x.2)
  exact (L.hasFPowerSeriesOnBall_derivWeierstrassPExcept l₀ x ⟨r, hr₀.le⟩ hr₀ hr).analyticAt

@[fun_prop]
lemma analyticAt_derivWeierstrassPExcept (l : ℂ) :
    AnalyticAt ℂ ℘'[L - l] ⟨l, by simp⟩ Subtype.val :=
  L.analyticOnNhd_derivWeierstrassPExcept l _ (by simp)

lemma differentiableOn_derivWeierstrassPExcept (l : ℂ) :
    DifferentiableOn ℂ ℘'[L - l] Set.univ Subtype.val := by
  intro x _
  exact differentiableWithinAt_univ.mpr
    ((L.analyticOnNhd_derivWeierstrassPExcept l x (by simp)).differentiableAt
      continuous_subtype_val.continuousAt)

lemma iteratedDeriv_derivWeierstrassPExcept_self (l : ℂ) (n : ℕ) :
    HasIteratedDerivAt n ℘'[L - l] ((n + 2)! * L.sumInvPow l (n + 3))
      ⟨l, by simp⟩ Subtype.val := by
  have h := (L.hasFPowerSeriesAt_derivWeierstrassPExcept l)
    |>.hasIteratedDerivAt_coeff continuous_subtype_val n
  have heq : n.factorial • ((n + 1 : ℂ) * (n + 2) * L.sumInvPow l (n + 3)) =
      (n + 2)! * L.sumInvPow l (n + 3) := by
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_eq_mul,
      show n + 2 = (n + 1) + 1 by omega, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  simpa only [FormalMultilinearSeries.coeff_ofScalars, heq] using h

lemma deriv_derivWeierstrassPExcept_self (l : ℂ) :
    HasDerivAt ℘'[L - l] (6 * L.sumInvPow l 4) ⟨l, by simp⟩ Subtype.val := by
  have h := L.iteratedDeriv_derivWeierstrassPExcept_self l 1
  norm_num [HasIteratedDerivAt.one, Nat.factorial] at h
  exact h

end AnalyticderivWeierstrassPExcept

section Analytic

/-- The power series expansion of `℘` at `x`.
See `PeriodPair.hasFPowerSeriesOnBall_weierstrassP`. -/
def weierstrassPSeries (x : {x : ℂ // x ∉ L.lattice}) : FormalMultilinearSeries ℂ ℂ ℂ :=
  .ofScalars _ fun i ↦ ∑' l : L.lattice, L.weierstrassPSummand x i l

lemma weierstrassPExceptSeries_of_notMem (l₀ : ℂ) (hl₀ : l₀ ∉ L.lattice)
    (x : {x : ℂ // x ∉ L.lattice}) :
    L.weierstrassPExceptSeries l₀ ⟨x.1, fun h ↦ x.2 h.1⟩ = L.weierstrassPSeries x := by
  simp only [weierstrassPExceptSeries, weierstrassPSeries,
    L.weierstrassPExceptSummand_of_notMem _ hl₀]

lemma coeff_weierstrassPSeries (x : {x : ℂ // x ∉ L.lattice}) (i : ℕ) :
    (L.weierstrassPSeries x).coeff i = ∑' l : L.lattice, L.weierstrassPSummand x i l := by
  simp only [weierstrassPSeries, FormalMultilinearSeries.coeff_ofScalars]

lemma summable_weierstrassPSummand (z x : {x : ℂ // x ∉ L.lattice})
    (hx : ∀ l : L.lattice, ‖z.1 - x.1‖ < ‖(l : ℂ) - x.1‖) :
    Summable (Function.uncurry fun b c ↦ L.weierstrassPSummand x b c * (z.1 - x.1) ^ b) := by
  have h := L.summable_weierstrassPExceptSummand (L.ω₁ / 2)
    ⟨z.1, fun h ↦ z.2 h.1⟩ ⟨x.1, fun h ↦ x.2 h.1⟩ (fun l _ ↦ hx l)
  refine h.congr fun i ↦ ?_
  change L.weierstrassPExceptSummand (L.ω₁ / 2) ⟨x.1, fun h ↦ x.2 h.1⟩ i.1 i.2 *
    (z.1 - x.1) ^ i.1 = L.weierstrassPSummand x i.1 i.2 * (z.1 - x.1) ^ i.1
  rw [L.weierstrassPExceptSummand_of_notMem _ L.ω₁_div_two_notMem_lattice x]

lemma weierstrassPSeries_hasSum (z x : {x : ℂ // x ∉ L.lattice})
    (hx : ∀ l : L.lattice, ‖z.1 - x.1‖ < ‖(l : ℂ) - x.1‖) :
    HasSum (fun i ↦ (L.weierstrassPSeries x).coeff i * (z.1 - x.1) ^ i) (℘[L] z) := by
  have h := L.weierstrassPExceptSeries_hasSum (L.ω₁ / 2)
    ⟨z.1, fun h ↦ z.2 h.1⟩ ⟨x.1, fun h ↦ x.2 h.1⟩ (fun l _ ↦ hx l)
  rw [L.weierstrassPExcept_of_notMem _ L.ω₁_div_two_notMem_lattice z,
    L.weierstrassPExceptSeries_of_notMem _ L.ω₁_div_two_notMem_lattice x] at h
  exact h

lemma hasFPowerSeriesOnBall_weierstrassP (x : {x : ℂ // x ∉ L.lattice})
    (r : NNReal) (hr0 : 0 < r) (hr : Metric.closedBall x.1 r ⊆ L.latticeᶜ) :
    HasFPowerSeriesOnBall ℘[L] (L.weierstrassPSeries x) x r Subtype.val := by
  let lift (z : {z : ℂ // z ∉ L.lattice}) : {z : ℂ // z ∉ (L.lattice : Set ℂ) \ {L.ω₁ / 2}} :=
    ⟨z.1, fun h ↦ z.2 h.1⟩
  have h := L.hasFPowerSeriesOnBall_weierstrassPExcept _ (lift x) r hr0
    (hr.trans (Set.compl_subset_compl.mpr Set.sdiff_subset))
  simpa only [lift, Function.comp_def,
    L.weierstrassPExceptSeries_of_notMem _ L.ω₁_div_two_notMem_lattice,
    L.weierstrassPExcept_of_notMem _ L.ω₁_div_two_notMem_lattice] using
      h.comp_domain (g := lift) (x := x)

lemma analyticOnNhd_weierstrassP : AnalyticOnNhd ℂ ℘[L] Set.univ Subtype.val := by
  intro x _
  obtain ⟨r, hr₀, hr⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (L.isClosed_lattice.isOpen_compl.mem_nhds x.2)
  exact (L.hasFPowerSeriesOnBall_weierstrassP x ⟨r, hr₀.le⟩ hr₀ hr).analyticAt

lemma analyticOnNhd_derivWeierstrassP : AnalyticOnNhd ℂ ℘'[L] Set.univ Subtype.val := by
  intro x _
  let lift (z : {z : ℂ // z ∉ L.lattice}) : {z : ℂ // z ∉ (L.lattice : Set ℂ) \ {L.ω₁ / 2}} :=
    ⟨z.1, fun h ↦ z.2 h.1⟩
  have ha := L.analyticOnNhd_derivWeierstrassPExcept (L.ω₁ / 2) (lift x) (by simp)
  have h := ha.comp_domain (g := lift) (x := x)
  simpa only [lift, Function.comp_def,
    L.derivWeierstrassPExcept_of_notMem _ L.ω₁_div_two_notMem_lattice] using h

/-- The derivative of `℘` on the complement of the period lattice is `℘'`. -/
lemma deriv_weierstrassP (x : {x : ℂ // x ∉ L.lattice}) :
    HasDerivAt ℘[L] (℘'[L] x) x Subtype.val := by
  obtain ⟨r, hr₀, hr⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (L.isClosed_lattice.isOpen_compl.mem_nhds x.2)
  have h := (L.hasFPowerSeriesOnBall_weierstrassP x ⟨r, hr₀.le⟩ hr₀ hr)
    |>.hasFPowerSeriesAt.hasIteratedDerivAt_coeff continuous_subtype_val 1
  simpa only [HasIteratedDerivAt.one, Nat.factorial_one, one_smul, coeff_weierstrassPSeries,
    derivWeierstrassP] using h

lemma differentiableOn_weierstrassP : DifferentiableOn ℂ ℘[L] Set.univ Subtype.val :=
  fun x _ ↦ differentiableWithinAt_univ.mpr (L.deriv_weierstrassP x).differentiableAt

lemma differentiableOn_derivWeierstrassP : DifferentiableOn ℂ ℘'[L] Set.univ Subtype.val :=
  fun x hx ↦ differentiableWithinAt_univ.mpr
    ((L.analyticOnNhd_derivWeierstrassP x hx).differentiableAt continuous_subtype_val.continuousAt)

private lemma hasDerivAt_comp_translate (x : {x : ℂ // x ∉ L.lattice}) (l : L.lattice) :
    HasDerivAt (℘[L] ∘ L.translate l) (℘'[L] x) x Subtype.val := by
  have hc : Continuous (L.translate l) := (continuous_subtype_val.add continuous_const).subtype_mk _
  have hd : HasFDerivAt (℘[L] ∘ L.translate l)
      (ContinuousLinearMap.toSpanSingleton ℂ (℘'[L] (L.translate l x))) x
      (Subtype.val ∘ L.translate l) :=
    (L.deriv_weierstrassP (L.translate l x)).hasFDerivAt.comp_tendsto (L.translate l)
      (hc.continuousAt.tendsto.prodMap (tendsto_pure_pure _ _))
  rw [hasDerivAt_iff_hasFDerivAt, hasFDerivAt_iff_isLittleOTVS]
  rw [L.derivWeierstrassP_add_coe] at hd
  rw [hasFDerivAt_iff_isLittleOTVS] at hd
  simpa only [Function.comp_def, translate, add_sub_add_right_eq_sub,
    id_eq] using hd

private lemma weierstrassP_add_coe_aux (z : {z : ℂ // z ∉ L.lattice}) (l : L.lattice)
    (hl : (l : ℂ) / 2 ∉ L.lattice) : ℘[L] (L.translate l z) = ℘[L] z := by
  let x : {x : ℂ // x ∉ L.lattice} := ⟨-((l : ℂ) / 2), fun h ↦ hl (neg_mem_iff.mp h)⟩
  have hx : L.translate l x = ⟨-x.1, fun h ↦ x.2 (neg_mem_iff.mp h)⟩ :=
    Subtype.ext (by dsimp [translate, x]; field)
  let f (z : {z : ℂ // z ∉ L.lattice}) := ℘[L] (L.translate l z) - ℘[L] z
  have hd (z : {z : ℂ // z ∉ L.lattice}) : HasDerivAt f 0 z Subtype.val := by
    have H := (L.hasDerivAt_comp_translate z l).hasFDerivAt.sub
      (L.deriv_weierstrassP z).hasFDerivAt
    simpa [f, Pi.sub_def, Function.comp_def] using H.hasDerivAt
  have hconnected : PreconnectedSpace {z : ℂ // z ∉ L.lattice} := by
    apply isPreconnected_iff_preconnectedSpace.mp
    exact (Set.Countable.isConnected_compl_of_one_lt_rank (by simp)
      (countable_of_Lindelof_of_discrete (X := L.lattice))).2
  have hopen := L.isClosed_lattice.isOpen_compl.isOpenEmbedding_subtypeVal
  have hconst := isOpen_univ.is_const_of_deriv_eq_zero (s := Set.univ) (f := f)
    isPreconnected_univ (fun y _ ↦ differentiableWithinAt_univ.mpr (hd y).differentiableAt)
    (fun y _ ↦ (hd y).deriv hopen) (x := z) (y := x) (by simp) (by simp) hopen
  exact sub_eq_zero.mp (hconst.trans (by simp only [f, hx, L.weierstrassP_neg, sub_self]))

@[simp]
lemma weierstrassP_add_coe (z : {z : ℂ // z ∉ L.lattice}) (l : L.lattice) :
    ℘[L] (L.translate l z) = ℘[L] z := by
  let G : AddSubgroup ℂ :=
    { carrier := {w | ∃ hw : w ∈ L.lattice, ∀ y, ℘[L] (L.translate ⟨w, hw⟩ y) = ℘[L] y}
      zero_mem' := ⟨zero_mem _, fun y ↦ congrArg ℘[L] (Subtype.ext (add_zero y.1))⟩
      add_mem' := by
        rintro a b ⟨ha, h₁⟩ ⟨hb, h₂⟩
        refine ⟨add_mem ha hb, fun y ↦ ?_⟩
        have heq : L.translate ⟨a + b, add_mem ha hb⟩ y =
            L.translate ⟨b, hb⟩ (L.translate ⟨a, ha⟩ y) :=
          Subtype.ext (add_assoc y.1 a b).symm
        rw [heq, h₂, h₁]
      neg_mem' := by
        rintro a ⟨ha, h⟩
        refine ⟨neg_mem ha, fun y ↦ ?_⟩
        have heq : L.translate ⟨a, ha⟩ (L.translate ⟨-a, neg_mem ha⟩ y) = y :=
          Subtype.ext (by simp [translate])
        exact (h _).symm.trans (congrArg ℘[L] heq) }
  have hG : L.lattice ≤ G.toIntSubmodule := by
    rw [lattice, Submodule.span_le]
    rintro _ (rfl | rfl)
    · exact ⟨L.ω₁_mem_lattice, fun y ↦
        L.weierstrassP_add_coe_aux y ⟨_, L.ω₁_mem_lattice⟩ L.ω₁_div_two_notMem_lattice⟩
    · exact ⟨L.ω₂_mem_lattice, fun y ↦
        L.weierstrassP_add_coe_aux y ⟨_, L.ω₂_mem_lattice⟩ L.ω₂_div_two_notMem_lattice⟩
  obtain ⟨_, h⟩ := hG l.2
  exact h z

lemma periodic_weierstrassP (l : L.lattice) : ℘[L] ∘ L.translate l = ℘[L] :=
  funext (L.weierstrassP_add_coe · l)

lemma weierstrassP_sub_coe (z : {z : ℂ // z ∉ L.lattice}) (l : L.lattice) :
    ℘[L] (L.translate (-l) z) = ℘[L] z :=
  L.weierstrassP_add_coe z (-l)

private lemma weierstrassPSummand_zero (z : {z : ℂ // z ∉ L.lattice}) (l : L.lattice) :
    L.weierstrassPSummand z 0 l =
      Checked.div 1 ((z.1 - (l : ℂ)) ^ 2)
        (pow_ne_zero 2 (sub_ne_zero.mpr (fun h : z.1 = (l : ℂ) ↦ z.2 (h.symm ▸ l.2)))).isUnit -
        L.latticeRenormalization l := by
  have hz : (l : ℂ) - z.1 ≠ 0 := sub_ne_zero.mpr fun h ↦ z.2 (h ▸ l.2)
  by_cases hl : (l : ℂ) = 0
  · have hz' : z.1 ≠ 0 := fun h ↦ z.2 (h.symm ▸ L.lattice.zero_mem)
    simp [weierstrassPSummand, latticeRenormalization, hl, zpow_neg₀ (neg_ne_zero.mpr hz'),
      one_div₀]
  · simp [weierstrassPSummand, latticeRenormalization, hl, zpow_neg₀ hz, zpow_neg₀ hl,
      sub_sq_comm, one_div₀]

/-- At an admissible point the derivative series consists of `−2 / (z - l)^3`. -/
lemma weierstrassPSummand_one (z : {z : ℂ // z ∉ L.lattice}) (l : L.lattice) :
    L.weierstrassPSummand z 1 l =
      Checked.div (-2) ((z.1 - (l : ℂ)) ^ 3)
        (pow_ne_zero 3 (sub_ne_zero.mpr (fun h : z.1 = (l : ℂ) ↦ z.2 (h.symm ▸ l.2)))).isUnit := by
  have hz : (l : ℂ) - z.1 ≠ 0 := sub_ne_zero.mpr fun h ↦ z.2 (h ▸ l.2)
  have hz' : z.1 - (l : ℂ) ≠ 0 := sub_ne_zero.mpr (sub_ne_zero.mp hz).symm
  have hcube : ((l : ℂ) - z.1) ^ 3 = -((z.1 - l.1) ^ 3) := by
    rw [show (l : ℂ) - z.1 = -(z.1 - l.1) by abel]
    exact (show Odd 3 by decide).neg_pow _
  have hu : IsUnit (-((z.1 - l.1) ^ 3)) := (neg_ne_zero.mpr (pow_ne_zero 3 hz')).isUnit
  have hinv : (((l : ℂ) - z.1) ^ 3)⁻¹ = -(((z.1 - l.1) ^ 3)⁻¹) := calc
    _ = (-((z.1 - l.1) ^ 3))⁻¹ := (inv_inj₀ (hb := hu)).mpr hcube
    _ = _ := inv_neg₀ (ha := hu)
  simp only [weierstrassPSummand, Nat.one_ne_zero, ite_false, sub_zero, Nat.cast_one,
    one_add_one_eq_two, zpow_neg₀ hz, zpow_natCast₀, hinv, div_eq_mul_inv₀, mul_neg, neg_mul]

/-- The analytic numerator of the order-two pole chart for `℘`. Its value at the center is one. -/
lemma sq_mul_weierstrassP (l : L.lattice) (z : {z : ℂ // z ∉ L.lattice}) :
    (z.1 - (l : ℂ)) ^ 2 * ℘[L] z =
      1 + (z.1 - (l : ℂ)) ^ 2 *
        (℘[L - (l : ℂ)] ⟨z.1, fun h ↦ z.2 h.1⟩ - L.latticeRenormalization l) := by
  rw [← L.weierstrassPExcept_add l z, L.weierstrassPSummand_zero, mul_add, mul_sub,
    mul_div_cancel₀]
  ring

/-- The analytic numerator of the order-three pole chart for `℘'`. -/
lemma cube_mul_derivWeierstrassP (l : L.lattice) (z : {z : ℂ // z ∉ L.lattice}) :
    (z.1 - (l : ℂ)) ^ 3 * ℘'[L] z =
      -2 + (z.1 - (l : ℂ)) ^ 3 * ℘'[L - (l : ℂ)] ⟨z.1, fun h ↦ z.2 h.1⟩ := by
  have hz : z.1 - (l : ℂ) ≠ 0 := sub_ne_zero.mpr fun h ↦ z.2 (h.symm ▸ l.2)
  rw [← L.derivWeierstrassPExcept_sub l z, L.weierstrassPSummand_one,
    mul_add, mul_div_cancel₀, add_comm]

private def weierstrassDomain : Opens ℂ :=
  ⟨L.latticeᶜ, L.isClosed_lattice.isOpen_compl⟩

private def poleChart (l : L.lattice) : Opens ℂ :=
  ⟨((L.lattice : Set ℂ) \ {(l : ℂ)})ᶜ, L.isOpen_compl_lattice_sdiff⟩

private def weierstrassPNumerator (l : L.lattice) (z : L.poleChart l) : ℂ :=
  1 + (z.1 - l) ^ 2 * (℘[L - (l : ℂ)] z - L.latticeRenormalization l)

private def derivWeierstrassPNumerator (l : L.lattice) (z : L.poleChart l) : ℂ :=
  -2 + (z.1 - l) ^ 3 * ℘'[L - (l : ℂ)] z

private def poleDenominator (n : ℕ) (l : L.lattice) (z : L.poleChart l) : ℂ := (z.1 - l) ^ n

private lemma analyticAt_poleDenominator (n : ℕ) (l : L.lattice) (z : L.poleChart l) :
    AnalyticAt ℂ (L.poleDenominator n l) z Subtype.val :=
  ((analyticAt_id.sub (analyticAt_const (v := (l : ℂ)))).pow n).comp_domain
    (g := Subtype.val) (x := z)

private lemma poleDenominator_germ_eq_coordinate_pow (n : ℕ) (l : L.lattice) (z : L.poleChart l)
    (hz : (z : ℂ) = l) :
    AnalyticGerm.ofDomain (L.poleChart l) (L.poleChart l).isOpen (L.poleDenominator n l) z
      (L.analyticAt_poleDenominator n l z) = AnalyticGerm.coordinate (z : ℂ) ^ n := by
  change _ = AnalyticGerm.ofFun (fun w : ℂ ↦ (w - (z : ℂ)) ^ n)
    ((analyticAt_id.sub analyticAt_const).pow n)
  exact (AnalyticGerm.ofDomain_eq_ofFun_iff ..).mpr
    (Filter.Eventually.of_forall fun w ↦ by simp only [poleDenominator, hz])

private lemma poleDenominator_germ_ne_zero (n : ℕ) (l : L.lattice) (z : L.poleChart l) :
    AnalyticGerm.ofDomain (L.poleChart l) (L.poleChart l).isOpen (L.poleDenominator n l) z
      (L.analyticAt_poleDenominator n l z) ≠ 0 := by
  by_cases hz : (z : ℂ) = l
  · rw [L.poleDenominator_germ_eq_coordinate_pow n l z hz]
    exact pow_ne_zero n (AnalyticGerm.coordinate_ne_zero (z : ℂ))
  · intro h
    have := congrArg AnalyticGerm.eval h
    simp only [AnalyticGerm.eval_ofDomain, map_zero, poleDenominator] at this
    exact pow_ne_zero n (sub_ne_zero.mpr hz) this

private lemma analyticAt_weierstrassPNumerator (l : L.lattice) (z : L.poleChart l) :
    AnalyticAt ℂ (L.weierstrassPNumerator l) z Subtype.val := by
  have hx : AnalyticAt ℂ (fun y : L.poleChart l ↦ (y.1 - l) ^ 2) z Subtype.val :=
    L.analyticAt_poleDenominator 2 l z
  have hp : AnalyticAt ℂ ℘[L - (l : ℂ)] z Subtype.val :=
    L.analyticOnNhd_weierstrassPExcept l z (Set.mem_univ _)
  have hc := (L.poleChart l).isOpen.isOpenEmbedding_subtypeVal.isEmbedding
  have hconst (c : ℂ) : AnalyticAt ℂ (fun _ : L.poleChart l ↦ c) z Subtype.val :=
    (analyticAt_const (v := c)).comp_domain (g := Subtype.val) (x := z)
  exact (hconst 1).add (hx.mul (hp.sub (hconst _)) hc)

/-- The actual-domain value of `℘` has no finite limit at a lattice point. -/
lemma not_continuousAt_weierstrassP (l : L.lattice) :
    ¬ ∃ a : ℂ, Tendsto ℘[L] (Filter.comap Subtype.val (𝓝 (l : ℂ))) (𝓝 a) := by
  let z : L.poleChart l := ⟨l.1, by simp [poleChart]⟩
  let includeRegular (x : L.weierstrassDomain) : L.poleChart l := ⟨x.1, fun h ↦ x.2 h.1⟩
  let F := Filter.comap (Subtype.val : L.weierstrassDomain → ℂ) (𝓝 (l : ℂ))
  have hF : NeBot F := by
    have hne : NeBot (Filter.comap (Subtype.val : L.weierstrassDomain → ℂ) (𝓝[≠] (l : ℂ))) := by
      apply NeBot.comap_of_range_mem (by infer_instance)
      change Set.range (Subtype.val : {z : ℂ // z ∉ L.lattice} → ℂ) ∈ 𝓝[≠] (l : ℂ)
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
        (L.compl_lattice_sdiff_singleton_mem_nhds (l : ℂ))] with w hw hw'
      exact ⟨⟨w, fun h ↦ hw' ⟨h, hw⟩⟩, rfl⟩
    exact hne.mono (comap_mono nhdsWithin_le_nhds)
  rintro ⟨a, ha⟩
  have hcoord : Tendsto (Subtype.val : L.weierstrassDomain → ℂ) F (𝓝 (l : ℂ)) :=
    tendsto_comap
  have hinclude : Tendsto includeRegular F (𝓝 z) := by
    have hz : 𝓝 z = Filter.comap Subtype.val (𝓝 (l : ℂ)) := nhds_subtype_eq_comap
    rw [hz]
    exact tendsto_comap_iff.mpr hcoord
  have h₁ : Tendsto (L.weierstrassPNumerator l ∘ includeRegular) F (𝓝 1) := by
    simpa only [weierstrassPNumerator, z, sub_self, zero_pow (by decide : 2 ≠ 0),
      zero_mul, add_zero] using
      ((L.analyticAt_weierstrassPNumerator l z).continuousAt
        continuous_subtype_val).tendsto.comp hinclude
  have h₂ : Tendsto (fun w : L.weierstrassDomain ↦ (w.1 - (l : ℂ)) ^ 2 * ℘[L] w) F (𝓝 0) := by
    have hc : Tendsto (fun _ : L.weierstrassDomain ↦ (l : ℂ)) F (𝓝 (l : ℂ)) := tendsto_const_nhds
    simpa only [sub_self, zero_pow (by decide : 2 ≠ 0), zero_mul] using
      ((hcoord.sub hc).pow 2).mul ha
  have h₃ := h₂.congr' (Filter.Eventually.of_forall fun w ↦ L.sq_mul_weierstrassP l w)
  exact zero_ne_one (tendsto_nhds_unique' hF h₃ h₁)

private lemma analyticAt_derivWeierstrassPNumerator (l : L.lattice) (z : L.poleChart l) :
    AnalyticAt ℂ (L.derivWeierstrassPNumerator l) z Subtype.val := by
  have hx : AnalyticAt ℂ (fun y : L.poleChart l ↦ (y.1 - l) ^ 3) z Subtype.val :=
    L.analyticAt_poleDenominator 3 l z
  have hp : AnalyticAt ℂ ℘'[L - (l : ℂ)] z Subtype.val :=
    L.analyticOnNhd_derivWeierstrassPExcept l z (Set.mem_univ _)
  have hc := (L.poleChart l).isOpen.isOpenEmbedding_subtypeVal.isEmbedding
  exact ((analyticAt_const (v := (-2 : ℂ))).comp_domain (g := Subtype.val) (x := z)).add
    (hx.mul hp hc)

private def poleSection (n : ℕ) (N : ∀ l : L.lattice, L.poleChart l → ℂ)
    (hN : ∀ l z, AnalyticAt ℂ (N l) z Subtype.val) (l : L.lattice) :
    MeromorphicSection (L.poleChart l) :=
  MeromorphicSection.ofAnalyticFraction (N l) (L.poleDenominator n l) (hN l)
    (L.analyticAt_poleDenominator n l) (L.poleDenominator_germ_ne_zero n l)

private lemma germ_poleSection_eq_regular (f : L.weierstrassDomain → ℂ)
    (hf : ∀ z, AnalyticAt ℂ f z Subtype.val) (n : ℕ)
    (N : ∀ l : L.lattice, L.poleChart l → ℂ) (hN : ∀ l z, AnalyticAt ℂ (N l) z Subtype.val)
    (he : ∀ l z, N l ⟨z.1, fun h ↦ z.2 h.1⟩ = (z.1 - l) ^ n * f z)
    (l : L.lattice) (z : L.weierstrassDomain) :
    MeromorphicSection.germ (U := L.poleChart l) ⟨z.1, fun h ↦ z.2 h.1⟩ (L.poleSection n N hN l) =
      MeromorphicSection.germ z (MeromorphicSection.ofAnalyticDomain f hf) := by
  rw [poleSection, MeromorphicSection.germ_ofAnalyticFraction,
    MeromorphicSection.germ_ofAnalyticDomain, div_eq_iff, ← map_mul]
  apply congrArg MeromorphicGerm.ofAnalytic
  simp only [AnalyticGerm.ofDomain, ← AnalyticGerm.ofFun_mul, AnalyticGerm.ofFun_eq_iff]
  filter_upwards [L.weierstrassDomain.isOpen.mem_nhds z.2] with w hw
  have hw' : w ∈ L.poleChart l := fun h ↦ hw h.1
  have hF : (Function.extend Subtype.val f 0) w = f ⟨w, hw⟩ :=
    Subtype.val_injective.extend_apply _ _ ⟨w, hw⟩
  have hN' : (Function.extend Subtype.val (N l) 0) w = N l ⟨w, hw'⟩ :=
    Subtype.val_injective.extend_apply _ _ ⟨w, hw'⟩
  have hD : (Function.extend Subtype.val (L.poleDenominator n l) 0) w =
      L.poleDenominator n l ⟨w, hw'⟩ := Subtype.val_injective.extend_apply _ _ ⟨w, hw'⟩
  rw [Pi.mul_apply]
  calc
    _ = N l ⟨w, hw'⟩ := hN'
    _ = (w - l) ^ n * f ⟨w, hw⟩ := he l ⟨w, hw⟩
    _ = f ⟨w, hw⟩ * L.poleDenominator n l ⟨w, hw'⟩ := mul_comm _ _
    _ = _ := (congrArg₂ (· * ·) hF hD).symm

private def ellipticChart : Option L.lattice → Opens ℂ
  | none => L.weierstrassDomain
  | some l => L.poleChart l

private def ellipticSection (f : L.weierstrassDomain → ℂ)
    (hf : ∀ z, AnalyticAt ℂ f z Subtype.val) (n : ℕ)
    (N : ∀ l : L.lattice, L.poleChart l → ℂ) (hN : ∀ l z, AnalyticAt ℂ (N l) z Subtype.val)
    (he : ∀ l z, N l ⟨z.1, fun h ↦ z.2 h.1⟩ = (z.1 - l) ^ n * f z) :
    MeromorphicSection (⊤ : Opens ℂ) := by
  let chart (i : Option L.lattice) : MeromorphicSection (L.ellipticChart i) :=
    match i with
    | none => MeromorphicSection.ofAnalyticDomain f hf
    | some l => L.poleSection n N hN l
  refine MeromorphicSection.glue L.ellipticChart (fun _ ↦ le_top) ?_ chart ?_
  · intro x
    by_cases hx : (x : ℂ) ∈ L.lattice
    · exact ⟨some ⟨x, hx⟩, by simp [ellipticChart, poleChart]⟩
    · exact ⟨none, hx⟩
  · intro i j z hi hj
    by_cases hz : z ∈ L.lattice
    · have hidx : ∀ k, z ∈ L.ellipticChart k → k = some ⟨z, hz⟩ := by
        rintro (_ | l) hk
        · exact False.elim (hk hz)
        · have heq : z = (l : ℂ) := by
            by_contra hne
            exact hk ⟨hz, hne⟩
          exact congrArg some (Subtype.ext heq.symm)
      have heq : i = j := (hidx i hi).trans (hidx j hj).symm
      subst j
      rfl
    · have hreg : ∀ k (hk : z ∈ L.ellipticChart k),
          MeromorphicSection.germ ⟨z, hk⟩ (chart k) =
            MeromorphicSection.germ ⟨z, hz⟩ (MeromorphicSection.ofAnalyticDomain f hf) := by
        rintro (_ | l) hk
        · rfl
        · exact L.germ_poleSection_eq_regular f hf n N hN he l ⟨z, hz⟩
      exact (hreg i hi).trans (hreg j hj).symm

/-- The Weierstrass function as a meromorphic section on the complex plane. -/
@[no_expose]
def meromorphicWeierstrassP : MeromorphicSection (⊤ : Opens ℂ) :=
  L.ellipticSection ℘[L] (fun z ↦ L.analyticOnNhd_weierstrassP z (Set.mem_univ _)) 2
    L.weierstrassPNumerator L.analyticAt_weierstrassPNumerator
    (fun l z ↦ (L.sq_mul_weierstrassP l z).symm)

/-- The derivative of the Weierstrass function as a meromorphic section on the complex plane. -/
@[no_expose]
def meromorphicDerivWeierstrassP : MeromorphicSection (⊤ : Opens ℂ) :=
  L.ellipticSection ℘'[L] (fun z ↦ L.analyticOnNhd_derivWeierstrassP z (Set.mem_univ _)) 3
    L.derivWeierstrassPNumerator L.analyticAt_derivWeierstrassPNumerator
    (fun l z ↦ (L.cube_mul_derivWeierstrassP l z).symm)

private theorem exists_eval_ellipticSection (f : L.weierstrassDomain → ℂ)
    (hf : ∀ z, AnalyticAt ℂ f z Subtype.val) (n : ℕ)
    (N : ∀ l : L.lattice, L.poleChart l → ℂ) (hN : ∀ l z, AnalyticAt ℂ (N l) z Subtype.val)
    (he : ∀ l z, N l ⟨z.1, fun h ↦ z.2 h.1⟩ = (z.1 - l) ^ n * f z)
    (z : L.weierstrassDomain) :
    let s := L.ellipticSection f hf n N hN he
    ∃ h : (⟨z.1, by simp⟩ : (⊤ : Opens ℂ)) ∈ s.regularLocus,
      s.eval ⟨⟨z.1, by simp⟩, h⟩ = f z := by
  intro s
  let a := AnalyticGerm.ofDomain (L.weierstrassDomain : Set ℂ) L.weierstrassDomain.isOpen f z (hf z)
  have ha : MeromorphicSection.germ ⟨z.1, by simp⟩ s = MeromorphicGerm.ofAnalytic a := by
    dsimp only [s, ellipticSection]
    rw [MeromorphicSection.germ_glue (i := none) (hx := z.2)]
    rfl
  refine ⟨⟨a, ha.symm⟩, ?_⟩
  change MeromorphicGerm.eval (⟨_, ⟨a, ha.symm⟩⟩ : MeromorphicGerm.regularSubring z.1) = f z
  rw [show (⟨_, ⟨a, ha.symm⟩⟩ : MeromorphicGerm.regularSubring z.1) =
      MeromorphicGerm.analyticEquivRegular z.1 a from Subtype.ext ha]
  exact (MeromorphicGerm.eval_ofAnalytic a).trans (AnalyticGerm.eval_ofDomain ..)

lemma exists_eval_meromorphic_weierstrassP (z : {z : ℂ // z ∉ L.lattice}) :
    ∃ h : (⟨z.1, by simp⟩ : (⊤ : Opens ℂ)) ∈ L.meromorphicWeierstrassP.regularLocus,
      L.meromorphicWeierstrassP.eval ⟨⟨z.1, by simp⟩, h⟩ = ℘[L] z :=
  L.exists_eval_ellipticSection ℘[L] (fun w ↦ L.analyticOnNhd_weierstrassP w (Set.mem_univ _)) 2
    L.weierstrassPNumerator L.analyticAt_weierstrassPNumerator
    (fun l w ↦ (L.sq_mul_weierstrassP l w).symm) z

lemma exists_eval_meromorphic_derivWeierstrassP (z : {z : ℂ // z ∉ L.lattice}) :
    ∃ h : (⟨z.1, by simp⟩ : (⊤ : Opens ℂ)) ∈ L.meromorphicDerivWeierstrassP.regularLocus,
      L.meromorphicDerivWeierstrassP.eval ⟨⟨z.1, by simp⟩, h⟩ = ℘'[L] z :=
  L.exists_eval_ellipticSection ℘'[L]
    (fun w ↦ L.analyticOnNhd_derivWeierstrassP w (Set.mem_univ _)) 3
    L.derivWeierstrassPNumerator L.analyticAt_derivWeierstrassPNumerator
    (fun l w ↦ (L.cube_mul_derivWeierstrassP l w).symm) z

lemma order_weierstrassP (l : L.lattice) :
    (MeromorphicSection.germ ⟨l.1, by simp⟩ L.meromorphicWeierstrassP).order = -2 := by
  let z : L.poleChart l := ⟨l.1, by simp [poleChart]⟩
  unfold meromorphicWeierstrassP ellipticSection
  rw [MeromorphicSection.germ_glue (i := some l) (hx := z.2)]
  change (MeromorphicSection.germ z
    (L.poleSection 2 L.weierstrassPNumerator L.analyticAt_weierstrassPNumerator l)).order = -2
  have hg := MeromorphicSection.germ_ofAnalyticFraction (U := L.poleChart l)
    (L.weierstrassPNumerator l) (L.poleDenominator 2 l) (L.analyticAt_weierstrassPNumerator l)
    (L.analyticAt_poleDenominator 2 l) (L.poleDenominator_germ_ne_zero 2 l) z
  refine (congrArg MeromorphicGerm.order hg).trans ?_
  rw [MeromorphicGerm.order_div _ _ (L.poleDenominator_germ_ne_zero 2 l z)]
  have hN : (AnalyticGerm.ofDomain (L.poleChart l) (L.poleChart l).isOpen
      (L.weierstrassPNumerator l) z (L.analyticAt_weierstrassPNumerator l z)).order = 0 := by
    apply (AnalyticGerm.order_eq_zero_iff _).mpr
    rw [AnalyticGerm.eval_ofDomain]
    simp [weierstrassPNumerator, z]
  rw [hN, L.poleDenominator_germ_eq_coordinate_pow 2 l z rfl, AnalyticGerm.order_coordinate_pow]
  norm_num

lemma order_derivWeierstrassP (l : L.lattice) :
    (MeromorphicSection.germ ⟨l.1, by simp⟩ L.meromorphicDerivWeierstrassP).order = -3 := by
  let z : L.poleChart l := ⟨l.1, by simp [poleChart]⟩
  unfold meromorphicDerivWeierstrassP ellipticSection
  rw [MeromorphicSection.germ_glue (i := some l) (hx := z.2)]
  change (MeromorphicSection.germ z (L.poleSection 3 L.derivWeierstrassPNumerator
    L.analyticAt_derivWeierstrassPNumerator l)).order = -3
  have hg := MeromorphicSection.germ_ofAnalyticFraction (U := L.poleChart l)
    (L.derivWeierstrassPNumerator l) (L.poleDenominator 3 l)
    (L.analyticAt_derivWeierstrassPNumerator l) (L.analyticAt_poleDenominator 3 l)
    (L.poleDenominator_germ_ne_zero 3 l) z
  refine (congrArg MeromorphicGerm.order hg).trans ?_
  rw [MeromorphicGerm.order_div _ _ (L.poleDenominator_germ_ne_zero 3 l z)]
  have hN : (AnalyticGerm.ofDomain (L.poleChart l) (L.poleChart l).isOpen
      (L.derivWeierstrassPNumerator l) z
      (L.analyticAt_derivWeierstrassPNumerator l z)).order = 0 := by
    apply (AnalyticGerm.order_eq_zero_iff _).mpr
    rw [AnalyticGerm.eval_ofDomain]
    norm_num [derivWeierstrassPNumerator, z]
  rw [hN, L.poleDenominator_germ_eq_coordinate_pow 3 l z rfl, AnalyticGerm.order_coordinate_pow]
  norm_num

/-- The Weierstrass section is regular exactly off the period lattice. -/
lemma mem_regularLocus_meromorphic_weierstrassP_iff (z : (⊤ : Opens ℂ)) :
    z ∈ L.meromorphicWeierstrassP.regularLocus ↔ (z : ℂ) ∉ L.lattice := by
  constructor
  · intro hz hl
    have ho := (MeromorphicGerm.mem_regularSubring_iff_order_nonneg _).mp hz
    rw [L.order_weierstrassP ⟨z.1, hl⟩] at ho
    change ((0 : ℤ) : WithTop ℤ) ≤ ((-2 : ℤ) : WithTop ℤ) at ho
    exact (by decide : ¬ (0 : ℤ) ≤ -2) (WithTop.coe_le_coe.mp ho)
  · intro hz
    exact (L.exists_eval_meromorphic_weierstrassP ⟨z.1, hz⟩).choose

/-- The derivative section is regular exactly off the period lattice. -/
lemma mem_regularLocus_meromorphic_derivWeierstrassP_iff (z : (⊤ : Opens ℂ)) :
    z ∈ L.meromorphicDerivWeierstrassP.regularLocus ↔ (z : ℂ) ∉ L.lattice := by
  constructor
  · intro hz hl
    have ho := (MeromorphicGerm.mem_regularSubring_iff_order_nonneg _).mp hz
    rw [L.order_derivWeierstrassP ⟨z.1, hl⟩] at ho
    change ((0 : ℤ) : WithTop ℤ) ≤ ((-3 : ℤ) : WithTop ℤ) at ho
    exact (by decide : ¬ (0 : ℤ) ≤ -3) (WithTop.coe_le_coe.mp ho)
  · intro hz
    exact (L.exists_eval_meromorphic_derivWeierstrassP ⟨z.1, hz⟩).choose

end Analytic

section Relation

/-- The reciprocal powers defining the Eisenstein series are summable in degree above two. -/
lemma summable_G (n : ℕ) (hn : 2 < n) :
    Summable (fun l : {l : L.lattice // (l : ℂ) ≠ 0} ↦ ((l.1 : ℂ) ^ n)⁻¹) := by
  simpa only [sub_zero] using L.summable_sumInvPow 0 (r := n) hn

/-- The Eisenstein series as a function on lattices.
It takes `L` to the convergent sum `∑ l⁻ʳ` over the nonzero lattice points.
TODO: Establish connections with the `ModularForm` library. -/
def G (n : ℕ)
    (_hs : Summable (fun l : {l : L.lattice // (l : ℂ) ≠ 0} ↦ ((l.1 : ℂ) ^ n)⁻¹) := by
      apply summable_G; omega) : ℂ :=
  ∑' l : {l : L.lattice // (l : ℂ) ≠ 0}, ((l.1 : ℂ) ^ n)⁻¹

@[simp]
lemma sumInvPow_zero (n : ℕ)
    (hs : Summable (fun l : {l : L.lattice // (l : ℂ) ≠ 0} ↦ ((l.1 : ℂ) ^ n)⁻¹) := by
      apply summable_G; omega) :
    L.sumInvPow 0 n (by simpa using hs) = L.G n hs := by
  simp [sumInvPow, G]

lemma G_eq_zero_of_odd (n : ℕ) (hn : Odd n)
    (hs : Summable (fun l : {l : L.lattice // (l : ℂ) ≠ 0} ↦ ((l.1 : ℂ) ^ n)⁻¹) := by
      apply summable_G; omega) : L.G n hs = 0 := by
  let e : {l : L.lattice // (l : ℂ) ≠ 0} ≃ {l : L.lattice // (l : ℂ) ≠ 0} :=
    { toFun l := ⟨-l.1, by simpa using l.2⟩
      invFun l := ⟨-l.1, by simpa using l.2⟩
      left_inv l := by ext; simp
      right_inv l := by ext; simp }
  rw [← CharZero.eq_neg_self_iff, G, ← tsum_neg, ← e.tsum_eq]
  congr with l
  simp only [e, Equiv.coe_fn_mk, NegMemClass.coe_neg, hn.neg_pow, inv_neg₀]

/-- The lattice invariant `g₂ := 60 G₄`. -/
def g₂ : ℂ := 60 * L.G 4

/-- The lattice invariant `g₃ := 140 G₆`. -/
def g₃ : ℂ := 140 * L.G 6

-- The regular extension, with the values at the poles proved by the Taylor calculation below.
private def relation (z : ℂ) : ℂ := by
  classical
  exact if hz : z ∈ L.lattice then 0 else
    ℘'[L] ⟨z, hz⟩ ^ 2 - 4 * ℘[L] ⟨z, hz⟩ ^ 3 + L.g₂ * ℘[L] ⟨z, hz⟩ + L.g₃

private lemma analyticAt_relation_zero : AnalyticAt ℂ L.relation 0 := by
  let l : L.lattice := 0
  let x : L.poleChart l := ⟨0, by simp [l, poleChart]⟩
  obtain ⟨R, hRa, hR⟩ :=
    (L.hasFPowerSeriesAt_weierstrassPExcept (0 : ℂ))
      |>.exists_eventuallyEq_sum_add_pow_smul continuous_subtype_val 5
  obtain ⟨S, hSa, hS⟩ :=
    (L.hasFPowerSeriesAt_derivWeierstrassPExcept (0 : ℂ))
      |>.exists_eventuallyEq_sum_add_pow_smul continuous_subtype_val 4
  let P (w : ℂ) := 3 * L.G 4 + w ^ 2 * (5 * L.G 6) + w ^ 3 * R w
  let Q (w : ℂ) := 6 * L.G 4 + w ^ 2 * (20 * L.G 6) + w ^ 3 * S w
  let B (w : ℂ) := w * (Q w ^ 2 - 12 * P w ^ 2 - 4 * w ^ 4 * P w ^ 3 + L.g₂ * P w) -
    4 * S w - 12 * R w
  have hBa : AnalyticAt ℂ (fun w ↦ w * B w) 0 := by
    dsimp only [B, Q, P]
    fun_prop
  refine hBa.congr ?_
  rw [← (L.poleChart l).isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq x]
  change ∀ᶠ w : L.poleChart l in 𝓝 x, w.1 * B w.1 = L.relation w.1
  filter_upwards [hR, hS] with w hwP hwQ
  have hG3 : L.sumInvPow 0 3 = 0 :=
    (L.sumInvPow_zero 3).trans (L.G_eq_zero_of_odd 3 (by decide))
  have hG4 : L.sumInvPow 0 4 = L.G 4 := L.sumInvPow_zero 4
  have hG5 : L.sumInvPow 0 5 = 0 :=
    (L.sumInvPow_zero 5).trans (L.G_eq_zero_of_odd 5 (by decide))
  have hG6 : L.sumInvPow 0 6 = L.G 6 := L.sumInvPow_zero 6
  have hp : ℘[L - (0 : ℂ)] w = w.1 ^ 2 * P w.1 := by
    norm_num [Finset.sum_range_succ, FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul,
      hG3, hG4, hG5, hG6] at hwP
    rw [hwP]
    dsimp only [P]
    ring
  have hq : ℘'[L - (0 : ℂ)] w = w.1 * Q w.1 := by
    norm_num [Finset.sum_range_succ, FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul,
      hG3, hG4, hG5, hG6] at hwQ
    rw [hwQ]
    dsimp only [Q]
    ring
  by_cases hw₀ : (w : ℂ) = 0
  · simp [hw₀, relation]
  have hw : (w : ℂ) ∉ L.lattice := fun h ↦ w.2 ⟨h, hw₀⟩
  let z : L.weierstrassDomain := ⟨w, hw⟩
  let w' : L.poleChart l := ⟨z.1, fun h ↦ z.2 h.1⟩
  have hw' : w' = w := Subtype.ext rfl
  have hP : w.1 ^ 2 * ℘[L] z = 1 + w.1 ^ 2 * ℘[L - (0 : ℂ)] w := by
    have h : (z.1 - (l : ℂ)) ^ 2 * ℘[L] z =
        1 + (z.1 - (l : ℂ)) ^ 2 * (℘[L - (l : ℂ)] w' - L.latticeRenormalization l) :=
      L.sq_mul_weierstrassP l z
    rw [hw'] at h
    simpa [l, z, latticeRenormalization] using h
  have hQ : w.1 ^ 3 * ℘'[L] z = -2 + w.1 ^ 3 * ℘'[L - (0 : ℂ)] w := by
    have h : (z.1 - (l : ℂ)) ^ 3 * ℘'[L] z =
        -2 + (z.1 - (l : ℂ)) ^ 3 * ℘'[L - (l : ℂ)] w' := L.cube_mul_derivWeierstrassP l z
    rw [hw'] at h
    simpa [l, z] using h
  have hrel : L.relation w.1 = ℘'[L] z ^ 2 - 4 * ℘[L] z ^ 3 + L.g₂ * ℘[L] z + L.g₃ := by
    rw [relation, dite_eq_right hw]
    rfl
  apply mul_left_cancel₀ (pow_ne_zero 6 hw₀)
  symm
  calc
    w.1 ^ 6 * L.relation w.1 =
      (w.1 ^ 3 * ℘'[L] z) ^ 2 - 4 * (w.1 ^ 2 * ℘[L] z) ^ 3 +
        L.g₂ * w.1 ^ 4 * (w.1 ^ 2 * ℘[L] z) + L.g₃ * w.1 ^ 6 := by
          rw [hrel]; ring
    _ = w.1 ^ 6 * (w.1 * B w.1) := by
      rw [hP, hQ, hp, hq]
      dsimp only [g₂, g₃, B, P, Q]
      ring

@[local simp]
private lemma relation_add_coe (x : ℂ) (l : L.lattice) : L.relation (x + l) = L.relation x := by
  by_cases hx : x ∈ L.lattice
  · simp only [relation, dite_eq_left hx, dite_eq_left (add_mem hx l.2)]
  · have hx' : x + (l : ℂ) ∉ L.lattice := (L.add_coe_notMem_lattice_iff x l).mpr hx
    simp only [relation, dite_eq_right hx, dite_eq_right hx',
      ← show L.translate l ⟨x, hx⟩ = ⟨x + l, hx'⟩ from rfl,
      L.weierstrassP_add_coe, L.derivWeierstrassP_add_coe]

@[local simp]
private lemma relation_sub_coe (x : ℂ) (l : L.lattice) : L.relation (x - l) = L.relation x := by
  rw [← L.relation_add_coe _ l, sub_add_cancel]

private lemma analyticAt_relation (x : ℂ) : AnalyticAt ℂ L.relation x := by
  by_cases hx : x ∈ L.lattice
  · let l : L.lattice := ⟨x, hx⟩
    have h := L.analyticAt_relation_zero
    rw [← sub_self x] at h
    exact (h.comp (f := (· - x)) (analyticAt_id.sub analyticAt_const)).congr
      (Filter.Eventually.of_forall fun y ↦ L.relation_sub_coe y l)
  · let z : L.weierstrassDomain := ⟨x, hx⟩
    apply AnalyticAt.of_comp_domain (coord := Subtype.val) (x := z)
    · have hp : AnalyticAt ℂ ℘[L] z Subtype.val :=
        L.analyticOnNhd_weierstrassP z (Set.mem_univ _)
      have hq : AnalyticAt ℂ ℘'[L] z Subtype.val :=
        L.analyticOnNhd_derivWeierstrassP z (Set.mem_univ _)
      have hc : Topology.IsEmbedding (Subtype.val : L.weierstrassDomain → ℂ) := .subtypeVal
      have hconst (c : ℂ) : AnalyticAt ℂ (fun _ : L.weierstrassDomain ↦ c) z Subtype.val :=
        (analyticAt_const (v := c)).comp_domain (g := Subtype.val) (x := z)
      have h := (((hq.mul hq hc).sub ((hconst 4).mul ((hp.mul hp hc).mul hp hc) hc)).add
        ((hconst L.g₂).mul hp hc)).add (hconst L.g₃)
      have heq : L.relation ∘ (Subtype.val : L.weierstrassDomain → ℂ) =
          ℘'[L] * ℘'[L] - (fun _ ↦ 4) * (℘[L] * ℘[L] * ℘[L]) +
            (fun _ ↦ L.g₂) * ℘[L] + fun _ ↦ L.g₃ := by
        funext w
        change L.relation w.1 = ℘'[L] w * ℘'[L] w - 4 * (℘[L] w * ℘[L] w * ℘[L] w) +
          L.g₂ * ℘[L] w + L.g₃
        have hw : (w : ℂ) ∉ L.lattice := w.2
        have hw' : (⟨w.1, hw⟩ : {w : ℂ // w ∉ L.lattice}) = w := Subtype.ext rfl
        simp only [relation, dite_eq_right hw, pow_two, pow_succ _ 2, hw']
      rw [heq]
      exact h
    · filter_upwards [L.weierstrassDomain.isOpen.mem_nhds hx] with w hw
      exact ⟨⟨w, hw⟩, rfl⟩

private lemma relation_eq_zero : L.relation = 0 := by
  ext x
  have h : Differentiable ℂ L.relation := fun z ↦ (L.analyticAt_relation z).differentiableAt
  exact (h.apply_eq_apply_of_bounded (IsZLattice.isCompact_range_of_periodic L.lattice _
    h.continuous fun z w hw ↦ L.relation_add_coe z ⟨w, hw⟩).isBounded x 0).trans
    (by simp [relation])

/-- `℘'(z)² = 4 ℘(z)³ - g₂ ℘(z) - g₃` on the complement of the period lattice. -/
lemma derivWeierstrassP_sq (z : {z : ℂ // z ∉ L.lattice}) :
    ℘'[L] z ^ 2 = 4 * ℘[L] z ^ 3 - L.g₂ * ℘[L] z - L.g₃ := by
  have h := congrFun L.relation_eq_zero z.1
  simp only [relation, dite_eq_right z.2, Pi.zero_apply] at h
  linear_combination h

end Relation

end PeriodPair
