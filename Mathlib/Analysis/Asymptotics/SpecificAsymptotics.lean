/-
Copyright (c) 2021 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# A collection of specific asymptotic results

This file contains specific lemmas about asymptotics which don't have their place in the general
theory developed in `Mathlib/Analysis/Asymptotics/Defs.lean` and
`Mathlib/Analysis/Asymptotics/Lemmas.lean`.
-/

public section

open Bornology Filter Asymptotics Set

open scoped Topology

section NormedField

/-- A bounded function is little-o of `(x - a)⁻¹` when its coordinate `x` tends to `a`
through the punctured neighborhood. Both functions are defined on the same actual domain. -/
theorem Filter.IsBoundedUnder.isLittleO_sub_self_inv {D 𝕜 E : Type*}
    [NormedField 𝕜] [Norm E] {a : 𝕜} {l : Filter D} {f : D → E} {x : D → 𝕜}
    (h : IsBoundedUnder (· ≤ ·) l (norm ∘ f)) (hx : Tendsto x l (𝓝[≠] a))
    {hsub : ∀ t, IsUnit (x t - a)} :
    f =o[l] (fun t ↦ Checked.inv (x t - a) (hsub t)) := by
  refine (h.isBigO_const (one_ne_zero' ℝ)).trans_isLittleO
    (isLittleO_const_left.2 <| Or.inr ?_)
  have ht := (tendsto_norm_sub_self_nhdsNE a).comp hx
  simpa only [Function.comp_def, norm_inv] using ht.fun_inv_tendsto_nhdsGT_zero
    (h0 := fun t ↦ (norm_ne_zero_iff.mpr (hsub t).ne_zero).isUnit)

end NormedField

section NormedRing

variable {R : Type*} [NormedRing R] [NormMulClass R] {p q : ℕ}

open Bornology

theorem Asymptotics.isLittleO_pow_pow_cobounded_of_lt (hpq : p < q) :
    (· ^ p) =o[cobounded R] (· ^ q) := by
  rw [← Nat.add_sub_of_le hpq.le]
  simpa [pow_add] using (isBigO_refl (· ^ p) (cobounded R)).mul_isLittleO
    ((isLittleO_const_id_cobounded 1).pow (Nat.sub_pos_of_lt hpq))

theorem Asymptotics.isBigO_pow_pow_cobounded_of_le (hpq : p ≤ q) :
    (· ^ p) =O[cobounded R] (· ^ q) := by
  rcases hpq.eq_or_lt with rfl | h
  · exact isBigO_refl ..
  · exact (isLittleO_pow_pow_cobounded_of_lt h).isBigO

end NormedRing

section LinearOrderedField

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

theorem pow_div_pow_eventuallyEq_atTop {p q : ℕ} :
    (fun x : {x : 𝕜 // x ^ q ≠ 0} ↦ Checked.div ((x : 𝕜) ^ p) ((x : 𝕜) ^ q) x.2.isUnit)
      =ᶠ[comap Subtype.val atTop]
    (fun x : {x : 𝕜 // x ^ q ≠ 0} ↦ Checked.zpow (x : 𝕜) ((p : ℤ) - q)
      (fun h ↦ (isUnit_pow_iff (by omega : q ≠ 0)).mp x.2.isUnit)) := by
  filter_upwards [tendsto_comap.eventually (eventually_gt_atTop (0 : 𝕜))] with x hx
  simp [zpow_sub₀ hx.ne', zpow_natCast₀]

theorem pow_div_pow_eventuallyEq_atBot {p q : ℕ} :
    (fun x : {x : 𝕜 // x ^ q ≠ 0} ↦ Checked.div ((x : 𝕜) ^ p) ((x : 𝕜) ^ q) x.2.isUnit)
      =ᶠ[comap Subtype.val atBot]
    (fun x : {x : 𝕜 // x ^ q ≠ 0} ↦ Checked.zpow (x : 𝕜) ((p : ℤ) - q)
      (fun h ↦ (isUnit_pow_iff (by omega : q ≠ 0)).mp x.2.isUnit)) := by
  filter_upwards [tendsto_comap.eventually (eventually_lt_atBot (0 : 𝕜))] with x hx
  simp [zpow_sub₀ hx.ne, zpow_natCast₀]

theorem tendsto_pow_div_pow_atTop_atTop {p q : ℕ} (hpq : q < p) :
    Tendsto (fun x : {x : 𝕜 // x ^ q ≠ 0} ↦
      Checked.div ((x : 𝕜) ^ p) ((x : 𝕜) ^ q) x.2.isUnit)
      (comap Subtype.val atTop) atTop := by
  rw [tendsto_congr' pow_div_pow_eventuallyEq_atTop]
  exact (tendsto_zpow_atTop_atTop (by omega : (0 : ℤ) < p - q)).comp tendsto_comap

theorem tendsto_pow_div_pow_atTop_zero [TopologicalSpace 𝕜] [OrderTopology 𝕜] {p q : ℕ}
    (hpq : p < q) :
    Tendsto (fun x : {x : 𝕜 // x ^ q ≠ 0} ↦
      Checked.div ((x : 𝕜) ^ p) ((x : 𝕜) ^ q) x.2.isUnit)
      (comap Subtype.val atTop) (𝓝 0) := by
  rw [tendsto_congr' pow_div_pow_eventuallyEq_atTop]
  exact (tendsto_zpow_atTop_zero (by omega : (p : ℤ) - q < 0)).comp
    (tendsto_comap_iff.mpr tendsto_comap :
      Tendsto (fun x : {x : 𝕜 // x ^ q ≠ 0} ↦
        (⟨(x : 𝕜), (isUnit_pow_iff (by omega : q ≠ 0)).mp x.2.isUnit⟩ : {x : 𝕜 // IsUnit x}))
        (comap Subtype.val atTop) (comap Subtype.val atTop))

end LinearOrderedField

section NormedLinearOrderedField

variable {𝕜 : Type*} [NormedField 𝕜]

theorem Asymptotics.isLittleO_pow_pow_atTop_of_lt
    [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [OrderTopology 𝕜] {p q : ℕ} (hpq : p < q) :
    (fun x : 𝕜 => x ^ p) =o[atTop] fun x => x ^ q := by
  refine (isLittleO_iff_tendsto' ?_).mpr (tendsto_pow_div_pow_atTop_zero hpq)
  exact (eventually_gt_atTop 0).mono fun x hx hxq => (pow_ne_zero q hx.ne' hxq).elim

theorem Asymptotics.IsBigO.trans_tendsto_norm_atTop {α : Type*} {u v : α → 𝕜} {l : Filter α}
    (huv : u =O[l] v) (hu : Tendsto (fun x => ‖u x‖) l atTop) :
    Tendsto (fun x => ‖v x‖) l atTop := by
  rcases huv.exists_pos with ⟨c, hc, hcuv⟩
  rw [IsBigOWith] at hcuv
  convert! Tendsto.atTop_div_const hc (tendsto_atTop_mono' l hcuv hu)
  rw [mul_div_cancel_left₀]

end NormedLinearOrderedField

section Real

theorem Asymptotics.IsEquivalent.rpow {α : Type*} {u v : α → ℝ} {l : Filter α}
    (hv : 0 ≤ v) (h : u ~[l] v) {r : ℝ} :
    u ^ r ~[l] v ^ r := by
  obtain ⟨φ, hφ, huφv⟩ := IsEquivalent.exists_eq_mul h
  rw [isEquivalent_iff_exists_eq_mul]
  have hφr : Tendsto ((fun x ↦ x ^ r) ∘ φ) l (𝓝 1) := by
    rw [← Real.one_rpow r]
    exact Tendsto.comp (Real.continuousAt_rpow_const _ _ (by left; norm_num)) hφ
  use (· ^ r) ∘ φ, hφr
  conv => enter [3]; change fun x ↦ φ x ^ r * v x ^ r
  filter_upwards [Tendsto.eventually_const_lt (zero_lt_one) hφ, huφv] with x hφ_pos huv'
  simp [← Real.mul_rpow (le_of_lt hφ_pos) (hv x), huv']

theorem Asymptotics.IsEquivalent.log {α : Type*} {l : Filter α} {f g : α → ℝ} (hfg : f ~[l] g)
    (g_tendsto : Tendsto g l atTop) :
    (fun n ↦ Real.log (f n)) ~[l] (fun n ↦ Real.log (g n)) := by
  obtain ⟨φ, hφ, hmul⟩ := hfg.exists_eq_mul
  have hlog : Tendsto (fun n ↦ Real.log (φ n)) l (𝓝 0) := by
    simpa only [Real.log_one] using hφ.log one_ne_zero
  have heq : (fun n ↦ Real.log (f n) - Real.log (g n)) =ᶠ[l] (fun n ↦ Real.log (φ n)) := by
    filter_upwards [hmul, hφ.eventually_const_lt zero_lt_one,
      g_tendsto.eventually_gt_atTop 0] with n hn hφn hgn
    rw [hn, Pi.mul_apply, Real.log_mul hφn.ne' hgn.ne', add_sub_cancel_right]
  exact IsLittleO.isEquivalent <| calc
    (fun n ↦ Real.log (f n) - Real.log (g n)) =o[l] fun _ ↦ (1 : ℝ) :=
      ((isLittleO_one_iff ℝ).mpr hlog).congr' heq.symm .rfl
    _ =o[l] fun n ↦ Real.log (g n) := isLittleO_one_left_iff ℝ |>.mpr <|
      tendsto_norm_atTop_atTop.comp <| Real.tendsto_log_atTop.comp g_tendsto

open Finset

theorem Asymptotics.IsLittleO.sum_range {α : Type*} [NormedAddCommGroup α] {f : ℕ → α} {g : ℕ → ℝ}
    (h : f =o[atTop] g) (hg : 0 ≤ g) (h'g : Tendsto (fun n => ∑ i ∈ range n, g i) atTop atTop) :
    (fun n => ∑ i ∈ range n, f i) =o[atTop] fun n => ∑ i ∈ range n, g i := by
  have A : ∀ i, ‖g i‖ = g i := fun i => Real.norm_of_nonneg (hg i)
  have B : ∀ n, ‖∑ i ∈ range n, g i‖ = ∑ i ∈ range n, g i := fun n => by
    rw [Real.norm_eq_abs, abs_sum_of_nonneg]; exact fun _ _ ↦ hg _
  refine isLittleO_iff.2 ?_
  intro ε εpos
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ b : ℕ, N ≤ b → ‖f b‖ ≤ ε / 2 * g b := by
    simpa only [A, eventually_atTop] using isLittleO_iff.mp h (half_pos εpos)
  have : (fun _ : ℕ => ∑ i ∈ range N, f i) =o[atTop] fun n : ℕ => ∑ i ∈ range n, g i := by
    apply isLittleO_const_left.2
    exact Or.inr (h'g.congr fun n => (B n).symm)
  filter_upwards [isLittleO_iff.1 this (half_pos εpos), Ici_mem_atTop N] with n hn Nn
  calc
    ‖∑ i ∈ range n, f i‖ = ‖(∑ i ∈ range N, f i) + ∑ i ∈ Ico N n, f i‖ := by
      rw [sum_range_add_sum_Ico _ Nn]
    _ ≤ ‖∑ i ∈ range N, f i‖ + ‖∑ i ∈ Ico N n, f i‖ := norm_add_le _ _
    _ ≤ ‖∑ i ∈ range N, f i‖ + ∑ i ∈ Ico N n, ε / 2 * g i :=
      (add_le_add le_rfl (norm_sum_le_of_le _ fun i hi => hN _ (mem_Ico.1 hi).1))
    _ ≤ ‖∑ i ∈ range N, f i‖ + ∑ i ∈ range n, ε / 2 * g i := by
      gcongr
      · exact fun i _ _ ↦ mul_nonneg (half_pos εpos).le (hg i)
      · rw [range_eq_Ico]
        exact Ico_subset_Ico zero_le le_rfl
    _ ≤ ε / 2 * ‖∑ i ∈ range n, g i‖ + ε / 2 * ∑ i ∈ range n, g i := by rw [← mul_sum]; gcongr
    _ = ε * ‖∑ i ∈ range n, g i‖ := by
      simp only [B]
      ring

theorem Asymptotics.isLittleO_sum_range_of_tendsto_zero {α : Type*} [NormedAddCommGroup α]
    {f : ℕ → α} (h : Tendsto f atTop (𝓝 0)) :
    (fun n => ∑ i ∈ range n, f i) =o[atTop] fun n => (n : ℝ) := by
  have := ((isLittleO_one_iff ℝ).2 h).sum_range fun i => zero_le_one
  simp only [sum_const, card_range, Nat.smul_one_eq_cast] at this
  exact this tendsto_natCast_atTop_atTop

/-- The Cesaro average of a converging sequence converges to the same limit. -/
theorem Filter.Tendsto.cesaro_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {u : ℕ → E}
    {l : E} (h : Tendsto u atTop (𝓝 l)) :
    Tendsto (fun n : {n : ℕ // n ≠ 0} ↦
      Checked.inv (n : ℝ) (Nat.cast_ne_zero.mpr n.2).isUnit • ∑ i ∈ range (n : ℕ), u i)
      (comap Subtype.val atTop) (𝓝 l) := by
  rw [← tendsto_sub_nhds_zero_iff, ← isLittleO_one_iff ℝ]
  have hs := (Asymptotics.isLittleO_sum_range_of_tendsto_zero
    (tendsto_sub_nhds_zero_iff.2 h)).comp_tendsto
      (tendsto_comap : Tendsto (Subtype.val : {n : ℕ // n ≠ 0} → ℕ)
        (comap Subtype.val atTop) atTop)
  apply ((isBigO_refl (fun n : {n : ℕ // n ≠ 0} ↦
    Checked.inv (n : ℝ) (Nat.cast_ne_zero.mpr n.2).isUnit) _).smul_isLittleO hs).congr' ?_ ?_
  · filter_upwards with n
    simp only [Function.comp_def, smul_sub, sum_sub_distrib, sum_const, card_range,
      sub_right_inj]
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀, one_smul]
  · filter_upwards with n
    simp only [Function.comp_def, smul_eq_mul, inv_mul_cancel₀]

/-- The Cesaro average of a converging sequence converges to the same limit, on positive indices. -/
theorem Filter.Tendsto.cesaro {u : ℕ → ℝ} {l : ℝ} (h : Tendsto u atTop (𝓝 l)) :
    Tendsto (fun n : {n : ℕ // n ≠ 0} ↦
      Checked.inv (n : ℝ) (Nat.cast_ne_zero.mpr n.2).isUnit * ∑ i ∈ range (n : ℕ), u i)
      (comap Subtype.val atTop) (𝓝 l) :=
  h.cesaro_smul

end Real

section NormedLinearOrderedField

variable {R : Type*} [NormedField R] [LinearOrder R] [IsStrictOrderedRing R]
  [OrderTopology R] [FloorRing R]

theorem Asymptotics.isEquivalent_nat_floor :
    (fun (x : R) ↦ ↑⌊x⌋₊) ~[atTop] (fun x ↦ x) :=
  isEquivalent_of_tendsto_one
    (Eventually.of_forall fun x hx ↦ by simp [hx]) tendsto_nat_floor_div_atTop

theorem Asymptotics.isEquivalent_nat_ceil :
    (fun (x : R) ↦ ↑⌈x⌉₊) ~[atTop] (fun x ↦ x) :=
  isEquivalent_of_tendsto_one
    (Eventually.of_forall fun x hx ↦ by simp [hx]) tendsto_nat_ceil_div_atTop

end NormedLinearOrderedField

section boundedRange

/-!
## Bounded Range versus `IsBigO` Asymptotics

For a continuous function `f` into a seminormed space, having bounded range is equivalent to being
`O(1)` along the cocompact filter (`Continuous.isBounded_range_iff_isBigO`). On an unbounded linear
order whose order topology has compact intervals, this means being `O(1)` along both `atTop` and
`atBot` (`Continuous.isBounded_range_iff_isBigO_atTop_atBot`). For an even function a single `O(1)`
bound along `atTop` already suffices (`Continuous.isBounded_range_iff_isBigO_atTop_of_even`).
-/

variable
  {E : Type*} [SeminormedAddCommGroup E]
  {D : Type*} [TopologicalSpace D]
  {β : Type*} [TopologicalSpace β] [LinearOrder β] [OrderClosedTopology β] [CompactIccSpace β]
    [NoMaxOrder β] [NoMinOrder β]

/--
A continuous function `f` has bounded range if and only if it is `O(1)` with respect to the
cocompact filter.
-/
theorem Continuous.isBounded_range_iff_isBigO {f : D → E} (hf : Continuous f) :
    IsBounded (range f) ↔ f =O[cocompact D] (1 : D → ℝ) := by
  constructor <;> intro h
  · rw [isBounded_iff_forall_norm_le] at h
    obtain ⟨c, hc⟩ := h
    simp only [Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff] at hc
    rw [isBigO_iff]
    use c
    apply Eventually.of_forall
    simpa using hc
  · simp_rw [isBigO_iff, Filter.Eventually, Filter.mem_cocompact] at h
    simp only [Pi.one_apply, norm_one, mul_one] at h
    obtain ⟨c, t, hcompact, h⟩ := h
    rw [← Set.image_union_image_compl_eq_range (s := t)]
    apply IsBounded.union
    · apply (IsCompact.image hcompact hf).isBounded
    · rw [isBounded_iff_forall_norm_le]
      refine ⟨c, fun x hx ↦ ?_⟩
      rw [Set.mem_image] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      simpa using mem_of_mem_of_subset hy h

/--
A continuous function `f` on an unbounded linear order with compact intervals has bounded range if
and only if it is `O(1)` at both `atTop` and `atBot`.
-/
theorem Continuous.isBounded_range_iff_isBigO_atTop_atBot {f : β → E} (hf : Continuous f) :
    IsBounded (range f) ↔ f =O[atTop] (1 : β → ℝ) ∧ f =O[atBot] (1 : β → ℝ) := by
  rw [hf.isBounded_range_iff_isBigO, cocompact_eq_atBot_atTop, isBigO_sup, and_comm]

/-- A continuous even function has bounded range if and only if `f =O[atTop] 1`. -/
theorem Continuous.isBounded_range_iff_isBigO_atTop_of_even [AddCommGroup β] [IsOrderedAddMonoid β]
    {f : β → E} (hf : Continuous f) (heven : Function.Even f) :
    IsBounded (range f) ↔ f =O[atTop] (1 : β → ℝ) :=
  ⟨fun h ↦ (hf.isBounded_range_iff_isBigO_atTop_atBot.mp h).1,
   fun h ↦ hf.isBounded_range_iff_isBigO_atTop_atBot.mpr
     ⟨h, by simpa only [← neg_atTop, ← Filter.map_neg, isBigO_map, Function.comp_def, heven.eq]⟩⟩

end boundedRange
