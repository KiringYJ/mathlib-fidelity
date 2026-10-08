/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler, Stefan Kebekus
-/
module

public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.Algebra.Order.WithTop.Untop0

/-!
# Orders of Meromorphic Functions

This file defines the order of a meromorphic function `f` at a point `z₀`, as an element of
`ℤ ∪ {∞}`.

We characterize the order being `< 0`, or `= 0`, or `> 0`, as the convergence of the function
to infinity, resp. a nonzero constant, resp. zero.

## TODO

Uniformize API between analytic and meromorphic functions
-/

@[expose] public section

open Filter Set WithTop.LinearOrderedAddCommGroup
open scoped Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {R : Type*} [NormedRing R] [NoZeroDivisors R]
  [Module R E] [IsBoundedSMul R E] [Module.IsTorsionFree R E]
  {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  {f f₁ f₂ : 𝕜 → E} {x : 𝕜}

/-!
## Order at a Point: Definition and Characterization
-/

/-- The order of a meromorphic function `f` at `z₀`, as an element of `ℤ ∪ {∞}`.

The order is defined to be `∞` if `f` is identically 0 on a neighbourhood of `z₀`, and otherwise the
unique `n` such that `f` can locally be written as `f z = (z - z₀) ^ n • g z`, where `g` is analytic
and does not vanish at `z₀`. See `meromorphicOrderAt_eq_top_iff` and
`meromorphicOrderAt_eq_int_iff` for these equivalences.

The order is only defined for a function that is meromorphic at `x`: the proof `hf` of meromorphy
is an argument of the definition, which `fun_prop` supplies by default. There is no value for a
function that is not meromorphic at `x`. -/
noncomputable def meromorphicOrderAt (f : 𝕜 → E) (x : 𝕜)
    (hf : MeromorphicAt f x := by fun_prop_default) : WithTop ℤ :=
  ((analyticOrderAt (fun z ↦ (z - x) ^ hf.choose • f z) x hf.choose_spec).map (↑· : ℕ → ℤ)) -
    hf.choose

/-- The order of a meromorphic function `f` at a `z₀` is infinity iff `f` vanishes locally around
`z₀`. -/
lemma meromorphicOrderAt_eq_top_iff (hf : MeromorphicAt f x) :
    meromorphicOrderAt f x hf = ⊤ ↔ ∀ᶠ z in 𝓝[≠] x, f z = 0 := by
  simp only [meromorphicOrderAt, sub_eq_top_iff, ENat.map_eq_top_iff, WithTop.natCast_ne_top,
    or_false]
  by_cases h : analyticOrderAt (fun z ↦ (z - x) ^ hf.choose • f z) x hf.choose_spec = ⊤
  · simp only [h, eventually_nhdsWithin_iff, mem_compl_iff, mem_singleton_iff, true_iff]
    rw [analyticOrderAt_eq_top] at h
    filter_upwards [h] with z hf hz
    rwa [smul_eq_zero_iff_right <| pow_ne_zero _ (sub_ne_zero.mpr hz)] at hf
  · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp h
    simp only [← hm, ENat.natCast_ne_top, false_iff]
    contrapose h
    rw [analyticOrderAt_eq_top]
    rw [← hf.choose_spec.frequently_eq_iff_eventually_eq analyticAt_const]
    apply Eventually.frequently
    filter_upwards [h] with z hfz
    rw [hfz, smul_zero]

lemma eventuallyConst_nhdsNE_iff_meromorphicOrderAt_sub_eq_top (hf : MeromorphicAt f x) :
    EventuallyConst f (𝓝[≠] x) ↔
      ∃ c, meromorphicOrderAt (f · - c) x (hf.fun_sub (.const c x)) = ⊤ := by
  simp only [eventuallyConst_iff_exists_eventuallyEq, meromorphicOrderAt_eq_top_iff,
    sub_eq_zero, EventuallyEq]

/-- The order of a meromorphic function `f` at `z₀` equals an integer `n` iff `f` can locally be
written as `f z = (z - z₀) ^ n • g z`, where `g` is analytic and does not vanish at `z₀`. -/
lemma meromorphicOrderAt_eq_int_iff {n : ℤ} (hf : MeromorphicAt f x) :
    meromorphicOrderAt f x hf = n ↔
      ∃ g : 𝕜 → E, AnalyticAt 𝕜 g x ∧ g x ≠ 0 ∧ ∀ᶠ z in 𝓝[≠] x, f z = (z - x) ^ n • g z := by
  simp only [meromorphicOrderAt]
  by_cases h : analyticOrderAt (fun z ↦ (z - x) ^ hf.choose • f z) x hf.choose_spec = ⊤
  · rw [h, ENat.map_top, ← WithTop.coe_natCast, top_sub,
      eq_false_intro WithTop.top_ne_coe, false_iff]
    rw [analyticOrderAt_eq_top] at h
    refine fun ⟨g, hg_an, hg_ne, hg_eq⟩ ↦ hg_ne ?_
    apply EventuallyEq.eq_of_nhds
    rw [EventuallyEq, ← AnalyticAt.frequently_eq_iff_eventually_eq hg_an analyticAt_const]
    apply Eventually.frequently
    rw [eventually_nhdsWithin_iff] at hg_eq ⊢
    filter_upwards [h, hg_eq] with z hfz hfz_eq hz
    rwa [hfz_eq hz, ← mul_smul, smul_eq_zero_iff_right] at hfz
    exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hz)) (zpow_ne_zero _ (sub_ne_zero.mpr hz))
  · obtain ⟨m, h⟩ := ENat.ne_top_iff_exists.mp h
    rw [← h, ENat.map_natCast, ← WithTop.coe_natCast, ← coe_sub, WithTop.coe_inj]
    obtain ⟨g, hg_an, hg_ne, hg_eq⟩ := hf.choose_spec.analyticOrderAt_eq_natCast.mp h.symm
    replace hg_eq : ∀ᶠ (z : 𝕜) in 𝓝[≠] x, f z = (z - x) ^ (↑m - ↑hf.choose : ℤ) • g z := by
      rw [eventually_nhdsWithin_iff]
      filter_upwards [hg_eq] with z hg_eq hz
      rwa [← smul_right_inj <| zpow_ne_zero _ (sub_ne_zero.mpr hz), ← mul_smul,
        ← zpow_add₀ (sub_ne_zero.mpr hz), ← add_sub_assoc, add_sub_cancel_left, zpow_natCast,
        zpow_natCast]
    exact ⟨fun h ↦ ⟨g, hg_an, hg_ne, h ▸ hg_eq⟩,
      AnalyticAt.unique_eventuallyEq_zpow_smul_nonzero ⟨g, hg_an, hg_ne, hg_eq⟩⟩

/--
The order of a meromorphic function `f` at `z₀` is finite iff `f` can locally be
written as `f z = (z - z₀) ^ order • g z`, where `g` is analytic and does not
vanish at `z₀`.
-/
theorem meromorphicOrderAt_ne_top_iff {f : 𝕜 → E} {z₀ : 𝕜} (hf : MeromorphicAt f z₀) :
    meromorphicOrderAt f z₀ hf ≠ ⊤ ↔ ∃ (g : 𝕜 → E), AnalyticAt 𝕜 g z₀ ∧ g z₀ ≠ 0 ∧
      f =ᶠ[𝓝[≠] z₀] fun z ↦ (z - z₀) ^ ((meromorphicOrderAt f z₀ hf).untop₀) • g z :=
  ⟨fun h ↦ (meromorphicOrderAt_eq_int_iff hf).1 (WithTop.coe_untop₀_of_ne_top h).symm,
    fun h ↦ Option.ne_none_iff_exists'.2
      ⟨(meromorphicOrderAt f z₀ hf).untopD 0, (meromorphicOrderAt_eq_int_iff hf).2 h⟩⟩

/--
The order of a meromorphic function `f` at `z₀` is finite iff `f` does not have
any zeros in a sufficiently small neighborhood of `z₀`.
-/
theorem meromorphicOrderAt_ne_top_iff_eventually_ne_zero {f : 𝕜 → E} (hf : MeromorphicAt f x) :
    meromorphicOrderAt f x hf ≠ ⊤ ↔ ∀ᶠ x in 𝓝[≠] x, f x ≠ 0 := by
  constructor
  · intro h
    obtain ⟨g, h₁g, h₂g, h₃g⟩ := (meromorphicOrderAt_ne_top_iff hf).1 h
    filter_upwards [h₃g, self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
      ((h₁g.continuousAt.ne_iff_eventually_ne continuousAt_const).mp h₂g)]
    simp_all [zpow_ne_zero, sub_ne_zero]
  · intro h h₀
    rw [meromorphicOrderAt_eq_top_iff hf] at h₀
    obtain ⟨z, hz, hz'⟩ := (h.and h₀).exists
    exact hz hz'

/-- The order of a meromorphic function `f` at `z₀` is finite iff `f` has multiplicative inverse
in a sufficiently small neighborhood of `z₀`. -/
theorem meromorphicOrderAt_ne_top_iff_mul_inv_eventuallyEq {f : 𝕜 → 𝕜'} (hf : MeromorphicAt f x) :
    meromorphicOrderAt f x hf ≠ ⊤ ↔ f * f⁻¹ =ᶠ[𝓝[≠] x] 1 := by
  rw [meromorphicOrderAt_ne_top_iff_eventually_ne_zero hf]
  exact eventually_congr (.of_forall (by aesop))

/--
A function meromorphic on `U`, with meromorphic order nowhere `⊤`, is nonvanishing away from a
codiscrete subset of `U`.
-/
theorem MeromorphicOn.eventually_codiscreteWithin_apply_ne_zero {U : Set 𝕜} {f : 𝕜 → E}
    (hf : MeromorphicOn f U) (h'f : ∀ x (hx : x ∈ U), meromorphicOrderAt f x (hf x hx) ≠ ⊤) :
    ∀ᶠ x in codiscreteWithin U, f x ≠ 0 := by
  simp_rw [eventually_iff, mem_codiscreteWithin, disjoint_principal_right]
  intro x hx
  filter_upwards [(meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hf x hx)).1 (h'f x hx)]
    with y hy
  simp [hy]

/-- If the order of a meromorphic function is negative, then this function converges to infinity
at this point. See also the iff version `tendsto_cobounded_iff_meromorphicOrderAt_neg`. -/
lemma tendsto_cobounded_of_meromorphicOrderAt_neg (hf : MeromorphicAt f x)
    (ho : meromorphicOrderAt f x hf < 0) :
    Tendsto f (𝓝[≠] x) (Bornology.cobounded E) := by
  simp only [← tendsto_norm_atTop_iff_cobounded]
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp ho.ne_top
  have m_neg : m < 0 := by simpa [← hm] using ho
  rcases (meromorphicOrderAt_eq_int_iff hf).1 hm.symm with ⟨g, g_an, gx, hg⟩
  have A : Tendsto (fun z ↦ ‖(z - x) ^ m • g z‖) (𝓝[≠] x) atTop := by
    simp only [norm_smul]
    apply Filter.Tendsto.atTop_mul_pos (C := ‖g x‖) (by simp [gx]) _
      g_an.continuousAt.continuousWithinAt.tendsto.norm
    have : Tendsto (fun z ↦ z - x) (𝓝[≠] x) (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : ContinuousWithinAt (fun z ↦ z - x) {x}ᶜ x := by fun_prop
        simpa using this.tendsto
      · filter_upwards [self_mem_nhdsWithin] with y hy
        simpa [sub_eq_zero] using hy
    exact (tendsto_norm_cobounded_atTop.comp (tendsto_zpow_nhdsNE_zero_cobounded m_neg)).comp this
  apply A.congr'
  filter_upwards [hg] with z hz using by simp [hz]

/-- If the order of a meromorphic function is zero, then this function converges to a nonzero
limit at this point. See also the iff version `tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero`. -/
lemma tendsto_ne_zero_of_meromorphicOrderAt_eq_zero
    (hf : MeromorphicAt f x) (ho : meromorphicOrderAt f x hf = 0) :
    ∃ c ≠ 0, Tendsto f (𝓝[≠] x) (𝓝 c) := by
  rcases (meromorphicOrderAt_eq_int_iff hf).1 ho with ⟨g, g_an, gx, hg⟩
  refine ⟨g x, gx, ?_⟩
  apply g_an.continuousAt.continuousWithinAt.tendsto.congr'
  filter_upwards [hg] with y hy using by simp [hy]

/-- If the order of a meromorphic function is positive, then this function converges to zero
at this point. See also the iff version `tendsto_zero_iff_meromorphicOrderAt_pos`. -/
lemma tendsto_zero_of_meromorphicOrderAt_pos (hf : MeromorphicAt f x)
    (ho : 0 < meromorphicOrderAt f x hf) :
    Tendsto f (𝓝[≠] x) (𝓝 0) := by
  cases h'o : meromorphicOrderAt f x hf with
  | top =>
    apply tendsto_const_nhds.congr'
    filter_upwards [(meromorphicOrderAt_eq_top_iff hf).1 h'o] with y hy using hy.symm
  | coe n =>
    rcases (meromorphicOrderAt_eq_int_iff hf).1 h'o with ⟨g, g_an, gx, hg⟩
    lift n to ℕ using by simpa [h'o] using ho.le
    have : (0 : E) = (x - x) ^ n • g x := by
      have : 0 < n := by simpa [h'o] using ho
      simp [zero_pow_eq_zero.2 this.ne']
    rw [this]
    have : ContinuousAt (fun z ↦ (z - x) ^ n • g z) x := by fun_prop
    apply this.continuousWithinAt.tendsto.congr'
    filter_upwards [hg] with y hy using by simp [hy]

/-- If the order of a meromorphic function is nonnegative, then this function converges
at this point. See also the iff version `tendsto_nhds_iff_meromorphicOrderAt_nonneg`. -/
lemma tendsto_nhds_of_meromorphicOrderAt_nonneg
    (hf : MeromorphicAt f x) (ho : 0 ≤ meromorphicOrderAt f x hf) :
    ∃ c, Tendsto f (𝓝[≠] x) (𝓝 c) := by
  rcases ho.eq_or_lt with ho | ho
  · rcases tendsto_ne_zero_of_meromorphicOrderAt_eq_zero hf ho.symm with ⟨c, -, hc⟩
    exact ⟨c, hc⟩
  · exact ⟨0, tendsto_zero_of_meromorphicOrderAt_pos hf ho⟩

/-- A meromorphic function converges to infinity iff its order is negative. -/
lemma tendsto_cobounded_iff_meromorphicOrderAt_neg (hf : MeromorphicAt f x) :
    Tendsto f (𝓝[≠] x) (Bornology.cobounded E) ↔ meromorphicOrderAt f x hf < 0 := by
  rcases lt_or_ge (meromorphicOrderAt f x hf) 0 with ho | ho
  · simp [ho, tendsto_cobounded_of_meromorphicOrderAt_neg hf]
  · simp only [lt_iff_not_ge, ho, not_true_eq_false, iff_false, ← tendsto_norm_atTop_iff_cobounded]
    obtain ⟨c, hc⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg hf ho
    exact not_tendsto_atTop_of_tendsto_nhds hc.norm

/-- A meromorphic function converges to a limit iff its order is nonnegative. -/
lemma tendsto_nhds_iff_meromorphicOrderAt_nonneg (hf : MeromorphicAt f x) :
    (∃ c, Tendsto f (𝓝[≠] x) (𝓝 c)) ↔ 0 ≤ meromorphicOrderAt f x hf := by
  rcases lt_or_ge (meromorphicOrderAt f x hf) 0 with ho | ho
  · simp only [← not_lt, ho, not_true_eq_false, iff_false, not_exists]
    intro c hc
    apply not_tendsto_atTop_of_tendsto_nhds hc.norm
    rw [tendsto_norm_atTop_iff_cobounded]
    exact tendsto_cobounded_of_meromorphicOrderAt_neg hf ho
  · simp [ho, tendsto_nhds_of_meromorphicOrderAt_nonneg hf ho]

/-- A meromorphic function converges to a nonzero limit iff its order is zero. -/
lemma tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero (hf : MeromorphicAt f x) :
    (∃ c ≠ 0, Tendsto f (𝓝[≠] x) (𝓝 c)) ↔ meromorphicOrderAt f x hf = 0 := by
  rcases eq_or_ne (meromorphicOrderAt f x hf) 0 with ho | ho
  · simp [ho, tendsto_ne_zero_of_meromorphicOrderAt_eq_zero hf ho]
  simp only [ne_eq, ho, iff_false, not_exists, not_and]
  intro c c_ne hc
  rcases ho.lt_or_gt with ho | ho
  · apply not_tendsto_atTop_of_tendsto_nhds hc.norm
    rw [tendsto_norm_atTop_iff_cobounded]
    exact tendsto_cobounded_of_meromorphicOrderAt_neg hf ho
  · apply c_ne
    exact tendsto_nhds_unique hc (tendsto_zero_of_meromorphicOrderAt_pos hf ho)

/-- A meromorphic function converges to zero iff its order is positive. -/
lemma tendsto_zero_iff_meromorphicOrderAt_pos (hf : MeromorphicAt f x) :
    (Tendsto f (𝓝[≠] x) (𝓝 0)) ↔ 0 < meromorphicOrderAt f x hf := by
  rcases lt_or_ge 0 (meromorphicOrderAt f x hf) with ho | ho
  · simp [ho, tendsto_zero_of_meromorphicOrderAt_pos hf ho]
  simp only [← not_le, ho, not_true_eq_false, iff_false]
  intro hc
  rcases ho.eq_or_lt with ho | ho
  · obtain ⟨c, c_ne, h'c⟩ := tendsto_ne_zero_of_meromorphicOrderAt_eq_zero hf ho
    apply c_ne
    exact tendsto_nhds_unique h'c hc
  · apply not_tendsto_atTop_of_tendsto_nhds hc.norm
    rw [tendsto_norm_atTop_iff_cobounded]
    exact tendsto_cobounded_of_meromorphicOrderAt_neg hf ho

/-- Meromorphic functions that agree in a punctured neighborhood of `z₀` have the same order at
`z₀`. -/
theorem meromorphicOrderAt_congr (hf₁ : MeromorphicAt f₁ x) (hf₁₂ : f₁ =ᶠ[𝓝[≠] x] f₂) :
    meromorphicOrderAt f₁ x hf₁ = meromorphicOrderAt f₂ x (hf₁.congr hf₁₂) := by
  rw [eq_comm]
  cases h₁f₁ : meromorphicOrderAt f₁ x hf₁ with
  | top =>
    rw [meromorphicOrderAt_eq_top_iff] at h₁f₁ ⊢
    filter_upwards [hf₁₂, h₁f₁] using by grind
  | coe n =>
    obtain ⟨g, h₁g, h₂g, h₃g⟩ := (meromorphicOrderAt_eq_int_iff hf₁).1 h₁f₁
    rw [meromorphicOrderAt_eq_int_iff (hf₁.congr hf₁₂)]
    use g, h₁g, h₂g
    filter_upwards [hf₁₂, h₃g] using by grind

/-- Compatibility of notions of `order` for analytic and meromorphic functions. -/
lemma AnalyticAt.meromorphicOrderAt_eq (hf : AnalyticAt 𝕜 f x) :
    meromorphicOrderAt f x hf.meromorphicAt = (analyticOrderAt f x hf).map (↑) := by
  cases hn : analyticOrderAt f x hf
  · rw [ENat.map_top, meromorphicOrderAt_eq_top_iff]
    exact ((analyticOrderAt_eq_top hf).mp hn).filter_mono nhdsWithin_le_nhds
  · simp_rw [ENat.map_natCast, meromorphicOrderAt_eq_int_iff hf.meromorphicAt, zpow_natCast]
    rcases hf.analyticOrderAt_eq_natCast.mp hn with ⟨g, h1, h2, h3⟩
    exact ⟨g, h1, h2, h3.filter_mono nhdsWithin_le_nhds⟩

/--
When seen as meromorphic functions, analytic functions have nonnegative order.
-/
theorem AnalyticAt.meromorphicOrderAt_nonneg (hf : AnalyticAt 𝕜 f x) :
    0 ≤ meromorphicOrderAt f x hf.meromorphicAt := by
  simp [hf.meromorphicOrderAt_eq]

/-- A meromorphic function has non-negative order iff there exists an analytic extension. -/
theorem MeromorphicAt.meromorphicOrderAt_nonneg_iff
    (hf : MeromorphicAt f x) :
    0 ≤ meromorphicOrderAt f x hf ↔ ∃ g : 𝕜 → E, AnalyticAt 𝕜 g x ∧ f =ᶠ[𝓝[≠] x] g := by
  refine ⟨fun nneg ↦ ?_, fun ⟨g, hg₁, hg₂⟩ ↦ ?_⟩
  · cases h₀ : meromorphicOrderAt f x hf with
    | top => exact ⟨0, analyticAt_const, (meromorphicOrderAt_eq_top_iff hf).mp h₀⟩
    | coe n =>
      obtain ⟨g, hg, -, hfg⟩ := (meromorphicOrderAt_eq_int_iff hf).mp h₀
      refine ⟨fun z ↦ (z - x) ^ n • g z, ?_, hfg⟩
      exact (AnalyticAt.zpow_nonneg (by fun_prop) (by simpa [h₀] using nneg)).smul hg
  · rw [meromorphicOrderAt_congr hf hg₂]
    exact hg₁.meromorphicOrderAt_nonneg

/-- If a function is both meromorphic and continuous at a point, then it is analytic there. -/
protected theorem MeromorphicAt.analyticAt {f : 𝕜 → E} {x : 𝕜}
    (h : MeromorphicAt f x) (h' : ContinuousAt f x) :
    AnalyticAt 𝕜 f x := by
  cases ho : meromorphicOrderAt f x h with
  | top =>
    /- If the order is infinite, then `f` vanishes on a pointed neighborhood of `x`. By continuity,
    it also vanishes at `x`.-/
    have : AnalyticAt 𝕜 (fun _ ↦ (0 : E)) x := analyticAt_const
    apply this.congr
    rw [← ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE continuousAt_const h']
    filter_upwards [(meromorphicOrderAt_eq_top_iff h).1 ho] with y hy using by simp [hy]
  | coe n =>
    /- If the order is finite, then the order has to be nonnegative, as otherwise the norm of `f`
    would tend to infinity at `x`. Then the local expression of `f` coming from its meromorphicity
    shows that it coincides with an analytic function close to `x`, except maybe at `x`. By
    continuity of `f`, the two functions also coincide at `x`. -/
    rcases (meromorphicOrderAt_eq_int_iff h).1 ho with ⟨g, g_an, gx, hg⟩
    have : 0 ≤ meromorphicOrderAt f x h := by
      apply (tendsto_nhds_iff_meromorphicOrderAt_nonneg h).1
      exact ⟨f x, h'.continuousWithinAt.tendsto⟩
    lift n to ℕ using by simpa [ho] using this
    have A : ∀ᶠ (z : 𝕜) in 𝓝 x, (z - x) ^ n • g z = f z := by
      apply (ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE (by fun_prop) h').1
      filter_upwards [hg] with z hz using by simpa using hz.symm
    exact AnalyticAt.congr (by fun_prop) A

lemma AnalyticAt.of_meromorphicOrderAt_pos {f : 𝕜 → E} {x : 𝕜}
    (hm : MeromorphicAt f x) (h : 0 < meromorphicOrderAt f x hm) (hf : f x = 0) :
    AnalyticAt 𝕜 f x := by
  refine hm.analyticAt ?_
  rw [continuousAt_iff_punctured_nhds, hf]
  exact tendsto_zero_of_meromorphicOrderAt_pos hm h

/--
The order of a constant function is `⊤` if the constant is zero and `0` otherwise.
-/
theorem meromorphicOrderAt_const (z₀ : 𝕜) (e : E) [Decidable (e = 0)] :
    meromorphicOrderAt (fun _ ↦ e) z₀ = if e = 0 then ⊤ else (0 : WithTop ℤ) := by
  split_ifs with he
  · rw [meromorphicOrderAt_eq_top_iff]
    exact .of_forall fun _ ↦ he
  · exact (meromorphicOrderAt_eq_int_iff (.const e z₀)).2 ⟨fun _ ↦ e, by fun_prop, by simpa⟩

@[simp]
lemma meromorphicOrderAt_id : meromorphicOrderAt (𝕜 := 𝕜) id 0 = 1 := by
  simp [analyticAt_id.meromorphicOrderAt_eq]

/--
The order of a constant function is `⊤` if the constant is zero and `0` otherwise.
-/
theorem meromorphicOrderAt_const_intCast (z₀ : 𝕜) (n : ℤ) [Decidable ((n : 𝕜') = 0)]
    (hf : MeromorphicAt (n : 𝕜 → 𝕜') z₀ := .const (n : 𝕜') z₀) :
    meromorphicOrderAt (n : 𝕜 → 𝕜') z₀ hf = if (n : 𝕜') = 0 then ⊤ else (0 : WithTop ℤ) :=
  meromorphicOrderAt_const z₀ (n : 𝕜')

/--
The order of a constant function is `⊤` if the constant is zero and `0` otherwise.
-/
theorem meromorphicOrderAt_const_natCast (z₀ : 𝕜) (n : ℕ) [Decidable ((n : 𝕜') = 0)]
    (hf : MeromorphicAt (n : 𝕜 → 𝕜') z₀ := .const (n : 𝕜') z₀) :
    meromorphicOrderAt (n : 𝕜 → 𝕜') z₀ hf = if (n : 𝕜') = 0 then ⊤ else (0 : WithTop ℤ) :=
  meromorphicOrderAt_const z₀ (n : 𝕜')

/--
The order of a constant function is `⊤` if the constant is zero and `0` otherwise.
-/
@[simp] theorem meromorphicOrderAt_const_ofNat (z₀ : 𝕜) (n : ℕ) [Decidable ((n : 𝕜') = 0)]
    (hf : MeromorphicAt (ofNat(n) : 𝕜 → 𝕜') z₀) :
    meromorphicOrderAt (ofNat(n) : 𝕜 → 𝕜') z₀ hf =
      if (n : 𝕜') = 0 then ⊤ else (0 : WithTop ℤ) := by
  convert! meromorphicOrderAt_const z₀ (n : 𝕜')
  simp [Semiring.toGrindSemiring_ofNat 𝕜' n]

/-- The order of `(· - x) ^ n` at `x` is `n`. -/
@[simp, to_fun] theorem meromorphicOrderAt_zpow_id_sub_const {n : ℤ} :
    meromorphicOrderAt ((· - x) ^ n) x = n := by
  rw [meromorphicOrderAt_eq_int_iff]
  exact ⟨fun z ↦ 1, by fun_prop, one_ne_zero, by aesop⟩

/-- The order of `(· - x) ^ n` at `x` is `n`. -/
@[simp, to_fun] theorem meromorphicOrderAt_pow_id_sub_const {n : ℕ} :
    meromorphicOrderAt ((· - x) ^ n) x = n := by
  convert! meromorphicOrderAt_zpow_id_sub_const
  simp only [zpow_natCast]

/-- The order of `· - x` at `x` is `1`. -/
@[simp] theorem meromorphicOrderAt_id_sub_const :
    meromorphicOrderAt (· - x) x = 1 := by
  rw [← WithTop.coe_one, meromorphicOrderAt_eq_int_iff]
  exact ⟨fun _ ↦ 1, by fun_prop, one_ne_zero, by simp⟩

/-!
## Order at a Point: Behaviour under Ring Operations

We establish additivity of the order under multiplication and taking powers.
-/

/-- The order of a function `f` equals the order of `-f`. -/
theorem meromorphicOrderAt_neg {f : 𝕜 → E} (hf : MeromorphicAt f x) :
    meromorphicOrderAt f x hf = meromorphicOrderAt (-f) x hf.neg := by
  by_cases h₂ : meromorphicOrderAt f x hf = ⊤
  · rw [h₂, eq_comm, meromorphicOrderAt_eq_top_iff]
    rw [meromorphicOrderAt_eq_top_iff] at h₂
    filter_upwards [h₂] with z hz
    simp [hz]
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp h₂
  obtain ⟨g, hg_an, hg_ne, hg_eq⟩ := (meromorphicOrderAt_eq_int_iff hf).1 hn.symm
  rw [← hn, eq_comm, meromorphicOrderAt_eq_int_iff hf.neg]
  refine ⟨-g, hg_an.neg, by simpa using hg_ne, ?_⟩
  filter_upwards [hg_eq] with z hz
  simp [hz]

/-- The order of a function `f` equals the order of `-f`. -/
theorem meromorphicOrderAt_fun_neg {f : 𝕜 → E} (hf : MeromorphicAt f x) :
    meromorphicOrderAt f x hf = meromorphicOrderAt (fun z ↦ -f z) x hf.fun_neg :=
  meromorphicOrderAt_neg hf

/-- The order is additive when multiplying scalar-valued and vector-valued meromorphic functions. -/
@[to_fun] theorem meromorphicOrderAt_smul [NormedAlgebra 𝕜 R] [IsScalarTower 𝕜 R E]
    {f : 𝕜 → R} {g : 𝕜 → E} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    meromorphicOrderAt (f • g) x (hf.smul hg) =
      meromorphicOrderAt f x hf + meromorphicOrderAt g x hg := by
  -- Trivial cases: one of the functions vanishes around z₀
  cases h₂f : meromorphicOrderAt f x hf with
  | top =>
    simp only [top_add, meromorphicOrderAt_eq_top_iff] at h₂f ⊢
    filter_upwards [h₂f] with z hz using by simp [hz]
  | coe m =>
    cases h₂g : meromorphicOrderAt g x hg with
    | top =>
      simp only [add_top, meromorphicOrderAt_eq_top_iff] at h₂g ⊢
      filter_upwards [h₂g] with z hz using by simp [hz]
    | coe n => -- Non-trivial case: both functions do not vanish around z₀
      rw [← WithTop.coe_add, meromorphicOrderAt_eq_int_iff (hf.smul hg)]
      obtain ⟨F, h₁F, h₂F, h₃F⟩ := (meromorphicOrderAt_eq_int_iff hf).1 h₂f
      obtain ⟨G, h₁G, h₂G, h₃G⟩ := (meromorphicOrderAt_eq_int_iff hg).1 h₂g
      use F • G, h₁F.smul h₁G, by simp [h₂F, h₂G]
      filter_upwards [self_mem_nhdsWithin, h₃F, h₃G] with a ha hfa hga
      simp [hfa, hga, smul_comm (F a), zpow_add₀ (sub_ne_zero.mpr ha), mul_smul]

/-- The order is additive when multiplying meromorphic functions. -/
@[to_fun] theorem meromorphicOrderAt_mul {f g : 𝕜 → 𝕜'} (hf : MeromorphicAt f x)
    (hg : MeromorphicAt g x) :
    meromorphicOrderAt (f * g) x (hf.mul hg) =
      meromorphicOrderAt f x hf + meromorphicOrderAt g x hg :=
  meromorphicOrderAt_smul hf hg

/--
The order is additive in products of meromorphic functions: if the factor `f i` has order `n i` for
every `i ∈ s`, then the product has order `∑ i ∈ s, n i`.
-/
theorem meromorphicOrderAt_prod {x : 𝕜} {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → 𝕜'}
    {n : ι → WithTop ℤ} (hf : ∀ i ∈ s, MeromorphicAt (f i) x)
    (hn : ∀ i (hi : i ∈ s), meromorphicOrderAt (f i) x (hf i hi) = n i) :
    meromorphicOrderAt (∏ i ∈ s, f i) x (MeromorphicAt.prod hf) = ∑ i ∈ s, n i := by
  classical
  induction s using Finset.induction with
  | empty =>
    rw [Finset.sum_empty, ← WithTop.coe_zero, meromorphicOrderAt_eq_int_iff]
    exact ⟨1, analyticAt_const, by simp⟩
  | insert a s ha hs =>
    have hfa : MeromorphicAt (f a) x := hf a (Finset.mem_insert_self a s)
    have hfs : ∀ i ∈ s, MeromorphicAt (f i) x := fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)
    have h₁ : meromorphicOrderAt (∏ i ∈ insert a s, f i) x (MeromorphicAt.prod hf) =
        meromorphicOrderAt (f a * ∏ i ∈ s, f i) x (hfa.mul (MeromorphicAt.prod hfs)) :=
      meromorphicOrderAt_congr (MeromorphicAt.prod hf) (.of_eq (Finset.prod_insert ha))
    rw [h₁, meromorphicOrderAt_mul hfa (MeromorphicAt.prod hfs), Finset.sum_insert ha,
      hs hfs (fun i hi ↦ hn i (Finset.mem_insert_of_mem hi)), hn a (Finset.mem_insert_self a s)]

/--
The order is additive in products of meromorphic functions: if the factor `f i` has order `n i` for
every `i ∈ s`, then the product has order `∑ i ∈ s, n i`.
-/
theorem meromorphicOrderAt_fun_prod {x : 𝕜} {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → 𝕜'}
    {n : ι → WithTop ℤ} (hf : ∀ i ∈ s, MeromorphicAt (f i) x)
    (hn : ∀ i (hi : i ∈ s), meromorphicOrderAt (f i) x (hf i hi) = n i) :
    meromorphicOrderAt (fun a ↦ ∏ i ∈ s, f i a) x (MeromorphicAt.fun_prod hf) = ∑ i ∈ s, n i := by
  convert! meromorphicOrderAt_prod hf hn
  exact (Finset.prod_apply _ s f).symm

/--
A finite product of meromorphic functions, none of which vanishes locally, does not vanish locally.
-/
lemma meromorphicOrderAt_prod_ne_top {x : 𝕜} {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → 𝕜'}
    (hf : ∀ i ∈ s, MeromorphicAt (f i) x)
    (h : ∀ i (hi : i ∈ s), meromorphicOrderAt (f i) x (hf i hi) ≠ ⊤) :
    meromorphicOrderAt (∏ i ∈ s, f i) x (MeromorphicAt.prod hf) ≠ ⊤ := by
  classical
  intro h₀
  rw [meromorphicOrderAt_prod hf (n := fun i ↦ if hi : i ∈ s then
    meromorphicOrderAt (f i) x (hf i hi) else 0) fun i hi ↦ by simp [hi],
    WithTop.sum_eq_top] at h₀
  obtain ⟨i, hi, hi'⟩ := h₀
  exact h i hi (by simpa [hi] using hi')

/--
A finprod of functions that do not vanish locally does not vanish locally.
-/
lemma meromorphicOrderAt_finprod_ne_top {x : 𝕜} {ι : Type*} {F : ι → 𝕜 → 𝕜}
    (h₁ : ∀ c, MeromorphicAt (F c) x) (h₂ : ∀ c, meromorphicOrderAt (F c) x (h₁ c) ≠ ⊤) :
    meromorphicOrderAt (∏ᶠ c, F c) x (MeromorphicAt.finprod h₁) ≠ ⊤ := by
  classical
  by_cases hF : F.HasFiniteMulSupport
  · obtain ⟨t, ht⟩ : ∃ t : Finset ι, ∏ᶠ c, F c = ∏ c ∈ t, F c := ⟨_, finprod_eq_prod F hF⟩
    rw [meromorphicOrderAt_congr (MeromorphicAt.finprod h₁) (.of_eq ht)]
    exact meromorphicOrderAt_prod_ne_top (fun c _ ↦ h₁ c) fun c _ ↦ h₂ c
  · rw [meromorphicOrderAt_ne_top_iff_eventually_ne_zero]
    simp [finprod_of_not_hasFiniteMulSupport hF]

/-- The order multiplies by `n` when taking a meromorphic function to its `n`th power. -/
@[to_fun] theorem meromorphicOrderAt_pow {f : 𝕜 → 𝕜'} {x : 𝕜} (hf : MeromorphicAt f x) {n : ℕ} :
    meromorphicOrderAt (f ^ n) x (hf.pow n) = n * meromorphicOrderAt f x hf := by
  induction n
  case zero =>
    simp only [CharP.cast_eq_zero, zero_mul]
    rw [← WithTop.coe_zero, meromorphicOrderAt_eq_int_iff]
    exact ⟨1, analyticAt_const, by simp⟩
  case succ n hn =>
    have h₁ : meromorphicOrderAt (f ^ (n + 1)) x (hf.pow (n + 1)) =
        meromorphicOrderAt (f ^ n * f) x ((hf.pow n).mul hf) :=
      meromorphicOrderAt_congr (hf.pow (n + 1)) (.of_eq (pow_succ f n))
    rw [h₁, meromorphicOrderAt_mul (hf.pow n) hf, hn, Nat.cast_add, Nat.cast_one]
    cases meromorphicOrderAt f x hf
    · aesop
    · norm_cast
      simp only [Nat.cast_add, Nat.cast_one]
      ring

/-- The order multiplies by `n` when taking a meromorphic function to its `n`th power. -/
@[to_fun] theorem meromorphicOrderAt_zpow {f : 𝕜 → 𝕜'} {x : 𝕜} (hf : MeromorphicAt f x) {n : ℤ} :
    meromorphicOrderAt (f ^ n) x (hf.zpow n) = n * meromorphicOrderAt f x hf := by
  -- Trivial case: n = 0
  by_cases hn : n = 0
  · subst hn
    rw [WithTop.coe_zero, zero_mul, ← WithTop.coe_zero, meromorphicOrderAt_eq_int_iff]
    exact ⟨1, analyticAt_const, by simp⟩
  -- Trivial case: f locally zero
  by_cases h : meromorphicOrderAt f x hf = ⊤
  · rw [h, WithTop.mul_top (by simpa using hn), meromorphicOrderAt_eq_top_iff]
    rw [meromorphicOrderAt_eq_top_iff] at h
    filter_upwards [h]
    intro y hy
    simp [hy, zero_zpow n hn]
  -- General case
  obtain ⟨g, h₁g, h₂g, h₃g⟩ := (meromorphicOrderAt_ne_top_iff hf).1 h
  rw [← WithTop.coe_untop₀_of_ne_top h, ← WithTop.coe_mul,
    meromorphicOrderAt_eq_int_iff (hf.zpow n)]
  use g ^ n, h₁g.zpow h₂g
  constructor
  · simpa using zpow_ne_zero n h₂g
  · filter_upwards [h₃g]
    intro y hy
    rw [Pi.pow_apply, hy, Algebra.smul_def, Algebra.smul_def, mul_zpow, ← map_zpow₀]
    congr 1
    rw [mul_comm, zpow_mul]

/-- The order of the inverse is the negative of the order. -/
@[to_fun] theorem meromorphicOrderAt_inv {f : 𝕜 → 𝕜'} (hf : MeromorphicAt f x) :
    meromorphicOrderAt (f⁻¹) x hf.inv = -meromorphicOrderAt f x hf := by
  by_cases h₂f : meromorphicOrderAt f x hf = ⊤
  · rw [h₂f, LinearOrderedAddCommGroupWithTop.neg_top, meromorphicOrderAt_eq_top_iff]
    rw [meromorphicOrderAt_eq_top_iff] at h₂f
    filter_upwards [h₂f] with z hz
    simp [hz]
  lift meromorphicOrderAt f x hf to ℤ using h₂f with a ha
  apply (meromorphicOrderAt_eq_int_iff hf.inv).2
  obtain ⟨g, h₁g, h₂g, h₃g⟩ := (meromorphicOrderAt_eq_int_iff hf).1 ha.symm
  use g⁻¹, h₁g.inv h₂g, inv_eq_zero.not.2 h₂g
  rw [eventually_nhdsWithin_iff] at *
  filter_upwards [h₃g]
  intro _ h₁a h₂a
  simp [h₁a h₂a, Algebra.smul_def, mul_comm]

/--
The order of a quotient is the difference of the orders.
-/
@[to_fun] theorem meromorphicOrderAt_div {f g : 𝕜 → 𝕜'} (hf : MeromorphicAt f x)
    (hg : MeromorphicAt g x) :
    meromorphicOrderAt (f / g) x (hf.div hg) =
      meromorphicOrderAt f x hf - meromorphicOrderAt g x hg := by
  have h₁ : meromorphicOrderAt (f / g) x (hf.div hg) =
      meromorphicOrderAt (f * g⁻¹) x (hf.mul hg.inv) :=
    meromorphicOrderAt_congr (hf.div hg) (.of_eq (div_eq_mul_inv f g))
  rw [h₁, meromorphicOrderAt_mul hf hg.inv, meromorphicOrderAt_inv hg, sub_eq_add_neg]

/--
Adding a locally vanishing function does not change the order.
-/
theorem meromorphicOrderAt_add_of_top_left
    {f₁ f₂ : 𝕜 → E} {x : 𝕜} (hf₁ : MeromorphicAt f₁ x) (hf₂ : MeromorphicAt f₂ x)
    (h : meromorphicOrderAt f₁ x hf₁ = ⊤) :
    meromorphicOrderAt (f₁ + f₂) x (hf₁.add hf₂) = meromorphicOrderAt f₂ x hf₂ := by
  have hfe : f₁ + f₂ =ᶠ[𝓝[≠] x] f₂ := by
    filter_upwards [(meromorphicOrderAt_eq_top_iff hf₁).1 h] with z hz
    simp [hz]
  exact meromorphicOrderAt_congr (hf₁.add hf₂) hfe

/--
Adding a locally vanishing function does not change the order.
-/
theorem meromorphicOrderAt_add_of_top_right
    {f₁ f₂ : 𝕜 → E} {x : 𝕜} (hf₁ : MeromorphicAt f₁ x) (hf₂ : MeromorphicAt f₂ x)
    (h : meromorphicOrderAt f₂ x hf₂ = ⊤) :
    meromorphicOrderAt (f₁ + f₂) x (hf₁.add hf₂) = meromorphicOrderAt f₁ x hf₁ := by
  have hfe : f₁ + f₂ =ᶠ[𝓝[≠] x] f₁ := by
    filter_upwards [(meromorphicOrderAt_eq_top_iff hf₂).1 h] with z hz
    simp [hz]
  exact meromorphicOrderAt_congr (hf₁.add hf₂) hfe

/--
The order of a sum is at least the minimum of the orders of the summands.
-/
theorem meromorphicOrderAt_add (hf₁ : MeromorphicAt f₁ x) (hf₂ : MeromorphicAt f₂ x) :
    min (meromorphicOrderAt f₁ x hf₁) (meromorphicOrderAt f₂ x hf₂) ≤
      meromorphicOrderAt (f₁ + f₂) x (hf₁.add hf₂) := by
  -- Handle the trivial cases where one of the orders equals ⊤
  by_cases h₂f₁ : meromorphicOrderAt f₁ x hf₁ = ⊤
  · rw [h₂f₁, min_top_left]
    refine (meromorphicOrderAt_congr hf₂ ?_).le
    filter_upwards [(meromorphicOrderAt_eq_top_iff hf₁).1 h₂f₁]
    simp
  by_cases h₂f₂ : meromorphicOrderAt f₂ x hf₂ = ⊤
  · rw [h₂f₂, min_top_right]
    refine (meromorphicOrderAt_congr hf₁ ?_).le
    filter_upwards [(meromorphicOrderAt_eq_top_iff hf₂).1 h₂f₂]
    simp
  -- General case
  lift meromorphicOrderAt f₁ x hf₁ to ℤ using h₂f₁ with n₁ hn₁
  lift meromorphicOrderAt f₂ x hf₂ to ℤ using h₂f₂ with n₂ hn₂
  obtain ⟨g₁, h₁g₁, h₂g₁, h₃g₁⟩ := (meromorphicOrderAt_eq_int_iff hf₁).1 hn₁.symm
  obtain ⟨g₂, h₁g₂, h₂g₂, h₃g₂⟩ := (meromorphicOrderAt_eq_int_iff hf₂).1 hn₂.symm
  let n := min n₁ n₂
  let g := (fun z ↦ (z - x) ^ (n₁ - n)) • g₁ + (fun z ↦ (z - x) ^ (n₂ - n)) • g₂
  have h₁g : AnalyticAt 𝕜 g x := by
    apply AnalyticAt.add
    · apply (AnalyticAt.zpow_nonneg (by fun_prop) (sub_nonneg.2 (min_le_left n₁ n₂))).smul h₁g₁
    apply (AnalyticAt.zpow_nonneg (by fun_prop) (sub_nonneg.2 (min_le_right n₁ n₂))).smul h₁g₂
  have : f₁ + f₂ =ᶠ[𝓝[≠] x] ((· - x) ^ n) • g := by
    filter_upwards [h₃g₁, h₃g₂, self_mem_nhdsWithin]
    simp_all [g, ← smul_assoc, ← zpow_add', sub_ne_zero]
  have t₀ : MeromorphicAt ((· - x) ^ n) x := by fun_prop
  have t₁ : meromorphicOrderAt ((· - x) ^ n) x t₀ = n :=
    (meromorphicOrderAt_eq_int_iff t₀).2 ⟨1, analyticAt_const, by simp⟩
  rw [meromorphicOrderAt_congr (hf₁.add hf₂) this,
    meromorphicOrderAt_smul t₀ h₁g.meromorphicAt, t₁]
  exact le_add_of_nonneg_right h₁g.meromorphicOrderAt_nonneg

/--
Helper lemma for `meromorphicOrderAt_add_of_ne`.
-/
lemma meromorphicOrderAt_add_eq_left_of_lt (hf₁ : MeromorphicAt f₁ x) (hf₂ : MeromorphicAt f₂ x)
    (h : meromorphicOrderAt f₁ x hf₁ < meromorphicOrderAt f₂ x hf₂) :
    meromorphicOrderAt (f₁ + f₂) x (hf₁.add hf₂) = meromorphicOrderAt f₁ x hf₁ := by
  -- Trivial case: f₂ vanishes identically around z₀
  by_cases h₁f₂ : meromorphicOrderAt f₂ x hf₂ = ⊤
  · refine meromorphicOrderAt_congr (hf₁.add hf₂) ?_
    filter_upwards [(meromorphicOrderAt_eq_top_iff hf₂).1 h₁f₂]
    simp
  -- General case
  lift meromorphicOrderAt f₂ x hf₂ to ℤ using h₁f₂ with n₂ hn₂
  lift meromorphicOrderAt f₁ x hf₁ to ℤ using h.ne_top with n₁ hn₁
  obtain ⟨g₁, h₁g₁, h₂g₁, h₃g₁⟩ := (meromorphicOrderAt_eq_int_iff hf₁).1 hn₁.symm
  obtain ⟨g₂, h₁g₂, h₂g₂, h₃g₂⟩ := (meromorphicOrderAt_eq_int_iff hf₂).1 hn₂.symm
  rw [meromorphicOrderAt_eq_int_iff (hf₁.add hf₂)]
  refine ⟨g₁ + (· - x) ^ (n₂ - n₁) • g₂, ?_, ?_, ?_⟩
  · apply h₁g₁.add (AnalyticAt.smul _ h₁g₂)
    apply AnalyticAt.zpow_nonneg (by fun_prop)
      (sub_nonneg.2 (le_of_lt (WithTop.coe_lt_coe.1 h)))
  · simpa [zero_zpow _ <| sub_ne_zero.mpr (WithTop.coe_lt_coe.1 h).ne']
  · filter_upwards [h₃g₁, h₃g₂, self_mem_nhdsWithin]
    simp_all [smul_add, ← smul_assoc, ← zpow_add', sub_ne_zero]

/--
Helper lemma for `meromorphicOrderAt_add_of_ne`.
-/
lemma meromorphicOrderAt_add_eq_right_of_lt (hf₁ : MeromorphicAt f₁ x) (hf₂ : MeromorphicAt f₂ x)
    (h : meromorphicOrderAt f₂ x hf₂ < meromorphicOrderAt f₁ x hf₁) :
    meromorphicOrderAt (f₁ + f₂) x (hf₁.add hf₂) = meromorphicOrderAt f₂ x hf₂ :=
  (meromorphicOrderAt_congr (hf₁.add hf₂) (.of_eq (add_comm f₁ f₂))).trans
    (meromorphicOrderAt_add_eq_left_of_lt hf₂ hf₁ h)

/--
If two meromorphic functions have unequal orders, then the order of their sum is
exactly the minimum of the orders of the summands.
-/
theorem meromorphicOrderAt_add_of_ne
    (hf₁ : MeromorphicAt f₁ x) (hf₂ : MeromorphicAt f₂ x)
    (h : meromorphicOrderAt f₁ x hf₁ ≠ meromorphicOrderAt f₂ x hf₂) :
    meromorphicOrderAt (f₁ + f₂) x (hf₁.add hf₂) =
      min (meromorphicOrderAt f₁ x hf₁) (meromorphicOrderAt f₂ x hf₂) := by
  rcases lt_or_lt_iff_ne.mpr h with h | h
  · simpa [h.le] using meromorphicOrderAt_add_eq_left_of_lt hf₁ hf₂ h
  · simpa [h.le] using meromorphicOrderAt_add_eq_right_of_lt hf₁ hf₂ h

/-!
## Level Sets of the Order Function
-/

namespace MeromorphicOn

variable {U : Set 𝕜}

/-- The set where a meromorphic function has infinite order is clopen in its domain of meromorphy.
-/
theorem isClopen_setOfPred_meromorphicOrderAt_eq_top (hf : MeromorphicOn f U) :
    IsClopen { u : U | meromorphicOrderAt f u.1 (hf u.1 u.2) = ⊤ } := by
  have hset : { u : U | meromorphicOrderAt f u.1 (hf u.1 u.2) = ⊤ } =
      { u : U | ∀ᶠ z in 𝓝[≠] u.1, f z = 0 } :=
    Set.ext fun u ↦ meromorphicOrderAt_eq_top_iff (hf u.1 u.2)
  rw [hset]
  constructor
  · rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro z hz
    rcases (hf z.1 z.2).eventually_eq_zero_or_eventually_ne_zero with h | h
    · -- Case: f is locally zero in a punctured neighborhood of z
      exact (hz h).elim
    · -- Case: f is locally nonzero in a punctured neighborhood of z
      obtain ⟨t', h₁t', h₂t', h₃t'⟩ := eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 h)
      refine ⟨Subtype.val ⁻¹' t', fun w hw hw₀ ↦ ?_, isOpen_induced h₂t', h₃t'⟩
      have hw₀' : ∀ᶠ y in 𝓝[≠] w.1, f y = 0 := hw₀
      by_cases h₁w : w = z
      · subst h₁w
        exact hz hw₀
      · have h₂ : ∀ᶠ y in 𝓝[≠] w.1, f y ≠ 0 := by
          rw [eventually_nhdsWithin_iff, eventually_nhds_iff]
          exact ⟨t' \ {z.1}, fun y h₁y _ ↦ h₁t' y h₁y.1 h₁y.2, h₂t'.sdiff isClosed_singleton,
            ⟨hw, mem_singleton_iff.not.2 (Subtype.coe_ne_coe.mpr h₁w)⟩⟩
        obtain ⟨y, hy, hy'⟩ := (h₂.and hw₀').exists
        exact hy hy'
  · apply isOpen_iff_forall_mem_open.mpr
    intro z hz
    have hz' : ∀ᶠ y in 𝓝[≠] z.1, f y = 0 := hz
    rw [eventually_nhdsWithin_iff, eventually_nhds_iff] at hz'
    obtain ⟨t', h₁t', h₂t', h₃t'⟩ := hz'
    refine ⟨Subtype.val ⁻¹' t', fun w hw ↦ ?_, isOpen_induced h₂t', h₃t'⟩
    change ∀ᶠ y in 𝓝[≠] w.1, f y = 0
    by_cases h₁w : w = z
    · subst h₁w
      exact hz
    · rw [eventually_nhdsWithin_iff, eventually_nhds_iff]
      exact ⟨t' \ {z.1}, fun y h₁y _ ↦ h₁t' y h₁y.1 h₁y.2, h₂t'.sdiff isClosed_singleton,
        ⟨hw, mem_singleton_iff.not.2 (Subtype.coe_ne_coe.mpr h₁w)⟩⟩

@[deprecated (since := "2026-07-09")]
alias isClopen_setOf_meromorphicOrderAt_eq_top := isClopen_setOfPred_meromorphicOrderAt_eq_top

/--
On a connected set, there exists a point where a meromorphic function `f` has finite order iff `f`
has finite order at every point.

See `Meromorphic.exists_meromorphicOrderAt_ne_top_iff_forall` in file
`Mathlib/Analysis/Meromorphic/RCLike` for a related result assuming that `f` is meromorphic on all
of `𝕜`.
-/
theorem exists_meromorphicOrderAt_ne_top_iff_forall (hf : MeromorphicOn f U) (hU : IsConnected U) :
    (∃ u : U, meromorphicOrderAt f u.1 (hf u.1 u.2) ≠ ⊤) ↔
      (∀ u : U, meromorphicOrderAt f u.1 (hf u.1 u.2) ≠ ⊤) := by
  constructor
  · intro h₂f
    have := isPreconnected_iff_preconnectedSpace.1 hU.isPreconnected
    rcases isClopen_iff.1 hf.isClopen_setOfPred_meromorphicOrderAt_eq_top with h | h
    · intro u
      have : u ∉ (∅ : Set U) := by exact fun a => a
      rw [← h] at this
      tauto
    · obtain ⟨u, hU⟩ := h₂f
      have : u ∈ univ := by trivial
      rw [← h] at this
      tauto
  · intro h₂f
    obtain ⟨v, hv⟩ := hU.nonempty
    exact ⟨⟨v, hv⟩, h₂f ⟨v, hv⟩⟩

/--
Variant of `MeromorphicOn.exists_meromorphicOrderAt_ne_top_iff_forall`, with membership in lieu of
subtypes.
-/
theorem exists_meromorphicOrderAt_ne_top_iff_forall_mem (hf : MeromorphicOn f U)
    (hU : IsConnected U) :
    (∃ u, ∃ hu : u ∈ U, meromorphicOrderAt f u (hf u hu) ≠ ⊤) ↔
      (∀ u, ∀ hu : u ∈ U, meromorphicOrderAt f u (hf u hu) ≠ ⊤) := by
  constructor
  · rintro ⟨u, hu, h⟩ v hv
    exact (exists_meromorphicOrderAt_ne_top_iff_forall hf hU).1 ⟨⟨u, hu⟩, h⟩ ⟨v, hv⟩
  · intro h
    obtain ⟨v, hv⟩ := hU.nonempty
    exact ⟨v, hv, h v hv⟩

/-- On a preconnected set, a meromorphic function has finite order at one point if it has finite
order at another point. -/
theorem meromorphicOrderAt_ne_top_of_isPreconnected (hf : MeromorphicOn f U) {y : 𝕜}
    (hU : IsPreconnected U) (h₁x : x ∈ U) (hy : y ∈ U)
    (h₂x : meromorphicOrderAt f x (hf x h₁x) ≠ ⊤) :
    meromorphicOrderAt f y (hf y hy) ≠ ⊤ :=
  (hf.exists_meromorphicOrderAt_ne_top_iff_forall ⟨nonempty_of_mem h₁x, hU⟩).1
    ⟨⟨x, h₁x⟩, h₂x⟩ ⟨y, hy⟩

theorem meromorphicOrderAt_eq_top_of_isPreconnected (hf : MeromorphicOn f U) {y : 𝕜}
    (hU : IsPreconnected U) (h₁x : x ∈ U) (hy : y ∈ U)
    (h₂x : meromorphicOrderAt f x (hf x h₁x) = ⊤) :
    meromorphicOrderAt f y (hf y hy) = ⊤ := by
  contrapose h₂x with h
  exact hf.meromorphicOrderAt_ne_top_of_isPreconnected hU hy h₁x h

/-- On a preconnected set, a meromorphic function that is not constantly zero has a
multiplicative inverse.

A version of `meromorphicOrderAt_ne_top_iff_mul_inv_eventuallyEq` where we relax the
equality to `=ᶠ[codiscreteWithin U]`. -/
theorem mul_inv_eventuallyEq {f : 𝕜 → 𝕜'} (hf : MeromorphicOn f U) (hU : IsPreconnected U)
    (h0 : ¬f =ᶠ[codiscreteWithin U] 0) :
    f * f⁻¹ =ᶠ[codiscreteWithin U] 1 := by
  simp_rw [EventuallyEq, Filter.Eventually, mem_codiscreteWithin_iff_forall_mem_nhdsNE,
    union_comm _ Uᶜ, ← mem_inf_principal'] at ⊢ h0
  intro x hx
  refine mem_inf_of_left <| (meromorphicOrderAt_ne_top_iff_mul_inv_eventuallyEq (hf x hx)).mp ?_
  contrapose h0
  intro y hy
  refine mem_inf_of_left <| (meromorphicOrderAt_eq_top_iff (hf y hy)).mp ?_
  exact hf.meromorphicOrderAt_eq_top_of_isPreconnected hU hx hy h0

/-- If a function is meromorphic on a set `U`, then for each point in `U`, it is analytic at nearby
points in `U`. When the target space is complete, this can be strengthened to analyticity at all
nearby points, see `MeromorphicAt.eventually_analyticAt`. -/
theorem eventually_analyticAt (h : MeromorphicOn f U) (hx : x ∈ U) :
    ∀ᶠ y in 𝓝[U \ {x}] x, AnalyticAt 𝕜 f y := by
  /- At neighboring points in `U`, the function `f` is both meromorphic (by meromorphicity on `U`)
  and continuous (thanks to the formula for a meromorphic function around the point `x`), so it is
  analytic. -/
  have : ∀ᶠ y in 𝓝[U \ {x}] x, ContinuousAt f y := by
    have : U \ {x} ⊆ {x}ᶜ := by simp
    exact nhdsWithin_mono _ this (h x hx).eventually_continuousAt
  filter_upwards [this, self_mem_nhdsWithin] with y hy h'y
  exact (h y h'y.1).analyticAt hy

theorem eventually_analyticAt_or_mem_compl (h : MeromorphicOn f U) (hx : x ∈ U) :
    ∀ᶠ y in 𝓝[≠] x, AnalyticAt 𝕜 f y ∨ y ∈ Uᶜ := by
  have : {x}ᶜ = (U \ {x}) ∪ Uᶜ := by aesop (add simp Classical.em)
  rw [this, nhdsWithin_union]
  simp only [mem_compl_iff, eventually_sup]
  refine ⟨?_, ?_⟩
  · filter_upwards [h.eventually_analyticAt hx] with y hy using Or.inl hy
  · filter_upwards [self_mem_nhdsWithin] with y hy using Or.inr hy

/-- Meromorphic functions on `U` are analytic on `U`, outside of a discrete subset. -/
theorem analyticAt_mem_codiscreteWithin (hf : MeromorphicOn f U) :
    { x | AnalyticAt 𝕜 f x } ∈ Filter.codiscreteWithin U := by
  rw [mem_codiscreteWithin]
  intro x hx
  rw [Filter.disjoint_principal_right, ← Filter.eventually_mem_set]
  filter_upwards [hf.eventually_analyticAt_or_mem_compl hx] with y hy
  simp
  tauto

/-- The set where a meromorphic function has zero or infinite
order is codiscrete within its domain of meromorphicity. -/
theorem codiscrete_setOfPred_meromorphicOrderAt_eq_zero_or_top (hf : MeromorphicOn f U) :
    {u : U | meromorphicOrderAt f u.1 (hf u.1 u.2) = 0 ∨
      meromorphicOrderAt f u.1 (hf u.1 u.2) = ⊤} ∈ Filter.codiscrete U := by
  rw [mem_codiscrete_subtype_iff_mem_codiscreteWithin, mem_codiscreteWithin]
  intro x hx
  rw [Filter.disjoint_principal_right]
  rcases (hf x hx).eventually_eq_zero_or_eventually_ne_zero with h₁f | h₁f
  · filter_upwards [eventually_eventually_nhdsWithin.2 h₁f] with a h₁a
    rintro ⟨haU, haS⟩
    have h₂a : ∀ᶠ (z : 𝕜) in 𝓝[≠] a, f z = 0 := by
      obtain rfl | hax := eq_or_ne a x
      · exact h₁a
      rw [eventually_nhdsWithin_iff, eventually_nhds_iff] at h₁a ⊢
      obtain ⟨t, h₁t, h₂t, h₃t⟩ := h₁a
      refine ⟨t \ {x}, fun y h₁y _ ↦ h₁t y h₁y.1 h₁y.2, h₂t.sdiff isClosed_singleton, ?_⟩
      exact Set.mem_sdiff_of_mem h₃t hax
    exact haS ⟨⟨a, haU⟩, Or.inr ((meromorphicOrderAt_eq_top_iff (hf a haU)).2 h₂a), rfl⟩
  · filter_upwards [hf.eventually_analyticAt_or_mem_compl hx, h₁f] with a h₁a h'₁a
    rintro ⟨haU, haS⟩
    rcases h₁a with h' | h'
    · refine haS ⟨⟨a, haU⟩, Or.inl ?_, rfl⟩
      change meromorphicOrderAt f a (hf a haU) = 0
      rw [h'.meromorphicOrderAt_eq, h'.analyticOrderAt_eq_zero.2 h'₁a]
      simp
    · exact h' haU

@[deprecated (since := "2026-07-09")]
alias codiscrete_setOf_meromorphicOrderAt_eq_zero_or_top :=
  codiscrete_setOfPred_meromorphicOrderAt_eq_zero_or_top

/--
Variant of `codiscrete_setOfPred_meromorphicOrderAt_eq_zero_or_top`: The set where a meromorphic
function has zero or infinite order is codiscrete within its domain of meromorphicity.
-/
theorem codiscreteWithin_setOfPred_meromorphicOrderAt_eq_zero_or_top (h₁f : MeromorphicOn f U) :
    {u : 𝕜 | ∃ hu : u ∈ U,
      meromorphicOrderAt f u (h₁f u hu) = 0 ∨ meromorphicOrderAt f u (h₁f u hu) = ⊤} ∈
        codiscreteWithin U := by
  refine mem_of_superset
    (mem_codiscrete_subtype_iff_mem_codiscreteWithin.1
      h₁f.codiscrete_setOfPred_meromorphicOrderAt_eq_zero_or_top) ?_
  rintro _ ⟨⟨v, hv⟩, h', rfl⟩
  exact ⟨hv, h'⟩

@[deprecated (since := "2026-07-09")]
alias codiscreteWithin_setOf_meromorphicOrderAt_eq_zero_or_top :=
  codiscreteWithin_setOfPred_meromorphicOrderAt_eq_zero_or_top

end MeromorphicOn

section comp
/-!
## Order at a Point: Behaviour under Composition
-/
variable {x : 𝕜} {f : 𝕜 → E} {g : 𝕜 → 𝕜}

/-- If `g` is analytic at `x`, `f` is meromorphic at `g x`, and `g` is not locally constant near
`x`, the order of `f ∘ g` is the product of the orders of `f` and `g · - g x`. -/
lemma MeromorphicAt.meromorphicOrderAt_comp (hf : MeromorphicAt f (g x)) (hg : AnalyticAt 𝕜 g x)
    (hg_nc : ¬EventuallyConst g (𝓝 x)) :
    meromorphicOrderAt (f ∘ g) x (hf.comp_analyticAt hg) =
      (meromorphicOrderAt f (g x) hf) *
        (analyticOrderAt (g · - g x) x (hg.fun_sub analyticAt_const)).map Nat.cast := by
  have hg' : AnalyticAt 𝕜 (g · - g x) x := hg.fun_sub analyticAt_const
  -- First deal with the silly case that `f` is identically zero around `g x`.
  rcases eq_or_ne (meromorphicOrderAt f (g x) hf) ⊤ with hf' | hf'
  · rw [hf', WithTop.top_mul]
    · rw [meromorphicOrderAt_eq_top_iff] at hf' ⊢
      rw [Function.comp_def, ← eventually_map (P := (f · = 0))]
      exact EventuallyEq.filter_mono hf' (hg.map_nhdsNE hg_nc)
    · simp [hg'.analyticOrderAt_eq_zero]
  -- Now the interesting case. First unpack the data
  have hr := (WithTop.coe_untop₀_of_ne_top hf').symm
  rw [meromorphicOrderAt_ne_top_iff hf] at hf'
  set r := (meromorphicOrderAt f (g x) hf).untop₀
  rw [hr]
  -- Now write `f = (· - g x) ^ r • F` for `F` analytic and nonzero at `g x`
  obtain ⟨F, hFan, hFne, hFev⟩ := hf'
  have hFg : AnalyticAt 𝕜 (F ∘ g) x := hFan.comp hg
  have aux1 : f ∘ g =ᶠ[𝓝[≠] x] (g · - g x) ^ r • (F ∘ g) := hFev.comp_tendsto (hg.map_nhdsNE hg_nc)
  have aux2 : meromorphicOrderAt (F ∘ g) x hFg.meromorphicAt = 0 := by
    rw [hFg.meromorphicOrderAt_eq, hFg.analyticOrderAt_eq_zero.mpr hFne, ENat.map_zero,
      CharP.cast_eq_zero, WithTop.coe_zero]
  have hpow : MeromorphicAt ((g · - g x) ^ r) x := by fun_prop
  rw [meromorphicOrderAt_congr (hf.comp_analyticAt hg) aux1,
    meromorphicOrderAt_smul hpow hFg.meromorphicAt, aux2, add_zero,
    meromorphicOrderAt_zpow hg'.meromorphicAt, hg'.meromorphicOrderAt_eq]

/-- If `f` is meromorphic at `g x`, `g` is analytic at `x`, and `g' x ≠ 0`, then the meromorphic
order of `f ∘ g` at `x` is the meromorphic order of `f` at `g x`. -/
lemma meromorphicOrderAt_comp_of_deriv_ne_zero (hf : MeromorphicAt f (g x)) (hg : AnalyticAt 𝕜 g x)
    (hg' : deriv g x ≠ 0) :
    meromorphicOrderAt (f ∘ g) x (hf.comp_analyticAt hg) = meromorphicOrderAt f (g x) hf := by
  have hgo : analyticOrderAt (g · - g x) x (hg.fun_sub analyticAt_const) = 1 :=
    hg.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hg'
  have hnc : ¬ EventuallyConst g (𝓝 x) := by
    rw [eventuallyConst_iff_analyticOrderAt_sub_eq_top hg, hgo]
    simp
  rw [hf.meromorphicOrderAt_comp hg hnc, hgo]
  simp

/-- `meromorphicOrderAt` is invariant under translation. -/
@[to_fun meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt]
theorem meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt {c : 𝕜} {f : 𝕜 → E}
    (hf : MeromorphicAt f (x + c)) :
    meromorphicOrderAt (f ∘ (· + c)) x (meromorphicAt_comp_add_const_iff_meromorphicAt.2 hf) =
      meromorphicOrderAt f (x + c) hf :=
  meromorphicOrderAt_comp_of_deriv_ne_zero (g := (· + c)) hf (by fun_prop) (by simp)

/-- `meromorphicOrderAt` is invariant under translation. -/
@[to_fun meromorphicOrderAt_fun_comp_sub_const_eq_meromorphicOrderAt]
theorem meromorphicOrderAt_comp_sub_const_eq_meromorphicOrderAt {c : 𝕜} {f : 𝕜 → E}
    (hf : MeromorphicAt f (x - c)) :
    meromorphicOrderAt (f ∘ (· - c)) x (meromorphicAt_comp_sub_const_iff_meromorphicAt.2 hf) =
      meromorphicOrderAt f (x - c) hf :=
  meromorphicOrderAt_comp_of_deriv_ne_zero (g := (· - c)) hf (by fun_prop) (by simp)

end comp

section smul

variable {g : 𝕜 → 𝕜}

lemma meromorphicOrderAt_smul_of_ne_zero (hf : MeromorphicAt f x) (hg : AnalyticAt 𝕜 g x)
    (hg' : g x ≠ 0) :
    meromorphicOrderAt (g • f) x (hg.meromorphicAt.smul hf) = meromorphicOrderAt f x hf := by
  rw [meromorphicOrderAt_smul hg.meromorphicAt hf, hg.meromorphicOrderAt_eq,
    hg.analyticOrderAt_eq_zero.mpr hg']
  simp

lemma meromorphicOrderAt_mul_of_ne_zero {f : 𝕜 → 𝕜} (hf : MeromorphicAt f x)
    (hg : AnalyticAt 𝕜 g x) (hg' : g x ≠ 0) :
    meromorphicOrderAt (g * f) x (hg.meromorphicAt.mul hf) = meromorphicOrderAt f x hf :=
  meromorphicOrderAt_smul_of_ne_zero hf hg hg'

/-- meromorphicOrderAt is invariant under scaling. -/
@[simp] theorem meromorphicOrderAt_const_smul_eq_meromorphicOrderAt {f : 𝕜 → E} {s : 𝕜}
    (hs : s ≠ 0) (hf : MeromorphicAt (s • f) x) :
    meromorphicOrderAt (s • f) x hf =
      meromorphicOrderAt f x ((meromorphicAt_const_smul_iff_meromorphicAt hs).mp hf) := by
  have h : s • f = (fun (_ : 𝕜) ↦ s) • f := by aesop
  exact (meromorphicOrderAt_congr hf (.of_eq h)).trans
    (meromorphicOrderAt_smul_of_ne_zero ((meromorphicAt_const_smul_iff_meromorphicAt hs).mp hf)
      analyticAt_const hs)

/-- meromorphicOrderAt is invariant under scaling. -/
@[simp] theorem meromorphicOrderAt_fun_const_smul_eq_meromorphicOrderAt {f : 𝕜 → E} {s : 𝕜}
    (hs : s ≠ 0) (hf : MeromorphicAt (fun z ↦ s • f z) x) :
    meromorphicOrderAt (fun z ↦ s • f z) x hf =
      meromorphicOrderAt f x ((meromorphicAt_fun_const_smul_iff_meromorphicAt hs).mp hf) :=
  meromorphicOrderAt_const_smul_eq_meromorphicOrderAt hs hf

end smul

/-!
## Order at a Point of the Derivative
-/

section deriv

/-- The meromorphic order of the derivative is one less than the order of the original function.
This however is not true if the characteristic of the domain field divides the original order,
where the order of the derivative can rise to a larger integer. -/
lemma meromorphicOrderAt_deriv_eq_sub_one [CompleteSpace E] {f : 𝕜 → E} {x : 𝕜} {n : ℤ}
    (hf : MeromorphicAt f x) (hn : (n : 𝕜) ≠ 0) (hfn : meromorphicOrderAt f x hf = ↑n) :
    meromorphicOrderAt (deriv f) x hf.deriv = ↑(n - 1) := by
  rw [meromorphicOrderAt_eq_int_iff hf] at hfn
  rw [meromorphicOrderAt_eq_int_iff hf.deriv]
  obtain ⟨g, hga, hg0, (hg : f =ᶠ[𝓝[≠] x] fun z ↦ (z - x) ^ n • g z)⟩ := hfn
  refine ⟨fun z ↦ (n : 𝕜) • g z + (z - x) • deriv g z, by fun_prop, by simpa using ⟨hn, hg0⟩, ?_⟩
  filter_upwards [hga.eventually_analyticAt.filter_mono (nhdsWithin_le_nhds),
    eventually_mem_nhdsWithin, hg.nhdsNE_deriv] with z hgz hmem hz
  have hzx : z - x ≠ 0 := by simpa [sub_eq_zero] using hmem
  calc
    deriv f z = deriv (fun z ↦ (z - x) ^ n • g z) z :=
      hz
    _ = (z - x) ^ n • deriv g z + deriv ((· ^ n) ∘ (· - x)) z • g z :=
      deriv_fun_smul (by fun_prop (disch := grind)) hgz.differentiableAt
    _ = (z - x) ^ n • deriv g z + (n * (z - x) ^ (n - 1)) • g z := by
      rw [deriv_comp _ (by fun_prop (disch := grind)) (by fun_prop)]
      simp [deriv_zpow]
    _ = (z - x) ^ (n - 1) • ((n : 𝕜) • g z + (z - x) • deriv g z) := by
      simp [smul_smul, ← zpow_add_one₀ hzx, add_comm, mul_comm]

/-- Equivalent to `meromorphicOrderAt_deriv_eq_sub_one` with a slightly different statement so the
conclusion matches more targets -/
lemma meromorphicOrderAt_deriv [CompleteSpace E] {f : 𝕜 → E} {x : 𝕜} {n : ℤ}
    (hf : MeromorphicAt f x) (hn : (↑(n + 1) : 𝕜) ≠ 0)
    (hfn : meromorphicOrderAt f x hf = ↑(n + 1)) :
    meromorphicOrderAt (deriv f) x hf.deriv = ↑n := by
  simpa using meromorphicOrderAt_deriv_eq_sub_one hf hn hfn
variable [CompleteSpace 𝕜] {f : 𝕜 → 𝕜}

/--
At zeros and poles of a meromorphic function `f`, the logarithmic derivative has a simple pole: its
meromorphic order equals `-1`.
-/
theorem meromorphicOrderAt_logDeriv_eq_neg_one [CharZero 𝕜] (hf : MeromorphicAt f x)
    (h₁ : meromorphicOrderAt f x hf ≠ 0) (h₂ : meromorphicOrderAt f x hf ≠ ⊤) :
    meromorphicOrderAt (logDeriv f) x hf.logDeriv = -1 := by
  lift meromorphicOrderAt f x hf to ℤ using h₂ with n hn
  change meromorphicOrderAt (deriv f / f) x (hf.deriv.div hf) = -1
  rw [meromorphicOrderAt_div hf.deriv hf,
    meromorphicOrderAt_deriv_eq_sub_one hf (Int.cast_ne_zero.mpr (by exact_mod_cast h₁))
      hn.symm,
    ← hn]
  norm_cast
  simp

/--
At points where a meromorphic function has order zero, the meromorphic order of the logarithmic
derivative is nonnegative.
-/
theorem meromorphicOrderAt_logDeriv_nonneg (hf : MeromorphicAt f x)
    (h : meromorphicOrderAt f x hf = 0) :
    0 ≤ meromorphicOrderAt (logDeriv f) x hf.logDeriv := by
  obtain ⟨g, h₁g, h₂g, h₃g⟩ :=
    (meromorphicOrderAt_eq_int_iff (n := 0) hf).1 (by exact_mod_cast h)
  have h₄ : f =ᶠ[𝓝[≠] x] g := by
    filter_upwards [h₃g] with z hz using by simpa using hz
  rw [meromorphicOrderAt_congr hf.logDeriv (logDeriv_congr_nhdsNE h₄)]
  exact (h₁g.deriv.div h₁g h₂g).meromorphicOrderAt_nonneg

end deriv
