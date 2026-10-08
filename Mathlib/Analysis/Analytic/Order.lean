/-
Copyright (c) 2022 Vincent Beffara. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Beffara, Stefan Kebekus
-/
module

public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Vanishing Order of Analytic Functions

This file defines the order of vanishing of an analytic function `f` at a point `z₀`, as an element
of `ℕ∞`.

## TODO

Uniformize API between analytic and meromorphic functions
-/

@[expose] public section

open Filter Set
open scoped Topology

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-!
## Vanishing Order at a Point: Definition and Characterization
-/

section NormedSpace
variable {f g : 𝕜 → E} {n : ℕ} {z₀ : 𝕜}

open scoped Classical in
/-- The order of vanishing of an analytic function `f` at `z₀`, as an element of `ℕ∞`.

The order is defined to be `∞` if `f` is identically 0 on a neighbourhood of `z₀`, and otherwise the
unique `n` such that `f` can locally be written as `f z = (z - z₀) ^ n • g z`, where `g` is analytic
and does not vanish at `z₀`. See `analyticOrderAt_eq_top` and
`AnalyticAt.analyticOrderAt_eq_natCast` for these equivalences.

The order is only defined for a function that is analytic at `z₀`: the proof `hf` of analyticity is
an argument of the definition, which `fun_prop` supplies by default. There is no value for a
function that is not analytic at `z₀`. -/
noncomputable def analyticOrderAt (f : 𝕜 → E) (z₀ : 𝕜)
    (hf : AnalyticAt 𝕜 f z₀ := by fun_prop_default) : ℕ∞ :=
  if h : ∀ᶠ z in 𝓝 z₀, f z = 0 then ⊤
  else ↑(hf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr h).choose

/-- The order of an analytic function `f` at a `z₀` is infinity iff `f` vanishes locally around
`z₀`. -/
lemma analyticOrderAt_eq_top (hf : AnalyticAt 𝕜 f z₀) :
    analyticOrderAt f z₀ hf = ⊤ ↔ ∀ᶠ z in 𝓝 z₀, f z = 0 := by
  unfold analyticOrderAt
  split_ifs with h
  · exact iff_of_true rfl h
  · exact iff_of_false (ENat.natCast_ne_top _) h

lemma eventuallyConst_iff_analyticOrderAt_sub_eq_top (hf : AnalyticAt 𝕜 f z₀) :
    EventuallyConst f (𝓝 z₀) ↔
      analyticOrderAt (f · - f z₀) z₀ (hf.fun_sub analyticAt_const) = ⊤ := by
  simpa [eventuallyConst_iff_exists_eventuallyEq, analyticOrderAt_eq_top, sub_eq_zero]
    using ⟨fun ⟨c, hc⟩ ↦ (show f z₀ = c from hc.self_of_nhds) ▸ hc, fun h ↦ ⟨_, h⟩⟩

/-- The order of an analytic function `f` at `z₀` equals a natural number `n` iff `f` can locally
be written as `f z = (z - z₀) ^ n • g z`, where `g` is analytic and does not vanish at `z₀`. -/
lemma AnalyticAt.analyticOrderAt_eq_natCast (hf : AnalyticAt 𝕜 f z₀) :
    analyticOrderAt f z₀ hf = n ↔
      ∃ (g : 𝕜 → E), AnalyticAt 𝕜 g z₀ ∧ g z₀ ≠ 0 ∧ ∀ᶠ z in 𝓝 z₀, f z = (z - z₀) ^ n • g z := by
  unfold analyticOrderAt
  split_ifs with h
  · simp only [ENat.top_ne_natCast, false_iff]
    contrapose h
    rw [← hf.exists_eventuallyEq_pow_smul_nonzero_iff]
    exact ⟨n, h⟩
  · rw [← hf.exists_eventuallyEq_pow_smul_nonzero_iff] at h
    refine ⟨fun hn ↦ (WithTop.coe_inj.mp hn : h.choose = n) ▸ h.choose_spec, fun h' ↦ ?_⟩
    rw [AnalyticAt.unique_eventuallyEq_pow_smul_nonzero h.choose_spec h']

/-- The order of an analytic function `f` at `z₀` is finite iff `f` can locally be written as
`f z = (z - z₀) ^ n • g z` for some natural number `n`, where `g` is analytic and does not vanish at
`z₀`. In this case, `n` is the order of `f` at `z₀`.

See `MeromorphicNFAt.order_eq_zero_iff` for an analogous statement about meromorphic functions in
normal form.
-/
lemma AnalyticAt.analyticOrderAt_ne_top (hf : AnalyticAt 𝕜 f z₀) :
    analyticOrderAt f z₀ hf ≠ ⊤ ↔
      ∃ (n : ℕ) (g : 𝕜 → E), analyticOrderAt f z₀ hf = n ∧ AnalyticAt 𝕜 g z₀ ∧ g z₀ ≠ 0 ∧
        ∀ᶠ z in 𝓝 z₀, f z = (z - z₀) ^ n • g z := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp h
    obtain ⟨g, hg⟩ := hf.analyticOrderAt_eq_natCast.mp hn.symm
    exact ⟨n, g, hn.symm, hg⟩
  · rintro ⟨n, g, hn, -⟩
    rw [hn]
    exact ENat.natCast_ne_top n

/-- The order of an analytic function `f` at `z₀` is zero iff `f` does not vanish at `z₀`. -/
protected lemma AnalyticAt.analyticOrderAt_eq_zero (hf : AnalyticAt 𝕜 f z₀) :
    analyticOrderAt f z₀ hf = 0 ↔ f z₀ ≠ 0 := by
  rw [← ENat.natCast_zero, hf.analyticOrderAt_eq_natCast]
  constructor
  · intro ⟨g, _, _, hg⟩
    simpa [hg.self_of_nhds]
  · exact fun hz ↦ ⟨f, hf, hz, by simp⟩

/-- The order of an analytic function `f` at `z₀` is nonzero iff `f` vanishes at `z₀`. -/
protected lemma AnalyticAt.analyticOrderAt_ne_zero (hf : AnalyticAt 𝕜 f z₀) :
    analyticOrderAt f z₀ hf ≠ 0 ↔ f z₀ = 0 := hf.analyticOrderAt_eq_zero.not_left

/-- A function vanishes at a point if its analytic order is nonzero in `ℕ∞`. -/
lemma apply_eq_zero_of_analyticOrderAt_ne_zero (hf : AnalyticAt 𝕜 f z₀)
    (h : analyticOrderAt f z₀ hf ≠ 0) : f z₀ = 0 :=
  hf.analyticOrderAt_ne_zero.mp h

/-- Characterization of which natural numbers are `≤ hf.order`. Useful for avoiding case splits,
since it applies whether or not the order is `∞`. -/
lemma natCast_le_analyticOrderAt (hf : AnalyticAt 𝕜 f z₀) {n : ℕ} :
    n ≤ analyticOrderAt f z₀ hf ↔
      ∃ g, AnalyticAt 𝕜 g z₀ ∧ ∀ᶠ z in 𝓝 z₀, f z = (z - z₀) ^ n • g z := by
  unfold analyticOrderAt
  split_ifs with h
  · simpa using ⟨0, analyticAt_const .., by simpa⟩
  · let m := (hf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr h).choose
    obtain ⟨g, hg, hg_ne, hm⟩ := (hf.exists_eventuallyEq_pow_smul_nonzero_iff.mpr h).choose_spec
    rw [ENat.natCast_le_natCast]
    refine ⟨fun hmn ↦ ⟨fun z ↦ (z - z₀) ^ (m - n) • g z, by fun_prop, ?_⟩, fun ⟨h, hh, hfh⟩ ↦ ?_⟩
    · filter_upwards [hm] with z hz using by rwa [← mul_smul, ← pow_add, Nat.add_sub_of_le hmn]
    · contrapose! hg_ne
      have : ContinuousAt (fun z ↦ (z - z₀) ^ (n - m) • h z) z₀ := by fun_prop
      rw [tendsto_nhds_unique_of_eventuallyEq (l := 𝓝[≠] z₀)
        hg.continuousAt.continuousWithinAt this.continuousWithinAt ?_]
      · simp [m, Nat.sub_ne_zero_of_lt hg_ne]
      · filter_upwards [self_mem_nhdsWithin, hm.filter_mono nhdsWithin_le_nhds,
          hfh.filter_mono nhdsWithin_le_nhds] with z hz hf' hf''
        rw [← inv_smul_eq_iff₀ (pow_ne_zero _ <| sub_ne_zero_of_ne hz), hf'', smul_comm,
          ← mul_smul] at hf'
        rw [pow_sub₀ _ (sub_ne_zero_of_ne hz) (by lia), ← hf']

/-- If two functions agree in a neighborhood of `z₀`, then their orders at `z₀` agree. -/
lemma analyticOrderAt_congr (hf : AnalyticAt 𝕜 f z₀) (hfg : f =ᶠ[𝓝 z₀] g) :
    analyticOrderAt f z₀ hf = analyticOrderAt g z₀ (hf.congr hfg) := by
  refine ENat.eq_of_forall_natCast_le_iff fun n ↦ ?_
  simp only [natCast_le_analyticOrderAt]
  congr! 3
  exact hfg.congr_left

/-- Subtracting the value at `z₀` does not change the order of an analytic function that vanishes
at `z₀`. -/
lemma analyticOrderAt_sub_apply_of_eq_zero (hf : AnalyticAt 𝕜 f z₀) (hz : f z₀ = 0) :
    analyticOrderAt (f · - f z₀) z₀ (hf.fun_sub analyticAt_const) = analyticOrderAt f z₀ hf := by
  have h : (f · - f z₀) =ᶠ[𝓝 z₀] f := .of_eq (funext fun z ↦ by simp [hz])
  exact analyticOrderAt_congr (hf.fun_sub analyticAt_const) h

@[simp] lemma analyticOrderAt_id : analyticOrderAt (𝕜 := 𝕜) id 0 = 1 :=
  analyticAt_id.analyticOrderAt_eq_natCast.mpr ⟨fun _ ↦ 1, by fun_prop, by simp, by simp⟩

@[simp] lemma analyticOrderAt_neg (hf : AnalyticAt 𝕜 (-f) z₀) :
    analyticOrderAt (-f) z₀ hf = analyticOrderAt f z₀ (analyticAt_neg.mp hf) := by
  refine ENat.eq_of_forall_natCast_le_iff fun n ↦ ?_
  simp only [natCast_le_analyticOrderAt]
  exact (Equiv.neg _).exists_congr <| by simp [neg_eq_iff_eq_neg]

/-- The order of a sum is at least the minimum of the orders of the summands. -/
theorem le_analyticOrderAt_add (hf : AnalyticAt 𝕜 f z₀) (hg : AnalyticAt 𝕜 g z₀) :
    min (analyticOrderAt f z₀ hf) (analyticOrderAt g z₀ hg) ≤
      analyticOrderAt (f + g) z₀ (hf.add hg) := by
  refine ENat.forall_natCast_le_iff_le.mp fun n ↦ ?_
  simp only [le_min_iff, natCast_le_analyticOrderAt]
  refine fun ⟨⟨F, hF, hF'⟩, ⟨G, hG, hG'⟩⟩ ↦ ⟨F + G, hF.add hG, ?_⟩
  filter_upwards [hF', hG'] with z using by simp +contextual

lemma le_analyticOrderAt_sub (hf : AnalyticAt 𝕜 f z₀) (hg : AnalyticAt 𝕜 g z₀) :
    min (analyticOrderAt f z₀ hf) (analyticOrderAt g z₀ hg) ≤
      analyticOrderAt (f - g) z₀ (hf.sub hg) := by
  have h := le_analyticOrderAt_add hf hg.neg
  rw [analyticOrderAt_neg] at h
  exact h.trans_eq (analyticOrderAt_congr (hf.add hg.neg) (.of_eq (sub_eq_add_neg f g).symm))

lemma analyticOrderAt_add_eq_left_of_lt (hf : AnalyticAt 𝕜 f z₀) (hg : AnalyticAt 𝕜 g z₀)
    (hfg : analyticOrderAt f z₀ hf < analyticOrderAt g z₀ hg) :
    analyticOrderAt (f + g) z₀ (hf.add hg) = analyticOrderAt f z₀ hf := by
  refine le_antisymm ?_ (by simpa [hfg.le] using le_analyticOrderAt_add hf hg)
  have h := le_analyticOrderAt_sub (hf.add hg) hg
  rw [analyticOrderAt_congr ((hf.add hg).sub hg) (.of_eq (add_sub_cancel_right f g))] at h
  exact (min_le_iff.mp h).resolve_right hfg.not_ge

lemma analyticOrderAt_add_eq_right_of_lt (hf : AnalyticAt 𝕜 f z₀) (hg : AnalyticAt 𝕜 g z₀)
    (hgf : analyticOrderAt g z₀ hg < analyticOrderAt f z₀ hf) :
    analyticOrderAt (f + g) z₀ (hf.add hg) = analyticOrderAt g z₀ hg :=
  (analyticOrderAt_congr (hf.add hg) (.of_eq (add_comm f g))).trans
    (analyticOrderAt_add_eq_left_of_lt hg hf hgf)

/-- If two functions have unequal orders, then the order of their sum is exactly the minimum
of the orders of the summands. -/
lemma analyticOrderAt_add_of_ne (hf : AnalyticAt 𝕜 f z₀) (hg : AnalyticAt 𝕜 g z₀)
    (hfg : analyticOrderAt f z₀ hf ≠ analyticOrderAt g z₀ hg) :
    analyticOrderAt (f + g) z₀ (hf.add hg) =
      min (analyticOrderAt f z₀ hf) (analyticOrderAt g z₀ hg) := by
  obtain hfg | hgf := hfg.lt_or_gt
  · simpa [hfg.le] using analyticOrderAt_add_eq_left_of_lt hf hg hfg
  · simpa [hgf.le] using analyticOrderAt_add_eq_right_of_lt hf hg hgf

/-- The order is additive when scalar multiplying analytic functions. -/
lemma analyticOrderAt_smul {f : 𝕜 → 𝕜} (hf : AnalyticAt 𝕜 f z₀) (hg : AnalyticAt 𝕜 g z₀) :
    analyticOrderAt (f • g) z₀ (hf.smul hg) =
      analyticOrderAt f z₀ hf + analyticOrderAt g z₀ hg := by
  -- Trivial cases: one of the functions vanishes around z₀
  by_cases hf' : analyticOrderAt f z₀ hf = ⊤
  · rw [hf', top_add, analyticOrderAt_eq_top]
    filter_upwards [(analyticOrderAt_eq_top hf).mp hf'] with z hz
    simp [hz]
  by_cases hg' : analyticOrderAt g z₀ hg = ⊤
  · rw [hg', add_top, analyticOrderAt_eq_top]
    filter_upwards [(analyticOrderAt_eq_top hg).mp hg'] with z hz
    simp [hz]
  -- Non-trivial case: both functions do not vanish around z₀
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hf'
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hg'
  obtain ⟨f', h₁f', h₂f', h₃f'⟩ := hf.analyticOrderAt_eq_natCast.mp hm.symm
  obtain ⟨g', h₁g', h₂g', h₃g'⟩ := hg.analyticOrderAt_eq_natCast.mp hn.symm
  rw [← hm, ← hn, ← ENat.natCast_add, (hf.smul hg).analyticOrderAt_eq_natCast]
  refine ⟨f' • g', h₁f'.smul h₁g', ?_, ?_⟩
  · simp
    tauto
  · obtain ⟨t, h₁t, h₂t, h₃t⟩ := eventually_nhds_iff.1 h₃f'
    obtain ⟨s, h₁s, h₂s, h₃s⟩ := eventually_nhds_iff.1 h₃g'
    exact eventually_nhds_iff.2
      ⟨t ∩ s, fun y hy ↦ (by simp [h₁t y hy.1, h₁s y hy.2]; module), h₂t.inter h₂s, h₃t, h₃s⟩

theorem AnalyticAt.analyticOrderAt_deriv_add_one {x : 𝕜} (hf : AnalyticAt 𝕜 f x)
    [CompleteSpace E] [CharZero 𝕜] :
    analyticOrderAt (deriv f) x hf.deriv + 1 =
      analyticOrderAt (f · - f x) x (hf.fun_sub analyticAt_const) := by
  generalize h : analyticOrderAt (f · - f x) x (hf.fun_sub analyticAt_const) = r
  cases r with
  | top =>
    suffices analyticOrderAt (deriv f) x hf.deriv = ⊤ by rw [this, top_add]
    simp only [analyticOrderAt_eq_top, sub_eq_zero] at h ⊢
    obtain ⟨U, hUf, hUo, hUx⟩ := eventually_nhds_iff.mp h
    filter_upwards [hUo.mem_nhds hUx] with y hy
    simp [(eventuallyEq_of_mem (hUo.mem_nhds hy) hUf).deriv_eq]
  | coe r =>
    have hrne : r ≠ 0 := by
      intro hr
      rw [hr, ENat.natCast_zero, AnalyticAt.analyticOrderAt_eq_zero] at h
      grind
    obtain ⟨s, rfl⟩ := Nat.exists_add_one_eq.mpr (Nat.pos_of_ne_zero hrne)
    rw [Nat.cast_succ]
    congr 1
    rw [AnalyticAt.analyticOrderAt_eq_natCast] at h
    obtain ⟨F, hFa, hFne, hfF⟩ := h
    simp only [sub_eq_iff_eq_add] at hfF
    obtain ⟨U, hUf, hUo, hUx⟩ := eventually_nhds_iff.mp (hfF.and hFa.eventually_analyticAt)
    have : ∀ y ∈ U, deriv f y =
        (y - x) ^ (s + 1) • deriv F y + (s + 1) • (y - x) ^ s • F y := by
      intro y hy
      rw [EventuallyEq.deriv_eq (eventually_of_mem (hUo.mem_nhds hy) (fun u hu ↦ (hUf u hu).1)),
        deriv_add_const, deriv_fun_smul (by fun_prop) (hUf y hy).2.differentiableAt]
      simp [mul_smul, add_smul, Nat.cast_smul_eq_nsmul]
    have hsum : deriv f =ᶠ[𝓝 x] ((fun y : 𝕜 ↦ (y - x) ^ (s + 1) • deriv F y) +
        (fun y : 𝕜 ↦ (s + 1) • (y - x) ^ s • F y)) :=
      eventually_of_mem (hUo.mem_nhds hUx) this
    have hA : AnalyticAt 𝕜 (fun y ↦ (y - x) ^ (s + 1) • deriv F y) x := by fun_prop
    have hB : AnalyticAt 𝕜 (fun y ↦ (s + 1) • (y - x) ^ s • F y) x := by
      simp_rw [← Nat.cast_smul_eq_nsmul 𝕜]
      fun_prop
    have hB' : analyticOrderAt (fun y ↦ (s + 1) • (y - x) ^ s • F y) x hB = s := by
      rw [AnalyticAt.analyticOrderAt_eq_natCast]
      refine ⟨fun z ↦ (↑(s + 1) : 𝕜) • F z, hFa.fun_const_smul, ?_, .of_forall fun y ↦ ?_⟩
      · simpa using ⟨by norm_cast, hFne⟩
      · simpa only [Nat.cast_smul_eq_nsmul] using smul_comm ..
    have hlt : analyticOrderAt (fun y ↦ (s + 1) • (y - x) ^ s • F y) x hB <
        analyticOrderAt (fun y ↦ (y - x) ^ (s + 1) • deriv F y) x hA := by
      rw [hB', ← ENat.add_one_le_iff (ENat.natCast_ne_top _), ← Nat.cast_add_one,
        natCast_le_analyticOrderAt]
      exact ⟨deriv F, hFa.deriv, by simp⟩
    exact (analyticOrderAt_congr hf.deriv hsum).trans
      ((analyticOrderAt_add_eq_right_of_lt hA hB hlt).trans hB')

theorem AnalyticAt.analyticOrderAt_sub_eq_one_of_deriv_ne_zero {x : 𝕜} (hf : AnalyticAt 𝕜 f x)
    (hf' : deriv f x ≠ 0) :
    analyticOrderAt (f · - f x) x (hf.fun_sub analyticAt_const) = 1 := by
  generalize h : analyticOrderAt (f · - f x) x (hf.fun_sub analyticAt_const) = r
  cases r with
  | top =>
    simp_rw [analyticOrderAt_eq_top, sub_eq_zero] at h
    refine (hf' ?_).elim
    rw [EventuallyEq.deriv_eq h, deriv_const]
  | coe r =>
    norm_cast
    obtain ⟨F, hFa, hFne, hfF⟩ := (hf.fun_sub analyticAt_const).analyticOrderAt_eq_natCast.mp h
    apply eq_of_ge_of_le
    · by_contra! hr
      have := hfF.self_of_nhds
      simp_all
    · contrapose! hf'
      simp_rw [sub_eq_iff_eq_add] at hfF
      rw [EventuallyEq.deriv_eq hfF, deriv_add_const, deriv_fun_smul (by fun_prop) (by fun_prop),
        deriv_fun_pow (by fun_prop), sub_self, zero_pow (by lia), zero_pow (by lia),
        mul_zero, zero_mul, zero_smul, zero_smul, add_zero]

/-- At a zero with nonvanishing derivative, the analytic order is 1.
This is a variant of `analyticOrderAt_sub_eq_one_of_deriv_ne_zero` with `f z₀ = 0`
replacing the subtraction. -/
theorem AnalyticAt.analyticOrderAt_eq_one_of_zero_deriv_ne_zero {x : 𝕜}
    (hf : AnalyticAt 𝕜 f x) (hfx : f x = 0) (hf' : deriv f x ≠ 0) :
    analyticOrderAt f x hf = 1 :=
  (analyticOrderAt_sub_apply_of_eq_zero hf hfx).symm.trans
    (hf.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hf')

lemma natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero [CharZero 𝕜] [CompleteSpace E]
    (hf : AnalyticAt 𝕜 f z₀) :
    n ≤ analyticOrderAt f z₀ hf ↔ ∀ i < n, iteratedDeriv i f z₀ = 0 := by
  induction n generalizing f with
  | zero => simp
  | succ n IH =>
    by_cases hfz : f z₀ = 0; swap
    · simpa [hf.analyticOrderAt_eq_zero.mpr hfz] using ⟨0, by simp, by simpa⟩
    have : analyticOrderAt (deriv f) z₀ hf.deriv + 1 = analyticOrderAt f z₀ hf :=
      hf.analyticOrderAt_deriv_add_one.trans (analyticOrderAt_sub_apply_of_eq_zero hf hfz)
    simp [← this, IH hf.deriv, iteratedDeriv_succ',
      -Order.lt_add_one_iff, Nat.forall_lt_succ_left, hfz]

lemma analyticOrderAt_deriv_of_pos {𝕜 : Type*} {E : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] {f : 𝕜 → E} {z₀ : 𝕜}
    (hf : AnalyticAt 𝕜 f z₀) {n : ℕ} (horder : analyticOrderAt f z₀ hf = n + 1) :
    analyticOrderAt (deriv f) z₀ hf.deriv = n := by
  have ⟨g, hg, hg₀, hfg⟩ := (AnalyticAt.analyticOrderAt_eq_natCast hf).1 horder
  have hz₀ : f z₀ = 0 := by
    simpa [sub_self, zero_pow, zero_smul] using Filter.Eventually.self_of_nhds hfg
  have h := hf.analyticOrderAt_deriv_add_one.trans (analyticOrderAt_sub_apply_of_eq_zero hf hz₀)
  rw [horder] at h
  simpa using h

lemma analyticOrderAt_iterated_deriv {𝕜 : Type*} {E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] {f : 𝕜 → E} {z₀ : 𝕜}
    (hf : AnalyticAt 𝕜 f z₀) {k n : ℕ} [CharZero 𝕜] :
    n = analyticOrderAt f z₀ hf → n ≠ 0 → k ≤ n →
      analyticOrderAt (deriv^[k] f) z₀ (hf.iterated_deriv k) = (n - k : ℕ) := by
  induction k generalizing n with
  | zero => exact fun Hn Hpos Hk ↦ Hn.symm
  | succ n' hk =>
    intro Hn Hpos Hk
    have horder : analyticOrderAt (deriv^[n'] f) z₀ (hf.iterated_deriv n') =
        ((n - n'.succ : ℕ) : ℕ∞) + 1 := by
      refine (hk Hn Hpos (by lia)).trans ?_
      have : (n - n'.succ) + 1 = n - n' := by grind
      rw [← this]
      simp
    have e : analyticOrderAt (deriv^[n' + 1] f) z₀ (hf.iterated_deriv (n' + 1)) =
        analyticOrderAt (deriv (deriv^[n'] f)) z₀ (hf.iterated_deriv n').deriv :=
      analyticOrderAt_congr (hf.iterated_deriv (n' + 1))
        (.of_eq (Function.iterate_succ_apply' deriv n' f))
    rw [e]
    exact analyticOrderAt_deriv_of_pos (hf.iterated_deriv n') horder

attribute [local simp] Nat.factorial_ne_zero in
/-- A version of **Taylor's theorem** for analytic functions in one variable, with the error
term of the form `z ^ n` times a function analytic at 0.

(See `AnalyticAt.exists_eq_sum_add_pow_mul` for a version asserting global equality rather than
just on a neighbourhood of 0.) -/
lemma AnalyticAt.exists_eventuallyEq_sum_add_pow_mul [CharZero 𝕜] [CompleteSpace E]
    {f : 𝕜 → E} (hf : AnalyticAt 𝕜 f 0) (n : ℕ) :
    ∃ F : 𝕜 → E, AnalyticAt 𝕜 F 0 ∧ ∀ᶠ z in 𝓝 0,
      f z = (∑ i ∈ .range n, (z ^ i / i.factorial) • iteratedDeriv i f 0) + z ^ n • F z := by
  simp only [← sub_eq_iff_eq_add']
  have : AnalyticAt 𝕜
      (fun z : 𝕜 ↦ ∑ i ∈ .range n, (z ^ i / i.factorial) • iteratedDeriv i f 0) 0 := by
    refine Finset.analyticAt_fun_sum _ fun i hi ↦ ?_
    fun_prop
  convert! (natCast_le_analyticOrderAt (hf.fun_sub this)).mp ?_
  · simp
  · rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hf.fun_sub this)]
    intro i hi
    rw [iteratedDeriv_fun_sub (AnalyticAt.contDiffAt <| by fun_prop) this.contDiffAt]
    simp (disch := fun_prop) only [iteratedDeriv_fun_sum, iteratedDeriv_smul_const,
      iteratedDeriv_div_const, iteratedDeriv_fun_pow_zero]
    simp [ite_div, Finset.sum_ite_eq_of_mem _ _ _ (Finset.mem_range.mpr hi)]

attribute [local simp] Nat.factorial_ne_zero in
/-- A version of **Taylor's theorem** for analytic functions in one variable, with the error
term of the form `z ^ n` times a function analytic at 0.

(See `AnalyticAt.exists_eventuallyEq_sum_add_pow_mul` for a version asserting equality on a
neighbourhood of `0` rather than globally.) -/
lemma AnalyticAt.exists_eq_sum_add_pow_mul [CharZero 𝕜] [CompleteSpace E]
    {f : 𝕜 → E} (hf : AnalyticAt 𝕜 f 0) (n : ℕ) :
    ∃ F : 𝕜 → E, AnalyticAt 𝕜 F 0 ∧ ∀ z,
      f z = (∑ i ∈ .range n, (z ^ i / i.factorial) • iteratedDeriv i f 0) + z ^ n • F z := by
  classical
  obtain ⟨F, hFa, hF⟩ := hf.exists_eventuallyEq_sum_add_pow_mul n
  obtain ⟨U, hU0, hU'⟩ := by rwa [eventually_iff_exists_mem] at hF
  refine ⟨fun z ↦ if z ∈ U then F z else (z ^ n)⁻¹ • (f z
      - (∑ i ∈ .range n, (z ^ i / i.factorial) • iteratedDeriv i f 0)), ?_, fun z ↦ ?_⟩
  · exact hFa.congr (by filter_upwards [hU0] using by simp +contextual)
  · by_cases hz : z ∈ U
    · simpa [hz] using hU' z hz
    · simp only [ite_eq_right hz]
      rw [smul_inv_smul₀]
      · module
      · contrapose hz
        exact (pow_eq_zero_iff'.mp hz).1 ▸ mem_of_mem_nhds hU0

variable [CharZero 𝕜] [CompleteSpace E] {z₀ : 𝕜} {f : 𝕜 → E}
  (hf : AnalyticAt 𝕜 f z₀) (hzero : f z₀ = 0)

include hf hzero

/-- If an analytic function `f` vanishes at `z₀`, then the analytic order of its derivative
at `z₀` is at least `n` if and only if the analytic order of `f` at `z₀` is at least `n + 1`. -/
lemma analyticOrderAt_deriv_ge_iff {n : ℕ} :
    n ≤ analyticOrderAt (deriv f) z₀ hf.deriv ↔ n + 1 ≤ analyticOrderAt f z₀ hf := by
  rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hf.deriv,
    ← Nat.cast_add_one, natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hf]
  simp only [← iteratedDeriv_succ']
  refine ⟨fun h k hk ↦ ?_, fun h k hk ↦ h (k + 1) <| by lia⟩
  cases k with
  | zero => simpa
  | succ k => exact h k <| by lia

/-- The derivative of an analytic function `f` has infinite analytic order at a zero `z₀` if and
only if `f` has infinite analytic order at `z₀`. -/
lemma analyticOrderAt_deriv_eq_top_iff_of_eq_zero :
    analyticOrderAt (deriv f) z₀ hf.deriv = ⊤ ↔ analyticOrderAt f z₀ hf = ⊤ := by
  simp_rw [ENat.eq_top_iff_forall_ge, analyticOrderAt_deriv_ge_iff hf hzero]
  exact ⟨fun h m ↦ le_self_add.trans (h m), fun h m ↦ h (m + 1)⟩

/-- If an analytic function `f` vanishes at `z₀`, then its derivative has finite analytic order `n`
at `z₀` if and only if `f` has analytic order `n + 1` at `z₀`. -/
lemma analyticOrderAt_deriv_eq_iff {n : ℕ} :
    analyticOrderAt f z₀ hf = n + 1 ↔ analyticOrderAt (deriv f) z₀ hf.deriv = n := by
  have H {m : ℕ} {n : ℕ∞} : n = m ↔ m ≤ n ∧ ¬ m + 1 ≤ n := by
    cases n with | top => simp | coe _ => norm_cast; lia
  rw [← Nat.cast_add_one n, H, H, analyticOrderAt_deriv_ge_iff hf hzero, ← Nat.cast_add_one n,
    analyticOrderAt_deriv_ge_iff hf hzero]

omit hzero in
/-- An analytic function `f` has finite analytic order `n` at `z₀` if and only if its first
`n` iterated derivatives (including `f` itself) vanish at `z₀` and the `n`-th iterated derivative is
non-zero. -/
lemma analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero {n : ℕ} :
    analyticOrderAt f z₀ hf = n ↔
      (∀ k < n, iteratedDeriv k f z₀ = 0) ∧ iteratedDeriv n f z₀ ≠ 0 := by
  induction n generalizing f with
  | zero => simp [hf.analyticOrderAt_eq_zero]
  | succ n IH =>
    specialize IH hf.deriv
    simp_rw [← iteratedDeriv_succ'] at IH
    refine ⟨fun ho ↦ ?_, fun ⟨hz, hnz⟩ ↦ ?_⟩
    · have ⟨h_zero, h_nz⟩ := IH.mp (analyticOrderAt_deriv_of_pos hf ho)
      refine ⟨fun k hk ↦ ?_, h_nz⟩
      match k with
      | 0 => rw [iteratedDeriv_zero, ← hf.analyticOrderAt_ne_zero, ho, Nat.cast_add_one]
             exact Nat.cast_add_one_ne_zero _
      | k + 1 => exact h_zero k (by lia)
    · exact (analyticOrderAt_deriv_eq_iff hf <| by simpa using hz 0 (by lia)).mpr <|
        IH.mpr ⟨fun j _ ↦ hz (j + 1) (by lia), hnz⟩

end NormedSpace

/-!
## Vanishing Order at a Point: Elementary Computations
-/

/-- Simplifier lemma for the order of a centered monomial -/
@[simp]
lemma analyticOrderAt_centeredMonomial {z₀ : 𝕜} {n : ℕ} :
    analyticOrderAt ((· - z₀) ^ n) z₀ = n := by
  rw [AnalyticAt.analyticOrderAt_eq_natCast]
  exact ⟨1, by simp [Pi.one_def, analyticAt_const]⟩

/-- The analytic order of the function `(· - c)` at `x` is one if `x = c`. -/
@[simp] theorem analyticOrderAt_id_sub_const_self {c : 𝕜} :
    analyticOrderAt (· - c) c = 1 := by
  have h : AnalyticAt 𝕜 (· - c) c := by fun_prop
  exact h.analyticOrderAt_eq_natCast.mpr ⟨fun _ ↦ 1, by fun_prop, by simp, by simp⟩

/-- The analytic order of the function `(· - c)` at `x` is zero if `x ≠ c`. -/
@[simp] theorem analyticOrderAt_id_sub_const_of_ne {c x : 𝕜} (h : x ≠ c) :
    analyticOrderAt (· - c) x = 0 := by
  rw [AnalyticAt.analyticOrderAt_eq_zero]
  exact sub_ne_zero.mpr h

section NontriviallyNormedField
variable {f g : 𝕜 → 𝕜} {z₀ : 𝕜}

/-- The order is additive when multiplying analytic functions. -/
theorem analyticOrderAt_mul (hf : AnalyticAt 𝕜 f z₀) (hg : AnalyticAt 𝕜 g z₀) :
    analyticOrderAt (f * g) z₀ (hf.mul hg) =
      analyticOrderAt f z₀ hf + analyticOrderAt g z₀ hg :=
  analyticOrderAt_smul hf hg

/-- The order multiplies by `n` when taking an analytic function to its `n`th power. -/
theorem analyticOrderAt_pow (hf : AnalyticAt 𝕜 f z₀) :
    ∀ n, analyticOrderAt (f ^ n) z₀ (hf.pow n) = n • analyticOrderAt f z₀ hf
  | 0 => by simpa using (hf.pow 0).analyticOrderAt_eq_zero.mpr (by simp)
  | n + 1 => by
    rw [analyticOrderAt_congr (hf.pow (n + 1)) (.of_eq (pow_succ f n)),
      analyticOrderAt_mul (hf.pow n) hf, analyticOrderAt_pow hf n, succ_nsmul]

end NontriviallyNormedField

section comp

/-!
## Vanishing Order at a Point: Composition
-/
variable {f : 𝕜 → E} {g : 𝕜 → 𝕜} {z₀ : 𝕜}

/-- Analytic order of a composition of analytic functions. -/
lemma AnalyticAt.analyticOrderAt_comp (hf : AnalyticAt 𝕜 f (g z₀)) (hg : AnalyticAt 𝕜 g z₀) :
    analyticOrderAt (f ∘ g) z₀ (hf.comp hg) =
      analyticOrderAt f (g z₀) hf *
        analyticOrderAt (g · - g z₀) z₀ (hg.fun_sub analyticAt_const) := by
  have hg' : AnalyticAt 𝕜 (g · - g z₀) z₀ := hg.fun_sub analyticAt_const
  by_cases hg_nc : EventuallyConst g (𝓝 z₀)
  · -- If `g` is eventually constant, both sides are either `⊤` or `0`.
    have h₁ := (eventuallyConst_iff_analyticOrderAt_sub_eq_top hg).mp hg_nc
    have h₂ := (eventuallyConst_iff_analyticOrderAt_sub_eq_top (hf.comp hg)).mp (hg_nc.comp f)
    rw [h₁]
    by_cases hf' : f (g z₀) = 0
    · rw [ENat.mul_top (hf.analyticOrderAt_ne_zero.mpr hf')]
      exact (analyticOrderAt_sub_apply_of_eq_zero (hf.comp hg) hf').symm.trans h₂
    · rw [hf.analyticOrderAt_eq_zero.mpr hf', zero_mul]
      exact (hf.comp hg).analyticOrderAt_eq_zero.mpr hf'
  by_cases hf' : analyticOrderAt f (g z₀) hf = ⊤
  · -- If `f` is eventually constant but `g` is not, we have `⊤ = ⊤ * (non-zero thing)`
    have h₁ : analyticOrderAt (f ∘ g) z₀ (hf.comp hg) = ⊤ :=
      (analyticOrderAt_eq_top (hf.comp hg)).mpr
        (EventuallyEq.comp_tendsto ((analyticOrderAt_eq_top hf).mp hf') hg.continuousAt)
    have h₂ : analyticOrderAt (g · - g z₀) z₀ hg' ≠ 0 := by
      rw [AnalyticAt.analyticOrderAt_ne_zero]
      simp
    rw [h₁, hf', ENat.top_mul h₂]
  · -- The interesting case: both orders are finite. First unpack the data:
    rw [eventuallyConst_iff_analyticOrderAt_sub_eq_top hg] at hg_nc
    obtain ⟨r, hr⟩ := ENat.ne_top_iff_exists.mp hf'
    obtain ⟨s, hs⟩ := ENat.ne_top_iff_exists.mp hg_nc
    rw [← hr, ← hs, ← ENat.natCast_mul, (hf.comp hg).analyticOrderAt_eq_natCast]
    rw [Eq.comm, hf.analyticOrderAt_eq_natCast] at hr
    rcases hr with ⟨F, hFa, hFne, hfF⟩
    rw [Eq.comm, AnalyticAt.analyticOrderAt_eq_natCast] at hs
    rcases hs with ⟨G, hGa, hGne, hgG⟩
    -- Now write `f ∘ g` locally as the product of `(z - z₀) ^ (r * s)` and the
    -- non-vanishing analytic function `fun z ↦ (G z) ^ r • F (g z)`.
    refine ⟨fun z ↦ (G z) ^ r • F (g z), by fun_prop, by aesop, ?_⟩
    filter_upwards [EventuallyEq.comp_tendsto hfF hg.continuousAt, hgG] with z hfz hgz
    simp only [hfz, Function.comp_def, hgz, smul_eq_mul, mul_pow, mul_smul, mul_comm r s, pow_mul]

/-- If `f` is analytic at `g z₀`, `g` is analytic at `z₀`, and `g' z₀ ≠ 0`, then the analytic order
of `f ∘ g` at `z₀` is the analytic order of `f` at `g z₀`. -/
lemma analyticOrderAt_comp_of_deriv_ne_zero (hf : AnalyticAt 𝕜 f (g z₀)) (hg : AnalyticAt 𝕜 g z₀)
    (hg' : deriv g z₀ ≠ 0) :
    analyticOrderAt (f ∘ g) z₀ (hf.comp hg) = analyticOrderAt f (g z₀) hf := by
  rw [hf.analyticOrderAt_comp hg, hg.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hg', mul_one]

end comp

/-!
## Level Sets of the Order Function
-/

namespace AnalyticOnNhd

variable {U : Set 𝕜} {f : 𝕜 → E}

/-- The set where an analytic function has infinite order is clopen in its domain of analyticity. -/
theorem isClopen_setOfPred_analyticOrderAt_eq_top (hf : AnalyticOnNhd 𝕜 f U) :
    IsClopen {u : U | analyticOrderAt f u.1 (hf u.1 u.2) = ⊤} := by
  have hset : {u : U | analyticOrderAt f u.1 (hf u.1 u.2) = ⊤} =
      {u : U | ∀ᶠ z in 𝓝 u.1, f z = 0} :=
    Set.ext fun u ↦ analyticOrderAt_eq_top (hf u.1 u.2)
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
      have hw₀' : ∀ᶠ y in 𝓝 w.1, f y = 0 := hw₀
      by_cases h₁w : w = z
      · subst h₁w
        exact hz hw₀
      · exact h₁t' w hw (Subtype.coe_ne_coe.mpr h₁w) hw₀'.self_of_nhds
  · apply isOpen_iff_forall_mem_open.mpr
    intro z hz
    have hz' : ∀ᶠ y in 𝓝 z.1, f y = 0 := hz
    obtain ⟨t', h₁t', h₂t', h₃t'⟩ := eventually_nhds_iff.1 hz'
    refine ⟨Subtype.val ⁻¹' t', fun w hw ↦ ?_, isOpen_induced h₂t', h₃t'⟩
    change ∀ᶠ y in 𝓝 w.1, f y = 0
    exact eventually_nhds_iff.2 ⟨t', h₁t', h₂t', hw⟩

@[deprecated (since := "2026-07-09")]
alias isClopen_setOf_analyticOrderAt_eq_top := isClopen_setOfPred_analyticOrderAt_eq_top

/-- On a connected set, there exists a point where a meromorphic function `f` has finite order iff
`f` has finite order at every point. -/
theorem exists_analyticOrderAt_ne_top_iff_forall (hf : AnalyticOnNhd 𝕜 f U) (hU : IsConnected U) :
    (∃ u : U, analyticOrderAt f u.1 (hf u.1 u.2) ≠ ⊤) ↔
      (∀ u : U, analyticOrderAt f u.1 (hf u.1 u.2) ≠ ⊤) := by
  have : ConnectedSpace U := Subtype.connectedSpace hU
  obtain ⟨v⟩ : Nonempty U := inferInstance
  suffices (∀ (u : U), analyticOrderAt f u.1 (hf u.1 u.2) ≠ ⊤) ∨
      ∀ (u : U), analyticOrderAt f u.1 (hf u.1 u.2) = ⊤ by tauto
  simpa [Set.eq_empty_iff_forall_notMem, Set.eq_univ_iff_forall] using
      isClopen_iff.1 hf.isClopen_setOfPred_analyticOrderAt_eq_top

/-- On a preconnected set, a meromorphic function has finite order at one point if it has finite
order at another point. -/
theorem analyticOrderAt_ne_top_of_isPreconnected {x y : 𝕜} (hf : AnalyticOnNhd 𝕜 f U)
    (hU : IsPreconnected U) (h₁x : x ∈ U) (hy : y ∈ U)
    (h₂x : analyticOrderAt f x (hf x h₁x) ≠ ⊤) :
    analyticOrderAt f y (hf y hy) ≠ ⊤ :=
  (hf.exists_analyticOrderAt_ne_top_iff_forall ⟨nonempty_of_mem h₁x, hU⟩).1 ⟨⟨x, h₁x⟩, h₂x⟩
    ⟨y, hy⟩

/-- The set where an analytic function has zero or infinite order is discrete within its domain of
analyticity. -/
theorem codiscrete_setOfPred_analyticOrderAt_eq_zero_or_top (hf : AnalyticOnNhd 𝕜 f U) :
    {u : U | analyticOrderAt f u.1 (hf u.1 u.2) = 0 ∨ analyticOrderAt f u.1 (hf u.1 u.2) = ⊤} ∈
      Filter.codiscrete U := by
  have hset : {u : U | analyticOrderAt f u.1 (hf u.1 u.2) = 0 ∨
      analyticOrderAt f u.1 (hf u.1 u.2) = ⊤} = {u : U | f u.1 ≠ 0 ∨ ∀ᶠ z in 𝓝 u.1, f z = 0} :=
    Set.ext fun u ↦ or_congr (hf u.1 u.2).analyticOrderAt_eq_zero
      (analyticOrderAt_eq_top (hf u.1 u.2))
  rw [hset]
  simp_rw [mem_codiscrete_subtype_iff_mem_codiscreteWithin, mem_codiscreteWithin,
    disjoint_principal_right]
  intro x hx
  rcases (hf x hx).eventually_eq_zero_or_eventually_ne_zero with h₁f | h₁f
  · filter_upwards [eventually_nhdsWithin_of_eventually_nhds h₁f.eventually_nhds] with a ha
    simp [ha]
  · filter_upwards [h₁f] with a ha
    simp +contextual [ha]

@[deprecated (since := "2026-07-09")]
alias codiscrete_setOf_analyticOrderAt_eq_zero_or_top :=
  codiscrete_setOfPred_analyticOrderAt_eq_zero_or_top

/--
The set where an analytic function has zero or infinite order is discrete within its domain of
analyticity.
-/
theorem codiscreteWithin_setOfPred_analyticOrderAt_eq_zero_or_top (hf : AnalyticOnNhd 𝕜 f U) :
    {u : 𝕜 | ∃ hu : u ∈ U,
      analyticOrderAt f u (hf u hu) = 0 ∨ analyticOrderAt f u (hf u hu) = ⊤} ∈
        codiscreteWithin U := by
  rw [mem_codiscreteWithin]
  intro x hx
  rw [disjoint_principal_right]
  rcases (hf x hx).eventually_eq_zero_or_eventually_ne_zero with h₁f | h₁f
  · filter_upwards [eventually_nhdsWithin_of_eventually_nhds h₁f.eventually_nhds] with a ha
    rintro ⟨haU, haS⟩
    exact haS ⟨haU, Or.inr ((analyticOrderAt_eq_top (hf a haU)).mpr ha)⟩
  · filter_upwards [h₁f] with a ha
    rintro ⟨haU, haS⟩
    exact haS ⟨haU, Or.inl ((hf a haU).analyticOrderAt_eq_zero.mpr ha)⟩

@[deprecated (since := "2026-07-09")]
alias codiscreteWithin_setOf_analyticOrderAt_eq_zero_or_top :=
  codiscreteWithin_setOfPred_analyticOrderAt_eq_zero_or_top

/--
If an analytic function `f` is not constantly zero on a connected set `U`, then its set of zeros is
codiscrete within `U`.

See `AnalyticOnNhd.preimage_mem_codiscreteWithin` for a more general statement in preimages of
codiscrete sets.
-/
theorem preimage_zero_mem_codiscreteWithin {x : 𝕜} (h₁f : AnalyticOnNhd 𝕜 f U) (h₂f : f x ≠ 0)
    (hx : x ∈ U) (hU : IsConnected U) :
    f ⁻¹' {0}ᶜ ∈ codiscreteWithin U := by
  rcases h₁f.eqOn_zero_or_eventually_ne_zero_of_preconnected hU.isPreconnected with hzero | hne
  · exact (h₂f (hzero hx)).elim
  · exact hne

/--
If an analytic function `f` is not constantly zero on `𝕜`, then its set of zeros is codiscrete.

See `AnalyticOnNhd.preimage_mem_codiscreteWithin` for a more general statement in preimages of
codiscrete sets.
-/
theorem preimage_zero_mem_codiscrete [ConnectedSpace 𝕜] {x : 𝕜} (hf : AnalyticOnNhd 𝕜 f Set.univ)
    (hx : f x ≠ 0) :
    f ⁻¹' {0}ᶜ ∈ codiscrete 𝕜 :=
  hf.preimage_zero_mem_codiscreteWithin hx trivial isConnected_univ

lemma analyticOrderAt_eq_top_iff_eq_zero [PreconnectedSpace 𝕜] {f : 𝕜 → E} (z : 𝕜)
    (hf : ∀ z₀, AnalyticAt 𝕜 f z₀) : analyticOrderAt f z (hf z) = ⊤ ↔ f = 0 := by
  refine (analyticOrderAt_eq_top (hf z)).trans
    ⟨fun h ↦ eqOn_univ .. |>.mp ?_, by simp +contextual⟩
  apply eqOn_zero_of_preconnected_of_frequently_eq_zero (fun z _ ↦ hf z) isPreconnected_univ trivial
  exact hf z |>.frequently_eq_iff_eventually_eq analyticAt_const |>.mpr h

lemma _root_.IsOpen.forall_analyticOrderAt_eq_top_iff_eqOn_zero {s : Set 𝕜} (hs : IsOpen s)
    (f : 𝕜 → E) (hf : AnalyticOnNhd 𝕜 f s) :
    (∀ z (hz : z ∈ s), analyticOrderAt f z (hf z hz) = ⊤) ↔ EqOn f 0 s := by
  refine ⟨fun h z hz ↦ EventuallyEq.eq_of_nhds
    ((analyticOrderAt_eq_top (hf z hz)).mp (h z hz)), fun hzero z hz ↦ ?_⟩
  apply (analyticOrderAt_eq_top (hf z hz)).mpr
  filter_upwards [hs.mem_nhds hz]
  exact fun _ ↦ hzero.eq_of_mem

end AnalyticOnNhd
