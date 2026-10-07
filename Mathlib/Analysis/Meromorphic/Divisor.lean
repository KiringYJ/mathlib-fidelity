/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Meromorphic.IsolatedZeros
public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Topology.LocallyFinsupp

/-!
# The Divisor of a meromorphic function

This file defines the divisor of a meromorphic function and proves the most basic lemmas about those
divisors. The divisor of `f` on `U` is defined when `f` is meromorphic on `U` and has finite order
at every point of `U`, and it maps a point of `U` to the order of `f` there. The pole divisor
`MeromorphicOn.poleDivisor`, which records only the orders of the poles, is defined for every
function that is meromorphic on `U`, including one that vanishes on an open subset of `U`. The lemma
`MeromorphicOn.divisor_restrict` guarantees compatibility between restrictions of divisors and of
meromorphic functions to subsets of their domain of definition.
-/

@[expose] public section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {U : Set 𝕜} {z : 𝕜}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

open Filter Metric

open scoped Topology

namespace MeromorphicOn

/-!
## Definition of the Divisor
-/

open scoped Classical in
/--
The divisor of a function `f` that is meromorphic on `U` and has finite order at every point of
`U`, mapping a point `z ∈ U` to the order of `f` at `z`. The proof `h` of finite order determines
the meromorphy proof. A function that vanishes on a punctured neighborhood of a point of `U` has
order `⊤` there and no divisor; its pole divisor `MeromorphicOn.poleDivisor` exists.
-/
noncomputable def divisor (f : 𝕜 → E) (U : Set 𝕜) {hf : MeromorphicOn f U}
    (h : ∀ z (hz : z ∈ U), meromorphicOrderAt f z (hf z hz) ≠ ⊤) :
    Function.locallyFinsuppWithin U ℤ where
  toFun z := if hz : z ∈ U then (meromorphicOrderAt f z (hf z hz)).untop (h z hz) else 0
  supportWithinDomain' z hz := by
    by_contra h₂z
    simp [h₂z] at hz
  supportLocallyFiniteWithinDomain' := by
    rw [← supportDiscreteWithin_iff_locallyFiniteWithin fun z hz ↦ by
      by_contra h₂z
      simp [h₂z] at hz]
    filter_upwards [hf.codiscreteWithin_setOfPred_meromorphicOrderAt_eq_zero_or_top]
      with z ⟨hz, h'⟩
    rcases h' with h' | h'
    · simp [hz, h']
    · exact absurd h' (h z hz)

open scoped Classical in
/-- Definition of the divisor -/
theorem divisor_def (f : 𝕜 → E) (U : Set 𝕜) {hf : MeromorphicOn f U}
    (h : ∀ z (hz : z ∈ U), meromorphicOrderAt f z (hf z hz) ≠ ⊤) :
    divisor f U h z =
      if hz : z ∈ U then (meromorphicOrderAt f z (hf z hz)).untop (h z hz) else 0 :=
  rfl

/--
Simplifier lemma: on `U`, the divisor of a function `f` evaluates to the order of `f`.
-/
@[simp]
lemma divisor_apply {f : 𝕜 → E} (hf : MeromorphicOn f U)
    {h : ∀ z (hz : z ∈ U), meromorphicOrderAt f z (hf z hz) ≠ ⊤} (hz : z ∈ U) :
    divisor f U h z = (meromorphicOrderAt f z (hf z hz)).untop (h z hz) := by
  simp [divisor_def, hz]

/-- On `U`, the divisor of a function `f`, as an element of `WithTop ℤ`, is the order of `f`. -/
lemma coe_divisor_apply {f : 𝕜 → E} (hf : MeromorphicOn f U)
    {h : ∀ z (hz : z ∈ U), meromorphicOrderAt f z (hf z hz) ≠ ⊤} (hz : z ∈ U) :
    (divisor f U h z : WithTop ℤ) = meromorphicOrderAt f z (hf z hz) := by
  simp [divisor_apply hf hz]

/-- The divisor of `f` vanishes at a point where the order of `f` is zero. -/
lemma divisor_apply_eq_zero {f : 𝕜 → E} {hf : MeromorphicOn f U}
    {h : ∀ z (hz : z ∈ U), meromorphicOrderAt f z (hf z hz) ≠ ⊤} {hz' : MeromorphicAt f z}
    (h₀ : meromorphicOrderAt f z hz' = 0) :
    divisor f U h z = 0 := by
  by_cases hz : z ∈ U
  · rw [divisor_apply hf hz, WithTop.untop_eq_iff]
    simpa using h₀
  · exact Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hz

/-- The divisor of an analytic function at a point of `U` is its analytic order there. -/
lemma AnalyticOnNhd.coe_divisor_apply {f : 𝕜 → E} (hf : AnalyticOnNhd 𝕜 f U)
    {h : ∀ z (hz : z ∈ U), meromorphicOrderAt f z (hf.meromorphicOn z hz) ≠ ⊤} (hz : z ∈ U) :
    (divisor f U h z : WithTop ℤ) = (analyticOrderAt f z (hf z hz)).map (↑) := by
  rw [MeromorphicOn.coe_divisor_apply hf.meromorphicOn hz, (hf z hz).meromorphicOrderAt_eq]

/-!
## Support Properties
-/

/--
Special case of `Function.locallyFinsuppWithin.finiteSupport` that frequently shows in complex
analysis: Divisors on spheres have finite support.
-/
lemma _root_.divisor_sphere_support_finite [ProperSpace 𝕜] {f : 𝕜 → E} {R : ℝ} {c : 𝕜}
    {hf : MeromorphicOn f (sphere c R)}
    {h : ∀ z (hz : z ∈ sphere c R), meromorphicOrderAt f z (hf z hz) ≠ ⊤} :
    (divisor f (sphere c R) h).support.Finite :=
  (divisor f (sphere c R) h).finiteSupport (isCompact_sphere c R)

/--
If `f` is meromorphic on a compact set `U` and `V ⊆ U`, then the divisor of `f` on `V` has finite
support.
-/
lemma divisor_support_finite_of_subset {f : 𝕜 → E} {V : Set 𝕜} (hf : MeromorphicOn f U)
    (hU : IsCompact U) (hV : V ⊆ U)
    {h : ∀ z (hz : z ∈ V), meromorphicOrderAt f z ((hf.mono_set hV) z hz) ≠ ⊤} :
    (divisor f V h).support.Finite := by
  apply (hU.finite_sdiff_of_mem_codiscreteWithin
    hf.codiscreteWithin_setOfPred_meromorphicOrderAt_eq_zero_or_top).subset
  intro z hz
  have hzV := (divisor f V h).supportWithinDomain hz
  have h₂ := coe_divisor_apply (h := h) (hf.mono_set hV) hzV
  refine ⟨hV hzV, fun ⟨_, h'⟩ ↦ ?_⟩
  rcases h' with h' | h'
  · exact hz (by exact_mod_cast h₂.trans h')
  · exact h z hzV h'

/--
Special case of `MeromorphicOn.divisor_support_finite_of_subset` that frequently shows in complex
analysis, where `U` is a closed ball and `V` is its interior.
-/
lemma divisor_ball_support_finite [ProperSpace 𝕜] {f : 𝕜 → E} {R : ℝ} {c : 𝕜}
    (hf : MeromorphicOn f (closedBall c R))
    {h : ∀ z (hz : z ∈ ball c R),
      meromorphicOrderAt f z ((hf.mono_set ball_subset_closedBall) z hz) ≠ ⊤} :
    (divisor f (ball c R) h).support.Finite :=
  hf.divisor_support_finite_of_subset (isCompact_closedBall c R) ball_subset_closedBall

/-!
## Congruence Lemmas
-/

/--
Two divisors on `U` agree if the orders of the two functions agree at every point of `U`.
-/
theorem divisor_congr {f₁ f₂ : 𝕜 → E} {hf₁ : MeromorphicOn f₁ U} {hf₂ : MeromorphicOn f₂ U}
    {h₁ : ∀ z (hz : z ∈ U), meromorphicOrderAt f₁ z (hf₁ z hz) ≠ ⊤}
    {h₂ : ∀ z (hz : z ∈ U), meromorphicOrderAt f₂ z (hf₂ z hz) ≠ ⊤}
    (h : ∀ z (hz : z ∈ U),
      meromorphicOrderAt f₁ z (hf₁ z hz) = meromorphicOrderAt f₂ z (hf₂ z hz)) :
    divisor f₁ U h₁ = divisor f₂ U h₂ := by
  ext z
  by_cases hz : z ∈ U
  · exact_mod_cast (coe_divisor_apply hf₁ hz).trans ((h z hz).trans (coe_divisor_apply hf₂ hz).symm)
  · simp [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hz]

/--
If `f₁` is meromorphic on `U`, if `f₂` agrees with `f₁` on a codiscrete subset of `U` and outside of
`U`, then `f₁` and `f₂` induce the same divisors on `U`.
-/
theorem divisor_congr_codiscreteWithin_of_eqOn_compl {f₁ f₂ : 𝕜 → E} (hf₁ : MeromorphicOn f₁ U)
    (h₁ : f₁ =ᶠ[codiscreteWithin U] f₂) (h₂ : Set.EqOn f₁ f₂ Uᶜ)
    {h₁' : ∀ z (hz : z ∈ U), meromorphicOrderAt f₁ z (hf₁ z hz) ≠ ⊤} {hf₂ : MeromorphicOn f₂ U}
    {h₂' : ∀ z (hz : z ∈ U), meromorphicOrderAt f₂ z (hf₂ z hz) ≠ ⊤} :
    divisor f₁ U h₁' = divisor f₂ U h₂' := by
  refine divisor_congr fun x hx ↦ meromorphicOrderAt_congr (hf₁ x hx) ?_
  simp_rw [EventuallyEq, Filter.Eventually, mem_codiscreteWithin, disjoint_principal_right] at h₁
  filter_upwards [h₁ x hx] with a ha
  simp at ha
  tauto

/-
If two meromorphic functions agree outside a set codiscrete within a perfect set, then they define
the same divisors there.
-/
theorem divisor_of_eventuallyEq_codiscreteWithin_preperfect {f₁ f₂ : 𝕜 → E}
    (hf₁ : MeromorphicOn f₁ U) (hf₂ : MeromorphicOn f₂ U) (hU : Preperfect U)
    (h : f₁ =ᶠ[codiscreteWithin U] f₂)
    {h₁ : ∀ z (hz : z ∈ U), meromorphicOrderAt f₁ z (hf₁ z hz) ≠ ⊤}
    {h₂ : ∀ z (hz : z ∈ U), meromorphicOrderAt f₂ z (hf₂ z hz) ≠ ⊤} :
    divisor f₁ U h₁ = divisor f₂ U h₂ :=
  divisor_congr fun z hz ↦ meromorphicOrderAt_congr (hf₁ z hz)
    ((hf₁ z hz).eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect (hf₂ z hz) hz hU h)

/--
If two functions differ only on a discrete set of an open, then they induce the same divisors.
-/
theorem divisor_congr_codiscreteWithin {f₁ f₂ : 𝕜 → E} (h₁ : f₁ =ᶠ[codiscreteWithin U] f₂)
    (h₂ : IsOpen U) {hf₁ : MeromorphicOn f₁ U}
    {h₁' : ∀ z (hz : z ∈ U), meromorphicOrderAt f₁ z (hf₁ z hz) ≠ ⊤} {hf₂ : MeromorphicOn f₂ U}
    {h₂' : ∀ z (hz : z ∈ U), meromorphicOrderAt f₂ z (hf₂ z hz) ≠ ⊤} :
    divisor f₁ U h₁' = divisor f₂ U h₂' := by
  refine divisor_congr fun x hx ↦ meromorphicOrderAt_congr (hf₁ x hx) ?_
  simp_rw [EventuallyEq, Filter.Eventually, mem_codiscreteWithin, disjoint_principal_right] at h₁
  have : U ∈ 𝓝[≠] x := by
    apply mem_nhdsWithin.mpr
    use U, h₂, hx, Set.inter_subset_left
  filter_upwards [this, h₁ x hx] with a h₁a h₂a
  simp only [Set.mem_compl_iff, Set.mem_sdiff, Set.mem_ofPred_eq, not_and] at h₂a
  tauto

/-!
## Divisors of Analytic Functions
-/

/-- Analytic functions have non-negative divisors. -/
theorem AnalyticOnNhd.divisor_nonneg {f : 𝕜 → E} (hf : AnalyticOnNhd 𝕜 f U)
    {h : ∀ z (hz : z ∈ U), meromorphicOrderAt f z (hf.meromorphicOn z hz) ≠ ⊤} :
    0 ≤ MeromorphicOn.divisor f U h := by
  intro x
  by_cases hx : x ∈ U
  · have := (hf x hx).meromorphicOrderAt_nonneg
    rw [← MeromorphicOn.coe_divisor_apply hf.meromorphicOn hx] at this
    exact_mod_cast this
  simp [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hx]

/--
The divisor of a constant function is `0`. The constant is nonzero unless `U` is empty, since the
order is finite.
-/
@[simp]
theorem divisor_const (e : E) {hf : MeromorphicOn (fun _ ↦ e) U}
    {h : ∀ z (hz : z ∈ U), meromorphicOrderAt (fun _ ↦ e) z (hf z hz) ≠ ⊤} :
    divisor (fun _ ↦ e) U h = 0 := by
  classical
  ext x
  by_cases hx : x ∈ U
  · have := h x hx
    have h₂ := coe_divisor_apply hf hx (h := h)
    rw [meromorphicOrderAt_const] at this h₂
    split_ifs at this h₂ with he
    · exact absurd rfl this
    · exact_mod_cast h₂
  · simp [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hx]

/--
The divisor of a constant function is `0`.
-/
@[simp]
theorem divisor_intCast (n : ℤ) {hf : MeromorphicOn (n : 𝕜 → 𝕜) U}
    {h : ∀ z (hz : z ∈ U), meromorphicOrderAt (n : 𝕜 → 𝕜) z (hf z hz) ≠ ⊤} :
    divisor (n : 𝕜 → 𝕜) U h = 0 := divisor_const (n : 𝕜)

/--
The divisor of a constant function is `0`.
-/
@[simp]
theorem divisor_natCast (n : ℕ) {hf : MeromorphicOn (n : 𝕜 → 𝕜) U}
    {h : ∀ z (hz : z ∈ U), meromorphicOrderAt (n : 𝕜 → 𝕜) z (hf z hz) ≠ ⊤} :
    divisor (n : 𝕜 → 𝕜) U h = 0 := divisor_const (n : 𝕜)

/--
The divisor of a constant function is `0`.
-/
@[simp] theorem divisor_ofNat (n : ℕ) {hf : MeromorphicOn (ofNat(n) : 𝕜 → 𝕜) U}
    {h : ∀ z (hz : z ∈ U), meromorphicOrderAt (ofNat(n) : 𝕜 → 𝕜) z (hf z hz) ≠ ⊤} :
    divisor (ofNat(n) : 𝕜 → 𝕜) U h = 0 :=
  divisor_const _

/-!
## The Pole Divisor
-/

open scoped Classical in
/--
The pole divisor of a function `f` that is meromorphic on `U`, mapping a point `z ∈ U` to the order
of the pole of `f` at `z`, which is `0` where `f` has no pole. Unlike the divisor, it exists for
every function that is meromorphic on `U`: a function that vanishes on a punctured neighborhood of a
point has no pole there. It is the negative part of the divisor where that is defined
(`MeromorphicOn.poleDivisor_eq_negPart_divisor`).
-/
noncomputable def poleDivisor (f : 𝕜 → E) (U : Set 𝕜) (hf : MeromorphicOn f U := by fun_prop) :
    Function.locallyFinsuppWithin U ℤ where
  toFun z := if hz : z ∈ U then
    -(min (meromorphicOrderAt f z (hf z hz)) 0).untop
      (ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_right _ 0)) else 0
  supportWithinDomain' z hz := by
    by_contra h₂z
    simp [h₂z] at hz
  supportLocallyFiniteWithinDomain' := by
    rw [← supportDiscreteWithin_iff_locallyFiniteWithin fun z hz ↦ by
      by_contra h₂z
      simp [h₂z] at hz]
    filter_upwards [hf.codiscreteWithin_setOfPred_meromorphicOrderAt_eq_zero_or_top]
      with z ⟨hz, h'⟩
    rcases h' with h' | h' <;> simp [hz, h']

open scoped Classical in
/-- Definition of the pole divisor -/
theorem poleDivisor_def (f : 𝕜 → E) (U : Set 𝕜) (hf : MeromorphicOn f U) :
    poleDivisor f U hf z = if hz : z ∈ U then -(min (meromorphicOrderAt f z (hf z hz)) 0).untop
      (ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_right _ 0)) else 0 :=
  rfl

/-- On `U`, the pole divisor of `f` is the negative of the minimum of the order and `0`. -/
lemma coe_poleDivisor_apply {f : 𝕜 → E} (hf : MeromorphicOn f U) (hz : z ∈ U) :
    (poleDivisor f U hf z : WithTop ℤ) = -min (meromorphicOrderAt f z (hf z hz)) 0 := by
  simp only [poleDivisor_def, hz, ↓reduceDIte]
  rw [WithTop.LinearOrderedAddCommGroup.coe_neg, WithTop.coe_untop]

/-- The minimum of the order and `0` is the negative of the pole divisor. -/
private lemma min_meromorphicOrderAt_zero {f : 𝕜 → E} (hf : MeromorphicOn f U) (hz : z ∈ U) :
    min (meromorphicOrderAt f z (hf z hz)) 0 = ((-poleDivisor f U hf z : ℤ) : WithTop ℤ) := by
  rw [WithTop.LinearOrderedAddCommGroup.coe_neg, coe_poleDivisor_apply hf hz, neg_neg]

/-- The pole divisor is non-negative. -/
theorem poleDivisor_nonneg {f : 𝕜 → E} (hf : MeromorphicOn f U) : 0 ≤ poleDivisor f U hf := by
  intro z
  by_cases hz : z ∈ U
  · have h₁ := min_meromorphicOrderAt_zero hf hz
    have h₂ : ((-poleDivisor f U hf z : ℤ) : WithTop ℤ) ≤ 0 := h₁ ▸ min_le_right _ _
    have : -poleDivisor f U hf z ≤ 0 := by exact_mod_cast h₂
    simp only [Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply]
    omega
  · simp [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hz]

/-- Where the divisor is defined, the pole divisor is its negative part. -/
theorem poleDivisor_eq_negPart_divisor {f : 𝕜 → E} {hf : MeromorphicOn f U}
    (h : ∀ z (hz : z ∈ U), meromorphicOrderAt f z (hf z hz) ≠ ⊤) :
    poleDivisor f U hf = (divisor f U h)⁻ := by
  ext z
  by_cases hz : z ∈ U
  · have h₁ := min_meromorphicOrderAt_zero hf hz
    rw [← coe_divisor_apply hf hz (h := h), ← WithTop.coe_zero, ← WithTop.coe_min,
      WithTop.coe_inj] at h₁
    rw [Function.locallyFinsuppWithin.negPart_apply, negPart_def]
    omega
  · simp [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hz]

/-- Two pole divisors on `U` agree if the minima of the orders with `0` agree at every point of
`U`. -/
private theorem poleDivisor_congr' {f₁ f₂ : 𝕜 → E} {hf₁ : MeromorphicOn f₁ U}
    {hf₂ : MeromorphicOn f₂ U}
    (h : ∀ z (hz : z ∈ U), min (meromorphicOrderAt f₁ z (hf₁ z hz)) 0 =
      min (meromorphicOrderAt f₂ z (hf₂ z hz)) 0) :
    poleDivisor f₁ U hf₁ = poleDivisor f₂ U hf₂ := by
  ext z
  by_cases hz : z ∈ U
  · exact_mod_cast (coe_poleDivisor_apply hf₁ hz).trans
      ((congrArg (-·) (h z hz)).trans (coe_poleDivisor_apply hf₂ hz).symm)
  · simp [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hz]

/-- Two pole divisors on `U` agree if the orders of the two functions agree at every point of
`U`. -/
theorem poleDivisor_congr {f₁ f₂ : 𝕜 → E} {hf₁ : MeromorphicOn f₁ U} {hf₂ : MeromorphicOn f₂ U}
    (h : ∀ z (hz : z ∈ U),
      meromorphicOrderAt f₁ z (hf₁ z hz) = meromorphicOrderAt f₂ z (hf₂ z hz)) :
    poleDivisor f₁ U hf₁ = poleDivisor f₂ U hf₂ :=
  poleDivisor_congr' fun z hz ↦ by rw [h z hz]

/--
If two functions differ only on a discrete set of an open, then they induce the same pole divisors.
-/
theorem poleDivisor_congr_codiscreteWithin {f₁ f₂ : 𝕜 → E} (h₁ : f₁ =ᶠ[codiscreteWithin U] f₂)
    (h₂ : IsOpen U) {hf₁ : MeromorphicOn f₁ U} {hf₂ : MeromorphicOn f₂ U} :
    poleDivisor f₁ U hf₁ = poleDivisor f₂ U hf₂ := by
  refine poleDivisor_congr fun x hx ↦ meromorphicOrderAt_congr (hf₁ x hx) ?_
  simp_rw [EventuallyEq, Filter.Eventually, mem_codiscreteWithin, disjoint_principal_right] at h₁
  have : U ∈ 𝓝[≠] x := by
    apply mem_nhdsWithin.mpr
    use U, h₂, hx, Set.inter_subset_left
  filter_upwards [this, h₁ x hx] with a h₁a h₂a
  simp only [Set.mem_compl_iff, Set.mem_sdiff, Set.mem_ofPred_eq, not_and] at h₂a
  tauto

/-- A function that is analytic on a neighborhood of `U` has no poles on `U`. -/
theorem AnalyticOnNhd.poleDivisor_eq_zero {f : 𝕜 → E} (hf : AnalyticOnNhd 𝕜 f U) :
    poleDivisor f U hf.meromorphicOn = 0 := by
  ext z
  by_cases hz : z ∈ U
  · have h₁ := min_meromorphicOrderAt_zero hf.meromorphicOn hz
    rw [min_eq_right (hf z hz).meromorphicOrderAt_nonneg, ← WithTop.coe_zero, WithTop.coe_inj]
      at h₁
    simp only [Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply]
    omega
  · simp [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hz]

/-!
## Behavior under Standard Operations
-/

/--
The divisor of `f₁ + f₂` is larger than or equal to the minimum of the divisors of `f₁` and `f₂`,
respectively.
-/
theorem min_divisor_le_divisor_add {f₁ f₂ : 𝕜 → E} {z : 𝕜} {U : Set 𝕜} (hf₁ : MeromorphicOn f₁ U)
    (hf₂ : MeromorphicOn f₂ U) (h₁z : z ∈ U)
    (h₁ : ∀ z (hz : z ∈ U), meromorphicOrderAt f₁ z (hf₁ z hz) ≠ ⊤)
    (h₂ : ∀ z (hz : z ∈ U), meromorphicOrderAt f₂ z (hf₂ z hz) ≠ ⊤)
    {h₃ : ∀ z (hz : z ∈ U), meromorphicOrderAt (f₁ + f₂) z ((hf₁.add hf₂) z hz) ≠ ⊤} :
    min (divisor f₁ U h₁ z) (divisor f₂ U h₂ z) ≤ divisor (f₁ + f₂) U h₃ z := by
  have := meromorphicOrderAt_add (hf₁ z h₁z) (hf₂ z h₁z)
  rw [← coe_divisor_apply hf₁ h₁z (h := h₁), ← coe_divisor_apply hf₂ h₁z (h := h₂),
    ← coe_divisor_apply (hf₁.add hf₂) h₁z (h := h₃)] at this
  exact_mod_cast this

/--
The pole divisor of `f₁ + f₂` is smaller than or equal to the maximum of the pole divisors of `f₁`
and `f₂`, respectively.
-/
theorem poleDivisor_add_le_max {f₁ f₂ : 𝕜 → E} {U : Set 𝕜} (hf₁ : MeromorphicOn f₁ U)
    (hf₂ : MeromorphicOn f₂ U) :
    poleDivisor (f₁ + f₂) U (hf₁.add hf₂) ≤ max (poleDivisor f₁ U hf₁) (poleDivisor f₂ U hf₂) := by
  intro z
  by_cases hz : z ∈ U
  · have h := min_le_min_right 0 (meromorphicOrderAt_add (hf₁ z hz) (hf₂ z hz))
    rw [inf_inf_distrib_right, min_meromorphicOrderAt_zero hf₁ hz,
      min_meromorphicOrderAt_zero hf₂ hz, min_meromorphicOrderAt_zero (hf₁.add hf₂) hz] at h
    have h' : min (-poleDivisor f₁ U hf₁ z) (-poleDivisor f₂ U hf₂ z) ≤
        -poleDivisor (f₁ + f₂) U (hf₁.add hf₂) z := by exact_mod_cast h
    simp only [Function.locallyFinsuppWithin.max_apply]
    omega
  · simp [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hz]

/--
The pole divisor of `f₁ + f₂` is smaller than or equal to the sum of the pole divisors of `f₁` and
`f₂`, respectively.
-/
theorem poleDivisor_add_le_add {f₁ f₂ : 𝕜 → E} {U : Set 𝕜} (hf₁ : MeromorphicOn f₁ U)
    (hf₂ : MeromorphicOn f₂ U) :
    poleDivisor (f₁ + f₂) U (hf₁.add hf₂) ≤ poleDivisor f₁ U hf₁ + poleDivisor f₂ U hf₂ := by
  intro z
  have h₁ : poleDivisor (f₁ + f₂) U (hf₁.add hf₂) z ≤
      max (poleDivisor f₁ U hf₁) (poleDivisor f₂ U hf₂) z := poleDivisor_add_le_max hf₁ hf₂ z
  have h₂ : 0 ≤ poleDivisor f₁ U hf₁ z := poleDivisor_nonneg hf₁ z
  have h₃ : 0 ≤ poleDivisor f₂ U hf₂ z := poleDivisor_nonneg hf₂ z
  simp only [Function.locallyFinsuppWithin.max_apply, Function.locallyFinsuppWithin.coe_add,
    Pi.add_apply] at h₁ ⊢
  omega

/--
The pole divisor of `f₁ • f₂` is smaller than or equal to the sum of the pole divisors of `f₁` and
`f₂`, respectively.  Unlike the formula for the divisor, this holds without finiteness of the
orders: where one of the factors vanishes on a punctured neighborhood, so does the product.
-/
theorem poleDivisor_smul_le_add {f₁ : 𝕜 → 𝕜} {f₂ : 𝕜 → E} (hf₁ : MeromorphicOn f₁ U)
    (hf₂ : MeromorphicOn f₂ U) :
    poleDivisor (f₁ • f₂) U (hf₁.smul hf₂) ≤ poleDivisor f₁ U hf₁ + poleDivisor f₂ U hf₂ := by
  intro z
  by_cases hz : z ∈ U
  · have e₁ := coe_poleDivisor_apply hf₁ hz
    have e₂ := coe_poleDivisor_apply hf₂ hz
    have e₃ := coe_poleDivisor_apply (hf₁.smul hf₂) hz
    have h : meromorphicOrderAt (f₁ • f₂) z ((hf₁.smul hf₂) z hz) =
        meromorphicOrderAt f₁ z (hf₁ z hz) + meromorphicOrderAt f₂ z (hf₂ z hz) :=
      meromorphicOrderAt_smul (hf₁ z hz) (hf₂ z hz)
    have n₁ : 0 ≤ poleDivisor f₁ U hf₁ z := poleDivisor_nonneg hf₁ z
    have n₂ : 0 ≤ poleDivisor f₂ U hf₂ z := poleDivisor_nonneg hf₂ z
    rw [h] at e₃
    simp only [Function.locallyFinsuppWithin.coe_add, Pi.add_apply]
    generalize meromorphicOrderAt f₁ z (hf₁ z hz) = a at e₁ e₃
    generalize meromorphicOrderAt f₂ z (hf₂ z hz) = b at e₂ e₃
    cases a with
    | top =>
      have : poleDivisor (f₁ • f₂) U (hf₁.smul hf₂) z = 0 := by simpa using e₃
      omega
    | coe m =>
      cases b with
      | top =>
        have : poleDivisor (f₁ • f₂) U (hf₁.smul hf₂) z = 0 := by simpa using e₃
        omega
      | coe n =>
        have e₁' : poleDivisor f₁ U hf₁ z = -min m 0 := by exact_mod_cast e₁
        have e₂' : poleDivisor f₂ U hf₂ z = -min n 0 := by exact_mod_cast e₂
        have e₃' : poleDivisor (f₁ • f₂) U (hf₁.smul hf₂) z = -min (m + n) 0 := by
          exact_mod_cast e₃
        omega
  · simp [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hz]

/--
The pole divisor of `f₁ * f₂` is smaller than or equal to the sum of the pole divisors of `f₁` and
`f₂`, respectively.
-/
theorem poleDivisor_mul_le_add {f₁ f₂ : 𝕜 → 𝕜} (hf₁ : MeromorphicOn f₁ U)
    (hf₂ : MeromorphicOn f₂ U) :
    poleDivisor (f₁ * f₂) U (hf₁.mul hf₂) ≤ poleDivisor f₁ U hf₁ + poleDivisor f₂ U hf₂ :=
  poleDivisor_smul_le_add hf₁ hf₂

/--
If orders are finite, the divisor of the scalar product of two meromorphic functions is the sum of
the divisors.

See `MeromorphicOn.exists_meromorphicOrderAt_ne_top_iff_forall_mem` and
`MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected` for two convenient criteria to
guarantee conditions `h₂f₁` and `h₂f₂`.
-/
theorem divisor_smul {f₁ : 𝕜 → 𝕜} {f₂ : 𝕜 → E} (h₁f₁ : MeromorphicOn f₁ U)
    (h₁f₂ : MeromorphicOn f₂ U) (h₂f₁ : ∀ z (hz : z ∈ U), meromorphicOrderAt f₁ z (h₁f₁ z hz) ≠ ⊤)
    (h₂f₂ : ∀ z (hz : z ∈ U), meromorphicOrderAt f₂ z (h₁f₂ z hz) ≠ ⊤)
    {h : ∀ z (hz : z ∈ U), meromorphicOrderAt (f₁ • f₂) z ((h₁f₁.smul h₁f₂) z hz) ≠ ⊤} :
    divisor (f₁ • f₂) U h = divisor f₁ U h₂f₁ + divisor f₂ U h₂f₂ := by
  ext z
  by_cases hz : z ∈ U
  · have := meromorphicOrderAt_smul (h₁f₁ z hz) (h₁f₂ z hz)
    rw [← coe_divisor_apply h₁f₁ hz (h := h₂f₁), ← coe_divisor_apply h₁f₂ hz (h := h₂f₂),
      ← coe_divisor_apply (h₁f₁.smul h₁f₂) hz (h := h)] at this
    simp only [Function.locallyFinsuppWithin.coe_add, Pi.add_apply]
    exact_mod_cast this
  · simp [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hz]

/--
If orders are finite, the divisor of the scalar product of two meromorphic functions is the sum of
the divisors.
-/
theorem divisor_fun_smul {f₁ : 𝕜 → 𝕜} {f₂ : 𝕜 → E} (h₁f₁ : MeromorphicOn f₁ U)
    (h₁f₂ : MeromorphicOn f₂ U) (h₂f₁ : ∀ z (hz : z ∈ U), meromorphicOrderAt f₁ z (h₁f₁ z hz) ≠ ⊤)
    (h₂f₂ : ∀ z (hz : z ∈ U), meromorphicOrderAt f₂ z (h₁f₂ z hz) ≠ ⊤)
    {h : ∀ z (hz : z ∈ U), meromorphicOrderAt (fun z ↦ f₁ z • f₂ z) z
      ((h₁f₁.fun_smul h₁f₂) z hz) ≠ ⊤} :
    divisor (fun z ↦ f₁ z • f₂ z) U h = divisor f₁ U h₂f₁ + divisor f₂ U h₂f₂ :=
  divisor_smul h₁f₁ h₁f₂ h₂f₁ h₂f₂

/-- The divisor of a function is invariant when scaling of the function. -/
@[to_fun divisor_fun_const_smul]
theorem divisor_const_smul {f : 𝕜 → E} {s : 𝕜} {U : Set 𝕜} (hs : s ≠ 0)
    {hf : MeromorphicOn f U} (h : ∀ z (hz : z ∈ U), meromorphicOrderAt f z (hf z hz) ≠ ⊤)
    {hf' : MeromorphicOn (s • f) U}
    {h' : ∀ z (hz : z ∈ U), meromorphicOrderAt (s • f) z (hf' z hz) ≠ ⊤} :
    divisor (s • f) U h' = divisor f U h :=
  divisor_congr fun z hz ↦ meromorphicOrderAt_const_smul_eq_meromorphicOrderAt hs (hf' z hz)

/--
If orders are finite, the divisor of the product of two meromorphic functions is the sum of the
divisors.

See `MeromorphicOn.exists_meromorphicOrderAt_ne_top_iff_forall_mem` and
`MeromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected` for two convenient criteria to
guarantee conditions `h₂f₁` and `h₂f₂`.
-/
theorem divisor_mul {f₁ f₂ : 𝕜 → 𝕜} (h₁f₁ : MeromorphicOn f₁ U)
    (h₁f₂ : MeromorphicOn f₂ U) (h₂f₁ : ∀ z (hz : z ∈ U), meromorphicOrderAt f₁ z (h₁f₁ z hz) ≠ ⊤)
    (h₂f₂ : ∀ z (hz : z ∈ U), meromorphicOrderAt f₂ z (h₁f₂ z hz) ≠ ⊤)
    {h : ∀ z (hz : z ∈ U), meromorphicOrderAt (f₁ * f₂) z ((h₁f₁.mul h₁f₂) z hz) ≠ ⊤} :
    divisor (f₁ * f₂) U h = divisor f₁ U h₂f₁ + divisor f₂ U h₂f₂ :=
  divisor_smul h₁f₁ h₁f₂ h₂f₁ h₂f₂

/--
If orders are finite, the divisor of the product of two meromorphic functions is the sum of the
divisors.
-/
theorem divisor_fun_mul {f₁ f₂ : 𝕜 → 𝕜} (h₁f₁ : MeromorphicOn f₁ U)
    (h₁f₂ : MeromorphicOn f₂ U) (h₂f₁ : ∀ z (hz : z ∈ U), meromorphicOrderAt f₁ z (h₁f₁ z hz) ≠ ⊤)
    (h₂f₂ : ∀ z (hz : z ∈ U), meromorphicOrderAt f₂ z (h₁f₂ z hz) ≠ ⊤)
    {h : ∀ z (hz : z ∈ U), meromorphicOrderAt (fun z ↦ f₁ z * f₂ z) z
      ((h₁f₁.fun_mul h₁f₂) z hz) ≠ ⊤} :
    divisor (fun z ↦ f₁ z * f₂ z) U h = divisor f₁ U h₂f₁ + divisor f₂ U h₂f₂ :=
  divisor_smul h₁f₁ h₁f₂ h₂f₁ h₂f₂

open Finset in
/-- The case of `MeromorphicOn.divisor_prod` where every function of the family is meromorphic on
`U` with finite orders. -/
private theorem divisor_prod_of_forall {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → 𝕜}
    (h₁f : ∀ i, MeromorphicOn (f i) U)
    (h₂f : ∀ i z (hz : z ∈ U), meromorphicOrderAt (f i) z (h₁f i z hz) ≠ ⊤)
    {h : ∀ z (hz : z ∈ U), meromorphicOrderAt (∏ i ∈ s, f i) z
      (MeromorphicOn.prod (fun i _ ↦ h₁f i) z hz) ≠ ⊤} :
    divisor (∏ i ∈ s, f i) U h = ∑ i ∈ s, divisor (f i) U (h₂f i) := by
  classical
  induction s using Finset.induction with
  | empty =>
    rw [sum_empty]
    exact divisor_const (1 : 𝕜)
  | insert a s ha hs =>
    have h₁ (z) (hz : z ∈ U) : meromorphicOrderAt (∏ i ∈ s, f i) z
        (MeromorphicOn.prod (fun i _ ↦ h₁f i) z hz) ≠ ⊤ :=
      meromorphicOrderAt_prod_ne_top (fun i _ ↦ h₁f i z hz) fun i _ ↦ h₂f i z hz
    have h₂ (z) (hz : z ∈ U) : meromorphicOrderAt (f a * ∏ i ∈ s, f i) z
        (((h₁f a).mul (MeromorphicOn.prod fun i _ ↦ h₁f i)) z hz) ≠ ⊤ := by
      rw [meromorphicOrderAt_mul (h₁f a z hz) (MeromorphicOn.prod (fun i _ ↦ h₁f i) z hz)]
      exact WithTop.add_ne_top.2 ⟨h₂f a z hz, h₁ z hz⟩
    rw [sum_insert ha, ← hs (h := h₁), ← divisor_mul (h₁f a) (MeromorphicOn.prod fun i _ ↦ h₁f i)
      (h₂f a) h₁ (h := h₂)]
    exact divisor_congr fun z hz ↦ meromorphicOrderAt_congr _ (.of_eq (prod_insert ha))

open Finset in
/--
If orders are finite, the divisor of a product of meromorphic functions is the sum of the divisors.
-/
theorem divisor_prod {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → 𝕜}
    (h₁f : ∀ i ∈ s, MeromorphicOn (f i) U)
    (h₂f : ∀ i (hi : i ∈ s) z (hz : z ∈ U), meromorphicOrderAt (f i) z (h₁f i hi z hz) ≠ ⊤)
    {h : ∀ z (hz : z ∈ U), meromorphicOrderAt (∏ i ∈ s, f i) z (MeromorphicOn.prod h₁f z hz) ≠ ⊤} :
    divisor (∏ i ∈ s, f i) U h = ∑ i ∈ s.attach, divisor (f i) U (h₂f i i.2) := by
  have h' (z) (hz : z ∈ U) : meromorphicOrderAt (∏ i ∈ s.attach, f i) z
      (MeromorphicOn.prod (fun (i : s) _ ↦ h₁f i i.2) z hz) ≠ ⊤ :=
    meromorphicOrderAt_prod_ne_top (fun (i : s) _ ↦ h₁f i i.2 z hz) fun (i : s) _ ↦ h₂f i i.2 z hz
  rw [← divisor_prod_of_forall (fun i : s ↦ h₁f i i.2) (fun i : s ↦ h₂f i i.2) (h := h')]
  exact divisor_congr fun z hz ↦ meromorphicOrderAt_congr _ (.of_eq (prod_attach s f).symm)

/--
If orders are finite, the divisor of a product of meromorphic functions is the sum of the divisors.
-/
theorem divisor_fun_prod {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → 𝕜}
    (h₁f : ∀ i ∈ s, MeromorphicOn (f i) U)
    (h₂f : ∀ i (hi : i ∈ s) z (hz : z ∈ U), meromorphicOrderAt (f i) z (h₁f i hi z hz) ≠ ⊤)
    {h : ∀ z (hz : z ∈ U), meromorphicOrderAt (fun x ↦ ∏ i ∈ s, f i x) z
      (MeromorphicOn.fun_prod h₁f z hz) ≠ ⊤} :
    divisor (fun x ↦ ∏ i ∈ s, f i x) U h = ∑ i ∈ s.attach, divisor (f i) U (h₂f i i.2) := by
  rw [← divisor_prod h₁f h₂f (h := fun z hz ↦ meromorphicOrderAt_prod_ne_top
    (fun i hi ↦ h₁f i hi z hz) fun i hi ↦ h₂f i hi z hz)]
  exact divisor_congr fun z hz ↦ meromorphicOrderAt_congr _ (.of_eq (by ext; simp))

/-- The divisor of the inverse is the negative of the divisor. -/
theorem divisor_inv {f : 𝕜 → 𝕜} {hf : MeromorphicOn f U}
    (h : ∀ z (hz : z ∈ U), meromorphicOrderAt f z (hf z hz) ≠ ⊤) {hf' : MeromorphicOn f⁻¹ U}
    {h' : ∀ z (hz : z ∈ U), meromorphicOrderAt f⁻¹ z (hf' z hz) ≠ ⊤} :
    divisor f⁻¹ U h' = -divisor f U h := by
  ext z
  by_cases hz : z ∈ U
  · have := meromorphicOrderAt_inv (hf z hz)
    rw [← coe_divisor_apply hf hz (h := h), ← coe_divisor_apply hf' hz (h := h'),
      ← WithTop.LinearOrderedAddCommGroup.coe_neg] at this
    simp only [Function.locallyFinsuppWithin.coe_neg, Pi.neg_apply]
    exact_mod_cast this
  · simp [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hz]

/-- The divisor of the inverse is the negative of the divisor. -/
theorem divisor_fun_inv {f : 𝕜 → 𝕜} {hf : MeromorphicOn f U}
    (h : ∀ z (hz : z ∈ U), meromorphicOrderAt f z (hf z hz) ≠ ⊤)
    {hf' : MeromorphicOn (fun z ↦ (f z)⁻¹) U}
    {h' : ∀ z (hz : z ∈ U), meromorphicOrderAt (fun z ↦ (f z)⁻¹) z (hf' z hz) ≠ ⊤} :
    divisor (fun z ↦ (f z)⁻¹) U h' = -divisor f U h :=
  divisor_inv h

/--
If orders are finite, then the divisor of `f ^ n` is `n` times the divisor of `f`.
-/
theorem divisor_pow {f : 𝕜 → 𝕜} {hf : MeromorphicOn f U}
    (h : ∀ z (hz : z ∈ U), meromorphicOrderAt f z (hf z hz) ≠ ⊤) (n : ℕ)
    {hf' : MeromorphicOn (f ^ n) U}
    {h' : ∀ z (hz : z ∈ U), meromorphicOrderAt (f ^ n) z (hf' z hz) ≠ ⊤} :
    divisor (f ^ n) U h' = n • divisor f U h := by
  ext z
  by_cases hz : z ∈ U
  · have := meromorphicOrderAt_pow (hf z hz) (n := n)
    rw [← coe_divisor_apply hf hz (h := h), ← coe_divisor_apply hf' hz (h := h')] at this
    simp only [Function.locallyFinsuppWithin.coe_nsmul, Pi.smul_apply, nsmul_eq_mul]
    exact_mod_cast this
  · simp [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hz]

/--
If orders are finite, then the divisor of `f ^ n` is `n` times the divisor of `f`.
-/
theorem divisor_fun_pow {f : 𝕜 → 𝕜} {hf : MeromorphicOn f U}
    (h : ∀ z (hz : z ∈ U), meromorphicOrderAt f z (hf z hz) ≠ ⊤) (n : ℕ)
    {hf' : MeromorphicOn (fun z ↦ f z ^ n) U}
    {h' : ∀ z (hz : z ∈ U), meromorphicOrderAt (fun z ↦ f z ^ n) z (hf' z hz) ≠ ⊤} :
    divisor (fun z ↦ f z ^ n) U h' = n • divisor f U h :=
  divisor_pow h n

/-- The pole divisor of `f ^ n` is `n` times the pole divisor of `f`. -/
theorem poleDivisor_pow {f : 𝕜 → 𝕜} (hf : MeromorphicOn f U) (n : ℕ) :
    poleDivisor (f ^ n) U (hf.pow n) = n • poleDivisor f U hf := by
  ext z
  by_cases hz : z ∈ U
  · have e₁ := coe_poleDivisor_apply hf hz
    have e₂ := coe_poleDivisor_apply (hf.pow n) hz
    have h : meromorphicOrderAt (f ^ n) z ((hf.pow n) z hz) =
        n * meromorphicOrderAt f z (hf z hz) :=
      meromorphicOrderAt_pow (hf z hz)
    rw [h] at e₂
    simp only [Function.locallyFinsuppWithin.coe_nsmul, Pi.smul_apply, nsmul_eq_mul]
    generalize meromorphicOrderAt f z (hf z hz) = a at e₁ e₂
    cases a with
    | top =>
      have h₁ : poleDivisor f U hf z = 0 := by simpa using e₁
      rcases eq_or_ne n 0 with rfl | hn
      · simpa using e₂
      · rw [WithTop.mul_top (by exact_mod_cast hn)] at e₂
        simpa [h₁] using e₂
    | coe m =>
      have e₁' : poleDivisor f U hf z = -min m 0 := by exact_mod_cast e₁
      have e₂' : poleDivisor (f ^ n) U (hf.pow n) z = -min (n * m) 0 := by exact_mod_cast e₂
      rw [e₁', e₂', mul_neg, mul_min_of_nonneg _ _ (Int.natCast_nonneg n), mul_zero]
  · simp [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hz]

/--
If orders are finite, then the divisor of `f ^ n` is `n` times the divisor of `f`.
-/
theorem divisor_zpow {f : 𝕜 → 𝕜} {hf : MeromorphicOn f U}
    (h : ∀ z (hz : z ∈ U), meromorphicOrderAt f z (hf z hz) ≠ ⊤) (n : ℤ)
    {hf' : MeromorphicOn (f ^ n) U}
    {h' : ∀ z (hz : z ∈ U), meromorphicOrderAt (f ^ n) z (hf' z hz) ≠ ⊤} :
    divisor (f ^ n) U h' = n • divisor f U h := by
  ext z
  by_cases hz : z ∈ U
  · have := meromorphicOrderAt_zpow (hf z hz) (n := n)
    rw [← coe_divisor_apply hf hz (h := h), ← coe_divisor_apply hf' hz (h := h')] at this
    simp only [Function.locallyFinsuppWithin.coe_zsmul, Pi.smul_apply, zsmul_eq_mul]
    exact_mod_cast this
  · simp [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hz]

/--
If orders are finite, then the divisor of `f ^ n` is `n` times the divisor of `f`.
-/
theorem divisor_fun_zpow {f : 𝕜 → 𝕜} {hf : MeromorphicOn f U}
    (h : ∀ z (hz : z ∈ U), meromorphicOrderAt f z (hf z hz) ≠ ⊤) (n : ℤ)
    {hf' : MeromorphicOn (fun z ↦ f z ^ n) U}
    {h' : ∀ z (hz : z ∈ U), meromorphicOrderAt (fun z ↦ f z ^ n) z (hf' z hz) ≠ ⊤} :
    divisor (fun z ↦ f z ^ n) U h' = n • divisor f U h :=
  divisor_zpow h n

/--
Taking the divisor of a meromorphic function commutes with restriction.
-/
@[simp]
theorem divisor_restrict {f : 𝕜 → E} {V : Set 𝕜} {hf : MeromorphicOn f U}
    {h : ∀ z (hz : z ∈ U), meromorphicOrderAt f z (hf z hz) ≠ ⊤} (hV : V ⊆ U) :
    (divisor f U h).restrict hV = divisor f V (hf := hf.mono_set hV) fun z hz ↦ h z (hV hz) := by
  ext x
  by_cases hx : x ∈ V
  · rw [Function.locallyFinsuppWithin.restrict_apply]
    simp [hx, hV hx]
  · simp [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hx]

/-- Taking the pole divisor of a meromorphic function commutes with restriction. -/
@[simp]
theorem poleDivisor_restrict {f : 𝕜 → E} {V : Set 𝕜} (hf : MeromorphicOn f U) (hV : V ⊆ U) :
    (poleDivisor f U hf).restrict hV = poleDivisor f V (hf.mono_set hV) := by
  ext x
  by_cases hx : x ∈ V
  · simp only [Function.locallyFinsuppWithin.restrict_apply, hx, ↓reduceIte]
    exact_mod_cast (coe_poleDivisor_apply hf (hV hx)).trans
      (coe_poleDivisor_apply (hf.mono_set hV) hx).symm
  · simp [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hx]

/-- Adding an analytic function to a meromorphic one does not change the pole divisor. -/
theorem poleDivisor_add_of_analyticOnNhd_right {f₁ f₂ : 𝕜 → E} (hf₁ : MeromorphicOn f₁ U)
    (hf₂ : AnalyticOnNhd 𝕜 f₂ U) :
    poleDivisor (f₁ + f₂) U (hf₁.add hf₂.meromorphicOn) = poleDivisor f₁ U hf₁ := by
  refine poleDivisor_congr' fun x hx ↦ ?_
  have h₁ := hf₁ x hx
  have h₂ := (hf₂ x hx).meromorphicAt
  by_cases h : 0 ≤ meromorphicOrderAt f₁ x h₁
  · have : 0 ≤ meromorphicOrderAt (f₁ + f₂) x (h₁.add h₂) :=
      (le_inf h (hf₂ x hx).meromorphicOrderAt_nonneg).trans (meromorphicOrderAt_add h₁ h₂)
    rw [min_eq_right this, min_eq_right h]
  · rw [meromorphicOrderAt_add_eq_left_of_lt h₁ h₂
      ((not_le.1 h).trans_le (hf₂ x hx).meromorphicOrderAt_nonneg)]

/-- Adding an analytic function to a meromorphic one does not change the pole divisor. -/
theorem poleDivisor_add_of_analyticOnNhd_left {f₁ f₂ : 𝕜 → E} (hf₁ : AnalyticOnNhd 𝕜 f₁ U)
    (hf₂ : MeromorphicOn f₂ U) :
    poleDivisor (f₁ + f₂) U (hf₁.meromorphicOn.add hf₂) = poleDivisor f₂ U hf₂ := by
  rw [← poleDivisor_add_of_analyticOnNhd_right hf₂ hf₁]
  exact poleDivisor_congr fun z hz ↦ meromorphicOrderAt_congr _ (.of_eq (add_comm f₁ f₂))

open WithTop in
/-- The divisor of the function `z ↦ z - z₀` at `x` is `0` if `x ≠ z₀`. -/
lemma divisor_sub_const_of_ne {U : Set 𝕜} {z₀ x : 𝕜} (hx : x ≠ z₀)
    {hf : MeromorphicOn (· - z₀) U}
    {h : ∀ z (hz : z ∈ U), meromorphicOrderAt (· - z₀) z (hf z hz) ≠ ⊤} :
    divisor (· - z₀) U h x = 0 := by
  by_cases hu : x ∈ U
  · rw [divisor_apply hf hu, untop_eq_iff]
    exact (meromorphicOrderAt_eq_int_iff (hf x hu)).mpr
      ⟨(· - z₀), analyticAt_id.fun_sub analyticAt_const, by simp [sub_ne_zero_of_ne hx]⟩
  · exact Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu

open WithTop in
/-- The divisor of the function `z ↦ z - z₀` at `z₀` is `1`. -/
lemma divisor_sub_const_self {z₀ : 𝕜} {U : Set 𝕜} (h₀ : z₀ ∈ U) {hf : MeromorphicOn (· - z₀) U}
    {h : ∀ z (hz : z ∈ U), meromorphicOrderAt (· - z₀) z (hf z hz) ≠ ⊤} :
    divisor (· - z₀) U h z₀ = 1 := by
  rw [divisor_apply hf h₀, untop_eq_iff]
  exact (meromorphicOrderAt_eq_int_iff (hf z₀ h₀)).mpr ⟨fun _ ↦ 1, analyticAt_const, by simp⟩

open scoped Pointwise

/-- Divisors are invariant under translation. -/
private theorem divisor_comp_add_const_of_mem_iff {c x : 𝕜} {f : 𝕜 → E} {V : Set 𝕜}
    (hV : ∀ x, x ∈ V ↔ x - c ∈ U) {hf : MeromorphicOn f V}
    (h : ∀ z (hz : z ∈ V), meromorphicOrderAt f z (hf z hz) ≠ ⊤)
    {hf' : MeromorphicOn (f ∘ (· + c)) U}
    {h' : ∀ z (hz : z ∈ U), meromorphicOrderAt (f ∘ (· + c)) z (hf' z hz) ≠ ⊤} :
    divisor (f ∘ (· + c)) U h' (x - c) = divisor f V h x := by
  by_cases h₁ : x ∈ V
  · have hU : x - c ∈ U := (hV x).1 h₁
    have hfx : MeromorphicAt f (x - c + c) := by simpa using hf x h₁
    have e : meromorphicOrderAt f (x - c + c) hfx = meromorphicOrderAt f x (hf x h₁) := by
      congr 1
      exact sub_add_cancel x c
    exact_mod_cast (coe_divisor_apply hf' hU (h := h')).trans
      ((meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt hfx).trans
        (e.trans (coe_divisor_apply hf h₁ (h := h)).symm))
  · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ h₁,
      Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ (mt (hV x).2 h₁)]

/-- Divisors are invariant under translation. -/
private theorem divisor_comp_sub_const_of_mem_iff {c : 𝕜} {f : 𝕜 → E} {V : Set 𝕜}
    (hV : ∀ z, z ∈ V ↔ z + c ∈ U) {hf : MeromorphicOn f V}
    (h : ∀ z (hz : z ∈ V), meromorphicOrderAt f z (hf z hz) ≠ ⊤)
    {hf' : MeromorphicOn (f ∘ (· - c)) U}
    {h' : ∀ z (hz : z ∈ U), meromorphicOrderAt (f ∘ (· - c)) z (hf' z hz) ≠ ⊤} :
    divisor (f ∘ (· - c)) U h' (z + c) = divisor f V h z := by
  by_cases h₁ : z ∈ V
  · have hU : z + c ∈ U := (hV z).1 h₁
    have hfx : MeromorphicAt f (z + c - c) := by simpa using hf z h₁
    have e : meromorphicOrderAt f (z + c - c) hfx = meromorphicOrderAt f z (hf z h₁) := by
      congr 1
      exact add_sub_cancel_right z c
    exact_mod_cast (coe_divisor_apply hf' hU (h := h')).trans
      ((meromorphicOrderAt_comp_sub_const_eq_meromorphicOrderAt hfx).trans
        (e.trans (coe_divisor_apply hf h₁ (h := h)).symm))
  · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ h₁,
      Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ (mt (hV z).2 h₁)]

/-- Divisors are invariant under translation. -/
@[to_fun divisor_fun_comp_add_const_eq_divisor]
theorem divisor_comp_add_const_eq_divisor {c x : 𝕜} {f : 𝕜 → E} {hf : MeromorphicOn f (U + {c})}
    (h : ∀ z (hz : z ∈ U + {c}), meromorphicOrderAt f z (hf z hz) ≠ ⊤)
    {hf' : MeromorphicOn (f ∘ (· + c)) U}
    {h' : ∀ z (hz : z ∈ U), meromorphicOrderAt (f ∘ (· + c)) z (hf' z hz) ≠ ⊤} :
    divisor (f ∘ (· + c)) U h' (x - c) = divisor f (U + {c}) h x :=
  divisor_comp_add_const_of_mem_iff (fun x ↦ by simp [← sub_eq_add_neg]) h

/-- Divisors are invariant under translation. -/
@[to_fun divisor_fun_comp_sub_const_eq_divisor]
theorem divisor_comp_sub_const_eq_divisor {c : 𝕜} {f : 𝕜 → E} {hf : MeromorphicOn f (U - {c})}
    (h : ∀ z (hz : z ∈ U - {c}), meromorphicOrderAt f z (hf z hz) ≠ ⊤)
    {hf' : MeromorphicOn (f ∘ (· - c)) U}
    {h' : ∀ z (hz : z ∈ U), meromorphicOrderAt (f ∘ (· - c)) z (hf' z hz) ≠ ⊤} :
    divisor (f ∘ (· - c)) U h' (z + c) = divisor f (U - {c}) h z :=
  divisor_comp_sub_const_of_mem_iff (fun z ↦ by simp [sub_eq_iff_eq_add]) h

/-- Divisors are invariant under translation, special case where the set is a ball.. -/
@[to_fun divisor_ball_fun_comp_sub_const_eq_divisor_ball]
theorem divisor_ball_comp_sub_const_eq_divisor_ball {c : 𝕜} {R : ℝ} {f : 𝕜 → E}
    {hf : MeromorphicOn f (ball 0 R)}
    (h : ∀ z (hz : z ∈ ball 0 R), meromorphicOrderAt f z (hf z hz) ≠ ⊤)
    {hf' : MeromorphicOn (f ∘ (· - c)) (ball c R)}
    {h' : ∀ z (hz : z ∈ ball c R), meromorphicOrderAt (f ∘ (· - c)) z (hf' z hz) ≠ ⊤} :
    divisor (f ∘ (· - c)) (ball c R) h' (z + c) = divisor f (ball 0 R) h z :=
  divisor_comp_sub_const_of_mem_iff (fun z ↦ by simp) h

/-- Divisors are invariant under translation, special case where the set is a closed ball. -/
@[to_fun divisor_closedBall_fun_comp_sub_const_eq_divisor_closedBall]
theorem divisor_closedBall_comp_sub_const_eq_divisor_closedBall {c : 𝕜} {R : ℝ} {f : 𝕜 → E}
    {hf : MeromorphicOn f (closedBall 0 R)}
    (h : ∀ z (hz : z ∈ closedBall 0 R), meromorphicOrderAt f z (hf z hz) ≠ ⊤)
    {hf' : MeromorphicOn (f ∘ (· - c)) (closedBall c R)}
    {h' : ∀ z (hz : z ∈ closedBall c R), meromorphicOrderAt (f ∘ (· - c)) z (hf' z hz) ≠ ⊤} :
    divisor (f ∘ (· - c)) (closedBall c R) h' (z + c) = divisor f (closedBall 0 R) h z :=
  divisor_comp_sub_const_of_mem_iff (fun z ↦ by simp) h

/-- Divisors are invariant under translation, special case where the set is a sphere. -/
@[to_fun divisor_sphere_fun_comp_sub_const_eq_divisor_sphere]
theorem divisor_sphere_comp_sub_const_eq_divisor_sphere {c : 𝕜} {R : ℝ} {f : 𝕜 → E}
    {hf : MeromorphicOn f (sphere 0 R)}
    (h : ∀ z (hz : z ∈ sphere 0 R), meromorphicOrderAt f z (hf z hz) ≠ ⊤)
    {hf' : MeromorphicOn (f ∘ (· - c)) (sphere c R)}
    {h' : ∀ z (hz : z ∈ sphere c R), meromorphicOrderAt (f ∘ (· - c)) z (hf' z hz) ≠ ⊤} :
    divisor (f ∘ (· - c)) (sphere c R) h' (z + c) = divisor f (sphere 0 R) h z :=
  divisor_comp_sub_const_of_mem_iff (fun z ↦ by simp) h

end MeromorphicOn
