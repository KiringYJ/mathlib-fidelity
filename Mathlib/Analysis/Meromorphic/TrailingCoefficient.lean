/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Meromorphic.Order

/-!
# The Trailing Coefficient of a Meromorphic Function

This file defines the trailing coefficient of a meromorphic function of finite order. If `f` is
meromorphic at a point `x` and its order at `x` is finite, the trailing coefficient is the (unique!)
value `g x` for a presentation of `f` in the form `(z - x) ^ order • g z` with `g` analytic at `x`.
It is nonzero. A function that vanishes on a punctured neighborhood of `x` has order `⊤` there and
no nonzero coefficient, so the trailing coefficient takes the finiteness of the order as an
argument.

The lemma `MeromorphicAt.tendsto_nhds_meromorphicTrailingCoeffAt` expresses the trailing coefficient
as a limit.
-/

@[expose] public section

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f g : 𝕜 → E} {x : 𝕜}

open Filter

open scoped Topology

variable (f x) in
/--
If `f` is meromorphic of finite order at a point `x`, the trailing coefficient is the (unique!)
value `g x` for a presentation of `f` in the form `(z - x) ^ order • g z` with `g` analytic at `x`.
The meromorphy proof is determined by the finiteness proof `h`.
-/
noncomputable def meromorphicTrailingCoeffAt {hf : MeromorphicAt f x}
    (h : meromorphicOrderAt f x hf ≠ ⊤) : E :=
  ((meromorphicOrderAt_ne_top_iff hf).1 h).choose x

/-!
## Finiteness of the Order
-/

/-- An analytic function that does not vanish at `x` has finite order at `x`. -/
lemma AnalyticAt.meromorphicOrderAt_ne_top_of_ne_zero (h₁ : AnalyticAt 𝕜 f x) (h₂ : f x ≠ 0) :
    meromorphicOrderAt f x h₁.meromorphicAt ≠ ⊤ := by
  rw [h₁.meromorphicOrderAt_eq, h₁.analyticOrderAt_eq_zero.2 h₂]
  simp

/-- The function `z ↦ z - y` has finite order at every point. -/
lemma meromorphicOrderAt_id_sub_const_ne_top {x y : 𝕜} :
    meromorphicOrderAt (· - y) x ≠ ⊤ := by
  rw [meromorphicOrderAt_ne_top_iff_eventually_ne_zero]
  by_cases h : x = y
  · subst h
    filter_upwards [self_mem_nhdsWithin] with z hz using sub_ne_zero.2 hz
  · filter_upwards [nhdsWithin_le_nhds (isOpen_ne.mem_nhds h)] with z hz using sub_ne_zero.2 hz

/-- If `g` is analytic at `x` and not locally constant, then `z ↦ g z - g x` has finite order at
`x`. -/
lemma AnalyticAt.meromorphicOrderAt_sub_ne_top {g : 𝕜 → 𝕜} (hg : AnalyticAt 𝕜 g x)
    (hg_nc : ¬EventuallyConst g (𝓝 x)) :
    meromorphicOrderAt (g · - g x) x ≠ ⊤ := by
  rw [(hg.fun_sub analyticAt_const).meromorphicOrderAt_eq, Ne, ENat.map_eq_top_iff]
  exact (eventuallyConst_iff_analyticOrderAt_sub_eq_top hg).not.1 hg_nc

/-!
## Characterization of the Trailing Coefficient
-/

/--
Definition of the trailing coefficient in case where `f` is meromorphic of finite order and a
presentation of the form `f = (z - x) ^ order • g z` is given, with `g` analytic at `x`.
-/
lemma AnalyticAt.meromorphicTrailingCoeffAt_of_eq_nhdsNE (h₁g : AnalyticAt 𝕜 g x)
    (h₁f : MeromorphicAt f x) (h₂f : meromorphicOrderAt f x h₁f ≠ ⊤)
    (h : f =ᶠ[𝓝[≠] x] fun z ↦ (z - x) ^ (meromorphicOrderAt f x h₁f).untop₀ • g z) :
    meromorphicTrailingCoeffAt f x h₂f = g x := by
  unfold meromorphicTrailingCoeffAt
  obtain ⟨h'₁, h'₂, h'₃⟩ := ((meromorphicOrderAt_ne_top_iff h₁f).1 h₂f).choose_spec
  apply Filter.EventuallyEq.eq_of_nhds
  rw [← h'₁.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE h₁g.continuousAt]
  filter_upwards [h, h'₃, self_mem_nhdsWithin] with y h₁y h₂y h₃y
  rw [← sub_eq_zero]
  rwa [h₂y, ← sub_eq_zero, ← smul_sub, smul_eq_zero_iff_right] at h₁y
  simp_all [zpow_ne_zero, sub_ne_zero]

/--
Variant of `AnalyticAt.meromorphicTrailingCoeffAt_of_eq_nhdsNE`: the trailing coefficient of a
function presented as `(z - x) ^ n • g z` near `x`, with `g` analytic at `x` and `g x ≠ 0`.
-/
lemma AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE {n : ℤ} (h₁g : AnalyticAt 𝕜 g x)
    (h₂g : g x ≠ 0) (h : f =ᶠ[𝓝[≠] x] fun z ↦ (z - x) ^ n • g z) {hf : MeromorphicAt f x}
    {h₂f : meromorphicOrderAt f x hf ≠ ⊤} :
    meromorphicTrailingCoeffAt f x h₂f = g x := by
  have : meromorphicOrderAt f x hf = n := (meromorphicOrderAt_eq_int_iff hf).2 ⟨g, h₁g, h₂g, h⟩
  exact h₁g.meromorphicTrailingCoeffAt_of_eq_nhdsNE hf h₂f (by simpa [this] using h)

/--
If `f` is analytic and does not vanish at `x`, then the trailing coefficient of `f` at `x` is `f x`.
-/
@[simp]
lemma AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero (h₁ : AnalyticAt 𝕜 f x) (h₂ : f x ≠ 0)
    {hf : MeromorphicAt f x} {h₃ : meromorphicOrderAt f x hf ≠ ⊤} :
    meromorphicTrailingCoeffAt f x h₃ = f x := by
  rw [h₁.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE (n := 0) h₂]
  filter_upwards
  simp

/--
If `f` is meromorphic of finite order at `x`, then the trailing coefficient of `f` at `x` is the
limit of the function `(· - x) ^ (-order) • f`.
-/
lemma MeromorphicAt.tendsto_nhds_meromorphicTrailingCoeffAt (h : MeromorphicAt f x)
    (h₂ : meromorphicOrderAt f x h ≠ ⊤) :
    Tendsto ((· - x) ^ (-(meromorphicOrderAt f x h).untop₀) • f) (𝓝[≠] x)
      (𝓝 (meromorphicTrailingCoeffAt f x h₂)) := by
  obtain ⟨g, h₁g, h₂g, h₃g⟩ := (meromorphicOrderAt_ne_top_iff h).1 h₂
  apply Tendsto.congr' (f₁ := g)
  · filter_upwards [h₃g, self_mem_nhdsWithin] with y h₁y h₂y
    rw [zpow_neg, Pi.smul_apply', Pi.inv_apply, Pi.pow_apply, h₁y, ← smul_assoc, smul_eq_mul,
      ← zpow_neg, ← zpow_add', neg_add_cancel, zpow_zero, one_smul]
    left
    simp_all [sub_ne_zero]
  · rw [h₁g.meromorphicTrailingCoeffAt_of_eq_nhdsNE h h₂ h₃g]
    apply h₁g.continuousAt.continuousWithinAt

/-!
## Elementary Properties
-/

/--
The trailing coefficient of a function that is meromorphic of finite order is not zero.
-/
lemma MeromorphicAt.meromorphicTrailingCoeffAt_ne_zero (h₁ : MeromorphicAt f x)
    (h₂ : meromorphicOrderAt f x h₁ ≠ ⊤) :
    meromorphicTrailingCoeffAt f x h₂ ≠ 0 := by
  obtain ⟨g, h₁g, h₂g, h₃g⟩ := (meromorphicOrderAt_ne_top_iff h₁).1 h₂
  simpa [h₁g.meromorphicTrailingCoeffAt_of_eq_nhdsNE h₁ h₂ h₃g] using h₂g

/--
The trailing coefficient of a constant function is the constant, which is nonzero since the order
is finite.
-/
@[simp]
theorem meromorphicTrailingCoeffAt_const {x : 𝕜} {e : E} {hf : MeromorphicAt (fun _ ↦ e) x}
    {h : meromorphicOrderAt (fun _ ↦ e) x hf ≠ ⊤} :
    meromorphicTrailingCoeffAt (fun _ ↦ e) x h = e := by
  have he : e ≠ 0 := by
    rintro rfl
    exact h ((meromorphicOrderAt_eq_top_iff hf).2 (by simp))
  exact analyticAt_const.meromorphicTrailingCoeffAt_of_ne_zero he

/--
The trailing coefficient of `fun z ↦ z - constant` at `z₀` equals one if `z₀ = constant`, or else
`z₀ - constant`.
-/
theorem meromorphicTrailingCoeffAt_id_sub_const [DecidableEq 𝕜] {x y : 𝕜}
    {hf : MeromorphicAt (· - y) x} {h : meromorphicOrderAt (· - y) x hf ≠ ⊤} :
    meromorphicTrailingCoeffAt (· - y) x h = if x = y then 1 else x - y := by
  split_ifs with hxy
  · subst hxy
    apply AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE (n := 1) (by fun_prop)
      (by apply one_ne_zero)
    simp
  · exact AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero (f := (· - y)) (by fun_prop)
      (sub_ne_zero.2 hxy)

/-!
## Congruence Lemma
-/

/--
If two functions agree in a punctured neighborhood, then their trailing coefficients agree.
-/
lemma meromorphicTrailingCoeffAt_congr_nhdsNE {f₁ f₂ : 𝕜 → E} (h : f₁ =ᶠ[𝓝[≠] x] f₂)
    {hf₁ : MeromorphicAt f₁ x} {h₁ : meromorphicOrderAt f₁ x hf₁ ≠ ⊤}
    {hf₂ : MeromorphicAt f₂ x} {h₂ : meromorphicOrderAt f₂ x hf₂ ≠ ⊤} :
    meromorphicTrailingCoeffAt f₁ x h₁ = meromorphicTrailingCoeffAt f₂ x h₂ := by
  obtain ⟨g, h₁g, h₂g, h₃g⟩ := (meromorphicOrderAt_ne_top_iff hf₁).1 h₁
  rw [h₁g.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE h₂g h₃g,
    h₁g.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE h₂g (h.symm.trans h₃g)]

/-!
## Behavior under Arithmetic Operations
-/

/--
Taking the negative commutes with taking `meromorphicTrailingCoeffAt`.
-/
theorem meromorphicTrailingCoeffAt_neg {f : 𝕜 → E} {hf : MeromorphicAt f x}
    (h : meromorphicOrderAt f x hf ≠ ⊤) {hf' : MeromorphicAt (-f) x}
    {h' : meromorphicOrderAt (-f) x hf' ≠ ⊤} :
    meromorphicTrailingCoeffAt (-f) x h' = -meromorphicTrailingCoeffAt f x h := by
  obtain ⟨g, h₁g, h₂g, h₃g⟩ := (meromorphicOrderAt_ne_top_iff hf).1 h
  rw [h₁g.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE h₂g h₃g,
    h₁g.neg.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE
      (n := (meromorphicOrderAt f x hf).untop₀) (neg_ne_zero.2 h₂g)]
  · rfl
  · filter_upwards [h₃g] with z hz
    simp [hz]

/--
Taking the negative commutes with taking `meromorphicTrailingCoeffAt`.
-/
theorem meromorphicTrailingCoeffAt_fun_neg {f : 𝕜 → E} {hf : MeromorphicAt f x}
    (h : meromorphicOrderAt f x hf ≠ ⊤) {hf' : MeromorphicAt (fun z ↦ -f z) x}
    {h' : meromorphicOrderAt (fun z ↦ -f z) x hf' ≠ ⊤} :
    meromorphicTrailingCoeffAt (fun z ↦ -f z) x h' = -meromorphicTrailingCoeffAt f x h :=
  meromorphicTrailingCoeffAt_neg h

/--
If `f₁` and `f₂` have unequal order at `x`, then the trailing coefficient of `f₁ + f₂` at `x` is the
trailing coefficient of the function with the lowest order.
-/
theorem MeromorphicAt.meromorphicTrailingCoeffAt_add_eq_left_of_lt {f₁ f₂ : 𝕜 → E}
    (hf₁ : MeromorphicAt f₁ x) (hf₂ : MeromorphicAt f₂ x)
    (h : meromorphicOrderAt f₁ x hf₁ < meromorphicOrderAt f₂ x hf₂)
    {hf : MeromorphicAt (f₁ + f₂) x} {h' : meromorphicOrderAt (f₁ + f₂) x hf ≠ ⊤} :
    meromorphicTrailingCoeffAt (f₁ + f₂) x h' = meromorphicTrailingCoeffAt f₁ x h.ne_top := by
  obtain ⟨n₁, hn₁⟩ := WithTop.ne_top_iff_exists.1 h.ne_top
  obtain ⟨g₁, h₁g₁, h₂g₁, h₃g₁⟩ := (meromorphicOrderAt_eq_int_iff hf₁).1 hn₁.symm
  rw [h₁g₁.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE h₂g₁ h₃g₁]
  -- Trivial case: f₂ vanishes locally around x
  by_cases h₁f₂ : meromorphicOrderAt f₂ x hf₂ = ⊤
  · apply h₁g₁.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE (n := n₁) h₂g₁
    filter_upwards [(meromorphicOrderAt_eq_top_iff hf₂).1 h₁f₂, h₃g₁] with z h₁z h₂z
    simp [h₁z, h₂z]
  -- General case
  obtain ⟨n₂, hn₂⟩ := WithTop.ne_top_iff_exists.1 h₁f₂
  obtain ⟨g₂, h₁g₂, h₂g₂, h₃g₂⟩ := (meromorphicOrderAt_eq_int_iff hf₂).1 hn₂.symm
  have hn : n₁ < n₂ := by
    rw [← WithTop.coe_lt_coe, hn₁, hn₂]
    exact h
  have τ₀ : ∀ᶠ z in 𝓝[≠] x, (f₁ + f₂) z = (z - x) ^ n₁ • (g₁ + (z - x) ^ (n₂ - n₁) • g₂) z := by
    filter_upwards [h₃g₁, h₃g₂, self_mem_nhdsWithin] with z h₁z h₂z h₃z
    simp only [Pi.add_apply, h₁z, h₂z, Pi.smul_apply, smul_add, ← smul_assoc, smul_eq_mul,
      add_right_inj]
    rw [← zpow_add₀, add_sub_cancel]
    simp_all [sub_ne_zero]
  have τ₁ : AnalyticAt 𝕜 (fun z ↦ g₁ z + (z - x) ^ (n₂ - n₁) • g₂ z) x :=
    h₁g₁.fun_add (AnalyticAt.fun_smul (AnalyticAt.fun_zpow_nonneg (by fun_prop)
      (sub_nonneg_of_le hn.le)) h₁g₂)
  have τ₂ : g₁ x + (x - x) ^ (n₂ - n₁) • g₂ x ≠ 0 := by
    simpa [zero_zpow _ (sub_ne_zero.2 hn.ne')] using h₂g₁
  rw [τ₁.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE τ₂ τ₀]
  simp [zero_zpow _ (sub_ne_zero.2 hn.ne')]

/--
If `f₁` and `f₂` have unequal order at `x`, then the trailing coefficient of `f₁ + f₂` at `x` is the
trailing coefficient of the function with the lowest order.
-/
theorem MeromorphicAt.meromorphicTrailingCoeffAt_fun_add_eq_left_of_lt {f₁ f₂ : 𝕜 → E}
    (hf₁ : MeromorphicAt f₁ x) (hf₂ : MeromorphicAt f₂ x)
    (h : meromorphicOrderAt f₁ x hf₁ < meromorphicOrderAt f₂ x hf₂)
    {hf : MeromorphicAt (fun z ↦ f₁ z + f₂ z) x}
    {h' : meromorphicOrderAt (fun z ↦ f₁ z + f₂ z) x hf ≠ ⊤} :
    meromorphicTrailingCoeffAt (fun z ↦ f₁ z + f₂ z) x h' =
      meromorphicTrailingCoeffAt f₁ x h.ne_top :=
  MeromorphicAt.meromorphicTrailingCoeffAt_add_eq_left_of_lt hf₁ hf₂ h

/--
If `f₁` and `f₂` have unequal order at `x`, then the trailing coefficient of `f₁ - f₂` at `x` is the
trailing coefficient of the function with the lowest order.
-/
theorem MeromorphicAt.meromorphicTrailingCoeffAt_sub_eq_left_of_lt {f₁ f₂ : 𝕜 → E}
    (hf₁ : MeromorphicAt f₁ x) (hf₂ : MeromorphicAt f₂ x)
    (h : meromorphicOrderAt f₁ x hf₁ < meromorphicOrderAt f₂ x hf₂)
    {hf : MeromorphicAt (f₁ - f₂) x} {h' : meromorphicOrderAt (f₁ - f₂) x hf ≠ ⊤} :
    meromorphicTrailingCoeffAt (f₁ - f₂) x h' = meromorphicTrailingCoeffAt f₁ x h.ne_top := by
  have h'' : meromorphicOrderAt f₁ x hf₁ < meromorphicOrderAt (-f₂) x hf₂.neg := by
    rwa [← meromorphicOrderAt_neg hf₂]
  have hfin : meromorphicOrderAt (f₁ + -f₂) x (hf₁.add hf₂.neg) ≠ ⊤ := by
    rwa [← meromorphicOrderAt_congr hf (.of_eq (sub_eq_add_neg f₁ f₂))]
  rw [meromorphicTrailingCoeffAt_congr_nhdsNE (.of_eq (sub_eq_add_neg f₁ f₂)) (h₂ := hfin),
    MeromorphicAt.meromorphicTrailingCoeffAt_add_eq_left_of_lt hf₁ hf₂.neg h'']

/--
If `f₁` and `f₂` have unequal order at `x`, then the trailing coefficient of `f₁ - f₂` at `x` is the
trailing coefficient of the function with the lowest order.
-/
theorem MeromorphicAt.meromorphicTrailingCoeffAt_fun_sub_eq_left_of_lt {f₁ f₂ : 𝕜 → E}
    (hf₁ : MeromorphicAt f₁ x) (hf₂ : MeromorphicAt f₂ x)
    (h : meromorphicOrderAt f₁ x hf₁ < meromorphicOrderAt f₂ x hf₂)
    {hf : MeromorphicAt (fun z ↦ f₁ z - f₂ z) x}
    {h' : meromorphicOrderAt (fun z ↦ f₁ z - f₂ z) x hf ≠ ⊤} :
    meromorphicTrailingCoeffAt (fun z ↦ f₁ z - f₂ z) x h' =
      meromorphicTrailingCoeffAt f₁ x h.ne_top :=
  MeromorphicAt.meromorphicTrailingCoeffAt_sub_eq_left_of_lt hf₁ hf₂ h

/--
If `f₁` and `f₂` have equal finite order at `x` and if their trailing coefficients do not cancel,
then the trailing coefficient of `f₁ + f₂` at `x` is the sum of the trailing coefficients.
-/
theorem MeromorphicAt.meromorphicTrailingCoeffAt_add_eq_add {f₁ f₂ : 𝕜 → E}
    (hf₁ : MeromorphicAt f₁ x) (hf₂ : MeromorphicAt f₂ x)
    (h₁f₁ : meromorphicOrderAt f₁ x hf₁ ≠ ⊤) (h₁f₂ : meromorphicOrderAt f₂ x hf₂ ≠ ⊤)
    (h₁ : meromorphicOrderAt f₁ x hf₁ = meromorphicOrderAt f₂ x hf₂)
    (h₂ : meromorphicTrailingCoeffAt f₁ x h₁f₁ + meromorphicTrailingCoeffAt f₂ x h₁f₂ ≠ 0)
    {hf : MeromorphicAt (f₁ + f₂) x} {h' : meromorphicOrderAt (f₁ + f₂) x hf ≠ ⊤} :
    meromorphicTrailingCoeffAt (f₁ + f₂) x h'
      = meromorphicTrailingCoeffAt f₁ x h₁f₁ + meromorphicTrailingCoeffAt f₂ x h₁f₂ := by
  obtain ⟨n₁, hn₁⟩ := WithTop.ne_top_iff_exists.1 h₁f₁
  obtain ⟨g₁, h₁g₁, h₂g₁, h₃g₁⟩ := (meromorphicOrderAt_eq_int_iff hf₁).1 hn₁.symm
  obtain ⟨g₂, h₁g₂, h₂g₂, h₃g₂⟩ := (meromorphicOrderAt_eq_int_iff hf₂).1 (h₁ ▸ hn₁.symm)
  rw [h₁g₁.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE h₂g₁ h₃g₁,
    h₁g₂.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE h₂g₂ h₃g₂] at h₂ ⊢
  have τ₀ : ∀ᶠ z in 𝓝[≠] x, (f₁ + f₂) z = (z - x) ^ n₁ • (g₁ + g₂) z := by
    filter_upwards [h₃g₁, h₃g₂] with z h₁z h₂z
    simp [h₁z, h₂z]
  exact (h₁g₁.add h₁g₂).meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE h₂ τ₀

/--
If `f₁` and `f₂` have equal finite order at `x` and if their trailing coefficients do not cancel,
then the trailing coefficient of `f₁ + f₂` at `x` is the sum of the trailing coefficients.
-/
theorem MeromorphicAt.meromorphicTrailingCoeffAt_fun_add_eq_add {f₁ f₂ : 𝕜 → E}
    (hf₁ : MeromorphicAt f₁ x) (hf₂ : MeromorphicAt f₂ x)
    (h₁f₁ : meromorphicOrderAt f₁ x hf₁ ≠ ⊤) (h₁f₂ : meromorphicOrderAt f₂ x hf₂ ≠ ⊤)
    (h₁ : meromorphicOrderAt f₁ x hf₁ = meromorphicOrderAt f₂ x hf₂)
    (h₂ : meromorphicTrailingCoeffAt f₁ x h₁f₁ + meromorphicTrailingCoeffAt f₂ x h₁f₂ ≠ 0)
    {hf : MeromorphicAt (fun z ↦ f₁ z + f₂ z) x}
    {h' : meromorphicOrderAt (fun z ↦ f₁ z + f₂ z) x hf ≠ ⊤} :
    meromorphicTrailingCoeffAt (fun z ↦ f₁ z + f₂ z) x h'
      = meromorphicTrailingCoeffAt f₁ x h₁f₁ + meromorphicTrailingCoeffAt f₂ x h₁f₂ :=
  MeromorphicAt.meromorphicTrailingCoeffAt_add_eq_add hf₁ hf₂ h₁f₁ h₁f₂ h₁ h₂

/--
If `f₁` and `f₂` have equal finite order at `x` and if their trailing coefficients do not cancel,
then the trailing coefficient of `f₁ - f₂` at `x` is the difference of the trailing coefficients.
-/
theorem MeromorphicAt.meromorphicTrailingCoeffAt_sub_eq_sub {f₁ f₂ : 𝕜 → E}
    (hf₁ : MeromorphicAt f₁ x) (hf₂ : MeromorphicAt f₂ x)
    (h₁f₁ : meromorphicOrderAt f₁ x hf₁ ≠ ⊤) (h₁f₂ : meromorphicOrderAt f₂ x hf₂ ≠ ⊤)
    (h₁ : meromorphicOrderAt f₁ x hf₁ = meromorphicOrderAt f₂ x hf₂)
    (h₂ : meromorphicTrailingCoeffAt f₁ x h₁f₁ - meromorphicTrailingCoeffAt f₂ x h₁f₂ ≠ 0)
    {hf : MeromorphicAt (f₁ - f₂) x} {h' : meromorphicOrderAt (f₁ - f₂) x hf ≠ ⊤} :
    meromorphicTrailingCoeffAt (f₁ - f₂) x h'
      = meromorphicTrailingCoeffAt f₁ x h₁f₁ - meromorphicTrailingCoeffAt f₂ x h₁f₂ := by
  have h₂f₂ : meromorphicOrderAt (-f₂) x hf₂.neg ≠ ⊤ := by
    rwa [← meromorphicOrderAt_neg hf₂]
  have hfin : meromorphicOrderAt (f₁ + -f₂) x (hf₁.add hf₂.neg) ≠ ⊤ := by
    rwa [← meromorphicOrderAt_congr hf (.of_eq (sub_eq_add_neg f₁ f₂))]
  rw [meromorphicTrailingCoeffAt_congr_nhdsNE (.of_eq (sub_eq_add_neg f₁ f₂)) (h₂ := hfin),
    MeromorphicAt.meromorphicTrailingCoeffAt_add_eq_add hf₁ hf₂.neg h₁f₁ h₂f₂,
    meromorphicTrailingCoeffAt_neg h₁f₂, sub_eq_add_neg]
  · rwa [← meromorphicOrderAt_neg hf₂]
  · rwa [meromorphicTrailingCoeffAt_neg h₁f₂, ← sub_eq_add_neg]

/--
If `f₁` and `f₂` have equal finite order at `x` and if their trailing coefficients do not cancel,
then the trailing coefficient of `f₁ - f₂` at `x` is the difference of the trailing coefficients.
-/
theorem MeromorphicAt.meromorphicTrailingCoeffAt_fun_sub_eq_sub {f₁ f₂ : 𝕜 → E}
    (hf₁ : MeromorphicAt f₁ x) (hf₂ : MeromorphicAt f₂ x)
    (h₁f₁ : meromorphicOrderAt f₁ x hf₁ ≠ ⊤) (h₁f₂ : meromorphicOrderAt f₂ x hf₂ ≠ ⊤)
    (h₁ : meromorphicOrderAt f₁ x hf₁ = meromorphicOrderAt f₂ x hf₂)
    (h₂ : meromorphicTrailingCoeffAt f₁ x h₁f₁ - meromorphicTrailingCoeffAt f₂ x h₁f₂ ≠ 0)
    {hf : MeromorphicAt (fun z ↦ f₁ z - f₂ z) x}
    {h' : meromorphicOrderAt (fun z ↦ f₁ z - f₂ z) x hf ≠ ⊤} :
    meromorphicTrailingCoeffAt (fun z ↦ f₁ z - f₂ z) x h'
      = meromorphicTrailingCoeffAt f₁ x h₁f₁ - meromorphicTrailingCoeffAt f₂ x h₁f₂ :=
  MeromorphicAt.meromorphicTrailingCoeffAt_sub_eq_sub hf₁ hf₂ h₁f₁ h₁f₂ h₁ h₂

/--
The trailing coefficient of a scalar product is the scalar product of the trailing coefficients.
-/
lemma MeromorphicAt.meromorphicTrailingCoeffAt_smul {f₁ : 𝕜 → 𝕜} {f₂ : 𝕜 → E}
    (hf₁ : MeromorphicAt f₁ x) (hf₂ : MeromorphicAt f₂ x)
    (h₁f₁ : meromorphicOrderAt f₁ x hf₁ ≠ ⊤) (h₁f₂ : meromorphicOrderAt f₂ x hf₂ ≠ ⊤)
    {hf : MeromorphicAt (f₁ • f₂) x} {h : meromorphicOrderAt (f₁ • f₂) x hf ≠ ⊤} :
    meromorphicTrailingCoeffAt (f₁ • f₂) x h =
      (meromorphicTrailingCoeffAt f₁ x h₁f₁) • (meromorphicTrailingCoeffAt f₂ x h₁f₂) := by
  obtain ⟨g₁, h₁g₁, h₂g₁, h₃g₁⟩ := (meromorphicOrderAt_ne_top_iff hf₁).1 h₁f₁
  obtain ⟨g₂, h₁g₂, h₂g₂, h₃g₂⟩ := (meromorphicOrderAt_ne_top_iff hf₂).1 h₁f₂
  have : f₁ • f₂ =ᶠ[𝓝[≠] x] fun z ↦ (z - x) ^ ((meromorphicOrderAt f₁ x hf₁).untop₀ +
      (meromorphicOrderAt f₂ x hf₂).untop₀) • (g₁ • g₂) z := by
    filter_upwards [h₃g₁, h₃g₂, self_mem_nhdsWithin] with y h₁y h₂y h₃y
    simp_all [zpow_add₀ (sub_ne_zero.2 h₃y)]
    module
  rw [h₁g₁.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE h₂g₁ h₃g₁,
    h₁g₂.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE h₂g₂ h₃g₂,
    (h₁g₁.smul h₁g₂).meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE (smul_ne_zero h₂g₁ h₂g₂)
      this]
  rfl

/--
The trailing coefficient of a scalar product is the scalar product of the trailing coefficients.
-/
lemma MeromorphicAt.meromorphicTrailingCoeffAt_fun_smul {f₁ : 𝕜 → 𝕜} {f₂ : 𝕜 → E}
    (hf₁ : MeromorphicAt f₁ x) (hf₂ : MeromorphicAt f₂ x)
    (h₁f₁ : meromorphicOrderAt f₁ x hf₁ ≠ ⊤) (h₁f₂ : meromorphicOrderAt f₂ x hf₂ ≠ ⊤)
    {hf : MeromorphicAt (fun z ↦ f₁ z • f₂ z) x}
    {h : meromorphicOrderAt (fun z ↦ f₁ z • f₂ z) x hf ≠ ⊤} :
    meromorphicTrailingCoeffAt (fun z ↦ f₁ z • f₂ z) x h =
      (meromorphicTrailingCoeffAt f₁ x h₁f₁) • (meromorphicTrailingCoeffAt f₂ x h₁f₂) :=
  MeromorphicAt.meromorphicTrailingCoeffAt_smul hf₁ hf₂ h₁f₁ h₁f₂

/--
The trailing coefficient of a product is the product of the trailing coefficients.
-/
lemma MeromorphicAt.meromorphicTrailingCoeffAt_mul {f₁ f₂ : 𝕜 → 𝕜} (hf₁ : MeromorphicAt f₁ x)
    (hf₂ : MeromorphicAt f₂ x)
    (h₁f₁ : meromorphicOrderAt f₁ x hf₁ ≠ ⊤) (h₁f₂ : meromorphicOrderAt f₂ x hf₂ ≠ ⊤)
    {hf : MeromorphicAt (f₁ * f₂) x} {h : meromorphicOrderAt (f₁ * f₂) x hf ≠ ⊤} :
    meromorphicTrailingCoeffAt (f₁ * f₂) x h =
      (meromorphicTrailingCoeffAt f₁ x h₁f₁) * (meromorphicTrailingCoeffAt f₂ x h₁f₂) :=
  meromorphicTrailingCoeffAt_smul hf₁ hf₂ h₁f₁ h₁f₂

/--
The trailing coefficient of a product is the product of the trailing coefficients.
-/
lemma MeromorphicAt.meromorphicTrailingCoeffAt_fun_mul {f₁ f₂ : 𝕜 → 𝕜}
    (hf₁ : MeromorphicAt f₁ x) (hf₂ : MeromorphicAt f₂ x)
    (h₁f₁ : meromorphicOrderAt f₁ x hf₁ ≠ ⊤) (h₁f₂ : meromorphicOrderAt f₂ x hf₂ ≠ ⊤)
    {hf : MeromorphicAt (fun z ↦ f₁ z * f₂ z) x}
    {h : meromorphicOrderAt (fun z ↦ f₁ z * f₂ z) x hf ≠ ⊤} :
    meromorphicTrailingCoeffAt (fun z ↦ f₁ z * f₂ z) x h =
      (meromorphicTrailingCoeffAt f₁ x h₁f₁) * (meromorphicTrailingCoeffAt f₂ x h₁f₂) :=
  meromorphicTrailingCoeffAt_smul hf₁ hf₂ h₁f₁ h₁f₂

/--
The trailing coefficient of a product is the product of the trailing coefficients.
-/
theorem meromorphicTrailingCoeffAt_prod {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → 𝕜}
    {x : 𝕜} (h : ∀ σ, MeromorphicAt (f σ) x) (h₂ : ∀ σ, meromorphicOrderAt (f σ) x (h σ) ≠ ⊤)
    {hf : MeromorphicAt (∏ n ∈ s, f n) x} {h' : meromorphicOrderAt (∏ n ∈ s, f n) x hf ≠ ⊤} :
    meromorphicTrailingCoeffAt (∏ n ∈ s, f n) x h' =
      ∏ n ∈ s, meromorphicTrailingCoeffAt (f n) x (h₂ n) := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.prod_empty]
    exact analyticAt_const.meromorphicTrailingCoeffAt_of_ne_zero one_ne_zero
  | insert σ s₁ hσ hind =>
    have hfs : MeromorphicAt (∏ n ∈ s₁, f n) x := MeromorphicAt.prod fun τ _ ↦ h τ
    have h₂s : meromorphicOrderAt (∏ n ∈ s₁, f n) x hfs ≠ ⊤ :=
      meromorphicOrderAt_prod_ne_top (fun τ _ ↦ h τ) fun τ _ ↦ h₂ τ
    have hfin : meromorphicOrderAt (f σ * ∏ n ∈ s₁, f n) x ((h σ).mul hfs) ≠ ⊤ := by
      rwa [← meromorphicOrderAt_congr hf (.of_eq (Finset.prod_insert hσ))]
    rw [meromorphicTrailingCoeffAt_congr_nhdsNE (.of_eq (Finset.prod_insert hσ)) (h₂ := hfin),
      MeromorphicAt.meromorphicTrailingCoeffAt_mul (h σ) hfs (h₂ σ) h₂s, hind,
      Finset.prod_insert hσ]

/--
The trailing coefficient of a product is the product of the trailing coefficients.
-/
theorem meromorphicTrailingCoeffAt_fun_prod {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → 𝕜}
    {x : 𝕜} (h : ∀ σ, MeromorphicAt (f σ) x) (h₂ : ∀ σ, meromorphicOrderAt (f σ) x (h σ) ≠ ⊤)
    {hf : MeromorphicAt (fun z ↦ ∏ n ∈ s, f n z) x}
    {h' : meromorphicOrderAt (fun z ↦ ∏ n ∈ s, f n z) x hf ≠ ⊤} :
    meromorphicTrailingCoeffAt (fun z ↦ ∏ n ∈ s, f n z) x h'
      = ∏ n ∈ s, meromorphicTrailingCoeffAt (f n) x (h₂ n) := by
  have hfin : meromorphicOrderAt (∏ n ∈ s, f n) x (MeromorphicAt.prod fun τ _ ↦ h τ) ≠ ⊤ :=
    meromorphicOrderAt_prod_ne_top (fun τ _ ↦ h τ) fun τ _ ↦ h₂ τ
  rw [← meromorphicTrailingCoeffAt_prod h h₂ (h' := hfin)]
  exact meromorphicTrailingCoeffAt_congr_nhdsNE (.of_eq (by ext; simp))

/--
The trailing coefficient of the inverse function is the inverse of the trailing coefficient.
-/
lemma meromorphicTrailingCoeffAt_inv {f : 𝕜 → 𝕜} {hf : MeromorphicAt f x}
    (h : meromorphicOrderAt f x hf ≠ ⊤) {hf' : MeromorphicAt f⁻¹ x}
    {h' : meromorphicOrderAt f⁻¹ x hf' ≠ ⊤} :
    meromorphicTrailingCoeffAt f⁻¹ x h' = (meromorphicTrailingCoeffAt f x h)⁻¹ := by
  obtain ⟨g, h₁g, h₂g, h₃g⟩ := (meromorphicOrderAt_ne_top_iff hf).1 h
  rw [h₁g.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE h₂g h₃g,
    (h₁g.inv h₂g).meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE
      (n := -(meromorphicOrderAt f x hf).untop₀) (inv_ne_zero h₂g)]
  · rfl
  · filter_upwards [h₃g] with z hz
    simp [hz, zpow_neg, mul_comm]

/--
The trailing coefficient of the inverse function is the inverse of the trailing coefficient.
-/
lemma meromorphicTrailingCoeffAt_fun_inv {f : 𝕜 → 𝕜} {hf : MeromorphicAt f x}
    (h : meromorphicOrderAt f x hf ≠ ⊤) {hf' : MeromorphicAt (fun z ↦ (f z)⁻¹) x}
    {h' : meromorphicOrderAt (fun z ↦ (f z)⁻¹) x hf' ≠ ⊤} :
    meromorphicTrailingCoeffAt (fun z ↦ (f z)⁻¹) x h' = (meromorphicTrailingCoeffAt f x h)⁻¹ :=
  meromorphicTrailingCoeffAt_inv h

/--
The trailing coefficient of the power of a function is the power of the trailing coefficient.
-/
lemma MeromorphicAt.meromorphicTrailingCoeffAt_zpow {n : ℤ} {f : 𝕜 → 𝕜} (h₁ : MeromorphicAt f x)
    (h₂ : meromorphicOrderAt f x h₁ ≠ ⊤) {hf : MeromorphicAt (f ^ n) x}
    {h : meromorphicOrderAt (f ^ n) x hf ≠ ⊤} :
    meromorphicTrailingCoeffAt (f ^ n) x h = (meromorphicTrailingCoeffAt f x h₂) ^ n := by
  obtain ⟨g, h₁g, h₂g, h₃g⟩ := (meromorphicOrderAt_ne_top_iff h₁).1 h₂
  rw [h₁g.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE h₂g h₃g,
    (h₁g.zpow h₂g (n := n)).meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE
      (n := n * (meromorphicOrderAt f x h₁).untop₀) (zpow_ne_zero n h₂g)]
  · rfl
  · filter_upwards [h₃g] with a ha
    simp [ha, mul_zpow, ← zpow_mul, mul_comm]

/--
The trailing coefficient of the power of a function is the power of the trailing coefficient.
-/
lemma MeromorphicAt.meromorphicTrailingCoeffAt_fun_zpow {n : ℤ} {f : 𝕜 → 𝕜}
    (h₁ : MeromorphicAt f x) (h₂ : meromorphicOrderAt f x h₁ ≠ ⊤)
    {hf : MeromorphicAt (fun z ↦ f z ^ n) x} {h : meromorphicOrderAt (fun z ↦ f z ^ n) x hf ≠ ⊤} :
    meromorphicTrailingCoeffAt (fun z ↦ f z ^ n) x h = (meromorphicTrailingCoeffAt f x h₂) ^ n :=
  MeromorphicAt.meromorphicTrailingCoeffAt_zpow h₁ h₂

/--
The trailing coefficient of the power of a function is the power of the trailing coefficient.
-/
lemma MeromorphicAt.meromorphicTrailingCoeffAt_pow {n : ℕ} {f : 𝕜 → 𝕜}
    (h₁ : MeromorphicAt f x) (h₂ : meromorphicOrderAt f x h₁ ≠ ⊤) {hf : MeromorphicAt (f ^ n) x}
    {h : meromorphicOrderAt (f ^ n) x hf ≠ ⊤} :
    meromorphicTrailingCoeffAt (f ^ n) x h = (meromorphicTrailingCoeffAt f x h₂) ^ n := by
  have hz : meromorphicOrderAt (f ^ (n : ℤ)) x (h₁.zpow n) ≠ ⊤ := by
    rwa [← meromorphicOrderAt_congr hf (.of_eq (by ext; simp))]
  rw [meromorphicTrailingCoeffAt_congr_nhdsNE (.of_eq (by ext; simp)) (h₂ := hz),
    MeromorphicAt.meromorphicTrailingCoeffAt_zpow h₁ h₂, zpow_natCast]

/--
The trailing coefficient of the power of a function is the power of the trailing coefficient.
-/
lemma MeromorphicAt.meromorphicTrailingCoeffAt_fun_pow {n : ℕ} {f : 𝕜 → 𝕜}
    (h₁ : MeromorphicAt f x) (h₂ : meromorphicOrderAt f x h₁ ≠ ⊤)
    {hf : MeromorphicAt (fun z ↦ f z ^ n) x} {h : meromorphicOrderAt (fun z ↦ f z ^ n) x hf ≠ ⊤} :
    meromorphicTrailingCoeffAt (fun z ↦ f z ^ n) x h = (meromorphicTrailingCoeffAt f x h₂) ^ n :=
  MeromorphicAt.meromorphicTrailingCoeffAt_pow h₁ h₂

/-!
## Behavior under Composition
-/

/--
If `g` is analytic at `x` and not locally constant, and `f` is meromorphic of finite order at `g x`,
express the trailing coefficient of `f ∘ g` at `x` in terms of `g` and `f`.
-/
theorem MeromorphicAt.meromorphicTrailingCoeffAt_comp {g : 𝕜 → 𝕜} (hf : MeromorphicAt f (g x))
    (h₂f : meromorphicOrderAt f (g x) hf ≠ ⊤) (hg : AnalyticAt 𝕜 g x)
    (hg_nc : ¬EventuallyConst g (𝓝 x)) {hfg : MeromorphicAt (f ∘ g) x}
    {h : meromorphicOrderAt (f ∘ g) x hfg ≠ ⊤} :
    meromorphicTrailingCoeffAt (f ∘ g) x h =
      (meromorphicTrailingCoeffAt (g · - g x) x (hg.meromorphicOrderAt_sub_ne_top hg_nc)) ^
        (meromorphicOrderAt f (g x) hf).untop₀ • meromorphicTrailingCoeffAt f (g x) h₂f := by
  set r := (meromorphicOrderAt f (g x) hf).untop₀
  obtain ⟨F, h₁F, h₂F, h₃F⟩ := (meromorphicOrderAt_ne_top_iff hf).1 h₂f
  have hg' : MeromorphicAt (g · - g x) x := by fun_prop
  have hgfin : meromorphicOrderAt (g · - g x) x hg' ≠ ⊤ := hg.meromorphicOrderAt_sub_ne_top hg_nc
  have hpow : meromorphicOrderAt ((g · - g x) ^ r) x (hg'.zpow r) ≠ ⊤ := by
    rw [meromorphicOrderAt_zpow hg']
    exact WithTop.mul_ne_top WithTop.coe_ne_top hgfin
  have hFg : meromorphicOrderAt (F ∘ g) x (h₁F.comp hg).meromorphicAt ≠ ⊤ :=
    (h₁F.comp hg).meromorphicOrderAt_ne_top_of_ne_zero h₂F
  have hsmul : meromorphicOrderAt ((g · - g x) ^ r • (F ∘ g)) x
      ((hg'.zpow r).smul (h₁F.comp hg).meromorphicAt) ≠ ⊤ := by
    rw [meromorphicOrderAt_smul (hg'.zpow r) (h₁F.comp hg).meromorphicAt]
    exact WithTop.add_ne_top.2 ⟨hpow, hFg⟩
  have hpres : f ∘ g =ᶠ[𝓝[≠] x] (g · - g x) ^ r • (F ∘ g) :=
    h₃F.comp_tendsto (hg.map_nhdsNE hg_nc)
  rw [meromorphicTrailingCoeffAt_congr_nhdsNE hpres (h₂ := hsmul),
    MeromorphicAt.meromorphicTrailingCoeffAt_smul (hg'.zpow r) (h₁F.comp hg).meromorphicAt hpow hFg,
    (h₁F.comp hg).meromorphicTrailingCoeffAt_of_ne_zero h₂F,
    h₁F.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE h₂F h₃F,
    MeromorphicAt.meromorphicTrailingCoeffAt_zpow hg' hgfin]
  rfl

/-- `meromorphicTrailingCoeffAt` is invariant under translation. -/
@[to_fun meromorphicTrailingCoeffAt_fun_comp_add_const_eq_meromorphicTrailingCoeffAt]
theorem meromorphicTrailingCoeffAt_comp_add_const_eq_meromorphicTrailingCoeffAt {c : 𝕜}
    {hf : MeromorphicAt f (x + c)} (h : meromorphicOrderAt f (x + c) hf ≠ ⊤)
    {hf' : MeromorphicAt (f ∘ (· + c)) x} {h' : meromorphicOrderAt (f ∘ (· + c)) x hf' ≠ ⊤} :
    meromorphicTrailingCoeffAt (f ∘ (· + c)) x h' = meromorphicTrailingCoeffAt f (x + c) h := by
  classical
  have hnc : ¬ EventuallyConst (· + c) (𝓝 x) := by
    rw [eventuallyConst_iff_analyticOrderAt_sub_eq_top (by fun_prop)]
    simp
  rw [MeromorphicAt.meromorphicTrailingCoeffAt_comp (g := (· + c)) hf h (by fun_prop) hnc]
  simp [meromorphicTrailingCoeffAt_id_sub_const]

/-- `meromorphicTrailingCoeffAt` is invariant under translation. -/
@[to_fun meromorphicTrailingCoeffAt_fun_comp_sub_const_eq_meromorphicTrailingCoeffAt]
theorem meromorphicTrailingCoeffAt_comp_sub_const_eq_meromorphicTrailingCoeffAt {c : 𝕜}
    {hf : MeromorphicAt f (x - c)} (h : meromorphicOrderAt f (x - c) hf ≠ ⊤)
    {hf' : MeromorphicAt (f ∘ (· - c)) x} {h' : meromorphicOrderAt (f ∘ (· - c)) x hf' ≠ ⊤} :
    meromorphicTrailingCoeffAt (f ∘ (· - c)) x h' = meromorphicTrailingCoeffAt f (x - c) h := by
  classical
  have hnc : ¬ EventuallyConst (· - c) (𝓝 x) := by
    rw [eventuallyConst_iff_analyticOrderAt_sub_eq_top (by fun_prop)]
    simp
  rw [MeromorphicAt.meromorphicTrailingCoeffAt_comp (g := (· - c)) hf h (by fun_prop) hnc]
  simp [meromorphicTrailingCoeffAt_id_sub_const]
