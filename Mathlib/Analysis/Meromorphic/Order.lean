/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler, Stefan Kebekus
-/
module

public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.Algebra.Order.WithTop.Untop0
public import Mathlib.Analysis.Calculus.Deriv.ZPow

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

open Filter Set
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
noncomputable def meromorphicOrderAt {D : Type*} (f : D → E) (x : 𝕜) {coord : D → 𝕜}
    (hf : MeromorphicAt f x coord := by fun_prop_default) : WithTop ℤ :=
  let hg := hf.2.choose_spec.choose_spec.1
  (analyticOrderAt hf.2.choose_spec.choose x hg).map (↑· : ℕ → ℤ) + ↑(-(hf.2.choose : ℤ))

/-- Any local analytic numerator and clearing power compute the same order. -/
theorem MeromorphicAt.order_eq_of_presentation {D : Type*} {coord : D → 𝕜} {f : D → E}
    (hf : MeromorphicAt f x coord) {n : ℕ} {g : 𝕜 → E} (hg : AnalyticAt 𝕜 g x)
    (he : ∀ᶠ y in comap coord (𝓝[≠] x), (coord y - x) ^ n • f y = g (coord y)) :
    meromorphicOrderAt f x hf = (analyticOrderAt g x hg).map (↑· : ℕ → ℤ) + ↑(-(n : ℤ)) := by
  let m := hf.2.choose
  let a := hf.2.choose_spec.choose
  have ha : AnalyticAt 𝕜 a x := hf.2.choose_spec.choose_spec.1
  have hfa : ∀ᶠ y in comap coord (𝓝[≠] x), (coord y - x) ^ m • f y = a (coord y) :=
    hf.2.choose_spec.choose_spec.2
  let c : 𝕜 → 𝕜 := fun y ↦ y - x
  have hc : AnalyticAt 𝕜 c x := analyticAt_id.sub analyticAt_const
  have h₁ := (hc.pow n).smul ha
  have h₂ := (hc.pow m).smul hg
  have hcross : c ^ n • a =ᶠ[𝓝[≠] x] c ^ m • g := by
    rw [← map_comap_of_mem hf.1]
    apply Filter.eventually_map.mpr
    filter_upwards [he, hfa] with y hy hy'
    change (coord y - x) ^ n • a (coord y) = (coord y - x) ^ m • g (coord y)
    rw [← hy', ← hy, smul_comm]
  have H := analyticOrderAt_congr h₁ ((h₁.frequently_eq_iff_eventually_eq h₂).mp hcross.frequently)
  rw [analyticOrderAt_smul (hc.pow n) ha, analyticOrderAt_smul (hc.pow m) hg] at H
  have hcn (k : ℕ) : analyticOrderAt (c ^ k) x (hc.pow k) = k := analyticOrderAt_centeredMonomial
  rw [hcn, hcn] at H
  change (analyticOrderAt a x ha).map (↑· : ℕ → ℤ) + ↑(-(m : ℤ)) =
    (analyticOrderAt g x hg).map (↑· : ℕ → ℤ) + ↑(-(n : ℤ))
  cases hₐ : analyticOrderAt a x ha with
  | top =>
    have hg' : analyticOrderAt g x hg = ⊤ := by simpa [hₐ] using H.symm
    simp [hg']
  | coe k =>
    cases h₉ : analyticOrderAt g x hg with
    | top => simp [hₐ, h₉] at H
    | coe j =>
      simp only [hₐ, h₉, ← Nat.cast_add, Nat.cast_inj] at H
      simp only [ENat.map_natCast, ← WithTop.coe_add, WithTop.coe_inj]
      omega

/-- Representatives on different domains have the same order if their values agree above
every point of a punctured neighborhood. -/
theorem MeromorphicAt.order_eq_of_eventuallyEq {D D' : Type*} {c : D → 𝕜} {c' : D' → 𝕜}
    {f : D → E} {g : D' → E} (hf : MeromorphicAt f x c) (hg : MeromorphicAt g x c')
    (h : ∀ᶠ t in 𝓝[≠] x, ∀ a b, c a = t → c' b = t → f a = g b) :
    meromorphicOrderAt f x hf = meromorphicOrderAt g x hg := by
  obtain ⟨n, p, hp, he⟩ := hf.2
  rw [hf.order_eq_of_presentation hp he]
  symm
  apply hg.order_eq_of_presentation hp
  apply eventually_comap.mpr
  filter_upwards [hf.1, eventually_comap.mp he, h] with t ⟨a, hat⟩ hea hab
  intro b hbt
  rw [← hab a b hat hbt, hbt, ← hat]
  exact hea a hat

/-- Restricting a meromorphic representative to another punctured neighborhood preserves order. -/
theorem MeromorphicAt.order_comp_domain {D D' : Type*} {coord : D → 𝕜} {f : D → E}
    (hf : MeromorphicAt f x coord) (j : D' → D) (hc : range (coord ∘ j) ∈ 𝓝[≠] x) :
    meromorphicOrderAt (f ∘ j) x (hf.comp_domain j hc) = meromorphicOrderAt f x hf := by
  obtain ⟨n, g, hg, he⟩ := hf.2
  rw [hf.order_eq_of_presentation hg he]
  apply (hf.comp_domain j hc).order_eq_of_presentation hg
  rw [← comap_comap]
  exact tendsto_comap.eventually he

/-- Puncturally equal meromorphic representatives have the same order in their common domain. -/
theorem MeromorphicAt.order_congr_domain {D : Type*} {coord : D → 𝕜} {f g : D → E}
    (hf : MeromorphicAt f x coord) (he : f =ᶠ[comap coord (𝓝[≠] x)] g) :
    meromorphicOrderAt f x hf = meromorphicOrderAt g x (hf.congr_domain he) := by
  obtain ⟨n, a, ha, hfa⟩ := hf.2
  rw [hf.order_eq_of_presentation ha hfa]
  apply Eq.symm
  apply (hf.congr_domain he).order_eq_of_presentation ha
  exact hfa.mp (he.mono fun y hy hh ↦ hy ▸ hh)

/-- The order of a meromorphic function `f` at a `z₀` is infinity iff `f` vanishes locally around
`z₀`. -/
lemma meromorphicOrderAt_eq_top_iff (hf : MeromorphicAt f x) :
    meromorphicOrderAt f x hf = ⊤ ↔ ∀ᶠ z in 𝓝[≠] x, f z = 0 := by
  let w := MeromorphicAt.iff_exists_analyticAt_pow_smul.mp hf
  rw [hf.order_eq_of_presentation w.choose_spec (.of_forall fun _ ↦ rfl)]
  simp only [WithTop.add_eq_top, ENat.map_eq_top_iff, WithTop.coe_ne_top, or_false]
  by_cases h : analyticOrderAt (fun z ↦ (z - x) ^ w.choose • f z) x w.choose_spec = ⊤
  · simp only [h, eventually_nhdsWithin_iff, mem_compl_iff, mem_singleton_iff, true_iff]
    rw [analyticOrderAt_eq_top] at h
    filter_upwards [h] with z hf hz
    rwa [smul_eq_zero_iff_right <| pow_ne_zero _ (sub_ne_zero.mpr hz)] at hf
  · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp h
    simp only [← hm, ENat.natCast_ne_top, false_iff]
    contrapose h
    rw [analyticOrderAt_eq_top]
    rw [← w.choose_spec.frequently_eq_iff_eventually_eq analyticAt_const]
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
      ∃ g : 𝕜 → E, AnalyticAt 𝕜 g x ∧ g x ≠ 0 ∧
        ∀ᶠ z : {z : 𝕜 // z ≠ x} in comap Subtype.val (𝓝 x),
          f z = Checked.zpow (z.val - x) n
            (fun _ ↦ (sub_ne_zero.mpr z.property).isUnit) • g z := by
  let w := MeromorphicAt.iff_exists_analyticAt_pow_smul.mp hf
  rw [hf.order_eq_of_presentation w.choose_spec (.of_forall fun _ ↦ rfl)]
  by_cases h : analyticOrderAt (fun z ↦ (z - x) ^ w.choose • f z) x w.choose_spec = ⊤
  · rw [h, ENat.map_top, top_add,
      eq_false_intro WithTop.top_ne_coe, false_iff]
    rw [analyticOrderAt_eq_top] at h
    refine fun ⟨g, hg_an, hg_ne, hg_eq⟩ ↦ hg_ne ?_
    apply EventuallyEq.eq_of_nhds
    rw [EventuallyEq, ← AnalyticAt.frequently_eq_iff_eventually_eq hg_an analyticAt_const]
    apply Eventually.frequently
    rw [eventually_nhdsWithin_iff]
    rw [eventually_comap] at hg_eq
    filter_upwards [h, hg_eq] with z hfz hfz_eq hz
    have heq := hfz_eq ⟨z, hz⟩ rfl
    let u : 𝕜ˣ := (sub_ne_zero.mpr hz).isUnit.unit
    have heq' : f z = (↑(u ^ n) : 𝕜) • g z := by
      simpa only [(sub_ne_zero.mpr hz).isUnit.zpow_eq_val_unit_zpow] using heq
    rw [heq', ← mul_smul] at hfz
    exact (smul_eq_zero_iff_right
      (mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hz)) (u ^ n).ne_zero)).mp hfz
  · obtain ⟨m, h⟩ := ENat.ne_top_iff_exists.mp h
    rw [← h, ENat.map_natCast, ← WithTop.coe_add, WithTop.coe_inj]
    obtain ⟨g, hg_an, hg_ne, hg_eq⟩ := w.choose_spec.analyticOrderAt_eq_natCast.mp h.symm
    have heq : ∀ᶠ z : {z : 𝕜 // z ≠ x} in comap Subtype.val (𝓝 x),
        f z = Checked.zpow (z.val - x) (↑m - ↑w.choose : ℤ)
          (fun _ ↦ (sub_ne_zero.mpr z.property).isUnit) • g z := by
      filter_upwards [tendsto_comap.eventually hg_eq] with z hz
      let u : 𝕜ˣ := (sub_ne_zero.mpr z.property).isUnit.unit
      have heq' : f z = (↑(u ^ (↑m - ↑w.choose : ℤ)) : 𝕜) • g z := by
        rw [← smul_right_inj (u ^ (w.choose : ℤ)).ne_zero, ← mul_smul,
          ← Units.val_mul, ← zpow_add]
        have hi : (w.choose : ℤ) + (↑m - ↑w.choose : ℤ) = m := by omega
        rw [hi]
        simpa only [zpow_natCast, Units.val_pow_eq_pow_val, u, IsUnit.unit_spec] using hz
      rwa [(sub_ne_zero.mpr z.property).isUnit.zpow_eq_val_unit_zpow]
    exact ⟨fun h ↦ ⟨g, hg_an, hg_ne, h ▸ heq⟩,
      AnalyticAt.unique_eventuallyEq_zpow_smul_nonzero ⟨g, hg_an, hg_ne, heq⟩⟩
/--
The order of a meromorphic function `f` at `z₀` is finite iff `f` can locally be
written as `f z = (z - z₀) ^ order • g z`, where `g` is analytic and does not
vanish at `z₀`.
-/
theorem meromorphicOrderAt_ne_top_iff {f : 𝕜 → E} {z₀ : 𝕜} (hf : MeromorphicAt f z₀) :
    meromorphicOrderAt f z₀ hf ≠ ⊤ ↔ ∃ (g : 𝕜 → E), AnalyticAt 𝕜 g z₀ ∧ g z₀ ≠ 0 ∧
      ∀ᶠ z : {z : 𝕜 // z ≠ z₀} in comap Subtype.val (𝓝 z₀),
        f z = Checked.zpow (z.val - z₀) ((meromorphicOrderAt f z₀ hf).untop₀)
          (fun _ ↦ (sub_ne_zero.mpr z.property).isUnit) • g z :=
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
    exact hf.eventually_eq_zero_or_eventually_ne_zero.resolve_left
      ((meromorphicOrderAt_eq_top_iff hf).not.mp h)
  · intro h h₀
    rw [meromorphicOrderAt_eq_top_iff hf] at h₀
    obtain ⟨z, hz, hz'⟩ := (h.and h₀).exists
    exact hz hz'

/-- A puncturally nonzero meromorphic function has finite order. -/
theorem MeromorphicAt.isAddUnit_order_of_eventually_ne_zero {f : 𝕜 → E} (hf : MeromorphicAt f x)
    (hn : ∀ᶠ y in 𝓝[≠] x, f y ≠ 0) : IsAddUnit (meromorphicOrderAt f x hf) := by
  apply LinearOrderedAddCommGroupWithTop.isAddUnit_iff.mpr
  exact (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (x := x) (f := f) hf).mpr hn

/-- The order of a meromorphic function `f` at `z₀` is finite iff `f` has multiplicative inverse
in a sufficiently small neighborhood of `z₀`. -/
theorem meromorphicOrderAt_ne_top_iff_mul_inv_eventuallyEq {f : 𝕜 → 𝕜'} (hf : MeromorphicAt f x) :
    meromorphicOrderAt f x hf ≠ ⊤ ↔
      ∀ᶠ z in 𝓝[≠] x, ∃ hz : IsUnit (f z), f z * Checked.inv (f z) hz = 1 := by
  rw [meromorphicOrderAt_ne_top_iff_eventually_ne_zero hf]
  apply eventually_congr
  exact .of_forall fun z ↦
    ⟨fun h ↦ ⟨h.isUnit, mul_inv_cancel₀⟩, fun ⟨h, _⟩ ↦ h.ne_zero⟩

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
  have hmap : map (Subtype.val : {z : 𝕜 // z ≠ x} → 𝕜)
      (comap Subtype.val (𝓝 x)) = 𝓝[≠] x :=
    Filter.subtype_coe_map_comap {x}ᶜ (𝓝 x)
  rw [← hmap, tendsto_map'_iff]
  let u : {z : 𝕜 // z ≠ x} → 𝕜ˣ := fun z ↦ (sub_ne_zero.mpr z.property).isUnit.unit
  have hsub : Tendsto (fun z : {z : 𝕜 // z ≠ x} ↦ z.val - x)
      (comap Subtype.val (𝓝 x)) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · simpa only [sub_self] using
        (tendsto_comap : Tendsto (Subtype.val : {z : 𝕜 // z ≠ x} → 𝕜) _ (𝓝 x)).sub_const x
    · exact Eventually.of_forall fun z ↦ sub_ne_zero.mpr z.property
  have hu : Tendsto u (comap Subtype.val (𝓝 x))
      (comap (fun v : 𝕜ˣ ↦ (v : 𝕜)) (𝓝[≠] 0)) := by
    rw [tendsto_comap_iff]
    simpa only [Function.comp_def, u, IsUnit.unit_spec] using hsub
  have A : Tendsto (fun z : {z : 𝕜 // z ≠ x} ↦ ‖(↑(u z ^ m) : 𝕜) • g z‖)
      (comap Subtype.val (𝓝 x)) atTop := by
    simp only [norm_smul]
    have hpow : Tendsto (fun y : 𝕜ˣ ↦ (↑(y ^ m) : 𝕜))
        (comap (fun y : 𝕜ˣ ↦ (y : 𝕜)) (𝓝[≠] 0)) (Bornology.cobounded 𝕜) :=
      tendsto_zpow_nhdsNE_zero_cobounded m_neg
    exact Filter.Tendsto.atTop_mul_pos (C := ‖g x‖) (by simpa only [norm_pos_iff] using gx)
      (tendsto_norm_cobounded_atTop.comp (hpow.comp hu))
      (g_an.continuousAt.tendsto.comp tendsto_comap).norm
  apply A.congr'
  filter_upwards [hg] with z hz
  simpa only [Function.comp_def, (sub_ne_zero.mpr z.property).isUnit.zpow_eq_val_unit_zpow, u]
    using congrArg norm hz.symm

/-- If the order of a meromorphic function is zero, then this function converges to a nonzero
limit at this point. See also the iff version `tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero`. -/
lemma tendsto_ne_zero_of_meromorphicOrderAt_eq_zero
    (hf : MeromorphicAt f x) (ho : meromorphicOrderAt f x hf = 0) :
    ∃ c ≠ 0, Tendsto f (𝓝[≠] x) (𝓝 c) := by
  rcases (meromorphicOrderAt_eq_int_iff hf).1 ho with ⟨g, g_an, gx, hg⟩
  refine ⟨g x, gx, ?_⟩
  apply g_an.continuousAt.continuousWithinAt.tendsto.congr'
  rw [EventuallyEq, eventually_nhdsWithin_iff]
  rw [eventually_comap] at hg
  filter_upwards [hg] with y hy hne
  simpa using (hy ⟨y, hne⟩ rfl).symm

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
    rw [EventuallyEq, eventually_nhdsWithin_iff]
    rw [eventually_comap] at hg
    filter_upwards [hg] with y hy hne
    simpa only [zpow_natCast₀] using (hy ⟨y, hne⟩ rfl).symm

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
    filter_upwards [tendsto_comap.eventually (eventually_nhdsWithin_iff.mp hf₁₂), h₃g]
      with z hz hz'
    exact (hz z.property).symm.trans hz'

/-- Compatibility of notions of `order` for analytic and meromorphic functions. -/
lemma AnalyticAt.meromorphicOrderAt_eq (hf : AnalyticAt 𝕜 f x) :
    meromorphicOrderAt f x hf.meromorphicAt = (analyticOrderAt f x hf).map (↑) := by
  cases hn : analyticOrderAt f x hf
  · rw [ENat.map_top, meromorphicOrderAt_eq_top_iff]
    exact ((analyticOrderAt_eq_top hf).mp hn).filter_mono nhdsWithin_le_nhds
  · simp_rw [ENat.map_natCast, meromorphicOrderAt_eq_int_iff hf.meromorphicAt, zpow_natCast₀]
    rcases hf.analyticOrderAt_eq_natCast.mp hn with ⟨g, h1, h2, h3⟩
    exact ⟨g, h1, h2, tendsto_comap.eventually h3⟩

/--
When seen as meromorphic functions, analytic functions have nonnegative order.
-/
theorem AnalyticAt.meromorphicOrderAt_nonneg (hf : AnalyticAt 𝕜 f x) :
    0 ≤ meromorphicOrderAt f x hf.meromorphicAt := by
  simp [hf.meromorphicOrderAt_eq]

/-- A meromorphic function has non-negative order iff there exists an analytic extension. -/
theorem MeromorphicAt.meromorphicOrderAt_nonneg_iff {D : Type*} {coord : D → 𝕜} {f : D → E}
    (hf : MeromorphicAt f x coord) :
    0 ≤ meromorphicOrderAt f x hf ↔ IsRegular f x coord := by
  constructor
  · intro h
    obtain ⟨n, a, ha, he⟩ := hf.2
    rw [hf.order_eq_of_presentation ha he] at h
    have hle : n ≤ analyticOrderAt a x ha := by
      cases ho : analyticOrderAt a x ha with
      | top => simp
      | coe k =>
        rw [ho, ENat.map_natCast] at h
        change (0 : WithTop ℤ) ≤ ((k - (n : ℤ) : ℤ) : WithTop ℤ) at h
        have h' : (0 : ℤ) ≤ k - (n : ℤ) := by exact_mod_cast h
        exact_mod_cast (show n ≤ k by omega)
    obtain ⟨g, hg, hag⟩ := (natCast_le_analyticOrderAt ha).mp hle
    refine ⟨g, hg, ?_⟩
    filter_upwards [he, tendsto_comap.eventually (hag.filter_mono nhdsWithin_le_nhds),
      tendsto_comap.eventually (self_mem_nhdsWithin : ∀ᶠ t in 𝓝[≠] x, t ≠ x)] with y hy hy' hne
    exact (smul_right_inj (pow_ne_zero n (sub_ne_zero.mpr hne))).mp (hy.trans hy')
  · rintro ⟨g, hg, he⟩
    rw [hf.order_eq_of_presentation (n := 0) hg (he.mono fun y hy ↦ by
      simpa only [pow_zero, one_smul, Function.comp_apply] using hy)]
    simp

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
      rw [EventuallyEq, eventually_nhdsWithin_iff]
      rw [eventually_comap] at hg
      filter_upwards [hg] with z hz hne
      simpa only [zpow_natCast₀] using (hz ⟨z, hne⟩ rfl).symm
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

/-- A meromorphic representative of the punctured coordinate power has order `n`.
For negative `n`, the coordinate power is defined only away from the base point. -/
theorem meromorphicOrderAt_zpow_id_sub_const {n : ℤ} {f : 𝕜 → 𝕜}
    (hf : MeromorphicAt f x)
    (heq : ∀ᶠ z : {z : 𝕜 // z ≠ x} in comap Subtype.val (𝓝 x),
      f z = Checked.zpow (z.val - x) n
        (fun _ ↦ (sub_ne_zero.mpr z.property).isUnit)) :
    meromorphicOrderAt f x hf = n := by
  rw [meromorphicOrderAt_eq_int_iff hf]
  exact ⟨fun _ ↦ 1, analyticAt_const, one_ne_zero, by simpa using heq⟩

/-- The order of `(· - x) ^ n` at `x` is `n`. -/
@[simp, to_fun] theorem meromorphicOrderAt_pow_id_sub_const {n : ℕ} :
    meromorphicOrderAt ((· - x) ^ n) x = n := by
  rw [← WithTop.coe_natCast, meromorphicOrderAt_eq_int_iff]
  exact ⟨fun _ ↦ 1, analyticAt_const, one_ne_zero, by simp⟩

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
      filter_upwards [h₃F, h₃G] with a hfa hga
      simp only [(sub_ne_zero.mpr a.property).isUnit.zpow_eq_val_unit_zpow] at hfa hga ⊢
      simp [hfa, hga, smul_comm (F a), zpow_add, mul_smul]

/-- The order is additive when multiplying meromorphic functions. -/
@[to_fun] theorem meromorphicOrderAt_mul {D : Type*} {coord : D → 𝕜} {f g : D → 𝕜'}
    (hf : MeromorphicAt f x coord) (hg : MeromorphicAt g x coord) :
    meromorphicOrderAt (f * g) x (hf.mul hg) =
      meromorphicOrderAt f x hf + meromorphicOrderAt g x hg := by
  obtain ⟨m, a, ha, hfa⟩ := hf.2
  obtain ⟨n, b, hb, hgb⟩ := hg.2
  have he : ∀ᶠ y in comap coord (𝓝[≠] x), (coord y - x) ^ (m + n) • (f * g) y =
      (a * b) (coord y) := by
    filter_upwards [hfa, hgb] with y hy hy'
    simp only [Pi.mul_apply, ← hy, ← hy', smul_mul_smul_comm, pow_add]
  rw [(hf.mul hg).order_eq_of_presentation (ha.mul hb) he,
    hf.order_eq_of_presentation ha hfa, hg.order_eq_of_presentation hb hgb]
  have hab := meromorphicOrderAt_smul (R := 𝕜') ha.meromorphicAt hb.meromorphicAt
  change meromorphicOrderAt (a * b) x _ = _ at hab
  rw [(ha.mul hb).meromorphicOrderAt_eq, ha.meromorphicOrderAt_eq, hb.meromorphicOrderAt_eq] at hab
  rw [hab]
  generalize (analyticOrderAt a x ha).map (↑· : ℕ → ℤ) = A
  generalize (analyticOrderAt b x hb).map (↑· : ℕ → ℤ) = B
  cases A <;> cases B <;> simp [← WithTop.coe_add]
  omega

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

/-- The constant unit germ has order zero on any punctured domain. -/
theorem MeromorphicAt.order_eq_zero_of_eventuallyEq_one {D : Type*} {coord : D → 𝕜} {f : D → 𝕜'}
    (hf : MeromorphicAt f x coord) (he : f =ᶠ[comap coord (𝓝[≠] x)] 1) :
    meromorphicOrderAt f x hf = 0 := by
  have h1 : AnalyticAt 𝕜 (1 : 𝕜 → 𝕜') x := analyticAt_const
  have horder := hf.order_eq_of_presentation (n := 0) h1 (he.mono fun y hy ↦ by
    simpa only [pow_zero, one_smul, Pi.one_apply] using hy)
  simpa only [h1.analyticOrderAt_eq_zero.mpr one_ne_zero, ENat.map_zero, Nat.cast_zero,
    neg_zero, WithTop.coe_zero, add_zero] using horder

/-- The order multiplies by `n` when taking a meromorphic function to its `n`th power. -/
@[to_fun] theorem meromorphicOrderAt_pow {D : Type*} {coord : D → 𝕜} {f : D → 𝕜'}
    (hf : MeromorphicAt f x coord) {n : ℕ} :
    meromorphicOrderAt (f ^ n) x (hf.pow n) = n * meromorphicOrderAt f x hf := by
  induction n with
  | zero =>
    rw [Nat.cast_zero, zero_mul]
    exact (hf.pow 0).order_eq_zero_of_eventuallyEq_one (.of_eq (pow_zero f))
  | succ n ih =>
    rw [(hf.pow (n + 1)).order_congr_domain (.of_eq (pow_succ f n)),
      meromorphicOrderAt_mul (hf.pow n) hf, ih, Nat.cast_succ]
    cases meromorphicOrderAt f x hf
    · aesop
    · norm_cast
      push_cast
      ring

/-- The orders of two meromorphic germs whose product is one add to zero. -/
theorem MeromorphicAt.order_add_eq_zero_of_mul_eq_one {D : Type*} {coord : D → 𝕜} {f g : D → 𝕜'}
    (hf : MeromorphicAt f x coord) (hg : MeromorphicAt g x coord)
    (he : f * g =ᶠ[comap coord (𝓝[≠] x)] 1) :
    meromorphicOrderAt f x hf + meromorphicOrderAt g x hg = 0 :=
  (meromorphicOrderAt_mul hf hg).symm.trans ((hf.mul hg).order_eq_zero_of_eventuallyEq_one he)

/-- Two meromorphic germs whose product equals one have opposite orders. -/
theorem MeromorphicAt.order_of_mul_eq_one {D : Type*} {coord : D → 𝕜} {f g : D → 𝕜'}
    (hf : MeromorphicAt f x coord) (hg : MeromorphicAt g x coord)
    (he : f * g =ᶠ[comap coord (𝓝[≠] x)] 1) :
    meromorphicOrderAt g x hg = Checked.neg (meromorphicOrderAt f x hf)
      (.of_add_eq_zero _ (hf.order_add_eq_zero_of_mul_eq_one hg he)) :=
  (Checked.neg_eq_of_add_eq_zero _ (hf.order_add_eq_zero_of_mul_eq_one hg he)).symm

/-- A meromorphic germ has finite order when its unit locus covers a punctured neighborhood. -/
theorem MeromorphicAt.isAddUnit_order_of_unit_locus {D : Type*} {coord : D → 𝕜} {f : D → 𝕜'}
    (hf : MeromorphicAt f x coord)
    (hc : range (fun y : {y : D | IsUnit (f y)} ↦ coord y.val) ∈ 𝓝[≠] x) :
    IsAddUnit (meromorphicOrderAt f x hf) := by
  rw [← hf.order_comp_domain Subtype.val hc]
  exact .of_add_eq_zero _ ((hf.comp_domain Subtype.val hc).order_add_eq_zero_of_mul_eq_one
    (hf.inv hc) (.of_forall fun _ ↦ mul_inv_cancel₀))

/-- The order of the inverse is the negative of the order. -/
theorem meromorphicOrderAt_inv {D : Type*} {coord : D → 𝕜} {f : D → 𝕜'}
    (hf : MeromorphicAt f x coord)
    (hc : range (fun y : {y : D | IsUnit (f y)} ↦ coord y.val) ∈ 𝓝[≠] x) :
    meromorphicOrderAt (fun y : {y : D | IsUnit (f y)} ↦ Checked.inv (f y) y.property)
      x (hf.inv hc) =
        Checked.neg (meromorphicOrderAt f x hf) (hf.isAddUnit_order_of_unit_locus hc) := by
  simpa only [hf.order_comp_domain Subtype.val hc] using
    (hf.comp_domain Subtype.val hc).order_of_mul_eq_one (hf.inv hc)
      (.of_forall fun _ ↦ mul_inv_cancel₀)

/-- The order of a quotient is the difference of the orders on its true punctured domain. -/
theorem meromorphicOrderAt_div {D : Type*} {coord : D → 𝕜} {f g : D → 𝕜'}
    (hf : MeromorphicAt f x coord) (hg : MeromorphicAt g x coord)
    (hc : range (fun y : {y : D | IsUnit (g y)} ↦ coord y.val) ∈ 𝓝[≠] x) :
    meromorphicOrderAt (fun y : {y : D | IsUnit (g y)} ↦ Checked.div (f y) (g y) y.property)
      x (hf.div hg hc) = Checked.sub (meromorphicOrderAt f x hf) (meromorphicOrderAt g x hg)
        (hg.isAddUnit_order_of_unit_locus hc) := by
  have h := meromorphicOrderAt_mul (hf.comp_domain Subtype.val hc) (hg.inv hc)
  rw [hf.order_comp_domain Subtype.val hc, meromorphicOrderAt_inv hg hc] at h
  simpa only [Checked.sub_eq_add_neg] using! h

/-- Coverage of the domain of a negative power forces the order of the base to be finite. -/
theorem MeromorphicAt.isAddUnit_order_of_zpow_locus {D : Type*} {coord : D → 𝕜} {f : D → 𝕜'}
    (hf : MeromorphicAt f x coord) {n : ℤ}
    (hc : range (fun y : {y : D | n < 0 → IsUnit (f y)} ↦ coord y.val) ∈ 𝓝[≠] x) (hn : n < 0) :
    IsAddUnit (meromorphicOrderAt f x hf) :=
  hf.isAddUnit_order_of_unit_locus (mem_of_superset hc fun _ ⟨y, hy⟩ ↦
    ⟨⟨y.val, y.property hn⟩, hy⟩)

/-- The order of an integer power on its exponent-dependent domain. -/
theorem meromorphicOrderAt_zpow {D : Type*} {coord : D → 𝕜} {f : D → 𝕜'}
    (hf : MeromorphicAt f x coord) (n : ℤ)
    (hc : range (fun y : {y : D | n < 0 → IsUnit (f y)} ↦ coord y.val) ∈ 𝓝[≠] x) :
    meromorphicOrderAt (fun y : {y : D | n < 0 → IsUnit (f y)} ↦ Checked.zpow (f y) n y.property)
      x (hf.zpow n hc) = Checked.zsmul n (meromorphicOrderAt f x hf)
        (hf.isAddUnit_order_of_zpow_locus hc) := by
  cases n with
  | ofNat n =>
    have h := meromorphicOrderAt_pow (hf.comp_domain Subtype.val hc) (n := n)
    rw [hf.order_comp_domain Subtype.val hc] at h
    simp only [Int.ofNat_eq_natCast, Checked.zsmul_ofNat, zpow_natCast₀]
    apply h.trans
    cases meromorphicOrderAt f x hf with
    | top =>
      cases n with
      | zero => simp
      | succ n => exact WithTop.mul_top (by exact_mod_cast Nat.succ_ne_zero n)
    | coe k => exact congrArg ((↑) : ℤ → WithTop ℤ) (nsmul_eq_mul n k).symm
  | negSucc n =>
    have hu := hf.isAddUnit_order_of_zpow_locus hc (Int.negSucc_lt_zero n)
    obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp
      (LinearOrderedAddCommGroupWithTop.isAddUnit_iff.mp hu)
    have h := ((hf.comp_domain Subtype.val hc).pow (n + 1)).order_add_eq_zero_of_mul_eq_one
      (hf.zpow (Int.negSucc n) hc) (.of_forall fun y ↦ by
        change f y.val ^ (n + 1) * Checked.zpow (f y.val) (Int.negSucc n) y.property = 1
        rw [zpow_negSucc₀, mul_inv_cancel₀])
    rw [meromorphicOrderAt_pow (hf.comp_domain Subtype.val hc), hf.order_comp_domain Subtype.val hc,
      ← hk, ← WithTop.coe_natCast, ← WithTop.coe_mul] at h
    simp only [← hk, WithTop.checked_zsmul_coe]
    apply add_right_injective_of_ne_top (↑(((n + 1 : ℕ) : ℤ) * k) : WithTop ℤ) WithTop.coe_ne_top
    exact h.trans (congrArg ((↑) : ℤ → WithTop ℤ)
      (show 0 = ((n + 1 : ℕ) : ℤ) * k + Int.negSucc n • k by
        simp [Int.negSucc_eq]
        ring))

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
  obtain ⟨m, a, ha, hfa⟩ := hf₁.2
  obtain ⟨n, b, hb, hgb⟩ := hf₂.2
  let c : 𝕜 → 𝕜 := fun y ↦ y - x
  have hc : AnalyticAt 𝕜 c x := analyticAt_id.sub analyticAt_const
  let A := c ^ n • a
  let B := c ^ m • b
  have hA : AnalyticAt 𝕜 A x := (hc.pow n).smul ha
  have hB : AnalyticAt 𝕜 B x := (hc.pow m).smul hb
  have heA : ∀ᶠ y in comap _root_.id (𝓝[≠] x), (y - x) ^ (m + n) • f₁ y = A y := by
    filter_upwards [hfa] with y hy
    simp only [id_eq] at hy
    change (y - x) ^ (m + n) • f₁ y = (y - x) ^ n • a y
    rw [← hy, ← mul_smul, ← pow_add, Nat.add_comm n m]
  have heB : ∀ᶠ y in comap _root_.id (𝓝[≠] x), (y - x) ^ (m + n) • f₂ y = B y := by
    filter_upwards [hgb] with y hy
    simp only [id_eq] at hy
    change (y - x) ^ (m + n) • f₂ y = (y - x) ^ m • b y
    rw [← hy, ← mul_smul, ← pow_add]
  have he := (heA.and heB).mono fun y hy ↦
    calc (y - x) ^ (m + n) • (f₁ + f₂) y = _ := smul_add _ _ _
         _ = (A + B) y := congrArg₂ (· + ·) hy.1 hy.2
  rw [hf₁.order_eq_of_presentation hA heA, hf₂.order_eq_of_presentation hB heB,
    (hf₁.add hf₂).order_eq_of_presentation (hA.add hB) he]
  have hm : Monotone (fun t : ℕ∞ ↦ t.map (↑· : ℕ → ℤ) + ↑(-((m + n : ℕ) : ℤ))) := by
    intro i j hij
    cases i <;> cases j <;>
      simp_all
  exact hm.map_min.ge.trans (hm (le_analyticOrderAt_add hA hB))

/--
Helper lemma for `meromorphicOrderAt_add_of_ne`.
-/
lemma meromorphicOrderAt_add_eq_left_of_lt (hf₁ : MeromorphicAt f₁ x) (hf₂ : MeromorphicAt f₂ x)
    (h : meromorphicOrderAt f₁ x hf₁ < meromorphicOrderAt f₂ x hf₂) :
    meromorphicOrderAt (f₁ + f₂) x (hf₁.add hf₂) = meromorphicOrderAt f₁ x hf₁ := by
  refine le_antisymm ?_ (by simpa [h.le] using meromorphicOrderAt_add hf₁ hf₂)
  have h' := meromorphicOrderAt_add (hf₁.add hf₂) hf₂.neg
  rw [← meromorphicOrderAt_neg hf₂,
    meromorphicOrderAt_congr ((hf₁.add hf₂).add hf₂.neg)
      (.of_eq (add_neg_cancel_right f₁ f₂))] at h'
  exact (min_le_iff.mp h').resolve_right h.not_ge

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

A version of `meromorphicOrderAt_ne_top_iff_mul_inv_eventuallyEq` on the codiscrete filter.
The reciprocal at each point is formed only after its invertibility is established. -/
theorem mul_inv_eventuallyEq {f : 𝕜 → 𝕜'} (hf : MeromorphicOn f U) (hU : IsPreconnected U)
    (h0 : ¬f =ᶠ[codiscreteWithin U] 0) :
    ∀ᶠ z in codiscreteWithin U, ∃ hz : IsUnit (f z), f z * Checked.inv (f z) hz = 1 := by
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
  obtain ⟨m, hm⟩ := iff_exists_analyticAt_pow_smul.mp hf
  let a : 𝕜 → E := fun z ↦ (z - g x) ^ m • f z
  have ha : AnalyticAt 𝕜 a (g x) := hm
  let c : 𝕜 → 𝕜 := fun z ↦ g z - g x
  have hc : AnalyticAt 𝕜 c x := hg'
  have hf_order := hf.order_eq_of_presentation (n := m) ha (.of_forall fun _ ↦ rfl)
  have hna : analyticOrderAt a (g x) ha ≠ ⊤ := by
    intro h
    apply hf'
    simp [hf_order, h]
  have hnc : analyticOrderAt c x hc ≠ ⊤ := by
    exact fun h ↦ hg_nc ((eventuallyConst_iff_analyticOrderAt_sub_eq_top hg).mpr h)
  obtain ⟨r, hr⟩ := ENat.ne_top_iff_exists.mp hna
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hnc
  have hc' := hf.comp_analyticAt hg
  have ham : AnalyticAt 𝕜 (a ∘ g) x := ha.comp hg
  have He := meromorphicOrderAt_smul (hc.pow m).meromorphicAt hc'
  change meromorphicOrderAt (a ∘ g) x _ =
    meromorphicOrderAt (c ^ m) x _ + meromorphicOrderAt (f ∘ g) x hc' at He
  rw [ham.meromorphicOrderAt_eq, ha.analyticOrderAt_comp hg, (hc.pow m).meromorphicOrderAt_eq,
    analyticOrderAt_pow hc] at He
  change _ = _ * (analyticOrderAt c x hc).map (↑· : ℕ → ℤ)
  rw [hf_order, ← hr, ← hn]
  change (analyticOrderAt a (g x) ha * analyticOrderAt c x hc).map (↑· : ℕ → ℤ) =
    (m • analyticOrderAt c x hc).map (↑· : ℕ → ℤ) + _ at He
  rw [← hr, ← hn, nsmul_eq_mul, ← Nat.cast_mul, ← Nat.cast_mul] at He
  cases hcomp : meromorphicOrderAt (f ∘ g) x hc' with
  | top =>
    simp only [hcomp, ENat.map_natCast, add_top] at He
    exact (WithTop.coe_ne_top He).elim
  | coe k =>
    simp only [hcomp, ENat.map_natCast, ← WithTop.coe_add, WithTop.coe_inj] at He
    simp only [ENat.map_natCast, ← WithTop.coe_add, ← WithTop.coe_mul,
      WithTop.coe_inj]
    push_cast at He ⊢
    linear_combination -He

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
  meromorphicOrderAt_comp_of_deriv_ne_zero (g := (· + c)) hf (by fun_prop)
    (((hasDerivAt_id x).add_const c).deriv.trans_ne one_ne_zero)

/-- `meromorphicOrderAt` is invariant under translation. -/
@[to_fun meromorphicOrderAt_fun_comp_sub_const_eq_meromorphicOrderAt]
theorem meromorphicOrderAt_comp_sub_const_eq_meromorphicOrderAt {c : 𝕜} {f : 𝕜 → E}
    (hf : MeromorphicAt f (x - c)) :
    meromorphicOrderAt (f ∘ (· - c)) x (meromorphicAt_comp_sub_const_iff_meromorphicAt.2 hf) =
      meromorphicOrderAt f (x - c) hf :=
  meromorphicOrderAt_comp_of_deriv_ne_zero (g := (· - c)) hf (by fun_prop)
    (((hasDerivAt_id x).sub_const c).deriv.trans_ne one_ne_zero)

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
  obtain ⟨g, hga, hg0, hg⟩ := hfn
  have hn' : n ≠ 0 := fun h ↦ hn (by simp [h])
  let S := {y : 𝕜 | n < 0 → IsUnit (y - x)}
  let p : S → 𝕜 := fun y ↦ Checked.zpow (y.val - x) n y.property
  let P : 𝕜 → 𝕜 := Function.extend Subtype.val p 0
  have hP (y : S) : P y = p y := Subtype.val_injective.extend_apply _ _ y
  have hup {y : 𝕜} (hy : y ≠ x) : y ∈ S := fun _ ↦ (sub_ne_zero.mpr hy).isUnit
  have hdiff (y : 𝕜) (hy : y ≠ x) :
      HasDerivAt P ((n : 𝕜) *
        Checked.zpow (y - x) (n - 1) (fun _ ↦ (sub_ne_zero.mpr hy).isUnit)) y := by
    have h₀ : HasDerivAt (fun w : 𝕜 ↦ w - x) 1 y := (hasDerivAt_id y).sub_const x
    have hs : S ∈ 𝓝 y := (eventually_ne_nhds hy).mono (fun _ hw ↦ hup hw)
    have hp := h₀.zpow n (hup hy)
    rw [hasDerivAt_iff_hasFDerivAt]
    apply HasFDerivAt.of_restrict (s := S) (x := (⟨y, hup hy⟩ : S)) _ hs
    simpa only [hP, p, Function.comp_def, id_eq, dite_eq_right hn', mul_one] using! hp.hasFDerivAt
  have he : f =ᶠ[𝓝[≠] x] fun z ↦ P z • g z := by
    rw [EventuallyEq, eventually_nhdsWithin_iff]
    rw [eventually_comap] at hg
    filter_upwards [hg] with y hy hyx
    exact (hy ⟨y, hyx⟩ rfl).trans (congrArg (· • g y) (hP ⟨y, hup hyx⟩).symm)
  refine ⟨fun z ↦ (n : 𝕜) • g z + (z - x) • deriv g z, ?_, ?_, ?_⟩
  · exact (hga.fun_const_smul).add ((analyticAt_id.sub analyticAt_const).fun_smul hga.deriv)
  · simpa using (smul_ne_zero hn hg0)
  have ht : Tendsto (Subtype.val : {y : 𝕜 // y ≠ x} → 𝕜) (comap Subtype.val (𝓝 x)) (𝓝[≠] x) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_comap, .of_forall fun z ↦ z.property⟩
  filter_upwards [tendsto_comap.eventually hga.eventually_analyticAt, ht.eventually he.nhdsNE_deriv]
    with z hz hd
  have hp := (hdiff z z.property).fun_smul hz.differentiableAt.hasDerivAt
  have hu := (sub_ne_zero.mpr z.property).isUnit
  have hpow : Checked.zpow (z.val - x) n (fun _ ↦ hu) =
      Checked.zpow (z.val - x) (n - 1) (fun _ ↦ hu) * (z.val - x) := by
    simpa only [sub_add_cancel] using zpow_add_one₀ (sub_ne_zero.mpr z.property) (n - 1)
  rw [hd]
  apply hp.deriv.trans
  rw [hP ⟨z.val, hup z.property⟩]
  change Checked.zpow (z.val - x) n (fun _ ↦ hu) • deriv g z +
      ((n : 𝕜) * Checked.zpow (z.val - x) (n - 1) (fun _ ↦ hu)) • g z = _
  rw [hpow, smul_add, ← mul_smul, ← mul_smul, mul_comm (n : 𝕜), add_comm]

/-- Equivalent to `meromorphicOrderAt_deriv_eq_sub_one` with a slightly different statement so the
conclusion matches more targets -/
lemma meromorphicOrderAt_deriv [CompleteSpace E] {f : 𝕜 → E} {x : 𝕜} {n : ℤ}
    (hf : MeromorphicAt f x) (hn : (↑(n + 1) : 𝕜) ≠ 0)
    (hfn : meromorphicOrderAt f x hf = ↑(n + 1)) :
    meromorphicOrderAt (deriv f) x hf.deriv = ↑n := by
  simpa using meromorphicOrderAt_deriv_eq_sub_one hf hn hfn
variable [CompleteSpace 𝕜] {f : 𝕜 → 𝕜}

/-- The order of the logarithmic derivative on its regular scalar domain is the order
of the derivative minus that of the function. -/
theorem meromorphicOrderAt_logDeriv (hf : MeromorphicAt f x) (hn : ∀ᶠ y in 𝓝[≠] x, f y ≠ 0) :
    meromorphicOrderAt (coord := (Subtype.val :
        {y : 𝕜 | DifferentiableAt 𝕜 f y ∧ IsUnit (f y)} → 𝕜))
      _ x (MeromorphicAt.logDeriv (𝕜 := 𝕜) (𝕜' := 𝕜) (f := f) (x := x) hf hn) =
      Checked.sub (meromorphicOrderAt (coord := _root_.id) (deriv f) x hf.deriv)
        (meromorphicOrderAt (coord := _root_.id) f x hf)
        (MeromorphicAt.isAddUnit_order_of_eventually_ne_zero (x := x) (f := f) hf hn) := by
  let S := {y : 𝕜 | DifferentiableAt 𝕜 f y ∧ IsUnit (f y)}
  have hc : range (Subtype.val : S → 𝕜) ∈ 𝓝[≠] x := by
    rw [Subtype.range_coe]
    exact (hf.eventually_analyticAt.and hn).mono fun y hy ↦ ⟨hy.1.differentiableAt, hy.2.isUnit⟩
  let r := fun y : S ↦ Checked.inv (f y) y.property.2
  have hf' := hf.comp_domain (Subtype.val : S → 𝕜) hc
  have hd := hf.deriv.comp_domain (Subtype.val : S → 𝕜) hc
  have he : (f ∘ (Subtype.val : S → 𝕜)) * r =ᶠ[comap Subtype.val (𝓝[≠] x)] 1 :=
    .of_forall fun y ↦ mul_inv_cancel₀ (ha := y.property.2)
  have hr : MeromorphicAt r x (Subtype.val : S → 𝕜) := hf'.of_mul_eq_one he
  have hlog := hf.logDeriv hn
  rw [hlog.order_congr_domain (g := ((fun y ↦ deriv f y _root_.id) ∘ (Subtype.val : S → 𝕜)) * r)
    (.of_forall fun y ↦ logDeriv_apply f y.val (hderiv := y.property.1.existsUnique_hasDerivAt)
      (hvalue := y.property.2)),
    meromorphicOrderAt_mul hd hr, hf'.order_of_mul_eq_one hr he,
    hf.deriv.order_comp_domain Subtype.val hc, Checked.sub_eq_add_neg]
  simp only [hf.order_comp_domain Subtype.val hc]

/-- At zeros and poles in characteristic zero the logarithmic derivative has a simple pole. -/
theorem meromorphicOrderAt_logDeriv_eq_neg_one [CharZero 𝕜] (hf : MeromorphicAt f x)
    (h₁ : meromorphicOrderAt f x hf ≠ 0) (h₂ : meromorphicOrderAt f x hf ≠ ⊤) :
    meromorphicOrderAt (coord := (Subtype.val :
        {y : 𝕜 | DifferentiableAt 𝕜 f y ∧ IsUnit (f y)} → 𝕜))
      _ x (MeromorphicAt.logDeriv (𝕜 := 𝕜) (𝕜' := 𝕜) (f := f) (x := x) hf (by
        exact (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (x := x) (f := f) hf).mp
          h₂)) = ↑(-1 : ℤ) := by
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp h₂
  have hn' : (n : 𝕜) ≠ 0 := Int.cast_ne_zero.mpr fun he ↦ h₁ (by simp [← hn, he])
  rw [meromorphicOrderAt_logDeriv hf ((meromorphicOrderAt_ne_top_iff_eventually_ne_zero hf).mp h₂),
    meromorphicOrderAt_deriv_eq_sub_one hf hn' hn.symm]
  simp only [← hn, WithTop.checked_sub_coe, show n - 1 - n = -1 by omega]

/-- At a point of order zero the logarithmic derivative has nonnegative order. -/
theorem meromorphicOrderAt_logDeriv_nonneg (hf : MeromorphicAt f x)
    (h : meromorphicOrderAt f x hf = 0) :
    0 ≤ meromorphicOrderAt (coord := (Subtype.val :
        {y : 𝕜 | DifferentiableAt 𝕜 f y ∧ IsUnit (f y)} → 𝕜))
      _ x (MeromorphicAt.logDeriv (𝕜 := 𝕜) (𝕜' := 𝕜) (f := f) (x := x) hf (by
        apply (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (x := x) (f := f) hf).mp
        rw [h]
        exact WithTop.zero_ne_top)) := by
  obtain ⟨g, hg, he⟩ := hf.meromorphicOrderAt_nonneg_iff.mp h.ge
  have he' : f =ᶠ[𝓝[≠] x] g := by simpa only [comap_id, Function.comp_id] using he
  have hn := (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hf).mp (h ▸ WithTop.zero_ne_top)
  rw [meromorphicOrderAt_logDeriv hf hn, Checked.sub_eq_add_neg,
    meromorphicOrderAt_congr hf.deriv he'.nhdsNE_deriv]
  have hneg (hu : IsAddUnit (0 : WithTop ℤ)) : Checked.neg (0 : WithTop ℤ) hu = 0 :=
    Checked.neg_eq_of_add_eq_zero hu (add_zero _)
  simpa only [h, hneg, add_zero] using hg.deriv.meromorphicOrderAt_nonneg

end deriv
