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

/-- Clearing a pole and factoring its analytic numerator produces a nonvanishing analytic
factor for a meromorphic function on arbitrary punctured coordinates. -/
theorem MeromorphicAt.exists_analytic_factor {D : Type*} {coord : D → 𝕜} {f : D → E}
    (hf : MeromorphicAt f x coord) (h : meromorphicOrderAt f x hf ≠ ⊤) :
    ∃ g : 𝕜 → E, AnalyticAt 𝕜 g x ∧ g x ≠ 0 ∧
      ∀ᶠ y in comap coord (𝓝[≠] x), ∀ hy : coord y ≠ x,
        f y = Checked.zpow (coord y - x) ((meromorphicOrderAt f x hf).untop h)
          (fun _ ↦ (sub_ne_zero.mpr hy).isUnit) • g (coord y) := by
  obtain ⟨m, a, ha, he⟩ := hf.2
  have hfOrder := hf.order_eq_of_presentation ha he
  have hfin : analyticOrderAt a x ha ≠ ⊤ := by
    intro ht
    exact h (by simpa [ht] using hfOrder)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin
  obtain ⟨g, hg, hgx, hag⟩ := ha.analyticOrderAt_eq_natCast.mp hn.symm
  have ho : (meromorphicOrderAt f x hf).untop h = (n : ℤ) - m := by
    apply WithTop.coe_injective
    rw [WithTop.coe_untop, hfOrder, ← hn, ENat.map_natCast,
      WithTop.LinearOrderedAddCommGroup.coe_sub]
    rfl
  refine ⟨g, hg, hgx, ?_⟩
  filter_upwards [he, tendsto_comap.eventually (hag.filter_mono nhdsWithin_le_nhds)] with y hya hyg
  intro hy
  let u := (sub_ne_zero.mpr hy).isUnit.unit
  rw [ho, (sub_ne_zero.mpr hy).isUnit.zpow_eq_val_unit_zpow]
  rw [← smul_right_inj (u ^ (m : ℤ)).ne_zero, ← mul_smul, ← Units.val_mul, ← zpow_add,
    show (m : ℤ) + (n - m) = n by omega]
  simpa only [zpow_natCast, Units.val_pow_eq_pow_val, u, IsUnit.unit_spec] using hya.trans hyg

/--
If `f` is meromorphic of finite order at a point `x`, the trailing coefficient is the (unique!)
value `g x` for a presentation of `f` in the form `(z - x) ^ order • g z` with `g` analytic at `x`.
The meromorphy proof is determined by the finiteness proof `h`.
-/
noncomputable def meromorphicTrailingCoeffAt {D : Type*} (f : D → E) (x : 𝕜)
    {coord : D → 𝕜} {hf : MeromorphicAt f x coord}
    (h : meromorphicOrderAt f x hf ≠ ⊤) : E :=
  (hf.exists_analytic_factor h).choose x

/-!
## Finiteness of the Order
-/

/-- An analytic function that does not vanish at `x` has finite order at `x`. -/
lemma AnalyticAt.meromorphicOrderAt_ne_top_of_ne_zero (h₁ : AnalyticAt 𝕜 f x) (h₂ : f x ≠ 0) :
    meromorphicOrderAt f x h₁.meromorphicAt ≠ ⊤ := by
  rw [h₁.meromorphicOrderAt_eq, h₁.analyticOrderAt_eq_zero.2 h₂]
  simp

/-- An analytic function on a neighborhood of a preconnected set `U` that does not vanish at a point
of `U` has finite order at every point of `U`. -/
lemma AnalyticOnNhd.meromorphicOrderAt_ne_top_of_ne_zero {U : Set 𝕜} (h₁ : AnalyticOnNhd 𝕜 f U)
    (hU : IsPreconnected U) (hx : x ∈ U) (h₂ : f x ≠ 0) :
    ∀ z (hz : z ∈ U), meromorphicOrderAt f z (h₁.meromorphicOn z hz) ≠ ⊤ :=
  fun _ hz ↦ h₁.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected hU hx hz
    ((h₁ x hx).meromorphicOrderAt_ne_top_of_ne_zero h₂)

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
lemma AnalyticAt.meromorphicTrailingCoeffAt_of_eq_nhdsNE {D : Type*} {coord : D → 𝕜} {f : D → E}
    (hg : AnalyticAt 𝕜 g x) (hf : MeromorphicAt f x coord) (h : meromorphicOrderAt f x hf ≠ ⊤)
    (he : ∀ᶠ y in comap coord (𝓝[≠] x), ∀ hy : coord y ≠ x,
      f y = Checked.zpow (coord y - x) ((meromorphicOrderAt f x hf).untop h)
        (fun _ ↦ (sub_ne_zero.mpr hy).isUnit) • g (coord y)) :
    meromorphicTrailingCoeffAt f x h = g x := by
  let a := (hf.exists_analytic_factor h).choose
  obtain ⟨ha, _, hfa⟩ := (hf.exists_analytic_factor h).choose_spec
  change a x = g x
  have hag : a =ᶠ[𝓝[≠] x] g := by
    rw [← map_comap_of_mem hf.1]
    apply eventually_map.mpr
    filter_upwards [hfa, he, tendsto_comap.eventually
      (self_mem_nhdsWithin : ∀ᶠ t in 𝓝[≠] x, t ≠ x)] with y h₁ h₂ hy
    let u := (sub_ne_zero.mpr hy).isUnit
    have hmul := (h₁ hy).symm.trans (h₂ hy)
    rw [u.zpow_eq_val_unit_zpow] at hmul
    exact (smul_right_inj (u.unit ^ _).ne_zero).mp hmul
  exact Filter.EventuallyEq.eq_of_nhds ((ha.frequently_eq_iff_eventually_eq hg).mp hag.frequently)

/--
Variant of `AnalyticAt.meromorphicTrailingCoeffAt_of_eq_nhdsNE`: the trailing coefficient of a
function presented as `(z - x) ^ n • g z` near `x`, with `g` analytic at `x` and `g x ≠ 0`.
-/
lemma AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE {n : ℤ}
    (hg : AnalyticAt 𝕜 g x) (hgx : g x ≠ 0) {hf : MeromorphicAt f x}
    {h : meromorphicOrderAt f x hf ≠ ⊤}
    (he : ∀ᶠ z : {z : 𝕜 // z ≠ x} in comap Subtype.val (𝓝 x),
      f z = Checked.zpow (z.val - x) n (fun _ ↦ (sub_ne_zero.mpr z.property).isUnit) • g z) :
    meromorphicTrailingCoeffAt f x h = g x := by
  have ho := (meromorphicOrderAt_eq_int_iff hf).mpr ⟨g, hg, hgx, he⟩
  apply hg.meromorphicTrailingCoeffAt_of_eq_nhdsNE hf h
  have hn : (meromorphicOrderAt f x hf).untop h = n := WithTop.coe_injective
    ((WithTop.coe_untop _ _).trans ho)
  rw [hn, comap_id]
  filter_upwards [(eventually_comap.mp he).filter_mono nhdsWithin_le_nhds] with y hy
  exact fun hne ↦ hy ⟨y, hne⟩ rfl

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
lemma MeromorphicAt.tendsto_nhds_meromorphicTrailingCoeffAt {D : Type*} {coord : D → 𝕜} {f : D → E}
    (hf : MeromorphicAt f x coord) (h : meromorphicOrderAt f x hf ≠ ⊤) :
    Tendsto (fun y : {y : D | coord y ≠ x} ↦
      Checked.zpow (coord y - x) (-(meromorphicOrderAt f x hf).untop h)
        (fun _ ↦ (sub_ne_zero.mpr y.property).isUnit) • f y)
      (comap (coord ∘ Subtype.val) (𝓝[≠] x)) (𝓝 (meromorphicTrailingCoeffAt f x h)) := by
  let a := (hf.exists_analytic_factor h).choose
  have ha : AnalyticAt 𝕜 a x := (hf.exists_analytic_factor h).choose_spec.1
  have he := (hf.exists_analytic_factor h).choose_spec.2.2
  let c := coord ∘ (Subtype.val : {y : D | coord y ≠ x} → D)
  have ht : Tendsto c (comap c (𝓝[≠] x)) (𝓝 x) :=
    tendsto_comap.mono_right nhdsWithin_le_nhds
  apply (ha.continuousAt.tendsto.comp ht).congr'
  rw [← comap_comap]
  filter_upwards [tendsto_comap.eventually he] with y hy
  let u := (sub_ne_zero.mpr y.property).isUnit
  rw [hy y.property, u.zpow_eq_val_unit_zpow, u.zpow_eq_val_unit_zpow, zpow_neg]
  exact (inv_smul_smul (u.unit ^ _) (a (coord y))).symm

/-!
## Elementary Properties
-/

/--
The trailing coefficient of a function that is meromorphic of finite order is not zero.
-/
lemma MeromorphicAt.meromorphicTrailingCoeffAt_ne_zero {D : Type*} {coord : D → 𝕜} {f : D → E}
    (hf : MeromorphicAt f x coord) (h : meromorphicOrderAt f x hf ≠ ⊤) :
    meromorphicTrailingCoeffAt f x h ≠ 0 :=
  (hf.exists_analytic_factor h).choose_spec.2.1

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

/-- Representatives over different coordinate domains have the same leading coefficient
when they agree above every point of a punctured neighborhood. -/
theorem MeromorphicAt.trailingCoeff_eq_of_eventuallyEq {D D' : Type*} {c : D → 𝕜} {c' : D' → 𝕜}
    {f : D → E} {g : D' → E} (hf : MeromorphicAt f x c) (hg : MeromorphicAt g x c')
    {h₁ : meromorphicOrderAt f x hf ≠ ⊤} {h₂ : meromorphicOrderAt g x hg ≠ ⊤}
    (he : ∀ᶠ t in 𝓝[≠] x, ∀ a b, c a = t → c' b = t → f a = g b) :
    meromorphicTrailingCoeffAt f x h₁ = meromorphicTrailingCoeffAt g x h₂ := by
  let p := (hf.exists_analytic_factor h₁).choose
  have hp : AnalyticAt 𝕜 p x := (hf.exists_analytic_factor h₁).choose_spec.1
  have hfp := (hf.exists_analytic_factor h₁).choose_spec.2.2
  have ho : (meromorphicOrderAt g x hg).untop h₂ = (meromorphicOrderAt f x hf).untop h₁ := by
    apply WithTop.coe_injective
    simpa only [WithTop.coe_untop] using (hf.order_eq_of_eventuallyEq hg he).symm
  symm
  apply hp.meromorphicTrailingCoeffAt_of_eq_nhdsNE hg h₂
  apply eventually_comap.mpr
  filter_upwards [hf.1, he, eventually_comap.mp hfp] with t ⟨a, hat⟩ he ha
  intro b hbt hn
  have hc : c' b = c a := hbt.trans hat.symm
  rw [ho, ← he a b hat hbt]
  simpa only [hc] using ha a hat (hc ▸ hn)

/-- Puncturally equal ambient functions have the same leading coefficient. -/
lemma meromorphicTrailingCoeffAt_congr_nhdsNE {f₁ f₂ : 𝕜 → E} (h : f₁ =ᶠ[𝓝[≠] x] f₂)
    {hf₁ : MeromorphicAt f₁ x} {h₁ : meromorphicOrderAt f₁ x hf₁ ≠ ⊤}
    {hf₂ : MeromorphicAt f₂ x} {h₂ : meromorphicOrderAt f₂ x hf₂ ≠ ⊤} :
    meromorphicTrailingCoeffAt f₁ x h₁ = meromorphicTrailingCoeffAt f₂ x h₂ :=
  hf₁.trailingCoeff_eq_of_eventuallyEq hf₂ (h.mono fun t he a b ha hb ↦
    (congrArg f₁ (show a = t from ha)).trans (he.trans (congrArg f₂ (show b = t from hb)).symm))

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
    have he := eventually_nhdsWithin_iff.mp ((meromorphicOrderAt_eq_top_iff hf₂).mp h₁f₂)
    filter_upwards [tendsto_comap.eventually he, h₃g₁] with z h₁z h₂z
    simpa only [Pi.add_apply, h₁z z.property, add_zero] using h₂z
  -- General case
  obtain ⟨n₂, hn₂⟩ := WithTop.ne_top_iff_exists.1 h₁f₂
  obtain ⟨g₂, h₁g₂, h₂g₂, h₃g₂⟩ := (meromorphicOrderAt_eq_int_iff hf₂).1 hn₂.symm
  have hn : n₁ < n₂ := by
    rw [← WithTop.coe_lt_coe, hn₁, hn₂]
    exact h
  let k := (n₂ - n₁).toNat
  have hk : (k : ℤ) = n₂ - n₁ := Int.toNat_of_nonneg (sub_nonneg.mpr hn.le)
  have hk' : k ≠ 0 := by omega
  let G := fun z ↦ g₁ z + (z - x) ^ k • g₂ z
  have hG : AnalyticAt 𝕜 G x :=
    h₁g₁.fun_add (((analyticAt_id.sub analyticAt_const).pow k).fun_smul h₁g₂)
  have hGx : G x = g₁ x := by simp [G, hk']
  rw [← hGx]
  apply hG.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE (n := n₁) (hGx ▸ h₂g₁)
  filter_upwards [h₃g₁, h₃g₂] with z h₁z h₂z
  let u := (sub_ne_zero.mpr z.property).isUnit.unit
  simp only [(sub_ne_zero.mpr z.property).isUnit.zpow_eq_val_unit_zpow] at h₁z h₂z ⊢
  have he : (↑(u ^ n₁) : 𝕜) * (z.val - x) ^ k = (↑(u ^ n₂) : 𝕜) := by
    have hsum : n₁ + k = n₂ := by omega
    simpa only [zpow_add, zpow_natCast, Units.val_mul, Units.val_pow_eq_pow_val, u,
      IsUnit.unit_spec] using congrArg (fun n : ℤ ↦ (↑(u ^ n) : 𝕜)) hsum
  simp only [Pi.add_apply, h₁z, h₂z, G, smul_add, ← mul_smul]
  exact congrArg (fun c : 𝕜 ↦ (↑(u ^ n₁) : 𝕜) • g₁ z + c • g₂ z) he.symm

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
  apply (h₁g₁.add h₁g₂).meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE (n := n₁) h₂
  filter_upwards [h₃g₁, h₃g₂] with z h₁z h₂z
  simp only [Pi.add_apply, h₁z, h₂z, smul_add]

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
  rw [h₁g₁.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE h₂g₁ h₃g₁,
    h₁g₂.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE h₂g₂ h₃g₂]
  apply (h₁g₁.smul h₁g₂).meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE
    (n := (meromorphicOrderAt f₁ x hf₁).untop₀ + (meromorphicOrderAt f₂ x hf₂).untop₀)
    (smul_ne_zero h₂g₁ h₂g₂)
  filter_upwards [h₃g₁, h₃g₂] with z h₁z h₂z
  simp only [(sub_ne_zero.mpr z.property).isUnit.zpow_eq_val_unit_zpow] at h₁z h₂z ⊢
  simp [h₁z, h₂z, smul_comm (g₁ z), zpow_add, mul_smul]

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

/-- A unit-valued analytic germ has an analytic representative for each integer power. -/
private theorem analyticAt_exists_zpow {g : 𝕜 → 𝕜} (hg : AnalyticAt 𝕜 g x) (hgx : g x ≠ 0) (n : ℤ) :
    ∃ G : 𝕜 → 𝕜, AnalyticAt 𝕜 G x ∧
      ∀ᶠ z in 𝓝 x, ∀ hu : IsUnit (g z), G z = Checked.zpow (g z) n (fun _ ↦ hu) := by
  cases n with
  | ofNat k => exact ⟨g ^ k, hg.pow k, .of_forall fun _ _ ↦ (zpow_natCast₀ _ _).symm⟩
  | negSucc k =>
      obtain ⟨v, hv, he⟩ := hg.exists_mul_eq_one hgx.isUnit
      refine ⟨v ^ (k + 1), hv.pow _, he.mono fun z hz hu ↦ ?_⟩
      rw [hu.zpow_eq_val_unit_zpow, zpow_negSucc, ← inv_pow, Units.val_pow_eq_pow_val]
      change v z ^ (k + 1) = (↑hu.unit⁻¹ : 𝕜) ^ (k + 1)
      apply congrArg (· ^ (k + 1))
      exact (inv_eq_of_mul_eq_one_right₀ (ha := hu) hz).symm.trans
        (inv_eq_val_inv_of_eq_val₀ hu.unit hu.unit_spec.symm)

private theorem zpow_of_eq_zpow_mul (a c b : 𝕜) (r n : ℤ)
    (uc : IsUnit c) (ub : IsUnit b) (ua : n < 0 → IsUnit a)
    (hab : a = Checked.zpow c r (fun _ ↦ uc) * b) :
    Checked.zpow a n ua = Checked.zpow c (n * r) (fun _ ↦ uc) * Checked.zpow b n (fun _ ↦ ub) := by
  subst a
  rw [mul_zpow₀, zpow_mul₀' uc.ne_zero]

/-- The trailing coefficient of an integer power on its actual domain is the corresponding
power of the nonzero leading coefficient. -/
lemma MeromorphicAt.meromorphicTrailingCoeffAt_zpow {D : Type*} {coord : D → 𝕜} {f : D → 𝕜}
    (hf : MeromorphicAt f x coord) (h : meromorphicOrderAt f x hf ≠ ⊤) (n : ℤ)
    {hp : MeromorphicAt (fun y : {y : D | n < 0 → IsUnit (f y)} ↦ Checked.zpow (f y) n y.2)
      x (coord ∘ Subtype.val)} {h' : meromorphicOrderAt _ x hp ≠ ⊤} :
    meromorphicTrailingCoeffAt _ x h' = Checked.zpow (meromorphicTrailingCoeffAt f x h) n
      (fun _ ↦ (hf.meromorphicTrailingCoeffAt_ne_zero h).isUnit) := by
  let g := (hf.exists_analytic_factor h).choose
  have hg : AnalyticAt 𝕜 g x := (hf.exists_analytic_factor h).choose_spec.1
  have hgx : g x ≠ 0 := (hf.exists_analytic_factor h).choose_spec.2.1
  have hfg := (hf.exists_analytic_factor h).choose_spec.2.2
  obtain ⟨G, hG, hGg⟩ := analyticAt_exists_zpow hg hgx n
  have ho : (meromorphicOrderAt _ x hp).untop h' = n * (meromorphicOrderAt f x hf).untop h := by
    apply WithTop.coe_injective
    rw [WithTop.coe_untop, meromorphicOrderAt_zpow hf n hp.1, WithTop.coe_mul, WithTop.coe_untop]
  have hcoef : meromorphicTrailingCoeffAt _ x h' = G x := by
    apply hG.meromorphicTrailingCoeffAt_of_eq_nhdsNE hp h'
    rw [← comap_comap]
    have H := hfg.and (tendsto_comap.eventually
      ((hGg.and (hg.continuousAt.eventually_ne hgx)).filter_mono nhdsWithin_le_nhds))
    filter_upwards [tendsto_comap.eventually H] with y hy
    intro hne
    let u := (sub_ne_zero.mpr hne).isUnit
    have hu := hy.2.2.isUnit
    change Checked.zpow (f y.val) n y.2 = Checked.zpow (coord y.val - x)
      ((meromorphicOrderAt _ x hp).untop h') _ * G (coord y.val)
    rw [ho, hy.2.1 hu]
    have hfac := hy.1 hne
    exact zpow_of_eq_zpow_mul _ _ _ _ n u hu _ hfac
  exact hcoef.trans (hGg.self_of_nhds hgx.isUnit)

/-- The reciprocal on the pointwise unit locus has reciprocal leading coefficient. -/
lemma meromorphicTrailingCoeffAt_inv {D : Type*} {coord : D → 𝕜} {f : D → 𝕜}
    (hf : MeromorphicAt f x coord) (h : meromorphicOrderAt f x hf ≠ ⊤)
    {hi : MeromorphicAt (fun y : {y : D | IsUnit (f y)} ↦ Checked.inv (f y) y.2)
      x (coord ∘ Subtype.val)} {h' : meromorphicOrderAt _ x hi ≠ ⊤} :
    meromorphicTrailingCoeffAt _ x h' =
      Checked.inv (meromorphicTrailingCoeffAt f x h)
        (hf.meromorphicTrailingCoeffAt_ne_zero h).isUnit := by
  have hc : Set.range (fun y : {y : D | (-1 : ℤ) < 0 → IsUnit (f y)} ↦ coord y.val) ∈ 𝓝[≠] x :=
    Filter.mem_of_superset hi.1 fun _ ⟨y, hy⟩ ↦ ⟨⟨y.val, fun _ ↦ y.2⟩, hy⟩
  have hp := hf.zpow (-1) hc
  have he : ∀ᶠ t in 𝓝[≠] x, ∀ (a : {y : D | IsUnit (f y)})
      (b : {y : D | (-1 : ℤ) < 0 → IsUnit (f y)}), coord a.val = t → coord b.val = t →
      Checked.inv (f a.val) a.2 = Checked.zpow (f b.val) (-1) b.2 := by
    obtain ⟨n, g, hg, hfg⟩ := hf.2
    filter_upwards [eventually_comap.mp hfg, self_mem_nhdsWithin] with t ht htx
    intro a b hat hbt
    have hfg' : f a.val = f b.val := by
      apply (smul_right_inj (pow_ne_zero n (sub_ne_zero.mpr htx))).mp
      simpa only [← hat, show coord b.val = coord a.val from hbt.trans hat.symm] using
        (ht a.val hat).trans (by simpa only [hat, hbt] using (ht b.val hbt).symm)
    simp only [zpow_neg_one₀, hfg']
  have hpfin := (hi.order_eq_of_eventuallyEq hp he).symm.trans_ne h'
  rw [hi.trailingCoeff_eq_of_eventuallyEq hp (h₂ := hpfin) he,
    hf.meromorphicTrailingCoeffAt_zpow h, zpow_neg_one₀]

/-- The leading coefficient of a natural power is the natural power of the leading coefficient. -/
lemma MeromorphicAt.meromorphicTrailingCoeffAt_pow {n : ℕ} {f : 𝕜 → 𝕜}
    (hf : MeromorphicAt f x) (h : meromorphicOrderAt f x hf ≠ ⊤) {hp : MeromorphicAt (f ^ n) x}
    {h' : meromorphicOrderAt (f ^ n) x hp ≠ ⊤} :
    meromorphicTrailingCoeffAt (f ^ n) x h' = (meromorphicTrailingCoeffAt f x h) ^ n := by
  induction n with
  | zero =>
    have he : f ^ 0 =ᶠ[𝓝[≠] x] (1 : 𝕜 → 𝕜) := .of_eq (pow_zero f)
    have ht :=
      (analyticAt_const (v := (1 : 𝕜)) (x := x)).meromorphicOrderAt_ne_top_of_ne_zero one_ne_zero
    rw [meromorphicTrailingCoeffAt_congr_nhdsNE he (h₂ := ht), pow_zero]
    exact (analyticAt_const (v := (1 : 𝕜))).meromorphicTrailingCoeffAt_of_ne_zero one_ne_zero
  | succ n ih =>
    have hn : meromorphicOrderAt (f ^ n) x (hf.pow n) ≠ ⊤ := by
      rw [meromorphicOrderAt_pow hf]
      exact WithTop.mul_ne_top (WithTop.natCast_ne_top _) h
    have he : f ^ (n + 1) =ᶠ[𝓝[≠] x] f ^ n * f := .of_eq (pow_succ f n)
    have ht := (meromorphicOrderAt_congr hp he).symm.trans_ne h'
    rw [meromorphicTrailingCoeffAt_congr_nhdsNE he (h₂ := ht),
      (hf.pow n).meromorphicTrailingCoeffAt_mul hf hn h, ih, pow_succ]

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
      Checked.zpow
        (meromorphicTrailingCoeffAt (g · - g x) x (hg.meromorphicOrderAt_sub_ne_top hg_nc))
        (meromorphicOrderAt f (g x) hf).untop₀ (fun _ ↦
          ((hg.fun_sub analyticAt_const).meromorphicAt.meromorphicTrailingCoeffAt_ne_zero
            _).isUnit) •
        meromorphicTrailingCoeffAt f (g x) h₂f := by
  let r := (meromorphicOrderAt f (g x) hf).untop₀
  have hB : MeromorphicAt (fun z ↦ g z - g x) x := (hg.fun_sub analyticAt_const).meromorphicAt
  have hfin := hg.meromorphicOrderAt_sub_ne_top hg_nc
  let k := (meromorphicOrderAt (g · - g x) x hB).untop₀
  obtain ⟨F, hF, hFx, hfrep⟩ := (meromorphicOrderAt_ne_top_iff hf).mp h₂f
  obtain ⟨B, hB', hBx, hgrep⟩ := (meromorphicOrderAt_ne_top_iff hB).mp hfin
  obtain ⟨V, hV, hVg⟩ := analyticAt_exists_zpow hB' hBx r
  have hVx : V x ≠ 0 := (hVg.self_of_nhds hBx.isUnit).trans_ne (hBx.isUnit.zpow₀ r).ne_zero
  have hcoef : meromorphicTrailingCoeffAt (f ∘ g) x h = V x • F (g x) := by
    apply (hV.smul (hF.comp hg)).meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE
      (n := r * k) (smul_ne_zero hVx hFx)
    have hF' := hg.continuousAt.tendsto.eventually (eventually_comap.mp hfrep)
    filter_upwards [hgrep, tendsto_comap.eventually
      (hF'.and (hVg.and (hB'.continuousAt.eventually_ne hBx)))]
      with z hz hlocal
    have hu := (sub_ne_zero.mpr z.property).isUnit
    have hBz := hlocal.2.2.isUnit
    have hn : g z - g x ≠ 0 := by
      rw [hz]
      exact mul_ne_zero (hu.zpow₀ k).ne_zero hBz.ne_zero
    have hFz := hlocal.1 ⟨g z, sub_ne_zero.mp hn⟩ rfl
    change f (g z) = Checked.zpow _ _ _ • (V z • F (g z))
    rw [hFz, ← mul_smul, hlocal.2.1 hBz]
    exact congrArg (· • F (g z))
      (zpow_of_eq_zpow_mul (g z - g x) _ (B z) k r hu hBz _ hz)
  rw [hcoef]
  have hcB := hB'.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE hBx hgrep (h := hfin)
  have hcF := hF.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE hFx hfrep (h := h₂f)
  simpa only [hcB, hcF] using congrArg (· • F (g x)) (hVg.self_of_nhds hBx.isUnit)

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
