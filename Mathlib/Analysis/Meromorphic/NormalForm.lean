/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Meromorphic.Divisor
public import Mathlib.Analysis.Meromorphic.GermOrder
public import Mathlib.Analysis.Meromorphic.Section

/-!
# Normal form of meromorphic functions and continuous extension

If a function `f` is meromorphic on `U` and if `g` differs from `f` only along a set that is
codiscrete within `U`, then `g` is likewise meromorphic. The set of meromorphic functions is
therefore huge, and `=ᶠ[codiscreteWithin U]` defines an equivalence relation.

Normalization fills removable singularities with their unique analytic extension values.
A normalized representative is defined at the center exactly when the meromorphic germ
extends analytically there. A pole is absent from its scalar domain.

The relevant notions are `MeromorphicNFAt` and `MeromorphicNFOn`; these guarantee normal
form at a single point and along a set, respectively.
-/

@[expose] public section

open Metric Set WithTop

open scoped Topology Pointwise

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f : 𝕜 → E} {g : 𝕜 → 𝕜}
  {x : 𝕜}
  {U : Set 𝕜}

/-!
## Normal form of meromorphic functions at a given point

### Definition and characterizations
-/

/-- A normalized meromorphic representative contains the center in its domain exactly when
its punctured germ extends analytically there. Its value at that point is the extension value. -/
@[fun_prop]
structure MeromorphicNFAt {D : Type*} (f : D → E) (x : 𝕜) (coord : D → 𝕜 := by exact _root_.id) :
    Prop where
  meromorphicAt : MeromorphicAt f x coord
  mem_range_iff : x ∈ Set.range coord ↔ MeromorphicAt.IsRegular f x coord
  value_eq : ∀ y (hy : coord y = x),
    f y = meromorphicAt.value (mem_range_iff.mp ⟨y, hy⟩)

open Filter in
/-- A normalized scalar representative is analytic at each point of its actual domain. -/
theorem MeromorphicNFAt.analyticAt_of_mem {D : Type*} {coord : D → 𝕜} {f : D → E} {y : D}
    (hf : MeromorphicNFAt f (coord y) coord) : AnalyticAt 𝕜 f y coord := by
  have hr := hf.mem_range_iff.mp ⟨y, rfl⟩
  obtain ⟨a, ha, he⟩ := hr
  have hall : ∀ᶠ t in 𝓝 (coord y), ∀ w, coord w = t → f w = a (coord w) := by
    filter_upwards [eventually_nhdsWithin_iff.mp (eventually_comap.mp he)] with t ht
    intro w hw
    by_cases h : t = coord y
    · have hw' := hw.trans h
      rw [hf.value_eq w hw', hf.meromorphicAt.value_eq _ ha he, hw']
    · exact ht h w hw
  obtain ⟨ε, hε, hball⟩ := EMetric.mem_nhds_iff.mp hall
  obtain ⟨p, r, hp⟩ := ha
  refine ⟨p, min r ε, (min_le_left _ _).trans hp.r_le, lt_min hp.r_pos hε, ?_⟩
  intro w hw
  have hwr := Metric.eball_subset_eball (min_le_left _ _) hw
  have hwe := Metric.eball_subset_eball (min_le_right _ _) hw
  have hwt : coord w ∈ Metric.eball (coord y) ε := by
    simpa [Metric.mem_eball, edist_eq_enorm_sub] using hwe
  rw [hball hwt w rfl]
  exact hp.hasSum hwr

/-- At an admissible center, order zero is equivalent to a nonzero normalized value. -/
theorem MeromorphicNFAt.order_eq_zero_iff_value_ne_zero {D : Type*} {f : D → E} {coord : D → 𝕜}
    {x : 𝕜} (hf : MeromorphicNFAt f x coord) {y : D} (hy : coord y = x) :
    meromorphicOrderAt f x hf.meromorphicAt = 0 ↔ f y ≠ 0 := by
  obtain ⟨a, ha, he⟩ := hf.mem_range_iff.mp ⟨y, hy⟩
  have hv := (hf.value_eq y hy).trans (hf.meromorphicAt.value_eq _ ha he)
  rw [hf.meromorphicAt.order_eq_of_presentation (n := 0) ha (he.mono fun z hz ↦ by
    simpa only [pow_zero, one_smul, Function.comp_apply] using hz), Nat.cast_zero, sub_zero,
    ENat.map_natCast_eq_zero, ha.analyticOrderAt_eq_zero, hv]

/-- An ambient representative is already normalized if and only if it is analytic at the center. -/
theorem meromorphicNFAt_iff_analyticAt : MeromorphicNFAt f x ↔ AnalyticAt 𝕜 f x := by
  constructor
  · intro hf
    have hr := hf.mem_range_iff.mp ⟨x, rfl⟩
    obtain ⟨g, hg, he⟩ := hr
    have hp : f =ᶠ[𝓝[≠] x] g := by simpa only [Filter.comap_id, Function.comp_id] using he
    have h0 : f x = g x :=
      (hf.value_eq x rfl).trans (hf.meromorphicAt.value_eq _ hg he)
    exact hg.congr (eventuallyEq_nhds_of_eventuallyEq_nhdsNE hp h0).symm
  · intro hf
    have hr : MeromorphicAt.IsRegular f x := ⟨f, hf, .refl _ _⟩
    refine ⟨hf.meromorphicAt, ⟨fun _ ↦ hr, fun _ ↦ ⟨x, rfl⟩⟩, ?_⟩
    intro y hy
    exact (congrArg f hy).trans (hf.meromorphicAt.value_eq hr hf (.refl _ _)).symm

/-!
### Relation to other properties of functions
-/

attribute [fun_prop] MeromorphicNFAt.meromorphicAt

/--
If a function is meromorphic in normal form at `x`, then it has non-negative order iff it is
analytic.
-/
theorem MeromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt (hf : MeromorphicNFAt f x) :
    0 ≤ meromorphicOrderAt f x ↔ AnalyticAt 𝕜 f x := by
  exact ⟨fun _ ↦ meromorphicNFAt_iff_analyticAt.mp hf, fun h ↦ h.meromorphicOrderAt_nonneg⟩

/-- Analytic functions are meromorphic in normal form. -/
@[fun_prop] theorem AnalyticAt.meromorphicNFAt (hf : AnalyticAt 𝕜 f x) :
    MeromorphicNFAt f x :=
  meromorphicNFAt_iff_analyticAt.mpr hf

/--
Meromorphic functions have normal form outside of a discrete subset in the domain of meromorphicity.
-/
theorem MeromorphicOn.meromorphicNFAt_mem_codiscreteWithin {U : Set 𝕜}
    (hf : MeromorphicOn f U) :
    { x | MeromorphicNFAt f x } ∈ Filter.codiscreteWithin U := by
  filter_upwards [hf.analyticAt_mem_codiscreteWithin] with _ ha
  exact ha.meromorphicNFAt

/-!
### Vanishing and order
-/

/--
If `f` is meromorphic in normal form at `x`, then `f` has order zero iff it does not vanish at `x`.

See `AnalyticAt.order_eq_zero_iff` for an analogous statement about analytic functions.
-/
theorem MeromorphicNFAt.meromorphicOrderAt_eq_zero_iff (hf : MeromorphicNFAt f x) :
    meromorphicOrderAt f x = 0 ↔ f x ≠ 0 := by
  have ha := meromorphicNFAt_iff_analyticAt.mp hf
  rw [ha.meromorphicOrderAt_eq, ENat.map_natCast_eq_zero, ha.analyticOrderAt_eq_zero]

/-!
### Local nature of the definition and local identity theorem
-/

/--
**Local identity theorem**: two meromorphic functions in normal form agree in a neighborhood iff
they agree in a pointed neighborhood.

See `ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE` for the analogous statement for
continuous functions.
-/
theorem MeromorphicNFAt.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds {g : 𝕜 → E}
    (hf : MeromorphicNFAt f x) (hg : MeromorphicNFAt g x) :
    f =ᶠ[𝓝[≠] x] g ↔ f =ᶠ[𝓝 x] g := by
  exact ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    (meromorphicNFAt_iff_analyticAt.mp hf).continuousAt
    (meromorphicNFAt_iff_analyticAt.mp hg).continuousAt

/-- Meromorphicity in normal form is a local property. -/
theorem meromorphicNFAt_congr {g : 𝕜 → E} (hfg : f =ᶠ[𝓝 x] g) :
    MeromorphicNFAt f x ↔ MeromorphicNFAt g x := by
  rw [meromorphicNFAt_iff_analyticAt, meromorphicNFAt_iff_analyticAt]
  exact analyticAt_congr hfg

/-!
### Criteria to guarantee normal form
-/

/--
If `f` is meromorphic in normal form at `x` and `g` is analytic at `x`, then `g • f` is
meromorphic in normal form at `x`.
-/
lemma MeromorphicNFAt.smul_analytic (hf : MeromorphicNFAt f x)
    (hg : AnalyticAt 𝕜 g x) :
    MeromorphicNFAt (g • f) x := by
  apply meromorphicNFAt_iff_analyticAt.mpr
  exact hg.smul (meromorphicNFAt_iff_analyticAt.mp hf)

@[fun_prop] theorem MeromorphicNFAt.smul_const {s : 𝕜} (hf : MeromorphicNFAt f x) :
    MeromorphicNFAt (s • f) x := by
  exact (meromorphicNFAt_iff_analyticAt.mp hf).fun_const_smul.meromorphicNFAt

/--
If `f` is any function and `g` is analytic without zero at `z₀`, then `f` is meromorphic in normal
form at `z₀` iff `g • f` is meromorphic in normal form at `z₀`.
-/
theorem meromorphicNFAt_smul_iff_right_of_analyticAt (h₁g : AnalyticAt 𝕜 g x)
    (h₂g : g x ≠ 0) :
    MeromorphicNFAt (g • f) x ↔ MeromorphicNFAt f x := by
  rw [meromorphicNFAt_iff_analyticAt, meromorphicNFAt_iff_analyticAt]
  refine ⟨fun hp ↦ ?_, h₁g.smul⟩
  obtain ⟨v, hv, he⟩ := h₁g.exists_mul_eq_one h₂g.isUnit
  apply (hv.smul hp).congr
  filter_upwards [he] with y hy
  simp only [Pi.smul_apply', ← mul_smul, mul_comm (v y), hy, one_smul]

/--
If `f` is any function and `g` is analytic without zero at `z₀`, then `f` is meromorphic in normal
form at `z₀` iff `g * f` is meromorphic in normal form at `z₀`.
-/
theorem meromorphicNFAt_mul_iff_right {f : 𝕜 → 𝕜} (h₁g : AnalyticAt 𝕜 g x)
    (h₂g : g x ≠ 0) :
    MeromorphicNFAt (g * f) x ↔ MeromorphicNFAt f x :=
  meromorphicNFAt_smul_iff_right_of_analyticAt h₁g h₂g

/--
If `f` is any function and `g` is analytic without zero at `z₀`, then `f` is meromorphic in normal
form at `z₀` iff `f * g` is meromorphic in normal form at `z₀`.
-/
theorem meromorphicNFAt_mul_iff_left {f : 𝕜 → 𝕜} (h₁g : AnalyticAt 𝕜 g x)
    (h₂g : g x ≠ 0) :
    MeromorphicNFAt (f * g) x ↔ MeromorphicNFAt f x := by
  rw [mul_comm, ← smul_eq_mul]
  exact meromorphicNFAt_smul_iff_right_of_analyticAt h₁g h₂g

/--
A product of meromorphic functions in normal form is in normal form on their common ambient domain.
-/
theorem meromorphicNFAt_prod {x : 𝕜} {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → 𝕜}
    (h₁f : ∀ i ∈ s, MeromorphicNFAt (f i) x) :
    MeromorphicNFAt (∏ i ∈ s, f i) x := by
  exact (Finset.analyticAt_prod _ fun i hi ↦
    meromorphicNFAt_iff_analyticAt.mp (h₁f i hi)).meromorphicNFAt

/--
A product of meromorphic functions in normal form is in normal form on their common ambient domain.
-/
theorem meromorphicNFAt_fun_prod {x : 𝕜} {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → 𝕜}
    (h₁f : ∀ i ∈ s, MeromorphicNFAt (f i) x) :
    MeromorphicNFAt (fun a ↦ ∏ i ∈ s, f i a) x := by
  convert! meromorphicNFAt_prod h₁f
  exact (Finset.prod_apply _ s f).symm

/--
A finprod of meromorphic functions in normal form is in normal form on their common ambient domain.
-/
theorem meromorphicNFAt_finprod {x : 𝕜} {ι : Type*} {f : ι → 𝕜 → 𝕜}
    (h₁f : ∀ i, MeromorphicNFAt (f i) x) :
    MeromorphicNFAt (∏ᶠ i, f i) x := by
  by_cases h₃f : Function.HasFiniteMulSupport f
  · simp_rw [finprod_eq_prod f h₃f]
    exact meromorphicNFAt_prod (by aesop)
  · exact finprod_of_not_hasFiniteMulSupport h₃f ▸ analyticAt_const.meromorphicNFAt

/-- MeromorphicNFAt is invariant under scaling. -/
@[to_fun (attr := simp) meromorphicNFAt_fun_const_smul_iff_meromorphicNFAt]
theorem meromorphicNFAt_const_smul_iff_meromorphicNFAt {s : 𝕜} (hs : s ≠ 0) :
    MeromorphicNFAt (s • f) x ↔ MeromorphicNFAt f x := by
  constructor
  <;> intro hf
  · rw [((eq_inv_smul_iff₀ (ha := hs.isUnit)).mpr rfl : f = s⁻¹ • s • f)]
    fun_prop
  · fun_prop

/-- An analytic fraction in which numerator and denominator have no common zero at
the center is already normalized on the complement of the denominator's zero set. -/
theorem AnalyticAt.meromorphicNFAt_div {f g : 𝕜 → 𝕜} (hf : AnalyticAt 𝕜 f x)
    (hg : AnalyticAt 𝕜 g x) (hn : ¬ g =ᶠ[𝓝 x] 0) (hcop : g x = 0 → f x ≠ 0) :
    MeromorphicNFAt (fun y : {y : 𝕜 | g y ≠ 0} ↦ Checked.div (f y) (g y) y.property.isUnit)
      x Subtype.val := by
  let S := {y : 𝕜 | g y ≠ 0}
  let q := fun y : S ↦ Checked.div (f y) (g y) y.property.isUnit
  have hm : MeromorphicAt q x Subtype.val := hf.meromorphicAt_div hg hn
  have hspec {a : 𝕜 → 𝕜} (ha : AnalyticAt 𝕜 a x)
      (he : q =ᶠ[Filter.comap Subtype.val (𝓝[≠] x)] a ∘ Subtype.val) : a x * g x = f x := by
    have hp : a * g =ᶠ[𝓝[≠] x] f := by
      rw [← Filter.map_comap_of_mem hm.1]
      apply Filter.eventually_map.mpr
      exact he.mono fun y hy ↦ eq_div_iff.mp hy.symm
    exact Filter.EventuallyEq.eq_of_nhds
      ((ha.mul hg).frequently_eq_iff_eventually_eq hf |>.mp hp.frequently)
  have hreg : x ∈ Set.range (Subtype.val : S → 𝕜) ↔ MeromorphicAt.IsRegular q x Subtype.val := by
    rw [Subtype.range_coe]
    constructor
    · intro hx
      obtain ⟨v, hv, he⟩ := hg.exists_mul_eq_one hx.isUnit
      refine ⟨f * v, hf.mul hv, ?_⟩
      filter_upwards [Filter.tendsto_comap.eventually (he.filter_mono nhdsWithin_le_nhds)] with y hy
      apply div_eq_iff.mpr
      change f y = (f y * v y) * g y
      rw [mul_assoc, mul_comm (v y), hy, mul_one]
    · rintro ⟨a, ha, he⟩ hz
      have h := hspec ha he
      apply hcop hz
      simp [← h, hz]
  refine ⟨hm, hreg, ?_⟩
  intro y hy
  have hr := hreg.mp ⟨y, hy⟩
  have h := hspec hr.choose_spec.1 hr.choose_spec.2
  change Checked.div (f y) (g y) _ = hr.choose x
  apply div_eq_iff.mpr
  simpa only [hy] using h.symm

/-- The reciprocal of a normalized ambient analytic function with nonzero germ is normalized
on the complement of its zero set. -/
theorem MeromorphicNFAt.inv {f : 𝕜 → 𝕜} (hf : MeromorphicNFAt f x)
    (hn : ¬ f =ᶠ[𝓝 x] 0) :
    MeromorphicNFAt
      (fun y : {y : 𝕜 | f y ≠ 0} ↦ Checked.inv (f y) y.property.isUnit) x Subtype.val := by
  simpa only [Pi.one_apply, one_div₀] using
    (analyticAt_const (v := (1 : 𝕜))).meromorphicNFAt_div (meromorphicNFAt_iff_analyticAt.mp hf) hn
      (fun _ ↦ one_ne_zero)

/--
The composition of a meromorphic function in normal form and an analytic function is meromorphic in
normal form.
-/
@[fun_prop]
theorem MeromorphicNFAt.comp_analyticAt (hf : MeromorphicNFAt f (g x)) (hg : AnalyticAt 𝕜 g x) :
    MeromorphicNFAt (f ∘ g) x := by
  exact ((meromorphicNFAt_iff_analyticAt.mp hf).comp hg).meromorphicNFAt

/--
A function is meromorphic in normal form at a point iff it is meromorphic in normal form after
composition with an analytic function of nonvanishing derivative, such as translation.
-/
theorem meromorphicNFAt_comp_iff_of_deriv_ne_zero [CompleteSpace 𝕜] [CharZero 𝕜] {x : 𝕜}
    {g : 𝕜 → 𝕜} (hg : AnalyticAt 𝕜 g x) (hg' : deriv g x ≠ 0) :
    MeromorphicNFAt (f ∘ g) x ↔ MeromorphicNFAt f (g x) := by
  simpa only [meromorphicNFAt_iff_analyticAt] using
    (analyticAt_comp_iff_of_deriv_ne_zero (g := f) hg hg')

/-- `MeromorphicNFAt` is invariant under translation. -/
@[to_fun meromorphicNFAt_fun_comp_add_const_iff_meromorphicNFAt]
theorem meromorphicNFAt_comp_add_const_iff_meromorphicNFAt {c : 𝕜} {f : 𝕜 → E} :
    MeromorphicNFAt (f ∘ (· + c)) x ↔ MeromorphicNFAt f (x + c) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [show f = ((f ∘ fun x ↦ x + c) ∘ fun z ↦ z - c) by aesop]
    rw [show x = (x + c) - c by ring] at h
    exact h.comp_analyticAt (g := fun z ↦ z - c) (by fun_prop)
  · exact h.comp_analyticAt (g := fun z ↦ z + c) (by fun_prop)

/-- `MeromorphicNFAt` is invariant under translation. -/
@[to_fun meromorphicNFAt_fun_comp_sub_const_iff_meromorphicNFAt]
theorem meromorphicNFAt_comp_sub_const_iff_meromorphicNFAt {c : 𝕜} {f : 𝕜 → E} :
    MeromorphicNFAt (f ∘ (· - c)) x ↔ MeromorphicNFAt f (x - c) := by
  simp_rw [sub_eq_add_neg, meromorphicNFAt_comp_add_const_iff_meromorphicNFAt]

/-!
### Continuous extension and conversion to normal form
-/

/-- The domain of the normalized function at one center includes that center precisely
when the meromorphic germ is regular. -/
def meromorphicNFAtDomain (f : 𝕜 → E) (x : 𝕜) : Set 𝕜 := {y | y = x → MeromorphicAt.IsRegular f x}

/-- Fill a removable singularity by its regular value and exclude a pole from the scalar domain. -/
noncomputable def toMeromorphicNFAt (f : 𝕜 → E) (x : 𝕜)
    (hf : MeromorphicAt f x := by fun_prop_default)
    (y : meromorphicNFAtDomain f x) : E := by
  classical
  exact if he : (y : 𝕜) = x then hf.value (y.property he) else f y

/-- Away from the center the local normalization agrees pointwise with the given function. -/
theorem toMeromorphicNFAt_apply_of_ne (hf : MeromorphicAt f x)
    (y : meromorphicNFAtDomain f x) (hy : y.val ≠ x) : toMeromorphicNFAt f x hf y = f y := by
  simp [toMeromorphicNFAt, hy]

/-- The normalized value at a removable point is the unique regular value. -/
theorem toMeromorphicNFAt_apply_center (hf : MeromorphicAt f x) (hr : MeromorphicAt.IsRegular f x) :
    toMeromorphicNFAt f x hf ⟨x, fun _ ↦ hr⟩ = hf.value hr := by simp [toMeromorphicNFAt]

/-- A representative on a punctured neighborhood has the same analytic extensions as
an ambient function that agrees with it throughout that germ. -/
theorem MeromorphicAt.isRegular_iff_of_restrict {s : Set 𝕜} {g : s → E} (hs : s ∈ 𝓝[≠] x)
    (he : g =ᶠ[Filter.comap Subtype.val (𝓝[≠] x)] f ∘ Subtype.val) :
    MeromorphicAt.IsRegular g x Subtype.val ↔ MeromorphicAt.IsRegular f x := by
  have hm : Filter.map (Subtype.val : s → 𝕜) (Filter.comap Subtype.val (𝓝[≠] x)) = 𝓝[≠] x :=
    Filter.map_comap_of_mem (by simpa only [Subtype.range_coe] using hs)
  constructor
  · rintro ⟨a, ha, h⟩
    refine ⟨a, ha, ?_⟩
    simp only [Filter.comap_id, Function.comp_id]
    rw [← hm]
    exact he.symm.trans h
  · rintro ⟨a, ha, h⟩
    refine ⟨a, ha, he.trans ?_⟩
    simp only [Filter.comap_id, Function.comp_id] at h
    exact h.comp_tendsto Filter.tendsto_comap

/-- Normalizing a punctured representative amounts to filling the removable center by its
regular value and excluding it when it is a pole. -/
theorem MeromorphicAt.normalForm_of_restrict (hf : MeromorphicAt f x) {s : Set 𝕜} {g : s → E}
    (hs : s ∈ 𝓝[≠] x) (he : g =ᶠ[Filter.comap Subtype.val (𝓝[≠] x)] f ∘ Subtype.val)
    (hdom : x ∈ s ↔ MeromorphicAt.IsRegular f x)
    (hc : ∀ hx : x ∈ s, g ⟨x, hx⟩ = hf.value (hdom.mp hx)) : MeromorphicNFAt g x Subtype.val := by
  have hs' : Set.range (Subtype.val : s → 𝕜) ∈ 𝓝[≠] x := by simpa only [Subtype.range_coe] using hs
  have hg := (hf.comp_domain (Subtype.val : s → 𝕜) hs').congr_domain he.symm
  have hr := MeromorphicAt.isRegular_iff_of_restrict hs he
  refine ⟨hg, ?_, ?_⟩
  · rw [Subtype.range_coe]
    exact hdom.trans hr.symm
  intro y hy
  have hx : x ∈ s := hy ▸ y.property
  obtain ⟨a, ha, h⟩ := hdom.mp hx
  refine (congrArg g (Subtype.ext hy : y = ⟨x, hx⟩)).trans ((hc hx).trans ?_)
  refine (hf.value_eq _ ha h).trans ?_
  apply Eq.symm
  apply hg.value_eq _ ha
  simp only [Filter.comap_id, Function.comp_id] at h
  exact he.trans (h.comp_tendsto Filter.tendsto_comap)

/-- Equivalent scalar domains give the same normalization criterion. -/
theorem MeromorphicNFAt.congr_subtype {s t : Set 𝕜} {F : s → E} {G : t → E}
    (hf : MeromorphicNFAt F x Subtype.val) (he : s = t)
    (hfg : ∀ (z : 𝕜) (hz : z ∈ s), F ⟨z, hz⟩ = G ⟨z, he ▸ hz⟩) :
    MeromorphicNFAt G x Subtype.val := by
  subst t
  have : F = G := funext fun z ↦ hfg z z.property
  exact this ▸ hf

/-- An integer power is normalized on its true scalar domain. For a negative exponent
the input germ must be nonzero. -/
theorem MeromorphicNFAt.zpow {f : 𝕜 → 𝕜} (hf : MeromorphicNFAt f x) (n : ℤ)
    (hn : n < 0 → ¬ f =ᶠ[𝓝 x] 0) :
    MeromorphicNFAt (fun y : {y : 𝕜 | n < 0 → IsUnit (f y)} ↦ Checked.zpow (f y) n y.property)
      x Subtype.val := by
  have ha := meromorphicNFAt_iff_analyticAt.mp hf
  cases n with
  | ofNat k =>
    let S := {y : 𝕜 | Int.ofNat k < 0 → IsUnit (f y)}
    have hs (y : 𝕜) : y ∈ S := fun h ↦ (not_lt_of_ge (Int.natCast_nonneg k) h).elim
    have hpow := ha.pow k
    have hr : MeromorphicAt.IsRegular (f ^ k) x := ⟨f ^ k, hpow, .refl _ _⟩
    apply hpow.meromorphicAt.normalForm_of_restrict (Filter.Eventually.of_forall hs)
      (Filter.EventuallyEq.refl _ _) (Iff.intro (fun _ ↦ hr) (fun _ ↦ hs x))
    intro hx
    exact (hpow.meromorphicAt.value_eq _ hpow (.refl _ _)).symm
  | negSucc k =>
    have hpow := (ha.pow (k + 1)).meromorphicNFAt
    have hne : ¬ f ^ (k + 1) =ᶠ[𝓝 x] 0 := by
      intro he
      apply hn (Int.negSucc_lt_zero k)
      exact he.mono (fun y hy ↦ (pow_eq_zero_iff (Nat.succ_ne_zero k)).mp hy)
    apply (hpow.inv hne).congr_subtype
      (show {y : 𝕜 | (f ^ (k + 1)) y ≠ 0} = {y : 𝕜 | Int.negSucc k < 0 → IsUnit (f y)} by
        ext y
        simp [Int.negSucc_lt_zero, isUnit_iff_ne_zero])
    intro z hz
    exact (zpow_negSucc₀ (f z) k).symm

/-- The local normalization covers a punctured neighborhood. -/
theorem meromorphicNFAtDomain_mem_nhdsNE (f : 𝕜 → E) (x : 𝕜) :
    meromorphicNFAtDomain f x ∈ 𝓝[≠] x :=
  Filter.Eventually.mono self_mem_nhdsWithin (fun _ h h' ↦ (h h').elim)

/-- Normalization leaves the punctured germ unchanged. -/
theorem MeromorphicAt.eq_nhdsNE_toMeromorphicNFAt (hf : MeromorphicAt f x) :
    f ∘ Subtype.val =ᶠ[Filter.comap Subtype.val (𝓝[≠] x)] toMeromorphicNFAt f x hf :=
  (Filter.tendsto_comap.eventually (self_mem_nhdsWithin : ∀ᶠ y in 𝓝[≠] x, y ≠ x)).mono
    fun y hy ↦ (toMeromorphicNFAt_apply_of_ne hf y hy).symm

/-- Local normalization yields a normalized meromorphic representative. -/
theorem meromorphicNFAt_toMeromorphicNFAt {hf : MeromorphicAt f x} :
    MeromorphicNFAt (toMeromorphicNFAt f x hf) x Subtype.val := by
  apply hf.normalForm_of_restrict (meromorphicNFAtDomain_mem_nhdsNE f x)
    hf.eq_nhdsNE_toMeromorphicNFAt.symm (show x ∈ meromorphicNFAtDomain f x ↔ _ from
      ⟨fun h ↦ h rfl, fun h _ ↦ h⟩)
  exact fun hx ↦ toMeromorphicNFAt_apply_center hf (hx rfl)

/-- The normalized representative has the original order. -/
@[simp] theorem meromorphicOrderAt_toMeromorphicNFAt (hf : MeromorphicAt f x) :
    meromorphicOrderAt (toMeromorphicNFAt f x hf) x
        meromorphicNFAt_toMeromorphicNFAt.meromorphicAt =
      meromorphicOrderAt f x hf := by
  have hs : Set.range (Subtype.val : meromorphicNFAtDomain f x → 𝕜) ∈ 𝓝[≠] x := by
    simpa only [Subtype.range_coe] using meromorphicNFAtDomain_mem_nhdsNE f x
  exact ((hf.comp_domain Subtype.val hs).order_congr_domain
    hf.eq_nhdsNE_toMeromorphicNFAt).symm.trans (hf.order_comp_domain Subtype.val hs)

/-!
## Normal form of meromorphic functions on a given set

### Definition
-/

/-- A function is 'meromorphic in normal form' on `U` if has normal form at every point of `U`. -/
def MeromorphicNFOn {D : Type*} (f : D → E) (U : Set 𝕜) (coord : D → 𝕜 := by exact _root_.id) :=
  ∀ ⦃z⦄, z ∈ U → MeromorphicNFAt f z coord

namespace MeromorphicSection

open AnalyticGerm MeromorphicGerm TopologicalSpace Filter

/-- In a local analytic fraction chart, a nonvanishing denominator value gives a regular
point and the usual scalar quotient. -/
theorem regular_of_fraction_of_ne_zero {U : Opens ℂ} (s : MeromorphicSection U) (x : U)
    {a b : AnalyticGerm (x : ℂ)} (h : germ x s * ofAnalytic b = ofAnalytic a)
    (hb : AnalyticGerm.eval b ≠ 0) : x ∈ regularLocus s := by
  have hn : b ≠ 0 := fun h ↦ hb (by simp [h])
  have hq : germ x s =
      Checked.div (ofAnalytic a) (ofAnalytic b) (ofAnalytic_ne_zero.mpr hn).isUnit :=
    eq_div_iff.mpr h
  change germ x s ∈ regularSubring (x : ℂ)
  rw [hq]
  exact (div_mem_regularSubring_iff hn (fun h ↦ (hb h).elim)).mpr hb

/-- The scalar evaluation of a compatible meromorphic section is meromorphic at every
point of its open domain, including the poles missing from its scalar domain. -/
theorem meromorphicOn_eval {U : Opens ℂ} (s : MeromorphicSection U) :
    MeromorphicOn s.eval (U : Set ℂ) (fun y : s.regularLocus ↦ (y.val : ℂ)) := by
  intro x hxU
  let c := fun y : s.regularLocus ↦ (y.val : ℂ)
  obtain ⟨V, hV, hx, hVU, f, g, hf, hg, hgn, he⟩ := s.property (⟨x, hxU⟩ : U)
  have hnon : ¬ g =ᶠ[𝓝 x] 0 := fun h ↦ hgn ⟨x, hxU⟩ hx
    ((ofFun_eq_iff (hf := hg x hx) (hg := analyticAt_const (v := (0 : ℂ)))).mpr h)
  have hn := (hg x hx).eventually_eq_zero_or_eventually_ne_zero.resolve_left hnon
  have hV' : (V : Set ℂ) ∈ 𝓝[≠] x := nhdsWithin_le_nhds (hV.mem_nhds hx)
  have hreg (y : U) (hy : (y : ℂ) ∈ V) (hy' : g y ≠ 0) : y ∈ s.regularLocus :=
    regular_of_fraction_of_ne_zero s y (he y hy).symm hy'
  have hc : range c ∈ 𝓝[≠] x := by
    filter_upwards [hn, hV'] with y hy hv
    exact ⟨⟨⟨y, hVU hv⟩, hreg ⟨y, hVU hv⟩ hv hy⟩, rfl⟩
  obtain ⟨_, k, a, ha, heq⟩ := (hf x hx).meromorphicAt_div (hg x hx) hnon
  refine ⟨hc, k, a, ha, ?_⟩
  have hp := (eventually_comap.mp heq).and (hn.and hV')
  filter_upwards [(tendsto_comap : Tendsto c _ (𝓝[≠] x)).eventually hp] with y hy
  obtain ⟨hh, hgy, hyV⟩ := hy
  have hval : s.eval y = Checked.div (f (c y)) (g (c y)) hgy.isUnit :=
    eval_eq_div_of_mul_eq y.property (he y.val hyV).symm hgy
  rw [hval]
  exact hh ⟨c y, hgy⟩ rfl

/-- The order computed from the scalar representative agrees with the intrinsic order
in the fraction field of analytic germs, including at a pole or a removable point. -/
theorem order_eval {U : Opens ℂ} (s : MeromorphicSection U) (x : U) :
    meromorphicOrderAt s.eval (x : ℂ) (s.meromorphicOn_eval x x.property) =
      MeromorphicGerm.order (germ x s) := by
  obtain ⟨V, hV, hx, _, f, g, hf, hg, hgn, he⟩ := s.property x
  have hnon : ¬ g =ᶠ[𝓝 (x : ℂ)] 0 := fun h ↦ hgn x hx
    ((ofFun_eq_iff (hf := hg x hx) (hg := analyticAt_const (v := (0 : ℂ)))).mpr h)
  have hn := (hg x hx).eventually_eq_zero_or_eventually_ne_zero.resolve_left hnon
  have hc : range (fun y : {y : ℂ | IsUnit (g y)} ↦ _root_.id y.val) ∈ 𝓝[≠] (x : ℂ) := by
    filter_upwards [hn] with y hy
    exact ⟨⟨y, hy.isUnit⟩, rfl⟩
  have hm := (hf x hx).meromorphicAt.div (hg x hx).meromorphicAt hc
  have ho := (s.meromorphicOn_eval x x.property).order_eq_of_eventuallyEq hm (by
    filter_upwards [nhdsWithin_le_nhds (hV.mem_nhds hx)] with t ht
    intro a b ha hb
    have hV' : (a.val : ℂ) ∈ V := ha ▸ ht
    have hab : (a.val : ℂ) = (b.val : ℂ) := ha.trans hb.symm
    apply eq_div_iff.mpr
    change s.eval a * g b.val = f b.val
    rw [← hab]
    exact eval_mul_eq_of_mul_eq a.property (he a.val hV').symm)
  rw [meromorphicOrderAt_div (hf x hx).meromorphicAt (hg x hx).meromorphicAt hc,
    (hf x hx).meromorphicOrderAt_eq, (hg x hx).meromorphicOrderAt_eq] at ho
  have hfrac : germ x s = Checked.div (ofAnalytic (ofFun f (hf x hx)))
      (ofAnalytic (ofFun g (hg x hx))) (ofAnalytic_ne_zero.mpr (hgn x hx)).isUnit :=
    eq_div_iff.mpr (he x hx).symm
  rw [hfrac, order_div _ _ (hgn x hx), order_ofFun, order_ofFun]
  exact ho

/-- A section admits scalar evaluation at exactly the points where its scalar representative
has nonnegative order. -/
theorem mem_regularLocus_iff_order_nonneg {U : Opens ℂ} (s : MeromorphicSection U) (x : U) :
    x ∈ s.regularLocus ↔
      0 ≤ meromorphicOrderAt s.eval (x : ℂ) (s.meromorphicOn_eval x x.property) := by
  rw [order_eval]
  exact mem_regularSubring_iff_order_nonneg (germ x s)

/-- The scalar function of a section has normal form on its full regular locus. At a
removable point its value is the value of the unique analytic extension. -/
theorem meromorphicNFOn_eval {U : Opens ℂ} (s : MeromorphicSection U) :
    MeromorphicNFOn s.eval (U : Set ℂ) (fun y : s.regularLocus ↦ (y.val : ℂ)) := by
  intro z hz
  let x : U := ⟨z, hz⟩
  let c := fun y : s.regularLocus ↦ (y.val : ℂ)
  have hm := s.meromorphicOn_eval z hz
  have hloc : z ∈ range c ↔ x ∈ s.regularLocus := by
    constructor
    · rintro ⟨y, hy⟩
      exact (Subtype.ext hy : y.val = x) ▸ y.property
    · exact fun hr ↦ ⟨⟨x, hr⟩, rfl⟩
  have hr := hloc.trans
    ((s.mem_regularLocus_iff_order_nonneg x).trans hm.meromorphicOrderAt_nonneg_iff)
  refine ⟨hm, hr, ?_⟩
  rintro ⟨⟨t, ht⟩, hyr⟩ hy
  change t = z at hy
  subst t
  have reg := hr.mp ⟨⟨x, hyr⟩, rfl⟩
  obtain ⟨a, ha, hsa⟩ := reg
  obtain ⟨V, hV, hx, _, f, g, hf, hg, hgn, he⟩ := s.property x
  have hprod : a * g =ᶠ[𝓝[≠] z] f := by
    rw [← map_comap_of_mem hm.1]
    apply eventually_map.mpr
    filter_upwards [hsa, tendsto_comap.eventually (nhdsWithin_le_nhds (hV.mem_nhds hx))]
      with w hw hwV
    change a (c w) * g (c w) = f (c w)
    rw [← show s.eval w = a (c w) from hw]
    exact eval_mul_eq_of_mul_eq w.property (he w.val hwV).symm
  have hfg := ((ha.mul (hg z hx)).frequently_eq_iff_eventually_eq (hf z hx)).mp hprod.frequently
  have hax : ofAnalytic (ofFun a ha) = germ x s := by
    apply mul_right_cancel₀ (ofAnalytic_ne_zero.mpr (hgn x hx))
    apply Eq.trans _ (he x hx)
    rw [← map_mul, ← ofFun_mul a g ha (hg z hx)]
    exact congrArg ofAnalytic (ofFun_eq_iff.mpr hfg)
  rw [hm.value_eq _ ha hsa]
  change MeromorphicGerm.eval _ = a z
  have heval : (⟨germ x s, hyr⟩ : regularSubring z) = analyticEquivRegular z (ofFun a ha) :=
    Subtype.ext hax.symm
  exact (congrArg MeromorphicGerm.eval heval).trans (eval_ofAnalytic (ofFun a ha))

end MeromorphicSection

/-!
### Relation to other properties of functions
-/

/-- If a function is meromorphic in normal form on `U`, then it is meromorphic on `U`. -/
theorem MeromorphicNFOn.meromorphicOn {D : Type*} {coord : D → 𝕜} {f : D → E}
    (hf : MeromorphicNFOn f U coord) : MeromorphicOn f U coord := fun _ hz ↦ (hf hz).meromorphicAt

/--
If a function is meromorphic in normal form on `U`, then its divisor is non-negative iff it is
analytic.
-/
theorem MeromorphicNFOn.divisor_nonneg_iff_analyticOnNhd
    (h₁f : MeromorphicNFOn f U)
    {h : ∀ z (hz : z ∈ U), meromorphicOrderAt f z (h₁f.meromorphicOn z hz) ≠ ⊤} :
    0 ≤ MeromorphicOn.divisor f U h ↔ AnalyticOnNhd 𝕜 f U := by
  constructor <;> intro h' x
  · intro hx
    rw [← (h₁f hx).meromorphicOrderAt_nonneg_iff_analyticAt]
    have : (0 : WithTop ℤ) ≤ (MeromorphicOn.divisor f U h x : WithTop ℤ) := by exact_mod_cast h' x
    rwa [MeromorphicOn.coe_divisor_apply h₁f.meromorphicOn hx] at this
  · by_cases hx : x ∈ U
    · have := (h₁f hx).meromorphicOrderAt_nonneg_iff_analyticAt.2 (h' x hx)
      rw [← MeromorphicOn.coe_divisor_apply h₁f.meromorphicOn hx (h := h)] at this
      simp only [Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply]
      exact_mod_cast this
    · simp [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hx]

/--
If a function is meromorphic in normal form on `U`, then its pole divisor vanishes iff it is
analytic.
-/
theorem MeromorphicNFOn.poleDivisor_eq_zero_iff_analyticOnNhd (h₁f : MeromorphicNFOn f U) :
    MeromorphicOn.poleDivisor f U h₁f.meromorphicOn = 0 ↔ AnalyticOnNhd 𝕜 f U := by
  refine ⟨fun h x hx ↦ ?_, fun h ↦ MeromorphicOn.AnalyticOnNhd.poleDivisor_eq_zero h⟩
  rw [← (h₁f hx).meromorphicOrderAt_nonneg_iff_analyticAt]
  have h₂ : (MeromorphicOn.poleDivisor f U h₁f.meromorphicOn x : WithTop ℤ) = 0 := by simp [h]
  rwa [MeromorphicOn.coe_poleDivisor_apply h₁f.meromorphicOn hx, neg_eq_zero,
    min_eq_right_iff] at h₂

/-- Analytic functions are meromorphic in normal form. -/
theorem AnalyticOnNhd.meromorphicNFOn (h₁f : AnalyticOnNhd 𝕜 f U) :
    MeromorphicNFOn f U := fun z hz ↦ (h₁f z hz).meromorphicNFAt

/-!
### Divisors and zeros of meromorphic functions in normal form.
-/

/--
If `f` is meromorphic in normal form on `U` and nowhere locally constant zero, then its zero set
equals the support of the associated divisor.
-/
theorem MeromorphicNFOn.zero_set_eq_divisor_support (h₁f : MeromorphicNFOn f U)
    (h₂f : ∀ z (hz : z ∈ U), meromorphicOrderAt f z (h₁f.meromorphicOn z hz) ≠ ⊤) :
    U ∩ f ⁻¹' {0} = Function.support (MeromorphicOn.divisor f U h₂f) := by
  ext u
  by_cases hu : u ∈ U
  · have h₂ := MeromorphicOn.coe_divisor_apply h₁f.meromorphicOn hu (h := h₂f)
    have h₃ := (h₁f hu).meromorphicOrderAt_eq_zero_iff
    simp only [Set.mem_inter_iff, hu, Set.mem_preimage, Set.mem_singleton_iff, true_and,
      Function.mem_support, ne_eq]
    rw [← not_iff_not, not_not, ← ne_eq, ← h₃, ← h₂]
    exact_mod_cast Iff.rfl
  · simp [hu, Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu]

/-!
### Criteria to guarantee normal form
-/

/--
If `f` is any function and `g` is analytic without zero on `U`, then `f` is meromorphic in normal
form on `U` iff `g • f` is meromorphic in normal form on `U`.
-/
theorem meromorphicNFOn_smul_iff_right_of_analyticOnNhd {g : 𝕜 → 𝕜} (h₁g : AnalyticOnNhd 𝕜 g U)
    (h₂g : ∀ u ∈ U, g u ≠ 0) :
    MeromorphicNFOn (g • f) U ↔ MeromorphicNFOn f U := by
  constructor <;> intro h z hz
  · rw [← meromorphicNFAt_smul_iff_right_of_analyticAt (h₁g z hz) (h₂g z hz)]
    exact h hz
  · exact (h hz).smul_analytic (h₁g z hz)

/--
If `f` is any function and `g` is analytic without zero in `U`, then `f` is meromorphic in normal
form on `U` iff `g * f` is meromorphic in normal form on `U`.
-/
theorem meromorphicNFOn_mul_iff_right_of_analyticOnNhd {f g : 𝕜 → 𝕜} (h₁g : AnalyticOnNhd 𝕜 g U)
    (h₂g : ∀ u ∈ U, g u ≠ 0) :
    MeromorphicNFOn (g * f) U ↔ MeromorphicNFOn f U := by
  rw [← smul_eq_mul]
  exact meromorphicNFOn_smul_iff_right_of_analyticOnNhd h₁g h₂g

/--
If `f` is any function and `g` is analytic without zero in `U`, then `f` is meromorphic in normal
form on `U` iff `f * g` is meromorphic in normal form on `U`.
-/
theorem meromorphicNFOn_mul_iff_left_of_analyticOnNhd {f g : 𝕜 → 𝕜} (h₁g : AnalyticOnNhd 𝕜 g U)
    (h₂g : ∀ u ∈ U, g u ≠ 0) :
    MeromorphicNFOn (f * g) U ↔ MeromorphicNFOn f U := by
  rw [mul_comm, ← smul_eq_mul]
  exact meromorphicNFOn_mul_iff_right_of_analyticOnNhd h₁g h₂g

/--
A product of meromorphic functions in normal form is in normal form on their common ambient domain.
-/
theorem meromorphicNFOn_prod {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → 𝕜}
    (h₁f : ∀ i ∈ s, MeromorphicNFOn (f i) U) :
    MeromorphicNFOn (∏ i ∈ s, f i) U :=
  fun _ hx ↦ meromorphicNFAt_prod (h₁f · · hx)

/--
A product of meromorphic functions in normal form is in normal form on their common ambient domain.
-/
theorem meromorphicNFOn_fun_prod {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → 𝕜}
    (h₁f : ∀ i ∈ s, MeromorphicNFOn (f i) U) :
    MeromorphicNFOn (fun x ↦ ∏ i ∈ s, f i x) U := by
  convert! meromorphicNFOn_prod h₁f
  exact (Finset.prod_apply _ s f).symm

/--
A finprod of meromorphic functions in normal form is in normal form on their common ambient domain.
-/
theorem meromorphicNFOn_finprod {ι : Type*} {f : ι → 𝕜 → 𝕜} (h₁f : ∀ i, MeromorphicNFOn (f i) U) :
    MeromorphicNFOn (∏ᶠ i, f i) U :=
  fun _ hx ↦ meromorphicNFAt_finprod (h₁f · hx)

/-- MeromorphicNFOn is invariant under scaling. -/
@[to_fun (attr := simp) meromorphicNFOn_fun_const_smul_iff_meromorphicNFOn]
theorem meromorphicNFOn_const_smul_iff_meromorphicNFOn {s : 𝕜} (hs : s ≠ 0) :
    MeromorphicNFOn (s • f) U ↔ MeromorphicNFOn f U :=
  ⟨fun hf _ hx ↦ (meromorphicNFAt_const_smul_iff_meromorphicNFAt hs).mp (hf hx),
    fun hf _ hx ↦ (meromorphicNFAt_const_smul_iff_meromorphicNFAt hs).mpr (hf hx)⟩

/-- Integer powers preserve setwise normal form on their exponent-dependent domain. -/
theorem MeromorphicNFOn.zpow {f : 𝕜 → 𝕜} (hf : MeromorphicNFOn f U) (n : ℤ)
    (hn : n < 0 → ∀ x ∈ U, ¬ f =ᶠ[𝓝 x] 0) :
    MeromorphicNFOn (fun y : {y : 𝕜 | n < 0 → IsUnit (f y)} ↦ Checked.zpow (f y) n y.property)
      U Subtype.val :=
  fun x hx ↦ (hf hx).zpow n fun h ↦ hn h x hx

/-- Reciprocals are normalized on the nonzero locus, provided the input germ is nonzero
at every point of the set. -/
theorem MeromorphicNFOn.inv {f : 𝕜 → 𝕜} (hf : MeromorphicNFOn f U)
    (hn : ∀ x ∈ U, ¬ f =ᶠ[𝓝 x] 0) :
    MeromorphicNFOn
      (fun y : {y : 𝕜 | f y ≠ 0} ↦ Checked.inv (f y) y.property.isUnit) U Subtype.val :=
  fun x hx ↦ (hf hx).inv (hn x hx)

/-- `MeromorphicNFOn` is invariant under translation. -/
@[to_fun meromorphicNFOn_fun_comp_add_const_iff_meromorphicNFOn]
theorem meromorphicNFOn_comp_add_const_iff_meromorphicNFOn {c : 𝕜} {U : Set 𝕜} :
    MeromorphicNFOn (f ∘ (· + c)) U ↔ MeromorphicNFOn f (U + {c}) := by
  refine ⟨fun h y hy ↦ ?_, fun h y hy ↦ ?_⟩
  · rw [add_singleton, mem_image] at hy
    obtain ⟨x, h₁x, h₂x⟩ := hy
    simpa [← h₂x, ← meromorphicNFAt_comp_add_const_iff_meromorphicNFAt] using h h₁x
  · rw [meromorphicNFAt_comp_add_const_iff_meromorphicNFAt]
    aesop

/-- `MeromorphicNFOn` is invariant under translation. -/
@[to_fun meromorphicNFOn_fun_comp_sub_const_iff_meromorphicNFOn]
theorem meromorphicNFOn_comp_sub_const_iff_meromorphicNFOn {c : 𝕜} {U : Set 𝕜} :
    MeromorphicNFOn (f ∘ (· - c)) U ↔ MeromorphicNFOn f (U - {c}) := by
  simp_rw [sub_eq_add_neg, meromorphicNFOn_comp_add_const_iff_meromorphicNFOn, neg_singleton]

/-- `MeromorphicNFOn` is invariant under translation, special case where the set is a ball. -/
@[to_fun (attr := simp) meromorphicNFOn_ball_fun_comp_sub_const_iff_meromorphicNFOn_ball]
theorem meromorphicNFOn_ball_comp_sub_const_iff_meromorphicNFOn_ball {c : 𝕜} {R : ℝ} :
    MeromorphicNFOn (f ∘ (· - c)) (ball c R) ↔ MeromorphicNFOn f (ball (0 : 𝕜) R) := by
  rw [meromorphicNFOn_comp_sub_const_iff_meromorphicNFOn, ball_sub_singleton, sub_self]

/--
`MeromorphicNFOn` is invariant under translation, special case where the set is a closed ball.
-/
@[to_fun (attr := simp)
  meromorphicNFOn_closedBall_fun_comp_sub_const_iff_meromorphicNFOn_closedBall]
theorem meromorphicNFOn_closedBall_comp_sub_const_iff_meromorphicNFOn_closedBall {c : 𝕜} {R : ℝ} :
    MeromorphicNFOn (f ∘ (· - c)) (closedBall c R) ↔ MeromorphicNFOn f (closedBall (0 : 𝕜) R) := by
  rw [meromorphicNFOn_comp_sub_const_iff_meromorphicNFOn, closedBall_sub_singleton, sub_self]

/-- `MeromorphicNFOn` is invariant under translation, special case where the set is a sphere. -/
@[to_fun (attr := simp) meromorphicNFOn_sphere_fun_comp_sub_const_iff_meromorphicNFOn_sphere]
theorem meromorphicNFOn_sphere_comp_sub_const_iff_meromorphicNFOn_sphere {c : 𝕜} {R : ℝ} :
    MeromorphicNFOn (f ∘ (· - c)) (sphere c R) ↔ MeromorphicNFOn f (sphere (0 : 𝕜) R) := by
  rw [meromorphicNFOn_comp_sub_const_iff_meromorphicNFOn, sphere_sub_singleton, sub_self]

/-!
### Continuous extension and conversion to normal form
-/

/-- The scalar domain of normalization on a set. Outside the set the original values
are retained. Within the set poles are excluded and removable points are filled in. -/
def meromorphicNFOnDomain (f : 𝕜 → E) (U : Set 𝕜) : Set 𝕜 :=
  {x | x ∈ U → MeromorphicAt.IsRegular f x}

/-- The normalized scalar representative on its regular locus in `U`. -/
noncomputable def toMeromorphicNFOn (f : 𝕜 → E) (U : Set 𝕜)
    (hf : MeromorphicOn f U := by fun_prop_default) (x : meromorphicNFOnDomain f U) : E := by
  classical
  exact if hx : (x : 𝕜) ∈ U then (hf x hx).value (x.property hx) else f x

/-- Normalization preserves values outside the set. -/
@[simp] theorem toMeromorphicNFOn_apply_of_notMem (hf : MeromorphicOn f U)
    (y : meromorphicNFOnDomain f U) (hy : (y : 𝕜) ∉ U) : toMeromorphicNFOn f U hf y = f y := by
  simp [toMeromorphicNFOn, hy]

/-- At a regular point in `U`, normalization recovers the extension value. -/
theorem toMeromorphicNFOn_apply_of_mem (hf : MeromorphicOn f U) (y : meromorphicNFOnDomain f U)
    (hy : (y : 𝕜) ∈ U) : toMeromorphicNFOn f U hf y = (hf y hy).value (y.property hy) := by
  simp [toMeromorphicNFOn, hy]

/-- The scalar domain of the normalization covers a punctured neighborhood of each point of `U`. -/
theorem MeromorphicOn.normalFormDomain_mem (hf : MeromorphicOn f U) (hx : x ∈ U) :
    meromorphicNFOnDomain f U ∈ 𝓝[≠] x :=
  (hf.eventually_analyticAt_or_mem_compl hx).mono fun _ hy hU ↦
    ⟨f, hy.resolve_right (fun h ↦ h hU), .refl _ _⟩

/-- The normalized representative agrees puncturally with the original function. -/
theorem MeromorphicOn.toMeromorphicNFOn_eq_self_on_nhdsNE (hf : MeromorphicOn f U) (hx : x ∈ U) :
    toMeromorphicNFOn f U hf =ᶠ[Filter.comap Subtype.val (𝓝[≠] x)] f ∘ Subtype.val := by
  filter_upwards [Filter.tendsto_comap.eventually (hf.eventually_analyticAt_or_mem_compl hx)]
    with y hy
  by_cases h : (y : 𝕜) ∈ U
  · exact (toMeromorphicNFOn_apply_of_mem hf y h).trans
      ((hf y h).value_eq _ (hy.resolve_right (fun h' ↦ h' h)) (.refl _ _))
  · exact toMeromorphicNFOn_apply_of_notMem hf y h

/-- Off a discrete subset, the normalized domain contains the point and the original value
agrees with the normalized one. -/
theorem toMeromorphicNFOn_eqOn_codiscrete (hf : MeromorphicOn f U) :
    ∀ᶠ y in Filter.codiscreteWithin U, ∃ hy : y ∈ meromorphicNFOnDomain f U,
      f y = toMeromorphicNFOn f U hf ⟨y, hy⟩ := by
  filter_upwards [hf.analyticAt_mem_codiscreteWithin] with y hy
  have hr : MeromorphicAt.IsRegular f y := ⟨f, hy, .refl _ _⟩
  refine ⟨fun _ ↦ hr, ?_⟩
  by_cases h : y ∈ U
  · exact ((toMeromorphicNFOn_apply_of_mem hf _ h).trans
      ((hf y h).value_eq _ hy (.refl _ _))).symm
  · exact (toMeromorphicNFOn_apply_of_notMem hf ⟨y, fun _ ↦ hr⟩ h).symm

/-- Local and setwise normalization give the same scalar value at a regular center. -/
theorem toMeromorphicNFOn_eq_toMeromorphicNFAt (hf : MeromorphicOn f U) (hx : x ∈ U)
    (hr : MeromorphicAt.IsRegular f x) :
    toMeromorphicNFOn f U hf ⟨x, fun _ ↦ hr⟩ =
      toMeromorphicNFAt f x (hf x hx) ⟨x, fun _ ↦ hr⟩ :=
  (toMeromorphicNFOn_apply_of_mem hf _ hx).trans
    (toMeromorphicNFAt_apply_center (hf x hx) hr).symm

/-- The setwise normalization is in normal form everywhere on `U`. -/
theorem meromorphicNFOn_toMeromorphicNFOn (f : 𝕜 → E) (U : Set 𝕜) {hf : MeromorphicOn f U} :
    MeromorphicNFOn (toMeromorphicNFOn f U hf) U Subtype.val := by
  intro x hx
  apply (hf x hx).normalForm_of_restrict (hf.normalFormDomain_mem hx)
    (hf.toMeromorphicNFOn_eq_self_on_nhdsNE hx) (show x ∈ meromorphicNFOnDomain f U ↔ _ from
      ⟨fun h ↦ h hx, fun h _ ↦ h⟩)
  exact fun h ↦ toMeromorphicNFOn_apply_of_mem hf ⟨x, h⟩ hx

/-- Setwise normalization preserves the order at every point of the set. -/
@[simp] theorem meromorphicOrderAt_toMeromorphicNFOn (hf : MeromorphicOn f U) (hx : x ∈ U) :
    meromorphicOrderAt (toMeromorphicNFOn f U hf) x
        ((meromorphicNFOn_toMeromorphicNFOn f U hx).meromorphicAt) =
      meromorphicOrderAt f x (hf x hx) := by
  have hs : Set.range (Subtype.val : meromorphicNFOnDomain f U → 𝕜) ∈ 𝓝[≠] x := by
    simpa only [Subtype.range_coe] using hf.normalFormDomain_mem hx
  exact (((hf x hx).comp_domain Subtype.val hs).order_congr_domain
    (hf.toMeromorphicNFOn_eq_self_on_nhdsNE hx).symm).symm.trans
      ((hf x hx).order_comp_domain Subtype.val hs)

/-- Conversion of normal form does not affect divisors. -/
theorem MeromorphicOn.divisor_of_toMeromorphicNFOn (hf : MeromorphicOn f U)
    (h : ∀ z (hz : z ∈ U), meromorphicOrderAt f z (hf z hz) ≠ ⊤)
    {h' : ∀ z (hz : z ∈ U), meromorphicOrderAt (toMeromorphicNFOn f U hf) z
      ((meromorphicNFOn_toMeromorphicNFOn f U).meromorphicOn z hz) ≠ ⊤} :
    divisor (toMeromorphicNFOn f U hf) U h' = divisor f U h :=
  divisor_congr fun _ hz ↦ meromorphicOrderAt_toMeromorphicNFOn hf hz

/-- Conversion of normal form does not affect pole divisors. -/
@[simp] theorem MeromorphicOn.poleDivisor_of_toMeromorphicNFOn (hf : MeromorphicOn f U) :
    poleDivisor (toMeromorphicNFOn f U hf) U (meromorphicNFOn_toMeromorphicNFOn f U).meromorphicOn =
      poleDivisor f U hf :=
  poleDivisor_congr fun _ hz ↦ meromorphicOrderAt_toMeromorphicNFOn hf hz

open Filter in
/-- A partial meromorphic presentation has a normalized representative on precisely its regular
points of the set, retaining the original domain and values outside the set. -/
theorem MeromorphicOn.exists_normalForm_on_domain {S : Set 𝕜} {f : S → E}
    (hf : MeromorphicOn f U Subtype.val) :
    ∃ (T : Set 𝕜) (G : T → E), MeromorphicNFOn G U Subtype.val ∧
      (∀ x ∈ U, x ∈ T ↔ MeromorphicAt.IsRegular f x Subtype.val) ∧
      (∀ x ∉ U, x ∈ T ↔ x ∈ S) ∧
      (∀ x ∉ U, ∀ (ht : x ∈ T) (hs : x ∈ S), G ⟨x, ht⟩ = f ⟨x, hs⟩) ∧
      ∀ x ∈ U, ∀ᶠ y in 𝓝[≠] x, ∀ (ht : y ∈ T) (hs : y ∈ S), G ⟨y, ht⟩ = f ⟨y, hs⟩ := by
  classical
  let T := {x : 𝕜 | if x ∈ U then MeromorphicAt.IsRegular f x Subtype.val else x ∈ S}
  have hTin (x) (hx : x ∈ U) : x ∈ T ↔ MeromorphicAt.IsRegular f x Subtype.val := by simp [T, hx]
  have hTout (x) (hx : x ∉ U) : x ∈ T ↔ x ∈ S := by simp [T, hx]
  let G (x : T) : E := if hx : x.val ∈ U then
    (hf x hx).value ((hTin x hx).mp x.property)
    else f ⟨x, (hTout x hx).mp x.property⟩
  let F : 𝕜 → E := Function.extend Subtype.val f 0
  have hFval (y : S) : F y = f y := Subtype.val_injective.extend_apply _ _ y
  have hF : MeromorphicOn F U := by
    intro x hx
    obtain ⟨hc, n, a, ha, he⟩ := hf x hx
    refine ⟨by simp, n, a, ha, ?_⟩
    rw [comap_id]
    filter_upwards [hc, eventually_comap.mp he] with y ⟨w, hw⟩ he'
    subst y
    rw [hFval w]
    exact he' w rfl
  have hreg (x) (hx : x ∈ U) :
      MeromorphicAt.IsRegular f x Subtype.val ↔ MeromorphicAt.IsRegular F x :=
    MeromorphicAt.isRegular_iff_of_restrict (by simpa only [Subtype.range_coe] using (hf x hx).1)
      (.of_forall fun y ↦ (hFval y).symm)
  have hvalue (x) (hx : x ∈ U) (hr : MeromorphicAt.IsRegular f x Subtype.val) :
      (hf x hx).value hr = (hF x hx).value ((hreg x hx).mp hr) := by
    obtain ⟨a, ha, he⟩ := (hreg x hx).mp hr
    apply Eq.trans _ ((hF x hx).value_eq _ ha he).symm
    apply (hf x hx).value_eq _ ha
    have he' : F =ᶠ[𝓝[≠] x] a := by simpa only [comap_id, Function.comp_id] using he
    exact (show f =ᶠ[comap Subtype.val (𝓝[≠] x)] F ∘ Subtype.val from
      .of_forall fun y ↦ (hFval y).symm).trans (he'.comp_tendsto tendsto_comap)
  have hT (x : 𝕜) (hx : x ∈ U) : T ∈ 𝓝[≠] x := by
    filter_upwards [(hf x hx).1, hF.eventually_analyticAt_or_mem_compl hx] with y ⟨w, hw⟩ hy
    by_cases hyU : y ∈ U
    · exact (hTin y hyU).mpr ((hreg y hyU).mpr ⟨F, hy.resolve_right (fun h ↦ h hyU), .refl _ _⟩)
    · exact (hTout y hyU).mpr (hw ▸ w.property)
  have heq (x : 𝕜) (hx : x ∈ U) : G =ᶠ[comap Subtype.val (𝓝[≠] x)] F ∘ Subtype.val := by
    filter_upwards [tendsto_comap.eventually (hF.eventually_analyticAt_or_mem_compl hx)] with y hy
    by_cases hyU : y.val ∈ U
    · have ha := hy.resolve_right (fun h ↦ h hyU)
      exact (dite_eq_left hyU).trans ((hvalue y hyU _).trans ((hF y hyU).value_eq _ ha (.refl _ _)))
    · exact (dite_eq_right hyU).trans (hFval _).symm
  refine ⟨T, G, ?_, hTin, hTout, fun x hx ht _ ↦ dite_eq_right hx, ?_⟩
  · intro x hx
    apply (hF x hx).normalForm_of_restrict (hT x hx) (heq x hx) ((hTin x hx).trans (hreg x hx))
    intro ht
    exact (dite_eq_left hx).trans (hvalue _ hx _)
  · intro x hx
    filter_upwards [eventually_comap.mp (heq x hx)] with y hy
    exact fun ht hs ↦ (hy ⟨y, ht⟩ rfl).trans (hFval ⟨y, hs⟩)

open Filter WithTop.LinearOrderedAddCommGroup in
/-- A partial scalar factor acting on an ambient meromorphic function adds its order. -/
theorem MeromorphicAt.order_smul_comp_domain {D : Type*} {c : D → 𝕜} {s : D → 𝕜}
    (hs : MeromorphicAt s x c) (hf : MeromorphicAt f x) :
    meromorphicOrderAt (s • (f ∘ c)) x
        (hs.smul (hf.comp_domain (coord := _root_.id) c
          (by simpa only [Function.id_comp] using hs.1))) =
      meromorphicOrderAt s x hs + meromorphicOrderAt f x hf := by
  obtain ⟨m, a, ha, hsa⟩ := hs.2
  obtain ⟨n, b, hb, hfb⟩ := hf.2
  have hfb' : ∀ᶠ t in 𝓝[≠] x, (t - x) ^ n • f t = b t := by simpa only [comap_id, id_eq] using hfb
  have he : ∀ᶠ y in comap c (𝓝[≠] x), (c y - x) ^ (m + n) • (s • (f ∘ c)) y =
      (a • b) (c y) := by
    filter_upwards [hsa, tendsto_comap.eventually hfb'] with y hy hy'
    change (c y - x) ^ (m + n) • (s y • f (c y)) = a (c y) • b (c y)
    rw [← hy, ← hy', smul_eq_mul, pow_add, ← mul_smul, ← mul_smul]
    congr 1
    ring
  rw [MeromorphicAt.order_eq_of_presentation _ (ha.smul hb) he,
    hs.order_eq_of_presentation ha hsa, hf.order_eq_of_presentation hb hfb,
    analyticOrderAt_smul ha hb]
  cases analyticOrderAt a x ha with
  | top => cases analyticOrderAt b x hb <;> simp
  | coe i =>
    cases analyticOrderAt b x hb with
    | top => simp
    | coe j =>
      simp only [← Nat.cast_add, ENat.map_natCast]
      exact congrArg ((↑) : ℤ → WithTop ℤ)
        (show ((i + j : ℕ) : ℤ) - (m + n : ℕ) = i - (m : ℤ) + (j - (n : ℤ)) by omega)
