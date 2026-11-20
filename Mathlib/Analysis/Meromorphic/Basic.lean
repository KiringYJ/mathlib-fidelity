/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler, Stefan Kebekus
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.LogDeriv.Basic
public import Mathlib.Analysis.Meromorphic.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Meromorphic functions

Main statements:

* `MeromorphicAt`: definition of meromorphy at a point
* `MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt`: `f` is meromorphic at `z₀` iff we have
  `f z = (z - z₀) ^ n • g z` on a punctured neighborhood of `z₀`, for some `n : ℤ`
  and `g` analytic at `z₀`.
-/

@[expose] public section

open Filter Metric Set

open scoped Pointwise Topology

variable {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedAlgebra 𝕜 𝕜'] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {R : Type*} [NormedRing R] [Module R E] [IsBoundedSMul R E]

@[fun_prop]
lemma AnalyticAt.meromorphicAt {f : 𝕜 → E} {x : 𝕜} (hf : AnalyticAt 𝕜 f x) :
    MeromorphicAt f x :=
  MeromorphicAt.iff_exists_analyticAt_pow_smul.mpr ⟨0, by simpa only [pow_zero, one_smul]⟩

/-- Analogue of the principle of isolated zeros for an analytic function: if a function is
meromorphic at `z₀`, then either it is identically zero in a punctured neighborhood of `z₀`, or it
does not vanish there at all. -/
theorem MeromorphicAt.eventually_eq_zero_or_eventually_ne_zero {f : 𝕜 → E} {z₀ : 𝕜}
    (hf : MeromorphicAt f z₀) :
    (∀ᶠ z in 𝓝[≠] z₀, f z = 0) ∨ (∀ᶠ z in 𝓝[≠] z₀, f z ≠ 0) := by
  obtain ⟨n, h⟩ := MeromorphicAt.iff_exists_analyticAt_pow_smul.mp hf
  rcases h.eventually_eq_zero_or_eventually_ne_zero with h₁ | h₂
  · left
    filter_upwards [nhdsWithin_le_nhds h₁, self_mem_nhdsWithin] with y h₁y h₂y
    rw [Set.mem_compl_iff, Set.mem_singleton_iff, ← sub_eq_zero] at h₂y
    exact smul_eq_zero_iff_right (pow_ne_zero n h₂y) |>.mp h₁y
  · right
    filter_upwards [h₂, self_mem_nhdsWithin] with y h₁y h₂y
    exact (smul_ne_zero_iff.1 h₁y).2

namespace MeromorphicAt

variable {ι : Type*} {s : Finset ι} {F : ι → 𝕜 → 𝕜'} {G : ι → 𝕜 → E}

@[fun_prop]
lemma id (x : 𝕜) : MeromorphicAt id x := analyticAt_id.meromorphicAt

@[fun_prop, simp]
lemma const (e : E) (x : 𝕜) : MeromorphicAt (fun _ ↦ e) x :=
  analyticAt_const.meromorphicAt

variable {x : 𝕜}

@[to_fun (attr := fun_prop)]
lemma const_smul [SMulCommClass 𝕜 R E] {x : 𝕜} {f : 𝕜 → E} (hf : MeromorphicAt f x) (c : R) :
    MeromorphicAt (c • f) x := by
  obtain ⟨m, hf⟩ := iff_exists_analyticAt_pow_smul.mp hf
  exact iff_exists_analyticAt_pow_smul.mpr ⟨m, by simpa [smul_comm _ c _] using! hf.fun_const_smul⟩

/-- Finite products of meromorphic functions are meromorphic. -/
@[fun_prop] -- TODO: to_fun generates an unreadable statement, see #32866
theorem prod (hf : ∀ σ ∈ s, MeromorphicAt (F σ) x) :
    MeromorphicAt (∏ i ∈ s, F i) x := by
  classical
  induction s using Finset.induction with
  | empty =>
    rw [Finset.prod_empty]
    apply MeromorphicAt.const
  | insert a s ha hs =>
    rw [Finset.prod_insert ha]
    apply (hf a (Finset.mem_insert_self a s)).mul
      (hs (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)))

/-- Finite products of meromorphic functions are meromorphic. -/
@[fun_prop]
theorem fun_prod (h : ∀ σ ∈ s, MeromorphicAt (F σ) x) :
    MeromorphicAt (fun z ↦ ∏ n ∈ s, F n z) x := by
  convert! prod h (s := s)
  simp

/-- Finprods of meromorphic functions are meromorphic. -/
@[fun_prop]
theorem finprod {x : 𝕜} (hf : ∀ i, MeromorphicAt (F i) x) :
    MeromorphicAt (∏ᶠ i, F i) x := by
  by_cases h₂f : Function.HasFiniteMulSupport F
  · simpa [finprod_eq_prod F h₂f] using prod (by aesop)
  · exact finprod_of_not_hasFiniteMulSupport h₂f ▸ const (1 : 𝕜') x

/-- Finite sums of meromorphic functions are meromorphic. -/
@[fun_prop] -- TODO: to_fun generates an unreadable statement, see #32866
theorem sum (h : ∀ σ ∈ s, MeromorphicAt (G σ) x) :
    MeromorphicAt (∑ n ∈ s, G n) x := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    exact analyticAt_const.meromorphicAt
  | insert σ s hσ hind =>
    rw [Finset.sum_insert hσ]
    apply (h σ (Finset.mem_insert_self σ s)).add
      (hind (fun τ hτ ↦ h τ (Finset.mem_insert_of_mem hτ)))

/-- Finite sums of meromorphic functions are meromorphic. -/
@[fun_prop]
theorem fun_sum (h : ∀ σ ∈ s, MeromorphicAt (G σ) x) :
    MeromorphicAt (fun z ↦ ∑ n ∈ s, G n z) x := by
  convert! sum h (s := s)
  simp

/-- Finsums of meromorphic functions are meromorphic. -/
@[fun_prop]
theorem finsum (hF : ∀ i, MeromorphicAt (F i) x) :
    MeromorphicAt (∑ᶠ i, F i) x := by
  by_cases h₂f : Function.HasFiniteSupport F
  · simpa [finsum_eq_sum F h₂f] using sum (by aesop)
  · exact finsum_of_not_hasFiniteSupport h₂f ▸ const (0 : 𝕜') x

@[to_fun (attr := fun_prop)]
lemma neg {f : 𝕜 → E} (hf : MeromorphicAt f x) : MeromorphicAt (-f) x := by
  convert (MeromorphicAt.const (-1 : 𝕜) x).smul hf
  ext1 z
  simp only [Pi.neg_apply, Pi.smul_apply', neg_smul, one_smul]

@[simp]
lemma neg_iff {f : 𝕜 → E} :
    MeromorphicAt (-f) x ↔ MeromorphicAt f x :=
  ⟨fun h ↦ by simpa only [neg_neg] using h.neg, MeromorphicAt.neg⟩

@[to_fun (attr := fun_prop)]
lemma sub {f g : 𝕜 → E} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    MeromorphicAt (f - g) x := by
  convert hf.add hg.neg
  ext1 z
  simp_rw [Pi.sub_apply, Pi.add_apply, Pi.neg_apply, sub_eq_add_neg]

/--
If `f` is meromorphic at `x`, then `f + g` is meromorphic at `x` if and only if `g` is meromorphic
at `x`.
-/
lemma meromorphicAt_add_iff_meromorphicAt₁ {f g : 𝕜 → E} (hf : MeromorphicAt f x) :
    MeromorphicAt (f + g) x ↔ MeromorphicAt g x := by
  exact ⟨fun h ↦ by simpa using h.sub hf, fun _ ↦ by fun_prop⟩

/--
If `f` is meromorphic at `x`, then `f + g` is meromorphic at `x` if and only if `g` is meromorphic
at `x`.
-/
lemma meromorphicAt_fun_add_iff_meromorphicAt₁ {f g : 𝕜 → E} (hf : MeromorphicAt f x) :
    MeromorphicAt (fun z ↦ f z + g z) x ↔ MeromorphicAt g x :=
  meromorphicAt_add_iff_meromorphicAt₁ hf

/--
If `g` is meromorphic at `x`, then `f + g` is meromorphic at `x` if and only if `f` is meromorphic
at `x`.
-/
lemma meromorphicAt_add_iff_meromorphicAt₂ {f g : 𝕜 → E} (hg : MeromorphicAt g x) :
    MeromorphicAt (f + g) x ↔ MeromorphicAt f x := by
  rw [add_comm]
  exact meromorphicAt_add_iff_meromorphicAt₁ hg

/--
If `g` is meromorphic at `x`, then `f + g` is meromorphic at `x` if and only if `f` is meromorphic
at `x`.
-/
lemma meromorphicAt_fun_add_iff_meromorphicAt₂ {f g : 𝕜 → E} (hg : MeromorphicAt g x) :
    MeromorphicAt (fun z ↦ f z + g z) x ↔ MeromorphicAt f x :=
  meromorphicAt_add_iff_meromorphicAt₂ hg

/--
If `f` is meromorphic at `x`, then `f - g` is meromorphic at `x` if and only if `g` is meromorphic
at `x`.
-/
lemma meromorphicAt_sub_iff_meromorphicAt₁ {f g : 𝕜 → E} (hf : MeromorphicAt f x) :
    MeromorphicAt (f - g) x ↔ MeromorphicAt g x := by
  exact ⟨fun h ↦ by simpa using h.sub hf, fun _ ↦ by fun_prop⟩

/--
If `f` is meromorphic at `x`, then `f - g` is meromorphic at `x` if and only if `g` is meromorphic
at `x`.
-/
lemma meromorphicAt_fun_sub_iff_meromorphicAt₁ {f g : 𝕜 → E} (hf : MeromorphicAt f x) :
    MeromorphicAt (fun z ↦ f z - g z) x ↔ MeromorphicAt g x :=
  meromorphicAt_sub_iff_meromorphicAt₁ hf

/--
If `g` is meromorphic at `x`, then `f - g` is meromorphic at `x` if and only if `f` is meromorphic
at `x`.
-/
lemma meromorphicAt_sub_iff_meromorphicAt₂ {f g : 𝕜 → E} (hg : MeromorphicAt g x) :
    MeromorphicAt (f - g) x ↔ MeromorphicAt f x := by
  exact ⟨fun h ↦ by simpa using h.add hg, fun _ ↦ by fun_prop⟩

/--
If `g` is meromorphic at `x`, then `f - g` is meromorphic at `x` if and only if `f` is meromorphic
at `x`.
-/
lemma meromorphicAt_fun_sub_iff_meromorphicAt₂ {f g : 𝕜 → E} (hg : MeromorphicAt g x) :
    MeromorphicAt (fun z ↦ f z - g z) x ↔ MeromorphicAt f x :=
  meromorphicAt_sub_iff_meromorphicAt₂ hg

/-- With our definitions, `MeromorphicAt f x` depends only on the values of `f` on a punctured
neighbourhood of `x` (not on `f x`) -/
lemma congr {f g : 𝕜 → E} (hf : MeromorphicAt f x) (hfg : f =ᶠ[𝓝[≠] x] g) :
    MeromorphicAt g x :=
  hf.congr_domain (by simpa only [comap_id] using hfg)

/--
If two functions agree on a punctured neighborhood, then one is meromorphic iff the other is so.
-/
lemma meromorphicAt_congr {f g : 𝕜 → E} (h : f =ᶠ[𝓝[≠] x] g) :
    MeromorphicAt f x ↔ MeromorphicAt g x :=
  ⟨fun hf ↦ hf.congr h, fun hg ↦ hg.congr h.symm⟩

@[simp]
lemma update_iff [DecidableEq 𝕜] {f : 𝕜 → E} {z w : 𝕜} {e : E} :
    MeromorphicAt (Function.update f w e) z ↔ MeromorphicAt f z :=
  meromorphicAt_congr (Function.update_eventuallyEq_nhdsNE f w z e)

@[fun_prop]
lemma update [DecidableEq 𝕜] {f : 𝕜 → E} {z} (hf : MeromorphicAt f z) (w e) :
    MeromorphicAt (Function.update f w e) z :=
  update_iff.mpr hf

/-- A local reciprocal of a meromorphic function is meromorphic on their common punctured
domain. The multiplication identity excludes the zero germ. -/
theorem of_mul_eq_one {D : Type*} {coord : D → 𝕜} {f g : D → 𝕜'}
    (hf : MeromorphicAt f x coord) (hp : ∀ᶠ y in comap coord (𝓝[≠] x), f y * g y = 1) :
    MeromorphicAt g x coord := by
  obtain ⟨hc, m, a, ha, he⟩ := hf
  have : (comap coord (𝓝[≠] x)).NeBot :=
    (inferInstance : (𝓝[≠] x).NeBot).comap_of_range_mem hc
  have hcoord : ∀ᶠ y in comap coord (𝓝[≠] x), coord y ≠ x :=
    tendsto_comap.eventually self_mem_nhdsWithin
  have ha₀ : ¬ a =ᶠ[𝓝 x] 0 := by
    intro h
    have hz : ∀ᶠ y in comap coord (𝓝[≠] x), a (coord y) = 0 :=
      tendsto_comap.eventually (h.filter_mono nhdsWithin_le_nhds)
    obtain ⟨y, hy, hz', he', hp'⟩ := (hcoord.and (hz.and (he.and hp))).exists
    have ha' : (coord y - x) ^ m • f y = 0 := he'.trans hz'
    have hf' := (smul_eq_zero_iff_right (pow_ne_zero m (sub_ne_zero.mpr hy))).mp ha'
    simp [hf'] at hp'
  obtain ⟨n, u, hu, hux, hau⟩ := ha.exists_eventuallyEq_pow_smul_nonzero_iff.mpr ha₀
  obtain ⟨v, hv, huv⟩ := hu.exists_mul_eq_one hux.isUnit
  have hd : AnalyticAt 𝕜 (fun z ↦ z - x) x := analyticAt_id.sub analyticAt_const
  refine ⟨hc, n, _, (hd.pow m).fun_smul hv, ?_⟩
  filter_upwards [he, hp, tendsto_comap.eventually (hau.filter_mono nhdsWithin_le_nhds),
    tendsto_comap.eventually (huv.filter_mono nhdsWithin_le_nhds)] with y he hp hau huv
  calc
    (coord y - x) ^ n • g y =
        ((coord y - x) ^ n • u (coord y)) * (v (coord y) * g y) := by
      rw [smul_mul_assoc, ← mul_assoc, huv, one_mul]
    _ = ((coord y - x) ^ m • f y) * (v (coord y) * g y) := by rw [he, hau]
    _ = (coord y - x) ^ m • v (coord y) := by
      rw [smul_mul_assoc, mul_left_comm, hp, mul_one]

/-- Inversion is meromorphic on its pointwise unit locus when this locus covers a
punctured neighborhood of the center. -/
theorem inv {D : Type*} {coord : D → 𝕜} {f : D → 𝕜'} (hf : MeromorphicAt f x coord)
    (hc : range (fun y : {y : D | IsUnit (f y)} ↦ coord y.val) ∈ 𝓝[≠] x) :
    MeromorphicAt (fun y : {y : D | IsUnit (f y)} ↦ Checked.inv (f y) y.property) x
      (coord ∘ Subtype.val) :=
  (hf.comp_domain Subtype.val hc).of_mul_eq_one (.of_forall fun _ ↦ mul_inv_cancel₀)

/-- The quotient of two meromorphic functions on the domain where the denominator is a unit. -/
theorem div {D : Type*} {coord : D → 𝕜} {f g : D → 𝕜'} (hf : MeromorphicAt f x coord)
    (hg : MeromorphicAt g x coord)
    (hc : range (fun y : {y : D | IsUnit (g y)} ↦ coord y.val) ∈ 𝓝[≠] x) :
    MeromorphicAt (fun y : {y : D | IsUnit (g y)} ↦ Checked.div (f y) (g y) y.property) x
      (coord ∘ Subtype.val) :=
  (hf.comp_domain Subtype.val hc).mul (hg.inv hc)

/-- A fraction of analytic functions with a nonzero denominator germ is meromorphic
on the punctured neighborhood covered by its scalar domain. -/
theorem _root_.AnalyticAt.meromorphicAt_div {f g : 𝕜 → 𝕜'} (hf : AnalyticAt 𝕜 f x)
    (hg : AnalyticAt 𝕜 g x) (hn : ¬ g =ᶠ[𝓝 x] 0) :
    MeromorphicAt (fun y : {y : 𝕜 | g y ≠ 0} ↦ Checked.div (f y) (g y) y.property.isUnit)
      x Subtype.val := by
  let S := {y : 𝕜 | g y ≠ 0}
  have hc : range (Subtype.val : S → 𝕜) ∈ 𝓝[≠] x := by
    rw [Subtype.range_coe]
    exact hg.eventually_eq_zero_or_eventually_ne_zero.resolve_left hn
  have hrec : MeromorphicAt (fun y : S ↦ Checked.inv (g y) y.property.isUnit) x Subtype.val :=
    (hg.meromorphicAt.comp_domain (Subtype.val : S → 𝕜) hc).of_mul_eq_one
      (.of_forall fun _ ↦ mul_inv_cancel₀)
  exact (hf.meromorphicAt.comp_domain (Subtype.val : S → 𝕜) hc).mul hrec

/-- Integer powers retain all base points for a nonnegative exponent and otherwise
require the pointwise unit locus to cover a punctured neighborhood. -/
theorem zpow {D : Type*} {coord : D → 𝕜} {f : D → 𝕜'} (hf : MeromorphicAt f x coord) (n : ℤ)
    (hc : range (fun y : {y : D | n < 0 → IsUnit (f y)} ↦ coord y.val) ∈ 𝓝[≠] x) :
    MeromorphicAt (fun y : {y : D | n < 0 → IsUnit (f y)} ↦ Checked.zpow (f y) n y.property) x
      (coord ∘ Subtype.val) := by
  cases n with
  | ofNat n => exact (hf.comp_domain Subtype.val hc).pow n
  | negSucc n =>
    refine ((hf.comp_domain Subtype.val hc).pow (n + 1)).of_mul_eq_one (.of_forall fun y ↦ ?_)
    change f y.val ^ (n + 1) * Checked.zpow (f y.val) (Int.negSucc n) y.property = 1
    rw [zpow_negSucc₀, mul_inv_cancel₀]

/-- If a function is meromorphic at a point, then it is continuous at nearby points. -/
theorem eventually_continuousAt {f : 𝕜 → E}
    (h : MeromorphicAt f x) : ∀ᶠ y in 𝓝[≠] x, ContinuousAt f y := by
  obtain ⟨n, h⟩ := iff_exists_analyticAt_pow_smul.mp h
  have : ∀ᶠ y in 𝓝[≠] x, ContinuousAt (fun z ↦ (z - x) ^ n • f z) y :=
    nhdsWithin_le_nhds h.eventually_continuousAt
  filter_upwards [this, self_mem_nhdsWithin] with y hy h'y
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at h'y
  have hd : AnalyticAt 𝕜 (fun z ↦ (z - x) ^ n) y := (analyticAt_id.sub analyticAt_const).pow n
  obtain ⟨g, hg, he⟩ := hd.exists_mul_eq_one (pow_ne_zero n (sub_ne_zero.mpr h'y)).isUnit
  apply (hg.continuousAt.smul hy).congr
  filter_upwards [he] with z hz
  simp only [Pi.smul_apply', ← mul_smul, mul_comm (g z), hz, one_smul]

/-- In a complete space, a function which is meromorphic at a point is analytic at all nearby
points. The completeness assumption can be dispensed with if one assumes that `f` is meromorphic
on a set around `x`, see `MeromorphicOn.eventually_analyticAt`. -/
theorem eventually_analyticAt [CompleteSpace E] {f : 𝕜 → E}
    (h : MeromorphicAt f x) : ∀ᶠ y in 𝓝[≠] x, AnalyticAt 𝕜 f y := by
  obtain ⟨n, h⟩ := iff_exists_analyticAt_pow_smul.mp h
  apply AnalyticAt.eventually_analyticAt at h
  refine (h.filter_mono ?_).mp ?_
  · simp [nhdsWithin]
  · rw [eventually_nhdsWithin_iff]
    apply Filter.Eventually.of_forall
    intro y hy hf
    rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hy
    have hd : AnalyticAt 𝕜 (fun z ↦ (z - x) ^ n) y := (analyticAt_id.sub analyticAt_const).pow n
    obtain ⟨g, hg, he⟩ := hd.exists_mul_eq_one (pow_ne_zero n (sub_ne_zero.mpr hy)).isUnit
    apply (hg.fun_smul hf).congr
    filter_upwards [he] with z hz
    simp only [← mul_smul, mul_comm (g z), hz, one_smul]

/-- A derivative defined throughout a punctured neighborhood of a meromorphic function
is meromorphic there. Differentiating the cleared product gives an analytic numerator
after multiplying the derivative by the square of the clearing power. -/
theorem of_hasDerivAt [CompleteSpace E] {f f' : 𝕜 → E} (hf : MeromorphicAt f x)
    (hd : ∀ᶠ y in 𝓝[≠] x, HasDerivAt f (f' y) y) : MeromorphicAt f' x := by
  obtain ⟨n, hg⟩ := iff_exists_analyticAt_pow_smul.mp hf
  let c : 𝕜 → 𝕜 := fun y ↦ (y - x) ^ n
  let c' : 𝕜 → 𝕜 := fun y ↦ n * (y - x) ^ (n - 1)
  let g : 𝕜 → E := c • f
  have hc (y : 𝕜) : AnalyticAt 𝕜 c y := (analyticAt_id.sub analyticAt_const).pow n
  have hc' : AnalyticAt 𝕜 c' x := analyticAt_const.mul ((analyticAt_id.sub analyticAt_const).pow _)
  have hdc (y : 𝕜) : HasDerivAt c (c' y) y := by
    simpa only [c, c', id_eq, mul_one] using! ((hasDerivAt_id y).sub_const x).fun_pow n
  have hg' : AnalyticAt 𝕜 g x := hg
  refine ⟨by simp, n + n, _, ((hc x).fun_smul hg'.deriv).sub (hc'.fun_smul hg'), ?_⟩
  rw [comap_id]
  filter_upwards [hd] with y hy
  have he : _root_.deriv g y = c y • f' y + c' y • f y := ((hdc y).smul hy).deriv
  change (y - x) ^ (n + n) • f' y = c y • _root_.deriv g y - c' y • (c y • f y)
  rw [he, pow_add, mul_smul, smul_add, smul_comm (c' y) (c y), add_sub_cancel_right]

/-- Derivatives of meromorphic functions are meromorphic. -/
@[fun_prop]
protected theorem deriv [CompleteSpace E] {f : 𝕜 → E} {x : 𝕜} (h : MeromorphicAt f x) :
    MeromorphicAt (deriv f) x :=
  h.of_hasDerivAt (h.eventually_analyticAt.mono fun _ hy ↦ hy.differentiableAt.hasDerivAt)

/--
Iterated derivatives of meromorphic functions are meromorphic.
-/
@[fun_prop] theorem iterated_deriv [CompleteSpace E] {n : ℕ} {f : 𝕜 → E} {x : 𝕜}
    (h : MeromorphicAt f x) :
    MeromorphicAt (_root_.deriv^[n] f) x := by
  induction n with
  | zero => exact h
  | succ n IH => simpa only [Function.iterate_succ', Function.comp_apply] using IH.deriv

/-- The logarithmic derivative is meromorphic wherever the function is nonzero throughout
a punctured neighborhood. -/
theorem logDeriv [CompleteSpace 𝕜'] {f : 𝕜 → 𝕜'} (hf : MeromorphicAt f x)
    (hn : ∀ᶠ y in 𝓝[≠] x, f y ≠ 0) :
    MeromorphicAt (fun y : {y : 𝕜 | DifferentiableAt 𝕜 f y ∧ IsUnit (f y)} ↦
      _root_.logDeriv f y.val _root_.id y.property.1.existsUnique_hasDerivAt y.property.2)
        x Subtype.val := by
  let S := {y : 𝕜 | DifferentiableAt 𝕜 f y ∧ IsUnit (f y)}
  have hc : range (Subtype.val : S → 𝕜) ∈ 𝓝[≠] x := by
    rw [Subtype.range_coe]
    exact (hf.eventually_analyticAt.and hn).mono fun y hy ↦ ⟨hy.1.differentiableAt, hy.2.isUnit⟩
  have hrec : MeromorphicAt (fun y : S ↦ Checked.inv (f y) y.property.2) x Subtype.val :=
    (hf.comp_domain (Subtype.val : S → 𝕜) hc).of_mul_eq_one (.of_forall fun _ ↦ mul_inv_cancel₀)
  apply ((hf.deriv.comp_domain (Subtype.val : S → 𝕜) hc).mul hrec).congr_domain
  exact .of_forall fun y ↦ (logDeriv_apply f y.val (hderiv := y.property.1.existsUnique_hasDerivAt)
    (hvalue := y.property.2)).symm

end MeromorphicAt

section smul_iff

variable {g : 𝕜 → 𝕜} {x : 𝕜}

lemma meromorphicAt_smul_iff_of_ne_zero {f : 𝕜 → E} (hg : AnalyticAt 𝕜 g x) (hg' : g x ≠ 0) :
    MeromorphicAt (g • f) x ↔ MeromorphicAt f x := by
  refine ⟨fun hfg ↦ ?_, hg.meromorphicAt.smul⟩
  obtain ⟨v, hv, he⟩ := hg.exists_mul_eq_one hg'.isUnit
  apply (hv.meromorphicAt.smul hfg).congr
  filter_upwards [he.filter_mono nhdsWithin_le_nhds] with z hz
  simp only [Pi.smul_apply', ← mul_smul, mul_comm (v z), hz, one_smul]

lemma meromorphicAt_mul_iff_of_ne_zero {f : 𝕜 → 𝕜} (hg : AnalyticAt 𝕜 g x) (hg' : g x ≠ 0) :
    MeromorphicAt (g * f) x ↔ MeromorphicAt f x :=
  meromorphicAt_smul_iff_of_ne_zero hg hg'

/-- `MeromorphicAt` is invariant under scaling. -/
@[to_fun (attr := simp) meromorphicAt_fun_const_smul_iff_meromorphicAt]
theorem meromorphicAt_const_smul_iff_meromorphicAt {f : 𝕜 → E} {s : 𝕜} (hs : s ≠ 0) :
    MeromorphicAt (s • f) x ↔ MeromorphicAt f x := by
  constructor
  <;> intro hf
  · rw [((eq_inv_smul_iff₀ (ha := hs.isUnit)).mpr rfl : f = s⁻¹ • s • f)]
    fun_prop
  · fun_prop

end smul_iff

section composition
/-!
### Composition with an analytic function
-/

variable
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace 𝕜' F] [IsScalarTower 𝕜 𝕜' F]
  {x : 𝕜}

/-- The composition of a meromorphic and an analytic function is meromorphic. -/
@[fun_prop]
lemma MeromorphicAt.comp_analyticAt {f : 𝕜' → F} {g : 𝕜 → 𝕜'}
    (hf : MeromorphicAt f (g x)) (hg : AnalyticAt 𝕜 g x) :
    MeromorphicAt (f ∘ g) x := by
  obtain ⟨r, hr⟩ := MeromorphicAt.iff_exists_analyticAt_pow_smul.mp hf
  have hg₀ : AnalyticAt 𝕜 (g · - g x) x := hg.fun_sub analyticAt_const
  by_cases hg' : analyticOrderAt (g · - g x) x hg₀ = ⊤
  · -- trivial case: `g` is locally constant near `x`
    refine .congr (.const (f (g x)) x) ?_
    filter_upwards [nhdsWithin_le_nhds <| (analyticOrderAt_eq_top hg₀).mp hg'] with z hz
    grind
  · -- interesting case: `g z - g x` looks like `(z - x) ^ n` times a non-vanishing function
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hg'
    obtain ⟨h, han, hne, heq⟩ := hg₀.analyticOrderAt_eq_natCast.mp hn.symm
    set j := fun z ↦ (z - g x) ^ r • f z
    obtain ⟨v, hv, hvh⟩ := han.exists_mul_eq_one hne.isUnit
    have : AnalyticAt 𝕜 (fun i ↦ (v i) ^ r • j (g i)) x :=
      (hv.pow r).smul (hr.restrictScalars.comp hg)
    refine MeromorphicAt.iff_exists_analyticAt_pow_smul.mpr ⟨n * r, this.congr ?_⟩
    filter_upwards [heq, hvh] with z hz hvz
    simp only [j, Function.comp_apply, hz, smul_pow, pow_mul, smul_assoc]
    rw [smul_comm (v z ^ r) (((z - x) ^ n) ^ r), ← mul_smul, ← mul_pow,
      mul_comm (v z), hvz, one_pow, one_smul]

lemma meromorphicAt_comp_iff_of_deriv_ne_zero [CompleteSpace 𝕜] [CharZero 𝕜] {f : 𝕜 → E}
    {g : 𝕜 → 𝕜} (hg : AnalyticAt 𝕜 g x) (hg' : deriv g x ≠ 0) :
    MeromorphicAt (f ∘ g) x ↔ MeromorphicAt f (g x) := by
  refine ⟨fun hf ↦ ?_, by fun_prop⟩
  let r := hg.hasStrictDerivAt.localInverse _ _ _ hg'
  have hra : AnalyticAt 𝕜 r (g x) := hg.analyticAt_localInverse hg'
  have : r (g x) = x := HasStrictFDerivAt.localInverse_apply_image ..
  rw [← this] at hf
  refine (hf.comp_analyticAt hra).congr (.filter_mono ?_ nhdsWithin_le_nhds)
  exact EventuallyEq.fun_comp (HasStrictDerivAt.eventually_right_inverse ..) f

/-- `MeromorphicAt` is invariant under translation. -/
@[to_fun meromorphicAt_fun_comp_add_const_iff_meromorphicAt]
theorem meromorphicAt_comp_add_const_iff_meromorphicAt {c : 𝕜} {f : 𝕜 → E} :
    MeromorphicAt (f ∘ (· + c)) x ↔ MeromorphicAt f (x + c) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [show f = ((f ∘ fun x ↦ x + c) ∘ fun z ↦ z - c) by aesop]
    rw [show x = (x + c) - c by ring] at h
    exact h.comp_analyticAt (g := fun z ↦ z - c) (by fun_prop)
  · exact h.comp_analyticAt (g := fun z ↦ z + c) (by fun_prop)

/-- `MeromorphicAt` is invariant under translation. -/
@[to_fun meromorphicAt_fun_comp_sub_const_iff_meromorphicAt]
theorem meromorphicAt_comp_sub_const_iff_meromorphicAt {c : 𝕜} {f : 𝕜 → E} :
    MeromorphicAt (f ∘ (· - c)) x ↔ MeromorphicAt f (x - c) := by
  simp_rw [sub_eq_add_neg, meromorphicAt_comp_add_const_iff_meromorphicAt]

end composition


/-- Meromorphy of a function on a set. -/
@[fun_prop]
def MeromorphicOn {D : Type*} (f : D → E) (U : Set 𝕜)
    (coord : D → 𝕜 := by exact _root_.id) : Prop :=
  ∀ x ∈ U, MeromorphicAt f x coord

@[fun_prop]
lemma AnalyticOnNhd.meromorphicOn {f : 𝕜 → E} {U : Set 𝕜} (hf : AnalyticOnNhd 𝕜 f U) :
    MeromorphicOn f U :=
  fun x hx ↦ (hf x hx).meromorphicAt

/-- A function that is meromorphic on `U` is meromorphic at each point of `U`.

This is a transition lemma for `fun_prop`: from `MeromorphicOn f U` and `x ∈ U` in the local
context, it lets `fun_prop` prove `MeromorphicAt f x`, which is the default argument of
`meromorphicOrderAt f x`. -/
@[fun_prop]
lemma MeromorphicOn.meromorphicAt {f : 𝕜 → E} {U : Set 𝕜} {x : 𝕜} (hf : MeromorphicOn f U)
    (hx : x ∈ U) : MeromorphicAt f x :=
  hf x hx

namespace MeromorphicOn

variable {s t : 𝕜 → 𝕜'} {f g : 𝕜 → E} {U : Set 𝕜}
  (hs : MeromorphicOn s U) (ht : MeromorphicOn t U)
  (hf : MeromorphicOn f U) (hg : MeromorphicOn g U)

/--
If `f` is meromorphic on `U`, if `g` agrees with `f` on a codiscrete subset of `U` and outside of
`U`, then `g` is also meromorphic on `U`.
-/
theorem congr_codiscreteWithin_of_eqOn_compl (hf : MeromorphicOn f U)
    (h₁ : f =ᶠ[codiscreteWithin U] g) (h₂ : Set.EqOn f g Uᶜ) :
    MeromorphicOn g U := by
  intro x hx
  apply (hf x hx).congr
  simp_rw [EventuallyEq, Filter.Eventually, mem_codiscreteWithin,
    disjoint_principal_right] at h₁
  filter_upwards [h₁ x hx] with a ha
  simp at ha
  tauto

/--
If `f` is meromorphic on an open set `U`, if `g` agrees with `f` on a codiscrete subset of `U`, then
`g` is also meromorphic on `U`.
-/
theorem congr_codiscreteWithin (hf : MeromorphicOn f U) (h₁ : f =ᶠ[codiscreteWithin U] g)
    (h₂ : IsOpen U) :
    MeromorphicOn g U := by
  intro x hx
  apply (hf x hx).congr
  simp_rw [EventuallyEq, Filter.Eventually, mem_codiscreteWithin,
    disjoint_principal_right] at h₁
  have : U ∈ 𝓝[≠] x := by
    apply mem_nhdsWithin.mpr
    use U, h₂, hx, Set.inter_subset_left
  filter_upwards [this, h₁ x hx] with a h₁a h₂a
  simp only [Set.mem_compl_iff, Set.mem_sdiff, Set.mem_ofPred_eq, not_and] at h₂a
  tauto

/--
If two functions differ only on a discrete set of an open, then one is meromorphic iff so is the
other.
-/
theorem _root_.meromorphicOn_congr_codiscreteWithin {f g : 𝕜 → E} (h₁ : f =ᶠ[codiscreteWithin U] g)
    (h₂ : IsOpen U) :
    MeromorphicOn f U ↔ MeromorphicOn g U :=
  ⟨(·.congr_codiscreteWithin h₁ h₂), (·.congr_codiscreteWithin h₁.symm h₂)⟩

@[fun_prop]
protected lemma id {U : Set 𝕜} : MeromorphicOn id U := fun x _ ↦ .id x

@[fun_prop]
lemma const (e : E) {U : Set 𝕜} : MeromorphicOn (fun _ ↦ e) U :=
  fun x _ ↦ .const e x

section arithmetic

include hf in
lemma mono_set {V : Set 𝕜} (hv : V ⊆ U) : MeromorphicOn f V := fun x hx ↦ hf x (hv hx)

include hf hg in
@[to_fun (attr := fun_prop)]
lemma add : MeromorphicOn (f + g) U := fun x hx ↦ (hf x hx).add (hg x hx)

include hf hg in
@[to_fun (attr := fun_prop)]
lemma sub : MeromorphicOn (f - g) U := fun x hx ↦ (hf x hx).sub (hg x hx)

include hf in
@[to_fun (attr := fun_prop)]
lemma neg : MeromorphicOn (-f) U := fun x hx ↦ (hf x hx).neg

@[simp] lemma neg_iff : MeromorphicOn (-f) U ↔ MeromorphicOn f U :=
  ⟨fun h ↦ by simpa only [neg_neg] using h.neg, neg⟩

@[to_fun (attr := fun_prop)]
lemma smul [NormedAlgebra 𝕜 R] [IsScalarTower 𝕜 R E] {s : 𝕜 → R} (hs : MeromorphicOn s U)
    {f : 𝕜 → E} (hf : MeromorphicOn f U) :
    MeromorphicOn (s • f) U :=
  fun x hx ↦ (hs x hx).smul (hf x hx)

include hf in
@[to_fun (attr := fun_prop)]
lemma const_smul [SMulCommClass 𝕜 R E] (c : R) : MeromorphicOn (c • f) U :=
  fun x hx ↦ (hf x hx).const_smul c

/-- MeromorphicOn is invariant under scaling. -/
@[to_fun (attr := simp) meromorphicOn_fun_const_smul_iff_meromorphicOn]
theorem meromorphicOn_const_smul_iff_meromorphicOn {s : 𝕜} (hs : s ≠ 0) :
    MeromorphicOn (s • f) U ↔ MeromorphicOn f U :=
  ⟨fun hf x hx ↦ (meromorphicAt_const_smul_iff_meromorphicAt hs).mp (hf x hx),
    fun hf x hx ↦ (meromorphicAt_const_smul_iff_meromorphicAt hs).mpr (hf x hx)⟩

include hs ht in
@[to_fun (attr := fun_prop)]
lemma mul : MeromorphicOn (s * t) U := fun x hx ↦ (hs x hx).mul (ht x hx)

/-- Finite products of meromorphic functions are meromorphic. -/
@[fun_prop]
lemma prod {U : Set 𝕜} {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → 𝕜'}
    (h : ∀ σ ∈ s, MeromorphicOn (f σ) U) :
    MeromorphicOn (∏ n ∈ s, f n) U :=
  fun z hz ↦ MeromorphicAt.prod (h · · z hz)

/-- Finite products of meromorphic functions are meromorphic. -/
@[fun_prop]
lemma fun_prod {U : Set 𝕜} {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → 𝕜'}
    (h : ∀ σ ∈ s, MeromorphicOn (f σ) U) :
    MeromorphicOn (fun z ↦ ∏ n ∈ s, f n z) U :=
  fun z hz ↦ MeromorphicAt.fun_prod (h · · z hz)

/-- Finprods of meromorphic functions are meromorphic. -/
@[fun_prop]
lemma finprod {U : Set 𝕜} {ι : Type*} {f : ι → 𝕜 → 𝕜'} (h : ∀ σ, MeromorphicOn (f σ) U) :
    MeromorphicOn (∏ᶠ n, f n) U :=
  fun z hz ↦ MeromorphicAt.finprod (h · z hz)

/-- Finite sums of meromorphic functions are meromorphic. -/
@[fun_prop]
lemma sum {U : Set 𝕜} {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → E}
    (h : ∀ σ ∈ s, MeromorphicOn (f σ) U) :
    MeromorphicOn (∑ n ∈ s, f n) U :=
  fun z hz ↦ MeromorphicAt.sum (h · · z hz)

/-- Finite sums of meromorphic functions are meromorphic. -/
@[fun_prop]
lemma fun_sum {U : Set 𝕜} {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → E}
    (h : ∀ σ ∈ s, MeromorphicOn (f σ) U) :
    MeromorphicOn (fun z ↦ ∑ n ∈ s, f n z) U :=
  fun z hz ↦ MeromorphicAt.fun_sum (fun σ hσ ↦ h σ hσ z hz)

/-- Finsums of meromorphic functions are meromorphic. -/
@[fun_prop]
lemma finsum {U : Set 𝕜} {ι : Type*} {f : ι → 𝕜 → 𝕜'} (h : ∀ σ, MeromorphicOn (f σ) U) :
    MeromorphicOn (∑ᶠ n, f n) U :=
  fun z hz ↦ MeromorphicAt.finsum (h · z hz)

@[fun_prop]
theorem inv {D : Type*} {coord : D → 𝕜} {s : D → 𝕜'} (hs : MeromorphicOn s U coord)
    (hc : ∀ x ∈ U, range (fun y : {y : D | IsUnit (s y)} ↦ coord y.val) ∈ 𝓝[≠] x) :
    MeromorphicOn (fun y : {y : D | IsUnit (s y)} ↦ Checked.inv (s y) y.property) U
      (coord ∘ Subtype.val) := fun x hx ↦ (hs x hx).inv (hc x hx)

@[fun_prop]
theorem div {D : Type*} {coord : D → 𝕜} {s t : D → 𝕜'} (hs : MeromorphicOn s U coord)
    (ht : MeromorphicOn t U coord)
    (hc : ∀ x ∈ U, range (fun y : {y : D | IsUnit (t y)} ↦ coord y.val) ∈ 𝓝[≠] x) :
    MeromorphicOn (fun y : {y : D | IsUnit (t y)} ↦ Checked.div (s y) (t y) y.property) U
      (coord ∘ Subtype.val) := fun x hx ↦ (hs x hx).div (ht x hx) (hc x hx)

include hs in
@[to_fun (attr := fun_prop)]
lemma pow (n : ℕ) : MeromorphicOn (s ^ n) U := fun x hx ↦ (hs x hx).pow _

theorem zpow {D : Type*} {coord : D → 𝕜} {s : D → 𝕜'} (hs : MeromorphicOn s U coord)
    (n : ℤ) (hc : ∀ x ∈ U, range (fun y : {y : D | n < 0 → IsUnit (s y)} ↦ coord y.val) ∈ 𝓝[≠] x) :
    MeromorphicOn (fun y : {y : D | n < 0 → IsUnit (s y)} ↦ Checked.zpow (s y) n y.property) U
      (coord ∘ Subtype.val) := fun x hx ↦ (hs x hx).zpow n (hc x hx)

include hf in
/-- Derivatives of meromorphic functions are meromorphic. -/
@[fun_prop]
protected theorem deriv [CompleteSpace E] : MeromorphicOn (deriv f) U := fun z hz ↦ (hf z hz).deriv

include hf in
/-- Iterated derivatives of meromorphic functions are meromorphic. -/
@[fun_prop]
theorem iterated_deriv [CompleteSpace E] {n : ℕ} : MeromorphicOn (deriv^[n] f) U :=
  fun z hz ↦ (hf z hz).iterated_deriv

/-- If `f` is meromorphic on a set, then so is its logarithmic derivative. -/
@[fun_prop]
protected theorem logDeriv [CompleteSpace 𝕜'] {f : 𝕜 → 𝕜'} (hf : MeromorphicOn f U)
    (hn : ∀ x ∈ U, ∀ᶠ y in 𝓝[≠] x, f y ≠ 0) :
    MeromorphicOn (fun y : {y : 𝕜 | DifferentiableAt 𝕜 f y ∧ IsUnit (f y)} ↦
      _root_.logDeriv f y.val _root_.id y.property.1.existsUnique_hasDerivAt y.property.2)
        U Subtype.val :=
  fun x hx ↦ (hf x hx).logDeriv (hn x hx)

/-- `MeromorphicOn` is invariant under translation. -/
@[to_fun meromorphicOn_fun_comp_add_const_iff_meromorphicOn]
theorem meromorphicOn_comp_add_const_iff_meromorphicOn {c : 𝕜} {U : Set 𝕜} :
    MeromorphicOn (f ∘ (· + c)) U ↔ MeromorphicOn f (U + {c}) := by
  refine ⟨fun h y hy ↦ ?_, fun h y hy ↦ ?_⟩
  · rw [add_singleton, mem_image] at hy
    obtain ⟨x, h₁x, h₂x⟩ := hy
    simpa [← h₂x, ← meromorphicAt_comp_add_const_iff_meromorphicAt] using h x h₁x
  · rw [meromorphicAt_comp_add_const_iff_meromorphicAt]
    aesop

/-- `MeromorphicOn` is invariant under translation. -/
@[to_fun meromorphicOn_fun_comp_sub_const_iff_meromorphicOn]
theorem meromorphicOn_comp_sub_const_iff_meromorphicOn {c : 𝕜} {U : Set 𝕜} :
    MeromorphicOn (f ∘ (· - c)) U ↔ MeromorphicOn f (U - {c}) := by
  simp_rw [sub_eq_add_neg, meromorphicOn_comp_add_const_iff_meromorphicOn, neg_singleton]

/-- `MeromorphicOn` is invariant under translation, special case where the set is a ball. -/
@[to_fun (attr := simp) meromorphicOn_ball_fun_comp_sub_const_iff_meromorphicOn_ball]
theorem meromorphicOn_ball_comp_sub_const_iff_meromorphicOn_ball {c : 𝕜} {R : ℝ} :
    MeromorphicOn (f ∘ (· - c)) (ball c R) ↔ MeromorphicOn f (ball (0 : 𝕜) R) := by
  rw [meromorphicOn_comp_sub_const_iff_meromorphicOn, ball_sub_singleton, sub_self]

/-- `MeromorphicOn` is invariant under translation, special case where the set is a closed ball. -/
@[to_fun (attr := simp) meromorphicOn_closedBall_fun_comp_sub_const_iff_meromorphicOn_closedBall]
theorem meromorphicOn_closedBall_comp_sub_const_iff_meromorphicOn_closedBall {c : 𝕜} {R : ℝ} :
    MeromorphicOn (f ∘ (· - c)) (closedBall c R) ↔ MeromorphicOn f (closedBall (0 : 𝕜) R) := by
  rw [meromorphicOn_comp_sub_const_iff_meromorphicOn, closedBall_sub_singleton, sub_self]

/-- `MeromorphicOn` is invariant under translation, special case where the set is a sphere. -/
@[to_fun (attr := simp) meromorphicOn_sphere_fun_comp_sub_const_iff_meromorphicOn_sphere]
theorem meromorphicOn_sphere_comp_sub_const_iff_meromorphicOn_sphere {c : 𝕜} {R : ℝ} :
    MeromorphicOn (f ∘ (· - c)) (sphere c R) ↔ MeromorphicOn f (sphere (0 : 𝕜) R) := by
  rw [meromorphicOn_comp_sub_const_iff_meromorphicOn, sphere_sub_singleton, sub_self]

end arithmetic

section composition

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace 𝕜' F]
  [IsScalarTower 𝕜 𝕜' F] {V : Set 𝕜'}

/-- The composition of a meromorphic and an analytic function is meromorphic. -/
lemma comp_analyticOnNhd {f : 𝕜' → F} {g : 𝕜 → 𝕜'} (hf : MeromorphicOn f V)
    (hg : AnalyticOnNhd 𝕜 g U) (hUV : Set.MapsTo g U V) :
    MeromorphicOn (f ∘ g) U :=
  fun z hz ↦ (hf _ (hUV hz)).comp_analyticAt (hg z hz)

/-- Variant of `MeromorphicOn.comp_analyticOnNhd` which trades the `Set.MapsTo` hypothesis for a
smaller set. -/
@[fun_prop]
lemma comp_analyticOnNhd_inter {f : 𝕜' → F} {g : 𝕜 → 𝕜'} (hf : MeromorphicOn f V)
    (hg : AnalyticOnNhd 𝕜 g U) :
    MeromorphicOn (f ∘ g) (U ∩ g ⁻¹' V) :=
  hf.comp_analyticOnNhd (hg.mono inter_subset_left) inter_subset_right

end composition

include hf in
lemma congr (h_eq : Set.EqOn f g U) (hu : IsOpen U) : MeromorphicOn g U := by
  refine fun x hx ↦ (hf x hx).congr (EventuallyEq.filter_mono ?_ nhdsWithin_le_nhds)
  exact eventually_of_mem (hu.mem_nhds hx) h_eq

theorem eventually_codiscreteWithin_analyticAt
    [CompleteSpace E] (f : 𝕜 → E) (h : MeromorphicOn f U) :
    ∀ᶠ (y : 𝕜) in codiscreteWithin U, AnalyticAt 𝕜 f y := by
  rw [eventually_iff, mem_codiscreteWithin]
  intro x hx
  rw [disjoint_principal_right]
  apply Filter.mem_of_superset ((h x hx).eventually_analyticAt)
  intro x hx
  simp [hx]

/--
The singular set of a meromorphic function is countable.
-/
theorem countable_compl_analyticAt_inter [SecondCountableTopology 𝕜] [CompleteSpace E]
    (h : MeromorphicOn f U) :
    ({z | AnalyticAt 𝕜 f z}ᶜ ∩ U).Countable := by
  apply (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete
    (isDiscrete_of_codiscreteWithin _)
  simpa using! eventually_codiscreteWithin_analyticAt f h

end MeromorphicOn

/-- Meromorphy of a function on all of 𝕜. -/
@[fun_prop]
def Meromorphic {D : Type*} (f : D → E) (coord : D → 𝕜 := by exact _root_.id) :=
  ∀ x, MeromorphicAt f x coord

/-- A function is meromorphic iff it is meromorphic on Set.univ. -/
@[simp]
lemma meromorphicOn_univ {f : 𝕜 → E} : MeromorphicOn f Set.univ ↔ Meromorphic f := by tauto

namespace Meromorphic

variable
  {ι : Type*} {s : Finset ι}
  {f g : 𝕜 → E} {F : ι → 𝕜 → 𝕜'} {G : ι → 𝕜 → E}

@[fun_prop]
lemma meromorphicAt {x : 𝕜} (hf : Meromorphic f) : MeromorphicAt f x := hf x

@[fun_prop]
lemma meromorphicOn {s : Set 𝕜} (hf : Meromorphic f) : MeromorphicOn f s := fun x _ ↦ hf x

section composition

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace 𝕜' F]
  [IsScalarTower 𝕜 𝕜' F]

/-- The composition of a meromorphic and an analytic function is meromorphic. Compared to
`MeromorphicOn.comp_analyticOnNhd`, the outer function is meromorphic everywhere, so no
`Set.MapsTo` hypothesis is required. -/
@[fun_prop]
lemma comp_analyticOnNhd {f : 𝕜' → F} {g : 𝕜 → 𝕜'} {U : Set 𝕜} (hf : Meromorphic f)
    (hg : AnalyticOnNhd 𝕜 g U) :
    MeromorphicOn (f ∘ g) U :=
  fun z hz ↦ (hf _).comp_analyticAt (hg z hz)

end composition

@[fun_prop]
protected lemma id : Meromorphic (id : 𝕜 → 𝕜) := fun x ↦ .id x

@[fun_prop]
lemma const (x : E) : Meromorphic fun _ : 𝕜 ↦ x := fun _ ↦ .const _ _

@[to_fun (attr := fun_prop)]
lemma neg (hf : Meromorphic f) : Meromorphic (-f) := fun x ↦ (hf x).neg

@[to_fun (attr := fun_prop)]
lemma add (hf : Meromorphic f) (hg : Meromorphic g) :
    Meromorphic (f + g) := fun x ↦ (hf x).add (hg x)

@[to_fun (attr := fun_prop)]
theorem sum (h : ∀ σ ∈ s, Meromorphic (G σ)) :
    Meromorphic (∑ n ∈ s, G n) := fun x ↦ MeromorphicAt.sum (h · · x)

@[fun_prop]
theorem finsum (h : ∀ σ, Meromorphic (F σ)) :
    Meromorphic (∑ᶠ σ, F σ) := fun x ↦ MeromorphicAt.finsum (h · x)

@[to_fun (attr := fun_prop)]
lemma sub (hf : Meromorphic f) (hg : Meromorphic g) :
    Meromorphic (f - g) := fun x ↦ (hf x).sub (hg x)

@[to_fun (attr := fun_prop)]
lemma smul [NormedAlgebra 𝕜 R] [IsScalarTower 𝕜 R E] {f : 𝕜 → R} (hf : Meromorphic f)
    (hg : Meromorphic g) :
    Meromorphic (f • g) := fun x ↦ (hf x).smul (hg x)

@[to_fun (attr := fun_prop)]
lemma const_smul [SMulCommClass 𝕜 R E] (hf : Meromorphic f) (c : R) :
    Meromorphic (c • f) := fun x ↦ (hf x).const_smul c

/-- Meromorphic is invariant under scaling. -/
@[to_fun (attr := simp) _root_.meromorphic_fun_const_smul_iff_meromorphic]
theorem _root_.meromorphic_const_smul_iff_meromorphic {s : 𝕜} (hs : s ≠ 0) :
    Meromorphic (s • f) ↔ Meromorphic f :=
  ⟨fun hf x ↦ (meromorphicAt_const_smul_iff_meromorphicAt hs).mp (hf x),
    fun hf x ↦ (meromorphicAt_const_smul_iff_meromorphicAt hs).mpr (hf x)⟩

@[to_fun (attr := fun_prop)]
lemma mul {f g : 𝕜 → 𝕜'} (hf : Meromorphic f) (hg : Meromorphic g) :
    Meromorphic (f * g) := fun x ↦ (hf x).mul (hg x)

theorem inv {D : Type*} {coord : D → 𝕜} {f : D → 𝕜'} (hf : Meromorphic f coord)
    (hc : ∀ x, range (fun y : {y : D | IsUnit (f y)} ↦ coord y.val) ∈ 𝓝[≠] x) :
    Meromorphic (fun y : {y : D | IsUnit (f y)} ↦ Checked.inv (f y) y.property)
      (coord ∘ Subtype.val) := fun x ↦ (hf x).inv (hc x)

@[to_fun (attr := fun_prop)]
theorem prod (h : ∀ σ ∈ s, Meromorphic (F σ)) :
    Meromorphic (∏ n ∈ s, F n) := fun x ↦ MeromorphicAt.prod (h · · x)

@[fun_prop]
theorem finprod (h : ∀ σ, Meromorphic (F σ)) :
    Meromorphic (∏ᶠ σ, F σ) := fun x ↦ MeromorphicAt.finprod (h · x)

theorem div {D : Type*} {coord : D → 𝕜} {f g : D → 𝕜'} (hf : Meromorphic f coord)
    (hg : Meromorphic g coord)
    (hc : ∀ x, range (fun y : {y : D | IsUnit (g y)} ↦ coord y.val) ∈ 𝓝[≠] x) :
    Meromorphic (fun y : {y : D | IsUnit (g y)} ↦ Checked.div (f y) (g y) y.property)
      (coord ∘ Subtype.val) := fun x ↦ (hf x).div (hg x) (hc x)

@[to_fun (attr := fun_prop)]
lemma pow {f : 𝕜 → 𝕜'} {n : ℕ} (hf : Meromorphic f) : Meromorphic (f ^ n) := fun x ↦ (hf x).pow n

theorem zpow {D : Type*} {coord : D → 𝕜} {f : D → 𝕜'} (hf : Meromorphic f coord)
    (n : ℤ) (hc : ∀ x, range (fun y : {y : D | n < 0 → IsUnit (f y)} ↦ coord y.val) ∈ 𝓝[≠] x) :
    Meromorphic (fun y : {y : D | n < 0 → IsUnit (f y)} ↦ Checked.zpow (f y) n y.property)
      (coord ∘ Subtype.val) := fun x ↦ (hf x).zpow n (hc x)

@[fun_prop]
protected lemma deriv [CompleteSpace E] (hf : Meromorphic f) : Meromorphic (deriv f) :=
  fun x ↦ (hf x).deriv

@[fun_prop]
lemma iterated_deriv [CompleteSpace E] {n : ℕ} (hf : Meromorphic f) :
    Meromorphic (deriv^[n] f) := fun x ↦ (hf x).iterated_deriv

/-- If `f` is meromorphic, then so is its logarithmic derivative. -/
protected theorem logDeriv [CompleteSpace 𝕜'] {f : 𝕜 → 𝕜'} (hf : Meromorphic f)
    (hn : ∀ x, ∀ᶠ y in 𝓝[≠] x, f y ≠ 0) :
    Meromorphic (fun y : {y : 𝕜 | DifferentiableAt 𝕜 f y ∧ IsUnit (f y)} ↦
      _root_.logDeriv f y.val _root_.id y.property.1.existsUnique_hasDerivAt y.property.2)
        Subtype.val :=
  fun x ↦ (hf x).logDeriv (hn x)

/--
If `f` is meromorphic, if `g` agrees with `f` on a codiscrete set, then `g` is also meromorphic.
-/
theorem congr_codiscrete (hf : Meromorphic f) (h₁ : f =ᶠ[codiscrete 𝕜] g) :
    Meromorphic g := by
  rw [← meromorphicOn_univ] at *
  exact hf.congr_codiscreteWithin (eventuallyEq_of_mem h₁ fun ⦃x⦄ a ↦ a) isOpen_univ

/--
If two functions differ only on a discrete set, then one is meromorphic iff so is the other.
-/
theorem _root_.meromorphic_congr_codiscrete (h₁ : f =ᶠ[codiscrete 𝕜] g) :
    Meromorphic f ↔ Meromorphic g :=
  ⟨(·.congr_codiscrete h₁), (·.congr_codiscrete h₁.symm)⟩

/--
The singular set of a meromorphic function is countable.
-/
theorem countable_compl_analyticAt [SecondCountableTopology 𝕜] [CompleteSpace E]
    (h : Meromorphic f) :
    {z | AnalyticAt 𝕜 f z}ᶜ.Countable := by
  simpa using (h.meromorphicOn (s := univ)).countable_compl_analyticAt_inter

/--
Meromorphic functions are measurable.
-/
@[fun_prop] theorem measurable [SigmaAlgebra 𝕜] [SecondCountableTopology 𝕜] [BorelSpace 𝕜]
    [SigmaAlgebra E] [CompleteSpace E] [BorelSpace E] (h : Meromorphic f) :
    Measurable f := by
  set s := {z : 𝕜 | AnalyticAt 𝕜 f z}
  have h₁ : sᶜ.Countable := by simpa using h.countable_compl_analyticAt
  have h₁' := h₁.to_subtype
  have h₂ : IsOpen s := isOpen_analyticAt 𝕜 f
  have h₃ : ContinuousOn f s := fun z hz ↦ hz.continuousAt.continuousWithinAt
  exact .of_union_range_cover (.subtype_coe h₂.measurableSet) (.subtype_coe h₁.measurableSet)
    (by simp [-mem_compl_iff]) h₃.domRestrict.measurable (measurable_of_countable _)

/-- `Meromorphic` is invariant under translation. -/
@[simp] theorem meromorphic_comp_add_const_iff_meromorphic {c : 𝕜} :
    Meromorphic (f ∘ (· + c)) ↔ Meromorphic f := by
  rw [Meromorphic, Meromorphic, (Equiv.subRight c).surjective.forall]
  simp [meromorphicAt_comp_add_const_iff_meromorphicAt]

/-- `Meromorphic` is invariant under translation. -/
@[simp] theorem meromorphic_fun_comp_add_const_iff_meromorphic {c : 𝕜} :
    Meromorphic (fun z ↦ f (z + c)) ↔ Meromorphic f :=
  meromorphic_comp_add_const_iff_meromorphic

/-- `Meromorphic` is invariant under translation. -/
@[simp] theorem meromorphic_comp_sub_const_iff_meromorphic {c : 𝕜} :
    Meromorphic (f ∘ (· - c)) ↔ Meromorphic f := by
  nth_rw 2 [← meromorphic_comp_add_const_iff_meromorphic (c := -c)]
  simp_rw [sub_eq_add_neg]

/-- `Meromorphic` is invariant under translation. -/
@[simp] theorem meromorphic_fun_comp_sub_const_iff_meromorphic {c : 𝕜} :
    Meromorphic (fun z ↦ f (z - c)) ↔ Meromorphic f :=
  meromorphic_comp_sub_const_iff_meromorphic

end Meromorphic
