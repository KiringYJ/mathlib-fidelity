/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
public import Mathlib.MeasureTheory.Integral.CircleAverage
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus


/-!
# The Proximity Function of Value Distribution Theory

This file defines the "proximity function" attached to a meromorphic function defined on the complex
plane.  Also known as the `Nevanlinna Proximity Function`, this is one of the three main functions
used in Value Distribution Theory.

The proximity function is a logarithmically weighted measure quantifying how well a meromorphic
function `f` approximates the constant function `a` on the circle of radius `R` in the complex
plane.  The definition ensures that large values correspond to good approximation.

For a finite target, the circle integral is taken over the angles at which the function differs
from that target. On a circle of nonzero radius only finitely many coincidences need to be omitted.
At radius zero the angle map is constant, so finite proximity exists exactly when the value at
the center differs from the target. Negative radii give the same average as their absolute values.

See Section VI.2 of [Lang, *Introduction to Complex Hyperbolic Spaces*][MR886677] or Section 1.1 of
[Noguchi-Winkelmann, *Nevanlinna Theory in Several Complex Variables and Diophantine
Approximation*][MR3156076] for a detailed discussion.
-/

@[expose] public section

open Filter Metric Real Set
open scoped Topology

namespace ValueDistribution

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f g : ℂ → E} {a : WithTop E} {a₀ : E}

open Real

/-- Evidence for a finite real proximity at radius zero; at every nonzero radius the usual
noncoincidence condition on meromorphic germs suffices. -/
syntax (name := valueDistributionRadius) "value_distribution_radius" : tactic
macro_rules
  | `(tactic| value_distribution_radius) =>
    `(tactic| first
      | assumption
      | exact fun _ ↦ WithTop.coe_ne_top
      | intro h; exfalso; contradiction
      | intro h; exfalso; linarith
      | intro hr; subst_vars; simpa using (by assumption)
      | fail "at radius zero, the center value must differ from the target")

/-- Nevanlinna proximity on its finite real domain. At a finite target the integral evaluates
the reciprocal only on the set of angles with nonzero distance to the target. -/
noncomputable def proximity (f : ℂ → E) (a : WithTop E) (_hf : Meromorphic f := by fun_prop_default)
    (_ha : ∀ z, ∃ᶠ w in 𝓝[≠] z, (f w : WithTop E) ≠ a := by value_distribution_frequently_ne)
    (r : ℝ) (hr : r = 0 → (f 0 : WithTop E) ≠ a := by value_distribution_radius) : ℝ :=
  match a, hr with
  | none, _ => circleAverage (log⁺ ‖f ·‖) 0 r
  | some a₀, _ => (2 * π)⁻¹ • intervalIntegral.integralSubtypeOn
      (fun θ : {θ : ℝ | f (circleMap 0 r θ) ≠ a₀} ↦
        log⁺ (Checked.inv ‖f (circleMap 0 r θ.val) - a₀‖
          (norm_ne_zero_iff.mpr (sub_ne_zero.mpr θ.property)).isUnit)) 0 (2 * π)

/-- Proximity to infinity is the circle average of the positive part of the log norm. -/
lemma proximity_top {hf : Meromorphic f} :
    (fun r ↦ proximity f ⊤ hf (frequently_coe_ne_top f) r) = circleAverage (log⁺ ‖f ·‖) 0 := rfl

@[simp] lemma proximity_top_apply {hf : Meromorphic f}
    {ha : ∀ z, ∃ᶠ w in 𝓝[≠] z, (f w : WithTop E) ≠ ⊤} {r : ℝ} {hr : r = 0 → (f 0 : WithTop E) ≠ ⊤} :
    proximity f ⊤ hf ha r hr = circleAverage (log⁺ ‖f ·‖) 0 r := rfl

/-!
## The Domain

For a finite value, the arguments of the proximity function make the conventions of its integrand
irrelevant: the function takes the value at only finitely many points of each circle, and the
integrand is circle integrable.
-/

/--
A meromorphic function that takes a finite value `a₀` on no punctured neighborhood takes it at only
finitely many points of each circle, so on a circle of nonzero radius the integrand
`log⁺ (1 / ‖f · - a₀‖)` of the proximity function is finite almost everywhere.
-/
lemma finite_sphere_inter_setOf_eq (hf : Meromorphic f)
    (ha : ∀ z, ∃ᶠ w in 𝓝[≠] z, (f w : WithTop E) ≠ a₀) (r : ℝ) :
    (sphere (0 : ℂ) |r| ∩ {w | f w = a₀}).Finite :=
  ((isCompact_sphere (0 : ℂ) |r|).finite_sdiff_of_mem_codiscreteWithin
    (codiscreteWithin_mono (subset_univ _) (mem_codiscrete_iff_forall_mem_nhdsNE.2 fun z ↦
      eventually_ne_of_frequently_coe_ne (hf z) (ha z)))).subset
    fun _ hw ↦ ⟨hw.1, fun h ↦ h hw.2⟩

open MeasureTheory in
open scoped Interval in
/-- The angular integral for a finite target is the circle average of the negative part
of the log distance on every admissible radius. -/
lemma proximity_coe {f : ℂ → E} {a : E} {hf : Meromorphic f}
    {ha : ∀ z, ∃ᶠ w in 𝓝[≠] z, (f w : WithTop E) ≠ a} {r : ℝ}
    (hr : r = 0 → (f 0 : WithTop E) ≠ a) :
    proximity f a hf ha r hr = circleAverage (fun z ↦ max 0 (-log ‖f z - a‖)) 0 r := by
  have hz := finite_sphere_inter_setOf_eq hf ha r
  let S := {θ : ℝ | f (circleMap 0 r θ) ≠ a}
  let Z := sphere (0 : ℂ) |r| ∩ {z | f z = a}
  have hS : S = (circleMap 0 r ⁻¹' Z)ᶜ := by
    ext θ
    simp [S, Z]
  have hs : MeasurableSet S := hS ▸ (hz.measurableSet.preimage (measurable_circleMap _ _)).compl
  have hfull : ∀ᵐ θ ∂volume.restrict [[(0 : ℝ), 2 * π]], θ ∈ S := by
    by_cases h : r = 0
    · subst r
      exact .of_forall fun θ ↦ by simpa [S] using (WithTop.coe_injective.ne_iff.mp (hr rfl))
    · have hcod : Zᶜ ∈ codiscreteWithin (sphere (0 : ℂ) |r|) := by
        rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE]
        intro z _
        exact Filter.mem_of_superset ((nhdsNE_le_cofinite z) hz.compl_mem_cofinite)
          Set.subset_union_left
      apply ae_restrict_le_codiscreteWithin measurableSet_uIcc
      rw [hS, ← preimage_compl]
      exact codiscreteWithin_mono (subset_univ _) (circleMap_preimage_codiscrete h hcod)
  have he : (fun θ : S ↦ log⁺ (Checked.inv ‖f (circleMap 0 r θ.val) - a‖
      (norm_ne_zero_iff.mpr (sub_ne_zero.mpr θ.property)).isUnit)) =
      fun θ : S ↦ max 0 (-log ‖f (circleMap 0 r θ.val) - a‖) := by
    funext θ
    rw [posLog_apply, log_inv]
  change (2 * π)⁻¹ • intervalIntegral.integralSubtypeOn
    (fun θ : S ↦ log⁺ (Checked.inv ‖f (circleMap 0 r θ.val) - a‖
      (norm_ne_zero_iff.mpr (sub_ne_zero.mpr θ.property)).isUnit)) 0 (2 * π) = _
  rw [he, circleAverage_def]
  exact congrArg ((2 * π)⁻¹ • ·) (intervalIntegral.integral_subtypeOn_eq_integral hs
    (fun θ : ℝ ↦ max 0 (-log ‖f (circleMap 0 r θ) - a‖)) hfull)

/-- Proximity to zero is the circle average of the negative part of the log norm. -/
lemma proximity_zero {hf : Meromorphic f} {ha : ∀ z, ∃ᶠ w in 𝓝[≠] z, (f w : WithTop E) ≠ 0}
    {r : ℝ} (hr : r = 0 → (f 0 : WithTop E) ≠ 0) :
    proximity f 0 hf ha r hr = circleAverage (fun z ↦ max 0 (-log ‖f z‖)) 0 r := by
  simpa only [sub_zero, WithTop.coe_zero] using (proximity_coe (hf := hf) (a := 0) (ha := ha) hr)

/-- At radius zero a finite-target proximity evaluates the genuine reciprocal distance. -/
@[simp] lemma proximity_coe_eval_zero {hf : Meromorphic f}
    {ha : ∀ z, ∃ᶠ w in 𝓝[≠] z, (f w : WithTop E) ≠ a₀} (hn : f 0 ≠ a₀) :
    proximity f a₀ hf ha 0 (fun _ ↦ WithTop.coe_injective.ne_iff.mpr hn) =
      log⁺ (Checked.inv ‖f 0 - a₀‖ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hn)).isUnit) := by
  rw [proximity_coe, circleAverage_zero, posLog_apply, log_inv]

lemma proximity_top_eval_zero {hf : Meromorphic f} :
    proximity f ⊤ hf (frequently_coe_ne_top f) 0 = log⁺ ‖f 0‖ := by
  rw [proximity_top_apply, circleAverage_zero]

/-- The negative part of the log distance is integrable on every circle. -/
lemma circleIntegrable_neg_log_norm_sub (hf : Meromorphic f) (a₀ : E) (r : ℝ) :
    CircleIntegrable (fun z ↦ max 0 (-log ‖f z - a₀‖)) 0 r := by
  have h : MeromorphicOn (f · - a₀) (sphere (0 : ℂ) |r|) := fun z _ ↦ (hf z).sub (.const a₀ z)
  convert h.circleIntegrable_posLog_norm.sub h.circleIntegrable_log_norm using 1
  funext z
  change max 0 (-log ‖f z - a₀‖) = max 0 (log ‖f z - a₀‖) - log ‖f z - a₀‖
  rw [← max_sub_sub_right, zero_sub, sub_self, max_comm]

open MeasureTheory in
/-- On the angular domain where the reciprocal distance exists, its positive logarithm
is integrable, including when the circle contains coincidences with the target. -/
lemma circleIntegrable_posLog_norm_sub_inv (hf : Meromorphic f) (a : E)
    (ha : ∀ z, ∃ᶠ w in 𝓝[≠] z, (f w : WithTop E) ≠ a) (r : ℝ) :
    CircleIntegrableOn (fun z : {z : ℂ | f z ≠ a} ↦ log⁺ (Checked.inv ‖f z - a‖
      (norm_ne_zero_iff.mpr (sub_ne_zero.mpr z.property)).isUnit)) 0 r := by
  let S := {z : ℂ | f z ≠ a}
  let Z := sphere (0 : ℂ) |r| ∩ {z | f z = a}
  have hZ := finite_sphere_inter_setOf_eq hf ha r
  have hset : circleAngles S 0 r = Icc 0 (2 * π) ∩ (circleMap 0 r ⁻¹' Z)ᶜ := by
    ext θ
    simp [circleAngles, S, Z]
  have hmeas : MeasurableSet (circleAngles S 0 r) := hset ▸
    measurableSet_Icc.inter (hZ.measurableSet.preimage (measurable_circleMap _ _)).compl
  let F (θ : ℝ) := max 0 (-log ‖f (circleMap 0 r θ) - a‖)
  have H : IntegrableOn F (Icc 0 (2 * π)) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by positivity)).mp
      (circleIntegrable_neg_log_norm_sub hf a r)
  have hi := (integrableOn_iff_comap_subtypeVal hmeas).mp
    (H.mono_set (show circleAngles S 0 r ⊆ Icc 0 (2 * π) from inter_subset_left))
  change Integrable (fun θ : circleAngles S 0 r ↦ log⁺ (Checked.inv ‖f (circleMap 0 r θ.val) - a‖
    (norm_ne_zero_iff.mpr (sub_ne_zero.mpr θ.property.2)).isUnit)) _
  change Integrable (fun θ : circleAngles S 0 r ↦ F θ.val) _ at hi
  simpa only [posLog_apply, log_inv, F] using hi

/-!
## Elementary Properties of the Proximity Function
-/

/--
If two functions differ only on a discrete subset of the circle of radius `r ≠ 0`, then their
proximity functions agree at `r`.
-/
lemma proximity_congr_codiscreteWithin {f g : ℂ → E} {a : WithTop E} {r : ℝ}
    (hfg : f =ᶠ[codiscreteWithin (sphere 0 |r|)] g) (hr : r ≠ 0) {hf : Meromorphic f}
    {ha : ∀ z, ∃ᶠ w in 𝓝[≠] z, (f w : WithTop E) ≠ a} {hg : Meromorphic g}
    {hga : ∀ z, ∃ᶠ w in 𝓝[≠] z, (g w : WithTop E) ≠ a} :
    proximity f a hf ha r (fun e ↦ (hr e).elim) = proximity g a hg hga r (fun e ↦ (hr e).elim) := by
  induction a using WithTop.recTopCoe <;>
  · simp only [proximity_top_apply, proximity_coe]
    apply circleAverage_congr_codiscreteWithin _ hr
    filter_upwards [hfg] using by aesop

/--
If two functions differ only on a discrete set, then their proximity functions
agree, except perhaps at radius 0.
-/
lemma proximity_congr_codiscrete {f g : ℂ → E} {a : WithTop E} {r : ℝ}
    (hfg : f =ᶠ[codiscrete ℂ] g) (hr : r ≠ 0) {hf : Meromorphic f}
    {ha : ∀ z, ∃ᶠ w in 𝓝[≠] z, (f w : WithTop E) ≠ a} :
    proximity f a hf ha r (fun e ↦ (hr e).elim) = proximity g a (hf.congr_codiscrete hfg)
      (frequently_coe_ne_of_eventuallyEq_codiscrete hfg ha) r (fun e ↦ (hr e).elim) :=
  proximity_congr_codiscreteWithin (hfg.filter_mono (codiscreteWithin_mono (by tauto))) hr

/--
For finite values `a₀`, the proximity function `proximity f a₀` equals the proximity function for
the value zero of the shifted function `f - a₀`.
-/
lemma proximity_coe_eq_proximity_sub_const_zero {hf : Meromorphic f}
    {ha : ∀ z, ∃ᶠ w in 𝓝[≠] z, (f w : WithTop E) ≠ a₀} (r : ℝ)
    (hr : r = 0 → f 0 ≠ a₀) :
    proximity f a₀ hf ha r (fun h ↦ WithTop.coe_injective.ne_iff.mpr (hr h)) =
      proximity (f - fun _ ↦ a₀) 0 (hf.sub (.const a₀))
        (fun z ↦ frequently_coe_sub_const_ne_zero (ha z)) r
        (fun h ↦ WithTop.coe_injective.ne_iff.mpr (sub_ne_zero.mpr (hr h))) := by
  rw [proximity_coe, proximity_zero]
  rfl

/-- Proximity to zero is the angular integral of the norm of the genuine reciprocal,
evaluated only at angles whose images are nonzero. -/
theorem proximity_inv {f : ℂ → ℂ} (hf : Meromorphic f)
    (ha : ∀ z, ∃ᶠ w in 𝓝[≠] z, (f w : WithTop ℂ) ≠ 0) (r : ℝ) (hr : r = 0 → f 0 ≠ 0) :
    proximity f 0 hf ha r (fun h ↦ WithTop.coe_injective.ne_iff.mpr (hr h)) =
      (2 * π)⁻¹ • intervalIntegral.integralSubtypeOn
        (fun θ : {θ : ℝ | f (circleMap 0 r θ) ≠ 0} ↦
          log⁺ ‖Checked.inv (f (circleMap 0 r θ.val)) θ.property.isUnit‖) 0 (2 * π) := by
  change (2 * π)⁻¹ • intervalIntegral.integralSubtypeOn
    (fun θ : {θ : ℝ | f (circleMap 0 r θ) ≠ 0} ↦ log⁺ (Checked.inv ‖f (circleMap 0 r θ.val) - 0‖
      (norm_ne_zero_iff.mpr (sub_ne_zero.mpr θ.property)).isUnit)) 0 (2 * π) = _
  simp only [sub_zero, norm_inv]

/-- The difference between proximity to infinity and proximity to zero is the circle
average of the log norm on their common finite domain. -/
theorem proximity_sub_proximity_zero_eq_circleAverage {f : ℂ → ℂ} (hf : Meromorphic f)
    (ha : ∀ z, ∃ᶠ w in 𝓝[≠] z, (f w : WithTop ℂ) ≠ 0) (r : ℝ) (hr : r = 0 → f 0 ≠ 0) :
    proximity f ⊤ hf (frequently_coe_ne_top f) r -
      proximity f 0 hf ha r (fun h ↦ WithTop.coe_injective.ne_iff.mpr (hr h)) =
        circleAverage (log ‖f ·‖) 0 r := by
  rw [proximity_zero]
  change circleAverage (log⁺ ‖f ·‖) 0 r - _ = _
  rw [← circleAverage_sub]
  · congr 1
    funext z
    change max 0 (log ‖f z‖) - max 0 (-log ‖f z‖) = log ‖f z‖
    rcases le_total 0 (log ‖f z‖) with h | h
    · rw [max_eq_right h, max_eq_left (neg_nonpos.mpr h), sub_zero]
    · rw [max_eq_left h, max_eq_right (neg_nonneg.mpr h), zero_sub, neg_neg]
  · exact hf.meromorphicOn.circleIntegrable_posLog_norm
  · simpa only [sub_zero] using circleIntegrable_neg_log_norm_sub hf 0 r

/-- Negating an admissible radius leaves proximity unchanged. -/
theorem proximity_even {hf : Meromorphic f} {ha : ∀ z, ∃ᶠ w in 𝓝[≠] z, (f w : WithTop E) ≠ a}
    (r : ℝ) (hr : r = 0 → (f 0 : WithTop E) ≠ a) :
    proximity f a hf ha (-r) (fun h ↦ hr (neg_eq_zero.mp h)) = proximity f a hf ha r hr := by
  induction a using WithTop.recTopCoe <;> simp [proximity_top_apply, proximity_coe]

/--
The proximity function is non-negative.
-/
theorem proximity_nonneg {a : WithTop E} {hf : Meromorphic f}
    {ha : ∀ z, ∃ᶠ w in 𝓝[≠] z, (f w : WithTop E) ≠ a} (r : ℝ)
    (hr : r = 0 → (f 0 : WithTop E) ≠ a) : 0 ≤ proximity f a hf ha r hr := by
  induction a using WithTop.recTopCoe with
  | top => rw [proximity_top_apply]; exact circleAverage_nonneg_of_nonneg (fun _ _ ↦ posLog_nonneg)
  | coe a =>
    rw [proximity_coe]
    exact circleAverage_nonneg_of_nonneg (fun _ _ ↦ le_max_left _ _)

omit [NormedSpace ℂ E] in
@[simp] lemma circleAverage_posLog_norm_const (c : E) (r : ℝ) :
    circleAverage (fun _ : ℂ ↦ log⁺ ‖c‖) 0 r = log⁺ ‖c‖ := circleAverage_const _ _ _

lemma proximity_const {c : E} {r : ℝ} {hf : Meromorphic fun _ : ℂ ↦ c} :
    (proximity (fun _ ↦ c) ⊤ hf) r = log⁺ ‖c‖ := by
  simp

/--
If `f` is meromorphic and continuous, that is, entire (`MeromorphicAt.analyticAt`), then its
proximity function at `⊤` is continuous.
-/
@[fun_prop] theorem continuous_proximity_top (hc : Continuous f) {hf : Meromorphic f} :
    Continuous (proximity f ⊤ hf) := by
  rw [proximity_top]
  fun_prop

/-!
## Behaviour under Arithmetic Operations
-/

/--
The proximity function of a sum of functions at `⊤` is less than or equal to the sum of the
proximity functions of the summand, plus `log` of the number of summands.
-/
theorem proximity_sum_top_le {α : Type*} (s : Finset α) (f : α → ℂ → E)
    (hf : ∀ a ∈ s, Meromorphic (f a)) :
    proximity (∑ a ∈ s, f a) ⊤ (Meromorphic.sum hf) ≤
      ∑ a ∈ s.attach, (proximity (f a) ⊤ (hf a a.2)) + (fun _ ↦ log s.card) := by
  simp only [proximity_top_apply, Finset.sum_apply]
  rw [Finset.sum_attach s fun a ↦ circleAverage (log⁺ ‖f a ·‖) 0]
  intro r
  have h₂f : ∀ i ∈ s, CircleIntegrable (log⁺ ‖f i ·‖) 0 r :=
    fun i hi ↦ MeromorphicOn.circleIntegrable_posLog_norm (fun x _ ↦ hf i hi x)
  simp only [Pi.add_apply, Finset.sum_apply]
  calc circleAverage (log⁺ ‖∑ c ∈ s, f c ·‖) 0 r
    _ ≤ circleAverage (∑ c ∈ s, log⁺ ‖f c ·‖ + log s.card) 0 r := by
      apply circleAverage_mono
      · apply (Meromorphic.fun_sum hf).meromorphicOn.circleIntegrable_posLog_norm
      · fun_prop
      · intro x hx
        rw [add_comm]
        apply posLog_norm_sum_le
    _ = ∑ c ∈ s, circleAverage (log⁺ ‖f c ·‖) 0 r + log s.card := by
      nth_rw 2 [← circleAverage_const (log s.card) 0 r]
      rw [← circleAverage_sum h₂f, ← circleAverage_add (CircleIntegrable.sum s h₂f)
        (circleIntegrable_const (log s.card) 0 r)]
      congr 1
      ext x
      simp

/--
The proximity function of `f + g` at `⊤` is less than or equal to the sum of the proximity functions
of `f` and `g`, plus `log 2` (where `2` is the number of summands).
-/
theorem proximity_add_top_le {f₁ f₂ : ℂ → E} (h₁f₁ : Meromorphic f₁) (h₁f₂ : Meromorphic f₂) :
    proximity (f₁ + f₂) ⊤ (h₁f₁.add h₁f₂) ≤
      (proximity f₁ ⊤ h₁f₁) + (proximity f₂ ⊤ h₁f₂) + (fun _ ↦ log 2) := by
  have h := proximity_sum_top_le Finset.univ ![f₁, f₂] fun i _ ↦ by fin_cases i <;> assumption
  simp only [proximity_top_apply] at h ⊢
  rw [Finset.sum_attach Finset.univ fun i ↦ circleAverage (log⁺ ‖![f₁, f₂] i ·‖) 0] at h
  simpa using h

/--
The proximity function `f * g` at `⊤` is less than or equal to the sum of the proximity functions of
`f` and `g`, respectively.
-/
theorem proximity_mul_top_le {f₁ f₂ : ℂ → ℂ} (h₁f₁ : Meromorphic f₁) (h₁f₂ : Meromorphic f₂) :
    proximity (f₁ * f₂) ⊤ (h₁f₁.mul h₁f₂) ≤ proximity f₁ ⊤ h₁f₁ + proximity f₂ ⊤ h₁f₂ := by
  calc proximity (f₁ * f₂) ⊤ (h₁f₁.mul h₁f₂)
    _ = circleAverage (fun x ↦ log⁺ (‖f₁ x‖ * ‖f₂ x‖)) 0 := by
      simp
    _ ≤ circleAverage (fun x ↦ log⁺ ‖f₁ x‖ + log⁺ ‖f₂ x‖) 0 := by
      intro r
      apply circleAverage_mono
      · simp_rw [← norm_mul]
        exact ((h₁f₁.meromorphicOn (s := sphere (0 : ℂ) |r|)).mul
          h₁f₂.meromorphicOn).circleIntegrable_posLog_norm
      · apply (MeromorphicOn.circleIntegrable_posLog_norm h₁f₁.meromorphicOn).add
          (MeromorphicOn.circleIntegrable_posLog_norm h₁f₂.meromorphicOn)
      · exact fun _ _ ↦ posLog_mul
    _ = circleAverage (log⁺ ‖f₁ ·‖) 0 + circleAverage (log⁺ ‖f₂ ·‖) 0 := by
      ext r
      apply circleAverage_add
      · exact MeromorphicOn.circleIntegrable_posLog_norm h₁f₁.meromorphicOn
      · exact MeromorphicOn.circleIntegrable_posLog_norm h₁f₂.meromorphicOn
    _ = proximity f₁ ⊤ h₁f₁ + proximity f₂ ⊤ h₁f₂ := by simp

/--
The proximity function `f * g` at `0` is less than or equal to the sum of the proximity functions of
`f` and `g`, respectively.
-/
theorem proximity_mul_zero_le {f₁ f₂ : ℂ → ℂ}
    (h₁f₁ : Meromorphic f₁) (h₂f₁ : ∀ z, ∃ᶠ w in 𝓝[≠] z, (f₁ w : WithTop ℂ) ≠ 0)
    (h₁f₂ : Meromorphic f₂) (h₂f₂ : ∀ z, ∃ᶠ w in 𝓝[≠] z, (f₂ w : WithTop ℂ) ≠ 0)
    {h : ∀ z, ∃ᶠ w in 𝓝[≠] z, ((f₁ * f₂) w : WithTop ℂ) ≠ 0} (r : ℝ)
    (hr₁ : r = 0 → f₁ 0 ≠ 0) (hr₂ : r = 0 → f₂ 0 ≠ 0) :
    proximity (f₁ * f₂) 0 (h₁f₁.mul h₁f₂) h r
        (fun e ↦ WithTop.coe_injective.ne_iff.mpr (mul_ne_zero (hr₁ e) (hr₂ e))) ≤
      proximity f₁ 0 h₁f₁ h₂f₁ r (fun e ↦ WithTop.coe_injective.ne_iff.mpr (hr₁ e)) +
      proximity f₂ 0 h₁f₂ h₂f₂ r (fun e ↦ WithTop.coe_injective.ne_iff.mpr (hr₂ e)) := by
  simp only [proximity_zero]
  have hi {f : ℂ → ℂ} (hf : Meromorphic f) :
      CircleIntegrable (fun y ↦ max 0 (-log ‖f y‖)) 0 r := by
    simpa only [sub_zero] using circleIntegrable_neg_log_norm_sub hf 0 r
  rw [← circleAverage_add (hi h₁f₁) (hi h₁f₂)]
  apply circleAverage_mono (hi (h₁f₁.mul h₁f₂)) ((hi h₁f₁).add (hi h₁f₂))
  intro y _
  change max 0 (-log ‖f₁ y * f₂ y‖) ≤ max 0 (-log ‖f₁ y‖) + max 0 (-log ‖f₂ y‖)
  by_cases h₁ : f₁ y = 0
  · simp [h₁]
  by_cases h₂ : f₂ y = 0
  · simp [h₂]
  rw [norm_mul, log_mul (norm_ne_zero_iff.mpr h₁) (norm_ne_zero_iff.mpr h₂), neg_add_rev]
  apply max_le (add_nonneg (le_max_left _ _) (le_max_left _ _))
  simpa only [add_comm] using
    add_le_add (le_max_right 0 (-log ‖f₁ y‖)) (le_max_right 0 (-log ‖f₂ y‖))

@[simp] lemma circleAverage_nat_mul_posLog_norm (f : ℂ → ℂ) (n : ℕ) (r : ℝ) :
    circleAverage (fun z ↦ (n : ℝ) * log⁺ ‖f z‖) 0 r =
      (n : ℝ) * circleAverage (log⁺ ‖f ·‖) 0 r := by
  simpa only [smul_eq_mul] using
    (circleAverage_fun_smul (a := (n : ℝ)) (f := fun z ↦ log⁺ ‖f z‖) (c := 0) (R := r))

/--
For natural numbers `n`, the proximity function of `f ^ n` at `⊤` equals `n` times the proximity
function of `f` at `⊤`.
-/
theorem proximity_pow_top {f : ℂ → ℂ} {n : ℕ} (hf : Meromorphic f)
    {hf' : Meromorphic (f ^ n)} :
    proximity (f ^ n) ⊤ hf' = n • (proximity f ⊤ hf) := by
  ext x
  simp [nsmul_eq_mul]

/--
For natural numbers `n`, the proximity function of `f ^ n` at `0` equals `n` times the proximity
function of `f` at `0`.
-/
theorem proximity_pow_zero {f : ℂ → ℂ} {n : ℕ} (hf : Meromorphic f)
    (ha : ∀ z, ∃ᶠ w in 𝓝[≠] z, (f w : WithTop ℂ) ≠ 0) {hf' : Meromorphic (f ^ n)}
    {ha' : ∀ z, ∃ᶠ w in 𝓝[≠] z, ((f ^ n) w : WithTop ℂ) ≠ 0} (r : ℝ) (hr : r = 0 → f 0 ≠ 0) :
    proximity (f ^ n) 0 hf' ha' r
        (fun e ↦ WithTop.coe_injective.ne_iff.mpr (pow_ne_zero _ (hr e))) =
      n * proximity f 0 hf ha r (fun e ↦ WithTop.coe_injective.ne_iff.mpr (hr e)) := by
  simp only [proximity_zero, Pi.pow_apply, norm_pow, log_pow, ← mul_neg]
  rw [← smul_eq_mul, ← circleAverage_fun_smul]
  congr 1
  funext y
  simpa only [mul_zero, smul_eq_mul] using
    (mul_max_of_nonneg 0 (-log ‖f y‖) (n.cast_nonneg (α := ℝ))).symm

end ValueDistribution
