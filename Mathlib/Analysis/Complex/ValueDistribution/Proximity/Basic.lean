/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Algebra.Order.WithTop.Untop0
public import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
public import Mathlib.MeasureTheory.Integral.CircleAverage


/-!
# The Proximity Function of Value Distribution Theory

This file defines the "proximity function" attached to a meromorphic function defined on the complex
plane.  Also known as the `Nevanlinna Proximity Function`, this is one of the three main functions
used in Value Distribution Theory.

The proximity function is a logarithmically weighted measure quantifying how well a meromorphic
function `f` approximates the constant function `a` on the circle of radius `R` in the complex
plane.  The definition ensures that large values correspond to good approximation.

The proximity function takes a meromorphic function `f` and a value `a` that `f` takes on no
punctured neighborhood, the arguments of the logarithmic counting function `logCounting` and of the
characteristic function.  For a finite value `a`, `f` then takes `a` at only finitely many points of
each circle (`ValueDistribution.finite_sphere_inter_setOf_eq`), and the integrand
`log⁺ ‖f · - a‖⁻¹` is circle integrable (`ValueDistribution.circleIntegrable_posLog_norm_sub_inv`),
so neither the convention `(0 : ℝ)⁻¹ = 0` nor the zero circle average of a function that is not
circle integrable affects a value at a radius `r ≠ 0`.  Integrability alone would not suffice: for
a function equal to `a`, the integrand is `0` by that convention, while the proximity function is
infinite.  For a
meromorphic function and a radius `r ≠ 0`, the identity theorem shows that `f ≠ a` almost
everywhere on the circle of radius `r` exactly when `f` takes `a` on no punctured neighborhood, so
these are the exact arguments among meromorphic functions.  For other functions the condition
depends on the radius; they are outside the setting of this file, which has no counting function
for them, and their circle averages remain available as such.

At radius `0` the circle average is the value of the integrand at the center
(`ValueDistribution.proximity_coe_eval_zero`, `ValueDistribution.proximity_top_eval_zero`), and a
negative radius gives the value at its absolute value (`ValueDistribution.proximity_even`); these
values are conventions, as for `logCounting`.

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

variable (f a) in
/--
The Proximity Function of Value Distribution Theory

If `f : ℂ → E` is meromorphic (`_hf`) and `a : WithTop E` is a value that `f` takes on no
punctured neighborhood (`_ha`), the proximity function is a logarithmically weighted measure
quantifying how well `f` approximates the constant function `a` on the circle of radius `R` in the
complex plane.  In the special case where `a = ⊤`, it quantifies how well `f` approximates infinity;
there `_ha` holds for every function and is supplied by default.  These are the arguments of
`logCounting`; the definition does not use the proofs.

Both proofs precede the radius, so the proximity function for the poles is evaluated as
`(proximity f ⊤) r`.
-/
noncomputable def proximity (_hf : Meromorphic f := by fun_prop_default)
    (_ha : ∀ z, ∃ᶠ w in 𝓝[≠] z, (f w : WithTop E) ≠ a := by
      first
      | exact ValueDistribution.frequently_coe_ne_top _
      | fail "the function must take the value on no punctured neighborhood; only for ⊤ is \
          this supplied by default") :
    ℝ → ℝ := by
  by_cases h : a = ⊤
  · exact circleAverage (log⁺ ‖f ·‖) 0
  · exact circleAverage (log⁺ ‖f · - a.untop₀‖⁻¹) 0

/-- Expand the definition of `proximity f a₀` in case where `a₀` is finite. -/
lemma proximity_coe {hf : Meromorphic f} {ha : ∀ z, ∃ᶠ w in 𝓝[≠] z, (f w : WithTop E) ≠ a₀} :
    proximity f a₀ hf ha = circleAverage (log⁺ ‖f · - a₀‖⁻¹) 0 := by
  simp [proximity]

/--
Expand the definition of `proximity f a₀` in case where `a₀` is zero.
-/
lemma proximity_zero {hf : Meromorphic f} {ha : ∀ z, ∃ᶠ w in 𝓝[≠] z, (f w : WithTop E) ≠ 0} :
    proximity f 0 hf ha = circleAverage (log⁺ ‖f ·‖⁻¹) 0 := by
  simp [proximity]

/--
For complex-valued functions, expand the definition of `proximity f a₀` in case where `a₀` is zero.
This is a simple variant of `proximity_zero` defined above.
-/
lemma proximity_zero_of_complexValued {f : ℂ → ℂ} {hf : Meromorphic f}
    {ha : ∀ z, ∃ᶠ w in 𝓝[≠] z, (f w : WithTop ℂ) ≠ 0} :
    proximity f 0 hf ha = circleAverage (log⁺ ‖f⁻¹ ·‖) 0 := by
  simp [proximity]

/--
Expand the definition of `proximity f a` in case where `a₀ = ⊤`.
-/
lemma proximity_top {hf : Meromorphic f} :
    proximity f ⊤ hf = circleAverage (log⁺ ‖f ·‖) 0 := by
  simp [proximity]

/--
At radius `0`, the proximity function at a finite value is the integrand at the center.
-/
@[simp] lemma proximity_coe_eval_zero {hf : Meromorphic f}
    {ha : ∀ z, ∃ᶠ w in 𝓝[≠] z, (f w : WithTop E) ≠ a₀} :
    proximity f a₀ hf ha 0 = log⁺ ‖f 0 - a₀‖⁻¹ := by
  simp [proximity_coe, circleAverage_zero]

/--
At radius `0`, the proximity function for the poles is the integrand at the center.
-/
@[simp] lemma proximity_top_eval_zero {hf : Meromorphic f} :
    (proximity f ⊤ hf) 0 = log⁺ ‖f 0‖ := by
  simp [proximity_top, circleAverage_zero]

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

/--
The integrand of the proximity function at a finite value is circle integrable on every circle for
every meromorphic function.  At `⊤` this is `MeromorphicOn.circleIntegrable_posLog_norm`.
-/
lemma circleIntegrable_posLog_norm_sub_inv (hf : Meromorphic f) (a₀ : E) (r : ℝ) :
    CircleIntegrable (fun z ↦ log⁺ ‖f z - a₀‖⁻¹) 0 r := by
  have h : MeromorphicOn (f · - a₀) (sphere 0 |r|) := fun z _ ↦ (hf z).sub (.const a₀ z)
  convert h.circleIntegrable_posLog_norm.sub h.circleIntegrable_log_norm using 1
  ext z
  simp [← posLog_sub_posLog_inv]

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
    proximity f a hf ha r = proximity g a hg hga r := by
  by_cases h : a = ⊤
  all_goals
    simp only [proximity, h, ↓reduceDIte]
    apply circleAverage_congr_codiscreteWithin _ hr
    filter_upwards [hfg] using by aesop

/--
If two functions differ only on a discrete set, then their proximity functions
agree, except perhaps at radius 0.
-/
lemma proximity_congr_codiscrete {f g : ℂ → E} {a : WithTop E} {r : ℝ}
    (hfg : f =ᶠ[codiscrete ℂ] g) (hr : r ≠ 0) {hf : Meromorphic f}
    {ha : ∀ z, ∃ᶠ w in 𝓝[≠] z, (f w : WithTop E) ≠ a} :
    proximity f a hf ha r = proximity g a (hf.congr_codiscrete hfg)
      (frequently_coe_ne_of_eventuallyEq_codiscrete hfg ha) r :=
  proximity_congr_codiscreteWithin (hfg.filter_mono (codiscreteWithin_mono (by tauto))) hr

/--
For finite values `a₀`, the proximity function `proximity f a₀` equals the proximity function for
the value zero of the shifted function `f - a₀`.
-/
lemma proximity_coe_eq_proximity_sub_const_zero {hf : Meromorphic f}
    {ha : ∀ z, ∃ᶠ w in 𝓝[≠] z, (f w : WithTop E) ≠ a₀} :
    proximity f a₀ hf ha = proximity (f - fun _ ↦ a₀) 0 (hf.sub (.const a₀))
      fun z ↦ frequently_coe_sub_const_ne_zero (ha z) := by
  simp [proximity]

/--
For complex-valued `f`, establish a simple relation between the proximity functions of `f` and of
`f⁻¹`.
-/
theorem proximity_inv {f : ℂ → ℂ} (hf : Meromorphic f)
    (ha : ∀ z, ∃ᶠ w in 𝓝[≠] z, (f w : WithTop ℂ) ≠ 0) {hf' : Meromorphic f⁻¹} :
    proximity f⁻¹ ⊤ hf' = proximity f 0 hf ha := by
  simp [proximity_zero, proximity_top]

/--
For complex-valued `f`, the difference between `proximity f ⊤` and `proximity f⁻¹ ⊤` is the circle
average of `log ‖f ·‖`.
-/
theorem proximity_sub_proximity_inv_eq_circleAverage {f : ℂ → ℂ} (h₁f : Meromorphic f) :
    proximity f ⊤ h₁f - proximity f⁻¹ ⊤ h₁f.inv = circleAverage (log ‖f ·‖) 0 := by
  ext R
  simp only [proximity, ↓reduceDIte, Pi.inv_apply, norm_inv, Pi.sub_apply]
  rw [← circleAverage_sub]
  · simp_rw [← posLog_sub_posLog_inv, Pi.sub_def]
  · apply h₁f.meromorphicOn.circleIntegrable_posLog_norm
  · simp_rw [← norm_inv]
    apply h₁f.inv.meromorphicOn.circleIntegrable_posLog_norm

/--
The proximity function is even.
-/
theorem proximity_even {hf : Meromorphic f} {ha : ∀ z, ∃ᶠ w in 𝓝[≠] z, (f w : WithTop E) ≠ a} :
    (proximity f a hf ha).Even := by
  intro r
  by_cases h : a = ⊤ <;> simp [proximity, h]

/--
The proximity function is non-negative.
-/
theorem proximity_nonneg {a : WithTop E} {hf : Meromorphic f}
    {ha : ∀ z, ∃ᶠ w in 𝓝[≠] z, (f w : WithTop E) ≠ a} :
    0 ≤ proximity f a hf ha := by
  by_cases h : a = ⊤ <;>
  · intro r
    simpa [proximity, h] using circleAverage_nonneg_of_nonneg (fun x _ ↦ posLog_nonneg)

@[simp] lemma proximity_const {c : E} {r : ℝ} {hf : Meromorphic fun _ : ℂ ↦ c} :
    (proximity (fun _ ↦ c) ⊤ hf) r = log⁺ ‖c‖ := by
  simp [proximity, circleAverage_const]

/--
If `f` is meromorphic and continuous, that is, entire (`MeromorphicAt.analyticAt`), then its
proximity function at `⊤` is continuous.
-/
@[fun_prop] theorem continuous_proximity_top (hc : Continuous f) {hf : Meromorphic f} :
    Continuous (proximity f ⊤ hf) := by
  simp only [proximity, reduceDIte]
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
  simp only [proximity_top, Finset.sum_apply]
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
  simp only [proximity_top] at h ⊢
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
      simp [proximity]
    _ ≤ circleAverage (fun x ↦ log⁺ ‖f₁ x‖ + log⁺ ‖f₂ x‖) 0 := by
      intro r
      apply circleAverage_mono
      · simp_rw [← norm_mul]
        apply MeromorphicOn.circleIntegrable_posLog_norm
        fun_prop
      · apply (MeromorphicOn.circleIntegrable_posLog_norm h₁f₁.meromorphicOn).add
          (MeromorphicOn.circleIntegrable_posLog_norm h₁f₂.meromorphicOn)
      · exact fun _ _ ↦ posLog_mul
    _ = circleAverage (log⁺ ‖f₁ ·‖) 0 + circleAverage (log⁺ ‖f₂ ·‖) 0 := by
      ext r
      apply circleAverage_add
      · exact MeromorphicOn.circleIntegrable_posLog_norm h₁f₁.meromorphicOn
      · exact MeromorphicOn.circleIntegrable_posLog_norm h₁f₂.meromorphicOn
    _ = proximity f₁ ⊤ h₁f₁ + proximity f₂ ⊤ h₁f₂ := by simp [proximity]

/--
The proximity function `f * g` at `0` is less than or equal to the sum of the proximity functions of
`f` and `g`, respectively.
-/
theorem proximity_mul_zero_le {f₁ f₂ : ℂ → ℂ}
    (h₁f₁ : Meromorphic f₁) (h₂f₁ : ∀ z, ∃ᶠ w in 𝓝[≠] z, (f₁ w : WithTop ℂ) ≠ 0)
    (h₁f₂ : Meromorphic f₂) (h₂f₂ : ∀ z, ∃ᶠ w in 𝓝[≠] z, (f₂ w : WithTop ℂ) ≠ 0)
    {h : ∀ z, ∃ᶠ w in 𝓝[≠] z, ((f₁ * f₂) w : WithTop ℂ) ≠ 0} :
    proximity (f₁ * f₂) 0 (h₁f₁.mul h₁f₂) h ≤
      proximity f₁ 0 h₁f₁ h₂f₁ + proximity f₂ 0 h₁f₂ h₂f₂ := by
  have := proximity_mul_top_le h₁f₁.inv h₁f₂.inv
  simp only [proximity_top] at this
  simpa only [proximity_zero_of_complexValued, mul_inv] using this

/--
For natural numbers `n`, the proximity function of `f ^ n` at `⊤` equals `n` times the proximity
function of `f` at `⊤`.
-/
@[simp] theorem proximity_pow_top {f : ℂ → ℂ} {n : ℕ} (hf : Meromorphic f)
    {hf' : Meromorphic (f ^ n)} :
    proximity (f ^ n) ⊤ hf' = n • (proximity f ⊤ hf) := by
  ext x
  simp [proximity, ← smul_eq_mul, circleAverage_fun_smul]

/--
For natural numbers `n`, the proximity function of `f ^ n` at `0` equals `n` times the proximity
function of `f` at `0`.
-/
theorem proximity_pow_zero {f : ℂ → ℂ} {n : ℕ} (hf : Meromorphic f)
    (ha : ∀ z, ∃ᶠ w in 𝓝[≠] z, (f w : WithTop ℂ) ≠ 0) {hf' : Meromorphic (f ^ n)}
    {ha' : ∀ z, ∃ᶠ w in 𝓝[≠] z, ((f ^ n) w : WithTop ℂ) ≠ 0} :
    proximity (f ^ n) 0 hf' ha' = n • (proximity f 0 hf ha) := by
  have := proximity_pow_top (n := n) hf.inv (hf' := hf.inv.pow (n := n))
  simp only [proximity_top] at this
  simpa only [proximity_zero_of_complexValued, inv_pow] using this

end ValueDistribution
