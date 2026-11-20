/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic
public import Mathlib.Analysis.Complex.ValueDistribution.Proximity.Basic

/-!
# The Characteristic Function of Value Distribution Theory

This file defines the "characteristic function" attached to a meromorphic function defined on the
complex plane.  Also known as "Nevanlinna Height", this is one of the three main functions used in
Value Distribution Theory.

The characteristic function plays a role analogous to the height function in number theory: both
measure the "complexity" of objects. For rational functions, the characteristic function grows like
the degree times the logarithm, much like the logarithmic height in number theory reflects the
degree of an algebraic number.

See Section VI.2 of [Lang, *Introduction to Complex Hyperbolic Spaces*][MR886677] or Section 1.1 of
[Noguchi-Winkelmann, *Nevanlinna Theory in Several Complex Variables and Diophantine
Approximation*][MR3156076] for a detailed discussion.

### TODO

- Characterize rational functions in terms of the growth rate of their characteristic function, as
  discussed in Theorem 2.6 on p. 170 of [Lang, *Introduction to Complex Hyperbolic
  Spaces*][MR886677].
-/

@[expose] public section

open Filter Real Set
open scoped Topology

namespace ValueDistribution

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f g : ℂ → E} {a : WithTop E}

variable (f a) in
/--
The Characteristic Function of Value Distribution Theory

If `f : ℂ → E` is meromorphic and `a : WithTop E` is a value that `f` takes on no punctured
neighborhood, the characteristic function of `f` is defined as the sum of two terms: the proximity
function, which quantifies how close `f` gets to `a` on the circle `∣z∣ = r`, and the logarithmic
counting function, which counts the number times that `f` attains the value `a` inside the disk
`∣z∣ ≤ r`, weighted by multiplicity.  Its domain is that of `ValueDistribution.logCounting`: for
`a = ⊤`, the condition `ha` holds for every function and is supplied by default, so that the
characteristic function for the poles is evaluated as `(characteristic f ⊤) r`.
-/
noncomputable def characteristic (hf : Meromorphic f := by fun_prop_default)
    (ha : ∀ z, ∃ᶠ w in 𝓝[≠] z, (f w : WithTop E) ≠ a := by
      value_distribution_frequently_ne) (r : ℝ)
    (hr : r = 0 → (f 0 : WithTop E) ≠ a := by value_distribution_radius) : ℝ :=
  proximity f a hf ha r hr + logCounting f a hf ha r

/-!
## Elementary Properties
-/

/--
If two functions differ only on a discrete set, then their characteristic functions agree, except
perhaps at radius 0.
-/
theorem characteristic_congr_codiscrete {r : ℝ} (hfg : f =ᶠ[codiscrete ℂ] g) (hr : r ≠ 0)
    {hf : Meromorphic f} {ha : ∀ z, ∃ᶠ w in 𝓝[≠] z, (f w : WithTop E) ≠ a} :
    characteristic f a hf ha r = characteristic g a (hf.congr_codiscrete hfg)
      (frequently_coe_ne_of_eventuallyEq_codiscrete hfg ha) r := by
  simp only [characteristic, proximity_congr_codiscrete hfg hr,
    logCounting_congr_codiscrete hfg]

/--
The difference between the characteristic functions for the poles of `f` and `f - const` simplifies
to the difference between the proximity functions.
-/
@[simp]
lemma characteristic_sub_characteristic_eq_proximity_sub_proximity (h : Meromorphic f) (a₀ : E)
    {h' : Meromorphic (f · - a₀)} :
    characteristic f ⊤ h - characteristic (f · - a₀) ⊤ h' =
      proximity f ⊤ h - proximity (f · - a₀) ⊤ h' := by
  have e : logCounting (f · - a₀) ⊤ h' = logCounting f ⊤ h := logCounting_sub_const h
  ext r
  change (_ + logCounting f ⊤ h _ r) - (_ + logCounting (f · - a₀) ⊤ h' _ r) = _
  rw [e, add_sub_add_right_eq_sub]
  rfl

/--
The characteristic function is even.
-/
theorem characteristic_even {hf : Meromorphic f}
    {ha : ∀ z, ∃ᶠ w in 𝓝[≠] z, (f w : WithTop E) ≠ a} :
    ∀ r (hr : r = 0 → (f 0 : WithTop E) ≠ a),
      characteristic f a hf ha (-r) (fun e ↦ hr (neg_eq_zero.mp e)) =
        characteristic f a hf ha r hr := by
  intro r hr
  rw [characteristic, characteristic, proximity_even r hr, logCounting_even r]

/--
For `1 ≤ r`, the characteristic function is non-negative.
-/
theorem characteristic_nonneg {r : ℝ} {hf : Meromorphic f}
    {ha : ∀ z, ∃ᶠ w in 𝓝[≠] z, (f w : WithTop E) ≠ a} (hr : 1 ≤ r) :
    0 ≤ characteristic f a hf ha r :=
  add_nonneg (proximity_nonneg r (fun e ↦ (by linarith : r ≠ 0) e |>.elim)) (logCounting_nonneg hr)

/--
The characteristic function is asymptotically non-negative.
-/
theorem characteristic_eventually_nonneg {hf : Meromorphic f}
    {ha : ∀ z, ∃ᶠ w in 𝓝[≠] z, (f w : WithTop E) ≠ a} :
    ∀ᶠ r : ℝ in Filter.atTop,
      ∀ hr : r = 0 → (f 0 : WithTop E) ≠ a, 0 ≤ characteristic f a hf ha r hr := by
  filter_upwards [Filter.eventually_ge_atTop 1] with r hr _
  exact characteristic_nonneg hr

/-!
## Behaviour under Arithmetic Operations
-/

/--
For `1 ≤ r`, the characteristic function of a sum `∑ a, f a` at `⊤` is less than or equal to the sum
of the characteristic functions of `f ·`, plus `log s.card`.
-/
theorem characteristic_sum_top_le {α : Type*} (s : Finset α) (f : α → ℂ → E) {r : ℝ}
    (hf : ∀ a ∈ s, Meromorphic (f a)) (hr : 1 ≤ r) :
    (characteristic (∑ a ∈ s, f a) ⊤ (Meromorphic.sum hf)) r ≤
      ∑ a ∈ s.attach, (characteristic (f a) ⊤ (hf a a.2)) r + log s.card := by
  have h₁ := proximity_sum_top_le s f hf r
  have h₂ := logCounting_sum_top_le s f hf hr
  simp only [Pi.add_apply, Finset.sum_apply] at h₁
  simp only [characteristic, Finset.sum_add_distrib]
  linarith

/--
Asymptotically, the characteristic function of a sum `∑ a, f a` at `⊤` is less than or equal to the
sum of the characteristic functions of `f ·`.
-/
theorem characteristic_sum_top_eventuallyLE {α : Type*} (s : Finset α) (f : α → ℂ → E)
    (hf : ∀ a ∈ s, Meromorphic (f a)) :
    characteristic (∑ a ∈ s, f a) ⊤ (Meromorphic.sum hf)
      ≤ᶠ[Filter.atTop] ∑ a ∈ s.attach, characteristic (f a) ⊤ (hf a a.2) + fun _ ↦ log s.card := by
  filter_upwards [Filter.eventually_ge_atTop 1] with r hr
  simpa using characteristic_sum_top_le s f hf hr

/--
For `1 ≤ r`, the characteristic function of `f + g` at `⊤` is less than or equal to the sum of the
characteristic functions of `f` and `g`, respectively, plus `log 2` (where `2` is the number of
summands).
-/
theorem characteristic_add_top_le {f₁ f₂ : ℂ → E} {r : ℝ} (h₁f₁ : Meromorphic f₁)
    (h₁f₂ : Meromorphic f₂) (hr : 1 ≤ r) :
    (characteristic (f₁ + f₂) ⊤ (h₁f₁.add h₁f₂)) r ≤
      (characteristic f₁ ⊤ h₁f₁) r + (characteristic f₂ ⊤ h₁f₂) r + log 2 := by
  have h₁ := proximity_add_top_le h₁f₁ h₁f₂ r
  have h₂ := logCounting_add_top_le h₁f₁ h₁f₂ hr
  simp only [Pi.add_apply] at h₁ h₂
  simp only [characteristic]
  linarith

/--
Asymptotically, the characteristic function of `f + g` at `⊤` is less than or equal to the sum of
the characteristic functions of `f` and `g`, respectively.
-/
theorem characteristic_add_top_eventuallyLE {f₁ f₂ : ℂ → E} (h₁f₁ : Meromorphic f₁)
    (h₁f₂ : Meromorphic f₂) :
    characteristic (f₁ + f₂) ⊤ (h₁f₁.add h₁f₂)
      ≤ᶠ[Filter.atTop] characteristic f₁ ⊤ h₁f₁ + characteristic f₂ ⊤ h₁f₂ + fun _ ↦ log 2 := by
  filter_upwards [Filter.eventually_ge_atTop 1] with r hr
    using characteristic_add_top_le h₁f₁ h₁f₂ hr

/--
For `1 ≤ r`, the characteristic function for the zeros of `f * g` is less than or equal to the sum
of the characteristic functions for the zeros of `f` and `g`, respectively.
-/
theorem characteristic_mul_zero_le {f₁ f₂ : ℂ → ℂ} {r : ℝ} (hr : 1 ≤ r)
    (h₁f₁ : Meromorphic f₁) (h₂f₁ : ∀ z, ∃ᶠ w in 𝓝[≠] z, (f₁ w : WithTop ℂ) ≠ 0)
    (h₁f₂ : Meromorphic f₂) (h₂f₂ : ∀ z, ∃ᶠ w in 𝓝[≠] z, (f₂ w : WithTop ℂ) ≠ 0)
    {h : ∀ z, ∃ᶠ w in 𝓝[≠] z, ((f₁ * f₂) w : WithTop ℂ) ≠ 0} :
    characteristic (f₁ * f₂) 0 (h₁f₁.mul h₁f₂) h r ≤
      characteristic f₁ 0 h₁f₁ h₂f₁ r + characteristic f₂ 0 h₁f₂ h₂f₂ r := by
  simp only [characteristic]
  rw [add_add_add_comm]
  exact add_le_add
    (proximity_mul_zero_le h₁f₁ h₂f₁ h₁f₂ h₂f₂ r
      (fun e ↦ (by linarith : r ≠ 0) e |>.elim) (fun e ↦ (by linarith : r ≠ 0) e |>.elim))
    (logCounting_mul_zero_le hr h₁f₁ h₂f₁ h₁f₂ h₂f₂)

/--
Asymptotically, the characteristic function for the zeros of `f * g` is less than or equal to the
sum of the characteristic functions for the zeros of `f` and `g`, respectively.
-/
theorem characteristic_mul_zero_eventuallyLE {f₁ f₂ : ℂ → ℂ}
    (h₁f₁ : Meromorphic f₁) (h₂f₁ : ∀ z, ∃ᶠ w in 𝓝[≠] z, (f₁ w : WithTop ℂ) ≠ 0)
    (h₁f₂ : Meromorphic f₂) (h₂f₂ : ∀ z, ∃ᶠ w in 𝓝[≠] z, (f₂ w : WithTop ℂ) ≠ 0)
    {h : ∀ z, ∃ᶠ w in 𝓝[≠] z, ((f₁ * f₂) w : WithTop ℂ) ≠ 0} :
    ∀ᶠ r : ℝ in Filter.atTop, ∀ hr : r ≠ 0,
      characteristic (f₁ * f₂) 0 (h₁f₁.mul h₁f₂) h r ≤
        characteristic f₁ 0 h₁f₁ h₂f₁ r + characteristic f₂ 0 h₁f₂ h₂f₂ r := by
  filter_upwards [Filter.eventually_ge_atTop 1] with r hr _
  exact characteristic_mul_zero_le hr h₁f₁ h₂f₁ h₁f₂ h₂f₂

/--
For `1 ≤ r`, the characteristic function for the poles of `f * g` is less than or equal to the sum
of the characteristic functions for the poles of `f` and `g`, respectively.
-/
theorem characteristic_mul_top_le {f₁ f₂ : ℂ → ℂ} {r : ℝ} (hr : 1 ≤ r)
    (h₁f₁ : Meromorphic f₁) (h₁f₂ : Meromorphic f₂) :
    (characteristic (f₁ * f₂) ⊤ (h₁f₁.mul h₁f₂)) r ≤
      (characteristic f₁ ⊤ h₁f₁ + characteristic f₂ ⊤ h₁f₂) r := by
  simp only [characteristic, Pi.add_apply]
  rw [add_add_add_comm]
  exact add_le_add (proximity_mul_top_le h₁f₁ h₁f₂ r) (logCounting_mul_top_le hr h₁f₁ h₁f₂)

/--
Asymptotically, the characteristic function for the poles of `f * g` is less than or equal to the
sum of the characteristic functions for the poles of `f` and `g`, respectively.
-/
theorem characteristic_mul_top_eventuallyLE {f₁ f₂ : ℂ → ℂ}
    (h₁f₁ : Meromorphic f₁) (h₁f₂ : Meromorphic f₂) :
    characteristic (f₁ * f₂) ⊤ (h₁f₁.mul h₁f₂)
      ≤ᶠ[Filter.atTop] characteristic f₁ ⊤ h₁f₁ + characteristic f₂ ⊤ h₁f₂ := by
  filter_upwards [Filter.eventually_ge_atTop 1]
    using fun _ hr ↦ characteristic_mul_top_le hr h₁f₁ h₁f₂

/--
For natural numbers `n`, the characteristic function for the zeros of `f ^ n` equals `n` times the
characteristic counting function for the zeros of `f`.
-/
theorem characteristic_pow_zero {f : ℂ → ℂ} {n : ℕ} (hf : Meromorphic f)
    (ha : ∀ z, ∃ᶠ w in 𝓝[≠] z, (f w : WithTop ℂ) ≠ 0) {hf' : Meromorphic (f ^ n)}
    {ha' : ∀ z, ∃ᶠ w in 𝓝[≠] z, ((f ^ n) w : WithTop ℂ) ≠ 0} (r : ℝ)
    (hr : r = 0 → f 0 ≠ 0) :
    characteristic (f ^ n) 0 hf' ha' r
        (fun e ↦ WithTop.coe_injective.ne_iff.mpr (pow_ne_zero _ (hr e))) =
      n * characteristic f 0 hf ha r (fun e ↦ WithTop.coe_injective.ne_iff.mpr (hr e)) := by
  rw [characteristic, characteristic, proximity_pow_zero hf ha r hr, logCounting_pow_zero hf ha]
  simp [mul_add, nsmul_eq_mul]

/--
For natural numbers `n`, the characteristic function for the poles of `f ^ n` equals `n` times the
characteristic function for the poles of `f`.
-/
@[simp]
theorem characteristic_pow_top {f : ℂ → ℂ} {n : ℕ} (hf : Meromorphic f)
    {hf' : Meromorphic (f ^ n)} :
    characteristic (f ^ n) ⊤ hf' = n • characteristic f ⊤ hf := by
  ext r
  have hp := congrFun (proximity_pow_top (n := n) hf (hf' := hf')) r
  have hc := congrFun (logCounting_pow_top (n := n) hf (hf' := hf')) r
  simpa only [characteristic, Pi.smul_apply, nsmul_add] using congrArg₂ (· + ·) hp hc

end ValueDistribution
