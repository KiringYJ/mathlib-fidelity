/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Stefan Kebekus
-/

module

public import Mathlib.Analysis.Complex.ValueDistribution.Proximity.IntegralPresentation
public import Mathlib.Analysis.Complex.ValueDistribution.CharacteristicFunction
public import Mathlib.Analysis.Meromorphic.RCLike

/-!
# Cartan's Formula

This file establishes Cartan's classic formula,
`ValueDistribution.characteristic_top_eq_circleAverage_add_circleAverage`, describing the
characteristic function `characteristic f ⊤ r` of a meromorphic function `f` that is not constant
near the origin as a sum of two circle averages,

- `circleAverage (fun a ↦ logCounting f a h (ha a) r) 0 1` and
- `circleAverage (fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0 (hf a)‖) 0 1`, where
  `hf a` states that `f - a` has finite order at the origin and `ha a`, derived from it by
  `ValueDistribution.frequently_coe_ne_of_meromorphicOrderAt_sub_ne_top`, that `f` takes the value
  `a` on no punctured neighborhood.

As a corollary, Cartan's formula implies the (surprisingly non-trivial) fact that the
characteristic function is monotone; this is stated in
`ValueDistribution.characteristic_monotoneOn`.

This file also establishes circle integrability of the function
`a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0 (hf a)‖` and computes values of the circle
average.

## References

See Section VI.2 of [Lang, *Introduction to Complex Hyperbolic Spaces*][MR886677] for a detailed
discussion.
-/

public section

open Filter Metric Real Set
open scoped Topology

variable {f : ℂ → ℂ} {R : ℝ}

namespace ValueDistribution

/-!
## Terms in Cartan's formula
-/

private lemma log_trailingCoeff_eq_zero_on_unitSphere {a : ℂ} (hf : MeromorphicAt f 0)
    (h : 0 < meromorphicOrderAt f 0 hf) (ha : a ∈ sphere 0 |1|)
    {h' : meromorphicOrderAt (f · - a) 0 ≠ ⊤} :
    log ‖meromorphicTrailingCoeffAt (f · - a) 0 h'‖ = 0 := by
  classical
  have ha₀ : a ≠ 0 := by
    rintro rfl
    simp at ha
  have hlt : meromorphicOrderAt (fun _ : ℂ ↦ -a) 0 (.const (-a) 0) < meromorphicOrderAt f 0 hf := by
    rw [meromorphicOrderAt_const]
    simpa [ha₀] using h
  simp_rw [sub_eq_neg_add]
  rw [MeromorphicAt.meromorphicTrailingCoeffAt_fun_add_eq_left_of_lt (.const (-a) 0) hf hlt,
    meromorphicTrailingCoeffAt_const]
  simp [mem_sphere_zero_iff_norm.1 ha]

private lemma eventuallyEq_log_trailingCoeff_of_meromorphicOrderAt_eq_zero (h₁ : MeromorphicAt f 0)
    (h₂ : meromorphicOrderAt f 0 h₁ = 0) (hfin : ∀ a, meromorphicOrderAt (f · - a) 0 ≠ ⊤) :
    (log ‖meromorphicTrailingCoeffAt f 0 (h₂.trans_ne WithTop.coe_ne_top) - ·‖)
      =ᶠ[codiscreteWithin (sphere 0 |1|)]
      fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0 (hfin a)‖ := by
  obtain ⟨g, h₁g, h₂g, h₃g⟩ := (meromorphicOrderAt_eq_int_iff h₁ (n := 0)).1 h₂
  have hg := h₁g.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE h₂g h₃g
    (h₂f := h₂.trans_ne WithTop.coe_ne_top)
  filter_upwards [compl_singleton_mem_codiscreteWithin (g 0)] with a ha
  have ha' : g 0 - a ≠ 0 := sub_ne_zero.2 (Ne.symm ha)
  rw [hg, (h₁g.sub analyticAt_const).meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE (n := 0)
    ha' (by filter_upwards [h₃g] with z hz; simp [hz]), Pi.sub_apply]

/--
Circle integrability of the term `fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0 (hfin a)‖`
that appears in Cartan's formula.
-/
theorem circleIntegrable_log_meromorphicTrailingCoeffAt (hf : MeromorphicAt f 0)
    (hfin : ∀ a, meromorphicOrderAt (f · - a) 0 ≠ ⊤) :
    CircleIntegrable (fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0 (hfin a)‖) 0 1 := by
  rcases lt_trichotomy (meromorphicOrderAt f 0 hf) 0 with hneg | hzero | hpos
  · refine (circleIntegrable_congr fun a ha ↦ ?_).2 (circleIntegrable_const
      (log ‖meromorphicTrailingCoeffAt f 0 hneg.ne_top‖) 0 1)
    rw [MeromorphicAt.meromorphicTrailingCoeffAt_fun_sub_eq_left_of_lt hf (.const a 0)]
    rw [meromorphicOrderAt_const]
    aesop
  · apply CircleIntegrable.congr_codiscreteWithin
      (eventuallyEq_log_trailingCoeff_of_meromorphicOrderAt_eq_zero hf hzero hfin)
    simpa [norm_sub_rev] using circleIntegrable_log_norm_sub_const 1
  · apply (circleIntegrable_congr _).2 (circleIntegrable_const 0 0 1)
    exact fun _ ha ↦ log_trailingCoeff_eq_zero_on_unitSphere hf hpos ha

/--
Circle average of the function `fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0 (hfin a)‖` that
appears in Cartan's formula, in the case where `f` has a zero at the origin.
-/
theorem circleAverage_log_norm_meromorphicTrailingCoeffAt_of_meromorphicOrderAt_pos
    (hf : MeromorphicAt f 0) (h : 0 < meromorphicOrderAt f 0 hf)
    (hfin : ∀ a, meromorphicOrderAt (f · - a) 0 ≠ ⊤) :
    circleAverage (fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0 (hfin a)‖) 0 1 = 0 :=
  circleAverage_const_on_circle (fun _ hx ↦ log_trailingCoeff_eq_zero_on_unitSphere hf h hx)

/--
Circle average of the function `fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0 (hfin a)‖` that
appears in Cartan's formula, in the case where `f` has order zero at the origin.
-/
theorem circleAverage_log_norm_meromorphicTrailingCoeffAt_of_meromorphicOrderAt_eq_zero
    (hf : MeromorphicAt f 0) (h : meromorphicOrderAt f 0 hf = 0)
    (hfin : ∀ a, meromorphicOrderAt (f · - a) 0 ≠ ⊤) :
    circleAverage (fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0 (hfin a)‖) 0 1
      = log⁺ ‖meromorphicTrailingCoeffAt f 0 (h.trans_ne WithTop.coe_ne_top)‖ := by
  rw [← circleAverage_congr_codiscreteWithin
    (eventuallyEq_log_trailingCoeff_of_meromorphicOrderAt_eq_zero hf h hfin) zero_ne_one.symm]
  simp_rw [norm_sub_rev]
  rw [circleAverage_log_norm_sub_const_eq_posLog]

/--
Circle average of the function `fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0 (hfin a)‖` that
appears in Cartan's formula, in the case where `f` has a pole at the origin.
-/
theorem circleAverage_log_norm_meromorphicTrailingCoeffAt_of_meromorphicOrderAt_lt_zero
    (hf : MeromorphicAt f 0) (h : meromorphicOrderAt f 0 hf < 0)
    (hfin : ∀ a, meromorphicOrderAt (f · - a) 0 ≠ ⊤) :
    circleAverage (fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0 (hfin a)‖) 0 1
      = log ‖meromorphicTrailingCoeffAt f 0 h.ne_top‖ := by
  rw [circleAverage_congr_sphere (f₂ := fun _ ↦ log ‖meromorphicTrailingCoeffAt f 0 h.ne_top‖),
    circleAverage_const]
  intro a ha
  simp only
  congr 2
  rw [MeromorphicAt.meromorphicTrailingCoeffAt_fun_sub_eq_left_of_lt hf (.const a 0)]
  rw [meromorphicOrderAt_const]
  aesop

/--
If `g` is meromorphic on `ℂ` and `g - a₀` has finite order at some point, then `g` takes the value
`a₀` on no punctured neighborhood of any point, so that `logCounting g a₀` is defined.
-/
theorem frequently_coe_ne_of_meromorphicOrderAt_sub_ne_top {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {g : ℂ → E} (h : Meromorphic g) {a₀ : E} {x : ℂ}
    (hx : meromorphicOrderAt (g · - a₀) x ≠ ⊤) (z : ℂ) :
    ∃ᶠ w in 𝓝[≠] z, (g w : WithTop E) ≠ a₀ :=
  (frequently_coe_ne_coe_iff (h z)).2
    ((h.fun_sub (.const a₀)).exists_meromorphicOrderAt_ne_top_iff_forall.1 ⟨x, hx⟩ z)

/- Specialized Jensen-type identity -/
private lemma logCounting_add_log_trailingCoeff_eq_circleAverage_add_logCounting_top
    (h : Meromorphic f) (hR : R ≠ 0) (a : ℂ) (ha : meromorphicOrderAt (f · - a) 0 ≠ ⊤) :
    logCounting f a h (frequently_coe_ne_of_meromorphicOrderAt_sub_ne_top h ha) R +
        log ‖meromorphicTrailingCoeffAt (f · - a) 0 ha‖ =
      circleAverage (log ‖f · - a‖) 0 R + (logCounting f ⊤ h) R := by
  have h' : Meromorphic (f · - a) := by fun_prop
  have h₀ : ∀ z (hz : z ∈ univ), meromorphicOrderAt (f · - a) z (h'.meromorphicOn z hz) ≠ ⊤ :=
    fun z _ ↦ h'.exists_meromorphicOrderAt_ne_top_iff_forall.1 ⟨0, ha⟩ z
  have e₁ : logCounting f a h (frequently_coe_ne_of_meromorphicOrderAt_sub_ne_top h ha) =
      (MeromorphicOn.divisor (f · - a) univ h₀)⁺.logCounting :=
    logCounting_coe _ _
  have e₂ : logCounting f ⊤ h = (MeromorphicOn.divisor (f · - a) univ h₀)⁻.logCounting := by
    rw [← MeromorphicOn.poleDivisor_eq_negPart_divisor h₀, ← logCounting_top h']
    exact (logCounting_sub_const h).symm
  have e₃ := Function.locallyFinsuppWithin.logCounting_divisor_eq_circleAverage_sub_const h' h₀ hR
  rw [← posPart_sub_negPart (MeromorphicOn.divisor (f · - a) univ h₀), map_sub,
    Pi.sub_apply] at e₃
  have e₄ : meromorphicTrailingCoeffAt (f · - a) 0 (h₀ 0 (mem_univ 0)) =
      meromorphicTrailingCoeffAt (f · - a) 0 ha := rfl
  rw [e₄] at e₃
  rw [e₁, e₂]
  linarith

/- If `f - c` has infinite order at the origin, then `f` is the constant `c` on a codiscrete set. -/
private lemma eventuallyEq_const_of_meromorphicOrderAt_sub_eq_top (h : Meromorphic f) {c : ℂ}
    (hc : meromorphicOrderAt (f · - c) 0 = ⊤) : f =ᶠ[codiscrete ℂ] fun _ ↦ c := by
  have h' : Meromorphic (f · - c) := by fun_prop
  filter_upwards [h'.eventuallyEq_zero_of_meromorphicOrderAt_eq_top hc] with z hz
  simpa [sub_eq_zero] using hz

/--
Circle integrability of the term
`fun a ↦ logCounting f a h (frequently_coe_ne_of_meromorphicOrderAt_sub_ne_top h (hfin a)) R` that
appears in Cartan's formula.
-/
theorem circleIntegrable_logCounting (h : Meromorphic f)
    (hfin : ∀ a, meromorphicOrderAt (f · - a) 0 ≠ ⊤) :
    CircleIntegrable (fun a ↦ logCounting f a h
      (frequently_coe_ne_of_meromorphicOrderAt_sub_ne_top h (hfin a)) R) 0 1 := by
  by_cases hR : R = 0
  · simp [hR, ValueDistribution.logCounting_eval_zero]
  convert circleIntegrable_circleAverage_log_norm_sub h |>.add
    (circleIntegrable_const ((logCounting f ⊤ h) R) 0 1) |>.sub
    (circleIntegrable_log_meromorphicTrailingCoeffAt (h 0) hfin)
  simpa using eq_sub_of_add_eq
    (logCounting_add_log_trailingCoeff_eq_circleAverage_add_logCounting_top h hR _ (hfin _))

/-!
## Cartan's formula
-/

/--
**Cartan's formula** with the additive constant written explicitly as a circle average of the
logarithm of the first nonzero Laurent coefficient of `f - a` at the origin. The formula concerns a
function `f` that is not constant near the origin, so that `f - a` has finite order at the origin
for every `a`.

See `circleIntegrable_logCounting` and `circleIntegrable_log_meromorphicTrailingCoeffAt` for the
facts that the summands are actually circle integrable.
-/
theorem characteristic_top_eq_circleAverage_add_circleAverage (h : Meromorphic f)
    (hfin : ∀ a, meromorphicOrderAt (f · - a) 0 ≠ ⊤) (hR : R ≠ 0) :
    (characteristic f ⊤ h) R = circleAverage (fun a ↦ logCounting f a h
        (frequently_coe_ne_of_meromorphicOrderAt_sub_ne_top h (hfin a)) R) 0 1
      + circleAverage (fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0 (hfin a)‖) 0 1 := calc
  (characteristic f ⊤ h) R
      = circleAverage (fun a ↦ circleAverage (log ‖f · - a‖) 0 R + (logCounting f ⊤ h) R) 0 1 := by
      simp only [characteristic, Pi.add_apply]
      rw [← circleAverage_circleAverage_eq_proximity_top h,
        circleAverage_fun_add (circleIntegrable_circleAverage_log_norm_sub h)
          (circleIntegrable_const ((logCounting f ⊤ h) R) 0 1), circleAverage_const]
    _ = circleAverage (fun a ↦ logCounting f a h
          (frequently_coe_ne_of_meromorphicOrderAt_sub_ne_top h (hfin a)) R) 0 1
          + circleAverage (fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0 (hfin a)‖) 0 1 := by
      rw [← circleAverage_add (circleIntegrable_logCounting h hfin)
        (circleIntegrable_log_meromorphicTrailingCoeffAt (h 0) hfin), circleAverage_congr_sphere]
      intro a ha
      simp [logCounting_add_log_trailingCoeff_eq_circleAverage_add_logCounting_top h hR a (hfin a)]

/--
**Cartan's formula** in the case where `0 < meromorphicOrderAt f 0`.
-/
theorem characteristic_top_eq_circleAverage_of_meromorphicOrderAt_pos
    (h₁f : Meromorphic f) (hfin : ∀ a, meromorphicOrderAt (f · - a) 0 ≠ ⊤)
    (h₂f : 0 < meromorphicOrderAt f 0) (hR : R ≠ 0) :
    (characteristic f ⊤ h₁f) R = circleAverage (fun a ↦ logCounting f a h₁f
      (frequently_coe_ne_of_meromorphicOrderAt_sub_ne_top h₁f (hfin a)) R) 0 1 := by
  rw [characteristic_top_eq_circleAverage_add_circleAverage h₁f hfin hR]
  simp [circleAverage_log_norm_meromorphicTrailingCoeffAt_of_meromorphicOrderAt_pos (h₁f 0) h₂f
    hfin]

/--
Qualitative version of **Cartan's formula**: Away from the point `0`, the difference between
`characteristic f ⊤` and the circle average of the logarithmic counting functions `logCounting f a`
over the unit circle is constant. This qualitative version of Cartan's formula exists because the
specific value of the constant does not matter in practice.
-/
theorem characteristic_top_eq_circleAverage_add_const (h : Meromorphic f)
    (hfin : ∀ a, meromorphicOrderAt (f · - a) 0 ≠ ⊤) :
    ∃ const, ∀ R ≠ 0, (characteristic f ⊤ h) R = circleAverage (fun a ↦ logCounting f a h
      (frequently_coe_ne_of_meromorphicOrderAt_sub_ne_top h (hfin a)) R) 0 1 + const :=
  ⟨circleAverage (fun a ↦ log ‖meromorphicTrailingCoeffAt (f · - a) 0 (hfin a)‖) 0 1,
    fun _ hr ↦ characteristic_top_eq_circleAverage_add_circleAverage h hfin hr⟩

/-!
## Application: Monotonicity of the Characteristic Function
-/

/--
The characteristic function is monotone on `(0, ∞)`. This result is surprisingly non-trivial, given
that the proximity function is not monotone in general.
-/
theorem characteristic_monotoneOn (h : Meromorphic f) :
    MonotoneOn (characteristic f ⊤ h) (Set.Ioi 0) := by
  intro a ha b hb hab
  by_cases hfin : ∀ a, meromorphicOrderAt (f · - a) 0 ≠ ⊤
  · rw [characteristic_top_eq_circleAverage_add_circleAverage h hfin ha.ne',
      characteristic_top_eq_circleAverage_add_circleAverage h hfin hb.ne']
    gcongr <;> try exact circleIntegrable_logCounting h hfin
    exact logCounting_monotoneOn ha hb hab
  -- Trivial case: `f` is constant on a codiscrete set
  push Not at hfin
  obtain ⟨c, hc⟩ := hfin
  have hfc := eventuallyEq_const_of_meromorphicOrderAt_sub_eq_top h hc
  rw [characteristic_congr_codiscrete hfc ha.ne', characteristic_congr_codiscrete hfc hb.ne']
  simp [characteristic]

end ValueDistribution
