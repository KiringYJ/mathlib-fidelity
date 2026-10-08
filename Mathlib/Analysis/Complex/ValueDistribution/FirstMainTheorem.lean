/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Analysis.Complex.ValueDistribution.CharacteristicFunction
public import Mathlib.Analysis.Meromorphic.RCLike

/-!
# The First Main Theorem of Value Distribution Theory

The First Main Theorem of Value Distribution Theory is a two-part statement, establishing invariance
of the characteristic function `characteristic f ⊤` under modifications of `f`.

- If `f` is meromorphic on the complex plane, then the characteristic functions for the value `⊤` of
  the function `f` and `f⁻¹` agree up to a constant, see Proposition 2.1 on p. 168 of [Lang,
  *Introduction to Complex Hyperbolic Spaces*][MR886677].

- If `f` is meromorphic on the complex plane, then the characteristic functions for the value `⊤` of
  the function `f` and `f - const` agree up to a constant, see Proposition 2.2 on p. 168 of [Lang,
  *Introduction to Complex Hyperbolic Spaces*][MR886677]

See Section VI.2 of [Lang, *Introduction to Complex Hyperbolic Spaces*][MR886677] or Section 1.1 of
[Noguchi-Winkelmann, *Nevanlinna Theory in Several Complex Variables and Diophantine
Approximation*][MR3156076] for a detailed discussion.
-/

public section
namespace ValueDistribution

open Asymptotics Filter Function.locallyFinsuppWithin MeromorphicOn Metric Real
open scoped Topology

section FirstPart

variable {f : ℂ → ℂ} {R : ℝ}

/-!
## First Part of the First Main Theorem
-/

/--
Helper lemma for the first part of the First Main Theorem: Given a meromorphic function `f` of
finite order everywhere, compute difference between the characteristic functions of `f` and of its
inverse.
-/
lemma characteristic_sub_characteristic_inv (h : Meromorphic f)
    (h₀ : ∀ z (hz : z ∈ Set.univ), meromorphicOrderAt f z (h.meromorphicOn z hz) ≠ ⊤) :
    characteristic f ⊤ h - characteristic f⁻¹ ⊤ h.inv =
      circleAverage (log ‖f ·‖) 0 - (divisor f Set.univ h₀).logCounting := by
  have ha z : ∃ᶠ w in 𝓝[≠] z, (f w : WithTop ℂ) ≠ 0 :=
    (frequently_coe_ne_zero_iff (h z)).2 (h₀ z (Set.mem_univ z))
  calc characteristic f ⊤ h - characteristic f⁻¹ ⊤ h.inv
  _ = proximity f ⊤ h - proximity f⁻¹ ⊤ h.inv -
      (logCounting f⁻¹ ⊤ h.inv - logCounting f ⊤ h) := by
    unfold characteristic
    ring
  _ = circleAverage (log ‖f ·‖) 0 - (logCounting f⁻¹ ⊤ h.inv - logCounting f ⊤ h) := by
    rw [proximity_sub_proximity_inv_eq_circleAverage h]
  _ = circleAverage (log ‖f ·‖) 0 - (logCounting f 0 h ha - logCounting f ⊤ h) := by
    rw [logCounting_inv h ha]
  _ = circleAverage (log ‖f ·‖) 0 - (divisor f Set.univ h₀).logCounting := by
    rw [log_counting_zero_sub_logCounting_top h h₀]

/--
Helper lemma for the first part of the First Main Theorem: If `f` has finite order at the origin,
then away from zero, the difference between the characteristic functions of `f` and `f⁻¹` equals
the logarithm of the norm of the trailing coefficient `meromorphicTrailingCoeffAt f 0`.
-/
lemma characteristic_sub_characteristic_inv_of_ne_zero
    (hf : Meromorphic f) (h₀ : meromorphicOrderAt f 0 ≠ ⊤) (hR : R ≠ 0) :
    (characteristic f ⊤ hf) R - (characteristic f⁻¹ ⊤ hf.inv) R =
      log ‖meromorphicTrailingCoeffAt f 0 h₀‖ := by
  have h₀' : ∀ z (hz : z ∈ Set.univ), meromorphicOrderAt f z (hf.meromorphicOn z hz) ≠ ⊤ :=
    fun z _ ↦ hf.exists_meromorphicOrderAt_ne_top_iff_forall.1 ⟨0, h₀⟩ z
  calc (characteristic f ⊤ hf) R - (characteristic f⁻¹ ⊤ hf.inv) R
  _ = (characteristic f ⊤ hf - characteristic f⁻¹ ⊤ hf.inv) R := rfl
  _ = circleAverage (log ‖f ·‖) 0 R - (divisor f Set.univ h₀').logCounting R := by
    rw [characteristic_sub_characteristic_inv hf h₀', Pi.sub_apply]
  _ = log ‖meromorphicTrailingCoeffAt f 0 h₀‖ := by
    rw [logCounting_divisor_eq_circleAverage_sub_const hf h₀' hR, sub_sub_cancel]

/--
Helper lemma for the first part of the First Main Theorem: At 0, the difference between the
characteristic functions of `f` and `f⁻¹` equals `log ‖f 0‖`.
-/
lemma characteristic_sub_characteristic_inv_at_zero (h : Meromorphic f) :
    (characteristic f ⊤ h) 0 - (characteristic f⁻¹ ⊤ h.inv) 0 = log ‖f 0‖ := by
  have e := congrFun (proximity_sub_proximity_inv_eq_circleAverage h) 0
  simp only [Pi.sub_apply, circleAverage_zero] at e
  simpa only [characteristic, Pi.add_apply, logCounting_eval_zero, add_zero] using e

/--
First part of the First Main Theorem, quantitative version: If `f` is meromorphic on the complex
plane and has finite order at the origin, then the difference between the characteristic functions
of `f` and `f⁻¹` is bounded by an explicit constant.
-/
theorem characteristic_sub_characteristic_inv_le (hf : Meromorphic f)
    (h₀ : meromorphicOrderAt f 0 ≠ ⊤) :
    |(characteristic f ⊤ hf) R - (characteristic f⁻¹ ⊤ hf.inv) R|
      ≤ max |log ‖f 0‖| |log ‖meromorphicTrailingCoeffAt f 0 h₀‖| := by
  by_cases h : R = 0
  · simp [h, characteristic_sub_characteristic_inv_at_zero hf]
  · simp [characteristic_sub_characteristic_inv_of_ne_zero hf h₀ h]

/--
First part of the First Main Theorem, qualitative version: If `f` is meromorphic on the complex
plane, then the characteristic functions of `f` and `f⁻¹` agree asymptotically up to a bounded
function.
-/
theorem isBigO_characteristic_sub_characteristic_inv (h : Meromorphic f) :
    (characteristic f ⊤ h - characteristic f⁻¹ ⊤ h.inv) =O[atTop] (1 : ℝ → ℝ) := by
  by_cases h₀ : meromorphicOrderAt f 0 = ⊤
  · -- Trivial case: `f` vanishes on a codiscrete set, and so does `f⁻¹`
    have h₁ : f =ᶠ[codiscrete ℂ] fun _ ↦ 0 := by
      filter_upwards [h.eventuallyEq_zero_of_meromorphicOrderAt_eq_top h₀] with z hz
      simpa using hz
    have h₂ : f⁻¹ =ᶠ[codiscrete ℂ] fun _ ↦ 0 := by
      filter_upwards [h₁] with z hz
      simp [hz]
    refine (isBigO_zero (1 : ℝ → ℝ) atTop).congr' ?_ EventuallyEq.rfl
    filter_upwards [eventually_ne_atTop 0] with R hR
    rw [Pi.sub_apply, characteristic_congr_codiscrete h₁ hR, characteristic_congr_codiscrete h₂ hR,
      sub_self]
  · exact isBigO_of_le' (c := max |log ‖f 0‖| |log ‖meromorphicTrailingCoeffAt f 0 h₀‖|) _
      (fun R ↦ by simpa using characteristic_sub_characteristic_inv_le h h₀ (R := R))

end FirstPart

section SecondPart

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {a₀ : E} {f : ℂ → E}

/-!
## Second Part of the First Main Theorem
-/

/--
Second part of the First Main Theorem of Value Distribution Theory, quantitative version: If `f` is
meromorphic on the complex plane, then the characteristic functions (for value `⊤`) of `f` and
`f - a₀` differ at most by `log⁺ ‖a₀‖ + log 2`.
-/
theorem abs_characteristic_sub_characteristic_shift_le {r : ℝ} (h : Meromorphic f) :
    |(characteristic f ⊤) r - (characteristic (f · - a₀) ⊤) r| ≤ log⁺ ‖a₀‖ + log 2 := by
  have h₁f : CircleIntegrable (fun x ↦ log⁺ ‖f x‖) 0 r :=
    h.meromorphicOn.circleIntegrable_posLog_norm
  have h₂f : CircleIntegrable (fun x ↦ log⁺ ‖f x - a₀‖) 0 r := by
    apply MeromorphicOn.circleIntegrable_posLog_norm
    fun_prop
  rw [← Pi.sub_apply, characteristic_sub_characteristic_eq_proximity_sub_proximity h]
  simp only [proximity_top, Pi.sub_apply, ← circleAverage_sub h₁f h₂f]
  apply le_trans abs_circleAverage_le_circleAverage_abs
  apply circleAverage_mono_on_of_le_circle
  · apply (h₁f.sub h₂f).abs
  · intro θ hθ
    simp only [Pi.abs_apply, Pi.sub_apply]
    by_cases h : 0 ≤ log⁺ ‖f θ‖ - log⁺ ‖f θ - a₀‖
    · simpa [abs_of_nonneg h, sub_le_iff_le_add, add_comm (log⁺ ‖a₀‖ + log 2), ← add_assoc]
        using (posLog_norm_add_le (f θ - a₀) a₀)
    · simp only [abs_of_nonpos (le_of_not_ge h), neg_sub, tsub_le_iff_right,
        add_comm (log⁺ ‖a₀‖ + log 2), ← add_assoc]
      convert! posLog_norm_add_le (-f θ) a₀ using 2
      · rw [← norm_neg]
        abel_nf
      · simp

/--
Second part of the First Main Theorem of Value Distribution Theory, qualitative version: If `f` is
meromorphic on the complex plane, then the characteristic functions for the value `⊤` of the
function `f` and `f - a₀` agree asymptotically up to a bounded function.
-/
theorem isBigO_characteristic_sub_characteristic_shift (h : Meromorphic f) :
    (characteristic f ⊤ - characteristic (f · - a₀) ⊤) =O[atTop] (1 : ℝ → ℝ) :=
  isBigO_of_le' (c := log⁺ ‖a₀‖ + log 2) _
    (fun R ↦ by simpa using abs_characteristic_sub_characteristic_shift_le h)

end SecondPart

end ValueDistribution
