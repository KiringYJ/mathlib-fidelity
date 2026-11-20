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

/-- The characteristics at infinity and zero differ by the circle mean of the log norm
minus the logarithmic counting function of the divisor. -/
lemma characteristic_sub_characteristic_zero (hf : Meromorphic f)
    (h₀ : ∀ z (hz : z ∈ Set.univ), meromorphicOrderAt f z (hf.meromorphicOn z hz) ≠ ⊤)
    (hr : R = 0 → f 0 ≠ 0) :
    characteristic f ⊤ hf (frequently_coe_ne_top f) R -
      characteristic f 0 hf (fun z ↦ (frequently_coe_ne_zero_iff (hf z)).mpr (h₀ z trivial)) R
        (fun e ↦ WithTop.coe_injective.ne_iff.mpr (hr e)) =
      circleAverage (log ‖f ·‖) 0 R - (divisor f Set.univ h₀).logCounting R := by
  let ha z := (frequently_coe_ne_zero_iff (hf z)).mpr (h₀ z trivial)
  have hp := proximity_sub_proximity_zero_eq_circleAverage hf ha R hr
  have hc := congrFun (log_counting_zero_sub_logCounting_top hf h₀) R
  simp only [Pi.sub_apply] at hc
  unfold characteristic
  linarith

/-- At nonzero radius the difference is the logarithm of the norm of the leading coefficient. -/
lemma characteristic_sub_characteristic_zero_of_ne_zero (hf : Meromorphic f (_root_.id : ℂ → ℂ))
    (ha : ∀ z : ℂ, ∃ᶠ w in 𝓝[≠] z, (f w : WithTop ℂ) ≠ 0) (hR : R ≠ 0) :
    characteristic f ⊤ hf (frequently_coe_ne_top f) R -
      characteristic f 0 hf ha R (fun e ↦ (hR e).elim) =
      log ‖meromorphicTrailingCoeffAt f (0 : ℂ)
        ((frequently_coe_ne_zero_iff (hf (0 : ℂ))).mp (ha 0))‖ := by
  have hfin (z : ℂ) (_ : z ∈ Set.univ) := (frequently_coe_ne_zero_iff (hf z)).mp (ha z)
  have hc := characteristic_sub_characteristic_zero hf hfin (R := R) (fun e ↦ (hR e).elim)
  rw [logCounting_divisor_eq_circleAverage_sub_const hf hfin hR, sub_sub_cancel] at hc
  exact hc

/-- Radius zero is admissible for the zero target precisely when the center value is nonzero. -/
lemma characteristic_sub_characteristic_zero_at_zero (hf : Meromorphic f)
    (ha : ∀ z, ∃ᶠ w in 𝓝[≠] z, (f w : WithTop ℂ) ≠ 0) (h₀ : f 0 ≠ 0) :
    characteristic f ⊤ hf (frequently_coe_ne_top f) 0 -
      characteristic f 0 hf ha 0 (fun _ ↦ WithTop.coe_injective.ne_iff.mpr h₀) = log ‖f 0‖ := by
  have he := proximity_sub_proximity_zero_eq_circleAverage hf ha 0 (fun _ ↦ h₀)
  simpa only [characteristic, circleAverage_zero, logCounting_eval_zero, add_zero] using he

/-- The difference between the two characteristics has an explicit uniform bound on their
common radius domain. -/
theorem characteristic_sub_characteristic_zero_le (hf : Meromorphic f (_root_.id : ℂ → ℂ))
    (ha : ∀ z : ℂ, ∃ᶠ w in 𝓝[≠] z, (f w : WithTop ℂ) ≠ 0) (hr : R = 0 → f 0 ≠ 0) :
    |characteristic f ⊤ hf (frequently_coe_ne_top f) R -
      characteristic f 0 hf ha R (fun e ↦ WithTop.coe_injective.ne_iff.mpr (hr e))| ≤
      max |log ‖f 0‖| |log ‖meromorphicTrailingCoeffAt f (0 : ℂ)
        ((frequently_coe_ne_zero_iff (hf (0 : ℂ))).mp (ha 0))‖| := by
  by_cases hR : R = 0
  · subst R
    rw [characteristic_sub_characteristic_zero_at_zero hf ha (hr rfl)]
    exact le_max_left _ _
  · rw [characteristic_sub_characteristic_zero_of_ne_zero hf ha hR]
    exact le_max_right _ _

/-- At large positive radii the zero and pole characteristics differ by a bounded function. -/
theorem isBigO_characteristic_sub_characteristic_zero (hf : Meromorphic f)
    (ha : ∀ z : ℂ, ∃ᶠ w in 𝓝[≠] z, (f w : WithTop ℂ) ≠ 0) :
    (fun r : Set.Ioi (0 : ℝ) ↦ characteristic f ⊤ hf (frequently_coe_ne_top f) r -
      characteristic f 0 hf ha r (fun e ↦ (r.property.ne' e).elim)) =O[comap Subtype.val atTop]
        (1 : Set.Ioi (0 : ℝ) → ℝ) := by
  apply isBigO_of_le' (c := |log ‖meromorphicTrailingCoeffAt f (0 : ℂ)
    ((frequently_coe_ne_zero_iff (hf (0 : ℂ))).mp (ha 0))‖|)
  intro r
  simp [characteristic_sub_characteristic_zero_of_ne_zero hf ha r.property.ne']

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
    exact (h.fun_sub (.const a₀)).meromorphicOn.circleIntegrable_posLog_norm
  have hshift := congrFun (characteristic_sub_characteristic_eq_proximity_sub_proximity h a₀
    (h' := h.fun_sub (.const a₀))) r
  change |(_ : ℝ) - _| ≤ _
  rw [show characteristic f ⊤ h (frequently_coe_ne_top f) r -
      characteristic (f · - a₀) ⊤ (h.fun_sub (.const a₀)) _ r = _ from hshift]
  simp only [Pi.sub_apply, proximity_top_apply, ← circleAverage_sub h₁f h₂f]
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
