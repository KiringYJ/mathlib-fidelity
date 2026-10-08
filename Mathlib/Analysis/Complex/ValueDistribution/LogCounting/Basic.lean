/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Complex.JensenFormula

/-!
# The Logarithmic Counting Function of Value Distribution Theory

For nontrivially normed fields `𝕜`, this file defines the logarithmic counting function of a
meromorphic function defined on `𝕜`.  Also known as the `Nevanlinna counting function`, this is one
of the three main functions used in Value Distribution Theory.

The logarithmic counting function of a meromorphic function `f` is a logarithmically weighted
measure of the number of times the function `f` takes a given value `a` within the disk `∣z∣ ≤ r`,
taking multiplicities into account.

See Section VI.1 of [Lang, *Introduction to Complex Hyperbolic Spaces*][MR886677] or Section 1.1 of
[Noguchi-Winkelmann, *Nevanlinna Theory in Several Complex Variables and Diophantine
Approximation*][MR3156076] for a detailed discussion.

## Implementation Notes

- This file defines the logarithmic counting function first for functions with locally finite
  support on `𝕜` and then specializes to the setting where the function with locally finite support
  is the pole divisor of a meromorphic function `f` or the positive part of the divisor of `f - a`.
  The counting function for the poles exists for every meromorphic function.  The one for a finite
  value `a` requires that `f` takes `a` on no punctured neighborhood, so that the divisor of `f - a`
  is defined.

- Even though value distribution theory is best developed for meromorphic functions on the complex
  plane (and therefore placed in the complex analysis section of Mathlib), we introduce the
  logarithmic counting function for arbitrary normed fields.

## TODO

- Discuss the logarithmic counting function for rational functions, add a forward reference to the
  upcoming converse, formulated in terms of the Nevanlinna height.
-/

@[expose] public section

open Filter Function MeromorphicOn Metric Real Set
open scoped Topology

/-!
## Supporting Notation
-/

namespace Function.locallyFinsuppWithin

variable {E : Type*} [NormedAddCommGroup E]

/--
Shorthand notation for the restriction of a function with locally finite support to the closed unit
ball of radius `r`.
-/
noncomputable def toClosedBall (r : ℝ) :
    locallyFinsupp E ℤ →+o locallyFinsuppWithin (closedBall (0 : E) |r|) ℤ :=
  restrictOrderMonoidHom (subset_univ _)

lemma toClosedBall_apply (r : ℝ) (f : locallyFinsupp E ℤ) :
    toClosedBall r f = f.restrict (subset_univ _) := rfl

@[simp]
lemma toClosedBall_eval_within {r : ℝ} {z : E} (f : locallyFinsupp E ℤ)
    (ha : z ∈ closedBall 0 |r|) :
    toClosedBall r f z = f z := by
  simp_all [toClosedBall_apply, restrict_apply]

/-- Restricting the divisor on `univ` to a closed ball yields the divisor on the closed ball. -/
lemma toClosedBall_divisor {r : ℝ} {f : ℂ → ℂ} {hf : MeromorphicOn f univ}
    (h : ∀ z (hz : z ∈ univ), meromorphicOrderAt f z (hf z hz) ≠ ⊤) :
    divisor f (closedBall 0 |r|) (hf := hf.mono_set (subset_univ _))
      (fun z hz ↦ h z (subset_univ _ hz)) = toClosedBall r (divisor f univ h) := by
  rw [toClosedBall_apply, divisor_restrict]

lemma toClosedBall_support_subset_closedBall {E : Type*} [NormedAddCommGroup E] {r : ℝ}
    (f : locallyFinsupp E ℤ) :
    (toClosedBall r f).support ⊆ closedBall 0 |r| := by
  simp_all [toClosedBall_apply, restrict_apply]

/-!
## The Logarithmic Counting Function of a Function with Locally Finite Support
-/

/--
Definition of the logarithmic counting function, as a group morphism mapping functions `D` with
locally finite support to maps `ℝ → ℝ`.  Given `D`, the result map `logCounting D` takes `r : ℝ` to
a logarithmically weighted measure of values that `D` takes within the disk `∣z∣ ≤ r`.

Implementation Note: In case where `z = 0`, the term `log (r * ‖z‖⁻¹)` evaluates to zero, which is
typically different from `log r - log ‖z‖ = log r`. The summand `(D 0) * log r` compensates this,
producing cleaner formulas when the logarithmic counting function is used in the main theorems of
Value Distribution Theory.  We refer the reader to page 164 of [Lang: Introduction to Complex
Hyperbolic Spaces](https://link.springer.com/book/10.1007/978-1-4757-1945-1) for more details, and
to the lemma `countingFunction_finsum_eq_finsum_add` in
`Mathlib/Analysis/Complex/JensenFormula.lean` for a formal statement.
-/
noncomputable def logCounting {E : Type*} [NormedAddCommGroup E] [ProperSpace E] :
    locallyFinsupp E ℤ →+ (ℝ → ℝ) where
  toFun D := fun r ↦ ∑ᶠ z, D.toClosedBall r z * log (r * ‖z‖⁻¹) + (D 0) * log r
  map_zero' := by aesop
  map_add' D₁ D₂ := by
    simp only [map_add, coe_add, Pi.add_apply, Int.cast_add]
    ext r
    have {A B C D : ℝ} : A + B + (C + D) = A + C + (B + D) := by ring
    rw [Pi.add_apply, this]
    congr 1
    · have h₁s : ((D₁.toClosedBall r).support ∪ (D₂.toClosedBall r).support).Finite := by
        apply Set.finite_union.2
        constructor
        <;> apply finiteSupport _ (isCompact_closedBall 0 |r|)
      repeat
        rw [finsum_eq_sum_of_support_subset (s := h₁s.toFinset)]
        try simp_rw [← Finset.sum_add_distrib, ← add_mul]
      repeat
        intro x hx
        by_contra
        simp_all
    · ring

/--
Evaluation of the logarithmic counting function at zero yields zero.
-/
@[simp] lemma logCounting_eval_zero {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    (D : locallyFinsupp E ℤ) :
    logCounting D 0 = 0 := by
  simp [logCounting]

/--
The logarithmic counting function of a singleton indicator is asymptotically equal to
`log · - log ‖e‖`.
-/
@[simp] lemma logCounting_single_eq_log_sub_const [DecidableEq E] [ProperSpace E] {e : E} {r : ℝ}
    {n : ℤ} (hr : ‖e‖ ≤ r) :
    logCounting (single e n) r = n * (log r - log ‖e‖) := by
  simp only [logCounting, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [finsum_eq_sum_of_support_subset _ (s := (finite_singleton e).toFinset)
    (by simp_all [toClosedBall_apply, restrict_apply, single_apply])]
  simp only [toFinite_toFinset, toFinset_singleton, Finset.sum_singleton]
  rw [toClosedBall_eval_within _ (by simpa [abs_of_nonneg ((norm_nonneg e).trans hr)])]
  by_cases he : 0 = e
  · simp [← he, single_apply]
  · simp only [single_apply, he, reduceIte, Int.cast_zero, zero_mul, add_zero,
      log_mul (ne_of_lt (lt_of_lt_of_le (norm_pos_iff.mpr (he ·.symm)) hr)).symm
      (inv_ne_zero (norm_ne_zero_iff.mpr (he ·.symm))), log_inv]
    grind

/-!
### Elementary Properties of Logarithmic Counting Functions
-/

/--
The logarithmic counting function is even.
-/
lemma logCounting_even [ProperSpace E] (D : locallyFinsupp E ℤ) :
    (logCounting D).Even := fun r ↦ by simp [logCounting, toClosedBall_apply, restrict_apply]

/--
The logarithmic counting function is monotonous.
-/
lemma logCounting_mono [ProperSpace E] {D : locallyFinsupp E ℤ} (hD : 0 ≤ D) :
    MonotoneOn (logCounting D) (Ioi 0) := by
  intro a ha b hb _
  simp_all only [mem_Ioi, logCounting, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  gcongr
  · let s := (toClosedBall b D).support
    have hs : s.Finite := (toClosedBall b D).finiteSupport (isCompact_closedBall 0 |b|)
    repeat rw [finsum_eq_sum_of_support_subset (s := hs.toFinset)]
    · gcongr 1 with z hz
      by_cases h₂z : z = 0
      · simp [h₂z]
      · have := (toClosedBall_support_subset_closedBall D (hs.mem_toFinset.1 hz))
        rw [toClosedBall_eval_within _ this]
        by_cases h₃z : z ∈ closedBall 0 |a|
        · rw [toClosedBall_eval_within _ h₃z]
          gcongr
          exact Int.cast_nonneg (hD z)
        · simp only [h₃z, not_false_eq_true, apply_eq_zero_of_notMem, Int.cast_zero, zero_mul,
            ge_iff_le]
          apply mul_nonneg (Int.cast_nonneg (hD z)) (log_nonneg _)
          apply (le_mul_inv_iff₀ (norm_pos_iff.mpr h₂z)).2
          simp_all [abs_of_pos hb]
    · intro z
      aesop
    · intro z
      simp only [support_mul, mem_inter_iff, mem_support, ne_eq, Int.cast_eq_zero, log_eq_zero,
        mul_eq_zero, inv_eq_zero, norm_eq_zero, not_or, Finite.coe_toFinset, and_imp, s]
      intro h₁ _ _ _ _
      have : z ∈ closedBall 0 |a| := mem_of_indicator_ne_zero h₁
      rw [toClosedBall_eval_within _ this] at h₁
      rwa [toClosedBall_eval_within]
      · simp_all only [abs_of_pos ha, mem_closedBall, dist_zero_right, abs_of_pos hb]
        linarith
  · exact Int.cast_nonneg (hD 0)

/--
The logarithmic counting function of a positive function with locally finite support is
asymptotically strictly monotone.
-/
lemma logCounting_strictMono [DecidableEq E] [ProperSpace E] {D : locallyFinsupp E ℤ} {e : E}
    (hD : single e 1 ≤ D) :
    StrictMonoOn (logCounting D) (Ioi ‖e‖) := by
  rw [(by aesop : logCounting D = logCounting (single e 1) + logCounting (D - single e 1))]
  apply StrictMonoOn.add_monotone
  · intro a ha b hb hab
    rw [mem_Ioi] at ha hb
    rw [logCounting_single_eq_log_sub_const ha.le, logCounting_single_eq_log_sub_const hb.le]
    gcongr
    exact (norm_nonneg e).trans_lt ha
  · intro a ha b hb hab
    apply logCounting_mono _ _ ((norm_nonneg e).trans_lt hb) hab
    · simp [hD]
    · simpa [mem_Ioi] using (norm_nonneg e).trans_lt ha

/--
For `1 ≤ r`, the logarithmic counting function is non-negative.
-/
theorem logCounting_nonneg {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    {f : locallyFinsupp E ℤ} {r : ℝ} (h : 0 ≤ f) (hr : 1 ≤ r) :
    0 ≤ logCounting f r := by
  have h₃r : 0 < r := by linarith
  suffices ∀ z, 0 ≤ toClosedBall r f z * log (r * ‖z‖⁻¹) from
    add_nonneg (finsum_nonneg this) <| mul_nonneg (by simpa using h 0) (log_nonneg hr)
  intro a
  by_cases h₁a : a = 0
  · simp_all
  by_cases h₂a : a ∈ closedBall 0 |r|
  · refine mul_nonneg ?_ <| log_nonneg ?_
    · simpa [h₂a] using h a
    · simpa [mul_comm r, one_le_inv_mul₀ (norm_pos_iff.mpr h₁a), abs_of_pos h₃r] using h₂a
  · simp [apply_eq_zero_of_notMem ((toClosedBall r) _) h₂a]

/--
For `1 ≤ r`, the logarithmic counting function respects the `≤` relation.
-/
theorem logCounting_le {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    {f₁ f₂ : locallyFinsupp E ℤ} {r : ℝ} (h : f₁ ≤ f₂) (hr : 1 ≤ r) :
    logCounting f₁ r ≤ logCounting f₂ r := by
  rw [← sub_nonneg] at h ⊢
  simpa using logCounting_nonneg h hr

/--
The logarithmic counting function respects the `≤` relation asymptotically.
-/
theorem logCounting_eventuallyLE {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    {f₁ f₂ : locallyFinsupp E ℤ} (h : f₁ ≤ f₂) :
    logCounting f₁ ≤ᶠ[atTop] logCounting f₂ := by
  filter_upwards [eventually_ge_atTop 1] using fun _ hr ↦ logCounting_le h hr

/--
**Counting estimate**: for a nonnegative function `D` on `ℂ` with locally finite support and for
radii `1 ≤ ρ < r`, the total mass of `D` on the closed ball of radius `ρ`, weighted by
`log (r / ρ)`, is bounded by the logarithmic counting function of `D` at radius `r`.
-/
theorem sum_toClosedBall_le_logCounting {D : Function.locallyFinsupp ℂ ℤ} {ρ r : ℝ}
    (hD : 0 ≤ D) (hρ : 1 ≤ ρ) (hρr : ρ < r) :
    (∑ᶠ z, (D.toClosedBall ρ z : ℝ)) * Real.log (r / ρ) ≤ D.logCounting r := by
  have hr₀ : (0 : ℝ) < r := by linarith
  have habsρ : |ρ| = ρ := abs_of_pos (by linarith)
  have habsr : |r| = r := abs_of_pos hr₀
  have hD' : ∀ z, 0 ≤ D z := (by simpa using (le_def.1 hD) ·)
  -- `toClosedBall` inherits nonnegativity
  have hpos {s : ℝ} {z : ℂ} : 0 ≤ D.toClosedBall s z := by
    simpa using le_def.1 (map_nonneg (toClosedBall s) hD) z
  -- The common finite index set
  have hfin : ((D.toClosedBall r).support).Finite :=
    finiteSupport _ (isCompact_closedBall 0 |r|)
  set t : Finset ℂ := insert 0 hfin.toFinset with ht_def
  have hmem {z : ℂ} : D.toClosedBall r z ≠ 0 → z ∈ t :=
    fun hz ↦ Finset.mem_insert_of_mem (hfin.mem_toFinset.2 hz)
  have hmemρ : ∀ z : ℂ, D.toClosedBall ρ z ≠ 0 → z ∈ t := by
    intro z hz
    by_cases h : z ∈ closedBall (0 : ℂ) |ρ|
    · apply hmem
      rw [toClosedBall_eval_within _ (by
        rw [mem_closedBall_zero_iff, habsr]
        exact le_trans (by rwa [mem_closedBall_zero_iff, habsρ] at h) hρr.le)]
      rwa [toClosedBall_eval_within _ h] at hz
    · exact absurd (apply_eq_zero_of_notMem _ h) hz
  -- Rewrite both sides as finite sums over `t`
  have hRHS : D.logCounting r
      = (∑ z ∈ t, (D.toClosedBall r z : ℝ) * Real.log (r * ‖z‖⁻¹)) + (D 0 : ℝ) * Real.log r := by
    simp only [logCounting, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    congr 1
    apply finsum_eq_sum_of_support_subset
    intro z hz
    simp only [mem_support, ne_eq] at hz
    apply hmem
    intro h
    simp [h] at hz
  rw [finsum_eq_sum_of_support_subset _ (by aesop), hRHS, Finset.sum_mul]
  -- Compare the sums term by term
  have key : ∀ z ∈ t, (D.toClosedBall ρ z : ℝ) * Real.log (r / ρ)
      ≤ (D.toClosedBall r z : ℝ) * Real.log (r * ‖z‖⁻¹)
        + (if z = 0 then (D 0 : ℝ) * Real.log r else 0) := by
    intro z hz
    by_cases hz0 : z = 0
    · subst hz0
      rw [ite_eq_left rfl, toClosedBall_eval_within _ (by simp),
        toClosedBall_eval_within _ (by simp)]
      simp only [norm_zero, inv_zero, mul_zero, log_zero, mul_zero, zero_add]
      apply mul_le_mul_of_nonneg_left _ (by exact_mod_cast hD' 0)
      apply Real.log_le_log (by positivity)
      exact div_le_self hr₀.le hρ
    · rw [ite_eq_right hz0, add_zero]
      by_cases hzρ : z ∈ closedBall (0 : ℂ) |ρ|
      · have hz_norm : ‖z‖ ≤ ρ := by rwa [mem_closedBall_zero_iff, habsρ] at hzρ
        have hz_pos : (0 : ℝ) < ‖z‖ := norm_pos_iff.2 hz0
        have : z ∈ closedBall 0 |r| := by
          rw [mem_closedBall_zero_iff, habsr]
          exact hz_norm.trans hρr.le
        rw [toClosedBall_eval_within _ hzρ, toClosedBall_eval_within _ this]
        apply mul_le_mul_of_nonneg_left _ (by exact_mod_cast hD' z)
        rw [div_eq_mul_inv]
        apply Real.log_le_log (by positivity)
        gcongr
      · rw [locallyFinsuppWithin.apply_eq_zero_of_notMem _ hzρ, Int.cast_zero, zero_mul]
        by_cases hzr : D.toClosedBall r z = 0
        · simp [hzr]
        · apply mul_nonneg (by exact_mod_cast hpos)
          have hz_le : ‖z‖ ≤ r := by
            rw [← mem_closedBall_zero_iff, ← habsr]
            exact toClosedBall_support_subset_closedBall (r := r) D (mem_support.2 hzr)
          apply Real.log_nonneg
          rw [← div_eq_mul_inv, le_div_iff₀ (norm_pos_iff.2 hz0)]
          simpa using hz_le
  calc ∑ z ∈ t, (D.toClosedBall ρ z : ℝ) * Real.log (r / ρ)
      ≤ ∑ z ∈ t, ((D.toClosedBall r z : ℝ) * Real.log (r * ‖z‖⁻¹)
          + (if z = 0 then (D 0 : ℝ) * Real.log r else 0)) := Finset.sum_le_sum key
    _ = (∑ z ∈ t, (D.toClosedBall r z : ℝ) * Real.log (r * ‖z‖⁻¹)) + (D 0 : ℝ) * Real.log r := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq' t 0 (fun _ ↦ (D 0 : ℝ) * Real.log r),
          ite_eq_left (Finset.mem_insert_self 0 hfin.toFinset)]

end Function.locallyFinsuppWithin

/-!
## The Logarithmic Counting Function of a Meromorphic Function
-/

namespace ValueDistribution

section Frequently

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} {f g : 𝕜 → E} {a : WithTop E}

/-- No function takes the value `⊤` on a punctured neighborhood. -/
lemma frequently_coe_ne_top (f : 𝕜 → E) (z : 𝕜) : ∃ᶠ w in 𝓝[≠] z, (f w : WithTop E) ≠ ⊤ :=
  .of_forall fun _ ↦ WithTop.coe_ne_top

/-- The default discharger for the argument `∀ z, ∃ᶠ w in 𝓝[≠] z, (f w : WithTop E) ≠ a` of
`ValueDistribution.logCounting`, `ValueDistribution.proximity`, and
`ValueDistribution.characteristic`: no function takes the value `⊤` on a punctured neighborhood
(`ValueDistribution.frequently_coe_ne_top`), and for a finite value it fails with an explanation.
It accepts a proof that unification has already supplied. -/
macro (name := frequentlyNe) &"value_distribution_frequently_ne" : tactic => `(tactic| first
  | done
  | exact ValueDistribution.frequently_coe_ne_top _
  | fail "the function must take the value on no punctured neighborhood; only for ⊤ is \
      this supplied by default")

/--
If two functions agree on a codiscrete set and the first one takes a value `a` on no punctured
neighborhood, then neither does the second one.
-/
lemma frequently_coe_ne_of_eventuallyEq_codiscrete (hfg : f =ᶠ[codiscrete 𝕜] g)
    (ha : ∀ z, ∃ᶠ w in 𝓝[≠] z, (f w : WithTop E) ≠ a) (z : 𝕜) :
    ∃ᶠ w in 𝓝[≠] z, (g w : WithTop E) ≠ a :=
  (ha z).mp ((hfg.filter_mono (nhdsNE_le_codiscrete z)).mono fun _ hw h ↦ hw ▸ h)

variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] {a₀ : E}

/--
A function that is meromorphic at `z` takes a finite value `a₀` on no punctured neighborhood of `z`
if and only if `f - a₀` has finite order at `z`.
-/
lemma frequently_coe_ne_coe_iff {z : 𝕜} (hf : MeromorphicAt f z) :
    (∃ᶠ w in 𝓝[≠] z, (f w : WithTop E) ≠ a₀) ↔ meromorphicOrderAt (f · - a₀) z ≠ ⊤ := by
  rw [Ne, meromorphicOrderAt_eq_top_iff, not_eventually]
  simp [sub_eq_zero]

/--
A function that is meromorphic at `z` takes the value `0` on no punctured neighborhood of `z` if and
only if it has finite order at `z`.
-/
lemma frequently_coe_ne_zero_iff {z : 𝕜} (hf : MeromorphicAt f z) :
    (∃ᶠ w in 𝓝[≠] z, (f w : WithTop E) ≠ 0) ↔ meromorphicOrderAt f z hf ≠ ⊤ := by
  rw [Ne, meromorphicOrderAt_eq_top_iff, not_eventually]
  simp

omit [NormedSpace 𝕜 E] in
/--
If `f` takes a finite value `a₀` on no punctured neighborhood of `z`, then `f - a₀` takes the value
`0` on no punctured neighborhood of `z`.
-/
lemma frequently_coe_sub_const_ne_zero {z : 𝕜} (ha : ∃ᶠ w in 𝓝[≠] z, (f w : WithTop E) ≠ a₀) :
    ∃ᶠ w in 𝓝[≠] z, (((f - fun _ ↦ a₀ : 𝕜 → E) w : E) : WithTop E) ≠ 0 :=
  ha.mono fun _ hw h ↦ hw (congrArg _ (sub_eq_zero.1 (WithTop.coe_eq_zero.1 h)))

/--
A function that is meromorphic at `z` and takes a finite value `a₀` on no punctured neighborhood of
`z` differs from `a₀` on a punctured neighborhood of `z`.
-/
lemma eventually_ne_of_frequently_coe_ne {z : 𝕜} (hf : MeromorphicAt f z)
    (ha : ∃ᶠ w in 𝓝[≠] z, (f w : WithTop E) ≠ a₀) : ∀ᶠ w in 𝓝[≠] z, f w ≠ a₀ := by
  have h : MeromorphicAt (f · - a₀) z := hf.sub (.const a₀ z)
  rcases h.eventually_eq_zero_or_eventually_ne_zero with h₀ | h₀
  · exact absurd ((meromorphicOrderAt_eq_top_iff h).2 h₀) ((frequently_coe_ne_coe_iff hf).1 ha)
  · filter_upwards [h₀] with w hw using sub_ne_zero.1 hw

/--
If two meromorphic functions vanish on no punctured neighborhood, then neither does their product.
-/
lemma frequently_coe_mul_ne_zero {f₁ f₂ : 𝕜 → 𝕜} (h₁f₁ : Meromorphic f₁)
    (h₂f₁ : ∀ z, ∃ᶠ w in 𝓝[≠] z, (f₁ w : WithTop 𝕜) ≠ 0) (h₁f₂ : Meromorphic f₂)
    (h₂f₂ : ∀ z, ∃ᶠ w in 𝓝[≠] z, (f₂ w : WithTop 𝕜) ≠ 0) (z : 𝕜) :
    ∃ᶠ w in 𝓝[≠] z, ((f₁ * f₂) w : WithTop 𝕜) ≠ 0 := by
  rw [frequently_coe_ne_zero_iff ((h₁f₁.mul h₁f₂) z),
    meromorphicOrderAt_mul (h₁f₁ z) (h₁f₂ z)]
  exact WithTop.add_ne_top.2 ⟨(frequently_coe_ne_zero_iff (h₁f₁ z)).1 (h₂f₁ z),
    (frequently_coe_ne_zero_iff (h₁f₂ z)).1 (h₂f₂ z)⟩

end Frequently

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [ProperSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f g : 𝕜 → E} {a : WithTop E} {a₀ : E}

variable (f a) in
/--
The logarithmic counting function of a meromorphic function.

If `f : 𝕜 → E` is meromorphic and `a : WithTop E` is a value that `f` takes on no punctured
neighborhood (`ha`), this is a logarithmically weighted measure of the number of times the function
`f` takes the value `a` within the disk `∣z∣ ≤ r`, taking multiplicities into account.  In the
special case where `a = ⊤`, it counts the poles of `f`; there `ha` holds for every function and is
supplied by default.  For a finite value `a`, the condition `ha` states that `f - a` has finite
order everywhere (`ValueDistribution.frequently_coe_ne_coe_iff`): a point near which `f` equals `a`
identically has no finite multiplicity.

Both proofs precede the radius, so the counting function for the poles is evaluated as
`(logCounting f ⊤) r`.
-/
noncomputable def logCounting (hf : Meromorphic f := by fun_prop_default)
    (ha : ∀ z, ∃ᶠ w in 𝓝[≠] z, (f w : WithTop E) ≠ a := by
      value_distribution_frequently_ne) :
    ℝ → ℝ :=
  match a, ha with
  | none, _ => (poleDivisor f univ hf.meromorphicOn).logCounting
  | some a₀, ha => (divisor (f · - a₀) univ (hf := (hf.fun_sub (.const a₀)).meromorphicOn)
      fun z _ ↦ (frequently_coe_ne_coe_iff (hf z)).1 (ha z))⁺.logCounting

/--
The logarithmic counting function `logCounting f ⊤` is the logarithmic counting function associated
with the pole divisor of `f`.
-/
lemma logCounting_top (hf : Meromorphic f) :
    logCounting f ⊤ hf = (poleDivisor f univ hf.meromorphicOn).logCounting :=
  rfl

/--
For finite values `a₀`, the logarithmic counting function `logCounting f a₀` is the logarithmic
counting function for the zeros of `f - a₀`.
-/
lemma logCounting_coe (hf : Meromorphic f) (ha : ∀ z, ∃ᶠ w in 𝓝[≠] z, (f w : WithTop E) ≠ a₀) :
    logCounting f a₀ hf ha = (divisor (f · - a₀) univ
      (hf := (hf.fun_sub (.const a₀)).meromorphicOn)
      fun z _ ↦ (frequently_coe_ne_coe_iff (hf z)).1 (ha z))⁺.logCounting :=
  rfl

/--
The logarithmic counting function `logCounting f 0` is the logarithmic counting function associated
with the zero divisor of `f`.
-/
lemma logCounting_zero (hf : Meromorphic f) (ha : ∀ z, ∃ᶠ w in 𝓝[≠] z, (f w : WithTop E) ≠ 0) :
    logCounting f 0 hf ha = (divisor f univ (hf := hf.meromorphicOn)
      fun z _ ↦ (frequently_coe_ne_zero_iff (hf z)).1 (ha z))⁺.logCounting := by
  change (divisor (f · - 0) univ (hf := (hf.fun_sub (.const 0)).meromorphicOn) _)⁺.logCounting =
    _
  congr 2
  exact divisor_congr fun z _ ↦ meromorphicOrderAt_congr _ (.of_eq (by simp))

/--
For finite values `a₀`, the logarithmic counting function `logCounting f a₀` equals the logarithmic
counting function for the zeros of `f - a₀`.
-/
lemma logCounting_coe_eq_logCounting_sub_const_zero {hf : Meromorphic f}
    {ha : ∀ z, ∃ᶠ w in 𝓝[≠] z, (f w : WithTop E) ≠ a₀} :
    logCounting f a₀ hf ha = logCounting (f - fun _ ↦ a₀) 0 (hf.sub (.const a₀))
      fun z ↦ frequently_coe_sub_const_ne_zero (ha z) := by
  rw [logCounting_coe, logCounting_zero]
  rfl

/--
Evaluation of the logarithmic counting function at zero yields zero.
-/
@[simp] lemma logCounting_eval_zero {hf : Meromorphic f}
    {ha : ∀ z, ∃ᶠ w in 𝓝[≠] z, (f w : WithTop E) ≠ a} :
    logCounting f a hf ha 0 = 0 := by
  cases a with
  | top => simp [logCounting_top]
  | coe a₀ => simp [logCounting_coe]

/--
The logarithmic counting function associated with the divisor of `f` is the difference between
`logCounting f 0` and `logCounting f ⊤`.
-/
theorem log_counting_zero_sub_logCounting_top (hf : Meromorphic f)
    (h : ∀ z (hz : z ∈ univ), meromorphicOrderAt f z (hf.meromorphicOn z hz) ≠ ⊤) :
    (divisor f univ h).logCounting =
      logCounting f 0 hf (fun z ↦ (frequently_coe_ne_zero_iff (hf z)).2 (h z (mem_univ z))) -
        logCounting f ⊤ hf := by
  rw [logCounting_zero, logCounting_top, poleDivisor_eq_negPart_divisor h, ← map_sub,
    posPart_sub_negPart]

/--
The logarithmic counting function of a constant function is zero.
-/
@[simp] theorem logCounting_const {c : E} {e : WithTop E} {hf : Meromorphic fun _ : 𝕜 ↦ c}
    {ha : ∀ z, ∃ᶠ w in 𝓝[≠] z, ((fun _ : 𝕜 ↦ c) w : WithTop E) ≠ e} :
    logCounting (fun _ ↦ c) e hf ha = 0 := by
  cases e with
  | top => rw [logCounting_top, AnalyticOnNhd.poleDivisor_eq_zero analyticOnNhd_const, map_zero]
  | coe e => rw [logCounting_coe, divisor_const, posPart_zero, map_zero]

/--
The logarithmic counting function of the constant function zero is zero.
-/
@[simp] theorem logCounting_const_zero {e : WithTop E} {hf : Meromorphic (0 : 𝕜 → E)}
    {ha : ∀ z, ∃ᶠ w in 𝓝[≠] z, ((0 : 𝕜 → E) w : WithTop E) ≠ e} :
    logCounting (0 : 𝕜 → E) e hf ha = 0 := logCounting_const

/--
The logarithmic counting function is even.
-/
theorem logCounting_even {e : WithTop E} {hf : Meromorphic f}
    {ha : ∀ z, ∃ᶠ w in 𝓝[≠] z, (f w : WithTop E) ≠ e} :
    (logCounting f e hf ha).Even := by
  cases e with
  | top => exact locallyFinsuppWithin.logCounting_even _
  | coe e => exact locallyFinsuppWithin.logCounting_even _

/--
The logarithmic counting function is monotonous.
-/
theorem logCounting_monotoneOn {e : WithTop E} {hf : Meromorphic f}
    {ha : ∀ z, ∃ᶠ w in 𝓝[≠] z, (f w : WithTop E) ≠ e} :
    MonotoneOn (logCounting f e hf ha) (Ioi 0) := by
  cases e with
  | top => exact locallyFinsuppWithin.logCounting_mono (poleDivisor_nonneg _)
  | coe e => exact locallyFinsuppWithin.logCounting_mono (posPart_nonneg _)

/--
For `1 ≤ r`, the logarithmic counting function is non-negative.
-/
theorem logCounting_nonneg {r : ℝ} {e : WithTop E} {hf : Meromorphic f}
    {ha : ∀ z, ∃ᶠ w in 𝓝[≠] z, (f w : WithTop E) ≠ e} (hr : 1 ≤ r) :
    0 ≤ logCounting f e hf ha r := by
  cases e with
  | top => exact locallyFinsuppWithin.logCounting_nonneg (poleDivisor_nonneg _) hr
  | coe e => exact locallyFinsuppWithin.logCounting_nonneg (posPart_nonneg _) hr

/--
The logarithmic counting function is asymptotically non-negative.
-/
theorem logCounting_eventually_nonneg {e : WithTop E} {hf : Meromorphic f}
    {ha : ∀ z, ∃ᶠ w in 𝓝[≠] z, (f w : WithTop E) ≠ e} :
    0 ≤ᶠ[atTop] logCounting f e hf ha := by
  filter_upwards [eventually_ge_atTop 1] using fun _ hr ↦ by simp [logCounting_nonneg hr]

/-!
## Elementary Properties of the Logarithmic Counting Function
-/

/--
If two functions differ only on a discrete set, then their logarithmic counting
functions agree.
-/
theorem logCounting_congr_codiscrete [NormedSpace ℂ E] {f g : ℂ → E} (hfg : f =ᶠ[codiscrete ℂ] g)
    {e : WithTop E} {hf : Meromorphic f} {ha : ∀ z, ∃ᶠ w in 𝓝[≠] z, (f w : WithTop E) ≠ e} :
    logCounting f e hf ha = logCounting g e (hf.congr_codiscrete hfg)
      (frequently_coe_ne_of_eventuallyEq_codiscrete hfg ha) := by
  cases e with
  | top =>
    rw [logCounting_top, logCounting_top, poleDivisor_congr_codiscreteWithin hfg isOpen_univ]
  | coe e =>
    rw [logCounting_coe, logCounting_coe]
    congr 2
    apply divisor_congr_codiscreteWithin _ isOpen_univ
    filter_upwards [hfg] using by simp

/--
Relation between the logarithmic counting functions of `f` and of `f⁻¹`.
-/
theorem logCounting_inv {f : 𝕜 → 𝕜} (hf : Meromorphic f)
    (ha : ∀ z, ∃ᶠ w in 𝓝[≠] z, (f w : WithTop 𝕜) ≠ 0) {hf' : Meromorphic f⁻¹} :
    logCounting f⁻¹ ⊤ hf' = logCounting f 0 hf ha := by
  have h z (hz : z ∈ univ) : meromorphicOrderAt f z (hf.meromorphicOn z hz) ≠ ⊤ :=
    (frequently_coe_ne_zero_iff (hf z)).1 (ha z)
  have h' z (hz : z ∈ univ) : meromorphicOrderAt f⁻¹ z (hf'.meromorphicOn z hz) ≠ ⊤ :=
    (meromorphicOrderAt_inv (hf z)).trans_ne (by simpa using h z hz)
  rw [logCounting_top, logCounting_zero, poleDivisor_eq_negPart_divisor h', divisor_inv h,
    negPart_neg]

/--
Adding an analytic function does not change the logarithmic counting function for the poles.
-/
theorem logCounting_add_analyticOn (hf : Meromorphic f) (hg : AnalyticOn 𝕜 g univ)
    {hfg : Meromorphic (f + g)} :
    logCounting (f + g) ⊤ hfg = logCounting f ⊤ hf := by
  rw [logCounting_top, logCounting_top, poleDivisor_add_of_analyticOnNhd_right hf.meromorphicOn
    (isOpen_univ.analyticOn_iff_analyticOnNhd.1 hg)]

/--
Special case of `logCounting_add_analyticOn`: Adding a constant does not change the logarithmic
counting function for the poles.
-/
@[simp] theorem logCounting_add_const (hf : Meromorphic f) {hf' : Meromorphic (f + fun _ ↦ a₀)} :
    logCounting (f + fun _ ↦ a₀) ⊤ hf' = logCounting f ⊤ hf :=
  logCounting_add_analyticOn hf analyticOn_const

/--
Special case of `logCounting_add_analyticOn`: Subtracting a constant does not change the logarithmic
counting function for the poles.
-/
@[simp] theorem logCounting_sub_const (hf : Meromorphic f) {hf' : Meromorphic (f - fun _ ↦ a₀)} :
    logCounting (f - fun _ ↦ a₀) ⊤ hf' = logCounting f ⊤ hf := by
  rw [logCounting_top, logCounting_top, ← poleDivisor_add_of_analyticOnNhd_right hf.meromorphicOn
    (analyticOnNhd_const (v := -a₀))]
  congr 1
  exact poleDivisor_congr fun z _ ↦
    meromorphicOrderAt_congr _ (.of_eq (by ext; simp [sub_eq_add_neg]))

/-!
## Behaviour under Arithmetic Operations
-/

/--
For `1 ≤ r`, the logarithmic counting function for the poles of `f + g` is less than or equal to the
sum of the logarithmic counting functions for the poles of `f` and `g`, respectively.
-/
theorem logCounting_add_top_le {f₁ f₂ : 𝕜 → E} {r : ℝ} (h₁f₁ : Meromorphic f₁)
    (h₁f₂ : Meromorphic f₂) (hr : 1 ≤ r) :
    (logCounting (f₁ + f₂) ⊤ (h₁f₁.add h₁f₂)) r ≤
      (logCounting f₁ ⊤ h₁f₁ + logCounting f₂ ⊤ h₁f₂) r := by
  rw [logCounting_top, logCounting_top, logCounting_top,
    ← locallyFinsuppWithin.logCounting.map_add]
  exact locallyFinsuppWithin.logCounting_le
    (poleDivisor_add_le_add h₁f₁.meromorphicOn h₁f₂.meromorphicOn) hr

/--
Asymptotically, the logarithmic counting function for the poles of `f + g` is less than or equal to
the sum of the logarithmic counting functions for the poles of `f` and `g`, respectively.
-/
theorem logCounting_add_top_eventuallyLE {f₁ f₂ : 𝕜 → E} (h₁f₁ : Meromorphic f₁)
    (h₁f₂ : Meromorphic f₂) :
    logCounting (f₁ + f₂) ⊤ (h₁f₁.add h₁f₂) ≤ᶠ[atTop]
      logCounting f₁ ⊤ h₁f₁ + logCounting f₂ ⊤ h₁f₂ := by
  filter_upwards [eventually_ge_atTop 1] using fun _ hr ↦ logCounting_add_top_le h₁f₁ h₁f₂ hr

/-- The case of `logCounting_sum_top_le` where every function of the family is meromorphic. -/
private theorem logCounting_sum_top_le_of_forall {α : Type*} (s : Finset α) (f : α → 𝕜 → E)
    {r : ℝ} (h₁f : ∀ a, Meromorphic (f a)) (hr : 1 ≤ r) :
    (logCounting (∑ a ∈ s, f a) ⊤ (Meromorphic.sum fun a _ ↦ h₁f a)) r ≤
      ∑ a ∈ s, (logCounting (f a) ⊤ (h₁f a)) r := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha hs =>
    calc (logCounting (∑ x ∈ insert a s, f x) ⊤ (Meromorphic.sum fun a _ ↦ h₁f a)) r
      _ = (logCounting (f a + ∑ x ∈ s, f x) ⊤ ((h₁f a).add (Meromorphic.sum fun a _ ↦ h₁f a))) r :=
        by simp only [Finset.sum_insert ha]
      _ ≤ (logCounting (f a) ⊤ (h₁f a) +
            logCounting (∑ x ∈ s, f x) ⊤ (Meromorphic.sum fun a _ ↦ h₁f a)) r :=
        logCounting_add_top_le (h₁f a) (Meromorphic.sum fun a _ ↦ h₁f a) hr
      _ ≤ (logCounting (f a) ⊤ (h₁f a)) r + ∑ x ∈ s, (logCounting (f x) ⊤ (h₁f x)) r :=
        add_le_add le_rfl hs
      _ = ∑ x ∈ insert a s, (logCounting (f x) ⊤ (h₁f x)) r := by rw [Finset.sum_insert ha]

/--
For `1 ≤ r`, the logarithmic counting function for the poles of a sum `∑ a ∈ s, f a` is less than or
equal to the sum of the logarithmic counting functions for the poles of the `f ·`.
-/
theorem logCounting_sum_top_le {α : Type*} (s : Finset α) (f : α → 𝕜 → E) {r : ℝ}
    (h₁f : ∀ a ∈ s, Meromorphic (f a)) (hr : 1 ≤ r) :
    (logCounting (∑ a ∈ s, f a) ⊤ (Meromorphic.sum h₁f)) r ≤
      ∑ a ∈ s.attach, (logCounting (f a) ⊤ (h₁f a a.2)) r := by
  have := logCounting_sum_top_le_of_forall s.attach (fun a : s ↦ f a) (fun a ↦ h₁f a a.2) hr
  simpa [Finset.sum_attach] using! this

/--
Asymptotically, the logarithmic counting function for the poles of a sum `∑ a ∈ s, f a` is less than
or equal to the sum of the logarithmic counting functions for the poles of the `f ·`.
-/
theorem logCounting_sum_top_eventuallyLE {α : Type*} (s : Finset α) (f : α → 𝕜 → E)
    (h₁f : ∀ a ∈ s, Meromorphic (f a)) :
    logCounting (∑ a ∈ s, f a) ⊤ (Meromorphic.sum h₁f) ≤ᶠ[atTop]
      ∑ a ∈ s.attach, logCounting (f a) ⊤ (h₁f a a.2) := by
  filter_upwards [eventually_ge_atTop 1] with r hr
  simpa using logCounting_sum_top_le s f h₁f hr

/--
For `1 ≤ r`, the logarithmic counting function for the zeros of `f * g` is less than or equal to the
sum of the logarithmic counting functions for the zeros of `f` and `g`, respectively.

Note: The statement proven here is found at the top of page 169 of [Lang: Introduction to Complex
Hyperbolic Spaces](https://link.springer.com/book/10.1007/978-1-4757-1945-1) where it is written as
an inequality between functions. This could be interpreted as claiming that the inequality holds for
ALL values of `r`, which is not true. For a counterexample, take `f₁ : z → z` and `f₂ : z → z⁻¹`.
Then,

- `logCounting f₁ 0 = log`
- `logCounting f₂ 0 = 0`
- `logCounting (f₁ * f₂) 0 = 0`

But `log r` is negative for small `r`.
-/
theorem logCounting_mul_zero_le {f₁ f₂ : 𝕜 → 𝕜} {r : ℝ} (hr : 1 ≤ r)
    (h₁f₁ : Meromorphic f₁) (h₂f₁ : ∀ z, ∃ᶠ w in 𝓝[≠] z, (f₁ w : WithTop 𝕜) ≠ 0)
    (h₁f₂ : Meromorphic f₂) (h₂f₂ : ∀ z, ∃ᶠ w in 𝓝[≠] z, (f₂ w : WithTop 𝕜) ≠ 0)
    {h : ∀ z, ∃ᶠ w in 𝓝[≠] z, ((f₁ * f₂) w : WithTop 𝕜) ≠ 0} :
    logCounting (f₁ * f₂) 0 (h₁f₁.mul h₁f₂) h r ≤
      (logCounting f₁ 0 h₁f₁ h₂f₁ + logCounting f₂ 0 h₁f₂ h₂f₂) r := by
  rw [logCounting_zero, logCounting_zero, logCounting_zero,
    divisor_mul h₁f₁.meromorphicOn h₁f₂.meromorphicOn
      (fun z _ ↦ (frequently_coe_ne_zero_iff (h₁f₁ z)).1 (h₂f₁ z))
      (fun z _ ↦ (frequently_coe_ne_zero_iff (h₁f₂ z)).1 (h₂f₂ z)),
    ← locallyFinsuppWithin.logCounting.map_add]
  exact locallyFinsuppWithin.logCounting_le (locallyFinsuppWithin.posPart_add _ _) hr

/--
Asymptotically, the logarithmic counting function for the zeros of `f * g` is less than or equal to
the sum of the logarithmic counting functions for the zeros of `f` and `g`, respectively.
-/
theorem logCounting_mul_zero_eventuallyLE {f₁ f₂ : 𝕜 → 𝕜}
    (h₁f₁ : Meromorphic f₁) (h₂f₁ : ∀ z, ∃ᶠ w in 𝓝[≠] z, (f₁ w : WithTop 𝕜) ≠ 0)
    (h₁f₂ : Meromorphic f₂) (h₂f₂ : ∀ z, ∃ᶠ w in 𝓝[≠] z, (f₂ w : WithTop 𝕜) ≠ 0)
    {h : ∀ z, ∃ᶠ w in 𝓝[≠] z, ((f₁ * f₂) w : WithTop 𝕜) ≠ 0} :
    logCounting (f₁ * f₂) 0 (h₁f₁.mul h₁f₂) h ≤ᶠ[atTop]
      logCounting f₁ 0 h₁f₁ h₂f₁ + logCounting f₂ 0 h₁f₂ h₂f₂ := by
  filter_upwards [eventually_ge_atTop 1] using
    fun _ hr ↦ logCounting_mul_zero_le hr h₁f₁ h₂f₁ h₁f₂ h₂f₂

/--
For `1 ≤ r`, the logarithmic counting function for the poles of `f * g` is less than or equal to the
sum of the logarithmic counting functions for the poles of `f` and `g`, respectively.
-/
theorem logCounting_mul_top_le {f₁ f₂ : 𝕜 → 𝕜} {r : ℝ} (hr : 1 ≤ r)
    (h₁f₁ : Meromorphic f₁) (h₁f₂ : Meromorphic f₂) :
    (logCounting (f₁ * f₂) ⊤ (h₁f₁.mul h₁f₂)) r ≤
      (logCounting f₁ ⊤ h₁f₁ + logCounting f₂ ⊤ h₁f₂) r := by
  rw [logCounting_top, logCounting_top, logCounting_top,
    ← locallyFinsuppWithin.logCounting.map_add]
  exact locallyFinsuppWithin.logCounting_le
    (poleDivisor_mul_le_add h₁f₁.meromorphicOn h₁f₂.meromorphicOn) hr

/--
Asymptotically, the logarithmic counting function for the poles of `f * g` is less than or equal to
the sum of the logarithmic counting functions for the poles of `f` and `g`, respectively.
-/
theorem logCounting_mul_top_eventuallyLE {f₁ f₂ : 𝕜 → 𝕜}
    (h₁f₁ : Meromorphic f₁) (h₁f₂ : Meromorphic f₂) :
    logCounting (f₁ * f₂) ⊤ (h₁f₁.mul h₁f₂) ≤ᶠ[atTop]
      logCounting f₁ ⊤ h₁f₁ + logCounting f₂ ⊤ h₁f₂ := by
  filter_upwards [eventually_ge_atTop 1] using
    fun _ hr ↦ logCounting_mul_top_le hr h₁f₁ h₁f₂

/--
For natural numbers `n`, the logarithmic counting function for the zeros of `f ^ n` equals `n`
times the logarithmic counting function for the zeros of `f`.
-/
theorem logCounting_pow_zero {f : 𝕜 → 𝕜} {n : ℕ} (hf : Meromorphic f)
    (ha : ∀ z, ∃ᶠ w in 𝓝[≠] z, (f w : WithTop 𝕜) ≠ 0) {hf' : Meromorphic (f ^ n)}
    {ha' : ∀ z, ∃ᶠ w in 𝓝[≠] z, ((f ^ n) w : WithTop 𝕜) ≠ 0} :
    logCounting (f ^ n) 0 hf' ha' = n • logCounting f 0 hf ha := by
  rw [logCounting_zero, logCounting_zero,
    divisor_pow (fun z _ ↦ (frequently_coe_ne_zero_iff (hf z)).1 (ha z)) n]
  simp

/--
For natural numbers `n`, the logarithmic counting function for the poles of `f ^ n` equals `n` times
the logarithmic counting function for the poles of `f`.
-/
@[simp] theorem logCounting_pow_top {f : 𝕜 → 𝕜} {n : ℕ} (hf : Meromorphic f)
    {hf' : Meromorphic (f ^ n)} :
    logCounting (f ^ n) ⊤ hf' = n • logCounting f ⊤ hf := by
  rw [logCounting_top, logCounting_top, poleDivisor_pow hf.meromorphicOn n, map_nsmul]

end ValueDistribution

/-!
## Representation by Integrals

For `𝕜 = ℂ`, the theorems below describe the logarithmic counting function in terms of circle
averages.
-/

/--
Over the complex numbers, present the logarithmic counting function attached to the divisor of a
meromorphic function `f` of finite order everywhere as a circle average over `log ‖f ·‖`.

This is a reformulation of Jensen's formula of complex analysis. See
`MeromorphicOn.circleAverage_log_norm` for Jensen's formula in the original context.
-/
theorem Function.locallyFinsuppWithin.logCounting_divisor_eq_circleAverage_sub_const {R : ℝ}
    {f : ℂ → ℂ} (h : Meromorphic f)
    (h₀ : ∀ z (hz : z ∈ univ), meromorphicOrderAt f z (h.meromorphicOn z hz) ≠ ⊤) (hR : R ≠ 0) :
    logCounting (divisor f univ h₀) R =
      circleAverage (log ‖f ·‖) 0 R - log ‖meromorphicTrailingCoeffAt f 0 (h₀ 0 (mem_univ 0))‖ := by
  rw [MeromorphicOn.circleAverage_log_norm hR h.meromorphicOn fun z _ ↦ h₀ z (mem_univ z)]
  simp only [logCounting, AddMonoidHom.coe_mk, ZeroHom.coe_mk, zero_sub, norm_neg,
    add_sub_cancel_right]
  congr 1
  · simp [toClosedBall_apply]
  · rw [divisor_apply _ (mem_univ 0), divisor_apply _ (mem_closedBall_self (abs_nonneg R))]

/--
Variant of `locallyFinsuppWithin.logCounting_divisor_eq_circleAverage_sub_const`, using
`ValueDistribution.logCounting` instead of `locallyFinsuppWithin.logCounting`.
-/
theorem ValueDistribution.logCounting_zero_sub_logCounting_top_eq_circleAverage_sub_const {R : ℝ}
    {f : ℂ → ℂ} (h : Meromorphic f) (ha : ∀ z, ∃ᶠ w in 𝓝[≠] z, (f w : WithTop ℂ) ≠ 0)
    (hR : R ≠ 0) :
    (logCounting f 0 h ha - logCounting f ⊤ h) R = circleAverage (log ‖f ·‖) 0 R -
      log ‖meromorphicTrailingCoeffAt f 0 ((frequently_coe_ne_zero_iff (h 0)).1 (ha 0))‖ := by
  rw [← log_counting_zero_sub_logCounting_top h
    fun z _ ↦ (frequently_coe_ne_zero_iff (h z)).1 (ha z)]
  exact locallyFinsuppWithin.logCounting_divisor_eq_circleAverage_sub_const h _ hR
