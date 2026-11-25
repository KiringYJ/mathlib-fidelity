/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Kexing Ying
-/
module

public import Mathlib.MeasureTheory.Function.UniformIntegrable
public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym

import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!

# Bounds for conditional expectations

This file proves that conditional expectations preserve almost everywhere bounds and do not increase
`Lᵖ` norms, `1 ≤ p`, and that a Radon-Nikodym derivative is a conditional expectation of a
real-valued integrable function.

## Main results

* `MeasureTheory.isCondExp_rnDeriv_withDensityᵥ`: the Radon-Nikodym derivative of `fμ` restricted
  to `m` with respect to `μ` restricted to `m` is a conditional expectation of `f` given `m`.
* `MeasureTheory.IsCondExp.ae_le_const`, `MeasureTheory.IsCondExp.ae_abs_le_const`,
  `MeasureTheory.IsCondExp.ae_norm_le_const`: a conditional expectation of an integrable function
  satisfies the almost everywhere bounds of the function by constants.
* `MeasureTheory.IsCondExp.integral_norm_rpow_le`, `MeasureTheory.IsCondExp.memLp`,
  `MeasureTheory.IsCondExp.eLpNorm_le`: a conditional expectation of an integrable function does not
  increase its `Lᵖ` norm.
* `MeasureTheory.Integrable.uniformIntegrable_condExp`: the conditional expectations of an
  integrable function given a family of sub-σ-algebras form a uniformly integrable family.

The bounds do not assume that the measure is σ-finite on the sub-σ-algebra: a conditional
expectation of an integrable function vanishes outside a set of `m` on which the measure is
σ-finite (`MeasureTheory.exists_mem_sigmaFinite_trim_restrict`). The Radon-Nikodym statement
assumes this σ-finiteness, and the uniform integrability a finite measure.

-/

public section


noncomputable section

open ENNReal Filter

open scoped NNReal

namespace MeasureTheory

variable {α : Type*} {m m0 : SigmaAlgebra α} {μ : Measure α}

/-- The Radon-Nikodym derivative of `fμ` restricted to `m` with respect to `μ` restricted to `m` is
a conditional expectation of an integrable `f` given `m`. -/
theorem isCondExp_rnDeriv_withDensityᵥ (hm : m ≤ m0) [SigmaFinite (μ.trim hm)] {f : α → ℝ}
    (hf : Integrable f μ) :
    IsCondExp m μ f (SignedMeasure.rnDeriv ((μ.withDensityᵥ f hf).trim hm) (μ.trim hm)) := by
  refine isCondExp_of_forall_setIntegral_eq hm hf ?_ ?_ ?_
  · exact fun _ _ _ => (integrable_of_integrable_trim hm
      (SignedMeasure.integrable_rnDeriv ((μ.withDensityᵥ f hf).trim hm) (μ.trim hm))).integrableOn
  · intro s hs _
    conv_rhs => rw [← hf.withDensityᵥ_trim_eq_integral hm hs,
      ← SignedMeasure.withDensityᵥ_rnDeriv_eq ((μ.withDensityᵥ f hf).trim hm) (μ.trim hm)
        (hf.withDensityᵥ_trim_absolutelyContinuous hm)]
    rw [withDensityᵥ_apply
      (SignedMeasure.integrable_rnDeriv ((μ.withDensityᵥ f hf).trim hm) (μ.trim hm)) hs,
      ← setIntegral_trim hm _ hs]
    exact (SignedMeasure.measurable_rnDeriv _ _).stronglyMeasurable
  · exact (SignedMeasure.measurable_rnDeriv _ _).stronglyMeasurable.aestronglyMeasurable

section Support

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {f g : α → E}

/-- A conditional expectation of an integrable function given a sub-σ-algebra `m` is almost
everywhere equal to its indicator on a set of `m` on which `μ` is σ-finite. -/
private theorem IsCondExp.exists_ae_eq_indicator (hm : m ≤ m0) (h : IsCondExp m μ f g)
    (hf : Integrable f μ) :
    ∃ t ∈ m, SigmaFinite ((μ.restrict t).trim hm) ∧ g =ᵐ[μ] t.indicator g := by
  obtain ⟨t, ht, hσ, hgt⟩ :=
    exists_mem_sigmaFinite_trim_restrict hm (h.integrable hf) h.aestronglyMeasurable
  refine ⟨t, ht, hσ, ?_⟩
  filter_upwards [(ae_restrict_iff' (MeasurableSet.compl (hm ht))).1 hgt] with x hx
  by_cases hxt : x ∈ t
  · simp [hxt]
  · simp [hxt, hx hxt]

end Support

section Order

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [PartialOrder E]
  [ClosedIciTopology E] [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] {f g : α → E}

/-- A conditional expectation of an integrable function bounded above almost everywhere by a
constant is bounded above by it. -/
theorem IsCondExp.ae_le_const (hm : m ≤ m0) (h : IsCondExp m μ f g) (hf : Integrable f μ) {c : E}
    (hfc : ∀ᵐ x ∂μ, f x ≤ c) : ∀ᵐ x ∂μ, g x ≤ c := by
  have h_closed : IsClosed (Set.Iic c) := by
    have : Set.Iic c = (fun x ↦ c - x) ⁻¹' Set.Ici 0 := by ext x; simp
    rw [this]
    exact isClosed_Ici.preimage (continuous_const.sub continuous_id)
  exact Convex.condExp_mem hm hf h_closed (convex_Iic c) hfc h

/-- A conditional expectation of an integrable function bounded below almost everywhere by a
constant is bounded below by it. -/
theorem IsCondExp.ae_const_le (hm : m ≤ m0) (h : IsCondExp m μ f g) (hf : Integrable f μ) {c : E}
    (hfc : ∀ᵐ x ∂μ, c ≤ f x) : ∀ᵐ x ∂μ, c ≤ g x := by
  filter_upwards [h.neg.ae_le_const hm hf.neg (c := -c) (hfc.mono fun x hx ↦ by simpa using hx)]
    with x hx
  simpa using hx

end Order

section Lattice

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Lattice E]
  [HasSolidNorm E] [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] {f g k : α → E}

/-- The absolute value of a conditional expectation of an integrable function is bounded by a
conditional expectation of the absolute value of the function. -/
theorem IsCondExp.abs_le (hm : m ≤ m0) (h : IsCondExp m μ f g)
    (hk : IsCondExp m μ (fun x ↦ |f x|) k) (hf : Integrable f μ) : ∀ᵐ x ∂μ, |g x| ≤ k x := by
  filter_upwards [h.mono hm hk hf hf.abs (.of_forall fun x ↦ le_abs_self (f x)),
    h.neg.mono hm hk hf.neg hf.abs (.of_forall fun x ↦ neg_le_abs (f x))] with x hx hx'
  exact abs_le'.2 ⟨hx, hx'⟩

/-- The integral of the absolute value of a conditional expectation of an integrable function is at
most that of the absolute value of the function. -/
theorem IsCondExp.integral_abs_le (hm : m ≤ m0) (h : IsCondExp m μ f g) (hf : Integrable f μ) :
    ∫ x, |g x| ∂μ ≤ ∫ x, |f x| ∂μ := by
  obtain ⟨t, ht, hσ, hgt⟩ := h.exists_ae_eq_indicator hm hf
  obtain ⟨k, -, hk⟩ := exists_stronglyMeasurable_isCondExp (μ := μ.restrict t) hm hf.abs.restrict
  calc ∫ x, |g x| ∂μ = ∫ x in t, |g x| ∂μ := by
        rw [← integral_indicator (hm ht)]
        refine integral_congr_ae (hgt.mono fun x hx ↦ ?_)
        by_cases hxt : x ∈ t
        · simp [hxt]
        · rw [Set.indicator_of_notMem hxt] at hx
          simp [hxt, hx]
    _ ≤ ∫ x in t, k x ∂μ :=
        integral_mono_ae (h.integrable hf).abs.restrict (hk.integrable hf.abs.restrict)
          ((h.restrict hm ht).abs_le hm hk hf.restrict)
    _ = ∫ x in t, |f x| ∂μ := hk.integral_eq hf.abs.restrict
    _ ≤ ∫ x, |f x| ∂μ := setIntegral_le_integral hf.abs (.of_forall fun x ↦ abs_nonneg (f x))

/-- The integral over a set of `m` of the absolute value of a conditional expectation of an
integrable function is at most that of the absolute value of the function. -/
theorem IsCondExp.setIntegral_abs_le (hm : m ≤ m0) (h : IsCondExp m μ f g) (hf : Integrable f μ)
    {s : Set α} (hs : s ∈ m) : ∫ x in s, |g x| ∂μ ≤ ∫ x in s, |f x| ∂μ :=
  (h.restrict hm hs).integral_abs_le hm hf.restrict

/-- If `|f|` is bounded almost everywhere by `R`, then so is the absolute value of a conditional
expectation of `f`. -/
theorem IsCondExp.ae_abs_le_const (hm : m ≤ m0) (h : IsCondExp m μ f g) (hf : Integrable f μ)
    {R : E} (hbdd : ∀ᵐ x ∂μ, |f x| ≤ R) : ∀ᵐ x ∂μ, |g x| ≤ R := by
  filter_upwards [h.ae_le_const hm hf (hbdd.mono fun x hx ↦ (le_abs_self (f x)).trans hx),
    h.neg.ae_le_const hm hf.neg (hbdd.mono fun x hx ↦ (neg_le_abs (f x)).trans hx)] with x hx hx'
  exact abs_le'.2 ⟨hx, hx'⟩

end Lattice

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {f g : α → E}

/-- If `‖f‖` is bounded almost everywhere by `R`, then so is the norm of a conditional expectation
of `f`. -/
theorem IsCondExp.ae_norm_le_const (hm : m ≤ m0) (h : IsCondExp m μ f g) (hf : Integrable f μ)
    {R : ℝ} (hbdd : ∀ᵐ x ∂μ, ‖f x‖ ≤ R) : ∀ᵐ x ∂μ, ‖g x‖ ≤ R := by
  filter_upwards [Convex.condExp_mem hm hf Metric.isClosed_closedBall (convex_closedBall 0 R)
    (hbdd.mono fun x hx ↦ mem_closedBall_zero_iff.2 hx) h] with x hx
  exact mem_closedBall_zero_iff.1 hx

theorem IsCondExp.ae_norm_le_essSup (hm : m ≤ m0) (h : IsCondExp m μ f g) (hf : Integrable f μ)
    (hf' : MemLp f ∞ μ) : ∀ᵐ x ∂μ, ‖g x‖ ≤ essSup (‖f ·‖) μ :=
  h.ae_norm_le_const hm hf (ae_le_essSup ⟨_, ae_le_lpNorm_exponent_top hf'⟩)

theorem IsCondExp.essSup_norm_le [NeZero μ] (hm : m ≤ m0) (h : IsCondExp m μ f g)
    (hf : Integrable f μ) (hf' : MemLp f ∞ μ) :
    essSup (fun x ↦ ‖g x‖) μ ≤ essSup (fun x ↦ ‖f x‖) μ :=
  essSup_le_of_ae_le _ (h.ae_norm_le_essSup hm hf hf')
    (isCoboundedUnder_le_of_le _ (fun _ => norm_nonneg _))

/-- On a set of `m` on which `μ` is σ-finite, the `p`-th power of the norm of a conditional
expectation of `f`, `1 ≤ p`, is bounded by a conditional expectation of `‖f‖ ^ p`, which is
integrable. -/
private theorem IsCondExp.exists_norm_rpow_le {p : ℝ} (hp : 1 ≤ p) (hm : m ≤ m0)
    (h : IsCondExp m μ f g) (hf : Integrable f μ) (hfp : Integrable (fun x ↦ ‖f x‖ ^ p) μ) :
    ∃ t ∈ m, g =ᵐ[μ] t.indicator g ∧ ∃ k, IsCondExp m (μ.restrict t) (fun x ↦ ‖f x‖ ^ p) k ∧
      (fun x ↦ ‖g x‖ ^ p) ≤ᵐ[μ.restrict t] k := by
  obtain ⟨t, ht, hσ, hgt⟩ := h.exists_ae_eq_indicator hm hf
  obtain ⟨k, -, hk⟩ := exists_stronglyMeasurable_isCondExp (μ := μ.restrict t) hm hfp.restrict
  exact ⟨t, ht, hgt, k, hk, (h.restrict hm ht).norm_rpow_le hp hm hk hf.restrict hfp.restrict⟩

/-- The integral of the `p`-th power of the norm of a conditional expectation of an integrable
function `f`, `1 ≤ p`, is at most that of `‖f‖ ^ p`. -/
theorem IsCondExp.integral_norm_rpow_le {p : ℝ} (hp : 1 ≤ p) (hm : m ≤ m0)
    (h : IsCondExp m μ f g) (hf : Integrable f μ) (hfp : Integrable (fun x ↦ ‖f x‖ ^ p) μ) :
    ∫ x, ‖g x‖ ^ p ∂μ ≤ ∫ x, ‖f x‖ ^ p ∂μ := by
  obtain ⟨t, ht, hgt, k, hk, hgk⟩ := h.exists_norm_rpow_le hp hm hf hfp
  have hp0 : p ≠ 0 := by linarith
  calc ∫ x, ‖g x‖ ^ p ∂μ = ∫ x in t, ‖g x‖ ^ p ∂μ := by
        rw [← integral_indicator (hm ht)]
        refine integral_congr_ae (hgt.mono fun x hx ↦ ?_)
        by_cases hxt : x ∈ t
        · simp [hxt]
        · rw [Set.indicator_of_notMem hxt] at hx
          simp [hxt, hx, hp0]
    _ ≤ ∫ x in t, k x ∂μ :=
        integral_mono_of_nonneg (.of_forall fun x ↦ by positivity) (hk.integrable hfp.restrict) hgk
    _ = ∫ x in t, ‖f x‖ ^ p ∂μ := hk.integral_eq hfp.restrict
    _ ≤ ∫ x, ‖f x‖ ^ p ∂μ := setIntegral_le_integral hfp (.of_forall fun x ↦ by positivity)

/-- The integral of the norm of a conditional expectation of an integrable function is at most that
of the norm of the function. -/
theorem IsCondExp.integral_norm_le (hm : m ≤ m0) (h : IsCondExp m μ f g) (hf : Integrable f μ) :
    ∫ x, ‖g x‖ ∂μ ≤ ∫ x, ‖f x‖ ∂μ := by
  simpa using h.integral_norm_rpow_le le_rfl hm hf (by simpa using hf.norm)

theorem IsCondExp.setIntegral_norm_rpow_le {p : ℝ} (hp : 1 ≤ p) (hm : m ≤ m0)
    (h : IsCondExp m μ f g) (hf : Integrable f μ) (hfp : Integrable (fun x ↦ ‖f x‖ ^ p) μ)
    {s : Set α} (hs : s ∈ m) : ∫ x in s, ‖g x‖ ^ p ∂μ ≤ ∫ x in s, ‖f x‖ ^ p ∂μ :=
  (h.restrict hm hs).integral_norm_rpow_le hp hm hf.restrict hfp.restrict

theorem IsCondExp.setIntegral_norm_le (hm : m ≤ m0) (h : IsCondExp m μ f g) (hf : Integrable f μ)
    {s : Set α} (hs : s ∈ m) : ∫ x in s, ‖g x‖ ∂μ ≤ ∫ x in s, ‖f x‖ ∂μ :=
  (h.restrict hm hs).integral_norm_le hm hf.restrict

/-- A conditional expectation of an integrable function in `Lᵖ`, `1 ≤ p`, is in `Lᵖ`. -/
theorem IsCondExp.memLp {p : ℝ≥0∞} (hp : 1 ≤ p) (hm : m ≤ m0) (h : IsCondExp m μ f g)
    (hf : Integrable f μ) (hf' : MemLp f p μ) : MemLp g p μ := by
  have hp' : 0 < p := zero_lt_one.trans_le hp
  have hg : AEStronglyMeasurable g μ := h.aestronglyMeasurable' hm
  by_cases! hpt : p = ⊤
  · subst hpt
    exact memLp_top_of_bound hg (essSup (‖f ·‖) μ) (h.ae_norm_le_essSup hm hf hf')
  have hp1 : 1 ≤ p.toReal := by rwa [← toReal_one, toReal_le_toReal one_ne_top hpt]
  have hp0 : p.toReal ≠ 0 := by linarith
  have hfp : Integrable (fun x ↦ ‖f x‖ ^ p.toReal) μ :=
    (integrable_norm_rpow_iff hf.1 hp'.ne' hpt).2 hf'
  obtain ⟨t, ht, hgt, k, hk, hgk⟩ := h.exists_norm_rpow_le hp1 hm hf hfp
  rw [← integrable_norm_rpow_iff hg hp'.ne' hpt]
  have h_on : IntegrableOn (fun x ↦ ‖g x‖ ^ p.toReal) t μ :=
    (hk.integrable hfp.restrict).mono_nonneg
      (hg.norm.aemeasurable.pow_const _).aestronglyMeasurable.restrict
      (.of_forall fun x ↦ by positivity) hgk
  refine (h_on.integrable_indicator (hm ht)).congr (hgt.mono fun x hx ↦ ?_)
  by_cases hxt : x ∈ t
  · simp [hxt]
  · rw [Set.indicator_of_notMem hxt] at hx
    simp [hxt, hx, hp0]

/-- A conditional expectation of an integrable function in `Lᵖ`, `1 ≤ p`, has at most its `Lᵖ`
norm. -/
theorem IsCondExp.lpNorm_le {p : ℝ≥0∞} (hp : 1 ≤ p) (hm : m ≤ m0) (h : IsCondExp m μ f g)
    (hf : Integrable f μ) (hf' : MemLp f p μ) : lpNorm g p μ ≤ lpNorm f p μ := by
  rcases eq_zero_or_neZero μ with rfl | hμ
  · simp
  have hp' : 0 < p := zero_lt_one.trans_le hp
  by_cases! hpt : p = ⊤
  · subst hpt
    rw [lpNorm_exponent_top_eq_essSup hf', lpNorm_exponent_top_eq_essSup (h.memLp hp hm hf hf')]
    exact h.essSup_norm_le hm hf hf'
  rw [lpNorm_eq_integral_norm_rpow_toReal hp'.ne' hpt hf'.1,
    lpNorm_eq_integral_norm_rpow_toReal hp'.ne' hpt (h.aestronglyMeasurable' hm)]
  gcongr ?_ ^ ?_
  have : 1 ≤ p.toReal := by rwa [← toReal_one, toReal_le_toReal one_ne_top hpt]
  exact h.integral_norm_rpow_le this hm hf ((integrable_norm_rpow_iff hf'.1 hp'.ne' hpt).2 hf')

/-- A conditional expectation of an integrable function has at most its `Lᵖ` seminorm, `1 ≤ p`. -/
theorem IsCondExp.eLpNorm_le {p : ℝ≥0∞} (hp : 1 ≤ p) (hm : m ≤ m0) (h : IsCondExp m μ f g)
    (hf : Integrable f μ) : eLpNorm g p μ ≤ eLpNorm f p μ := by
  by_cases! hf' : MemLp f p μ
  · rw [← ofReal_lpNorm hf', ← ofReal_lpNorm (h.memLp hp hm hf hf')]
    exact ofReal_le_ofReal (h.lpNorm_le hp hm hf hf')
  · have : eLpNorm f p μ = ∞ := top_le_iff.1 (not_lt.1 fun h ↦ hf' ⟨hf.1, h⟩)
    simp [this]

end NormedSpace

/-- The conditional expectations of an integrable function `g` given a family of sub-σ-algebras form
a uniformly integrable family. -/
theorem Integrable.uniformIntegrable_condExp {ι : Type*} [IsFiniteMeasure μ] {g : α → ℝ}
    (hint : Integrable g μ) {ℱ : ι → SigmaAlgebra α} (hℱ : ∀ i, ℱ i ≤ m0) {G : ι → α → ℝ}
    (hG : ∀ i, IsCondExp (ℱ i) μ g (G i)) : UniformIntegrable G 1 μ := by
  -- it suffices to treat `ℱ i`-strongly measurable versions
  let G' (i : ι) : α → ℝ := (hG i).aestronglyMeasurable.mk (G i)
  have hG'm (i : ι) : StronglyMeasurable[ℱ i] (G' i) :=
    (hG i).aestronglyMeasurable.stronglyMeasurable_mk
  have hGG' (i : ι) : G i =ᵐ[μ] G' i := (hG i).aestronglyMeasurable.ae_eq_mk
  have hG' (i : ι) : IsCondExp (ℱ i) μ g (G' i) := (hG i).congr_right (hGG' i)
  refine (uniformIntegrable_congr_ae hGG').2 ?_
  let A : SigmaAlgebra α := m0
  have hmeas : ∀ n, ∀ C, MeasurableSet {x | C ≤ ‖G' n x‖₊} := fun n C =>
    measurableSet_le measurable_const ((hG'm n).mono (hℱ n)).measurable.nnnorm
  have hg : MemLp g 1 μ := memLp_one_iff_integrable.2 hint
  refine uniformIntegrable_of le_rfl one_ne_top
    (fun n => ((hG'm n).mono (hℱ n)).aestronglyMeasurable) fun ε hε => ?_
  rcases eq_zero_or_pos (eLpNorm g 1 μ) with hne | hne
  · rw [eLpNorm_eq_zero_iff hg.1 one_ne_zero] at hne
    refine ⟨0, fun n => (le_of_eq <|
      (eLpNorm_eq_zero_iff (((hG'm n).mono (hℱ n)).aestronglyMeasurable.indicator
        (hmeas n 0)) one_ne_zero).2 ?_).trans zero_le⟩
    filter_upwards [(hG' n).ae_eq (hℱ n) hint (IsCondExp.zero.congr_left hne.symm)] with x hx
    simp [hx]
  obtain ⟨δ, hδ, h⟩ := hg.eLpNorm_indicator_le le_rfl one_ne_top hε
  rcases eq_top_or_lt_top δ with rfl | hδ_top
  · refine ⟨0, fun i ↦ ?_⟩
    specialize h .univ
    simp only [zero_le, Set.ofPred_true, Set.indicator_univ, MeasurableSet.univ, le_top,
      forall_const] at h ⊢
    exact ((hG' i).eLpNorm_le le_rfl (hℱ i) hint).trans h
  set C : ℝ≥0 := δ⁻¹.toNNReal * (eLpNorm g 1 μ).toNNReal with hC
  have hCpos : 0 < C := _root_.mul_pos (toNNReal_pos (ENNReal.inv_ne_zero.2 hδ_top.ne)
    (inv_ne_top.2 hδ.ne')) (toNNReal_pos hne.ne' hg.2.ne)
  have : ∀ n, μ {x : α | C ≤ ‖G' n x‖₊} ≤ δ := by
    intro n
    have : C ^ ENNReal.toReal 1 * μ {x | ENNReal.ofNNReal C ≤ ‖G' n x‖₊} ≤
        eLpNorm (G' n) 1 μ ^ ENNReal.toReal 1 := by
      rw [toReal_one, rpow_one]
      convert!
        mul_meas_ge_le_pow_eLpNorm μ one_ne_zero one_ne_top
          ((hG'm n).mono (hℱ n)).aestronglyMeasurable C
      · rw [toReal_one, rpow_one, enorm_eq_nnnorm]
    have hc₀ : (C : ℝ≥0∞) ≠ 0 := coe_ne_zero.2 hCpos.ne'
    rw [toReal_one, rpow_one, mul_comm, ← ENNReal.le_div_iff_mul_le
        ⟨hc₀, .inr coe_ne_top⟩] at this
    simp_rw [coe_le_coe] at this
    refine this.trans ?_
    rw [ENNReal.div_le_iff hc₀ coe_ne_top,
      hC, ← toNNReal_mul, coe_toNNReal (mul_ne_top (inv_ne_top.2 hδ.ne') hg.2.ne),
      ← mul_assoc, ENNReal.mul_inv_cancel hδ.ne' hδ_top.ne, one_mul, rpow_one]
    exact (hG' n).eLpNorm_le le_rfl (hℱ n) hint
  refine ⟨C, fun n => le_trans ?_ (h {x : α | C ≤ ‖G' n x‖₊} (hmeas n C) (this n))⟩
  have hmeasℱ : {x : α | C ≤ ‖G' n x‖₊} ∈ ℱ n :=
    @measurableSet_le _ _ _ _ _ (ℱ n) _ _ _ _ _ measurable_const
      (@Measurable.nnnorm _ _ _ _ _ (ℱ n) _ (hG'm n).measurable)
  exact ((hG' n).indicator (hℱ n) hmeasℱ).eLpNorm_le le_rfl (hℱ n)
    (hint.indicator (hℱ n hmeasℱ))

end MeasureTheory
