/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL1
public import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
public import Mathlib.Order.Filter.Germ.Representative
public import Mathlib.Tactic.CrossRefAttribute

import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Conditional expectation

Given a measure `μ` on a σ-algebra `m₀` and a σ-algebra `m`, a function `g` is a conditional
expectation of `f : α → E` given `m`, written `IsCondExp m μ f g`, when `g` is almost everywhere
`m`-strongly measurable and, on each set of `m` on which `f` is integrable, `g` is integrable with
the same integral. For an integrable `f` this is Kolmogorov's definition: `g` is integrable and
`∫ x in s, g x ∂μ = ∫ x in s, f x ∂μ` for all `s ∈ m`. Stating the identity only on the sets where
`f` is integrable also covers functions that are integrable on each set of a sequence in `m`
exhausting the space, and makes the relation local: on a set of `m`, a conditional expectation of
`f` restricts to one of the restriction of `f`. For a function that is integrable on no set of `m`
of positive measure, every almost everywhere `m`-strongly measurable function satisfies the
relation, so the conditional expectations are unique only for the functions of the domain
`HasUniqueCondExp`.

A conditional expectation is determined only up to almost everywhere equality. The conditional
expectation `μ[f | m] = condExp m μ f` is therefore the almost everywhere class of the conditional
expectations of `f`, a germ along `ae μ`. A function `g` represents it, written `g ∈ μ[f | m]`,
exactly when `IsCondExp m μ f g` (`MeasureTheory.mem_condExp_iff`). Statements about conditional
expectations are mostly stated for the representatives, through `IsCondExp`, and `μ[f | m]` names
their common class.

## Domain

`condExp m μ f` takes a proof of `HasUniqueCondExp m μ f`: the sets of `m` are null-measurable for
`μ`, a conditional expectation of `f` exists, and any two agree almost everywhere. The sets of `m`
must be null-measurable because on a set that is not, the restricted measure in the defining
identity follows the outer-measure convention of `Measure.restrict`, on which the specification
would then depend. On the null-measurable σ-algebras, this is the exact domain of the conditional
expectation, and it depends on `f`. The tactic `has_unique_cond_exp`
finds it from a hypothesis or from the sufficient condition `HasUniqueCondExp.of_integrable`: an
integrable `f` and a sub-σ-algebra `hm : m ≤ m₀` on which `μ` is σ-finite, which instance search
finds, for example from a finite measure. The tactics `sub_sigma_algebra` and `integrability` prove
the last two hypotheses. A conditional expectation of an integrable function given a sub-σ-algebra
is unique without σ-finiteness (`MeasureTheory.IsCondExp.ae_eq`), so a known conditional expectation
also supplies the domain (`HasUniqueCondExp.of_isCondExp`).

The codomain `E` is a complete normed space. The defining identity compares Bochner integrals,
which are only meaningful in a complete space; for an incomplete codomain a conditional expectation
need not exist, so completeness is a sufficient condition for the integrals rather than part of the
exact domain.

## Main definitions

* `MeasureTheory.IsCondExp m μ f g`: `g` is a conditional expectation of `f` given `m`.
* `MeasureTheory.HasUniqueCondExp m μ f`: `f` has a conditional expectation given `m`, unique almost
  everywhere. This is the exact domain of `condExp`.
* `MeasureTheory.condExp m μ f`, with notation `μ[f | m]`: the almost everywhere class of the
  conditional expectations of `f`.

## Main results

* `MeasureTheory.exists_stronglyMeasurable_isCondExp`: an integrable function has an `m`-strongly
  measurable conditional expectation given a sub-σ-algebra `m` on which `μ` is σ-finite.
* `MeasureTheory.IsCondExp.ae_eq`: conditional expectations of an integrable function given a
  sub-σ-algebra agree almost everywhere.
* `MeasureTheory.IsCondExp.trans`: the tower property.
* `MeasureTheory.IsCondExp.add`, `MeasureTheory.IsCondExp.smul`, `MeasureTheory.IsCondExp.tsum`,
  `MeasureTheory.IsCondExp.of_tendsto` and `MeasureTheory.IsCondExp.mono`: linearity, countable
  additivity, dominated convergence and monotonicity.
* `MeasureTheory.IsCondExp.exists_isCondExp_of_nonneg_of_le`: an integrable function between `0`
  and an integrable function with a conditional expectation has a nonnegative one, without
  σ-finiteness.

## Implementation notes

The construction is done in four steps:
* Define the conditional expectation of an `L²` function, as an element of `L²`. This is the
  orthogonal projection on the subspace of almost everywhere `m`-measurable functions.
* Show that the conditional expectation of the indicator of a measurable set with finite measure
  is integrable, and define for each such set a continuous linear map `condExpInd` from `E` to
  `α →₁[μ] E`, which sends `x` to the conditional expectation of the indicator of the set with value
  `x`.
* Extend these maps to `condExpL1CLM : (α →₁[μ] E) →L[ℝ] (α →₁[μ] E)`. This is done using the same
  construction as the Bochner integral (see the file `MeasureTheory/Integral/SetToL1`).
* For an integrable `f`, the representatives of `condExpL1CLM` applied to the class of `f` in `L¹`
  are conditional expectations of `f` (`MeasureTheory.isCondExp_condExpL1CLM`), which proves their
  existence.

The first step is done in `MeasureTheory.Function.ConditionalExpectation.CondexpL2`, the two
next steps in `MeasureTheory.Function.ConditionalExpectation.CondexpL1` and the final step is
performed in this file.

## Tags

conditional expectation, conditional expected value

-/

@[expose] public section

open TopologicalSpace MeasureTheory.Lp Filter
open scoped ENNReal Topology MeasureTheory

namespace MeasureTheory

/-- `integrability` proves `Integrable f μ`: it tries a hypothesis, then `fun_prop`, whose side
conditions of measurability it proves from hypotheses, then the integrability of the indicator of
a set of finite measure, null-measurable by a hypothesis about it or about its complement. Later
files extend it with `macro_rules`. -/
syntax (name := integrability) "integrability" : tactic

macro_rules
  | `(tactic| integrability) => `(tactic| first
    | done
    | assumption
    | fun_prop (disch := first
        | assumption
        | exact MeasurableSet.univ
        | exact MeasurableSet.empty
        | exact MeasureTheory.nullMeasurableSet_univ
        | exact MeasureTheory.nullMeasurableSet_empty
        | (apply MeasurableSet.nullMeasurableSet; assumption))
    | (refine MeasureTheory.IntegrableOn.integrable_indicator₀
          (MeasureTheory.integrableOn_const ?_) ?_
       · finiteness
       · first
         | assumption
         | (apply MeasurableSet.nullMeasurableSet; assumption)
         | (apply MeasureTheory.NullMeasurableSet.compl; assumption)
         | (apply MeasurableSet.nullMeasurableSet; apply MeasurableSet.compl; assumption))
    | fail "this function needs a proof that it is integrable")

variable {α β E F 𝕜 : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

section Definitions

/-- A function `g` is a conditional expectation of `f` given the σ-algebra `m` with respect to the
measure `μ`: `g` is almost everywhere `m`-strongly measurable and, on each set of `m` on which `f`
is integrable, `g` is integrable with the same integral.

For an integrable `f` this is Kolmogorov's definition. For other functions the relation constrains
`g` only on the sets of `m` on which `f` is integrable, and `MeasureTheory.HasUniqueCondExp` states
when it determines `g` almost everywhere. The integrals are Bochner integrals, so the codomain is
complete. -/
structure IsCondExp (m : SigmaAlgebra α) {m₀ : SigmaAlgebra α} (μ : Measure[m₀] α)
    [CompleteSpace E] (f g : α → E) : Prop where
  /-- A conditional expectation given `m` is almost everywhere `m`-strongly measurable. -/
  aestronglyMeasurable : AEStronglyMeasurable[m] g μ
  /-- A conditional expectation is integrable on each set of `m` on which `f` is. -/
  integrableOn : ∀ s ∈ m, IntegrableOn f s μ → IntegrableOn g s μ
  /-- A conditional expectation has the integral of `f` over each set of `m` on which `f` is
  integrable. -/
  setIntegral_eq : ∀ s ∈ m, IntegrableOn f s μ → ∫ x in s, g x ∂μ = ∫ x in s, f x ∂μ

/-- The function `f` has a conditional expectation given `m` with respect to `μ` that is unique
almost everywhere: the sets of `m` are null-measurable, a conditional expectation of `f` exists,
and any two agree almost everywhere.

The null-measurability excludes the sets on which the restricted measure in the defining identity
follows the outer-measure convention of `Measure.restrict`. With it, this is the exact domain of
`MeasureTheory.condExp`. The tactic `has_unique_cond_exp` derives it from the sufficient condition
`MeasureTheory.HasUniqueCondExp.of_integrable`. It is strictly larger:
for counting measure on a type with the discrete σ-algebra, every integrable function is its own
unique conditional expectation given the discrete σ-algebra, on which counting measure need not be
σ-finite. -/
structure HasUniqueCondExp (m : SigmaAlgebra α) {m₀ : SigmaAlgebra α} (μ : Measure[m₀] α)
    [CompleteSpace E] (f : α → E) : Prop where
  /-- The sets of `m` are null-measurable. -/
  le_eventuallySigmaAlgebra : m ≤ eventuallySigmaAlgebra m₀ (ae μ)
  /-- A conditional expectation exists. -/
  exists_isCondExp : ∃ g, IsCondExp m μ f g
  /-- Two conditional expectations agree almost everywhere. -/
  ae_eq_of_isCondExp ⦃g₁ g₂ : α → E⦄ : IsCondExp m μ f g₁ → IsCondExp m μ f g₂ → g₁ =ᵐ[μ] g₂

end Definitions

variable {m m₀ : SigmaAlgebra α} {μ : Measure α} {f f' g g' : α → E} {s : Set α}

/-! ### Conditional expectations as a relation -/

namespace IsCondExp

theorem congr_right (h : IsCondExp m μ f g) (hg : g =ᵐ[μ] g') : IsCondExp m μ f g' where
  aestronglyMeasurable := h.aestronglyMeasurable.congr hg
  integrableOn s hs hf := (h.integrableOn s hs hf).congr_fun_ae (ae_restrict_of_ae hg)
  setIntegral_eq s hs hf := by
    rw [← h.setIntegral_eq s hs hf]
    exact integral_congr_ae (ae_restrict_of_ae hg.symm)

theorem congr_left (h : IsCondExp m μ f g) (hf : f =ᵐ[μ] f') : IsCondExp m μ f' g where
  aestronglyMeasurable := h.aestronglyMeasurable
  integrableOn s hs hf' := h.integrableOn s hs (hf'.congr_fun_ae (ae_restrict_of_ae hf.symm))
  setIntegral_eq s hs hf' := by
    rw [h.setIntegral_eq s hs (hf'.congr_fun_ae (ae_restrict_of_ae hf.symm))]
    exact integral_congr_ae (ae_restrict_of_ae hf)

theorem congr (h : IsCondExp m μ f g) (hf : f =ᵐ[μ] f') (hg : g =ᵐ[μ] g') :
    IsCondExp m μ f' g' :=
  (h.congr_left hf).congr_right hg

theorem integrable (h : IsCondExp m μ f g) (hf : Integrable f μ) : Integrable g μ := by
  simpa only [integrableOn_univ] using h.integrableOn _ m.univ_mem hf.integrableOn

theorem integral_eq (h : IsCondExp m μ f g) (hf : Integrable f μ) :
    ∫ x, g x ∂μ = ∫ x, f x ∂μ := by
  simpa only [setIntegral_univ] using h.setIntegral_eq _ m.univ_mem hf.integrableOn

/-- A conditional expectation given a sub-σ-algebra is almost everywhere strongly measurable. -/
theorem aestronglyMeasurable' (hm : m ≤ m₀) (h : IsCondExp m μ f g) :
    AEStronglyMeasurable g μ :=
  (h.aestronglyMeasurable.stronglyMeasurable_mk.mono hm).aestronglyMeasurable.congr
    h.aestronglyMeasurable.ae_eq_mk.symm

/-- Two conditional expectations of an integrable function given a sub-σ-algebra agree almost
everywhere. No σ-finiteness is needed: their difference is integrable, so its support is σ-finite
for the restriction of `μ` to `m`. -/
theorem ae_eq (hm : m ≤ m₀) (hf : Integrable f μ) (h₁ : IsCondExp m μ f g)
    (h₂ : IsCondExp m μ f g') : g =ᵐ[μ] g' := by
  have hg := h₁.integrable hf
  have hg' := h₂.integrable hf
  obtain ⟨u, hu_meas, hu⟩ : AEStronglyMeasurable[m] (g - g') μ :=
    h₁.aestronglyMeasurable.sub h₂.aestronglyMeasurable
  have hu_trim : Integrable u (μ.trim hm) := ((hg.sub hg').congr hu).trim hm hu_meas
  have h0 : u =ᵐ[μ.trim hm] 0 := by
    refine hu_trim.ae_eq_zero_of_forall_setIntegral_eq_zero fun t ht _ ↦ ?_
    have ht' : t ∈ m := measurableSet_iff_mem.mp ht
    rw [← setIntegral_trim hm hu_meas ht,
      setIntegral_congr_ae (hm ht') (hu.mono fun x hx _ ↦ hx.symm)]
    simp only [Pi.sub_apply]
    rw [integral_sub hg.integrableOn hg'.integrableOn, h₁.setIntegral_eq t ht' hf.integrableOn,
      h₂.setIntegral_eq t ht' hf.integrableOn, sub_self]
  filter_upwards [hu.trans (ae_eq_of_ae_eq_trim h0)] with x hx
  simpa [sub_eq_zero] using hx

theorem zero : IsCondExp m μ (0 : α → E) 0 :=
  ⟨aestronglyMeasurable_zero, fun _ _ _ ↦ integrableOn_zero, fun _ _ _ ↦ rfl⟩

theorem smul [NormedSpace 𝕜 E] [SMulCommClass ℝ 𝕜 E] (h : IsCondExp m μ f g) (c : 𝕜) :
    IsCondExp m μ (c • f) (c • g) := by
  rcases eq_or_ne c 0 with rfl | hc
  · simpa only [zero_smul] using zero
  refine ⟨h.aestronglyMeasurable.const_smul c, fun s hs hf ↦ ?_, fun s hs hf ↦ ?_⟩
  · exact (h.integrableOn s hs ((integrable_smul_iff hc f).1 hf)).smul c
  · simp only [Pi.smul_apply]
    rw [integral_smul, integral_smul, h.setIntegral_eq s hs ((integrable_smul_iff hc f).1 hf)]

theorem neg (h : IsCondExp m μ f g) : IsCondExp m μ (-f) (-g) := by
  simpa only [neg_one_smul] using h.smul (-1 : ℝ)

theorem add (h : IsCondExp m μ f g) (h' : IsCondExp m μ f' g') (hf : Integrable f μ)
    (hf' : Integrable f' μ) : IsCondExp m μ (f + f') (g + g') where
  aestronglyMeasurable := h.aestronglyMeasurable.add h'.aestronglyMeasurable
  integrableOn s hs _ :=
    (h.integrableOn s hs hf.integrableOn).add (h'.integrableOn s hs hf'.integrableOn)
  setIntegral_eq s hs _ := by
    simp only [Pi.add_apply]
    rw [integral_add (h.integrableOn s hs hf.integrableOn) (h'.integrableOn s hs hf'.integrableOn),
      integral_add hf.integrableOn hf'.integrableOn, h.setIntegral_eq s hs hf.integrableOn,
      h'.setIntegral_eq s hs hf'.integrableOn]

theorem sub (h : IsCondExp m μ f g) (h' : IsCondExp m μ f' g') (hf : Integrable f μ)
    (hf' : Integrable f' μ) : IsCondExp m μ (f - f') (g - g') := by
  simpa only [sub_eq_add_neg] using h.add h'.neg hf hf'.neg

theorem finsetSum {ι : Type*} {t : Finset ι} {f g : ι → α → E}
    (h : ∀ i ∈ t, IsCondExp m μ (f i) (g i)) (hf : ∀ i ∈ t, Integrable (f i) μ) :
    IsCondExp m μ (∑ i ∈ t, f i) (∑ i ∈ t, g i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using zero
  | insert i t hit ih =>
    rw [Finset.sum_insert hit, Finset.sum_insert hit]
    exact (h i (Finset.mem_insert_self i t)).add
      (ih (fun j hj ↦ h j (Finset.mem_insert_of_mem hj))
        (fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)))
      (hf i (Finset.mem_insert_self i t)) (integrable_finsetSum' t fun j hj ↦
        hf j (Finset.mem_insert_of_mem hj))

/-- **Tower property**: a conditional expectation given `m₁ ≤ m₂` of a conditional expectation
given `m₂` is a conditional expectation given `m₁`. -/
theorem trans {m₁ m₂ : SigmaAlgebra α} {k : α → E} (h₂ : IsCondExp m₂ μ f g)
    (h₁ : IsCondExp m₁ μ g k) (h₁₂ : m₁ ≤ m₂) : IsCondExp m₁ μ f k where
  aestronglyMeasurable := h₁.aestronglyMeasurable
  integrableOn s hs hf := h₁.integrableOn s hs (h₂.integrableOn s (h₁₂ hs) hf)
  setIntegral_eq s hs hf := by
    rw [h₁.setIntegral_eq s hs (h₂.integrableOn s (h₁₂ hs) hf), h₂.setIntegral_eq s (h₁₂ hs) hf]

/-- The converse of the tower property: conditional expectations `g` given `m₂` and `k` given
`m₁ ≤ m₂` of an integrable function make `k` a conditional expectation of `g` given `m₁`. -/
theorem of_trans {m₁ m₂ : SigmaAlgebra α} {k : α → E} (h₁₂ : m₁ ≤ m₂) (hf : Integrable f μ)
    (h₂ : IsCondExp m₂ μ f g) (h₁ : IsCondExp m₁ μ f k) : IsCondExp m₁ μ g k where
  aestronglyMeasurable := h₁.aestronglyMeasurable
  integrableOn _ _ _ := (h₁.integrable hf).integrableOn
  setIntegral_eq s hs _ := by
    rw [h₁.setIntegral_eq s hs hf.integrableOn, h₂.setIntegral_eq s (h₁₂ hs) hf.integrableOn]

/-- Conditional expectation commutes with continuous linear maps. -/
theorem comp_continuousLinearMap (h : IsCondExp m μ f g) (hf : Integrable f μ) (T : E →L[ℝ] F) :
    IsCondExp m μ (T ∘ f) (T ∘ g) where
  aestronglyMeasurable := T.continuous.comp_aestronglyMeasurable h.aestronglyMeasurable
  integrableOn s hs _ := T.integrable_comp (h.integrableOn s hs hf.integrableOn)
  setIntegral_eq s hs _ := by
    simp only [Function.comp_apply]
    rw [T.integral_comp_comm (h.integrableOn s hs hf.integrableOn),
      T.integral_comp_comm hf.integrableOn, h.setIntegral_eq s hs hf.integrableOn]

/-- **Dominated convergence**: if `G n` is a conditional expectation of `F n` for every `n`, and
`F n` and `G n` converge almost everywhere to `f` and `g` with integrable bounds, then the almost
everywhere `m`-strongly measurable `g` is a conditional expectation of `f`. -/
theorem of_tendsto (hm : m ≤ m₀) {F G : ℕ → α → E} (hFG : ∀ n, IsCondExp m μ (F n) (G n))
    (hF_meas : ∀ n, AEStronglyMeasurable (F n) μ) (bF : α → ℝ) (hbF : Integrable bF μ)
    (hF_bound : ∀ n, ∀ᵐ x ∂μ, ‖F n x‖ ≤ bF x)
    (hF : ∀ᵐ x ∂μ, Tendsto (fun n ↦ F n x) atTop (𝓝 (f x))) (bG : α → ℝ) (hbG : Integrable bG μ)
    (hG_bound : ∀ n, ∀ᵐ x ∂μ, ‖G n x‖ ≤ bG x)
    (hG : ∀ᵐ x ∂μ, Tendsto (fun n ↦ G n x) atTop (𝓝 (g x))) (hgm : AEStronglyMeasurable[m] g μ) :
    IsCondExp m μ f g := by
  have hF_int n : Integrable (F n) μ := hbF.mono' (hF_meas n) (hF_bound n)
  have hG_meas n : AEStronglyMeasurable (G n) μ := (hFG n).aestronglyMeasurable' hm
  have hf_meas : AEStronglyMeasurable f μ := aestronglyMeasurable_of_tendsto_ae _ hF_meas hF
  have hf_bound : ∀ᵐ x ∂μ, ‖f x‖ ≤ bF x := by
    filter_upwards [hF, ae_all_iff.2 hF_bound] with x hx hxb
    exact le_of_tendsto' (continuous_norm.tendsto _ |>.comp hx) hxb
  have hg_bound : ∀ᵐ x ∂μ, ‖g x‖ ≤ bG x := by
    filter_upwards [hG, ae_all_iff.2 hG_bound] with x hx hxb
    exact le_of_tendsto' (continuous_norm.tendsto _ |>.comp hx) hxb
  have hg_int : Integrable g μ :=
    hbG.mono' ((hgm.stronglyMeasurable_mk.mono hm).aestronglyMeasurable.congr hgm.ae_eq_mk.symm)
      hg_bound
  refine ⟨hgm, fun s _ _ ↦ hg_int.integrableOn, fun s hs _ ↦ ?_⟩
  have h_lim_G := tendsto_integral_of_dominated_convergence (μ := μ.restrict s) bG
    (fun n ↦ (hG_meas n).restrict) hbG.integrableOn (fun n ↦ ae_restrict_of_ae (hG_bound n))
    (ae_restrict_of_ae hG)
  have h_lim_F := tendsto_integral_of_dominated_convergence (μ := μ.restrict s) bF
    (fun n ↦ (hF_meas n).restrict) hbF.integrableOn (fun n ↦ ae_restrict_of_ae (hF_bound n))
    (ae_restrict_of_ae hF)
  simp_rw [fun n ↦ (hFG n).setIntegral_eq s hs (hF_int n).integrableOn] at h_lim_G
  exact tendsto_nhds_unique h_lim_G h_lim_F

end IsCondExp

/-- An almost everywhere `m`-strongly measurable function is a conditional expectation of itself
given `m`. -/
theorem isCondExp_self (hf : AEStronglyMeasurable[m] f μ) : IsCondExp m μ f f :=
  ⟨hf, fun _ _ h ↦ h, fun _ _ _ ↦ rfl⟩

/-- A constant function is a conditional expectation of itself. -/
theorem isCondExp_const (c : E) : IsCondExp m μ (fun _ ↦ c) fun _ ↦ c :=
  isCondExp_self aestronglyMeasurable_const

/-- Given the trivial σ-algebra, the conditional expectation of an integrable function for a finite
measure is the constant function equal to its mean. For an infinite measure it exists only for
functions with integral zero. -/
theorem isCondExp_bot [IsFiniteMeasure μ] (hf : Integrable f μ) :
    IsCondExp ⊥ μ f fun _ ↦ (μ.real Set.univ)⁻¹ • ∫ x, f x ∂μ := by
  refine ⟨aestronglyMeasurable_const, fun _ _ _ ↦ integrableOn_const, fun s hs _ ↦ ?_⟩
  rcases SigmaAlgebra.mem_bot_iff.mp hs with rfl | rfl
  · simp
  rw [setIntegral_univ, setIntegral_univ, integral_const, smul_smul]
  rcases eq_zero_or_neZero μ with rfl | hμ
  · simp
  rw [mul_inv_cancel₀ (by simp [measureReal_def, ENNReal.toReal_eq_zero_iff,
    measure_ne_top μ Set.univ, NeZero.ne μ]), one_smul]

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- An integrable, almost everywhere `m`-strongly measurable function vanishes almost everywhere
outside a set of `m` on which the restriction of `μ` to `m` is σ-finite. This reduces statements
about conditional expectations of integrable functions to σ-finite sub-σ-algebras. -/
theorem exists_mem_sigmaFinite_trim_restrict (hm : m ≤ m₀) {g : α → E} (hg : Integrable g μ)
    (hgm : AEStronglyMeasurable[m] g μ) :
    ∃ t ∈ m, SigmaFinite ((μ.restrict t).trim hm) ∧ g =ᵐ[μ.restrict tᶜ] 0 := by
  obtain ⟨u, hu, hgu⟩ := hgm
  have hu_int : Integrable u (μ.trim hm) := (hg.congr hgu).trim hm hu
  obtain ⟨t, ht, hut, hσ⟩ := hu_int.aefinStronglyMeasurable.exists_set_sigmaFinite
  have ht' : t ∈ m := measurableSet_iff_mem.mp ht
  refine ⟨t, ht', by rwa [← restrict_trim hm μ ht'], ?_⟩
  rw [restrict_trim hm μ (m.compl_mem ht')] at hut
  exact EventuallyEq.trans (ae_restrict_of_ae hgu) (ae_eq_of_ae_eq_trim hut)

/-- The representatives of `condExpL1CLM` applied to the class of an integrable function in `L¹`
are conditional expectations of the function. -/
theorem isCondExp_condExpL1CLM (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)] (hf : Integrable f μ) :
    IsCondExp m μ f (condExpL1CLM E hm μ (hf.toL1 f)) where
  aestronglyMeasurable := aestronglyMeasurable_condExpL1CLM _
  integrableOn s _ _ := (L1.integrable_coeFn _).integrableOn
  setIntegral_eq s hs _ := by
    rw [setIntegral_condExpL1CLM (hf.toL1 f) hs]
    exact setIntegral_congr_ae (hm hs) (hf.coeFn_toL1.mono fun x hx _ ↦ hx)

/-- An integrable function has an `m`-strongly measurable conditional expectation given a
sub-σ-algebra `m` on which `μ` is σ-finite. -/
theorem exists_stronglyMeasurable_isCondExp (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    (hf : Integrable f μ) : ∃ g, StronglyMeasurable[m] g ∧ IsCondExp m μ f g :=
  have h := isCondExp_condExpL1CLM hm hf
  ⟨h.aestronglyMeasurable.mk _, h.aestronglyMeasurable.stronglyMeasurable_mk,
    h.congr_right h.aestronglyMeasurable.ae_eq_mk⟩

/-- An integrable function whose integrals over the sets of `m` in the complement of a set `t ∈ m`
vanish has a conditional expectation given `m` when the restriction of `μ` to `t` is σ-finite on
`m`: the indicator of `t` of a conditional expectation for the measure restricted to `t`. -/
theorem exists_isCondExp_of_setIntegral_compl_eq_zero (hm : m ≤ m₀) {t : Set α} (ht : t ∈ m)
    [SigmaFinite ((μ.restrict t).trim hm)] (hf : Integrable f μ)
    (hft : ∀ s ∈ m, s ⊆ tᶜ → ∫ x in s, f x ∂μ = 0) : ∃ g, IsCondExp m μ f g := by
  obtain ⟨g, hgm, hg⟩ := exists_stronglyMeasurable_isCondExp (μ := μ.restrict t) hm hf.restrict
  have hg_int : Integrable (t.indicator g) μ :=
    (integrable_indicator_iff (hm ht)).2 (hg.integrable hf.restrict)
  refine ⟨t.indicator g, (hgm.indicator ht).aestronglyMeasurable,
    fun _ _ _ ↦ hg_int.integrableOn, fun s hs _ ↦ ?_⟩
  have h_split := integral_inter_add_sdiff (hm ht) (hf.integrableOn : IntegrableOn f s μ)
  rw [hft (s \ t) (by rw [Set.sdiff_eq]; exact m.inter_mem hs (m.compl_mem ht)) fun _ hx ↦ hx.2,
    add_zero] at h_split
  rw [setIntegral_indicator (hm ht), ← Measure.restrict_restrict (hm hs),
    hg.setIntegral_eq s hs hf.restrict.integrableOn, Measure.restrict_restrict (hm hs), h_split]

/-- A function that is almost everywhere `m`-strongly measurable, integrable on the sets of `m` of
finite measure, and has the integral of an integrable `f` over each of them is a conditional
expectation of `f`, when `μ` is σ-finite on the sub-σ-algebra `m`. -/
theorem isCondExp_of_forall_setIntegral_eq (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    (hf : Integrable f μ) (hg_int_finite : ∀ s, s ∈ m → μ s < ∞ → IntegrableOn g s μ)
    (hg_eq : ∀ s : Set α, s ∈ m → μ s < ∞ → ∫ x in s, g x ∂μ = ∫ x in s, f x ∂μ)
    (hgm : AEStronglyMeasurable[m] g μ) : IsCondExp m μ f g := by
  have h := isCondExp_condExpL1CLM hm hf
  refine h.congr_right ?_
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite' hm
    (fun s _ _ ↦ (L1.integrable_coeFn _).integrableOn) hg_int_finite (fun s hs hμs ↦ ?_)
    h.aestronglyMeasurable hgm
  rw [hg_eq s hs hμs, h.setIntegral_eq s hs hf.integrableOn]

/-- For an almost everywhere `m`-measurable function `G` that is finite almost everywhere and a
null-measurable set `t` of finite measure, `fun x ↦ (G x).toReal` is a conditional expectation of
the indicator of `t` given a sub-σ-algebra `m`, that is, a conditional probability of `t`, exactly
when `G` integrates over each set of `m` to the measure of its intersection with `t`. -/
theorem isCondExp_indicator_toReal_iff (hm : m ≤ m₀) {t : Set α} (ht : NullMeasurableSet t μ)
    (hμt : μ t ≠ ∞) {G : α → ℝ≥0∞} (hG : AEStronglyMeasurable[m] G μ)
    (hG_fin : ∀ᵐ x ∂μ, G x ≠ ∞) :
    IsCondExp m μ (t.indicator fun _ ↦ (1 : ℝ)) (fun x ↦ (G x).toReal) ↔
      ∀ s ∈ m, ∫⁻ x in s, G x ∂μ = μ (s ∩ t) := by
  -- it suffices to treat an `m`-measurable modification of `G`
  wlog hGm : Measurable[m] G generalizing G with h_meas
  · obtain ⟨G', hG'm, hGG'⟩ := hG
    have h_toReal : (fun x ↦ (G x).toReal) =ᵐ[μ] fun x ↦ (G' x).toReal :=
      hGG'.fun_comp ENNReal.toReal
    have h_lint (s : Set α) : ∫⁻ x in s, G x ∂μ = ∫⁻ x in s, G' x ∂μ :=
      lintegral_congr_ae (ae_restrict_of_ae hGG')
    have hG'_fin : ∀ᵐ x ∂μ, G' x ≠ ∞ := by
      filter_upwards [hG_fin, hGG'] with x hx hx' using hx' ▸ hx
    simp_rw [h_lint]
    exact ⟨fun h ↦ (h_meas hG'm.aestronglyMeasurable hG'_fin hG'm.measurable).1
        (h.congr_right h_toReal),
      fun h ↦ ((h_meas hG'm.aestronglyMeasurable hG'_fin hG'm.measurable).2 h).congr_right
        h_toReal.symm⟩
  have hG' : Measurable G := hGm.mono hm le_rfl
  have h_indic : Integrable (t.indicator fun _ ↦ (1 : ℝ)) μ :=
    (integrableOn_const hμt).integrable_indicator₀ ht
  have h_ind {s : Set α} (hs : s ∈ m) :
      ∫ x in s, t.indicator (fun _ ↦ (1 : ℝ)) x ∂μ = μ.real (s ∩ t) := by
    rw [integral_indicator₀ (ht.mono Measure.restrict_le_self), setIntegral_const, smul_eq_mul,
      mul_one, measureReal_restrict_apply' (measurableSet_iff_mem.mpr (hm hs)), Set.inter_comm]
  have h_fin {s : Set α} : μ (s ∩ t) ≠ ∞ :=
    ne_top_of_le_ne_top hμt (measure_mono Set.inter_subset_right)
  constructor
  · intro h s hs
    have h_int : Integrable (fun x ↦ (G x).toReal) (μ.restrict s) := (h.integrable h_indic).restrict
    rw [← ENNReal.ofReal_toReal h_fin, ← measureReal_def, ← h_ind hs,
      ← h.setIntegral_eq s hs h_indic.integrableOn,
      ofReal_integral_eq_lintegral_ofReal h_int (ae_of_all _ fun x ↦ ENNReal.toReal_nonneg)]
    exact setLIntegral_congr_fun_ae (measurableSet_iff_mem.mpr (hm hs))
      (hG_fin.mono fun x hx _ ↦ (ENNReal.ofReal_toReal hx).symm)
  · intro h
    have h_int (s : Set α) (hs : s ∈ m) : IntegrableOn (fun x ↦ (G x).toReal) s μ :=
      integrable_toReal_of_lintegral_ne_top hG'.aemeasurable (by rw [h s hs]; exact h_fin)
    refine ⟨hGm.ennreal_toReal.aestronglyMeasurable, fun s hs _ ↦ h_int s hs, fun s hs _ ↦ ?_⟩
    rw [integral_toReal hG'.aemeasurable (ae_restrict_of_ae (hG_fin.mono fun x hx ↦ hx.lt_top)),
      h s hs, h_ind hs, measureReal_def]

/-- The conditional expectation of an `L²` function in the sense of `condExpL2`, the orthogonal
projection on the almost everywhere `m`-measurable functions, is a conditional expectation of an
integrable square-integrable function. -/
lemma MemLp.isCondExp_condExpL2 [InnerProductSpace 𝕜 E] (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    (hf1 : Integrable f μ) (hf2 : MemLp f 2 μ) :
    IsCondExp m μ f (condExpL2 E 𝕜 hm hf2.toLp) := by
  refine isCondExp_of_forall_setIntegral_eq hm hf1
    (fun s hs htop ↦ integrableOn_condExpL2_of_measure_ne_top hm htop.ne _) (fun s hs htop ↦ ?_)
    (aestronglyMeasurable_condExpL2 hm _)
  rw [integral_condExpL2_eq hm (hf2.toLp _) hs htop.ne]
  refine setIntegral_congr_ae (hm hs) ?_
  filter_upwards [hf2.coeFn_toLp] with ω hω _ using hω

namespace IsCondExp

/-- Countable additivity: the sum of conditional expectations of almost everywhere strongly
measurable functions whose `L¹` norms are summable is a conditional expectation of their sum. -/
theorem tsum {ι : Type*} [Countable ι] (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)] {f g : ι → α → E}
    (h : ∀ i, IsCondExp m μ (f i) (g i)) (hf₀ : ∀ i, AEStronglyMeasurable (f i) μ)
    (hf' : ∑' i, ∫⁻ a, ‖f i a‖ₑ ∂μ ≠ ∞) :
    IsCondExp m μ (fun a ↦ ∑' i, f i a) fun a ↦ ∑' i, g i a := by
  have hf (i : ι) : Integrable (f i) μ := ⟨hf₀ i, (ENNReal.le_tsum i).trans_lt hf'.lt_top⟩
  have hT := dominatedFinMeasAdditive_condExpInd E hm μ
  have hsum : Integrable (fun a ↦ ∑' i, f i a) μ := integrable_tsum hf₀ hf'
  have h_eq (u : α → E) (hu : Integrable u μ) :
      (condExpL1CLM E hm μ (hu.toL1 u) : α → E) = setToFun μ _ hT u := by
    rw [setToFun_eq _ hu]; rfl
  refine (isCondExp_condExpL1CLM hm hsum).congr_right ?_
  rw [h_eq _ hsum, setToFun_tsum hT hf₀ hf']
  have A : ∀ᵐ a ∂μ, ∀ i, setToFun μ _ hT (f i) a = g i a := ae_all_iff.2 fun i ↦ by
    rw [← h_eq _ (hf i)]
    exact (isCondExp_condExpL1CLM hm (hf i)).ae_eq hm (hf i) (h i)
  have B : ∑' i, ‖setToFun μ _ hT (f i)‖ₑ ≠ ∞ := by
    apply (lt_of_le_of_lt ?_ hf'.lt_top).ne
    gcongr with i
    exact (enorm_setToFun_le _ (by simp)).trans_eq (by simp)
  filter_upwards [A, Lp.coeFn_tsum B] with a ha h'a
  rw [h'a]
  exact tsum_congr ha

/-- **Locality**: a conditional expectation of `f` given a sub-σ-algebra `m` is one for the measure
restricted to a set `s ∈ m`. -/
theorem restrict (hm : m ≤ m₀) (h : IsCondExp m μ f g) (hs : s ∈ m) :
    IsCondExp m (μ.restrict s) f g where
  aestronglyMeasurable := h.aestronglyMeasurable.mono_measure Measure.restrict_le_self
  integrableOn t ht hf := by
    rw [IntegrableOn, Measure.restrict_restrict (hm ht)] at hf ⊢
    exact h.integrableOn _ (m.inter_mem ht hs) hf
  setIntegral_eq t ht hf := by
    rw [IntegrableOn, Measure.restrict_restrict (hm ht)] at hf
    rw [Measure.restrict_restrict (hm ht), h.setIntegral_eq _ (m.inter_mem ht hs) hf]

variable [PartialOrder E] [ClosedIciTopology E] [IsOrderedAddMonoid E] [IsOrderedModule ℝ E]

private theorem mono_of_sigmaFinite (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)]
    (h : IsCondExp m μ f g) (h' : IsCondExp m μ f' g') (hf : Integrable f μ)
    (hf' : Integrable f' μ) (hff' : f ≤ᵐ[μ] f') : g ≤ᵐ[μ] g' := by
  have h₁ := (isCondExp_condExpL1CLM hm hf).ae_eq hm hf h
  have h₂ := (isCondExp_condExpL1CLM hm hf').ae_eq hm hf' h'
  refine h₁.symm.trans_le (EventuallyLE.trans_eq ?_ h₂)
  exact (Lp.coeFn_le _ _).2 (condExpL1CLM_mono ((Lp.coeFn_le _ _).1 <|
    hf.coeFn_toL1.trans_le (hff'.trans_eq hf'.coeFn_toL1.symm)))

/-- Conditional expectations of integrable functions given a sub-σ-algebra are monotone. No
σ-finiteness is needed: conditional expectations of integrable functions vanish outside a set of
`m` on which the restriction of `μ` to `m` is σ-finite. -/
theorem mono (hm : m ≤ m₀) (h : IsCondExp m μ f g) (h' : IsCondExp m μ f' g')
    (hf : Integrable f μ) (hf' : Integrable f' μ) (hff' : f ≤ᵐ[μ] f') : g ≤ᵐ[μ] g' := by
  obtain ⟨t₁, ht₁, hσ₁, hg₁⟩ :=
    exists_mem_sigmaFinite_trim_restrict hm (h.integrable hf) h.aestronglyMeasurable
  obtain ⟨t₂, ht₂, hσ₂, hg₂⟩ :=
    exists_mem_sigmaFinite_trim_restrict hm (h'.integrable hf') h'.aestronglyMeasurable
  have ht : t₁ ∪ t₂ ∈ m := m.union_mem ht₁ ht₂
  have hσ : SigmaFinite ((μ.restrict (t₁ ∪ t₂)).trim hm) := by
    rw [← restrict_trim hm μ ht]
    rw [← restrict_trim hm μ ht₁] at hσ₁
    rw [← restrict_trim hm μ ht₂] at hσ₂
    exact Measure.sigmaFinite_of_le _ (Measure.restrict_union_le (μ := μ.trim hm) t₁ t₂)
  have h_on : g ≤ᵐ[μ.restrict (t₁ ∪ t₂)] g' :=
    mono_of_sigmaFinite hm (h.restrict hm ht) (h'.restrict hm ht) hf.restrict hf'.restrict
      (ae_restrict_of_ae hff')
  have h_off : g ≤ᵐ[μ.restrict (t₁ ∪ t₂)ᶜ] g' := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset
        (Set.compl_subset_compl.2 Set.subset_union_left) hg₁,
      ae_restrict_of_ae_restrict_of_subset
        (Set.compl_subset_compl.2 Set.subset_union_right) hg₂] with x hx hx'
    simp [hx, hx']
  exact ae_of_ae_restrict_of_ae_restrict_compl _ h_on h_off

/-- A conditional expectation of a nonnegative integrable function given a sub-σ-algebra is
nonnegative. -/
theorem nonneg (hm : m ≤ m₀) (h : IsCondExp m μ f g) (hf : Integrable f μ)
    (hf_nonneg : 0 ≤ᵐ[μ] f) : 0 ≤ᵐ[μ] g :=
  zero.mono hm h (integrable_zero _ _ _) hf hf_nonneg

/-- A conditional expectation of a nonpositive integrable function given a sub-σ-algebra is
nonpositive. -/
theorem nonpos (hm : m ≤ m₀) (h : IsCondExp m μ f g) (hf : Integrable f μ)
    (hf_nonpos : f ≤ᵐ[μ] 0) : g ≤ᵐ[μ] 0 :=
  h.mono hm zero hf (integrable_zero _ _ _) hf_nonpos

/-- An integrable function between `0` and an integrable function with a conditional expectation
given a sub-σ-algebra has a nonnegative conditional expectation. No σ-finiteness is needed: the
conditional expectation of the larger function vanishes outside a set of `m` on which `μ` is
σ-finite, so the integrals of both functions over the sets of `m` outside it vanish. -/
theorem exists_isCondExp_of_nonneg_of_le (hm : m ≤ m₀) (h' : IsCondExp m μ f' g')
    (hf : Integrable f μ) (hf' : Integrable f' μ) (hf0 : 0 ≤ᵐ[μ] f) (hff' : f ≤ᵐ[μ] f') :
    ∃ g, IsCondExp m μ f g ∧ 0 ≤ᵐ[μ] g := by
  obtain ⟨t, ht, hσ, hgt⟩ :=
    exists_mem_sigmaFinite_trim_restrict hm (h'.integrable hf') h'.aestronglyMeasurable
  obtain ⟨g, hg⟩ := exists_isCondExp_of_setIntegral_compl_eq_zero hm ht hf fun s hs hst ↦ by
    have hf's : ∫ x in s, f' x ∂μ = 0 := by
      rw [← h'.setIntegral_eq s hs hf'.integrableOn]
      exact integral_eq_zero_of_ae (ae_restrict_of_ae_restrict_of_subset hst hgt)
    refine le_antisymm ?_ (integral_nonneg_of_ae (ae_restrict_of_ae hf0))
    calc ∫ x in s, f x ∂μ ≤ ∫ x in s, f' x ∂μ :=
          integral_mono_ae hf.integrableOn hf'.integrableOn (ae_restrict_of_ae hff')
      _ = 0 := hf's
  exact ⟨g, hg, hg.nonneg hm hf hf0⟩

end IsCondExp

/-! ### The domain -/

namespace HasUniqueCondExp

/-- A conditional expectation of an integrable function given a sub-σ-algebra makes it unique. -/
theorem of_isCondExp (hm : m ≤ m₀) (hf : Integrable f μ) (hg : IsCondExp m μ f g) :
    HasUniqueCondExp m μ f where
  le_eventuallySigmaAlgebra := hm.trans _root_.le_eventuallySigmaAlgebra
  exists_isCondExp := ⟨g, hg⟩
  ae_eq_of_isCondExp _ _ h₁ h₂ := h₁.ae_eq hm hf h₂

/-- An integrable function has a unique conditional expectation given a sub-σ-algebra on which the
measure is σ-finite. -/
theorem of_integrable (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)] (hf : Integrable f μ) :
    HasUniqueCondExp m μ f :=
  of_isCondExp hm hf (isCondExp_condExpL1CLM hm hf)

/-- An integrable function between `0` and an integrable function with a unique conditional
expectation given a sub-σ-algebra has a unique conditional expectation. -/
theorem of_nonneg_of_le [PartialOrder E] [ClosedIciTopology E] [IsOrderedAddMonoid E]
    [IsOrderedModule ℝ E] (hm : m ≤ m₀) (h' : HasUniqueCondExp m μ f') (hf : Integrable f μ)
    (hf' : Integrable f' μ) (hf0 : 0 ≤ᵐ[μ] f) (hff' : f ≤ᵐ[μ] f') : HasUniqueCondExp m μ f :=
  let ⟨_, hg'⟩ := h'.exists_isCondExp
  let ⟨_, hg, _⟩ := hg'.exists_isCondExp_of_nonneg_of_le hm hf hf' hf0 hff'
  of_isCondExp hm hf hg

theorem congr (h : HasUniqueCondExp m μ f) (hf : f =ᵐ[μ] f') : HasUniqueCondExp m μ f' where
  le_eventuallySigmaAlgebra := h.le_eventuallySigmaAlgebra
  exists_isCondExp := let ⟨g, hg⟩ := h.exists_isCondExp; ⟨g, hg.congr_left hf⟩
  ae_eq_of_isCondExp _ _ h₁ h₂ :=
    h.ae_eq_of_isCondExp (h₁.congr_left hf.symm) (h₂.congr_left hf.symm)

theorem add (hm : m ≤ m₀) (h : HasUniqueCondExp m μ f) (h' : HasUniqueCondExp m μ f')
    (hf : Integrable f μ) (hf' : Integrable f' μ) : HasUniqueCondExp m μ (f + f') :=
  let ⟨_, hg⟩ := h.exists_isCondExp
  let ⟨_, hg'⟩ := h'.exists_isCondExp
  .of_isCondExp hm (hf.add hf') (hg.add hg' hf hf')

theorem sub (hm : m ≤ m₀) (h : HasUniqueCondExp m μ f) (h' : HasUniqueCondExp m μ f')
    (hf : Integrable f μ) (hf' : Integrable f' μ) : HasUniqueCondExp m μ (f - f') :=
  let ⟨_, hg⟩ := h.exists_isCondExp
  let ⟨_, hg'⟩ := h'.exists_isCondExp
  .of_isCondExp hm (hf.sub hf') (hg.sub hg' hf hf')

theorem finsetSum {ι : Type*} {t : Finset ι} {f : ι → α → E} (hm : m ≤ m₀)
    (h : ∀ i ∈ t, HasUniqueCondExp m μ (f i)) (hf : ∀ i ∈ t, Integrable (f i) μ) :
    HasUniqueCondExp m μ (∑ i ∈ t, f i) := by
  have (i : ι) : ∃ g, i ∈ t → IsCondExp m μ (f i) g := by
    by_cases hi : i ∈ t
    · obtain ⟨g, hg⟩ := (h i hi).exists_isCondExp
      exact ⟨g, fun _ ↦ hg⟩
    · exact ⟨0, fun h' ↦ absurd h' hi⟩
  choose g hg using this
  exact .of_isCondExp hm (integrable_finsetSum' t hf) (IsCondExp.finsetSum hg hf)

theorem neg (h : HasUniqueCondExp m μ f) : HasUniqueCondExp m μ (-f) where
  le_eventuallySigmaAlgebra := h.le_eventuallySigmaAlgebra
  exists_isCondExp := let ⟨g, hg⟩ := h.exists_isCondExp; ⟨-g, hg.neg⟩
  ae_eq_of_isCondExp g₁ g₂ h₁ h₂ := by
    filter_upwards [h.ae_eq_of_isCondExp (by simpa using h₁.neg) (by simpa using h₂.neg)]
      with x hx
    simpa using hx

theorem smul [NormedSpace 𝕜 E] [SMulCommClass ℝ 𝕜 E] (h : HasUniqueCondExp m μ f) {c : 𝕜}
    (hc : c ≠ 0) : HasUniqueCondExp m μ (c • f) where
  le_eventuallySigmaAlgebra := h.le_eventuallySigmaAlgebra
  exists_isCondExp := let ⟨g, hg⟩ := h.exists_isCondExp; ⟨c • g, hg.smul c⟩
  ae_eq_of_isCondExp g₁ g₂ h₁ h₂ := by
    have h_inv {g : α → E} (hg : IsCondExp m μ (c • f) g) : IsCondExp m μ f (c⁻¹ • g) := by
      simpa [smul_smul, inv_mul_cancel₀ hc] using hg.smul c⁻¹
    filter_upwards [h.ae_eq_of_isCondExp (h_inv h₁) (h_inv h₂)] with x hx
    exact smul_right_injective E (inv_ne_zero hc) hx

end HasUniqueCondExp

/-- `has_unique_cond_exp` proves `HasUniqueCondExp m μ f`, the domain of the conditional
expectation `μ[f | m]`: it tries a hypothesis, then `HasUniqueCondExp.of_integrable`, whose
sub-σ-algebra and integrability hypotheses it proves with `sub_sigma_algebra` and `integrability`
and whose σ-finiteness it finds by instance search, then `HasUniqueCondExp.of_isCondExp` with a
conditional expectation from a hypothesis. Later files extend it with `macro_rules`. -/
syntax (name := hasUniqueCondExp) "has_unique_cond_exp" : tactic

macro_rules
  | `(tactic| has_unique_cond_exp) => `(tactic| first
    | done
    | assumption
    | exact MeasureTheory.HasUniqueCondExp.of_integrable (by sub_sigma_algebra) (by integrability)
    | exact MeasureTheory.HasUniqueCondExp.of_isCondExp (by sub_sigma_algebra) (by integrability)
        (by assumption)
    | fail "this function needs a proof `HasUniqueCondExp m μ f` that it has a conditional \
        expectation given `m`, unique almost everywhere, for example from its integrability and \
        the σ-finiteness of `μ` on `m`")

/-! ### The conditional expectation as an almost everywhere class -/

/-- Some germ along `ae μ` is represented by a conditional expectation of `f`. By the uniqueness in
`HasUniqueCondExp m μ f`, such a germ is unique. -/
theorem exists_germ_isCondExp (h : HasUniqueCondExp m μ f) :
    ∃ φ : (ae μ).Germ E, ∃ g, IsCondExp m μ f g ∧ g ∈ φ :=
  let ⟨g, hg⟩ := h.exists_isCondExp
  ⟨g, g, hg, Germ.coe_mem g⟩

variable (m) in
/-- The conditional expectation of `f` given the σ-algebra `m` with respect to `μ`, with notation
`μ[f | m]`: the almost everywhere class of the conditional expectations of `f`, as a germ along
`ae μ`. A function `g` represents it, written `g ∈ μ[f | m]`, exactly when it is a conditional
expectation of `f` (`MeasureTheory.mem_condExp_iff`).

It takes a proof of `HasUniqueCondExp m μ f`, its exact domain, which the tactic
`has_unique_cond_exp` finds for an integrable `f` and a sub-σ-algebra on which `μ` is σ-finite. -/
@[wikidata Q772232]
noncomputable def condExp (μ : Measure[m₀] α) (f : α → E)
    (h : HasUniqueCondExp m μ f := by has_unique_cond_exp) : (ae μ).Germ E :=
  (exists_germ_isCondExp h).choose

@[inherit_doc MeasureTheory.condExp]
scoped macro:max μ:term noWs "[" f:term " | " m:term "]" : term =>
  `(MeasureTheory.condExp $m $μ $f)

/-- Unexpander for `μ[f | m]` notation. -/
@[app_unexpander MeasureTheory.condExp]
meta def condExpUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $m $μ $f $_) => `($μ[$f|$m])
  | _ => throw ()

/-- info: fun h ↦ μ[f | m] : HasUniqueCondExp m μ f → (ae μ).Germ E -/
#guard_msgs in
#check fun h : HasUniqueCondExp m μ f ↦ μ[f | m]

/-- Every conditional expectation of `f` represents `μ[f | m]`. -/
theorem IsCondExp.mem_condExp (h : HasUniqueCondExp m μ f) (hg : IsCondExp m μ f g) :
    g ∈ condExp m μ f h := by
  obtain ⟨g', hg', hg'_mem⟩ := (exists_germ_isCondExp h).choose_spec
  exact Germ.mem_of_eventuallyEq hg'_mem (h.ae_eq_of_isCondExp hg' hg)

/-- Every representative of `μ[f | m]` is a conditional expectation of `f`. -/
theorem isCondExp_of_mem_condExp (h : HasUniqueCondExp m μ f) (hg : g ∈ condExp m μ f h) :
    IsCondExp m μ f g := by
  obtain ⟨g', hg', hg'_mem⟩ := (exists_germ_isCondExp h).choose_spec
  exact hg'.congr_right (Germ.eventuallyEq_of_mem hg'_mem hg)

/-- The representatives of `μ[f | m]` are the conditional expectations of `f`. -/
theorem mem_condExp_iff (h : HasUniqueCondExp m μ f) : g ∈ condExp m μ f h ↔ IsCondExp m μ f g :=
  ⟨isCondExp_of_mem_condExp h, fun hg ↦ hg.mem_condExp h⟩

/-- `μ[f | m]` is the class of any conditional expectation of `f`. -/
theorem IsCondExp.condExp_eq (h : HasUniqueCondExp m μ f) (hg : IsCondExp m μ f g) :
    condExp m μ f h = g :=
  Germ.eq_coe_of_mem (hg.mem_condExp h)

/-- `μ[f | m]` is the class of `g` exactly when `g` is a conditional expectation of `f`. -/
theorem condExp_eq_coe_iff (h : HasUniqueCondExp m μ f) :
    condExp m μ f h = g ↔ IsCondExp m μ f g := by
  refine ⟨fun hg ↦ isCondExp_of_mem_condExp h ?_, fun hg ↦ hg.condExp_eq h⟩
  rw [hg]
  exact Germ.coe_mem g

/-- `μ[f | m]` has an `m`-strongly measurable representative. -/
theorem exists_stronglyMeasurable_mem_condExp (h : HasUniqueCondExp m μ f) :
    ∃ g, StronglyMeasurable[m] g ∧ g ∈ condExp m μ f h := by
  obtain ⟨g, hg⟩ := h.exists_isCondExp
  exact ⟨hg.aestronglyMeasurable.mk g, hg.aestronglyMeasurable.stronglyMeasurable_mk,
    (hg.congr_right hg.aestronglyMeasurable.ae_eq_mk).mem_condExp h⟩

theorem condExp_congr_ae (h : HasUniqueCondExp m μ f) (hf : f =ᵐ[μ] f') :
    condExp m μ f h = condExp m μ f' (h.congr hf) := by
  obtain ⟨g, hg⟩ := h.exists_isCondExp
  rw [hg.condExp_eq h, (hg.congr_left hf).condExp_eq]

/-- The conditional expectation of an almost everywhere `m`-strongly measurable function is its
class. -/
theorem condExp_of_aestronglyMeasurable (h : HasUniqueCondExp m μ f)
    (hf : AEStronglyMeasurable[m] f μ) : condExp m μ f h = f :=
  (isCondExp_self hf).condExp_eq h

theorem condExp_add (hf : Integrable f μ) (hf' : Integrable f' μ) (h : HasUniqueCondExp m μ f)
    (h' : HasUniqueCondExp m μ f') (h'' : HasUniqueCondExp m μ (f + f')) :
    condExp m μ (f + f') h'' = condExp m μ f h + condExp m μ f' h' := by
  obtain ⟨g, hg⟩ := h.exists_isCondExp
  obtain ⟨g', hg'⟩ := h'.exists_isCondExp
  rw [hg.condExp_eq h, hg'.condExp_eq h', ← Germ.coe_add, (hg.add hg' hf hf').condExp_eq h'']

theorem condExp_smul [NormedSpace 𝕜 E] [SMulCommClass ℝ 𝕜 E] (c : 𝕜) (h : HasUniqueCondExp m μ f)
    (h' : HasUniqueCondExp m μ (c • f)) : condExp m μ (c • f) h' = c • condExp m μ f h := by
  obtain ⟨g, hg⟩ := h.exists_isCondExp
  rw [hg.condExp_eq h, ← Germ.coe_smul, (hg.smul c).condExp_eq h']

theorem condExp_neg (h : HasUniqueCondExp m μ f) (h' : HasUniqueCondExp m μ (-f)) :
    condExp m μ (-f) h' = -condExp m μ f h := by
  obtain ⟨g, hg⟩ := h.exists_isCondExp
  rw [hg.condExp_eq h, ← Germ.coe_neg, hg.neg.condExp_eq h']

theorem condExp_sub (hf : Integrable f μ) (hf' : Integrable f' μ) (h : HasUniqueCondExp m μ f)
    (h' : HasUniqueCondExp m μ f') (h'' : HasUniqueCondExp m μ (f - f')) :
    condExp m μ (f - f') h'' = condExp m μ f h - condExp m μ f' h' := by
  obtain ⟨g, hg⟩ := h.exists_isCondExp
  obtain ⟨g', hg'⟩ := h'.exists_isCondExp
  rw [hg.condExp_eq h, hg'.condExp_eq h', ← Germ.coe_sub, (hg.sub hg' hf hf').condExp_eq h'']

/-- The conditional expectation given a sub-σ-algebra is monotone on integrable functions. -/
theorem condExp_mono [PartialOrder E] [ClosedIciTopology E] [IsOrderedAddMonoid E]
    [IsOrderedModule ℝ E] (hm : m ≤ m₀) (hf : Integrable f μ) (hf' : Integrable f' μ)
    (hff' : f ≤ᵐ[μ] f') (h : HasUniqueCondExp m μ f) (h' : HasUniqueCondExp m μ f') :
    condExp m μ f h ≤ condExp m μ f' h' := by
  obtain ⟨g, hg⟩ := h.exists_isCondExp
  obtain ⟨g', hg'⟩ := h'.exists_isCondExp
  rw [hg.condExp_eq h, hg'.condExp_eq h']
  exact Germ.coe_le.2 (hg.mono hm hg' hf hf' hff')

/-- The tower property for the classes: for a representative `g` of `μ[f | m₂]` and `m₁ ≤ m₂`, the
conditional expectation of `g` given `m₁` is that of `f`. -/
theorem condExp_of_mem_condExp {m₁ m₂ : SigmaAlgebra α} (h₁₂ : m₁ ≤ m₂)
    (h : HasUniqueCondExp m₂ μ f) (hg : g ∈ condExp m₂ μ f h) (h₁ : HasUniqueCondExp m₁ μ g)
    (h₁' : HasUniqueCondExp m₁ μ f) : condExp m₁ μ g h₁ = condExp m₁ μ f h₁' := by
  obtain ⟨k, hk⟩ := h₁.exists_isCondExp
  rw [hk.condExp_eq h₁, (((isCondExp_of_mem_condExp h hg).trans hk h₁₂)).condExp_eq h₁']

end MeasureTheory
