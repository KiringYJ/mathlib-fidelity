/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module

public import Mathlib.Analysis.Real.Cardinality
public import Mathlib.Probability.Independence.Conditional
public import Mathlib.Probability.Kernel.Condexp

/-!
# A probability measure whose conditional kernels are not unique

Conditional independence given a sub-σ-algebra `m'` is stated with versions of the conditional
probabilities of null-measurable sets, the conditional expectations of their indicators, which
exist and agree almost everywhere for every finite measure on every measurable space. The
conditional expectation kernel `ProbabilityTheory.condExpKernel μ hm'` is defined only when the
joint law of `(ω, ω)` has a unique conditional kernel, and the uniqueness can fail for a
probability measure.

Let `CountableCocountable` be `ℝ` with the countable-cocountable σ-algebra, whose measurable sets
are the countable sets and their complements, and let `oneOnCocountable` be the probability measure
that is `0` on countable sets and `1` on cocountable ones. Given the whole σ-algebra, both the Dirac
kernel and the constant kernel of this measure disintegrate the joint law of `(ω, ω)`, since they
give a rectangle `A ×ˢ B` the measures `μ (A ∩ B) = μ A * μ B`, and they differ at every point, so
the joint law has no unique conditional kernel
(`Counterexample.CondExpKernelCocountable.not_hasUniqueCondKernel`). Both kernels give versions of
the conditional probabilities, which here are the indicators. Conditional independence given the
whole σ-algebra is nevertheless defined, and the whole σ-algebra is conditionally independent of
itself (`Counterexample.CondExpKernelCocountable.condIndep_self`).
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Counterexample.CondExpKernelCocountable

/-- The countable-cocountable σ-algebra: the countable sets and their complements. -/
@[instance_reducible]
def countableCocountable (α : Type*) : SigmaAlgebra α where
  carrier := {s | s.Countable ∨ sᶜ.Countable}
  isSigmaAlgebra :=
    { empty_mem := Or.inl countable_empty
      compl_mem := fun _ hs ↦ hs.symm.imp_right fun h ↦ by rwa [compl_compl]
      iUnion_mem_nat := fun f hf ↦ by
        by_cases h : ∀ i, (f i).Countable
        · exact Or.inl (countable_iUnion h)
        · push Not at h
          obtain ⟨i, hi⟩ := h
          exact Or.inr (((hf i).resolve_left hi).mono
            (compl_subset_compl.2 (subset_iUnion f i))) }

/-- The real line with the countable-cocountable σ-algebra. -/
def CountableCocountable : Type := ℝ

instance instSigmaAlgebra : SigmaAlgebra CountableCocountable :=
  countableCocountable CountableCocountable

lemma measurableSet_iff {s : Set CountableCocountable} :
    MeasurableSet s ↔ s.Countable ∨ sᶜ.Countable :=
  measurableSet_iff_mem

/-- `CountableCocountable` is uncountable, as `ℝ` is. -/
lemma not_countable_univ : ¬ (univ : Set CountableCocountable).Countable :=
  Cardinal.not_countable_real

/-- No set is both countable and cocountable. -/
lemma not_countable_and_countable_compl {s : Set CountableCocountable} (h₁ : s.Countable)
    (h₂ : sᶜ.Countable) : False :=
  not_countable_univ (by simpa using h₁.union h₂)

open scoped Classical in
/-- The probability measure that is `0` on countable sets and `1` on cocountable sets. Of disjoint
measurable sets at most one is cocountable, since the complements of two disjoint sets cover the
space, and their union is cocountable exactly when one of them is. -/
def oneOnCocountable : Measure CountableCocountable :=
  Measure.ofMeasurable (fun s _ ↦ if sᶜ.Countable then 1 else 0) (by simp [not_countable_univ])
    (by
      intro f hf hd
      by_cases h : ∃ j, (f j)ᶜ.Countable
      · obtain ⟨j, hj⟩ := h
        rw [tsum_eq_single j fun i hij ↦ ite_eq_right fun hc ↦ not_countable_and_countable_compl
            (hj.mono fun _ hx ↦ Set.disjoint_left.1 (hd hij) hx) hc,
          ite_eq_left hj, ite_eq_left (hj.mono (compl_subset_compl.2 (subset_iUnion f j)))]
      · push Not at h
        have hU : (⋃ i, f i).Countable :=
          countable_iUnion fun i ↦ (measurableSet_iff.1 (hf i)).resolve_right (h i)
        rw [ite_eq_right fun hc ↦ not_countable_and_countable_compl hU hc]
        simp [h])

open scoped Classical in
lemma oneOnCocountable_apply {s : Set CountableCocountable} (hs : MeasurableSet s) :
    oneOnCocountable s = if sᶜ.Countable then 1 else 0 :=
  Measure.ofMeasurable_apply s hs

lemma oneOnCocountable_of_countable {s : Set CountableCocountable} (hs : s.Countable) :
    oneOnCocountable s = 0 := by
  rw [oneOnCocountable_apply (measurableSet_iff.2 (Or.inl hs)),
    ite_eq_right fun hc ↦ not_countable_and_countable_compl hs hc]

lemma oneOnCocountable_of_countable_compl {s : Set CountableCocountable} (hs : sᶜ.Countable) :
    oneOnCocountable s = 1 := by
  rw [oneOnCocountable_apply (measurableSet_iff.2 (Or.inr hs)), ite_eq_left hs]

instance : IsProbabilityMeasure oneOnCocountable :=
  ⟨oneOnCocountable_of_countable_compl (by simp)⟩

/-- The joint law of `(ω, ω)` given the whole σ-algebra. -/
abbrev jointLaw : Measure (CountableCocountable × CountableCocountable) :=
  condExpJointLaw oneOnCocountable le_rfl

/-- The Dirac kernel disintegrates the joint law of `(ω, ω)`. -/
lemma isCondKernel_id : jointLaw.IsCondKernel Kernel.id := by
  refine .of_compProd_eq (fst_condExpJointLaw _ _) ?_
  rw [trim_eq_self, Measure.compProd_id_eq_copy_comp]
  exact Measure.deterministic_comp_eq_map _

/-- The constant kernel of `oneOnCocountable` disintegrates the joint law of `(ω, ω)`: on a
rectangle `A ×ˢ B` both give `μ (A ∩ B) = μ A * μ B`, since an intersection of two sets is
cocountable exactly when both are. -/
lemma isCondKernel_const :
    jointLaw.IsCondKernel (Kernel.const CountableCocountable oneOnCocountable) := by
  refine .of_compProd_eq (fst_condExpJointLaw _ _) ?_
  refine Measure.ext_prod fun {A B} hA hB ↦ ?_
  rw [Measure.compProd_apply_prod hA hB, condExpJointLaw_apply_prod (measurableSet_iff_mem.1 hA) hB]
  simp only [Kernel.const_apply]
  rw [setLIntegral_const, trim_measurableSet_eq le_rfl hA]
  rcases measurableSet_iff.1 hA with hA | hA
  · rw [oneOnCocountable_of_countable hA, oneOnCocountable_of_countable (hA.mono inter_subset_left),
      mul_zero]
  rcases measurableSet_iff.1 hB with hB | hB
  · rw [oneOnCocountable_of_countable hB,
      oneOnCocountable_of_countable (hB.mono inter_subset_right), zero_mul]
  · rw [oneOnCocountable_of_countable_compl hA, oneOnCocountable_of_countable_compl hB,
      oneOnCocountable_of_countable_compl (by rw [compl_inter]; exact hA.union hB), one_mul]

/-- The joint law of `(ω, ω)` given the whole σ-algebra has no unique conditional kernel: the Dirac
kernel and the constant kernel of `oneOnCocountable` both disintegrate it, and they differ at every
point, where the Dirac measure gives the point mass `1` and the other measure gives it `0`. So
`condExpKernel oneOnCocountable le_rfl` is not defined. -/
theorem not_hasUniqueCondKernel : ¬ jointLaw.HasUniqueCondKernel := by
  intro h
  have := isCondKernel_id
  have := isCondKernel_const
  have h_ae := h.ae_eq_of_isCondKernel Kernel.id
    (Kernel.const CountableCocountable oneOnCocountable)
  rw [fst_condExpJointLaw, trim_eq_self] at h_ae
  obtain ⟨x, hx⟩ := h_ae.exists
  have h₁ : ((Kernel.id : Kernel CountableCocountable CountableCocountable) x) {x} = 1 := by
    rw [Kernel.id_apply]
    exact Measure.dirac_apply_of_mem rfl
  rw [hx, Kernel.const_apply, oneOnCocountable_of_countable (countable_singleton x)] at h₁
  exact zero_ne_one h₁

/-- Conditional independence given the whole σ-algebra is defined for `oneOnCocountable`, although
the conditional expectation kernel is not: the whole σ-algebra is conditionally independent of
itself, since the indicator of each of its sets is a version of the conditional probability of the
set. -/
theorem condIndep_self :
    CondIndep instSigmaAlgebra instSigmaAlgebra instSigmaAlgebra le_rfl oneOnCocountable :=
  condIndep_of_le_left le_rfl fun _ hs ↦ (measurableSet_iff_mem.2 hs).nullMeasurableSet

end Counterexample.CondExpKernelCocountable
