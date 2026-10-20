/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.MeasureTheory.SigmaAlgebra.Pi
public import Mathlib.Probability.Notation

/-!
# Conditional Independence

We define conditional independence of sets/σ-algebras/functions with respect to a σ-algebra.

A version of the conditional probability of a set `t` given a sub-σ-algebra `m'` is a version `g` of
the conditional expectation of its indicator, `IsCondExp m' μ (t.indicator fun _ ↦ 1) g`, and the
conditional probability `μ⟦t | m'⟧` is their almost everywhere class, a germ along `ae μ`. For a
null-measurable set `t` and a finite measure `μ` the indicator is integrable, so versions exist
and any two agree almost everywhere: the conditional probabilities of null-measurable sets are
determined up to `μ`-null sets on every measurable space. The definitions therefore require the
sets to be null-measurable, and the measure to be finite, as in probability theory.

Two σ-algebras `m₁` and `m₂` are conditionally independent given `m'` with respect to `μ` if their
sets are null-measurable and, for all `t₁ ∈ m₁` and `t₂ ∈ m₂`, the product of versions of the
conditional probabilities of `t₁` and `t₂` is a version of the conditional probability of
`t₁ ∩ t₂`. Since versions are unique almost everywhere, this holds for all versions as soon as it
holds for some (`ProbabilityTheory.CondIndepSets.of_isCondExp`), and it is the identity
`μ⟦t₁ ∩ t₂ | m'⟧ = μ⟦t₁ | m'⟧ * μ⟦t₂ | m'⟧` of germs (`ProbabilityTheory.condIndep_iff_condExp`).
The empty intersection of a family is `Set.univ`, whose conditional probability is the constant
`1`.

## Main definitions

We provide four definitions of conditional independence:
* `iCondIndepSets`: conditional independence of a family of sets of sets `pi : ι → Set (Set Ω)`.
  This is meant to be used with π-systems.
* `iCondIndep`: conditional independence of a family of σ-algebras `m : ι → SigmaAlgebra Ω`,
* `iCondIndepSet`: conditional independence of a family of sets `s : ι → Set Ω`,
* `iCondIndepFun`: conditional independence of a family of functions. For measurable spaces
  `m : Π (i : ι), SigmaAlgebra (β i)`, we consider functions `f : Π (i : ι), Ω → β i`.

Additionally, we provide four corresponding statements for two σ-algebras (resp. sets of sets,
sets, functions) instead of a family. These properties are denoted by the same names as for a
family, but without the starting `i`, for example `CondIndepFun` is the version of `iCondIndepFun`
for two functions.

## Main statements

* `ProbabilityTheory.iCondIndepSets.iCondIndep`: if π-systems are conditionally independent as sets
  of sets, then the σ-algebras they generate are conditionally independent.
* `ProbabilityTheory.CondIndepSets.condIndep`: variant with two π-systems.
* `ProbabilityTheory.condIndep_iff_condExp`, `ProbabilityTheory.iCondIndep_iff_condExp`: the
  characterizations through conditional probabilities as germs,
  `μ⟦t₁ ∩ t₂ | m'⟧ = μ⟦t₁ | m'⟧ * μ⟦t₂ | m'⟧` and `μ⟦⋂ i ∈ s, f i | m'⟧ = ∏ i : s, μ⟦f i | m'⟧`.
  The corresponding statements without the suffix `_condExp`, such as
  `ProbabilityTheory.condIndep_iff`, state them with versions.

## Notation

* `X ⟂ᵢ[Z, hZ; μ] Y` for `CondIndepFun (SigmaAlgebra.comap Z inferInstance) hZ.comap_le X Y μ`,
  independence of `X` and `Y` given `Z`.
* `X ⟂ᵢ[Z, hZ] Y` for the cases of `μ = volume`.

These notations are scoped in the `ProbabilityTheory` namespace.

## Implementation notes

The definitions use conditional expectations rather than the kernel
`ProbabilityTheory.condExpKernel μ hm'`, which is defined only when the joint law of `(ω, ω)` has a
unique conditional kernel. Uniqueness can fail for a probability measure: on an uncountable type
with the countable-cocountable σ-algebra and the measure that is one on cocountable sets, given the
whole σ-algebra, both the Dirac kernel and the constant kernel of that measure disintegrate the
joint law, since both give a rectangle `A ×ˢ B` the mass `μ (A ∩ B) = μ A * μ B`, and they differ at
every point (`Counterexamples/CondExpKernelCocountable.lean`). The π-system lemmas are therefore
proved with versions of the conditional probabilities themselves, whose sums over countably many
disjoint sets are versions for their union (`MeasureTheory.IsCondExp.indicator_iUnion`). The
characterizations through the kernel, which hold under the class of the joint law, and those
through the conditional distributions given a random variable, which need only the classes of the
joint laws they involve, are in `Mathlib.Probability.Independence.ConditionalKernel`.

-/

set_option linter.style.longFile 1900

@[expose] public section

open MeasureTheory SigmaAlgebra Filter

open scoped MeasureTheory ENNReal

namespace ProbabilityTheory

variable {Ω ι : Type*}

/-! ### Versions of conditional probabilities

For a finite measure, the indicator `t.indicator fun _ ↦ (1 : ℝ)` of a null-measurable set `t` is
integrable, so it has versions of its conditional expectation given a sub-σ-algebra `m'`, and any
two agree almost everywhere. A product of versions for some sets is therefore a version for another
set exactly when the corresponding identity of conditional probabilities holds as germs.

Versions are additive on differences, complements, and countable disjoint unions of null-measurable
sets (`MeasureTheory.IsCondExp.indicator_sdiff`, `MeasureTheory.IsCondExp.indicator_compl_one`,
`MeasureTheory.IsCondExp.indicator_iUnion`), and `0` is a version for `∅`
(`MeasureTheory.isCondExp_indicator_empty`). For a fixed null-measurable set `t` with a version
`gt`, the sets `u` such that `gt * gu` is a version for `t ∩ u` for every version `gu` for `u`
therefore contain `∅` and are closed under complements and countable disjoint unions, so this
property extends from a π-system to the σ-algebra it generates. -/

section CondProb

variable {m' : SigmaAlgebra Ω} {mΩ : SigmaAlgebra Ω} {μ : Measure Ω} [IsFiniteMeasure μ]

omit [IsFiniteMeasure μ] in
private lemma nullMeasurableSet_of_mem_generateFrom {C : Set (Set Ω)}
    (hC : ∀ s ∈ C, NullMeasurableSet s μ) {s : Set Ω} (hs : s ∈ generateFrom C) :
    NullMeasurableSet s μ := by
  induction hs using generateFrom_induction with
  | basic t ht => exact hC t ht
  | empty => exact .empty
  | compl t _ ht => exact ht.compl
  | iUnion f _ hf => exact .iUnion hf

/-- The indicator of a null-measurable set is integrable for a finite measure. -/
private lemma integrable_indicator_one {t : Set Ω} (ht : NullMeasurableSet t μ) :
    Integrable (t.indicator fun _ ↦ (1 : ℝ)) μ :=
  (integrable_const 1).indicator₀ ht

/-- A null-measurable set has a version of its conditional probability given a sub-σ-algebra. -/
private lemma exists_isCondExp_indicator (hm' : m' ≤ mΩ) {t : Set Ω}
    (ht : NullMeasurableSet t μ) : ∃ g : Ω → ℝ, IsCondExp m' μ (t.indicator fun _ ↦ (1 : ℝ)) g :=
  (HasUniqueCondExp.of_integrable hm' (integrable_indicator_one ht)).exists_isCondExp

omit [IsFiniteMeasure μ] in
/-- A function whose class is the conditional expectation of `f` is a version of it. -/
private lemma isCondExp_of_condExp_eq {f g : Ω → ℝ} {h : HasUniqueCondExp m' μ f}
    (hg : condExp m' μ f h = g) : IsCondExp m' μ f g :=
  isCondExp_of_mem_condExp h (hg ▸ Germ.coe_mem g)

/-- For null-measurable sets `t`, `t₁` and `t₂`, the product of any versions of the conditional
probabilities of `t₁` and `t₂` is a version of that of `t` if and only if
`μ⟦t | m'⟧ = μ⟦t₁ | m'⟧ * μ⟦t₂ | m'⟧`. -/
private lemma forall_isCondExp_mul_iff (hm' : m' ≤ mΩ) {t t₁ t₂ : Set Ω}
    (ht : NullMeasurableSet t μ) (ht₁ : NullMeasurableSet t₁ μ) (ht₂ : NullMeasurableSet t₂ μ) :
    (∀ ⦃g₁ g₂ : Ω → ℝ⦄, IsCondExp m' μ (t₁.indicator fun _ ↦ (1 : ℝ)) g₁ →
      IsCondExp m' μ (t₂.indicator fun _ ↦ (1 : ℝ)) g₂ →
        IsCondExp m' μ (t.indicator fun _ ↦ (1 : ℝ)) (g₁ * g₂)) ↔
      μ⟦t | m'⟧ = μ⟦t₁ | m'⟧ * μ⟦t₂ | m'⟧ := by
  obtain ⟨g₁, hg₁⟩ := exists_isCondExp_indicator hm' ht₁
  obtain ⟨g₂, hg₂⟩ := exists_isCondExp_indicator hm' ht₂
  rw [hg₁.condExp_eq _, hg₂.condExp_eq _, ← Germ.coe_mul]
  refine ⟨fun h ↦ (h hg₁ hg₂).condExp_eq _, fun h g₁' g₂' hg₁' hg₂' ↦ ?_⟩
  exact (isCondExp_of_condExp_eq h).congr_right
    ((hg₁.ae_eq hm' (integrable_indicator_one ht₁) hg₁').mul
      (hg₂.ae_eq hm' (integrable_indicator_one ht₂) hg₂'))

/-- For a null-measurable set `t` and null-measurable sets `f i`, `i ∈ s`, the product of any
versions of the conditional probabilities of the sets `f i` is a version of that of `t` if and only
if `μ⟦t | m'⟧ = ∏ i : s, μ⟦f i | m'⟧`. -/
private lemma forall_isCondExp_prod_iff (hm' : m' ≤ mΩ) {s : Finset ι} {f : ι → Set Ω}
    {t : Set Ω} (ht : NullMeasurableSet t μ) (hf : ∀ i ∈ s, NullMeasurableSet (f i) μ) :
    (∀ ⦃g : ι → Ω → ℝ⦄, (∀ i ∈ s, IsCondExp m' μ ((f i).indicator fun _ ↦ (1 : ℝ)) (g i)) →
      IsCondExp m' μ (t.indicator fun _ ↦ (1 : ℝ)) (∏ i ∈ s, g i)) ↔
      μ⟦t | m'⟧ = ∏ i : s, haveI := hf i i.2; μ⟦f i | m'⟧ := by
  choose! g hg using fun i (hi : i ∈ s) ↦ exists_isCondExp_indicator hm' (hf i hi)
  have h_prod : (∏ i : s, haveI := hf i i.2; μ⟦f i | m'⟧) =
      ((∏ i ∈ s, g i : Ω → ℝ) : (ae μ).Germ ℝ) := by
    rw [← Finset.prod_coe_sort s g]
    calc (∏ i : s, haveI := hf i i.2; μ⟦f i | m'⟧)
      _ = ∏ i : s, ((g i : Ω → ℝ) : (ae μ).Germ ℝ) :=
        Finset.prod_congr rfl fun i _ ↦ (hg i i.2).condExp_eq _
      _ = ((∏ i : s, g i : Ω → ℝ) : (ae μ).Germ ℝ) :=
        (map_prod (Germ.coeMulHom (ae μ)) (fun i : s ↦ g i) Finset.univ).symm
  rw [h_prod]
  refine ⟨fun h ↦ (h hg).condExp_eq _, fun h g' hg' ↦ ?_⟩
  exact (isCondExp_of_condExp_eq h).congr_right (eventuallyEq_prod fun i hi ↦
    (hg i hi).ae_eq hm' (integrable_indicator_one (hf i hi)) (hg' i hi))

/-- The variant of `forall_isCondExp_prod_iff` for a family of null-measurable sets. -/
private lemma forall_isCondExp_prod_iff' (hm' : m' ≤ mΩ) {s : Finset ι} {f : ι → Set Ω}
    {t : Set Ω} (ht : NullMeasurableSet t μ) (hf : ∀ i, NullMeasurableSet (f i) μ) :
    (∀ ⦃g : ι → Ω → ℝ⦄, (∀ i ∈ s, IsCondExp m' μ ((f i).indicator fun _ ↦ (1 : ℝ)) (g i)) →
      IsCondExp m' μ (t.indicator fun _ ↦ (1 : ℝ)) (∏ i ∈ s, g i)) ↔
      μ⟦t | m'⟧ = ∏ i ∈ s, haveI := hf i; μ⟦f i | m'⟧ := by
  rw [forall_isCondExp_prod_iff hm' ht fun i _ ↦ hf i,
    Finset.prod_coe_sort s fun i ↦ haveI := hf i; μ⟦f i | m'⟧]

/-- For a null-measurable set `t` with a version `gt` of its conditional probability, if the product
of `gt` with every version of the conditional probability of a set of a π-system `p` of
null-measurable sets is a version of that of the intersection, then the same holds for the sets of
the σ-algebra generated by `p`: those sets contain `∅` and are closed under complements and
countable disjoint unions. -/
private lemma isCondExp_inter_of_mem_generateFrom (hm' : m' ≤ mΩ) {p : Set (Set Ω)}
    (hp : IsPiSystem p) (hpμ : ∀ u ∈ p, NullMeasurableSet u μ) {t : Set Ω}
    (ht : NullMeasurableSet t μ) {gt : Ω → ℝ}
    (hgt : IsCondExp m' μ (t.indicator fun _ ↦ (1 : ℝ)) gt)
    (h : ∀ u ∈ p, ∀ ⦃gu : Ω → ℝ⦄, IsCondExp m' μ (u.indicator fun _ ↦ (1 : ℝ)) gu →
      IsCondExp m' μ ((t ∩ u).indicator fun _ ↦ (1 : ℝ)) (gt * gu))
    {u : Set Ω} (hu : u ∈ generateFrom p) {gu : Ω → ℝ}
    (hgu : IsCondExp m' μ (u.indicator fun _ ↦ (1 : ℝ)) gu) :
    IsCondExp m' μ ((t ∩ u).indicator fun _ ↦ (1 : ℝ)) (gt * gu) := by
  have hgen : ∀ v ∈ generateFrom p, NullMeasurableSet v μ := fun v hv ↦
    nullMeasurableSet_of_mem_generateFrom hpμ hv
  induction u, hu using induction_on_inter rfl hp generalizing gu with
  | empty =>
    have h0 : gu =ᵐ[μ] 0 := hgu.ae_eq hm' (integrable_indicator_one .empty)
      isCondExp_indicator_empty
    rw [Set.inter_empty]
    refine isCondExp_indicator_empty.congr_right ?_
    filter_upwards [h0] with ω hω
    simp [hω]
  | basic v hv => exact h v hv hgu
  | compl v hv ihv =>
    have hv' := hgen v hv
    obtain ⟨gv, hgv⟩ := exists_isCondExp_indicator hm' hv'
    have h_compl : gu =ᵐ[μ] 1 - gv :=
      hgu.ae_eq hm' (integrable_indicator_one hv'.compl) (hgv.indicator_compl_one hv')
    rw [show t ∩ vᶜ = t \ (t ∩ v) by rw [Set.sdiff_self_inter, Set.sdiff_eq]]
    refine (hgt.indicator_sdiff (ihv hgv) ht (ht.inter hv') Set.inter_subset_left
      (integrable_const 1).integrableOn).congr_right ?_
    filter_upwards [h_compl] with ω hω
    simp only [Pi.sub_apply, Pi.mul_apply, Pi.one_apply] at hω ⊢
    rw [hω]
    ring
  | iUnion f hfd hfm ihf =>
    have hf' : ∀ i, NullMeasurableSet (f i) μ := fun i ↦ hgen _ (hfm i)
    choose gf hgf using fun i ↦ exists_isCondExp_indicator hm' (hf' i)
    have h_eq : gu =ᵐ[μ] fun ω ↦ ∑' i, gf i ω :=
      hgu.ae_eq hm' (integrable_indicator_one (.iUnion hf'))
        (IsCondExp.indicator_iUnion hm' hgf hf' hfd (integrable_const 1).integrableOn)
    rw [Set.inter_iUnion]
    refine (IsCondExp.indicator_iUnion hm' (fun i ↦ ihf i (hgf i)) (fun i ↦ ht.inter (hf' i))
      (hfd.mono fun i j h ↦ (h.inter_left' t).inter_right' t)
      (integrable_const 1).integrableOn).congr_right ?_
    filter_upwards [h_eq] with ω hω
    simp only [Pi.mul_apply]
    rw [hω, tsum_mul_left]

end CondProb

section Definitions

/-- A family of sets of sets `π : ι → Set (Set Ω)` is conditionally independent given `m'` with
respect to a finite measure `μ` if its sets are null-measurable and, for any finite set of indices
`s = {i_1, ..., i_n}`, any sets `f i_1 ∈ π i_1, ..., f i_n ∈ π i_n` and any versions `g i` of their
conditional probabilities given `m'`, the product `∏ i ∈ s, g i` is a version of the conditional
probability of `⋂ i ∈ s, f i`. The empty intersection `Set.univ` has the conditional probability
`1`. Versions are unique almost everywhere, so one choice of versions suffices
(`ProbabilityTheory.iCondIndepSets.of_isCondExp`), and this is the identity
`μ⟦⋂ i ∈ s, f i | m'⟧ = ∏ i : s, μ⟦f i | m'⟧` of germs
(`ProbabilityTheory.iCondIndepSets_iff_condExp`).
It will be used for families of π-systems. -/
structure iCondIndepSets (m' : SigmaAlgebra Ω) {mΩ : SigmaAlgebra Ω} (hm' : m' ≤ mΩ)
    (π : ι → Set (Set Ω)) (μ : Measure Ω := by volume_tac) [IsFiniteMeasure μ] : Prop where
  /-- The sets of the family are null-measurable. -/
  nullMeasurableSet : ∀ i, ∀ s ∈ π i, NullMeasurableSet s μ
  /-- The product of versions of the conditional probabilities of finitely many sets of the family
  is a version of the conditional probability of their intersection. -/
  isCondExp_biInter : ∀ (s : Finset ι) {f : ι → Set Ω}, (∀ i ∈ s, f i ∈ π i) →
    ∀ ⦃g : ι → Ω → ℝ⦄, (∀ i ∈ s, IsCondExp m' μ ((f i).indicator fun _ ↦ (1 : ℝ)) (g i)) →
      IsCondExp m' μ ((⋂ i ∈ s, f i).indicator fun _ ↦ (1 : ℝ)) (∏ i ∈ s, g i)

/-- Two sets of sets `s₁, s₂` are conditionally independent given `m'` with respect to a finite
measure `μ` if their sets are null-measurable and, for any sets `t₁ ∈ s₁, t₂ ∈ s₂` and any versions
`g₁, g₂` of their conditional probabilities given `m'`, the product `g₁ * g₂` is a version of the
conditional probability of `t₁ ∩ t₂`. Versions are unique almost everywhere, so one choice of
versions suffices (`ProbabilityTheory.CondIndepSets.of_isCondExp`), and this is the identity
`μ⟦t₁ ∩ t₂ | m'⟧ = μ⟦t₁ | m'⟧ * μ⟦t₂ | m'⟧` of germs
(`ProbabilityTheory.condIndepSets_iff_condExp`). -/
structure CondIndepSets (m' : SigmaAlgebra Ω) {mΩ : SigmaAlgebra Ω} (hm' : m' ≤ mΩ)
    (s1 s2 : Set (Set Ω)) (μ : Measure Ω := by volume_tac) [IsFiniteMeasure μ] : Prop where
  /-- The sets of the first family are null-measurable. -/
  nullMeasurableSet_left : ∀ s ∈ s1, NullMeasurableSet s μ
  /-- The sets of the second family are null-measurable. -/
  nullMeasurableSet_right : ∀ s ∈ s2, NullMeasurableSet s μ
  /-- The product of versions of the conditional probabilities of two sets is a version of the
  conditional probability of their intersection. -/
  isCondExp_inter : ∀ t1 t2, t1 ∈ s1 → t2 ∈ s2 → ∀ ⦃g1 g2 : Ω → ℝ⦄,
    IsCondExp m' μ (t1.indicator fun _ ↦ (1 : ℝ)) g1 →
    IsCondExp m' μ (t2.indicator fun _ ↦ (1 : ℝ)) g2 →
      IsCondExp m' μ ((t1 ∩ t2).indicator fun _ ↦ (1 : ℝ)) (g1 * g2)

section

variable (m' : SigmaAlgebra Ω) {mΩ : SigmaAlgebra Ω} (hm' : m' ≤ mΩ)

/-- A family of σ-algebras is conditionally independent given `m'` with respect to a finite measure
`μ` if the family of sets of sets they define is conditionally independent: their sets are
null-measurable and, for any finite set of indices `s = {i_1, ..., i_n}`, any sets
`f i_1 ∈ m i_1, ..., f i_n ∈ m i_n` and any versions of their conditional probabilities given `m'`,
the product of the versions is a version of the conditional probability of `⋂ i ∈ s, f i`.
See `ProbabilityTheory.iCondIndep_iff_condExp` for the identity
`μ⟦⋂ i ∈ s, f i | m'⟧ = ∏ i : s, μ⟦f i | m'⟧`. -/
def iCondIndep (m : ι → SigmaAlgebra Ω)
    (μ : @Measure Ω mΩ := by volume_tac) [IsFiniteMeasure μ] : Prop :=
  iCondIndepSets m' hm' (fun x ↦ (m x : Set (Set Ω))) μ

end

/-- Two σ-algebras `m₁, m₂` are conditionally independent given `m'` with respect to a finite
measure `μ` if their sets are null-measurable and, for any sets `t₁ ∈ m₁, t₂ ∈ m₂` and any versions
of their conditional probabilities given `m'`, the product of the versions is a version of the
conditional probability of `t₁ ∩ t₂`.
See `ProbabilityTheory.condIndep_iff_condExp` for the identity
`μ⟦t₁ ∩ t₂ | m'⟧ = μ⟦t₁ | m'⟧ * μ⟦t₂ | m'⟧`. -/
def CondIndep (m' m₁ m₂ : SigmaAlgebra Ω) {mΩ : SigmaAlgebra Ω} (hm' : m' ≤ mΩ)
    (μ : Measure Ω := by volume_tac) [IsFiniteMeasure μ] : Prop :=
  CondIndepSets m' hm' (m₁ : Set (Set Ω)) (m₂ : Set (Set Ω)) μ

section

variable (m' : SigmaAlgebra Ω) {mΩ : SigmaAlgebra Ω} (hm' : m' ≤ mΩ)

/-- A family of sets is conditionally independent if the family of σ-algebras they generate is
conditionally independent. For a set `s`, the generated σ-algebra has measurable sets
`∅, s, sᶜ, univ`.
See `ProbabilityTheory.iCondIndepSet_iff_condExp`. -/
def iCondIndepSet (s : ι → Set Ω) (μ : Measure Ω := by volume_tac) [IsFiniteMeasure μ] : Prop :=
  iCondIndep m' hm' (fun i ↦ generateFrom {s i}) μ

/-- Two sets are conditionally independent if the two σ-algebras they generate are conditionally
independent. For a set `s`, the generated σ-algebra has measurable sets `∅, s, sᶜ, univ`.
See `ProbabilityTheory.condIndepSet_iff_condExp`. -/
def CondIndepSet (s t : Set Ω) (μ : Measure Ω := by volume_tac) [IsFiniteMeasure μ] : Prop :=
  CondIndep m' (generateFrom {s}) (generateFrom {t}) hm' μ

/-- A family of functions defined on the same space `Ω` and taking values in possibly different
spaces, each with a σ-algebra, is conditionally independent if the family of σ-algebras they
generate on `Ω` is conditionally independent. For a function `g` with codomain having σ-algebra
`m`, the generated σ-algebra is `m.comap g`.
See `ProbabilityTheory.iCondIndepFun_iff_condExp_inter_preimage_eq_mul`. -/
def iCondIndepFun {β : ι → Type*} [m : ∀ x : ι, SigmaAlgebra (β x)]
    (f : ∀ x : ι, Ω → β x) (μ : Measure Ω := by volume_tac) [IsFiniteMeasure μ] : Prop :=
  iCondIndep m' hm' (fun x ↦ SigmaAlgebra.comap (f x) (m x)) μ

/-- Two functions are conditionally independent if the two σ-algebras they generate are
conditionally independent. For a function `f` with codomain having σ-algebra `m`, the generated
σ-algebra is `m.comap f`.
See `ProbabilityTheory.condIndepFun_iff_condExp_inter_preimage_eq_mul`.
We use the notation `X ⟂ᵢ[Z, hZ; μ] Y` to write that `X` and `Y` are conditionally independent
given (the σ-algebra generated by) `Z` (scoped in `ProbabilityTheory`). -/
def CondIndepFun {β γ : Type*} [SigmaAlgebra β] [SigmaAlgebra γ]
    (f : Ω → β) (g : Ω → γ) (μ : Measure Ω := by volume_tac) [IsFiniteMeasure μ] : Prop :=
  CondIndep m' (SigmaAlgebra.comap f inferInstance) (SigmaAlgebra.comap g inferInstance) hm' μ

end

end Definitions

@[inherit_doc ProbabilityTheory.CondIndepFun]
scoped[ProbabilityTheory] notation3 X:50 " ⟂ᵢ[" Z ", " hZ "; " μ "] " Y:50 =>
  ProbabilityTheory.CondIndepFun (SigmaAlgebra.comap Z inferInstance) (Measurable.comap_le hZ)
  X Y μ

@[inherit_doc ProbabilityTheory.CondIndepFun]
scoped[ProbabilityTheory] notation3 X:50 " ⟂ᵢ[" Z ", " hZ "] " Y:50 =>
  ProbabilityTheory.CondIndepFun (SigmaAlgebra.comap Z inferInstance) (Measurable.comap_le hZ)
  X Y volume

/-! ### The sets are null-measurable

Conditional independence carries the null-measurability of the sets whose conditional probabilities
it compares. -/

section Domain

variable {m' m₁ m₂ : SigmaAlgebra Ω} {mΩ : SigmaAlgebra Ω} {hm' : m' ≤ mΩ} {μ : Measure Ω}
  [IsFiniteMeasure μ]

lemma iCondIndep.nullMeasurableSet {m : ι → SigmaAlgebra Ω} (h : iCondIndep m' hm' m μ) :
    ∀ i, ∀ s ∈ m i, NullMeasurableSet s μ :=
  iCondIndepSets.nullMeasurableSet h

/-- The sets of the σ-algebra generated by the σ-algebras of a conditionally independent family
are null-measurable. -/
lemma iCondIndep.nullMeasurableSet_iSup {m : ι → SigmaAlgebra Ω} (h : iCondIndep m' hm' m μ)
    {s : Set Ω} (hs : s ∈ ⨆ i, m i) : NullMeasurableSet s μ :=
  nullMeasurableSet_of_mem_generateFrom (fun t ht ↦ by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 ht
    exact h.nullMeasurableSet i t hi) (SigmaAlgebra.mem_iSup_iff.1 hs)

lemma CondIndep.nullMeasurableSet_left (h : CondIndep m' m₁ m₂ hm' μ) :
    ∀ s ∈ m₁, NullMeasurableSet s μ :=
  CondIndepSets.nullMeasurableSet_left h

lemma CondIndep.nullMeasurableSet_right (h : CondIndep m' m₁ m₂ hm' μ) :
    ∀ s ∈ m₂, NullMeasurableSet s μ :=
  CondIndepSets.nullMeasurableSet_right h

lemma iCondIndepSet.nullMeasurableSet {s : ι → Set Ω} (h : iCondIndepSet m' hm' s μ) (i : ι) :
    NullMeasurableSet (s i) μ :=
  iCondIndepSets.nullMeasurableSet h i (s i) (mem_generateFrom (Set.mem_singleton _))

lemma CondIndepSet.nullMeasurableSet_left {s t : Set Ω} (h : CondIndepSet m' hm' s t μ) :
    NullMeasurableSet s μ :=
  CondIndepSets.nullMeasurableSet_left h s (mem_generateFrom (Set.mem_singleton _))

lemma CondIndepSet.nullMeasurableSet_right {s t : Set Ω} (h : CondIndepSet m' hm' s t μ) :
    NullMeasurableSet t μ :=
  CondIndepSets.nullMeasurableSet_right h t (mem_generateFrom (Set.mem_singleton _))

lemma iCondIndepFun.nullMeasurable {β : ι → Type*} {m : ∀ i, SigmaAlgebra (β i)}
    {f : ∀ i, Ω → β i} (h : iCondIndepFun m' hm' f μ) (i : ι) : NullMeasurable (f i) μ :=
  fun _ ht ↦ iCondIndepSets.nullMeasurableSet h i _ ⟨_, ht, rfl⟩

lemma CondIndepFun.nullMeasurable_left {β γ : Type*} {mβ : SigmaAlgebra β} {mγ : SigmaAlgebra γ}
    {f : Ω → β} {g : Ω → γ} (h : CondIndepFun m' hm' f g μ) : NullMeasurable f μ :=
  fun _ ht ↦ CondIndepSets.nullMeasurableSet_left h _ ⟨_, ht, rfl⟩

lemma CondIndepFun.nullMeasurable_right {β γ : Type*} {mβ : SigmaAlgebra β}
    {mγ : SigmaAlgebra γ} {f : Ω → β} {g : Ω → γ} (h : CondIndepFun m' hm' f g μ) :
    NullMeasurable g μ :=
  fun _ ht ↦ CondIndepSets.nullMeasurableSet_right h _ ⟨_, ht, rfl⟩

end Domain

/-! ### One choice of versions suffices

Versions of the conditional probabilities of null-measurable sets are unique almost everywhere, so
the defining property holds for all versions as soon as it holds for some. -/

section OfIsCondExp

variable {m' : SigmaAlgebra Ω} {mΩ : SigmaAlgebra Ω} {hm' : m' ≤ mΩ} {μ : Measure Ω}
  [IsFiniteMeasure μ]

/-- A family of sets of null-measurable sets is conditionally independent as soon as, for every
finite set of indices and sets of the family, the product of some versions of the conditional
probabilities of the sets is a version of the conditional probability of their intersection. -/
theorem iCondIndepSets.of_isCondExp {π : ι → Set (Set Ω)}
    (hπ : ∀ i, ∀ s ∈ π i, NullMeasurableSet s μ)
    (h : ∀ (s : Finset ι) {f : ι → Set Ω}, (∀ i ∈ s, f i ∈ π i) → ∃ g : ι → Ω → ℝ,
      (∀ i ∈ s, IsCondExp m' μ ((f i).indicator fun _ ↦ (1 : ℝ)) (g i)) ∧
        IsCondExp m' μ ((⋂ i ∈ s, f i).indicator fun _ ↦ (1 : ℝ)) (∏ i ∈ s, g i)) :
    iCondIndepSets m' hm' π μ := by
  refine ⟨hπ, fun s f hf g' hg' ↦ ?_⟩
  obtain ⟨g, hg, hprod⟩ := h s hf
  exact hprod.congr_right (eventuallyEq_prod fun i hi ↦
    (hg i hi).ae_eq hm' (integrable_indicator_one (hπ i _ (hf i hi))) (hg' i hi))

/-- Two sets of null-measurable sets are conditionally independent as soon as, for all sets
`t₁ ∈ s₁` and `t₂ ∈ s₂`, the product of some versions of the conditional probabilities of `t₁` and
`t₂` is a version of the conditional probability of `t₁ ∩ t₂`. -/
theorem CondIndepSets.of_isCondExp {s1 s2 : Set (Set Ω)}
    (hs1 : ∀ s ∈ s1, NullMeasurableSet s μ) (hs2 : ∀ s ∈ s2, NullMeasurableSet s μ)
    (h : ∀ t1 t2, t1 ∈ s1 → t2 ∈ s2 → ∃ g1 g2 : Ω → ℝ,
      IsCondExp m' μ (t1.indicator fun _ ↦ (1 : ℝ)) g1 ∧
        IsCondExp m' μ (t2.indicator fun _ ↦ (1 : ℝ)) g2 ∧
          IsCondExp m' μ ((t1 ∩ t2).indicator fun _ ↦ (1 : ℝ)) (g1 * g2)) :
    CondIndepSets m' hm' s1 s2 μ := by
  refine ⟨hs1, hs2, fun t1 t2 ht1 ht2 g1' g2' hg1' hg2' ↦ ?_⟩
  obtain ⟨g1, g2, hg1, hg2, hprod⟩ := h t1 t2 ht1 ht2
  exact hprod.congr_right ((hg1.ae_eq hm' (integrable_indicator_one (hs1 t1 ht1)) hg1').mul
    (hg2.ae_eq hm' (integrable_indicator_one (hs2 t2 ht2)) hg2'))

end OfIsCondExp

/-! ### Characterizations

Each notion is characterized with versions of the conditional probabilities, which is the
definition, and through the conditional probabilities as germs along `ae μ`, which is the textbook
statement (the lemmas with the suffix `_condExp`). The germ `μ⟦t | m'⟧` takes a proof of its
domain `HasUniqueCondExp`, which the statements derive from the null-measurability of `t`. -/

section DefinitionLemmas

section
variable (m' : SigmaAlgebra Ω) {mΩ : SigmaAlgebra Ω} (hm' : m' ≤ mΩ)

lemma iCondIndepSets_iff (π : ι → Set (Set Ω)) (μ : Measure Ω) [IsFiniteMeasure μ]
    (hπ : ∀ i, ∀ s ∈ π i, NullMeasurableSet s μ) :
    iCondIndepSets m' hm' π μ ↔ ∀ (s : Finset ι) {f : ι → Set Ω}, (∀ i ∈ s, f i ∈ π i) →
      ∀ ⦃g : ι → Ω → ℝ⦄, (∀ i ∈ s, IsCondExp m' μ ((f i).indicator fun _ ↦ (1 : ℝ)) (g i)) →
        IsCondExp m' μ ((⋂ i ∈ s, f i).indicator fun _ ↦ (1 : ℝ)) (∏ i ∈ s, g i) :=
  ⟨fun h ↦ h.isCondExp_biInter, fun h ↦ ⟨hπ, h⟩⟩

/-- A family of sets of null-measurable sets is conditionally independent exactly when
`μ⟦⋂ i ∈ s, f i | m'⟧ = ∏ i : s, μ⟦f i | m'⟧` for every finite set of indices `s` and sets
`f i ∈ π i`, as germs along `ae μ`. -/
lemma iCondIndepSets_iff_condExp (π : ι → Set (Set Ω)) (μ : Measure Ω) [IsFiniteMeasure μ]
    (hπ : ∀ i, ∀ s ∈ π i, NullMeasurableSet s μ) :
    iCondIndepSets m' hm' π μ ↔ ∀ (s : Finset ι) {f : ι → Set Ω} (hf : ∀ i ∈ s, f i ∈ π i),
      haveI : NullMeasurableSet (⋂ i ∈ s, f i) μ :=
        .biInter s.countable_toSet fun i hi ↦ hπ i _ (hf i hi)
      μ⟦⋂ i ∈ s, f i | m'⟧ = ∏ i : s, haveI := hπ i _ (hf i i.2); μ⟦f i | m'⟧ := by
  rw [iCondIndepSets_iff m' hm' π μ hπ]
  exact forall_congr' fun s ↦ forall_congr' fun f ↦ forall_congr' fun hf ↦
    forall_isCondExp_prod_iff hm' (.biInter s.countable_toSet fun i hi ↦ hπ i _ (hf i hi))
      fun i hi ↦ hπ i _ (hf i hi)

lemma condIndepSets_iff (s1 s2 : Set (Set Ω)) (μ : Measure Ω) [IsFiniteMeasure μ]
    (hs1 : ∀ s ∈ s1, NullMeasurableSet s μ) (hs2 : ∀ s ∈ s2, NullMeasurableSet s μ) :
    CondIndepSets m' hm' s1 s2 μ ↔ ∀ t1 t2, t1 ∈ s1 → t2 ∈ s2 → ∀ ⦃g1 g2 : Ω → ℝ⦄,
      IsCondExp m' μ (t1.indicator fun _ ↦ (1 : ℝ)) g1 →
      IsCondExp m' μ (t2.indicator fun _ ↦ (1 : ℝ)) g2 →
        IsCondExp m' μ ((t1 ∩ t2).indicator fun _ ↦ (1 : ℝ)) (g1 * g2) :=
  ⟨fun h ↦ h.isCondExp_inter, fun h ↦ ⟨hs1, hs2, h⟩⟩

/-- Two sets of null-measurable sets are conditionally independent exactly when
`μ⟦t₁ ∩ t₂ | m'⟧ = μ⟦t₁ | m'⟧ * μ⟦t₂ | m'⟧` for all `t₁ ∈ s₁` and `t₂ ∈ s₂`, as germs along
`ae μ`. -/
lemma condIndepSets_iff_condExp (s1 s2 : Set (Set Ω)) (μ : Measure Ω) [IsFiniteMeasure μ]
    (hs1 : ∀ s ∈ s1, NullMeasurableSet s μ) (hs2 : ∀ s ∈ s2, NullMeasurableSet s μ) :
    CondIndepSets m' hm' s1 s2 μ ↔ ∀ t1 t2 (ht1 : t1 ∈ s1) (ht2 : t2 ∈ s2),
      haveI := hs1 t1 ht1; haveI := hs2 t2 ht2; haveI := (hs1 t1 ht1).inter (hs2 t2 ht2)
      μ⟦t1 ∩ t2 | m'⟧ = μ⟦t1 | m'⟧ * μ⟦t2 | m'⟧ := by
  rw [condIndepSets_iff m' hm' s1 s2 μ hs1 hs2]
  exact forall₄_congr fun t1 t2 ht1 ht2 ↦ forall_isCondExp_mul_iff hm'
    ((hs1 t1 ht1).inter (hs2 t2 ht2)) (hs1 t1 ht1) (hs2 t2 ht2)

lemma iCondIndepSets_singleton_iff (s : ι → Set Ω) (μ : Measure Ω) [IsFiniteMeasure μ]
    (hπ : ∀ i, NullMeasurableSet (s i) μ) :
    iCondIndepSets m' hm' (fun i ↦ {s i}) μ ↔ ∀ (S : Finset ι) ⦃g : ι → Ω → ℝ⦄,
      (∀ i ∈ S, IsCondExp m' μ ((s i).indicator fun _ ↦ (1 : ℝ)) (g i)) →
        IsCondExp m' μ ((⋂ i ∈ S, s i).indicator fun _ ↦ (1 : ℝ)) (∏ i ∈ S, g i) := by
  rw [iCondIndepSets_iff _ _ _ _ fun i t ht ↦ (Set.mem_singleton_iff.1 ht).symm ▸ hπ i]
  refine ⟨fun h S ↦ h S (f := s) fun i _ ↦ Set.mem_singleton _, fun h S f hf g hg ↦ ?_⟩
  have hfs : ∀ i ∈ S, f i = s i := fun i hi ↦ Set.mem_singleton_iff.1 (hf i hi)
  rw [Set.iInter₂_congr hfs]
  exact h S fun i hi ↦ hfs i hi ▸ hg i hi

lemma iCondIndepSets_singleton_iff_condExp (s : ι → Set Ω) (μ : Measure Ω) [IsFiniteMeasure μ]
    (hπ : ∀ i, NullMeasurableSet (s i) μ) :
    iCondIndepSets m' hm' (fun i ↦ {s i}) μ ↔ ∀ S : Finset ι,
      haveI : NullMeasurableSet (⋂ i ∈ S, s i) μ := .biInter S.countable_toSet fun i _ ↦ hπ i
      μ⟦⋂ i ∈ S, s i | m'⟧ = ∏ i ∈ S, haveI := hπ i; μ⟦s i | m'⟧ := by
  rw [iCondIndepSets_singleton_iff m' hm' s μ hπ]
  exact forall_congr' fun S ↦
    forall_isCondExp_prod_iff' hm' (.biInter S.countable_toSet fun i _ ↦ hπ i) hπ

theorem condIndepSets_singleton_iff {μ : Measure Ω} [IsFiniteMeasure μ]
    {s t : Set Ω} (hs : NullMeasurableSet s μ) (ht : NullMeasurableSet t μ) :
    CondIndepSets m' hm' {s} {t} μ ↔ ∀ ⦃g1 g2 : Ω → ℝ⦄,
      IsCondExp m' μ (s.indicator fun _ ↦ (1 : ℝ)) g1 →
      IsCondExp m' μ (t.indicator fun _ ↦ (1 : ℝ)) g2 →
        IsCondExp m' μ ((s ∩ t).indicator fun _ ↦ (1 : ℝ)) (g1 * g2) := by
  rw [condIndepSets_iff _ _ _ _ _ (fun _ h ↦ Set.mem_singleton_iff.1 h ▸ hs)
    (fun _ h ↦ Set.mem_singleton_iff.1 h ▸ ht)]
  refine ⟨fun h ↦ h s t (Set.mem_singleton s) (Set.mem_singleton t), fun h t1 t2 ht1 ht2 ↦ ?_⟩
  rw [Set.mem_singleton_iff.1 ht1, Set.mem_singleton_iff.1 ht2]
  exact h

theorem condIndepSets_singleton_iff_condExp {μ : Measure Ω} [IsFiniteMeasure μ]
    {s t : Set Ω} (hs : NullMeasurableSet s μ) (ht : NullMeasurableSet t μ) :
    CondIndepSets m' hm' {s} {t} μ ↔
      haveI := hs.inter ht; μ⟦s ∩ t | m'⟧ = μ⟦s | m'⟧ * μ⟦t | m'⟧ :=
  (condIndepSets_singleton_iff m' hm' hs ht).trans
    (forall_isCondExp_mul_iff hm' (hs.inter ht) hs ht)

lemma iCondIndep_iff_iCondIndepSets (m : ι → SigmaAlgebra Ω)
    (μ : @Measure Ω mΩ) [IsFiniteMeasure μ] :
    iCondIndep m' hm' m μ ↔ iCondIndepSets m' hm' (fun x ↦ (m x : Set (Set Ω))) μ :=
  Iff.rfl

lemma iCondIndep_iff (m : ι → SigmaAlgebra Ω) (μ : @Measure Ω mΩ) [IsFiniteMeasure μ]
    (hm : ∀ i, ∀ s ∈ m i, NullMeasurableSet s μ) :
    iCondIndep m' hm' m μ ↔ ∀ (s : Finset ι) {f : ι → Set Ω}, (∀ i ∈ s, f i ∈ m i) →
      ∀ ⦃g : ι → Ω → ℝ⦄, (∀ i ∈ s, IsCondExp m' μ ((f i).indicator fun _ ↦ (1 : ℝ)) (g i)) →
        IsCondExp m' μ ((⋂ i ∈ s, f i).indicator fun _ ↦ (1 : ℝ)) (∏ i ∈ s, g i) :=
  iCondIndepSets_iff m' hm' _ μ hm

/-- A family of σ-algebras of null-measurable sets is conditionally independent exactly when
`μ⟦⋂ i ∈ s, f i | m'⟧ = ∏ i : s, μ⟦f i | m'⟧` for every finite set of indices `s` and sets
`f i ∈ m i`, as germs along `ae μ`. -/
lemma iCondIndep_iff_condExp (m : ι → SigmaAlgebra Ω) (μ : @Measure Ω mΩ) [IsFiniteMeasure μ]
    (hm : ∀ i, ∀ s ∈ m i, NullMeasurableSet s μ) :
    iCondIndep m' hm' m μ ↔ ∀ (s : Finset ι) {f : ι → Set Ω} (hf : ∀ i ∈ s, f i ∈ m i),
      haveI : NullMeasurableSet (⋂ i ∈ s, f i) μ :=
        .biInter s.countable_toSet fun i hi ↦ hm i _ (hf i hi)
      μ⟦⋂ i ∈ s, f i | m'⟧ = ∏ i : s, haveI := hm i _ (hf i i.2); μ⟦f i | m'⟧ :=
  iCondIndepSets_iff_condExp m' hm' _ μ hm

end

section CondIndep

lemma condIndep_iff_condIndepSets (m' m₁ m₂ : SigmaAlgebra Ω) {mΩ : SigmaAlgebra Ω}
    (hm' : m' ≤ mΩ) (μ : Measure Ω) [IsFiniteMeasure μ] :
    CondIndep m' m₁ m₂ hm' μ
      ↔ CondIndepSets m' hm' (m₁ : Set (Set Ω)) (m₂ : Set (Set Ω)) μ :=
  Iff.rfl

lemma condIndep_iff (m' m₁ m₂ : SigmaAlgebra Ω) {mΩ : SigmaAlgebra Ω} (hm' : m' ≤ mΩ)
    (μ : Measure Ω) [IsFiniteMeasure μ] (hm₁ : ∀ s ∈ m₁, NullMeasurableSet s μ)
    (hm₂ : ∀ s ∈ m₂, NullMeasurableSet s μ) :
    CondIndep m' m₁ m₂ hm' μ ↔ ∀ t1 t2, t1 ∈ m₁ → t2 ∈ m₂ → ∀ ⦃g1 g2 : Ω → ℝ⦄,
      IsCondExp m' μ (t1.indicator fun _ ↦ (1 : ℝ)) g1 →
      IsCondExp m' μ (t2.indicator fun _ ↦ (1 : ℝ)) g2 →
        IsCondExp m' μ ((t1 ∩ t2).indicator fun _ ↦ (1 : ℝ)) (g1 * g2) :=
  condIndepSets_iff m' hm' _ _ μ hm₁ hm₂

/-- Two σ-algebras of null-measurable sets are conditionally independent exactly when
`μ⟦t₁ ∩ t₂ | m'⟧ = μ⟦t₁ | m'⟧ * μ⟦t₂ | m'⟧` for all `t₁ ∈ m₁` and `t₂ ∈ m₂`, as germs along
`ae μ`. -/
lemma condIndep_iff_condExp (m' m₁ m₂ : SigmaAlgebra Ω) {mΩ : SigmaAlgebra Ω} (hm' : m' ≤ mΩ)
    (μ : Measure Ω) [IsFiniteMeasure μ] (hm₁ : ∀ s ∈ m₁, NullMeasurableSet s μ)
    (hm₂ : ∀ s ∈ m₂, NullMeasurableSet s μ) :
    CondIndep m' m₁ m₂ hm' μ ↔ ∀ t1 t2 (ht1 : t1 ∈ m₁) (ht2 : t2 ∈ m₂),
      haveI := hm₁ t1 ht1; haveI := hm₂ t2 ht2; haveI := (hm₁ t1 ht1).inter (hm₂ t2 ht2)
      μ⟦t1 ∩ t2 | m'⟧ = μ⟦t1 | m'⟧ * μ⟦t2 | m'⟧ :=
  condIndepSets_iff_condExp m' hm' _ _ μ hm₁ hm₂

end CondIndep

variable (m' : SigmaAlgebra Ω) {mΩ : SigmaAlgebra Ω} (hm' : m' ≤ mΩ)

lemma iCondIndepSet_iff_iCondIndep (s : ι → Set Ω) (μ : Measure Ω) [IsFiniteMeasure μ] :
    iCondIndepSet m' hm' s μ ↔ iCondIndep m' hm' (fun i ↦ generateFrom {s i}) μ :=
  Iff.rfl

lemma condIndepSet_iff_condIndep (s t : Set Ω) (μ : Measure Ω) [IsFiniteMeasure μ] :
    CondIndepSet m' hm' s t μ ↔ CondIndep m' (generateFrom {s}) (generateFrom {t}) hm' μ :=
  Iff.rfl

lemma iCondIndepFun_iff_iCondIndep {β : ι → Type*}
    (m : ∀ x : ι, SigmaAlgebra (β x)) (f : ∀ x : ι, Ω → β x)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    iCondIndepFun m' hm' f μ
      ↔ iCondIndep m' hm' (fun x ↦ SigmaAlgebra.comap (f x) (m x)) μ :=
  Iff.rfl

lemma iCondIndepFun_iff {β : ι → Type*}
    (m : ∀ x : ι, SigmaAlgebra (β x)) (f : ∀ x : ι, Ω → β x)
    (μ : Measure Ω) [IsFiniteMeasure μ] (hf : ∀ i, NullMeasurable (f i) μ) :
    iCondIndepFun m' hm' f μ ↔ ∀ (s : Finset ι) {t : ι → Set Ω},
      (∀ i ∈ s, t i ∈ (m i).comap (f i)) → ∀ ⦃g : ι → Ω → ℝ⦄,
        (∀ i ∈ s, IsCondExp m' μ ((t i).indicator fun _ ↦ (1 : ℝ)) (g i)) →
          IsCondExp m' μ ((⋂ i ∈ s, t i).indicator fun _ ↦ (1 : ℝ)) (∏ i ∈ s, g i) :=
  iCondIndep_iff m' hm' _ μ fun i _ hs ↦ (hf i).measurable'.comap_le hs

/-- A family of null-measurable functions is conditionally independent exactly when
`μ⟦⋂ i ∈ s, t i | m'⟧ = ∏ i : s, μ⟦t i | m'⟧` for every finite set of indices `s` and sets `t i`
of the σ-algebras generated by the functions, as germs along `ae μ`. -/
lemma iCondIndepFun_iff_condExp {β : ι → Type*}
    (m : ∀ x : ι, SigmaAlgebra (β x)) (f : ∀ x : ι, Ω → β x)
    (μ : Measure Ω) [IsFiniteMeasure μ] (hf : ∀ i, NullMeasurable (f i) μ) :
    iCondIndepFun m' hm' f μ ↔ ∀ (s : Finset ι) {t : ι → Set Ω}
      (ht : ∀ i ∈ s, t i ∈ (m i).comap (f i)),
      haveI : NullMeasurableSet (⋂ i ∈ s, t i) μ :=
        .biInter s.countable_toSet fun i hi ↦ (hf i).measurable'.comap_le (ht i hi)
      μ⟦⋂ i ∈ s, t i | m'⟧ = ∏ i : s,
        haveI : NullMeasurableSet (t i) μ := (hf i).measurable'.comap_le (ht i i.2)
        μ⟦t i | m'⟧ :=
  iCondIndep_iff_condExp m' hm' _ μ fun i _ hs ↦ (hf i).measurable'.comap_le hs

lemma condIndepFun_iff_condIndep {β γ : Type*} [mβ : SigmaAlgebra β]
    [mγ : SigmaAlgebra γ] (f : Ω → β) (g : Ω → γ) (μ : Measure Ω) [IsFiniteMeasure μ] :
    CondIndepFun m' hm' f g μ
      ↔ CondIndep m' (SigmaAlgebra.comap f mβ) (SigmaAlgebra.comap g mγ) hm' μ :=
  Iff.rfl

lemma condIndepFun_iff {β γ : Type*} [mβ : SigmaAlgebra β] [mγ : SigmaAlgebra γ]
    (f : Ω → β) (g : Ω → γ) (μ : Measure Ω) [IsFiniteMeasure μ] (hf : NullMeasurable f μ)
    (hg : NullMeasurable g μ) :
    CondIndepFun m' hm' f g μ ↔ ∀ t1 t2, t1 ∈ mβ.comap f → t2 ∈ mγ.comap g →
      ∀ ⦃g1 g2 : Ω → ℝ⦄, IsCondExp m' μ (t1.indicator fun _ ↦ (1 : ℝ)) g1 →
        IsCondExp m' μ (t2.indicator fun _ ↦ (1 : ℝ)) g2 →
          IsCondExp m' μ ((t1 ∩ t2).indicator fun _ ↦ (1 : ℝ)) (g1 * g2) :=
  condIndep_iff _ _ _ hm' μ (fun _ hs ↦ hf.measurable'.comap_le hs)
    (fun _ hs ↦ hg.measurable'.comap_le hs)

/-- Two null-measurable functions are conditionally independent exactly when
`μ⟦t₁ ∩ t₂ | m'⟧ = μ⟦t₁ | m'⟧ * μ⟦t₂ | m'⟧` for all sets `t₁` and `t₂` of the σ-algebras they
generate, as germs along `ae μ`. -/
lemma condIndepFun_iff_condExp {β γ : Type*} [mβ : SigmaAlgebra β] [mγ : SigmaAlgebra γ]
    (f : Ω → β) (g : Ω → γ) (μ : Measure Ω) [IsFiniteMeasure μ] (hf : NullMeasurable f μ)
    (hg : NullMeasurable g μ) :
    CondIndepFun m' hm' f g μ ↔ ∀ t1 t2 (ht1 : t1 ∈ mβ.comap f) (ht2 : t2 ∈ mγ.comap g),
      haveI : NullMeasurableSet t1 μ := hf.measurable'.comap_le ht1
      haveI : NullMeasurableSet t2 μ := hg.measurable'.comap_le ht2
      haveI : NullMeasurableSet (t1 ∩ t2) μ :=
        NullMeasurableSet.inter (hf.measurable'.comap_le ht1) (hg.measurable'.comap_le ht2)
      μ⟦t1 ∩ t2 | m'⟧ = μ⟦t1 | m'⟧ * μ⟦t2 | m'⟧ :=
  condIndep_iff_condExp _ _ _ hm' μ (fun _ hs ↦ hf.measurable'.comap_le hs)
    (fun _ hs ↦ hg.measurable'.comap_le hs)

end DefinitionLemmas

section CondIndepSets

variable {m' : SigmaAlgebra Ω} {mΩ : SigmaAlgebra Ω} {hm' : m' ≤ mΩ} {μ : Measure Ω}
  [IsFiniteMeasure μ]

@[symm]
theorem CondIndepSets.symm {s₁ s₂ : Set (Set Ω)}
    (h : CondIndepSets m' hm' s₁ s₂ μ) : CondIndepSets m' hm' s₂ s₁ μ :=
  ⟨h.nullMeasurableSet_right, h.nullMeasurableSet_left, fun t₁ t₂ ht₁ ht₂ g₁ g₂ hg₁ hg₂ ↦ by
    rw [Set.inter_comm, mul_comm]
    exact h.isCondExp_inter t₂ t₁ ht₂ ht₁ hg₂ hg₁⟩

theorem condIndepSets_of_condIndepSets_of_le_left {s₁ s₂ s₃ : Set (Set Ω)}
    (h_indep : CondIndepSets m' hm' s₁ s₂ μ) (h31 : s₃ ⊆ s₁) :
    CondIndepSets m' hm' s₃ s₂ μ :=
  ⟨fun s hs ↦ h_indep.nullMeasurableSet_left s (h31 hs), h_indep.nullMeasurableSet_right,
    fun t₁ t₂ ht₁ ht₂ ↦ h_indep.isCondExp_inter t₁ t₂ (h31 ht₁) ht₂⟩

theorem condIndepSets_of_condIndepSets_of_le_right {s₁ s₂ s₃ : Set (Set Ω)}
    (h_indep : CondIndepSets m' hm' s₁ s₂ μ) (h32 : s₃ ⊆ s₂) :
    CondIndepSets m' hm' s₁ s₃ μ :=
  ⟨h_indep.nullMeasurableSet_left, fun s hs ↦ h_indep.nullMeasurableSet_right s (h32 hs),
    fun t₁ t₂ ht₁ ht₂ ↦ h_indep.isCondExp_inter t₁ t₂ ht₁ (h32 ht₂)⟩

theorem CondIndepSets.union {s₁ s₂ s' : Set (Set Ω)}
    (h₁ : CondIndepSets m' hm' s₁ s' μ) (h₂ : CondIndepSets m' hm' s₂ s' μ) :
    CondIndepSets m' hm' (s₁ ∪ s₂) s' μ :=
  ⟨fun s hs ↦ hs.elim (h₁.nullMeasurableSet_left s) (h₂.nullMeasurableSet_left s),
    h₁.nullMeasurableSet_right, fun t₁ t₂ ht₁ ht₂ ↦
      ht₁.elim (h₁.isCondExp_inter t₁ t₂ · ht₂) (h₂.isCondExp_inter t₁ t₂ · ht₂)⟩

@[simp]
theorem CondIndepSets.union_iff {s₁ s₂ s' : Set (Set Ω)} :
    CondIndepSets m' hm' (s₁ ∪ s₂) s' μ
      ↔ CondIndepSets m' hm' s₁ s' μ ∧ CondIndepSets m' hm' s₂ s' μ :=
  ⟨fun h ↦ ⟨condIndepSets_of_condIndepSets_of_le_left h Set.subset_union_left,
    condIndepSets_of_condIndepSets_of_le_left h Set.subset_union_right⟩, fun h ↦ h.1.union h.2⟩

/-- The null-measurability of the sets of `s'` is needed for an empty family. -/
theorem CondIndepSets.iUnion {s : ι → Set (Set Ω)} {s' : Set (Set Ω)}
    (hs' : ∀ t ∈ s', NullMeasurableSet t μ) (hyp : ∀ n, CondIndepSets m' hm' (s n) s' μ) :
    CondIndepSets m' hm' (⋃ n, s n) s' μ := by
  refine ⟨fun t ht ↦ ?_, hs', fun t₁ t₂ ht₁ ht₂ ↦ ?_⟩
  · obtain ⟨n, hn⟩ := Set.mem_iUnion.1 ht
    exact (hyp n).nullMeasurableSet_left t hn
  · obtain ⟨n, hn⟩ := Set.mem_iUnion.1 ht₁
    exact (hyp n).isCondExp_inter t₁ t₂ hn ht₂

/-- The null-measurability of the sets of `s'` is needed for an empty set of indices. -/
theorem CondIndepSets.biUnion {s : ι → Set (Set Ω)} {s' : Set (Set Ω)}
    {u : Set ι} (hs' : ∀ t ∈ s', NullMeasurableSet t μ)
    (hyp : ∀ n ∈ u, CondIndepSets m' hm' (s n) s' μ) :
    CondIndepSets m' hm' (⋃ n ∈ u, s n) s' μ := by
  refine ⟨fun t ht ↦ ?_, hs', fun t₁ t₂ ht₁ ht₂ ↦ ?_⟩
  · simp_rw [Set.mem_iUnion] at ht
    obtain ⟨n, hn, ht⟩ := ht
    exact (hyp n hn).nullMeasurableSet_left t ht
  · simp_rw [Set.mem_iUnion] at ht₁
    obtain ⟨n, hn, ht₁⟩ := ht₁
    exact (hyp n hn).isCondExp_inter t₁ t₂ ht₁ ht₂

theorem CondIndepSets.inter {s₁ s' : Set (Set Ω)} (s₂ : Set (Set Ω))
    (h₁ : CondIndepSets m' hm' s₁ s' μ) :
    CondIndepSets m' hm' (s₁ ∩ s₂) s' μ :=
  condIndepSets_of_condIndepSets_of_le_left h₁ Set.inter_subset_left

theorem CondIndepSets.iInter {s : ι → Set (Set Ω)} {s' : Set (Set Ω)}
    (h : ∃ n, CondIndepSets m' hm' (s n) s' μ) :
    CondIndepSets m' hm' (⋂ n, s n) s' μ :=
  let ⟨n, hn⟩ := h
  condIndepSets_of_condIndepSets_of_le_left hn (Set.iInter_subset s n)

theorem CondIndepSets.bInter {s : ι → Set (Set Ω)} {s' : Set (Set Ω)}
    {u : Set ι} (h : ∃ n ∈ u, CondIndepSets m' hm' (s n) s' μ) :
    CondIndepSets m' hm' (⋂ n ∈ u, s n) s' μ :=
  let ⟨_, hn, h⟩ := h
  condIndepSets_of_condIndepSets_of_le_left h (Set.biInter_subset_of_mem hn)

end CondIndepSets

section CondIndep

variable {m' m₁ m₂ m₃ : SigmaAlgebra Ω} {mΩ : SigmaAlgebra Ω} {hm' : m' ≤ mΩ} {μ : Measure Ω}
  [IsFiniteMeasure μ]

@[symm]
theorem CondIndep.symm (h : CondIndep m' m₁ m₂ hm' μ) : CondIndep m' m₂ m₁ hm' μ :=
  CondIndepSets.symm h

end CondIndep

/-- The null-measurability of the sets of `m₁` is the domain of conditional independence. -/
theorem condIndep_bot_right (m₁ : SigmaAlgebra Ω) {m' : SigmaAlgebra Ω} {mΩ : SigmaAlgebra Ω}
    {hm' : m' ≤ mΩ} {μ : Measure Ω} [IsFiniteMeasure μ] (hm₁ : ∀ s ∈ m₁, NullMeasurableSet s μ) :
    CondIndep m' m₁ ⊥ hm' μ := by
  have h_bot : ∀ t ∈ (⊥ : SigmaAlgebra Ω), t = ∅ ∨ t = Set.univ := fun t ht ↦
    SigmaAlgebra.mem_bot_iff.1 ht
  refine ⟨hm₁, fun t ht ↦ ?_, fun t₁ t₂ _ ht₂ g₁ g₂ hg₁ hg₂ ↦ ?_⟩
  · rcases h_bot t ht with rfl | rfl
    exacts [nullMeasurableSet_empty, nullMeasurableSet_univ]
  · rcases h_bot t₂ ht₂ with rfl | rfl
    · have h0 : g₂ =ᵐ[μ] 0 := hg₂.ae_eq hm' (integrable_indicator_one .empty)
        isCondExp_indicator_empty
      rw [Set.inter_empty]
      refine isCondExp_indicator_empty.congr_right ?_
      filter_upwards [h0] with ω hω
      simp [hω]
    · have h1 : g₂ =ᵐ[μ] 1 := hg₂.ae_eq hm' (integrable_indicator_one .univ)
        (isCondExp_indicator_univ 1)
      rw [Set.inter_univ]
      refine hg₁.congr_right ?_
      filter_upwards [h1] with ω hω
      simp [hω]

theorem condIndep_bot_left (m₁ : SigmaAlgebra Ω) {m' : SigmaAlgebra Ω} {mΩ : SigmaAlgebra Ω}
    {hm' : m' ≤ mΩ} {μ : Measure Ω} [IsFiniteMeasure μ] (hm₁ : ∀ s ∈ m₁, NullMeasurableSet s μ) :
    CondIndep m' ⊥ m₁ hm' μ :=
  (condIndep_bot_right m₁ hm₁).symm

section CondIndep

variable {m' m₁ m₂ m₃ m₄ : SigmaAlgebra Ω} {mΩ : SigmaAlgebra Ω} {hm' : m' ≤ mΩ} {μ : Measure Ω}
  [IsFiniteMeasure μ]

theorem condIndep_of_condIndep_of_le_left (h_indep : CondIndep m' m₁ m₂ hm' μ) (h31 : m₃ ≤ m₁) :
    CondIndep m' m₃ m₂ hm' μ :=
  condIndepSets_of_condIndepSets_of_le_left h_indep fun _ hs ↦ h31 hs

theorem condIndep_of_condIndep_of_le_right (h_indep : CondIndep m' m₁ m₂ hm' μ) (h32 : m₃ ≤ m₂) :
    CondIndep m' m₁ m₃ hm' μ :=
  condIndepSets_of_condIndepSets_of_le_right h_indep fun _ hs ↦ h32 hs

/-- Conditional independence passes to σ-algebras whose sets are almost everywhere equal to sets of
the original ones: if `m₁` and `m₂` are conditionally independent given `m'`, so are sub-σ-algebras
`m₃` of `eventuallySigmaAlgebra m₁ (ae μ)` and `m₄` of `eventuallySigmaAlgebra m₂ (ae μ)`, since
almost everywhere equal sets have the same versions of their conditional probabilities. -/
theorem CondIndep.of_le_eventuallySigmaAlgebra (h : CondIndep m' m₁ m₂ hm' μ)
    (h₃ : m₃ ≤ eventuallySigmaAlgebra m₁ (ae μ)) (h₄ : m₄ ≤ eventuallySigmaAlgebra m₂ (ae μ)) :
    CondIndep m' m₃ m₄ hm' μ := by
  refine ⟨fun t ht ↦ ?_, fun t ht ↦ ?_, fun t₁ t₂ ht₁ ht₂ g₁ g₂ hg₁ hg₂ ↦ ?_⟩
  · obtain ⟨s, hs, hts⟩ := h₃ ht
    exact (h.nullMeasurableSet_left s hs).congr hts.symm
  · obtain ⟨s, hs, hts⟩ := h₄ ht
    exact (h.nullMeasurableSet_right s hs).congr hts.symm
  obtain ⟨s₁, hs₁, h₁⟩ := h₃ ht₁
  obtain ⟨s₂, hs₂, h₂⟩ := h₄ ht₂
  exact (CondIndepSets.isCondExp_inter h s₁ s₂ hs₁ hs₂
    (hg₁.congr_left (indicator_ae_eq_of_ae_eq_set h₁))
    (hg₂.congr_left (indicator_ae_eq_of_ae_eq_set h₂))).congr_left
    (indicator_ae_eq_of_ae_eq_set (h₁.inter h₂)).symm

/-- A σ-algebra contained in `m'` is conditionally independent given `m'` of every σ-algebra of
null-measurable sets: the indicator of a set of `m'` is a version of its conditional probability,
and it pulls out of the conditional expectation. More generally, a σ-algebra has this property
exactly when its sets are almost everywhere equal to sets of `m'`
(`condIndep_of_le_eventuallySigmaAlgebra_left`, `condIndep_self_iff`). -/
theorem condIndep_of_le_left (hm₁ : m₁ ≤ m') (hm₂ : ∀ s ∈ m₂, NullMeasurableSet s μ) :
    CondIndep m' m₁ m₂ hm' μ := by
  have hm₁' : ∀ s ∈ m₁, NullMeasurableSet s μ := fun s hs ↦
    (measurableSet_iff_mem.2 (hm' (hm₁ hs))).nullMeasurableSet
  refine ⟨hm₁', hm₂, fun t₁ t₂ ht₁ ht₂ g₁ g₂ hg₁ hg₂ ↦ ?_⟩
  have h_meas : AEStronglyMeasurable[m'] (t₁.indicator fun _ ↦ (1 : ℝ)) μ :=
    (stronglyMeasurable_const.indicator (hm₁ ht₁)).aestronglyMeasurable
  have h_eq : t₁.indicator (fun _ ↦ (1 : ℝ)) =ᵐ[μ] g₁ :=
    (isCondExp_self h_meas).ae_eq hm' (integrable_indicator_one (hm₁' t₁ ht₁)) hg₁
  have h_int : Integrable ((t₁.indicator fun _ ↦ (1 : ℝ)) * t₂.indicator fun _ ↦ (1 : ℝ)) μ := by
    rw [show (fun _ : Ω ↦ (1 : ℝ)) = 1 from rfl, ← Set.inter_indicator_one]
    exact integrable_indicator_one ((hm₁' t₁ ht₁).inter (hm₂ t₂ ht₂))
  rw [show (fun _ : Ω ↦ (1 : ℝ)) = 1 from rfl, Set.inter_indicator_one]
  exact (hg₂.mul_left hm' h_meas h_int (integrable_indicator_one (hm₂ t₂ ht₂))).congr_right
    (h_eq.mul (EventuallyEq.refl _ _))

theorem condIndep_of_le_right (hm₁ : ∀ s ∈ m₁, NullMeasurableSet s μ) (hm₂ : m₂ ≤ m') :
    CondIndep m' m₁ m₂ hm' μ :=
  (condIndep_of_le_left hm₂ hm₁).symm

/-- A σ-algebra whose sets are almost everywhere equal to sets of `m'`, that is, a sub-σ-algebra of
`eventuallySigmaAlgebra m' (ae μ)`, is conditionally independent given `m'` of every σ-algebra of
null-measurable sets. This condition is exact: a σ-algebra that is conditionally independent of
itself given `m'` satisfies it (`condIndep_self_iff`). -/
theorem condIndep_of_le_eventuallySigmaAlgebra_left
    (hm₁ : m₁ ≤ eventuallySigmaAlgebra m' (ae μ)) (hm₂ : ∀ s ∈ m₂, NullMeasurableSet s μ) :
    CondIndep m' m₁ m₂ hm' μ :=
  (condIndep_of_le_left (m₁ := m') le_rfl hm₂).of_le_eventuallySigmaAlgebra hm₁
    le_eventuallySigmaAlgebra

theorem condIndep_of_le_eventuallySigmaAlgebra_right (hm₁ : ∀ s ∈ m₁, NullMeasurableSet s μ)
    (hm₂ : m₂ ≤ eventuallySigmaAlgebra m' (ae μ)) : CondIndep m' m₁ m₂ hm' μ :=
  (condIndep_of_le_eventuallySigmaAlgebra_left hm₂ hm₁).symm

theorem iCondIndep_of_iCondIndep_of_le {m₁ m₂ : ι → SigmaAlgebra Ω}
    (h_indep : iCondIndep m' hm' m₂ μ) (h_le : ∀ i, m₁ i ≤ m₂ i) :
    iCondIndep m' hm' m₁ μ :=
  ⟨fun i s hs ↦ h_indep.nullMeasurableSet i s (h_le i hs), fun s _f hf ↦
    iCondIndepSets.isCondExp_biInter h_indep s fun i hi ↦ h_le i (hf i hi)⟩

/-- Conditional independence of a family passes to σ-algebras whose sets are almost everywhere
equal to sets of the original ones: if the family `m₁` is conditionally independent given `m'`, so
is every family `m₂` with `m₂ i ≤ eventuallySigmaAlgebra (m₁ i) (ae μ)` for all `i`, since almost
everywhere equal sets have the same versions of their conditional probabilities. -/
theorem iCondIndep.of_le_eventuallySigmaAlgebra {m₁ m₂ : ι → SigmaAlgebra Ω}
    (h : iCondIndep m' hm' m₁ μ) (h_le : ∀ i, m₂ i ≤ eventuallySigmaAlgebra (m₁ i) (ae μ)) :
    iCondIndep m' hm' m₂ μ := by
  refine ⟨fun i t ht ↦ ?_, fun S f hf g hg ↦ ?_⟩
  · obtain ⟨s, hs, hts⟩ := h_le i ht
    exact (h.nullMeasurableSet i s hs).congr hts.symm
  have hex : ∀ i ∈ S, ∃ s ∈ m₁ i, f i =ᵐ[μ] s := fun i hi ↦ h_le i (hf i hi)
  choose! k hk hfk using hex
  exact (h.isCondExp_biInter S hk fun i hi ↦
    (hg i hi).congr_left (indicator_ae_eq_of_ae_eq_set (hfk i hi))).congr_left
    (indicator_ae_eq_of_ae_eq_set (S.eventuallyEqSet_iInter hfk)).symm

end CondIndep

section CondIndepSet

variable {m' : SigmaAlgebra Ω} {mΩ : SigmaAlgebra Ω} {hm' : m' ≤ mΩ} {μ : Measure Ω}
  [IsFiniteMeasure μ]

theorem condIndepSet_empty_right {s : Set Ω} (hs : NullMeasurableSet s μ) :
    CondIndepSet m' hm' s ∅ μ := by
  simp only [CondIndepSet, generateFrom_singleton_empty]
  exact condIndep_bot_right _ fun t ht ↦ nullMeasurableSet_of_mem_generateFrom
    (fun _ hu ↦ (Set.mem_singleton_iff.1 hu).symm ▸ hs) ht

theorem condIndepSet_empty_left {s : Set Ω} (hs : NullMeasurableSet s μ) :
    CondIndepSet m' hm' ∅ s μ :=
  CondIndep.symm (condIndepSet_empty_right hs)

end CondIndepSet

/-! ### Deducing `CondIndep` from `iCondIndep` -/


section FromiCondIndepToCondIndep

variable {m' : SigmaAlgebra Ω} {mΩ : SigmaAlgebra Ω} {hm' : m' ≤ mΩ} {μ : Measure Ω}
  [IsFiniteMeasure μ]

theorem iCondIndepSets.condIndepSets {s : ι → Set (Set Ω)}
    (h_indep : iCondIndepSets m' hm' s μ) {i j : ι} (hij : i ≠ j) :
    CondIndepSets m' hm' (s i) (s j) μ := by
  classical
  refine ⟨h_indep.nullMeasurableSet i, h_indep.nullMeasurableSet j,
    fun t₁ t₂ ht₁ ht₂ g₁ g₂ hg₁ hg₂ ↦ ?_⟩
  have hf_m : ∀ x ∈ ({i, j} : Finset ι), (if x = i then t₁ else t₂) ∈ s x := by
    intro x hx
    rcases Finset.mem_insert.mp hx with hx | hx
    · rw [ite_eq_left hx, hx]
      exact ht₁
    · rw [Finset.mem_singleton.mp hx, ite_eq_right hij.symm]
      exact ht₂
  have hg_m : ∀ x ∈ ({i, j} : Finset ι), IsCondExp m' μ
      ((if x = i then t₁ else t₂).indicator fun _ ↦ (1 : ℝ)) (if x = i then g₁ else g₂) := by
    intro x hx
    rcases Finset.mem_insert.mp hx with hx | hx
    · simp only [ite_eq_left hx]
      exact hg₁
    · simp only [Finset.mem_singleton.mp hx, ite_eq_right hij.symm]
      exact hg₂
  have h := h_indep.isCondExp_biInter {i, j} hf_m hg_m
  rw [Finset.set_biInter_insert, Finset.set_biInter_singleton, Finset.prod_pair hij] at h
  simpa only [↓reduceIte, ite_eq_right hij.symm] using h

theorem iCondIndep.condIndep {m : ι → SigmaAlgebra Ω}
    (h_indep : iCondIndep m' hm' m μ) {i j : ι} (hij : i ≠ j) :
    CondIndep m' (m i) (m j) hm' μ :=
  iCondIndepSets.condIndepSets h_indep hij

theorem iCondIndepFun.condIndepFun {β : ι → Type*}
    {m : ∀ x, SigmaAlgebra (β x)} {f : ∀ i, Ω → β i}
    (hf_Indep : iCondIndepFun m' hm' f μ) {i j : ι} (hij : i ≠ j) :
    CondIndepFun m' hm' (f i) (f j) μ :=
  iCondIndep.condIndep hf_Indep hij

end FromiCondIndepToCondIndep

/-!
## π-system lemma

Conditional independence of σ-algebras is equivalent to conditional independence of generating
π-systems.
-/


section FromSigmaAlgebrasToSetsOfSets

/-! ### Conditional independence of σ-algebras implies conditional independence of
  generating π-systems -/

variable {m' : SigmaAlgebra Ω} {mΩ : SigmaAlgebra Ω} {hm' : m' ≤ mΩ} {μ : Measure Ω}
  [IsFiniteMeasure μ]

theorem iCondIndep.iCondIndepSets {m : ι → SigmaAlgebra Ω}
    {s : ι → Set (Set Ω)} (hms : ∀ n, m n = generateFrom (s n))
    (h_indep : iCondIndep m' hm' m μ) :
    iCondIndepSets m' hm' s μ :=
  ⟨fun i t ht ↦ h_indep.nullMeasurableSet i t ((hms i).symm ▸ mem_generateFrom ht),
    fun S _f hfs ↦ iCondIndepSets.isCondExp_biInter h_indep S fun x hxS ↦
      ((hms x).symm ▸ mem_generateFrom (hfs x hxS) : _ ∈ m x)⟩

theorem CondIndep.condIndepSets {s1 s2 : Set (Set Ω)}
    (h_indep : CondIndep m' (generateFrom s1) (generateFrom s2) hm' μ) :
    CondIndepSets m' hm' s1 s2 μ :=
  ⟨fun t ht ↦ h_indep.nullMeasurableSet_left t (mem_generateFrom ht),
    fun t ht ↦ h_indep.nullMeasurableSet_right t (mem_generateFrom ht),
    fun t1 t2 ht1 ht2 ↦ CondIndepSets.isCondExp_inter h_indep t1 t2 (mem_generateFrom ht1)
      (mem_generateFrom ht2)⟩

end FromSigmaAlgebrasToSetsOfSets

section FromPiSystemsToSigmaAlgebras

/-! ### Conditional independence of generating π-systems implies conditional independence of
  σ-algebras -/

variable {m' m₁ m₂ : SigmaAlgebra Ω} {mΩ : SigmaAlgebra Ω} {hm' : m' ≤ mΩ} {μ : Measure Ω}
  [IsFiniteMeasure μ]

/-- The σ-algebras generated by conditionally independent π-systems are conditionally independent.
The sets of the generated σ-algebras are null-measurable since those of the π-systems are. -/
theorem CondIndepSets.condIndep
    {p1 p2 : Set (Set Ω)} (hp1 : IsPiSystem p1) (hp2 : IsPiSystem p2)
    (hpm1 : m₁ = generateFrom p1) (hpm2 : m₂ = generateFrom p2)
    (hyp : CondIndepSets m' hm' p1 p2 μ) :
    CondIndep m' m₁ m₂ hm' μ := by
  subst hpm1 hpm2
  have h1 : ∀ s ∈ generateFrom p1, NullMeasurableSet s μ := fun s hs ↦
    nullMeasurableSet_of_mem_generateFrom hyp.nullMeasurableSet_left hs
  have h2 : ∀ s ∈ generateFrom p2, NullMeasurableSet s μ := fun s hs ↦
    nullMeasurableSet_of_mem_generateFrom hyp.nullMeasurableSet_right hs
  refine ⟨h1, h2, fun t1 t2 ht1 ht2 g1 g2 hg1 hg2 ↦ ?_⟩
  have step : ∀ u ∈ p1, ∀ ⦃gu : Ω → ℝ⦄, IsCondExp m' μ (u.indicator fun _ ↦ (1 : ℝ)) gu →
      IsCondExp m' μ ((t2 ∩ u).indicator fun _ ↦ (1 : ℝ)) (g2 * gu) := fun u hu gu hgu ↦ by
    have h := isCondExp_inter_of_mem_generateFrom hm' hp2 hyp.nullMeasurableSet_right
      (hyp.nullMeasurableSet_left u hu) hgu
      (fun v hv _ hgv ↦ hyp.isCondExp_inter u v hu hv hgu hgv) ht2 hg2
    rw [Set.inter_comm, mul_comm]
    exact h
  have h := isCondExp_inter_of_mem_generateFrom hm' hp1 hyp.nullMeasurableSet_left (h2 t2 ht2)
    hg2 step ht1 hg1
  rw [Set.inter_comm, mul_comm]
  exact h

theorem CondIndepSets.condIndep'
    {p1 p2 : Set (Set Ω)} (hp1 : IsPiSystem p1) (hp2 : IsPiSystem p2)
    (hyp : CondIndepSets m' hm' p1 p2 μ) :
    CondIndep m' (generateFrom p1) (generateFrom p2) hm' μ :=
  hyp.condIndep hp1 hp2 rfl rfl

theorem condIndepSets_piiUnionInter_of_disjoint {s : ι → Set (Set Ω)}
    {S T : Set ι} (h_indep : iCondIndepSets m' hm' s μ) (hST : Disjoint S T) :
    CondIndepSets m' hm' (piiUnionInter s S) (piiUnionInter s T) μ := by
  have h_meas : ∀ U : Set ι, ∀ t ∈ piiUnionInter s U, NullMeasurableSet t μ := by
    rintro U _ ⟨p, -, f, hf, rfl⟩
    exact .biInter p.countable_toSet fun i hi ↦ h_indep.nullMeasurableSet i _ (hf i hi)
  refine CondIndepSets.of_isCondExp (h_meas S) (h_meas T) ?_
  rintro t1 t2 ⟨p1, hp1, f1, ht1_m, ht1_eq⟩ ⟨p2, hp2, f2, ht2_m, ht2_eq⟩
  classical
  have h_disj : Disjoint p1 p2 := Finset.disjoint_left.2 fun i hi1 hi2 ↦
    Set.disjoint_left.1 hST (hp1 hi1) (hp2 hi2)
  let g i := ite (i ∈ p1) (f1 i) Set.univ ∩ ite (i ∈ p2) (f2 i) Set.univ
  have hg1 : ∀ i ∈ p1, g i = f1 i := fun i hi ↦ by
    simp [g, hi, Finset.disjoint_left.1 h_disj hi]
  have hg2 : ∀ i ∈ p2, g i = f2 i := fun i hi ↦ by
    simp [g, hi, Finset.disjoint_right.1 h_disj hi]
  have hgm : ∀ i ∈ p1 ∪ p2, g i ∈ s i := by
    intro i hi
    rcases Finset.mem_union.1 hi with hi | hi
    · rw [hg1 i hi]
      exact ht1_m i hi
    · rw [hg2 i hi]
      exact ht2_m i hi
  have h_inter : t1 ∩ t2 = ⋂ i ∈ p1 ∪ p2, g i := by
    rw [ht1_eq, ht2_eq]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_iInter, Finset.mem_union]
    constructor
    · rintro ⟨h1, h2⟩ i (hi | hi)
      · rw [hg1 i hi]
        exact h1 i hi
      · rw [hg2 i hi]
        exact h2 i hi
    · intro h
      exact ⟨fun i hi ↦ hg1 i hi ▸ h i (Or.inl hi), fun i hi ↦ hg2 i hi ▸ h i (Or.inr hi)⟩
  -- versions of the conditional probabilities of the sets `g i`
  choose! k hk using fun i (hi : i ∈ p1 ∪ p2) ↦
    exists_isCondExp_indicator hm' (h_indep.nullMeasurableSet i _ (hgm i hi))
  refine ⟨∏ i ∈ p1, k i, ∏ i ∈ p2, k i, ?_, ?_, ?_⟩
  · rw [ht1_eq]
    refine h_indep.isCondExp_biInter p1 ht1_m fun i hi ↦ ?_
    rw [← hg1 i hi]
    exact hk i (Finset.mem_union_left _ hi)
  · rw [ht2_eq]
    refine h_indep.isCondExp_biInter p2 ht2_m fun i hi ↦ ?_
    rw [← hg2 i hi]
    exact hk i (Finset.mem_union_right _ hi)
  · rw [h_inter, ← Finset.prod_union h_disj]
    exact h_indep.isCondExp_biInter (p1 ∪ p2) hgm hk

theorem iCondIndepSet.condIndep_generateFrom_of_disjoint {s : ι → Set Ω}
    (hs : iCondIndepSet m' hm' s μ) (S T : Set ι) (hST : Disjoint S T) :
    CondIndep m' (generateFrom { t | ∃ n ∈ S, s n = t })
      (generateFrom { t | ∃ k ∈ T, s k = t }) hm' μ := by
  rw [← generateFrom_piiUnionInter_singleton_left, ← generateFrom_piiUnionInter_singleton_left]
  exact CondIndepSets.condIndep' (isPiSystem_piiUnionInter _ (fun k ↦ IsPiSystem.singleton _) _)
    (isPiSystem_piiUnionInter _ (fun k ↦ IsPiSystem.singleton _) _)
    (condIndepSets_piiUnionInter_of_disjoint (iCondIndep.iCondIndepSets (fun n ↦ rfl) hs) hST)

theorem condIndep_iSup_of_disjoint {m : ι → SigmaAlgebra Ω}
    (h_indep : iCondIndep m' hm' m μ) {S T : Set ι} (hST : Disjoint S T) :
    CondIndep m' (⨆ i ∈ S, m i) (⨆ i ∈ T, m i) hm' μ :=
  CondIndepSets.condIndep
    (isPiSystem_piiUnionInter _ (fun n ↦ SigmaAlgebra.isPiSystem (m n)) _)
    (isPiSystem_piiUnionInter _ (fun n ↦ SigmaAlgebra.isPiSystem (m n)) _)
    (generateFrom_piiUnionInter m S).symm (generateFrom_piiUnionInter m T).symm
    (condIndepSets_piiUnionInter_of_disjoint h_indep hST)

/-- The null-measurability of the sets of `m₁` is needed for an empty family. -/
theorem condIndep_iSup_of_directed_le {m : ι → SigmaAlgebra Ω}
    (h_indep : ∀ i, CondIndep m' (m i) m₁ hm' μ) (hm₁ : ∀ s ∈ m₁, NullMeasurableSet s μ)
    (hm : Directed (· ≤ ·) m) :
    CondIndep m' (⨆ i, m i) m₁ hm' μ := by
  let p : ι → Set (Set Ω) := fun n ↦ m n
  have hp : ∀ n, IsPiSystem (p n) := fun n ↦ SigmaAlgebra.isPiSystem (m n)
  have hp_supr_pi : IsPiSystem (⋃ n, p n) := isPiSystem_iUnion_of_directed_le p hp hm
  have h_gen' : m₁ = generateFrom (m₁ : Set (Set Ω)) := (SigmaAlgebra.generateFrom_self m₁).symm
  have h_pi_system_indep : CondIndepSets m' hm' (⋃ n, p n) m₁ μ :=
    CondIndepSets.iUnion hm₁ h_indep
  exact CondIndepSets.condIndep hp_supr_pi (SigmaAlgebra.isPiSystem m₁)
    (SigmaAlgebra.iSup_eq_generateFrom _) h_gen' h_pi_system_indep

theorem iCondIndepSet.condIndep_generateFrom_lt [Preorder ι] {s : ι → Set Ω}
    (hs : iCondIndepSet m' hm' s μ) (i : ι) :
    CondIndep m' (generateFrom {s i}) (generateFrom { t | ∃ j < i, s j = t }) hm' μ := by
  convert!
    iCondIndepSet.condIndep_generateFrom_of_disjoint hs { i } {j | j < i}
      (Set.disjoint_singleton_left.mpr (lt_irrefl _)) using 1
  simp only [Set.mem_singleton_iff, exists_eq_left, Set.ofPred_eq_eq_singleton']

theorem iCondIndepSet.condIndep_generateFrom_le [Preorder ι] {s : ι → Set Ω}
    (hs : iCondIndepSet m' hm' s μ) (i : ι) {k : ι} (hk : i < k) :
    CondIndep m' (generateFrom {s k}) (generateFrom { t | ∃ j ≤ i, s j = t }) hm' μ := by
  convert!
    iCondIndepSet.condIndep_generateFrom_of_disjoint hs { k } {j | j ≤ i}
      (Set.disjoint_singleton_left.mpr hk.not_ge) using 1
  simp only [Set.mem_singleton_iff, exists_eq_left, Set.ofPred_eq_eq_singleton']

theorem iCondIndepSet.condIndep_generateFrom_le_nat {s : ℕ → Set Ω}
    (hs : iCondIndepSet m' hm' s μ) (n : ℕ) :
    CondIndep m' (generateFrom {s (n + 1)}) (generateFrom { t | ∃ k ≤ n, s k = t }) hm' μ :=
  iCondIndepSet.condIndep_generateFrom_le hs _ n.lt_succ_self

theorem condIndep_iSup_of_monotone [SemilatticeSup ι] {m : ι → SigmaAlgebra Ω}
    (h_indep : ∀ i, CondIndep m' (m i) m₁ hm' μ) (hm₁ : ∀ s ∈ m₁, NullMeasurableSet s μ)
    (hm : Monotone m) :
    CondIndep m' (⨆ i, m i) m₁ hm' μ :=
  condIndep_iSup_of_directed_le h_indep hm₁ (Monotone.directed_le hm)

theorem condIndep_iSup_of_antitone [SemilatticeInf ι] {m : ι → SigmaAlgebra Ω}
    (h_indep : ∀ i, CondIndep m' (m i) m₁ hm' μ) (hm₁ : ∀ s ∈ m₁, NullMeasurableSet s μ)
    (hm : Antitone m) :
    CondIndep m' (⨆ i, m i) m₁ hm' μ :=
  condIndep_iSup_of_directed_le h_indep hm₁ hm.directed_le

theorem iCondIndepSets.piiUnionInter_of_notMem {π : ι → Set (Set Ω)} {a : ι} {S : Finset ι}
    (hp_ind : iCondIndepSets m' hm' π μ) (haS : a ∉ S) :
    CondIndepSets m' hm' (piiUnionInter π S) (π a) μ := by
  have h_meas : ∀ t ∈ piiUnionInter π S, NullMeasurableSet t μ := by
    rintro _ ⟨p, -, f, hf, rfl⟩
    exact .biInter p.countable_toSet fun i hi ↦ hp_ind.nullMeasurableSet i _ (hf i hi)
  refine CondIndepSets.of_isCondExp h_meas (hp_ind.nullMeasurableSet a) ?_
  rintro t1 t2 ⟨s, hs_mem, ft1, hft1_mem, ht1_eq⟩ ht2_mem_pia
  rw [Finset.coe_subset] at hs_mem
  classical
  let f := fun n ↦ ite (n = a) t2 (ite (n ∈ s) (ft1 n) Set.univ)
  have h_f_mem : ∀ n ∈ insert a s, f n ∈ π n := by
    intro n hn_mem_insert
    dsimp only [f]
    rcases Finset.mem_insert.mp hn_mem_insert with hn_mem | hn_mem
    · simp [hn_mem, ht2_mem_pia]
    · grind
  have h_f_mem_pi : ∀ n ∈ s, f n ∈ π n := fun x hxS ↦ h_f_mem x (by simp [hxS])
  have h_t1 : t1 = ⋂ n ∈ s, f n := by
    suffices h_forall : ∀ n ∈ s, f n = ft1 n by grind
    intro n hnS
    have hn_ne_a : n ≠ a := by rintro rfl; exact haS (hs_mem hnS)
    simp_rw [f, ite_eq_left hnS, ite_eq_right hn_ne_a]
  have h_t2 : t2 = f a := by simp [f]
  have h_t1_inter_t2 : t1 ∩ t2 = ⋂ n ∈ insert a s, f n := by
    rw [h_t1, h_t2, Finset.set_biInter_insert, Set.inter_comm]
  have has : a ∉ s := fun has_mem ↦ haS (hs_mem has_mem)
  -- versions of the conditional probabilities of the sets `f n`
  choose! k hk using fun n (hn : n ∈ insert a s) ↦
    exists_isCondExp_indicator hm' (hp_ind.nullMeasurableSet n _ (h_f_mem n hn))
  refine ⟨∏ n ∈ s, k n, k a, ?_, ?_, ?_⟩
  · rw [h_t1]
    exact hp_ind.isCondExp_biInter s h_f_mem_pi fun n hn ↦ hk n (Finset.mem_insert_of_mem hn)
  · rw [h_t2]
    exact hk a (Finset.mem_insert_self a s)
  · rw [h_t1_inter_t2, mul_comm, ← Finset.prod_insert has]
    exact hp_ind.isCondExp_biInter (insert a s) h_f_mem hk

/-- The σ-algebras generated by conditionally independent π-systems are conditionally independent.
-/
theorem iCondIndepSets.iCondIndep (m : ι → SigmaAlgebra Ω) (π : ι → Set (Set Ω))
    (h_pi : ∀ n, IsPiSystem (π n)) (h_generate : ∀ i, m i = generateFrom (π i))
    (h_ind : iCondIndepSets m' hm' π μ) :
    iCondIndep m' hm' m μ := by
  classical
  refine ⟨fun i s hs ↦ nullMeasurableSet_of_mem_generateFrom (h_ind.nullMeasurableSet i)
    ((h_generate i) ▸ hs), ?_⟩
  intro s f
  induction s using Finset.induction_on with
  | empty =>
    intro _ g _
    simp only [Finset.notMem_empty, Set.iInter_of_empty, Set.iInter_univ, Finset.prod_empty]
    exact isCondExp_indicator_univ 1
  | insert a S ha_notin_S h_rec =>
    intro hf_m g hg
    have hf_m_S : ∀ x ∈ S, f x ∈ m x := fun x hx ↦ hf_m x (by simp [hx])
    let p := piiUnionInter π S
    set m_p := generateFrom p with hS_eq_generate
    have h_indep : CondIndep m' m_p (m a) hm' μ :=
      CondIndepSets.condIndep (isPiSystem_piiUnionInter π h_pi S) (h_pi a) hS_eq_generate
        (h_generate a) (iCondIndepSets.piiUnionInter_of_notMem h_ind ha_notin_S)
    have h_le_p : ∀ i ∈ S, m i ≤ m_p := by
      intro n hn
      rw [hS_eq_generate, h_generate n]
      exact le_generateFrom_piiUnionInter (S : Set ι) hn
    have h_S_f : ⋂ n ∈ S, f n ∈ m_p :=
      S.measurableSet_biInter fun i hi ↦ h_le_p i hi (hf_m_S i hi)
    rw [Finset.set_biInter_insert, Finset.prod_insert ha_notin_S]
    exact h_indep.symm.isCondExp_inter (f a) (⋂ n ∈ S, f n)
      (hf_m a (Finset.mem_insert_self a S)) h_S_f (hg a (Finset.mem_insert_self a S))
      (h_rec hf_m_S fun i hi ↦ hg i (Finset.mem_insert_of_mem hi))

end FromPiSystemsToSigmaAlgebras

section CondIndepSet

/-! ### Conditional independence of sets

We prove the following equivalences on `CondIndepSet`, for null-measurable sets `s, t`.
* `CondIndepSet m' hm' s t μ ↔ μ⟦s ∩ t | m'⟧ = μ⟦s | m'⟧ * μ⟦t | m'⟧`
  (`ProbabilityTheory.condIndepSet_iff_condExp`), and its form with versions
  (`ProbabilityTheory.condIndepSet_iff`),
* `CondIndepSet m' hm' s t μ ↔ CondIndepSets m' hm' {s} {t} μ`.
-/

section
variable (m' : SigmaAlgebra Ω) {mΩ : SigmaAlgebra Ω} (hm' : m' ≤ mΩ)

theorem iCondIndepSet_iff_iCondIndepSets_singleton (s : ι → Set Ω)
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    iCondIndepSet m' hm' s μ ↔ iCondIndepSets m' hm' (fun i ↦ {s i}) μ :=
  ⟨iCondIndep.iCondIndepSets fun _ ↦ rfl,
    iCondIndepSets.iCondIndep _ _ (fun _ ↦ IsPiSystem.singleton _) fun _ ↦ rfl⟩

lemma iCondIndepSet_iff (s : ι → Set Ω) (μ : Measure Ω) [IsFiniteMeasure μ]
    (hs : ∀ i, NullMeasurableSet (s i) μ) :
    iCondIndepSet m' hm' s μ ↔ ∀ (S : Finset ι) ⦃g : ι → Ω → ℝ⦄,
      (∀ i ∈ S, IsCondExp m' μ ((s i).indicator fun _ ↦ (1 : ℝ)) (g i)) →
        IsCondExp m' μ ((⋂ i ∈ S, s i).indicator fun _ ↦ (1 : ℝ)) (∏ i ∈ S, g i) := by
  rw [iCondIndepSet_iff_iCondIndepSets_singleton, iCondIndepSets_singleton_iff _ _ _ _ hs]

/-- A family of null-measurable sets is conditionally independent exactly when
`μ⟦⋂ i ∈ S, s i | m'⟧ = ∏ i ∈ S, μ⟦s i | m'⟧` for every finite set of indices `S`, as germs along
`ae μ`. -/
lemma iCondIndepSet_iff_condExp (s : ι → Set Ω) (μ : Measure Ω) [IsFiniteMeasure μ]
    (hs : ∀ i, NullMeasurableSet (s i) μ) :
    iCondIndepSet m' hm' s μ ↔ ∀ S : Finset ι,
      haveI : NullMeasurableSet (⋂ i ∈ S, s i) μ := .biInter S.countable_toSet fun i _ ↦ hs i
      μ⟦⋂ i ∈ S, s i | m'⟧ = ∏ i ∈ S, haveI := hs i; μ⟦s i | m'⟧ := by
  rw [iCondIndepSet_iff_iCondIndepSets_singleton, iCondIndepSets_singleton_iff_condExp _ _ _ _ hs]

theorem condIndepSet_iff_condIndepSets_singleton {s t : Set Ω}
    (μ : Measure Ω) [IsFiniteMeasure μ] :
    CondIndepSet m' hm' s t μ ↔ CondIndepSets m' hm' {s} {t} μ :=
  ⟨CondIndep.condIndepSets,
    fun h ↦ CondIndepSets.condIndep' (IsPiSystem.singleton s) (IsPiSystem.singleton t) h⟩

lemma condIndepSet_iff (s t : Set Ω) (μ : Measure Ω) [IsFiniteMeasure μ]
    (hs : NullMeasurableSet s μ) (ht : NullMeasurableSet t μ) :
    CondIndepSet m' hm' s t μ ↔ ∀ ⦃g1 g2 : Ω → ℝ⦄,
      IsCondExp m' μ (s.indicator fun _ ↦ (1 : ℝ)) g1 →
      IsCondExp m' μ (t.indicator fun _ ↦ (1 : ℝ)) g2 →
        IsCondExp m' μ ((s ∩ t).indicator fun _ ↦ (1 : ℝ)) (g1 * g2) := by
  rw [condIndepSet_iff_condIndepSets_singleton _ _ μ, condIndepSets_singleton_iff _ _ hs ht]

/-- Two null-measurable sets `s` and `t` are conditionally independent exactly when
`μ⟦s ∩ t | m'⟧ = μ⟦s | m'⟧ * μ⟦t | m'⟧` as germs along `ae μ`. -/
lemma condIndepSet_iff_condExp (s t : Set Ω) (μ : Measure Ω) [IsFiniteMeasure μ]
    (hs : NullMeasurableSet s μ) (ht : NullMeasurableSet t μ) :
    CondIndepSet m' hm' s t μ ↔
      haveI := hs.inter ht; μ⟦s ∩ t | m'⟧ = μ⟦s | m'⟧ * μ⟦t | m'⟧ := by
  rw [condIndepSet_iff_condIndepSets_singleton _ _ μ,
    condIndepSets_singleton_iff_condExp _ _ hs ht]

end

variable {m' m₁ m₂ : SigmaAlgebra Ω} {mΩ : SigmaAlgebra Ω} {hm' : m' ≤ mΩ}
  {s t : Set Ω} (S T : Set (Set Ω))

theorem CondIndepSets.condIndepSet_of_mem (hs : s ∈ S) (ht : t ∈ T)
    (μ : Measure Ω) [IsFiniteMeasure μ] (h_indep : CondIndepSets m' hm' S T μ) :
    CondIndepSet m' hm' s t μ :=
  (condIndepSet_iff_condIndepSets_singleton m' hm' μ).2
    (condIndepSets_of_condIndepSets_of_le_right
      (condIndepSets_of_condIndepSets_of_le_left h_indep (Set.singleton_subset_iff.2 hs))
      (Set.singleton_subset_iff.2 ht))

theorem CondIndep.condIndepSet_of_measurableSet {μ : Measure Ω} [IsFiniteMeasure μ]
    (h_indep : CondIndep m' m₁ m₂ hm' μ) {s t : Set Ω} (hs : s ∈ m₁)
    (ht : t ∈ m₂) :
    CondIndepSet m' hm' s t μ :=
  condIndep_of_condIndep_of_le_right
    (condIndep_of_condIndep_of_le_left h_indep (generateFrom_le (Set.singleton_subset_iff.2 hs)))
    (generateFrom_le (Set.singleton_subset_iff.2 ht))

theorem condIndep_iff_forall_condIndepSet (μ : Measure Ω) [IsFiniteMeasure μ] :
    CondIndep m' m₁ m₂ hm' μ ↔ ∀ s t, s ∈ m₁ → t ∈ m₂
      → CondIndepSet m' hm' s t μ :=
  ⟨fun h _ _ hs ht ↦ h.condIndepSet_of_measurableSet hs ht, fun h ↦
    ⟨fun s hs ↦ (h s ∅ hs m₂.empty_mem).nullMeasurableSet_left,
      fun t ht ↦ (h ∅ t m₁.empty_mem ht).nullMeasurableSet_right,
      fun s t hs ht ↦ CondIndepSets.isCondExp_inter (h s t hs ht) s t
        (mem_generateFrom (Set.mem_singleton s)) (mem_generateFrom (Set.mem_singleton t))⟩⟩

end CondIndepSet

section CondIndepFun

/-! ### Conditional independence of random variables

-/

variable {β β' : Type*} {m' : SigmaAlgebra Ω}
  {mΩ : SigmaAlgebra Ω} {hm' : m' ≤ mΩ} {μ : Measure Ω} [IsFiniteMeasure μ]
  {f : Ω → β} {g : Ω → β'}

/-- Two null-measurable random variables `f` and `g` are conditionally independent exactly when,
for all measurable sets `s` and `t`, the product of versions of the conditional probabilities of
`f ⁻¹' s` and `g ⁻¹' t` is a version of the conditional probability of `f ⁻¹' s ∩ g ⁻¹' t`. -/
theorem condIndepFun_iff_isCondExp_inter_preimage {mβ : SigmaAlgebra β}
    {mβ' : SigmaAlgebra β'} (hf : NullMeasurable f μ) (hg : NullMeasurable g μ) :
    CondIndepFun m' hm' f g μ ↔ ∀ s t, MeasurableSet s → MeasurableSet t →
      ∀ ⦃g1 g2 : Ω → ℝ⦄, IsCondExp m' μ ((f ⁻¹' s).indicator fun _ ↦ (1 : ℝ)) g1 →
        IsCondExp m' μ ((g ⁻¹' t).indicator fun _ ↦ (1 : ℝ)) g2 →
          IsCondExp m' μ ((f ⁻¹' s ∩ g ⁻¹' t).indicator fun _ ↦ (1 : ℝ)) (g1 * g2) := by
  rw [condIndepFun_iff _ _ _ _ _ hf hg]
  refine ⟨fun h s t hs ht ↦ ?_, fun h s t ↦ ?_⟩
  · exact h (f ⁻¹' s) (g ⁻¹' t) ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
  · rintro ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
    exact h s t hs ht

/-- Two null-measurable random variables `f` and `g` are conditionally independent exactly when
`μ⟦f ⁻¹' s ∩ g ⁻¹' t | m'⟧ = μ⟦f ⁻¹' s | m'⟧ * μ⟦g ⁻¹' t | m'⟧` for all measurable sets `s` and
`t`, as germs along `ae μ`. -/
theorem condIndepFun_iff_condExp_inter_preimage_eq_mul {mβ : SigmaAlgebra β}
    {mβ' : SigmaAlgebra β'} (hf : NullMeasurable f μ) (hg : NullMeasurable g μ) :
    CondIndepFun m' hm' f g μ ↔ ∀ s t (hs : MeasurableSet s) (ht : MeasurableSet t),
      haveI := hf hs; haveI := hg ht; haveI := (hf hs).inter (hg ht)
      μ⟦f ⁻¹' s ∩ g ⁻¹' t | m'⟧ = μ⟦f ⁻¹' s | m'⟧ * μ⟦g ⁻¹' t | m'⟧ := by
  rw [condIndepFun_iff_isCondExp_inter_preimage hf hg]
  exact forall₄_congr fun s t hs ht ↦
    forall_isCondExp_mul_iff hm' ((hf hs).inter (hg ht)) (hf hs) (hg ht)

/-- A family of null-measurable random variables is conditionally independent exactly when, for
every finite set of indices `S` and measurable sets `sets i`, the product of versions of the
conditional probabilities of the preimages `f i ⁻¹' sets i` is a version of the conditional
probability of their intersection. -/
theorem iCondIndepFun_iff_isCondExp_inter_preimage {β : ι → Type*}
    (m : ∀ x, SigmaAlgebra (β x)) (f : ∀ i, Ω → β i) (hf : ∀ i, NullMeasurable (f i) μ) :
    iCondIndepFun m' hm' f μ ↔ ∀ (S : Finset ι) {sets : ∀ i : ι, Set (β i)},
      (∀ i ∈ S, sets i ∈ m i) → ∀ ⦃g : ι → Ω → ℝ⦄,
        (∀ i ∈ S, IsCondExp m' μ ((f i ⁻¹' sets i).indicator fun _ ↦ (1 : ℝ)) (g i)) →
          IsCondExp m' μ ((⋂ i ∈ S, f i ⁻¹' sets i).indicator fun _ ↦ (1 : ℝ))
            (∏ i ∈ S, g i) := by
  rw [iCondIndepFun_iff _ _ _ _ _ hf]
  refine ⟨fun h S sets h_sets ↦ h S fun i hi ↦ ⟨sets i, h_sets i hi, rfl⟩,
    fun h S t ht g hg ↦ ?_⟩
  have ht' : ∀ i ∈ S, ∃ sets : Set (β i), sets ∈ m i ∧ f i ⁻¹' sets = t i := ht
  choose! sets h_sets h_eq using ht'
  have ht_eq : ∀ i ∈ S, t i = f i ⁻¹' sets i := fun i hi ↦ (h_eq i hi).symm
  rw [Set.iInter₂_congr ht_eq]
  exact h S h_sets fun i hi ↦ ht_eq i hi ▸ hg i hi

/-- A family of null-measurable random variables is conditionally independent exactly when
`μ⟦⋂ i ∈ S, f i ⁻¹' sets i | m'⟧ = ∏ i : S, μ⟦f i ⁻¹' sets i | m'⟧` for every finite set of
indices `S` and measurable sets `sets i`, as germs along `ae μ`. -/
theorem iCondIndepFun_iff_condExp_inter_preimage_eq_mul {β : ι → Type*}
    (m : ∀ x, SigmaAlgebra (β x)) (f : ∀ i, Ω → β i) (hf : ∀ i, NullMeasurable (f i) μ) :
    iCondIndepFun m' hm' f μ ↔ ∀ (S : Finset ι) {sets : ∀ i : ι, Set (β i)}
      (h_sets : ∀ i ∈ S, sets i ∈ m i),
      haveI : NullMeasurableSet (⋂ i ∈ S, f i ⁻¹' sets i) μ :=
        .biInter S.countable_toSet fun i hi ↦ hf i (h_sets i hi)
      μ⟦⋂ i ∈ S, f i ⁻¹' sets i | m'⟧ =
        ∏ i : S, haveI := hf i (h_sets i i.2); μ⟦f i ⁻¹' sets i | m'⟧ := by
  rw [iCondIndepFun_iff_isCondExp_inter_preimage m f hf]
  exact forall_congr' fun S ↦ forall_congr' fun sets ↦ forall_congr' fun h_sets ↦
    forall_isCondExp_prod_iff hm' (.biInter S.countable_toSet fun i hi ↦ hf i (h_sets i hi))
      fun i hi ↦ hf i (h_sets i hi)

/-- The null-measurability of `f` and `g` comes from either side: on the right, from the
preimages of `Set.univ` under the other function. -/
theorem condIndepFun_iff_condIndepSet_preimage {mβ : SigmaAlgebra β} {mβ' : SigmaAlgebra β'} :
    CondIndepFun m' hm' f g μ ↔
      ∀ s t, MeasurableSet s → MeasurableSet t → CondIndepSet m' hm' (f ⁻¹' s) (g ⁻¹' t) μ := by
  refine ⟨fun h s t hs ht ↦ CondIndep.condIndepSet_of_measurableSet h ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩,
    fun h ↦ ⟨?_, ?_, ?_⟩⟩
  · rintro _ ⟨s, hs, rfl⟩
    exact (h s Set.univ hs .univ).nullMeasurableSet_left
  · rintro _ ⟨t, ht, rfl⟩
    exact (h Set.univ t .univ ht).nullMeasurableSet_right
  · rintro _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
    exact CondIndepSets.isCondExp_inter (h s t hs ht) _ _
      (mem_generateFrom (Set.mem_singleton _)) (mem_generateFrom (Set.mem_singleton _))

@[symm]
theorem CondIndepFun.symm {mβ : SigmaAlgebra β} {mβ' : SigmaAlgebra β'}
    {f : Ω → β} {g : Ω → β'} (hfg : CondIndepFun m' hm' f g μ) :
    CondIndepFun m' hm' g f μ :=
  CondIndep.symm hfg

/-- Conditional independence of random variables is invariant under almost everywhere equality. -/
theorem CondIndepFun.congr {mβ : SigmaAlgebra β} {mβ' : SigmaAlgebra β'} {f' : Ω → β}
    {g' : Ω → β'} (hfg : CondIndepFun m' hm' f g μ) (hf : f =ᵐ[μ] f') (hg : g =ᵐ[μ] g') :
    CondIndepFun m' hm' f' g' μ :=
  hfg.of_le_eventuallySigmaAlgebra
    ((comap_measurable f).eventuallyMeasurable_of_eventuallyEq hf.symm).comap_le
    ((comap_measurable g).eventuallyMeasurable_of_eventuallyEq hg.symm).comap_le

/-- The σ-algebra generated by `φ ∘ f` is contained in the σ-algebra generated by `f` for a
measurable `φ`. -/
private lemma comap_comp_le {γ : Type*} {mβ : SigmaAlgebra β} {mγ : SigmaAlgebra γ} {φ : β → γ}
    (hφ : Measurable φ) (f : Ω → β) : mγ.comap (φ ∘ f) ≤ mβ.comap f := by
  rintro _ ⟨A, hA, rfl⟩
  exact ⟨φ ⁻¹' A, hφ hA, Set.preimage_comp.symm⟩

theorem CondIndepFun.comp {γ γ' : Type*} {_mβ : SigmaAlgebra β} {_mβ' : SigmaAlgebra β'}
    {_mγ : SigmaAlgebra γ} {_mγ' : SigmaAlgebra γ'} {φ : β → γ} {ψ : β' → γ'}
    (hfg : CondIndepFun m' hm' f g μ) (hφ : Measurable φ) (hψ : Measurable ψ) :
    CondIndepFun m' hm' (φ ∘ f) (ψ ∘ g) μ :=
  condIndep_of_condIndep_of_le_right (condIndep_of_condIndep_of_le_left hfg (comap_comp_le hφ f))
    (comap_comp_le hψ g)

/-- The null-measurability of `X` is the domain of conditional independence. -/
lemma condIndepFun_const_left {mβ : SigmaAlgebra β} {mβ' : SigmaAlgebra β'}
    (c : β) {X : Ω → β'} (hX : NullMeasurable X μ) :
    CondIndepFun m' hm' (fun _ ↦ c) X μ := by
  rw [CondIndepFun, SigmaAlgebra.comap_const]
  exact condIndep_bot_left _ fun _ hs ↦ hX.measurable'.comap_le hs

/-- The null-measurability of `X` is the domain of conditional independence. -/
lemma condIndepFun_const_right {mβ : SigmaAlgebra β} {mβ' : SigmaAlgebra β'}
    {X : Ω → β} (hX : NullMeasurable X μ) (c : β') :
    CondIndepFun m' hm' X (fun _ ↦ c) μ :=
  (condIndepFun_const_left c hX).symm

theorem CondIndepFun.neg_right {_mβ : SigmaAlgebra β} {_mβ' : SigmaAlgebra β'} [Neg β']
    [MeasurableNeg β'] (hfg : CondIndepFun m' hm' f g μ) :
    CondIndepFun m' hm' f (-g) μ := hfg.comp measurable_id measurable_neg

theorem CondIndepFun.neg_left {_mβ : SigmaAlgebra β} {_mβ' : SigmaAlgebra β'} [Neg β]
    [MeasurableNeg β] (hfg : CondIndepFun m' hm' f g μ) :
    CondIndepFun m' hm' (-f) g μ := hfg.comp measurable_neg measurable_id

/-- An `m'`-measurable random variable is conditionally independent given `m'` of every
null-measurable one, and so is one almost everywhere equal to it (`CondIndepFun.congr`). Exactly
the random variables that are `EventuallyMeasurable m' (ae μ)` have this property
(`condIndepFun_of_eventuallyMeasurable_left`, `condIndep_self_iff`). -/
lemma condIndepFun_of_measurable_left {mβ : SigmaAlgebra β} {mβ' : SigmaAlgebra β'}
    {X : Ω → β} {Y : Ω → β'} (hX : Measurable[m'] X) (hY : NullMeasurable Y μ) :
    CondIndepFun m' hm' X Y μ :=
  condIndep_of_le_left hX.comap_le fun _ hs ↦ hY.measurable'.comap_le hs

lemma condIndepFun_of_measurable_right {mβ : SigmaAlgebra β} {mβ' : SigmaAlgebra β'}
    {X : Ω → β} {Y : Ω → β'} (hX : NullMeasurable X μ) (hY : Measurable[m'] Y) :
    CondIndepFun m' hm' X Y μ :=
  (condIndepFun_of_measurable_left hY hX).symm

/-- A random variable whose σ-algebra has its sets almost everywhere equal to sets of `m'` is
conditionally independent given `m'` of every null-measurable random variable, and this condition
is exact (`condIndep_self_iff`). It holds in particular for a random variable almost everywhere
equal to an `m'`-measurable one (`Measurable.eventuallyMeasurable_of_eventuallyEq`), which is a
stronger condition in general. -/
lemma condIndepFun_of_eventuallyMeasurable_left {mβ : SigmaAlgebra β} {mβ' : SigmaAlgebra β'}
    {X : Ω → β} {Y : Ω → β'} (hX : EventuallyMeasurable m' (ae μ) X) (hY : NullMeasurable Y μ) :
    CondIndepFun m' hm' X Y μ :=
  condIndep_of_le_eventuallySigmaAlgebra_left hX.comap_le hY.measurable'.comap_le

lemma condIndepFun_of_eventuallyMeasurable_right {mβ : SigmaAlgebra β} {mβ' : SigmaAlgebra β'}
    {X : Ω → β} {Y : Ω → β'} (hX : NullMeasurable X μ) (hY : EventuallyMeasurable m' (ae μ) Y) :
    CondIndepFun m' hm' X Y μ :=
  (condIndepFun_of_eventuallyMeasurable_left hY hX).symm

lemma condIndepFun_self_left {mβ : SigmaAlgebra β} {mβ' : SigmaAlgebra β'}
    {X : Ω → β} {Z : Ω → β'} (hX : NullMeasurable X μ) (hZ : Measurable Z) :
    Z ⟂ᵢ[Z, hZ; μ] X :=
  condIndepFun_of_measurable_left (comap_measurable Z) hX

lemma condIndepFun_self_right {mβ : SigmaAlgebra β} {mβ' : SigmaAlgebra β'}
    {X : Ω → β} {Z : Ω → β'} (hX : NullMeasurable X μ) (hZ : Measurable Z) :
    X ⟂ᵢ[Z, hZ; μ] Z :=
  condIndepFun_of_measurable_right hX (comap_measurable Z)

section iCondIndepFun
variable {β : ι → Type*} {m : ∀ i, SigmaAlgebra (β i)} {f : ∀ i, Ω → β i}

/-- Conditional independence of a family of random variables is invariant under almost everywhere
equality. -/
theorem iCondIndepFun_congr {g : ∀ i, Ω → β i} (h : ∀ i, f i =ᵐ[μ] g i) :
    iCondIndepFun m' hm' f μ ↔ iCondIndepFun m' hm' g μ :=
  ⟨fun hf ↦ iCondIndep.of_le_eventuallySigmaAlgebra hf fun i ↦
      ((comap_measurable (f i)).eventuallyMeasurable_of_eventuallyEq (h i).symm).comap_le,
    fun hg ↦ iCondIndep.of_le_eventuallySigmaAlgebra hg fun i ↦
      ((comap_measurable (g i)).eventuallyMeasurable_of_eventuallyEq (h i)).comap_le⟩

alias ⟨iCondIndepFun.congr, _⟩ := iCondIndepFun_congr

/-- The null-measurability of the functions is the domain of conditional independence. -/
lemma iCondIndepFun.of_subsingleton [Subsingleton ι] (hf : ∀ i, NullMeasurable (f i) μ) :
    iCondIndepFun m' hm' f μ := by
  refine ⟨fun i _ hs ↦ (hf i).measurable'.comap_le hs, fun s t _ g hg ↦ ?_⟩
  rcases Finset.eq_empty_or_nonempty s with rfl | ⟨i, hi⟩
  · simp only [Finset.notMem_empty, Set.iInter_of_empty, Set.iInter_univ, Finset.prod_empty]
    exact isCondExp_indicator_univ 1
  · obtain rfl : s = {i} :=
      Finset.eq_singleton_iff_unique_mem.2 ⟨hi, fun j _ ↦ Subsingleton.elim j i⟩
    simp only [Finset.set_biInter_singleton, Finset.prod_singleton]
    exact hg i (Finset.mem_singleton_self i)

/-- If `f` is a family of mutually conditionally independent random variables
(`iCondIndepFun m' hm' m f μ`) and `S, T` are two disjoint finite index sets, then the tuple formed
by `f i` for `i ∈ S` is conditionally independent of the tuple `(f i)_i` for `i ∈ T`. -/
theorem iCondIndepFun.condIndepFun_finset (S T : Finset ι) (hST : Disjoint S T)
    (hf_Indep : iCondIndepFun m' hm' f μ) :
    CondIndepFun m' hm' (fun a (i : S) ↦ f i a) (fun a (i : T) ↦ f i a) μ := by
  have hf_meas : ∀ i, NullMeasurable (f i) μ := hf_Indep.nullMeasurable
  -- We introduce π-systems, built from the π-system of boxes which generates `SigmaAlgebra.pi`.
  let πSβ := Set.pi (Set.univ : Set S) ''
    Set.pi (Set.univ : Set S) fun i ↦ (m i : Set (Set (β i)))
  let πS := { s : Set Ω | ∃ t ∈ πSβ, (fun a (i : S) ↦ f i a) ⁻¹' t = s }
  have hπS_pi : IsPiSystem πS := by exact IsPiSystem.comap (@isPiSystem_pi _ _ ?_) _
  have hπS_gen : (SigmaAlgebra.pi.comap fun a (i : S) ↦ f i a) = generateFrom πS := by
    rw [generateFrom_pi.symm, comap_generateFrom]
    congr
  let πTβ := Set.pi (Set.univ : Set T) ''
      Set.pi (Set.univ : Set T) fun i ↦ (m i : Set (Set (β i)))
  let πT := { s : Set Ω | ∃ t ∈ πTβ, (fun a (i : T) ↦ f i a) ⁻¹' t = s }
  have hπT_pi : IsPiSystem πT := by exact IsPiSystem.comap (@isPiSystem_pi _ _ ?_) _
  have hπT_gen : (SigmaAlgebra.pi.comap fun a (i : T) ↦ f i a) = generateFrom πT := by
    rw [generateFrom_pi.symm, comap_generateFrom]
    congr
  -- The preimages of boxes are finite intersections of preimages of measurable sets.
  have h_box (U : Finset ι) (sets : ∀ i : U, Set (β i)) :
      (fun (ω : Ω) (i : U) ↦ f i ω) ⁻¹' Set.pi Set.univ sets = ⋂ i : U, f i ⁻¹' sets i := by
    ext x
    simp [Set.mem_pi]
  have h_box_meas (U : Finset ι) (sets : ∀ i : U, Set (β i))
      (hsets : sets ∈ Set.pi Set.univ fun i : U ↦ (m i : Set (Set (β i)))) :
      NullMeasurableSet ((fun (ω : Ω) (i : U) ↦ f i ω) ⁻¹' Set.pi Set.univ sets) μ := by
    rw [h_box]
    exact .iInter fun i ↦ hf_meas i (measurableSet_iff_mem.mpr (hsets i (Set.mem_univ i)))
  -- To prove conditional independence, we prove it for the generating π-systems, with products
  -- of versions of the conditional probabilities of preimages of measurable sets.
  refine CondIndepSets.condIndep hπS_pi hπT_pi hπS_gen hπT_gen
    (CondIndepSets.of_isCondExp ?_ ?_ ?_)
  · rintro _ ⟨_, ⟨sets, hsets, rfl⟩, rfl⟩
    exact h_box_meas S sets hsets
  · rintro _ ⟨_, ⟨sets, hsets, rfl⟩, rfl⟩
    exact h_box_meas T sets hsets
  rintro _ _ ⟨s, ⟨sets_s, hs1, hs2⟩, rfl⟩ ⟨t, ⟨sets_t, ht1, ht2⟩, rfl⟩
  simp only [Set.mem_univ_pi] at hs1 ht1
  rw [← hs2, ← ht2]
  classical
  let sets_s' : ∀ i : ι, Set (β i) := fun i ↦
    dite (i ∈ S) (fun hi ↦ sets_s ⟨i, hi⟩) fun _ ↦ Set.univ
  have h_sets_s'_eq : ∀ {i} (hi : i ∈ S), sets_s' i = sets_s ⟨i, hi⟩ := by
    intro i hi; simp_rw [sets_s', dite_eq_left hi]
  have h_sets_s'_univ : ∀ {i} (_hi : i ∈ T), sets_s' i = Set.univ := by
    intro i hi; simp_rw [sets_s', dite_eq_right (Finset.disjoint_right.mp hST hi)]
  let sets_t' : ∀ i : ι, Set (β i) := fun i ↦
    dite (i ∈ T) (fun hi ↦ sets_t ⟨i, hi⟩) fun _ ↦ Set.univ
  have h_sets_t'_univ : ∀ {i} (_hi : i ∈ S), sets_t' i = Set.univ := by
    intro i hi; simp_rw [sets_t', dite_eq_right (Finset.disjoint_left.mp hST hi)]
  have h_meas_s' : ∀ i ∈ S, sets_s' i ∈ m i := by
    intro i hi
    rw [h_sets_s'_eq hi]
    simpa using hs1 ⟨i, hi⟩
  have h_meas_t' : ∀ i ∈ T, sets_t' i ∈ m i := by
    intro i hi
    simp_rw [sets_t', dite_eq_left hi]
    simpa using ht1 ⟨i, hi⟩
  have h_eq_inter_S : (fun (ω : Ω) (i : ↥S) ↦
    f (↑i) ω) ⁻¹' Set.pi Set.univ sets_s = ⋂ i ∈ S, f i ⁻¹' sets_s' i := by
    ext1 x
    simp_rw [Set.mem_preimage, Set.mem_univ_pi, Set.mem_iInter]
    grind
  have h_eq_inter_T : (fun (ω : Ω) (i : ↥T) ↦ f (↑i) ω) ⁻¹' Set.pi Set.univ sets_t
    = ⋂ i ∈ T, f i ⁻¹' sets_t' i := by
    ext1 x
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_iInter]
    constructor <;> intro h
    · intro i hi; simp_rw [sets_t', dite_eq_left hi]; exact h ⟨i, hi⟩
    · rintro ⟨i, hi⟩; specialize h i hi; simp_rw [sets_t', dite_eq_left hi] at h; exact h
  rw [iCondIndepFun_iff_isCondExp_inter_preimage _ _ hf_meas] at hf_Indep
  have h_Inter_inter :
    ((⋂ i ∈ S, f i ⁻¹' sets_s' i) ∩ ⋂ i ∈ T, f i ⁻¹' sets_t' i) =
      ⋂ i ∈ S ∪ T, f i ⁻¹' (sets_s' i ∩ sets_t' i) := by
    ext1 x
    simp_rw [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Finset.mem_union]
    constructor <;> intro h
    · grind
    · exact ⟨fun i hi ↦ (h i (Or.inl hi)).1, fun i hi ↦ (h i (Or.inr hi)).2⟩
  have h_meas_inter : ∀ i ∈ S ∪ T, sets_s' i ∩ sets_t' i ∈ m i := by
    intro i hi_mem
    rw [Finset.mem_union] at hi_mem
    rcases hi_mem with hi_mem | hi_mem
    · rw [h_sets_t'_univ hi_mem, Set.inter_univ]
      exact h_meas_s' i hi_mem
    · rw [h_sets_s'_univ hi_mem, Set.univ_inter]
      exact h_meas_t' i hi_mem
  -- versions of the conditional probabilities of the preimages `f i ⁻¹' (sets_s' i ∩ sets_t' i)`
  choose! k hk using fun i (hi : i ∈ S ∪ T) ↦ exists_isCondExp_indicator hm'
    (hf_meas i (measurableSet_iff_mem.mpr (h_meas_inter i hi)))
  have hkS : ∀ i ∈ S,
      IsCondExp m' μ ((f i ⁻¹' sets_s' i).indicator fun _ ↦ (1 : ℝ)) (k i) := fun i hi ↦ by
    simpa only [h_sets_t'_univ hi, Set.inter_univ] using hk i (Finset.mem_union_left T hi)
  have hkT : ∀ i ∈ T,
      IsCondExp m' μ ((f i ⁻¹' sets_t' i).indicator fun _ ↦ (1 : ℝ)) (k i) := fun i hi ↦ by
    simpa only [h_sets_s'_univ hi, Set.univ_inter] using hk i (Finset.mem_union_right S hi)
  refine ⟨∏ i ∈ S, k i, ∏ i ∈ T, k i, ?_, ?_, ?_⟩
  · rw [h_eq_inter_S]
    exact hf_Indep S h_meas_s' hkS
  · rw [h_eq_inter_T]
    exact hf_Indep T h_meas_t' hkT
  · rw [h_eq_inter_S, h_eq_inter_T, h_Inter_inter, ← Finset.prod_union hST]
    exact hf_Indep (S ∪ T) h_meas_inter hk

theorem iCondIndepFun.condIndepFun_prodMk (hf_Indep : iCondIndepFun m' hm' f μ)
    (i j k : ι) (hik : i ≠ k) (hjk : j ≠ k) :
    CondIndepFun m' hm' (fun a ↦ (f i a, f j a)) (f k) μ := by
  classical
  have h_right :
      f k = (fun p : ∀ j : ({k} : Finset ι), β j ↦ p ⟨k, Finset.mem_singleton_self k⟩) ∘
        fun a (j : ({k} : Finset ι)) ↦ f j a :=
    rfl
  have h_meas_right : Measurable fun p : ∀ j : ({k} : Finset ι),
      β j ↦ p ⟨k, Finset.mem_singleton_self k⟩ :=
    measurable_pi_apply _
  let s : Finset ι := {i, j}
  have h_left : (fun ω ↦ (f i ω, f j ω)) = (fun p : ∀ l : s, β l ↦
      (p ⟨i, Finset.mem_insert_self i _⟩,
        p ⟨j, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩)) ∘
        fun a (j : s) ↦ f j a := by
    ext1 a
    simp only
    constructor
  have h_meas_left : Measurable fun p : ∀ l : s, β l ↦
      (p ⟨i, Finset.mem_insert_self i _⟩,
        p ⟨j, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩) :=
    Measurable.prod (measurable_pi_apply _) (measurable_pi_apply _)
  rw [h_left, h_right]
  refine (hf_Indep.condIndepFun_finset s {k} ?_).comp h_meas_left h_meas_right
  rw [Finset.disjoint_singleton_right]
  simp only [s, Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨hik.symm, hjk.symm⟩

open Finset in
lemma iCondIndepFun.condIndepFun_prodMk_prodMk (h_indep : iCondIndepFun m' hm' f μ)
    (i j k l : ι) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    CondIndepFun m' hm' (fun a ↦ (f i a, f j a)) (fun a ↦ (f k a, f l a)) μ := by
  classical
  let g (i j : ι) (v : Π x : ({i, j} : Finset ι), β x) : β i × β j :=
    ⟨v ⟨i, mem_insert_self _ _⟩, v ⟨j, mem_insert_of_mem <| mem_singleton_self _⟩⟩
  have hg (i j : ι) : Measurable (g i j) := by fun_prop
  exact (h_indep.condIndepFun_finset {i, j} {k, l} (by aesop)).comp (hg i j) (hg k l)

end iCondIndepFun

section Mul
variable {m : SigmaAlgebra β} [Mul β] [MeasurableMul₂ β] {f : ι → Ω → β}

@[to_additive]
lemma iCondIndepFun.indepFun_mul_left (hf_indep : iCondIndepFun m' hm' f μ)
    (i j k : ι) (hik : i ≠ k) (hjk : j ≠ k) :
    CondIndepFun m' hm' (f i * f j) (f k) μ := by
  have : CondIndepFun m' hm' (fun ω ↦ (f i ω, f j ω)) (f k) μ :=
    hf_indep.condIndepFun_prodMk i j k hik hjk
  simpa using! this.comp (measurable_fst.mul measurable_snd) measurable_id

@[to_additive]
lemma iCondIndepFun.indepFun_mul_right (hf_indep : iCondIndepFun m' hm' f μ)
    (i j k : ι) (hij : i ≠ j) (hik : i ≠ k) :
    CondIndepFun m' hm' (f i) (f j * f k) μ :=
  (hf_indep.indepFun_mul_left _ _ _ hij.symm hik.symm).symm

@[to_additive]
lemma iCondIndepFun.indepFun_mul_mul (hf_indep : iCondIndepFun m' hm' f μ)
    (i j k l : ι) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    CondIndepFun m' hm' (f i * f j) (f k * f l) μ :=
  (hf_indep.condIndepFun_prodMk_prodMk i j k l hik hil hjk hjl).comp measurable_mul measurable_mul

end Mul

section Div
variable {m : SigmaAlgebra β} [Div β] [MeasurableDiv₂ β] {f : ι → Ω → β}

@[to_additive]
lemma iCondIndepFun.indepFun_div_left (hf_indep : iCondIndepFun m' hm' f μ)
    (i j k : ι) (hik : i ≠ k) (hjk : j ≠ k) :
    CondIndepFun m' hm' (f i / f j) (f k) μ := by
  have : CondIndepFun m' hm' (fun ω ↦ (f i ω, f j ω)) (f k) μ :=
    hf_indep.condIndepFun_prodMk i j k hik hjk
  simpa using! this.comp (measurable_fst.div measurable_snd) measurable_id

@[to_additive]
lemma iCondIndepFun.indepFun_div_right (hf_indep : iCondIndepFun m' hm' f μ)
    (i j k : ι) (hij : i ≠ j) (hik : i ≠ k) :
    CondIndepFun m' hm' (f i) (f j / f k) μ :=
  (hf_indep.indepFun_div_left _ _ _ hij.symm hik.symm).symm

@[to_additive]
lemma iCondIndepFun.indepFun_div_div (hf_indep : iCondIndepFun m' hm' f μ)
    (i j k l : ι) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    CondIndepFun m' hm' (f i / f j) (f k / f l) μ :=
  (hf_indep.condIndepFun_prodMk_prodMk i j k l hik hil hjk hjl).comp measurable_div measurable_div

end Div

section CommMonoid
variable {m : SigmaAlgebra β} [CommMonoid β] [MeasurableMul₂ β] {f : ι → Ω → β}

@[to_additive]
theorem iCondIndepFun.condIndepFun_finsetProd_of_notMem
    (hf_Indep : iCondIndepFun m' hm' f μ) {s : Finset ι} {i : ι} (hi : i ∉ s) :
    CondIndepFun m' hm' (∏ j ∈ s, f j) (f i) μ := by
  have h_right : f i =
    (fun p : ({i} : Finset ι) → β ↦ p ⟨i, Finset.mem_singleton_self i⟩) ∘
    fun a (j : ({i} : Finset ι)) ↦ f j a := rfl
  have h_meas_right : Measurable fun p : ({i} : Finset ι) → β ↦
      p ⟨i, Finset.mem_singleton_self i⟩ := measurable_pi_apply _
  have h_left : ∏ j ∈ s, f j = (fun p : s → β ↦ ∏ j, p j) ∘ fun a (j : s) ↦ f j a := by
    ext1 a
    simp only [Function.comp_apply]
    have : (∏ j : ↥s, f (↑j) a) = (∏ j : ↥s, f ↑j) a := by rw [Finset.prod_apply]
    rw [this, Finset.prod_coe_sort]
  have h_meas_left : Measurable fun p : s → β ↦ ∏ j, p j :=
    Finset.univ.measurable_fun_prod fun (j : ↥s) (_H : j ∈ Finset.univ) ↦ measurable_pi_apply j
  rw [h_left, h_right]
  exact (hf_Indep.condIndepFun_finset s {i} (Finset.disjoint_singleton_left.mpr hi).symm).comp
    h_meas_left h_meas_right

@[deprecated (since := "2026-04-08")]
alias iCondIndepFun.condIndepFun_finset_sum_of_notMem :=
  iCondIndepFun.condIndepFun_finsetSum_of_notMem

@[to_additive existing, deprecated (since := "2026-04-08")]
alias iCondIndepFun.condIndepFun_finset_prod_of_notMem :=
  iCondIndepFun.condIndepFun_finsetProd_of_notMem

@[to_additive]
theorem iCondIndepFun.condIndepFun_prod_range_succ {f : ℕ → Ω → β}
    (hf_Indep : iCondIndepFun m' hm' f μ) (n : ℕ) :
    CondIndepFun m' hm' (∏ j ∈ Finset.range n, f j) (f n) μ :=
  hf_Indep.condIndepFun_finsetProd_of_notMem Finset.notMem_range_self

end CommMonoid

theorem iCondIndepSet.iCondIndepFun_indicator [Zero β] [One β] {m : SigmaAlgebra β}
    {s : ι → Set Ω} (hs : iCondIndepSet m' hm' s μ) :
    iCondIndepFun m' hm' (fun n ↦ (s n).indicator fun _ω ↦ (1 : β)) μ :=
  iCondIndep_of_iCondIndep_of_le hs fun i ↦ Measurable.comap_le
    ((@measurable_const β Ω _ (generateFrom {s i}) (1 : β)).indicator
      (mem_generateFrom (Set.mem_singleton (s i))))

end CondIndepFun

end ProbabilityTheory
