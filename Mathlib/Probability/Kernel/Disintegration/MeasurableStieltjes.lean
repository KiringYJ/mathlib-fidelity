/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Measure.Stieltjes
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

/-!
# Measurable parametric Stieltjes functions

We provide tools to build a measurable function `α → StieltjesFunction ℝ` with limits 0 at -∞
and 1 at +∞ for all `a : α` from a measurable function `f : α → ℚ → ℝ`. These measurable parametric
Stieltjes functions are cumulative distribution functions (CDF) of transition kernels.
The reason for going through `ℚ` instead of defining directly a Stieltjes function is that since
`ℚ` is countable, building a measurable function is easier and we can obtain properties of the
form `∀ᵐ (a : α) ∂μ, ∀ (q : ℚ), ...` (for some measure `μ` on `α`) by proving the weaker
`∀ (q : ℚ), ∀ᵐ (a : α) ∂μ, ...`.

This construction will be possible if `f a : ℚ → ℝ` satisfies a package of properties for all `a`:
monotonicity, limits at +-∞ and a continuity property. We define `IsRatStieltjesPoint f a` to state
that this is the case at `a` and define the property `IsMeasurableRatCDF f` that `f` is measurable
and `IsRatStieltjesPoint f a` for all `a`.
The function `α → StieltjesFunction ℝ` obtained by extending `f` by continuity from the right is
then called `IsMeasurableRatCDF.stieltjesFunction`.

In applications, we will often only have `IsRatStieltjesPoint f a` almost surely with respect to
some measure. The file `Mathlib/Probability/Kernel/Disintegration/CDFToKernel.lean` treats that case
for the conditional kernel CDFs of a finite kernel: from a function with the property
`ProbabilityTheory.IsRatCondKernelCDF`, it proves that a conditional kernel CDF exists that agrees
with it almost everywhere at every rational.

## Main definitions

* `ProbabilityTheory.IsRatStieltjesPoint f a`: `f a` is monotone with limit 0 at -∞ and 1 at +∞
  and satisfies a continuity property.
* `ProbabilityTheory.IsMeasurableRatCDF f`: `f` is measurable and `IsRatStieltjesPoint f a` holds
  for every `a`.
* `ProbabilityTheory.IsMeasurableRatCDF.stieltjesFunction`: extend a function with the property
  `IsMeasurableRatCDF` from `ℚ` to `ℝ`, giving a measurable function `α → StieltjesFunction ℝ`.

-/

@[expose] public section

open MeasureTheory Set Filter TopologicalSpace

open scoped NNReal ENNReal MeasureTheory Topology

/-- A measurable function `α → StieltjesFunction ℝ` with limits 0 at -∞ and 1 at +∞ gives a
measurable function `α → Measure ℝ` by taking `StieltjesFunction.measure` at each point. -/
lemma StieltjesFunction.measurable_measure {α : Type*} {_ : SigmaAlgebra α}
    {f : α → StieltjesFunction ℝ} (hf : ∀ q, Measurable fun a ↦ f a q)
    (hf_bot : ∀ a, Tendsto (f a) atBot (𝓝 0))
    (hf_top : ∀ a, Tendsto (f a) atTop (𝓝 1)) :
    Measurable fun a ↦ (f a).measure :=
  have : ∀ a, IsProbabilityMeasure (f a).measure :=
    fun a ↦ (f a).isProbabilityMeasure (hf_bot a) (hf_top a)
  .measure_of_isPiSystem_of_isProbabilityMeasure (borel_eq_generateFrom_Iic ℝ) isPiSystem_Iic <| by
    simp_rw [forall_mem_range, StieltjesFunction.measure_Iic (f _) (hf_bot _), sub_zero]
    exact fun _ ↦ (hf _).ennreal_ofReal

namespace ProbabilityTheory

variable {α : Type*}

section IsMeasurableRatCDF

variable {f : α → ℚ → ℝ}

/-- `a : α` is a Stieltjes point for `f : α → ℚ → ℝ` if `f a` is monotone with limit 0 at -∞
and 1 at +∞ and satisfies a continuity property. -/
structure IsRatStieltjesPoint (f : α → ℚ → ℝ) (a : α) : Prop where
  mono : Monotone (f a)
  tendsto_atTop_one : Tendsto (f a) atTop (𝓝 1)
  tendsto_atBot_zero : Tendsto (f a) atBot (𝓝 0)
  iInf_rat_gt_eq : ∀ t : ℚ, ⨅ r : Ioi t, f a r = f a t

lemma isRatStieltjesPoint_unit_prod_iff (f : α → ℚ → ℝ) (a : α) :
    IsRatStieltjesPoint (fun p : Unit × α ↦ f p.2) ((), a)
      ↔ IsRatStieltjesPoint f a := by
  constructor <;>
    exact fun h ↦ ⟨h.mono, h.tendsto_atTop_one, h.tendsto_atBot_zero, h.iInf_rat_gt_eq⟩

lemma measurableSet_isRatStieltjesPoint [SigmaAlgebra α] (hf : Measurable f) :
    MeasurableSet {a | IsRatStieltjesPoint f a} := by
  have h1 : MeasurableSet {a | Monotone (f a)} := by
    change MeasurableSet {a | ∀ q r (_ : q ≤ r), f a q ≤ f a r}
    simp_rw [Set.ofPred_forall]
    refine MeasurableSet.iInter (fun q ↦ ?_)
    refine MeasurableSet.iInter (fun r ↦ ?_)
    refine MeasurableSet.iInter (fun _ ↦ ?_)
    exact measurableSet_le hf.eval hf.eval
  have h2 : MeasurableSet {a | Tendsto (f a) atTop (𝓝 1)} :=
    measurableSet_tendsto _ (fun q ↦ hf.eval)
  have h3 : MeasurableSet {a | Tendsto (f a) atBot (𝓝 0)} :=
    measurableSet_tendsto _ (fun q ↦ hf.eval)
  have h4 : MeasurableSet {a | ∀ t : ℚ, ⨅ r : Ioi t, f a r = f a t} := by
    rw [Set.ofPred_forall]
    refine MeasurableSet.iInter (fun q ↦ ?_)
    exact measurableSet_eq_fun (.iInf fun _ ↦ hf.eval) hf.eval
  suffices {a | IsRatStieltjesPoint f a}
      = ({a | Monotone (f a)} ∩ {a | Tendsto (f a) atTop (𝓝 1)} ∩ {a | Tendsto (f a) atBot (𝓝 0)}
        ∩ {a | ∀ t : ℚ, ⨅ r : Ioi t, f a r = f a t}) by
    rw [this]
    exact (((h1.inter h2).inter h3).inter h4)
  ext a
  simp only [mem_ofPred_eq, mem_inter_iff]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact ⟨⟨⟨h.mono, h.tendsto_atTop_one⟩, h.tendsto_atBot_zero⟩, h.iInf_rat_gt_eq⟩
  · exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

lemma IsRatStieltjesPoint.ite {f g : α → ℚ → ℝ} {a : α} (p : α → Prop) [DecidablePred p]
    (hf : p a → IsRatStieltjesPoint f a) (hg : ¬ p a → IsRatStieltjesPoint g a) :
    IsRatStieltjesPoint (fun a ↦ if p a then f a else g a) a where
  mono := by split_ifs with h; exacts [(hf h).mono, (hg h).mono]
  tendsto_atTop_one := by
    split_ifs with h; exacts [(hf h).tendsto_atTop_one, (hg h).tendsto_atTop_one]
  tendsto_atBot_zero := by
    split_ifs with h; exacts [(hf h).tendsto_atBot_zero, (hg h).tendsto_atBot_zero]
  iInf_rat_gt_eq := by split_ifs with h; exacts [(hf h).iInf_rat_gt_eq, (hg h).iInf_rat_gt_eq]

variable [SigmaAlgebra α]

/-- A function `f : α → ℚ → ℝ` is a (kernel) rational cumulative distribution function if it is
measurable in the first argument and if `f a` satisfies a list of properties for all `a : α`:
monotonicity between 0 at -∞ and 1 at +∞ and a form of continuity.

A function with these properties can be extended to a measurable function `α → StieltjesFunction ℝ`.
See `ProbabilityTheory.IsMeasurableRatCDF.stieltjesFunction`.
-/
structure IsMeasurableRatCDF (f : α → ℚ → ℝ) : Prop where
  isRatStieltjesPoint : ∀ a, IsRatStieltjesPoint f a
  measurable : Measurable f

lemma IsMeasurableRatCDF.nonneg {f : α → ℚ → ℝ} (hf : IsMeasurableRatCDF f) (a : α) (q : ℚ) :
    0 ≤ f a q :=
  Monotone.le_of_tendsto (hf.isRatStieltjesPoint a).mono
    (hf.isRatStieltjesPoint a).tendsto_atBot_zero q

lemma IsMeasurableRatCDF.le_one {f : α → ℚ → ℝ} (hf : IsMeasurableRatCDF f) (a : α) (q : ℚ) :
    f a q ≤ 1 :=
  Monotone.ge_of_tendsto (hf.isRatStieltjesPoint a).mono
    (hf.isRatStieltjesPoint a).tendsto_atTop_one q

lemma IsMeasurableRatCDF.tendsto_atTop_one {f : α → ℚ → ℝ} (hf : IsMeasurableRatCDF f) (a : α) :
    Tendsto (f a) atTop (𝓝 1) := (hf.isRatStieltjesPoint a).tendsto_atTop_one

lemma IsMeasurableRatCDF.tendsto_atBot_zero {f : α → ℚ → ℝ} (hf : IsMeasurableRatCDF f) (a : α) :
    Tendsto (f a) atBot (𝓝 0) := (hf.isRatStieltjesPoint a).tendsto_atBot_zero

lemma IsMeasurableRatCDF.iInf_rat_gt_eq {f : α → ℚ → ℝ} (hf : IsMeasurableRatCDF f) (a : α)
    (q : ℚ) :
    ⨅ r : Ioi q, f a r = f a q := (hf.isRatStieltjesPoint a).iInf_rat_gt_eq q

end IsMeasurableRatCDF

section IsMeasurableRatCDF.stieltjesFunction

/-- Auxiliary definition for `IsMeasurableRatCDF.stieltjesFunction`: turn `f : α → ℚ → ℝ` into
a function `α → ℝ → ℝ` by assigning to `f a x` the infimum of `f a q` over `q : ℚ` with `x < q`. -/
noncomputable irreducible_def IsMeasurableRatCDF.stieltjesFunctionAux (f : α → ℚ → ℝ) :
    α → ℝ → ℝ :=
  fun a x ↦ ⨅ q : { q' : ℚ // x < q' }, f a q

lemma IsMeasurableRatCDF.stieltjesFunctionAux_def' (f : α → ℚ → ℝ) (a : α) :
    IsMeasurableRatCDF.stieltjesFunctionAux f a
      = fun (t : ℝ) ↦ ⨅ r : { r' : ℚ // t < r' }, f a r := by
  ext t; exact IsMeasurableRatCDF.stieltjesFunctionAux_def f a t

lemma IsMeasurableRatCDF.stieltjesFunctionAux_unit_prod {f : α → ℚ → ℝ} (a : α) :
    IsMeasurableRatCDF.stieltjesFunctionAux (fun (p : Unit × α) ↦ f p.2) ((), a)
      = IsMeasurableRatCDF.stieltjesFunctionAux f a := by
  simp_rw [IsMeasurableRatCDF.stieltjesFunctionAux_def']

variable {f : α → ℚ → ℝ} [SigmaAlgebra α] (hf : IsMeasurableRatCDF f)
include hf

lemma IsMeasurableRatCDF.stieltjesFunctionAux_eq (a : α) (r : ℚ) :
    IsMeasurableRatCDF.stieltjesFunctionAux f a r = f a r := by
  rw [← hf.iInf_rat_gt_eq a r, IsMeasurableRatCDF.stieltjesFunctionAux]
  refine Equiv.iInf_congr ?_ ?_
  · exact
      { toFun := fun t ↦ ⟨t.1, mod_cast t.2⟩
        invFun := fun t ↦ ⟨t.1, mod_cast t.2⟩ }
  · intro t
    rfl

lemma IsMeasurableRatCDF.stieltjesFunctionAux_nonneg (a : α) (r : ℝ) :
    0 ≤ IsMeasurableRatCDF.stieltjesFunctionAux f a r := by
  have : Nonempty { r' : ℚ // r < ↑r' } := by
    obtain ⟨r, hrx⟩ := exists_rat_gt r
    exact ⟨⟨r, hrx⟩⟩
  rw [IsMeasurableRatCDF.stieltjesFunctionAux_def]
  exact le_ciInf fun r' ↦ hf.nonneg a _

lemma IsMeasurableRatCDF.monotone_stieltjesFunctionAux (a : α) :
    Monotone (IsMeasurableRatCDF.stieltjesFunctionAux f a) := by
  intro x y hxy
  have : Nonempty { r' : ℚ // y < ↑r' } := by
    obtain ⟨r, hrx⟩ := exists_rat_gt y
    exact ⟨⟨r, hrx⟩⟩
  simp_rw [IsMeasurableRatCDF.stieltjesFunctionAux_def]
  refine le_ciInf fun r ↦ (ciInf_le ?_ ?_).trans_eq ?_
  · refine ⟨0, fun z ↦ ?_⟩; rintro ⟨u, rfl⟩; exact hf.nonneg a _
  · exact ⟨r.1, hxy.trans_lt r.prop⟩
  · rfl

lemma IsMeasurableRatCDF.continuousWithinAt_stieltjesFunctionAux_Ici (a : α) (x : ℝ) :
    ContinuousWithinAt (IsMeasurableRatCDF.stieltjesFunctionAux f a) (Ici x) x := by
  rw [← continuousWithinAt_Ioi_iff_Ici]
  convert! Monotone.tendsto_nhdsGT (monotone_stieltjesFunctionAux hf a) x
  rw [sInf_image']
  have h' : ⨅ r : Ioi x, stieltjesFunctionAux f a r
      = ⨅ r : { r' : ℚ // x < r' }, stieltjesFunctionAux f a r := by
    refine Real.iInf_Ioi_eq_iInf_rat_gt x ?_ (monotone_stieltjesFunctionAux hf a)
    refine ⟨0, fun z ↦ ?_⟩
    rintro ⟨u, -, rfl⟩
    exact stieltjesFunctionAux_nonneg hf a u
  have h'' :
    ⨅ r : { r' : ℚ // x < r' }, stieltjesFunctionAux f a r =
      ⨅ r : { r' : ℚ // x < r' }, f a r := by
    congr with r
    exact stieltjesFunctionAux_eq hf a r
  rw [h', h'', ContinuousWithinAt]
  congr!
  rw [stieltjesFunctionAux_def]

/-- Extend a function `f : α → ℚ → ℝ` with property `IsMeasurableRatCDF` from `ℚ` to `ℝ`,
to a function `α → StieltjesFunction ℝ`. -/
noncomputable def IsMeasurableRatCDF.stieltjesFunction (a : α) : StieltjesFunction ℝ where
  toFun := stieltjesFunctionAux f a
  mono' := monotone_stieltjesFunctionAux hf a
  right_continuous' x := continuousWithinAt_stieltjesFunctionAux_Ici hf a x

lemma IsMeasurableRatCDF.stieltjesFunction_eq (a : α) (r : ℚ) : hf.stieltjesFunction a r = f a r :=
  stieltjesFunctionAux_eq hf a r

lemma IsMeasurableRatCDF.stieltjesFunction_nonneg (a : α) (r : ℝ) : 0 ≤ hf.stieltjesFunction a r :=
  stieltjesFunctionAux_nonneg hf a r

lemma IsMeasurableRatCDF.stieltjesFunction_le_one (a : α) (x : ℝ) :
    hf.stieltjesFunction a x ≤ 1 := by
  obtain ⟨r, hrx⟩ := exists_rat_gt x
  rw [← StieltjesFunction.iInf_rat_gt_eq]
  simp_rw [IsMeasurableRatCDF.stieltjesFunction_eq]
  refine ciInf_le_of_le ?_ ?_ (hf.le_one _ _)
  · refine ⟨0, fun z ↦ ?_⟩; rintro ⟨u, rfl⟩; exact hf.nonneg a _
  · exact ⟨r, hrx⟩

lemma IsMeasurableRatCDF.tendsto_stieltjesFunction_atBot (a : α) :
    Tendsto (hf.stieltjesFunction a) atBot (𝓝 0) := by
  have h_exists : ∀ x : ℝ, ∃ q : ℚ, x < q ∧ ↑q < x + 1 := fun x ↦ exists_rat_btwn (lt_add_one x)
  let qs : ℝ → ℚ := fun x ↦ (h_exists x).choose
  have hqs_tendsto : Tendsto qs atBot atBot := by
    rw [tendsto_atBot_atBot]
    refine fun q ↦ ⟨q - 1, fun y hy ↦ ?_⟩
    have h_le : ↑(qs y) ≤ (q : ℝ) - 1 + 1 :=
      (h_exists y).choose_spec.2.le.trans (add_le_add hy le_rfl)
    rw [sub_add_cancel] at h_le
    exact mod_cast h_le
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    ((hf.tendsto_atBot_zero a).comp hqs_tendsto) (stieltjesFunction_nonneg hf a) fun x ↦ ?_
  rw [Function.comp_apply, ← stieltjesFunction_eq hf]
  exact (hf.stieltjesFunction a).mono (h_exists x).choose_spec.1.le

lemma IsMeasurableRatCDF.tendsto_stieltjesFunction_atTop (a : α) :
    Tendsto (hf.stieltjesFunction a) atTop (𝓝 1) := by
  have h_exists : ∀ x : ℝ, ∃ q : ℚ, x - 1 < q ∧ ↑q < x := fun x ↦ exists_rat_btwn (sub_one_lt x)
  let qs : ℝ → ℚ := fun x ↦ (h_exists x).choose
  have hqs_tendsto : Tendsto qs atTop atTop := by
    rw [tendsto_atTop_atTop]
    refine fun q ↦ ⟨q + 1, fun y hy ↦ ?_⟩
    have h_le : y - 1 ≤ qs y := (h_exists y).choose_spec.1.le
    rw [sub_le_iff_le_add] at h_le
    exact_mod_cast le_of_add_le_add_right (hy.trans h_le)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le ((hf.tendsto_atTop_one a).comp hqs_tendsto)
      tendsto_const_nhds ?_ (stieltjesFunction_le_one hf a)
  intro x
  rw [Function.comp_apply, ← stieltjesFunction_eq hf]
  exact (hf.stieltjesFunction a).mono (le_of_lt (h_exists x).choose_spec.2)

lemma IsMeasurableRatCDF.measurable_stieltjesFunction (x : ℝ) :
    Measurable fun a ↦ hf.stieltjesFunction a x := by
  have : (fun a ↦ hf.stieltjesFunction a x) = fun a ↦ ⨅ r : { r' : ℚ // x < r' }, f a ↑r := by
    ext1 a
    rw [← StieltjesFunction.iInf_rat_gt_eq]
    congr with q
    rw [stieltjesFunction_eq]
  rw [this]
  exact .iInf (fun q ↦ hf.measurable.eval)

lemma IsMeasurableRatCDF.stronglyMeasurable_stieltjesFunction (x : ℝ) :
    StronglyMeasurable fun a ↦ hf.stieltjesFunction a x :=
  (measurable_stieltjesFunction hf x).stronglyMeasurable

section Measure

lemma IsMeasurableRatCDF.measure_stieltjesFunction_Iic (a : α) (x : ℝ) :
    (hf.stieltjesFunction a).measure (Iic x) = ENNReal.ofReal (hf.stieltjesFunction a x) := by
  rw [← sub_zero (hf.stieltjesFunction a x)]
  exact (hf.stieltjesFunction a).measure_Iic (tendsto_stieltjesFunction_atBot hf a) _

lemma IsMeasurableRatCDF.measure_stieltjesFunction_univ (a : α) :
    (hf.stieltjesFunction a).measure univ = 1 := by
  rw [← ENNReal.ofReal_one, ← sub_zero (1 : ℝ)]
  exact StieltjesFunction.measure_univ _ (tendsto_stieltjesFunction_atBot hf a)
    (tendsto_stieltjesFunction_atTop hf a)

instance IsMeasurableRatCDF.instIsProbabilityMeasure_stieltjesFunction (a : α) :
    IsProbabilityMeasure (hf.stieltjesFunction a).measure :=
  ⟨measure_stieltjesFunction_univ hf a⟩

lemma IsMeasurableRatCDF.measurable_measure_stieltjesFunction :
    Measurable fun a ↦ (hf.stieltjesFunction a).measure := by
  apply_rules [StieltjesFunction.measurable_measure, measurable_stieltjesFunction,
    tendsto_stieltjesFunction_atBot, tendsto_stieltjesFunction_atTop]

end Measure

end IsMeasurableRatCDF.stieltjesFunction

end ProbabilityTheory
