/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.CompleteOfCompleteLp
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2

/-! # Conditional expectation in L1

This file contains two more steps of the construction of the conditional expectation, which is
completed in `Mathlib/MeasureTheory/Function/ConditionalExpectation/Basic.lean`. See that file for a
description of the full process.

The conditional expectation of an `L²` function is defined in
`MeasureTheory.Function.ConditionalExpectation.CondexpL2`. In this file, we perform two steps.
* Show that the conditional expectation of the indicator of a measurable set with finite measure
  is integrable and define, for each such set, a continuous linear map `condExpInd` from `E` to
  `α →₁[μ] E`, which sends `x ∈ E` to the conditional expectation of the indicator of the set with
  value `x`.
* Extend these maps to `condExpL1CLM : (α →₁[μ] E) →L[ℝ] (α →₁[μ] E)`. This is done using the same
  construction as the Bochner integral (see the file `MeasureTheory/Integral/SetToL1`). That
  construction takes a set function defined on every set, so `dominatedFinMeasAdditive_condExpInd`
  extends `condExpInd` by `0` to the other sets at its single construction site; the result does
  not depend on the extension.

## Main definitions

* `condExpInd`: conditional expectation of the indicator of a measurable set of finite measure, as
  a continuous linear map from the values to `L1`.
* `condExpL1CLM`: conditional expectation as a continuous linear map from `L1` to itself.

-/

@[expose] public section


noncomputable section

open TopologicalSpace MeasureTheory.Lp Filter ContinuousLinearMap

open scoped NNReal ENNReal Topology MeasureTheory

namespace MeasureTheory

variable {α F F' G G' 𝕜 : Type*} [RCLike 𝕜]
  -- 𝕜 for ℝ or ℂ
  -- F for a Lp submodule
  [NormedAddCommGroup F]
  [NormedSpace 𝕜 F]
  -- F' for integrals on a Lp submodule
  [NormedAddCommGroup F']
  [NormedSpace 𝕜 F'] [NormedSpace ℝ F']
  -- G for a Lp add_subgroup
  [NormedAddCommGroup G]
  -- G' for integrals on a Lp add_subgroup
  [NormedAddCommGroup G']
  [NormedSpace ℝ G'] [CompleteSpace G']

section CondexpInd

/-! ## Conditional expectation of an indicator as a continuous linear map.

The goal of this section is to build `condExpInd G hm hs hμs : G →L[ℝ] α →₁[μ] G` for a
measurable set `s` of finite measure, which takes `x : G` to the conditional expectation of the
indicator of the set `s` with value `x`, seen as an element of `α →₁[μ] G`.
-/


variable {m m0 : SigmaAlgebra α} {μ : Measure α} {s t : Set α} [NormedSpace ℝ G]

section CondexpIndL1Fin


/-- Conditional expectation of the indicator of a measurable set with finite measure,
as a function in L1. -/
def condExpIndL1Fin (hm : m ≤ m0) [SigmaFinite (μ.trim hm)] (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (x : G) : α →₁[μ] G :=
  (integrable_condExpIndSMul hm hs hμs x).toL1 _

theorem condExpIndL1Fin_ae_eq_condExpIndSMul (hm : m ≤ m0) [SigmaFinite (μ.trim hm)]
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : G) :
    condExpIndL1Fin hm hs hμs x =ᵐ[μ] condExpIndSMul hm hs hμs x :=
  (integrable_condExpIndSMul hm hs hμs x).coeFn_toL1

variable {hm : m ≤ m0} [SigmaFinite (μ.trim hm)]

-- Porting note: this lemma fills the hole in `refine' (MemLp.coeFn_toLp _) ...`
-- which is not automatically filled in Lean 4
private theorem q {hs : MeasurableSet s} {hμs : μ s ≠ ∞} {x : G} :
    MemLp (condExpIndSMul hm hs hμs x) 1 μ := by
  rw [memLp_one_iff_integrable]; apply integrable_condExpIndSMul

theorem condExpIndL1Fin_add (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x y : G) :
    condExpIndL1Fin hm hs hμs (x + y) =
    condExpIndL1Fin hm hs hμs x + condExpIndL1Fin hm hs hμs y := by
  ext1
  unfold condExpIndL1Fin Integrable.toL1
  grw [Lp.coeFn_add, MemLp.coeFn_toLp, MemLp.coeFn_toLp, MemLp.coeFn_toLp, condExpIndSMul_add,
    Lp.coeFn_add]

theorem condExpIndL1Fin_smul (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : ℝ) (x : G) :
    condExpIndL1Fin hm hs hμs (c • x) = c • condExpIndL1Fin hm hs hμs x := by
  ext1
  grw [Lp.coeFn_smul, condExpIndL1Fin_ae_eq_condExpIndSMul, condExpIndL1Fin_ae_eq_condExpIndSMul,
    condExpIndSMul_smul, Lp.coeFn_smul]

theorem condExpIndL1Fin_smul' [NormedSpace ℝ F] [SMulCommClass ℝ 𝕜 F] (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) (c : 𝕜) (x : F) :
    condExpIndL1Fin hm hs hμs (c • x) = c • condExpIndL1Fin hm hs hμs x := by
  ext1
  grw [Lp.coeFn_smul, condExpIndL1Fin_ae_eq_condExpIndSMul, condExpIndL1Fin_ae_eq_condExpIndSMul,
    condExpIndSMul_smul, Lp.coeFn_smul]

theorem norm_condExpIndL1Fin_le (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : G) :
    ‖condExpIndL1Fin hm hs hμs x‖ ≤ μ.real s * ‖x‖ := by
  rw [L1.norm_eq_integral_norm, ← ENNReal.toReal_ofReal (norm_nonneg x), measureReal_def,
    ← ENNReal.toReal_mul,
    ← ENNReal.ofReal_le_iff_le_toReal (ENNReal.mul_ne_top hμs ENNReal.ofReal_ne_top),
    ofReal_integral_norm_eq_lintegral_enorm]
  swap; · rw [← memLp_one_iff_integrable]; exact Lp.memLp _
  have h_eq :
    ∫⁻ a, ‖condExpIndL1Fin hm hs hμs x a‖ₑ ∂μ = ∫⁻ a, ‖condExpIndSMul hm hs hμs x a‖ₑ ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards [condExpIndL1Fin_ae_eq_condExpIndSMul hm hs hμs x] with z hz
    rw [hz]
  rw [h_eq, ofReal_norm]
  exact lintegral_nnnorm_condExpIndSMul_le hm hs hμs x

theorem condExpIndL1Fin_disjoint_union (hs : MeasurableSet s) (ht : MeasurableSet t) (hμs : μ s ≠ ∞)
    (hμt : μ t ≠ ∞) (hst : Disjoint s t) (x : G) :
    condExpIndL1Fin hm (hs.union ht) ((measure_union_le s t).trans_lt
      (lt_top_iff_ne_top.mpr (ENNReal.add_ne_top.mpr ⟨hμs, hμt⟩))).ne x =
    condExpIndL1Fin hm hs hμs x + condExpIndL1Fin hm ht hμt x := by
  ext1
  grw [Lp.coeFn_add, condExpIndL1Fin_ae_eq_condExpIndSMul, condExpIndL1Fin_ae_eq_condExpIndSMul,
    condExpIndL1Fin_ae_eq_condExpIndSMul]
  rw [condExpIndSMul]
  rw [indicatorConstLp_disjoint_union hs ht hμs hμt hst (1 : ℝ)]
  rw [map_add]
  push_cast
  rw [map_add]
  grw [Lp.coeFn_add]
  rfl

theorem continuous_condExpIndL1Fin (hs : MeasurableSet s) (hμs : μ s ≠ ∞) :
    Continuous fun x : G => condExpIndL1Fin hm hs hμs x :=
  continuous_of_linear_of_bound (condExpIndL1Fin_add hs hμs) (condExpIndL1Fin_smul hs hμs)
    (norm_condExpIndL1Fin_le hs hμs)

end CondexpIndL1Fin

variable (G)

/-- Conditional expectation of the indicator of a measurable set of finite measure, as a
continuous linear map from `G` to L1: it sends `x` to the conditional expectation of the indicator
of the set with value `x`. -/
def condExpInd {m m0 : SigmaAlgebra α} (hm : m ≤ m0) {μ : Measure α} [SigmaFinite (μ.trim hm)]
    {s : Set α} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) : G →L[ℝ] α →₁[μ] G where
  toFun := condExpIndL1Fin hm hs hμs
  map_add' := condExpIndL1Fin_add hs hμs
  map_smul' := condExpIndL1Fin_smul hs hμs
  cont := continuous_condExpIndL1Fin hs hμs

variable {G}

theorem condExpInd_ae_eq_condExpIndSMul (hm : m ≤ m0) [SigmaFinite (μ.trim hm)]
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : G) :
    condExpInd G hm hs hμs x =ᵐ[μ] condExpIndSMul hm hs hμs x :=
  condExpIndL1Fin_ae_eq_condExpIndSMul hm hs hμs x

variable {hm : m ≤ m0} [SigmaFinite (μ.trim hm)]

theorem aestronglyMeasurable_condExpInd (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : G) :
    AEStronglyMeasurable[m] (condExpInd G hm hs hμs x) μ :=
  (aestronglyMeasurable_condExpIndSMul hm hs hμs x).congr
    (condExpInd_ae_eq_condExpIndSMul hm hs hμs x).symm

@[simp]
theorem condExpInd_empty :
    condExpInd G hm MeasurableSet.empty (by simp : μ ∅ ≠ ∞) = (0 : G →L[ℝ] α →₁[μ] G) := by
  ext x
  grw [condExpInd_ae_eq_condExpIndSMul hm MeasurableSet.empty (by simp), condExpIndSMul_empty,
    zero_apply, Lp.coeFn_zero, Lp.coeFn_zero]

theorem condExpInd_smul' [NormedSpace ℝ F] [SMulCommClass ℝ 𝕜 F] (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞) (c : 𝕜) (x : F) :
    condExpInd F hm hs hμs (c • x) = c • condExpInd F hm hs hμs x :=
  condExpIndL1Fin_smul' hs hμs c x

theorem norm_condExpInd_apply_le (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : G) :
    ‖condExpInd G hm hs hμs x‖ ≤ μ.real s * ‖x‖ :=
  norm_condExpIndL1Fin_le hs hμs x

theorem norm_condExpInd_le (hs : MeasurableSet s) (hμs : μ s ≠ ∞) :
    ‖(condExpInd G hm hs hμs : G →L[ℝ] α →₁[μ] G)‖ ≤ μ.real s :=
  ContinuousLinearMap.opNorm_le_bound _ ENNReal.toReal_nonneg (norm_condExpInd_apply_le hs hμs)

theorem condExpInd_disjoint_union_apply (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hμs : μ s ≠ ∞) (hμt : μ t ≠ ∞) (hst : Disjoint s t) (x : G) :
    condExpInd G hm (hs.union ht) (measure_union_ne_top hμs hμt) x =
      condExpInd G hm hs hμs x + condExpInd G hm ht hμt x :=
  condExpIndL1Fin_disjoint_union hs ht hμs hμt hst x

theorem condExpInd_disjoint_union (hs : MeasurableSet s) (ht : MeasurableSet t) (hμs : μ s ≠ ∞)
    (hμt : μ t ≠ ∞) (hst : Disjoint s t) :
    (condExpInd G hm (hs.union ht) (measure_union_ne_top hμs hμt) : G →L[ℝ] α →₁[μ] G) =
      condExpInd G hm hs hμs + condExpInd G hm ht hμt := by
  ext1 x; push_cast; exact condExpInd_disjoint_union_apply hs ht hμs hμt hst x

variable (G) in
open scoped Classical in
/-- The conditional expectations of the indicators of measurable sets of finite measure, extended
by `0` to the other sets, form a dominated finitely measure-additive set function, which
`L1.setToL1` extends to `condExpL1CLM`. That extension uses only the values on measurable sets of
finite measure (`L1.setToL1_congr_left'`), so the value `0` on the other sets does not affect it. -/
theorem dominatedFinMeasAdditive_condExpInd (hm : m ≤ m0) (μ : Measure α)
    [SigmaFinite (μ.trim hm)] :
    DominatedFinMeasAdditive μ (fun s ↦ if h : MeasurableSet s ∧ μ s ≠ ∞ then
      condExpInd G hm h.1 h.2 else 0 : Set α → G →L[ℝ] α →₁[μ] G) 1 := by
  refine ⟨fun s t hs ht hμs hμt hst ↦ ?_, fun s hs hμs ↦ ?_⟩
  · simp only [dite_eq_left (show MeasurableSet (s ∪ t) ∧ μ (s ∪ t) ≠ ∞ from
      ⟨hs.union ht, measure_union_ne_top hμs hμt⟩),
      dite_eq_left (show MeasurableSet s ∧ μ s ≠ ∞ from ⟨hs, hμs⟩),
      dite_eq_left (show MeasurableSet t ∧ μ t ≠ ∞ from ⟨ht, hμt⟩)]
    exact condExpInd_disjoint_union hs ht hμs hμt hst
  · simp only [dite_eq_left (show MeasurableSet s ∧ μ s ≠ ∞ from ⟨hs, hμs.ne⟩), one_mul]
    exact norm_condExpInd_le hs hμs.ne

theorem setIntegral_condExpInd (hs : s ∈ m) (ht : MeasurableSet t) (hμs : μ s ≠ ∞)
    (hμt : μ t ≠ ∞) (x : G') : ∫ a in s, condExpInd G' hm ht hμt x a ∂μ = μ.real (t ∩ s) • x :=
  calc
    ∫ a in s, condExpInd G' hm ht hμt x a ∂μ = ∫ a in s, condExpIndSMul hm ht hμt x a ∂μ :=
      setIntegral_congr_ae (hm hs)
        ((condExpInd_ae_eq_condExpIndSMul hm ht hμt x).mono fun _ hx _ => hx)
    _ = μ.real (t ∩ s) • x := setIntegral_condExpIndSMul hs ht hμs hμt x

theorem condExpInd_of_measurable (hs : s ∈ m) (hμs : μ s ≠ ∞) (c : G) :
    condExpInd G hm (measurableSet_iff_mem.mpr (hm hs)) hμs c =
      indicatorConstLp 1 (measurableSet_iff_mem.mpr (hm hs)) hμs c := by
  ext1
  grw [indicatorConstLp_coeFn, condExpInd_ae_eq_condExpIndSMul hm _ hμs,
    condExpIndSMul_ae_eq_smul]
  rw [condExpL2_indicator_of_measurable hm hs hμs (1 : ℝ)]
  filter_upwards [@indicatorConstLp_coeFn α _ _ 2 μ _ s (measurableSet_iff_mem.mpr (hm hs)) hμs
    (1 : ℝ)] with x hx
  rw [hx]
  by_cases hx_mem : x ∈ s <;> simp [hx_mem]

theorem condExpInd_nonneg {E} [NormedAddCommGroup E] [PartialOrder E] [NormedSpace ℝ E]
    [IsOrderedModule ℝ E] (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : E) (hx : 0 ≤ x) :
    0 ≤ condExpInd E hm hs hμs x := by
  rw [← coeFn_le]
  refine EventuallyLE.trans_eq ?_ (condExpInd_ae_eq_condExpIndSMul hm hs hμs x).symm
  exact (coeFn_zero E 1 μ).trans_le (condExpIndSMul_nonneg hs hμs x hx)

end CondexpInd

section CondexpL1


variable {m m0 : SigmaAlgebra α} {μ : Measure α} {hm : m ≤ m0} [SigmaFinite (μ.trim hm)]
  {f g : α → F'} {s : Set α}

section CondExpL1CLM

variable (F')

/-- Conditional expectation of a function as a linear map from `α →₁[μ] F'` to itself. -/
def condExpL1CLM (hm : m ≤ m0) (μ : Measure α) [CompleteSpace ↑(Lp F' 1 μ)]
    [SigmaFinite (μ.trim hm)] :
    (α →₁[μ] F') →L[ℝ] α →₁[μ] F' :=
  L1.setToL1 (dominatedFinMeasAdditive_condExpInd F' hm μ)

variable {F'}
variable [CompleteSpace F']

theorem condExpL1CLM_smul (c : 𝕜) (f : α →₁[μ] F') :
    condExpL1CLM F' hm μ (c • f) = c • condExpL1CLM F' hm μ f := by
  refine L1.setToL1_smul (dominatedFinMeasAdditive_condExpInd F' hm μ) (fun c s x ↦ ?_) c f
  split_ifs with h
  · exact condExpInd_smul' h.1 h.2 c x
  · simp

theorem condExpL1CLM_indicatorConstLp (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : F') :
    (condExpL1CLM F' hm μ) (indicatorConstLp 1 hs hμs x) = condExpInd F' hm hs hμs x := by
  rw [condExpL1CLM, L1.setToL1_indicatorConstLp (dominatedFinMeasAdditive_condExpInd F' hm μ) hs
    hμs x, dite_eq_left (show MeasurableSet s ∧ μ s ≠ ∞ from ⟨hs, hμs⟩)]

theorem condExpL1CLM_indicatorConst (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (x : F') :
    (condExpL1CLM F' hm μ) ↑(simpleFunc.indicatorConst 1 hs hμs x) =
      condExpInd F' hm hs hμs x := by
  rw [Lp.simpleFunc.coe_indicatorConst]; exact condExpL1CLM_indicatorConstLp hs hμs x

/-- Auxiliary lemma used in the proof of `setIntegral_condExpL1CLM`. -/
theorem setIntegral_condExpL1CLM_of_measure_ne_top (f : α →₁[μ] F') (hs : s ∈ m)
    (hμs : μ s ≠ ∞) : ∫ x in s, condExpL1CLM F' hm μ f x ∂μ = ∫ x in s, f x ∂μ := by
  refine @Lp.induction _ _ _ _ _ _ _ ENNReal.one_ne_top
    (fun f : α →₁[μ] F' => ∫ x in s, condExpL1CLM F' hm μ f x ∂μ = ∫ x in s, f x ∂μ) ?_ ?_
    (isClosed_eq ?_ ?_) f
  · intro x t ht hμt
    simp_rw [condExpL1CLM_indicatorConst ht hμt.ne x]
    rw [Lp.simpleFunc.coe_indicatorConst, setIntegral_indicatorConstLp (hm hs)]
    exact setIntegral_condExpInd hs ht hμs hμt.ne x
  · intro f g hf_Lp hg_Lp _ hf hg
    simp_rw [(condExpL1CLM F' hm μ).map_add]
    rw [setIntegral_congr_ae (hm hs) ((Lp.coeFn_add (condExpL1CLM F' hm μ (hf_Lp.toLp f))
      (condExpL1CLM F' hm μ (hg_Lp.toLp g))).mono fun x hx _ => hx)]
    rw [setIntegral_congr_ae (hm hs)
      ((Lp.coeFn_add (hf_Lp.toLp f) (hg_Lp.toLp g)).mono fun x hx _ => hx)]
    simp_rw [Pi.add_apply]
    rw [integral_add (L1.integrable_coeFn _).integrableOn (L1.integrable_coeFn _).integrableOn,
      integral_add (L1.integrable_coeFn _).integrableOn (L1.integrable_coeFn _).integrableOn, hf,
      hg]
  · exact (continuous_setIntegral s).comp (condExpL1CLM F' hm μ).continuous
  · exact continuous_setIntegral s

/-- The integral of the conditional expectation `condExpL1CLM` over an `m`-measurable set is equal
to the integral of `f` on that set. See also `MeasureTheory.IsCondExp.setIntegral_eq`, the defining
property of a conditional expectation. -/
theorem setIntegral_condExpL1CLM (f : α →₁[μ] F') (hs : s ∈ m) :
    ∫ x in s, condExpL1CLM F' hm μ f x ∂μ = ∫ x in s, f x ∂μ := by
  let S := spanningSets (μ.trim hm)
  have hS_meas : ∀ i, S i ∈ m := measurableSet_spanningSets (μ.trim hm)
  have hS_meas0 : ∀ i, MeasurableSet (S i) := fun i => hm (hS_meas i)
  have hs_eq : s = ⋃ i, S i ∩ s := by
    simp_rw [Set.inter_comm]
    rw [← Set.inter_iUnion, iUnion_spanningSets (μ.trim hm), Set.inter_univ]
  have hS_finite : ∀ i, μ (S i ∩ s) < ∞ := by
    refine fun i => (measure_mono Set.inter_subset_left).trans_lt ?_
    have hS_finite_trim := measure_spanningSets_lt_top (μ.trim hm) i
    rwa [trim_measurableSet_eq hm (hS_meas i)] at hS_finite_trim
  have h_mono : Monotone fun i => S i ∩ s := by
    intro i j hij x
    simp_rw [Set.mem_inter_iff]
    exact fun h => ⟨monotone_spanningSets (μ.trim hm) hij h.1, h.2⟩
  have h_eq_forall :
    (fun i => ∫ x in S i ∩ s, condExpL1CLM F' hm μ f x ∂μ) = fun i => ∫ x in S i ∩ s, f x ∂μ :=
    funext fun i =>
      setIntegral_condExpL1CLM_of_measure_ne_top f (@MeasurableSet.inter α m _ _ (hS_meas i) hs)
        (hS_finite i).ne
  have h_right : Tendsto (fun i => ∫ x in S i ∩ s, f x ∂μ) atTop (𝓝 (∫ x in s, f x ∂μ)) := by
    have h :=
      tendsto_setIntegral_of_monotone (fun i => (hS_meas0 i).inter (hm hs)) h_mono
        (L1.integrable_coeFn f).integrableOn
    rwa [← hs_eq] at h
  have h_left : Tendsto (fun i => ∫ x in S i ∩ s, condExpL1CLM F' hm μ f x ∂μ) atTop
      (𝓝 (∫ x in s, condExpL1CLM F' hm μ f x ∂μ)) := by
    have h := tendsto_setIntegral_of_monotone (fun i => (hS_meas0 i).inter (hm hs)) h_mono
      (L1.integrable_coeFn (condExpL1CLM F' hm μ f)).integrableOn
    rwa [← hs_eq] at h
  rw [h_eq_forall] at h_left
  exact tendsto_nhds_unique h_left h_right

theorem aestronglyMeasurable_condExpL1CLM (f : α →₁[μ] F') :
    AEStronglyMeasurable[m] (condExpL1CLM F' hm μ f) μ := by
  refine @Lp.induction _ _ _ _ _ _ _ ENNReal.one_ne_top
    (fun f : α →₁[μ] F' => AEStronglyMeasurable[m] (condExpL1CLM F' hm μ f) μ) ?_ ?_ ?_ f
  · intro c s hs hμs
    rw [condExpL1CLM_indicatorConst hs hμs.ne c]
    exact aestronglyMeasurable_condExpInd hs hμs.ne c
  · intro f g hf hg _ hfm hgm
    rw [(condExpL1CLM F' hm μ).map_add]
    exact (hfm.add hgm).congr (coeFn_add ..).symm
  · have : {f : Lp F' 1 μ | AEStronglyMeasurable[m] (condExpL1CLM F' hm μ f) μ} =
        condExpL1CLM F' hm μ ⁻¹' {f | AEStronglyMeasurable[m] f μ} := rfl
    rw [this]
    refine IsClosed.preimage (condExpL1CLM F' hm μ).continuous ?_
    exact isClosed_aestronglyMeasurable hm

theorem condExpL1CLM_lpMeas (f : lpMeas F' ℝ m 1 μ) :
    condExpL1CLM F' hm μ (f : α →₁[μ] F') = ↑f := by
  let g := lpMeasToLpTrimLie F' ℝ 1 μ hm f
  have hfg : f = (lpMeasToLpTrimLie F' ℝ 1 μ hm).symm g := by
    simp only [g, LinearIsometryEquiv.symm_apply_apply]
  rw [hfg]
  refine @Lp.induction α F' m _ 1 (μ.trim hm) _ ENNReal.coe_ne_top (fun g : α →₁[μ.trim hm] F' =>
    condExpL1CLM F' hm μ ((lpMeasToLpTrimLie F' ℝ 1 μ hm).symm g : α →₁[μ] F') =
    ↑((lpMeasToLpTrimLie F' ℝ 1 μ hm).symm g)) ?_ ?_ ?_ g
  · intro c s hs hμs
    rw [@Lp.simpleFunc.coe_indicatorConst _ _ m, lpMeasToLpTrimLie_symm_indicator hs hμs.ne c,
      condExpL1CLM_indicatorConstLp]
    exact condExpInd_of_measurable hs ((le_trim hm).trans_lt hμs).ne c
  · intro f g hf hg _ hf_eq hg_eq
    rw [LinearIsometryEquiv.map_add]
    push_cast
    rw [map_add, hf_eq, hg_eq]
  · refine isClosed_eq ?_ ?_
    · refine (condExpL1CLM F' hm μ).continuous.comp (continuous_induced_dom.comp ?_)
      exact LinearIsometryEquiv.continuous _
    · refine continuous_induced_dom.comp ?_
      exact LinearIsometryEquiv.continuous _

theorem condExpL1CLM_of_aestronglyMeasurable' (f : α →₁[μ] F') (hfm : AEStronglyMeasurable[m] f μ) :
    condExpL1CLM F' hm μ f = f :=
  condExpL1CLM_lpMeas (⟨f, hfm⟩ : lpMeas F' ℝ m 1 μ)

theorem condExpL1CLM_mono {E} [NormedAddCommGroup E] [PartialOrder E] [ClosedIciTopology E]
    [IsOrderedAddMonoid E] [NormedSpace ℝ E] [IsOrderedModule ℝ E] [CompleteSpace E]
    {f g : α →₁[μ] E} (hfg : f ≤ g) : condExpL1CLM E hm μ f ≤ condExpL1CLM E hm μ g :=
  L1.setToL1_mono (dominatedFinMeasAdditive_condExpInd E hm μ) (fun s hs hμs x hx ↦ by
    simp only [dite_eq_left (show MeasurableSet s ∧ μ s ≠ ∞ from ⟨hs, hμs.ne⟩)]
    exact condExpInd_nonneg hs hμs.ne x hx) hfg

end CondExpL1CLM

end CondexpL1

end MeasureTheory
