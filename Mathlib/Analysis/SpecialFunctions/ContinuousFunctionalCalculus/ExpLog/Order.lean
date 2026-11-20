/-
Copyright (c) 2025 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.Analysis.SpecialFunctions.Log.RpowTendsto
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Convex.FunctionTopology

/-!
# Order properties of the operator logarithm

This file shows that the logarithm is operator monotone and concave, i.e. that `CFC.log` is
monotone and concave on the strictly positive elements of a unital C⋆-algebra.

## Main declarations

* `CFC.log_monotoneOn`: the logarithm is operator monotone
* `CFC.concaveOn_log`: the logarithm is operator concave

## TODO

* Show that `x => x * log x` is operator convex
-/

public section

open scoped Topology
open Filter Set

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma CFC.tendsto_cfc_rpow_sub_one_log {a : A} (ha : IsStrictlyPositive a := by cfc_tac) :
    Tendsto (fun p : Ioi (0 : ℝ) ↦ cfc
      (fun x : ℝ ↦ Checked.inv (p : ℝ) p.property.ne'.isUnit * (x ^ (p : ℝ) - 1)) a)
      (comap Subtype.val (𝓝 0)) (𝓝 (CFC.log a)) := by
  refine tendsto_cfc_fun ?tendsto ?cont
  case cont =>
    exact .of_forall fun p ↦
      (continuous_const.mul ((Real.continuous_rpow_const p.property.le).sub
        continuous_const)).continuousOn
  case tendsto =>
    have hmain := Real.tendstoLocallyUniformlyOn_rpow_sub_one_log
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_Ioi] at hmain
    exact hmain (spectrum ℝ a) (fun _ hx ↦ ha.spectrum_pos hx) (spectrum.isCompact _)

private lemma CFC.cfc_rpow_sub_one_eq (p : Ioi (0 : ℝ)) {a : A} (ha : IsStrictlyPositive a) :
    cfc (fun x : ℝ ↦ Checked.inv (p : ℝ) p.property.ne'.isUnit * (x ^ (p : ℝ) - 1)) a =
      Checked.inv (p : ℝ) p.property.ne'.isUnit • (a ^ (p : ℝ) - (1 : A)) := by
  let r : ℝ := Checked.inv (p : ℝ) p.property.ne'.isUnit
  have hf := (Real.continuous_rpow_const p.property.le).continuousOn (s := spectrum ℝ a)
  have hdiff : cfc (fun x : ℝ ↦ x ^ (p : ℝ) - 1) a = a ^ (p : ℝ) - (1 : A) := by
    calc
      _ = cfc (fun x : ℝ ↦ x ^ (p : ℝ)) a - cfc (fun _ : ℝ ↦ 1) a :=
        cfc_sub _ _ a hf continuousOn_const
      _ = _ := by rw [rpow_eq_cfc_real ha.nonneg, cfc_const_one (R := ℝ) a ha.isSelfAdjoint]
  calc
    _ = r • cfc (fun x : ℝ ↦ x ^ (p : ℝ) - 1) a :=
      cfc_smul r _ a (hf.sub continuousOn_const)
    _ = _ := congrArg (r • ·) hdiff

private lemma CFC.tendsto_rpow_sub_one_log {a : A} (ha : IsStrictlyPositive a) :
    Tendsto (fun p : Ioi (0 : ℝ) ↦
      Checked.inv (p : ℝ) p.property.ne'.isUnit • (a ^ (p : ℝ) - (1 : A)))
      (comap Subtype.val (𝓝 0)) (𝓝 (CFC.log a)) :=
  (tendsto_cfc_rpow_sub_one_log ha).congr fun p ↦ cfc_rpow_sub_one_eq p ha

private lemma neBot_comap_positive_nhds_zero :
    NeBot (comap (Subtype.val : Ioi (0 : ℝ) → ℝ) (𝓝 0)) := by
  have h : NeBot (comap (Subtype.val : Ioi (0 : ℝ) → ℝ) (𝓝[>] 0)) := by
    apply NeBot.comap_of_range_mem (by infer_instance)
    rw [Subtype.range_coe]
    exact self_mem_nhdsWithin
  exact h.mono (comap_mono nhdsWithin_le_nhds)

/-- `log` is operator monotone. -/
lemma CFC.log_monotoneOn : MonotoneOn log {a : A | IsStrictlyPositive a} := by
  intro a ha b hb hab
  let := neBot_comap_positive_nhds_zero
  refine le_of_tendsto_of_tendsto (tendsto_rpow_sub_one_log ha) (tendsto_rpow_sub_one_log hb) ?_
  filter_upwards [tendsto_comap.eventually (eventually_lt_nhds (zero_lt_one : (0 : ℝ) < 1))]
    with p hp
  exact smul_le_smul_of_nonneg_left
    (sub_le_sub_right (CFC.monotone_rpow ⟨p.property.le, hp.le⟩ hab) 1)
    (_root_.inv_nonneg.mpr p.property.le)

@[gcongr]
lemma CFC.log_le_log {a b : A} (hab : a ≤ b) (ha : IsStrictlyPositive a := by cfc_tac) :
    log a ≤ log b :=
  log_monotoneOn ha (ha.of_le hab) hab

/-- `log` is operator concave. -/
lemma CFC.concaveOn_log : ConcaveOn ℝ {a : A | IsStrictlyPositive a} log := by
  have hconv : Convex ℝ {a : A | IsStrictlyPositive a} := by
    apply convex_iff_forall_pos.mpr
    intro x hx y hy a b ha hb _
    exact (IsStrictlyPositive.smul ha hx).add_nonneg
      (smul_nonneg hb.le (show IsStrictlyPositive y from hy).nonneg)
  refine concaveOn_iff.mpr ⟨hconv, ?_⟩
  intro x hx y hy a b ha hb hab
  have hz : IsStrictlyPositive (a • x + b • y) := hconv hx hy ha hb hab
  let := neBot_comap_positive_nhds_zero
  refine le_of_tendsto_of_tendsto
    (((tendsto_rpow_sub_one_log hx).const_smul a).add
      ((tendsto_rpow_sub_one_log hy).const_smul b)) (tendsto_rpow_sub_one_log hz) ?_
  filter_upwards [tendsto_comap.eventually (eventually_lt_nhds (zero_lt_one : (0 : ℝ) < 1))]
    with p hp
  have hpow : ConcaveOn ℝ (Ici (0 : A)) (fun a : A ↦ a ^ (p : ℝ)) :=
    CFC.concaveOn_rpow ⟨p.property.le, hp.le⟩
  have hp₀ : 0 ≤ Checked.inv (p : ℝ) p.property.ne'.isUnit := _root_.inv_nonneg.mpr p.property.le
  have hquot := (hpow.sub (convexOn_const (1 : A) (convex_Ici 0))).smul hp₀
  exact (concaveOn_iff.mp hquot).2 (show IsStrictlyPositive x from hx).nonneg
    (show IsStrictlyPositive y from hy).nonneg ha hb hab
