/-
Copyright (c) 2026 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.ConjSqrt
import Mathlib.Analysis.Convex.Mul
public import Mathlib.Algebra.Algebra.StrictPositivity
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.NormNum.GCD

/-!
# Order properties of inversion in C⋆-algebras

This file shows that inversion on the domain of strictly positive operators is convex.

## Main declarations

* `convexOn_inv`: inversion is convex on strictly positive operators, i.e. the inverse
  is operator convex.
-/

namespace CStarAlgebra

open CFC Set

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

public lemma convexOn_inv :
    ConvexOn ℝ Set.univ
      (fun x : {a : A // IsStrictlyPositive a} ↦ Checked.inv (x : A) x.property.isUnit)
      Subtype.val := by
  refine ⟨?_, ?_⟩
  · rw [Set.image_univ]
    have hrange : Set.range (Subtype.val : {a : A // IsStrictlyPositive a} → A) =
        {a : A | IsStrictlyPositive a} := by
      ext a
      exact ⟨fun ⟨b, hb⟩ ↦ hb ▸ b.property, fun h ↦ ⟨⟨a, h⟩, rfl⟩⟩
    rw [hrange]
    apply convex_iff_forall_pos.mpr
    intro x hx y hy a b ha hb _
    exact (IsStrictlyPositive.smul ha hx).add_nonneg (smul_nonneg hb.le hy.nonneg)
  intro ⟨x, xpos⟩ _ ⟨y, ypos⟩ _ a b ha hb hab ⟨w, wpos⟩ _ hw
  change w = a • x + b • y at hw
  subst w
  have hxunit : IsUnit x := xpos.isUnit
  have hyunit : IsUnit y := ypos.isUnit
  let z := conjSqrt x⁻¹ y
  have zpos : IsStrictlyPositive z := (isStrictlyPositive_conjSqrt_iff _ _ xpos.inv).mpr ypos
  have hzunit : IsUnit z := zpos.isUnit
  have hsp : IsStrictlyPositive (a • 1 + b • z) := by
    by_cases ha' : 0 < a
    · exact (IsStrictlyPositive.smul ha' isStrictlyPositive_one).add_nonneg
        (smul_nonneg hb zpos.nonneg)
    · have hb' : 0 < b := by linarith
      exact IsStrictlyPositive.nonneg_add (smul_nonneg ha zero_le_one)
        (IsStrictlyPositive.smul hb' zpos)
  have hspunit : IsUnit (a • 1 + b • z) := hsp.isUnit
  let r : C(spectrum ℝ z, ℝ) := (ContinuousMap.id ℝ).restrict (spectrum ℝ z)
  let q : C(spectrum ℝ z, ℝ) := a • 1 + b • r
  have hpos (v : spectrum ℝ z) : 0 < q v := by
    have hv : 0 < (v : ℝ) := zpos.spectrum_pos v.property
    have hmem : a • (1 : ℝ) + b • (v : ℝ) ∈ Ioi 0 :=
      (convex_Ioi (0 : ℝ)) (Set.mem_Ioi.mpr zero_lt_one) (Set.mem_Ioi.mpr hv) ha hb hab
    simpa only [q, r, ContinuousMap.add_apply, ContinuousMap.smul_apply,
      ContinuousMap.one_apply, ContinuousMap.restrict_apply, ContinuousMap.id_apply] using
      Set.mem_Ioi.mp hmem
  let qi : C(spectrum ℝ z, ℝ) := ⟨fun v ↦ Checked.inv (q v) (hpos v).ne'.isUnit,
    q.continuous.fun_inv₀ (h0 := fun v ↦ (hpos v).ne'.isUnit)⟩
  let ri : C(spectrum ℝ z, ℝ) := ⟨fun v ↦ Checked.inv (v : ℝ)
    (zpos.spectrum_pos v.property).ne'.isUnit,
    continuous_subtype_val.fun_inv₀ (h0 := fun v : spectrum ℝ z ↦
      (zpos.spectrum_pos v.property).ne'.isUnit)⟩
  have hr : cfcHom (R := ℝ) zpos.isSelfAdjoint r = z := cfcHom_id _
  have hq : cfcHom (R := ℝ) zpos.isSelfAdjoint q = a • 1 + b • z := by
    simp only [q, map_add, map_smul, map_one, hr]
  have hqi : cfcHom (R := ℝ) zpos.isSelfAdjoint qi =
      Checked.inv (a • 1 + b • z) hspunit := by
    apply (inv_eq_of_mul_eq_one_right₀ ?_).symm
    rw [← hq, ← map_mul]
    have heq : q * qi = 1 := by ext v; exact mul_inv_cancel₀
    rw [heq, map_one]
  have hri : cfcHom (R := ℝ) zpos.isSelfAdjoint ri = Checked.inv z hzunit := by
    apply (inv_eq_of_mul_eq_one_right₀ ?_).symm
    have heq : r * ri = 1 := by ext v; exact mul_inv_cancel₀
    calc
      _ = cfcHom (R := ℝ) zpos.isSelfAdjoint r * cfcHom (R := ℝ) zpos.isSelfAdjoint ri :=
        congrArg (fun u : A ↦ u * cfcHom (R := ℝ) zpos.isSelfAdjoint ri) hr.symm
      _ = _ := by rw [← map_mul, heq, map_one]
  have hbound : Checked.inv (a • 1 + b • z) hspunit ≤ a • 1 + b • Checked.inv z hzunit := by
    calc _ = cfcHom (R := ℝ) zpos.isSelfAdjoint qi := hqi.symm
      _ ≤ cfcHom (R := ℝ) zpos.isSelfAdjoint (a • 1 + b • ri) := by
        apply (cfcHom_le_iff zpos.isSelfAdjoint).mpr
        intro v
        have hv : 0 < (v : ℝ) := zpos.spectrum_pos v.property
        have hconv := (convexOn_zpow (𝕜 := ℝ) (-1)).2
          (x := ⟨1, Set.mem_Ioi.mpr zero_lt_one⟩) (y := ⟨v, Set.mem_Ioi.mpr hv⟩)
          (by trivial) (by trivial) ha hb hab
          (z := ⟨q v, Set.mem_Ioi.mpr (hpos v)⟩) (by trivial) rfl
        change Checked.inv (q v) (hpos v).ne'.isUnit ≤
          a • (1 : ℝ) + b • Checked.inv (v : ℝ) hv.ne'.isUnit
        simpa only [zpow_neg_one₀, inv_one₀] using hconv
      _ = _ := by simp only [map_add, map_smul, map_one, hri]
  calc _ = Checked.inv (conjSqrt x (a • 1 + b • z))
        (((xpos.isUnit_cfcSqrt x).mul hspunit).mul (xpos.isUnit_cfcSqrt x)) := by
        simp only [map_add, map_smul, conjSqrt_one x xpos.nonneg, z,
          conjSqrt_conjSqrt_inv x y xpos]
      _ = conjSqrt x⁻¹ (Checked.inv (a • 1 + b • z) hspunit) := inv_conjSqrt x _ xpos
      _ ≤ conjSqrt x⁻¹ (a • 1 + b • z⁻¹) := conjSqrt_monotone hbound
      _ = a • x⁻¹ + b • conjSqrt x⁻¹ z⁻¹ := by
        simp only [map_add, map_smul, conjSqrt_one x⁻¹ xpos.inv.nonneg]
      _ = a • x⁻¹ + b • y⁻¹ := by
        congr 1
        rw [← inv_conjSqrt x z xpos]
        simp only [z, conjSqrt_conjSqrt_inv x y xpos]
/-- A positive scalar shift makes every nonnegative operator invertible; inversion
of this shift is convex on the nonnegative cone in its inclusion coordinates. -/
public lemma convexOn_inv_algebraMap_add {t : ℝ} (ht : 0 < t) :
    ConvexOn ℝ Set.univ
      (fun x : Ici (0 : A) ↦ Checked.inv (algebraMap ℝ A t + x)
        ((isStrictlyPositive_algebraMap (A := A) ht).add_nonneg x.property).isUnit)
      Subtype.val := by
  have hpos (x : Ici (0 : A)) : IsStrictlyPositive (algebraMap ℝ A t + x) :=
    (isStrictlyPositive_algebraMap (A := A) ht).add_nonneg x.property
  refine ⟨?_, ?_⟩
  · simpa only [Set.image_univ, Subtype.range_coe] using convex_Ici (0 : A)
  intro x _ y _ a b ha hb hab z _ hz
  apply convexOn_inv.2 (x := ⟨_, hpos x⟩) (y := ⟨_, hpos y⟩)
    (by trivial) (by trivial) ha hb hab (z := ⟨_, hpos z⟩) (by trivial)
  change algebraMap ℝ A t + (z : A) =
    a • (algebraMap ℝ A t + (x : A)) + b • (algebraMap ℝ A t + (y : A))
  rw [hz, smul_add, smul_add, ← add_add_add_comm, ← add_smul, hab, one_smul]

end CStarAlgebra
