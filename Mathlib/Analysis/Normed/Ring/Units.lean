/-
Copyright (c) 2020 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.RingTheory.Ideal.Nonunits

/-!
# The group of units of a complete normed ring

This file contains the basic theory for the group of units (invertible elements) of a complete
normed ring (Banach algebras being a notable special case).

## Main results

The constructions `Units.add` and `Units.ofNearby` (based on `Units.oneSub` defined elsewhere)
state, in varying forms, that perturbations of a unit are units. They are not stated
in their optimal form; more precise versions would use the spectral radius.

The first main result is `Units.isOpen`: the group of units of a normed ring with summable
geometric series is an open subset of the ring.

Inverse values in this file are evaluated only on units. The finite expansion and asymptotic
estimates use a second unit `y` and its ambient displacement `y - x`. Continuity on the ambient
unit subtype establishes that its topology agrees with the usual topology on `Rˣ`.
-/

@[expose] public section

noncomputable section

open Topology

variable {R : Type*} [NormedRing R] [HasSummableGeomSeries R]

namespace Units

/-- A perturbation of a unit is invertible when its relative displacement has norm below one.
The multiplicative bound also applies to the trivial ring. -/
@[simps! val]
def add (x : Rˣ) (t : R) (h : ‖(↑x⁻¹ : R)‖ * ‖t‖ < 1) : Rˣ :=
  Units.copy
    (x * Units.oneSub (-((x⁻¹).1 * t)) (by
      exact (norm_neg _).trans_le (norm_mul_le _ _) |>.trans_lt h))
    (x + t) (by simp [mul_add]) _ rfl

/-- Construct a nearby unit using the exact relative-displacement bound. -/
@[simps! val]
def ofNearby (x : Rˣ) (y : R) (h : ‖(↑x⁻¹ : R)‖ * ‖y - x‖ < 1) : Rˣ :=
  (x.add (y - x : R) h).copy y (by simp) _ rfl

/-- The invertible elements of a normed ring with summable geometric series form an open set. -/
protected theorem isOpen : IsOpen { x : R | IsUnit x } := by
  rw [Metric.isOpen_iff]
  rintro _ ⟨x, rfl⟩
  have hp : 0 < ‖(↑x⁻¹ : R)‖ + 1 := by positivity
  refine ⟨(‖(↑x⁻¹ : R)‖ + 1)⁻¹, _root_.inv_pos.mpr hp, fun y hy ↦ ?_⟩
  rw [mem_ball_iff_norm] at hy
  have hy' : ‖y - (x : R)‖ * (‖(↑x⁻¹ : R)‖ + 1) < 1 :=
    (lt_div_iff₀ hp).mp (by simpa only [one_div₀] using hy)
  exact (x.ofNearby y (by nlinarith [norm_nonneg (y - (x : R))])).isUnit

protected theorem nhds (x : Rˣ) : { x : R | IsUnit x } ∈ 𝓝 (x : R) :=
  IsOpen.mem_nhds Units.isOpen x.isUnit

end Units

namespace nonunits

/-- The `nonunits` in a normed ring with summable geometric series are contained in the
complement of the ball of radius `1` centered at `1 : R`. -/
theorem subset_compl_ball : nonunits R ⊆ (Metric.ball (1 : R) 1)ᶜ := fun x hx h₁ ↦ hx <|
  sub_sub_self 1 x ▸ (Units.oneSub (1 - x) (by rwa [mem_ball_iff_norm'] at h₁)).isUnit

-- The `nonunits` in a normed ring with summable geometric series are a closed set
protected theorem isClosed : IsClosed (nonunits R) :=
  Units.isOpen.isClosed_compl

end nonunits

namespace NormedRing

open Asymptotics Filter Metric Finset

/-- The inverse of `1 - t`, constructed as a unit, is its convergent geometric series. -/
theorem inverse_one_sub (t : R) (h : ‖t‖ < 1) :
    (↑(Units.oneSub t h)⁻¹ : R) = ∑' i : ℕ, t ^ i :=
  (geom_series_eq_inverse t h).symm

omit [HasSummableGeomSeries R] in
/-- Recenter an inverse at another unit. Both arguments lie in the exact inverse domain. -/
theorem inverse_add (x y : Rˣ) : (↑y⁻¹ : R) = ↑(x⁻¹ * y)⁻¹ * ↑x⁻¹ := by
  simp only [mul_inv_rev, inv_inv, Units.val_mul, mul_assoc, Units.mul_inv, mul_one]

omit [HasSummableGeomSeries R] in
/-- The finite geometric expansion of an inverse is valid on the entire unit domain. -/
theorem inverse_one_sub_nth_order (u : Rˣ) (n : ℕ) :
    (↑u⁻¹ : R) = (∑ i ∈ range n, (1 - (u : R)) ^ i) + (1 - (u : R)) ^ n * ↑u⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, pow_succ, mul_assoc, sub_mul, one_mul, Units.mul_inv]
    calc
      (↑u⁻¹ : R) = (∑ i ∈ range n, (1 - (u : R)) ^ i) + (1 - (u : R)) ^ n * ↑u⁻¹ := ih
      _ = _ := by
        rw [add_assoc, mul_sub, mul_one, ← add_sub_assoc, add_sub_cancel_left]

theorem inverse_one_sub_nth_order' (n : ℕ) {t : R} (ht : ‖t‖ < 1) :
    (↑(Units.oneSub t ht)⁻¹ : R) =
      (∑ i ∈ range n, t ^ i) + t ^ n * ↑(Units.oneSub t ht)⁻¹ := by
  simpa only [Units.val_oneSub, sub_sub_cancel] using
    inverse_one_sub_nth_order (Units.oneSub t ht) n

omit [HasSummableGeomSeries R] in
/-- The finite inverse expansion about `x`, with displacement `y - x`. -/
theorem inverse_add_nth_order (x y : Rˣ) (n : ℕ) :
    (↑y⁻¹ : R) =
      (∑ i ∈ range n, (-(↑x⁻¹ : R) * ((y : R) - x)) ^ i) * ↑x⁻¹ +
        (-(↑x⁻¹ : R) * ((y : R) - x)) ^ n * ↑y⁻¹ := by
  have ht : (1 : R) - ↑(x⁻¹ * y) = -(↑x⁻¹ : R) * ((y : R) - x) := by
    rw [Units.val_mul, neg_mul, mul_sub, Units.inv_mul, neg_sub]
  have h := congrArg (fun z : R ↦ z * ↑x⁻¹) (inverse_one_sub_nth_order (x⁻¹ * y) n)
  simpa only [add_mul, mul_assoc, ← inverse_add x y, ht] using h

omit [HasSummableGeomSeries R] in
/-- Inverse values are locally bounded on units. -/
theorem inverse_add_norm (x : Rˣ) :
    (fun y : Rˣ ↦ (↑y⁻¹ : R)) =O[𝓝 x] (fun _ ↦ (1 : ℝ)) :=
  (Units.continuous_coe_inv.tendsto x).isBigO_one ℝ

omit [HasSummableGeomSeries R] in
/-- The remainder of the finite expansion is bounded by the corresponding displacement power. -/
theorem inverse_add_norm_diff_nth_order (x : Rˣ) (n : ℕ) :
    (fun y : Rˣ ↦ (↑y⁻¹ : R) -
      (∑ i ∈ range n, (-(↑x⁻¹ : R) * ((y : R) - x)) ^ i) * ↑x⁻¹) =O[𝓝 x]
      (fun y ↦ ‖(y : R) - x‖ ^ n) := by
  have heq :
      (fun y : Rˣ ↦ (↑y⁻¹ : R) -
        (∑ i ∈ range n, (-(↑x⁻¹ : R) * ((y : R) - x)) ^ i) * ↑x⁻¹) =
      (fun y : Rˣ ↦ (-(↑x⁻¹ : R) * ((y : R) - x)) ^ n * ↑y⁻¹) := by
    funext y
    exact sub_eq_iff_eq_add.mpr ((inverse_add_nth_order x y n).trans (add_comm _ _))
  rw [heq]
  refine ((isBigO_refl _ _).norm_right.mul (inverse_add_norm x)).trans ?_
  simp only [mul_one, isBigO_norm_left]
  exact ((isBigO_refl _ _).norm_right.const_mul_left _).pow _

omit [HasSummableGeomSeries R] in
/-- First-order control of inverse values on their unit domain. -/
theorem inverse_add_norm_diff_first_order (x : Rˣ) :
    (fun y : Rˣ ↦ (↑y⁻¹ : R) - ↑x⁻¹) =O[𝓝 x] (fun y ↦ ‖(y : R) - x‖) := by
  simpa using inverse_add_norm_diff_nth_order x 1

omit [HasSummableGeomSeries R] in
/-- Second-order control after subtracting the derivative of inversion. -/
theorem inverse_add_norm_diff_second_order (x : Rˣ) :
    (fun y : Rˣ ↦ (↑y⁻¹ : R) - ↑x⁻¹ + ↑x⁻¹ * ((y : R) - x) * ↑x⁻¹) =O[𝓝 x]
      (fun y ↦ ‖(y : R) - x‖ ^ 2) := by
  convert! inverse_add_norm_diff_nth_order x 2 using 2
  simp only [sum_range_succ, sum_range_zero, zero_add, pow_zero, pow_one, add_mul, one_mul,
    ← sub_sub, neg_mul, sub_neg_eq_add]

omit [HasSummableGeomSeries R] in
/-- A local estimate for inverse values, using only multiplication of units. -/
theorem inverse_sub_norm_le (x y : Rˣ)
    (h : ‖(↑x⁻¹ : R)‖ * ‖(y : R) - x‖ ≤ (1 / 2 : ℝ)) :
    ‖(↑y⁻¹ : R) - ↑x⁻¹‖ ≤ 2 * ‖(↑x⁻¹ : R)‖ ^ 2 * ‖(y : R) - x‖ := by
  have hdiff : ‖(↑y⁻¹ : R) - ↑x⁻¹‖ ≤
      ‖(↑y⁻¹ : R)‖ * ‖(y : R) - x‖ * ‖(↑x⁻¹ : R)‖ := by
    rw [Units.inv_sub_inv' y x]
    calc
      ‖(↑y⁻¹ : R) * (↑x - ↑y) * ↑x⁻¹‖ ≤
          ‖(↑y⁻¹ : R) * (↑x - ↑y)‖ * ‖(↑x⁻¹ : R)‖ := norm_mul_le _ _
      _ ≤ (‖(↑y⁻¹ : R)‖ * ‖(x : R) - y‖) * ‖(↑x⁻¹ : R)‖ :=
        mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ = _ := by rw [norm_sub_rev]
  have hnorm : ‖(↑y⁻¹ : R)‖ ≤
      ‖(↑y⁻¹ : R)‖ * ‖(y : R) - x‖ * ‖(↑x⁻¹ : R)‖ + ‖(↑x⁻¹ : R)‖ :=
    calc
      ‖(↑y⁻¹ : R)‖ ≤ ‖(↑x⁻¹ : R)‖ + ‖(↑y⁻¹ : R) - ↑x⁻¹‖ := norm_le_norm_add_norm_sub' _ _
      _ ≤ ‖(↑x⁻¹ : R)‖ + ‖(↑y⁻¹ : R)‖ * ‖(y : R) - x‖ * ‖(↑x⁻¹ : R)‖ :=
        add_le_add le_rfl hdiff
      _ = _ := add_comm _ _
  have hmul := mul_le_mul_of_nonneg_left h (norm_nonneg (↑y⁻¹ : R))
  have hbound : ‖(↑y⁻¹ : R)‖ ≤ 2 * ‖(↑x⁻¹ : R)‖ := by nlinarith
  have hmul' := mul_le_mul_of_nonneg_right hbound
    (mul_nonneg (norm_nonneg ((y : R) - x)) (norm_nonneg (↑x⁻¹ : R)))
  nlinarith

omit [HasSummableGeomSeries R] in
/-- Inverse values are continuous on the subtype of invertible elements with its ambient topology.
This proof does not extend inversion to nonunits or assume completeness of the ring. -/
theorem inverse_continuous :
    Continuous (fun x : {x : R | IsUnit x} ↦ (↑x.property.unit⁻¹ : R)) := by
  apply continuous_iff_continuousAt.2
  intro x
  apply Metric.continuousAt_iff.2
  intro ε hε
  let c := ‖(↑x.property.unit⁻¹ : R)‖
  have hc : 0 ≤ c := norm_nonneg _
  have hp : 0 < 2 * c + 1 := by positivity
  have hq : 0 < 2 * c ^ 2 + 1 := by positivity
  refine ⟨min ((2 * c + 1)⁻¹) (ε / (2 * c ^ 2 + 1)),
    lt_min (_root_.inv_pos.mpr hp) (div_pos hε hq), ?_⟩
  intro y hy
  change dist (y : R) (x : R) < _ at hy
  rw [dist_eq_norm] at hy
  have hy₁ := lt_of_lt_of_le hy (min_le_left _ _)
  have hy₂ := lt_of_lt_of_le hy (min_le_right _ _)
  have hsmall : c * ‖(y : R) - x‖ ≤ (1 / 2 : ℝ) := by
    have := (lt_div_iff₀ hp).mp
      (show ‖(y : R) - x‖ < 1 / (2 * c + 1) by simpa only [one_div₀] using hy₁)
    nlinarith [norm_nonneg ((y : R) - x)]
  have hε' := (lt_div_iff₀ hq).mp hy₂
  have hbound := inverse_sub_norm_le x.property.unit y.property.unit (by
    simpa only [IsUnit.unit_spec] using hsmall)
  rw [dist_eq_norm]
  simp only [IsUnit.unit_spec] at hbound
  change ‖(↑y.property.unit⁻¹ : R) - ↑x.property.unit⁻¹‖ < ε
  dsimp only [c] at hε' ⊢
  nlinarith [norm_nonneg ((y : R) - x)]

omit [HasSummableGeomSeries R] in
/-- Inverse values of `1 - t` are bounded near zero on their exact domain. -/
theorem inverse_one_sub_norm :
    (fun t : {t : R | IsUnit (1 - t)} ↦ (↑t.property.unit⁻¹ : R)) =O[
      𝓝 (⟨0, by simp⟩ : {t : R | IsUnit (1 - t)})]
      (fun _ ↦ (1 : ℝ)) := by
  have hmap : Continuous (fun t : {t : R | IsUnit (1 - t)} ↦
      (⟨1 - t.val, t.property⟩ : {x : R | IsUnit x})) :=
    (continuous_const.sub continuous_subtype_val).subtype_mk fun t ↦ t.property
  exact ((inverse_continuous.comp hmap).tendsto _).isBigO_one ℝ

omit [HasSummableGeomSeries R] in
/-- Inverse values are continuous at every point of their exact domain. -/
theorem inverse_continuousAt (x : Rˣ) :
    ContinuousAt (fun y : {y : R | IsUnit y} ↦ (↑y.property.unit⁻¹ : R))
      ⟨(x : R), x.isUnit⟩ :=
  inverse_continuous.continuousAt

end NormedRing

namespace Units

open NormedRing

/-- In a normed ring with summable geometric series, the coercion from `Rˣ` (equipped with the
induced topology from the embedding in `R × R`) to `R` is an open embedding. -/
theorem isOpenEmbedding_val : IsOpenEmbedding (val : Rˣ → R) where
  toIsEmbedding := isEmbedding_val_mk' inverse_continuous fun u ↦ by
    have hu : u.isUnit.unit = u := Units.ext u.isUnit.unit_spec
    change (↑u.isUnit.unit⁻¹ : R) = ↑u⁻¹
    rw [hu]
  isOpen_range := Units.isOpen

/-- In a normed ring with summable geometric series, the coercion from `Rˣ` (equipped with the
induced topology from the embedding in `R × R`) to `R` is an open map. -/
theorem isOpenMap_val : IsOpenMap (val : Rˣ → R) :=
  isOpenEmbedding_val.isOpenMap

end Units

namespace Ideal

/-- An ideal which contains an element within `1` of `1 : R` is the unit ideal. -/
theorem eq_top_of_norm_lt_one (I : Ideal R) {x : R} (hxI : x ∈ I) (hx : ‖1 - x‖ < 1) : I = ⊤ :=
  let u := Units.oneSub (1 - x) hx
  I.eq_top_iff_one.mpr <| by
    simpa only [show u.inv * x = 1 by simp [u]] using I.mul_mem_left u.inv hxI

/-- The `Ideal.closure` of a proper ideal in a normed ring with summable
geometric series is proper. -/
theorem closure_ne_top (I : Ideal R) (hI : I ≠ ⊤) : I.closure ≠ ⊤ := by
  have h := closure_minimal (coe_subset_nonunits hI) nonunits.isClosed
  simpa only [I.closure.eq_top_iff_one, Ne] using! mt (@h 1) one_notMem_nonunits

/-- The `Ideal.closure` of a maximal ideal in a normed ring with summable
geometric series is the ideal itself. -/
theorem IsMaximal.closure_eq {I : Ideal R} (hI : I.IsMaximal) : I.closure = I :=
  (hI.eq_of_le (I.closure_ne_top hI.ne_top) subset_closure).symm

/-- Maximal ideals in normed rings with summable geometric series are closed. -/
instance IsMaximal.isClosed {I : Ideal R} [hI : I.IsMaximal] : IsClosed (I : Set R) :=
  isClosed_of_closure_subset <| Eq.subset <| congr_arg ((↑) : Ideal R → Set R) hI.closure_eq

end Ideal
