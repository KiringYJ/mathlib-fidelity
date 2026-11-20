/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module

import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Algebra.TrivSqZeroExt

/-! Domain checks for analytic powers, coefficient ratios, and factorial exponential series. -/

open Filter FormalMultilinearSeries
open scoped Topology ENNReal NNReal

noncomputable section

-- Nonnegative powers remain analytic at a zero of the underlying function.
example : AnalyticAt ℝ (fun x : ℝ ↦ x ^ (0 : ℤ)) 0 := by
  simpa only [id_eq] using
    (analyticAt_id (𝕜 := ℝ) (z := (0 : ℝ))).zpow_nonneg (n := 0) (by omega)

example : AnalyticAt ℝ (fun x : ℝ ↦ x ^ (3 : ℤ)) 0 := by
  simpa only [id_eq] using
    (analyticAt_id (𝕜 := ℝ) (z := (0 : ℝ))).zpow_nonneg (n := 3) (by omega)

-- Inversion is analytic on its own domain, read in ambient coordinates.
example (x : ℝˣ) : AnalyticAt ℝ (fun y : ℝˣ ↦ (↑y⁻¹ : ℝ)) x Units.val :=
  analyticAt_inv x

example {f : ℝ → ℝ} {x : ℝ} (hf : AnalyticAt ℝ f x) (hx : IsUnit (f x)) :
    AnalyticAt ℝ
      (fun y : {y : ℝ // IsUnit (f y)} ↦ Checked.inv (f y.1) y.2)
      ⟨x, hx⟩ Subtype.val :=
  hf.inv hx

-- Coefficient uniqueness and radius exchange apply directly to open coordinate domains.
example {p : FormalMultilinearSeries ℝ ℝ ℝ} {x : {y : ℝ // 0 < y}}
    (hp : HasFPowerSeriesAt (0 : {y : ℝ // 0 < y} → ℝ) p x Subtype.val) : p = 0 := by
  apply hp.eq_zero (hcover := ?_)
  exact Filter.mem_of_superset (isOpen_Ioi.mem_nhds x.2) fun y hy ↦ ⟨⟨y, hy⟩, rfl⟩

example {f : {y : ℝ // 0 < y} → ℝ} {p q : FormalMultilinearSeries ℝ ℝ ℝ}
    {x : {y : ℝ // 0 < y}} {r s : ℝ≥0∞}
    (hp : HasFPowerSeriesOnBall f p x r Subtype.val)
    (hq : HasFPowerSeriesOnBall f q x s Subtype.val) :
    HasFPowerSeriesOnBall f p x s Subtype.val := by
  apply hp.exchange_radius hq (hcover := ?_)
  exact Filter.mem_of_superset (isOpen_Ioi.mem_nhds x.2) fun y hy ↦ ⟨⟨y, hy⟩, rfl⟩

-- A collapsed coordinate domain can give a nonzero series for the zero function.
example : HasFPowerSeriesAt (fun _ : PUnit ↦ (0 : ℝ))
      (FormalMultilinearSeries.id ℝ ℝ 0) PUnit.unit (fun _ ↦ 0) ∧
    FormalMultilinearSeries.id ℝ ℝ 0 ≠ 0 := by
  constructor
  · have hid : (ContinuousLinearMap.id ℝ ℝ).fpowerSeries 0 =
        FormalMultilinearSeries.id ℝ ℝ 0 := rfl
    simpa only [hid, Function.comp_def, id_eq, ContinuousLinearMap.id_apply] using
      ((ContinuousLinearMap.id ℝ ℝ).hasFPowerSeriesAt 0).comp_domain
        (g := fun _ : PUnit ↦ (0 : ℝ)) (x := PUnit.unit)
  · intro h
    have h₁ := congrArg (fun p : FormalMultilinearSeries ℝ ℝ ℝ ↦ p 1 fun _ ↦ 1) h
    exact one_ne_zero (by simpa only [FormalMultilinearSeries.id_apply_one,
      FormalMultilinearSeries.zero_apply, _root_.zero_apply] using h₁)

-- The derivative relation needs coordinate continuity, even when the coordinates are collapsed.
-- Uniqueness of that derivative is a separate condition.
example : HasFDerivAt (fun _ : PUnit ↦ (0 : ℝ)) (ContinuousLinearMap.id ℝ ℝ)
    PUnit.unit (fun _ ↦ (0 : ℝ)) := by
  have hp := ((ContinuousLinearMap.id ℝ ℝ).hasFPowerSeriesAt 0).comp_domain
    (g := fun _ : PUnit ↦ (0 : ℝ)) (x := PUnit.unit)
  have hd := hp.hasFDerivAt (by fun_prop)
  have hid : (ContinuousLinearMap.id ℝ ℝ).fpowerSeries 0 =
      FormalMultilinearSeries.id ℝ ℝ 0 := rfl
  have hcoeff : continuousMultilinearCurryFin1 ℝ ℝ ℝ
      (FormalMultilinearSeries.id ℝ ℝ 0 1) = ContinuousLinearMap.id ℝ ℝ := by
    ext
    simp only [continuousMultilinearCurryFin1_apply, FormalMultilinearSeries.id_apply_one,
      ContinuousLinearMap.id_apply, Fin.snoc_zero]
  simpa only [hid, hcoeff, Function.comp_def, id_eq, ContinuousLinearMap.id_apply] using hd

-- A zero series has every restricted ratio limit, so radius equality needs frequent
-- admissibility as well as convergence of the ratios.
example (r : ℝ) :
    Tendsto
        (fun _n : {_n : ℕ // ‖(0 : ℝ)‖ ≠ 0} ↦
          Checked.div ‖(0 : ℝ)‖ ‖(0 : ℝ)‖ _n.2.isUnit)
        (comap Subtype.val atTop) (𝓝 r) ∧
      (ofScalars ℝ (fun _ : ℕ ↦ (0 : ℝ))).radius = ⊤ := by
  constructor
  · let : IsEmpty {n : ℕ // ‖(0 : ℝ)‖ ≠ 0} := ⟨fun n ↦ n.2 (by simp)⟩
    exact tendsto_of_isEmpty
  · apply radius_eq_top_of_eventually_eq_zero
    exact Eventually.of_forall fun n ↦ ofScalars_eq_zero_of_scalar_zero ℝ rfl

-- In the radius formula, a zero coefficient contributes infinity without taking a field inverse
-- of its zero norm.
example (p : FormalMultilinearSeries ℝ ℝ ℝ) (n : {n : ℕ // n ≠ 0})
    (hn : p (n : ℕ) = 0) :
    ((‖p (n : ℕ)‖₊ : ℝ≥0∞) ^ (1 / (n : ℕ) : ℝ))⁻¹ = ∞ := by
  have hn0 : 0 < ((n : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.pos_iff_ne_zero.mpr n.2)
  simp only [hn, nnnorm_zero, ENNReal.coe_zero,
    ENNReal.zero_rpow_of_pos (one_div_pos.mpr hn0), ENNReal.inv_zero]

-- The exponential has a checked inverse even in a nondivision algebra.
example {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] [CompleteSpace A] (x : A) :
    NormedSpace.exp (-x) =
      Checked.inv (NormedSpace.exp x) (NormedSpace.isUnit_exp x) :=
  NormedSpace.exp_neg x

example {A : Type*} [NormedRing A] [NormedAlgebra ℚ A] [CompleteSpace A]
    (x : A) (n : ℤ) :
    NormedSpace.exp (n • x) =
      Checked.zpow (NormedSpace.exp x) n (fun _ ↦ NormedSpace.isUnit_exp x) :=
  NormedSpace.exp_zsmul n x

-- Every factorial denominator is valid over a characteristic-zero scalar field.
example {K : Type*} [Field K] [CharZero K] [TopologicalSpace K] [IsTopologicalRing K]
    (n : ℕ) :
    NormedSpace.expSeries K K n (fun _ ↦ (1 : K)) = (n.factorial : K)⁻¹ := by
  simp [NormedSpace.expSeries_apply_eq]

/--
error: failed to synthesize instance of type class
  CharZero K

Hint: Type class instance resolution failures can be inspected with the
`set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs (whitespace := lax) in
example {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] :
    FormalMultilinearSeries K K K :=
  NormedSpace.expSeries K K
