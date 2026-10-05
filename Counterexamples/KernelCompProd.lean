/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module

public import Counterexamples.CondCDF
public import Mathlib.Probability.Kernel.Disintegration.Basic

/-!
# Composition-products outside s-finite inputs

The composition-product `μ ⊗ₘ κ` of a measure and a kernel integrates the measures of sections:
`(μ ⊗ₘ κ) s = ∫⁻ a, κ a (Prod.mk a ⁻¹' s) ∂μ` for measurable `s`. Its domain
`MeasureTheory.Measure.HasCompProd μ κ` contains inputs that are not s-finite, and a statement that
holds for s-finite inputs can fail on it. Formerly `μ ⊗ₘ κ` was zero unless `μ` and `κ` were
s-finite.

## Counting measure composed with a Dirac kernel

Counting measure on `ℝ` is not s-finite (`Counterexample.CondCDF.not_sFinite_count`), but its
composition-product with the constant kernel `dirac 0` exists and is counting measure on the
horizontal axis (`Counterexample.KernelCompProd.count_compProd_const_dirac`), not the zero measure.
This measure is not s-finite
(`Counterexample.KernelCompProd.not_sFinite_count_compProd_const_dirac`), so the
composition-product of a measure that is not s-finite with an s-finite kernel need not be s-finite.

## A conditional kernel that is not s-finite

Let `κ` be the kernel on `ℝ` that is counting measure at `0` and `dirac 0` elsewhere
(`Counterexample.KernelCompProd.countAtZero`). It is not s-finite, because counting measure is not
(`Counterexample.KernelCompProd.not_isSFiniteKernel_countAtZero`). The measures of the sections of
a measurable set depend measurably on the point, so `volume ⊗ₘ κ` exists; since `{0}` is
Lebesgue-null, it is the image of Lebesgue measure under `a ↦ (a, 0)`, whose first marginal is
Lebesgue measure. Hence `κ` is a conditional kernel of the nonzero measure `volume ⊗ₘ κ`
(`Counterexample.KernelCompProd.isCondKernel_countAtZero`). A conditional kernel of a nonzero
measure was formerly s-finite only because the composition-product was zero for every kernel that
is not (`Counterexample.KernelCompProd.exists_isCondKernel_not_isSFiniteKernel`).
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Counterexample.KernelCompProd

open Counterexample.CondCDF

/-! ### Counting measure composed with a Dirac kernel -/

/-- The composition-product of counting measure on `ℝ`, which is not s-finite, with the constant
kernel `dirac 0` is counting measure on the horizontal axis. -/
lemma count_compProd_const_dirac :
    (Measure.count : Measure ℝ) ⊗ₘ Kernel.const ℝ (Measure.dirac (0 : ℝ)) = countOnAxis := by
  ext s hs
  have hs' : MeasurableSet ((fun a : ℝ ↦ (a, (0 : ℝ))) ⁻¹' s) :=
    (measurable_id.prodMk measurable_const) hs
  rw [Measure.compProd_apply hs, countOnAxis, Measure.map_apply hs, ← lintegral_indicator_one hs']
  congr with a
  rw [Kernel.const_apply, Measure.dirac_apply' _ (measurable_prodMk_left hs)]
  rfl

/-- The composition-product of counting measure on `ℝ` with the constant kernel `dirac 0` is not
s-finite, although the kernel is. -/
lemma not_sFinite_count_compProd_const_dirac :
    ¬ SFinite ((Measure.count : Measure ℝ) ⊗ₘ Kernel.const ℝ (Measure.dirac (0 : ℝ))) := by
  rw [count_compProd_const_dirac]
  exact not_sFinite_countOnAxis

/-! ### A conditional kernel that is not s-finite -/

open scoped Classical in
/-- The kernel on `ℝ` that is counting measure at `0` and `dirac 0` elsewhere. -/
def countAtZero : Kernel ℝ ℝ :=
  Kernel.piecewise (measurableSet_singleton (0 : ℝ)) (Kernel.const ℝ Measure.count)
    (Kernel.const ℝ (Measure.dirac 0))

lemma countAtZero_zero : countAtZero 0 = Measure.count := by
  simp [countAtZero, Kernel.piecewise_apply]

lemma countAtZero_of_ne {a : ℝ} (ha : a ≠ 0) : countAtZero a = Measure.dirac 0 := by
  simp [countAtZero, Kernel.piecewise_apply, ha]

/-- `countAtZero` is not s-finite, since its value at `0`, counting measure, is not. -/
lemma not_isSFiniteKernel_countAtZero : ¬ IsSFiniteKernel countAtZero := fun _ ↦
  not_sFinite_count (countAtZero_zero ▸ inferInstance)

/-- The measures of the sections of a measurable set under `countAtZero` depend measurably on the
point: away from `0` they are those under the constant kernel `dirac 0`. -/
lemma measurable_countAtZero_apply_prodMk {s : Set (ℝ × ℝ)} (hs : MeasurableSet s) :
    Measurable fun a ↦ countAtZero a (Prod.mk a ⁻¹' s) := by
  classical
  have h_eq : (fun a ↦ countAtZero a (Prod.mk a ⁻¹' s)) = ({0} : Set ℝ).piecewise
      (fun _ ↦ Measure.count (Prod.mk (0 : ℝ) ⁻¹' s))
      (fun a ↦ Kernel.const ℝ (Measure.dirac (0 : ℝ)) a (Prod.mk a ⁻¹' s)) := by
    ext a
    by_cases ha : a = 0
    · simp [ha, countAtZero_zero]
    · simp [ha, countAtZero_of_ne ha]
  rw [h_eq]
  exact measurable_const.piecewise (measurableSet_singleton 0)
    (Kernel.measurable_kernel_prodMk_left hs)

instance : (volume : Measure ℝ).HasCompProd countAtZero :=
  .of_aemeasurable fun _ hs ↦ (measurable_countAtZero_apply_prodMk hs).aemeasurable

/-- Since `{0}` is Lebesgue-null, `volume ⊗ₘ countAtZero` is the image of Lebesgue measure under
`a ↦ (a, 0)`. -/
lemma volume_compProd_countAtZero :
    (volume : Measure ℝ) ⊗ₘ countAtZero = (volume : Measure ℝ).map (fun a ↦ (a, (0 : ℝ))) := by
  ext s hs
  have hs' : MeasurableSet ((fun a : ℝ ↦ (a, (0 : ℝ))) ⁻¹' s) :=
    (measurable_id.prodMk measurable_const) hs
  rw [Measure.compProd_apply hs, Measure.map_apply hs, ← lintegral_indicator_one hs']
  refine lintegral_congr_ae ?_
  filter_upwards [Measure.ae_ne volume (0 : ℝ)] with a ha
  rw [countAtZero_of_ne ha, Measure.dirac_apply' _ (measurable_prodMk_left hs)]
  rfl

lemma fst_volume_compProd_countAtZero :
    ((volume : Measure ℝ) ⊗ₘ countAtZero).fst = volume := by
  rw [volume_compProd_countAtZero, Measure.fst_map_prodMk (X := fun a : ℝ ↦ a)
    (Y := fun _ : ℝ ↦ (0 : ℝ)) measurable_id' measurable_const]
  exact Measure.map_id'

lemma volume_compProd_countAtZero_ne_zero : (volume : Measure ℝ) ⊗ₘ countAtZero ≠ 0 := by
  intro h
  have := congrArg Measure.fst h
  rw [fst_volume_compProd_countAtZero, Measure.fst_zero] at this
  exact NeZero.ne (volume : Measure ℝ) this

instance : ((volume : Measure ℝ) ⊗ₘ countAtZero).fst.HasCompProd countAtZero := by
  rw [fst_volume_compProd_countAtZero]
  infer_instance

/-- `countAtZero` is a conditional kernel of the nonzero measure `volume ⊗ₘ countAtZero`, although
it is not s-finite. -/
theorem isCondKernel_countAtZero :
    ((volume : Measure ℝ) ⊗ₘ countAtZero).IsCondKernel countAtZero where
  hasCompProd_fst := inferInstance
  disintegrate := by
    ext s hs
    rw [Measure.compProd_apply hs, fst_volume_compProd_countAtZero, Measure.compProd_apply hs]

/-- A conditional kernel of a nonzero measure need not be s-finite. -/
theorem exists_isCondKernel_not_isSFiniteKernel :
    ∃ (ρ : Measure (ℝ × ℝ)) (κ : Kernel ℝ ℝ), ρ ≠ 0 ∧ ρ.IsCondKernel κ ∧ ¬ IsSFiniteKernel κ :=
  ⟨_, countAtZero, volume_compProd_countAtZero_ne_zero, isCondKernel_countAtZero,
    not_isSFiniteKernel_countAtZero⟩

end Counterexample.KernelCompProd
