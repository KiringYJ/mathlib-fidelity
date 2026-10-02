/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Measure.Typeclasses.FiniteOnIic

/-!
# Restrictions to right half-lines that are finite on initial rays

Let `μ` be a measure that is finite on compact sets on a linear order whose closed intervals are
compact. Its restriction to a right half-line `Ici a` or `Ioi a` is finite on every initial ray
`Iic x`, since the ray meets the half-line in a subset of `Icc a x`. For instance, the restriction
of Lebesgue measure to `[0, ∞)` is finite on initial rays, although it is infinite.
-/

public section

open Set

namespace MeasureTheory

variable {α : Type*} {m0 : SigmaAlgebra α} [TopologicalSpace α] [LinearOrder α]
  [OpensSigmaAlgebra α] [CompactIccSpace α]

instance isFiniteMeasureOnIic_restrict_Ici [ClosedIciTopology α] (μ : Measure α)
    [IsFiniteMeasureOnCompacts μ] (a : α) : IsFiniteMeasureOnIic (μ.restrict (Ici a)) :=
  ⟨fun x ↦ by
    rw [Measure.restrict_apply' measurableSet_Ici, Iic_inter_Ici]
    exact isCompact_Icc.measure_lt_top⟩

instance isFiniteMeasureOnIic_restrict_Ioi [ClosedIicTopology α] (μ : Measure α)
    [IsFiniteMeasureOnCompacts μ] (a : α) : IsFiniteMeasureOnIic (μ.restrict (Ioi a)) :=
  ⟨fun x ↦ by
    rw [Measure.restrict_apply' measurableSet_Ioi, Iic_inter_Ioi]
    exact (measure_mono Ioc_subset_Icc_self).trans_lt isCompact_Icc.measure_lt_top⟩

end MeasureTheory
