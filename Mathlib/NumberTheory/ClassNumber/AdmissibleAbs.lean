/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.NumberTheory.ClassNumber.AdmissibleAbsoluteValue

/-!
# Admissible absolute value on the integers

This file defines an admissible absolute value `AbsoluteValue.absIsAdmissible`
which we use to show the class number of the ring of integers of a number field
is finite.

## Main results

* `AbsoluteValue.absIsAdmissible` shows the "standard" absolute value on `ℤ`,
  mapping negative `x` to `-x`, is admissible.
-/

@[expose] public section


namespace AbsoluteValue

open Int

/-- We can partition a finite family into `partition_card ε` sets, such that the remainders
in each set are close together. -/
theorem exists_partition_int (n : ℕ) {ε : ℝ} (hε : 0 < ε) {b : ℤ} (hb : b ≠ 0) (A : Fin n → ℤ) :
    ∃ t : Fin n → Fin ⌈1 / ε⌉₊,
    ∀ i₀ i₁, t i₀ = t i₁ → ↑(abs (A i₁ % b - A i₀ % b)) < abs b • ε := by
  have hb' : (0 : ℝ) < ↑(abs b) := Int.cast_pos.mpr (abs_pos.mpr hb)
  have hbε : 0 < abs b • ε := by
    rw [Algebra.smul_def]
    exact mul_pos hb' hε
  have hfloor : ∀ i, 0 ≤ floor (((A i % b : ℤ) : ℝ) / (abs b • ε)) :=
    fun _ ↦ floor_nonneg.mpr (div_nonneg (cast_nonneg (emod_nonneg _ hb)) hbε.le)
  refine ⟨fun i ↦ ⟨natAbs (floor (((A i % b : ℤ) : ℝ) / (abs b • ε))), ?_⟩, ?_⟩
  · rw [← ofNat_lt, natAbs_of_nonneg (hfloor i), floor_lt]
    simp only [zsmul_eq_mul, div_mul_eq_div_div₀]
    apply lt_of_lt_of_le _ (Nat.le_ceil _)
    gcongr
    rw [div_lt_one hb', cast_lt]
    exact Int.emod_lt_abs _ hb
  intro i₀ i₁ hi
  have hi : (⌊((A i₀ % b : ℤ) : ℝ) / (abs b • ε)⌋.natAbs : ℤ) =
      ⌊((A i₁ % b : ℤ) : ℝ) / (abs b • ε)⌋.natAbs :=
    congr_arg ((↑) : ℕ → ℤ) (Fin.mk_eq_mk.mp hi)
  rw [natAbs_of_nonneg (hfloor i₀), natAbs_of_nonneg (hfloor i₁)] at hi
  have hi := abs_sub_lt_one_of_floor_eq_floor hi
  rw [abs_sub_comm, ← sub_div, abs_div, div_lt_iff₀ (abs_pos.2 hbε.ne'), one_mul,
    abs_of_nonneg hbε.le] at hi
  rwa [Int.cast_abs, Int.cast_sub]

/-- `abs : ℤ → ℤ` is an admissible absolute value. The cardinality `⌈1 / ε⌉₊` is needed only for
`0 < ε`; the field `card` is a function on all of `ℝ`, and it is `0` elsewhere. -/
noncomputable def absIsAdmissible : IsAdmissible AbsoluteValue.abs :=
  { AbsoluteValue.abs_isEuclidean with
    card := fun ε ↦ if hε : 0 < ε then ⌈1 / ε⌉₊ else 0
    exists_partition' := fun n _ hε _ hb A ↦ by
      rw [dite_eq_left hε]
      exact exists_partition_int n hε hb A }

noncomputable instance : Inhabited (IsAdmissible AbsoluteValue.abs) :=
  ⟨absIsAdmissible⟩

end AbsoluteValue
