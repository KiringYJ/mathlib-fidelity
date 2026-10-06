import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.GroupTheory.OrderOfElement

/-!
# Minimal periods are defined on periodic points

These tests ensure that `Function.minimalPeriod` and `Function.periodicOrbit` take a proof that the
point is periodic, so that a point that never returns no longer receives the minimal period `0` or
the empty orbit, while `MulAction.period` and `orderOf` keep the value `0`, which records that a
point does not return and that an element has infinite order.
-/

open Function

/-- info: Unknown identifier `Function.minimalPeriod_eq_zero_of_notMem_periodicPts` -/
#guard_msgs in
#check_failure Function.minimalPeriod_eq_zero_of_notMem_periodicPts

/-- info: Unknown identifier `Function.minimalPeriod_pos_iff_mem_periodicPts` -/
#guard_msgs in
#check_failure Function.minimalPeriod_pos_iff_mem_periodicPts

/-- info: Unknown identifier `Function.minimalPeriod_eq_zero_iff_notMem_periodicPts` -/
#guard_msgs in
#check_failure Function.minimalPeriod_eq_zero_iff_notMem_periodicPts

/-- info: Unknown identifier `Function.minimalPeriod_pos_of_mem_periodicPts` -/
#guard_msgs in
#check_failure Function.minimalPeriod_pos_of_mem_periodicPts

/-- info: Unknown identifier `Function.periodicOrbit_eq_nil_iff_not_periodic_pt` -/
#guard_msgs in
#check_failure Function.periodicOrbit_eq_nil_iff_not_periodic_pt

/-- info: Unknown identifier `Function.periodicOrbit_eq_nil_of_not_periodic_pt` -/
#guard_msgs in
#check_failure Function.periodicOrbit_eq_nil_of_not_periodic_pt

/-- info: Unknown identifier `Function.minimalPeriod_iterate_eq_div_gcd'` -/
#guard_msgs in
#check_failure Function.minimalPeriod_iterate_eq_div_gcd'

/-- info: Unknown constant `MulAction.pow_smul_eq_iff_minimalPeriod_dvd` -/
#guard_msgs in
#check_failure MulAction.pow_smul_eq_iff_minimalPeriod_dvd

/-- info: Unknown constant `MulAction.zpow_smul_mod_minimalPeriod` -/
#guard_msgs in
#check_failure MulAction.zpow_smul_mod_minimalPeriod

/-! The successor map on `ℕ` has no periodic point, so `0` has neither a minimal period nor a
periodic orbit. -/

theorem zero_notMem_periodicPts_succ : (0 : ℕ) ∉ periodicPts Nat.succ := by
  rintro ⟨n, hn, h⟩
  rw [IsPeriodicPt, IsFixedPt, Nat.succ_iterate] at h
  omega

/--
error: could not synthesize default value for parameter 'hx' using tactics
---
error: this point needs a proof that it is periodic, `x ∈ periodicPts f`
⊢ 0 ∈ periodicPts Nat.succ
-/
#guard_msgs in
noncomputable example : ℕ := minimalPeriod Nat.succ 0

/--
error: could not synthesize default value for parameter 'hx' using tactics
---
error: this point needs a proof that it is periodic, `x ∈ periodicPts f`
⊢ 0 ∈ periodicPts Nat.succ
-/
#guard_msgs in
noncomputable example : Cycle ℕ := periodicOrbit Nat.succ 0

/-! The discharger uses a periodic point of positive period from the context, and a fixed point
has minimal period `1`. -/

example {α : Type*} (f : α → α) (x : α) (n : ℕ) (hn : 0 < n) (hx : IsPeriodicPt f n x) :
    minimalPeriod f x ∣ n :=
  hx.minimalPeriod_dvd _

example {α : Type*} (f : α → α) (x : α) (h : IsFixedPt f x) :
    minimalPeriod f x h.mem_periodicPts = 1 :=
  (minimalPeriod_eq_one_iff_isFixedPt _).2 h

/-! `MulAction.period` and `orderOf` keep the value `0` for a point that does not return. -/

example : AddAction.period (1 : ℤ) (0 : ℤ) = 0 := by
  refine AddAction.period_eq_zero_of_notMem_periodicPts fun ⟨n, hn, h⟩ => ?_
  rw [AddAction.isPeriodicPt_vadd_iff] at h
  simp at h
  omega

example : addOrderOf (1 : ℤ) = 0 :=
  addOrderOf_eq_zero_iff'.2 fun n hn ↦ by simp [hn.ne']
