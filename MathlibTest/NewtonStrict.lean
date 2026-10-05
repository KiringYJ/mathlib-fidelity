import Mathlib.Dynamics.Newton
import Mathlib.Tactic.NormNum

/-!
# Strict Newton iteration

These tests ensure that the Newton step is defined exactly where the derivative is a unit, so that
a point where it is not cannot become a spurious fixed point, and that Newton iteration runs on the
points where the polynomial is nilpotent and its derivative a unit.
-/

open Polynomial

/-- info: Unknown constant `Polynomial.newtonMap_apply_of_not_isUnit` -/
#guard_msgs in
#check_failure Polynomial.newtonMap_apply_of_not_isUnit

/-- info: Unknown constant `Polynomial.isFixedPt_newtonMap_of_isUnit_iff` -/
#guard_msgs in
#check_failure Polynomial.isFixedPt_newtonMap_of_isUnit_iff

/-- info: Unknown constant `Polynomial.isNilpotent_iterate_newtonMap_sub_of_isNilpotent` -/
#guard_msgs in
#check_failure Polynomial.isNilpotent_iterate_newtonMap_sub_of_isNilpotent

/-- info: Unknown constant `Polynomial.newtonMap_apply_of_isUnit` -/
#guard_msgs in
#check_failure Polynomial.newtonMap_apply_of_isUnit

/-- info: Unknown constant `Polynomial.isFixedPt_newtonMap_of_aeval_eq_zero` -/
#guard_msgs in
#check_failure Polynomial.isFixedPt_newtonMap_of_aeval_eq_zero

/-- info: Unknown constant `Polynomial.aeval_pow_two_pow_dvd_aeval_iterate_newtonMap` -/
#guard_msgs in
#check_failure Polynomial.aeval_pow_two_pow_dvd_aeval_iterate_newtonMap

/-! At `0` the derivative of `X ^ 2 + 1` vanishes, and `0` is not a root. The former identity
fallback made `0` a fixed point of Newton's map; now no Newton step exists there. -/

example : ¬IsUnit (aeval (0 : ℚ) (derivative (X ^ 2 + 1 : ℚ[X]))) := by
  simp

example : aeval (0 : ℚ) (X ^ 2 + 1 : ℚ[X]) ≠ 0 := by
  simp

/--
error: Type mismatch
  (X ^ 2 + 1).newtonMap 0
has type
  IsUnit ((aeval 0) (derivative (X ^ 2 + 1))) → ℚ
but is expected to have type
  ℚ
-/
#guard_msgs in
noncomputable example : ℚ := newtonMap (X ^ 2 + 1 : ℚ[X]) (0 : ℚ)

/-! A Newton step where the derivative is a unit. -/

private lemma isUnit_derivative_one :
    IsUnit (aeval (1 : ℚ) (derivative (X ^ 2 - 2 : ℚ[X]))) := by
  simp

example : newtonMap (X ^ 2 - 2 : ℚ[X]) (1 : ℚ) isUnit_derivative_one = 3 / 2 := by
  rw [newtonMap_apply, Units.val_inv_eq_inv_val, IsUnit.unit_spec]
  simp
  norm_num

/-! A unit derivative need not survive a step: the step of `X ^ 2 + 1` from `1` reaches `0`, where
the derivative vanishes. -/

private lemma isUnit_derivative_one' :
    IsUnit (aeval (1 : ℚ) (derivative (X ^ 2 + 1 : ℚ[X]))) := by
  simp

example : newtonMap (X ^ 2 + 1 : ℚ[X]) (1 : ℚ) isUnit_derivative_one' = 0 := by
  rw [newtonMap_apply, Units.val_inv_eq_inv_val, IsUnit.unit_spec]
  norm_num

/-! Fixed points of the Newton step are exactly the roots. -/

example {R : Type*} [CommRing R] (P : R[X]) {x : R} (h : IsUnit (aeval x (derivative P))) :
    P.newtonMap x h = x ↔ aeval x P = 0 :=
  newtonMap_eq_self_iff h

/-! Newton iteration from a point where the polynomial is nilpotent and the derivative a unit. -/

example {R : Type*} [CommRing R] (P : R[X]) (x : P.NewtonDomain R) (n : ℕ) :
    IsNilpotent ((NewtonDomain.step^[n] x : R) - x) :=
  NewtonDomain.isNilpotent_iterate_step_sub x n

example {R : Type*} [CommRing R] (P : R[X]) {x : R} (h : IsNilpotent (aeval x P))
    (h' : IsUnit (aeval x (derivative P))) : ∃! r, IsNilpotent (x - r) ∧ aeval r P = 0 :=
  existsUnique_nilpotent_sub_and_aeval_eq_zero h h'
