import Mathlib.RingTheory.Nilpotent.Exp
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.Algebra.Lie.Nilpotent

/-!
# Nilpotency invariants need nilpotency

These tests ensure that the nilpotency class of an element and of a group, the nilpotency length of
a Lie module, and the exponential of a nilpotent element take nilpotency evidence, so that a
nonnilpotent object no longer receives the value `0`.
-/

/-- info: Unknown identifier `isNilpotent_of_pos_nilpotencyClass` -/
#guard_msgs in
#check_failure isNilpotent_of_pos_nilpotencyClass

/-- info: Unknown identifier `pos_nilpotencyClass_iff` -/
#guard_msgs in
#check_failure pos_nilpotencyClass_iff

/-- info: Unknown constant `Group.nilpotencyClass_of_not_nilpotent` -/
#guard_msgs in
#check_failure Group.nilpotencyClass_of_not_nilpotent

/-! The exponential of `1 : ℚ`, which is not nilpotent, was formerly `0`. -/

/--
error: Type mismatch
  IsNilpotent.exp 1
has type
  IsNilpotent 1 → ℚ
but is expected to have type
  ℚ
-/
#guard_msgs in
noncomputable example : ℚ := IsNilpotent.exp (1 : ℚ)

example : ¬IsNilpotent (1 : ℚ) := not_isNilpotent_one

example : IsNilpotent.exp (0 : ℚ) IsNilpotent.zero = 1 := IsNilpotent.exp_zero _

example : nilpotencyClass (0 : ℚ) IsNilpotent.zero = 1 := nilpotencyClass_zero _

/-! The symmetric group on three letters is not nilpotent; its nilpotency class was `0`. -/

/--
error: failed to synthesize instance of type class
  Group.IsNilpotent (Equiv.Perm (Fin 3))
-/
#guard_msgs (substring := true) in
noncomputable example : ℕ := Group.nilpotencyClass (Equiv.Perm (Fin 3))

/-- A nilpotent group of class at most `n` has its `n`-th upper central term equal to the group. -/
example {G : Type*} [Group G] [Group.IsNilpotent G] :
    Subgroup.upperCentralSeries G (Group.nilpotencyClass G) = ⊤ :=
  Subgroup.upperCentralSeries_nilpotencyClass
