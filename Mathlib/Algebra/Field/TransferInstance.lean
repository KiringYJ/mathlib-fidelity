/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.GroupWithZero.TransferInstance
public import Mathlib.Algebra.Ring.TransferInstance

/-!
# Transfer algebraic structures across `Equiv`s

This continues the pattern set in `Mathlib/Algebra/Group/TransferInstance.lean`.
-/

public section

assert_not_exists Module

namespace Equiv
variable {α β : Type*} (e : α ≃ β)

-- See note [instance transfer via equivalence]
/-- Transfer `NNRatCast` across an `Equiv` -/
protected abbrev nnratCast [NNRatCast β] : NNRatCast α where nnratCast q := e.invFun q

/-- Transfer `RatCast` across an `Equiv` -/
protected abbrev ratCast [RatCast β] : RatCast α where ratCast n := e.invFun n

/-- Transfer `DivisionRing` across an `Equiv`. In characteristic zero, the rational embeddings
and actions are transferred from `β`. -/
protected abbrev divisionRing [DivisionRing β] : DivisionRing α where
  toRing := e.ring
  __ := e.groupWithZero
  nnratCastOfCharZero _ q :=
    letI := e.ring
    haveI := CharZero.of_map_natCast (R := β) (S := α) e.symm fun _ => rfl
    e.symm q
  nnratCastOfCharZero_mul_den _ q := by
    let := e.ring
    have := CharZero.of_map_natCast (R := β) (S := α) e.symm fun _ => rfl
    change e.symm (e (e.symm _) * e (e.symm _)) = e.symm _
    rw [e.apply_symm_apply, e.apply_symm_apply]
    exact congrArg e.symm (DivisionRing.nnratCastOfCharZero_mul_den _ q)
  nnqsmulOfCharZero _ q a :=
    letI := e.ring
    haveI := CharZero.of_map_natCast (R := β) (S := α) e.symm fun _ => rfl
    e.symm (q • e a)
  nnqsmulOfCharZero_eq_mul _ q a := by
    let := e.ring
    have := CharZero.of_map_natCast (R := β) (S := α) e.symm fun _ => rfl
    change e.symm _ = e.symm (e (e.symm _) * e a)
    rw [e.apply_symm_apply]
    exact congrArg e.symm (DivisionRing.nnqsmulOfCharZero_eq_mul _ q (e a))
  ratCastOfCharZero _ q :=
    letI := e.ring
    haveI := CharZero.of_map_natCast (R := β) (S := α) e.symm fun _ => rfl
    e.symm q
  ratCastOfCharZero_mul_den _ q := by
    let := e.ring
    have := CharZero.of_map_natCast (R := β) (S := α) e.symm fun _ => rfl
    change e.symm (e (e.symm _) * e (e.symm _)) = e.symm _
    rw [e.apply_symm_apply, e.apply_symm_apply]
    exact congrArg e.symm (DivisionRing.ratCastOfCharZero_mul_den _ q)
  qsmulOfCharZero _ q a :=
    letI := e.ring
    haveI := CharZero.of_map_natCast (R := β) (S := α) e.symm fun _ => rfl
    e.symm (q • e a)
  qsmulOfCharZero_eq_mul _ q a := by
    let := e.ring
    have := CharZero.of_map_natCast (R := β) (S := α) e.symm fun _ => rfl
    change e.symm _ = e.symm (e (e.symm _) * e a)
    rw [e.apply_symm_apply]
    exact congrArg e.symm (DivisionRing.qsmulOfCharZero_eq_mul _ q (e a))

/-- Transfer `Field` across an `Equiv` -/
protected abbrev field [Field β] : Field α where
  toCommRing := e.commRing
  __ := e.divisionRing

end Equiv
