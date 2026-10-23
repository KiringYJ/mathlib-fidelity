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

/-- Transfer `DivisionRing` across an `Equiv` -/
protected abbrev divisionRing [DivisionRing β] : DivisionRing α where
  toRing := e.ring
  __ := e.groupWithZero

/-- Transfer `Field` across an `Equiv` -/
protected abbrev field [Field β] : Field α where
  toCommRing := e.commRing
  __ := e.divisionRing

end Equiv
