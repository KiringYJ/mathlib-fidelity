/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.GroupWithZero.Action.ConjAct
public import Mathlib.Algebra.GroupWithZero.Action.Defs

/-!
# Conjugation action of units on a semiring
-/

public section

namespace ConjAct

variable {K : Type*} [Semiring K]

instance unitsDistribMulAction : DistribMulAction (ConjAct Kˣ) K :=
  { ConjAct.unitsMulDistribMulAction.toMulAction with
    smul_zero := by simp [units_smul_def]
    smul_add := by simp [units_smul_def, mul_add, add_mul] }

end ConjAct
