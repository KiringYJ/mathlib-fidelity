/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Conjugation by the units of a group with zero

The nonzero elements of a group with zero `G₀` act on `G₀` by conjugation through `ConjAct G₀ˣ`.
See `ConjAct.unitsMulDistribMulAction` and `ConjAct.units_smul_def`. This file also equips the type
alias `ConjAct G₀` with its group-with-zero structure.
-/

public section

assert_not_exists Ring

variable {G₀ : Type*}

namespace ConjAct
variable [GroupWithZero G₀]

instance : GroupWithZero (ConjAct G₀) := inferInstanceAs <| GroupWithZero G₀

@[simp] lemma ofConjAct_zero : ofConjAct 0 = (0 : G₀) := rfl
@[simp] lemma toConjAct_zero : toConjAct (0 : G₀) = 0 := rfl

end ConjAct
