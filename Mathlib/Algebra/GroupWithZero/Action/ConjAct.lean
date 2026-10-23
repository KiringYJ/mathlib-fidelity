/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Conjugation action of a group with zero on itself
-/

public section

assert_not_exists Ring

variable {α G₀ : Type*}

namespace ConjAct
variable [GroupWithZero G₀]

instance : GroupWithZero (ConjAct G₀) := inferInstanceAs <| GroupWithZero G₀

-- Conjugation acts through `ConjAct G₀ˣ` on `G₀`, using the existing
-- `ConjAct.unitsMulDistribMulAction` and `ConjAct.units_smul_def`.
end ConjAct
