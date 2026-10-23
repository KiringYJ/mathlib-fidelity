/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.Algebra.Group.Conj
public import Mathlib.Algebra.GroupWithZero.Units.Basic

/-!
# Conjugacy in a group with zero
-/

public section

assert_not_exists Multiset Ring
-- TODO
-- assert_not_exists DenselyOrdered

namespace GroupWithZero

variable {α : Type*} [GroupWithZero α] {a b : α}

/-- Conjugacy can be witnessed by a checked nonzero conjugating element. -/
lemma isConj_iff_exists_mk0 : IsConj a b ↔
    ∃ (c : α) (hc : c ≠ 0), c * a /ₚ Units.mk0 c hc = b := by
  rw [IsConj, Units.exists0]
  exact exists_congr fun c => exists_congr fun hc =>
    (divp_eq_iff_mul_eq.trans eq_comm).symm

end GroupWithZero
