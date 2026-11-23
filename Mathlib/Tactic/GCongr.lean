/-
Copyright (c) 2023 Mario Carneiro, Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Heather Macbeth, Jovan Gerbscheid, Yury Kudryashov
-/
module

public import Mathlib.Lean.Elab.NativeDivision
public import Mathlib.Tactic.GCongr.Core
public import Mathlib.Tactic.Hint

/-! # Setup for the `gcongr` tactic

The core implementation of the `gcongr` ("generalized congruence") tactic is in the file
`Tactic.GCongr.Core`. -/

public section

/-- Natural quotients are monotone in the dividend and antitone in the nonzero divisor. -/
@[gcongr] theorem Nat.euclideanDiv_le_euclideanDiv {a b c d : Nat} {hb : b ≠ 0} {hd : d ≠ 0}
    (hac : a ≤ c) (hdb : d ≤ b) : Nat.euclideanDiv a b hb ≤ Nat.euclideanDiv c d hd := by
  apply (Nat.le_euclideanDiv_iff_mul_le hd).2
  calc
    d * Nat.euclideanDiv a b hb ≤ b * Nat.euclideanDiv a b hb := Nat.mul_le_mul_right _ hdb
    _ ≤ a := (Nat.le_euclideanDiv_iff_mul_le hb).1 (Nat.le_refl _)
    _ ≤ c := hac

/-- Taking natural quotients by the same nonzero divisor preserves order. -/
@[gcongr] theorem Nat.euclideanDiv_le_euclideanDiv_right {a b c : Nat} {hc : c ≠ 0} (hab : a ≤ b) :
    Nat.euclideanDiv a c hc ≤ Nat.euclideanDiv b c hc :=
  Nat.euclideanDiv_le_euclideanDiv hab (Nat.le_refl _)

namespace Mathlib.Tactic.GCongr

variable {a b c d : Prop}

/-- A version of `imp_imp_imp` that has an extra hypothesis `c` in the `b → d` hypothesis. -/
@[gcongr] lemma imp_mono (h₁ : c → a) (h₂ : c → b → d) : (a → b) → c → d :=
  fun h₃ hc => h₂ hc (h₃ (h₁ hc))

/-- A version of `And.imp` with an extra hypothesis `a` in the `b → d` hypothesis. -/
@[gcongr] lemma and_mono (h₁ : a → c) (h₂ : a → b → d) : (a ∧ b) → c ∧ d :=
  fun ⟨ha, hb⟩ => ⟨h₁ ha, h₂ ha hb⟩

attribute [gcongr] mt Or.imp forall_imp Exists.imp
  List.Sublist.append List.Sublist.reverse List.drop_sublist_drop_left List.Sublist.drop
  List.Perm.cons List.Perm.append List.Perm.map
  List.cons_subset_cons
  Nat.sub_le_sub_left Nat.sub_le_sub_right Nat.sub_lt_sub_left Nat.sub_lt_sub_right
  Nat.succ_le_succ

-- `Nat.pow_le_pow_right` has side condition `0 < n`, which `gcongr` discharges automatically via
-- `positivity`, unlike the `1 ≤ a` side condition of the more general `pow_le_pow_right₀`.
attribute [gcongr high] Nat.pow_le_pow_right


/-! We also use `assumption` to discharge side goals.
In a further downstream file, `positivity` will also be registered as a discharger.
From that point, `positivity` will be tried before `assumption` is: that is perfectly fine. -/
macro_rules | `(tactic| gcongr_discharger) => `(tactic| assumption)

/-!
We register `gcongr` with the `hint` tactic.
-/

register_hint 1000 gcongr

end Mathlib.Tactic.GCongr
