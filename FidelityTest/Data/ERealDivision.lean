/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
import Mathlib.Data.EReal.Inv

open scoped ENNReal

example (a b : EReal) (h : EReal.DivDomain a b) : a / b = EReal.div a b h := rfl

example (a b : ℝ) (hb : IsUnit b) :
    (↑(a / b) : EReal) = (a : EReal) / (b : EReal) :=
  EReal.coe_div a b

example (a b : EReal) (hb : IsUnit b) : a / b = Checked.div a b hb :=
  EReal.div_eq_checked_div a b hb

example (a b : EReal) (ha : IsUnit a) (hb : IsUnit b) : IsUnit (a / b) := by
  checked_unit

example (a b : EReal) (hb : b ≠ 0)
    (hfin : (a ≠ ⊤ ∧ a ≠ ⊥) ∨ (b ≠ ⊤ ∧ b ≠ ⊥)) :
    a / b = EReal.div a b ⟨hb, hfin⟩ := rfl

example (a : ℝ) : (a : EReal) / (⊤ : EReal) = 0 := rfl
example (a : ℝ) : (a : EReal) / (⊥ : EReal) = 0 := rfl
example : (0 : EReal) / (⊤ : EReal) = 0 := rfl
example : (2 : EReal) / (⊥ : EReal) = 0 := rfl

example (b : EReal) (hb : 0 < b) (hfin : b ≠ ⊤) : (⊤ : EReal) / b = ⊤ :=
  EReal.top_div_of_pos_ne_top hb hfin

example (b : EReal) (hb : b < 0) (hfin : b ≠ ⊥) : (⊥ : EReal) / b = ⊤ :=
  EReal.bot_div_of_neg_ne_bot hb hfin

example (a b : EReal) (ha : 0 ≤ a) (hb : 0 ≤ b) (h : EReal.DivDomain a b) :
    0 ≤ a / b := by positivity

example (a b : ℝ≥0∞) :
    EReal.DivDomain (a : EReal) (b : EReal) ↔ b ≠ 0 ∧ (a ≠ ⊤ ∨ b ≠ ⊤) :=
  EReal.divDomain_coe_ennreal

noncomputable section

/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: extended-real division requires a nonzero denominator and a finite operand
a b : EReal
⊢ a.DivDomain b
-/
#guard_msgs in
example (a b : EReal) : EReal := a / b

/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: extended-real division requires a nonzero denominator and a finite operand
a : EReal
⊢ a.DivDomain 0
-/
#guard_msgs in
example (a : EReal) : EReal := a / (0 : EReal)

/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: extended-real division requires a nonzero denominator and a finite operand
⊢ ⊤.DivDomain ⊤
-/
#guard_msgs in
example : EReal := (⊤ : EReal) / (⊤ : EReal)

/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: extended-real division requires a nonzero denominator and a finite operand
⊢ ⊤.DivDomain ⊥
-/
#guard_msgs in
example : EReal := (⊤ : EReal) / (⊥ : EReal)

/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: extended-real division requires a nonzero denominator and a finite operand
⊢ ⊥.DivDomain ⊤
-/
#guard_msgs in
example : EReal := (⊥ : EReal) / (⊤ : EReal)

/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: extended-real division requires a nonzero denominator and a finite operand
⊢ ⊥.DivDomain ⊥
-/
#guard_msgs in
example : EReal := (⊥ : EReal) / (⊥ : EReal)

/--
error: failed to synthesize
  Div EReal

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth Div EReal

/--
error: failed to synthesize
  HDiv EReal EReal EReal

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth HDiv EReal EReal EReal

section

variable (a b : EReal) (h : EReal.DivDomain a b)

/-- info: a / b : EReal -/
#guard_msgs in
#check EReal.div a b h

end

section

variable (a b : EReal) (evidence : Unit → EReal.DivDomain a b)

/-- info: a.div b ⋯ : EReal -/
#guard_msgs in
#check EReal.div a b (evidence ())

end

end
