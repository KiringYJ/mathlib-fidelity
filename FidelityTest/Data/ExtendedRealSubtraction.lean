/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
import Mathlib.Data.EReal.Operations
import Mathlib.Basic.ENNReal.Inv

open scoped ENNReal NNReal

noncomputable section

/--
error: failed to synthesize
  Sub EReal

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth Sub EReal

/--
error: failed to synthesize
  HSub EReal EReal EReal

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth HSub EReal EReal EReal

/--
error: failed to synthesize
  Sub ℝ≥0∞

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth Sub ℝ≥0∞

/--
error: failed to synthesize
  HSub ℝ≥0∞ ℝ≥0∞ ℝ≥0∞

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth HSub ℝ≥0∞ ℝ≥0∞ ℝ≥0∞

/--
error: could not synthesize default value for parameter '_h' using tactics
---
error: extended-real subtraction excludes equal infinities
⊢ ⊤.SubDomain ⊤
-/
#guard_msgs in
example : EReal := (⊤ : EReal) - ⊤

/--
error: could not synthesize default value for parameter '_h' using tactics
---
error: extended-real subtraction excludes equal infinities
⊢ ⊥.SubDomain ⊥
-/
#guard_msgs in
example : EReal := (⊥ : EReal) - ⊥

/-- error: no subtraction notation on ENNReal; use ENNReal.monus or cast explicitly to EReal -/
#guard_msgs in
example (a b : ℝ≥0∞) : ℝ≥0∞ := a - b

/-- error: no subtraction notation on ENNReal; use ENNReal.monus or cast explicitly to EReal -/
#guard_msgs in
example (a b : ℝ≥0∞) : EReal := a - b

/-- error: no subtraction notation on ENNReal; use ENNReal.monus or cast explicitly to EReal -/
#guard_msgs in
example (a : EReal) (b : ℝ≥0∞) : EReal := a - b

/-- error: no subtraction notation on ENNReal; use ENNReal.monus or cast explicitly to EReal -/
#guard_msgs in
example (a b : ℝ≥0) : ℝ≥0∞ := (a : ℝ≥0∞) - (b : ℝ≥0∞)

section

private def ENNRealAlias := ENNReal

local instance : Coe ENNRealAlias EReal := ⟨ENNReal.toEReal⟩

/-- error: no subtraction notation on ENNReal; use ENNReal.monus or cast explicitly to EReal -/
#guard_msgs in
example (a b : ENNRealAlias) : EReal := a - b

end

example : (⊥ : EReal) - ⊤ = ⊥ := rfl
example : (⊤ : EReal) - ⊥ = ⊤ := rfl

example (a b : ℝ) (h : a < b) : (a : EReal) - (b : EReal) < 0 :=
  (EReal.sub_neg (by simp [EReal.SubDomain])).2 (by exact_mod_cast h)

example (u v : ℝ≥0∞) (hv : v ≠ ⊤) (huv : v ≤ u) :
    (ENNReal.monus u v : EReal) = (u : EReal) - (v : EReal) :=
  ENNReal.toEReal_sub hv huv

example (u v : ℝ≥0∞) : EReal.SubDomain u.toEReal v.toEReal ↔ u ≠ ⊤ ∨ v ≠ ⊤ :=
  EReal.subDomain_coe_ennreal u v

example (a b q : ℝ≥0∞) : ENNReal.monus a b ≤ q ↔ a ≤ q + b :=
  ENNReal.monus_le_iff

example (a b : ℝ≥0∞) : ENNReal.monus a b = sInf {q | a ≤ q + b} :=
  ENNReal.monus_eq_sInf

example : ENNReal.monus ∞ ∞ = 0 := ENNReal.monus_top

example (a b : WithTop ℝ≥0) : a - b = WithTop.sub a b := rfl

example (z : Int) : z - 1 = Int.sub z 1 := rfl

example (a : EReal) (b : ℝ) : a - b = EReal.sub a (b : EReal) := rfl

example (a : EReal) (P : EReal → Prop) (h : ∀ b, b = a → P b) : ∃ b, P b := by
  specialize h (a - 0) (EReal.sub_zero a)
  exact ⟨_, h⟩

section

variable (a b : EReal) (h : EReal.SubDomain a b)

/-- info: a - b : EReal -/
#guard_msgs in
#check EReal.sub a b h

end

section

variable (a b : EReal) (domain : PLift (EReal.SubDomain a b))

/-- info: a.sub b ⋯ : EReal -/
#guard_msgs in
#check EReal.sub a b domain.down

end
