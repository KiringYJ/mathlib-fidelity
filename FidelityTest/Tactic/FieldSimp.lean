/-
Copyright (c) 2022 Jon Eugster. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Eugster, David Renshaw, Heather Macbeth, Michael Rothgang
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Field
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Test denominator evidence and relation preservation in `field_simp`. -/

set_option linter.unusedVariables false

-- Forming the original reciprocal requires evidence, even when the factors would cancel.
example (x : ℚ) : True := by
  fail_if_success have := (x / x : ℚ)
  fail_if_success have := (x⁻¹ : ℚ)
  trivial

-- The denominator itself certifies that both factors are units.
example {P : ℚ → Prop} {x y : ℚ} (hd : IsUnit (x * y))
    (h : P (Checked.div 1 y (IsUnit.mul_iff.mp hd).2)) :
    P (Checked.div x (x * y) hd) := by
  field_simp
  exact h

-- Elaboration can wrap a comparison in metadata. Preserve its explicitly supplied relation.
open Lean Meta Elab Tactic Mathlib.Tactic in
example {K : Type*} [Field K] (cmp : LE K) (a b : K) (h : @LE.le K cmp (a ^ 2) b) :
    @LE.le K cmp (a * a) b := by
  run_tac liftMetaTactic1 fun g ↦ do
    let t := Term.mkNoImplicitLambdaAnnotation (← g.getType)
    let r ← AtomM.run .reducible <| FieldSimp.reduceProp (fun _ ↦ failure) t
    g.replaceTargetEq r.expr (← r.getProof)
  exact h

-- An unknown-sign factor cannot be canceled from an inequality.
example (x y c : ℝ) (hc : c ≠ 0) (h : x * c ≤ y * c) : x / c ≤ y / c := by
  field_simp
  simpa only [mul_comm c] using h

-- The zero branch cannot synthesize the original denominator certificate.
example (x : ℚ) (hx : x = 0) : True := by
  fail_if_success have := (x / x : ℚ)
  trivial
