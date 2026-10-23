/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module
public import Mathlib.Basic.Real.Basic
public meta import Lean.Meta.SynthInstance
public meta import Lean.Elab.Command

public section

namespace InverseCauchy

open CauSeq

def initialZero : CauSeq ℚ abs :=
  ⟨fun n ↦ if n = 0 then 0 else 1, by
    intro ε hε
    refine ⟨1, fun j hj ↦ ?_⟩
    have hj0 : j ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_one.trans_le hj)
    simpa [hj0] using hε⟩

theorem initialZero_not_limZero : ¬LimZero initialZero := by
  intro h
  obtain ⟨n, hn⟩ := h 1 zero_lt_one
  have hlt := hn (n + 1) (Nat.le_succ n)
  simp [initialZero] at hlt

example : initialZero 0 = 0 := rfl

example (n : ℕ) : inv initialZero initialZero_not_limZero n ≠ 0 := by
  rw [inv_apply]
  exact Units.ne_zero _

example : inv initialZero initialZero_not_limZero 0 * initialZero 0 = 0 := by
  rw [show initialZero 0 = 0 from rfl, mul_zero]

example : inv initialZero initialZero_not_limZero * initialZero ≈ 1 :=
  inv_mul_cancel initialZero_not_limZero

example : initialZero * inv initialZero initialZero_not_limZero ≈ 1 :=
  mul_inv_cancel initialZero_not_limZero

example (f : CauSeq ℚ abs) (h₁ h₂ : ¬LimZero f) : inv f h₁ = inv f h₂ := rfl

example (f g : CauSeq ℚ abs) (hf : ¬LimZero f) (hg : ¬LimZero g) (hfg : f ≈ g) :
    Completion.mkUnit f hf = Completion.mkUnit g hg := Completion.mkUnit_eq hf hg hfg

example :
    (Completion.mkUnit initialZero initialZero_not_limZero : Completion.Cauchy (abs : ℚ → ℚ)) *
      ↑(Completion.mkUnit initialZero initialZero_not_limZero)⁻¹ = 1 :=
  (Completion.mkUnit initialZero initialZero_not_limZero).mul_inv

example (u : ℝˣ) :
    (↑u⁻¹ : ℝ).cauchy =
      (↑(Units.map Real.ringEquivCauchy.toMonoidHom u)⁻¹ : Completion.Cauchy (abs : ℚ → ℚ)) :=
  Real.cauchy_inv u

example {x : ℝ} (hx : x ≠ 0) : x * Checked.inv x = 1 :=
  Checked.mul_inv_cancel _ (GroupWithZero.isUnit_of_ne_zero hx)

example (u : ℝˣ) : u ^ (-1 : Int) = u⁻¹ := zpow_neg_one u

open Lean Meta in
run_meta do
  for cls in [``Inv, ``Div] do
    let type ← mkAppM cls #[mkConst ``Real]
    unless (← synthInstance? type).isNone do
      throwError "unexpected total real operation: {type}"
  let powerType ← mkAppM ``Pow #[mkConst ``Real, mkConst ``Int]
  unless (← synthInstance? powerType).isNone do
    throwError "unexpected total real integer power: {powerType}"

end InverseCauchy
