/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module

public meta import Lean.Elab.Declaration
public import Lean.Elab.Term
public meta import Lean.Elab.BuiltinCommand
public meta import Lean.Elab.BuiltinEvalCommand
public meta import Lean.Elab.Tactic.Guard
import Mathlib.Tactic.Linter.Header

/-!
# Instance inference boundary for retired rational operations

Core rational numbers remain available, but their total inverse, division, integer powers,
and totalized Grind field instance are not implicit mathematical operations in this library.

Instance-attribute erasures do not survive imports. These exported command elaborators apply
the same selective erasure in each importing module before delegating directly to Lean's
original elaborator. No declaration or kernel object in the official toolchain is modified.

This is an instance-inference boundary for the covered standard commands, not an all-source
semantic enforcement mechanism. Explicit references to retired constants and custom command
elaborators that directly elaborate terms or add declarations require a separate dependency audit.
-/

public meta section

namespace Mathlib.OperatorPolicy

open Lean Elab Command

/-- Remove only the core rational instances implementing the retired operations. -/
def suppressRetiredInstances : CommandElabM Unit := do
  modifyEnv fun env => Meta.instanceExtension.modifyState env fun state =>
    #[`Rat.instInv, `Rat.instDiv, `Rat.instPowInt, `Lean.Grind.instFieldRat].foldl
      (fun state name => state.eraseCore name) state

/-- Elaborate a declaration with the retired rational instances removed. -/
@[command_elab Lean.Parser.Command.declaration, builtin_incremental]
def elabDeclaration : CommandElab := fun stx => do
  suppressRetiredInstances
  Lean.Elab.Command.elabDeclaration stx

/-- Apply the retired-instance policy before elaborating a mutual block. -/
@[command_elab Lean.Parser.Command.mutual, builtin_incremental]
def elabMutual : CommandElab := fun stx => do
  suppressRetiredInstances
  Lean.Elab.Command.elabMutual stx

/-- Run `#synth` in the instance environment with retired rational instances removed. -/
@[command_elab Lean.Parser.Command.synth]
def elabSynth : CommandElab := fun stx => do
  suppressRetiredInstances
  Lean.Elab.Command.elabSynth stx

/-- Apply the retired-instance policy before elaborating the term in `#check`. -/
@[command_elab Lean.Parser.Command.check]
def elabCheck : CommandElab := fun stx => do
  suppressRetiredInstances
  Lean.Elab.Command.elabCheck stx

/-- Apply the retired-instance policy before checking the expected failure of a term. -/
@[command_elab Lean.Parser.Command.check_failure]
def elabCheckFailure : CommandElab := fun stx => do
  suppressRetiredInstances
  Lean.Elab.Command.elabCheckFailure stx

/-- Elaborate the term in `#eval` after removing retired rational instances. -/
@[command_elab Lean.Parser.Command.eval]
def elabEval : CommandElab := fun stx => do
  suppressRetiredInstances
  Lean.Elab.Command.elabEval stx

/-- Elaborate the term in `#eval!` under the retired-instance policy. -/
@[command_elab Lean.Parser.Command.evalBang]
def elabEvalBang : CommandElab := fun stx => do
  suppressRetiredInstances
  Lean.Elab.Command.elabEvalBang stx

/-- Apply the retired-instance policy before elaborating a `run_cmd` action. -/
@[command_elab Lean.runCmd]
def elabRunCmd : CommandElab := fun stx => do
  suppressRetiredInstances
  Lean.Elab.Command.elabRunCmd stx

/-- Apply the retired-instance policy before elaborating a `run_elab` action. -/
@[command_elab Lean.runElab]
def elabRunElab : CommandElab := fun stx => do
  suppressRetiredInstances
  Lean.Elab.Command.elabRunElab stx

/-- Apply the retired-instance policy before elaborating a `run_meta` action. -/
@[command_elab Lean.runMeta]
def elabRunMeta : CommandElab := fun stx => do
  suppressRetiredInstances
  Lean.Elab.Command.elabRunMeta stx

/-- Elaborate the binders of a `variable` command with the retired rational instances removed. -/
@[command_elab Lean.Parser.Command.variable]
def elabVariable : CommandElab := fun stx => do
  suppressRetiredInstances
  Lean.Elab.Command.elabVariable stx

/-- Apply the retired-instance policy before elaborating the term to reduce. -/
@[command_elab Lean.reduceCmd]
def elabReduce : CommandElab := fun stx => do
  suppressRetiredInstances
  Lean.Elab.Command.elabReduce stx

/-- Apply the retired-instance policy before elaborating an initialization declaration. -/
@[command_elab Lean.Parser.Command.initialize]
def elabInitialize : CommandElab := fun stx => do
  suppressRetiredInstances
  Lean.Elab.Command.elabInitialize stx

/-- Elaborate the condition tested by `#guard` under the retired-instance policy. -/
@[command_elab Lean.Parser.Command.guardCmd]
def elabGuard : CommandElab := fun stx => do
  suppressRetiredInstances
  Lean.Elab.Tactic.GuardExpr.evalGuardCmd stx

/-- Elaborate the expressions compared by `#guard_expr` under the retired-instance policy. -/
@[command_elab Lean.Parser.Command.guardExprCmd]
def elabGuardExpr : CommandElab := fun stx => do
  suppressRetiredInstances
  Lean.Elab.Tactic.GuardExpr.evalGuardExprCmd stx

end Mathlib.OperatorPolicy
