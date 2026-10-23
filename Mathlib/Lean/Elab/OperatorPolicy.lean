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

@[command_elab Lean.Parser.Command.declaration, builtin_incremental]
def elabDeclaration : CommandElab := fun stx => do
  suppressRetiredInstances
  Lean.Elab.Command.elabDeclaration stx

@[command_elab Lean.Parser.Command.mutual, builtin_incremental]
def elabMutual : CommandElab := fun stx => do
  suppressRetiredInstances
  Lean.Elab.Command.elabMutual stx

@[command_elab Lean.Parser.Command.synth]
def elabSynth : CommandElab := fun stx => do
  suppressRetiredInstances
  Lean.Elab.Command.elabSynth stx

@[command_elab Lean.Parser.Command.check]
def elabCheck : CommandElab := fun stx => do
  suppressRetiredInstances
  Lean.Elab.Command.elabCheck stx

@[command_elab Lean.Parser.Command.check_failure]
def elabCheckFailure : CommandElab := fun stx => do
  suppressRetiredInstances
  Lean.Elab.Command.elabCheckFailure stx

@[command_elab Lean.Parser.Command.eval]
def elabEval : CommandElab := fun stx => do
  suppressRetiredInstances
  Lean.Elab.Command.elabEval stx

@[command_elab Lean.Parser.Command.evalBang]
def elabEvalBang : CommandElab := fun stx => do
  suppressRetiredInstances
  Lean.Elab.Command.elabEvalBang stx

@[command_elab Lean.runCmd]
def elabRunCmd : CommandElab := fun stx => do
  suppressRetiredInstances
  Lean.Elab.Command.elabRunCmd stx

@[command_elab Lean.runElab]
def elabRunElab : CommandElab := fun stx => do
  suppressRetiredInstances
  Lean.Elab.Command.elabRunElab stx

@[command_elab Lean.runMeta]
def elabRunMeta : CommandElab := fun stx => do
  suppressRetiredInstances
  Lean.Elab.Command.elabRunMeta stx

@[command_elab Lean.Parser.Command.variable]
def elabVariable : CommandElab := fun stx => do
  suppressRetiredInstances
  Lean.Elab.Command.elabVariable stx

@[command_elab Lean.reduceCmd]
def elabReduce : CommandElab := fun stx => do
  suppressRetiredInstances
  Lean.Elab.Command.elabReduce stx

@[command_elab Lean.Parser.Command.initialize]
def elabInitialize : CommandElab := fun stx => do
  suppressRetiredInstances
  Lean.Elab.Command.elabInitialize stx

@[command_elab Lean.Parser.Command.guardCmd]
def elabGuard : CommandElab := fun stx => do
  suppressRetiredInstances
  Lean.Elab.Tactic.GuardExpr.evalGuardCmd stx

@[command_elab Lean.Parser.Command.guardExprCmd]
def elabGuardExpr : CommandElab := fun stx => do
  suppressRetiredInstances
  Lean.Elab.Tactic.GuardExpr.evalGuardExprCmd stx

end Mathlib.OperatorPolicy
