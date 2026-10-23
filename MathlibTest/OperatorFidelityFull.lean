/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module

public import Mathlib
public import Mathlib.Tactic.Linter.OperatorFidelity

/-!
# Mathlib package operator-fidelity gate

This target audits the declarations owned by the Mathlib package after importing `Mathlib`.
It does not audit declarations owned by MathlibTest, Archive, Counterexamples, or Wanted.
The semantic command fails closed; the proof command reports without failing.
-/

#operator_fidelity in Mathlib
#operator_fidelity_proofs in Mathlib
