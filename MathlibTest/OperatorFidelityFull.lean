/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
import Mathlib
import Mathlib.Tactic.Linter.OperatorFidelity

/-!
# Mathlib package operator-fidelity gate

This target audits Mathlib's elaborated declarations. The legacy import mode loads private
declarations throughout the library. The proof report fails if its traversal is incomplete.
Use `scripts/operator_fidelity_packages.py` to audit the other maintained packages.
-/

set_option maxHeartbeats 0

#operator_fidelity with_proofs in Mathlib
