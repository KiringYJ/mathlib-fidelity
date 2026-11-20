import Mathlib

/-
This file checks that every declaration and import that have been flagged with
`assert_not_exists` or `assert_not_imported` is present in the environment once
all of `Mathlib` is available.

The expected diagnostic records the retirement of the unchecked inverse `Nonneg.inv`.
-/

/--
warning: ❌️ 'Nonneg.inv' (declaration) asserted in 'Mathlib.Algebra.Module.Basic'.
---
✅️ means the declaration or import exists.
❌️ means the declaration or import does not exist.
-/
#guard_msgs in
#check_assertions!
