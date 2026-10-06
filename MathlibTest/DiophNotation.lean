import Mathlib.NumberTheory.Dioph

/-!
# The Diophantine closure notation is file-local

`Mathlib/NumberTheory/Dioph.lean` writes its constructions with file-local symbolic forms of the
closure lemmas such as `D∧`; they are not exported, so the named lemmas are the interface.
-/

open scoped Dioph

variable {α : Type} {S S' : Set (α → ℕ)}

example (d : Dioph S) (d' : Dioph S') : Dioph (S ∩ S') := d.inter d'

example (d : Dioph S) (d' : Dioph S') : Dioph (S ∪ S') := d.union d'

/--
error: Function expected at
  d
but this term has type
  Dioph S

Note: Expected a function because this term is being applied to the argument
  D
-/
#guard_msgs in
example (d : Dioph S) (d' : Dioph S') : Dioph (S ∩ S') := d D∧ d'
