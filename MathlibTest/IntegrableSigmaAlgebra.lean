import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Integrability with respect to an explicit σ-algebra

The σ-algebra of `MeasureTheory.Integrable` is passed as the named argument `mα`; there is no
bracket notation `Integrable[m]`, which would compete with element lookup.
-/

open MeasureTheory

variable {α : Type*} (m : SigmaAlgebra α) (μ : @Measure α m) (f : α → ℝ)

example : Integrable (mα := m) f μ ↔ AEStronglyMeasurable f μ ∧ HasFiniteIntegral f μ := Iff.rfl

/--
error: failed to synthesize instance of type class
  GetElem ((?_ → ?_) → Prop) (SigmaAlgebra α) ?_ ?_

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
---
error: could not synthesize default value for parameter 'μ' using tactics
---
error: unsolved goals
α : Type u_1
m : SigmaAlgebra α
μ : Measure α
f : α → ℝ
f✝ : ?_ → ?_
⊢ Measure ?_
---
error: failed to prove index is valid, possible solutions:
  - Use `have`-expressions to prove the index is valid
  - Use `a[i]!` notation instead, runtime check is performed, and 'Panic' error message is produced if index is not valid
  - Use `a[i]?` notation instead, result is an `Option` type
  - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
α : Type u_1
m : SigmaAlgebra α
μ : Measure α
f : α → ℝ
⊢ ?_ (fun f => Integrable f ?_) m
-/
#guard_msgs in
example : Prop := Integrable[m] f μ
