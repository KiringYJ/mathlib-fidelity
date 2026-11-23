import Mathlib.Probability.Notation

/-!
# Element lookup is not reread as an expectation

The expectation of `X` under a measure `P` is the integral `∫ ω, X ω ∂P`, which names `P`; the
notation `𝔼[X]` is reserved for the ambient measure `volume`. No notation reads an adjacent
`P[X]` as an integral, so with `ProbabilityTheory` open, a list lookup whose index cannot be
shown valid is reported as a lookup error, and `P[X]` for a measure `P` is an element lookup.
-/

open MeasureTheory ProbabilityTheory

/-! An invalid lookup is diagnosed as a lookup error. -/

/--
error: failed to prove index is valid, possible solutions:
  - Use `have`-expressions to prove the index is valid
  - Use `a[i]!` notation instead, runtime check is performed, and 'Panic' error message is produced if index is not valid
  - Use `a[i]?` notation instead, result is an `Option` type
  - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
l : List ℕ
i : ℕ
⊢ i < l.length
-/
#guard_msgs in
example (l : List ℕ) (i : ℕ) : ℕ := l[i]

/-! A measure followed by a bracket is an element lookup, which a measure does not support. -/

/--
error: failed to synthesize instance of type class
  GetElem (Measure Ω) (Ω → ℝ) ?_ ?_

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example {Ω : Type*} [SigmaAlgebra Ω] (P : Measure Ω) (X : Ω → ℝ) : ℝ := P[X]

/-! The expectation under a named measure, and under `volume`. -/

example {Ω : Type*} [SigmaAlgebra Ω] (P : Measure Ω) (X : Ω → ℝ) :
    ∫ ω, X ω ∂P = integral P X :=
  rfl

example {Ω : Type*} [MeasureSpace Ω] (X : Ω → ℝ) : 𝔼[X] = ∫ ω, X ω ∂volume :=
  rfl
