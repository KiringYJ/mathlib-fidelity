import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.FiberwiseAE

/-!
# The fiberwise almost-everywhere filter of a kernel

These tests check that a property holds eventually along the fiberwise almost-everywhere filter of
a kernel exactly when it holds almost everywhere on every fiber, and that a failure on a set of
positive measure in a single fiber is detected.
-/

open MeasureTheory ProbabilityTheory Filter

variable {α β : Type*} [SigmaAlgebra α] [SigmaAlgebra β] {ν : Kernel α β}

example {p : α × β → Prop} : (∀ᶠ x in ν.fiberwiseAE, p x) ↔ ∀ a, ∀ᵐ b ∂(ν a), p (a, b) :=
  Kernel.eventually_fiberwiseAE_iff

example {f g : α × β → ℝ} :
    f =ᶠ[ν.fiberwiseAE] g ↔ ∀ a, ∀ᵐ b ∂(ν a), f (a, b) = g (a, b) :=
  Kernel.eventuallyEq_fiberwiseAE_iff

-- For the zero kernel every property holds eventually.
example (p : α × β → Prop) : ∀ᶠ x in (0 : Kernel α β).fiberwiseAE, p x :=
  Kernel.eventually_fiberwiseAE_iff.2 fun a ↦ by simp

/-- The kernel on `Bool` with value `dirac a` at `a`. -/
noncomputable abbrev diagKernel : Kernel Bool Bool := Kernel.deterministic id measurable_id

-- A property that holds on the diagonal holds eventually, since each fiber `{a} × Bool` carries
-- the point mass at `(a, a)`.
example : ∀ᶠ x in diagKernel.fiberwiseAE, x.1 = x.2 := by
  refine Kernel.eventually_fiberwiseAE_iff.2 fun a ↦ ?_
  rw [Kernel.deterministic_apply, ae_dirac_eq, Filter.eventually_pure]
  rfl

-- A property that fails at the atom of the fiber over `true` does not hold eventually, although it
-- holds on the whole fiber over `false`.
example : ¬ ∀ᶠ x in diagKernel.fiberwiseAE, x ≠ (true, true) := by
  rw [Kernel.eventually_fiberwiseAE_iff]
  intro h
  have h_true := h true
  rw [Kernel.deterministic_apply, ae_dirac_eq, Filter.eventually_pure] at h_true
  exact h_true rfl
