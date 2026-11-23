import Mathlib.Probability.Kernel.AEClass
import Mathlib.Probability.Kernel.Basic

/-!
# Almost-everywhere classes of kernels

These tests check that a kernel represents its class; that two kernels have the same class exactly
when they agree eventually along the filter; that every class has a representative and is
determined by its representatives; that a class keeps its representatives when it is restated along
an equal filter; that two kernels that differ on a set of positive measure lie in different classes,
while all kernels lie in one class along the null filter; and that only kernels are members.
-/

open MeasureTheory ProbabilityTheory Filter

variable {α β : Type*} [SigmaAlgebra α] [SigmaAlgebra β] {μ : Measure α} {κ η : Kernel α β}

example : κ ∈ Kernel.AEClass.mk (ae μ) κ := Kernel.AEClass.mem_mk _ κ

example : η ∈ Kernel.AEClass.mk (ae μ) κ ↔ ∀ᵐ a ∂μ, η a = κ a := Kernel.AEClass.mem_mk_iff

example : Kernel.AEClass.mk (ae μ) κ = Kernel.AEClass.mk (ae μ) η ↔ ∀ᵐ a ∂μ, κ a = η a :=
  Kernel.AEClass.mk_eq_mk_iff

example {c : Kernel.AEClass (ae μ) β} (hκ : κ ∈ c) (hη : η ∈ c) : ∀ᵐ a ∂μ, κ a = η a :=
  Kernel.AEClass.eventuallyEq_of_mem hκ hη

example {c : Kernel.AEClass (ae μ) β} (hκ : κ ∈ c) (h : ∀ᵐ a ∂μ, κ a = η a) : η ∈ c :=
  Kernel.AEClass.mem_of_eventuallyEq hκ h

example (c : Kernel.AEClass (ae μ) β) : ∃ κ : Kernel α β, κ ∈ c := c.exists_mem

example {c d : Kernel.AEClass (ae μ) β} (hc : κ ∈ c) (hd : κ ∈ d) : c = d :=
  Kernel.AEClass.eq_of_mem hc hd

example {c d : Kernel.AEClass (ae μ) β} (h : ∀ κ : Kernel α β, κ ∈ c ↔ κ ∈ d) : c = d :=
  Kernel.AEClass.ext h

-- Restating a class along an equal filter keeps its representatives.
example {ν : Measure α} (h : ae ν = ae μ) (c : Kernel.AEClass (ae μ) β) :
    κ ∈ c.copy h ↔ κ ∈ c :=
  Kernel.AEClass.mem_copy h

-- Two kernels that differ on a set of positive measure lie in different classes.
example : Kernel.AEClass.mk (ae (Measure.dirac (0 : ℕ))) (Kernel.const ℕ (Measure.dirac (0 : ℕ))) ≠
    Kernel.AEClass.mk (ae (Measure.dirac (0 : ℕ))) (Kernel.const ℕ (Measure.dirac (1 : ℕ))) := by
  rw [Ne, Kernel.AEClass.mk_eq_mk_iff, Filter.EventuallyEq, ae_dirac_eq, Filter.eventually_pure]
  intro h
  simpa [Kernel.const_apply] using congrArg (fun ν : Measure ℕ ↦ ν {0}) h

-- Along the null filter of the zero measure all kernels lie in one class.
example : Kernel.AEClass.mk (ae (0 : Measure α)) κ = Kernel.AEClass.mk (ae 0) η := by
  rw [Kernel.AEClass.mk_eq_mk_iff, ae_zero]
  exact Filter.eventually_bot

-- Only kernels are members: a function into measures is not elaborated as a representative.
/--
error: failed to synthesize instance of type class
  Membership (α → Measure β) (Kernel.AEClass (ae μ) β)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example (f : α → Measure β) (c : Kernel.AEClass (ae μ) β) : Prop := f ∈ c
