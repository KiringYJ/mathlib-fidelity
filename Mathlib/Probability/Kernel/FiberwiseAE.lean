/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module

public import Mathlib.Probability.Kernel.Defs

/-!
# The fiberwise almost-everywhere filter of a kernel

For a kernel `ν : Kernel α β`, `ProbabilityTheory.Kernel.fiberwiseAE ν` is the filter on `α × β`
of the properties that hold, for every `a : α`, at `(a, b)` for `ν a`-almost every `b`. Functions
on `α × β` that agree eventually along it are the functions that agree `ν a`-almost everywhere on
the fiber over each `a`. This is the equivalence up to which a disintegration of a kernel is
determined, so objects with that specification are germs along this filter.

## Main declarations

* `ProbabilityTheory.Kernel.fiberwiseAE ν`: the fiberwise almost-everywhere filter of `ν`.
* `ProbabilityTheory.Kernel.eventually_fiberwiseAE_iff`: a property holds eventually along
  `ν.fiberwiseAE` if and only if, for every `a`, it holds at `(a, b)` for `ν a`-almost every `b`.
-/

@[expose] public section

open MeasureTheory Filter

namespace ProbabilityTheory.Kernel

variable {α β γ : Type*} {mα : SigmaAlgebra α} {mβ : SigmaAlgebra β}

/-- For a kernel `ν : Kernel α β`, the filter on `α × β` of the properties that hold, for every
`a : α`, at `(a, b)` for `ν a`-almost every `b`. It is the supremum over `a` of the images of the
filters `ae (ν a)` under `Prod.mk a`. -/
def fiberwiseAE (ν : Kernel α β) : Filter (α × β) :=
  ⨆ a, (ae (ν a)).map (Prod.mk a)

variable {ν : Kernel α β}

theorem eventually_fiberwiseAE_iff {p : α × β → Prop} :
    (∀ᶠ x in ν.fiberwiseAE, p x) ↔ ∀ a, ∀ᵐ b ∂(ν a), p (a, b) := by
  simp [fiberwiseAE, eventually_iSup, eventually_map]

theorem eventuallyEq_fiberwiseAE_iff {f g : α × β → γ} :
    f =ᶠ[ν.fiberwiseAE] g ↔ ∀ a, ∀ᵐ b ∂(ν a), f (a, b) = g (a, b) :=
  eventually_fiberwiseAE_iff

end ProbabilityTheory.Kernel
