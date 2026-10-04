/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module

public import Mathlib.Probability.Kernel.Defs

/-!
# Almost-everywhere classes of kernels

`ProbabilityTheory.Kernel.AEClass l β` is the type of kernels from `α` to `β` modulo eventual
equality along a filter `l` on `α`, the kernels being viewed as functions `α → Measure β`. A kernel
`κ` represents a class `c`, written `κ ∈ c`, when the class of `κ` is `c`; every class is the class
of a kernel.

A kernel that a specification determines only up to null sets is canonically such a class, not a
chosen representative. For a measure `μ`, the filter `ae μ` identifies the kernels that agree
`μ`-almost everywhere. For a kernel `ν : Kernel α β`, the filter `ν.fiberwiseAE` on `α × β`
identifies the kernels that agree `ν a`-almost everywhere on the fiber over every `a`.

## Main definitions

* `ProbabilityTheory.Kernel.AEClass l β`: kernels modulo eventual equality along `l`.
* `ProbabilityTheory.Kernel.AEClass.mk l κ`: the class of the kernel `κ`.
-/

@[expose] public section

open MeasureTheory Filter

namespace ProbabilityTheory.Kernel

/-- Eventual equality along `l` of kernels, viewed as functions `α → Measure β`. -/
def aeClassSetoid {α : Type*} (l : Filter α) (β : Type*) [SigmaAlgebra α] [SigmaAlgebra β] :
    Setoid (Kernel α β) where
  r κ η := ⇑κ =ᶠ[l] ⇑η
  iseqv := ⟨fun _ ↦ EventuallyEq.rfl, EventuallyEq.symm, EventuallyEq.trans⟩

/-- Kernels from `α` to `β` modulo eventual equality along a filter `l` on `α`, the kernels being
viewed as functions `α → Measure β`. A kernel `κ` represents a class `c`, written `κ ∈ c`, when the
class of `κ` is `c`. -/
def AEClass {α : Type*} (l : Filter α) (β : Type*) [SigmaAlgebra α] [SigmaAlgebra β] : Type _ :=
  Quotient (aeClassSetoid l β)

namespace AEClass

variable {α β : Type*} {mα : SigmaAlgebra α} {mβ : SigmaAlgebra β} {l : Filter α}
  {κ η : Kernel α β} {c d : AEClass l β}

/-- The class of the kernel `κ` modulo eventual equality along `l`. -/
def mk (l : Filter α) (κ : Kernel α β) : AEClass l β :=
  Quotient.mk (aeClassSetoid l β) κ

/-- A kernel `κ` represents the class `c`, written `κ ∈ c`, when the class of `κ` is `c`. -/
instance instMembership : Membership (Kernel α β) (AEClass l β) where
  mem c κ := mk l κ = c

theorem mem_def : κ ∈ c ↔ mk l κ = c := Iff.rfl

theorem mem_mk (l : Filter α) (κ : Kernel α β) : κ ∈ mk l κ := rfl

theorem mk_eq_mk_iff : mk l κ = mk l η ↔ ⇑κ =ᶠ[l] ⇑η :=
  Quotient.eq (r := aeClassSetoid l β)

theorem mem_mk_iff : η ∈ mk l κ ↔ ⇑η =ᶠ[l] ⇑κ :=
  mk_eq_mk_iff

theorem exists_mem (c : AEClass l β) : ∃ κ : Kernel α β, κ ∈ c :=
  Quotient.exists_rep c

theorem eventuallyEq_of_mem (hκ : κ ∈ c) (hη : η ∈ c) : ⇑κ =ᶠ[l] ⇑η :=
  mk_eq_mk_iff.1 (hκ.trans hη.symm)

theorem mem_of_eventuallyEq (hκ : κ ∈ c) (h : ⇑κ =ᶠ[l] ⇑η) : η ∈ c :=
  (mk_eq_mk_iff.2 h.symm).trans hκ

theorem mem_iff_eventuallyEq (hκ : κ ∈ c) : η ∈ c ↔ ⇑η =ᶠ[l] ⇑κ :=
  ⟨fun hη ↦ eventuallyEq_of_mem hη hκ, fun h ↦ mem_of_eventuallyEq hκ h.symm⟩

theorem eq_of_mem (hc : κ ∈ c) (hd : κ ∈ d) : c = d :=
  hc.symm.trans hd

theorem eq_mk_of_mem (hκ : κ ∈ c) : c = mk l κ :=
  hκ.symm

/-- Two classes are equal when they have the same representatives. -/
@[ext]
theorem ext (h : ∀ κ : Kernel α β, κ ∈ c ↔ κ ∈ d) : c = d :=
  let ⟨κ, hκ⟩ := exists_mem c
  eq_of_mem hκ ((h κ).1 hκ)

/-- The class `c` along a filter `l` as a class along an equal filter `l'`. It has the same
representatives as `c` (`ProbabilityTheory.Kernel.AEClass.mem_copy`); it serves to state a class
along the filter in which it is naturally described, such as `ae (μ.map X)` instead of
`ae (μ.map (fun a ↦ (X a, Y a))).fst`. -/
def copy (c : AEClass l β) {l' : Filter α} (h : l' = l) : AEClass l' β :=
  h ▸ c

@[simp]
theorem mem_copy {l' : Filter α} (h : l' = l) : κ ∈ c.copy h ↔ κ ∈ c := by
  subst h
  rfl

end AEClass

end ProbabilityTheory.Kernel
