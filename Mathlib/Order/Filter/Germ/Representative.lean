/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module

public import Mathlib.Order.Filter.Germ.Basic

/-!
# Representatives of germs

A function `f : α → β` represents a germ `φ : Filter.Germ l β`, written `f ∈ φ`, when the germ of
`f` is `φ`. A germ is the class of its representatives modulo eventual equality along `l`: any two
representatives agree eventually along `l`, and a function that agrees eventually along `l` with a
representative is again one.

This is the interface for an object that its specification determines only up to eventual
equality, such as an almost-everywhere class: the germ is the canonical object, and a statement
about a particular function is a statement about one of its representatives.

## Main declarations

* `Filter.Germ.instMembership`: `f ∈ φ` means that the germ of `f` is `φ`.
* `Filter.Germ.eventuallyEq_of_mem`: two representatives of a germ agree eventually.
* `Filter.Germ.mem_iff_eventuallyEq`: given one representative, the representatives are exactly
  the functions that agree with it eventually.
-/

@[expose] public section

namespace Filter.Germ

variable {α β : Type*} {l : Filter α} {f g : α → β} {φ ψ : Germ l β}

/-- A function `f` represents the germ `φ`, written `f ∈ φ`, when the germ of `f` is `φ`. -/
instance instMembership : Membership (α → β) (Germ l β) where
  mem φ f := (f : Germ l β) = φ

theorem mem_def : f ∈ φ ↔ (f : Germ l β) = φ := Iff.rfl

@[simp]
theorem mem_coe : f ∈ (g : Germ l β) ↔ f =ᶠ[l] g := coe_eq

theorem coe_mem (f : α → β) : f ∈ (f : Germ l β) := rfl

theorem exists_mem (φ : Germ l β) : ∃ f : α → β, f ∈ φ :=
  φ.inductionOn fun f ↦ ⟨f, rfl⟩

theorem eventuallyEq_of_mem (hf : f ∈ φ) (hg : g ∈ φ) : f =ᶠ[l] g :=
  coe_eq.1 (hf.trans hg.symm)

theorem mem_of_eventuallyEq (hf : f ∈ φ) (h : f =ᶠ[l] g) : g ∈ φ :=
  (coe_eq.2 h.symm).trans hf

theorem mem_iff_eventuallyEq (hf : f ∈ φ) : g ∈ φ ↔ g =ᶠ[l] f :=
  ⟨fun hg ↦ eventuallyEq_of_mem hg hf, fun h ↦ mem_of_eventuallyEq hf h.symm⟩

theorem eq_of_mem (hφ : f ∈ φ) (hψ : f ∈ ψ) : φ = ψ :=
  hφ.symm.trans hψ

theorem eq_coe_of_mem (hf : f ∈ φ) : φ = f :=
  hf.symm

end Filter.Germ
