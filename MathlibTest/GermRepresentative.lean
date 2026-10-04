import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Germ.Representative

/-!
# Representatives of germs

These tests check that a function represents its own germ, that the representatives of a germ are
exactly the functions that agree eventually with one of them, and that germs with a common
representative are equal.
-/

open Filter

variable {α β : Type*} {l : Filter α} {f g : α → β} {φ ψ : l.Germ β}

example : f ∈ (f : l.Germ β) := Germ.coe_mem f

example : g ∈ (f : l.Germ β) ↔ g =ᶠ[l] f := Germ.mem_coe

example (hf : f ∈ φ) (hg : g ∈ φ) : f =ᶠ[l] g := Germ.eventuallyEq_of_mem hf hg

example (hf : f ∈ φ) (h : f =ᶠ[l] g) : g ∈ φ := Germ.mem_of_eventuallyEq hf h

example (hf : f ∈ φ) : g ∈ φ ↔ g =ᶠ[l] f := Germ.mem_iff_eventuallyEq hf

example (hφ : f ∈ φ) (hψ : f ∈ ψ) : φ = ψ := Germ.eq_of_mem hφ hψ

example (hf : f ∈ φ) : φ = f := Germ.eq_coe_of_mem hf

example : ∃ f : α → β, f ∈ φ := φ.exists_mem

-- Along `⊤`, eventual equality is equality, so `f` is the only representative of its germ.
example (f g : ℕ → ℕ) (h : g ∈ ((f : (⊤ : Filter ℕ).Germ ℕ))) : g = f :=
  funext (Filter.eventually_top.1 (Germ.mem_coe.1 h))

-- Along `atTop`, a function that differs from `f` only at `0` represents the germ of `f`, while
-- one that differs at every point does not.
example : (fun n : ℕ ↦ if n = 0 then 1 else n) ∈
    ((fun n : ℕ ↦ n : ℕ → ℕ) : (atTop : Filter ℕ).Germ ℕ) := by
  rw [Germ.mem_coe]
  filter_upwards [eventually_ge_atTop 1] with n hn
  simp [Nat.one_le_iff_ne_zero.1 hn]

example : (fun n : ℕ ↦ n + 1) ∉ ((fun n : ℕ ↦ n : ℕ → ℕ) : (atTop : Filter ℕ).Germ ℕ) := by
  rw [Germ.mem_coe]
  intro h
  obtain ⟨n, hn⟩ := h.exists
  simp at hn
