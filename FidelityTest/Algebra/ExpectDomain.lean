/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Combinatorics.Additive.DoublingConst

/-! Exact domains for finite averages, density, and doubling constants. -/

open Finset
open scoped BigOperators

example {α : Type*} (s : Finset α) (hs : s.Nonempty) (a : ℚ≥0) :
    Finset.expect s (fun _ ↦ a) hs = a := Finset.expect_const hs a

example {α : Type*} [Fintype α] [Nonempty α] : (Finset.univ : Finset α).dens = 1 :=
  Finset.dens_univ

example : (∅ : Finset (Fin 1)).dens = 0 := Finset.dens_empty

/--
error: could not synthesize default value for parameter 'hs' using tactics
---
error: finite average requires a proof that the index set is nonempty
⊢ ∅.Nonempty
-/
#guard_msgs in
example : ℚ≥0 := Finset.expect (∅ : Finset ℕ) (fun _ ↦ (1 : ℚ≥0))

/--
error: failed to synthesize instance of type class
  Nonempty Empty

Hint: Adding the command `deriving instance Nonempty for Empty` may allow Lean to derive the missing instance.
-/
#guard_msgs in
example : ℚ≥0 := Finset.dens (∅ : Finset Empty)

example : Finset.addConst ({0} : Finset ℤ) ∅ (singleton_nonempty 0) = 0 :=
  Finset.addConst_empty_right _ (singleton_nonempty 0)

/--
error: could not synthesize default value for parameter 'hA' using tactics
---
error: doubling and difference constants require a nonempty left set
⊢ ∅.Nonempty
-/
#guard_msgs in
example : ℚ≥0 := Finset.addConst (∅ : Finset ℤ) ∅
