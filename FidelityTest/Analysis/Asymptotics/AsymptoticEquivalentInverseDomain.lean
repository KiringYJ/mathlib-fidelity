/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

open Asymptotics Filter
open scoped Topology

variable {α : Type*} {l : Filter α} {u v : α → ℝ}

example (h : u ~[l] v) :
    (fun x : {x // u x ≠ 0 ∧ v x ≠ 0} ↦ Checked.inv (u x) x.2.1.isUnit)
      ~[comap Subtype.val l]
    (fun x : {x // u x ≠ 0 ∧ v x ≠ 0} ↦ Checked.inv (v x) x.2.2.isUnit) :=
  (h.comp_tendsto tendsto_comap).inv

example (h : u ~[l] v) (f g : α → ℝ) (hfg : f ~[l] g) :
    (fun x : {x // u x ≠ 0 ∧ v x ≠ 0} ↦ Checked.div (f x) (u x) x.2.1.isUnit)
      ~[comap Subtype.val l]
    (fun x : {x // u x ≠ 0 ∧ v x ≠ 0} ↦ Checked.div (g x) (v x) x.2.2.isUnit) :=
  (hfg.comp_tendsto tendsto_comap).div (h.comp_tendsto tendsto_comap)

example (h : u ~[l] v) :
    (fun x ↦ u x ^ (0 : ℤ)) ~[l] (fun x ↦ v x ^ (0 : ℤ)) := h.zpow 0

example (h : u ~[l] v) :
    (fun x : {x // u x ≠ 0 ∧ v x ≠ 0} ↦
      Checked.zpow (u x) (-2) (fun _ ↦ x.2.1.isUnit)) ~[comap Subtype.val l]
    (fun x : {x // u x ≠ 0 ∧ v x ≠ 0} ↦
      Checked.zpow (v x) (-2) (fun _ ↦ x.2.2.isUnit)) :=
  (h.comp_tendsto tendsto_comap).zpow (-2)

-- No eventual nonvanishing is needed when the functions have compatible zeros.
example (hz : ∀ᶠ x in l, v x = 0 → u x = 0) :
    u ~[l] v ↔ Tendsto (fun x : {x // v x ≠ 0} ↦ Checked.div (u x) (v x) x.2.isUnit)
      (comap Subtype.val l) (𝓝 1) := isEquivalent_iff_tendsto_one hz

-- In particular, the quotient domain may be empty.
example : (fun _ : α ↦ (0 : ℝ)) ~[l] (fun _ : α ↦ (0 : ℝ)) := by
  let : IsEmpty {x : α // (0 : ℝ) ≠ 0} := ⟨fun x ↦ x.2 rfl⟩
  exact isEquivalent_of_tendsto_one (Eventually.of_forall fun _ _ ↦ rfl) tendsto_of_isEmpty
