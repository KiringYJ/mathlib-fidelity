/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
import Mathlib.Analysis.Asymptotics.Theta

open Asymptotics Filter
open scoped Topology

variable {α : Type*} {l : Filter α} {f g : α → ℝ}

-- Only the actual domain carries invertibility; ambient functions may vanish elsewhere.
example (h : f =Θ[l] g) :
    (fun x : {x // f x ≠ 0 ∧ g x ≠ 0} ↦ Checked.inv (f x) x.2.1.isUnit)
      =Θ[comap Subtype.val l]
    (fun x : {x // f x ≠ 0 ∧ g x ≠ 0} ↦ Checked.inv (g x) x.2.2.isUnit) :=
  (h.comp_tendsto tendsto_comap).inv

example (h : f =Θ[l] g) (u v : α → ℝ) (huv : u =Θ[l] v) :
    (fun x : {x // u x ≠ 0 ∧ v x ≠ 0} ↦ Checked.div (f x) (u x) x.2.1.isUnit)
      =Θ[comap Subtype.val l]
    (fun x : {x // u x ≠ 0 ∧ v x ≠ 0} ↦ Checked.div (g x) (v x) x.2.2.isUnit) :=
  (h.comp_tendsto tendsto_comap).div (huv.comp_tendsto tendsto_comap)

example (h : f =Θ[l] g) :
    (fun x ↦ f x ^ (0 : ℤ)) =Θ[l] (fun x ↦ g x ^ (0 : ℤ)) :=
  h.zpow 0

example (h : f =Θ[l] g) :
    (fun x : {x // f x ≠ 0 ∧ g x ≠ 0} ↦
      Checked.zpow (f x) (-2) (fun _ ↦ x.2.1.isUnit)) =Θ[comap Subtype.val l]
    (fun x : {x // f x ≠ 0 ∧ g x ≠ 0} ↦
      Checked.zpow (g x) (-2) (fun _ ↦ x.2.2.isUnit)) :=
  (h.comp_tendsto tendsto_comap).zpow (-2)

example (hf : ∀ᶠ x in l, f x ≠ 0) {c : ℝ} (hc : c ≠ 0)
    (h : Tendsto (fun x : {x // f x ≠ 0} ↦ Checked.div (g x) (f x) x.2.isUnit)
      (comap Subtype.val l) (𝓝 c)) : f =Θ[l] g :=
  isTheta_of_div_tendsto_nhds_ne_zero (hf.mono fun _ hx hzero ↦ (hx hzero).elim) h hc

-- Simultaneous zeros are permitted; eventual denominator nonvanishing is unnecessary.
example (hfg : ∀ᶠ x in l, f x = 0 → g x = 0) {c : ℝ} (hc : c ≠ 0)
    (h : Tendsto (fun x : {x // f x ≠ 0} ↦ Checked.div (g x) (f x) x.2.isUnit)
      (comap Subtype.val l) (𝓝 c)) : f =Θ[l] g :=
  isTheta_of_div_tendsto_nhds_ne_zero hfg h hc

example : (fun _ : α ↦ (0 : ℝ)) =Θ[l] (fun _ : α ↦ (0 : ℝ)) := by
  let : IsEmpty {x : α // (0 : ℝ) ≠ 0} := ⟨fun x ↦ x.2 rfl⟩
  exact isTheta_of_div_tendsto_nhds_ne_zero (c := 1)
    (Eventually.of_forall fun _ _ ↦ rfl) tendsto_of_isEmpty one_ne_zero

-- Eventual nonvanishing alone cannot define an inverse on every ambient point.
/--
error: could not synthesize default value for parameter 'ha' using tactics
---
error: an invertibility proof is required
α : Type u_1
l : Filter α
f g : α → ℝ
hf : ∀ᶠ (x : α) in l, f x ≠ 0
x : α
⊢ IsUnit (f x)
-/
#guard_msgs in
noncomputable example (hf : ∀ᶠ x in l, f x ≠ 0) : α → ℝ := fun x ↦ (f x)⁻¹
