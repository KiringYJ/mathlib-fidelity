/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module

public import Mathlib.Analysis.Asymptotics.TVS

/-! The quotient limit lives on its actual domain; omitted zeros still matter to the converse. -/

open Asymptotics Filter
open scoped Topology

example {α E : Type*} [AddCommGroup E] [TopologicalSpace E] [Module ℝ E]
    [ContinuousSMul ℝ E] {f : α → ℝ} {g : α → E} {l : Filter α}
    (h : g =o[ℝ; l] f) :
    Tendsto (fun x : {x // f x ≠ 0} ↦
      have hx := x.property
      (f x)⁻¹ • g x) (comap Subtype.val l) (𝓝 0) := h.tendsto_inv_smul

-- Empty quotient domains are valid when the omitted values are compatible zeros.
example : (fun _ : ℕ ↦ (0 : ℝ)) =o[ℝ; atTop] (fun _ ↦ (0 : ℝ)) := by
  let : IsEmpty {x : ℕ // (0 : ℝ) ≠ 0} := ⟨fun x ↦ x.2 rfl⟩
  exact (isLittleOTVS_iff_tendsto_inv_smul
    (Eventually.of_forall fun _ _ ↦ rfl)).mpr tendsto_of_isEmpty

-- A limit over an empty quotient domain alone does not justify the ambient little-o relation.
example : Tendsto
    (fun x : {_n : ℕ // (0 : ℝ) ≠ 0} ↦ Checked.inv (0 : ℝ) x.2.isUnit * 1)
    (comap Subtype.val (atTop : Filter ℕ)) (𝓝 0) := by
  let : IsEmpty {_n : ℕ // (0 : ℝ) ≠ 0} := ⟨fun x ↦ x.2 rfl⟩
  exact tendsto_of_isEmpty

example : ¬((fun _ : ℕ ↦ (1 : ℝ)) =o[ℝ; atTop] (fun _ ↦ (0 : ℝ))) := by
  intro h
  have h' := isLittleOTVS_iff_isLittleO.mp h
  obtain ⟨n, hn⟩ := (h'.bound zero_lt_one).exists
  norm_num at hn
