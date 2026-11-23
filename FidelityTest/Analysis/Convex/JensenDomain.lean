/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module

public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! Jensen's inequality on genuine domains, including noninjective coordinates. -/

open Finset Set

noncomputable section

-- Renamed caller binders exercise the identity-coordinate default without name capture.
example {ι E : Type*} [AddCommGroup E] [Module ℝ E]
    {S : Set E} {F : E → ℝ} {U : Finset ι} {W : ι → ℝ} {P : ι → E}
    (H : ConvexOn ℝ S F) (H₀ : ∀ i ∈ U, 0 ≤ W i)
    (H₁ : ∑ i ∈ U, W i = 1) (Hm : ∀ i ∈ U, P i ∈ S) :
    F (∑ i ∈ U, W i • P i) ≤ ∑ i ∈ U, W i * F (P i) := by
  simpa only [smul_eq_mul] using H.map_sum_le H₀ H₁ Hm (H.convex.sum_mem H₀ H₁ Hm)

example {ι E : Type*} [AddCommGroup E] [Module ℝ E]
    {S : Set E} {F : E → ℝ} {U : Finset ι} {W : ι → ℝ} {P : ι → E}
    (H : ConcaveOn ℝ S F) (H₀ : ∀ i ∈ U, 0 ≤ W i)
    (Hpos : 0 < ∑ i ∈ U, W i) (Hm : ∀ i ∈ U, P i ∈ S) :
    U.centerMass W (F ∘ P) Hpos.ne' ≤ F (U.centerMass W P Hpos.ne') :=
  H.le_map_centerMass H₀ Hpos Hm (H.convex.centerMass_mem H₀ Hpos Hm)

-- No additive structure or total inverse is imposed on the positive source domain.
-- Weights may be zero; only their sum is normalized.
example {ι : Type*} [Fintype ι] (W : ι → ℝ) (P : ι → Ioi (0 : ℝ))
    (H₀ : ∀ i, 0 ≤ W i) (H₁ : ∑ i, W i = 1) (M : Ioi (0 : ℝ))
    (HM : (M : ℝ) = ∑ i, W i * (P i : ℝ)) :
    Checked.inv (M : ℝ) M.2.ne'.isUnit ≤
      ∑ i, W i * Checked.inv (P i : ℝ) (P i).2.ne'.isUnit := by
  have H := (convexOn_zpow (-1 : ℤ)).map_sum_le (t := univ) (w := W) (p := P)
    (fun i _ => H₀ i) H₁ (fun _ _ => Set.mem_univ _) (Set.mem_univ M)
    (hcoord := by simpa only [smul_eq_mul] using HM)
  simpa only [zpow_neg_one₀, smul_eq_mul] using H

-- Coincident coordinates do not require the source points to coincide.
example {ι : Type*} (U : Finset ι) (W : ι → ℝ) (P : ι → Bool) (Q : Bool)
    (H₀ : ∀ i ∈ U, 0 ≤ W i) (H₁ : ∑ i ∈ U, W i = 1) :
    (3 : ℝ) ≤ ∑ i ∈ U, W i * 3 := by
  have H : ConvexOn ℝ (univ : Set Bool) (fun _ => (3 : ℝ)) (fun _ => (0 : ℝ)) := by
    refine ⟨?_, ?_⟩
    · have himage : (fun _ : Bool => (0 : ℝ)) '' univ = {0} := by ext; simp
      rw [himage]
      exact convex_singleton 0
    · intro x hx y hy a b ha hb hab z hz hcoord
      simp only [← add_smul, hab, one_smul, le_refl]
  simpa only [smul_eq_mul] using H.map_sum_le (t := U) (p := P) H₀ H₁
    (fun _ _ => Set.mem_univ _) (Set.mem_univ Q) (hcoord := by simp)

-- An empty weighted center has no admissible denominator.
/-- error: unsolved goals
⊢ False -/
#guard_msgs in
example : ℝ :=
  (∅ : Finset Unit).centerMass (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)) (by simp)
