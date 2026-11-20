/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.Topology.MetricSpace.Infsep

/-!
# The Second Main Theorem of Value Distribution Theory

This file will, in the future, establish the second main theorem of Value Distribution Theory. At
present, it collects material that will be used in the proof.

See Section VI.4 of [Lang, *Introduction to Complex Hyperbolic Spaces*][MR886677] for a detailed
discussion. A full formalized proof of the second main theorem is available at
https://github.com/kebekus/ProjectVD
-/

public section

open Finset

namespace Real

/-!
## The Separation Lemma

This section proves the pointwise **separation lemma**, over a general normed field.
-/

variable {𝕜 : Type*} [NormedField 𝕜]

/-- The separation lemma for a finite set of points in a normed field. Off the given points,
the sum of their individual logarithmic proximities is controlled, up to a fixed constant,
by the positive logarithm of the norm of the sum of their reciprocals. -/
theorem exists_sum_posLog_inv_norm_sub_le (s : Finset 𝕜) :
    ∃ C : ℝ, ∀ w : {w : 𝕜 // w ∉ s},
      let q (a : s) := Checked.inv (w.val - a.val)
        (sub_ne_zero.mpr (fun (e : w.val = a.val) ↦ w.property (e.symm ▸ a.property))).isUnit
      ∑ a : s, log⁺ ‖q a‖ ≤ log⁺ ‖∑ a : s, q a‖ + C := by
  classical
  obtain (rfl | ⟨a, rfl⟩ | hs) : s = ∅ ∨ (∃ a, s = {a}) ∨ s.Nontrivial := by
    grind [Finset.Nonempty.exists_eq_singleton_or_nontrivial]
  · exact ⟨0, by simp⟩
  · let : Unique ↥({a} : Finset 𝕜) :=
      { default := ⟨a, mem_singleton_self _⟩
        uniq := fun x ↦ Subtype.ext (mem_singleton.mp x.property) }
    exact ⟨0, by simp⟩
  obtain ⟨δ, hδ, hgap⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ a ∈ s, ∀ b ∈ s, a ≠ b → δ ≤ ‖a - b‖ := by
    refine ⟨(s : Set 𝕜).infsep, (Finset.infsep_pos_iff_nontrivial _).mpr hs, ?_⟩
    intro a ha b hb hab
    rw [← dist_eq_norm]
    exact Set.le_edist_of_le_infsep ha hb hab le_rfl
  let d := δ / 2
  have hd : 0 < d := half_pos hδ
  let B := Checked.inv d hd.ne'.isUnit
  have hBd : B * d = 1 := inv_mul_cancel₀
  have hB : 0 < B := inv_pos.mpr hd
  have hN : (2 : ℝ) ≤ #s := by exact_mod_cast hs.two_le_card
  have hB' : B ≤ #s * B := by nlinarith
  have hn : 0 ≤ log #s := log_nonneg (by linarith)
  let K := log⁺ ((#s : ℝ) * B)
  have hK : 0 ≤ K := posLog_nonneg
  refine ⟨#s * K + log #s, fun w ↦ ?_⟩
  let q (a : s) := Checked.inv (w.val - a.val)
    (sub_ne_zero.mpr (fun (e : w.val = a.val) ↦ w.property (e.symm ▸ a.property))).isUnit
  change ∑ a : s, log⁺ ‖q a‖ ≤ log⁺ ‖∑ a : s, q a‖ + (#s * K + log #s)
  have hq (a : s) : ‖q a‖ * ‖w.val - a.val‖ = 1 := by
    rw [← norm_mul, show q a * (w.val - a.val) = 1 from inv_mul_cancel₀, norm_one]
  have hle (t : Finset s) (ht : ∀ i ∈ t, ‖q i‖ ≤ #s * B) :
      ∑ i ∈ t, log⁺ ‖q i‖ ≤ #t * K := by
    calc
      _ ≤ ∑ _ ∈ t, K := sum_le_sum fun i hi ↦
        posLog_le_posLog (by linarith [norm_nonneg (q i)]) (ht i hi)
      _ = _ := by rw [sum_const, nsmul_eq_mul]
  by_cases hfar : ∀ a : s, ‖q a‖ ≤ #s * B
  · have hsum := hle univ (fun i _ ↦ hfar i)
    simp only [card_univ, Fintype.card_coe] at hsum
    linarith [show 0 ≤ log⁺ ‖∑ a : s, q a‖ from posLog_nonneg]
  push Not at hfar
  obtain ⟨a, ha⟩ := hfar
  have hnear : ‖w.val - a.val‖ < d := by
    by_contra! h
    have h₁ := (mul_lt_mul_of_pos_right (hB'.trans_lt ha) hd).trans_le
      (mul_le_mul_of_nonneg_left h (norm_nonneg _))
    linarith [hq a]
  let t := (univ : Finset s).erase a
  have hcard : (#t : ℝ) = #s - 1 := by
    have e : t.card + 1 = s.card := by
      simpa [t] using card_erase_add_one (mem_univ a)
    exact eq_sub_of_add_eq (by exact_mod_cast e)
  have hother (i : s) (hi : i ∈ t) : ‖q i‖ ≤ B := by
    have hne : a.val ≠ i.val := fun he ↦ (mem_erase.mp hi).1 (Subtype.ext he).symm
    have htriangle : δ ≤ ‖w.val - a.val‖ + ‖w.val - i.val‖ :=
      (hgap _ a.property _ i.property hne).trans (by
        simpa [norm_sub_rev] using norm_sub_le (w.val - a.val) (w.val - i.val))
    have hdist : d ≤ ‖w.val - i.val‖ := by dsimp [d] at *; linarith
    by_contra! h
    have h₁ := (mul_lt_mul_of_pos_right h hd).trans_le
      (mul_le_mul_of_nonneg_left hdist (norm_nonneg _))
    linarith [hq i]
  have htail := hle t (fun i hi ↦ (hother i hi).trans hB')
  rw [hcard] at htail
  have hnorm : ‖∑ i ∈ t, q i‖ ≤ (#s - 1) * B := calc
    _ ≤ ∑ i ∈ t, ‖q i‖ := norm_sum_le _ _
    _ ≤ ∑ _ ∈ t, B := sum_le_sum hother
    _ = _ := by rw [sum_const, nsmul_eq_mul, hcard]
  have hsplit : q a + ∑ i ∈ t, q i = ∑ i : s, q i := add_sum_erase _ _ (mem_univ a)
  have hh := norm_sub_le (q a + ∑ i ∈ t, q i) (∑ i ∈ t, q i)
  rw [add_sub_cancel_right, hsplit] at hh
  have hlow : ‖q a‖ - (#s - 1) * B ≤ ‖∑ i : s, q i‖ := by linarith
  have hdom : ‖q a‖ ≤ #s * ‖∑ i : s, q i‖ := by
    have h₁ := mul_nonneg (show (0 : ℝ) ≤ #s - 1 by linarith) (sub_nonneg.mpr ha.le)
    nlinarith [mul_le_mul_of_nonneg_left hlow (show 0 ≤ (#s : ℝ) by positivity)]
  have hhead := (posLog_le_posLog (by linarith [norm_nonneg (q a)]) hdom).trans posLog_nat_mul
  rw [← add_sum_erase (univ : Finset s) (fun i ↦ log⁺ ‖q i‖) (mem_univ a)]
  change log⁺ ‖q a‖ + ∑ i ∈ t, log⁺ ‖q i‖ ≤ _
  nlinarith

end Real
