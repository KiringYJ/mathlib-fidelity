/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Gauss-Lucas Theorem

In this file we prove Gauss-Lucas Theorem:
the roots of the derivative of a nonconstant complex polynomial
are included in the convex hull of the roots of the polynomial.
-/

@[expose] public section
open scoped Polynomial ComplexConjugate

namespace Polynomial

/-- Given a nonzero polynomial `P` and a root `z` of its derivative, `derivRootWeight P z w` gives
the weight of a root `w` of `P` in a convex combination of the roots that is equal to `z`. The
weights are indexed by the roots: if `z` is not a root of `P`, it differs from every root `w`,
which gives the quotient by `‖z - w‖ ^ 2` its evidence. -/
noncomputable def derivRootWeight (P : ℂ[X]) {hP : P ≠ 0} (z : ℂ) (w : (P.roots hP).toFinset) :
    ℝ :=
  if h : P.eval z = 0 then (Pi.single z 1 : ℂ → ℝ) w
  else
    have : ‖z - w‖ ^ 2 ≠ 0 := pow_ne_zero 2 <| norm_ne_zero_iff.2 <| sub_ne_zero.2 fun hzw ↦
      h <| by rw [hzw]; exact (mem_roots hP).1 (Multiset.mem_toFinset.1 w.2)
    (P.rootMultiplicity (w : ℂ) hP : ℝ) / ‖z - w‖ ^ 2

theorem derivRootWeight_nonneg (P : ℂ[X]) {hP : P ≠ 0} (z : ℂ) (w : (P.roots hP).toFinset) :
    0 ≤ derivRootWeight P z w := by
  simp only [derivRootWeight, Pi.single, Function.update_apply]
  split_ifs <;> first | positivity | simp

variable {P : ℂ[X]} {z : ℂ}

/-- The sum of the weights `derivRootWeight P z w` of all the roots `w` of `P` is positive,
provided that `P` is not a constant polynomial. -/
theorem sum_derivRootWeight_pos (hP : 0 < degree P) (z : ℂ) :
    0 < ∑ w ∈ P.roots.toFinset.attach, derivRootWeight P z w := by
  have hP₀ : P ≠ 0 := by rintro rfl; simp at hP
  by_cases hPz : P.eval z = 0
  · have hz : z ∈ (P.roots hP₀).toFinset := Multiset.mem_toFinset.2 ((mem_roots hP₀).2 hPz)
    simp only [derivRootWeight, dite_eq_left hPz]
    rw [Finset.sum_attach (P.roots hP₀).toFinset fun w ↦ (Pi.single z 1 : ℂ → ℝ) w]
    simp [hz]
  · simp only [derivRootWeight, dite_eq_right hPz]
    apply Finset.sum_pos
    · intro w _
      have hw : P.IsRoot w := (mem_roots hP₀).1 (Multiset.mem_toFinset.1 w.2)
      have hzw : z - w ≠ 0 := sub_ne_zero.2 fun h ↦ hPz (h ▸ hw)
      apply div_pos
      · exact_mod_cast (rootMultiplicity_pos hP₀).2 hw
      · positivity
    · rw [Finset.attach_nonempty_iff, Multiset.toFinset_nonempty]
      apply Splits.roots_ne_zero (IsAlgClosed.splits _)
      rwa [← pos_iff_ne_zero, natDegree_pos_iff_degree_pos]

/-- *Gauss-Lucas Theorem*: if $P$ is a nonconstant polynomial with complex coefficients,
then all zeros of $P'$ belong to the convex hull of the set of zeros of $P$.

This version provides explicit formulas for the coefficients of the convex combination.
See also `rootSet_derivative_subset_convexHull_rootSet` below.
-/
theorem eq_centerMass_of_eval_derivative_eq_zero (hP : 0 < P.degree)
    (hz : P.derivative.eval z = 0) :
    z = P.roots.toFinset.attach.centerMass (P.derivRootWeight z) (↑)
      (sum_derivRootWeight_pos hP z).ne' := by
  have hP₀ : P ≠ 0 := ne_zero_of_degree_gt hP
  set s := (P.roots hP₀).toFinset
  set weight : s → ℝ := P.derivRootWeight z
  have hw := (sum_derivRootWeight_pos hP z).ne'
  suffices h : ∑ x ∈ s.attach, weight x • (z - ↑x) = 0 by
    calc
      z = s.attach.centerMass weight (Function.const _ z) hw := (Finset.centerMass_const hw z).symm
      _ = s.attach.centerMass weight (fun x ↦ z - ↑x) hw + s.attach.centerMass weight (↑) hw := by
        simp only [Finset.centerMass, Function.const_apply, ← smul_add, ← Finset.sum_add_distrib,
          sub_add_cancel]
      _ = s.attach.centerMass weight (↑) hw := by
        simp only [Finset.centerMass, h, smul_zero, zero_add]
  by_cases hzP : P.eval z = 0
  · simp only [weight, derivRootWeight, dite_eq_left hzP]
    rw [Finset.sum_attach s fun x ↦ (Pi.single z 1 : ℂ → ℝ) x • (z - x)]
    rw [Finset.sum_eq_single z] <;> simp_all
  have hne : ∀ x : ℂ, P.IsRoot x → z - x ≠ 0 := fun x hx ↦ sub_ne_zero.2 fun h ↦ hzP (h ▸ hx)
  let t := P.roots hP₀
  let f (x : {x // x ∈ t}) : ℂ := Checked.div 1 (z - x.1) (hne x.1 ((mem_roots hP₀).1 x.2)).isUnit
  let e : s ≃ {x // x ∈ t} := Equiv.subtypeEquivRight fun _ ↦ Multiset.mem_toFinset
  have hdiv := (IsAlgClosed.splits P).eval_derivative_div_eval_of_ne_zero hzP
  calc
    ∑ x ∈ s.attach, weight x • (z - ↑x) = conj (∑ x ∈ s.attach, (t.count x.1 : ℂ) * f (e x)) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      have hx : z - ↑x ≠ 0 := hne x ((mem_roots hP₀).1 (Multiset.mem_toFinset.1 x.2))
      simp only [weight, derivRootWeight, dite_eq_right hzP, f, e, t, count_roots]
      simp [← Complex.conj_mul', field, mul_comm]
    _ = conj (t.attach.map f).sum := by
      rw [Finset.sum_multiset_map_count, show s.attach = Finset.univ by ext; simp,
        show t.attach.toFinset = Finset.univ by ext; simp]
      simp only [Multiset.count_attach, nsmul_eq_mul]
      exact congrArg conj (Fintype.sum_equiv e _ _ fun _ ↦ rfl)
    _ = 0 := by
      change conj ((P.roots hP₀).attach.map _).sum = 0
      rw [← hdiv]
      simp [hz]

/-- *Gauss-Lucas Theorem*: if $P$ is a nonconstant polynomial with complex coefficients,
then all zeros of $P'$ belong to the convex hull of the set of zeros of $P$.

See also `eq_centerMass_of_eval_derivative_eq_zero`
for a version that provides explicit coefficients of the convex combination.
-/
theorem rootSet_derivative_subset_convexHull_rootSet (h₀ : 0 < P.degree) :
    haveI : P.derivative ≠ 0 := fun h ↦
      (natDegree_pos_iff_degree_pos.mpr h₀).ne' (derivative_eq_zero.mp h)
    P.derivative.rootSet ℂ ⊆ convexHull ℝ (P.rootSet ℂ) := by
  intro z hz
  rw [mem_rootSet, coe_aeval_eq_eval] at hz
  rw [eq_centerMass_of_eval_derivative_eq_zero h₀ hz]
  apply Finset.centerMass_mem_convexHull
  · simp [derivRootWeight_nonneg]
  · apply sum_derivRootWeight_pos h₀
  · simp [mem_rootSet]

end Polynomial
