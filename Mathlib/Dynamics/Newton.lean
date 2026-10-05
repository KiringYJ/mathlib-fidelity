/-
Copyright (c) 2024 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, Oliver Nash
-/
module

public import Mathlib.RingTheory.Polynomial.Nilpotent

/-!
# Newton-Raphson method

Given a single-variable polynomial `P` with derivative `P'`, Newton's method concerns iteration of
the rational map: `x ↦ x - P(x) / P'(x)`.

Over a field, it can serve as a root-finding algorithm. It is also useful in proving results such
as Hensel's lemma and the Jordan-Chevalley decomposition.

The Newton step `x ↦ x - P'(x)⁻¹ * P(x)` is defined where `P'(x)` is a unit, which over a field is
exactly where `P(x) / P'(x)` is defined. A unit derivative need not survive a step, but it does when
`P(x)` is nilpotent: then the step changes `x` by a nilpotent element, so `P'` stays a unit, and
`P(x) ^ 2` divides the new value of `P`, which is therefore nilpotent. Newton iteration is
therefore defined on the set `Polynomial.NewtonDomain P S` of such points. Over a field these are
the simple roots of `P`, so iteration from other points, as in root-finding, is not covered.

## Main definitions / results:

* `Polynomial.newtonMap`: the map `x ↦ x - P'(x)⁻¹ * P(x)`, where `P'` is the derivative of the
  polynomial `P`, defined when `P'(x)` is a unit.
* `Polynomial.newtonMap_eq_self_iff`: `x` is a fixed point for Newton iteration iff it is a root of
  `P`.
* `Polynomial.NewtonDomain`: the points at which `P` is nilpotent and `P'` is a unit, and
  `Polynomial.NewtonDomain.step`, the Newton step as a self-map of them.
* `Polynomial.existsUnique_nilpotent_sub_and_aeval_eq_zero`: if `x` is almost a root of `P` in the
  sense that `P(x)` is nilpotent (and `P'(x)` is a unit) then we may write `x` as a sum
  `x = n + r` where `n` is nilpotent and `r` is a root of `P`. This can be used to prove the
  Jordan-Chevalley decomposition of linear endomorphisms.

-/

@[expose] public section

open Function

noncomputable section

namespace Polynomial

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (P : R[X]) {x : S}

/-- Given a single-variable polynomial `P` with derivative `P'`, this is the map
`x ↦ x - P'(x)⁻¹ * P(x)`, defined when `P'(x)` is a unit, which over a field is exactly where
`P(x) / P'(x)` is defined. -/
def newtonMap (x : S) (h : IsUnit <| aeval x (derivative P)) : S :=
  x - h.unit⁻¹ * aeval x P

theorem newtonMap_apply (h : IsUnit <| aeval x (derivative P)) :
    P.newtonMap x h = x - h.unit⁻¹ * aeval x P :=
  rfl

variable {P}

theorem newtonMap_eq_self_of_aeval_eq_zero (h : IsUnit <| aeval x (derivative P))
    (hx : aeval x P = 0) : P.newtonMap x h = x := by
  rw [newtonMap_apply, hx, mul_zero, sub_zero]

theorem newtonMap_eq_self_iff (h : IsUnit <| aeval x (derivative P)) :
    P.newtonMap x h = x ↔ aeval x P = 0 := by
  rw [newtonMap_apply, sub_eq_self, Units.mul_right_eq_zero]

theorem isNilpotent_newtonMap_sub (h : IsUnit <| aeval x (derivative P))
    (hx : IsNilpotent <| aeval x P) : IsNilpotent <| P.newtonMap x h - x := by
  rw [newtonMap_apply, sub_sub_cancel_left, isNilpotent_neg_iff]
  exact (Commute.all _ _).isNilpotent_mul_left hx

/-- If `P'(x)` is a unit, then `P(x) ^ 2` divides the value of `P` at the Newton step. -/
theorem aeval_sq_dvd_aeval_newtonMap (h : IsUnit <| aeval x (derivative P)) :
    (aeval x P) ^ 2 ∣ aeval (P.newtonMap x h) P := by
  have ⟨d, hd⟩ := binomExpansion (P.map (algebraMap R S)) x (-(h.unit⁻¹ * aeval x P))
  rw [eval_map_algebraMap, eval_map_algebraMap] at hd
  rw [newtonMap_apply, sub_eq_add_neg, hd]
  refine dvd_add ?_ (dvd_mul_of_dvd_right ?_ _)
  · convert! dvd_zero _
    have hu : (↑h.unit⁻¹ : S) * aeval x (derivative P) = 1 := by simp
    rw [derivative_map, eval_map_algebraMap, mul_neg, ← mul_assoc,
      mul_comm (aeval x (derivative P)), hu, one_mul, add_neg_cancel]
  · rw [even_two.neg_pow, mul_pow]
    exact dvd_mul_left _ _

variable (P S) in
/-- The points at which `P` is nilpotent and `P'` is a unit. Newton iteration is defined on them:
the Newton step maps them to themselves (`Polynomial.NewtonDomain.step`). -/
def NewtonDomain : Set S :=
  {x | IsNilpotent (aeval x P) ∧ IsUnit (aeval x (derivative P))}

namespace NewtonDomain

/-- The Newton step as a self-map of `Polynomial.NewtonDomain P S`. -/
def step (x : P.NewtonDomain S) : P.NewtonDomain S :=
  ⟨P.newtonMap x.1 x.2.2, by
    have hn := isNilpotent_newtonMap_sub x.2.2 x.2.1
    refine ⟨?_, isUnit_aeval_of_isUnit_aeval_of_isNilpotent_sub x.2.2 ?_⟩
    · obtain ⟨c, hc⟩ := aeval_sq_dvd_aeval_newtonMap x.2.2
      rw [hc]
      exact (Commute.all _ _).isNilpotent_mul_right (x.2.1.pow_of_pos two_ne_zero)
    · exact hn⟩

theorem coe_step (x : P.NewtonDomain S) : (step x : S) = P.newtonMap x.1 x.2.2 :=
  rfl

theorem isNilpotent_iterate_step_sub (x : P.NewtonDomain S) (n : ℕ) :
    IsNilpotent <| (step^[n] x : S) - x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ', comp_apply, coe_step, ← sub_add_sub_cancel _ (step^[n] x : S)]
    exact (Commute.all _ _).isNilpotent_add
      (isNilpotent_newtonMap_sub _ (step^[n] x).2.1) ih

theorem aeval_pow_two_pow_dvd_aeval_iterate_step (x : P.NewtonDomain S) (n : ℕ) :
    (aeval (x : S) P) ^ (2 ^ n) ∣ aeval (step^[n] x : S) P := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ', comp_apply, coe_step, pow_succ, pow_mul]
    exact (pow_dvd_pow_of_dvd ih 2).trans (aeval_sq_dvd_aeval_newtonMap _)

end NewtonDomain

/-- If `x` is almost a root of `P` in the sense that `P(x)` is nilpotent (and `P'(x)` is a
unit) then we may write `x` as a sum `x = n + r` where `n` is nilpotent and `r` is a root of `P`.
Moreover, `n` and `r` are unique.

This can be used to prove the Jordan-Chevalley decomposition of linear endomorphisms. -/
theorem existsUnique_nilpotent_sub_and_aeval_eq_zero
    (h : IsNilpotent (aeval x P)) (h' : IsUnit (aeval x <| derivative P)) :
    ∃! r, IsNilpotent (x - r) ∧ aeval r P = 0 := by
  simp_rw [(neg_sub _ x).symm, isNilpotent_neg_iff]
  refine existsUnique_of_exists_of_unique ?_ fun r₁ r₂ ⟨hr₁, hr₁'⟩ ⟨hr₂, hr₂'⟩ ↦ ?_
  · -- Existence
    obtain ⟨n, hn⟩ := id h
    let x' : P.NewtonDomain S := ⟨x, h, h'⟩
    refine ⟨NewtonDomain.step^[n] x', NewtonDomain.isNilpotent_iterate_step_sub x' n, ?_⟩
    rw [← zero_dvd_iff, ← pow_eq_zero_of_le (n.lt_two_pow_self).le hn]
    exact NewtonDomain.aeval_pow_two_pow_dvd_aeval_iterate_step x' n
  · -- Uniqueness
    have ⟨u, hu⟩ := binomExpansion (P.map (algebraMap R S)) r₁ (r₂ - r₁)
    suffices IsUnit (aeval r₁ (derivative P) + u * (r₂ - r₁)) by
      rwa [derivative_map, eval_map_algebraMap, eval_map_algebraMap, eval_map_algebraMap,
        add_sub_cancel, hr₂', hr₁', zero_add, pow_two, ← mul_assoc, ← add_mul, eq_comm,
        this.mul_right_eq_zero, sub_eq_zero, eq_comm] at hu
    have : IsUnit (aeval r₁ (derivative P)) :=
      isUnit_aeval_of_isUnit_aeval_of_isNilpotent_sub h' hr₁
    rw [← sub_sub_sub_cancel_right r₂ r₁ x]
    refine IsNilpotent.isUnit_add_left_of_commute ?_ this (Commute.all _ _)
    exact (Commute.all _ _).isNilpotent_mul_left <| (Commute.all _ _).isNilpotent_sub hr₂ hr₁

end Polynomial
