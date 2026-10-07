/-
Copyright (c) 2022 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Algebra.Polynomial.Cardinal
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.RingTheory.Algebraic.Defs

/-!
# Cardinality of algebraic extensions

This file contains results on cardinality of algebraic extensions.
-/

public section


universe u v

open Cardinal Module
open scoped Polynomial

namespace Algebra.IsAlgebraic

variable (R : Type u) [CommRing R] [IsDomain R] (L : Type v) [CommRing L] [IsDomain L] [Algebra R L]
variable [IsTorsionFree R L] [Algebra.IsAlgebraic R L]

theorem lift_cardinalMk_le_sigma_polynomial :
    lift.{u} #L ≤
      #(Σ p : {p : R[X] // p.map (algebraMap R L) ≠ 0}, { x : L // x ∈ p.1.aroots L p.2 }) := by
  have := @lift_mk_le_lift_mk_of_injective L
    (Σ p : {p : R[X] // p.map (algebraMap R L) ≠ 0}, {x : L | x ∈ p.1.aroots L p.2})
    (fun x : L =>
      let p := Classical.indefiniteDescription _ (Algebra.IsAlgebraic.isAlgebraic x)
      have hp := (Polynomial.map_ne_zero_iff (FaithfulSMul.algebraMap_injective R L)).2 p.2.1
      ⟨⟨p.1, hp⟩, x, by
        dsimp
        rw [Polynomial.mem_roots hp, Polynomial.IsRoot, Polynomial.eval_map,
          ← Polynomial.aeval_def, p.2.2]⟩)
    fun x y h => congrArg (fun z => (z.2 : L)) h
  rwa [lift_umax, lift_id'.{v}] at this

theorem lift_cardinalMk_le_max : lift.{u} #L ≤ lift.{v} #R ⊔ ℵ₀ :=
  calc
    lift.{u} #L ≤
        #(Σ p : {p : R[X] // p.map (algebraMap R L) ≠ 0}, { x : L // x ∈ p.1.aroots L p.2 }) :=
      lift_cardinalMk_le_sigma_polynomial R L
    _ = Cardinal.sum fun p : {p : R[X] // p.map (algebraMap R L) ≠ 0} =>
          #{x : L | x ∈ p.1.aroots L p.2} := by
      rw [← mk_sigma]; rfl
    _ ≤ Cardinal.sum.{u, v} fun _ : {p : R[X] // p.map (algebraMap R L) ≠ 0} => ℵ₀ :=
      (sum_le_sum _ _ fun _ => (Multiset.finite_toSet _).lt_aleph0.le)
    _ = lift.{v} #{p : R[X] // p.map (algebraMap R L) ≠ 0} * ℵ₀ := by
      rw [sum_const, lift_aleph0]
    _ ≤ lift.{v} #(R[X]) * ℵ₀ := by gcongr; exact lift_le.2 (mk_subtype_le _)
    _ ≤ lift.{v} (#R ⊔ ℵ₀) ⊔ ℵ₀ ⊔ ℵ₀ := (mul_le_max _ _).trans <| by
      gcongr; simp only [lift_le, Polynomial.cardinalMk_le_max]
    _ = _ := by simp

variable (L : Type u) [CommRing L] [IsDomain L] [Algebra R L]
variable [IsTorsionFree R L] [Algebra.IsAlgebraic R L]

theorem cardinalMk_le_sigma_polynomial :
    #L ≤ #(Σ p : {p : R[X] // p.map (algebraMap R L) ≠ 0}, { x : L // x ∈ p.1.aroots L p.2 }) := by
  simpa only [lift_id] using lift_cardinalMk_le_sigma_polynomial R L

/-- The cardinality of an algebraic extension is at most the maximum of the cardinality
of the base ring or `ℵ₀`. -/
@[stacks 09GK]
theorem cardinalMk_le_max : #L ≤ max #R ℵ₀ := by
  simpa only [lift_id] using lift_cardinalMk_le_max R L

end Algebra.IsAlgebraic
