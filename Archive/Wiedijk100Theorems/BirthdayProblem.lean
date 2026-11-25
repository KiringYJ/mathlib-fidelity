/-
Copyright (c) 2021 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
module

public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.Probability.UniformOn
public import Mathlib.Probability.Notation

/-!
# Birthday Problem

This file proves Theorem 93 from the [100 Theorems List](https://www.cs.ru.nl/~freek/100/).

As opposed to the standard probabilistic statement, we instead state the birthday problem
in terms of injective functions. The general result about `Fintype.card (α ↪ β)` which this proof
uses is `Fintype.card_embedding_eq`.
-/

@[expose] public section

namespace Theorems100

local notation "|" x "|" => Finset.card x
local notation "‖" x "‖" => Fintype.card x

/-- **Birthday Problem**: set cardinality interpretation. -/
theorem birthday :
    2 * ‖Fin 23 ↪ Fin 365‖ < ‖Fin 23 → Fin 365‖ ∧ 2 * ‖Fin 22 ↪ Fin 365‖ > ‖Fin 22 → Fin 365‖ := by
  simp only [Fintype.card_fin, Fintype.card_embedding_eq, Fintype.card_fun]
  decide

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {n m : ℕ} [NeZero m]

/- We then endow the space with a canonical measure, which is called ℙ.
We define this to be the conditional counting measure, the uniform measure on the nonempty finite
space. -/
noncomputable instance measureSpace : MeasureSpace (Fin n → Fin m) :=
  ⟨uniformOn Set.univ .univ⟩

theorem Fin.measure_apply {s : Set <| Fin n → Fin m} :
    ℙ s = ENNReal.div (|s.toFinite.toFinset|) (‖Fin n → Fin m‖)
      ⟨Nat.cast_ne_zero.2 Fintype.card_ne_zero, Or.inr (ENNReal.natCast_ne_top _)⟩ := by
  rw [volume, measureSpace, uniformOn_univ]
  simp only [ENNReal.div_eq_mul_inv, Measure.count_apply_finite s s.toFinite]

/-- **Birthday Problem**: first probabilistic interpretation. -/
theorem birthday_measure :
    ℙ ({f | f.Injective} : Set (Fin 23 → Fin 365)) < (2 : ℝ≥0∞)⁻¹ := by
  rw [Fin.measure_apply, ENNReal.div_lt_iff]
  generalize_proofs hfin
  have : |hfin.toFinset| = 42200819302092359872395663074908957253749760700776448000000 := by
    trans ‖Fin 23 ↪ Fin 365‖
    · rw [← Fintype.card_coe]
      apply Fintype.card_congr
      rw [Set.Finite.coeSort_toFinset, Set.coe_ofPred]
      exact Equiv.subtypeInjectiveEquivEmbedding _ _
    · rw [Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin]
      rfl
  rw [this, mul_comm (2 : ℝ≥0∞)⁻¹]
  change _ < ENNReal.div (‖Fin 23 → Fin 365‖) 2 ⟨two_ne_zero, Or.inr ENNReal.ofNat_ne_top⟩
  rw [ENNReal.lt_div_iff_mul_lt _ (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top)]
  all_goals
    simp only [Fintype.card_pi, Fintype.card_fin, Finset.prod_const, Finset.card_univ]
    norm_num

end Theorems100
