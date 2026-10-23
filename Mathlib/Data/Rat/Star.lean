/-
Copyright (c) 2023 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux, Yaël Dillies
-/
module

public import Mathlib.Algebra.GroupWithZero.Commute
public import Mathlib.Algebra.Order.Monoid.Submonoid
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.Order.Ring.NNRat
public import Mathlib.Algebra.Order.Star.Basic

/-!
# Star ordered ring structures on `ℚ` and `ℚ≥0`

This file shows that `ℚ` and `ℚ≥0` are `StarOrderedRing`s. In particular, this means that every
nonnegative rational number is a sum of squares.
-/

public section

open AddSubmonoid Set
open scoped NNRat

namespace NNRat

@[simp] lemma addSubmonoid_closure_range_pow {n : ℕ} (hn₀ : n ≠ 0) :
    closure (range fun x : ℚ≥0 ↦ x ^ n) = ⊤ := by
  refine (eq_top_iff' _).2 fun x ↦ ?_
  have hd : (x.den : ℚ≥0) ≠ 0 := Nat.cast_ne_zero.mpr x.den_ne_zero
  let u := Units.mk0 (x.den : ℚ≥0) hd
  suffices x = (x.num * x.den ^ (n - 1)) • u.inv ^ n by
    rw [this]
    exact nsmul_mem (subset_closure <| mem_range_self _) _
  simp only [nsmul_eq_mul, Nat.cast_mul, Nat.cast_pow]
  apply mul_right_cancel₀ (pow_ne_zero n hd)
  have hu : u.inv * (x.den : ℚ≥0) = 1 := u.inv_mul
  rw [mul_assoc, ← mul_pow, hu, one_pow, mul_one]
  have hpow : (x.den : ℚ≥0) ^ n = (x.den : ℚ≥0) * (x.den : ℚ≥0) ^ (n - 1) := by
    simpa only [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn₀)] using
      pow_succ' (x.den : ℚ≥0) (n - 1)
  rw [hpow, ← mul_assoc, NNRat.mul_den_eq_num]

@[simp] lemma addSubmonoid_closure_range_mul_self : closure (range fun x : ℚ≥0 ↦ x * x) = ⊤ := by
  simpa only [sq] using addSubmonoid_closure_range_pow two_ne_zero

instance instStarOrderedRing : StarOrderedRing ℚ≥0 where
  le_iff a b := by simp [eq_comm, le_iff_exists_nonneg_add (a := a)]

end NNRat

namespace Rat

@[simp] lemma addSubmonoid_closure_range_pow {n : ℕ} (hn₀ : n ≠ 0) (hn : Even n) :
    closure (range fun x : ℚ ↦ x ^ n) = nonneg _ := by
  convert! (AddMonoidHom.map_mclosure NNRat.coeHom <| range fun x ↦ x ^ n).symm
  · have (x : ℚ) : ∃ y : ℚ≥0, (y : ℚ) ^ n = x ^ n := ⟨x.nnabs, by simp [hn.pow_abs]⟩
    simp only [subset_antisymm_iff, range_subset_iff, Set.mem_image, Set.mem_range]
    constructor
    · intro x
      obtain ⟨y, hy⟩ := this x
      exact ⟨y ^ n, ⟨y, rfl⟩, by
        change ((y ^ n : ℚ≥0) : ℚ) = x ^ n
        simpa only [NNRat.coe_pow] using hy⟩
    · rintro _ ⟨y, ⟨z, rfl⟩, rfl⟩
      exact ⟨(z : ℚ), NNRat.coe_pow z n |>.symm⟩
  · ext
    simp only [NNRat.addSubmonoid_closure_range_pow hn₀]
    constructor
    · intro h
      exact ⟨⟨_, h⟩, trivial, rfl⟩
    · rintro ⟨q, _, rfl⟩
      exact q.2

@[simp]
lemma addSubmonoid_closure_range_mul_self : closure (range fun x : ℚ ↦ x * x) = nonneg _ := by
  simpa only [sq] using addSubmonoid_closure_range_pow two_ne_zero even_two

instance instStarOrderedRing : StarOrderedRing ℚ where
  le_iff a b := by simp [eq_comm, le_iff_exists_nonneg_add (a := a)]

end Rat
