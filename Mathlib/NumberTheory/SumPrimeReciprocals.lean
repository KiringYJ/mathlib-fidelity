/-
Copyright (c) 2023 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Order.Group.Indicator
public import Mathlib.Analysis.PSeries
public import Mathlib.NumberTheory.SmoothNumbers

/-!
# The sum of the reciprocals of the primes diverges

We show that the sum of `1/p`, where `p` runs through the prime numbers, diverges.
We follow the elementary proof by Erdős that is reproduced in "Proofs from THE BOOK".
There are two versions of the main result: `not_summable_one_div_on_primes`, which
expresses the sum as a sub-sum of the harmonic series, and `Nat.Primes.not_summable_one_div`,
which writes it as a sum over `Nat.Primes`. We also show that the sum of `p^r` for `r : ℝ`
converges if and only if `r < -1`; see `Nat.Primes.summable_rpow`.

## References

See the sixth proof for the infinity of primes in Chapter 1 of [aigner1999proofs].
The proof is due to Erdős.
-/

public section

open Set Nat
open scoped Topology

section PrimeSums

variable {M : Type*} [CommMonoid M] [TopologicalSpace M] (f : ℕ → M)

omit [TopologicalSpace M] in
@[to_additive]
private lemma ite_prime_eq_mulIndicator :
    (fun n : ℕ ↦ if n.Prime then f n else 1) = {n | n.Prime}.mulIndicator f := by
  ext; simp [Set.mulIndicator_apply]

/-- Reindex a product over `Nat.Primes` as a product over `ℕ`, extending `f` by `1`. -/
@[to_additive /-- Reindex a sum over `Nat.Primes` as a sum over `ℕ`, extending `f` by `0`. -/]
theorem Nat.Primes.tprod_eq_tprod_ite :
    ∏' p : Primes, f p = ∏' n : ℕ, if n.Prime then f n else 1 := by
  rw [ite_prime_eq_mulIndicator]; exact tprod_subtype {n | n.Prime} f

/-- `Multipliable` over `Nat.Primes` iff over `ℕ` extending `f` by `1`. -/
@[to_additive /-- `Summable` over `Nat.Primes` iff over `ℕ` extending `f` by `0`. -/]
theorem Nat.Primes.multipliable_iff_multipliable_ite :
    Multipliable (fun p : Primes ↦ f p) ↔ Multipliable fun n : ℕ ↦ if n.Prime then f n else 1 := by
  rw [ite_prime_eq_mulIndicator]; exact multipliable_subtype_iff_mulIndicator

/-- `HasProd` over `Nat.Primes` iff over `ℕ` extending `f` by `1`. -/
@[to_additive /-- `HasSum` over `Nat.Primes` iff over `ℕ` extending `f` by `0`. -/]
theorem Nat.Primes.hasProd_iff_hasProd_ite {a : M} :
    HasProd (fun p : Primes ↦ f p) a ↔ HasProd (fun n : ℕ ↦ if n.Prime then f n else 1) a := by
  rw [ite_prime_eq_mulIndicator]; exact hasProd_subtype_iff_mulIndicator

end PrimeSums

/-- The cardinality of the set of `k`-rough numbers `≤ N` is bounded by `N` times the sum
of `1/p` over the primes `k ≤ p ≤ N`. -/
-- This needs `Mathlib/Analysis/RCLike/Basic.lean`, so we put it here
-- instead of in `Mathlib/NumberTheory/SmoothNumbers.lean`.
lemma Nat.roughNumbersUpTo_card_le' (N k : ℕ) :
    (roughNumbersUpTo N k).card ≤
      N * ∑ p : ↥(N.succ.primesBelow \ k.primesBelow), Checked.div (1 : ℝ) p
        (Nat.cast_ne_zero.mpr
          (prime_of_mem_primesBelow (Finset.mem_sdiff.mp p.2).1).ne_zero).isUnit := by
  rw [Finset.mul_sum]
  refine (Nat.cast_le.mpr <| roughNumbersUpTo_card_le N k).trans ?_
  rw [cast_sum]
  refine Finset.sum_le_sum fun p _ ↦ ?_
  have hp : (p : ℕ) ≠ 0 := (prime_of_mem_primesBelow (Finset.mem_sdiff.mp p.2).1).ne_zero
  rw [mul_one_div₀]
  exact cast_div_le

/-- The sum over primes `k ≤ p ≤ 4^(π(k-1)+1)` over `1/p` (as a real number) is at least `1/2`. -/
lemma one_half_le_sum_primes_ge_one_div (k : ℕ) :
    1 / 2 ≤ ∑ p : ↥((4 ^ (k.primesBelow.card + 1)).succ.primesBelow \ k.primesBelow),
      Checked.div (1 : ℝ) p (Nat.cast_ne_zero.mpr
        (prime_of_mem_primesBelow (Finset.mem_sdiff.mp p.2).1).ne_zero).isUnit := by
  set m : ℕ := 2 ^ k.primesBelow.card
  set N₀ : ℕ := 2 * m ^ 2 with hN₀
  let S : ℝ := ∑ p : ↥((2 * N₀).succ.primesBelow \ k.primesBelow), Checked.div 1 p
    (Nat.cast_ne_zero.mpr
      (prime_of_mem_primesBelow (Finset.mem_sdiff.mp p.2).1).ne_zero).isUnit
  suffices 1 / 2 ≤ S by
    have hbound : 4 ^ (k.primesBelow.card + 1) = 2 * N₀ := by
      dsimp [N₀, m]
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, pow_right_comm, pow_succ]
      ring
    convert this using 1
    refine Fintype.sum_equiv
      (Equiv.subtypeEquivRight fun p ↦ by rw [hbound]) _ _ ?_
    intro p
    rfl
  suffices 2 * N₀ ≤ m * (2 * N₀).sqrt + 2 * N₀ * S by
    rwa [hN₀, ← mul_assoc, ← pow_two 2, ← mul_pow, sqrt_eq', ← sub_le_iff_le_add',
      cast_mul, cast_mul, cast_pow, cast_two,
      show (2 * (2 * m ^ 2) - m * (2 * m) : ℝ) = 2 * (2 * m ^ 2) * (1 / 2) by ring,
      mul_le_mul_iff_right₀ <| by positivity] at this
  calc (2 * N₀ : ℝ)
    _ = ((2 * N₀).smoothNumbersUpTo k).card + ((2 * N₀).roughNumbersUpTo k).card := by
        exact_mod_cast ((2 * N₀).smoothNumbersUpTo_card_add_roughNumbersUpTo_card k).symm
    _ ≤ m * (2 * N₀).sqrt + ((2 * N₀).roughNumbersUpTo k).card := by
        exact_mod_cast Nat.add_le_add_right ((2 * N₀).smoothNumbersUpTo_card_le k) _
    _ ≤ m * (2 * N₀).sqrt + 2 * N₀ * S := by grw [roughNumbersUpTo_card_le']; norm_cast

/-- The sum over the reciprocals of the primes diverges. -/
theorem not_summable_one_div_on_primes :
    ¬ Summable (fun n : ℕ ↦ if hn : n.Prime then
      Checked.div (1 : ℝ) n (Nat.cast_ne_zero.mpr hn.ne_zero).isUnit else 0) := by
  let f : ℕ → ℝ := fun n ↦ if hn : n.Prime then
    Checked.div 1 n (Nat.cast_ne_zero.mpr hn.ne_zero).isUnit else 0
  change ¬ Summable f
  intro h
  obtain ⟨k, hk⟩ := h.nat_tsum_vanishing (Iio_mem_nhds one_half_pos : Iio (1 / 2 : ℝ) ∈ 𝓝 0)
  specialize hk ({p | Nat.Prime p} ∩ {p | k ≤ p}) inter_subset_right
  have hmask : indicator ({p | Nat.Prime p} ∩ {p | k ≤ p}) f = indicator {p | k ≤ p} f := by
    funext n
    by_cases hp : n.Prime <;> by_cases hkn : k ≤ n <;> simp [indicator, f, hp, hkn]
  rw [tsum_subtype, hmask, mem_Iio] at hk
  have h' := h.indicator {n : ℕ | k ≤ n}
  let B := primesBelow ((4 ^ (k.primesBelow.card + 1)).succ) \ primesBelow k
  have hfinite :
      (∑ p : B, Checked.div (1 : ℝ) p (Nat.cast_ne_zero.mpr
        (prime_of_mem_primesBelow (Finset.mem_sdiff.mp p.2).1).ne_zero).isUnit) =
        ∑ p ∈ B, indicator {n | k ≤ n} f p := by
    conv_rhs => rw [← Finset.sum_coe_sort]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    obtain ⟨hp₁, hp₂⟩ := Finset.mem_sdiff.mp p.2
    have hpp := prime_of_mem_primesBelow hp₁
    have hpk : k ≤ (p : ℕ) := by
      by_contra hn
      exact hp₂ (mem_primesBelow.mpr ⟨lt_of_not_ge hn, hpp⟩)
    simp [indicator, f, hpk, hpp]
  have hnonneg (n : ℕ) : 0 ≤ indicator {p | k ≤ p} f n := by
    apply indicator_nonneg
    intro p _
    dsimp only [f]
    split_ifs <;> positivity
  have hupper := Summable.sum_le_tsum B (fun n _ ↦ hnonneg n) h'
  have hlower : 1 / 2 ≤ ∑ p ∈ B, indicator {n | k ≤ n} f p := by
    rw [← hfinite]
    exact one_half_le_sum_primes_ge_one_div k
  exact (not_lt_of_ge (hlower.trans hupper)) hk

set_option backward.isDefEq.respectTransparency false in
/-- The sum over the reciprocals of the primes diverges. -/
theorem Nat.Primes.not_summable_one_div :
    ¬ Summable (fun p : Nat.Primes ↦ Checked.div (1 : ℝ) p
      (Nat.cast_ne_zero.mpr p.property.ne_zero).isUnit) := by
  intro h
  apply not_summable_one_div_on_primes
  let f : ℕ → ℝ := fun n ↦ if hn : n.Prime then
    Checked.div 1 n (Nat.cast_ne_zero.mpr hn.ne_zero).isUnit else 0
  have hf : Function.support f ⊆ {n | n.Prime} := by
    intro n hn
    by_contra hp
    exact hn (dite_eq_right hp)
  have hs : Summable (fun p : Nat.Primes ↦ f p) := by
    refine h.congr fun p ↦ ?_
    dsimp only [f]
    rw [dite_eq_left p.property]
  exact ((hasSum_subtype_iff_of_support_subset hf).mp hs.hasSum).summable

/-- The series over `p^r` for primes `p` converges if and only if `r < -1`. -/
theorem Nat.Primes.summable_rpow {r : ℝ} :
    Summable (fun p : Nat.Primes ↦ (p : ℝ) ^ r) ↔ r < -1 := by
  by_cases h : r < -1
  · -- case `r < -1`
    simp only [h, iff_true]
    exact (Real.summable_nat_rpow.mpr h).subtype _
  · -- case `-1 ≤ r`
    simp only [h, iff_false]
    refine fun H ↦ Nat.Primes.not_summable_one_div <| H.of_nonneg_of_le (fun _ ↦ by positivity) ?_
    intro p
    rw [one_div₀, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast p.prop.one_lt.le) <| not_lt.mp h
