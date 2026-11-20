/-
Copyright (c) 2025 Alastair Irving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alastair Irving, Terry Tao, Ruben Van de Velde
-/
module

public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Analysis.SpecialFunctions.Log.InvLog
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.NumberTheory.AbelSummation
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.NumberTheory.Primorial
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.InvLog
import Mathlib.Data.Nat.Prime.Int

/-!
# Chebyshev functions

This file defines the Chebyshev functions `theta` and `psi`.
These give logarithmically weighted sums of primes and prime powers.

## Main definitions

- `Chebyshev.psi` gives the sum of `ArithmeticFunction.vonMangoldt`
- `Chebyshev.theta` gives the sum of `log p` over primes
- `Chebyshev.lcmUpto n` gives the least common multiple of `{1,...,n}`

## Main results

- `Chebyshev.theta_eq_log_primorial` shows that `θ x` is the log of the product of primes up to x
- `Chebyshev.theta_le_log4_mul_x` gives Chebyshev's upper bound on `θ`
- `Chebyshev.theta_ge` gives Chebyshev's lower bound on `θ`.
- `Chebyshev.psi_eq_log_lcmUpto` shows that `ψ n` is the log of the lcm of `{1,...,n}`.
- `Chebyshev.psi_eq_sum_theta` and `Chebyshev.psi_eq_theta_add_sum_theta` relate `ψ` to `θ`.
- `Chebyshev.psi_sub_theta_le_mul_sqrt` gives an upper bound on `ψ - θ`.
- `Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi` and
   `Chebyshev.psi_sub_theta_ge_psi_add_psi_add_psi` establish the Costa-Pereira inequalities
   for `ψ - θ`.
- `Chebyshev.psi_le_const_mul_self` gives Chebyshev's upper bound on `ψ`.
- `Chebyshev.psi_ge` gives Chebyshev's lower bound on `ψ`.
- `Chebyshev.primeCounting_eq_theta_div_log_add_integral` relates the prime counting function to `θ`
- `Chebyshev.eventually_primeCounting_le` gives an asymptotic upper bound on the
  prime counting function.
- `Chebyshev.pi_le_log4_mul_div` gives an explicit upper bound on the prime counting function.
- `Chebyshev.pi_ge` gives an explicit lower bound on the prime counting function.

## Notation

We introduce the scoped notations `θ` and `ψ` in the Chebyshev namespace for the Chebyshev
functions.

## References

Parts of this file were upstreamed from the PrimeNumberTheoremAnd project by Kontorovich et al, https://github.com/alexKontorovich/PrimeNumberTheoremAnd.

-/

@[expose] public section

open Nat hiding log
open Finset Real
open ArithmeticFunction hiding log id
open scoped Nat.Prime

namespace Chebyshev

/-- The sum of `ArithmeticFunction.vonMangoldt` over integers `n ≤ x`. -/
noncomputable def psi (x : ℝ) : ℝ :=
  ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n

@[inherit_doc]
scoped notation "ψ" => Chebyshev.psi

/-- The sum of `log p` over primes `p ≤ x`. -/
noncomputable def theta (x : ℝ) : ℝ :=
  ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, log p

@[inherit_doc]
scoped notation "θ" => Chebyshev.theta

theorem psi_nonneg (x : ℝ) : 0 ≤ ψ x := sum_nonneg fun _ _ ↦ (by simp)

theorem theta_nonneg (x : ℝ) : 0 ≤ θ x := sum_nonneg fun _ _ ↦ log_nonneg (by aesop)

theorem theta_pos {x : ℝ} (hy : 2 ≤ x) : 0 < θ x := by
  refine sum_pos (fun n hn ↦ log_pos ?_) ⟨2, ?_⟩
  · simp only [mem_filter] at hn; exact_mod_cast hn.2.one_lt
  · have : 0 ≤ x := by grind
    simpa using ⟨(le_floor_iff this).2 hy, prime_two⟩

theorem psi_eq_sum_Icc (x : ℝ) :
    ψ x = ∑ n ∈ Icc 0 ⌊x⌋₊, Λ n := by
  rw [psi, ← add_sum_Ioc_eq_sum_Icc] <;> simp

theorem theta_eq_sum_Icc (x : ℝ) :
    θ x = ∑ p ∈ Icc 0 ⌊x⌋₊ with p.Prime, log p := by
  rw [theta, sum_filter, sum_filter, ← add_sum_Ioc_eq_sum_Icc] <;> simp

theorem theta_eq_sum_primesLE (x : ℝ) :
    θ x = ∑ p ∈ primesLE ⌊x⌋₊, log p := by
  simp [theta_eq_sum_Icc, primesLE_eq_filter_Icc_zero]

theorem theta_eq_sum_primesLE_log (n : ℕ) : θ n = ∑ p ∈ primesLE n, log p := by
  simp [theta_eq_sum_primesLE]

theorem psi_eq_zero_of_lt_two {x : ℝ} (hx : x < 2) : ψ x = 0 := by
  apply sum_eq_zero fun n hn ↦ ?_
  simp only [mem_Ioc] at hn
  convert! vonMangoldt_apply_one
  have := lt_of_le_of_lt (le_floor_iff' hn.1.ne' |>.mp hn.2) hx
  norm_cast at this
  linarith

@[simp]
theorem psi_eq_zero_iff {x : ℝ} : ψ x = 0 ↔ x < 2 := by
  refine ⟨fun h₀ ↦ ?_, psi_eq_zero_of_lt_two⟩
  by_contra! contra
  replace contra : 2 ∈ Ioc 0 ⌊x⌋₊ := by rw [mem_Ioc, le_floor_iff (by grind)]; grind
  have : Λ 2 ≤ ψ x := single_le_sum (fun n _ ↦ vonMangoldt_nonneg (n := n)) contra
  have := vonMangoldt_pos_iff.mpr prime_two.isPrimePow
  linarith

theorem psi_eq_zero_of_le_one {x : ℝ} (hx : x ≤ 1) : ψ x = 0 :=
  psi_eq_zero_of_lt_two (by linarith)

@[simp]
theorem psi_zero : ψ 0 = 0 := psi_eq_zero_of_lt_two zero_lt_two

@[simp]
theorem psi_one : ψ 1 = 0 := psi_eq_zero_of_lt_two one_lt_two

theorem theta_eq_zero_of_lt_two {x : ℝ} (hx : x < 2) : θ x = 0 := by
  apply sum_eq_zero fun n hn ↦ ?_
  convert! log_one
  simp only [mem_filter, mem_Ioc] at hn
  have := lt_of_le_of_lt (le_floor_iff' hn.1.1.ne' |>.mp hn.1.2) hx
  norm_cast at ⊢ this
  linarith

@[simp]
theorem theta_eq_zero_iff {x : ℝ} : θ x = 0 ↔ x < 2 := by
  refine ⟨fun h₀ ↦ ?_, theta_eq_zero_of_lt_two⟩
  by_contra! contra
  replace contra : 2 ∈ Ioc 0 ⌊x⌋₊ := by rw [mem_Ioc, le_floor_iff (by grind)]; grind
  have h₁ : log (↑(2 : ℕ) : ℝ) ≤ θ x :=
    single_le_sum (fun p hp ↦ log_nonneg (by aesop)) (by aesop (add simp prime_two))
  have := Real.log_pos one_lt_two
  grind

theorem theta_eq_zero_of_le_one {x : ℝ} (hx : x ≤ 1) : θ x = 0 :=
  theta_eq_zero_of_lt_two (by linarith)

@[simp]
theorem theta_zero : θ 0 = 0 := theta_eq_zero_of_lt_two zero_lt_two

@[simp]
theorem theta_one : θ 1 = 0 := theta_eq_zero_of_lt_two one_lt_two

theorem psi_eq_psi_coe_floor (x : ℝ) : ψ x = ψ ⌊x⌋₊ := by
  unfold psi
  rw [floor_natCast]

theorem theta_eq_theta_coe_floor (x : ℝ) : θ x = θ ⌊x⌋₊ := by
  unfold theta
  rw [floor_natCast]

@[gcongr]
theorem psi_mono : Monotone ψ := by
  intro x y hxy
  apply sum_le_sum_of_subset_of_nonneg
  · exact Ioc_subset_Ioc (by rfl) (by gcongr)
  · simp

@[gcongr]
theorem theta_mono : Monotone θ := by
  intro x y hxy
  apply sum_le_sum_of_subset_of_nonneg
  · exact filter_subset_filter _ <| Ioc_subset_Ioc_right (by gcongr)
  · exact fun p _ _ ↦ log_natCast_nonneg p

/-- `θ x` is the log of the product of the primes up to `x`. -/
theorem theta_eq_log_primorial (x : ℝ) : θ x = log (primorial ⌊x⌋₊) := by
  unfold theta primorial
  rw [cast_prod, log_prod (fun p hp ↦ mod_cast (mem_filter.mp hp).2.pos.ne')]
  congr 1 with p
  simp_all [Prime.pos]

/-- Chebyshev's upper bound: `θ x ≤ c x` with the constant `c = log 4`. -/
theorem theta_le_log4_mul_x {x : ℝ} (hx : 0 ≤ x) : θ x ≤ log 4 * x := by
  rw [theta_eq_log_primorial]
  trans log (4 ^ ⌊x⌋₊)
  · gcongr <;> norm_cast
    exacts [primorial_pos _, primorial_le_four_pow _]
  rw [Real.log_pow, mul_comm]
  gcongr
  exact floor_le hx

end Chebyshev

namespace Nat
/-!
## Least common multiple of `{1,...,n}`

Basic facts about the least common multiple of the first `n` natural numbers
-/

/-- Least common multiple of `Icc 1 n`. -/
def lcmUpto (n : ℕ) : ℕ := (Icc 1 n).lcm id

theorem lcmUpto_ne_zero (n : ℕ) : lcmUpto n ≠ 0 := by simp [lcmUpto]

theorem lcmUpto_pos (n : ℕ) : 0 < lcmUpto n := pos_of_ne_zero <| lcmUpto_ne_zero n

theorem factorization_lcmUpto {n : ℕ} (hn : n ≠ 0) {p : ℕ} (hp : p.Prime) :
    (lcmUpto n).factorization p = Nat.log p n hp.one_lt hn := by
  rw [lcmUpto, Finset.factorization_lcm (fun _ _ ↦ by grind)]
  have := hp.one_lt
  refine le_antisymm ?_ ?_
  · simp only [Finset.sup_le_iff, mem_Icc, and_imp]
    exact fun m _ h ↦ Nat.le_log_of_pow_le this <|
      le_of_dvd (by grind) (ordProj_dvd m p) |>.trans h
  rcases le_or_gt p n with _ | h
  · have := Nat.pow_log_le_self this hn
    grw [← le_sup (b := p ^ Nat.log p n hp.one_lt hn) (by grind)]
    simp [hp]
  simp [Nat.log_of_lt this hn h]

theorem lcmUpto_dvd_factorial (n : ℕ) : lcmUpto n ∣ n ! := by
  simp +contextual [lcmUpto, dvd_factorial, Order.one_le_iff_pos]

theorem primeFactors_lcmUpto (n : ℕ) : primeFactors (lcmUpto n) = primesLE n := by
  ext p
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hp := prime_of_mem_primeFactors h
    rcases eq_or_ne n 0 with rfl | hn
    · simp [lcmUpto] at h
    rw [← support_factorization, Finsupp.mem_support_iff, factorization_lcmUpto hn hp, Ne,
      Nat.log_eq_zero_iff hp.one_lt hn, not_lt] at h
    exact mem_primesLE.mpr ⟨h, hp⟩
  · refine Prime.mem_primeFactors (prime_of_mem_primesLE h) (dvd_lcm ?_) <| lcmUpto_ne_zero n
    exact mem_Icc.mpr ⟨(prime_of_mem_primesLE h).one_le, le_of_mem_primesLE h⟩

theorem primorial_dvd_lcmUpto (n : ℕ) : primorial n ∣ lcmUpto n := by
  simp only [primorial]
  rw [← primesLE_eq_filter_range, ← primeFactors_lcmUpto]
  exact prod_primeFactors_dvd _

theorem lcmUpto_eq_prod (n : ℕ) :
    lcmUpto n = ∏ p ∈ primesLE n, p ^ ((lcmUpto n).factorization p) := by
  conv_lhs => rw [← prod_factorization_pow_eq_self (lcmUpto_ne_zero n)]
  rw [prod_factorization_eq_prod_primeFactors]
  congr
  exact primeFactors_lcmUpto n

/-- `lcmUpto n` is the product of the largest powers `p ^ Nat.log p n ≤ n` of the primes
`p ≤ n`. -/
theorem lcmUpto_eq_prod_pow_log (n : ℕ) :
    lcmUpto n = ∏ p ∈ (primesLE n).attach,
      (p : ℕ) ^ Nat.log p n (one_lt_of_mem_primesLE p.2) (ne_zero_of_mem_primesLE p.2) := by
  rw [lcmUpto_eq_prod, ← prod_attach (primesLE n)]
  exact prod_congr rfl fun p _ ↦ congrArg (p.1 ^ ·) <|
    factorization_lcmUpto (ne_zero_of_mem_primesLE p.2) (prime_of_mem_primesLE p.2)

theorem lcmUpto_eq_prod_pow_floor (n : ℕ) :
    lcmUpto n = ∏ p ∈ (primesLE n).attach,
      (p : ℕ) ^ ⌊Checked.div (Real.log n) (Real.log (p : ℕ))
        (Nat.Prime.log_ne_zero (prime_of_mem_primesLE p.2)).isUnit⌋₊ := by
  rw [lcmUpto_eq_prod, ← prod_attach (primesLE n)]
  refine prod_congr rfl fun p _ ↦ congrArg ((p : ℕ) ^ ·) ?_
  rw [factorization_lcmUpto (ne_zero_of_mem_primesLE p.2) (prime_of_mem_primesLE p.2),
    ← natFloor_logb_natCast (one_lt_of_mem_primesLE p.2) (ne_zero_of_mem_primesLE p.2),
    ← log_div_log]

end Nat

namespace Chebyshev

/-- The exponents `1 ≤ k ≤ Nat.log p n` are the `k ∈ Icc 1 n` with `p ^ k ≤ n`. -/
private theorem filter_pow_le_eq_Icc_log {n p : ℕ} (hp : 1 < p) (hn : n ≠ 0) :
    {k ∈ Icc 1 n | p ^ k ≤ n} = Icc 1 (Nat.log p n hp hn) := by
  ext k
  simp only [mem_filter, mem_Icc, Nat.le_log_iff_pow_le hp hn]
  exact ⟨fun h ↦ ⟨h.1.1, h.2⟩, fun h ↦ ⟨⟨h.1, (Nat.lt_pow_self hp).le.trans h.2⟩, h.2⟩⟩

theorem psi_eq_sum_mul_log_prime (n : ℕ) :
    ψ n = ∑ p ∈ (primesLE n).attach,
      Nat.log p n (one_lt_of_mem_primesLE p.2) (ne_zero_of_mem_primesLE p.2) * log (p : ℕ) :=
  calc
  _ = ∑ m ∈ Icc 1 n, Λ m := by simp [psi, ← Icc_add_one_left_eq_Ioc]
  _ = ∑ m ∈ ((Icc 1 n).filter Prime).biUnion
        fun p ↦ image (p ^ ·) {k ∈ Icc 1 n | p ^ k ≤ n}, Λ m := by
    refine (sum_subset (fun q hq ↦ ?_) fun x hx ↦ ?_).symm
    · simp only [mem_biUnion, mem_filter, mem_Icc, mem_image] at hq ⊢
      obtain ⟨p, ⟨_, hp⟩, k, ⟨_, hk⟩, rfl⟩ := hq
      exact ⟨Nat.one_le_pow _ _ hp.pos, hk⟩
    · simp only [mem_biUnion, mem_filter, mem_Icc, mem_image, not_exists, not_and, and_imp,
        vonMangoldt_eq_zero_iff, isPrimePow_nat_iff]
      contrapose!
      rintro ⟨p, k, hp, hk, rfl⟩
      simp only [mem_Icc] at hx
      have hpn : p ≤ n := (le_of_dvd (by lia) (dvd_pow_self p hk.ne')).trans hx.2
      have hkn : k ≤ n := (Nat.lt_pow_self hp.one_lt).le.trans hx.2
      exact ⟨p, ⟨hp.one_le, hpn, hp, ⟨k, ⟨by lia, hkn, hx.2, rfl⟩⟩⟩⟩
  _ = ∑ p ∈ Icc 1 n with p.Prime, ∑ q ∈ image (fun k ↦ p ^ k) {k ∈ Icc 1 n | p ^ k ≤ n}, Λ q := by
      rw [sum_biUnion <| by rw [pairwiseDisjoint_iff]; grind [Prime.pow_inj']]
  _ = ∑ p ∈ primesLE n, ∑ k ∈ Icc 1 n with p ^ k ≤ n, Λ (p ^ k) := by
      refine sum_congr (primesLE_eq_filter_Icc_one n).symm fun p hp ↦ ?_
      exact sum_image fun a _ b _ hab ↦ Nat.pow_right_injective (two_le_of_mem_primesLE hp) hab
  _ = ∑ p ∈ primesLE n, ∑ k ∈ Icc 1 n with p ^ k ≤ n, log p := by
      refine sum_congr rfl fun p hp ↦ sum_congr rfl fun k hk ↦ ?_
      rw [vonMangoldt_apply_pow (by grind), vonMangoldt_apply_prime <| prime_of_mem_primesLE hp]
  _ = ∑ p ∈ (primesLE n).attach, ∑ k ∈ Icc 1 n with (p : ℕ) ^ k ≤ n, log (p : ℕ) :=
      (sum_attach (primesLE n) fun p ↦ ∑ k ∈ Icc 1 n with p ^ k ≤ n, log p).symm
  _ = _ := by
      refine sum_congr rfl fun p _ ↦ ?_
      rw [filter_pow_le_eq_Icc_log (one_lt_of_mem_primesLE p.2) (ne_zero_of_mem_primesLE p.2)]
      simp

theorem psi_le_primeCounting_mul_log (n : ℕ) : ψ n ≤ (π n) * log n := by
  rw [psi_eq_sum_mul_log_prime, ← primesLE_card_eq_primeCounting, ← card_attach, ← nsmul_eq_mul,
    ← sum_const]
  gcongr with p
  refine Real.le_log_of_pow_le (mod_cast (prime_of_mem_primesLE p.2).pos) ?_
  exact_mod_cast Nat.pow_log_le_self (one_lt_of_mem_primesLE p.2) (ne_zero_of_mem_primesLE p.2)

theorem psi_le_primeCounting_mul_log' (x : ℝ) : ψ x ≤ (π ⌊x⌋₊) * log x := by
  grw [psi_eq_psi_coe_floor, psi_le_primeCounting_mul_log]
  rcases lt_or_ge x 1 with h | h
  · simp [floor_eq_zero.mpr h]
  gcongr
  · exact_mod_cast lt_of_add_one_le <| (one_le_floor_iff x).mpr h
  · exact floor_le (by positivity)

/-- `ψ n` is the logarithm of `lcmUpto n`. -/
theorem psi_eq_log_lcmUpto (n : ℕ) : ψ n = log (lcmUpto n) := by
  rw [lcmUpto_eq_prod_pow_log, cast_prod, log_prod fun p _ ↦ Nat.cast_ne_zero.mpr <|
    pow_ne_zero _ (prime_of_mem_primesLE p.2).ne_zero]
  simp [psi_eq_sum_mul_log_prime]

/-- `lcmUpto n` is divisible by `choose n k` for all `k ≤ n` -/
theorem choose_dvd_lcmUpto {n k : ℕ} (hkn : k ≤ n) : choose n k ∣ lcmUpto n := by
  rw [← factorization_prime_le_iff_dvd (choose_ne_zero hkn) (lcmUpto_ne_zero n)]
  intro p hp
  rcases eq_or_ne n 0 with rfl | hn
  · simp [Nat.le_zero.mp hkn]
  rw [factorization_lcmUpto hn hp]
  exact factorization_choose_le_log hp.one_lt hn

theorem two_pow_le_mul_lcmUpto (n : ℕ) : 2 ^ n ≤ (n + 1) * lcmUpto n := calc
  _ = ∑ m ∈ range (n + 1), n.choose m := (sum_range_choose _).symm
  _ ≤ ∑ k ∈ range (n + 1), lcmUpto n := by
    gcongr with k hk
    exact le_of_dvd (lcmUpto_pos n) (choose_dvd_lcmUpto <| by grind)
  _ = _ := by simp

/-!
## Relating `ψ` and `θ`

We isolate the contributions of different prime powers to `ψ` and use this to show that `ψ` and `θ`
are close.
-/

/-- A sum over prime powers may be written as a double sum over exponents and then primes. -/
theorem sum_PrimePow_eq_sum_sum' {R : Type*} [AddCommMonoid R] (f : ℕ → R) {x : ℝ} (hx : 0 ≤ x)
  {N : ℕ} (hN : ⌊log x / log 2⌋₊ ≤ N) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊ with IsPrimePow n, f n
      = ∑ k ∈ range N, ∑ p ∈ Ioc 0 ⌊x ^ ((k : ℝ) + 1)⁻¹⌋₊ with p.Prime, f (p ^ (k + 1)) := by
  have hroot (k p : ℕ) : p ≤ ⌊x ^ ((k : ℝ) + 1)⁻¹⌋₊ ↔ (p : ℝ) ^ (k + 1) ≤ x := by
    rw [le_floor_iff (rpow_nonneg hx _),
      le_rpow_inv_iff_of_pos (by positivity) hx (by positivity), ← Nat.cast_succ, rpow_natCast]
  trans ∑ ⟨k, p⟩ ∈ range N ×ˢ (Ioc 0 ⌊x⌋₊).filter Nat.Prime
    with p ≤ ⌊x ^ ((k : ℝ) + 1)⁻¹⌋₊, f (p ^ (k + 1))
  · refine (sum_bij (i := fun ⟨k, p⟩ _ ↦ p ^ (k + 1)) ?_ ?_ ?_ ?_).symm
    · rintro ⟨k, p⟩ hkp
      obtain ⟨hkp, hle⟩ := mem_filter.mp hkp
      have hp := (mem_filter.mp (mem_product.mp hkp).2).2
      refine mem_filter.mpr ⟨mem_Ioc.mpr ⟨pow_pos hp.pos _, ?_⟩,
        (isPrimePow_pow_iff (Nat.succ_ne_zero k)).2 hp.isPrimePow⟩
      exact (le_floor_iff hx).2 (by simpa only [cast_pow] using (hroot k p).1 hle)
    · rintro ⟨k, p⟩ hkp ⟨l, q⟩ hlq h
      have hp := (mem_filter.mp (mem_product.mp (mem_filter.mp hkp).1).2).2
      have hq := (mem_filter.mp (mem_product.mp (mem_filter.mp hlq).1).2).2
      obtain ⟨heq, hkl⟩ := hp.pow_inj' hq (by omega) (by omega) h
      exact Prod.ext (Nat.add_right_cancel hkl) heq
    · intro b hb
      obtain ⟨hb, p, l, hp, hl, rfl⟩ := mem_filter.mp hb
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hl.ne'
      have hbx : (p : ℝ) ^ (k + 1) ≤ x := by
        simpa only [cast_pow] using (le_floor_iff hx).1 (mem_Ioc.mp hb).2
      have hk : k + 1 ≤ ⌊log x / log 2⌋₊ := by
        apply le_floor
        rw [le_div_iff₀ (log_pos (by norm_num)), ← Real.log_pow]
        gcongr
        exact (pow_le_pow_left₀ (by norm_num) (mod_cast hp.nat_prime.two_le) _).trans hbx
      have hpx : p ≤ ⌊x⌋₊ := (le_floor_iff hx).2 <|
        (le_self_pow₀ (mod_cast hp.nat_prime.one_le) (by omega)).trans hbx
      exact ⟨(k, p), mem_filter.mpr ⟨mem_product.mpr ⟨mem_range.mpr (hk.trans hN),
        mem_filter.mpr ⟨mem_Ioc.mpr ⟨hp.nat_prime.pos, hpx⟩, hp.nat_prime⟩⟩,
        (hroot k p).2 hbx⟩, rfl⟩
    · intro _ _
      rfl
  · rw [sum_filter, sum_product]
    refine sum_congr rfl fun k _ ↦ ?_
    simp only [sum_ite, not_le, sum_const_zero, add_zero]
    congr 1
    ext p
    simp only [mem_filter, mem_Ioc]
    refine ⟨fun h ↦ ⟨⟨h.1.1.1, h.2⟩, h.1.2⟩, ?_⟩
    rintro ⟨⟨hp, hle⟩, hprime⟩
    have hpx : p ≤ ⌊x⌋₊ := (le_floor_iff hx).2 <|
      (le_self_pow₀ (mod_cast hprime.one_le) (by omega)).trans ((hroot k p).1 hle)
    exact ⟨⟨⟨hp, hpx⟩, hprime⟩, hle⟩

theorem sum_PrimePow_eq_sum_sum {R : Type*} [AddCommMonoid R] (f : ℕ → R) {x : ℝ} (hx : 0 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊ with IsPrimePow n, f n
      = ∑ k ∈ range ⌊log x / log 2⌋₊,
          ∑ p ∈ Ioc 0 ⌊x ^ ((k : ℝ) + 1)⁻¹⌋₊ with p.Prime, f (p ^ (k + 1)) :=
  sum_PrimePow_eq_sum_sum' f hx (le_refl _)

theorem psi_eq_sum_theta' {x : ℝ} (hx : 0 ≤ x) {N : ℕ} (hN : ⌊log x / log 2⌋₊ ≤ N) :
    ψ x = ∑ n ∈ range N, θ (x ^ ((n : ℝ) + 1)⁻¹) := by
  rw [psi, ← sum_filter_of_ne (p := IsPrimePow) fun _ _ h => vonMangoldt_ne_zero_iff.1 h,
    sum_PrimePow_eq_sum_sum' _ hx hN]
  apply sum_congr rfl fun _ _ ↦ sum_congr rfl fun _ hp ↦ ?_
  rw [vonMangoldt_apply_pow (Nat.succ_ne_zero _), vonMangoldt_apply_prime (mem_filter.1 hp).2]

theorem psi_eq_sum_theta {x : ℝ} (hx : 0 ≤ x) :
    ψ x = ∑ n ∈ range ⌊log x / log 2⌋₊, θ (x ^ ((n : ℝ) + 1)⁻¹) :=
  psi_eq_sum_theta' hx (le_refl _)

theorem psi_eq_theta_add_sum_theta' {x : ℝ} (hx : 2 ≤ x) {N : ℕ} (hN : ⌊log x / log 2⌋₊ ≤ N) :
    ψ x = θ x + ∑ n ∈ range (N - 1), θ (x ^ ((n : ℝ) + 2)⁻¹) := by
  have hN_pos : 1 ≤ N := by
    apply le_trans _ hN
    rw [le_floor_iff' one_ne_zero, le_div_iff₀ (by positivity), cast_one, one_mul]
    gcongr
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  rw [psi_eq_sum_theta' (by linarith) hN, sum_range_succ', add_comm]
  simp only [cast_zero, zero_add, inv_one₀, rpow_one, Nat.succ_sub_one, cast_succ, add_assoc]
  norm_num

theorem psi_eq_theta_add_sum_theta {x : ℝ} (hx : 2 ≤ x) :
    ψ x = θ x + ∑ n ∈ range (⌊log x / log 2⌋₊ - 1), θ (x ^ ((n : ℝ) + 2)⁻¹) :=
  psi_eq_theta_add_sum_theta' hx (le_refl _)

theorem theta_le_psi (x : ℝ) : θ x ≤ ψ x := by
  by_cases! h : x < 2
  · rw [theta_eq_zero_of_lt_two h, psi_eq_zero_of_lt_two h]
  rw [psi_eq_theta_add_sum_theta h]
  simp only [le_add_iff_nonneg_right]
  exact sum_nonneg fun _ _ ↦ theta_nonneg _

/-- `|ψ x - θ x| ≤ c √ x log x` with an explicit constant c.  To remove the log, see
`psi_sub_theta_le_mul_sqrt`. -/
theorem abs_psi_sub_theta_le_sqrt_mul_log {x : ℝ} (hx : 1 ≤ x) :
    |ψ x - θ x| ≤ 2 * x.sqrt * x.log := by
  by_cases! hx : x < 2
  · rw [psi_eq_zero_of_lt_two hx, theta_eq_zero_of_lt_two hx, sub_zero, abs_zero]
    bound
  rw [psi_eq_theta_add_sum_theta hx, add_sub_cancel_left]
  apply le_trans <| abs_sum_le_sum_abs ..
  simp_rw [abs_of_nonneg <| theta_nonneg _]
  trans ∑ i ∈ range (⌊log x / log 2⌋₊ - 1), log 4 * x.sqrt
  · gcongr with i
    apply le_trans (theta_le_log4_mul_x (rpow_nonneg (by linarith) _))
    rw [sqrt_eq_rpow, one_div₀]
    refine mul_le_mul_of_nonneg_left (rpow_le_rpow_of_exponent_le (by linarith) ?_) (by positivity)
    exact (inv_le_inv₀ (by positivity) two_pos).2 (by linarith [Nat.cast_nonneg (α := ℝ) i])
  simp only [sum_const, card_range, nsmul_eq_mul]
  calc
  _ ≤ (log x / log 2) * (log 4 * √x) := by
    gcongr
    rw [cast_sub]
    · trans ↑⌊log x / log 2⌋₊
      · linarith
      · exact floor_le (by bound)
    apply le_floor
    norm_cast
    apply one_le_div _ |>.mpr <;> bound
  _ = (log 4 / log 2) * x.sqrt * x.log := by field
  _ = _ := by
    congr
    rw [(by norm_num : (4 : ℝ) = 2 ^ 2), Real.log_pow]
    field

/-- Explicit upper bound on `ψ`. -/
theorem psi_le {x : ℝ} (hx : 1 ≤ x) :
    ψ x ≤ log 4 * x + 2 * x.sqrt * x.log := by
  calc
  _ = ψ x - θ x + θ x := by ring
  _ ≤ 2 * x.sqrt * x.log + log 4 * x := by
    gcongr
    · exact le_trans (le_abs_self _) (abs_psi_sub_theta_le_sqrt_mul_log hx)
    · exact theta_le_log4_mul_x (by linarith)
  _ = _ := by ring

/-- Chebyshev's bound `ψ x ≤ c x` with an explicit constant.
Note that `Chebyshev.psi_le` gives a sharper bound with a better main term. -/
theorem psi_le_const_mul_self {x : ℝ} (hx : 0 ≤ x) :
    ψ x ≤ (log 4 + 4) * x := by
  by_cases! hx : x < 1
  · rw [psi_eq_zero_of_lt_two (by linarith)]
    bound
  apply le_trans (psi_le hx)
  rw [add_mul]
  gcongr 1
  grw [sqrt_eq_rpow, log_le_rpow_div (ε := 1 / 2) (by linarith) (by linarith), ← mul_div_assoc₀,
    ← mul_one_div₀]
  nth_rw 2 [mul_assoc]
  rw [← rpow_add (by linarith)]
  norm_num
  linarith

/-- `ψ - θ` is the sum of `Λ` over non-primes. -/
theorem psi_sub_theta_eq_sum_not_prime (x : ℝ) :
    ψ x - θ x = ∑ n ∈ Ioc 0 ⌊x⌋₊ with ¬n.Prime, vonMangoldt n := by
  rw [psi, theta, sum_filter, sum_filter, ← sum_sub_distrib]
  refine sum_congr rfl fun n hn ↦ ?_
  split_ifs with h
  · simp [h, vonMangoldt_apply_prime]
  · simp

/-- The Chebyshev lower bound for `ψ`. -/
theorem psi_ge (n : ℕ) : n * log 2 - log (n + 1) ≤ ψ n := by
  rw [tsub_le_iff_left, psi_eq_log_lcmUpto, ← log_pow 2,
    ← log_mul (by positivity) (by simp [lcmUpto_ne_zero])]
  exact log_le_log (by positivity) <| mod_cast two_pow_le_mul_lcmUpto n

theorem psi_ge' {x : ℝ} (hx : 0 ≤ x) : (x - 1) * log 2 - log (x + 2) ≤ ψ x := by
  grw [psi_eq_psi_coe_floor, ← psi_ge]
  gcongr
  · exact (Nat.sub_one_lt_floor x).le
  · exact floor_le hx
  · exact one_le_two

theorem psi_sub_theta_le {x : ℝ} (hx : 1 ≤ x) : ψ x - θ x ≤ 2 * √x * log x := by
  grw [← abs_psi_sub_theta_le_sqrt_mul_log hx]
  exact le_abs_self _

/-- The Chebyshev lower bound for `θ`. -/
theorem theta_ge (n : ℕ) : n * log 2 - log (n + 1) - 2 * √n * log n ≤ θ n := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  linarith [psi_ge n, psi_sub_theta_le (x := n) (mod_cast (one_le_of_lt hn))]

theorem theta_ge' {x : ℝ} (hx : 1 ≤ x) :
    (x - 1) * log 2 - log (x + 2) - 2 * √x * log x ≤ θ x := by
  grw [psi_ge' (by linarith)]
  linarith [psi_sub_theta_le hx]

section CostaPereira

/-! ## The Costa-Pereira inequalities

The Costa-Pereira inequalities give explicit upper and lower bounds on the difference
`ψ x - θ x`, namely that they lie between `ψ x^(1/2) + ψ x^(1/3) + ψ x^(1/7)` and
`ψ x^(1/2) + ψ x^(1/3) + ψ x^(1/5)`.  These are useful for applications in explicit
analytic number theory. -/

variable (x : ℝ) (n : ℕ)

-- Index by the predecessor of the positive root degree.
private noncomputable def b := θ (x ^ ((n : ℝ) + 1)⁻¹)

private noncomputable def c := b x (6 * n + 4) - b x (6 * n + 5) + b x (6 * n + 6)

private theorem b_antitone (hx : 0 ≤ x) : Antitone (b x) := by
  intro n m hnm
  unfold b
  rcases le_or_gt x 1 with h | h
  · repeat rw [theta_eq_zero_of_le_one (rpow_le_one hx h (by positivity))]
  apply theta_mono (monotone_rpow_of_base_ge_one h.le _)
  exact (inv_le_inv₀ (by positivity) (by positivity)).2
    (add_le_add_left (Nat.cast_le.mpr hnm) _)

private theorem psi_pow_eq_sum_b (hx : 0 ≤ x) : ∃ M, ∀ N ≥ M,
    ψ (x ^ ((n : ℝ) + 1)⁻¹) = ∑ k ∈ range N, b x ((n + 1) * k + n) := by
  have hroot : 0 ≤ x ^ ((n : ℝ) + 1)⁻¹ := by positivity
  use ⌊log (x ^ ((n : ℝ) + 1)⁻¹) / log 2⌋₊
  intro N hN
  rw [psi_eq_sum_theta' hroot hN]
  refine sum_congr rfl fun k _ ↦ ?_
  unfold b
  rw [← rpow_mul hx]
  congr 1
  push_cast
  field_simp
  ring

private theorem sum_b_eq_b_add_sum_add_sum_add_sum (N : ℕ) :
    ∑ n ∈ range (1 + 6 * N), b x n =
      b x 0 +
      ∑ n ∈ range (3 * N), b x (2 * n + 1) +
      ∑ n ∈ range (2 * N), b x (3 * n + 2) +
      ∑ n ∈ range N, c x n := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 1 + 6 * (N + 1) = (1 + 6 * N) + 1 + 1 + 1 + 1 + 1 + 1 by ring,
      show 3 * (N + 1) = 3 * N + 1 + 1 + 1 by ring,
      show 2 * (N + 1) = 2 * N + 1 + 1 by ring]
    simp only [sum_range_succ, ih, c]
    ring_nf

private theorem psi_sub_theta_bounds {x : ℝ} (hx : 0 ≤ x) :
    ψ x - θ x ≤ ψ (x ^ (2 : ℝ)⁻¹) + ψ (x ^ (3 : ℝ)⁻¹) + ψ (x ^ (5 : ℝ)⁻¹) ∧
    ψ (x ^ (2 : ℝ)⁻¹) + ψ (x ^ (3 : ℝ)⁻¹) + ψ (x ^ (7 : ℝ)⁻¹) ≤ ψ x - θ x := by
  obtain ⟨N₁, h1⟩ := psi_pow_eq_sum_b x 0 hx
  obtain ⟨N₂, h2⟩ := psi_pow_eq_sum_b x 1 hx
  obtain ⟨N₃, h3⟩ := psi_pow_eq_sum_b x 2 hx
  obtain ⟨N₅, h5⟩ := psi_pow_eq_sum_b x 4 hx
  obtain ⟨N₇, h7⟩ := psi_pow_eq_sum_b x 6 hx
  let N := N₁ + N₂ + N₃ + N₅ + N₇
  specialize h1 (1 + 6 * N) (by lia)
  specialize h2 (3 * N) (by lia)
  specialize h3 (2 * N) (by lia)
  specialize h5 N (by lia)
  specialize h7 N (by lia)
  have h_upper : ∑ n ∈ range N, c x n ≤ ∑ n ∈ range N, b x (5 * n + 4) := by
    apply sum_le_sum
    intro n _
    unfold c
    linarith [b_antitone x hx (show 6 * n + 5 ≤ 6 * n + 6 by omega),
      b_antitone x hx (show 5 * n + 4 ≤ 6 * n + 4 by omega)]
  have h_lower : ∑ n ∈ range N, b x (7 * n + 6) ≤ ∑ n ∈ range N, c x n := by
    apply sum_le_sum
    intro n _
    unfold c
    linarith [b_antitone x hx (show 6 * n + 4 ≤ 6 * n + 5 by omega),
      b_antitone x hx (show 6 * n + 6 ≤ 7 * n + 6 by omega)]
  have hb₀ : b x 0 = θ x := by simp [b]
  norm_num at h1 h2 h3 h5 h7
  rw [sum_b_eq_b_add_sum_add_sum_add_sum, hb₀] at h1
  exact ⟨by linarith, by linarith⟩

theorem psi_sub_theta_le_psi_add_psi_add_psi (x : ℝ) :
    ψ x - θ x ≤ ψ (x ^ (2 : ℝ)⁻¹) + ψ (x ^ (3 : ℝ)⁻¹) + ψ (x ^ (5 : ℝ)⁻¹) := by
  rcases le_total x 0 with hx | hx
  · grind [theta_eq_zero_iff, psi_eq_zero_iff, psi_nonneg]
  · exact (psi_sub_theta_bounds hx).1

theorem psi_sub_theta_ge_psi_add_psi_add_psi {x : ℝ} (hx : 0 ≤ x) :
    ψ (x ^ (2 : ℝ)⁻¹) + ψ (x ^ (3 : ℝ)⁻¹) + ψ (x ^ (7 : ℝ)⁻¹) ≤ ψ x - θ x :=
  (psi_sub_theta_bounds hx).2

/-- `ψ x = θ x + O( √x )`. -/
theorem psi_sub_theta_le_mul_sqrt : ∃ C, ∀ x, ψ x - θ x ≤ C * x.sqrt := by
  use (log 4 + 4) * 3
  intro x
  rcases le_total x 1 with h | h
  · rw [theta_eq_zero_of_le_one h, psi_eq_zero_of_le_one h, sub_self]; positivity
  have (n : ℕ) (hn : 2 ≤ n) :
      ψ (x ^ (Checked.inv (n : ℝ) (Nat.cast_ne_zero.mpr (by omega)).isUnit)) ≤
        (log 4 + 4) * x.sqrt := by
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    grw [psi_le_const_mul_self (by positivity), sqrt_eq_rpow x, one_div₀]
    gcongr
  linarith [psi_sub_theta_le_psi_add_psi_add_psi x, this 2 (le_refl _), this 3 (by norm_num),
    this 5 (by norm_num)]

open Asymptotics Filter in
theorem isBigO_psi_sub_theta_sqrt : IsBigO atTop (ψ - θ) sqrt := by
  simp_rw [isBigO_iff, Pi.sub_apply, norm_eq_abs, eventually_atTop]
  obtain ⟨C, hC⟩ := psi_sub_theta_le_mul_sqrt
  refine ⟨C, 0, fun x _ ↦ ?_⟩
  have := theta_le_psi x
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  exact hC x

end CostaPereira

section PrimeCounting

/-! ## Relation to prime counting

We relate `θ` to the prime counting function `π`.-/

open Asymptotics Filter MeasureTheory
open scoped Topology

private lemma exists_invLog_representative :
    ∃ F : ℝ → ℝ,
      (∀ t : Set.Ioi (1 : ℝ), F t.val = Checked.inv (log t.val) (log_pos t.property).ne'.isUnit) ∧
      (∀ t : Set.Ioi (1 : ℝ), HasDerivAt F
        (-Checked.inv (t.val * log t.val ^ 2)
          ((lt_trans (show (0 : ℝ) < 1 from zero_lt_one) t.property).ne'.isUnit.mul
            ((log_pos t.property).ne'.isUnit.pow 2)))
        t.val) ∧
      ContDiffOn ℝ 1 F (Set.Ioi 1) := by
  classical
  let D := Set.Ioi (1 : ℝ)
  let L (t : D) : ℝ := Checked.inv (log t.val) (log_pos t.property).ne'.isUnit
  let F : ℝ → ℝ := Function.extend Subtype.val L 0
  have hF (t : D) : F t.val = L t := Subtype.val_injective.extend_apply _ _ _
  refine ⟨F, hF, ?_, ?_⟩
  · intro t
    let q (y : D) : {w : ℝ // IsUnit (log w)} := ⟨y.val, (log_pos y.property).ne'.isUnit⟩
    have hq : Continuous q := continuous_subtype_val.subtype_mk _
    have hd := (Real.hasDerivAt_inv_log (q t)).hasFDerivAt.comp_tendsto q
      (hq.continuousAt.tendsto.prodMap (tendsto_pure_pure q t))
    have hderiv : HasFDerivAt (fun y : D ↦ F y.val)
        (ContinuousLinearMap.toSpanSingleton ℝ (-Checked.inv (t.val * log t.val ^ 2)
          ((lt_trans (show (0 : ℝ) < 1 from zero_lt_one) t.property).ne'.isUnit.mul
            ((log_pos t.property).ne'.isUnit.pow 2))))
        t Subtype.val := by
      simpa only [HasFDerivAt, q, Function.comp_def, hF, L, div_eq_mul_inv₀, mul_inv₀, neg_mul]
        using hd
    simpa only [ContinuousLinearMap.toSpanSingleton_apply, one_smul] using
      hasFDerivAt_iff_hasDerivAt.mp (hderiv.of_restrict (coord := id) (x := t)
        (isOpen_Ioi.mem_nhds t.property))
  · refine ContDiffOn.inv ((Real.contDiffOn_log (n := 1)).mono ?_) ?_
    · exact fun t ht ↦ (lt_trans zero_lt_one ht).ne'
    · exact fun t ht ↦ ⟨(log_pos ht).ne'.isUnit, hF ⟨t, ht⟩⟩

/-- Integrability of the Chebyshev kernel on its actual interval domain. -/
theorem integrableOn_theta_div_id_mul_log_sq (x : ℝ) :
    Integrable (fun t : Set.Icc (2 : ℝ) x ↦ Checked.div (θ t.val) (t.val * log t.val ^ 2) (by
      have ht : 1 < t.val := one_lt_two.trans_le (Set.mem_Icc.mp t.property).1
      exact (lt_trans (show (0 : ℝ) < 1 from zero_lt_one) ht).ne'.isUnit.mul
        ((log_pos ht).ne'.isUnit.pow 2))) (volume.comap Subtype.val) := by
  obtain ⟨F, _, hFd, hFc⟩ := exists_invLog_representative
  have hDom : Set.Icc (2 : ℝ) x ⊆ Set.Ioi 1 := fun _ ht ↦ one_lt_two.trans_le ht.1
  have hInt : IntegrableOn (deriv F) (Set.Icc 2 x) :=
    ((hFc.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl).mono hDom).integrableOn_Icc
  let a : ℕ → ℝ := Set.indicator (Set.ofPred Nat.Prime) (fun n ↦ log n)
  have hmul := integrableOn_mul_sum_Icc a (m := 0) (by norm_num : (0 : ℝ) ≤ 2) hInt
  have hpull := (integrableOn_iff_comap_subtypeVal measurableSet_Icc).mp hmul
  refine hpull.neg.congr (.of_forall fun t ↦ ?_)
  have he : ∑ n ∈ Icc 0 ⌊t.val⌋₊, a n = θ t.val := by
    simp [a, Set.indicator_apply, theta_eq_sum_Icc, sum_filter]
  have ht : 1 < t.val := hDom t.property
  have hd : deriv F t.val = -Checked.inv (t.val * log t.val ^ 2)
      ((lt_trans (show (0 : ℝ) < 1 from zero_lt_one) ht).ne'.isUnit.mul
        ((log_pos ht).ne'.isUnit.pow 2)) := (hFd ⟨t.val, ht⟩).deriv
  change -(deriv F t.val * (∑ n ∈ Icc 0 ⌊t.val⌋₊, a n)) = _
  simp only [he, hd, neg_mul, neg_neg, div_eq_inv_mul₀]


/-- Expresses the prime counting function `π` in terms of `θ` by using Abel summation. -/
theorem primeCounting_eq_theta_div_log_add_integral {x : ℝ} (hx : 2 ≤ x) :
    π ⌊x⌋₊ =
      Checked.div (θ x) (log x) (log_pos (one_lt_two.trans_le hx)).ne'.isUnit +
      intervalIntegral.integralSubtypeOn (fun t : Set.Ioi (1 : ℝ) ↦
        Checked.div (θ t.val) (t.val * log t.val ^ 2)
          ((lt_trans (show (0 : ℝ) < 1 from zero_lt_one) t.property).ne'.isUnit.mul
            ((log_pos t.property).ne'.isUnit.pow 2)))
        2 x := by
  obtain ⟨F, hF, hFd, hFc⟩ := exists_invLog_representative
  have hDom : Set.Icc (2 : ℝ) x ⊆ Set.Ioi 1 := fun _ ht ↦ one_lt_two.trans_le ht.1
  have hInt : IntegrableOn (deriv F) (Set.Icc 2 x) :=
    ((hFc.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl).mono hDom).integrableOn_Icc
  have hAE : ∀ᵐ u ∂volume.restrict (Set.uIcc (2 : ℝ) x), u ∈ Set.Ioi 1 := by
    refine (ae_restrict_iff' measurableSet_uIcc).mpr (.of_forall fun u hu ↦ hDom ?_)
    simpa only [Set.uIcc_of_le hx] using hu
  have hint (g : ℝ → ℝ) : (∫ u in (2 : ℝ)..x, deriv F u * g u) =
      -intervalIntegral.integralSubtypeOn (fun t : Set.Ioi (1 : ℝ) ↦
        Checked.div (g t.val) (t.val * log t.val ^ 2)
          ((lt_trans (show (0 : ℝ) < 1 from zero_lt_one) t.property).ne'.isUnit.mul
            ((log_pos t.property).ne'.isUnit.pow 2)))
        2 x := by
    have he : (fun t : Set.Ioi (1 : ℝ) ↦ -(deriv F t.val * g t.val)) =
        (fun t : Set.Ioi (1 : ℝ) ↦
          Checked.div (g t.val) (t.val * log t.val ^ 2)
            ((lt_trans (show (0 : ℝ) < 1 from zero_lt_one) t.property).ne'.isUnit.mul
              ((log_pos t.property).ne'.isUnit.pow 2))) := by
      funext t
      simp only [(hFd t).deriv, neg_mul, neg_neg, div_eq_inv_mul₀]
    rw [← he, intervalIntegral.integral_subtypeOn_eq_integral measurableSet_Ioi
      (fun u ↦ -(deriv F u id * g u)) hAE, intervalIntegral.integral_neg, neg_neg]
  simp only [primeCounting, primeCounting', count_eq_card_filter_range]
  rw [card_eq_sum_ones, range_succ_eq_Icc_zero, sum_filter]
  push_cast
  let a : ℕ → ℝ := Set.indicator (Set.ofPred Nat.Prime) (fun n ↦ log n)
  trans ∑ n ∈ Icc 0 ⌊x⌋₊, F n * a n
  · refine sum_congr rfl fun n _ ↦ ?_
    split_ifs with hp
    · have hn : 1 < (n : ℝ) := by exact_mod_cast hp.one_lt
      have hFn : F n = Checked.inv (log n) (log_pos hn).ne'.isUnit := hF ⟨n, hn⟩
      simp [a, hp, hFn, inv_mul_cancel₀]
    · simp [a, hp]
  have hSum (t : ℝ) : ∑ n ∈ Icc 0 ⌊t⌋₊, a n = θ t := by
    simp [a, Set.indicator_apply, theta_eq_sum_Icc, sum_filter]
  have hFx : F x = Checked.inv (log x) (log_pos (one_lt_two.trans_le hx)).ne'.isUnit :=
    hF ⟨x, one_lt_two.trans_le hx⟩
  rw [sum_mul_eq_sub_integral_mul₁ a (by simp [a]) (by simp [a]) x
    (fun u hu ↦ (hFd ⟨u, hDom hu⟩).differentiableAt) hInt,
    ← intervalIntegral.integral_of_le hx, hint]
  simp_rw [hSum, hFx, div_eq_inv_mul₀, sub_neg_eq_add]


/-- Expresses the Chebyshev theta function `ϑ` in terms of `π` by using Abel summation. -/
theorem theta_eq_primeCounting_mul_log_sub_integral {x : ℝ} (hx : 2 ≤ x) :
    θ x = π ⌊x⌋₊ * log x - intervalIntegral.integralSubtype
      (fun t : Set.uIcc (2 : ℝ) x ↦ Checked.div (π ⌊t.val⌋₊ : ℝ) t.val (by
        have ht : t.val ∈ Set.Icc (2 : ℝ) x := by simpa only [Set.uIcc_of_le hx] using t.property
        exact (lt_of_lt_of_le two_pos (Set.mem_Icc.mp ht).1).ne'.isUnit)) := by
  -- Rewrite in a form to which Abel summation can be applied
  rw [theta_eq_sum_Icc, sum_filter]
  let a : ℕ → ℝ := Set.indicator (Set.ofPred Nat.Prime) (fun n ↦ 1)
  trans ∑ n ∈ Icc 0 ⌊x⌋₊, log n * a n
  · refine sum_congr rfl fun n _ ↦ ?_
    split_ifs with h <;> simp [a, h]
  rw [sum_mul_eq_sub_integral_mul₁ a (by simp [a, not_prime_zero])
    (by simp [a, not_prime_one]) x (fun z hz ↦
      (Real.hasDerivAt_log (hx := (lt_of_lt_of_le two_pos hz.1).ne'.isUnit)).differentiableAt)
    ?hint,
    ← intervalIntegral.integral_of_le hx]
  case hint =>
    refine ((Real.contDiffOn_log (n := 1)).continuousOn_deriv_of_isOpen
      isOpen_compl_singleton le_rfl).mono (t := Set.Icc (2 : ℝ) x) ?_ |>.integrableOn_Icc
    exact fun z hz ↦ (lt_of_lt_of_le two_pos hz.1).ne'
  -- Rewrite the derivative inside the integral
  simp only [primeCounting, primeCounting', count_eq_card_filter_range]
  have int_deriv (f : ℝ → ℝ) : (∫ u in 2..x, deriv log u * f u) =
      intervalIntegral.integralSubtype (fun t : Set.uIcc (2 : ℝ) x ↦
        Checked.div (f t.val) t.val (by
          have ht : t.val ∈ Set.Icc (2 : ℝ) x := by
            simpa only [Set.uIcc_of_le hx] using t.property
          exact (lt_of_lt_of_le two_pos (Set.mem_Icc.mp ht).1).ne'.isUnit)) := by
    refine (intervalIntegral.integral_subtype_eq_integral (a := (2 : ℝ)) (b := x)
      (fun u ↦ deriv log u id * f u)).symm.trans ?_
    apply congrArg intervalIntegral.integralSubtype
    funext t
    have ht : t.val ∈ Set.Icc (2 : ℝ) x := by simpa only [Set.uIcc_of_le hx] using t.property
    have hunit : IsUnit t.val := (lt_of_lt_of_le two_pos ht.1).ne'.isUnit
    simp only [Real.deriv_log t.val (hx := hunit), div_eq_inv_mul₀]
  rw [int_deriv]
  simp [a, Set.indicator_apply, range_succ_eq_Icc_zero, mul_comm]

private noncomputable abbrev divLog (a : ℝ) (x : Set.Ioi (1 : ℝ)) : ℝ :=
  Checked.div a (log x.val) (log_pos x.property).ne'.isUnit

private noncomputable abbrev divLogSq (a : ℝ) (x : Set.Ioi (1 : ℝ)) : ℝ :=
  Checked.div a (log x.val ^ 2) ((log_pos x.property).ne'.isUnit.pow 2)

private noncomputable abbrev thetaDivIdMulLogSq (x : Set.Ioi (1 : ℝ)) : ℝ :=
  Checked.div (θ x.val) (x.val * log x.val ^ 2)
    ((zero_lt_one.trans x.property).ne'.isUnit.mul ((log_pos x.property).ne'.isUnit.pow 2))

private abbrev twoAboveOne : Set.Ioi (1 : ℝ) := ⟨2, Set.mem_Ioi.mpr (by norm_num)⟩

private lemma uIcc_subset_one_lt (a b : Set.Ioi (1 : ℝ)) :
    Set.uIcc a.val b.val ⊆ Set.Ioi 1 :=
  fun _ ht ↦ (lt_min a.property b.property).trans_le ht.1

private lemma exists_invLogSq_representative :
    ∃ F : ℝ → ℝ, (∀ t : Set.Ioi (1 : ℝ), F t.val = divLogSq 1 t) ∧ ContinuousOn F (Set.Ioi 1) := by
  obtain ⟨F, hF, _, hc⟩ := exists_invLog_representative
  refine ⟨fun t ↦ F t ^ 2, fun t ↦ ?_, hc.continuousOn.pow 2⟩
  simp only [hF t, divLogSq, inv_pow₀, one_div₀]

private lemma integral_subtypeOn_Ioi_eq_integral (f : Set.Ioi (1 : ℝ) → ℝ) (F : ℝ → ℝ)
    (hF : ∀ t : Set.Ioi (1 : ℝ), F t.val = f t) (a b : Set.Ioi (1 : ℝ)) :
    intervalIntegral.integralSubtypeOn f a.val b.val = ∫ t in a.val..b.val, F t := by
  simpa only [hF] using intervalIntegral.integral_subtypeOn_eq_integral (a := a.val) (b := b.val)
    measurableSet_Ioi F ((ae_restrict_iff' measurableSet_uIcc).2
      (.of_forall fun _ ht ↦ uIcc_subset_one_lt a b ht))

/-- The reciprocal squared logarithm is integrable over closed intervals above one. -/
theorem integrable_uIcc_one_div_log_sq (a b : Set.Ioi (1 : ℝ)) :
    Integrable (fun t : Set.uIcc a.val b.val ↦ Checked.div 1 (log t.val ^ 2) (by
      have ht : 1 < t.val := (lt_min a.property b.property).trans_le t.property.1
      exact (log_pos ht).ne'.isUnit.pow 2))
      (volume.comap Subtype.val) := by
  obtain ⟨F, hF, hc⟩ := exists_invLogSq_representative
  let q (t : Set.uIcc a.val b.val) : Set.Ioi (1 : ℝ) :=
    ⟨t.val, uIcc_subset_one_lt a b t.property⟩
  have ht := (hc.mono (uIcc_subset_one_lt a b)).domRestrict
  have he : (fun t : Set.uIcc a.val b.val ↦ F t.val) = fun t ↦ divLogSq 1 (q t) :=
    funext fun t ↦ hF (q t)
  apply intervalIntegral.integrable_subtype_uIcc (μ := volume)
  exact he ▸ ht

/-- Simple bound on the integral from monotonicity.
We will bound the integral on 2..x by splitting into two intervals and using this result on both. -/
private theorem integral_1_div_log_sq_le {a b : Set.Ioi (1 : ℝ)} (hab : a ≤ b) :
    intervalIntegral.integralSubtypeOn (divLogSq 1) a.val b.val ≤ divLogSq (b.val - a.val) a := by
  obtain ⟨F, hF, hc⟩ := exists_invLogSq_representative
  rw [integral_subtypeOn_Ioi_eq_integral _ F hF]
  calc
    _ ≤ ∫ t in a.val..b.val, divLogSq 1 a := by
      refine intervalIntegral.integral_mono_on hab
        ((hc.mono (uIcc_subset_one_lt a b)).intervalIntegrable) (by simp) fun t ht ↦ ?_
      have ht1 : 1 < t := a.property.trans_le ht.1
      rw [hF ⟨t, ht1⟩]
      have hlog := Real.log_le_log (zero_lt_one.trans a.property) ht.1
      have ha := log_pos a.property
      have hb := log_pos ht1
      change Checked.div 1 (log t ^ 2) (hb.ne'.isUnit.pow 2) ≤ divLogSq 1 a
      unfold divLogSq
      gcongr
    _ = _ := by rw [intervalIntegral.integral_const, smul_eq_mul, divLogSq, mul_one_div₀]

/-- Explicit integral bound, we expose a BigO version below since the constants and lower order term
aren't very convenient. -/
private theorem integral_one_div_log_sq_le_explicit {x : Set.Ioi (1 : ℝ)} (hx : 4 ≤ x.val) :
    intervalIntegral.integralSubtypeOn (divLogSq 1) 2 x.val ≤
      divLogSq (4 * x.val) x + divLogSq (√x.val) twoAboveOne := by
  let a := twoAboveOne
  have two_le_sqrt : 2 ≤ √x.val := le_sqrt_of_sq_le <| by norm_num [hx]
  have sqrt_le_x : √x.val ≤ x.val :=
    (sqrt_le_left (by linarith)).mpr (le_self_pow₀ (by linarith) (by decide))
  let s : Set.Ioi (1 : ℝ) := ⟨√x.val, Set.mem_Ioi.mpr (one_lt_two.trans_le two_le_sqrt)⟩
  obtain ⟨F, hF, hc⟩ := exists_invLogSq_representative
  have hi (a b : Set.Ioi (1 : ℝ)) := integral_subtypeOn_Ioi_eq_integral _ F hF a b
  have hint (a b : Set.Ioi (1 : ℝ)) : IntervalIntegrable F volume a.val b.val :=
    (hc.mono (uIcc_subset_one_lt a b)).intervalIntegrable
  have hsplit : intervalIntegral.integralSubtypeOn (divLogSq 1) a.val x.val =
      intervalIntegral.integralSubtypeOn (divLogSq 1) a.val s.val +
      intervalIntegral.integralSubtypeOn (divLogSq 1) s.val x.val := by
    rw [hi a x, hi a s, hi s x,
      intervalIntegral.integral_add_adjacent_intervals (hint a s) (hint s x)]
  have hden : divLogSq (x.val - s.val) s = divLogSq (4 * (x.val - s.val)) x := by
    apply div_eq_div_iff.mpr
    dsimp only [s]
    rw [log_sqrt (show 0 ≤ x.val from (zero_lt_one.trans x.property).le)]
    field_simp
    ring
  change intervalIntegral.integralSubtypeOn (divLogSq 1) a.val x.val ≤ _
  rw [hsplit]
  refine (_root_.add_le_add (integral_1_div_log_sq_le (a := a) (b := s) two_le_sqrt)
    (integral_1_div_log_sq_le (a := s) (b := x) sqrt_le_x)).trans ?_
  rw [hden, add_comm]
  unfold divLogSq
  gcongr <;> dsimp only [a, s] <;> linarith [sqrt_nonneg x.val]

private lemma tendsto_val_atTop : Tendsto (Subtype.val : Set.Ioi (1 : ℝ) → ℝ) atTop atTop := by
  refine tendsto_atTop.2 fun y ↦ ?_
  let z : Set.Ioi (1 : ℝ) := ⟨max 2 y,
    Set.mem_Ioi.mpr (one_lt_two.trans_le (le_max_left (2 : ℝ) y))⟩
  exact (eventually_ge_atTop z).mono fun _ hx ↦ (le_max_right (2 : ℝ) y).trans hx

/-- The square-root error is little-o of the main term on the logarithm quotient's domain. -/
private theorem sqrt_isLittleO :
    (fun x : Set.Ioi (1 : ℝ) ↦ √x.val) =o[atTop] (fun x ↦ divLogSq x.val x) := by
  have hlog : (fun x : Set.Ioi (1 : ℝ) ↦ log x.val ^ 2) =o[atTop] (fun x ↦ √x.val) := by
    simpa only [Function.comp_def, rpow_two, ← sqrt_eq_rpow] using
      (isLittleO_log_rpow_rpow_atTop 2 (s := 1 / 2) (by norm_num)).comp_tendsto tendsto_val_atTop
  have hmain : (fun x : Set.Ioi (1 : ℝ) ↦ log x.val ^ 2 * √x.val) =o[atTop] Subtype.val := by
    refine (hlog.mul_isBigO (isBigO_refl (fun x ↦ √x.val) atTop)).congr (fun _ ↦ rfl) fun x ↦ ?_
    exact Real.mul_self_sqrt (zero_lt_one.trans x.property).le
  refine IsLittleO.of_bound fun c hc ↦ ?_
  filter_upwards [hmain.bound hc] with x hx
  have hlog : 0 < log x.val ^ 2 := pow_pos (log_pos x.property) _
  have hx0 : 0 ≤ x.val := (zero_lt_one.trans x.property).le
  rw [norm_of_nonneg (mul_nonneg hlog.le (sqrt_nonneg _)), norm_of_nonneg hx0] at hx
  rw [norm_of_nonneg (sqrt_nonneg _), norm_of_nonneg (div_nonneg hx0 hlog.le),
    ← mul_div_assoc₀, le_div_iff₀ hlog, mul_comm (√x.val)]
  exact hx

theorem integral_one_div_log_sq_isBigO :
    (fun x : Set.Ioi (1 : ℝ) ↦ intervalIntegral.integralSubtypeOn (fun t : Set.Ioi (1 : ℝ) ↦
      Checked.div 1 (log t.val ^ 2) ((log_pos t.property).ne'.isUnit.pow 2)) 2 x.val)
      =O[atTop] (fun x ↦ Checked.div x.val (log x.val ^ 2)
        ((log_pos x.property).ne'.isUnit.pow 2)) := by
  change (fun x : Set.Ioi (1 : ℝ) ↦ intervalIntegral.integralSubtypeOn (divLogSq 1) 2 x.val)
    =O[atTop] (fun x ↦ divLogSq x.val x)
  let a := twoAboveOne
  trans (fun x : Set.Ioi (1 : ℝ) ↦ divLogSq (4 * x.val) x + divLogSq (√x.val) a)
  · apply IsBigO.of_bound'
    filter_upwards [eventually_ge_atTop (⟨4, by norm_num⟩ : Set.Ioi (1 : ℝ))] with x hx
    have hx4 : (4 : ℝ) ≤ x.val := hx
    obtain ⟨F, hF, _⟩ := exists_invLogSq_representative
    have hpos : 0 ≤ intervalIntegral.integralSubtypeOn (divLogSq 1) 2 x.val := by
      rw [integral_subtypeOn_Ioi_eq_integral _ F hF a x]
      refine intervalIntegral.integral_nonneg (by linarith) fun t ht ↦ ?_
      rw [hF ⟨t, one_lt_two.trans_le ht.1⟩]
      unfold divLogSq
      positivity
    exact (norm_of_nonneg hpos).le.trans
      ((integral_one_div_log_sq_le_explicit hx4).trans (le_norm_self _))
  refine IsBigO.add ?_ ?_
  · simpa only [divLogSq, mul_div_assoc₀] using
      (isBigO_const_mul_self (4 : ℝ) (fun x : Set.Ioi (1 : ℝ) ↦ divLogSq x.val x) atTop)
  · simpa only [divLogSq, mul_one_div₀, mul_comm] using
      (sqrt_isLittleO.isBigO.const_mul_left (divLogSq 1 a))

/-- Bound on the integral in `Chebyshev.primeCounting_eq_theta_div_log_add_integral`. -/
theorem integral_theta_div_log_sq_isBigO :
    (fun x : Set.Ioi (1 : ℝ) ↦ intervalIntegral.integralSubtypeOn (fun t : Set.Ioi (1 : ℝ) ↦
      Checked.div (θ t.val) (t.val * log t.val ^ 2)
        ((zero_lt_one.trans t.property).ne'.isUnit.mul ((log_pos t.property).ne'.isUnit.pow 2)))
      2 x.val) =O[atTop] (fun x ↦ Checked.div x.val (log x.val ^ 2)
        ((log_pos x.property).ne'.isUnit.pow 2)) := by
  change (fun x : Set.Ioi (1 : ℝ) ↦ intervalIntegral.integralSubtypeOn thetaDivIdMulLogSq 2 x.val)
    =O[atTop] (fun x ↦ divLogSq x.val x)
  refine (IsBigO.of_bound (log 4) ?_).trans integral_one_div_log_sq_isBigO
  let a := twoAboveOne
  filter_upwards [eventually_ge_atTop a] with x hx
  have hx2 : (2 : ℝ) ≤ x.val := hx
  obtain ⟨F, hF, hFc⟩ := exists_invLogSq_representative
  obtain ⟨L, _, hL, _⟩ := exists_invLog_representative
  let G : ℝ → ℝ := fun t ↦ θ t * -deriv L t
  have hG (t : Set.Ioi (1 : ℝ)) : G t.val = thetaDivIdMulLogSq t := by
    simp only [G, (hL t).deriv, neg_neg, thetaDivIdMulLogSq, div_eq_mul_inv₀]
  have hGint : IntervalIntegrable G volume 2 x.val := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx2, ← integrableOn_Icc_iff_integrableOn_Ioc]
    refine (integrableOn_iff_comap_subtypeVal measurableSet_Icc).mpr <|
      (integrableOn_theta_div_id_mul_log_sq x.val).congr (.of_forall fun t ↦ ?_)
    exact (hG ⟨t.val, one_lt_two.trans_le t.property.1⟩).symm
  rw [integral_subtypeOn_Ioi_eq_integral _ G hG a x,
    integral_subtypeOn_Ioi_eq_integral _ F hF a x]
  simp_rw [norm_eq_abs]
  have hFint : IntervalIntegrable F volume 2 x.val :=
    (hFc.mono (uIcc_subset_one_lt a x)).intervalIntegrable
  calc
    |∫ t in 2..x.val, G t| ≤ ∫ t in 2..x.val, |G t| :=
      intervalIntegral.abs_integral_le_integral_abs hx2
    _ ≤ ∫ t in 2..x.val, log 4 * F t := by
      refine intervalIntegral.integral_mono_on hx2 hGint.abs (hFint.const_mul _) fun t ht ↦ ?_
      let u : Set.Ioi (1 : ℝ) := ⟨t, one_lt_two.trans_le ht.1⟩
      rw [hF u, hG u]
      have ht0 : 0 < t := two_pos.trans_le ht.1
      have hl : 0 < log t ^ 2 := pow_pos (log_pos u.property) _
      unfold thetaDivIdMulLogSq divLogSq
      rw [abs_of_nonneg (div_nonneg (theta_nonneg _) (mul_nonneg ht0.le hl.le)),
        mul_one_div₀, div_le_div_iff₀ (mul_pos ht0 hl) hl]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (theta_le_log4_mul_x ht0.le) hl.le
    _ ≤ log 4 * |∫ t in 2..x.val, F t| := by
      rw [intervalIntegral.integral_const_mul]
      exact mul_le_mul_of_nonneg_left (le_abs_self _) (log_nonneg (by norm_num))

theorem integral_theta_div_log_sq_isLittleO :
    (fun x : Set.Ioi (1 : ℝ) ↦ intervalIntegral.integralSubtypeOn (fun t : Set.Ioi (1 : ℝ) ↦
      Checked.div (θ t.val) (t.val * log t.val ^ 2)
        ((zero_lt_one.trans t.property).ne'.isUnit.mul ((log_pos t.property).ne'.isUnit.pow 2)))
      2 x.val) =o[atTop]
        (fun x ↦ Checked.div x.val (log x.val) (log_pos x.property).ne'.isUnit) := by
  change (fun x : Set.Ioi (1 : ℝ) ↦ intervalIntegral.integralSubtypeOn thetaDivIdMulLogSq 2 x.val)
    =o[atTop] (fun x ↦ divLog x.val x)
  refine integral_theta_div_log_sq_isBigO.trans_isLittleO ?_
  have htend : Tendsto (fun x : Set.Ioi (1 : ℝ) ↦ Checked.inv (log x.val)
      (log_pos x.property).ne'.isUnit) atTop (𝓝 (0 : ℝ)) :=
    (tendsto_log_atTop.comp tendsto_val_atTop).fun_inv_tendsto_atTop
  refine IsLittleO.of_bound fun c hc ↦ ?_
  filter_upwards [htend.eventually (eventually_le_nhds hc)] with x hx
  have hx0 : 0 ≤ x.val := (zero_lt_one.trans x.property).le
  have hl := log_pos x.property
  have h1 : 0 ≤ divLog x.val x := div_nonneg hx0 hl.le
  have h2 : 0 ≤ divLogSq x.val x := div_nonneg hx0 (sq_nonneg _)
  rw [norm_of_nonneg h1, norm_of_nonneg h2]
  calc
    divLogSq x.val x = Checked.inv (log x.val) hl.ne'.isUnit * divLog x.val x := by
      unfold divLogSq divLog
      field_simp [hl.ne']
    _ ≤ c * divLog x.val x := mul_le_mul_of_nonneg_right hx h1

theorem primeCounting_sub_theta_div_log_isBigO :
    (fun x : Set.Ioi (1 : ℝ) ↦ (π ⌊x.val⌋₊ : ℝ) -
      Checked.div (θ x.val) (log x.val) (log_pos x.property).ne'.isUnit)
      =O[atTop] (fun x ↦ Checked.div x.val (log x.val ^ 2)
        ((log_pos x.property).ne'.isUnit.pow 2)) := by
  apply integral_theta_div_log_sq_isBigO.congr' _ (by rfl)
  let a := twoAboveOne
  filter_upwards [eventually_ge_atTop a] with x hx
  have hx2 : (2 : ℝ) ≤ x.val := hx
  have he := primeCounting_eq_theta_div_log_add_integral hx2
  change (π ⌊x.val⌋₊ : ℝ) = divLog (θ x.val) x +
    intervalIntegral.integralSubtypeOn thetaDivIdMulLogSq 2 x.val at he
  simp only [he, add_sub_cancel_left]

/-- Chebyshev's upper bound on the prime counting function -/
theorem eventually_primeCounting_le {ε : ℝ} (εpos : 0 < ε) :
    ∀ᶠ x : Set.Ioi (1 : ℝ) in atTop, π ⌊x.val⌋₊ ≤
      Checked.div ((log 4 + ε) * x.val) (log x.val) (log_pos x.property).ne'.isUnit := by
  let a := twoAboveOne
  filter_upwards [eventually_ge_atTop a,
    integral_theta_div_log_sq_isLittleO.bound εpos] with x hx hI
  have hx2 : (2 : ℝ) ≤ x.val := hx
  have hx0 : 0 ≤ x.val := (zero_lt_one.trans x.property).le
  have he := primeCounting_eq_theta_div_log_add_integral hx2
  change (π ⌊x.val⌋₊ : ℝ) = divLog (θ x.val) x +
    intervalIntegral.integralSubtypeOn thetaDivIdMulLogSq 2 x.val at he
  rw [he]
  rw [norm_of_nonneg (div_nonneg hx0 (log_pos x.property).le)] at hI
  have hθ : divLog (θ x.val) x ≤ divLog (log 4 * x.val) x := by
    exact div_le_div_of_nonneg_right (theta_le_log4_mul_x hx0) (log_pos x.property).le
  calc
    _ ≤ divLog (log 4 * x.val) x + ε * divLog x.val x :=
      add_le_add hθ ((le_norm_self _).trans hI)
    _ = _ := by simp only [divLog, add_mul, add_div, mul_div_assoc₀]

theorem pi_ge (n : ℕ) (hn : 1 < n) :
    Checked.div (n * log 2 - log (n + 1)) (log n)
      (log_pos (show (1 : ℝ) < n by exact_mod_cast hn)).ne'.isUnit ≤ π n := by
  grw [div_le_iff₀ (log_pos (show (1 : ℝ) < n by exact_mod_cast hn)),
    ← psi_le_primeCounting_mul_log, psi_ge]

theorem pi_ge' {x : ℝ} (hx : 1 < x) :
    Checked.div ((x - 1) * log 2 - log (x + 2)) (log x) (log_pos hx).ne'.isUnit ≤ π ⌊x⌋₊ := by
  grw [div_le_iff₀ (log_pos hx), ← psi_le_primeCounting_mul_log', psi_ge']
  positivity

theorem theta_le_pi_mul_log (n : ℕ) : θ n ≤ (π n) * log n :=
  (theta_le_psi n).trans (psi_le_primeCounting_mul_log n)

theorem theta_le_pi_mul_log' (x : ℝ) : θ x ≤ (π ⌊x⌋₊) * log x := by
  grw [← psi_le_primeCounting_mul_log', theta_le_psi]

private theorem pi_mul_log_sqrt_le {x : ℝ} (hx : 1 ≤ x) :
    (π ⌊x⌋₊) * log √x ≤ log 4 * x + √x * log √x := calc
  _ = ∑ p ∈ primesLE ⌊x⌋₊, log √x := by simp
  _ ≤ ∑ p ∈ primesLE ⌊x⌋₊, (log p + (if p ≤ √x then log √x else 0)) := by
    refine sum_le_sum fun p _ ↦ ?_
    split_ifs with h
    · simp [log_natCast_nonneg]
    have : log √x < log p := log_lt_log (by positivity) (not_le.mp h)
    grind
  _ ≤ _ := by
    grw [← theta_le_log4_mul_x (by positivity)]
    rw [sum_add_distrib, theta_eq_theta_coe_floor, theta_eq_sum_primesLE_log, ← sum_filter]
    simp only [sum_const, nsmul_eq_mul]
    gcongr
    · exact log_nonneg (one_le_sqrt.mpr hx)
    refine le_trans ?_ <| floor_le (sqrt_nonneg x)
    norm_cast
    rw [show ⌊√x⌋₊ = #(Icc 1 ⌊√x⌋₊) by simp]
    refine card_le_card fun p hp ↦ ?_
    simp only [mem_filter, mem_Icc, mem_primesLE] at hp ⊢
    exact ⟨hp.1.2.one_le, le_floor hp.2⟩

/-- A weak but completely explicit upper bound on $\pi(x)$. -/
theorem pi_le_log4_mul_div {x : ℝ} (hx : 1 < x) :
    π ⌊x⌋₊ ≤ Checked.div (log 4 * x) (log √x)
      (Real.log_pos (lt_sqrt_of_sq_lt (show (1 : ℝ) ^ 2 < x by simpa using hx))).ne'.isUnit +
      √x := by
  have h : 0 < log √x := Real.log_pos (lt_sqrt_of_sq_lt (show (1 : ℝ) ^ 2 < x by simpa using hx))
  rw [← sub_le_iff_le_add, le_div_iff₀ h, sub_mul]
  linarith [pi_mul_log_sqrt_le hx.le]

end PrimeCounting
end Chebyshev

namespace Mathlib.Meta.Positivity

open Lean Qq

/-- Extension for the `positivity` tactic: the first Chebyshev function is nonnegative. -/
@[positivity Chebyshev.theta _]
meta def evalTheta : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@Chebyshev.theta $a) =>
    assertInstancesCommute
    pure (.nonnegative q(Chebyshev.theta_nonneg $a))
  | _, _, _ => throwError "not theta"

/-- Extension for the `positivity` tactic: the second Chebyshev function is nonnegative. -/
@[positivity Chebyshev.psi _]
meta def evalPsi : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@Chebyshev.psi $a) =>
    assertInstancesCommute
    pure (.nonnegative q(Chebyshev.psi_nonneg $a))
  | _, _, _ => throwError "not psi"

end Mathlib.Meta.Positivity
