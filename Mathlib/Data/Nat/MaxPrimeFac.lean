/-
Copyright (c) 2026 Bo Cowgill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bo Cowgill
-/
module

public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Order.Lattice.Nat

/-!
# Greatest prime factor of a natural number

This file defines `Nat.maxPrimeFac n hn`, the greatest prime factor of a natural number `n`,
with an explicit proof `hn : 1 < n`.

## Implementation notes

The prime-divisor set has a greatest element exactly when `1 < n`, as expressed by
`Nat.exists_isGreatest_prime_dvd_iff`. At zero it contains every prime and is unbounded;
at one it is empty. On the valid domain, the sorted list `n.primeFactorsList` is nonempty,
so its last element computes the greatest prime factor without a default value.
-/

@[expose] public section

namespace Nat

variable {m n p : ℕ}

/-- The greatest prime divisor of a natural number `n > 1`. -/
def maxPrimeFac (n : ℕ) (hn : 1 < n) : ℕ :=
  n.primeFactorsList.getLast ((primeFactorsList_ne_nil n).2 hn)

lemma prime_maxPrimeFac (hn : 1 < n) : (n.maxPrimeFac hn).Prime :=
  prime_of_mem_primeFactorsList <| List.getLast_mem _

/-- The greatest prime factor of a natural number divides it. -/
lemma maxPrimeFac_dvd (hn : 1 < n) : maxPrimeFac n hn ∣ n :=
  dvd_of_mem_primeFactorsList <| List.getLast_mem _

/-- Every prime factor of a natural number greater than one is at most its greatest prime factor. -/
lemma le_maxPrimeFac (hn : 1 < n) (hp : p.Prime) (h_dvd : p ∣ n) :
    p ≤ maxPrimeFac n hn := by
  have := (mem_primeFactorsList (Nat.ne_zero_of_lt hn)).2 ⟨hp, h_dvd⟩
  simpa only [maxPrimeFac]
    using (primeFactorsList_sorted n).pairwise.rel_getLast this

/-- The greatest prime factor of a natural number greater than one is the greatest of its prime
factors. -/
lemma isGreatest_maxPrimeFac (hn : 1 < n) :
    IsGreatest {p : ℕ | p.Prime ∧ p ∣ n} (maxPrimeFac n hn) :=
  ⟨⟨prime_maxPrimeFac hn, maxPrimeFac_dvd hn⟩, fun _ hp => le_maxPrimeFac hn hp.1 hp.2⟩

/-- A natural number has a greatest prime divisor exactly when it is greater than one. -/
lemma exists_isGreatest_prime_dvd_iff :
    (∃ p, IsGreatest {p : ℕ | p.Prime ∧ p ∣ n} p) ↔ 1 < n := by
  constructor
  · rintro ⟨p, hp⟩
    have hn : n ≠ 0 := by
      rintro rfl
      exact not_bddAbove_setOfPred_prime ⟨p, fun q hq => hp.2 ⟨hq, dvd_zero q⟩⟩
    exact hp.1.1.one_lt.trans_le (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hp.1.2)
  · intro hn
    exact ⟨maxPrimeFac n hn, isGreatest_maxPrimeFac hn⟩

/-- The greatest prime factor of a natural number greater than one is the least upper bound of
its prime factors. -/
lemma isLUB_maxPrimeFac (hn : 1 < n) :
    IsLUB {p : ℕ | p.Prime ∧ p ∣ n} (maxPrimeFac n hn) :=
  (isGreatest_maxPrimeFac hn).isLUB

lemma maxPrimeFac_le_iff (hn : 1 < n) :
    n.maxPrimeFac hn ≤ m ↔ ∀ p, p.Prime → p ∣ n → p ≤ m := by
  simp [isLUB_le_iff <| isLUB_maxPrimeFac hn, upperBounds]

@[simp]
lemma one_le_maxPrimeFac (hn : 1 < n) : 1 ≤ maxPrimeFac n hn :=
  (prime_maxPrimeFac hn).one_lt.le

@[simp]
lemma one_lt_maxPrimeFac (hn : 1 < n) : 1 < maxPrimeFac n hn :=
  (prime_maxPrimeFac hn).one_lt

/-- The greatest prime factor of a product of natural numbers greater than one is the maximum
of their greatest prime factors. -/
lemma maxPrimeFac_mul (hm : 1 < m) (hn : 1 < n) :
    maxPrimeFac (m * n) (one_lt_mul'' hm hn) = max (maxPrimeFac m hm) (maxPrimeFac n hn) := by
  refine eq_of_forall_ge_iff fun c ↦ ?_
  simp +contextual [maxPrimeFac_le_iff, Nat.Prime.dvd_mul, or_imp, forall_and]

/-- The greatest prime factor of a power with nonzero exponent is the greatest prime factor of
its base. -/
@[simp]
lemma maxPrimeFac_pow (hn : 1 < n) {k : ℕ} (hk : k ≠ 0) :
    maxPrimeFac (n ^ k) (one_lt_pow hk hn) = maxPrimeFac n hn := by
  apply le_antisymm
  · exact le_maxPrimeFac hn (prime_maxPrimeFac _)
      ((prime_maxPrimeFac _).dvd_of_dvd_pow (maxPrimeFac_dvd _))
  · exact le_maxPrimeFac _ (prime_maxPrimeFac hn) (dvd_pow (maxPrimeFac_dvd hn) hk)

/-- The greatest prime factor of a prime is the prime itself. -/
@[simp]
lemma Prime.maxPrimeFac_eq_self (hp : p.Prime) : maxPrimeFac p hp.one_lt = p := by
  apply le_antisymm
  · exact Nat.le_of_dvd hp.pos (maxPrimeFac_dvd hp.one_lt)
  · exact le_maxPrimeFac hp.one_lt hp (dvd_refl p)

/-- The fixed points of `maxPrimeFac` are the primes. -/
@[simp]
lemma maxPrimeFac_eq_self_iff (hn : 1 < n) : maxPrimeFac n hn = n ↔ n.Prime where
  mp h := h ▸ prime_maxPrimeFac hn
  mpr hp := hp.maxPrimeFac_eq_self

/-- The greatest prime factor of a natural number is at most that number. -/
lemma maxPrimeFac_le (hn : 1 < n) : maxPrimeFac n hn ≤ n :=
  Nat.le_of_dvd (Nat.zero_lt_of_lt hn) (maxPrimeFac_dvd hn)

/-- The computable greatest prime factor agrees with its supremum characterization. -/
lemma maxPrimeFac_eq_sSup (hn : 1 < n) :
    maxPrimeFac n hn = sSup {p : ℕ | p.Prime ∧ p ∣ n} :=
  ((isLUB_maxPrimeFac hn).csSup_eq ⟨_, (isGreatest_maxPrimeFac hn).1⟩).symm

end Nat
