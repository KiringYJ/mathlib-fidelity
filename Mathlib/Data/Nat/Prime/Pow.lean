/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
module

public import Mathlib.Data.Nat.Prime.Basic

/-!
# Prime numbers

This file develops the theory of prime numbers: natural numbers `p ≥ 2` whose only divisors are
`p` and `1`.

-/

public section

namespace Nat

theorem pow_minFac {n k : ℕ} {hnk : n ^ k ≠ 1} (hk : k ≠ 0) :
    (n ^ k).minFac hnk = n.minFac (fun hn => hnk (by rw [hn, one_pow])) := by
  have hn : n ≠ 1 := fun hn => hnk (by rw [hn, one_pow])
  apply (minFac_le_of_dvd (minFac_prime hn).two_le ((minFac_dvd n hn).pow hk)).antisymm
  apply
    minFac_le_of_dvd (minFac_prime hnk).two_le
      ((minFac_prime hnk).dvd_of_dvd_pow (minFac_dvd _ hnk))

theorem Prime.pow_minFac {p k : ℕ} {hpk : p ^ k ≠ 1} (hp : p.Prime) (hk : k ≠ 0) :
    (p ^ k).minFac hpk = p := by
  rw [Nat.pow_minFac hk, hp.minFac_eq]

end Nat
