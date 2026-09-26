module

meta import Mathlib.Data.Nat.MaxPrimeFac

#guard Nat.maxPrimeFac 2 (by decide) = 2
#guard Nat.maxPrimeFac 12 (by decide) = 3
#guard Nat.maxPrimeFac 97 (by decide) = 97
#guard Nat.maxPrimeFac 125 (by decide) = 5
#guard Nat.maxPrimeFac 360 (by decide) = 5

-- Neither an omitted proof nor an invalid input can produce a natural number.
example : True := by
  fail_if_success
    let _ : ℕ := Nat.maxPrimeFac 12
  fail_if_success
    let _ : ℕ := Nat.maxPrimeFac 0 (by decide)
  fail_if_success
    let _ : ℕ := Nat.maxPrimeFac 1 (by decide)
  trivial

example : ¬ ∃ p, IsGreatest {p : ℕ | p.Prime ∧ p ∣ 0} p := by
  rw [Nat.exists_isGreatest_prime_dvd_iff]
  decide

example : ¬ ∃ p, IsGreatest {p : ℕ | p.Prime ∧ p ∣ 1} p := by
  rw [Nat.exists_isGreatest_prime_dvd_iff]
  decide

-- Rewriting works with independently supplied proofs of the result's domain.
example {m n : ℕ} (hm : 1 < m) (hn : 1 < n) (hmn : 1 < m * n) :
    Nat.maxPrimeFac (m * n) hmn = max (Nat.maxPrimeFac m hm) (Nat.maxPrimeFac n hn) := by
  rw [Nat.maxPrimeFac_mul hm hn]

example {n k : ℕ} (hn : 1 < n) (hk : k ≠ 0) (hnk : 1 < n ^ k) :
    Nat.maxPrimeFac (n ^ k) hnk = Nat.maxPrimeFac n hn := by
  simp [hn, hk]

example {p : ℕ} (hp : p.Prime) (hn : 1 < p) : Nat.maxPrimeFac p hn = p := by
  simp [hp]

example {n : ℕ} (hn : 1 < n) (hleft : 1 < 1 * n) (hright : 1 < n * 1) :
    Nat.maxPrimeFac (1 * n) hleft = Nat.maxPrimeFac n hn ∧
      Nat.maxPrimeFac (n * 1) hright = Nat.maxPrimeFac n hn := by
  simp

-- The fixed-point description has no exceptional nonprime cases.
example {n : ℕ} (hn : 1 < n) (h : ¬ n.Prime) : Nat.maxPrimeFac n hn < n := by
  exact lt_of_le_of_ne (Nat.maxPrimeFac_le hn) (by simpa using h)
