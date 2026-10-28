/-
Copyright (c) 2025 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
module

public import Mathlib.Data.Nat.Factorial.NatCast
public import Mathlib.RingTheory.DividedPowers.Basic

/-! # Examples of divided power structures

In this file we show that, for certain choices of a commutative (semi)ring `A` and an ideal `I` of
`A`, the family of maps `ℕ → A → A` given by `fun n x ↦ x^n/n!` (where `n!` is invertible, and
by `0` in the degrees where `x^n = 0` for all `x ∈ I`) is a divided power structure on `I`.

## Main Definitions

* `DividedPowers.OfInvertibleFactorial.dpow` : given a natural number `n` such that `(n-1)!` is
  invertible in `A`, the family of functions `ℕ → A → A` given by `x^m/m!` for `m < n` and by
  `0` for `n ≤ m`.
* `DividedPowers.OfInvertibleFactorial.dividedPowers` : the divided power structure on `I` given by
  this family, assuming that there exists a natural number `n` such that `(n-1)!` is
  invertible in `A` and `I^n = 0`.
* `DividedPowers.OfSquareZero.dividedPowers` : given an ideal `I` such that `I^2 =0`, this is
  the divided power structure on `I` given by `fun x n ↦ x^n/n!` for `n < 2` and by `0` for
  `2 ≤ n`.
* `DividedPowers.CharP.dividedPowers` : if `A` is a commutative ring of prime characteristic `p`
  and `I` is an ideal such that `I^p = 0`, , this is the divided power structure on `I` given by
  `fun x n ↦ x^n/n!` for `n < p` and by `0` for `p ≤ n`.
* `DividedPowers.RatAlgebra.dividedPowers` : if `I` is any ideal in a `ℚ`-algebra, this is the
  divided power structure on `I` given by `fun x n ↦ x^n/n!`.

## Main Results

* `DividedPowers.RatAlgebra.dividedPowers_unique`: there are no other divided power structures on an
  ideal of a `ℚ`-algebra.

## References

* [P. Berthelot (1974), *Cohomologie cristalline des schémas de
  caractéristique $p$ > 0*][Berthelot-1974]

* [P. Berthelot and A. Ogus (1978), *Notes on crystalline
  cohomology*][BerthelotOgus-1978]

* [N. Roby (1963), *Lois polynomes et lois formelles en théorie des
  modules*][Roby-1963]

* [N. Roby (1965), *Les algèbres à puissances dividées*][Roby-1965]

-/

@[expose] public section

open Nat

namespace DividedPowers

namespace OfInvertibleFactorial

variable {A : Type*} [CommSemiring A] (I : Ideal A) [DecidablePred (fun x ↦ x ∈ I)]

/-- Given a natural number `n` such that `(n-1)!` is invertible in `A`, the family of functions
`ℕ → A → A` given by `x^m/m!` for `x ∈ I` and `m < n` (so that `m!` is invertible), and by `0`
otherwise. When `I^n = 0`, it is the divided power structure of Proposition 1.2.7 of [B74],
part (ii). -/
noncomputable def dpow {n : ℕ} (hn_fac : IsUnit ((n - 1)! : A)) : ℕ → A → A := fun m x =>
  if h : x ∈ I ∧ m < n then Checked.inv (m ! : A) (hn_fac.natCast_factorial_of_lt h.2) * x ^ m
  else 0

variable {I}

theorem dpow_eq_of_mem {n : ℕ} (hn_fac : IsUnit ((n - 1)! : A)) {m : ℕ} (hmn : m < n) {x : A}
    (hx : x ∈ I) :
    dpow I hn_fac m x = Checked.inv (m ! : A) (hn_fac.natCast_factorial_of_lt hmn) * x ^ m :=
  dite_eq_left ⟨hx, hmn⟩

theorem dpow_eq_zero_of_le {n : ℕ} (hn_fac : IsUnit ((n - 1)! : A)) {m : ℕ} (hnm : n ≤ m)
    (x : A) : dpow I hn_fac m x = 0 :=
  dite_eq_right fun h ↦ (h.2.trans_le hnm).false

theorem dpow_eq_of_not_mem {n : ℕ} (hn_fac : IsUnit ((n - 1)! : A)) {m : ℕ} {x : A}
    (hx : x ∉ I) : dpow I hn_fac m x = 0 :=
  dite_eq_right fun h ↦ hx h.1

theorem dpow_null {n : ℕ} (hn_fac : IsUnit ((n - 1)! : A)) {m : ℕ} {x : A} (hx : x ∉ I) :
    dpow I hn_fac m x = 0 :=
  dpow_eq_of_not_mem hn_fac hx

theorem dpow_zero {n : ℕ} (hn_fac : IsUnit ((n - 1)! : A)) (hn : 0 < n) {x : A} (hx : x ∈ I) :
    dpow I hn_fac 0 x = 1 := by
  simp [dpow_eq_of_mem hn_fac hn hx]

theorem dpow_one {n : ℕ} (hn_fac : IsUnit ((n - 1)! : A)) (hn : 1 < n) {x : A} (hx : x ∈ I) :
    dpow I hn_fac 1 x = x := by
  simp [dpow_eq_of_mem hn_fac hn hx]

theorem dpow_mem {n : ℕ} (hn_fac : IsUnit ((n - 1)! : A)) {m : ℕ} (hm : m ≠ 0) {x : A}
    (hx : x ∈ I) : dpow I hn_fac m x ∈ I := by
  by_cases! hmn : m < n
  · rw [dpow_eq_of_mem hn_fac hmn hx]
    exact Ideal.mul_mem_left I _ (Ideal.pow_mem_of_mem I hx _ (Nat.pos_of_ne_zero hm))
  · rw [dpow_eq_zero_of_le hn_fac hmn]
    exact I.zero_mem

theorem dpow_add_of_lt {n : ℕ} (hn_fac : IsUnit ((n - 1)! : A)) {m : ℕ} (hmn : m < n)
    {x y : A} (hx : x ∈ I) (hy : y ∈ I) :
    dpow I hn_fac m (x + y) =
      (Finset.antidiagonal m).sum (fun k ↦ dpow I hn_fac k.1 x * dpow I hn_fac k.2 y) := by
  rw [dpow_eq_of_mem hn_fac hmn (Ideal.add_mem I hx hy), inv_mul_eq_iff_eq_mul₀,
    Finset.mul_sum, Commute.add_pow' (Commute.all _ _)]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [dpow_eq_of_mem hn_fac
      ((Nat.le_of_lt_succ (Finset.Nat.antidiagonal.fst_lt hk)).trans_lt hmn) hx,
    dpow_eq_of_mem hn_fac
      ((Nat.le_of_lt_succ (Finset.Nat.antidiagonal.snd_lt hk)).trans_lt hmn) hy, nsmul_eq_mul,
    castChoose_eq (hn_fac.natCast_factorial_of_lt hmn) hk]
  ring

theorem dpow_add {n : ℕ} (hn_fac : IsUnit ((n - 1)! : A)) (hnI : I ^ n = 0) {m : ℕ} {x : A}
    (hx : x ∈ I) {y : A} (hy : y ∈ I) :
    dpow I hn_fac m (x + y) =
      (Finset.antidiagonal m).sum fun k ↦ dpow I hn_fac k.1 x * dpow I hn_fac k.2 y := by
  by_cases! hmn : m < n
  · exact dpow_add_of_lt hn_fac hmn hx hy
  · rw [dpow_eq_zero_of_le hn_fac hmn, eq_comm]
    refine Finset.sum_eq_zero fun k hk ↦ ?_
    by_cases! hk₁ : n ≤ k.1
    · rw [dpow_eq_zero_of_le hn_fac hk₁, zero_mul]
    by_cases! hk₂ : n ≤ k.2
    · rw [dpow_eq_zero_of_le hn_fac hk₂, mul_zero]
    rw [dpow_eq_of_mem hn_fac hk₁ hx, dpow_eq_of_mem hn_fac hk₂ hy, mul_mul_mul_comm]
    apply mul_eq_zero_of_right
    rw [← Ideal.mem_bot, ← Ideal.zero_eq_bot, ← hnI]
    apply Ideal.pow_le_pow_right hmn
    rw [← Finset.mem_antidiagonal.mp hk, pow_add]
    exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hx _) (Ideal.pow_mem_pow hy _)

theorem dpow_mul {n : ℕ} (hn_fac : IsUnit ((n - 1)! : A)) {m : ℕ} {a x : A} (hx : x ∈ I) :
    dpow I hn_fac m (a * x) = a ^ m * dpow I hn_fac m x := by
  by_cases! hmn : m < n
  · rw [dpow_eq_of_mem hn_fac hmn (Ideal.mul_mem_left I _ hx), dpow_eq_of_mem hn_fac hmn hx,
      mul_pow, ← mul_assoc, mul_comm _ (a ^ m), mul_assoc]
  · rw [dpow_eq_zero_of_le hn_fac hmn, dpow_eq_zero_of_le hn_fac hmn, mul_zero]

theorem dpow_mul_of_add_lt {n : ℕ} (hn_fac : IsUnit ((n - 1)! : A)) {m k : ℕ}
    (hkm : m + k < n) {x : A} (hx : x ∈ I) :
    dpow I hn_fac m x * dpow I hn_fac k x = ↑((m + k).choose m) * dpow I hn_fac (m + k) x := by
  have hm : m < n := lt_of_le_of_lt le_self_add hkm
  have hk : k < n := lt_of_le_of_lt le_add_self hkm
  rw [dpow_eq_of_mem hn_fac hm hx, dpow_eq_of_mem hn_fac hk hx, dpow_eq_of_mem hn_fac hkm hx,
    mul_assoc, ← mul_assoc (x ^ m), mul_comm (x ^ m), mul_assoc _ (x ^ m),
    ← pow_add, ← mul_assoc, ← mul_assoc]
  apply congr_arg₂ _ _ rfl
  rw [eq_mul_inv_iff_mul_eq₀, mul_assoc, inv_mul_eq_iff_eq_mul₀, inv_mul_eq_iff_eq_mul₀]
  norm_cast; apply congr_arg
  rw [← Nat.add_choose_mul_factorial_mul_factorial, mul_comm, mul_comm _ (m !), Nat.choose_symm_add]

theorem mul_dpow {n : ℕ} (hn_fac : IsUnit ((n - 1).factorial : A)) (hnI : I ^ n = 0)
    {m k : ℕ} {x : A} (hx : x ∈ I) :
    dpow I hn_fac m x * dpow I hn_fac k x = ↑((m + k).choose m) * dpow I hn_fac (m + k) x := by
  by_cases! hkm : m + k < n
  · exact dpow_mul_of_add_lt hn_fac hkm hx
  · rw [dpow_eq_zero_of_le hn_fac hkm, mul_zero]
    by_cases! hm : n ≤ m
    · rw [dpow_eq_zero_of_le hn_fac hm, zero_mul]
    by_cases! hk : n ≤ k
    · rw [dpow_eq_zero_of_le hn_fac hk, mul_zero]
    rw [dpow_eq_of_mem hn_fac hm hx, dpow_eq_of_mem hn_fac hk hx, mul_mul_mul_comm, ← pow_add,
      Ideal.pow_eq_zero_of_mem hnI hkm hx, mul_zero]

theorem dpow_comp_of_mul_lt {n : ℕ} (hn_fac : IsUnit ((n - 1)! : A)) {m k : ℕ} (hk : k ≠ 0)
    (hkm : m * k < n) {x : A} (hx : x ∈ I) :
    dpow I hn_fac m (dpow I hn_fac k x) = ↑(uniformBell m k) * dpow I hn_fac (m * k) x := by
  have hmn : m < n := lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hk)) hkm
  rw [dpow_eq_of_mem hn_fac hkm hx, dpow_eq_of_mem hn_fac hmn (dpow_mem hn_fac hk hx)]
  by_cases hm0 : m = 0
  · simp only [hm0, zero_mul, _root_.pow_zero, mul_one, uniformBell_zero_left, cast_one, one_mul]
  · have hkn : k < n := lt_of_le_of_lt (Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hm0)) hkm
    rw [dpow_eq_of_mem hn_fac hkn hx, mul_pow, ← pow_mul, mul_comm k, ← mul_assoc, ← mul_assoc]
    apply congr_arg₂ _ _ rfl
    rw [eq_mul_inv_iff_mul_eq₀, mul_assoc, inv_mul_eq_iff_eq_mul₀, inv_pow₀,
      inv_mul_eq_iff_eq_mul₀, ← uniformBell_mul_eq _ hk]
    push_cast
    ring_nf

theorem dpow_comp {n : ℕ} (hn_fac : IsUnit ((n - 1).factorial : A)) (hnI : I ^ n = 0)
    {m k : ℕ} (hk : k ≠ 0) {x : A} (hx : x ∈ I) :
    dpow I hn_fac m (dpow I hn_fac k x) = ↑(uniformBell m k) * dpow I hn_fac (m * k) x := by
  by_cases! hmk : m * k < n
  · exact dpow_comp_of_mul_lt hn_fac hk hmk hx
  · rw [dpow_eq_zero_of_le hn_fac hmk, mul_zero]
    by_cases! hm : n ≤ m
    · exact dpow_eq_zero_of_le hn_fac hm _
    have hm0 : m ≠ 0 := by
      rintro rfl
      omega
    by_cases! hkn : n ≤ k
    · rw [dpow_eq_zero_of_le hn_fac hkn, dpow_eq_of_mem hn_fac hm I.zero_mem, zero_pow hm0,
        mul_zero]
    rw [dpow_eq_of_mem hn_fac hm (dpow_mem hn_fac hk hx), dpow_eq_of_mem hn_fac hkn hx, mul_pow,
      ← pow_mul, mul_comm k, Ideal.pow_eq_zero_of_mem hnI hmk hx, mul_zero, mul_zero]

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- If `(n-1)!` is invertible in `A` and `I^n = 0`, then `I` admits a divided power structure.
  Proposition 1.2.7 of [B74], part (ii). -/
noncomputable def dividedPowers {n : ℕ} (hn_fac : IsUnit ((n - 1).factorial : A))
    (hnI : I ^ n = 0) : DividedPowers I where
  dpow            := dpow I hn_fac
  dpow_null hx    := dpow_null hn_fac hx
  dpow_zero {x} hx := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact eq_of_zero_eq_one (by simpa using (Ideal.pow_eq_zero_of_mem hnI le_rfl hx).symm) _ _
    · exact dpow_zero hn_fac hn hx
  dpow_one {x} hx := by
    by_cases! hn : n ≤ 1
    · rw [dpow_eq_zero_of_le hn_fac hn, eq_comm, ← pow_one x]
      exact Ideal.pow_eq_zero_of_mem hnI hn hx
    · exact dpow_one hn_fac hn hx
  dpow_mem hn hx  := dpow_mem hn_fac hn hx
  dpow_add hx hy  := dpow_add hn_fac hnI hx hy
  dpow_mul        := dpow_mul hn_fac
  mul_dpow hx     := mul_dpow hn_fac hnI hx
  dpow_comp hk hx := dpow_comp hn_fac hnI hk hx

lemma dpow_apply {n : ℕ} (hn_fac : IsUnit ((n - 1).factorial : A)) (hnI : I ^ n = 0)
    {m : ℕ} {x : A} :
  (dividedPowers hn_fac hnI).dpow m x =
    if h : x ∈ I ∧ m < n then
      Checked.inv (m ! : A) (hn_fac.natCast_factorial_of_lt h.2) * x ^ m
    else 0 := rfl

end OfInvertibleFactorial

namespace OfSquareZero

variable {A : Type*} [CommSemiring A] {I : Ideal A} [DecidablePred (fun x ↦ x ∈ I)]
  (hI2 : I ^ 2 = 0)

/-- If `I^2 = 0`, then `I` admits a divided power structure. -/
noncomputable def dividedPowers : DividedPowers I :=
  OfInvertibleFactorial.dividedPowers (by norm_num) hI2

theorem dpow_of_two_le {n : ℕ} (hn : 2 ≤ n) (a : A) :
    (dividedPowers hI2) n a = 0 :=
  OfInvertibleFactorial.dpow_eq_zero_of_le (by norm_num) hn a

end OfSquareZero

namespace IsNilpotent

variable {A : Type*} [CommRing A] {p : ℕ} [Fact (Nat.Prime p)] (hp : IsNilpotent (p : A))
  {I : Ideal A} [DecidablePred (fun x ↦ x ∈ I)] (hIp : I ^ p = 0)

/-- If `A` is a commutative ring of prime characteristic `p` and `I` is an ideal such that
  `I^p = 0`, then `I` admits a divided power structure. -/
noncomputable def dividedPowers : DividedPowers I :=
  OfInvertibleFactorial.dividedPowers (n := p)
    (IsUnit.natCast_factorial_of_isNilpotent hp (Nat.sub_one_lt (NeZero.ne' p).symm)) hIp

theorem dpow_of_prime_le {n : ℕ} (hn : p ≤ n) (a : A) : (dividedPowers hp hIp) n a = 0 :=
  OfInvertibleFactorial.dpow_eq_zero_of_le
    (IsUnit.natCast_factorial_of_isNilpotent hp (Nat.sub_one_lt (NeZero.ne' p).symm)) hn a

end IsNilpotent

namespace CharP

variable (A : Type*) [CommRing A] (p : ℕ) [CharP A p] [Fact (Nat.Prime p)]
  {I : Ideal A} [DecidablePred (fun x ↦ x ∈ I)] (hIp : I ^ p = 0)

/-- If `A` is a commutative ring of prime characteristic `p` and `I` is an ideal such that
  `I^p = 0`, then `I` admits a divided power structure. -/
noncomputable def dividedPowers : DividedPowers I :=
  IsNilpotent.dividedPowers ((CharP.cast_eq_zero A p) ▸ IsNilpotent.zero) hIp

theorem dpow_of_prime_le {n : ℕ} (hn : p ≤ n) (a : A) : (dividedPowers A p hIp) n a = 0 :=
  IsNilpotent.dpow_of_prime_le ((CharP.cast_eq_zero A p) ▸ IsNilpotent.zero) hIp hn a

end CharP

-- We formalize example 2 from [BO], Section 3.
namespace RatAlgebra

variable {R : Type*} [CommSemiring R] (I : Ideal R) [DecidablePred (fun x ↦ x ∈ I)]
  [Algebra ℚ R]

/-- The family `ℕ → R → R` given by `dpow n x = x ^ n / n!`, where `n!` is invertible since `R` is
a `ℚ`-algebra. -/
noncomputable def dpow : ℕ → R → R := fun n x =>
  if x ∈ I then Checked.inv (n ! : R) (IsUnit.natCast_factorial_of_algebra ℚ n) * x ^ n else 0

variable {I}

theorem dpow_eq_of_mem (n : ℕ) {x : R} (hx : x ∈ I) :
    dpow I n x = Checked.inv (n ! : R) (IsUnit.natCast_factorial_of_algebra ℚ n) * x ^ n :=
  ite_eq_left hx

/-- Below `n`, the divided powers on a `ℚ`-algebra are those of
`OfInvertibleFactorial.dpow`. -/
private theorem dpow_eq_ofInvertibleFactorial_dpow {n m : ℕ} (hmn : m < n) (x : R) :
    dpow I m x =
      OfInvertibleFactorial.dpow I (IsUnit.natCast_factorial_of_algebra ℚ (n - 1)) m x := by
  by_cases hx : x ∈ I
  · rw [dpow_eq_of_mem m hx, OfInvertibleFactorial.dpow_eq_of_mem _ hmn hx]
  · rw [dpow, ite_eq_right hx, OfInvertibleFactorial.dpow_null _ hx]

variable (I)

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- If `I` is an ideal in a `ℚ`-algebra `A`, then `I` admits a unique divided power structure,
  given by `dpow n x = x ^ n / n!`. -/
noncomputable def dividedPowers : DividedPowers I where
  dpow           := dpow I
  dpow_null hx   := ite_eq_right hx
  dpow_zero hx   := by simp [dpow_eq_of_mem 0 hx]
  dpow_one hx    := by simp [dpow_eq_of_mem 1 hx]
  dpow_mem hn hx := by
    rw [dpow_eq_of_mem _ hx]
    exact Ideal.mul_mem_left I _ (Ideal.pow_mem_of_mem I hx _ (Nat.pos_of_ne_zero hn))
  dpow_add {n} x y hx hy := by
    rw [dpow_eq_ofInvertibleFactorial_dpow (n := n + 1) (Nat.lt_add_one n),
      OfInvertibleFactorial.dpow_add_of_lt _ (Nat.lt_add_one n) hx hy]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [dpow_eq_ofInvertibleFactorial_dpow (Finset.Nat.antidiagonal.fst_lt hk),
      dpow_eq_ofInvertibleFactorial_dpow (Finset.Nat.antidiagonal.snd_lt hk)]
  dpow_mul {n a x} hx := by
    rw [dpow_eq_of_mem n (Ideal.mul_mem_left I _ hx), dpow_eq_of_mem n hx, mul_pow, ← mul_assoc,
      mul_comm _ (a ^ n), mul_assoc]
  mul_dpow {m k x} hx := by
    rw [dpow_eq_ofInvertibleFactorial_dpow (n := m + k + 1) (m := m) (by omega),
      dpow_eq_ofInvertibleFactorial_dpow (n := m + k + 1) (m := k) (by omega),
      dpow_eq_ofInvertibleFactorial_dpow (n := m + k + 1) (m := m + k) (by omega),
      OfInvertibleFactorial.dpow_mul_of_add_lt _ (Nat.lt_add_one _) hx]
  dpow_comp {m k x} hk hx := by
    rw [dpow_eq_ofInvertibleFactorial_dpow (n := m * k + m + k + 1) (m := k) (by omega),
      dpow_eq_ofInvertibleFactorial_dpow (n := m * k + m + k + 1) (m := m) (by omega),
      dpow_eq_ofInvertibleFactorial_dpow (n := m * k + m + k + 1) (m := m * k) (by omega),
      OfInvertibleFactorial.dpow_comp_of_mul_lt _ hk (by omega) hx]

@[simp]
lemma dpow_apply {n : ℕ} {x : R} :
    (dividedPowers I).dpow n x =
      if x ∈ I then
        Checked.inv (n.factorial : R) (IsUnit.natCast_factorial_of_algebra ℚ n) * x ^ n
      else 0 := rfl

omit [DecidablePred fun x ↦ x ∈ I] in
/-- If `I` is an ideal in a `ℚ`-algebra `A`, then the divided power structure on `I` given by
  `dpow n x = x ^ n / n!` is the only possible one. -/
theorem dpow_eq_inv_fact_smul (hI : DividedPowers I) {n : ℕ} {x : R} (hx : x ∈ I) :
    hI.dpow n x = (n.factorial : ℚ)⁻¹ • x ^ n := by
  rw [← factorial_mul_dpow_eq_pow hI hx, ← smul_eq_mul, ← smul_assoc]
  nth_rewrite 1 [← one_smul R (hI.dpow n x)]
  congr
  have aux : ((n !) : R) = (n ! : ℚ) • (1 : R) := by
    rw [cast_smul_eq_nsmul, nsmul_eq_mul, mul_one]
  rw [aux, ← mul_smul]
  suffices (n ! : ℚ)⁻¹ * (n !) = 1 by
    rw [this, one_smul]
  exact inv_mul_cancel₀

variable {I}

/-- There are no other divided power structures on an ideal of a  `ℚ`-algebra. -/
theorem dividedPowers_unique (hI : DividedPowers I) : hI = dividedPowers I :=
  hI.ext _ (fun n x hx ↦ by
    rw [dpow_apply, ite_eq_left hx, eq_comm, inv_mul_eq_iff_eq_mul₀,
      factorial_mul_dpow_eq_pow _ hx])

end RatAlgebra

end DividedPowers
