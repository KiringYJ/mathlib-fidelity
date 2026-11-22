/-
Copyright (c) 2024 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.Tactic.FieldSimp

/-!
# The Selberg Sieve

We set up the working assumptions of the Selberg sieve, define the notion of an upper bound sieve
and show that every upper bound sieve yields an upper bound on the size of the sifted set. We also
define the Λ² sieve and prove that Λ² sieves are upper bound sieves. We then diagonalise the main
term of the Λ² sieve.

We mostly follow the treatment outlined by Heath-Brown in the notes to an old graduate course. One
minor notational difference is that we write $\nu(n)$ in place of $\frac{\omega(n)}{n}$.

## Results
* `siftedSum_le_mainSum_errSum_of_UpperBoundSieve` - Every upper bound sieve gives an upper bound
  on the size of the sifted set in terms of `mainSum` and `errSum`
* `upperMoebius_of_lambda_sq` - Lambda squared weights produce upper bound sieves
* `lambdaSquared_mainSum_eq_diag_quad_form` - The main sum of a Λ² sieve has a nice diagonalisation

## References

* [Heath-Brown, *Lectures on sieves*][heathbrown2002lecturessieves]
* [Koukoulopoulos, *The Distribution of Prime Numbers*][MR3971232]

-/

@[expose] public section

noncomputable section

open scoped ArithmeticFunction.Moebius

open Finset Real Nat ArithmeticFunction

/-- We set up a sieve problem as follows. Take a finite set of natural numbers `A`, whose elements
are weighted by a sequence `a n`. Also take a finite set of primes `P`, represented by a squarefree
natural number. These are the primes that we will sift from our set `A`. Suppose we can approximate
`∑ n ∈ A with d ∣ n, a n = ν d * X + R d`, where `X` is an approximation to the total size of `A`
and `ν` is a multiplicative arithmetic function such that `0 < ν p < 1` for all primes `p ∣ P`.

Then a sieve-type theorem will give us an upper (or lower) bound on the size of the sifted sum
`∑ n ∈ support with n.Coprime P, a n`, obtained by removing any elements of `A` that are a
multiple of a prime in `P`. -/
structure BoundingSieve where
  /-- The set of natural numbers that is to be sifted. The fundamental lemma yields an upper bound
  on the size of this set after the multiples of small primes have been removed. -/
  support : Finset ℕ
  /-- The finite set of prime numbers whose multiples are to be sifted from `support`. We work with
  their product because it lets us treat `nu` as a multiplicative arithmetic function. It also
  plays well with Moebius inversion. -/
  prodPrimes : ℕ
  prodPrimes_squarefree : Squarefree prodPrimes
  /-- A sequence representing how much each element of `support` should be weighted. -/
  weights : ℕ → ℝ
  weights_nonneg : ∀ n : ℕ, 0 ≤ weights n
  /-- An approximation to `∑ i in support, weights i`, i.e. the size of the unsifted set. A bad
  approximation will yield a weak statement in the final theorem. -/
  totalMass : ℝ
  /-- `nu d` is an approximation to the proportion of elements of `support` that are a multiple of
  `d` -/
  nu : ArithmeticFunction ℝ
  nu_mult : nu.IsMultiplicative
  nu_pos_of_prime : ∀ p : ℕ, p.Prime → p ∣ prodPrimes → 0 < nu p
  nu_lt_one_of_prime : ∀ p : ℕ, p.Prime → p ∣ prodPrimes → nu p < 1

/-- The Selberg upper bound sieve in particular introduces a parameter called the `level` which
  gives the user control over the size of the error term. -/
structure SelbergSieve extends BoundingSieve where
  /-- The `level` of the sieve controls how many terms we include in the inclusion-exclusion type
  sum. A higher level will yield a tighter bound for the main term, but will also increase the
  size of the error term. -/
  level : ℝ
  one_le_level : 1 ≤ level

attribute [arith_mult] BoundingSieve.nu_mult

namespace Mathlib.Meta.Positivity

open Lean Qq

/-- Extension for the `positivity` tactic: `BoundingSieve.weights`. -/
@[positivity BoundingSieve.weights _ _]
meta def evalBoundingSieveWeights : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@BoundingSieve.weights $s $n) =>
    assertInstancesCommute
    pure (.nonnegative q(BoundingSieve.weights_nonneg $s $n))
  | _, _, _ => throwError "not BoundingSieve.weights"

end Mathlib.Meta.Positivity

namespace BoundingSieve
open SelbergSieve

theorem one_le_y {s : SelbergSieve} : 1 ≤ s.level := s.one_le_level

variable {s : BoundingSieve}

/-! Lemmas about prodPrimes. -/

theorem prodPrimes_ne_zero : s.prodPrimes ≠ 0 :=
  Squarefree.ne_zero s.prodPrimes_squarefree

theorem squarefree_of_dvd_prodPrimes {d : ℕ} (hd : d ∣ s.prodPrimes) : Squarefree d :=
  Squarefree.squarefree_of_dvd hd s.prodPrimes_squarefree

theorem squarefree_of_mem_divisors_prodPrimes {d : ℕ} (hd : d ∈ divisors s.prodPrimes) :
    Squarefree d := by
  simp only [Nat.mem_divisors] at hd
  exact Squarefree.squarefree_of_dvd hd.left s.prodPrimes_squarefree

/-! Lemmas about $\nu$. -/

theorem prod_primeFactors_nu {d : ℕ} (hd : d ∣ s.prodPrimes) :
    ∏ p ∈ d.primeFactors, s.nu p = s.nu d := by
  rw [← s.nu_mult.map_prod_of_subset_primeFactors _ _ subset_rfl,
    Nat.prod_primeFactors_of_squarefree <| Squarefree.squarefree_of_dvd hd s.prodPrimes_squarefree]

theorem nu_pos_of_dvd_prodPrimes {d : ℕ} (hd : d ∣ s.prodPrimes) : 0 < s.nu d := by
  calc
    0 < ∏ p ∈ d.primeFactors, s.nu p := by
      apply prod_pos
      intro p hpd
      have hp_prime : p.Prime := prime_of_mem_primeFactors hpd
      have hp_dvd : p ∣ s.prodPrimes := (dvd_of_mem_primeFactors hpd).trans hd
      exact s.nu_pos_of_prime p hp_prime hp_dvd
    _ = s.nu d := prod_primeFactors_nu hd

theorem nu_ne_zero {d : ℕ} (hd : d ∣ s.prodPrimes) : s.nu d ≠ 0 := by
  apply _root_.ne_of_gt
  exact nu_pos_of_dvd_prodPrimes hd

theorem nu_lt_one_of_dvd_prodPrimes {d : ℕ} (hdP : d ∣ s.prodPrimes) (hd_ne_one : d ≠ 1) :
    s.nu d < 1 := by
  have hd_sq : Squarefree d := Squarefree.squarefree_of_dvd hdP s.prodPrimes_squarefree
  have := hd_sq.ne_zero
  calc
    s.nu d = ∏ p ∈ d.primeFactors, s.nu p := (prod_primeFactors_nu hdP).symm
    _ < ∏ p ∈ d.primeFactors, 1 := by
      apply prod_lt_prod_of_nonempty₀
      · intro p hp
        simp only [mem_primeFactors] at hp
        apply s.nu_pos_of_prime p hp.1 (hp.2.1.trans hdP)
      · intro p hpd; rw [mem_primeFactors_of_ne_zero hd_sq.ne_zero] at hpd
        apply s.nu_lt_one_of_prime p hpd.left (hpd.2.trans hdP)
      · simp only [nonempty_primeFactors, show 1 < d by lia]
    _ = 1 := by
      simp

/-- The factors `1 - ν p` over the prime factors of a divisor of `P` have a positive product. -/
theorem prod_primeFactors_one_sub_nu_pos {d : ℕ} (hd : d ∣ s.prodPrimes) :
    0 < ∏ p ∈ d.primeFactors, (1 - s.nu p) :=
  prod_pos fun p hp ↦ sub_pos.2 <| s.nu_lt_one_of_prime p (prime_of_mem_primeFactors hp)
    ((dvd_of_mem_primeFactors hp).trans hd)

/-! The evidence search `checked_nonzero` uses that `ν` and the product of the factors `1 - ν p`
do not vanish on the divisors of `P`: a hypothesis `hd : d ∣ s.prodPrimes` gives the evidence for
`(s.nu d)⁻¹` and for a quotient by `∏ p ∈ d.primeFactors, (1 - s.nu p)`. -/

macro_rules | `(tactic| checked_nonzero) => `(tactic|
    solve
    | assumption
    | (apply BoundingSieve.nu_ne_zero; assumption)
    | exact (BoundingSieve.prod_primeFactors_one_sub_nu_pos ‹_›).ne')

/-- The weight of all the elements that are a multiple of `d`. -/
@[simp]
def multSum (d : ℕ) : ℝ := ∑ n ∈ s.support, if d ∣ n then s.weights n else 0


/-- The remainder term in the approximation A_d = ν (d) X + R_d. This is the degree to which `nu`
  fails to approximate the proportion of the weight that is a multiple of `d`. -/
@[simp]
def rem (d : ℕ) : ℝ := s.multSum d - s.nu d * s.totalMass

/-- The weight of all the elements that are not a multiple of any of our finite set of primes. -/
def siftedSum : ℝ := ∑ d ∈ s.support, if Coprime s.prodPrimes d then s.weights d else 0

/-- `X * mainSum μ⁺` is the main term in the upper bound on `sifted_sum`. -/
def mainSum (muPlus : ℕ → ℝ) : ℝ := ∑ d ∈ divisors s.prodPrimes, muPlus d * s.nu d

/-- `errSum μ⁺` is the error term in the upper bound on `sifted_sum`. -/
def errSum (muPlus : ℕ → ℝ) : ℝ := ∑ d ∈ divisors s.prodPrimes, |muPlus d| * |s.rem d|

theorem multSum_eq_main_err (d : ℕ) : s.multSum d = s.nu d * s.totalMass + s.rem d := by
  rw [rem]
  ring

theorem siftedSum_eq_sum_support_mul_ite :
    s.siftedSum = ∑ d ∈ s.support, s.weights d * if Nat.gcd s.prodPrimes d = 1 then 1 else 0 := by
  rw [siftedSum]
  simp_rw [mul_ite, mul_one, mul_zero]

omit s in
/-- A sequence of coefficients $\mu^{+}$ is upper Moebius if $\mu * \zeta ≤ \mu^{+} * \zeta$. These
  coefficients then yield an upper bound on the sifted sum. -/
def IsUpperMoebius (muPlus : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, (if n = 1 then 1 else 0) ≤ ∑ d ∈ n.divisors, muPlus d

theorem siftedSum_le_sum_of_upperMoebius (muPlus : ℕ → ℝ) (h : IsUpperMoebius muPlus) :
    s.siftedSum ≤ ∑ d ∈ divisors s.prodPrimes, muPlus d * s.multSum d := by
  have hμ : ∀ n, (if n = 1 then 1 else 0) ≤ ∑ d ∈ n.divisors, muPlus d := h
  calc siftedSum ≤
    ∑ n ∈ s.support, s.weights n * ∑ d ∈ (Nat.gcd s.prodPrimes n).divisors, muPlus d := ?caseA
    _ = ∑ n ∈ s.support, ∑ d ∈ divisors s.prodPrimes,
        if d ∣ n then s.weights n * muPlus d else 0 := ?caseB
    _ = ∑ d ∈ divisors s.prodPrimes, muPlus d * multSum d := ?caseC
  case caseA =>
    rw [siftedSum_eq_sum_support_mul_ite]
    gcongr with n
    exact hμ (Nat.gcd s.prodPrimes n)
  case caseB =>
    simp_rw [mul_sum, ← sum_filter]
    congr with n
    congr
    · rw [← divisors_filter_dvd_of_dvd prodPrimes_ne_zero (Nat.gcd_dvd_left _ _)]
      ext x; simp +contextual [dvd_gcd_iff]
  case caseC =>
    rw [sum_comm]
    simp_rw [multSum, ← sum_filter, mul_sum, mul_comm]

theorem siftedSum_le_mainSum_errSum_of_upperMoebius (muPlus : ℕ → ℝ) (h : IsUpperMoebius muPlus) :
    s.siftedSum ≤ s.totalMass * s.mainSum muPlus + s.errSum muPlus := calc
  s.siftedSum ≤ ∑ d ∈ divisors s.prodPrimes, muPlus d * multSum d :=
    siftedSum_le_sum_of_upperMoebius _ h
  _ = s.totalMass * mainSum muPlus + ∑ d ∈ divisors s.prodPrimes, muPlus d * s.rem d := by
    rw [mainSum, mul_sum, ← sum_add_distrib]
    congr with d
    rw [rem]
    ring
  _ ≤ s.totalMass * mainSum muPlus + errSum muPlus := by
    rw [errSum]
    gcongr _ + ∑ d ∈ _, ?_ with d
    rw [← abs_mul]
    exact le_abs_self (muPlus d * s.rem d)

section LambdaSquared

/-- We consider a special class of upper bound sieves called the Λ² sieve. This class is
  parameterised by a sequence of real numbers. We will later choose a set of weights that minimises
  the main term, under a constraint that lets us control the error term. -/
def lambdaSquared (weights : ℕ → ℝ) : ℕ → ℝ := fun d =>
  ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors, if d = Nat.lcm d1 d2 then weights d1 * weights d2 else 0

private theorem sum_divisors_lambda_sq_larger_sum (f : ℕ → ℕ → ℕ → ℝ) (n : ℕ) :
    (∑ d ∈ n.divisors, ∑ d1 ∈ d.divisors, ∑ d2 ∈ d.divisors,
      if d = Nat.lcm d1 d2 then f d1 d2 d else 0) =
    (∑ d ∈ n.divisors, ∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors,
     if d = Nat.lcm d1 d2 then f d1 d2 d else 0) := by
  congr! 1 with d hd
  rw [mem_divisors] at hd
  suffices ∀ d1 d2, (d1 ∣ d ∧ d2 ∣ d ∧ d = d1.lcm d2) = (d = d1.lcm d2) by
    simp_rw [← Nat.divisors_filter_dvd_of_dvd hd.2 hd.1, sum_filter, ite_sum_zero, ← ite_and, this]
  simp +contextual [← and_assoc, Nat.dvd_lcm_left, Nat.dvd_lcm_right]

theorem upperMoebius_lambdaSquared (weights : ℕ → ℝ) (hw : weights 1 = 1) :
    IsUpperMoebius <| lambdaSquared weights := by
  dsimp only [IsUpperMoebius, lambdaSquared]
  intro n
  split_ifs
  · simp_all
  grw [sq_nonneg (∑ d ∈ n.divisors, weights d), sum_divisors_lambda_sq_larger_sum _ n, sum_comm]
  apply le_of_eq
  simp_rw [sq, mul_sum, sum_mul]
  congr! 1 with d1 hd1
  rw [sum_comm]
  congr! 1 with d2 hd2
  rw [sum_ite_eq_of_mem', mul_comm]
  -- Deal with the side goal from `sum_ite_eq_of_mem'`
  rw [mem_divisors, Nat.lcm_dvd_iff]
  exact ⟨⟨dvd_of_mem_divisors hd1, dvd_of_mem_divisors hd2⟩, (mem_divisors.mp hd1).2⟩

end LambdaSquared

section SelbergTerms

variable {s : BoundingSieve}

/-- These are the terms that appear in the sum `S` in the main term of the fundamental theorem.

$$S = \sum_{l \mid P, l \le \sqrt{y}} g(l)$$

The term $g(d) = \nu(d) / \prod_{p \mid d} (1 - \nu(p))$ is defined for the divisors `d` of `P`,
whose prime factors `p` satisfy `0 < ν p < 1`; the sieve does not constrain `ν` at other primes. -/
def selbergTerms (d : ℕ) (hd : d ∣ s.prodPrimes) : ℝ :=
  s.nu d / ∏ p ∈ d.primeFactors, (1 - s.nu p)

theorem selbergTerms_apply (d : ℕ) {hd : d ∣ s.prodPrimes} :
    s.selbergTerms d hd = s.nu d / ∏ p ∈ d.primeFactors, (1 - s.nu p) :=
  rfl

/-! Now follow some important identities involving `selbergTerms` -/

theorem selbergTerms_pos {l : ℕ} {hl : l ∣ s.prodPrimes} : 0 < s.selbergTerms l hl :=
  div_pos (nu_pos_of_dvd_prodPrimes hl) (prod_primeFactors_one_sub_nu_pos hl)

/-! The evidence search `checked_nonzero` uses that the Selberg terms are positive: the inverse
`(s.selbergTerms l hl)⁻¹` finds its evidence. -/

macro_rules | `(tactic| checked_nonzero) => `(tactic|
    solve
    | assumption
    | exact (BoundingSieve.selbergTerms_pos).ne')

theorem selbergTerms_one : s.selbergTerms 1 (one_dvd _) = 1 := by
  simp [selbergTerms_apply, s.nu_mult.map_one]

/-- The Selberg terms are multiplicative on the divisors of `P`. -/
theorem selbergTerms_mul {m n : ℕ} {hmn : m * n ∣ s.prodPrimes} :
    s.selbergTerms (m * n) hmn =
      s.selbergTerms m (dvd_of_mul_right_dvd hmn) *
        s.selbergTerms n (dvd_of_mul_left_dvd hmn) := by
  have hcop : m.Coprime n := coprime_of_squarefree_mul (squarefree_of_dvd_prodPrimes hmn)
  simp only [selbergTerms_apply, s.nu_mult.map_mul_of_coprime hcop, hcop.primeFactors_mul,
    prod_union hcop.disjoint_primeFactors]
  exact div_mul_div_comm₀.symm

theorem inv_selbergTerms_eq_sum_divisors_moebius_nu {l : ℕ} {hl : l ∣ s.prodPrimes} :
    (s.selbergTerms l hl)⁻¹ = ∑ x : l.divisorsAntidiagonal, μ x.1.1 *
      Checked.inv (s.nu x.1.2) (nu_ne_zero <|
        (dvd_of_mem_divisors <| snd_mem_divisors_of_mem_antidiagonal x.2).trans hl).isUnit := by
  have hl_sq : Squarefree l := squarefree_of_dvd_prodPrimes hl
  calc (s.selbergTerms l hl)⁻¹
      = ∑ d ∈ l.divisors, (μ d : ℝ) * s.nu d * (s.nu l)⁻¹ := by
        simp only [selbergTerms_apply, inv_div₀,
          s.nu_mult.prodPrimeFactors_one_sub_of_squarefree _ hl_sq]
        rw [div_eq_mul_inv₀, sum_mul]
    _ = ∑ x ∈ l.divisorsAntidiagonal, (μ x.1 : ℝ) * s.nu x.1 * (s.nu l)⁻¹ := by
        rw [← sum_attach l.divisors (fun d ↦ (μ d : ℝ) * s.nu d * (s.nu l)⁻¹)]
        exact (Nat.sum_divisorsAntidiagonal fun d _ ↦ (μ d : ℝ) * s.nu d * (s.nu l)⁻¹).symm
    _ = _ := by
        rw [← sum_coe_sort l.divisorsAntidiagonal]
        refine Fintype.sum_congr _ _ fun x ↦ ?_
        obtain ⟨hde, -⟩ := Nat.mem_divisorsAntidiagonal.1 x.2
        have hcop : (x.1.1).Coprime x.1.2 :=
          coprime_of_squarefree_mul (by rw [hde]; exact hl_sq)
        have hνl : s.nu l = s.nu x.1.1 * s.nu x.1.2 := by
          rw [← s.nu_mult.map_mul_of_coprime hcop, hde]
        rw [mul_assoc]
        congr 1
        simp only [hνl]
        field_simp

theorem nu_inv_eq_sum_divisors_inv_selbergTerms {d : ℕ} (hdP : d ∣ s.prodPrimes) :
    (s.nu d)⁻¹ = ∑ l ∈ divisors s.prodPrimes,
      if hl : l ∣ d then (s.selbergTerms l (hl.trans hdP))⁻¹ else 0 := by
  -- Möbius inversion on the divisors of `P`; outside them, the extensions take the value `0`.
  let f : ℕ → ℝ := fun l ↦ if hl : l ∣ s.prodPrimes then (s.selbergTerms l hl)⁻¹ else 0
  let g : ℕ → ℝ := fun n ↦ if hn : n ∣ s.prodPrimes then (s.nu n)⁻¹ else 0
  have hfg : ∀ n > 0, n ∈ {n | n ∣ s.prodPrimes} → ∑ i ∈ n.divisors, f i = g n := by
    refine (sum_eq_iff_sum_mul_moebius_eq_on _ fun _ _ ↦ Nat.dvd_trans).mpr fun n _ hn ↦ ?_
    have hnP : n ∣ s.prodPrimes := hn
    simp only [f, dite_eq_left hnP, inv_selbergTerms_eq_sum_divisors_moebius_nu]
    rw [← sum_coe_sort n.divisorsAntidiagonal]
    refine Fintype.sum_congr _ _ fun x ↦ ?_
    have he : x.1.2 ∣ s.prodPrimes :=
      (dvd_of_mem_divisors <| snd_mem_divisors_of_mem_antidiagonal x.2).trans hnP
    simp only [g, dite_eq_left he]
  have hd_pos : 0 < d := Nat.pos_of_ne_zero <| ne_zero_of_dvd_ne_zero prodPrimes_ne_zero hdP
  have hd := hfg d hd_pos hdP
  simp only [g, dite_eq_left hdP] at hd
  rw [← hd, ← divisors_filter_dvd_of_dvd prodPrimes_ne_zero hdP, sum_filter]
  refine sum_congr rfl fun l _ ↦ ?_
  split_ifs with hl
  · simp only [f, dite_eq_left (hl.trans hdP)]
  · rfl

theorem sum_divisors_selbergTerms_eq_selbergTerms_mul_nu_inv {d : ℕ} (hd : d ∣ s.prodPrimes) :
    (∑ l ∈ divisors s.prodPrimes, if hl : l ∣ d then s.selbergTerms l (hl.trans hd) else 0) =
      s.selbergTerms d hd * (s.nu d)⁻¹ := by
  -- The Selberg terms and their inverses, extended by `0` outside the divisors of `P`.
  let g : ℕ → ℝ := fun l ↦ if hl : l ∣ s.prodPrimes then s.selbergTerms l hl else 0
  let gInv : ℕ → ℝ := fun l ↦ if hl : l ∣ s.prodPrimes then (s.selbergTerms l hl)⁻¹ else 0
  have hg : (∑ l ∈ divisors s.prodPrimes,
      if hl : l ∣ d then s.selbergTerms l (hl.trans hd) else 0) = ∑ l ∈ d.divisors, g l := by
    rw [← divisors_filter_dvd_of_dvd prodPrimes_ne_zero hd, sum_filter]
    refine sum_congr rfl fun l _ ↦ ?_
    split_ifs with hl
    · simp only [g, dite_eq_left (hl.trans hd)]
    · rfl
  have hgInv : (∑ l ∈ divisors s.prodPrimes,
      if hl : l ∣ d then (s.selbergTerms l (hl.trans hd))⁻¹ else 0) =
        ∑ l ∈ d.divisors, gInv l := by
    rw [← divisors_filter_dvd_of_dvd prodPrimes_ne_zero hd, sum_filter]
    refine sum_congr rfl fun l _ ↦ ?_
    split_ifs with hl
    · simp only [gInv, dite_eq_left (hl.trans hd)]
    · rfl
  rw [hg, ← sum_div_divisors d g, nu_inv_eq_sum_divisors_inv_selbergTerms hd, hgInv,
    ← sum_attach d.divisors gInv, mul_sum]
  refine sum_congr rfl fun l _ ↦ ?_
  have hld := dvd_of_mem_divisors l.property
  have hl := (pos_of_mem_divisors l.property).ne'
  have hfac : l.val * Nat.euclideanDiv d l.val hl = d := by
    simpa only [Nat.mod_eq_zero_of_dvd hld, Nat.add_zero, Nat.mul_comm] using
      Nat.euclideanDiv_mul_add_mod d l.val hl
  have hdl : Nat.euclideanDiv d l.val hl ∣ d := ⟨l.val, by simpa [Nat.mul_comm] using hfac.symm⟩
  have hmul := selbergTerms_mul (s := s) (m := l.val) (n := Nat.euclideanDiv d l.val hl)
    (hmn := by rwa [hfac])
  simp only [hfac] at hmul
  simp only [g, gInv, dite_eq_left (hld.trans hd), dite_eq_left (hdl.trans hd), hmul]
  rw [mul_comm (s.selbergTerms l _), mul_assoc, mul_inv_cancel₀, mul_one]

end SelbergTerms

section QuadForm

/-- The main sum we get from Λ² coefficients is a quadratic form. Used to prove the Selberg sieve
  identity by choosing weights that maximize this sum. The sums run over the divisors of `P`
  themselves, where `ν` does not vanish. -/
theorem mainSum_lambdaSquared_eq_sum_sum_mul (w : ℕ → ℝ) :
    s.mainSum (lambdaSquared w) =
      ∑ d1 : divisors s.prodPrimes, ∑ d2 : divisors s.prodPrimes,
        s.nu d1 * w d1 * s.nu d2 * w d2 * Checked.inv (s.nu (Nat.gcd d1 d2))
          (nu_ne_zero <| (Nat.gcd_dvd_left _ _).trans (dvd_of_mem_divisors d1.2)).isUnit := by
  calc mainSum (lambdaSquared w)
      = ∑ d ∈ divisors s.prodPrimes, ∑ d1 ∈ divisors d, ∑ d2 ∈ divisors d,
          if d = d1.lcm d2 then w d1 * w d2 * s.nu d else 0 := ?caseA
    _ = ∑ d ∈ divisors s.prodPrimes, ∑ d1 ∈ divisors s.prodPrimes, ∑ d2 ∈ divisors s.prodPrimes,
          if d = d1.lcm d2 then w d1 * w d2 * s.nu d else 0 := sum_divisors_lambda_sq_larger_sum _ _
    _ = ∑ d1 ∈ divisors s.prodPrimes, ∑ d2 ∈ divisors s.prodPrimes,
          w d1 * w d2 * s.nu (d1.lcm d2) := ?caseB
    _ = _ := ?caseC
  case caseA =>
    simp [mainSum, lambdaSquared, sum_mul]
  case caseB =>
    rw [sum_comm, sum_congr rfl]; intro d1 hd1
    rw [sum_comm, sum_congr rfl]; intro d2 hd2
    have h : d1.lcm d2 ∣ s.prodPrimes :=
      Nat.lcm_dvd_iff.mpr ⟨dvd_of_mem_divisors hd1, dvd_of_mem_divisors hd2⟩
    rw [sum_ite_eq_of_mem' (divisors s.prodPrimes) (d1.lcm d2) _
      (mem_divisors.mpr ⟨h, prodPrimes_ne_zero⟩)]
  case caseC =>
    rw [← sum_coe_sort (divisors s.prodPrimes)]
    refine Fintype.sum_congr _ _ fun d1 ↦ ?_
    rw [← sum_coe_sort (divisors s.prodPrimes)]
    refine Fintype.sum_congr _ _ fun d2 ↦ ?_
    rw [s.nu_mult.map_lcm (nu_ne_zero <| (Nat.gcd_dvd_left _ _).trans (dvd_of_mem_divisors d1.2)),
      div_eq_mul_inv₀]
    ring

/-- The main sum we get from Λ² coefficients can be written as a diagonalized quadratic form with
  eigenvalues given by `1/selbergTerms`. The outer sum runs over the divisors of `P` themselves,
  where the Selberg terms are defined. -/
theorem mainSum_lambdaSquared_eq_sum_mul_sum_sq (w : ℕ → ℝ) :
    s.mainSum (lambdaSquared w) =
      ∑ l : divisors s.prodPrimes, (s.selbergTerms l (dvd_of_mem_divisors l.2))⁻¹ *
        (∑ d ∈ divisors s.prodPrimes, if (l : ℕ) ∣ d then s.nu d * w d else 0) ^ 2 := by
  -- The inverses of the Selberg terms, extended by `0` outside the divisors of `P`.
  let G : ℕ → ℝ := fun l ↦ if hl : l ∣ s.prodPrimes then (s.selbergTerms l hl)⁻¹ else 0
  calc mainSum (lambdaSquared w) =
    ∑ d1 ∈ divisors s.prodPrimes, ∑ d2 ∈ divisors s.prodPrimes, (∑ l ∈ divisors s.prodPrimes,
      if l ∣ d1.gcd d2 then G l * (s.nu d1 * w d1) * (s.nu d2 * w d2) else 0) :=
        ?caseA
    _ = ∑ l ∈ divisors s.prodPrimes, ∑ d1 ∈ divisors s.prodPrimes, ∑ d2 ∈ divisors s.prodPrimes,
      if l ∣ Nat.gcd d1 d2 then G l * (s.nu d1 * w d1) * (s.nu d2 * w d2) else 0 :=
        ?caseB
    _ = ∑ l ∈ divisors s.prodPrimes,
      G l * (∑ d ∈ divisors s.prodPrimes, if l ∣ d then s.nu d * w d else 0) ^ 2 :=
        ?caseC
    _ = _ := ?caseD
  case caseA =>
    rw [mainSum_lambdaSquared_eq_sum_sum_mul w, ← sum_coe_sort (divisors s.prodPrimes)]
    refine Fintype.sum_congr _ _ fun d1 ↦ ?_
    rw [← sum_coe_sort (divisors s.prodPrimes)]
    refine Fintype.sum_congr _ _ fun d2 ↦ ?_
    have hgcd_dvd : Nat.gcd d1 d2 ∣ s.prodPrimes :=
      (Nat.gcd_dvd_left _ _).trans (dvd_of_mem_divisors d1.2)
    rw [nu_inv_eq_sum_divisors_inv_selbergTerms hgcd_dvd, mul_sum]
    refine sum_congr rfl fun l _ ↦ ?_
    split_ifs with hl
    · simp only [G, dite_eq_left (hl.trans hgcd_dvd)]
      ring
    · rw [mul_zero]
  case caseB =>
    rw [eq_comm, sum_comm, sum_congr rfl fun _ _ ↦ sum_comm]
  case caseC =>
    simp_rw [← sum_filter, sq, sum_mul, mul_sum, sum_filter, ite_sum_zero,
      ← ite_and, Nat.dvd_gcd_iff, mul_assoc]
  case caseD =>
    rw [← sum_coe_sort (divisors s.prodPrimes)]
    refine Fintype.sum_congr _ _ fun l ↦ ?_
    simp only [G, dite_eq_left (dvd_of_mem_divisors l.2)]

end QuadForm

end BoundingSieve
