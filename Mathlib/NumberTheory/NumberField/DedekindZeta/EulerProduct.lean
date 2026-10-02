/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module

public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.NumberTheory.NumberField.DedekindZeta

/-!
# The Euler product of the Dedekind zeta function

For real arguments greater than one, the Dedekind zeta function is the sum of inverse
norm powers over nonzero ideals. Its logarithm is the sum of the logarithms of the
Euler factors over nonzero prime ideals.

The Euler product is proved by removing finitely many prime divisors from the ideal
sum, then applying dominated convergence to the remaining ideals.
-/

public section

noncomputable section

open Filter Ideal IsDedekindDomain
open scoped Topology nonZeroDivisors

namespace NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- For real `s > 1`, the Dedekind zeta function is the sum over nonzero ideals. -/
theorem dedekindZeta_re_eq_tsum {s : ℝ} (hs : 1 < s) :
    (dedekindZeta K s).re =
      ∑' I : (Ideal (𝓞 K))⁰, (absNorm (I : Ideal (𝓞 K)) : ℝ) ^ (-s) := by
  have hzero : (0 : ℝ) ^ (-s) = 0 := Real.zero_rpow (by linarith)
  have hz (I : Ideal (𝓞 K)) (hI : I ∉ Set.range (Subtype.val : (Ideal (𝓞 K))⁰ → _)) :
      (absNorm I : ℝ) ^ (-s) = 0 := by
    have : I = 0 := by
      by_contra h
      exact hI ⟨⟨I, mem_nonZeroDivisors_of_ne_zero h⟩, rfl⟩
    simp [this, hzero]
  have hsum : Summable (fun I : Ideal (𝓞 K) ↦ (absNorm I : ℝ) ^ (-s)) :=
    (Subtype.val_injective.summable_iff hz).mp (summable_absNorm_rpow K hs)
  rw [dedekindZeta, LSeries, Complex.re_tsum (LSeriesSummable_dedekindZeta K hs),
    Subtype.val_injective.tsum_eq (Function.support_subset_iff'.mpr hz)]
  calc
    _ = ∑' n : ℕ, (Nat.card {I : Ideal (𝓞 K) // absNorm I = n} : ℝ) *
        (n : ℝ) ^ (-s) := by
      apply tsum_congr
      intro n
      by_cases hn : n = 0
      · simp [hn, hzero]
      · rw [LSeries.term_of_ne_zero hn]
        rw [show (n : ℂ) ^ (s : ℂ) = (((n : ℝ) ^ s : ℝ) : ℂ) from
          (Complex.ofReal_cpow (Nat.cast_nonneg n) s).symm]
        change (((Nat.card {I : Ideal (𝓞 K) // absNorm I = n} : ℝ) : ℂ) /
          (((n : ℝ) ^ s : ℝ) : ℂ)).re = _
        rw [← Complex.ofReal_div, Complex.ofReal_re,
          Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
    _ = _ := by
      rw [← hsum.hasSum.tsum_fiberwise absNorm |>.tsum_eq]
      apply tsum_congr
      intro n
      have := (finite_setOfPred_absNorm_eq (S := 𝓞 K) n).to_subtype
      change _ = ∑' I : {I : Ideal (𝓞 K) // absNorm I = n}, _
      simp_rw [show ∀ I : {I : Ideal (𝓞 K) // absNorm I = n}, absNorm I.1 = n from
        fun I ↦ I.property]
      simp [tsum_const, nsmul_eq_mul]

private def primeIdeal (p : HeightOneSpectrum (𝓞 K)) : (Ideal (𝓞 K))⁰ :=
  ⟨p.asIdeal, mem_nonZeroDivisors_of_ne_zero p.ne_bot⟩

omit [NumberField K] in
private theorem primeIdeal_injective :
    Function.Injective (primeIdeal K) := by
  intro p q h
  exact HeightOneSpectrum.ext (congrArg Subtype.val h)

private def idealWeight (s : ℝ) (I : (Ideal (𝓞 K))⁰) : ℝ :=
  (absNorm (I : Ideal (𝓞 K)) : ℝ) ^ (-s)

private theorem idealWeight_nonneg (s : ℝ) (I : (Ideal (𝓞 K))⁰) :
    0 ≤ idealWeight K s I := Real.rpow_nonneg (Nat.cast_nonneg _) _

private theorem idealWeight_mul (s : ℝ) (I J : (Ideal (𝓞 K))⁰) :
    idealWeight K s (I * J) = idealWeight K s I * idealWeight K s J := by
  simp only [idealWeight, Submonoid.coe_mul, map_mul, Nat.cast_mul,
    Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]

private def sievedWeight (s : ℝ) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (I : (Ideal (𝓞 K))⁰) : ℝ := by
  classical
  exact if ∀ p ∈ S, ¬p.asIdeal ∣ (I : Ideal (𝓞 K)) then idealWeight K s I else 0

private theorem norm_sievedWeight_le (s : ℝ) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (I : (Ideal (𝓞 K))⁰) : ‖sievedWeight K s S I‖ ≤ idealWeight K s I := by
  classical
  unfold sievedWeight
  split_ifs
  · exact (Real.norm_of_nonneg (idealWeight_nonneg K s I)).le
  · simpa using idealWeight_nonneg K s I

private theorem summable_sievedWeight {s : ℝ} (hs : 1 < s)
    (S : Finset (HeightOneSpectrum (𝓞 K))) : Summable (sievedWeight K s S) :=
  (summable_absNorm_rpow K hs).of_norm_bounded (norm_sievedWeight_le K s S)

private theorem sievedWeight_mul (s : ℝ) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (p : HeightOneSpectrum (𝓞 K)) (hp : p ∉ S) (I : (Ideal (𝓞 K))⁰) :
    sievedWeight K s S (primeIdeal K p * I) =
      idealWeight K s (primeIdeal K p) * sievedWeight K s S I := by
  classical
  have hdiv (q : HeightOneSpectrum (𝓞 K)) (hq : q ∈ S) :
      q.asIdeal ∣ (primeIdeal K p * I : Ideal (𝓞 K)) ↔ q.asIdeal ∣ (I : Ideal (𝓞 K)) := by
    change q.asIdeal ∣ p.asIdeal * (I : Ideal (𝓞 K)) ↔ _
    rw [(Ideal.prime_of_isPrime q.ne_bot q.isPrime).dvd_mul]
    have hqp : ¬q.asIdeal ∣ p.asIdeal := by
      intro h
      have heq := (Prime.dvd_prime_iff_associated
        (Ideal.prime_of_isPrime q.ne_bot q.isPrime)
        (Ideal.prime_of_isPrime p.ne_bot p.isPrime)).mp h
      have : q = p := HeightOneSpectrum.ext (associated_iff_eq.mp heq)
      exact hp (this ▸ hq)
    simp [hqp]
  have hfree : (∀ q ∈ S, ¬q.asIdeal ∣ (primeIdeal K p * I : Ideal (𝓞 K))) ↔
      ∀ q ∈ S, ¬q.asIdeal ∣ (I : Ideal (𝓞 K)) := by
    constructor <;> intro h q hq
    · rw [← hdiv q hq]
      exact h q hq
    · rw [hdiv q hq]
      exact h q hq
  simp only [sievedWeight, Submonoid.coe_mul, hfree]
  split_ifs <;> simp [idealWeight_mul]

open Classical in
private theorem tsum_sievedWeight_dvd (s : ℝ)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (p : HeightOneSpectrum (𝓞 K)) (hp : p ∉ S) :
    (∑' I : (Ideal (𝓞 K))⁰,
      if p.asIdeal ∣ (I : Ideal (𝓞 K)) then sievedWeight K s S I else 0) =
      idealWeight K s (primeIdeal K p) * ∑' I, sievedWeight K s S I := by
  classical
  have hinj : Function.Injective (fun I : (Ideal (𝓞 K))⁰ ↦ primeIdeal K p * I) :=
    fun _ _ h ↦ mul_left_cancel h
  have hsupport : Function.support (fun I : (Ideal (𝓞 K))⁰ ↦
      if p.asIdeal ∣ (I : Ideal (𝓞 K)) then sievedWeight K s S I else 0) ⊆
      Set.range (fun I : (Ideal (𝓞 K))⁰ ↦ primeIdeal K p * I) := by
    intro I hI
    have hd : p.asIdeal ∣ (I : Ideal (𝓞 K)) := by
      by_contra hd
      simp [Function.mem_support, hd] at hI
    obtain ⟨J, hJ⟩ := hd
    have hJ0 : J ≠ 0 := by
      intro h
      exact nonZeroDivisors.ne_zero I.property (by simpa [h] using hJ)
    exact ⟨⟨J, mem_nonZeroDivisors_of_ne_zero hJ0⟩, Subtype.ext hJ.symm⟩
  rw [← hinj.tsum_eq hsupport]
  simp only [Submonoid.coe_mul]
  simp_rw [show ∀ I : (Ideal (𝓞 K))⁰,
    p.asIdeal ∣ (primeIdeal K p * I : Ideal (𝓞 K)) from fun I ↦ dvd_mul_right _ _,
    ite_true, sievedWeight_mul K s S p hp]
  exact tsum_mul_left

private theorem tsum_sievedWeight {s : ℝ} (hs : 1 < s)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (∑' I, sievedWeight K s S I) =
      (∑' I, idealWeight K s I) * ∏ p ∈ S, (1 - idealWeight K s (primeIdeal K p)) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [sievedWeight]
  | @insert p S hp ih =>
    have hsub (I : (Ideal (𝓞 K))⁰) :
        sievedWeight K s (insert p S) I = sievedWeight K s S I -
          if p.asIdeal ∣ (I : Ideal (𝓞 K)) then sievedWeight K s S I else 0 := by
      by_cases hd : p.asIdeal ∣ (I : Ideal (𝓞 K)) <;>
        simp [sievedWeight, hd]
    have hdivsum : Summable (fun I : (Ideal (𝓞 K))⁰ ↦
        if p.asIdeal ∣ (I : Ideal (𝓞 K)) then sievedWeight K s S I else 0) := by
      exact ((summable_sievedWeight K hs S).indicator
        {I | p.asIdeal ∣ (I : Ideal (𝓞 K))}).congr fun I ↦ by
          simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    simp_rw [hsub]
    rw [(summable_sievedWeight K hs S).tsum_sub hdivsum,
      tsum_sievedWeight_dvd K s S p hp, ih, Finset.prod_insert hp]
    ring

private theorem tendsto_tsum_sievedWeight {s : ℝ} (hs : 1 < s) :
    Tendsto (fun S : Finset (HeightOneSpectrum (𝓞 K)) ↦ ∑' I, sievedWeight K s S I)
      atTop (𝓝 1) := by
  classical
  have hlim (I : (Ideal (𝓞 K))⁰) :
      Tendsto (fun S : Finset (HeightOneSpectrum (𝓞 K)) ↦ sievedWeight K s S I)
        atTop (𝓝 (if I = 1 then 1 else 0)) := by
    by_cases hI : I = 1
    · subst I
      have hfree (p : HeightOneSpectrum (𝓞 K)) : ¬p.asIdeal ∣ (⊤ : Ideal (𝓞 K)) := by
        simpa only [Ideal.one_eq_top] using
          (Ideal.prime_of_isPrime p.ne_bot p.isPrime).not_dvd_one
      simp [sievedWeight, idealWeight, hfree]
    · have hunit : ¬IsUnit (I : Ideal (𝓞 K)) := by
        intro hu
        exact hI (Subtype.ext (by simpa using Ideal.isUnit_iff.mp hu))
      obtain ⟨P, hP, hPI⟩ := WfDvdMonoid.exists_irreducible_factor hunit
        (nonZeroDivisors.ne_zero I.property)
      let p : HeightOneSpectrum (𝓞 K) :=
        ⟨P, Ideal.isPrime_of_prime hP.prime, hP.ne_zero⟩
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_finset_mem_atTop p] with S hS
      have hfree : ¬∀ q ∈ S, ¬q.asIdeal ∣ (I : Ideal (𝓞 K)) := fun h ↦ h p hS hPI
      simp [sievedWeight, hI, hfree]
  have ht := tendsto_tsum_of_dominated_convergence (summable_absNorm_rpow K hs) hlim
    (Filter.Eventually.of_forall (fun S I ↦ norm_sievedWeight_le K s S I))
  simpa using ht

private theorem prime_idealWeight_lt_one {s : ℝ} (hs : 1 < s)
    (p : HeightOneSpectrum (𝓞 K)) : idealWeight K s (primeIdeal K p) < 1 := by
  have hpos : 0 < absNorm p.asIdeal := Nat.pos_of_ne_zero <|
    Ideal.absNorm_eq_zero_iff.not.mpr p.ne_bot
  have hne : absNorm p.asIdeal ≠ 1 := Ideal.absNorm_eq_one_iff.not.mpr p.isPrime.ne_top
  have hone : (1 : ℝ) < absNorm p.asIdeal := by exact_mod_cast lt_of_le_of_ne hpos hne.symm
  exact Real.rpow_lt_one_of_one_lt_of_neg hone (by linarith)

/-- The logarithms of the Euler factors converge absolutely for real `s > 1`. -/
theorem summable_neg_log_one_sub_absNorm_rpow {s : ℝ} (hs : 1 < s) :
    Summable (fun p : HeightOneSpectrum (𝓞 K) ↦
      -Real.log (1 - (absNorm p.asIdeal : ℝ) ^ (-s))) := by
  have h := (summable_absNorm_rpow K hs).comp_injective (primeIdeal_injective K)
  simpa only [sub_eq_add_neg, Function.comp_apply, primeIdeal] using
    (Real.summable_log_one_add_of_summable h.neg).neg

/-- The logarithmic Euler product for the Dedekind zeta function on the real axis. -/
theorem log_dedekindZeta_eq_tsum {s : ℝ} (hs : 1 < s) :
    Real.log ((dedekindZeta K s).re) =
      ∑' p : HeightOneSpectrum (𝓞 K), -Real.log (1 - (absNorm p.asIdeal : ℝ) ^ (-s)) := by
  have hlog := (summable_neg_log_one_sub_absNorm_rpow K hs).neg
  simp only [neg_neg] at hlog
  have hprod := Real.hasProd_of_hasSum_log
    (fun p : HeightOneSpectrum (𝓞 K) ↦ sub_pos.mpr (prime_idealWeight_lt_one K hs p))
    hlog.hasSum
  have hmul := (tendsto_const_nhds (x := ∑' I, idealWeight K s I)).mul hprod
  have heq : (∑' I, idealWeight K s I) *
      Real.exp (∑' p : HeightOneSpectrum (𝓞 K),
        Real.log (1 - (absNorm p.asIdeal : ℝ) ^ (-s))) = 1 := by
    apply tendsto_nhds_unique hmul
    change Tendsto (fun S : Finset (HeightOneSpectrum (𝓞 K)) ↦
      (∑' I, idealWeight K s I) * ∏ p ∈ S, (1 - idealWeight K s (primeIdeal K p)))
      atTop (𝓝 1)
    exact (tendsto_tsum_sievedWeight K hs).congr (tsum_sievedWeight K hs)
  rw [dedekindZeta_re_eq_tsum K hs]
  change Real.log (∑' I, idealWeight K s I) = _
  rw [eq_div_iff (Real.exp_ne_zero _) |>.mpr heq, one_div, Real.log_inv, Real.log_exp,
    tsum_neg]

end NumberField
