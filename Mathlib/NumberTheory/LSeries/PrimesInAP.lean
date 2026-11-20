/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.NumberTheory.LSeries.Linearity
public import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Dirichlet's Theorem on primes in arithmetic progression

The goal of this file is to prove **Dirichlet's Theorem**: If `q` is a positive natural number
and `a : ZMod q` is invertible, then there are infinitely many prime numbers `p` such that
`(p : ZMod q) = a`.

The main steps of the proof are as follows.
1. Define `ArithmeticFunction.vonMangoldt.residueClass a` for `a : ZMod q`, which is
   a function `ℕ → ℝ` taking the value zero when `(n : ZMod q) ≠ a` and `Λ n` else
   (where `Λ` is the von Mangoldt function `ArithmeticFunction.vonMangoldt`; we have
   `Λ (p^k) = log p` for prime powers and `Λ n = 0` otherwise.)
2. Show that this function can be written as a linear combination of functions
   of the form `χ * Λ` (pointwise product) with Dirichlet characters `χ` mod `q`.
   See `ArithmeticFunction.vonMangoldt.residueClass_eq`.
3. This implies that the L-series of `ArithmeticFunction.vonMangoldt.residueClass a`
   agrees (on `re s > 1`) with the corresponding linear combination of negative logarithmic
   derivatives of Dirichlet L-functions.
   See `ArithmeticFunction.vonMangoldt.LSeries_residueClass_eq`.
4. Define an auxiliary function `ArithmeticFunction.vonMangoldt.LFunctionResidueClassAux a` that is
   this linear combination of negative logarithmic derivatives of L-functions minus
   `(q.totient)⁻¹/(s-1)`, which cancels the pole at `s = 1`.
   See `ArithmeticFunction.vonMangoldt.eqOn_LFunctionResidueClassAux` for the statement
   that the auxiliary function agrees with the L-series of
   `ArithmeticFunction.vonMangoldt.residueClass` up to the term `(q.totient)⁻¹/(s-1)`.
5. Show that the auxiliary function is continuous on `re s ≥ 1`;
   see `ArithmeticFunction.vonMangoldt.continuousOn_LFunctionResidueClassAux`.
   This relies heavily on the non-vanishing of Dirichlet L-functions on the *closed*
   half-plane `re s ≥ 1` (`DirichletCharacter.LFunction_ne_zero_of_one_le_re`), which
   in turn can only be stated since we know that the L-series of a Dirichlet character
   extends to an entire function (unless the character is trivial; then there is a
   simple pole at `s = 1`); see `DirichletCharacter.LFunction_eq_LSeries`
   (contributed by David Loeffler).
6. Show that the sum of `Λ n / n` over any residue class, but *excluding* the primes, converges.
   See `ArithmeticFunction.vonMangoldt.summable_residueClass_non_primes_div`.
7. Combining these ingredients, we can deduce that the sum of `Λ n / n` over
   the *primes* in a residue class must diverge.
   See `ArithmeticFunction.vonMangoldt.not_summable_residueClass_prime_div`.
8. This finally easily implies that there must be infinitely many primes in the residue class.

## Definitions

* `ArithmeticFunction.vonMangoldt.residueClass a` (see above).
* `ArithmeticFunction.vonMangoldt.continuousOn_LFunctionResidueClassAux` (see above).

## Main Result

We give two versions of **Dirichlet's Theorem**:
* `Nat.infinite_setOfPred_prime_and_eq_mod` states that the set of primes `p`
  such that `(p : ZMod q) = a` is infinite (when `a` is invertible in `ZMod q`).
* `Nat.forall_exists_prime_gt_and_eq_mod` states that for any natural number `n`
  there is a prime `p > n` such that `(p : ZMod q) = a`.

## Tags

prime number, arithmetic progression, residue class, Dirichlet's Theorem
-/

@[expose] public section

/-!
### The L-series of the von Mangoldt function restricted to a residue class
-/

section arith_prog

namespace ArithmeticFunction.vonMangoldt

open Complex LSeries DirichletCharacter

open scoped LSeries.notation

variable {q : ℕ} (a : ZMod q)

/-- The von Mangoldt function restricted to the residue class `a` mod `q`. -/
noncomputable abbrev residueClass : ℕ → ℝ :=
  {n : ℕ | (n : ZMod q) = a}.indicator (vonMangoldt ·)

lemma residueClass_nonneg (n : ℕ) : 0 ≤ residueClass a n :=
  Set.indicator_apply_nonneg fun _ ↦ vonMangoldt_nonneg

lemma residueClass_le (n : ℕ) : residueClass a n ≤ vonMangoldt n :=
  Set.indicator_apply_le' (fun _ ↦ le_rfl) (fun _ ↦ vonMangoldt_nonneg)

@[simp]
lemma residueClass_apply_zero : residueClass a 0 = 0 := by
  simp only [Set.indicator_apply_eq_zero, Set.mem_ofPred_eq, Nat.cast_zero, map_zero,
    implies_true]

lemma abscissaOfAbsConv_residueClass_le_one :
    abscissaOfAbsConv ↗(residueClass a) ≤ 1 := by
  refine abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy ↦ ?_
  unfold LSeriesSummable
  have := LSeriesSummable_vonMangoldt <| show 1 < (y : ℂ).re by simp only [ofReal_re, hy]
  convert! this.indicator {n : ℕ | (n : ZMod q) = a}
  ext1 n
  by_cases hn : (n : ZMod q) = a
  · simp only [term, Set.indicator, Set.mem_ofPred_eq, hn, ↓reduceIte]
  · simp +contextual only [term, Set.mem_ofPred_eq, hn, not_false_eq_true, Set.indicator_of_notMem,
      ofReal_zero, zero_div]
    split_ifs <;> rfl

/-- The set we are interested in (prime numbers in the residue class `a`) is the same as the support
of `ArithmeticFunction.vonMangoldt.residueClass` restricted to primes (and divided by `n`;
this is how this result is used later). -/
lemma support_residueClass_prime_div :
    Function.support (fun n : ℕ ↦ if hn : n.Prime then
      Checked.div (residueClass a n) (n : ℝ) (Nat.cast_ne_zero.mpr hn.ne_zero).isUnit else 0) =
      {p : ℕ | p.Prime ∧ (p : ZMod q) = a} := by
  ext p
  by_cases hp : p.Prime
  · simp [Function.mem_support, hp, Set.indicator_apply_eq_zero,
      vonMangoldt_ne_zero_iff.mpr hp.isPrimePow]
  · simp [Function.mem_support, hp]

private noncomputable def F₀ (n : ℕ) : ℝ :=
  if hn : n = 0 then 0 else
    Checked.div (if n.Prime then 0 else vonMangoldt n) (n : ℝ)
      (Nat.cast_ne_zero.mpr hn).isUnit

private noncomputable def F' (pk : Nat.Primes × ℕ) : ℝ := F₀ (pk.1 ^ (pk.2 + 1))

private noncomputable def F'' : Nat.Primes × ℕ → ℝ := F' ∘ (Prod.map _root_.id (· + 1))

private noncomputable def invPrime (p : Nat.Primes) : ℝ :=
  Checked.inv (p : ℝ) (Nat.cast_ne_zero.mpr p.prop.ne_zero).isUnit

private lemma F''_le (p : Nat.Primes) (k : ℕ) : F'' (p, k) ≤ 2 * invPrime p ^ (k + 3 / 2 : ℝ) := by
  have hp : 0 < (p : ℝ) := Nat.cast_pos.mpr p.prop.pos
  have hp' : 0 < invPrime p := inv_pos.mpr hp
  calc _
    _ = Real.log p * invPrime p ^ (k + 2) := by
      have hpow : p.val ^ (k + 2) ≠ 0 := pow_ne_zero _ p.prop.ne_zero
      simp only [F'', Function.comp_apply, F', F₀, Prod.map_apply, id_eq, dite_eq_right hpow,
        le_add_iff_nonneg_left, zero_le, Nat.Prime.not_prime_pow, ↓reduceIte,
        vonMangoldt_apply_prime p.prop, vonMangoldt_apply_pow (Nat.zero_ne_add_one _).symm,
        Nat.cast_pow, div_eq_mul_inv₀, invPrime, inv_pow₀]
    _ ≤ (p : ℝ) ^ (1 / 2 : ℝ) / (1 / 2) * invPrime p ^ (k + 2) :=
        mul_le_mul_of_nonneg_right (Real.log_le_rpow_div p.val.cast_nonneg one_half_pos)
          (pow_nonneg hp'.le (k + 2))
    _ = 2 * invPrime p ^ (-1 / 2 : ℝ) * invPrime p ^ (k + 2) := by
      have hpow : invPrime p ^ (-1 / 2 : ℝ) = (p : ℝ) ^ (1 / 2 : ℝ) := by
        rw [show (-1 : ℝ) / 2 = -(1 / 2 : ℝ) by ring, invPrime,
          ← Real.rpow_neg_eq_inv_rpow, neg_neg]
      rw [hpow]
      field
    _ = _ := by
      rw [mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add hp', Nat.cast_add, Nat.cast_two,
        add_comm, add_assoc]
      norm_num

open Nat.Primes

private lemma summable_F'' : Summable F'' := by
  have hp₀ (p : Nat.Primes) : 0 < invPrime p := inv_pos.mpr (Nat.cast_pos.mpr p.prop.pos)
  have hp₁ (p : Nat.Primes) : invPrime p < 1 :=
    (inv_lt_one₀ <| mod_cast p.prop.pos).mpr <| Nat.one_lt_cast.mpr <| p.prop.one_lt
  suffices Summable fun (pk : Nat.Primes × ℕ) ↦ invPrime pk.1 ^ (pk.2 + 3 / 2 : ℝ) by
    refine (Summable.mul_left 2 this).of_nonneg_of_le (fun pk ↦ ?_) (fun pk ↦ F''_le pk.1 pk.2)
    simp only [F'', Function.comp_apply, F', F₀, Prod.map_fst, id_eq, Prod.map_snd, Nat.cast_pow]
    split_ifs <;> positivity [vonMangoldt_nonneg (n := (pk.1 : ℕ) ^ (pk.2 + 2))]
  conv => enter [1, pk]; rw [Real.rpow_add <| hp₀ pk.1, Real.rpow_natCast]
  refine (summable_prod_of_nonneg (fun pk ↦
    mul_nonneg (pow_nonneg (hp₀ pk.1).le _) (Real.rpow_nonneg (hp₀ pk.1).le _))).mpr
    ⟨(fun p ↦ ?_), ?_⟩
  · dsimp only -- otherwise the `exact` below times out
    exact Summable.mul_right _ <| summable_geometric_of_lt_one (hp₀ p).le (hp₁ p)
  · dsimp only
    conv => enter [1, p]; rw [tsum_mul_right, tsum_geometric_of_lt_one (hp₀ p).le (hp₁ p)]
    refine (summable_rpow.mpr (by norm_num : -(3 / 2 : ℝ) < -1)).mul_left 2
      |>.of_nonneg_of_le (fun p ↦ ?_) (fun p ↦ ?_)
    · exact mul_nonneg (inv_nonneg.mpr (sub_pos.mpr (hp₁ p)).le)
        (Real.rpow_nonneg (hp₀ p).le _)
    · have hpow : invPrime p ^ (3 / 2 : ℝ) = (p : ℝ) ^ (-(3 / 2 : ℝ)) := by
        rw [invPrime, Real.rpow_neg_eq_inv_rpow]
      have hpinv : invPrime p ≤ (2 : ℝ)⁻¹ :=
        (inv_le_inv₀ (Nat.cast_pos.mpr p.prop.pos) two_pos).mpr (by exact_mod_cast p.prop.two_le)
      have hhalf : (2 : ℝ)⁻¹ = 1 / 2 := (one_div₀ (2 : ℝ)).symm
      have hden : (2 : ℝ)⁻¹ ≤ 1 - invPrime p := by linarith
      have hbound : (1 - invPrime p)⁻¹ ≤ 2 := by
        simpa only [inv_inv₀] using
          (inv_le_inv₀ (sub_pos.mpr (hp₁ p)) (inv_pos.mpr (two_pos : (0 : ℝ) < 2))).mpr hden
      simpa only [hpow] using
        mul_le_mul_of_nonneg_right hbound (Real.rpow_nonneg p.val.cast_nonneg (-(3 / 2 : ℝ)))

/-- The function `n ↦ Λ n / n`, restricted to non-primes in a residue class, is summable.
This is used to convert results on `ArithmeticFunction.vonMangoldt.residueClass` to results
on primes in an arithmetic progression. -/
lemma summable_residueClass_non_primes_div :
    Summable fun n : ℕ+ ↦ (if Nat.Prime (n : ℕ) then 0 else residueClass a n) / (n : ℝ) := by
  have hF₀ : Summable F₀ := by
    have hprime (p : Nat.Primes) : F₀ p.val = 0 := by
      simp [F₀, p.prop, p.prop.ne_zero]
    refine (summable_subtype_iff_indicator (s := {n | IsPrimePow n}).mp ?_).congr
        fun n ↦ Set.indicator_apply_eq_self.mpr fun (hn : ¬ IsPrimePow n) ↦ ?_
    swap
    · by_cases hzero : n = 0 <;> simp [F₀, hzero, vonMangoldt_eq_zero_iff.mpr hn]
    have hFF' :
        F₀ ∘ Subtype.val (p := fun n ↦ n ∈ {n | IsPrimePow n}) = F' ∘ ⇑prodNatEquiv.symm := by
      refine (Equiv.eq_comp_symm prodNatEquiv (F₀ ∘ Subtype.val) F').mpr ?_
      ext1 n
      simp only [Function.comp_apply, F']
      congr
    rw [hFF']
    refine (Nat.Primes.prodNatEquiv.symm.summable_iff (f := F')).mpr ?_
    have hF'₀ (p : Nat.Primes) : F' (p, 0) = 0 := by simp only [zero_add, pow_one, hprime, F']
    have hF'₁ : F'' = F' ∘ (Prod.map _root_.id (· + 1)) := by
      ext1
      simp only [Function.comp_apply, Prod.map_fst, id_eq, Prod.map_snd, F'', F']
    refine (Function.Injective.summable_iff ?_ fun u hu ↦ ?_).mp <| hF'₁ ▸ summable_F''
    · exact Function.Injective.prodMap (fun ⦃a₁ a₂⦄ a ↦ a) <| add_left_injective 1
    · simp only [Set.range_prodMap, Set.range_id, Set.mem_prod, Set.mem_univ, Set.mem_range,
        Nat.exists_add_one_eq, true_and, not_lt, nonpos_iff_eq_zero] at hu
      rw [← hF'₀ u.1, ← hu]
  have hpos : Summable (fun n : ℕ+ ↦ F₀ n) := hF₀.comp_injective Subtype.val_injective
  refine hpos.of_nonneg_of_le (fun n ↦ ?_) (fun n ↦ ?_)
  · apply div_nonneg _ (Nat.cast_nonneg (n : ℕ))
    split_ifs <;> simp [residueClass_nonneg]
  · rw [F₀, dite_eq_right n.ne_zero]
    refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg (n : ℕ))
    split_ifs <;> simp [residueClass_le]

variable [NeZero q] {a}

private lemma isUnit_totient_cast {K : Type*} [DivisionSemiring K] [CharZero K] (q : ℕ)
    [NeZero q] : IsUnit (q.totient : K) :=
  (Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr q.pos_of_neZero).ne').isUnit

private lemma ne_one_of_one_lt_real_part {s : ℂ} (hs : 1 < s.re) : s ≠ 1 := by
  rintro rfl
  simp at hs

/-- We can express `ArithmeticFunction.vonMangoldt.residueClass` as a linear combination
of twists of the von Mangoldt function by Dirichlet characters. -/
lemma residueClass_apply (ha : IsUnit a) (n : ℕ) :
    residueClass a n =
      Checked.inv (q.totient : ℂ) (by exact isUnit_totient_cast q) *
        ∑ χ : DirichletCharacter ℂ q, χ (Checked.inv a ha) * χ n * vonMangoldt n := by
  have horth := sum_char_inv_mul_char_eq ℂ ha n
  rw [eq_inv_mul_iff_mul_eq₀]
  simp +contextual only [residueClass, Set.indicator_apply, Set.mem_ofPred_eq, apply_ite,
    ofReal_zero, mul_zero, ← Finset.sum_mul, horth, eq_comm (a := a),
    ite_mul, zero_mul, ↓reduceIte, ite_self]

/-- We can express `ArithmeticFunction.vonMangoldt.residueClass` as a linear combination
of twists of the von Mangoldt function by Dirichlet characters. -/
lemma residueClass_eq (ha : IsUnit a) :
    ↗(residueClass a) = Checked.inv (q.totient : ℂ) (by exact isUnit_totient_cast q) •
      ∑ χ : DirichletCharacter ℂ q, χ (Checked.inv a ha) • (fun n : ℕ ↦ χ n * vonMangoldt n) := by
  ext1 n
  simpa only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, ← mul_assoc]
    using residueClass_apply ha n

/-- The L-series of the von Mangoldt function restricted to the residue class `a` mod `q`
with `a` invertible in `ZMod q` is a linear combination of logarithmic derivatives of
L-functions of the Dirichlet characters mod `q` (on `re s > 1`). -/
lemma LSeries_residueClass_eq (ha : IsUnit a) {s : ℂ} (hs : 1 < s.re) :
    LSeries ↗(residueClass a) s =
      Checked.inv (q.totient : ℂ) (by exact isUnit_totient_cast q) *
        ∑ χ : DirichletCharacter ℂ q, χ (Checked.inv a ha) * Checked.div
          (-deriv (LFunctionOn χ) ⟨s, Or.inr (by exact ne_one_of_one_lt_real_part hs)⟩ Subtype.val)
          (LFunction χ s (hs := Or.inr (by exact ne_one_of_one_lt_real_part hs)))
          (LFunction_ne_zero_of_one_le_re χ (Or.inr (by exact ne_one_of_one_lt_real_part hs))
            hs.le).isUnit := by
  have hs' := ne_one_of_one_lt_real_part hs
  have hχ (χ : DirichletCharacter ℂ q) :
      Checked.div (-deriv (LFunctionOn χ) ⟨s, Or.inr hs'⟩ Subtype.val)
        (LFunction χ s (hs := Or.inr hs'))
        (LFunction_ne_zero_of_one_le_re χ (Or.inr hs') hs.le).isUnit =
      LSeries (fun n ↦ χ n * vonMangoldt n) s := by
    apply (div_eq_iff).mpr
    rw [deriv_LFunction_eq_deriv_LSeries χ hs, LFunction_eq_LSeries χ hs]
    exact (eq_div_iff.mp (LSeries_twist_vonMangoldt_eq χ hs)).symm
  rw [residueClass_eq ha, LSeries_smul,
    LSeries_sum (f := fun χ : DirichletCharacter ℂ q ↦
      χ (Checked.inv a ha) • (fun n : ℕ ↦ χ n * vonMangoldt n))
      (fun χ _ ↦ (LSeriesSummable_twist_vonMangoldt χ hs).smul (χ (Checked.inv a ha)))]
  simp only [LSeries_smul, hχ]

variable (a)

/-- The points where the entire normalization of the trivial L-function and all nontrivial
Dirichlet L-functions modulo `q` are nonzero. -/
abbrev LFunctionResidueClassAuxDomain (q : ℕ) [NeZero q] : Set ℂ :=
  {s | IsUnit (LFunctionTrivChar₁ q s) ∧
    ∀ (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1), IsUnit (LFunction χ s (hs := Or.inl hχ))}

open scoped Classical in
/-- The auxiliary function used, e.g., with the Wiener-Ikehara Theorem to prove
Dirichlet's Theorem. On `re s > 1`, it agrees with the L-series of the von Mangoldt
function restricted to the residue class `a : ZMod q` minus the principal part
`(q.totient)⁻¹/(s-1)` of the pole at `s = 1`;
see `ArithmeticFunction.vonMangoldt.eqOn_LFunctionResidueClassAux`. -/
noncomputable
abbrev LFunctionResidueClassAux (ha : IsUnit a) (s : ℂ)
    (hs : s ∈ LFunctionResidueClassAuxDomain q) : ℂ :=
  Checked.inv (q.totient : ℂ) (by exact isUnit_totient_cast q) *
    (Checked.div (-deriv (LFunctionTrivChar₁ q) s) (LFunctionTrivChar₁ q s) hs.1 +
      ∑ χ : {χ : DirichletCharacter ℂ q // χ ≠ 1}, χ.val (Checked.inv a ha) * Checked.div
        (-deriv (fun z ↦ LFunction χ.val z (hs := Or.inl χ.2)) s)
        (LFunction χ.val s (hs := Or.inl χ.2)) (hs.2 χ.val χ.2))

/-- The auxiliary function is continuous away from the zeros of the L-functions of the Dirichlet
characters mod `q` (including at `s = 1`). -/
lemma continuousOn_LFunctionResidueClassAux' (ha : IsUnit a) :
    Continuous
      (fun s : LFunctionResidueClassAuxDomain q ↦ LFunctionResidueClassAux a ha s s.2) := by
  classical
  let D := LFunctionResidueClassAuxDomain q
  let φ : D → {s : ℂ // IsUnit (LFunctionTrivChar₁ q s)} := fun s ↦ ⟨s, s.2.1⟩
  have hφ : Continuous φ := continuous_subtype_val.subtype_mk _
  refine continuous_const.mul ((continuousOn_neg_logDeriv_LFunctionTrivChar₁ q).comp hφ |>.add ?_)
  refine continuous_finsetSum _ fun χ _ ↦ continuous_const.mul ?_
  let ψ : D → {s : ℂ // IsUnit (LFunction χ.val s (hs := Or.inl χ.2))} :=
    fun s ↦ ⟨s, s.2.2 χ.val χ.2⟩
  have hψ : Continuous ψ := continuous_subtype_val.subtype_mk _
  exact (continuousOn_neg_logDeriv_LFunction_of_nontriv χ.2).comp hψ

lemma mem_LFunctionResidueClassAuxDomain_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) :
    s ∈ LFunctionResidueClassAuxDomain q := by
  refine ⟨?_, fun χ hχ ↦ (LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hs).isUnit⟩
  rcases eq_or_ne s 1 with rfl | hs₁
  · exact (LFunctionTrivChar₁_apply_one_ne_zero q).isUnit
  · rw [LFunctionTrivChar₁, LFunction₁_eq_mul _ hs₁]
    exact (sub_ne_zero.mpr hs₁).isUnit.mul
      (LFunction_ne_zero_of_one_le_re _ (Or.inr hs₁) hs).isUnit

/-- The L-series of the von Mangoldt function restricted to the prime residue class `a` mod `q`
is continuous on `re s ≥ 1` except for a simple pole at `s = 1` with residue `(q.totient)⁻¹`.
The statement as given here in terms of `ArithmeticFunction.vonMangoldt.LFunctionResidueClassAux`
is equivalent. -/
lemma continuousOn_LFunctionResidueClassAux (ha : IsUnit a) :
    Continuous (fun s : {z : ℂ // 1 ≤ z.re} ↦ LFunctionResidueClassAux a ha s
      (mem_LFunctionResidueClassAuxDomain_of_one_le_re s.2)) := by
  exact (continuousOn_LFunctionResidueClassAux' a ha).comp
    (continuous_subtype_val.subtype_mk fun s : {z : ℂ // 1 ≤ z.re} ↦
      mem_LFunctionResidueClassAuxDomain_of_one_le_re s.2)

variable {a}

open scoped LSeries.notation

/-- The auxiliary function agrees on `re s > 1` with the L-series of the von Mangoldt function
restricted to the residue class `a : ZMod q` minus the principal part `(q.totient)⁻¹/(s-1)`
of its pole at `s = 1`. -/
lemma eqOn_LFunctionResidueClassAux (ha : IsUnit a) :
    ∀ {s : ℂ} (hs : 1 < s.re),
      LFunctionResidueClassAux a ha s (mem_LFunctionResidueClassAuxDomain_of_one_le_re hs.le) =
        L ↗(residueClass a) s - Checked.div
          (Checked.inv (q.totient : ℂ) (by exact isUnit_totient_cast q)) (s - 1)
          (sub_ne_zero.mpr (by exact ne_one_of_one_lt_real_part hs)).isUnit := by
  classical
  intro s hs
  have hs₁ := ne_one_of_one_lt_real_part hs
  have hdom := mem_LFunctionResidueClassAuxDomain_of_one_le_re (q := q) hs.le
  have hsub := (sub_ne_zero.mpr hs₁).isUnit
  let Lχ (χ : DirichletCharacter ℂ q) := LFunction χ s (hs := Or.inr hs₁)
  let dχ (χ : DirichletCharacter ℂ q) := deriv (LFunctionOn χ) ⟨s, Or.inr hs₁⟩ Subtype.val
  let Q (χ : DirichletCharacter ℂ q) := Checked.div (-dχ χ) (Lχ χ)
    (LFunction_ne_zero_of_one_le_re χ (Or.inr hs₁) hs.le).isUnit
  let g (χ : DirichletCharacter ℂ q) := χ (Checked.inv a ha) * Q χ
  let c := Checked.inv (q.totient : ℂ) (isUnit_totient_cast q)
  have ha' : IsUnit (Checked.inv a ha) := ha.inv₀
  have hsplit : (∑ χ, g χ) = Q 1 + ∑ χ : {χ : DirichletCharacter ℂ q // χ ≠ 1}, g χ.val := by
    rw [Fintype.sum_eq_add_sum_compl 1,
      Finset.sum_subtype (p := fun χ : DirichletCharacter ℂ q ↦ χ ≠ 1)
        (F := inferInstance) _ (by simp) g]
    simp only [g, MulChar.one_apply ha', one_mul]
  have hseries : L ↗(residueClass a) s = c * ∑ χ, g χ := LSeries_residueClass_eq ha hs
  have hnormal : Checked.div (-deriv (LFunctionTrivChar₁ q) s) (LFunctionTrivChar₁ q s) hdom.1 =
      Q 1 - 1 / (s - 1) := by
    have hL : IsUnit (Lχ 1) := (LFunction_ne_zero_of_one_le_re _ (Or.inr hs₁) hs.le).isUnit
    apply (div_eq_iff).mpr
    rw [deriv_LFunctionTrivChar₁_apply_of_ne_one _ hs₁, LFunctionTrivChar₁, LFunction₁_eq_mul _ hs₁]
    change -((s - 1) * dχ 1 + Lχ 1) = (Q 1 - 1 / (s - 1)) * ((s - 1) * Lχ 1)
    dsimp only [Q]
    field
  have hQ (χ : {χ : DirichletCharacter ℂ q // χ ≠ 1}) :
      Checked.div (-deriv (fun z ↦ LFunction χ.val z (hs := Or.inl χ.2)) s)
        (LFunction χ.val s (hs := Or.inl χ.2)) (hdom.2 χ.val χ.2) = Q χ.val := by
    simp only [Q, dχ, Lχ, deriv_LFunctionOn_eq_deriv_of_ne_one χ.2]
  rw [hseries, hsplit]
  simp only [LFunctionResidueClassAux, hnormal, hQ, c, g, mul_add, mul_sub, mul_one_div₀]
  ring

private lemma LSeries_ofReal_rpow (f : ℕ → ℝ) (x : ℝ) :
    LSeries (f ·) x = ↑(∑' n : ℕ+, Checked.div (f n) ((n : ℝ) ^ x)
      (Real.rpow_ne_zero_of_pos (Nat.cast_pos.mpr n.pos) x).isUnit) := by
  rw [LSeries_def, ofReal_tsum]
  refine tsum_congr fun n ↦ ?_
  symm
  apply (eq_div_iff).mpr
  have hpow : (((n : ℝ) ^ x : ℝ) : ℂ) = ((n : ℕ) : ℂ) ^ (x : ℂ) := by
    rw [ofReal_cpow (Nat.cast_nonneg (n : ℕ)), ofReal_natCast]
  rw [← hpow, ← ofReal_mul, div_mul_cancel₀]

private lemma ofReal_totient_div_sub_one {x : ℝ} (hx : 1 < x) :
    (↑(Checked.div (Checked.inv (q.totient : ℝ) (isUnit_totient_cast q))
      (x - 1) (sub_pos.mpr hx).ne'.isUnit) : ℂ) =
      Checked.div (Checked.inv (q.totient : ℂ) (isUnit_totient_cast q)) ((x : ℂ) - 1) (by
        exact (sub_ne_zero.mpr (ne_one_of_one_lt_real_part
          (by simpa only [ofReal_re] using hx))).isUnit) := by
  apply (eq_div_iff).mpr
  rw [← ofReal_one, ← ofReal_sub, ← ofReal_mul, div_mul_cancel₀, ofReal_inv]
  have hinv (b : ℂ) (hb : IsUnit b) (h : b = (q.totient : ℂ)) :
      Checked.inv b hb = Checked.inv (q.totient : ℂ) (isUnit_totient_cast q) := by
    subst b
    rfl
  exact hinv _ _ (ofReal_natCast q.totient)

/-- The auxiliary function takes real values for real arguments `x > 1`. -/
lemma LFunctionResidueClassAux_real (ha : IsUnit a) {x : ℝ} (hx : 1 < x) :
    LFunctionResidueClassAux a ha (x : ℂ)
      (mem_LFunctionResidueClassAuxDomain_of_one_le_re (by simpa only [ofReal_re] using hx.le)) =
      (LFunctionResidueClassAux a ha (x : ℂ)
        (mem_LFunctionResidueClassAuxDomain_of_one_le_re
          (by simpa only [ofReal_re] using hx.le))).re := by
  have hx' : 1 < (x : ℂ).re := by simpa only [ofReal_re] using hx
  rw [eqOn_LFunctionResidueClassAux ha hx', LSeries_ofReal_rpow,
    ← ofReal_totient_div_sub_one (q := q) hx, ← ofReal_sub, ofReal_re]

variable {q : ℕ} [NeZero q] {a : ZMod q}

/-- As `x` approaches `1` from the right along the real axis, the L-series of
`ArithmeticFunction.vonMangoldt.residueClass` is bounded below by `(q.totient)⁻¹/(x-1) - C`. -/
lemma LSeries_residueClass_lower_bound (ha : IsUnit a) :
    ∃ C : ℝ, ∀ {x : ℝ} (hx : x ∈ Set.Ioc 1 2),
      Checked.div (Checked.inv (q.totient : ℝ) (by exact isUnit_totient_cast q))
        (x - 1) (sub_pos.mpr hx.1).ne'.isUnit - C ≤
        ∑' n : ℕ+, Checked.div (residueClass a n) ((n : ℝ) ^ x)
          (Real.rpow_ne_zero_of_pos (Nat.cast_pos.mpr n.pos) x).isUnit := by
  have H {x : ℝ} (hx : 1 < x) :
      (∑' n : ℕ+, Checked.div (residueClass a n) ((n : ℝ) ^ x)
        (Real.rpow_ne_zero_of_pos (Nat.cast_pos.mpr n.pos) x).isUnit) =
        (LFunctionResidueClassAux a ha (x : ℂ)
           (mem_LFunctionResidueClassAuxDomain_of_one_le_re
             (by simpa only [ofReal_re] using hx.le))).re +
          Checked.div (Checked.inv (q.totient : ℝ) (isUnit_totient_cast q))
            (x - 1) (sub_pos.mpr hx).ne'.isUnit := by
    have hx' : 1 < (x : ℂ).re := by simpa only [ofReal_re] using hx
    refine ofReal_injective ?_
    rw [← LSeries_ofReal_rpow, ofReal_add, ← LFunctionResidueClassAux_real ha hx,
      ofReal_totient_div_sub_one (q := q) hx, eqOn_LFunctionResidueClassAux ha hx', sub_add_cancel]
  let D := Set.Icc (1 : ℝ) 2
  let φ (x : D) : {z : ℂ // 1 ≤ z.re} := ⟨(x : ℝ), by simpa only [ofReal_re] using x.2.1⟩
  have hφ : Continuous φ := (continuous_ofReal.comp continuous_subtype_val).subtype_mk _
  let f (x : D) : ℝ :=
    (LFunctionResidueClassAux a ha (φ x)
      (mem_LFunctionResidueClassAuxDomain_of_one_le_re (φ x).2)).re
  have hf : Continuous f :=
    continuous_re.comp ((continuousOn_LFunctionResidueClassAux a ha).comp hφ)
  have : CompactSpace D := isCompact_iff_compactSpace.mp isCompact_Icc
  obtain ⟨C, hC⟩ := bddBelow_def.mp (isCompact_range hf).bddBelow
  refine ⟨-C, fun {x} hx ↦ ?_⟩
  rw [H hx.1, add_comm, sub_neg_eq_add, add_le_add_iff_left]
  exact hC _ ⟨⟨x, Set.mem_Icc_of_Ioc hx⟩, rfl⟩

open vonMangoldt Filter Topology in
/-- The function `n ↦ Λ n / n` restricted to primes in an invertible residue class
is not summable. This then implies that there must be infinitely many such primes. -/
lemma not_summable_residueClass_prime_div (ha : IsUnit a) :
    ¬ Summable fun n : ℕ+ ↦ (if Nat.Prime (n : ℕ) then residueClass a n else 0) / (n : ℝ) := by
  intro H
  have key : Summable fun n : ℕ+ ↦ residueClass a n / (n : ℝ) := by
    convert! (summable_residueClass_non_primes_div a).add H using 2 with n
    simp only [← add_div, ite_add_ite, zero_add, add_zero, ite_self]
  let C := ∑' n : ℕ+, residueClass a n / (n : ℝ)
  have H₁ {x : ℝ} (hx : 1 < x) :
      (∑' n : ℕ+, Checked.div (residueClass a n) ((n : ℝ) ^ x)
        (Real.rpow_ne_zero_of_pos (Nat.cast_pos.mpr n.pos) x).isUnit) ≤ C := by
    refine Summable.tsum_le_tsum (fun n ↦ ?_) ?_ key
    · refine div_le_div_of_nonneg_left (residueClass_nonneg a _) (Nat.cast_pos.mpr n.pos) ?_
      calc
        (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast n.pos) hx.le
    · exact summable_real_of_abscissaOfAbsConv_lt <|
        (abscissaOfAbsConv_residueClass_le_one a).trans_lt <| mod_cast hx
  obtain ⟨C', hC'⟩ := LSeries_residueClass_lower_bound ha
  have H₁ {x} (hx : x ∈ Set.Ioc 1 2) : (q.totient : ℝ)⁻¹ ≤ (C + C') * (x - 1) :=
    (div_le_iff₀ <| sub_pos.mpr hx.1).mp <|
      sub_le_iff_le_add.mp <| (hC' hx).trans (H₁ hx.1)
  have hq : 0 < (q.totient : ℝ)⁻¹ := inv_pos.mpr (mod_cast q.totient.pos_of_neZero)
  rcases le_or_gt (C + C') 0 with h₀ | h₀
  · have := hq.trans_le (H₁ (Set.right_mem_Ioc.mpr one_lt_two))
    rw [show (2 : ℝ) - 1 = 1 by norm_num, mul_one] at this
    exact (this.trans_le h₀).false
  · obtain ⟨ξ, hξ₁, hξ₂⟩ : ∃ ξ ∈ Set.Ioc 1 2, (C + C') * (ξ - 1) < (q.totient : ℝ)⁻¹ := by
      refine ⟨min (1 + (q.totient : ℝ)⁻¹ / (C + C') / 2) 2, ⟨?_, min_le_right ..⟩, ?_⟩
      · simpa only [lt_inf_iff, lt_add_iff_pos_right, Nat.ofNat_pos, div_pos_iff_of_pos_right,
          Nat.one_lt_ofNat, and_true] using div_pos hq h₀
      · rw [← min_sub_sub_right, add_sub_cancel_left, ← lt_div_iff₀' h₀]
        exact (min_le_left ..).trans_lt <| div_lt_self (div_pos hq h₀) one_lt_two
    exact ((H₁ hξ₁).trans_lt hξ₂).false

end ArithmeticFunction.vonMangoldt

end arith_prog

/-!
### Dirichlet's Theorem
-/

section DirichletsTheorem

namespace Nat

open ArithmeticFunction vonMangoldt

variable {q : ℕ} [NeZero q] {a : ZMod q}

/-- **Dirichlet's Theorem** on primes in arithmetic progression: if `q` is a positive
integer and `a : ZMod q` is a unit, then there are infinitely many prime numbers `p`
such that `(p : ZMod q) = a`. -/
theorem infinite_setOfPred_prime_and_eq_mod (ha : IsUnit a) :
    {p : ℕ | p.Prime ∧ (p : ZMod q) = a}.Infinite := by
  by_contra! H
  have hfinite : (Function.support (fun n : ℕ ↦ if hn : n.Prime then
    Checked.div (residueClass a n) (n : ℝ) (Nat.cast_ne_zero.mpr hn.ne_zero).isUnit
    else 0)).Finite :=
    support_residueClass_prime_div a ▸ H
  apply not_summable_residueClass_prime_div ha
  refine ((summable_of_hasFiniteSupport hfinite).comp_injective PNat.coe_injective).congr
    fun n ↦ ?_
  by_cases hn : Nat.Prime (n : ℕ) <;> simp [Function.comp_apply, hn]

@[deprecated (since := "2026-07-09")]
alias infinite_setOf_prime_and_eq_mod := infinite_setOfPred_prime_and_eq_mod

/-- **Dirichlet's Theorem** on primes in arithmetic progression: if `q` is a positive
integer and `a : ZMod q` is a unit, then there are infinitely many prime numbers `p`
such that `(p : ZMod q) = a`. -/
theorem forall_exists_prime_gt_and_eq_mod (ha : IsUnit a) (n : ℕ) :
    ∃ p > n, p.Prime ∧ (p : ZMod q) = a := by
  obtain ⟨p, hp₁, hp₂⟩ := Set.infinite_iff_exists_gt.mp (infinite_setOfPred_prime_and_eq_mod ha) n
  exact ⟨p, hp₂.gt, Set.mem_ofPred.mp hp₁⟩

/-- **Dirichlet's Theorem** on primes in arithmetic progression: if `q` is a positive
integer and `a : ℤ` is coprime to `q`, then there are infinitely many prime numbers `p`
such that `p ≡ a mod q`. -/
theorem forall_exists_prime_gt_and_zmodEq (n : ℕ) {q : ℕ} {a : ℤ} (hq : q ≠ 0) (h : IsCoprime a q) :
    ∃ p > n, p.Prime ∧ p ≡ a [ZMOD q] := by
  have : NeZero q := ⟨hq⟩
  have : IsUnit (a : ZMod q) := by
    rwa [ZMod.coe_int_isUnit_iff_isCoprime, isCoprime_comm]
  obtain ⟨p, hpn, hpp, heq⟩ := forall_exists_prime_gt_and_eq_mod this n
  refine ⟨p, hpn, hpp, ?_⟩
  simpa [← ZMod.intCast_eq_intCast_iff] using heq

/-- **Dirichlet's Theorem** on primes in arithmetic progression: if `q` is a positive
integer and `a : ℕ` is coprime to `q`, then there are infinitely many prime numbers `p`
such that `p ≡ a mod q`. -/
theorem forall_exists_prime_gt_and_modEq (n : ℕ) {q a : ℕ} (hq : q ≠ 0) (h : a.Coprime q) :
    ∃ p > n, p.Prime ∧ p ≡ a [MOD q] := by
  simpa using forall_exists_prime_gt_and_zmodEq n (q := q) (a := a) hq (by simpa)

open Filter in
lemma frequently_atTop_prime_and_modEq {q a : ℕ} (hq : q ≠ 0) (h : a.Coprime q) :
    ∃ᶠ p in atTop, p.Prime ∧ p ≡ a [MOD q] := by
  rw [frequently_atTop]
  intro n
  obtain ⟨p, hn, hp, ha⟩ := forall_exists_prime_gt_and_modEq n hq h
  exact ⟨p, hn.le, hp, ha⟩

lemma infinite_setOfPred_prime_and_modEq {q a : ℕ} (hq : q ≠ 0) (h : a.Coprime q) :
    Set.Infinite {p : ℕ | p.Prime ∧ p ≡ a [MOD q]} :=
  frequently_atTop_iff_infinite.1 (frequently_atTop_prime_and_modEq hq h)

@[deprecated (since := "2026-07-09")]
alias infinite_setOf_prime_and_modEq := infinite_setOfPred_prime_and_modEq

end Nat

end DirichletsTheorem
