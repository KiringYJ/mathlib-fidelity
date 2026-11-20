/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler, Michael Stoll
-/
module

public import Mathlib.NumberTheory.LSeries.ZMod
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

/-!
# Analytic continuation of Dirichlet L-functions

We show that if `χ` is a Dirichlet character `ZMod N → ℂ`, for a positive integer `N`, then the
L-series of `χ` has analytic continuation (away from a pole at `s = 1` if `χ` is trivial), and
similarly for completed L-functions.

All definitions and theorems are in the `DirichletCharacter` namespace.

## Main definitions

* `LFunction χ s`: the L-function, defined as a linear combination of Hurwitz zeta functions.
* `completedLFunction χ s`: the completed L-function, which for *almost* all `s` is equal to
  `LFunction χ s * gammaFactor χ s` where `gammaFactor χ s` is the archimedean Gamma-factor.
* `rootNumber χ hχ`: the global root number of the L-series of `χ`, where `hχ` proves that `χ` is
  primitive.

## Main theorems

* `LFunction_eq_LSeries`: if `1 < re s` then the `LFunction` coincides with the naive `LSeries`.
* `differentiable_LFunction`: if `χ` is nontrivial then `LFunction χ s` is differentiable
  everywhere.
* `LFunction_eq_completed_mul_reciprocalGammaFactor`: on the regular domain of the completion,
  `LFunction χ s = completedLFunction χ s * reciprocalGammaFactor χ s`.
* `differentiable_completedLFunction`: if `χ` is nontrivial then `completedLFunction χ s` is
  differentiable everywhere.
* `IsPrimitive.completedLFunction_one_sub`: the **functional equation** for Dirichlet L-functions,
  showing that if `χ` is primitive modulo `N`, with proof `hχ`, then
  `completedLFunction χ (1 - s) =
    N ^ (s - 1 / 2) * rootNumber χ hχ * completedLFunction χ⁻¹ s`.
-/

@[expose] public section

open Complex Finset ZMod Filter

open scoped Real Topology

namespace DirichletCharacter

variable {N : ℕ} [NeZero N]

/-- The Dirichlet L-function on its regular domain. It has a pole at one exactly for the
trivial character. In the half-plane of absolute convergence it agrees with the Dirichlet
series. -/
@[pp_nodot]
noncomputable def LFunction (χ : DirichletCharacter ℂ N) (s : ℂ)
    (hs : χ ≠ 1 ∨ s ≠ 1 := by
      first | assumption | exact Or.inl (by assumption) | exact Or.inr (by checked_nonzero)) : ℂ :=
  ZMod.LFunction χ s (hs.elim (fun hχ ↦ Or.inr (χ.sum_eq_zero_of_ne_one hχ)) Or.inl)

/-- Regular points of the Dirichlet L-function. -/
abbrev LFunctionDomain (χ : DirichletCharacter ℂ N) : Set ℂ := {s | χ ≠ 1 ∨ s ≠ 1}

/-- The Dirichlet L-function as an ordinary function of a regular point. -/
noncomputable abbrev LFunctionOn (χ : DirichletCharacter ℂ N) (s : LFunctionDomain χ) : ℂ :=
  LFunction χ s (hs := s.2)

omit [NeZero N] in
lemma isOpen_LFunctionDomain (χ : DirichletCharacter ℂ N) : IsOpen (LFunctionDomain χ) := by
  by_cases hχ : χ ≠ 1
  · simp [LFunctionDomain, hχ]
  · simp only [LFunctionDomain, hχ, false_or]
    exact isOpen_compl_singleton

private lemma ne_one_of_one_lt_real_part {s : ℂ} (hs : 1 < s.re) : s ≠ 1 := by
  rintro rfl
  simp at hs

/--
The L-function of the (unique) Dirichlet character mod 1 is the Riemann zeta function.
(Compare `DirichletCharacter.LSeries_modOne_eq`.)
-/
@[simp] lemma LFunction_modOne_eq {χ : DirichletCharacter ℂ 1} {s : ℂ} (hs : s ≠ 1) :
    LFunction χ s (hs := Or.inr hs) = riemannZeta s (hs := hs) := by
  change ZMod.LFunction χ s (Or.inl hs) = _
  have hχ : χ (0 : ZMod 1) = 1 := by rw [show (0 : ZMod 1) = 1 from rfl, map_one]
  rw [ZMod.LFunction_modOne_eq χ s hs, hχ, one_mul]

/--
For `1 < re s` the L-function of a Dirichlet character agrees with the sum of the naive Dirichlet
series.
-/
lemma LFunction_eq_LSeries (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < re s) :
    LFunction χ s (hs := Or.inr (by exact ne_one_of_one_lt_real_part hs)) = LSeries (χ ·) s :=
  ZMod.LFunction_eq_LSeries χ hs

private lemma hasDerivAt_subtype_val {U : Set ℂ} {f : ℂ → ℂ} {d : ℂ} {x : U}
    (h : HasDerivAt f d (x : ℂ)) : HasDerivAt (fun z : U ↦ f z) d x Subtype.val :=
  hasDerivAt_iff_hasFDerivAt.mpr <|
    h.hasFDerivAt.comp_tendsto Subtype.val
      ((continuous_subtype_val.tendsto x).prodMap (tendsto_pure_pure Subtype.val x))

lemma deriv_LFunction_eq_deriv_LSeries (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    deriv (LFunctionOn χ) ⟨s, Or.inr (by exact ne_one_of_one_lt_real_part hs)⟩ Subtype.val =
      deriv (LSeries (χ ·)) s := by
  let x : LFunctionDomain χ := ⟨s, Or.inr (ne_one_of_one_lt_real_part hs)⟩
  have hAbs : LSeries.abscissaOfAbsConv (χ ·) ≤ 1 := by
    refine LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy ↦ ?_
    exact ZMod.LSeriesSummable_of_one_lt_re χ (by simpa only [ofReal_re] using hy)
  have hd := (LSeries_hasDerivAt (f := (χ ·)) (s := s)
    (hAbs.trans_lt (by exact_mod_cast hs))).differentiableAt.hasDerivAt
  have hsub : HasDerivAt (fun z : LFunctionDomain χ ↦ LSeries (χ ·) z)
      (deriv (LSeries (χ ·)) s) x Subtype.val := hasDerivAt_subtype_val hd
  have heq : (fun z : LFunctionDomain χ ↦ LSeries (χ ·) z) =ᶠ[𝓝 x] LFunctionOn χ := by
    filter_upwards [((continuous_re.comp continuous_subtype_val).tendsto x).eventually
      (eventually_gt_nhds hs)] with z hz
    exact (LFunction_eq_LSeries χ hz).symm
  have hd' : HasDerivAt (LFunctionOn χ) (deriv (LSeries (χ ·)) s) x Subtype.val := by
    refine hasDerivAt_iff_hasFDerivAt.mpr <| HasFDerivAt.of_isLittleO ?_
    refine hsub.hasFDerivAt.isLittleO.congr' ?_ EventuallyEq.rfl
    filter_upwards [heq] with z hz
    rw [hz, heq.eq_of_nhds]
  exact hd'.deriv (isOpen_LFunctionDomain χ).isOpenEmbedding_subtypeVal

/--
The L-function of a Dirichlet character is differentiable, except at `s = 1` if the character is
trivial.
-/
@[fun_prop]
lemma differentiableAt_LFunction (χ : DirichletCharacter ℂ N) (s : ℂ) (hs : s ≠ 1 ∨ χ ≠ 1) :
    DifferentiableAt ℂ (LFunctionOn χ) ⟨s, hs.symm⟩ Subtype.val := by
  let φ : LFunctionDomain χ → {z : ℂ // z ≠ 1 ∨ ∑ j, χ j = 0} :=
    fun z ↦ ⟨z.val, z.2.symm.imp_right χ.sum_eq_zero_of_ne_one⟩
  have hφ : Continuous φ := continuous_subtype_val.subtype_mk _
  obtain ⟨d, hd⟩ := ZMod.differentiableAt_LFunction χ s (hs.imp_right χ.sum_eq_zero_of_ne_one)
  exact ⟨d, HasFDerivAtFilter.comp_tendsto hd φ
    ((hφ.tendsto ⟨s, hs.symm⟩).prodMap (tendsto_pure_pure ..))⟩

/-- The L-function of a non-trivial Dirichlet character is differentiable everywhere. -/
@[fun_prop]
lemma differentiable_LFunction {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    Differentiable ℂ (fun s ↦ LFunction χ s (hs := Or.inl hχ)) :=
  ZMod.differentiable_LFunction_of_sum_zero (χ.sum_eq_zero_of_ne_one hχ)

lemma deriv_LFunctionOn_eq_deriv_of_ne_one {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (s : LFunctionDomain χ) :
    deriv (LFunctionOn χ) s Subtype.val =
      deriv (fun z ↦ LFunction χ z (hs := Or.inl hχ)) s := by
  have hd := (differentiable_LFunction hχ (s : ℂ)).hasDerivAt
  have hsub : HasDerivAt (LFunctionOn χ)
      (deriv (fun z ↦ LFunction χ z (hs := Or.inl hχ)) s) s Subtype.val := hasDerivAt_subtype_val hd
  exact hsub.deriv (isOpen_LFunctionDomain χ).isOpenEmbedding_subtypeVal

/-- The L-function of an even Dirichlet character vanishes at strictly negative even integers. -/
@[simp]
lemma Even.LFunction_neg_two_mul_nat_add_one {χ : DirichletCharacter ℂ N} (hχ : Even χ) (n : ℕ) :
    LFunction χ (-(2 * (n + 1))) (Or.inr (by
      exact_mod_cast (show -(2 * (n + 1) : ℤ) ≠ 1 by omega))) = 0 :=
  ZMod.LFunction_neg_two_mul_nat_add_one hχ.to_fun n

/-- The L-function of an even Dirichlet character vanishes at strictly negative even integers. -/
@[simp]
lemma Even.LFunction_neg_two_mul_nat {χ : DirichletCharacter ℂ N} (hχ : Even χ) (n : ℕ) [NeZero n] :
    LFunction χ (-(2 * n)) (Or.inr (by
      exact_mod_cast (show -(2 * n : ℤ) ≠ 1 by omega))) = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  exact_mod_cast hχ.LFunction_neg_two_mul_nat_add_one m

/-- The L-function of an odd Dirichlet character vanishes at negative odd integers. -/
@[simp] lemma Odd.LFunction_neg_two_mul_nat_sub_one
    {χ : DirichletCharacter ℂ N} (hχ : Odd χ) (n : ℕ) :
    LFunction χ (-(2 * n) - 1) (Or.inr (by
      exact_mod_cast (show -(2 * n : ℤ) - 1 ≠ 1 by omega))) = 0 :=
  ZMod.LFunction_neg_two_mul_nat_sub_one hχ.to_fun n

/-!
### Results on changing levels
-/

/-- The entire normalization obtained by multiplying a Dirichlet L-function by `s - 1`. -/
noncomputable def LFunction₁ (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  (s - 1) * ZMod.LFunctionRegularPart χ s +
    N ^ (-s) * (∑ j, χ j) * reciprocalGammaℝ s

lemma differentiable_LFunction₁ (χ : DirichletCharacter ℂ N) : Differentiable ℂ (LFunction₁ χ) := by
  have hn : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hp : Differentiable ℂ (fun s : ℂ ↦ (N : ℂ) ^ (-s)) :=
    differentiable_id.neg.const_cpow (Or.inl hn)
  have hR := ZMod.differentiable_LFunctionRegularPart (χ : ZMod N → ℂ)
  exact ((differentiable_id.sub_const 1).mul hR).add
    ((hp.mul_const _).mul differentiable_reciprocalGammaℝ)

lemma LFunction₁_eq_mul (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : s ≠ 1) :
    LFunction₁ χ s = (s - 1) * LFunction χ s (hs := Or.inr hs) := by
  have hs' : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  unfold LFunction₁ LFunction ZMod.LFunction
  split_ifs with hχ
  · simp [hχ]
  · field

private lemma LFunction₁_changeLevel {M N : ℕ} [NeZero M] [NeZero N] (hMN : M ∣ N)
    (χ : DirichletCharacter ℂ M) :
    LFunction₁ (changeLevel hMN χ) = fun s ↦
      LFunction₁ χ s * ∏ p ∈ N.primeFactors, (1 - χ p * p ^ (-s)) := by
  have hprod : Differentiable ℂ (fun s : ℂ ↦ ∏ p ∈ N.primeFactors, (1 - χ p * p ^ (-s))) := by
    refine .fun_finsetProd fun p hp ↦ ?_
    have : NeZero p := ⟨(Nat.prime_of_mem_primeFactors hp).ne_zero⟩
    fun_prop
  have hf := (differentiable_LFunction₁ (changeLevel hMN χ)).differentiableOn.analyticOnNhd
    isOpen_univ
  have hg := ((differentiable_LFunction₁ χ).mul hprod).differentiableOn.analyticOnNhd isOpen_univ
  refine AnalyticOnNhd.eq_of_frequently_eq (z₀ := (2 : ℂ)) hf hg ?_
  have h : {z : ℂ | 1 < z.re} ∈ 𝓝[≠] (2 : ℂ) := nhdsWithin_le_nhds
    ((isOpen_lt continuous_const continuous_re).mem_nhds (by simp : 1 < (2 : ℂ).re))
  apply (eventually_of_mem h fun z hz ↦ ?_).frequently
  have hz' : 1 < z.re := hz
  have hz1 := ne_one_of_one_lt_real_part hz'
  rw [LFunction₁_eq_mul _ hz1, LFunction₁_eq_mul _ hz1, LFunction_eq_LSeries _ hz',
    LFunction_eq_LSeries _ hz', LSeries_changeLevel hMN χ hz', mul_assoc]

private lemma LFunction_changeLevel_aux {M N : ℕ} [NeZero M] [NeZero N] (hMN : M ∣ N)
    (χ : DirichletCharacter ℂ M) {s : ℂ} (hs : s ≠ 1) :
    LFunction (changeLevel hMN χ) s (hs := Or.inr hs) =
      LFunction χ s (hs := Or.inr hs) * ∏ p ∈ N.primeFactors, (1 - χ p * p ^ (-s)) := by
  have h := congrFun (LFunction₁_changeLevel hMN χ) s
  apply mul_left_cancel₀ (sub_ne_zero.mpr hs)
  simpa only [LFunction₁_eq_mul _ hs, mul_assoc] using h

/-- If `χ` is a Dirichlet character and its level `M` divides `N`, then we obtain the L function
of `χ` considered as a Dirichlet character of level `N` from the L function of `χ` by multiplying
with `∏ p ∈ N.primeFactors, (1 - χ p * p ^ (-s))`.
(Note that `1 - χ p * p ^ (-s) = 1` when `p` divides `M`). -/
lemma LFunction_changeLevel {M N : ℕ} [NeZero M] [NeZero N] (hMN : M ∣ N)
    (χ : DirichletCharacter ℂ M) {s : ℂ} (h : χ ≠ 1 ∨ s ≠ 1) :
    LFunction (changeLevel hMN χ) s (hs := h.imp_left
      fun hχ ↦ hχ ∘ (changeLevel_eq_one_iff hMN).mp) =
      LFunction χ s (hs := h) * ∏ p ∈ N.primeFactors, (1 - χ p * p ^ (-s)) := by
  rcases h with h | h
  · have hχ : changeLevel hMN χ ≠ 1 := h ∘ (changeLevel_eq_one_iff hMN).mp
    have h' : Continuous fun s ↦
        LFunction χ s (hs := Or.inl h) * ∏ p ∈ N.primeFactors, (1 - χ p * ↑p ^ (-s)) :=
      (differentiable_LFunction h).continuous.mul <| continuous_finsetProd _ fun p hp ↦ by
        have : NeZero p := ⟨(Nat.prime_of_mem_primeFactors hp).ne_zero⟩
        fun_prop
    exact congrFun ((differentiable_LFunction hχ).continuous.ext_on
      (dense_compl_singleton 1) h' (fun _ h ↦ LFunction_changeLevel_aux hMN χ h)) s
  · exact LFunction_changeLevel_aux hMN χ h

/-!
### The `L`-function of the trivial character mod `N`
-/

/-- The `L`-function of the trivial character mod `N`. -/
noncomputable abbrev LFunctionTrivChar (N : ℕ) [NeZero N] (s : ℂ)
    (hs : s ≠ 1 := by checked_nonzero) :=
  LFunction (1 : DirichletCharacter ℂ N) s (hs := Or.inr hs)

/-- The L function of the trivial Dirichlet character mod `N` is obtained from the Riemann
zeta function by multiplying with `∏ p ∈ N.primeFactors, (1 - (p : ℂ) ^ (-s))`. -/
lemma LFunctionTrivChar_eq_mul_riemannZeta {s : ℂ} (hs : s ≠ 1) :
    LFunctionTrivChar N s hs =
      (∏ p ∈ N.primeFactors, (1 - (p : ℂ) ^ (-s))) * riemannZeta s (hs := hs) := by
  rw [← LFunction_modOne_eq (χ := 1) hs, mul_comm]
  have h := congrArg (fun χ : DirichletCharacter ℂ N ↦ LFunction χ s (Or.inr hs))
    (changeLevel_one (R := ℂ) N.one_dvd)
  change LFunction (1 : DirichletCharacter ℂ N) s (Or.inr hs) = _
  rw [← h, LFunction_changeLevel N.one_dvd 1 (.inr hs)]
  congr 1
  exact prod_congr rfl fun p _ ↦ by rw [MulChar.one_apply (isUnit_of_subsingleton _), one_mul]

/-- The entire normalization of the trivial Dirichlet L-function. -/
noncomputable abbrev LFunctionTrivChar₁ (N : ℕ) [NeZero N] : ℂ → ℂ :=
  LFunction₁ (1 : DirichletCharacter ℂ N)

lemma LFunctionTrivChar₁_apply_one (N : ℕ) [NeZero N] :
    LFunctionTrivChar₁ N 1 = ∏ p ∈ N.primeFactors, (1 - (p : ℂ) ^ (-1 : ℂ)) := by
  have hzero : (1 : DirichletCharacter ℂ 1) (0 : ZMod 1) = 1 := by
    rw [show (0 : ZMod 1) = 1 from rfl, map_one]
  have hone : LFunctionTrivChar₁ 1 1 = 1 := by
    simp only [LFunctionTrivChar₁, LFunction₁, sub_self, zero_mul, zero_add,
      Nat.cast_one, one_cpow, ← singleton_eq_univ (0 : ZMod 1), sum_singleton,
      hzero, one_mul, reciprocalGammaℝ_one]
  have h := congrFun (LFunction₁_changeLevel N.one_dvd (1 : DirichletCharacter ℂ 1)) (1 : ℂ)
  rw [changeLevel_one N.one_dvd, show LFunction₁ (1 : DirichletCharacter ℂ 1) 1 = 1 from hone,
    one_mul] at h
  refine h.trans (Finset.prod_congr rfl fun p _ ↦ ?_)
  rw [MulChar.one_apply (isUnit_of_subsingleton _), one_mul]

/-- The L function of the trivial Dirichlet character mod `N` has a simple pole with
residue `∏ p ∈ N.primeFactors, (1 - p⁻¹)` at `s = 1`. -/
lemma LFunctionTrivChar_residue_one :
    Tendsto (fun s : {z : ℂ // z ≠ 1} ↦ ((s : ℂ) - 1) * LFunctionTrivChar N s s.2)
      (comap Subtype.val (𝓝 1))
      (𝓝 <| ∏ p ∈ N.primeFactors, (1 - (p : ℂ) ^ (-1 : ℂ))) := by
  rw [← LFunctionTrivChar₁_apply_one]
  refine ((differentiable_LFunction₁ (1 : DirichletCharacter ℂ N)).continuous.tendsto 1 |>.comp
    tendsto_comap).congr fun s ↦ ?_
  exact LFunction₁_eq_mul (1 : DirichletCharacter ℂ N) s.2

/-!
### Completed L-functions and the functional equation
-/

section gammaFactor

omit [NeZero N] -- not required for these declarations

open scoped Classical in
/-- The Archimedean Gamma factor: `Gammaℝ s` if `χ` is even, and `Gammaℝ (s + 1)` otherwise. -/
noncomputable def gammaFactor (χ : DirichletCharacter ℂ N) (s : ℂ) :=
  if χ.Even then Gammaℝ s else Gammaℝ (s + 1)

lemma Even.gammaFactor_def {χ : DirichletCharacter ℂ N} (hχ : χ.Even) (s : ℂ) :
    gammaFactor χ s = Gammaℝ s := by
  simp [gammaFactor, hχ]

lemma Odd.gammaFactor_def {χ : DirichletCharacter ℂ N} (hχ : χ.Odd) (s : ℂ) :
    gammaFactor χ s = Gammaℝ (s + 1) := by
  simp [gammaFactor, hχ.not_even]

end gammaFactor

/-- The regular domain of the completed Dirichlet L-function. -/
abbrev completedLFunctionDomain (χ : DirichletCharacter ℂ N) : Set ℂ :=
  {s | (s ≠ 0 ∨ N ≠ 1) ∧ (s ≠ 1 ∨ χ ≠ 1)}

/-- The completed L-function on its regular domain. -/
@[pp_nodot] noncomputable def completedLFunction (χ : DirichletCharacter ℂ N) (s : ℂ)
    (hs : s ∈ completedLFunctionDomain χ := by assumption) : ℂ :=
  ZMod.completedLFunction χ s (hs := ⟨hs.1.imp_right χ.map_zero',
    hs.2.imp_right χ.sum_eq_zero_of_ne_one⟩)

/-- The completed Dirichlet L-function as a function of a regular point. -/
noncomputable abbrev completedLFunctionOn (χ : DirichletCharacter ℂ N)
    (s : completedLFunctionDomain χ) : ℂ := completedLFunction χ s (hs := s.2)

/--
The completed L-function of the (unique) Dirichlet character mod 1 is the completed Riemann zeta
function.
-/
lemma completedLFunction_modOne_eq {χ : DirichletCharacter ℂ 1} {s : ℂ}
    (hs₀ : s ≠ 0) (hs₁ : s ≠ 1) :
    completedLFunction χ s (hs := ⟨Or.inl hs₀, Or.inl hs₁⟩) = completedRiemannZeta s hs₀ hs₁ := by
  change ZMod.completedLFunction χ s (hs := ⟨Or.inl hs₀, Or.inl hs₁⟩) = _
  rw [ZMod.completedLFunction_modOne_eq χ s hs₀ hs₁, map_one, one_mul]

/--
The completed L-function of a Dirichlet character is differentiable, with the following
exceptions: at `s = 1` if `χ` is the trivial character (to any modulus); and at `s = 0` if the
modulus is 1. This result is best possible.

Note both `χ` and `s` are explicit arguments: we will always be able to infer one or other
of them from the hypotheses, but it's not clear which!
-/
lemma differentiableAt_completedLFunction (χ : DirichletCharacter ℂ N) (s : ℂ)
    (hs₀ : s ≠ 0 ∨ N ≠ 1) (hs₁ : s ≠ 1 ∨ χ ≠ 1) :
    DifferentiableAt ℂ (completedLFunctionOn χ) ⟨s, hs₀, hs₁⟩ Subtype.val := by
  let φ : completedLFunctionDomain χ → ZMod.completedLFunctionDomain (χ : ZMod N → ℂ) :=
    fun z ↦ ⟨z, z.2.1.imp_right χ.map_zero', z.2.2.imp_right χ.sum_eq_zero_of_ne_one⟩
  have hφ : Continuous φ := continuous_subtype_val.subtype_mk _
  obtain ⟨d, hd⟩ := ZMod.differentiableAt_completedLFunction χ s
    ⟨hs₀.imp_right χ.map_zero', hs₁.imp_right χ.sum_eq_zero_of_ne_one⟩
  exact ⟨d, HasFDerivAtFilter.comp_tendsto hd φ
    ((hφ.tendsto ⟨s, hs₀, hs₁⟩).prodMap (tendsto_pure_pure ..))⟩

/-- The completed L-function of a non-trivial Dirichlet character is differentiable everywhere. -/
lemma differentiable_completedLFunction {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    Differentiable ℂ (fun s ↦ completedLFunction χ s (hs := ⟨
      Or.inr (hχ ∘ level_one' _), Or.inr hχ⟩)) :=
  ZMod.differentiable_completedLFunction (χ.map_zero' (hχ ∘ level_one' _))
    (χ.sum_eq_zero_of_ne_one hχ)

open scoped Classical in
/-- The entire reciprocal of the archimedean Gamma factor of a Dirichlet character. -/
noncomputable def reciprocalGammaFactor (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  if χ.Even then reciprocalGammaℝ s else reciprocalGammaℝ (s + 1)

/-- On the regular domain of the completion, the Dirichlet L-function is its product with the
entire reciprocal Gamma factor. -/
lemma LFunction_eq_completed_mul_reciprocalGammaFactor (χ : DirichletCharacter ℂ N) (s : ℂ)
    (hs : s ∈ completedLFunctionDomain χ) :
    LFunction χ s (hs := hs.2.symm) =
      completedLFunction χ s (hs := hs) * reciprocalGammaFactor χ s := by
  rcases χ.even_or_odd with hχ | hχ
  · simpa only [LFunction, completedLFunction, reciprocalGammaFactor, ite_eq_left hχ] using
      LFunction_eq_completed_mul_reciprocalGammaℝ_even hχ.to_fun s
        ⟨hs.1.imp_right χ.map_zero', hs.2.imp_right χ.sum_eq_zero_of_ne_one⟩
  · simpa only [LFunction, completedLFunction, reciprocalGammaFactor, ite_eq_right hχ.not_even]
      using
      LFunction_eq_completed_mul_reciprocalGammaℝ_odd hχ.to_fun s

open scoped Classical in
/--
Global root number of a primitive Dirichlet character `χ`, with primitivity witnessed by `hχ`.
Defined as
`gaussSum χ stdAddChar / I ^ a / N ^ (1 / 2)`, where `a = 0` if even, `a = 1` if odd. (The factor
`1 / I ^ a` is the Archimedean root number.) This is a complex number of absolute value 1.
-/
@[nolint unusedArguments]
noncomputable def rootNumber (χ : DirichletCharacter ℂ N) (_hχ : IsPrimitive χ) : ℂ :=
  Checked.div (Checked.div (gaussSum χ stdAddChar) (I ^ (if χ.Even then 0 else 1 : ℕ))
    (pow_ne_zero _ I_ne_zero).isUnit) ((N : ℂ) ^ (1 / 2 : ℂ))
    (cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr (NeZero.ne N)))).isUnit

/-- The root number of the unique Dirichlet character modulo 1 is 1. -/
@[simp] lemma rootNumber_modOne (χ : DirichletCharacter ℂ 1) (hχ : IsPrimitive χ) :
    rootNumber χ hχ = 1 := by
  simp [rootNumber, gaussSum, -univ_unique, ← singleton_eq_univ (1 : ZMod 1),
    (show stdAddChar (1 : ZMod 1) = 1 from AddChar.map_zero_eq_one _),
    (show χ.Even from map_one _)]

namespace IsPrimitive

private lemma ne_one_of_ne_level_one {χ : DirichletCharacter ℂ N} (hχ : IsPrimitive χ)
    (hN : N ≠ 1) : χ ≠ 1 := by
  intro h
  apply hN.symm
  rwa [IsPrimitive, h, conductor_one] at hχ

private lemma completedDomain_one_sub {χ : DirichletCharacter ℂ N} (hχ : IsPrimitive χ) {s : ℂ}
    (hs : s ∈ completedLFunctionDomain χ) : 1 - s ∈ completedLFunctionDomain χ := by
  refine ⟨?_, ?_⟩
  · exact (hs.2.imp_left (sub_ne_zero.mpr ∘ Ne.symm)).imp_right fun h ↦ h ∘ level_one' _
  · exact (hs.1.imp_left fun h h' ↦ h (by linear_combination -h')).imp_right
      (ne_one_of_ne_level_one hχ)

omit [NeZero N] in
private lemma completedDomain_inv {χ : DirichletCharacter ℂ N} {s : ℂ}
    (hs : s ∈ completedLFunctionDomain χ) : s ∈ completedLFunctionDomain χ⁻¹ :=
  ⟨hs.1, hs.2.imp_right fun h h' ↦ h (inv_eq_one.mp h')⟩

/-- **Functional equation** for primitive Dirichlet L-functions. -/
theorem completedLFunction_one_sub {χ : DirichletCharacter ℂ N} (hχ : IsPrimitive χ) (s : ℂ)
    (hs : s ∈ completedLFunctionDomain χ) :
    completedLFunction χ (1 - s) (hs := by exact completedDomain_one_sub hχ hs) =
      N ^ (s - 1 / 2) * rootNumber χ hχ *
        completedLFunction χ⁻¹ s (hs := by exact completedDomain_inv hs) := by
  classical
  rcases eq_or_ne N 1 with rfl | hN
  · have hχ₁ : χ = 1 := level_one' χ rfl
    have hs₀ : s ≠ 0 := hs.1.resolve_right (fun h ↦ h rfl)
    have hs₁ : s ≠ 1 := hs.2.resolve_right (fun h ↦ h hχ₁)
    have hleft₀ : 1 - s ≠ 0 := sub_ne_zero.mpr hs₁.symm
    have hleft₁ : 1 - s ≠ 1 := fun h ↦ hs₀ (by linear_combination -h)
    simpa only [completedLFunction_modOne_eq hleft₀ hleft₁,
      completedLFunction_modOne_eq hs₀ hs₁, rootNumber_modOne, Nat.cast_one, one_cpow, one_mul]
      using completedRiemannZeta_one_sub (s := s) (hs0 := hs₀) (hs1 := hs₁)
  have hχ₁ : χ ≠ 1 := ne_one_of_ne_level_one hχ hN
  have hχinv : χ⁻¹ ≠ 1 := fun h ↦ hχ₁ (inv_eq_one.mp h)
  let ε : ℂ := I ^ (if χ.Even then 0 else 1 : ℕ)
  have hε : IsUnit ε := (pow_ne_zero _ I_ne_zero).isUnit
  have hN₀ : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hNhalf : IsUnit ((N : ℂ) ^ (1 / 2 : ℂ)) := (cpow_ne_zero_iff.mpr (Or.inl hN₀)).isUnit
  let c := χ⁻¹ (-1) * gaussSum χ stdAddChar
  have hFourier : (𝓕 (χ : ZMod N → ℂ)) = fun j ↦ c * χ⁻¹ j := by
    funext j
    dsimp only [c]
    rw [hχ.fourierTransform_eq_inv_mul_gaussSum, ← neg_one_mul j, map_mul, mul_right_comm]
  have hF₀ : (𝓕 (χ : ZMod N → ℂ)) 0 = 0 := by
    rw [hFourier]
    change c * χ⁻¹ 0 = 0
    rw [χ⁻¹.map_zero' hN, mul_zero]
  have hF₁ : ∑ j, (𝓕 (χ : ZMod N → ℂ)) j = 0 := by
    rw [hFourier, ← mul_sum, χ⁻¹.sum_eq_zero_of_ne_one hχinv, mul_zero]
  let H := ZMod.completedLFunction (𝓕 (χ : ZMod N → ℂ)) s
    (hs := ⟨Or.inr hF₀, Or.inr hF₁⟩)
  let R := completedLFunction χ⁻¹ s (hs := completedDomain_inv hs)
  have hscale : H = c * R := by
    dsimp only [H, R, completedLFunction]
    rw [ZMod.completedLFunction_congr hFourier, ZMod.completedLFunction_const_mul c _ s
      ⟨Or.inr (χ⁻¹.map_zero' hN), Or.inr (χ⁻¹.sum_eq_zero_of_ne_one hχinv)⟩]
  have hFE : completedLFunction χ (1 - s) (hs := completedDomain_one_sub hχ hs) =
      (N : ℂ) ^ (s - 1) * (χ (-1) / ε) * H := by
    rcases χ.even_or_odd with hev | hod
    · have h := ZMod.completedLFunction_one_sub_even hev.to_fun s
        (Or.inr (χ.sum_eq_zero_of_ne_one hχ₁)) (Or.inr (χ.map_zero' hN))
      have hminus : χ (-1) = 1 := hev
      have he : ε = 1 := by simp [ε, hev]
      simpa only [completedLFunction, H, he, hminus, div_one₀, mul_one]
        using h
    · have h := ZMod.completedLFunction_one_sub_odd hod.to_fun s
      have hminus : χ (-1) = -1 := hod
      have he : ε = I := by simp [ε, hod.not_even]
      simpa only [completedLFunction, H, he, hminus, div_I, neg_one_mul, neg_neg] using h
  have hχneg : χ (-1) * χ⁻¹ (-1) = 1 := by
    rw [← MulChar.mul_apply, mul_inv_cancel, MulChar.one_apply (isUnit_one.neg)]
  have hpow : (N : ℂ) ^ (s - 1 / 2) = (N : ℂ) ^ (s - 1) * (N : ℂ) ^ (1 / 2 : ℂ) := by
    rw [← cpow_add _ _ hN₀]
    congr 1
    ring
  calc
    _ = (N : ℂ) ^ (s - 1) * (χ (-1) / ε) * H := hFE
    _ = (N : ℂ) ^ (s - 1) * (gaussSum χ stdAddChar / ε) * R := by
      rw [hscale]
      dsimp only [c]
      simp only [div_eq_mul_inv₀]
      calc
        _ = (χ (-1) * χ⁻¹ (-1)) * ((N : ℂ) ^ (s - 1) * (gaussSum χ stdAddChar * ε⁻¹) * R) := by
          ring
        _ = _ := by rw [hχneg, one_mul]
    _ = (N : ℂ) ^ (s - 1) * (((N : ℂ) ^ (1 / 2 : ℂ)) *
          ((gaussSum χ stdAddChar / ε) / (N : ℂ) ^ (1 / 2 : ℂ))) * R := by
      rw [mul_div_cancel₀]
    _ = _ := by rw [hpow, rootNumber]; dsimp only [ε, R]; ring

end IsPrimitive

end DirichletCharacter

/-!
### The logarithmic derivative of the L-function of a Dirichlet character

We show that `s ↦ -(L' χ s) / L χ s + 1 / (s - 1)` is continuous outside the zeros of `L χ`
when `χ` is a trivial Dirichlet character and that `-L' χ / L χ` is continuous outside
the zeros of `L χ` when `χ` is nontrivial.
-/

namespace DirichletCharacter

open Complex

section trivial

variable (n : ℕ) [NeZero n]

lemma LFunctionTrivChar₁_apply_one_ne_zero : LFunctionTrivChar₁ n 1 ≠ 0 := by
  rw [LFunctionTrivChar₁_apply_one]
  refine Finset.prod_ne_zero_iff.mpr fun p hp ↦ ?_
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hpu : IsUnit (p : ℂ) := (Nat.cast_ne_zero.mpr hprime.ne_zero).isUnit
  rw [cpow_neg_one _ (hx := hpu), sub_ne_zero]
  intro h
  have h' := congrArg (fun z : ℂ ↦ z * (p : ℂ)) h
  rw [one_mul, inv_mul_cancel₀] at h'
  exact hprime.ne_one (by exact_mod_cast h')

/-- `s ↦ (s - 1) * L χ s` is an entire function when `χ` is a trivial Dirichlet character. -/
lemma differentiable_LFunctionTrivChar₁ : Differentiable ℂ (LFunctionTrivChar₁ n) := by
  exact differentiable_LFunction₁ (1 : DirichletCharacter ℂ n)

lemma deriv_LFunctionTrivChar₁_apply_of_ne_one {s : ℂ} (hs : s ≠ 1) :
    deriv (LFunctionTrivChar₁ n) s =
      (s - 1) * deriv (LFunctionOn (1 : DirichletCharacter ℂ n)) ⟨s, Or.inr hs⟩ Subtype.val +
        LFunctionTrivChar n s hs := by
  let D := LFunctionDomain (1 : DirichletCharacter ℂ n)
  let x : D := ⟨s, Or.inr hs⟩
  have hD := (isOpen_LFunctionDomain (1 : DirichletCharacter ℂ n)).isOpenEmbedding_subtypeVal
  have hI : HasDerivAt (fun z : D ↦ (z : ℂ) - 1) 1 x Subtype.val :=
    hasDerivAt_subtype_val (x := x) ((hasDerivAt_id' (x : ℂ)).sub_const 1)
  have hL : HasDerivAt (LFunctionOn (1 : DirichletCharacter ℂ n))
      (deriv (LFunctionOn (1 : DirichletCharacter ℂ n)) x Subtype.val) x Subtype.val :=
    (differentiableAt_LFunction (1 : DirichletCharacter ℂ n) s (Or.inl hs)).hasFDerivAt.hasDerivAt
  have hprod := hI.fun_mul hL (hcoord := continuousAt_subtype_val)
  have hNorm : HasDerivAt (fun z : D ↦ LFunctionTrivChar₁ n z)
      (deriv (LFunctionTrivChar₁ n) s) x Subtype.val :=
    hasDerivAt_subtype_val (differentiable_LFunctionTrivChar₁ n s).hasDerivAt
  have hEq : (fun z : D ↦ LFunctionTrivChar₁ n z) =
      fun z : D ↦ ((z : ℂ) - 1) * LFunctionOn (1 : DirichletCharacter ℂ n) z := by
    funext z
    exact LFunction₁_eq_mul (1 : DirichletCharacter ℂ n) (z.2.resolve_left (fun h ↦ h rfl))
  calc
    _ = deriv (fun z : D ↦ LFunctionTrivChar₁ n z) x Subtype.val := (hNorm.deriv hD).symm
    _ = _ := by
      rw [hEq]
      simpa only [one_mul, add_comm] using hprod.deriv hD

/-- The negative logarithmic derivative of `s ↦ (s - 1) * L χ s` for a trivial
Dirichlet character `χ` is continuous away from the zeros of `L χ` (including at `s = 1`). -/
lemma continuousOn_neg_logDeriv_LFunctionTrivChar₁ :
    Continuous (fun s : {z : ℂ // IsUnit (LFunctionTrivChar₁ n z)} ↦
      Checked.div (-deriv (LFunctionTrivChar₁ n) s) (LFunctionTrivChar₁ n s) s.2) := by
  have h := differentiable_LFunctionTrivChar₁ n
  exact Continuous.div₀ ((h.contDiff.continuous_deriv le_rfl).neg.comp continuous_subtype_val)
    (h.continuous.comp continuous_subtype_val)

end trivial

section nontrivial

variable {n : ℕ} [NeZero n] {χ : DirichletCharacter ℂ n}

/-- The negative logarithmic derivative of the L-function of a nontrivial Dirichlet character
is continuous away from the zeros of the L-function. -/
lemma continuousOn_neg_logDeriv_LFunction_of_nontriv (hχ : χ ≠ 1) :
    Continuous (fun s : {z : ℂ // IsUnit (LFunction χ z (hs := Or.inl hχ))} ↦
      Checked.div (-deriv (fun z ↦ LFunction χ z (hs := Or.inl hχ)) s)
        (LFunction χ s (hs := Or.inl hχ)) s.2) := by
  have h := differentiable_LFunction hχ
  exact Continuous.div₀ ((h.contDiff.continuous_deriv le_rfl).neg.comp continuous_subtype_val)
    (h.continuous.comp continuous_subtype_val)

end nontrivial

end DirichletCharacter
