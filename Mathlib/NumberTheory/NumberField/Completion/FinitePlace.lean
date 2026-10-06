/-
Copyright (c) 2024 Fabrizio Barroero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero
-/
module

public import Mathlib.Algebra.Order.Archimedean.Submonoid
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.NumberTheory.RamificationInertia.Valuation
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.RamificationInertia.Inertia
public import Mathlib.RingTheory.Valuation.Archimedean
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
public import Mathlib.Topology.Algebra.Valued.NormedValued

import Mathlib.Algebra.FiniteSupport.Basic

/-!
# Finite places of number fields

This file defines finite places of a number field `K` as absolute values coming from an embedding
into a completion of `K` associated to a non-zero prime ideal of `𝓞 K`.

Many of the results in this file are expressed in the generality of: `R` is a Dedekind domain
with field of fractions `K` such that `Module.Finite ℤ R` and `Module.Free ℤ R`. If `K` is
a number field, then this characterises `R` as being isomorphic to `𝓞 K` without explicitly
requiring `𝓞 K`. This is so that `ℤ` and `𝓞 ℚ` can be used interchangeably.

## Main Definitions and Results
* `NumberField.adicAbv`: a `v`-adic absolute value on `K`.
* `NumberField.FinitePlace`: the type of finite places of a number field `K`.
* `NumberField.FinitePlace.embedding`: the canonical embedding of a number field `K` to the
  `v`-adic completion `v.adicCompletion K` of `K`, where `v` is a non-zero prime ideal of `𝓞 K`
* `NumberField.FinitePlace.norm_embedding`: the norm of `embedding v x` is the same as the `v`-adic
  absolute value of `x`. See also `NumberField.FinitePlace.norm_embedding'` and
  `NumberField.FinitePlace.norm_embedding_int` for versions where the `v`-adic absolute value is
  unfolded.
* `NumberField.FinitePlace.hasFiniteMulSupport`: the `v`-adic absolute value of a non-zero element
  of `K` is different from 1 for at most finitely many `v`.
*  The valuation subrings of the field at the `v`-valuation and it's adic completion are
   discrete valuation rings.
* `IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.quotientAlgEquivResidueField`: the
  residue field of the completed integers at `v` is the residue field `A ⧸ v` of `A`. It is finite
  when `A` has finite quotients, and its size is then the absolute norm of `v`.

## Tags
number field, places, finite places
-/

@[expose] public section

open Ideal IsDedekindDomain HeightOneSpectrum WithZeroMulInt WithZero

open scoped WithZero NNReal

section DVR

variable (A : Type*) [CommRing A] [IsDedekindDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (v : HeightOneSpectrum A) (hv : Finite (A ⧸ v.asIdeal))

instance : IsPrincipalIdealRing (v.valuation K).integer := by
  rw [(Valuation.integer.integers (v.valuation K)).isPrincipalIdealRing_iff_not_denselyOrdered,
    WithZero.denselyOrdered_set_iff_subsingleton]
  simpa using (v.valuation K).toMonoidWithZeroHom.range_nontrivial

instance : IsDiscreteValuationRing (v.valuation K).integer :=
  (v.valuation K).valuationSubring_isDiscreteValuationRing

instance : IsPrincipalIdealRing (v.adicCompletionIntegers K) := by
  unfold HeightOneSpectrum.adicCompletionIntegers
  rw [(Valuation.valuationSubring.integers (Valued.v)).isPrincipalIdealRing_iff_not_denselyOrdered,
    WithZero.denselyOrdered_set_iff_subsingleton]
  simpa using Valued.v.range_nontrivial

-- TODO: make this inferred from `IsRankOneDiscrete`, or
-- develop the API for a completion of a base `IsDVR` ring
instance : IsDiscreteValuationRing (v.adicCompletionIntegers K) where
  not_a_field' := by
    unfold HeightOneSpectrum.adicCompletionIntegers
    simp only [ne_eq, Ideal.ext_iff, Valuation.mem_maximalIdeal_iff, Ideal.mem_bot, Subtype.ext_iff,
      ZeroMemClass.coe_zero, Subtype.forall, Valuation.mem_valuationSubring_iff, not_forall,
      exists_prop]
    obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer K
    use (WithVal.equiv (v.valuation K)).symm π
    simp [hπ, ← exp_zero,
      ← (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).map_eq_zero_iff]

end DVR

namespace IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers

/-! ### The residue field of the completed integers -/

open IsLocalRing Topology

variable {A : Type*} [CommRing A] [IsDedekindDomain A] (K : Type*) [Field K] [Algebra A K]
  [IsFractionRing A K] (v : HeightOneSpectrum A)

variable {K v} in
/-- Every element of the completed integers is congruent to an element of `A` modulo the maximal
ideal. -/
theorem exists_algebraMap_sub_mem_maximalIdeal (x : v.adicCompletionIntegers K) :
    ∃ a : A, algebraMap A (v.adicCompletionIntegers K) a - x ∈
      maximalIdeal (v.adicCompletionIntegers K) := by
  have hs : {z : v.adicCompletion K | Valued.v (z - x) < 1} ∈ 𝓝 (x : v.adicCompletion K) :=
    Valued.mem_nhds.2 ⟨1, fun y hy ↦ by simpa [Valuation.restrict_lt_one_iff] using hy⟩
  obtain ⟨_, hmem, k, rfl⟩ :=
    mem_closure_iff_nhds.1 (denseRange_algebraMap K v (x : v.adicCompletion K)) _ hs
  have hz : Valued.v (algebraMap K (v.adicCompletion K) k - x) < 1 := hmem
  have hk : v.valuation K k ≤ 1 := by
    have h := Valuation.map_add_le Valued.v hz.le x.2
    rw [sub_add_cancel] at h
    rwa [← valuedAdicCompletion_eq_valuation']
  obtain ⟨a, ha⟩ := exists_valuation_sub_lt_of_integer v hk 1
  refine ⟨a, (Valuation.mem_maximalIdeal_iff (v.adicCompletion K) Valued.v).2 ?_⟩
  have hsplit : algebraMap A (v.adicCompletion K) a - x =
      algebraMap K (v.adicCompletion K) (algebraMap A K a - k) +
        (algebraMap K (v.adicCompletion K) k - x) := by
    rw [map_sub, ← IsScalarTower.algebraMap_apply]
    ring
  change Valued.v (algebraMap A (v.adicCompletion K) a - x) < 1
  rw [hsplit]
  refine Valuation.map_add_lt _ ?_ hz
  exact (valuedAdicCompletion_eq_valuation' v (algebraMap A K a - k)).trans_lt (by simpa using ha)

/-- Every residue class of the completed integers is represented by an element of `A`. -/
theorem algebraMap_residueField_surjective :
    Function.Surjective (algebraMap A (IsLocalRing.ResidueField (v.adicCompletionIntegers K))) := by
  intro y
  obtain ⟨x, rfl⟩ := residue_surjective y
  obtain ⟨a, ha⟩ := exists_algebraMap_sub_mem_maximalIdeal x
  refine ⟨a, ?_⟩
  rw [IsScalarTower.algebraMap_apply A (v.adicCompletionIntegers K), ResidueField.algebraMap_eq,
    ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
  exact ha

/-- An element of `A` vanishes in the residue field of the completed integers if and only if it
lies in `v`. -/
theorem ker_algebraMap_residueField :
    RingHom.ker (algebraMap A (IsLocalRing.ResidueField (v.adicCompletionIntegers K))) =
      v.asIdeal := by
  ext a
  rw [RingHom.mem_ker, IsScalarTower.algebraMap_apply A (v.adicCompletionIntegers K),
    ResidueField.algebraMap_eq, residue_eq_zero_iff, ← valuation_lt_one_iff_mem (K := K),
    ← valuedAdicCompletion_eq_valuation]
  exact Valuation.mem_maximalIdeal_iff (v.adicCompletion K) Valued.v

/-- The residue field of the completed integers at `v` is the residue field `A ⧸ v` of `A`. -/
noncomputable def quotientAlgEquivResidueField :
    (A ⧸ v.asIdeal) ≃ₐ[A] IsLocalRing.ResidueField (v.adicCompletionIntegers K) :=
  (Ideal.quotientEquivAlgOfEq A (ker_algebraMap_residueField K v).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId A _)
      (algebraMap_residueField_surjective K v))

/-- The residue fields of `A` and of its completed integers at `v` have the same size. -/
theorem natCard_residueField :
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) = Nat.card (A ⧸ v.asIdeal) :=
  (Nat.card_congr (quotientAlgEquivResidueField K v).toEquiv).symm

/-- The residue field of the completed integers is finite if and only if `A ⧸ v` is. -/
theorem finite_residueField_iff :
    Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) ↔ Finite (A ⧸ v.asIdeal) :=
  (quotientAlgEquivResidueField K v).toEquiv.finite_iff.symm

/-- The completed integers of a ring with finite quotients, such as the ring of integers of a
number field, have a finite residue field. -/
instance finite_residueField [Ring.HasFiniteQuotients A] :
    Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) :=
  (finite_residueField_iff K v).2 (Ring.HasFiniteQuotients.finiteQuotient v.ne_bot)

/-- The size of the residue field of the completed integers is the absolute norm of `v`. Both are
sizes of finite sets when `A` has finite quotients, as for the ring of integers of a number
field. -/
theorem natCard_residueField_eq_absNorm [Infinite A] :
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) = absNorm v.asIdeal := by
  rw [natCard_residueField, absNorm_apply, Submodule.cardQuot_apply]

end IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers

namespace IsDiscreteValuationRing

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- The canonical residue-field isomorphism of a discrete valuation ring with its completion. -/
noncomputable def residueFieldEquivAdicCompletion :
    IsLocalRing.ResidueField R ≃ₐ[R]
      IsLocalRing.ResidueField ((maximalIdeal R).adicCompletionIntegers K) :=
  IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.quotientAlgEquivResidueField K
    (maximalIdeal R)

/-- Completing a discrete valuation ring preserves finiteness of its residue field. -/
instance finite_residueField_adicCompletion [Finite (IsLocalRing.ResidueField R)] :
    Finite (IsLocalRing.ResidueField ((maximalIdeal R).adicCompletionIntegers K)) :=
  Finite.of_equiv _ (residueFieldEquivAdicCompletion R (K := K)).toEquiv

end IsDiscreteValuationRing

namespace NumberField

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {R : Type*} [CommRing R] [Algebra R K]
  [IsDedekindDomain R] [IsFractionRing R K] (v : HeightOneSpectrum R)

/-- The embedding of a field inside its `adicCompletion` with respect to `v`. -/
noncomputable def FinitePlace.embedding : K →+* adicCompletion K v :=
  (adicCompletion.equiv K v).symm.toRingHom.comp
    (UniformSpace.Completion.coeRingHom.comp (WithVal.equiv (v.valuation K)).symm)

theorem FinitePlace.embedding_apply (x : K) : embedding v x = ↑x := rfl

section AbsoluteValue

noncomputable instance : ((Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)).IsRankOneDiscrete where
  exists_generator_lt_one' := by
    have h : (v.valuation K).IsRankOneDiscrete := Valuation.IsRankOneDiscrete.mk' (valuation K v)
    exact ⟨h.generator, by rw [h.generator_zpowers_eq_valueGroup, adicCompletion_valueGroup_eq],
      h.generator_lt_one⟩

section FiniteFree

/-! In this section we assume further that `R` has finite quotients and is infinite,
as holds for the ring of integers `𝓞 K` of a number field. -/

variable [Ring.HasFiniteQuotients R] [Infinite R]

namespace HeightOneSpectrum

/-- The norm of a maximal ideal is `> 1` -/
lemma one_lt_absNorm : 1 < absNorm v.asIdeal := by
  by_contra! h
  apply IsPrime.ne_top v.isPrime
  rw [← absNorm_eq_one_iff]
  have : 0 < absNorm v.asIdeal := by
    rw [Nat.pos_iff_ne_zero, absNorm_ne_zero_iff]
    exact Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  lia

/-- The norm of a maximal ideal as an element of `ℝ≥0` is `> 1` -/
lemma one_lt_absNorm_nnreal : 1 < (absNorm v.asIdeal : ℝ≥0) := mod_cast one_lt_absNorm v

lemma two_le_absNorm_nnreal : 2 ≤ (absNorm v.asIdeal : ℝ≥0) := mod_cast one_lt_absNorm v

/-- The norm of a maximal ideal as an element of `ℝ≥0` is `≠ 0` -/
lemma absNorm_ne_zero : (absNorm v.asIdeal : ℝ≥0) ≠ 0 :=
  ne_zero_of_lt (one_lt_absNorm_nnreal v)

variable (K)

/-- The `v`-adic absolute value on `K` defined as the norm of `v` raised to negative `v`-adic
valuation -/
noncomputable def adicAbv : AbsoluteValue K ℝ := v.adicAbv <| one_lt_absNorm_nnreal v

theorem adicAbv_def {x : K} : adicAbv K v x = toNNReal (absNorm_ne_zero v) (v.valuation K x) := rfl

/-- The `v`-adic absolute value is nonarchimedean -/
theorem isNonarchimedean_adicAbv : IsNonarchimedean (adicAbv K v) :=
  v.isNonarchimedean_adicAbv <| one_lt_absNorm_nnreal v

open Valuation.IsRankOneDiscrete

noncomputable instance : (v.valuation K).RankOne :=
  rankOne (v.valuation K) (one_lt_absNorm_nnreal v)

noncomputable instance instRankOneAdicCompletion :
    (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).RankOne :=
  rankOne (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰) (one_lt_absNorm_nnreal v)

lemma rankOne_hom'_def :
    (instRankOneAdicCompletion K v).hom' = (toNNReal (absNorm_ne_zero v)).comp
      (valueGroup₀_equiv_withZeroMulInt Valued.v).toMonoidWithZeroHom := rfl

/-- The `v`-adic completion of `K` is a normed field. -/
noncomputable instance instNormedFieldValuedAdicCompletion : NormedField (adicCompletion K v) :=
  Valued.toNormedField (adicCompletion K v) ℤᵐ⁰

lemma toNNReal_valued_eq_adicAbv (x : WithVal (v.valuation K)) :
    toNNReal (absNorm_ne_zero v) (Valued.v x) = adicAbv K v (WithVal.equiv _ x) := rfl

/-- The `v`-adic absolute value satisfies the ultrametric inequality. -/
theorem adicAbv_add_le_max (x y : K) :
    adicAbv K v (x + y) ≤ (adicAbv K v x) ⊔ (adicAbv K v y) := isNonarchimedean_adicAbv K v x y

/-- The `v`-adic absolute value of a natural number is `≤ 1`. -/
theorem adicAbv_natCast_le_one (n : ℕ) : adicAbv K v n ≤ 1 :=
  (isNonarchimedean_adicAbv K v).apply_natCast_le_one (map_zero_le (adicAbv K v) 1)
  (map_one (adicAbv K v))

/-- The `v`-adic absolute value of an integer is `≤ 1`. -/
theorem adicAbv_intCast_le_one (n : ℤ) : adicAbv K v n ≤ 1 :=
  (isNonarchimedean_adicAbv K v).apply_intCast_le_one (map_zero_le (adicAbv K v) 1)
  (map_one (adicAbv K v)) (map_neg_eq_map (adicAbv K v))


set_option linter.dupNamespace false in
@[deprecated (since := "2026-03-11")]
alias NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm := one_lt_absNorm
@[deprecated (since := "2026-03-11")]
alias _root_.NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm := one_lt_absNorm
set_option linter.dupNamespace false in
@[deprecated (since := "2026-03-11")]
alias NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm_nnreal := one_lt_absNorm_nnreal
@[deprecated (since := "2026-03-11")]
alias _root_.NumberField.RingOfIntegers.HeightOneSpectrum.one_lt_absNorm_nnreal :=
  one_lt_absNorm_nnreal
set_option linter.dupNamespace false in
@[deprecated (since := "2026-03-11")]
alias NumberField.RingOfIntegers.HeightOneSpectrum.absNorm_ne_zero := absNorm_ne_zero
@[deprecated (since := "2026-03-11")]
alias _root_.NumberField.RingOfIntegers.HeightOneSpectrum.absNorm_ne_zero := absNorm_ne_zero
set_option linter.dupNamespace false in
@[deprecated (since := "2026-03-11")]
alias NumberField.RingOfIntegers.HeightOneSpectrum.adicAbv := adicAbv
@[deprecated (since := "2026-03-11")]
alias _root_.NumberField.RingOfIntegers.HeightOneSpectrum.adicAbv := adicAbv
set_option linter.dupNamespace false in
@[deprecated (since := "2026-03-11")]
alias NumberField.RingOfIntegers.HeightOneSpectrum.adicAbv_def := adicAbv_def
@[deprecated (since := "2026-03-11")]
alias _root_.NumberField.RingOfIntegers.HeightOneSpectrum.adicAbv_def := adicAbv_def
set_option linter.dupNamespace false in
@[deprecated (since := "2026-03-11")]
alias NumberField.RingOfIntegers.HeightOneSpectrum.isNonarchimedean_adicAbv :=
  isNonarchimedean_adicAbv
@[deprecated (since := "2026-03-11")]
alias _root_.NumberField.RingOfIntegers.HeightOneSpectrum.isNonarchimedean_adicAbv :=
  isNonarchimedean_adicAbv
set_option linter.dupNamespace false in
@[deprecated (since := "2026-03-11")]
alias NumberField.instRankOneAdicCompletion := instRankOneAdicCompletion
@[deprecated (since := "2026-03-11")]
alias _root_.NumberField.instRankOneAdicCompletion := instRankOneAdicCompletion
set_option linter.dupNamespace false in
@[deprecated (since := "2026-03-11")]
alias NumberField.instNormedFieldValuedAdicCompletion := instNormedFieldValuedAdicCompletion
@[deprecated (since := "2026-03-11")]
alias _root_.NumberField.instNormedFieldValuedAdicCompletion := instNormedFieldValuedAdicCompletion
set_option linter.dupNamespace false in
@[deprecated (since := "2026-03-11")]
alias NumberField.rankOne_hom'_def := rankOne_hom'_def
@[deprecated (since := "2026-03-11")]
alias _root_.NumberField.rankOne_hom'_def := rankOne_hom'_def
set_option linter.dupNamespace false in
@[deprecated (since := "2026-03-11")]
alias NumberField.toNNReal_valued_eq_adicAbv := toNNReal_valued_eq_adicAbv
@[deprecated (since := "2026-03-11")]
alias _root_.NumberField.toNNReal_valued_eq_adicAbv := toNNReal_valued_eq_adicAbv
set_option linter.dupNamespace false in
@[deprecated (since := "2026-03-11")]
alias NumberField.RingOfIntegers.HeightOneSpectrum.adicAbv_add_le_max := adicAbv_add_le_max
@[deprecated (since := "2026-03-11")]
alias _root_.NumberField.RingOfIntegers.HeightOneSpectrum.adicAbv_add_le_max := adicAbv_add_le_max
set_option linter.dupNamespace false in
@[deprecated (since := "2026-03-11")]
alias NumberField.RingOfIntegers.HeightOneSpectrum.adicAbv_natCast_le_one := adicAbv_natCast_le_one
@[deprecated (since := "2026-03-11")]
alias _root_.NumberField.RingOfIntegers.HeightOneSpectrum.adicAbv_natCast_le_one :=
  adicAbv_natCast_le_one
set_option linter.dupNamespace false in
@[deprecated (since := "2026-03-11")]
alias NumberField.RingOfIntegers.HeightOneSpectrum.adicAbv_intCast_le_one := adicAbv_intCast_le_one
@[deprecated (since := "2026-03-11")]
alias _root_.NumberField.RingOfIntegers.HeightOneSpectrum.adicAbv_intCast_le_one :=
  adicAbv_intCast_le_one

end HeightOneSpectrum

open HeightOneSpectrum Valuation.IsRankOneDiscrete

/-- The norm of an element in the `v`-adic completion of `K`. See `FinitePlace.norm_embedding`
for the equality involving `‖embedding v x‖` on the LHS. -/
theorem FinitePlace.norm_def (x : v.adicCompletion K) :
    ‖x‖ = toNNReal (absNorm_ne_zero v) (Valued.v x) := by
  simp [Valued.toNormedField.norm_def, Valuation.RankOne.hom, HeightOneSpectrum.rankOne_hom'_def,
    valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective
      (valuedAdicCompletion_surjective K v)]

/-- The norm of the image after the embedding associated to `v` is equal to the `v`-adic absolute
value. -/
theorem FinitePlace.norm_embedding (x : K) : ‖embedding v x‖ = adicAbv K v x := by
  simp [norm_def, embedding_apply, adicAbv_def]

/-- The norm of the image after the embedding associated to `v` is equal to the norm of `v` raised
to the power of the `v`-adic valuation. -/
theorem FinitePlace.norm_embedding' (x : K) :
    ‖embedding v x‖ = toNNReal (absNorm_ne_zero v) (v.valuation K x) := by
  rw [norm_embedding, adicAbv_def]

variable (K)

/-- The norm of the image after the embedding associated to `v` is equal to the norm of `v` raised
to the power of the `v`-adic valuation for integers. -/
theorem FinitePlace.norm_embedding_int (x : R) :
    ‖embedding v (algebraMap _ K x)‖ = toNNReal (absNorm_ne_zero v) (v.intValuation x) := by
  simp [norm_embedding, adicAbv_def, valuation_of_algebraMap]

@[deprecated (since := "2026-03-05")] alias FinitePlace.norm_def' := FinitePlace.norm_embedding'
@[deprecated (since := "2026-03-05")] alias FinitePlace.norm_def_int :=
  FinitePlace.norm_embedding_int

open FinitePlace

/-- The `v`-adic norm of an integer is at most 1. -/
theorem FinitePlace.norm_le_one (x : R) : ‖embedding v (algebraMap _ K x)‖ ≤ 1 := by
  rw [norm_embedding]
  exact v.adicAbv_coe_le_one (one_lt_absNorm_nnreal v) x

/-- The `v`-adic norm of an integer is 1 if and only if it is not in the ideal. -/
theorem FinitePlace.norm_eq_one_iff_notMem (x : R) :
    ‖embedding v (algebraMap _ K x)‖ = 1 ↔ x ∉ v.asIdeal := by
  rw [norm_embedding]
  exact v.adicAbv_coe_eq_one_iff (one_lt_absNorm_nnreal v) x

/-- The `v`-adic norm of an integer is less than 1 if and only if it is in the ideal. -/
theorem FinitePlace.norm_lt_one_iff_mem (x : R) :
    ‖embedding v (algebraMap _ K x)‖ < 1 ↔ x ∈ v.asIdeal := by
  rw [norm_embedding]
  exact v.adicAbv_coe_lt_one_iff (one_lt_absNorm_nnreal v) x

variable {v} in
lemma FinitePlace.two_le_norm_of_one_lt_norm (x : v.adicCompletion K) (h : 1 < ‖x‖) : 2 ≤ ‖x‖ := by
  rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply (absNorm_ne_zero v) (by aesop)]
  apply (two_le_absNorm_nnreal v).trans
  conv_lhs => rw [← zpow_one (v.asIdeal.absNorm : NNReal)]
  apply zpow_le_zpow_right₀ (one_lt_absNorm_nnreal v).le
  simpa [← Int.sub_one_lt_iff, sub_self, ← toAdd_one, Multiplicative.toAdd_lt,
    WithZero.lt_unzero_iff] using Valued.toNormedField.one_lt_norm_iff.1 h

set_option backward.isDefEq.respectTransparency false in
lemma HeightOneSpectrum.embedding_mul_absNorm {x : R} (h_x_nezero : x ≠ 0) :
    ‖embedding v (algebraMap _ K x)‖ * absNorm (v.maxPowDividing (span {x})) = 1 := by
  rw [maxPowDividing, map_pow, Nat.cast_pow, norm_embedding, adicAbv_def,
    WithZeroMulInt.toNNReal_neg_apply _ ((v.valuation K).ne_zero_iff.mpr
      ((FaithfulSMul.algebraMap_eq_zero_iff R K).not.2 h_x_nezero))]
  push_cast
  rw [← zpow_natCast, ← zpow_add₀ <| mod_cast (zero_lt_one.trans (one_lt_absNorm_nnreal v)).ne']
  norm_cast
  rw [zpow_eq_one_iff_right₀ (Nat.cast_nonneg' _) (mod_cast (one_lt_absNorm_nnreal v).ne')]
  simp [valuation_of_algebraMap, intValuation_if_neg, h_x_nezero]

end FiniteFree

end AbsoluteValue

open HeightOneSpectrum

/-- A finite place of a number field `K` is a place associated to an embedding into a completion
with respect to a maximal ideal. -/
def FinitePlace (K : Type*) [Field K] [NumberField K] :=
  {w : AbsoluteValue K ℝ // ∃ v : HeightOneSpectrum (𝓞 K), place (FinitePlace.embedding v) = w}

/-- Return the finite place defined by a maximal ideal `v`. -/
noncomputable def FinitePlace.mk [NumberField K] (v : HeightOneSpectrum (𝓞 K)) : FinitePlace K :=
  ⟨place (embedding v), ⟨v, rfl⟩⟩

/-- A predicate singling out finite places among the absolute values on a number field `K`. -/
def IsFinitePlace [NumberField K] (w : AbsoluteValue K ℝ) : Prop :=
  ∃ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), place (FinitePlace.embedding v) = w

lemma FinitePlace.isFinitePlace [NumberField K] (v : FinitePlace K) : IsFinitePlace v.val := by
  simp [IsFinitePlace, v.prop]

lemma isFinitePlace_iff [NumberField K] (v : AbsoluteValue K ℝ) :
    IsFinitePlace v ↔ ∃ w : FinitePlace K, w.val = v :=
  ⟨fun H ↦ ⟨⟨v, H⟩, rfl⟩, fun ⟨w, hw⟩ ↦ hw ▸ w.isFinitePlace⟩

namespace FinitePlace

variable [NumberField K] [NumberField L]

@[macro_inline]
instance : FunLike (FinitePlace K) K ℝ where
  coe w x := w.1 x
  coe_injective _ _ h := Subtype.ext (AbsoluteValue.ext <| congr_fun h)

instance : MonoidWithZeroHomClass (FinitePlace K) K ℝ where
  map_mul w := w.1.map_mul
  map_one w := w.1.map_one
  map_zero w := w.1.map_zero

instance : NonnegHomClass (FinitePlace K) K ℝ where
  apply_nonneg w := w.1.nonneg

@[simp]
theorem mk_apply (v : HeightOneSpectrum (𝓞 K)) (x : K) : mk v x = ‖embedding v x‖ := rfl

lemma coe_apply (v : FinitePlace K) (x : K) : v x = v.val x := rfl

instance : MulRingNormClass (FinitePlace K) K ℝ where
  map_add_le_add v x y := by simpa [coe_apply] using IsAbsoluteValue.abv_add' x y
  map_neg_eq_map v x := by simp [coe_apply]
  eq_zero_of_map_eq_zero v := by simp

/-- For a finite place `w`, return a maximal ideal `v` such that `w = finite_place v` . -/
noncomputable def maximalIdeal (w : FinitePlace K) : HeightOneSpectrum (𝓞 K) := w.2.choose

@[simp]
theorem mk_maximalIdeal (w : FinitePlace K) : mk (maximalIdeal w) = w := Subtype.ext w.2.choose_spec

@[simp]
theorem norm_embedding_eq (w : FinitePlace K) (x : K) :
    ‖embedding (maximalIdeal w) x‖ = w x := by
  conv_rhs => rw [← mk_maximalIdeal w, mk_apply]

theorem pos_iff {w : FinitePlace K} {x : K} : 0 < w x ↔ x ≠ 0 := w.1.pos_iff

@[simp]
theorem mk_eq_iff {v₁ v₂ : HeightOneSpectrum (𝓞 K)} : mk v₁ = mk v₂ ↔ v₁ = v₂ := by
  refine ⟨?_, fun a ↦ by rw [a]⟩
  contrapose!
  intro h
  rw [DFunLike.ne_iff]
  have ⟨x, hx1, hx2⟩ : ∃ x : 𝓞 K, x ∈ v₁.asIdeal ∧ x ∉ v₂.asIdeal := by
    by_contra! H
    exact h <| HeightOneSpectrum.ext_iff.mpr <| IsMaximal.eq_of_le (isMaximal v₁) IsPrime.ne_top' H
  use x
  simp only [mk_apply]
  rw [← norm_lt_one_iff_mem K] at hx1
  rw [← norm_eq_one_iff_notMem K] at hx2
  linarith

theorem maximalIdeal_mk (v : HeightOneSpectrum (𝓞 K)) : maximalIdeal (mk v) = v := by
  rw [← mk_eq_iff, mk_maximalIdeal]

/-- The equivalence between finite places and maximal ideals. -/
@[simps apply]
noncomputable def equivHeightOneSpectrum :
    FinitePlace K ≃ HeightOneSpectrum (𝓞 K) where
  toFun := maximalIdeal
  invFun := mk
  left_inv := mk_maximalIdeal
  right_inv := maximalIdeal_mk

lemma maximalIdeal_injective : (fun w : FinitePlace K ↦ maximalIdeal w).Injective :=
  equivHeightOneSpectrum.injective

lemma maximalIdeal_inj (w₁ w₂ : FinitePlace K) : maximalIdeal w₁ = maximalIdeal w₂ ↔ w₁ = w₂ :=
  equivHeightOneSpectrum.injective.eq_iff

@[fun_prop]
theorem hasFiniteMulSupport_int {x : 𝓞 K} (h_x_nezero : x ≠ 0) :
    (fun w : FinitePlace K ↦ w x).HasFiniteMulSupport := by
  have (w : FinitePlace K) : w x ≠ 1 ↔ w x < 1 :=
    ne_iff_lt_iff_le.mpr <| norm_embedding_eq w x ▸ norm_le_one K w.maximalIdeal x
  simp_rw [Function.HasFiniteMulSupport, Function.mulSupport, this, ← norm_embedding_eq,
    norm_lt_one_iff_mem, ← Ideal.dvd_span_singleton]
  have h : {v : HeightOneSpectrum (𝓞 K) | v.asIdeal ∣ span {x}}.Finite := by
    apply Ideal.finite_factors
    simp only [Submodule.zero_eq_bot, ne_eq, span_singleton_eq_bot, h_x_nezero, not_false_eq_true]
  have h_inj : Set.InjOn FinitePlace.maximalIdeal {w | w.maximalIdeal.asIdeal ∣ span {x}} :=
    Function.Injective.injOn maximalIdeal_injective
  refine (h.subset ?_).of_finite_image h_inj
  simp only [dvd_span_singleton, Set.image_subset_iff, Set.preimage_ofPred_eq, subset_refl]

@[deprecated (since := "2026-03-03")] alias mulSupport_finite_int := hasFiniteMulSupport_int

@[fun_prop]
theorem hasFiniteMulSupport {x : K} (h_x_nezero : x ≠ 0) :
    (fun w : FinitePlace K ↦ w x).HasFiniteMulSupport := by
  rcases IsFractionRing.div_surjective (𝓞 K) x with ⟨a, b, hb, rfl⟩
  simp_all only [ne_eq, div_eq_zero_iff, FaithfulSMul.algebraMap_eq_zero_iff, not_or, map_div₀]
  obtain ⟨ha, hb⟩ := h_x_nezero
  simp_rw [← RingOfIntegers.coe_eq_algebraMap]
  fun_prop

@[deprecated (since := "2026-03-03")] alias mulSupport_finite := hasFiniteMulSupport

lemma hasFiniteMulSupport_fun_pow_multiplicity {M : Type*} [CommMonoid M] {I : Ideal (𝓞 K)}
    (hI : I ≠ ⊥) (f : Ideal (𝓞 K) → M) :
    (fun v : FinitePlace K ↦ f v.maximalIdeal.asIdeal ^
      multiplicity v.maximalIdeal.asIdeal I
        (v.maximalIdeal.finiteMultiplicity hI)).HasFiniteMulSupport :=
  UniqueFactorizationMonoid.hasFiniteMulSupport_fun_pow_multiplicity _
    (asIdeal_injective.comp maximalIdeal_injective) (fun v ↦ v.maximalIdeal.irreducible) hI

protected
lemma add_le (v : FinitePlace K) (x y : K) :
    v (x + y) ≤ max (v x) (v y) := by
  obtain ⟨w, hw⟩ := v.prop
  have H x : v x = NumberField.HeightOneSpectrum.adicAbv K w x := by
    rw [show v x = v.val x from rfl]
    grind only [place_apply, norm_embedding]
  simpa only [H] using adicAbv_add_le_max K w x y

instance : NonarchimedeanHomClass (FinitePlace K) K ℝ where
  map_add_le_max v a b := FinitePlace.add_le v a b

lemma equivHeightOneSpectrum_symm_apply (v : HeightOneSpectrum (𝓞 K)) (x : K) :
    (equivHeightOneSpectrum.symm v) x = ‖embedding v x‖ := rfl

@[deprecated (since := "2026-03-11")]
alias IsDedekindDomain.HeightOneSpectrum.equivHeightOneSpectrum_symm_apply :=
  equivHeightOneSpectrum_symm_apply
@[deprecated (since := "2026-03-11")]
alias IsDedekindDomain.HeightOneSpectrum.embedding_mul_absNorm := embedding_mul_absNorm

-- TODO: restate in terms of finite places rather than non-trivial prime ideals of the Dedekind
-- domains `𝓞 K` and `𝓞 L` once we have a ramification theory for finite places set up.
-- Note that this will mean `FinitePlace.equivHeightOneSpectrum` no longer appears in the statement.
lemma equivHeightOneSpectrum_symm_apply_algebraMap
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.1.LiesOver v.1] (x : K) :
    FinitePlace.equivHeightOneSpectrum.symm w (algebraMap K L x) =
      FinitePlace.equivHeightOneSpectrum.symm v x ^
        (w.1.ramificationIdx (𝓞 K) * w.1.inertiaDeg (𝓞 K)) := by
  by_cases hx : x = 0
  · rw [hx, map_zero, map_zero, map_zero, zero_pow]
    exact (mul_pos (w.asIdeal.ramificationIdx_pos (𝓞 K)) (w.asIdeal.inertiaDeg_pos (𝓞 K))).ne'
  simp_rw [NumberField.FinitePlace.equivHeightOneSpectrum_symm_apply,
    FinitePlace.norm_embedding, HeightOneSpectrum.adicAbv_def]
  rw [← IsDedekindDomain.HeightOneSpectrum.valuation_liesOver L v, map_pow,
    Ideal.ramificationIdx'_eq_ramificationIdx v.1 w.1 v.ne_bot,
    WithZeroMulInt.toNNReal_neg_apply _ (by simpa), WithZeroMulInt.toNNReal_neg_apply _ (by simpa),
    ← Ideal.absNorm_pow_inertiaDeg v.1 w.1]
  simp only [Nat.cast_pow, NNReal.coe_zpow, ← zpow_natCast, ← zpow_mul]
  grind

lemma finprod_finitePlace_pow_multiplicity {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    ∏ᶠ v : FinitePlace K, v.maximalIdeal.asIdeal ^
      multiplicity v.maximalIdeal.asIdeal I (v.maximalIdeal.finiteMultiplicity hI) = I := by
  conv_rhs => rw [← finprod_heightOneSpectrum_pow_multiplicity hI]
  simp only [← finprod_comp_equiv (equivHeightOneSpectrum (K := K)), equivHeightOneSpectrum_apply]

lemma apply_mul_absNorm_pow_eq_one (v : FinitePlace K) {x : 𝓞 K} (hx : x ≠ 0) :
    v x * v.maximalIdeal.asIdeal.absNorm ^ multiplicity v.maximalIdeal.asIdeal (span {x})
      (v.maximalIdeal.finiteMultiplicity (Ideal.span_singleton_eq_bot.not.2 hx)) = 1 := by
  have hnz : span {x} ≠ ⊥ := mt Submodule.span_singleton_eq_bot.mp hx
  rw [← norm_embedding_eq v x, ← Nat.cast_pow, ← map_pow, ← maxPowDividing_eq_pow_multiplicity hnz]
  exact HeightOneSpectrum.embedding_mul_absNorm K v.maximalIdeal hx

end FinitePlace

section LiesOver

namespace HeightOneSpectrum

variable [NumberField K] [NumberField L]
variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
variable [Algebra (v.adicCompletion K) (w.adicCompletion L)]
    [ContinuousSMul (v.adicCompletion K) (w.adicCompletion L)]
    [IsScalarTower K (v.adicCompletion K) (w.adicCompletion L)]

local notation "Kv" => v.adicCompletion K
local notation "Lw" => w.adicCompletion L

open scoped TensorProduct Valued in
instance : Module.Finite Kv Lw :=
  let Φ : Kv ⊗[K] L →ₗ[Kv] Lw := Algebra.TensorProduct.lift (Algebra.algHom Kv Kv Lw)
    (Algebra.algHom K L Lw) (fun _ _ ↦ mul_comm ..) |>.toLinearMap
  have h_dense : DenseRange Φ := by
    apply (w.denseRange_algebraMap L).mono
    rintro _ ⟨l, rfl⟩
    exact ⟨1 ⊗ₜ l, by simp [Φ, Algebra.algHom]⟩
  .of_surjective Φ (by
    rw [← Set.range_eq_univ, ← Φ.coe_range, ← Φ.range.closed_of_finiteDimensional.closure_eq]
    exact h_dense.closure_range)

end HeightOneSpectrum

end LiesOver

end NumberField
