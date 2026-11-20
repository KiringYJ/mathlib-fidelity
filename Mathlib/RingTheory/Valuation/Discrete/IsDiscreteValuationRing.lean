/-
Copyright (c) 2022 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation

/-!
# Valuations associated to discrete valuation rings

Given a discrete valuation ring `A` with field of fractions `K`, the maximal ideal of `A`
is a height-one prime, and the associated valuation `(maximalIdeal A).valuation K` is
a rank-one discrete valuation on `K`.

## Main Definitions

* `IsDiscreteValuationRing.maximalIdeal`: The maximal ideal of `A` (as an element of
  `HeightOneSpectrum A`).
* `IsDiscreteValuationRing.equivValuationSubring`: The ring isomorphism between a DVR and the
  unit ball in its field of fractions endowed with the adic valuation of the maximal ideal.

## Main Results

* `IsDiscreteValuationRing.isRankOneDiscrete`: Given a DVR `A` and a field `K` satisfying
  `IsFractionRing A K`, the valuation induced on `K` is discrete.
-/

@[expose] public section

namespace IsDiscreteValuationRing

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsDiscreteValuationRing
  IsLocalRing MonoidWithZeroHom Multiplicative Subring Valuation

variable (A K : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Field K]
  [Algebra A K] [IsFractionRing A K]

/-- The maximal ideal of a discrete valuation ring. -/
def maximalIdeal : HeightOneSpectrum A where
  asIdeal := IsLocalRing.maximalIdeal A
  isPrime := Ideal.IsMaximal.isPrime (maximalIdeal.isMaximal A)
  ne_bot := by simpa [ne_eq, ← isField_iff_maximalIdeal_eq] using not_isField A

instance isRankOneDiscrete :
    IsRankOneDiscrete ((maximalIdeal A).valuation K) := by
  have : Nontrivial (valueGroup
      (.ofClass (valuation K (maximalIdeal A)))) := by
    let v := (maximalIdeal A).valuation K
    let π := valuation_exists_uniformizer K (maximalIdeal A) |>.choose
    have hπ : v π = ↑(ofAdd (-1 : ℤ)) :=
      valuation_exists_uniformizer K (maximalIdeal A) |>.choose_spec
    rw [Subgroup.nontrivial_iff_exists_ne_one]
    use Units.mk0 (v π) (by simp [hπ])
    constructor
    · apply mem_valueGroup
      use π
      simp [v]
    · intro h
      have hval : v π = 1 := congrArg Units.val h
      rw [hπ, ← WithZero.coe_one, WithZero.coe_inj, ofAdd_eq_one] at hval
      exact Int.neg_ne_zero.mpr one_ne_zero hval
  infer_instance

variable {A K}

open scoped WithZero

theorem exists_lift_of_le_one {x : K} (H : ((maximalIdeal A).valuation K) x ≤ (1 : ℤᵐ⁰)) :
    ∃ a : A, algebraMap A K a = x := by
  obtain ⟨π, hπ⟩ := exists_irreducible A
  obtain ⟨a, b, hb, h_frac⟩ := IsFractionRing.div_surjective A x
  by_cases ha : a = 0
  · rw [← h_frac]
    use 0
    rw [ha, map_zero, zero_div]
  · rw [← h_frac] at H
    obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible ha hπ
    obtain ⟨m, w, rfl⟩ := eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero hb) hπ
    have hbK := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (K := K) hb
    have hden := ((maximalIdeal A).valuation K).pos_iff.mpr hbK
    rw [map_div₀, div_le_iff₀ hden, one_mul] at H
    have hu := Integers.one_of_isUnit' u.isUnit (valuation_le_one (K := K) (maximalIdeal A))
    have hw := Integers.one_of_isUnit' w.isUnit (valuation_le_one (K := K) (maximalIdeal A))
    simp only [valuation_of_algebraMap, map_mul, map_pow] at H
    rw [← valuation_of_algebraMap (K := K) _ (u : A),
      ← valuation_of_algebraMap (K := K) _ (w : A), hu, hw, one_mul, one_mul] at H
    have h_mn : m ≤ n := by
      have v_π_lt_one := (intValuation_lt_one_iff_dvd (maximalIdeal A) π).mpr
          (dvd_of_eq ((irreducible_iff_uniformizer _).mp hπ))
      have v_π_pos := zero_lt_iff.mpr ((maximalIdeal A).intValuation_ne_zero π hπ.ne_zero)
      exact (pow_le_pow_iff_right_of_lt_one₀ v_π_pos v_π_lt_one).mp H
    use u * π ^ (n - m) * w.2
    rw [← h_frac, eq_div_iff, ← map_mul]
    congr 1
    rw [mul_assoc _ (w.2) _, ← mul_assoc (w.2) _, w.inv_val, one_mul,
      mul_assoc, pow_sub_mul_pow π h_mn]

lemma mker_valuation_eq_isUnitSubmonoid :
    MonoidHom.mker ((IsDiscreteValuationRing.maximalIdeal A).valuation K) =
    (IsUnit.submonoid A).map (algebraMap A K) := by
  ext a
  simp only [MonoidHom.mem_mker, Submonoid.mem_map]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨b, rfl⟩ := IsDiscreteValuationRing.exists_lift_of_le_one h.le
    rw [valuation_eq_one_iff_notMem] at h
    simp only [IsDiscreteValuationRing.maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      not_not] at h
    use b, h
  · obtain ⟨x, h, rfl⟩ := h
    simpa [IsDiscreteValuationRing.maximalIdeal] using! h

theorem associated_of_valuation_eq (x y : K)
    (h : ((maximalIdeal A).valuation K) x =
    ((maximalIdeal A).valuation K) y) : ∃ u : Aˣ, u • x = y := by
  by_cases hx : x = 0
  · rw [eq_comm] at h
    simp_all
  by_cases hy : y = 0
  · simp_all
  have : (y / x) ∈ MonoidHom.mker (((maximalIdeal A).valuation K)) := by simp_all
  rw [mker_valuation_eq_isUnitSubmonoid] at this
  obtain ⟨u, h⟩ := this
  use IsUnit.unit h.1
  simp only [Units.smul_def, Algebra.smul_def, IsUnit.unit_spec h.1, h.2]
  field_simp

theorem map_algebraMap_eq_valuationSubring : Subring.map (algebraMap A K) ⊤ =
    ((maximalIdeal A).valuation K).valuationSubring.toSubring := by
  ext
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨_, _, rfl⟩ := Subring.mem_map.mp h
    apply valuation_le_one
  · obtain ⟨y, rfl⟩ := exists_lift_of_le_one h
    rw [Subring.mem_map]
    exact ⟨y, mem_top _, rfl⟩

/-- The ring isomorphism between a DVR `A` and the valuation subring of a field of fractions
  of `A` endowed with the adic valuation of the maximal ideal. -/
noncomputable def equivValuationSubring :
    A ≃+* ((maximalIdeal A).valuation K).valuationSubring :=
  (topEquiv.symm.trans (equivMapOfInjective ⊤ (algebraMap A K)
    (IsFractionRing.injective A _))).trans
      (RingEquiv.subringCongr map_algebraMap_eq_valuationSubring)

lemma intValuation_maximalIdeal (x : A) :
    (maximalIdeal A).intValuation x =
      ENat.recTopCoe 0 (fun n ↦ WithZero.exp (-(n : ℤ))) (addVal A x) := by
  by_cases hx : x = 0
  · simp [hx]
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible A
  obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible hx hϖ
  have : (maximalIdeal A).intValuation ↑u = 1 := by simp [maximalIdeal]
  simp [(maximalIdeal A).intValuation_singleton hϖ.ne_zero
    hϖ.maximalIdeal_eq, hϖ, this]

end IsDiscreteValuationRing

end
