/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Derivatives of `x ^ m`, `m : ℤ`

In this file we prove theorems about (iterated) derivatives of `x ^ m`, `m : ℤ`.

For a more detailed overview of one-dimensional derivatives in mathlib, see the module docstring of
`Mathlib/Analysis/Calculus/Deriv/Basic.lean`.

## Keywords

derivative, power
-/

public section

universe u v w

open Set
open scoped Nat Topology

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {x : 𝕜}
variable {s : Set 𝕜}
variable {m : ℤ}

/-! ### Derivative of `x ↦ x^m` for `m : ℤ` -/

/-- The exact domain of an integer power is open: it is the unit locus for negative exponents
and the whole field for nonnegative exponents. -/
lemma isOpen_zpow_domain (m : ℤ) : IsOpen {x : 𝕜 | m < 0 → IsUnit x} := by
  by_cases hm : m < 0
  · simpa only [hm, true_implies] using (Units.isOpen : IsOpen {x : 𝕜 | IsUnit x})
  · simp only [hm, false_implies, Set.ofPred_true]
    exact isOpen_univ

/-- The derivative of an integer power on its exact domain. At exponent zero the derivative
is zero, without evaluating the negative power `x ^ (-1)` at the origin. -/
theorem hasStrictDerivAt_zpow (m : ℤ) (x : {x : 𝕜 // m < 0 → IsUnit x}) :
    HasStrictDerivAt (fun y : {y : 𝕜 // m < 0 → IsUnit y} ↦ Checked.zpow y.val m y.property)
      (if hm : m = 0 then 0 else (m : 𝕜) * Checked.zpow x.val (m - 1)
        (fun h ↦ x.property (by omega))) x Subtype.val := by
  cases m with
  | ofNat n =>
    have hp : HasStrictDerivAt
        (fun y : {y : 𝕜 // (n : ℤ) < 0 → IsUnit y} ↦ y.val ^ n)
        ((n : 𝕜) * x.val ^ (n - 1)) x Subtype.val := by
      exact (hasStrictDerivAt_pow n x.val).hasStrictFDerivAt.comp_tendsto Subtype.val
        (continuous_subtype_val.continuousAt.tendsto.prodMap_nhds
          continuous_subtype_val.continuousAt.tendsto)
    cases n with
    | zero => simpa [Checked.zpow] using hp
    | succ n =>
      have hm : Int.ofNat (n + 1) ≠ 0 := by
        change ((n + 1 : ℕ) : ℤ) ≠ 0
        exact_mod_cast Nat.succ_ne_zero n
      have he : Int.ofNat (n + 1) - 1 = Int.ofNat n := by
        change ((n + 1 : ℕ) : ℤ) - 1 = (n : ℤ)
        rw [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
      have hpow (r : ℤ) (hr : r = Int.ofNat n) (hu : r < 0 → IsUnit x.val) :
          Checked.zpow x.val r hu = x.val ^ n := by
        subst r
        rfl
      have hcast : (Int.ofNat (n + 1) : 𝕜) = ((n + 1 : ℕ) : 𝕜) := Int.cast_natCast _
      rw [dite_eq_right hm, hpow _ he, hcast]
      exact hp
  | negSucc n =>
    let D := {y : 𝕜 // Int.negSucc n < 0 → IsUnit y}
    let u : D → 𝕜ˣ := fun y ↦ (y.property (Int.negSucc_lt_zero n)).unit ^ (n + 1)
    have hp : HasStrictDerivAt (fun y : D ↦ y.val ^ (n + 1))
        (((n + 1 : ℕ) : 𝕜) * x.val ^ n) x Subtype.val := by
      have hp := (hasStrictDerivAt_pow (n + 1) x.val).hasStrictFDerivAt.comp_tendsto Subtype.val
          (continuous_subtype_val.continuousAt.tendsto.prodMap_nhds
            continuous_subtype_val.continuousAt.tendsto)
      rw [Nat.add_sub_cancel] at hp
      exact hp
    have hunit : HasStrictFDerivAt ((fun z : 𝕜ˣ ↦ (z : 𝕜)) ∘ u)
        (ContinuousLinearMap.toSpanSingleton 𝕜 (((n + 1 : ℕ) : 𝕜) * x.val ^ n))
        x Subtype.val := by
      simpa only [u, Function.comp_def, Units.val_pow_eq_pow_val, IsUnit.unit_spec]
        using hp.hasStrictFDerivAt
    have hi := (hasStrictDerivAt_inv (u x)).hasStrictFDerivAt.comp x hunit
      continuous_subtype_val.continuousAt Units.isOpenEmbedding_val.isEmbedding
    have hd := hi.hasStrictDerivAt
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
      smul_eq_mul] at hd
    convert hd using 1
    · funext y
      simp only [Checked.zpow, zpow_negSucc, u]
    · have hm : Int.negSucc n ≠ 0 := by omega
      have he : Int.negSucc n - 1 = Int.negSucc (n + 1) := by omega
      have hx : IsUnit x.val := x.property (Int.negSucc_lt_zero n)
      simp only [dite_eq_right hm, he, zpow_negSucc₀, u, Units.val_inv_eq_inv_val₀,
        Units.val_pow_eq_pow_val, IsUnit.unit_spec, Int.cast_negSucc]
      field_simp
      simp only [pow_succ]
      ring

theorem hasDerivAt_zpow (m : ℤ) (x : {x : 𝕜 // m < 0 → IsUnit x}) :
    HasDerivAt (fun y : {y : 𝕜 // m < 0 → IsUnit y} ↦ Checked.zpow y.val m y.property)
      (if hm : m = 0 then 0 else (m : 𝕜) * Checked.zpow x.val (m - 1)
        (fun h ↦ x.property (by omega))) x Subtype.val :=
  (hasStrictDerivAt_zpow m x).hasStrictFDerivAt.hasFDerivAt

/-- The chain rule for integer powers, restricted to the preimage of the power's domain. -/
theorem HasDerivAt.zpow {D 𝕜' : Type*} [TopologicalSpace D] [NontriviallyNormedField 𝕜']
    [NormedAlgebra 𝕜 𝕜'] {f : D → 𝕜'} {f' : 𝕜'} {x : D} {coord : D → 𝕜}
    (hf : HasDerivAt f f' x coord) (m : ℤ) (hx : m < 0 → IsUnit (f x))
    (hcoord : ContinuousAt coord x := by exact continuousAt_id) :
    HasDerivAt (fun y : {y : D // m < 0 → IsUnit (f y)} ↦ Checked.zpow (f y.val) m y.property)
      ((if hm : m = 0 then 0 else (m : 𝕜') * Checked.zpow (f x) (m - 1)
        (fun h ↦ hx (by omega))) * f') ⟨x, hx⟩ (coord ∘ Subtype.val) := by
  let q : {y : D // m < 0 → IsUnit (f y)} → {z : 𝕜' // m < 0 → IsUnit z} :=
    fun y ↦ ⟨f y.val, y.property⟩
  have hq : HasFDerivAt (Subtype.val ∘ q) (ContinuousLinearMap.toSpanSingleton 𝕜 f')
      ⟨x, hx⟩ (coord ∘ Subtype.val) :=
    hf.hasFDerivAt.comp_tendsto Subtype.val
      (continuous_subtype_val.continuousAt.tendsto.prodMap (Filter.tendsto_pure_pure ..))
  have hc := ((hasDerivAt_zpow m (q ⟨x, hx⟩)).hasFDerivAt.restrictScalars 𝕜).comp ⟨x, hx⟩ hq
    (hcoord.comp continuous_subtype_val.continuousAt) Topology.IsEmbedding.subtypeVal
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.toSpanSingleton_apply, one_smul, smul_eq_mul, mul_comm f', q,
    Function.comp_def]
    using hc.hasDerivAt

theorem hasDerivWithinAt_zpow (m : ℤ) (x : {x : 𝕜 // m < 0 → IsUnit x})
    (s : Set {x : 𝕜 // m < 0 → IsUnit x}) :
    HasDerivWithinAt (fun y : {y : 𝕜 // m < 0 → IsUnit y} ↦ Checked.zpow y.val m y.property)
      (if hm : m = 0 then 0 else (m : 𝕜) * Checked.zpow x.val (m - 1)
        (fun h ↦ x.property (by omega))) s x Subtype.val :=
  (hasDerivAt_zpow m x).hasFDerivAt.hasFDerivWithinAt

theorem differentiableAt_zpow (m : ℤ) (x : {x : 𝕜 // m < 0 → IsUnit x}) :
    DifferentiableAt 𝕜
      (fun y : {y : 𝕜 // m < 0 → IsUnit y} ↦ Checked.zpow y.val m y.property) x Subtype.val :=
  (hasDerivAt_zpow m x).differentiableAt

theorem differentiableWithinAt_zpow (m : ℤ) (x : {x : 𝕜 // m < 0 → IsUnit x})
    (s : Set {x : 𝕜 // m < 0 → IsUnit x}) :
    DifferentiableWithinAt 𝕜
      (fun y : {y : 𝕜 // m < 0 → IsUnit y} ↦ Checked.zpow y.val m y.property) s x Subtype.val :=
  (hasDerivWithinAt_zpow m x s).differentiableWithinAt

theorem differentiableOn_zpow (m : ℤ) (s : Set {x : 𝕜 // m < 0 → IsUnit x}) :
    DifferentiableOn 𝕜
      (fun y : {y : 𝕜 // m < 0 → IsUnit y} ↦ Checked.zpow y.val m y.property) s Subtype.val :=
  fun x _ ↦ differentiableWithinAt_zpow m x s

theorem deriv_zpow (m : ℤ) (x : {x : 𝕜 // m < 0 → IsUnit x}) :
    deriv (fun y : {y : 𝕜 // m < 0 → IsUnit y} ↦ Checked.zpow y.val m y.property) x Subtype.val =
      if hm : m = 0 then 0 else (m : 𝕜) * Checked.zpow x.val (m - 1)
        (fun h ↦ x.property (by omega)) :=
  (hasDerivAt_zpow m x).deriv (isOpen_zpow_domain m).isOpenEmbedding_subtypeVal

@[simp]
theorem deriv_zpow' (m : ℤ) :
    (fun x : {x : 𝕜 // m < 0 → IsUnit x} ↦
      deriv (fun y : {y : 𝕜 // m < 0 → IsUnit y} ↦ Checked.zpow y.val m y.property)
        x Subtype.val) =
      fun x ↦ if hm : m = 0 then 0 else (m : 𝕜) * Checked.zpow x.val (m - 1)
        (fun h ↦ x.property (by omega)) :=
  funext (deriv_zpow m)

theorem derivWithin_zpow (m : ℤ) (x : {x : 𝕜 // m < 0 → IsUnit x})
    {s : Set {x : 𝕜 // m < 0 → IsUnit x}}
    (hxs : UniqueDiffWithinAt 𝕜 (Subtype.val '' s) x.val) :
    derivWithin (fun y : {y : 𝕜 // m < 0 → IsUnit y} ↦ Checked.zpow y.val m y.property)
      s x Subtype.val =
      if hm : m = 0 then 0 else (m : 𝕜) * Checked.zpow x.val (m - 1)
        (fun h ↦ x.property (by omega)) :=
  (hasDerivWithinAt_zpow m x s).derivWithin_of_isEmbedding
    Topology.IsEmbedding.subtypeVal hxs

private lemma fallingProduct_succ (z : 𝕜) (k : ℕ) :
    (∏ i ∈ Finset.range (k + 1), (z - i)) =
      z * ∏ i ∈ Finset.range k, (z - 1 - i) := by
  rw [Finset.prod_range_succ']
  simp only [Nat.cast_zero, sub_zero]
  rw [mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  push_cast
  ring

/-- Every iterated derivative of a natural power exists on the whole field, including at zero.
The natural exponent in the formula never requires an inverse. -/
theorem hasIteratedDerivAt_pow (n : ℕ) (x : 𝕜) (k : ℕ) :
    HasIteratedDerivAt k (fun y : 𝕜 ↦ y ^ n)
      ((∏ i ∈ Finset.range k, ((n : 𝕜) - i)) * x ^ (n - k)) x := by
  induction k generalizing n with
  | zero => simp only [HasIteratedDerivAt.zero, Finset.prod_range_zero, one_mul, Nat.sub_zero]
  | succ k ih =>
    refine ⟨fun y ↦ (n : 𝕜) * y ^ (n - 1), hasDerivAt_pow n x,
      Or.inr (Filter.Eventually.of_forall fun y ↦ hasDerivAt_pow n y), ?_⟩
    have hn := (ih (n - 1)).const_smul (n : 𝕜)
    simp only [smul_eq_mul] at hn
    convert hn using 1
    have he : n - (k + 1) = (n - 1) - k := by omega
    rw [he, fallingProduct_succ]
    cases n with
    | zero => simp
    | succ n => simp only [Nat.succ_sub_one, Nat.cast_succ, add_sub_cancel_right, mul_assoc]

private lemma hasDerivAt_units_zpow (m : ℤ) (x : 𝕜ˣ) :
    HasDerivAt (fun y : 𝕜ˣ ↦ (↑(y ^ m) : 𝕜))
      ((m : 𝕜) * (↑(x ^ (m - 1)) : 𝕜)) x Units.val := by
  let q : 𝕜ˣ → {y : 𝕜 // m < 0 → IsUnit y} := fun y ↦ ⟨y, fun _ ↦ y.isUnit⟩
  have hq : Continuous q := Units.continuous_val.subtype_mk _
  have hp : HasDerivAt
      ((fun y : {y : 𝕜 // m < 0 → IsUnit y} ↦ Checked.zpow y.val m y.property) ∘ q)
      (if hm : m = 0 then 0 else (m : 𝕜) * Checked.zpow (q x).val (m - 1)
        (fun h ↦ (q x).property (by omega))) x (Subtype.val ∘ q) :=
    (hasDerivAt_zpow m (q x)).hasFDerivAt.comp_tendsto q
      (hq.continuousAt.tendsto.prodMap (Filter.tendsto_pure_pure ..))
  have hu (y : 𝕜ˣ) : y.isUnit.unit = y := Units.ext y.isUnit.unit_spec
  have hpow (y : 𝕜ˣ) (k : ℤ) :
      Checked.zpow (y : 𝕜) k (fun _ ↦ y.isUnit) = (↑(y ^ k) : 𝕜) := by
    rw [y.isUnit.zpow_eq_val_unit_zpow, hu]
  have hfun : ((fun y : {y : 𝕜 // m < 0 → IsUnit y} ↦ Checked.zpow y.val m y.property) ∘ q) =
      (fun y : 𝕜ˣ ↦ (↑(y ^ m) : 𝕜)) := funext fun y ↦ hpow y m
  rw [hfun] at hp
  by_cases hm : m = 0
  · subst m
    rw [dite_eq_left rfl] at hp
    rw [Int.cast_zero, zero_mul]
    exact hp
  · change HasDerivAt (fun y : 𝕜ˣ ↦ (↑(y ^ m) : 𝕜))
      (if hm : m = 0 then 0 else (m : 𝕜) * Checked.zpow (x : 𝕜) (m - 1)
        (fun _ ↦ x.isUnit)) x Units.val at hp
    rw [dite_eq_right hm, hpow] at hp
    exact hp

private lemma hasIteratedDerivAt_units_zpow (m : ℤ) (x : 𝕜ˣ) (k : ℕ) :
    HasIteratedDerivAt k (fun y : 𝕜ˣ ↦ (↑(y ^ m) : 𝕜))
      ((∏ i ∈ Finset.range k, ((m : 𝕜) - i)) * (↑(x ^ (m - k)) : 𝕜)) x Units.val := by
  induction k generalizing m with
  | zero => simp only [HasIteratedDerivAt.zero, Finset.prod_range_zero, one_mul,
      Nat.cast_zero, sub_zero]
  | succ k ih =>
    refine ⟨fun y ↦ (m : 𝕜) * (↑(y ^ (m - 1)) : 𝕜), hasDerivAt_units_zpow m x,
      Or.inr (Filter.Eventually.of_forall fun y ↦ hasDerivAt_units_zpow m y), ?_⟩
    have hm := (ih (m - 1)).const_smul (m : 𝕜)
    simp only [smul_eq_mul] at hm
    convert hm using 1
    have he : m - (k + 1 : ℕ) = m - 1 - k := by omega
    rw [he, fallingProduct_succ]
    simp only [Int.cast_sub, Int.cast_one, mul_assoc]

/-- Integer powers have iterated derivatives on their exact exponent-dependent domain.
The polynomial exhaustion branch is evaluated before any potentially negative power. -/
theorem hasIteratedDerivAt_zpow (m : ℤ) (x : {x : 𝕜 // m < 0 → IsUnit x}) (k : ℕ) :
    HasIteratedDerivAt k
      (fun y : {y : 𝕜 // m < 0 → IsUnit y} ↦ Checked.zpow y.val m y.property)
      (if hpol : 0 ≤ m ∧ m < (k : ℤ) then 0 else
        (∏ i ∈ Finset.range k, ((m : 𝕜) - i)) *
          Checked.zpow x.val (m - k) (fun h ↦ x.property (by omega))) x Subtype.val := by
  by_cases hm : 0 ≤ m
  · lift m to ℕ using hm
    have hp := (hasIteratedDerivAt_pow m x.val k).comp_domain
      (g := Subtype.val) continuous_subtype_val
    by_cases hmk : m < k
    · have hpol : 0 ≤ (m : ℤ) ∧ (m : ℤ) < k := by omega
      have hzero : (∏ i ∈ Finset.range k, ((m : 𝕜) - i)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_range.mpr hmk) (sub_self _)
      simpa only [Function.comp_def, id_eq, zpow_natCast₀, Int.cast_natCast,
        dite_eq_left hpol, hzero, zero_mul] using hp
    · have hpol : ¬(0 ≤ (m : ℤ) ∧ (m : ℤ) < k) := by omega
      have he : (m : ℤ) - k = ((m - k : ℕ) : ℤ) := by omega
      simpa only [Function.comp_def, id_eq, zpow_natCast₀, Int.cast_natCast,
        dite_eq_right hpol, he] using hp
  · have hm' : m < 0 := by omega
    let u : {y : 𝕜 // m < 0 → IsUnit y} → 𝕜ˣ := fun y ↦ (y.property hm').unit
    have hu : Continuous u := Units.isOpenEmbedding_val.isEmbedding.isInducing.continuous_iff.mpr
      (by simpa only [Function.comp_def, u, IsUnit.unit_spec] using continuous_subtype_val)
    have hp := (hasIteratedDerivAt_units_zpow m (u x) k).comp_domain (g := u) hu
    have hpol : ¬(0 ≤ m ∧ m < (k : ℤ)) := by omega
    rw [dite_eq_right hpol]
    convert hp using 1
    · funext y
      exact (y.property hm').zpow_eq_val_unit_zpow _
    · rw [(x.property hm').zpow_eq_val_unit_zpow]
    · funext y
      exact (y.property hm').unit_spec.symm

private lemma fallingProduct_neg_one (k : ℕ) :
    (∏ i ∈ Finset.range k, ((-1 : 𝕜) - i)) = (-1) ^ k * k ! := by
  simp only [← neg_add', Finset.prod_neg, ← Finset.prod_Ico_id_eq_factorial,
    Finset.prod_Ico_eq_prod_range]
  simp

/-- The iterated derivatives of inversion are specified on the group of units. -/
theorem hasIteratedDerivAt_inv (k : ℕ) (x : 𝕜ˣ) :
    HasIteratedDerivAt k (fun y : 𝕜ˣ ↦ (↑y⁻¹ : 𝕜))
      ((-1) ^ k * k ! * (↑(x ^ (-1 - (k : ℤ))) : 𝕜)) x Units.val := by
  simpa only [zpow_neg_one, Int.cast_neg, Int.cast_one, fallingProduct_neg_one] using
    hasIteratedDerivAt_units_zpow (-1) x k

private lemma hasDerivAt_affine_units_zpow (c d : 𝕜) (m : ℤ)
    (x : {x : 𝕜 // IsUnit (c * x + d)}) :
    HasDerivAt (fun y : {y : 𝕜 // IsUnit (c * y + d)} ↦
      (↑(y.property.unit ^ m) : 𝕜))
      (c * (m : 𝕜) * (↑(x.property.unit ^ (m - 1)) : 𝕜)) x Subtype.val := by
  let u : {y : 𝕜 // IsUnit (c * y + d)} → 𝕜ˣ := fun y ↦ y.property.unit
  have hlin : HasDerivAt (fun y : 𝕜 ↦ c * y + d) c x.val := by
    have h := ((hasDerivAt_id x.val).const_mul c).add_const d
    rw [mul_one] at h
    exact h
  have hl : HasDerivAt (fun y : {y : 𝕜 // IsUnit (c * y + d)} ↦ c * y.val + d)
      c x Subtype.val := by
    exact hlin.hasFDerivAt.comp_tendsto Subtype.val
      (continuous_subtype_val.continuousAt.tendsto.prodMap (Filter.tendsto_pure_pure ..))
  have hc := (hasDerivAt_units_zpow m (u x)).hasFDerivAt.comp x
    (f := u) (by simpa only [u, Function.comp_def, IsUnit.unit_spec] using hl.hasFDerivAt)
    continuous_subtype_val.continuousAt Units.isOpenEmbedding_val.isEmbedding
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
    one_mul, smul_eq_mul, mul_assoc, u, Function.comp_def] using hc.hasDerivAt

private lemma hasIteratedDerivAt_affine_units_zpow (c d : 𝕜) (m : ℤ)
    (x : {x : 𝕜 // IsUnit (c * x + d)}) (k : ℕ) :
    HasIteratedDerivAt k (fun y : {y : 𝕜 // IsUnit (c * y + d)} ↦
      (↑(y.property.unit ^ m) : 𝕜))
      (c ^ k * (∏ i ∈ Finset.range k, ((m : 𝕜) - i)) *
        (↑(x.property.unit ^ (m - k)) : 𝕜)) x Subtype.val := by
  induction k generalizing m with
  | zero => simp only [HasIteratedDerivAt.zero, pow_zero, Finset.prod_range_zero,
      one_mul, Nat.cast_zero, sub_zero]
  | succ k ih =>
    refine ⟨fun y ↦ (c * (m : 𝕜)) * (↑(y.property.unit ^ (m - 1)) : 𝕜),
      hasDerivAt_affine_units_zpow c d m x,
      Or.inr (Filter.Eventually.of_forall fun y ↦ hasDerivAt_affine_units_zpow c d m y), ?_⟩
    have hm := (ih (m - 1)).const_smul (c * (m : 𝕜))
    simp only [smul_eq_mul] at hm
    convert hm using 1
    have he : m - (k + 1 : ℕ) = m - 1 - k := by omega
    rw [he, fallingProduct_succ, pow_succ]
    simp only [Int.cast_sub, Int.cast_one]
    ring

/-- Iterated derivatives of an inverse affine function on its exact invertibility locus.
No nonzero condition on the slope is needed, and no reciprocal of the slope is formed. -/
theorem hasIteratedDerivAt_inv_linear (k : ℕ) (c d : 𝕜)
    (x : {x : 𝕜 // IsUnit (c * x + d)}) :
    HasIteratedDerivAt k
      (fun y : {y : 𝕜 // IsUnit (c * y + d)} ↦ Checked.inv (c * y.val + d) y.property)
      ((-1) ^ k * k ! * c ^ k *
        Checked.zpow (c * x.val + d) (-1 - (k : ℤ)) (fun _ ↦ x.property)) x Subtype.val := by
  have hp := hasIteratedDerivAt_affine_units_zpow c d (-1) x k
  simp only [zpow_neg_one, Int.cast_neg, Int.cast_one,
    fallingProduct_neg_one] at hp
  convert hp using 1
  · rfl
  · rw [x.property.zpow_eq_val_unit_zpow]
    ring

theorem hasIteratedDerivAt_inv_linear_sub (k : ℕ) (c d : 𝕜)
    (x : {x : 𝕜 // IsUnit (c * x - d)}) :
    HasIteratedDerivAt k
      (fun y : {y : 𝕜 // IsUnit (c * y - d)} ↦ Checked.inv (c * y.val - d) y.property)
      ((-1) ^ k * k ! * c ^ k *
        Checked.zpow (c * x.val - d) (-1 - (k : ℤ)) (fun _ ↦ x.property)) x Subtype.val := by
  let q : {y : 𝕜 // IsUnit (c * y - d)} → {y : 𝕜 // IsUnit (c * y + -d)} :=
    fun y ↦ ⟨y.val, by simpa only [sub_eq_add_neg] using y.property⟩
  have hp := (hasIteratedDerivAt_inv_linear k c (-d) (q x)).comp_domain
    (g := q) (continuous_subtype_val.subtype_mk _)
  simpa only [q, Function.comp_def, sub_eq_add_neg] using hp

variable {f : E → 𝕜} {t : Set E} {a : E}

@[fun_prop]
theorem DifferentiableWithinAt.zpow (hf : DifferentiableWithinAt 𝕜 f t a)
    (h : m < 0 → IsUnit (f a)) :
    DifferentiableWithinAt 𝕜
      (fun y : {y : E // m < 0 → IsUnit (f y)} ↦ Checked.zpow (f y.val) m y.property)
      (Subtype.val ⁻¹' t) ⟨a, h⟩ Subtype.val := by
  let D := {y : E // m < 0 → IsUnit (f y)}
  let q : D → {y : 𝕜 // m < 0 → IsUnit y} := fun y ↦ ⟨f y.val, y.property⟩
  have hcoords : HasFDerivWithinAt (Subtype.val ∘ q) (fderivWithin 𝕜 f t a)
      (Subtype.val ⁻¹' t) ⟨a, h⟩ Subtype.val := by
    exact hf.hasFDerivWithinAt.comp_tendsto Subtype.val
      ((continuous_subtype_val.continuousWithinAt.tendsto_nhdsWithin
        (fun y hy ↦ hy)).prodMap (Filter.tendsto_pure_pure ..))
  have hc := (hasDerivAt_zpow m (q ⟨a, h⟩)).hasFDerivAt.comp_hasFDerivWithinAt ⟨a, h⟩ hcoords
    continuous_subtype_val.continuousWithinAt Topology.IsEmbedding.subtypeVal
  exact hc.differentiableWithinAt

@[fun_prop]
theorem DifferentiableAt.zpow (hf : DifferentiableAt 𝕜 f a) (h : m < 0 → IsUnit (f a)) :
    DifferentiableAt 𝕜
      (fun y : {y : E // m < 0 → IsUnit (f y)} ↦ Checked.zpow (f y.val) m y.property)
      ⟨a, h⟩ Subtype.val := by
  let D := {y : E // m < 0 → IsUnit (f y)}
  let q : D → {y : 𝕜 // m < 0 → IsUnit y} := fun y ↦ ⟨f y.val, y.property⟩
  have hcoords : HasFDerivAt (Subtype.val ∘ q) (fderiv 𝕜 f a) ⟨a, h⟩ Subtype.val := by
    exact hf.hasFDerivAt.comp_tendsto Subtype.val
      (continuous_subtype_val.continuousAt.tendsto.prodMap (Filter.tendsto_pure_pure ..))
  exact ((hasDerivAt_zpow m (q ⟨a, h⟩)).hasFDerivAt.comp ⟨a, h⟩ hcoords
    continuous_subtype_val.continuousAt Topology.IsEmbedding.subtypeVal).differentiableAt

@[fun_prop]
theorem DifferentiableOn.zpow (hf : DifferentiableOn 𝕜 f t) :
    DifferentiableOn 𝕜
      (fun y : {y : E // m < 0 → IsUnit (f y)} ↦ Checked.zpow (f y.val) m y.property)
      (Subtype.val ⁻¹' t) Subtype.val :=
  fun y hy ↦ (hf y.val hy).zpow y.property

@[fun_prop]
theorem Differentiable.zpow (hf : Differentiable 𝕜 f) :
    Differentiable 𝕜
      (fun y : {y : E // m < 0 → IsUnit (f y)} ↦ Checked.zpow (f y.val) m y.property)
      Subtype.val :=
  fun y ↦ (hf y.val).zpow y.property

/-- A nonnegative integer power preserves differentiability at zeros on the original domain. -/
theorem DifferentiableWithinAt.zpow_nonneg (hf : DifferentiableWithinAt 𝕜 f t a)
    (hm : 0 ≤ m) :
    DifferentiableWithinAt 𝕜
      (fun y ↦ Checked.zpow (f y) m (fun h ↦ (not_lt_of_ge hm h).elim)) t a := by
  lift m to ℕ using hm
  simpa only [zpow_natCast₀, Pi.pow_def] using hf.pow m

/-- A nonnegative integer power preserves differentiability at zeros on the original domain. -/
theorem DifferentiableAt.zpow_nonneg (hf : DifferentiableAt 𝕜 f a) (hm : 0 ≤ m) :
    DifferentiableAt 𝕜
      (fun y ↦ Checked.zpow (f y) m (fun h ↦ (not_lt_of_ge hm h).elim)) a := by
  lift m to ℕ using hm
  simpa only [zpow_natCast₀, Pi.pow_def] using hf.pow m

/-- A nonnegative integer power is differentiable wherever the original function is. -/
theorem DifferentiableOn.zpow_nonneg (hf : DifferentiableOn 𝕜 f t) (hm : 0 ≤ m) :
    DifferentiableOn 𝕜
      (fun y ↦ Checked.zpow (f y) m (fun h ↦ (not_lt_of_ge hm h).elim)) t :=
  fun y hy ↦ (hf y hy).zpow_nonneg hm

/-- A nonnegative integer power preserves differentiability on the full domain. -/
theorem Differentiable.zpow_nonneg (hf : Differentiable 𝕜 f) (hm : 0 ≤ m) :
    Differentiable 𝕜
      (fun y ↦ Checked.zpow (f y) m (fun h ↦ (not_lt_of_ge hm h).elim)) :=
  fun y ↦ (hf y).zpow_nonneg hm
