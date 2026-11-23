/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, David Loeffler
-/
module

public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.NumberTheory.ModularForms.SlashInvariantForms
public import Mathlib.RingTheory.EuclideanDomain
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

/-!
# Eisenstein Series

## Main definitions

* We define Eisenstein series of level `Γ(N)` for any `N : ℕ` and weight `k : ℤ` as the infinite sum
  `∑' v : (Fin 2 → ℤ), (1 / (v 0 * z + v 1) ^ k)`, where `z : ℍ` and `v` ranges over all pairs of
  coprime integers congruent to a fixed pair `(a, b)` modulo `N`. Note that by using `(Fin 2 → ℤ)`
  instead of `ℤ × ℤ` we can state all of the required equivalences using matrices and vectors, which
  makes working with them more convenient.

* We show that they define a slash invariant form of level `Γ(N)` and weight `k`.

## References
* [F. Diamond and J. Shurman, *A First Course in Modular Forms*][diamondshurman2005]
-/

@[expose] public section

noncomputable section

open ModularForm UpperHalfPlane Complex Matrix CongruenceSubgroup Set

open scoped MatrixGroups

namespace EisensteinSeries

variable (N r : ℕ) (a : Fin 2 → ZMod N)

section gammaSet_def

/-- The set of pairs of integers congruent to `a` mod `N` and with `gcd` equal to `r`. -/
def gammaSet := {v : Fin 2 → ℤ | (↑) ∘ v = a ∧ (v 0).gcd (v 1) = r}

open scoped Function in -- required for scoped `on` notation
lemma pairwise_disjoint_gammaSet : Pairwise (Disjoint on gammaSet N r) := by
  refine fun u v huv ↦ ?_
  contrapose huv
  obtain ⟨f, hf⟩ := Set.not_disjoint_iff.mp huv
  exact hf.1.1.symm.trans hf.2.1

/-- For level `N = 1`, the gamma sets are all equal. -/
lemma gammaSet_one_const (a a' : Fin 2 → ZMod 1) : gammaSet 1 r a = gammaSet 1 r a' :=
  congr_arg _ (Subsingleton.elim _ _)

/-- For level `N = 1`, the gamma sets simplify to only a `gcd` condition. -/
lemma gammaSet_one_eq (a : Fin 2 → ZMod 1) :
    gammaSet 1 r a = {v : Fin 2 → ℤ | (v 0).gcd (v 1) = r} := by
  simp [gammaSet, Subsingleton.eq_zero (α := Fin 2 → ZMod 1)]

lemma gammaSet_one_mem_iff (v : Fin 2 → ℤ) : v ∈ gammaSet 1 r 0 ↔ (v 0).gcd (v 1) = r := by
  simp [gammaSet, Subsingleton.eq_zero (α := Fin 2 → ZMod 1)]

/-- For level `N = 1`, the gamma sets are all equivalent; this is the equivalence. -/
def gammaSet_one_equiv (a a' : Fin 2 → ZMod 1) : gammaSet 1 r a ≃ gammaSet 1 r a' :=
  Set.equivOfEq (gammaSet_one_const r a a')

/-- The map from `Fin 2 → ℤ` sending `![a,b]` to `a.gcd b`. -/
abbrev finGcdMap (v : Fin 2 → ℤ) : ℕ := (v 0).gcd (v 1)

lemma finGcdMap_eq_zero_iff {v : Fin 2 → ℤ} : finGcdMap v = 0 ↔ v = 0 := by
  rw [Int.gcd_eq_zero_iff]
  constructor
  · rintro ⟨h₀, h₁⟩
    ext i
    fin_cases i <;> assumption
  · rintro rfl
    exact ⟨rfl, rfl⟩

lemma gammaSet_ne_zero {N r : ℕ} {a : Fin 2 → ZMod N} (v : gammaSet N r a)
    (hr : r ≠ 0) : v.val ≠ 0 := by
  intro hv
  exact hr (v.property.2.symm.trans (finGcdMap_eq_zero_iff.mpr hv))

/-- Take the Euclidean quotient of every coordinate by a nonzero integer. -/
abbrev divIntMap (r : ℤ) [NeZero r] {m : ℕ} (v : Fin m → ℤ) : Fin m → ℤ :=
  fun i => Int.euclideanDiv (v i) r (NeZero.ne r)

lemma finGcdMap_div {r : ℕ} [NeZero r] (v : Fin 2 → ℤ) (hv : finGcdMap v = r) :
    IsCoprime (divIntMap r v 0) (divIntMap r v 1) := by
  have hg : 0 < finGcdMap v := hv ▸ Nat.pos_of_ne_zero (NeZero.ne r)
  subst r
  exact Int.isCoprime_iff_gcd_eq_one.mpr (Int.gcd_div_gcd_div_gcd hg)

lemma finGcdMap_smul {r : ℕ} (a : ℤ) {v : Fin 2 → ℤ} (hv : finGcdMap v = r) :
    finGcdMap (a • v) = a.natAbs * r := by
  simp [finGcdMap, Int.gcd_mul_left, hv]

lemma mem_gammaSet_one (v : Fin 2 → ℤ) : v ∈ gammaSet 1 1 0 ↔ IsCoprime (v 0) (v 1) := by
  rw [gammaSet_one_mem_iff, Int.isCoprime_iff_gcd_eq_one]

lemma gammaSet_div_gcd {r : ℕ} {v : Fin 2 → ℤ} (hv : v ∈ (gammaSet 1 r 0)) (i : Fin 2) :
   (r : ℤ) ∣ v i := by
  fin_cases i <;> simp [← hv.2, Int.gcd_dvd_left, Int.gcd_dvd_right]

lemma gammaSet_div_gcd_to_gammaSet10_bijection (r : ℕ) [NeZero r] :
    Set.BijOn (divIntMap r) (gammaSet 1 r 0) (gammaSet 1 1 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    simp only [divIntMap, mem_gammaSet_one] at *
    exact finGcdMap_div _ hx.2
  · intro x hx v hv hv2
    ext i
    have he := congrArg (fun y : ℤ ↦ (r : ℤ) * y) (congr_fun hv2 i)
    simpa only [divIntMap,
      show (r : ℤ) * Int.euclideanDiv (x i) r _ = x i from
        Int.mul_exactQuotient _ _ (gammaSet_div_gcd hx i) _,
      show (r : ℤ) * Int.euclideanDiv (v i) r _ = v i from
        Int.mul_exactQuotient _ _ (gammaSet_div_gcd hv i) _] using he
  · intro x hx
    use r • x
    simp only [nsmul_eq_mul]
    constructor
    · rw [mem_gammaSet_one, Int.isCoprime_iff_gcd_eq_one] at hx
      exact ⟨Subsingleton.eq_zero _, by simp [Int.gcd_mul_left, hx]⟩
    · ext i
      change Int.euclideanDiv ((r : ℤ) * x i) r _ = x i
      exact (Int.exactQuotient_eq_iff (Int.dvd_mul_right _ _) (NeZero.ne (r : ℤ))).2 rfl

lemma gammaSet_eq_gcd_mul_divIntMap {r : ℕ} [NeZero r] {v : Fin 2 → ℤ} (hv : v ∈ gammaSet 1 r 0) :
    v = r • (divIntMap r v) := by
  ext i
  exact (Int.mul_exactQuotient _ _ (gammaSet_div_gcd hv i) (NeZero.ne (r : ℤ))).symm

/-- The equivalence between `gammaSet 1 r 0` and `gammaSet 1 1 0` for non-zero `r`. -/
def gammaSetDivGcdEquiv (r : ℕ) [NeZero r] : gammaSet 1 r 0 ≃ gammaSet 1 1 0 :=
    Set.BijOn.equiv _ (gammaSet_div_gcd_to_gammaSet10_bijection r)

@[simp]
lemma gammaSetDivGcdEquiv_eq (r : ℕ) [NeZero r] (v : gammaSet 1 r 0) :
    (gammaSetDivGcdEquiv r) v = divIntMap r v.1 := rfl

/-- The equivalence between `(Fin 2 → ℤ)` and `Σ n : ℕ, gammaSet 1 n 0)` . -/
def gammaSetDivGcdSigmaEquiv : (Fin 2 → ℤ) ≃ (Σ r : ℕ, gammaSet 1 r 0) := by
  apply (Equiv.sigmaFiberEquiv finGcdMap).symm.trans
  refine Equiv.sigmaCongrRight fun b => ?_
  apply Equiv.subtypeEquivProp
  simp [gammaSet_one_eq]

@[simp]
lemma gammaSetDivGcdSigmaEquiv_symm_eq (v : Σ r : ℕ, gammaSet 1 r 0) :
    (gammaSetDivGcdSigmaEquiv.symm v) = v.2 := rfl

end gammaSet_def

variable {N a r} [NeZero r]

section gamma_action

/-- Right-multiplying a vector by a matrix in `SL(2, ℤ)` doesn't change its gcd. -/
lemma vecMulSL_gcd {v : Fin 2 → ℤ} (hab : finGcdMap v = r) (A : SL(2, ℤ)) :
    finGcdMap (v ᵥ* A.1) = r := by
  have hvr : v = r • divIntMap r v := by
    ext i
    refine Eq.symm (Int.mul_exactQuotient _ _ ?_ (NeZero.ne (r : ℤ)))
    fin_cases i <;> simp [← hab, Int.gcd_dvd_left, Int.gcd_dvd_right]
  rw [hvr, smul_vecMul]
  simpa using finGcdMap_smul r (Int.isCoprime_iff_gcd_eq_one.mp ((finGcdMap_div v hab).vecMulSL A))

/-- Right-multiplying by `γ ∈ SL(2, ℤ)` sends `gammaSet N a` to `gammaSet N (a ᵥ* γ)`. -/
lemma vecMul_SL2_mem_gammaSet {v : Fin 2 → ℤ} (hv : v ∈ gammaSet N r a)
    (γ : SL(2, ℤ)) : v ᵥ* γ ∈ gammaSet N r (a ᵥ* γ) := by
  refine ⟨?_, vecMulSL_gcd hv.2 γ⟩
  have := RingHom.map_vecMul (m := Fin 2) (n := Fin 2) (Int.castRingHom (ZMod N)) γ v
  simp only [eq_intCast, Int.coe_castRingHom] at this
  simp_rw [Function.comp_def, this, hv.1]
  simp

variable (a) in
/-- The bijection between `GammaSets` given by multiplying by an element of `SL(2, ℤ)`. -/
def gammaSetEquiv (γ : SL(2, ℤ)) : gammaSet N r a ≃ gammaSet N r (a ᵥ* γ) where
  toFun v := ⟨v.1 ᵥ* γ, vecMul_SL2_mem_gammaSet v.2 γ⟩
  invFun v := ⟨v.1 ᵥ* ↑(γ⁻¹), by
      have := vecMul_SL2_mem_gammaSet v.2 γ⁻¹
      rw [vecMul_vecMul, ← SpecialLinearGroup.coe_mul] at this
      simpa only [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Int.coe_castRingHom,
        map_inv, mul_inv_cancel, SpecialLinearGroup.coe_one, vecMul_one]⟩
  left_inv v := by simp_rw [vecMul_vecMul, ← SpecialLinearGroup.coe_mul, mul_inv_cancel,
    SpecialLinearGroup.coe_one, vecMul_one]
  right_inv v := by simp_rw [vecMul_vecMul, ← SpecialLinearGroup.coe_mul, inv_mul_cancel,
    SpecialLinearGroup.coe_one, vecMul_one]

end gamma_action

section eisSummand

lemma eisSummand_base_ne_zero {v : Fin 2 → ℤ} (hv : v ≠ 0) (z : ℍ) :
    (v 0 : ℂ) * z + v 1 ≠ 0 := by
  have hv' : (fun i ↦ (v i : ℝ)) ≠ 0 := by
    intro h
    apply hv
    ext i
    exact Int.cast_eq_zero.mp (congrFun h i)
  simpa only [Complex.ofReal_intCast] using linear_ne_zero z hv'

/-- The summand defining an Eisenstein series. Positive weight requires a nonzero lattice
vector; nonpositive weight retains the zero vector, since its exponent is nonnegative. -/
def eisSummand (k : ℤ) (v : Fin 2 → ℤ) (z : ℍ)
    (hv : 0 < k → v ≠ 0 := by intro hk; first | omega | checked_nonzero) : ℂ :=
  Checked.zpow (v 0 * z + v 1) (-k) (fun hk ↦ (eisSummand_base_ne_zero (hv (by omega)) z).isUnit)

lemma eisSummand_nat_eq (k : ℕ) {v : Fin 2 → ℤ} (hv : v ≠ 0) (z : ℍ) :
    eisSummand k v z (fun _ ↦ hv) = Checked.inv (((v 0 : ℂ) * z + v 1) ^ k)
      ((eisSummand_base_ne_zero hv z).isUnit.pow k) := by
  simp only [eisSummand, zpow_neg₀ (eisSummand_base_ne_zero hv z), zpow_natCast₀]

/-- How the `eisSummand` function changes under the Moebius action. -/
theorem eisSummand_SL2_apply (k : ℤ) (i : (Fin 2 → ℤ)) (A : SL(2, ℤ)) (z : ℍ)
    {hi : 0 < k → i ≠ 0} {hiA : 0 < k → i ᵥ* (A : Matrix (Fin 2) (Fin 2) ℤ) ≠ 0} :
    eisSummand k i (A • z) hi =
      Checked.zpow (denom A z) k (fun _ ↦ (denom_ne_zero A z).isUnit) *
        eisSummand k (i ᵥ* A) z hiA := by
  have hd : IsUnit (denom A z) := (denom_ne_zero A z).isUnit
  let j : Fin 2 → ℤ := i ᵥ* (A : Matrix (Fin 2) (Fin 2) ℤ)
  have hlinear : (i 0 : ℂ) * (A • z : ℍ) + i 1 =
      ((j 0 : ℂ) * z + j 1) / denom A z := by
    have hu : IsUnit ((A 1 0 : ℂ) * z + A 1 1) := by
      simpa only [ModularGroup.denom_apply] using hd
    simp only [j, vecMul, vec2_dotProduct, ModularGroup.denom_apply A z,
      UpperHalfPlane.coe_specialLinearGroup_apply, algebraMap_int_eq, Int.coe_castRingHom,
      Complex.ofReal_intCast]
    push_cast
    field_simp
    ring
  have hbase (h : -k < 0) : IsUnit ((j 0 : ℂ) * z + j 1) :=
    (eisSummand_base_ne_zero (hiA (by omega)) z).isUnit
  simp only [eisSummand, hlinear]
  refine (div_zpow₀ ((j 0 : ℂ) * z + j 1) (denom A z) (-k) (hb := hd)
    (h := fun h ↦ (hbase h).div₀ hd)).trans ?_
  have hn : (denom A z ^ (-k))⁻¹ = denom A z ^ k := by
    simpa only [neg_neg] using (zpow_neg₀ hd.ne_zero (-k)).symm
  rw [div_eq_mul_inv₀ _ _ (hb := hd.zpow₀ (-k)), hn]
  exact mul_comm _ _

end eisSummand

variable (a)

/-- An Eisenstein series of weight `k` and level `Γ(N)`, with congruence condition `a`. -/
def _root_.eisensteinSeries (k : ℤ) (z : ℍ) : ℂ :=
  ∑' x : gammaSet N 1 a, eisSummand k x z (fun _ ↦ gammaSet_ne_zero x one_ne_zero)

lemma eisensteinSeries_slash_apply (k : ℤ) (γ : SL(2, ℤ)) :
    eisensteinSeries a k ∣[k] γ = eisensteinSeries (a ᵥ* γ) k := by
  ext1 z
  have hd := denom_ne_zero (γ : GL (Fin 2) ℝ) z
  have hdu := hd.isUnit.zpow₀ k
  rw [SL_slash_apply, zpow_neg₀ hd]
  simp only [eisensteinSeries, ← tsum_mul_right]
  trans ∑' x : gammaSet N 1 a, eisSummand k (gammaSetEquiv a γ x) z
    (fun _ ↦ gammaSet_ne_zero (gammaSetEquiv a γ x) one_ne_zero)
  · refine tsum_congr fun x ↦ ?_
    rw [eisSummand_SL2_apply (hiA := fun _ ↦ gammaSet_ne_zero (gammaSetEquiv a γ x) one_ne_zero)]
    rw [mul_comm (denom γ z ^ k), mul_assoc, mul_inv_cancel₀ (ha := hdu), mul_one]
    rfl
  · exact (gammaSetEquiv a γ).tsum_eq (fun x ↦
      eisSummand k x z (fun _ ↦ gammaSet_ne_zero x one_ne_zero))

/-- The `SlashInvariantForm` defined by an Eisenstein series of weight `k : ℤ`, level `Γ(N)`,
and congruence condition given by `a : Fin 2 → ZMod N`. -/
def eisensteinSeriesSIF (k : ℤ) : SlashInvariantForm (Gamma N) k where
  toFun := eisensteinSeries a k
  slash_action_eq' A hA := by
    obtain ⟨A, (hA : A ∈ Γ(N)), rfl⟩ := hA
    simp [SpecialLinearGroup.mapGL, ← SL_slash, eisensteinSeries_slash_apply, Gamma_mem'.mp hA]

lemma eisensteinSeriesSIF_apply (k : ℤ) (z : ℍ) :
    eisensteinSeriesSIF a k z = eisensteinSeries a k z := rfl

end EisensteinSeries
