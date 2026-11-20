/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.ConditionalInt

/-!
# Eisenstein Series E2

We define the Eisenstein series `E2` of weight `2` and level `1` as a limit of partial sums
over non-symmetric intervals.

-/

open UpperHalfPlane hiding I

open ModularForm EisensteinSeries Matrix.SpecialLinearGroup Filter Complex MatrixGroups
  SummationFilter Real

@[expose] public noncomputable section

namespace EisensteinSeries

/-- This is an auxiliary summand used to define the Eisenstein series `G2`. -/
def e2Summand (m : ℤ) (z : ℍ) : ℂ :=
  ∑' n : {n : ℤ // ![m, n] ≠ 0}, eisSummand 2 ![m, (n : ℤ)] z (fun _ ↦ n.2)

lemma e2Summand_summable (m : ℤ) (z : ℍ) :
    Summable (fun n : {n : ℤ // ![m, n] ≠ 0} ↦
      eisSummand 2 ![m, (n : ℤ)] z (fun _ ↦ n.2)) := by
  have hlinear (n : {n : ℤ // ![m, n] ≠ 0}) : IsUnit ((m : ℂ) * z + n) := by
    simpa using (eisSummand_base_ne_zero n.property z).isUnit
  have hs := linear_right_summable z m (k := 2) (by norm_num)
    (fun n : {n : ℤ // ![m, n] ≠ 0} ↦ (n : ℤ)) Subtype.coe_injective
    (hpower := fun n ↦ (hlinear n).zpow₀ 2)
  refine hs.congr fun n ↦ ?_
  refine Eq.trans ?_ (eisSummand_nat_eq 2 n.2 z).symm
  simp only [zpow_ofNat₀, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]

@[simp]
lemma e2Summand_zero_eq_two_riemannZeta_two (z : ℍ) : e2Summand 0 z = 2 * riemannZeta 2 := by
  let q : {n : ℤ // ![0, n] ≠ 0} ≃ {n : ℤ // n ≠ 0} :=
    Equiv.subtypeEquiv (Equiv.refl ℤ) (fun n ↦ by
      apply not_congr
      constructor
      · exact fun h ↦ by simpa using congrFun h (1 : Fin 2)
      · rintro rfl
        ext i
        fin_cases i <;> rfl)
  have hζ : 2 * riemannZeta 2 = ∑' n : {n : ℤ // n ≠ 0}, (((n : ℤ) : ℂ) ^ 2)⁻¹ := by
    simpa only [Nat.cast_ofNat] using
      two_mul_riemannZeta_eq_tsum_int_inv_pow_of_even (k := 2) (by decide) (by decide)
  rw [e2Summand, hζ, ← q.tsum_eq]
  refine tsum_congr fun n ↦ ?_
  refine (eisSummand_nat_eq 2 n.2 z).trans ?_
  simp only [q, Equiv.subtypeEquiv_apply, Equiv.refl_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Int.cast_zero,
    zero_mul, zero_add]

lemma e2Summand_even (z : ℍ) : (e2Summand · z).Even := by
  intro m
  let q : {n : ℤ // ![-m, n] ≠ 0} ≃ {n : ℤ // ![m, n] ≠ 0} :=
    Equiv.subtypeEquiv (Equiv.neg ℤ) (fun n ↦ by
      have h : (![-m, n] : Fin 2 → ℤ) = -![m, -n] := by
        ext i
        fin_cases i <;> simp
      simp only [Equiv.neg_apply, h, neg_ne_zero])
  simp only [e2Summand, ← q.tsum_eq]
  refine tsum_congr fun n ↦ ?_
  refine (eisSummand_nat_eq 2 n.2 z).trans (Eq.trans ?_ (eisSummand_nat_eq 2 (q n).2 z).symm)
  have he : -((m : ℂ) * z) + (n.val : ℂ) = -((m : ℂ) * z + -(n.val : ℂ)) := by ring
  simp only [q, Equiv.subtypeEquiv_apply, Equiv.neg_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Int.cast_neg,
    neg_mul, he, neg_sq]

/-- The Eisenstein series of weight `2` and level `1` defined as the conditional sum
of `m` in `[N,N]` of `e2Summand m`. This sum over symmetric intervals is handy in showing it is
Summable. -/
def G2 : ℍ → ℂ := fun z ↦ ∑'[symmetricIcc ℤ] m, e2Summand m z

lemma isUnit_two_mul_riemannZeta_two : IsUnit (2 * riemannZeta 2) := by
  rw [riemannZeta_two]
  have hπ := (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero).isUnit
  exact (show IsUnit (2 : ℂ) by exact (by norm_num : (2 : ℂ) ≠ 0).isUnit).mul
    ((hπ.pow 2).div₀ (by exact (by norm_num : (6 : ℂ) ≠ 0).isUnit))

/-- The normalised Eisenstein series of weight `2` and level `1`, obtained by dividing `G2`
by `2 * ζ(2)`. -/
def E2 : ℍ → ℂ := Checked.div 1 (2 * riemannZeta 2) isUnit_two_mul_riemannZeta_two • G2

/-- This function measures the defect in `G2` being a modular form. -/
def D2 (γ : SL(2, ℤ)) : ℍ → ℂ := fun z ↦
  Checked.div (2 * π * I * γ 1 0) (denom γ z) (isUnit_denom γ z)

@[simp]
lemma D2_one : D2 1 = 0 := by
  ext z
  simp [D2]

private lemma denom_aux (A B : SL(2, ℤ)) (z : ℍ) : ((A * B) 1 0) * (denom B z) =
    (A 1 0) * B.1.det + (B 1 0) * denom (A * B) z := by
  have h0 := Matrix.two_mul_expl A.1 B.1
  simp only [Fin.isValue, Matrix.SpecialLinearGroup.coe_mul, h0.2.2.1, Int.cast_add, Int.cast_mul,
    ModularGroup.denom_apply, Matrix.det_fin_two B.1, Int.cast_sub, ← map_mul, h0.2.2.2]
  ring

lemma D2_mul (A B : SL(2, ℤ)) : D2 (A * B) = (D2 A) ∣[(2 : ℤ)] B + D2 B := by
  ext z
  have hA := denom_ne_zero (A : GL (Fin 2) ℝ) (B • z)
  have hB := denom_ne_zero (B : GL (Fin 2) ℝ) z
  have hAB := denom_ne_zero ((A * B : SL(2, ℤ)) : GL (Fin 2) ℝ) z
  have hsmul : Checked.div (num B z) (denom B z) hB.isUnit = (↑(B • z) : ℂ) := by
    rw [coe_specialLinearGroup_apply]
    rfl
  have hmul : ((A * B : SL(2, ℤ)) : GL (Fin 2) ℝ) =
      (A : GL (Fin 2) ℝ) * (B : GL (Fin 2) ℝ) := map_mul (Matrix.SpecialLinearGroup.mapGL ℝ) A B
  have hden : denom (A * B : SL(2, ℤ)) z = denom A (B • z : ℍ) * denom B z := by
    rw [hmul, denom_cocycle A B (hh := hB.isUnit), hsmul]
  have hentry : (((A * B) 1 0 : ℤ) : ℂ) * denom B z =
      (A 1 0 : ℂ) + (B 1 0 : ℂ) * (denom A (B • z : ℍ) * denom B z) := by
    rw [← hden]
    simpa only [B.property, Int.cast_one, mul_one, ← hmul] using! denom_aux A B z
  have h := congrArg (fun x : ℂ ↦ 2 * π * I * x /
    (denom A (B • z : ℍ) * denom B z * denom B z)) hentry
  rw [Pi.add_apply, SL_slash_apply]
  simp only [D2, zpow_neg₀ hB, zpow_ofNat₀, hden]
  convert h using 1 <;> field_simp

lemma D2_inv (A) : (D2 A) ∣[(2 : ℤ)] A⁻¹ = -D2 A⁻¹ := by
  simpa [eq_neg_iff_add_eq_zero] using (D2_mul A A⁻¹).symm

lemma D2_T : D2 ModularGroup.T = 0 := by
  ext z
  simp [D2, ModularGroup.T]

set_option backward.isDefEq.respectTransparency.types false in
lemma D2_S (z : ℍ) : D2 ModularGroup.S z = Checked.div (2 * π * I) (z : ℂ) z.ne_zero.isUnit := by
  simp [D2, ModularGroup.S, ModularGroup.denom_apply]

end EisensteinSeries
