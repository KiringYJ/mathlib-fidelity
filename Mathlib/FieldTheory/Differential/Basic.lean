/-
Copyright (c) 2024 Daniel Weber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Weber
-/
module

public import Mathlib.RingTheory.Derivation.MapCoeffs
public import Mathlib.FieldTheory.PrimitiveElement

/-!
# Differential Fields

This file defines the logarithmic derivative `Differential.logDeriv` and proves properties of it.
This is defined algebraically, compared to `logDeriv` which is analytical.
-/

@[expose] public section

namespace Differential

open algebraMap Polynomial IntermediateField

variable {R : Type*} [Field R] [Differential R] (a b : R)

/--
The logarithmic derivative `a′ / a` of a unit `a`.
-/
noncomputable def logDeriv (ha : IsUnit a := by checked_unit) : R := a′ / a

@[simp]
lemma logDeriv_one : logDeriv (1 : R) = 0 := by
  simp [logDeriv]

lemma logDeriv_mul {hab : IsUnit (a * b)} : logDeriv (a * b) = logDeriv a + logDeriv b := by
  have ha : IsUnit a := isUnit_of_mul_isUnit_left hab
  have hb : IsUnit b := isUnit_of_mul_isUnit_right hab
  unfold logDeriv
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  field_simp
  ring

lemma logDeriv_div {hb : IsUnit b} {hab : IsUnit (a / b)} :
    logDeriv (a / b) = logDeriv a - logDeriv b := by
  have ha : IsUnit a := IsUnit.of_div₀ hab
  unfold logDeriv
  rw [Derivation.leibniz_div]
  simp only [smul_eq_mul]
  field_simp

lemma logDeriv_pow (n : ℕ) (a : R) {ha : IsUnit a} : logDeriv (a ^ n) = n * logDeriv a := by
  induction n with
  | zero => simp
  | succ n h2 =>
    have : logDeriv (a ^ (n + 1)) = logDeriv (a ^ n * a) := by simp only [pow_succ]
    rw [this, logDeriv_mul, h2, Nat.cast_add, Nat.cast_one, add_mul, one_mul]

@[simp]
lemma logDeriv_pow_of_ne_zero (n : ℕ) (a : R) {ha : a ≠ 0} : logDeriv (a ^ n) = n * logDeriv a :=
  logDeriv_pow n a (ha := ha.isUnit)

lemma logDeriv_eq_zero {ha : IsUnit a} : logDeriv a = 0 ↔ a′ = 0 := by
  simp [logDeriv]

/-- The logarithmic derivative of a product is the sum of the logarithmic derivatives of its
factors. The sum is taken over the elements of the multiset, each of which is nonzero. -/
lemma logDeriv_multisetProd {ι : Type*} (s : Multiset ι) {f : ι → R} (h : ∀ x ∈ s, f x ≠ 0) :
    logDeriv (s.map f).prod (Multiset.prod_ne_zero fun h0 ↦
      have ⟨x, hx, e⟩ := Multiset.mem_map.1 h0; h x hx e).isUnit =
      (s.attach.map fun x ↦ logDeriv (f x.1) (h x.1 x.2).isUnit).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ha : f a ≠ 0 := h a (Multiset.mem_cons_self a s)
    have hs : (s.map f).prod ≠ 0 := Multiset.prod_ne_zero fun h0 ↦
      have ⟨x, hx, e⟩ := Multiset.mem_map.1 h0; h x (Multiset.mem_cons_of_mem hx) e
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.attach_cons, Multiset.sum_cons,
      Multiset.map_map, Function.comp_def]
    rw [logDeriv_mul, ih fun x hx ↦ h x (Multiset.mem_cons_of_mem hx)]

/-- The logarithmic derivative of a product is the sum of the logarithmic derivatives of its
factors. The sum is taken over the elements of `s`, each of which is nonzero. -/
lemma logDeriv_prod (ι : Type*) (s : Finset ι) (f : ι → R) (h : ∀ x ∈ s, f x ≠ 0) :
    logDeriv (∏ x ∈ s, f x) (Finset.prod_ne_zero_iff.2 h).isUnit =
      ∑ x : s, logDeriv (f x) (h x x.2).isUnit := by
  refine (logDeriv_multisetProd s.1 h).trans ?_
  rw [Finset.sum_eq_multiset_sum, Finset.univ_eq_attach]
  rfl

lemma logDeriv_algebraMap {F K : Type*} [Field F] [Field K] [Differential F] [Differential K]
    [Algebra F K] [DifferentialAlgebra F K]
    (a : F) {ha : IsUnit a} :
    logDeriv (algebraMap F K a) (ha.map _) = algebraMap F K (logDeriv a) := by
  unfold logDeriv
  simp [deriv_algebraMap]

@[norm_cast]
lemma _root_.algebraMap.coe_logDeriv {F K : Type*} [Field F] [Field K] [Differential F]
    [Differential K] [Algebra F K] [DifferentialAlgebra F K]
    (a : F) {ha : IsUnit a} : logDeriv a = logDeriv (a : K) (ha.map _) :=
  (logDeriv_algebraMap a).symm

variable {F : Type*} [Field F] [Differential F] [CharZero F]

omit [Differential F] in
lemma aeval_root_derivative_ne_zero (p : F[X]) [Fact (Irreducible p)] :
    aeval (AdjoinRoot.root p) (derivative p) ≠ 0 := by
  rw [AdjoinRoot.aeval_eq, ne_eq, AdjoinRoot.mk_eq_zero]
  have : 0 < p.natDegree := Irreducible.natDegree_pos (Fact.out)
  apply not_dvd_of_natDegree_lt
  · intro nh
    simp_all
  apply natDegree_derivative_lt
  exact Nat.ne_zero_of_lt this

noncomputable instance (p : F[X]) [Fact (Irreducible p)] [Fact p.Monic] :
    Differential (AdjoinRoot p) where
  deriv := Derivation.liftOfSurjective (f := (AdjoinRoot.mk p).toIntAlgHom) AdjoinRoot.mk_surjective
    (d := haveI := aeval_root_derivative_ne_zero p
      implicitDeriv <| AdjoinRoot.modByMonicHom Fact.out <|
        - (aeval (AdjoinRoot.root p) (mapCoeffs p)) / (aeval (AdjoinRoot.root p) (derivative p)))
    (by
      rintro x hx
      simp_all only [RingHom.toIntAlgHom_apply, AdjoinRoot.mk_eq_zero]
      obtain ⟨q, rfl⟩ := hx
      simp only [Derivation.leibniz, smul_eq_mul]
      apply dvd_add (dvd_mul_right ..)
      apply dvd_mul_of_dvd_right
      rw [← AdjoinRoot.mk_eq_zero]
      unfold implicitDeriv
      simp only [AdjoinRoot.aeval_eq, Derivation.coe_add, Derivation.coe_smul, Pi.add_apply,
        Pi.smul_apply, Derivation.restrictScalars_apply, derivative'_apply, smul_eq_mul, map_add,
        map_mul, AdjoinRoot.mk_leftInverse Fact.out _]
      rw [div_mul_cancel₀, add_neg_cancel])

set_option backward.isDefEq.respectTransparency false in
instance (p : F[X]) [Fact (Irreducible p)] [Fact p.Monic] :
    DifferentialAlgebra F (AdjoinRoot p) where
  deriv_algebraMap a := by
    change (Derivation.liftOfSurjective _ _) ((AdjoinRoot.mk p).toIntAlgHom (C a)) = _
    rw [Derivation.liftOfSurjective_apply, implicitDeriv_C]
    rfl

variable {K : Type*} [Field K] [Algebra F K]

variable (F K) in
/--
If `K` is a finite field extension of `F` then we can define a differential algebra on `K`, by
choosing a primitive element of `K`, `k` and then using the equivalence to `AdjoinRoot (minpoly k)`.
-/
@[reducible]
noncomputable def differentialFiniteDimensional [FiniteDimensional F K] : Differential K :=
  let k := (Field.exists_primitive_element F K).choose
  have h : F⟮k⟯ = ⊤ := (Field.exists_primitive_element F K).choose_spec
  have : Fact (minpoly F k).Monic := ⟨minpoly.monic (IsAlgebraic.of_finite ..).isIntegral⟩
  have : Fact (Irreducible (minpoly F k)) :=
    ⟨minpoly.irreducible (IsAlgebraic.of_finite ..).isIntegral⟩
  Differential.equiv (IntermediateField.adjoinRootEquivAdjoin F
    (IsAlgebraic.of_finite F k).isIntegral |>.trans (IntermediateField.equivOfEq h) |>.trans
    IntermediateField.topEquiv).symm.toRingEquiv

lemma differentialAlgebraFiniteDimensional [FiniteDimensional F K] :
    letI := differentialFiniteDimensional F K
    DifferentialAlgebra F K := by
  let k := (Field.exists_primitive_element F K).choose
  have h : F⟮k⟯ = ⊤ := (Field.exists_primitive_element F K).choose_spec
  have : Fact (minpoly F k).Monic := ⟨minpoly.monic (IsAlgebraic.of_finite ..).isIntegral⟩
  have : Fact (Irreducible (minpoly F k)) :=
    ⟨minpoly.irreducible (IsAlgebraic.of_finite ..).isIntegral⟩
  apply DifferentialAlgebra.equiv

/--
A finite extension of a differential field has a unique derivation which agrees with the one on the
base field.
-/
@[instance_reducible]
noncomputable def uniqueDifferentialAlgebraFiniteDimensional [FiniteDimensional F K] :
    Unique {_a : Differential K // DifferentialAlgebra F K} := by
  let default : {_a : Differential K // DifferentialAlgebra F K} :=
      ⟨differentialFiniteDimensional F K, differentialAlgebraFiniteDimensional⟩
  refine ⟨⟨default⟩, fun ⟨a, ha⟩ ↦ ?_⟩
  ext x
  apply_fun (aeval x (mapCoeffs (minpoly F x)) + aeval x (derivative (minpoly F x)) * ·)
  · conv_lhs => apply (deriv_aeval_eq ..).symm
    conv_rhs => apply (@deriv_aeval_eq _ _ _ _ _ default.1 _ default.2 _ _).symm
    simp
  · apply (add_right_injective _).comp
    apply mul_right_injective₀
    rw [ne_eq, ← minpoly.dvd_iff]
    have : 0 < (minpoly F x).natDegree := Irreducible.natDegree_pos
      (minpoly.irreducible (Algebra.IsIntegral.isIntegral _))
    apply not_dvd_of_natDegree_lt
    · intro nh
      simp_all
    apply natDegree_derivative_lt
    exact Nat.ne_zero_of_lt this

noncomputable instance (B : IntermediateField F K) [FiniteDimensional F B] : Differential B :=
  differentialFiniteDimensional F B

instance (B : IntermediateField F K) [FiniteDimensional F B] :
    DifferentialAlgebra F B := differentialAlgebraFiniteDimensional

instance [Differential K] [DifferentialAlgebra F K] (B : IntermediateField F K)
    [FiniteDimensional F B] : DifferentialAlgebra B K where
  deriv_algebraMap a := by
    change (B.val a)′ = B.val a′
    rw [algHom_deriv']
    exact Subtype.val_injective

end Differential
