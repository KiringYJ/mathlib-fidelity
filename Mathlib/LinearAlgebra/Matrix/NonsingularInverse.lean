/-
Copyright (c) 2019 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Lu-Ming Zhang
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Invertible
public import Mathlib.LinearAlgebra.Matrix.SemiringInverse
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Nonsingular inverses

In this file, we define an inverse for square matrices of invertible determinant.

For matrices that are not square or not of full rank, there is a more general notion of
pseudoinverses which we do not consider here.

The inverse used in this file is the adjugate multiplied by the inverse of the determinant unit.
It is exposed as `nonsingularInverse A h`, where `h : IsUnit A.det`, and as the bundled unit
`unitOfIsUnitDet A h`. A matrix with a nonunit determinant has no value under this operation.

The constructive interface `⅟A` remains available in the presence of `[Invertible A]`.

We start by working with `Invertible`, and show the main results:

* `Matrix.invertibleOfDetInvertible`
* `Matrix.detInvertibleOfInvertible`
* `Matrix.isUnit_iff_isUnit_det`
* `Matrix.mul_eq_one_comm`

After this we define the exact-domain nonsingular inverse and prove its multiplicative laws.

## References

  * https://en.wikipedia.org/wiki/Cramer's_rule#Finding_inverse_matrix

## Tags

matrix inverse, cramer, cramer's rule, adjugate
-/

@[expose] public section


namespace Matrix

universe u u' v

variable {l : Type*} {m : Type u} {n : Type u'} {α : Type v}

open Matrix Equiv Equiv.Perm Finset
open scoped Ring

/-! ### Matrices are `Invertible` iff their determinants are -/


section Invertible

variable [Fintype n] [DecidableEq n] [CommRing α]
variable (A : Matrix n n α) (B : Matrix n n α)

/-- If `A.det` has a constructive inverse, produce one for `A`. -/
@[instance_reducible]
def invertibleOfDetInvertible [Invertible A.det] : Invertible A where
  invOf := ⅟A.det • A.adjugate
  mul_invOf_self := by
    rw [mul_smul_comm, mul_adjugate, smul_smul, invOf_mul_self, one_smul]
  invOf_mul_self := by
    rw [smul_mul_assoc, adjugate_mul, smul_smul, invOf_mul_self, one_smul]

theorem invOf_eq [Invertible A.det] [Invertible A] : ⅟A = ⅟A.det • A.adjugate := by
  let := invertibleOfDetInvertible A
  convert! (rfl : ⅟A = _)

/-- `A.det` is invertible if `A` has a left inverse. -/
@[instance_reducible]
def detInvertibleOfLeftInverse (h : B * A = 1) : Invertible A.det where
  invOf := B.det
  mul_invOf_self := by rw [mul_comm, ← det_mul, h, det_one]
  invOf_mul_self := by rw [← det_mul, h, det_one]

/-- `A.det` is invertible if `A` has a right inverse. -/
@[instance_reducible]
def detInvertibleOfRightInverse (h : A * B = 1) : Invertible A.det where
  invOf := B.det
  mul_invOf_self := by rw [← det_mul, h, det_one]
  invOf_mul_self := by rw [mul_comm, ← det_mul, h, det_one]

/-- If `A` has a constructive inverse, produce one for `A.det`. -/
@[instance_reducible]
def detInvertibleOfInvertible [Invertible A] : Invertible A.det :=
  detInvertibleOfLeftInverse A (⅟A) (invOf_mul_self _)

theorem det_invOf [Invertible A] [Invertible A.det] : (⅟A).det = ⅟A.det := by
  let := detInvertibleOfInvertible A
  convert! (rfl : _ = ⅟A.det)

/-- Together `Matrix.detInvertibleOfInvertible` and `Matrix.invertibleOfDetInvertible` form an
equivalence, although both sides of the equiv are subsingleton anyway. -/
@[simps]
def invertibleEquivDetInvertible : Invertible A ≃ Invertible A.det where
  toFun := @detInvertibleOfInvertible _ _ _ _ _ A
  invFun := @invertibleOfDetInvertible _ _ _ _ _ A
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/-- Given a proof that `A.det` has a constructive inverse, lift `A` to `(Matrix n n α)ˣ` -/
def unitOfDetInvertible [Invertible A.det] : (Matrix n n α)ˣ :=
  @unitOfInvertible _ _ A (invertibleOfDetInvertible A)

/-- When lowered to a prop, `Matrix.invertibleEquivDetInvertible` forms an `iff`. -/
theorem isUnit_iff_isUnit_det : IsUnit A ↔ IsUnit A.det := by
  simp only [← nonempty_invertible_iff_isUnit, (invertibleEquivDetInvertible A).nonempty_congr]

@[simp]
theorem isUnits_det_units (A : (Matrix n n α)ˣ) : IsUnit (A : Matrix n n α).det :=
  isUnit_iff_isUnit_det _ |>.mp A.isUnit

/-! #### Variants of the statements above with `IsUnit` -/


theorem isUnit_det_of_invertible [Invertible A] : IsUnit A.det :=
  @isUnit_of_invertible _ _ _ (detInvertibleOfInvertible A)

variable {A B}

theorem isUnit_det_of_left_inverse (h : B * A = 1) : IsUnit A.det :=
  @isUnit_of_invertible _ _ _ (detInvertibleOfLeftInverse _ _ h)

theorem isUnit_det_of_right_inverse (h : A * B = 1) : IsUnit A.det :=
  @isUnit_of_invertible _ _ _ (detInvertibleOfRightInverse _ _ h)

theorem det_ne_zero_of_left_inverse [Nontrivial α] (h : B * A = 1) : A.det ≠ 0 :=
  (isUnit_det_of_left_inverse h).ne_zero

theorem det_ne_zero_of_right_inverse [Nontrivial α] (h : A * B = 1) : A.det ≠ 0 :=
  (isUnit_det_of_right_inverse h).ne_zero

end Invertible

section NonsingularInverse

variable [Fintype n] [DecidableEq n] [CommRing α]
variable (A : Matrix n n α) (B : Matrix n n α)

theorem isUnit_det_transpose (h : IsUnit A.det) : IsUnit Aᵀ.det := by
  rw [det_transpose]
  exact h

/-! ### The inverse on the exact unit-determinant domain -/

/-- The inverse of a square matrix whose determinant is a unit. -/
noncomputable def nonsingularInverse (A : Matrix n n α) (h : IsUnit A.det) : Matrix n n α :=
  (↑h.unit⁻¹ : α) • A.adjugate

theorem nonsingularInverse_def (h : IsUnit A.det) :
    nonsingularInverse A h = (↑h.unit⁻¹ : α) • A.adjugate := rfl

@[simp]
theorem mul_nonsingularInverse (h : IsUnit A.det) : A * nonsingularInverse A h = 1 := by
  rw [nonsingularInverse, mul_smul_comm, mul_adjugate, smul_smul, h.val_inv_mul, one_smul]

@[simp]
theorem nonsingularInverse_mul (h : IsUnit A.det) : nonsingularInverse A h * A = 1 := by
  rw [nonsingularInverse, smul_mul_assoc, adjugate_mul, smul_smul, h.val_inv_mul, one_smul]

@[instance_reducible]
noncomputable def invertibleOfIsUnitDet (A : Matrix n n α) (h : IsUnit A.det) : Invertible A where
  invOf := nonsingularInverse A h
  invOf_mul_self := nonsingularInverse_mul A h
  mul_invOf_self := mul_nonsingularInverse A h

/-- A matrix with unit determinant, bundled with its multiplicative inverse. -/
noncomputable def unitOfIsUnitDet (A : Matrix n n α) (h : IsUnit A.det) :
    (Matrix n n α)ˣ where
  val := A
  inv := nonsingularInverse A h
  val_inv := mul_nonsingularInverse A h
  inv_val := nonsingularInverse_mul A h

@[simp, norm_cast] theorem coe_unitOfIsUnitDet (h : IsUnit A.det) :
    ↑(unitOfIsUnitDet A h) = A := rfl

@[simp, norm_cast] theorem coe_unitOfIsUnitDet_inv (h : IsUnit A.det) :
    ↑(unitOfIsUnitDet A h)⁻¹ = nonsingularInverse A h := rfl

theorem left_inv_eq_left_inv {A B C : Matrix n n α}
    (h : B * A = 1) (g : C * A = 1) : B = C := by
  have g' : A * C = 1 := mul_eq_one_comm.2 g
  calc B = B * (A * C) := by rw [g', mul_one]
       _ = (B * A) * C := by rw [mul_assoc]
       _ = C := by rw [h, one_mul]

theorem right_inv_eq_right_inv {A B C : Matrix n n α}
    (h : A * B = 1) (g : A * C = 1) : B = C :=
  left_inv_eq_left_inv (mul_eq_one_comm.2 h) (mul_eq_one_comm.2 g)

theorem right_inv_eq_left_inv {A B C : Matrix n n α}
    (h : A * B = 1) (g : C * A = 1) : B = C := by
  calc B = 1 * B := by rw [one_mul]
       _ = (C * A) * B := by rw [g]
       _ = C * (A * B) := by rw [mul_assoc]
       _ = C := by rw [h, mul_one]

/-- The inverse selected by constructive `Invertible` data is the determinant-unit inverse. -/
theorem invOf_eq_nonsingularInverse [Invertible A] :
    ⅟A = nonsingularInverse A (isUnit_det_of_invertible A) :=
  right_inv_eq_right_inv (mul_invOf_self A) (mul_nonsingularInverse A _)

theorem transpose_nonsingularInverse (h : IsUnit A.det) :
    (nonsingularInverse A h)ᵀ = nonsingularInverse Aᵀ (isUnit_det_transpose A h) := by
  apply right_inv_eq_right_inv
  · rw [← transpose_mul, nonsingularInverse_mul, transpose_one]
  · exact mul_nonsingularInverse _ _

theorem conjTranspose_nonsingularInverse [StarRing α] (h : IsUnit A.det) :
    (nonsingularInverse A h)ᴴ =
      nonsingularInverse Aᴴ (by simpa only [det_conjTranspose] using h.star) := by
  apply right_inv_eq_right_inv
  · rw [← conjTranspose_mul, nonsingularInverse_mul, conjTranspose_one]
  · exact mul_nonsingularInverse _ _

@[simp]
theorem mul_nonsingularInverse_cancel_right (B : Matrix m n α) (h : IsUnit A.det) :
    B * A * nonsingularInverse A h = B := by
  simp [Matrix.mul_assoc, mul_nonsingularInverse A h]

@[simp]
theorem mul_nonsingularInverse_cancel_left (B : Matrix n m α) (h : IsUnit A.det) :
    A * (nonsingularInverse A h * B) = B := by
  simp [← Matrix.mul_assoc, mul_nonsingularInverse A h]

@[simp]
theorem nonsingularInverse_mul_cancel_right (B : Matrix m n α) (h : IsUnit A.det) :
    B * nonsingularInverse A h * A = B := by
  simp [Matrix.mul_assoc, nonsingularInverse_mul A h]

@[simp]
theorem nonsingularInverse_mul_cancel_left (B : Matrix n m α) (h : IsUnit A.det) :
    nonsingularInverse A h * (A * B) = B := by
  simp [← Matrix.mul_assoc, nonsingularInverse_mul A h]

lemma nonsingularInverse_mulVec_eq_vec {A : Matrix n n α} (h : IsUnit A.det)
    {u v : n → α} (hM : u = A.mulVec v) : (nonsingularInverse A h).mulVec u = v := by
  rw [hM, Matrix.mulVec_mulVec, nonsingularInverse_mul, Matrix.one_mulVec]

@[simp]
theorem mulVec_nonsingularInverse_mulVec (h : IsUnit A.det) (b : n → α) :
    A *ᵥ (nonsingularInverse A h *ᵥ b) = b := by
  rw [mulVec_mulVec, mul_nonsingularInverse, one_mulVec]

theorem mulVec_eq_iff_eq_nonsingularInverse_mulVec (h : IsUnit A.det) (x b : n → α) :
    A *ᵥ x = b ↔ x = nonsingularInverse A h *ᵥ b := by
  constructor
  · intro hx
    rw [← hx, mulVec_mulVec, nonsingularInverse_mul, one_mulVec]
  · rintro rfl
    exact mulVec_nonsingularInverse_mulVec A h b

lemma mul_right_injective_of_isUnitDet (h : IsUnit A.det) :
    Function.Injective (fun (x : Matrix n m α) => A * x) :=
  fun _ _ hxy => by
    simpa only [nonsingularInverse_mul_cancel_left A _ h] using
      congr_arg (nonsingularInverse A h * ·) hxy

lemma mul_left_injective_of_isUnitDet (h : IsUnit A.det) :
    Function.Injective (fun (x : Matrix m n α) => x * A) :=
  fun _ _ hxy => by
    simpa only [mul_nonsingularInverse_cancel_right A _ h] using
      congr_arg (· * nonsingularInverse A h) hxy

lemma IsSymm.nonsingularInverse {A : Matrix n n α} (hA : A.IsSymm) (h : IsUnit A.det) :
    (nonsingularInverse A h).IsSymm := hA.adjugate.smul _

end NonsingularInverse

section InjectiveMul
variable [Fintype n] [Fintype m] [DecidableEq m] [CommRing α]

lemma mul_left_injective_of_inv (A : Matrix m n α) (B : Matrix n m α) (h : A * B = 1) :
    Function.Injective (fun x : Matrix l m α => x * A) := fun _ _ g => by
  simpa only [Matrix.mul_assoc, Matrix.mul_one, h] using congr_arg (· * B) g

lemma mul_right_injective_of_inv (A : Matrix m n α) (B : Matrix n m α) (h : A * B = 1) :
    Function.Injective (fun x : Matrix m l α => B * x) :=
  fun _ _ g => by simpa only [← Matrix.mul_assoc, Matrix.one_mul, h] using congr_arg (A * ·) g

end InjectiveMul

section vecMul

section Semiring

variable {R : Type*} [Semiring R]

theorem vecMul_surjective_iff_exists_left_inverse
    [DecidableEq n] [Fintype m] [Finite n] {A : Matrix m n R} :
    Function.Surjective A.vecMul ↔ ∃ B : Matrix n m R, B * A = 1 := by
  cases nonempty_fintype n
  refine ⟨fun h ↦ ?_, fun ⟨B, hBA⟩ y ↦ ⟨y ᵥ* B, by simp [hBA]⟩⟩
  choose rows hrows using (h <| Pi.single · 1)
  refine ⟨Matrix.of rows, Matrix.ext fun i j => ?_⟩
  rw [mul_apply_eq_vecMul, one_eq_pi_single, ← hrows]
  rfl

theorem mulVec_surjective_iff_exists_right_inverse
    [DecidableEq m] [Finite m] [Fintype n] {A : Matrix m n R} :
    Function.Surjective A.mulVec ↔ ∃ B : Matrix n m R, A * B = 1 := by
  cases nonempty_fintype m
  refine ⟨fun h ↦ ?_, fun ⟨B, hBA⟩ y ↦ ⟨B *ᵥ y, by simp [hBA]⟩⟩
  choose cols hcols using (h <| Pi.single · 1)
  refine ⟨(Matrix.of cols)ᵀ, Matrix.ext fun i j ↦ ?_⟩
  rw [one_eq_pi_single, Pi.single_comm, ← hcols j]
  rfl

end Semiring

variable [DecidableEq m] {R K : Type*} [CommRing R] [Field K] [Fintype m]

theorem vecMul_surjective_iff_isUnit {A : Matrix m m R} :
    Function.Surjective A.vecMul ↔ IsUnit A := by
  rw [vecMul_surjective_iff_exists_left_inverse, isUnit_iff_exists_inv']

theorem mulVec_surjective_iff_isUnit {A : Matrix m m R} :
    Function.Surjective A.mulVec ↔ IsUnit A := by
  rw [mulVec_surjective_iff_exists_right_inverse, isUnit_iff_exists_inv]

theorem vecMul_injective_iff_isUnit {A : Matrix m m K} :
    Function.Injective A.vecMul ↔ IsUnit A := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← vecMul_surjective_iff_isUnit]
    exact LinearMap.surjective_of_injective (f := A.vecMulLinear) h
  exact vecMul_injective_of_isUnit h

theorem mulVec_injective_iff_isUnit {A : Matrix m m K} :
    Function.Injective A.mulVec ↔ IsUnit A := by
  rw [← isUnit_transpose, ← vecMul_injective_iff_isUnit]
  simp_rw [vecMul_transpose]

theorem linearIndependent_rows_iff_isUnit {A : Matrix m m K} :
    LinearIndependent K A.row ↔ IsUnit A := by
  rw [← col_transpose, ← mulVec_injective_iff, ← coe_mulVecLin, mulVecLin_transpose,
    ← vecMul_injective_iff_isUnit, coe_vecMulLinear]

theorem linearIndependent_cols_iff_isUnit {A : Matrix m m K} :
    LinearIndependent K A.col ↔ IsUnit A := by
  rw [← row_transpose, linearIndependent_rows_iff_isUnit, isUnit_transpose]

theorem vecMul_surjective_of_invertible (A : Matrix m m R) [Invertible A] :
    Function.Surjective A.vecMul :=
  vecMul_surjective_iff_isUnit.2 <| isUnit_of_invertible A

theorem mulVec_surjective_of_invertible (A : Matrix m m R) [Invertible A] :
    Function.Surjective A.mulVec :=
  mulVec_surjective_iff_isUnit.2 <| isUnit_of_invertible A

theorem vecMul_injective_of_invertible (A : Matrix m m K) [Invertible A] :
    Function.Injective A.vecMul :=
  vecMul_injective_iff_isUnit.2 <| isUnit_of_invertible A

theorem mulVec_injective_of_invertible (A : Matrix m m K) [Invertible A] :
    Function.Injective A.mulVec :=
  mulVec_injective_iff_isUnit.2 <| isUnit_of_invertible A

theorem linearIndependent_rows_of_invertible (A : Matrix m m K) [Invertible A] :
    LinearIndependent K A.row :=
  linearIndependent_rows_iff_isUnit.2 <| isUnit_of_invertible A

theorem linearIndependent_cols_of_invertible (A : Matrix m m K) [Invertible A] :
    LinearIndependent K A.col :=
  linearIndependent_cols_iff_isUnit.2 <| isUnit_of_invertible A

end vecMul

variable [Fintype n] [DecidableEq n] [CommRing α]
variable (A : Matrix n n α) (B : Matrix n n α)

theorem nonsingularInverse_eq_leftInverse (h : B * A = 1) :
    nonsingularInverse A (isUnit_det_of_left_inverse h) = B :=
  left_inv_eq_left_inv (nonsingularInverse_mul A _) h

theorem nonsingularInverse_eq_rightInverse (h : A * B = 1) :
    nonsingularInverse A (isUnit_det_of_right_inverse h) = B :=
  right_inv_eq_right_inv (mul_nonsingularInverse A _) h

theorem det_nonsingularInverse_mul_det (h : IsUnit A.det) :
    (nonsingularInverse A h).det * A.det = 1 := by
  rw [← det_mul, nonsingularInverse_mul A h, det_one]

@[simp]
theorem det_nonsingularInverse (h : IsUnit A.det) :
    (nonsingularInverse A h).det = (↑h.unit⁻¹ : α) := by
  have hmul := det_nonsingularInverse_mul_det A h
  rw [← h.unit_spec] at hmul
  calc
    (nonsingularInverse A h).det = (nonsingularInverse A h).det * 1 := by rw [mul_one]
    _ = (nonsingularInverse A h).det * ((h.unit : α) * (h.unit⁻¹ : α)) := by
      rw [Units.mul_inv]
    _ = ((nonsingularInverse A h).det * (h.unit : α)) * (h.unit⁻¹ : α) := by rw [mul_assoc]
    _ = (↑h.unit⁻¹ : α) := by rw [hmul, one_mul]

theorem isUnit_det_nonsingularInverse (h : IsUnit A.det) :
    IsUnit (nonsingularInverse A h).det :=
  .of_mul_eq_one _ (det_nonsingularInverse_mul_det A h)

theorem isUnit_nonsingularInverse (h : IsUnit A.det) : IsUnit (nonsingularInverse A h) :=
  isUnit_iff_isUnit_det _ |>.2 <| isUnit_det_nonsingularInverse A h

@[simp]
theorem nonsingularInverse_nonsingularInverse (h : IsUnit A.det) :
    nonsingularInverse (nonsingularInverse A h) (isUnit_det_nonsingularInverse A h) = A := by
  symm
  exact right_inv_eq_left_inv (nonsingularInverse_mul A h) (nonsingularInverse_mul _ _)

theorem nonsingularInverse_mul_distrib (hA : IsUnit A.det) (hB : IsUnit B.det) :
    nonsingularInverse (A * B) (by simpa only [det_mul] using hA.mul hB) =
      nonsingularInverse B hB * nonsingularInverse A hA := by
  apply nonsingularInverse_eq_rightInverse
  rw [mul_assoc, ← mul_assoc B, mul_nonsingularInverse, one_mul,
    mul_nonsingularInverse]

section Diagonal

attribute [local instance] Invertible.map in
/-- `diagonal v` is invertible if `v` is -/
@[instance_reducible]
def diagonalInvertible {α} [NonAssocSemiring α] (v : n → α) [Invertible v] :
    Invertible (diagonal v) :=
  inferInstanceAs <| Invertible (diagonalRingHom n α v)

theorem invOf_diagonal_eq {α} [Semiring α] (v : n → α) [Invertible v] [Invertible (diagonal v)] :
    ⅟(diagonal v) = diagonal (⅟v) := by
  rw [@Invertible.congr _ _ _ _ _ (diagonalInvertible v) rfl]
  rfl

/-- `v` is invertible if `diagonal v` is -/
@[instance_reducible]
def invertibleOfDiagonalInvertible (v : n → α) [Invertible (diagonal v)] : Invertible v where
  invOf := diag (⅟(diagonal v))
  invOf_mul_self :=
    funext fun i => by
      let : Invertible (diagonal v).det := detInvertibleOfInvertible _
      rw [invOf_eq, diag_smul, adjugate_diagonal, diag_diagonal]
      dsimp
      rw [mul_assoc, prod_erase_mul _ _ (Finset.mem_univ _), ← det_diagonal]
      exact mul_invOf_self _
  mul_invOf_self :=
    funext fun i => by
      let : Invertible (diagonal v).det := detInvertibleOfInvertible _
      rw [invOf_eq, diag_smul, adjugate_diagonal, diag_diagonal]
      dsimp
      rw [mul_left_comm, mul_prod_erase _ _ (Finset.mem_univ _), ← det_diagonal]
      exact mul_invOf_self _

/-- Together `Matrix.diagonalInvertible` and `Matrix.invertibleOfDiagonalInvertible` form an
equivalence, although both sides of the equiv are subsingleton anyway. -/
@[simps]
def diagonalInvertibleEquivInvertible (v : n → α) : Invertible (diagonal v) ≃ Invertible v where
  toFun := @invertibleOfDiagonalInvertible _ _ _ _ _ _
  invFun := @diagonalInvertible _ _ _ _ _ _
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/-- When lowered to a prop, `Matrix.diagonalInvertibleEquivInvertible` forms an `iff`. -/
@[simp]
theorem isUnit_diagonal {v : n → α} : IsUnit (diagonal v) ↔ IsUnit v := by
  simp only [← nonempty_invertible_iff_isUnit,
    (diagonalInvertibleEquivInvertible v).nonempty_congr]

end Diagonal

/-- One form of **Cramer's rule**. See `Matrix.mulVec_cramer` for a stronger form. -/
@[simp]
theorem det_smul_nonsingularInverse_mulVec_eq_cramer
    (A : Matrix n n α) (b : n → α) (h : IsUnit A.det) :
    A.det • nonsingularInverse A h *ᵥ b = cramer A b := by
  rw [cramer_eq_adjugate_mulVec, nonsingularInverse, ← smul_mulVec, smul_smul,
    h.mul_val_inv, one_smul]

/-- One form of **Cramer's rule**. See `Matrix.mulVec_cramer` for a stronger form. -/
@[simp]
theorem det_smul_vecMul_nonsingularInverse_eq_cramer_transpose
    (A : Matrix n n α) (b : n → α) (h : IsUnit A.det) :
    A.det • b ᵥ* nonsingularInverse A h = cramer Aᵀ b := by
  rw [← (nonsingularInverse A h).transpose_transpose, vecMul_transpose,
    transpose_nonsingularInverse, ← det_transpose,
    Aᵀ.det_smul_nonsingularInverse_mulVec_eq_cramer _ (isUnit_det_transpose A h)]

/-! ### Inverses of permutated matrices

Note that the simp-normal form of `Matrix.reindex` is `Matrix.submatrix`, so we prove most of these
results about only the latter.
-/


section Submatrix

variable [Fintype m]
variable [DecidableEq m]

/-- `A.submatrix e₁ e₂` is invertible if `A` is -/
@[instance_reducible]
def submatrixEquivInvertible (A : Matrix m m α) (e₁ e₂ : n ≃ m) [Invertible A] :
    Invertible (A.submatrix e₁ e₂) :=
  invertibleOfRightInverse _ ((⅟A).submatrix e₂ e₁) <| by
    rw [Matrix.submatrix_mul_equiv, mul_invOf_self, submatrix_one_equiv]

/-- `A` is invertible if `A.submatrix e₁ e₂` is -/
@[instance_reducible]
def invertibleOfSubmatrixEquivInvertible (A : Matrix m m α) (e₁ e₂ : n ≃ m)
    [Invertible (A.submatrix e₁ e₂)] : Invertible A :=
  invertibleOfRightInverse _ ((⅟(A.submatrix e₁ e₂)).submatrix e₂.symm e₁.symm) <| by
    have : A = (A.submatrix e₁ e₂).submatrix e₁.symm e₂.symm := by simp
    conv in _ * _ =>
      congr
      rw [this]
    rw [Matrix.submatrix_mul_equiv, mul_invOf_self, submatrix_one_equiv]

theorem invOf_submatrix_equiv_eq (A : Matrix m m α) (e₁ e₂ : n ≃ m) [Invertible A]
    [Invertible (A.submatrix e₁ e₂)] : ⅟(A.submatrix e₁ e₂) = (⅟A).submatrix e₂ e₁ := by
  rw [@Invertible.congr _ _ _ _ _ (submatrixEquivInvertible A e₁ e₂) rfl]
  rfl

/-- Together `Matrix.submatrixEquivInvertible` and
`Matrix.invertibleOfSubmatrixEquivInvertible` form an equivalence, although both sides of the
equiv are subsingleton anyway. -/
@[simps]
def submatrixEquivInvertibleEquivInvertible (A : Matrix m m α) (e₁ e₂ : n ≃ m) :
    Invertible (A.submatrix e₁ e₂) ≃ Invertible A where
  toFun _ := invertibleOfSubmatrixEquivInvertible A e₁ e₂
  invFun _ := submatrixEquivInvertible A e₁ e₂
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/-- When lowered to a prop, `Matrix.invertibleOfSubmatrixEquivInvertible` forms an `iff`. -/
@[simp]
theorem isUnit_submatrix_equiv {A : Matrix m m α} (e₁ e₂ : n ≃ m) :
    IsUnit (A.submatrix e₁ e₂) ↔ IsUnit A := by
  simp only [← nonempty_invertible_iff_isUnit,
    (submatrixEquivInvertibleEquivInvertible A _ _).nonempty_congr]

/-- Reindexing the rows and columns of a determinant-unit matrix preserves the determinant-unit
domain. -/
theorem isUnit_det_submatrix_equiv (A : Matrix m m α) (e₁ e₂ : n ≃ m)
    (h : IsUnit A.det) : IsUnit (A.submatrix e₁ e₂).det :=
  isUnit_iff_isUnit_det _ |>.mp <| (isUnit_submatrix_equiv e₁ e₂).2 <|
    isUnit_iff_isUnit_det A |>.2 h

@[simp]
theorem nonsingularInverse_submatrix_equiv (A : Matrix m m α) (e₁ e₂ : n ≃ m)
    (h : IsUnit A.det) :
    nonsingularInverse (A.submatrix e₁ e₂) (isUnit_det_submatrix_equiv A e₁ e₂ h) =
      (nonsingularInverse A h).submatrix e₂ e₁ := by
  apply nonsingularInverse_eq_rightInverse
  rw [Matrix.submatrix_mul_equiv, mul_nonsingularInverse, submatrix_one_equiv]

end Submatrix

end Matrix
