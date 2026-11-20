/-
Copyright (c) 2019 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Lu-Ming Zhang
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Invertible
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.SemiringInverse
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Nonsingular inverses

In this file, we study the inverse of a square matrix over a commutative ring.

For matrices that are not square or not of full rank, there is a more general notion of
pseudoinverses which we do not consider here.

A square matrix `A` is invertible exactly when its determinant is a unit
(`Matrix.isUnit_iff_isUnit_det`). Matrices have no ambient inverse operation: `A⁻¹` is the inverse
of `A` in the group of units of the matrix ring, and it requires the evidence `IsUnit A`. The
evidence is found from a hypothesis `IsUnit A` or `IsUnit A.det` (over a field, also `A.det ≠ 0`),
and it passes to transposes and conjugate transposes. A matrix that is not invertible has no
inverse.

The inverse is the adjugate scaled by the inverse of the determinant (`Matrix.inv_def`), and it
agrees with the constructive inverse `⅟A` of `[Invertible A]` (`Matrix.invOf_eq_nonsing_inv`).
General facts about inverses of units, such as `mul_inv_cancel₀`, `inv_inv₀`, `mul_inv_rev₀` and
`inv_eq_of_mul_eq_one_left₀`, apply to matrices directly; this file proves the facts that are
specific to matrices.

We start by working with `Invertible`, and show the main results:

* `Matrix.invertibleOfDetInvertible`
* `Matrix.detInvertibleOfInvertible`
* `Matrix.isUnit_iff_isUnit_det`
* `mul_eq_one_comm`

After this we study the inverse `A⁻¹`.

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

/- Evidence rules: a square matrix is invertible when its determinant is a unit, the determinant
of a matrix known to be invertible is a unit, and invertibility passes to the transpose and the
conjugate transpose. -/
macro_rules | `(tactic| checked_unit) => `(tactic|
    solve
    | assumption
    | ((with_reducible apply (Matrix.isUnit_iff_isUnit_det _).mpr); checked_unit)
    | ((with_reducible apply (Matrix.isUnit_iff_isUnit_det _).mp); assumption)
    | ((with_reducible apply (Matrix.isUnit_transpose _).mpr); checked_unit)
    | ((with_reducible apply (Matrix.isUnit_conjTranspose _).mpr); checked_unit))

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

section Inv

variable [Fintype n] [DecidableEq n] [CommRing α]
variable (A : Matrix n n α) (B : Matrix n n α)

theorem isUnit_det_transpose (h : IsUnit A.det) : IsUnit Aᵀ.det := by
  rw [det_transpose]
  exact h

/-! ### The inverse of an invertible matrix -/

/-- The inverse of an invertible matrix is its adjugate scaled by the inverse of its
determinant. -/
theorem inv_def {hA : IsUnit A} : A⁻¹ = A.det⁻¹ • A.adjugate := by
  refine inv_eq_of_mul_eq_one_right₀ ?_
  rw [mul_smul_comm, mul_adjugate, smul_smul, inv_mul_cancel₀, one_smul]

/-- The constructive inverse `⅟A` of an `Invertible` matrix is its inverse. -/
theorem invOf_eq_nonsing_inv [Invertible A] : ⅟A = Checked.inv A (isUnit_of_invertible A) :=
  invOf_eq_right_inv mul_inv_cancel₀

theorem transpose_nonsing_inv {hA : IsUnit A} : A⁻¹ᵀ = Aᵀ⁻¹ := by
  refine (inv_eq_of_mul_eq_one_right₀ ?_).symm
  rw [← transpose_mul, inv_mul_cancel₀, transpose_one]

theorem conjTranspose_nonsing_inv [StarRing α] {hA : IsUnit A} : A⁻¹ᴴ = Aᴴ⁻¹ := by
  refine (inv_eq_of_mul_eq_one_right₀ ?_).symm
  rw [← conjTranspose_mul, inv_mul_cancel₀, conjTranspose_one]

@[simp]
theorem mul_nonsing_inv_cancel_right {hA : IsUnit A} (B : Matrix m n α) : B * A * A⁻¹ = B := by
  rw [Matrix.mul_assoc, mul_inv_cancel₀, Matrix.mul_one]

@[simp]
theorem mul_nonsing_inv_cancel_left {hA : IsUnit A} (B : Matrix n m α) : A * (A⁻¹ * B) = B := by
  rw [← Matrix.mul_assoc, mul_inv_cancel₀, Matrix.one_mul]

@[simp]
theorem nonsing_inv_mul_cancel_right {hA : IsUnit A} (B : Matrix m n α) : B * A⁻¹ * A = B := by
  rw [Matrix.mul_assoc, inv_mul_cancel₀, Matrix.mul_one]

@[simp]
theorem nonsing_inv_mul_cancel_left {hA : IsUnit A} (B : Matrix n m α) : A⁻¹ * (A * B) = B := by
  rw [← Matrix.mul_assoc, inv_mul_cancel₀, Matrix.one_mul]

theorem inv_mul_eq_iff_eq_mul_of_invertible (A : Matrix n n α) {hA : IsUnit A}
    (B C : Matrix n m α) : A⁻¹ * B = C ↔ B = A * C :=
  ⟨fun h => by rw [← h, mul_nonsing_inv_cancel_left], fun h => by
    rw [h, nonsing_inv_mul_cancel_left]⟩

theorem mul_inv_eq_iff_eq_mul_of_invertible (A : Matrix n n α) {hA : IsUnit A}
    (B C : Matrix m n α) : B * A⁻¹ = C ↔ B = C * A :=
  ⟨fun h => by rw [← h, nonsing_inv_mul_cancel_right], fun h => by
    rw [h, mul_nonsing_inv_cancel_right]⟩

lemma inv_mulVec_eq_vec {A : Matrix n n α} {hA : IsUnit A} {u v : n → α}
    (hM : u = A.mulVec v) : A⁻¹.mulVec u = v := by
  rw [hM, Matrix.mulVec_mulVec, inv_mul_cancel₀, Matrix.one_mulVec]

/-- The inverse solves the linear system of an invertible matrix. -/
theorem mulVec_nonsing_inv_mulVec {hA : IsUnit A} (b : n → α) : A *ᵥ (A⁻¹ *ᵥ b) = b := by
  rw [mulVec_mulVec, mul_inv_cancel₀, one_mulVec]

/-- The linear system of an invertible matrix has exactly one solution. -/
theorem mulVec_eq_iff_eq_nonsing_inv_mulVec {hA : IsUnit A} (x b : n → α) :
    A *ᵥ x = b ↔ x = A⁻¹ *ᵥ b := by
  constructor
  · rintro rfl
    rw [mulVec_mulVec, inv_mul_cancel₀, one_mulVec]
  · rintro rfl
    exact mulVec_nonsing_inv_mulVec A b

lemma mul_right_injective_of_invertible [Invertible A] :
    Function.Injective (fun (x : Matrix n m α) => A * x) :=
  fun _ _ h => by simpa only [Matrix.invOf_mul_cancel_left] using congr_arg (⅟A * ·) h

lemma mul_left_injective_of_invertible [Invertible A] :
    Function.Injective (fun (x : Matrix m n α) => x * A) :=
  fun _ _ h => by simpa only [Matrix.mul_invOf_cancel_right] using congr_arg (· * ⅟A) h

lemma mul_right_inj_of_invertible [Invertible A] {x y : Matrix n m α} : A * x = A * y ↔ x = y :=
  (mul_right_injective_of_invertible A).eq_iff

lemma mul_left_inj_of_invertible [Invertible A] {x y : Matrix m n α} : x * A = y * A ↔ x = y :=
  (mul_left_injective_of_invertible A).eq_iff

lemma IsSymm.inv {A : Matrix n n α} {hAUnit : IsUnit A} (hA : A.IsSymm) : A⁻¹.IsSymm := by
  rw [inv_def]
  exact hA.adjugate.smul _

end Inv

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

theorem det_nonsing_inv_mul_det {hA : IsUnit A} : A⁻¹.det * A.det = 1 := by
  rw [← det_mul, inv_mul_cancel₀, det_one]

@[simp]
theorem det_nonsing_inv {hA : IsUnit A} : A⁻¹.det = A.det⁻¹ :=
  eq_inv_of_mul_eq_one_left₀ (det_nonsing_inv_mul_det A)

theorem isUnit_nonsing_inv_det {hA : IsUnit A} : IsUnit A⁻¹.det :=
  .of_mul_eq_one _ (det_nonsing_inv_mul_det A)

/-- A version of `Matrix.invertibleOfDetInvertible` with the inverse defeq to `A⁻¹` that is
therefore noncomputable. -/
@[instance_reducible]
noncomputable def invertibleOfIsUnitDet (h : IsUnit A.det) : Invertible A :=
  ⟨A⁻¹, inv_mul_cancel₀, mul_inv_cancel₀⟩

/-- A version of `Matrix.unitOfDetInvertible` with the inverse defeq to `A⁻¹` that is therefore
noncomputable. -/
noncomputable def nonsingInvUnit (h : IsUnit A.det) : (Matrix n n α)ˣ :=
  @unitOfInvertible _ _ _ (invertibleOfIsUnitDet A h)

@[simp, norm_cast]
theorem coe_nonsingInvUnit (h : IsUnit A.det) : (nonsingInvUnit A h : Matrix n n α) = A :=
  rfl

@[simp, norm_cast]
theorem coe_nonsingInvUnit_inv (h : IsUnit A.det) :
    (↑(nonsingInvUnit A h)⁻¹ : Matrix n n α) = A⁻¹ :=
  rfl

theorem unitOfDetInvertible_eq_nonsingInvUnit [Invertible A.det] :
    unitOfDetInvertible A = nonsingInvUnit A (isUnit_of_invertible _) := by
  ext
  rfl

variable {A} {B}

section InvEqInv

variable {C : Matrix n n α}

/-- The left inverse of matrix A is unique when existing. -/
theorem left_inv_eq_left_inv (h : B * A = 1) (g : C * A = 1) : B = C := by
  have g' : A * C = 1 := mul_eq_one_comm.2 g
  calc B = B * (A * C) := by rw [g', mul_one]
       _ = (B * A) * C := by rw [mul_assoc]
       _ = C := by rw [h, one_mul]

/-- The right inverse of matrix A is unique when existing. -/
theorem right_inv_eq_right_inv (h : A * B = 1) (g : A * C = 1) : B = C :=
  left_inv_eq_left_inv (mul_eq_one_comm.2 h) (mul_eq_one_comm.2 g)

/-- The right inverse of matrix A equals the left inverse of A when they exist. -/
theorem right_inv_eq_left_inv (h : A * B = 1) (g : C * A = 1) : B = C := by
  calc B = 1 * B := by rw [one_mul]
       _ = (C * A) * B := by rw [g]
       _ = C * (A * B) := by rw [mul_assoc]
       _ = C := by rw [h, mul_one]

end InvEqInv

variable (A)

/-- A matrix scaled by a unit is invertible exactly when the matrix is. -/
theorem isUnit_smul_iff_of_isUnit {k : α} (hk : IsUnit k) : IsUnit (k • A) ↔ IsUnit A := by
  simp only [isUnit_iff_isUnit_det, det_smul, IsUnit.mul_iff, hk.pow, true_and]

theorem inv_smul (k : α) [Invertible k] {hkA : IsUnit (k • A)} :
    (k • A)⁻¹ = ⅟k • Checked.inv A ((isUnit_smul_iff_of_isUnit A (isUnit_of_invertible k)).1 hkA) :=
  inv_eq_of_mul_eq_one_left₀ (by simp [smul_smul])

theorem inv_smul' (k : αˣ) {hkA : IsUnit (k • A)} :
    (k • A)⁻¹ = k⁻¹ • Checked.inv A ((isUnit_smul_iff_of_isUnit A k.isUnit).1 hkA) :=
  inv_eq_of_mul_eq_one_left₀ (by simp [smul_smul])

/-- The adjugate of a matrix with a unit determinant is invertible. -/
theorem isUnit_adjugate {A : Matrix n n α} (h : IsUnit A.det) : IsUnit A.adjugate := by
  rw [isUnit_iff_isUnit_det, det_adjugate]
  exact h.pow _

theorem inv_adjugate (h : IsUnit A.det) :
    Checked.inv (adjugate A) (isUnit_adjugate h) = h.unit⁻¹ • A := by
  refine inv_eq_of_mul_eq_one_left₀ ?_
  rw [smul_mul, mul_adjugate, Units.smul_def, smul_smul, h.val_inv_mul, one_smul]

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

/-- The inverse of an invertible diagonal matrix is the diagonal matrix of the entrywise
inverses. -/
theorem inv_diagonal (v : n → α) {hv : IsUnit (diagonal v)} :
    (diagonal v)⁻¹ = diagonal (Checked.inv v (isUnit_diagonal.1 hv)) := by
  have h : v * Checked.inv v (isUnit_diagonal.1 hv) = 1 := mul_inv_cancel₀
  refine inv_eq_of_mul_eq_one_right₀ ?_
  rw [diagonal_mul_diagonal]
  exact (congrArg diagonal h).trans diagonal_one'

end Diagonal

/-- The inverse of an invertible 1×1 or 0×0 matrix is diagonal.

`Matrix.diagonal_unique` can be used to reach the form of a constant matrix. -/
@[simp]
theorem inv_subsingleton [Subsingleton m] [Fintype m] [DecidableEq m] (A : Matrix m m α)
    {hA : IsUnit A} :
    A⁻¹ = diagonal fun i =>
      Checked.inv (A i i) (det_eq_elem_of_subsingleton A i ▸ (isUnit_iff_isUnit_det A).1 hA) := by
  rw [inv_def, adjugate_subsingleton, smul_one_eq_diagonal]
  congr! with i
  exact det_eq_elem_of_subsingleton _ _

section Woodbury

variable [Fintype m] [DecidableEq m]
variable (A : Matrix n n α) (U : Matrix n m α) (C : Matrix m m α) (V : Matrix m n α)

/-- If matrices `A`, `C`, and `C⁻¹ + V * A⁻¹ * U` are invertible, then so is `A + U * C * V`. -/
theorem isUnit_add_mul_mul (hA : IsUnit A) (hC : IsUnit C)
    (hAC : IsUnit (C⁻¹ + V * A⁻¹ * U)) : IsUnit (A + U * C * V) := by
  let := hA.invertible
  let := hC.invertible
  let : Invertible (⅟C + V * ⅟A * U) := by
    simpa only [invOf_eq_nonsing_inv] using hAC.invertible
  exact @isUnit_of_invertible _ _ _ (invertibleAddMulMul A U C V)

/-- The **Woodbury Identity** (`⁻¹` version).

See `add_mul_mul_inv_eq_sub'` for the binomial inverse theorem. -/
theorem add_mul_mul_inv_eq_sub (hA : IsUnit A) (hC : IsUnit C)
    (hAC : IsUnit (C⁻¹ + V * A⁻¹ * U)) :
    Checked.inv (A + U * C * V) (isUnit_add_mul_mul A U C V hA hC hAC) =
      A⁻¹ - A⁻¹ * U * (C⁻¹ + V * A⁻¹ * U)⁻¹ * V * A⁻¹ := by
  let := hA.invertible
  let := hC.invertible
  let iAC : Invertible (⅟C + V * ⅟A * U) := by
    simpa only [invOf_eq_nonsing_inv] using hAC.invertible
  let := invertibleAddMulMul A U C V
  have h := invOf_add_mul_mul A U C V
  simp only [invOf_eq_nonsing_inv] at h
  exact h

/-- If matrices `A` and `C + C * V * A⁻¹ * U * C` are invertible, then so is `A + U * C * V`. -/
theorem isUnit_add_mul_mul' (hA : IsUnit A) (h : IsUnit (C + C * V * A⁻¹ * U * C)) :
    IsUnit (A + U * C * V) := by
  let := hA.invertible
  let : Invertible (C + C * V * ⅟A * U * C) := by
    simpa only [invOf_eq_nonsing_inv] using h.invertible
  exact @isUnit_of_invertible _ _ _ (invertibleAddMulMul' A U C V)

/-- The **binomial inverse theorem** (variant of the Woodbury identity). -/
theorem add_mul_mul_inv_eq_sub' (hA : IsUnit A) (h : IsUnit (C + C * V * A⁻¹ * U * C)) :
    Checked.inv (A + U * C * V) (isUnit_add_mul_mul' A U C V hA h) =
      A⁻¹ - A⁻¹ * U * C * (C + C * V * A⁻¹ * U * C)⁻¹ * C * V * A⁻¹ := by
  let := hA.invertible
  let ih : Invertible (C + C * V * ⅟A * U * C) := by
    simpa only [invOf_eq_nonsing_inv] using h.invertible
  let := invertibleAddMulMul' A U C V
  have h' := invOf_add_mul_mul' A U C V
  simp only [invOf_eq_nonsing_inv] at h'
  exact h'

end Woodbury

/-- One form of **Cramer's rule**. See `Matrix.mulVec_cramer` for a stronger form. -/
@[simp]
theorem det_smul_inv_mulVec_eq_cramer {hA : IsUnit A} (b : n → α) :
    A.det • A⁻¹ *ᵥ b = cramer A b := by
  rw [cramer_eq_adjugate_mulVec, inv_def, ← smul_mulVec, smul_smul, mul_inv_cancel₀, one_smul]

/-- One form of **Cramer's rule**. See `Matrix.mulVec_cramer` for a stronger form. -/
@[simp]
theorem det_smul_inv_vecMul_eq_cramer_transpose {hA : IsUnit A} (b : n → α) :
    A.det • b ᵥ* A⁻¹ = cramer Aᵀ b := by
  rw [← A⁻¹.transpose_transpose, vecMul_transpose, transpose_nonsing_inv, ← det_transpose,
    det_smul_inv_mulVec_eq_cramer]

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

@[simp]
theorem inv_submatrix_equiv (A : Matrix m m α) (e₁ e₂ : n ≃ m) {hA : IsUnit (A.submatrix e₁ e₂)} :
    (A.submatrix e₁ e₂)⁻¹ =
      (Checked.inv A ((isUnit_submatrix_equiv e₁ e₂).1 hA)).submatrix e₂ e₁ := by
  refine inv_eq_of_mul_eq_one_right₀ ?_
  rw [Matrix.submatrix_mul_equiv, mul_inv_cancel₀, submatrix_one_equiv]

theorem inv_reindex (e₁ e₂ : n ≃ m) (A : Matrix n n α) {hA : IsUnit (reindex e₁ e₂ A)} :
    (reindex e₁ e₂ A)⁻¹ =
      reindex e₂ e₁ (Checked.inv A ((isUnit_submatrix_equiv e₁.symm e₂.symm).1 hA)) :=
  inv_submatrix_equiv A e₁.symm e₂.symm

end Submatrix

section Kronecker

open scoped Kronecker

variable [Fintype m] [DecidableEq m]

/-- The Kronecker product of invertible matrices is invertible. -/
theorem isUnit_kronecker {A : Matrix m m α} {B : Matrix n n α} (hA : IsUnit A) (hB : IsUnit B) :
    IsUnit (A ⊗ₖ B) := by
  rw [isUnit_iff_isUnit_det, det_kronecker]
  exact (((isUnit_iff_isUnit_det A).1 hA).pow _).mul (((isUnit_iff_isUnit_det B).1 hB).pow _)

theorem inv_kronecker (A : Matrix m m α) (B : Matrix n n α) (hA : IsUnit A) (hB : IsUnit B) :
    Checked.inv (A ⊗ₖ B) (isUnit_kronecker hA hB) = A⁻¹ ⊗ₖ B⁻¹ := by
  refine inv_eq_of_mul_eq_one_right₀ ?_
  rw [← mul_kronecker_mul, mul_inv_cancel₀, mul_inv_cancel₀, one_kronecker_one]

end Kronecker

/-! ### More results about determinants -/


section Det

variable [Fintype m] [DecidableEq m]

/-- A variant of `Matrix.det_units_conj`. -/
theorem det_conj {M : Matrix m m α} {hM : IsUnit M} (N : Matrix m m α) :
    det (M * N * M⁻¹) = det N := by
  rw [det_mul, det_mul, mul_right_comm, ← det_mul, mul_inv_cancel₀, det_one, one_mul]

/-- A variant of `Matrix.det_units_conj'`. -/
theorem det_conj' {M : Matrix m m α} {hM : IsUnit M} (N : Matrix m m α) :
    det (M⁻¹ * N * M) = det N := by
  rw [det_mul, det_mul, mul_right_comm, ← det_mul, inv_mul_cancel₀, det_one, one_mul]

end Det

/-! ### More results about traces -/


section trace

variable [Fintype m] [DecidableEq m]

/-- A variant of `Matrix.trace_units_conj`. -/
theorem trace_conj {M : Matrix m m α} {hM : IsUnit M} (N : Matrix m m α) :
    trace (M * N * M⁻¹) = trace N := by
  rw [trace_mul_comm, ← Matrix.mul_assoc, inv_mul_cancel₀, Matrix.one_mul]

/-- A variant of `Matrix.trace_units_conj'`. -/
theorem trace_conj' {M : Matrix m m α} {hM : IsUnit M} (N : Matrix m m α) :
    trace (M⁻¹ * N * M) = trace N := by
  rw [Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc, mul_inv_cancel₀, Matrix.mul_one]

end trace

end Matrix
