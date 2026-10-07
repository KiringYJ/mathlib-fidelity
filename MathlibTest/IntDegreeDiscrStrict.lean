import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.LinearAlgebra.Matrix.Charpoly.Disc

/-!
# The degree of a rational function and the discriminant take their domains

`RatFunc.intDegree x hx` is the degree of a nonzero rational function: the zero rational function
has degree `⊥`, as the zero polynomial does. `Polynomial.discr f hf` is the discriminant of a
polynomial of positive degree: a constant polynomial has no discriminant, and there is no common
convention for one. `Matrix.discr` is `1` when the characteristic polynomial is constant, the
empty product of the squared differences of the eigenvalues.
-/

open Polynomial

/-! The lemmas that stated the former values are removed. -/

/-- info: Unknown constant `RatFunc.intDegree_zero` -/
#guard_msgs in
#check_failure RatFunc.intDegree_zero

/-- info: Unknown constant `Polynomial.discr_C` -/
#guard_msgs in
#check_failure Polynomial.discr_C

/-! The degree of a nonzero rational function. -/

example (K : Type*) [Field K] (x y : RatFunc K) (hx : x ≠ 0) (hy : y ≠ 0) :
    (x * y).intDegree (mul_ne_zero hx hy) = x.intDegree + y.intDegree :=
  RatFunc.intDegree_mul hx hy

example (K : Type*) [Field K] : RatFunc.intDegree (RatFunc.X : RatFunc K) RatFunc.X_ne_zero = 1 :=
  RatFunc.intDegree_X

example (K : Type*) [Field K] (x : RatFunc K) (hx : x ≠ 0) :
    x⁻¹.intDegree (inv_ne_zero hx) = -x.intDegree :=
  RatFunc.intDegree_inv hx

/-! The discriminant of a polynomial of positive degree. -/

example (R : Type*) [CommRing R] (f : R[X]) (hf : f.degree = 2) (h : 0 < f.natDegree) :
    f.discr = f.coeff 1 ^ 2 - 4 * f.coeff 0 * f.coeff 2 :=
  discr_of_degree_eq_two hf

example (R : Type*) [CommRing R] (f : R[X]) (hf : f.degree = 1) (h : 0 < f.natDegree) :
    f.discr = 1 :=
  discr_of_degree_eq_one hf

example (R : Type*) [CommRing R] (A : Matrix (Fin 2) (Fin 2) R) :
    A.discr = A.trace ^ 2 - 4 * A.det :=
  A.discr_fin_two

/-! Without the domain there is no degree and no discriminant. -/

/--
error: could not synthesize default value for parameter 'hx' using tactics
---
error: Tactic `assumption` failed

K : Type u_1
inst✝ : Field K
x : RatFunc K
⊢ x ≠ 0
-/
#guard_msgs in
noncomputable example (K : Type*) [Field K] (x : RatFunc K) : ℤ := x.intDegree

/--
error: could not synthesize default value for parameter 'hf' using tactics
---
error: Tactic `assumption` failed

R : Type u_1
inst✝ : CommRing R
f : R[X]
⊢ 0 < f.natDegree
-/
#guard_msgs in
noncomputable example (R : Type*) [CommRing R] (f : R[X]) : R := f.discr

/-! A `0 × 0` matrix has discriminant `1`. -/

example (R : Type*) [CommRing R] (A : Matrix (Fin 0) (Fin 0) R) : A.discr = 1 := by
  simp [Matrix.discr, Matrix.charpoly]
