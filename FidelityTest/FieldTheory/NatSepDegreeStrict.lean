import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure

/-!
# The separable degree takes a nonzero polynomial

`Polynomial.natSepDegree f hf` counts the distinct roots of a nonzero polynomial `f` in its
splitting field, and `nonzero_tac` finds the proof `hf`. The zero polynomial has no finite set of
roots, so it has no separable degree; the statements about minimal polynomials carry the
integrality of the element.
-/

open Polynomial

/-! The lemmas about the former value at `0` are removed. -/

/-- info: Unknown constant `Polynomial.natSepDegree_zero` -/
#guard_msgs in
#check_failure Polynomial.natSepDegree_zero

/-- info: Unknown constant `Polynomial.natSepDegree_of_ne_zero` -/
#guard_msgs in
#check_failure Polynomial.natSepDegree_of_ne_zero

/-! The default discharger handles hypotheses, monic and separable polynomials, and products. -/

example (F : Type*) [Field F] (x : F) : (X - C x).natSepDegree = 1 := natSepDegree_X_sub_C x

example (F : Type*) [Field F] (f : F[X]) (hf : f ≠ 0) : f.natSepDegree ≤ f.natDegree :=
  natSepDegree_le_natDegree f hf

example (F : Type*) [Field F] (f : F[X]) (h : f.Separable) : f.natSepDegree = f.natDegree :=
  natSepDegree_eq_natDegree_of_separable f h

example (F : Type*) [Field F] (f g : F[X]) (hf : f ≠ 0) (hg : g ≠ 0) (h : IsCoprime f g) :
    (f * g).natSepDegree = f.natSepDegree + g.natSepDegree :=
  natSepDegree_mul_of_isCoprime f g hf hg h

example (F : Type*) [Field F] (f g : F[X]) (hf : f ≠ 0) (hg : g ≠ 0) :
    (f * g).natSepDegree = f.natSepDegree + g.natSepDegree ↔ IsCoprime f g :=
  natSepDegree_mul_eq_iff f g hf hg

/-! Without a proof that the polynomial is nonzero, there is no separable degree. -/

/--
error: could not synthesize default value for parameter 'hf' using tactics
---
error: the polynomial must be nonzero
F : Type u_1
inst✝ : Field F
f : F[X]
⊢ f ≠ 0
-/
#guard_msgs in
noncomputable example (F : Type*) [Field F] (f : F[X]) : ℕ := f.natSepDegree

/-! The characterizations through minimal polynomials carry the integrality of the element. -/

example (F E : Type*) [Field F] [Field E] [Algebra F E] (q : ℕ) [ExpChar F q] (x : E) :
    (∃ hx : IsIntegral F x, (minpoly F x).natSepDegree (minpoly.ne_zero hx) = 1) ↔
      ∃ n : ℕ, x ^ q ^ n ∈ (algebraMap F E).range :=
  minpoly.natSepDegree_eq_one_iff_pow_mem q

example (F E : Type*) [Field F] [Field E] [Algebra F E] [IsPurelyInseparable F E] (x : E) :
    (minpoly F x).natSepDegree = 1 :=
  IsPurelyInseparable.natSepDegree_eq_one F x
