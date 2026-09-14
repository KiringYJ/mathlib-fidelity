import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.FinTwo

/-!
# Strict parabolic eigenvalues

These tests ensure that the eigenvalue of a parabolic matrix is exposed through the standard
`HasEigenvalue` predicate, without introducing a proof-gated scalar wrapper.
-/

open Matrix

/-- info: Unknown constant `Matrix.halfTrace` -/
#guard_msgs in
#check_failure Matrix.halfTrace

/-- info: Unknown constant `Matrix.parabolicEigenvalue` -/
#guard_msgs in
#check_failure Matrix.parabolicEigenvalue

/-- info: Unknown constant `Matrix.GeneralLinearGroup.halfTrace` -/
#guard_msgs in
#check_failure Matrix.GeneralLinearGroup.halfTrace

/-- info: Unknown constant `Matrix.GeneralLinearGroup.parabolicEigenvalue` -/
#guard_msgs in
#check_failure Matrix.GeneralLinearGroup.parabolicEigenvalue

example (m : Matrix (Fin 2) (Fin 2) ℚ) (hm : m.IsParabolic) {μ : ℚ} :
    Module.End.HasEigenvalue m.toLin' μ ↔ μ = m.trace / 2 :=
  hm.hasEigenvalue_iff_eq_trace_div_two

example (m : Matrix (Fin 2) (Fin 2) ℚ) (hm : m.IsParabolic) :
    (m - scalar _ (m.trace / 2)) ^ 2 = 0 :=
  hm.sub_trace_div_two_sq_eq_zero

example (g : GL (Fin 2) ℚ) (hg : g.IsParabolic) : g.val.trace ≠ 0 :=
  hg.trace_ne_zero

variable {K : Type*} [Field K]

example (m : Matrix (Fin 2) (Fin 2) K) (hm : m.IsParabolic) {μ ν : K}
    (hμ : Module.End.HasEigenvalue m.toLin' μ) (hν : Module.End.HasEigenvalue m.toLin' ν) :
    μ = ν :=
  hm.eigenvalue_unique hμ hν

set_option linter.unusedVariables false in
example (m : Matrix (Fin 2) (Fin 2) K) (hm : m.IsParabolic) : True := by
  fail_if_success
    have _h : Module.End.HasEigenvalue m.toLin' (m.trace / 2) :=
      hm.hasEigenvalue_trace_div_two
  trivial

variable {L : Type*} [Field L] [CharZero L]

example (m : Matrix (Fin 2) (Fin 2) L) (hm : m.IsParabolic) {μ : L} :
    Module.End.HasEigenvalue m.toLin' μ ↔ μ = m.trace / 2 :=
  hm.hasEigenvalue_iff_eq_trace_div_two

private def charTwoParabolic : Matrix (Fin 2) (Fin 2) (ZMod 2) := !![1, 1; 0, 1]

private lemma charTwoParabolic_isParabolic : charTwoParabolic.IsParabolic := by
  rw [Matrix.isParabolic_iff_of_upperTriangular (m := charTwoParabolic)
    (by simp [charTwoParabolic])]
  simp [charTwoParabolic]

private lemma charTwoParabolic_hasEigenvalue_one :
    Module.End.HasEigenvalue charTwoParabolic.toLin' 1 := by
  rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin',
    Matrix.charpoly_fin_two, Polynomial.IsRoot.def]
  simp [charTwoParabolic, Matrix.trace_fin_two, Matrix.det_fin_two]
  decide

example :
    ¬Module.End.HasEigenvalue charTwoParabolic.toLin' (charTwoParabolic.trace / 2) := by
  rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin',
    Matrix.charpoly_fin_two, Polynomial.IsRoot.def]
  simp [charTwoParabolic, Matrix.trace_fin_two, Matrix.det_fin_two]
  native_decide

example {μ : ZMod 2} (hμ : Module.End.HasEigenvalue charTwoParabolic.toLin' μ) :
    μ = 1 :=
  charTwoParabolic_isParabolic.eigenvalue_unique hμ charTwoParabolic_hasEigenvalue_one

set_option linter.unusedVariables false in
example : True := by
  fail_if_success
    have _h : Module.End.HasEigenvalue charTwoParabolic.toLin'
        (charTwoParabolic.trace / 2) :=
      charTwoParabolic_isParabolic.hasEigenvalue_trace_div_two
  trivial
