import Mathlib.Analysis.Meromorphic.Germ

open AnalyticGerm MeromorphicGerm

noncomputable section

-- A vanishing denominator is nonzero in the germ field, so cancellation is valid.
private theorem coordinateUnit : IsUnit (ofAnalytic (coordinate 0)) :=
  (ofAnalytic_ne_zero.mpr (coordinate_ne_zero 0)).isUnit

example : Checked.div (ofAnalytic (coordinate 0)) (ofAnalytic (coordinate 0)) coordinateUnit =
    (1 : MeromorphicGerm 0) :=
  MeromorphicGerm.div_self _ (coordinate_ne_zero 0)

-- The canceled germ evaluates to one at the center.
example :
    MeromorphicGerm.eval
      ⟨Checked.div (ofAnalytic (coordinate 0)) (ofAnalytic (coordinate 0)) coordinateUnit,
        by
          rw [MeromorphicGerm.div_self _ (coordinate_ne_zero 0)]
          exact (regularSubring 0).one_mem⟩ =
      1 := by
  apply Eq.trans _ (map_one (MeromorphicGerm.eval (z := 0)))
  exact congrArg MeromorphicGerm.eval
    (Subtype.ext (MeromorphicGerm.div_self _ (coordinate_ne_zero 0)))

-- An actual reciprocal of the coordinate has a genuine pole.
example : Checked.inv (ofAnalytic (coordinate 0)) coordinateUnit ∉ regularSubring 0 :=
  not_regular_of_mul_eq_one (eval_coordinate 0) mul_inv_cancel₀

-- The zero germ cannot acquire an inverse through passage to fractions.
example (g : MeromorphicGerm 0) : ofAnalytic 0 * g ≠ 1 := by simp
