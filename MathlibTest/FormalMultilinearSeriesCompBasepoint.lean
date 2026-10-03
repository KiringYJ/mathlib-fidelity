import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.OfScalars

/-!
# Constant coefficients in the composition of formal multilinear series

A formal multilinear series does not record the point at which it is expanded. In `q.comp p` the
outer series `q` is read as an expansion at the constant coefficient `p 0` of the inner series, as
for the composition of jets. Composition is therefore not the substitution of `p` into a series
expanded at the same origin.
-/

noncomputable section

open FormalMultilinearSeries

/-- Power series of `g` at `f x` and of `f` at `x` compose; the constant coefficient of the inner
series is `f x`, which need not vanish. -/
example {f g : ℝ → ℝ} {p q : FormalMultilinearSeries ℝ ℝ ℝ} {x : ℝ}
    (hg : HasFPowerSeriesAt g q (f x)) (hf : HasFPowerSeriesAt f p x) :
    HasFPowerSeriesAt (g ∘ f) (q.comp p) x ∧ p 0 (fun _ ↦ 0) = f x :=
  ⟨hg.comp hf, hf.coeff_zero _⟩

/-- The constant coefficient of the inner series only fixes the expansion point of the outer
series, so the composite does not depend on it. -/
example (q : FormalMultilinearSeries ℝ ℝ ℝ) (a : ℝ) :
    q.comp (constFormalMultilinearSeries ℝ ℝ a) = q.comp (constFormalMultilinearSeries ℝ ℝ 0) := by
  rw [← comp_removeZero q (constFormalMultilinearSeries ℝ ℝ a),
    ← comp_removeZero q (constFormalMultilinearSeries ℝ ℝ 0)]
  congr 1

/-- The series of `y ↦ y ^ 2` at `0`. -/
def squareAtZero : FormalMultilinearSeries ℝ ℝ ℝ := ofScalars ℝ fun n ↦ if n = 2 then 1 else 0

/-- Substituting the constant `1` into `y ↦ y ^ 2` would give the constant `1`. Composition
instead reads `squareAtZero` as an expansion at `1`, that is, as `y ↦ (y - 1) ^ 2`, so the
constant coefficient of the composite is `0`. -/
example : (squareAtZero.comp (constFormalMultilinearSeries ℝ ℝ 1)) 0 (fun _ ↦ 0) = 0 := by
  rw [comp_coeff_zero']
  simp [squareAtZero, ofScalars]

/-- The identity series at `x` is a right identity for every `x`. -/
example (p : FormalMultilinearSeries ℝ ℝ ℝ) (x : ℝ) : p.comp (id ℝ ℝ x) = p :=
  comp_id p x

/-- The identity series at `1` is not a left identity for a series with constant coefficient
`0`: it is the expansion at `0` of the translation `y ↦ y + 1`. -/
example : (id ℝ ℝ 1).comp (id ℝ ℝ 0) ≠ id ℝ ℝ 0 := by
  intro h
  have := congr_arg (fun q : FormalMultilinearSeries ℝ ℝ ℝ ↦ q 0 fun _ ↦ 0) h
  simp only [comp_coeff_zero', id_apply_zero] at this
  norm_num at this
