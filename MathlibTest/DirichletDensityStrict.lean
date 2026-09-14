import Mathlib.NumberTheory.NumberField.DirichletDensity

/-!
# Certified Dirichlet density fibers

These tests ensure that `HasDirichletDensity` is the ordinary proposition-valued API and that
`DirichletDensity S` carries an explicit certified value rather than extracting one from mere
propositional existence. Ordinary theorems continue to use a real number and its
`HasDirichletDensity` proof directly.
-/

open IsDedekindDomain NumberField

namespace NumberField.Set

variable {K : Type*} [Field K] [NumberField K]
  {S : Set (HeightOneSpectrum (𝓞 K))}

set_option linter.unusedVariables false in
example (S : Set (HeightOneSpectrum (𝓞 K))) : True := by
  fail_if_success
    let _δ : ℝ := S.dirichletDensity
  trivial

example {δ : ℝ} (h : S.HasDirichletDensity δ) : S.DirichletDensity :=
  h.toDirichletDensity

example (d : S.DirichletDensity) : ℝ :=
  d

example (d : S.DirichletDensity) : S.HasDirichletDensity (d : ℝ) :=
  d.hasDirichletDensity

example (d e : S.DirichletDensity) : d = e :=
  Subsingleton.elim d e

example {δ : ℝ} (h : S.HasDirichletDensity δ) :
    (h.toDirichletDensity : ℝ) = δ := by
  simp

example : Nonempty S.DirichletDensity ↔ ∃ δ, S.HasDirichletDensity δ :=
  nonempty_dirichletDensity_iff

example : ((hasDirichletDensity_empty.toDirichletDensity :
    DirichletDensity (∅ : Set (HeightOneSpectrum (𝓞 K)))) : ℝ) = 0 := by
  simp

example (d : S.DirichletDensity) : 0 ≤ (d : ℝ) ∧ (d : ℝ) ≤ 1 :=
  ⟨d.hasDirichletDensity.nonneg, d.hasDirichletDensity.le_one⟩

end NumberField.Set
