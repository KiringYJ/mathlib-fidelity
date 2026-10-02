import Mathlib.NumberTheory.NumberField.DirichletDensity.Asymptotics

/-!
# Certified Dirichlet density fibers

These tests ensure that `HasDirichletDensity` is the ordinary proposition-valued API and that
`DirichletDensity S` carries an explicit certified value rather than extracting one from mere
propositional existence. Ordinary theorems continue to use a real number and its
`HasDirichletDensity` proof directly. The analytic tests check normalization on the right of
`1` and decomposition into a set and its complement using genuine convergent series.
-/

open IsDedekindDomain NumberField

open scoped Topology

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

-- The full set has density exactly one, so its certified fiber cannot contain zero.
example : ¬ HasDirichletDensity (Set.univ : Set (HeightOneSpectrum (𝓞 K))) 0 := by
  intro h
  have := h.unique hasDirichletDensity_univ
  norm_num at this

-- Convergence of the ambient series propagates to an arbitrary set and its complement.
example {s : ℝ} (hs : 1 < s) :
    S.primeIdealZetaSum s + Sᶜ.primeIdealZetaSum s =
      (Set.univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s := by
  simp only [primeIdealZetaSum_def]
  rw [tsum_univ fun p : HeightOneSpectrum (𝓞 K) ↦ (p.asIdeal.absNorm : ℝ) ^ (-s)]
  exact (summable_primeIdealZeta K hs).tsum_subtype_add_tsum_subtype_compl S

-- A nonempty set contributes a strictly positive numerator on the convergence half-line.
example (p : HeightOneSpectrum (𝓞 K)) :
    0 < ({p} : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum 2 := by
  exact primeIdealZetaSum_pos (Set.singleton_nonempty p) (by norm_num)

-- Values outside the convergence half-line cannot affect the density relation.
example {δ : ℝ} (h : S.HasDirichletDensity δ) :
    Filter.Tendsto (fun s : ℝ ↦ if 1 < s then S.primeIdealZetaSum s /
      (Set.univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s else 37)
      (𝓝[>] 1) (𝓝 δ) := by
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (ite_eq_left hs).symm

-- A proof in the logarithmic normalization constructs the same certified density fiber.
example {δ : ℝ} (h : Filter.Tendsto
    (fun s : ℝ ↦ S.primeIdealZetaSum s / Real.log (1 / (s - 1)))
    (𝓝[>] 1) (𝓝 δ)) : S.DirichletDensity :=
  (hasDirichletDensity_iff_tendsto_div_log.mpr h).toDirichletDensity

-- Every certified density of a finite set is zero, without choosing a density value.
example (hS : S.Finite) (d : S.DirichletDensity) : (d : ℝ) = 0 :=
  d.hasDirichletDensity.unique (hasDirichletDensity_of_finite hS)

end NumberField.Set
