import Mathlib.Probability.BrownianMotion.GaussianProjectiveFamily

/-!
# Covariance domain of the multivariate Gaussian distribution

These tests ensure that `multivariateGaussian` takes a proof that its covariance matrix is
positive semidefinite, symmetry included; that this obligation is false for an indefinite matrix
and for a matrix that is not symmetric but has a nonnegative quadratic form, which no measure has
as its covariance matrix and which the characteristic function formula cannot tell apart from its
symmetric part; that a Gaussian measure with the given mean and covariance matrix is
`multivariateGaussian`; that singular covariance matrices are retained, including the zero matrix
and the finite-dimensional distributions of Brownian motion at times including zero; that the
instances follow from the proof in the term; that measurability automation applies, jointly in
the parameters; and that values and rewriting do not depend on the proof.
-/

open MeasureTheory ProbabilityTheory Matrix Complex
open scoped RealInnerProductSpace NNReal

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The covariance matrix carries a proof of positive semidefiniteness -/

/--
error: Type mismatch
  multivariateGaussian μ S
has type
  S.PosSemidef → Measure (EuclideanSpace ℝ ι)
but is expected to have type
  Measure (EuclideanSpace ℝ ι)
-/
#guard_msgs in
example (μ : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) : Measure (EuclideanSpace ℝ ι) :=
  multivariateGaussian μ S

-- Symmetry alone is not enough.
/--
error: Application type mismatch: The argument
  hS
has type
  S.IsHermitian
but is expected to have type
  S.PosSemidef
in the application
  multivariateGaussian μ S hS
-/
#guard_msgs in
example (μ : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) (hS : S.IsHermitian) :
    Measure (EuclideanSpace ℝ ι) :=
  multivariateGaussian μ S hS

-- An indefinite matrix has no proof, and no measure has it as its covariance matrix, because
-- variances are nonnegative.
example : ¬ (diagonal ![(1 : ℝ), -1]).PosSemidef := by
  simp [Fin.forall_fin_two]

example (ν : Measure (EuclideanSpace ℝ (Fin 2))) :
    ¬ ∀ x y, covarianceBilin ν x y = x ⬝ᵥ diagonal ![(1 : ℝ), -1] *ᵥ y := by
  intro h
  have := covarianceBilin_self_nonneg (μ := ν) (EuclideanSpace.single 1 1)
  rw [h] at this
  norm_num [dotProduct, mulVec, diagonal, Fin.sum_univ_two] at this

/-- A matrix that is not symmetric but has the quadratic form of the identity matrix. -/
def nonsymmetric : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; -1, 1]

lemma dotProduct_nonsymmetric_mulVec (x : Fin 2 → ℝ) :
    x ⬝ᵥ nonsymmetric *ᵥ x = x ⬝ᵥ (1 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ x := by
  simp [nonsymmetric, dotProduct, mulVec, Fin.sum_univ_two]
  ring

example (x : Fin 2 → ℝ) : 0 ≤ x ⬝ᵥ nonsymmetric *ᵥ x := by
  rw [dotProduct_nonsymmetric_mulVec]
  exact PosSemidef.one.dotProduct_mulVec_nonneg x

example : ¬ nonsymmetric.PosSemidef := by
  intro h
  have := congrFun (congrFun h.isHermitian 0) 1
  norm_num [nonsymmetric, conjTranspose_apply] at this

-- The characteristic function formula only sees the symmetric part of the matrix: with
-- `nonsymmetric` it is the characteristic function of `multivariateGaussian μ 1 _`.
example (μ x : EuclideanSpace ℝ (Fin 2)) :
    charFun (multivariateGaussian μ 1 PosSemidef.one) x =
      exp (⟪x, μ⟫ * I - x ⬝ᵥ nonsymmetric *ᵥ x / 2) := by
  rw [charFun_multivariateGaussian, dotProduct_nonsymmetric_mulVec]

-- No measure has `nonsymmetric` as its covariance matrix, because covariances are symmetric.
example (ν : Measure (EuclideanSpace ℝ (Fin 2))) :
    ¬ ∀ x y, covarianceBilin ν x y = x ⬝ᵥ nonsymmetric *ᵥ y := by
  intro h
  have := covarianceBilin_comm (μ := ν) (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1)
  rw [h, h] at this
  norm_num [nonsymmetric, dotProduct, mulVec, Fin.sum_univ_two] at this

/-! ### The mean and the covariance matrix determine the distribution -/

example (μ : EuclideanSpace ℝ ι) {S : Matrix ι ι ℝ} (hS : S.PosSemidef)
    (ν : Measure (EuclideanSpace ℝ ι)) [IsGaussian ν] (hm : ν[id] = μ)
    (hc : ∀ x y, covarianceBilin ν x y = x ⬝ᵥ S *ᵥ y) : ν = multivariateGaussian μ S hS :=
  IsGaussian.ext (by rw [hm, integral_id_multivariateGaussian' hS])
    (by ext x y; rw [hc, covarianceBilin_multivariateGaussian hS])

/-! ### Singular covariance matrices are retained -/

-- The zero covariance matrix gives the Dirac measure at the mean, for any proof.
example (μ : EuclideanSpace ℝ ι) (h : (0 : Matrix ι ι ℝ).PosSemidef) :
    multivariateGaussian μ 0 h = Measure.dirac μ := by
  simp

example (μ : EuclideanSpace ℝ ι) : IsGaussian (multivariateGaussian μ 0 PosSemidef.zero) :=
  inferInstance

-- The coordinate of Brownian motion at time zero vanishes almost surely, so its covariance matrix
-- at the times `0` and `1` is singular.
example : MeasurePreserving (fun x : ({0, 1} : Finset ℝ≥0) → ℝ ↦ x ⟨0, by simp⟩)
    (BrownianReal.projectiveFamily {0, 1}) (Measure.dirac 0) := by
  simpa using BrownianReal.measurePreserving_eval_projectiveFamily (I := {0, 1}) ⟨0, by simp⟩

/-! ### Instances and statements use the proof in the term -/

example (μ : EuclideanSpace ℝ ι) {S : Matrix ι ι ℝ} (hS : S.PosSemidef) :
    IsGaussian (multivariateGaussian μ S hS) :=
  inferInstance

example (μ : EuclideanSpace ℝ ι) {S : Matrix ι ι ℝ} (hS : S.PosSemidef) :
    IsProbabilityMeasure (multivariateGaussian μ S hS) :=
  inferInstance

example (μ : EuclideanSpace ℝ ι) {S : Matrix ι ι ℝ} (hS : S.PosSemidef) :
    ∫ x, x ∂(multivariateGaussian μ S hS) = μ := by
  simp

example (μ : EuclideanSpace ℝ ι) {S : Matrix ι ι ℝ} (hS : S.PosSemidef) (i j : ι) :
    cov[fun x ↦ x i, fun x ↦ x j; multivariateGaussian μ S hS] = S i j :=
  covariance_eval_multivariateGaussian hS i j

-- The standard Gaussian distribution is recovered for any proof about the identity matrix.
example (h : (1 : Matrix ι ι ℝ).PosSemidef) :
    multivariateGaussian 0 1 h = stdGaussian (EuclideanSpace ℝ ι) := by
  simp

/-! ### Measurability automation -/

-- The distribution is measurable jointly in the parameters on the positive semidefinite matrices.
example : Measurable fun p : EuclideanSpace ℝ ι × {S : Matrix ι ι ℝ // S.PosSemidef} ↦
    multivariateGaussian p.1 p.2.1 p.2.2 := by
  fun_prop

example {S : Matrix ι ι ℝ} (hS : S.PosSemidef) :
    Measurable fun μ : EuclideanSpace ℝ ι ↦ multivariateGaussian μ S hS := by
  fun_prop

/-! ### Values and rewriting do not depend on the proof -/

example (μ : EuclideanSpace ℝ ι) {S : Matrix ι ι ℝ} (hS hS' : S.PosSemidef) :
    multivariateGaussian μ S hS = multivariateGaussian μ S hS' :=
  rfl

-- A lemma stated with one proof rewrites a goal that carries another.
example (μ x : EuclideanSpace ℝ ι) {S : Matrix ι ι ℝ} (hS hS' : S.PosSemidef) :
    charFun (multivariateGaussian μ S hS') x = exp (⟪x, μ⟫ * I - x ⬝ᵥ S *ᵥ x / 2) := by
  rw [charFun_multivariateGaussian hS]

-- `rw [h]` cannot replace the matrix below its proof; `simp only [h]` and `subst` can.
example (μ : EuclideanSpace ℝ ι) {S T : Matrix ι ι ℝ} (hS : S.PosSemidef) (hT : T.PosSemidef)
    (h : S = T) :
    ∫ x, x ∂(multivariateGaussian μ S hS) = ∫ x, x ∂(multivariateGaussian μ T hT) := by
  simp only [h]

example (μ : EuclideanSpace ℝ ι) {S T : Matrix ι ι ℝ} (hS : S.PosSemidef) (hT : T.PosSemidef)
    (h : S = T) : multivariateGaussian μ S hS = multivariateGaussian μ T hT := by
  subst h
  rfl
