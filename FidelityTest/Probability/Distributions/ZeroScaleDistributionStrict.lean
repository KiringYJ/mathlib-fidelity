import Mathlib.Probability.Distributions.Cauchy
import Mathlib.Probability.Distributions.Gaussian.Basic

/-!
# Zero-scale Gaussian and Cauchy distributions

These tests ensure that the Gaussian densities take a proof that the variance is nonzero; that the
Cauchy distribution and its densities take a proof that the scale is nonzero, an obligation that
is false at zero; that the degenerate Gaussian distribution with variance zero is retained as a
Dirac measure, with its atom, its characteristic function, its role as the image under the zero
map and in `IsGaussian`, and its vanishing Radon-Nikodym derivative; that measurability
automation applies, including jointly in the parameters; and that values and rewriting do not
depend on the proofs.
-/

open MeasureTheory ProbabilityTheory Complex
open scoped ENNReal NNReal

noncomputable section

/-! ### The densities and the Cauchy distribution take a proof of a nonzero scale -/

/--
error: Type mismatch
  gaussianPDFReal μ v
has type
  v ≠ 0 → ℝ → ℝ
but is expected to have type
  ℝ → ℝ
-/
#guard_msgs in
example (μ : ℝ) (v : ℝ≥0) : ℝ → ℝ := gaussianPDFReal μ v

/--
error: Type mismatch
  gaussianPDF μ v
has type
  v ≠ 0 → ℝ → ℝ≥0∞
but is expected to have type
  ℝ → ℝ≥0∞
-/
#guard_msgs in
example (μ : ℝ) (v : ℝ≥0) : ℝ → ℝ≥0∞ := gaussianPDF μ v

/--
error: Type mismatch
  cauchyPDFReal x₀ γ
has type
  γ ≠ 0 → ℝ → ℝ
but is expected to have type
  ℝ → ℝ
-/
#guard_msgs in
example (x₀ : ℝ) (γ : ℝ≥0) : ℝ → ℝ := cauchyPDFReal x₀ γ

/--
error: Type mismatch
  cauchyPDF x₀ γ
has type
  γ ≠ 0 → ℝ → ℝ≥0∞
but is expected to have type
  ℝ → ℝ≥0∞
-/
#guard_msgs in
example (x₀ : ℝ) (γ : ℝ≥0) : ℝ → ℝ≥0∞ := cauchyPDF x₀ γ

/--
error: Type mismatch
  cauchyMeasure x₀ γ
has type
  γ ≠ 0 → Measure ℝ
but is expected to have type
  Measure ℝ
-/
#guard_msgs in
example (x₀ : ℝ) (γ : ℝ≥0) : Measure ℝ := cauchyMeasure x₀ γ

-- A nonnegative scale is not enough.
/--
error: Application type mismatch: The argument
  hγ
has type
  0 ≤ γ
but is expected to have type
  γ ≠ 0
in the application
  cauchyMeasure x₀ γ hγ
-/
#guard_msgs in
example (x₀ : ℝ) (γ : ℝ≥0) (hγ : 0 ≤ γ) : Measure ℝ := cauchyMeasure x₀ γ hγ

/--
error: Application type mismatch: The argument
  hv
has type
  0 ≤ v
but is expected to have type
  v ≠ 0
in the application
  gaussianPDFReal μ v hv
-/
#guard_msgs in
example (μ : ℝ) (v : ℝ≥0) (hv : 0 ≤ v) : ℝ → ℝ := gaussianPDFReal μ v hv

-- At the zero scale the obligation is `0 ≠ 0`, which is false.
/--
error: unsolved goals
x₀ : ℝ
⊢ 0 ≠ 0
-/
#guard_msgs in
example (x₀ : ℝ) : Measure ℝ := cauchyMeasure x₀ 0 (by skip)

/--
error: unsolved goals
μ : ℝ
⊢ 0 ≠ 0
-/
#guard_msgs in
example (μ : ℝ) : ℝ → ℝ := gaussianPDFReal μ 0 (by skip)

example : ¬ ((0 : ℝ≥0) ≠ 0) := by
  simp

/-! ### The degenerate Gaussian distribution is retained -/

example (μ : ℝ) : gaussianReal μ 0 = Measure.dirac μ := by
  simp

example (μ : ℝ) : IsProbabilityMeasure (gaussianReal μ 0) := inferInstance

example (μ : ℝ) : IsGaussian (gaussianReal μ 0) := inferInstance

-- The degenerate distribution has an atom, unlike the distributions with a density.
example (μ : ℝ) : gaussianReal μ 0 {μ} = 1 := by
  simp

-- A Dirac measure is Gaussian, and `IsGaussian` identifies it with the degenerate distribution.
example (x : ℝ) : Measure.dirac x = gaussianReal x 0 := by
  rw [IsGaussian.eq_gaussianReal (Measure.dirac x) inferInstance]
  simp

-- The characteristic function specifies the distribution for every variance.
example (μ t : ℝ) : charFun (gaussianReal μ 0) t = cexp (t * μ * I) := by
  rw [charFun_gaussianReal]
  simp

-- The image under the zero map is the degenerate distribution at zero.
example (μ : ℝ) (v : ℝ≥0) : (gaussianReal μ v).map (fun x ↦ 0 * x) = gaussianReal 0 0 := by
  rw [gaussianReal_map_const_mul]
  simp

-- The degenerate distribution is singular, while the others have the Gaussian density.
example (μ : ℝ) : ∂(gaussianReal μ 0)/∂volume =ₐₛ 0 :=
  rnDeriv_gaussianReal_zero_var μ

example (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) : ∂(gaussianReal μ v)/∂volume =ₐₛ gaussianPDF μ v hv :=
  rnDeriv_gaussianReal μ hv

/-! ### Instances and automation -/

example (x₀ : ℝ) {γ : ℝ≥0} (hγ : γ ≠ 0) : IsProbabilityMeasure (cauchyMeasure x₀ γ hγ) :=
  inferInstance

example (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) : Measurable (gaussianPDFReal μ v hv) := by
  fun_prop

example (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) : Measurable fun x ↦ gaussianPDF μ v hv x + 1 := by
  fun_prop

example (x₀ : ℝ) {γ : ℝ≥0} (hγ : γ ≠ 0) : Measurable (cauchyPDF x₀ γ hγ) := by
  fun_prop

-- The Gaussian densities are measurable jointly in the parameters on the nonzero variances.
example : Measurable fun p : ℝ × {v : ℝ≥0 // v ≠ 0} × ℝ ↦
    gaussianPDFReal p.1 p.2.1 p.2.1.2 p.2.2 := by
  fun_prop

example : StronglyMeasurable fun p : ℝ × {v : ℝ≥0 // v ≠ 0} × ℝ ↦
    gaussianPDF p.1 p.2.1 p.2.1.2 p.2.2 := by
  fun_prop

example : Measurable fun v : ℝ≥0 ↦ gaussianReal 0 v := by
  fun_prop

-- The total mass of a density is an unconditional simp lemma.
example (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) : ∫⁻ x, gaussianPDF μ v hv x = 1 := by
  simp

example (x₀ : ℝ) {γ : ℝ≥0} (hγ : γ ≠ 0) : ∫⁻ x, cauchyPDF x₀ γ hγ x = 1 := by
  simp

/-! ### Values and rewriting do not depend on the proofs -/

example (μ : ℝ) {v : ℝ≥0} (hv hv' : v ≠ 0) : gaussianPDFReal μ v hv = gaussianPDFReal μ v hv' :=
  rfl

example (x₀ : ℝ) {γ : ℝ≥0} (hγ hγ' : γ ≠ 0) : cauchyMeasure x₀ γ hγ = cauchyMeasure x₀ γ hγ' :=
  rfl

-- A lemma stated with one proof rewrites a goal that carries another.
example (μ : ℝ) {v : ℝ≥0} (hv hv' : v ≠ 0) (s : Set ℝ) :
    gaussianReal μ v s = ∫⁻ x in s, gaussianPDF μ v hv' x := by
  rw [gaussianReal_apply μ hv]

example (x₀ : ℝ) {γ : ℝ≥0} (hγ hγ' : γ ≠ 0) (x : ℝ) : 0 < cauchyPDFReal x₀ γ hγ' x :=
  cauchyPDFReal_pos x₀ hγ x
