import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Beta
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.Distributions.Pareto

/-!
# Parameter domains of parametric distributions

These tests ensure that the gamma, exponential, Pareto, beta, and geometric distributions, their
densities, and the beta normalizing constant take proofs of their exact parameter domains; that
the probability instance follows from the proofs in the term, without a local `haveI`; that the
degenerate geometric distribution with success probability one is included; that the exponential
distribution is still the gamma distribution with shape one; and that values and rewriting do not
depend on the proofs.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology

noncomputable section

/-! ### The domain is enforced -/

/--
error: Type mismatch
  gammaMeasure a r
has type
  0 < a → 0 < r → Measure ℝ
but is expected to have type
  Measure ℝ
-/
#guard_msgs in
example (a r : ℝ) : Measure ℝ := gammaMeasure a r

/--
error: Type mismatch
  expMeasure r
has type
  0 < r → Measure ℝ
but is expected to have type
  Measure ℝ
-/
#guard_msgs in
example (r : ℝ) : Measure ℝ := expMeasure r

/--
error: Type mismatch
  paretoMeasure t r
has type
  0 < t → 0 < r → Measure ℝ
but is expected to have type
  Measure ℝ
-/
#guard_msgs in
example (t r : ℝ) : Measure ℝ := paretoMeasure t r

/--
error: Type mismatch
  betaMeasure α β
has type
  0 < α → 0 < β → Measure ℝ
but is expected to have type
  Measure ℝ
-/
#guard_msgs in
example (α β : ℝ) : Measure ℝ := betaMeasure α β

/--
error: Type mismatch
  geometricMeasure p
has type
  p ≠ 0 → Measure ℕ
but is expected to have type
  Measure ℕ
-/
#guard_msgs in
example (p : unitInterval) : Measure ℕ := geometricMeasure p

-- The densities and the beta normalizing constant carry the same domain.
/--
error: Type mismatch
  gammaPDFReal a r
has type
  0 < a → 0 < r → ℝ → ℝ
but is expected to have type
  ℝ → ℝ
-/
#guard_msgs in
example (a r : ℝ) : ℝ → ℝ := gammaPDFReal a r

/--
error: Type mismatch
  exponentialPDF r
has type
  0 < r → ℝ → ℝ≥0∞
but is expected to have type
  ℝ → ℝ≥0∞
-/
#guard_msgs in
example (r : ℝ) : ℝ → ℝ≥0∞ := exponentialPDF r

/--
error: Type mismatch
  paretoPDFReal t r
has type
  0 < t → 0 < r → ℝ → ℝ
but is expected to have type
  ℝ → ℝ
-/
#guard_msgs in
example (t r : ℝ) : ℝ → ℝ := paretoPDFReal t r

/--
error: Type mismatch
  betaPDF α β
has type
  0 < α → 0 < β → ℝ → ℝ≥0∞
but is expected to have type
  ℝ → ℝ≥0∞
-/
#guard_msgs in
example (α β : ℝ) : ℝ → ℝ≥0∞ := betaPDF α β

/--
error: Type mismatch
  beta α β
has type
  0 < α → 0 < β → ℝ
but is expected to have type
  ℝ
-/
#guard_msgs in
example (α β : ℝ) : ℝ := ProbabilityTheory.beta α β

-- Nonnegative parameters are not enough: a zero parameter has no distribution.
/--
error: Application type mismatch: The argument
  ha
has type
  0 ≤ a
but is expected to have type
  0 < a
in the application
  gammaMeasure a r ha
-/
#guard_msgs in
example (a r : ℝ) (ha : 0 ≤ a) (hr : 0 < r) : Measure ℝ := gammaMeasure a r ha hr

/--
error: Application type mismatch: The argument
  hr
has type
  0 ≤ r
but is expected to have type
  0 < r
in the application
  expMeasure r hr
-/
#guard_msgs in
example (r : ℝ) (hr : 0 ≤ r) : Measure ℝ := expMeasure r hr

/--
error: Application type mismatch: The argument
  ht
has type
  0 ≤ t
but is expected to have type
  0 < t
in the application
  paretoMeasure t r ht
-/
#guard_msgs in
example (t r : ℝ) (ht : 0 ≤ t) (hr : 0 < r) : Measure ℝ := paretoMeasure t r ht hr

/--
error: Application type mismatch: The argument
  hβ
has type
  0 ≤ β
but is expected to have type
  0 < β
in the application
  betaMeasure α β hα hβ
-/
#guard_msgs in
example (α β : ℝ) (hα : 0 < α) (hβ : 0 ≤ β) : Measure ℝ := betaMeasure α β hα hβ

-- The excluded geometric parameter is `p = 0`, not the other endpoint `p = 1`.
/--
error: Application type mismatch: The argument
  hp
has type
  p ≠ 1
but is expected to have type
  p ≠ 0
in the application
  geometricMeasure p hp
-/
#guard_msgs in
example (p : unitInterval) (hp : p ≠ 1) : Measure ℕ := geometricMeasure p hp

/-! ### The probability instance comes from the proofs in the term -/

example {a r : ℝ} (ha : 0 < a) (hr : 0 < r) : IsProbabilityMeasure (gammaMeasure a r ha hr) :=
  inferInstance

example {r : ℝ} (hr : 0 < r) : IsProbabilityMeasure (expMeasure r hr) := inferInstance

example {t r : ℝ} (ht : 0 < t) (hr : 0 < r) : IsProbabilityMeasure (paretoMeasure t r ht hr) :=
  inferInstance

example {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) : IsProbabilityMeasure (betaMeasure α β hα hβ) :=
  inferInstance

example {p : unitInterval} (hp : p ≠ 0) : IsProbabilityMeasure (geometricMeasure p hp) :=
  inferInstance

example : IsProbabilityMeasure (gammaMeasure 2 3 (by norm_num) (by norm_num)) := inferInstance

-- The instances can also be applied to the proofs directly.
example {a r : ℝ} (ha : 0 < a) (hr : 0 < r) : IsProbabilityMeasure (gammaMeasure a r ha hr) :=
  isProbabilityMeasure_gammaMeasure ha hr

-- The cdf and its probability statements need no local instance.
example {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (x : ℝ) :
    cdf (gammaMeasure a r ha hr) x = ∫ y in Iic x, gammaPDFReal a r ha hr y :=
  cdf_gammaMeasure_eq_integral ha hr x

example {t r : ℝ} (ht : 0 < t) (hr : 0 < r) (x : ℝ) : cdf (paretoMeasure t r ht hr) x ≤ 1 :=
  cdf_le_one _ x

example {r : ℝ} (hr : 0 < r) : Tendsto (cdf (expMeasure r hr)) atTop (𝓝 1) :=
  tendsto_cdf_atTop _

example {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) : betaMeasure α β hα hβ univ = 1 :=
  measure_univ

/-! ### The degenerate geometric distribution is included -/

example : geometricMeasure 1 one_ne_zero = Measure.dirac 0 := by
  rw [Measure.ext_iff_singleton]
  intro n
  rw [geometricMeasure_singleton]
  cases n <;> simp

/-! ### The exponential distribution is the gamma distribution with shape one -/

example {r : ℝ} (hr : 0 < r) : expMeasure r hr = gammaMeasure 1 r one_pos hr :=
  rfl

example {r : ℝ} (hr : 0 < r) : exponentialPDFReal r hr = gammaPDFReal 1 r one_pos hr :=
  rfl

/-! ### Automation applies to the densities -/

example {a r : ℝ} (ha : 0 < a) (hr : 0 < r) : Measurable (gammaPDFReal a r ha hr) := by
  fun_prop

example {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    Measurable fun x ↦ betaPDFReal α β hα hβ x + 1 := by
  fun_prop

-- The total mass of a density is an unconditional simp lemma.
example {a r : ℝ} (ha : 0 < a) (hr : 0 < r) : ∫⁻ x, gammaPDF a r ha hr x = 1 := by
  simp

example {r : ℝ} (hr : 0 < r) : ∫⁻ x, exponentialPDF r hr x = 1 := by
  simp

example {t r : ℝ} (ht : 0 < t) (hr : 0 < r) : ∫⁻ x, paretoPDF t r ht hr x = 1 := by
  simp

example {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) : ∫⁻ x, betaPDF α β hα hβ x = 1 := by
  simp

/-! ### Values and rewriting do not depend on the proofs -/

example {a r : ℝ} (ha ha' : 0 < a) (hr hr' : 0 < r) :
    gammaMeasure a r ha hr = gammaMeasure a r ha' hr' :=
  rfl

example {α β : ℝ} (hα hα' : 0 < α) (hβ hβ' : 0 < β) :
    betaPDFReal α β hα hβ = betaPDFReal α β hα' hβ' :=
  rfl

example {p : unitInterval} (hp hp' : p ≠ 0) : geometricMeasure p hp = geometricMeasure p hp' :=
  rfl

-- A lemma stated with some proofs rewrites a goal that carries others.
example {a r : ℝ} (ha ha' : 0 < a) (hr hr' : 0 < r) (x : ℝ) :
    cdf (gammaMeasure a r ha' hr') x = ∫ y in Iic x, gammaPDFReal a r ha hr y := by
  rw [cdf_gammaMeasure_eq_integral ha hr]

example {p : unitInterval} (hp hp' : p ≠ 0) (n : ℕ) :
    geometricMeasure p hp' {n} = ENNReal.ofReal ((1 - p) ^ n * p) := by
  rw [geometricMeasure_singleton hp]

-- `rw [h]` cannot replace a parameter below its proof; `simp only [h]` and `subst` can.
example {a b r : ℝ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (h : a = b) (x : ℝ) :
    cdf (gammaMeasure a r ha hr) x = cdf (gammaMeasure b r hb hr) x := by
  simp only [h]

example {a b r : ℝ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (h : a = b) :
    gammaMeasure a r ha hr = gammaMeasure b r hb hr := by
  subst h
  rfl
