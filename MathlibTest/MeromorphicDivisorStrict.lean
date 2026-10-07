import Mathlib.Analysis.Complex.ValueDistribution.Cartan
import Mathlib.Analysis.Complex.ValueDistribution.FirstMainTheorem
import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Asymptotic

/-!
# The divisor takes finite orders

`MeromorphicOn.divisor f U h` is the divisor of a function `f` that is meromorphic on `U`, where `h`
proves that the order of `f` is finite at every point of `U`; the meromorphy proof is the implicit
argument of these orders.  A function that vanishes on a punctured neighborhood of a point has order
`⊤` there and no divisor.  The pole divisor `MeromorphicOn.poleDivisor f U hf` exists for every
function that is meromorphic on `U`.  The logarithmic counting function and the characteristic
function take meromorphy and, for a finite value `a`, the condition that `f` takes `a` on no
punctured neighborhood; for `a = ⊤` this condition holds for every function and is supplied by
default.
-/

open MeromorphicOn Real ValueDistribution Set

/-! The former values outside the domain are removed. -/

/-- info: Unknown constant `MeromorphicOn.divisor_eq_zero_of_not_meromorphicOn` -/
#guard_msgs in
#check_failure MeromorphicOn.divisor_eq_zero_of_not_meromorphicOn

/-- info: Unknown constant `MeromorphicOn.negPart_divisor_add_of_analyticNhdOn_right` -/
#guard_msgs in
#check_failure MeromorphicOn.negPart_divisor_add_of_analyticNhdOn_right

/-- info: Unknown identifier `locallyFinsuppWithin.logCounting_divisor` -/
#guard_msgs in
#check_failure locallyFinsuppWithin.logCounting_divisor

/-! The divisor needs finite order at every point. -/

/--
error: Type mismatch
  divisor f univ
has type
  (∀ (z : ℂ) (hz : z ∈ univ), meromorphicOrderAt f z ⋯ ≠ ⊤) → Function.locallyFinsuppWithin univ ℤ
but is expected to have type
  Function.locallyFinsuppWithin univ ℤ
-/
#guard_msgs in
noncomputable example (f : ℂ → ℂ) (hf : MeromorphicOn f univ) :
    Function.locallyFinsuppWithin (univ : Set ℂ) ℤ :=
  divisor f univ

/-! The zero function has infinite order and hence no divisor, but it has a pole divisor. -/

example (x : ℂ) : meromorphicOrderAt (fun _ : ℂ ↦ (0 : ℂ)) x = ⊤ := by
  classical
  simp [meromorphicOrderAt_const]

example : poleDivisor (fun _ : ℂ ↦ (0 : ℂ)) univ = 0 :=
  AnalyticOnNhd.poleDivisor_eq_zero analyticOnNhd_const

/-! Where the divisor exists, the pole divisor is its negative part. -/

example {f : ℂ → ℂ} {U : Set ℂ} (hf : MeromorphicOn f U)
    (h : ∀ z (hz : z ∈ U), meromorphicOrderAt f z (hf z hz) ≠ ⊤) :
    poleDivisor f U hf = (divisor f U h)⁻ :=
  poleDivisor_eq_negPart_divisor h

/-! The divisor of a nonzero constant is zero. -/

example (U : Set ℂ) :
    divisor (fun _ : ℂ ↦ (2 : ℂ)) U (hf := fun _ _ ↦ .const _ _) (fun _ _ ↦
      (analyticAt_const (v := (2 : ℂ))).meromorphicOrderAt_ne_top_of_ne_zero two_ne_zero) = 0 :=
  divisor_const _

/-! Without meromorphy, neither the pole divisor nor the counting function for the poles can be
formed. -/

/--
error: could not synthesize default value for parameter 'hf' using tactics
---
error: `fun_prop` was unable to prove `MeromorphicOn f univ`

Issues:
  No theorems found for `f` in order to prove `MeromorphicOn (fun a => f a) univ`
-/
#guard_msgs in
noncomputable example (f : ℂ → ℂ) : Function.locallyFinsuppWithin (univ : Set ℂ) ℤ :=
  poleDivisor f univ

/--
error: could not synthesize default value for parameter 'hf' using tactics
---
error: `fun_prop` was unable to prove `Meromorphic f`

Issues:
  No theorems found for `f` in order to prove `Meromorphic fun a => f a`
-/
#guard_msgs in
noncomputable example (f : ℂ → ℂ) : ℝ → ℝ := logCounting f ⊤

/-! The counting function for the poles needs only meromorphy, and its evaluation at a radius
supplies the remaining proof by default. -/

example {f : ℂ → ℂ} (hf : Meromorphic f) :
    logCounting f ⊤ = (poleDivisor f univ).logCounting :=
  logCounting_top hf

example {f : ℂ → ℂ} (hf : Meromorphic f) : (logCounting f ⊤) 0 = 0 :=
  logCounting_eval_zero

/-! A finite value needs that `f` takes it on no punctured neighborhood. -/

/--
error: could not synthesize default value for parameter 'ha' using tactics
---
error: the function must take the value on no punctured neighborhood; only for ⊤ is this supplied by default
f : ℂ → ℂ
hf : Meromorphic f
a : ℂ
⊢ ∀ (z : ℂ), ∃ᶠ (w : ℂ) in nhdsWithin z {z}ᶜ, ↑(f w) ≠ ↑a
-/
#guard_msgs in
noncomputable example {f : ℂ → ℂ} (hf : Meromorphic f) (a : ℂ) : ℝ → ℝ := logCounting f a

/--
error: could not synthesize default value for parameter 'ha' using tactics
---
error: the function must take the value on no punctured neighborhood; only for ⊤ is this supplied by default
f : ℂ → ℂ
hf : Meromorphic f
a : ℂ
⊢ ∀ (z : ℂ), ∃ᶠ (w : ℂ) in nhdsWithin z {z}ᶜ, ↑(f w) ≠ ↑a
-/
#guard_msgs in
noncomputable example {f : ℂ → ℂ} (hf : Meromorphic f) (a : ℂ) : ℝ → ℝ := characteristic f a

example {f : ℂ → ℂ} {z a : ℂ} (hf : MeromorphicAt f z) :
    (∃ᶠ w in nhdsWithin z {z}ᶜ, (f w : WithTop ℂ) ≠ a) ↔ meromorphicOrderAt (f · - a) z ≠ ⊤ :=
  frequently_coe_ne_coe_iff hf

/-! A constant takes no other value. -/

example (r : ℝ) :
    logCounting (fun _ : ℂ ↦ (1 : ℂ)) (0 : ℂ) (.const 1)
      (fun _ ↦ .of_forall fun _ ↦ by simp) r = 0 := by
  simp

/-! The pole count of a product is bounded by the pole counts of the factors, also when a factor
vanishes identically. -/

example {f : ℂ → ℂ} {r : ℝ} (hf : Meromorphic f) (hr : 1 ≤ r) :
    (logCounting ((fun _ : ℂ ↦ (0 : ℂ)) * f) ⊤ ((Meromorphic.const (0 : ℂ)).mul hf)) r ≤
      (logCounting (fun _ : ℂ ↦ (0 : ℂ)) ⊤ (.const 0) + logCounting f ⊤ hf) r :=
  logCounting_mul_top_le hr (.const 0) hf

/-! Jensen's formula for the counting functions takes finite order everywhere. -/

example {f : ℂ → ℂ} {R : ℝ} (h : Meromorphic f)
    (h₀ : ∀ z (hz : z ∈ univ), meromorphicOrderAt f z (h.meromorphicOn z hz) ≠ ⊤) (hR : R ≠ 0) :
    Function.locallyFinsuppWithin.logCounting (divisor f univ h₀) R =
      circleAverage (Real.log ‖f ·‖) 0 R -
        Real.log ‖meromorphicTrailingCoeffAt f 0 (h₀ 0 (mem_univ 0))‖ :=
  Function.locallyFinsuppWithin.logCounting_divisor_eq_circleAverage_sub_const h h₀ hR
