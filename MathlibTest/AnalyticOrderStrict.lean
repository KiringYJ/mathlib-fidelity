import Mathlib.Analysis.Meromorphic.Order

/-!
# Analytic and meromorphic orders take their germ hypotheses

`analyticOrderAt f x hf` takes a proof that `f` is analytic at `x`, and `meromorphicOrderAt f x hf`
a proof that `f` is meromorphic at `x`; `fun_prop` supplies them by default.  Neither order has a
value outside its domain, and a function that vanishes locally has order `⊤`.
-/

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {f : 𝕜 → E} {U : Set 𝕜} {x : 𝕜}

/-! The natural-number order and the fallback lemmas are removed. -/

/-- info: Unknown identifier `analyticOrderNatAt` -/
#guard_msgs in
#check_failure analyticOrderNatAt

/-- info: Unknown identifier `analyticOrderAt_of_not_analyticAt` -/
#guard_msgs in
#check_failure analyticOrderAt_of_not_analyticAt

/-- info: Unknown identifier `meromorphicOrderAt_of_not_meromorphicAt` -/
#guard_msgs in
#check_failure meromorphicOrderAt_of_not_meromorphicAt

/-- info: Unknown identifier `meromorphicAt_of_meromorphicOrderAt_ne_zero` -/
#guard_msgs in
#check_failure meromorphicAt_of_meromorphicOrderAt_ne_zero

/-! The default argument is found from the local context. -/

example (hf : AnalyticAt 𝕜 f x) : analyticOrderAt f x = analyticOrderAt f x hf := rfl

example (hf : ∀ x, MeromorphicAt f x) : meromorphicOrderAt f x = meromorphicOrderAt f x (hf x) :=
  rfl

example (hf : MeromorphicOn f U) (hx : x ∈ U) : MeromorphicAt f x := by fun_prop

example (hf : MeromorphicOn f U) (hx : x ∈ U) :
    meromorphicOrderAt f x = meromorphicOrderAt f x (hf x hx) := rfl

example (hf : MeromorphicOn f U) (h : ∀ x (hx : x ∈ U), meromorphicOrderAt f x ≠ ⊤) :
    ∀ x (hx : x ∈ U), meromorphicOrderAt f x (hf x hx) ≠ ⊤ := h

/-! Without the germ hypothesis, the order is not defined. -/

/--
error: could not synthesize default value for parameter 'hf' using tactics
---
error: `fun_prop` was unable to prove `AnalyticAt 𝕜 f x`

Issues:
  No theorems found for `f` in order to prove `AnalyticAt 𝕜 (fun a => f a) x`
-/
#guard_msgs in
noncomputable example : ℕ∞ := analyticOrderAt f x

/--
error: could not synthesize default value for parameter 'hf' using tactics
---
error: `fun_prop` was unable to prove `MeromorphicAt f x`

Issues:
  No theorems found for `f` in order to prove `MeromorphicAt (fun a => f a) x`
-/
#guard_msgs in
noncomputable example : WithTop ℤ := meromorphicOrderAt f x

/-! A function that vanishes locally has infinite order. -/

example : analyticOrderAt (fun _ : 𝕜 ↦ (0 : E)) x = ⊤ :=
  (analyticOrderAt_eq_top analyticAt_const).2 (.of_forall fun _ ↦ rfl)

example : meromorphicOrderAt (fun _ : 𝕜 ↦ (0 : E)) x = ⊤ :=
  (meromorphicOrderAt_eq_top_iff (.const 0 x)).2 (.of_forall fun _ ↦ rfl)

example : analyticOrderAt (fun z : 𝕜 ↦ z - x) x = 1 := by simp

example (n : ℤ) : meromorphicOrderAt ((· - x) ^ n) x = n := by simp
