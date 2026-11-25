import Mathlib.Analysis.Meromorphic.Order

/-!
# Analytic and meromorphic orders take their germ hypotheses

`analyticOrderAt f x hf` takes a proof that `f` is analytic at `x`, and `meromorphicOrderAt f x hf`
a proof that `f` is meromorphic at `x`; `fun_prop` supplies them by default.  Neither order has a
value outside its domain, and a function that vanishes locally has order `⊤`.
-/

open scoped Topology

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

example (hf : ∀ x, MeromorphicAt f x) :
    meromorphicOrderAt f x (coord := id) = meromorphicOrderAt f x (hf x) := rfl

example (hf : MeromorphicOn f U) (hx : x ∈ U) : MeromorphicAt f x := by fun_prop

example (hf : MeromorphicOn f U) (hx : x ∈ U) :
    meromorphicOrderAt f x (coord := id) = meromorphicOrderAt f x (hf x hx) := rfl

example (hf : MeromorphicOn f U)
    (h : ∀ x (hx : x ∈ U), meromorphicOrderAt f x (coord := id) ≠ ⊤) :
    ∀ x (hx : x ∈ U), meromorphicOrderAt f x (hf x hx) ≠ ⊤ := h

/-! Without the germ hypothesis, the order is not defined. -/

/--
error: could not synthesize default value for parameter 'hf' using tactics
---
error: `fun_prop` was unable to prove `AnalyticAt 𝕜 f x id`

Issues:
  No theorems found for `f` in order to prove `AnalyticAt 𝕜 (fun a => f a) x id`
-/
#guard_msgs in
noncomputable example : ℕ∞ := analyticOrderAt f x

/--
error: could not synthesize default value for parameter 'hf' using tactics
---
error: `fun_prop` was unable to prove `MeromorphicAt f x id`

Issues:
  No theorems found for `f` in order to prove `MeromorphicAt (fun a => f a) x id`
-/
#guard_msgs in
noncomputable example : WithTop ℤ := meromorphicOrderAt f x (coord := id)

/-! A function that vanishes locally has infinite order. -/

example : analyticOrderAt (fun _ : 𝕜 ↦ (0 : E)) x = ⊤ :=
  (analyticOrderAt_eq_top analyticAt_const).2 (.of_forall fun _ ↦ rfl)

example : meromorphicOrderAt (fun _ : 𝕜 ↦ (0 : E)) x = ⊤ :=
  (meromorphicOrderAt_eq_top_iff (.const 0 x)).2 (.of_forall fun _ ↦ rfl)

example : analyticOrderAt (fun z : 𝕜 ↦ z - x) x = 1 := by simp

example (n : ℤ) :
    let S := {z : 𝕜 // n < 0 → IsUnit (z - x)}
    ∃ hf : MeromorphicAt (fun z : S ↦ Checked.zpow (z.val - x) n z.property) x Subtype.val,
      meromorphicOrderAt _ x hf = n := by
  have hf : MeromorphicAt (fun z : 𝕜 ↦ z - x) x := by fun_prop
  have hc : Set.range (Subtype.val : {z : 𝕜 // n < 0 → IsUnit (z - x)} → 𝕜) ∈ 𝓝[≠] x := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact ⟨⟨z, fun _ ↦ (sub_ne_zero.mpr hz).isUnit⟩, rfl⟩
  refine ⟨hf.zpow n hc, ?_⟩
  simpa only [meromorphicOrderAt_id_sub_const, ← WithTop.coe_one, WithTop.checked_zsmul_coe,
    Int.zsmul_eq_mul, Int.mul_one] using!
    meromorphicOrderAt_zpow hf n hc
