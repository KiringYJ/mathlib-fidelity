import Mathlib.Analysis.Distribution.Distribution

/-!
# Regularity inequalities of operators on supported maps and test functions

These tests ensure that differentiation, inclusions, structure maps, and seminorms of supported
maps and test functions take their regularity inequality, so that an impossible request no longer
gives the zero operator, and that `regularity_le` finds the routine inequalities.
-/

open scoped Distributions
open ContDiffMapSupportedIn TopologicalSpace

/-- info: Unknown constant `ContDiffMapSupportedIn.fderivLM_apply_of_gt` -/
#guard_msgs in
#check_failure ContDiffMapSupportedIn.fderivLM_apply_of_gt

/-- info: Unknown constant `ContDiffMapSupportedIn.iteratedFDerivLM_apply_of_gt` -/
#guard_msgs in
#check_failure ContDiffMapSupportedIn.iteratedFDerivLM_apply_of_gt

/-- info: Unknown constant `ContDiffMapSupportedIn.monoLM_eq_zero` -/
#guard_msgs in
#check_failure ContDiffMapSupportedIn.monoLM_eq_zero

/-- info: Unknown constant `ContDiffMapSupportedIn.seminorm_eq_bot_of_gt` -/
#guard_msgs in
#check_failure ContDiffMapSupportedIn.seminorm_eq_bot_of_gt

/-- info: Unknown constant `ContDiffMapSupportedIn.continuous_iff_comp_order_le` -/
#guard_msgs in
#check_failure ContDiffMapSupportedIn.continuous_iff_comp_order_le

/-- info: Unknown constant `TestFunction.fderivCLM_apply_of_gt` -/
#guard_msgs in
#check_failure TestFunction.fderivCLM_apply_of_gt

/-- info: Unknown constant `TestFunction.lineDerivCLM_apply_of_gt` -/
#guard_msgs in
#check_failure TestFunction.lineDerivCLM_apply_of_gt

/-- info: Unknown constant `TestFunction.monoCLM_eq_zero` -/
#guard_msgs in
#check_failure TestFunction.monoCLM_eq_zero

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {K : Compacts E} {Ω : Opens E}

/-! A derivative needs one more order of regularity than its target; it was formerly zero. -/

/-- error: this operator needs a proof of its regularity inequality -/
#guard_msgs (substring := true) in
noncomputable example : 𝓓^{1}_{K}(E, F) →L[ℝ] 𝓓^{1}_{K}(E, E →L[ℝ] F) := fderivCLM ℝ 1 1

/-- error: this operator needs a proof of its regularity inequality -/
#guard_msgs (substring := true) in
noncomputable example : 𝓓^{1}(Ω, F) →L[ℝ] 𝓓^{1}(Ω, F) := TestFunction.lineDerivCLM ℝ (0 : E)

/-! The regularity inequality is found for smooth maps, numerals, and hypotheses. -/

noncomputable example : 𝓓_{K}(E, F) →L[ℝ] 𝓓_{K}(E, E →L[ℝ] F) := fderivCLM ℝ ⊤ ⊤

noncomputable example : 𝓓^{2}_{K}(E, F) →L[ℝ] 𝓓^{1}_{K}(E, E →L[ℝ] F) := fderivCLM ℝ 2 1

noncomputable example {n k : ℕ∞} (hk : k + 1 ≤ n) :
    𝓓^{n}(Ω, F) →L[ℝ] 𝓓^{k}(Ω, E →L[ℝ] F) :=
  TestFunction.fderivCLM ℝ n k

example (f : 𝓓_{K}(E, F)) : fderivCLM ℝ ⊤ ⊤ le_top f = fderiv ℝ f := rfl

/-! A seminorm of an order beyond the regularity does not exist; it was formerly `0`. -/

/-- error: this operator needs a proof of its regularity inequality -/
#guard_msgs (substring := true) in
noncomputable example : Seminorm ℝ 𝓓^{1}_{K}(E, F) := N[ℝ]_{K, 1, 2}

example {i : ℕ} (f : 𝓓_{K}(E, F)) (x : E) : ‖iteratedFDeriv ℝ i f x‖ ≤ N[ℝ]_{K, i} f :=
  norm_iteratedFDeriv_apply_le_seminorm_top ℝ

/-! The inclusion needs the regularities in the right order. -/

/-- error: this operator needs a proof of its regularity inequality -/
#guard_msgs (substring := true) in
noncomputable example : 𝓓^{1}_{K}(E, F) →L[ℝ] 𝓓^{2}_{K}(E, F) := monoCLM ℝ le_rfl

noncomputable example {K₁ K₂ : Compacts E} (hK : K₁ ≤ K₂) :
    𝓓^{2}_{K₁}(E, F) →L[ℝ] 𝓓^{1}_{K₂}(E, F) :=
  monoCLM ℝ hK
