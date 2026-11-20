import Mathlib.Analysis.Complex.CanonicalDecomposition

open Complex MeromorphicSection Metric Set TopologicalSpace

noncomputable section

-- At the boundary center, the numerator and denominator cancel and a scalar value exists.
example : (⟨(1 : ℂ), mem_univ _⟩ : (⊤ : Opens ℂ)) ∈ (canonicalFactor 1 1).regularLocus := by
  rw [mem_regularLocus_canonicalFactor_center_iff]
  norm_num

example : canonicalFactor 1 1 =
    ofAnalyticOn (fun _ : ℂ ↦ (-1 : ℂ)) (fun _ _ ↦ analyticAt_const) := by
  simpa using canonicalFactor_of_center_eq (R := 1) (w := 1) (hR := one_ne_zero) (by norm_num)

-- The interior center of the inverse Blaschke factor is a genuine pole.
example : (⟨(0 : ℂ), mem_univ _⟩ : (⊤ : Opens ℂ)) ∉ (canonicalFactor 1 0).regularLocus := by
  rw [mem_regularLocus_canonicalFactor_center_iff]
  norm_num

-- A boundary pole of the original function remains outside the scalar domain of the remainder.
example {R : ℝ} {T : Set ℂ} {f : ℂ → ℂ} {g : T → ℂ} (D : CanonicalDecomp f g R)
    {x : ℂ} (hx : x ∈ sphere (0 : ℂ) R)
    (hp : MeromorphicOn.divisor f (sphere (0 : ℂ) R) D.meromorphicOrderAt_ne_top_sphere x < 0) :
    x ∉ T := fun h ↦ hp.not_ge ((D.mem_domain_iff (sphere_subset_closedBall hx)).mp h)
