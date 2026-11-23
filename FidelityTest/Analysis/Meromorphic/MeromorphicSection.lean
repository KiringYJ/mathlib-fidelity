import Mathlib.Analysis.Meromorphic.Section

open TopologicalSpace MeromorphicSection
open scoped Topology

noncomputable section

-- No connectedness hypothesis is needed for the section ring.
example (U : Opens ℂ) : CommRing (MeromorphicSection U) := inferInstance

-- Global inversion uses nonzero germs at every point, not a nonzero section alone.
example (U : Opens ℂ) (s : MeromorphicSection U) (hs : s.Nonvanishing) :
    IsUnit s := (MeromorphicSection.isUnit_iff s).mpr hs

-- On two nonempty disjoint open sets, a section equal to one on the first and zero
-- on the second is nonzero and has no global inverse.
example (U V : Opens ℂ) (hUV : Disjoint (U : Set ℂ) V) (u : U) (v : V) :
    ∃ s : MeromorphicSection (U ⊔ V), s ≠ 0 ∧ ¬ IsUnit s := by
  classical
  let f : ℂ → ℂ := fun z ↦ if z ∈ U then 1 else 0
  have h₁ (z : ℂ) (hz : z ∈ U) : f =ᶠ[𝓝 z] (1 : ℂ → ℂ) := by
    filter_upwards [U.isOpen.mem_nhds hz] with w hw
    exact ite_eq_left (show w ∈ U from hw)
  have h₀ (z : ℂ) (hz : z ∈ V) : f =ᶠ[𝓝 z] (0 : ℂ → ℂ) := by
    filter_upwards [V.isOpen.mem_nhds hz] with w hw
    exact ite_eq_right (show w ∉ U from fun hu ↦ Set.disjoint_left.mp hUV hu hw)
  have hf : AnalyticOnNhd ℂ f (U ⊔ V : Opens ℂ) := by
    intro z hz
    rcases hz with hz | hz
    · exact analyticAt_const.congr (h₁ z hz).symm
    · exact analyticAt_const.congr (h₀ z hz).symm
  let x : ↥(U ⊔ V) := ⟨u, Or.inl u.property⟩
  let y : ↥(U ⊔ V) := ⟨v, Or.inr v.property⟩
  refine ⟨ofAnalyticOn f hf, ?_, ?_⟩
  · intro h
    have hx := congrArg (germ x) h
    rw [germ_ofAnalyticOn, map_zero] at hx
    have hfun : AnalyticGerm.ofFun f (hf x x.property) = 1 :=
      (AnalyticGerm.ofFun_eq_iff (hf := hf x x.property)
        (hg := analyticAt_const)).mpr (h₁ u u.property)
    rw [hfun, map_one] at hx
    exact one_ne_zero hx
  · intro h
    have hy := (isUnit_iff _).mp h y
    rw [germ_ofAnalyticOn] at hy
    have hfun : AnalyticGerm.ofFun f (hf y y.property) = 0 :=
      (AnalyticGerm.ofFun_eq_iff (hf := hf y y.property)
        (hg := analyticAt_const)).mpr (h₀ v v.property)
    exact hy ((congrArg MeromorphicGerm.ofAnalytic hfun).trans (map_zero _))

-- Intrinsic evaluation agrees with the analytic function throughout its open domain.
example (U : Opens ℂ) (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f U) (x : U) :
    eval (ofAnalyticOn f hf) ⟨x, mem_regularLocus_ofAnalyticOn f hf x⟩ = f x :=
  eval_ofAnalyticOn f hf x
