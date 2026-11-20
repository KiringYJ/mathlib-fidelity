/-
Copyright (c) 2025 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
module

public import Mathlib.Analysis.Meromorphic.Section
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# The Gamma function is meromorphic
-/

@[expose] public noncomputable section

open Set TopologicalSpace MeromorphicSection
open scoped Topology

namespace Complex

/-- The entire reciprocal Gamma function as a regular meromorphic section. -/
abbrev reciprocalGammaSection : MeromorphicSection (⊤ : Opens ℂ) :=
  ofAnalyticOn reciprocalGamma analyticOnNhd_reciprocalGamma

/-- The reciprocal Gamma function is nonzero as a germ everywhere. -/
theorem reciprocalGammaSection_nonvanishing : reciprocalGammaSection.Nonvanishing :=
  nonvanishing_of_preconnected analyticOnNhd_reciprocalGamma isPreconnected_univ
    (mem_univ (1 : ℂ)) (by simp [reciprocalGamma_one])

/-- The meromorphic Gamma section on the complex plane, defined by inversion of the
entire reciprocal Gamma section. At its poles this section still has a meromorphic germ. -/
def meromorphicGamma : MeromorphicSection (⊤ : Opens ℂ) :=
  ((unit reciprocalGammaSection reciprocalGammaSection_nonvanishing)⁻¹ :
    (MeromorphicSection ⊤)ˣ).val

private theorem reciprocalGamma_germ_mul_gamma (z : ℂ) :
    germ ⟨z, mem_univ z⟩ reciprocalGammaSection * germ ⟨z, mem_univ z⟩ meromorphicGamma = 1 := by
  let u := unit reciprocalGammaSection reciprocalGammaSection_nonvanishing
  exact (congrArg (germ ⟨z, mem_univ z⟩) u.val_inv).trans (map_one _)

theorem analyticAt_Gamma {z : ℂ} (hz : ∀ n : ℕ, z ≠ -n) :
    AnalyticAt ℂ Gamma z := by
  let U := {w : ℂ | reciprocalGamma w ≠ 0}
  have hU : IsOpen U := isOpen_ne_fun differentiable_reciprocalGamma.continuous continuous_const
  have hd : DifferentiableOn ℂ Gamma U := fun w hw ↦
    (differentiableAt_Gamma w (fun n hn ↦ hw ((reciprocalGamma_eq_zero_iff w).mpr
      ⟨n, hn⟩))).differentiableWithinAt
  exact hd.analyticOnNhd hU z (reciprocalGamma_ne_zero hz)

theorem germ_meromorphicGamma_of_regular {z : ℂ} (hz : ∀ n : ℕ, z ≠ -n) :
    germ ⟨z, mem_univ z⟩ meromorphicGamma =
      MeromorphicGerm.ofAnalytic (AnalyticGerm.ofFun Gamma (analyticAt_Gamma hz)) := by
  apply mul_left_cancel₀ (reciprocalGammaSection_nonvanishing ⟨z, mem_univ z⟩)
  rw [reciprocalGamma_germ_mul_gamma, germ_ofAnalyticOn, ← map_mul,
    ← map_one (MeromorphicGerm.ofAnalytic (z := z))]
  apply congrArg MeromorphicGerm.ofAnalytic
  apply AnalyticGerm.ofFun_eq_iff.mpr
  · have he := differentiable_reciprocalGamma.continuous.continuousAt.eventually_ne
      (reciprocalGamma_ne_zero hz)
    filter_upwards [he] with w hw
    exact (reciprocalGamma_mul_Gamma (fun n hn ↦ hw ((reciprocalGamma_eq_zero_iff w).mpr
      ⟨n, hn⟩))).symm
  all_goals first
    | exact analyticAt_const
    | exact (analyticOnNhd_reciprocalGamma z (mem_univ z)).mul (analyticAt_Gamma hz)

/-- Gamma admits a complex value precisely away from the nonpositive integers. -/
theorem mem_regularLocus_meromorphicGamma_iff (z : ℂ) :
    (⟨z, mem_univ z⟩ : (⊤ : Opens ℂ)) ∈ regularLocus meromorphicGamma ↔ ∀ n : ℕ, z ≠ -n := by
  constructor
  · intro hr n hn
    exact MeromorphicGerm.not_regular_of_mul_eq_one
      (f := AnalyticGerm.ofFun reciprocalGamma (analyticOnNhd_reciprocalGamma z (mem_univ z)))
      ((reciprocalGamma_eq_zero_iff z).mpr ⟨n, hn⟩) (reciprocalGamma_germ_mul_gamma z) hr
  · intro hz
    exact ⟨_, (germ_meromorphicGamma_of_regular hz).symm⟩

@[simp] theorem eval_meromorphicGamma {z : ℂ} (hz : ∀ n : ℕ, z ≠ -n) :
    eval meromorphicGamma ⟨⟨z, mem_univ z⟩, (mem_regularLocus_meromorphicGamma_iff z).mpr hz⟩ =
      Gamma z := by
  let a := AnalyticGerm.ofFun Gamma (analyticAt_Gamma hz)
  apply Eq.trans _ (MeromorphicGerm.eval_ofAnalytic a)
  exact congrArg MeromorphicGerm.eval (Subtype.ext (germ_meromorphicGamma_of_regular hz))

end Complex
