/-
Copyright (c) 2026 Xuanji Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuanji Li
-/
module

public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.Analysis.Meromorphic.Section
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Geometry.Manifold.Algebra.Structures

/-!
# Meromorphicity of the complex tangent and hyperbolic tangent

The real and complex tangents are smooth on their open domains.
-/

@[expose] public noncomputable section

open TopologicalSpace MeromorphicSection

namespace Complex

/-- The analytic denominator is nonzero as a germ at every complex point. -/
theorem cosSection_nonvanishing :
    (ofAnalyticOn (U := ⊤) cos (fun _ _ ↦ analyticAt_cos)).Nonvanishing :=
  nonvanishing_of_preconnected _ isPreconnected_univ (Set.mem_univ (0 : ℂ)) (by simp)

/-- The tangent section on the complex plane. Its poles are the zeros of cosine. -/
def meromorphicTan : MeromorphicSection (⊤ : Opens ℂ) :=
  ofAnalyticOn (U := ⊤) sin (fun _ _ ↦ analyticAt_sin) /ₚ
    unit (ofAnalyticOn cos (fun _ _ ↦ analyticAt_cos)) cosSection_nonvanishing

theorem mem_regularLocus_meromorphicTan_iff (z : ℂ) :
    (⟨z, Set.mem_univ z⟩ : (⊤ : Opens ℂ)) ∈ regularLocus meromorphicTan ↔ cos z ≠ 0 := by
  let a := AnalyticGerm.ofFun sin (z := z) analyticAt_sin
  let b := AnalyticGerm.ofFun cos (z := z) analyticAt_cos
  have hb : b ≠ 0 := MeromorphicGerm.ofAnalytic_ne_zero.mp
    (cosSection_nonvanishing ⟨z, Set.mem_univ z⟩)
  change Checked.div (MeromorphicGerm.ofAnalytic a) (MeromorphicGerm.ofAnalytic b)
    (MeromorphicGerm.ofAnalytic_ne_zero.mpr hb).isUnit ∈ MeromorphicGerm.regularSubring z ↔ _
  apply MeromorphicGerm.div_mem_regularSubring_iff hb
  change cos z = 0 → sin z ≠ 0
  intro hc hs
  simpa [hc, hs] using sin_sq_add_cos_sq z

/-- The scalar tangent on the nonzero locus of cosine is meromorphic at every center. -/
theorem meromorphicAt_tan (z : ℂ) :
    MeromorphicAt (fun w : {w : ℂ | cos w ≠ 0} ↦ tan w w.property) z Subtype.val := by
  apply analyticAt_sin.meromorphicAt_div analyticAt_cos
  intro he
  apply cosSection_nonvanishing ⟨z, Set.mem_univ z⟩
  change MeromorphicGerm.ofAnalytic (AnalyticGerm.ofFun cos (z := z) analyticAt_cos) = 0
  rw [← map_zero MeromorphicGerm.ofAnalytic]
  exact congrArg MeromorphicGerm.ofAnalytic ((AnalyticGerm.ofFun_eq_iff (hf := analyticAt_cos)
    (hg := analyticAt_const (v := (0 : ℂ)))).mpr he)

/-- The tangent is meromorphic on the complex plane. -/
theorem meromorphic_tan :
    Meromorphic (fun w : {w : ℂ | cos w ≠ 0} ↦ tan w w.property) Subtype.val := meromorphicAt_tan

/-- The analytic denominator is nonzero as a germ at every complex point. -/
theorem coshSection_nonvanishing :
    (ofAnalyticOn (U := ⊤) cosh (fun _ _ ↦ analyticAt_cosh)).Nonvanishing :=
  nonvanishing_of_preconnected _ isPreconnected_univ (Set.mem_univ (0 : ℂ)) (by simp)

/-- The hyperbolic tangent section on the complex plane. Its poles are the zeros of cosh. -/
def meromorphicTanh : MeromorphicSection (⊤ : Opens ℂ) :=
  ofAnalyticOn (U := ⊤) sinh (fun _ _ ↦ analyticAt_sinh) /ₚ
    unit (ofAnalyticOn cosh (fun _ _ ↦ analyticAt_cosh)) coshSection_nonvanishing

theorem mem_regularLocus_meromorphicTanh_iff (z : ℂ) :
    (⟨z, Set.mem_univ z⟩ : (⊤ : Opens ℂ)) ∈ regularLocus meromorphicTanh ↔ cosh z ≠ 0 := by
  let a := AnalyticGerm.ofFun sinh (z := z) analyticAt_sinh
  let b := AnalyticGerm.ofFun cosh (z := z) analyticAt_cosh
  have hb : b ≠ 0 := MeromorphicGerm.ofAnalytic_ne_zero.mp
    (coshSection_nonvanishing ⟨z, Set.mem_univ z⟩)
  change Checked.div (MeromorphicGerm.ofAnalytic a) (MeromorphicGerm.ofAnalytic b)
    (MeromorphicGerm.ofAnalytic_ne_zero.mpr hb).isUnit ∈ MeromorphicGerm.regularSubring z ↔ _
  apply MeromorphicGerm.div_mem_regularSubring_iff hb
  change cosh z = 0 → sinh z ≠ 0
  intro hc hs
  simpa [hc, hs] using cosh_sq_sub_sinh_sq z

/-- The scalar hyperbolic tangent on the nonzero locus of cosh is meromorphic at every center. -/
theorem meromorphicAt_tanh (z : ℂ) :
    MeromorphicAt (fun w : {w : ℂ | cosh w ≠ 0} ↦ tanh w w.property) z Subtype.val := by
  apply analyticAt_sinh.meromorphicAt_div analyticAt_cosh
  intro he
  apply coshSection_nonvanishing ⟨z, Set.mem_univ z⟩
  change MeromorphicGerm.ofAnalytic (AnalyticGerm.ofFun cosh (z := z) analyticAt_cosh) = 0
  rw [← map_zero MeromorphicGerm.ofAnalytic]
  exact congrArg MeromorphicGerm.ofAnalytic ((AnalyticGerm.ofFun_eq_iff (hf := analyticAt_cosh)
    (hg := analyticAt_const (v := (0 : ℂ)))).mpr he)

/-- The hyperbolic tangent is meromorphic on the complex plane. -/
theorem meromorphic_tanh :
    Meromorphic (fun w : {w : ℂ | cosh w ≠ 0} ↦ tanh w w.property) Subtype.val := meromorphicAt_tanh

end Complex

open scoped Manifold ContDiff

namespace Real

/-- The open domain of the real tangent. -/
def tanDomain : Opens ℝ :=
  ⟨{x | cos x ≠ 0}, isOpen_ne_fun (contDiff_cos (n := ω)).continuous continuous_const⟩

/-- Tangent is smooth at every real point where its cosine is nonzero. -/
theorem contDiffAt_tan {n : WithTop ℕ∞} {x : ℝ} (hx : cos x ≠ 0) :
    ContMDiffAt 𝓘(ℝ) 𝓘(ℝ) n (fun z : tanDomain ↦ tan z.val z.2) ⟨x, hx⟩ := by
  have hv : ContMDiff 𝓘(ℝ) 𝓘(ℝ) n (Subtype.val : tanDomain → ℝ) := contMDiff_subtype_val
  exact ((contDiff_sin.contMDiff.comp hv).div₀ (contDiff_cos.contMDiff.comp hv)
    (h := fun z ↦ z.2.isUnit)).contMDiffAt

end Real

namespace Complex

/-- The open domain of the complex tangent. -/
def tanDomain : Opens ℂ :=
  ⟨{z | cos z ≠ 0}, isOpen_ne_fun (contDiff_cos (n := ω)).continuous continuous_const⟩

/-- Tangent is smooth at every complex point where its cosine is nonzero. -/
theorem contDiffAt_tan {n : WithTop ℕ∞} {x : ℂ} (hx : cos x ≠ 0) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) n (fun z : tanDomain ↦ tan z.val z.2) ⟨x, hx⟩ := by
  have hv : ContMDiff 𝓘(ℂ) 𝓘(ℂ) n (Subtype.val : tanDomain → ℂ) := contMDiff_subtype_val
  exact ((contDiff_sin.contMDiff.comp hv).div₀ (contDiff_cos.contMDiff.comp hv)
    (h := fun z ↦ z.2.isUnit)).contMDiffAt

end Complex
