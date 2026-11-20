/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

module

public import Mathlib.NumberTheory.ModularForms.DedekindEta

/-!
# MDifferentiability of the weight 2 Eisenstein series

We show that the weight 2 Eisenstein series `E2` is MDifferentiable (i.e. holomorphic as a
function `ℍ → ℂ`). The proof uses the relation between `E2` and the logarithmic derivative of
the Dedekind eta function.
-/

public section

open UpperHalfPlane hiding I
open Real Complex EisensteinSeries ModularForm

open scoped Manifold


--This proof was provided by Gauss to the sphere packing project.
/-- The weight 2 Eisenstein series `E2` is MDifferentiable -/
lemma E2_mdifferentiable : MDiff E2 := by
  have hη : DifferentiableOn ℂ η upperHalfPlaneSet := fun z hz ↦
    (differentiableAt_eta_of_mem_upperHalfPlaneSet hz).differentiableWithinAt
  have hrestrict {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f upperHalfPlaneSet) :
      MDiff (fun z : ℍ ↦ f z) := fun z ↦
    (hf.differentiableAt (isOpen_upperHalfPlaneSet.mem_nhds z.2)).mdifferentiableAt.comp z
      (mdifferentiable_coe z)
  let logη (z : ℍ) := logDeriv η (z : ℂ) id
    (differentiableAt_eta_of_mem_upperHalfPlaneSet z.2).existsUnique_hasDerivAt
    (eta_ne_zero z.2).isUnit
  have hlog : MDiff logη := by
    simp only [logη, logDeriv_apply]
    exact (hrestrict (hη.deriv isOpen_upperHalfPlaneSet)).div (hrestrict hη)
  let c : ℂ := π * I / 12
  have hc : IsUnit c :=
    (div_ne_zero (mul_ne_zero (ofReal_ne_zero.mpr pi_ne_zero) I_ne_zero)).isUnit
  have hE2 : E2 = fun z : ℍ ↦ Checked.inv c hc * logη z := by
    funext z
    have hz : logη z = c * E2 z := logDeriv_eta_eq_E2 z
    rw [hz, ← mul_assoc, inv_mul_cancel₀, one_mul]
  rw [hE2]
  exact mdifferentiable_const.mul hlog

end
