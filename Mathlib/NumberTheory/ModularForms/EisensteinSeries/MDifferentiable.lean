/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.UniformConvergence
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-!
# Holomorphicity of Eisenstein series

We show that Eisenstein series of weight `k` and level `Γ(N)` with congruence condition
`a : Fin 2 → ZMod N` are holomorphic on the upper half plane, which is stated as being
MDifferentiable.
-/

public section

noncomputable section

open UpperHalfPlane Filter Function Complex CongruenceSubgroup

open scoped Manifold

namespace EisensteinSeries

/-- A representative of the inverse power of a linear function is differentiable on the
upper half-plane when the lattice vector is admissible for the weight. -/
lemma div_linear_zpow_differentiableOn (k : ℤ) (a : Fin 2 → ℤ) (ha : 0 < k → a ≠ 0)
    {f : ℂ → ℂ} (hf : ∀ z : ℍ, f z = eisSummand k a z ha) :
    DifferentiableOn ℂ f upperHalfPlaneSet := by
  intro w hw
  let W : ℂ → ℂ := fun z ↦ (a 0 : ℂ) * z + a 1
  let q (y : upperHalfPlaneSet) : {x : ℂ // -k < 0 → IsUnit (W x)} :=
    ⟨y.val, fun h ↦ (eisSummand_base_ne_zero (ha (by omega)) ⟨y.val, y.property⟩).isUnit⟩
  let z : upperHalfPlaneSet := ⟨w, hw⟩
  have hW : DifferentiableAt ℂ W (q z).val := by dsimp [W]; fun_prop
  have hq : Continuous q := continuous_subtype_val.subtype_mk _
  have hqc : ContinuousAt q z := hq.continuousAt
  have hPower : DifferentiableAt ℂ
      (fun y : {x : ℂ // -k < 0 → IsUnit (W x)} ↦ Checked.zpow (W y.val) (-k) y.property)
      (q z) Subtype.val := hW.zpow (m := -k) (q z).property
  have hp := hPower.hasFDerivAt.comp_tendsto q
    (hqc.tendsto.prodMap (tendsto_pure_pure q z))
  have heq : (fun y : upperHalfPlaneSet ↦ f y.val) =
      (fun y : {x : ℂ // -k < 0 → IsUnit (W x)} ↦ Checked.zpow (W y.val) (-k) y.property) ∘ q :=
    funext fun y ↦ hf ⟨y.val, y.property⟩
  rw [← heq] at hp
  exact (HasFDerivAt.of_restrict (coord := id) (x := z) hp
    (isOpen_upperHalfPlaneSet.mem_nhds hw)).differentiableAt.differentiableWithinAt

/-- Auxiliary lemma showing that for any `k : ℤ` and `(a : Fin 2 → ℤ)`
the extension of `eisSummand` is differentiable on `{z : ℂ | 0 < z.im}`. -/
lemma eisSummand_extension_differentiableOn (k : ℤ) (a : Fin 2 → ℤ) (ha : 0 < k → a ≠ 0) :
    DifferentiableOn ℂ (↑ₕ(fun z ↦ eisSummand k a z ha)) upperHalfPlaneSet := by
  apply div_linear_zpow_differentiableOn k a ha
  intro z
  exact comp_ofComplex _ z

/-- Eisenstein series are MDifferentiable (i.e. holomorphic functions from `ℍ → ℂ`). -/
theorem eisensteinSeriesSIF_mdifferentiable {k : ℤ} {N : ℕ} (hk : 3 ≤ k) (a : Fin 2 → ZMod N) :
    MDiff (eisensteinSeriesSIF a k) := by
  intro τ
  suffices DifferentiableAt ℂ (↑ₕeisensteinSeriesSIF a k) τ.1 by
    convert!
      MDifferentiableAt.comp τ (DifferentiableAt.mdifferentiableAt this) τ.mdifferentiable_coe
    exact funext fun z ↦ (comp_ofComplex (eisensteinSeriesSIF a k) z).symm
  refine DifferentiableOn.differentiableAt ?_ (isOpen_upperHalfPlaneSet.mem_nhds τ.2)
  exact (eisensteinSeries_tendstoLocallyUniformlyOn hk a).differentiableOn
    (Eventually.of_forall fun s ↦ DifferentiableOn.fun_sum
    fun v _ ↦ eisSummand_extension_differentiableOn _ v
      (fun _ ↦ gammaSet_ne_zero v one_ne_zero)) isOpen_upperHalfPlaneSet

end EisensteinSeries
