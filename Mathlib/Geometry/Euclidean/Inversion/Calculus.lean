/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Geometry.Euclidean.Inversion.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.Geometry.Manifold.Algebra.Structures

/-!
# Derivative of the inversion

In this file we prove a formula for the derivative of `EuclideanGeometry.inversion c R`.
We use the inclusion of the punctured vector space as its coordinates.

## Keywords

inversion, derivative
-/

public section

open Function Set Filter
open scoped Topology RealInnerProductSpace Manifold ContDiff

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

open EuclideanGeometry

section Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
  {c x : M → F} {R : M → ℝ} {s : Set M} {a : M} {n : ℕ∞ω} {hne : ∀ b, x b ≠ c b}

protected theorem ContMDiffWithinAt.inversion (hc : ContMDiffWithinAt I 𝓘(ℝ, F) n c s a)
    (hR : ContMDiffWithinAt I 𝓘(ℝ) n R s a) (hx : ContMDiffWithinAt I 𝓘(ℝ, F) n x s a) :
    ContMDiffWithinAt I 𝓘(ℝ, F) n (fun b ↦ inversion (c b) (R b) (x b) (hne b)) s a := by
  have hv := hx.sub hc
  have hd : ContMDiffWithinAt I 𝓘(ℝ) n (fun b ↦ ‖x b - c b‖ ^ 2) s a :=
    (contDiff_norm_sq ℝ).contMDiff.contMDiffAt.comp_contMDiffWithinAt a hv
  have hu (b : M) : IsUnit (‖x b - c b‖ ^ 2) :=
    (pow_ne_zero _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hne b)))).isUnit
  have hq : ContMDiffWithinAt I 𝓘(ℝ) n
      (fun b ↦ Checked.div (R b ^ 2) (‖x b - c b‖ ^ 2) (hu b)) s a :=
    (hR.pow 2).div₀ hd (.of_forall fun b ↦ ⟨hu b, rfl⟩)
  convert (hq.smul hv).add hc using 1
  funext b
  simp only [inversion_def, dist_eq_norm, div_pow₀, vsub_eq_sub, vadd_eq_add, Pi.add_apply,
    Pi.smul_apply']

protected theorem ContMDiffOn.inversion (hc : ContMDiffOn I 𝓘(ℝ, F) n c s)
    (hR : ContMDiffOn I 𝓘(ℝ) n R s) (hx : ContMDiffOn I 𝓘(ℝ, F) n x s) :
    ContMDiffOn I 𝓘(ℝ, F) n (fun b ↦ inversion (c b) (R b) (x b) (hne b)) s :=
  fun b hb ↦ (hc b hb).inversion (hR b hb) (hx b hb)

protected theorem ContMDiffAt.inversion (hc : ContMDiffAt I 𝓘(ℝ, F) n c a)
    (hR : ContMDiffAt I 𝓘(ℝ) n R a) (hx : ContMDiffAt I 𝓘(ℝ, F) n x a) :
    ContMDiffAt I 𝓘(ℝ, F) n (fun b ↦ inversion (c b) (R b) (x b) (hne b)) a :=
  ContMDiffWithinAt.inversion hc hR hx

protected theorem ContMDiff.inversion (hc : ContMDiff I 𝓘(ℝ, F) n c)
    (hR : ContMDiff I 𝓘(ℝ) n R) (hx : ContMDiff I 𝓘(ℝ, F) n x) :
    ContMDiff I 𝓘(ℝ, F) n (fun b ↦ inversion (c b) (R b) (x b) (hne b)) :=
  fun b ↦ (hc b).inversion (hR b) (hx b)

end Manifold

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {c x : E → F} {R : E → ℝ} {s : Set E} {a : E} {n : ℕ∞ω} {hne : ∀ b, x b ≠ c b}

protected theorem ContDiffWithinAt.inversion (hc : ContDiffWithinAt ℝ n c s a)
    (hR : ContDiffWithinAt ℝ n R s a) (hx : ContDiffWithinAt ℝ n x s a) :
    ContDiffWithinAt ℝ n (fun b ↦ inversion (c b) (R b) (x b) (hne b)) s a :=
  (hc.contMDiffWithinAt.inversion hR.contMDiffWithinAt hx.contMDiffWithinAt).contDiffWithinAt

protected theorem ContDiffOn.inversion (hc : ContDiffOn ℝ n c s)
    (hR : ContDiffOn ℝ n R s) (hx : ContDiffOn ℝ n x s) :
    ContDiffOn ℝ n (fun b ↦ inversion (c b) (R b) (x b) (hne b)) s :=
  (hc.contMDiffOn.inversion hR.contMDiffOn hx.contMDiffOn).contDiffOn

protected theorem ContDiffAt.inversion (hc : ContDiffAt ℝ n c a)
    (hR : ContDiffAt ℝ n R a) (hx : ContDiffAt ℝ n x a) :
    ContDiffAt ℝ n (fun b ↦ inversion (c b) (R b) (x b) (hne b)) a :=
  (hc.contMDiffAt.inversion hR.contMDiffAt hx.contMDiffAt).contDiffAt

protected theorem ContDiff.inversion (hc : ContDiff ℝ n c) (hR : ContDiff ℝ n R)
    (hx : ContDiff ℝ n x) :
    ContDiff ℝ n (fun b ↦ inversion (c b) (R b) (x b) (hne b)) :=
  (hc.contMDiff.inversion hR.contMDiff hx.contMDiff).contDiff

end NormedSpace

namespace EuclideanGeometry

variable {c x : F} {R : ℝ}

open ContinuousLinearMap in
/-- Formula for the Fréchet derivative of spherical inversion in the punctured space. -/
theorem hasFDerivAt_inversion (hx : x ≠ c) :
    HasFDerivAt (fun y : {y : F // y ≠ c} ↦ inversion c R y y.2)
      ((R / dist x c) ^ 2 • ((ℝ ∙ (x - c))ᗮ.reflection : F →L[ℝ] F))
      ⟨x, hx⟩ (fun y ↦ (y : F)) := by
  let D := {y : F // y ≠ c}
  let p : D := ⟨x, hx⟩
  let v : D → F := fun y ↦ (y : F) - c
  let u (y : D) : IsUnit (‖v y‖ ^ 2) :=
    (pow_ne_zero _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr y.2))).isUnit
  let q (y : D) : ℝˣ := (u y).unit
  have hv : HasFDerivAt v (.id ℝ F) p (fun y ↦ (y : F)) := by
    exact HasFDerivAtFilter.comp_tendsto (hasFDerivAt_sub_const c (x := x)) Subtype.val
      ((continuous_subtype_val.tendsto p).prodMap (tendsto_pure_pure ..))
  have hq : HasFDerivAt ((fun y : ℝˣ ↦ (y : ℝ)) ∘ q) (2 • innerSL ℝ (v p))
      p (fun y ↦ (y : F)) := by
    simpa only [q, Function.comp_def, IsUnit.unit_spec, ContinuousLinearMap.comp_id] using
      (hasStrictFDerivAt_norm_sq (v p)).hasFDerivAt.comp p hv
        (hcoord := continuous_subtype_val.continuousAt) (coord' := @id F)
  have hi := (hasFDerivAt_inv (q p)).comp p hq
    (hcoord := continuous_subtype_val.continuousAt)
    (hcoord' := Units.isOpenEmbedding_val.isEmbedding)
  have hm := hi.const_smul (R ^ 2)
  have h := ((isBoundedBilinearMap_smul (𝕜 := ℝ)).hasFDerivAt
    (R ^ 2 * (↑(q p)⁻¹ : ℝ), v p)).comp p (hm.prodMk hv)
      (hcoord := continuous_subtype_val.continuousAt) (coord' := @id (ℝ × F))
  have he (y : D) :
      inversion c R y y.2 = (R ^ 2 * (↑(q y)⁻¹ : ℝ)) • v y + c := by
    simp only [inversion_def, div_eq_mul_inv₀, dist_eq_norm, vsub_eq_sub, vadd_eq_add,
      mul_pow, inv_pow₀, q, v, Units.val_inv_eq_inv_val₀, IsUnit.unit_spec]
  simp only [he]
  convert h.add_const c using 1
  · funext y
    simp only [Function.comp_def, Pi.smul_apply, smul_eq_mul]
  apply ContinuousLinearMap.coe_injective
  have hvp : v p = x - c := rfl
  have hscale : (R / dist x c) ^ 2 = R ^ 2 * (↑(q p)⁻¹ : ℝ) := by
    simp only [div_eq_mul_inv₀, mul_pow, inv_pow₀, q, Units.val_inv_eq_inv_val₀,
      IsUnit.unit_spec, hvp, dist_eq_norm]
  rw [hscale, ← hvp]
  have hc : IsCompl (ℝ ∙ v p) (ℝ ∙ v p)ᗮ :=
    Submodule.isCompl_orthogonal _
  refine LinearMap.ext_on_codisjoint hc.codisjoint (LinearMap.eqOn_span' ?_) fun y hy ↦ ?_
  · rw [Set.eqOn_singleton]
    let t : ℝ := ↑(q p)⁻¹
    have ht : t * ‖v p‖ ^ 2 = 1 := by
      simpa only [t, q, IsUnit.unit_spec, ← Units.val_mul, inv_mul_cancel, Units.val_one]
        using (show t * (↑(q p) : ℝ) = 1 by simp [t])
    have ht₂ : R ^ 2 * (2 * ‖v p‖ ^ 2 * -t ^ 2) = -(2 * (R ^ 2 * t)) := by
      calc
        _ = -(2 * R ^ 2 * t * (t * ‖v p‖ ^ 2)) := by ring
        _ = _ := by rw [ht, mul_one, mul_assoc]
    simp only [coe_coe, smul_apply,
      ContinuousLinearMap.comp_apply, IsBoundedBilinearMap.deriv_apply,
      ContinuousLinearMap.prod_apply, id_apply, toSpanSingleton_apply, innerSL_apply_apply,
      real_inner_self_eq_norm_sq, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, ← add_smul]
    change (R ^ 2 * t) • (ℝ ∙ v p)ᗮ.reflection (v p) =
      (R ^ 2 * t + R ^ 2 * (2 * ‖v p‖ ^ 2 * -t ^ 2)) • v p
    rw [Submodule.reflection_orthogonalComplement_singleton_eq_neg, smul_neg, ← neg_smul, ht₂]
    congr 1
    ring
  · simp only [coe_coe, smul_apply,
      ContinuousLinearMap.comp_apply, IsBoundedBilinearMap.deriv_apply,
      ContinuousLinearMap.prod_apply, id_apply, toSpanSingleton_apply, innerSL_apply_apply,
      Submodule.mem_orthogonal_singleton_iff_inner_right.1 hy, smul_eq_mul, smul_zero, zero_mul,
      mul_zero, zero_smul, add_zero]
    change (R ^ 2 * (↑(q p)⁻¹ : ℝ)) • (ℝ ∙ v p)ᗮ.reflection y = _
    rw [Submodule.reflection_mem_subspace_eq_self hy]

end EuclideanGeometry

section Differentiable

variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace D]
  {coord : D → E} {c x : D → F} {R : D → ℝ} {s : Set D} {a : D} {hne : ∀ b, x b ≠ c b}

protected theorem DifferentiableWithinAt.inversion (hc : DifferentiableWithinAt ℝ c s a coord)
    (hR : DifferentiableWithinAt ℝ R s a coord) (hx : DifferentiableWithinAt ℝ x s a coord)
    (hcoord : ContinuousWithinAt coord s a := by exact continuousWithinAt_id) :
    DifferentiableWithinAt ℝ (fun b ↦ inversion (c b) (R b) (x b) (hne b)) s a coord := by
  let v (b : D) : {y : F // y ≠ 0} := ⟨x b - c b, sub_ne_zero.mpr (hne b)⟩
  have hv := (hx.sub hc).hasFDerivWithinAt
  have hi := (hasFDerivAt_inversion (R := 1) (v a).2).comp_hasFDerivWithinAt
    (f := v) a hv hcoord Topology.IsEmbedding.subtypeVal
  have hpow := ((hasFDerivAt_id (R a)).pow 2).comp_hasFDerivWithinAt a hR.hasFDerivWithinAt
    hcoord (coord' := @id ℝ)
  have hm := (isBoundedBilinearMap_smul (𝕜 := ℝ)).hasFDerivAt
    (R a ^ 2, inversion 0 1 (v a : F) (v a).2)
  have hsmul := hm.comp_hasFDerivWithinAt a (hpow.prodMk hi) hcoord (coord' := @id (ℝ × F))
  have he (b : D) :
      R b ^ 2 • inversion 0 1 (v b : F) (v b).2 + c b = inversion (c b) (R b) (x b) (hne b) := by
    simp only [inversion_def, v, vsub_eq_sub, vadd_eq_add, dist_eq_norm, sub_zero, add_zero,
      div_eq_mul_inv₀, one_mul, smul_smul, mul_pow]
  convert (hsmul.add hc.hasFDerivWithinAt).differentiableWithinAt using 1
  funext b
  simpa only [Function.comp_def, id_eq, Pi.add_apply] using (he b).symm

protected theorem DifferentiableOn.inversion (hc : DifferentiableOn ℝ c s coord)
    (hR : DifferentiableOn ℝ R s coord) (hx : DifferentiableOn ℝ x s coord)
    (hcoord : ContinuousOn coord s := by exact continuous_id.continuousOn) :
    DifferentiableOn ℝ (fun b ↦ inversion (c b) (R b) (x b) (hne b)) s coord :=
  fun b hb ↦ (hc b hb).inversion (hR b hb) (hx b hb) (hcoord b hb)

protected theorem DifferentiableAt.inversion (hc : DifferentiableAt ℝ c a coord)
    (hR : DifferentiableAt ℝ R a coord) (hx : DifferentiableAt ℝ x a coord)
    (hcoord : ContinuousAt coord a := by exact continuousAt_id) :
    DifferentiableAt ℝ (fun b ↦ inversion (c b) (R b) (x b) (hne b)) a coord := by
  rw [← differentiableWithinAt_univ] at hc hR hx ⊢
  exact hc.inversion hR hx hcoord.continuousWithinAt

protected theorem Differentiable.inversion (hc : Differentiable ℝ c coord)
    (hR : Differentiable ℝ R coord) (hx : Differentiable ℝ x coord)
    (hcoord : Continuous coord := by exact continuous_id) :
    Differentiable ℝ (fun b ↦ inversion (c b) (R b) (x b) (hne b)) coord :=
  fun b ↦ (hc b).inversion (hR b) (hx b) hcoord.continuousAt

end Differentiable
