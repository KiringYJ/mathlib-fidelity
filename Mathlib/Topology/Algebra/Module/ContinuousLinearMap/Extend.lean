/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Moritz Doll
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-! # Extension of continuous linear maps

In this file we provide a way to extend a continuous linear map defined on a dense
subspace to the entire space.

* `ContinuousLinearMap.extend`: Extend `f : E →SL[σ₁₂] F` to a continuous linear map
  `Eₗ →SL[σ₁₂] F`, where `e : E →ₗ[𝕜] Eₗ` is a dense map that is `IsUniformInducing`. It takes the
  density of the range of `e` and the uniform inducing property, under which the extension exists
  and is unique. -/

namespace ContinuousLinearMap
variable {𝕜 𝕜₂ E F Eₗ : Type*} [AddCommGroup E] [UniformSpace E] [IsUniformAddGroup E]
  [AddCommGroup F] [UniformSpace F] [IsUniformAddGroup F] [T0Space F]
  [AddCommMonoid Eₗ] [UniformSpace Eₗ] [ContinuousAdd Eₗ]
  [Semiring 𝕜] [Semiring 𝕜₂] [Module 𝕜 E] [Module 𝕜₂ F] [Module 𝕜 Eₗ]
  [ContinuousConstSMul 𝕜 Eₗ] [ContinuousConstSMul 𝕜₂ F]
  {σ₁₂ : 𝕜 →+* 𝕜₂} (f : E →SL[σ₁₂] F) [CompleteSpace F] (e : E →L[𝕜] Eₗ)

/-- Extension of a continuous linear map `f : E →SL[σ₁₂] F` along a uniformly inducing map
`e : E →L[𝕜] Eₗ` with dense range: the unique continuous linear map `g` with `g ∘ e = f`
(`extend_eq`, `extend_unique`). -/
@[expose] public noncomputable def extend (h_dense : DenseRange e) (h_e : IsUniformInducing e) :
    Eₗ →SL[σ₁₂] F :=
  -- extension of `f` is continuous
  have cont := (uniformContinuous_uniformly_extend h_e h_dense f.uniformContinuous).continuous
  -- extension of `f` agrees with `f` on the domain of the embedding `e`
  have eq := uniformly_extend_of_ind h_e h_dense f.uniformContinuous
  { toFun := (h_e.isDenseInducing h_dense).extend f
    map_add' := by
      refine h_dense.induction_on₂ ?_ ?_
      · exact isClosed_eq (cont.comp continuous_add)
          ((cont.comp continuous_fst).add (cont.comp continuous_snd))
      · intro x y
        simp only [eq, ← e.map_add]
        exact f.map_add _ _
    map_smul' := fun k => by
      refine fun b => h_dense.induction_on b ?_ ?_
      · exact isClosed_eq (cont.comp (continuous_const_smul _))
          ((continuous_const_smul _).comp cont)
      · intro x
        rw [← map_smul]
        simp only [eq]
        exact map_smulₛₗ _ _ _
    cont }

variable {e}

@[simp] public theorem extend_eq (h_dense : DenseRange e) (h_e : IsUniformInducing e) (x : E) :
    extend f e h_dense h_e (e x) = f x :=
  IsDenseInducing.extend_eq (h_e.isDenseInducing h_dense) f.cont _

public theorem extend_unique (h_dense : DenseRange e) (h_e : IsUniformInducing e)
    (g : Eₗ →SL[σ₁₂] F) (H : g.comp e = f) : extend f e h_dense h_e = g :=
  ContinuousLinearMap.coeFn_injective <|
    uniformly_extend_unique h_e h_dense (ContinuousLinearMap.ext_iff.1 H) g.continuous

@[simp] public theorem extend_zero (h_dense : DenseRange e) (h_e : IsUniformInducing e) :
    extend (0 : E →SL[σ₁₂] F) e h_dense h_e = 0 :=
  extend_unique _ h_dense h_e _ (zero_comp _)

end ContinuousLinearMap
