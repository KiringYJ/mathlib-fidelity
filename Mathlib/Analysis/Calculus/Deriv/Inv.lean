/-
Copyright (c) 2023 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Derivatives of `x ↦ x⁻¹` and `f x / g x`

In this file we prove `(x⁻¹)' = -1 / x ^ 2`, `((f x)⁻¹)' = -f' x / (f x) ^ 2`, and
`(f x / g x)' = (f' x * g x - f x * g' x) / (g x) ^ 2` for different notions of derivative.

For a more detailed overview of one-dimensional derivatives in mathlib, see the module docstring of
`Analysis/Calculus/Deriv/Basic`.

## Keywords

derivative
-/

public section


universe u

open scoped Topology
open Filter Asymptotics Set Topology

open ContinuousLinearMap (toSpanSingleton)

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] {x : 𝕜} {s : Set 𝕜}

section Inverse

/-! ### Derivative of `x ↦ x⁻¹` -/

theorem hasStrictDerivAt_inv (x : 𝕜ˣ) :
    HasStrictDerivAt (fun y : 𝕜ˣ ↦ (↑y⁻¹ : 𝕜)) (-(↑x⁻¹ : 𝕜) ^ 2) x
      (fun y ↦ (y : 𝕜)) := by
  simpa only [neg_apply, ContinuousLinearMap.mulLeftRight_apply,
    mul_one, pow_two] using (hasStrictFDerivAt_inv' (𝕜 := 𝕜) x).hasStrictDerivAt

theorem hasDerivAt_inv (x : 𝕜ˣ) :
    HasDerivAt (fun y : 𝕜ˣ ↦ (↑y⁻¹ : 𝕜)) (-(↑x⁻¹ : 𝕜) ^ 2) x
      (fun y ↦ (y : 𝕜)) := by
  simpa only [neg_apply, ContinuousLinearMap.mulLeftRight_apply,
    mul_one, pow_two] using (hasFDerivAt_inv' (𝕜 := 𝕜) x).hasDerivAt

theorem hasDerivWithinAt_inv (x : 𝕜ˣ) (s : Set 𝕜ˣ) :
    HasDerivWithinAt (fun y : 𝕜ˣ ↦ (↑y⁻¹ : 𝕜)) (-(↑x⁻¹ : 𝕜) ^ 2) s x
      (fun y ↦ (y : 𝕜)) := by
  simpa only [neg_apply, ContinuousLinearMap.mulLeftRight_apply,
    mul_one, pow_two] using (hasFDerivAt_inv' (𝕜 := 𝕜) x).hasFDerivWithinAt.hasDerivWithinAt

theorem deriv_inv (x : 𝕜ˣ) :
    deriv (fun y : 𝕜ˣ ↦ (↑y⁻¹ : 𝕜)) x (fun y ↦ (y : 𝕜)) = -(↑x⁻¹ : 𝕜) ^ 2 :=
  (hasDerivAt_inv x).deriv Units.isOpenEmbedding_val

@[simp]
theorem deriv_inv' :
    (fun x : 𝕜ˣ ↦ deriv (fun y : 𝕜ˣ ↦ (↑y⁻¹ : 𝕜)) x (fun y ↦ (y : 𝕜))) =
      fun x : 𝕜ˣ ↦ -(↑x⁻¹ : 𝕜) ^ 2 :=
  funext deriv_inv

theorem derivWithin_inv (x : 𝕜ˣ) {s : Set 𝕜ˣ}
    (hxs : UniqueDiffWithinAt 𝕜 ((fun y : 𝕜ˣ ↦ (y : 𝕜)) '' s) (x : 𝕜)) :
    derivWithin (fun y : 𝕜ˣ ↦ (↑y⁻¹ : 𝕜)) s x (fun y ↦ (y : 𝕜)) = -(↑x⁻¹ : 𝕜) ^ 2 :=
  (hasDerivWithinAt_inv x s).derivWithin_of_isEmbedding Units.isOpenEmbedding_val.isEmbedding hxs

theorem hasFDerivAt_inv (x : 𝕜ˣ) :
    HasFDerivAt (fun y : 𝕜ˣ ↦ (↑y⁻¹ : 𝕜))
      (toSpanSingleton 𝕜 (-(↑x⁻¹ : 𝕜) ^ 2) : 𝕜 →L[𝕜] 𝕜) x (fun y ↦ (y : 𝕜)) :=
  hasDerivAt_inv x

theorem hasStrictFDerivAt_inv (x : 𝕜ˣ) :
    HasStrictFDerivAt (fun y : 𝕜ˣ ↦ (↑y⁻¹ : 𝕜))
      (toSpanSingleton 𝕜 (-(↑x⁻¹ : 𝕜) ^ 2) : 𝕜 →L[𝕜] 𝕜) x (fun y ↦ (y : 𝕜)) :=
  hasStrictDerivAt_inv x

theorem hasFDerivWithinAt_inv (x : 𝕜ˣ) {s : Set 𝕜ˣ} :
    HasFDerivWithinAt (fun y : 𝕜ˣ ↦ (↑y⁻¹ : 𝕜))
      (toSpanSingleton 𝕜 (-(↑x⁻¹ : 𝕜) ^ 2) : 𝕜 →L[𝕜] 𝕜) s x (fun y ↦ (y : 𝕜)) :=
  hasDerivWithinAt_inv x s

theorem fderiv_inv (x : 𝕜ˣ) :
    fderiv 𝕜 (fun y : 𝕜ˣ ↦ (↑y⁻¹ : 𝕜)) x (fun y ↦ (y : 𝕜)) =
      toSpanSingleton 𝕜 (-(↑x⁻¹ : 𝕜) ^ 2) :=
  (hasFDerivAt_inv x).fderiv Units.isOpenEmbedding_val

theorem fderivWithin_inv (x : 𝕜ˣ) {s : Set 𝕜ˣ}
    (hxs : UniqueDiffWithinAt 𝕜 ((fun y : 𝕜ˣ ↦ (y : 𝕜)) '' s) (x : 𝕜)) :
    fderivWithin 𝕜 (fun y : 𝕜ˣ ↦ (↑y⁻¹ : 𝕜)) s x (fun y ↦ (y : 𝕜)) =
      toSpanSingleton 𝕜 (-(↑x⁻¹ : 𝕜) ^ 2) := by
  apply (hasFDerivWithinAt_inv x).fderivWithin_of_unique
  intro g hg
  exact hg.unique_of_isEmbedding (hasFDerivWithinAt_inv x)
    Units.isOpenEmbedding_val.isEmbedding hxs

variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
variable {c : 𝕜 → 𝕜'} {c' : 𝕜'}

theorem HasDerivWithinAt.inv (hc : HasDerivWithinAt c c' s x) (hx : IsUnit (c x)) :
    HasDerivWithinAt (fun y : {y : 𝕜 | IsUnit (c y)} ↦ (↑y.property.unit⁻¹ : 𝕜'))
      (-c' * (↑hx.unit⁻¹ : 𝕜') ^ 2) (Subtype.val ⁻¹' s) ⟨x, hx⟩ (fun y ↦ (y : 𝕜)) := by
  convert (hc.hasFDerivWithinAt.inv hx).hasDerivWithinAt using 1
  simp only [ContinuousLinearMap.comp_apply, neg_apply,
    ContinuousLinearMap.mulLeftRight_apply, ContinuousLinearMap.toSpanSingleton_apply,
    one_smul, pow_two]
  ring

theorem HasStrictDerivAt.inv (hc : HasStrictDerivAt c c' x) (hx : IsUnit (c x)) :
    HasStrictDerivAt (fun y : {y : 𝕜 | IsUnit (c y)} ↦ (↑y.property.unit⁻¹ : 𝕜'))
      (-c' * (↑hx.unit⁻¹ : 𝕜') ^ 2) ⟨x, hx⟩ (fun y ↦ (y : 𝕜)) := by
  convert (hc.hasStrictFDerivAt.inv hx).hasStrictDerivAt using 1
  simp only [ContinuousLinearMap.comp_apply, neg_apply,
    ContinuousLinearMap.mulLeftRight_apply, ContinuousLinearMap.toSpanSingleton_apply,
    one_smul, pow_two]
  ring

theorem HasDerivAt.inv (hc : HasDerivAt c c' x) (hx : IsUnit (c x)) :
    HasDerivAt (fun y : {y : 𝕜 | IsUnit (c y)} ↦ (↑y.property.unit⁻¹ : 𝕜'))
      (-c' * (↑hx.unit⁻¹ : 𝕜') ^ 2) ⟨x, hx⟩ (fun y ↦ (y : 𝕜)) := by
  convert (hc.hasFDerivAt.inv hx).hasDerivAt using 1
  simp only [ContinuousLinearMap.comp_apply, neg_apply,
    ContinuousLinearMap.mulLeftRight_apply, ContinuousLinearMap.toSpanSingleton_apply,
    one_smul, pow_two]
  ring

theorem derivWithin_fun_inv' (hc : DifferentiableWithinAt 𝕜 c s x) (hx : IsUnit (c x))
    (hxs : UniqueDiffWithinAt 𝕜 (s ∩ {y | IsUnit (c y)}) x) :
    derivWithin (fun y : {y : 𝕜 | IsUnit (c y)} ↦ (↑y.property.unit⁻¹ : 𝕜'))
      (Subtype.val ⁻¹' s) ⟨x, hx⟩ (fun y ↦ (y : 𝕜)) =
        -derivWithin c s x * (↑hx.unit⁻¹ : 𝕜') ^ 2 := by
  apply (hc.hasDerivWithinAt.inv hx).derivWithin_of_isEmbedding IsEmbedding.subtypeVal
  convert hxs using 1
  ext y
  simp [and_comm]

@[simp]
theorem deriv_fun_inv'' (hc : DifferentiableAt 𝕜 c x) (hx : IsUnit (c x)) :
    deriv (fun y : {y : 𝕜 | IsUnit (c y)} ↦ (↑y.property.unit⁻¹ : 𝕜'))
      ⟨x, hx⟩ (fun y ↦ (y : 𝕜)) = -deriv c x * (↑hx.unit⁻¹ : 𝕜') ^ 2 := by
  apply (hc.hasDerivAt.inv hx).deriv_of_mem_nhds IsEmbedding.subtypeVal
  rw [Subtype.range_val]
  change ∀ᶠ y in 𝓝 x, IsUnit (c y)
  exact hc.continuousAt.eventually (Units.isOpen.mem_nhds hx)

end Inverse

section Division

/-! ### Derivative of `x ↦ c x / d x` -/

variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] {c d : 𝕜 → 𝕜'} {c' d' : 𝕜'}

theorem HasDerivWithinAt.div (hc : HasDerivWithinAt c c' s x) (hd : HasDerivWithinAt d d' s x)
    (hx : IsUnit (d x)) :
    HasDerivWithinAt (fun y : {y : 𝕜 | IsUnit (d y)} ↦ c y /ₚ y.property.unit)
      ((c' * d x - c x * d') /ₚ (hx.unit ^ 2)) (Subtype.val ⁻¹' s) ⟨x, hx⟩ (fun y ↦ (y : 𝕜)) := by
  have hrestricted : HasDerivWithinAt (fun y : {y : 𝕜 | IsUnit (d y)} ↦ c y) c'
      (Subtype.val ⁻¹' s) ⟨x, hx⟩ (fun y ↦ (y : 𝕜)) := by
    exact HasFDerivAtFilter.comp_tendsto hc.hasFDerivWithinAt Subtype.val
      ((continuous_subtype_val.continuousWithinAt.tendsto_nhdsWithin (fun _ hy ↦ hy)).prodMap
        (tendsto_pure_pure ..))
  convert hrestricted.mul (hd.inv hx) continuous_subtype_val.continuousWithinAt using 1
  · ext y
    rfl
  · simp only [divp, ← inv_pow, Units.val_pow_eq_pow_val]
    have hcancel : c' * (↑hx.unit⁻¹ : 𝕜') = c' * d x * (↑hx.unit⁻¹ : 𝕜') ^ 2 := by
      calc
        _ = c' * (d x * (↑hx.unit⁻¹ : 𝕜')) * ↑hx.unit⁻¹ := by rw [hx.mul_val_inv, mul_one]
        _ = _ := by ring
    rw [hcancel]
    ring

theorem HasStrictDerivAt.div (hc : HasStrictDerivAt c c' x) (hd : HasStrictDerivAt d d' x)
    (hx : IsUnit (d x)) :
    HasStrictDerivAt (fun y : {y : 𝕜 | IsUnit (d y)} ↦ c y /ₚ y.property.unit)
      ((c' * d x - c x * d') /ₚ (hx.unit ^ 2)) ⟨x, hx⟩ (fun y ↦ (y : 𝕜)) := by
  have hrestricted : HasStrictDerivAt (fun y : {y : 𝕜 | IsUnit (d y)} ↦ c y) c'
      ⟨x, hx⟩ (fun y ↦ (y : 𝕜)) := by
    exact HasFDerivAtFilter.comp_tendsto hc.hasStrictFDerivAt Subtype.val
      ((continuous_subtype_val.tendsto ⟨x, hx⟩).prodMap_nhds
        (continuous_subtype_val.tendsto ⟨x, hx⟩))
  convert hrestricted.mul (hd.inv hx) continuous_subtype_val.continuousAt using 1
  · ext y
    rfl
  · simp only [divp, ← inv_pow, Units.val_pow_eq_pow_val]
    have hcancel : c' * (↑hx.unit⁻¹ : 𝕜') = c' * d x * (↑hx.unit⁻¹ : 𝕜') ^ 2 := by
      calc
        _ = c' * (d x * (↑hx.unit⁻¹ : 𝕜')) * ↑hx.unit⁻¹ := by rw [hx.mul_val_inv, mul_one]
        _ = _ := by ring
    rw [hcancel]
    ring

theorem HasDerivAt.div (hc : HasDerivAt c c' x) (hd : HasDerivAt d d' x)
    (hx : IsUnit (d x)) :
    HasDerivAt (fun y : {y : 𝕜 | IsUnit (d y)} ↦ c y /ₚ y.property.unit)
      ((c' * d x - c x * d') /ₚ (hx.unit ^ 2)) ⟨x, hx⟩ (fun y ↦ (y : 𝕜)) := by
  have hrestricted : HasDerivAt (fun y : {y : 𝕜 | IsUnit (d y)} ↦ c y) c'
      ⟨x, hx⟩ (fun y ↦ (y : 𝕜)) := by
    exact HasFDerivAtFilter.comp_tendsto hc.hasFDerivAt Subtype.val
      ((continuous_subtype_val.tendsto ⟨x, hx⟩).prodMap (tendsto_pure_pure ..))
  convert hrestricted.mul (hd.inv hx) continuous_subtype_val.continuousAt using 1
  · ext y
    rfl
  · simp only [divp, ← inv_pow, Units.val_pow_eq_pow_val]
    have hcancel : c' * (↑hx.unit⁻¹ : 𝕜') = c' * d x * (↑hx.unit⁻¹ : 𝕜') ^ 2 := by
      calc
        _ = c' * (d x * (↑hx.unit⁻¹ : 𝕜')) * ↑hx.unit⁻¹ := by rw [hx.mul_val_inv, mul_one]
        _ = _ := by ring
    rw [hcancel]
    ring

theorem DifferentiableWithinAt.div (hc : DifferentiableWithinAt 𝕜 c s x)
    (hd : DifferentiableWithinAt 𝕜 d s x) (hx : IsUnit (d x)) :
    DifferentiableWithinAt 𝕜 (fun y : {y : 𝕜 | IsUnit (d y)} ↦ c y /ₚ y.property.unit)
      (Subtype.val ⁻¹' s) ⟨x, hx⟩ (fun y ↦ (y : 𝕜)) :=
  (hc.hasDerivWithinAt.div hd.hasDerivWithinAt hx).differentiableWithinAt

@[simp, fun_prop]
theorem DifferentiableAt.div (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x)
    (hx : IsUnit (d x)) :
    DifferentiableAt 𝕜 (fun y : {y : 𝕜 | IsUnit (d y)} ↦ c y /ₚ y.property.unit)
      ⟨x, hx⟩ (fun y ↦ (y : 𝕜)) :=
  (hc.hasDerivAt.div hd.hasDerivAt hx).differentiableAt

@[fun_prop]
theorem DifferentiableOn.div (hc : DifferentiableOn 𝕜 c s) (hd : DifferentiableOn 𝕜 d s)
    (hx : ∀ x ∈ s, IsUnit (d x)) :
    DifferentiableOn 𝕜 (fun y : {y : 𝕜 | IsUnit (d y)} ↦ c y /ₚ y.property.unit)
      (Subtype.val ⁻¹' s) (fun y ↦ (y : 𝕜)) :=
  fun x h ↦ (hc x h).div (hd x h) (hx x h)

@[simp, fun_prop]
theorem Differentiable.div (hc : Differentiable 𝕜 c) (hd : Differentiable 𝕜 d)
    (hx : ∀ x, IsUnit (d x)) : Differentiable 𝕜 (fun x ↦ c x /ₚ (hx x).unit) := by
  simpa only [divp, Pi.mul_def] using hc.mul (hd.inv hx)

theorem derivWithin_div (hc : DifferentiableWithinAt 𝕜 c s x)
    (hd : DifferentiableWithinAt 𝕜 d s x) (hx : IsUnit (d x))
    (hxs : UniqueDiffWithinAt 𝕜 (s ∩ {y | IsUnit (d y)}) x) :
    derivWithin (fun y : {y : 𝕜 | IsUnit (d y)} ↦ c y /ₚ y.property.unit)
      (Subtype.val ⁻¹' s) ⟨x, hx⟩ (fun y ↦ (y : 𝕜)) =
        (derivWithin c s x * d x - c x * derivWithin d s x) /ₚ (hx.unit ^ 2) := by
  apply (hc.hasDerivWithinAt.div hd.hasDerivWithinAt hx).derivWithin_of_isEmbedding
    IsEmbedding.subtypeVal
  convert hxs using 1
  ext y
  simp [and_comm]

@[simp]
theorem deriv_div (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x)
    (hx : IsUnit (d x)) :
    deriv (fun y : {y : 𝕜 | IsUnit (d y)} ↦ c y /ₚ y.property.unit)
      ⟨x, hx⟩ (fun y ↦ (y : 𝕜)) = (deriv c x * d x - c x * deriv d x) /ₚ (hx.unit ^ 2) := by
  apply (hc.hasDerivAt.div hd.hasDerivAt hx).deriv_of_mem_nhds IsEmbedding.subtypeVal
  rw [Subtype.range_val]
  change ∀ᶠ y in 𝓝 x, IsUnit (d y)
  exact hd.continuousAt.eventually (Units.isOpen.mem_nhds hx)

theorem deriv_const_div (c : 𝕜') (hd : DifferentiableAt 𝕜 d x) (hx : IsUnit (d x)) :
    deriv (fun y : {y : 𝕜 | IsUnit (d y)} ↦ c /ₚ y.property.unit)
      ⟨x, hx⟩ (fun y ↦ (y : 𝕜)) = (-c * deriv d x) /ₚ (hx.unit ^ 2) := by
  simpa only [deriv_const, zero_mul, zero_sub, neg_mul] using
    deriv_div (differentiableAt_const c) hd hx

@[simp]
theorem deriv_const_div_id (c : 𝕜) (x : 𝕜ˣ) :
    deriv (fun y : 𝕜ˣ ↦ c /ₚ y) x (fun y ↦ (y : 𝕜)) = -c /ₚ (x ^ 2) := by
  have hc : HasDerivAt (fun _ : 𝕜ˣ ↦ c) 0 x (fun y ↦ (y : 𝕜)) := by
    apply HasFDerivAt.of_isLittleOTVS
    simp only [sub_self, ContinuousLinearMap.toSpanSingleton_apply, smul_zero]
    change (0 : 𝕜ˣ → 𝕜) =o[𝕜; 𝓝 x] (fun y : 𝕜ˣ ↦ (y : 𝕜) - x)
    exact IsLittleOTVS.zero _ _
  have h := (hc.mul (hasDerivAt_inv x) Units.continuous_val.continuousAt).deriv
    Units.isOpenEmbedding_val
  simpa only [divp, Pi.mul_def, ← inv_pow, Units.val_pow_eq_pow_val, zero_mul, zero_add, mul_neg,
    neg_mul] using h

end Division
