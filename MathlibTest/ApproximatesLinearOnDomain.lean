/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn

open Set Metric
open scoped NNReal

noncomputable section

-- The inverse operator of an equivalence of zero spaces has norm zero.
example :
    let E := Fin 0 → ℝ
    AntilipschitzWith 0 (univ.domRestrict (fun x : E ↦ x)) := by
  dsimp only
  let e := ContinuousLinearEquiv.refl ℝ (Fin 0 → ℝ)
  have he : (e.symm : (Fin 0 → ℝ) →L[ℝ] (Fin 0 → ℝ)) = 0 := Subsingleton.elim _ _
  have hN : ‖(e.symm : (Fin 0 → ℝ) →L[ℝ] (Fin 0 → ℝ))‖₊ = 0 := by simp [he]
  have hf : ApproximatesLinearOn (fun x : Fin 0 → ℝ ↦ x) (e : _ →L[ℝ] _) univ 7 := by
    intro x _ y _
    simp only [Subsingleton.elim x y, sub_self, map_zero, norm_zero, mul_zero]
    exact le_rfl
  have hc : (7 : ℝ≥0) * ‖(e.symm : (Fin 0 → ℝ) →L[ℝ] (Fin 0 → ℝ))‖₊ < 1 := by
    simp [hN]
  simpa only [hN, mul_zero, tsub_zero, div_one₀] using hf.antilipschitz hc

-- A nonlinear right inverse into a zero codomain may carry a positive, nonminimal bound.
example :
    let F := Fin 0 → ℝ
    let f' : ℝ →L[ℝ] F := 0
    ∃ R : f'.NonlinearRightInverse,
      R.nnnorm = 2 ∧ ¬ (4 : ℝ≥0) * R.nnnorm < 1 ∧
        IsOpen ((fun _ : ℝ ↦ (0 : F)) '' univ) := by
  dsimp only
  let R : (0 : ℝ →L[ℝ] (Fin 0 → ℝ)).NonlinearRightInverse :=
    { toFun := fun _ ↦ 0
      nnnorm := 2
      bound' := by intro y; simp
      right_inv' := by intro y; exact Subsingleton.elim _ _ }
  refine ⟨R, rfl, by norm_num [R], ?_⟩
  have hf : ApproximatesLinearOn (fun _ : ℝ ↦ (0 : Fin 0 → ℝ))
      (0 : ℝ →L[ℝ] (Fin 0 → ℝ)) univ 4 := by
    intro x _ y _
    simp only [zero_apply, sub_self, norm_zero]
    positivity
  exact hf.open_image R isOpen_univ (Or.inl inferInstance)

-- The ball-surjectivity theorem still admits c*N = 1 and radius zero.
example :
    SurjOn (fun x : ℝ ↦ x) (closedBall 0 0) (closedBall 0 0) := by
  let R : (ContinuousLinearMap.id ℝ ℝ).NonlinearRightInverse :=
    { toFun := fun x ↦ x
      nnnorm := 1
      bound' := by intro y; simp
      right_inv' := by intro y; rfl }
  have hf : ApproximatesLinearOn (fun x : ℝ ↦ x)
      (ContinuousLinearMap.id ℝ ℝ) univ 1 := by
    intro x _ y _
    simp
  simpa only [R, mul_zero, sub_self] using
    hf.surjOn_closedBall_of_nonlinearRightInverse R (b := 0) (ε := 0) le_rfl (subset_univ _)

-- A zero right-inverse bound gives a zero-radius source ball without inverting that bound.
example :
    SurjOn (fun _ : ℝ ↦ (0 : Fin 0 → ℝ)) (closedBall 0 0) (closedBall 0 1) := by
  let R : (0 : ℝ →L[ℝ] (Fin 0 → ℝ)).NonlinearRightInverse :=
    { toFun := fun _ ↦ 0
      nnnorm := 0
      bound' := by intro y; simp
      right_inv' := by intro y; exact Subsingleton.elim _ _ }
  have hf : ApproximatesLinearOn (fun _ : ℝ ↦ (0 : Fin 0 → ℝ))
      (0 : ℝ →L[ℝ] (Fin 0 → ℝ)) univ 7 := by
    intro x _ y _
    simp only [zero_apply, sub_self, norm_zero]
    positivity
  simpa only [R, NNReal.coe_zero, zero_mul, mul_zero, sub_zero, one_mul] using
    hf.surjOn_closedBall_of_nonlinearRightInverse R (b := 0) (ε := 1) zero_le_one (subset_univ _)
