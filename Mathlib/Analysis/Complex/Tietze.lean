/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Topology.TietzeExtension
public import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
public import Mathlib.Analysis.Normed.Module.RCLike.Basic
/-!
# Finite-dimensional topological vector spaces over `ℝ` satisfy the Tietze extension property

There are two main results here:

- `RCLike.instTietzeExtensionTVS`: finite-dimensional topological vector spaces over `ℝ` (or `ℂ`)
  have the Tietze extension property.
- `BoundedContinuousFunction.exists_norm_eq_domRestrict_eq`: when mapping into a finite-dimensional
  normed vector space over `ℝ` (or `ℂ`), the extension can be chosen to preserve the norm of the
  bounded continuous function it extends.

-/

public section

universe u u₁ v w

-- this is not an instance because Lean cannot determine `𝕜`.
theorem TietzeExtension.of_tvs (𝕜 : Type v) [NontriviallyNormedField 𝕜] {E : Type w}
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [T2Space E] [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜]
    [TietzeExtension.{u, v} 𝕜] : TietzeExtension.{u, w} E :=
  Module.Basis.ofVectorSpace 𝕜 E |>.equivFun.toContinuousLinearEquiv.toHomeomorph |> .of_homeo

instance Complex.instTietzeExtension : TietzeExtension ℂ :=
  TietzeExtension.of_tvs ℝ

instance (priority := 900) RCLike.instTietzeExtension {𝕜 : Type*} [RCLike 𝕜] :
    TietzeExtension 𝕜 := TietzeExtension.of_tvs ℝ

instance RCLike.instTietzeExtensionTVS {𝕜 : Type v} [RCLike 𝕜] {E : Type w}
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul 𝕜 E] [T2Space E] [FiniteDimensional 𝕜 E] :
    TietzeExtension.{u, w} E :=
  TietzeExtension.of_tvs 𝕜

instance Set.instTietzeExtensionUnitBall {𝕜 : Type v} [RCLike 𝕜] {E : Type w}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] :
    TietzeExtension.{u, w} (Metric.ball (0 : E) 1) :=
  have : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  .of_homeo Homeomorph.unitBall.symm

instance Set.instTietzeExtensionUnitClosedBall {𝕜 : Type v} [RCLike 𝕜] {E : Type w}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] :
    TietzeExtension.{u, w} (Metric.closedBall (0 : E) 1) := by
  have : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  have : IsScalarTower ℝ 𝕜 E := Real.isScalarTower
  have hpos (x : E) : 0 < max 1 ‖x‖ := zero_lt_one.trans_le (le_max_left _ _)
  let r : E → ℝ := fun x ↦ Checked.inv (max 1 ‖x‖) (hpos x).ne'.isUnit
  have hr : Continuous r := (continuous_const.max continuous_norm).fun_inv₀
  refine .of_retract ⟨Subtype.val, by fun_prop⟩
    ⟨_, (hr.smul continuous_id).codRestrict fun x ↦ ?_⟩ ?_
  · rw [Metric.mem_closedBall, dist_zero_right]
    change ‖r x • x‖ ≤ 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hpos x))]
    exact (mul_le_mul_of_nonneg_left (le_max_right 1 ‖x‖) (inv_pos.mpr (hpos x)).le).trans_eq
      inv_mul_cancel₀
  · ext x
    have hx : ‖(x : E)‖ ≤ 1 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using x.property
    simp [r, max_eq_left hx]

theorem Metric.instTietzeExtensionBall {𝕜 : Type v} [RCLike 𝕜] {E : Type w}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] {r : ℝ} (hr : 0 < r) :
    TietzeExtension.{u, w} (Metric.ball (0 : E) r) :=
  have : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  .of_homeo <| show (Metric.ball (0 : E) r) ≃ₜ (Metric.ball (0 : E) 1) from
    OpenPartialHomeomorph.unitBallBall (0 : E) r hr |>.toHomeomorphSourceTarget.symm

theorem Metric.instTietzeExtensionClosedBall (𝕜 : Type v) [RCLike 𝕜] {E : Type w}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] (y : E) {r : ℝ} (hr : 0 < r) :
    TietzeExtension.{u, w} (Metric.closedBall y r) :=
  .of_homeo (Z := Metric.closedBall (0 : E) 1) <| by
    symm
    apply (DilationEquiv.smulTorsor y (k := (r : 𝕜)) <| by exact_mod_cast hr.ne').toHomeomorph.sets
    ext x
    simp only [mem_closedBall, dist_zero_right, DilationEquiv.coe_toHomeomorph, Set.mem_preimage,
      DilationEquiv.smulTorsor_apply, vadd_eq_add, dist_add_self_left, norm_smul,
      RCLike.norm_ofReal, abs_of_nonneg hr.le]
    exact (mul_le_iff_le_one_right hr).symm

instance unitInterval.instTietzeExtension : TietzeExtension unitInterval := by
  rw [unitInterval.eq_closedBall]
  exact Metric.instTietzeExtensionClosedBall ℝ _ (by norm_num)

variable {X : Type u} [TopologicalSpace X] [NormalSpace X] {s : Set X} (hs : IsClosed s)
variable (𝕜 : Type v) [RCLike 𝕜]
variable {E : Type w} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

namespace BoundedContinuousFunction

include 𝕜 hs in
/-- **Tietze extension theorem** for real-valued bounded continuous maps, a version with a closed
embedding and bundled composition. If `e : C(X, Y)` is a closed embedding of a topological space
into a normal topological space and `f : X →ᵇ ℝ` is a bounded continuous function, then there exists
a bounded continuous function `g : Y →ᵇ ℝ` of the same norm such that `g ∘ e = f`. -/
theorem exists_norm_eq_domRestrict_eq (f : s →ᵇ E) :
    ∃ g : X →ᵇ E, ‖g‖ = ‖f‖ ∧ g.domRestrict s = f := by
  by_cases hf : ‖f‖ = 0; · exact ⟨0, by aesop⟩
  have := Metric.instTietzeExtensionClosedBall.{u, v} 𝕜 (0 : E) (by simp_all : 0 < ‖f‖)
  have hf' x : f x ∈ Metric.closedBall 0 ‖f‖ := by simpa using! f.norm_coe_le_norm x
  obtain ⟨g, hg_mem, hg⟩ := (f : C(s, E)).exists_forall_mem_restrict_eq hs hf'
  simp only [Metric.mem_closedBall, dist_zero_right] at hg_mem
  let g' : X →ᵇ E := .ofNormedAddCommGroup g (map_continuous g) ‖f‖ hg_mem
  refine ⟨g', ?_, by ext x; congrm($(hg) x)⟩
  apply le_antisymm ((g'.norm_le <| by positivity).mpr hg_mem)
  refine (f.norm_le <| by positivity).mpr fun x ↦ ?_
  have hx : f x = g' x := by simpa using! congr($(hg) x).symm
  rw [hx]
  exact g'.norm_le (norm_nonneg g') |>.mp le_rfl x

@[deprecated (since := "2026-07-19")]
alias exists_norm_eq_restrict_eq := exists_norm_eq_domRestrict_eq

end BoundedContinuousFunction
