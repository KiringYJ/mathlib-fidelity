/-
Copyright (c) 2024 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.VectorField
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
public import Mathlib.Geometry.Manifold.VectorField.Pullback

/-!
# Lie brackets of vector fields on manifolds

We define the Lie bracket of two vector fields, denoted with
`VectorField.mlieBracket I V W x`, as the pullback in the manifold of the corresponding notion
in the model space (through `extChartAt I x`).

The main results are the following:
* `VectorField.mpullback_mlieBracket` states that the pullback of the Lie bracket
  is the Lie bracket of the pullbacks.
* `VectorField.leibniz_identity_mlieBracket` is the Leibniz (or Jacobi)
  identity `[U, [V, W]] = [[U, V], W] + [V, [U, W]]`.

-/

public section

open Set Function Filter NormedSpace
open scoped Topology Manifold ContDiff

noncomputable section

/- We work in the `VectorField` namespace because pullbacks, Lie brackets, and so on, are notions
that make sense in a variety of contexts. We also prefix the notions with `m` to distinguish the
manifold notions from the vector space notions. For instance, the Lie bracket of two vector
fields in a manifold is denoted with `VectorField.mlieBracket I V W x`, where `I` is the relevant
model with corners, `V W : Π (x : M), TangentSpace I x` are the vector fields, and `x : M` is
the basepoint.
-/

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {H : Type*} [TopologicalSpace H] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {H' : Type*} [TopologicalSpace H'] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {I' : ModelWithCorners 𝕜 E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {f : M → M'} {s t : Set M} {x x₀ : M}

namespace VectorField

section LieBracket

/-! ### The Lie bracket of vector fields in manifolds -/

variable {V W V₁ W₁ : Π (x : M), TangentSpace I x}

-- The forward chart derivative gives a representative on the model space. Every use of this
-- representative in the bracket depends only on its germ within the chart target.
local macro "chartRep" E:term:max I:term:max a:term:max V:term:max : term =>
  `(fun z : $E ↦ (mfderiv $I 𝓘(_, $E) (extChartAt $I $a) ((extChartAt $I $a).symm z)
    ($V ((extChartAt $I $a).symm z)) : $E))

private lemma inChart_chartRep (a : M) (V : Π y : M, TangentSpace I y) :
    InChart I a V (chartRep E I a V) := by
  intro y hy
  exact congrArg (fun z : M ↦ mfderiv I 𝓘(𝕜, E) (extChartAt I a) z (V z))
    ((extChartAt I a).left_inv hy)

variable (I) in
/-- The Lie bracket in the chart centered at the point, using the derivative within the set. -/
def mlieBracketWithin (V W : Π x : M, TangentSpace I x) (s : Set M) (x : M) : TangentSpace I x :=
  lieBracketWithin (E := E) 𝕜 (chartRep E I x V) (chartRep E I x W)
    ((extChartAt I x).symm ⁻¹' s ∩ range I) (extChartAt I x x)

variable (I) in
/-- The Lie bracket of two vector fields on a manifold. -/
def mlieBracket (V W : Π x : M, TangentSpace I x) (x : M) : TangentSpace I x :=
  mlieBracketWithin I V W univ x

lemma mlieBracketWithin_def :
    mlieBracketWithin I V W s = fun x ↦
      lieBracketWithin (E := E) 𝕜 (chartRep E I x V) (chartRep E I x W)
      ((extChartAt I x).symm ⁻¹' s ∩ range I) (extChartAt I x x) := by rfl

lemma mlieBracketWithin_apply :
    mlieBracketWithin I V W s x = lieBracketWithin (E := E) 𝕜 (chartRep E I x V) (chartRep E I x W)
      ((extChartAt I x).symm ⁻¹' s ∩ range I) (extChartAt I x x) := by rfl

set_option backward.isDefEq.respectTransparency false in
lemma mlieBracketWithin_eq_lieBracketWithin {V W : Π (x : E), TangentSpace 𝓘(𝕜, E) x} {s : Set E} :
    mlieBracketWithin 𝓘(𝕜, E) V W s = lieBracketWithin 𝕜 V W s := by
  ext x
  simp [mlieBracketWithin_apply]

/- Copy of the `lieBracket` API to manifolds -/

@[simp] lemma mlieBracketWithin_univ :
    mlieBracketWithin I V W univ = mlieBracket I V W := (rfl)

set_option backward.isDefEq.respectTransparency false in
lemma mlieBracketWithin_eq_zero_of_eq_zero (hV : V x = 0) (hW : W x = 0) :
    mlieBracketWithin I V W s x = 0 := by
  rw [mlieBracketWithin_apply]
  apply lieBracketWithin_eq_zero_of_eq_zero (E := E) (𝕜 := 𝕜)
  · simp only [(inChart_chartRep x V) x (mem_extChartAt_source x), hV, map_zero]
  · simp only [(inChart_chartRep x W) x (mem_extChartAt_source x), hW, map_zero]

set_option backward.isDefEq.respectTransparency false in
lemma mlieBracketWithin_swap_apply :
    mlieBracketWithin I V W s x = - mlieBracketWithin I W V s x := by
  exact congrFun (lieBracketWithin_swap (𝕜 := 𝕜) (V := chartRep E I x V)
    (W := chartRep E I x W) (s := _)) (extChartAt I x x)

lemma mlieBracketWithin_swap :
    mlieBracketWithin I V W s = - mlieBracketWithin I W V s := by
  ext x
  exact mlieBracketWithin_swap_apply

lemma mlieBracket_swap_apply : mlieBracket I V W x = - mlieBracket I W V x :=
  mlieBracketWithin_swap_apply

lemma mlieBracket_swap : mlieBracket I V W = - mlieBracket I W V :=
  mlieBracketWithin_swap

set_option backward.isDefEq.respectTransparency false in
@[simp] lemma mlieBracketWithin_self : mlieBracketWithin I V V = 0 := by
  ext x; simp [mlieBracketWithin]

@[simp] lemma mlieBracket_self : mlieBracket I V V = 0 := by
  ext x; simp_rw [mlieBracket, mlieBracketWithin_self, Pi.zero_apply]

set_option backward.isDefEq.respectTransparency false in
/-- We have `[0, W] = 0` for all vector fields `W`: this depends on the junk value 0
if `W` is not differentiable. Version within a set. -/
@[simp]
lemma mlieBracketWithin_zero_left : mlieBracketWithin I 0 W s = 0 := by
  funext x
  change lieBracketWithin 𝕜 (chartRep E I x (0 : Π y : M, TangentSpace I y)) (chartRep E I x W)
    _ _ = 0
  have hz : chartRep E I x (0 : Π y : M, TangentSpace I y) = 0 := funext fun y ↦ map_zero _
  rw [hz, lieBracketWithin_zero_left]
  rfl

/-- We have `[W, 0] = 0` for all vector fields `W`: this depends on the junk value 0
if `W` is not differentiable. Version within a set. -/
@[simp]
lemma mlieBracketWithin_zero_right : mlieBracketWithin I W 0 s = 0 := by
  rw [mlieBracketWithin_swap]; simp

/-- We have `[0, W] = 0` for all vector fields `W`: this depends on the junk value 0
if `W` is not differentiable. -/
@[simp]
lemma mlieBracket_zero_left : mlieBracket I 0 W = 0 := by simp [← mlieBracketWithin_univ]

/-- We have `[W, 0] = 0` for all vector fields `W`: this depends on the junk value 0
if `W` is not differentiable. -/
@[simp]
lemma mlieBracket_zero_right : mlieBracket I W 0 = 0 := by simp [← mlieBracketWithin_univ]

/-- Variant of `mlieBracketWithin_congr_set` where one requires the sets to coincide only in
the complement of a point. -/
theorem mlieBracketWithin_congr_set' (y : M) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    mlieBracketWithin I V W s x = mlieBracketWithin I V W t x := by
  simp only [mlieBracketWithin_apply]
  suffices A : ((extChartAt I x).symm ⁻¹' s ∩ range I : Set E)
    =ᶠ[𝓝[{(extChartAt I x) x}ᶜ] (extChartAt I x x)]
      ((extChartAt I x).symm ⁻¹' t ∩ range I : Set E) by
    apply lieBracketWithin_congr_set' _ A
  exact preimage_extChartAt_eventuallyEqSet_compl_singleton y h

theorem mlieBracketWithin_congr_set (h : s =ᶠ[𝓝 x] t) :
    mlieBracketWithin I V W s x = mlieBracketWithin I V W t x :=
  mlieBracketWithin_congr_set' x <| h.filter_mono inf_le_left

theorem mlieBracketWithin_inter (ht : t ∈ 𝓝 x) :
    mlieBracketWithin I V W (s ∩ t) x = mlieBracketWithin I V W s x := by
  apply mlieBracketWithin_congr_set
  filter_upwards [ht] with y hy
  simp_all

theorem mlieBracketWithin_of_mem_nhds (h : s ∈ 𝓝 x) :
    mlieBracketWithin I V W s x = mlieBracket I V W x := by
  rw [← mlieBracketWithin_univ, ← univ_inter s, mlieBracketWithin_inter h]

theorem mlieBracketWithin_of_isOpen (hs : IsOpen s) (hx : x ∈ s) :
    mlieBracketWithin I V W s x = mlieBracket I V W x :=
  mlieBracketWithin_of_mem_nhds (hs.mem_nhds hx)

/-- Variant of `mlieBracketWithin_eventually_congr_set` where one requires the sets to coincide only
in the complement of a point. -/
theorem mlieBracketWithin_eventually_congr_set' (y : M) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    mlieBracketWithin I V W s =ᶠ[𝓝 x] mlieBracketWithin I V W t :=
  (eventually_nhds_nhdsWithin.2 h).mono fun _ => mlieBracketWithin_congr_set' y

theorem mlieBracketWithin_eventually_congr_set (h : s =ᶠ[𝓝 x] t) :
    mlieBracketWithin I V W s =ᶠ[𝓝 x] mlieBracketWithin I V W t :=
  mlieBracketWithin_eventually_congr_set' x <| h.filter_mono inf_le_left

set_option backward.isDefEq.respectTransparency false in
theorem _root_.Filter.EventuallyEq.mlieBracketWithin_vectorField_eq
    (hV : V₁ =ᶠ[𝓝[s] x] V) (hxV : V₁ x = V x) (hW : W₁ =ᶠ[𝓝[s] x] W) (hxW : W₁ x = W x) :
    mlieBracketWithin I V₁ W₁ s x = mlieBracketWithin I V W s x := by
  simp only [mlieBracketWithin_apply]
  have heq {A B : Π y : M, TangentSpace I y} (h : A =ᶠ[𝓝[s] x] B) :
      chartRep E I x A =ᶠ[𝓝[(extChartAt I x).symm ⁻¹' s ∩ range I] (extChartAt I x x)]
        chartRep E I x B := by
    apply nhdsWithin_mono _ inter_subset_left
    filter_upwards [(continuousAt_extChartAt_symm x).continuousWithinAt.preimage_mem_nhdsWithin''
      h (by simp)] with y hy
    exact congrArg (mfderiv I 𝓘(𝕜, E) (extChartAt I x) ((extChartAt I x).symm y)) hy
  exact (heq hV).lieBracketWithin_vectorField_eq
    (((inChart_chartRep x V₁) x (mem_extChartAt_source x)).trans
      ((congrArg _ hxV).trans ((inChart_chartRep x V) x (mem_extChartAt_source x)).symm)) (heq hW)
    (((inChart_chartRep x W₁) x (mem_extChartAt_source x)).trans
      ((congrArg _ hxW).trans ((inChart_chartRep x W) x (mem_extChartAt_source x)).symm))

theorem _root_.Filter.EventuallyEq.mlieBracketWithin_vectorField_eq_of_mem
    (hV : V₁ =ᶠ[𝓝[s] x] V) (hW : W₁ =ᶠ[𝓝[s] x] W) (hx : x ∈ s) :
    mlieBracketWithin I V₁ W₁ s x = mlieBracketWithin I V W s x :=
  hV.mlieBracketWithin_vectorField_eq (mem_of_mem_nhdsWithin hx hV :)
    hW (mem_of_mem_nhdsWithin hx hW :)

/-- If vector fields coincide on a neighborhood of a point within a set, then the Lie brackets
also coincide on a neighborhood of this point within this set. Version where one considers the Lie
bracket within a subset. -/
theorem _root_.Filter.EventuallyEq.mlieBracketWithin_vectorField'
    (hV : V₁ =ᶠ[𝓝[s] x] V) (hW : W₁ =ᶠ[𝓝[s] x] W) (ht : t ⊆ s) :
    mlieBracketWithin I V₁ W₁ t =ᶠ[𝓝[s] x] mlieBracketWithin I V W t := by
  filter_upwards [hV, hW, eventually_eventually_nhdsWithin.2 hV,
    eventually_eventually_nhdsWithin.2 hW] with y hVy hWy hVy' hWy'
  apply Filter.EventuallyEq.mlieBracketWithin_vectorField_eq
  · apply nhdsWithin_mono _ ht
    exact hVy'
  · exact hVy
  · apply nhdsWithin_mono _ ht
    exact hWy'
  · exact hWy

protected theorem _root_.Filter.EventuallyEq.mlieBracketWithin_vectorField
    (hV : V₁ =ᶠ[𝓝[s] x] V) (hW : W₁ =ᶠ[𝓝[s] x] W) :
    mlieBracketWithin I V₁ W₁ s =ᶠ[𝓝[s] x] mlieBracketWithin I V W s :=
  hV.mlieBracketWithin_vectorField' hW Subset.rfl

protected theorem _root_.Filter.EventuallyEq.mlieBracketWithin_vectorField_of_insert
    (hV : V₁ =ᶠ[𝓝[insert x s] x] V) (hW : W₁ =ᶠ[𝓝[insert x s] x] W) :
    mlieBracketWithin I V₁ W₁ s x = mlieBracketWithin I V W s x := by
  apply mem_of_mem_nhdsWithin (mem_insert x s)
    (hV.mlieBracketWithin_vectorField' hW (subset_insert x s))

theorem _root_.Filter.EventuallyEq.mlieBracketWithin_vectorField_eq_nhds
    (hV : V₁ =ᶠ[𝓝 x] V) (hW : W₁ =ᶠ[𝓝 x] W) :
    mlieBracketWithin I V₁ W₁ s x = mlieBracketWithin I V W s x :=
  (hV.filter_mono nhdsWithin_le_nhds).mlieBracketWithin_vectorField_eq hV.self_of_nhds
    (hW.filter_mono nhdsWithin_le_nhds) hW.self_of_nhds

theorem mlieBracketWithin_congr
    (hV : EqOn V₁ V s) (hVx : V₁ x = V x) (hW : EqOn W₁ W s) (hWx : W₁ x = W x) :
    mlieBracketWithin I V₁ W₁ s x = mlieBracketWithin I V W s x :=
  (hV.eventuallyEq.filter_mono inf_le_right).mlieBracketWithin_vectorField_eq hVx
    (hW.eventuallyEq.filter_mono inf_le_right) hWx

/-- Version of `mlieBracketWithin_congr` in which one assumes that the point belongs to the
given set. -/
theorem mlieBracketWithin_congr' (hV : EqOn V₁ V s) (hW : EqOn W₁ W s) (hx : x ∈ s) :
    mlieBracketWithin I V₁ W₁ s x = mlieBracketWithin I V W s x :=
  mlieBracketWithin_congr hV (hV hx) hW (hW hx)

theorem _root_.Filter.EventuallyEq.mlieBracket_vectorField_eq
    (hV : V₁ =ᶠ[𝓝 x] V) (hW : W₁ =ᶠ[𝓝 x] W) :
    mlieBracket I V₁ W₁ x = mlieBracket I V W x := by
  rw [← mlieBracketWithin_univ, ← mlieBracketWithin_univ,
    hV.mlieBracketWithin_vectorField_eq_nhds hW]

protected theorem _root_.Filter.EventuallyEq.mlieBracket_vectorField
    (hV : V₁ =ᶠ[𝓝 x] V) (hW : W₁ =ᶠ[𝓝 x] W) : mlieBracket I V₁ W₁ =ᶠ[𝓝 x] mlieBracket I V W := by
  filter_upwards [hV.eventuallyEq_nhds, hW.eventuallyEq_nhds] with y hVy hWy
  exact hVy.mlieBracket_vectorField_eq hWy

section

variable {c : 𝕜}
variable [IsManifold I 2 M]

lemma _root_.MDifferentiableWithinAt.differentiableWithinAt_mpullbackWithin_vectorField
    (hV : MDiffAt[s] (fun x ↦ (V x : TangentBundle I M)) x) :
    DifferentiableWithinAt 𝕜 (chartRep E I x V)
      ((extChartAt I x).symm ⁻¹' s ∩ range I) (extChartAt I x x) := by
  let e := extChartAt I x
  let b := trivializationAt E (TangentSpace I) x
  have heq (z : E) (hz : z ∈ e.target) :
      (chartRep E I x V) z = (b ⟨e.symm z, V (e.symm z)⟩).2 := by
    have hy : e.symm z ∈ (chartAt H x).source := by
      simpa only [e, extChartAt_source] using (e.map_target hz)
    have h := congrArg (fun A : TangentSpace I (e.symm z) →L[𝕜] E ↦ A (V (e.symm z)))
      (TangentBundle.continuousLinearMapAt_trivializationAt (I := I) hy)
    exact h.symm.trans (b.continuousLinearMapAt_apply_of_mem 𝕜
      (by simpa only [b, TangentBundle.trivializationAt_baseSet] using hy) _)
  have hv := (mdifferentiableWithinAt_section I V).mp hV
  have hreg := hv.differentiableWithinAt_comp_extChartAt_symm
  apply hreg.congr_of_eventuallyEq _ (heq _ (mem_extChartAt_target x))
  filter_upwards [nhdsWithin_mono _ inter_subset_right (extChartAt_target_mem_nhdsWithin x)]
    with z hz using heq z hz

/-- At the chart center the derivative of the chart and of its inverse are mutually inverse. -/
lemma mfderiv_extChartAt_inverse_comp_mfderivWithin_extChartAT_symm (Y : TangentSpace I x) :
    let e := extChartAt I x
    (mfderivWithin 𝓘(𝕜, E) I e.symm (range I) (e x)) (mfderiv I 𝓘(𝕜, E) e x Y) = Y := by
  dsimp only
  have h := congrArg (fun L : TangentSpace I x →L[𝕜] TangentSpace I x ↦ L Y)
    (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' (I := I)
      (x := x) (mem_extChartAt_source x))
  exact h

/-- In the centered chart, the differential of a scalar function acts on the coordinate
representative of the vector just as the manifold derivative acts on the original vector. -/
lemma mpullback_mfderivWithin_apply_smul {f : M → 𝕜} (hf : MDiffAt[s] f x) :
    (fderivWithin 𝕜 (f ∘ (extChartAt I x).symm) ((extChartAt I x).symm ⁻¹' s ∩ range I)
      (extChartAt I x x) id ((chartRep E I x V) (extChartAt I x x))) •
      (chartRep E I x W) (extChartAt I x x) = (d[s] f x) (V x) • W x := by
  rw [(inChart_chartRep x V) x (mem_extChartAt_source x),
    (inChart_chartRep x W) x (mem_extChartAt_source x),
    mfderiv_extChartAt_self]
  rw [hf.mvfderivWithin]
  simp only [writtenInExtChartAt, comp_def, mfld_simps]
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
Product rule for Lie brackets: given two vector fields `V` and `W` on `M` and a function
`f : M → 𝕜`, we have `[V, f • W] = (df V) • W + f • [V, W]`. Version within a set.
-/
lemma mlieBracketWithin_smul_right {f : M → 𝕜} (hf : MDiffAt[s] f x)
    (hW : MDiffAt[s] (fun x ↦ (W x : TangentBundle I M)) x)
    (hs : UniqueMDiffAt[s] x) :
    mlieBracketWithin I V (f • W) s x =
      d[s] f x (V x) • (W x) + (f x) • mlieBracketWithin I V W s x := by
  have heq : chartRep E I x (f • W) =
      fun z ↦ f ((extChartAt I x).symm z) • (chartRep E I x W) z := by
    exact funext fun z ↦ map_smul _ _ _
  simp only [mlieBracketWithin_apply, heq]
  have hB := lieBracketWithin_smul_right (V := chartRep E I x V)
    hf.differentiableWithinAt_comp_extChartAt_symm
    hW.differentiableWithinAt_mpullbackWithin_vectorField
    (uniqueMDiffWithinAt_iff_inter_range.1 hs)
  refine hB.trans ?_
  exact congrArg₂ (· + ·) (mpullback_mfderivWithin_apply_smul hf)
    (congrArg (fun y ↦ f y • _) (extChartAt_to_inv x))

/--
Product rule for Lie brackets: given two vector fields `V` and `W` on `M` and a function
`f : M → 𝕜`, we have `[V, f • W] = (df V) • W + f • [V, W]`.
-/
lemma mlieBracket_smul_right {f : M → 𝕜} (hf : MDiffAt f x)
    (hW : MDiffAt (fun x ↦ (W x : TangentBundle I M)) x) :
    mlieBracket I V (f • W) x = d% f x (V x) • (W x) + (f x) • mlieBracket I V W x := by
  rw [← mdifferentiableWithinAt_univ] at hf hW
  rw [← mlieBracketWithin_univ, ← mvfderivWithin_univ]
  exact mlieBracketWithin_smul_right hf hW (uniqueMDiffWithinAt_univ I)

/--
Product rule for Lie brackets: given two vector fields `V` and `W` on `M` and a function
`f : M → 𝕜`, we have `[f • V, W] = -(df W) • V + f • [V, W]`. Version within a set.
-/
lemma mlieBracketWithin_smul_left {f : M → 𝕜} (hf : MDiffAt[s] f x)
    (hV : MDiffAt[s] (fun x ↦ (V x : TangentBundle I M)) x)
    (hs : UniqueMDiffAt[s] x) :
    mlieBracketWithin I (f • V) W s x =
      - d[s] f x (W x) • (V x) + (f x) • mlieBracketWithin I V W s x := by
  rw [mlieBracketWithin_swap, Pi.neg_apply, mlieBracketWithin_smul_right hf hV (V := W) hs,
    mlieBracketWithin_swap]
  simp; abel

/--
Product rule for Lie brackets: given two vector fields `V` and `W` on `M` and a function
`f : M → 𝕜`, we have `[f • V, W] = -(df W) • V + f • [V, W]`.
-/
lemma mlieBracket_smul_left {f : M → 𝕜} (hf : MDiffAt f x)
    (hV : MDiffAt (fun x ↦ (V x : TangentBundle I M)) x) :
    mlieBracket I (f • V) W x = - d% f x (W x) • (V x) + (f x) • mlieBracket I V W x := by
  rw [← mdifferentiableWithinAt_univ] at hf hV
  rw [← mlieBracketWithin_univ, mvfderiv, ← mfderivWithin_univ]
  exact mlieBracketWithin_smul_left hf hV (uniqueMDiffWithinAt_univ I)

lemma mlieBracketWithin_const_smul_left
    (hV : MDiffAt[s] (T% V) x) (hs : UniqueMDiffAt[s] x) :
    mlieBracketWithin I (c • V) W s x = c • mlieBracketWithin I V W s x := by
  simpa [mfderivWithin_const, mvfderivWithin] using!
    mlieBracketWithin_smul_left (mdifferentiableWithinAt_const (c := c)) (W := W) hV hs

lemma mlieBracket_const_smul_left (hV : MDiffAt (T% V) x) :
    mlieBracket I (c • V) W x = c • mlieBracket I V W x := by
  simp only [← mlieBracketWithin_univ] at hV ⊢
  exact mlieBracketWithin_const_smul_left hV (uniqueMDiffWithinAt_univ _)

lemma mlieBracketWithin_const_smul_right
    (hW : MDiffAt[s] (T% W) x) (hs : UniqueMDiffAt[s] x) :
    mlieBracketWithin I V (c • W) s x = c • mlieBracketWithin I V W s x := by
  simpa [mfderivWithin_const, mvfderivWithin] using!
    mlieBracketWithin_smul_right (mdifferentiableWithinAt_const (c := c)) (V := V) hW hs

lemma mlieBracket_const_smul_right (hW : MDiffAt (T% W) x) :
    mlieBracket I V (c • W) x = c • mlieBracket I V W x := by
  simp only [← mlieBracketWithin_univ] at hW ⊢
  exact mlieBracketWithin_const_smul_right hW (uniqueMDiffWithinAt_univ _)

set_option backward.isDefEq.respectTransparency false in
lemma mlieBracketWithin_add_left
    (hV : MDiffAt[s] (T% V) x) (hV₁ : MDiffAt[s] (T% V₁) x) (hs : UniqueMDiffAt[s] x) :
    mlieBracketWithin I (V + V₁) W s x =
      mlieBracketWithin I V W s x + mlieBracketWithin I V₁ W s x := by
  simp only [mlieBracketWithin_apply]
  have heq : chartRep E I x (V + V₁) = chartRep E I x V + chartRep E I x V₁ :=
    funext fun z ↦ map_add _ _ _
  rw [heq, lieBracketWithin_add_left]
  · exact hV.differentiableWithinAt_mpullbackWithin_vectorField
  · exact hV₁.differentiableWithinAt_mpullbackWithin_vectorField
  · exact uniqueMDiffWithinAt_iff_inter_range.1 hs

lemma mlieBracket_add_left (hV : MDiffAt (T% V) x) (hV₁ : MDiffAt (T% V₁) x) :
    mlieBracket I (V + V₁) W x = mlieBracket I V W x + mlieBracket I V₁ W x := by
  simp only [← mlieBracketWithin_univ] at hV hV₁ ⊢
  exact mlieBracketWithin_add_left hV hV₁ (uniqueMDiffWithinAt_univ _)

lemma mlieBracketWithin_add_right
    (hW : MDiffAt[s] (T% W) x) (hW₁ : MDiffAt[s] (T% W₁) x) (hs : UniqueMDiffAt[s] x) :
    mlieBracketWithin I V (W + W₁) s x =
      mlieBracketWithin I V W s x + mlieBracketWithin I V W₁ s x := by
  rw [mlieBracketWithin_swap, Pi.neg_apply, mlieBracketWithin_add_left hW hW₁ hs,
    mlieBracketWithin_swap (V := V), mlieBracketWithin_swap (V := V), Pi.neg_apply, Pi.neg_apply]
  abel

lemma mlieBracket_add_right (hW : MDiffAt (T% W) x) (hW₁ : MDiffAt (T% W₁) x) :
    mlieBracket I V (W + W₁) x = mlieBracket I V W x + mlieBracket I V W₁ x := by
  simp only [← mlieBracketWithin_univ] at hW hW₁ ⊢
  exact mlieBracketWithin_add_right hW hW₁ (uniqueMDiffWithinAt_univ _)

set_option backward.isDefEq.respectTransparency false in
theorem mlieBracketWithin_of_mem_nhdsWithin (st : t ∈ 𝓝[s] x) (hs : UniqueMDiffAt[s] x)
    (hV : MDiffAt[t] (T% V) x) (hW : MDiffAt[t] (T% W) x) :
    mlieBracketWithin I V W s x = mlieBracketWithin I V W t x := by
  simp only [mlieBracketWithin_apply]
  rw [lieBracketWithin_of_mem_nhdsWithin (t := (extChartAt I x).symm ⁻¹' t ∩ range I)]
  · apply Filter.inter_mem
    · apply nhdsWithin_mono _ inter_subset_left <|
        (continuousAt_extChartAt_symm x).continuousWithinAt.preimage_mem_nhdsWithin'' st (by simp)
    · exact nhdsWithin_mono _ inter_subset_right self_mem_nhdsWithin
  · exact uniqueMDiffWithinAt_iff_inter_range.1 hs
  · exact hV.differentiableWithinAt_mpullbackWithin_vectorField
  · exact hW.differentiableWithinAt_mpullbackWithin_vectorField

theorem mlieBracketWithin_subset (st : s ⊆ t) (ht : UniqueMDiffAt[s] x)
    (hV : MDiffAt[t] (T% V) x) (hW : MDiffAt[t] (T% W) x) :
    mlieBracketWithin I V W s x = mlieBracketWithin I V W t x :=
  mlieBracketWithin_of_mem_nhdsWithin (nhdsWithin_mono _ st self_mem_nhdsWithin) ht hV hW

theorem mlieBracketWithin_eq_mlieBracket (hs : UniqueMDiffAt[s] x)
    (hV : MDiffAt (T% V) x) (hW : MDiffAt (T% W) x) :
    mlieBracketWithin I V W s x = mlieBracket I V W x := by
  simp only [← mlieBracketWithin_univ, ← mdifferentiableWithinAt_univ] at hV hW ⊢
  exact mlieBracketWithin_subset (subset_univ _) hs hV hW

theorem _root_.DifferentiableWithinAt.mlieBracketWithin_congr_mono
    (hV : MDiffAt[s] (T% V) x) (hVs : EqOn V₁ V t) (hVx : V₁ x = V x)
    (hW : MDiffAt[s] (T% W) x) (hWs : EqOn W₁ W t) (hWx : W₁ x = W x)
    (hxt : UniqueMDiffAt[t] x) (h₁ : t ⊆ s) :
    mlieBracketWithin I V₁ W₁ t x = mlieBracketWithin I V W s x := by
  rw [mlieBracketWithin_congr hVs hVx hWs hWx]
  exact mlieBracketWithin_subset h₁ hxt hV hW

end

section Invariance_IsSymmSndFDerivWithinAt

variable [IsManifold I 2 M] [IsManifold I' 2 M'] [CompleteSpace E]

omit [CompleteSpace E] in
/-- The bracket of two differentiable related fields is related to the target bracket. -/
lemma IsMRelatedWithinAt.mlieBracketWithin
    {U Z : Π y : M, TangentSpace I y} {V W : Π y : M', TangentSpace I' y} {t : Set M'}
    (hV : MDiffAt[t] (T% V) (f x₀)) (hW : MDiffAt[t] (T% W) (f x₀))
    (hs : UniqueMDiff[s]) (hf : CMDiffAt[s] 2 f x₀) (hx : x₀ ∈ s)
    (hst : f ⁻¹' t ∈ 𝓝[s] x₀)
    (hsymm : IsSymmSndFDerivWithinAt 𝕜 (writtenInExtChartAt I I' x₀ f)
      ((extChartAt I x₀).symm ⁻¹' s ∩ range I) (extChartAt I x₀ x₀))
    (hU : MDiffAt[s] (T% U) x₀) (hZ : MDiffAt[s] (T% Z) x₀)
    (hUV : ∀ᶠ y in 𝓝[s] x₀, IsMRelatedWithinAt f U V s y)
    (hZW : ∀ᶠ y in 𝓝[s] x₀, IsMRelatedWithinAt f Z W s y) :
    IsMRelatedWithinAt f (VectorField.mlieBracketWithin I U Z s)
      (VectorField.mlieBracketWithin I' V W t) s x₀ := by
  let e := extChartAt I x₀
  let e' := extChartAt I' (f x₀)
  let F := writtenInExtChartAt I I' x₀ f
  let S := e.symm ⁻¹' s ∩ range I
  let T := e'.symm ⁻¹' t ∩ range I'
  have he : e.symm (e x₀) = x₀ := extChartAt_to_inv x₀
  have hfchart : f ⁻¹' e'.source ∈ 𝓝[s] x₀ :=
    hf.continuousWithinAt.preimage_mem_nhdsWithin (extChartAt_source_mem_nhds _)
  obtain ⟨o, ho, hxo, hos⟩ := mem_nhdsWithin.mp (inter_mem hst hfchart)
  let R := e.symm ⁻¹' (s ∩ o) ∩ e.target
  have hRS : R =ᶠ[𝓝 (e x₀)] S := by
    apply EventuallyEqSet.inter _ extChartAt_target_eventuallyEqSet
    have hnear : e.symm ⁻¹' o ∈ 𝓝 (e x₀) := by
      apply (continuousAt_extChartAt_symm x₀).preimage_mem_nhds
      change o ∈ 𝓝 (e.symm (e x₀))
      rw [he]
      exact ho.mem_nhds hxo
    filter_upwards [hnear] with z hz
    exact propext (and_iff_left hz)
  have hu : UniqueDiffOn 𝕜 R := by
    rw [show R = e.target ∩ e.symm ⁻¹' (s ∩ o) from inter_comm ..]
    exact UniqueMDiffOn.uniqueDiffOn_target_inter (hs.inter ho) x₀
  have hp : e x₀ ∈ R := by
    refine ⟨?_, mem_extChartAt_target _⟩
    change e.symm (e x₀) ∈ s ∩ o
    rw [he]
    exact ⟨hx, hxo⟩
  have hlim : Tendsto e.symm (𝓝[R] (e x₀)) (𝓝[s] x₀) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, eventually_nhdsWithin_of_forall fun z hz ↦ hz.1.1⟩
    have hc : Tendsto e.symm (𝓝 (e x₀)) (𝓝 (e.symm (e x₀))) :=
      continuousAt_extChartAt_symm x₀
    rw [he] at hc
    exact hc.mono_left nhdsWithin_le_nhds
  have hFT : MapsTo F R T := by
    intro z hz
    have hw := hos (show e.symm z ∈ o ∩ s from ⟨hz.1.2, hz.1.1⟩)
    refine ⟨?_, mem_range_self _⟩
    change e'.symm (e' (f (e.symm z))) ∈ t
    rw [e'.left_inv hw.2]
    exact hw.1
  have hFp : F (e x₀) = e' (f x₀) := congrArg (fun y ↦ e' (f y)) he
  have hF : ContDiffWithinAt 𝕜 2 F R (e x₀) := (contMDiffWithinAt_iff.mp hf).2.congr_set hRS.symm
  have transport {A : Π y : M, TangentSpace I y} {B : Π y : M', TangentSpace I' y}
      (hAB : ∀ᶠ y in 𝓝[s] x₀, IsMRelatedWithinAt f A B s y) :
      ∀ᶠ z in 𝓝[R] (e x₀), IsRelatedWithinAt (𝕜 := 𝕜) F
        (chartRep E I x₀ A) (chartRep E' I' (f x₀) B) R z := by
    filter_upwards [self_mem_nhdsWithin, hlim.eventually hAB] with z hz hrel
    have hw := hos (show e.symm z ∈ o ∩ s from ⟨hz.1.2, hz.1.1⟩)
    have hIn := (inChart_chartRep x₀ A).isMRelatedWithinAt hz.2
    have hOut : IsMRelatedWithinAt (I' := 𝓘(𝕜, E')) e' B (chartRep E' I' (f x₀) B) univ
        (f (e.symm z)) := by
      have hc := mdifferentiableAt_extChartAt (I := I') (by simpa [e'] using hw.2)
      refine ⟨_, hc.hasMFDerivAt.hasMFDerivWithinAt, ?_⟩
      exact ((inChart_chartRep (f x₀) B) _ hw.2).symm
    have hR : R ⊆ range I := inter_subset_right.trans (extChartAt_target_subset_range _)
    have h1 := hIn.mono hR
    have h2 := hrel.comp h1 (fun _ (hz : _ ∈ R) ↦ hz.1.1)
    exact (hOut.comp (f := f ∘ e.symm) h2 (mapsTo_univ _ _)).to_model
  have hsource {A : Π y : M, TangentSpace I y} (hA : MDiffAt[s] (T% A) x₀) :
      DifferentiableWithinAt 𝕜 (chartRep E I x₀ A) R (e x₀) :=
    hA.differentiableWithinAt_mpullbackWithin_vectorField.congr_nhds
      (nhdsWithin_eq_iff_eventuallyEqSet.mpr hRS.symm)
  have htarget {B : Π y : M', TangentSpace I' y} (hB : MDiffAt[t] (T% B) (f x₀)) :
      DifferentiableWithinAt 𝕜 (chartRep E' I' (f x₀) B) T (F (e x₀)) := by
    rw [hFp]
    exact hB.differentiableWithinAt_mpullbackWithin_vectorField
  have hbr := IsRelatedWithinAt.lieBracketWithin (hsymm.congr_set hRS.symm) hF
    (htarget hV) (htarget hW) hu hp hFT (hsource hU) (hsource hZ) (transport hUV) (transport hZW)
  have hb := hbr.fderivWithin_apply (hu _ hp)
  change fderivWithin 𝕜 F R (e x₀) id (lieBracketWithin 𝕜 (chartRep E I x₀ U)
    (chartRep E I x₀ Z) R (e x₀)) = lieBracketWithin 𝕜 (chartRep E' I' (f x₀) V)
    (chartRep E' I' (f x₀) W) T (F (e x₀)) at hb
  have hbrS := VectorField.lieBracketWithin_congr_set (𝕜 := 𝕜)
    (V := chartRep E I x₀ U) (W := chartRep E I x₀ Z) hRS
  rw [hFp, fderivWithin_congr_set hRS, hbrS] at hb
  have hdf := hf.mdifferentiableWithinAt two_ne_zero
  refine ⟨_, hdf.hasMFDerivWithinAt, ?_⟩
  rw [hdf.mfderivWithin_abuse]
  exact hb

/-- Pullback commutes with the Lie bracket on a germ with invertible derivative. -/
lemma mpullbackWithin_mlieBracketWithin_of_isSymmSndFDerivWithinAt
    {V W : Π y : M', TangentSpace I' y} {U Z : Π y : M, TangentSpace I y} {t : Set M'}
    (hV : MDiffAt[t] (T% V) (f x₀)) (hW : MDiffAt[t] (T% W) (f x₀))
    (hs : UniqueMDiff[s]) (hf : CMDiffAt[s] 2 f x₀) (hx : x₀ ∈ s)
    (hst : f ⁻¹' t ∈ 𝓝[s] x₀)
    (hsymm : IsSymmSndFDerivWithinAt 𝕜 (writtenInExtChartAt I I' x₀ f)
      ((extChartAt I x₀).symm ⁻¹' s ∩ range I) (extChartAt I x₀ x₀))
    (h : (mfderiv[s] f x₀).IsInvertible)
    (hUV : ∀ᶠ y in 𝓝[s] x₀, IsMRelatedWithinAt f U V s y)
    (hZW : ∀ᶠ y in 𝓝[s] x₀, IsMRelatedWithinAt f Z W s y) :
    mpullbackWithin I I' f (mlieBracketWithin I' V W t) s x₀
      ((hf.mdifferentiableWithinAt two_ne_zero).existsUnique_mfderivWithin (hs _ hx))
      (h.existsUnique_preimage _) = mlieBracketWithin I U Z s x₀ := by
  have hreg {A : Π y : M, TangentSpace I y} {B : Π y : M', TangentSpace I' y}
      (hB : MDiffAt[t] (T% B) (f x₀)) (hAB : ∀ᶠ y in 𝓝[s] x₀, IsMRelatedWithinAt f A B s y) :
      MDiffAt[s] (T% A) x₀ := by
    apply (hB.mpullbackWithin_vectorField_inter hf h hx hs le_rfl ?_).mono_of_mem_nhdsWithin
      (inter_mem self_mem_nhdsWithin hst)
    exact hAB.filter_mono (nhdsWithin_mono _ (insert_subset hx inter_subset_left))
  exact mpullbackWithin_apply.mpr ((IsMRelatedWithinAt.mlieBracketWithin hV hW hs hf hx hst hsymm
    (hreg hV hUV) (hreg hW hZW) hUV hZW).mfderivWithin_apply (hs _ hx))

end Invariance_IsSymmSndFDerivWithinAt

section Invariance

variable [IsManifold I (minSmoothness 𝕜 2) M] [IsManifold I' (minSmoothness 𝕜 2) M']
  [CompleteSpace E] {n : ℕ∞ω}

/-- The pullback commutes with the Lie bracket of vector fields on manifolds. Version where one
assumes that the map is smooth on a larger set `u` (so that the
condition `x₀ ∈ closure (interior u)`, needed to guarantee the symmetry of the second derivative,
becomes easier to check.) -/
lemma mpullbackWithin_mlieBracketWithin'
    {U Z : Π y : M, TangentSpace I y} {f : M → M'} {V W : Π x : M', TangentSpace I' x}
    {x₀ : M} {s u : Set M} {t : Set M'}
    (hV : MDiffAt[t] (T% V) (f x₀)) (hW : MDiffAt[t] (T% W) (f x₀))
    (hs : UniqueMDiff[s]) (hu : UniqueMDiff[u])
    (hf : CMDiffAt[u] n f x₀) (hx₀ : x₀ ∈ s) (hn : minSmoothness 𝕜 2 ≤ n)
    (hst : f ⁻¹' t ∈ 𝓝[s] x₀) (h'x₀ : x₀ ∈ closure (interior u)) (hsu : s ⊆ u)
    (h : (mfderivWithin I I' f s x₀).IsInvertible)
    (hUV : ∀ᶠ y in 𝓝[s] x₀, IsMRelatedWithinAt f U V s y)
    (hZW : ∀ᶠ y in 𝓝[s] x₀, IsMRelatedWithinAt f Z W s y) :
    mpullbackWithin I I' f (mlieBracketWithin I' V W t) s x₀
      ((((hf.mono hsu).of_le (le_minSmoothness.trans hn)).mdifferentiableWithinAt
        two_ne_zero).existsUnique_mfderivWithin (hs _ hx₀))
      (h.existsUnique_preimage _) = mlieBracketWithin I U Z s x₀ := by
  have B : ContDiffWithinAt 𝕜 n ((extChartAt I' (f x₀)) ∘ f ∘ (extChartAt I x₀).symm)
      ((extChartAt I x₀).symm ⁻¹' u ∩ (extChartAt I x₀).target) (extChartAt I x₀ x₀) := by
    apply (contMDiffWithinAt_iff.1 hf).2.congr_set
    exact EventuallyEqSet.inter (by rfl) extChartAt_target_eventuallyEqSet.symm
  refine mpullbackWithin_mlieBracketWithin_of_isSymmSndFDerivWithinAt hV hW hs
    ((hf.mono hsu).of_le (le_minSmoothness.trans hn)) hx₀ hst ?_ h hUV hZW
  have : ((extChartAt I x₀).symm ⁻¹' s ∩ (extChartAt I x₀).target : Set E)
      =ᶠ[𝓝 (extChartAt I x₀ x₀)] (extChartAt I x₀).symm ⁻¹' s ∩ range I :=
    EventuallyEqSet.inter (by rfl) extChartAt_target_eventuallyEqSet
  apply IsSymmSndFDerivWithinAt.congr_set _ this
  have : IsSymmSndFDerivWithinAt 𝕜 ((extChartAt I' (f x₀)) ∘ f ∘ (extChartAt I x₀).symm)
      ((extChartAt I x₀).symm ⁻¹' u ∩ (extChartAt I x₀).target) (extChartAt I x₀ x₀) := by
    apply ContDiffWithinAt.isSymmSndFDerivWithinAt (n := minSmoothness 𝕜 2) _ le_rfl
    · rw [inter_comm]
      exact UniqueMDiffOn.uniqueDiffOn_target_inter hu x₀
    · apply extChartAt_mem_closure_interior h'x₀ (mem_extChartAt_source x₀)
    · simp [hsu hx₀]
    · exact B.of_le hn
  apply IsSymmSndFDerivWithinAt.mono_of_mem_nhdsWithin this
  · apply mem_of_superset self_mem_nhdsWithin (inter_subset_inter_left _ (preimage_mono hsu))
  · exact (B.of_le hn).of_le le_minSmoothness
  · rw [inter_comm]
    exact UniqueMDiffOn.uniqueDiffOn_target_inter hs x₀
  · rw [inter_comm]
    exact UniqueMDiffOn.uniqueDiffOn_target_inter hu x₀
  · simp [hx₀]

/-- The pullback commutes with the Lie bracket of vector fields on manifolds. -/
lemma mpullbackWithin_mlieBracketWithin
    {U Z : Π y : M, TangentSpace I y} {f : M → M'} {V W : Π x : M', TangentSpace I' x}
    {x₀ : M} {s : Set M} {t : Set M'}
    (hV : MDiffAt[t] (T% V) (f x₀)) (hW : MDiffAt[t] (T% W) (f x₀))
    (hu : UniqueMDiff[s]) (hf : CMDiffAt[s] n f x₀) (hx₀ : x₀ ∈ s)
    (hn : minSmoothness 𝕜 2 ≤ n)
    (hst : f ⁻¹' t ∈ 𝓝[s] x₀) (h'x₀ : x₀ ∈ closure (interior s))
    (h : (mfderivWithin I I' f s x₀).IsInvertible)
    (hUV : ∀ᶠ y in 𝓝[s] x₀, IsMRelatedWithinAt f U V s y)
    (hZW : ∀ᶠ y in 𝓝[s] x₀, IsMRelatedWithinAt f Z W s y) :
    mpullbackWithin I I' f (mlieBracketWithin I' V W t) s x₀
      (((hf.of_le (le_minSmoothness.trans hn)).mdifferentiableWithinAt
        two_ne_zero).existsUnique_mfderivWithin (hu _ hx₀))
      (h.existsUnique_preimage _) = mlieBracketWithin I U Z s x₀ :=
  mpullbackWithin_mlieBracketWithin' hV hW hu hu hf hx₀ hn hst h'x₀ Subset.rfl h hUV hZW

/-- The pullback commutes with the Lie bracket of vector fields on manifolds. -/
lemma mpullback_mlieBracketWithin
    {U Z : Π y : M, TangentSpace I y} {f : M → M'} {V W : Π x : M', TangentSpace I' x}
    {x₀ : M} {s : Set M} {t : Set M'}
    (hV : MDiffAt[t] (T% V) (f x₀)) (hW : MDiffAt[t] (T% W) (f x₀))
    (hu : UniqueMDiff[s]) (hf : CMDiffAt n f x₀) (hx₀ : x₀ ∈ s)
    (hn : minSmoothness 𝕜 2 ≤ n) (hst : f ⁻¹' t ∈ 𝓝[s] x₀)
    (h : (mfderiv I I' f x₀).IsInvertible)
    (hUV : ∀ᶠ y in 𝓝[s] x₀, IsMRelatedWithinAt f U V univ y)
    (hZW : ∀ᶠ y in 𝓝[s] x₀, IsMRelatedWithinAt f Z W univ y) :
      mpullback I I' f (mlieBracketWithin I' V W t) x₀
      ((hf.of_le (le_minSmoothness.trans hn)).mdifferentiableAt two_ne_zero)
      (h.existsUnique_preimage _) = mlieBracketWithin I U Z s x₀ := by
  have hd := (hf.of_le (le_minSmoothness.trans hn)).mdifferentiableAt two_ne_zero
  have heq := mfderivWithin_eq_mfderiv (hu _ hx₀) hd
  apply mpullback_apply.mpr
  rw [← heq]
  exact mpullbackWithin_apply.mp (mpullbackWithin_mlieBracketWithin' hV hW hu uniqueMDiffOn_univ
    hf.contMDiffWithinAt hx₀ hn hst (by simp) (subset_univ _) (heq ▸ h)
    (hUV.mono fun _ hy ↦ hy.mono (subset_univ _)) (hZW.mono fun _ hy ↦ hy.mono (subset_univ _)))

lemma mpullback_mlieBracket {U Z : Π y : M, TangentSpace I y}
    {f : M → M'} {V W : Π (x : M'), TangentSpace I' x} {x₀ : M}
    (hV : MDiffAt (T% V) (f x₀)) (hW : MDiffAt (T% W) (f x₀))
    (hf : CMDiffAt n f x₀) (hn : minSmoothness 𝕜 2 ≤ n)
    (h : (mfderiv I I' f x₀).IsInvertible)
    (hUV : ∀ᶠ y in 𝓝 x₀, IsMRelatedWithinAt f U V univ y)
    (hZW : ∀ᶠ y in 𝓝 x₀, IsMRelatedWithinAt f Z W univ y) :
    mpullback I I' f (mlieBracket I' V W) x₀
      ((hf.of_le (le_minSmoothness.trans hn)).mdifferentiableAt two_ne_zero)
      (h.existsUnique_preimage _) = mlieBracket I U Z x₀ := by
  exact mpullback_mlieBracketWithin hV.mdifferentiableWithinAt hW.mdifferentiableWithinAt
    uniqueMDiffOn_univ hf (mem_univ _) hn (by simp) h (by simpa using hUV) (by simpa using hZW)

omit [CompleteSpace E] in
private lemma InChart.eventually_related {a y : M} {U : Π z : M, TangentSpace I z} {P : E → E}
    (hp : InChart I a U P) (hy : y ∈ (extChartAt I a).source) :
    ∀ᶠ z in 𝓝[s] y, IsMRelatedWithinAt (I' := 𝓘(𝕜, E)) (extChartAt I a) U P univ z := by
  filter_upwards [extChartAt_source_mem_nhdsWithin' hy] with z hz
  exact ⟨_, (mdifferentiableAt_extChartAt (by simpa using hz)).hasMFDerivAt.hasMFDerivWithinAt,
    (hp z hz).symm⟩

/-- The bracket in a fixed chart represents the manifold bracket at every nearby point where
the coordinate fields are differentiable. -/
private lemma related_chart_bracket {a y : M} {U V : Π z : M, TangentSpace I z}
    {P Q : Π z : E, TangentSpace 𝓘(𝕜, E) z} {t : Set E}
    (hP : MDiffAt[t] (T% P) (extChartAt I a y)) (hQ : MDiffAt[t] (T% Q) (extChartAt I a y))
    (hs' : UniqueMDiffOn I s) (hy : y ∈ s)
    (hyc : y ∈ (extChartAt I a).source) (hpre : (extChartAt I a) ⁻¹' t ∈ 𝓝[s] y)
    (hU : ∀ᶠ z in 𝓝[s] y, IsMRelatedWithinAt (I' := 𝓘(𝕜, E)) (extChartAt I a) U P univ z)
    (hV : ∀ᶠ z in 𝓝[s] y, IsMRelatedWithinAt (I' := 𝓘(𝕜, E)) (extChartAt I a) V Q univ z) :
    IsMRelatedWithinAt (I' := 𝓘(𝕜, E)) (extChartAt I a) (mlieBracketWithin I U V s)
      (mlieBracketWithin 𝓘(𝕜, E) P Q t) univ y := by
  have hp := mpullback_mlieBracketWithin (n := minSmoothness 𝕜 2) hP hQ hs'
    (contMDiffAt_extChartAt' (by simpa using hyc)) hy le_rfl hpre
    (isInvertible_mfderiv_extChartAt hyc) hU hV
  have hd := mdifferentiableAt_extChartAt (I := I) (by simpa using hyc)
  refine ⟨_, hd.hasMFDerivAt.hasMFDerivWithinAt, ?_⟩
  exact mpullback_apply.mp hp

/-- If two vector fields are `C^n` with `n ≥ m + 1`, then their Lie bracket is `C^m`. -/
protected lemma _root_.ContMDiffWithinAt.mlieBracketWithin_vectorField
    {m : ℕ∞ω}
    {U V : Π (x : M), TangentSpace I x} {s : Set M} {x : M}
    (hU : CMDiffAt[s] n (T% U) x) (hV : CMDiffAt[s] n (T% V) x)
    (hs : UniqueMDiff[s]) (hx : x ∈ s) (hmn : minSmoothness 𝕜 (m + 1) ≤ n) :
    CMDiffAt[s] m (T% (mlieBracketWithin I U V s)) x := by
  /- The statement is not obvious, since at different points the Lie bracket is defined using
  different charts. However, since we know that the Lie bracket is invariant under diffeos, we can
  use a single chart to prove the statement. Let `U'` and `V'` denote the pullbacks of `U` and `V`
  in the chart around `x`. Then the Lie bracket there is smooth (as it coincides with the vector
  space Lie bracket, given by an explicit formula). Pulling back this Lie bracket in `M` gives
  locally a smooth function, which coincides with the initial Lie bracket by invariance
  under diffeos. -/
  apply contMDiffWithinAt_iff_le_ne_infty.2 (fun m' hm' h'm' ↦ ?_)
  have hn : 1 ≤ m' + 1 := le_add_self
  have hm'n : m' + 1 ≤ n := by grw [hm', ← hmn, ← le_minSmoothness]
  have pre_mem : (extChartAt I x) ⁻¹' ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s)
      ∈ 𝓝[s] x := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (extChartAt_source_mem_nhds (I := I) x)] with y hy h'y
    exact ⟨(extChartAt I x).map_source h'y,
      by simpa only [mem_preimage, (extChartAt I x).left_inv h'y] using hy⟩
  let U' (y : E) : TangentSpace 𝓘(𝕜, E) y := (chartRep E I x U) y
  let V' (y : E) : TangentSpace 𝓘(𝕜, E) y := (chartRep E I x V) y
  have A : ContDiffWithinAt 𝕜 m' (lieBracketWithin 𝕜 U' V'
      ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s))
      ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) (extChartAt I x x) :=
    ContDiffWithinAt.lieBracketWithin_vectorField
      (contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt.1
        (contMDiffWithinAt_mpullbackWithin_extChartAt_symm (inChart_chartRep x U) hU hs hx le_rfl))
      (contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt.1
        (contMDiffWithinAt_mpullbackWithin_extChartAt_symm (inChart_chartRep x V) hV hs hx le_rfl))
      (hs.uniqueDiffOn_target_inter x) hm'n (by simp [hx])
  have B : CMDiffAt[((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s)] m'
      (T% (mlieBracketWithin 𝓘(𝕜, E) U' V' ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s)))
      (extChartAt I x x) := by
    rw [← mlieBracketWithin_eq_lieBracketWithin] at A
    exact contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt.2 A
  apply ContMDiffWithinAt.mpullback_vectorField_of_mem_nhdsWithin_of_eq B (n := m' + 1)
    contMDiffAt_extChartAt (isInvertible_mfderiv_extChartAt (mem_extChartAt_source x))
    le_rfl pre_mem rfl
  rw [insert_eq_of_mem hx]
  filter_upwards [eventually_eventually_nhdsWithin.2 pre_mem, self_mem_nhdsWithin,
    extChartAt_source_mem_nhdsWithin (I := I) x,
    eventually_contMDiffWithinAt_mpullbackWithin_extChartAt_symm (inChart_chartRep x U)
      (hU.of_le hm'n) hs hx le_rfl (by simpa using h'm'),
    eventually_contMDiffWithinAt_mpullbackWithin_extChartAt_symm (inChart_chartRep x V)
      (hV.of_le hm'n) hs hx le_rfl (by simpa using h'm')] with
      y hyt hys hyc hyU hyV
  exact related_chart_bracket (hyU.mdifferentiableWithinAt (by positivity))
    (hyV.mdifferentiableWithinAt (by positivity)) hs hys hyc hyt
    ((inChart_chartRep x U).eventually_related hyc) ((inChart_chartRep x V).eventually_related hyc)

/-- If two vector fields are `C^n` with `n ≥ m + 1`, then their Lie bracket is `C^m`. -/
lemma _root_.ContMDiffAt.mlieBracket_vectorField {m n : ℕ∞}
    {U V : Π (x : M), TangentSpace I x} {x : M}
    (hU : CMDiffAt n (T% U) x) (hV : CMDiffAt n (T% V) x)
    (hmn : minSmoothness 𝕜 (m + 1) ≤ n) :
    CMDiffAt m (T% (mlieBracket I U V)) x := by
  simp only [← contMDiffWithinAt_univ, ← mlieBracketWithin_univ] at hU hV ⊢
  exact hU.mlieBracketWithin_vectorField hV uniqueMDiffOn_univ (mem_univ _) hmn

/-- If two vector fields are `C^n` with `n ≥ m + 1`, then their Lie bracket is `C^m`. -/
lemma _root_.ContMDiffOn.mlieBracketWithin_vectorField {m n : ℕ∞}
    {U V : Π (x : M), TangentSpace I x}
    (hU : CMDiff[s] n (T% U)) (hV : CMDiff[s] n (T% V))
    (hs : UniqueMDiff[s]) (hmn : minSmoothness 𝕜 (m + 1) ≤ n) :
    CMDiff[s] m (T% (mlieBracketWithin I U V s)) :=
  fun x hx ↦ (hU x hx).mlieBracketWithin_vectorField (hV x hx) hs hx hmn

/-- If two vector fields are `C^n` with `n ≥ m + 1`, then their Lie bracket is `C^m`. -/
lemma _root_.ContDiff.mlieBracket_vectorField {m n : ℕ∞}
    {U V : Π (x : M), TangentSpace I x}
    (hU : CMDiff n (T% U)) (hV : CMDiff n (T% V)) (hmn : minSmoothness 𝕜 (m + 1) ≤ n) :
    CMDiff m (T% (mlieBracket I U V)) := by
  simp only [← contMDiffOn_univ] at hU hV ⊢
  exact hU.mlieBracketWithin_vectorField hV uniqueMDiffOn_univ hmn

end Invariance

section Leibniz

variable [IsManifold I (minSmoothness 𝕜 3) M] [CompleteSpace E]

set_option backward.isDefEq.respectTransparency false in
/-- The Lie bracket of vector fields in manifolds satisfies the Leibniz identity
`[U, [V, W]] = [[U, V], W] + [V, [U, W]]` (also called Jacobi identity). -/
theorem leibniz_identity_mlieBracketWithin_apply
    {U V W : Π (x : M), TangentSpace I x} {s : Set M} {x : M}
    (hs : UniqueMDiff[s]) (h's : x ∈ closure (interior s)) (hx : x ∈ s)
    (hU : CMDiffAt[s] (minSmoothness 𝕜 2) (T% U) x)
    (hV : CMDiffAt[s] (minSmoothness 𝕜 2) (T% V) x)
    (hW : CMDiffAt[s] (minSmoothness 𝕜 2) (T% W) x) :
    mlieBracketWithin I U (mlieBracketWithin I V W s) s x =
      mlieBracketWithin I (mlieBracketWithin I U V s) W s x
      + mlieBracketWithin I V (mlieBracketWithin I U W s) s x := by
  have A : minSmoothness 𝕜 2 + 1 ≤ minSmoothness 𝕜 3 := by
    simp only [← minSmoothness_add]
    exact le_rfl
  have s_inter_mem : s ∩ (extChartAt I x).source ∈ 𝓝[s] x :=
    inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (extChartAt_source_mem_nhds x))
  have pre_mem : (extChartAt I x) ⁻¹' ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s)
      ∈ 𝓝[s] x := by
    filter_upwards [s_inter_mem] with y hy
    exact ⟨(extChartAt I x).map_source hy.2,
      by simpa only [mem_preimage, (extChartAt I x).left_inv hy.2] using hy.1⟩
  -- write everything as pullbacks of vector fields in `E` (denoted with primes), for which
  -- the identity can be checked via direct calculation.
  let U' (y : E) : TangentSpace 𝓘(𝕜, E) y := (chartRep E I x U) y
  let V' (y : E) : TangentSpace 𝓘(𝕜, E) y := (chartRep E I x V) y
  let W' (y : E) : TangentSpace 𝓘(𝕜, E) y := (chartRep E I x W) y
  -- register basic facts on the pullbacks in the vector space
  have J0U : CMDiffAt[(extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s] (minSmoothness 𝕜 2)
      (T% U') (extChartAt I x x) :=
    contMDiffWithinAt_mpullbackWithin_extChartAt_symm (inChart_chartRep x U) hU hs hx A
  have J0V : CMDiffAt[(extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s] (minSmoothness 𝕜 2)
      (T% V') (extChartAt I x x) :=
    contMDiffWithinAt_mpullbackWithin_extChartAt_symm (inChart_chartRep x V) hV hs hx A
  have J0W : CMDiffAt[(extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s] (minSmoothness 𝕜 2)
      (T% W') (extChartAt I x x) :=
    contMDiffWithinAt_mpullbackWithin_extChartAt_symm (inChart_chartRep x W) hW hs hx A
  have J1U : ∀ᶠ y in 𝓝[s] x, CMDiffAt[(extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s]
      (minSmoothness 𝕜 2) (T% U') (extChartAt I x y) :=
    eventually_contMDiffWithinAt_mpullbackWithin_extChartAt_symm (inChart_chartRep x U)
      hU hs hx A (by simp)
  have J1V : ∀ᶠ y in 𝓝[s] x, CMDiffAt[(extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s]
      (minSmoothness 𝕜 2) (T% V') (extChartAt I x y) :=
    eventually_contMDiffWithinAt_mpullbackWithin_extChartAt_symm (inChart_chartRep x V)
      hV hs hx A (by simp)
  have J1W : ∀ᶠ y in 𝓝[s] x, CMDiffAt[(extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s]
      (minSmoothness 𝕜 2) (T% W') (extChartAt I x y) :=
    eventually_contMDiffWithinAt_mpullbackWithin_extChartAt_symm (inChart_chartRep x W)
      hW hs hx A (by simp)
  let e := extChartAt I x
  let t := e.target ∩ e.symm ⁻¹' s
  have rel {A : Π y : M, TangentSpace I y} {P : E → E} (hp : InChart I x A P) :=
    hp.eventually_related (s := s) (mem_extChartAt_source x)
  have inner {A B : Π y : M, TangentSpace I y}
      {P Q : Π y : E, TangentSpace 𝓘(𝕜, E) y} (hp : InChart I x A P) (hq : InChart I x B Q)
      (hP : ∀ᶠ y in 𝓝[s] x, CMDiffAt[t] (minSmoothness 𝕜 2) (T% P) (e y))
      (hQ : ∀ᶠ y in 𝓝[s] x, CMDiffAt[t] (minSmoothness 𝕜 2) (T% Q) (e y)) :
      ∀ᶠ y in 𝓝[s] x, IsMRelatedWithinAt e (mlieBracketWithin I A B s)
        (mlieBracketWithin 𝓘(𝕜, E) P Q t) univ y := by
    filter_upwards [eventually_eventually_nhdsWithin.2 pre_mem, self_mem_nhdsWithin,
      extChartAt_source_mem_nhdsWithin (I := I) x, hP, hQ] with y hyt hys hyc hyP hyQ
    exact related_chart_bracket
      (hyP.mdifferentiableWithinAt (two_pos.trans_le le_minSmoothness).ne')
      (hyQ.mdifferentiableWithinAt (two_pos.trans_le le_minSmoothness).ne') hs hys hyc hyt
      (hp.eventually_related hyc) (hq.eventually_related hyc)
  have diff {P Q : Π y : E, TangentSpace 𝓘(𝕜, E) y}
      (hP : CMDiffAt[t] (minSmoothness 𝕜 2) (T% P) (e x))
      (hQ : CMDiffAt[t] (minSmoothness 𝕜 2) (T% Q) (e x)) :
      MDiffAt[t] (T% (mlieBracketWithin 𝓘(𝕜, E) P Q t)) (e x) :=
    (hP.mlieBracketWithin_vectorField hQ (m := 1) (hs.uniqueMDiffOn_target_inter x)
      ⟨mem_extChartAt_target x, by simp [e, hx]⟩ le_rfl).mdifferentiableWithinAt one_ne_zero
  have outer {A B : Π y : M, TangentSpace I y} {P Q : Π y : E, TangentSpace 𝓘(𝕜, E) y}
      (hP : MDiffAt[t] (T% P) (e x)) (hQ : MDiffAt[t] (T% Q) (e x))
      (hA : ∀ᶠ y in 𝓝[s] x, IsMRelatedWithinAt e A P univ y)
      (hB : ∀ᶠ y in 𝓝[s] x, IsMRelatedWithinAt e B Q univ y) :
      (mlieBracketWithin I A B s x : E) = mlieBracketWithin 𝓘(𝕜, E) P Q t (e x) := by
    have hbr := related_chart_bracket hP hQ hs hx (mem_extChartAt_source x) pre_mem hA hB
    have h := hbr.mfderivWithin_apply (uniqueMDiffWithinAt_univ I)
    simp only [mfderivWithin_univ, mfderiv_extChartAt_self] at h
    exact h
  have hn : minSmoothness 𝕜 2 ≠ 0 := (two_pos.trans_le le_minSmoothness).ne'
  have hU' := inChart_chartRep x U
  have hV' := inChart_chartRep x V
  have hW' := inChart_chartRep x W
  rw [outer (J0U.mdifferentiableWithinAt hn) (diff J0V J0W) (rel hU') (inner hV' hW' J1V J1W),
    outer (diff J0U J0V) (J0W.mdifferentiableWithinAt hn) (inner hU' hV' J1U J1V) (rel hW'),
    outer (J0V.mdifferentiableWithinAt hn) (diff J0U J0W) (rel hV') (inner hU' hW' J1U J1W)]
  simp_rw [mlieBracketWithin_eq_lieBracketWithin]
  apply leibniz_identity_lieBracketWithin (E := E) le_rfl
  · exact hs.uniqueDiffOn_target_inter x
  · dsimp only [t, e]
    rw [inter_comm]
    exact extChartAt_mem_closure_interior h's (mem_extChartAt_source x)
  · exact ⟨mem_extChartAt_target x, by simp [e, hx]⟩
  · exact contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt.mp J0U
  · exact contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt.mp J0V
  · exact contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt.mp J0W

/-- The Lie bracket of vector fields in manifolds satisfies the Leibniz identity
`[U, [V, W]] = [[U, V], W] + [V, [U, W]]` (also called Jacobi identity). -/
lemma leibniz_identity_mlieBracket_apply
    {U V W : Π (x : M), TangentSpace I x} {x : M}
    (hU : CMDiffAt (minSmoothness 𝕜 2) (T% U) x)
    (hV : CMDiffAt (minSmoothness 𝕜 2) (T% V) x)
    (hW : CMDiffAt (minSmoothness 𝕜 2) (T% W) x) :
    mlieBracket I U (mlieBracket I V W) x =
      mlieBracket I (mlieBracket I U V) W x + mlieBracket I V (mlieBracket I U W) x := by
  simp only [← mlieBracketWithin_univ, ← contMDiffWithinAt_univ] at hU hV hW ⊢
  exact leibniz_identity_mlieBracketWithin_apply uniqueMDiffOn_univ (by simp) (mem_univ _) hU hV hW

/-- The Lie bracket of vector fields in manifolds satisfies the Leibniz identity
`[U, [V, W]] = [[U, V], W] + [V, [U, W]]` (also called Jacobi identity). -/
lemma leibniz_identity_mlieBracket
    {U V W : Π (x : M), TangentSpace I x}
    (hU : CMDiff (minSmoothness 𝕜 2) (T% U))
    (hV : CMDiff (minSmoothness 𝕜 2) (T% V))
    (hW : CMDiff (minSmoothness 𝕜 2) (T% W)) :
    mlieBracket I U (mlieBracket I V W) =
      mlieBracket I (mlieBracket I U V) W + mlieBracket I V (mlieBracket I U W) := by
  ext x
  exact leibniz_identity_mlieBracket_apply (hU x) (hV x) (hW x)

end Leibniz

end LieBracket

end VectorField
