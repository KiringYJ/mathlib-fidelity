/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang, Samantha Naranjo Guevara
-/
module

public import Mathlib.Geometry.Manifold.LocalSourceTargetProperty
public import Mathlib.Analysis.Normed.Module.Shrink
public import Mathlib.Topology.Algebra.Module.TransferInstance
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.Notation

/-! # Smooth submersions

In this file, we define `C^n` submersions between `C^n` manifolds.
As in the case of immersions, the correct definition in the infinite-dimensional setting differs
from the classical finite-dimensional one (which is usually phrased in terms of surjectivity of the
`mfderiv`). Future work will prove that our definition implies the latter, and that both are
equivalent for finite-dimensional manifolds.

Our definition is formulated in terms of local normal forms; i.e., a map `f` is a submersion at `x`
if there exist charts near `x` and `f x` in which `f` looks like the standard projection
`(u, v) ↦ u`. The results in this file follow from abstract results about such local properties.

## Main definitions

* `IsSubmersionAtOfComplement F I J n f x` means a map `f : M → N` between `C^n` manifolds `M` and
  `N` is a submersion at `x : M`: there are charts `φ` and `ψ` of `M` and `N` around `x` and `f x`,
  respectively, such that in these charts, `f` looks like `(u, v) ↦ u`, w.r.t. some equivalence
  `E ≃L[𝕜] (E'' × F)`. Differentiability of `f` is not assumed as it follows from this definition.
* `IsSubmersionAt I J n f x` means that `f` is a `C^n` submersion at `x : M` for some choice of a
  complement `F` of the model normed space `E` of `M` in the model normed space `E''` of `N`.
* `IsSubmersionOfComplement F I J n f` means `f : M → N` is a submersion at every point `x : M`,
  w.r.t. the chosen complement `F`.
* `IsSubmersion I J n f` means `f : M → N` is a submersion at every point `x : M`,
  w.r.t. some global choice of complement.

## Main results

* `IsSubmersionAt.congr_of_eventuallyEq`: being a submersion is a local property.
  If `f` and `g` agree near `x` and `f` is a submersion at `x`, then so is `g`.
* `IsSubmersionAtOfComplement.congr_F`, `IsSubmersionOfComplement.congr_F`:
  being a submersion at `x` w.r.t. `F` is stable under
  replacing the complement `F` by an isomorphic copy.
* `isOpen_isSubmersionAtOfComplement` and `isOpen_isSubmersionAt`:
  the set of points where `IsSubmersionAt(OfComplement)` holds is open.
* `IsSubmersionAt.prodMap` and `IsSubmersion.prodMap`: the product of two submersions (at a point)
  is a submersion (at the product point).
* `IsSubmersionAt.contMDiffAt`: if `f` is a submersion at `x`, it is `C^n` at `x`.
* `IsSubmersion.contMDiff`: if `f` is a submersion, it is automatically `C^n`
  in the sense of `ContMDiff`.

## Implementation notes

The implementation strategy is identical to the one for immersions. See the implementation notes in
`Mathlib/Geometry/Manifold/Immersion` for details on:
* `IsSubmersionAt(OfComplement)`,
* universe level issues for complements,
* `small` and `smallEquiv` constructions.

## TODO
* The converse to `IsSubmersionAtOfComplement.congr_F` also holds: any two complements are
  isomorphic, as they are isomorphic to the kernel of the differential `mfderiv I J f x`.
* If `f` is a submersion at `x`, its differential `mfderiv I J f x` admits a continuous right
  inverse, in particular is surjective.
* If `f : M → N` is a map between Banach manifolds, `mfderiv I J f x` having a continuous right
  inverse implies `f` is a submersion at `x`. (This requires the inverse function theorem.)
* `IsSubmersionAt.comp`: if `f : M → N` and `g: N → N'` are maps between Banach manifolds such that
  `f` is a submersion at `x : M` and `g` is a submersion at `f x`, then `g ∘ f` is a submersion
  at `x`.
* `IsSubmersion.comp`: the composition of submersions is a submersion
* If `f : M → N` is a map between finite-dimensional manifolds, `mfderiv I J f x` being surjective
  implies `f` is a submersion at `x`.
* `IsLocalDiffeomorphAt.isSubmersionAt` and `IsLocalDiffeomorph.isSubmersion`:
  a local diffeomorphism (at `x`) is a submersion (at `x`)
* `Diffeomorph.isSubmersion`: in particular, a diffeomorphism is a submersion

## References

* [Alexander Schmeding, *An introduction to infinite-dimensional differential geometry*]
  [schmeding2023]
* Note that Margelef-Roig and Dominguez have a slightly different definition of submersions.

**Please talk** to Michael Rothgang before working on this file, to avoid duplicate work.
The above TODOs are the topic of Samantha Naranjo's master's thesis; it's nicer to coordinate.

-/

public noncomputable section

open scoped Topology ContDiff Manifold
open OpenPartialHomeomorph Function Set

namespace Manifold

universe u
-- We manually name the universe of `E` as `IsSubmersionAt` will use it.

variable {𝕜 E' E'' E''' F F' H H' G G' : Type*} {E : Type u} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [NormedAddCommGroup E'''] [NormedSpace 𝕜 E''']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace G] [TopologicalSpace G']
  {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'}
  {J : ModelWithCorners 𝕜 E'' G} {J' : ModelWithCorners 𝕜 E''' G'}

variable {M M' N N' : Type*}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace M'] [ChartedSpace H' M']
  [TopologicalSpace N] [ChartedSpace G N] [TopologicalSpace N'] [ChartedSpace G' N']
  {n : WithTop ℕ∞}

variable (F I J M N) in
/-- The local property of being a submersion at a point: `f : M → N` is a submersion at `x` if
there exist charts `φ` and `ψ` of `M` and `N` around `x` and `f x`, respectively, such that in these
charts, `f` looks like the projection `(u, v) ↦ u`.
This definition has a fixed parameter `F`, which is a choice of complement of `E''` in the model
normed space `E` of `M`: being a submersion at `x` includes a choice of linear isomorphism
between `E'' × F` and `E`. -/
def SubmersionAtProp :
    (M → N) → OpenPartialHomeomorph M H → OpenPartialHomeomorph N G → Prop :=
  fun f domChart codChart ↦ ∃ equiv : E ≃L[𝕜] (E'' × F),
    EqOn ((codChart.extend J) ∘ f ∘ (domChart.extend I).symm) (Prod.fst ∘ equiv)
      (domChart.extend I).target

omit [ChartedSpace H M] [ChartedSpace G N] in
/-- Being a submersion at `x` is a local property. -/
lemma isLocalSourceTargetProperty_submmersionAtProp :
    IsLocalSourceTargetProperty (SubmersionAtProp F I J M N) where
  mono_source {f φ ψ s} hs := fun ⟨equiv, hf⟩ ↦ ⟨equiv, hf.mono (by simp; grind)⟩
  congr {f g φ ψ} hfg := by
    intro ⟨equiv, hf⟩
    refine ⟨equiv, EqOn.trans (fun x hx ↦ ?_) (hf.mono (by simp))⟩
    have : ((φ.extend I).symm) x ∈ φ.source := by simp_all
    grind

variable (F I J n) in
/-- `f : M → N` is a `C^n` submersion at `x` if there are charts `φ` and `ψ` of `M` and `N`
around `x` and `f x`, respectively such that in these charts, `f` looks like `(u, v) ↦ u`.
Additionally, we demand that `f` map `φ.source` into `ψ.source`.

NB. We don't know the particular atlasses used for `M` and `N`, so asking for `φ` and `ψ` to be
in the `atlas` would be too optimistic: lying in the `maximalAtlas` is sufficient.

This definition has a fixed parameter `F`, which is a choice of complement of `E''` in `E`:
being an submersion at `x` includes a choice of linear isomorphism between `E'' × F` and `E`.
While the particular choice of complement is often not important, choosing a complement is useful
in some settings, such as proving that embedded submanifolds are locally given either by an
immersion or a submersion.
Unless you have a particular reason, prefer to use `IsSubmersionAt` instead.
-/
def IsSubmersionAtOfComplement (f : M → N) (x : M) : Prop :=
  LiftSourceTargetPropertyAt I J n f x (SubmersionAtProp F I J M N)

-- Lift the universe from `E`, to avoid a free universe parameter.

variable (I J n) in
/-- `f : M → N` is a `C^n` submersion at `x` if there are charts `φ` and `ψ` of `M` and `N`
around `x` and `f x`, respectively such that in these charts, `f` looks like `(u, v) ↦ u`.
Additionally, we demand that `f` map `φ.source` into `ψ.source`.

NB. We don't know the particular atlasses used for `M` and `N`, so asking for `φ` and `ψ` to be
in the `atlas` would be too optimistic: lying in the `maximalAtlas` is sufficient.

Implicit in this definition is an abstract choice `F` of a complement of `E''` in `E`: being
a submersion at `x` includes a choice of linear isomorphism between `E` and `E'' × F`, which is
where the choice of `F` enters.
If you need stronger control over the complement `F`, use `IsSubmersionAtOfComplement` instead.
-/
def IsSubmersionAt (f : M → N) (x : M) : Prop :=
  ∃ (F : Type u) (_ : NormedAddCommGroup F) (_ : NormedSpace 𝕜 F),
    IsSubmersionAtOfComplement F I J n f x

variable {f g : M → N} {x : M}

namespace IsSubmersionAtOfComplement

lemma mk_of_charts (equiv : E ≃L[𝕜] (E'' × F)) (domChart : OpenPartialHomeomorph M H)
    (codChart : OpenPartialHomeomorph N G)
    (hx : x ∈ domChart.source) (hfx : f x ∈ codChart.source)
    (hdomChart : domChart ∈ IsManifold.maximalAtlas I n M)
    (hcodChart : codChart ∈ IsManifold.maximalAtlas J n N)
    (hsource : domChart.source ⊆ f ⁻¹' codChart.source)
    (hwrittenInExtend : EqOn ((codChart.extend J) ∘ f ∘ (domChart.extend I).symm) (Prod.fst ∘ equiv)
      (domChart.extend I).target) : IsSubmersionAtOfComplement F I J n f x := by
  use domChart, codChart
  use equiv

/-- `f : M → N` is a `C^n` submersion at `x` if there are charts `φ` and `ψ` of `M` and `N`
around `x` and `f x`, respectively such that in these charts, `f` looks like `(u,v) ↦ u`.
This version does not assume that `f` maps `φ.source` to `ψ.source`,
but that `f` is continuous at `x`. -/
lemma mk_of_continuousAt {f : M → N} {x : M} (hf : ContinuousAt f x) (equiv : E ≃L[𝕜] (E'' × F))
    (domChart : OpenPartialHomeomorph M H) (codChart : OpenPartialHomeomorph N G)
    (hx : x ∈ domChart.source) (hfx : f x ∈ codChart.source)
    (hdomChart : domChart ∈ IsManifold.maximalAtlas I n M)
    (hcodChart : codChart ∈ IsManifold.maximalAtlas J n N)
    (hwrittenInExtend : EqOn ((codChart.extend J) ∘ f ∘ (domChart.extend I).symm) (Prod.fst ∘ equiv)
      (domChart.extend I).target) : IsSubmersionAtOfComplement F I J n f x :=
      LiftSourceTargetPropertyAt.mk_of_continuousAt hf
    isLocalSourceTargetProperty_submmersionAtProp
    _ _ hx hfx hdomChart hcodChart ⟨equiv, hwrittenInExtend⟩

lemma property (h : IsSubmersionAtOfComplement F I J n f x) :
    LiftSourceTargetPropertyAt I J n f x (SubmersionAtProp F I J M N) := h

omit [ChartedSpace H M] [ChartedSpace G N] in
/-- If `f` maps the source of a chart `φ` into the source of a chart `ψ` and reads as
`u ↦ (equiv u).1` in these charts, as for the charts of a submersion, then `Prod.fst ∘ equiv`
maps the target of `φ.extend I` into the target of `ψ.extend J`.

See `target_subset_preimage_target` for a version stated using preimages instead of images.
-/
lemma image_target_subset_target {φ : OpenPartialHomeomorph M H}
    {ψ : OpenPartialHomeomorph N G} {equiv : E ≃L[𝕜] (E'' × F)}
    (hsource : φ.source ⊆ f ⁻¹' ψ.source)
    (hwritten : EqOn ((ψ.extend J) ∘ f ∘ (φ.extend I).symm) (Prod.fst ∘ equiv)
      (φ.extend I).target) :
    (Prod.fst ∘ equiv) '' (φ.extend I).target ⊆ (ψ.extend J).target := by
  rw [← hwritten.image_eq, Set.image_comp, Set.image_comp,
    PartialEquiv.symm_image_target_eq_source, OpenPartialHomeomorph.extend_source,
    ← PartialEquiv.image_source_eq_target]
  have : f '' φ.source ⊆ ψ.source := by
    simp [hsource]
  grw [this, OpenPartialHomeomorph.extend_source]

omit [ChartedSpace H M] [ChartedSpace G N] in
/-- If `f` maps the source of a chart `φ` into the source of a chart `ψ` and reads as
`u ↦ (equiv u).1` in these charts, then the target of `φ.extend I` is mapped into the target of
`ψ.extend J`: see `image_target_subset_target` for a version stated using images. -/
lemma target_subset_preimage_target {φ : OpenPartialHomeomorph M H}
    {ψ : OpenPartialHomeomorph N G} {equiv : E ≃L[𝕜] (E'' × F)}
    (hsource : φ.source ⊆ f ⁻¹' ψ.source)
    (hwritten : EqOn ((ψ.extend J) ∘ f ∘ (φ.extend I).symm) (Prod.fst ∘ equiv)
      (φ.extend I).target) :
    (φ.extend I).target ⊆ (Prod.fst ∘ equiv) ⁻¹' (ψ.extend J).target :=
  fun _x hx ↦ image_target_subset_target hsource hwritten (mem_image_of_mem _ hx)

/-- If `f` is a submersion at `x` and `g = f` on some neighbourhood of `x`,
then `g` is a submersion at `x`. -/
lemma congr_of_eventuallyEq (hf : IsSubmersionAtOfComplement F I J n f x) (hfg : f =ᶠ[𝓝 x] g) :
    IsSubmersionAtOfComplement F I J n g x := by
  exact LiftSourceTargetPropertyAt.congr_of_eventuallyEq
    isLocalSourceTargetProperty_submmersionAtProp hf.property hfg

/-- If `f = g` on some neighbourhood of `x`,
then `f` is a submersion at `x` if and only if `g` is a submersion at `x`. -/
lemma congr_iff_of_eventuallyEq (hfg : f =ᶠ[𝓝 x] g) :
    IsSubmersionAtOfComplement F I J n f x ↔ IsSubmersionAtOfComplement F I J n g x :=
  LiftSourceTargetPropertyAt.congr_iff_of_eventuallyEq
    isLocalSourceTargetProperty_submmersionAtProp hfg

lemma small (hf : IsSubmersionAtOfComplement F I J n f x) : Small.{u} F := by
  obtain ⟨p⟩ := hf
  obtain ⟨equiv, -⟩ := p.property
  exact small_of_injective <| equiv.symm.injective.comp (Prod.mk_right_injective 0)

/-- Given a submersion `f` at `x`, this is a choice of complement which lives in the same universe
as the model space for the domain of `f`: this is useful to avoid universe restrictions. -/
def smallComplement (hf : IsSubmersionAtOfComplement F I J n f x) : Type u :=
  haveI := hf.small
  Shrink.{u} F

instance (hf : IsSubmersionAtOfComplement F I J n f x) : NormedAddCommGroup hf.smallComplement :=
  haveI := hf.small
  inferInstanceAs <| NormedAddCommGroup (Shrink F)

instance (hf : IsSubmersionAtOfComplement F I J n f x) : NormedSpace 𝕜 hf.smallComplement :=
  haveI := hf.small
  inferInstanceAs <| NormedSpace 𝕜 (Shrink F)

/-- Given a submersion `f` at `x` w.r.t. a complement `F`, this construction provides
a continuous linear equivalence from `F` to the small complement of `F`:
mathematically, this is just the identity map; however, this is technically useful as it enables
us to always work with `hf.smallComplement`. -/
def smallEquiv (hf : IsSubmersionAtOfComplement F I J n f x) : F ≃L[𝕜] hf.smallComplement :=
  haveI := hf.small
  ((Shrink.addEquiv (α := F)).continuousLinearEquiv 𝕜).symm

lemma trans_F (h : IsSubmersionAtOfComplement F I J n f x) (e : F ≃L[𝕜] F') :
    IsSubmersionAtOfComplement F' I J n f x := by
  obtain ⟨p⟩ := h
  obtain ⟨equiv, hwritten⟩ := p.property
  refine ⟨p.domChart, p.codChart, p.mem_domChart_source, p.mem_codChart_source,
    p.domChart_mem_maximalAtlas, p.codChart_mem_maximalAtlas, p.source_subset_preimage_source, ?_⟩
  use equiv.trans ((ContinuousLinearEquiv.refl 𝕜 E'').prodCongr e)
  apply Set.EqOn.trans hwritten
  intro x hx
  simp

/-- Being a submersion at `x` w.r.t. `F` is stable under replacing `F` by an isomorphic copy. -/
lemma congr_F (e : F ≃L[𝕜] F') :
    IsSubmersionAtOfComplement F I J n f x ↔ IsSubmersionAtOfComplement F' I J n f x :=
  ⟨fun h ↦ trans_F (e := e) h, fun h ↦ trans_F (e := e.symm) h⟩

/- The set of points where `IsSubmersionAtOfComplement` holds is open. -/
lemma _root_.isOpen_isSubmersionAtOfComplement :
    IsOpen {x | IsSubmersionAtOfComplement F I J n f x} := by
  exact IsOpen.liftSourceTargetPropertyAt

/-- If `f: M → N` and `g: M' → N'` are submersions at `x` and `x'`, respectively,
then `f × g: M × M' → N × N'` is a submersion at `(x, x')`. -/
theorem prodMap {f : M → N} {g : M' → N'} {x' : M'}
    [IsManifold I n M] [IsManifold I' n M'] [IsManifold J n N] [IsManifold J' n N']
    (hf : IsSubmersionAtOfComplement F I J n f x)
    (hg : IsSubmersionAtOfComplement F' I' J' n g x') :
    IsSubmersionAtOfComplement (F × F') (I.prod I') (J.prod J') n (Prod.map f g) (x, x') := by
  apply LiftSourceTargetPropertyAt.prodMap hf.property hg.property
  rintro f φ₁ ψ₁ g φ₂ ψ₂ ⟨equiv₁, hfprop⟩ ⟨equiv₂, hgprop⟩
  use (equiv₁.prodCongr equiv₂).trans (ContinuousLinearEquiv.prodProdProdComm 𝕜 E'' F E''' F')
  rw [φ₁.extend_prod φ₂, ψ₁.extend_prod, PartialEquiv.prod_target, eqOn_prod_iff]
  exact ⟨fun x ⟨hx, hx'⟩ ↦ by simpa using hfprop hx, fun x ⟨hx, hx'⟩ ↦ by simpa using hgprop hx'⟩

/-- If `f` is a submersion at `x` w.r.t. some complement `F`, it is a submersion at `x`.

Note that the proof contains a small formalisation-related subtlety: `F` can live in any universe,
while being a submersion at `x` requires the existence of a complement in the same universe as
the model normed space of `N`. This is solved by `smallComplement` and `smallEquiv`. -/
lemma isSubmersionAt (h : IsSubmersionAtOfComplement F I J n f x) :
    IsSubmersionAt I J n f x := by
  use h.smallComplement, by infer_instance, by infer_instance
  exact (IsSubmersionAtOfComplement.congr_F h.smallEquiv).mp h

/-- If `f` maps the source of a chart `φ` into the source of a chart `ψ` of the maximal atlases and
reads as `u ↦ (equiv u).1` in these charts, as for the charts of a submersion, then `f` is `C^n`
on the source of `φ`. -/
theorem contMDiffOn_of_eqOn {φ : OpenPartialHomeomorph M H} {ψ : OpenPartialHomeomorph N G}
    {equiv : E ≃L[𝕜] (E'' × F)} (hφ : φ ∈ IsManifold.maximalAtlas I n M)
    (hψ : ψ ∈ IsManifold.maximalAtlas J n N) (hsource : φ.source ⊆ f ⁻¹' ψ.source)
    (hwritten : EqOn ((ψ.extend J) ∘ f ∘ (φ.extend I).symm) (Prod.fst ∘ equiv)
      (φ.extend I).target) :
    ContMDiffOn I J n f φ.source := by
  rw [← contMDiffOn_writtenInExtend_iff hφ hψ le_rfl hsource,
    ← φ.extend_target_eq_image_source]
  have : CMDiff n (Prod.fst ∘ equiv) := by rw [contMDiff_iff_contDiff]; fun_prop
  exact this.contMDiffOn.congr hwritten

/-- A `C^n` submersion at `x` is `C^n` at `x`. -/
theorem contMDiffAt (h : IsSubmersionAtOfComplement F I J n f x) : CMDiffAt n f x := by
  obtain ⟨p⟩ := h
  obtain ⟨equiv, hwritten⟩ := p.property
  exact (contMDiffOn_of_eqOn p.domChart_mem_maximalAtlas p.codChart_mem_maximalAtlas
    p.source_subset_preimage_source hwritten).contMDiffAt
    (p.domChart.open_source.mem_nhds p.mem_domChart_source)

end IsSubmersionAtOfComplement

namespace IsSubmersionAt

lemma mk_of_charts (equiv : E ≃L[𝕜] (E'' × F))
    (domChart : OpenPartialHomeomorph M H) (codChart : OpenPartialHomeomorph N G)
    (hx : x ∈ domChart.source) (hfx : f x ∈ codChart.source)
    (hdomChart : domChart ∈ IsManifold.maximalAtlas I n M)
    (hcodChart : codChart ∈ IsManifold.maximalAtlas J n N)
    (hsource : domChart.source ⊆ f ⁻¹' codChart.source)
    (hwrittenInExtend : EqOn ((codChart.extend J) ∘ f ∘ (domChart.extend I).symm) (Prod.fst ∘ equiv)
      (domChart.extend I).target) : IsSubmersionAt I J n f x := by
  have aux : IsSubmersionAtOfComplement F I J n f x := by
    apply IsSubmersionAtOfComplement.mk_of_charts <;> assumption
  use aux.smallComplement, by infer_instance, by infer_instance
  rwa [← IsSubmersionAtOfComplement.congr_F aux.smallEquiv]

/-- `f : M → N` is a `C^n` submersion at `x` if there are charts `φ` and `ψ` of `M` and `N`
around `x` and `f x`, respectively such that in these charts, `f` looks like `(u, v) ↦ u`.
This version does not assume that `f` maps `φ.source` to `ψ.source`,
but that `f` is continuous at `x`. -/
lemma mk_of_continuousAt {f : M → N} {x : M} (hf : ContinuousAt f x) (equiv : E ≃L[𝕜] (E'' × F))
    (domChart : OpenPartialHomeomorph M H) (codChart : OpenPartialHomeomorph N G)
    (hx : x ∈ domChart.source) (hfx : f x ∈ codChart.source)
    (hdomChart : domChart ∈ IsManifold.maximalAtlas I n M)
    (hcodChart : codChart ∈ IsManifold.maximalAtlas J n N)
    (hwrittenInExtend : EqOn ((codChart.extend J) ∘ f ∘ (domChart.extend I).symm) (Prod.fst ∘ equiv)
      (domChart.extend I).target) : IsSubmersionAt I J n f x := by
  have aux : IsSubmersionAtOfComplement F I J n f x := by
    apply IsSubmersionAtOfComplement.mk_of_continuousAt <;> assumption
  use aux.smallComplement, by infer_instance, by infer_instance
  rwa [← IsSubmersionAtOfComplement.congr_F aux.smallEquiv]

/-- If `f` is a submersion at `x` and `g = f` on some neighbourhood of `x`,
then `g` is a submersion at `x`. -/
lemma congr_of_eventuallyEq (hf : IsSubmersionAt I J n f x) (hfg : f =ᶠ[𝓝 x] g) :
    IsSubmersionAt I J n g x := by
  obtain ⟨F, _, _, hf⟩ := hf
  exact ⟨F, _, _, hf.congr_of_eventuallyEq hfg⟩

/-- If `f = g` on some neighbourhood of `x`,
then `f` is a submersion at `x` if and only if `g` is a submersion at `x`. -/
lemma congr_iff (hfg : f =ᶠ[𝓝 x] g) :
    IsSubmersionAt I J n f x ↔ IsSubmersionAt I J n g x :=
  ⟨fun h ↦ h.congr_of_eventuallyEq hfg, fun h ↦ h.congr_of_eventuallyEq hfg.symm⟩

/- The set of points where `IsSubmersionAt` holds is open. -/
lemma _root_.isOpen_isSubmersionAt :
    IsOpen {x | IsSubmersionAt I J n f x} := by
  rw [isOpen_iff_forall_mem_open]
  rintro x ⟨F, _, _, hx⟩
  exact ⟨{x | IsSubmersionAtOfComplement F I J n f x }, fun y hy ↦ hy.isSubmersionAt,
    isOpen_isSubmersionAtOfComplement, hx⟩

/-- If `f: M → N` and `g: M' → N'` are submersions at `x` and `x'`, respectively,
then `f × g: M × M' → N × N'` is a submersion at `(x, x')`. -/
theorem prodMap {f : M → N} {g : M' → N'} {x' : M'}
    [IsManifold I n M] [IsManifold I' n M'] [IsManifold J n N] [IsManifold J' n N']
    (hf : IsSubmersionAt I J n f x) (hg : IsSubmersionAt I' J' n g x') :
    IsSubmersionAt (I.prod I') (J.prod J') n (Prod.map f g) (x, x') := by
  obtain ⟨F, _, _, hf⟩ := hf
  obtain ⟨F', _, _, hg⟩ := hg
  exact (hf.prodMap hg).isSubmersionAt

/-- A `C^n` submersion at `x` is `C^n` at `x`. -/
theorem contMDiffAt (h : IsSubmersionAt I J n f x) : CMDiffAt n f x := by
  obtain ⟨F, _, _, h⟩ := h
  exact h.contMDiffAt

end IsSubmersionAt

variable (F I J n) in
/-- `f : M → N` is a `C^n` submersion if around each point `x ∈ M`,
there are charts `φ` and `ψ` of `M` and `N` around `x` and `f x`, respectively
such that in these charts, `f` looks like `(u, v) ↦ u`.

In other words, `f` is a submersion at each `x ∈ M`.

This definition has a fixed parameter `F`, which is a choice of complement of `E` in `E'`:
being a submersion at `x` includes a choice of linear isomorphism between `E` and `E'' × F`. -/
def IsSubmersionOfComplement (f : M → N) : Prop := ∀ x, IsSubmersionAtOfComplement F I J n f x

variable (I J n) in
/-- `f : M → N` is a `C^n` submersion if around each point `x ∈ M`,
there are charts `φ` and `ψ` of `M` and `N` around `x` and `f x`, respectively
such that in these charts, `f` looks like `(u, v) ↦ u`.

Implicit in this definition is an abstract choice `F` of a complement of `E` in `E'`:
being a submersion includes a choice of linear isomorphism between `E` and `E'' × F`, which is where
the choice of `F` enters. If you need stronger control over the complement `F`,
use `IsSubmersionOfComplement` instead.

Note that our global choice of complement is a bit stronger than asking `f` to be a submersion at
each `x ∈ M` w.r.t. to potentially varying complements: see `isSubmersionAt` for details.
-/
def IsSubmersion (f : M → N) : Prop :=
  ∃ (F : Type u) (_ : NormedAddCommGroup F) (_ : NormedSpace 𝕜 F),
    IsSubmersionOfComplement F I J n f

namespace IsSubmersionOfComplement

variable {f g : M → N}

/-- If `f` is a submersion, it is a submersion at each point. -/
lemma isSubmersionAt (h : IsSubmersionOfComplement F I J n f) (x : M) :
    IsSubmersionAtOfComplement F I J n f x := h x

lemma trans_F (h : IsSubmersionOfComplement F I J n f) (e : F ≃L[𝕜] F') :
    IsSubmersionOfComplement F' I J n f :=
  fun x ↦ (h x).trans_F e

/-- Being a submersion w.r.t. `F` is stable under replacing `F` by an isomorphic copy. -/
lemma congr_F (e : F ≃L[𝕜] F') :
    IsSubmersionOfComplement F I J n f ↔ IsSubmersionOfComplement F' I J n f :=
  ⟨fun h ↦ trans_F (e := e) h, fun h ↦ trans_F (e := e.symm) h⟩

/-- If `f: M → N` and `g: M' → N'` are submersions at `x` and `x'` (w.r.t. `F` and `F'`),
respectively, then `f × g: M × M' → N × N'` is a submersion at `(x, x')` w.r.t. `F × F'`. -/
theorem prodMap {f : M → N} {g : M' → N'}
    [IsManifold I n M] [IsManifold I' n M'] [IsManifold J n N] [IsManifold J' n N']
    (h : IsSubmersionOfComplement F I J n f) (h' : IsSubmersionOfComplement F' I' J' n g) :
    IsSubmersionOfComplement (F × F') (I.prod I') (J.prod J') n (Prod.map f g) :=
  fun ⟨x, x'⟩ ↦ (h x).prodMap (h' x')

/-- If `f` is a submersion w.r.t. some complement `F`, it is a submersion.

Note that the proof contains a small formalisation-related subtlety: `F` can live in any universe,
while being a submersion requires the existence of a complement in the same universe as
the model normed space of `N`. This is solved by `smallComplement` and `smallEquiv`.
-/
lemma isSubmersion (h : IsSubmersionOfComplement F I J n f) : IsSubmersion I J n f := by
  by_cases! hM : IsEmpty M
  · rw [IsSubmersion]
    use PUnit, by infer_instance, by infer_instance
    exact fun x ↦ (IsEmpty.false x).elim
  inhabit M
  let x : M := Inhabited.default
  use (h x).smallComplement, by infer_instance, by infer_instance
  exact (IsSubmersionOfComplement.congr_F (h x).smallEquiv).mp h

open IsManifold in
/-- The identity map is a submersion with complement `PUnit`. -/
protected lemma id [IsManifold I n M] : IsSubmersionOfComplement PUnit I I n (@id M) := by
  intro x
  apply IsSubmersionAtOfComplement.mk_of_continuousAt (continuousAt_id)
    (ContinuousLinearEquiv.prodUnique 𝕜 E PUnit).symm
    (chartAt H x) (chartAt H x) (mem_chart_source H x) (mem_chart_source H x)
    (chart_mem_maximalAtlas x) (chart_mem_maximalAtlas x)
  intro y hy
  have : I ((chartAt H x) ((chartAt H x).symm (I.symm y))) = y := by
    rw [(chartAt H x).right_inv (by simp_all), I.right_inv (by simp_all)]
  simpa

/-- A `C^n` submersion is `C^n` -/
theorem contMDiff (h : IsSubmersionOfComplement F I J n f) : CMDiff n f :=
  fun x ↦ (h x).contMDiffAt

end IsSubmersionOfComplement

namespace IsSubmersion

variable {f g : M → N}

/-- If `f` is a submersion, it is a submersion at each point. -/
lemma isSubmersionAt (h : IsSubmersion I J n f) (x : M) : IsSubmersionAt I J n f x := by
  obtain ⟨F, _, _, h⟩ := h
  exact ⟨F, _, _, h x⟩

/-- If `f: M → N` and `g: M' → N'` are submersions at `x` and `x'`, respectively,
then `f × g: M × M' → N × N'` is a submersion at `(x, x')`. -/
theorem prodMap {f : M → N} {g : M' → N'}
    [IsManifold I n M] [IsManifold I' n M'] [IsManifold J n N] [IsManifold J' n N']
    (hf : IsSubmersion I J n f) (hg : IsSubmersion I' J' n g) :
    IsSubmersion (I.prod I') (J.prod J') n (Prod.map f g) := by
  obtain ⟨F, _, _, hf⟩ := hf
  obtain ⟨F', _, _, hg⟩ := hg
  exact (hf.prodMap hg).isSubmersion

/-- The identity map is an submersion. -/
protected lemma id [IsManifold I n M] : IsSubmersion I I n (@id M) := by
  use PUnit, by infer_instance, by infer_instance
  exact IsSubmersionOfComplement.id

/-- A `C^n` submersion is `C^n` -/
theorem contMDiff (h : IsSubmersion I J n f) : CMDiff n f :=
  fun x ↦ (h.isSubmersionAt x).contMDiffAt

end IsSubmersion

end Manifold
