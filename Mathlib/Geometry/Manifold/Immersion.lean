/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.ImmersionDiff
public import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
public import Mathlib.Geometry.Manifold.LocalSourceTargetProperty
public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Geometry.Manifold.Notation
public import Mathlib.Analysis.Normed.Module.Shrink  -- shake: keep (NormedAddCommGroup (Shrink ...)), cf. lean#13417
public import Mathlib.Topology.Algebra.Module.TransferInstance

/-! # Smooth immersions

In this file, we define `C^n` immersions between `C^n` manifolds.
The correct definition in the infinite-dimensional setting differs from the standard
finite-dimensional definition (concerning the `mfderiv` being injective): future pull requests will
prove that our definition implies the latter, and that both are equivalent for finite-dimensional
manifolds.

This definition can be conveniently formulated in terms of local properties: `f` is an immersion at
`x` iff there exist suitable charts near `x` and `f x` such that `f` has a nice form w.r.t. these
charts. Most results below can be deduced from more abstract results about such local properties.
This shortens the overall argument, as the definition of submersions has the same general form.

## Main definitions

* `IsImmersionAtOfComplement F I J n f x` means a map `f : M → N` between `C^n` manifolds `M` and
  `N` is an immersion at `x : M`: there are charts `φ` and `ψ` of `M` and `N` around `x` and `f x`,
  respectively, such that in these charts, `f` looks like `u ↦ (u, 0)`, w.r.t. some equivalence
  `E' ≃L[𝕜] E × F`. We do not demand that `f` be differentiable (this follows from this definition).
* `IsImmersionAt I J n f x` means that `f` is a `C^n` immersion at `x : M` for some choice of a
  complement `F` of the model normed space `E` of `M` in the model normed space `E'` of `N`.
  In most cases, prefer this definition over `IsImmersionAtOfComplement`.
* `IsImmersionOfComplement F I J n f` means `f : M → N` is an immersion at every point `x : M`,
  w.r.t. the chosen complement `F`.
* `IsImmersion I J n f` means `f : M → N` is an immersion at every point `x : M`,
  w.r.t. some global choice of complement.

## Main results

* `IsImmersionAt.congr_of_eventuallyEq`: being an immersion is a local property.
  If `f` and `g` agree near `x` and `f` is an immersion at `x`, so is `g`
* `IsImmersionAtOfComplement.congr_F`, `IsImmersionOfComplement.congr_F`:
  being an immersion (at `x`) w.r.t. `F` is stable under
  replacing the complement `F` by an isomorphic copy.
* `IsOpen.isImmersionAtOfComplement` and `IsOpen.isImmersionAt`:
  the set of points where `IsImmersionAt(OfComplement)` holds is open.
* `IsImmersionAt.prodMap` and `IsImmersion.prodMap`: the product of two immersions (at a point)
  is an immersion (at the product point).
* `IsImmersion.id`: the identity map is an immersion
* `IsImmersion.of_opens`: the inclusion of an open subset `s → M` of a smooth manifold
  is a smooth immersion
* `ModelWithCorners.isImmersion`: every model with corners is itself an immersion
* `IsImmersionOfComplement.sumInl` and `IsImmersionOfComplement.sumInr`: given `C^n` manifolds
  `M` and `N`, `Sum.inl : M → M ⊕ N` and `Sum.inr : N → M ⊕ N` are `C^n` immersions
* `IsImmersionAt.contMDiffAt`: if f is an immersion at `x`, it is `C^n` at `x`.
* `IsImmersion.contMDiff`: if f is a `C^n` immersion, it is automatically `C^n`
  in the sense of `ContMDiff`.
* `ContMDiffAt.iff_comp_isImmersionAt` and `ContMDiff.iff_comp_isImmersion`: a function `f : M → N`
  is `C^n` (at `x`) if and only if it is continuous (at `x`) and its composition `φ ∘ f` with a
  `C^n` immersion `φ : N → P` (at `f x`) is `C^n`.
* `IsImmersionAt.isDiffImmersionAt`: if `f` is an immersion at `x`, it is also an immersion in the
  sense of differentials at `x`, i.e. `mfderiv% f x` has a continuous left inverse
* `IsImmersionAt.injective_mfderiv`: if `f` is an immersion at `x`, the differential `mfderiv% f x`
  at `x` is injective
* `IsImmersion.isDiffImmersionAt` and `IsImmersion.injective_mfderiv`: if `f` is an immersion,
  it is an immersion (in the sense of differentials) at every point of the domain.
  In particular, the differential at each point is injective.

## Implementation notes

* In most applications, there is no need to control the choice of complement in the definition of an
  immersion, so `IsImmersion(At)` is perfectly adequate. Such control will be helpful, however,
  when considering the local characterisation of submanifolds: locally, a submanifold is described
  either as the image of an immersion, or the preimage of a submersion --- w.r.t. the same
  complement. Providing a version of the definition that includes complements enables stating this
  equivalence cleanly.
* To avoid a free universe variable in `IsImmersion(At)`, we ask for a complement in the same
  universe as the model normed space for `N`. We provide convenience constructors which do not
  have this restriction to preserve usability.
  This relies on the observation that the equivalence in the definition of immersions allows
  shrinking the universe of the complement: this is implemented in
  `IsImmersion(At)OfComplement.small` and `IsImmersion(At)OfComplement.smallEquiv`.

## TODO
* The converse to `IsImmersionAtOfComplement.congr_F` also holds: any two complements are
  isomorphic, as they are isomorphic to the cokernel of the differential `mfderiv I J f x`.
* If `f` is an immersion at `x`, its differential splits, hence is injective.
* If `f : M → N` is a map between Banach manifolds, `mfderiv I J f x` splitting implies `f` is an
  immersion at `x`. (This requires the inverse function theorem.)
* `IsImmersionAt.comp`: if `f : M → N` and `g: N → N'` are maps between Banach manifolds such that
  `f` is an immersion at `x : M` and `g` is an immersion at `f x`, then `g ∘ f` is an immersion
  at `x`.
* `IsImmersion.comp`: the composition of immersions (between Banach manifolds) is an immersion
* If `f : M → N` is a map between finite-dimensional manifolds, `mfderiv I J f x` being injective
  implies `f` is an immersion at `x`.
* `IsLocalDiffeomorphAt.isImmersionAt` and `IsLocalDiffeomorph.isImmersion`:
  a local diffeomorphism (at `x`) is an immersion (at `x`)
* `Diffeomorph.isImmersion`: in particular, a diffeomorphism is an immersion

## References

* [Juan Margalef-Roig and Enrique Outerelo Dominguez, *Differential topology*][roigdomingues1992]

-/

open scoped Topology ContDiff
open Function Set

public noncomputable section

namespace Manifold

-- We manually name the universe of `E''` as `IsImmersionAt` will use it.
universe u
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E E' E''' : Type*} {E'' : Type u} {F F' : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [NormedAddCommGroup E'''] [NormedSpace 𝕜 E''']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  {G : Type*} [TopologicalSpace G] {G' : Type*} [TopologicalSpace G']
  {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'}
  {J : ModelWithCorners 𝕜 E'' G} {J' : ModelWithCorners 𝕜 E''' G'}

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {N' : Type*} [TopologicalSpace N'] [ChartedSpace G' N']
  {n : ℕ∞ω}

variable (F I J M N) in
/-- The local property of being an immersion at a point: `f : M → N` is an immersion at `x` if
there exist charts `φ` and `ψ` of `M` and `N` around `x` and `f x`, respectively, such that in these
charts, `f` looks like the inclusion `u ↦ (u, 0)`.

This definition has a fixed parameter `F`, which is a choice of complement of `E` in the model
normed space `E'` of `N`: being an immersion at `x` includes a choice of linear isomorphism
between `E × F` and `E'`. -/
def ImmersionAtProp : (M → N) → OpenPartialHomeomorph M H → OpenPartialHomeomorph N G → Prop :=
  fun f domChart codChart ↦ ∃ equiv : (E × F) ≃L[𝕜] E'',
    EqOn ((codChart.extend J) ∘ f ∘ (domChart.extend I).symm) (equiv ∘ (·, 0))
      (domChart.extend I).target

omit [ChartedSpace H M] [ChartedSpace G N] in
/-- Being an immersion at `x` is a local property. -/
lemma isLocalSourceTargetProperty_immersionAtProp :
    IsLocalSourceTargetProperty (ImmersionAtProp F I J M N) where
  mono_source {f φ ψ s} hs := fun ⟨equiv, hf⟩ ↦ ⟨equiv, hf.mono (by simp; grind)⟩
  congr {f g φ ψ} hfg := by
    intro ⟨equiv, hf⟩
    refine ⟨equiv, EqOn.trans (fun x hx ↦ ?_) (hf.mono (by simp))⟩
    have : ((φ.extend I).symm) x ∈ φ.source := by simp_all
    grind

variable (F I J n) in
/-- `f : M → N` is a `C^n` immersion at `x` if there are charts `φ` and `ψ` of `M` and `N`
around `x` and `f x`, respectively such that in these charts, `f` looks like `u ↦ (u, 0)`.
Additionally, we demand that `f` map `φ.source` into `ψ.source`.

NB. We don't know the particular atlases used for `M` and `N`, so asking for `φ` and `ψ` to be
in the `atlas` would be too optimistic: lying in the `maximalAtlas` is sufficient.

This definition has a fixed parameter `F`, which is a choice of complement of `E` in `E'`:
being an immersion at `x` includes a choice of linear isomorphism between `E × F` and `E'`.
While the particular choice of complement is often not important, choosing a complement is useful
in some settings, such as proving that embedded submanifolds are locally given either by an
immersion or a submersion.
Unless you have a particular reason, prefer to use `IsImmersionAt` instead.
-/
def IsImmersionAtOfComplement (f : M → N) (x : M) : Prop :=
  LiftSourceTargetPropertyAt I J n f x (ImmersionAtProp F I J M N)

-- Lift the universe from `E''`, to avoid a free universe parameter.
variable (I J n) in
/-- `f : M → N` is a `C^n` immersion at `x` if there are charts `φ` and `ψ` of `M` and `N`
around `x` and `f x`, respectively such that in these charts, `f` looks like `u ↦ (u, 0)`.
Additionally, we demand that `f` map `φ.source` into `ψ.source`.

NB. We don't know the particular atlases used for `M` and `N`, so asking for `φ` and `ψ` to be
in the `atlas` would be too optimistic: lying in the `maximalAtlas` is sufficient.

Implicit in this definition is an abstract choice `F` of a complement of `E` in `E'`: being an
immersion at `x` includes a choice of linear isomorphism between `E × F` and `E'`, which is
where the choice of `F` enters.
If you need stronger control over the complement `F`, use `IsImmersionAtOfComplement` instead.
-/
def IsImmersionAt (f : M → N) (x : M) : Prop :=
  ∃ (F : Type u) (_ : NormedAddCommGroup F) (_ : NormedSpace 𝕜 F),
    IsImmersionAtOfComplement F I J n f x

variable {f g : M → N} {x : M}

namespace IsImmersionAtOfComplement

lemma mk_of_charts (equiv : (E × F) ≃L[𝕜] E'') (domChart : OpenPartialHomeomorph M H)
    (codChart : OpenPartialHomeomorph N G)
    (hx : x ∈ domChart.source) (hfx : f x ∈ codChart.source)
    (hdomChart : domChart ∈ IsManifold.maximalAtlas I n M)
    (hcodChart : codChart ∈ IsManifold.maximalAtlas J n N)
    (hsource : domChart.source ⊆ f ⁻¹' codChart.source)
    (hwrittenInExtend : EqOn ((codChart.extend J) ∘ f ∘ (domChart.extend I).symm) (equiv ∘ (·, 0))
      (domChart.extend I).target) : IsImmersionAtOfComplement F I J n f x := by
  use domChart, codChart
  use equiv

/-- `f : M → N` is a `C^n` immersion at `x` if there are charts `φ` and `ψ` of `M` and `N`
around `x` and `f x`, respectively such that in these charts, `f` looks like `u ↦ (u, 0)`.
This version does not assume that `f` maps `φ.source` to `ψ.source`,
but that `f` is continuous at `x`. -/
lemma mk_of_continuousAt {f : M → N} {x : M} (hf : ContinuousAt f x) (equiv : (E × F) ≃L[𝕜] E'')
    (domChart : OpenPartialHomeomorph M H) (codChart : OpenPartialHomeomorph N G)
    (hx : x ∈ domChart.source) (hfx : f x ∈ codChart.source)
    (hdomChart : domChart ∈ IsManifold.maximalAtlas I n M)
    (hcodChart : codChart ∈ IsManifold.maximalAtlas J n N)
    (hwrittenInExtend : EqOn ((codChart.extend J) ∘ f ∘ (domChart.extend I).symm) (equiv ∘ (·, 0))
      (domChart.extend I).target) : IsImmersionAtOfComplement F I J n f x :=
  LiftSourceTargetPropertyAt.mk_of_continuousAt hf isLocalSourceTargetProperty_immersionAtProp
    _ _ hx hfx hdomChart hcodChart ⟨equiv, hwrittenInExtend⟩

/-- `f : M → N` is a `C^n` immersion at `x` if `f` is continuous at `x` and `f` looks like
`u ↦ (u, 0)` in the preferred charts at `x` and `f x`.
Version of `mk_of_continuousAt` specialized to the preferred charts at each point. -/
lemma mk_of_continuousAt_of_extChartAt [IsManifold I n M] [IsManifold J n N]
    {f : M → N} {x : M} (hf : ContinuousAt f x) (equiv : (E × F) ≃L[𝕜] E'')
    (hwrittenInExtend : EqOn ((extChartAt J (f x)) ∘ f ∘ (extChartAt I x).symm) (equiv ∘ (·, 0))
      (extChartAt I x).target) : IsImmersionAtOfComplement F I J n f x :=
  mk_of_continuousAt hf equiv (chartAt H x) (chartAt G (f x))
    (mem_chart_source H x) (mem_chart_source G (f x))
    (IsManifold.chart_mem_maximalAtlas x) (IsManifold.chart_mem_maximalAtlas (f x)) hwrittenInExtend

lemma property (h : IsImmersionAtOfComplement F I J n f x) :
    LiftSourceTargetPropertyAt I J n f x (ImmersionAtProp F I J M N) := h

omit [ChartedSpace H M] [ChartedSpace G N] in
/--
If `f` maps the source of a chart `φ` into the source of a chart `ψ` and reads as
`u ↦ equiv (u, 0)` in these charts, as for the charts of an immersion, then `equiv ∘ (·, 0)` maps
the target of `φ.extend I` into the target of `ψ.extend J`.

Roig and Domingues' [roigdomingues1992] definition of immersions only asks for this inclusion
between the targets of the local charts: using mathlib's formalisation conventions, that condition
is *slightly* weaker than `hsource`: the latter implies that `ψ.extend J ∘ f` maps `φ.source` to
`(ψ.extend J).target = (ψ.extend J) '' ψ.source`, but that does *not* imply `f` maps `φ.source`
to `ψ.source`; a priori `f` could map some point `f ∘ φ.extend I x ∉ ψ.source` into the target.
Note that this difference only occurs because of our design using junk values;
this is not a mathematically meaningful difference.

At the same time, this condition is fairly weak: it is implied, for instance, by `f` being
continuous at `x` (see `mk_of_continuousAt`), which is easy to ascertain in practice.

See `target_subset_preimage_target` for a version stated using preimages instead of images.
-/
lemma map_target_subset_target {φ : OpenPartialHomeomorph M H} {ψ : OpenPartialHomeomorph N G}
    {equiv : (E × F) ≃L[𝕜] E''} (hsource : φ.source ⊆ f ⁻¹' ψ.source)
    (hwritten : EqOn ((ψ.extend J) ∘ f ∘ (φ.extend I).symm) (equiv ∘ (·, 0)) (φ.extend I).target) :
    (equiv ∘ (·, 0)) '' (φ.extend I).target ⊆ (ψ.extend J).target := by
  rw [← hwritten.image_eq, Set.image_comp, Set.image_comp,
    PartialEquiv.symm_image_target_eq_source, OpenPartialHomeomorph.extend_source,
    ← PartialEquiv.image_source_eq_target]
  have : f '' φ.source ⊆ ψ.source := by
    simp [hsource]
  grw [this, OpenPartialHomeomorph.extend_source]

omit [ChartedSpace H M] [ChartedSpace G N] in
/-- If `f` maps the source of a chart `φ` into the source of a chart `ψ` and reads as
`u ↦ equiv (u, 0)` in these charts, then the target of `φ.extend I` is mapped into the target of
`ψ.extend J`: see `map_target_subset_target` for a version stated using images. -/
lemma target_subset_preimage_target {φ : OpenPartialHomeomorph M H}
    {ψ : OpenPartialHomeomorph N G} {equiv : (E × F) ≃L[𝕜] E''}
    (hsource : φ.source ⊆ f ⁻¹' ψ.source)
    (hwritten : EqOn ((ψ.extend J) ∘ f ∘ (φ.extend I).symm) (equiv ∘ (·, 0)) (φ.extend I).target) :
    (φ.extend I).target ⊆ (equiv ∘ (·, 0)) ⁻¹' (ψ.extend J).target :=
  fun _x hx ↦ map_target_subset_target hsource hwritten (mem_image_of_mem _ hx)

/-- If `f` is an immersion at `x` and `g = f` on some neighbourhood of `x`,
then `g` is an immersion at `x`. -/
lemma congr_of_eventuallyEq (hf : IsImmersionAtOfComplement F I J n f x) (hfg : f =ᶠ[𝓝 x] g) :
    IsImmersionAtOfComplement F I J n g x :=
  LiftSourceTargetPropertyAt.congr_of_eventuallyEq
    isLocalSourceTargetProperty_immersionAtProp hf.property hfg

/-- If `f = g` on some neighbourhood of `x`,
then `f` is an immersion at `x` if and only if `g` is an immersion at `x`. -/
lemma congr_iff_of_eventuallyEq (hfg : f =ᶠ[𝓝 x] g) :
    IsImmersionAtOfComplement F I J n f x ↔ IsImmersionAtOfComplement F I J n g x :=
  LiftSourceTargetPropertyAt.congr_iff_of_eventuallyEq
      isLocalSourceTargetProperty_immersionAtProp hfg

lemma small (hf : IsImmersionAtOfComplement F I J n f x) : Small.{u} F := by
  obtain ⟨p⟩ := hf
  obtain ⟨equiv, -⟩ := p.property
  exact small_of_injective <| equiv.injective.comp (Prod.mk_right_injective 0)

/-- Given an immersion `f` at `x`, this is a choice of complement which lives in the same universe
as the model space for the co-domain of `f`: this is useful to avoid universe restrictions. -/
def smallComplement (hf : IsImmersionAtOfComplement F I J n f x) : Type u :=
  haveI := hf.small
  Shrink.{u} F

instance (hf : IsImmersionAtOfComplement F I J n f x) : NormedAddCommGroup hf.smallComplement :=
  haveI := hf.small
  inferInstanceAs <| NormedAddCommGroup (Shrink F)

instance (hf : IsImmersionAtOfComplement F I J n f x) : NormedSpace 𝕜 hf.smallComplement :=
  haveI := hf.small
  inferInstanceAs <| NormedSpace 𝕜 (Shrink F)

/-- Given an immersion `f` at `x` w.r.t. a complement `F`, this construction provides
a continuous linear equivalence from `F` to the small complement of `F`:
mathematically, this is just the identity map; however, this is technically useful as it enables
us to always work with `hf.smallComplement`. -/
def smallEquiv (hf : IsImmersionAtOfComplement F I J n f x) : F ≃L[𝕜] hf.smallComplement :=
  haveI := hf.small
  ((Shrink.addEquiv (α := F)).continuousLinearEquiv 𝕜).symm

lemma trans_F (h : IsImmersionAtOfComplement F I J n f x) (e : F ≃L[𝕜] F') :
    IsImmersionAtOfComplement F' I J n f x := by
  obtain ⟨p⟩ := h
  obtain ⟨equiv, hwritten⟩ := p.property
  refine ⟨p.domChart, p.codChart, p.mem_domChart_source, p.mem_codChart_source,
    p.domChart_mem_maximalAtlas, p.codChart_mem_maximalAtlas, p.source_subset_preimage_source, ?_⟩
  use ((ContinuousLinearEquiv.refl 𝕜 E).prodCongr e.symm).trans equiv
  apply Set.EqOn.trans hwritten
  intro x hx
  simp

/-- Being an immersion at `x` w.r.t. `F` is stable under replacing `F` by an isomorphic copy. -/
lemma congr_F (e : F ≃L[𝕜] F') :
    IsImmersionAtOfComplement F I J n f x ↔ IsImmersionAtOfComplement F' I J n f x :=
  ⟨fun h ↦ trans_F (e := e) h, fun h ↦ trans_F (e := e.symm) h⟩

/- The set of points where `IsImmersionAtOfComplement` holds is open. -/
lemma _root_.IsOpen.isImmersionAtOfComplement :
    IsOpen {x | IsImmersionAtOfComplement F I J n f x} :=
  IsOpen.liftSourceTargetPropertyAt

/-- If `f: M → N` and `g: M' × N'` are immersions at `x` and `x'`, respectively,
then `f × g: M × N → M' × N'` is an immersion at `(x, x')`. -/
theorem prodMap {f : M → N} {g : M' → N'} {x' : M'}
    [IsManifold I n M] [IsManifold I' n M'] [IsManifold J n N] [IsManifold J' n N']
    (hf : IsImmersionAtOfComplement F I J n f x) (hg : IsImmersionAtOfComplement F' I' J' n g x') :
    IsImmersionAtOfComplement (F × F') (I.prod I') (J.prod J') n (Prod.map f g) (x, x') := by
  apply LiftSourceTargetPropertyAt.prodMap hf.property hg.property
  rintro f φ₁ ψ₁ g φ₂ ψ₂ ⟨equiv₁, hfprop⟩ ⟨equiv₂, hgprop⟩
  use (ContinuousLinearEquiv.prodProdProdComm 𝕜 E E' F F').trans (equiv₁.prodCongr equiv₂)
  rw [φ₁.extend_prod φ₂, ψ₁.extend_prod, PartialEquiv.prod_target, eqOn_prod_iff]
  exact ⟨fun x ⟨hx, hx'⟩ ↦ by simpa using hfprop hx, fun x ⟨hx, hx'⟩ ↦ by simpa using hgprop hx'⟩

/-- If `f` is an immersion at `x` w.r.t. some complement `F`, it is an immersion at `x`.

Note that the proof contains a small formalisation-related subtlety: `F` can live in any universe,
while being an immersion at `x` requires the existence of a complement in the same universe as
the model normed space of `N`. This is solved by `smallComplement` and `smallEquiv`.
-/
lemma isImmersionAt (h : IsImmersionAtOfComplement F I J n f x) :
    IsImmersionAt I J n f x := by
  use h.smallComplement, by infer_instance, by infer_instance
  exact (IsImmersionAtOfComplement.congr_F h.smallEquiv).mp h

open IsManifold in
/- The inclusion of an open subset `s` of a smooth manifold `M` is an immersion at every point. -/
lemma of_opens [IsManifold I n M] (s : TopologicalSpace.Opens M) (y : s) :
    IsImmersionAtOfComplement PUnit I I n (Subtype.val : s → M) y := by
  apply mk_of_continuousAt_of_extChartAt (by fun_prop) (.prodUnique 𝕜 E _)
  intro x hx
  suffices I ((chartAt H y) ((chartAt H y).symm (I.symm x))) = x by simpa +contextual
  simp_all

/-- Every `ModelWithCorners 𝕜 E H` is an immersion when viewed as a map `H → E`. -/
protected lemma _root_.ModelWithCorners.isImmersionAtOfComplement {n : ℕ} {x : H} :
    IsImmersionAtOfComplement PUnit I 𝓘(𝕜, E) n I x :=
  mk_of_continuousAt_of_extChartAt (by fun_prop) (.prodUnique ..)
    (by simp [Function.comp_def, chartAt_self_eq])

omit [ChartedSpace H M] [ChartedSpace G N] in
/-- If `f` maps the source of a chart `φ` into the source of a chart `ψ` and reads as
`u ↦ equiv (u, 0)` in these charts, as for the charts of an immersion, then `f` is continuous on
the source of `φ`. -/
theorem continuousOn_of_eqOn {φ : OpenPartialHomeomorph M H} {ψ : OpenPartialHomeomorph N G}
    {equiv : (E × F) ≃L[𝕜] E''} (hsource : φ.source ⊆ f ⁻¹' ψ.source)
    (hwritten : EqOn ((ψ.extend J) ∘ f ∘ (φ.extend I).symm) (equiv ∘ (·, 0)) (φ.extend I).target) :
    ContinuousOn f φ.source := by
  rw [← φ.continuousOn_writtenInExtend_iff le_rfl hsource (I' := J) (I := I),
    ← φ.extend_target_eq_image_source]
  have : ContinuousOn (equiv ∘ fun x ↦ (x, 0)) (φ.extend I).target := by fun_prop
  exact this.congr hwritten

/-- A `C^n` immersion at `x` is continuous at `x`. -/
theorem continuousAt (h : IsImmersionAtOfComplement F I J n f x) : ContinuousAt f x := by
  obtain ⟨p⟩ := h
  obtain ⟨equiv, hwritten⟩ := p.property
  exact (continuousOn_of_eqOn p.source_subset_preimage_source hwritten).continuousAt
    (p.domChart.open_source.mem_nhds p.mem_domChart_source)

/-- If `f` maps the source of a chart `φ` into the source of a chart `ψ` of the maximal atlases and
reads as `u ↦ equiv (u, 0)` in these charts, as for the charts of an immersion, then `f` is `C^n`
on the source of `φ`. -/
theorem contMDiffOn_of_eqOn {φ : OpenPartialHomeomorph M H} {ψ : OpenPartialHomeomorph N G}
    {equiv : (E × F) ≃L[𝕜] E''} (hφ : φ ∈ IsManifold.maximalAtlas I n M)
    (hψ : ψ ∈ IsManifold.maximalAtlas J n N) (hsource : φ.source ⊆ f ⁻¹' ψ.source)
    (hwritten : EqOn ((ψ.extend J) ∘ f ∘ (φ.extend I).symm) (equiv ∘ (·, 0)) (φ.extend I).target) :
    CMDiff[φ.source] n f := by
  rw [← φ.contMDiffOn_writtenInExtend_iff hφ hψ le_rfl hsource,
    ← φ.extend_target_eq_image_source]
  have : CMDiff n (equiv ∘ fun x ↦ (x, 0)) := by
    rw [contMDiff_iff_contDiff]; fun_prop
  exact this.contMDiffOn.congr hwritten

/-- A `C^n` immersion at `x` is `C^n` at `x`. -/
theorem contMDiffAt (h : IsImmersionAtOfComplement F I J n f x) : CMDiffAt n f x := by
  obtain ⟨p⟩ := h
  obtain ⟨equiv, hwritten⟩ := p.property
  exact (contMDiffOn_of_eqOn p.domChart_mem_maximalAtlas p.codChart_mem_maximalAtlas
    p.source_subset_preimage_source hwritten).contMDiffAt
    (p.domChart.open_source.mem_nhds p.mem_domChart_source)

/-- Let `f : M → N` be a function, and suppose `φ : N → N'` is a `C^n` immersion at `f x`, such
that `φ ∘ f` is `C^n` at `x`. Let `x ∈ t ⊆ M` be contained in the slice chart at `f x`.
Then `f` seen in the slice chart at `φ (f x)` and the preferred chart at `x`
is `C^n` at (the image of) `x` within (the image of) `t`. -/
private lemma aux {f : M → N} {φ : N → N'}
    (h : LocalPresentationAt J J' n φ (f x) (ImmersionAtProp F J J' N N'))
    {equiv : (E'' × F) ≃L[𝕜] E'''}
    (hwritten : EqOn ((h.codChart.extend J') ∘ φ ∘ (h.domChart.extend J).symm) (equiv ∘ (·, 0))
      (h.domChart.extend J).target)
    (h' : CMDiffAt n (φ ∘ f) x)
    {t : Set M} (ht : t ⊆ f ⁻¹' h.domChart.source) (hxt : x ∈ t) :
    ContDiffWithinAt 𝕜 n ((h.domChart.extend J) ∘ f ∘ (extChartAt I x).symm)
      ((extChartAt I x).symm ⁻¹' t ∩ range I) ((extChartAt I x) x) := by
  -- Consider the local expressions of `f`, `φ`, `x` and `s'` in the charts we're considering.
  set f' := (h.domChart.extend J) ∘ f ∘ (extChartAt I x).symm
  set φ' := (h.codChart.extend J') ∘ φ ∘ (h.domChart.extend J).symm
  set x' := (extChartAt I x) x
  set s := (extChartAt I x).symm ⁻¹' t ∩ range I
  have hx' : extChartAt I x x ∈ s := ⟨by simp [mem_chart_source H x, hxt], mem_range_self _⟩
  have h'loc : ContDiffWithinAt 𝕜 n ((h.codChart.extend J') ∘ (φ ∘ f) ∘ (extChartAt I x).symm)
      ((extChartAt I x).symm ⁻¹' t ∩ range I) (extChartAt I x x) := by
    replace h' : CMDiffAt[t] n (φ ∘ f) x := h'.contMDiffWithinAt
    rw [contMDiffWithinAt_iff_of_mem_maximalAtlas' h.codChart_mem_maximalAtlas] at h'
    exacts [h'.2, h.mem_codChart_source]
  -- By hypothesis, `φ ∘ f` (read in our charts) is `C^n` at `x'` within `s`.
  have h'' : ContDiffWithinAt 𝕜 n (φ' ∘ f') s x' := by
    apply h'loc.congr_of_mem (fun y hy ↦ ?_) hx'
    simp only [mfld_simps, φ', f']
    rw [h.domChart.left_inv]
    apply ht hy.1
  -- On the other hand, composing `f'` with the inclusion `u ↦ (u, 0)` is also `C^n`
  -- (as a composition of `C^n` functions); this locally equals `φ ∘ f` in coordinates
  -- (since `f` is an immersion).
  set f'' := (equiv ∘ fun x ↦ (x, 0)) ∘ f'
  have h''' : ContDiffWithinAt 𝕜 n f'' s x' := by
    refine h''.congr_of_mem (fun y hy ↦ ?_) hx'
    simp only [f'', φ', f']
    nth_rw 2 [comp_apply]
    have hw : EqOn ((h.codChart.extend J') ∘ φ ∘ (h.domChart.extend J).symm) (equiv ∘ (·, 0))
        (h.domChart.extend J).target := hwritten
    rw [Function.comp_apply, hw]
    rw [h.domChart.extend_target_eq_image_source]
    exact ⟨(f ∘ (extChartAt I x).symm) y, ht hy.1, by simp⟩
  -- Composing with a suitable projection to cancel the inclusion, we deduce that `f` is `C^n`.
  have h'''' : ContDiffWithinAt 𝕜 n ((Prod.fst ∘ equiv.symm) ∘ f'') s x' :=
    ContDiffWithinAt.comp x' (by fun_prop) h''' (mapsTo_univ _ _)
  exact h''''.congr_of_mem (fun y hy ↦ by simp [f'']) hx'

/-- A function `f : M → N` between `C^n` manifolds is `C^n` at `x` if and only if it is continuous
at `x` and its composition `φ ∘ f` with a `C^n` immersion `φ : N → N'` at `f x` is `C^n` at `x`. -/
lemma _root_.ContMDiffAt.iff_comp_isImmersionAtOfComplement
    {f : M → N} {φ : N → N'} (hφ : IsImmersionAtOfComplement F J J' n φ (f x)) :
    -- Note: `φ` need not be inducing, so continuity of `φ ∘ f` at `x`
    -- generally does not imply continuity of `f`
    CMDiffAt n f x ↔ ContinuousAt f x ∧ CMDiffAt n (φ ∘ f) x := by
  refine ⟨fun hf ↦ ⟨hf.continuousAt, hφ.contMDiffAt.comp x hf⟩, fun ⟨hf, h'⟩ ↦ ?_⟩
  obtain ⟨p⟩ := hφ
  obtain ⟨equiv, hwritten⟩ := p.property
  -- Since `f` is continuous at `x`, some neighbourhood `t` of `x` is mapped
  -- into `p.domChart.source` under `f`. By restriction, we may assume `t` is open,
  -- so it suffices to test smoothness on `t`.
  have : p.domChart.source ∈ 𝓝 (f x) := p.domChart.open_source.mem_nhds p.mem_domChart_source
  obtain ⟨t, ht, htopen, hxt⟩ := mem_nhds_iff.mp (hf this)
  suffices CMDiffAt[t] n f x from this.contMDiffAt <| htopen.mem_nhds hxt
  -- We test smoothness of `f` on `t` in the preferred chart at `x` and `p.domChart`.
  rw [contMDiffWithinAt_iff_of_mem_maximalAtlas'
    p.domChart_mem_maximalAtlas p.mem_domChart_source]
  refine ⟨hf.continuousWithinAt, ?_⟩
  exact aux p hwritten h' ht hxt

-- Special case of "the composition of immersions is an immersion", for post-composing
-- with a diffeomorphism: unlike the former (which requires Banach manifolds and some conditions
-- on the boundary behaviour), this statement is always true.
-- Note that generalizing this proof to diffeomorphisms w.r.t. different models with corners is not
-- trivial: constructing a codomain chart from a chart of `N` requires a nice map between
-- the topological spaces that `N` and `N'` are modelled on. `Φ` does not induce such a map.
-- Also, for `n = 0` it is not obvious that `E''` and `E'''` are continuously linearly equivalent.
-- The current version may be good enough in practice.
/-- Post-composing an immersion at `x` with a diffeomorphism for the same model with corners
still yields an immersion at `x`. -/
lemma comp_diffeomorph
    {N' : Type*} [TopologicalSpace N'] [ChartedSpace G N'] [IsManifold J n N']
    (h : IsImmersionAtOfComplement F I J n f x) (Φ : Diffeomorph J J N N' n) :
    IsImmersionAtOfComplement F I J n (Φ ∘ f) x := by
  have := h.continuousAt -- help `fun_prop`
  obtain ⟨p⟩ := h
  obtain ⟨equiv, hwritten⟩ := p.property
  apply mk_of_continuousAt (by fun_prop) equiv
    p.domChart (Φ.symm.toHomeomorph.transOpenPartialHomeomorph p.codChart)
    p.mem_domChart_source (by simp [p.mem_codChart_source]) p.domChart_mem_maximalAtlas ?_
  · intro x hx
    simpa using hwritten hx
  · apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
    · have : Φ.symm.symm ⁻¹' Φ.symm ⁻¹' p.codChart.source = p.codChart.source := by ext; simp
      simpa [this] using contMDiffOn_of_mem_maximalAtlas p.codChart_mem_maximalAtlas
    · simpa using contMDiffOn_symm_of_mem_maximalAtlas p.codChart_mem_maximalAtlas

/-- If `f` is an immersion at `x`, then `mfderiv f x` has a continuous left inverse. -/
lemma isDiffImmersionAt (h : IsImmersionAtOfComplement F I J n f x) (hn : n ≠ 0) :
    IsDiffImmersionAt I J f x := by
  have hn' : 1 ≤ n := ENat.one_le_iff_ne_zero_withTop.mpr hn
  have hf := h.contMDiffAt
  obtain ⟨p⟩ := h
  obtain ⟨equiv, hwritten⟩ := p.property
  suffices IsDiffImmersionAt I 𝓘(𝕜, E'') ((p.codChart.extend J) ∘ f) x by
    apply IsDiffImmersionAt.of_comp (hf.mdifferentiableAt hn) ?_ this
    exact p.codChart.mdifferentiableAt_extend
      (IsManifold.maximalAtlas_subset_of_le hn' p.codChart_mem_maximalAtlas) p.mem_codChart_source
  -- The local representative of f in the nice charts at x, as a continuous linear map.
  let rhs : E →L[𝕜] E'' := equiv.toContinuousLinearMap.comp ((ContinuousLinearMap.id _ _).prod 0)
  have heq : EqOn ((p.codChart.extend J) ∘ f) (rhs ∘ (p.domChart.extend I)) p.domChart.source := by
    intro x' hx'
    trans ((p.codChart.extend J) ∘ f ∘ (p.domChart.extend I).symm ∘ (p.domChart.extend I)) x'
    · simp [p.domChart.left_inv hx']
    · exact hwritten ((p.domChart.extend I).map_source' (by simpa))
  suffices IsDiffImmersionAt I 𝓘(𝕜, E'') (rhs ∘ (p.domChart.extend I)) x from
    this.congr
      (Filter.eventually_of_mem (p.domChart.open_source.mem_nhds p.mem_domChart_source) heq)
  apply IsDiffImmersionAt.comp (I' := 𝓘(𝕜, E))
  · apply equiv.isDiffImmersionAt.comp
    dsimp
    rw [isDiffImmersionAt_iff, mfderiv_eq_fderiv, ContinuousLinearMap.fderiv]
    exact ContinuousLinearMap.HasLeftInverse.inl
  · exact IsDiffImmersionAt.of_mfderiv_isInvertible <| isInvertible_mfderiv_extend
      (IsManifold.maximalAtlas_subset_of_le hn' p.domChart_mem_maximalAtlas)
      (by simp [p.mem_domChart_source])

/-- An immersion at `x` has injective differential. -/
lemma injective_mfderiv (h : IsImmersionAtOfComplement F I J n f x) (hn : n ≠ 0) :
    Injective (mfderiv% f x) :=
  (h.isDiffImmersionAt hn).mfderiv_injective

end IsImmersionAtOfComplement

namespace IsImmersionAt

lemma mk_of_charts (equiv : (E × F) ≃L[𝕜] E'')
    (domChart : OpenPartialHomeomorph M H) (codChart : OpenPartialHomeomorph N G)
    (hx : x ∈ domChart.source) (hfx : f x ∈ codChart.source)
    (hdomChart : domChart ∈ IsManifold.maximalAtlas I n M)
    (hcodChart : codChart ∈ IsManifold.maximalAtlas J n N)
    (hsource : domChart.source ⊆ f ⁻¹' codChart.source)
    (hwrittenInExtend : EqOn ((codChart.extend J) ∘ f ∘ (domChart.extend I).symm) (equiv ∘ (·, 0))
      (domChart.extend I).target) : IsImmersionAt I J n f x := by
  have aux : IsImmersionAtOfComplement F I J n f x := by
    apply IsImmersionAtOfComplement.mk_of_charts <;> assumption
  use aux.smallComplement, by infer_instance, by infer_instance
  rwa [← IsImmersionAtOfComplement.congr_F aux.smallEquiv]

/-- `f : M → N` is a `C^n` immersion at `x` if there are charts `φ` and `ψ` of `M` and `N`
around `x` and `f x`, respectively such that in these charts, `f` looks like `u ↦ (u, 0)`.
This version does not assume that `f` maps `φ.source` to `ψ.source`,
but that `f` is continuous at `x`. -/
lemma mk_of_continuousAt {f : M → N} {x : M} (hf : ContinuousAt f x) (equiv : (E × F) ≃L[𝕜] E'')
    (domChart : OpenPartialHomeomorph M H) (codChart : OpenPartialHomeomorph N G)
    (hx : x ∈ domChart.source) (hfx : f x ∈ codChart.source)
    (hdomChart : domChart ∈ IsManifold.maximalAtlas I n M)
    (hcodChart : codChart ∈ IsManifold.maximalAtlas J n N)
    (hwrittenInExtend : EqOn ((codChart.extend J) ∘ f ∘ (domChart.extend I).symm) (equiv ∘ (·, 0))
      (domChart.extend I).target) : IsImmersionAt I J n f x := by
  have aux : IsImmersionAtOfComplement F I J n f x := by
    apply IsImmersionAtOfComplement.mk_of_continuousAt <;> assumption
  use aux.smallComplement, by infer_instance, by infer_instance
  rwa [← IsImmersionAtOfComplement.congr_F aux.smallEquiv]

/-- If `f` is an immersion at `x` and `g = f` on some neighbourhood of `x`,
then `g` is an immersion at `x`. -/
lemma congr_of_eventuallyEq (hf : IsImmersionAt I J n f x) (hfg : f =ᶠ[𝓝 x] g) :
    IsImmersionAt I J n g x := by
  obtain ⟨F, _, _, hf⟩ := hf
  exact ⟨F, _, _, hf.congr_of_eventuallyEq hfg⟩

/-- If `f = g` on some neighbourhood of `x`,
then `f` is an immersion at `x` if and only if `g` is an immersion at `x`. -/
lemma congr_iff (hfg : f =ᶠ[𝓝 x] g) :
    IsImmersionAt I J n f x ↔ IsImmersionAt I J n g x :=
  ⟨fun h ↦ h.congr_of_eventuallyEq hfg, fun h ↦ h.congr_of_eventuallyEq hfg.symm⟩

/- The set of points where `IsImmersionAt` holds is open. -/
lemma _root_.IsOpen.isImmersionAt :
    IsOpen {x | IsImmersionAt I J n f x} := by
  rw [isOpen_iff_forall_mem_open]
  rintro x ⟨F, _, _, hx⟩
  exact ⟨{x | IsImmersionAtOfComplement F I J n f x }, fun y hy ↦ hy.isImmersionAt,
    .isImmersionAtOfComplement, hx⟩

/-- If `f: M → N` and `g: M' × N'` are immersions at `x` and `x'`, respectively,
then `f × g: M × N → M' × N'` is an immersion at `(x, x')`. -/
theorem prodMap {f : M → N} {g : M' → N'} {x' : M'}
    [IsManifold I n M] [IsManifold I' n M'] [IsManifold J n N] [IsManifold J' n N']
    (hf : IsImmersionAt I J n f x) (hg : IsImmersionAt I' J' n g x') :
    IsImmersionAt (I.prod I') (J.prod J') n (Prod.map f g) (x, x') := by
  obtain ⟨F, _, _, hf⟩ := hf
  obtain ⟨F', _, _, hg⟩ := hg
  exact (hf.prodMap hg).isImmersionAt

/- The inclusion of an open subset `s` of a smooth manifold `M` is an immersion at every point. -/
lemma of_opens [IsManifold I n M] (s : TopologicalSpace.Opens M) (hx : x ∈ s) :
    IsImmersionAt I I n (Subtype.val : s → M) ⟨x, hx⟩ := by
  use PUnit, by infer_instance, by infer_instance
  apply IsImmersionAtOfComplement.of_opens

/-- Every `ModelWithCorners 𝕜 E H` is an immersion when viewed as a map `H → E`. -/
protected lemma _root_.ModelWithCorners.isImmersionAt {n : ℕ} {x : H} :
    IsImmersionAt I (modelWithCornersSelf 𝕜 E) n I x := by
  use PUnit, by infer_instance, by infer_instance
  exact I.isImmersionAtOfComplement

/-- A `C^n` immersion at `x` is continuous at `x`. -/
theorem continuousAt (h : IsImmersionAt I J n f x) : ContinuousAt f x := by
  obtain ⟨F, _, _, h⟩ := h
  exact h.continuousAt

/-- A `C^n` immersion at `x` is `C^n` at `x`. -/
theorem contMDiffAt (h : IsImmersionAt I J n f x) : CMDiffAt n f x := by
  obtain ⟨F, _, _, h⟩ := h
  exact h.contMDiffAt

/-- A function `f : M → N` between `C^n` manifolds is `C^n` at `x` if and only if it is continuous
at `x` and its composition `φ ∘ f` with a `C^n` immersion `φ : N → N'` at `f x` is `C^n` at `x`. -/
lemma _root_.ContMDiffAt.iff_comp_isImmersionAt {f : M → N} {φ : N → N'}
    (hφ : IsImmersionAt J J' n φ (f x)) :
    -- Note: `φ` need not be inducing, so continuity of `φ ∘ f` at `x`
    -- generally does not imply continuity of `f`
    CMDiffAt n f x ↔ ContinuousAt f x ∧ CMDiffAt n (φ ∘ f) x := by
  obtain ⟨F, _, _, hφ⟩ := hφ
  rw [← ContMDiffAt.iff_comp_isImmersionAtOfComplement hφ]

/-- Post-composing an immersion at `x` with a diffeomorphism for the same model with corners
still yields an immersion at `x`. -/
lemma comp_diffeomorph
    {N' : Type*} [TopologicalSpace N'] [ChartedSpace G N'] [IsManifold J n N']
    (h : IsImmersionAt I J n f x) (Φ : Diffeomorph J J N N' n) :
    IsImmersionAt I J n (Φ ∘ f) x := by
  obtain ⟨F, _, _, h⟩ := h
  exact ⟨F, _, _, h.comp_diffeomorph Φ⟩

/-- If `f` is an immersion at `x`, then `mfderiv f x` has a continuous left inverse. -/
lemma isDiffImmersionAt (h : IsImmersionAt I J n f x) (hn : n ≠ 0) :
    IsDiffImmersionAt I J f x := by
  obtain ⟨F, _, _, h⟩ := h
  exact h.isDiffImmersionAt hn

/-- An immersion at `x` has injective differential. -/
lemma injective_mfderiv (h : IsImmersionAt I J n f x) (hn : n ≠ 0) : Injective (mfderiv% f x) :=
  (h.isDiffImmersionAt hn).mfderiv_injective

end IsImmersionAt

variable (F I J n) in
/-- `f : M → N` is a `C^n` immersion if around each point `x ∈ M`,
there are charts `φ` and `ψ` of `M` and `N` around `x` and `f x`, respectively
such that in these charts, `f` looks like `u ↦ (u, 0)`.

In other words, `f` is an immersion at each `x ∈ M`.

This definition has a fixed parameter `F`, which is a choice of complement of `E` in `E'`:
being an immersion at `x` includes a choice of linear isomorphism between `E × F` and `E'`.
-/
@[expose]
def IsImmersionOfComplement (f : M → N) : Prop := ∀ x, IsImmersionAtOfComplement F I J n f x

variable (I J n) in
/-- `f : M → N` is a `C^n` immersion if around each point `x ∈ M`,
there are charts `φ` and `ψ` of `M` and `N` around `x` and `f x`, respectively
such that in these charts, `f` looks like `u ↦ (u, 0)`.

Implicit in this definition is an abstract choice `F` of a complement of `E` in `E'`:
being an immersion includes a choice of linear isomorphism between `E × F` and `E'`, which is where
the choice of `F` enters. If you need stronger control over the complement `F`,
use `IsImmersionOfComplement` instead.

Note that our global choice of complement is a bit stronger than asking `f` to be an immersion at
each `x ∈ M` w.r.t. potentially varying complements: see `isImmersionAt` for details.
-/
def IsImmersion (f : M → N) : Prop :=
  ∃ (F : Type u) (_ : NormedAddCommGroup F) (_ : NormedSpace 𝕜 F), IsImmersionOfComplement F I J n f

namespace IsImmersionOfComplement

variable {f g : M → N}

/-- If `f` is an immersion, it is an immersion at each point. -/
lemma isImmersionAt (h : IsImmersionOfComplement F I J n f) (x : M) :
    IsImmersionAtOfComplement F I J n f x := h x

/-- If `f = g` and `f` is an immersion, so is `g`. -/
theorem congr (h : IsImmersionOfComplement F I J n f) (heq : f = g) :
    IsImmersionOfComplement F I J n g :=
  heq ▸ h

lemma trans_F (h : IsImmersionOfComplement F I J n f) (e : F ≃L[𝕜] F') :
    IsImmersionOfComplement F' I J n f :=
  fun x ↦ (h x).trans_F e

/-- Being an immersion w.r.t. `F` is stable under replacing `F` by an isomorphic copy. -/
lemma congr_F (e : F ≃L[𝕜] F') :
    IsImmersionOfComplement F I J n f ↔ IsImmersionOfComplement F' I J n f :=
  ⟨fun h ↦ trans_F (e := e) h, fun h ↦ trans_F (e := e.symm) h⟩

/-- If `f: M → N` and `g: M' × N'` are immersions at `x` and `x'` (w.r.t. `F` and `F'`),
respectively, then `f × g: M × N → M' × N'` is an immersion at `(x, x')` w.r.t. `F × F'`. -/
theorem prodMap {f : M → N} {g : M' → N'}
    [IsManifold I n M] [IsManifold I' n M'] [IsManifold J n N] [IsManifold J' n N']
    (h : IsImmersionOfComplement F I J n f) (h' : IsImmersionOfComplement F' I' J' n g) :
    IsImmersionOfComplement (F × F') (I.prod I') (J.prod J') n (Prod.map f g) :=
  fun ⟨x, x'⟩ ↦ (h x).prodMap (h' x')

/-- If `f` is an immersion w.r.t. some complement `F`, it is an immersion.

Note that the proof contains a small formalisation-related subtlety: `F` can live in any universe,
while being an immersion requires the existence of a complement in the same universe as
the model normed space of `N`. This is solved by `smallComplement` and `smallEquiv`.
-/
lemma isImmersion (h : IsImmersionOfComplement F I J n f) : IsImmersion I J n f := by
  by_cases! hM : IsEmpty M
  · rw [IsImmersion]
    use PUnit, by infer_instance, by infer_instance
    exact fun x ↦ (IsEmpty.false x).elim
  inhabit M
  let x : M := Inhabited.default
  use (h x).smallComplement, by infer_instance, by infer_instance
  exact (IsImmersionOfComplement.congr_F (h x).smallEquiv).mp h

open IsManifold in
/-- The identity map is an immersion with complement `PUnit`. -/
protected lemma id [IsManifold I n M] : IsImmersionOfComplement PUnit I I n (@id M) := by
  intro x
  apply IsImmersionAtOfComplement.mk_of_continuousAt_of_extChartAt continuousAt_id (.prodUnique ..)
  intro y hy
  have : I ((chartAt H x) ((chartAt H x).symm (I.symm y))) = y := by
    rw [(chartAt H x).right_inv (by simp_all), I.right_inv (by simp_all)]
  simpa

/- The inclusion of an open subset `s` of a smooth manifold `M` is an immersion. -/
lemma of_opens [IsManifold I n M] (s : TopologicalSpace.Opens M) :
    IsImmersionOfComplement PUnit I I n (Subtype.val : s → M) :=
  fun y ↦ IsImmersionAtOfComplement.of_opens s y

/-- Every `ModelWithCorners 𝕜 E H` is an immersion when viewed as a map `H → E`. -/
protected lemma _root_.ModelWithCorners.isImmersionOfComplement {n : ℕ} :
    IsImmersionOfComplement PUnit I (modelWithCornersSelf 𝕜 E) n I :=
  fun _ ↦ I.isImmersionAtOfComplement

/-- Post-composing an immersion with a diffeomorphism for the same model with corners
still yields an immersion. -/
lemma comp_diffeomorph
    {N' : Type*} [TopologicalSpace N'] [ChartedSpace G N'] [IsManifold J n N']
    (h : IsImmersionOfComplement F I J n f) (Φ : Diffeomorph J J N N' n) :
    IsImmersionOfComplement F I J n (Φ ∘ f) :=
  fun x ↦ (h x).comp_diffeomorph Φ

/-- Given `C^n` manifolds `M` and `N` over the same model `I`,
`Sum.inl : M → M ⊕ N` is a `C^n` immersion with complement `Unit` -/
lemma sumInl {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M']
    [IsManifold I n M] [IsManifold I n M'] :
    IsImmersionOfComplement Unit I I n (@Sum.inl M M') := by
  intro x
  apply IsImmersionAtOfComplement.mk_of_continuousAt_of_extChartAt (by fun_prop) (.prodUnique ..)
  intro y hy
  have : I ((chartAt H x) ((chartAt H x).symm (I.symm y))) = y := by
    rw [(chartAt H x).right_inv (by simp_all), I.right_inv (by simp_all)]
  simpa

/-- Given `C^n` manifolds `M` and `N` over the same model `I`,
`Sum.inr : N → M ⊕ N` is a `C^n` immersion with complement `Unit` -/
lemma sumInr {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M']
    [IsManifold I n M] [IsManifold I n M'] :
    IsImmersionOfComplement Unit I I n (@Sum.inr M M') := by
  rw [← Diffeomorph.sumComm_inl I M' n M]
  exact IsImmersionOfComplement.sumInl.comp_diffeomorph (Diffeomorph.sumComm I M' n M)

/-- A `C^n` immersion is `C^n`. -/
theorem contMDiff (h : IsImmersionOfComplement F I J n f) : CMDiff n f :=
  fun x ↦ (h x).contMDiffAt

/-- A function `f : M → N` between `C^n` manifolds is `C^n` if and only if it is continuous
and its composition `φ ∘ f` with a `C^n` immersion `φ : N → N'` is `C^n`. -/
lemma _root_.ContMDiff.iff_comp_isImmersionOfComplement {f : M → N} {φ : N → N'}
    (hφ : IsImmersionOfComplement F J J' n φ) :
    CMDiff n f ↔ Continuous f ∧ CMDiff n (φ ∘ f) := by
  refine ⟨fun h ↦ ⟨h.continuous, hφ.contMDiff.comp h⟩, fun ⟨h, h'⟩ x ↦ ?_⟩
  rw [ContMDiffAt.iff_comp_isImmersionAtOfComplement (hφ (f x))]
  exact ⟨h.continuousAt, h' x⟩

/-- If `f` is an immersion, each differential `mfderiv f x` has a continuous left inverse. -/
lemma isDiffImmersionAt (h : IsImmersionOfComplement F I J n f) (hn : n ≠ 0) (x : M) :
    IsDiffImmersionAt I J f x :=
  (h x).isDiffImmersionAt hn

/-- An immersion has injective differential at each point. -/
lemma injective_mfderiv (h : IsImmersionOfComplement F I J n f) (hn : n ≠ 0) (x : M) :
    Injective (mfderiv% f x) :=
  (h x).injective_mfderiv hn

end IsImmersionOfComplement

namespace IsImmersion

variable {f g : M → N}

/-- If `f` is an immersion, it is an immersion at each point.

Note that the converse statement is false in general:
if `f` is an immersion at each `x`, but with the choice of complement possibly depending on `x`,
there need not be a global choice of complement for which `f` is an immersion at each point.
The complement of `f` at `x` is isomorphic to the cokernel of `mfderiv I J f x`, but the `mfderiv`
of `f` at (even nearby) points `x` and `x'` are not directly related. They have the same rank
(the dimension of `E`, as will follow from injectivity), but if `E''` is infinite-dimensional this
is not conclusive. If `E''` is infinite-dimensional, this dimension can indeed change between
different connected components of `M`.
-/
lemma isImmersionAt (h : IsImmersion I J n f) (x : M) : IsImmersionAt I J n f x := by
  obtain ⟨F, _, _, h⟩ := h
  exact ⟨F, _, _, h x⟩

/-- If `f = g` and `f` is an immersion, so is `g`. -/
theorem congr (h : IsImmersion I J n f) (heq : f = g) : IsImmersion I J n g :=
  heq ▸ h

/-- If `f: M → N` and `g: M' × N'` are immersions at `x` and `x'`, respectively,
then `f × g: M × N → M' × N'` is an immersion at `(x, x')`. -/
theorem prodMap {f : M → N} {g : M' → N'}
    [IsManifold I n M] [IsManifold I' n M'] [IsManifold J n N] [IsManifold J' n N']
    (hf : IsImmersion I J n f) (hg : IsImmersion I' J' n g) :
    IsImmersion (I.prod I') (J.prod J') n (Prod.map f g) := by
  obtain ⟨F, _, _, hf⟩ := hf
  obtain ⟨F', _, _, hg⟩ := hg
  exact (hf.prodMap hg).isImmersion

open IsManifold in
/-- The identity map is an immersion. -/
protected lemma id [IsManifold I n M] : IsImmersion I I n (@id M) := by
  use PUnit, by infer_instance, by infer_instance
  exact IsImmersionOfComplement.id

/- The inclusion of an open subset `s` of a smooth manifold `M` is an immersion. -/
lemma of_opens [IsManifold I n M] (s : TopologicalSpace.Opens M) :
    IsImmersion I I n (Subtype.val : s → M) := by
  use PUnit, by infer_instance, by infer_instance
  exact IsImmersionOfComplement.of_opens s

/-- Every `ModelWithCorners 𝕜 E H` is an immersion when viewed as a map `H → E`. -/
protected lemma _root_.ModelWithCorners.isImmersion {n : ℕ} :
    IsImmersion I (modelWithCornersSelf 𝕜 E) n I := by
  use PUnit, by infer_instance, by infer_instance
  exact I.isImmersionOfComplement

/-- A `C^n` immersion is `C^n`. -/
theorem contMDiff (h : IsImmersion I J n f) : CMDiff n f :=
  fun x ↦ (h.isImmersionAt x).contMDiffAt

/-- A function `f : M → N` between `C^n` manifolds is `C^n` if and only if it is continuous
and its composition `φ ∘ f` with a `C^n` immersion `φ : N → N'` is `C^n`. -/
lemma _root_.ContMDiff.iff_comp_isImmersion {f : M → N} {φ : N → N'} (hφ : IsImmersion J J' n φ) :
    CMDiff n f ↔ Continuous f ∧ CMDiff n (φ ∘ f) := by
  obtain ⟨F, _, _, hφ⟩ := hφ
  rw [ContMDiff.iff_comp_isImmersionOfComplement hφ]

/-- Post-composing an immersion with a diffeomorphism for the same model with corners
still yields an immersion. -/
lemma comp_diffeomorph {N' : Type*} [TopologicalSpace N'] [ChartedSpace G N'] [IsManifold J n N']
    (h : IsImmersion I J n f) (Φ : Diffeomorph J J N N' n) :
    IsImmersion I J n (Φ ∘ f) := by
  obtain ⟨F, _, _, h⟩ := h
  exact ⟨F, _, _, h.comp_diffeomorph Φ⟩

/-- If `f` is an immersion, each differential `mfderiv f x` has a continuous left inverse. -/
lemma isDiffImmersionAt (h : IsImmersion I J n f) (hn : n ≠ 0) (x : M) :
    IsDiffImmersionAt I J f x :=
  (h.isImmersionAt x).isDiffImmersionAt hn

/-- An immersion has injective differential at each point. -/
lemma injective_mfderiv (h : IsImmersion I J n f) (hn : n ≠ 0) (x : M) :
    Injective (mfderiv% f x) :=
  (h.isImmersionAt x).injective_mfderiv hn

end IsImmersion

end Manifold
