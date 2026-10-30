/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Asymptotics.TVS

/-!
# The Fréchet derivative: definition

Let `E` and `F` be normed spaces, `f : E → F`, and `f' : E →L[𝕜] F` a
continuous 𝕜-linear map, where `𝕜` is a non-discrete normed field. More generally, a function
`f : D → F` can be differentiated in coordinates `coord : D → E`. A subset uses its inclusion;
units use their coercion into the ambient algebra. The tangent space stays `E`. Identity
coordinates are the default for an ambient function. Then

  `HasFDerivWithinAt f f' s x`

says that `f` has derivative `f'` at `x`, where the domain of interest
is restricted to `s`. We also have

  `HasFDerivAt f f' x := HasFDerivWithinAt f f' x univ`

Finally,

  `HasStrictFDerivAt f f' x`

means that `f : E → F` has derivative `f' : E →L[𝕜] F` in the sense of strict differentiability,
i.e., `f y - f z - f'(y - z) = o(y - z)` as `y, z → x`. This notion is used in the inverse
function theorem, and is defined here only to avoid proving theorems like
`IsBoundedBilinearMap.hasFDerivAt` twice: first for `HasFDerivAt`, then for
`HasStrictFDerivAt`.

This file `Defs.lean` is intended to just contain the definitions and the bare minimum of
supporting lemmas; a much wider range of elementary properties are proved in the file  `Basic.lean`.

Other files in the folder `Analysis/Calculus/FDeriv/` contain the usual formulas
(and existence assertions) for the derivative of
* constants (`Const.lean`)
* the identity
* bounded linear maps (`Linear.lean`)
* bounded bilinear maps (`Bilinear.lean`)
* sum of two functions (`Add.lean`)
* sum of finitely many functions (`Add.lean`)
* multiplication of a function by a scalar constant (`Add.lean`)
* negative of a function (`Add.lean`)
* subtraction of two functions (`Add.lean`)
* multiplication of a function by a scalar function (`Mul.lean`)
* multiplication of two scalar functions (`Mul.lean`)
* composition of functions (the chain rule) (`Comp.lean`)
* inverse function (`Mul.lean`)
  (assuming that it exists; the inverse function theorem is in `../Inverse.lean`)

## Implementation details

The derivative is defined in terms of the `IsLittleOTVS` relation to ensure the definition does not
ingrain a choice of norm, and is then quickly translated to the more convenient `IsLittleO` in the
subsequent theorems. It is also characterized in terms of the `Tendsto` relation.

We also introduce predicates `DifferentiableWithinAt 𝕜 f s x` (where `𝕜` is the base field,
`f` the function to be differentiated, `x` the point at which the derivative is asserted to exist,
and `s` the set along which the derivative is defined), as well as `DifferentiableAt 𝕜 f x`,
`DifferentiableOn 𝕜 f s` and `Differentiable 𝕜 f` to express the existence of a derivative.

To be able to compute with derivatives, we write `fderivWithin 𝕜 f s x` and `fderiv 𝕜 f x`
for some choice of a derivative if it exists, and the zero function otherwise. This choice only
behaves well along sets for which the derivative is unique, i.e., those for which the tangent
directions span a dense subset of the whole space. The predicates `UniqueDiffWithinAt s x` and
`UniqueDiffOn s`, defined in `TangentCone.lean` express this property. We prove that indeed
they imply the uniqueness of the derivative. This is satisfied for open subsets, and in particular
for `univ`. This uniqueness only holds when the field is non-discrete, which we request at the very
beginning: otherwise, a derivative can be defined, but it has no interesting properties whatsoever.

## TODO

Generalize more results to topological vector spaces.

## Tags

derivative, differentiable, Fréchet, calculus

-/

@[expose] public section

open Filter Asymptotics ContinuousLinearMap Set

open scoped Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

noncomputable section TVS
/-!
## Definitions valid in an arbitrary topological vector space
-/

variable {E : Type*} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
variable {F : Type*} [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]

/-- A function `f` has the continuous linear map `f'` as derivative along the filter `L` if
`f x₁ = f x₂ + f' (x₁ - x₂) + o (x₁ - x₂)` when `x = (x₁, x₂)` converges along the filter `L`.
The domain `D` can be a subset or the units of an ambient algebra. In that case `coord` is
its inclusion into the ambient vector space `E`; tangent vectors and the linear map still belong
to `E`. No additive structure on `D` or extension of `f` outside `D` is required. For functions
on `E` itself, `coord` defaults to the identity, recovering the usual relation.

This definition is designed to be specialized

- for `L = 𝓝 (x, x)` (in `HasStrictFDerivAt`),
  giving rise to the derivative in the sense of strict differentiability;
- for `L = 𝓝 x ×ˢ pure x` (in `HasFDerivAt`), giving rise to the usual notion of Fréchet derivative;
- for `L = 𝓝[s] x ×ˢ pure x` (in `HasFDerivWithinAt`),
  giving rise to the notion of Fréchet derivative along the set `s`.
-/
@[mk_iff hasFDerivAtFilter_iff_isLittleOTVS]
structure HasFDerivAtFilter {D : Type*} (f : D → F) (f' : E →L[𝕜] F)
    (L : Filter (D × D)) (coord : D → E := by exact _root_.id) : Prop where
  of_isLittleOTVS ::
    isLittleOTVS :
      (fun p ↦ f p.1 - f p.2 - f' (coord p.1 - coord p.2)) =o[𝕜; L]
        (fun p ↦ coord p.1 - coord p.2)

/-- Pull back a derivative relation along a map of domains. The ambient tangent map is unchanged;
only the domain coordinates and the filter are pulled back. -/
theorem HasFDerivAtFilter.comp_tendsto {D D' : Type*} {f : D → F}
    {f' : E →L[𝕜] F} {coord : D → E} {L : Filter (D × D)}
    {L' : Filter (D' × D')} (h : HasFDerivAtFilter f f' L coord) (g : D' → D)
    (hg : Tendsto (Prod.map g g) L' L) :
    HasFDerivAtFilter (f ∘ g) f' L' (coord ∘ g) := by
  constructor
  simpa only [Function.comp_def, Prod.map] using h.isLittleOTVS.comp_tendsto hg

/-- A function `f` has the continuous linear map `f'` as derivative at `x` within a set `s` if
`f x' = f x + f' (coord x' - coord x) + o (coord x' - coord x)` as `x'` tends to `x`
inside `s`. Identity coordinates give the ordinary within-set derivative. -/
@[fun_prop]
def HasFDerivWithinAt {D : Type*} [TopologicalSpace D] (f : D → F)
    (f' : E →L[𝕜] F) (s : Set D) (x : D) (coord : D → E := by exact _root_.id) :=
  HasFDerivAtFilter f f' (𝓝[s] x ×ˢ pure x) coord

/-- A function `f` has the continuous linear map `f'` as derivative at `x` if
`f x' = f x + f' (coord x' - coord x) + o (coord x' - coord x)` as `x'` tends to `x`. -/
@[fun_prop]
def HasFDerivAt {D : Type*} [TopologicalSpace D] (f : D → F)
    (f' : E →L[𝕜] F) (x : D) (coord : D → E := by exact _root_.id) :=
  HasFDerivAtFilter f f' (𝓝 x ×ˢ pure x) coord

/-- A function `f` has derivative `f'` at `a` in the sense of *strict differentiability*
if `f x - f y - f' (coord x - coord y) = o(coord x - coord y)` as `x, y → a`.
This form of differentiability is required,
e.g., by the inverse function theorem. Any `C^1` function on a vector space over `ℝ` is strictly
differentiable but this definition works, e.g., for vector spaces over `p`-adic numbers. -/
@[fun_prop]
def HasStrictFDerivAt {D : Type*} [TopologicalSpace D] (f : D → F)
    (f' : E →L[𝕜] F) (x : D) (coord : D → E := by exact _root_.id) :=
  HasFDerivAtFilter f f' (𝓝 (x, x)) coord

variable (𝕜)

/-- A function `f` is differentiable at a point `x` within a set `s` if it admits a derivative
there (possibly non-unique). -/
@[fun_prop]
def DifferentiableWithinAt {D : Type*} [TopologicalSpace D] (f : D → F)
    (s : Set D) (x : D) (coord : D → E := by exact _root_.id) :=
  ∃ f' : E →L[𝕜] F, HasFDerivWithinAt f f' s x coord

/-- A function `f` is differentiable at a point `x` if it admits a derivative there (possibly
non-unique). -/
@[fun_prop]
def DifferentiableAt {D : Type*} [TopologicalSpace D] (f : D → F)
    (x : D) (coord : D → E := by exact _root_.id) :=
  ∃ f' : E →L[𝕜] F, HasFDerivAt f f' x coord

open scoped Classical in
/-- If `f` has a derivative at `x` within `s`, then `fderivWithin 𝕜 f s x` is such a derivative.
Otherwise, it is set to `0`. We also set it to be zero, if zero is one of possible derivatives. -/
irreducible_def fderivWithin {D : Type*} [TopologicalSpace D] (f : D → F)
    (s : Set D) (x : D) (coord : D → E := by exact _root_.id) : E →L[𝕜] F :=
  if HasFDerivWithinAt f (0 : E →L[𝕜] F) s x coord
    then 0
  else if h : DifferentiableWithinAt 𝕜 f s x coord
    then Classical.choose h
  else 0

/-- If `f` has a derivative at `x`, then `fderiv 𝕜 f x` is such a derivative. Otherwise, it is
set to `0`. -/
irreducible_def fderiv {D : Type*} [TopologicalSpace D] (f : D → F)
    (x : D) (coord : D → E := by exact _root_.id) : E →L[𝕜] F :=
  fderivWithin 𝕜 f univ x coord

/-- `DifferentiableOn 𝕜 f s` means that `f` is differentiable within `s` at any point of `s`. -/
@[fun_prop]
def DifferentiableOn {D : Type*} [TopologicalSpace D] (f : D → F)
    (s : Set D) (coord : D → E := by exact _root_.id) :=
  ∀ x ∈ s, DifferentiableWithinAt 𝕜 f s x coord

/-- `Differentiable 𝕜 f` means that `f` is differentiable at any point. -/
@[fun_prop]
def Differentiable {D : Type*} [TopologicalSpace D] (f : D → F)
    (coord : D → E := by exact _root_.id) :=
  ∀ x, DifferentiableAt 𝕜 f x coord

variable {𝕜}
variable {f : E → F}
variable {f' : E →L[𝕜] F}
variable {x : E}
variable {s : Set E}
variable {L : Filter E}

theorem hasFDerivAt_iff_isLittleOTVS {D : Type*} [TopologicalSpace D]
    {f : D → F} {coord : D → E} {x : D} :
    HasFDerivAt f f' x coord ↔
      (fun x' ↦ f x' - f x - f' (coord x' - coord x)) =o[𝕜; 𝓝 x] (fun x' ↦ coord x' - coord x) := by
  simp [HasFDerivAt, hasFDerivAtFilter_iff_isLittleOTVS, Function.comp_def]

alias ⟨HasFDerivAt.isLittleOTVS, HasFDerivAt.of_isLittleOTVS⟩ := hasFDerivAt_iff_isLittleOTVS

theorem hasFDerivWithinAt_iff_isLittleOTVS {D : Type*} [TopologicalSpace D]
    {f : D → F} {coord : D → E} {x : D} {s : Set D} :
    HasFDerivWithinAt f f' s x coord ↔
      (fun x' ↦ f x' - f x - f' (coord x' - coord x)) =o[𝕜; 𝓝[s] x]
        (fun x' ↦ coord x' - coord x) := by
  simp [HasFDerivWithinAt, hasFDerivAtFilter_iff_isLittleOTVS, Function.comp_def]

alias ⟨HasFDerivWithinAt.isLittleOTVS, HasFDerivWithinAt.of_isLittleOTVS⟩ :=
  hasFDerivWithinAt_iff_isLittleOTVS

theorem hasStrictFDerivAt_iff_isLittleOTVS {D : Type*} [TopologicalSpace D]
    {f : D → F} {coord : D → E} {x : D} :
    HasStrictFDerivAt f f' x coord ↔
      (fun p ↦ f p.1 - f p.2 - f' (coord p.1 - coord p.2)) =o[𝕜; 𝓝 (x, x)]
        (fun p ↦ coord p.1 - coord p.2) :=
  hasFDerivAtFilter_iff_isLittleOTVS f f' (𝓝 (x, x)) coord

theorem fderivWithin_zero_of_not_differentiableWithinAt (h : ¬DifferentiableWithinAt 𝕜 f s x) :
    fderivWithin 𝕜 f s x = 0 := by
  simp [fderivWithin, h]

@[simp]
theorem fderivWithin_univ : fderivWithin 𝕜 f univ = fderiv 𝕜 f := by
  ext
  rw [fderiv]

end TVS

section Normed
/-!
## Reformulations for seminormed spaces
-/

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {f : E → F} {f' : E →L[𝕜] F} {s : Set E} {x : E}

theorem hasFDerivAtFilter_iff_isLittleO {D : Type*} {f : D → F} {coord : D → E} {L : Filter (D × D)} :
    HasFDerivAtFilter f f' L coord ↔
      (fun p => f p.1 - f p.2 - f' (coord p.1 - coord p.2)) =o[L] fun p => coord p.1 - coord p.2 :=
  (hasFDerivAtFilter_iff_isLittleOTVS f f' L coord).trans isLittleOTVS_iff_isLittleO

alias ⟨HasFDerivAtFilter.isLittleO, HasFDerivAtFilter.of_isLittleO⟩ :=
  hasFDerivAtFilter_iff_isLittleO

theorem hasFDerivAt_iff_isLittleO {D : Type*} [TopologicalSpace D]
    {f : D → F} {coord : D → E} {x : D} :
    HasFDerivAt f f' x coord ↔
      (fun x' ↦ f x' - f x - f' (coord x' - coord x)) =o[𝓝 x] (fun x' ↦ coord x' - coord x) :=
  (hasFDerivAt_iff_isLittleOTVS (f := f) (f' := f') (coord := coord) (x := x)).trans
    isLittleOTVS_iff_isLittleO

alias ⟨HasFDerivAt.isLittleO, HasFDerivAt.of_isLittleO⟩ := hasFDerivAt_iff_isLittleO

theorem hasFDerivWithinAt_iff_isLittleO {D : Type*} [TopologicalSpace D]
    {f : D → F} {coord : D → E} {x : D} {s : Set D} :
    HasFDerivWithinAt f f' s x coord ↔
      (fun x' ↦ f x' - f x - f' (coord x' - coord x)) =o[𝓝[s] x] (fun x' ↦ coord x' - coord x) :=
  (hasFDerivWithinAt_iff_isLittleOTVS (f := f) (f' := f') (coord := coord) (x := x) (s := s)).trans
    isLittleOTVS_iff_isLittleO

alias ⟨HasFDerivWithinAt.isLittleO, HasFDerivWithinAt.of_isLittleO⟩ :=
  hasFDerivWithinAt_iff_isLittleO

theorem hasStrictFDerivAt_iff_isLittleO {D : Type*} [TopologicalSpace D]
    {f : D → F} {coord : D → E} {x : D} :
    HasStrictFDerivAt f f' x coord ↔
      (fun p : D × D => f p.1 - f p.2 - f' (coord p.1 - coord p.2)) =o[𝓝 (x, x)]
        fun p : D × D => coord p.1 - coord p.2 :=
  (hasStrictFDerivAt_iff_isLittleOTVS (f := f) (f' := f') (coord := coord) (x := x)).trans
    isLittleOTVS_iff_isLittleO

alias ⟨HasStrictFDerivAt.isLittleO, HasStrictFDerivAt.of_isLittleO⟩ :=
  hasStrictFDerivAt_iff_isLittleO

end Normed
