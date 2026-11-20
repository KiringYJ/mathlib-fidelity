/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Normed.Operator.Asymptotics
public import Mathlib.Analysis.Calculus.TangentCone.Basic
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.TangentCone.DimOne

/-!
# The Fréchet derivative: basic properties

Let `E` and `F` be normed spaces, `f : E → F`, and `f' : E →L[𝕜] F` a
continuous 𝕜-linear map, where `𝕜` is a non-discrete normed field. Then

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

## Main results

This file builds on the bare-bones definition given in `Defs.lean` by establishing a variety of
relatively straightforward properties of the derivative.

Deeper properties are defined in other files in the folder `Analysis/Calculus/FDeriv/`, which
contain the usual formulas (and existence assertions) for the derivative of
* constants (`Const.lean`)
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

For most binary operations we also define `const_op` and `op_const` theorems for the cases when
the first or second argument is a constant. This makes writing chains of `HasDerivAt`'s easier,
and they more frequently lead to the desired result.

One can also interpret the derivative of a function `f : 𝕜 → E` as an element of `E` (by identifying
a linear function from `𝕜` to `E` with its value at `1`). Results on the Fréchet derivative are
translated to this more elementary point of view on the derivative in the file `Deriv.lean`. The
derivative of polynomials is handled there, as it is naturally one-dimensional.

The simplifier is set up to prove automatically that some functions are differentiable, or
differentiable at a point (but not differentiable on a set or within a set at a point, as checking
automatically that the good domains are mapped one to the other when using composition is not
something the simplifier can easily do). This means that one can write
`example (x : ℝ) : Differentiable ℝ (fun x ↦ sin (exp (3 + x^2)) - 5 * cos x) := by simp`.
If there are divisions, one needs to supply to the simplifier proofs that the denominators do
not vanish, as in
```lean
example (x : ℝ) (h : 1 + sin x ≠ 0) : DifferentiableAt ℝ (fun x ↦ exp x / (1 + sin x)) x := by
  simp [h]
```
Of course, these examples only work once `exp`, `cos` and `sin` have been shown to be
differentiable, in `Mathlib/Analysis/SpecialFunctions/Trigonometric/Deriv.lean`.

The simplifier is not set up to compute the Fréchet derivative of maps (as these are in general
complicated multidimensional linear maps), but it will compute one-dimensional derivatives,
see `Deriv.lean`.

## Implementation details

For a discussion of the definitions and their rationale, see the file docstring of
`Mathlib.Analysis.Calculus.FDeriv.Defs`.

To make sure that the simplifier can prove automatically that functions are differentiable, we tag
many lemmas with the `simp` attribute, for instance those saying that the sum of differentiable
functions is differentiable, as well as their product, their Cartesian product, and so on. A notable
exception is the chain rule: we do not mark as a simp lemma the fact that, if `f` and `g` are
differentiable, then their composition also is: `simp` would always be able to match this lemma,
by taking `f` or `g` to be the identity. Instead, for every reasonable function (say, `exp`),
we add a lemma that if `f` is differentiable then so is `(fun x ↦ exp (f x))`. This means adding
some boilerplate lemmas, but these can also be useful in their own right.

## TODO

Generalize more results to topological vector spaces.

## Tags

derivative, differentiable, Fréchet, calculus

-/

public section

open Filter Asymptotics ContinuousLinearMap Set Topology NNReal

noncomputable section

section
section DerivativeUniqueness
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul 𝕜 E]
variable {F : Type*} [AddCommGroup F] [Module 𝕜 F]
  [TopologicalSpace F] [ContinuousAdd F] [ContinuousSMul 𝕜 F]

variable {f : E → F}
variable {f' f₁' : E →L[𝕜] F}
variable {x : E}
variable {s : Set E}

/-!
### Uniqueness of the derivative

In this section, we discuss the uniqueness of the derivative.
We prove that the definitions `UniqueDiffWithinAt` and `UniqueDiffOn` indeed imply the
uniqueness of the derivative. -/

/-- If a function f has a derivative f' at x, a rescaled version of f around x converges to f',
i.e., `n (f (x + (1/n) v) - f x)` converges to `f' v`. More generally, if `d n` tends to zero
and `c n * d n` tends to `v`, then `c n * (f (x + d n) - f x)` tends to `f' v`. This lemma expresses
this fact, for functions having a derivative within a set. Its specific formulation is useful for
tangent cone related discussions. -/
theorem HasFDerivWithinAt.lim (h : HasFDerivWithinAt f f' s x) {α : Type*} {l : Filter α}
    {c : α → 𝕜} {d : α → E} {v : E} (dlim : Tendsto d l (𝓝 0)) (dtop : ∀ᶠ n in l, x + d n ∈ s)
    (cdlim : Tendsto (fun n => c n • d n) l (𝓝 v)) :
    Tendsto (fun n => c n • (f (x + d n) - f x)) l (𝓝 (f' v)) := by
  have tendsto_arg : Tendsto (fun n => x + d n) l (𝓝[s] x) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨by simpa using tendsto_const_nhds.add dlim, dtop⟩
  have := calc
    (fun n ↦ c n • (f (x + d n) - f x) - f' (c n • d n)) =o[𝕜; l] fun n ↦ c n • d n := by
      simpa [smul_sub] using h.isLittleOTVS.comp_tendsto tendsto_arg |>.smul_left c
    _ =O[𝕜; l] (1 : α → 𝕜) := cdlim.isBigOTVS_one _
  rw [isLittleOTVS_one] at this
  simpa using this.add <| ((map_continuous f').tendsto v).comp cdlim

variable [T2Space F]

/-- If `f'` and `f₁'` are two derivatives of `f` within `s` at `x`, then they are equal on the
tangent cone to `s` at `x` -/
theorem HasFDerivWithinAt.unique_on (hf : HasFDerivWithinAt f f' s x)
    (hg : HasFDerivWithinAt f f₁' s x) : EqOn f' f₁' (tangentConeAt 𝕜 s x) := by
  intro y hy
  rcases exists_fun_of_mem_tangentConeAt hy with ⟨ι, l, hl, c, d, hd₀, hds, hcd⟩
  exact tendsto_nhds_unique (hf.lim hd₀ hds hcd) (hg.lim hd₀ hds hcd)

/-- `UniqueDiffWithinAt` achieves its goal: it implies the uniqueness of the derivative. -/
theorem UniqueDiffWithinAt.eq (H : UniqueDiffWithinAt 𝕜 s x) (hf : HasFDerivWithinAt f f' s x)
    (hg : HasFDerivWithinAt f f₁' s x) : f' = f₁' :=
  ContinuousLinearMap.ext_on H.1 (hf.unique_on hg)

theorem UniqueDiffOn.eq (H : UniqueDiffOn 𝕜 s) (hx : x ∈ s) (h : HasFDerivWithinAt f f' s x)
    (h₁ : HasFDerivWithinAt f f₁' s x) : f' = f₁' :=
  (H x hx).eq h h₁

/-- A coordinate embedding transports the usual sufficient condition for uniqueness of a
within-set derivative. No uniqueness is asserted without the tangent-domain hypothesis. -/
theorem HasFDerivWithinAt.unique_of_isEmbedding {D : Type*} [TopologicalSpace D]
    {f : D → F} {coord : D → E} {x : D} {s : Set D}
    (h₀ : HasFDerivWithinAt f f' s x coord) (h₁ : HasFDerivWithinAt f f₁' s x coord)
    (hcoord : IsEmbedding coord) (hxs : UniqueDiffWithinAt 𝕜 (coord '' s) (coord x)) :
    f' = f₁' := by
  let : ContinuousNeg F := ⟨by
    simpa only [neg_one_smul, Pi.neg_def, id_eq] using
      (continuous_id.const_smul (-1 : 𝕜) : Continuous fun y : F ↦ (-1 : 𝕜) • y)⟩
  let : IsTopologicalAddGroup F := { ‹ContinuousAdd F›, ‹ContinuousNeg F› with }
  let d : E →L[𝕜] F := f' - f₁'
  have hdiff : (fun y : D ↦ d (coord y - coord x)) =o[𝕜; 𝓝[s] x]
      (fun y ↦ coord y - coord x) := by
    simpa only [d, sub_apply, Pi.add_apply, Pi.neg_apply, ← sub_eq_add_neg, Pi.sub_def,
      sub_sub_sub_cancel_left] using h₁.isLittleOTVS.add h₀.isLittleOTVS.neg_left
  have hambient : (fun y : E ↦ d (y - coord x)) =o[𝕜; 𝓝[coord '' s] (coord x)]
      (fun y ↦ y - coord x) := by
    rw [← hcoord.map_nhdsWithin_eq s x, isLittleOTVS_map]
    exact hdiff
  have hzero : HasFDerivWithinAt (fun y : E ↦ d (y - coord x)) (0 : E →L[𝕜] F)
      (coord '' s) (coord x) := by
    apply HasFDerivWithinAt.of_isLittleOTVS
    simpa only [id_eq, sub_self, map_zero, zero_apply, sub_zero] using hambient
  have hself : HasFDerivWithinAt (fun y : E ↦ d (y - coord x)) d (coord '' s) (coord x) := by
    apply HasFDerivWithinAt.of_isLittleOTVS
    simpa only [id_eq, sub_self, map_zero, sub_zero, Pi.zero_def] using
      (IsLittleOTVS.zero (𝕜 := 𝕜) (fun y : E ↦ y - coord x) (𝓝[coord '' s] (coord x)))
  exact sub_eq_zero.mp (hxs.eq hself hzero)

/-- Local openness of the coordinate image suffices for uniqueness at the point. -/
theorem HasFDerivAt.unique_of_mem_nhds {D : Type*} [TopologicalSpace D] {f : D → F}
    {coord : D → E} {x : D} (h₀ : HasFDerivAt f f' x coord)
    (h₁ : HasFDerivAt f f₁' x coord) (hcoord : IsEmbedding coord)
    (hdom : range coord ∈ 𝓝 (coord x)) : f' = f₁' := by
  rw [HasFDerivAt, ← nhdsWithin_univ] at h₀ h₁
  apply HasFDerivWithinAt.unique_of_isEmbedding h₀ h₁ hcoord
  simpa only [image_univ] using uniqueDiffWithinAt_of_mem_nhds hdom

/-- Derivatives are unique in an open coordinate domain. The identity coordinates recover
ordinary uniqueness; this statement does not assert uniqueness on an arbitrary subset. -/
theorem HasFDerivAt.unique {D : Type*} [TopologicalSpace D] {f : D → F}
    {coord : D → E} {x : D} (h₀ : HasFDerivAt f f' x coord)
    (h₁ : HasFDerivAt f f₁' x coord)
    (hcoord : IsOpenEmbedding coord := by exact Topology.IsOpenEmbedding.id) : f' = f₁' :=
  h₀.unique_of_mem_nhds h₁ hcoord.isEmbedding
    (hcoord.isOpen_range.mem_nhds (mem_range_self x))

end DerivativeUniqueness

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
variable {F : Type*} [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]

variable {f : E → F}
variable {f' : E →L[𝕜] F}
variable {x : E}
variable {s t : Set E}
variable {L L₁ L₂ : Filter (E × E)}

section FDerivProperties

/-! ### Basic properties of the derivative -/

nonrec theorem HasFDerivAtFilter.mono {D : Type*} {f : D → F} {coord : D → E}
    {L₁ L₂ : Filter (D × D)} (h : HasFDerivAtFilter f f' L₂ coord) (hst : L₁ ≤ L₂) :
    HasFDerivAtFilter f f' L₁ coord :=
  .of_isLittleOTVS <| h.isLittleOTVS.mono hst

theorem HasFDerivWithinAt.mono_of_mem_nhdsWithin {D : Type*} [TopologicalSpace D] {f : D → F}
    {coord : D → E} {x : D} {s t : Set D}
    (h : HasFDerivWithinAt f f' t x coord) (hst : t ∈ 𝓝[s] x) :
    HasFDerivWithinAt f f' s x coord :=
  h.mono <| prod_mono_left _ (nhdsWithin_le_iff.mpr hst)

nonrec theorem HasFDerivWithinAt.mono {D : Type*} [TopologicalSpace D] {f : D → F} {coord : D → E}
    {x : D} {s t : Set D} (h : HasFDerivWithinAt f f' t x coord) (hst : s ⊆ t) :
    HasFDerivWithinAt f f' s x coord :=
  h.mono <| by gcongr

theorem HasFDerivAt.hasFDerivAtFilter {D : Type*} [TopologicalSpace D] {f : D → F} {coord : D → E}
    {x : D} {L : Filter (D × D)} (h : HasFDerivAt f f' x coord) (hL : L ≤ 𝓝 x ×ˢ pure x) :
    HasFDerivAtFilter f f' L coord :=
  h.mono hL

@[fun_prop]
theorem HasFDerivAt.hasFDerivWithinAt {D : Type*} [TopologicalSpace D] {f : D → F} {coord : D → E}
    {x : D} {s : Set D} (h : HasFDerivAt f f' x coord) : HasFDerivWithinAt f f' s x coord :=
  h.hasFDerivAtFilter <| prod_mono_left _ nhdsWithin_le_nhds

@[fun_prop]
theorem HasFDerivWithinAt.differentiableWithinAt {D : Type*} [TopologicalSpace D] {f : D → F}
    {coord : D → E} {x : D} {s : Set D} (h : HasFDerivWithinAt f f' s x coord) :
    DifferentiableWithinAt 𝕜 f s x coord :=
  ⟨f', h⟩

@[fun_prop]
theorem HasFDerivAt.differentiableAt {D : Type*} [TopologicalSpace D] {f : D → F} {coord : D → E}
    {x : D} (h : HasFDerivAt f f' x coord) : DifferentiableAt 𝕜 f x coord :=
  ⟨f', h⟩

@[simp]
theorem hasFDerivWithinAt_univ {D : Type*} [TopologicalSpace D] {f : D → F} {coord : D → E}
    {x : D} : HasFDerivWithinAt f f' univ x coord ↔ HasFDerivAt f f' x coord := by
  simp only [HasFDerivWithinAt, nhdsWithin_univ, HasFDerivAt]

alias ⟨HasFDerivWithinAt.hasFDerivAt_of_univ, _⟩ := hasFDerivWithinAt_univ

theorem differentiableWithinAt_univ {D : Type*} [TopologicalSpace D] {f : D → F} {coord : D → E}
    {x : D} : DifferentiableWithinAt 𝕜 f univ x coord ↔ DifferentiableAt 𝕜 f x coord := by
  simp only [DifferentiableWithinAt, hasFDerivWithinAt_univ, DifferentiableAt]

theorem fderiv_zero_of_not_differentiableAt (h : ¬DifferentiableAt 𝕜 f x) : fderiv 𝕜 f x = 0 := by
  rw [fderiv, fderivWithin_zero_of_not_differentiableWithinAt]
  rwa [differentiableWithinAt_univ]

theorem hasFDerivWithinAt_of_mem_nhds (h : s ∈ 𝓝 x) :
    HasFDerivWithinAt f f' s x ↔ HasFDerivAt f f' x := by
  rw [HasFDerivAt, HasFDerivWithinAt, nhdsWithin_eq_nhds.mpr h]

lemma hasFDerivWithinAt_of_isOpen (h : IsOpen s) (hx : x ∈ s) :
    HasFDerivWithinAt f f' s x ↔ HasFDerivAt f f' x :=
  hasFDerivWithinAt_of_mem_nhds (h.mem_nhds hx)

@[simp]
theorem hasFDerivWithinAt_insert_self :
    HasFDerivWithinAt f f' (insert x s) x ↔ HasFDerivWithinAt f f' s x := by
  simp_rw [hasFDerivWithinAt_iff_isLittleOTVS]
  apply isLittleOTVS_insert
  simp only [sub_self, map_zero]

protected alias ⟨_, HasFDerivWithinAt.insert⟩ := hasFDerivWithinAt_insert_self

theorem HasFDerivWithinAt.of_insert {y : E} (h : HasFDerivWithinAt f f' (insert y s) x) :
    HasFDerivWithinAt f f' s x :=
  h.mono <| subset_insert y s

@[simp]
theorem hasFDerivWithinAt_insert [T1Space E] {y : E} :
    HasFDerivWithinAt f f' (insert y s) x ↔ HasFDerivWithinAt f f' s x := by
  rcases eq_or_ne x y with (rfl | h)
  · apply hasFDerivWithinAt_insert_self
  · refine ⟨.of_insert, fun hf => hf.mono_of_mem_nhdsWithin ?_⟩
    simp_rw [nhdsWithin_insert_of_ne h, self_mem_nhdsWithin]

alias ⟨_, HasFDerivWithinAt.insert'⟩ := hasFDerivWithinAt_insert

@[simp]
theorem hasFDerivWithinAt_sdiff_singleton_self :
    HasFDerivWithinAt f f' (s \ {x}) x ↔ HasFDerivWithinAt f f' s x := by
  rw [← hasFDerivWithinAt_insert_self, insert_sdiff_singleton, hasFDerivWithinAt_insert_self]

@[deprecated (since := "2026-06-03")]
alias hasFDerivWithinAt_diff_singleton_self := hasFDerivWithinAt_sdiff_singleton_self

@[simp]
theorem hasFDerivWithinAt_sdiff_singleton [T1Space E] (y : E) :
    HasFDerivWithinAt f f' (s \ {y}) x ↔ HasFDerivWithinAt f f' s x := by
  rw [← hasFDerivWithinAt_insert, insert_sdiff_singleton, hasFDerivWithinAt_insert]

@[deprecated (since := "2026-06-03")]
alias hasFDerivWithinAt_diff_singleton := hasFDerivWithinAt_sdiff_singleton

@[simp]
protected theorem HasFDerivWithinAt.empty : HasFDerivWithinAt f f' ∅ x := by
  simp [HasFDerivWithinAt, hasFDerivAtFilter_iff_isLittleOTVS]

@[simp]
protected theorem DifferentiableWithinAt.empty : DifferentiableWithinAt 𝕜 f ∅ x :=
  ⟨0, .empty⟩

@[fun_prop]
theorem differentiableOn_empty : DifferentiableOn 𝕜 f ∅ := fun _ => False.elim

theorem HasFDerivWithinAt.of_finite [T1Space E] (h : s.Finite) : HasFDerivWithinAt f f' s x := by
  induction s, h using Set.Finite.induction_on with
  | empty => exact .empty
  | insert _ _ ih => exact ih.insert'

theorem DifferentiableWithinAt.of_finite [T1Space E] (h : s.Finite) :
    DifferentiableWithinAt 𝕜 f s x :=
  ⟨0, .of_finite h⟩

@[simp]
protected theorem HasFDerivWithinAt.singleton [T1Space E] {y} : HasFDerivWithinAt f f' {x} y :=
  .of_finite <| finite_singleton _

@[simp]
protected theorem DifferentiableWithinAt.singleton [T1Space E] {y} :
    DifferentiableWithinAt 𝕜 f {x} y :=
  ⟨0, .singleton⟩

theorem HasFDerivWithinAt.of_subsingleton [T1Space E] (h : s.Subsingleton) :
    HasFDerivWithinAt f f' s x :=
  .of_finite h.finite

theorem DifferentiableWithinAt.of_subsingleton [T1Space E] (h : s.Subsingleton) :
    DifferentiableWithinAt 𝕜 f s x :=
  .of_finite h.finite

@[fun_prop]
protected theorem HasStrictFDerivAt.hasFDerivAt {D : Type*} [TopologicalSpace D] {f : D → F}
    {coord : D → E} {x : D} (hf : HasStrictFDerivAt f f' x coord) :
    HasFDerivAt f f' x coord :=
  .of_isLittleOTVS <| by
    simpa only using! hf.isLittleOTVS.comp_tendsto (tendsto_id.prodMk_nhds tendsto_const_nhds)

protected theorem HasStrictFDerivAt.differentiableAt (hf : HasStrictFDerivAt f f' x) :
    DifferentiableAt 𝕜 f x :=
  hf.hasFDerivAt.differentiableAt

/-- Directional derivative agrees with `HasFDeriv`. -/
theorem HasFDerivAt.lim
    [ContinuousAdd E] [ContinuousSMul 𝕜 E] [ContinuousAdd F] [ContinuousSMul 𝕜 F]
    (hf : HasFDerivAt f f' x) (v : E) {α : Type*} {c : α → 𝕜} {l : Filter α}
    (hc : Tendsto (fun n => ‖c n‖) l atTop) :
    Tendsto (fun n : {n // c n ≠ 0} ↦
      c n • (f (x + Checked.inv (c n) n.2.isUnit • v) - f x))
      (comap Subtype.val l) (𝓝 (f' v)) := by
  refine (hasFDerivWithinAt_univ.2 hf).lim ?_ (.of_forall fun _ ↦ mem_univ _) ?_
  · have hunits : Tendsto (fun n : {n // c n ≠ 0} ↦
        n.2.isUnit.unit) (comap Subtype.val l)
        (comap (fun u : 𝕜ˣ ↦ (u : 𝕜)) (Bornology.cobounded 𝕜)) := by
      rw [tendsto_comap_iff]
      simpa only [Function.comp_def, IsUnit.unit_spec] using
        (tendsto_norm_atTop_iff_cobounded.mp hc).comp
          (tendsto_comap (f := (Subtype.val : {n // c n ≠ 0} → α)))
    simpa only [Function.comp_def, Checked.inv, zero_smul] using
      (tendsto_inv₀_cobounded.comp hunits).smul (tendsto_const_nhds (x := v))
  · simpa only [smul_smul, mul_inv_cancel₀, one_smul] using
      (tendsto_const_nhds (x := v) : Tendsto (fun _ : {n // c n ≠ 0} ↦ v)
        (comap Subtype.val l) (𝓝 v))

theorem hasFDerivWithinAt_inter' (h : t ∈ 𝓝[s] x) :
    HasFDerivWithinAt f f' (s ∩ t) x ↔ HasFDerivWithinAt f f' s x := by
  simp [HasFDerivWithinAt, nhdsWithin_restrict'' s h]

theorem hasFDerivWithinAt_inter (h : t ∈ 𝓝 x) :
    HasFDerivWithinAt f f' (s ∩ t) x ↔ HasFDerivWithinAt f f' s x := by
  simp [HasFDerivWithinAt, nhdsWithin_restrict' s h]

theorem HasFDerivWithinAt.union (hs : HasFDerivWithinAt f f' s x)
    (ht : HasFDerivWithinAt f f' t x) : HasFDerivWithinAt f f' (s ∪ t) x := by
  simp only [hasFDerivWithinAt_iff_isLittleOTVS, nhdsWithin_union] at *
  exact hs.sup ht

theorem HasFDerivWithinAt.hasFDerivAt (h : HasFDerivWithinAt f f' s x) (hs : s ∈ 𝓝 x) :
    HasFDerivAt f f' x := by
  rwa [← univ_inter s, hasFDerivWithinAt_inter hs, hasFDerivWithinAt_univ] at h

theorem DifferentiableWithinAt.differentiableAt (h : DifferentiableWithinAt 𝕜 f s x)
    (hs : s ∈ 𝓝 x) : DifferentiableAt 𝕜 f x :=
  h.imp fun _ hf' => hf'.hasFDerivAt hs

/-- A derivative of the restriction of a function to a neighborhood is a derivative of the
original function. The original domain and its coordinates need no vector-space structure. -/
theorem HasFDerivAt.of_restrict {D : Type*} [TopologicalSpace D] {f : D → F}
    {coord : D → E} {s : Set D} {x : s}
    (h : HasFDerivAt (fun y : s ↦ f y) f' x (fun y ↦ coord y))
    (hs : s ∈ 𝓝 (x : D)) : HasFDerivAt f f' (x : D) coord := by
  rw [hasFDerivAt_iff_isLittleOTVS, ← map_nhds_subtype_coe_eq_nhds x.property hs,
    isLittleOTVS_map]
  exact h.isLittleOTVS

/-- Differentiability can be checked after restricting the genuine function to a neighborhood. -/
theorem DifferentiableAt.of_restrict {D : Type*} [TopologicalSpace D] {f : D → F}
    {coord : D → E} {s : Set D} {x : s}
    (h : DifferentiableAt 𝕜 (fun y : s ↦ f y) x (fun y ↦ coord y))
    (hs : s ∈ 𝓝 (x : D)) : DifferentiableAt 𝕜 f (x : D) coord :=
  h.imp fun _ hf' ↦ hf'.of_restrict hs

/-- If `x` is isolated in `s`, then `f` has any derivative at `x` within `s`,
as this statement is empty. -/
theorem HasFDerivWithinAt.of_not_accPt (h : ¬AccPt x (𝓟 s)) :
    HasFDerivWithinAt f f' s x := by
  rw [accPt_principal_iff_nhdsWithin, not_neBot] at h
  rw [← hasFDerivWithinAt_sdiff_singleton_self, hasFDerivWithinAt_iff_isLittleOTVS, h]
  exact .bot

/-- If `x` is not in the closure of `s`, then `f` has any derivative at `x` within `s`,
as this statement is empty. -/
theorem HasFDerivWithinAt.of_notMem_closure (h : x ∉ closure s) : HasFDerivWithinAt f f' s x :=
  .of_not_accPt (h ·.clusterPt.mem_closure)

theorem fderivWithin_zero_of_not_accPt (h : ¬AccPt x (𝓟 s)) :
    fderivWithin 𝕜 f s x = 0 := by
  rw [fderivWithin, ite_eq_left (.of_not_accPt h)]

theorem fderivWithin_zero_of_notMem_closure (h : x ∉ closure s) :
    fderivWithin 𝕜 f s x = 0 :=
  fderivWithin_zero_of_not_accPt (h ·.clusterPt.mem_closure)

theorem fderivWithin_zero_of_not_uniqueDiffWithinAt {f : 𝕜 → F} {x : 𝕜} {s : Set 𝕜}
    (h : ¬UniqueDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 f s x = 0 :=
  fderivWithin_zero_of_not_accPt <| mt AccPt.uniqueDiffWithinAt h

theorem DifferentiableWithinAt.hasFDerivWithinAt {D : Type*} [TopologicalSpace D] {f : D → F}
    {coord : D → E} {x : D} {s : Set D} (h : DifferentiableWithinAt 𝕜 f s x coord) :
    HasFDerivWithinAt f (fderivWithin 𝕜 f s x coord) s x coord := by
  simp only [fderivWithin, dite_eq_left h]
  split_ifs with h₀
  exacts [h₀, Classical.choose_spec h]

theorem DifferentiableAt.hasFDerivAt {D : Type*} [TopologicalSpace D] {f : D → F} {coord : D → E}
    {x : D} (h : DifferentiableAt 𝕜 f x coord) :
    HasFDerivAt f (fderiv 𝕜 f x coord) x coord := by
  rw [fderiv, ← hasFDerivWithinAt_univ]
  rw [← differentiableWithinAt_univ] at h
  exact h.hasFDerivWithinAt

theorem DifferentiableOn.hasFDerivAt (h : DifferentiableOn 𝕜 f s) (hs : s ∈ 𝓝 x) :
    HasFDerivAt f (fderiv 𝕜 f x) x :=
  ((h x (mem_of_mem_nhds hs)).differentiableAt hs).hasFDerivAt

theorem DifferentiableOn.differentiableAt (h : DifferentiableOn 𝕜 f s) (hs : s ∈ 𝓝 x) :
    DifferentiableAt 𝕜 f x :=
  (h.hasFDerivAt hs).differentiableAt

theorem DifferentiableOn.eventually_differentiableAt (h : DifferentiableOn 𝕜 f s) (hs : s ∈ 𝓝 x) :
    ∀ᶠ y in 𝓝 x, DifferentiableAt 𝕜 f y :=
  (eventually_eventually_nhds.2 hs).mono fun _ => h.differentiableAt

/-- A valid local coordinate neighbourhood makes the existing derivative projection canonical. -/
theorem HasFDerivAt.fderiv_of_mem_nhds
    [ContinuousAdd E] [ContinuousSMul 𝕜 E] [ContinuousAdd F] [ContinuousSMul 𝕜 F] [T2Space F]
    {D : Type*} [TopologicalSpace D] {f : D → F} {coord : D → E} {x : D}
    (h : HasFDerivAt f f' x coord) (hcoord : IsEmbedding coord)
    (hdom : range coord ∈ 𝓝 (coord x)) : fderiv 𝕜 f x coord = f' :=
  (h.unique_of_mem_nhds h.differentiableAt.hasFDerivAt hcoord hdom).symm

protected theorem HasFDerivAt.fderiv
    [ContinuousAdd E] [ContinuousSMul 𝕜 E] [ContinuousAdd F] [ContinuousSMul 𝕜 F] [T2Space F]
    {D : Type*} [TopologicalSpace D] {f : D → F} {coord : D → E} {x : D}
    (h : HasFDerivAt f f' x coord)
    (hcoord : IsOpenEmbedding coord := by exact Topology.IsOpenEmbedding.id) :
    fderiv 𝕜 f x coord = f' :=
  (h.unique h.differentiableAt.hasFDerivAt hcoord).symm

theorem fderiv_eq
    [ContinuousAdd E] [ContinuousSMul 𝕜 E] [ContinuousAdd F] [ContinuousSMul 𝕜 F] [T2Space F]
    {f' : E → E →L[𝕜] F} (h : ∀ x, HasFDerivAt f (f' x) x) : fderiv 𝕜 f = f' :=
  funext fun x => (h x).fderiv

/-- The existing derivative projection equals any derivative proved to be unique on its domain.
This lemma uses no value from the nondifferentiable branch of the projection. -/
theorem HasFDerivWithinAt.fderivWithin_of_unique {D : Type*} [TopologicalSpace D]
    {f : D → F} {coord : D → E} {x : D} {s : Set D}
    (h : HasFDerivWithinAt f f' s x coord)
    (huniq : ∀ g : E →L[𝕜] F, HasFDerivWithinAt f g s x coord → g = f') :
    fderivWithin 𝕜 f s x coord = f' :=
  huniq _ h.differentiableWithinAt.hasFDerivWithinAt

protected theorem HasFDerivWithinAt.fderivWithin
    [ContinuousAdd E] [ContinuousSMul 𝕜 E] [ContinuousAdd F] [ContinuousSMul 𝕜 F] [T2Space F]
    (h : HasFDerivWithinAt f f' s x)
    (hxs : UniqueDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 f s x = f' :=
  (hxs.eq h h.differentiableWithinAt.hasFDerivWithinAt).symm

theorem DifferentiableWithinAt.mono (h : DifferentiableWithinAt 𝕜 f t x) (st : s ⊆ t) :
    DifferentiableWithinAt 𝕜 f s x := by
  rcases h with ⟨f', hf'⟩
  exact ⟨f', hf'.mono st⟩

theorem DifferentiableWithinAt.mono_of_mem_nhdsWithin
    (h : DifferentiableWithinAt 𝕜 f s x) {t : Set E} (hst : s ∈ 𝓝[t] x) :
    DifferentiableWithinAt 𝕜 f t x :=
  (h.hasFDerivWithinAt.mono_of_mem_nhdsWithin hst).differentiableWithinAt

theorem DifferentiableWithinAt.congr_nhds (h : DifferentiableWithinAt 𝕜 f s x) {t : Set E}
    (hst : 𝓝[s] x = 𝓝[t] x) : DifferentiableWithinAt 𝕜 f t x :=
  h.mono_of_mem_nhdsWithin <| hst ▸ self_mem_nhdsWithin

theorem differentiableWithinAt_congr_nhds {t : Set E} (hst : 𝓝[s] x = 𝓝[t] x) :
    DifferentiableWithinAt 𝕜 f s x ↔ DifferentiableWithinAt 𝕜 f t x :=
  ⟨fun h => h.congr_nhds hst, fun h => h.congr_nhds hst.symm⟩

theorem differentiableWithinAt_inter (ht : t ∈ 𝓝 x) :
    DifferentiableWithinAt 𝕜 f (s ∩ t) x ↔ DifferentiableWithinAt 𝕜 f s x := by
  simp only [DifferentiableWithinAt, hasFDerivWithinAt_inter ht]

theorem differentiableWithinAt_inter' (ht : t ∈ 𝓝[s] x) :
    DifferentiableWithinAt 𝕜 f (s ∩ t) x ↔ DifferentiableWithinAt 𝕜 f s x := by
  simp only [DifferentiableWithinAt, hasFDerivWithinAt_inter' ht]

theorem differentiableWithinAt_insert_self :
    DifferentiableWithinAt 𝕜 f (insert x s) x ↔ DifferentiableWithinAt 𝕜 f s x :=
  ⟨fun h ↦ h.mono (subset_insert x s), fun h ↦ h.hasFDerivWithinAt.insert.differentiableWithinAt⟩

protected alias ⟨_, DifferentiableWithinAt.insert⟩ := differentiableWithinAt_insert_self

theorem DifferentiableWithinAt.of_insert {y : E} (h : DifferentiableWithinAt 𝕜 f (insert y s) x) :
    DifferentiableWithinAt 𝕜 f s x :=
  h.mono <| subset_insert _ _

theorem differentiableWithinAt_insert [T1Space E] {y : E} :
    DifferentiableWithinAt 𝕜 f (insert y s) x ↔ DifferentiableWithinAt 𝕜 f s x := by
  simp only [DifferentiableWithinAt, hasFDerivWithinAt_insert]

alias ⟨_, DifferentiableWithinAt.insert'⟩ := differentiableWithinAt_insert

theorem DifferentiableAt.differentiableWithinAt (h : DifferentiableAt 𝕜 f x) :
    DifferentiableWithinAt 𝕜 f s x :=
  (differentiableWithinAt_univ.2 h).mono (subset_univ _)

@[fun_prop]
theorem Differentiable.differentiableAt (h : Differentiable 𝕜 f) : DifferentiableAt 𝕜 f x :=
  h x

protected theorem DifferentiableAt.fderivWithin
    [ContinuousAdd E] [ContinuousSMul 𝕜 E] [ContinuousAdd F] [ContinuousSMul 𝕜 F] [T2Space F]
    (h : DifferentiableAt 𝕜 f x)
    (hxs : UniqueDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 f s x = fderiv 𝕜 f x :=
  h.hasFDerivAt.hasFDerivWithinAt.fderivWithin hxs

theorem DifferentiableOn.mono (h : DifferentiableOn 𝕜 f t) (st : s ⊆ t) : DifferentiableOn 𝕜 f s :=
  fun x hx => (h x (st hx)).mono st

theorem differentiableOn_univ : DifferentiableOn 𝕜 f univ ↔ Differentiable 𝕜 f := by
  simp only [DifferentiableOn, Differentiable, differentiableWithinAt_univ, mem_univ,
    forall_true_left]

@[fun_prop]
theorem Differentiable.differentiableOn (h : Differentiable 𝕜 f) : DifferentiableOn 𝕜 f s :=
  (differentiableOn_univ.2 h).mono (subset_univ _)

theorem differentiableOn_of_locally_differentiableOn
    (h : ∀ x ∈ s, ∃ u, IsOpen u ∧ x ∈ u ∧ DifferentiableOn 𝕜 f (s ∩ u)) :
    DifferentiableOn 𝕜 f s := by
  intro x xs
  rcases h x xs with ⟨t, t_open, xt, ht⟩
  exact (differentiableWithinAt_inter (IsOpen.mem_nhds t_open xt)).1 (ht x ⟨xs, xt⟩)

theorem fderivWithin_of_mem_nhdsWithin
    [ContinuousAdd E] [ContinuousSMul 𝕜 E] [ContinuousAdd F] [ContinuousSMul 𝕜 F] [T2Space F]
    (st : t ∈ 𝓝[s] x) (ht : UniqueDiffWithinAt 𝕜 s x)
    (h : DifferentiableWithinAt 𝕜 f t x) : fderivWithin 𝕜 f s x = fderivWithin 𝕜 f t x :=
  ((DifferentiableWithinAt.hasFDerivWithinAt h).mono_of_mem_nhdsWithin st).fderivWithin ht

theorem fderivWithin_subset (st : s ⊆ t) (ht : UniqueDiffWithinAt 𝕜 s x)
    [ContinuousAdd E] [ContinuousSMul 𝕜 E] [ContinuousAdd F] [ContinuousSMul 𝕜 F] [T2Space F]
    (h : DifferentiableWithinAt 𝕜 f t x) : fderivWithin 𝕜 f s x = fderivWithin 𝕜 f t x :=
  fderivWithin_of_mem_nhdsWithin (nhdsWithin_mono _ st self_mem_nhdsWithin) ht h

set_option backward.isDefEq.respectTransparency false in
theorem fderivWithin_inter (ht : t ∈ 𝓝 x) : fderivWithin 𝕜 f (s ∩ t) x = fderivWithin 𝕜 f s x := by
  classical
  simp [fderivWithin, hasFDerivWithinAt_inter ht, DifferentiableWithinAt]

theorem fderivWithin_of_mem_nhds (h : s ∈ 𝓝 x) : fderivWithin 𝕜 f s x = fderiv 𝕜 f x := by
  rw [fderiv, ← univ_inter s, fderivWithin_inter h]

theorem fderivWithin_of_isOpen (hs : IsOpen s) (hx : x ∈ s) : fderivWithin 𝕜 f s x = fderiv 𝕜 f x :=
  fderivWithin_of_mem_nhds (hs.mem_nhds hx)

theorem fderivWithin_eq_fderiv
    [ContinuousAdd E] [ContinuousSMul 𝕜 E] [ContinuousAdd F] [ContinuousSMul 𝕜 F] [T2Space F]
    (hs : UniqueDiffWithinAt 𝕜 s x) (h : DifferentiableAt 𝕜 f x) :
    fderivWithin 𝕜 f s x = fderiv 𝕜 f x := by
  rw [fderiv]
  exact fderivWithin_subset (subset_univ _) hs h.differentiableWithinAt

theorem fderiv_mem_iff {f : E → F} {s : Set (E →L[𝕜] F)} {x : E} : fderiv 𝕜 f x ∈ s ↔
    DifferentiableAt 𝕜 f x ∧ fderiv 𝕜 f x ∈ s ∨ ¬DifferentiableAt 𝕜 f x ∧ (0 : E →L[𝕜] F) ∈ s := by
  by_cases hx : DifferentiableAt 𝕜 f x <;> simp [fderiv_zero_of_not_differentiableAt, *]

theorem fderivWithin_mem_iff {f : E → F} {t : Set E} {s : Set (E →L[𝕜] F)} {x : E} :
    fderivWithin 𝕜 f t x ∈ s ↔
      DifferentiableWithinAt 𝕜 f t x ∧ fderivWithin 𝕜 f t x ∈ s ∨
        ¬DifferentiableWithinAt 𝕜 f t x ∧ (0 : E →L[𝕜] F) ∈ s := by
  by_cases hx : DifferentiableWithinAt 𝕜 f t x <;>
    simp [fderivWithin_zero_of_not_differentiableWithinAt, *]

end FDerivProperties

/-! ### Being differentiable on a union of open sets can be tested on each set -/
section differentiableOn_union

/-- If a function is differentiable on two open sets, it is also differentiable on their union. -/
lemma DifferentiableOn.union_of_isOpen
    (hf : DifferentiableOn 𝕜 f s) (hf' : DifferentiableOn 𝕜 f t)
    (hs : IsOpen s) (ht : IsOpen t) :
    DifferentiableOn 𝕜 f (s ∪ t) := by
  intro x hx
  obtain (hx | hx) := hx
  · exact (hf x hx).differentiableAt (hs.mem_nhds hx) |>.differentiableWithinAt
  · exact (hf' x hx).differentiableAt (ht.mem_nhds hx) |>.differentiableWithinAt

/-- A function is differentiable on two open sets iff it is differentiable on their union. -/
lemma differentiableOn_union_iff_of_isOpen (hs : IsOpen s) (ht : IsOpen t) :
    DifferentiableOn 𝕜 f (s ∪ t) ↔ DifferentiableOn 𝕜 f s ∧ DifferentiableOn 𝕜 f t :=
  ⟨fun h ↦ ⟨h.mono subset_union_left, h.mono subset_union_right⟩,
    fun ⟨hfs, hft⟩ ↦ DifferentiableOn.union_of_isOpen hfs hft hs ht⟩

lemma differentiable_of_differentiableOn_union_of_isOpen (hf : DifferentiableOn 𝕜 f s)
    (hf' : DifferentiableOn 𝕜 f t) (hst : s ∪ t = univ) (hs : IsOpen s) (ht : IsOpen t) :
    Differentiable 𝕜 f := by
  rw [← differentiableOn_univ, ← hst]
  exact hf.union_of_isOpen hf' hs ht

/-- If a function is differentiable on open sets `s i`, it is differentiable on their union. -/
lemma DifferentiableOn.iUnion_of_isOpen {ι : Type*} {s : ι → Set E}
    (hf : ∀ i : ι, DifferentiableOn 𝕜 f (s i)) (hs : ∀ i, IsOpen (s i)) :
    DifferentiableOn 𝕜 f (⋃ i, s i) := by
  rintro x ⟨si, ⟨i, rfl⟩, hxsi⟩
  exact (hf i).differentiableAt ((hs i).mem_nhds hxsi) |>.differentiableWithinAt

/-- A function is differentiable on a union of open sets `s i`
iff it is differentiable on each `s i`. -/
lemma differentiableOn_iUnion_iff_of_isOpen {ι : Type*} {s : ι → Set E}
    (hs : ∀ i, IsOpen (s i)) :
    DifferentiableOn 𝕜 f (⋃ i, s i) ↔ ∀ i : ι, DifferentiableOn 𝕜 f (s i) :=
  ⟨fun h i ↦ h.mono <| subset_iUnion_of_subset i fun _ a ↦ a,
   fun h ↦ DifferentiableOn.iUnion_of_isOpen h hs⟩

lemma differentiable_of_differentiableOn_iUnion_of_isOpen {ι : Type*} {s : ι → Set E}
    (hf : ∀ i : ι, DifferentiableOn 𝕜 f (s i))
    (hs : ∀ i, IsOpen (s i)) (hs' : ⋃ i, s i = univ) :
    Differentiable 𝕜 f := by
  rw [← differentiableOn_univ, ← hs']
  exact DifferentiableOn.iUnion_of_isOpen hf hs

end differentiableOn_union

/-! ### Asymptotics, both spaces are TVS

In this section we prove big-O and little-O lemmas about differentiable functions
between two topological vector spaces.
-/
section Asymptotics
variable [ContinuousAdd F] [ContinuousSMul 𝕜 F]

theorem HasFDerivAtFilter.isBigOTVS_sub {D : Type*} {f : D → F} {coord : D → E}
    {L : Filter (D × D)} (hf : HasFDerivAtFilter f f' L coord) :
    (fun p => f p.1 - f p.2) =O[𝕜; L] fun p => coord p.1 - coord p.2 := by
  simpa using hf.isLittleOTVS.isBigOTVS.fun_add f'.isBigOTVS_comp

section Domain

variable {D : Type*} [TopologicalSpace D] {f : D → F} {coord : D → E}
  {x : D} {s : Set D}

theorem HasStrictFDerivAt.isBigOTVS_sub (hf : HasStrictFDerivAt f f' x coord) :
    (fun p : D × D => f p.1 - f p.2) =O[𝕜; 𝓝 (x, x)]
      fun p => coord p.1 - coord p.2 :=
  HasFDerivAtFilter.isBigOTVS_sub hf

theorem HasFDerivWithinAt.isBigOTVS_sub (h : HasFDerivWithinAt f f' s x coord) :
    (fun y ↦ f y - f x) =O[𝕜; 𝓝[s] x] (fun y ↦ coord y - coord x) :=
  (HasFDerivAtFilter.isBigOTVS_sub h).comp_tendsto prod_pure.ge

lemma DifferentiableWithinAt.isBigOTVS_sub (h : DifferentiableWithinAt 𝕜 f s x coord) :
    (fun y ↦ f y - f x) =O[𝕜; 𝓝[s] x] (fun y ↦ coord y - coord x) :=
  h.hasFDerivWithinAt.isBigOTVS_sub

theorem HasFDerivAt.isBigOTVS_sub (h : HasFDerivAt f f' x coord) :
    (fun y ↦ f y - f x) =O[𝕜; 𝓝 x] (fun y ↦ coord y - coord x) :=
  (HasFDerivAtFilter.isBigOTVS_sub h).comp_tendsto prod_pure.ge

theorem DifferentiableAt.isBigOTVS_sub (h : DifferentiableAt 𝕜 f x coord) :
    (fun y ↦ f y - f x) =O[𝕜; 𝓝 x] (fun y ↦ coord y - coord x) :=
  h.hasFDerivAt.isBigOTVS_sub

end Domain

end Asymptotics

section Continuous

/-! ### Deducing continuity from differentiability -/
variable [ContinuousAdd E] [ContinuousSMul 𝕜 E] [ContinuousAdd F] [ContinuousSMul 𝕜 F]

theorem HasFDerivAtFilter.tendsto_nhds {D : Type*} [TopologicalSpace D]
    {f : D → F} {coord : D → E} {x : D} {L : Filter D} (_hL : L ≤ 𝓝 x)
    (h : HasFDerivAtFilter f f' (L ×ˢ pure x) coord)
    (hcoord : Tendsto coord L (𝓝 (coord x)) := by
      first | exact Filter.tendsto_id | exact Filter.tendsto_id'.mpr (by assumption)) :
    Tendsto f L (𝓝 (f x)) := by
  have : (f · - f x) =o[𝕜; L] (1 : D → 𝕜) := by
    refine h.isBigOTVS_sub |>.comp_tendsto prod_pure.ge |>.trans_isLittleOTVS ?_
    rw [isLittleOTVS_one]
    simpa [sub_eq_add_neg] using! hcoord.add_const (-coord x)
  rw [isLittleOTVS_one] at this
  simpa using! this.add_const (f x)

theorem HasFDerivWithinAt.continuousWithinAt {D : Type*} [TopologicalSpace D]
    {f : D → F} {coord : D → E} {x : D} {s : Set D}
    (h : HasFDerivWithinAt f f' s x coord)
    (hcoord : ContinuousWithinAt coord s x := by exact continuousWithinAt_id) :
    ContinuousWithinAt f s x :=
  HasFDerivAtFilter.tendsto_nhds inf_le_left h hcoord

theorem HasFDerivAt.continuousAt {D : Type*} [TopologicalSpace D]
    {f : D → F} {coord : D → E} {x : D} (h : HasFDerivAt f f' x coord)
    (hcoord : ContinuousAt coord x := by exact continuousAt_id) : ContinuousAt f x :=
  HasFDerivAtFilter.tendsto_nhds le_rfl h hcoord

@[fun_prop]
theorem DifferentiableWithinAt.continuousWithinAt {D : Type*} [TopologicalSpace D]
    {f : D → F} {coord : D → E} {x : D} {s : Set D}
    (h : DifferentiableWithinAt 𝕜 f s x coord)
    (hcoord : ContinuousWithinAt coord s x := by exact continuousWithinAt_id) :
    ContinuousWithinAt f s x :=
  let ⟨_, hf'⟩ := h
  hf'.continuousWithinAt hcoord

@[fun_prop]
theorem DifferentiableAt.continuousAt {D : Type*} [TopologicalSpace D]
    {f : D → F} {coord : D → E} {x : D} (h : DifferentiableAt 𝕜 f x coord)
    (hcoord : ContinuousAt coord x := by exact continuousAt_id) : ContinuousAt f x :=
  let ⟨_, hf'⟩ := h
  hf'.continuousAt hcoord

@[fun_prop]
theorem DifferentiableOn.continuousOn {D : Type*} [TopologicalSpace D]
    {f : D → F} {coord : D → E} {s : Set D} (h : DifferentiableOn 𝕜 f s coord)
    (hcoord : ContinuousOn coord s := by exact continuousOn_id) : ContinuousOn f s :=
  fun x hx => (h x hx).continuousWithinAt (hcoord x hx)

@[fun_prop]
theorem Differentiable.continuous {D : Type*} [TopologicalSpace D]
    {f : D → F} {coord : D → E} (h : Differentiable 𝕜 f coord)
    (hcoord : Continuous coord := by exact continuous_id) : Continuous f :=
  continuous_iff_continuousAt.2 fun x => (h x).continuousAt hcoord.continuousAt

protected theorem HasStrictFDerivAt.continuousAt {D : Type*} [TopologicalSpace D]
    {f : D → F} {coord : D → E} {x : D} (hf : HasStrictFDerivAt f f' x coord)
    (hcoord : ContinuousAt coord x := by exact continuousAt_id) : ContinuousAt f x :=
  hf.hasFDerivAt.continuousAt hcoord

end Continuous

section id

/-! ### Derivative of the identity -/

theorem hasFDerivAtFilter_id (L : Filter (E × E)) : HasFDerivAtFilter id (.id 𝕜 E) L :=
  .of_isLittleOTVS <| (IsLittleOTVS.zero _ _).congr_left <| by simp

@[fun_prop]
theorem hasStrictFDerivAt_id (x : E) : HasStrictFDerivAt id (.id 𝕜 E) x :=
  hasFDerivAtFilter_id _

@[fun_prop]
theorem hasFDerivWithinAt_id (x : E) (s : Set E) : HasFDerivWithinAt id (.id 𝕜 E) s x :=
  hasFDerivAtFilter_id _

@[fun_prop]
theorem hasFDerivAt_id (x : E) : HasFDerivAt id (.id 𝕜 E) x :=
  hasFDerivAtFilter_id _

@[to_fun (attr := simp, fun_prop) differentiableAt_fun_id]
theorem differentiableAt_id : DifferentiableAt 𝕜 id x :=
  (hasFDerivAt_id x).differentiableAt

@[to_fun (attr := fun_prop) differentiableWithinAt_fun_id]
theorem differentiableWithinAt_id : DifferentiableWithinAt 𝕜 id s x :=
  differentiableAt_id.differentiableWithinAt

@[deprecated (since := "2026-05-17")]
alias differentiableWithinAt_id' := differentiableWithinAt_fun_id

@[to_fun (attr := simp, fun_prop) differentiable_fun_id]
theorem differentiable_id : Differentiable 𝕜 (id : E → E) := fun _ => differentiableAt_id

@[fun_prop]
theorem differentiableOn_id : DifferentiableOn 𝕜 id s :=
  differentiable_id.differentiableOn

@[to_fun (attr := simp) fderiv_fun_id]
theorem fderiv_id [ContinuousAdd E] [ContinuousSMul 𝕜 E] [T2Space E] : fderiv 𝕜 id x = .id 𝕜 E :=
  HasFDerivAt.fderiv (hasFDerivAt_id x)

@[deprecated (since := "2026-05-17")] alias fderiv_id' := fderiv_fun_id

@[to_fun fderivWithin_fun_id]
theorem fderivWithin_id [ContinuousAdd E] [ContinuousSMul 𝕜 E] [T2Space E]
    (hxs : UniqueDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 id s x = .id 𝕜 E := by
  rw [DifferentiableAt.fderivWithin differentiableAt_id hxs]
  exact fderiv_id

@[deprecated (since := "2026-05-17")] alias fderivWithin_id' := fderivWithin_fun_id

end id

end

section NormedCodomain
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable {f : E → F}
variable {f' : E →L[𝕜] F}
variable {x : E}
variable {s : Set E}
variable {L : Filter (E × E)}

theorem HasFDerivAtFilter.isEquivalent_sub (hf : HasFDerivAtFilter f f' L)
    (hf' : Topology.IsInducing f') :
    (fun p ↦ f p.1 - f p.2) ~[L] (fun p ↦ f' (p.1 - p.2)) := by
  rw [IsEquivalent, ← isLittleOTVS_iff_isLittleO (𝕜 := 𝕜)]
  exact hf.isLittleOTVS.trans_isBigOTVS <| f'.isThetaTVS_comp hf' |>.symm.isBigOTVS

theorem HasFDerivAtFilter.isThetaTVS_sub (hf : HasFDerivAtFilter f f' L)
    (hf' : Topology.IsInducing f') :
    (fun p ↦ f p.1 - f p.2) =Θ[𝕜; L] (fun p ↦ p.1 - p.2) :=
  hf.isEquivalent_sub hf' |>.isTheta.isThetaTVS.trans <| f'.isThetaTVS_comp hf'

theorem HasFDerivAt.isEquivalent_sub (hf : HasFDerivAt f f' x) (hf' : Topology.IsInducing f') :
    (f · - f x) ~[𝓝 x] (f' <| · - x) := by
  simpa using! HasFDerivAtFilter.isEquivalent_sub hf hf'

theorem HasFDerivAt.isThetaTVS_sub (hf : HasFDerivAt f f' x) (hf' : Topology.IsInducing f') :
    (f · - f x) =Θ[𝕜; 𝓝 x] (· - x) := by
  simpa [IsThetaTVS] using! HasFDerivAtFilter.isThetaTVS_sub hf hf'

theorem HasFDerivWithinAt.isEquivalent_sub (hf : HasFDerivWithinAt f f' s x)
    (hf' : Topology.IsInducing f') :
    (f · - f x) ~[𝓝[s] x] (f' <| · - x) := by
  simpa using! HasFDerivAtFilter.isEquivalent_sub hf hf'

theorem HasFDerivWithinAt.isThetaTVS_sub (hf : HasFDerivWithinAt f f' s x)
    (hf' : Topology.IsInducing f') :
    (f · - f x) =Θ[𝕜; 𝓝[s] x] (· - x) := by
  simpa [IsThetaTVS] using! HasFDerivAtFilter.isThetaTVS_sub hf hf'

theorem HasStrictFDerivAt.isEquivalent_sub (hf : HasStrictFDerivAt f f' x)
    (hf' : Topology.IsInducing f') :
    (fun p : E × E ↦ f p.1 - f p.2) ~[𝓝 (x, x)] (fun p ↦ f' (p.1 - p.2)) :=
  HasFDerivAtFilter.isEquivalent_sub hf hf'

theorem HasStrictFDerivAt.isThetaTVS_sub (hf : HasStrictFDerivAt f f' x)
    (hf' : Topology.IsInducing f') :
    (fun p : E × E ↦ f p.1 - f p.2) =Θ[𝕜; 𝓝 (x, x)] (fun p ↦ p.1 - p.2) :=
  HasFDerivAtFilter.isThetaTVS_sub hf hf'

end NormedCodomain

-- These lemmas won't generalize to Topological Vector Spaces, at least without changing the
-- statement.
section not_TVS
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable {f : E → F}
variable {f' : E →L[𝕜] F}
variable {x x₀ : E}
variable {s : Set E}
variable {L : Filter (E × E)}

/-- The normalized error is evaluated only at nonzero coordinate displacements. The hypothesis
records the error at zero displacements; it is automatic for identity coordinates. -/
theorem hasFDerivAtFilter_iff_tendsto {D : Type*} {f : D → F} {coord : D → E}
    {L : Filter (D × D)}
    (h₀ : ∀ᶠ p in L, coord p.1 = coord p.2 → f p.1 = f p.2 := by
      exact Filter.Eventually.of_forall fun p h ↦ congrArg _ h) :
    HasFDerivAtFilter f f' L coord ↔
      Tendsto (fun p : {p : D × D // coord p.1 - coord p.2 ≠ 0} ↦
        Checked.div ‖f p.1.1 - f p.1.2 - f' (coord p.1.1 - coord p.1.2)‖
          ‖coord p.1.1 - coord p.1.2‖ (norm_ne_zero_iff.mpr p.2).isUnit)
        (comap Subtype.val L) (𝓝 0) := by
  rw [hasFDerivAtFilter_iff_isLittleO, ← isLittleO_norm_left, ← isLittleO_norm_right]
  have hz : ∀ᶠ p in L, ‖coord p.1 - coord p.2‖ = 0 →
      ‖f p.1 - f p.2 - f' (coord p.1 - coord p.2)‖ = 0 := by
    filter_upwards [h₀] with p hp h
    have hc : coord p.1 = coord p.2 := sub_eq_zero.mp (norm_eq_zero.mp h)
    simp only [hc, hp hc, sub_self, map_zero, norm_zero]
  refine (isLittleO_iff_tendsto' hz).trans ⟨?_, ?_⟩
  · intro h
    let q : {p : D × D // coord p.1 - coord p.2 ≠ 0} →
        {p : D × D // ‖coord p.1 - coord p.2‖ ≠ 0} :=
      fun p ↦ ⟨p, norm_ne_zero_iff.mpr p.2⟩
    have hq : Tendsto q (comap Subtype.val L) (comap Subtype.val L) :=
      tendsto_comap_iff.mpr tendsto_comap
    exact (h.comp hq).congr fun p ↦ rfl
  · intro h
    let q : {p : D × D // ‖coord p.1 - coord p.2‖ ≠ 0} →
        {p : D × D // coord p.1 - coord p.2 ≠ 0} :=
      fun p ↦ ⟨p, norm_ne_zero_iff.mp p.2⟩
    have hq : Tendsto q (comap Subtype.val L) (comap Subtype.val L) :=
      tendsto_comap_iff.mpr tendsto_comap
    exact (h.comp hq).congr fun p ↦ rfl

/-- The within-set derivative is characterized by its normalized error on the actual
nonzero-displacement domain, together with compatibility on coordinate fibers. -/
theorem hasFDerivWithinAt_iff_tendsto {D : Type*} [TopologicalSpace D] {f : D → F}
    {coord : D → E} {s : Set D} {x : D}
    (h₀ : ∀ᶠ y in 𝓝[s] x, coord y = coord x → f y = f x := by
      exact Filter.Eventually.of_forall fun y h ↦ congrArg _ h) :
    HasFDerivWithinAt f f' s x coord ↔
      Tendsto (fun y : {y : D // coord y - coord x ≠ 0} ↦
        Checked.div ‖f y - f x - f' (coord y - coord x)‖
          ‖coord y - coord x‖ (norm_ne_zero_iff.mpr y.2).isUnit)
        (comap Subtype.val (𝓝[s] x)) (𝓝 0) := by
  rw [hasFDerivWithinAt_iff_isLittleO, ← isLittleO_norm_left, ← isLittleO_norm_right]
  have hz : ∀ᶠ y in 𝓝[s] x, ‖coord y - coord x‖ = 0 →
      ‖f y - f x - f' (coord y - coord x)‖ = 0 := by
    filter_upwards [h₀] with y hy h
    have hc : coord y = coord x := sub_eq_zero.mp (norm_eq_zero.mp h)
    simp only [hc, hy hc, sub_self, map_zero, norm_zero]
  refine (isLittleO_iff_tendsto' hz).trans ⟨?_, ?_⟩
  · intro h
    let q : {y : D // coord y - coord x ≠ 0} →
        {y : D // ‖coord y - coord x‖ ≠ 0} :=
      fun y ↦ ⟨y, norm_ne_zero_iff.mpr y.2⟩
    have hq : Tendsto q (comap Subtype.val (𝓝[s] x))
        (comap Subtype.val (𝓝[s] x)) := tendsto_comap_iff.mpr tendsto_comap
    exact (h.comp hq).congr fun y ↦ rfl
  · intro h
    let q : {y : D // ‖coord y - coord x‖ ≠ 0} →
        {y : D // coord y - coord x ≠ 0} :=
      fun y ↦ ⟨y, norm_ne_zero_iff.mp y.2⟩
    have hq : Tendsto q (comap Subtype.val (𝓝[s] x))
        (comap Subtype.val (𝓝[s] x)) := tendsto_comap_iff.mpr tendsto_comap
    exact (h.comp hq).congr fun y ↦ rfl

/-- The normalized-error characterization uses only nonzero coordinate displacements and
retains the required agreement of function values on zero-displacement fibers. -/
theorem hasFDerivAt_iff_tendsto {D : Type*} [TopologicalSpace D] {f : D → F}
    {coord : D → E} {x : D}
    (h₀ : ∀ᶠ y in 𝓝 x, coord y = coord x → f y = f x := by
      exact Filter.Eventually.of_forall fun y h ↦ congrArg _ h) :
    HasFDerivAt f f' x coord ↔
      Tendsto (fun y : {y : D // coord y - coord x ≠ 0} ↦
        Checked.div ‖f y - f x - f' (coord y - coord x)‖
          ‖coord y - coord x‖ (norm_ne_zero_iff.mpr y.2).isUnit)
        (comap Subtype.val (𝓝 x)) (𝓝 0) := by
  simpa only [hasFDerivWithinAt_univ, nhdsWithin_univ] using
    (hasFDerivWithinAt_iff_tendsto (f := f) (f' := f') (s := univ) (x := x)
      (coord := coord) (by simpa only [nhdsWithin_univ] using h₀))

theorem hasFDerivAt_iff_isLittleO_nhds_zero :
    HasFDerivAt f f' x ↔ (fun h : E => f (x + h) - f x - f' h) =o[𝓝 0] fun h => h := by
  rw [hasFDerivAt_iff_isLittleO, ← map_add_left_nhds_zero x, isLittleO_map]
  simp [Function.comp_def]

theorem HasFDerivAtFilter.isBigO_sub {D : Type*} {f : D → F} {coord : D → E}
    {L : Filter (D × D)} (h : HasFDerivAtFilter f f' L coord) :
    (fun p => f p.1 - f p.2) =O[L] fun p => coord p.1 - coord p.2 :=
  h.isBigOTVS_sub.isBigO

section Domain

variable {D : Type*} [TopologicalSpace D] {f : D → F} {coord : D → E}
  {x₀ : D} {s : Set D}

theorem HasStrictFDerivAt.isBigO_sub (hf : HasStrictFDerivAt f f' x₀ coord) :
    (fun p : D × D => f p.1 - f p.2) =O[𝓝 (x₀, x₀)]
      fun p => coord p.1 - coord p.2 :=
  hf.isBigOTVS_sub.isBigO

theorem HasFDerivWithinAt.isBigO_sub (h : HasFDerivWithinAt f f' s x₀ coord) :
    (fun y ↦ f y - f x₀) =O[𝓝[s] x₀] (fun y ↦ coord y - coord x₀) :=
  h.isBigOTVS_sub.isBigO

lemma DifferentiableWithinAt.isBigO_sub (h : DifferentiableWithinAt 𝕜 f s x₀ coord) :
    (fun y ↦ f y - f x₀) =O[𝓝[s] x₀] (fun y ↦ coord y - coord x₀) :=
  h.hasFDerivWithinAt.isBigO_sub

theorem HasFDerivAt.isBigO_sub (h : HasFDerivAt f f' x₀ coord) :
    (fun y ↦ f y - f x₀) =O[𝓝 x₀] (fun y ↦ coord y - coord x₀) :=
  h.isBigOTVS_sub.isBigO

theorem DifferentiableAt.isBigO_sub (h : DifferentiableAt 𝕜 f x₀ coord) :
    (fun y ↦ f y - f x₀) =O[𝓝 x₀] (fun y ↦ coord y - coord x₀) :=
  h.hasFDerivAt.isBigO_sub

end Domain

theorem Asymptotics.IsBigO.hasFDerivWithinAt {n : ℕ}
    (h : f =O[𝓝[s] x₀] fun x => ‖x - x₀‖ ^ n) (hx₀ : x₀ ∈ s) (hn : 1 < n) :
    HasFDerivWithinAt f (0 : E →L[𝕜] F) s x₀ := by
  apply HasFDerivWithinAt.of_isLittleO
  simpa only [id_eq, h.eq_zero_of_norm_pow_within hx₀ hn.ne_bot, zero_apply, sub_zero] using
    h.trans_isLittleO ((isLittleO_pow_sub_sub x₀ hn).mono nhdsWithin_le_nhds)

theorem Asymptotics.IsBigO.hasFDerivAt {x₀ : E} {n : ℕ} (h : f =O[𝓝 x₀] fun x => ‖x - x₀‖ ^ n)
    (hn : 1 < n) : HasFDerivAt f (0 : E →L[𝕜] F) x₀ := by
  rw [← nhdsWithin_univ] at h
  exact (h.hasFDerivWithinAt (mem_univ _) hn).hasFDerivAt_of_univ

theorem HasStrictFDerivAt.isTheta_sub (hf : HasStrictFDerivAt f f' x)
    (hf' : Topology.IsInducing f') :
    (fun p : E × E ↦ f p.1 - f p.2) =Θ[𝓝 (x, x)] (fun p ↦ p.1 - p.2) :=
  hf.isThetaTVS_sub hf' |>.isTheta

theorem HasFDerivAtFilter.isTheta_sub (hf : HasFDerivAtFilter f f' L)
    (hf' : Topology.IsInducing f') :
    (fun p ↦ f p.1 - f p.2) =Θ[L] (fun p ↦ p.1 - p.2) :=
  hf.isThetaTVS_sub hf' |>.isTheta

theorem HasFDerivWithinAt.isTheta_sub (hf : HasFDerivWithinAt f f' s x)
    (hf' : Topology.IsInducing f') :
    (f · - f x) =Θ[𝓝[s] x] (· - x) :=
  hf.isThetaTVS_sub hf' |>.isTheta

theorem HasFDerivAt.isTheta_sub (hf : HasFDerivAt f f' x) (hf' : Topology.IsInducing f') :
    (f · - f x) =Θ[𝓝 x] (· - x) :=
  hf.isThetaTVS_sub hf' |>.isTheta

section Lipschitz
/-! ### Estimates on the norm of the derivative vs Lipschitz-like estimates on `f` -/

/-- If `f` is strictly differentiable at `x` with derivative `f'` and `K > ‖f'‖₊`, then `f` is
`K`-Lipschitz in a neighborhood of `x`. -/
theorem HasStrictFDerivAt.exists_lipschitzOnWith_of_nnnorm_lt (hf : HasStrictFDerivAt f f' x)
    (K : ℝ≥0) (hK : ‖f'‖₊ < K) : ∃ s ∈ 𝓝 x, LipschitzOnWith K f s := by
  have := hf.isLittleO.add_isBigOWith (f'.isBigOWith_comp _ _) hK
  simp only [sub_add_cancel, IsBigOWith] at this
  rcases exists_nhds_square this with ⟨U, Uo, xU, hU⟩
  exact
    ⟨U, Uo.mem_nhds xU, lipschitzOnWith_iff_norm_sub_le.2 fun x hx y hy => hU (mk_mem_prod hx hy)⟩

/-- If `f` is strictly differentiable at `x` with derivative `f'`, then `f` is Lipschitz in a
neighborhood of `x`. See also `HasStrictFDerivAt.exists_lipschitzOnWith_of_nnnorm_lt` for a
more precise statement. -/
theorem HasStrictFDerivAt.exists_lipschitzOnWith (hf : HasStrictFDerivAt f f' x) :
    ∃ K, ∃ s ∈ 𝓝 x, LipschitzOnWith K f s :=
  (exists_gt _).imp hf.exists_lipschitzOnWith_of_nnnorm_lt

/-- Converse to the mean value inequality: if `f` is differentiable at `x₀` and `C`-lipschitz
on a neighborhood of `x₀` then its derivative at `x₀` has norm bounded by `C`. This version
only assumes that `‖f x - f x₀‖ ≤ C * ‖x - x₀‖` in a neighborhood of `x`. -/
theorem HasFDerivAt.le_of_lip' {f : E → F} {f' : E →L[𝕜] F} {x₀ : E} (hf : HasFDerivAt f f' x₀)
    {C : ℝ} (hC₀ : 0 ≤ C) (hlip : ∀ᶠ x in 𝓝 x₀, ‖f x - f x₀‖ ≤ C * ‖x - x₀‖) : ‖f'‖ ≤ C := by
  refine le_of_forall_pos_le_add fun ε ε0 => opNorm_le_of_nhds_zero ?_ ?_
  · exact add_nonneg hC₀ ε0.le
  rw [← map_add_left_nhds_zero x₀, eventually_map] at hlip
  filter_upwards [isLittleO_iff.1 (hasFDerivAt_iff_isLittleO_nhds_zero.1 hf) ε0, hlip] with y hy hyC
  rw [add_sub_cancel_left] at hyC
  calc
    ‖f' y‖ ≤ ‖f (x₀ + y) - f x₀‖ + ‖f (x₀ + y) - f x₀ - f' y‖ := norm_le_insert _ _
    _ ≤ C * ‖y‖ + ε * ‖y‖ := add_le_add hyC hy
    _ = (C + ε) * ‖y‖ := (add_mul _ _ _).symm

/-- Converse to the mean value inequality: if `f` is differentiable at `x₀` and `C`-lipschitz
on a neighborhood of `x₀` then its derivative at `x₀` has norm bounded by `C`. -/
theorem HasFDerivAt.le_of_lipschitzOn
    {f : E → F} {f' : E →L[𝕜] F} {x₀ : E} (hf : HasFDerivAt f f' x₀)
    {s : Set E} (hs : s ∈ 𝓝 x₀) {C : ℝ≥0} (hlip : LipschitzOnWith C f s) : ‖f'‖ ≤ C := by
  refine hf.le_of_lip' C.coe_nonneg ?_
  filter_upwards [hs] with x hx using hlip.norm_sub_le hx (mem_of_mem_nhds hs)

/-- Converse to the mean value inequality: if `f` is differentiable at `x₀` and `C`-lipschitz
then its derivative at `x₀` has norm bounded by `C`. -/
theorem HasFDerivAt.le_of_lipschitz {f : E → F} {f' : E →L[𝕜] F} {x₀ : E} (hf : HasFDerivAt f f' x₀)
    {C : ℝ≥0} (hlip : LipschitzWith C f) : ‖f'‖ ≤ C :=
  hf.le_of_lipschitzOn univ_mem (lipschitzOnWith_univ.2 hlip)

variable (𝕜)

/-- Converse to the mean value inequality: if `f` is `C`-lipschitz
on a neighborhood of `x₀` then its derivative at `x₀` has norm bounded by `C`. This version
only assumes that `‖f x - f x₀‖ ≤ C * ‖x - x₀‖` in a neighborhood of `x`. -/
theorem norm_fderiv_le_of_lip' {f : E → F} {x₀ : E}
    {C : ℝ} (hC₀ : 0 ≤ C) (hlip : ∀ᶠ x in 𝓝 x₀, ‖f x - f x₀‖ ≤ C * ‖x - x₀‖) :
    ‖fderiv 𝕜 f x₀‖ ≤ C := by
  by_cases hf : DifferentiableAt 𝕜 f x₀
  · exact hf.hasFDerivAt.le_of_lip' hC₀ hlip
  · rw [fderiv_zero_of_not_differentiableAt hf]
    simp [hC₀]

/-- Converse to the mean value inequality: if `f` is `C`-lipschitz
on a neighborhood of `x₀` then its derivative at `x₀` has norm bounded by `C`.
Version using `fderiv`. -/
theorem norm_fderiv_le_of_lipschitzOn {f : E → F} {x₀ : E} {s : Set E} (hs : s ∈ 𝓝 x₀)
    {C : ℝ≥0} (hlip : LipschitzOnWith C f s) : ‖fderiv 𝕜 f x₀‖ ≤ C := by
  refine norm_fderiv_le_of_lip' 𝕜 C.coe_nonneg ?_
  filter_upwards [hs] with x hx using hlip.norm_sub_le hx (mem_of_mem_nhds hs)

/-- Converse to the mean value inequality: if `f` is `C`-lipschitz then
its derivative at `x₀` has norm bounded by `C`.
Version using `fderiv`. -/
theorem norm_fderiv_le_of_lipschitz {f : E → F} {x₀ : E}
    {C : ℝ≥0} (hlip : LipschitzWith C f) : ‖fderiv 𝕜 f x₀‖ ≤ C :=
  norm_fderiv_le_of_lipschitzOn 𝕜 univ_mem (lipschitzOnWith_univ.2 hlip)

end Lipschitz

end not_TVS

section Semilinear
/-!
## Results involving semilinear maps
-/
variable {𝕜 V V' W W' : Type*} [NontriviallyNormedField 𝕜] {σ σ' : RingHom 𝕜 𝕜}
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedAddCommGroup V'] [NormedSpace 𝕜 V']
  [NormedAddCommGroup W] [NormedSpace 𝕜 W] [NormedAddCommGroup W'] [NormedSpace 𝕜 W']
  [RingHomIsometric σ] [RingHomInvPair σ σ'] (L : W →SL[σ] W') (R : V' →SL[σ'] V)

/-- If `L` and `R` are semilinear maps whose composite is linear, and `f` has Fréchet derivative
`f'` at `R z`, then `L ∘ f ∘ R` has Fréchet derivative `L ∘ f' ∘ R` at `z`. -/
lemma HasFDerivAt.comp_semilinear {f : V → W} {z : V'} {f' : V →L[𝕜] W}
    (hf : HasFDerivAt f f' (R z)) : HasFDerivAt (L ∘ f ∘ R) (L.comp (f'.comp R)) z := by
  have : RingHomIsometric σ' := .inv σ
  rw [hasFDerivAt_iff_isLittleO_nhds_zero] at ⊢ hf
  have := hf.comp_tendsto (R.map_zero ▸ R.continuous.continuousAt.tendsto)
  simpa using ((L.isBigO_comp _ _).trans_isLittleO this).trans_isBigO (R.isBigO_id _)

/-- If `L` and `R` are semilinear maps whose composite is linear, and `f` is differentiable at
`R z`, then `L ∘ f ∘ R` is differentiable at `z`. -/
lemma DifferentiableAt.comp_semilinear₂ {f : V → W} {z : V'} (hf : DifferentiableAt 𝕜 f (R z)) :
    DifferentiableAt 𝕜 (L ∘ f ∘ R) z := by
  simpa using (hf.hasFDerivAt.comp_semilinear L R).differentiableAt

end Semilinear
