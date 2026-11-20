/-
Copyright (c) 2023 Ziyu Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ziyu Wang, Chenyi Li, Sébastien Gouëzel, Penghao Yu, Zhipeng Cao
-/
module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Gradient

## Main Definitions

Let `f` be a function from a domain `D` with coordinates in a Hilbert space `F` to `𝕜`
(`𝕜` is `ℝ` or `ℂ`), `x` be a point in `D`, and `f'` be a vector in `F`. Identity coordinates
recover functions on `F`. Then

  `HasGradientWithinAt f f' s x`

says that `f` has a gradient `f'` at `x`, where the domain of interest
is restricted to `s`. We also have

  `HasGradientAt f f' x := HasGradientWithinAt f f' univ x`

## Main results

This file develops the following aspects of the theory of gradients:
* definitions of gradients, both within a set and on the whole space.
* translating between `HasGradientAtFilter` and `HasFDerivAtFilter`,
  `HasGradientWithinAt` and `HasFDerivWithinAt`, `HasGradientAt` and `HasFDerivAt`,
  `gradient` and `fderiv`.
* uniqueness of gradients.
* translating between `HasGradientAtFilter` and `HasDerivAtFilter`,
  `HasGradientAt` and `HasDerivAt`, `gradient` and `deriv` when `F = 𝕜`.
* the theorems about the inner product of the gradient.
* the congruence of the gradient.
* the gradient of constant functions.
* the continuity of a function admitting a gradient.
-/

@[expose] public section

@[expose] public section

open InnerProductSpace Function Set

open scoped ComplexConjugate Topology

noncomputable section

variable {𝕜 F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {f : F → 𝕜} {f' x y : F}

/-- A function `f` has the gradient `f'` as derivative along the filter `L` if
  `f x' = f x + ⟨f', coord x' - coord x⟩ + o (coord x' - coord x)` when `x'` converges
along the filter `L`. -/
def HasGradientAtFilter {D : Type*} (f : D → 𝕜) (f' : F) (x : D) (L : Filter D)
    (coord : D → F := by exact _root_.id) :=
  HasFDerivAtFilter f (toDual 𝕜 F f') (L ×ˢ pure x) coord

/-- `f` has the gradient `f'` at the point `x` within the subset `s` if
  `f x' = f x + ⟨f', coord x' - coord x⟩ + o (coord x' - coord x)` where `x'` converges
to `x` inside `s`. -/
def HasGradientWithinAt {D : Type*} [TopologicalSpace D] (f : D → 𝕜) (f' : F)
    (s : Set D) (x : D) (coord : D → F := by exact _root_.id) :=
  HasGradientAtFilter f f' x (𝓝[s] x) coord

/-- `f` has the gradient `f'` at the point `x` if
  `f x' = f x + ⟨f', coord x' - coord x⟩ + o (coord x' - coord x)` where `x'` converges
to `x`. -/
def HasGradientAt {D : Type*} [TopologicalSpace D] (f : D → 𝕜) (f' : F) (x : D)
    (coord : D → F := by exact _root_.id) :=
  HasGradientAtFilter f f' x (𝓝 x) coord

/-- Gradient of `f` at the point `x` within the set `s`, if it exists.  Zero otherwise.

If the derivative exists (i.e., `∃ f', HasGradientWithinAt f f' s x`), then
`f x' = f x + ⟨f', x' - x⟩ + o (x' - x)` where `x'` converges to `x` inside `s`. -/
def gradientWithin (f : F → 𝕜) (s : Set F) (x : F) : F :=
  (toDual 𝕜 F).symm (fderivWithin 𝕜 f s x)

/-- Gradient of `f` at the point `x`, if it exists.  Zero otherwise.
Denoted as `∇` within the Gradient namespace.

If the derivative exists (i.e., `∃ f', HasGradientAt f f' x`), then
`f x' = f x + ⟨f', x' - x⟩ + o (x' - x)` where `x'` converges to `x`. -/
def gradient (f : F → 𝕜) (x : F) : F :=
  (toDual 𝕜 F).symm (fderiv 𝕜 f x)

@[inherit_doc]
scoped[Gradient] notation "∇" => gradient

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

open scoped Gradient

variable {s : Set F} {L : Filter F}

section Domain

variable {D : Type*} [TopologicalSpace D] {f : D → 𝕜} {coord : D → F}
  {s : Set D} {x : D}

theorem hasGradientWithinAt_iff_hasFDerivWithinAt :
    HasGradientWithinAt f f' s x coord ↔ HasFDerivWithinAt f (toDual 𝕜 F f') s x coord :=
  Iff.rfl

theorem hasFDerivWithinAt_iff_hasGradientWithinAt {frechet : StrongDual 𝕜 F} :
    HasFDerivWithinAt f frechet s x coord ↔
      HasGradientWithinAt f ((toDual 𝕜 F).symm frechet) s x coord := by
  rw [hasGradientWithinAt_iff_hasFDerivWithinAt, (toDual 𝕜 F).apply_symm_apply frechet]

theorem hasGradientAt_iff_hasFDerivAt :
    HasGradientAt f f' x coord ↔ HasFDerivAt f (toDual 𝕜 F f') x coord :=
  Iff.rfl

theorem hasFDerivAt_iff_hasGradientAt {frechet : StrongDual 𝕜 F} :
    HasFDerivAt f frechet x coord ↔ HasGradientAt f ((toDual 𝕜 F).symm frechet) x coord := by
  rw [hasGradientAt_iff_hasFDerivAt, (toDual 𝕜 F).apply_symm_apply frechet]

alias ⟨HasGradientWithinAt.hasFDerivWithinAt, _⟩ := hasGradientWithinAt_iff_hasFDerivWithinAt

alias ⟨HasFDerivWithinAt.hasGradientWithinAt, _⟩ := hasFDerivWithinAt_iff_hasGradientWithinAt

alias ⟨HasGradientAt.hasFDerivAt, _⟩ := hasGradientAt_iff_hasFDerivAt

alias ⟨HasFDerivAt.hasGradientAt, _⟩ := hasFDerivAt_iff_hasGradientAt

end Domain

theorem gradient_eq_zero_of_not_differentiableAt (h : ¬DifferentiableAt 𝕜 f x) : ∇ f x = 0 := by
  rw [gradient, fderiv_zero_of_not_differentiableAt h, map_zero]

@[simp]
lemma toDual_gradientWithin :
    (toDual 𝕜 F) (gradientWithin f s x) = fderivWithin 𝕜 f s x := by
  rw [gradientWithin, (toDual 𝕜 F).apply_symm_apply]

@[simp]
lemma toDual_gradient : (toDual 𝕜 F) (∇ f x) = fderiv 𝕜 f x := by
  rw [gradient, (toDual 𝕜 F).apply_symm_apply]

@[simp]
lemma toDual_comp_gradientWithin :
    (toDual 𝕜 F) ∘ gradientWithin f s = fderivWithin 𝕜 f s :=
  funext fun _ => toDual_gradientWithin

@[simp]
lemma toDual_comp_gradient : (toDual 𝕜 F) ∘ ∇ f = fderiv 𝕜 f :=
  funext fun _ => toDual_gradient

theorem HasGradientAt.unique {gradf gradg : F}
    (hf : HasGradientAt f gradf x) (hg : HasGradientAt f gradg x) :
    gradf = gradg :=
  (toDual 𝕜 F).injective (hf.hasFDerivAt.unique hg.hasFDerivAt)

theorem DifferentiableAt.hasGradientAt (h : DifferentiableAt 𝕜 f x) :
    HasGradientAt f (∇ f x) x := by
  simpa [hasGradientAt_iff_hasFDerivAt] using h.hasFDerivAt

theorem HasGradientAt.differentiableAt {D : Type*} [TopologicalSpace D]
    {f : D → 𝕜} {coord : D → F} {x : D} (h : HasGradientAt f f' x coord) :
    DifferentiableAt 𝕜 f x coord :=
  h.hasFDerivAt.differentiableAt

theorem DifferentiableWithinAt.hasGradientWithinAt (h : DifferentiableWithinAt 𝕜 f s x) :
    HasGradientWithinAt f (gradientWithin f s x) s x := by
  simpa [hasGradientWithinAt_iff_hasFDerivWithinAt] using h.hasFDerivWithinAt

theorem HasGradientWithinAt.differentiableWithinAt {D : Type*} [TopologicalSpace D]
    {f : D → 𝕜} {coord : D → F} {s : Set D} {x : D}
    (h : HasGradientWithinAt f f' s x coord) : DifferentiableWithinAt 𝕜 f s x coord :=
  h.hasFDerivWithinAt.differentiableWithinAt

@[simp]
theorem hasGradientWithinAt_univ {D : Type*} [TopologicalSpace D]
    {f : D → 𝕜} {coord : D → F} {x : D} :
    HasGradientWithinAt f f' univ x coord ↔ HasGradientAt f f' x coord := by
  rw [hasGradientWithinAt_iff_hasFDerivWithinAt, hasGradientAt_iff_hasFDerivAt]
  exact hasFDerivWithinAt_univ

@[simp]
lemma gradientWithin_univ : gradientWithin f univ = gradient f := by
  ext
  simp only [gradientWithin, gradient, fderiv]

theorem DifferentiableOn.hasGradientAt (h : DifferentiableOn 𝕜 f s) (hs : s ∈ 𝓝 x) :
    HasGradientAt f (∇ f x) x :=
  (h.hasFDerivAt hs).hasGradientAt

theorem HasGradientAt.gradient (h : HasGradientAt f f' x) : ∇ f x = f' :=
  h.differentiableAt.hasGradientAt.unique h

theorem gradient_eq {f' : F → F} (h : ∀ x, HasGradientAt f (f' x) x) : ∇ f = f' :=
  funext fun x => (h x).gradient

section OneDimension

variable {g : 𝕜 → 𝕜} {g' u : 𝕜} {L' : Filter 𝕜}

theorem HasGradientAtFilter.hasDerivAtFilter (h : HasGradientAtFilter g g' u L') :
    HasDerivAtFilter g (conj g') (L' ×ˢ pure u) :=
  h

theorem HasDerivAtFilter.hasGradientAtFilter (h : HasDerivAtFilter g g' (L' ×ˢ pure u)) :
    HasGradientAtFilter g (conj g') u L' := by
  have : ContinuousLinearMap.smulRight (1 : 𝕜 →L[𝕜] 𝕜) g' = (toDual 𝕜 𝕜) (conj g') := by
    ext; simp
  rwa [HasGradientAtFilter, ← this]

theorem HasGradientAt.hasDerivAt (h : HasGradientAt g g' u) : HasDerivAt g (conj g') u := by
  rw [hasGradientAt_iff_hasFDerivAt, hasFDerivAt_iff_hasDerivAt] at h
  simpa using h

theorem HasDerivAt.hasGradientAt (h : HasDerivAt g g' u) : HasGradientAt g (conj g') u := by
  rw [hasGradientAt_iff_hasFDerivAt, hasFDerivAt_iff_hasDerivAt]
  simpa

theorem gradient_eq_deriv : ∇ g u = conj (deriv g u) := by
  by_cases h : DifferentiableAt 𝕜 g u
  · rw [h.hasGradientAt.hasDerivAt.deriv, RCLike.conj_conj]
  · rw [gradient_eq_zero_of_not_differentiableAt h, deriv_zero_of_not_differentiableAt h, map_zero]

end OneDimension

section OneDimensionReal

variable {g : ℝ → ℝ} {g' u : ℝ} {L' : Filter ℝ}

theorem HasGradientAtFilter.hasDerivAtFilter' (h : HasGradientAtFilter g g' u L') :
    HasDerivAtFilter g g' (L' ×ˢ pure u) := h.hasDerivAtFilter

theorem HasDerivAtFilter.hasGradientAtFilter' (h : HasDerivAtFilter g g' (L' ×ˢ pure u)) :
    HasGradientAtFilter g g' u L' := h.hasGradientAtFilter

theorem HasGradientAt.hasDerivAt' (h : HasGradientAt g g' u) :
    HasDerivAt g g' u := h.hasDerivAt

theorem HasDerivAt.hasGradientAt' (h : HasDerivAt g g' u) :
    HasGradientAt g g' u := h.hasGradientAt

theorem gradient_eq_deriv' : ∇ g u = deriv g u := gradient_eq_deriv

end OneDimensionReal

open Filter

section GradientProperties

theorem hasGradientAtFilter_iff_isLittleO {D : Type*} {f : D → 𝕜} {coord : D → F}
    {x : D} {L : Filter D} :
    HasGradientAtFilter f f' x L coord ↔
      (fun x' => f x' - f x - ⟪f', coord x' - coord x⟫) =o[L]
        fun x' => coord x' - coord x :=
  hasFDerivAtFilter_iff_isLittleO.trans <| by simp [Function.comp_def]

theorem hasGradientWithinAt_iff_isLittleO {D : Type*} [TopologicalSpace D]
    {f : D → 𝕜} {coord : D → F} {s : Set D} {x : D} :
    HasGradientWithinAt f f' s x coord ↔
      (fun x' => f x' - f x - ⟪f', coord x' - coord x⟫) =o[𝓝[s] x]
        fun x' => coord x' - coord x :=
  hasGradientAtFilter_iff_isLittleO

theorem hasGradientWithinAt_iff_tendsto {D : Type*} [TopologicalSpace D] {f : D → 𝕜}
    {coord : D → F} {s : Set D} {x : D}
    (h₀ : ∀ᶠ y in 𝓝[s] x, coord y = coord x → f y = f x := by
      exact Filter.Eventually.of_forall fun y h ↦ congrArg _ h) :
    HasGradientWithinAt f f' s x coord ↔
      Tendsto (fun y : {y : D // coord y - coord x ≠ 0} ↦
        Checked.div ‖f y - f x - ⟪f', coord y - coord x⟫‖
          ‖coord y - coord x‖ (norm_ne_zero_iff.mpr y.2).isUnit)
        (comap Subtype.val (𝓝[s] x)) (𝓝 0) :=
  hasFDerivWithinAt_iff_tendsto h₀

theorem hasGradientAt_iff_isLittleO {D : Type*} [TopologicalSpace D]
    {f : D → 𝕜} {coord : D → F} {x : D} : HasGradientAt f f' x coord ↔
      (fun x' => f x' - f x - ⟪f', coord x' - coord x⟫) =o[𝓝 x]
        fun x' => coord x' - coord x :=
  hasGradientAtFilter_iff_isLittleO

theorem hasGradientAt_iff_tendsto {D : Type*} [TopologicalSpace D] {f : D → 𝕜}
    {coord : D → F} {x : D}
    (h₀ : ∀ᶠ y in 𝓝 x, coord y = coord x → f y = f x := by
      exact Filter.Eventually.of_forall fun y h ↦ congrArg _ h) :
    HasGradientAt f f' x coord ↔
      Tendsto (fun y : {y : D // coord y - coord x ≠ 0} ↦
        Checked.div ‖f y - f x - ⟪f', coord y - coord x⟫‖
          ‖coord y - coord x‖ (norm_ne_zero_iff.mpr y.2).isUnit)
        (comap Subtype.val (𝓝 x)) (𝓝 0) :=
  hasFDerivAt_iff_tendsto h₀

theorem HasGradientAtFilter.isBigO_sub {D : Type*} {f : D → 𝕜} {coord : D → F}
    {x : D} {L : Filter D} (h : HasGradientAtFilter f f' x L coord) :
    (fun x' => f x' - f x) =O[L] fun x' => coord x' - coord x :=
  (HasFDerivAtFilter.isBigOTVS_sub h).isBigO.comp_tendsto prod_pure.ge

theorem hasGradientWithinAt_congr_set' {s t : Set F} (y : F) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    HasGradientWithinAt f f' s x ↔ HasGradientWithinAt f f' t x :=
  hasFDerivWithinAt_congr_set' y h

theorem hasGradientWithinAt_congr_set {s t : Set F} (h : s =ᶠ[𝓝 x] t) :
    HasGradientWithinAt f f' s x ↔ HasGradientWithinAt f f' t x :=
  hasFDerivWithinAt_congr_set h

theorem hasGradientAt_iff_isLittleO_nhds_zero : HasGradientAt f f' x ↔
    (fun h => f (x + h) - f x - ⟪f', h⟫) =o[𝓝 0] fun h => h :=
  hasFDerivAt_iff_isLittleO_nhds_zero

end GradientProperties

section Inner

lemma HasGradientWithinAt.fderivWithin_apply
    (h : HasGradientWithinAt f f' s x) (hs : UniqueDiffWithinAt 𝕜 s x) :
    (fderivWithin 𝕜 f s x : F → 𝕜) y = ⟪f', y⟫ := by
  rw [h.hasFDerivWithinAt.fderivWithin hs, toDual_apply_apply]

lemma HasGradientAt.fderiv_apply (h : HasGradientAt f f' x) :
    (fderiv 𝕜 f x : F → 𝕜) y = ⟪f', y⟫ := by
  rw [h.hasFDerivAt.fderiv, toDual_apply_apply]

@[simp]
lemma inner_gradientWithin_left :
    ⟪gradientWithin f s x, y⟫ = (fderivWithin 𝕜 f s x : F → 𝕜) y := by
  rw [gradientWithin, ← toDual_apply_apply (𝕜 := 𝕜) (E := F),
      LinearIsometryEquiv.apply_symm_apply]

@[simp]
lemma inner_gradient_left : ⟪∇ f x, y⟫ = (fderiv 𝕜 f x : F → 𝕜) y := by
  rw [gradient, ← toDual_apply_apply (𝕜 := 𝕜) (E := F),
    LinearIsometryEquiv.apply_symm_apply]

@[simp]
lemma inner_gradientWithin_right :
    ⟪x, gradientWithin f s y⟫ = conj ((fderivWithin 𝕜 f s y : F → 𝕜) x) := by
  rw [← inner_conj_symm, inner_gradientWithin_left]

@[simp]
lemma inner_gradient_right : ⟪x, ∇ f y⟫ = conj ((fderiv 𝕜 f y : F → 𝕜) x) := by
  rw [← inner_conj_symm, inner_gradient_left]

end Inner

section congr

/-! ### Congruence properties of the Gradient -/

variable {f₀ f₁ : F → 𝕜} {f₀' f₁' : F} {t : Set F}

theorem Filter.EventuallyEq.hasGradientAtFilter_iff (h₀ : f₀ =ᶠ[L] f₁) (hx : f₀ x = f₁ x)
    (h₁ : f₀' = f₁') : HasGradientAtFilter f₀ f₀' x L ↔ HasGradientAtFilter f₁ f₁' x L :=
  (h₀.prodMap <| by assumption).hasFDerivAtFilter_iff <| by simp [h₁]

theorem HasGradientAtFilter.congr_of_eventuallyEq (h : HasGradientAtFilter f f' x L)
    (hL : f₁ =ᶠ[L] f) (hx : f₁ x = f x) : HasGradientAtFilter f₁ f' x L := by
  rwa [hL.hasGradientAtFilter_iff hx rfl]

theorem HasGradientWithinAt.congr_mono (h : HasGradientWithinAt f f' s x) (ht : ∀ x ∈ t, f₁ x = f x)
    (hx : f₁ x = f x) (h₁ : t ⊆ s) : HasGradientWithinAt f₁ f' t x :=
  HasFDerivWithinAt.congr_mono h ht hx h₁

theorem HasGradientWithinAt.congr (h : HasGradientWithinAt f f' s x) (hs : ∀ x ∈ s, f₁ x = f x)
    (hx : f₁ x = f x) : HasGradientWithinAt f₁ f' s x :=
  h.congr_mono hs hx (by tauto)

theorem HasGradientWithinAt.congr_of_mem (h : HasGradientWithinAt f f' s x)
    (hs : ∀ x ∈ s, f₁ x = f x) (hx : x ∈ s) : HasGradientWithinAt f₁ f' s x :=
  h.congr hs (hs _ hx)

theorem HasGradientWithinAt.congr_of_eventuallyEq (h : HasGradientWithinAt f f' s x)
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : HasGradientWithinAt f₁ f' s x :=
  HasGradientAtFilter.congr_of_eventuallyEq h h₁ hx

theorem HasGradientWithinAt.congr_of_eventuallyEq_of_mem (h : HasGradientWithinAt f f' s x)
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : x ∈ s) : HasGradientWithinAt f₁ f' s x :=
  h.congr_of_eventuallyEq h₁ (h₁.eq_of_nhdsWithin hx)

theorem HasGradientAt.congr_of_eventuallyEq (h : HasGradientAt f f' x) (h₁ : f₁ =ᶠ[𝓝 x] f) :
    HasGradientAt f₁ f' x :=
  HasGradientAtFilter.congr_of_eventuallyEq h h₁ (mem_of_mem_nhds h₁ :)

theorem Filter.EventuallyEq.gradient_eq (hL : f₁ =ᶠ[𝓝 x] f) : ∇ f₁ x = ∇ f x := by
  unfold gradient
  rwa [Filter.EventuallyEq.fderiv_eq]

protected theorem Filter.EventuallyEq.gradient (h : f₁ =ᶠ[𝓝 x] f) : ∇ f₁ =ᶠ[𝓝 x] ∇ f :=
  h.eventuallyEq_nhds.mono fun _ h => h.gradient_eq

end congr

/-! ### The Gradient of constant functions -/

section Const

variable (c : 𝕜) (s x L)

theorem hasGradientAtFilter_const : HasGradientAtFilter (fun _ => c) (0 : F) x L := by
  rw [HasGradientAtFilter, map_zero]; exact hasFDerivAtFilter_const c _

theorem hasGradientWithinAt_const : HasGradientWithinAt (fun _ => c) (0 : F) s x :=
  hasGradientAtFilter_const _ _ _

theorem hasGradientAt_const : HasGradientAt (fun _ => c) (0 : F) x :=
  hasGradientAtFilter_const _ _ _

theorem gradient_fun_const : ∇ (fun _ => c) x = 0 := by
  simp only [gradient, fderiv_const_apply, map_zero]

theorem gradient_const : ∇ (const F c) x = 0 := gradient_fun_const x c

@[simp]
theorem gradient_fun_const' : (∇ fun _ : F => c) = fun _ => 0 :=
  funext fun x => gradient_const x c

@[simp]
theorem gradient_const' : ∇ (const F c) = 0 := gradient_fun_const' c

end Const

section Continuous

/-! ### Continuity of a function admitting a gradient -/

theorem HasGradientAtFilter.tendsto_nhds {D : Type*} [TopologicalSpace D]
    {f : D → 𝕜} {coord : D → F} {x : D} {L : Filter D}
    (hL : L ≤ 𝓝 x) (h : HasGradientAtFilter f f' x L coord)
    (hcoord : Tendsto coord L (𝓝 (coord x)) := by
      exact tendsto_id.mono_left (by assumption)) : Tendsto f L (𝓝 (f x)) :=
  HasFDerivAtFilter.tendsto_nhds hL h hcoord

theorem HasGradientWithinAt.continuousWithinAt {D : Type*} [TopologicalSpace D]
    {f : D → 𝕜} {coord : D → F} {s : Set D} {x : D}
    (h : HasGradientWithinAt f f' s x coord)
    (hcoord : ContinuousWithinAt coord s x := by exact continuousWithinAt_id) :
    ContinuousWithinAt f s x :=
  HasGradientAtFilter.tendsto_nhds inf_le_left h hcoord

theorem HasGradientAt.continuousAt {D : Type*} [TopologicalSpace D]
    {f : D → 𝕜} {coord : D → F} {x : D} (h : HasGradientAt f f' x coord)
    (hcoord : ContinuousAt coord x := by exact continuousAt_id) : ContinuousAt f x :=
  HasGradientAtFilter.tendsto_nhds le_rfl h hcoord

protected theorem HasGradientAt.continuousOn {D : Type*} [TopologicalSpace D]
    {f : D → 𝕜} {coord : D → F} {s : Set D} {f' : D → F}
    (h : ∀ x ∈ s, HasGradientAt f (f' x) x coord)
    (hcoord : ∀ x ∈ s, ContinuousAt coord x := by
      exact fun _ _ ↦ continuousAt_id) :
    ContinuousOn f s :=
  fun x hx => ((h x hx).continuousAt (hcoord x hx)).continuousWithinAt

end Continuous
