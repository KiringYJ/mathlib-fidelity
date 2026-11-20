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
public import Mathlib.Geometry.Manifold.Notation

/-!
# Vector fields in manifolds

We study functions of the form `V : Π (x : M), TangentSpace I x` on a manifold, i.e.,
vector fields.

At a point, a vector field pulls back to the unique tangent vector mapped to its given value
by the derivative. A within-set pullback also requires a unique within-set derivative.
Regularity theorems apply to local fields related by that derivative.

See `Mathlib/Geometry/Manifold/VectorField/LieBracket.lean` for the Lie bracket of two vector
fields.

These definitions are given in the `VectorField` namespace because pullbacks, Lie brackets,
and so on, are notions that make sense in a variety of contexts.
We also prefix the notions with `m` to distinguish the manifold notions from the vector space
notions.

For notions that come naturally in other namespaces for dot notation, we specify `vectorField` in
the name to lift ambiguities. For instance, the fact that the Lie bracket of two smooth vector
fields is smooth is `ContMDiffAt.mlieBracket_vectorField`.

Note that a smoothness assumption for a vector field is written by seeing the vector field as
a function from `M` to its tangent bundle through a coercion, as in:
`MDifferentiableWithinAt I I.tangent (fun y ↦ (V y : TangentBundle I M)) s x`
(or `MDiffAt[s] (T% V) x`, for short).
-/

@[expose] public section

open Set Function Filter
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
  {H'' : Type*} [TopologicalSpace H''] {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {I'' : ModelWithCorners 𝕜 E'' H''}
  {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H'' M'']
  {f : M → M'} {s t : Set M} {x x₀ : M}

instance {n : ℕ} [n.AtLeastTwo] [IsManifold I (minSmoothness 𝕜 (ofNat(n))) M] :
    IsManifold I (ofNat(n)) M :=
  IsManifold.of_le (n := minSmoothness 𝕜 n) le_minSmoothness

instance [IsManifold I (minSmoothness 𝕜 1) M] :
    IsManifold I 1 M :=
  IsManifold.of_le (n := minSmoothness 𝕜 1) le_minSmoothness

instance [IsManifold I (minSmoothness 𝕜 3) M] :
    IsManifold I (minSmoothness 𝕜 2) M :=
  IsManifold.of_le (n := minSmoothness 𝕜 3) (minSmoothness_monotone (by norm_cast))

instance [IsManifold I (minSmoothness 𝕜 2) M] :
    IsManifold I (minSmoothness 𝕜 1) M :=
  IsManifold.of_le (n := minSmoothness 𝕜 2) (minSmoothness_monotone (by norm_cast))

namespace VectorField

section Pullback

/-! ### Pullback of vector fields in manifolds -/

open ContinuousLinearMap

variable {V V₁ : Π (x : M'), TangentSpace I' x}
variable {c : 𝕜} {m n : ℕ∞ω} {t : Set M'} {y₀ : M'}

/-- A vector with a unique lift under a supplied manifold derivative. -/
def _root_.HasMFDerivWithinAt.pullback
    {A : TangentSpace I x →L[𝕜] TangentSpace I' (f x)}
    (_h : HasMFDerivWithinAt I I' f s x A) (w : TangentSpace I' (f x))
    (hw : ∃! v, A v = w) : TangentSpace I x := hw.exists.choose

variable (I I') in
/-- The pointwise pullback within a set, where the derivative is unique and the target vector has
a unique preimage. -/
def mpullbackWithin (f : M → M') (V : Π x : M', TangentSpace I' x) (s : Set M) (x : M)
    (hd : ∃! A, HasMFDerivWithinAt I I' f s x A)
    (hv : ∃! v, mfderivWithin I I' f s x v = V (f x)) : TangentSpace I x :=
  hd.exists.choose_spec.mdifferentiableWithinAt.hasMFDerivWithinAt.pullback _ hv

variable (I I') in
/-- The pointwise pullback of a vector field where the derivative exists and the target vector
has a unique preimage. -/
def mpullback (f : M → M') (V : Π x : M', TangentSpace I' x) (x : M)
    (_hd : MDifferentiableAt I I' f x)
    (hv : ∃! v, mfderiv I I' f x v = V (f x)) : TangentSpace I x := hv.exists.choose

lemma _root_.MDifferentiableWithinAt.existsUnique_mfderivWithin
    (hd : MDifferentiableWithinAt I I' f s x) (hs : UniqueMDiffWithinAt I s x) :
    ∃! A, HasMFDerivWithinAt I I' f s x A :=
  ⟨_, hd.hasMFDerivWithinAt, fun _ hA ↦ hs.eq hA hd.hasMFDerivWithinAt⟩

/-- The two tangent vectors are related by a derivative of the map within the set. -/
def IsMRelatedWithinAt (f : M → M') (U : Π x : M, TangentSpace I x)
    (V : Π x : M', TangentSpace I' x) (s : Set M) (x : M) : Prop :=
  ∃ A, HasMFDerivWithinAt I I' f s x A ∧ A (U x) = V (f x)

lemma IsMRelatedWithinAt.comp {g : M' → M''} {t : Set M'}
    {U : Π x : M, TangentSpace I x} {W : Π x : M'', TangentSpace I'' x}
    (hg : IsMRelatedWithinAt g V W t (f x)) (hf : IsMRelatedWithinAt f U V s x)
    (hst : MapsTo f s t) : IsMRelatedWithinAt (g ∘ f) U W s x := by
  obtain ⟨B, hB, hW⟩ := hg
  obtain ⟨A, hA, hV⟩ := hf
  exact ⟨B.comp A, hB.comp x hA hst, (congrArg B hV).trans hW⟩

lemma IsMRelatedWithinAt.to_model {f : E → E'} {s : Set E} {x : E} {U : E → E} {V : E' → E'}
    (h : IsMRelatedWithinAt (I := 𝓘(𝕜, E)) (I' := 𝓘(𝕜, E')) f U V s x) :
    IsRelatedWithinAt (𝕜 := 𝕜) f U V s x := by
  obtain ⟨A, hA, h⟩ := h
  exact ⟨A, hA.hasFDerivWithinAt, h⟩

lemma IsMRelatedWithinAt.mono {U : Π x : M, TangentSpace I x} {u : Set M}
    (h : IsMRelatedWithinAt f U V s x) (hu : u ⊆ s) : IsMRelatedWithinAt f U V u x := by
  obtain ⟨A, hA, h⟩ := h
  exact ⟨A, hA.mono hu, h⟩

lemma IsMRelatedWithinAt.mfderivWithin_apply {U : Π x : M, TangentSpace I x}
    (h : IsMRelatedWithinAt f U V s x) (hs : UniqueMDiffWithinAt I s x) :
    mfderivWithin I I' f s x (U x) = V (f x) := by
  obtain ⟨A, hA, h⟩ := h
  rwa [hA.mfderivWithin hs]

lemma mpullbackWithin_apply {hd hv} {v : TangentSpace I x} :
    mpullbackWithin I I' f V s x hd hv = v ↔ mfderivWithin I I' f s x v = V (f x) :=
  ⟨fun h ↦ h ▸ hv.exists.choose_spec, fun h ↦ hv.unique hv.exists.choose_spec h⟩

lemma mpullbackWithin_const_smul_apply {hD hV hP} :
    mpullbackWithin I I' f (c • V) s x hD hP = c • (mpullbackWithin I I' f V s x hD hV) := by
  apply mpullbackWithin_apply.mpr
  rw [map_smul, mpullbackWithin_apply.mp (rfl : mpullbackWithin I I' f V s x hD hV = _)]
  rfl

lemma mpullbackWithin_const_smul {D : Type*} (base : D → M)
    {hD : ∀ y, ∃! A, HasMFDerivWithinAt I I' f s (base y) A}
    {hV : ∀ y, ∃! v, mfderivWithin I I' f s (base y) v = V (f (base y))}
    {hP : ∀ y, ∃! v, mfderivWithin I I' f s (base y) v = c • V (f (base y))} :
    (fun y ↦ mpullbackWithin I I' f (c • V) s (base y) (hD y) (hP y)) =
      fun y ↦ c • (mpullbackWithin I I' f V s (base y) (hD y) (hV y)) :=
  funext fun _ ↦ mpullbackWithin_const_smul_apply

lemma mpullbackWithin_smul_apply {g : M' → 𝕜} {hD hV hP} :
    mpullbackWithin I I' f (g • V) s x hD hP = g (f x) • (mpullbackWithin I I' f V s x hD hV) := by
  apply mpullbackWithin_apply.mpr
  rw [map_smul, mpullbackWithin_apply.mp (rfl : mpullbackWithin I I' f V s x hD hV = _)]
  rfl

lemma mpullbackWithin_smul {g : M' → 𝕜} {D : Type*} (base : D → M)
    {hD : ∀ y, ∃! A, HasMFDerivWithinAt I I' f s (base y) A}
    {hV : ∀ y, ∃! v, mfderivWithin I I' f s (base y) v = V (f (base y))}
    {hP : ∀ y, ∃! v, mfderivWithin I I' f s (base y) v = g (f (base y)) • V (f (base y))} :
    (fun y ↦ mpullbackWithin I I' f (g • V) s (base y) (hD y) (hP y)) =
      fun y ↦ g (f (base y)) • (mpullbackWithin I I' f V s (base y) (hD y) (hV y)) :=
  funext fun _ ↦ mpullbackWithin_smul_apply

lemma mpullbackWithin_add_apply {hD hV hW hP} :
    mpullbackWithin I I' f (V + V₁) s x hD hP =
      mpullbackWithin I I' f V s x hD hV + mpullbackWithin I I' f V₁ s x hD hW := by
  apply mpullbackWithin_apply.mpr
  rw [map_add, mpullbackWithin_apply.mp (rfl : mpullbackWithin I I' f V s x hD hV = _),
    mpullbackWithin_apply.mp (rfl : mpullbackWithin I I' f V₁ s x hD hW = _)]
  rfl

lemma mpullbackWithin_add {D : Type*} (base : D → M)
    {hD : ∀ y, ∃! A, HasMFDerivWithinAt I I' f s (base y) A}
    {hV : ∀ y, ∃! v, mfderivWithin I I' f s (base y) v = V (f (base y))}
    {hW : ∀ y, ∃! v, mfderivWithin I I' f s (base y) v = V₁ (f (base y))}
    {hP : ∀ y, ∃! v, mfderivWithin I I' f s (base y) v = V (f (base y)) + V₁ (f (base y))} :
    (fun y ↦ mpullbackWithin I I' f (V + V₁) s (base y) (hD y) (hP y)) =
      fun y ↦ (mpullbackWithin I I' f V s (base y) (hD y) (hV y)) +
        (mpullbackWithin I I' f V₁ s (base y) (hD y) (hW y)) :=
  funext fun _ ↦ mpullbackWithin_add_apply

lemma mpullbackWithin_neg_apply {hD hV hP} :
    mpullbackWithin I I' f (-V) s x hD hP = -(mpullbackWithin I I' f V s x hD hV) := by
  apply mpullbackWithin_apply.mpr
  rw [map_neg, mpullbackWithin_apply.mp (rfl : mpullbackWithin I I' f V s x hD hV = _)]
  rfl

lemma mpullbackWithin_neg {D : Type*} (base : D → M)
    {hD : ∀ y, ∃! A, HasMFDerivWithinAt I I' f s (base y) A}
    {hV : ∀ y, ∃! v, mfderivWithin I I' f s (base y) v = V (f (base y))}
    {hP : ∀ y, ∃! v, mfderivWithin I I' f s (base y) v = -V (f (base y))} :
    (fun y ↦ mpullbackWithin I I' f (-V) s (base y) (hD y) (hP y)) =
      fun y ↦ -(mpullbackWithin I I' f V s (base y) (hD y) (hV y)) :=
  funext fun _ ↦ mpullbackWithin_neg_apply

@[simp] lemma mpullbackWithin_zero {hD hP} :
    mpullbackWithin I I' f 0 s x hD hP = 0 :=
  mpullbackWithin_apply.mpr (map_zero _)

lemma mpullback_apply {hd hv} {v : TangentSpace I x} :
    mpullback I I' f V x hd hv = v ↔ mfderiv I I' f x v = V (f x) :=
  ⟨fun h ↦ h ▸ hv.exists.choose_spec, fun h ↦ hv.unique hv.exists.choose_spec h⟩

lemma mpullback_const_smul_apply {hD hV hP} :
    mpullback I I' f (c • V) x hD hP = c • (mpullback I I' f V x hD hV) := by
  apply mpullback_apply.mpr
  rw [map_smul, mpullback_apply.mp (rfl : mpullback I I' f V x hD hV = _)]
  rfl

lemma mpullback_const_smul {D : Type*} (base : D → M)
    {hD : ∀ y, MDifferentiableAt I I' f (base y)}
    {hV : ∀ y, ∃! v, mfderiv I I' f (base y) v = V (f (base y))}
    {hP : ∀ y, ∃! v, mfderiv I I' f (base y) v = c • V (f (base y))} :
    (fun y ↦ mpullback I I' f (c • V) (base y) (hD y) (hP y)) =
      fun y ↦ c • (mpullback I I' f V (base y) (hD y) (hV y)) :=
  funext fun _ ↦ mpullback_const_smul_apply

lemma mpullback_smul_apply {g : M' → 𝕜} {hD hV hP} :
    mpullback I I' f (g • V) x hD hP = g (f x) • (mpullback I I' f V x hD hV) := by
  apply mpullback_apply.mpr
  rw [map_smul, mpullback_apply.mp (rfl : mpullback I I' f V x hD hV = _)]
  rfl

lemma mpullback_smul {g : M' → 𝕜} {D : Type*} (base : D → M)
    {hD : ∀ y, MDifferentiableAt I I' f (base y)}
    {hV : ∀ y, ∃! v, mfderiv I I' f (base y) v = V (f (base y))}
    {hP : ∀ y, ∃! v, mfderiv I I' f (base y) v = g (f (base y)) • V (f (base y))} :
    (fun y ↦ mpullback I I' f (g • V) (base y) (hD y) (hP y)) =
      fun y ↦ g (f (base y)) • (mpullback I I' f V (base y) (hD y) (hV y)) :=
  funext fun _ ↦ mpullback_smul_apply

lemma mpullback_add_apply {hD hV hW hP} :
    mpullback I I' f (V + V₁) x hD hP =
      mpullback I I' f V x hD hV + mpullback I I' f V₁ x hD hW := by
  apply mpullback_apply.mpr
  rw [map_add, mpullback_apply.mp (rfl : mpullback I I' f V x hD hV = _),
    mpullback_apply.mp (rfl : mpullback I I' f V₁ x hD hW = _)]
  rfl

lemma mpullback_add {D : Type*} (base : D → M)
    {hD : ∀ y, MDifferentiableAt I I' f (base y)}
    {hV : ∀ y, ∃! v, mfderiv I I' f (base y) v = V (f (base y))}
    {hW : ∀ y, ∃! v, mfderiv I I' f (base y) v = V₁ (f (base y))}
    {hP : ∀ y, ∃! v, mfderiv I I' f (base y) v = V (f (base y)) + V₁ (f (base y))} :
    (fun y ↦ mpullback I I' f (V + V₁) (base y) (hD y) (hP y)) =
      fun y ↦ (mpullback I I' f V (base y) (hD y) (hV y)) +
        (mpullback I I' f V₁ (base y) (hD y) (hW y)) :=
  funext fun _ ↦ mpullback_add_apply

lemma mpullback_neg_apply {hD hV hP} :
    mpullback I I' f (-V) x hD hP = -(mpullback I I' f V x hD hV) := by
  apply mpullback_apply.mpr
  rw [map_neg, mpullback_apply.mp (rfl : mpullback I I' f V x hD hV = _)]
  rfl

lemma mpullback_neg {D : Type*} (base : D → M)
    {hD : ∀ y, MDifferentiableAt I I' f (base y)}
    {hV : ∀ y, ∃! v, mfderiv I I' f (base y) v = V (f (base y))}
    {hP : ∀ y, ∃! v, mfderiv I I' f (base y) v = -V (f (base y))} :
    (fun y ↦ mpullback I I' f (-V) (base y) (hD y) (hP y)) =
      fun y ↦ -(mpullback I I' f V (base y) (hD y) (hV y)) :=
  funext fun _ ↦ mpullback_neg_apply

@[simp] lemma mpullback_zero {hD hP} :
    mpullback I I' f 0 x hD hP = 0 :=
  mpullback_apply.mpr (map_zero _)

@[simp] lemma mpullbackWithin_id {V : Π x : M, TangentSpace I x}
    (h : UniqueMDiffWithinAt I s x) {hd hv} : mpullbackWithin I I id V s x hd hv = V x := by
  apply mpullbackWithin_apply.mpr
  simp [mfderivWithin_id h]

@[simp] lemma mpullback_id {V : Π x : M, TangentSpace I x} {hd hv} :
    mpullback I I id V x hd hv = V x := by
  apply mpullback_apply.mpr
  simp

@[simp] lemma mpullbackWithin_univ {hd hw hf hv} :
    mpullbackWithin I I' f V univ x hd hw = mpullback I I' f V x hf hv := by
  apply mpullbackWithin_apply.mpr
  simpa only [mfderivWithin_univ] using mpullback_apply.mp (rfl : mpullback I I' f V x hf hv = _)

lemma mpullbackWithin_eq_pullbackWithin {f : E → E'} {V : E' → E'} {s : Set E} {x : E}
    {hm hw hd hv} : mpullbackWithin 𝓘(𝕜, E) 𝓘(𝕜, E') f V s x hm hw =
      pullbackWithin 𝕜 f V s x hd hv := by
  apply mpullbackWithin_apply.mpr
  rw [mfderivWithin_eq_fderivWithin]
  exact fderivWithin_pullbackWithin (𝕜 := 𝕜) f V s x

lemma mpullback_eq_pullback {f : E → E'} {V : E' → E'} {x : E} {hm hw hd hv} :
    mpullback 𝓘(𝕜, E) 𝓘(𝕜, E') f V x hm hw = pullback 𝕜 f V x hd hv := by
  apply mpullback_apply.mpr
  rw [mfderiv_eq_fderiv]
  exact fderiv_pullback (𝕜 := 𝕜) f V x

/-- Unique lifts under two successive derivatives give a unique lift under their composite. -/
lemma existsUnique_mpullbackWithin_comp {g : M' → M''} {V : Π x : M'', TangentSpace I'' x}
    {t : Set M'} (hf : MDifferentiableWithinAt I I' f s x)
    {hg : ∃! A, HasMFDerivWithinAt I' I'' g t (f x) A}
    (hst : MapsTo f s t) (hs : UniqueMDiffWithinAt I s x)
    (hW : ∃! w, mfderivWithin I' I'' g t (f x) w = V (g (f x)))
    (hU : ∃! u, mfderivWithin I I' f s x u = mpullbackWithin I' I'' g V t (f x) hg hW) :
    ∃! u, mfderivWithin I I'' (g ∘ f) s x u = V (g (f x)) := by
  rw [mfderivWithin_comp x hg.exists.choose_spec.mdifferentiableWithinAt hf hst hs]
  refine ⟨hU.exists.choose, ?_, fun u hu ↦ ?_⟩
  · change mfderivWithin I' I'' g t (f x) (mfderivWithin I I' f s x hU.exists.choose) = _
    rw [hU.exists.choose_spec]
    exact hW.exists.choose_spec
  · exact hU.unique (hW.unique hu hW.exists.choose_spec) hU.exists.choose_spec

/-- Pulling back by the composite agrees with the two successive pointwise lifts. -/
lemma mpullbackWithin_comp {g : M' → M''} {V : Π x : M'', TangentSpace I'' x} {t : Set M'}
    (hf : MDifferentiableWithinAt I I' f s x) (hg : ∃! A, HasMFDerivWithinAt I' I'' g t (f x) A)
    (hst : MapsTo f s t) (hs : UniqueMDiffWithinAt I s x) {hW hU} :
    mpullbackWithin I I'' (g ∘ f) V s x
      ((hg.exists.choose_spec.mdifferentiableWithinAt.comp x hf hst).existsUnique_mfderivWithin hs)
      (existsUnique_mpullbackWithin_comp (hg := hg) hf hst hs hW hU) =
      hf.hasMFDerivWithinAt.pullback (mpullbackWithin I' I'' g V t (f x) hg hW) hU := by
  apply mpullbackWithin_apply.mpr
  rw [mfderivWithin_comp x hg.exists.choose_spec.mdifferentiableWithinAt hf hst hs,
    ContinuousLinearMap.comp_apply]
  have h := hU.exists.choose_spec
  change mfderivWithin I I' f s x (hf.hasMFDerivWithinAt.pullback _ hU) = _ at h
  rw [h]
  exact hW.exists.choose_spec

lemma mpullbackWithin_comp_of_left {g : M' → M''} {V : Π x : M'', TangentSpace I'' x} {t : Set M'}
    (hf : MDifferentiableWithinAt I I' f s x) (hg : ∃! A, HasMFDerivWithinAt I' I'' g t (f x) A)
    (hst : MapsTo f s t) (hs : UniqueMDiffWithinAt I s x)
    (hB : (mfderivWithin I' I'' g t (f x)).IsInvertible) {hU} :
    mpullbackWithin I I'' (g ∘ f) V s x
      ((hg.exists.choose_spec.mdifferentiableWithinAt.comp x hf hst).existsUnique_mfderivWithin hs)
      (existsUnique_mpullbackWithin_comp (hg := hg) hf hst hs (hB.existsUnique_preimage _) hU) =
      hf.hasMFDerivWithinAt.pullback
        (mpullbackWithin I' I'' g V t (f x) hg (hB.existsUnique_preimage _)) hU :=
  mpullbackWithin_comp hf hg hst hs

lemma mpullbackWithin_comp_of_right {g : M' → M''} {V : Π x : M'', TangentSpace I'' x} {t : Set M'}
    (hf : MDifferentiableWithinAt I I' f s x) (hg : ∃! A, HasMFDerivWithinAt I' I'' g t (f x) A)
    (hst : MapsTo f s t) (hs : UniqueMDiffWithinAt I s x)
    (hA : (mfderivWithin I I' f s x).IsInvertible) {hW} :
    mpullbackWithin I I'' (g ∘ f) V s x
      ((hg.exists.choose_spec.mdifferentiableWithinAt.comp x hf hst).existsUnique_mfderivWithin hs)
      (existsUnique_mpullbackWithin_comp (hg := hg) hf hst hs hW (hA.existsUnique_preimage _)) =
      hf.hasMFDerivWithinAt.pullback
        (mpullbackWithin I' I'' g V t (f x) hg hW) (hA.existsUnique_preimage _) :=
  mpullbackWithin_comp hf hg hst hs

/-! ### Regularity of pullback of vector fields

In this paragraph, we assume that the model space is complete, to ensure that the set of invertible
linear maps is open and that inversion is a smooth map there. Otherwise, the pullback of vector
fields could behave wildly, even at points where the derivative of the map is invertible.
-/

variable {U : Π x : M, TangentSpace I x}

/-- Invertible continuous linear maps have locally smooth inverses in bundle coordinates. -/
private theorem exists_inverse_germ [CompleteSpace E] {A : M → E →L[𝕜] E'}
    (hA : ContMDiffWithinAt I 𝓘(𝕜, E →L[𝕜] E') m A s x₀) (h : (A x₀).IsInvertible) :
    ∃ G : M → E' →L[𝕜] E, ContMDiffWithinAt I 𝓘(𝕜, E' →L[𝕜] E) m G s x₀ ∧
      ∀ᶠ y in 𝓝[s] x₀, ∀ v, G y (A y v) = v := by
  classical
  obtain ⟨e, he⟩ := h
  let g := Function.extend (fun e : E ≃L[𝕜] E' ↦ (e : E →L[𝕜] E'))
    (fun e ↦ (e.symm : E' →L[𝕜] E)) (fun _ ↦ (e.symm : E' →L[𝕜] E))
  have hg (u : E ≃L[𝕜] E') : g u = (u.symm : E' →L[𝕜] E) :=
    (show Injective (fun e : E ≃L[𝕜] E' ↦ (e : E →L[𝕜] E')) from
      fun _ _ H ↦ ContinuousLinearEquiv.coe_inj.mp H).extend_apply _ _ _
  have hcont : ContDiffAt 𝕜 m g (A x₀) := he ▸ contDiffAt_map_inverse e hg
  refine ⟨g ∘ A, hcont.contMDiffAt.comp_contMDiffWithinAt x₀ hA, ?_⟩
  have h₀ : (A x₀).IsInvertible := ⟨e, he⟩
  filter_upwards [hA.continuousWithinAt h₀.eventually_nhds] with y hy v
  obtain ⟨e', he'⟩ := hy
  simp [Function.comp_apply, ← he', hg]

private theorem eventually_coord_lift [IsManifold I 1 M] [IsManifold I' 1 M'] {r : Set M}
    (hs' : UniqueMDiffOn I s)
    (hx : x₀ ∈ s) (hrs : r ⊆ s) (hf : ContinuousWithinAt f s x₀)
    (hU : ∀ᶠ y in 𝓝[insert x₀ r] x₀, IsMRelatedWithinAt f U V s y) :
    ∀ᶠ y in 𝓝[insert x₀ r] x₀,
      inCoordinates E (TangentSpace I (M := M)) E' (TangentSpace I' (M := M'))
        x₀ y (f x₀) (f y) (mfderivWithin I I' f s y)
        ((trivializationAt E (TangentSpace I) x₀) ⟨y, U y⟩).2 =
      ((trivializationAt E' (TangentSpace I') (f x₀)) ⟨f y, V (f y)⟩).2 := by
  have hr : insert x₀ r ⊆ s := insert_subset hx hrs
  have hB := hf.preimage_mem_nhdsWithin <|
    (trivializationAt E' (TangentSpace I') (f x₀)).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt' _)
  have hA := (trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt' _)
  filter_upwards [hU, self_mem_nhdsWithin, nhdsWithin_le_nhds hA, nhdsWithin_mono _ hr hB]
    with y hy hys hAy hBy
  rw [inCoordinates_eq hAy hBy]
  have H := hy.mfderivWithin_apply (hs' y (hr hys))
  let L := (trivializationAt E (TangentSpace I) x₀).continuousLinearEquivAt 𝕜 y hAy
  let R := (trivializationAt E' (TangentSpace I') (f x₀)).continuousLinearEquivAt 𝕜 (f y) hBy
  change R (mfderivWithin I I' f s y (L.symm (L (U y)))) = R (V (f y))
  rw [L.symm_apply_apply, H]

section MDifferentiability

variable [IsManifold I 2 M] [IsManifold I' 2 M'] [CompleteSpace E]

/-- The pullback of a differentiable vector field by a `C^n` function with `2 ≤ n` is
differentiable. Version within a set at a point. -/
private lemma mdiffWithinAt_of_related {r : Set M}
    (hV : MDiffAt[t] (T% V) (f x₀)) (hf : CMDiffAt[s] n f x₀) (hf' : (mfderiv[s] f x₀).IsInvertible)
    (hx₀ : x₀ ∈ s) (hs : UniqueMDiff[s]) (hmn : 2 ≤ n)
    (hrs : r ⊆ s) (hrt : MapsTo f r t)
    (hU : ∀ᶠ y in 𝓝[insert x₀ r] x₀, IsMRelatedWithinAt f U V s y) :
    MDiffAt[r] (T% U) x₀ := by
  let A y := inCoordinates E (TangentSpace I (M := M)) E' (TangentSpace I' (M := M'))
    x₀ y (f x₀) (f y) (mfderivWithin I I' f s y)
  have hA : ContMDiffWithinAt I 𝓘(𝕜, E →L[𝕜] E') 1 A s x₀ :=
    (hf.of_le hmn).mfderivWithin_const le_rfl hx₀ hs
  have h₀ : (A x₀).IsInvertible := by
    dsimp only [A]
    rw [inCoordinates_eq (FiberBundle.mem_baseSet_trivializationAt' x₀)
      (FiberBundle.mem_baseSet_trivializationAt' (f x₀))]
    exact isInvertible_equiv.comp (hf'.comp isInvertible_equiv)
  obtain ⟨G, hG, he⟩ := exists_inverse_germ hA h₀
  have hv := ((mdifferentiableWithinAt_section I' V).mp hV).comp x₀
    ((hf.mdifferentiableWithinAt (by positivity)).mono hrs)
    hrt
  apply (mdifferentiableWithinAt_section I U).mpr
  apply (((hG.mdifferentiableWithinAt one_ne_zero).mono hrs).clm_apply hv).congr_of_eventuallyEq
  · have H := eventually_coord_lift hs hx₀ hrs hf.continuousWithinAt hU
    filter_upwards [H.filter_mono (nhdsWithin_mono _ (subset_insert ..)),
      he.filter_mono (nhdsWithin_mono _ hrs)] with y hy hGy
    exact (hGy _).symm.trans (congrArg (G y) hy)
  · have H := mem_of_mem_nhdsWithin (mem_insert ..)
      (eventually_coord_lift hs hx₀ hrs hf.continuousWithinAt hU)
    exact (mem_of_mem_nhdsWithin hx₀ he _).symm.trans (congrArg (G x₀) H)

protected lemma _root_.MDifferentiableWithinAt.mpullbackWithin_vectorField_inter
    (hV : MDiffAt[t] (T% V) (f x₀)) (hf : CMDiffAt[s] n f x₀) (hf' : (mfderiv[s] f x₀).IsInvertible)
    (hx₀ : x₀ ∈ s) (hs : UniqueMDiff[s]) (hmn : 2 ≤ n)
    (hU : ∀ᶠ y in 𝓝[insert x₀ (s ∩ f ⁻¹' t)] x₀, IsMRelatedWithinAt f U V s y) :
    MDiffAt[s ∩ f ⁻¹' t] (T% U) x₀ :=
  mdiffWithinAt_of_related hV hf hf' hx₀ hs hmn inter_subset_left
    ((mapsTo_preimage f t).mono_left inter_subset_right) hU

lemma _root_.MDifferentiableWithinAt.mpullbackWithin_vectorField_inter_of_eq
    (hV : MDiffAt[t] (T% V) y₀) (hf : CMDiffAt[s] n f x₀)
    (hf' : (mfderiv[s] f x₀).IsInvertible)
    (hx₀ : x₀ ∈ s) (hs : UniqueMDiff[s]) (hmn : 2 ≤ n) (h : y₀ = f x₀)
    (hU : ∀ᶠ y in 𝓝[insert x₀ (s ∩ f ⁻¹' t)] x₀, IsMRelatedWithinAt f U V s y) :
    MDiffAt[s ∩ f ⁻¹' t] (T% U) x₀ := by
  subst h
  exact hV.mpullbackWithin_vectorField_inter hf hf' hx₀ hs hmn hU

/-- The pullback of a differentiable vector field by a `C^n` function with `2 ≤ n` is
differentiable. Version on a set. -/
protected lemma _root_.MDifferentiableOn.mpullbackWithin_vectorField_inter
    (hV : MDiff[t] (T% V)) (hf : CMDiff[s] n f)
    (hf' : ∀ x ∈ s ∩ f ⁻¹' t, (mfderiv[s] f x).IsInvertible)
    (hs : UniqueMDiff[s]) (hmn : 2 ≤ n)
    (hU : ∀ y ∈ (s ∩ f ⁻¹' t), IsMRelatedWithinAt f U V s y) :
    MDiff[(s ∩ f ⁻¹' t)] (T% U) :=
  fun x₀ hx₀ ↦ MDifferentiableWithinAt.mpullbackWithin_vectorField_inter
    (hV _ hx₀.2) (hf _ hx₀.1) (hf' _ hx₀) hx₀.1 hs hmn (by
    rw [insert_eq_of_mem hx₀]
    exact eventually_nhdsWithin_of_forall fun y hy ↦ hU y hy)

/-- The pullback of a differentiable vector field by a `C^n` function with `2 ≤ n` is
differentiable. Version within a set at a point, but with full pullback. -/
protected lemma _root_.MDifferentiableWithinAt.mpullback_vectorField_preimage
    (hV : MDiffAt[t] (T% V) (f x₀)) (hf : CMDiffAt n f x₀)
    (hf' : (mfderiv% f x₀).IsInvertible) (hmn : 2 ≤ n)
    (hU : ∀ᶠ y in 𝓝[insert x₀ (f ⁻¹' t)] x₀, IsMRelatedWithinAt f U V univ y) :
    MDiffAt[f ⁻¹' t] (T% U) x₀ := by
  simp only [← contMDiffWithinAt_univ, ← mfderivWithin_univ] at hV hf hf' ⊢
  simpa using hV.mpullbackWithin_vectorField_inter hf hf' (mem_univ _) uniqueMDiffOn_univ hmn
    (by simpa using hU)

/-- The pullback of a differentiable vector field by a `C^n` function with `2 ≤ n` is
differentiable. Version within a set at a point, but with full pullback. -/
protected lemma _root_.MDifferentiableWithinAt.mpullback_vectorField_preimage_of_eq
    (hV : MDiffAt[t] (T% V) y₀) (hf : CMDiffAt n f x₀)
    (hf' : (mfderiv% f x₀).IsInvertible) (hmn : 2 ≤ n) (hy₀ : y₀ = f x₀)
    (hU : ∀ᶠ y in 𝓝[insert x₀ (f ⁻¹' t)] x₀, IsMRelatedWithinAt f U V univ y) :
    MDiffAt[f ⁻¹' t] (T% U) x₀ := by
  subst hy₀
  exact hV.mpullback_vectorField_preimage hf hf' hmn hU

/-- The pullback of a differentiable vector field by a `C^n` function with `2 ≤ n` is
differentiable. Version on a set, but with full pullback -/
protected lemma _root_.MDifferentiableOn.mpullback_vectorField_preimage
    (hV : MDiff[t] (T% V)) (hf : CMDiff n f)
    (hf' : ∀ x ∈ f ⁻¹' t, (mfderiv% f x).IsInvertible)
    (hmn : 2 ≤ n)
    (hU : ∀ y ∈ (f ⁻¹' t), IsMRelatedWithinAt f U V univ y) :
    MDiff[f ⁻¹' t] (T% U) :=
  fun x₀ hx₀ ↦ MDifferentiableWithinAt.mpullback_vectorField_preimage
    (hV _ hx₀) (hf x₀) (hf' _ hx₀) hmn (by
    rw [insert_eq_of_mem hx₀]
    exact eventually_nhdsWithin_of_forall fun y hy ↦ hU y hy)

/-- The pullback of a differentiable vector field by a `C^n` function with `2 ≤ n` is
differentiable. Version at a point. -/
protected lemma _root_.MDifferentiableAt.mpullback_vectorField
    (hV : MDiffAt (T% V) (f x₀)) (hf : CMDiffAt n f x₀)
    (hf' : (mfderiv% f x₀).IsInvertible) (hmn : 2 ≤ n)
    (hU : ∀ᶠ y in 𝓝 x₀, IsMRelatedWithinAt f U V univ y) :
    MDiffAt (T% U) x₀ := by
  simpa using! MDifferentiableWithinAt.mpullback_vectorField_preimage hV hf hf' hmn
    (by simpa using hU)

/-- The pullback of a differentiable vector field by a `C^n` function with `2 ≤ n` is
differentiable. -/
protected lemma _root_.MDifferentiable.mpullback_vectorField
    (hV : MDiff (T% V)) (hf : CMDiff n f) (hf' : ∀ x, (mfderiv% f x).IsInvertible) (hmn : 2 ≤ n)
    (hU : ∀ y, IsMRelatedWithinAt f U V univ y) :
    MDiff (T% U) :=
  fun x ↦ MDifferentiableAt.mpullback_vectorField (hV (f x)) (hf x) (hf' x) hmn
    (Eventually.of_forall hU)

end MDifferentiability


section ContMDiff

variable [CompleteSpace E] [IsManifold I 1 M] [IsManifold I' 1 M']

/-- The pullback of a `C^m` vector field by a `C^n` function with invertible derivative and
`m + 1 ≤ n` is `C^m`.
Version within a set at a point. -/
private lemma contMDiffWithinAt_of_related {r : Set M}
    (hV : CMDiffAt[t] m (T% V) (f x₀)) (hf : CMDiffAt[s] n f x₀)
    (hf' : (mfderiv[s] f x₀).IsInvertible)
    (hx₀ : x₀ ∈ s) (hs : UniqueMDiff[s]) (hmn : m + 1 ≤ n)
    (hrs : r ⊆ s) (hrt : MapsTo f r t)
    (hU : ∀ᶠ y in 𝓝[insert x₀ r] x₀, IsMRelatedWithinAt f U V s y) :
    CMDiffAt[r] m (T% U) x₀ := by
  let A y := inCoordinates E (TangentSpace I (M := M)) E' (TangentSpace I' (M := M'))
    x₀ y (f x₀) (f y) (mfderivWithin I I' f s y)
  have hA : ContMDiffWithinAt I 𝓘(𝕜, E →L[𝕜] E') m A s x₀ := hf.mfderivWithin_const hmn hx₀ hs
  have h₀ : (A x₀).IsInvertible := by
    dsimp only [A]
    rw [inCoordinates_eq (FiberBundle.mem_baseSet_trivializationAt' x₀)
      (FiberBundle.mem_baseSet_trivializationAt' (f x₀))]
    exact isInvertible_equiv.comp (hf'.comp isInvertible_equiv)
  obtain ⟨G, hG, he⟩ := exists_inverse_germ hA h₀
  have hv := (Bundle.contMDiffWithinAt_section.mp hV).comp x₀
    ((hf.of_le (le_trans le_self_add hmn)).mono hrs)
    hrt
  apply Bundle.contMDiffWithinAt_section.mpr
  apply ((hG.mono hrs).clm_apply hv).congr_of_eventuallyEq
  · have H := eventually_coord_lift hs hx₀ hrs hf.continuousWithinAt hU
    filter_upwards [H.filter_mono (nhdsWithin_mono _ (subset_insert ..)),
      he.filter_mono (nhdsWithin_mono _ hrs)] with y hy hGy
    exact (hGy _).symm.trans (congrArg (G y) hy)
  · have H := mem_of_mem_nhdsWithin (mem_insert ..)
      (eventually_coord_lift hs hx₀ hrs hf.continuousWithinAt hU)
    exact (mem_of_mem_nhdsWithin hx₀ he _).symm.trans (congrArg (G x₀) H)

protected lemma _root_.ContMDiffWithinAt.mpullbackWithin_vectorField_inter
    (hV : CMDiffAt[t] m (T% V) (f x₀)) (hf : CMDiffAt[s] n f x₀)
    (hf' : (mfderiv[s] f x₀).IsInvertible)
    (hx₀ : x₀ ∈ s) (hs : UniqueMDiff[s]) (hmn : m + 1 ≤ n)
    (hU : ∀ᶠ y in 𝓝[insert x₀ (s ∩ f ⁻¹' t)] x₀, IsMRelatedWithinAt f U V s y) :
    CMDiffAt[s ∩ f ⁻¹' t] m (T% U) x₀ :=
  contMDiffWithinAt_of_related hV hf hf' hx₀ hs hmn inter_subset_left
    ((mapsTo_preimage f t).mono_left inter_subset_right) hU

lemma _root_.ContMDiffWithinAt.mpullbackWithin_vectorField_inter_of_eq
    (hV : CMDiffAt[t] m (T% V) y₀) (hf : CMDiffAt[s] n f x₀) (hf' : (mfderiv[s] f x₀).IsInvertible)
    (hx₀ : x₀ ∈ s) (hs : UniqueMDiff[s]) (hmn : m + 1 ≤ n) (h : f x₀ = y₀)
    (hU : ∀ᶠ y in 𝓝[insert x₀ (s ∩ f ⁻¹' t)] x₀, IsMRelatedWithinAt f U V s y) :
    CMDiffAt[s ∩ f ⁻¹' t] m (T% U) x₀ := by
  subst h
  exact ContMDiffWithinAt.mpullbackWithin_vectorField_inter hV hf hf' hx₀ hs hmn hU

/-- The pullback of a `C^m` vector field by a `C^n` function with invertible derivative and
with `m + 1 ≤ n` is `C^m`.
Version within a set at a point. -/
protected lemma _root_.ContMDiffWithinAt.mpullbackWithin_vectorField_of_mem
    (hV : CMDiffAt[t] m (T% V) (f x₀)) (hf : CMDiffAt[s] n f x₀)
    (hf' : (mfderiv[s] f x₀).IsInvertible)
    (hx₀ : x₀ ∈ s) (hs : UniqueMDiff[s]) (hmn : m + 1 ≤ n) (hst : f ⁻¹' t ∈ 𝓝[s] x₀)
    (hU : ∀ᶠ y in 𝓝[insert x₀ s] x₀, IsMRelatedWithinAt f U V s y) :
    CMDiffAt[s] m (T% U) x₀ := by
  have hr := contMDiffWithinAt_of_related hV hf hf' hx₀ hs hmn
    inter_subset_left ((mapsTo_preimage f t).mono_left (inter_subset_right (s := s)))
    (hU.filter_mono (nhdsWithin_mono _ (insert_subset_insert inter_subset_left)))
  exact hr.mono_of_mem_nhdsWithin (inter_mem self_mem_nhdsWithin hst)

/-- The pullback of a `C^m` vector field by a `C^n` function with invertible derivative and
with `m + 1 ≤ n` is `C^m`.
Version within a set at a point. -/
protected lemma _root_.ContMDiffWithinAt.mpullbackWithin_vectorField_of_mem_of_eq
    (hV : CMDiffAt[t] m (T% V) y₀) (hf : CMDiffAt[s] n f x₀) (hf' : (mfderiv[s] f x₀).IsInvertible)
    (hx₀ : x₀ ∈ s) (hs : UniqueMDiff[s]) (hmn : m + 1 ≤ n) (hst : f ⁻¹' t ∈ 𝓝[s] x₀)
    (hy₀ : f x₀ = y₀)
    (hU : ∀ᶠ y in 𝓝[insert x₀ s] x₀, IsMRelatedWithinAt f U V s y) :
    CMDiffAt[s] m (T% U) x₀ := by
  subst hy₀
  exact ContMDiffWithinAt.mpullbackWithin_vectorField_of_mem hV hf hf' hx₀ hs hmn hst hU

/-- The pullback of a `C^m` vector field by a `C^n` function with invertible derivative and
with `m + 1 ≤ n` is `C^m`.
Version within a set at a point. -/
protected lemma _root_.ContMDiffWithinAt.mpullbackWithin_vectorField
    (hV : CMDiffAt[t] m (T% V) (f x₀)) (hf : CMDiffAt[s] n f x₀)
    (hf' : (mfderiv[s] f x₀).IsInvertible)
    (hx₀ : x₀ ∈ s) (hs : UniqueMDiff[s]) (hmn : m + 1 ≤ n) (hst : MapsTo f s t)
    (hU : ∀ᶠ y in 𝓝[insert x₀ s] x₀, IsMRelatedWithinAt f U V s y) :
    CMDiffAt[s] m (T% U) x₀ :=
  ContMDiffWithinAt.mpullbackWithin_vectorField_of_mem hV hf hf' hx₀ hs hmn
    hst.preimage_mem_nhdsWithin hU

/-- The pullback of a `C^m` vector field by a `C^n` function with invertible derivative and
with `m + 1 ≤ n` is `C^m`.
Version within a set at a point. -/
protected lemma _root_.ContMDiffWithinAt.mpullbackWithin_vectorField_of_eq
    (hV : CMDiffAt[t] m (T% V) y₀) (hf : CMDiffAt[s] n f x₀) (hf' : (mfderiv[s] f x₀).IsInvertible)
    (hx₀ : x₀ ∈ s) (hs : UniqueMDiff[s]) (hmn : m + 1 ≤ n) (hst : MapsTo f s t) (h : f x₀ = y₀)
    (hU : ∀ᶠ y in 𝓝[insert x₀ s] x₀, IsMRelatedWithinAt f U V s y) :
    CMDiffAt[s] m (T% U) x₀ := by
  subst h
  exact ContMDiffWithinAt.mpullbackWithin_vectorField hV hf hf' hx₀ hs hmn hst hU

/-- The pullback of a `C^m` vector field by a `C^n` function with invertible derivative and
with `m + 1 ≤ n` is `C^m`.
Version within a set at a point, with a set used for the pullback possibly larger. -/
protected lemma _root_.ContMDiffWithinAt.mpullbackWithin_vectorField' {u : Set M}
    (hV : CMDiffAt[t] m (T% V) (f x₀))
    (hf : CMDiffAt[u] n f x₀) (hf' : (mfderiv[u] f x₀).IsInvertible)
    (hx₀ : x₀ ∈ s) (hs : UniqueMDiff[s]) (hmn : m + 1 ≤ n)
    (hst : f ⁻¹' t ∈ 𝓝[s] x₀) (hu : s ⊆ u)
    (hU : ∀ᶠ y in 𝓝[insert x₀ s] x₀, IsMRelatedWithinAt f U V u y) :
    CMDiffAt[s] m (T% U) x₀ := by
  have hn : 1 ≤ n := le_trans (by simp) hmn
  have hh : (mfderiv[s] f x₀).IsInvertible := by
    convert! hf' using 1
    exact (hf.mdifferentiableWithinAt <| by positivity).mfderivWithin_mono (hs _ hx₀) hu
  exact hV.mpullbackWithin_vectorField_of_mem (hf.mono hu) hh hx₀ hs hmn hst
    (hU.mono fun _ hy ↦ hy.mono hu)

/-- The pullback of a `C^m` vector field by a `C^n` function with invertible derivative and
with `m + 1 ≤ n` is `C^m`.
Version within a set at a point, with a set used for the pullback possibly larger. -/
protected lemma _root_.ContMDiffWithinAt.mpullbackWithin_vectorField_of_eq' {u : Set M}
    (hV : CMDiffAt[t] m (T% V) y₀) (hf : CMDiffAt[u] n f x₀) (hf' : (mfderiv[u] f x₀).IsInvertible)
    (hx₀ : x₀ ∈ s) (hs : UniqueMDiff[s]) (hmn : m + 1 ≤ n) (hst : f ⁻¹' t ∈ 𝓝[s] x₀)
    (hu : s ⊆ u) (hy₀ : f x₀ = y₀)
    (hU : ∀ᶠ y in 𝓝[insert x₀ s] x₀, IsMRelatedWithinAt f U V u y) :
    CMDiffAt[s] m (T% U) x₀ := by
  subst hy₀
  exact ContMDiffWithinAt.mpullbackWithin_vectorField' hV hf hf' hx₀ hs hmn hst hu hU

/-- The pullback of a `C^m` vector field by a `C^n` function with invertible derivative and
with `m + 1 ≤ n` is `C^m`.
Version on a set. -/
protected lemma _root_.ContMDiffOn.mpullbackWithin_vectorField_inter
    (hV : CMDiff[t] m (T% V)) (hf : CMDiff[s] n f)
    (hf' : ∀ x ∈ s ∩ f ⁻¹' t, (mfderiv[s] f x).IsInvertible)
    (hs : UniqueMDiff[s]) (hmn : m + 1 ≤ n)
    (hU : ∀ y ∈ (s ∩ f ⁻¹' t), IsMRelatedWithinAt f U V s y) :
    CMDiff[s ∩ f ⁻¹' t] m (T% U) :=
  fun x₀ hx₀ ↦ ContMDiffWithinAt.mpullbackWithin_vectorField_inter
    (hV _ hx₀.2) (hf _ hx₀.1) (hf' _ hx₀) hx₀.1 hs hmn (by
    rw [insert_eq_of_mem hx₀]
    exact eventually_nhdsWithin_of_forall fun y hy ↦ hU y hy)

/-- The pullback of a `C^m` vector field by a `C^n` function with invertible derivative and
with `m + 1 ≤ n` is `C^m`.
Version within a set at a point, but with full pullback. -/
protected lemma _root_.ContMDiffWithinAt.mpullback_vectorField_preimage
    (hV : CMDiffAt[t] m (T% V) (f x₀)) (hf : CMDiffAt n f x₀)
    (hf' : (mfderiv% f x₀).IsInvertible) (hmn : m + 1 ≤ n)
    (hU : ∀ᶠ y in 𝓝[insert x₀ (f ⁻¹' t)] x₀, IsMRelatedWithinAt f U V univ y) :
    CMDiffAt[f ⁻¹' t] m (T% U) x₀ := by
  simp only [← contMDiffWithinAt_univ, ← mfderivWithin_univ] at hV hf hf' ⊢
  simpa using hV.mpullbackWithin_vectorField_inter hf hf' (mem_univ _) uniqueMDiffOn_univ hmn
    (by simpa using hU)

/-- The pullback of a `C^m` vector field by a `C^n` function with invertible derivative and
with `m + 1 ≤ n` is `C^m`.
Version within a set at a point, but with full pullback. -/
protected lemma _root_.ContMDiffWithinAt.mpullback_vectorField_preimage_of_eq
    (hV : CMDiffAt[t] m (T% V) y₀) (hf : CMDiffAt n f x₀)
    (hf' : (mfderiv% f x₀).IsInvertible) (hmn : m + 1 ≤ n) (hy₀ : y₀ = f x₀)
    (hU : ∀ᶠ y in 𝓝[insert x₀ (f ⁻¹' t)] x₀, IsMRelatedWithinAt f U V univ y) :
    CMDiffAt[f ⁻¹' t] m (T% U) x₀ := by
  subst hy₀
  exact ContMDiffWithinAt.mpullback_vectorField_preimage hV hf hf' hmn hU

/-- The pullback of a `C^m` vector field by a `C^n` function with invertible derivative and
with `m + 1 ≤ n` is `C^m`.
Version within a set at a point, but with full pullback. -/
protected lemma _root_.ContMDiffWithinAt.mpullback_vectorField_of_mem_nhdsWithin
    (hV : CMDiffAt[t] m (T% V) (f x₀)) (hf : CMDiffAt n f x₀)
    (hf' : (mfderiv% f x₀).IsInvertible) (hmn : m + 1 ≤ n) (hst : f ⁻¹' t ∈ 𝓝[s] x₀)
    (hU : ∀ᶠ y in 𝓝[insert x₀ s] x₀, IsMRelatedWithinAt f U V univ y) :
    CMDiffAt[s] m (T% U) x₀ := by
  have hr := contMDiffWithinAt_of_related hV hf.contMDiffWithinAt (by simpa using hf')
    (mem_univ _) uniqueMDiffOn_univ hmn
    (subset_univ _) ((mapsTo_preimage f t).mono_left (inter_subset_right (s := s)))
    (hU.filter_mono (nhdsWithin_mono _ (insert_subset_insert inter_subset_left)))
  exact hr.mono_of_mem_nhdsWithin (inter_mem self_mem_nhdsWithin hst)

/-- The pullback of a `C^m` vector field by a `C^n` function with invertible derivative and
with `m + 1 ≤ n` is `C^m`.
Version within a set at a point, but with full pullback. -/
protected lemma _root_.ContMDiffWithinAt.mpullback_vectorField_of_mem_nhdsWithin_of_eq
    (hV : CMDiffAt[t] m (T% V) y₀) (hf : CMDiffAt n f x₀)
    (hf' : (mfderiv% f x₀).IsInvertible) (hmn : m + 1 ≤ n)
    (hst : f ⁻¹' t ∈ 𝓝[s] x₀) (hy₀ : y₀ = f x₀)
    (hU : ∀ᶠ y in 𝓝[insert x₀ s] x₀, IsMRelatedWithinAt f U V univ y) :
    CMDiffAt[s] m (T% U) x₀ := by
  subst hy₀
  exact ContMDiffWithinAt.mpullback_vectorField_of_mem_nhdsWithin hV hf hf' hmn hst hU

/-- The pullback of a `C^m` vector field by a `C^n` function with invertible derivative and
with `m + 1 ≤ n` is `C^m`.
Version on a set, but with full pullback -/
protected lemma _root_.ContMDiffOn.mpullback_vectorField_preimage
    (hV : CMDiff[t] m (T% V)) (hf : CMDiff n f)
    (hf' : ∀ x ∈ f ⁻¹' t, (mfderiv% f x).IsInvertible) (hmn : m + 1 ≤ n)
    (hU : ∀ y ∈ (f ⁻¹' t), IsMRelatedWithinAt f U V univ y) :
    CMDiff[f ⁻¹' t] m (T% U) :=
  fun x₀ hx₀ ↦ ContMDiffWithinAt.mpullback_vectorField_preimage
    (hV _ hx₀) (hf x₀) (hf' _ hx₀) hmn (by
    rw [insert_eq_of_mem hx₀]
    exact eventually_nhdsWithin_of_forall fun y hy ↦ hU y hy)

/-- The pullback of a `C^m` vector field by a `C^n` function with invertible derivative and
with `m + 1 ≤ n` is `C^m`.
Version at a point. -/
protected lemma _root_.ContMDiffAt.mpullback_vectorField_preimage
    (hV : CMDiffAt m (T% V) (f x₀)) (hf : CMDiffAt n f x₀)
    (hf' : (mfderiv% f x₀).IsInvertible) (hmn : m + 1 ≤ n)
    (hU : ∀ᶠ y in 𝓝 x₀, IsMRelatedWithinAt f U V univ y) :
    CMDiffAt m (T% U) x₀ := by
  simp only [← contMDiffWithinAt_univ] at hV hf hf' ⊢
  simpa using ContMDiffWithinAt.mpullback_vectorField_preimage hV hf hf' hmn
    (by simpa using hU)

/-- The pullback of a `C^m` vector field by a `C^n` function with invertible derivative and
with `m + 1 ≤ n` is `C^m`. -/
protected lemma _root_.ContMDiff.mpullback_vectorField
    (hV : CMDiff m (T% V)) (hf : CMDiff n f)
    (hf' : ∀ x, (mfderiv% f x).IsInvertible) (hmn : m + 1 ≤ n)
    (hU : ∀ y, IsMRelatedWithinAt f U V univ y) :
    CMDiff m (T% U) :=
  fun x ↦ ContMDiffAt.mpullback_vectorField_preimage (hV (f x)) (hf x) (hf' x) hmn
    (Eventually.of_forall hU)
/-- A model-space field represents a manifold vector field in a chart when the forward chart
derivative sends the field to the representative on the chart source. -/
def InChart (I : ModelWithCorners 𝕜 E H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (a : M) (V : Π x : M, TangentSpace I x) (P : E → E) : Prop :=
  ∀ y ∈ (extChartAt I a).source, P (extChartAt I a y) = mfderiv I 𝓘(𝕜, E) (extChartAt I a) y (V y)

omit [CompleteSpace E] [IsManifold I 1 M] in
lemma exists_inChart (a : M) (V : Π x : M, TangentSpace I x) :
    ∃ P : E → E, InChart I a V P := by
  let e := extChartAt I a
  refine ⟨fun z ↦ mfderiv I 𝓘(𝕜, E) e (e.symm z) (V (e.symm z)), ?_⟩
  intro y hy
  exact congrArg (fun z : M ↦ mfderiv I 𝓘(𝕜, E) e z (V z)) (e.left_inv hy)

omit [CompleteSpace E] in
lemma InChart.isMRelatedWithinAt {a : M} {V : Π x : M, TangentSpace I x} {P : E → E}
    (hP : InChart I a V P) {y : E} (hy : y ∈ (extChartAt I a).target) :
    IsMRelatedWithinAt (I := 𝓘(𝕜, E)) (extChartAt I a).symm P V (range I) y := by
  let e := extChartAt I a
  refine ⟨_, (mdifferentiableWithinAt_extChartAt_symm hy).hasMFDerivWithinAt, ?_⟩
  have h := hP (e.symm y) (e.map_target hy)
  change P (e (e.symm y)) = _ at h
  rw [e.right_inv hy] at h
  rw [h]
  exact congrArg (fun A : TangentSpace I (e.symm y) →L[𝕜] TangentSpace I (e.symm y) ↦
    A (V (e.symm y))) (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt hy)

lemma contMDiffWithinAt_mpullbackWithin_extChartAt_symm
    {V : Π (x : M), TangentSpace I x} {P : E → E} (hP : InChart I x V P)
    (hV : CMDiffAt[s] m (T% V) x)
    (hs : UniqueMDiff[s]) (hx : x ∈ s) (hmn : m + 1 ≤ n) :
    ContMDiffWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E).tangent m
      (fun y : E ↦ (⟨y, P y⟩ : TangentBundle 𝓘(𝕜, E) E))
      ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) (extChartAt I x x) :=
  ContMDiffWithinAt.mpullbackWithin_vectorField_of_eq'
    (U := fun y : E ↦ (P y : TangentSpace 𝓘(𝕜, E) y)) hV
    (contMDiffWithinAt_extChartAt_symm_range_self (n := n) x)
    (isInvertible_mfderivWithin_extChartAt_symm (mem_extChartAt_target x))
    (by simp [hx]) (UniqueMDiffOn.uniqueMDiffOn_target_inter hs x) hmn
    ((mapsTo_preimage _ _).mono_left inter_subset_right).preimage_mem_nhdsWithin
    (Subset.trans inter_subset_left (extChartAt_target_subset_range x)) (extChartAt_to_inv x) (by
      rw [insert_eq_of_mem (show extChartAt I x x ∈
        (extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s from
        ⟨mem_extChartAt_target x,
        by simpa only [mem_preimage, extChartAt_to_inv] using hx⟩)]
      exact eventually_nhdsWithin_of_forall fun y hy ↦ hP.isMRelatedWithinAt hy.1)

lemma eventually_contMDiffWithinAt_mpullbackWithin_extChartAt_symm
    {V : Π (x : M), TangentSpace I x} {P : E → E} (hP : InChart I x V P)
    (hV : CMDiffAt[s] m (T% V) x)
    (hs : UniqueMDiff[s]) (hx : x ∈ s) (hmn : m + 1 ≤ n) (hm : m ≠ ∞) :
    ∀ᶠ y in 𝓝[s] x, ContMDiffWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E).tangent m
      (fun z : E ↦ (⟨z, P z⟩ : TangentBundle 𝓘(𝕜, E) E))
      ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) (extChartAt I x y) := by
  have T := nhdsWithin_mono _ (subset_insert _ _)
    ((contMDiffWithinAt_iff_contMDiffWithinAt_nhdsWithin hm).1
      (contMDiffWithinAt_mpullbackWithin_extChartAt_symm hP hV hs hx hmn))
  have A := (continuousAt_extChartAt (I := I) x).continuousWithinAt.preimage_mem_nhdsWithin'' T rfl
  apply (nhdsWithin_le_iff.2 _) A
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (extChartAt_source_mem_nhds (I := I) x)]
    with y hy h'y
  simp only [mfld_simps] at hy h'y
  simp [hy, h'y]

set_option backward.isDefEq.respectTransparency false in
omit [CompleteSpace E] in
lemma eventuallyEq_mpullback_mpullbackWithin_extChartAt
    {V Q : Π y : M, TangentSpace I y} {P : E → E} (hP : InChart I x V P)
    (hQ : ∀ᶠ y in 𝓝[s] x, IsMRelatedWithinAt (I' := 𝓘(𝕜, E)) (extChartAt I x) Q P univ y) :
    V =ᶠ[𝓝[s] x] Q := by
  filter_upwards [hQ, nhdsWithin_le_nhds (extChartAt_source_mem_nhds (I := I) x)] with y hy hys
  have hinj : Injective (mfderiv I 𝓘(𝕜, E) (extChartAt I x) y) := by
    obtain ⟨e, he⟩ := isInvertible_mfderiv_extChartAt hys
    rw [← he]
    exact e.injective
  apply hinj
  exact (hP y hys).symm.trans (by
    simpa using (hy.mfderivWithin_apply (uniqueMDiffWithinAt_univ I)).symm)

end ContMDiff

end Pullback

end VectorField
