/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# One-dimensional iterated derivatives

We define the `n`-th derivative of a function `f : 𝕜 → F` as a function
`iteratedDeriv n f : 𝕜 → F`, as well as a version on domains `iteratedDerivWithin n f s : 𝕜 → F`,
and prove their basic properties.

## Main definitions and results

Let `𝕜` be a nontrivially normed field, and `F` a normed vector space over `𝕜`. Let `f : 𝕜 → F`.

* `iteratedDeriv n f` is the `n`-th derivative of `f`, seen as a function from `𝕜` to `F`.
  It is defined as the `n`-th Fréchet derivative (which is a multilinear map) applied to the
  vector `(1, ..., 1)`, to take advantage of all the existing framework, but we show that it
  coincides with the naive iterative definition.
* `iteratedDeriv_eq_iterate` states that the `n`-th derivative of `f` is obtained by starting
  from `f` and differentiating it `n` times.
* `iteratedDerivWithin n f s` is the `n`-th derivative of `f` within the domain `s`. It only
  behaves well when `s` has the unique derivative property.
* `iteratedDerivWithin_eq_iterate` states that the `n`-th derivative of `f` in the domain `s` is
  obtained by starting from `f` and differentiating it `n` times within `s`. This only holds when
  `s` has the unique derivative property.

## Implementation details

The results are deduced from the corresponding results for the more general (multilinear) iterated
Fréchet derivative. For this, we write `iteratedDeriv n f` as the composition of
`iteratedFDeriv 𝕜 n f` and a continuous linear equiv. As continuous linear equivs respect
differentiability and commute with differentiation, this makes it possible to prove readily that
the derivative of the `n`-th derivative is the `n+1`-th derivative in `iteratedDerivWithin_succ`,
by translating the corresponding result `iteratedFDerivWithin_succ_apply_left` for the
iterated Fréchet derivative.
-/

@[expose] public section

noncomputable section

open scoped Topology ContDiff
open Filter Set

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The relation specifying an iterated scalar derivative on an actual coordinate domain.
Order zero is evaluation, and order one requires differentiability only at the point.
When another derivative follows, the first derivative must exist on a neighborhood.
The witness functions are used only inside this relation; no value is chosen where
differentiability or uniqueness fails. -/
def HasIteratedDerivAt {D : Type*} [TopologicalSpace D] (n : ℕ) (f : D → F)
    (d : F) (x : D) (coord : D → 𝕜 := by exact _root_.id) : Prop :=
  match n with
  | 0 => f x = d
  | n + 1 => ∃ g : D → F, HasDerivAt f (g x) x coord ∧
      (n = 0 ∨ ∀ᶠ y in 𝓝 x, HasDerivAt f (g y) y coord) ∧
      HasIteratedDerivAt n g d x coord

namespace HasIteratedDerivAt

variable {D : Type*} [TopologicalSpace D] {coord : D → 𝕜}
  {f f₁ : D → F} {d e : F} {x : D} {n : ℕ}

@[simp] theorem zero : HasIteratedDerivAt 0 f d x coord ↔ f x = d := Iff.rfl

@[simp] theorem one : HasIteratedDerivAt 1 f d x coord ↔ HasDerivAt f d x coord := by
  constructor
  · rintro ⟨g, hg, _, hzero⟩
    change g x = d at hzero
    simpa only [hzero] using hg
  · intro h
    exact ⟨fun _ ↦ d, h, Or.inl rfl, rfl⟩

theorem succ_succ : HasIteratedDerivAt (n + 2) f d x coord ↔
    ∃ g : D → F, HasDerivAt f (g x) x coord ∧
      (∀ᶠ y in 𝓝 x, HasDerivAt f (g y) y coord) ∧
      HasIteratedDerivAt (n + 1) g d x coord := by
  change (∃ g : D → F, HasDerivAt f (g x) x coord ∧
    (n + 1 = 0 ∨ ∀ᶠ y in 𝓝 x, HasDerivAt f (g y) y coord) ∧
    HasIteratedDerivAt (n + 1) g d x coord) ↔ _
  simp only [Nat.add_one_ne_zero, false_or]

/-- Iterated differentiation depends only on the local function on its actual domain. -/
theorem congr_of_eventuallyEq (h : HasIteratedDerivAt n f d x coord)
    (heq : f₁ =ᶠ[𝓝 x] f) : HasIteratedDerivAt n f₁ d x coord := by
  have hcongr {u v : D → F} {y : D} {a : F}
      (hd : HasDerivAt u a y coord) (huv : v =ᶠ[𝓝 y] u) : HasDerivAt v a y coord := by
    change HasFDerivAt v (ContinuousLinearMap.toSpanSingleton 𝕜 a) y coord
    rw [hasFDerivAt_iff_isLittleOTVS]
    apply hd.hasFDerivAt.isLittleOTVS.congr' _ Filter.EventuallyEq.rfl
    filter_upwards [huv] with z hz
    simp only [hz, huv.self_of_nhds]
  cases n with
  | zero => exact heq.self_of_nhds.trans h
  | succ n =>
    obtain ⟨g, hg, hlocal, hn⟩ := h
    refine ⟨g, hcongr hg heq, ?_, hn⟩
    rcases hlocal with hn | hg'
    · exact Or.inl hn
    · right
      filter_upwards [hg', heq.eventually_nhds] with y hy heqy
      exact hcongr hy heqy

/-- Pull back an iterated derivative along a continuous map of actual domains, pulling back
the coordinates at the same time. This asserts existence, not uniqueness on the new domain. -/
theorem comp_domain {D' : Type*} [TopologicalSpace D'] {g : D' → D} {x : D'}
    (h : HasIteratedDerivAt n f d (g x) coord) (hg : Continuous g) :
    HasIteratedDerivAt n (f ∘ g) d x (coord ∘ g) := by
  have hpull {u : D → F} {a : F} {y : D'} (hu : HasDerivAt u a (g y) coord) :
      HasDerivAt (u ∘ g) a y (coord ∘ g) :=
    hu.hasFDerivAt.comp_tendsto g
      (hg.continuousAt.tendsto.prodMap (tendsto_pure_pure _ _))
  induction n generalizing f d with
  | zero => exact h
  | succ n ih =>
    obtain ⟨q, hq, hlocal, hn⟩ := h
    refine ⟨q ∘ g, hpull hq, ?_, ih hn⟩
    rcases hlocal with hn | hq'
    · exact Or.inl hn
    · right
      filter_upwards [hg.continuousAt.tendsto.eventually hq'] with y hy
      exact hpull hy

/-- Multiplication by a constant commutes with the iterated derivative relation. -/
theorem const_smul (h : HasIteratedDerivAt n f d x coord) (c : 𝕜) :
    HasIteratedDerivAt n (fun y ↦ c • f y) (c • d) x coord := by
  have hsmul {u : D → F} {a : F} {y : D} (hu : HasDerivAt u a y coord) :
      HasDerivAt (fun z ↦ c • u z) (c • a) y coord := by
    simpa only [Pi.smul_def, smul_apply,
      ContinuousLinearMap.toSpanSingleton_apply, one_smul] using
      (hu.hasFDerivAt.const_smul c).hasDerivAt
  induction n generalizing f d with
  | zero => exact congrArg (c • ·) h
  | succ n ih =>
    obtain ⟨g, hg, hlocal, hn⟩ := h
    refine ⟨fun y ↦ c • g y, hsmul hg, ?_, ih hn⟩
    rcases hlocal with hn | hg'
    · exact Or.inl hn
    · exact Or.inr (hg'.mono fun y hy ↦ hsmul hy)

/-- Open coordinate embeddings ensure uniqueness, without restricting the derivative relation
itself to this sufficient class of domains. -/
theorem unique (h : HasIteratedDerivAt n f d x coord)
    (h' : HasIteratedDerivAt n f e x coord)
    (hcoord : Topology.IsOpenEmbedding coord := by exact Topology.IsOpenEmbedding.id) : d = e := by
  induction n generalizing f d e with
  | zero => exact h.symm.trans h'
  | succ n ih =>
    obtain ⟨g, hg, hglocal, hgn⟩ := h
    obtain ⟨q, hq, hqlocal, hqn⟩ := h'
    by_cases hn : n = 0
    · subst n
      change g x = d at hgn
      change q x = e at hqn
      exact hgn.symm.trans (((hg.deriv hcoord).symm.trans (hq.deriv hcoord)).trans hqn)
    · have hge := hglocal.resolve_left hn
      have hqe := hqlocal.resolve_left hn
      have heq : q =ᶠ[𝓝 x] g := by
        filter_upwards [hge, hqe] with y hgy hqy
        exact (hqy.deriv hcoord).symm.trans (hgy.deriv hcoord)
      exact ih (hgn.congr_of_eventuallyEq heq) hqn

end HasIteratedDerivAt

/-- The `n`-th iterated derivative of a function from `𝕜` to `F`, as a function from `𝕜` to `F`. -/
def iteratedDeriv (n : ℕ) (f : 𝕜 → F) (x : 𝕜) : F :=
  (iteratedFDeriv 𝕜 n f x : (Fin n → 𝕜) → F) fun _ : Fin n => 1

/-- The `n`-th iterated derivative of a function from `𝕜` to `F` within a set `s`, as a function
from `𝕜` to `F`. -/
def iteratedDerivWithin (n : ℕ) (f : 𝕜 → F) (s : Set 𝕜) (x : 𝕜) : F :=
  (iteratedFDerivWithin 𝕜 n f s x : (Fin n → 𝕜) → F) fun _ : Fin n => 1

variable {n : ℕ} {f : 𝕜 → F} {s : Set 𝕜} {x : 𝕜}

@[simp]
theorem iteratedDerivWithin_univ : iteratedDerivWithin n f univ = iteratedDeriv n f := by
  ext x
  rw [iteratedDerivWithin, iteratedDeriv, iteratedFDerivWithin_univ]

theorem iteratedDerivWithin_eq_iteratedDeriv (hs : UniqueDiffOn 𝕜 s) (h : ContDiffAt 𝕜 n f x)
    (hx : x ∈ s) : iteratedDerivWithin n f s x = iteratedDeriv n f x := by
  rw [iteratedDerivWithin, iteratedDeriv, iteratedFDerivWithin_eq_iteratedFDeriv hs h hx]

/-! ### Properties of the iterated derivative within a set -/


theorem iteratedDerivWithin_eq_iteratedFDerivWithin : iteratedDerivWithin n f s x =
    (iteratedFDerivWithin 𝕜 n f s x : (Fin n → 𝕜) → F) fun _ : Fin n => 1 :=
  rfl

/-- Write the iterated derivative as the composition of a continuous linear equiv and the iterated
Fréchet derivative -/
theorem iteratedDerivWithin_eq_equiv_comp : iteratedDerivWithin n f s =
    (ContinuousMultilinearMap.piFieldEquiv 𝕜 (Fin n) F).symm ∘ iteratedFDerivWithin 𝕜 n f s := by
  ext x; rfl

/-- Write the iterated Fréchet derivative as the composition of a continuous linear equiv and the
iterated derivative. -/
theorem iteratedFDerivWithin_eq_equiv_comp :
    iteratedFDerivWithin 𝕜 n f s =
      ContinuousMultilinearMap.piFieldEquiv 𝕜 (Fin n) F ∘ iteratedDerivWithin n f s := by
  rw [iteratedDerivWithin_eq_equiv_comp, ← Function.comp_assoc, LinearIsometryEquiv.self_comp_symm,
    Function.id_comp]

/-- The `n`-th Fréchet derivative applied to a vector `(m 0, ..., m (n-1))` is the derivative
multiplied by the product of the `m i`s. -/
theorem iteratedFDerivWithin_apply_eq_iteratedDerivWithin_mul_prod {m : Fin n → 𝕜} :
    (iteratedFDerivWithin 𝕜 n f s x : (Fin n → 𝕜) → F) m =
      (∏ i, m i) • iteratedDerivWithin n f s x := by
  rw [iteratedDerivWithin_eq_iteratedFDerivWithin, ← ContinuousMultilinearMap.map_smul_univ]
  simp

theorem norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin :
    ‖iteratedFDerivWithin 𝕜 n f s x‖ = ‖iteratedDerivWithin n f s x‖ := by
  rw [iteratedDerivWithin_eq_equiv_comp, Function.comp_apply, LinearIsometryEquiv.norm_map]

@[simp]
theorem iteratedDerivWithin_zero : iteratedDerivWithin 0 f s = f := by
  ext x
  simp [iteratedDerivWithin]

@[simp]
theorem iteratedDerivWithin_one :
    iteratedDerivWithin 1 f s = derivWithin f s := by
  ext x
  by_cases hsx : AccPt x (𝓟 s)
  · simp only [iteratedDerivWithin, iteratedFDerivWithin_one_apply hsx.uniqueDiffWithinAt,
      derivWithin]
  · simp [derivWithin_zero_of_not_accPt hsx, iteratedDerivWithin, iteratedFDerivWithin,
      fderivWithin_zero_of_not_accPt hsx]

/-- If the first `n` derivatives within a set of a function are continuous, and its first `n-1`
derivatives are differentiable, then the function is `C^n`. This is not an equivalence in general,
but this is an equivalence when the set has unique derivatives, see
`contDiffOn_iff_continuousOn_differentiableOn_deriv`. -/
theorem contDiffOn_of_continuousOn_differentiableOn_deriv {n : ℕ∞}
    (Hcont : ∀ m : ℕ, (m : ℕ∞) ≤ n → ContinuousOn (fun x => iteratedDerivWithin m f s x) s)
    (Hdiff : ∀ m : ℕ, (m : ℕ∞) < n → DifferentiableOn 𝕜 (fun x => iteratedDerivWithin m f s x) s) :
    ContDiffOn 𝕜 n f s := by
  apply contDiffOn_of_continuousOn_differentiableOn
  · simpa only [iteratedFDerivWithin_eq_equiv_comp, LinearIsometryEquiv.comp_continuousOn_iff]
  · simpa only [iteratedFDerivWithin_eq_equiv_comp, LinearIsometryEquiv.comp_differentiableOn_iff]

/-- To check that a function is `n` times continuously differentiable, it suffices to check that its
first `n` derivatives are differentiable. This is slightly too strong as the condition we
require on the `n`-th derivative is differentiability instead of continuity, but it has the
advantage of avoiding the discussion of continuity in the proof (and for `n = ∞` this is optimal).
-/
theorem contDiffOn_of_differentiableOn_deriv {n : ℕ∞}
    (h : ∀ m : ℕ, (m : ℕ∞) ≤ n → DifferentiableOn 𝕜 (iteratedDerivWithin m f s) s) :
    ContDiffOn 𝕜 n f s := by
  apply contDiffOn_of_differentiableOn
  simpa only [iteratedFDerivWithin_eq_equiv_comp, LinearIsometryEquiv.comp_differentiableOn_iff]

/-- On a set with unique derivatives, a `C^n` function has derivatives up to `n` which are
continuous. -/
theorem ContDiffOn.continuousOn_iteratedDerivWithin
    {n : ℕ∞ω} {m : ℕ} (h : ContDiffOn 𝕜 n f s)
    (hmn : m ≤ n) (hs : UniqueDiffOn 𝕜 s) : ContinuousOn (iteratedDerivWithin m f s) s := by
  simpa only [iteratedDerivWithin_eq_equiv_comp, LinearIsometryEquiv.comp_continuousOn_iff] using
    h.continuousOn_iteratedFDerivWithin hmn hs

theorem ContDiffWithinAt.differentiableWithinAt_iteratedDerivWithin {n : ℕ∞ω} {m : ℕ}
    (h : ContDiffWithinAt 𝕜 n f s x) (hmn : m < n) (hs : UniqueDiffOn 𝕜 (insert x s)) :
    DifferentiableWithinAt 𝕜 (iteratedDerivWithin m f s) s x := by
  simpa only [iteratedDerivWithin_eq_equiv_comp,
    LinearIsometryEquiv.comp_differentiableWithinAt_iff] using
    h.differentiableWithinAt_iteratedFDerivWithin hmn hs

/-- On a set with unique derivatives, a `C^n` function has derivatives less than `n` which are
differentiable. -/
theorem ContDiffOn.differentiableOn_iteratedDerivWithin {n : ℕ∞ω} {m : ℕ}
    (h : ContDiffOn 𝕜 n f s) (hmn : m < n) (hs : UniqueDiffOn 𝕜 s) :
    DifferentiableOn 𝕜 (iteratedDerivWithin m f s) s := fun x hx =>
  (h x hx).differentiableWithinAt_iteratedDerivWithin hmn <| by rwa [insert_eq_of_mem hx]

/-- The property of being `C^n`, initially defined in terms of the Fréchet derivative, can be
reformulated in terms of the one-dimensional derivative on sets with unique derivatives. -/
theorem contDiffOn_iff_continuousOn_differentiableOn_deriv {n : ℕ∞} (hs : UniqueDiffOn 𝕜 s) :
    ContDiffOn 𝕜 n f s ↔ (∀ m : ℕ, (m : ℕ∞) ≤ n → ContinuousOn (iteratedDerivWithin m f s) s) ∧
      ∀ m : ℕ, (m : ℕ∞) < n → DifferentiableOn 𝕜 (iteratedDerivWithin m f s) s := by
  simp only [contDiffOn_iff_continuousOn_differentiableOn hs, iteratedFDerivWithin_eq_equiv_comp,
    LinearIsometryEquiv.comp_continuousOn_iff, LinearIsometryEquiv.comp_differentiableOn_iff]

/-- The property of being `C^n`, initially defined in terms of the Fréchet derivative, can be
reformulated in terms of the one-dimensional derivative on sets with unique derivatives. -/
theorem contDiffOn_nat_iff_continuousOn_differentiableOn_deriv {n : ℕ} (hs : UniqueDiffOn 𝕜 s) :
    ContDiffOn 𝕜 n f s ↔ (∀ m : ℕ, m ≤ n → ContinuousOn (iteratedDerivWithin m f s) s) ∧
      ∀ m : ℕ, m < n → DifferentiableOn 𝕜 (iteratedDerivWithin m f s) s := by
  rw [show n = ((n : ℕ∞) : ℕ∞ω) from rfl,
    contDiffOn_iff_continuousOn_differentiableOn_deriv hs]
  simp

/-- The `n+1`-th iterated derivative within a set with unique derivatives can be obtained by
differentiating the `n`-th iterated derivative. -/
theorem iteratedDerivWithin_succ :
    iteratedDerivWithin (n + 1) f s = derivWithin (iteratedDerivWithin n f s) s := by
  ext x
  by_cases hxs : AccPt x (𝓟 s)
  · rw [iteratedDerivWithin_eq_iteratedFDerivWithin, iteratedFDerivWithin_succ_apply_left,
      iteratedFDerivWithin_eq_equiv_comp,
      LinearIsometryEquiv.comp_fderivWithin _ hxs.uniqueDiffWithinAt, derivWithin]
    change ((ContinuousMultilinearMap.mkPiRing 𝕜 (Fin n) ((fderivWithin 𝕜
      (iteratedDerivWithin n f s) s x : 𝕜 → F) 1) : (Fin n → 𝕜) → F) fun _ : Fin n => 1) =
      (fderivWithin 𝕜 (iteratedDerivWithin n f s) s x : 𝕜 → F) 1
    simp
  · simp [derivWithin_zero_of_not_accPt hxs, iteratedDerivWithin, iteratedFDerivWithin,
      fderivWithin_zero_of_not_accPt hxs]

/-- The `n`-th iterated derivative within a set with unique derivatives can be obtained by
iterating `n` times the differentiation operation. -/
theorem iteratedDerivWithin_eq_iterate {x : 𝕜} :
    iteratedDerivWithin n f s x = (fun g : 𝕜 → F => derivWithin g s)^[n] f x := by
  induction n generalizing x with
  | zero => simp
  | succ n IH =>
    rw [iteratedDerivWithin_succ, Function.iterate_succ']
    exact derivWithin_congr (fun y hy => IH) IH

/-- The `n+1`-th iterated derivative within a set with unique derivatives can be obtained by
taking the `n`-th derivative of the derivative. -/
theorem iteratedDerivWithin_succ' :
    iteratedDerivWithin (n + 1) f s = (iteratedDerivWithin n (derivWithin f s) s) := by
  ext x; rw [iteratedDerivWithin_eq_iterate, iteratedDerivWithin_eq_iterate]; rfl

/-- `C^{n + 1}` is equivalent to `C^n` and the `n`-th derivative being `C^1`. -/
theorem contDiffOn_nat_succ_iff_contDiffOn_one_iteratedDerivWithin {n : ℕ}
    (hs : UniqueDiffOn 𝕜 s) : ContDiffOn 𝕜 (n + 1 : ℕ) f s ↔
      ContDiffOn 𝕜 n f s ∧ ContDiffOn 𝕜 1 (iteratedDerivWithin n f s) s := by
  simp only [contDiffOn_nat_iff_continuousOn_differentiableOn_deriv, hs,
    contDiffOn_one_iff_derivWithin, ← iteratedDerivWithin_succ]
  grind

/-! ### Properties of the iterated derivative on the whole space -/


theorem iteratedDeriv_eq_iteratedFDeriv :
    iteratedDeriv n f x = (iteratedFDeriv 𝕜 n f x : (Fin n → 𝕜) → F) fun _ : Fin n => 1 :=
  rfl

/-- Write the iterated derivative as the composition of a continuous linear equiv and the iterated
Fréchet derivative -/
theorem iteratedDeriv_eq_equiv_comp : iteratedDeriv n f =
    (ContinuousMultilinearMap.piFieldEquiv 𝕜 (Fin n) F).symm ∘ iteratedFDeriv 𝕜 n f := by
  ext x; rfl

/-- Write the iterated Fréchet derivative as the composition of a continuous linear equiv and the
iterated derivative. -/
theorem iteratedFDeriv_eq_equiv_comp : iteratedFDeriv 𝕜 n f =
    ContinuousMultilinearMap.piFieldEquiv 𝕜 (Fin n) F ∘ iteratedDeriv n f := by
  rw [iteratedDeriv_eq_equiv_comp, ← Function.comp_assoc, LinearIsometryEquiv.self_comp_symm,
    Function.id_comp]

/-- The `n`-th Fréchet derivative applied to a vector `(m 0, ..., m (n-1))` is the derivative
multiplied by the product of the `m i`s. -/
theorem iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod {m : Fin n → 𝕜} :
    (iteratedFDeriv 𝕜 n f x : (Fin n → 𝕜) → F) m = (∏ i, m i) • iteratedDeriv n f x := by
  rw [iteratedDeriv_eq_iteratedFDeriv, ← ContinuousMultilinearMap.map_smul_univ]; simp

theorem norm_iteratedFDeriv_eq_norm_iteratedDeriv :
    ‖iteratedFDeriv 𝕜 n f x‖ = ‖iteratedDeriv n f x‖ := by
  rw [iteratedDeriv_eq_equiv_comp, Function.comp_apply, LinearIsometryEquiv.norm_map]

@[simp]
theorem iteratedDeriv_zero : iteratedDeriv 0 f = f := by ext x; simp [iteratedDeriv]

@[simp]
theorem iteratedDeriv_one : iteratedDeriv 1 f = deriv f := by ext x; simp [iteratedDeriv]

/-- The property of being `C^n`, initially defined in terms of the Fréchet derivative, can be
reformulated in terms of the one-dimensional derivative. -/
theorem contDiff_iff_iteratedDeriv {n : ℕ∞} : ContDiff 𝕜 n f ↔
    (∀ m : ℕ, (m : ℕ∞) ≤ n → Continuous (iteratedDeriv m f)) ∧
      ∀ m : ℕ, (m : ℕ∞) < n → Differentiable 𝕜 (iteratedDeriv m f) := by
  simp only [contDiff_iff_continuous_differentiable, iteratedFDeriv_eq_equiv_comp,
    LinearIsometryEquiv.comp_continuous_iff, LinearIsometryEquiv.comp_differentiable_iff]

/-- The property of being `C^n`, initially defined in terms of the Fréchet derivative, can be
reformulated in terms of the one-dimensional derivative. -/
theorem contDiff_nat_iff_iteratedDeriv {n : ℕ} : ContDiff 𝕜 n f ↔
    (∀ m : ℕ, m ≤ n → Continuous (iteratedDeriv m f)) ∧
      ∀ m : ℕ, m < n → Differentiable 𝕜 (iteratedDeriv m f) := by
  rw [← WithTop.coe_natCast, contDiff_iff_iteratedDeriv]
  simp

/-- To check that a function is `n` times continuously differentiable, it suffices to check that its
first `n` derivatives are differentiable. This is slightly too strong as the condition we
require on the `n`-th derivative is differentiability instead of continuity, but it has the
advantage of avoiding the discussion of continuity in the proof (and for `n = ∞` this is optimal).
-/
theorem contDiff_of_differentiable_iteratedDeriv {n : ℕ∞}
    (h : ∀ m : ℕ, (m : ℕ∞) ≤ n → Differentiable 𝕜 (iteratedDeriv m f)) : ContDiff 𝕜 n f :=
  contDiff_iff_iteratedDeriv.2 ⟨fun m hm => (h m hm).continuous, fun m hm => h m (le_of_lt hm)⟩

theorem ContDiff.continuous_iteratedDeriv {n : ℕ∞ω} (m : ℕ) (h : ContDiff 𝕜 n f)
    (hmn : m ≤ n) : Continuous (iteratedDeriv m f) :=
  (contDiff_iff_iteratedDeriv.1 (h.of_le hmn)).1 m le_rfl

@[fun_prop]
theorem ContDiff.continuous_iteratedDeriv' (m : ℕ) (h : ContDiff 𝕜 m f) :
    Continuous (iteratedDeriv m f) :=
  ContDiff.continuous_iteratedDeriv m h (le_refl _)

theorem ContDiff.differentiable_iteratedDeriv {n : ℕ∞ω} (m : ℕ) (h : ContDiff 𝕜 n f)
    (hmn : m < n) : Differentiable 𝕜 (iteratedDeriv m f) :=
  (contDiff_iff_iteratedDeriv.1 (h.of_le (ENat.add_one_natCast_le_withTop_of_lt hmn))).2 m
    (mod_cast (lt_add_one m))

@[fun_prop]
theorem ContDiff.differentiable_iteratedDeriv' (m : ℕ) (h : ContDiff 𝕜 (m + 1) f) :
    Differentiable 𝕜 (iteratedDeriv m f) :=
  h.differentiable_iteratedDeriv m (Nat.cast_lt.mpr m.lt_succ_self)

/-- The `n+1`-th iterated derivative can be obtained by differentiating the `n`-th
iterated derivative. -/
theorem iteratedDeriv_succ : iteratedDeriv (n + 1) f = deriv (iteratedDeriv n f) := by
  rw [← iteratedDerivWithin_univ, ← iteratedDerivWithin_univ, ← derivWithin_univ]
  exact iteratedDerivWithin_succ

/-- The `n`-th iterated derivative can be obtained by iterating `n` times the
differentiation operation. -/
theorem iteratedDeriv_eq_iterate : iteratedDeriv n f = deriv^[n] f := by
  induction n with
  | zero => rw [iteratedDeriv_zero, Function.iterate_zero_apply]
  | succ n ih => rw [iteratedDeriv_succ, ih, Function.iterate_succ_apply']

theorem iteratedDerivWithin_of_isOpen (hs : IsOpen s) :
    Set.EqOn (iteratedDerivWithin n f s) (iteratedDeriv n f) s := by
  intro x hx
  simp_rw [iteratedDerivWithin, iteratedDeriv, iteratedFDerivWithin_of_isOpen n hs hx]

theorem iteratedDerivWithin_congr_right_of_isOpen (f : 𝕜 → F) (n : ℕ) {s t : Set 𝕜} (hs : IsOpen s)
    (ht : IsOpen t) : (s ∩ t).EqOn (iteratedDerivWithin n f s) (iteratedDerivWithin n f t) := by
  intro r hr
  rw [iteratedDerivWithin_of_isOpen hs hr.1, iteratedDerivWithin_of_isOpen ht hr.2]

theorem iteratedDerivWithin_of_isOpen_eq_iterate (hs : IsOpen s) :
    EqOn (iteratedDerivWithin n f s) (deriv^[n] f) s := by
  apply Set.EqOn.trans (iteratedDerivWithin_of_isOpen hs)
  rw [iteratedDeriv_eq_iterate]
  exact Set.eqOn_refl _ _

/-- The `n+1`-th iterated derivative can be obtained by taking the `n`-th derivative of the
derivative. -/
theorem iteratedDeriv_succ' : iteratedDeriv (n + 1) f = iteratedDeriv n (deriv f) := by
  rw [iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate, Function.iterate_succ_apply]

/-- On the domain where the iterated derivative relation holds, the existing ambient
projection agrees with it. No nondifferentiable or nonunique branch is used. -/
theorem HasIteratedDerivAt.iteratedDeriv {n : ℕ} {f : 𝕜 → F} {d : F} {x : 𝕜}
    (h : HasIteratedDerivAt n f d x) : iteratedDeriv n f x = d := by
  induction n generalizing f d with
  | zero => simpa only [iteratedDeriv_zero] using HasIteratedDerivAt.zero.mp h
  | succ n ih =>
    obtain ⟨g, hg, hlocal, hn⟩ := h
    rw [iteratedDeriv_succ']
    by_cases hn0 : n = 0
    · subst n
      change g x = d at hn
      simpa only [iteratedDeriv_zero] using hg.deriv.trans hn
    · have heq : deriv f =ᶠ[𝓝 x] g := by
        filter_upwards [hlocal.resolve_left hn0] with y hy
        exact hy.deriv
      exact ih (hn.congr_of_eventuallyEq heq)

/-- Analyticity supplies every finite derivative tower, with its genuine ambient value. -/
theorem AnalyticAt.hasIteratedDerivAt [CompleteSpace F] {f : 𝕜 → F} {x : 𝕜}
    (hf : AnalyticAt 𝕜 f x) (n : ℕ) : HasIteratedDerivAt n f (iteratedDeriv n f x) x := by
  induction n generalizing f with
  | zero => simp only [iteratedDeriv_zero, HasIteratedDerivAt.zero]
  | succ n ih =>
    rw [iteratedDeriv_succ']
    refine ⟨deriv f, hf.differentiableAt.hasDerivAt, Or.inr ?_, ih hf.deriv⟩
    exact hf.eventually_analyticAt.mono fun y hy ↦ hy.differentiableAt.hasDerivAt

lemma AnalyticAt.hasFPowerSeriesAt {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
    [CharZero 𝕜] {f : 𝕜 → 𝕜} {x : 𝕜} (h : AnalyticAt 𝕜 f x) :
    HasFPowerSeriesAt f
      (FormalMultilinearSeries.ofScalars 𝕜 (fun n ↦ iteratedDeriv n f x / n.factorial)) x := by
  obtain ⟨p, hp⟩ := h
  convert! hp
  obtain ⟨r, hpr⟩ := hp
  ext n
  have h_fact_smul := hpr.factorial_smul 1
  simp only [FormalMultilinearSeries.apply_eq_prod_smul_coeff, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, nsmul_eq_mul, one_pow, one_mul] at h_fact_smul
  simp only [FormalMultilinearSeries.apply_eq_prod_smul_coeff,
    FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, mul_eq_mul_left_iff]
  left
  rw [div_eq_iff, mul_comm, h_fact_smul, ← iteratedDeriv_eq_iteratedFDeriv]

theorem iteratedDeriv_const {n : ℕ} {c : F} {x : 𝕜} :
    iteratedDeriv n (fun _ ↦ c) x = if n = 0 then c else 0 := by
  induction n generalizing c with
  | zero => simp
  | succ n h => simp [iteratedDeriv_succ', h]

theorem iteratedDerivWithin_const {n : ℕ} {c : F} {s : Set 𝕜} {x : 𝕜} :
    iteratedDerivWithin n (fun _ ↦ c) s x = if n = 0 then c else 0 := by
  induction n generalizing c with
  | zero => simp
  | succ n h => simp [iteratedDerivWithin_succ', Pi.zero_def, h]

@[simp]
lemma iteratedDeriv_fun_const_zero : iteratedDeriv n (fun _ ↦ 0) x = (0 : F) := by
  simpa using @iteratedDeriv_const 𝕜 _ F _ _ n 0

@[simp]
lemma iteratedDeriv_const_zero : iteratedDeriv n (0 : 𝕜 → F) x = (0 : F) := by
  simp [Pi.zero_def]

@[simp]
lemma iteratedDerivWithin_fun_const_zero {s : Set 𝕜} :
    iteratedDerivWithin n (fun _ ↦ 0) s x = (0 : F) := by
  simpa using @iteratedDerivWithin_const 𝕜 _ F _ _ n 0

@[simp]
lemma iteratedDerivWithin_const_zero {s : Set 𝕜} :
    iteratedDerivWithin n (0 : 𝕜 → F) s x = (0 : F) := by
  simp [Pi.zero_def]

/-- `C^{n + 1}` is equivalent to `C^n` and the `n`-th derivative being `C^1`. -/
theorem contDiff_nat_succ_iff_contDiff_one_iteratedDeriv {n : ℕ} : ContDiff 𝕜 (n + 1 : ℕ) f ↔
    ContDiff 𝕜 n f ∧ ContDiff 𝕜 1 (iteratedDeriv n f) := by
  simp only [contDiff_nat_iff_iteratedDeriv, contDiff_one_iff_deriv, ← iteratedDeriv_succ]
  grind
