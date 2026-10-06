/-
Copyright (c) 2025 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Luigi Massacci
-/
module

public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.Topology.Algebra.Module.Spaces.CompactConvergenceCLM

/-!
# Distributions

Let `E` be a real **finite-dimensional normed space**, `Ω` an open subset of `E`,
and `F` a real **locally convex topological vector space**.

An **`F`-valued distribution on `Ω`** is a continuous `ℝ`-linear map `T : 𝓓(Ω, ℝ) →L[ℝ] F`,
defined on the space `𝓓(Ω, ℝ)` of real-valued test functions, and taking values in `F`.
In particular, if `𝕜` is an `RCLike` field, `𝓓'(Ω, 𝕜)` is the usual notion of real or complex
distribution on `Ω`.

We denote the space of `F`-valued distributions on `Ω` by `𝓓'(Ω, F)`. Topologically,
it is defined as `𝓓(Ω, ℝ) →L_c[ℝ] F`, meaning that we endow it with the topology of uniform
convergence on compact subsets of `𝓓(Ω, ℝ)`. In this particular case, this happens to coincide
with the topology of `𝓓(Ω, ℝ) →L[ℝ] F`, namely that of uniform convergence on bounded subsets.
See the implementation notes below for more details.

Right now, this file contains very few mathematical statements.
The theory will be expanded in future PRs.

## Main Declarations

* `𝓓'^{n}(Ω, F) = Distribution Ω F n` is the space of `F`-valued distributions on `Ω` with
  order at most `n`. See the implementation notes below for more information about the parameter
  `n : ℕ∞`; in most cases you want to use the space `𝓓'(Ω, F) = Distribution Ω F ⊤`.
* `Distribution.mapCLM`: any continuous linear map `A : F →L[ℝ] G` induces a continuous linear
  map `𝓓'(Ω, F) →L[ℝ] 𝓓'(Ω, G)`. On locally integrable functions, this corresponds to applying `A`
  pointwise.
* `Distribution.ofFun Ω f μ n hf`: the distribution induced by a function `f : E → F` that is
  locally integrable on `Ω`, sending a test function `φ` to `∫ x, φ x • f x ∂μ`.

## Notation

In the `Distributions` scope, we introduce the following notations:
* `𝓓'^{n}(Ω, F)`: the space of `F`-valued distributions on the open set `Ω` with order at most
  `n : ℕ∞`.
* `𝓓'(Ω, F)`: the space of `F`-valued distributions on the open set `Ω`, i.e `𝓓'^{⊤}(Ω, F)`.

Note that the parameter `n` here lives in `ℕ∞`, unlike the parameter for `ContDiff` which lives
in `WithTop ℕ∞` (to incorporate analytic functions). This means that we can't use the notation
`∞` introduced for `ContDiff` for our regularity, because it denotes an element of `WithTop ℕ∞`.
We could introduce another notation `∞` for `⊤ : ℕ∞`, but we believe it would be confusing.

## Implementation Notes

### `abbrev` or `def`

At this point in time, it is not clear whether we should enforce a separation between the API
for `𝓓'(Ω, F)` and the more generic API about `𝓓(Ω, ℝ) →L_c[ℝ] F`.
For now, we have made the "default" choice to implement `Distribution` as an `abbrev`, which means
that we get a lot of instances for free, but also that there is no such separation of APIs.

If this happens to be a bad decision, which will become clear while developing the theory,
do not hesitate to refactor to a `def` instead.

### Vector-valued distributions

The theory of vector-valued distributions is not as well-known as its scalar-valued analog. The
definition we choose is studied in
[L. Schwartz, *Théorie des distributions à valeurs vectorielles*][schwartz1957].

Let us give two examples of how we plan to use this level of generality:
* In the short term, this will allow us to define the *Fréchet derivative* of a distribution,
  as a continuous linear map `𝓓'(Ω, F) →L[ℝ] 𝓓'(Ω, E →L[ℝ] F)`. Note that, even if `F = ℝ`,
  the derivative is naturally vector-valued.
* On a longer timescale, we should aim to prove the
  [Schwartz Kernel Theorem](https://en.wikipedia.org/wiki/Schwartz_kernel_theorem), which is
  formulated nicely in terms of vector-valued distributions. Indeed, it says precisely that one
  can (algebraically, at least) identify the spaces `𝓓'(Ω₁ ×ˢ Ω₂, ℝ)` and `𝓓'(Ω₁, 𝓓'(Ω₂, ℝ))`.

### Choice of scalar field

In the literature, it is common to define complex-valued distributions as continuous `ℂ`-linear
forms `T : 𝓓(Ω, ℂ) →L[ℂ] ℂ`. We use `𝓓(Ω, ℝ) →L[ℝ] ℂ` instead, that is, we only ever test
against *real-valued* test functions.

This makes no difference mathematically, since `𝓓(Ω, ℂ)` is the complexification of `𝓓(Ω, ℝ)`,
hence there is a topological isomorphism between `𝓓(Ω, ℝ) →L[ℝ] F` and `𝓓(Ω, ℂ) →L[ℂ] F`
whenever `F` is a complex vector space.

We choose this definition because it avoids adding a base field as an extra parameter.
Instead, we use the generality of vector-valued distributions to our advantage: a complex-valued
distribution is nothing more than a distribution taking values in the real vector-space `ℂ`.

### Order of distributions

Based on established practice in the literature, a natural way to express the order of a
distribution would be to introduce a predicate `Distribution.HasOrderAtMost` on the space of all
distributions. Here though, we define a separate space `𝓓'^{n}(Ω, F)` whose elements are precisely
distributions of order at most `n`.

This is not incompatible with the predicate approach: in fact, we think that such a predicate
should eventually become the primary interface for the order of a distribution. However, we believe
that being able to talk about the space `𝓓'^{n}(Ω, F)` is also quite important, for the following
reasons:
* if `T : 𝓓'(Ω,F)` is a distribution whose order is at most `n`, it is natural to test it against
  a `C^n` test function (especially if `n = 0`). This means that we naturally want to consider its
  extension `T'` as an element of `𝓓'^{n}(Ω, F)`.
* it is often quite easy to keep track of the regularities while *defining* an operation on
  distributions (e. g. differentiation). On the other hand, once you have defined an operation on
  `𝓓'^(Ω, F)`, it can be quite painful to study its relation to order *a posteriori*.

Note that the topology on `𝓓'^{n}(Ω, F)` has no reason to be the subspace topology coming from
`𝓓'(Ω, F)`.

### Choice of topology

Our choice of the compact convergence topology on `𝓓'^{n}(Ω, F)` follows
[L. Schwartz, *Théorie des distributions à valeurs vectorielles*, §2, p. 49][schwartz1957].

Note that, since `𝓓(Ω, ℝ)` is a Montel space, the topology on `𝓓'(Ω, F)` is also that of
bounded convergence. Hence, our definition also agrees with
[L. Schwartz, *Théorie des distributions*, Chapitre III, §3][schwartz1950].

When `n` is finite, however, `𝓓^{n}(Ω, ℝ)` is no longer a Montel space
(see [L. Schwartz, *Théorie des distributions*, Chapitre III, §2, p. 71][schwartz1950]), hence
these two topologies have no reason to be the same. Schwartz uses compact convergence as a default
(see [L. Schwartz, *Théorie des distributions à valeurs vectorielles*, §2, p. 50][schwartz1957]),
which we follow here.

Finally, note that a **sequence** of distributions converges in `𝓓'(Ω, F)` if and only if it
converges pointwise
(see [L. Schwartz, *Théorie des distributions*, Chapitre III, §3, Théorème XIII][schwartz1950]).
Due to this fact, some texts endow `𝓓'(Ω, F)` with the pointwise convergence topology. While this
gives the same converging sequences as the topology of bounded/compact convergence, this is no
longer true for general filters.

## References

* [L. Schwartz, *Théorie des distributions*][schwartz1950]
* [L. Schwartz, *Théorie des distributions à valeurs vectorielles*][schwartz1957]
* [L. Hörmander, *The Analysis of Linear Partial Differential Operators I*][hormander2003]

-/

@[expose] public section

open Set TopologicalSpace
open scoped Distributions CompactConvergenceCLM

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Opens E}
  {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  {F' : Type*} [AddCommGroup F'] [Module ℝ F'] [TopologicalSpace F']
  {n k : ℕ∞}

-- TODO: def or abbrev?
variable (Ω F n) in
/-- `𝓓'^{n}(Ω, F) = Distribution Ω F n` is the space of `F`-valued distributions on `Ω` with
order at most `n`.

In most cases you want to use the space `𝓓'(Ω, F) = Distribution Ω F ⊤`. -/
abbrev Distribution := 𝓓^{n}(Ω, ℝ) →L_c[ℝ] F

/-- We denote `𝓓'^{n}(Ω, F)` the space of `F`-valued distributions on `Ω` with order at most
`n : ℕ∞`. Note that using `𝓓'` is a bit abusive since this is no longer a dual space unless
`F = 𝕜`. -/
scoped[Distributions] notation "𝓓'^{" n "}(" Ω ", " F ")" => Distribution Ω F n

/-- We denote `𝓓'(Ω, F)` the space of `F`-valued distributions on `Ω`. Note that using `𝓓'`
is a bit abusive since this is no longer a dual space unless `F = 𝕜`. -/
scoped[Distributions] notation "𝓓'(" Ω ", " F ")" => Distribution Ω F ⊤

variable [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
variable [IsTopologicalAddGroup F'] [ContinuousSMul ℝ F']

namespace Distribution

section mapCLM
-- TODO: generalize this section to `𝕜` linear maps (or even semilinear maps)
-- by generalizing `ContinuousLinearMap.postcompCompactConvergenceCLM`

/-- Any continuous linear map `A : F →L[ℝ] G` induces a continuous linear map
`𝓓'(Ω, F) →L[ℝ] 𝓓'(Ω, G)`. On locally integrable functions, this corresponds to applying `A`
pointwise. -/
noncomputable def mapCLM (A : F →L[ℝ] F') : 𝓓'^{n}(Ω, F) →L[ℝ] 𝓓'^{n}(Ω, F') :=
  A.postcompCompactConvergenceCLM _

@[simp]
lemma mapCLM_apply {A : F →L[ℝ] F'} {T : 𝓓'^{n}(Ω, F)} {f : 𝓓^{n}(Ω, ℝ)} :
    mapCLM A T f = A (T f) := rfl

end mapCLM

section DiracDelta

/-- The Dirac delta distribution. This is zero if `x` does not belong to `Ω`. -/
@[wikidata Q209675]
noncomputable def delta (x : E) : 𝓓'^{n}(Ω, ℝ) where
  toFun f := f x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_eval_const _

@[simp]
theorem delta_apply (x : E) (f : 𝓓^{n}(Ω, ℝ)) : delta x f = f x := by
  rfl

@[simp]
theorem delta_eq_zero_of_notMem (x : E) (hx : x ∉ Ω) : (delta x : 𝓓'^{n}(Ω, ℝ)) = 0 := by
  ext f
  change f x = 0
  have hx_support : x ∉ tsupport f := by
    intro hx_mem
    exact hx (f.tsupport_subset hx_mem)
  exact image_eq_zero_of_notMem_tsupport hx_support

end DiracDelta

section LineDerivCLM
-- TODO: generalize this section to `𝕜` linearity
-- by generalizing `ContinuousLinearMap.precompCompactConvergenceCLM`

/-- `lineDerivCLM 𝕜 v` is the continuous `𝕜`-linear-map sending a distribution
`T : 𝓓'^{k}_{K}(E, F)` to its derivative along the vector `v`, which is a
distribution in `𝓓^{n}_{K}(E, F)`. Because differentiating increases the order, it is defined when
`k + 1 ≤ n`; the proof `hk` can usually be omitted, see `regularity_le`.

The parameters `n` and `k` are implicit as they can often be inferred from context, or
specified by a type ascription. For `n = k = ⊤`, we also provide instances of the `LineDeriv`
notation typeclass. -/
noncomputable def lineDerivCLM (v : E) (hk : k + 1 ≤ n := by regularity_le) :
    𝓓'^{k}(Ω, F) →L[ℝ] 𝓓'^{n}(Ω, F) :=
  - (TestFunction.lineDerivCLM ℝ v hk).precompCompactConvergenceCLM _

lemma lineDerivCLM_apply {v : E} (hk : k + 1 ≤ n) {T : 𝓓'^{k}(Ω, F)} {f : 𝓓^{n}(Ω, ℝ)} :
    lineDerivCLM v hk T f = - T (TestFunction.lineDerivCLM ℝ v hk f) :=
  rfl

lemma lineDerivCLM_add {v₁ v₂ : E} (hk : k + 1 ≤ n) :
    (lineDerivCLM (v₁ + v₂) hk : 𝓓'^{k}(Ω, F) →L[ℝ] 𝓓'^{n}(Ω, F)) =
      lineDerivCLM v₁ hk + lineDerivCLM v₂ hk := by
  ext T f
  simp [lineDerivCLM_apply, TestFunction.lineDerivCLM_add, neg_add, -neg_add_rev]

lemma lineDerivCLM_smul {c : ℝ} {v : E} (hk : k + 1 ≤ n) :
    (lineDerivCLM (c • v) hk : 𝓓'^{k}(Ω, F) →L[ℝ] 𝓓'^{n}(Ω, F)) =
      c • lineDerivCLM v hk := by
  ext T f
  simp [lineDerivCLM_apply, TestFunction.lineDerivCLM_smul]

open LineDeriv

/-- Note: we cannot express the full generality of `lineDerivCLM` purely in terms of this typeclass,
because (by design) the target type `𝓓^{k}_{K}(E, F)` is not determined by the input type
`𝓓^{n}_{K}(E, F)`. -/
noncomputable instance : LineDeriv E 𝓓'(Ω, F) 𝓓'(Ω, F) where
  lineDerivOp v := lineDerivCLM v le_top

variable (𝕜) in
lemma lineDerivOp_eq_lineDerivCLM {v : E} {T : 𝓓'(Ω, F)} :
    ∂_{v} T = lineDerivCLM v le_top T :=
  rfl

@[simp]
theorem lineDerivOp_apply_apply (f : 𝓓'(Ω, F)) (g : 𝓓(Ω, ℝ)) (m : E) :
    ∂_{m} f g = f (- ∂_{m} g) := by
  rw [map_neg]; rfl

noncomputable instance : LineDerivAdd E 𝓓'(Ω, F) 𝓓'(Ω, F) where
  lineDerivOp_add v := map_add (lineDerivCLM v le_top)
  lineDerivOp_left_add _ _ T := congr($(lineDerivCLM_add le_top) T)

noncomputable instance : LineDerivSMul ℝ E 𝓓'(Ω, F) 𝓓'(Ω, F) where
  lineDerivOp_smul v := map_smul (lineDerivCLM v le_top)

noncomputable instance : LineDerivLeftSMul ℝ E 𝓓'(Ω, F) 𝓓'(Ω, F) where
  lineDerivOp_left_smul _ _ T := congr($(lineDerivCLM_smul le_top) T)

noncomputable instance : ContinuousLineDeriv E 𝓓'(Ω, F) 𝓓'(Ω, F) where
  continuous_lineDerivOp v := (lineDerivCLM v le_top).continuous

lemma lineDerivOpCLM_eq_lineDerivCLM {v : E} :
    lineDerivOpCLM ℝ 𝓓'(Ω, F) v = lineDerivCLM v le_top :=
  rfl

end LineDerivCLM

section ofFun

open MeasureTheory

variable [SigmaAlgebra E] [OpensSigmaAlgebra E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

variable (Ω) in
/-- The distribution induced by a function `f : E → F` that is locally integrable on `Ω` with
respect to a measure `μ`, sending a test function `φ` to `∫ x, φ x • f x ∂μ`. -/
noncomputable def ofFun (f : E → F) (μ : Measure E := by volume_tac) (n : ℕ∞)
    (hf : LocallyIntegrableOn f Ω μ) : 𝓓'^{n}(Ω, F) :=
  TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.lsmul ℝ ℝ) μ f hf

@[grind =]
theorem ofFun_apply {f : E → F} {μ : Measure E} {hf : LocallyIntegrableOn f Ω μ}
    {φ : 𝓓^{n}(Ω, ℝ)} :
    ofFun Ω f μ n hf φ = ∫ x, φ x • f x ∂μ :=
  rfl

@[simp, grind =]
theorem ofFun_zero {μ : Measure E} {h0 : LocallyIntegrableOn (0 : E → F) Ω μ} :
    ofFun Ω (0 : E → F) μ n h0 = 0 := by
  ext; simp [ofFun_apply]

theorem ofFun_congr_ae {f f' : E → F} {μ : Measure E} {hf : LocallyIntegrableOn f Ω μ}
    (h : f =ᵐ[μ.restrict Ω] f') :
    ofFun Ω f μ n hf = ofFun Ω f' μ n (hf.congr h) := by
  ext φ
  rw [ofFun_apply, ofFun_apply]
  have h' : ∀ x ∉ Ω, φ x • f x = 0 ∧ φ x • f' x = 0 := fun x hx ↦ by simp [φ.zero_on_compl hx]
  obtain ⟨h₁, h₂⟩ := forall₂_and.mp h'
  rw [← setIntegral_eq_integral_of_ae_compl_eq_zero (.of_forall h₁),
    ← setIntegral_eq_integral_of_ae_compl_eq_zero (.of_forall h₂)]
  exact integral_congr_ae <| ae_eq_rfl.smul h

@[simp]
theorem ofFun_add {f g : E → F} {μ : Measure E} {hfg : LocallyIntegrableOn (f + g) Ω μ}
    (hf : LocallyIntegrableOn f Ω μ) (hg : LocallyIntegrableOn g Ω μ) :
    ofFun Ω (f + g) μ n hfg = ofFun Ω f μ n hf + ofFun Ω g μ n hg := by
  ext φ
  rw [add_apply, ofFun_apply, ofFun_apply, ofFun_apply,
    ← integral_add (φ.integrable_smul hf) (φ.integrable_smul hg)]
  simp

@[simp]
theorem ofFun_neg {f : E → F} {μ : Measure E} {hf' : LocallyIntegrableOn (-f) Ω μ}
    (hf : LocallyIntegrableOn f Ω μ) :
    ofFun Ω (-f) μ n hf' = -ofFun Ω f μ n hf := by
  ext; simp [ofFun_apply, integral_neg]

@[simp]
theorem ofFun_smul {f : E → F} {μ : Measure E} (c : ℝ) {hcf : LocallyIntegrableOn (c • f) Ω μ}
    (hf : LocallyIntegrableOn f Ω μ) :
    ofFun Ω (c • f) μ n hcf = c • ofFun Ω f μ n hf := by
  ext φ
  rw [ofFun_apply, smul_apply, ofFun_apply, ← integral_smul]
  refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  simp [smul_comm c]

variable [BorelSpace E] [FiniteDimensional ℝ E] [CompleteSpace F]

theorem ofFun_injective {f f' : E → F} {μ : Measure E}
    (hf : LocallyIntegrableOn f Ω μ) (hf' : LocallyIntegrableOn f' Ω μ)
    (h : ofFun Ω f μ n hf = ofFun Ω f' μ n hf') :
    f =ᵐ[μ.restrict Ω] f' := by
  suffices h' : ∀ᵐ x ∂μ, x ∈ Ω → (f - f') x = 0 by
    rw [← sub_ae_eq_zero]
    exact (ae_restrict_iff' Ω.isOpen.measurableSet).mpr h'
  refine Ω.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hf.sub hf')
    fun g g_diff g_compact g_tsupp ↦ ?_
  let φ : 𝓓^{n}(Ω, ℝ) := ⟨g, g_diff.of_le (mod_cast le_top), g_compact, g_tsupp⟩
  have : ∫ x, φ x • (f - f') x ∂μ = 0:= by
    simp_rw [Pi.sub_apply, smul_sub]
    rw [integral_sub (φ.integrable_smul hf) (φ.integrable_smul hf'), sub_eq_zero]
    rw [← ofFun_apply (hf := hf), ← ofFun_apply (hf := hf'), h]
  congr

end ofFun

end Distribution
