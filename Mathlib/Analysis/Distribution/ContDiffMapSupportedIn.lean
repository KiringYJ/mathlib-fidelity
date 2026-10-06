/-
Copyright (c) 2023 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Luigi Massacci
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Continuously differentiable functions supported in a given compact set

This file develops the basic theory of bundled `n`-times continuously differentiable functions
with support contained in a given compact set.

Given `n : ℕ∞` and a compact subset `K` of a normed space `E`, we consider the type of bundled
functions `f : E → F` (where `F` is a normed vector space) such that:

- `f` is `n`-times continuously differentiable: `ContDiff ℝ n f`.
- `f` vanishes outside of a compact set: `EqOn f 0 Kᶜ`.

The main reason this exists as a bundled type is to be endowed with its natural locally convex
topology (namely, uniform convergence of `f` and its derivatives up to order `n`).
Taking the locally convex inductive limit of these as `K` varies yields the natural topology on test
functions, used to define distributions. While most of distribution theory cares only about `C^∞`
functions, we also want to endow the space of `C^n` test functions with its natural topology.
Indeed, distributions of order less than `n` are precisely those which extend continuously to this
larger space of test functions.

## Main definitions

- `ContDiffMapSupportedIn E F n K`: the type of bundled `n`-times continuously differentiable
  functions `E → F` which vanish outside of `K`.
- `ContDiffMapSupportedIn.iteratedFDerivLM`: wrapper, as a `𝕜`-linear map, for
  `iteratedFDeriv` from `ContDiffMapSupportedIn E F n K` to
  `ContDiffMapSupportedIn E (E [×i]→L[ℝ] F) k K`.
- `ContDiffMapSupportedIn.topologicalSpace`, `ContDiffMapSupportedIn.uniformSpace`: the topology
  and uniform structures on `𝓓^{n}_{K}(E, F)`, given by uniform convergence of the functions and
  all their derivatives up to order `n`.

## Main statements

- `ContDiffMapSupportedIn.isTopologicalAddGroup`, `ContDiffMapSupportedIn.continuousSMul` and
  `ContDiffMapSupportedIn.instLocallyConvexSpace`: `𝓓^{n}_{K}(E, F)` is a locally convex
  topological vector space.

## Notation

In the `Distributions` scope, we introduce the following notations:
- `𝓓^{n}_{K}(E, F)`: the space of `n`-times continuously differentiable functions `E → F`
  which vanish outside of `K`.
- `𝓓_{K}(E, F)`: the space of smooth (infinitely differentiable) functions `E → F`
  which vanish outside of `K`, i.e. `𝓓^{⊤}_{K}(E, F)`.
- `N[𝕜; F]_{K, n, i}` (or simply `N[𝕜]_{K, n, i}`): the `𝕜`-seminorm on `𝓓^{n}_{K}(E, F)`
  given by the sup-norm of the `i`-th derivative.
- `N[𝕜; F]_{K, i}` (or simply `N[𝕜]_{K, i}`): the `𝕜`-seminorm on `𝓓_{K}(E, F)`
  given by the sup-norm of the `i`-th derivative.

## Implementation details

* The technical choice of spelling `EqOn f 0 Kᶜ` in the definition, as opposed to `tsupport f ⊆ K`
  is to make rewriting `f x` to `0` easier when `x ∉ K`.
* Having the parameter `n` (instead of just using smooth functions) is useful because
  it allows us to track the regularity of our operations, which will tell us how the order
  of a distribution behaves under the transpose of said operation. For example, the fact
  that differentiation of test functions *decreases* regularity by (at most) one will imply that
  differentiation of distributions *increases* their order by (at most) one. This comes
  with the downside of many regularity parameters; we considered specializing all the
  definitions to the (most common) smooth case, but we believe it is better to wait and see
  what is more practical to use later on.
* In `iteratedFDerivLM`, we define the `i`-th iterated differentiation operator as
  a map from `𝓓^{n}_{K}` to `𝓓^{k}_{K}` for `k + i ≤ n`, which it takes as an argument. The
  regularity inequalities of these operators, of the structure maps, the seminorms, and the
  inclusions, are found by the tactic `regularity_le` in routine cases. Since the inequality is
  an explicit argument, an operator applied to a function takes it explicitly, as in
  `fderivLM 𝕜 n k hk f`, or is parenthesized, as in `(fderivLM 𝕜 ⊤ ⊤) f`.

## Tags

distributions
-/

@[expose] public section

open TopologicalSpace Set Function UniformSpace WithSeminorms
open scoped BoundedContinuousFunction Topology NNReal ContDiff

variable (𝕜 E F F' : Type*) [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]
  [NormedAddCommGroup F'] [NormedSpace ℝ F'] [NormedSpace 𝕜 F'] [SMulCommClass ℝ 𝕜 F']
  {n n₁ n₂ k : ℕ∞} {K K₁ K₂ : Compacts E}

/-- The type of bundled `n`-times continuously differentiable maps which vanish outside of a fixed
compact set `K`. -/
structure ContDiffMapSupportedIn (n : ℕ∞) (K : Compacts E) : Type _ where
  /-- The underlying function. Use coercion instead. -/
  protected toFun : E → F
  protected contDiff' : ContDiff ℝ n toFun
  protected zero_on_compl' : EqOn toFun 0 Kᶜ

/-- Notation for the space of bundled `n`-times continuously differentiable
functions with support in a compact set `K`. -/
scoped[Distributions] notation "𝓓^{" n "}_{" K "}(" E ", " F ")" =>
  ContDiffMapSupportedIn E F n K

/-- Notation for the space of bundled smooth (infinitely differentiable)
functions with support in a compact set `K`. -/
scoped[Distributions] notation "𝓓_{" K "}(" E ", " F ")" =>
  ContDiffMapSupportedIn E F ⊤ K

open scoped Distributions

/-- `ContDiffMapSupportedInClass B E F n K` states that `B` is a type of bundled `n`-times
continuously differentiable functions with support in the compact set `K`. -/
class ContDiffMapSupportedInClass (B : Type*) (E F : outParam <| Type*)
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℝ F]
    (n : outParam ℕ∞) (K : outParam <| Compacts E)
    extends FunLike B E F where
  map_contDiff (f : B) : ContDiff ℝ n f
  map_zero_on_compl (f : B) : EqOn f 0 Kᶜ

open ContDiffMapSupportedInClass

namespace ContDiffMapSupportedInClass

instance (B : Type*) (E F : outParam <| Type*)
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℝ F]
    (n : outParam ℕ∞) (K : outParam <| Compacts E)
    [ContDiffMapSupportedInClass B E F n K] :
    ContinuousMapClass B E F where
  map_continuous f := (map_contDiff f).continuous

instance (B : Type*) (E F : outParam <| Type*)
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℝ F]
    (n : outParam ℕ∞) (K : outParam <| Compacts E)
    [ContDiffMapSupportedInClass B E F n K] :
    BoundedContinuousMapClass B E F where
  map_bounded f := by
    have := HasCompactSupport.intro K.isCompact (map_zero_on_compl f)
    rcases (map_continuous f).bounded_above_of_compact_support this with ⟨C, hC⟩
    exact map_bounded (BoundedContinuousFunction.ofNormedAddCommGroup f (map_continuous f) C hC)

end ContDiffMapSupportedInClass

namespace ContDiffMapSupportedIn

instance toContDiffMapSupportedInClass :
    ContDiffMapSupportedInClass 𝓓^{n}_{K}(E, F) E F n K where
  coe f := f.toFun
  coe_injective f g h := by cases f; cases g; congr
  map_contDiff f := f.contDiff'
  map_zero_on_compl f := f.zero_on_compl'

variable {E F F'}

protected theorem contDiff (f : 𝓓^{n}_{K}(E, F)) : ContDiff ℝ n f := map_contDiff f
protected theorem zero_on_compl (f : 𝓓^{n}_{K}(E, F)) : EqOn f 0 Kᶜ := map_zero_on_compl f
protected theorem compact_supp (f : 𝓓^{n}_{K}(E, F)) : HasCompactSupport f :=
  .intro K.isCompact (map_zero_on_compl f)

@[simp]
theorem toFun_eq_coe {f : 𝓓^{n}_{K}(E, F)} : f.toFun = (f : E → F) :=
  rfl

/-- See note [custom simps projection]. -/
def Simps.coe (f : 𝓓^{n}_{K}(E, F)) : E → F := f

initialize_simps_projections ContDiffMapSupportedIn (toFun → coe, as_prefix coe)

@[ext]
theorem ext {f g : 𝓓^{n}_{K}(E, F)} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext _ _ h

/-- Copy of a `ContDiffMapSupportedIn` with a new `toFun` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : 𝓓^{n}_{K}(E, F)) (f' : E → F) (h : f' = f) : 𝓓^{n}_{K}(E, F) where
  toFun := f'
  contDiff' := h.symm ▸ f.contDiff
  zero_on_compl' := h.symm ▸ f.zero_on_compl

@[simp]
theorem coe_copy (f : 𝓓^{n}_{K}(E, F)) (f' : E → F) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

theorem copy_eq (f : 𝓓^{n}_{K}(E, F)) (f' : E → F) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

@[simp]
theorem coe_toBoundedContinuousFunction (f : 𝓓^{n}_{K}(E, F)) :
    (f : BoundedContinuousFunction E F) = (f : E → F) := rfl

section AddCommGroup

instance : Zero 𝓓^{n}_{K}(E, F) where
  zero := .mk 0 contDiff_zero_fun fun _ _ ↦ rfl

instance : IsZeroApply 𝓓^{n}_{K}(E, F) E F where
  zero_apply _ := rfl

@[deprecated (since := "2026-06-15")] alias coe_zero := FunLike.coe_zero

instance : Add 𝓓^{n}_{K}(E, F) where
  add f g := .mk (f + g) (f.contDiff.add g.contDiff) <| by
    rw [← add_zero 0]
    exact f.zero_on_compl.comp_left₂ g.zero_on_compl

instance : IsAddApply 𝓓^{n}_{K}(E, F) E F where
  add_apply _ _ _ := rfl

@[deprecated (since := "2026-06-15")] alias coe_add := FunLike.coe_add

instance : Neg 𝓓^{n}_{K}(E, F) where
  neg f := .mk (-f) (f.contDiff.neg) <| by
    rw [← neg_zero]
    exact f.zero_on_compl.comp_left

instance : IsNegApply 𝓓^{n}_{K}(E, F) E F where
  neg_apply _ _ := rfl

@[deprecated (since := "2026-06-15")] alias coe_neg := FunLike.coe_neg

instance instSub : Sub 𝓓^{n}_{K}(E, F) where
  sub f g := .mk (f - g) (f.contDiff.sub g.contDiff) <| by
    rw [← sub_zero 0]
    exact f.zero_on_compl.comp_left₂ g.zero_on_compl

instance : IsSubApply 𝓓^{n}_{K}(E, F) E F where
  sub_apply _ _ _ := rfl

@[deprecated (since := "2026-06-15")] alias coe_sub := FunLike.coe_sub

instance instSMul {R} [Semiring R] [Module R F] [SMulCommClass ℝ R F] [ContinuousConstSMul R F] :
    SMul R 𝓓^{n}_{K}(E, F) where
  smul c f := .mk (c • (f : E → F)) (f.contDiff.const_smul c) <| by
    rw [← smul_zero c]
    exact f.zero_on_compl.comp_left

instance {R} [Semiring R] [Module R F] [SMulCommClass ℝ R F] [ContinuousConstSMul R F] :
    IsSMulApply R 𝓓^{n}_{K}(E, F) E F where
  smul_apply _ _ _ := rfl

@[deprecated (since := "2026-06-15")] alias coe_smul := FunLike.coe_smul

instance : AddCommGroup 𝓓^{n}_{K}(E, F) := fast_instance% FunLike.addCommGroup

@[deprecated (since := "2026-06-15")] alias coeHom := FunLike.coeAddMonoidHom

@[deprecated (since := "2026-06-15")] alias coe_coeHom := FunLike.coe_coeAddMonoidHom

@[deprecated (since := "2026-06-15")] alias coeHom_injective := FunLike.coeAddMonoidHom_injective

end AddCommGroup

section Module

instance {R} [Semiring R] [Module R F] [SMulCommClass ℝ R F] [ContinuousConstSMul R F] :
    Module R 𝓓^{n}_{K}(E, F) := fast_instance% FunLike.module

end Module

protected theorem support_subset (f : 𝓓^{n}_{K}(E, F)) : support f ⊆ K :=
  support_subset_iff'.mpr f.zero_on_compl

protected theorem tsupport_subset (f : 𝓓^{n}_{K}(E, F)) : tsupport f ⊆ K :=
  closure_minimal f.support_subset K.isCompact.isClosed

protected theorem hasCompactSupport (f : 𝓓^{n}_{K}(E, F)) : HasCompactSupport f :=
  HasCompactSupport.intro K.isCompact f.zero_on_compl

@[fun_prop]
protected theorem continuous (f : 𝓓^{n}_{K}(E, F)) : Continuous f :=
  f.contDiff.continuous

/-- Inclusion of unbundled `n`-times continuously differentiable function with support included
in a compact `K` into the space `𝓓^{n}_{K}`. -/
@[simps]
protected def of_support_subset {f : E → F} (hf : ContDiff ℝ n f) (hsupp : support f ⊆ K) :
    𝓓^{n}_{K}(E, F) where
  toFun := f
  contDiff' := hf
  zero_on_compl' := support_subset_iff'.mp hsupp

protected theorem bounded_iteratedFDeriv (f : 𝓓^{n}_{K}(E, F)) {i : ℕ} (hi : i ≤ n) :
    ∃ C, ∀ x, ‖iteratedFDeriv ℝ i f x‖ ≤ C :=
  Continuous.bounded_above_of_compact_support
    (f.contDiff.continuous_iteratedFDeriv <| (WithTop.le_coe rfl).mpr hi)
    (f.hasCompactSupport.iteratedFDeriv i)

protected theorem iteratedFDeriv_zero_on_compl (f : 𝓓^{n}_{K}(E, F)) {i : ℕ} :
    EqOn (iteratedFDeriv ℝ i f) 0 Kᶜ := by
  intro x (hx : x ∉ K)
  contrapose! hx
  exact f.tsupport_subset (support_iteratedFDeriv_subset i hx)

/-- Inclusion of `𝓓^{n}_{K}(E, F)` into the space `E →ᵇ F` of bounded continuous maps
as a `𝕜`-linear map.

This is subsumed by `toBoundedContinuousFunctionCLM`, which also bundles the continuity. -/
noncomputable def toBoundedContinuousFunctionLM : 𝓓^{n}_{K}(E, F) →ₗ[𝕜] E →ᵇ F where
  toFun f := f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
lemma toBoundedContinuousFunctionLM_apply (f : 𝓓^{n}_{K}(E, F)) :
    toBoundedContinuousFunctionLM 𝕜 f = f :=
  rfl

lemma toBoundedContinuousFunctionLM_eq_of_scalars (𝕜' : Type*) [NontriviallyNormedField 𝕜']
    [NormedSpace 𝕜' F] [SMulCommClass ℝ 𝕜' F] :
    (toBoundedContinuousFunctionLM 𝕜 : 𝓓^{n}_{K}(E, F) → _) = toBoundedContinuousFunctionLM 𝕜' :=
  rfl

variable {𝕜} in
-- Note: generalizing this to a semilinear setting would require a semilinear version of
-- `CompatibleSMul`.
/-- Given `T : F →L[𝕜] F'`, `postcompLM T` is the `𝕜`-linear-map sending `f : 𝓓^{n}_{K}(E, F)`
to `T ∘ f` as an element of `𝓓^{n}_{K}(E, F')`.

This is subsumed by `postcompCLM T`, which also bundles the continuity. -/
noncomputable def postcompLM [LinearMap.CompatibleSMul F F' ℝ 𝕜] (T : F →L[𝕜] F') :
    𝓓^{n}_{K}(E, F) →ₗ[𝕜] 𝓓^{n}_{K}(E, F') where
  toFun f := ⟨T ∘ f, T.restrictScalars ℝ |>.contDiff.comp f.contDiff,
    fun x hx ↦ by simp [f.zero_on_compl hx]⟩
  map_add' f g := by ext x; exact map_add T (f x) (g x)
  map_smul' c f := by ext x; exact map_smul T c (f x)

@[simp]
lemma postcompLM_apply [LinearMap.CompatibleSMul F F' ℝ 𝕜] (T : F →L[𝕜] F')
    (f : 𝓓^{n}_{K}(E, F)) :
    postcompLM T f = T ∘ f :=
  rfl

open Lean Elab Tactic in
/-- The default discharger for the regularity inequalities in `ℕ∞` of the operators on
`ContDiffMapSupportedIn` and on test functions, such as `k + 1 ≤ n` for `fderivLM 𝕜 n k`.

It closes the goal with a local hypothesis, with `le_top` for smooth functions, with `le_rfl`, with
`zero_le`, or by `norm_num` for numerals. Other inequalities are passed explicitly. It never
chooses the regularities: if they are not determined when the tactic runs, it fails instead. -/
elab (name := regularityLe) "regularity_le" : tactic => do
  if (← instantiateMVars (← getMainTarget)).hasExprMVar then
    throwError "the regularities are not determined; pass the regularity inequality explicitly"
  evalTactic (← `(tactic|
    first
      | assumption
      | exact le_top
      | exact le_rfl
      | exact zero_le _
      | (norm_num; done)
      | fail "this operator needs a proof of its regularity inequality"))

/-- If `n₁ ≥ n₂` and `K₁ ⊆ K₂`, `monoLM 𝕜 hK hn` is the `𝕜`-linear inclusion of
`𝓓^{n₁}_{K₁}(E, F)` inside `𝓓^{n₂}_{K₂}(E, F)`. The proof `hn` of `n₂ ≤ n₁` can usually be
omitted, see `regularity_le`.

This is in fact continuous (see `monoCLM`). Furthermore:
* it is a topological embedding when `n₁ = n₂` and `K₁ ⊆ K₂` (not in Mathlib as of March 2026).
* it maps bounded sets to compact sets when `n₁ ≥ n₂ + 1` and `K₁ ⊆ K₂` (not in Mathlib as of
March 2026).

The parameters `n₁, n₂, K₁, K₂` are implicit as they can often be inferred from context, or
specified by a type ascription.
-/
noncomputable def monoLM (hK : K₁ ≤ K₂) (hn : n₂ ≤ n₁ := by regularity_le) :
    𝓓^{n₁}_{K₁}(E, F) →ₗ[𝕜] 𝓓^{n₂}_{K₂}(E, F) where
  toFun f := .of_support_subset (f.contDiff.of_le (mod_cast hn)) (f.support_subset.trans hK)
  map_add' f g := by ext; simp
  map_smul' c f := by ext; simp

@[simp]
lemma monoLM_apply (hK : K₁ ≤ K₂) (hn : n₂ ≤ n₁) (f : 𝓓^{n₁}_{K₁}(E, F)) :
    ((monoLM 𝕜 hK hn f : 𝓓^{n₂}_{K₂}(E, F)) : E → F) = f :=
  rfl

lemma monoLM_eq_of_scalars (𝕜' : Type*)
    [NontriviallyNormedField 𝕜'] [NormedSpace 𝕜' F] [SMulCommClass ℝ 𝕜' F] (hK : K₁ ≤ K₂)
    (hn : n₂ ≤ n₁) :
    (monoLM 𝕜 hK hn : 𝓓^{n₁}_{K₁}(E, F) → 𝓓^{n₂}_{K₂}(E, F)) = monoLM 𝕜' hK hn :=
  rfl

variable (n k) in
/-- `fderivLM 𝕜 n k` is the `𝕜`-linear-map sending `f : 𝓓^{n}_{K}(E, F)` to
its derivative as an element of `𝓓^{k}_{K}(E, E →L[ℝ] F)`. It is defined when `k + 1 ≤ n`; the
proof `hk` can usually be omitted, see `regularity_le`.

This is subsumed by `fderivCLM`, which also bundles the continuity. -/
noncomputable def fderivLM (hk : k + 1 ≤ n := by regularity_le) :
    𝓓^{n}_{K}(E, F) →ₗ[𝕜] 𝓓^{k}_{K}(E, E →L[ℝ] F) where
  toFun f :=
    .of_support_subset
      (f.contDiff.fderiv_right <| mod_cast hk)
      ((support_fderiv_subset ℝ).trans f.tsupport_subset)
  map_add' f g := by
    have hk' : 0 < (n : ℕ∞ω) := mod_cast (add_pos_of_right zero_lt_one k).trans_le hk
    ext
    simp [fderiv_add (f.contDiff.differentiable hk'.ne').differentiableAt
                     (g.contDiff.differentiable hk'.ne').differentiableAt, FunLike.coe_add]
  map_smul' c f := by
    have hk' : 0 < (n : ℕ∞ω) := mod_cast (add_pos_of_right zero_lt_one k).trans_le hk
    ext
    simp [fderiv_const_smul (f.contDiff.differentiable hk'.ne').differentiableAt,
      FunLike.coe_smul]

@[simp]
lemma fderivLM_apply (hk : k + 1 ≤ n) (f : 𝓓^{n}_{K}(E, F)) :
    fderivLM 𝕜 n k hk f = fderiv ℝ f :=
  rfl

lemma fderivLM_eq_of_scalars (𝕜' : Type*) [NontriviallyNormedField 𝕜']
    [NormedSpace 𝕜' F] [SMulCommClass ℝ 𝕜' F] (hk : k + 1 ≤ n) :
    (fderivLM 𝕜 n k hk : 𝓓^{n}_{K}(E, F) → _) = fderivLM 𝕜' n k hk :=
  rfl

variable (n k) in
/-- `iteratedFDerivLM 𝕜 n k i` is the `𝕜`-linear-map sending `f : 𝓓^{n}_{K}(E, F)` to
its `i`-th iterated derivative as an element of `𝓓^{k}_{K}(E, E [×i]→L[ℝ] F)`. It is defined when
`k + i ≤ n`; the proof `hi` can usually be omitted, see `regularity_le`.

This is subsumed by `iteratedFDerivCLM` (not yet in Mathlib), which also bundles the
continuity. -/
noncomputable def iteratedFDerivLM (i : ℕ) (hi : k + i ≤ n := by regularity_le) :
    𝓓^{n}_{K}(E, F) →ₗ[𝕜] 𝓓^{k}_{K}(E, E [×i]→L[ℝ] F) where
  toFun f :=
    .of_support_subset
      (f.contDiff.iteratedFDeriv_right <| mod_cast hi)
      ((support_iteratedFDeriv_subset i).trans f.tsupport_subset)
  map_add' f g := by
    have hi' : (i : ℕ∞ω) ≤ n := mod_cast (le_of_add_le_right hi)
    ext
    simp [iteratedFDeriv_add (f.contDiff.of_le hi') (g.contDiff.of_le hi'), FunLike.coe_add]
  map_smul' c f := by
    have hi' : (i : ℕ∞ω) ≤ n := mod_cast (le_of_add_le_right hi)
    ext
    simp [iteratedFDeriv_const_smul_apply (f.contDiff.of_le hi').contDiffAt, FunLike.coe_smul]

@[simp]
lemma iteratedFDerivLM_apply {i : ℕ} (hi : k + i ≤ n) (f : 𝓓^{n}_{K}(E, F)) :
    iteratedFDerivLM 𝕜 n k i hi f = iteratedFDeriv ℝ i f :=
  rfl

lemma iteratedFDerivLM_eq_of_scalars {i : ℕ} (𝕜' : Type*) [NontriviallyNormedField 𝕜']
    [NormedSpace 𝕜' F] [SMulCommClass ℝ 𝕜' F] (hi : k + i ≤ n) :
    (iteratedFDerivLM 𝕜 n k i hi : 𝓓^{n}_{K}(E, F) → _)
      = iteratedFDerivLM 𝕜' n k i hi :=
  rfl

variable (n) in
/-- `structureMapLM 𝕜 n i` is the `𝕜`-linear-map sending `f : 𝓓^{n}_{K}(E, F)` to its
`i`-th iterated derivative as an element of `E →ᵇ (E [×i]→L[ℝ] F)`. In other words, it
is the composition of `toBoundedContinuousFunctionLM 𝕜` and `iteratedFDerivLM 𝕜 n 0 i`. It is
defined when `i ≤ n`; the proof `hi` can usually be omitted, see `regularity_le`.

We call these "structure maps" because they define the topology on `𝓓^{n}_{K}(E, F)`.

This is subsumed by `structureMapCLM`, which also bundles the
continuity. -/
noncomputable def structureMapLM (i : ℕ) (hi : (i : ℕ∞) ≤ n := by regularity_le) :
    𝓓^{n}_{K}(E, F) →ₗ[𝕜] E →ᵇ (E [×i]→L[ℝ] F) :=
  toBoundedContinuousFunctionLM 𝕜 ∘ₗ iteratedFDerivLM 𝕜 n 0 i (by rwa [zero_add])

lemma structureMapLM_eq {i : ℕ} (hi : (i : ℕ∞) ≤ n) :
    (structureMapLM 𝕜 n i hi : 𝓓^{n}_{K}(E, F) →ₗ[𝕜] E →ᵇ (E [×i]→L[ℝ] F)) =
      (toBoundedContinuousFunctionLM 𝕜 : 𝓓^{0}_{K}(E, E [×i]→L[ℝ] F) →ₗ[𝕜] E →ᵇ (E [×i]→L[ℝ] F)) ∘ₗ
      (iteratedFDerivLM 𝕜 n 0 i (by rwa [zero_add]) :
        𝓓^{n}_{K}(E, F) →ₗ[𝕜] 𝓓^{0}_{K}(E, E [×i]→L[ℝ] F)) :=
  rfl

@[simp]
lemma structureMapLM_apply {i : ℕ} (hi : (i : ℕ∞) ≤ n) (f : 𝓓^{n}_{K}(E, F)) :
    structureMapLM 𝕜 n i hi f = iteratedFDeriv ℝ i f :=
  rfl

lemma structureMapLM_eq_of_scalars {i : ℕ} (𝕜' : Type*) [NontriviallyNormedField 𝕜']
    [NormedSpace 𝕜' F] [SMulCommClass ℝ 𝕜' F] (hi : (i : ℕ∞) ≤ n) :
    (structureMapLM 𝕜 n i hi : 𝓓^{n}_{K}(E, F) → _) = structureMapLM 𝕜' n i hi :=
  rfl

lemma structureMapLM_zero_apply {f : 𝓓^{n}_{K}(E, F)} {x : E} :
    structureMapLM 𝕜 n 0 (by simp) f x = ContinuousMultilinearMap.uncurry0 ℝ E (f x) := by
  ext
  simp [iteratedFDeriv_zero_eq_comp]

lemma structureMapLM_zero_injective :
    Injective (structureMapLM 𝕜 n 0 (by simp) : 𝓓^{n}_{K}(E, F) → E →ᵇ E [×0]→L[ℝ] F) := by
  intro f g hfg
  simpa [BoundedContinuousFunction.ext_iff, ContinuousMultilinearMap.ext_iff,
    structureMapLM_zero_apply, ContDiffMapSupportedIn.ext_iff] using hfg

section Topology

noncomputable instance topologicalSpace : TopologicalSpace 𝓓^{n}_{K}(E, F) :=
  ⨅ (i : {i : ℕ // (i : ℕ∞) ≤ n}), induced (structureMapLM ℝ n i i.2) inferInstance

noncomputable instance uniformSpace : UniformSpace 𝓓^{n}_{K}(E, F) := .replaceTopology
  (⨅ (i : {i : ℕ // (i : ℕ∞) ≤ n}), UniformSpace.comap (structureMapLM ℝ n i i.2) inferInstance)
  toTopologicalSpace_iInf.symm

protected theorem uniformSpace_eq_iInf : (uniformSpace : UniformSpace 𝓓^{n}_{K}(E, F)) =
    ⨅ (i : {i : ℕ // (i : ℕ∞) ≤ n}), UniformSpace.comap (structureMapLM ℝ n i i.2) inferInstance :=
  UniformSpace.replaceTopology_eq _ toTopologicalSpace_iInf.symm

instance isTopologicalAddGroup : IsTopologicalAddGroup 𝓓^{n}_{K}(E, F) :=
  isTopologicalAddGroup_iInf fun _ ↦ isTopologicalAddGroup_induced _

instance isUniformAddGroup : IsUniformAddGroup 𝓓^{n}_{K}(E, F) := by
  rw [ContDiffMapSupportedIn.uniformSpace_eq_iInf]
  exact isUniformAddGroup_iInf fun _ ↦ IsUniformAddGroup.comap _

instance continuousSMul : ContinuousSMul 𝕜 𝓓^{n}_{K}(E, F) :=
  continuousSMul_iInf fun i ↦ continuousSMul_induced (structureMapLM 𝕜 n i i.2)

instance locallyConvexSpace : LocallyConvexSpace ℝ 𝓓^{n}_{K}(E, F) :=
  LocallyConvexSpace.iInf fun _ ↦ LocallyConvexSpace.induced _

variable (n) in
/-- `structureMapCLM 𝕜 n i` is the continuous `𝕜`-linear-map sending `f : 𝓓^{n}_{K}(E, F)` to its
`i`-th iterated derivative as an element of `E →ᵇ (E [×i]→L[ℝ] F)`. It is defined when `i ≤ n`;
the proof `hi` can usually be omitted, see `regularity_le`.

We call these "structure maps" because they define the topology on `𝓓^{n}_{K}(E, F)`. -/
noncomputable def structureMapCLM (i : ℕ) (hi : (i : ℕ∞) ≤ n := by regularity_le) :
    𝓓^{n}_{K}(E, F) →L[𝕜] E →ᵇ (E [×i]→L[ℝ] F) where
  toLinearMap := structureMapLM 𝕜 n i hi
  cont := continuous_iInf_dom (i := ⟨i, hi⟩) continuous_induced_dom

@[simp]
lemma structureMapCLM_apply {i : ℕ} (hi : (i : ℕ∞) ≤ n) (f : 𝓓^{n}_{K}(E, F)) :
    structureMapCLM 𝕜 n i hi f = iteratedFDeriv ℝ i f :=
  rfl

lemma structureMapCLM_eq_of_scalars {i : ℕ} (𝕜' : Type*) [NontriviallyNormedField 𝕜']
    [NormedSpace 𝕜' F] [SMulCommClass ℝ 𝕜' F] (hi : (i : ℕ∞) ≤ n) :
    (structureMapCLM 𝕜 n i hi : 𝓓^{n}_{K}(E, F) → _) = structureMapCLM 𝕜' n i hi :=
  rfl

lemma structureMapCLM_zero_apply {f : 𝓓^{n}_{K}(E, F)} {x : E} :
    structureMapCLM 𝕜 n 0 (by simp) f x = ContinuousMultilinearMap.uncurry0 ℝ E (f x) :=
  structureMapLM_zero_apply 𝕜

lemma structureMapCLM_zero_injective :
    Injective (structureMapCLM 𝕜 n 0 (by simp) : 𝓓^{n}_{K}(E, F) → E →ᵇ E [×0]→L[ℝ] F) :=
  structureMapLM_zero_injective 𝕜

lemma isUniformEmbedding_pi_structureMapCLM :
    IsUniformEmbedding (ContinuousLinearMap.pi fun i : {i : ℕ // (i : ℕ∞) ≤ n} ↦
      structureMapCLM 𝕜 n i i.2 :
        𝓓^{n}_{K}(E, F) →L[𝕜] Π i : {i : ℕ // (i : ℕ∞) ≤ n}, E →ᵇ (E [×i]→L[ℝ] F)) where
  injective f g hfg := structureMapCLM_zero_injective 𝕜 (congr($hfg ⟨0, by simp⟩))
  toIsUniformInducing := by
    simp_rw [isUniformInducing_iff_uniformSpace, ContDiffMapSupportedIn.uniformSpace_eq_iInf,
      Pi.uniformSpace_eq, comap_iInf, ← comap_comap]
    rfl

/-- The **universal property** of the topology on `𝓓^{n}_{K}(E, F)`: a map to `𝓓^{n}_{K}(E, F)`
is continuous if and only if its composition with the structure map
`structureMapCLM ℝ n i : 𝓓^{n}_{K}(E, F) → (E →ᵇ (E [×i]→L[ℝ] F))` is continuous for each
`i ≤ n`. -/
-- Note: if needed, we could allow an extra parameter `𝕜` in case the user wants to use
-- `structureMapCLM 𝕜 n i`.
theorem continuous_iff_comp {X} [TopologicalSpace X] (φ : X → 𝓓^{n}_{K}(E, F)) :
    Continuous φ ↔ ∀ (i : ℕ) (hi : (i : ℕ∞) ≤ n), Continuous (structureMapCLM ℝ n i hi ∘ φ) := by
  simp [continuous_iInf_rng, continuous_induced_rng, structureMapCLM, Subtype.forall]

variable (E F n K)

/-- The seminorms on the space `𝓓^{n}_{K}(E, F)` given by the sup norm of the iterated derivatives
of order `i ≤ n`; the proof `hi` can usually be omitted, see `regularity_le`.
In the scope `Distributions.Seminorm`, we denote them by `N[𝕜; F]_{K, n, i}`
(or `N[𝕜]_{K, n, i}`), or simply by `N[𝕜; F]_{K, i}` (or `N[𝕜; F]_{K, i}`) when `n = ∞`. -/
protected noncomputable def seminorm (i : ℕ) (hi : (i : ℕ∞) ≤ n := by regularity_le) :
    Seminorm 𝕜 𝓓^{n}_{K}(E, F) :=
  (normSeminorm 𝕜 (E →ᵇ (E [×i]→L[ℝ] F))).comp (structureMapLM 𝕜 n i hi)

-- Note: If these end up conflicting with other seminorms (e.g `SchwartzMap.seminorm`),
-- we may want to put them in a more specific scope.
@[inherit_doc ContDiffMapSupportedIn.seminorm]
scoped[Distributions] notation "N[" 𝕜 "]_{" K ", " n ", " i "}" =>
  (ContDiffMapSupportedIn.seminorm 𝕜 _ _ n K i : Seminorm 𝕜 _)

@[inherit_doc ContDiffMapSupportedIn.seminorm]
scoped[Distributions] notation "N[" 𝕜 "]_{" K ", " i "}" =>
  (ContDiffMapSupportedIn.seminorm 𝕜 _ _ ⊤ K i : Seminorm 𝕜 _)

@[inherit_doc ContDiffMapSupportedIn.seminorm]
scoped[Distributions] notation "N[" 𝕜 "; " F "]_{" K ", " n ", " i "}" =>
  (ContDiffMapSupportedIn.seminorm 𝕜 _ F n K i : Seminorm 𝕜 _)

@[inherit_doc ContDiffMapSupportedIn.seminorm]
scoped[Distributions] notation "N[" 𝕜 "; " F "]_{" K ", " i "}" =>
  (ContDiffMapSupportedIn.seminorm 𝕜 _ F ⊤ K i : Seminorm 𝕜 _)

/-- The seminorms `N[𝕜]_{K, n, i}` of `𝓓^{n}_{K}(E, F)` for `i ≤ n`, indexed by these `i`. They
define its topology (`ContDiffMapSupportedIn.withSeminorms`). -/
protected noncomputable def seminormFamily :
    SeminormFamily 𝕜 𝓓^{n}_{K}(E, F) {i : ℕ // (i : ℕ∞) ≤ n} :=
  fun i ↦ ContDiffMapSupportedIn.seminorm 𝕜 E F n K i i.2

@[simp]
lemma seminormFamily_apply (i : {i : ℕ // (i : ℕ∞) ≤ n}) :
    ContDiffMapSupportedIn.seminormFamily 𝕜 E F n K i =
      ContDiffMapSupportedIn.seminorm 𝕜 E F n K i i.2 :=
  rfl

/-- The seminorms on the space `𝓓^{n}_{K}(E, F)` given by sup of the
`ContDiffMapSupportedIn.seminorm j` for `j ≤ i`, for `i ≤ n`. -/
protected noncomputable def supSeminorm (i : ℕ) (hi : (i : ℕ∞) ≤ n := by regularity_le) :
    Seminorm 𝕜 𝓓^{n}_{K}(E, F) :=
  (Finset.Iic i).attach.sup fun j ↦ ContDiffMapSupportedIn.seminorm 𝕜 E F n K j
    ((Nat.cast_le.2 (Finset.mem_Iic.1 j.2)).trans hi)

protected theorem withSeminorms :
    WithSeminorms (ContDiffMapSupportedIn.seminormFamily 𝕜 E F n K) := by
  let p : SeminormFamily 𝕜 𝓓^{n}_{K}(E, F) ((_ : {i : ℕ // (i : ℕ∞) ≤ n}) × Fin 1) :=
    SeminormFamily.sigma fun i _ ↦
      (normSeminorm 𝕜 (E →ᵇ (E [×i]→L[ℝ] F))).comp (structureMapLM 𝕜 n i i.2)
  have : WithSeminorms p :=
    withSeminorms_iInf fun i ↦ LinearMap.withSeminorms_induced (norm_withSeminorms _ _) _
  exact this.congr_equiv (Equiv.sigmaUnique _ _).symm

protected theorem withSeminorms' :
    WithSeminorms fun i : {i : ℕ // (i : ℕ∞) ≤ n} ↦
      ContDiffMapSupportedIn.supSeminorm 𝕜 E F n K i i.2 := by
  refine (ContDiffMapSupportedIn.withSeminorms 𝕜 E F n K).congr (fun i ↦ ?_) (fun i ↦ ?_)
  · refine ⟨(Finset.Iic i.1).subtype fun j : ℕ ↦ (j : ℕ∞) ≤ n, 1, ?_⟩
    rw [Seminorm.comp_id, one_smul]
    refine Finset.sup_le fun j _ ↦ ?_
    exact Finset.le_sup (f := ContDiffMapSupportedIn.seminormFamily 𝕜 E F n K)
      (b := ⟨j, (Nat.cast_le.2 (Finset.mem_Iic.1 j.2)).trans i.2⟩) (Finset.mem_subtype.2 j.2)
  · refine ⟨{i}, 1, ?_⟩
    rw [Seminorm.comp_id, Finset.sup_singleton, one_smul]
    exact Finset.le_sup (f := fun j : {j // j ∈ Finset.Iic i.1} ↦
        ContDiffMapSupportedIn.seminorm 𝕜 E F n K j
          ((Nat.cast_le.2 (Finset.mem_Iic.1 j.2)).trans i.2))
      (b := ⟨i.1, Finset.mem_Iic.2 le_rfl⟩) (Finset.mem_attach _ _)

variable {E F n K}

protected theorem seminorm_apply (i : ℕ) (hi : (i : ℕ∞) ≤ n) (f : 𝓓^{n}_{K}(E, F)) :
    N[𝕜]_{K, n, i} f = ‖structureMapCLM 𝕜 n i hi f‖ :=
  rfl

protected theorem seminorm_le_iff {C : ℝ} (hC : 0 ≤ C) (i : ℕ) (hi : (i : ℕ∞) ≤ n)
    (f : 𝓓^{n}_{K}(E, F)) :
    N[𝕜]_{K, n, i} f ≤ C ↔ ∀ x ∈ K, ‖iteratedFDeriv ℝ i f x‖ ≤ C := by
  have : (∀ x, ‖iteratedFDeriv ℝ i f x‖ ≤ C) ↔ (∀ x ∈ K, ‖iteratedFDeriv ℝ i f x‖ ≤ C) := by
    congrm ∀ x, ?_
    by_cases hx : x ∈ K
    · simp [hx]
    · simp [hx, f.iteratedFDeriv_zero_on_compl hx, hC]
  simp [ContDiffMapSupportedIn.seminorm_apply 𝕜 i hi, BoundedContinuousFunction.norm_le hC, this]

protected theorem seminorm_top_le_iff {C : ℝ} (hC : 0 ≤ C) (i : ℕ) (f : 𝓓_{K}(E, F)) :
    N[𝕜]_{K, i} f ≤ C ↔ ∀ x ∈ K, ‖iteratedFDeriv ℝ i f x‖ ≤ C :=
  ContDiffMapSupportedIn.seminorm_le_iff 𝕜 hC i le_top f

theorem norm_iteratedFDeriv_apply_le_seminorm {i : ℕ} (hin : (i : ℕ∞) ≤ n)
    {f : 𝓓^{n}_{K}(E, F)} {x : E} :
    ‖iteratedFDeriv ℝ i f x‖ ≤ N[𝕜]_{K, n, i} f :=
  BoundedContinuousFunction.norm_coe_le_norm (structureMapLM ℝ n i hin f) x

theorem norm_iteratedFDeriv_apply_le_seminorm_top {i : ℕ}
    {f : 𝓓_{K}(E, F)} {x : E} :
    ‖iteratedFDeriv ℝ i f x‖ ≤ N[𝕜]_{K, i} f :=
  norm_iteratedFDeriv_apply_le_seminorm 𝕜 le_top

theorem norm_apply_le_seminorm {f : 𝓓^{n}_{K}(E, F)} {x : E} :
    ‖f x‖ ≤ N[𝕜]_{K, n, 0} f := by
  rw [← norm_iteratedFDeriv_zero (𝕜 := ℝ) (f := f) (x := x)]
  exact norm_iteratedFDeriv_apply_le_seminorm 𝕜 _

theorem norm_toBoundedContinuousFunction (f : 𝓓^{n}_{K}(E, F)) :
    ‖(f : E →ᵇ F)‖ = N[𝕜]_{K, n, 0} f := by
  simp [BoundedContinuousFunction.norm_eq_iSup_norm,
    ContDiffMapSupportedIn.seminorm_apply 𝕜 0 (by simp)]

/-- Define a continuous `𝕜`-linear map from `𝓓^{n₁}_{K₁}(E, F)` to `𝓓^{n₂}_{K₂}(E, F')`. -/
protected noncomputable def mkCLM (A : 𝓓^{n₁}_{K₁}(E, F) → E → F')
    (hadd : ∀ f g x, A (f + g) x = A f x + A g x)
    (hsmul : ∀ (c : 𝕜) f x, A (c • f) x = c • A f x)
    (hsmooth : ∀ f, ContDiff ℝ n₂ (A f))
    (hsupp : ∀ f, EqOn (A f) 0 K₂ᶜ)
    (hbound : ∀ i : ℕ, (i : ℕ∞) ≤ n₂ →
      ∃ (s : Finset {j : ℕ // (j : ℕ∞) ≤ n₁}) (C : ℝ), 0 ≤ C ∧ ∀ f, ∀ x ∈ K₂,
        ‖iteratedFDeriv ℝ i (A f) x‖ ≤
          C * (s.sup (ContDiffMapSupportedIn.seminormFamily 𝕜 E F n₁ K₁)) f) :
    𝓓^{n₁}_{K₁}(E, F) →L[𝕜] 𝓓^{n₂}_{K₂}(E, F') :=
  letI Φ : 𝓓^{n₁}_{K₁}(E, F) →ₗ[𝕜] 𝓓^{n₂}_{K₂}(E, F') :=
    { toFun f := ⟨A f, hsmooth f, hsupp f⟩
      map_add' f g := ext (hadd f g)
      map_smul' c f := ext (hsmul c f) }
  { toLinearMap := Φ
    cont := show Continuous Φ by
      refine continuous_of_isBounded (ContDiffMapSupportedIn.withSeminorms ..)
        (ContDiffMapSupportedIn.withSeminorms ..) _ (.of_real fun i ↦ ?_)
      obtain ⟨s, C, hC, h⟩ := hbound i i.2
      exact ⟨s, C, fun f ↦
        ((Φ f).seminorm_le_iff 𝕜 (mul_nonneg hC (apply_nonneg _ _)) i i.2).2 fun x hx ↦
          h f x hx⟩ }

/-- Define a continous `𝕜`-linear map fom `𝓓^{n}_{K}(E, F)` to a normed space. -/
protected noncomputable def mkCLMtoNormedSpace {G : Type*} [NormedAddCommGroup G]
    [NormedSpace 𝕜 G] (A : 𝓓^{n}_{K}(E, F) → G)
    (hadd : ∀ f g, A (f + g) = A f + A g)
    (hsmul : ∀ (c : 𝕜) f, A (c • f) = c • A f)
    (hbound : ∃ (s : Finset {i : ℕ // (i : ℕ∞) ≤ n}) (C : ℝ), 0 ≤ C ∧ ∀ f,
      ‖A f‖ ≤ C * (s.sup (ContDiffMapSupportedIn.seminormFamily 𝕜 E F n K)) f) :
    𝓓^{n}_{K}(E, F) →L[𝕜] G :=
  letI Φ : 𝓓^{n}_{K}(E, F) →ₗ[𝕜] G := ⟨⟨A, hadd⟩, hsmul⟩
  { toLinearMap := Φ
    cont := show Continuous Φ by
      obtain ⟨s, C, hC, h⟩ := hbound
      exact continuous_normedSpace_rng G (ContDiffMapSupportedIn.withSeminorms 𝕜 E F n K)
        Φ ⟨s, ⟨C, hC⟩, h⟩ }

/-- The inclusion of the space `𝓓^{n}_{K}(E, F)` into the space `E →ᵇ F` of bounded continuous
functions as a continuous `𝕜`-linear map. -/
noncomputable def toBoundedContinuousFunctionCLM : 𝓓^{n}_{K}(E, F) →L[𝕜] E →ᵇ F where
  toLinearMap := toBoundedContinuousFunctionLM 𝕜
  cont := show Continuous (toBoundedContinuousFunctionLM 𝕜) by
    refine continuous_of_isBounded (ContDiffMapSupportedIn.withSeminorms ..)
      (norm_withSeminorms 𝕜 _) _ (fun _ ↦ ⟨{⟨0, by simp⟩}, 1, fun f ↦ ?_⟩)
    simp [norm_toBoundedContinuousFunction 𝕜 f]

@[simp]
lemma toBoundedContinuousFunctionCLM_apply (f : 𝓓^{n}_{K}(E, F)) :
    toBoundedContinuousFunctionCLM 𝕜 f = f :=
  rfl

lemma toBoundedContinuousFunctionCLM_eq_of_scalars (𝕜' : Type*) [NontriviallyNormedField 𝕜']
    [NormedSpace 𝕜' F] [SMulCommClass ℝ 𝕜' F] :
    (toBoundedContinuousFunctionCLM 𝕜 : 𝓓^{n}_{K}(E, F) → _) = toBoundedContinuousFunctionCLM 𝕜' :=
  rfl

instance : ContinuousEval 𝓓^{n}_{K}(E, F) E F :=
  ContinuousEval.of_continuous_forget
    (toBoundedContinuousFunctionCLM ℝ).continuous

instance : T3Space 𝓓^{n}_{K}(E, F) :=
  have : Injective (toBoundedContinuousFunctionCLM ℝ : 𝓓^{n}_{K}(E, F) →L[ℝ] E →ᵇ F) :=
    fun _ _ hfg ↦ ext fun x ↦ congr(($hfg : E → F) x)
  have : T2Space 𝓓^{n}_{K}(E, F) := .of_injective_continuous this
    (toBoundedContinuousFunctionCLM ℝ).continuous
  inferInstance

theorem seminorm_postcompLM_le [LinearMap.CompatibleSMul F F' ℝ 𝕜] {i : ℕ} (hi : (i : ℕ∞) ≤ n)
    (T : F →L[𝕜] F') (f : 𝓓^{n}_{K}(E, F)) :
    N[𝕜]_{K, n, i} (postcompLM T f) ≤ ‖T‖ * N[𝕜]_{K, n, i} f := by
  set T' := T.restrictScalars ℝ
  change N[ℝ]_{K, n, i} (postcompLM T' f) ≤ ‖T'‖ * N[ℝ]_{K, n, i} f
  rw [ContDiffMapSupportedIn.seminorm_le_iff ℝ (by positivity) i hi]
  intro x hx
  rw [postcompLM_apply]
  calc
      ‖iteratedFDeriv ℝ i (T' ∘ f) x‖
  _ = ‖T'.compContinuousMultilinearMap (iteratedFDeriv ℝ i f x)‖ := by
        rw [T'.iteratedFDeriv_comp_left f.contDiff.contDiffAt (mod_cast hi)]
  _ ≤ ‖T'‖ * ‖iteratedFDeriv ℝ i f x‖ := T'.norm_compContinuousMultilinearMap_le _
  _ ≤ ‖T'‖ * N[ℝ]_{K, n, i} f := by grw [norm_iteratedFDeriv_apply_le_seminorm ℝ hi]

variable {𝕜} in
-- Note: generalizing this to a semilinear setting would require a semilinear version of
-- `CompatibleSMul`.
/-- Given `T : F →L[𝕜] F'`, `postcompCLM T` is the continuous `𝕜`-linear-map sending
`f : 𝓓^{n}_{K}(E, F)` to `T ∘ f` as an element of `𝓓^{n}_{K}(E, F')`. -/
noncomputable def postcompCLM [LinearMap.CompatibleSMul F F' ℝ 𝕜] (T : F →L[𝕜] F') :
    𝓓^{n}_{K}(E, F) →L[𝕜] 𝓓^{n}_{K}(E, F') where
  toLinearMap := postcompLM T
  cont := show Continuous (postcompLM T) by
    refine continuous_of_isBounded (ContDiffMapSupportedIn.withSeminorms ..)
      (ContDiffMapSupportedIn.withSeminorms ..) _ (.of_real fun i ↦ ⟨{i}, ‖T‖, fun f ↦ ?_⟩)
    simpa using seminorm_postcompLM_le 𝕜 i.2 T f

@[simp]
lemma postcompCLM_apply [LinearMap.CompatibleSMul F F' ℝ 𝕜] (T : F →L[𝕜] F')
    (f : 𝓓^{n}_{K}(E, F)) :
    postcompCLM T f = T ∘ f :=
  rfl

theorem seminorm_monoLM_le {i : ℕ} (hK : K₁ ≤ K₂) (hn : n₂ ≤ n₁) (hi : (i : ℕ∞) ≤ n₂)
    (f : 𝓓^{n₁}_{K₁}(E, F)) :
    N[𝕜]_{K₂, n₂, i} (monoLM 𝕜 hK hn f) ≤
      ContDiffMapSupportedIn.seminorm 𝕜 E F n₁ K₁ i (hi.trans hn) f := by
  rw [ContDiffMapSupportedIn.seminorm_le_iff 𝕜 (by positivity) i hi]
  intro x _
  exact norm_iteratedFDeriv_apply_le_seminorm _ (hi.trans hn)

theorem seminorm_monoLM_eq {i : ℕ} (hK : K₁ ≤ K₂) (hi : (i : ℕ∞) ≤ n₁)
    (f : 𝓓^{n₁}_{K₁}(E, F)) :
    ContDiffMapSupportedIn.seminorm 𝕜 E F n₁ K₂ i hi (monoLM 𝕜 hK le_rfl f) =
      N[𝕜]_{K₁, n₁, i} f := by
  simp [BoundedContinuousFunction.norm_eq_iSup_norm, ContDiffMapSupportedIn.seminorm_apply 𝕜 i hi]

/-- If `n₁ ≥ n₂` and `K₁ ⊆ K₂`, `monoCLM 𝕜 hK hn` is the continuous `𝕜`-linear inclusion of
`𝓓^{n₁}_{K₁}(E, F)` inside `𝓓^{n₂}_{K₂}(E, F)`. The proof `hn` of `n₂ ≤ n₁` can usually be
omitted, see `regularity_le`.

Furthermore:
* it is a topological embedding when `n₁ = n₂` and `K₁ ⊆ K₂` (not in Mathlib as of March 2026).
* it maps bounded sets to compact sets when `n₁ ≥ n₂ + 1` and `K₁ ⊆ K₂` (not in Mathlib as of
March 2026).

The parameters `n₁, n₂, K₁, K₂` are implicit as they can often be inferred from context, or
specified by a type ascription.
-/
noncomputable def monoCLM (hK : K₁ ≤ K₂) (hn : n₂ ≤ n₁ := by regularity_le) :
    𝓓^{n₁}_{K₁}(E, F) →L[𝕜] 𝓓^{n₂}_{K₂}(E, F) where
  toLinearMap := monoLM 𝕜 hK hn
  cont := show Continuous (monoLM 𝕜 hK hn) by
    refine continuous_of_isBounded (ContDiffMapSupportedIn.withSeminorms _ _ _ _ _)
      (ContDiffMapSupportedIn.withSeminorms _ _ _ _ _) _
      (fun i ↦ ⟨{⟨i, i.2.trans hn⟩}, 1, fun f ↦ ?_⟩)
    simpa using seminorm_monoLM_le 𝕜 hK hn i.2 f

@[simp]
lemma monoCLM_apply (hK : K₁ ≤ K₂) (hn : n₂ ≤ n₁) (f : 𝓓^{n₁}_{K₁}(E, F)) :
    ((monoCLM 𝕜 hK hn f : 𝓓^{n₂}_{K₂}(E, F)) : E → F) = f :=
  rfl

lemma monoCLM_eq_of_scalars (𝕜' : Type*)
    [NontriviallyNormedField 𝕜'] [NormedSpace 𝕜' F] [SMulCommClass ℝ 𝕜' F] (hK : K₁ ≤ K₂)
    (hn : n₂ ≤ n₁) :
    (monoCLM 𝕜 hK hn : 𝓓^{n₁}_{K₁}(E, F) → 𝓓^{n₂}_{K₂}(E, F)) = monoCLM 𝕜' hK hn :=
  rfl

theorem seminorm_fderivLM_le {i : ℕ} (hk : k + 1 ≤ n) (hi : (i : ℕ∞) ≤ k)
    (f : 𝓓^{n}_{K}(E, F)) :
    N[𝕜]_{K, k, i} (fderivLM 𝕜 n k hk f) ≤
      ContDiffMapSupportedIn.seminorm 𝕜 E F n K (i + 1)
        (by push_cast; exact (add_le_add_left hi 1).trans hk) f := by
  rw [ContDiffMapSupportedIn.seminorm_le_iff 𝕜 (apply_nonneg ..) i hi]
  intro x hx
  simpa [norm_iteratedFDeriv_fderiv] using
    norm_iteratedFDeriv_apply_le_seminorm 𝕜 (n := n) (i := i + 1)
      (by push_cast; exact (add_le_add_left hi 1).trans hk) (f := f) (x := x)

theorem seminorm_fderivLM_top {i : ℕ} (f : 𝓓_{K}(E, F)) :
    N[𝕜]_{K, i} (fderivLM 𝕜 ⊤ ⊤ le_top f) = N[𝕜]_{K, i + 1} f := by
  simp [ContDiffMapSupportedIn.seminorm_apply 𝕜 _ le_top,
    BoundedContinuousFunction.norm_eq_iSup_norm, norm_iteratedFDeriv_fderiv]

variable (n k) in
/-- `fderivCLM 𝕜 n k` is the continuous `𝕜`-linear-map sending `f : 𝓓^{n}_{K}(E, F)` to
its derivative as an element of `𝓓^{k}_{K}(E, E →L[ℝ] F)`. It is defined when `k + 1 ≤ n`; the
proof `hk` can usually be omitted, see `regularity_le`. -/
noncomputable def fderivCLM (hk : k + 1 ≤ n := by regularity_le) :
    𝓓^{n}_{K}(E, F) →L[𝕜] 𝓓^{k}_{K}(E, E →L[ℝ] F) where
  toLinearMap := fderivLM 𝕜 n k hk
  cont := show Continuous (fderivLM 𝕜 n k hk) by
    refine continuous_of_isBounded (ContDiffMapSupportedIn.withSeminorms ..)
      (ContDiffMapSupportedIn.withSeminorms ..) _
      (fun i ↦ ⟨{⟨i + 1, by push_cast; exact (add_le_add_left i.2 1).trans hk⟩}, 1, fun f ↦ ?_⟩)
    simpa using seminorm_fderivLM_le 𝕜 hk i.2 f

@[simp]
lemma fderivCLM_apply (hk : k + 1 ≤ n) (f : 𝓓^{n}_{K}(E, F)) :
    fderivCLM 𝕜 n k hk f = fderiv ℝ f :=
  rfl

lemma fderivCLM_eq_of_scalars (𝕜' : Type*) [NontriviallyNormedField 𝕜']
    [NormedSpace 𝕜' F] [SMulCommClass ℝ 𝕜' F] (hk : k + 1 ≤ n) :
    (fderivCLM 𝕜 n k hk : 𝓓^{n}_{K}(E, F) → _) = fderivCLM 𝕜' n k hk :=
  rfl

end Topology

section Integral

open MeasureTheory

variable {𝕜} {m : SigmaAlgebra E} [OpensSigmaAlgebra E] {F₁ F₂ F₃ : Type*}
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [NormedSpace ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃]

@[fun_prop]
protected theorem stronglyMeasurable (f : 𝓓^{n}_{K}(E, F)) :
    StronglyMeasurable f := by
  exact f.continuous.stronglyMeasurable_of_hasCompactSupport f.hasCompactSupport

@[fun_prop]
protected theorem aestronglyMeasurable {μ : Measure E} (f : 𝓓^{n}_{K}(E, F)) :
    AEStronglyMeasurable f μ :=
  f.stronglyMeasurable.aestronglyMeasurable

protected theorem memLp_top {μ : Measure E} (f : 𝓓^{n}_{K}(E, F)) :
    MemLp f ⊤ μ :=
  f.continuous.memLp_top_of_hasCompactSupport f.hasCompactSupport μ

protected theorem integrable {μ : Measure E} [μ_finite : IsFiniteMeasure (μ.restrict K)]
    (f : 𝓓^{n}_{K}(E, F)) :
    Integrable f μ := by
  rw [← integrableOn_iff_integrable_of_support_subset f.support_subset]
  exact f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport

protected theorem integrable_bilin (B : F₁ →L[𝕜] F₂ →L[𝕜] F₃) {μ : Measure E} {φ : E → F₂}
    (hφ : IntegrableOn φ K μ) (f : 𝓓^{n}_{K}(E, F₁)) :
    Integrable (fun x ↦ B (f x) (φ x)) μ := by
  suffices IntegrableOn (fun x ↦ B (f x) (φ x)) K μ by
    rwa [integrableOn_iff_integrable_of_support_subset] at this
    refine subset_trans ?_ f.support_subset
    exact fun x hx hfx ↦ hx (by simp [hfx])
  rw [IntegrableOn, ← memLp_one_iff_integrable] at hφ ⊢
  exact B.memLp_of_bilin 1 f.memLp_top hφ

variable [SMulCommClass ℝ 𝕜 F₁] [NormedSpace ℝ F₃] [SMulCommClass ℝ 𝕜 F₃]

-- TODO: semilinearize
/-- Given a continuous `𝕜`-bilinear map `B : F₁ →L[𝕜] F₂ →L[𝕜] F₃`, a measure `μ` on `E`,
and a function `φ : E → F₂` which is `μ`-integrable on `K`, this is the `𝕜`-linear map
`f ↦ ∫ x, B (f x) (φ x) ∂μ` from `𝓓^{n}_{K}(E, F₁)` to `F₃`.

You should probably use `integralAgainstBilinCLM`, which bundles the continuity. -/
noncomputable def integralAgainstBilinLM (B : F₁ →L[𝕜] F₂ →L[𝕜] F₃) (μ : Measure E) (φ : E → F₂)
    (hφ : IntegrableOn φ K μ) : 𝓓^{n}_{K}(E, F₁) →ₗ[𝕜] F₃ where
  toFun f := ∫ x, B (f x) (φ x) ∂μ
  map_add' f g := by
    simp_rw [add_apply, map_add, add_apply,
      integral_add (f.integrable_bilin B hφ) (g.integrable_bilin B hφ)]
  map_smul' c f := by
    simp_rw [smul_apply, map_smul, smul_apply, integral_smul c, RingHom.id_apply]

@[simp]
lemma integralAgainstBilinLM_apply {B : F₁ →L[𝕜] F₂ →L[𝕜] F₃} {μ : Measure E} {φ : E → F₂}
    {hφ : IntegrableOn φ K μ} {f : 𝓓^{n}_{K}(E, F₁)} :
    integralAgainstBilinLM B μ φ hφ f = ∫ x, B (f x) (φ x) ∂μ :=
  rfl

lemma integralAgainstBilinLM_eq_setIntegral {B : F₁ →L[𝕜] F₂ →L[𝕜] F₃} {μ : Measure E} {φ : E → F₂}
    {hφ : IntegrableOn φ K μ} {f : 𝓓^{n}_{K}(E, F₁)} :
    integralAgainstBilinLM B μ φ hφ f = ∫ x in K, B (f x) (φ x) ∂μ := by
  rw [integralAgainstBilinLM_apply, setIntegral_eq_integral_of_forall_compl_eq_zero]
  intro x hx
  rw [f.zero_on_compl hx, Pi.zero_apply, map_zero, zero_apply]

lemma norm_integralAgainstBilinLM_le {B : F₁ →L[𝕜] F₂ →L[𝕜] F₃} {μ : Measure E} {φ : E → F₂}
    {hφ : IntegrableOn φ K μ} {f : 𝓓^{n}_{K}(E, F₁)} :
    ‖integralAgainstBilinLM B μ φ hφ f‖ ≤
      (∫ x in K, ‖φ x‖ ∂μ) * ‖B‖ * N[𝕜]_{K, n, 0} f := by
  have h : ∀ᵐ x ∂(μ.restrict K), ‖B (f x) (φ x)‖ ≤ ‖φ x‖ * ‖B‖ * N[𝕜]_{K, n, 0} f := by
    filter_upwards [] with x
    grw [ContinuousLinearMap.le_opNorm, ContinuousLinearMap.le_opNorm, norm_apply_le_seminorm 𝕜,
      mul_comm, mul_assoc]
  rw [integralAgainstBilinLM_eq_setIntegral]
  apply le_trans (norm_integral_le_of_norm_le ((hφ.norm.mul_const _).mul_const _) h)
  rw [integral_mul_const, integral_mul_const]

-- TODO: semilinearize
/-- Given a continuous `𝕜`-bilinear map `B : F₁ →L[𝕜] F₂ →L[𝕜] F₃`, a measure `μ` on `E`,
and a function `φ : E → F₂` which is integrable on `K`, this is the *continuous* `𝕜`-linear map
`f ↦ ∫ x, B (f x) (φ x) ∂μ` from `𝓓^{n}_{K}(E, F₁)` to `F₃`. -/
noncomputable def integralAgainstBilinCLM (B : F₁ →L[𝕜] F₂ →L[𝕜] F₃) (μ : Measure E) (φ : E → F₂)
    (hφ : IntegrableOn φ K μ) : 𝓓^{n}_{K}(E, F₁) →L[𝕜] F₃ :=
  ContDiffMapSupportedIn.mkCLMtoNormedSpace 𝕜 (integralAgainstBilinLM B μ φ hφ)
    (integralAgainstBilinLM B μ φ hφ).map_add (integralAgainstBilinLM B μ φ hφ).map_smul
    ⟨{⟨0, by simp⟩}, (∫ x in K, ‖φ x‖ ∂μ) * ‖B‖, by positivity,
      fun f ↦ by simpa using! norm_integralAgainstBilinLM_le (hφ := hφ)⟩

@[simp]
lemma integralAgainstBilinCLM_apply {B : F₁ →L[𝕜] F₂ →L[𝕜] F₃} {μ : Measure E} {φ : E → F₂}
    {hφ : IntegrableOn φ K μ} {f : 𝓓^{n}_{K}(E, F₁)} :
    integralAgainstBilinCLM B μ φ hφ f = ∫ x, B (f x) (φ x) ∂μ :=
  integralAgainstBilinLM_apply (hφ := hφ)

lemma integralAgainstBilinCLM_eq_setIntegral {B : F₁ →L[𝕜] F₂ →L[𝕜] F₃} {μ : Measure E} {φ : E → F₂}
    {hφ : IntegrableOn φ K μ} {f : 𝓓^{n}_{K}(E, F₁)} :
    integralAgainstBilinCLM B μ φ hφ f = ∫ x in K, B (f x) (φ x) ∂μ :=
  integralAgainstBilinLM_eq_setIntegral (hφ := hφ)

end Integral

section Multiplication

section bilin

open ContDiffMapSupportedIn

variable {F₁ F₂ F₃ G : Type*} [NormedAlgebra ℝ 𝕜]
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] [NormedSpace ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [NormedSpace ℝ F₂]
  [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃] [NormedSpace ℝ F₃]

open ContinuousLinearMap Finset

variable {𝕜}
/-- The map `f ↦ (x ↦ B (f x) (g x))` as a continuous `𝕜`-linear map on 𝓓^{n}_{K}(E, F₁),
where `B` is a continuous `𝕜`-linear map and `g` is a C^n function.

TODO: Introduce a type of bundled C^k functions. -/
noncomputable def bilinLeftCLM (B : F₁ →L[𝕜] F₂ →L[𝕜] F₃) {g : E → F₂} (hg : ContDiff ℝ n g) :
    𝓓^{n}_{K}(E, F₁) →L[𝕜] 𝓓^{n}_{K}(E, F₃) :=
  ContDiffMapSupportedIn.mkCLM 𝕜 (fun φ x ↦ B (φ x) (g x)) ?hadd ?hsmul (fun φ ↦ ?hsmooth)
    (fun φ x hx ↦ ?hsupp) (fun k hk ↦ ?hbound)
where finally
  case hadd | hsmul => intros; simp
  case hsmooth =>
    exact (B.bilinearRestrictScalars ℝ).isBoundedBilinearMap.contDiff.comp (φ.contDiff.prodMk hg)
  case hsupp => simp only [φ.zero_on_compl hx, Pi.zero_apply, map_zero, zero_apply]
  case hbound =>
    have hcont : Continuous fun x ↦ (Finset.range (k + 1)).sup' Finset.nonempty_range_add_one
        (fun i ↦ ‖iteratedFDeriv ℝ i g x‖) :=
      Continuous.finset_sup'_apply Finset.nonempty_range_add_one fun i hi ↦
        (hg.continuous_iteratedFDeriv (WithTop.coe_le_coe.2
          (le_trans (WithTop.coe_le_coe.2 (mem_range_succ_iff.mp hi)) hk))).norm
    obtain ⟨C₀, hC₀⟩ := K.isCompact.exists_bound_of_continuousOn hcont.continuousOn
    have hgC₀ : ∀ i ≤ k, ∀ x ∈ K, ‖iteratedFDeriv ℝ i g x‖ ≤ ‖C₀‖ := fun i hi x hx ↦
      (Finset.le_sup' _ (Finset.mem_range_succ_iff.2 hi)).trans
        ((Real.le_norm_self _).trans ((hC₀ x hx).trans (Real.le_norm_self C₀)))
    refine ⟨(Finset.Iic k).subtype fun j : ℕ ↦ (j : ℕ∞) ≤ n, ‖B‖ * 2 ^ k * ‖C₀‖, by positivity,
      fun φ x hx ↦ ?_⟩
    calc
      ‖iteratedFDeriv ℝ k (fun y ↦ B (φ y) (g y)) x‖
        ≤ ‖B‖ * ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i φ x‖ *
            ‖iteratedFDeriv ℝ (k - i) g x‖ := by
          simpa using (B.bilinearRestrictScalars ℝ).norm_iteratedFDeriv_le_of_bilinear
            φ.contDiff hg x (mod_cast hk)
      _ ≤ ‖B‖ * ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
            (((Finset.Iic k).subtype fun j : ℕ ↦ (j : ℕ∞) ≤ n).sup
              (ContDiffMapSupportedIn.seminormFamily 𝕜 E F₁ n K)) φ * ‖C₀‖ := by
          gcongr with i hi
          · have hik : (i : ℕ∞) ≤ n :=
              (WithTop.coe_le_coe.2 (mem_range_succ_iff.mp hi)).trans hk
            exact (norm_iteratedFDeriv_apply_le_seminorm 𝕜 hik).trans
              (Seminorm.le_finset_sup_apply (p := ContDiffMapSupportedIn.seminormFamily 𝕜 E F₁ n K)
                (i := ⟨i, hik⟩)
                (Finset.mem_subtype.2 (Finset.mem_Iic.2 (mem_range_succ_iff.mp hi))))
          · exact hgC₀ (k - i) (Nat.sub_le k i) x hx
      _ = ‖B‖ * 2 ^ k * ‖C₀‖ * (((Finset.Iic k).subtype fun j : ℕ ↦ (j : ℕ∞) ≤ n).sup
            (ContDiffMapSupportedIn.seminormFamily 𝕜 E F₁ n K)) φ := by
          simp_rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
          push_cast
          ring

@[simp]
theorem bilinLeftCLM_apply (B : F₁ →L[𝕜] F₂ →L[𝕜] F₃) {g : E → F₂} (hg : ContDiff ℝ n g)
    (φ : 𝓓^{n}_{K}(E, F₁)) : bilinLeftCLM B hg φ = fun x => B (φ x) (g x) := rfl

end bilin

end Multiplication

end ContDiffMapSupportedIn
