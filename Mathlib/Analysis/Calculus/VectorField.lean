/-
Copyright (c) 2024 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Vector fields in vector spaces

We study functions of the form `V : E → E` on a vector space, thinking of these as vector fields.
We define several notions in this context, with the aim to generalize them to vector fields on
manifolds.

The pullback of a vector field at a point is the unique vector whose image under the derivative
is the given target vector. Within a set the canonical pullback uses a unique derivative.
A supplied derivative also gives a pullback when its preimage is unique.

We also define the Lie bracket of two vector fields as
`VectorField.lieBracket 𝕜 V W x := fderiv 𝕜 W x id (V x) - fderiv 𝕜 V x id (W x)`
(together with the same notion within a set).

In addition to comprehensive API on these two notions, the main results are the following:
* `VectorField.pullback_lieBracket` states that the pullback of the Lie bracket
  is the Lie bracket of the pullbacks, when the second derivative is symmetric.
* `VectorField.leibniz_identity_lieBracket` is the Leibniz
  identity `[U, [V, W]] = [[U, V], W] + [V, [U, W]]`.

-/

@[expose] public section

open Set
open scoped Topology ContDiff

noncomputable section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ∞ω}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {V W V₁ W₁ : E → E} {s t : Set E} {x : E}

/-!
### The Lie bracket of vector fields in a vector space

We define the Lie bracket of two vector fields, and call it `lieBracket 𝕜 V W x`. We also define
a version localized to sets, `lieBracketWithin 𝕜 V W s x`. We copy the relevant API
of `fderivWithin` and `fderiv` for these notions to get a comprehensive API.
-/

namespace VectorField

variable (𝕜) in
/-- The Lie bracket `[V, W] (x)` of two vector fields at a point, defined as
`DW(x) (V x) - DV(x) (W x)`. -/
def lieBracket (V W : E → E) (x : E) : E :=
  fderiv 𝕜 W x id (V x) - fderiv 𝕜 V x id (W x)

variable (𝕜) in
/-- The Lie bracket `[V, W] (x)` of two vector fields within a set at a point, defined as
`DW(x) (V x) - DV(x) (W x)` where the derivatives are taken inside `s`. -/
def lieBracketWithin (V W : E → E) (s : Set E) (x : E) : E :=
  fderivWithin 𝕜 W s x id (V x) - fderivWithin 𝕜 V s x id (W x)

lemma lieBracket_eq :
    lieBracket 𝕜 V W = fun x ↦ fderiv 𝕜 W x id (V x) - fderiv 𝕜 V x id (W x) := rfl

lemma lieBracketWithin_eq :
    lieBracketWithin 𝕜 V W s =
      fun x ↦ fderivWithin 𝕜 W s x id (V x) - fderivWithin 𝕜 V s x id (W x) := rfl

@[simp]
theorem lieBracketWithin_univ : lieBracketWithin 𝕜 V W univ = lieBracket 𝕜 V W := by
  funext x
  simp only [lieBracketWithin, lieBracket, fderiv]

lemma lieBracketWithin_eq_zero_of_eq_zero (hV : V x = 0) (hW : W x = 0) :
    lieBracketWithin 𝕜 V W s x = 0 := by
  simp [lieBracketWithin, hV, hW]

lemma lieBracket_eq_zero_of_eq_zero (hV : V x = 0) (hW : W x = 0) :
    lieBracket 𝕜 V W x = 0 := by
  simp [lieBracket, hV, hW]

lemma lieBracketWithin_swap : lieBracketWithin 𝕜 V W s = - lieBracketWithin 𝕜 W V s := by
  ext x; simp [lieBracketWithin]

lemma lieBracket_swap : lieBracket 𝕜 V W x = - lieBracket 𝕜 W V x := by
  simp [lieBracket]

@[simp] lemma lieBracketWithin_self : lieBracketWithin 𝕜 V V s = 0 := by
  ext x; simp [lieBracketWithin]

@[simp] lemma lieBracket_self : lieBracket 𝕜 V V = 0 := by
  ext x; simp [lieBracket]

lemma lieBracketWithin_const_smul_left {c : 𝕜} (hV : DifferentiableWithinAt 𝕜 V s x)
    (hs : UniqueDiffWithinAt 𝕜 s x) :
    lieBracketWithin 𝕜 (c • V) W s x =
      c • lieBracketWithin 𝕜 V W s x := by
  simp [lieBracketWithin, smul_sub, fderivWithin_const_smul hs hV]

lemma lieBracket_const_smul_left {c : 𝕜} (hV : DifferentiableAt 𝕜 V x) :
    lieBracket 𝕜 (c • V) W x = c • lieBracket 𝕜 V W x := by
  simp only [← differentiableWithinAt_univ, ← lieBracketWithin_univ] at hV ⊢
  exact lieBracketWithin_const_smul_left hV uniqueDiffWithinAt_univ

lemma lieBracketWithin_const_smul_right {c : 𝕜} (hW : DifferentiableWithinAt 𝕜 W s x)
    (hs : UniqueDiffWithinAt 𝕜 s x) :
    lieBracketWithin 𝕜 V (c • W) s x =
      c • lieBracketWithin 𝕜 V W s x := by
  simp [lieBracketWithin, smul_sub, fderivWithin_const_smul hs hW]

lemma lieBracket_const_smul_right {c : 𝕜} (hW : DifferentiableAt 𝕜 W x) :
    lieBracket 𝕜 V (c • W) x = c • lieBracket 𝕜 V W x := by
  simp only [← differentiableWithinAt_univ, ← lieBracketWithin_univ] at hW ⊢
  exact lieBracketWithin_const_smul_right hW uniqueDiffWithinAt_univ

/--
Product rule for Lie Brackets: given two vector fields `V W : E → E` and a function `f : E → 𝕜`,
we have `[V, f • W] = (df V) • W + f • [V, W]`
-/
lemma lieBracketWithin_smul_right {f : E → 𝕜} (hf : DifferentiableWithinAt 𝕜 f s x)
    (hW : DifferentiableWithinAt 𝕜 W s x) (hs : UniqueDiffWithinAt 𝕜 s x) :
    lieBracketWithin 𝕜 V (fun y ↦ f y • W y) s x =
      (fderivWithin 𝕜 f s x) (V x) • (W x) + (f x) • lieBracketWithin 𝕜 V W s x := by
  simp [lieBracketWithin, fderivWithin_fun_smul hs hf hW, map_smul, add_comm, smul_sub,
    add_sub_assoc]

/--
Product rule for Lie Brackets: given two vector fields `V W : E → E` and a function `f : E → 𝕜`,
we have `[V, f • W] = (df V) • W + f • [V, W]`
-/
lemma lieBracket_smul_right {f : E → 𝕜} (hf : DifferentiableAt 𝕜 f x)
    (hW : DifferentiableAt 𝕜 W x) :
    lieBracket 𝕜 V (fun y ↦ f y • W y) x =
      (fderiv 𝕜 f x) (V x) • (W x) + (f x) • lieBracket 𝕜 V W x := by
  simp_rw [← differentiableWithinAt_univ, ← lieBracketWithin_univ, fderiv] at hW hf ⊢
  exact lieBracketWithin_smul_right hf hW uniqueDiffWithinAt_univ

/--
Product rule for Lie Brackets: given two vector fields `V W : E → E` and a function `f : E → 𝕜`,
we have `[f • V, W] = - (df W) • V + f • [V, W]`
-/
lemma lieBracketWithin_smul_left {f : E → 𝕜} (hf : DifferentiableWithinAt 𝕜 f s x)
    (hV : DifferentiableWithinAt 𝕜 V s x) (hs : UniqueDiffWithinAt 𝕜 s x) :
    lieBracketWithin 𝕜 (fun y ↦ f y • V y) W s x =
      - (fderivWithin 𝕜 f s x) (W x) • (V x) + (f x) • lieBracketWithin 𝕜 V W s x := by
  rw [lieBracketWithin_swap, Pi.neg_apply, lieBracketWithin_smul_right hf hV hs,
    lieBracketWithin_swap, add_comm]
  simp

/--
Product rule for Lie Brackets: given two vector fields `V W : E → E` and a function `f : E → 𝕜`,
we have `[f • V, W] = - (df W) • V + f • [V, W]`
-/
lemma lieBracket_smul_left {f : E → 𝕜} (hf : DifferentiableAt 𝕜 f x)
    (hV : DifferentiableAt 𝕜 V x) :
    lieBracket 𝕜 (fun y ↦ f y • V y) W x =
      - (fderiv 𝕜 f x) (W x) • (V x) + (f x) • lieBracket 𝕜 V W x := by
  rw [lieBracket_swap, lieBracket_smul_right hf hV, lieBracket_swap, add_comm]
  simp

lemma lieBracketWithin_add_left (hV : DifferentiableWithinAt 𝕜 V s x)
    (hV₁ : DifferentiableWithinAt 𝕜 V₁ s x) (hs : UniqueDiffWithinAt 𝕜 s x) :
    lieBracketWithin 𝕜 (V + V₁) W s x =
      lieBracketWithin 𝕜 V W s x + lieBracketWithin 𝕜 V₁ W s x := by
  simp only [lieBracketWithin, Pi.add_apply, map_add]
  rw [fderivWithin_add hs hV hV₁, add_apply]
  abel

lemma lieBracket_add_left (hV : DifferentiableAt 𝕜 V x) (hV₁ : DifferentiableAt 𝕜 V₁ x) :
    lieBracket 𝕜 (V + V₁) W x =
      lieBracket 𝕜 V W x + lieBracket 𝕜 V₁ W x := by
  simp only [lieBracket, Pi.add_apply, map_add]
  rw [fderiv_add hV hV₁, add_apply]
  abel

/-- We have `[0, W] = 0` for all vector fields `W`: this depends on the junk value 0
if `W` is not differentiable. Version within a set. -/
@[simp]
lemma lieBracketWithin_zero_left : lieBracketWithin 𝕜 0 W s = 0 := by
  ext x
  simp [lieBracketWithin, show (0 : E → E) = fun _ ↦ 0 from rfl, fderivWithin_const_apply]

/-- We have `[W, 0] = 0` for all vector fields `W`: this depends on the junk value 0
if `W` is not differentiable. Version within a set. -/
@[simp]
lemma lieBracketWithin_zero_right : lieBracketWithin 𝕜 W 0 s = 0 := by
  ext x
  simp [lieBracketWithin, show (0 : E → E) = fun _ ↦ 0 from rfl, fderivWithin_const_apply]

/-- We have `[0, W] = 0` for all vector fields `W`: this depends on the junk value 0
if `W` is not differentiable. -/
@[simp]
lemma lieBracket_zero_left : lieBracket 𝕜 0 W = 0 := by simp [← lieBracketWithin_univ]

/-- We have `[W, 0] = 0` for all vector fields `W`: this depends on the junk value 0
if `W` is not differentiable. -/
@[simp]
lemma lieBracket_zero_right : lieBracket 𝕜 W 0 = 0 := by simp [← lieBracketWithin_univ]

lemma lieBracketWithin_add_right (hW : DifferentiableWithinAt 𝕜 W s x)
    (hW₁ : DifferentiableWithinAt 𝕜 W₁ s x) (hs : UniqueDiffWithinAt 𝕜 s x) :
    lieBracketWithin 𝕜 V (W + W₁) s x =
      lieBracketWithin 𝕜 V W s x + lieBracketWithin 𝕜 V W₁ s x := by
  simp only [lieBracketWithin, Pi.add_apply, map_add]
  rw [fderivWithin_add hs hW hW₁, add_apply]
  abel

lemma lieBracket_add_right (hW : DifferentiableAt 𝕜 W x) (hW₁ : DifferentiableAt 𝕜 W₁ x) :
    lieBracket 𝕜 V (W + W₁) x =
      lieBracket 𝕜 V W x + lieBracket 𝕜 V W₁ x := by
  simp only [lieBracket, Pi.add_apply, map_add]
  rw [fderiv_add hW hW₁, add_apply]
  abel

/-- The differentiation operator along `[W, V]`
is the commutator of the differentiation operators along `W` and `V`. -/
lemma fderivWithin_apply_lieBracket_of_isSymmSndFDerivWithinAt {f : E → F}
    (hf : ContDiffWithinAt 𝕜 2 f s x) (hsymm : IsSymmSndFDerivWithinAt 𝕜 f s x)
    (hs : UniqueDiffOn 𝕜 s) (hxs : x ∈ s)
    (hW : DifferentiableWithinAt 𝕜 W s x) (hV : DifferentiableWithinAt 𝕜 V s x) :
    fderivWithin 𝕜 f s x id (lieBracketWithin 𝕜 V W s x) =
      fderivWithin 𝕜 (fun x ↦ fderivWithin 𝕜 f s x id (W x)) s x id (V x) -
        fderivWithin 𝕜 (fun x ↦ fderivWithin 𝕜 f s x id (V x)) s x id (W x) := by
  have H₀ : DifferentiableWithinAt 𝕜 (fderivWithin 𝕜 f s) s x :=
    (hf.fderivWithin_right hs (by decide) hxs).differentiableWithinAt one_ne_zero
  have H₁ : UniqueDiffWithinAt 𝕜 s x := hs x hxs
  rw [fderivWithin_clm_apply, fderivWithin_clm_apply] <;> try assumption
  simp [lieBracketWithin, hsymm (V _) (W _)]

/-- The differentiation operator along `[W, V]`
is the commutator of the differentiation operators along `W` and `V`. -/
lemma fderiv_apply_lieBracket_of_isSymmSndFDerivAt {f : E → F}
    (hf : ContDiffAt 𝕜 2 f x) (hsymm : IsSymmSndFDerivAt 𝕜 f x)
    (hW : DifferentiableAt 𝕜 W x) (hV : DifferentiableAt 𝕜 V x) :
    fderiv 𝕜 f x id (lieBracket 𝕜 V W x) =
      fderiv 𝕜 (fun x ↦ fderiv 𝕜 f x id (W x)) x id (V x) -
        fderiv 𝕜 (fun x ↦ fderiv 𝕜 f x id (V x)) x id (W x) := by
  simp only [fderiv, ← lieBracketWithin_univ, ← contDiffWithinAt_univ,
    ← isSymmSndFDerivWithinAt_univ, ← differentiableWithinAt_univ] at *
  exact fderivWithin_apply_lieBracket_of_isSymmSndFDerivWithinAt hf hsymm (by simp) (by simp)
    hW hV

/-- The differentiation operator along `[W, V]`
is the commutator of the differentiation operators along `W` and `V`. -/
lemma fderivWithin_apply_lieBracket {f : E → F} {n : ℕ∞ω}
    (hf : ContDiffWithinAt 𝕜 n f s x) (hn : minSmoothness 𝕜 2 ≤ n)
    (hs : UniqueDiffOn 𝕜 s) (hxs' : x ∈ closure (interior s)) (hxs : x ∈ s)
    (hW : DifferentiableWithinAt 𝕜 W s x) (hV : DifferentiableWithinAt 𝕜 V s x) :
    fderivWithin 𝕜 f s x id (lieBracketWithin 𝕜 V W s x) =
      fderivWithin 𝕜 (fun x ↦ fderivWithin 𝕜 f s x id (W x)) s x id (V x) -
        fderivWithin 𝕜 (fun x ↦ fderivWithin 𝕜 f s x id (V x)) s x id (W x) := by
  apply fderivWithin_apply_lieBracket_of_isSymmSndFDerivWithinAt <;> try assumption
  exacts [hf.of_le <| le_minSmoothness.trans hn, hf.isSymmSndFDerivWithinAt hn hs hxs' hxs]

/-- The differentiation operator along `[W, V]`
is the commutator of the differentiation operators along `W` and `V`. -/
lemma fderiv_apply_lieBracket {f : E → F} {n : ℕ∞ω}
    (hf : ContDiffAt 𝕜 n f x) (hn : minSmoothness 𝕜 2 ≤ n)
    (hW : DifferentiableAt 𝕜 W x) (hV : DifferentiableAt 𝕜 V x) :
    fderiv 𝕜 f x id (lieBracket 𝕜 V W x) =
      fderiv 𝕜 (fun x ↦ fderiv 𝕜 f x id (W x)) x id (V x) -
        fderiv 𝕜 (fun x ↦ fderiv 𝕜 f x id (V x)) x id (W x) := by
  apply fderiv_apply_lieBracket_of_isSymmSndFDerivAt <;> try assumption
  exacts [hf.of_le <| le_minSmoothness.trans hn, hf.isSymmSndFDerivAt hn]

lemma _root_.ContDiffWithinAt.lieBracketWithin_vectorField
    {m n : ℕ∞ω} (hV : ContDiffWithinAt 𝕜 n V s x)
    (hW : ContDiffWithinAt 𝕜 n W s x) (hs : UniqueDiffOn 𝕜 s) (hmn : m + 1 ≤ n) (hx : x ∈ s) :
    ContDiffWithinAt 𝕜 m (lieBracketWithin 𝕜 V W s) s x := by
  apply ContDiffWithinAt.sub
  · exact ContDiffWithinAt.clm_apply (hW.fderivWithin_right hs hmn hx)
      (hV.of_le (le_trans le_self_add hmn))
  · exact ContDiffWithinAt.clm_apply (hV.fderivWithin_right hs hmn hx)
      (hW.of_le (le_trans le_self_add hmn))

lemma _root_.ContDiffAt.lieBracket_vectorField {m n : ℕ∞ω} (hV : ContDiffAt 𝕜 n V x)
    (hW : ContDiffAt 𝕜 n W x) (hmn : m + 1 ≤ n) :
    ContDiffAt 𝕜 m (lieBracket 𝕜 V W) x := by
  rw [← contDiffWithinAt_univ] at hV hW ⊢
  simp_rw [← lieBracketWithin_univ]
  exact hV.lieBracketWithin_vectorField hW uniqueDiffOn_univ hmn (mem_univ _)

lemma _root_.ContDiffOn.lieBracketWithin_vectorField {m n : ℕ∞ω} (hV : ContDiffOn 𝕜 n V s)
    (hW : ContDiffOn 𝕜 n W s) (hs : UniqueDiffOn 𝕜 s) (hmn : m + 1 ≤ n) :
    ContDiffOn 𝕜 m (lieBracketWithin 𝕜 V W s) s :=
  fun x hx ↦ (hV x hx).lieBracketWithin_vectorField (hW x hx) hs hmn hx

lemma _root_.ContDiff.lieBracket_vectorField {m n : ℕ∞ω} (hV : ContDiff 𝕜 n V)
    (hW : ContDiff 𝕜 n W) (hmn : m + 1 ≤ n) :
    ContDiff 𝕜 m (lieBracket 𝕜 V W) :=
  contDiff_iff_contDiffAt.2 (fun _ ↦ hV.contDiffAt.lieBracket_vectorField hW.contDiffAt hmn)

theorem lieBracketWithin_of_mem_nhdsWithin (st : t ∈ 𝓝[s] x) (hs : UniqueDiffWithinAt 𝕜 s x)
    (hV : DifferentiableWithinAt 𝕜 V t x) (hW : DifferentiableWithinAt 𝕜 W t x) :
    lieBracketWithin 𝕜 V W s x = lieBracketWithin 𝕜 V W t x := by
  simp [lieBracketWithin, fderivWithin_of_mem_nhdsWithin st hs hV,
    fderivWithin_of_mem_nhdsWithin st hs hW]

theorem lieBracketWithin_subset (st : s ⊆ t) (ht : UniqueDiffWithinAt 𝕜 s x)
    (hV : DifferentiableWithinAt 𝕜 V t x) (hW : DifferentiableWithinAt 𝕜 W t x) :
    lieBracketWithin 𝕜 V W s x = lieBracketWithin 𝕜 V W t x :=
  lieBracketWithin_of_mem_nhdsWithin (nhdsWithin_mono _ st self_mem_nhdsWithin) ht hV hW

theorem lieBracketWithin_inter (ht : t ∈ 𝓝 x) :
    lieBracketWithin 𝕜 V W (s ∩ t) x = lieBracketWithin 𝕜 V W s x := by
  simp [lieBracketWithin, fderivWithin_inter, ht]

theorem lieBracketWithin_of_mem_nhds (h : s ∈ 𝓝 x) :
    lieBracketWithin 𝕜 V W s x = lieBracket 𝕜 V W x := by
  rw [← lieBracketWithin_univ, ← univ_inter s, lieBracketWithin_inter h]

theorem lieBracketWithin_of_isOpen (hs : IsOpen s) (hx : x ∈ s) :
    lieBracketWithin 𝕜 V W s x = lieBracket 𝕜 V W x :=
  lieBracketWithin_of_mem_nhds (hs.mem_nhds hx)

theorem lieBracketWithin_eq_lieBracket (hs : UniqueDiffWithinAt 𝕜 s x)
    (hV : DifferentiableAt 𝕜 V x) (hW : DifferentiableAt 𝕜 W x) :
    lieBracketWithin 𝕜 V W s x = lieBracket 𝕜 V W x := by
  simp [lieBracketWithin, lieBracket, fderivWithin_eq_fderiv, hs, hV, hW]

/-- Variant of `lieBracketWithin_congr_set` where one requires the sets to coincide only in
the complement of a point. -/
theorem lieBracketWithin_congr_set' (y : E) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    lieBracketWithin 𝕜 V W s x = lieBracketWithin 𝕜 V W t x := by
  simp [lieBracketWithin, fderivWithin_congr_set' _ h]

theorem lieBracketWithin_congr_set (h : s =ᶠ[𝓝 x] t) :
    lieBracketWithin 𝕜 V W s x = lieBracketWithin 𝕜 V W t x :=
  lieBracketWithin_congr_set' x <| h.filter_mono inf_le_left

/-- Variant of `lieBracketWithin_eventually_congr_set` where one requires the sets to coincide only
in the complement of a point. -/
theorem lieBracketWithin_eventually_congr_set' (y : E) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    lieBracketWithin 𝕜 V W s =ᶠ[𝓝 x] lieBracketWithin 𝕜 V W t :=
  (eventually_nhds_nhdsWithin.2 h).mono fun _ => lieBracketWithin_congr_set' y

theorem lieBracketWithin_eventually_congr_set (h : s =ᶠ[𝓝 x] t) :
    lieBracketWithin 𝕜 V W s =ᶠ[𝓝 x] lieBracketWithin 𝕜 V W t :=
  lieBracketWithin_eventually_congr_set' x <| h.filter_mono inf_le_left

theorem _root_.DifferentiableWithinAt.lieBracketWithin_congr_mono
    (hV : DifferentiableWithinAt 𝕜 V s x) (hVs : EqOn V₁ V t) (hVx : V₁ x = V x)
    (hW : DifferentiableWithinAt 𝕜 W s x) (hWs : EqOn W₁ W t) (hWx : W₁ x = W x)
    (hxt : UniqueDiffWithinAt 𝕜 t x) (h₁ : t ⊆ s) :
    lieBracketWithin 𝕜 V₁ W₁ t x = lieBracketWithin 𝕜 V W s x := by
  simp [lieBracketWithin, hV.fderivWithin_congr_mono, hW.fderivWithin_congr_mono, hVs, hVx,
    hWs, hWx, hxt, h₁]

theorem _root_.Filter.EventuallyEq.lieBracketWithin_vectorField_eq
    (hV : V₁ =ᶠ[𝓝[s] x] V) (hxV : V₁ x = V x) (hW : W₁ =ᶠ[𝓝[s] x] W) (hxW : W₁ x = W x) :
    lieBracketWithin 𝕜 V₁ W₁ s x = lieBracketWithin 𝕜 V W s x := by
  simp only [lieBracketWithin, hV.fderivWithin_eq hxV, hW.fderivWithin_eq hxW, hxV, hxW]

theorem _root_.Filter.EventuallyEq.lieBracketWithin_vectorField_eq_of_mem
    (hV : V₁ =ᶠ[𝓝[s] x] V) (hW : W₁ =ᶠ[𝓝[s] x] W) (hx : x ∈ s) :
    lieBracketWithin 𝕜 V₁ W₁ s x = lieBracketWithin 𝕜 V W s x :=
  hV.lieBracketWithin_vectorField_eq (mem_of_mem_nhdsWithin hx hV :)
    hW (mem_of_mem_nhdsWithin hx hW :)

/-- If vector fields coincide on a neighborhood of a point within a set, then the Lie brackets
also coincide on a neighborhood of this point within this set. Version where one considers the Lie
bracket within a subset. -/
theorem _root_.Filter.EventuallyEq.lieBracketWithin_vectorField'
    (hV : V₁ =ᶠ[𝓝[s] x] V) (hW : W₁ =ᶠ[𝓝[s] x] W) (ht : t ⊆ s) :
    lieBracketWithin 𝕜 V₁ W₁ t =ᶠ[𝓝[s] x] lieBracketWithin 𝕜 V W t := by
  filter_upwards [hV.fderivWithin' ht (𝕜 := 𝕜), hW.fderivWithin' ht (𝕜 := 𝕜), hV, hW]
    with x hV' hW' hV hW
  simp [lieBracketWithin, hV', hW', hV, hW]

protected theorem _root_.Filter.EventuallyEq.lieBracketWithin_vectorField
    (hV : V₁ =ᶠ[𝓝[s] x] V) (hW : W₁ =ᶠ[𝓝[s] x] W) :
    lieBracketWithin 𝕜 V₁ W₁ s =ᶠ[𝓝[s] x] lieBracketWithin 𝕜 V W s :=
  hV.lieBracketWithin_vectorField' hW Subset.rfl

protected theorem _root_.Filter.EventuallyEq.lieBracketWithin_vectorField_eq_of_insert
    (hV : V₁ =ᶠ[𝓝[insert x s] x] V) (hW : W₁ =ᶠ[𝓝[insert x s] x] W) :
    lieBracketWithin 𝕜 V₁ W₁ s x = lieBracketWithin 𝕜 V W s x := by
  apply mem_of_mem_nhdsWithin (mem_insert x s) (hV.lieBracketWithin_vectorField' hW
    (subset_insert x s))

theorem _root_.Filter.EventuallyEq.lieBracketWithin_vectorField_eq_nhds
    (hV : V₁ =ᶠ[𝓝 x] V) (hW : W₁ =ᶠ[𝓝 x] W) :
    lieBracketWithin 𝕜 V₁ W₁ s x = lieBracketWithin 𝕜 V W s x :=
  (hV.filter_mono nhdsWithin_le_nhds).lieBracketWithin_vectorField_eq hV.self_of_nhds
    (hW.filter_mono nhdsWithin_le_nhds) hW.self_of_nhds

theorem lieBracketWithin_congr
    (hV : EqOn V₁ V s) (hVx : V₁ x = V x) (hW : EqOn W₁ W s) (hWx : W₁ x = W x) :
    lieBracketWithin 𝕜 V₁ W₁ s x = lieBracketWithin 𝕜 V W s x :=
  (hV.eventuallyEq.filter_mono inf_le_right).lieBracketWithin_vectorField_eq hVx
    (hW.eventuallyEq.filter_mono inf_le_right) hWx

/-- Version of `lieBracketWithin_congr` in which one assumes that the point belongs to the
given set. -/
theorem lieBracketWithin_congr' (hV : EqOn V₁ V s) (hW : EqOn W₁ W s) (hx : x ∈ s) :
    lieBracketWithin 𝕜 V₁ W₁ s x = lieBracketWithin 𝕜 V W s x :=
  lieBracketWithin_congr hV (hV hx) hW (hW hx)

theorem _root_.Filter.EventuallyEq.lieBracket_vectorField_eq
    (hV : V₁ =ᶠ[𝓝 x] V) (hW : W₁ =ᶠ[𝓝 x] W) :
    lieBracket 𝕜 V₁ W₁ x = lieBracket 𝕜 V W x := by
  rw [← lieBracketWithin_univ, ← lieBracketWithin_univ, hV.lieBracketWithin_vectorField_eq_nhds hW]

protected theorem _root_.Filter.EventuallyEq.lieBracket_vectorField
    (hV : V₁ =ᶠ[𝓝 x] V) (hW : W₁ =ᶠ[𝓝 x] W) : lieBracket 𝕜 V₁ W₁ =ᶠ[𝓝 x] lieBracket 𝕜 V W := by
  filter_upwards [hV.eventuallyEq_nhds, hW.eventuallyEq_nhds] with y hVy hWy
  exact hVy.lieBracket_vectorField_eq hWy

/-- The Lie bracket of vector fields in vector spaces satisfies the Leibniz identity
`[U, [V, W]] = [[U, V], W] + [V, [U, W]]`. -/
lemma leibniz_identity_lieBracketWithin_of_isSymmSndFDerivWithinAt
    {U V W : E → E} {s : Set E} {x : E} (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s)
    (hU : ContDiffWithinAt 𝕜 2 U s x) (hV : ContDiffWithinAt 𝕜 2 V s x)
    (hW : ContDiffWithinAt 𝕜 2 W s x)
    (h'U : IsSymmSndFDerivWithinAt 𝕜 U s x) (h'V : IsSymmSndFDerivWithinAt 𝕜 V s x)
    (h'W : IsSymmSndFDerivWithinAt 𝕜 W s x) :
    lieBracketWithin 𝕜 U (lieBracketWithin 𝕜 V W s) s x =
      lieBracketWithin 𝕜 (lieBracketWithin 𝕜 U V s) W s x
      + lieBracketWithin 𝕜 V (lieBracketWithin 𝕜 U W s) s x := by
  simp only [lieBracketWithin_eq, map_sub]
  have aux₁ {U V : E → E} (hU : ContDiffWithinAt 𝕜 2 U s x) (hV : ContDiffWithinAt 𝕜 2 V s x) :
      DifferentiableWithinAt 𝕜 (fun x ↦ (fderivWithin 𝕜 V s x) (U x)) s x :=
    have := hV.fderivWithin_right_apply (hU.of_le one_le_two) hs le_rfl hx
    this.differentiableWithinAt one_ne_zero
  have aux₂ {U V : E → E} (hU : ContDiffWithinAt 𝕜 2 U s x) (hV : ContDiffWithinAt 𝕜 2 V s x) :
      fderivWithin 𝕜 (fun y ↦ (fderivWithin 𝕜 U s y) (V y)) s x =
        (fderivWithin 𝕜 U s x).comp (fderivWithin 𝕜 V s x) +
        (fderivWithin 𝕜 (fderivWithin 𝕜 U s) s x).flip (V x) := by
    refine fderivWithin_clm_apply (hs x hx) ?_ (hV.differentiableWithinAt two_ne_zero)
    exact (hU.fderivWithin_right hs le_rfl hx).differentiableWithinAt one_ne_zero
  rw [fderivWithin_fun_sub (hs x hx) (aux₁ hV hW) (aux₁ hW hV)]
  rw [fderivWithin_fun_sub (hs x hx) (aux₁ hU hV) (aux₁ hV hU)]
  rw [fderivWithin_fun_sub (hs x hx) (aux₁ hU hW) (aux₁ hW hU)]
  rw [aux₂ hW hV, aux₂ hV hW, aux₂ hV hU, aux₂ hU hV, aux₂ hW hU, aux₂ hU hW]
  simp only [FunLike.coe_sub, Pi.sub_apply, add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, h'V.eq, h'U.eq, h'W.eq]
  abel

/-- The Lie bracket of vector fields in vector spaces satisfies the Leibniz identity
`[U, [V, W]] = [[U, V], W] + [V, [U, W]]`. -/
lemma leibniz_identity_lieBracketWithin (hn : minSmoothness 𝕜 2 ≤ n)
    {U V W : E → E} {s : Set E} {x : E}
    (hs : UniqueDiffOn 𝕜 s) (h'x : x ∈ closure (interior s)) (hx : x ∈ s)
    (hU : ContDiffWithinAt 𝕜 n U s x) (hV : ContDiffWithinAt 𝕜 n V s x)
    (hW : ContDiffWithinAt 𝕜 n W s x) :
    lieBracketWithin 𝕜 U (lieBracketWithin 𝕜 V W s) s x =
      lieBracketWithin 𝕜 (lieBracketWithin 𝕜 U V s) W s x
      + lieBracketWithin 𝕜 V (lieBracketWithin 𝕜 U W s) s x := by
  apply leibniz_identity_lieBracketWithin_of_isSymmSndFDerivWithinAt hs hx
    (hU.of_le (le_minSmoothness.trans hn)) (hV.of_le (le_minSmoothness.trans hn))
    (hW.of_le (le_minSmoothness.trans hn))
  · exact hU.isSymmSndFDerivWithinAt hn hs h'x hx
  · exact hV.isSymmSndFDerivWithinAt hn hs h'x hx
  · exact hW.isSymmSndFDerivWithinAt hn hs h'x hx

/-- The Lie bracket of vector fields in vector spaces satisfies the Leibniz identity
`[U, [V, W]] = [[U, V], W] + [V, [U, W]]`. -/
lemma leibniz_identity_lieBracket (hn : minSmoothness 𝕜 2 ≤ n) {U V W : E → E} {x : E}
    (hU : ContDiffAt 𝕜 n U x) (hV : ContDiffAt 𝕜 n V x) (hW : ContDiffAt 𝕜 n W x) :
    lieBracket 𝕜 U (lieBracket 𝕜 V W) x =
      lieBracket 𝕜 (lieBracket 𝕜 U V) W x + lieBracket 𝕜 V (lieBracket 𝕜 U W) x := by
  simp only [← lieBracketWithin_univ, ← contDiffWithinAt_univ] at hU hV hW ⊢
  exact leibniz_identity_lieBracketWithin hn uniqueDiffOn_univ (by simp) (mem_univ _) hU hV hW


/-!
### The pullback of vector fields in a vector space
-/

/-- Pull back a vector by a supplied derivative when it has a unique preimage. This includes
injective derivatives whose range contains the vector. -/
def _root_.HasFDerivWithinAt.pullback {f : E → F} {A : E →L[𝕜] F}
    (_hA : HasFDerivWithinAt f A s x) (w : F) (hw : ∃! v, A v = w) : E := hw.exists.choose

variable (𝕜) in
/-- The pointwise pullback of a vector field, defined when the derivative within the set is
unique and the specified target vector has a unique preimage under it. -/
def pullbackWithin (f : E → F) (V : F → F) (s : Set E) (x : E)
    (hd : ∃! A : E →L[𝕜] F, HasFDerivWithinAt f A s x)
    (hv : ∃! v, fderivWithin 𝕜 f s x id v = V (f x)) : E :=
  hd.exists.choose_spec.differentiableWithinAt.hasFDerivWithinAt.pullback (V (f x)) hv

variable (𝕜) in
/-- The pointwise pullback of a vector field by a differentiable map at a point with a unique
lift of the target vector. -/
def pullback (f : E → F) (V : F → F) (x : E) (hd : DifferentiableAt 𝕜 f x)
    (hv : ∃! v, fderiv 𝕜 f x id v = V (f x)) : E :=
  hd.hasFDerivAt.hasFDerivWithinAt.pullback (s := univ) (V (f x)) hv

lemma _root_.DifferentiableWithinAt.existsUnique_fderivWithin {f : E → F}
    (hf : DifferentiableWithinAt 𝕜 f s x) (hs : UniqueDiffWithinAt 𝕜 s x) :
    ∃! A : E →L[𝕜] F, HasFDerivWithinAt f A s x :=
  ⟨_, hf.hasFDerivWithinAt, fun _ hA ↦ hs.eq hA hf.hasFDerivWithinAt⟩

lemma _root_.ContinuousLinearMap.IsInvertible.existsUnique_preimage
    {R X Y : Type*} [Semiring R] [TopologicalSpace X] [TopologicalSpace Y]
    [AddCommMonoid X] [Module R X] [AddCommMonoid Y] [Module R Y] {A : X →L[R] Y}
    (hA : A.IsInvertible) (w : Y) : ∃! v, A v = w := by
  obtain ⟨M, rfl⟩ := hA
  exact M.bijective.existsUnique w

lemma pullbackWithin_eq {f : E → F} {V : F → F} {hd hv} {v : E} :
    pullbackWithin 𝕜 f V s x hd hv = v ↔ fderivWithin 𝕜 f s x id v = V (f x) :=
  ⟨fun h ↦ h ▸ hv.exists.choose_spec, fun h ↦ hv.unique hv.exists.choose_spec h⟩

lemma pullback_eq_of_fderiv_eq {f : E → F} {M : E ≃L[𝕜] F} (hf : HasFDerivAt f M x)
    (V : F → F) {hv} : pullback 𝕜 f V x hf.differentiableAt hv = M.symm (V (f x)) := by
  apply hv.unique hv.exists.choose_spec
  simp [hf.fderiv]

lemma pullbackWithin_eq_of_fderivWithin_eq {f : E → F} {M : E ≃L[𝕜] F}
    (hf : HasFDerivWithinAt f (M : E →L[𝕜] F) s x) (V : F → F) {hd hv} :
    pullbackWithin 𝕜 f V s x hd hv = M.symm (V (f x)) := by
  apply pullbackWithin_eq.mpr
  have h := hd.unique hd.exists.choose_spec.differentiableWithinAt.hasFDerivWithinAt hf
  change fderivWithin 𝕜 f s x id = (M : E →L[𝕜] F) at h
  simp [h]

lemma fderiv_pullback (f : E → F) (V : F → F) (x : E) {hd hv} :
    fderiv 𝕜 f x id (pullback 𝕜 f V x hd hv) = V (f x) := hv.exists.choose_spec

lemma fderivWithin_pullbackWithin (f : E → F) (V : F → F) (s : Set E) (x : E) {hd hv} :
    fderivWithin 𝕜 f s x id (pullbackWithin 𝕜 f V s x hd hv) = V (f x) := hv.exists.choose_spec

@[simp] lemma pullbackWithin_univ {f : E → F} {V : F → F} {hd hv}
    {hf : DifferentiableAt 𝕜 f x} :
    pullbackWithin 𝕜 f V univ x hd hv =
      pullback 𝕜 f V x hf (by simpa only [fderiv] using hv) := by
  apply pullbackWithin_eq.mpr
  simpa only [fderiv] using
    (fderiv_pullback f V x (hd := hf) (hv := by simpa only [fderiv] using hv))

/-- The vector `U x` is related to `V (f x)` by a derivative of `f` within `s`.
On a set of unique differentiability the relation is independent of the representative. -/
def IsRelatedWithinAt (f : E → F) (U : E → E) (V : F → F) (s : Set E) (x : E) :=
  ∃ A : E →L[𝕜] F, HasFDerivWithinAt f A s x ∧ A (U x) = V (f x)

lemma IsRelatedWithinAt.fderivWithin_apply {f : E → F} {U : E → E} {V : F → F}
    (h : IsRelatedWithinAt (𝕜 := 𝕜) f U V s x) (hs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 f s x id (U x) = V (f x) := by
  rcases h with ⟨A, hA, h⟩
  rwa [hA.fderivWithin hs]

open scoped Topology Filter

variable [CompleteSpace E]

/-- If a `C^2` map has an invertible derivative within a set at a point, then nearby derivatives
can be written as continuous linear equivs, which depend in a `C^1` way on the point, as well as
their inverse, and moreover one can compute the derivative of the inverse. -/
lemma _root_.exists_continuousLinearEquiv_fderivWithin_symm_eq
    {f : E → F} {s : Set E} {x : E} (h'f : ContDiffWithinAt 𝕜 2 f s x)
    (hf : (fderivWithin 𝕜 f s x).IsInvertible) (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) :
    ∃ N : E → (E ≃L[𝕜] F), ContDiffWithinAt 𝕜 1 (fun y ↦ (N y : E →L[𝕜] F)) s x
    ∧ ContDiffWithinAt 𝕜 1 (fun y ↦ ((N y).symm : F →L[𝕜] E)) s x
    ∧ (∀ᶠ y in 𝓝[s] x, (N y : E →L[𝕜] F) = fderivWithin 𝕜 f s y)
    ∧ ∀ v, fderivWithin 𝕜 (fun y ↦ ((N y).symm : F →L[𝕜] E)) s x id v
      = - (N x).symm ∘L ((fderivWithin 𝕜 (fderivWithin 𝕜 f s) s x id v)) ∘L (N x).symm := by
  classical
  rcases hf with ⟨M, hM⟩
  let U := {y | ∃ (N : E ≃L[𝕜] F), (N : E →L[𝕜] F) = fderivWithin 𝕜 f s y}
  have hU : U ∈ 𝓝[s] x := by
    have I : range ((↑) : (E ≃L[𝕜] F) → E →L[𝕜] F) ∈ 𝓝 (fderivWithin 𝕜 f s x) := by
      rw [← hM]
      exact M.nhds
    have : ContinuousWithinAt (fderivWithin 𝕜 f s) s x :=
      (h'f.fderivWithin_right (m := 1) hs le_rfl hx).continuousWithinAt
    exact this I
  let N : E → (E ≃L[𝕜] F) := fun x ↦ if h : x ∈ U then h.choose else M
  have eN : (fun y ↦ (N y : E →L[𝕜] F)) =ᶠ[𝓝[s] x] fun y ↦ fderivWithin 𝕜 f s y := by
    filter_upwards [hU] with y hy
    simpa only [hy, ↓reduceDIte, N] using Exists.choose_spec hy
  have e'N : (N x : E →L[𝕜] F) = fderivWithin 𝕜 f s x := by apply mem_of_mem_nhdsWithin hx eN
  have hN : ContDiffWithinAt 𝕜 1 (fun y ↦ (N y : E →L[𝕜] F)) s x := by
    have : ContDiffWithinAt 𝕜 1 (fun y ↦ fderivWithin 𝕜 f s y) s x :=
      h'f.fderivWithin_right (m := 1) hs le_rfl hx
    apply this.congr_of_eventuallyEq eN e'N
  have hN' : ContDiffWithinAt 𝕜 1 (fun y ↦ ((N y).symm : F →L[𝕜] E)) s x := by
    let g := Function.extend (fun e : E ≃L[𝕜] F ↦ (e : E →L[𝕜] F))
      (fun e ↦ (e.symm : F →L[𝕜] E)) (fun _ ↦ ((N x).symm : F →L[𝕜] E))
    have hg (e : E ≃L[𝕜] F) : g e = (e.symm : F →L[𝕜] E) :=
      (show Function.Injective (fun u : E ≃L[𝕜] F ↦ (u : E →L[𝕜] F)) from
        fun _ _ h ↦ ContinuousLinearEquiv.coe_inj.mp h).extend_apply _ _ _
    have hcomp := (contDiffAt_map_inverse (N x) hg (n := 1)).comp_contDiffWithinAt x hN
    simpa only [Function.comp_def, hg] using hcomp
  refine ⟨N, hN, hN', eN, fun v ↦ ?_⟩
  have A' y : ContinuousLinearMap.compL 𝕜 F E F (N y : E →L[𝕜] F) ((N y).symm : F →L[𝕜] E)
      = ContinuousLinearMap.id 𝕜 F := by ext; simp
  have : fderivWithin 𝕜 (fun y ↦ ContinuousLinearMap.compL 𝕜 F E F (N y : E →L[𝕜] F)
      ((N y).symm : F →L[𝕜] E)) s x id v = 0 := by
    simp [A', fderivWithin_const_apply]
  have I : (N x : E →L[𝕜] F) ∘L (fderivWithin 𝕜 (fun y ↦ ((N y).symm : F →L[𝕜] E)) s x id v) =
      - (fderivWithin 𝕜 (fun y ↦ (N y : E →L[𝕜] F)) s x id v) ∘L ((N x).symm : F →L[𝕜] E) := by
    rw [ContinuousLinearMap.fderivWithin_of_bilinear _ (hN.differentiableWithinAt one_ne_zero)
      (hN'.differentiableWithinAt one_ne_zero) (hs x hx)] at this
    simpa [eq_neg_iff_add_eq_zero] using this
  have B (M : F →L[𝕜] E) : M = ((N x).symm : F →L[𝕜] E) ∘L ((N x) ∘L M) := by
    ext; simp
  rw [B (fderivWithin 𝕜 (fun y ↦ ((N y).symm : F →L[𝕜] E)) s x id v), I]
  simp only [ContinuousLinearMap.comp_neg, eN.fderivWithin_eq e'N]

lemma DifferentiableWithinAt.pullbackWithin {f : E → F} {V : F → F} {U : E → E} {t : Set F}
    (hV : DifferentiableWithinAt 𝕜 V t (f x))
    (hf : ContDiffWithinAt 𝕜 2 f s x) (hf' : (fderivWithin 𝕜 f s x).IsInvertible)
    (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) (hst : MapsTo f s t)
    (hU : ∀ᶠ y in 𝓝[s] x, IsRelatedWithinAt (𝕜 := 𝕜) f U V s y) :
    DifferentiableWithinAt 𝕜 U s x := by
  obtain ⟨M, -, hMdiff, hM, -⟩ := exists_continuousLinearEquiv_fderivWithin_symm_eq hf hf' hs hx
  have hreg : DifferentiableWithinAt 𝕜 (fun y ↦ ((M y).symm : F →L[𝕜] E) (V (f y))) s x :=
    (hMdiff.differentiableWithinAt one_ne_zero).clm_apply
      (hV.comp _ (hf.differentiableWithinAt two_ne_zero) hst)
  apply hreg.congr_of_eventuallyEq_of_mem _ hx
  filter_upwards [hU, hM, self_mem_nhdsWithin] with y hy hMy hys
  apply (M y).eq_symm_apply.mpr
  change (M y : E →L[𝕜] F) (U y) = _
  rw [hMy]
  exact hy.fderivWithin_apply (hs y hys)

/-- If a `C^2` map has an invertible derivative at a point, then nearby derivatives can be written
as continuous linear equivs, which depend in a `C^1` way on the point, as well as their inverse, and
moreover one can compute the derivative of the inverse. -/
lemma _root_.exists_continuousLinearEquiv_fderiv_symm_eq
    {f : E → F} {x : E} (h'f : ContDiffAt 𝕜 2 f x) (hf : (fderiv 𝕜 f x).IsInvertible) :
    ∃ N : E → (E ≃L[𝕜] F), ContDiffAt 𝕜 1 (fun y ↦ (N y : E →L[𝕜] F)) x
    ∧ ContDiffAt 𝕜 1 (fun y ↦ ((N y).symm : F →L[𝕜] E)) x
    ∧ (∀ᶠ y in 𝓝 x, (N y : E →L[𝕜] F) = fderiv 𝕜 f y)
    ∧ ∀ v, fderiv 𝕜 (fun y ↦ ((N y).symm : F →L[𝕜] E)) x id v
      = - (N x).symm ∘L ((fderiv 𝕜 (fderiv 𝕜 f) x id v)) ∘L (N x).symm := by
  simp only [fderiv, ← contDiffWithinAt_univ, ← nhdsWithin_univ] at hf h'f ⊢
  exact exists_continuousLinearEquiv_fderivWithin_symm_eq h'f hf uniqueDiffOn_univ (mem_univ _)

/-- An invertible derivative has a germ of related lifts for every target field. -/
lemma exists_eventually_isRelatedWithinAt {f : E → F} (V : F → F)
    (hf : ContDiffWithinAt 𝕜 2 f s x) (h : (fderivWithin 𝕜 f s x).IsInvertible)
    (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) :
    ∃ U : E → E, ∀ᶠ y in 𝓝[s] x, IsRelatedWithinAt (𝕜 := 𝕜) f U V s y := by
  obtain ⟨M, -, -, hM, -⟩ := exists_continuousLinearEquiv_fderivWithin_symm_eq hf h hs hx
  refine ⟨fun y ↦ (M y).symm (V (f y)), ?_⟩
  have hreg := hf.eventually (by simp)
  rw [insert_eq_of_mem hx] at hreg
  filter_upwards [hM, hreg] with y hy hfy
  exact ⟨_, (hfy.differentiableWithinAt two_ne_zero).hasFDerivWithinAt, by rw [← hy]; simp⟩

omit [CompleteSpace E] in
/-- The Lie bracket of related fields is related to the target bracket. Only the two local
relations and differentiability of the related fields are needed. -/
lemma IsRelatedWithinAt.lieBracketWithin {f : E → F} {U Z : E → E} {V W : F → F} {t : Set F}
    (hf : IsSymmSndFDerivWithinAt 𝕜 f s x) (h'f : ContDiffWithinAt 𝕜 2 f s x)
    (hV : DifferentiableWithinAt 𝕜 V t (f x)) (hW : DifferentiableWithinAt 𝕜 W t (f x))
    (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) (hst : MapsTo f s t)
    (hU : DifferentiableWithinAt 𝕜 U s x) (hZ : DifferentiableWithinAt 𝕜 Z s x)
    (hUV : ∀ᶠ y in 𝓝[s] x, IsRelatedWithinAt (𝕜 := 𝕜) f U V s y)
    (hZW : ∀ᶠ y in 𝓝[s] x, IsRelatedWithinAt (𝕜 := 𝕜) f Z W s y) :
    IsRelatedWithinAt (𝕜 := 𝕜) f (lieBracketWithin 𝕜 U Z s) (lieBracketWithin 𝕜 V W t) s x := by
  have hr {P : E → E} {Q : F → F}
      (hr : ∀ᶠ y in 𝓝[s] x, IsRelatedWithinAt (𝕜 := 𝕜) f P Q s y) :
      (fun y ↦ fderivWithin 𝕜 f s y id (P y)) =ᶠ[𝓝[s] x] fun y ↦ Q (f y) := by
    filter_upwards [hr, self_mem_nhdsWithin] with y hy hys using hy.fderivWithin_apply (hs y hys)
  have hd := h'f.differentiableWithinAt two_ne_zero
  refine ⟨_, hd.hasFDerivWithinAt, ?_⟩
  rw [fderivWithin_apply_lieBracket_of_isSymmSndFDerivWithinAt h'f hf hs hx hZ hU,
    (hr hZW).fderivWithin_eq_of_mem hx, (hr hUV).fderivWithin_eq_of_mem hx]
  have hcomp {Q : F → F} (hQ : DifferentiableWithinAt 𝕜 Q t (f x)) :
      fderivWithin 𝕜 (fun y ↦ Q (f y)) s x id =
        (fderivWithin 𝕜 Q t (f x) id).comp (fderivWithin 𝕜 f s x id) :=
    (hQ.hasFDerivWithinAt.comp (coord := id) (coord' := id) x
      hd.hasFDerivWithinAt hst).fderivWithin (hs x hx)
  rw [hcomp hW, hcomp hV]
  have hxU := (mem_of_mem_nhdsWithin hx hUV).fderivWithin_apply (hs x hx)
  have hxZ := (mem_of_mem_nhdsWithin hx hZW).fderivWithin_apply (hs x hx)
  simp only [ContinuousLinearMap.comp_apply, VectorField.lieBracketWithin, hxU, hxZ]

/-- On an invertible derivative germ the bracket of the pullbacks is the pullback of the bracket.
The two source fields represent the pointwise pullbacks locally. -/
lemma pullbackWithin_lieBracketWithin_of_isSymmSndFDerivWithinAt
    {f : E → F} {U Z : E → E} {V W : F → F} {t : Set F}
    (hf : IsSymmSndFDerivWithinAt 𝕜 f s x) (h'f : ContDiffWithinAt 𝕜 2 f s x)
    (hV : DifferentiableWithinAt 𝕜 V t (f x)) (hW : DifferentiableWithinAt 𝕜 W t (f x))
    (hu : UniqueDiffOn 𝕜 s) (hx : x ∈ s) (hst : MapsTo f s t)
    (h : (fderivWithin 𝕜 f s x).IsInvertible)
    (hUV : ∀ᶠ y in 𝓝[s] x, IsRelatedWithinAt (𝕜 := 𝕜) f U V s y)
    (hZW : ∀ᶠ y in 𝓝[s] x, IsRelatedWithinAt (𝕜 := 𝕜) f Z W s y) :
    pullbackWithin 𝕜 f (lieBracketWithin 𝕜 V W t) s x
      ((h'f.differentiableWithinAt two_ne_zero).existsUnique_fderivWithin (hu x hx))
      (h.existsUnique_preimage _) = lieBracketWithin 𝕜 U Z s x := by
  apply pullbackWithin_eq.mpr
  exact (IsRelatedWithinAt.lieBracketWithin hf h'f hV hW hu hx hst
    (DifferentiableWithinAt.pullbackWithin hV h'f h hu hx hst hUV)
    (DifferentiableWithinAt.pullbackWithin hW h'f h hu hx hst hZW) hUV hZW).fderivWithin_apply
      (hu x hx)

/-- The Lie bracket commutes with taking pullbacks. This requires the function to have symmetric
second derivative. Version in a complete space. One could also give a version avoiding
completeness but requiring that `f` is a local diffeomorphism. Variant where unique
differentiability and the invariance property are only required in a smaller set `u`. -/
lemma pullbackWithin_lieBracketWithin_of_isSymmSndFDerivWithinAt_of_eventuallyEqSet
    {f : E → F} {U Z : E → E} {V W : F → F} {t : Set F} {u : Set E}
    (hf : IsSymmSndFDerivWithinAt 𝕜 f s x) (h'f : ContDiffWithinAt 𝕜 2 f s x)
    (hV : DifferentiableWithinAt 𝕜 V t (f x)) (hW : DifferentiableWithinAt 𝕜 W t (f x))
    (hu : UniqueDiffOn 𝕜 u) (hx : x ∈ u) (hst : MapsTo f u t) (hus : u =ᶠ[𝓝 x] s)
    (h : (fderivWithin 𝕜 f s x).IsInvertible)
    (hUV : ∀ᶠ y in 𝓝[u] x, IsRelatedWithinAt (𝕜 := 𝕜) f U V u y)
    (hZW : ∀ᶠ y in 𝓝[u] x, IsRelatedWithinAt (𝕜 := 𝕜) f Z W u y) :
    pullbackWithin 𝕜 f (lieBracketWithin 𝕜 V W t) s x
      ((h'f.differentiableWithinAt two_ne_zero).existsUnique_fderivWithin
        ((uniqueDiffWithinAt_congr (nhdsWithin_eq_iff_eventuallyEqSet.mpr hus)).mp (hu x hx)))
      (h.existsUnique_preimage _) = lieBracketWithin 𝕜 U Z s x := by
  apply pullbackWithin_eq.mpr
  have heq := fderivWithin_congr_set (𝕜 := 𝕜) (f := f) hus
  rw [← heq, ← lieBracketWithin_congr_set hus]
  exact pullbackWithin_eq.mp (pullbackWithin_lieBracketWithin_of_isSymmSndFDerivWithinAt
    (hf.congr_set hus.symm) (h'f.congr_set hus.symm) hV hW hu hx hst (heq ▸ h) hUV hZW)

@[deprecated (since := "2026-08-14")]
alias pullbackWithin_lieBracketWithin_of_isSymmSndFDerivWithinAt_of_eventuallyEq :=
  pullbackWithin_lieBracketWithin_of_isSymmSndFDerivWithinAt_of_eventuallyEqSet

/-- The Lie bracket commutes with taking pullbacks. This requires the function to have symmetric
second derivative. Version in a complete space. One could also give a version avoiding
completeness but requiring that `f` is a local diffeomorphism. -/
lemma pullback_lieBracket_of_isSymmSndFDerivAt {f : E → F} {U Z : E → E} {V W : F → F}
    (hf : IsSymmSndFDerivAt 𝕜 f x) (h'f : ContDiffAt 𝕜 2 f x)
    (hV : DifferentiableAt 𝕜 V (f x)) (hW : DifferentiableAt 𝕜 W (f x))
    (h : (fderiv 𝕜 f x).IsInvertible)
    (hUV : ∀ᶠ y in 𝓝 x, IsRelatedWithinAt (𝕜 := 𝕜) f U V univ y)
    (hZW : ∀ᶠ y in 𝓝 x, IsRelatedWithinAt (𝕜 := 𝕜) f Z W univ y) :
    pullback 𝕜 f (lieBracket 𝕜 V W) x (h'f.differentiableAt two_ne_zero)
      (h.existsUnique_preimage _) = lieBracket 𝕜 U Z x := by
  apply (h.existsUnique_preimage _).unique (fderiv_pullback ..)
  have h' := pullbackWithin_lieBracketWithin_of_isSymmSndFDerivWithinAt
    (isSymmSndFDerivWithinAt_univ.mpr hf) h'f.contDiffWithinAt hV.differentiableWithinAt
    hW.differentiableWithinAt uniqueDiffOn_univ (mem_univ x) (mapsTo_univ f univ)
    (by simpa only [fderiv] using h) (by simpa using hUV) (by simpa using hZW)
  simpa only [lieBracketWithin_univ, fderiv] using pullbackWithin_eq.mp h'

/-- The Lie bracket commutes with taking pullbacks. This requires the function to have symmetric
second derivative. Version in a complete space. One could also give a version avoiding
completeness but requiring that `f` is a local diffeomorphism. -/
lemma pullbackWithin_lieBracketWithin
    {f : E → F} {U Z : E → E} {V W : F → F} {t : Set F} (hn : minSmoothness 𝕜 2 ≤ n)
    (h'f : ContDiffWithinAt 𝕜 n f s x)
    (hV : DifferentiableWithinAt 𝕜 V t (f x)) (hW : DifferentiableWithinAt 𝕜 W t (f x))
    (hu : UniqueDiffOn 𝕜 s) (hx : x ∈ s) (h'x : x ∈ closure (interior s)) (hst : MapsTo f s t)
    (h : (fderivWithin 𝕜 f s x).IsInvertible)
    (hUV : ∀ᶠ y in 𝓝[s] x, IsRelatedWithinAt (𝕜 := 𝕜) f U V s y)
    (hZW : ∀ᶠ y in 𝓝[s] x, IsRelatedWithinAt (𝕜 := 𝕜) f Z W s y) :
    pullbackWithin 𝕜 f (lieBracketWithin 𝕜 V W t) s x
      (((h'f.of_le (le_minSmoothness.trans hn)).differentiableWithinAt
        two_ne_zero).existsUnique_fderivWithin
        (hu x hx)) (h.existsUnique_preimage _) = lieBracketWithin 𝕜 U Z s x :=
  pullbackWithin_lieBracketWithin_of_isSymmSndFDerivWithinAt
    (h'f.isSymmSndFDerivWithinAt hn hu h'x hx) (h'f.of_le (le_minSmoothness.trans hn))
    hV hW hu hx hst h hUV hZW

/-- The Lie bracket commutes with taking pullbacks. One could also give a version avoiding
completeness but requiring that `f` is a local diffeomorphism. -/
lemma pullback_lieBracket (hn : minSmoothness 𝕜 2 ≤ n)
    {f : E → F} {U Z : E → E} {V W : F → F} (h'f : ContDiffAt 𝕜 n f x)
    (hV : DifferentiableAt 𝕜 V (f x)) (hW : DifferentiableAt 𝕜 W (f x))
    (h : (fderiv 𝕜 f x).IsInvertible)
    (hUV : ∀ᶠ y in 𝓝 x, IsRelatedWithinAt (𝕜 := 𝕜) f U V univ y)
    (hZW : ∀ᶠ y in 𝓝 x, IsRelatedWithinAt (𝕜 := 𝕜) f Z W univ y) :
    pullback 𝕜 f (lieBracket 𝕜 V W) x
      ((h'f.of_le (le_minSmoothness.trans hn)).differentiableAt two_ne_zero)
      (h.existsUnique_preimage _) = lieBracket 𝕜 U Z x :=
  pullback_lieBracket_of_isSymmSndFDerivAt (h'f.isSymmSndFDerivAt hn)
    (h'f.of_le (le_minSmoothness.trans hn)) hV hW h hUV hZW

end VectorField
