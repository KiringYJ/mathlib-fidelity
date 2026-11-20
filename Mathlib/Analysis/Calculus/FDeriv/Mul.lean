/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.FDeriv.Bilinear

/-!
# Multiplicative operations on derivatives

For detailed documentation of the Fréchet derivative,
see the module docstring of `Mathlib/Analysis/Calculus/FDeriv/Basic.lean`.

This file contains the usual formulas (and existence assertions) for the derivative of

* multiplication of a function by a scalar function
* product of finitely many scalar functions
* multiplicative inversion on units and inverse compositions on their exact unit domains
-/

public section

open Asymptotics ContinuousLinearMap

open scoped Topology

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {f : E → F}
variable {f' : E →L[𝕜] F}
variable {x : E}
variable {s : Set E}

section SMul

/-! ### Derivative of the product of a scalar-valued function and a vector-valued function

If `c` is a differentiable scalar-valued function and `f` is a differentiable vector-valued
function, then `fun x ↦ c x • f x` is differentiable as well. Lemmas in this section work for
functions `c` taking values in the base field, as well as in a normed algebra over the base
field: e.g., they work for `c : E → ℂ` and `f : E → F` provided that `F` is a complex
normed vector space.
-/


variable {𝕜' : Type*} [NormedRing 𝕜'] [NormedAlgebra 𝕜 𝕜'] [Module 𝕜' F] [IsBoundedSMul 𝕜' F]
  [IsScalarTower 𝕜 𝕜' F]

variable {c : E → 𝕜'} {c' : E →L[𝕜] 𝕜'}

@[to_fun (attr := fun_prop)]
theorem HasStrictFDerivAt.smul (hc : HasStrictFDerivAt c c' x) (hf : HasStrictFDerivAt f f' x) :
    HasStrictFDerivAt (c • f) (c x • f' + c'.smulRight (f x)) x :=
  (isBoundedBilinearMap_smul.hasStrictFDerivAt (c x, f x)).comp
    (coord' := @id (𝕜' × F)) x (hc.prodMk hf)

@[to_fun (attr := fun_prop)]
theorem HasFDerivWithinAt.smul
    (hc : HasFDerivWithinAt c c' s x) (hf : HasFDerivWithinAt f f' s x) :
    HasFDerivWithinAt (c • f) (c x • f' + c'.smulRight (f x)) s x := by
  -- `by exact` to solve unification issues.
  exact (isBoundedBilinearMap_smul.hasFDerivAt (𝕜 := 𝕜) (c x, f x)).comp_hasFDerivWithinAt
    (coord' := @id (𝕜' × F)) (s := s) x (hc.prodMk hf)

@[to_fun (attr := fun_prop)]
theorem HasFDerivAt.smul (hc : HasFDerivAt c c' x) (hf : HasFDerivAt f f' x) :
    HasFDerivAt (c • f) (c x • f' + c'.smulRight (f x)) x := by
  -- `by exact` to solve unification issues.
  exact (isBoundedBilinearMap_smul.hasFDerivAt (𝕜 := 𝕜) (c x, f x)).comp
    (coord' := @id (𝕜' × F)) x (hc.prodMk hf)

@[to_fun (attr := fun_prop)]
theorem DifferentiableWithinAt.smul (hc : DifferentiableWithinAt 𝕜 c s x)
    (hf : DifferentiableWithinAt 𝕜 f s x) : DifferentiableWithinAt 𝕜 (c • f) s x :=
  (hc.hasFDerivWithinAt.smul hf.hasFDerivWithinAt).differentiableWithinAt

@[to_fun (attr := simp, fun_prop)]
theorem DifferentiableAt.smul (hc : DifferentiableAt 𝕜 c x) (hf : DifferentiableAt 𝕜 f x) :
    DifferentiableAt 𝕜 (c • f) x :=
  (hc.hasFDerivAt.smul hf.hasFDerivAt).differentiableAt

@[to_fun (attr := fun_prop)]
theorem DifferentiableOn.smul (hc : DifferentiableOn 𝕜 c s) (hf : DifferentiableOn 𝕜 f s) :
    DifferentiableOn 𝕜 (c • f) s := fun x hx => (hc x hx).smul (hf x hx)

@[to_fun (attr := simp, fun_prop)]
theorem Differentiable.smul (hc : Differentiable 𝕜 c) (hf : Differentiable 𝕜 f) :
    Differentiable 𝕜 (c • f) := fun x => (hc x).smul (hf x)

theorem fderivWithin_fun_smul (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : DifferentiableWithinAt 𝕜 c s x)
    (hf : DifferentiableWithinAt 𝕜 f s x) :
    fderivWithin 𝕜 (fun y => c y • f y) s x =
      c x • fderivWithin 𝕜 f s x + (fderivWithin 𝕜 c s x).smulRight (f x) :=
  (hc.hasFDerivWithinAt.smul hf.hasFDerivWithinAt).fderivWithin hxs

theorem fderivWithin_smul (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : DifferentiableWithinAt 𝕜 c s x)
    (hf : DifferentiableWithinAt 𝕜 f s x) :
    fderivWithin 𝕜 (c • f) s x =
      c x • fderivWithin 𝕜 f s x + (fderivWithin 𝕜 c s x).smulRight (f x) :=
  (hc.hasFDerivWithinAt.smul hf.hasFDerivWithinAt).fderivWithin hxs

theorem fderiv_fun_smul (hc : DifferentiableAt 𝕜 c x) (hf : DifferentiableAt 𝕜 f x) :
    fderiv 𝕜 (fun y => c y • f y) x = c x • fderiv 𝕜 f x + (fderiv 𝕜 c x).smulRight (f x) :=
  (hc.hasFDerivAt.smul hf.hasFDerivAt).fderiv

theorem fderiv_smul (hc : DifferentiableAt 𝕜 c x) (hf : DifferentiableAt 𝕜 f x) :
    fderiv 𝕜 (c • f) x = c x • fderiv 𝕜 f x + (fderiv 𝕜 c x).smulRight (f x) :=
  (hc.hasFDerivAt.smul hf.hasFDerivAt).fderiv

@[fun_prop]
theorem HasStrictFDerivAt.smul_const (hc : HasStrictFDerivAt c c' x) (f : F) :
    HasStrictFDerivAt (fun y => c y • f) (c'.smulRight f) x := by
  simpa only [smul_zero, zero_add] using! hc.smul (hasStrictFDerivAt_const f x)

@[fun_prop]
theorem HasFDerivWithinAt.smul_const (hc : HasFDerivWithinAt c c' s x) (f : F) :
    HasFDerivWithinAt (fun y => c y • f) (c'.smulRight f) s x := by
  simpa only [smul_zero, zero_add] using! hc.smul (hasFDerivWithinAt_const f x s)

@[fun_prop]
theorem HasFDerivAt.smul_const (hc : HasFDerivAt c c' x) (f : F) :
    HasFDerivAt (fun y => c y • f) (c'.smulRight f) x := by
  simpa only [smul_zero, zero_add] using! hc.smul (hasFDerivAt_const f x)

@[fun_prop]
theorem DifferentiableWithinAt.smul_const (hc : DifferentiableWithinAt 𝕜 c s x) (f : F) :
    DifferentiableWithinAt 𝕜 (fun y => c y • f) s x :=
  (hc.hasFDerivWithinAt.smul_const f).differentiableWithinAt

@[fun_prop]
theorem DifferentiableAt.smul_const (hc : DifferentiableAt 𝕜 c x) (f : F) :
    DifferentiableAt 𝕜 (fun y => c y • f) x :=
  (hc.hasFDerivAt.smul_const f).differentiableAt

@[fun_prop]
theorem DifferentiableOn.smul_const (hc : DifferentiableOn 𝕜 c s) (f : F) :
    DifferentiableOn 𝕜 (fun y => c y • f) s := fun x hx => (hc x hx).smul_const f

@[fun_prop]
theorem Differentiable.smul_const (hc : Differentiable 𝕜 c) (f : F) :
    Differentiable 𝕜 fun y => c y • f := fun x => (hc x).smul_const f

theorem fderivWithin_smul_const (hxs : UniqueDiffWithinAt 𝕜 s x)
    (hc : DifferentiableWithinAt 𝕜 c s x) (f : F) :
    fderivWithin 𝕜 (fun y => c y • f) s x = (fderivWithin 𝕜 c s x).smulRight f :=
  (hc.hasFDerivWithinAt.smul_const f).fderivWithin hxs

theorem fderiv_smul_const (hc : DifferentiableAt 𝕜 c x) (f : F) :
    fderiv 𝕜 (fun y => c y • f) x = (fderiv 𝕜 c x).smulRight f :=
  (hc.hasFDerivAt.smul_const f).fderiv

end SMul

section Mul

/-! ### Derivative of the product of two functions -/

open scoped RightActions


variable {𝔸 𝔸' : Type*} [NormedRing 𝔸] [NormedCommRing 𝔸'] [NormedAlgebra 𝕜 𝔸] [NormedAlgebra 𝕜 𝔸']
  {a b : E → 𝔸} {a' b' : E →L[𝕜] 𝔸} {c d : E → 𝔸'} {c' d' : E →L[𝕜] 𝔸'}

@[to_fun (attr := fun_prop)]
theorem HasStrictFDerivAt.mul' {D : Type*} [TopologicalSpace D] {a b : D → 𝔸} {coord : D → E}
    {x : D} (ha : HasStrictFDerivAt a a' x coord) (hb : HasStrictFDerivAt b b' x coord)
    (hcoord : ContinuousAt coord x := by exact continuousAt_id) :
    HasStrictFDerivAt (a * b) (a x • b' + a' <• b x) x coord :=
  ((ContinuousLinearMap.mul 𝕜 𝔸).isBoundedBilinearMap.hasStrictFDerivAt (a x, b x)).comp
    (coord' := @id (𝔸 × 𝔸)) x
    (ha.prodMk hb) hcoord

@[to_fun (attr := fun_prop)]
theorem HasStrictFDerivAt.mul {D : Type*} [TopologicalSpace D] {c d : D → 𝔸'} {coord : D → E}
    {x : D} (hc : HasStrictFDerivAt c c' x coord) (hd : HasStrictFDerivAt d d' x coord)
    (hcoord : ContinuousAt coord x := by exact continuousAt_id) :
    HasStrictFDerivAt (c * d) (c x • d' + d x • c') x coord := by
  convert! hc.mul' hd hcoord
  ext z
  apply mul_comm

@[to_fun (attr := fun_prop)]
theorem HasFDerivWithinAt.mul' {D : Type*} [TopologicalSpace D] {a b : D → 𝔸} {coord : D → E}
    {x : D} {s : Set D} (ha : HasFDerivWithinAt a a' s x coord)
    (hb : HasFDerivWithinAt b b' s x coord)
    (hcoord : ContinuousWithinAt coord s x := by exact continuousWithinAt_id) :
    HasFDerivWithinAt (a * b) (a x • b' + a' <• b x) s x coord := by
  -- `by exact` to solve unification issues.
  exact ((ContinuousLinearMap.mul 𝕜 𝔸).isBoundedBilinearMap.hasFDerivAt
    (a x, b x)).comp_hasFDerivWithinAt (coord' := @id (𝔸 × 𝔸)) x (ha.prodMk hb) hcoord

@[to_fun (attr := fun_prop)]
theorem HasFDerivWithinAt.mul {D : Type*} [TopologicalSpace D] {c d : D → 𝔸'} {coord : D → E}
    {x : D} {s : Set D} (hc : HasFDerivWithinAt c c' s x coord)
    (hd : HasFDerivWithinAt d d' s x coord)
    (hcoord : ContinuousWithinAt coord s x := by exact continuousWithinAt_id) :
    HasFDerivWithinAt (c * d) (c x • d' + d x • c') s x coord := by
  convert! hc.mul' hd hcoord
  ext z
  apply mul_comm

@[to_fun (attr := fun_prop)]
theorem HasFDerivAt.mul' {D : Type*} [TopologicalSpace D] {a b : D → 𝔸} {coord : D → E} {x : D}
    (ha : HasFDerivAt a a' x coord) (hb : HasFDerivAt b b' x coord)
    (hcoord : ContinuousAt coord x := by exact continuousAt_id) :
    HasFDerivAt (a * b) (a x • b' + a' <• b x) x coord := by
  -- `by exact` to solve unification issues.
  exact ((ContinuousLinearMap.mul 𝕜 𝔸).isBoundedBilinearMap.hasFDerivAt
    (a x, b x)).comp (coord' := @id (𝔸 × 𝔸)) x (ha.prodMk hb) hcoord

@[to_fun (attr := fun_prop)]
theorem HasFDerivAt.mul {D : Type*} [TopologicalSpace D] {c d : D → 𝔸'} {coord : D → E} {x : D}
    (hc : HasFDerivAt c c' x coord) (hd : HasFDerivAt d d' x coord)
    (hcoord : ContinuousAt coord x := by exact continuousAt_id) :
    HasFDerivAt (c * d) (c x • d' + d x • c') x coord := by
  convert! hc.mul' hd hcoord
  ext z
  apply mul_comm

section Domain

variable {D : Type*} [TopologicalSpace D] {a b : D → 𝔸} {coord : D → E}
  {x : D} {s : Set D}

@[to_fun (attr := fun_prop)]
theorem DifferentiableWithinAt.mul (ha : DifferentiableWithinAt 𝕜 a s x coord)
    (hb : DifferentiableWithinAt 𝕜 b s x coord)
    (hcoord : ContinuousWithinAt coord s x := by exact continuousWithinAt_id) :
    DifferentiableWithinAt 𝕜 (a * b) s x coord :=
  (ha.hasFDerivWithinAt.mul' hb.hasFDerivWithinAt hcoord).differentiableWithinAt

@[to_fun (attr := simp, fun_prop)]
theorem DifferentiableAt.mul (ha : DifferentiableAt 𝕜 a x coord)
    (hb : DifferentiableAt 𝕜 b x coord)
    (hcoord : ContinuousAt coord x := by exact continuousAt_id) :
    DifferentiableAt 𝕜 (a * b) x coord :=
  (ha.hasFDerivAt.mul' hb.hasFDerivAt hcoord).differentiableAt

@[to_fun (attr := fun_prop)]
theorem DifferentiableOn.mul (ha : DifferentiableOn 𝕜 a s coord)
    (hb : DifferentiableOn 𝕜 b s coord)
    (hcoord : ContinuousOn coord s := by exact continuousOn_id) :
    DifferentiableOn 𝕜 (a * b) s coord := fun x hx => (ha x hx).mul (hb x hx) (hcoord x hx)

@[to_fun (attr := simp, fun_prop)]
theorem Differentiable.mul (ha : Differentiable 𝕜 a coord) (hb : Differentiable 𝕜 b coord)
    (hcoord : Continuous coord := by exact continuous_id) : Differentiable 𝕜 (a * b) coord :=
  fun x => (ha x).mul (hb x) hcoord.continuousAt

end Domain

theorem fderivWithin_fun_mul' (hxs : UniqueDiffWithinAt 𝕜 s x) (ha : DifferentiableWithinAt 𝕜 a s x)
    (hb : DifferentiableWithinAt 𝕜 b s x) :
    fderivWithin 𝕜 (fun y => a y * b y) s x =
      a x • fderivWithin 𝕜 b s x + fderivWithin 𝕜 a s x <• b x :=
  (ha.hasFDerivWithinAt.mul' hb.hasFDerivWithinAt).fderivWithin hxs

theorem fderivWithin_mul' (hxs : UniqueDiffWithinAt 𝕜 s x) (ha : DifferentiableWithinAt 𝕜 a s x)
    (hb : DifferentiableWithinAt 𝕜 b s x) :
    fderivWithin 𝕜 (a * b) s x =
      a x • fderivWithin 𝕜 b s x + fderivWithin 𝕜 a s x <• b x :=
  (ha.hasFDerivWithinAt.mul' hb.hasFDerivWithinAt).fderivWithin hxs

theorem fderivWithin_fun_mul (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : DifferentiableWithinAt 𝕜 c s x)
    (hd : DifferentiableWithinAt 𝕜 d s x) :
    fderivWithin 𝕜 (fun y => c y * d y) s x =
      c x • fderivWithin 𝕜 d s x + d x • fderivWithin 𝕜 c s x :=
  (hc.hasFDerivWithinAt.mul hd.hasFDerivWithinAt).fderivWithin hxs

theorem fderivWithin_mul (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : DifferentiableWithinAt 𝕜 c s x)
    (hd : DifferentiableWithinAt 𝕜 d s x) :
    fderivWithin 𝕜 (c * d) s x =
      c x • fderivWithin 𝕜 d s x + d x • fderivWithin 𝕜 c s x :=
  (hc.hasFDerivWithinAt.mul hd.hasFDerivWithinAt).fderivWithin hxs

theorem fderiv_fun_mul' (ha : DifferentiableAt 𝕜 a x) (hb : DifferentiableAt 𝕜 b x) :
    fderiv 𝕜 (fun y => a y * b y) x = a x • fderiv 𝕜 b x + fderiv 𝕜 a x <• b x :=
  (ha.hasFDerivAt.mul' hb.hasFDerivAt).fderiv

theorem fderiv_mul' (ha : DifferentiableAt 𝕜 a x) (hb : DifferentiableAt 𝕜 b x) :
    fderiv 𝕜 (a * b) x = a x • fderiv 𝕜 b x + fderiv 𝕜 a x <• b x :=
  (ha.hasFDerivAt.mul' hb.hasFDerivAt).fderiv

theorem fderiv_fun_mul (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x) :
    fderiv 𝕜 (fun y => c y * d y) x = c x • fderiv 𝕜 d x + d x • fderiv 𝕜 c x :=
  (hc.hasFDerivAt.mul hd.hasFDerivAt).fderiv

theorem fderiv_mul (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x) :
    fderiv 𝕜 (c * d) x = c x • fderiv 𝕜 d x + d x • fderiv 𝕜 c x :=
  (hc.hasFDerivAt.mul hd.hasFDerivAt).fderiv

section Domain

variable {D : Type*} [TopologicalSpace D] {a : D → 𝔸} {c : D → 𝔸'}
  {coord : D → E} {x : D} {s : Set D}

@[fun_prop]
theorem HasStrictFDerivAt.mul_const' (ha : HasStrictFDerivAt a a' x coord) (b : 𝔸) :
    HasStrictFDerivAt (fun y => a y * b) (a' <• b) x coord :=
  ((ContinuousLinearMap.mul 𝕜 𝔸).flip b).hasFDerivAtFilter.comp (coord' := id) ha Filter.tendsto_map

@[fun_prop]
theorem HasStrictFDerivAt.mul_const (hc : HasStrictFDerivAt c c' x coord) (d : 𝔸') :
    HasStrictFDerivAt (fun y => c y * d) (d • c') x coord := by
  convert! hc.mul_const' d
  ext z
  apply mul_comm

@[fun_prop]
theorem HasFDerivWithinAt.mul_const' (ha : HasFDerivWithinAt a a' s x coord) (b : 𝔸) :
    HasFDerivWithinAt (fun y => a y * b) (a' <• b) s x coord :=
  ((ContinuousLinearMap.mul 𝕜 𝔸).flip b).hasFDerivAtFilter.comp (coord' := id) ha Filter.tendsto_map

@[fun_prop]
theorem HasFDerivWithinAt.mul_const (hc : HasFDerivWithinAt c c' s x coord) (d : 𝔸') :
    HasFDerivWithinAt (fun y => c y * d) (d • c') s x coord := by
  convert! hc.mul_const' d
  ext z
  apply mul_comm

@[fun_prop]
theorem HasFDerivAt.mul_const' (ha : HasFDerivAt a a' x coord) (b : 𝔸) :
    HasFDerivAt (fun y => a y * b) (a' <• b) x coord :=
  ((ContinuousLinearMap.mul 𝕜 𝔸).flip b).hasFDerivAtFilter.comp (coord' := id) ha Filter.tendsto_map

@[fun_prop]
theorem HasFDerivAt.mul_const (hc : HasFDerivAt c c' x coord) (d : 𝔸') :
    HasFDerivAt (fun y => c y * d) (d • c') x coord := by
  convert! hc.mul_const' d
  ext z
  apply mul_comm

@[fun_prop]
theorem DifferentiableWithinAt.mul_const (ha : DifferentiableWithinAt 𝕜 a s x coord) (b : 𝔸) :
    DifferentiableWithinAt 𝕜 (fun y => a y * b) s x coord :=
  (ha.hasFDerivWithinAt.mul_const' b).differentiableWithinAt

@[fun_prop]
theorem DifferentiableAt.mul_const (ha : DifferentiableAt 𝕜 a x coord) (b : 𝔸) :
    DifferentiableAt 𝕜 (fun y => a y * b) x coord :=
  (ha.hasFDerivAt.mul_const' b).differentiableAt

@[fun_prop]
theorem DifferentiableOn.mul_const (ha : DifferentiableOn 𝕜 a s coord) (b : 𝔸) :
    DifferentiableOn 𝕜 (fun y => a y * b) s coord := fun x hx => (ha x hx).mul_const b

@[fun_prop]
theorem Differentiable.mul_const (ha : Differentiable 𝕜 a coord) (b : 𝔸) :
    Differentiable 𝕜 (fun y => a y * b) coord := fun x => (ha x).mul_const b

end Domain

theorem fderivWithin_mul_const' (hxs : UniqueDiffWithinAt 𝕜 s x)
    (ha : DifferentiableWithinAt 𝕜 a s x) (b : 𝔸) :
    fderivWithin 𝕜 (fun y => a y * b) s x = fderivWithin 𝕜 a s x <• b :=
  (ha.hasFDerivWithinAt.mul_const' b).fderivWithin hxs

theorem fderivWithin_mul_const (hxs : UniqueDiffWithinAt 𝕜 s x)
    (hc : DifferentiableWithinAt 𝕜 c s x) (d : 𝔸') :
    fderivWithin 𝕜 (fun y => c y * d) s x = d • fderivWithin 𝕜 c s x :=
  (hc.hasFDerivWithinAt.mul_const d).fderivWithin hxs

theorem fderiv_mul_const' (ha : DifferentiableAt 𝕜 a x) (b : 𝔸) :
    fderiv 𝕜 (fun y => a y * b) x = fderiv 𝕜 a x <• b :=
  (ha.hasFDerivAt.mul_const' b).fderiv

theorem fderiv_mul_const (hc : DifferentiableAt 𝕜 c x) (d : 𝔸') :
    fderiv 𝕜 (fun y => c y * d) x = d • fderiv 𝕜 c x :=
  (hc.hasFDerivAt.mul_const d).fderiv

section Domain

variable {D : Type*} [TopologicalSpace D] {a : D → 𝔸} {coord : D → E} {x : D} {s : Set D}

@[fun_prop]
theorem HasStrictFDerivAt.const_mul (ha : HasStrictFDerivAt a a' x coord) (b : 𝔸) :
    HasStrictFDerivAt (fun y => b * a y) (b • a') x coord :=
  ((ContinuousLinearMap.mul 𝕜 𝔸) b).hasFDerivAtFilter.comp (coord' := id) ha Filter.tendsto_map

@[fun_prop]
theorem HasFDerivWithinAt.const_mul (ha : HasFDerivWithinAt a a' s x coord) (b : 𝔸) :
    HasFDerivWithinAt (fun y => b * a y) (b • a') s x coord :=
  ((ContinuousLinearMap.mul 𝕜 𝔸) b).hasFDerivAtFilter.comp (coord' := id) ha Filter.tendsto_map

@[fun_prop]
theorem HasFDerivAt.const_mul (ha : HasFDerivAt a a' x coord) (b : 𝔸) :
    HasFDerivAt (fun y => b * a y) (b • a') x coord :=
  ((ContinuousLinearMap.mul 𝕜 𝔸) b).hasFDerivAtFilter.comp (coord' := id) ha Filter.tendsto_map

@[fun_prop]
theorem DifferentiableWithinAt.const_mul (ha : DifferentiableWithinAt 𝕜 a s x coord) (b : 𝔸) :
    DifferentiableWithinAt 𝕜 (fun y => b * a y) s x coord :=
  (ha.hasFDerivWithinAt.const_mul b).differentiableWithinAt

@[fun_prop]
theorem DifferentiableAt.const_mul (ha : DifferentiableAt 𝕜 a x coord) (b : 𝔸) :
    DifferentiableAt 𝕜 (fun y => b * a y) x coord :=
  (ha.hasFDerivAt.const_mul b).differentiableAt

@[fun_prop]
theorem DifferentiableOn.const_mul (ha : DifferentiableOn 𝕜 a s coord) (b : 𝔸) :
    DifferentiableOn 𝕜 (fun y => b * a y) s coord := fun x hx => (ha x hx).const_mul b

@[fun_prop]
theorem Differentiable.const_mul (ha : Differentiable 𝕜 a coord) (b : 𝔸) :
    Differentiable 𝕜 (fun y => b * a y) coord := fun x => (ha x).const_mul b

end Domain

theorem fderivWithin_const_mul (hxs : UniqueDiffWithinAt 𝕜 s x)
    (ha : DifferentiableWithinAt 𝕜 a s x) (b : 𝔸) :
    fderivWithin 𝕜 (fun y => b * a y) s x = b • fderivWithin 𝕜 a s x :=
  (ha.hasFDerivWithinAt.const_mul b).fderivWithin hxs

theorem fderiv_const_mul (ha : DifferentiableAt 𝕜 a x) (b : 𝔸) :
    fderiv 𝕜 (fun y => b * a y) x = b • fderiv 𝕜 a x :=
  (ha.hasFDerivAt.const_mul b).fderiv

end Mul

section Prod
open scoped RightActions

/-! ### Derivative of a finite product of functions -/

variable {ι : Type*} {𝔸 𝔸' : Type*} [NormedRing 𝔸] [NormedCommRing 𝔸'] [NormedAlgebra 𝕜 𝔸]
  [NormedAlgebra 𝕜 𝔸'] {u : Finset ι} {f : ι → E → 𝔸} {f' : ι → E →L[𝕜] 𝔸} {g : ι → E → 𝔸'}
  {g' : ι → E →L[𝕜] 𝔸'}

@[fun_prop]
theorem hasStrictFDerivAt_list_prod' [Finite ι] {l : List ι} {x : ι → 𝔸} :
    HasStrictFDerivAt (𝕜 := 𝕜) (fun x ↦ (l.map x).prod)
      (∑ i : Fin l.length, ((l.take i).map x).prod •
        proj l[i] <• ((l.drop (.succ i)).map x).prod) x := by
  have := Fintype.ofFinite ι
  induction l with
  | nil => simp [hasStrictFDerivAt_const]
  | cons a l IH =>
    simp only [List.map_cons, List.prod_cons, ← proj_apply (R := 𝕜) (φ := fun _ : ι ↦ 𝔸) a]
    exact .congr_fderiv (.mul' (ContinuousLinearMap.hasStrictFDerivAt _) IH)
      (by ext; simp [Fin.sum_univ_succ, Finset.mul_sum, mul_assoc, add_comm])

@[fun_prop]
theorem hasStrictFDerivAt_list_prod_finRange' {n : ℕ} {x : Fin n → 𝔸} :
    HasStrictFDerivAt (𝕜 := 𝕜) (fun x ↦ ((List.finRange n).map x).prod)
      (∑ i : Fin n, (((List.finRange n).take i).map x).prod •
        proj i <• (((List.finRange n).drop (.succ i)).map x).prod) x :=
  hasStrictFDerivAt_list_prod'.congr_fderiv <|
    Finset.sum_equiv (finCongr List.length_finRange) (by simp) (by simp)

@[fun_prop]
theorem hasStrictFDerivAt_list_prod_attach' {l : List ι} {x : {i // i ∈ l} → 𝔸} :
    HasStrictFDerivAt (𝕜 := 𝕜) (fun x ↦ (l.attach.map x).prod)
      (∑ i : Fin l.length, ((l.attach.take i).map x).prod •
        proj l.attach[i.cast List.length_attach.symm] <•
          ((l.attach.drop (.succ i)).map x).prod) x := by
  classical exact hasStrictFDerivAt_list_prod'.congr_fderiv <| Eq.symm <|
    Finset.sum_equiv (finCongr List.length_attach.symm) (by simp) (by simp)

@[fun_prop]
theorem hasFDerivAt_list_prod' [Finite ι] {l : List ι} {x : ι → 𝔸'} :
    HasFDerivAt (𝕜 := 𝕜) (fun x ↦ (l.map x).prod)
      (∑ i : Fin l.length, ((l.take i).map x).prod •
        proj l[i] <• ((l.drop (.succ i)).map x).prod) x :=
  have := Fintype.ofFinite ι
  hasStrictFDerivAt_list_prod'.hasFDerivAt

@[fun_prop]
theorem hasFDerivAt_list_prod_finRange' {n : ℕ} {x : Fin n → 𝔸} :
    HasFDerivAt (𝕜 := 𝕜) (fun x ↦ ((List.finRange n).map x).prod)
      (∑ i : Fin n, (((List.finRange n).take i).map x).prod •
        proj i <• (((List.finRange n).drop (.succ i)).map x).prod) x :=
  hasStrictFDerivAt_list_prod_finRange'.hasFDerivAt

@[fun_prop]
theorem hasFDerivAt_list_prod_attach' {l : List ι} {x : {i // i ∈ l} → 𝔸} :
    HasFDerivAt (𝕜 := 𝕜) (fun x ↦ (l.attach.map x).prod)
      (∑ i : Fin l.length, ((l.attach.take i).map x).prod •
        (proj l.attach[i.cast List.length_attach.symm]) <•
          ((l.attach.drop (.succ i)).map x).prod) x := by
  exact hasStrictFDerivAt_list_prod_attach'.hasFDerivAt

/--
Auxiliary lemma for `hasStrictFDerivAt_multiset_prod`.

For `NormedCommRing 𝔸'`, can rewrite as `Multiset` using `Multiset.prod_coe`.
-/
@[fun_prop]
theorem hasStrictFDerivAt_list_prod [DecidableEq ι] [Finite ι] {l : List ι} {x : ι → 𝔸'} :
    HasStrictFDerivAt (𝕜 := 𝕜) (fun x ↦ (l.map x).prod)
      (l.map fun i ↦ ((l.erase i).map x).prod • proj i).sum x := by
  have := Fintype.ofFinite ι
  refine hasStrictFDerivAt_list_prod'.congr_fderiv ?_
  conv_rhs => arg 1; arg 2; rw [← List.map_get_finRange l]
  simp only [List.map_map, ← List.sum_toFinset _ (List.nodup_finRange _), List.toFinset_finRange,
    Function.comp_def, ((List.erase_getElem _).map _).prod_eq, List.eraseIdx_eq_take_drop_succ,
    List.map_append, List.prod_append, List.get_eq_getElem, Fin.getElem_fin, Nat.succ_eq_add_one]
  exact Finset.sum_congr rfl fun i _ ↦ by
    ext; simp only [smul_apply, op_smul_eq_smul, smul_eq_mul]; ring

@[fun_prop]
theorem hasStrictFDerivAt_multiset_prod [DecidableEq ι] [Finite ι] {u : Multiset ι} {x : ι → 𝔸'} :
    HasStrictFDerivAt (𝕜 := 𝕜) (fun x ↦ (u.map x).prod)
      (u.map (fun i ↦ ((u.erase i).map x).prod • proj i)).sum x :=
  have := Fintype.ofFinite ι
  u.inductionOn fun l ↦ by simpa using hasStrictFDerivAt_list_prod

@[fun_prop]
theorem hasFDerivAt_multiset_prod [DecidableEq ι] [Finite ι] {u : Multiset ι} {x : ι → 𝔸'} :
    HasFDerivAt (𝕜 := 𝕜) (fun x ↦ (u.map x).prod)
      (Multiset.sum (u.map (fun i ↦ ((u.erase i).map x).prod • proj i))) x :=
  have := Fintype.ofFinite ι
  hasStrictFDerivAt_multiset_prod.hasFDerivAt

theorem hasStrictFDerivAt_finsetProd [DecidableEq ι] [Finite ι] {x : ι → 𝔸'} :
    HasStrictFDerivAt (𝕜 := 𝕜) (∏ i ∈ u, · i) (∑ i ∈ u, (∏ j ∈ u.erase i, x j) • proj i) x := by
  simp only [Finset.sum_eq_multiset_sum, Finset.prod_eq_multiset_prod]
  exact hasStrictFDerivAt_multiset_prod

@[deprecated (since := "2026-04-08")]
alias hasStrictFDerivAt_finset_prod := hasStrictFDerivAt_finsetProd

theorem hasFDerivAt_finsetProd [DecidableEq ι] [Finite ι] {x : ι → 𝔸'} :
    HasFDerivAt (𝕜 := 𝕜) (∏ i ∈ u, · i) (∑ i ∈ u, (∏ j ∈ u.erase i, x j) • proj i) x :=
  have := Fintype.ofFinite ι
  hasStrictFDerivAt_finsetProd.hasFDerivAt

@[deprecated (since := "2026-04-08")] alias hasFDerivAt_finset_prod := hasFDerivAt_finsetProd

section Comp

@[fun_prop]
theorem HasStrictFDerivAt.list_prod' {l : List ι} {x : E}
    (h : ∀ i ∈ l, HasStrictFDerivAt (f i ·) (f' i) x) :
    HasStrictFDerivAt (fun x ↦ (l.map (f · x)).prod)
      (∑ i : Fin l.length, ((l.take i).map (f · x)).prod •
        f' l[i] <• ((l.drop (.succ i)).map (f · x)).prod) x := by
  simp_rw [Fin.getElem_fin, ← l.get_eq_getElem, ← List.map_get_finRange l, List.map_map]
  refine .congr_fderiv (hasStrictFDerivAt_list_prod_finRange'.comp
    (coord' := @id (Fin l.length → 𝔸)) x
    (hasStrictFDerivAt_pi.mpr fun i ↦ h (l.get i) (List.getElem_mem ..))) ?_
  ext m
  simp_rw [List.map_take, List.map_drop, List.map_map, comp_apply, sum_apply, smul_apply,
    proj_apply, pi_apply, Function.comp_def]

/--
Unlike `HasFDerivAt.finsetProd`, supports non-commutative multiply and duplicate elements.
-/
@[fun_prop]
theorem HasFDerivAt.list_prod' {l : List ι} {x : E}
    (h : ∀ i ∈ l, HasFDerivAt (f i ·) (f' i) x) :
    HasFDerivAt (fun x ↦ (l.map (f · x)).prod)
      (∑ i : Fin l.length, ((l.take i).map (f · x)).prod •
        f' l[i] <• ((l.drop (.succ i)).map (f · x)).prod) x := by
  simp_rw [Fin.getElem_fin, ← l.get_eq_getElem, ← List.map_get_finRange l, List.map_map]
  have hcomp := hasFDerivAt_list_prod_finRange'.comp (coord' := @id (Fin l.length → 𝔸)) x
    (hasFDerivAt_pi.mpr fun i ↦ h (l.get i) (l.get_mem i))
  refine hcomp.congr_fderiv ?_
  ext m
  simp_rw [List.map_take, List.map_drop, List.map_map, comp_apply, sum_apply, smul_apply,
    proj_apply, pi_apply, Function.comp_def]

@[fun_prop]
theorem HasFDerivWithinAt.list_prod' {l : List ι} {x : E}
    (h : ∀ i ∈ l, HasFDerivWithinAt (f i ·) (f' i) s x) :
    HasFDerivWithinAt (fun x ↦ (l.map (f · x)).prod)
      (∑ i : Fin l.length, ((l.take i).map (f · x)).prod •
        f' l[i] <• ((l.drop (.succ i)).map (f · x)).prod) s x := by
  simp_rw [Fin.getElem_fin, ← l.get_eq_getElem, ← List.map_get_finRange l, List.map_map]
  have hcomp := hasFDerivAt_list_prod_finRange'.comp_hasFDerivWithinAt
    (coord' := @id (Fin l.length → 𝔸)) (s := s) x
    (hasFDerivWithinAt_pi.mpr fun i ↦ h (l.get i) (l.get_mem i))
  refine hcomp.congr_fderiv ?_
  ext m
  simp_rw [List.map_take, List.map_drop, List.map_map, comp_apply, sum_apply, smul_apply,
    proj_apply, pi_apply, Function.comp_def]

theorem fderiv_list_prod' {l : List ι} {x : E}
    (h : ∀ i ∈ l, DifferentiableAt 𝕜 (f i ·) x) :
    fderiv 𝕜 (fun x ↦ (l.map (f · x)).prod) x =
      ∑ i : Fin l.length, ((l.take i).map (f · x)).prod •
        (fderiv 𝕜 (fun x ↦ f l[i] x) x) <• ((l.drop (.succ i)).map (f · x)).prod :=
  (HasFDerivAt.list_prod' fun i hi ↦ (h i hi).hasFDerivAt).fderiv

theorem fderivWithin_list_prod' {l : List ι} {x : E}
    (hxs : UniqueDiffWithinAt 𝕜 s x) (h : ∀ i ∈ l, DifferentiableWithinAt 𝕜 (f i ·) s x) :
    fderivWithin 𝕜 (fun x ↦ (l.map (f · x)).prod) s x =
      ∑ i : Fin l.length, ((l.take i).map (f · x)).prod •
        (fderivWithin 𝕜 (fun x ↦ f l[i] x) s x) <• ((l.drop (.succ i)).map (f · x)).prod :=
  (HasFDerivWithinAt.list_prod' fun i hi ↦ (h i hi).hasFDerivWithinAt).fderivWithin hxs

@[fun_prop]
theorem HasStrictFDerivAt.multiset_prod [DecidableEq ι] {u : Multiset ι} {x : E}
    (h : ∀ i ∈ u, HasStrictFDerivAt (g i ·) (g' i) x) :
    HasStrictFDerivAt (fun x ↦ (u.map (g · x)).prod)
      (u.map fun i ↦ ((u.erase i).map (g · x)).prod • g' i).sum x := by
  simp only [← Multiset.attach_map_val u, Multiset.map_map]
  exact .congr_fderiv
    (hasStrictFDerivAt_multiset_prod.comp (coord' := @id ({i // i ∈ u} → 𝔸')) x
      (hasStrictFDerivAt_pi.mpr fun i ↦ h i.val i.prop))
    (by ext; simp [Finset.sum_multiset_map_count, u.erase_attach_map (g · x)])

/--
Unlike `HasFDerivAt.finsetProd`, supports duplicate elements.
-/
@[fun_prop]
theorem HasFDerivAt.multiset_prod [DecidableEq ι] {u : Multiset ι} {x : E}
    (h : ∀ i ∈ u, HasFDerivAt (g i ·) (g' i) x) :
    HasFDerivAt (fun x ↦ (u.map (g · x)).prod)
      (u.map fun i ↦ ((u.erase i).map (g · x)).prod • g' i).sum x := by
  simp only [← Multiset.attach_map_val u, Multiset.map_map]
  have hcomp := (hasFDerivAt_multiset_prod (u := u.attach)).comp
    (coord' := @id ({i // i ∈ u} → 𝔸')) x (hasFDerivAt_pi.mpr fun i ↦ h i.val i.prop)
  exact hcomp.congr_fderiv (by
    ext
    simp [Finset.sum_multiset_map_count, u.erase_attach_map (g · x)])

@[fun_prop]
theorem HasFDerivWithinAt.multiset_prod [DecidableEq ι] {u : Multiset ι} {x : E}
    (h : ∀ i ∈ u, HasFDerivWithinAt (g i ·) (g' i) s x) :
    HasFDerivWithinAt (fun x ↦ (u.map (g · x)).prod)
      (u.map fun i ↦ ((u.erase i).map (g · x)).prod • g' i).sum s x := by
  simp only [← Multiset.attach_map_val u, Multiset.map_map]
  have hcomp := (hasFDerivAt_multiset_prod (u := u.attach)).comp_hasFDerivWithinAt
    (coord' := @id ({i // i ∈ u} → 𝔸')) (s := s) x
    (hasFDerivWithinAt_pi.mpr fun i ↦ h i.val i.prop)
  exact hcomp.congr_fderiv (by
    ext
    simp [Finset.sum_multiset_map_count, u.erase_attach_map (g · x)])

theorem fderiv_multiset_prod [DecidableEq ι] {u : Multiset ι} {x : E}
    (h : ∀ i ∈ u, DifferentiableAt 𝕜 (g i ·) x) :
    fderiv 𝕜 (fun x ↦ (u.map (g · x)).prod) x =
      (u.map fun i ↦ ((u.erase i).map (g · x)).prod • fderiv 𝕜 (g i) x).sum :=
  (HasFDerivAt.multiset_prod fun i hi ↦ (h i hi).hasFDerivAt).fderiv

theorem fderivWithin_multiset_prod [DecidableEq ι] {u : Multiset ι} {x : E}
    (hxs : UniqueDiffWithinAt 𝕜 s x) (h : ∀ i ∈ u, DifferentiableWithinAt 𝕜 (g i ·) s x) :
    fderivWithin 𝕜 (fun x ↦ (u.map (g · x)).prod) s x =
      (u.map fun i ↦ ((u.erase i).map (g · x)).prod • fderivWithin 𝕜 (g i) s x).sum :=
  (HasFDerivWithinAt.multiset_prod fun i hi ↦ (h i hi).hasFDerivWithinAt).fderivWithin hxs

theorem HasStrictFDerivAt.finsetProd [DecidableEq ι] {x : E}
    (hg : ∀ i ∈ u, HasStrictFDerivAt (g i) (g' i) x) :
    HasStrictFDerivAt (∏ i ∈ u, g i ·) (∑ i ∈ u, (∏ j ∈ u.erase i, g j x) • g' i) x := by
  simpa [← Finset.prod_attach u] using .congr_fderiv
    (hasStrictFDerivAt_finsetProd.comp (coord' := @id (u → 𝔸')) x
      (hasStrictFDerivAt_pi.mpr fun i ↦ hg i.val i.prop))
    (by ext; simp [Finset.prod_erase_attach (g · x), ← u.sum_attach])

@[deprecated (since := "2026-04-08")]
alias HasStrictFDerivAt.finset_prod := HasStrictFDerivAt.finsetProd

theorem HasFDerivAt.finsetProd [DecidableEq ι] {x : E}
    (hg : ∀ i ∈ u, HasFDerivAt (g i) (g' i) x) :
    HasFDerivAt (∏ i ∈ u, g i ·) (∑ i ∈ u, (∏ j ∈ u.erase i, g j x) • g' i) x := by
  have hcomp := (hasFDerivAt_finsetProd (u := u.attach)).comp (coord' := @id (u → 𝔸')) x
    (hasFDerivAt_pi.mpr fun i ↦ hg i.val i.prop)
  simpa [Function.comp_def, ← Finset.prod_attach u] using hcomp.congr_fderiv
    (by ext; simp [Finset.prod_erase_attach (g · x), ← u.sum_attach])

@[deprecated (since := "2026-04-08")] alias HasFDerivAt.finset_prod := HasFDerivAt.finsetProd

theorem HasFDerivWithinAt.finsetProd [DecidableEq ι] {x : E}
    (hg : ∀ i ∈ u, HasFDerivWithinAt (g i) (g' i) s x) :
    HasFDerivWithinAt (∏ i ∈ u, g i ·) (∑ i ∈ u, (∏ j ∈ u.erase i, g j x) • g' i) s x := by
  have hcomp := (hasFDerivAt_finsetProd (u := u.attach)).comp_hasFDerivWithinAt
    (coord' := @id (u → 𝔸')) (s := s) x (hasFDerivWithinAt_pi.mpr fun i ↦ hg i.val i.prop)
  simpa [Function.comp_def, ← Finset.prod_attach u] using hcomp.congr_fderiv
    (by ext; simp [Finset.prod_erase_attach (g · x), ← u.sum_attach])

@[deprecated (since := "2026-04-08")]
alias HasFDerivWithinAt.finset_prod := HasFDerivWithinAt.finsetProd

theorem fderiv_finsetProd [DecidableEq ι] {x : E} (hg : ∀ i ∈ u, DifferentiableAt 𝕜 (g i) x) :
    fderiv 𝕜 (∏ i ∈ u, g i ·) x = ∑ i ∈ u, (∏ j ∈ u.erase i, (g j x)) • fderiv 𝕜 (g i) x :=
  (HasFDerivAt.finsetProd fun i hi ↦ (hg i hi).hasFDerivAt).fderiv

@[deprecated (since := "2026-04-08")] alias fderiv_finset_prod := fderiv_finsetProd

theorem fderivWithin_finsetProd [DecidableEq ι] {x : E} (hxs : UniqueDiffWithinAt 𝕜 s x)
    (hg : ∀ i ∈ u, DifferentiableWithinAt 𝕜 (g i) s x) :
    fderivWithin 𝕜 (∏ i ∈ u, g i ·) s x =
      ∑ i ∈ u, (∏ j ∈ u.erase i, (g j x)) • fderivWithin 𝕜 (g i) s x :=
  (HasFDerivWithinAt.finsetProd fun i hi ↦ (hg i hi).hasFDerivWithinAt).fderivWithin hxs

@[deprecated (since := "2026-04-08")] alias fderivWithin_finset_prod := fderivWithin_finsetProd

end Comp

end Prod

section AlgebraInverse

variable {R : Type*} [NormedRing R] [NormedAlgebra 𝕜 R]

open NormedRing ContinuousLinearMap Filter

/-- At an invertible element `x` of a normed algebra `R`, the Fréchet derivative of the inversion
operation is the linear map `fun t ↦ - x⁻¹ * t * x⁻¹`.

The function is defined on units, with their coercion as coordinates in the ambient algebra.
The derivative relation therefore requires no value of inversion at a nonunit. -/
@[fun_prop]
theorem hasFDerivAt_inv' (x : Rˣ) :
    HasFDerivAt (fun u : Rˣ ↦ (↑u⁻¹ : R)) (-mulLeftRight 𝕜 R ↑x⁻¹ ↑x⁻¹) x
      (fun u ↦ (u : R)) := by
  apply HasFDerivAt.of_isLittleO
  have hsmall : (fun u : Rˣ ↦ (↑x⁻¹ : R) - ↑u⁻¹) =o[𝓝 x]
      (fun _ ↦ (1 : ℝ)) := by
    apply (isLittleO_one_iff ℝ).2
    simpa only [sub_self] using
      (tendsto_const_nhds (x := (↑x⁻¹ : R))).sub (Units.continuous_coe_inv.tendsto x)
  have hlinear :
      (fun u : Rˣ ↦ ((↑x⁻¹ : R) - ↑u⁻¹) * (↑u - ↑x) * ↑x⁻¹) =o[𝓝 x]
        (fun u ↦ (u : R) - ↑x) := by
    simpa only [one_mul, mul_one, isLittleO_norm_right] using
      (hsmall.mul_isBigO (isBigO_refl (fun u : Rˣ ↦ (u : R) - ↑x) (𝓝 x)).norm_right).mul_isBigO
        (isBigO_const_const (↑x⁻¹ : R) (one_ne_zero : (1 : ℝ) ≠ 0) (𝓝 x))
  simpa only [neg_apply, mulLeftRight_apply, sub_neg_eq_add,
    Units.inv_sub_inv_remainder, sub_self, mul_zero, add_zero] using hlinear

@[fun_prop]
theorem differentiableAt_inv (x : Rˣ) :
    DifferentiableAt 𝕜 (fun u : Rˣ ↦ (↑u⁻¹ : R)) x (fun u ↦ (u : R)) :=
  (hasFDerivAt_inv' x).differentiableAt

@[fun_prop]
theorem differentiableWithinAt_inv (x : Rˣ) (s : Set Rˣ) :
    DifferentiableWithinAt 𝕜 (fun u : Rˣ ↦ (↑u⁻¹ : R)) s x (fun u ↦ (u : R)) :=
  (hasFDerivAt_inv' x).hasFDerivWithinAt.differentiableWithinAt

@[fun_prop]
theorem differentiableOn_inv (s : Set Rˣ) :
    DifferentiableOn 𝕜 (fun u : Rˣ ↦ (↑u⁻¹ : R)) s (fun u ↦ (u : R)) :=
  fun x _ ↦ differentiableWithinAt_inv x s

variable [HasSummableGeomSeries R]

/-- The computed derivative of inversion on its open unit domain. -/
theorem fderiv_inv' (x : Rˣ) :
    fderiv 𝕜 (fun u : Rˣ ↦ (↑u⁻¹ : R)) x (fun u ↦ (u : R)) =
      -mulLeftRight 𝕜 R ↑x⁻¹ ↑x⁻¹ :=
  (hasFDerivAt_inv' x).fderiv Units.isOpenEmbedding_val

/-- The computed inverse derivative within a set whose ambient tangent directions determine it. -/
theorem fderivWithin_inv' {s : Set Rˣ} (x : Rˣ)
    (hxs : UniqueDiffWithinAt 𝕜 ((fun u : Rˣ ↦ (u : R)) '' s) (x : R)) :
    fderivWithin 𝕜 (fun u : Rˣ ↦ (↑u⁻¹ : R)) s x (fun u ↦ (u : R)) =
      -mulLeftRight 𝕜 R ↑x⁻¹ ↑x⁻¹ := by
  apply (hasFDerivAt_inv' x).hasFDerivWithinAt.fderivWithin_of_unique
  intro g hg
  exact hg.unique_of_isEmbedding (hasFDerivAt_inv' x).hasFDerivWithinAt
    Units.isOpenEmbedding_val.isEmbedding hxs

/-- Inversion on the open unit locus has a uniquely determined ambient derivative. -/
theorem hasUniqueFDerivAt_inv' (x : Rˣ) :
    ∃! f' : R →L[𝕜] R,
      HasFDerivAt (fun u : Rˣ ↦ (↑u⁻¹ : R)) f' x (fun u ↦ (u : R)) := by
  refine ⟨-mulLeftRight 𝕜 R ↑x⁻¹ ↑x⁻¹, hasFDerivAt_inv' x, ?_⟩
  intro f' hf'
  exact hf'.unique (hasFDerivAt_inv' x) Units.isOpenEmbedding_val

omit [HasSummableGeomSeries R] in
theorem hasStrictFDerivAt_inv' (x : Rˣ) :
    HasStrictFDerivAt (fun u : Rˣ ↦ (↑u⁻¹ : R)) (-mulLeftRight 𝕜 R ↑x⁻¹ ↑x⁻¹) x
      (fun u ↦ (u : R)) := by
  apply HasStrictFDerivAt.of_isLittleO
  let d : Rˣ × Rˣ → R := fun p ↦ (p.1 : R) - ↑p.2
  have hu : Tendsto (fun p : Rˣ × Rˣ ↦ (↑p.1⁻¹ : R)) (𝓝 (x, x)) (𝓝 (↑x⁻¹ : R)) :=
    (Units.continuous_coe_inv.comp continuous_fst).tendsto (x, x)
  have hv : Tendsto (fun p : Rˣ × Rˣ ↦ (↑p.2⁻¹ : R)) (𝓝 (x, x)) (𝓝 (↑x⁻¹ : R)) :=
    (Units.continuous_coe_inv.comp continuous_snd).tendsto (x, x)
  have hdu : (fun p : Rˣ × Rˣ ↦ (↑x⁻¹ : R) - ↑p.1⁻¹) =o[𝓝 (x, x)]
      (fun _ ↦ (1 : ℝ)) :=
    (isLittleO_one_iff ℝ).2 (by
      simpa only [sub_self] using (tendsto_const_nhds (x := (↑x⁻¹ : R))).sub hu)
  have hdv : (fun p : Rˣ × Rˣ ↦ (↑x⁻¹ : R) - ↑p.2⁻¹) =o[𝓝 (x, x)]
      (fun _ ↦ (1 : ℝ)) :=
    (isLittleO_one_iff ℝ).2 (by
      simpa only [sub_self] using (tendsto_const_nhds (x := (↑x⁻¹ : R))).sub hv)
  have hd := (isBigO_refl d (𝓝 (x, x))).norm_right
  have hleft := (hdu.mul_isBigO hd).mul_isBigO
    (isBigO_const_const (↑x⁻¹ : R) (one_ne_zero : (1 : ℝ) ≠ 0) (𝓝 (x, x)))
  have hright := ((hu.isBigO_one ℝ).mul hd).mul_isLittleO hdv
  have hrem :
      (fun p : Rˣ × Rˣ ↦ ((↑x⁻¹ : R) - ↑p.1⁻¹) * d p * ↑x⁻¹ +
        ↑p.1⁻¹ * d p * (↑x⁻¹ - ↑p.2⁻¹)) =o[𝓝 (x, x)] d := by
    simpa only [one_mul, mul_one, isLittleO_norm_right] using hleft.add hright
  simpa only [d, neg_apply, mulLeftRight_apply, sub_neg_eq_add,
    Units.inv_sub_inv_remainder] using hrem

variable {h : E → R} {z : E} {S : Set E}

@[fun_prop]
theorem HasFDerivWithinAt.inv {h' : E →L[𝕜] R} (hf : HasFDerivWithinAt h h' S z)
    (hz : IsUnit (h z)) :
    HasFDerivWithinAt
      (fun y : {y : E | IsUnit (h y)} ↦ (↑y.property.unit⁻¹ : R))
      ((-mulLeftRight 𝕜 R ↑hz.unit⁻¹ ↑hz.unit⁻¹).comp h') (Subtype.val ⁻¹' S) ⟨z, hz⟩
      (fun y ↦ (y : E)) := by
  let D := {y : E | IsUnit (h y)}
  let q : D → Rˣ := fun y ↦ y.property.unit
  have hrestricted :
      HasFDerivWithinAt (fun y : D ↦ h y) h'
        (Subtype.val ⁻¹' S) ⟨z, hz⟩ (fun y ↦ (y : E)) := by
    exact HasFDerivAtFilter.comp_tendsto hf Subtype.val
      ((continuous_subtype_val.continuousWithinAt.tendsto_nhdsWithin (fun _ hy ↦ hy)).prodMap
        (tendsto_pure_pure ..))
  have hcoordinates :
      HasFDerivWithinAt ((fun u : Rˣ ↦ (u : R)) ∘ q) h'
        (Subtype.val ⁻¹' S) ⟨z, hz⟩ (fun y ↦ (y : E)) := by
    simpa only [q, Function.comp_def, IsUnit.unit_spec] using hrestricted
  exact ((hasFDerivAt_inv' (q ⟨z, hz⟩)).comp_hasFDerivWithinAt ⟨z, hz⟩ hcoordinates
    continuous_subtype_val.continuousWithinAt Units.isOpenEmbedding_val.isEmbedding)

@[fun_prop]
theorem HasStrictFDerivAt.inv {h' : E →L[𝕜] R} (hf : HasStrictFDerivAt h h' z) (hz : IsUnit (h z)) :
    HasStrictFDerivAt (fun y : {y : E | IsUnit (h y)} ↦ (↑y.property.unit⁻¹ : R))
      ((-mulLeftRight 𝕜 R ↑hz.unit⁻¹ ↑hz.unit⁻¹).comp h') ⟨z, hz⟩ (fun y ↦ (y : E)) := by
  let D := {y : E | IsUnit (h y)}
  let q : D → Rˣ := fun y ↦ y.property.unit
  have hrestricted : HasStrictFDerivAt (fun y : D ↦ h y) h'
      ⟨z, hz⟩ (fun y ↦ (y : E)) := by
    exact HasFDerivAtFilter.comp_tendsto hf Subtype.val
      ((continuous_subtype_val.tendsto ⟨z, hz⟩).prodMap_nhds
        (continuous_subtype_val.tendsto ⟨z, hz⟩))
  have hcoordinates : HasStrictFDerivAt ((fun u : Rˣ ↦ (u : R)) ∘ q) h'
      ⟨z, hz⟩ (fun y ↦ (y : E)) := by
    simpa only [q, Function.comp_def, IsUnit.unit_spec] using hrestricted
  exact ((hasStrictFDerivAt_inv' (q ⟨z, hz⟩)).comp ⟨z, hz⟩ hcoordinates
    continuous_subtype_val.continuousAt Units.isOpenEmbedding_val.isEmbedding)

@[fun_prop]
theorem HasFDerivAt.inv {h' : E →L[𝕜] R} (hf : HasFDerivAt h h' z) (hz : IsUnit (h z)) :
    HasFDerivAt (fun y : {y : E | IsUnit (h y)} ↦ (↑y.property.unit⁻¹ : R))
      ((-mulLeftRight 𝕜 R ↑hz.unit⁻¹ ↑hz.unit⁻¹).comp h') ⟨z, hz⟩ (fun y ↦ (y : E)) := by
  let D := {y : E | IsUnit (h y)}
  let q : D → Rˣ := fun y ↦ y.property.unit
  have hrestricted : HasFDerivAt (fun y : D ↦ h y) h'
      ⟨z, hz⟩ (fun y ↦ (y : E)) := by
    exact HasFDerivAtFilter.comp_tendsto hf Subtype.val
      ((continuous_subtype_val.tendsto ⟨z, hz⟩).prodMap (tendsto_pure_pure ..))
  have hcoordinates : HasFDerivAt ((fun u : Rˣ ↦ (u : R)) ∘ q) h'
      ⟨z, hz⟩ (fun y ↦ (y : E)) := by
    simpa only [q, Function.comp_def, IsUnit.unit_spec] using hrestricted
  exact ((hasFDerivAt_inv' (q ⟨z, hz⟩)).comp ⟨z, hz⟩ hcoordinates
    continuous_subtype_val.continuousAt Units.isOpenEmbedding_val.isEmbedding)

@[fun_prop]
theorem DifferentiableWithinAt.inv (hf : DifferentiableWithinAt 𝕜 h S z) (hz : IsUnit (h z)) :
    DifferentiableWithinAt 𝕜
      (fun y : {y : E | IsUnit (h y)} ↦ (↑y.property.unit⁻¹ : R))
      (Subtype.val ⁻¹' S) ⟨z, hz⟩ (fun y ↦ (y : E)) :=
  (hf.hasFDerivWithinAt.inv hz).differentiableWithinAt

@[simp, fun_prop]
theorem DifferentiableAt.inv (hf : DifferentiableAt 𝕜 h z) (hz : IsUnit (h z)) :
    DifferentiableAt 𝕜 (fun y : {y : E | IsUnit (h y)} ↦ (↑y.property.unit⁻¹ : R))
      ⟨z, hz⟩ (fun y ↦ (y : E)) :=
  (hf.hasFDerivAt.inv hz).differentiableAt

@[fun_prop]
theorem DifferentiableOn.inv (hf : DifferentiableOn 𝕜 h S) (hz : ∀ x ∈ S, IsUnit (h x)) :
    DifferentiableOn 𝕜 (fun y : {y : E | IsUnit (h y)} ↦ (↑y.property.unit⁻¹ : R))
      (Subtype.val ⁻¹' S) (fun y ↦ (y : E)) :=
  fun x hx ↦ (hf x hx).inv (hz x hx)

@[simp, fun_prop]
theorem Differentiable.inv (hf : Differentiable 𝕜 h) (hz : ∀ x, IsUnit (h x)) :
    Differentiable 𝕜 (fun x ↦ (↑(hz x).unit⁻¹ : R)) := by
  intro z
  let q : E → Rˣ := fun x ↦ (hz x).unit
  have hcoordinates : HasFDerivAt ((fun u : Rˣ ↦ (u : R)) ∘ q) (fderiv 𝕜 h z) z := by
    simpa only [q, Function.comp_def, IsUnit.unit_spec] using (hf z).hasFDerivAt
  exact ((hasFDerivAt_inv' (q z)).comp z hcoordinates
    continuousAt_id Units.isOpenEmbedding_val.isEmbedding).differentiableAt

end AlgebraInverse

end
