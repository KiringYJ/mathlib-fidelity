/-
Copyright (c) 2026 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.OneSidedInverse
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Continuous left/right inverses in finite dimension and between Banach spaces

We prove sufficient criteria for a continuous linear map to admit a continuous left/right inverse,
in the sense of `ContinuousLinearMap.HasLeftInverse` and `ContinuousLinearMap.HasRightInverse`.
Over a complete nontrivially normed field, a surjective continuous linear map onto a
finite-dimensional Hausdorff space always admits a continuous right inverse, and an injective
continuous linear map into a finite-dimensional Hausdorff space always admits a continuous left
inverse.

We also prove the converse of `ContinuousLinearMap.HasLeftInverse.closedComplemented_range` and
`ContinuousLinearMap.HasLeftInverse.isClosed_range` between Banach spaces: `f` admits a continuous
left inverse if it is injective, has closed range and its range admits a closed complement.

## Main results

* `ContinuousLinearMap.HasLeftInverse.of_injective_of_isClosed_range_of_closedComplement_range`:
  if `f` is a continuous linear map between Banach spaces which is injective and has closed range
  with a closed complement, it admits a continuous left inverse
* `ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional`: over a complete field,
  if `f : E → F` is injective and `F` is finite-dimensional, `f` has a continuous left inverse.
* `ContinuousLinearMap.HasRightInverse.of_surjective_of_finiteDimensional`: over a complete field,
  if `f : E → F` is surjective and `F` is finite-dimensional, `f` has a continuous right inverse.

## TODO

* Suppose `E` and `F` are Banach and `f : E → F` is Fredholm.
  If `f` is surjective, it has a continuous right inverse.
  If `f` is injective, it has a continuous left inverse.

-/

public section

open Function Set

noncomputable section

namespace ContinuousLinearMap

namespace HasLeftInverse

section NontriviallyNormedField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E F : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  [TopologicalSpace F] [AddCommGroup F] [Module 𝕜 F] [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F]
  [T2Space F] {f : E →L[𝕜] F}

/-- If `f : E → F` is injective and `F` is finite-dimensional,
`f` has a continuous left inverse. -/
lemma of_injective_of_finiteDimensional [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]
    (hf : Injective f) :
    f.HasLeftInverse := by
  -- An injective linear map has a linear inverse; this inverse is automatically continuous
  -- because its domain is finite-dimensional.
  obtain ⟨g, hg⟩ :=
    f.toLinearMap.exists_leftInverse_of_injective (f.ker_eq_bot_of_injective hf)
  exact ⟨⟨g, LinearMap.continuous_of_finiteDimensional _⟩, fun x ↦ congr($hg x)⟩

end NontriviallyNormedField

section

variable {R E F : Type*} [NontriviallyNormedField R]
  [NormedAddCommGroup E] [NormedSpace R E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace R F] [CompleteSpace F]

/-- A continuous linear map between Banach spaces has a continuous left inverse if it is injective,
has closed range and its range has a closed complement. -/
lemma of_injective_of_isClosed_range_of_closedComplement_range {f : E →L[R] F}
    (hf : Injective f) (hf' : IsClosed (range f)) (hf'' : Submodule.ClosedComplemented f.range) :
    f.HasLeftInverse := by
  -- We compose the continuous inverse of `f : E → range f` with the projection `p : F → range f`.
  obtain ⟨p, hp⟩ := hf''
  refine ⟨(f.leftInverseOfInjectiveOfIsClosedRange hf hf').comp p, fun x ↦ ?_⟩
  simpa [hp ⟨f x, by simp⟩] using! f.leftInverseOfInjectiveOfIsClosedRange_apply hf hf' x

end

end HasLeftInverse

namespace HasRightInverse

section NontriviallyNormedField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E F : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  [TopologicalSpace F] [AddCommGroup F] [Module 𝕜 F] [IsTopologicalAddGroup F] [ContinuousSMul 𝕜 F]
  [T2Space F] {f : E →L[𝕜] F}

/-- If `f : E → F` is surjective and `F` is finite-dimensional,
`f` has a continuous right inverse. -/
lemma of_surjective_of_finiteDimensional [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F]
    (hf : Surjective f) :
    f.HasRightInverse := by
  -- A surjective linear map has a linear inverse, which is automatically continuous
  -- because its domain is finite-dimensional.
  obtain ⟨g, hg⟩ :=
    f.toLinearMap.exists_rightInverse_of_surjective (f.range_eq_top_of_surjective hf)
  exact ⟨⟨g, g.continuous_of_finiteDimensional⟩, fun x ↦ congr($hg x)⟩

end NontriviallyNormedField

end HasRightInverse

end ContinuousLinearMap

end
