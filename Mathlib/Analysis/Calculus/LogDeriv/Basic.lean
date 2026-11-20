/-
Copyright (c) 2024 Chris Birkbeck, 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Yi-Jing Tseng
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Logarithmic derivative on its canonical domain

The logarithmic derivative at a point requires a uniquely determined scalar derivative and an
invertible function value. The source can be an arbitrary topological domain with coordinates
in the scalar field. Open coordinates provide a routine sufficient condition for uniqueness;
explicit uniqueness evidence also permits thinner domains.
-/

@[expose] public section

noncomputable section

open scoped Topology

variable {𝕜 𝕜' D : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedAlgebra 𝕜 𝕜'] [TopologicalSpace D]

/-- A local coordinate neighbourhood gives a uniquely determined scalar derivative. -/
theorem HasDerivAt.existsUnique_hasDerivAt_of_mem_nhds {F : Type*} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] {f : D → F} {x : D} {d : F} {coord : D → 𝕜}
    (hf : HasDerivAt f d x coord) (hcoord : Topology.IsEmbedding coord)
    (hdom : Set.range coord ∈ 𝓝 (coord x)) : ∃! e, HasDerivAt f e x coord := by
  refine ⟨d, hf, fun e he ↦ ?_⟩
  exact ContinuousLinearMap.toSpanSingleton_inj.mp
    (he.hasFDerivAt.unique_of_mem_nhds hf.hasFDerivAt hcoord hdom)

/-- Open coordinates are a routine sufficient condition for uniqueness, not its definition. -/
theorem HasDerivAt.existsUnique_hasDerivAt {F : Type*} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] {f : D → F} {x : D} {d : F}
    {coord : D → 𝕜} (hf : HasDerivAt f d x coord)
    (hcoord : Topology.IsOpenEmbedding coord := by exact Topology.IsOpenEmbedding.id) :
    ∃! e, HasDerivAt f e x coord :=
  hf.existsUnique_hasDerivAt_of_mem_nhds hcoord.isEmbedding
    (hcoord.isOpen_range.mem_nhds (Set.mem_range_self x))

theorem DifferentiableAt.existsUnique_hasDerivAt {F : Type*} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] {f : D → F} {x : D}
    {coord : D → 𝕜} (hf : DifferentiableAt 𝕜 f x coord)
    (hcoord : Topology.IsOpenEmbedding coord := by exact Topology.IsOpenEmbedding.id) :
    ∃! e, HasDerivAt f e x coord :=
  hf.hasFDerivAt.hasDerivAt.existsUnique_hasDerivAt hcoord

/-- The logarithmic derivative uses only an existing unique derivative and a unit value. -/
noncomputable def logDeriv (f : D → 𝕜') (x : D) (coord : D → 𝕜 := by exact id)
    (hderiv : ∃! d, HasDerivAt f d x coord := by
      run_tac Checked.addSubtypeFacts
      first
      | assumption
      | solve_by_elim (maxDepth := 6)
          [HasDerivAt.existsUnique_hasDerivAt, DifferentiableAt.existsUnique_hasDerivAt,
            HasDerivAt.existsUnique_hasDerivAt_of_mem_nhds,
            hasDerivAt_const, hasDerivAt_id, DifferentiableAt.mul, DifferentiableAt.neg,
            DifferentiableAt.mul_const, DifferentiableAt.const_mul,
            DifferentiableOn.differentiableAt, IsOpen.mem_nhds, continuousAt_id,
            Topology.IsOpenEmbedding.id, And.left, And.right]
      | fail "an existing unique derivative is required")
    (hvalue : IsUnit (f x) := by checked_unit) : 𝕜' :=
  Checked.div (Classical.choose hderiv) (f x) hvalue

theorem logDeriv_eq {f : D → 𝕜'} {x : D} {coord : D → 𝕜} {d : 𝕜'}
    {hderiv : ∃! e, HasDerivAt f e x coord} {hvalue : IsUnit (f x)}
    (hf : HasDerivAt f d x coord) :
    logDeriv f x coord hderiv hvalue = Checked.div d (f x) hvalue := by
  unfold logDeriv
  congr 1
  exact ((Classical.choose_spec hderiv).2 d hf).symm

theorem logDeriv_apply (f : D → 𝕜') (x : D) {coord : D → 𝕜}
    {hderiv : ∃! d, HasDerivAt f d x coord} {hvalue : IsUnit (f x)} :
    logDeriv f x coord hderiv hvalue = Checked.div (deriv f x coord) (f x) hvalue := by
  apply logDeriv_eq
  have hd : DifferentiableAt 𝕜 f x coord := (Classical.choose_spec hderiv).1.differentiableAt
  exact hd.hasFDerivAt.hasDerivAt
