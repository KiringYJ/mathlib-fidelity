import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

open scoped Topology

-- Order zero is evaluation even when coordinates are collapsed.
example {D : Type*} [TopologicalSpace D] (f : D → ℝ) (x : D) (coord : D → ℝ) :
    HasIteratedDerivAt 0 f (f x) x coord := rfl

-- Order one uses only a derivative at the point, not a derivative on a neighborhood.
example {D : Type*} [TopologicalSpace D] {f : D → ℝ} {d : ℝ} {x : D} {coord : D → ℝ}
    (h : HasDerivAt f d x coord) : HasIteratedDerivAt 1 f d x coord :=
  HasIteratedDerivAt.one.mpr h

-- The relation does not invent uniqueness for a collapsed coordinate domain.
example (d : ℝ) :
    HasIteratedDerivAt 1 (fun _ : Unit ↦ (0 : ℝ)) d () (fun _ ↦ (0 : ℝ)) := by
  apply HasIteratedDerivAt.one.mpr
  change HasFDerivAt _ (ContinuousLinearMap.toSpanSingleton ℝ d) _ _
  rw [hasFDerivAt_iff_isLittleOTVS]
  simp
  exact Asymptotics.IsLittleOTVS.zero _ _

-- Open coordinates supply a sufficient uniqueness hypothesis.
example {D : Type*} [TopologicalSpace D] {f : D → ℝ} {d e : ℝ} {x : D} {coord : D → ℝ}
    {n : ℕ} (h : HasIteratedDerivAt n f d x coord) (h' : HasIteratedDerivAt n f e x coord)
    (hc : Topology.IsOpenEmbedding coord) : d = e := h.unique h' hc
