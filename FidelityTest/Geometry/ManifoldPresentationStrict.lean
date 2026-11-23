import Mathlib.Geometry.Manifold.Immersion
import Mathlib.Geometry.Manifold.Submersion

/-!
# Immersions and submersions expose no chosen local data

Being an immersion or a submersion at a point is the existence of charts and a linear equivalence
presenting the map in a normal form, with a complement of a model space. None of these is
determined by the map, so they are not functions of the proof: a proof obtains them from the
existence statement, and the statements about given charts take the charts explicitly.
-/

open Manifold
open scoped ContDiff

/-! The chosen witnesses are removed. -/

/-- info: Unknown constant `Manifold.LiftSourceTargetPropertyAt.localPresentationAt` -/
#guard_msgs in
#check_failure Manifold.LiftSourceTargetPropertyAt.localPresentationAt

/-- info: Unknown constant `Manifold.LiftSourceTargetPropertyAt.domChart` -/
#guard_msgs in
#check_failure Manifold.LiftSourceTargetPropertyAt.domChart

/-- info: Unknown constant `Manifold.IsImmersionAtOfComplement.equiv` -/
#guard_msgs in
#check_failure Manifold.IsImmersionAtOfComplement.equiv

/-- info: Unknown constant `Manifold.IsImmersionAt.complement` -/
#guard_msgs in
#check_failure Manifold.IsImmersionAt.complement

/-- info: Unknown constant `Manifold.IsImmersion.complement` -/
#guard_msgs in
#check_failure Manifold.IsImmersion.complement

/-- info: Unknown constant `Manifold.IsSubmersionAtOfComplement.equiv` -/
#guard_msgs in
#check_failure Manifold.IsSubmersionAtOfComplement.equiv

/-- info: Unknown constant `Manifold.IsSubmersionAt.complement` -/
#guard_msgs in
#check_failure Manifold.IsSubmersionAt.complement

/-- info: Unknown constant `Manifold.IsSubmersion.complement` -/
#guard_msgs in
#check_failure Manifold.IsSubmersion.complement

/-! A proof obtains a presentation from the existence statement. -/

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E E'' F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H G : Type*} [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E'' G}
  {M N : Type*} [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω} {f : M → N} {x : M}

example (h : IsImmersionAtOfComplement F I J n f x) : ∃ U ∈ nhds x, ContinuousOn f U := by
  obtain ⟨p⟩ := h
  obtain ⟨equiv, hwritten⟩ := p.property
  exact ⟨p.domChart.source, p.domChart.open_source.mem_nhds p.mem_domChart_source,
    IsImmersionAtOfComplement.continuousOn_of_eqOn p.source_subset_preimage_source hwritten⟩

example (h : IsImmersionAtOfComplement F I J n f x) : ContinuousAt f x := h.continuousAt

example (h : IsSubmersionAtOfComplement F I J n f x) : ContMDiffAt I J n f x := h.contMDiffAt

end
