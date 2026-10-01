import Mathlib.MeasureTheory.Group.Measure

/-!
# Pulling back Haar measures along open embeddings

These tests check that `MeasureTheory.Measure.IsHaarMeasure.comap` and its additive version find
their `MeasurableMul` (resp. `MeasurableAdd`) argument on the codomain by instance search.
-/

open MeasureTheory Measure

variable {G H : Type*} [SigmaAlgebra G] [SigmaAlgebra H]

example [Group G] [TopologicalSpace G] [BorelSpace G]
    [Group H] [TopologicalSpace H] [BorelSpace H] [MeasurableMul H]
    (μ : Measure H) [IsHaarMeasure μ] {f : G →* H} (hf : Topology.IsOpenEmbedding f) :
    (μ.comap f).IsHaarMeasure :=
  IsHaarMeasure.comap μ hf

example [AddGroup G] [TopologicalSpace G] [BorelSpace G]
    [AddGroup H] [TopologicalSpace H] [BorelSpace H] [MeasurableAdd H]
    (μ : Measure H) [IsAddHaarMeasure μ] {f : G →+ H} (hf : Topology.IsOpenEmbedding f) :
    (μ.comap f).IsAddHaarMeasure :=
  IsAddHaarMeasure.comap μ hf

/- A Haar measure on a topological group restricts to a Haar measure on an open subgroup. Here
`MeasurableMul H` is derived from the continuity of multiplication. -/
example [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [BorelSpace H]
    (μ : Measure H) [IsHaarMeasure μ] (U : Subgroup H) (hU : IsOpen (U : Set H)) :
    (μ.comap U.subtype).IsHaarMeasure :=
  IsHaarMeasure.comap μ hU.isOpenEmbedding_subtypeVal
