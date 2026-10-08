/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module

public import Mathlib.Topology.UniformSpace.UniformEmbedding

/-!
# Cauchy continuous maps

A map between uniform spaces is *Cauchy continuous* if it maps Cauchy filters to Cauchy filters.
A uniformly continuous map is Cauchy continuous (`UniformContinuous.cauchyContinuous`), and a
Cauchy continuous map is continuous (`CauchyContinuous.continuous`).

Cauchy continuity is sufficient for extending a map along a dense uniform inducing map: if
`e : α → β` is uniform inducing with dense range and `f : α → γ` is Cauchy continuous with `γ`
complete and separated, then `f` has a continuous extension to `β`
(`CauchyContinuous.continuous_extend`, `CauchyContinuous.extend_eq`).  It is also necessary when
`β` is complete, as for the completion: a continuous map after a Cauchy continuous map into a
complete space is Cauchy continuous (`Continuous.cauchyContinuous_comp`).  For the completion of
`α`, `UniformSpace.Completion.cauchyContinuous_iff_exists_continuous_extension` states the
equivalence.  This is how the operations of a uniform space extend to its completion.

## Main definitions

* `CauchyContinuous f`: the map `f` sends Cauchy filters to Cauchy filters.
-/

@[expose] public section

open Filter Topology

variable {α β γ : Type*} [UniformSpace α] [UniformSpace β] [UniformSpace γ]

/-- A map between uniform spaces is Cauchy continuous if it maps Cauchy filters to Cauchy
filters. -/
def CauchyContinuous (f : α → β) : Prop :=
  ∀ ⦃F : Filter α⦄, Cauchy F → Cauchy (F.map f)

theorem UniformContinuous.cauchyContinuous {f : α → β} (hf : UniformContinuous f) :
    CauchyContinuous f :=
  fun _ hF ↦ hF.map hf

theorem cauchyContinuous_id : CauchyContinuous (id : α → α) :=
  uniformContinuous_id.cauchyContinuous

theorem CauchyContinuous.comp {g : β → γ} {f : α → β} (hg : CauchyContinuous g)
    (hf : CauchyContinuous f) : CauchyContinuous (g ∘ f) := fun F hF ↦ by
  rw [← map_map]
  exact hg (hf hF)

/-- A Cauchy continuous map is continuous: the image of a neighborhood filter is a Cauchy filter
that clusters at the image of the point. -/
theorem CauchyContinuous.continuous {f : α → β} (hf : CauchyContinuous f) : Continuous f := by
  refine continuous_iff_continuousAt.2 fun x ↦ le_nhds_of_cauchy_adhp (hf cauchy_nhds) ?_
  have hle : pure (f x) ≤ 𝓝 (f x) ⊓ map f (𝓝 x) :=
    le_inf (pure_le_nhds _) ((map_pure f x).symm.le.trans (map_mono (pure_le_nhds x)))
  exact neBot_of_le hle

/-- Composing with a uniform inducing map neither creates nor destroys Cauchy continuity. -/
theorem IsUniformInducing.cauchyContinuous_iff {g : β → γ} (hg : IsUniformInducing g)
    {f : α → β} : CauchyContinuous f ↔ CauchyContinuous (g ∘ f) := by
  refine ⟨fun hf ↦ hg.uniformContinuous.cauchyContinuous.comp hf, fun hgf F hF ↦ ?_⟩
  rw [← hg.cauchy_map_iff, map_map]
  exact hgf hF

/-- A continuous map after a Cauchy continuous map into a complete space is Cauchy continuous: the
image of a Cauchy filter converges in the complete space. -/
theorem Continuous.cauchyContinuous_comp [CompleteSpace β] {e : α → β} {g : β → γ}
    (hg : Continuous g) (he : CauchyContinuous e) : CauchyContinuous (g ∘ e) := fun F hF ↦ by
  obtain ⟨b, hb⟩ := CompleteSpace.complete (he hF)
  have := hF.1
  rw [← map_map]
  exact cauchy_nhds.mono ((map_mono hb).trans (hg.tendsto b))

section Extend

variable [CompleteSpace γ] {e : α → β} {f : α → γ}

/-- Along a dense uniform inducing map, a Cauchy continuous map into a complete space has a limit
at every point.  This generalizes `uniformly_extend_exists` from uniformly continuous maps. -/
theorem CauchyContinuous.exists_tendsto_comap_nhds (hf : CauchyContinuous f)
    (he : IsUniformInducing e) (hd : DenseRange e) (b : β) :
    ∃ c, Tendsto f (comap e (𝓝 b)) (𝓝 c) := by
  have := (he.isDenseInducing hd).comap_nhds_neBot b
  exact CompleteSpace.complete (hf (cauchy_nhds.comap he.comap_uniformity.le))

variable [T0Space γ]

/-- Along a dense uniform inducing map, a Cauchy continuous map into a complete separated space
has a continuous extension.  Compare `IsDenseInducing.continuous_extend_of_cauchy`, which assumes
the Cauchy property of the images of the neighborhood filters directly. -/
theorem CauchyContinuous.continuous_extend (hf : CauchyContinuous f) (he : IsUniformInducing e)
    (hd : DenseRange e) : Continuous ((he.isDenseInducing hd).extend f) :=
  (he.isDenseInducing hd).continuous_extend (hf.exists_tendsto_comap_nhds he hd)

/-- The continuous extension of a Cauchy continuous map along a dense uniform inducing map agrees
with the map. -/
theorem CauchyContinuous.extend_eq (hf : CauchyContinuous f) (he : IsUniformInducing e)
    (hd : DenseRange e) (a : α) : (he.isDenseInducing hd).extend f (e a) = f a :=
  (he.isDenseInducing hd).extend_eq' (hf.exists_tendsto_comap_nhds he hd) a

end Extend
