/-
Copyright (c) 2019 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
module

public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.UniformRing

/-!
# Completion of topological fields

The goal of this file is to prove the main part of Proposition 7 of Bourbaki GT III 6.8 :

The completion `hat K` of a Hausdorff topological field is a field if the image under
the mapping `x ↦ x⁻¹` of every Cauchy filter (with respect to the additive uniform structure)
which does not have a cluster point at `0` is a Cauchy filter
(with respect to the additive uniform structure).

Bourbaki does not give any detail here, he refers to the general discussion of extending
functions defined on a dense subset with values in a complete Hausdorff space. In particular
the subtlety about clustering at zero is totally left to readers.

Note that the separated completion of a non-separated topological field is the zero ring, hence
the separation assumption is needed. Indeed the kernel of the completion map is the closure of
zero which is an ideal. Hence it's either zero (and the field is separated) or the full field,
which implies one is sent to zero and the completion ring is trivial.

The main definition is `CompletableTopField` which packages the assumptions as a Prop-valued
type class and the main results are the instances `UniformSpace.Completion.instField` and
`IsTopologicalDivisionRing (UniformSpace.Completion K)`.

Inversion is defined on the nonzero elements only. A filter without a cluster point at `0` is
supported on them, so its image under `x ↦ x⁻¹` is the image of its restriction to the
invertible elements. The inverse of a nonzero element `x` of the completion is the limit of the
inverses of the nonzero elements of `K` near `x`, and inversion is continuous on the nonzero
elements of the completion (`ContinuousInv₀`). These constructions use the topological ring
structure of `K`, but not the continuity of inversion on `K`.
-/

@[expose] public section

noncomputable section

open uniformity Topology

open Set UniformSpace UniformSpace.Completion Filter

variable (K : Type*) [Field K] [UniformSpace K]

local notation "hat" => Completion

/-- A topological field is completable if it is separated and the image under
the mapping x ↦ x⁻¹ of every Cauchy filter (with respect to the additive uniform structure)
which does not have a cluster point at 0 is a Cauchy filter
(with respect to the additive uniform structure). This ensures the completion is
a field.

A filter without a cluster point at `0` is supported on the invertible elements, where the
inverse is defined, so its image under the inverse is the image of its restriction
`comap Subtype.val F` to the invertible elements. -/
class CompletableTopField : Prop extends T0Space K where
  nice : ∀ F : Filter K, Cauchy F → 𝓝 0 ⊓ F = ⊥ →
    Cauchy (map (fun x : {x : K | IsUnit x} ↦ Checked.inv (x : K) x.2)
      (Filter.comap Subtype.val F))

variable {K} in
/-- A filter without a cluster point at `0` is supported on the invertible elements. -/
private theorem setOf_isUnit_mem_of_inf_eq_bot {F : Filter K} (hF : 𝓝 0 ⊓ F = ⊥) :
    {x : K | IsUnit x} ∈ F := by
  obtain ⟨U, hU, V, hV, hUV⟩ := inf_eq_bot_iff.mp hF
  refine mem_of_superset hV fun x hx ↦ Ne.isUnit fun h ↦ ?_
  have h0 : (0 : K) ∈ U ∩ V := ⟨mem_of_mem_nhds hU, h ▸ hx⟩
  rwa [hUV] at h0

namespace UniformSpace

namespace Completion

instance (priority := 100) [T0Space K] : Nontrivial (hat K) :=
  (isUniformEmbedding_coe K).injective.nontrivial

variable {K}

/-- The inverses of the invertible elements of `K` near a nonzero element of the completion
converge in the completion. -/
private theorem exists_tendsto_coe_inv [CompletableTopField K] {x : hat K} (hx : x ≠ 0) :
    ∃ y : hat K, Tendsto (fun z : {z : K | IsUnit z} ↦ ((Checked.inv (z : K) z.2 : K) : hat K))
      (Filter.comap Subtype.val (Filter.comap (↑) (𝓝 x))) (𝓝 y) := by
  have hF : Cauchy (Filter.comap ((↑) : K → hat K) (𝓝 x)) := by
    have := isDenseInducing_coe.comap_nhds_neBot x
    apply cauchy_nhds.comap
    rw [Completion.comap_coe_eq_uniformity]
  have h0 : 𝓝 0 ⊓ Filter.comap ((↑) : K → hat K) (𝓝 x) = ⊥ := by
    have eq_bot : 𝓝 (0 : hat K) ⊓ 𝓝 x = ⊥ := by
      by_contra h
      exact hx (eq_of_nhds_neBot <| neBot_iff.mpr h).symm
    rw [isDenseInducing_coe.nhds_eq_comap (0 : K), ← Filter.comap_inf]
    norm_cast
    rw [eq_bot]
    exact comap_bot
  obtain ⟨y, hy⟩ :=
    CompleteSpace.complete ((CompletableTopField.nice _ hF h0).map (uniformContinuous_coe K))
  exact ⟨y, by rwa [Filter.map_map] at hy⟩

section Ring

variable [IsTopologicalRing K] [IsUniformAddGroup K]

/-- The inverse of the image of an element of a separated field is the image of its inverse. The
completion is then nontrivial, so an element whose image is invertible is nonzero. -/
@[norm_cast]
theorem coe_inv [T0Space K] (x : K) {hx : IsUnit (x : hat K)} :
    (x : hat K)⁻¹ =
      ((Checked.inv x (Ne.isUnit fun h ↦ hx.ne_zero (h ▸ coe_zero)) : K) : hat K) :=
  inv_eq_of_mul_eq_one_right₀ (by rw [← coe_mul, mul_inv_cancel₀, coe_one])

/-- A limit of the inverses of the invertible elements of `K` near a nonzero element `x` of the
completion is an inverse of `x`. -/
private theorem mul_eq_one_of_tendsto {x y : hat K} (hx : x ≠ 0)
    (hy : Tendsto (fun z : {z : K | IsUnit z} ↦ ((Checked.inv (z : K) z.2 : K) : hat K))
      (Filter.comap Subtype.val (Filter.comap (↑) (𝓝 x))) (𝓝 y)) :
    x * y = 1 := by
  have : NeBot (Filter.comap (Subtype.val : {z : K | IsUnit z} → K)
      (Filter.comap ((↑) : K → hat K) (𝓝 x))) := by
    refine (isDenseInducing_coe.comap_nhds_neBot x).comap_of_range_mem ?_
    rw [Subtype.range_val]
    refine Filter.mem_comap.mpr
      ⟨{0}ᶜ, compl_singleton_mem_nhds hx, fun z hz ↦ Ne.isUnit fun h ↦ hz ?_⟩
    rw [mem_singleton_iff, h, coe_zero]
  have hval : Tendsto (fun z : {z : K | IsUnit z} ↦ ((z : K) : hat K))
      (Filter.comap Subtype.val (Filter.comap (↑) (𝓝 x))) (𝓝 x) :=
    (tendsto_comap (f := ((↑) : K → hat K))).comp tendsto_comap
  have hone : Tendsto (fun _ : {z : K | IsUnit z} ↦ (1 : hat K))
      (Filter.comap Subtype.val (Filter.comap (↑) (𝓝 x))) (𝓝 (x * y)) :=
    (hval.mul hy).congr fun z ↦ by rw [← coe_mul, mul_inv_cancel₀, coe_one]
  exact tendsto_nhds_unique hone tendsto_const_nhds

variable [CompletableTopField K]

/-- The inverse of an invertible element `x` of the completion is the limit of the inverses of
the invertible elements of `K` near `x`. -/
private theorem tendsto_coe_inv {x : hat K} (hx : IsUnit x) :
    Tendsto (fun z : {z : K | IsUnit z} ↦ ((Checked.inv (z : K) z.2 : K) : hat K))
      (Filter.comap Subtype.val (Filter.comap (↑) (𝓝 x))) (𝓝 x⁻¹) := by
  obtain ⟨y, hy⟩ := exists_tendsto_coe_inv hx.ne_zero
  rwa [inv_eq_of_mul_eq_one_right₀ (mul_eq_one_of_tendsto hx.ne_zero hy)]

/-- The completion of a completable topological field is a field. The inverse of a nonzero
element `x` is the limit of the inverses of the nonzero elements of `K` near `x`. -/
instance instField : Field (hat K) where
  isUnit_of_ne_zero {x} hx := by
    obtain ⟨y, hy⟩ := exists_tendsto_coe_inv hx
    exact isUnit_iff_exists_inv.mpr ⟨y, mul_eq_one_of_tendsto hx hy⟩

/-- Inversion on the completion is continuous on the invertible elements: it is the extension by
continuity of inversion on the invertible elements of `K`, which are dense among them. -/
instance : ContinuousInv₀ (hat K) where
  continuous_inv := by
    let j : {z : K | IsUnit z} → {x : hat K | IsUnit x} := fun z ↦ ⟨z, z.2.map coeRingHom⟩
    have hrange : range j = Subtype.val ⁻¹' range ((↑) : K → hat K) := by
      ext u
      refine ⟨fun ⟨z, hz⟩ ↦ ⟨z, congrArg Subtype.val hz⟩, fun ⟨z, hz⟩ ↦ ?_⟩
      refine ⟨⟨z, Ne.isUnit fun h ↦ u.2.ne_zero ?_⟩, Subtype.ext hz⟩
      rw [← hz, h, coe_zero]
    have hopen : IsOpen {x : hat K | IsUnit x} := by
      simpa only [isUnit_iff_ne_zero] using isOpen_ne
    have hj : IsDenseInducing j :=
      ⟨IsInducing.subtypeVal.of_comp_iff.mp
          ((isUniformInducing_coe K).isInducing.comp IsInducing.subtypeVal),
        by rw [DenseRange, hrange]; exact denseRange_coe.preimage hopen.isOpenMap_subtype_val⟩
    have h (u : {x : hat K | IsUnit x}) :
        Tendsto (fun z : {z : K | IsUnit z} ↦ ((Checked.inv (z : K) z.2 : K) : hat K))
          (Filter.comap j (𝓝 u)) (𝓝 (Units.val (u.2.unit⁻¹) : hat K)) := by
      have := tendsto_coe_inv u.2
      rw [Filter.comap_comap] at this
      rwa [nhds_subtype, Filter.comap_comap]
    have heq : (fun u : {x : hat K | IsUnit x} ↦ (Units.val (u.2.unit⁻¹) : hat K)) =
        hj.extend fun z ↦ ((Checked.inv (z : K) z.2 : K) : hat K) :=
      funext fun u ↦ (hj.extend_eq_of_tendsto (h u)).symm
    change Continuous fun u : {x : hat K | IsUnit x} ↦ (Units.val (u.2.unit⁻¹) : hat K)
    rw [heq]
    exact hj.continuous_extend fun u ↦ ⟨_, h u⟩

instance : IsTopologicalDivisionRing (hat K) :=
  { Completion.topologicalRing with }

end Ring

end Completion

end UniformSpace

section UniformInducing

variable {α β : Type*} [Field β] [b : UniformSpace β] [CompletableTopField β]
  [Field α]

/-- The pullback of a completable topological field along a uniform inducing
ring homomorphism is a completable topological field. -/
theorem IsUniformInducing.completableTopField
    [UniformSpace α] [T0Space α]
    {f : α →+* β} (hf : IsUniformInducing f) :
    CompletableTopField α := by
  refine CompletableTopField.mk (fun F F_cau inf_F => ?_)
  have inf_F' : 𝓝 0 ⊓ map f F = ⊥ := by
    rw [← Filter.push_pull', ← map_zero f, ← hf.isInducing.nhds_eq_comap, inf_F,
      Filter.map_bot]
  have : NeBot (Filter.comap Subtype.val F) := F_cau.1.comap_of_range_mem <| by
    rw [Subtype.range_val]
    exact setOf_isUnit_mem_of_inf_eq_bot inf_F
  -- `f` maps the invertible elements of `α` to invertible elements of `β`, and commutes with
  -- inversion there.
  let k : {x : α | IsUnit x} → {y : β | IsUnit y} := fun x ↦ ⟨f x, x.2.map f⟩
  have hk : Tendsto k (Filter.comap Subtype.val F) (Filter.comap Subtype.val (map f F)) :=
    tendsto_comap_iff.mpr (tendsto_map.comp tendsto_comap)
  have hinv : (f ∘ fun x : {x : α | IsUnit x} ↦ Checked.inv (x : α) x.2) =
      (fun y : {y : β | IsUnit y} ↦ Checked.inv (y : β) y.2) ∘ k :=
    funext fun x ↦ map_inv₀ f (x : α)
  rw [← hf.cauchy_map_iff, Filter.map_map, hinv, ← Filter.map_map]
  exact (CompletableTopField.nice _ (F_cau.map hf.uniformContinuous) inf_F').mono'
    ((this.map _).map _) (map_mono hk)

end UniformInducing

variable (L : Type*) [Field L] [UniformSpace L] [CompletableTopField L]

instance Subfield.completableTopField (K : Subfield L) : CompletableTopField K :=
  IsUniformInducing.completableTopField (f := K.subtype)
    isUniformEmbedding_subtype_val.isUniformInducing

instance (priority := 100) completableTopField_of_complete (L : Type*) [Field L] [UniformSpace L]
    [IsTopologicalDivisionRing L] [T0Space L] [CompleteSpace L] : CompletableTopField L where
  nice F cau_F hF := by
    have : NeBot F := cau_F.1
    rcases CompleteSpace.complete cau_F with ⟨x, hx⟩
    have hx' : x ≠ 0 := by
      rintro rfl
      rw [inf_eq_right.mpr hx] at hF
      exact cau_F.1.ne hF
    have : NeBot (Filter.comap Subtype.val F) := this.comap_of_range_mem <| by
      rw [Subtype.range_val]
      exact setOf_isUnit_mem_of_inf_eq_bot hF
    refine Filter.Tendsto.cauchy_map
      ((continuousAt_inv₀ (⟨x, hx'.isUnit⟩ : {x : L | IsUnit x})).tendsto.mono_left ?_)
    rw [nhds_subtype]
    exact Filter.comap_mono hx
