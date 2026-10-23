/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Rat
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Topology.MetricSpace.DilationEquiv
import Mathlib.Analysis.Normed.MulAction

/-!
# Normed fields

In this file we continue building the theory of normed division rings and fields.

Some useful results that relate the topology of the normed field to the discrete topology include:
* `discreteTopology_or_nontriviallyNormedField`
* `discreteTopology_of_bddAbove_range_norm`

-/

@[expose] public section

-- Guard against import creep.
assert_not_exists RestrictScalars

variable {α β ι : Type*}

open Filter Bornology Metric
open scoped Topology NNReal Pointwise Uniformity

section NormedDivisionRing

variable [NormedDivisionRing α]

/-- Multiplication by a nonzero element `a` on the left
as a `DilationEquiv` of a normed division ring. -/
@[simps!]
def DilationEquiv.mulLeft (a : α) (ha : a ≠ 0) : α ≃ᵈ α where
  __ := Dilation.mulLeft a ha
  toEquiv := Equiv.mulLeft₀ a ha

/-- Multiplication by a nonzero element `a` on the right
as a `DilationEquiv` of a normed division ring. -/
@[simps!]
def DilationEquiv.mulRight (a : α) (ha : a ≠ 0) : α ≃ᵈ α where
  __ := Dilation.mulRight a ha
  toEquiv := Equiv.mulRight₀ a ha

namespace Filter

@[simp]
lemma map_mul_left_cobounded {a : α} (ha : a ≠ 0) :
    map (a * ·) (cobounded α) = cobounded α :=
  DilationEquiv.map_cobounded (DilationEquiv.mulLeft a ha)

@[simp]
lemma map_mul_right_cobounded {a : α} (ha : a ≠ 0) :
    map (· * a) (cobounded α) = cobounded α :=
  DilationEquiv.map_cobounded (DilationEquiv.mulRight a ha)

/-- Multiplication on the left by a nonzero element of a normed division ring tends to infinity at
infinity. -/
theorem tendsto_mul_left_cobounded {a : α} (ha : a ≠ 0) :
    Tendsto (a * ·) (cobounded α) (cobounded α) :=
  (map_mul_left_cobounded ha).le

/-- Multiplication on the right by a nonzero element of a normed division ring tends to infinity at
infinity. -/
theorem tendsto_mul_right_cobounded {a : α} (ha : a ≠ 0) :
    Tendsto (· * a) (cobounded α) (cobounded α) :=
  (map_mul_right_cobounded ha).le

@[simp]
lemma inv_cobounded₀ :
    map (fun u : αˣ ↦ (↑u⁻¹ : α))
      (comap (fun u : αˣ ↦ (u : α)) (cobounded α)) = 𝓝[≠] 0 := by
  have hb : (cobounded α).HasBasis
      (fun u : ℝˣ ↦ 0 < (u : ℝ)) (fun u ↦ {x | (u : ℝ) < ‖x‖}) :=
    (atTop_basis_Ioi' (0 : ℝ)).cobounded_of_norm.to_hasBasis
      (fun a ha ↦ ⟨Units.mk0 a ha.ne', ha, Subset.rfl⟩)
      (fun u hu ↦ ⟨(u : ℝ), hu, Subset.rfl⟩)
  have hn : (𝓝[≠] (0 : α)).HasBasis
      (fun u : ℝˣ ↦ 0 < (u : ℝ)) (fun u ↦ {x | 0 < ‖x‖ ∧ ‖x‖ < (u : ℝ)}) := by
    rw [← comap_norm_nhdsGT_zero]
    exact ((nhdsGT_basis (0 : ℝ)).comap norm).to_hasBasis
      (fun a ha ↦ ⟨Units.mk0 a ha.ne', ha, Subset.rfl⟩)
      (fun u hu ↦ ⟨(u : ℝ), hu, Subset.rfl⟩)
  apply (((hb.comap (fun u : αˣ ↦ (u : α))).map
    (fun u : αˣ ↦ (↑u⁻¹ : α))).comp_surjective
      (inv_surjective : Function.Surjective (Inv.inv : ℝˣ → ℝˣ))).eq_of_same_basis
  apply hn.congr
  · intro u
    exact (Units.inv_pos u).symm
  · intro u hu
    ext y
    symm
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨norm_pos_iff.mpr (v⁻¹).ne_zero, ?_⟩
      simpa only [inv_inv] using
        (Units.inv_lt_inv (u := Units.map normHom.toMonoidHom v) (v := u⁻¹)
          (norm_pos_iff.mpr v.ne_zero) ((Units.inv_pos u).mpr hu)).mpr hv
    · intro hy
      let v := Units.mk0 y (norm_pos_iff.mp hy.1)
      refine ⟨v⁻¹, ?_, by simp [v]⟩
      exact (Units.inv_lt_inv (u := u) (v := Units.map normHom.toMonoidHom v)
        hu hy.1).mpr hy.2

@[simp]
lemma inv_nhdsNE_zero :
    map (fun u : αˣ ↦ (↑u⁻¹ : α))
      (comap (fun u : αˣ ↦ (u : α)) (𝓝[≠] 0)) = cobounded α := by
  have hb : (cobounded α).HasBasis
      (fun u : ℝˣ ↦ 0 < (u : ℝ)) (fun u ↦ {x | (u : ℝ) < ‖x‖}) :=
    (atTop_basis_Ioi' (0 : ℝ)).cobounded_of_norm.to_hasBasis
      (fun a ha ↦ ⟨Units.mk0 a ha.ne', ha, Subset.rfl⟩)
      (fun u hu ↦ ⟨(u : ℝ), hu, Subset.rfl⟩)
  have hn : (𝓝[≠] (0 : α)).HasBasis
      (fun u : ℝˣ ↦ 0 < (u : ℝ)) (fun u ↦ {x | 0 < ‖x‖ ∧ ‖x‖ < (u : ℝ)}) := by
    rw [← comap_norm_nhdsGT_zero]
    exact ((nhdsGT_basis (0 : ℝ)).comap norm).to_hasBasis
      (fun a ha ↦ ⟨Units.mk0 a ha.ne', ha, Subset.rfl⟩)
      (fun u hu ↦ ⟨(u : ℝ), hu, Subset.rfl⟩)
  apply (((hn.comap (fun u : αˣ ↦ (u : α))).map
    (fun u : αˣ ↦ (↑u⁻¹ : α))).comp_surjective
      (inv_surjective : Function.Surjective (Inv.inv : ℝˣ → ℝˣ))).eq_of_same_basis
  apply hb.congr
  · intro u
    exact (Units.inv_pos u).symm
  · intro u hu
    ext y
    symm
    constructor
    · rintro ⟨v, hv, rfl⟩
      simpa only [inv_inv] using
        (Units.inv_lt_inv (u := u⁻¹) (v := Units.map normHom.toMonoidHom v)
          ((Units.inv_pos u).mpr hu) hv.1).mpr hv.2
    · intro hy
      have hypos : 0 < ‖y‖ := hu.trans hy
      let v := Units.mk0 y (norm_pos_iff.mp hypos)
      refine ⟨v⁻¹, ⟨norm_pos_iff.mpr (v⁻¹).ne_zero, ?_⟩, by simp [v]⟩
      exact (Units.inv_lt_inv (u := Units.map normHom.toMonoidHom v) (v := u)
        hypos hu).mpr hy

lemma tendsto_inv₀_cobounded' :
    Tendsto (fun u : αˣ ↦ (↑u⁻¹ : α))
      (comap (fun u : αˣ ↦ (u : α)) (cobounded α)) (𝓝[≠] 0) :=
  inv_cobounded₀.le

theorem tendsto_inv₀_cobounded :
    Tendsto (fun u : αˣ ↦ (↑u⁻¹ : α))
      (comap (fun u : αˣ ↦ (u : α)) (cobounded α)) (𝓝 0) :=
  tendsto_inv₀_cobounded'.mono_right inf_le_left

lemma tendsto_inv₀_nhdsNE_zero :
    Tendsto (fun u : αˣ ↦ (↑u⁻¹ : α))
      (comap (fun u : αˣ ↦ (u : α)) (𝓝[≠] 0)) (cobounded α) :=
  inv_nhdsNE_zero.le

end Filter

/-- On an invertibility-domain subset bounded away from zero in the ambient norm,
inversion is uniformly continuous for the ambient subspace uniformity. -/
theorem uniformContinuousOn_inv₀ {s : Set {x : α | IsUnit x}}
    (hs : (Subtype.val '' s)ᶜ ∈ 𝓝 0) :
    UniformContinuousOn (fun x : {x : α | IsUnit x} ↦ (↑x.property.unit⁻¹ : α)) s := by
  rw [Metric.uniformContinuousOn_iff_le]
  intro ε hε
  rcases NormedAddGroup.nhds_zero_basis_norm_lt.mem_iff.mp hs with ⟨r, hr₀, hr⟩
  simp only [Set.subset_compl_comm (t := Subtype.val '' s), Set.compl_ofPred, not_lt] at hr
  refine ⟨ε * r ^ 2, by positivity, fun x hx y hy hxy ↦ ?_⟩
  have hxnorm : r ≤ ‖x.val‖ := hr (Set.mem_image_of_mem Subtype.val hx)
  have hynorm : r ≤ ‖y.val‖ := hr (Set.mem_image_of_mem Subtype.val hy)
  have hpos : 0 < (↑(Units.map normHom.toMonoidHom x.property.unit *
      Units.map normHom.toMonoidHom y.property.unit) : ℝ) :=
    mul_pos (hr₀.trans_le hxnorm) (hr₀.trans_le hynorm)
  rw [dist_inv_inv₀, divp_le_iff hpos]
  change dist (x : α) y ≤ ε * (‖x.val‖ * ‖y.val‖)
  exact hxy.trans (by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul hxnorm hynorm hr₀.le (norm_nonneg _)) hε.le)

theorem UniformContinuousOn.inv₀ {X : Type*} [UniformSpace X]
    {f : X → {x : α | IsUnit x}} {s : Set X}
    (hf : UniformContinuousOn (fun x ↦ (f x).val) s)
    (hf₀ : ((fun x ↦ (f x).val) '' s)ᶜ ∈ 𝓝 0) :
    UniformContinuousOn (fun x ↦ (↑(f x).property.unit⁻¹ : α)) s := by
  have hsub : UniformContinuousOn f s := by
    rw [uniformContinuousOn_iff_restrict]
    exact hf.restrict.subtype_mk (fun x ↦ (f x.val).property)
  apply (uniformContinuousOn_inv₀ (s := f '' s) ?_).comp hsub (Set.mapsTo_image f s)
  simpa only [Set.image_image, Function.comp_def] using hf₀

theorem UniformContinuous.inv₀ {X : Type*} [UniformSpace X]
    {f : X → {x : α | IsUnit x}} (hf : UniformContinuous (fun x ↦ (f x).val))
    (hf₀ : (Set.range (fun x ↦ (f x).val))ᶜ ∈ 𝓝 0) :
    UniformContinuous (fun x ↦ (↑(f x).property.unit⁻¹ : α)) := by
  rw [← uniformContinuousOn_univ]
  exact hf.uniformContinuousOn.inv₀ (by simpa only [Set.image_univ] using hf₀)

/-- Locally uniform inversion on the actual domains. The local range-disjointness
hypothesis supplies a positive lower bound for the limit and hence eventual coverage by the
invertibility domains of the approximating family. -/
theorem TendstoLocallyUniformlyOn.inv₀_of_disjoint {X ι : Type*} [TopologicalSpace X]
    {s : Set X} {F : ι → X → α} {f : X → α} {l : Filter ι}
    (hF : TendstoLocallyUniformlyOn F f l s)
    (hf : ∀ x ∈ s, Disjoint (map f (𝓝[s] x)) (𝓝 0)) :
    TendstoLocallyUniformlyOn (fun i (y : {y : {x : X | IsUnit (f x)} | IsUnit (F i y.val)}) ↦
        (↑y.property.unit⁻¹ : α))
      (fun y : {x : X | IsUnit (f x)} ↦ (↑y.property.unit⁻¹ : α)) l (Subtype.val ⁻¹' s) (fun i ↦ Function.Embedding.subtype (fun y : {x : X | IsUnit (f x)} ↦ IsUnit (F i y.val))) := by
  intro u hu x hx
  obtain ⟨ε, hε, hεu⟩ := Metric.mem_uniformity_dist.mp hu
  rcases basis_sets _ |>.map _ |>.disjoint_iff nhds_basis_ball |>.mp (hf x.val hx) with
    ⟨U, hUx, r, hr₀, hr⟩
  have hfbound (y : X) (hy : y ∈ U) : r ≤ ‖f y‖ := by
    have hnot := Set.disjoint_left.mp hr (Set.mem_image_of_mem f hy)
    simpa only [Metric.mem_ball, dist_zero_right, not_lt] using hnot
  have hδ : 0 < min (r / 2) (ε * (r / 2) ^ 2) := by positivity
  obtain ⟨v, hv, H⟩ := (tendstoLocallyUniformlyOn_iff.mp hF)
    {q : α × α | dist q.1 q.2 < min (r / 2) (ε * (r / 2) ^ 2)}
    (Metric.dist_mem_uniformity hδ) x.val hx
  have hval : Tendsto (Subtype.val : {x : X | IsUnit (f x)} → X)
      (𝓝[Subtype.val ⁻¹' s] x) (𝓝[s] x.val) :=
    continuous_subtype_val.continuousWithinAt.tendsto_nhdsWithin (fun _ hy => hy)
  refine ⟨Subtype.val ⁻¹' (U ∩ v), hval (inter_mem hUx hv), H.mono fun i hi => ?_⟩
  have hFbound (y : {x : X | IsUnit (f x)}) (hy : y.val ∈ U ∩ v) :
      r / 2 < ‖F i y.val‖ := by
    have hd : dist (f y.val) (F i y.val) < r / 2 :=
      (hi y.val hy.2).trans_le (min_le_left _ _)
    have hb := hfbound y.val hy.1
    rw [dist_eq_norm] at hd
    linarith [norm_sub_norm_le (f y.val) (F i y.val)]
  constructor
  · intro y hy
    exact ⟨⟨y, isUnit_iff_ne_zero.mpr (norm_pos_iff.mp ((half_pos hr₀).trans (hFbound y hy)))⟩, rfl⟩
  · intro y hy
    apply hεu
    change dist (↑y.val.property.unit⁻¹ : α) ↑y.property.unit⁻¹ < ε
    have hfy : r ≤ ‖f y.val.val‖ := hfbound y.val.val hy.1
    have hFy : r / 2 < ‖F i y.val.val‖ := hFbound y.val hy
    have hp : 0 < (↑(Units.map normHom.toMonoidHom y.val.property.unit *
        Units.map normHom.toMonoidHom y.property.unit) : ℝ) :=
      mul_pos (hr₀.trans_le hfy) ((half_pos hr₀).trans hFy)
    rw [dist_inv_inv₀, divp_lt_iff hp]
    change dist (f y.val.val) (F i y.val.val) < ε * (‖f y.val.val‖ * ‖F i y.val.val‖)
    apply ((hi y.val.val hy.2).trans_le (min_le_right _ _)).trans_le
    apply mul_le_mul_of_nonneg_left _ hε.le
    rw [pow_two]
    exact mul_le_mul ((half_le_self hr₀.le).trans hfy) hFy.le (half_pos hr₀).le (norm_nonneg _)

theorem TendstoLocallyUniformly.inv₀_of_disjoint {X ι : Type*} [TopologicalSpace X]
    {F : ι → X → α} {f : X → α} {l : Filter ι}
    (hF : TendstoLocallyUniformly F f l)
    (hf : ∀ x, Disjoint (map f (𝓝 x)) (𝓝 0)) :
    TendstoLocallyUniformly (fun i (y : {y : {x : X | IsUnit (f x)} | IsUnit (F i y.val)}) ↦
        (↑y.property.unit⁻¹ : α))
      (fun y : {x : X | IsUnit (f x)} ↦ (↑y.property.unit⁻¹ : α)) l (fun i ↦ Function.Embedding.subtype (fun y : {x : X | IsUnit (f x)} ↦ IsUnit (F i y.val))) := by
  rw [← tendstoLocallyUniformlyOn_univ]
  simpa only [Set.preimage_univ] using hF.tendstoLocallyUniformlyOn.inv₀_of_disjoint
    (s := Set.univ) (by simpa only [nhdsWithin_univ] using fun x _ => hf x)

theorem TendstoLocallyUniformlyOn.inv₀ {X ι : Type*} [TopologicalSpace X]
    {s : Set X} {F : ι → X → α} {f : X → α} {l : Filter ι}
    (hF : TendstoLocallyUniformlyOn F f l s) (hf : ContinuousOn f s)
    (hf₀ : ∀ x ∈ s, f x ≠ 0) :
    TendstoLocallyUniformlyOn (fun i (y : {y : {x : X | IsUnit (f x)} | IsUnit (F i y.val)}) ↦
        (↑y.property.unit⁻¹ : α))
      (fun y : {x : X | IsUnit (f x)} ↦ (↑y.property.unit⁻¹ : α)) l (Subtype.val ⁻¹' s) (fun i ↦ Function.Embedding.subtype (fun y : {x : X | IsUnit (f x)} ↦ IsUnit (F i y.val))) :=
  hF.inv₀_of_disjoint fun x hx ↦ disjoint_nhds_nhds.2 (hf₀ x hx) |>.mono_left (hf x hx)

theorem TendstoLocallyUniformly.inv₀ {X ι : Type*} [TopologicalSpace X]
    {F : ι → X → α} {f : X → α} {l : Filter ι}
    (hF : TendstoLocallyUniformly F f l) (hf : Continuous f) (hf₀ : ∀ x, f x ≠ 0) :
    TendstoLocallyUniformly (fun i (y : {y : {x : X | IsUnit (f x)} | IsUnit (F i y.val)}) ↦
        (↑y.property.unit⁻¹ : α))
      (fun y : {x : X | IsUnit (f x)} ↦ (↑y.property.unit⁻¹ : α)) l (fun i ↦ Function.Embedding.subtype (fun y : {x : X | IsUnit (f x)} ↦ IsUnit (F i y.val))) :=
  hF.inv₀_of_disjoint fun x ↦ disjoint_nhds_nhds.2 (hf₀ x) |>.mono_left (hf.tendsto x)

-- see Note [lower instance priority]
instance (priority := 100) NormedDivisionRing.to_continuousInv₀ : ContinuousInv₀ α where
  continuous_inv := by
    rw [continuous_iff_continuousAt]
    intro x
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hn := (continuous_subtype_val.tendsto x).norm
    have hi : Tendsto
        (fun y : {y : α | IsUnit y} ↦ ‖(↑y.property.unit⁻¹ : α)‖)
        (𝓝 x) (𝓝 ‖(↑x.property.unit⁻¹ : α)‖) := by
      simpa only [IsUnit.unit_of_val_units, Units.coe_map_inv] using
        hn.inv₀ (fun y ↦ (Units.map normHom.toMonoidHom y.property.unit).isUnit)
          (Units.map normHom.toMonoidHom x.property.unit).isUnit
    have hs := ((continuous_subtype_val.tendsto x).const_sub x.val).norm
    simpa only [Units.inv_sub_inv', norm_mul, sub_self, norm_zero, mul_zero, zero_mul] using
      (hi.mul hs).mul_const ‖(↑x.property.unit⁻¹ : α)‖

theorem TendstoLocallyUniformlyOn.div₀ {X ι : Type*} [TopologicalSpace X]
    {s : Set X} {F G : ι → X → α} {f g : X → α} {l : Filter ι}
    (hF : TendstoLocallyUniformlyOn F f l s) (hG : TendstoLocallyUniformlyOn G g l s)
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) (hg₀ : ∀ x ∈ s, g x ≠ 0) :
    TendstoLocallyUniformlyOn (fun i (y : {y : {x : X | IsUnit (g x)} | IsUnit (G i y.val)}) ↦
        F i y.val.val /ₚ y.property.unit)
      (fun y : {x : X | IsUnit (g x)} ↦ f y.val /ₚ y.property.unit) l (Subtype.val ⁻¹' s) (fun i ↦ Function.Embedding.subtype (fun y : {x : X | IsUnit (g x)} ↦ IsUnit (G i y.val))) := by
  rw [tendstoLocallyUniformlyOn_iff_domain]
  intro x hx
  have hinv := tendstoLocallyUniformlyOn_iff_domain.mp (hG.inv₀ hg hg₀) x hx
  refine ⟨hinv.1, ?_⟩
  let D (i : ι) := {y : {x : X | IsUnit (g x)} | IsUnit (G i y.val)}
  let L := comap (fun q : Σ i, D i ↦ (q.1, q.2.val))
    (l ×ˢ 𝓝[Subtype.val ⁻¹' s] x)
  have hval : Tendsto (Subtype.val : {x : X | IsUnit (g x)} → X)
      (𝓝[Subtype.val ⁻¹' s] x) (𝓝[s] x.val) :=
    continuous_subtype_val.continuousWithinAt.tendsto_nhdsWithin (fun _ hy => hy)
  have hmap : Tendsto (fun q : Σ i, D i ↦ (q.1, q.2.val.val)) L (l ×ˢ 𝓝[s] x.val) := by
    simpa only [Function.comp_def, Prod.map_apply, id_eq] using
      (tendsto_id.prodMap hval).comp (tendsto_comap
        (f := fun q : Σ i, D i ↦ (q.1, q.2.val)))
  have hFjoint : Tendsto (fun q : ι × X ↦ F q.1 q.2) (l ×ˢ 𝓝[s] x.val) (𝓝 (f x.val)) :=
    (hF.comp_tendsto tendsto_fst).tendsto_comp (hf x.val hx) hx tendsto_snd
  have hGjoint : Tendsto (fun q : ι × X ↦ G q.1 q.2) (l ×ˢ 𝓝[s] x.val) (𝓝 (g x.val)) :=
    (hG.comp_tendsto tendsto_fst).tendsto_comp (hg x.val hx) hx tendsto_snd
  have hfamily := (hFjoint.comp hmap).div (hGjoint.comp hmap)
    (fun q : Σ i, D i ↦ q.2.property) x.property
  have hlimit := ((hf x.val hx).tendsto.comp (tendsto_snd.comp hmap)).div
    ((hg x.val hx).tendsto.comp (tendsto_snd.comp hmap))
    (fun q : Σ i, D i ↦ q.2.val.property) x.property
  exact (hlimit.prodMk_nhds hfamily).mono_right (nhds_le_uniformity _)

theorem TendstoLocallyUniformly.div₀ {X ι : Type*} [TopologicalSpace X]
    {F G : ι → X → α} {f g : X → α} {l : Filter ι}
    (hF : TendstoLocallyUniformly F f l) (hG : TendstoLocallyUniformly G g l)
    (hf : Continuous f) (hg : Continuous g) (hg₀ : ∀ x, g x ≠ 0) :
    TendstoLocallyUniformly (fun i (y : {y : {x : X | IsUnit (g x)} | IsUnit (G i y.val)}) ↦
        F i y.val.val /ₚ y.property.unit)
      (fun y : {x : X | IsUnit (g x)} ↦ f y.val /ₚ y.property.unit) l (fun i ↦ Function.Embedding.subtype (fun y : {x : X | IsUnit (g x)} ↦ IsUnit (G i y.val))) := by
  rw [← tendstoLocallyUniformlyOn_univ]
  simpa only [Set.preimage_univ] using
    hF.tendstoLocallyUniformlyOn.div₀ hG.tendstoLocallyUniformlyOn hf.continuousOn hg.continuousOn
      (s := Set.univ) (fun x _ => hg₀ x)

-- see Note [lower instance priority]
/-- A normed division ring is a topological division ring. -/
instance (priority := 100) NormedDivisionRing.to_isTopologicalDivisionRing :
    IsTopologicalDivisionRing α where

lemma tendsto_norm_inv_nhdsNE_zero_atTop :
    Tendsto (fun x : αˣ ↦ ‖(↑x⁻¹ : α)‖)
      (comap (fun u : αˣ ↦ (u : α)) (𝓝[≠] 0)) atTop :=
  tendsto_norm_cobounded_atTop.comp tendsto_inv₀_nhdsNE_zero

lemma tendsto_zpow_nhdsNE_zero_cobounded {m : ℤ} (hm : m < 0) :
    Tendsto (fun x : αˣ ↦ (↑(x ^ m) : α))
      (comap (fun u : αˣ ↦ (u : α)) (𝓝[≠] 0)) (cobounded α) := by
  obtain ⟨m, rfl⟩ := neg_surjective m
  lift m to ℕ using by lia
  simpa only [Function.comp_def, zpow_neg, zpow_natCast, ← inv_pow,
    Units.val_pow_eq_pow_val] using
    (tendsto_pow_cobounded_cobounded (by lia)).comp tendsto_inv₀_nhdsNE_zero

end NormedDivisionRing

namespace NormedField

/-- A normed field is either nontrivially normed or has a discrete topology.
In the discrete topology case, all the norms are 1, by `norm_eq_one_iff_ne_zero_of_discrete`.
The nontrivially normed field instance is provided by a subtype with a proof that the
forgetful inheritance to the existing `NormedField` instance is definitionally true.
This allows one to have the new `NontriviallyNormedField` instance without data clashes. -/
lemma discreteTopology_or_nontriviallyNormedField (𝕜 : Type*) [h : NormedField 𝕜] :
    DiscreteTopology 𝕜 ∨ Nonempty ({h' : NontriviallyNormedField 𝕜 // h'.toNormedField = h}) := by
  by_cases H : ∃ x : 𝕜, x ≠ 0 ∧ ‖x‖ ≠ 1
  · exact Or.inr ⟨(⟨NontriviallyNormedField.ofNormNeOne H, rfl⟩)⟩
  · simp_rw [discreteTopology_iff_isOpen_singleton_zero, Metric.isOpen_singleton_iff, dist_eq_norm,
             sub_zero]
    refine Or.inl ⟨1, zero_lt_one, ?_⟩
    contrapose! H
    refine H.imp ?_
    -- contextual to reuse the `a ≠ 0` hypothesis in the proof of `a ≠ 0 ∧ ‖a‖ ≠ 1`
    simp +contextual [ne_of_lt]

lemma discreteTopology_of_bddAbove_range_norm {𝕜 : Type*} [NormedField 𝕜]
    (h : BddAbove (Set.range fun k : 𝕜 ↦ ‖k‖)) :
    DiscreteTopology 𝕜 := by
  refine (NormedField.discreteTopology_or_nontriviallyNormedField _).resolve_right ?_
  rintro ⟨_, rfl⟩
  obtain ⟨x, h⟩ := h
  obtain ⟨k, hk⟩ := NormedField.exists_lt_norm 𝕜 x
  exact hk.not_ge (h (Set.mem_range_self k))

section Densely

variable (α) [DenselyNormedField α]

theorem denseRange_nnnorm : DenseRange (nnnorm : α → ℝ≥0) :=
  dense_of_exists_between fun _ _ hr =>
    let ⟨x, h⟩ := exists_lt_nnnorm_lt α hr
    ⟨‖x‖₊, ⟨x, rfl⟩, h⟩

end Densely

section NontriviallyNormedField
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℤ} {x : 𝕜}

/-- A negative integer power has no finite limit at zero on its actual domain. -/
protected lemma not_tendsto_zpow_zero (hn : n < 0) (a : 𝕜) :
    ¬ Tendsto (fun u : 𝕜ˣ ↦ (↑(u ^ n) : 𝕜))
      (comap (fun u : 𝕜ˣ ↦ (u : 𝕜)) (𝓝[≠] 0)) (𝓝 a) := by
  have hrange : Set.range (fun u : 𝕜ˣ ↦ (u : 𝕜)) ∈ 𝓝[≠] (0 : 𝕜) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact ⟨Units.mk0 y hy, rfl⟩
  haveI : NeBot (comap (fun u : 𝕜ˣ ↦ (u : 𝕜)) (𝓝[≠] (0 : 𝕜))) :=
    (inferInstance : NeBot (𝓝[≠] (0 : 𝕜))).comap_of_range_mem hrange
  exact (tendsto_zpow_nhdsNE_zero_cobounded hn).not_tendsto
    (Metric.disjoint_nhds_cobounded a).symm

/-- Inversion has no finite limit at zero; no inverse value at zero is chosen. -/
protected lemma not_tendsto_inv_zero (a : 𝕜) :
    ¬ Tendsto (fun u : 𝕜ˣ ↦ (↑u⁻¹ : 𝕜))
      (comap (fun u : 𝕜ˣ ↦ (u : 𝕜)) (𝓝[≠] 0)) (𝓝 a) := by
  simpa only [zpow_neg_one] using NormedField.not_tendsto_zpow_zero (n := -1) (by norm_num) a

end NontriviallyNormedField
end NormedField

instance Rat.instNormedField : NormedField ℚ where
  __ := instField
  __ := instNormedAddCommGroup
  norm_mul a b := by simp only [norm, Rat.cast_mul, abs_mul]

instance Rat.instDenselyNormedField : DenselyNormedField ℚ where
  lt_norm_lt r₁ r₂ h₀ hr :=
    let ⟨q, h⟩ := exists_rat_btwn hr
    ⟨q, by rwa [← Rat.norm_cast_real, Real.norm_eq_abs, abs_of_pos (h₀.trans_lt h.1)]⟩

section Complete

lemma NormedField.completeSpace_iff_isComplete_closedBall {K : Type*} [NormedField K] :
    CompleteSpace K ↔ IsComplete (Metric.closedBall 0 1 : Set K) := by
  constructor <;> intro h
  · exact Metric.isClosed_closedBall.isComplete
  rcases NormedField.discreteTopology_or_nontriviallyNormedField K with _ | ⟨_, rfl⟩
  · rwa [completeSpace_iff_isComplete_univ,
         ← NormedDivisionRing.unitClosedBall_eq_univ_of_discrete]
  refine Metric.complete_of_cauchySeq_tendsto fun u hu ↦ ?_
  obtain ⟨k, hk⟩ := hu.norm_bddAbove
  have kpos : 0 ≤ k := (_root_.norm_nonneg (u 0)).trans (hk (by simp))
  obtain ⟨x, hx⟩ := NormedField.exists_lt_norm K k
  let v := Units.mk0 x (norm_pos_iff.mp (kpos.trans_lt hx))
  have hu' : CauchySeq ((fun y ↦ y /ₚ v) ∘ u) := (uniformContinuous_div_const' v).comp_cauchySeq hu
  have hb : ∀ n, ((fun y ↦ y /ₚ v) ∘ u) n ∈ Metric.closedBall 0 1 := by
    intro
    simp only [Function.comp_apply, Metric.mem_closedBall, dist_zero_right, norm_div]
    rw [divp_le_one (kpos.trans_lt hx)]
    exact hx.le.trans' (hk (by simp))
  obtain ⟨a, -, ha'⟩ := cauchySeq_tendsto_of_isComplete h hb hu'
  refine ⟨a * x, (((continuous_mul_const x).tendsto a).comp ha').congr ?_⟩
  simp only [Function.comp_def, divp_mul_cancel]

end Complete
