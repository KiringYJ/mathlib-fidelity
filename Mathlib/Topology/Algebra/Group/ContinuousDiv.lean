/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
module

public import Mathlib.Topology.Algebra.Group.Neighborhood

/-!
# Continuous division in topological groups

Continuity, homeomorphism, and neighborhood results for division and subtraction.
-/

@[expose] public section

open Set Filter Topology

variable {G α : Type*}

section ContinuousSub

variable [TopologicalSpace G] [Sub G] [ContinuousSub G]

theorem Filter.Tendsto.sub_const {c : G} {f : α → G} {l : Filter α} (h : Tendsto f l (𝓝 c))
    (b : G) : Tendsto (f · - b) l (𝓝 (c - b)) :=
  h.sub tendsto_const_nhds

theorem Filter.Tendsto.const_sub (b : G) {c : G} {f : α → G} {l : Filter α}
    (h : Tendsto f l (𝓝 c)) : Tendsto (b - f ·) l (𝓝 (b - c)) :=
  tendsto_const_nhds.sub h

@[continuity] lemma continuous_sub_left (a : G) : Continuous (a - ·) := by fun_prop

@[continuity] lemma continuous_sub_right (a : G) : Continuous (· - a) := by fun_prop

end ContinuousSub

section ContinuousDiv

variable [TopologicalSpace G] [Group G] [ContinuousDiv G]

theorem Filter.Tendsto.div_const' {c : G} {f : α → G} {l : Filter α} (h : Tendsto f l (𝓝 c))
    (b : G) : Tendsto (f · / b) l (𝓝 (c / b)) :=
  h.div' tendsto_const_nhds

/-- Division by a fixed invertible element preserves and reflects limits. This needs only
continuity of right multiplication: in a monoid without an ambient division, the quotient by an
invertible element is multiplication by its inverse. -/
lemma Filter.tendsto_div_const_iff {G : Type*}
    [Monoid G] [TopologicalSpace G] [SeparatelyContinuousMul G]
    {b : G} {hb : IsUnit b} {c : G} {f : α → G} {l : Filter α} :
    Tendsto (fun k ↦ f k * ↑(hb.unit⁻¹)) l (𝓝 (c * ↑(hb.unit⁻¹))) ↔ Tendsto f l (𝓝 c) := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.mul_const _⟩
  simpa only [mul_assoc, hb.val_inv_mul, mul_one] using h.mul_const b

lemma Filter.tendsto_sub_const_iff {G : Type*}
    [TopologicalSpace G] [AddGroup G] [ContinuousSub G]
    (b : G) {c : G} {f : α → G} {l : Filter α} :
    Tendsto (f · - b) l (𝓝 (c - b)) ↔ Tendsto f l (𝓝 c) := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.sub_const b⟩
  simpa only [sub_neg_eq_add, sub_add_cancel] using h.sub_const (-b)

lemma Filter.tendsto_div_const_iff' {G : Type*}
    [TopologicalSpace G] [Group G] [ContinuousDiv G]
    (b : G) {c : G} {f : α → G} {l : Filter α} :
    Tendsto (f · / b) l (𝓝 (c / b)) ↔ Tendsto f l (𝓝 c) := by
  refine ⟨fun h ↦ ?_, fun h ↦ Filter.Tendsto.div_const' h b⟩
  convert! h.div_const' b⁻¹ with k <;> rw [← div_mul_eq_div_div_swap, inv_mul_cancel, div_one]

theorem Filter.Tendsto.const_div' (b : G) {c : G} {f : α → G} {l : Filter α}
    (h : Tendsto f l (𝓝 c)) : Tendsto (b / f ·) l (𝓝 (b / c)) :=
  tendsto_const_nhds.div' h

@[continuity]
lemma continuous_div_left' (a : G) : Continuous (a / ·) := by fun_prop

@[continuity]
lemma continuous_div_right' (a : G) : Continuous (· / a) := by fun_prop

end ContinuousDiv

section DivInvTopologicalGroup

variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

@[to_additive tendsto_const_sub_iff]
lemma Filter.tendsto_const_div_iff' (b : G) {c : G} {f : α → G} {l : Filter α} :
    Tendsto (fun k : α ↦ b / f k) l (𝓝 (b / c)) ↔ Tendsto f l (𝓝 c) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · convert! h.inv.mul_const b with k <;> rw [inv_div, div_mul_cancel]
  · simpa only [div_eq_mul_inv] using (tendsto_const_nhds (x := b)).mul h.inv

/-- A version of `Homeomorph.mulLeft a b⁻¹` that is defeq to `a / b`. -/
@[to_additive (attr := simps! +simpRhs)
  /-- A version of `Homeomorph.addLeft a (-b)` that is defeq to `a - b`. -/]
def Homeomorph.divLeft (x : G) : G ≃ₜ G :=
  { Equiv.divLeft x with
    continuous_toFun := by
      change Continuous fun y : G => x / y
      simp_rw [div_eq_mul_inv]
      exact continuous_const.mul continuous_inv
    continuous_invFun := continuous_inv.mul continuous_const }

@[to_additive (attr := simp)]
theorem Homeomorph.coe_divLeft (a : G) : ⇑(Homeomorph.divLeft a) = (a / ·) :=
  rfl

@[to_additive]
theorem isOpenMap_div_left (a : G) : IsOpenMap (a / ·) :=
  (Homeomorph.divLeft _).isOpenMap

@[to_additive]
theorem isClosedMap_div_left (a : G) : IsClosedMap (a / ·) :=
  (Homeomorph.divLeft _).isClosedMap

/-- A version of `Homeomorph.mulRight a⁻¹ b` that is defeq to `b / a`. -/
@[to_additive (attr := simps! +simpRhs)
  /-- A version of `Homeomorph.addRight (-a) b` that is defeq to `b - a`. -/]
def Homeomorph.divRight (x : G) : G ≃ₜ G :=
  { Equiv.divRight x with
    continuous_toFun := by
      change Continuous fun y : G => y / x
      simp_rw [div_eq_mul_inv]
      exact continuous_id.mul continuous_const
    continuous_invFun := continuous_id.mul continuous_const }

@[to_additive (attr := simp)]
theorem Homeomorph.coe_divRight (a : G) : ⇑(Homeomorph.divRight a) = (· / a) :=
  rfl

@[to_additive]
lemma isOpenMap_div_right (a : G) : IsOpenMap (· / a) := (Homeomorph.divRight a).isOpenMap

@[to_additive]
lemma isClosedMap_div_right (a : G) : IsClosedMap (· / a) := (Homeomorph.divRight a).isClosedMap

@[to_additive]
theorem tendsto_div_nhds_one_iff {α : Type*} {l : Filter α} {x : G} {u : α → G} :
    Tendsto (u · / x) l (𝓝 1) ↔ Tendsto u l (𝓝 x) :=
  haveI A : Tendsto (fun _ : α => x) l (𝓝 x) := tendsto_const_nhds
  ⟨fun h => by simpa using h.mul A, fun h => by simpa [div_eq_mul_inv] using h.mul A.inv⟩

/-- If `f → a` and `g → b` along a nontrivial filter on the domain, valued in a
Hausdorff topological group, then `f / g → 1` if and only if `a = b`. -/
@[to_additive]
theorem tendsto_div_nhds_one_iff_eq {α : Type*} {l : Filter α} [l.NeBot] [T2Space G]
    {f g : α → G} {a b : G} (hf : Tendsto f l (𝓝 a)) (hg : Tendsto g l (𝓝 b)) :
    Tendsto (fun x ↦ f x / g x) l (𝓝 1) ↔ a = b :=
  ⟨fun hfg => tendsto_nhds_unique hf <| by simpa using hfg.mul hg,
   fun h => by subst h; simpa [div_eq_mul_inv] using hf.mul hg.inv⟩

@[to_additive]
alias ⟨eq_of_tendsto_div_nhds_one, _⟩ := tendsto_div_nhds_one_iff_eq

@[to_additive]
theorem nhds_translation_div (x : G) : comap (· / x) (𝓝 1) = 𝓝 x := by
  simpa only [div_eq_mul_inv] using nhds_translation_mul_inv x

@[to_additive (attr := simp)]
theorem Filter.map_divRight_nhdsNE {c a : G} :
    map (· / c) (𝓝[≠] a) = 𝓝[≠] (a / c) := by
  convert! (Homeomorph.divRight c).isEmbedding.map_nhdsWithin_eq .. using 2
  simp [div_eq_mul_inv]

@[to_additive (attr := simp)]
theorem Filter.map_divRight_nhds {c a : G} :
    map (· / c) (𝓝 a) = 𝓝 (a / c) := by
  convert! (Homeomorph.divRight c).map_nhds_eq .. using 2

@[to_additive (attr := simp)]
theorem Filter.map_divLeft_nhdsNE {c a : G} :
    map (c / ·) (𝓝[≠] a) = 𝓝[≠] (c / a) := by
  convert! (Homeomorph.divLeft c).isEmbedding.map_nhdsWithin_eq .. using 2
  simp [image_div_left]

@[to_additive (attr := simp)]
theorem Filter.map_divLeft_nhds {c a : G} :
    map (c / ·) (𝓝 a) = 𝓝 (c / a) := by
  convert! (Homeomorph.divLeft c).map_nhds_eq .. using 2

end DivInvTopologicalGroup
