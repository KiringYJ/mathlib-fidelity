/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.Algebra.GroupWithZero.Units.Equiv
public import Mathlib.Topology.Algebra.Group.ContinuousInv
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Topological group with zero

In this file we define `ContinuousInv₀` to express continuity of inversion on the subtype
of invertible elements, equipped with the ambient subspace topology. Any
normed (semi)field has this property. Currently the only example of `ContinuousInv₀` in
`mathlib` which is not a normed field is the type `NNReal` (a.k.a. `ℝ≥0`) of nonnegative real
numbers.

Then we prove lemmas about continuity of `x ↦ x⁻¹` and `f / g` providing dot-style `*.inv₀` and
`*.div` operations on `Filter.Tendsto`, `ContinuousAt`, `ContinuousWithinAt`, `ContinuousOn`,
and `Continuous`. As a special case, we provide `*.div_const` operations that require only
`DivInvMonoid` and `ContinuousMul` instances.

All lemmas about `(⁻¹)` use `inv₀` in their names because lemmas without `₀` are used for
`IsTopologicalGroup`s. We also use `'` in the typeclass name `ContinuousInv₀` for the sake of
consistency of notation.

On a `GroupWithZero` with continuous multiplication, we also define left and right multiplication
as homeomorphisms.
-/

@[expose] public section
open Topology Filter Function
open scoped Classical

/-!
### A `DivInvMonoid` with continuous multiplication

If `G₀` is a `DivInvMonoid` with continuous `(*)`, then `(/y)` is continuous for any `y`. In this
section we prove lemmas that immediately follow from this fact providing `*.div_const` dot-style
operations on `Filter.Tendsto`, `ContinuousAt`, `ContinuousWithinAt`, `ContinuousOn`, and
`Continuous`.
-/


variable {α β G₀ : Type*}

section DivConst

variable [DivInvMonoid G₀] [TopologicalSpace G₀] [SeparatelyContinuousMul G₀]
  {f : α → G₀} {s : Set α} {l : Filter α}

theorem Filter.Tendsto.div_const {x : G₀} (hf : Tendsto f l (𝓝 x)) (y : G₀) :
    Tendsto (fun a => f a / y) l (𝓝 (x / y)) := by
  simpa only [div_eq_mul_inv] using hf.mul_const _

variable [TopologicalSpace α]

nonrec theorem ContinuousAt.div_const {a : α} (hf : ContinuousAt f a) (y : G₀) :
    ContinuousAt (fun x => f x / y) a :=
  hf.div_const y

nonrec theorem ContinuousWithinAt.div_const {a} (hf : ContinuousWithinAt f s a) (y : G₀) :
    ContinuousWithinAt (fun x => f x / y) s a :=
  hf.div_const _

theorem ContinuousOn.div_const (hf : ContinuousOn f s) (y : G₀) :
    ContinuousOn (fun x => f x / y) s := by
  simpa only [div_eq_mul_inv] using hf.mul_const _

@[continuity, fun_prop]
theorem Continuous.div_const (hf : Continuous f) (y : G₀) : Continuous fun x => f x / y := by
  simpa only [div_eq_mul_inv] using hf.mul_const _

end DivConst

section DivpConst

variable [Monoid G₀] [TopologicalSpace G₀] [SeparatelyContinuousMul G₀]
  {f : α → G₀} {s : Set α} {l : Filter α}

theorem Filter.Tendsto.divp_const {x : G₀} (hf : Tendsto f l (𝓝 x)) (u : G₀ˣ) :
    Tendsto (fun a => f a /ₚ u) l (𝓝 (x /ₚ u)) := hf.mul_const _

variable [TopologicalSpace α]

theorem ContinuousAt.divp_const {a : α} (hf : ContinuousAt f a) (u : G₀ˣ) :
    ContinuousAt (fun x => f x /ₚ u) a := hf.mul_const _

theorem ContinuousWithinAt.divp_const {a : α} (hf : ContinuousWithinAt f s a) (u : G₀ˣ) :
    ContinuousWithinAt (fun x => f x /ₚ u) s a := hf.mul_const _

theorem ContinuousOn.divp_const (hf : ContinuousOn f s) (u : G₀ˣ) :
    ContinuousOn (fun x => f x /ₚ u) s := hf.mul_const _

theorem Continuous.divp_const (hf : Continuous f) (u : G₀ˣ) :
    Continuous (fun x => f x /ₚ u) := hf.mul_const _

end DivpConst

/-- Inversion is continuous on the invertible-element subtype with its ambient subspace
 topology. This condition does not equip the ambient monoid with a total inverse. -/
class ContinuousInv₀ (G₀ : Type*) [Monoid G₀] [TopologicalSpace G₀] : Prop where
  continuous_inv : Continuous (fun x : {x : G₀ | IsUnit x} ↦ (↑x.property.unit⁻¹ : G₀))

section Inv₀

variable [Monoid G₀] [TopologicalSpace G₀] [ContinuousInv₀ G₀]
  {l : Filter α} {f : α → G₀} {s : Set α} {a : α}

theorem continuousAt_inv₀ (x : {x : G₀ | IsUnit x}) :
    ContinuousAt (fun y : {y : G₀ | IsUnit y} ↦ (↑y.property.unit⁻¹ : G₀)) x :=
  ContinuousInv₀.continuous_inv.continuousAt

theorem tendsto_inv₀ (x : {x : G₀ | IsUnit x}) :
    Tendsto (fun y : {y : G₀ | IsUnit y} ↦ (↑y.property.unit⁻¹ : G₀))
      (𝓝 x) (𝓝 (↑x.property.unit⁻¹ : G₀)) := continuousAt_inv₀ x

theorem continuousOn_inv₀ :
    ContinuousOn (fun y : {y : G₀ | IsUnit y} ↦ (↑y.property.unit⁻¹ : G₀)) Set.univ :=
  ContinuousInv₀.continuous_inv.continuousOn

/-- A family of invertible elements converging in the ambient monoid has convergent inverses. -/
theorem Filter.Tendsto.inv₀ {b : G₀} (hf : Tendsto f l (𝓝 b))
    (hfunit : ∀ x, IsUnit (f x)) (hb : IsUnit b) :
    Tendsto (fun x ↦ (↑(hfunit x).unit⁻¹ : G₀)) l (𝓝 (↑hb.unit⁻¹ : G₀)) :=
  (tendsto_inv₀ ⟨b, hb⟩).comp
    (tendsto_subtype_rng.mpr hf : Tendsto (fun x ↦ (⟨f x, hfunit x⟩ : {y : G₀ | IsUnit y}))
      l (𝓝 ⟨b, hb⟩))

variable [TopologicalSpace α]

theorem ContinuousWithinAt.inv₀ (hf : ContinuousWithinAt f s a) (ha : IsUnit (f a)) :
    ContinuousWithinAt (fun y : {y : α | IsUnit (f y)} ↦ (↑y.property.unit⁻¹ : G₀))
      (Subtype.val ⁻¹' s) ⟨a, ha⟩ := by
  have hv : ContinuousWithinAt (fun y : {y : α | IsUnit (f y)} ↦ f y.val) (Subtype.val ⁻¹' s) ⟨a, ha⟩ :=
    hf.comp continuous_subtype_val.continuousWithinAt (fun _ hy => hy)
  have h : Tendsto (fun y : {y : α | IsUnit (f y)} ↦
      (⟨f y.val, y.property⟩ : {y : G₀ | IsUnit y}))
      (𝓝[Subtype.val ⁻¹' s] ⟨a, ha⟩) (𝓝 ⟨f a, ha⟩) := tendsto_subtype_rng.mpr hv
  exact (tendsto_inv₀ ⟨f a, ha⟩).comp h

theorem ContinuousAt.inv₀ (hf : ContinuousAt f a) (ha : IsUnit (f a)) :
    ContinuousAt (fun y : {y : α | IsUnit (f y)} ↦ (↑y.property.unit⁻¹ : G₀)) ⟨a, ha⟩ := by
  have hv : ContinuousAt (fun y : {y : α | IsUnit (f y)} ↦ f y.val) ⟨a, ha⟩ :=
    hf.comp continuous_subtype_val.continuousAt
  have h : Tendsto (fun y : {y : α | IsUnit (f y)} ↦
      (⟨f y.val, y.property⟩ : {y : G₀ | IsUnit y}))
      (𝓝 ⟨a, ha⟩) (𝓝 ⟨f a, ha⟩) := tendsto_subtype_rng.mpr hv
  exact (tendsto_inv₀ ⟨f a, ha⟩).comp h

theorem Continuous.inv₀ (hf : Continuous f) (h0 : ∀ x, IsUnit (f x)) :
    Continuous (fun x ↦ (↑(h0 x).unit⁻¹ : G₀)) :=
  ContinuousInv₀.continuous_inv.comp (hf.subtype_mk h0)

theorem ContinuousOn.inv₀ (hf : ContinuousOn f s) :
    ContinuousOn (fun y : {y : α | IsUnit (f y)} ↦ (↑y.property.unit⁻¹ : G₀))
      (Subtype.val ⁻¹' s) :=
  fun y hy ↦ (hf y.val hy).inv₀ y.property

end Inv₀

section GroupWithZero

variable [GroupWithZero G₀] [TopologicalSpace G₀] [ContinuousInv₀ G₀]

/-- If `G₀` is a group with zero with topology such that `x ↦ x⁻¹` is continuous at all nonzero
points. Then the coercion `G₀ˣ → G₀` is a topological embedding. -/
theorem Units.isEmbedding_val₀ : IsEmbedding (val : G₀ˣ → G₀) :=
  Units.isEmbedding_val_mk' ContinuousInv₀.continuous_inv (fun _ => by simp)

/-- If a group with zero has continuous inversion, then its group of units is homeomorphic to
the set of nonzero elements. -/
noncomputable def unitsHomeomorphNeZero : G₀ˣ ≃ₜ {g : G₀ // g ≠ 0} :=
  Units.isEmbedding_val₀.toHomeomorph.trans <| show _ ≃ₜ {g | _} from .setCongr <|
    Set.ext fun x ↦ (Units.exists_iff_ne_zero (p := (· = x))).trans <| by simp

variable (G₀) in
/-- If a group with zero has continuous inversion, then the inversion map restricts to an
auto-homeomorphism on the set of nonzero elements. -/
noncomputable def Homeomorph.inv₀ : {g : G₀ // g ≠ 0} ≃ₜ {g : G₀ // g ≠ 0} := by
  letI : ContinuousInv G₀ˣ := ⟨Units.continuous_iff.mpr
    ⟨Units.continuous_coe_inv, by simpa only [inv_inv] using Units.continuous_val⟩⟩
  exact unitsHomeomorphNeZero.symm.trans ((Homeomorph.inv G₀ˣ).trans unitsHomeomorphNeZero)

end GroupWithZero

section NhdsInv

open scoped Pointwise

variable [GroupWithZero G₀] [TopologicalSpace G₀] [ContinuousInv₀ G₀] {x : G₀}

lemma nhds_inv₀ (x : {g : G₀ | g ≠ 0}) :
    map (Homeomorph.inv₀ G₀) (𝓝 x) = 𝓝 (Homeomorph.inv₀ G₀ x) :=
  (Homeomorph.inv₀ G₀).map_nhds_eq x

lemma tendsto_inv_iff₀ {l : Filter α} {f : α → {g : G₀ | g ≠ 0}}
    {x : {g : G₀ | g ≠ 0}} :
    Tendsto (fun y ↦ Homeomorph.inv₀ G₀ (f y)) l (𝓝 (Homeomorph.inv₀ G₀ x)) ↔
      Tendsto f l (𝓝 x) := by
  constructor
  · intro h
    simpa only [Function.comp_def, Homeomorph.symm_apply_apply] using
      (Homeomorph.inv₀ G₀).symm.continuous.continuousAt.tendsto.comp h
  · exact fun h ↦ (Homeomorph.inv₀ G₀).continuous.continuousAt.tendsto.comp h

end NhdsInv

/-!
### Continuity of division

If `G₀` is a `GroupWithZero` with `x ↦ x⁻¹` continuous at all nonzero points and `(*)`, then
division `(/)` is continuous at any point where the denominator is continuous.
-/

section Div

variable [GroupWithZero G₀] [TopologicalSpace G₀] [ContinuousInv₀ G₀] [ContinuousMul G₀]
  {f g : α → G₀}

theorem Filter.Tendsto.div {l : Filter α} {a b : G₀} (hf : Tendsto f l (𝓝 a))
    (hg : Tendsto g l (𝓝 b)) (hgu : ∀ x, IsUnit (g x)) (hb : IsUnit b) :
    Tendsto (fun x ↦ f x /ₚ (hgu x).unit) l (𝓝 (a /ₚ hb.unit)) := by
  exact hf.mul (hg.inv₀ hgu hb)

theorem tendsto_div_nhds_one_iff_eq₀
    {l : Filter α} [l.NeBot] [T2Space G₀] {a b : G₀}
    (hf : Tendsto f l (𝓝 a)) (hg : Tendsto g l (𝓝 b))
    (hgu : ∀ x, IsUnit (g x)) (hb : IsUnit b) :
    Tendsto (fun x ↦ f x /ₚ (hgu x).unit) l (𝓝 1) ↔ a = b :=
  ⟨fun hfg => divp_eq_one_iff_eq.mp (tendsto_nhds_unique (hf.div hg hgu hb) hfg),
   fun hab => (show a /ₚ hb.unit = 1 from divp_eq_one_iff_eq.mpr hab) ▸ hf.div hg hgu hb⟩

alias ⟨eq_of_tendsto_div_nhds_one₀, _⟩ := tendsto_div_nhds_one_iff_eq₀

theorem Filter.tendsto_mul_iff_of_ne_zero [T1Space G₀] {f g : α → G₀} {l : Filter α} {x y : G₀}
    (hg : Tendsto g l (𝓝 y)) (hy : y ≠ 0) :
    Tendsto (fun n => f n * g n) l (𝓝 <| x * y) ↔ Tendsto f l (𝓝 x) := by
  refine ⟨fun hfg => ?_, fun hf => hf.mul hg⟩
  have hl : {n | IsUnit (g n)} ∈ l :=
    (hg.eventually_ne hy).mono (fun _ h => isUnit_iff_ne_zero.mpr h)
  apply (tendsto_comap'_iff (i := (Subtype.val : {n | IsUnit (g n)} → α))
    (by simpa only [Subtype.range_val] using hl)).mp
  have h := (hfg.comp tendsto_comap).div (hg.comp tendsto_comap)
    (fun n : {n | IsUnit (g n)} ↦ n.property) (isUnit_iff_ne_zero.mpr hy)
  simpa only [Function.comp_def, divp, mul_assoc, IsUnit.mul_val_inv, mul_one] using h

variable [TopologicalSpace α] [TopologicalSpace β] {s : Set α} {a : α}

theorem ContinuousWithinAt.div (hf : ContinuousWithinAt f s a)
    (hg : ContinuousWithinAt g s a) (h₀ : IsUnit (g a)) :
    ContinuousWithinAt (fun x : {x | IsUnit (g x)} ↦ f x.val /ₚ x.property.unit)
      (Subtype.val ⁻¹' s) ⟨a, h₀⟩ :=
  (hf.comp continuous_subtype_val.continuousWithinAt (fun _ hx => hx)).mul (hg.inv₀ h₀)

theorem ContinuousOn.div (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun x : {x | IsUnit (g x)} ↦ f x.val /ₚ x.property.unit)
      (Subtype.val ⁻¹' s) :=
  fun x hx => (hf x.val hx).div (hg x.val hx) x.property

theorem ContinuousAt.div (hf : ContinuousAt f a) (hg : ContinuousAt g a)
    (h₀ : IsUnit (g a)) :
    ContinuousAt (fun x : {x | IsUnit (g x)} ↦ f x.val /ₚ x.property.unit) ⟨a, h₀⟩ :=
  (hf.comp continuous_subtype_val.continuousAt).mul (hg.inv₀ h₀)

theorem Continuous.div (hf : Continuous f) (hg : Continuous g) (h₀ : ∀ x, IsUnit (g x)) :
    Continuous (fun x ↦ f x /ₚ (h₀ x).unit) := hf.mul (hg.inv₀ h₀)

theorem continuousOn_div :
    ContinuousOn (fun p : {p : G₀ × G₀ | IsUnit p.2} ↦ p.val.1 /ₚ p.property.unit)
      Set.univ := by
  simpa only [Set.preimage_univ] using (continuousOn_fst (s := (Set.univ : Set (G₀ × G₀)))).div continuousOn_snd

/-- An outer function with a prescribed limit independent of its second argument extends
continuously across a zero denominator. The boundary value is part of this composite function;
no value of division at zero is defined. -/
theorem ContinuousAt.comp_div_cases {f g : α → G₀} (h : α → G₀ → β) (hf : ContinuousAt f a)
    (hg : ContinuousAt g a)
    (hh : ∀ hga : g a ≠ 0, ContinuousAt ↿h (a, f a /ₚ Units.mk0 (g a) hga))
    (hdom : g a ≠ 0 → {x | g x ≠ 0} ∈ 𝓝 a)
    (h2h : g a = 0 → Tendsto ↿h (𝓝 a ×ˢ ⊤) (𝓝 (h a 0))) :
    ContinuousAt
      (fun x ↦ if hx : g x = 0 then h x 0 else h x (f x /ₚ Units.mk0 (g x) hx)) a := by
  classical
  by_cases hga : g a = 0
  · change Tendsto _ (𝓝 a) _
    simp only [dite_eq_left hga]
    let b : α → G₀ := fun x ↦ if hx : g x = 0 then 0 else f x /ₚ Units.mk0 (g x) hx
    convert (h2h hga).comp (continuousAt_id.tendsto.prodMk (tendsto_top (f := b))) using 1
    funext x
    change (if hx : g x = 0 then h x 0 else h x (f x /ₚ Units.mk0 (g x) hx)) =
      h x (if hx : g x = 0 then 0 else f x /ₚ Units.mk0 (g x) hx)
    by_cases hx : g x = 0 <;> simp [hx]
  · change Tendsto _ (𝓝 a) _
    simp only [dite_eq_right hga]
    apply (tendsto_comap'_iff (i := (Subtype.val : {x | g x ≠ 0} → α))
      (by simpa only [Subtype.range_val] using hdom hga)).mp
    have hdiv := (hf.tendsto.comp tendsto_comap).div (hg.tendsto.comp tendsto_comap)
      (fun x : {x | g x ≠ 0} ↦ GroupWithZero.isUnit_of_ne_zero x.property)
      (GroupWithZero.isUnit_of_ne_zero hga)
    convert (hh hga).tendsto.comp (by simpa only [nhds_prod_eq, Units.mk0] using tendsto_comap.prodMk hdiv) using 1
    funext x
    simp only [Function.comp_def, dite_eq_right x.property]
    all_goals rfl

/-- The composite with its specified zero-denominator boundary value is continuous everywhere. -/
theorem Continuous.comp_div_cases {f g : α → G₀} (h : α → G₀ → β) (hf : Continuous f)
    (hg : Continuous g)
    (hh : ∀ a (ha : g a ≠ 0), ContinuousAt ↿h (a, f a /ₚ Units.mk0 (g a) ha))
    (hdom : ∀ a, g a ≠ 0 → {x | g x ≠ 0} ∈ 𝓝 a)
    (h2h : ∀ a, g a = 0 → Tendsto ↿h (𝓝 a ×ˢ ⊤) (𝓝 (h a 0))) :
    Continuous
      (fun x ↦ if hx : g x = 0 then h x 0 else h x (f x /ₚ Units.mk0 (g x) hx)) :=
  continuous_iff_continuousAt.mpr fun a =>
    hf.continuousAt.comp_div_cases _ hg.continuousAt (hh a) (hdom a) (h2h a)

end Div

/-! ### Left and right multiplication as homeomorphisms -/


namespace Homeomorph

variable [TopologicalSpace α] [GroupWithZero α] [SeparatelyContinuousMul α]

/-- Left multiplication by a nonzero element in a `GroupWithZero` with continuous multiplication
is a homeomorphism of the underlying type. -/
protected noncomputable def mulLeft₀ (c : α) (hc : c ≠ 0) : α ≃ₜ α :=
  { Equiv.mulLeft₀ c hc with
    continuous_toFun := continuous_const_mul _
    continuous_invFun := continuous_const_mul _ }

/-- Right multiplication by a nonzero element in a `GroupWithZero` with continuous multiplication
is a homeomorphism of the underlying type. -/
protected noncomputable def mulRight₀ (c : α) (hc : c ≠ 0) : α ≃ₜ α :=
  { Equiv.mulRight₀ c hc with
    continuous_toFun := continuous_mul_const _
    continuous_invFun := continuous_mul_const _ }

@[simp]
theorem coe_mulLeft₀ (c : α) (hc : c ≠ 0) : ⇑(Homeomorph.mulLeft₀ c hc) = (c * ·) :=
  rfl

@[simp]
theorem mulLeft₀_symm_apply (c : α) (hc : c ≠ 0) :
    ((Homeomorph.mulLeft₀ c hc).symm : α → α) = ((↑(Units.mk0 c hc)⁻¹ : α) * ·) :=
  rfl

@[simp]
theorem coe_mulRight₀ (c : α) (hc : c ≠ 0) : ⇑(Homeomorph.mulRight₀ c hc) = (· * c) :=
  rfl

@[simp]
theorem mulRight₀_symm_apply (c : α) (hc : c ≠ 0) :
    ((Homeomorph.mulRight₀ c hc).symm : α → α) = (· * (↑(Units.mk0 c hc)⁻¹ : α)) :=
  rfl

end Homeomorph

section map_comap

variable [TopologicalSpace G₀] [GroupWithZero G₀] [SeparatelyContinuousMul G₀] {a : G₀}

theorem map_mul_left_nhds₀ (ha : a ≠ 0) (b : G₀) : map (a * ·) (𝓝 b) = 𝓝 (a * b) :=
  (Homeomorph.mulLeft₀ a ha).map_nhds_eq b

theorem map_mul_left_nhds_one₀ (ha : a ≠ 0) : map (a * ·) (𝓝 1) = 𝓝 (a) := by
  rw [map_mul_left_nhds₀ ha, mul_one]

theorem map_mul_right_nhds₀ (ha : a ≠ 0) (b : G₀) : map (· * a) (𝓝 b) = 𝓝 (b * a) :=
  (Homeomorph.mulRight₀ a ha).map_nhds_eq b

theorem map_mul_right_nhds_one₀ (ha : a ≠ 0) : map (· * a) (𝓝 1) = 𝓝 (a) := by
  rw [map_mul_right_nhds₀ ha, one_mul]

theorem nhds_translation_mul_inv₀ (ha : a ≠ 0) : comap (· * (↑(Units.mk0 a ha)⁻¹ : G₀)) (𝓝 1) = 𝓝 a :=
  ((Homeomorph.mulRight₀ a ha).symm.comap_nhds_eq 1).trans <| by simp

/-- Continuity of inversion at the identity of the invertible-element subtype implies
continuity at every point of that subtype. -/
theorem ContinuousInv₀.of_nhds_one
    (h : Tendsto (fun y : {y : G₀ | IsUnit y} ↦ (↑y.property.unit⁻¹ : G₀))
      (𝓝 ⟨1, isUnit_one⟩) (𝓝 1)) : ContinuousInv₀ G₀ where
  continuous_inv := by
    rw [continuous_iff_continuousAt]
    intro x
    change Tendsto _ (𝓝 x) _
    let g : {y : G₀ | IsUnit y} → {y : G₀ | IsUnit y} := fun y ↦
      ⟨y.val * ↑x.property.unit⁻¹, y.property.mul (x.property.unit⁻¹).isUnit⟩
    have hg : Tendsto g (𝓝 x) (𝓝 ⟨1, isUnit_one⟩) := by
      apply tendsto_subtype_rng.mpr
      simpa only [g, x.property.mul_val_inv] using
        (continuous_subtype_val.tendsto x).mul_const (↑x.property.unit⁻¹ : G₀)
    have hu (y : {y : G₀ | IsUnit y}) :
        (g y).property.unit = y.property.unit * x.property.unit⁻¹ := Units.ext rfl
    have hi := (h.comp hg).const_mul (↑x.property.unit⁻¹ : G₀)
    simpa only [Function.comp_def, hu, mul_inv_rev, inv_inv, Units.val_mul,
      ← mul_assoc, Units.inv_mul, one_mul, mul_one] using hi

end map_comap

section ZPow

variable [GroupWithZero G₀] [TopologicalSpace G₀] [ContinuousInv₀ G₀] [ContinuousMul G₀]

/-- Integer powers are continuous on their exact domain, including zero when the exponent
is nonnegative. -/
theorem continuous_zpow₀ (m : ℤ) :
    Continuous (fun x : {x : G₀ | m < 0 → IsUnit x} ↦ Checked.zpow x.val m x.property) := by
  cases m with
  | ofNat n => exact continuous_subtype_val.pow n
  | negSucc n =>
    have h := continuous_subtype_val.inv₀
      (fun x : {x : G₀ | Int.negSucc n < 0 → IsUnit x} ↦
        x.property (Int.negSucc_lt_zero n))
    have hp : Continuous (fun x : {x : G₀ | Int.negSucc n < 0 → IsUnit x} ↦
        (↑(x.property (Int.negSucc_lt_zero n)).unit⁻¹ : G₀) ^ (n + 1)) := h.pow (n + 1)
    simpa only [Checked.zpow, zpow_negSucc, ← inv_pow, Units.val_pow_eq_pow_val] using hp

theorem continuousAt_zpow₀ (m : ℤ) (x : {x : G₀ | m < 0 → IsUnit x}) :
    ContinuousAt (fun y : {y : G₀ | m < 0 → IsUnit y} ↦ Checked.zpow y.val m y.property) x :=
  (continuous_zpow₀ m).continuousAt

theorem continuousOn_zpow₀ (m : ℤ) :
    ContinuousOn (fun y : {y : G₀ | m < 0 → IsUnit y} ↦ Checked.zpow y.val m y.property)
      Set.univ := (continuous_zpow₀ m).continuousOn

theorem Filter.Tendsto.zpow₀ {f : α → G₀} {l : Filter α} {a : G₀}
    (hf : Tendsto f l (𝓝 a)) (m : ℤ)
    (hfunit : ∀ x, m < 0 → IsUnit (f x)) (ha : m < 0 → IsUnit a) :
    Tendsto (fun x => Checked.zpow (f x) m (hfunit x)) l (𝓝 (Checked.zpow a m ha)) :=
  (continuousAt_zpow₀ m ⟨a, ha⟩).tendsto.comp
    (tendsto_subtype_rng.mpr hf : Tendsto
      (fun x ↦ (⟨f x, hfunit x⟩ : {y : G₀ | m < 0 → IsUnit y})) l (𝓝 ⟨a, ha⟩))

variable {X : Type*} [TopologicalSpace X] {a : X} {s : Set X} {f : X → G₀}

theorem ContinuousAt.zpow₀ (hf : ContinuousAt f a) (m : ℤ)
    (ha : m < 0 → IsUnit (f a)) :
    ContinuousAt
      (fun x : {x : X | m < 0 → IsUnit (f x)} ↦ Checked.zpow (f x.val) m x.property)
      ⟨a, ha⟩ := by
  have hv : ContinuousAt (fun y : {y : X | m < 0 → IsUnit (f y)} ↦ f y.val) ⟨a, ha⟩ :=
    hf.comp continuous_subtype_val.continuousAt
  have h : Tendsto (fun y : {y : X | m < 0 → IsUnit (f y)} ↦
      (⟨f y.val, y.property⟩ : {y : G₀ | m < 0 → IsUnit y}))
      (𝓝 ⟨a, ha⟩) (𝓝 ⟨f a, ha⟩) := tendsto_subtype_rng.mpr hv
  exact (continuousAt_zpow₀ m ⟨f a, ha⟩).tendsto.comp h

theorem ContinuousWithinAt.zpow₀ (hf : ContinuousWithinAt f s a) (m : ℤ)
    (ha : m < 0 → IsUnit (f a)) :
    ContinuousWithinAt
      (fun x : {x : X | m < 0 → IsUnit (f x)} ↦ Checked.zpow (f x.val) m x.property)
      (Subtype.val ⁻¹' s) ⟨a, ha⟩ := by
  have hv : ContinuousWithinAt (fun y : {y : X | m < 0 → IsUnit (f y)} ↦ f y.val) (Subtype.val ⁻¹' s) ⟨a, ha⟩ :=
    hf.comp continuous_subtype_val.continuousWithinAt (fun _ hy => hy)
  have h : Tendsto (fun y : {y : X | m < 0 → IsUnit (f y)} ↦
      (⟨f y.val, y.property⟩ : {y : G₀ | m < 0 → IsUnit y}))
      (𝓝[Subtype.val ⁻¹' s] ⟨a, ha⟩) (𝓝 ⟨f a, ha⟩) := tendsto_subtype_rng.mpr hv
  exact (continuousAt_zpow₀ m ⟨f a, ha⟩).tendsto.comp h

theorem ContinuousOn.zpow₀ (hf : ContinuousOn f s) (m : ℤ) :
    ContinuousOn
      (fun x : {x : X | m < 0 → IsUnit (f x)} ↦ Checked.zpow (f x.val) m x.property)
      (Subtype.val ⁻¹' s) :=
  fun x hx ↦ (hf x.val hx).zpow₀ m x.property

theorem Continuous.zpow₀ (hf : Continuous f) (m : ℤ)
    (h0 : ∀ x, m < 0 → IsUnit (f x)) :
    Continuous (fun x => Checked.zpow (f x) m (h0 x)) :=
  (continuous_zpow₀ m).comp (hf.subtype_mk h0)

end ZPow
