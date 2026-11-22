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
and `Continuous`. The inverse and the quotient are the checked operations: the function `f⁻¹`
exists when `f` is invertible, `fun x ↦ (f x)⁻¹` when every value `f x` is, and the lemmas take
this evidence implicitly from the term. The `*.fun_inv₀` and `*.div₀` versions are about the
pointwise functions `fun x ↦ (f x)⁻¹` and `fun x ↦ f x / g x`. The `*_restrict` versions give
limits and continuity on the subtype where the inverted function takes invertible values.
As a special case,
we provide `*.div_const` operations that require only `DivInvMonoid` and `ContinuousMul`
instances, and `*.div_const₀` operations for a quotient by an invertible element of a monoid.

All lemmas about `(⁻¹)` use `inv₀` in their names because lemmas without `₀` are used for
`IsTopologicalGroup`s. We also use `'` in the typeclass name `ContinuousInv₀` for the sake of
consistency of notation.

On a `GroupWithZero` with continuous multiplication, we also define left and right multiplication
as homeomorphisms.
-/

@[expose] public section
open Topology Filter Function

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
    Tendsto (fun a => f a * y⁻¹) l (𝓝 (x * y⁻¹)) :=
  hf.mul_const _

variable [TopologicalSpace α]

nonrec theorem ContinuousAt.div_const {a : α} (hf : ContinuousAt f a) (y : G₀) :
    ContinuousAt (fun x => f x * y⁻¹) a :=
  hf.div_const y

nonrec theorem ContinuousWithinAt.div_const {a} (hf : ContinuousWithinAt f s a) (y : G₀) :
    ContinuousWithinAt (fun x => f x * y⁻¹) s a :=
  hf.div_const _

theorem ContinuousOn.div_const (hf : ContinuousOn f s) (y : G₀) :
    ContinuousOn (fun x => f x * y⁻¹) s :=
  hf.mul_const _

@[continuity, fun_prop]
theorem Continuous.div_const (hf : Continuous f) (y : G₀) : Continuous fun x => f x * y⁻¹ :=
  hf.mul_const _

end DivConst

/-!
### Division by an invertible constant in a monoid

In a monoid without an ambient division, such as a group with zero, `f x / y` is the checked
quotient by an invertible element `y`. The `*.div_const₀` lemmas take its evidence from the term.
-/

section DivConst₀

variable [Monoid G₀] [TopologicalSpace G₀] [SeparatelyContinuousMul G₀]
  {f : α → G₀} {s : Set α} {l : Filter α}

theorem Filter.Tendsto.div_const₀ {x : G₀} (hf : Tendsto f l (𝓝 x)) (y : G₀) {hy : IsUnit y} :
    Tendsto (fun a => f a / y) l (𝓝 (x / y)) :=
  hf.mul_const _

variable [TopologicalSpace α]

nonrec theorem ContinuousAt.div_const₀ {a : α} (hf : ContinuousAt f a) (y : G₀)
    {hy : IsUnit y} : ContinuousAt (fun x => f x / y) a :=
  hf.div_const₀ y

nonrec theorem ContinuousWithinAt.div_const₀ {a} (hf : ContinuousWithinAt f s a) (y : G₀)
    {hy : IsUnit y} : ContinuousWithinAt (fun x => f x / y) s a :=
  hf.div_const₀ _

theorem ContinuousOn.div_const₀ (hf : ContinuousOn f s) (y : G₀) {hy : IsUnit y} :
    ContinuousOn (fun x => f x / y) s :=
  hf.mul_const _

@[continuity, fun_prop]
theorem Continuous.div_const₀ (hf : Continuous f) (y : G₀) {hy : IsUnit y} :
    Continuous fun x => f x / y :=
  hf.mul_const _

end DivConst₀

/-- Inversion is continuous on the invertible-element subtype with its ambient subspace
topology. This condition does not equip the ambient monoid with a total inverse. -/
class ContinuousInv₀ (G₀ : Type*) [Monoid G₀] [TopologicalSpace G₀] : Prop where
  /-- Inversion is continuous on the subtype of invertible elements. -/
  continuous_inv : Continuous fun x : {x : G₀ | IsUnit x} ↦ Checked.inv (x : G₀) x.2

section Inv₀

variable [Monoid G₀] [TopologicalSpace G₀] [ContinuousInv₀ G₀]
  {l : Filter α} {f : α → G₀} {s : Set α} {a : α}

/-!
### Continuity of `fun x ↦ x⁻¹` at an invertible point

Inversion is defined on the subtype of invertible elements, where `ContinuousInv₀` makes it
continuous. In this section we prove dot-style `*.inv₀` lemmas for `Filter.Tendsto`,
`ContinuousAt`, `ContinuousWithinAt`, `ContinuousOn`, and `Continuous`.
-/

theorem continuousAt_inv₀ (x : {x : G₀ | IsUnit x}) :
    ContinuousAt (fun y : {y : G₀ | IsUnit y} ↦ Checked.inv (y : G₀) y.2) x :=
  ContinuousInv₀.continuous_inv.continuousAt

theorem tendsto_inv₀ (x : {x : G₀ | IsUnit x}) :
    Tendsto (fun y : {y : G₀ | IsUnit y} ↦ Checked.inv (y : G₀) y.2) (𝓝 x)
      (𝓝 (Checked.inv (x : G₀) x.2)) :=
  continuousAt_inv₀ x

theorem continuousOn_inv₀ :
    ContinuousOn (fun y : {y : G₀ | IsUnit y} ↦ Checked.inv (y : G₀) y.2) Set.univ :=
  ContinuousInv₀.continuous_inv.continuousOn

/-- If a function converges to an invertible value, its inverse converges to the inverse of this
value. We use the name `Filter.Tendsto.inv₀` as `Filter.Tendsto.inv` is already used in
multiplicative topological groups. -/
theorem Filter.Tendsto.inv₀ {a : G₀} {h0 : ∀ x, IsUnit (f x)} {ha : IsUnit a}
    (hf : Tendsto f l (𝓝 a)) : Tendsto (fun x => Checked.inv (f x) (h0 x)) l (𝓝 a⁻¹) :=
  (tendsto_inv₀ ⟨a, ha⟩).comp (tendsto_subtype_rng.mpr hf :
    Tendsto (fun x ↦ (⟨f x, h0 x⟩ : {y : G₀ | IsUnit y})) l (𝓝 ⟨a, ha⟩))

/-- The pointwise inverse converges on the subtype of inputs with invertible values, equipped with
the restriction of the original filter. -/
theorem Filter.Tendsto.inv₀_restrict {b : G₀} {hb : IsUnit b}
    (hf : Tendsto f l (𝓝 b)) :
    Tendsto (fun x : {x // IsUnit (f x)} ↦ Checked.inv (f x.val) x.property)
      (comap Subtype.val l) (𝓝 (Checked.inv b hb)) :=
  (hf.comp tendsto_comap).inv₀ (h0 := fun x ↦ x.property)

variable [TopologicalSpace α]

@[fun_prop]
nonrec theorem ContinuousWithinAt.fun_inv₀ {h0 : ∀ x, IsUnit (f x)}
    (hf : ContinuousWithinAt f s a) :
    ContinuousWithinAt (fun x ↦ Checked.inv (f x) (h0 x)) s a :=
  hf.inv₀ (ha := h0 a)

/-- The pointwise inverse is continuous within the restriction of `s` to the inputs with
invertible values, at an input where the value is invertible. -/
theorem ContinuousWithinAt.fun_inv₀_restrict (hf : ContinuousWithinAt f s a)
    (ha : IsUnit (f a)) :
    ContinuousWithinAt (fun x : {x // IsUnit (f x)} ↦ Checked.inv (f x.val) x.property)
      (Subtype.val ⁻¹' s) ⟨a, ha⟩ := by
  have h : ContinuousWithinAt (f ∘ Subtype.val) (Subtype.val ⁻¹' s)
      (⟨a, ha⟩ : {x // IsUnit (f x)}) :=
    hf.comp continuous_subtype_val.continuousWithinAt (fun _ hx ↦ hx)
  exact h.fun_inv₀

@[fun_prop]
theorem ContinuousWithinAt.inv₀ {h0 : IsUnit f} (hf : ContinuousWithinAt f s a) :
    ContinuousWithinAt f⁻¹ s a := by
  rw [funext (Pi.inv_apply₀ f)]
  exact hf.fun_inv₀

@[fun_prop]
nonrec theorem ContinuousAt.fun_inv₀ {h0 : ∀ x, IsUnit (f x)} (hf : ContinuousAt f a) :
    ContinuousAt (fun x ↦ Checked.inv (f x) (h0 x)) a :=
  hf.inv₀ (ha := h0 a)

@[fun_prop]
theorem ContinuousAt.inv₀ {h0 : IsUnit f} (hf : ContinuousAt f a) : ContinuousAt f⁻¹ a := by
  rw [funext (Pi.inv_apply₀ f)]
  exact hf.fun_inv₀

@[continuity, fun_prop]
theorem Continuous.fun_inv₀ {h0 : ∀ x, IsUnit (f x)} (hf : Continuous f) :
    Continuous fun x ↦ Checked.inv (f x) (h0 x) :=
  ContinuousInv₀.continuous_inv.comp (hf.subtype_mk h0)

@[continuity, fun_prop]
theorem Continuous.inv₀ {h0 : IsUnit f} (hf : Continuous f) : Continuous f⁻¹ := by
  rw [funext (Pi.inv_apply₀ f)]
  exact hf.fun_inv₀

@[fun_prop]
theorem ContinuousOn.fun_inv₀ {h0 : ∀ x, IsUnit (f x)} (hf : ContinuousOn f s) :
    ContinuousOn (fun x ↦ Checked.inv (f x) (h0 x)) s :=
  fun x hx ↦ (hf x hx).fun_inv₀

/-- The pointwise inverse of a function continuous on `s` is continuous on the restriction of
`s` to inputs with invertible values. -/
theorem ContinuousOn.fun_inv₀_restrict (hf : ContinuousOn f s) :
    ContinuousOn (fun x : {x // IsUnit (f x)} ↦ Checked.inv (f x.val) x.property)
      (Subtype.val ⁻¹' s) := by
  rintro ⟨x, hx⟩ hxs
  exact (hf x hxs).fun_inv₀_restrict hx

@[fun_prop]
theorem ContinuousOn.inv₀ {h0 : IsUnit f} (hf : ContinuousOn f s) : ContinuousOn f⁻¹ s := by
  rw [funext (Pi.inv_apply₀ f)]
  exact hf.fun_inv₀

end Inv₀

section GroupWithZero

variable [GroupWithZero G₀] [TopologicalSpace G₀] [ContinuousInv₀ G₀]

/-- If `G₀` is a group with zero with topology such that `x ↦ x⁻¹` is continuous at all nonzero
points. Then the coercion `G₀ˣ → G₀` is a topological embedding. -/
theorem Units.isEmbedding_val₀ : IsEmbedding (val : G₀ˣ → G₀) :=
  Units.isEmbedding_val_mk' ContinuousInv₀.continuous_inv fun u =>
    (Units.val_inv_eq_inv_val₀ u).symm

/-- If a group with zero has continuous inversion, then its group of units is homeomorphic to
the set of nonzero elements. -/
noncomputable def unitsHomeomorphNeZero : G₀ˣ ≃ₜ {g : G₀ // g ≠ 0} :=
  Units.isEmbedding_val₀.toHomeomorph.trans <| show _ ≃ₜ {g | _} from .setCongr <|
    Set.ext fun x ↦ (Units.exists_iff_ne_zero (p := (· = x))).trans <| by simp

variable (G₀) in
/-- If a group with zero has continuous inversion, then the inversion map restricts to an
auto-homeomorphism on the set of nonzero elements. -/
noncomputable def Homeomorph.inv₀ : {g : G₀ // g ≠ 0} ≃ₜ {g : G₀ // g ≠ 0} where
  toFun g := ⟨Checked.inv (g : G₀) g.2.isUnit, inv_ne_zero⟩
  invFun g := ⟨Checked.inv (g : G₀) g.2.isUnit, inv_ne_zero⟩
  left_inv _ := Subtype.ext (inv_inv₀ _)
  right_inv _ := Subtype.ext (inv_inv₀ _)
  continuous_toFun := (continuous_subtype_val.fun_inv₀ (h0 := fun g ↦ g.2.isUnit)).subtype_mk _
  continuous_invFun := (continuous_subtype_val.fun_inv₀ (h0 := fun g ↦ g.2.isUnit)).subtype_mk _

end GroupWithZero

section NhdsInv

variable [GroupWithZero G₀] [TopologicalSpace G₀] [ContinuousInv₀ G₀] {x : G₀}

lemma nhds_inv₀ (x : {g : G₀ | g ≠ 0}) :
    map (Homeomorph.inv₀ G₀) (𝓝 x) = 𝓝 (Homeomorph.inv₀ G₀ x) :=
  (Homeomorph.inv₀ G₀).map_nhds_eq x

lemma tendsto_inv_iff₀ {l : Filter α} {f : α → G₀} {h0 : ∀ y, IsUnit (f y)} {hx : IsUnit x} :
    Tendsto (fun y ↦ Checked.inv (f y) (h0 y)) l (𝓝 x⁻¹) ↔ Tendsto f l (𝓝 x) := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.inv₀⟩
  simpa only [inv_inv₀] using h.inv₀ (h0 := fun y ↦ (h0 y).inv₀) (ha := hx.inv₀)

end NhdsInv

/-!
### Continuity of division

If `G₀` is a `GroupWithZero` with `x ↦ x⁻¹` continuous at all nonzero points and `(*)`, then
division `(/)` is continuous at any point where the denominator is continuous.
-/

section Div

variable [GroupWithZero G₀] [TopologicalSpace G₀] [ContinuousInv₀ G₀] [ContinuousMul G₀]
  {f g : α → G₀}

theorem Filter.Tendsto.div₀ {l : Filter α} {a b : G₀} {h₀ : ∀ x, IsUnit (g x)} {hb : IsUnit b}
    (hf : Tendsto f l (𝓝 a)) (hg : Tendsto g l (𝓝 b)) :
    Tendsto (fun x ↦ Checked.div (f x) (g x) (h₀ x)) l (𝓝 (a / b)) := by
  simpa only [div_eq_mul_inv₀] using hf.mul (hg.inv₀ (h0 := h₀) (ha := hb))

/-- The pointwise quotient converges on the subtype where the denominator is invertible,
equipped with the restriction of the original filter. -/
theorem Filter.Tendsto.div₀_restrict {l : Filter α} {a b : G₀} {hb : IsUnit b}
    (hf : Tendsto f l (𝓝 a)) (hg : Tendsto g l (𝓝 b)) :
    Tendsto (fun x : {x // IsUnit (g x)} ↦ Checked.div (f x.val) (g x.val) x.property)
      (comap Subtype.val l) (𝓝 (Checked.div a b hb)) := by
  simpa only [div_eq_mul_inv₀, Function.comp_apply] using
    (hf.comp tendsto_comap).mul (hg.inv₀_restrict (hb := hb))

theorem Filter.Tendsto.div {l : Filter α} {a b : G₀} {h₀ : IsUnit g} {hb : IsUnit b}
    (hf : Tendsto f l (𝓝 a)) (hg : Tendsto g l (𝓝 b)) : Tendsto (f / g) l (𝓝 (a / b)) := by
  rw [funext (Pi.div_apply₀ f g)]
  exact hf.div₀ hg

/-- If `f → a` and `g → b` along a nontrivial filter, valued in a Hausdorff
`GroupWithZero` with continuous multiplication and `ContinuousInv₀`, and `b ≠ 0`,
then `f / g → 1` if and only if `a = b`. -/
theorem tendsto_div_nhds_one_iff_eq₀
    {l : Filter α} [l.NeBot] [T2Space G₀] {a b : G₀} {h₀ : ∀ x, IsUnit (g x)}
    (hf : Tendsto f l (𝓝 a)) (hg : Tendsto g l (𝓝 b)) (hb : b ≠ 0) :
    Tendsto (fun x ↦ Checked.div (f x) (g x) (h₀ x)) l (𝓝 1) ↔ a = b := by
  have hab : Tendsto (fun x ↦ Checked.div (f x) (g x) (h₀ x)) l (𝓝 (a / b)) :=
    hf.div₀ hg (hb := hb.isUnit)
  refine ⟨fun hfg => (div_eq_one_iff_eq (hb := hb.isUnit)).mp (tendsto_nhds_unique hab hfg),
    fun h => ?_⟩
  rwa [(div_eq_one_iff_eq (hb := hb.isUnit)).mpr h] at hab

alias ⟨eq_of_tendsto_div_nhds_one₀, _⟩ := tendsto_div_nhds_one_iff_eq₀

theorem Filter.tendsto_mul_iff_of_ne_zero [T1Space G₀] {f g : α → G₀} {l : Filter α} {x y : G₀}
    (hg : Tendsto g l (𝓝 y)) (hy : y ≠ 0) :
    Tendsto (fun n => f n * g n) l (𝓝 <| x * y) ↔ Tendsto f l (𝓝 x) := by
  refine ⟨fun hfg => ?_, fun hf => hf.mul hg⟩
  -- The quotient by `g` is taken on the indices where `g` is invertible, which form a set of `l`.
  have hl : {n | IsUnit (g n)} ∈ l := (hg.eventually_ne hy).mono fun _ h => h.isUnit
  apply (tendsto_comap'_iff (i := (Subtype.val : {n | IsUnit (g n)} → α))
    (by simpa only [Subtype.range_val] using hl)).mp
  have h := (hfg.comp tendsto_comap).div₀ (hg.comp tendsto_comap)
    (h₀ := fun n : {n | IsUnit (g n)} ↦ n.2) (hb := hy.isUnit)
  simpa only [Function.comp_def, mul_div_cancel_right₀] using h

variable [TopologicalSpace α] [TopologicalSpace β] {s : Set α} {a : α}

@[fun_prop]
nonrec theorem ContinuousWithinAt.div₀ {h₀ : ∀ x, IsUnit (g x)} (hf : ContinuousWithinAt f s a)
    (hg : ContinuousWithinAt g s a) :
    ContinuousWithinAt (fun x ↦ Checked.div (f x) (g x) (h₀ x)) s a :=
  hf.div₀ hg (hb := h₀ a)

/-- The pointwise quotient is continuous within the restriction of `s` to inputs with invertible
denominator, at an input where the denominator is invertible. -/
theorem ContinuousWithinAt.div₀_restrict (hf : ContinuousWithinAt f s a)
    (hg : ContinuousWithinAt g s a) (ha : IsUnit (g a)) :
    ContinuousWithinAt (fun x : {x // IsUnit (g x)} ↦ Checked.div (f x.val) (g x.val) x.property)
      (Subtype.val ⁻¹' s) ⟨a, ha⟩ := by
  have h : ContinuousWithinAt (f ∘ Subtype.val) (Subtype.val ⁻¹' s)
      (⟨a, ha⟩ : {x // IsUnit (g x)}) :=
    hf.comp continuous_subtype_val.continuousWithinAt (fun _ hx ↦ hx)
  simpa only [div_eq_mul_inv₀, Pi.mul_def, Function.comp_apply] using
    h.mul (hg.fun_inv₀_restrict ha)

theorem ContinuousWithinAt.div {h₀ : IsUnit g} (hf : ContinuousWithinAt f s a)
    (hg : ContinuousWithinAt g s a) : ContinuousWithinAt (f / g) s a := by
  rw [funext (Pi.div_apply₀ f g)]
  exact hf.div₀ hg

@[fun_prop]
theorem ContinuousOn.div₀ {h₀ : ∀ x, IsUnit (g x)} (hf : ContinuousOn f s)
    (hg : ContinuousOn g s) : ContinuousOn (fun x ↦ Checked.div (f x) (g x) (h₀ x)) s :=
  fun x hx => (hf x hx).div₀ (hg x hx)

/-- The pointwise quotient of functions continuous on `s` is continuous on the restriction of
`s` to inputs with invertible denominator. -/
theorem ContinuousOn.div₀_restrict (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun x : {x // IsUnit (g x)} ↦ Checked.div (f x.val) (g x.val) x.property)
      (Subtype.val ⁻¹' s) := by
  rintro ⟨x, hx⟩ hxs
  exact (hf x hxs).div₀_restrict (hg x hxs) hx

theorem ContinuousOn.div {h₀ : IsUnit g} (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (f / g) s := by
  rw [funext (Pi.div_apply₀ f g)]
  exact hf.div₀ hg

/-- Continuity at a point of the result of dividing two functions continuous at that point, where
the denominator is invertible. -/
@[fun_prop]
nonrec theorem ContinuousAt.div₀ {h₀ : ∀ x, IsUnit (g x)} (hf : ContinuousAt f a)
    (hg : ContinuousAt g a) : ContinuousAt (fun x ↦ Checked.div (f x) (g x) (h₀ x)) a :=
  hf.div₀ hg (hb := h₀ a)

theorem ContinuousAt.div {h₀ : IsUnit g} (hf : ContinuousAt f a) (hg : ContinuousAt g a) :
    ContinuousAt (f / g) a := by
  rw [funext (Pi.div_apply₀ f g)]
  exact hf.div₀ hg

@[fun_prop]
theorem Continuous.div₀ {h₀ : ∀ x, IsUnit (g x)} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x ↦ Checked.div (f x) (g x) (h₀ x) := by
  simpa only [div_eq_mul_inv₀] using hf.fun_mul (hg.fun_inv₀ (h0 := h₀))

@[continuity]
theorem Continuous.div {h₀ : IsUnit g} (hf : Continuous f) (hg : Continuous g) :
    Continuous (f / g) := by
  rw [funext (Pi.div_apply₀ f g)]
  exact hf.div₀ hg

theorem continuousOn_div :
    ContinuousOn (fun p : {p : G₀ × G₀ | IsUnit p.2} ↦ Checked.div p.1.1 p.1.2 p.2) Set.univ :=
  ((continuous_fst.comp continuous_subtype_val).div₀
    (continuous_snd.comp continuous_subtype_val) (h₀ := fun p ↦ p.2)).continuousOn

open Classical in
/-- An outer function with a prescribed limit independent of its second argument extends
continuously across a zero denominator. The boundary value is part of this composite function;
no value of division at zero is defined. -/
theorem ContinuousAt.comp_div_cases {f g : α → G₀} (h : α → G₀ → β) (hf : ContinuousAt f a)
    (hg : ContinuousAt g a)
    (hh : ∀ hga : g a ≠ 0, ContinuousAt ↿h (a, f a / g a))
    (hdom : g a ≠ 0 → {x | g x ≠ 0} ∈ 𝓝 a)
    (h2h : g a = 0 → Tendsto ↿h (𝓝 a ×ˢ ⊤) (𝓝 (h a 0))) :
    ContinuousAt (fun x ↦ if hx : g x = 0 then h x 0 else h x (f x / g x)) a := by
  by_cases hga : g a = 0
  · change Tendsto _ (𝓝 a) _
    simp only [dite_eq_left hga]
    let b : α → G₀ := fun x ↦ if hx : g x = 0 then 0 else f x / g x
    convert (h2h hga).comp (continuousAt_id.tendsto.prodMk (tendsto_top (f := b))) using 1
    funext x
    change (if hx : g x = 0 then h x 0 else h x (f x / g x)) =
      h x (if hx : g x = 0 then 0 else f x / g x)
    by_cases hx : g x = 0 <;> simp [hx]
  · change Tendsto _ (𝓝 a) _
    simp only [dite_eq_right hga]
    apply (tendsto_comap'_iff (i := (Subtype.val : {x | g x ≠ 0} → α))
      (by simpa only [Subtype.range_val] using hdom hga)).mp
    have hdiv := (hf.tendsto.comp tendsto_comap).div₀ (hg.tendsto.comp tendsto_comap)
      (h₀ := fun x : {x | g x ≠ 0} ↦ x.2.isUnit) (hb := Ne.isUnit hga)
    convert (hh hga).tendsto.comp
      (by simpa only [nhds_prod_eq] using tendsto_comap.prodMk hdiv) using 1
    · funext x
      simp only [Function.comp_def, dite_eq_right x.property]
      rfl
    · rfl

open Classical in
/-- The composite with its specified zero-denominator boundary value is continuous everywhere. -/
theorem Continuous.comp_div_cases {f g : α → G₀} (h : α → G₀ → β) (hf : Continuous f)
    (hg : Continuous g)
    (hh : ∀ a (ha : g a ≠ 0), ContinuousAt ↿h (a, f a / g a))
    (hdom : ∀ a, g a ≠ 0 → {x | g x ≠ 0} ∈ 𝓝 a)
    (h2h : ∀ a, g a = 0 → Tendsto ↿h (𝓝 a ×ˢ ⊤) (𝓝 (h a 0))) :
    Continuous (fun x ↦ if hx : g x = 0 then h x 0 else h x (f x / g x)) :=
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
    ((Homeomorph.mulLeft₀ c hc).symm : α → α) = (c⁻¹ * ·) :=
  rfl

@[simp]
theorem coe_mulRight₀ (c : α) (hc : c ≠ 0) : ⇑(Homeomorph.mulRight₀ c hc) = (· * c) :=
  rfl

@[simp]
theorem mulRight₀_symm_apply (c : α) (hc : c ≠ 0) :
    ((Homeomorph.mulRight₀ c hc).symm : α → α) = (· * c⁻¹) :=
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

theorem nhds_translation_mul_inv₀ (ha : a ≠ 0) : comap (· * a⁻¹) (𝓝 1) = 𝓝 a :=
  ((Homeomorph.mulRight₀ a ha).symm.comap_nhds_eq 1).trans <| by simp

/-- Continuity of inversion at the identity of the invertible-element subtype implies
continuity at every point of that subtype. -/
theorem ContinuousInv₀.of_nhds_one
    (h : Tendsto (fun y : {y : G₀ | IsUnit y} ↦ Checked.inv (y : G₀) y.2)
      (𝓝 ⟨1, isUnit_one⟩) (𝓝 1)) : ContinuousInv₀ G₀ where
  continuous_inv := by
    rw [continuous_iff_continuousAt]
    intro x
    change Tendsto (fun y : {y : G₀ | IsUnit y} ↦ (↑y.2.unit⁻¹ : G₀)) (𝓝 x)
      (𝓝 (↑x.2.unit⁻¹ : G₀))
    let g : {y : G₀ | IsUnit y} → {y : G₀ | IsUnit y} := fun y ↦
      ⟨y.val * ↑x.property.unit⁻¹, y.property.mul (x.property.unit⁻¹).isUnit⟩
    have hg : Tendsto g (𝓝 x) (𝓝 ⟨1, isUnit_one⟩) := by
      apply tendsto_subtype_rng.mpr
      simpa only [g, x.property.mul_val_inv] using
        (continuous_subtype_val.tendsto x).mul_const (↑x.property.unit⁻¹ : G₀)
    have hu (y : {y : G₀ | IsUnit y}) :
        (g y).property.unit = y.property.unit * x.property.unit⁻¹ := Units.ext rfl
    have hi := (h.comp hg).const_mul (↑x.property.unit⁻¹ : G₀)
    change Tendsto (fun y ↦ (↑x.property.unit⁻¹ : G₀) * ↑(g y).2.unit⁻¹) (𝓝 x) _ at hi
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
    have h := (continuous_subtype_val.pow (n + 1)).fun_inv₀
      (h0 := fun x : {x : G₀ | Int.negSucc n < 0 → IsUnit x} ↦
        (x.property (Int.negSucc_lt_zero n)).pow (n + 1))
    exact h.congr fun x ↦ (zpow_negSucc₀ (x : G₀) n (h := x.property)).symm

theorem continuousAt_zpow₀ (m : ℤ) (x : {x : G₀ | m < 0 → IsUnit x}) :
    ContinuousAt (fun y : {y : G₀ | m < 0 → IsUnit y} ↦ Checked.zpow y.val m y.property) x :=
  (continuous_zpow₀ m).continuousAt

theorem continuousOn_zpow₀ (m : ℤ) :
    ContinuousOn (fun y : {y : G₀ | m < 0 → IsUnit y} ↦ Checked.zpow y.val m y.property)
      Set.univ := (continuous_zpow₀ m).continuousOn

theorem Filter.Tendsto.zpow₀ {f : α → G₀} {l : Filter α} {a : G₀} (hf : Tendsto f l (𝓝 a))
    (m : ℤ) {h0 : ∀ x, m < 0 → IsUnit (f x)} {h : m < 0 → IsUnit a} :
    Tendsto (fun x => Checked.zpow (f x) m (h0 x)) l (𝓝 (a ^ m)) :=
  (continuousAt_zpow₀ m ⟨a, h⟩).tendsto.comp
    (tendsto_subtype_rng.mpr hf : Tendsto
      (fun x ↦ (⟨f x, h0 x⟩ : {y : G₀ | m < 0 → IsUnit y})) l (𝓝 ⟨a, h⟩))

variable {X : Type*} [TopologicalSpace X] {a : X} {s : Set X} {f : X → G₀}

@[fun_prop]
nonrec theorem ContinuousAt.zpow₀ (hf : ContinuousAt f a) (m : ℤ)
    {h0 : ∀ x, m < 0 → IsUnit (f x)} : ContinuousAt (fun x => Checked.zpow (f x) m (h0 x)) a :=
  hf.zpow₀ m (h := h0 a)

nonrec theorem ContinuousWithinAt.zpow₀ (hf : ContinuousWithinAt f s a) (m : ℤ)
    {h0 : ∀ x, m < 0 → IsUnit (f x)} :
    ContinuousWithinAt (fun x => Checked.zpow (f x) m (h0 x)) s a :=
  hf.zpow₀ m (h := h0 a)

@[fun_prop]
theorem ContinuousOn.zpow₀ (hf : ContinuousOn f s) (m : ℤ) {h0 : ∀ x, m < 0 → IsUnit (f x)} :
    ContinuousOn (fun x => Checked.zpow (f x) m (h0 x)) s := fun a ha => (hf a ha).zpow₀ m

@[continuity, fun_prop]
theorem Continuous.zpow₀ (hf : Continuous f) (m : ℤ) {h0 : ∀ x, m < 0 → IsUnit (f x)} :
    Continuous fun x => Checked.zpow (f x) m (h0 x) :=
  (continuous_zpow₀ m).comp (hf.subtype_mk h0)

end ZPow
