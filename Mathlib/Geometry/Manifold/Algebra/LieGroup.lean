/-
Copyright (c) 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/
module

public import Mathlib.Geometry.Manifold.Algebra.Monoid

/-!
# Lie groups

A Lie group is a group that is also a `C^n` manifold, in which the group operations of
multiplication and inversion are `C^n` maps. Regularity of the group multiplication means that
multiplication is a `C^n` mapping of the product manifold `G` × `G` into `G`.

Note that, since a manifold here is not second-countable and Hausdorff, a Lie group here is not
guaranteed to be second-countable (even though it can be proved that it is Hausdorff). Note also
that Lie groups here are not necessarily finite dimensional.

## Main definitions

* `LieAddGroup I G` : a Lie additive group where `G` is a manifold on the model with corners `I`.
* `LieGroup I G` : a Lie multiplicative group where `G` is a manifold on the model with corners `I`.
* `ContMDiffInv₀`: inversion in a monoid is `C^n` on its invertibility domain.


## Main results
* `ContMDiff.inv`, `ContMDiff.div` and variants: point-wise inversion and division of maps `M → G`
  is `C^n`.
* `ContMDiff.inv₀` and variants: if `ContMDiffInv₀ I n N`, point-wise inversion of `C^n`
  maps `f : M → N` is `C^n` on the domain where the values of `f` are invertible.
* `ContMDiff.div₀` and variants: if also `ContMDiffMul I n N`, similar results hold for point-wise
  division on its domain.
* `instNormedSpaceLieAddGroup` : a normed vector space over a nontrivially normed field
  is an additive Lie group.
* `Instances/UnitsOfNormedAlgebra` shows that the group of units of a complete normed `𝕜`-algebra
  is a multiplicative Lie group.

## Implementation notes

A priori, a Lie group here is a manifold with corners.

The definition of Lie group cannot require `I : ModelWithCorners 𝕜 E E` with the same space as the
model space and as the model vector space, as one might hope, because in the product situation,
the model space is `ModelProd E E'` and the model vector space is `E × E'`, which are not the same,
so the definition does not apply. Hence the definition should be more general, allowing
`I : ModelWithCorners 𝕜 E H`.
-/

public section

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

-- See note [Design choices about smooth algebraic structures]
/-- An additive Lie group is a group and a `C^n` manifold at the same time in which
the addition and negation operations are `C^n`. -/
class LieAddGroup {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] (I : ModelWithCorners 𝕜 E H)
    (n : ℕ∞ω) (G : Type*)
    [AddGroup G] [TopologicalSpace G] [ChartedSpace H G] : Prop extends ContMDiffAdd I n G where
  /-- Negation is smooth in an additive Lie group. -/
  contMDiff_neg : CMDiff n fun a : G ↦ -a

-- See note [Design choices about smooth algebraic structures]
/-- A (multiplicative) Lie group is a group and a `C^n` manifold at the same time in which
the multiplication and inverse operations are `C^n`. -/
@[to_additive]
class LieGroup {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] (I : ModelWithCorners 𝕜 E H)
    (n : ℕ∞ω) (G : Type*)
    [Group G] [TopologicalSpace G] [ChartedSpace H G] : Prop extends ContMDiffMul I n G where
  /-- Inversion is smooth in a Lie group. -/
  contMDiff_inv : CMDiff n fun a : G ↦ a⁻¹

/-!
  ### Smoothness of inversion, negation, division and subtraction

  Let `f : M → G` be a `C^n` function into a Lie group, then `f` is point-wise
  invertible with smooth inverse `f`. If `f` and `g` are two such functions, the quotient
  `f / g` (i.e., the point-wise product of `f` and the point-wise inverse of `g`) is also `C^n`. -/
section PointwiseDivision

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω} {G : Type*}
  [TopologicalSpace G] [ChartedSpace H G] [Group G] {E' : Type*}
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M : Type*} [TopologicalSpace M] [ChartedSpace H' M]

@[to_additive]
protected theorem LieGroup.of_le {m n : ℕ∞ω} (hmn : m ≤ n)
    [h : LieGroup I n G] : LieGroup I m G := by
  have : ContMDiffMul I m G := ContMDiffMul.of_le hmn
  exact ⟨h.contMDiff_inv.of_le hmn⟩

@[to_additive]
instance {a : ℕ∞ω} [LieGroup I ∞ G] [h : ENat.LEInfty a] : LieGroup I a G :=
  LieGroup.of_le h.out

@[to_additive]
instance {a : ℕ∞ω} [LieGroup I ω G] : LieGroup I a G :=
  LieGroup.of_le le_top

@[to_additive]
instance [IsTopologicalGroup G] : LieGroup I 0 G := by
  constructor
  rw [contMDiff_zero_iff]
  exact continuous_inv

@[to_additive]
instance [LieGroup I 2 G] : LieGroup I 1 G :=
  LieGroup.of_le one_le_two

variable [LieGroup I n G]

section

variable (I n)

/-- In a Lie group, inversion is `C^n`. -/
@[to_additive /-- In an additive Lie group, inversion is a smooth map. -/]
theorem contMDiff_inv : CMDiff n fun x : G ↦ x⁻¹ :=
  LieGroup.contMDiff_inv

include I n in
/-- A Lie group is a topological group. This is not an instance for technical reasons,
see note [Design choices about smooth algebraic structures]. -/
@[to_additive /-- An additive Lie group is an additive topological group. This is not an instance
for technical reasons, see note [Design choices about smooth algebraic structures]. -/]
theorem topologicalGroup_of_lieGroup : IsTopologicalGroup G :=
  { continuousMul_of_contMDiffMul I n with continuous_inv := (contMDiff_inv I n).continuous }

end

@[to_additive]
theorem ContMDiffWithinAt.inv {f : M → G} {s : Set M} {x₀ : M}
    (hf : CMDiffAt[s] n f x₀) : CMDiffAt[s] n (fun x ↦ (f x)⁻¹) x₀ :=
  (contMDiff_inv I n).contMDiffAt.contMDiffWithinAt.comp x₀ hf <| Set.mapsTo_univ _ _

@[to_additive]
theorem ContMDiffAt.inv {f : M → G} {x₀ : M} (hf : CMDiffAt n f x₀) :
    CMDiffAt n (fun x ↦ (f x)⁻¹) x₀ :=
  (contMDiff_inv I n).contMDiffAt.comp x₀ hf

@[to_additive]
theorem ContMDiffOn.inv {f : M → G} {s : Set M} (hf : CMDiff[s] n f) :
    CMDiff[s] n (fun x ↦ (f x)⁻¹) := fun x hx ↦ (hf x hx).inv

@[to_additive]
theorem ContMDiff.inv {f : M → G} (hf : CMDiff n f) : CMDiff n fun x ↦ (f x)⁻¹ :=
  fun x ↦ (hf x).inv

@[to_additive]
theorem ContMDiffWithinAt.div {f g : M → G} {s : Set M} {x₀ : M}
    (hf : CMDiffAt[s] n f x₀) (hg : CMDiffAt[s] n g x₀) :
    CMDiffAt[s] n (fun x ↦ f x / g x) x₀ := by
  simp_rw [div_eq_mul_inv]; exact hf.mul hg.inv

@[to_additive]
theorem ContMDiffAt.div {f g : M → G} {x₀ : M} (hf : CMDiffAt n f x₀)
    (hg : CMDiffAt n g x₀) : CMDiffAt n (fun x ↦ f x / g x) x₀ := by
  simp_rw [div_eq_mul_inv]; exact hf.mul hg.inv

@[to_additive]
theorem ContMDiffOn.div {f g : M → G} {s : Set M} (hf : CMDiff[s] n f)
    (hg : CMDiff[s] n g) : CMDiff[s] n (fun x ↦ f x / g x) := by
  simp_rw [div_eq_mul_inv]; exact hf.mul hg.inv

@[to_additive]
theorem ContMDiff.div {f g : M → G} (hf : CMDiff n f) (hg : CMDiff n g) :
    CMDiff n fun x ↦ f x / g x := by simp_rw [div_eq_mul_inv]; exact hf.mul hg.inv

end PointwiseDivision

/-! Binary product of Lie groups -/
section Product

-- Instance of product group
@[to_additive]
instance Prod.instLieGroup {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ∞ω}
    {H : Type*} [TopologicalSpace H] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H} {G : Type*}
    [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I n G] {E' : Type*}
    [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
    {I' : ModelWithCorners 𝕜 E' H'} {G' : Type*} [TopologicalSpace G'] [ChartedSpace H' G']
    [Group G'] [LieGroup I' n G'] : LieGroup (I.prod I') n (G × G') :=
  { ContMDiffMul.prod _ _ _ _ with contMDiff_inv := contMDiff_fst.inv.prodMk contMDiff_snd.inv }

end Product

/-! ### Normed spaces are Lie groups -/

instance instNormedSpaceLieAddGroup {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ∞ω}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] : LieAddGroup 𝓘(𝕜, E) n E where
  contMDiff_neg := contDiff_neg.contMDiff

/-! ## Smooth inversion and division on the invertibility domain -/

section ContMDiffInv₀

-- See note [Design choices about smooth algebraic structures]
/-- Inversion is smooth on the set of invertible elements. The smoothness condition is
expressed using any ambient representative agreeing with the checked inverse on that set. -/
class ContMDiffInv₀ {𝕜 : Type*} [NontriviallyNormedField 𝕜] {H : Type*} [TopologicalSpace H]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] (I : ModelWithCorners 𝕜 E H)
    (n : ℕ∞ω) (G : Type*) [Monoid G] [TopologicalSpace G] [ChartedSpace H G] : Prop where
  /-- A representative of inversion on the units is smooth there. -/
  contMDiffOn_inv₀ (g : G → G) (hg : ∀ x (hx : IsUnit x), g x = Checked.inv x hx) :
    CMDiff[{x : G | IsUnit x}] n g

instance {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ∞ω} : ContMDiffInv₀ 𝓘(𝕜) n 𝕜 where
  contMDiffOn_inv₀ g hg := by
    rw [contMDiffOn_iff_contDiffOn]
    apply contDiffOn_inv
    intro y
    rw [Units.val_inv_eq_inv_val₀]
    exact hg y y.isUnit

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ∞ω}
  {H : Type*} [TopologicalSpace H] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H} {G : Type*}
  [TopologicalSpace G] [ChartedSpace H G] [Monoid G] {E' : Type*}
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M : Type*} [TopologicalSpace M] [ChartedSpace H' M]
  {f : M → G}

protected theorem ContMDiffInv₀.of_le {m n : ℕ∞ω} (hmn : m ≤ n)
    [h : ContMDiffInv₀ I n G] : ContMDiffInv₀ I m G :=
  ⟨fun g hg ↦ (h.contMDiffOn_inv₀ g hg).of_le hmn⟩

instance {a : ℕ∞ω} [ContMDiffInv₀ I ∞ G] [h : ENat.LEInfty a] : ContMDiffInv₀ I a G :=
  ContMDiffInv₀.of_le h.out

instance {a : ℕ∞ω} [ContMDiffInv₀ I ω G] : ContMDiffInv₀ I a G :=
  ContMDiffInv₀.of_le le_top

instance [ContinuousInv₀ G] : ContMDiffInv₀ I 0 G := by
  constructor
  intro g hg
  rw [contMDiffOn_zero_iff, continuousOn_iff_continuous_domRestrict]
  change Continuous (fun x : {x : G | IsUnit x} ↦ g x.val)
  have he : (fun x : {x : G | IsUnit x} ↦ g x.val) = fun x ↦ Checked.inv x.val x.2 :=
    funext fun x ↦ hg x x.2
  rw [he]
  exact ContinuousInv₀.continuous_inv

instance [ContMDiffInv₀ I 2 G] : ContMDiffInv₀ I 1 G :=
  ContMDiffInv₀.of_le one_le_two

variable [ContMDiffInv₀ I n G]

theorem contMDiffOn_inv₀ (g : G → G) (hg : ∀ x (hx : IsUnit x), g x = Checked.inv x hx) :
    CMDiff[{x : G | IsUnit x}] n g :=
  ContMDiffInv₀.contMDiffOn_inv₀ g hg

/-- A representative of inversion is smooth at points with a neighborhood of invertible elements. -/
theorem contMDiffAt_inv₀ {g : G → G} {x : G} (hx : {x : G | IsUnit x} ∈ 𝓝 x)
    (hg : ∀ y (hy : IsUnit y), g y = Checked.inv y hy) : ContMDiffAt I I n g x :=
  (contMDiffOn_inv₀ g hg x (mem_of_mem_nhds hx)).contMDiffAt hx

include I n in
/-- Smooth inversion is continuous on the subtype of invertible elements. -/
theorem continuousInv₀_of_contMDiffInv₀ : ContinuousInv₀ G := by
  classical
  let g (x : G) := if hx : IsUnit x then Checked.inv x hx else x
  have hg (x : G) (hx : IsUnit x) : g x = Checked.inv x hx := dite_eq_left hx
  have hcont := continuousOn_iff_continuous_domRestrict.mp
    (contMDiffOn_inv₀ (I := I) (n := n) g hg).continuousOn
  change Continuous (fun x : {x : G | IsUnit x} ↦ g x.val) at hcont
  have he : (fun x : {x : G | IsUnit x} ↦ g x.val) = fun x ↦ Checked.inv x.val x.2 :=
    funext fun x ↦ hg x x.2
  rw [he] at hcont
  exact ⟨hcont⟩

variable {s : Set M} {a : M}

/-- A representative of the checked inverse of a smooth function is smooth locally. -/
theorem ContMDiffWithinAt.inv₀ {q : M → G} (hf : CMDiffAt[s] n f a)
    (hq : ∀ᶠ x in 𝓝[insert a s] a, ∃ hx : IsUnit (f x), q x = Checked.inv (f x) hx) :
    CMDiffAt[s] n q a := by
  classical
  let r (x : G) := if hx : IsUnit x then Checked.inv x hx else x
  have hr (x : G) (hx : IsUnit x) : r x = Checked.inv x hx := dite_eq_left hx
  obtain ⟨ha, hqa⟩ := mem_of_mem_nhdsWithin (mem_insert a s) hq
  have hq' := hq.filter_mono (nhdsWithin_mono a (subset_insert a s))
  let t := s ∩ {x | IsUnit (f x)}
  have ht : t ∈ 𝓝[s] a := Filter.inter_mem self_mem_nhdsWithin
    (hq'.mono (fun _ ⟨hx, _⟩ ↦ hx))
  have hc : CMDiffAt[t] n (r ∘ f) a :=
    (contMDiffOn_inv₀ r hr (f a) ha).comp a (hf.mono inter_subset_left) (fun _ hx ↦ hx.2)
  refine (hc.mono_of_mem_nhdsWithin ht).congr_of_eventuallyEq ?_ (hqa.trans (hr (f a) ha).symm)
  filter_upwards [hq'] with x hx
  obtain ⟨hu, he⟩ := hx
  exact he.trans (hr (f x) hu).symm

theorem ContMDiffAt.inv₀ {q : M → G} (hf : CMDiffAt n f a)
    (hq : ∀ᶠ x in 𝓝 a, ∃ hx : IsUnit (f x), q x = Checked.inv (f x) hx) : CMDiffAt n q a := by
  rw [← contMDiffWithinAt_univ] at hf ⊢
  apply hf.inv₀
  simpa only [insert_eq_of_mem (mem_univ a), nhdsWithin_univ] using hq

theorem ContMDiff.inv₀ (hf : CMDiff n f) {h : ∀ x, IsUnit (f x)} :
    CMDiff n (fun x ↦ Checked.inv (f x) (h x)) :=
  fun x ↦ (hf x).inv₀ (.of_forall fun y ↦ ⟨h y, rfl⟩)

theorem ContMDiffOn.inv₀ {q : M → G} (hf : CMDiff[s] n f)
    (hq : ∀ x ∈ s, ∃ hx : IsUnit (f x), q x = Checked.inv (f x) hx) : CMDiff[s] n q := by
  intro x hx
  apply (hf x hx).inv₀
  rw [insert_eq_of_mem hx]
  filter_upwards [self_mem_nhdsWithin] with y hy using hq y hy

end ContMDiffInv₀

/-! ### Smoothness of checked quotients -/
section Div

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ∞ω}
  {H : Type*} [TopologicalSpace H] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {I : ModelWithCorners 𝕜 E H} {G : Type*}
  [TopologicalSpace G] [ChartedSpace H G] [Monoid G] [ContMDiffInv₀ I n G]
  [ContMDiffMul I n G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M : Type*} [TopologicalSpace M] [ChartedSpace H' M]
  {f g q : M → G} {s : Set M} {a : M}

/-- A representative of a checked quotient is smooth wherever both factors are smooth. -/
theorem ContMDiffWithinAt.div₀ (hf : CMDiffAt[s] n f a) (hg : CMDiffAt[s] n g a)
    (hq : ∀ᶠ x in 𝓝[insert a s] a, ∃ hx : IsUnit (g x), q x = Checked.div (f x) (g x) hx) :
    CMDiffAt[s] n q a := by
  classical
  let r (x : M) := if hx : IsUnit (g x) then Checked.inv (g x) hx else g x
  have hr : CMDiffAt[s] n r a := hg.inv₀ (hq.mono fun x ⟨hx, _⟩ ↦ ⟨hx, dite_eq_left hx⟩)
  have heq (x : M) (hx : ∃ hx : IsUnit (g x), q x = Checked.div (f x) (g x) hx) :
      q x = f x * r x := by
    obtain ⟨hu, he⟩ := hx
    simpa only [r, dite_eq_left hu, div_eq_mul_inv₀] using he
  have hqa : ∃ hx : IsUnit (g a), q a = Checked.div (f a) (g a) hx :=
    mem_of_mem_nhdsWithin (t := {x : M | ∃ hx : IsUnit (g x), q x = Checked.div (f x) (g x) hx})
      (mem_insert a s) hq
  refine (hf.mul hr).congr_of_eventuallyEq ?_ (heq a hqa)
  exact (hq.filter_mono (nhdsWithin_mono a (subset_insert a s))).mono heq

theorem ContMDiffOn.div₀ (hf : CMDiff[s] n f) (hg : CMDiff[s] n g)
    (hq : ∀ x ∈ s, ∃ hx : IsUnit (g x), q x = Checked.div (f x) (g x) hx) : CMDiff[s] n q := by
  intro x hx
  apply (hf x hx).div₀ (hg x hx)
  rw [insert_eq_of_mem hx]
  filter_upwards [self_mem_nhdsWithin] with y hy using hq y hy

theorem ContMDiffAt.div₀ (hf : CMDiffAt n f a) (hg : CMDiffAt n g a)
    (hq : ∀ᶠ x in 𝓝 a, ∃ hx : IsUnit (g x), q x = Checked.div (f x) (g x) hx) : CMDiffAt n q a := by
  rw [← contMDiffWithinAt_univ] at hf hg ⊢
  apply hf.div₀ hg
  simpa only [insert_eq_of_mem (mem_univ a), nhdsWithin_univ] using hq

theorem ContMDiff.div₀ (hf : CMDiff n f) (hg : CMDiff n g) {h : ∀ x, IsUnit (g x)} :
    CMDiff n (fun x ↦ Checked.div (f x) (g x) (h x)) :=
  fun x ↦ (hf x).div₀ (hg x) (.of_forall fun y ↦ ⟨h y, rfl⟩)

end Div
