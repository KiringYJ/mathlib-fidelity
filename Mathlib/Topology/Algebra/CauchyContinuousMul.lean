/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module

public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import Mathlib.Topology.UniformSpace.CauchyContinuous

/-!
# Cauchy continuous operations

The classes in this file state that an operation on a uniform space is Cauchy continuous: it maps
Cauchy filters to Cauchy filters.  This is the condition under which the operation extends
continuously to the completion (`CauchyContinuous.continuous_extend`), so it is the domain of the
corresponding operation on `UniformSpace.Completion`.

## Main definitions

* `CauchyContinuousMul M`, `CauchyContinuousAdd M`: multiplication, respectively addition, is
  Cauchy continuous as a map of two variables.
* `CauchyContinuousInv G`, `CauchyContinuousNeg G`: inversion, respectively negation, is Cauchy
  continuous.
* `CauchyContinuousDiv G`, `CauchyContinuousSub G`: division, respectively subtraction, is Cauchy
  continuous as a map of two variables.

A uniform group has all three, since its operations are uniformly continuous.  Multiplication on a
topological ring whose uniform structure is that of its additive group is Cauchy continuous but
not uniformly continuous in general, as on `ℝ`; that instance is in
`Mathlib/Topology/Algebra/UniformRing.lean`.

A Cauchy continuous operation is continuous (`CauchyContinuousMul.continuousMul` and its
siblings), and on a complete space a continuous operation is Cauchy continuous
(`CauchyContinuousMul.of_continuousMul`), so the classes differ from the continuity classes only
on spaces that are not complete, which is where completions are taken.
-/

@[expose] public section

/-- Addition on a uniform space is Cauchy continuous: it maps Cauchy filters on the product to
Cauchy filters. -/
class CauchyContinuousAdd (M : Type*) [UniformSpace M] [Add M] : Prop where
  cauchyContinuous_add : CauchyContinuous fun p : M × M ↦ p.1 + p.2

/-- Multiplication on a uniform space is Cauchy continuous: it maps Cauchy filters on the product
to Cauchy filters. -/
@[to_additive]
class CauchyContinuousMul (M : Type*) [UniformSpace M] [Mul M] : Prop where
  cauchyContinuous_mul : CauchyContinuous fun p : M × M ↦ p.1 * p.2

/-- Negation on a uniform space is Cauchy continuous. -/
class CauchyContinuousNeg (G : Type*) [UniformSpace G] [Neg G] : Prop where
  cauchyContinuous_neg : CauchyContinuous fun a : G ↦ -a

/-- Inversion on a uniform space is Cauchy continuous. -/
@[to_additive]
class CauchyContinuousInv (G : Type*) [UniformSpace G] [Inv G] : Prop where
  cauchyContinuous_inv : CauchyContinuous fun a : G ↦ a⁻¹

/-- Subtraction on a uniform space is Cauchy continuous: it maps Cauchy filters on the product to
Cauchy filters. -/
class CauchyContinuousSub (G : Type*) [UniformSpace G] [Sub G] : Prop where
  cauchyContinuous_sub : CauchyContinuous fun p : G × G ↦ p.1 - p.2

/-- Right division in a group maps Cauchy filters on the product to Cauchy filters. -/
class CauchyContinuousDiv (G : Type*) [UniformSpace G] [Group G] : Prop where
  cauchyContinuous_div : CauchyContinuous fun p : G × G ↦ p.1 / p.2

export CauchyContinuousAdd (cauchyContinuous_add)
export CauchyContinuousMul (cauchyContinuous_mul)
export CauchyContinuousNeg (cauchyContinuous_neg)
export CauchyContinuousInv (cauchyContinuous_inv)
export CauchyContinuousSub (cauchyContinuous_sub)
export CauchyContinuousDiv (cauchyContinuous_div)

/-- Apply a Cauchy continuous binary operation to two Cauchy continuous maps. -/
theorem CauchyContinuous.comp₂ {X A B C : Type*} [UniformSpace X] [UniformSpace A]
    [UniformSpace B] [UniformSpace C] {op : A → B → C}
    (hop : CauchyContinuous (Function.uncurry op)) {f : X → A} {g : X → B}
    (hf : CauchyContinuous f) (hg : CauchyContinuous g) :
    CauchyContinuous fun x ↦ op (f x) (g x) := by
  apply hop.comp (f := fun x ↦ (f x, g x))
  intro F hF
  apply cauchy_prod_iff.2
  simpa only [Filter.map_map, Function.comp_def] using And.intro (hf hF) (hg hF)

section IsUniformGroup

variable {G : Type*} [UniformSpace G] [Group G] [IsUniformGroup G]

@[to_additive]
instance (priority := 100) IsUniformGroup.cauchyContinuousMul : CauchyContinuousMul G :=
  ⟨uniformContinuous_mul.cauchyContinuous⟩

@[to_additive]
instance (priority := 100) IsUniformGroup.cauchyContinuousInv : CauchyContinuousInv G :=
  ⟨uniformContinuous_inv.cauchyContinuous⟩

instance (priority := 100) IsUniformGroup.cauchyContinuousDiv : CauchyContinuousDiv G :=
  ⟨uniformContinuous_div.cauchyContinuous⟩

instance (priority := 100) IsUniformAddGroup.cauchyContinuousSub {A : Type*}
    [UniformSpace A] [AddGroup A] [IsUniformAddGroup A] : CauchyContinuousSub A :=
  ⟨uniformContinuous_sub.cauchyContinuous⟩

end IsUniformGroup

section Continuity

variable {M : Type*} [UniformSpace M]

/-- A Cauchy continuous multiplication is continuous. -/
@[to_additive /-- A Cauchy continuous addition is continuous. -/]
theorem CauchyContinuousMul.continuousMul [Mul M] [CauchyContinuousMul M] : ContinuousMul M :=
  ⟨cauchyContinuous_mul.continuous⟩

/-- A Cauchy continuous inversion is continuous. -/
@[to_additive /-- A Cauchy continuous negation is continuous. -/]
theorem CauchyContinuousInv.continuousInv [Inv M] [CauchyContinuousInv M] : ContinuousInv M :=
  ⟨cauchyContinuous_inv.continuous⟩

/-- Cauchy continuous group division is continuous. -/
theorem CauchyContinuousDiv.continuousDiv [Group M] [CauchyContinuousDiv M] : ContinuousDiv M :=
  ⟨cauchyContinuous_div.continuous⟩

/-- A Cauchy continuous subtraction is continuous. -/
theorem CauchyContinuousSub.continuousSub [Sub M] [CauchyContinuousSub M] : ContinuousSub M :=
  ⟨cauchyContinuous_sub.continuous⟩

/-- On a complete space, a continuous multiplication is Cauchy continuous. -/
@[to_additive /-- On a complete space, a continuous addition is Cauchy continuous. -/]
theorem CauchyContinuousMul.of_continuousMul [Mul M] [ContinuousMul M] [CompleteSpace M] :
    CauchyContinuousMul M :=
  ⟨(continuous_mul.cauchyContinuous_comp cauchyContinuous_id :
    CauchyContinuous ((fun p : M × M ↦ p.1 * p.2) ∘ id))⟩

/-- On a complete space, a continuous inversion is Cauchy continuous. -/
@[to_additive /-- On a complete space, a continuous negation is Cauchy continuous. -/]
theorem CauchyContinuousInv.of_continuousInv [Inv M] [ContinuousInv M] [CompleteSpace M] :
    CauchyContinuousInv M :=
  ⟨(continuous_inv.cauchyContinuous_comp cauchyContinuous_id :
    CauchyContinuous ((fun a : M ↦ a⁻¹) ∘ id))⟩

/-- On a complete group, continuous right division is Cauchy continuous. -/
theorem CauchyContinuousDiv.of_continuousDiv [Group M] [ContinuousDiv M] [CompleteSpace M] :
    CauchyContinuousDiv M :=
  ⟨(continuous_div'.cauchyContinuous_comp cauchyContinuous_id :
    CauchyContinuous ((fun p : M × M ↦ p.1 / p.2) ∘ id))⟩

/-- On a complete space, a continuous subtraction is Cauchy continuous. -/
theorem CauchyContinuousSub.of_continuousSub [Sub M] [ContinuousSub M] [CompleteSpace M] :
    CauchyContinuousSub M :=
  ⟨(continuous_sub.cauchyContinuous_comp cauchyContinuous_id :
    CauchyContinuous ((fun p : M × M ↦ p.1 - p.2) ∘ id))⟩

end Continuity
