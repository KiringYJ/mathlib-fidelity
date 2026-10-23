/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Kim Morrison
-/
module

public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.Order.Group.Pointwise.Interval
public import Mathlib.Algebra.Order.Nonneg.Field
public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Order.LocalExtr

/-!
# Topological fields

A topological division ring is a topological ring whose inversion function is continuous at every
non-zero element.

-/

@[expose] public section

variable {K : Type*} [DivisionRing K] [TopologicalSpace K]

/-- Left-multiplication by a nonzero element of a topological division ring is proper, i.e.,
inverse images of compact sets are compact. -/
theorem Filter.tendsto_cocompact_mul_left₀ [SeparatelyContinuousMul K] {a : K} (ha : a ≠ 0) :
    Filter.Tendsto (fun x : K => a * x) (Filter.cocompact K) (Filter.cocompact K) :=
  Filter.tendsto_cocompact_mul_left (Units.mk0 a ha).inv_mul

/-- Right-multiplication by a nonzero element of a topological division ring is proper, i.e.,
inverse images of compact sets are compact. -/
theorem Filter.tendsto_cocompact_mul_right₀ [SeparatelyContinuousMul K] {a : K} (ha : a ≠ 0) :
    Filter.Tendsto (fun x : K => x * a) (Filter.cocompact K) (Filter.cocompact K) :=
  Filter.tendsto_cocompact_mul_right (Units.mk0 a ha).mul_inv

/-- Compact Hausdorff topological fields are finite. This is not an instance, as it would apply to
every `Finite` goal, causing slowly failing typeclass search in some cases. -/
theorem DivisionRing.finite_of_compactSpace_of_t2Space {K} [DivisionRing K] [TopologicalSpace K]
    [IsTopologicalRing K] [CompactSpace K] [T2Space K] : Finite K := by
  suffices DiscreteTopology K by
    exact finite_of_compact_of_discrete
  rw [discreteTopology_iff_isOpen_singleton_zero]
  exact GroupWithZero.isOpen_singleton_zero

variable (K)

/-- A topological division ring is a division ring with a topology where all operations are
continuous, including inversion. -/
class IsTopologicalDivisionRing : Prop extends IsTopologicalRing K, ContinuousInv₀ K

section Subfield

variable {α : Type*} [Field α] [TopologicalSpace α] [IsTopologicalDivisionRing α]

/-- The (topological-space) closure of a subfield of a topological field is
itself a subfield. -/
def Subfield.topologicalClosure (K : Subfield α) : Subfield α :=
  { K.toSubring.topologicalClosure with
    carrier := _root_.closure (K : Set α)
    inv_mem' := fun u hu => by
      by_cases hu0 : (u : α) ∈ closure ({0} : Set α)
      · have hi : (↑u⁻¹ : α) ∈ closure ({0} : Set α) := by
          have h := (continuous_mul_const ((↑u⁻¹ : α) * ↑u⁻¹)).continuousAt.continuousWithinAt.mem_closure
            hu0 (t := ({0} : Set α)) (by
              intro y hy
              rcases Set.mem_singleton_iff.mp hy with rfl
              simp)
          simpa only [← mul_assoc, Units.mul_inv, one_mul] using h
        exact closure_mono (Set.singleton_subset_iff.mpr K.zero_mem) hi
      · have hsplit : (K : Set α) = ((K : Set α) \ {0}) ∪ {0} := by
          ext y
          by_cases hy : y = 0 <;> simp [hy, K.zero_mem]
        rw [hsplit, closure_union] at hu
        have hnonzero := hu.resolve_right hu0
        have himage : Subtype.val '' {y : {y : α | IsUnit y} | y.val ∈ K} =
            (K : Set α) \ {0} := by
          ext y
          constructor
          · rintro ⟨z, hz, rfl⟩
            exact ⟨hz, z.property.ne_zero⟩
          · intro hy
            exact ⟨⟨y, isUnit_iff_ne_zero.mpr hy.2⟩, hy.1, rfl⟩
        have hsub : (⟨(u : α), u.isUnit⟩ : {y : α | IsUnit y}) ∈
            closure {y : {y : α | IsUnit y} | y.val ∈ K} := by
          rw [closure_subtype, himage]
          exact hnonzero
        have hi := (continuousAt_inv₀ ⟨(u : α), u.isUnit⟩).continuousWithinAt.mem_closure
          hsub (t := (K : Set α)) (fun y hy ↦ K.inv_mem (u := y.property.unit) hy)
        simpa only [IsUnit.unit_of_val_units] using hi }

theorem Subfield.le_topologicalClosure (s : Subfield α) : s ≤ s.topologicalClosure :=
  _root_.subset_closure

theorem Subfield.isClosed_topologicalClosure (s : Subfield α) :
    IsClosed (s.topologicalClosure : Set α) :=
  isClosed_closure

theorem Subfield.topologicalClosure_minimal (s : Subfield α) {t : Subfield α} (h : s ≤ t)
    (ht : IsClosed (t : Set α)) : s.topologicalClosure ≤ t :=
  closure_minimal h ht

end Subfield

section Units

/-- In an ordered field, the units of the nonnegative elements are the positive elements. -/
@[simps!]
noncomputable def Nonneg.unitsHomeomorphPos (R : Type*) [DivisionSemiring R] [PartialOrder R]
    [IsStrictOrderedRing R] [PosMulReflectLT R]
    [TopologicalSpace R] [ContinuousInv₀ R] :
    (Nonneg R)ˣ ≃ₜ { r : R // 0 < r } where
  __ := Nonneg.unitsEquivPos R
  continuous_toFun := by
    rw [Topology.IsEmbedding.subtypeVal.continuous_iff]
    exact Continuous.subtype_val (p := (0 ≤ ·)) Units.continuous_val
  continuous_invFun := by
    rw [Units.continuous_iff]
    refine ⟨by fun_prop, ?_⟩
    suffices Continuous (fun x : {r : R | 0 < r} ↦
        (↑(Units.mk0 x.val x.property.ne')⁻¹ : R)) by
      simpa [Topology.IsEmbedding.subtypeVal.continuous_iff, Function.comp_def]
    exact ContinuousInv₀.continuous_inv.comp
      (continuous_subtype_val.subtype_mk fun x ↦ GroupWithZero.isUnit_of_ne_zero x.property.ne')

end Units

section affineHomeomorph

/-!
This section is about affine homeomorphisms from a topological field `𝕜` to itself.
Technically it does not require `𝕜` to be a topological field, a topological ring that
happens to be a field is enough.
-/


variable {𝕜 : Type*} [Field 𝕜] [TopologicalSpace 𝕜] [IsTopologicalRing 𝕜]

/--
The map `fun x => a * x + b`, as a homeomorphism from `𝕜` (a topological field) to itself,
when `a ≠ 0`.
-/
@[simps]
noncomputable def affineHomeomorph (a b : 𝕜) (h : a ≠ 0) : 𝕜 ≃ₜ 𝕜 where
  toFun x := a * x + b
  invFun y := (y - b) /ₚ Units.mk0 a h
  left_inv x := by rw [add_sub_cancel_right, mul_comm a x, mul_divp_cancel]
  right_inv y := by rw [mul_comm a, divp_mul_cancel, sub_add_cancel]
  continuous_toFun := (continuous_const.mul continuous_id).add continuous_const
  continuous_invFun := (continuous_id.sub continuous_const).mul_const _

theorem affineHomeomorph_image_Icc {𝕜 : Type*}
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜]
    [IsTopologicalRing 𝕜] (a b c d : 𝕜) (h : 0 < a) :
    affineHomeomorph a b h.ne' '' Set.Icc c d = Set.Icc (a * c + b) (a * d + b) := by
  simp [h]

theorem affineHomeomorph_image_Ico {𝕜 : Type*}
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜]
    [IsTopologicalRing 𝕜] (a b c d : 𝕜) (h : 0 < a) :
    affineHomeomorph a b h.ne' '' Set.Ico c d = Set.Ico (a * c + b) (a * d + b) := by
  simp [h]

theorem affineHomeomorph_image_Ioc {𝕜 : Type*}
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜]
    [IsTopologicalRing 𝕜] (a b c d : 𝕜) (h : 0 < a) :
    affineHomeomorph a b h.ne' '' Set.Ioc c d = Set.Ioc (a * c + b) (a * d + b) := by
  simp [h]

theorem affineHomeomorph_image_Ioo {𝕜 : Type*}
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜]
    [IsTopologicalRing 𝕜] (a b c d : 𝕜) (h : 0 < a) :
    affineHomeomorph a b h.ne' '' Set.Ioo c d = Set.Ioo (a * c + b) (a * d + b) := by
  simp [h]

end affineHomeomorph

section LocalExtr

variable {α β : Type*} [TopologicalSpace α]
  [Semifield β] [LinearOrder β] [IsStrictOrderedRing β] {a : α}

open scoped Topology

theorem IsLocalMin.inv {f : α → β} {a : α} (h1 : IsLocalMin f a)
    (h2 : ∀ᶠ z in 𝓝 a, 0 < f z) :
    IsLocalMax (fun z : {z : α | IsUnit (f z)} ↦ (↑z.property.unit⁻¹ : β))
      ⟨a, GroupWithZero.isUnit_of_ne_zero h2.self_of_nhds.ne'⟩ := by
  have hval := continuous_subtype_val.tendsto
    (⟨a, GroupWithZero.isUnit_of_ne_zero h2.self_of_nhds.ne'⟩ : {z : α | IsUnit (f z)})
  filter_upwards [hval.eventually h1, hval.eventually h2] with z hmin hz
  exact (Units.inv_le_inv (u := z.property.unit)
    (v := (GroupWithZero.isUnit_of_ne_zero h2.self_of_nhds.ne').unit) hz h2.self_of_nhds).mpr hmin

end LocalExtr

section Preconnected

/-! Some results about functions on preconnected sets valued in a ring or field with a topology. -/

open Set

variable {α 𝕜 : Type*} {f g : α → 𝕜} {S : Set α} [TopologicalSpace α] [TopologicalSpace 𝕜]
  [T1Space 𝕜]

/-- If `f` is a function `α → 𝕜` which is continuous on a preconnected set `S`, and
`f ^ 2 = 1` on `S`, then either `f = 1` on `S`, or `f = -1` on `S`. -/
theorem IsPreconnected.eq_one_or_eq_neg_one_of_sq_eq [Ring 𝕜] [NoZeroDivisors 𝕜]
    (hS : IsPreconnected S) (hf : ContinuousOn f S) (hsq : EqOn (f ^ 2) 1 S) :
    EqOn f 1 S ∨ EqOn f (-1) S := by
  have hmaps : MapsTo f S {1, -1} := by
    simpa only [EqOn, Pi.one_apply, Pi.pow_apply, sq_eq_one_iff] using! hsq
  simpa using! hS.eqOn_const_of_mapsTo (toFinite _).isDiscrete hf hmaps

/-- If `f, g` are functions `α → 𝕜`, both continuous on a preconnected set `S`, with
`f ^ 2 = g ^ 2` on `S`, and `g z ≠ 0` all `z ∈ S`, then either `f = g` or `f = -g` on
`S`. -/
theorem IsPreconnected.eq_or_eq_neg_of_sq_eq [Field 𝕜] [ContinuousInv₀ 𝕜] [ContinuousMul 𝕜]
    (hS : IsPreconnected S) (hf : ContinuousOn f S) (hg : ContinuousOn g S)
    (hsq : EqOn (f ^ 2) (g ^ 2) S) (hg_ne : ∀ {x : α}, x ∈ S → g x ≠ 0) :
    EqOn f g S ∨ EqOn f (-g) S := by
  letI : PreconnectedSpace S := isPreconnected_iff_preconnectedSpace.mp hS
  let u (x : S) : 𝕜ˣ := Units.mk0 (g x.val) (hg_ne x.property)
  have hfc : Continuous (fun x : S ↦ f x.val) := continuousOn_iff_continuous_domRestrict.mp hf
  have hgc : Continuous (fun x : S ↦ g x.val) := continuousOn_iff_continuous_domRestrict.mp hg
  have hquot : Continuous (fun x : S ↦ f x.val /ₚ u x) :=
    hfc.div hgc (fun x ↦ GroupWithZero.isUnit_of_ne_zero (hg_ne x.property))
  have hsquare : EqOn ((fun x : S ↦ f x.val /ₚ u x) ^ 2) 1 Set.univ := by
    intro x _
    change (f x.val * (↑(u x)⁻¹ : 𝕜)) ^ 2 = 1
    rw [mul_pow, hsq x.property, ← mul_pow,
      show g x.val * (↑(u x)⁻¹ : 𝕜) = 1 from (u x).mul_inv, one_pow]
  rcases isPreconnected_univ.eq_one_or_eq_neg_one_of_sq_eq hquot.continuousOn hsquare with h | h
  · left
    intro x hx
    exact divp_eq_one_iff_eq.mp (h (Set.mem_univ (⟨x, hx⟩ : S)))
  · right
    intro x hx
    have hh := (divp_eq_iff_mul_eq).mp (h (Set.mem_univ (⟨x, hx⟩ : S)))
    simpa only [Pi.neg_apply, Pi.one_apply, neg_one_mul] using hh

/-- If `f, g` are functions `α → 𝕜`, both continuous on a preconnected set `S`, with
`f ^ 2 = g ^ 2` on `S`, and `g z ≠ 0` all `z ∈ S`, then as soon as `f = g` holds at
one point of `S` it holds for all points. -/
theorem IsPreconnected.eq_of_sq_eq [Field 𝕜] [ContinuousInv₀ 𝕜] [ContinuousMul 𝕜]
    (hS : IsPreconnected S) (hf : ContinuousOn f S) (hg : ContinuousOn g S)
    (hsq : EqOn (f ^ 2) (g ^ 2) S) (hg_ne : ∀ {x : α}, x ∈ S → g x ≠ 0) {y : α} (hy : y ∈ S)
    (hy' : f y = g y) : EqOn f g S := fun x hx => by
  rcases hS.eq_or_eq_neg_of_sq_eq hf hg @hsq @hg_ne with (h | h)
  · exact h hx
  · rw [h _, Pi.neg_apply, neg_eq_iff_add_eq_zero, ← two_mul, mul_eq_zero,
      (iff_of_eq (iff_false _)).2 (hg_ne _)] at hy' ⊢ <;> assumption

end Preconnected

section ContinuousSMul

variable {F : Type*} [DivisionRing F] [TopologicalSpace F] [IsTopologicalRing F]
    (X : Type*) [TopologicalSpace X] [MulAction F X] [ContinuousSMul F X]

instance Subfield.continuousSMul (M : Subfield F) : ContinuousSMul M X :=
  Subring.continuousSMul M.toSubring X

end ContinuousSMul
