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

A topological division ring is a topological ring whose inversion is continuous on the subspace
of nonzero elements, see `ContinuousInv₀`.

-/

@[expose] public section

variable {K : Type*} [DivisionRing K] [TopologicalSpace K]

/-- Left-multiplication by a nonzero element of a topological division ring is proper, i.e.,
inverse images of compact sets are compact. -/
theorem Filter.tendsto_cocompact_mul_left₀ [SeparatelyContinuousMul K] {a : K} (ha : a ≠ 0) :
    Filter.Tendsto (fun x : K => a * x) (Filter.cocompact K) (Filter.cocompact K) :=
  Filter.tendsto_cocompact_mul_left (inv_mul_cancel₀ (ha := ha.isUnit))

/-- Right-multiplication by a nonzero element of a topological division ring is proper, i.e.,
inverse images of compact sets are compact. -/
theorem Filter.tendsto_cocompact_mul_right₀ [SeparatelyContinuousMul K] {a : K} (ha : a ≠ 0) :
    Filter.Tendsto (fun x : K => x * a) (Filter.cocompact K) (Filter.cocompact K) :=
  Filter.tendsto_cocompact_mul_right (mul_inv_cancel₀ (ha := ha.isUnit))

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
    inv_mem' := fun {x} {hx} hxK => by
      by_cases h0 : x ∈ closure ({0} : Set α)
      · -- Without a separation axiom, a nonzero element can lie in the closure of `{0}`. Its
        -- inverse `x * (x⁻¹ * x⁻¹)` then lies there too, by continuity of multiplication.
        refine closure_mono (Set.singleton_subset_iff.mpr K.zero_mem) ?_
        have h := map_mem_closure (continuous_mul_const (x⁻¹ * x⁻¹)) h0 (t := {0})
          (Set.mapsTo_singleton.mpr (zero_mul _))
        rwa [mul_inv_cancel_left₀] at h
      · -- Otherwise `x` lies in the closure of the nonzero elements of `K`, and inversion is
        -- continuous on the subspace of nonzero elements.
        have hK : (K : Set α) ⊆ ((K : Set α) \ {0}) ∪ {0} := fun y hy => by
          by_cases hy0 : y = 0
          · exact Or.inr hy0
          · exact Or.inl ⟨hy, hy0⟩
        have hnonzero : x ∈ closure ((K : Set α) \ {0}) := by
          have h := closure_mono hK hxK
          rw [closure_union] at h
          exact h.resolve_right h0
        have himage : Subtype.val '' {y : {y : α | IsUnit y} | y.val ∈ K} =
            (K : Set α) \ {0} := by
          ext y
          constructor
          · rintro ⟨z, hz, rfl⟩
            exact ⟨hz, z.property.ne_zero⟩
          · intro hy
            exact ⟨⟨y, isUnit_iff_ne_zero.mpr hy.2⟩, hy.1, rfl⟩
        have hsub : (⟨x, hx⟩ : {y : α | IsUnit y}) ∈
            closure {y : {y : α | IsUnit y} | y.val ∈ K} := by
          rw [closure_subtype, himage]
          exact hnonzero
        have hi := map_mem_closure ContinuousInv₀.continuous_inv hsub (t := (K : Set α))
          fun y hy ↦ K.inv_mem (hx := y.property) hy
        exact hi }

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
    refine ⟨?_, ?_⟩
    · rw [Topology.IsEmbedding.subtypeVal.continuous_iff]
      exact continuous_subtype_val
    rw [Topology.IsEmbedding.subtypeVal.continuous_iff]
    exact ContinuousInv₀.continuous_inv.comp
      (continuous_subtype_val.subtype_mk fun x : { r : R // 0 < r } ↦ x.2.ne'.isUnit)

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
  invFun y := (y - b) / a
  left_inv x := by
    simp only [add_sub_cancel_right]
    exact mul_div_cancel_left₀ x
  right_inv y := by simp [mul_div_cancel₀]
  continuous_toFun := (continuous_const.mul continuous_id).add continuous_const
  continuous_invFun := by
    simp only [div_eq_mul_inv₀]
    fun_prop

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

/-- If `f` has a local minimum at `a` and is positive near `a`, then `z ↦ (f z)⁻¹` has a local
maximum at `a`. The inverse is taken on its domain, the subspace where `f z` is invertible. -/
theorem IsLocalMin.inv {f : α → β} {a : α} (h1 : IsLocalMin f a)
    (h2 : ∀ᶠ z in 𝓝 a, 0 < f z) :
    IsLocalMax (fun z : {z : α | IsUnit (f z)} ↦ Checked.inv (f z) z.property)
      ⟨a, h2.self_of_nhds.ne'.isUnit⟩ := by
  have hval := continuous_subtype_val.tendsto
    (⟨a, h2.self_of_nhds.ne'.isUnit⟩ : {z : α | IsUnit (f z)})
  filter_upwards [hval.eventually h1, hval.eventually h2] with z h3 h4
  exact (inv_le_inv₀ h4 h2.self_of_nhds).mpr h3

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
  -- The quotient `f / g` exists on `S`, so the argument takes place in the subspace `S`.
  have : PreconnectedSpace S := isPreconnected_iff_preconnectedSpace.mp hS
  have hgu (x : S) : IsUnit (g x) := (hg_ne x.property).isUnit
  have hfc : Continuous (fun x : S ↦ f x) := continuousOn_iff_continuous_domRestrict.mp hf
  have hgc : Continuous (fun x : S ↦ g x) := continuousOn_iff_continuous_domRestrict.mp hg
  have hquot : Continuous (fun x : S ↦ Checked.div (f x) (g x) (hgu x)) := hfc.div₀ hgc
  have hsquare : EqOn ((fun x : S ↦ Checked.div (f x) (g x) (hgu x)) ^ 2) 1 univ := by
    intro x _
    have hx : f x ^ 2 = g x ^ 2 := hsq x.property
    simp only [Pi.pow_apply, Pi.one_apply]
    rw [div_pow₀, hx, div_self]
  rcases isPreconnected_univ.eq_one_or_eq_neg_one_of_sq_eq hquot.continuousOn hsquare with h | h
  · exact Or.inl fun x hx ↦ div_eq_one_iff_eq.mp (h (mem_univ (⟨x, hx⟩ : S)))
  · refine Or.inr fun x hx ↦ ?_
    have hx' := div_eq_iff.mp (h (mem_univ (⟨x, hx⟩ : S)))
    simpa only [Pi.neg_apply, Pi.one_apply, neg_one_mul] using hx'

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
