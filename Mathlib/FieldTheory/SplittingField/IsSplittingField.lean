/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
public import Mathlib.RingTheory.Adjoin.Field

/-!
# Splitting fields

This file introduces the notion of a splitting field of a polynomial and provides an embedding from
a splitting field to any field that splits the polynomial. A polynomial `f : K[X]` splits
over a field extension `L` of `K` if it is zero or all of its irreducible factors over `L` have
degree `1`. A field extension of `K` of a polynomial `f : K[X]` is called a splitting field
if it is the smallest field extension of `K` such that `f` splits.

## Main definitions

* `Polynomial.IsSplittingField`: A predicate on a field to be a splitting field of a polynomial
  `f`.

## Main statements

* `Polynomial.IsSplittingField.lift`: An embedding of a splitting field of the polynomial `f` into
  another field such that `f` splits.

-/

@[expose] public section

noncomputable section

universe u v w

variable {F : Type u} (K : Type v) (L : Type w)

namespace Polynomial

variable [Field K] [Field L] [Field F] [Algebra K L]

/-- Typeclass characterising splitting fields: `f` splits in `L`, and `L` is the smallest field
extension of `K` over which `f` splits. For `f ≠ 0`, this means that `L` is generated over `K` by
the roots of `f` in `L`. The zero polynomial already splits over `K`, so for `f = 0` it means that
`L` is `K`. -/
@[stacks 09HV "Predicate version"]
class IsSplittingField (f : K[X]) : Prop where
  splits' : Splits (f.map (algebraMap K L))
  adjoin_rootSet' (hf : f ≠ 0) : Algebra.adjoin K (f.rootSet L : Set L) = ⊤
  top_eq_bot_of_eq_zero' (hf : f = 0) : (⊤ : Subalgebra K L) = ⊥

namespace IsSplittingField

variable {K}

theorem splits (f : K[X]) [IsSplittingField K L f] : Splits (f.map (algebraMap K L)) :=
  splits'

theorem adjoin_rootSet (f : K[X]) [IsSplittingField K L f] (hf : f ≠ 0) :
    Algebra.adjoin K (f.rootSet L : Set L) = ⊤ :=
  adjoin_rootSet' hf

theorem top_eq_bot_of_eq_zero (f : K[X]) [IsSplittingField K L f] (hf : f = 0) :
    (⊤ : Subalgebra K L) = ⊥ :=
  top_eq_bot_of_eq_zero' hf

section ScalarTower

variable [Algebra F K] [Algebra F L] [IsScalarTower F K L]

instance map (f : F[X]) [IsSplittingField F L f] :
    IsSplittingField K L (f.map <| algebraMap F K) where
  splits' := by rw [map_map, ← IsScalarTower.algebraMap_eq]; exact splits L f
  adjoin_rootSet' hf := by
    have hf' : f ≠ 0 := ne_zero_of_map_ne_zero hf
    have key : (f.map (algebraMap F K)).rootSet L = f.rootSet L := by
      ext x
      simp only [mem_rootSet, aeval_map_algebraMap]
    apply Subalgebra.restrictScalars_injective F
    rw [key, Subalgebra.restrictScalars_top, eq_top_iff, ← adjoin_rootSet L f hf',
      Algebra.adjoin_le_iff]
    exact fun x hx => @Algebra.subset_adjoin K _ _ _ _ _ _ hx
  top_eq_bot_of_eq_zero' hf := by
    have h : (⊤ : Subalgebra F L) = ⊥ :=
      top_eq_bot_of_eq_zero' ((Polynomial.map_eq_zero_iff (algebraMap F K).injective).mp hf)
    refine eq_bot_iff.mpr fun x _ ↦ ?_
    obtain ⟨y, rfl⟩ := Algebra.mem_bot.mp (h ▸ Algebra.mem_top : x ∈ (⊥ : Subalgebra F L))
    rw [IsScalarTower.algebraMap_apply F K L]
    exact Subalgebra.algebraMap_mem _ _

theorem splits_iff (f : K[X]) [IsSplittingField K L f] :
    Splits f ↔ (⊤ : Subalgebra K L) = ⊥ where
  mp h := by
    rcases eq_or_ne f 0 with hf0 | hf0
    · exact top_eq_bot_of_eq_zero L f hf0
    rw [eq_bot_iff, ← adjoin_rootSet L f hf0, Algebra.adjoin_le_iff]
    intro y hy
    rw [mem_rootSet, aeval_def, eval₂_eq_eval_map] at hy
    obtain ⟨x, rfl⟩ := h.mem_range_of_isRoot hf0 hy
    exact SetLike.mem_coe.2 <| Subalgebra.algebraMap_mem _ _
  mpr h := by
    rw [← Polynomial.map_id (p := f), ← RingEquiv.toRingHom_refl, ← RingEquiv.self_trans_symm
      (RingEquiv.ofBijective _ <| Algebra.bijective_algebraMap_iff.2 h),
      RingEquiv.toRingHom_trans, ← map_map]
    apply (splits L f).map

theorem IsScalarTower.splits (f : F[X]) [IsSplittingField K L (mapAlg F K f)] :
    Splits (mapAlg F L f) := by
  rw [mapAlg_comp K L f, mapAlg_eq_map]
  apply IsSplittingField.splits

theorem mul (f g : F[X]) (hf : f ≠ 0) (hg : g ≠ 0) [IsSplittingField F K f]
    [IsSplittingField K L (g.map <| algebraMap F K)] : IsSplittingField F L (f * g) where
  splits' := by
    rw [Polynomial.map_mul, IsScalarTower.algebraMap_eq F K L, ← map_map, ← map_map]
    exact Splits.mul ((splits K f).map _) (splits L (g.map (algebraMap F K)))
  adjoin_rootSet' _ := by
    have h1 : (f * g).rootSet L = f.rootSet L ∪ (g.map (algebraMap F K)).rootSet L := by
      ext x
      simp only [mem_rootSet, Set.mem_union, map_mul, mul_eq_zero, aeval_map_algebraMap]
    have h2 : f.rootSet L = algebraMap K L '' f.rootSet K := by
      rw [← (splits K f).image_rootSet (map_ne_zero hf) (IsScalarTower.toAlgHom F K L)]
      rfl
    rw [h1, h2, Algebra.adjoin_union_eq_adjoin_adjoin, Algebra.adjoin_algebraMap,
      adjoin_rootSet K f hf, Algebra.map_top, IsScalarTower.adjoin_range_toAlgHom,
      adjoin_rootSet L _ (map_ne_zero hg), Subalgebra.restrictScalars_top]
  top_eq_bot_of_eq_zero' h := absurd h (mul_ne_zero hf hg)

end ScalarTower

open scoped Classical in
/-- Splitting field of `f` embeds into any field that splits `f`. -/
def lift [Algebra K F] (f : K[X]) [IsSplittingField K L f]
    (hf : Splits (f.map (algebraMap K F))) : L →ₐ[K] F :=
  if hf0 : f = 0 then
    (Algebra.ofId K F).comp <|
      (Algebra.botEquiv K L : (⊥ : Subalgebra K L) →ₐ[K] K).comp <| by
        rw [← (splits_iff L f).1 (show f.Splits by simp [hf0])]
        exact Algebra.toTop
  else AlgHom.comp (by
    rw [← adjoin_rootSet L f hf0]
    exact Classical.choice (lift_of_splits _ fun y hy =>
      have : aeval y f = 0 := (eval₂_eq_eval_map _).trans <|
        (mem_roots <| map_ne_zero hf0).1 (Multiset.mem_toFinset.mp hy)
    ⟨IsAlgebraic.isIntegral ⟨f, hf0, this⟩, hf.of_dvd (map_ne_zero hf0)
      ((map_dvd_map' _).mpr (minpoly.dvd K y this))⟩)) Algebra.toTop

theorem finiteDimensional (f : K[X]) [IsSplittingField K L f] : FiniteDimensional K L := by
  classical
  rcases eq_or_ne f 0 with hf | hf
  · refine ⟨?_⟩
    rw [← Algebra.top_toSubmodule, top_eq_bot_of_eq_zero L f hf, Algebra.toSubmodule_bot,
      Submodule.one_eq_span]
    exact Submodule.fg_span_singleton 1
  exact ⟨@Algebra.top_toSubmodule K L _ _ _ ▸
    adjoin_rootSet L f hf ▸ fg_adjoin_of_finite (Finset.finite_toSet _) fun y hy ↦
      IsAlgebraic.isIntegral ⟨f, hf, mem_rootSet.mp hy⟩⟩

theorem IsScalarTower.isAlgebraic [Algebra F K] [Algebra F L] [Algebra.IsAlgebraic F K]
    [IsScalarTower F K L] (f : K[X]) [IsSplittingField K L f] :
    Algebra.IsAlgebraic F L := by
  have : FiniteDimensional K L := IsSplittingField.finiteDimensional L f
  exact Algebra.IsAlgebraic.trans F K L

theorem of_algEquiv [Algebra K F] (p : K[X]) (f : F ≃ₐ[K] L) [IsSplittingField K F p] :
    IsSplittingField K L p where
  splits' := by
    rw [← f.toAlgHom.comp_algebraMap, ← map_map]
    exact (splits F p).map _
  adjoin_rootSet' hp := by
    rw [← (AlgHom.range_eq_top f.toAlgHom).mpr f.surjective,
      (splits F p).adjoin_rootSet_eq_range (map_ne_zero hp), adjoin_rootSet F p hp]
  top_eq_bot_of_eq_zero' hp := by
    rw [← (AlgHom.range_eq_top f.toAlgHom).mpr f.surjective, ← Algebra.map_top,
      top_eq_bot_of_eq_zero F p hp, Algebra.map_bot]

theorem adjoin_rootSet_eq_range [Algebra K F] (f : K[X]) [IsSplittingField K L f] (hf : f ≠ 0)
    (i : L →ₐ[K] F) : Algebra.adjoin K (rootSet f F) = i.range :=
  ((splits L f).adjoin_rootSet_eq_range (map_ne_zero hf) i).mpr (adjoin_rootSet L f hf)

end IsSplittingField

end Polynomial

open Polynomial

variable {K L} [Field K] [Field L] [Algebra K L] {p : K[X]} {F : IntermediateField K L}

theorem IntermediateField.splits_of_splits (h : (p.map (algebraMap K L)).Splits) (hp : p ≠ 0)
    (hF : ∀ x ∈ p.rootSet L, x ∈ F) : (p.map (algebraMap K F)).Splits := by
  classical
  have := Splits.of_splits_map (f := p.map (algebraMap K F)) (algebraMap F L)
  rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq] at this
  refine this h fun _ a ha ↦ ?_
  exact ⟨⟨a, hF a (by rwa [rootSet_def, Finset.mem_coe, Multiset.mem_toFinset])⟩, rfl⟩

theorem IntermediateField.splits_iff_mem (h : (p.map (algebraMap K L)).Splits) (hp : p ≠ 0) :
    (p.map (algebraMap K F)).Splits ↔ ∀ x ∈ p.rootSet L, x ∈ F := by
  refine ⟨?_, IntermediateField.splits_of_splits h hp⟩
  intro hF
  rw [← hF.image_rootSet_of_map_ne_zero F.val (map_ne_zero hp), Set.forall_mem_image]
  exact fun x _ ↦ x.2

theorem IsIntegral.mem_intermediateField_of_minpoly_splits {x : L} (int : IsIntegral K x)
    {F : IntermediateField K L} (h : Splits ((minpoly K x).map (algebraMap K F))) : x ∈ F := by
  rw [← F.fieldRange_val]; exact int.mem_range_algebraMap_of_minpoly_splits h

/-- Characterize `IsSplittingField` with `IntermediateField.adjoin` instead of `Algebra.adjoin`. -/
theorem isSplittingField_iff_intermediateField (hp : p ≠ 0) : p.IsSplittingField K L ↔
    (p.map (algebraMap K L)).Splits ∧ IntermediateField.adjoin K (p.rootSet L) = ⊤ := by
  rw [← IntermediateField.toSubalgebra_injective.eq_iff,
      IntermediateField.adjoin_toSubalgebra_of_isAlgebraic fun _ ↦ isAlgebraic_of_mem_rootSet]
  exact ⟨fun h ↦ ⟨h.1, h.2 hp⟩, fun ⟨spl, adj⟩ ↦ ⟨spl, fun _ ↦ adj, fun h ↦ absurd h hp⟩⟩

-- Note: p.Splits (algebraMap F E) also works
theorem IntermediateField.isSplittingField_iff (hp : p ≠ 0) :
    p.IsSplittingField K F ↔ (p.map (algebraMap K F)).Splits ∧ F = adjoin K (p.rootSet L) := by
  suffices _ → (Algebra.adjoin K (p.rootSet F) = ⊤ ↔ F = adjoin K (p.rootSet L)) by
    exact ⟨fun h ↦ ⟨h.1, (this h.1).mp (h.2 hp)⟩,
      fun h ↦ ⟨h.1, fun _ ↦ (this h.1).mpr h.2, fun h' ↦ absurd h' hp⟩⟩
  rw [← toSubalgebra_injective.eq_iff,
      adjoin_toSubalgebra_of_isAlgebraic fun x ↦ isAlgebraic_of_mem_rootSet]
  refine fun hsp ↦ (hsp.adjoin_rootSet_eq_range (map_ne_zero hp) F.val).symm.trans ?_
  rw [← F.range_val, eq_comm]

theorem IntermediateField.adjoin_rootSet_isSplittingField (hp : (p.map (algebraMap K L)).Splits)
    (hp0 : p ≠ 0) : p.IsSplittingField K (adjoin K (p.rootSet L)) :=
  (isSplittingField_iff hp0).mpr
    ⟨splits_of_splits hp hp0 fun _ hx ↦ subset_adjoin K (p.rootSet L) hx, rfl⟩

theorem Polynomial.isSplittingField_C (a : K) : Polynomial.IsSplittingField K K (C a) where
  splits' := by simp
  adjoin_rootSet' _ := by simp
  top_eq_bot_of_eq_zero' _ := (by simp : (⊥ : Subalgebra K K) = ⊤).symm
