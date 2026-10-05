/-
Copyright (c) 2025 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Euler characteristic of homological complexes

The Euler characteristic is defined using the `ComplexShape.EulerCharSigns` typeclass,
which provides the alternating signs for each index. This allows the definition to work
uniformly for chain complexes, cochain complexes, and complexes with other index types.

The definitions work on graded objects, with the homological complex versions
defined as abbreviations that apply the graded object versions to `C.X` and `C.homology`.

## Domain

The Euler characteristic is the alternating sum of the ranks of the objects. It is defined for
graded modules of finite rank (`GradedObject.HasFiniteRank`): every object has finite rank and only
finitely many have nonzero rank. The ring is required to satisfy `HasRankNullity`, so that rank is
additive on short exact sequences, as it is over division rings and commutative domains. Over a
division ring a graded module has finite rank exactly when it has finite total dimension
(`GradedObject.hasFiniteRank_iff_finiteDimensional`), and the Euler characteristic is the
alternating sum of the dimensions. Over `ℤ` it is the alternating sum of the ranks of abelian
groups used for the Euler characteristic of a space.

## Main definitions

* `ComplexShape.EulerCharSigns`: Typeclass providing alternating signs for Euler characteristic
* `GradedObject.finrankSupport`: Indices where the rank is finite and nonzero
* `GradedObject.HasFiniteRank`: Every object has finite rank and only finitely many have
  nonzero rank
* `GradedObject.eulerChar`: The Euler characteristic of a graded module of finite rank
* `HomologicalComplex.eulerChar`: The Euler characteristic of a complex of finite rank
* `HomologicalComplex.homologyEulerChar`: The Euler characteristic of the homology

## Main results

* `GradedObject.eulerChar_eq_sum_finSet_of_finrankSupport_subset`: The Euler characteristic is the
  finite sum over any finite set containing the support
* `GradedObject.hasFiniteRank_iff_finiteDimensional`: Over a division ring, finite rank is finite
  total dimension

-/

@[expose] public section

namespace ComplexShape

variable {ι : Type*} (c : ComplexShape ι)

/-- Signs for terms of Euler characteristic on complexes. -/
class EulerCharSigns where
  /-- The sign for each index -/
  χ : ι → ℤˣ
  /-- Signs alternate along relations in the complex shape -/
  χ_next {i j : ι} (h : c.Rel i j) : χ j = - χ i

variable [c.EulerCharSigns]

/-- The sign at index `i` for Euler characteristic computations. -/
abbrev χ : ι → ℤˣ := EulerCharSigns.χ c

/-- Signs alternate in the forward direction of the complex shape. -/
lemma χ_next {i j : ι} (h : c.Rel i j) : c.χ j = - c.χ i := EulerCharSigns.χ_next h

/-- Signs alternate in the backward direction of the complex shape. -/
lemma χ_prev {i j : ι} (h : c.Rel i j) : c.χ i = - c.χ j := by simp [c.χ_next h]

@[simps]
instance eulerCharSignsUpInt : (up ℤ).EulerCharSigns where
  χ := Int.negOnePow
  χ_next := by rintro _ _ rfl; rw [Int.negOnePow_succ]

@[simps]
instance eulerCharSignsDownInt : (down ℤ).EulerCharSigns where
  χ := Int.negOnePow
  χ_next := by rintro _ _ rfl; simp [Int.negOnePow_succ]

@[simps]
instance eulerCharSignsUpNat : (up ℕ).EulerCharSigns where
  χ n := (-1) ^ n
  χ_next := by rintro _ _ rfl; simp [pow_add]

@[simps]
instance eulerCharSignsDownNat : (down ℕ).EulerCharSigns where
  χ n := (-1) ^ n
  χ_next := by rintro _ _ rfl; simp [pow_add]

end ComplexShape

open ComplexShape CategoryTheory

universe v

variable {R : Type*} [Ring R] {ι : Type*}

namespace GradedObject

/-- The support of a graded object with respect to finite rank: the set of indices where
`Module.finrank` is nonzero, that is, where the rank is finite and nonzero. -/
-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
noncomputable def finrankSupport (X : CategoryTheory.GradedObject ι (ModuleCat.{v} R)) : Set ι :=
  Function.support (fun i => Module.finrank R (X i))

/-- The finite rank support is contained in a set if and only if
the rank vanishes outside that set. -/
lemma finrankSupport_subset_iff (X : CategoryTheory.GradedObject ι (ModuleCat.{v} R)) (s : Set ι) :
    finrankSupport X ⊆ s ↔ ∀ i ∉ s, Module.finrank R (X i) = 0 :=
  Function.support_subset_iff'

/-- A graded module has finite rank if every object has finite rank and only finitely many objects
have nonzero rank. This is the domain of the Euler characteristic `GradedObject.eulerChar`. -/
structure HasFiniteRank (X : CategoryTheory.GradedObject ι (ModuleCat.{v} R)) : Prop where
  /-- Every object has finite rank. -/
  rank_lt_aleph0 (i : ι) : Module.rank R (X i) < Cardinal.aleph0
  /-- Only finitely many objects have nonzero rank. -/
  finite_finrankSupport : (finrankSupport X).Finite

variable (c : ComplexShape ι) [c.EulerCharSigns]

/-- The Euler characteristic of a graded module of finite rank: the alternating sum of the ranks of
its objects, with the signs of the `ComplexShape.EulerCharSigns` instance. It is defined over rings
on which rank is additive (`HasRankNullity`). -/
@[nolint unusedArguments]
noncomputable def eulerChar [HasRankNullity.{v} R]
    (X : CategoryTheory.GradedObject ι (ModuleCat.{v} R)) (hX : HasFiniteRank X) : ℤ :=
  ∑ i ∈ hX.finite_finrankSupport.toFinset, (c.χ i : ℤ) * Module.finrank R (X i)

/-- The Euler characteristic equals the finite sum over any finite set containing the
finite rank support. -/
theorem eulerChar_eq_sum_finSet_of_finrankSupport_subset [HasRankNullity.{v} R]
    (X : CategoryTheory.GradedObject ι (ModuleCat.{v} R)) (hX : HasFiniteRank X)
    (indices : Finset ι) (h_support : finrankSupport X ⊆ indices) :
    eulerChar c X hX = ∑ i ∈ indices, (c.χ i : ℤ) * Module.finrank R (X i) := by
  refine Finset.sum_subset (by simpa using h_support) fun i _ hi ↦ ?_
  rw [Set.Finite.mem_toFinset, finrankSupport, Function.mem_support, not_not] at hi
  simp [hi]

end GradedObject

namespace GradedObject

variable {k : Type*} [DivisionRing k]

/-- Over a division ring, a graded vector space has finite rank exactly when it has finite total
dimension: every object is finite-dimensional and only finitely many are nontrivial. -/
theorem hasFiniteRank_iff_finiteDimensional (X : CategoryTheory.GradedObject ι (ModuleCat.{v} k)) :
    HasFiniteRank X ↔ (∀ i, Module.Finite k (X i)) ∧ {i | Nontrivial (X i)}.Finite := by
  have h (i : ι) (hi : Module.Finite k (X i)) :
      Module.finrank k (X i) ≠ 0 ↔ Nontrivial (X i) := by
    rw [Ne, Module.finrank_eq_zero_iff_of_free, not_subsingleton_iff_nontrivial]
  refine ⟨fun hX ↦ ⟨fun i ↦ Module.rank_lt_aleph0_iff.1 (hX.rank_lt_aleph0 i), ?_⟩,
    fun ⟨hfin, hsupp⟩ ↦ ⟨fun i ↦ Module.rank_lt_aleph0_iff.2 (hfin i), ?_⟩⟩
  · convert hX.finite_finrankSupport using 1
    ext i
    have := Module.rank_lt_aleph0_iff.1 (hX.rank_lt_aleph0 i)
    simp [finrankSupport, h i this]
  · convert hsupp using 1
    ext i
    simp [finrankSupport, h i (hfin i)]

end GradedObject

namespace HomologicalComplex

variable [HasRankNullity.{v} R] {c : ComplexShape ι} [c.EulerCharSigns]

/-- The Euler characteristic of a homological complex of finite rank: the alternating sum of the
ranks of its terms, with the signs of the `ComplexShape.EulerCharSigns` instance. -/
noncomputable abbrev eulerChar (C : HomologicalComplex (ModuleCat.{v} R) c)
    (hC : GradedObject.HasFiniteRank C.X) : ℤ :=
  GradedObject.eulerChar c C.X hC

/-- The homological Euler characteristic: the Euler characteristic of the homology, defined when
the homology has finite rank. -/
noncomputable abbrev homologyEulerChar (C : HomologicalComplex (ModuleCat.{v} R) c)
    [∀ i : ι, C.HasHomology i] (hC : GradedObject.HasFiniteRank (fun i => C.homology i)) : ℤ :=
  GradedObject.eulerChar c (fun i => C.homology i) hC

/-- The Euler characteristic of a complex equals the finite sum over any finite set containing the
finite rank support. -/
theorem eulerChar_eq_sum_finSet_of_finrankSupport_subset
    (C : HomologicalComplex (ModuleCat.{v} R) c) (hC : GradedObject.HasFiniteRank C.X)
    (indices : Finset ι)
    (h_support : GradedObject.finrankSupport C.X ⊆ indices) :
    eulerChar C hC = ∑ i ∈ indices, (c.χ i : ℤ) * Module.finrank R (C.X i) :=
  GradedObject.eulerChar_eq_sum_finSet_of_finrankSupport_subset c C.X hC indices h_support

/-- The homological Euler characteristic equals the finite sum over any finite set containing
the finite rank support of the homology. -/
theorem homologyEulerChar_eq_sum_finSet_of_finrankSupport_subset
    (C : HomologicalComplex (ModuleCat.{v} R) c) [∀ i : ι, C.HasHomology i]
    (hC : GradedObject.HasFiniteRank (fun i => C.homology i)) (indices : Finset ι)
    (h_support : GradedObject.finrankSupport (fun i => C.homology i) ⊆ indices) :
    homologyEulerChar C hC = ∑ i ∈ indices, (c.χ i : ℤ) * Module.finrank R (C.homology i) :=
  GradedObject.eulerChar_eq_sum_finSet_of_finrankSupport_subset c
    (fun i => C.homology i) hC indices h_support

end HomologicalComplex
