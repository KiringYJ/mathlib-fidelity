/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Topology.OneSidedInverse
public import Mathlib.Analysis.Analytic.Inverse

/-!
# The category of formal multilinear series

The composition of formal multilinear series reads the outer series as an expansion at the constant
coefficient of the inner one (see `Mathlib/Analysis/Analytic/Composition.lean`). This file records
that convention as a category: the objects are normed spaces with a chosen point, and a morphism
`X ⟶ Y` is a formal multilinear series from `X` to `Y` whose constant coefficient is the point of
`Y`. Composition is `FormalMultilinearSeries.comp`, the identity of `X` is
`FormalMultilinearSeries.id 𝕜 X X.point`, and the category laws are
`FormalMultilinearSeries.comp_id`, `FormalMultilinearSeries.id_comp` and
`FormalMultilinearSeries.comp_assoc`. The matching of basepoints that composition presupposes is
part of the type of morphisms. Morphisms constrain only the point of their target, so the chosen
point is not an isomorphism invariant: the identity series expanded at `0` is an isomorphism from
a space with any point to the same space with the origin, whose inverse is the identity series
expanded at the original point.

Taking the linear term is a functor `FormalMultilinearSeriesCat.linearTerm` to `TopModuleCat 𝕜`.
It reflects split monomorphisms, split epimorphisms and isomorphisms: a formal multilinear series
has a formal left, right or two-sided inverse exactly when its linear term has a continuous linear
one. This is the formal analogue of the fact that a jet is invertible exactly when its underlying
1-jet is ([kolar_michor_slovak1993], §12.3). The formal one-sided inverses
`FormalMultilinearSeries.leftInv` and `FormalMultilinearSeries.rightInv` provide the splittings,
and the inverse of an isomorphism is both of them.

For real finite-dimensional spaces, restricted to the diagonal and truncated at each finite order,
a morphism determines an infinite jet in the sense of [kolar_michor_slovak1993], §12.18, and
composition becomes the composition of jets of §12.3. The coefficients of a formal multilinear
series need not be symmetric, so different morphisms can determine the same jet.

The objects of this category lie in a single universe. The unbundled statements about formal
multilinear series remain the main interface; the results here are their categorical form.

## Main definitions and results

* `FormalMultilinearSeriesCat 𝕜`: normed spaces over `𝕜` with a chosen point.
* `FormalMultilinearSeriesCat.Hom X Y`: formal multilinear series with constant coefficient the
  point of `Y`, the morphisms of the category.
* `FormalMultilinearSeriesCat.linearTerm`: the linear term, as a functor to `TopModuleCat 𝕜`.
* `FormalMultilinearSeriesCat.isSplitMono_iff_hasLeftInverse`,
  `FormalMultilinearSeriesCat.isSplitEpi_iff_hasRightInverse`,
  `FormalMultilinearSeriesCat.isIso_iff_isInvertible`: a morphism splits, or is an isomorphism,
  exactly when its linear term does.
* `FormalMultilinearSeriesCat.linearTerm` reflects isomorphisms.
* `FormalMultilinearSeriesCat.series_inv_eq_leftInv`,
  `FormalMultilinearSeriesCat.series_inv_eq_rightInv`: the inverse of an isomorphism is its
  formal left and right inverse.

## References

* [Kolář, Michor, Slovák, *Natural operations in differential geometry*][kolar_michor_slovak1993]
-/

@[expose] public section

open CategoryTheory

universe v u

/-- Normed spaces over `𝕜` with a chosen point. They are the objects of the category whose
morphisms are formal multilinear series with constant coefficient the point of the target. -/
structure FormalMultilinearSeriesCat (𝕜 : Type u) [NontriviallyNormedField 𝕜] where
  /-- The underlying type. -/
  carrier : Type v
  /-- The normed group structure of the underlying type. -/
  [normedAddCommGroup : NormedAddCommGroup carrier]
  /-- The normed space structure of the underlying type. -/
  [normedSpace : NormedSpace 𝕜 carrier]
  /-- The chosen point, at which the series leaving this object are expanded. -/
  point : carrier

namespace FormalMultilinearSeriesCat

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]

attribute [instance] normedAddCommGroup normedSpace

instance : CoeSort (FormalMultilinearSeriesCat.{v} 𝕜) (Type v) :=
  ⟨carrier⟩

attribute [coe] carrier

variable (𝕜) in
/-- The normed space `E` with the point `x`. -/
abbrev of (E : Type v) [NormedAddCommGroup E] [NormedSpace 𝕜 E] (x : E) :
    FormalMultilinearSeriesCat.{v} 𝕜 :=
  ⟨E, x⟩

/-- A morphism `X ⟶ Y`: a formal multilinear series from `X` to `Y` whose constant coefficient is
the point of `Y`. -/
@[ext]
structure Hom (X Y : FormalMultilinearSeriesCat.{v} 𝕜) where
  /-- The underlying formal multilinear series. -/
  series : FormalMultilinearSeries 𝕜 X Y
  series_coeff_zero : series 0 0 = Y.point

noncomputable instance : Category (FormalMultilinearSeriesCat.{v} 𝕜) where
  Hom := Hom
  id X := ⟨FormalMultilinearSeries.id 𝕜 X X.point, rfl⟩
  comp f g := ⟨g.series.comp f.series, by
    rw [FormalMultilinearSeries.comp_coeff_zero g.series f.series 0 0, g.series_coeff_zero]⟩
  id_comp f := Hom.ext (f.series.comp_id _)
  comp_id f := Hom.ext (FormalMultilinearSeries.id_comp' f.series _ 0 f.series_coeff_zero.symm)
  assoc f g h := Hom.ext (FormalMultilinearSeries.comp_assoc h.series g.series f.series).symm

variable {X Y Z : FormalMultilinearSeriesCat.{v} 𝕜}

@[ext]
theorem hom_ext {f g : X ⟶ Y} (h : f.series = g.series) : f = g :=
  Hom.ext h

@[simp]
theorem series_id (X : FormalMultilinearSeriesCat.{v} 𝕜) :
    (𝟙 X : X ⟶ X).series = FormalMultilinearSeries.id 𝕜 X X.point :=
  rfl

@[simp]
theorem series_comp (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).series = g.series.comp f.series :=
  rfl

/-- The constant coefficient of a morphism is the point of its target. -/
@[simp]
theorem series_apply_zero (f : X ⟶ Y) (v : Fin 0 → X) : f.series 0 v = Y.point := by
  rw [Subsingleton.elim v 0]
  exact f.series_coeff_zero

/-- A formal multilinear series, as a morphism from its source space with any point to its target
space with its constant coefficient as point. -/
abbrev ofSeries {E F : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] (p : FormalMultilinearSeries 𝕜 E F) (x : E) : of 𝕜 E x ⟶ of 𝕜 F (p 0 0) :=
  ⟨p, rfl⟩

@[simp]
theorem series_ofSeries {E F : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] (p : FormalMultilinearSeries 𝕜 E F) (x : E) :
    (ofSeries p x).series = p :=
  rfl

/-- The linear term of a formal multilinear series, as a functor to topological modules. -/
noncomputable def linearTerm : FormalMultilinearSeriesCat.{v} 𝕜 ⥤ TopModuleCat.{v} 𝕜 where
  obj X := TopModuleCat.of 𝕜 X
  map {X Y} f := TopModuleCat.ofHom (continuousMultilinearCurryFin1 𝕜 X Y (f.series 1))
  map_id X := by
    ext v
    simp
  map_comp {X Y Z} f g := by
    ext v
    simp [FormalMultilinearSeries.comp_coeff_one, Matrix.vec_single_eq_const]

@[simp]
theorem linearTerm_obj (X : FormalMultilinearSeriesCat.{v} 𝕜) :
    linearTerm.obj X = TopModuleCat.of 𝕜 X :=
  rfl

@[simp]
theorem linearTerm_map_hom (f : X ⟶ Y) :
    (linearTerm.map f).hom = continuousMultilinearCurryFin1 𝕜 X Y (f.series 1) :=
  rfl

/-- The formal left inverse constructed from a continuous linear left inverse `r` of the linear
term splits a morphism. -/
noncomputable def splitMonoOfLeftInverse (f : X ⟶ Y) (r : Y →L[𝕜] X)
    (hr : Function.LeftInverse r (continuousMultilinearCurryFin1 𝕜 X Y (f.series 1))) :
    SplitMono f where
  retraction := ⟨f.series.leftInv r hr X.point, by simp⟩
  id := Hom.ext (FormalMultilinearSeries.leftInv_comp _ _ _ _)

/-- The formal right inverse constructed from a continuous linear right inverse `s` of the linear
term splits a morphism. -/
noncomputable def splitEpiOfRightInverse (f : X ⟶ Y) (s : Y →L[𝕜] X)
    (hs : Function.RightInverse s (continuousMultilinearCurryFin1 𝕜 X Y (f.series 1))) :
    SplitEpi f where
  section_ := ⟨f.series.rightInv s hs X.point, by simp⟩
  id := by
    ext1
    rw [series_comp, FormalMultilinearSeries.comp_rightInv, f.series_coeff_zero]
    rfl

/-- A morphism is a split monomorphism exactly when its linear term has a continuous linear left
inverse. -/
theorem isSplitMono_iff_hasLeftInverse (f : X ⟶ Y) :
    IsSplitMono f ↔ (continuousMultilinearCurryFin1 𝕜 X Y (f.series 1)).HasLeftInverse := by
  constructor
  · rintro ⟨⟨r, hr⟩⟩
    exact (f.series.exists_comp_eq_id_iff_hasLeftInverse X.point).1
      ⟨r.series, congr_arg Hom.series hr⟩
  · rintro ⟨r, hr⟩
    exact ⟨⟨splitMonoOfLeftInverse f r hr⟩⟩

/-- A morphism is a split epimorphism exactly when its linear term has a continuous linear right
inverse. -/
theorem isSplitEpi_iff_hasRightInverse (f : X ⟶ Y) :
    IsSplitEpi f ↔ (continuousMultilinearCurryFin1 𝕜 X Y (f.series 1)).HasRightInverse := by
  constructor
  · rintro ⟨⟨s, hs⟩⟩
    refine f.series.exists_comp_eq_id_iff_hasRightInverse.1 ⟨s.series, ?_⟩
    rw [f.series_coeff_zero]
    exact congr_arg Hom.series hs
  · rintro ⟨s, hs⟩
    exact ⟨⟨splitEpiOfRightInverse f s hs⟩⟩

/-- The linear term detects split monomorphisms. -/
theorem isSplitMono_iff_isSplitMono_linearTerm_map (f : X ⟶ Y) :
    IsSplitMono f ↔ IsSplitMono (linearTerm.map f) := by
  rw [isSplitMono_iff_hasLeftInverse, TopModuleCat.isSplitMono_iff_hasLeftInverse]
  rfl

/-- The linear term detects split epimorphisms. -/
theorem isSplitEpi_iff_isSplitEpi_linearTerm_map (f : X ⟶ Y) :
    IsSplitEpi f ↔ IsSplitEpi (linearTerm.map f) := by
  rw [isSplitEpi_iff_hasRightInverse, TopModuleCat.isSplitEpi_iff_hasRightInverse]
  rfl

/-- A formal multilinear series is invertible exactly when its linear term is. -/
instance : (linearTerm.{v} (𝕜 := 𝕜)).ReflectsIsomorphisms where
  reflects f _ := by
    have : IsSplitMono f := (isSplitMono_iff_isSplitMono_linearTerm_map f).2 inferInstance
    have : IsSplitEpi f := (isSplitEpi_iff_isSplitEpi_linearTerm_map f).2 inferInstance
    exact isIso_of_mono_of_isSplitEpi f

/-- A morphism is an isomorphism exactly when its linear term is a continuous linear
equivalence. -/
theorem isIso_iff_isInvertible (f : X ⟶ Y) :
    IsIso f ↔ (continuousMultilinearCurryFin1 𝕜 X Y (f.series 1)).IsInvertible := by
  rw [← isIso_iff_of_reflects_iso f linearTerm, TopModuleCat.isIso_iff_isInvertible]
  rfl

/-- The inverse of an isomorphism is its formal left inverse. -/
theorem series_inv_eq_leftInv (f : X ⟶ Y) [IsIso f] (r : Y →L[𝕜] X)
    (hr : Function.LeftInverse r (continuousMultilinearCurryFin1 𝕜 X Y (f.series 1))) :
    (inv f).series = f.series.leftInv r hr X.point :=
  congr_arg Hom.series (IsIso.inv_eq_of_hom_inv_id (splitMonoOfLeftInverse f r hr).id)

/-- The inverse of an isomorphism is its formal right inverse. -/
theorem series_inv_eq_rightInv (f : X ⟶ Y) [IsIso f] (s : Y →L[𝕜] X)
    (hs : Function.RightInverse s (continuousMultilinearCurryFin1 𝕜 X Y (f.series 1))) :
    (inv f).series = f.series.rightInv s hs X.point :=
  congr_arg Hom.series (IsIso.inv_eq_of_inv_hom_id (splitEpiOfRightInverse f s hs).id)

end FormalMultilinearSeriesCat
