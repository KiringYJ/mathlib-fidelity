/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
module

public import Mathlib.Algebra.Category.Grp.Basic

/-!
# Equivalence between `Group` and `AddGroup`

This file contains two equivalences:
* `groupAddGroupEquivalence` : the equivalence between `GrpCat` and `AddGrpCat` by sending
  `X : GrpCat` to `Additive X` and `Y : AddGrpCat` to `Multiplicative Y`.
* `commGroupAddCommGroupEquivalence` : the equivalence between `CommGrpCat` and `AddCommGrpCat`
  by sending `X : CommGrpCat` to `Additive X` and `Y : AddCommGrpCat` to `Multiplicative Y`.
-/

@[expose] public section


open CategoryTheory

namespace GrpCat

/-- The functor `GrpCat ⥤ AddGrpCat` by sending `X ↦ Additive X` and `f ↦ f`.
-/
@[simps]
def toAddGrp : GrpCat ⥤ AddGrpCat where
  obj X := ↧(Additive X)
  map {_} {_} f := AddGrpCat.ofHom f.hom.toAdditive

end GrpCat

namespace CommGrpCat

/-- The functor `CommGrpCat ⥤ AddCommGrpCat` by sending `X ↦ Additive X` and `f ↦ f`.
-/
@[simps]
def toAddCommGrp : CommGrpCat ⥤ AddCommGrpCat where
  obj X := ↧(Additive X)
  map {_} {_} f := AddCommGrpCat.ofHom f.hom.toAdditive

end CommGrpCat

namespace AddGrpCat

/-- The functor `AddGrpCat ⥤ GrpCat` by sending `X ↦ Multiplicative X` and `f ↦ f`.
-/
@[simps]
def toGrp : AddGrpCat ⥤ GrpCat where
  obj X := ↧(Multiplicative X)
  map {_} {_} f := GrpCat.ofHom f.hom.toMultiplicative

end AddGrpCat

namespace AddCommGrpCat

/-- The functor `AddCommGrpCat ⥤ CommGrpCat` by sending `X ↦ Multiplicative X` and `f ↦ f`.
-/
@[simps]
def toCommGrp : AddCommGrpCat ⥤ CommGrpCat where
  obj X := ↧(Multiplicative X)
  map {_} {_} f := CommGrpCat.ofHom f.hom.toMultiplicative

end AddCommGrpCat

/-- The equivalence of categories between `GrpCat` and `AddGrpCat`
-/
@[simps]
def groupAddGroupEquivalence : GrpCat ≌ AddGrpCat where
  functor := GrpCat.toAddGrp
  inverse := AddGrpCat.toGrp
  unitIso := NatIso.ofComponents (fun X => MulEquiv.toGrpIso {
    toEquiv := Equiv.refl (X : Type _)
    map_mul' := fun _ _ => rfl }) (by
    intro X Y f
    ext x
    rfl)
  counitIso := NatIso.ofComponents (fun X => AddEquiv.toAddGrpIso {
    toEquiv := Equiv.refl (X : Type _)
    map_add' := fun _ _ => rfl }) (by
    intro X Y f
    ext x
    rfl)
  functor_unitIso_comp X := by
    ext x
    rfl

/-- The equivalence of categories between `CommGrpCat` and `AddCommGrpCat`.
-/
@[simps]
def commGroupAddCommGroupEquivalence : CommGrpCat ≌ AddCommGrpCat where
  functor := CommGrpCat.toAddCommGrp
  inverse := AddCommGrpCat.toCommGrp
  unitIso := NatIso.ofComponents (fun X => MulEquiv.toCommGrpIso {
    toEquiv := Equiv.refl (X : Type _)
    map_mul' := fun _ _ => rfl }) (by
    intro X Y f
    ext x
    rfl)
  counitIso := NatIso.ofComponents (fun X => AddEquiv.toAddCommGrpIso {
    toEquiv := Equiv.refl (X : Type _)
    map_add' := fun _ _ => rfl }) (by
    intro X Y f
    ext x
    rfl)
  functor_unitIso_comp X := by
    ext x
    rfl
