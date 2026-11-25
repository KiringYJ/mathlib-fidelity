/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module

public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Algebra.Group.Units.Defs

/-!
# Units of multiplicatively written additive monoids
-/

public section

@[simp]
theorem Multiplicative.isUnit_iff {A : Type*} [AddMonoid A] {x : Multiplicative A} :
    IsUnit x ↔ IsAddUnit x.toAdd :=
  isUnit_iff_exists.trans (isAddUnit_iff_exists (x := x.toAdd)).symm
