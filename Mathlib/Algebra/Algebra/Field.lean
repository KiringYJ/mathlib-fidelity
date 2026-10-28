/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Data.Rat.Cast.CharZero

/-!
# Facts about `algebraMap` when the coefficient ring is a field.

The algebra map commutes with inversion of an invertible element, division by an invertible
element and integer powers (of an invertible element when the exponent is negative); the
invertibility evidence on the image is the image of the original evidence. Rational casts exist
in characteristic zero, where the algebra map commutes with them.
-/

public section

namespace algebraMap

universe u v w u₁ v₁

section SemifieldSemidivisionRing

variable {R : Type*} (A : Type*) [Semifield R] [DivisionSemiring A] [Algebra R A]

@[norm_cast]
theorem coe_inv (r : R) {hr : IsUnit r} :
    ↑r⁻¹ = (Checked.inv (↑r) (hr.map (algebraMap R A)) : A) :=
  map_inv₀ (algebraMap R A) r

@[norm_cast]
theorem coe_div (r s : R) {hs : IsUnit s} :
    ↑(r / s) = (Checked.div (↑r) (↑s) (hs.map (algebraMap R A)) : A) :=
  map_div₀ (algebraMap R A) r s

@[norm_cast]
theorem coe_zpow (r : R) (z : ℤ) {h : z < 0 → IsUnit r} :
    ↑(r ^ z) = Checked.zpow (r : A) z fun hz => (h hz).map (algebraMap R A) :=
  map_zpow₀ (algebraMap R A) r z

end SemifieldSemidivisionRing

section FieldDivisionRing

variable (R A : Type*) [Field R] [CharZero R] [DivisionRing A] [CharZero A] [Algebra R A]

@[norm_cast]
theorem coe_ratCast (q : ℚ) : ↑(q : R) = (q : A) := map_ratCast (algebraMap R A) q

end FieldDivisionRing

end algebraMap
