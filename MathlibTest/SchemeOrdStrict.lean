import Mathlib.AlgebraicGeometry.OrderOfVanishing

/-!
# Strict order of vanishing on schemes

These tests ensure that the order of vanishing of a rational function on a scheme is defined only at
points of codimension one, and that the zero function has order `⊤`, as for a discrete valuation,
instead of the former value `0`.
-/

open AlgebraicGeometry Order

universe u

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- info: Unknown constant `AlgebraicGeometry.Scheme.ord_eq_zero_of_coheight_neq_one` -/
#guard_msgs in
#check_failure AlgebraicGeometry.Scheme.ord_eq_zero_of_coheight_neq_one

/-- info: Unknown constant `AlgebraicGeometry.Scheme.ord_eq_ordHom_of_coheight_eq_one` -/
#guard_msgs in
#check_failure AlgebraicGeometry.Scheme.ord_eq_ordHom_of_coheight_eq_one

/-! The order needs the codimension condition. -/

/--
error: Type mismatch
  Scheme.ord f z
has type
  coheight z = 1 → WithTop ℤ
but is expected to have type
  WithTop ℤ
-/
#guard_msgs in
noncomputable example (f : X.functionField) (z : X) : WithTop ℤ := Scheme.ord f z

/-! The zero function has order `⊤`, and every other function has an integer order. -/

example (z : X) (hz : coheight z = 1) : Scheme.ord 0 z hz = ⊤ := by simp

example (z : X) (hz : coheight z = 1) (f : X.functionField) (hf : f ≠ 0) :
    Scheme.ord f z hz ≠ ⊤ :=
  (Scheme.ord_eq_top_iff hz).not.2 hf

/-! Multiplicativity holds without nonvanishing hypotheses. -/

example (z : X) (hz : coheight z = 1) (f g : X.functionField) :
    Scheme.ord (f * g) z hz = Scheme.ord f z hz + Scheme.ord g z hz :=
  Scheme.ord_mul hz f g
