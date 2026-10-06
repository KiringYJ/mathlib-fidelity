import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.RingTheory.IsAdjoinRoot
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

/-!
# Division by a monic polynomial takes the monicity of the divisor

`p /ₘ q` and `p %ₘ q` take a proof that `q` is monic, which `monic_tac` finds by default. They have
no value at a divisor that is not monic.
-/

open Polynomial

/-! The lemmas that stated values at a divisor that is not monic are removed. -/

/-- info: Unknown identifier `divByMonic_eq_of_not_monic` -/
#guard_msgs in
#check_failure divByMonic_eq_of_not_monic

/-- info: Unknown identifier `modByMonic_eq_of_not_monic` -/
#guard_msgs in
#check_failure modByMonic_eq_of_not_monic

/-- info: Unknown identifier `modByMonic_zero` -/
#guard_msgs in
#check_failure modByMonic_zero

/-- info: Unknown identifier `divByMonic_zero` -/
#guard_msgs in
#check_failure divByMonic_zero

/-! The notation omits the proof that the divisor is monic. -/

/-- info: fun p q hq => p /ₘ q + p %ₘ q : ℤ[X] → (q : ℤ[X]) → q.Monic → ℤ[X] -/
#guard_msgs in
#check fun (p q : ℤ[X]) (hq : q.Monic) => p /ₘ q + p %ₘ q

/-! The default discharger handles hypotheses, `X`, `1`, `X ± C a`, products, powers, images,
finite products, and the extensions for minimal polynomials, characteristic polynomials,
cyclotomic polynomials, presentations by a root of a monic polynomial, and normalization over a
field. -/

example (p : ℤ[X]) (a : ℤ) : p %ₘ (X - C a) = C (p.eval a) :=
  modByMonic_X_sub_C_eq_C_eval p a

noncomputable example (p : ℤ[X]) (a : ℤ) : ℤ[X] := p /ₘ X + p /ₘ 1 + p /ₘ (X + C a)

noncomputable example (p q r : ℤ[X]) (hq : q.Monic) (hr : r.Monic) : ℤ[X] := p /ₘ (q * r)

noncomputable example (p q : ℤ[X]) (hq : q.Monic) (n : ℕ) : ℤ[X] := p /ₘ q ^ n

noncomputable example (p : ℤ[X]) (a : ℤ) (n : ℕ) : ℤ[X] := p %ₘ (X - C a) ^ n

noncomputable example (p q : ℤ[X]) (hq : q.Monic) : ℚ[X] :=
  p.map (Int.castRingHom ℚ) /ₘ q.map (Int.castRingHom ℚ)

noncomputable example (p : ℤ[X]) (s : Finset ℤ) : ℤ[X] := p /ₘ ∏ a ∈ s, (X - C a)

example (p q : ℤ[X]) (hq : q.Monic) : p %ₘ q + q * (p /ₘ q) = p :=
  modByMonic_add_div p hq

example {A B : Type*} [CommRing A] [Ring B] [Algebra A B] (x : B) (hx : IsIntegral A x)
    (p : A[X]) : (p %ₘ minpoly A x).aeval x = p.aeval x := by
  simp

noncomputable example (p : ℤ[X]) (M : Matrix (Fin 2) (Fin 2) ℤ) : ℤ[X] := p %ₘ M.charpoly

noncomputable example (p : ℤ[X]) (n : ℕ) : ℤ[X] := p /ₘ cyclotomic n ℤ

noncomputable example {S : Type*} [CommRing S] [Algebra ℤ S] (f : ℤ[X])
    (h : IsAdjoinRootMonic S f) (p : ℤ[X]) : ℤ[X] :=
  p %ₘ f

noncomputable example (p q : ℚ[X]) (hq : q ≠ 0) : ℚ[X] := p /ₘ (q * C (leadingCoeff q)⁻¹)

/-! Division and remainder over a field keep the values that `EuclideanDomain` requires at `0`,
and unfold to division by a monic polynomial only for a nonzero divisor. -/

example (p : ℚ[X]) : p / 0 = 0 := EuclideanDomain.div_zero p

example (p : ℚ[X]) : p % 0 = p := EuclideanDomain.mod_zero p

example (p q : ℚ[X]) (hq : q ≠ 0) :
    p / q = C (leadingCoeff q)⁻¹ * (p /ₘ (q * C (leadingCoeff q)⁻¹)) :=
  div_def hq

/-! Without a proof that the divisor is monic, there is no quotient. -/

/--
error: could not synthesize default value for parameter 'hq' using tactics
---
error: the divisor must be monic
p q : ℤ[X]
⊢ q.Monic
-/
#guard_msgs in
noncomputable example (p q : ℤ[X]) : ℤ[X] := p /ₘ q

/--
error: could not synthesize default value for parameter 'hq' using tactics
---
error: the divisor must be monic
p : ℤ[X]
⊢ (2 * X).Monic
-/
#guard_msgs in
noncomputable example (p : ℤ[X]) : ℤ[X] := p %ₘ (2 * X)

/-! The rules only unify at reducible and instance transparency, so that a hypothesis about another
concrete polynomial is rejected without unfolding powers. -/

/--
error: could not synthesize default value for parameter 'hq' using tactics
---
error: the divisor must be monic
h : (X ^ 1000 + 1).Monic
p : ℤ[X]
⊢ (X ^ 1001 + 1).Monic
-/
#guard_msgs in
noncomputable example (h : (X ^ 1000 + 1 : ℤ[X]).Monic) (p : ℤ[X]) : ℤ[X] :=
  p /ₘ (X ^ 1001 + 1)

/-! The discharger never chooses an undetermined divisor. -/

/--
error: could not synthesize default value for parameter 'hq' using tactics
---
error: the divisor is not determined; pass its monicity explicitly
-/
#guard_msgs in
example (p : ℤ[X]) : p /ₘ _ = p /ₘ X := rfl
