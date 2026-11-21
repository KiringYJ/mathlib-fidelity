/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Chris Hughes
-/
module

public import Mathlib.Algebra.GCDMonoid.Basic
public import Mathlib.Algebra.EuclideanDomain.Basic
public import Mathlib.RingTheory.Ideal.Basic
public import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Lemmas about Euclidean domains

Various about Euclidean domains are proved; all of them seem to be true
more generally for principal ideal domains, so these lemmas should
probably be reproved in more generality and this file perhaps removed?

## Tags

euclidean domain
-/

@[expose] public section


section

open EuclideanDomain Set Ideal

section GCDMonoid

open EuclideanDomain (quotient)

variable {R : Type*} [EuclideanDomain R] [GCDMonoid R] {p q : R}

theorem left_div_gcd_ne_zero {p q : R} (hp : p ≠ 0) :
    quotient p (GCDMonoid.gcd p q) (gcd_ne_zero_of_left hp) ≠ 0 := by
  have h := EuclideanDomain.mul_div_cancel' (gcd_ne_zero_of_left hp) (GCDMonoid.gcd_dvd_left p q)
  exact right_ne_zero_of_mul (h.symm ▸ hp)

theorem right_div_gcd_ne_zero {p q : R} (hq : q ≠ 0) :
    quotient q (GCDMonoid.gcd p q) (gcd_ne_zero_of_right hq) ≠ 0 := by
  have h := EuclideanDomain.mul_div_cancel' (gcd_ne_zero_of_right hq) (GCDMonoid.gcd_dvd_right p q)
  exact right_ne_zero_of_mul (h.symm ▸ hq)

/-- Dividing two elements by their nonzero gcd gives coprime quotients. -/
theorem isCoprime_div_gcd_div_gcd_of_gcd_ne_zero (hpq : GCDMonoid.gcd p q ≠ 0) :
    IsCoprime (quotient p (GCDMonoid.gcd p q) hpq) (quotient q (GCDMonoid.gcd p q) hpq) :=
  (gcd_isUnit_iff _ _).1 <|
    isUnit_gcd_of_eq_mul_gcd
        (EuclideanDomain.mul_div_cancel' hpq <| gcd_dvd_left _ _).symm
        (EuclideanDomain.mul_div_cancel' hpq <| gcd_dvd_right _ _).symm <| hpq

theorem isCoprime_div_gcd_div_gcd (hq : q ≠ 0) :
    IsCoprime (quotient p (GCDMonoid.gcd p q) (gcd_ne_zero_of_right hq))
      (quotient q (GCDMonoid.gcd p q) (gcd_ne_zero_of_right hq)) :=
  isCoprime_div_gcd_div_gcd_of_gcd_ne_zero (gcd_ne_zero_of_right hq)

end GCDMonoid

namespace EuclideanDomain

/-- Create a `GCDMonoid` whose `GCDMonoid.gcd` matches `EuclideanDomain.gcd`. -/
@[instance_reducible]
def gcdMonoid (R) [EuclideanDomain R] [DecidableEq R] : GCDMonoid R where
  gcd := gcd
  lcm := lcm
  gcd_dvd_left := gcd_dvd_left
  gcd_dvd_right := gcd_dvd_right
  dvd_gcd := dvd_gcd
  gcd_mul_lcm a b := by rw [EuclideanDomain.gcd_mul_lcm]; rfl
  lcm_zero_left := lcm_zero_left
  lcm_zero_right := lcm_zero_right

variable {α : Type*} [EuclideanDomain α]

theorem span_gcd [DecidableEq α] (x y : α) :
    span ({gcd x y} : Set α) = span ({x, y} : Set α) :=
  letI := EuclideanDomain.gcdMonoid α
  _root_.span_gcd x y

theorem gcd_isUnit_iff [DecidableEq α] {x y : α} : IsUnit (gcd x y) ↔ IsCoprime x y :=
  letI := EuclideanDomain.gcdMonoid α
  _root_.gcd_isUnit_iff x y

-- this should be proved for UFDs surely?
theorem isCoprime_of_dvd {x y : α} (nonzero : ¬(x = 0 ∧ y = 0))
    (H : ∀ z ∈ nonunits α, z ≠ 0 → z ∣ x → ¬z ∣ y) : IsCoprime x y :=
  letI := Classical.decEq α
  letI := EuclideanDomain.gcdMonoid α
  _root_.isCoprime_of_dvd x y nonzero H

-- this should be proved for UFDs surely?
theorem dvd_or_coprime (x y : α) (h : Irreducible x) :
    x ∣ y ∨ IsCoprime x y :=
  letI := Classical.decEq α
  letI := EuclideanDomain.gcdMonoid α
  _root_.dvd_or_isCoprime x y h

end EuclideanDomain

end
