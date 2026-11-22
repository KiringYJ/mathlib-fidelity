module

import Mathlib.Algebra.Field.Subfield.Defs
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.GroupWithZero.Units.Lemmas

/-! Regression tests for the checked subfield API: membership of inverses, quotients and integer
powers, coercions out of a subfield, and construction of a subfield from an inversion-closed
subring. -/

section

variable {K : Type*} [DivisionRing K]

-- membership with implicit evidence unified from the goal
example (s : Subfield K) {x : K} (hx : x ∈ s) (h : x ≠ 0) : x⁻¹ ∈ s := s.inv_mem hx
example (s : Subfield K) {x y : K} (hx : x ∈ s) (hy : y ∈ s) (h : y ≠ 0) : x / y ∈ s :=
  s.div_mem hx hy
example (s : Subfield K) {x : K} (hx : x ∈ s) (n : ℤ) (h : x ≠ 0) : x ^ n ∈ s := s.zpow_mem hx n
example (s : Subfield K) {x : K} (hx : x ∈ s) (n : ℕ) : x ^ (n : ℤ) ∈ s := s.zpow_mem hx n

-- the `SetLike` automation uses the same lemmas
example (s : Subfield K) {x y : K} (hx : x ∈ s) (hy : y ∈ s) (h : y ≠ 0) : x / y ∈ s := by aesop
example (s : Subfield K) {x : K} (hx : x ∈ s) (h : x ≠ 0) : x⁻¹ ∈ s := by aesop

-- coercions: the ambient evidence is derived from the subfield evidence
example (s : Subfield K) (x : s) (hx : x ≠ 0) : ((x⁻¹ : s) : K) = (x : K)⁻¹ := by simp
example (s : Subfield K) (x y : s) (hy : y ≠ 0) : ((x / y : s) : K) = (x : K) / (y : K) := by
  simp
example (s : Subfield K) (x y : s) (hy : IsUnit y) : (x : K) / (y : K) = ((x / y : s) : K) := by
  norm_cast
example (s : Subfield K) (x : s) (h : x ≠ 0) : x * x⁻¹ = 1 := mul_inv_cancel₀

-- a subring closed under inversion of its nonzero elements is a subfield
example (s : Subring K) (h : ∀ {x : K} {hx : IsUnit x}, x ∈ s → x⁻¹ ∈ s) : Subfield K :=
  s.toSubfield h

example (f : K →+* K) (s : Subfield K) : Subfield K :=
  { s.toSubring.comap f with
    inv_mem' := fun {x} {_} h => show f x⁻¹ ∈ s by rw [map_inv₀ f]; exact s.inv_mem h }

end

section

variable {F : Type*} [Field F]

example (s : Subfield F) (x y : s) (hy : y ≠ 0) : ((x / y : s) : F) = (x : F) / (y : F) := by
  simp
example (s : Subfield F) (x : s) (h : x ≠ 0) : ((x * x⁻¹ : s) : F) = 1 := by simp

end
