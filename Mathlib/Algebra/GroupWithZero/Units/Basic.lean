/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Group.Units.Basic
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Data.Nat.Basic  -- shake: keep (non-recorded `nontrivial` dependency?)
public import Mathlib.Lean.Meta.CongrTheorems
public import Mathlib.Tactic.Contrapose
public import Mathlib.Tactic.Spread
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.Nontriviality

/-!
# Lemmas about units in a `MonoidWithZero` or a `GroupWithZero`.

Inversion takes place in the group of units; mixed division uses `divp` with a unit denominator.
-/

@[expose] public section

assert_not_exists DenselyOrdered Equiv Subtype.restrict Multiplicative Ring

variable {α M₀ G₀ : Type*}
variable [MonoidWithZero M₀]

namespace Units

/-- An element of the unit group of a nonzero monoid with zero represented as an element
of the monoid is nonzero. -/
@[simp]
theorem ne_zero [Nontrivial M₀] (u : M₀ˣ) : (u : M₀) ≠ 0 :=
  left_ne_zero_of_mul_eq_one u.mul_inv

-- We can't use `mul_eq_zero` + `Units.ne_zero` in the next two lemmas because we don't assume
-- `Nontrivial M₀`.
@[simp]
theorem mul_left_eq_zero (u : M₀ˣ) {a : M₀} : a * u = 0 ↔ a = 0 :=
  ⟨fun h => by simpa using mul_eq_zero_of_left h ↑u⁻¹, fun h => mul_eq_zero_of_left h u⟩

@[simp]
theorem mul_right_eq_zero (u : M₀ˣ) {a : M₀} : ↑u * a = 0 ↔ a = 0 :=
  ⟨fun h => by simpa using mul_eq_zero_of_right (↑u⁻¹) h, mul_eq_zero_of_right (u : M₀)⟩

end Units

namespace IsUnit

theorem ne_zero [Nontrivial M₀] {a : M₀} (ha : IsUnit a) : a ≠ 0 :=
  let ⟨u, hu⟩ := ha
  hu ▸ u.ne_zero

theorem mul_right_eq_zero {a b : M₀} (ha : IsUnit a) : a * b = 0 ↔ b = 0 :=
  let ⟨u, hu⟩ := ha
  hu ▸ u.mul_right_eq_zero

theorem mul_left_eq_zero {a b : M₀} (hb : IsUnit b) : a * b = 0 ↔ a = 0 :=
  let ⟨u, hu⟩ := hb
  hu ▸ u.mul_left_eq_zero

end IsUnit

@[simp]
theorem isUnit_zero_iff : IsUnit (0 : M₀) ↔ (0 : M₀) = 1 :=
  ⟨fun ⟨⟨_, a, (a0 : 0 * a = 1), _⟩, rfl⟩ => by rwa [zero_mul] at a0, fun h =>
    @isUnit_of_subsingleton _ _ (subsingleton_of_zero_eq_one h) 0⟩

theorem not_isUnit_zero [Nontrivial M₀] : ¬IsUnit (0 : M₀) :=
  mt isUnit_zero_iff.1 zero_ne_one

namespace Units

variable [GroupWithZero G₀]

@[simp]
theorem mk0_one (h := one_ne_zero) : mk0 (1 : G₀) h = 1 := by
  ext
  rfl

@[simp]
theorem mk0_val (u : G₀ˣ) (h : (u : G₀) ≠ 0) : mk0 (u : G₀) h = u :=
  Units.ext rfl

@[simp]
theorem mk0_inj {a b : G₀} (ha : a ≠ 0) (hb : b ≠ 0) : Units.mk0 a ha = Units.mk0 b hb ↔ a = b :=
  ⟨fun h => by injection h, fun h => Units.ext h⟩

/-- In a group with zero, an existential over a unit can be rewritten in terms of `Units.mk0`. -/
theorem exists0 {p : G₀ˣ → Prop} : (∃ g : G₀ˣ, p g) ↔ ∃ (g : G₀) (hg : g ≠ 0), p (Units.mk0 g hg) :=
  ⟨fun ⟨g, pg⟩ => ⟨g, g.ne_zero, (g.mk0_val g.ne_zero).symm ▸ pg⟩,
  fun ⟨g, hg, pg⟩ => ⟨Units.mk0 g hg, pg⟩⟩

/-- An alternative version of `Units.exists0`. This one is useful if Lean cannot
figure out `p` when using `Units.exists0` from right to left. -/
theorem exists0' {p : ∀ g : G₀, g ≠ 0 → Prop} :
    (∃ (g : G₀) (hg : g ≠ 0), p g hg) ↔ ∃ g : G₀ˣ, p g g.ne_zero :=
  Iff.trans (by simp_rw [val_mk0]) exists0.symm

@[simp]
theorem exists_iff_ne_zero {p : G₀ → Prop} : (∃ u : G₀ˣ, p u) ↔ ∃ x ≠ 0, p x := by
  simp [exists0]

theorem _root_.GroupWithZero.eq_zero_or_unit (a : G₀) : a = 0 ∨ ∃ u : G₀ˣ, a = u := by
  simpa using em _

end Units

section GroupWithZero
variable [GroupWithZero G₀] {a b c : G₀} {m n : ℕ}

theorem IsUnit.mk0 (x : G₀) (hx : x ≠ 0) : IsUnit x :=
  (Units.mk0 x hx).isUnit

@[simp]
theorem isUnit_iff_ne_zero : IsUnit a ↔ a ≠ 0 :=
  (Units.exists_iff_ne_zero (p := (· = a))).trans (by simp)

protected alias ⟨_, Ne.isUnit⟩ := isUnit_iff_ne_zero

@[simp]
theorem Units.mk0_mul (x y : G₀) (hxy) :
    Units.mk0 (x * y) hxy =
      Units.mk0 x (mul_ne_zero_iff.mp hxy).1 * Units.mk0 y (mul_ne_zero_iff.mp hxy).2 := by
  ext; rfl

end GroupWithZero

section MonoidWithZero

variable {a : M₀} (u : M₀ˣ)

@[simp] theorem divp_eq_zero_iff : a /ₚ u = 0 ↔ a = 0 := by
  exact u⁻¹.mul_left_eq_zero

theorem divp_ne_zero_iff : a /ₚ u ≠ 0 ↔ a ≠ 0 := (divp_eq_zero_iff u).not

@[simp] theorem zero_divp : (0 : M₀) /ₚ u = 0 := zero_mul _

end MonoidWithZero

section GroupWithZero

variable [GroupWithZero G₀] {m n : ℕ}

/-- Subtract natural exponents by dividing by a unit power. -/
lemma pow_sub_divp (a : G₀) (ha : a ≠ 0) (h : n ≤ m) :
    a ^ (m - n) = a ^ m /ₚ (Units.mk0 a ha) ^ n := by
  apply eq_divp_iff_mul_eq.mpr
  change a ^ (m - n) * a ^ n = a ^ m
  rw [← pow_add, Nat.sub_add_cancel h]

end GroupWithZero

section Constructors

variable {M : Type*} [Nontrivial M]

/-- Construct a group with zero from the property that every element is a unit or zero. -/
@[instance_reducible]
def groupWithZeroOfIsUnitOrEqZero [hM : MonoidWithZero M]
    (h : ∀ a : M, IsUnit a ∨ a = 0) : GroupWithZero M :=
  { hM with isUnit_of_ne_zero := fun {a} ha => (h a).resolve_right ha }

/-- Construct a commutative group with zero from the unit-or-zero property. -/
@[instance_reducible]
def commGroupWithZeroOfIsUnitOrEqZero [hM : CommMonoidWithZero M]
    (h : ∀ a : M, IsUnit a ∨ a = 0) : CommGroupWithZero M :=
  { groupWithZeroOfIsUnitOrEqZero h, hM with }

end Constructors
