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

@[simp] lemma divp_mk0 (a : G₀) (hb : b ≠ 0) : a /ₚ Units.mk0 b hb = Checked.div a b hb.isUnit :=
  congrArg (a /ₚ ·) (Units.ext rfl)

end GroupWithZero

/-! ### Integer powers

A negative power requires an invertible base; nonnegative powers are the natural powers of the
monoid. In particular `(0 : M₀) ^ n` is defined exactly for `0 ≤ n` in a nontrivial monoid with
zero, and `0 ^ 0 = 1` is the empty product. -/

section MonoidWithZero
variable {n : ℤ}

lemma zero_zpow (n : ℤ) (hn : n ≠ 0) {h : n < 0 → IsUnit (0 : M₀)} : (0 : M₀) ^ n = 0 := by
  cases n with
  | ofNat k => exact zero_pow (by rintro rfl; exact hn rfl)
  | negSucc k =>
    exact eq_of_zero_eq_one (isUnit_zero_iff.1 (h (Int.negSucc_lt_zero k))) _ _

lemma zero_zpow_eq (n : ℤ) {h : n < 0 → IsUnit (0 : M₀)} :
    (0 : M₀) ^ n = if n = 0 then 1 else 0 := by
  split_ifs with hn
  · subst hn; exact zpow_zero₀ 0
  · exact zero_zpow n hn

lemma zero_zpow_eq_one₀ [Nontrivial M₀] {h : n < 0 → IsUnit (0 : M₀)} :
    (0 : M₀) ^ n = 1 ↔ n = 0 := by
  rw [zero_zpow_eq, one_ne_zero.ite_eq_left_iff]

end MonoidWithZero

section GroupWithZero
variable [GroupWithZero G₀] {a b : G₀} {m n : ℕ}

lemma zpow_ne_zero (n : ℤ) (h : a ≠ 0) : a ^ n ≠ 0 := by
  rw [(GroupWithZero.isUnit_of_ne_zero h).zpow_eq_val_unit_zpow]
  exact Units.ne_zero _

lemma eq_zero_of_zpow_eq_zero {n : ℤ} {h : n < 0 → IsUnit a} : a ^ n = 0 → a = 0 :=
  not_imp_not.1 (zpow_ne_zero n)

lemma zpow_eq_zero_iff {n : ℤ} (hn : n ≠ 0) {h : n < 0 → IsUnit a} : a ^ n = 0 ↔ a = 0 where
  mp := eq_zero_of_zpow_eq_zero
  mpr ha := by
    subst ha
    exact zero_zpow n hn

lemma zpow_ne_zero_iff {n : ℤ} (hn : n ≠ 0) {h : n < 0 → IsUnit a} : a ^ n ≠ 0 ↔ a ≠ 0 :=
  (zpow_eq_zero_iff hn).not

lemma zpow_add₀ (ha : a ≠ 0) (m n : ℤ) : a ^ (m + n) = a ^ m * a ^ n := by
  have hu := GroupWithZero.isUnit_of_ne_zero ha
  rw [hu.zpow_eq_val_unit_zpow (m + n), hu.zpow_eq_val_unit_zpow m, hu.zpow_eq_val_unit_zpow n,
    zpow_add, Units.val_mul]

/-- Integer powers add whenever all three powers are defined: either the base is invertible or
all exponents are nonnegative. -/
lemma zpow_add' {a : G₀} {m n : ℤ} {h₁ : m + n < 0 → IsUnit a} {h₂ : m < 0 → IsUnit a}
    {h₃ : n < 0 → IsUnit a} : a ^ (m + n) = a ^ m * a ^ n := by
  by_cases ha : a = 0
  · subst ha
    obtain ⟨m, rfl⟩ : ∃ k : ℕ, (k : ℤ) = m :=
      ⟨m.toNat, Int.toNat_of_nonneg (Int.not_lt.1 fun hm => not_isUnit_zero (h₂ hm))⟩
    obtain ⟨n, rfl⟩ : ∃ k : ℕ, (k : ℤ) = n :=
      ⟨n.toNat, Int.toNat_of_nonneg (Int.not_lt.1 fun hn => not_isUnit_zero (h₃ hn))⟩
    simp only [← Int.natCast_add, zpow_natCast₀, pow_add]
  · exact zpow_add₀ ha m n

lemma zpow_add_one₀ (ha : a ≠ 0) (n : ℤ) : a ^ (n + 1) = a ^ n * a := by
  rw [zpow_add₀ ha, zpow_one₀]

lemma zpow_one_add₀ (ha : a ≠ 0) (n : ℤ) : a ^ (1 + n) = a * a ^ n := by
  rw [zpow_add₀ ha, zpow_one₀]

lemma zpow_neg₀ (ha : a ≠ 0) (n : ℤ) : a ^ (-n) = (a ^ n)⁻¹ := by
  have hu := GroupWithZero.isUnit_of_ne_zero ha
  rw [hu.zpow_eq_val_unit_zpow (-n), zpow_neg, inv_eq_val_inv_of_eq_val₀ (hu.unit ^ n)
    (hu.zpow_eq_val_unit_zpow n)]

lemma zpow_sub_one₀ (ha : a ≠ 0) (n : ℤ) : a ^ (n - 1) = a ^ n * a⁻¹ := by
  simp only [Int.sub_eq_add_neg, zpow_add₀ ha, zpow_neg₀ ha, zpow_one₀]

lemma zpow_sub₀ (ha : a ≠ 0) (m n : ℤ) : a ^ (m - n) = Checked.div (a ^ m) (a ^ n) := by
  simp only [Int.sub_eq_add_neg, zpow_add₀ ha, zpow_neg₀ ha, div_eq_mul_inv₀]

lemma zpow_natCast_sub_natCast₀ (ha : a ≠ 0) (m n : ℕ) :
    a ^ (m - n : ℤ) = Checked.div (a ^ m) (a ^ n) := by
  simp only [zpow_sub₀ ha, zpow_natCast₀]

lemma zpow_natCast_sub_one₀ (ha : a ≠ 0) (n : ℕ) : a ^ (n - 1 : ℤ) = Checked.div (a ^ n) a := by
  simp only [zpow_sub₀ ha, zpow_natCast₀, zpow_one₀]

lemma zpow_one_sub_natCast₀ (ha : a ≠ 0) (n : ℕ) : a ^ (1 - n : ℤ) = Checked.div a (a ^ n) := by
  simp only [zpow_sub₀ ha, zpow_natCast₀, zpow_one₀]

lemma zpow_neg_mul_zpow_self (n : ℤ) (ha : a ≠ 0) : a ^ (-n) * a ^ n = 1 := by
  simp only [← zpow_add₀ ha, Int.add_left_neg, zpow_zero₀]

lemma zpow_mul₀ (ha : a ≠ 0) (m n : ℤ) : a ^ (m * n) = (a ^ m) ^ n := by
  have hu := GroupWithZero.isUnit_of_ne_zero ha
  have hm : IsUnit (a ^ m) := hu.zpow₀ m
  rw [hu.zpow_eq_val_unit_zpow (m * n), hm.zpow_eq_val_unit_zpow n, zpow_mul]
  congr 2
  ext
  exact (hu.zpow_eq_val_unit_zpow m).symm

lemma zpow_mul₀' (ha : a ≠ 0) (m n : ℤ) : a ^ (m * n) = (a ^ n) ^ m := by
  rw [← zpow_mul₀ ha n m]
  simp only [Int.mul_comm]

lemma pow_sub₀ (a : G₀) (ha : a ≠ 0) (h : n ≤ m) : a ^ (m - n) = a ^ m * (a ^ n)⁻¹ := by
  have hn : IsUnit (a ^ n) := (GroupWithZero.isUnit_of_ne_zero ha).pow n
  rw [eq_mul_inv_iff_mul_eq₀, ← pow_add, Nat.sub_add_cancel h]

lemma inv_pow_sub₀ (ha : a ≠ 0) (h : n ≤ m) : a⁻¹ ^ (m - n) = (a ^ m)⁻¹ * a ^ n := by
  have hu := GroupWithZero.isUnit_of_ne_zero ha
  rw [pow_sub₀ a⁻¹ inv_ne_zero h]
  simp only [inv_pow₀, inv_inv₀]

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
