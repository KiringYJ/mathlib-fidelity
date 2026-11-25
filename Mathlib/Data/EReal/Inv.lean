/-
Copyright (c) 2019 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Mathlib.Basic.ENNReal.Inv
public import Mathlib.Basic.Sign.Basic
public import Mathlib.Data.EReal.Operations
public import Mathlib.Data.Nat.Cast.Order.Field

/-!
# Absolute value, sign, inversion and division on extended real numbers

This file defines an absolute value and sign function on `EReal` and uses them to provide a
`CommMonoidWithZero` instance, based on the absolute value and sign characterising all `EReal`s.

The operation `a⁻¹` requires a unit of `EReal`. The units are its nonzero real elements
(`EReal.isUnit_iff`). The evidence search `checked_unit` finds the requisite evidence
from hypotheses such as `0 < b` and `b ≠ ⊤`, and for real and natural casts.

The quotient `a / b` requires `EReal.DivDomain a b`. A nonzero finite denominator permits any
numerator. An infinite denominator permits a finite numerator and gives quotient zero.

A total inverse would need a value at `0`, and any value is arbitrary: the one-sided limits of
`x⁻¹` at `0` are `⊥` and `⊤`. The reciprocals `⊥⁻¹ = ⊤⁻¹ = 0` of extended real arithmetic are
limits of `x⁻¹` rather than multiplicative inverses, since `⊤ * 0 = 0`; this extended reciprocal
on the nonzero elements is not defined here.
-/

@[expose] public section

open ENNReal Set SignType

noncomputable section

namespace EReal

/-! ### Absolute value -/

-- TODO: use `Real.nnabs` for the case `(x : ℝ)`
/-- The absolute value from `EReal` to `ℝ≥0∞`, mapping `⊥` and `⊤` to `⊤` and
a real `x` to `|x|`. -/
protected def abs : EReal → ℝ≥0∞
  | ⊥ => ⊤
  | ⊤ => ⊤
  | (x : ℝ) => ENNReal.ofReal |x|

@[simp] theorem abs_top : (⊤ : EReal).abs = ⊤ := rfl

@[simp] theorem abs_bot : (⊥ : EReal).abs = ⊤ := rfl

theorem abs_def (x : ℝ) : (x : EReal).abs = ENNReal.ofReal |x| := rfl

theorem abs_coe_lt_top (x : ℝ) : (x : EReal).abs < ⊤ :=
  ENNReal.ofReal_lt_top

@[simp]
theorem abs_eq_zero_iff {x : EReal} : x.abs = 0 ↔ x = 0 := by
  induction x
  · simp
  · simp only [abs_def, coe_eq_zero, ENNReal.ofReal_eq_zero, abs_nonpos_iff]
  · simp only [abs_top, ENNReal.top_ne_zero, top_ne_zero]

@[simp]
theorem abs_zero : (0 : EReal).abs = 0 := by rw [abs_eq_zero_iff]

@[simp]
theorem coe_abs (x : ℝ) : ((x : EReal).abs : EReal) = (|x| : ℝ) := by
  rw [abs_def, ← Real.coe_nnabs, ENNReal.ofReal_coe_nnreal]; rfl

@[simp]
protected theorem abs_neg : ∀ x : EReal, (-x).abs = x.abs
  | ⊤ => rfl
  | ⊥ => rfl
  | (x : ℝ) => by rw [abs_def, ← coe_neg, abs_def, abs_neg]

@[simp]
theorem abs_mul (x y : EReal) : (x * y).abs = x.abs * y.abs := by
  induction x, y using induction₂_symm_neg with
  | top_zero => simp only [mul_zero, abs_zero]
  | top_top => rfl
  | symm h => rwa [mul_comm, EReal.mul_comm]
  | coe_coe => simp only [← coe_mul, abs_def, _root_.abs_mul, ENNReal.ofReal_mul (abs_nonneg _)]
  | top_pos _ h =>
    rw [top_mul_coe_of_pos h, abs_top, ENNReal.top_mul]
    rw [Ne, abs_eq_zero_iff, coe_eq_zero]
    exact h.ne'
  | neg_left h => rwa [neg_mul, EReal.abs_neg, EReal.abs_neg]

/-! ### Sign -/

open SignType (sign)

theorem sign_top : sign (⊤ : EReal) = 1 := rfl

theorem sign_bot : sign (⊥ : EReal) = -1 := rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem sign_coe (x : ℝ) : sign (x : EReal) = sign x := by
  simp only [sign, OrderHom.coe_mk, EReal.coe_pos, EReal.coe_neg']

@[simp, norm_cast]
theorem coe_coe_sign (x : SignType) : ((x : ℝ) : EReal) = x := by cases x <;> rfl

@[simp] theorem sign_neg : ∀ x : EReal, sign (-x) = -sign x
  | ⊤ => rfl
  | ⊥ => rfl
  | (x : ℝ) => by rw [← coe_neg, sign_coe, sign_coe, Left.sign_neg]

@[simp]
theorem sign_mul (x y : EReal) : sign (x * y) = sign x * sign y := by
  induction x, y using induction₂_symm_neg with
  | top_zero => simp only [mul_zero, sign_zero]
  | top_top => rfl
  | symm h => rwa [mul_comm, EReal.mul_comm]
  | coe_coe => simp only [← coe_mul, sign_coe, _root_.sign_mul]
  | top_pos _ h =>
    rw [top_mul_coe_of_pos h, sign_top, one_mul, sign_pos (EReal.coe_pos.2 h)]
  | neg_left h => rw [neg_mul, sign_neg, sign_neg, h, neg_mul]

@[simp] protected theorem sign_mul_abs : ∀ x : EReal, (sign x * x.abs : EReal) = x
  | ⊥ => by simp
  | ⊤ => by simp
  | (x : ℝ) => by rw [sign_coe, coe_abs, ← coe_coe_sign, ← coe_mul, sign_mul_abs]

@[simp] protected theorem abs_mul_sign (x : EReal) : (x.abs * sign x : EReal) = x := by
  rw [EReal.mul_comm, EReal.sign_mul_abs]

theorem sign_eq_and_abs_eq_iff_eq {x y : EReal} :
    x.abs = y.abs ∧ sign x = sign y ↔ x = y := by
  constructor
  · rintro ⟨habs, hsign⟩
    rw [← x.sign_mul_abs, ← y.sign_mul_abs, habs, hsign]
  · rintro rfl
    exact ⟨rfl, rfl⟩

theorem le_iff_sign {x y : EReal} :
    x ≤ y ↔ sign x < sign y ∨
      sign x = SignType.neg ∧ sign y = SignType.neg ∧ y.abs ≤ x.abs ∨
        sign x = SignType.zero ∧ sign y = SignType.zero ∨
          sign x = SignType.pos ∧ sign y = SignType.pos ∧ x.abs ≤ y.abs := by
  constructor
  · intro h
    refine (sign.monotone h).lt_or_eq.imp_right (fun hs => ?_)
    rw [← x.sign_mul_abs, ← y.sign_mul_abs] at h
    cases hy : sign y <;> rw [hs, hy] at h ⊢
    · simp
    · left; simpa using h
    · right; right; simpa using h
  · rintro (h | h | h | h)
    · exact (sign.monotone.reflect_lt h).le
    all_goals rw [← x.sign_mul_abs, ← y.sign_mul_abs]; simp [h]

instance : CommMonoidWithZero EReal :=
  { (inferInstance : MulZeroOneClass EReal) with
    mul_assoc := fun x y z => by
      rw [← sign_eq_and_abs_eq_iff_eq]
      simp only [mul_assoc, abs_mul, sign_mul, and_self_iff]
    mul_comm := EReal.mul_comm }

instance : PosMulMono EReal := posMulMono_iff_covariant_pos.2 <| .mk <| by
  rintro ⟨x, x0⟩ a b h
  simp only [le_iff_sign, EReal.sign_mul, sign_pos x0, one_mul, EReal.abs_mul] at h ⊢
  exact h.imp_right <| Or.imp (And.imp_right <| And.imp_right (mul_le_mul_right · _)) <|
    Or.imp_right <| And.imp_right <| And.imp_right (mul_le_mul_right · _)

instance : MulPosMono EReal := posMulMono_iff_mulPosMono.1 inferInstance

instance : PosMulReflectLT EReal := PosMulMono.toPosMulReflectLT

instance : MulPosReflectLT EReal := MulPosMono.toMulPosReflectLT

lemma mul_le_mul_of_nonpos_right {a b c : EReal} (h : b ≤ a) (hc : c ≤ 0) : a * c ≤ b * c := by
  rw [mul_comm a c, mul_comm b c, ← neg_le_neg_iff, ← neg_mul c b, ← neg_mul c a]
  rw [← neg_zero, EReal.le_neg] at hc
  gcongr

@[simp, norm_cast]
theorem coe_pow (x : ℝ) (n : ℕ) : (↑(x ^ n) : EReal) = (x : EReal) ^ n :=
  map_pow (⟨⟨(↑), coe_one⟩, coe_mul⟩ : ℝ →* EReal) _ _

@[simp, norm_cast]
theorem coe_ennreal_pow (x : ℝ≥0∞) (n : ℕ) : (↑(x ^ n) : EReal) = (x : EReal) ^ n :=
  map_pow (⟨⟨(↑), coe_ennreal_one⟩, coe_ennreal_mul⟩ : ℝ≥0∞ →* EReal) _ _

lemma exists_nat_ge_mul {a : EReal} (ha : a ≠ ⊤) (n : ℕ) :
    ∃ m : ℕ, a * n ≤ m :=
  match a with
  | ⊤ => ha.irrefl.rec
  | ⊥ => ⟨0, Nat.cast_zero (R := EReal) ▸ mul_nonpos_iff.2 (.inr ⟨bot_le, n.cast_nonneg'⟩)⟩
  | (a : ℝ) => by
    obtain ⟨m, an_m⟩ := exists_nat_ge (a * n)
    use m
    rwa [← coe_coe_eq_natCast n, ← coe_coe_eq_natCast m, ← EReal.coe_mul, EReal.coe_le_coe_iff]

/-! ### Min and Max -/

lemma min_neg_neg (x y : EReal) : min (-x) (-y) = -max x y := by
  rcases le_total x y with (h | h) <;> simp_all

lemma max_neg_neg (x y : EReal) : max (-x) (-y) = -min x y := by
  rcases le_total x y with (h | h) <;> simp_all

/-! ### Units -/

/-- The units of `EReal` are its nonzero real elements: `⊥` and `⊤` have no inverse, since
`|⊥| = |⊤| = ⊤` and no product `⊤ * a` in `ℝ≥0∞` is `1`. -/
theorem isUnit_iff {x : EReal} : IsUnit x ↔ x ≠ ⊥ ∧ x ≠ ⊤ ∧ x ≠ 0 := by
  refine ⟨fun hx ↦ ?_, fun ⟨h₁, h₂, h₃⟩ ↦ ?_⟩
  · obtain ⟨y, hxy⟩ := hx.exists_right_inv
    have habs : x.abs * y.abs = 1 := by
      rw [← abs_mul, hxy, ← coe_one, abs_def, abs_one, ENNReal.ofReal_one]
    have key : ∀ z : ℝ≥0∞, ⊤ * z ≠ 1 := fun z ↦ by
      rcases eq_or_ne z 0 with rfl | hz
      · simp
      · rw [ENNReal.top_mul hz]
        exact ENNReal.top_ne_one
    refine ⟨fun h ↦ ?_, fun h ↦ ?_, hx.ne_zero⟩
    · rw [h, abs_bot] at habs
      exact key _ habs
    · rw [h, abs_top] at habs
      exact key _ habs
  · lift x to ℝ using ⟨h₂, h₁⟩
    have hx : x ≠ 0 := coe_ne_zero.1 h₃
    exact ⟨⟨x, ((x⁻¹ : ℝ) : EReal), by rw [← coe_mul, mul_inv_cancel₀, coe_one],
      by rw [← coe_mul, inv_mul_cancel₀, coe_one]⟩, rfl⟩

theorem isUnit_coe_iff {x : ℝ} : IsUnit (x : EReal) ↔ x ≠ 0 := by
  simp [isUnit_iff, coe_ne_bot, coe_ne_top]

/-! The evidence search `checked_unit` uses `EReal.isUnit_iff`: an element of `EReal` is a unit
when it is neither `⊥` nor `⊤` and is nonzero. These conditions are found from hypotheses, from
strict inequalities such as `0 < b` (so `b ≠ ⊥`) or `b < 0` (so `b ≠ ⊤`), and for real and
natural casts. -/

macro_rules | `(tactic| checked_unit) => `(tactic|
    solve
    | assumption
    | (refine EReal.isUnit_iff.mpr ⟨?_, ?_, ?_⟩
       · solve
         | assumption
         | exact EReal.coe_ne_bot _
         | exact EReal.natCast_ne_bot _
         | (apply ne_bot_of_gt; assumption)
       · solve
         | assumption
         | exact EReal.coe_ne_top _
         | exact EReal.natCast_ne_top _
         | (apply ne_top_of_lt; assumption)
       · solve
         | assumption
         | (apply EReal.coe_ne_zero.mpr; checked_nonzero)
         | checked_nonzero))

/-! ### Inverse

There is no ambient inverse on `EReal`: `a⁻¹` is the inverse of a unit, defined for the nonzero
real elements. -/

lemma coe_inv (x : ℝ) {hx : IsUnit x} : ((x⁻¹ : ℝ) : EReal) = (x : EReal)⁻¹ :=
  eq_inv_of_mul_eq_one_left₀ (by rw [← coe_mul, inv_mul_cancel₀, coe_one])

/-- The absolute value of a unit of `EReal` is a unit. -/
lemma isUnit_coe_abs {a : EReal} (ha : IsUnit a) : IsUnit (a.abs : EReal) := by
  obtain ⟨h₁, h₂, h₃⟩ := isUnit_iff.1 ha
  lift a to ℝ using ⟨h₂, h₁⟩
  rw [coe_abs, isUnit_coe_iff, abs_ne_zero]
  exact coe_ne_zero.1 h₃

/-! #### Inversion and Absolute Value -/

lemma sign_mul_inv_abs (a : EReal) {ha : IsUnit a} :
    (sign a) * Checked.inv (a.abs : EReal) (isUnit_coe_abs ha) = a⁻¹ := by
  obtain ⟨h₁, h₂, h₃⟩ := isUnit_iff.1 ha
  lift a to ℝ using ⟨h₂, h₁⟩
  have ha' : a ≠ 0 := coe_ne_zero.1 h₃
  have habs : IsUnit |a| := (abs_ne_zero.2 ha').isUnit
  simp only [coe_abs]
  rw [← coe_inv |a| (hx := habs), ← coe_inv a (hx := ha'.isUnit), sign_coe, ← coe_coe_sign,
    ← coe_mul, EReal.coe_eq_coe_iff]
  rcases ha'.lt_or_gt with a_neg | a_pos
  · simp only [_root_.sign_neg a_neg, abs_of_neg a_neg, SignType.coe_neg_one, neg_one_mul,
      inv_neg₀, neg_neg]
  · simp only [_root_.sign_pos a_pos, abs_of_pos a_pos, SignType.coe_one, one_mul]

lemma sign_mul_inv_abs' (a : EReal) {ha : IsUnit a} :
    (sign a) * ((a.abs⁻¹ : ℝ≥0∞) : EReal) = a⁻¹ := by
  obtain ⟨h₁, h₂, h₃⟩ := isUnit_iff.1 ha
  lift a to ℝ using ⟨h₂, h₁⟩
  have ha' : a ≠ 0 := coe_ne_zero.1 h₃
  have ha₀ : 0 < |a| := abs_pos.2 ha'
  rw [abs_def a, ← ofReal_inv_of_pos ha₀, coe_ennreal_ofReal, max_eq_left (inv_pos_of_pos ha₀).le,
    ← coe_inv a (hx := ha'.isUnit), sign_coe, ← coe_coe_sign, ← coe_mul]
  rcases ha'.lt_or_gt with a_neg | a_pos
  · rw [_root_.sign_neg a_neg]
    simp only [abs_of_neg a_neg, inv_neg₀ (ha := ha'.isUnit.neg), SignType.coe_neg_one, neg_one_mul,
      neg_neg]
  · rw [_root_.sign_pos a_pos]
    simp only [abs_of_pos a_pos, SignType.coe_one, one_mul]

/-! #### Inversion and Positivity -/

lemma bot_lt_inv (x : EReal) {hx : IsUnit x} : ⊥ < x⁻¹ :=
  bot_lt_iff_ne_bot.2 (isUnit_iff.1 hx.inv₀).1

lemma inv_lt_top (x : EReal) {hx : IsUnit x} : x⁻¹ < ⊤ :=
  lt_top_iff_ne_top.2 (isUnit_iff.1 hx.inv₀).2.1

lemma inv_nonpos_of_nonpos {a : EReal} {ha : IsUnit a} (h : a ≤ 0) : a⁻¹ ≤ 0 := by
  obtain ⟨h₁, h₂, h₃⟩ := isUnit_iff.1 ha
  lift a to ℝ using ⟨h₂, h₁⟩
  rw [← coe_inv a (hx := (coe_ne_zero.1 h₃).isUnit), EReal.coe_nonpos]
  exact inv_nonpos.2 (EReal.coe_nonpos.1 h)

lemma inv_pos_of_pos_ne_top {a : EReal} (h : 0 < a) (h' : a ≠ ⊤) : 0 < a⁻¹ := by
  lift a to ℝ using ⟨h', ne_bot_of_gt h⟩
  rw [EReal.coe_pos] at h
  rw [← coe_inv a (hx := h.ne'.isUnit), EReal.coe_pos]
  exact inv_pos_of_pos h

lemma inv_neg_of_neg_ne_bot {a : EReal} (h : a < 0) (h' : a ≠ ⊥) : a⁻¹ < 0 := by
  lift a to ℝ using ⟨ne_top_of_lt h, h'⟩
  rw [EReal.coe_neg'] at h
  rw [← coe_inv a (hx := h.ne.isUnit), EReal.coe_neg']
  exact inv_lt_zero.2 h

/-- Inversion is strictly antitone on the positive real elements `Ioo 0 ⊤` of `EReal`, the
positive elements where it is defined. -/
lemma inv_strictAntiOn :
    StrictAnti fun x : Ioo (0 : EReal) ⊤ ↦
      Checked.inv (x : EReal) (isUnit_iff.2 ⟨ne_bot_of_gt x.2.1, x.2.2.ne, x.2.1.ne'⟩) := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩ a_b
  change a < b at a_b
  have a_0 := ha.1
  have b_0 := hb.1
  lift a to ℝ using ⟨ha.2.ne, ne_bot_of_gt a_0⟩
  lift b to ℝ using ⟨hb.2.ne, ne_bot_of_gt b_0⟩
  rw [EReal.coe_pos] at a_0 b_0
  rw [EReal.coe_lt_coe_iff] at a_b
  dsimp only
  rw [← coe_inv a (hx := a_0.ne'.isUnit), ← coe_inv b (hx := b_0.ne'.isUnit),
    EReal.coe_lt_coe_iff]
  exact (inv_lt_inv₀ b_0 a_0).2 a_b

/-! ### Division

The domain consists of pairs with nonzero denominator and at least one finite operand.

At a zero denominator and a nonzero limiting numerator, approaching zero on opposite sides
gives quotients tending to opposite infinities. At `(0, 0)`, the real pairs `(c * t, t)` give
different limits as `c` varies and `t` tends to zero through positive values. At a pair of
infinities, let the two operands tend to their respective endpoints at a fixed ratio of
magnitudes. Different positive ratios again give distinct limits. These cases exhaust the
points where real division has no continuous extension.
-/

/-- The domain of ordinary division on the two-sided extended real line. -/
def DivDomain (a b : EReal) : Prop :=
  b ≠ 0 ∧ ((a ≠ ⊤ ∧ a ≠ ⊥) ∨ (b ≠ ⊤ ∧ b ≠ ⊥))

theorem DivDomain.of_isUnit (a : EReal) {b : EReal} (hb : IsUnit b) : DivDomain a b :=
  let ⟨hbot, htop, hzero⟩ := isUnit_iff.1 hb
  ⟨hzero, Or.inr ⟨htop, hbot⟩⟩

theorem divDomain_coe_ennreal {a b : ℝ≥0∞} :
    DivDomain (a : EReal) (b : EReal) ↔ b ≠ 0 ∧ (a ≠ ⊤ ∨ b ≠ ⊤) := by
  simp [DivDomain]

/-- Discharge the domain of signed extended-real division. -/
syntax (name := solveERealDivDomain) "ereal_div_domain" : tactic

set_option linter.style.setOption false in
-- Limit the search run by the default domain argument, including during delaboration.
macro_rules
  | `(tactic| ereal_div_domain) => `(tactic|
      set_option maxHeartbeats 4000 in
      solve
      | assumption
      | (apply EReal.DivDomain.of_isUnit; checked_unit)
      | (refine ⟨?_, ?_⟩
         · solve
           | exact top_ne_zero
           | exact bot_ne_zero
           | checked_nonzero
         · solve
           | assumption
           | exact Or.inl ‹_›
           | exact Or.inr ‹_›
           | (left
              constructor
              · solve
                | assumption
                | exact EReal.coe_ne_top _
                | exact EReal.zero_ne_top
                | exact EReal.natCast_ne_top _
                | exact ne_top_of_lt ‹_›
              · solve
                | assumption
                | exact EReal.coe_ne_bot _
                | exact EReal.zero_ne_bot
                | exact EReal.natCast_ne_bot _
                | exact ne_bot_of_gt ‹_›))
      | fail "extended-real division requires a nonzero denominator and a finite operand")

/-- The continuous extension of real division to its domain on the extended real line.
With a finite denominator it is division by a unit. With an infinite denominator its value is
zero. Write it as `a / b`. -/
protected def div (a b : EReal) (h : DivDomain a b := by ereal_div_domain) : EReal :=
  match b with
  | ⊥ => 0
  | ⊤ => 0
  | (x : ℝ) => Checked.div a (x : EReal) (isUnit_coe_iff.2 (coe_ne_zero.1 h.1))

/-- Ordinary division agrees with unit division for a finite nonzero denominator. -/
lemma div_eq_checked_div (a b : EReal) (hb : IsUnit b) {h : DivDomain a b} :
    a / b = Checked.div a b hb := by
  have ⟨hbot, htop, _⟩ := isUnit_iff.1 hb
  lift b to ℝ using ⟨htop, hbot⟩
  rfl

lemma isUnit_div {a b : EReal} {h : DivDomain a b} (ha : IsUnit a) (hb : IsUnit b) :
    IsUnit (a / b) :=
  (div_eq_checked_div a b hb).symm ▸ ha.div₀ hb

macro_rules
  | `(tactic| checked_unit) => `(tactic|
      (with_reducible apply EReal.isUnit_div) <;> checked_unit)

lemma div_eq_mul_inv (a b : EReal) {hb : IsUnit b} : a / b = a * b⁻¹ :=
  (div_eq_checked_div a b hb).trans rfl

lemma div_eq_inv_mul (a b : EReal) {hb : IsUnit b} : a / b = b⁻¹ * a :=
  (div_eq_mul_inv a b (hb := hb)).trans (mul_comm _ _)

@[simp]
lemma div_top (a : EReal) {h : DivDomain a ⊤} : a / ⊤ = 0 := rfl

@[simp]
lemma div_bot (a : EReal) {h : DivDomain a ⊥} : a / ⊥ = 0 := rfl

@[simp]
lemma zero_div (b : EReal) {h : DivDomain 0 b} : 0 / b = 0 := by
  induction b
  · rfl
  · exact zero_mul _
  · rfl

@[simp]
lemma div_one (a : EReal) : a / (1 : EReal) = a :=
  (div_eq_checked_div a 1 isUnit_one).trans (div_one₀ a)

@[simp]
lemma mul_div_cancel_right (a b : EReal) {hb : IsUnit b} : (a * b) / b = a :=
  (div_eq_checked_div (a * b) b hb).trans (mul_div_cancel_right₀ a)

@[simp]
lemma mul_div_cancel_left (a b : EReal) {ha : IsUnit a} : (a * b) / a = b :=
  (div_eq_checked_div (a * b) a ha).trans (mul_div_cancel_left₀ b)

@[simp]
lemma div_mul_cancel (a b : EReal) {hb : IsUnit b} : a / b * b = a :=
  (congrArg (· * b) (div_eq_checked_div a b hb)).trans (div_mul_cancel₀ a)

lemma div_eq_iff {a b c : EReal} {hb : IsUnit b} : a / b = c ↔ a = c * b := by
  rw [div_eq_checked_div _ _ hb, _root_.div_eq_iff (hb := hb)]

lemma neg_div {a b : EReal} {h : DivDomain a b} {hn : DivDomain (-a) b} :
    -a / b = -(a / b) := by
  induction b with
  | bot => simp
  | top => simp
  | coe r =>
    have hr := isUnit_coe_iff.2 (coe_ne_zero.1 h.1)
    simp only [div_eq_mul_inv _ _ (hb := hr), neg_mul]

lemma coe_div (a b : ℝ) {hb : IsUnit b} : ((a / b : ℝ) : EReal) = (a : EReal) / (b : EReal) := by
  rw [div_eq_mul_inv₀, div_eq_mul_inv _ _ (hb := isUnit_coe_iff.2 hb.ne_zero), coe_mul, coe_inv]

theorem natCast_div_le (m n : ℕ) {hn : IsUnit (n : EReal)} :
    (Nat.euclideanDiv m n (fun he => (isUnit_iff.1 hn).2.2 (he ▸ Nat.cast_zero)) : EReal) ≤
      (m : EReal) / (n : EReal) := by
  have hn' : n ≠ 0 := by
    rintro rfl
    exact (isUnit_iff.1 hn).2.2 Nat.cast_zero
  simp only [← coe_coe_eq_natCast]
  rw [← coe_div (hb := (Nat.cast_ne_zero.2 hn').isUnit), EReal.coe_le_coe_iff]
  exact Nat.cast_div_le (hn := (Nat.cast_ne_zero.2 hn').isUnit)

lemma top_div_of_pos_ne_top {a : EReal} (h : 0 < a) (h' : a ≠ ⊤) : ⊤ / a = ⊤ := by
  rw [div_eq_mul_inv ⊤ a (hb := by checked_unit)]
  exact top_mul_of_pos (inv_pos_of_pos_ne_top h h')

lemma top_div_of_neg_ne_bot {a : EReal} (h : a < 0) (h' : a ≠ ⊥) : ⊤ / a = ⊥ := by
  rw [div_eq_mul_inv ⊤ a (hb := by checked_unit)]
  exact top_mul_of_neg (inv_neg_of_neg_ne_bot h h')

lemma bot_div_of_pos_ne_top {a : EReal} (h : 0 < a) (h' : a ≠ ⊤) : ⊥ / a = ⊥ := by
  rw [div_eq_mul_inv ⊥ a (hb := by checked_unit)]
  exact bot_mul_of_pos (inv_pos_of_pos_ne_top h h')

lemma bot_div_of_neg_ne_bot {a : EReal} (h : a < 0) (h' : a ≠ ⊥) : ⊥ / a = ⊤ := by
  rw [div_eq_mul_inv ⊥ a (hb := by checked_unit)]
  exact bot_mul_of_neg (inv_neg_of_neg_ne_bot h h')

/-! #### Division and Order -/

variable {a b c : EReal}

lemma monotone_div_right_of_nonneg {hb : IsUnit b} (h : 0 ≤ b) : Monotone fun a ↦ a / b := by
  intro a a' h'
  simpa only [div_eq_mul_inv _ _ (hb := hb)] using
    mul_le_mul_of_nonneg_right h' (inv_nonneg_of_nonneg (ha := hb) h)

@[gcongr]
lemma div_le_div_right_of_nonneg {hc : IsUnit c} (h : 0 ≤ c) (h' : a ≤ b) : a / c ≤ b / c :=
  monotone_div_right_of_nonneg (hb := hc) h h'

lemma strictMono_div_right_of_pos (h : 0 < b) (h' : b ≠ ⊤) : StrictMono fun a ↦ a / b := by
  have hb : IsUnit b := isUnit_iff.2 ⟨ne_bot_of_gt h, h', h.ne'⟩
  intro a a' a_lt_a'
  apply lt_of_le_of_ne <| div_le_div_right_of_nonneg (hc := hb) (le_of_lt h) (le_of_lt a_lt_a')
  intro hyp
  apply ne_of_lt a_lt_a'
  simpa only [div_mul_cancel _ _ (hb := hb)] using congrArg (· * b) hyp

@[gcongr]
lemma div_lt_div_right_of_pos (h₁ : 0 < c) (h₂ : c ≠ ⊤) (h₃ : a < b) : a / c < b / c :=
  strictMono_div_right_of_pos h₁ h₂ h₃

lemma antitone_div_right_of_nonpos {hb : IsUnit b} (h : b ≤ 0) : Antitone fun a ↦ a / b := by
  intro a a' h'
  have key : ∀ x : EReal, x / b = -(x / -b) := fun x ↦ by
    rw [div_eq_mul_inv (hb := hb), div_eq_mul_inv (hb := hb.neg), inv_neg₀ (ha := hb.neg), mul_neg,
      neg_neg]
  change a' / b ≤ a / b
  rw [key a, key a', neg_le_neg_iff]
  have : 0 ≤ -b := by apply EReal.le_neg_of_le_neg; simp [h]
  exact div_le_div_right_of_nonneg (hc := hb.neg) this h'

lemma div_le_div_right_of_nonpos {hc : IsUnit c} (h : c ≤ 0) (h' : a ≤ b) : b / c ≤ a / c :=
  antitone_div_right_of_nonpos (hb := hc) h h'

lemma strictAnti_div_right_of_neg (h : b < 0) (h' : b ≠ ⊥) : StrictAnti fun a ↦ a / b := by
  have hb : IsUnit b := isUnit_iff.2 ⟨h', ne_top_of_lt h, h.ne⟩
  intro a a' a_lt_a'
  apply lt_of_le_of_ne <| div_le_div_right_of_nonpos (hc := hb) (le_of_lt h) (le_of_lt a_lt_a')
  intro hyp
  apply ne_of_lt a_lt_a'
  simpa only [div_mul_cancel _ _ (hb := hb)] using congrArg (· * b) hyp.symm

lemma div_lt_div_right_of_neg (h₁ : c < 0) (h₂ : c ≠ ⊥) (h₃ : a < b) : b / c < a / c :=
  strictAnti_div_right_of_neg h₁ h₂ h₃

lemma le_div_iff_mul_le (h : b > 0) (h' : b ≠ ⊤) : a ≤ c / b ↔ a * b ≤ c := by
  have hb : IsUnit b := isUnit_iff.2 ⟨ne_bot_of_gt h, h', h.ne'⟩
  rw [← (strictMono_div_right_of_pos h h').le_iff_le (a := a * b) (b := c)]
  rw [mul_div_cancel_right (hb := hb)]

lemma div_le_iff_le_mul (h : 0 < b) (h' : b ≠ ⊤) : a / b ≤ c ↔ a ≤ b * c := by
  have hb : IsUnit b := isUnit_iff.2 ⟨ne_bot_of_gt h, h', h.ne'⟩
  rw [mul_comm b c, ← (strictMono_div_right_of_pos h h').le_iff_le (a := a) (b := c * b)]
  rw [mul_div_cancel_right (hb := hb)]

lemma lt_div_iff (h : 0 < b) (h' : b ≠ ⊤) : a < c / b ↔ a * b < c := by
  have hb : IsUnit b := isUnit_iff.2 ⟨ne_bot_of_gt h, h', h.ne'⟩
  rw [← (strictMono_div_right_of_pos h h').lt_iff_lt (a := a * b) (b := c)]
  rw [mul_div_cancel_right (hb := hb)]

lemma div_lt_iff (h : 0 < c) (h' : c ≠ ⊤) : b / c < a ↔ b < a * c := by
  have hc : IsUnit c := isUnit_iff.2 ⟨ne_bot_of_gt h, h', h.ne'⟩
  rw [← (strictMono_div_right_of_pos h h').lt_iff_lt (a := b) (b := a * c)]
  rw [mul_div_cancel_right (hb := hc)]

lemma div_nonneg {h : DivDomain a b} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a / b := by
  by_cases htop : b = ⊤
  · subst b
    simp
  have hu := isUnit_iff.2 ⟨ne_bot_of_gt (bot_lt_zero.trans_le hb), htop, h.1⟩
  rw [div_eq_mul_inv (hb := hu)]
  exact mul_nonneg ha (inv_nonneg_of_nonneg (ha := hu) hb)

lemma div_pos (ha : 0 < a) (hb : 0 < b) (hb' : b ≠ ⊤) : 0 < a / b := by
  rw [div_eq_mul_inv a b (hb := by checked_unit)]
  exact EReal.mul_pos ha (inv_pos_of_pos_ne_top hb hb')

lemma div_nonpos_of_nonpos_of_nonneg {hb : IsUnit b} (h : a ≤ 0) (h' : 0 ≤ b) : a / b ≤ 0 := by
  rw [div_eq_mul_inv (hb := hb)]
  exact mul_nonpos_of_nonpos_of_nonneg h (inv_nonneg_of_nonneg (ha := hb) h')

lemma div_nonpos_of_nonneg_of_nonpos {hb : IsUnit b} (h : 0 ≤ a) (h' : b ≤ 0) : a / b ≤ 0 := by
  rw [div_eq_mul_inv (hb := hb)]
  exact mul_nonpos_of_nonneg_of_nonpos h (inv_nonpos_of_nonpos (ha := hb) h')

lemma div_nonneg_of_nonpos_of_nonpos {hb : IsUnit b} (h : a ≤ 0) (h' : b ≤ 0) : 0 ≤ a / b :=
  le_of_eq_of_le (zero_div (h := DivDomain.of_isUnit 0 hb) b).symm
    (div_le_div_right_of_nonpos (hc := hb) h' h)

private lemma exists_lt_mul_left_of_nonneg (ha : 0 ≤ a) (hc : 0 ≤ c) (h : c < a * b) :
    ∃ a' ∈ Ioo 0 a, c < a' * b := by
  rcases eq_or_ne b ⊤ with rfl | b_top
  · rcases eq_or_lt_of_le ha with rfl | ha
    · rw [zero_mul] at h
      exact (not_le_of_gt h hc).rec
    · obtain ⟨a', a0', aa'⟩ := exists_between ha
      use a', mem_Ioo.2 ⟨a0', aa'⟩
      rw [mul_top_of_pos ha] at h
      rwa [mul_top_of_pos a0']
  · have b0 : 0 < b := pos_of_mul_pos_right (hc.trans_lt h) ha
    obtain ⟨a', ha', aa'⟩ := exists_between ((div_lt_iff b0 b_top).2 h)
    exact ⟨a', ⟨(div_nonneg hc b0.le).trans_lt ha', aa'⟩, (div_lt_iff b0 b_top).1 ha'⟩

private lemma exists_lt_mul_right_of_nonneg (ha : 0 ≤ a) (hc : 0 ≤ c) (h : c < a * b) :
    ∃ b' ∈ Ioo 0 b, c < a * b' := by
  have hb : 0 < b := pos_of_mul_pos_right (hc.trans_lt h) ha
  simp_rw [mul_comm a] at h ⊢
  exact exists_lt_mul_left_of_nonneg hb.le hc h

private lemma exists_mul_left_lt (h₁ : a ≠ 0 ∨ b ≠ ⊤) (h₂ : a ≠ ⊤ ∨ 0 < b) (hc : a * b < c) :
    ∃ a' ∈ Ioo a ⊤, a' * b < c := by
  rcases eq_top_or_lt_top a with rfl | a_top
  · rw [ne_self_iff_false, false_or] at h₂; rw [top_mul_of_pos h₂] at hc; exact (not_top_lt hc).rec
  rcases le_or_gt b 0 with b0 | b0
  · obtain ⟨a', aa', a_top'⟩ := exists_between a_top
    exact ⟨a', mem_Ioo.2 ⟨aa', a_top'⟩, lt_of_le_of_lt (mul_le_mul_of_nonpos_right aa'.le b0) hc⟩
  rcases eq_top_or_lt_top b with rfl | b_top
  · rcases lt_trichotomy a 0 with a0 | rfl | a0
    · obtain ⟨a', aa', a0'⟩ := exists_between a0
      rw [mul_top_of_neg a0] at hc
      refine ⟨a', mem_Ioo.2 ⟨aa', lt_top_of_lt a0'⟩, mul_top_of_neg a0' ▸ hc⟩
    · rw [ne_self_iff_false, ne_self_iff_false, false_or] at h₁; exact h₁.rec
    · rw [mul_top_of_pos a0] at hc; exact (not_top_lt hc).rec
  · obtain ⟨a', aa', hc'⟩ := exists_between ((lt_div_iff b0 b_top.ne).2 hc)
    exact ⟨a', mem_Ioo.2 ⟨aa', lt_top_of_lt hc'⟩, (lt_div_iff b0 b_top.ne).1 hc'⟩

private lemma exists_mul_right_lt (h₁ : 0 < a ∨ b ≠ ⊤) (h₂ : a ≠ ⊤ ∨ b ≠ 0) (hc : a * b < c) :
    ∃ b' ∈ Ioo b ⊤, a * b' < c := by
  simp_rw [mul_comm a] at hc ⊢
  exact exists_mul_left_lt h₂.symm h₁.symm hc

lemma le_mul_of_forall_lt (h₁ : 0 < a ∨ b ≠ ⊤) (h₂ : a ≠ ⊤ ∨ 0 < b)
    (h : ∀ a' > a, ∀ b' > b, c ≤ a' * b') : c ≤ a * b := by
  refine le_of_forall_gt_imp_ge_of_dense fun d hd ↦ ?_
  obtain ⟨a', aa', hd⟩ := exists_mul_left_lt (h₁.imp_left ne_of_gt) h₂ hd
  replace h₁ : 0 < a' ∨ b ≠ ⊤ := h₁.imp_left fun a0 ↦ a0.trans (mem_Ioo.1 aa').1
  replace h₂ : a' ≠ ⊤ ∨ b ≠ 0 := Or.inl (mem_Ioo.1 aa').2.ne
  obtain ⟨b', bb', hd⟩ := exists_mul_right_lt h₁ h₂ hd
  exact (h a' (mem_Ioo.1 aa').1 b' (mem_Ioo.1 bb').1).trans hd.le

lemma mul_le_of_forall_lt_of_nonneg (ha : 0 ≤ a) (hc : 0 ≤ c)
    (h : ∀ a' ∈ Ioo 0 a, ∀ b' ∈ Ioo 0 b, a' * b' ≤ c) : a * b ≤ c := by
  refine le_of_forall_lt_imp_le_of_dense fun d dab ↦ ?_
  rcases lt_or_ge d 0 with d0 | d0
  · exact d0.le.trans hc
  obtain ⟨a', aa', dab⟩ := exists_lt_mul_left_of_nonneg ha d0 dab
  obtain ⟨b', bb', dab⟩ := exists_lt_mul_right_of_nonneg aa'.1.le d0 dab
  exact dab.le.trans (h a' aa' b' bb')

/-! #### Division Distributivity -/

lemma div_right_distrib_of_nonneg {hc : IsUnit c} (h : 0 ≤ a) (h' : 0 ≤ b) :
    (a + b) / c = a / c + b / c := by
  simp only [div_eq_mul_inv _ _ (hb := hc)]
  exact EReal.right_distrib_of_nonneg h h'

lemma add_div_of_nonneg_right {hc : IsUnit c} (h : 0 ≤ c) :
    (a + b) / c = a / c + b / c := by
  simp only [div_eq_mul_inv _ _ (hb := hc)]
  exact right_distrib_of_nonneg_of_ne_top
    (inv_nonneg_of_nonneg (ha := hc) h) (inv_lt_top c (hx := hc)).ne a b

/-- Ordinary nonnegative division commutes with the embedding into the signed extended reals. -/
theorem coe_ennreal_div (a b : ℝ≥0∞) (h : b ≠ 0 ∧ (a ≠ ⊤ ∨ b ≠ ⊤)) :
    ((a / b : ℝ≥0∞) : EReal) =
      EReal.div (a : EReal) (b : EReal) (divDomain_coe_ennreal.2 h) := by
  by_cases hb : b = ⊤
  · subst b
    change ((a * (⊤ : ℝ≥0∞)⁻¹ : ℝ≥0∞) : EReal) = EReal.div (a : EReal) ⊤ _
    rw [ENNReal.inv_top, mul_zero, coe_ennreal_zero]
    rfl
  have hu : IsUnit (b : EReal) :=
    isUnit_iff.2 ⟨coe_ennreal_ne_bot b, coe_ennreal_eq_top_iff.not.2 hb, coe_ennreal_ne_zero.2 h.1⟩
  have hinv : ((b⁻¹ : ℝ≥0∞) : EReal) = Checked.inv (b : EReal) hu :=
    eq_inv_of_mul_eq_one_left₀ (by
      rw [← coe_ennreal_mul, ENNReal.inv_mul_cancel h.1 hb, coe_ennreal_one])
  change ((a * b⁻¹ : ℝ≥0∞) : EReal) = _
  rw [div_eq_mul_inv _ _ (hb := hu), coe_ennreal_mul, hinv]

theorem div_coe_ennreal_nonneg (a b : ℝ≥0∞) (h : DivDomain (a : EReal) (b : EReal)) :
    0 ≤ (a : EReal) / (b : EReal) := by
  rw [← coe_ennreal_div a b (divDomain_coe_ennreal.1 h)]
  exact coe_ennreal_nonneg _

end EReal

namespace Mathlib.Meta.Positivity

open Lean Meta Qq

/-- Extension for the `positivity` tactic: inverse of an `EReal`, the inverse of a unit. -/
@[positivity Checked.inv _ _]
meta def evalERealInv : PositivityExt where eval {u α} zα pα? e :=
  match pα? with | none => pure .none | some pα => do
  match u, α, e with
  | 0, ~q(EReal), e =>
    let e' ← withReducible (whnf e)
    unless e'.isAppOfArity ``Checked.inv 4 do throwError "not an inverse of an `EReal`"
    let .app (.app _ (a : Q(EReal))) (ha : Q(IsUnit $a)) := e'
      | throwError "not an inverse of an `EReal`"
    let _e_eq : $e =Q Checked.inv $a $ha := ⟨⟩
    assertInstancesCommute
    match (← core zα pα a).toNonneg with
    | some pa => pure (.nonnegative q(inv_nonneg_of_nonneg (ha := $ha) $pa))
    | none => pure .none
  | _, _, _ => throwError "not an inverse of an `EReal`"

/-- Extension for the `positivity` tactic for ordinary `EReal` division. -/
@[positivity EReal.div _ _ _]
meta def evalERealDiv : PositivityExt where eval {u α} zα pα? e :=
  match pα? with | none => pure .none | some pα => do
  match u, α, e with
  | 0, ~q(EReal), e =>
    let .app (.app (.app (.const ``EReal.div _) (a : Q(EReal))) (b : Q(EReal)))
      (h : Q(EReal.DivDomain $a $b)) := e
      | throwError "not a ratio of two extended real numbers"
    let _e_eq : $e =Q EReal.div $a $b $h := ⟨⟩
    assertInstancesCommute
    let some pa := (← core zα pα a).toNonneg | return .none
    let some pb := (← core zα pα b).toNonneg | return .none
    return .nonnegative q(EReal.div_nonneg (h := $h) $pa $pb)
  | _, _, _ => throwError "not a ratio of two extended real numbers"

end Mathlib.Meta.Positivity
