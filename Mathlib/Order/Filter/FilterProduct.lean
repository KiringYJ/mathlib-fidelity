/-
Copyright (c) 2019 Abhimanyu Pallavi Sudhir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhimanyu Pallavi Sudhir, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Order.Filter.Ring
public import Mathlib.Order.Filter.Ultrafilter.Defs

/-!
# Ultraproducts

If `φ` is an ultrafilter, then the space of germs of functions `f : α → β` at `φ` is called
the *ultraproduct*. In this file we prove properties of ultraproducts that rely on `φ` being an
ultrafilter. Definitions and properties that work for any filter should go to `Order.Filter.Germ`.

A group with zero has no ambient inverse, so its germs carry no pointwise inverse. Over an
ultrafilter a nonzero germ is a unit, which makes the ultraproduct of a group with zero, a division
ring or a field again such a structure; its inverse is the inverse of units. The lemmas
`Filter.Germ.coe_inv₀`, `Filter.Germ.const_inv₀` and their analogues for division and integer
powers compute it from representatives.

## Tags

ultrafilter, ultraproduct
-/

public section


universe u v

variable {α : Type u} {β : Type v} {φ : Ultrafilter α}

namespace Filter

local notation3 "∀* "(...)", "r:(scoped p => Filter.Eventually p (Ultrafilter.toFilter φ)) => r

namespace Germ

open Ultrafilter

local notation "β*" => Germ (φ : Filter α) β

/-! ### Checked inverses of germs

In a monoid without an ambient inverse, such as a group with zero, the germ of an invertible
function or constant is invertible, and inversion, division and integer powers commute with taking
germs. These lemmas hold for every filter. -/

section Checked

variable {M : Type*} [Monoid M] {l : Filter α}

@[simp, norm_cast]
theorem coe_inv₀ (f : α → M) {hf : IsUnit f} :
    ((f⁻¹ : α → M) : Germ l M) =
      Checked.inv (f : Germ l M) (show IsUnit (f : Germ l M) from hf.map (coeMulHom l)) :=
  (inv_eq_of_mul_eq_one_right₀ (congrArg ofFun mul_inv_cancel₀)).symm

@[simp, norm_cast]
theorem const_inv₀ (a : M) {ha : IsUnit a} :
    ((a⁻¹ : M) : Germ l M) = Checked.inv (a : Germ l M)
      (show IsUnit (a : Germ l M) from (ha.map (Pi.constMonoidHom α M)).map (coeMulHom l)) :=
  (inv_eq_of_mul_eq_one_right₀ (congrArg const mul_inv_cancel₀)).symm

@[simp, norm_cast]
theorem coe_div₀ (f g : α → M) {hg : IsUnit g} :
    ((f / g : α → M) : Germ l M) = Checked.div (f : Germ l M) (g : Germ l M)
      (show IsUnit (g : Germ l M) from hg.map (coeMulHom l)) := by
  rw [div_eq_mul_inv₀, div_eq_mul_inv₀, coe_mul, coe_inv₀]

@[simp, norm_cast]
theorem const_div₀ (a b : M) {hb : IsUnit b} :
    ((a / b : M) : Germ l M) = Checked.div (a : Germ l M) (b : Germ l M)
      (show IsUnit (b : Germ l M) from (hb.map (Pi.constMonoidHom α M)).map (coeMulHom l)) := by
  rw [div_eq_mul_inv₀, div_eq_mul_inv₀, ← const_inv₀ b (ha := hb)]
  rfl

@[simp, norm_cast]
theorem coe_zpow₀ (f : α → M) (n : ℤ) {h : n < 0 → IsUnit f} :
    ((f ^ n : α → M) : Germ l M) = Checked.zpow (f : Germ l M) n
      fun hn ↦ show IsUnit (f : Germ l M) from (h hn).map (coeMulHom l) := by
  cases n with
  | ofNat k => exact coe_pow f k
  | negSucc k => rw [zpow_negSucc₀, zpow_negSucc₀, coe_inv₀]; rfl

@[simp, norm_cast]
theorem const_zpow₀ (a : M) (n : ℤ) {h : n < 0 → IsUnit a} :
    ((a ^ n : M) : Germ l M) = Checked.zpow (a : Germ l M) n fun hn ↦
      show IsUnit (a : Germ l M) from ((h hn).map (Pi.constMonoidHom α M)).map (coeMulHom l) := by
  cases n with
  | ofNat k => exact const_pow a k
  | negSucc k => rw [zpow_negSucc₀, zpow_negSucc₀, const_inv₀]; rfl

end Checked

/-- Over an ultrafilter, a germ that is not zero is eventually nonzero, hence a unit: its inverse
is the germ of the pointwise inverse wherever that exists. -/
instance instGroupWithZero [GroupWithZero β] : GroupWithZero β* where
  __ := instMonoidWithZero
  isUnit_of_ne_zero {x} := inductionOn x fun f hf ↦ by
    classical
    have H : ∀* y, f y ≠ 0 := (φ.em fun y ↦ f y = 0).resolve_left fun H ↦ hf <| coe_eq.2 H
    let g : α → β := fun y ↦ if hy : f y ≠ 0 then (f y)⁻¹ else 1
    refine ⟨⟨f, g, ?_, ?_⟩, rfl⟩ <;> exact coe_eq.2 <| H.mono fun y hy ↦ by simp [g, hy]

/-- In characteristic zero, the embedding of `ℚ≥0` sends `q` to the constant germ of `(q : β)`
and its action is the action `Filter.Germ.instSMul` on representatives. Characteristic zero of the
ultraproduct gives characteristic zero of `β`, because constant germs preserve natural casts. -/
instance instDivisionSemiring [DivisionSemiring β] : DivisionSemiring β* where
  toSemiring := instSemiring
  __ := instGroupWithZero
  nnratCastOfCharZero _ q :=
    haveI := CharZero.of_map_natCast (const : β → β*) fun _ ↦ rfl
    ((q : β) : β*)
  nnratCastOfCharZero_mul_den _ q :=
    congrArg const <| DivisionSemiring.nnratCastOfCharZero_mul_den
      (CharZero.of_map_natCast (const : β → β*) fun _ ↦ rfl) q
  nnqsmulOfCharZero _ q a :=
    haveI := CharZero.of_map_natCast (const : β → β*) fun _ ↦ rfl
    q • a
  nnqsmulOfCharZero_eq_mul _ q a := inductionOn a fun f ↦ congrArg ofFun <| funext fun x ↦
    DivisionSemiring.nnqsmulOfCharZero_eq_mul
      (CharZero.of_map_natCast (const : β → β*) fun _ ↦ rfl) q (f x)

/-- In characteristic zero, the embedding of `ℚ` sends `q` to the constant germ of `(q : β)` and
its action is the action `Filter.Germ.instSMul` on representatives. -/
instance instDivisionRing [DivisionRing β] : DivisionRing β* where
  __ := instRing
  __ := instDivisionSemiring
  ratCastOfCharZero _ q :=
    haveI := CharZero.of_map_natCast (const : β → β*) fun _ ↦ rfl
    ((q : β) : β*)
  ratCastOfCharZero_mul_den _ q :=
    congrArg const <| DivisionRing.ratCastOfCharZero_mul_den
      (CharZero.of_map_natCast (const : β → β*) fun _ ↦ rfl) q
  qsmulOfCharZero _ q a :=
    haveI := CharZero.of_map_natCast (const : β → β*) fun _ ↦ rfl
    q • a
  qsmulOfCharZero_eq_mul _ q a := inductionOn a fun f ↦ congrArg ofFun <| funext fun x ↦
    DivisionRing.qsmulOfCharZero_eq_mul
      (CharZero.of_map_natCast (const : β → β*) fun _ ↦ rfl) q (f x)

instance instSemifield [Semifield β] : Semifield β* where
  __ := instCommSemiring
  __ := instDivisionSemiring

instance instField [Field β] : Field β* where
  __ := instCommRing
  __ := instDivisionRing

theorem coe_lt [Preorder β] {f g : α → β} : (f : β*) < g ↔ ∀* x, f x < g x := by
  simp only [lt_iff_le_not_ge, eventually_and, coe_le, eventually_not, EventuallyLE]

theorem coe_pos [Preorder β] [Zero β] {f : α → β} : 0 < (f : β*) ↔ ∀* x, 0 < f x :=
  coe_lt

theorem const_lt [Preorder β] {x y : β} : x < y → (↑x : β*) < ↑y :=
  coe_lt.mpr ∘ liftRel_const

@[simp, norm_cast]
theorem const_lt_iff [Preorder β] {x y : β} : (↑x : β*) < ↑y ↔ x < y :=
  coe_lt.trans liftRel_const_iff

theorem lt_def [Preorder β] : ((· < ·) : β* → β* → Prop) = LiftRel (· < ·) := by
  ext ⟨f⟩ ⟨g⟩
  exact coe_lt

instance total [LE β] [@Std.Total β (· ≤ ·)] : @Std.Total β* (· ≤ ·) :=
  ⟨fun f g =>
    inductionOn₂ f g fun _f _g => eventually_or.1 <| Eventually.of_forall fun _x => total_of _ _ _⟩

open scoped Classical in
/-- If `φ` is an ultrafilter then the ultraproduct is a linear order. -/
noncomputable instance instLinearOrder [LinearOrder β] : LinearOrder β* :=
  Lattice.toLinearOrder _

instance instIsStrictOrderedRing [Semiring β] [PartialOrder β] [IsStrictOrderedRing β] :
    IsStrictOrderedRing β* where
  mul_lt_mul_of_pos_left x := inductionOn x fun _f hf y z ↦ inductionOn₂ y z fun _g _h hgh ↦
    coe_lt.2 <| (coe_lt.1 hf).mp <| (coe_lt.1 hgh).mono fun _a ↦ mul_lt_mul_of_pos_left
  mul_lt_mul_of_pos_right x := inductionOn x fun _f hf y z ↦ inductionOn₂ y z fun _g _h hgh ↦
    coe_lt.2 <| (coe_lt.1 hf).mp <| (coe_lt.1 hgh).mono fun _a ↦ mul_lt_mul_of_pos_right

theorem max_def [LinearOrder β] (x y : β*) : max x y = map₂ max x y :=
  inductionOn₂ x y fun a b => by
    rcases le_total (a : β*) b with h | h
    · rw [max_eq_right h, map₂_coe, coe_eq]
      exact h.mono fun i hi => (max_eq_right hi).symm
    · rw [max_eq_left h, map₂_coe, coe_eq]
      exact h.mono fun i hi => (max_eq_left hi).symm

theorem min_def [K : LinearOrder β] (x y : β*) : min x y = map₂ min x y :=
  inductionOn₂ x y fun a b => by
    rcases le_total (a : β*) b with h | h
    · rw [min_eq_left h, map₂_coe, coe_eq]
      exact h.mono fun i hi => (min_eq_left hi).symm
    · rw [min_eq_right h, map₂_coe, coe_eq]
      exact h.mono fun i hi => (min_eq_right hi).symm

theorem abs_def [AddCommGroup β] [LinearOrder β] (x : β*) :
    |x| = map abs x :=
  inductionOn x fun _a => rfl

@[simp]
theorem const_max [LinearOrder β] (x y : β) : (↑(max x y : β) : β*) = max ↑x ↑y := by
  rw [max_def, map₂_const]

@[simp]
theorem const_min [LinearOrder β] (x y : β) : (↑(min x y : β) : β*) = min ↑x ↑y := by
  rw [min_def, map₂_const]

@[simp]
theorem const_abs [AddCommGroup β] [LinearOrder β] (x : β) :
    (↑|x| : β*) = |↑x| := by
  rw [abs_def, map_const]

end Germ

end Filter
