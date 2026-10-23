/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public meta import Mathlib.Data.Rat.Init
public import Mathlib.Algebra.Ring.Invertible
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Tactic.NormNum.Core

/-!
# Checked inverse certificates for `norm_num`

The inverse evaluator needs only the source unit evidence. Rational cast plugins
live in `Mathlib.Tactic.NormNum.Inv`, so integer-power evaluation can use these
certificates without importing the rational cast and ordered-field hierarchy.
-/

public meta section

namespace Mathlib.Meta.NormNum

open Lean.Meta Qq

private theorem inverse_fraction {α : Type*} [Monoid α] {a n d : α}
    [Invertible n] [Invertible d] (ha : IsUnit a) (h : a = n * ⅟d) :
    Checked.inv a ha = d * ⅟n := by
  symm
  apply ha.unit.eq_inv_of_mul_eq_one_left
  rw [ha.unit_spec, h, mul_assoc, ← mul_assoc (⅟d) d (⅟n),
    invOf_mul_self, one_mul, mul_invOf_self]

theorem isNNRat_inv_pos {α} [DivisionSemiring α] {a : α} {n d : ℕ}
    (ha : IsUnit a) (h : IsNNRat a (Nat.succ n) d) :
    IsNNRat (Checked.inv a ha) d (Nat.succ n) := by
  obtain ⟨invD, h⟩ := h
  let _ := invD
  have hn : (n.succ : α) ≠ 0 := by
    intro hn
    apply ha.ne_zero
    rw [h, hn, zero_mul]
  let _ := invertibleOfNonzero hn
  exact ⟨inferInstance, inverse_fraction ha h⟩

theorem isRat_inv_pos {α} [DivisionRing α] {a : α} {n d : ℕ}
    (ha : IsUnit a) (h : IsRat a (.ofNat (Nat.succ n)) d) :
    IsRat (Checked.inv a ha) (.ofNat d) (Nat.succ n) := by
  obtain ⟨invD, h⟩ := h
  let _ := invD
  have h' : a = (n.succ : α) * ⅟(d : α) := by
    simpa only [Int.ofNat_eq_natCast, Int.cast_natCast] using h
  have hn : (n.succ : α) ≠ 0 := by
    intro hn
    apply ha.ne_zero
    rw [h', hn, zero_mul]
  let _ := invertibleOfNonzero hn
  refine ⟨inferInstance, ?_⟩
  simpa only [Int.ofNat_eq_natCast, Int.cast_natCast] using inverse_fraction ha h'

theorem isRat_inv_neg {α} [DivisionRing α] {a : α} {n d : ℕ}
    (ha : IsUnit a) (h : IsRat a (.negOfNat (Nat.succ n)) d) :
    IsRat (Checked.inv a ha) (.negOfNat d) (Nat.succ n) := by
  obtain ⟨invD, h⟩ := h
  let _ := invD
  have h' : a = -(n.succ : α) * ⅟(d : α) := by
    simpa only [Int.negOfNat_eq, Int.ofNat_eq_natCast, Int.cast_neg, Int.cast_natCast] using h
  have hn : (n.succ : α) ≠ 0 := by
    intro hn
    apply ha.ne_zero
    rw [h', hn, neg_zero, zero_mul]
  let _ := invertibleOfNonzero hn
  let _ := invertibleNeg (n.succ : α)
  refine ⟨inferInstance, ?_⟩
  simpa only [Int.negOfNat_eq, Int.ofNat_eq_natCast, Int.cast_neg,
    Int.cast_natCast, invOf_neg, mul_neg, neg_mul] using inverse_fraction ha h'

open Lean

/-- The result of inverting a `norm_num` result. -/
meta def Result.inv {u : Level} {α : Q(Type u)} {a : Q($α)} (ra : Result a)
    (dsα : Q(DivisionSemiring $α)) (ha : Q(IsUnit $a)) :
    MetaM (Result q(Checked.inv $a $ha)) := do
  if let .some ⟨qa, na, da, pa⟩ := ra.toNNRat' dsα then
    if hqa : qa = 0 then
      failure
    else if qa > 0 then
      let qb := Rat.reciprocal qa hqa
      have lit2 : Q(ℕ) := mkRawNatLit (na.natLit! - 1)
      haveI : $na =Q ($lit2).succ := ⟨⟩
      return .isNNRat' dsα qb q($da) q($na) q(isNNRat_inv_pos $ha $pa)
    else
      failure
  else
    let dα : Q(DivisionRing $α) ← synthInstanceQ q(DivisionRing $α)
    assertInstancesCommute
    let some ⟨qa, na, da, pa⟩ := ra.toRat' dα | failure
    if hqa : qa = 0 then
      failure
    else if qa < 0 then
      let qb := Rat.reciprocal qa hqa
      have lit : Q(ℕ) := na.appArg!
      haveI : $na =Q Int.negOfNat $lit := ⟨⟩
      have lit2 : Q(ℕ) := mkRawNatLit (lit.natLit! - 1)
      haveI : $lit =Q ($lit2).succ := ⟨⟩
      return .isRat dα qb q(.negOfNat $da) lit q(isRat_inv_neg $ha $pa)
    else
      failure

/-- The `norm_num` extension which identifies checked inverses,
such that `norm_num` successfully recognises `a`. -/
@[norm_num (Checked.inv _ _ : _)] meta def evalInv : NormNumExt where eval {u α} e := do
  let .app (.app (.app (.app (.const ``Checked.inv _) _) (inst : Q(Monoid $α)))
      (a : Q($α))) (ha : Expr) := e | failure
  let ra ← derive a
  let dsα : Q(DivisionSemiring $α) ← synthInstanceQ q(DivisionSemiring $α)
  guard <| ← isDefEq inst q(@Semiring.toMonoid $α (@DivisionSemiring.toSemiring $α $dsα))
  have ha' : Q(@IsUnit $α (@Semiring.toMonoid $α
      (@DivisionSemiring.toSemiring $α $dsα)) $a) := ha
  ra.inv q($dsα) ha'

end Mathlib.Meta.NormNum
