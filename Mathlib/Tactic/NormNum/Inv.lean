/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.Tactic.NormNum.Inv.Basic
public import Mathlib.Tactic.NormNum.Basic
public meta import Mathlib.Data.Rat.Init

/-!
# `norm_num` plugins for `Rat.cast` and `⁻¹`.
-/

public meta section

variable {u : Lean.Level}

namespace Mathlib.Meta.NormNum

open Lean.Meta Qq

/-- Helper function to synthesize a typed `CharZero α` expression given `Ring α`. -/
def inferCharZeroOfRing {α : Q(Type u)} (_i : Q(Ring $α) := by with_reducible assumption) :
    MetaM Q(CharZero $α) :=
  return ← synthInstanceQ q(CharZero $α) <|>
    throwError "not a characteristic zero ring"

/-- Helper function to synthesize a typed `CharZero α` expression given `Ring α`, if it exists. -/
def inferCharZeroOfRing? {α : Q(Type u)} (_i : Q(Ring $α) := by with_reducible assumption) :
    MetaM (Option Q(CharZero $α)) :=
  return (← trySynthInstanceQ q(CharZero $α)).toOption

/-- Helper function to synthesize a typed `CharZero α` expression given `AddMonoidWithOne α`. -/
def inferCharZeroOfAddMonoidWithOne {α : Q(Type u)}
    (_i : Q(AddMonoidWithOne $α) := by with_reducible assumption) : MetaM Q(CharZero $α) :=
  return ← synthInstanceQ q(CharZero $α) <|>
    throwError "not a characteristic zero AddMonoidWithOne"

/-- Helper function to synthesize a typed `CharZero α` expression given `AddMonoidWithOne α`, if it
exists. -/
def inferCharZeroOfAddMonoidWithOne? {α : Q(Type u)}
    (_i : Q(AddMonoidWithOne $α) := by with_reducible assumption) :
      MetaM (Option Q(CharZero $α)) :=
  return (← trySynthInstanceQ q(CharZero $α)).toOption

/-- Helper function to synthesize a typed `CharZero α` expression given `DivisionRing α`. -/
def inferCharZeroOfDivisionRing {α : Q(Type u)}
    (_i : Q(DivisionRing $α) := by with_reducible assumption) : MetaM Q(CharZero $α) :=
  return ← synthInstanceQ q(CharZero $α) <|>
    throwError "not a characteristic zero division ring"

/-- Helper function to synthesize a typed `CharZero α` expression given `Divisionsemiring α`, if it
exists. -/
def inferCharZeroOfDivisionSemiring? {α : Q(Type u)}
    (_i : Q(DivisionSemiring $α) := by with_reducible assumption) : MetaM (Option Q(CharZero $α)) :=
  return (← trySynthInstanceQ (q(CharZero $α) : Q(Prop))).toOption

/-- Helper function to synthesize a typed `CharZero α` expression given `DivisionRing α`, if it
exists. -/
def inferCharZeroOfDivisionRing? {α : Q(Type u)}
    (_i : Q(DivisionRing $α) := by with_reducible assumption) : MetaM (Option Q(CharZero $α)) :=
  return (← trySynthInstanceQ q(CharZero $α)).toOption

theorem isNNRat_divNat : {a na n : ℕ} → {b nb d : ℕ} → IsNat a na → IsNat b nb →
    (hb : b ≠ 0) → (hnb : nb ≠ 0) → IsNNRat (NNRat.divNat na nb hnb) n d →
      IsNNRat (NNRat.divNat a b hb) n d
  | _, _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, _, _, h => h

/-- The `norm_num` extension which identifies expressions of the form `NNRat.divNat a b`,
such that `norm_num` successfully recognises both `a` and `b`, and returns `a / b`. -/
@[norm_num NNRat.divNat _ _ _]
def evalNNRatDivNat : NormNumExt where eval {u α} (e : Q(ℚ≥0)) : MetaM (Result e) := do
  let .app (.app (.app (.const ``NNRat.divNat _) (a : Q(ℕ))) (b : Q(ℕ)))
      (hb : Q($b ≠ 0)) ← whnfR e | failure
  haveI' : $e =Q NNRat.divNat $a $b $hb := ⟨⟩
  let ra ← derive q($a)
  let ⟨na, pa⟩ ← deriveNat q($a) q(AddCommMonoidWithOne.toAddMonoidWithOne)
  let ⟨nb, pb⟩ ← deriveNat q($b) q(AddCommMonoidWithOne.toAddMonoidWithOne)
  let hnb ← mkDecideProofQ q($nb ≠ 0)
  let rab ← derive q(NNRat.divNat $na $nb $hnb)
  let some ⟨q, n, d, p⟩ := rab.toNNRat' q(NNRat.instSemifield.toDivisionSemiring) | failure
  return .isNNRat _ q n d q(isNNRat_divNat $pa $pb $hb $hnb $p)

theorem isNat_ratCast {R : Type*} [DivisionRing R] [CharZero R] : {q : ℚ} → {n : ℕ} →
    IsNat q n → IsNat (q : R) n
  | _, _, ⟨rfl⟩ => ⟨by simp⟩

theorem isNat_nnratCast {R : Type*} [DivisionSemiring R] [CharZero R] : {q : ℚ≥0} → {n : ℕ} →
    IsNat q n → IsNat (q : R) n
  | _, _, ⟨rfl⟩ => ⟨by simp⟩

theorem isInt_ratCast {R : Type*} [DivisionRing R] [CharZero R] : {q : ℚ} → {n : ℤ} →
    IsInt q n → IsInt (q : R) n
  | _, _, ⟨rfl⟩ => ⟨by simp⟩

theorem isNNRat_ratCast {R : Type*} [DivisionRing R] [CharZero R] :
    {q : ℚ} → {n : ℕ} → {d : ℕ} →
    IsNNRat q n d → IsNNRat (q : R) n d
  | _, _, _, ⟨⟨qi, _, _⟩, rfl⟩ =>
      ⟨⟨(qi : R), by norm_cast, by norm_cast⟩, by simp only; norm_cast⟩

theorem isNNRat_nnratCast {R : Type*} [DivisionSemiring R] [CharZero R] :
    {q : ℚ≥0} → {n : ℕ} →
    {d : ℕ} → IsNNRat q n d → IsNNRat (q : R) n d
  | _, _, _, ⟨⟨qi, _, _⟩, rfl⟩ =>
      ⟨⟨(qi : R), by norm_cast, by norm_cast⟩, by simp only; norm_cast⟩

theorem isRat_ratCast {R : Type*} [DivisionRing R] [CharZero R] :
    {q : ℚ} → {n : ℤ} → {d : ℕ} →
    IsRat q n d → IsRat (q : R) n d
  | _, _, _, ⟨⟨qi, _, _⟩, rfl⟩ =>
      ⟨⟨(qi : R), by norm_cast, by norm_cast⟩, by simp only; norm_cast⟩

/-- The `norm_num` extension which identifies an expression `RatCast.ratCast q` where `norm_num`
recognizes `q`, returning the cast of `q`. -/
@[norm_num Rat.cast _, RatCast.ratCast _] def evalRatCast : NormNumExt where eval {u α} e := do
  let dα : Q(DivisionRing $α) ← inferDivisionRing α
  let _cz : Q(CharZero $α) ← inferCharZeroOfDivisionRing dα
  let .app r (a : Q(ℚ)) ← whnfR e | failure
  guard <|← withNewMCtxDepth <| isDefEq r q(@Rat.cast $α DivisionRing.toRatCast)
  let r ← derive q($a)
  haveI' : $e =Q @Rat.cast $α DivisionRing.toRatCast $a := ⟨⟩
  match r with
  | .isNat _ na pa =>
    assumeInstancesCommute
    return .isNat _ na q(isNat_ratCast $pa)
  | .isNegNat _ na pa =>
    assumeInstancesCommute
    return .isNegNat _ na q(isInt_ratCast $pa)
  | .isNNRat _ qa na da pa =>
    assumeInstancesCommute
    return .isNNRat q(inferInstance) qa na da q(isNNRat_ratCast $pa)
  | .isNegNNRat _ qa na da pa =>
    assumeInstancesCommute
    return .isNegNNRat dα qa na da q(isRat_ratCast $pa)
  | _ => failure

/-- The `norm_num` extension which identifies an expression `NNRat.cast q` where `norm_num`
recognizes `q`, returning the cast of `q`. -/
@[norm_num NNRat.cast _, NNRatCast.nnratCast _]
def evalNNRatCast : NormNumExt where eval {u α} e := do
  let dα : Q(DivisionSemiring $α) ← inferDivisionSemiring α
  let some (_cz : Q(CharZero $α)) ← inferCharZeroOfDivisionSemiring? dα | failure
  let ~q(@NNRat.cast _ $nα' $a) := e | failure
  guard <| ← matchesInstance nα' q(@DivisionSemiring.toNNRatCast _ $dα)
  match ← derive q($a) with
  | .isNat _ na pa =>
    assumeInstancesCommute
    return .isNat _ na q(isNat_nnratCast $pa)
  | .isNNRat _ qa na da pa =>
    assumeInstancesCommute
    return .isNNRat q(inferInstance) qa na da q(isNNRat_nnratCast $pa)
  | _ => failure

end Mathlib.Meta.NormNum
