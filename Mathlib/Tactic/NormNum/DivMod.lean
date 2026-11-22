/-
Copyright (c) 2023 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Mario Carneiro
-/
module

public import Mathlib.Tactic.NormNum.Ineq
public meta import Mathlib.Data.Int.Init

/-!
# `norm_num` extensions for integer quotient, remainder and divisibility

This file adds support for integer Euclidean quotients, remainder and divisibility to `norm_num`.
-/

public meta section

namespace Mathlib
open Lean
open Meta

namespace Meta.NormNum
open Qq

lemma isInt_intDiv {a b a' b' c : ℤ} {r : ℕ} (hb : b ≠ 0)
    (pa : IsInt a a') (pb : IsInt b b') (h : b' * c + r = a')
    (hr : r.blt b'.natAbs = true) : IsInt (Int.euclideanDiv a b hb) c := by
  obtain ⟨⟨rfl⟩, ⟨rfl⟩⟩ := pa, pb
  exact ⟨by
    simpa only [Int.cast_id] using
      Int.euclideanDiv_eq_of_remainder hb h.symm (Int.natCast_nonneg r)
        (Int.ofNat_lt.mpr (Nat.blt_eq.mp hr))⟩

attribute [local instance] monadLiftOptionMetaM in
/-- Normalize an integer Euclidean quotient with numeral operands. -/
@[norm_num Int.euclideanDiv _ _ _]
def evalIntDiv : NormNumExt where eval {u α} e := do
  match u, α, e with
  | 0, ~q(ℤ), ~q(Int.euclideanDiv $a $b $hb) =>
    let rℤ : Q(Ring ℤ) := q(Int.instRing)
    let ⟨za, na, pa⟩ ← (← derive a).toInt rℤ
    let ⟨zb, nb, pb⟩ ← (← derive b).toInt rℤ
    if hd : zb ≠ 0 then
      let zc := Int.euclideanDiv za zb hd
      have nc := mkRawIntLit zc
      have nr : Q(ℕ) := mkRawNatLit (za % zb).toNat
      have h : Q($nb * $nc + $nr = $na) := (q(Eq.refl $na) : Expr)
      have hr : Q(Nat.blt $nr (Int.natAbs $nb) = true) := (q(Eq.refl true) : Expr)
      return .isInt rℤ nc zc q(isInt_intDiv $hb $pa $pb $h $hr)
    else failure
  | _, _, _ => failure

lemma isInt_emod {a b a' b' r : ℤ} (pa : IsInt a a') (pb : IsInt b b')
    (h : Int.emod a' b' = r) : IsInt (a % b) r := by
  obtain ⟨⟨rfl⟩, ⟨rfl⟩⟩ := pa, pb
  exact ⟨by
    simp only [Int.cast_id]
    exact h⟩

/-- Evaluate an integer remainder from the numeral results for its operands. -/
def evalIntMod.go (a na : Q(ℤ)) (za : ℤ) (pa : Q(IsInt $a $na))
    (b : Q(ℤ)) (rb : Result (u := .zero) b) : Option (Result q($a % $b)) := do
  let rℤ : Q(Ring ℤ) := q(Int.instRing)
  let ⟨zb, nb, pb⟩ ← rb.toInt rℤ
  let zr := za % zb
  have nr := mkRawIntLit zr
  have h : Q(Int.emod $na $nb = $nr) := (q(Eq.refl $nr) : Expr)
  return .isInt rℤ nr zr q(isInt_emod $pa $pb $h)

attribute [local instance] monadLiftOptionMetaM in
/-- The `norm_num` extension which identifies expressions of the form `Int.emod a b`,
such that `norm_num` successfully recognises both `a` and `b`. -/
@[norm_num (_ : ℤ) % _, Int.emod _ _]
partial def evalIntMod : NormNumExt where eval {u α} e := do
  let .app (.app f (a : Q(ℤ))) (b : Q(ℤ)) ← whnfR e | failure
  -- We assert that the default instance for `HMod` is `Int.emod` when the first parameter is `ℤ`.
  guard <|← withNewMCtxDepth <| isDefEq f q(HMod.hMod (α := ℤ))
  haveI' : u =QL 0 := ⟨⟩; haveI' : $α =Q ℤ := ⟨⟩
  haveI' : $e =Q ($a % $b) := ⟨⟩
  let rℤ : Q(Ring ℤ) := q(Int.instRing)
  let some ⟨za, na, pa⟩ := (← derive a).toInt rℤ | failure
  evalIntMod.go a na za pa b (← derive (u := .zero) b)

theorem isInt_dvd_true : {a b : ℤ} → {a' b' c : ℤ} →
    IsInt a a' → IsInt b b' → Int.mul a' c = b' → a ∣ b
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, rfl => ⟨_, rfl⟩

theorem isInt_dvd_false : {a b : ℤ} → {a' b' : ℤ} →
    IsInt a a' → IsInt b b' → Int.emod b' a' != 0 → ¬a ∣ b
  | _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, e => mt Int.emod_eq_zero_of_dvd (by simpa using! e)

attribute [local instance] monadLiftOptionMetaM in
/-- The `norm_num` extension which identifies expressions of the form `(a : ℤ) ∣ b`,
such that `norm_num` successfully recognises both `a` and `b`. -/
@[norm_num (_ : ℤ) ∣ _] def evalIntDvd : NormNumExt where eval {u α} e := do
  let .app (.app f (a : Q(ℤ))) (b : Q(ℤ)) ← whnfR e | failure
  haveI' : u =QL 0 := ⟨⟩; haveI' : $α =Q Prop := ⟨⟩
  haveI' : $e =Q ($a ∣ $b) := ⟨⟩
  -- We assert that the default instance for `Dvd` is `Int.dvd` when the first parameter is `ℤ`.
  guard <|← withNewMCtxDepth <| isDefEq f q(Dvd.dvd (α := ℤ))
  let rℤ : Q(Ring ℤ) := q(Int.instRing)
  let ⟨za, na, pa⟩ ← (← derive a).toInt rℤ
  let ⟨zb, nb, pb⟩ ← (← derive b).toInt rℤ
  if zb % za == 0 then
    let zc := if ha : za ≠ 0 then Int.euclideanDiv zb za ha else 0
    have c := mkRawIntLit zc
    haveI' : Int.mul $na $c =Q $nb := ⟨⟩
    return .isTrue q(isInt_dvd_true $pa $pb (.refl $nb))
  else
    have : Q(Int.emod $nb $na != 0) := (q(Eq.refl true) : Expr)
    return .isFalse q(isInt_dvd_false $pa $pb $this)

end Mathlib.Meta.NormNum
