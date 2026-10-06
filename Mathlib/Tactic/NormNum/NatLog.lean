/-
Copyright (c) 2024 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Andreas Gittis
-/
module

public meta import Mathlib.Data.Nat.Log
public import Mathlib.Data.Nat.Log
public import Mathlib.Tactic.NormNum
public import Batteries.Lean.Expr

/-! # `norm_num` extensions for `Nat.log` and `Nat.clog`

This module defines `norm_num` extensions for `Nat.log` and `Nat.clog`.
-/

public meta section

namespace Mathlib.Meta.NormNum

open Qq Lean Elab.Tactic

lemma one_lt_of_blt {b : ℕ} (h : Nat.blt 1 b = true) : 1 < b := Nat.blt_eq.mp h

lemma ne_zero_of_blt {n : ℕ} (h : Nat.blt 0 n = true) : n ≠ 0 := (Nat.blt_eq.mp h).ne'

lemma nat_log_helper0 (b n : Nat) {hb : 1 < b} {hn : n ≠ 0} (hl : Nat.blt n b = true) :
    Nat.log b n hb hn = 0 :=
  Nat.log_of_lt hb hn (Nat.blt_eq.mp hl)

lemma nat_log_helper (b n k : Nat) {hb : 1 < b} {hn : n ≠ 0}
    (hl : Nat.ble (b ^ k) n = true) (hh : Nat.blt n (b ^ (k + 1)) = true) :
    Nat.log b n hb hn = k :=
  Nat.log_eq_of_pow_le_of_lt_pow (Nat.le_of_ble_eq_true hl) (Nat.le_of_ble_eq_true hh)

theorem isNat_log : {b nb n nn k : ℕ} → {hb : 1 < b} → {hn : n ≠ 0} → IsNat b nb → IsNat n nn →
    (hb' : 1 < nb) → (hn' : nn ≠ 0) → Nat.log nb nn hb' hn' = k → IsNat (Nat.log b n hb hn) k
  | _, _, _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, _, _, rfl => ⟨rfl⟩

/--
Given the natural number literals `eb` and `en` with `1 < eb` and `en ≠ 0`, returns
`Nat.log eb en` as a natural number literal and an equality proof.
Panics if `eb` or `en` aren't natural number literals.
-/
def proveNatLog (eb en : Q(ℕ)) (hb : Q(1 < $eb)) (hn : Q($en ≠ 0)) :
    (ek : Q(ℕ)) × Q(Nat.log $eb $en $hb $hn = $ek) :=
  let b := eb.natLit!
  let n := en.natLit!
  if n < b then
    have hh : Q(Nat.blt $en $eb = true) := (q(Eq.refl true) : Expr)
    ⟨q(nat_lit 0), q(nat_log_helper0 $eb $en (hb := $hb) (hn := $hn) $hh)⟩
  else
    let k := if h : 1 < b ∧ n ≠ 0 then Nat.log b n h.1 h.2 else 0
    have ek : Q(ℕ) := mkRawNatLit k
    have hl : Q(Nat.ble ($eb ^ $ek) $en = true) := (q(Eq.refl true) : Expr)
    have hh : Q(Nat.blt $en ($eb ^ ($ek + 1)) = true) := (q(Eq.refl true) : Expr)
    ⟨ek, q(nat_log_helper $eb $en $ek (hb := $hb) (hn := $hn) $hl $hh)⟩

/--
Evaluates the `Nat.log` function.
-/
@[norm_num Nat.log _ _ _ _]
def evalNatLog : NormNumExt where eval {u α} e := do
  let .app (.app (.app (.app (.const ``Nat.log _) (b : Q(ℕ))) (n : Q(ℕ))) (hb : Q(1 < $b)))
    (hn : Q($n ≠ 0)) ← Meta.whnfR e | failure
  let sℕ : Q(AddMonoidWithOne ℕ) := q(Nat.instAddMonoidWithOne)
  let ⟨eb, pb⟩ ← deriveNat b sℕ
  let ⟨en, pn⟩ ← deriveNat n sℕ
  unless 1 < eb.natLit! ∧ en.natLit! ≠ 0 do failure
  have hbl : Q(Nat.blt 1 $eb = true) := (q(Eq.refl true) : Expr)
  have hnl : Q(Nat.blt 0 $en = true) := (q(Eq.refl true) : Expr)
  let hb' : Q(1 < $eb) := q(one_lt_of_blt $hbl)
  let hn' : Q($en ≠ 0) := q(ne_zero_of_blt $hnl)
  let ⟨ek, pf⟩ := proveNatLog eb en hb' hn'
  let pf' : Q(IsNat (Nat.log $b $n $hb $hn) $ek) :=
    q(isNat_log (hb := $hb) (hn := $hn) $pb $pn $hb' $hn' $pf)
  return .isNat sℕ ek pf'

lemma clog_cond_of_bool {b n : ℕ} (h : (Nat.blt 1 b || Nat.ble n 1) = true) : 1 < b ∨ n ≤ 1 := by
  simpa [Nat.blt_eq, Nat.ble_eq] using h

lemma nat_clog_zero_right (b n : Nat) {h : 1 < b ∨ n ≤ 1} (hn : Nat.ble n 1 = true) :
    Nat.clog b n h = 0 := Nat.clog_of_right_le_one (Nat.le_of_ble_eq_true hn) b

theorem nat_clog_helper {b m n : ℕ} {h : 1 < b ∨ n ≤ 1} (hb : Nat.blt 1 b = true)
    (h₁ : Nat.blt (b ^ m) n = true) (h₂ : Nat.ble n (b ^ (m + 1)) = true) :
    Nat.clog b n h = m + 1 := by
  rw [Nat.blt_eq] at hb
  rw [Nat.blt_eq, ← Nat.lt_clog_iff_pow_lt hb] at h₁
  rw [Nat.ble_eq, ← Nat.clog_le_iff_le_pow hb] at h₂
  lia

theorem isNat_clog : {b nb n nn k : ℕ} → {h : 1 < b ∨ n ≤ 1} → IsNat b nb → IsNat n nn →
    (h' : 1 < nb ∨ nn ≤ 1) → Nat.clog nb nn h' = k → IsNat (Nat.clog b n h) k
  | _, _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, _, rfl => ⟨rfl⟩

/--
Given the natural number literals `eb` and `en` with `1 < eb ∨ en ≤ 1`, returns `Nat.clog eb en`
as a natural number literal and an equality proof.
Panics if `eb` or `en` aren't natural number literals.
-/
def proveNatClog (eb en : Q(ℕ)) (h : Q(1 < $eb ∨ $en ≤ 1)) :
    MetaM ((ek : Q(ℕ)) × Q(Nat.clog $eb $en $h = $ek)) := do
  let b := eb.natLit!
  let n := en.natLit!
  if _ : n ≤ 1 then
    have hn : Q(Nat.ble $en 1 = true) := reflBoolTrue
    return ⟨q(nat_lit 0), q(nat_clog_zero_right $eb $en (h := $h) $hn)⟩
  else if hb1 : b ≤ 1 then
    failure
  else
    match hc : Nat.clog b n (Or.inl (by lia)) with
    | 0 => return False.elim <|
      Nat.ne_of_gt (Nat.clog_pos (by lia) (by lia)) hc
    | k + 1 =>
      have ek : Q(ℕ) := mkRawNatLit k
      have ek1 : Q(ℕ) := mkRawNatLit (k + 1)
      have _ : $ek1 =Q $ek + 1 := ⟨⟩
      have hb : Q(Nat.blt 1 $eb = true) := reflBoolTrue
      have hl : Q(Nat.blt ($eb ^ $ek) $en = true) := reflBoolTrue
      have hh : Q(Nat.ble $en ($eb ^ ($ek + 1)) = true) := reflBoolTrue
      return ⟨ek1, q(nat_clog_helper (h := $h) $hb $hl $hh)⟩

/--
Evaluates the `Nat.clog` function.
-/
@[norm_num Nat.clog _ _ _]
def evalNatClog : NormNumExt where eval {u α} e := do
  let .app (.app (.app (.const ``Nat.clog _) (b : Q(ℕ))) (n : Q(ℕ))) (h : Q(1 < $b ∨ $n ≤ 1)) ←
    Meta.whnfR e | failure
  let sℕ : Q(AddMonoidWithOne ℕ) := q(Nat.instAddMonoidWithOne)
  let ⟨eb, pb⟩ ← deriveNat b sℕ
  let ⟨en, pn⟩ ← deriveNat n sℕ
  unless 1 < eb.natLit! ∨ en.natLit! ≤ 1 do failure
  have hc : Q((Nat.blt 1 $eb || Nat.ble $en 1) = true) := (q(Eq.refl true) : Expr)
  let h' : Q(1 < $eb ∨ $en ≤ 1) := q(clog_cond_of_bool $hc)
  let ⟨ek, pf⟩ ← proveNatClog eb en h'
  let pf' : Q(IsNat (Nat.clog $b $n $h) $ek) := q(isNat_clog (h := $h) $pb $pn $h' $pf)
  return .isNat sℕ ek pf'

end Mathlib.Meta.NormNum
