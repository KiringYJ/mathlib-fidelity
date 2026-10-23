/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module

public meta import Mathlib.Algebra.Group.Nat.Defs

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv

/-!
# Nonzero cancellation factors from source denominator certificates

The product collected here need not be the least common denominator. Its cast is certified
nonzero using the original expression's evidence. A kernel-checked natural divisibility proof
then certifies the proposed cancellation factor, including in positive characteristic.
-/

public section

namespace Mathlib.Tactic.CancelDenoms

theorem denominator_one (K : Type*) [Field K] : ((1 : ℕ) : K) ≠ 0 := by simp

theorem denominator_mul {K : Type*} [Field K] {a b : ℕ}
    (ha : (a : K) ≠ 0) (hb : (b : K) ≠ 0) : ((a * b : ℕ) : K) ≠ 0 := by
  simpa only [Nat.cast_mul] using mul_ne_zero ha hb

theorem denominator_pow {K : Type*} [Field K] {a : ℕ}
    (ha : (a : K) ≠ 0) (n : ℕ) : ((a ^ n : ℕ) : K) ≠ 0 := by
  simpa only [Nat.cast_pow] using pow_ne_zero n ha

theorem cancelFactorNonzero_of_dvd {K : Type*} [Field K] {a : K} {n d : ℕ}
    (hn : Mathlib.Meta.NormNum.IsNat a n) (hd : (d : K) ≠ 0) (hdiv : n ∣ d) : a ≠ 0 := by
  intro ha
  have hn0 : (n : K) = 0 := hn.out.symm.trans ha
  obtain ⟨k, rfl⟩ := hdiv
  apply hd
  rw [Nat.cast_mul, hn0, zero_mul]

end Mathlib.Tactic.CancelDenoms

public meta section

open Lean Meta Qq Mathlib.Meta.NormNum

namespace Mathlib.Tactic.CancelDenoms

/-- A natural denominator product and a proof that its cast in the source field is nonzero. -/
private structure DenominatorCertificate where
  value : ℕ
  proof : Expr

private def oneCertificate (α : Expr) : MetaM DenominatorCertificate := do
  let inst ← synthInstance (← mkAppM ``Field #[α])
  return ⟨1, ← mkAppOptM ``denominator_one #[some α, some inst]⟩

private def mulCertificate (a b : DenominatorCertificate) : MetaM DenominatorCertificate := do
  if a.value == 1 then return b
  if b.value == 1 then return a
  return ⟨a.value * b.value, ← mkAppM ``denominator_mul #[a.proof, b.proof]⟩

private def resultCertificate {u : Level} {α : Q(Type u)} {e : Q($α)}
    (r : Result e) : MetaM DenominatorCertificate := do
  match r with
  | .isNNRat _ _ _ d p =>
    return ⟨d.natLit!, ← mkAppM ``IsNNRat.den_nz #[p]⟩
  | .isNegNNRat _ _ _ d p =>
    return ⟨d.natLit!, ← mkAppM ``IsRat.den_nz #[p]⟩
  | .isNat .. | .isNegNat .. => oneCertificate α
  | .isBool .. => throwError "a denominator certificate requires a field expression"

/-- Preserve the numeral syntax when reducing the value of a certified numeric unit. -/
private def numericInput (e : Expr) : MetaM Expr := do
  if let (``Units.val, #[_, _, unit]) := e.getAppFnArgs then
    if let (``Units.mk0, #[_, _, a, _]) := unit.getAppFnArgs then
      return a
  whnf e

private def numericCertificate {u : Level} {α : Q(Type u)} (e : Q($α)) :
    MetaM DenominatorCertificate := do
  let e' : Q($α) ← numericInput e
  try resultCertificate (← derive e) catch _ => resultCertificate (← derive e')

private def reciprocalCertificate {u : Level} {α : Q(Type u)} (e : Q($α)) (h : Expr) :
    MetaM DenominatorCertificate := do
  let dsα : Q(DivisionSemiring $α) ← synthInstanceQ q(DivisionSemiring $α)
  let e' : Q($α) ← numericInput e
  let inverse (a : Q($α)) : MetaM DenominatorCertificate := do
    let r ← derive a
    have ha : Q(@IsUnit $α (@Semiring.toMonoid $α
      (@DivisionSemiring.toSemiring $α $dsα)) $a) := h
    resultCertificate (← r.inv dsα ha)
  try inverse e catch _ => inverse e'

/-- Collect only arithmetic subexpressions; unrelated function arguments are not inspected. -/
private partial def collectDenominators {u : Level} {α : Q(Type u)} (e : Q($α)) :
    MetaM DenominatorCertificate := do
  let one ← oneCertificate α
  let reciprocal (a : Q($α)) (ha : Expr) := do
    try reciprocalCertificate a ha catch _ => pure one
  match e.getAppFnArgs with
  | (``NNRat.rawCast, #[_, _, _, d, hd])
  | (``Rat.rawCast, #[_, _, _, d, hd]) =>
    if let some n := d.rawNatLit? <|> d.nat? then return ⟨n, hd⟩
    return one
  | (``HAdd.hAdd, #[_, _, _, _, a, b])
  | (``HSub.hSub, #[_, _, _, _, a, b])
  | (``HMul.hMul, #[_, _, _, _, a, b]) =>
    mulCertificate (← collectDenominators (u := u) (α := α) a)
      (← collectDenominators (u := u) (α := α) b)
  | (``Neg.neg, #[_, _, a]) => collectDenominators (u := u) (α := α) a
  | (``HPow.hPow, #[_, t, _, _, a, n]) =>
    if t.isConstOf ``Nat then
      if let some k := n.nat? then
        let d ← collectDenominators (u := u) (α := α) a
        return ⟨d.value ^ k, ← mkAppM ``denominator_pow #[d.proof, mkNatLit k]⟩
    return one
  | (``Checked.div, #[_, _, a, b, hb]) =>
    let da ← collectDenominators (u := u) (α := α) a
    let db ← collectDenominators (u := u) (α := α) b
    mulCertificate (← mulCertificate da db) (← reciprocal b hb)
  | (``Checked.inv, #[_, _, a, ha]) =>
    mulCertificate (← collectDenominators (u := u) (α := α) a) (← reciprocal a ha)
  | (``divp, #[_, _, a, unit]) =>
    let b : Q($α) ← mkAppM ``Units.val #[unit]
    let hb ← mkAppM ``Units.isUnit #[unit]
    let da ← collectDenominators (u := u) (α := α) a
    let db ← collectDenominators (u := u) (α := α) b
    mulCertificate (← mulCertificate da db)
      (← reciprocal b hb)
  | (``Units.val, #[_, _, unit]) =>
    match unit.getAppFnArgs with
    | (``Inv.inv, #[_, _, v]) =>
      let a : Q($α) ← mkAppM ``Units.val #[v]
      let ha ← mkAppM ``Units.isUnit #[v]
      mulCertificate (← collectDenominators (u := u) (α := α) a) (← reciprocal a ha)
    | _ =>
      try numericCertificate e catch _ => pure one
  | _ =>
    try numericCertificate e catch _ => pure one

/-- Prove a proposed cancellation factor nonzero using the original expression's denominator
certificates. The proposed factor must divide the certified product; this is checked in the kernel.
No characteristic-zero hypothesis is introduced. -/
def proveCancelFactorNonzero (source : Expr) (factor : Nat) (factorExpr : Expr) : MetaM Expr := do
  let ⟨u, α, source⟩ ← inferTypeQ' source
  let _fα : Q(Field $α) ← synthInstanceQ q(Field $α)
  unless ← isDefEq (← inferType factorExpr) α do
    throwError "the cancellation factor and source have different types"
  have factorExpr : Q($α) := factorExpr
  let ⟨n, hn⟩ ← deriveNat factorExpr q(inferInstance)
  unless n.natLit! == factor do
    throwError "the cancellation factor expression does not represent {factor}"
  let d ← collectDenominators (u := u) (α := α) source
  let dn : Q(ℕ) := mkRawNatLit d.value
  unless factor ∣ d.value do
    throwError "cancellation factor {factor} does not divide source denominator product {d.value}"
  let hdiv ← mkDecideProofQ q($n ∣ $dn)
  mkAppM ``cancelFactorNonzero_of_dvd #[hn, d.proof, hdiv]

end Mathlib.Tactic.CancelDenoms
