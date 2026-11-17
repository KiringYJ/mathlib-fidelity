/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Thomas Murrills
-/
module

public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.Algebra.Order.Ring.Unbundled.Rat
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.SetLike

/-!
## `norm_num` plugin for scientific notation.
-/

public meta section

namespace Mathlib
open Lean
open Meta

namespace Meta.NormNum
open Qq

variable {α : Type*}

-- see note [norm_num lemma function equality]
theorem nnrat_divNat_pow10_eq_ofScientific (m e : ℕ) (h : 10 ^ e ≠ 0) :
    NNRat.divNat m (10 ^ e) h = OfScientific.ofScientific m true e := by
  apply NNRat.coe_injective
  rw [NNRat.coe_divNat]
  change Rat.fraction m (10 ^ e) h = Rat.ofScientific m true e
  rw [Rat.fraction, Rat.ofScientific]
  rfl

theorem nnrat_ofScientific_false (m e : ℕ) :
    OfScientific.ofScientific m false e = (m * 10 ^ e : ℚ≥0) := by
  change (⟨Rat.ofScientific m false e, _⟩ : ℚ≥0) = _
  apply NNRat.coe_injective
  simp only [NNRat.coe_mul, NNRat.coe_pow, NNRat.coe_natCast]
  change Rat.ofScientific m false e = (m : ℚ) * 10 ^ e
  simp [Rat.ofScientific]

-- see note [norm_num lemma function equality]
theorem isNNRat_ofScientific_of_true [DivisionSemiring α] [CharZero α] :
    {m e : ℕ} → {n : ℕ} → {d : ℕ} →
    (hpow : 10 ^ e ≠ 0) → IsNNRat (NNRat.divNat m (10 ^ e) hpow : α) n d →
      IsNNRat (OfScientific.ofScientific m true e : α) n d
  | m, e, _, _, hpow, h => by
      rw [← NNRat.cast_ofScientific, ← nnrat_divNat_pow10_eq_ofScientific m e hpow]
      exact h

-- see note [norm_num lemma function equality]
theorem isNat_ofScientific_of_false [DivisionSemiring α] [CharZero α] :
    {m e nm ne n : ℕ} →
    IsNat m nm → IsNat e ne → n = Nat.mul nm ((10 : ℕ) ^ ne) →
    IsNat (OfScientific.ofScientific m false e : α) n
  | _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, (rfl : (_ : ℕ) = _ * _) => ⟨by
      rw [← NNRat.cast_ofScientific, nnrat_ofScientific_false]
      norm_cast⟩

/-- The `norm_num` extension which identifies expressions in scientific notation, normalizing them
to rat casts if the scientific notation is inherited from the one for rationals. -/
@[norm_num OfScientific.ofScientific _ _ _] def evalOfScientific :
    NormNumExt where eval {u α} e := do
  let mkApp3 f (m : Q(ℕ)) (b : Q(Bool)) (exp : Q(ℕ)) ← whnfR e | failure
  let dα ← inferDivisionSemiring α
  let czα : Q(CharZero $α) ← synthInstanceQ q(CharZero $α) <|> failure
  guard <|← withNewMCtxDepth <| isDefEq f
    q(@OfScientific.ofScientific $α
      (@NNRatCast.toOfScientific $α (@DivisionSemiring.toNNRatCast $α $dα $czα)))
  haveI' : $e =Q @OfScientific.ofScientific $α
      (@NNRatCast.toOfScientific $α (@DivisionSemiring.toNNRatCast $α $dα $czα))
      $m $b $exp := ⟨⟩
  match b with
  | ~q(true) =>
    let hpow ← mkDecideProofQ q(10 ^ $exp ≠ 0)
    let rme ← derive q(NNRat.divNat $m (10 ^ $exp) $hpow)
    let some ⟨value, n, d, p⟩ := rme.toNNRat' q(NNRat.instSemifield.toDivisionSemiring) | failure
    let castProof := q(@isNNRat_nnratCast $α $dα $czα (NNRat.divNat $m (10 ^ $exp) $hpow) $n $d $p)
    return .isNNRat dα value n d
      q(@isNNRat_ofScientific_of_true $α $dα $czα $m $exp $n $d $hpow $castProof)
  | ~q(false) =>
    let ⟨nm, pm⟩ ← deriveNat m q(AddCommMonoidWithOne.toAddMonoidWithOne)
    let ⟨ne, pe⟩ ← deriveNat exp q(AddCommMonoidWithOne.toAddMonoidWithOne)
    have pm : Q(IsNat $m $nm) := pm
    have pe : Q(IsNat $exp $ne) := pe
    let m' := nm.natLit!
    let exp' := ne.natLit!
    let n' := Nat.mul m' (Nat.pow (10 : ℕ) exp')
    have n : Q(ℕ) := mkRawNatLit n'
    haveI' : $n =Q Nat.mul $nm ((10 : ℕ) ^ $ne) := ⟨⟩
    return .isNat _ n
      q(@isNat_ofScientific_of_false $α $dα $czα $m $exp $nm $ne $n
        $pm $pe (.refl $n))

end NormNum

end Meta

end Mathlib
