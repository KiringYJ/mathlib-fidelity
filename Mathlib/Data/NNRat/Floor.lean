/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public meta import Mathlib.Data.Rat.Floor

public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Algebra.Order.Ring.NNRat
public import Mathlib.Data.Rat.Floor

/-!
# Floor Function for Non-negative Rational Numbers

## Summary

We define the `FloorSemiring` instance on `ℚ≥0`, and relate its operators to `NNRat.cast`.

Note that we cannot talk about `Int.fract`, which currently only works for rings.

## Tags

nnrat, rationals, ℚ≥0, floor
-/

@[expose] public section

assert_not_exists Finset

namespace NNRat

instance : FloorSemiring ℚ≥0 where
  floor q := ⌊q.val⌋₊
  ceil q := ⌈q.val⌉₊
  floor_of_neg h := absurd h (not_lt.2 zero_le)
  gc_floor {a n} h := by rw [← NNRat.coe_le_coe, Nat.le_floor_iff] <;> norm_cast
  gc_ceil {a b} := by rw [← NNRat.coe_le_coe, Nat.ceil_le]; norm_cast

@[simp, norm_cast]
theorem floor_coe (q : ℚ≥0) : ⌊(q : ℚ)⌋₊ = ⌊q⌋₊ := rfl

@[simp, norm_cast]
theorem ceil_coe (q : ℚ≥0) : ⌈(q : ℚ)⌉₊ = ⌈q⌉₊ := rfl

@[simp, norm_cast]
theorem coe_floor (q : ℚ≥0) : ↑⌊q⌋₊ = ⌊(q : ℚ)⌋ := Int.natCast_floor_eq_floor q.coe_nonneg

@[simp, norm_cast]
theorem coe_ceil (q : ℚ≥0) : ↑⌈q⌉₊ = ⌈(q : ℚ)⌉ := Int.natCast_ceil_eq_ceil q.coe_nonneg

protected theorem floor_def (q : ℚ≥0) : ⌊q⌋₊ = Nat.euclideanDiv q.num q.den q.den_ne_zero := by
  rw [← Int.natCast_inj, NNRat.coe_floor, Rat.floor_def']
  simp only [Int.euclideanDiv_eq_core, Nat.euclideanDiv_eq_core, Int.natCast_ediv, den_coe, num_coe]

section Semifield

variable {K} [Semifield K] [LinearOrder K] [IsStrictOrderedRing K] [FloorSemiring K]

@[simp, norm_cast]
theorem floor_cast (x : ℚ≥0) : ⌊(x : K)⌋₊ = ⌊x⌋₊ :=
  (Nat.floor_eq_iff x.cast_nonneg).2
    (mod_cast (Nat.floor_eq_iff (zero_le : 0 ≤ x)).1 (Eq.refl ⌊x⌋₊))

@[simp, norm_cast]
theorem ceil_cast (x : ℚ≥0) : ⌈(x : K)⌉₊ = ⌈x⌉₊ := by
  obtain rfl | hx := eq_or_ne x 0
  · simp
  · refine (Nat.ceil_eq_iff ?_).2 (mod_cast (Nat.ceil_eq_iff ?_).1 (Eq.refl ⌈x⌉₊)) <;> simpa

end Semifield

section Field

variable {K} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

@[simp, norm_cast]
theorem intFloor_cast (x : ℚ≥0) : ⌊(x : K)⌋ = ⌊(x : ℚ)⌋ := by
  rw [Int.floor_eq_iff, ← coe_floor]
  norm_cast
  norm_cast
  rw [Nat.cast_add_one, ← Nat.floor_eq_iff zero_le]

@[simp, norm_cast]
theorem intCeil_cast (x : ℚ≥0) : ⌈(x : K)⌉ = ⌈(x : ℚ)⌉ := by
  rw [Int.ceil_eq_iff, ← coe_ceil, sub_lt_iff_lt_add]
  constructor
  · exact_mod_cast NNRat.cast_strictMono <| Nat.ceil_lt_add_one zero_le
  · rw [Int.cast_natCast, NNRat.cast_le_natCast]
    exact Nat.le_ceil _

end Field

@[norm_cast]
theorem floor_natCast_div_natCast (n d : ℕ) {hd : IsUnit (d : ℚ≥0)} :
    ⌊(n : ℚ≥0) / (d : ℚ≥0)⌋₊ = Nat.euclideanDiv n d (Nat.cast_ne_zero.mp hd.ne_zero) := by
  rw [← floor_coe, coe_div]
  simp only [coe_natCast]
  exact Rat.natFloor_natCast_div_natCast n d

end NNRat

namespace Mathlib.Meta.NormNum

open Qq

/-!
### `norm_num` extension for `Nat.ceil`
-/

theorem IsNat.natCeil {R : Type*} [Semiring R] [LinearOrder R] [IsStrictOrderedRing R]
    [FloorSemiring R] (r : R) (m : ℕ) : IsNat r m → IsNat (⌈r⌉₊) m := by
  rintro ⟨⟨⟩⟩
  exact ⟨by simp⟩

theorem IsInt.natCeil {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorSemiring R]
    (r : R) (m : ℕ) : IsInt r (.negOfNat m) → IsNat (⌈r⌉₊) 0 := by
  rintro ⟨⟨⟩⟩
  exact ⟨by simp⟩

theorem IsNNRat.natCeil {R : Type*} [Semifield R] [LinearOrder R] [IsStrictOrderedRing R]
    [FloorSemiring R] (r : R) (n d : ℕ) (h : IsNNRat r n d) (res : ℕ)
    (hd : d ≠ 0) (hres : ⌈NNRat.divNat n d hd⌉₊ = res) : IsNat ⌈r⌉₊ res := by
  constructor
  rw [← hres, h.to_eq rfl rfl, ← @NNRat.ceil_cast R]
  simp

theorem IsRat.natCeil {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [FloorSemiring R] (r : R) (n d : ℕ) (h : IsRat r (.negOfNat n) d) : IsNat ⌈r⌉₊ 0 := by
  have hd : d ≠ 0 := fun hd => h.den_nz (by simp [hd])
  constructor
  rw [h.eq_cast_fraction r (.negOfNat n) d hd]
  simpa using Rat.fraction_nonpos (by simp [Int.negOfNat_eq]) d hd

open Lean in
/-- `norm_num` extension for `Nat.ceil` -/
@[norm_num ⌈_⌉₊]
meta def evalNatCeil : NormNumExt where eval {u αZ} e := do
  match u, αZ, e with
  | 0, ~q(ℕ), ~q(@Nat.ceil $α $instSemiring $instPartialOrder $instFloorSemiring $x) =>
    match ← derive x with
    | .isBool .. => failure
    | .isNat sα nb pb => do
      let instLinearOrder ← synthInstanceQ q(LinearOrder $α)
      let instIsStrictOrderedRing ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      return .isNat q(inferInstance) nb q(IsNat.natCeil $x _ $pb)
    | .isNegNat sα nb pb => do
      let instLinearOrder ← synthInstanceQ q(LinearOrder $α)
      let instIsStrictOrderedRing ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      return .isNat q(inferInstance) (mkRawNatLit 0) q(IsInt.natCeil _ _ $pb)
    | .isNNRat _ q n d h => do
      let instSemifield ← synthInstanceQ q(Semifield $α)
      let instLinearOrder ← synthInstanceQ q(LinearOrder $α)
      let instIsStrictOrderedRing ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      have z : Q(ℕ) := mkRawNatLit (⌈q⌉₊)
      let hd ← mkDecideProofQ q($d ≠ 0)
      letI : $z =Q ⌈NNRat.divNat $n $d $hd⌉₊ := ⟨⟩
      return .isNat q(inferInstance) z q(IsNNRat.natCeil _ $n $d $h $z $hd rfl)
    | .isNegNNRat _ q n d h => do
      let instField ← synthInstanceQ q(Field $α)
      let instLinearOrder ← synthInstanceQ q(LinearOrder $α)
      let instIsStrictOrderedRing ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      return .isNat q(inferInstance) (mkRawNatLit 0) q(IsRat.natCeil _ _ _ $h)
  | _, _, _ => failure

end Mathlib.Meta.NormNum
