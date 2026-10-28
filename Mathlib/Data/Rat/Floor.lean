/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Kappelmann
-/
module

public import Mathlib.Algebra.Order.Round
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public meta import Mathlib.Algebra.Order.Round
public meta import Mathlib.Algebra.GroupWithZero.Checked.Notation

/-!
# Floor Function for Rational Numbers

## Summary

We define the `FloorRing` instance on `ℚ`. Some technical lemmas relating `floor` to integer
division and modulo arithmetic are derived as well as some simple inequalities.

## Tags

rat, rationals, ℚ, floor
-/

@[expose] public section

assert_not_exists Finset

open Int

namespace Rat

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]
variable {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

instance : FloorRing ℚ :=
  (FloorRing.ofFloor ℚ Rat.floor) fun _ _ => Rat.le_floor_iff.symm

/--
This variant of `floor_def` uses the `Int.floor` (for any `FloorRing`) rather than `Rat.floor`.
-/
protected theorem floor_def' {q : ℚ} : ⌊q⌋ = q.num / q.den := Rat.floor_def q

/--
This variant of `ceil_def` uses the `Int.ceil` (for any `FloorRing`) rather than `Rat.ceil`.
-/
protected theorem ceil_def' (q : ℚ) : ⌈q⌉ = -(-q.num / ↑q.den) := by
  change -⌊-q⌋ = _
  rw [Rat.floor_def', num_neg_eq_neg_num, den_neg_eq_den]


@[norm_cast]
theorem floor_intCast_div_natCast (n : ℤ) (d : ℕ) {hd : IsUnit (d : ℚ)} :
    ⌊(↑n / ↑d : ℚ)⌋ = n / (↑d : ℤ) := by
  rw [Rat.floor_def']
  have hd₀ : 0 < d := Nat.pos_of_ne_zero (Nat.cast_ne_zero.mp hd.ne_zero)
  set q := (n : ℚ) / d with q_eq
  obtain ⟨c, n_eq_c_mul_num, d_eq_c_mul_denom⟩ : ∃ c, n = c * q.num ∧ (d : ℤ) = c * q.den := by
    rw [q_eq]
    exact mod_cast Rat.exists_eq_mul_div_num_and_eq_mul_div_den n (d := d) (hd := by simpa using hd)
  rw [n_eq_c_mul_num, d_eq_c_mul_denom]
  refine (Int.mul_ediv_mul_of_pos _ _ <| pos_of_mul_pos_left ?_ <| Int.natCast_nonneg q.den).symm
  rwa [← d_eq_c_mul_denom, Int.natCast_pos]

@[norm_cast]
theorem ceil_intCast_div_natCast (n : ℤ) (d : ℕ) {hd : IsUnit (d : ℚ)} :
    ⌈(↑n / ↑d : ℚ)⌉ = -((-n) / (↑d : ℤ)) := by
  conv_lhs => rw [← neg_neg ⌈_⌉, ← floor_neg]
  rw [← neg_div₀, ← Int.cast_neg, floor_intCast_div_natCast]

@[norm_cast]
theorem floor_natCast_div_natCast (n d : ℕ) {hd : IsUnit (d : ℚ)} :
    ⌊(↑n / ↑d : ℚ)⌋ = n / d :=
  floor_intCast_div_natCast n d

@[norm_cast]
theorem ceil_natCast_div_natCast (n d : ℕ) {hd : IsUnit (d : ℚ)} :
    ⌈(↑n / ↑d : ℚ)⌉ = -((-n) / d) :=
  ceil_intCast_div_natCast n d

@[norm_cast]
theorem natFloor_natCast_div_natCast (n d : ℕ) {hd : IsUnit (d : ℚ)} :
    ⌊(↑n / ↑d : ℚ)⌋₊ = n / d := by
  rw [← Int.ofNat_inj, Int.natCast_floor_eq_floor (by positivity)]
  push_cast
  exact floor_intCast_div_natCast n d

@[simp, norm_cast]
theorem floor_cast (x : ℚ) : ⌊(x : α)⌋ = ⌊x⌋ :=
  floor_eq_iff.2 (mod_cast floor_eq_iff.1 (Eq.refl ⌊x⌋))

@[simp, norm_cast]
theorem ceil_cast (x : ℚ) : ⌈(x : α)⌉ = ⌈x⌉ := by
  rw [← neg_inj, ← floor_neg, ← floor_neg, ← Rat.cast_neg, Rat.floor_cast]

@[simp, norm_cast]
theorem round_cast (x : ℚ) : round (x : α) = round x := by
  have : ((x + 1 / 2 : ℚ) : α) = x + 1 / 2 := by simp
  rw [round_eq, round_eq, ← this, floor_cast]

@[simp, norm_cast]
theorem cast_fract (x : ℚ) : (↑(fract x) : α) = fract (x : α) := by
  simp only [fract, cast_sub, cast_intCast, floor_cast]

@[simp]
theorem den_intFract (x : ℚ) : (fract x).den = x.den :=
  Rat.sub_intCast_den _ _

theorem num_intFract (x : ℚ) : (fract x).num = x.num - ⌊x⌋ * x.den := by
  apply Rat.intCast_injective
  rw [← mul_den_eq_num (fract x), den_intFract, fract, sub_mul, mul_den_eq_num]
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast]

section NormNum

open Mathlib.Meta.NormNum Qq

theorem _root_.Mathlib.Meta.NormNum.IsNNRat.eq_cast_fraction {K : Type*} [DivisionRing K]
    [CharZero K] (r : K) (n d : ℕ) (h : IsNNRat r n d)
    (hd : d ≠ 0) : r = (Rat.fraction n d hd : K) := by
  apply mul_left_injective₀ h.den_nz
  change r * (d : K) = (Rat.fraction n d hd : K) * (d : K)
  rw [h.to_raw_eq, NNRat.rawCast]
  calc
    (n : K) /ₚ Units.mk0 (d : K) h.den_nz * (d : K) = (n : K) :=
      divp_mul_cancel _ _
    _ = (Rat.fraction n d hd : K) * (d : K) := by
      have hc := congrArg (fun q : ℚ => (q : K)) (Rat.fraction_mul_den n d hd)
      simpa using hc.symm

theorem _root_.Mathlib.Meta.NormNum.IsRat.eq_cast_fraction {K : Type*} [DivisionRing K]
    [CharZero K] (r : K) (n : ℤ) (d : ℕ) (h : IsRat r n d)
    (hd : d ≠ 0) : r = (Rat.fraction n d hd : K) := by
  apply mul_left_injective₀ h.den_nz
  change r * (d : K) = (Rat.fraction n d hd : K) * (d : K)
  rw [h.to_raw_eq, Rat.rawCast]
  calc
    (n : K) /ₚ Units.mk0 (d : K) h.den_nz * (d : K) = (n : K) :=
      divp_mul_cancel _ _
    _ = (Rat.fraction n d hd : K) * (d : K) := by
      have hc := congrArg (fun q : ℚ => (q : K)) (Rat.fraction_mul_den n d hd)
      simpa using hc.symm

theorem isNat_intFloor {R} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    (r : R) (m : ℕ) :
    IsNat r m → IsNat ⌊r⌋ m := by rintro ⟨⟨⟩⟩; exact ⟨by simp⟩

theorem isInt_intFloor {R} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    (r : R) (m : ℤ) :
    IsInt r m → IsInt ⌊r⌋ m := by rintro ⟨⟨⟩⟩; exact ⟨by simp⟩

theorem isNat_intFloor_ofIsNNRat (r : α) (n : ℕ) (d : ℕ) :
    IsNNRat r n d → IsNat ⌊r⌋ (n / d) := by
  intro h
  have hd : d ≠ 0 := fun hd => h.den_nz (by simp [hd])
  constructor
  rw [h.eq_cast_fraction r n d hd, floor_cast, fraction_eq_div, floor_intCast_div_natCast]
  exact Int.ofNat_ediv_ofNat

theorem isInt_intFloor_ofIsRat_neg (r : α) (n : ℕ) (d : ℕ) :
    IsRat r (.negOfNat n) d → IsInt ⌊r⌋ (.negOfNat (-(-n / d) : ℤ).toNat) := by
  intro h
  have hd : d ≠ 0 := fun hd => h.den_nz (by simp [hd])
  have hq : -(n : ℤ) / (d : ℤ) ≤ 0 :=
    Int.ediv_nonpos_of_nonpos_of_neg (neg_nonpos.mpr (Int.natCast_nonneg n))
      (Int.natCast_pos.mpr (Nat.pos_of_ne_zero hd))
  constructor
  rw [h.eq_cast_fraction r (.negOfNat n) d hd, floor_cast, fraction_eq_div,
    floor_intCast_div_natCast]
  simp only [Int.cast_id, Int.negOfNat_eq, Int.ofNat_eq_natCast,
    Int.natCast_toNat_eq_self.mpr (neg_nonneg.mpr hq), neg_neg]

/-- `norm_num` extension for `Int.floor` -/
@[norm_num ⌊_⌋]
meta def evalIntFloor : NormNumExt where eval {u αZ} e := do
  match u, αZ, e with
  | 0, ~q(ℤ), ~q(@Int.floor $α $instR $instO $instF $x) =>
    match ← derive x with
    | .isBool .. => failure
    | .isNat _ _ pb => do
      let _i ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      return .isNat q(inferInstance) _ q(isNat_intFloor $x _ $pb)
    | .isNegNat _ _ pb => do
      let _i ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      -- floor always keeps naturals negative, so we can shortcut `.isInt`
      return .isNegNat q(inferInstance) _ q(isInt_intFloor _ _ $pb)
    | .isNNRat _ q n d h => do
      let _i ← synthInstanceQ q(Field $α)
      let _i ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      have z : Q(ℕ) := Lean.mkRawNatLit q.floor.toNat
      letI : $z =Q $n / $d := ⟨⟩
      return .isNat q(inferInstance) z q(isNat_intFloor_ofIsNNRat $x $n $d $h)
    | .isNegNNRat _ q n d h => do
      let _i ← synthInstanceQ q(Field $α)
      let _i ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      have z : Q(ℕ) := Lean.mkRawNatLit (-q.floor).toNat
      letI : $z =Q (-(-$n / $d) : ℤ).toNat := ⟨⟩
      return .isNegNat q(inferInstance) z q(isInt_intFloor_ofIsRat_neg $x $n $d $h)
  | _, _, _ => failure

theorem isNat_intCeil {R} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    (r : R) (m : ℕ) :
    IsNat r m → IsNat ⌈r⌉ m := by rintro ⟨⟨⟩⟩; exact ⟨by simp⟩

theorem isInt_intCeil {R} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    (r : R) (m : ℤ) :
    IsInt r m → IsInt ⌈r⌉ m := by rintro ⟨⟨⟩⟩; exact ⟨by simp⟩

theorem isNat_intCeil_ofIsNNRat (r : α) (n : ℕ) (d : ℕ) :
    IsNNRat r n d → IsNat ⌈r⌉ (-(-n / d) : ℤ).toNat := by
  intro h
  have hd : d ≠ 0 := fun hd => h.den_nz (by simp [hd])
  have hq : -(n : ℤ) / (d : ℤ) ≤ 0 :=
    Int.ediv_nonpos_of_nonpos_of_neg (neg_nonpos.mpr (Int.natCast_nonneg n))
      (Int.natCast_pos.mpr (Nat.pos_of_ne_zero hd))
  constructor
  rw [h.eq_cast_fraction r n d hd, ceil_cast, fraction_eq_div, ceil_intCast_div_natCast]
  exact (Int.natCast_toNat_eq_self.mpr (neg_nonneg.mpr hq)).symm

theorem isInt_intCeil_ofIsRat_neg (r : α) (n : ℕ) (d : ℕ) :
    IsRat r (.negOfNat n) d → IsInt ⌈r⌉ (.negOfNat (n / d)) := by
  intro h
  have hd : d ≠ 0 := fun hd => h.den_nz (by simp [hd])
  constructor
  rw [h.eq_cast_fraction r (.negOfNat n) d hd, ceil_cast, fraction_eq_div,
    ceil_intCast_div_natCast]
  norm_num [Int.negOfNat_eq]

/-- `norm_num` extension for `Int.ceil` -/
@[norm_num ⌈_⌉]
meta def evalIntCeil : NormNumExt where eval {u αZ} e := do
  match u, αZ, e with
  | 0, ~q(ℤ), ~q(@Int.ceil $α $instR $instO $instF $x) =>
    match ← derive x with
    | .isBool .. => failure
    | .isNat _ _ pb => do
      let _i ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      return .isNat q(inferInstance) _ q(isNat_intCeil $x _ $pb)
    | .isNegNat _ _ pb => do
      let _i ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      -- ceil always keeps naturals negative, so we can shortcut `.isInt`
      return .isNegNat q(inferInstance) _ q(isInt_intCeil _ _ $pb)
    | .isNNRat _ q n d h => do
      let _i ← synthInstanceQ q(Field $α)
      let _i ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      have z : Q(ℕ) := Lean.mkRawNatLit q.ceil.toNat
      letI : $z =Q (-(-$n / $d) : ℤ).toNat := ⟨⟩
      return .isNat q(inferInstance) z q(isNat_intCeil_ofIsNNRat $x $n $d $h)
    | .isNegNNRat _ q n d h => do
      let _i ← synthInstanceQ q(Field $α)
      let _i ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      have z : Q(ℕ) := Lean.mkRawNatLit (-q.ceil).toNat
      letI : $z =Q $n / $d := ⟨⟩
      return .isNegNat q(inferInstance) z q(isInt_intCeil_ofIsRat_neg $x $n $d $h)
  | _, _, _ => failure

theorem isNat_intFract_of_isNat (r : R) (m : ℕ) : IsNat r m → IsNat (Int.fract r) 0 := by
  rintro ⟨⟨⟩⟩; exact ⟨by simp⟩

theorem isNat_intFract_of_isInt (r : R) (m : ℤ) : IsInt r m → IsNat (Int.fract r) 0 := by
  rintro ⟨⟨⟩⟩; exact ⟨by simp⟩

theorem isNNRat_intFract_of_isNNRat (r : α) (n d : ℕ) :
    IsNNRat r n d → IsNNRat (Int.fract r) (n % d) d := by
  intro h
  have hd : (d : α) ≠ 0 := h.den_nz
  have hraw : IsNNRat ((n % d : ℕ) / (d : α)) (n % d) d := IsNNRat.of_raw α (n % d) d hd
  rwa [h.to_eq rfl rfl, fract_div_natCast_eq_div_natCast_mod]

theorem isRat_intFract_of_isRat_negOfNat (r : α) (n d : ℕ) :
    IsRat r (negOfNat n) d → IsRat (Int.fract r) (-n % d) d := by
  intro h
  have hd : (d : α) ≠ 0 := h.den_nz
  have hraw : IsRat (((-n % d : ℤ) : α) / (d : α)) (-n % d) d := IsRat.of_raw α (-n % d) d hd
  rw [h.to_raw_eq, show (Rat.rawCast (negOfNat n) d h.den_nz : α) =
    ((negOfNat n : ℤ) : α) / (d : α) from rfl, fract_div_intCast_eq_div_intCast_mod]
  -- `Int.negOfNat n` and `-↑n` agree definitionally.
  exact hraw

/-- `norm_num` extension for `Int.fract` -/
@[norm_num (Int.fract _)]
meta def evalIntFract : NormNumExt where eval {u α} e := do
  match e with
  | ~q(@Int.fract _ $instR $instO $instF $x) =>
    match ← derive x with
    | .isBool .. => failure
    | .isNat _ _ pb => do
      let _i ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      have z : Q(ℕ) := Lean.mkRawNatLit 0
      letI : $z =Q 0 := ⟨⟩
      return .isNat _ z q(isNat_intFract_of_isNat $x _ $pb)
    | .isNegNat _ _ pb => do
      let _i ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      have z : Q(ℕ) := Lean.mkRawNatLit 0
      letI : $z =Q 0 := ⟨⟩
      return .isNat _ z q(isNat_intFract_of_isInt _ _ $pb)
    | .isNNRat _ q n d h => do
      let _i ← synthInstanceQ q(Field $α)
      let _i ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      have n' : Q(ℕ) := Lean.mkRawNatLit (q.num.natAbs % q.den)
      letI : $n' =Q $n % $d := ⟨⟩
      return .isNNRat _ (q - Rat.floor q) n' d q(isNNRat_intFract_of_isNNRat _ $n $d $h)
    | .isNegNNRat _ q n d h => do
      let _i ← synthInstanceQ q(Field $α)
      let _i ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      have n' : Q(ℤ) := mkRawIntLit (q.num % q.den)
      letI : $n' =Q -$n % $d := ⟨⟩
      return .isRat _ (q - Rat.floor q) n' d q(isRat_intFract_of_isRat_negOfNat _ $n $d $h)
  | _, _, _ => failure

/-!
### `norm_num` extension for `round`
-/

theorem isNat_round {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    (r : R) (m : ℕ) : IsNat r m → IsNat (round r) m := by
  rintro ⟨⟨⟩⟩; exact ⟨by simp⟩

theorem isInt_round {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]
    (r : R) (m : ℤ) : IsInt r m → IsInt (round r) m := by
  rintro ⟨⟨⟩⟩; exact ⟨by simp⟩

theorem IsRat.isInt_round {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [FloorRing R] (r : R) (n : ℤ) (d : ℕ) (hd : d ≠ 0) (res : ℤ)
    (hres : round (Rat.fraction n d hd) = res) :
    IsRat r n d → IsInt (round r) res := by
  intro h
  subst res
  constructor
  rw [h.eq_cast_fraction r n d hd, round_cast]
  simp only [Int.cast_id]

/-- local copy tagged `meta` for evaluation of `round` below -/
private meta local instance : FloorRing ℚ :=
  (FloorRing.ofFloor ℚ Rat.floor) fun _ _ => Rat.le_floor_iff.symm

/-- `norm_num` extension for `round` -/
@[norm_num round _]
meta def evalRound : NormNumExt where eval {u αZ} e := do
  match u, αZ, e with
  | 0, ~q(ℤ), ~q(@round $α $instRing $instLinearOrder $instFloorRing $x) =>
    match ← derive x with
    | .isBool .. => failure
    | .isNat sα nb pb => do
      let instIsStrictOrderedRing ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      return .isNat q(inferInstance) nb q(isNat_round $x _ $pb)
    | .isNegNat sα nb pb => do
      let _instIsStrictOrderedRing ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      return .isNegNat q(inferInstance) nb q(isInt_round _ _ $pb)
    | .isNNRat _ q n d h => do
      let _instField ← synthInstanceQ q(Field $α)
      let _instIsStrictOrderedRing ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      have z : Q(ℤ) := mkRawIntLit (round q)
      let hd ← mkDecideProofQ q($d ≠ 0)
      haveI : $z =Q round (Rat.fraction (Int.ofNat $n) $d $hd) := ⟨⟩
      return .isInt q(inferInstance) z (round q)
        q(IsRat.isInt_round $x $n $d $hd $z rfl (IsNNRat.to_isRat $h))
    | .isNegNNRat _ q n d h => do
      let _instField ← synthInstanceQ q(Field $α)
      let _instIsStrictOrderedRing ← synthInstanceQ q(IsStrictOrderedRing $α)
      assertInstancesCommute
      have z : Q(ℤ) := mkRawIntLit (round q)
      let hd ← mkDecideProofQ q($d ≠ 0)
      haveI : $z =Q round (Rat.fraction (.negOfNat $n) $d $hd) := ⟨⟩
      return .isInt q(inferInstance) z (round q)
        q(IsRat.isInt_round $x (.negOfNat $n) $d $hd $z rfl $h)
  | _, _, _ => failure

end NormNum

end Rat

theorem Int.mod_nat_eq_sub_mul_floor_rat_div {n : ℤ} {d : ℕ} {hd : IsUnit (d : ℚ)} :
    n % d = n - d * ⌊(n : ℚ) / d⌋ := by
  rw [Int.emod_def, Rat.floor_intCast_div_natCast]

theorem Nat.coprime_sub_mul_floor_rat_div_of_coprime {n d : ℕ} {hd : IsUnit (d : ℚ)}
    (n_coprime_d : n.Coprime d) :
    ((n : ℤ) - d * ⌊(n : ℚ) / d⌋).natAbs.Coprime d := by
  have : (n : ℤ) % d = n - d * ⌊(n : ℚ) / d⌋ := Int.mod_nat_eq_sub_mul_floor_rat_div
  rw [← this]
  have : d.Coprime n := n_coprime_d.symm
  rwa [Nat.Coprime, Nat.gcd_rec] at this

namespace Rat

theorem num_lt_succ_floor_mul_den (q : ℚ) : q.num < (⌊q⌋ + 1) * q.den := by
  suffices (q.num : ℚ) < (⌊q⌋ + 1) * q.den from mod_cast this
  suffices (q.num : ℚ) < (q - fract q + 1) * q.den by
    have : (⌊q⌋ : ℚ) = q - fract q := eq_sub_of_add_eq <| floor_add_fract q
    rwa [this]
  suffices (q.num : ℚ) < q.num + (1 - fract q) * q.den by
    have : (q - fract q + 1) * q.den = q.num + (1 - fract q) * q.den := by
      calc
        (q - fract q + 1) * q.den = (q + (1 - fract q)) * q.den := by ring
        _ = q * q.den + (1 - fract q) * q.den := by rw [add_mul]
        _ = q.num + (1 - fract q) * q.den := by simp
    rwa [this]
  suffices 0 < (1 - fract q) * q.den by
    rw [← sub_lt_iff_lt_add']
    simpa
  have : 0 < 1 - fract q := by
    have : fract q < 1 := fract_lt_one q
    have : 0 + fract q < 1 := by simp [this]
    rwa [lt_sub_iff_add_lt]
  exact mul_pos this (by exact mod_cast q.pos)

theorem fract_inv_num_lt_num_of_pos {q : ℚ} (q_pos : 0 < q) : (fract q⁻¹).num < q.num := by
  have hnum : 0 < q.num := Rat.num_pos.mpr q_pos
  have h := num_lt_succ_floor_mul_den q⁻¹
  rw [add_mul, one_mul, ← sub_lt_iff_lt_add', ← num_intFract] at h
  simpa only [den_inv_of_ne_zero, Int.natAbs_of_nonneg hnum.le] using h

end Rat
