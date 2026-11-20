/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Basic
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Data.Rat.Floor
public meta import Mathlib.Tactic.NormNum.Basic

/-!
# Rational enclosures for interval_dyadic_real

This file defines inclusion operations for the `interval_dyadic_real` inclusion family which
define dyadic interval enclosures for rational numbers.
-/

public meta section

open Lean Qq

namespace Inclusion

namespace IntervalDyadicReal

/-- The precision of dyadic approximations, defaulting to zero. -/
@[inclusion_param]
def precParam : InclusionParamDecl where
  name := `prec
  type := q(Nat)
  defaultValue? := some q(0)

end IntervalDyadicReal

end Inclusion

end

@[expose] public section

namespace Inclusion

namespace IntervalDyadicReal

open Lean Qq

/-- Enclose a rational number in a dyadic interval with precision `prec`. -/
def rat (x : ℚ) (prec : ℕ) : Interval Dyadic :=
  let lower := x.toDyadic prec
  let upper := if lower.toRat = x then lower else lower + Dyadic.step prec
  Interval.Icc lower upper

@[inclusion_op interval_dyadic_real]
theorem ratCast_mem (q : ℚ) (prec : ℕ) : (q : ℝ) ∈ rat q prec := by
  apply Interval.mem_map_Icc Dyadic.toReal
  · exact Rat.cast_le.mpr Rat.toRat_toDyadic_le
  · split_ifs with h
    · rw [Dyadic.toReal, h]
    · rw [← Dyadic.ofIntWithPrec_one]
      exact Rat.cast_lt.mpr Rat.lt_toRat_toDyadic_add |>.le

private theorem ratCast_mem_of_isRat {q : ℚ} {n : ℤ} {d : ℕ}
    (h : Mathlib.Meta.NormNum.IsRat q n d) (hd : d ≠ 0) (prec : ℕ) :
    (q : ℝ) ∈ rat (Rat.fraction n d hd) prec := by
  have hq : q = Rat.fraction n d hd := by
    simpa only [Rat.cast_id] using h.eq_cast_fraction q n d hd
  rw [hq]
  exact ratCast_mem _ _

private meta def deriveRatCast (e : Expr) (r : Q(ℚ)) : InclusionM ExprInclusionBody := do
  unless ← Lean.Meta.isDefEq e q(($r : ℝ)) do failure
  let ⟨_, n, d, h⟩ ← Mathlib.Meta.NormNum.deriveRat r (_inst := q(inferInstance))
  let prec : Q(ℕ) ← InclusionM.getParam `prec
  let hd : Q($d ≠ 0) := q(Nat.cast_ne_zero.mp (Mathlib.Meta.NormNum.IsRat.den_nz $h))
  return ⟨q(rat (Rat.fraction $n $d $hd) $prec), q(ratCast_mem_of_isRat $h $hd $prec)⟩

/-- Enclose closed rational arithmetic using the fraction certified by `norm_num`. -/
@[inclusion_ext((_ : ℚ) : ℝ)]
meta def ratCastOfNumerals : InclusionExt where
  declName := decl_name%
  family := `interval_dyadic_real
  priority := eval_prio high
  derive e := do
    let .app _ r := e | failure
    deriveRatCast e r

/-- Efficiently enclose `m / d` in a dyadic interval with precision `prec` for a positive `d`. -/
def natDiv (m d prec : ℕ) (_hd : 0 < d) : Interval Dyadic :=
  let scaled := m <<< prec
  let quotient := scaled / d
  let lower := Dyadic.ofIntWithPrec quotient prec
  let upper := if quotient * d = scaled then lower else lower + Dyadic.step prec
  Interval.Icc lower upper

theorem natDiv_eq_rat (m : ℕ) {d : ℕ} (prec : ℕ) (hd : 0 < d) :
    natDiv m d prec hd = rat ((m : ℚ) / d) prec := by
  let q := Rat.fraction (m : ℤ) d hd.ne'
  have hq : (m : ℚ) / d = q := by
    simpa only [q, Int.cast_natCast] using (Rat.fraction_eq_div (m : ℤ) d hd.ne').symm
  -- Normalization cancels a common positive factor, so the shifted quotient is unchanged.
  obtain ⟨c, hc, hm, hden⟩ := Rat.normalize_num_den' (m : ℤ) d hd.ne'
  change (m : ℤ) = q.num * c at hm
  change d = q.den * c at hden
  have hquotient : ((m : ℤ) <<< prec) / (d : ℤ) = (q.num <<< prec) / (q.den : ℤ) := by
    rw [hm, hden, Int.natCast_mul, Int.mul_comm (q.den : ℤ),
      ← Int.ediv_ediv_of_nonneg (by simp), ← Int.shiftLeft_mul,
      Int.mul_ediv_cancel _ (by exact_mod_cast hc)]
  let k := (m <<< prec) / d
  let lower := Dyadic.ofIntWithPrec (k : ℤ) (prec : ℤ)
  have hlower : q.toDyadic (prec : ℤ) = lower := by
    change Dyadic.ofIntWithPrec ((q.num <<< prec) / (q.den : ℤ)) (prec : ℤ) = lower
    rw [← hquotient]
    simp only [lower, k, Int.natCast_ediv, Int.natCast_shiftLeft]
  have hodd (i p : ℤ) (hi : i % 2 = 1) : (Dyadic.ofOdd i p hi).toRat =
      Rat.fraction (i <<< (-p).toNat) (1 <<< p.toNat) (NeZero.ne _) := by
    cases p
    · simp [Dyadic.toRat, Rat.fraction, Rat.mk_eq_normalize, Int.shiftLeft_eq, Nat.shiftLeft_eq]
    · simp [Dyadic.toRat, Rat.fraction, Rat.normalize_eq, Int.neg_negSucc, Int.shiftLeft_eq]
  have hdyadic (i p : ℤ) : (Dyadic.ofIntWithPrec i p).toRat =
      Rat.fraction (i <<< (-p).toNat) (1 <<< p.toNat) (NeZero.ne _) := by
    simp only [Dyadic.ofIntWithPrec]
    split
    · simp_all [Rat.fraction]
    rw [hodd, Rat.fraction, Rat.fraction, Rat.normalize_eq_iff]
    simp only [Int.natCast_shiftLeft, Int.cast_ofNat_Int, Int.shiftLeft_mul_shiftLeft, Int.mul_one]
    have : (-(p - i.trailingZeros) : ℤ).toNat + p.toNat =
        i.trailingZeros + ((-p).toNat + (p - i.trailingZeros).toNat) := by omega
    rw [this, Int.shiftLeft_add, Int.shiftRight_shiftLeft_cancel]
    exact Int.two_pow_trailingZeros_dvd ‹_›
  have hexact : lower.toRat = q ↔ k * d = m <<< prec := by
    dsimp only [lower, q]
    rw [hdyadic, Int.toNat_neg_natCast, Int.toNat_natCast, Int.shiftLeft_zero,
      Rat.fraction, Rat.fraction, Rat.normalize_eq_iff]
    norm_cast
    simp only [Nat.shiftLeft_eq, Nat.one_mul]
  simp only [hq, natDiv, rat, hlower, hexact, lower, k]

theorem natDiv_mem (m : ℕ) {d : ℕ} (prec : ℕ) (hd : 0 < d) :
    (m : ℝ) / d ∈ natDiv m d prec hd := by
  rw [natDiv_eq_rat m prec hd]
  have h := ratCast_mem ((m : ℚ) / d) prec
  simpa only [Rat.cast_div, Rat.cast_natCast] using h

/-- Enclose a scientific literal in a dyadic interval with precision `prec`. -/
def scientific (m : ℕ) (s : Bool) (e prec : ℕ) : Interval Dyadic :=
  if s then
    natDiv m (10 ^ e) prec (Nat.pow_pos (by decide : 0 < 10))
  else
    Interval.singleton (m * (10 : Dyadic) ^ e)

@[inclusion_op interval_dyadic_real]
theorem scientific_mem (m : ℕ) (s : Bool) (e prec : ℕ) :
    (OfScientific.ofScientific (α := ℝ) m s e) ∈ scientific m s e prec := by
  cases s
  · simpa [scientific, NNRatCast.ofScientific_eq_ite, mem_iff_mem_map] using
      Interval.mem_map_singleton (m * (10 : Dyadic) ^ e) Dyadic.toReal
  · simpa [scientific, NNRatCast.ofScientific_eq_ite] using
      natDiv_mem m prec (Nat.pow_pos (by decide : 0 < 10))

end IntervalDyadicReal

end Inclusion
