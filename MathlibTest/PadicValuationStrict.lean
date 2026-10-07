import Mathlib.NumberTheory.Padics.RingHoms

/-!
# The `p`-adic valuations on `ℚ_[p]` and `ℤ_[p]` take a nonzero argument

`Padic.valuation x hx` and `PadicInt.valuation x hx` are the valuations of a nonzero element, and
`padic_val_tac` finds the proof `hx`. The valuation of `0` is `⊤`, which the additive valuation
`Padic.addValuation`, with values in `WithTop ℤ`, records; there is no integer valuation at `0`.
-/

variable {p : ℕ} [Fact p.Prime]

/-! The lemmas that stated the value `0` at `0` are removed. -/

/-- info: Unknown constant `Padic.valuation_zero` -/
#guard_msgs in
#check_failure Padic.valuation_zero

/-- info: Unknown constant `PadicInt.valuation_zero` -/
#guard_msgs in
#check_failure PadicInt.valuation_zero

/-! The default discharger handles hypotheses, casts of nonzero elements, products, powers,
inverses, and the prime itself. -/

example (x : ℚ_[p]) (hx : x ≠ 0) : ‖x‖ = (p : ℝ) ^ (-x.valuation) :=
  Padic.norm_eq_zpow_neg_valuation hx

example (x y : ℚ_[p]) (hx : x ≠ 0) (hy : y ≠ 0) :
    (x * y).valuation = x.valuation + y.valuation :=
  Padic.valuation_mul hx hy

example (x : ℚ_[p]) (hx : x ≠ 0) (n : ℤ) : (x ^ n).valuation = n * x.valuation :=
  Padic.valuation_zpow hx n

example (x : ℚ_[p]) (hx : x ≠ 0) : x⁻¹.valuation = -x.valuation := Padic.valuation_inv hx

example (q : ℚ) (hq : q ≠ 0) : (q : ℚ_[p]).valuation = padicValRat p q :=
  Padic.valuation_ratCast hq

example : (p : ℚ_[p]).valuation = 1 := Padic.valuation_p

example (x : ℤ_[p]) (hx : x ≠ 0) : (x : ℚ_[p]).valuation = x.valuation := PadicInt.valuation_coe x

example (x : ℤ_[p]) (hx : x ≠ 0) (n : ℕ) :
    ((p : ℤ_[p]) ^ n * x).valuation = n + x.valuation :=
  PadicInt.valuation_p_pow_mul n x hx

example (n : ℕ) (hn : n ≠ 0) : (n : ℤ_[p]).valuation = padicValNat p n :=
  PadicInt.valuation_natCast hn

/-! The additive valuation is `⊤` at `0` and agrees with the valuation elsewhere. -/

example : Padic.addValuation (0 : ℚ_[p]) = ⊤ := AddValuation.map_zero _

example (x : ℚ_[p]) (hx : x ≠ 0) : Padic.addValuation x = x.valuation :=
  Padic.addValuation.apply hx

/-! Without a proof that the argument is nonzero, there is no valuation. -/

/--
error: could not synthesize default value for parameter 'hx' using tactics
---
error: the `p`-adic valuation needs `p ≠ 1` and a nonzero argument
p : ℕ
inst✝ : Fact (Nat.Prime p)
x : ℚ_[p]
⊢ x ≠ 0
-/
#guard_msgs in
noncomputable example (x : ℚ_[p]) : ℤ := x.valuation

/--
error: could not synthesize default value for parameter 'hx' using tactics
---
error: the `p`-adic valuation needs `p ≠ 1` and a nonzero argument
p : ℕ
inst✝ : Fact (Nat.Prime p)
x : ℤ_[p]
⊢ x ≠ 0
-/
#guard_msgs in
noncomputable example (x : ℤ_[p]) : ℕ := x.valuation

/--
error: could not synthesize default value for parameter 'hx' using tactics
---
error: the `p`-adic valuation needs `p ≠ 1` and a nonzero argument
p : ℕ
inst✝ : Fact (Nat.Prime p)
⊢ 0 ≠ 0
-/
#guard_msgs in
noncomputable example : ℤ := (0 : ℚ_[p]).valuation
