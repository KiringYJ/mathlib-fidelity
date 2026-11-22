/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Basic.ENNReal.Holder
public import Mathlib.Tactic.LinearCombination

/-!
# Real conjugate exponents

This file defines Hölder triple and Hölder conjugate exponents in `ℝ` and `ℝ≥0`. Real numbers `p`,
`q` and `r` form a *Hölder triple* if `0 < p`, `0 < q`, `r ≠ 0` and `p⁻¹ + q⁻¹ = r⁻¹`: the
condition `r ≠ 0` is the domain of `r⁻¹`, and the equation then implies `0 < r`. We say `p` and `q`
are *Hölder conjugate* if `p`, `q` and `1` are a Hölder triple. In this case, `1 < p` and `1 < q`.
This property shows up often in analysis, especially when dealing with `L^p` spaces.

These notions mimic the same notions for extended nonnegative reals where `p q r : ℝ≥0∞` are allowed
to take the values `0` and `∞`.

The evidence search `checked_nonzero` uses Hölder hypotheses: `h : p.HolderTriple q r` gives the
evidence for `p⁻¹`, `q⁻¹`, `r⁻¹` and for quotients by `p`, `q` and `r`, and
`h : p.HolderConjugate q` also for quotients by `p - 1` and `q - 1`, such as the conjugate exponent
`p / (p - 1)`.

## Main declarations

* `Real.HolderTriple`: Predicate for two real numbers to be a Hölder triple.
* `Real.HolderConjugate`: Predicate for two real numbers to be Hölder conjugate.
* `Real.conjExponent`: Conjugate exponent of a real number `p ≠ 1`.
* `NNReal.HolderTriple`: Predicate for two nonnegative real numbers to be a Hölder triple.
* `NNReal.HolderConjugate`: Predicate for two nonnegative real numbers to be Hölder conjugate.
* `NNReal.conjExponent`: Conjugate exponent of a nonnegative real number `1 < p`.
* `ENNReal.conjExponent`: Conjugate exponent of an extended nonnegative real number.

## TODO

* Eradicate the `1 / p` spelling in lemmas.
-/

@[expose] public section

noncomputable section

open scoped ENNReal NNReal

namespace Real

/-- Real numbers `p q r : ℝ` are said to be a **Hölder triple** if `p` and `q` are positive
and `p⁻¹ + q⁻¹ = r⁻¹`. The inverse `r⁻¹` requires `r ≠ 0`; the equation then implies `0 < r`
(`Real.HolderTriple.pos'`). -/
@[mk_iff]
structure HolderTriple (p q r : ℝ) : Prop where
  left_pos : 0 < p
  right_pos : 0 < q
  /-- For `r`, instead of `p`. This is the domain condition of `r⁻¹`. -/
  ne_zero' : r ≠ 0
  inv_add_inv_eq_inv : p⁻¹ + q⁻¹ = r⁻¹

/-- Real numbers `p q : ℝ` are **Hölder conjugate** if they are positive and satisfy the
equality `p⁻¹ + q⁻¹ = 1`. This is an abbreviation for `Real.HolderTriple p q 1`. This condition
shows up in many theorems in analysis, notably related to `L^p` norms.

It is equivalent that `1 < p`, `q ≠ 0` and `p⁻¹ + q⁻¹ = 1`. See `Real.holderConjugate_iff`. -/
abbrev HolderConjugate (p q : ℝ) := HolderTriple p q 1

/-- The conjugate exponent of `p` is `q = p / (p - 1)`, so that `p⁻¹ + q⁻¹ = 1` when `p ≠ 0`.

It is defined for `p ≠ 1`. The default proof uses the local context, for example `1 < p`,
`p < 1`, or `p.HolderConjugate q`. -/
def conjExponent (p : ℝ)
    (hp : p ≠ 1 := by first | checked_nonzero | exact sub_ne_zero.mp (by checked_nonzero)) : ℝ :=
  Checked.div p (p - 1) (sub_ne_zero.mpr hp).isUnit

variable {a b p q r : ℝ}

namespace HolderTriple

lemma of_pos (hp : 0 < p) (hq : 0 < q) : HolderTriple p q (p⁻¹ + q⁻¹)⁻¹ where
  left_pos := hp
  right_pos := hq
  ne_zero' := inv_ne_zero
  inv_add_inv_eq_inv := (inv_inv₀ _).symm

variable (h : p.HolderTriple q r)
include h

@[symm]
protected lemma symm : q.HolderTriple p r where
  left_pos := h.right_pos
  right_pos := h.left_pos
  ne_zero' := h.ne_zero'
  inv_add_inv_eq_inv := by rw [add_comm]; exact h.inv_add_inv_eq_inv

theorem pos : 0 < p := h.left_pos
theorem nonneg : 0 ≤ p := h.pos.le
theorem ne_zero : p ≠ 0 := h.pos.ne'

/-! The evidence search `checked_nonzero` uses that the exponents of a Hölder triple are nonzero:
a hypothesis `h : p.HolderTriple q r` gives the evidence for `p⁻¹`, `q⁻¹` and `r⁻¹`. -/

macro_rules | `(tactic| checked_nonzero) => `(tactic|
    solve
    | assumption
    | (apply Real.HolderTriple.ne_zero; assumption)
    | (apply Real.HolderTriple.ne_zero; apply Real.HolderTriple.symm; assumption)
    | (apply Real.HolderTriple.ne_zero'; assumption))

protected lemma inv_pos : 0 < p⁻¹ := inv_pos_of_pos h.pos
protected lemma inv_nonneg : 0 ≤ p⁻¹ := h.inv_pos.le
protected lemma inv_ne_zero : p⁻¹ ≠ 0 := h.inv_pos.ne'
theorem one_div_pos : 0 < 1 / p := _root_.one_div_pos.2 h.pos
theorem one_div_nonneg : 0 ≤ 1 / p := le_of_lt h.one_div_pos
theorem one_div_ne_zero : 1 / p ≠ 0 := ne_of_gt h.one_div_pos

/-- For `r`, instead of `p` -/
theorem pos' : 0 < r := by
  have := add_pos h.inv_pos h.symm.inv_pos
  rw [h.inv_add_inv_eq_inv] at this
  exact inv_pos.mp this
/-- For `r`, instead of `p` -/
theorem nonneg' : 0 ≤ r := h.pos'.le
/-- For `r`, instead of `p` -/
protected lemma inv_pos' : 0 < r⁻¹ := inv_pos_of_pos h.pos'
/-- For `r`, instead of `p` -/
protected lemma inv_nonneg' : 0 ≤ r⁻¹ := h.inv_pos'.le
/-- For `r`, instead of `p` -/
protected lemma inv_ne_zero' : r⁻¹ ≠ 0 := h.inv_pos'.ne'
/-- For `r`, instead of `p` -/
theorem one_div_pos' : 0 < 1 / r := _root_.one_div_pos.2 h.pos'
/-- For `r`, instead of `p` -/
theorem one_div_nonneg' : 0 ≤ 1 / r := le_of_lt h.one_div_pos'
/-- For `r`, instead of `p` -/
theorem one_div_ne_zero' : 1 / r ≠ 0 := ne_of_gt h.one_div_pos'

/-- useful for introducing all three facts simultaneously within a proof. -/
@[grind →]
theorem all_pos : 0 < p ∧ 0 < q ∧ 0 < r := ⟨h.pos, h.symm.pos, h.pos'⟩

lemma inv_eq : r⁻¹ = p⁻¹ + q⁻¹ := h.inv_add_inv_eq_inv.symm
lemma one_div_add_one_div : 1 / p + 1 / q = 1 / r := by
  simpa only [one_div₀] using h.inv_add_inv_eq_inv
lemma one_div_eq : 1 / r = 1 / p + 1 / q := h.one_div_add_one_div.symm
lemma inv_inv_add_inv :
    Checked.inv (p⁻¹ + q⁻¹) (add_pos h.inv_pos h.symm.inv_pos).ne'.isUnit = r := by
  simp only [h.inv_add_inv_eq_inv, inv_inv₀]

protected lemma inv_lt_inv : p⁻¹ < r⁻¹ :=
  (lt_add_of_pos_right _ h.symm.inv_pos).trans_eq h.inv_add_inv_eq_inv
lemma lt : r < p := (inv_lt_inv₀ h.pos h.pos').1 h.inv_lt_inv
lemma inv_sub_inv_eq_inv : r⁻¹ - q⁻¹ = p⁻¹ := sub_eq_of_eq_add h.inv_eq

lemma holderConjugate_div_div : (p / r).HolderConjugate (q / r) where
  left_pos := div_pos h.pos h.pos'
  right_pos := div_pos h.symm.pos h.pos'
  ne_zero' := one_ne_zero
  inv_add_inv_eq_inv := by
    rw [inv_div₀, inv_div₀, div_eq_mul_inv₀ r p, div_eq_mul_inv₀ r q, ← mul_add,
      h.inv_add_inv_eq_inv, mul_inv_cancel₀, inv_one₀]

end HolderTriple

namespace HolderConjugate

lemma two_two : HolderConjugate 2 2 where
  left_pos := zero_lt_two
  right_pos := zero_lt_two
  ne_zero' := one_ne_zero
  inv_add_inv_eq_inv := by norm_num

section
variable (h : p.HolderConjugate q)
include h

@[symm]
protected lemma symm : q.HolderConjugate p := HolderTriple.symm h

theorem inv_add_inv_eq_one : p⁻¹ + q⁻¹ = 1 := h.inv_add_inv_eq_inv.trans inv_one₀

theorem sub_one_pos : 0 < p - 1 := sub_pos.2 h.lt
theorem sub_one_ne_zero : p - 1 ≠ 0 := h.sub_one_pos.ne'

/-! The evidence search `checked_nonzero` uses that `p - 1` and `q - 1` are nonzero for Hölder
conjugate exponents `p` and `q`. -/

macro_rules | `(tactic| checked_nonzero) => `(tactic|
    solve
    | assumption
    | (apply Real.HolderConjugate.sub_one_ne_zero; assumption)
    | (apply Real.HolderConjugate.sub_one_ne_zero; apply Real.HolderConjugate.symm; assumption))

theorem conjugate_eq : q = p / (p - 1) := by
  rw [eq_div_iff]
  have hpq := h.inv_add_inv_eq_one
  field_simp at hpq
  linear_combination -hpq

lemma conjExponent_eq : conjExponent p = q := h.conjugate_eq.symm

lemma one_sub_inv : 1 - p⁻¹ = q⁻¹ := sub_eq_of_eq_add h.symm.inv_add_inv_eq_one.symm
lemma inv_sub_one : p⁻¹ - 1 = -q⁻¹ := by simpa using congr(-$(h.one_sub_inv))

theorem sub_one_mul_conj : (p - 1) * q = p := by
  rw [mul_comm]
  exact eq_div_iff.1 h.conjugate_eq

theorem mul_eq_add : p * q = p + q := by
  simpa only [sub_mul, sub_eq_iff_eq_add, one_mul] using h.sub_one_mul_conj

theorem div_conj_eq_sub_one : p / q = p - 1 := by
  field_simp
  linear_combination -h.sub_one_mul_conj

theorem inv_add_inv_ennreal : (ENNReal.ofReal p)⁻¹ + (ENNReal.ofReal q)⁻¹ = 1 := by
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_inv_of_pos h.pos,
    ← ENNReal.ofReal_inv_of_pos h.symm.pos, ← ENNReal.ofReal_add h.inv_nonneg h.symm.inv_nonneg,
    h.inv_add_inv_eq_one]

end

/-- The inverse `q⁻¹` requires `q ≠ 0`; then `1 < p` and `p⁻¹ + q⁻¹ = 1` imply `0 < q`. -/
lemma _root_.Real.holderConjugate_iff :
    p.HolderConjugate q ↔ ∃ (hp : 1 < p) (hq : q ≠ 0), p⁻¹ + q⁻¹ = 1 := by
  refine ⟨fun h ↦ ⟨h.lt, h.symm.ne_zero, h.inv_add_inv_eq_one⟩, ?_⟩
  rintro ⟨hp, hq, h⟩
  have hp' := zero_lt_one.trans hp
  have hq' : 0 < q⁻¹ := by
    rw [eq_sub_of_add_eq' h, sub_pos]
    exact (inv_lt_one₀ hp').2 hp
  exact ⟨hp', inv_pos.mp hq', one_ne_zero, h.trans inv_one₀.symm⟩

protected lemma inv_inv (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) : a⁻¹.HolderConjugate b⁻¹ where
  left_pos := inv_pos_of_pos ha
  right_pos := inv_pos_of_pos hb
  ne_zero' := one_ne_zero
  inv_add_inv_eq_inv := by simpa using hab

lemma inv_one_sub_inv (ha₀ : 0 < a) (ha₁ : a < 1) : a⁻¹.HolderConjugate (1 - a)⁻¹ :=
  .inv_inv ha₀ (sub_pos.2 ha₁) (add_sub_cancel a 1)

lemma one_sub_inv_inv (ha₀ : 0 < a) (ha₁ : a < 1) : (1 - a)⁻¹.HolderConjugate a⁻¹ :=
  (inv_one_sub_inv ha₀ ha₁).symm

end HolderConjugate

lemma holderConjugate_comm : p.HolderConjugate q ↔ q.HolderConjugate p := ⟨.symm, .symm⟩

lemma holderConjugate_iff_eq_conjExponent (hp : 1 < p) : p.HolderConjugate q ↔ q = p / (p - 1) := by
  refine ⟨HolderConjugate.conjugate_eq, fun h ↦ ?_⟩
  subst h
  refine holderConjugate_iff.2 ⟨hp, (div_pos (zero_lt_one.trans hp) (sub_pos.2 hp)).ne', ?_⟩
  rw [inv_div₀, div_eq_mul_inv₀, ← one_add_mul, add_sub_cancel, mul_inv_cancel₀]

lemma HolderConjugate.conjExponent (h : 1 < p) : p.HolderConjugate (conjExponent p) :=
  (holderConjugate_iff_eq_conjExponent h).2 rfl

lemma holderConjugate_one_div (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    (1 / a).HolderConjugate (1 / b) := by simpa using HolderConjugate.inv_inv ha hb hab

end Real

namespace NNReal

/-- Nonnegative real numbers `p q r : ℝ≥0` are said to be a **Hölder triple** if `p` and `q` are
positive and `p⁻¹ + q⁻¹ = r⁻¹`. The inverse `r⁻¹` requires `r ≠ 0`. -/
@[mk_iff]
structure HolderTriple (p q r : ℝ≥0) : Prop where
  left_pos : 0 < p
  right_pos : 0 < q
  /-- For `r`, instead of `p`. This is the domain condition of `r⁻¹`. -/
  ne_zero' : r ≠ 0
  inv_add_inv_eq_inv : p⁻¹ + q⁻¹ = r⁻¹

/-- Nonnegative real numbers `p q : ℝ≥0` are **Hölder conjugate** if they are positive and satisfy
the equality `p⁻¹ + q⁻¹ = 1`. This is an abbreviation for `NNReal.HolderTriple p q 1`. This
condition shows up in many theorems in analysis, notably related to `L^p` norms.

It is equivalent that `1 < p`, `q ≠ 0` and `p⁻¹ + q⁻¹ = 1`. See `NNReal.holderConjugate_iff`. -/
abbrev HolderConjugate (p q : ℝ≥0) := HolderTriple p q 1

/-- The conjugate exponent of `p` is `q = p/(p-1)`, so that `p⁻¹ + q⁻¹ = 1`.

It is defined for `1 < p`. The default proof uses the local context, for example
`p.HolderConjugate q`. -/
def conjExponent (p : ℝ≥0)
    (hp : 1 < p := by
      solve
      | assumption
      | exact Fact.out
      | exact tsub_pos_iff_lt.mp (pos_iff_ne_zero.mpr (by checked_nonzero))
      | norm_num) : ℝ≥0 :=
  Checked.div p (p - 1) (tsub_pos_of_lt hp).ne'.isUnit

@[simp, norm_cast]
lemma holderTriple_coe_iff {p q r : ℝ≥0} :
    Real.HolderTriple (p : ℝ) (q : ℝ) (r : ℝ) ↔ HolderTriple p q r := by
  refine ⟨fun h ↦ ⟨mod_cast h.pos, mod_cast h.symm.pos, mod_cast h.ne_zero', ?_⟩,
    fun h ↦ ⟨mod_cast h.left_pos, mod_cast h.right_pos, mod_cast h.ne_zero', ?_⟩⟩
  · exact NNReal.coe_injective (by push_cast; exact h.inv_add_inv_eq_inv)
  · have := congrArg ((↑) : ℝ≥0 → ℝ) h.inv_add_inv_eq_inv
    push_cast at this
    exact this

alias ⟨_, HolderTriple.coe⟩ := holderTriple_coe_iff

@[simp, norm_cast]
lemma holderConjugate_coe_iff {p q : ℝ≥0} :
    Real.HolderConjugate (p : ℝ) (q : ℝ) ↔ HolderConjugate p q :=
  holderTriple_coe_iff (r := 1)

alias ⟨_, HolderConjugate.coe⟩ := holderConjugate_coe_iff

variable {a b p q r : ℝ≥0}

namespace HolderTriple

lemma of_pos (hp : 0 < p) (hq : 0 < q) : HolderTriple p q (p⁻¹ + q⁻¹)⁻¹ where
  left_pos := hp
  right_pos := hq
  ne_zero' := inv_ne_zero
  inv_add_inv_eq_inv := (inv_inv₀ _).symm

variable (h : p.HolderTriple q r)
include h

@[symm]
protected lemma symm : q.HolderTriple p r where
  left_pos := h.right_pos
  right_pos := h.left_pos
  ne_zero' := h.ne_zero'
  inv_add_inv_eq_inv := by rw [add_comm]; exact h.inv_add_inv_eq_inv

theorem pos : 0 < p := h.left_pos
theorem nonneg : 0 ≤ p := h.pos.le
theorem ne_zero : p ≠ 0 := h.pos.ne'

/-! The evidence search `checked_nonzero` uses that the exponents of a Hölder triple in `ℝ≥0` are
nonzero: a hypothesis `h : p.HolderTriple q r` gives the evidence for `p⁻¹`, `q⁻¹` and `r⁻¹`. -/

macro_rules | `(tactic| checked_nonzero) => `(tactic|
    solve
    | assumption
    | (apply NNReal.HolderTriple.ne_zero; assumption)
    | (apply NNReal.HolderTriple.ne_zero; apply NNReal.HolderTriple.symm; assumption)
    | (apply NNReal.HolderTriple.ne_zero'; assumption))

protected lemma inv_pos : 0 < p⁻¹ := inv_pos_of_pos h.pos
protected lemma inv_nonneg : 0 ≤ p⁻¹ := h.inv_pos.le
protected lemma inv_ne_zero : p⁻¹ ≠ 0 := h.inv_pos.ne'
theorem one_div_pos : 0 < 1 / p := _root_.one_div_pos.2 h.pos
theorem one_div_nonneg : 0 ≤ 1 / p := le_of_lt h.one_div_pos
theorem one_div_ne_zero : 1 / p ≠ 0 := ne_of_gt h.one_div_pos

/-- For `r`, instead of `p` -/
theorem pos' : 0 < r := by
  have := add_pos h.inv_pos h.symm.inv_pos
  rw [h.inv_add_inv_eq_inv] at this
  exact inv_pos.mp this
/-- For `r`, instead of `p` -/
theorem nonneg' : 0 ≤ r := h.pos'.le
/-- For `r`, instead of `p` -/
protected lemma inv_pos' : 0 < r⁻¹ := inv_pos_of_pos h.pos'
/-- For `r`, instead of `p` -/
protected lemma inv_nonneg' : 0 ≤ r⁻¹ := h.inv_pos'.le
/-- For `r`, instead of `p` -/
protected lemma inv_ne_zero' : r⁻¹ ≠ 0 := h.inv_pos'.ne'
/-- For `r`, instead of `p` -/
theorem one_div_pos' : 0 < 1 / r := _root_.one_div_pos.2 h.pos'
/-- For `r`, instead of `p` -/
theorem one_div_nonneg' : 0 ≤ 1 / r := le_of_lt h.one_div_pos'
/-- For `r`, instead of `p` -/
theorem one_div_ne_zero' : 1 / r ≠ 0 := ne_of_gt h.one_div_pos'

/-- useful for introducing all three facts simultaneously within a proof. -/
@[grind →]
theorem all_pos : 0 < p ∧ 0 < q ∧ 0 < r := ⟨h.pos, h.symm.pos, h.pos'⟩

lemma inv_eq : r⁻¹ = p⁻¹ + q⁻¹ := h.inv_add_inv_eq_inv.symm
lemma one_div_add_one_div : 1 / p + 1 / q = 1 / r := by
  simpa only [one_div₀] using h.inv_add_inv_eq_inv
lemma one_div_eq : 1 / r = 1 / p + 1 / q := h.one_div_add_one_div.symm
lemma inv_inv_add_inv :
    Checked.inv (p⁻¹ + q⁻¹) (add_pos h.inv_pos h.symm.inv_pos).ne'.isUnit = r := by
  simp only [h.inv_add_inv_eq_inv, inv_inv₀]

protected lemma inv_lt_inv : p⁻¹ < r⁻¹ :=
  (lt_add_of_pos_right _ h.symm.inv_pos).trans_eq h.inv_add_inv_eq_inv
lemma lt : r < p := (inv_lt_inv₀ h.pos h.pos').1 h.inv_lt_inv
lemma inv_sub_inv_eq_inv : r⁻¹ - q⁻¹ = p⁻¹ := tsub_eq_of_eq_add h.inv_eq

lemma holderConjugate_div_div : (p / r).HolderConjugate (q / r) where
  left_pos := div_pos h.pos h.pos'
  right_pos := div_pos h.symm.pos h.pos'
  ne_zero' := one_ne_zero
  inv_add_inv_eq_inv := by
    rw [inv_div₀, inv_div₀, div_eq_mul_inv₀ r p, div_eq_mul_inv₀ r q, ← mul_add,
      h.inv_add_inv_eq_inv, mul_inv_cancel₀, inv_one₀]

end HolderTriple

namespace HolderConjugate

lemma two_two : HolderConjugate 2 2 where
  left_pos := zero_lt_two
  right_pos := zero_lt_two
  ne_zero' := one_ne_zero
  inv_add_inv_eq_inv := by simpa using add_halves (1 : ℝ≥0)

section
variable (h : p.HolderConjugate q)
include h

@[symm]
protected lemma symm : q.HolderConjugate p := HolderTriple.symm h

theorem inv_add_inv_eq_one : p⁻¹ + q⁻¹ = 1 := h.inv_add_inv_eq_inv.trans inv_one₀

theorem sub_one_pos : 0 < p - 1 := tsub_pos_of_lt h.lt
theorem sub_one_ne_zero : p - 1 ≠ 0 := h.sub_one_pos.ne'

/-! The evidence search `checked_nonzero` uses that `p - 1` and `q - 1` are nonzero for Hölder
conjugate exponents `p` and `q` in `ℝ≥0`. -/

macro_rules | `(tactic| checked_nonzero) => `(tactic|
    solve
    | assumption
    | (apply NNReal.HolderConjugate.sub_one_ne_zero; assumption)
    | (apply NNReal.HolderConjugate.sub_one_ne_zero; apply NNReal.HolderConjugate.symm;
        assumption))

theorem conjugate_eq : q = p / (p - 1) :=
  NNReal.coe_injective (by push_cast [NNReal.coe_sub h.lt.le]; exact h.coe.conjugate_eq)

lemma conjExponent_eq : conjExponent p = q := h.conjugate_eq.symm

lemma one_sub_inv : 1 - p⁻¹ = q⁻¹ := tsub_eq_of_eq_add h.symm.inv_add_inv_eq_one.symm

theorem sub_one_mul_conj : (p - 1) * q = p := by
  rw [mul_comm]
  exact eq_div_iff.1 h.conjugate_eq

theorem mul_eq_add : p * q = p + q :=
  NNReal.coe_injective (by push_cast; exact h.coe.mul_eq_add)

theorem div_conj_eq_sub_one : p / q = p - 1 :=
  NNReal.coe_injective (by push_cast [NNReal.coe_sub h.lt.le]; exact h.coe.div_conj_eq_sub_one)

lemma inv_add_inv_ennreal : (p⁻¹ + q⁻¹ : ℝ≥0∞) = 1 := by norm_cast; exact h.inv_add_inv_eq_one

end

/-- The inverse `q⁻¹` requires `q ≠ 0`. -/
lemma _root_.NNReal.holderConjugate_iff :
    p.HolderConjugate q ↔ ∃ (hp : 1 < p) (hq : q ≠ 0), p⁻¹ + q⁻¹ = 1 := by
  refine ⟨fun h ↦ ⟨h.lt, h.symm.ne_zero, h.inv_add_inv_eq_one⟩, ?_⟩
  rintro ⟨hp, hq, h⟩
  exact ⟨zero_lt_one.trans hp, pos_iff_ne_zero.2 hq, one_ne_zero, h.trans inv_one₀.symm⟩

protected lemma inv_inv (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) : a⁻¹.HolderConjugate b⁻¹ where
  left_pos := inv_pos_of_pos ha
  right_pos := inv_pos_of_pos hb
  ne_zero' := one_ne_zero
  inv_add_inv_eq_inv := by simpa using hab

lemma inv_one_sub_inv (ha₀ : 0 < a) (ha₁ : a < 1) :
    a⁻¹.HolderConjugate (Checked.inv (1 - a) (tsub_pos_of_lt ha₁).ne'.isUnit) :=
  .inv_inv ha₀ (tsub_pos_of_lt ha₁) (add_tsub_cancel_of_le ha₁.le)

lemma one_sub_inv_inv (ha₀ : 0 < a) (ha₁ : a < 1) :
    (Checked.inv (1 - a) (tsub_pos_of_lt ha₁).ne'.isUnit).HolderConjugate a⁻¹ :=
  (inv_one_sub_inv ha₀ ha₁).symm

end HolderConjugate

lemma holderConjugate_comm : p.HolderConjugate q ↔ q.HolderConjugate p := ⟨.symm, .symm⟩

lemma holderConjugate_iff_eq_conjExponent (hp : 1 < p) :
    p.HolderConjugate q ↔ q = Checked.div p (p - 1) (tsub_pos_of_lt hp).ne'.isUnit := by
  refine ⟨HolderConjugate.conjugate_eq, fun h ↦ ?_⟩
  subst h
  refine holderConjugate_iff.2
    ⟨hp, (div_pos (zero_lt_one.trans hp) (tsub_pos_of_lt hp)).ne', ?_⟩
  rw [inv_div₀, div_eq_mul_inv₀, ← one_add_mul, add_tsub_cancel_of_le hp.le, mul_inv_cancel₀]

lemma HolderConjugate.conjExponent (h : 1 < p) :
    p.HolderConjugate (conjExponent p h) :=
  (holderConjugate_iff_eq_conjExponent h).2 rfl

lemma holderConjugate_one_div (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    (1 / a).HolderConjugate (1 / b) := by simpa using HolderConjugate.inv_inv ha hb hab

end NNReal

protected lemma Real.HolderTriple.toNNReal {p q r : ℝ} (h : p.HolderTriple q r) :
    p.toNNReal.HolderTriple q.toNNReal r.toNNReal := by
  simpa [← NNReal.holderTriple_coe_iff, h.nonneg, h.symm.nonneg, h.nonneg']

protected lemma Real.HolderConjugate.toNNReal {p q : ℝ} (h : p.HolderConjugate q) :
    p.toNNReal.HolderConjugate q.toNNReal := by
  simpa using Real.HolderTriple.toNNReal h

namespace ENNReal

/-- The conjugate exponent of `p` is `q = 1 + (p - 1)⁻¹`, so that `p⁻¹ + q⁻¹ = 1`. -/
noncomputable def conjExponent (p : ℝ≥0∞) : ℝ≥0∞ := 1 + (p - 1)⁻¹

lemma coe_conjExponent {p : ℝ≥0} (hp : 1 < p) :
    p.conjExponent hp = conjExponent p := by
  have hp' : p - 1 ≠ 0 := (tsub_pos_of_lt hp).ne'
  have h : p / (p - 1) = 1 + (p - 1)⁻¹ := by
    rw [div_eq_iff, add_mul, one_mul, inv_mul_cancel₀, tsub_add_cancel_of_le hp.le]
  rw [NNReal.conjExponent, conjExponent, h, coe_add, coe_one, coe_inv, coe_sub, coe_one]


variable {a b p q r : ℝ≥0∞}

@[simp, norm_cast]
lemma holderTriple_coe_iff {p q r : ℝ≥0} (hr : r ≠ 0) :
    HolderTriple (p : ℝ≥0∞) (q : ℝ≥0∞) (r : ℝ≥0∞) ↔ NNReal.HolderTriple p q r := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨hp, hq⟩ : p ≠ 0 ∧ q ≠ 0 := by
      constructor
      all_goals
        rintro rfl
        apply hr
        exact_mod_cast (coe_zero ▸ h).unique _ _ r 0
    refine ⟨hp.bot_lt, hq.bot_lt, hr, ?_⟩
    have := h.inv_add_inv_eq_inv
    rw [← coe_inv (hr := hp.isUnit), ← coe_inv (hr := hq.isUnit), ← coe_inv (hr := hr.isUnit),
      ← coe_add, coe_inj] at this
    exact this
  · rw [holderTriple_iff, ← coe_inv (hr := h.ne_zero.isUnit),
      ← coe_inv (hr := h.symm.ne_zero.isUnit), ← coe_inv (hr := h.ne_zero'.isUnit), ← coe_add,
      h.inv_add_inv_eq_inv]

alias ⟨_, _root_.NNReal.HolderTriple.coe_ennreal⟩ := holderTriple_coe_iff

@[simp, norm_cast]
lemma holderConjugate_coe_iff {p q : ℝ≥0} :
    HolderConjugate (p : ℝ≥0∞) (q : ℝ≥0∞) ↔ NNReal.HolderConjugate p q :=
  holderTriple_coe_iff one_ne_zero

alias ⟨_, _root_.NNReal.HolderConjugate.coe_ennreal⟩ := holderConjugate_coe_iff

namespace HolderTriple

lemma _root_.Real.HolderTriple.ennrealOfReal {p q r : ℝ} (h : p.HolderTriple q r) :
    HolderTriple (ENNReal.ofReal p) (ENNReal.ofReal q) (ENNReal.ofReal r) := by
  rw [holderTriple_iff, ← ofReal_inv_of_pos h.pos, ← ofReal_inv_of_pos h.symm.pos,
    ← ofReal_inv_of_pos h.pos', ← ofReal_add h.inv_nonneg h.symm.inv_nonneg,
    h.inv_add_inv_eq_inv]

lemma _root_.Real.HolderConjugate.ennrealOfReal {p q : ℝ} (h : p.HolderConjugate q) :
    HolderConjugate (ENNReal.ofReal p) (ENNReal.ofReal q) := by
  simpa using Real.HolderTriple.ennrealOfReal h

lemma of_toReal (h : Real.HolderTriple p.toReal q.toReal r.toReal) : HolderTriple p q r := by
  have hp := h.pos
  have hq := h.symm.pos
  have hr := h.pos'
  rw [toReal_pos_iff] at hp hq hr
  simpa [hp.2.ne, hq.2.ne, hr.2.ne] using h.ennrealOfReal

variable (r) in
lemma toReal_iff (hp : 0 < p.toReal) (hq : 0 < q.toReal) :
    Real.HolderTriple p.toReal q.toReal r.toReal ↔ HolderTriple p q r := by
  refine ⟨of_toReal, fun h ↦ ?_⟩
  have hp' := toReal_pos_iff.1 hp
  have hq' := toReal_pos_iff.1 hq
  have hpq : p⁻¹ + q⁻¹ ≠ ∞ :=
    add_ne_top.2 ⟨inv_ne_top.2 hp'.1.ne', inv_ne_top.2 hq'.1.ne'⟩
  have hr₀ : r ≠ 0 := by
    rintro rfl
    exact hpq (h.inv_add_inv_eq_inv.trans inv_zero)
  have hr : r ≠ ∞ := by
    rintro rfl
    have := h.inv_add_inv_eq_inv.trans inv_top
    exact (ENNReal.inv_pos.2 hp'.2.ne).ne' (add_eq_zero.1 this).1
  have hr' : r.toReal ≠ 0 := toReal_ne_zero.2 ⟨hr₀, hr⟩
  refine ⟨hp, hq, hr', ?_⟩
  have := congrArg ENNReal.toReal h.inv_add_inv_eq_inv
  rwa [toReal_add (inv_ne_top.2 hp'.1.ne') (inv_ne_top.2 hq'.1.ne'),
    toReal_inv p (ha := hp.ne'.isUnit), toReal_inv q (ha := hq.ne'.isUnit),
    toReal_inv r (ha := hr'.isUnit)] at this

variable (r) in
lemma toReal (hp : 0 < p.toReal) (hq : 0 < q.toReal) [HolderTriple p q r] :
    Real.HolderTriple p.toReal q.toReal r.toReal :=
  toReal_iff r hp hq |>.mpr ‹_›

lemma of_toNNReal (h : NNReal.HolderTriple p.toNNReal q.toNNReal r.toNNReal) :
    HolderTriple p q r :=
  .of_toReal <| by simpa only [coe_toNNReal_eq_toReal] using h.coe

variable (r) in
lemma toNNReal_iff (hp : 0 < p.toNNReal) (hq : 0 < q.toNNReal) :
    NNReal.HolderTriple p.toNNReal q.toNNReal r.toNNReal ↔ HolderTriple p q r := by
  simp_rw [← NNReal.holderTriple_coe_iff, coe_toNNReal_eq_toReal]
  apply toReal_iff r ?_ ?_
  all_goals simpa [← coe_toNNReal_eq_toReal]

variable (r) in
lemma toNNReal (hp : 0 < p.toNNReal) (hq : 0 < q.toNNReal) [HolderTriple p q r] :
    NNReal.HolderTriple p.toNNReal q.toNNReal r.toNNReal :=
  toNNReal_iff r hp hq |>.mpr ‹_›

end HolderTriple

namespace HolderConjugate

lemma of_toReal (h : p.toReal.HolderConjugate q.toReal) : p.HolderConjugate q := by
  rw [Real.HolderConjugate] at h
  exact HolderTriple.of_toReal (toReal_one ▸ h)

lemma toReal_iff (hp : 1 < p.toReal) :
    p.toReal.HolderConjugate q.toReal ↔ p.HolderConjugate q := by
  refine ⟨of_toReal, fun h ↦ ?_⟩
  have hq : 0 < q.toReal := by
    rw [toReal_pos_iff]
    refine ⟨pos q p, lt_top_iff_one_lt q p |>.mpr ?_⟩
    contrapose! hp
    exact toReal_mono one_ne_top hp
  simpa using HolderTriple.toReal 1 (zero_lt_one.trans hp) hq

lemma toReal (hp : 1 < p.toReal) [HolderConjugate p q] :
    p.toReal.HolderConjugate q.toReal :=
  toReal_iff hp |>.mpr ‹_›

lemma toReal_of_ne_top (hp : p ≠ ∞) (hq : q ≠ ∞) [HolderConjugate p q] :
    p.toReal.HolderConjugate q.toReal :=
  toReal ((toReal_lt_toReal one_ne_top hp).mpr ((lt_top_iff_one_lt q p).mp hq.lt_top))

lemma of_toNNReal (h : NNReal.HolderConjugate p.toNNReal q.toNNReal) :
    HolderConjugate p q :=
  .of_toReal <| by simpa only [coe_toNNReal_eq_toReal] using h.coe

lemma toNNReal_iff (hp : 1 < p.toNNReal) :
    NNReal.HolderConjugate p.toNNReal q.toNNReal ↔ HolderConjugate p q := by
  simp_rw [← NNReal.holderTriple_coe_iff, coe_toNNReal_eq_toReal]
  apply toReal_iff ?_
  all_goals simpa [← coe_toNNReal_eq_toReal]

lemma toNNReal (hp : 1 < p.toNNReal) [HolderConjugate p q] :
    NNReal.HolderConjugate p.toNNReal q.toNNReal :=
  toNNReal_iff hp |>.mpr ‹_›

protected lemma conjExponent {p : ℝ≥0∞} (hp : 1 ≤ p) : p.HolderConjugate (conjExponent p) := by
  have : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  rw [HolderConjugate, holderTriple_iff, conjExponent, add_comm]
  refine (AddLECancellable.eq_tsub_iff_add_eq_of_le (α := ℝ≥0∞) (by simpa) (by simpa)).1 ?_
  rw [inv_eq_iff_eq_inv]
  obtain rfl | hp₁ := hp.eq_or_lt
  · simp
  obtain rfl | hp := eq_or_ne p ∞
  · simp
  calc
    1 + (p - 1)⁻¹ = ((p - 1 + 1) / (p - 1)) := by
      rw [ENNReal.add_div, ENNReal.div_self ((tsub_pos_of_lt hp₁).ne') (sub_ne_top hp),
        ENNReal.one_div]
    _ = (1⁻¹ - p⁻¹)⁻¹ := by
      rw [tsub_add_cancel_of_le, ← inv_eq_iff_eq_inv, ENNReal.div_eq_mul_inv,
        ENNReal.mul_inv, inv_inv, ENNReal.mul_sub, ENNReal.inv_mul_cancel, mul_one] <;> simp [*]

instance {p : ℝ≥0∞} [Fact (1 ≤ p)] : p.HolderConjugate (conjExponent p) := .conjExponent Fact.out

section

variable [h : HolderConjugate p q]

lemma conjExponent_eq : conjExponent p = q :=
  have : Fact (1 ≤ p) := ⟨one_le p q⟩
  unique p (conjExponent p) q

lemma conj_eq : q = 1 + (p - 1)⁻¹ := conjExponent_eq.symm

lemma mul_eq_add : p * q = p + q := by
  obtain rfl | hp := eq_or_ne p ∞
  · simp [ne_zero q ∞]
  obtain rfl | hq := eq_or_ne q ∞
  · simp [ne_zero p ∞]
  simpa [add_comm p, mul_add, add_mul, hp, hq, ne_zero p q, ne_zero q p, ENNReal.mul_inv_cancel,
    ENNReal.inv_mul_cancel_right] using congr(p * $((inv_add_inv_eq_one p q).symm) * q)

lemma div_conj_eq_sub_one : (p / q) = p - 1 := by
  obtain rfl | hq := eq_or_ne q ∞
  · obtain rfl := unique ∞ p 1
    simp
  refine ENNReal.eq_sub_of_add_eq one_ne_top ?_
  rw [← ENNReal.div_self (ne_zero q p) hq, ← ENNReal.add_div, ← h.mul_eq_add, ENNReal.mul_div_assoc,
    ENNReal.div_self (ne_zero q p) hq, mul_one]

end

protected lemma inv_inv (hab : a + b = 1) : a⁻¹.HolderConjugate b⁻¹ where
  inv_add_inv_eq_inv := by simpa [inv_inv] using hab

lemma inv_one_sub_inv (ha : a ≤ 1) : a⁻¹.HolderConjugate (1 - a)⁻¹ :=
  .inv_inv <| add_tsub_cancel_of_le ha

lemma inv_one_sub_inv' (ha : 1 ≤ a) : a.HolderConjugate (1 - a⁻¹)⁻¹ := by
  simpa using inv_one_sub_inv (ENNReal.inv_le_one.mpr ha)

lemma one_sub_inv_inv (ha : a ≤ 1) : (1 - a)⁻¹.HolderConjugate a⁻¹ := (inv_one_sub_inv ha).symm

lemma top_one : HolderConjugate ∞ 1 := ⟨by simp⟩
lemma one_top : HolderConjugate 1 ∞ := ⟨by simp⟩

end HolderConjugate

lemma isConjExponent_comm : p.HolderConjugate q ↔ q.HolderConjugate p := ⟨(·.symm), (·.symm)⟩

lemma isConjExponent_iff_eq_conjExponent (hp : 1 ≤ p) : p.HolderConjugate q ↔ q = 1 + (p - 1)⁻¹ :=
  ⟨fun h ↦ h.conj_eq, by rintro rfl; exact .conjExponent hp⟩

end ENNReal
