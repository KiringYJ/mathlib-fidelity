/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Sébastien Gouëzel,
  Rémy Degenne, David Loeffler
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-! # Power function on `ℂ`

We construct the power functions `x ^ y`, where `x` and `y` are complex numbers.
-/

@[expose] public section

open Real Topology Filter Finset Set

open scoped ComplexConjugate

namespace Complex

/-- The complex power function `x ^ y`, given by `x ^ y = exp(y log x)` (where `log` is the
principal determination of the logarithm), unless `x = 0` where one sets `0 ^ 0 = 1` and
`0 ^ y = 0` for `y ≠ 0`. -/
noncomputable def cpow (x y : ℂ) : ℂ :=
  if x = 0 then if y = 0 then 1 else 0 else exp (log x * y)

noncomputable instance : Pow ℂ ℂ :=
  ⟨cpow⟩

@[simp]
theorem cpow_eq_pow (x y : ℂ) : cpow x y = x ^ y :=
  rfl

theorem cpow_def (x y : ℂ) : x ^ y = if x = 0 then if y = 0 then 1 else 0 else exp (log x * y) :=
  rfl

theorem cpow_def_of_ne_zero {x : ℂ} (hx : x ≠ 0) (y : ℂ) : x ^ y = exp (log x * y) :=
  ite_eq_right hx

@[simp]
theorem cpow_zero (x : ℂ) : x ^ (0 : ℂ) = 1 := by simp [cpow_def]

@[simp]
theorem cpow_eq_zero_iff (x y : ℂ) : x ^ y = 0 ↔ x = 0 ∧ y ≠ 0 := by
  simp only [cpow_def]
  split_ifs <;> simp [*, exp_ne_zero]

theorem cpow_ne_zero_iff {x y : ℂ} :
    x ^ y ≠ 0 ↔ x ≠ 0 ∨ y = 0 := by
  rw [ne_eq, cpow_eq_zero_iff, not_and_or, ne_eq, not_not]

theorem cpow_ne_zero_iff_of_exponent_ne_zero {x y : ℂ} (hy : y ≠ 0) :
    x ^ y ≠ 0 ↔ x ≠ 0 := by simp [hy]

@[simp]
theorem zero_cpow {x : ℂ} (h : x ≠ 0) : (0 : ℂ) ^ x = 0 := by simp [cpow_def, *]

theorem zero_cpow_eq_iff {x : ℂ} {a : ℂ} : (0 : ℂ) ^ x = a ↔ x ≠ 0 ∧ a = 0 ∨ x = 0 ∧ a = 1 := by
  constructor
  · intro hyp
    simp only [cpow_def, ite_true] at hyp
    grind
  · rintro (⟨h, rfl⟩ | ⟨rfl, rfl⟩)
    · exact zero_cpow h
    · exact cpow_zero _

theorem eq_zero_cpow_iff {x : ℂ} {a : ℂ} : a = (0 : ℂ) ^ x ↔ x ≠ 0 ∧ a = 0 ∨ x = 0 ∧ a = 1 := by
  rw [← zero_cpow_eq_iff, eq_comm]

@[simp]
theorem cpow_one (x : ℂ) : x ^ (1 : ℂ) = x :=
  if hx : x = 0 then by simp [hx, cpow_def]
  else by
    rw [cpow_def, ite_eq_right (one_ne_zero : (1 : ℂ) ≠ 0), ite_eq_right hx, mul_one, exp_log hx]

@[simp]
theorem one_cpow (x : ℂ) : (1 : ℂ) ^ x = 1 := by
  rw [cpow_def]
  split_ifs <;> simp_all [one_ne_zero]

theorem cpow_add {x : ℂ} (y z : ℂ) (hx : x ≠ 0) : x ^ (y + z) = x ^ y * x ^ z := by
  simp only [cpow_def, ite_mul, mul_ite]
  simp_all [exp_add, mul_add]

theorem cpow_mul {x y : ℂ} (z : ℂ) (h₁ : -π < (log x * y).im) (h₂ : (log x * y).im ≤ π) :
    x ^ (y * z) = (x ^ y) ^ z := by
  simp only [cpow_def]
  split_ifs <;> simp_all [exp_ne_zero, log_exp h₁ h₂, mul_assoc]

theorem cpow_neg (x y : ℂ) {hxy : IsUnit (x ^ y)} : x ^ (-y) = (x ^ y)⁻¹ := by
  rcases eq_or_ne x 0 with rfl | hx
  · have hy : y = 0 := by simpa using (cpow_ne_zero_iff.mp hxy.ne_zero)
    subst y
    simp
  · simp only [cpow_def_of_ne_zero hx, mul_neg, exp_neg]

theorem cpow_sub {x : ℂ} (y z : ℂ) {hxz : IsUnit (x ^ z)} :
    x ^ (y - z) = x ^ y / x ^ z := by
  rcases eq_or_ne x 0 with rfl | hx
  · have hz : z = 0 := by simpa using (cpow_ne_zero_iff.mp hxz.ne_zero)
    subst z
    simp
  · rw [sub_eq_add_neg, cpow_add _ _ hx, cpow_neg, div_eq_mul_inv₀]

theorem cpow_neg_one (x : ℂ) {hx : IsUnit x} : x ^ (-1 : ℂ) = x⁻¹ := by
  simpa using cpow_neg x 1 (hxy := by simpa using hx)

/-- See also `Complex.cpow_int_mul'`. -/
lemma cpow_int_mul (x : ℂ) (n : ℤ) (y : ℂ) {h : n < 0 → IsUnit (x ^ y)} :
    x ^ (n * y) = (x ^ y) ^ n := by
  rcases eq_or_ne x 0 with rfl | hx
  · rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rcases eq_or_ne y 0 with rfl | hy
      · simp
      · have hnpos : 0 < n := lt_of_le_of_ne (by
          by_contra hnneg
          exact (h (lt_of_not_ge hnneg)).ne_zero (by simp [hy])) (Ne.symm hn)
        simp [hy, hn, zero_zpow]
  · simp only [cpow_def_of_ne_zero hx]
    rw [← exp_int_mul]
    congr 1
    ring

lemma cpow_mul_int (x y : ℂ) (n : ℤ) {h : n < 0 → IsUnit (x ^ y)} :
    x ^ (y * n) = (x ^ y) ^ n := by rw [mul_comm, cpow_int_mul]

lemma cpow_nat_mul (x : ℂ) (n : ℕ) (y : ℂ) : x ^ (n * y) = (x ^ y) ^ n :=
  mod_cast cpow_int_mul x n y (h := fun hn => (not_lt_of_ge (Int.natCast_nonneg n) hn).elim)

lemma cpow_ofNat_mul (x : ℂ) (n : ℕ) [n.AtLeastTwo] (y : ℂ) :
    x ^ (ofNat(n) * y) = (x ^ y) ^ ofNat(n) :=
  cpow_nat_mul x n y

lemma cpow_mul_nat (x y : ℂ) (n : ℕ) : x ^ (y * n) = (x ^ y) ^ n := by
  rw [mul_comm, cpow_nat_mul]

lemma cpow_mul_ofNat (x y : ℂ) (n : ℕ) [n.AtLeastTwo] :
    x ^ (y * ofNat(n)) = (x ^ y) ^ ofNat(n) :=
  cpow_mul_nat x y n

@[simp, norm_cast]
theorem cpow_natCast (x : ℂ) (n : ℕ) : x ^ (n : ℂ) = x ^ n := by simpa using cpow_nat_mul x n 1

@[simp]
lemma cpow_ofNat (x : ℂ) (n : ℕ) [n.AtLeastTwo] :
    x ^ (ofNat(n) : ℂ) = x ^ ofNat(n) :=
  cpow_natCast x n

theorem cpow_two (x : ℂ) : x ^ (2 : ℂ) = x ^ (2 : ℕ) := cpow_ofNat x 2

@[simp, norm_cast]
theorem cpow_intCast (x : ℂ) (n : ℤ) {h : n < 0 → x ≠ 0} :
    x ^ (n : ℂ) = Checked.zpow x n (fun hn => (h hn).isUnit) := by
  simpa using cpow_int_mul x n 1 (h := fun hn => by simpa using (h hn).isUnit)

@[simp]
theorem cpow_nat_inv_pow (x : ℂ) {n : ℕ} (hn : n ≠ 0) : (x ^ (n⁻¹ : ℂ)) ^ n = x := by
  rw [← cpow_nat_mul, mul_inv_cancel₀, cpow_one]

@[simp]
lemma cpow_ofNat_inv_pow (x : ℂ) (n : ℕ) [n.AtLeastTwo] :
    (x ^ ((ofNat(n) : ℂ)⁻¹)) ^ (ofNat(n) : ℕ) = x :=
  cpow_nat_inv_pow _ (NeZero.ne n)

/-- A version of `Complex.cpow_int_mul` with RHS that matches `Complex.cpow_mul`.

The assumptions on the arguments are needed
because the equality fails, e.g., for `x = -I`, `n = 2`, `y = 1/2`. -/
lemma cpow_int_mul' {x : ℂ} {n : ℤ} {h : n < 0 → IsUnit x}
    (hlt : -π < n * x.arg) (hle : n * x.arg ≤ π) (y : ℂ) :
    x ^ (n * y) = (x ^ n) ^ y := by
  rw [mul_comm] at hlt hle
  rw [cpow_mul, cpow_intCast (h := fun hn => (h hn).ne_zero)] <;> simpa [log_im]

/-- A version of `Complex.cpow_nat_mul` with RHS that matches `Complex.cpow_mul`.

The assumptions on the arguments are needed
because the equality fails, e.g., for `x = -I`, `n = 2`, `y = 1/2`. -/
lemma cpow_nat_mul' {x : ℂ} {n : ℕ} (hlt : -π < n * x.arg) (hle : n * x.arg ≤ π) (y : ℂ) :
    x ^ (n * y) = (x ^ n) ^ y :=
  cpow_int_mul' (h := fun hn => (not_lt_of_ge (Int.natCast_nonneg n) hn).elim) hlt hle y

lemma cpow_ofNat_mul' {x : ℂ} {n : ℕ} [n.AtLeastTwo] (hlt : -π < OfNat.ofNat n * x.arg)
    (hle : OfNat.ofNat n * x.arg ≤ π) (y : ℂ) :
    x ^ (OfNat.ofNat n * y) = (x ^ ofNat(n)) ^ y :=
  cpow_nat_mul' hlt hle y

lemma pow_cpow_nat_inv {x : ℂ} {n : ℕ} (h₀ : n ≠ 0)
    (hlt : -(π / (n : ℝ)) < x.arg) (hle : x.arg ≤ π / (n : ℝ)) :
    (x ^ n) ^ (n⁻¹ : ℂ) = x := by
  rw [← cpow_nat_mul', mul_inv_cancel₀, cpow_one]
  · rwa [← div_lt_iff₀' (Nat.cast_pos.2 h₀.bot_lt), neg_div₀]
  · rwa [← le_div_iff₀' (Nat.cast_pos.2 h₀.bot_lt)]

lemma pow_cpow_ofNat_inv {x : ℂ} {n : ℕ} [n.AtLeastTwo] (hlt : -(π / OfNat.ofNat n) < x.arg)
    (hle : x.arg ≤ π / OfNat.ofNat n) :
    (x ^ ofNat(n)) ^ ((OfNat.ofNat n : ℂ)⁻¹) = x :=
  pow_cpow_nat_inv (NeZero.ne n) hlt hle

/-- See also `Complex.pow_cpow_ofNat_inv` for a version that also works for `x * I`, `0 ≤ x`. -/
lemma sq_cpow_two_inv {x : ℂ} (hx : 0 < x.re) : (x ^ (2 : ℕ)) ^ (2⁻¹ : ℂ) = x :=
  pow_cpow_ofNat_inv (neg_pi_div_two_lt_arg_iff.2 <| .inl hx)
    (arg_le_pi_div_two_iff.2 <| .inl hx.le)

@[simp] lemma isSquare (x : ℂ) : IsSquare x := ⟨x ^ (2⁻¹ : ℂ), by simp [← sq]⟩

theorem mul_cpow_ofReal_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (r : ℂ) :
    ((a : ℂ) * (b : ℂ)) ^ r = (a : ℂ) ^ r * (b : ℂ) ^ r := by
  rcases eq_or_ne r 0 with (rfl | hr)
  · simp only [cpow_zero, mul_one]
  rcases eq_or_lt_of_le ha with (rfl | ha')
  · rw [ofReal_zero, zero_mul, zero_cpow hr, zero_mul]
  rcases eq_or_lt_of_le hb with (rfl | hb')
  · rw [ofReal_zero, mul_zero, zero_cpow hr, mul_zero]
  have ha'' : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha'.ne'
  have hb'' : (b : ℂ) ≠ 0 := ofReal_ne_zero.mpr hb'.ne'
  rw [cpow_def_of_ne_zero (mul_ne_zero ha'' hb''), log_ofReal_mul ha' hb'', ofReal_log ha,
    add_mul, exp_add, ← cpow_def_of_ne_zero ha'', ← cpow_def_of_ne_zero hb'']

lemma natCast_mul_natCast_cpow (m n : ℕ) (s : ℂ) : (m * n : ℂ) ^ s = m ^ s * n ^ s :=
  ofReal_natCast m ▸ ofReal_natCast n ▸ mul_cpow_ofReal_nonneg m.cast_nonneg n.cast_nonneg s

lemma natCast_cpow_natCast_mul (n m : ℕ) (z : ℂ) : (n : ℂ) ^ (m * z) = ((n : ℂ) ^ m) ^ z := by
  refine cpow_nat_mul' (x := n) (n := m) ?_ ?_ z
  · simp only [natCast_arg, mul_zero, Left.neg_neg_iff, pi_pos]
  · simp only [natCast_arg, mul_zero, pi_pos.le]

theorem inv_cpow_eq_ite (x : ℂ) (n : ℂ) {hx : IsUnit x} :
    x⁻¹ ^ n = if x.arg = π then conj (x ^ conj n)⁻¹ else (x ^ n)⁻¹ := by
  simp only [cpow_def_of_ne_zero hx.ne_zero, cpow_def_of_ne_zero (inv_ne_zero (ha := hx)),
    log_inv_eq_ite, ite_mul]
  split_ifs <;> simp [neg_mul, exp_neg, ← exp_conj, map_mul]

theorem inv_cpow (x : ℂ) (n : ℂ) {hx₀ : IsUnit x} (hx : x.arg ≠ π) : x⁻¹ ^ n = (x ^ n)⁻¹ := by
  rw [inv_cpow_eq_ite, ite_eq_right hx]

lemma inv_cpow_ofReal_nonneg {a : ℝ} (ha : 0 ≤ a) (r : ℂ) {ha₀ : IsUnit a} :
    ((a : ℂ)⁻¹) ^ r = (a ^ r : ℂ)⁻¹ :=
  inv_cpow _ _ <| by simpa [arg_ofReal_of_nonneg ha] using Real.pi_ne_zero.symm

lemma div_cpow_ofReal_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (r : ℂ) {hb₀ : IsUnit b} :
    ((a : ℂ) / (b : ℂ)) ^ r = (a : ℂ) ^ r / (b : ℂ) ^ r := by
  rw [div_eq_mul_inv₀, ← ofReal_inv, mul_cpow_ofReal_nonneg ha (inv_nonneg_of_nonneg hb),
    ofReal_inv, inv_cpow_ofReal_nonneg hb, div_eq_mul_inv₀]
  all_goals assumption

/-- `Complex.inv_cpow_eq_ite` with the `ite` on the other side. -/
theorem inv_cpow_eq_ite' (x : ℂ) (n : ℂ) {hx : IsUnit x} :
    (x ^ n)⁻¹ = if x.arg = π then conj (x⁻¹ ^ conj n) else x⁻¹ ^ n := by
  simp only [inv_cpow_eq_ite, apply_ite conj, conj_conj]
  split_ifs <;> rfl

theorem conj_cpow_eq_ite (x : ℂ) (n : ℂ) :
    conj x ^ n = if x.arg = π then x ^ n else conj (x ^ conj n) := by
  simp_rw [cpow_def, map_eq_zero, apply_ite conj, map_one, map_zero, ← exp_conj, map_mul, conj_conj,
    log_conj_eq_ite]
  split_ifs with hcx hn hx <;> rfl

theorem conj_cpow (x : ℂ) (n : ℂ) (hx : x.arg ≠ π) : conj x ^ n = conj (x ^ conj n) := by
  rw [conj_cpow_eq_ite, ite_eq_right hx]

theorem cpow_conj (x : ℂ) (n : ℂ) (hx : x.arg ≠ π) : x ^ conj n = conj (conj x ^ n) := by
  rw [conj_cpow _ _ hx, conj_conj]

lemma natCast_add_one_cpow_ne_zero (n : ℕ) (z : ℂ) : (n + 1 : ℂ) ^ z ≠ 0 :=
  mt (cpow_eq_zero_iff ..).mp fun H ↦ by norm_cast at H; exact H.1

end Complex

-- section Tactics

-- /-!
-- ## Tactic extensions for complex powers
-- -/


-- namespace NormNum

-- theorem cpow_pos (a b : ℂ) (b' : ℕ) (c : ℂ) (hb : b = b') (h : a ^ b' = c) : a ^ b = c := by
--   rw [← h, hb, Complex.cpow_natCast]

-- theorem cpow_neg (a b : ℂ) (b' : ℕ) (c c' : ℂ) (hb : b = b') (h : a ^ b' = c) (hc : c⁻¹ = c') :
--     a ^ (-b) = c' := by rw [← hc, ← h, hb, Complex.cpow_neg, Complex.cpow_natCast]

-- open Tactic

-- /-- Generalized version of `prove_cpow`, `prove_nnrpow`, `prove_ennrpow`. -/
-- unsafe def prove_rpow' (pos neg zero : Name) (α β one a b : expr) : tactic (expr × expr) := do
--   let na ← a.to_rat
--   let icα ← mk_instance_cache α
--   let icβ ← mk_instance_cache β
--   match match_sign b with
--     | Sum.inl b => do
--       let nc ← mk_instance_cache q(ℕ)
--       let (icβ, nc, b', hb) ← prove_nat_uncast icβ nc b
--       let (icα, c, h) ← prove_pow a na icα b'
--       let cr ← c
--       let (icα, c', hc) ← prove_inv icα c cr
--       pure (c', (expr.const neg []).mk_app [a, b, b', c, c', hb, h, hc])
--     | Sum.inr ff => pure (one, expr.const zero [] a)
--     | Sum.inr tt => do
--       let nc ← mk_instance_cache q(ℕ)
--       let (icβ, nc, b', hb) ← prove_nat_uncast icβ nc b
--       let (icα, c, h) ← prove_pow a na icα b'
--       pure (c, (expr.const Pos []).mk_app [a, b, b', c, hb, h])

-- /-- Evaluate `Complex.cpow a b` where `a` is a rational numeral and `b` is an integer. -/
-- unsafe def prove_cpow : expr → expr → tactic (expr × expr) :=
--   prove_rpow' `` cpow_pos `` cpow_neg `` Complex.cpow_zero q(ℂ) q(ℂ) q((1 : ℂ))

-- /-- Evaluates expressions of the form `cpow a b` and `a ^ b` in the special case where
-- `b` is an integer and `a` is a positive rational (so it's really just a rational power). -/
-- @[norm_num]
-- unsafe def eval_cpow : expr → tactic (expr × expr)
--   | q(@Pow.pow _ _ Complex.hasPow $(a) $(b)) => b.to_int >> prove_cpow a b
--   | q(Complex.cpow $(a) $(b)) => b.to_int >> prove_cpow a b
--   | _ => tactic.failed

-- end NormNum

-- end Tactics
