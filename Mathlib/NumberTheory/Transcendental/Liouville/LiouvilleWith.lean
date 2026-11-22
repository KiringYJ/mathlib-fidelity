/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.NumberTheory.Transcendental.Liouville.Basic
public import Mathlib.Topology.Instances.Irrational

/-!
# Liouville numbers with a given exponent

We say that a real number `x` is a Liouville number with exponent `p : ℝ` if there exists a real
number `C` such that for infinitely many denominators `n` there exists a numerator `m` such that
`x ≠ m / n` and `|x - m / n| < C / n ^ p`. A number is a Liouville number in the sense of
`Liouville` if it is `LiouvilleWith` any real exponent, see `forall_liouvilleWith_iff`.

* If `p ≤ 1`, then this condition is trivial.

* If `1 < p ≤ 2`, then this condition is equivalent to `Irrational x`. The forward implication
  does not require `p ≤ 2` and is formalized as `LiouvilleWith.irrational`; the other implication
  follows from approximations by continued fractions and is not formalized yet.

* If `p > 2`, then this is a non-trivial condition on irrational numbers. In particular,
  [Thue–Siegel–Roth theorem](https://en.wikipedia.org/wiki/Roth's_theorem) states that such numbers
  must be transcendental.

In this file we define the predicate `LiouvilleWith` and prove some basic facts about this
predicate.

## Tags

Liouville number, irrational, irrationality exponent
-/

@[expose] public section


open Filter Real Set

open scoped Filter Topology

/-- We say that a real number `x` is a Liouville number with exponent `p : ℝ` if there exists a real
number `C` such that for infinitely many denominators `n` there exists a numerator `m` such that
`x ≠ m / n` and `|x - m / n| < C / n ^ p`.

A number is a Liouville number in the sense of `Liouville` if it is `LiouvilleWith` any real
exponent. -/
def LiouvilleWith (p x : ℝ) : Prop :=
  ∃ C, ∃ᶠ n : ℕ in atTop, ∃ (_ : 0 < n) (m : ℤ),
        x ≠ (m : ℝ) / (n : ℝ) ∧ |x - (m : ℝ) / (n : ℝ)| < C / (n : ℝ) ^ p

/-- For `p = 1` (hence, for any `p ≤ 1`), the condition `LiouvilleWith p x` is trivial. -/
theorem liouvilleWith_one (x : ℝ) : LiouvilleWith 1 x := by
  use 2
  refine ((eventually_gt_atTop 0).mono fun n hn => ?_).frequently
  have hn' : (0 : ℝ) < n := by simpa
  have : x < ↑(⌊x * ↑n⌋ + 1) / ↑n := by
    rw [lt_div_iff₀ hn', Int.cast_add, Int.cast_one]
    exact Int.lt_floor_add_one _
  refine ⟨hn, ⌊x * n⌋ + 1, this.ne, ?_⟩
  simp only [rpow_one]
  rw [abs_sub_comm, abs_of_pos (sub_pos.2 this), sub_lt_iff_lt_add',
    add_div_eq_mul_add_div]
  gcongr
  calc _ ≤ x * n + 1 := by push_cast; gcongr; apply Int.floor_le
    _ < x * n + 2 := by linarith

namespace LiouvilleWith

variable {p q x : ℝ} {r : ℚ} {m : ℤ} {n : ℕ}

/-- The constant `C` provided by the definition of `LiouvilleWith` can be made positive.
The denominators satisfy `1 ≤ n`. -/
theorem exists_pos (h : LiouvilleWith p x) :
    ∃ (C : ℝ) (_h₀ : 0 < C),
      ∃ᶠ n : ℕ in atTop, ∃ (_ : 1 ≤ n) (m : ℤ),
        x ≠ (m : ℝ) / (n : ℝ) ∧ |x - (m : ℝ) / (n : ℝ)| < C / (n : ℝ) ^ p := by
  rcases h with ⟨C, hC⟩
  refine ⟨max C 1, zero_lt_one.trans_le <| le_max_right _ _, ?_⟩
  refine hC.mono ?_
  rintro n ⟨hle, m, hne, hlt⟩
  refine ⟨hle, m, hne, hlt.trans_le ?_⟩
  gcongr
  apply le_max_left

/-- If a number is Liouville with exponent `p`, then it is Liouville with any smaller exponent. -/
theorem mono (h : LiouvilleWith p x) (hle : q ≤ p) : LiouvilleWith q x := by
  rcases h.exists_pos with ⟨C, hC₀, hC⟩
  refine ⟨C, hC.mono ?_⟩; rintro n ⟨hn, m, hne, hlt⟩
  refine ⟨hn, m, hne, hlt.trans_le <| ?_⟩
  gcongr
  exact_mod_cast hn

/-- If `x` satisfies Liouville condition with exponent `p` and `q < p`, then `x`
satisfies Liouville condition with exponent `q` and constant `1`. -/
theorem frequently_lt_rpow_neg (h : LiouvilleWith p x) (hlt : q < p) :
    ∃ᶠ n : ℕ in atTop, ∃ (_ : 0 < n) (m : ℤ),
        x ≠ (m : ℝ) / (n : ℝ) ∧ |x - (m : ℝ) / (n : ℝ)| < (n : ℝ) ^ (-q) := by
  rcases h.exists_pos with ⟨C, _hC₀, hC⟩
  have : ∀ᶠ n : ℕ in atTop, C < n ^ (p - q) := by
    simpa only [(· ∘ ·), neg_sub, one_div] using
      ((tendsto_rpow_atTop (sub_pos.2 hlt)).comp tendsto_natCast_atTop_atTop).eventually
        (eventually_gt_atTop C)
  refine (this.and_frequently hC).mono ?_
  rintro n ⟨hnC, hn, m, hne, hlt⟩
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  refine ⟨hn, m, hne, hlt.trans <| (div_lt_iff₀ <| rpow_pos_of_pos hn' _).2 ?_⟩
  rwa [mul_comm, ← rpow_add hn', ← sub_eq_add_neg]

/-- The product of a Liouville number and a nonzero rational number is again a Liouville number. -/
theorem mul_rat (h : LiouvilleWith p x) (hr : r ≠ 0) : LiouvilleWith p (x * r) := by
  rcases h.exists_pos with ⟨C, _hC₀, hC⟩
  refine ⟨r.den ^ p * (|r| * C), (tendsto_id.nsmul_atTop r.pos).frequently (hC.mono ?_)⟩
  rintro n ⟨hn, m, hne, hlt⟩
  have hn' : 0 < r.den • id n := Nat.mul_pos r.pos hn
  have A : (↑(r.num * m) : ℝ) / ↑(r.den • id n) = (m : ℝ) / (n : ℝ) * r := by
    rw [Rat.cast_def r, div_mul_div_comm₀]
    simp [mul_comm]
  refine ⟨hn', r.num * m, ?_, ?_⟩
  · rw [A]; simp [hne, hr]
  · rw [A, ← sub_mul, abs_mul]
    simp only [smul_eq_mul, id, Nat.cast_mul]
    calc _ < C / ↑n ^ p * |↑r| := by gcongr
      _ = ↑r.den ^ p * (↑|r| * C) / (↑r.den * ↑n) ^ p := ?_
    rw [eq_div_iff, mul_rpow (by positivity : (0 : ℝ) ≤ r.den)
      (by positivity : (0 : ℝ) ≤ n), Rat.cast_abs]
    calc
      C / (n : ℝ) ^ p * |(r : ℝ)| * ((r.den : ℝ) ^ p * (n : ℝ) ^ p) =
          ((C / (n : ℝ) ^ p) * (n : ℝ) ^ p) * ((r.den : ℝ) ^ p * |(r : ℝ)|) := by ring
      _ = _ := by rw [div_mul_cancel₀]; ring

/-- The product `x * r`, `r : ℚ`, `r ≠ 0`, is a Liouville number with exponent `p` if and only if
`x` satisfies the same condition. -/
theorem mul_rat_iff (hr : r ≠ 0) : LiouvilleWith p (x * r) ↔ LiouvilleWith p x :=
  ⟨fun h => by
    have hu : IsUnit r := hr.isUnit
    simpa only [mul_assoc, ← Rat.cast_mul, mul_inv_cancel₀, Rat.cast_one, mul_one] using
      h.mul_rat (inv_ne_zero (ha := hu)),
    fun h => h.mul_rat hr⟩

/-- The product `r * x`, `r : ℚ`, `r ≠ 0`, is a Liouville number with exponent `p` if and only if
`x` satisfies the same condition. -/
theorem rat_mul_iff (hr : r ≠ 0) : LiouvilleWith p (r * x) ↔ LiouvilleWith p x := by
  rw [mul_comm, mul_rat_iff hr]

theorem rat_mul (h : LiouvilleWith p x) (hr : r ≠ 0) : LiouvilleWith p (r * x) :=
  (rat_mul_iff hr).2 h

theorem mul_int_iff (hm : m ≠ 0) : LiouvilleWith p (x * m) ↔ LiouvilleWith p x := by
  rw [← Rat.cast_intCast, mul_rat_iff (Int.cast_ne_zero.2 hm)]

theorem mul_int (h : LiouvilleWith p x) (hm : m ≠ 0) : LiouvilleWith p (x * m) :=
  (mul_int_iff hm).2 h

theorem int_mul_iff (hm : m ≠ 0) : LiouvilleWith p (m * x) ↔ LiouvilleWith p x := by
  rw [mul_comm, mul_int_iff hm]

theorem int_mul (h : LiouvilleWith p x) (hm : m ≠ 0) : LiouvilleWith p (m * x) :=
  (int_mul_iff hm).2 h

theorem mul_nat_iff (hn : n ≠ 0) : LiouvilleWith p (x * n) ↔ LiouvilleWith p x := by
  rw [← Rat.cast_natCast, mul_rat_iff (Nat.cast_ne_zero.2 hn)]

theorem mul_nat (h : LiouvilleWith p x) (hn : n ≠ 0) : LiouvilleWith p (x * n) :=
  (mul_nat_iff hn).2 h

theorem nat_mul_iff (hn : n ≠ 0) : LiouvilleWith p (n * x) ↔ LiouvilleWith p x := by
  rw [mul_comm, mul_nat_iff hn]

theorem nat_mul (h : LiouvilleWith p x) (hn : n ≠ 0) : LiouvilleWith p (n * x) := by
  rw [mul_comm]; exact h.mul_nat hn

theorem add_rat (h : LiouvilleWith p x) (r : ℚ) : LiouvilleWith p (x + r) := by
  rcases h.exists_pos with ⟨C, _hC₀, hC⟩
  refine ⟨r.den ^ p * C, (tendsto_id.nsmul_atTop r.pos).frequently (hC.mono ?_)⟩
  rintro n ⟨hn, m, hne, hlt⟩
  have hn' : 0 < r.den • id n := Nat.mul_pos r.pos hn
  have : (↑(r.den * m + r.num * n : ℤ) / ↑(r.den • id n) : ℝ) = (m : ℝ) / (n : ℝ) + r := by
    rw [Rat.cast_def r]
    simp only [smul_eq_mul, id_eq, Nat.cast_mul, Int.cast_add, Int.cast_mul, Int.cast_natCast]
    rw [add_div, mul_div_mul_left, mul_div_mul_right]
  refine ⟨hn', r.den * m + r.num * n, ?_⟩; rw [this, add_sub_add_right_eq_sub]
  refine ⟨by simpa, hlt.trans_le (le_of_eq ?_)⟩
  simp only [smul_eq_mul, id_eq, Nat.cast_mul, mul_rpow (by positivity : (0 : ℝ) ≤ r.den)
    (by positivity : (0 : ℝ) ≤ n), mul_div_mul_left]

@[simp]
theorem add_rat_iff : LiouvilleWith p (x + r) ↔ LiouvilleWith p x :=
  ⟨fun h => by simpa using h.add_rat (-r), fun h => h.add_rat r⟩

@[simp]
theorem rat_add_iff : LiouvilleWith p (r + x) ↔ LiouvilleWith p x := by rw [add_comm, add_rat_iff]

theorem rat_add (h : LiouvilleWith p x) (r : ℚ) : LiouvilleWith p (r + x) :=
  add_comm x r ▸ h.add_rat r

@[simp]
theorem add_int_iff : LiouvilleWith p (x + m) ↔ LiouvilleWith p x := by
  rw [← Rat.cast_intCast m, add_rat_iff]

@[simp]
theorem int_add_iff : LiouvilleWith p (m + x) ↔ LiouvilleWith p x := by rw [add_comm, add_int_iff]

@[simp]
theorem add_nat_iff : LiouvilleWith p (x + n) ↔ LiouvilleWith p x := by
  rw [← Rat.cast_natCast n, add_rat_iff]

@[simp]
theorem nat_add_iff : LiouvilleWith p (n + x) ↔ LiouvilleWith p x := by rw [add_comm, add_nat_iff]

theorem add_int (h : LiouvilleWith p x) (m : ℤ) : LiouvilleWith p (x + m) :=
  add_int_iff.2 h

theorem int_add (h : LiouvilleWith p x) (m : ℤ) : LiouvilleWith p (m + x) :=
  int_add_iff.2 h

theorem add_nat (h : LiouvilleWith p x) (n : ℕ) : LiouvilleWith p (x + n) :=
  h.add_int n

theorem nat_add (h : LiouvilleWith p x) (n : ℕ) : LiouvilleWith p (n + x) :=
  h.int_add n

protected theorem neg (h : LiouvilleWith p x) : LiouvilleWith p (-x) := by
  rcases h with ⟨C, hC⟩
  refine ⟨C, hC.mono ?_⟩
  rintro n ⟨hn, m, hne, hlt⟩
  refine ⟨hn, -m, by simp [neg_div₀, hne], ?_⟩
  convert! hlt using 1
  rw [abs_sub_comm]
  congr! 1; push_cast; ring

@[simp]
theorem neg_iff : LiouvilleWith p (-x) ↔ LiouvilleWith p x :=
  ⟨fun h => neg_neg x ▸ h.neg, LiouvilleWith.neg⟩

@[simp]
theorem sub_rat_iff : LiouvilleWith p (x - r) ↔ LiouvilleWith p x := by
  rw [sub_eq_add_neg, ← Rat.cast_neg, add_rat_iff]

theorem sub_rat (h : LiouvilleWith p x) (r : ℚ) : LiouvilleWith p (x - r) :=
  sub_rat_iff.2 h

@[simp]
theorem sub_int_iff : LiouvilleWith p (x - m) ↔ LiouvilleWith p x := by
  rw [← Rat.cast_intCast, sub_rat_iff]

theorem sub_int (h : LiouvilleWith p x) (m : ℤ) : LiouvilleWith p (x - m) :=
  sub_int_iff.2 h

@[simp]
theorem sub_nat_iff : LiouvilleWith p (x - n) ↔ LiouvilleWith p x := by
  rw [← Rat.cast_natCast, sub_rat_iff]

theorem sub_nat (h : LiouvilleWith p x) (n : ℕ) : LiouvilleWith p (x - n) :=
  sub_nat_iff.2 h

@[simp]
theorem rat_sub_iff : LiouvilleWith p (r - x) ↔ LiouvilleWith p x := by simp [sub_eq_add_neg]

theorem rat_sub (h : LiouvilleWith p x) (r : ℚ) : LiouvilleWith p (r - x) :=
  rat_sub_iff.2 h

@[simp]
theorem int_sub_iff : LiouvilleWith p (m - x) ↔ LiouvilleWith p x := by simp [sub_eq_add_neg]

theorem int_sub (h : LiouvilleWith p x) (m : ℤ) : LiouvilleWith p (m - x) :=
  int_sub_iff.2 h

@[simp]
theorem nat_sub_iff : LiouvilleWith p (n - x) ↔ LiouvilleWith p x := by simp [sub_eq_add_neg]

theorem nat_sub (h : LiouvilleWith p x) (n : ℕ) : LiouvilleWith p (n - x) :=
  nat_sub_iff.2 h

theorem ne_cast_int (h : LiouvilleWith p x) (hp : 1 < p) (m : ℤ) : x ≠ m := by
  rintro rfl; rename' m => M
  rcases (h.frequently_lt_rpow_neg hp).exists with
    ⟨n : ℕ, hn : 0 < n, m : ℤ, hne : (M : ℝ) ≠ (m : ℝ) / (n : ℝ),
      hlt : |(M - (m : ℝ) / (n : ℝ) : ℝ)| < (n : ℝ) ^ (-1 : ℝ)⟩
  refine hlt.not_ge ?_
  have hn' : (0 : ℝ) < n := by simpa
  rw [rpow_neg_one _ (hx := hn'.ne'.isUnit), ← one_div₀, sub_div', abs_div]
  simp only [abs_of_pos hn']
  gcongr
  norm_cast
  rw [← zero_add (1 : ℤ), Int.add_one_le_iff, abs_pos, sub_ne_zero]
  rw [Ne, eq_div_iff] at hne
  exact mod_cast hne

/-- A number satisfying the Liouville condition with exponent `p > 1` is an irrational number. -/
protected theorem irrational (h : LiouvilleWith p x) (hp : 1 < p) : Irrational x := by
  rintro ⟨r, rfl⟩
  rcases eq_or_ne r 0 with (rfl | h0)
  · refine h.ne_cast_int hp 0 ?_; rw [Rat.cast_zero, Int.cast_zero]
  · have hu : IsUnit r := h0.isUnit
    refine (h.mul_rat (inv_ne_zero (ha := hu))).ne_cast_int hp 1 ?_
    rw [← Rat.cast_mul, mul_inv_cancel₀, Rat.cast_one, Int.cast_one]

end LiouvilleWith

namespace Liouville

variable {x : ℝ}

/-- If `x` is a Liouville number, then for any `n`, for infinitely many denominators `b` there
exists a numerator `a` such that `x ≠ a / b` and `|x - a / b| < 1 / b ^ n`. -/
theorem frequently_exists_num (hx : Liouville x) (n : ℕ) :
    ∃ᶠ b : ℕ in atTop, ∃ (_ : 0 < b) (a : ℤ),
      x ≠ (a : ℝ) / (b : ℝ) ∧ |x - (a : ℝ) / (b : ℝ)| < 1 / (b : ℝ) ^ n := by
  by_contra! H
  simp only [eventually_atTop] at H
  rcases H with ⟨N, hN⟩
  have : ∀ (b : ℕ) (_ : 1 < b), ∀ᶠ m : ℕ in atTop, ∀ a : ℤ,
      1 / (b : ℝ) ^ m ≤ |x - (a : ℝ) / (b : ℝ)| := by
    intro b hb
    replace hb : (1 : ℝ) < b := Nat.one_lt_cast.2 hb
    have H : Tendsto (fun m => 1 / (b : ℝ) ^ m : ℕ → ℝ) atTop (𝓝 0) := by
      simpa only [one_div₀] using (tendsto_pow_atTop_atTop_of_one_lt hb).fun_inv_tendsto_atTop
        (h0 := fun m => (zero_lt_one.trans hb).ne'.isUnit.pow m)
    refine (H.eventually (hx.irrational.eventually_forall_le_dist_cast_div b
      (Nat.cast_ne_zero.1 (zero_lt_one.trans hb).ne'))).mono ?_
    exact fun m hm a => hm a
  have : ∀ᶠ m : ℕ in atTop, ∀ b < N, ∀ (_ : 1 < b) (a : ℤ),
      1 / (b : ℝ) ^ m ≤ |x - (a : ℝ) / (b : ℝ)| :=
    (finite_lt_nat N).eventually_all.2 fun b _hb => by
      by_cases h : 1 < b
      · exact (this b h).mono fun _ hm _ a => hm a
      · exact .of_forall fun _ h' => absurd h' h
  rcases (this.and (eventually_ge_atTop n)).exists with ⟨m, hm, hnm⟩
  rcases hx m with ⟨a, b, hb, hne, hlt⟩
  lift b to ℕ using zero_le_one.trans hb.le; norm_cast at hb; push_cast at hne hlt
  rcases le_or_gt N b with h | h
  · refine (hN b h (zero_lt_one.trans hb) a hne).not_gt (hlt.trans_le ?_)
    gcongr
    exact_mod_cast hb.le
  · exact (hm b h hb _).not_gt hlt

/-- A Liouville number is a Liouville number with any real exponent. -/
protected theorem liouvilleWith (hx : Liouville x) (p : ℝ) : LiouvilleWith p x := by
  suffices LiouvilleWith ⌈p⌉₊ x from this.mono (Nat.le_ceil p)
  refine ⟨1, (hx.frequently_exists_num ⌈p⌉₊).mono ?_⟩
  rintro b ⟨hb, a, hne, hlt⟩
  exact ⟨hb, a, hne, by simpa only [rpow_natCast] using hlt⟩

end Liouville

/-- A number satisfies the Liouville condition with any exponent if and only if it is a Liouville
number. -/
theorem forall_liouvilleWith_iff {x : ℝ} : (∀ p, LiouvilleWith p x) ↔ Liouville x := by
  refine ⟨fun H n => ?_, Liouville.liouvilleWith⟩
  rcases ((eventually_gt_atTop 1).and_frequently
    ((H (n + 1)).frequently_lt_rpow_neg (lt_add_one (n : ℝ)))).exists
    with ⟨b, hb, _, a, hne, hlt⟩
  have hb' : (0 : ℝ) < b := Nat.cast_pos.mpr (zero_lt_one.trans hb)
  exact ⟨a, b, mod_cast hb, hne, by simpa only [Int.cast_natCast, one_div₀,
    (rpow_neg hb'.le n (hxy := (rpow_pos_of_pos hb' _).ne'.isUnit)), rpow_natCast] using hlt⟩
