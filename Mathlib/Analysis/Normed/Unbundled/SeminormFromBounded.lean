/-
Copyright (c) 2024 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
module

public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm

/-!
# seminormFromBounded

In this file, we prove [BGR, Proposition 1.2.1/2][bosch-guntzer-remmert] : given a nonzero
additive group seminorm on a commutative ring `R` such that for some `c : ℝ` and every `x y : R`,
the inequality `f (x * y) ≤ c * f x * f y)` is satisfied, we create a ring seminorm on `R`.

In the file comments, we will use the expression `f is multiplicatively bounded` to indicate that
this condition holds.


## Main Definitions

* `seminormFromBounded'` : the real-valued function sending `x ∈ R` to the supremum of
  `f(x*y)/f(y)` over the elements `y` with `f y ≠ 0`.
* `seminormFromBounded` : the function `seminormFromBounded'` as a `RingSeminorm` on `R`.
* `normFromBounded` :`seminormFromBounded' f` as a `RingNorm` on `R`, provided that `f` is
  nonnegative, multiplicatively bounded and subadditive, that it preserves `0` and negation, and
  that `f` has trivial kernel.


## Main Results

* `seminormFromBounded_isNonarchimedean` : if `f : R → ℝ` is a nonnegative, multiplicatively
  bounded, nonarchimedean function, then `seminormFromBounded' f` is nonarchimedean.
* `seminormFromBounded_of_mul_is_mul` : if `f : R → ℝ` is a nonnegative, multiplicatively bounded
  function and `x : R` is multiplicative for `f`, then `x` is multiplicative for
  `seminormFromBounded' f`.

## References
* [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert]

## Tags

seminormFromBounded, RingSeminorm, Nonarchimedean
-/

@[expose] public section

noncomputable section

open scoped Topology NNReal

variable {R : Type _} [CommRing R] (f : R → ℝ) {c : ℝ}

section seminormFromBounded

/-- The real-valued function sending `x ∈ R` to the supremum of `f(x*y)/f(y)` over
the elements `y` with `f y ≠ 0`. The empty supremum gives the zero seminorm when `f = 0`. -/
def seminormFromBounded' : R → ℝ := fun x ↦
  ⨆ y : {y : R // f y ≠ 0}, Checked.div (f (x * y)) (f y) y.2.isUnit

variable {f}

private theorem seminormFromBounded_le_of_forall {x : R} {b : ℝ} (hb : 0 ≤ b)
    (hle : ∀ y : {y : R // f y ≠ 0}, Checked.div (f (x * y)) (f y) y.2.isUnit ≤ b) :
    seminormFromBounded' f x ≤ b := by
  rw [seminormFromBounded']
  rcases isEmpty_or_nonempty {y : R // f y ≠ 0} with _ | _
  · rwa [Real.iSup_of_isEmpty]
  · exact ciSup_le hle

private theorem seminormFromBounded_nonneg_of_bddAbove (f_nonneg : 0 ≤ f) (x : R)
    (hbdd : BddAbove (Set.range fun y : {y : R // f y ≠ 0} ↦
      Checked.div (f (x * y)) (f y) y.2.isUnit)) : 0 ≤ seminormFromBounded' f x := by
  rw [seminormFromBounded']
  rcases isEmpty_or_nonempty {y : R // f y ≠ 0} with _ | h
  · rw [Real.iSup_of_isEmpty]
  · obtain ⟨y⟩ := h
    exact le_ciSup_of_le hbdd y (div_nonneg (f_nonneg _) (f_nonneg _))

/-- If `f : R → ℝ` is a nonzero, nonnegative, multiplicatively bounded function, then `f 1 ≠ 0`. -/
theorem map_one_ne_zero (f_ne_zero : f ≠ 0) (f_nonneg : 0 ≤ f)
    (f_mul : ∀ x y : R, f (x * y) ≤ c * f x * f y) : f 1 ≠ 0 := by
  intro h1
  specialize f_mul 1
  simp_rw [h1, one_mul, mul_zero, zero_mul] at f_mul
  obtain ⟨z, hz⟩ := Function.ne_iff.mp f_ne_zero
  exact hz <| (f_mul z).antisymm (f_nonneg z)

/-- If `f : R → ℝ` is a nonnegative multiplicatively bounded function and `x : R` is a unit with
  `f x ≠ 0`, then for every `n : ℕ`, we have `f (x ^ n) ≠ 0`. -/
theorem map_pow_ne_zero (f_nonneg : 0 ≤ f) {x : R} (hx : IsUnit x) (hfx : f x ≠ 0) (n : ℕ)
    (f_mul : ∀ x y : R, f (x * y) ≤ c * f x * f y) : f (x ^ n) ≠ 0 := by
  have h1 : f 1 ≠ 0 := map_one_ne_zero (Function.ne_iff.mpr ⟨x, hfx⟩) f_nonneg f_mul
  intro hxn
  have : f 1 ≤ 0 := by simpa [← mul_pow, hxn] using f_mul (x ^ n) (hx.unit⁻¹ ^ n)
  exact h1 <| this.antisymm (f_nonneg 1)

/-- If `f : R → ℝ` is a nonnegative, multiplicatively bounded function, then given `x y : R` with
  `f x = 0`, we have `f (x * y) = 0`. -/
theorem map_mul_zero_of_map_zero (f_nonneg : 0 ≤ f)
    (f_mul : ∀ x y : R, f (x * y) ≤ c * f x * f y) {x : R} (hx : f x = 0)
    (y : R) : f (x * y) = 0 := by
  replace f_mul : f (x * y) ≤ 0 := by simpa [hx] using f_mul x y
  exact le_antisymm f_mul (f_nonneg _)

/-- `seminormFromBounded' f` preserves `0`. -/
theorem seminormFromBounded_zero (f_zero : f 0 = 0) : seminormFromBounded' f (0 : R) = 0 := by
  simp [seminormFromBounded', f_zero]

theorem seminormFromBounded_aux (f_nonneg : 0 ≤ f)
    (f_mul : ∀ x y : R, f (x * y) ≤ c * f x * f y) (x : R) : 0 ≤ c * f x := by
  rcases (f_nonneg x).eq_or_lt' with hx | hx
  · simp [hx]
  · change 0 < f x at hx
    by_contra! h
    have hle : f x ≤ c * f x * f 1 := by simpa only [mul_one] using f_mul x 1
    exact hx.not_ge (hle.trans (mul_nonpos_of_nonpos_of_nonneg h.le (f_nonneg 1)))

/-- If `f : R → ℝ` is a nonnegative, multiplicatively bounded function, then for every `x : R`,
  the image of `y ↦ f (x * y) / f y` over `y` with `f y ≠ 0` is bounded above. -/
theorem seminormFromBounded_bddAbove_range (f_nonneg : 0 ≤ f)
    (f_mul : ∀ x y : R, f (x * y) ≤ c * f x * f y) (x : R) :
    BddAbove (Set.range fun y : {y : R // f y ≠ 0} ↦
      Checked.div (f (x * y)) (f y) y.2.isUnit) := by
  use c * f x
  rintro r ⟨y, rfl⟩
  exact (div_le_iff₀ (lt_of_le_of_ne' (f_nonneg _) y.2)).2 (f_mul x y)

private theorem le_seminormFromBounded (f_nonneg : 0 ≤ f)
    (f_mul : ∀ x y : R, f (x * y) ≤ c * f x * f y) (x : R) (y : {y : R // f y ≠ 0}) :
    Checked.div (f (x * y)) (f y) y.2.isUnit ≤ seminormFromBounded' f x :=
  le_ciSup (seminormFromBounded_bddAbove_range f_nonneg f_mul x) y

/-- If `f : R → ℝ` is a nonnegative, multiplicatively bounded function, then for every `x : R`,
  `seminormFromBounded' f x` is bounded above by some multiple of `f x`. -/
theorem seminormFromBounded_le (f_nonneg : 0 ≤ f)
    (f_mul : ∀ x y : R, f (x * y) ≤ c * f x * f y) (x : R) :
    seminormFromBounded' f x ≤ c * f x := by
  apply seminormFromBounded_le_of_forall (seminormFromBounded_aux f_nonneg f_mul x)
  intro y
  exact (div_le_iff₀ (lt_of_le_of_ne' (f_nonneg _) y.2)).2 (f_mul x y)

/-- If `f : R → ℝ` is a nonnegative, multiplicatively bounded function, then for every `x : R`,
  `f x ≤ f 1 * seminormFromBounded' f x`. -/
theorem seminormFromBounded_ge (f_nonneg : 0 ≤ f)
    (f_mul : ∀ x y : R, f (x * y) ≤ c * f x * f y) (x : R) :
    f x ≤ f 1 * seminormFromBounded' f x := by
  by_cases h1 : f 1 = 0
  · specialize f_mul x 1
    rw [mul_one, h1, mul_zero] at f_mul
    have hx0 : f x = 0 := f_mul.antisymm (f_nonneg _)
    rw [hx0, h1, zero_mul]
  · rw [mul_comm, ← div_le_iff₀ (lt_of_le_of_ne' (f_nonneg _) h1)]
    simpa only [mul_one] using le_seminormFromBounded f_nonneg f_mul x ⟨1, h1⟩

/-- If `f : R → ℝ` is a nonnegative, multiplicatively bounded function, then
  `seminormFromBounded' f` is nonnegative. -/
theorem seminormFromBounded_nonneg (f_nonneg : 0 ≤ f)
    (f_mul : ∀ x y : R, f (x * y) ≤ c * f x * f y) :
    0 ≤ seminormFromBounded' f := fun x ↦
  seminormFromBounded_nonneg_of_bddAbove f_nonneg x
    (seminormFromBounded_bddAbove_range f_nonneg f_mul x)

/-- If `f : R → ℝ` is a nonnegative, multiplicatively bounded function, then
  `seminormFromBounded' f x = 0` if and only if `f x = 0`. -/
theorem seminormFromBounded_eq_zero_iff (f_nonneg : 0 ≤ f)
    (f_mul : ∀ x y : R, f (x * y) ≤ c * f x * f y) (x : R) :
    seminormFromBounded' f x = 0 ↔ f x = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hf := seminormFromBounded_ge f_nonneg f_mul x
    rw [h, mul_zero] at hf
    exact hf.antisymm (f_nonneg _)
  · have hf : seminormFromBounded' f x ≤ c * f x :=
      seminormFromBounded_le f_nonneg f_mul x
    rw [h, mul_zero] at hf
    exact hf.antisymm (seminormFromBounded_nonneg f_nonneg f_mul x)

/-- If `f` is invariant under negation of `x`, then so is `seminormFromBounded'`. -/
theorem seminormFromBounded_neg (f_neg : ∀ x : R, f (-x) = f x) (x : R) :
    seminormFromBounded' f (-x) = seminormFromBounded' f x := by
  simp [seminormFromBounded', neg_mul, f_neg]

/-- If `f : R → ℝ` is a nonnegative, multiplicatively bounded function, then
  `seminormFromBounded' f` is submultiplicative. -/
theorem seminormFromBounded_mul (f_nonneg : 0 ≤ f)
    (f_mul : ∀ x y : R, f (x * y) ≤ c * f x * f y) (x y : R) :
    seminormFromBounded' f (x * y) ≤ seminormFromBounded' f x * seminormFromBounded' f y := by
  have hnonneg := seminormFromBounded_nonneg f_nonneg f_mul
  apply seminormFromBounded_le_of_forall (mul_nonneg (hnonneg x) (hnonneg y))
  intro z
  have hz := lt_of_le_of_ne' (f_nonneg _) z.2
  rw [div_le_iff₀ hz, mul_right_comm x y (z : R)]
  by_cases hxz : f (x * z) = 0
  · rw [map_mul_zero_of_map_zero f_nonneg f_mul hxz y]
    exact mul_nonneg (mul_nonneg (hnonneg x) (hnonneg y)) (f_nonneg _)
  · have hx := (div_le_iff₀ hz).1 (le_seminormFromBounded f_nonneg f_mul x z)
    have hy := (div_le_iff₀ (lt_of_le_of_ne' (f_nonneg _) hxz)).1
      (le_seminormFromBounded f_nonneg f_mul y ⟨x * z, hxz⟩)
    calc
      f ((x * z) * y) = f (y * (x * z)) := by rw [mul_comm]
      _ ≤ seminormFromBounded' f y * f (x * z) := hy
      _ ≤ seminormFromBounded' f y * (seminormFromBounded' f x * f z) :=
        mul_le_mul_of_nonneg_left hx (hnonneg y)
      _ = _ := by rw [← mul_assoc, mul_comm (seminormFromBounded' f y)]

/-- If `f : R → ℝ` is a nonzero, nonnegative, multiplicatively bounded function, then
  `seminormFromBounded' f 1 = 1`. -/
theorem seminormFromBounded_one (f_ne_zero : f ≠ 0) (f_nonneg : 0 ≤ f)
    (f_mul : ∀ x y : R, f (x * y) ≤ c * f x * f y) :
    seminormFromBounded' f 1 = 1 := by
  apply le_antisymm
  · exact seminormFromBounded_le_of_forall zero_le_one (fun y ↦ by simp)
  · simpa using
      le_seminormFromBounded f_nonneg f_mul 1 ⟨1, map_one_ne_zero f_ne_zero f_nonneg f_mul⟩

/-- If `f : R → ℝ` is a nonnegative, multiplicatively bounded function, then
  `seminormFromBounded' f 1 ≤ 1`. -/
theorem seminormFromBounded_one_le (f_nonneg : 0 ≤ f)
    (f_mul : ∀ x y : R, f (x * y) ≤ c * f x * f y) :
    seminormFromBounded' f 1 ≤ 1 := by
  by_cases! f_ne_zero : f ≠ 0
  · exact le_of_eq (seminormFromBounded_one f_ne_zero f_nonneg f_mul)
  · subst f
    have : IsEmpty {y : R // (0 : R → ℝ) y ≠ 0} := ⟨fun y ↦ y.2 rfl⟩
    rw [seminormFromBounded', Real.iSup_of_isEmpty]
    exact zero_le_one

/-- If `f : R → ℝ` is a nonnegative, multiplicatively bounded, subadditive function, then
  `seminormFromBounded' f` is subadditive. -/
theorem seminormFromBounded_add (f_nonneg : 0 ≤ f)
    (f_mul : ∀ x y : R, f (x * y) ≤ c * f x * f y)
    (f_add : ∀ a b, f (a + b) ≤ f a + f b) (x y : R) :
    seminormFromBounded' f (x + y) ≤ seminormFromBounded' f x + seminormFromBounded' f y := by
  have hnonneg := seminormFromBounded_nonneg f_nonneg f_mul
  apply seminormFromBounded_le_of_forall (add_nonneg (hnonneg x) (hnonneg y))
  intro z
  have hz := lt_of_le_of_ne' (f_nonneg _) z.2
  refine le_trans ?_ (add_le_add
    (le_seminormFromBounded f_nonneg f_mul x z) (le_seminormFromBounded f_nonneg f_mul y z))
  rw [← add_div, div_le_div_iff_of_pos_right hz, add_mul]
  exact f_add _ _

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- `seminormFromBounded'` is a ring seminorm on `R`. -/
def seminormFromBounded (f_zero : f 0 = 0) (f_nonneg : 0 ≤ f)
    (f_mul : ∀ x y : R, f (x * y) ≤ c * f x * f y)
    (f_add : ∀ a b, f (a + b) ≤ f a + f b) (f_neg : ∀ x : R, f (-x) = f x) : RingSeminorm R where
  toFun     := seminormFromBounded' f
  map_zero' := seminormFromBounded_zero f_zero
  add_le'   := seminormFromBounded_add f_nonneg f_mul f_add
  mul_le'   := seminormFromBounded_mul f_nonneg f_mul
  neg'      := seminormFromBounded_neg f_neg

/-- If `f : R → ℝ` is a nonnegative, multiplicatively bounded, nonarchimedean function, then
  `seminormFromBounded' f` is nonarchimedean. -/
theorem seminormFromBounded_isNonarchimedean (f_nonneg : 0 ≤ f)
    (f_mul : ∀ x y : R, f (x * y) ≤ c * f x * f y)
    (hna : IsNonarchimedean f) : IsNonarchimedean (seminormFromBounded' f) := by
  intro x y
  apply seminormFromBounded_le_of_forall
    ((seminormFromBounded_nonneg f_nonneg f_mul x).trans (le_max_left _ _))
  intro z
  have hz := lt_of_le_of_ne' (f_nonneg _) z.2
  have h := le_max_iff.mp (hna (x * z) (y * z))
  rw [add_mul]
  rcases h with h | h
  · exact le_max_of_le_left (((div_le_div_iff_of_pos_right hz).2 h).trans
      (le_seminormFromBounded f_nonneg f_mul x z))
  · exact le_max_of_le_right (((div_le_div_iff_of_pos_right hz).2 h).trans
      (le_seminormFromBounded f_nonneg f_mul y z))

/-- If `f : R → ℝ` is a nonnegative, multiplicatively bounded function and `x : R` is
  multiplicative for `f`, then `seminormFromBounded' f x = f x`. -/
theorem seminormFromBounded_of_mul_apply (f_nonneg : 0 ≤ f)
    (f_mul : ∀ x y : R, f (x * y) ≤ c * f x * f y) {x : R}
    (hx : ∀ y : R, f (x * y) = f x * f y) : seminormFromBounded' f x = f x := by
  apply le_antisymm
  · exact seminormFromBounded_le_of_forall (f_nonneg _) (fun y ↦ by simp [hx])
  · by_cases hf : f = 0
    · simpa only [hf, Pi.zero_apply] using seminormFromBounded_nonneg f_nonneg f_mul x
    · simpa only [hx, mul_div_cancel_right₀] using
        le_seminormFromBounded f_nonneg f_mul x ⟨1, map_one_ne_zero hf f_nonneg f_mul⟩

/-- If `f : R → ℝ` is a nonnegative function and `x : R` is submultiplicative for `f`, then
  `seminormFromBounded' f x = f x`. -/
theorem seminormFromBounded_of_mul_le (f_nonneg : 0 ≤ f) {x : R}
    (hx : ∀ y : R, f (x * y) ≤ f x * f y) (h_one : f 1 ≤ 1) : seminormFromBounded' f x = f x := by
  have hle (y : {y : R // f y ≠ 0}) : Checked.div (f (x * y)) (f y) y.2.isUnit ≤ f x :=
    (div_le_iff₀ (lt_of_le_of_ne' (f_nonneg _) y.2)).2 (hx y)
  have hbdd : BddAbove (Set.range fun y : {y : R // f y ≠ 0} ↦
      Checked.div (f (x * y)) (f y) y.2.isUnit) := by
    use f x
    rintro _ ⟨y, rfl⟩
    exact hle y
  apply le_antisymm
  · exact seminormFromBounded_le_of_forall (f_nonneg _) hle
  · by_cases h0 : f x = 0
    · rw [h0]
      exact seminormFromBounded_nonneg_of_bddAbove f_nonneg x hbdd
    · have heq : f 1 = 1 := by
        apply h_one.antisymm
        simpa only [mul_one, le_mul_iff_one_le_right (lt_of_le_of_ne' (f_nonneg _) h0)]
          using hx 1
      have h1 : f 1 ≠ 0 := heq.trans_ne one_ne_zero
      have hquot : Checked.div (f x) (f 1) h1.isUnit = f x := by
        apply div_eq_iff.2
        rw [heq, mul_one]
      simpa only [seminormFromBounded', mul_one, hquot] using
        le_ciSup hbdd (⟨1, h1⟩ : {y : R // f y ≠ 0})

/-- If `f : R → ℝ` is a nonzero, nonnegative, multiplicatively bounded function, then
  `seminormFromBounded' f` is nonzero. -/
theorem seminormFromBounded_nonzero (f_ne_zero : f ≠ 0) (f_nonneg : 0 ≤ f)
    (f_mul : ∀ x y : R, f (x * y) ≤ c * f x * f y) :
    seminormFromBounded' f ≠ 0 := by
  obtain ⟨x, hx⟩ := Function.ne_iff.mp f_ne_zero
  rw [Function.ne_iff]
  use x
  rw [ne_eq, Pi.zero_apply, seminormFromBounded_eq_zero_iff f_nonneg f_mul x]
  exact hx

/-- If `f : R → ℝ` is a nonnegative, multiplicatively bounded function, then the kernel of
  `seminormFromBounded' f` equals the kernel of `f`. -/
theorem seminormFromBounded_ker (f_nonneg : 0 ≤ f)
    (f_mul : ∀ x y : R, f (x * y) ≤ c * f x * f y) :
    seminormFromBounded' f ⁻¹' {0} = f ⁻¹' {0} := by
  ext x
  exact seminormFromBounded_eq_zero_iff f_nonneg f_mul x

/-- If `f : R → ℝ` is a nonnegative, multiplicatively bounded, subadditive function that preserves
  zero and negation, then `seminormFromBounded' f` is a norm if and only if `f⁻¹' {0} = {0}`. -/
theorem seminormFromBounded_is_norm_iff (f_zero : f 0 = 0) (f_nonneg : 0 ≤ f)
    (f_mul : ∀ x y : R, f (x * y) ≤ c * f x * f y)
    (f_add : ∀ a b, f (a + b) ≤ f a + f b) (f_neg : ∀ x : R, f (-x) = f x) :
    (∀ x : R, (seminormFromBounded f_zero f_nonneg f_mul f_add f_neg).toFun x = 0 → x = 0) ↔
      f ⁻¹' {0} = {0} := by
  refine ⟨fun h0 ↦ ?_, fun h_ker x hx ↦ ?_⟩
  · rw [← seminormFromBounded_ker f_nonneg f_mul]
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun h ↦ h0 x h, fun h ↦ by rw [h]; exact seminormFromBounded_zero f_zero⟩
  · rw [← Set.mem_singleton_iff, ← h_ker, Set.mem_preimage, Set.mem_singleton_iff,
      ← seminormFromBounded_eq_zero_iff f_nonneg f_mul x]
    exact hx

/-- `seminormFromBounded' f` as a `RingNorm` on `R`, provided that `f` is nonnegative,
  multiplicatively bounded and subadditive, that it preserves `0` and negation, and that `f` has
  trivial kernel. -/
def normFromBounded (f_zero : f 0 = 0) (f_nonneg : 0 ≤ f)
    (f_mul : ∀ x y : R, f (x * y) ≤ c * f x * f y)
    (f_add : ∀ a b, f (a + b) ≤ f a + f b) (f_neg : ∀ x : R, f (-x) = f x)
    (f_ker : f ⁻¹' {0} = {0}) : RingNorm R :=
  { seminormFromBounded f_zero f_nonneg f_mul f_add f_neg with
    eq_zero_of_map_eq_zero' :=
      (seminormFromBounded_is_norm_iff f_zero f_nonneg f_mul f_add f_neg).mpr f_ker }

/-- If `f : R → ℝ` is a nonnegative, multiplicatively bounded function and `x : R` is
  multiplicative for `f`, then `x` is multiplicative for `seminormFromBounded' f`. -/
theorem seminormFromBounded_of_mul_is_mul (f_nonneg : 0 ≤ f)
    (f_mul : ∀ x y : R, f (x * y) ≤ c * f x * f y) {x : R}
    (hx : ∀ y : R, f (x * y) = f x * f y) (y : R) :
    seminormFromBounded' f (x * y) = seminormFromBounded' f x * seminormFromBounded' f y := by
  rw [seminormFromBounded_of_mul_apply f_nonneg f_mul hx]
  simp only [seminormFromBounded', mul_assoc, hx, mul_div_assoc₀,
    Real.mul_iSup_of_nonneg (f_nonneg _)]

end seminormFromBounded
