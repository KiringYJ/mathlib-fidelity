/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson
-/
module

public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# Complex trigonometric functions

Basic facts and derivatives for the complex trigonometric functions.

Several facts about the real trigonometric functions have the proofs deferred here, rather than
`Analysis.SpecialFunctions.Trigonometric.Basic`,
as they are most easily proved by appealing to the corresponding fact for complex trigonometric
functions, or require additional imports which are not available in that file.
-/

public section


noncomputable section

namespace Complex

open Set Filter Finset

open scoped Real

theorem cos_eq_zero_iff {θ : ℂ} : cos θ = 0 ↔ ∃ k : ℤ, θ = (2 * k + 1) * π / 2 := by
  have h : (exp (θ * I) + exp (-θ * I)) / 2 = 0 ↔ exp (2 * θ * I) = -1 := by
    rw [@div_eq_iff _ _ (exp (θ * I) + exp (-θ * I)) 2 0 two_ne_zero, zero_mul,
      add_eq_zero_iff_eq_neg, neg_eq_neg_one_mul, ← div_eq_iff (exp_ne_zero _), ← exp_sub]
    ring_nf
  rw [cos, h, ← exp_pi_mul_I, exp_eq_exp_iff_exists_int, mul_right_comm]
  refine exists_congr fun x => ?_
  refine (iff_of_eq <| congr_arg _ ?_).trans (mul_right_inj' <| mul_ne_zero two_ne_zero I_ne_zero)
  ring

theorem cos_ne_zero_iff {θ : ℂ} : cos θ ≠ 0 ↔ ∀ k : ℤ, θ ≠ (2 * k + 1) * π / 2 := by
  contrapose!; exact cos_eq_zero_iff

theorem sin_eq_zero_iff {θ : ℂ} : sin θ = 0 ↔ ∃ k : ℤ, θ = k * π := by
  rw [← Complex.cos_sub_pi_div_two, cos_eq_zero_iff]
  constructor
  · rintro ⟨k, hk⟩
    use k + 1
    simp [eq_add_of_sub_eq hk]
    ring
  · rintro ⟨k, rfl⟩
    use k - 1
    simp
    ring

theorem sin_ne_zero_iff {θ : ℂ} : sin θ ≠ 0 ↔ ∀ k : ℤ, θ ≠ k * π := by
  contrapose!; exact sin_eq_zero_iff

/-- The tangent of a complex number at which it is defined is zero iff the number is an integer
multiple of `π`. -/
theorem tan_eq_zero_iff {θ : ℂ} {hθ : cos θ ≠ 0} : tan θ = 0 ↔ ∃ k : ℤ, k * π = θ := by
  simp only [tan_eq_sin_div_cos, div_eq_zero_iff, sin_eq_zero_iff]
  simp [eq_comm]

theorem tan_ne_zero_iff {θ : ℂ} {hθ : cos θ ≠ 0} : tan θ ≠ 0 ↔ ∀ k : ℤ, (k * π : ℂ) ≠ θ := by
  rw [Ne, tan_eq_zero_iff, not_exists]

theorem cos_eq_cos_iff {x y : ℂ} : cos x = cos y ↔ ∃ k : ℤ, y = 2 * k * π + x ∨ y = 2 * k * π - x :=
  calc
    cos x = cos y ↔ cos x - cos y = 0 := sub_eq_zero.symm
    _ ↔ -2 * sin ((x + y) / 2) * sin ((x - y) / 2) = 0 := by rw [cos_sub_cos]
    _ ↔ sin ((x + y) / 2) = 0 ∨ sin ((x - y) / 2) = 0 := by simp [(by simp : (2 : ℂ) ≠ 0)]
    _ ↔ sin ((x - y) / 2) = 0 ∨ sin ((x + y) / 2) = 0 := or_comm
    _ ↔ (∃ k : ℤ, y = 2 * k * π + x) ∨ ∃ k : ℤ, y = 2 * k * π - x := by
      apply or_congr <;>
        simp only [field, sin_eq_zero_iff, eq_sub_iff_add_eq',
          sub_eq_iff_eq_add, mul_comm (2 : ℂ), mul_right_comm _ (2 : ℂ)]
      constructor <;> · rintro ⟨k, rfl⟩; use -k; simp
    _ ↔ ∃ k : ℤ, y = 2 * k * π + x ∨ y = 2 * k * π - x := exists_or.symm

theorem sin_eq_sin_iff {x y : ℂ} :
    sin x = sin y ↔ ∃ k : ℤ, y = 2 * k * π + x ∨ y = (2 * k + 1) * π - x := by
  simp only [← Complex.cos_sub_pi_div_two, cos_eq_cos_iff, sub_eq_iff_eq_add]
  refine exists_congr fun k => or_congr ?_ ?_ <;> refine Eq.congr rfl ?_ <;> simp [field] <;> ring

theorem cos_eq_one_iff {x : ℂ} : cos x = 1 ↔ ∃ k : ℤ, k * (2 * π) = x := by
  rw [← cos_zero, eq_comm, cos_eq_cos_iff]
  simp [mul_assoc, mul_left_comm, eq_comm]

theorem cos_eq_neg_one_iff {x : ℂ} : cos x = -1 ↔ ∃ k : ℤ, π + k * (2 * π) = x := by
  rw [← neg_eq_iff_eq_neg, ← cos_sub_pi, cos_eq_one_iff]
  simp only [eq_sub_iff_add_eq']

theorem sin_eq_one_iff {x : ℂ} : sin x = 1 ↔ ∃ k : ℤ, π / 2 + k * (2 * π) = x := by
  rw [← cos_sub_pi_div_two, cos_eq_one_iff]
  simp only [eq_sub_iff_add_eq']

theorem sin_eq_neg_one_iff {x : ℂ} : sin x = -1 ↔ ∃ k : ℤ, -(π / 2) + k * (2 * π) = x := by
  rw [← neg_eq_iff_eq_neg, ← cos_add_pi_div_two, cos_eq_one_iff]
  simp only [← sub_eq_neg_add, sub_eq_iff_eq_add]

/-- The cosine of a sum in terms of the tangents of the summands. -/
theorem cos_add_eq_mul_one_sub_tan_mul_tan {x y : ℂ} (hx : cos x ≠ 0) (hy : cos y ≠ 0) :
    cos (x + y) = cos x * cos y * (1 - tan x * tan y) := by
  rw [cos_add, ← tan_mul_cos hx, ← tan_mul_cos hy]
  ring

/-- The cosine of a difference in terms of the tangents of the terms. -/
theorem cos_sub_eq_mul_one_add_tan_mul_tan {x y : ℂ} (hx : cos x ≠ 0) (hy : cos y ≠ 0) :
    cos (x - y) = cos x * cos y * (1 + tan x * tan y) := by
  rw [cos_sub, ← tan_mul_cos hx, ← tan_mul_cos hy]
  ring

theorem one_sub_tan_mul_tan_ne_zero {x y : ℂ} (hx : cos x ≠ 0) (hy : cos y ≠ 0)
    (hxy : cos (x + y) ≠ 0) : 1 - tan x * tan y ≠ 0 :=
  right_ne_zero_of_mul (cos_add_eq_mul_one_sub_tan_mul_tan hx hy ▸ hxy)

theorem one_add_tan_mul_tan_ne_zero {x y : ℂ} (hx : cos x ≠ 0) (hy : cos y ≠ 0)
    (hxy : cos (x - y) ≠ 0) : 1 + tan x * tan y ≠ 0 :=
  right_ne_zero_of_mul (cos_sub_eq_mul_one_add_tan_mul_tan hx hy ▸ hxy)

theorem one_sub_tan_sq_ne_zero {z : ℂ} (hz : cos z ≠ 0) (h : cos (2 * z) ≠ 0) :
    1 - tan z ^ 2 ≠ 0 := by
  rw [sq]
  exact one_sub_tan_mul_tan_ne_zero hz hz (two_mul z ▸ h)

/-! The rule below extends `checked_nonzero`: the denominators of the addition formulas for the
tangent are nonzero where the tangent of the sum or difference is defined. -/

macro_rules | `(tactic| checked_nonzero) => `(tactic|
    solve
    | assumption
    | (apply Complex.one_sub_tan_mul_tan_ne_zero <;> assumption)
    | (apply Complex.one_add_tan_mul_tan_ne_zero <;> assumption)
    | (apply Complex.one_sub_tan_sq_ne_zero <;> assumption))

/-- The addition formula for the tangent, where the tangents of `x`, `y` and `x + y` are
defined. -/
theorem tan_add {x y : ℂ} (hx : cos x ≠ 0) (hy : cos y ≠ 0) {hxy : cos (x + y) ≠ 0} :
    tan (x + y) = (tan x + tan y) / (1 - tan x * tan y) := by
  rw [eq_div_iff_mul_eq]
  refine mul_right_cancel₀ (mul_ne_zero hx hy) ?_
  calc tan (x + y) * (1 - tan x * tan y) * (cos x * cos y) = tan (x + y) * cos (x + y) := by
        rw [cos_add_eq_mul_one_sub_tan_mul_tan hx hy]; ring
    _ = (tan x + tan y) * (cos x * cos y) := by
        rw [tan_mul_cos, sin_add, ← tan_mul_cos hx, ← tan_mul_cos hy]; ring

/-- The subtraction formula for the tangent, where the tangents of `x`, `y` and `x - y` are
defined. -/
theorem tan_sub {x y : ℂ} (hx : cos x ≠ 0) (hy : cos y ≠ 0) {hxy : cos (x - y) ≠ 0} :
    tan (x - y) = (tan x - tan y) / (1 + tan x * tan y) := by
  rw [eq_div_iff_mul_eq]
  refine mul_right_cancel₀ (mul_ne_zero hx hy) ?_
  calc tan (x - y) * (1 + tan x * tan y) * (cos x * cos y) = tan (x - y) * cos (x - y) := by
        rw [cos_sub_eq_mul_one_add_tan_mul_tan hx hy]; ring
    _ = (tan x - tan y) * (cos x * cos y) := by
        rw [tan_mul_cos, sin_sub, ← tan_mul_cos hx, ← tan_mul_cos hy]; ring

theorem tan_two_mul {z : ℂ} {h : cos (2 * z) ≠ 0} (hz : cos z ≠ 0) :
    tan (2 * z) = 2 * tan z / (1 - tan z ^ 2) := by
  have := tan_add hz hz (hxy := two_mul z ▸ h)
  simp only [two_mul, sq] at this ⊢
  exact this

theorem tan_add_mul_I {x y : ℂ} (hx : cos x ≠ 0) (hy : cosh y ≠ 0) {h : cos (x + y * I) ≠ 0} :
    tan (x + y * I) =
      Checked.div (tan x + tanh y * I) (1 - tan x * tanh y * I) (by
        have := one_sub_tan_mul_tan_ne_zero (y := y * I) hx (cos_mul_I y ▸ hy) h
        rw [tan_mul_I, ← mul_assoc] at this
        exact this.isUnit) := by
  rw [tan_add (y := y * I) hx (cos_mul_I y ▸ hy) (hxy := h)]
  simp only [tan_mul_I, mul_assoc]

theorem tan_eq {z : ℂ} {hz : cos z ≠ 0} (hre : cos (z.re : ℂ) ≠ 0) :
    tan z =
      Checked.div (tan z.re + tanh z.im * I) (1 - tan z.re * tanh z.im * I) (by
        have := one_sub_tan_mul_tan_ne_zero (y := z.im * I) hre
          (cos_mul_I z.im ▸ cosh_ofReal_ne_zero z.im)
          (by rwa [re_add_im])
        rw [tan_mul_I, ← mul_assoc] at this
        exact this.isUnit) := by
  have := tan_add_mul_I (x := z.re) (y := z.im) hre (cosh_ofReal_ne_zero z.im)
    (h := by rwa [re_add_im])
  simp only [re_add_im] at this
  exact this

-- tangent half-angle substitution formulas

theorem cos_half_ne_zero_of_cos_ne_neg_one {x : ℂ} (h : cos x ≠ -1) : cos (x / 2) ≠ 0 := by
  intro h0
  apply h
  rw [show x = 2 * (x / 2) by ring, cos_two_mul, h0]
  ring

theorem cos_eq_two_mul_tan_half_div_one_sub_tan_half_sq (x : ℂ) (h : cos x ≠ -1) :
    cos x = (1 - tan (x / 2) (cos_half_ne_zero_of_cos_ne_neg_one h) ^ 2) /
      (1 + tan (x / 2) (cos_half_ne_zero_of_cos_ne_neg_one h) ^ 2) := by
  have hc := cos_half_ne_zero_of_cos_ne_neg_one h
  rw [div_eq_mul_inv₀, inv_one_add_tan_sq hc]
  conv_lhs => rw [show x = 2 * (x / 2) by ring, cos_two_mul', ← tan_mul_cos hc]
  ring

theorem sin_eq_two_mul_tan_half_div_one_add_tan_half_sq (x : ℂ) (h : cos (x / 2) ≠ 0) :
    sin x = (2 * tan (x / 2)) / (1 + tan (x / 2) ^ 2) := by
  rw [div_eq_mul_inv₀, inv_one_add_tan_sq h]
  conv_lhs => rw [show x = 2 * (x / 2) by ring, sin_two_mul, ← tan_mul_cos h]
  ring

theorem tan_eq_one_sub_tan_half_sq_div_one_add_tan_half_sq (x : ℂ) {hx : cos x ≠ 0}
    (h : cos (x / 2) ≠ 0) :
    tan x = Checked.div (2 * tan (x / 2)) (1 - tan (x / 2) ^ 2)
      (one_sub_tan_sq_ne_zero h (by rwa [mul_div_cancel₀])).isUnit := by
  have := tan_two_mul (z := x / 2) (h := by rwa [mul_div_cancel₀]) h
  simp only [mul_div_cancel₀] at this
  exact this

open scoped Topology

/-- The tangent is continuous on its domain. -/
@[continuity]
theorem continuous_tan : Continuous fun x : {x : ℂ // cos x ≠ 0} ↦ tan x x.2 :=
  (continuous_sin.comp continuous_subtype_val).div (continuous_cos.comp continuous_subtype_val)
    fun x ↦ x.2.isUnit

theorem cos_eq_iff_quadratic {z w : ℂ} :
    cos z = w ↔ exp (z * I) ^ 2 - 2 * w * exp (z * I) + 1 = 0 := by
  rw [← sub_eq_zero]
  simpa [field, cos, exp_neg] using Eq.congr (by ring) rfl

theorem cos_surjective : Function.Surjective cos := by
  intro x
  obtain ⟨w, w₀, hw⟩ : ∃ w ≠ 0, 1 * (w * w) + -2 * x * w + 1 = 0 := by
    rcases exists_quadratic_eq_zero one_ne_zero
        ⟨_, (cpow_nat_inv_pow _ two_ne_zero).symm.trans <| pow_two _⟩ with
      ⟨w, hw⟩
    refine ⟨w, ?_, hw⟩
    rintro rfl
    simp only [zero_add, one_ne_zero, mul_zero] at hw
  refine ⟨log w / I, cos_eq_iff_quadratic.2 ?_⟩
  rw [div_mul_cancel₀ _ I_ne_zero, exp_log w₀]
  convert! hw using 1
  ring

@[simp]
theorem range_cos : Set.range cos = Set.univ :=
  cos_surjective.range_eq

theorem sin_surjective : Function.Surjective sin := by
  intro x
  rcases cos_surjective x with ⟨z, rfl⟩
  exact ⟨z + π / 2, sin_add_pi_div_two z⟩

@[simp]
theorem range_sin : Set.range sin = Set.univ :=
  sin_surjective.range_eq

theorem sin_mul_sum_sin (n : ℕ) (a b : ℂ) :
    sin (a / 2) * ∑ i ∈ range n, sin (a * i + b) = sin (n * a / 2) * sin ((n - 1) * a / 2 + b) := by
  apply mul_left_cancel₀ (show (-2 : ℂ) ≠ 0 by simp)
  simp_rw [← mul_assoc, mul_sum]
  calc
    ∑ i ∈ range n, -2 * sin (a / 2) * sin (a * i + b)
      = ∑ x ∈ range n, (cos (a * (↑(x + 1) - 1 / 2) + b) - cos (-(a * (x - 1 / 2) + b))) := by
      congr! 1 with x hx
      rw [cos_sub_cos]
      push_cast
      ring_nf
    _ = -2 * sin (n * a / 2) * sin ((n - 1) * a / 2 + b) := by
      simp_rw [cos_neg, sum_range_sub (fun i ↦ cos (a * (i - 1 / 2) + b)), cos_sub_cos]
      ring_nf

theorem sin_half_ne_zero_of_ne {a : ℂ} (h : ∀ k : ℤ, a ≠ k * (2 * π)) : sin (a / 2) ≠ 0 :=
  sin_ne_zero_iff.2 fun k hk ↦ h k <| by
    calc a = 2 * (a / 2) := (mul_div_cancel₀ a).symm
      _ = k * (2 * π) := by rw [hk]; ring

theorem sum_sin (n : ℕ) {a : ℂ} (h : ∀ k : ℤ, a ≠ k * (2 * π)) (b : ℂ) :
    ∑ i ∈ range n, sin (a * i + b) =
      Checked.div (sin (n * a / 2) * sin ((n - 1) * a / 2 + b)) (sin (a / 2))
        (sin_half_ne_zero_of_ne h).isUnit := by
  rw [eq_div_iff_mul_eq, mul_comm _ (sin (a / 2)), sin_mul_sum_sin]

theorem sin_mul_sum_cos (n : ℕ) (a b : ℂ) :
    sin (a / 2) * ∑ i ∈ range n, cos (a * i + b) = sin (n * a / 2) * cos ((n - 1) * a / 2 + b) := by
  apply mul_left_cancel₀ (show (2 : ℂ) ≠ 0 by simp)
  simp_rw [← mul_assoc, mul_sum]
  calc
    ∑ i ∈ range n, 2 * sin (a / 2) * cos (a * i + b)
      = ∑ x ∈ range n, (sin (a * (↑(x + 1) - 1 / 2) + b) - sin (a * (x - 1 / 2) + b)) := by
      congr! 1 with x hx
      rw [sin_sub_sin]
      push_cast
      ring_nf
    _ = 2 * sin (n * a / 2) * cos ((n - 1) * a / 2 + b) := by
      simp_rw [sum_range_sub (fun i ↦ sin (a * (i - 1 / 2) + b)), sin_sub_sin]
      ring_nf

theorem sum_cos (n : ℕ) {a : ℂ} (h : ∀ k : ℤ, a ≠ k * (2 * π)) (b : ℂ) :
    ∑ i ∈ range n, cos (a * i + b) =
      Checked.div (sin (n * a / 2) * cos ((n - 1) * a / 2 + b)) (sin (a / 2))
        (sin_half_ne_zero_of_ne h).isUnit := by
  rw [eq_div_iff_mul_eq, mul_comm _ (sin (a / 2)), sin_mul_sum_cos]

end Complex

namespace Real

open scoped Real
open Finset

theorem cos_eq_zero_iff {θ : ℝ} : cos θ = 0 ↔ ∃ k : ℤ, θ = (2 * k + 1) * π / 2 :=
  mod_cast @Complex.cos_eq_zero_iff θ

theorem cos_ne_zero_iff {θ : ℝ} : cos θ ≠ 0 ↔ ∀ k : ℤ, θ ≠ (2 * k + 1) * π / 2 :=
  mod_cast @Complex.cos_ne_zero_iff θ

theorem cos_eq_cos_iff {x y : ℝ} : cos x = cos y ↔ ∃ k : ℤ, y = 2 * k * π + x ∨ y = 2 * k * π - x :=
  mod_cast @Complex.cos_eq_cos_iff x y

theorem sin_eq_sin_iff {x y : ℝ} :
    sin x = sin y ↔ ∃ k : ℤ, y = 2 * k * π + x ∨ y = (2 * k + 1) * π - x :=
  mod_cast @Complex.sin_eq_sin_iff x y

theorem cos_eq_neg_one_iff {x : ℝ} : cos x = -1 ↔ ∃ k : ℤ, π + k * (2 * π) = x :=
  mod_cast @Complex.cos_eq_neg_one_iff x

lemma abs_cos_eq_one_iff {x : ℝ} :
    |cos x| = 1 ↔ ∃ k : ℤ, k * π = x := by
  rw [← abs_one, abs_eq_abs, cos_eq_one_iff, cos_eq_neg_one_iff]
  constructor
  · rintro (⟨n, h⟩ | ⟨n, h⟩)
    · exact ⟨2 * n, by grind⟩
    · exact ⟨1 + n * 2, by grind⟩
  · rintro (⟨n, h⟩)
    obtain (⟨n, rfl⟩ | ⟨n, rfl⟩) := n.even_or_odd
    · exact .inl ⟨n, by grind⟩
    · exact .inr ⟨n, by grind⟩

theorem sin_eq_one_iff {x : ℝ} : sin x = 1 ↔ ∃ k : ℤ, π / 2 + k * (2 * π) = x :=
  mod_cast @Complex.sin_eq_one_iff x

theorem sin_eq_neg_one_iff {x : ℝ} : sin x = -1 ↔ ∃ k : ℤ, -(π / 2) + k * (2 * π) = x :=
  mod_cast @Complex.sin_eq_neg_one_iff x

lemma abs_sin_eq_one_iff {x : ℝ} :
    |sin x| = 1 ↔ ∃ k : ℤ, π / 2 + k * π = x := by
  rw [← abs_one, abs_eq_abs, sin_eq_one_iff, sin_eq_neg_one_iff]
  constructor
  · rintro (⟨n, h⟩ | ⟨n, h⟩)
    · exact ⟨2 * n, by grind⟩
    · exact ⟨-1 + n * 2, by grind⟩
  · rintro (⟨n, h⟩)
    obtain (⟨n, rfl⟩ | ⟨n, rfl⟩) := n.even_or_odd
    · exact .inl ⟨n, by grind⟩
    · exact .inr ⟨n + 1, by grind⟩

/-- The tangent of a real number at which it is defined is zero iff the number is an integer
multiple of `π`. -/
theorem tan_eq_zero_iff {θ : ℝ} {hθ : cos θ ≠ 0} : tan θ = 0 ↔ ∃ k : ℤ, k * π = θ := by
  rw [tan_eq_sin_div_cos, div_eq_zero_iff, sin_eq_zero_iff]

theorem tan_ne_zero_iff {θ : ℝ} {hθ : cos θ ≠ 0} : tan θ ≠ 0 ↔ ∀ k : ℤ, k * π ≠ θ := by
  rw [Ne, tan_eq_zero_iff, not_exists]

/-- The cosine of a sum in terms of the tangents of the summands. -/
theorem cos_add_eq_mul_one_sub_tan_mul_tan {x y : ℝ} (hx : cos x ≠ 0) (hy : cos y ≠ 0) :
    cos (x + y) = cos x * cos y * (1 - tan x * tan y) := by
  rw [cos_add, ← tan_mul_cos hx, ← tan_mul_cos hy]
  ring

/-- The cosine of a difference in terms of the tangents of the terms. -/
theorem cos_sub_eq_mul_one_add_tan_mul_tan {x y : ℝ} (hx : cos x ≠ 0) (hy : cos y ≠ 0) :
    cos (x - y) = cos x * cos y * (1 + tan x * tan y) := by
  rw [cos_sub, ← tan_mul_cos hx, ← tan_mul_cos hy]
  ring

theorem one_sub_tan_mul_tan_ne_zero {x y : ℝ} (hx : cos x ≠ 0) (hy : cos y ≠ 0)
    (hxy : cos (x + y) ≠ 0) : 1 - tan x * tan y ≠ 0 :=
  right_ne_zero_of_mul (cos_add_eq_mul_one_sub_tan_mul_tan hx hy ▸ hxy)

theorem one_add_tan_mul_tan_ne_zero {x y : ℝ} (hx : cos x ≠ 0) (hy : cos y ≠ 0)
    (hxy : cos (x - y) ≠ 0) : 1 + tan x * tan y ≠ 0 :=
  right_ne_zero_of_mul (cos_sub_eq_mul_one_add_tan_mul_tan hx hy ▸ hxy)

theorem one_sub_tan_sq_ne_zero {z : ℝ} (hz : cos z ≠ 0) (h : cos (2 * z) ≠ 0) :
    1 - tan z ^ 2 ≠ 0 := by
  rw [sq]
  exact one_sub_tan_mul_tan_ne_zero hz hz (two_mul z ▸ h)

/-! The rule below extends `checked_nonzero`: the denominators of the addition formulas for the
real tangent are nonzero where the tangent of the sum or difference is defined. -/

macro_rules | `(tactic| checked_nonzero) => `(tactic|
    solve
    | assumption
    | (apply Real.one_sub_tan_mul_tan_ne_zero <;> assumption)
    | (apply Real.one_add_tan_mul_tan_ne_zero <;> assumption)
    | (apply Real.one_sub_tan_sq_ne_zero <;> assumption))

-- tangent half-angle substitution formulas

theorem cos_half_ne_zero_of_cos_ne_neg_one {x : ℝ} (h : cos x ≠ -1) : cos (x / 2) ≠ 0 := by
  intro h0
  apply h
  rw [show x = 2 * (x / 2) by ring, cos_two_mul, h0]
  ring

theorem cos_eq_two_mul_tan_half_div_one_sub_tan_half_sq (x : ℝ) (h : cos x ≠ -1) :
    cos x = (1 - tan (x / 2) (cos_half_ne_zero_of_cos_ne_neg_one h) ^ 2) /
      (1 + tan (x / 2) (cos_half_ne_zero_of_cos_ne_neg_one h) ^ 2) := by
  have hc := cos_half_ne_zero_of_cos_ne_neg_one h
  rw [div_eq_mul_inv₀, inv_one_add_tan_sq hc]
  conv_lhs => rw [show x = 2 * (x / 2) by ring, cos_two_mul', ← tan_mul_cos hc]
  ring

theorem sin_eq_two_mul_tan_half_div_one_add_tan_half_sq (x : ℝ) (h : cos (x / 2) ≠ 0) :
    sin x = (2 * tan (x / 2)) / (1 + tan (x / 2) ^ 2) := by
  rw [div_eq_mul_inv₀, inv_one_add_tan_sq h]
  conv_lhs => rw [show x = 2 * (x / 2) by ring, sin_two_mul, ← tan_mul_cos h]
  ring

theorem sin_mul_sum_sin (n : ℕ) (a b : ℝ) :
    sin (a / 2) * ∑ i ∈ range n, sin (a * i + b) = sin (n * a / 2) * sin ((n - 1) * a / 2 + b) := by
  exact_mod_cast congr($(Complex.sin_mul_sum_sin n a b).re)

theorem sin_half_ne_zero_of_ne {a : ℝ} (h : ∀ k : ℤ, a ≠ k * (2 * π)) : sin (a / 2) ≠ 0 :=
  sin_ne_zero_iff.2 fun k hk ↦ h k <| by linarith

theorem sum_sin (n : ℕ) {a : ℝ} (h : ∀ k : ℤ, a ≠ k * (2 * π)) (b : ℝ) :
    ∑ i ∈ range n, sin (a * i + b) =
      Checked.div (sin (n * a / 2) * sin ((n - 1) * a / 2 + b)) (sin (a / 2))
        (sin_half_ne_zero_of_ne h).isUnit := by
  rw [eq_div_iff_mul_eq, mul_comm _ (sin (a / 2)), sin_mul_sum_sin]

theorem sin_mul_sum_cos (n : ℕ) (a b : ℝ) :
    sin (a / 2) * ∑ i ∈ range n, cos (a * i + b) = sin (n * a / 2) * cos ((n - 1) * a / 2 + b) := by
  exact_mod_cast congr($(Complex.sin_mul_sum_cos n a b).re)

theorem sum_cos (n : ℕ) {a : ℝ} (h : ∀ k : ℤ, a ≠ k * (2 * π)) (b : ℝ) :
    ∑ i ∈ range n, cos (a * i + b) =
      Checked.div (sin (n * a / 2) * cos ((n - 1) * a / 2 + b)) (sin (a / 2))
        (sin_half_ne_zero_of_ne h).isUnit := by
  rw [eq_div_iff_mul_eq, mul_comm _ (sin (a / 2)), sin_mul_sum_cos]

end Real
