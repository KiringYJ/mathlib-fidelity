/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Topology.Order.AtTopBotIxx

/-!
# The `arctan` function.

Inequalities, identities and `Real.tan` as a homeomorphism between `(-(π / 2), π / 2)`
and the whole line.

The result of `arctan x + arctan y` is given by `arctan_add`, `arctan_add_eq_add_pi` or
`arctan_add_eq_sub_pi` depending on whether `x * y < 1` and `0 < x`. As an application of
`arctan_add` we give four Machin-like formulas (linear combinations of arctangents equal to
`π / 4 = arctan 1`), including John Machin's original one at
`four_mul_arctan_inv_5_sub_arctan_inv_239`.
-/

@[expose] public section


noncomputable section

open Set Filter
open scoped Topology

namespace Real

variable {x y : ℝ}

/-- The addition formula for the tangent, where the tangents of `x`, `y` and `x + y` are
defined. -/
theorem tan_add (hx : cos x ≠ 0) (hy : cos y ≠ 0) {hxy : cos (x + y) ≠ 0} :
    tan (x + y) = (tan x + tan y) / (1 - tan x * tan y) := by
  rw [eq_div_iff_mul_eq]
  refine mul_right_cancel₀ (mul_ne_zero hx hy) ?_
  calc tan (x + y) * (1 - tan x * tan y) * (cos x * cos y) = tan (x + y) * cos (x + y) := by
        rw [cos_add_eq_mul_one_sub_tan_mul_tan hx hy]; ring
    _ = (tan x + tan y) * (cos x * cos y) := by
        rw [tan_mul_cos, sin_add, ← tan_mul_cos hx, ← tan_mul_cos hy]; ring

/-- The subtraction formula for the tangent, where the tangents of `x`, `y` and `x - y` are
defined. -/
theorem tan_sub (hx : cos x ≠ 0) (hy : cos y ≠ 0) {hxy : cos (x - y) ≠ 0} :
    tan (x - y) = (tan x - tan y) / (1 + tan x * tan y) := by
  rw [eq_div_iff_mul_eq]
  refine mul_right_cancel₀ (mul_ne_zero hx hy) ?_
  calc tan (x - y) * (1 + tan x * tan y) * (cos x * cos y) = tan (x - y) * cos (x - y) := by
        rw [cos_sub_eq_mul_one_add_tan_mul_tan hx hy]; ring
    _ = (tan x - tan y) * (cos x * cos y) := by
        rw [tan_mul_cos, sin_sub, ← tan_mul_cos hx, ← tan_mul_cos hy]; ring

theorem tan_two_mul {h : cos (2 * x) ≠ 0} (hx : cos x ≠ 0) :
    tan (2 * x) = 2 * tan x / (1 - tan x ^ 2) := by
  have := tan_add hx hx (hxy := two_mul x ▸ h)
  simp only [two_mul, sq] at this ⊢
  exact this

/-- The tangent is continuous on its domain. -/
@[continuity]
theorem continuous_tan : Continuous fun x : {x : ℝ // cos x ≠ 0} ↦ tan x x.2 :=
  (continuous_sin.comp continuous_subtype_val).div₀ (continuous_cos.comp continuous_subtype_val)
    (h₀ := fun x ↦ x.2.isUnit)

/-- The tangent is continuous on `(-(π / 2), π / 2)`, as a function on that interval. -/
theorem continuousOn_tan_Ioo :
    Continuous fun x : Ioo (-(π / 2)) (π / 2) ↦ tan x (cos_pos_of_mem_Ioo x.2).ne' :=
  continuous_tan.comp (continuous_subtype_val.subtype_mk fun x ↦ (cos_pos_of_mem_Ioo x.2).ne')

/-- The tangent maps `(-(π / 2), π / 2)` onto `ℝ`. -/
theorem surjOn_tan :
    Function.Surjective fun x : Ioo (-(π / 2)) (π / 2) ↦ tan x (cos_pos_of_mem_Ioo x.2).ne' := by
  intro y
  let r := √(1 + y ^ 2)
  have hr : 0 < r := Real.sqrt_pos.mpr (by positivity)
  have hr₂ : r ^ 2 = 1 + y ^ 2 := Real.sq_sqrt (by positivity)
  have hy : |y| < r := (sq_lt_sq₀ (abs_nonneg _) hr.le).mp (by rw [sq_abs, hr₂]; linarith)
  have hlt : |y / r| < 1 := by
    simpa only [abs_div, abs_of_pos hr] using (div_lt_one₀ hr).mpr hy
  obtain ⟨hy₁, hy₂⟩ := abs_lt.mp hlt
  let θ := arcsin (y / r)
  have hθ : θ ∈ Ioo (-(π / 2)) (π / 2) :=
    ⟨neg_pi_div_two_lt_arcsin.mpr hy₁, arcsin_lt_pi_div_two.mpr hy₂⟩
  have hs : sin θ * r = y := by
    rw [show sin θ = y / r from sin_arcsin hy₁.le hy₂.le, div_mul_cancel₀]
  have hc : cos θ * r = 1 := by
    apply (sq_eq_sq₀ (mul_nonneg (cos_pos_of_mem_Ioo hθ).le hr.le) zero_le_one).mp
    linear_combination r ^ 2 * sin_sq_add_cos_sq θ - (sin θ * r + y) * hs + hr₂
  refine ⟨⟨θ, hθ⟩, ?_⟩
  apply div_eq_iff.mpr
  apply mul_right_cancel₀ hr.ne'
  rw [hs, mul_assoc, hc, mul_one]

/-- The tangent of a point of its domain takes every real value. -/
theorem tan_surjective : Function.Surjective fun x : {x : ℝ // cos x ≠ 0} ↦ tan x x.2 :=
  fun y ↦
    let ⟨x, hx⟩ := surjOn_tan y
    ⟨⟨x, (cos_pos_of_mem_Ioo x.2).ne'⟩, hx⟩

theorem image_tan_Ioo :
    range (fun x : Ioo (-(π / 2)) (π / 2) ↦ tan x (cos_pos_of_mem_Ioo x.2).ne') = univ :=
  surjOn_tan.range_eq

/-- `Real.tan` as an `OrderIso` between `(-(π / 2), π / 2)` and `ℝ`. -/
def tanOrderIso : Ioo (-(π / 2)) (π / 2) ≃o ℝ :=
  StrictMono.orderIsoOfSurjective _ strictMonoOn_tan surjOn_tan

/-- Tangent is a homeomorphism from its principal interval onto the real line. -/
def tanHomeomorph : Ioo (-(π / 2)) (π / 2) ≃ₜ ℝ := tanOrderIso.toHomeomorph

@[simp] theorem tanHomeomorph_apply (x : Ioo (-(π / 2)) (π / 2)) :
    tanHomeomorph x = tan x (cos_pos_of_mem_Ioo x.2).ne' := rfl

/-- Inverse of the `tan` function, returns values in the range `-π / 2 < arctan x` and
`arctan x < π / 2` -/
@[pp_nodot]
noncomputable def arctan (x : ℝ) : ℝ :=
  tanOrderIso.symm x

@[simp] theorem coe_tanHomeomorph_symm_apply (x : ℝ) :
    (tanHomeomorph.symm x : ℝ) = arctan x := rfl

@[simp]
theorem tan_arctan (x : ℝ) {h : cos (arctan x) ≠ 0} : tan (arctan x) h = x :=
  tanOrderIso.apply_symm_apply x

theorem arctan_mem_Ioo (x : ℝ) : arctan x ∈ Ioo (-(π / 2)) (π / 2) :=
  Subtype.coe_prop _

@[simp]
theorem range_arctan : range arctan = Ioo (-(π / 2)) (π / 2) :=
  ((EquivLike.surjective _).range_comp _).trans Subtype.range_coe

theorem arctan_tan (hx₁ : -(π / 2) < x) (hx₂ : x < π / 2) :
    arctan (tan x (cos_pos_of_mem_Ioo ⟨hx₁, hx₂⟩).ne') = x :=
  Subtype.ext_iff.1 <| tanOrderIso.symm_apply_apply ⟨x, hx₁, hx₂⟩

theorem cos_arctan_pos (x : ℝ) : 0 < cos (arctan x) :=
  cos_pos_of_mem_Ioo <| arctan_mem_Ioo x

theorem sin_sq_arctan (x : ℝ) : sin (arctan x) ^ 2 = x ^ 2 / (1 + x ^ 2) := by
  rw [← tan_sq_div_one_add_tan_sq (cos_arctan_pos x).ne']
  simp only [tan_arctan]

theorem cos_sq_arctan (x : ℝ) : cos (arctan x) ^ 2 = 1 / (1 + x ^ 2) := by
  rw [one_div₀, ← inv_one_add_tan_sq (cos_arctan_pos x).ne']
  simp only [tan_arctan]

theorem sin_arctan (x : ℝ) : sin (arctan x) = x / √(1 + x ^ 2) := by
  rw [← tan_div_sqrt_one_add_tan_sq (cos_arctan_pos x)]
  simp only [tan_arctan]

theorem cos_arctan (x : ℝ) : cos (arctan x) = 1 / √(1 + x ^ 2) := by
  rw [one_div₀, ← inv_sqrt_one_add_tan_sq (cos_arctan_pos x)]
  simp only [tan_arctan]

theorem arctan_lt_pi_div_two (x : ℝ) : arctan x < π / 2 :=
  (arctan_mem_Ioo x).2

theorem neg_pi_div_two_lt_arctan (x : ℝ) : -(π / 2) < arctan x :=
  (arctan_mem_Ioo x).1

theorem arctan_eq_arcsin (x : ℝ) : arctan x = arcsin (x / √(1 + x ^ 2)) :=
  Eq.symm <| arcsin_eq_of_sin_eq (sin_arctan x) (mem_Icc_of_Ioo <| arctan_mem_Ioo x)

theorem arcsin_eq_arctan (h : x ∈ Ioo (-(1 : ℝ)) 1) :
    arcsin x = arctan (Checked.div x (√(1 - x ^ 2))
      (sqrt_pos.mpr (sub_pos.mpr ((sq_lt_one_iff_abs_lt_one x).mpr
        (abs_lt.mpr h)))).ne'.isUnit) := by
  have hcos : cos (arcsin x) ≠ 0 :=
    (cos_pos_of_mem_Ioo ⟨neg_pi_div_two_lt_arcsin.mpr h.1,
      arcsin_lt_pi_div_two.mpr h.2⟩).ne'
  rw [← tan_arcsin x (h := hcos)]
  exact (arctan_tan (neg_pi_div_two_lt_arcsin.mpr h.1)
    (arcsin_lt_pi_div_two.mpr h.2)).symm

@[simp]
theorem arctan_zero : arctan 0 = 0 := by simp [arctan_eq_arcsin]

@[gcongr, mono]
theorem arctan_strictMono : StrictMono arctan := tanOrderIso.symm.strictMono

@[gcongr]
theorem arctan_mono : Monotone arctan := arctan_strictMono.monotone

@[simp]
theorem arctan_lt_arctan_iff : arctan x < arctan y ↔ x < y := arctan_strictMono.lt_iff_lt

@[simp]
theorem arctan_le_arctan_iff : arctan x ≤ arctan y ↔ x ≤ y := arctan_strictMono.le_iff_le

theorem arctan_injective : arctan.Injective := arctan_strictMono.injective

@[simp]
theorem arctan_inj : arctan x = arctan y ↔ x = y := arctan_injective.eq_iff

@[simp]
theorem arctan_eq_zero_iff : arctan x = 0 ↔ x = 0 :=
  .trans (by rw [arctan_zero]) arctan_injective.eq_iff

theorem tendsto_arctan_atTop : Tendsto arctan atTop (𝓝[<] (π / 2)) :=
  tendsto_Ioo_atTop (by simp) |>.mp tanOrderIso.symm.tendsto_atTop

theorem tendsto_arctan_atBot : Tendsto arctan atBot (𝓝[>] (-(π / 2))) :=
  tendsto_Ioo_atBot (by simp) |>.mp tanOrderIso.symm.tendsto_atBot

theorem arctan_eq_of_tan_eq {hc : cos x ≠ 0} (h : tan x = y) (hx : x ∈ Ioo (-(π / 2)) (π / 2)) :
    arctan y = x :=
  congrArg Subtype.val <| @injOn_tan ⟨arctan y, arctan_mem_Ioo y⟩ ⟨x, hx⟩ <| by
    dsimp only
    rw [tan_arctan, ← h]

@[simp]
theorem arctan_one : arctan 1 = π / 4 :=
  arctan_eq_of_tan_eq tan_pi_div_four <| by constructor <;> linarith [pi_pos]

@[simp]
theorem arctan_sqrt_three : arctan (√3) = π / 3 := by
  rw [← tan_pi_div_three, arctan_tan]
  all_goals
  · field_simp
    nlinarith [pi_pos]

@[simp]
theorem arctan_inv_sqrt_three : arctan (√3)⁻¹ = π / 6 := by
  rw [inv_eq_one_div₀, ← tan_pi_div_six, arctan_tan]
  all_goals
  · field_simp
    nlinarith [pi_pos]

@[simp]
theorem arctan_eq_pi_div_four : arctan x = π / 4 ↔ x = 1 := arctan_injective.eq_iff' arctan_one

@[simp]
theorem arctan_neg (x : ℝ) : arctan (-x) = -arctan x := by simp [arctan_eq_arcsin, neg_div₀]

@[simp]
theorem arctan_eq_neg_pi_div_four : arctan x = -(π / 4) ↔ x = -1 :=
  arctan_injective.eq_iff' <| by rw [arctan_neg, arctan_one]

@[simp]
theorem arctan_pos : 0 < arctan x ↔ 0 < x := by
  simpa only [arctan_zero] using arctan_lt_arctan_iff (x := 0)

@[simp]
theorem arctan_lt_zero : arctan x < 0 ↔ x < 0 := by
  simpa only [arctan_zero] using arctan_lt_arctan_iff (y := 0)

@[simp]
theorem arctan_nonneg : 0 ≤ arctan x ↔ 0 ≤ x := by
  simpa only [arctan_zero] using arctan_le_arctan_iff (x := 0)

@[simp]
theorem arctan_le_zero : arctan x ≤ 0 ↔ x ≤ 0 := by
  simpa only [arctan_zero] using arctan_le_arctan_iff (y := 0)

theorem arctan_eq_arccos (h : 0 ≤ x) : arctan x = arccos (√(1 + x ^ 2))⁻¹ := by
  rw [arctan_eq_arcsin, arccos_eq_arcsin]; swap; · exact inv_nonneg.2 (sqrt_nonneg _)
  congr 1
  rw_mod_cast [← sqrt_inv, sq_sqrt, ← one_div₀, one_sub_div, add_sub_cancel_left, sqrt_div,
    sqrt_sq h]
  all_goals positivity

-- The junk values for `arccos` and `sqrt` make this true even for `1 < x`.
theorem arccos_eq_arctan (h : 0 < x) : arccos x = arctan (√(1 - x ^ 2) / x) := by
  rcases lt_or_ge x 1 with hx1 | hx1
  · rw [arccos, eq_comm]
    have hc : cos (arcsin x) ≠ 0 := by
      rw [cos_arcsin]
      exact (sqrt_pos.2 (by nlinarith)).ne'
    have hs : cos (π / 2 - arcsin x) ≠ 0 := by
      rw [cos_pi_div_two_sub, sin_arcsin (by linarith) hx1.le]
      exact h.ne'
    refine arctan_eq_of_tan_eq (hc := hs) ?_ ⟨?_, ?_⟩
    · rw [tan_pi_div_two_sub _ hc (h := hs)]
      simp only [tan_arcsin, inv_div₀]
    · linarith only [arcsin_le_pi_div_two x, pi_pos]
    · linarith only [arcsin_pos.2 h]
  · rw [arccos_of_one_le hx1, sqrt_eq_zero_of_nonpos (by nlinarith), zero_div, arctan_zero]

theorem arctan_inv_of_pos (h : 0 < x) : arctan x⁻¹ = π / 2 - arctan x := by
  have hlt : π / 2 - arctan x < π / 2 := by
    rw [sub_lt_self_iff, ← arctan_zero]
    exact tanOrderIso.symm.strictMono h
  have hgt : -(π / 2) < π / 2 - arctan x := by
    simpa using (arctan_lt_pi_div_two x).trans (half_lt_self_iff.mpr pi_pos)
  have hc : cos (π / 2 - arctan x) ≠ 0 := (cos_pos_of_mem_Ioo ⟨hgt, hlt⟩).ne'
  refine arctan_eq_of_tan_eq (hc := hc) ?_ ⟨hgt, hlt⟩
  rw [tan_pi_div_two_sub _ (cos_arctan_pos x).ne' (h := hc)]
  simp only [tan_arctan]

theorem arctan_inv_of_neg (h : x < 0) : arctan x⁻¹ = -(π / 2) - arctan x := by
  have := arctan_inv_of_pos (neg_pos.mpr h)
  rwa [inv_neg₀, arctan_neg, neg_eq_iff_eq_neg, neg_sub', arctan_neg, neg_neg] at this

section ArctanAdd

lemma arctan_ne_mul_pi_div_two : ∀ (k : ℤ), arctan x ≠ (2 * k + 1) * π / 2 := by
  by_contra! ⟨k, h⟩
  obtain ⟨lb, ub⟩ := arctan_mem_Ioo x
  rw [h, neg_eq_neg_one_mul, mul_div_assoc₀, mul_lt_mul_iff_left₀ (by positivity)] at lb
  rw [h, ← one_mul (π / 2), mul_div_assoc₀, mul_lt_mul_iff_left₀ (by positivity)] at ub
  norm_cast at lb ub; change -1 < _ at lb; lia

lemma arctan_add_arctan_lt_pi_div_two (h : x * y < 1) : arctan x + arctan y < π / 2 := by
  rcases le_or_gt y 0 with hy | hy
  · rw [← add_zero (π / 2), ← arctan_zero]
    exact add_lt_add_of_lt_of_le (arctan_lt_pi_div_two _) (tanOrderIso.symm.monotone hy)
  · rw [← lt_div_iff₀ hy, ← inv_eq_one_div₀] at h
    replace h : arctan x < arctan y⁻¹ := tanOrderIso.symm.strictMono h
    rwa [arctan_inv_of_pos hy, lt_tsub_iff_right] at h

theorem arctan_add (h : x * y < 1) :
    arctan x + arctan y = arctan ((x + y) / (1 - x * y)) := by
  have hlt := arctan_add_arctan_lt_pi_div_two h
  have hgt : -(π / 2) < arctan x + arctan y := by
    rw [neg_lt, neg_add, ← arctan_neg, ← arctan_neg]
    rw [← neg_mul_neg] at h
    exact arctan_add_arctan_lt_pi_div_two h
  have hxy : cos (arctan x + arctan y) ≠ 0 := (cos_pos_of_mem_Ioo ⟨hgt, hlt⟩).ne'
  refine (arctan_eq_of_tan_eq (hc := hxy) ?_ ⟨hgt, hlt⟩).symm
  rw [tan_add (cos_arctan_pos x).ne' (cos_arctan_pos y).ne' (hxy := hxy)]
  simp only [tan_arctan]

theorem arctan_add_eq_add_pi (h : 1 < x * y) (hx : 0 < x) :
    arctan x + arctan y = arctan ((x + y) / (1 - x * y)) + π := by
  have hy : 0 < y := by
    have := mul_pos_iff.mp (zero_lt_one.trans h)
    simpa [hx, hx.asymm]
  have hinv : x⁻¹ * y⁻¹ < 1 := by
    simpa only [mul_inv₀] using inv_lt_one_of_one_lt₀ h
  have hfrac : (x⁻¹ + y⁻¹) / (1 - x⁻¹ * y⁻¹) = -((x + y) / (1 - x * y)) := by
    field_simp
    ring
  have k := arctan_add hinv
  rw [arctan_inv_of_pos hx, arctan_inv_of_pos hy, hfrac, arctan_neg] at k
  linarith

theorem arctan_add_eq_sub_pi (h : 1 < x * y) (hx : x < 0) :
    arctan x + arctan y = arctan ((x + y) / (1 - x * y)) - π := by
  rw [← neg_mul_neg] at h
  have k := arctan_add_eq_add_pi h (neg_pos.mpr hx)
  rw [show _ / _ = -((x + y) / (1 - x * y)) by ring, ← neg_inj] at k
  simp only [arctan_neg, neg_add, neg_neg, ← sub_eq_add_neg _ π] at k
  exact k

theorem two_mul_arctan (h₁ : -1 < x) (h₂ : x < 1) :
    2 * arctan x = arctan (Checked.div (2 * x) (1 - x ^ 2)
      (sub_pos.mpr ((sq_lt_one_iff_abs_lt_one x).mpr (abs_lt.mpr ⟨h₁, h₂⟩))).ne'.isUnit) := by
  rw [two_mul, arctan_add (by nlinarith)]
  congr 1
  simp only [div_eq_mul_inv₀]
  ring

theorem two_mul_arctan_add_pi (h : 1 < x) :
    2 * arctan x = arctan (Checked.div (2 * x) (1 - x ^ 2)
      (show 1 - x ^ 2 ≠ 0 by nlinarith).isUnit) + π := by
  rw [two_mul, arctan_add_eq_add_pi (by nlinarith) (by linarith)]
  congr 2
  simp only [div_eq_mul_inv₀]
  ring

theorem two_mul_arctan_sub_pi (h : x < -1) :
    2 * arctan x = arctan (Checked.div (2 * x) (1 - x ^ 2)
      (show 1 - x ^ 2 ≠ 0 by nlinarith).isUnit) - π := by
  rw [two_mul, arctan_add_eq_sub_pi (by nlinarith) (by linarith)]
  congr 2
  simp only [div_eq_mul_inv₀]
  ring

theorem arctan_inv_2_add_arctan_inv_3 : arctan 2⁻¹ + arctan 3⁻¹ = π / 4 := by
  rw [arctan_add] <;> norm_num

theorem two_mul_arctan_inv_2_sub_arctan_inv_7 : 2 * arctan 2⁻¹ - arctan 7⁻¹ = π / 4 := by
  rw [two_mul_arctan, ← arctan_one, sub_eq_iff_eq_add, arctan_add] <;> norm_num

theorem two_mul_arctan_inv_3_add_arctan_inv_7 : 2 * arctan 3⁻¹ + arctan 7⁻¹ = π / 4 := by
  rw [two_mul_arctan, arctan_add] <;> norm_num

/-- **John Machin's 1706 formula**, which he used to compute π to 100 decimal places. -/
theorem four_mul_arctan_inv_5_sub_arctan_inv_239 : 4 * arctan 5⁻¹ - arctan 239⁻¹ = π / 4 := by
  rw [show 4 * arctan _ = 2 * (2 * _) by ring, two_mul_arctan, two_mul_arctan, ← arctan_one,
    sub_eq_iff_eq_add, arctan_add] <;> norm_num

end ArctanAdd

theorem sin_arctan_strictMono : StrictMono (sin <| arctan ·) := fun x y h ↦
  strictMonoOn_sin (Ioo_subset_Icc_self <| arctan_mem_Ioo x)
    (Ioo_subset_Icc_self <| arctan_mem_Ioo y) (arctan_strictMono h)

@[simp]
theorem sin_arctan_pos : 0 < sin (arctan x) ↔ 0 < x := by
  simpa using sin_arctan_strictMono.lt_iff_lt (a := 0)

@[simp]
theorem sin_arctan_lt_zero : sin (arctan x) < 0 ↔ x < 0 := by
  simpa using sin_arctan_strictMono.lt_iff_lt (b := 0)

@[simp]
theorem sin_arctan_eq_zero : sin (arctan x) = 0 ↔ x = 0 :=
  sin_arctan_strictMono.injective.eq_iff' <| by simp

@[simp]
theorem sin_arctan_nonneg : 0 ≤ sin (arctan x) ↔ 0 ≤ x := by
  simpa using sin_arctan_strictMono.le_iff_le (a := 0)

@[simp]
theorem sin_arctan_le_zero : sin (arctan x) ≤ 0 ↔ x ≤ 0 := by
  simpa using sin_arctan_strictMono.le_iff_le (b := 0)

@[continuity, fun_prop]
theorem continuous_arctan : Continuous arctan :=
  continuous_subtype_val.comp tanOrderIso.toHomeomorph.continuous_invFun

theorem continuousAt_arctan : ContinuousAt arctan x :=
  continuous_arctan.continuousAt

end Real

namespace Mathlib.Meta.Positivity
open Lean Qq

/-- Extension for `Real.arctan`. -/
@[positivity Real.arctan _]
meta def evalRealArctan : PositivityExt where eval {u α} z p e :=
  match p with | none => pure .none | some p => do
  match u, α, e with
  | 0, ~q(ℝ), ~q(Real.arctan $a) =>
    let ra ← core z p a
    match ra with
    | .positive pa =>
      assumeInstancesCommute
      return .positive q(Real.arctan_pos.mpr $pa)
    | .nonnegative na =>
      assumeInstancesCommute
      return .nonnegative q(Real.arctan_nonneg.mpr $na)
    | .nonzero na =>
      assumeInstancesCommute
      return .nonzero q(mt Real.arctan_eq_zero_iff.mp $na)
    | .none => return .none
  | _ => throwError "not Real.arctan"

/-- Extension for `Real.cos (Real.arctan _)`. -/
@[positivity Real.cos (Real.arctan _)]
meta def evalRealCosArctan : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℝ), ~q(Real.cos (Real.arctan $a)) =>
    assumeInstancesCommute
    return .positive q(Real.cos_arctan_pos _)
  | _ => throwError "not Real.cos (Real.arctan _)"

/-- Extension for `Real.sin (Real.arctan _)`. -/
@[positivity Real.sin (Real.arctan _)]
meta def evalRealSinArctan : PositivityExt where eval {u α} z p e :=
  match p with | none => pure .none | some p => do
  match u, α, e with
  | 0, ~q(ℝ), ~q(Real.sin (Real.arctan $a)) =>
    match ← core z p a with
    | .positive pa =>
      assumeInstancesCommute
      return .positive q(Real.sin_arctan_pos.mpr $pa)
    | .nonnegative na =>
      assumeInstancesCommute
      return .nonnegative q(Real.sin_arctan_nonneg.mpr $na)
    | .nonzero na =>
      assumeInstancesCommute
      return .nonzero q(mt Real.sin_arctan_eq_zero.mp $na)
    | .none => return .none
  | _ => throwError "not Real.sin (Real.arctan _)"

end Mathlib.Meta.Positivity
