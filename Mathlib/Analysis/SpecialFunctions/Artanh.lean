/-
Copyright (c) 2025 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuval Filmus
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Inverse of the tanh function

In this file we define an inverse of tanh on the open interval (-1, 1).

## Main definitions

- `Real.artanh`: An inverse function of `Real.tanh` as a function from ℝ to (-1, 1).

- `Real.tanhPartialEquiv`: `Real.tanh` and `Real.artanh` bundled as an equivalence
  from ℝ to the open interval (-1, 1).

## Main Results

- `Real.tanh_artanh`, `Real.artanh_tanh`: tanh and artanh are inverse in the appropriate domains.

- `Real.tanh_bijOn`, `Real.tanh_injective`, `Real.tanh_surjOn`: `Real.tanh` is
  bijective, injective and surjective as a function from ℝ to (-1, 1)

- `Real.artanh_bijOn`, `Real.artanh_injOn`, `Real.artanh_surjOn`: `Real.artanh` is bijective,
  injective and surjective as a function from (-1, 1) to ℝ

## Tags

artanh, arctanh, argtanh, atanh
-/

@[expose] public section


noncomputable section

open Function Set

open scoped Topology

namespace Real

variable {x y : ℝ}

/-- `artanh` is defined using a logarithm, `artanh x = log √((1 + x) / (1 - x))`. -/
@[pp_nodot]
def artanh (x : Ioo (-1 : ℝ) 1) : ℝ :=
  log √(Checked.div (1 + x.val) (1 - x.val) (sub_pos.mpr x.property.2).ne'.isUnit)

theorem artanh_eq_half_log (x : Ioo (-1 : ℝ) 1) :
    artanh x = 1 / 2 * log (Checked.div (1 + x.val) (1 - x.val)
      (sub_pos.mpr x.property.2).ne'.isUnit) := by
  have hn : 0 < 1 + x.val := by linarith [x.property.1]
  rw [artanh, log_sqrt (div_pos hn (sub_pos.mpr x.property.2)).le, one_div_mul_eq_div₀]

theorem exp_artanh (x : Ioo (-1 : ℝ) 1) :
    exp (artanh x) = √(Checked.div (1 + x.val) (1 - x.val) (sub_pos.mpr x.property.2).ne'.isUnit) :=
  exp_log <| sqrt_pos_of_pos <| div_pos (by linarith [x.property.1]) (sub_pos.mpr x.property.2)

@[simp]
theorem artanh_zero : artanh ⟨0, by constructor <;> norm_num⟩ = 0 := by norm_num [artanh]

private theorem exp_artanh_sq_mul (x : Ioo (-1 : ℝ) 1) :
    exp (artanh x) ^ 2 * (1 - x.val) = 1 + x.val := by
  rw [exp_artanh, sq_sqrt (div_pos (by linarith [x.property.1]) (sub_pos.mpr x.property.2)).le,
    div_mul_cancel₀]

/-- `artanh` is the right inverse of `tanh` over (-1, 1). -/
theorem tanh_artanh (x : Ioo (-1 : ℝ) 1) : tanh (artanh x) = x := by
  rw [tanh_eq, div_eq_iff]
  have hneg := exp_add (artanh x) (-artanh x)
  rw [add_neg_cancel, exp_zero] at hneg
  apply mul_right_cancel₀ (exp_pos (artanh x)).ne'
  nlinarith [exp_artanh_sq_mul x, hneg, congrArg (x.val * ·) hneg]

theorem cosh_artanh (x : Ioo (-1 : ℝ) 1) : cosh (artanh x) =
    Checked.div 1 √(1 - x.val ^ 2) (sqrt_pos.mpr
      (sub_pos.mpr ((sq_lt_one_iff_abs_lt_one _).mpr (abs_lt.mpr x.property)))).ne'.isUnit := by
  have h := tanh_artanh x
  rw [tanh_eq_sinh_div_cosh, div_eq_iff] at h
  have hid := cosh_sq_sub_sinh_sq (artanh x)
  rw [h] at hid
  apply eq_div_iff.mpr
  have hm : 0 ≤ cosh (artanh x) * √(1 - x.val ^ 2) := by positivity
  apply (sq_eq_sq₀ hm zero_le_one).mp
  rw [mul_pow, sq_sqrt (sub_nonneg.mpr
    ((sq_lt_one_iff_abs_lt_one _).mpr (abs_lt.mpr x.property)).le)]
  nlinarith only [hid]

theorem sinh_artanh (x : Ioo (-1 : ℝ) 1) : sinh (artanh x) =
    Checked.div x.val √(1 - x.val ^ 2) (sqrt_pos.mpr
      (sub_pos.mpr ((sq_lt_one_iff_abs_lt_one _).mpr (abs_lt.mpr x.property)))).ne'.isUnit := by
  have h := tanh_artanh x
  rw [tanh_eq_sinh_div_cosh, div_eq_iff, cosh_artanh] at h
  simpa only [mul_one_div₀] using h

/-- `artanh` is the left inverse of `tanh`. -/
theorem artanh_tanh (x : ℝ) : artanh ⟨tanh x, neg_one_lt_tanh x, tanh_lt_one x⟩ = x := by
  apply exp_injective
  apply (sq_eq_sq₀ (exp_pos _).le (exp_pos _).le).mp
  let y : Ioo (-1 : ℝ) 1 := ⟨tanh x, neg_one_lt_tanh x, tanh_lt_one x⟩
  have h := exp_artanh_sq_mul y
  change exp (artanh y) ^ 2 = exp x ^ 2
  apply mul_right_cancel₀ (sub_pos.mpr y.property.2).ne'
  rw [h]
  change 1 + tanh x = exp x ^ 2 * (1 - tanh x)
  rw [tanh_eq]
  have hneg := exp_add x (-x)
  rw [add_neg_cancel, exp_zero] at hneg
  field_simp
  nlinarith [hneg, congrArg (exp x ^ 2 * ·) hneg]

theorem strictMonoOn_one_add_div_one_sub :
    StrictMono (fun x : Ioo (-1 : ℝ) 1 ↦
      Checked.div (1 + x.val) (1 - x.val) (sub_pos.mpr x.property.2).ne'.isUnit) := by
  intro x y h
  rw [div_lt_div_iff₀ (sub_pos.mpr x.property.2) (sub_pos.mpr y.property.2)]
  linarith [show x.val < y.val from h]

theorem strictMonoOn_artanh : StrictMono artanh := by
  intro x y h
  apply log_lt_log (sqrt_pos_of_pos
    (div_pos (by linarith [x.property.1]) (sub_pos.mpr x.property.2)))
  apply sqrt_lt_sqrt (div_pos (by linarith [x.property.1]) (sub_pos.mpr x.property.2)).le
  exact strictMonoOn_one_add_div_one_sub h

theorem artanh_le_artanh_iff {x y : Ioo (-1 : ℝ) 1} : artanh x ≤ artanh y ↔ x ≤ y :=
  strictMonoOn_artanh.le_iff_le

theorem artanh_lt_artanh_iff {x y : Ioo (-1 : ℝ) 1} : artanh x < artanh y ↔ x < y :=
  strictMonoOn_artanh.lt_iff_lt

theorem artanh_le_artanh {x y : Ioo (-1 : ℝ) 1} (h : x ≤ y) : artanh x ≤ artanh y :=
  strictMonoOn_artanh.monotone h

theorem artanh_lt_artanh {x y : Ioo (-1 : ℝ) 1} (h : x < y) : artanh x < artanh y :=
  strictMonoOn_artanh h

theorem artanh_eq_zero_iff (x : Ioo (-1 : ℝ) 1) : artanh x = 0 ↔ x.val = 0 := by
  exact strictMonoOn_artanh.injective.eq_iff' artanh_zero |>.trans Subtype.ext_iff

theorem artanh_pos {x : Ioo (-1 : ℝ) 1} (hx : 0 < x.val) : 0 < artanh x :=
  artanh_zero ▸ artanh_lt_artanh hx

theorem artanh_neg {x : Ioo (-1 : ℝ) 1} (hx : x.val < 0) : artanh x < 0 :=
  artanh_zero ▸ artanh_lt_artanh hx

theorem artanh_nonneg {x : Ioo (-1 : ℝ) 1} (hx : 0 ≤ x.val) : 0 ≤ artanh x :=
  artanh_zero ▸ artanh_le_artanh hx

theorem artanh_nonpos {x : Ioo (-1 : ℝ) 1} (hx : x.val ≤ 0) : artanh x ≤ 0 :=
  artanh_zero ▸ artanh_le_artanh hx

/-- The hyperbolic tangent and its inverse on the open interval (-1, 1). -/
def tanhPartialEquiv : ℝ ≃ Ioo (-1 : ℝ) 1 where
  toFun x := ⟨tanh x, neg_one_lt_tanh x, tanh_lt_one x⟩
  invFun := artanh
  left_inv := artanh_tanh
  right_inv x := Subtype.ext (tanh_artanh x)

theorem tanh_bijOn : BijOn tanh univ (Ioo (-1) 1) := by
  refine ⟨fun x _ ↦ ⟨neg_one_lt_tanh x, tanh_lt_one x⟩, fun x _ y _ h ↦ ?_, fun x hx ↦ ?_⟩
  · exact tanhPartialEquiv.injective (Subtype.ext h)
  · exact ⟨artanh ⟨x, hx⟩, trivial, tanh_artanh ⟨x, hx⟩⟩

theorem tanh_injective : Injective tanh := fun _ _ h ↦ tanh_bijOn.injOn trivial trivial h

theorem tanh_surjOn : SurjOn tanh univ (Ioo (-1) 1) := tanh_bijOn.surjOn

theorem artanh_bijOn : BijOn artanh univ univ := tanhPartialEquiv.symm.bijective.bijOn_univ

theorem artanh_injOn : InjOn artanh univ := artanh_bijOn.injOn

theorem artanh_surjOn : SurjOn artanh univ univ := artanh_bijOn.surjOn

end Real
