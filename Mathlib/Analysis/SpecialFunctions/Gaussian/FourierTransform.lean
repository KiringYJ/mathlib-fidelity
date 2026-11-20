/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Analysis.Fourier.FourierTransform

/-!
# Fourier transform of the Gaussian

We prove that the Fourier transform of the Gaussian function is another Gaussian:

* `integral_cexp_quadratic`: general formula for `∫ (x : ℝ), exp (b * x ^ 2 + c * x + d)`
* `fourierIntegral_gaussian`: for all complex `b` and `t` with `0 < re b`, we have
  `∫ x:ℝ, exp (I * t * x) * exp (-b * x^2) = (π / b) ^ (1 / 2) * exp (-t ^ 2 / (4 * b))`.
* `fourierIntegral_gaussian_pi`: a variant with `b` and `t` scaled to give a more symmetric
  statement, and formulated in terms of the Fourier transform operator `𝓕`.

We also give versions of these formulas in finite-dimensional inner product spaces, see
`integral_cexp_neg_mul_sq_norm_add` and `fourierIntegral_gaussian_innerProductSpace`.

-/

@[expose] public section

/-!
## Fourier integral of Gaussian functions
-/

open Real Set MeasureTheory Filter intervalIntegral

open scoped Real Topology FourierTransform RealInnerProductSpace

open Complex hiding exp continuous_exp

noncomputable section

namespace GaussianFourier

variable {b : ℂ}

/-- The integral of the Gaussian function over the vertical edges of a rectangle
with vertices at `(±T, 0)` and `(±T, c)`. -/
def verticalIntegral (b : ℂ) (c T : ℝ) : ℂ :=
  ∫ y : ℝ in (0 : ℝ)..c, I * (cexp (-b * (T + y * I) ^ 2) - cexp (-b * (T - y * I) ^ 2))

/-- Explicit formula for the norm of the Gaussian function along the vertical
edges. -/
theorem norm_cexp_neg_mul_sq_add_mul_I (b : ℂ) (c T : ℝ) :
    ‖cexp (-b * (T + c * I) ^ 2)‖ = exp (-(b.re * T ^ 2 - 2 * b.im * c * T - b.re * c ^ 2)) := by
  rw [Complex.norm_exp, neg_mul, neg_re, ← re_add_im b]
  simp only [sq, re_add_im, mul_re, mul_im, add_re, add_im, ofReal_re, ofReal_im, I_re, I_im]
  ring_nf

theorem norm_cexp_neg_mul_sq_add_mul_I' (hb : b.re ≠ 0) (c T : ℝ) :
    ‖cexp (-b * (T + c * I) ^ 2)‖ =
      exp (-(b.re * (T - b.im * c / b.re) ^ 2 - c ^ 2 * (b.im ^ 2 / b.re + b.re))) := by
  have :
    b.re * T ^ 2 - 2 * b.im * c * T - b.re * c ^ 2 =
      b.re * (T - b.im * c / b.re) ^ 2 - c ^ 2 * (b.im ^ 2 / b.re + b.re) := by
    field
  rw [norm_cexp_neg_mul_sq_add_mul_I, this]

theorem verticalIntegral_norm_le (hb : 0 < b.re) (c : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ‖verticalIntegral b c T‖ ≤
      (2 : ℝ) * |c| * exp (-(b.re * T ^ 2 - (2 : ℝ) * |b.im| * |c| * T - b.re * c ^ 2)) := by
  -- first get uniform bound for integrand
  have vert_norm_bound :
    ∀ {T : ℝ},
      0 ≤ T →
        ∀ {c y : ℝ},
          |y| ≤ |c| →
            ‖cexp (-b * (T + y * I) ^ 2)‖ ≤
              exp (-(b.re * T ^ 2 - (2 : ℝ) * |b.im| * |c| * T - b.re * c ^ 2)) := by
    intro T hT c y hy
    rw [norm_cexp_neg_mul_sq_add_mul_I b]
    gcongr exp (-(_ - ?_ * _ - _ * ?_))
    · (conv_lhs => rw [mul_assoc]); (conv_rhs => rw [mul_assoc])
      gcongr _ * ?_
      refine (le_abs_self _).trans ?_
      rw [abs_mul]
      gcongr
    · rwa [sq_le_sq]
  -- now main proof
  apply (intervalIntegral.norm_integral_le_of_norm_le_const _).trans
  · rw [sub_zero]
    conv_lhs => simp only [mul_comm _ |c|]
    conv_rhs =>
      conv =>
        congr
        rw [mul_comm]
      rw [mul_assoc]
  · intro y hy
    have absy : |y| ≤ |c| := by
      simpa using abs_sub_left_of_mem_uIcc (uIoc_subset_uIcc hy)
    rw [norm_mul, norm_I, one_mul, two_mul]
    refine (norm_sub_le _ _).trans (add_le_add (vert_norm_bound hT absy) ?_)
    rw [← abs_neg y] at absy
    simpa only [neg_mul, ofReal_neg] using! vert_norm_bound hT absy

theorem tendsto_verticalIntegral (hb : 0 < b.re) (c : ℝ) :
    Tendsto (verticalIntegral b c) atTop (𝓝 0) := by
  -- complete proof using squeeze theorem:
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ?_
      (Eventually.of_forall fun _ => norm_nonneg _)
      ((eventually_ge_atTop (0 : ℝ)).mp
        (Eventually.of_forall fun T hT => verticalIntegral_norm_le hb c hT))
  rw [(by ring : 0 = 2 * |c| * 0)]
  refine (tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp ?_)).const_mul _
  apply tendsto_atTop_add_const_right
  simp_rw [sq, ← mul_assoc, ← sub_mul]
  refine Tendsto.atTop_mul_atTop₀ (tendsto_atTop_add_const_right _ _ ?_) tendsto_id
  exact (tendsto_const_mul_atTop_of_pos hb).mpr tendsto_id

theorem integrable_cexp_neg_mul_sq_add_real_mul_I (hb : 0 < b.re) (c : ℝ) :
    Integrable fun x : ℝ => cexp (-b * (x + c * I) ^ 2) := by
  refine ⟨by fun_prop, ?_⟩
  rw [← hasFiniteIntegral_norm_iff]
  simp_rw [norm_cexp_neg_mul_sq_add_mul_I' hb.ne', neg_sub _ (c ^ 2 * _),
    sub_eq_add_neg _ (b.re * _), Real.exp_add]
  suffices Integrable fun x : ℝ => exp (-(b.re * x ^ 2)) by
    exact (Integrable.comp_sub_right this (b.im * c / b.re)).hasFiniteIntegral.const_mul _
  simp_rw [← neg_mul]
  apply integrable_exp_neg_mul_sq hb

private lemma isUnit_four_mul_of_re_pos {b : ℂ} (hb : 0 < b.re) : IsUnit (4 * b) :=
  (show IsUnit (4 : ℂ) by checked_unit).mul (ne_zero_of_re_pos hb).isUnit

private lemma isUnit_of_re_neg {b : ℂ} (hb : b.re < 0) : IsUnit b :=
  (neg_ne_zero.1 (ne_zero_of_re_pos (s := -b) (by simpa only [neg_re] using neg_pos.2 hb))).isUnit

private lemma isUnit_cpow_half_of_re_pos {b : ℂ} (hb : 0 < b.re) : IsUnit (b ^ (1 / 2 : ℂ)) := by
  apply Ne.isUnit
  rw [Ne, cpow_eq_zero_iff, not_and_or]
  exact Or.inl (ne_zero_of_re_pos hb)

theorem integral_cexp_neg_mul_sq_add_real_mul_I (hb : 0 < b.re) (c : ℝ) :
    ∫ x : ℝ, cexp (-b * (x + c * I) ^ 2) =
      (Checked.div (π : ℂ) b (ne_zero_of_re_pos hb).isUnit) ^ (1 / 2 : ℂ) := by
  have hu := (ne_zero_of_re_pos hb).isUnit
  refine
    tendsto_nhds_unique
      (intervalIntegral_tendsto_integral (integrable_cexp_neg_mul_sq_add_real_mul_I hb c)
        tendsto_neg_atTop_atBot tendsto_id)
      ?_
  set I₁ := fun T => ∫ x : ℝ in -T..T, cexp (-b * (x + c * I) ^ 2) with HI₁
  let I₂ := fun T : ℝ => ∫ x : ℝ in -T..T, cexp (-b * (x : ℂ) ^ 2)
  let I₄ := fun T : ℝ => ∫ y : ℝ in (0 : ℝ)..c, cexp (-b * (T + y * I) ^ 2)
  let I₅ := fun T : ℝ => ∫ y : ℝ in (0 : ℝ)..c, cexp (-b * (-T + y * I) ^ 2)
  have C : ∀ T : ℝ, I₂ T - I₁ T + I * I₄ T - I * I₅ T = 0 := by
    intro T
    have :=
      integral_boundary_rect_eq_zero_of_differentiableOn (fun z => cexp (-b * z ^ 2)) (-T)
        (T + c * I)
        (by
          refine Differentiable.differentiableOn (Differentiable.const_mul ?_ _).cexp
          exact differentiable_pow 2)
    simpa only [neg_im, ofReal_im, neg_zero, ofReal_zero, zero_mul, add_zero, neg_re,
      ofReal_re, add_re, mul_re, I_re, mul_zero, I_im, tsub_zero, add_im, mul_im,
      mul_one, zero_add, smul_eq_mul, ofReal_neg] using this
  simp_rw [id, ← HI₁]
  have : I₁ = fun T : ℝ => I₂ T + verticalIntegral b c T := by
    ext1 T
    specialize C T
    rw [sub_eq_zero] at C
    unfold verticalIntegral
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub]
    · simp_rw [(fun a b => by rw [sq]; ring_nf : ∀ a b : ℂ, (a - b * I) ^ 2 = (-a + b * I) ^ 2)]
      change I₁ T = I₂ T + I * (I₄ T - I₅ T)
      rw [mul_sub, ← C]
      abel
    all_goals apply Continuous.intervalIntegrable; fun_prop
  rw [this, ← add_zero ((π / b : ℂ) ^ (1 / 2 : ℂ)), ← integral_gaussian_complex hb]
  refine Tendsto.add ?_ (tendsto_verticalIntegral hb c)
  exact
    intervalIntegral_tendsto_integral (integrable_cexp_neg_mul_sq hb) tendsto_neg_atTop_atBot
      tendsto_id

theorem _root_.integral_cexp_quadratic (hb : b.re < 0) (c d : ℂ) :
    ∫ x : ℝ,
      cexp (b * x ^ 2 + c * x + d) =
        (Checked.div (π : ℂ) (-b) (by exact (isUnit_of_re_neg hb).neg)) ^ (1 / 2 : ℂ) *
          cexp (d - Checked.div (c ^ 2) (4 * b)
            (by exact (show IsUnit (4 : ℂ) by checked_unit).mul (isUnit_of_re_neg hb))) := by
  have hu := isUnit_of_re_neg hb
  have hb' := hu.ne_zero
  have h (x : ℝ) : cexp (b * x ^ 2 + c * x + d) =
      cexp (- -b * (x + c / (2 * b)) ^ 2) * cexp (d - c ^ 2 / (4 * b)) := by
    simp_rw [← Complex.exp_add]
    congr 1
    field
  let w := c / (2 * b)
  let g (x : ℝ) := cexp (- -b * ((x : ℂ) + (w.im : ℂ) * I) ^ 2)
  have hw (x : ℝ) : cexp (- -b * ((x : ℂ) + c / (2 * b)) ^ 2) = g (x + w.re) := by
    change cexp (- -b * ((x : ℂ) + w) ^ 2) = g (x + w.re)
    simp only [g, ofReal_add, add_assoc, re_add_im]
  simp_rw [h, MeasureTheory.integral_mul_const, hw]
  rw [integral_add_right_eq_self g w.re]
  exact congrArg (fun z ↦ z * cexp (d - c ^ 2 / (4 * b)))
    (integral_cexp_neg_mul_sq_add_real_mul_I (b := -b) (by simpa only [neg_re] using neg_pos.2 hb)
      w.im)

lemma _root_.integrable_cexp_quadratic' (hb : b.re < 0) (c d : ℂ) :
    Integrable (fun (x : ℝ) ↦ cexp (b * x ^ 2 + c * x + d)) := by
  have hb' : b ≠ 0 := by contrapose! hb; rw [hb, zero_re]
  by_contra H
  simpa [hb', pi_ne_zero, Complex.exp_ne_zero, integral_undef H]
    using integral_cexp_quadratic hb c d

lemma _root_.integrable_cexp_quadratic (hb : 0 < b.re) (c d : ℂ) :
    Integrable (fun (x : ℝ) ↦ cexp (-b * x ^ 2 + c * x + d)) := by
  have : (-b).re < 0 := by simpa using hb
  exact integrable_cexp_quadratic' this c d

theorem _root_.fourierIntegral_gaussian (hb : 0 < b.re) (t : ℂ) :
    ∫ x : ℝ, cexp (I * t * x) * cexp (-b * x ^ 2) =
    (Checked.div (π : ℂ) b (ne_zero_of_re_pos hb).isUnit) ^ (1 / 2 : ℂ) *
      cexp (Checked.div (-t ^ 2) (4 * b) (by exact isUnit_four_mul_of_re_pos hb)) := by
  have hu := (ne_zero_of_re_pos hb).isUnit
  conv => enter [1, 2, x]; rw [← Complex.exp_add, add_comm, ← add_zero (-b * x ^ 2 + I * t * x)]
  rw [integral_cexp_quadratic (show (-b).re < 0 by rwa [neg_re, neg_lt_zero])]
  simp only [neg_neg, zero_sub, mul_neg, div_neg₀, mul_pow, I_sq, neg_one_mul, neg_div₀]

theorem _root_.fourier_gaussian_pi' (hb : 0 < b.re) (c : ℂ) :
    (𝓕 fun x : ℝ => cexp (-π * b * x ^ 2 + 2 * π * c * x)) = fun t : ℝ =>
    Checked.div 1 (b ^ (1 / 2 : ℂ)) (by exact isUnit_cpow_half_of_re_pos hb) *
      cexp (Checked.div (-π : ℂ) b (ne_zero_of_re_pos hb).isUnit * (t + I * c) ^ 2) := by
  have hu := (ne_zero_of_re_pos hb).isUnit
  have h : (-↑π * b).re < 0 := by
    simpa only [neg_mul, neg_re, re_ofReal_mul, neg_lt_zero] using mul_pos pi_pos hb
  ext1 t
  simp_rw [fourier_real_eq_integral_exp_smul, smul_eq_mul, ← Complex.exp_add, ← add_assoc]
  have (x : ℝ) : ↑(-2 * π * x * t) * I + -π * b * x ^ 2 + 2 * π * c * x =
    -π * b * x ^ 2 + (-2 * π * I * t + 2 * π * c) * x + 0 := by push_cast; ring
  simp_rw [this, integral_cexp_quadratic h, neg_mul, neg_neg]
  congr 2
  · have hp : IsUnit (π : ℂ) := (ofReal_ne_zero.mpr pi_ne_zero).isUnit
    have hquot : (π : ℂ) / ((π : ℂ) * b) = b⁻¹ :=
      div_mul_cancel_left₀ (hab := hp.mul hu)
    rw [hquot, one_div₀ (b ^ (1 / 2 : ℂ)), inv_cpow]
    rw [Ne, arg_eq_pi_iff, not_and_or, not_lt]
    exact Or.inl hb.le
  · field_simp
    ring_nf
    simp only [I_sq]
    ring

theorem _root_.fourier_gaussian_pi (hb : 0 < b.re) :
    (𝓕 fun (x : ℝ) ↦ cexp (-π * b * x ^ 2)) =
    fun t : ℝ ↦ Checked.div 1 (b ^ (1 / 2 : ℂ)) (by exact isUnit_cpow_half_of_re_pos hb) *
      cexp (Checked.div (-π : ℂ) b (ne_zero_of_re_pos hb).isUnit * t ^ 2) := by
  simpa only [mul_zero, zero_mul, add_zero] using fourier_gaussian_pi' hb 0

section InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [SigmaAlgebra V] [BorelSpace V]

theorem integrable_cexp_neg_sum_mul_add {ι : Type*} [Fintype ι] {b : ι → ℂ}
    (hb : ∀ i, 0 < (b i).re) (c : ι → ℂ) :
    Integrable (fun (v : ι → ℝ) ↦ cexp (-∑ i, b i * (v i : ℂ) ^ 2 + ∑ i, c i * v i)) := by
  simp_rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, Complex.exp_sum, ← neg_mul]
  apply Integrable.fintype_prod (f := fun i (v : ℝ) ↦ cexp (-b i * v ^ 2 + c i * v)) (fun i ↦ ?_)
  convert! integrable_cexp_quadratic (hb i) (c i) 0 using 3 with x
  simp only [add_zero]

theorem integrable_cexp_neg_mul_sum_add {ι : Type*} [Fintype ι] (hb : 0 < b.re) (c : ι → ℂ) :
    Integrable (fun (v : ι → ℝ) ↦ cexp (-b * ∑ i, (v i : ℂ) ^ 2 + ∑ i, c i * v i)) := by
  simp_rw [neg_mul, Finset.mul_sum]
  exact integrable_cexp_neg_sum_mul_add (fun _ ↦ hb) c

theorem integrable_cexp_neg_mul_sq_norm_add_of_euclideanSpace
    {ι : Type*} [Fintype ι] (hb : 0 < b.re) (c : ℂ) (w : EuclideanSpace ℝ ι) :
    Integrable (fun (v : EuclideanSpace ℝ ι) ↦ cexp (- b * ‖v‖ ^ 2 + c * ⟪w, v⟫)) := by
  rw [← (PiLp.volume_preserving_toLp ι).integrable_comp_emb
    (MeasurableEquiv.toLp 2 _).measurableEmbedding]
  simp only [neg_mul, Function.comp_def]
  convert! integrable_cexp_neg_mul_sum_add hb (fun i ↦ c * w i) using 3 with v
  simp only [EuclideanSpace.norm_eq, norm_eq_abs, sq_abs, PiLp.inner_apply, RCLike.inner_apply,
    conj_trivial, ofReal_sum, ofReal_mul, Finset.mul_sum, neg_mul, Finset.sum_neg_distrib,
    mul_assoc]
  norm_cast
  rw [sq_sqrt]
  · simp [Finset.mul_sum, mul_comm]
  · exact Finset.sum_nonneg (fun i _hi ↦ by positivity)

/-- In a real inner product space, the complex exponential of minus the square of the norm plus
a scalar product is integrable. Useful when discussing the Fourier transform of a Gaussian. -/
theorem integrable_cexp_neg_mul_sq_norm_add (hb : 0 < b.re) (c : ℂ) (w : V) :
    Integrable (fun (v : V) ↦ cexp (-b * ‖v‖ ^ 2 + c * ⟪w, v⟫)) := by
  let e := (stdOrthonormalBasis ℝ V).repr.symm
  rw [← e.measurePreserving.integrable_comp_emb e.toHomeomorph.measurableEmbedding]
  convert! integrable_cexp_neg_mul_sq_norm_add_of_euclideanSpace hb c (e.symm w) with v
  simp only [neg_mul, Function.comp_apply, LinearIsometryEquiv.norm_map,
    LinearIsometryEquiv.symm_symm,
    LinearIsometryEquiv.inner_map_eq_flip]

theorem integral_cexp_neg_sum_mul_add {ι : Type*} [Fintype ι] {b : ι → ℂ}
    (hb : ∀ i, 0 < (b i).re) (c : ι → ℂ) :
    ∫ v : ι → ℝ, cexp (-∑ i, b i * (v i : ℂ) ^ 2 + ∑ i, c i * v i)
      = ∏ i, (Checked.div (π : ℂ) (b i) (ne_zero_of_re_pos (hb i)).isUnit) ^ (1 / 2 : ℂ) *
        cexp (Checked.div (c i ^ 2) (4 * b i) (by exact isUnit_four_mul_of_re_pos (hb i))) := by
  simp_rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, Complex.exp_sum, ← neg_mul]
  rw [integral_fintype_prod_volume_eq_prod (f := fun i (v : ℝ) ↦ cexp (-b i * v ^ 2 + c i * v))]
  congr with i
  have : (-b i).re < 0 := by simpa using hb i
  convert! integral_cexp_quadratic this (c i) 0 using 1 <;> simp [div_neg₀]

theorem integral_cexp_neg_mul_sum_add {ι : Type*} [Fintype ι] (hb : 0 < b.re) (c : ι → ℂ) :
    ∫ v : ι → ℝ, cexp (-b * ∑ i, (v i : ℂ) ^ 2 + ∑ i, c i * v i)
      = (Checked.div (π : ℂ) b (ne_zero_of_re_pos hb).isUnit) ^ (Fintype.card ι / 2 : ℂ) *
        cexp (Checked.div (∑ i, c i ^ 2) (4 * b) (by exact isUnit_four_mul_of_re_pos hb)) := by
  simp_rw [neg_mul, Finset.mul_sum, integral_cexp_neg_sum_mul_add (fun _ ↦ hb) c, one_div₀,
    Finset.prod_mul_distrib, Finset.prod_const, ← cpow_nat_mul, ← Complex.exp_sum, Fintype.card,
    Finset.sum_div, div_eq_mul_inv₀]

theorem integral_cexp_neg_mul_sq_norm_add_of_euclideanSpace
    {ι : Type*} [Fintype ι] (hb : 0 < b.re) (c : ℂ) (w : EuclideanSpace ℝ ι) :
    ∫ v : EuclideanSpace ℝ ι, cexp (- b * ‖v‖ ^ 2 + c * ⟪w, v⟫) =
      (Checked.div (π : ℂ) b (ne_zero_of_re_pos hb).isUnit) ^ (Fintype.card ι / 2 : ℂ) *
        cexp (Checked.div (c ^ 2 * ‖w‖ ^ 2) (4 * b) (by exact isUnit_four_mul_of_re_pos hb)) := by
  rw [← (PiLp.volume_preserving_toLp ι).integral_comp
    (MeasurableEquiv.toLp 2 _).measurableEmbedding]
  simp only [neg_mul]
  convert! integral_cexp_neg_mul_sum_add hb (fun i ↦ c * w i) using 5 with _x y
  · simp only [EuclideanSpace.norm_eq, norm_eq_abs, sq_abs, neg_mul, neg_inj, mul_eq_mul_left_iff]
    norm_cast
    left
    rw [sq_sqrt]
    exact Finset.sum_nonneg (fun i _hi ↦ by positivity)
  · simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, ofReal_sum, ofReal_mul,
      Finset.mul_sum, mul_assoc]
    simp_rw [mul_comm]
  · simp only [EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs, mul_pow, ← Finset.mul_sum]
    congr
    norm_cast
    rw [sq_sqrt]
    exact Finset.sum_nonneg (fun i _hi ↦ by positivity)

theorem integral_cexp_neg_mul_sq_norm_add
    (hb : 0 < b.re) (c : ℂ) (w : V) :
    ∫ v : V, cexp (-b * ‖v‖ ^ 2 + c * ⟪w, v⟫) =
      (Checked.div (π : ℂ) b (ne_zero_of_re_pos hb).isUnit) ^ (Module.finrank ℝ V / 2 : ℂ) *
        cexp (Checked.div (c ^ 2 * ‖w‖ ^ 2) (4 * b) (by exact isUnit_four_mul_of_re_pos hb)) := by
  let e := (stdOrthonormalBasis ℝ V).repr.symm
  rw [← e.measurePreserving.integral_comp e.toHomeomorph.measurableEmbedding]
  convert! integral_cexp_neg_mul_sq_norm_add_of_euclideanSpace hb c (e.symm w) <;>
    simp [LinearIsometryEquiv.inner_map_eq_flip]

theorem integral_cexp_neg_mul_sq_norm (hb : 0 < b.re) :
    ∫ v : V, cexp (-b * ‖v‖ ^ 2) =
      (Checked.div (π : ℂ) b (ne_zero_of_re_pos hb).isUnit) ^ (Module.finrank ℝ V / 2 : ℂ) := by
  simpa using integral_cexp_neg_mul_sq_norm_add hb 0 (0 : V)

set_option backward.isDefEq.respectTransparency.types false in
theorem integral_rexp_neg_mul_sq_norm {b : ℝ} (hb : 0 < b) :
    ∫ v : V, rexp (-b * ‖v‖ ^ 2) = (π / b) ^ (Module.finrank ℝ V / 2 : ℝ) := by
  rw [← ofReal_inj]
  convert! integral_cexp_neg_mul_sq_norm (show 0 < (b : ℂ).re from hb) (V := V)
  · change ofRealLI (∫ (v : V), rexp (-b * ‖v‖ ^ 2)) = ∫ (v : V), cexp (-↑b * ↑‖v‖ ^ 2)
    rw [← ofRealLI.integral_comp_comm]
    simp [ofRealLI]
  · have hdiv₂ (x : ℝ) : (↑(x / 2) : ℂ) = (x : ℂ) / 2 := by
      simpa only [ofReal_ofNat] using ofReal_div x 2
    have hquot := @ofReal_div π b hb.ne'.isUnit
    simp only [ofReal_cpow (div_pos pi_pos hb).le, hdiv₂, hquot, ofReal_natCast]

theorem _root_.fourier_gaussian_innerProductSpace' (hb : 0 < b.re) (x w : V) :
    𝓕 (fun v ↦ cexp (-b * ‖v‖ ^ 2 + 2 * π * Complex.I * ⟪x, v⟫)) w =
      (Checked.div (π : ℂ) b (ne_zero_of_re_pos hb).isUnit) ^ (Module.finrank ℝ V / 2 : ℂ) *
        cexp (Checked.div (-(π : ℂ) ^ 2 * ‖x - w‖ ^ 2) b (ne_zero_of_re_pos hb).isUnit) := by
  simp only [neg_mul, fourier_eq', ofReal_neg, ofReal_mul, ofReal_ofNat,
    smul_eq_mul, ← Complex.exp_add, real_inner_comm w]
  convert! integral_cexp_neg_mul_sq_norm_add hb (2 * π * Complex.I) (x - w) using 3 with v
  · congr 1
    simp [inner_sub_left]
    ring
  · have : b ≠ 0 := by contrapose! hb; rw [hb, zero_re]
    simp [mul_pow]
    ring

theorem _root_.fourier_gaussian_innerProductSpace (hb : 0 < b.re) (w : V) :
    𝓕 (fun (v : V) ↦ cexp (-b * ‖v‖ ^ 2)) w =
      (Checked.div (π : ℂ) b (ne_zero_of_re_pos hb).isUnit) ^ (Module.finrank ℝ V / 2 : ℂ) *
        cexp (Checked.div (-(π : ℂ) ^ 2 * ‖w‖ ^ 2) b (ne_zero_of_re_pos hb).isUnit) := by
  simpa using fourier_gaussian_innerProductSpace' hb 0 w

end InnerProductSpace

end GaussianFourier
