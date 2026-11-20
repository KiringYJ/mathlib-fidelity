/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Calculus.Deriv.ZPow
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import Mathlib.Analysis.SpecialFunctions.NonIntegrable
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Integral over a circle in `ℂ`

In this file we define `∮ z in C(c, R), f z` to be the integral $\oint_{|z-c|=|R|} f(z)\,dz$ and
prove some properties of this integral. We give definition and prove most lemmas for a function
`f : ℂ → E`, where `E` is a complex Banach space. For this reason,
some lemmas use, e.g., `(z - c)⁻¹ • f z` instead of `f z / (z - c)`.

## Main definitions

* `CircleIntegrable f c R`: a function `f : ℂ → E` is integrable on the circle with center `c` and
  radius `R` if `f ∘ circleMap c R` is integrable on `[0, 2π]`;

* `circleIntegral f c R`: the integral $\oint_{|z-c|=|R|} f(z)\,dz$, defined as
  $\int_{0}^{2π}(c + Re^{θ i})' f(c+Re^{θ i})\,dθ$;

* `cauchyPowerSeries f c R`: the power series that is equal to
  $\sum_{n=0}^{\infty} \oint_{|z-c|=R} \left(\frac{w-c}{z - c}\right)^n \frac{1}{z-c}f(z)\,dz$ at
  `w - c`. The coefficients of this power series depend only on `f ∘ circleMap c R`, and the power
  series converges to `f w` if `f` is differentiable on the closed ball `Metric.closedBall c R`
  and `w` belongs to the corresponding open ball.

## Main statements

* `hasFPowerSeriesOn_cauchy_integral`: for any circle integrable function `f`, the power series
  `cauchyPowerSeries f c R`, `R > 0`, converges to the Cauchy integral
  `(2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • f z` on the open disc `Metric.ball c R`;

* `circleIntegral.integral_sub_zpow_of_undef`, `circleIntegral.integral_sub_zpow_of_ne`, and
  `circleIntegral.integral_sub_inv_of_mem_ball`: formulas for `∮ z in C(c, R), (z - w) ^ n`,
  `n : ℤ`. These lemmas cover the following cases:

  - `circleIntegral.integral_sub_zpow_of_undef`, `n < 0` and `|w - c| = |R|`: in this case the
    function is not integrable, so the integral is equal to its default value (zero);

  - `circleIntegral.integral_sub_zpow_of_ne`, `n ≠ -1`: in the cases not covered by the previous
    lemma, we have `(z - w) ^ n = ((z - w) ^ (n + 1) / (n + 1))'`, thus the integral equals zero;

  - `circleIntegral.integral_sub_inv_of_mem_ball`, `n = -1`, `|w - c| < R`: in this case the
    integral is equal to `2πi`.

  The case `n = -1`, `|w -c| > R` is not covered by these lemmas. While it is possible to construct
  an explicit primitive, it is easier to apply Cauchy theorem, so we postpone the proof till we have
  this theorem (see https://github.com/leanprover-community/mathlib4/pull/10000).

## Notation

- `∮ z in C(c, R), f z`: notation for the integral $\oint_{|z-c|=|R|} f(z)\,dz$, defined as
  $\int_{0}^{2π}(c + Re^{θ i})' f(c+Re^{θ i})\,dθ$.

## Tags

integral, circle, Cauchy integral
-/

@[expose] public section

variable {E : Type*} [NormedAddCommGroup E]

noncomputable section

open scoped Real NNReal Interval Pointwise Topology

open Complex MeasureTheory TopologicalSpace Metric Function Set Filter Asymptotics

/-!
### Facts about `circleMap`
-/

/-- The range of `circleMap c R` is the circle with center `c` and radius `|R|`. -/
@[simp]
theorem range_circleMap (c : ℂ) (R : ℝ) : range (circleMap c R) = sphere c |R| :=
  calc
    range (circleMap c R) = c +ᵥ R • range fun θ : ℝ => exp (θ * I) := by
      simp +unfoldPartialApp only [← image_vadd, ← image_smul, ← range_comp,
        vadd_eq_add, circleMap, comp_def, real_smul]
    _ = sphere c |R| := by
      rw [range_exp_mul_I, smul_sphere R 0 zero_le_one]
      simp

/-- The image of `(0, 2π]` under `circleMap c R` is the circle with center `c` and radius `|R|`. -/
@[simp]
theorem image_circleMap_Ioc (c : ℂ) (R : ℝ) : circleMap c R '' Ioc 0 (2 * π) = sphere c |R| := by
  rw [← range_circleMap, ← (periodic_circleMap c R).image_Ioc Real.two_pi_pos 0, zero_add]

theorem hasDerivAt_circleMap (c : ℂ) (R : ℝ) (θ : ℝ) :
    HasDerivAt (circleMap c R) (circleMap 0 R θ * I) θ := by
  simpa only [mul_assoc, one_mul, ofRealCLM_apply, circleMap, ofReal_one, zero_add]
    using! (((ofRealCLM.hasDerivAt (x := θ)).mul_const I).cexp.const_mul (R : ℂ)).const_add c

theorem differentiable_circleMap (c : ℂ) (R : ℝ) : Differentiable ℝ (circleMap c R) := fun θ =>
  (hasDerivAt_circleMap c R θ).differentiableAt

/-- The circleMap is real analytic. -/
@[fun_prop]
theorem analyticOnNhd_circleMap (c : ℂ) (R : ℝ) {u : Set ℝ} :
    AnalyticOnNhd ℝ (circleMap c R) u := by
  intro z hz
  apply analyticAt_const.add
  apply analyticAt_const.mul
  rw [← Function.comp_def]
  apply analyticAt_cexp.restrictScalars.comp ((ofRealCLM.analyticAt z).mul (by fun_prop))

/-- The circleMap is continuously differentiable. -/
theorem contDiff_circleMap (c : ℂ) (R : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (circleMap c R) :=
  (analyticOnNhd_circleMap c R).contDiff

@[continuity, fun_prop]
theorem continuous_circleMap (c : ℂ) (R : ℝ) : Continuous (circleMap c R) :=
  (differentiable_circleMap c R).continuous

@[fun_prop]
theorem measurable_circleMap (c : ℂ) (R : ℝ) : Measurable (circleMap c R) :=
  (continuous_circleMap c R).measurable

@[simp]
theorem deriv_circleMap (c : ℂ) (R : ℝ) (θ : ℝ) : deriv (circleMap c R) θ = circleMap 0 R θ * I :=
  (hasDerivAt_circleMap _ _ _).deriv

theorem deriv_circleMap_eq_zero_iff {c : ℂ} {R : ℝ} {θ : ℝ} :
    deriv (circleMap c R) θ = 0 ↔ R = 0 := by simp [I_ne_zero]

theorem deriv_circleMap_ne_zero {c : ℂ} {R : ℝ} {θ : ℝ} (hR : R ≠ 0) :
    deriv (circleMap c R) θ ≠ 0 :=
  mt deriv_circleMap_eq_zero_iff.1 hR

theorem lipschitzWith_circleMap (c : ℂ) (R : ℝ) : LipschitzWith (Real.nnabs R) (circleMap c R) :=
  lipschitzWith_of_nnnorm_deriv_le (differentiable_circleMap _ _) fun θ =>
    NNReal.coe_le_coe.1 <| by simp

theorem continuous_circleMap_inv {R : ℝ} {z w : ℂ} (hw : w ∈ ball z R) :
    Continuous (fun θ ↦ Checked.inv (circleMap z R θ - w)
      (sub_ne_zero.mpr (circleMap_ne_mem_ball hw θ)).isUnit) :=
  ((continuous_circleMap z R).sub continuous_const).fun_inv₀

theorem circleMap_preimage_codiscrete {c : ℂ} {R : ℝ} (hR : R ≠ 0) :
    map (circleMap c R) (codiscrete ℝ) ≤ codiscreteWithin (sphere c |R|) := by
  intro s hs
  apply (analyticOnNhd_circleMap c R).preimage_mem_codiscreteWithin
  · intro x hx
    by_contra hCon
    obtain ⟨a, ha⟩ := eventuallyConst_iff_exists_eventuallyEq.1 hCon
    exact deriv_circleMap_ne_zero (θ := x) hR (ha.deriv_eq.trans (deriv_const x a))
  · rwa [Set.image_univ, range_circleMap]

theorem circleMap_neg_radius {r x : ℝ} {c : ℂ} :
    circleMap c (-r) x = circleMap c r (x + π) := by
  simp [circleMap, add_mul, Complex.exp_add]

/-!
### Integrability of a function on a circle
-/

/-- We say that a function `f : ℂ → E` is integrable on the circle with center `c` and radius `R` if
the function `f ∘ circleMap c R` is integrable on `[0, 2π]`.

Note that the actual function used in the definition of `circleIntegral` is
`(deriv (circleMap c R) θ) • f (circleMap c R θ)`. Integrability of this function is equivalent
to integrability of `f ∘ circleMap c R` whenever `R ≠ 0`. -/
@[fun_prop]
def CircleIntegrable (f : ℂ → E) (c : ℂ) (R : ℝ) : Prop :=
  IntervalIntegrable (fun θ : ℝ ↦ f (circleMap c R θ)) volume 0 (2 * π)

/-- The angles in one turn of a circle whose images belong to the domain `s`. -/
def circleAngles (s : Set ℂ) (c : ℂ) (R : ℝ) : Set ℝ :=
  Icc 0 (2 * π) ∩ circleMap c R ⁻¹' s

/-- Integrability of a function on the part of a circle in its domain. -/
def CircleIntegrableOn {s : Set ℂ} (f : s → E) (c : ℂ) (R : ℝ) : Prop :=
  Integrable (fun θ : circleAngles s c R ↦ f ⟨circleMap c R θ.val, θ.2.2⟩)
    (volume.comap Subtype.val)

theorem measurableSet_circleAngles {s : Set ℂ} (hs : MeasurableSet s) (c : ℂ) (R : ℝ) :
    MeasurableSet (circleAngles s c R) :=
  measurableSet_Icc.inter (hs.preimage (measurable_circleMap c R))

theorem circleIntegrableOn_iff_integrableOn {s : Set ℂ} (hs : MeasurableSet s)
    (f : ℂ → E) (c : ℂ) (R : ℝ) :
    CircleIntegrableOn (fun z : s ↦ f z.val) c R ↔
      IntegrableOn (fun θ ↦ f (circleMap c R θ)) (circleAngles s c R) :=
  (integrableOn_iff_comap_subtypeVal (μ := volume) (f := fun θ : ℝ ↦ f (circleMap c R θ))
    (measurableSet_circleAngles hs c R)).symm

theorem circleIntegrable_def (f : ℂ → E) (c : ℂ) (R : ℝ) : CircleIntegrable f c R ↔
    IntervalIntegrable (fun θ : ℝ ↦ f (circleMap c R θ)) volume 0 (2 * π) := Iff.rfl

@[simp, fun_prop]
theorem circleIntegrable_const (a : E) (c : ℂ) (R : ℝ) : CircleIntegrable (fun _ => a) c R :=
  intervalIntegrable_const

@[fun_prop]
theorem circleIntegrable_id (c : ℂ) (R : ℝ) : CircleIntegrable (fun z => z) c R :=
  (continuous_circleMap c R).intervalIntegrable 0 (2 * π)

namespace CircleIntegrable

variable {f g : ℂ → E} {c : ℂ} {R : ℝ} {A : Type*} [NormedRing A] {a : A}

/--
Analogue of `IntervalIntegrable.abs`: If a real-valued function `f` is circle integrable, then so is
`|f|`.
-/
@[to_fun (attr := fun_prop)]
theorem abs {f : ℂ → ℝ} (hf : CircleIntegrable f c R) :
    CircleIntegrable |f| c R := IntervalIntegrable.abs hf

@[to_fun (attr := fun_prop)]
theorem add (hf : CircleIntegrable f c R) (hg : CircleIntegrable g c R) :
    CircleIntegrable (f + g) c R :=
  IntervalIntegrable.add hf hg

@[to_fun (attr := fun_prop)]
theorem sub (hf : CircleIntegrable f c R) (hg : CircleIntegrable g c R) :
    CircleIntegrable (f - g) c R :=
  IntervalIntegrable.sub hf hg

/-- Sums of circle integrable functions are circle integrable. -/
@[to_fun (attr := fun_prop)]
protected theorem sum {ι : Type*} (s : Finset ι) {f : ι → ℂ → E}
    (h : ∀ i ∈ s, CircleIntegrable (f i) c R) :
    CircleIntegrable (∑ i ∈ s, f i) c R := by
  rw [CircleIntegrable, (by aesop : (fun θ ↦ (∑ i ∈ s, f i) (circleMap c R θ))
    = ∑ i ∈ s, fun θ ↦ f i (circleMap c R θ))] at *
  exact IntervalIntegrable.sum s h

/-- `finsum`s of circle integrable functions are circle integrable. -/
@[fun_prop]
protected theorem finsum {ι : Type*} {f : ι → ℂ → E} (h : ∀ i, CircleIntegrable (f i) c R) :
    CircleIntegrable (∑ᶠ i, f i) c R := by
  by_cases h₁ : (Function.support f).Finite
  · rw [finsum_eq_sum f h₁]
    exact CircleIntegrable.sum h₁.toFinset (fun i _ ↦ h i)
  · rw [finsum_of_infinite_support h₁]
    apply circleIntegrable_const

@[to_fun (attr := fun_prop)]
nonrec theorem neg (hf : CircleIntegrable f c R) : CircleIntegrable (-f) c R :=
  hf.neg

/-- If `f` is circle integrable, then so are its scalar multiples. -/
@[to_fun (attr := fun_prop) const_fun_smul]
theorem const_smul {f : ℂ → A} (h : CircleIntegrable f c R) : CircleIntegrable (a • f) c R :=
  IntervalIntegrable.const_mul h _

variable
  {𝕜 F : Type*} [NormedRing 𝕜] [NormedAddCommGroup F] [Module 𝕜 F] [NormSMulClass 𝕜 F]

/--
If `g` is continuous on the circle `sphere c |R|` and `f` is circle integrable, then `g • f` is
circle integrable.
-/
@[to_fun (attr := fun_prop)]
theorem continuousOn_smul {f : ℂ → F} {g : ℂ → 𝕜} (hf : CircleIntegrable f c R)
    (hg : ContinuousOn g (sphere c |R|)) :
    CircleIntegrable (g • f) c R :=
  IntervalIntegrable.continuousOn_smul hf
    (hg.comp (by fun_prop) (fun x hx ↦ circleMap_mem_sphere' c R x))

/--
If `f` is circle integrable and `g` is continuous on the circle `sphere c |R|`, then `f • g` is
circle integrable.
-/
@[to_fun (attr := fun_prop)]
theorem smul_continuousOn {f : ℂ → 𝕜} {g : ℂ → F} (hf : CircleIntegrable f c R)
    (hg : ContinuousOn g (sphere c |R|)) :
    CircleIntegrable (f • g) c R :=
  IntervalIntegrable.smul_continuousOn hf
    (hg.comp (by fun_prop) (fun x hx ↦ circleMap_mem_sphere' c R x))

/--
If `g` is continuous on the circle `sphere c |R|` and `f` is circle integrable, then `g * f` is
circle integrable.
-/
@[to_fun (attr := fun_prop)]
theorem continuousOn_mul {f g : ℂ → 𝕜} (hf : CircleIntegrable f c R)
    (hg : ContinuousOn g (sphere c |R|)) :
    CircleIntegrable (g * f) c R :=
  IntervalIntegrable.continuousOn_mul hf
    (hg.comp (by fun_prop) (fun x hx ↦ circleMap_mem_sphere' c R x))

/--
If `f` is circle integrable and `g` is continuous on the circle `sphere c |R|`, then `f * g` is
circle integrable.
-/
@[to_fun (attr := fun_prop)]
theorem mul_continuousOn {f g : ℂ → 𝕜} (hf : CircleIntegrable f c R)
    (hg : ContinuousOn g (sphere c |R|)) :
    CircleIntegrable (f * g) c R :=
  IntervalIntegrable.mul_continuousOn hf
    (hg.comp (by fun_prop) (fun x hx ↦ circleMap_mem_sphere' c R x))

@[deprecated (since := "2026-07-01")] alias smul_of_continuousOn := continuousOn_smul
@[deprecated (since := "2026-07-01")] alias mul_of_continuousOn := continuousOn_mul
@[deprecated (since := "2026-07-01")] alias fun_smul_of_continuousOn := fun_continuousOn_smul
@[deprecated (since := "2026-07-01")] alias fun_mul_of_continuousOn := fun_continuousOn_mul

/-- The function we actually integrate over `[0, 2π]` in the definition of `circleIntegral` is
integrable. -/
theorem out [NormedSpace ℂ E] (hf : CircleIntegrable f c R) :
    IntervalIntegrable (fun θ : ℝ => deriv (circleMap c R) θ • f (circleMap c R θ)) volume 0
      (2 * π) := by
  simp only [CircleIntegrable, deriv_circleMap, intervalIntegrable_iff] at *
  refine (hf.norm.const_mul |R|).mono' ?_ ?_
  · exact ((continuous_circleMap _ _).aestronglyMeasurable.mul_const I).smul hf.aestronglyMeasurable
  · simp [norm_smul]

end CircleIntegrable

@[simp]
theorem circleIntegrable_zero_radius {f : ℂ → E} {c : ℂ} : CircleIntegrable f c 0 := by
  simp [CircleIntegrable]

/--
Circle integrability depends only on the restriction of the function to the sphere.
-/
theorem circleIntegrable_congr {c : ℂ} {R : ℝ} {f₁ f₂ : ℂ → E}
    (hf : Set.EqOn f₁ f₂ (sphere c |R|)) :
    CircleIntegrable f₁ c R ↔ CircleIntegrable f₂ c R :=
  intervalIntegrable_congr fun x _ ↦ hf (circleMap_mem_sphere' c R x)

@[deprecated (since := "2026-04-26")] alias crcleIntegrable_congr := circleIntegrable_congr

/--
Circle integrability is invariant when taking negative radius.
-/
@[simp] theorem circleIntegrable_neg_radius {c : ℂ} {R : ℝ} {f : ℂ → E} :
    CircleIntegrable f c (-R) ↔ CircleIntegrable f c R := by
  unfold CircleIntegrable
  rw [intervalIntegrable_congr (f := fun θ ↦ f (circleMap c (-R) θ))
    (g := fun θ ↦ (f ∘ (circleMap c R)) (θ + π)) (fun _ _ ↦ by simp [circleMap_neg_radius]),
    IntervalIntegrable.comp_add_right_iff (c := π), add_comm (2 * π) π]
  simpa using! ((periodic_circleMap c R).comp f).intervalIntegrable_iff (t₂ := 0)

/-- Circle integrability is invariant when functions change along discrete sets. -/
theorem CircleIntegrable.congr_codiscreteWithin {c : ℂ} {R : ℝ} {f₁ f₂ : ℂ → E}
    (hf : f₁ =ᶠ[codiscreteWithin (sphere c |R|)] f₂) (hf₁ : CircleIntegrable f₁ c R) :
    CircleIntegrable f₂ c R := by
  by_cases hR : R = 0
  · simp [hR]
  apply (intervalIntegrable_congr_codiscreteWithin _).1 hf₁
  rw [eventuallyEq_iff_exists_mem]
  exact ⟨(circleMap c R)⁻¹' {z | f₁ z = f₂ z},
    codiscreteWithin_mono (by simp only [Set.subset_univ]) (circleMap_preimage_codiscrete hR hf),
    by tauto⟩

/-- Circle integrability is invariant when functions change along discrete sets. -/
theorem circleIntegrable_congr_codiscreteWithin {c : ℂ} {R : ℝ} {f₁ f₂ : ℂ → E}
    (hf : f₁ =ᶠ[codiscreteWithin (sphere c |R|)] f₂) :
    CircleIntegrable f₁ c R ↔ CircleIntegrable f₂ c R :=
  ⟨(CircleIntegrable.congr_codiscreteWithin hf ·),
    (CircleIntegrable.congr_codiscreteWithin hf.symm ·)⟩

theorem circleIntegrable_iff [NormedSpace ℂ E] {f : ℂ → E} {c : ℂ} (R : ℝ) :
    CircleIntegrable f c R ↔ IntervalIntegrable (fun θ : ℝ =>
      deriv (circleMap c R) θ • f (circleMap c R θ)) volume 0 (2 * π) := by
  by_cases h₀ : R = 0
  · rw [h₀]
    simp only [deriv_circleMap]
    simp [circleMap]
  refine ⟨fun h => h.out, fun h => ?_⟩
  simp only [CircleIntegrable, intervalIntegrable_iff, deriv_circleMap] at h ⊢
  refine (h.norm.const_mul |R|⁻¹).mono' ?_ ?_
  · have H (θ : ℝ) : IsUnit (circleMap 0 R θ * I) :=
      (show circleMap 0 R θ * I ≠ 0 by simp [h₀, I_ne_zero]).isUnit
    have hc : Continuous (fun θ ↦ Checked.inv (circleMap 0 R θ * I) (H θ)) :=
      ((continuous_circleMap 0 R).mul continuous_const).fun_inv₀
    simpa only [inv_smul_smul₀] using
      hc.aestronglyMeasurable.fun_smul h.aestronglyMeasurable
  · simp [norm_smul]

@[fun_prop]
theorem ContinuousOn.circleIntegrable' {f : ℂ → E} {c : ℂ} {R : ℝ}
    (hf : ContinuousOn f (sphere c |R|)) : CircleIntegrable f c R :=
  (hf.comp_continuous (continuous_circleMap _ _) (circleMap_mem_sphere' _ _)).intervalIntegrable _ _

theorem ContinuousOn.circleIntegrable {f : ℂ → E} {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hf : ContinuousOn f (sphere c R)) : CircleIntegrable f c R :=
  ContinuousOn.circleIntegrable' <| (abs_of_nonneg hR).symm ▸ hf

/-- The function `fun z ↦ (z - w) ^ n`, `n : ℤ`, is circle integrable on the circle with center `c`
and radius `|R|` if and only if `R = 0` or `0 ≤ n`, or `w` does not belong to this circle. -/
@[simp]
theorem circleIntegrable_sub_zpow_iff {c w : ℂ} {R : ℝ} {n : ℤ} :
    CircleIntegrableOn (fun z : {z : ℂ | n < 0 → z ≠ w} ↦
      Checked.zpow (z.val - w) n (fun hn ↦ (sub_ne_zero.mpr (z.2 hn)).isUnit)) c R ↔
        R = 0 ∨ 0 ≤ n ∨ w ∉ sphere c |R| := by
  let S : Set ℂ := {z | n < 0 → z ≠ w}
  let g : S → ℂ := fun z ↦ Checked.zpow (z.val - w) n
    fun hn ↦ (sub_ne_zero.mpr (z.2 hn)).isUnit
  let G : ℂ → ℂ := Function.extend Subtype.val g 0
  have hG (z : S) : G z.val = g z := Subtype.val_injective.extend_apply _ _ _
  have hg : Continuous g := (continuous_subtype_val.sub continuous_const).zpow₀ n
  have hS : MeasurableSet S := by
    by_cases hn : n < 0
    · have hset : S = {w}ᶜ := by ext z; simp [S, hn]
      rw [hset]
      exact (measurableSet_singleton w).compl
    · simp [S, hn]
  have hparam := measurableSet_circleAngles hS c R
  change CircleIntegrableOn g c R ↔ _
  have hiff : CircleIntegrableOn g c R ↔
      IntegrableOn (G ∘ circleMap c R) (circleAngles S c R) := by
    rw [integrableOn_iff_comap_subtypeVal hparam]
    exact integrable_congr (Eventually.of_forall fun θ ↦
      (hG ⟨circleMap c R θ.val, θ.2.2⟩).symm)
  rw [hiff]
  constructor
  · intro hint
    by_contra! h
    obtain ⟨hR, hn, hw⟩ := h
    have hparams : circleAngles S c R =ᵐ[volume] Icc 0 (2 * π) := by
      have hcount : (circleMap c R ⁻¹' {w}).Countable :=
        (countable_singleton _).preimage_circleMap c hR
      filter_upwards [hcount.ae_notMem volume] with θ hθ
      have hθ' : circleMap c R θ ≠ w := hθ
      simp [circleAngles, S, hθ']
    have hint' : IntervalIntegrable (G ∘ circleMap c R) volume 0 (2 * π) := by
      rwa [intervalIntegrable_iff_integrableOn_Icc_of_le Real.two_pi_pos.le, IntegrableOn,
        ← Measure.restrict_congr_set hparams]
    rw [← image_circleMap_Ioc] at hw
    obtain ⟨θ, hθ, hw⟩ := hw
    replace hθ : θ ∈ [[0, 2 * π]] := Icc_subset_uIcc (Ioc_subset_Icc_self hθ)
    refine not_intervalIntegrable_of_sub_inv_isBigO_punctured ?_ Real.two_pi_pos.ne hθ hint'
    let f : ℝ → ℂ := fun θ' ↦ circleMap c R θ' - w
    have hf : ∀ᶠ θ' in 𝓝[≠] θ, f θ' ∈ ball (0 : ℂ) 1 \ {0} := by
      suffices ∀ᶠ z in 𝓝[≠] circleMap c R θ, z - circleMap c R θ ∈ ball (0 : ℂ) 1 \ {0} from
        by simpa only [f, hw] using
          ((differentiable_circleMap c R θ).hasDerivAt.tendsto_nhdsNE
            (deriv_circleMap_ne_zero hR)).eventually this
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds _ zero_lt_one)]
      simp_all [dist_eq, sub_eq_zero]
    obtain ⟨C, hC₀, hC⟩ := ((hasDerivAt_circleMap c R θ).isBigO_sub.mono inf_le_left).exists_pos
    have hval : Tendsto (Subtype.val : {t : ℝ // t ≠ θ} → ℝ)
        (comap Subtype.val (𝓝[≠] θ)) (𝓝[≠] θ) := tendsto_comap
    refine IsBigO.of_bound C ?_
    filter_upwards [hval.eventually hf, hval.eventually hC.bound] with t ht hbound
    have ht0 : 0 < ‖f t.val‖ := norm_pos_iff.mpr ht.2
    have ht1 : ‖f t.val‖ < 1 := by simpa [mem_ball, dist_zero_right] using ht.1
    have htw : circleMap c R t.val ≠ w := sub_ne_zero.mp ht.2
    have htθ : IsUnit ‖t.val - θ‖ := (norm_ne_zero_iff.mpr (sub_ne_zero.mpr t.2)).isUnit
    have hrec : Checked.inv ‖t.val - θ‖ htθ ≤ C / ‖f t.val‖ := by
      rw [le_div_iff₀ ht0]
      have hbound' : ‖f t.val‖ ≤ C * ‖t.val - θ‖ := by
        simpa only [f, hw, id_eq] using hbound
      calc
        _ ≤ Checked.inv ‖t.val - θ‖ htθ * (C * ‖t.val - θ‖) :=
          mul_le_mul_of_nonneg_left hbound' (inv_nonneg.mpr (norm_nonneg _))
        _ = C := by rw [mul_left_comm, inv_mul_cancel₀, mul_one]
    have hpow : (‖f t.val‖ ^ (-1 : ℤ)) ≤ ‖f t.val‖ ^ n :=
      (zpow_right_strictAnti₀ ht0 ht1).antitone (by omega)
    simp only [Function.comp_apply, hG ⟨circleMap c R t.val, fun _ ↦ htw⟩, g, norm_inv, norm_zpow]
    exact hrec.trans <| by
      simpa only [div_eq_mul_inv₀, zpow_neg_one₀] using mul_le_mul_of_nonneg_left hpow hC₀.le
  · intro H
    suffices IntervalIntegrable (G ∘ circleMap c R) volume 0 (2 * π) from
      ((intervalIntegrable_iff_integrableOn_Icc_of_le Real.two_pi_pos.le).mp this).mono_set
        inter_subset_left
    rcases H with rfl | H
    · simp [Function.comp_def]
    have hmap (θ : ℝ) : circleMap c R θ ∈ S := fun hn ↦
      ne_of_mem_of_not_mem (circleMap_mem_sphere' c R θ) (H.resolve_left hn.not_ge)
    let j (θ : ℝ) : S := ⟨circleMap c R θ, hmap θ⟩
    have hj : Continuous j := (continuous_circleMap c R).subtype_mk hmap
    simpa only [show (g ∘ j) = G ∘ circleMap c R from
      funext fun θ ↦ (hG (j θ)).symm] using (hg.comp hj).intervalIntegrable 0 (2 * π)

@[simp]
theorem circleIntegrable_sub_inv_iff {c w : ℂ} {R : ℝ} :
    CircleIntegrableOn (fun z : ({w}ᶜ : Set ℂ) ↦
      Checked.inv (z.val - w) (sub_ne_zero.mpr z.2).isUnit) c R ↔
        R = 0 ∨ w ∉ sphere c |R| := by
  let S : Set ℂ := {z | (-1 : ℤ) < 0 → z ≠ w}
  have hset : S = {w}ᶜ := by ext z; simp [S]
  have hmeas : MeasurableSet ({w}ᶜ : Set ℂ) := (measurableSet_singleton w).compl
  let g (z : ({w}ᶜ : Set ℂ)) := Checked.inv (z.val - w) (sub_ne_zero.mpr z.2).isUnit
  let G : ℂ → ℂ := Function.extend Subtype.val g 0
  have hG (z : ({w}ᶜ : Set ℂ)) : G z.val = g z := Subtype.val_injective.extend_apply _ _ _
  have hpow : (fun z : S ↦
      Checked.zpow (z.val - w) (-1) (fun hn ↦ (sub_ne_zero.mpr (z.2 hn)).isUnit)) =
      fun z : S ↦ G z.val := by
    funext z
    simpa only [g, zpow_neg_one₀] using (hG ⟨z.val, z.2 (by decide)⟩).symm
  have h := circleIntegrable_sub_zpow_iff (c := c) (w := w) (R := R) (n := -1)
  change CircleIntegrableOn (fun z : S ↦
    Checked.zpow (z.val - w) (-1) (fun hn ↦ (sub_ne_zero.mpr (z.2 hn)).isUnit)) c R ↔ _ at h
  rw [hpow, circleIntegrableOn_iff_integrableOn (hset.symm ▸ hmeas) G c R, hset] at h
  change CircleIntegrableOn g c R ↔ _
  rw [← funext hG, circleIntegrableOn_iff_integrableOn hmeas G c R]
  simpa only [show ¬ (0 : ℤ) ≤ -1 by decide, false_or] using h

variable [NormedSpace ℂ E]

/-- If `f` is circle integrable and `w` does not lie on the circle, then
`fun z ↦ (z - w) ^ n • f z` is circle integrable for every `n : ℤ`. -/
theorem CircleIntegrable.sub_zpow_smul {f : ℂ → E} {c w : ℂ} {R : ℝ} (n : ℤ)
    (hf : CircleIntegrable f c R) (hw : w ∉ sphere c |R|) :
    CircleIntegrableOn (fun z : {z : ℂ | n < 0 → z ≠ w} ↦
      Checked.zpow (z.val - w) n (fun hn ↦ (sub_ne_zero.mpr (z.2 hn)).isUnit) • f z.val) c R := by
  have hmap (θ : ℝ) : circleMap c R θ ≠ w :=
    ne_of_mem_of_not_mem (circleMap_mem_sphere' _ _ _) hw
  let g (θ : ℝ) := Checked.zpow (circleMap c R θ - w) n
    (fun _ ↦ (sub_ne_zero.mpr (hmap θ)).isUnit) • f (circleMap c R θ)
  have hg : IntervalIntegrable g volume 0 (2 * π) :=
    ((circleIntegrable_def _ _ _).mp hf).continuousOn_smul <|
      ((continuous_circleMap _ _).sub continuous_const).continuousOn.zpow₀ n
  have hset : circleAngles {z : ℂ | n < 0 → z ≠ w} c R = Icc 0 (2 * π) := by
    ext θ
    simp [circleAngles, hmap]
  exact (integrableOn_iff_comap_subtypeVal (hset.symm ▸ measurableSet_Icc)).mp
    (hset.symm ▸ (intervalIntegrable_iff_integrableOn_Icc_of_le Real.two_pi_pos.le).mp hg)

/-- Definition for $\oint_{|z-c|=R} f(z)\,dz$ -/
def circleIntegral (f : ℂ → E) (c : ℂ) (R : ℝ) : E :=
  ∫ θ : ℝ in 0..2 * π, deriv (circleMap c R) θ • f (circleMap c R θ)

/-- The integral along the part of a circle in the integrand's domain. -/
def circleIntegralOn {s : Set ℂ} (f : s → E) (c : ℂ) (R : ℝ) : E :=
  ∫ θ : circleAngles s c R,
    deriv (circleMap c R) θ.val • f ⟨circleMap c R θ.val, θ.2.2⟩ ∂(volume.comap Subtype.val)

theorem circleIntegralOn_eq_integral {s : Set ℂ} (hs : MeasurableSet s) (f : ℂ → E)
    (c : ℂ) (R : ℝ) :
    circleIntegralOn (fun z : s ↦ f z.val) c R =
      ∫ θ in circleAngles s c R, deriv (circleMap c R) θ • f (circleMap c R θ) :=
  integral_subtype_comap (μ := volume) (measurableSet_circleAngles hs c R)
    (fun θ : ℝ ↦ deriv (circleMap c R) θ id • f (circleMap c R θ))

/-- `∮ z in C(c, R), f z` is the circle integral $\oint_{|z-c|=R} f(z)\,dz$. -/
notation3 "∮ "(...)" in ""C("c", "R")"", "r:60:(scoped f => circleIntegral f c R) => r

theorem circleIntegral_def_Icc (f : ℂ → E) (c : ℂ) (R : ℝ) :
    (∮ z in C(c, R), f z) = ∫ θ in Icc 0 (2 * π),
    deriv (circleMap c R) θ • f (circleMap c R θ) := by
  rw [circleIntegral, intervalIntegral.integral_of_le Real.two_pi_pos.le,
    Measure.restrict_congr_set Ioc_ae_eq_Icc]

theorem circleIntegralOn_eq_circleIntegral {s : Set ℂ} (hs : MeasurableSet s) (f : ℂ → E)
    (c : ℂ) (R : ℝ)
    (h : ∀ᵐ θ ∂volume.restrict (Icc 0 (2 * π)), circleMap c R θ ∈ s) :
    circleIntegralOn (fun z : s ↦ f z.val) c R = circleIntegral f c R := by
  rw [circleIntegralOn_eq_integral hs, circleIntegral_def_Icc]
  congr 1
  apply Measure.restrict_congr_set
  filter_upwards [(ae_restrict_iff' measurableSet_Icc).mp h] with θ hθ
  exact propext (and_iff_left_of_imp hθ)

theorem circleIntegralOn_eq_intervalIntegral {s : Set ℂ} {c : ℂ} {R : ℝ} (f : s → E)
    (h : ∀ θ, circleMap c R θ ∈ s) :
    circleIntegralOn f c R =
      ∫ θ in 0..2 * π, deriv (circleMap c R) θ • f ⟨circleMap c R θ, h θ⟩ := by
  let g (θ : ℝ) := deriv (circleMap c R) θ • f ⟨circleMap c R θ, h θ⟩
  have hset : circleAngles s c R = Icc 0 (2 * π) := by
    ext θ
    simp [circleAngles, h]
  change (∫ θ : circleAngles s c R, g θ.val ∂(volume.comap Subtype.val)) =
    ∫ θ in 0..2 * π, g θ
  rw [integral_subtype_comap (hset.symm ▸ measurableSet_Icc), hset,
    integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le Real.two_pi_pos.le]

theorem circleIntegralOn_sphere {c : ℂ} {R : ℝ} (f : sphere c |R| → E) :
    circleIntegralOn f c R =
      ∫ θ in 0..2 * π, deriv (circleMap c R) θ •
        f ⟨circleMap c R θ, circleMap_mem_sphere' c R θ⟩ :=
  circleIntegralOn_eq_intervalIntegral f (circleMap_mem_sphere' c R)

private theorem circleIntegrableOn_of_weighted {s : Set ℂ} {c : ℂ} {R : ℝ} (hR : R ≠ 0)
    {f : s → E}
    (hf : Integrable (fun θ : circleAngles s c R ↦
      deriv (circleMap c R) θ.val • f ⟨circleMap c R θ.val, θ.2.2⟩) (volume.comap Subtype.val)) :
    CircleIntegrableOn f c R := by
  let u (θ : circleAngles s c R) := circleMap 0 R θ.val * I
  have hu (θ : circleAngles s c R) : IsUnit (u θ) := by
    apply (isUnit_iff_ne_zero).mpr
    simp [u, hR, I_ne_zero]
  have hcont : Continuous u :=
    ((continuous_circleMap 0 R).comp continuous_subtype_val).mul continuous_const
  have hInv : Continuous (fun θ ↦ Checked.inv (u θ) (hu θ)) := hcont.fun_inv₀
  simp only [CircleIntegrableOn, deriv_circleMap] at hf ⊢
  refine (hf.norm.const_mul |R|⁻¹).mono' ?_ ?_
  · simpa only [u, inv_smul_smul₀] using
      hInv.aestronglyMeasurable.fun_smul hf.aestronglyMeasurable
  · refine Eventually.of_forall fun θ ↦ ?_
    simp [norm_smul, norm_I]

theorem isUnit_sub_center_of_mem_sphere {c : ℂ} {R : ℝ} (hR : IsUnit R) (z : sphere c |R|) :
    IsUnit (z.val - c) := by
  apply (isUnit_iff_ne_zero).mpr
  rw [← norm_ne_zero_iff, mem_sphere_iff_norm.mp z.2, abs_ne_zero]
  exact hR.ne_zero

theorem isUnit_sub_of_mem_sphere_of_mem_ball {c w : ℂ} {R : ℝ} (hw : w ∈ ball c R)
    (z : sphere c |R|) : IsUnit (z.val - w) := by
  have hR : 0 < R := dist_nonneg.trans_lt hw
  refine (sub_ne_zero.mpr fun h ↦ ?_).isUnit
  have hnorm : dist w c = R := by
    rw [← h]
    simpa only [mem_sphere, abs_of_pos hR] using z.2
  exact (show dist w c < R from hw).ne hnorm

/-- If a sequence of continuous functions converges uniformly on the circle,
then their circle integrals converge to the circle integral of the limit function. -/
theorem _root_.TendstoUniformlyOn.tendsto_circleIntegral_of_continuousOn
    {ι : Type*} {f : ι → ℂ → E} {g : ℂ → E} {c : ℂ} {R : ℝ}
    {l : Filter ι} [l.IsCountablyGenerated] (hR : 0 ≤ R)
    (hf : ∀ᶠ i in l, ContinuousOn (f i) (sphere c R)) (h : TendstoUniformlyOn f g l (sphere c R)) :
    Tendsto (fun n ↦ ∮ z in C(c, R), f n z) l (𝓝 (∮ z in C(c, R), g z)) := by
  apply TendstoUniformlyOn.tendsto_intervalIntegral_of_continuousOn
  · refine hf.mono fun i hi ↦ .smul ?_ (hi.comp ?_ ?_)
    · rw [funext (deriv_circleMap _ _)]
      fun_prop
    · fun_prop
    · simp [hR, MapsTo]
  · rw [Metric.tendstoUniformlyOn_iff] at h ⊢
    simp only [dist_smul₀, deriv_circleMap, norm_mul, norm_I, norm_circleMap_zero,
      abs_of_nonneg hR, mul_one]
    intro ε hε
    rcases exists_pos_mul_lt hε R with ⟨δ, hδ₀, hRδ⟩
    refine (h δ hδ₀).mono fun i hi x hx ↦ ?_
    grw [← hRδ, hi (circleMap c R x) (by simp [hR])]

namespace circleIntegral

@[simp]
theorem integral_radius_zero (f : ℂ → E) (c : ℂ) : (∮ z in C(c, 0), f z) = 0 := by
  simp only [circleIntegral, deriv_circleMap]
  simp

theorem integral_congr {f g : ℂ → E} {c : ℂ} {R : ℝ} (hR : 0 ≤ R) (h : EqOn f g (sphere c R)) :
    (∮ z in C(c, R), f z) = ∮ z in C(c, R), g z :=
  intervalIntegral.integral_congr fun θ _ => by simp only [h (circleMap_mem_sphere _ hR _)]

/-- Circle integrals are invariant when functions change along discrete sets. -/
theorem circleIntegral_congr_codiscreteWithin {c : ℂ} {R : ℝ} {f₁ f₂ : ℂ → ℂ}
    (hf : f₁ =ᶠ[codiscreteWithin (sphere c |R|)] f₂) (hR : R ≠ 0) :
    (∮ z in C(c, R), f₁ z) = (∮ z in C(c, R), f₂ z) := by
  apply intervalIntegral.integral_congr_ae_restrict
  apply ae_restrict_le_codiscreteWithin measurableSet_uIoc
  simp only [deriv_circleMap, smul_eq_mul, mul_eq_mul_left_iff, mul_eq_zero,
    circleMap_eq_center_iff, hR, Complex.I_ne_zero, or_self, or_false]
  exact codiscreteWithin_mono (by tauto) (circleMap_preimage_codiscrete hR hf)

theorem integral_sub_inv_smul_sub_smul (f : ℂ → E) (c w : ℂ) (R : ℝ) :
    circleIntegralOn (fun z : ({w}ᶜ : Set ℂ) ↦
      Checked.inv (z.val - w) (sub_ne_zero.mpr z.2).isUnit • (z.val - w) • f z.val) c R =
        ∮ z in C(c, R), f z := by
  simp only [inv_smul_smul₀]
  by_cases hR : R = 0
  · simp only [circleIntegralOn, deriv_circleMap]
    simp [hR]
  apply circleIntegralOn_eq_circleIntegral (measurableSet_singleton w).compl
  exact ((countable_singleton w).preimage_circleMap c hR).ae_notMem _

theorem integral_undef {f : ℂ → E} {c : ℂ} {R : ℝ} (hf : ¬CircleIntegrable f c R) :
    (∮ z in C(c, R), f z) = 0 :=
  intervalIntegral.integral_undef (mt (circleIntegrable_iff R).mpr hf)

theorem integral_add {f g : ℂ → E} {c : ℂ} {R : ℝ} (hf : CircleIntegrable f c R)
    (hg : CircleIntegrable g c R) :
    (∮ z in C(c, R), f z + g z) = (∮ z in C(c, R), f z) + (∮ z in C(c, R), g z) := by
  simp only [circleIntegral, smul_add, intervalIntegral.integral_add hf.out hg.out]

theorem integral_sub {f g : ℂ → E} {c : ℂ} {R : ℝ} (hf : CircleIntegrable f c R)
    (hg : CircleIntegrable g c R) :
    (∮ z in C(c, R), f z - g z) = (∮ z in C(c, R), f z) - ∮ z in C(c, R), g z := by
  simp only [circleIntegral, smul_sub, intervalIntegral.integral_sub hf.out hg.out]

theorem integral_fun_sum {ι : Type*} {s : Finset ι} {f : ι → ℂ → E} {c : ℂ} {R : ℝ}
    (h : ∀ i ∈ s, CircleIntegrable (f i) c R) :
    (∮ z in C(c, R), ∑ i ∈ s, f i z) = ∑ i ∈ s, ∮ z in C(c, R), f i z := by
  simp only [circleIntegral, Finset.smul_sum,
    intervalIntegral.integral_finsetSum fun i hi ↦ (h i hi).out]

theorem norm_integral_le_of_norm_le_const' {f : ℂ → E} {c : ℂ} {R C : ℝ}
    (hf : ∀ z ∈ sphere c |R|, ‖f z‖ ≤ C) : ‖∮ z in C(c, R), f z‖ ≤ 2 * π * |R| * C :=
  calc
    ‖∮ z in C(c, R), f z‖ ≤ |R| * C * |2 * π - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const fun θ _ =>
        calc
          ‖deriv (circleMap c R) θ • f (circleMap c R θ)‖ = |R| * ‖f (circleMap c R θ)‖ := by
            simp [norm_smul]
          _ ≤ |R| * C := by
            gcongr; exact hf _ <| circleMap_mem_sphere' _ _ _
    _ = 2 * π * |R| * C := by rw [sub_zero, _root_.abs_of_pos Real.two_pi_pos]; ac_rfl

theorem norm_integral_le_of_norm_le_const {f : ℂ → E} {c : ℂ} {R C : ℝ} (hR : 0 ≤ R)
    (hf : ∀ z ∈ sphere c R, ‖f z‖ ≤ C) : ‖∮ z in C(c, R), f z‖ ≤ 2 * π * R * C :=
  have : |R| = R := abs_of_nonneg hR
  calc
    ‖∮ z in C(c, R), f z‖ ≤ 2 * π * |R| * C := norm_integral_le_of_norm_le_const' <| by rwa [this]
    _ = 2 * π * R * C := by rw [this]

theorem norm_two_pi_i_inv_smul_integral_le_of_norm_le_const {f : ℂ → E} {c : ℂ} {R C : ℝ}
    (hR : 0 ≤ R) (hf : ∀ z ∈ sphere c R, ‖f z‖ ≤ C) :
    ‖(2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), f z‖ ≤ R * C := by
  have : ‖(2 * π * I : ℂ)⁻¹‖ = (2 * π)⁻¹ := by simp
  rw [norm_smul, this, ← div_eq_inv_mul₀, div_le_iff₀ Real.two_pi_pos,
    mul_comm (R * C), ← mul_assoc]
  exact norm_integral_le_of_norm_le_const hR hf

/-- If `f` is continuous on the circle `|z - c| = R`, `R > 0`, the `‖f z‖` is less than or equal to
`C : ℝ` on this circle, and this norm is strictly less than `C` at some point `z` of the circle,
then `‖∮ z in C(c, R), f z‖ < 2 * π * R * C`. -/
theorem norm_integral_lt_of_norm_le_const_of_lt {f : ℂ → E} {c : ℂ} {R C : ℝ} (hR : 0 < R)
    (hc : ContinuousOn f (sphere c R)) (hf : ∀ z ∈ sphere c R, ‖f z‖ ≤ C)
    (hlt : ∃ z ∈ sphere c R, ‖f z‖ < C) : ‖∮ z in C(c, R), f z‖ < 2 * π * R * C := by
  rw [← _root_.abs_of_pos hR, ← image_circleMap_Ioc] at hlt
  rcases hlt with ⟨_, ⟨θ₀, hmem, rfl⟩, hlt⟩
  calc
    ‖∮ z in C(c, R), f z‖ ≤ ∫ θ in 0..2 * π, ‖deriv (circleMap c R) θ • f (circleMap c R θ)‖ :=
      intervalIntegral.norm_integral_le_integral_norm Real.two_pi_pos.le
    _ < ∫ _ in 0..2 * π, R * C := by
      simp only [deriv_circleMap, norm_smul, norm_mul, norm_circleMap_zero, abs_of_pos hR, norm_I,
        mul_one]
      refine intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
          Real.two_pi_pos ?_ continuousOn_const (fun θ _ => ?_) ⟨θ₀, Ioc_subset_Icc_self hmem, ?_⟩
      · exact continuousOn_const.mul (hc.comp (continuous_circleMap _ _).continuousOn fun θ _ =>
          circleMap_mem_sphere _ hR.le _).norm
      · gcongr
        exact hf _ <| circleMap_mem_sphere _ hR.le _
      · gcongr
    _ = 2 * π * R * C := by simp [mul_assoc]; ring

@[simp]
theorem integral_smul {𝕜 : Type*} [RCLike 𝕜] [NormedSpace 𝕜 E] [SMulCommClass 𝕜 ℂ E] (a : 𝕜)
    (f : ℂ → E) (c : ℂ) (R : ℝ) : (∮ z in C(c, R), a • f z) = a • ∮ z in C(c, R), f z := by
  simp only [circleIntegral, ← smul_comm a (_ : ℂ) (_ : E), intervalIntegral.integral_smul]

@[simp]
theorem integral_smul_const [CompleteSpace E] (f : ℂ → ℂ) (a : E) (c : ℂ) (R : ℝ) :
    (∮ z in C(c, R), f z • a) = (∮ z in C(c, R), f z) • a := by
  simp only [circleIntegral, intervalIntegral.integral_smul_const, ← smul_assoc]

@[simp]
theorem integral_const_mul (a : ℂ) (f : ℂ → ℂ) (c : ℂ) (R : ℝ) :
    (∮ z in C(c, R), a * f z) = a * ∮ z in C(c, R), f z :=
  integral_smul a f c R

@[simp]
theorem integral_sub_center_inv (c : ℂ) {R : ℝ} (hR : R ≠ 0) :
    circleIntegralOn (fun z : sphere c |R| ↦
      Checked.inv (z.val - c) (isUnit_sub_center_of_mem_sphere hR.isUnit z)) c R = 2 * π * I := by
  rw [circleIntegralOn_sphere]
  have h (θ : ℝ) : deriv (circleMap c R) θ •
      Checked.inv (circleMap c R θ - c)
        (isUnit_sub_center_of_mem_sphere hR.isUnit ⟨circleMap c R θ, circleMap_mem_sphere' c R θ⟩) =
      I := by
    rw [deriv_circleMap, smul_eq_mul, ← circleMap_sub_center c R θ]
    rw [mul_comm _ I, mul_assoc, mul_inv_cancel₀, mul_one]
  simp only [h, intervalIntegral.integral_const, sub_zero, real_smul, ofReal_mul, ofReal_ofNat]

/-- If `f' : ℂ → E` is a derivative of a complex differentiable function on the circle
`Metric.sphere c |R|`, then `∮ z in C(c, R), f' z = 0`. -/
theorem integral_eq_zero_of_hasDerivWithinAt' [CompleteSpace E] {f f' : ℂ → E} {c : ℂ} {R : ℝ}
    (h : ∀ z ∈ sphere c |R|, HasDerivWithinAt f (f' z) (sphere c |R|) z) :
    (∮ z in C(c, R), f' z) = 0 := by
  by_cases hi : CircleIntegrable f' c R
  · rw [← sub_eq_zero.2 ((periodic_circleMap c R).comp f).eq]
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => ?_) hi.out
    exact (h _ (circleMap_mem_sphere' _ _ _)).scomp_hasDerivAt θ
      (differentiable_circleMap _ _ _).hasDerivAt (circleMap_mem_sphere' _ _)
  · exact integral_undef hi

/-- If `f' : ℂ → E` is a derivative of a complex differentiable function on the circle
`Metric.sphere c R`, then `∮ z in C(c, R), f' z = 0`. -/
theorem integral_eq_zero_of_hasDerivWithinAt [CompleteSpace E]
    {f f' : ℂ → E} {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (h : ∀ z ∈ sphere c R, HasDerivWithinAt f (f' z) (sphere c R) z) : (∮ z in C(c, R), f' z) = 0 :=
  integral_eq_zero_of_hasDerivWithinAt' <| (abs_of_nonneg hR).symm ▸ h

/-- If `n < 0` and `|w - c| = |R|`, then `(z - w) ^ n` is not circle integrable on the circle with
center `c` and radius `|R|`, so the integral `∮ z in C(c, R), (z - w) ^ n` is equal to zero. -/
theorem integral_sub_zpow_of_undef {n : ℤ} {c w : ℂ} {R : ℝ} (hn : n < 0)
    (hw : w ∈ sphere c |R|) :
    circleIntegralOn (fun z : {z : ℂ | n < 0 → z ≠ w} ↦
      Checked.zpow (z.val - w) n (fun h ↦ (sub_ne_zero.mpr (z.2 h)).isUnit)) c R = 0 := by
  by_cases hR : R = 0
  · simp only [circleIntegralOn, deriv_circleMap, smul_eq_mul]
    simp [hR]
  unfold circleIntegralOn
  apply MeasureTheory.integral_undef
  intro hint
  have h := circleIntegrable_sub_zpow_iff.mp (circleIntegrableOn_of_weighted hR hint)
  exact h.elim hR fun h' ↦ h'.elim hn.not_ge (fun h'' ↦ h'' hw)

/-- If `n ≠ -1` is an integer number, then the integral of `(z - w) ^ n` over the circle equals
zero. -/
theorem integral_sub_zpow_of_ne {n : ℤ} (hn : n ≠ -1) (c w : ℂ) (R : ℝ) :
    circleIntegralOn (fun z : {z : ℂ | n < 0 → z ≠ w} ↦
      Checked.zpow (z.val - w) n (fun h ↦ (sub_ne_zero.mpr (z.2 h)).isUnit)) c R = 0 := by
  by_cases H : w ∈ sphere c |R| ∧ n < 0
  · exact integral_sub_zpow_of_undef H.2 H.1
  have hs (θ : ℝ) (h : n < 0) : circleMap c R θ ≠ w :=
    ne_of_mem_of_not_mem (circleMap_mem_sphere' c R θ) fun hw ↦ H ⟨hw, h⟩
  have hu (θ : ℝ) (h : n < 0) : IsUnit (circleMap c R θ - w) :=
    (sub_ne_zero.mpr (hs θ h)).isUnit
  let g (θ : ℝ) := Checked.zpow (circleMap c R θ - w) n (hu θ)
  let x (θ : ℝ) : {x : ℂ // n + 1 < 0 → IsUnit x} :=
    ⟨circleMap c R θ - w, fun h ↦ hu θ (by omega)⟩
  have hnc : IsUnit ((n : ℂ) + 1) := (show (n : ℂ) + 1 ≠ 0 by
    rw [Ne, add_eq_zero_iff_eq_neg, ← Int.cast_one, ← Int.cast_neg, Int.cast_inj]
    exact hn).isUnit
  let F (θ : ℝ) := Checked.div (Checked.zpow (x θ).val (n + 1) (x θ).2) ((n : ℂ) + 1) hnc
  have hd (θ : ℝ) : HasDerivAt F (deriv (circleMap c R) θ • g θ) θ := by
    have hx : HasDerivAt (Subtype.val ∘ x) (circleMap 0 R θ * I) θ :=
      (hasDerivAt_circleMap c R θ).sub_const w
    have hy := (hasDerivAt_zpow (n + 1) (x θ)).scomp (h := x) (coord' := Subtype.val) θ hx
      continuousAt_id Topology.IsEmbedding.subtypeVal
    convert (hy.div_const ((n : ℂ) + 1) (hd := hnc)) using 1
    · rfl
    · rw [dite_eq_right (by omega : n + 1 ≠ 0)]
      simp [g, x, deriv_circleMap, smul_eq_mul, Int.cast_add, mul_assoc, mul_comm]
      field
  have hg : Continuous g := ((continuous_circleMap _ _).sub continuous_const).zpow₀ n
  have hdcont : Continuous (fun θ ↦ deriv (circleMap c R) θ • g θ) := by
    simp_rw [deriv_circleMap]
    exact ((continuous_circleMap _ _).mul continuous_const).smul hg
  rw [circleIntegralOn_eq_intervalIntegral (s := {z : ℂ | n < 0 → z ≠ w}) _ hs]
  change (∫ θ in 0..2 * π, deriv (circleMap c R) θ • g θ) = 0
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ ↦ hd θ)
    (hdcont.intervalIntegrable _ _), sub_eq_zero]
  simp only [F, x, (periodic_circleMap c R).eq]

end circleIntegral

/-- The power series that is equal to
$\frac{1}{2πi}\sum_{n=0}^{\infty}
  \oint_{|z-c|=R} \left(\frac{w-c}{z - c}\right)^n \frac{1}{z-c}f(z)\,dz$ at
`w - c`. The coefficients of this power series depend only on `f ∘ circleMap c R`, and the power
series converges to `f w` if `f` is differentiable on the closed ball `Metric.closedBall c R` and
`w` belongs to the corresponding open ball. For any circle integrable function `f`, this power
series converges to the Cauchy integral for `f`. -/
def cauchyPowerSeries (f : ℂ → E) (c : ℂ) (R : ℝ) {hR : IsUnit R} :
    FormalMultilinearSeries ℂ ℂ E := fun n =>
  ContinuousMultilinearMap.mkPiRing ℂ _ <|
    (2 * π * I : ℂ)⁻¹ • circleIntegralOn (fun z : sphere c |R| ↦
      Checked.inv (z.val - c) (isUnit_sub_center_of_mem_sphere hR z) ^ n •
        Checked.inv (z.val - c) (isUnit_sub_center_of_mem_sphere hR z) • f z.val) c R

theorem cauchyPowerSeries_apply (f : ℂ → E) (c : ℂ) (R : ℝ) (n : ℕ) (w : ℂ)
    {hR : IsUnit R} :
    (cauchyPowerSeries f c R (hR := hR) n fun _ => w) =
      (2 * π * I : ℂ)⁻¹ • circleIntegralOn (fun z : sphere c |R| ↦
        Checked.div w (z.val - c) (isUnit_sub_center_of_mem_sphere hR z) ^ n •
          Checked.inv (z.val - c) (isUnit_sub_center_of_mem_sphere hR z) • f z.val) c R := by
  simp only [cauchyPowerSeries, ContinuousMultilinearMap.mkPiRing_apply, Fin.prod_const,
    circleIntegralOn_sphere, div_eq_mul_inv₀, mul_pow, mul_smul]
  simp_rw [← smul_comm (w ^ n), intervalIntegral.integral_smul]
  rw [← smul_comm (w ^ n)]

theorem norm_cauchyPowerSeries_le (f : ℂ → E) (c : ℂ) (R : ℝ) (n : ℕ) {hR : IsUnit R} :
    ‖cauchyPowerSeries f c R (hR := hR) n‖ ≤
      ((2 * π)⁻¹ * ∫ θ : ℝ in 0..2 * π, ‖f (circleMap c R θ)‖) *
        Checked.inv |R| (abs_ne_zero.mpr hR.ne_zero).isUnit ^ n :=
  let iR := Checked.inv |R| (abs_ne_zero.mpr hR.ne_zero).isUnit
  let hθ (θ : ℝ) : IsUnit (circleMap c R θ - c) :=
    isUnit_sub_center_of_mem_sphere hR ⟨circleMap c R θ, circleMap_mem_sphere' c R θ⟩
  let g (θ : ℝ) := deriv (circleMap c R) θ •
    Checked.inv (circleMap c R θ - c) (hθ θ) ^ n •
      Checked.inv (circleMap c R θ - c) (hθ θ) • f (circleMap c R θ)
  calc ‖cauchyPowerSeries f c R (hR := hR) n‖
    _ = (2 * π)⁻¹ * ‖∫ θ in 0..2 * π, g θ‖ := by
      simp [cauchyPowerSeries, circleIntegralOn_sphere, g, norm_smul]
    _ ≤ (2 * π)⁻¹ * ∫ θ in 0..2 * π, ‖g θ‖ := by
      gcongr
      exact intervalIntegral.norm_integral_le_integral_norm (by positivity)
    _ = (2 * π)⁻¹ * (iR ^ n * ∫ x : ℝ in 0..2 * π, ‖f (circleMap c R x)‖) := by
      simp [g, iR, norm_smul, mul_left_comm |R|]
      simpa only [smul_eq_mul] using
        (intervalIntegral.integral_smul (a := 0) (b := 2 * π) (μ := volume)
          (Checked.inv (|R| ^ n) ((abs_ne_zero.mpr hR.ne_zero).isUnit.pow n))
          (fun θ : ℝ ↦ ‖f (circleMap c R θ)‖))
    _ = ((2 * π)⁻¹ * ∫ θ : ℝ in 0..2 * π, ‖f (circleMap c R θ)‖) * iR ^ n := by
      ring

theorem le_radius_cauchyPowerSeries (f : ℂ → E) (c : ℂ) (R : ℝ≥0) {hR : IsUnit (R : ℝ)} :
    ↑R ≤ (cauchyPowerSeries f c R (hR := hR)).radius := by
  refine
    (cauchyPowerSeries f c R (hR := hR)).le_radius_of_bound
      ((2 * π)⁻¹ * ∫ θ : ℝ in 0..2 * π, ‖f (circleMap c R θ)‖) fun n => ?_
  refine (mul_le_mul_of_nonneg_right (norm_cauchyPowerSeries_le _ _ _ _ (hR := hR))
    (pow_nonneg R.coe_nonneg _)).trans ?_
  simp only [abs_of_nonneg R.coe_nonneg, inv_pow₀, inv_mul_cancel_right₀, le_refl]

/-- For any circle integrable function `f`, the power series `cauchyPowerSeries f c R` multiplied
by `2πI` converges to the integral `∮ z in C(c, R), (z - w)⁻¹ • f z` on the open disc
`Metric.ball c R`. -/
theorem hasSum_two_pi_I_cauchyPowerSeries_integral {f : ℂ → E} {c : ℂ} {R : ℝ} {w : ℂ}
    (hf : CircleIntegrable f c R) (hw : ‖w‖ < R) :
    HasSum (fun n : ℕ ↦ circleIntegralOn (fun z : sphere c |R| ↦
      Checked.div w (z.val - c)
        (isUnit_sub_center_of_mem_sphere (norm_nonneg w |>.trans_lt hw).ne'.isUnit z) ^ n •
        Checked.inv (z.val - c)
          (isUnit_sub_center_of_mem_sphere (norm_nonneg w |>.trans_lt hw).ne'.isUnit z) •
          f z.val) c R)
      (circleIntegralOn (fun z : sphere c |R| ↦ Checked.inv (z.val - (c + w))
        (isUnit_sub_of_mem_sphere_of_mem_ball
          (mem_ball_iff_norm.mpr (by simpa only [add_sub_cancel_left] using hw)) z)
          • f z.val) c R) := by
  have hR : 0 < R := (norm_nonneg w).trans_lt hw
  let hθ (θ : ℝ) : IsUnit (circleMap c R θ - c) :=
    isUnit_sub_center_of_mem_sphere hR.ne'.isUnit ⟨circleMap c R θ, circleMap_mem_sphere' c R θ⟩
  have hwR : ‖w‖ / R ∈ Ico (0 : ℝ) 1 :=
    ⟨div_nonneg (norm_nonneg w) hR.le, (div_lt_one hR).2 hw⟩
  simp only [circleIntegralOn_sphere]
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun n θ => ‖f (circleMap c R θ)‖ * (‖w‖ / R) ^ n) (fun n => ?_) (fun n => ?_) ?_ ?_ ?_
  · simp only [deriv_circleMap]
    apply_rules [AEStronglyMeasurable.smul, hf.def'.1] <;> apply Measurable.aestronglyMeasurable
    · fun_prop
    · exact ((continuous_const.div₀ ((continuous_circleMap _ _).sub continuous_const)
        (h₀ := hθ)).pow _).measurable
    · exact (((continuous_circleMap _ _).sub continuous_const).fun_inv₀ (h0 := hθ)).measurable
  · simp [norm_smul, abs_of_pos hR, mul_left_comm R, mul_comm ‖_‖]
  · exact Eventually.of_forall fun _ _ => (summable_geometric_of_lt_one hwR.1 hwR.2).mul_left _
  · simpa only [tsum_mul_left, tsum_geometric_of_lt_one hwR.1 hwR.2] using
      hf.norm.mul_continuousOn continuousOn_const
  · refine Eventually.of_forall fun θ _ => HasSum.const_smul _ ?_
    simp only [smul_smul]
    refine HasSum.smul_const ?_ _
    have : ‖Checked.div w (circleMap c R θ - c) (hθ θ)‖ < 1 := by
      simpa [abs_of_pos hR] using hwR.2
    convert! (hasSum_geometric_of_norm_lt_one this).mul_right _ using 1
    field [hθ θ]

/-- For any circle integrable function `f`, the power series `cauchyPowerSeries f c R`, `R > 0`,
converges to the Cauchy integral `(2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • f z` on the open
disc `Metric.ball c R`. -/
theorem hasSum_cauchyPowerSeries_integral {f : ℂ → E} {c : ℂ} {R : ℝ} {w : ℂ}
    (hf : CircleIntegrable f c R) (hw : ‖w‖ < R) :
    HasSum (fun n => cauchyPowerSeries f c R (hR := (norm_nonneg w |>.trans_lt hw).ne'.isUnit)
      n fun _ => w)
      ((2 * π * I : ℂ)⁻¹ • circleIntegralOn (fun z : sphere c |R| ↦
        Checked.inv (z.val - (c + w))
          (isUnit_sub_of_mem_sphere_of_mem_ball (mem_ball_iff_norm.mpr
            (by simpa only [add_sub_cancel_left] using hw)) z) • f z.val) c R) := by
  simp only [cauchyPowerSeries_apply]
  exact (hasSum_two_pi_I_cauchyPowerSeries_integral hf hw).const_smul _

/-- For any circle integrable function `f`, the power series `cauchyPowerSeries f c R`, `R > 0`,
converges to the Cauchy integral `(2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • f z` on the open
disc `Metric.ball c R`. -/
theorem sum_cauchyPowerSeries_eq_integral {f : ℂ → E} {c : ℂ} {R : ℝ} {w : ℂ}
    (hf : CircleIntegrable f c R) (hw : ‖w‖ < R) :
    (cauchyPowerSeries f c R (hR := (norm_nonneg w |>.trans_lt hw).ne'.isUnit)).sum w =
      (2 * π * I : ℂ)⁻¹ • circleIntegralOn (fun z : sphere c |R| ↦
        Checked.inv (z.val - (c + w))
          (isUnit_sub_of_mem_sphere_of_mem_ball (mem_ball_iff_norm.mpr
            (by simpa only [add_sub_cancel_left] using hw)) z) • f z.val) c R :=
  (hasSum_cauchyPowerSeries_integral hf hw).tsum_eq

/-- For any circle integrable function `f`, the power series `cauchyPowerSeries f c R`, `R > 0`,
converges to the Cauchy integral `(2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • f z` on the open
disc `Metric.ball c R`. -/
theorem hasFPowerSeriesOn_cauchy_integral {f : ℂ → E} {c : ℂ} {R : ℝ≥0}
    (hf : CircleIntegrable f c R) (hR : 0 < R) :
    HasFPowerSeriesOnBall (fun w : ball c (R : ℝ) ↦ (2 * π * I : ℂ)⁻¹ •
      circleIntegralOn (fun z : sphere c |(R : ℝ)| ↦
        Checked.inv (z.val - w.val) (isUnit_sub_of_mem_sphere_of_mem_ball w.2 z) • f z.val) c R)
      (cauchyPowerSeries f c R (hR := (show 0 < (R : ℝ) from hR).ne'.isUnit))
      ⟨c, mem_ball_self (show 0 < (R : ℝ) from hR)⟩ R Subtype.val := by
  refine ⟨le_radius_cauchyPowerSeries _ _ _ (hR := (show 0 < (R : ℝ) from hR).ne'.isUnit),
    ENNReal.coe_pos.2 hR, ?_⟩
  intro w _
  have hw : c + (w.val - c) = w.val := by abel
  simpa only [hw] using
    hasSum_cauchyPowerSeries_integral hf (mem_ball_iff_norm.mp w.2)

namespace circleIntegral

/-- Integral $\oint_{|z-c|=R} \frac{dz}{z-w} = 2πi$ whenever $|w-c| < R$. -/
theorem integral_sub_inv_of_mem_ball {c w : ℂ} {R : ℝ} (hw : w ∈ ball c R) :
    circleIntegralOn (fun z : sphere c |R| ↦
      Checked.inv (z.val - w) (isUnit_sub_of_mem_sphere_of_mem_ball hw z)) c R = 2 * π * I := by
  have hR : 0 < R := dist_nonneg.trans_lt hw
  suffices H : HasSum (fun n : ℕ ↦ circleIntegralOn (fun z : sphere c |R| ↦
      Checked.div (w - c) (z.val - c) (isUnit_sub_center_of_mem_sphere hR.ne'.isUnit z) ^ n *
        Checked.inv (z.val - c) (isUnit_sub_center_of_mem_sphere hR.ne'.isUnit z)) c R)
      (2 * π * I) by
    have A : CircleIntegrable (fun _ => (1 : ℂ)) c R := continuousOn_const.circleIntegrable'
    refine (H.unique ?_).symm
    simpa only [smul_eq_mul, mul_one, add_sub_cancel] using
      hasSum_two_pi_I_cauchyPowerSeries_integral A (mem_ball_iff_norm.1 hw)
  let u (z : sphere c |R|) :=
    Checked.inv (z.val - c) (isUnit_sub_center_of_mem_sphere hR.ne'.isUnit z)
  let q (z : sphere c |R|) :=
    Checked.div (w - c) (z.val - c) (isUnit_sub_center_of_mem_sphere hR.ne'.isUnit z)
  change HasSum (fun n : ℕ ↦ circleIntegralOn (fun z ↦ q z ^ n * u z) c R) (2 * π * I)
  have h₀ : circleIntegralOn (fun z ↦ q z ^ 0 * u z) c R = 2 * π * I := by
    simpa only [pow_zero, one_mul, u] using integral_sub_center_inv c hR.ne'
  refine h₀ ▸ hasSum_single _ fun n hn ↦ ?_
  have hₙ : circleIntegralOn (fun z ↦ u z ^ (n + 1)) c R = 0 := by
    have hn' : (-((n + 1 : ℕ) : ℤ)) ≠ -1 := by omega
    have h := integral_sub_zpow_of_ne hn' c c R
    have hmap (θ : ℝ) : circleMap c R θ ∈ {z : ℂ | (-((n + 1 : ℕ) : ℤ)) < 0 → z ≠ c} :=
      fun _ ↦ circleMap_ne_center hR.ne'
    rw [circleIntegralOn_eq_intervalIntegral _ hmap] at h
    rw [circleIntegralOn_sphere]
    convert h using 2
    rfl
  calc
    _ = (w - c) ^ n * circleIntegralOn (fun z ↦ u z ^ (n + 1)) c R := by
      simp only [circleIntegralOn_sphere, q, u, div_eq_mul_inv₀, mul_pow, pow_succ, smul_eq_mul]
      rw [← intervalIntegral.integral_const_mul]
      congr 1
      funext θ
      ring
    _ = 0 := by rw [hₙ, mul_zero]

end circleIntegral
