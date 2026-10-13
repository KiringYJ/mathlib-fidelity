/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Probability.Kernel.MeasurableLIntegral

/-!
# With Density

For a kernel `κ : Kernel α β` and a function `f : α → β → ℝ≥0∞`, `withDensity κ f h` is
the kernel `a ↦ (κ a).withDensity (f a)`. Its domain is exactly the measurability of this
measure-valued map. The default proof tactic supplies this condition when `κ` is s-finite and
`Function.uncurry f` is measurable, and for zero kernels and constant densities zero and one.

## Main definitions

* `ProbabilityTheory.Kernel.withDensity κ f h`: the unique kernel whose value at each `a` is
  `(κ a).withDensity (f a)`. There is no value outside this domain. Joint measurability of the
  density and s-finiteness of the base kernel are sufficient, not necessary, for existence.

## Main statements

* `ProbabilityTheory.Kernel.lintegral_withDensity`:
  `∫⁻ b, g b ∂(withDensity κ f h a) = ∫⁻ b, f a b * g b ∂(κ a)` for measurable `f a` and `g`.
* `ProbabilityTheory.Kernel.IsSFiniteKernel.withDensity`: a jointly measurable density preserves
  s-finiteness of a kernel, including when the density has infinite values.

-/

@[expose] public section


open MeasureTheory ProbabilityTheory

open scoped MeasureTheory ENNReal NNReal

namespace ProbabilityTheory.Kernel

variable {α β ι : Type*} {mα : SigmaAlgebra α} {mβ : SigmaAlgebra β}
variable {κ : Kernel α β} {f : α → β → ℝ≥0∞}

@[fun_prop]
lemma measurable_withDensity [IsSFiniteKernel κ] (hf : Measurable (Function.uncurry f)) :
    Measurable fun a ↦ (κ a).withDensity (f a) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs ↦ ?_
  simp_rw [MeasureTheory.withDensity_apply _ hs]
  exact hf.setLIntegral_kernel_prod_right hs

@[fun_prop]
lemma measurable_withDensity_zero (κ : Kernel α β) :
    Measurable fun a ↦ (κ a).withDensity (0 : β → ℝ≥0∞) := by
  simp

@[fun_prop]
lemma measurable_withDensity_one (κ : Kernel α β) :
    Measurable fun a ↦ (κ a).withDensity (1 : β → ℝ≥0∞) := by
  simpa using κ.measurable

@[fun_prop]
lemma measurable_zero_withDensity (f : α → β → ℝ≥0∞) :
    Measurable fun a ↦ (0 : Measure β).withDensity (f a) := by
  simp

/-- A measurable weight depending only on the parameter defines a weighted kernel without any
finiteness assumption. -/
lemma measurable_withDensity_const (κ : Kernel α β) {c : α → ℝ≥0∞} (hc : Measurable c) :
    Measurable fun a ↦ (κ a).withDensity (fun _ ↦ c a) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs ↦ ?_
  simp only [MeasureTheory.withDensity_const, Measure.smul_apply, smul_eq_mul]
  exact hc.mul (κ.measurable_coe hs)

/-- The weighted measures form a kernel exactly when their values on measurable sets are
measurable functions of the parameter. -/
lemma measurable_withDensity_iff :
    (Measurable fun a ↦ (κ a).withDensity (f a)) ↔
      ∀ s, MeasurableSet s → Measurable fun a ↦ ∫⁻ b in s, f a b ∂κ a := by
  rw [Measure.measurable_measure]
  constructor <;> intro h s hs
  · simpa only [MeasureTheory.withDensity_apply _ hs] using h s hs
  · simpa only [MeasureTheory.withDensity_apply _ hs] using h s hs

/-- Pointwise almost everywhere equal densities have the same domain. -/
lemma measurable_withDensity_congr_ae {g : α → β → ℝ≥0∞}
    (hfg : ∀ a, f a =ᵐ[κ a] g a) :
    (Measurable fun a ↦ (κ a).withDensity (f a)) ↔
      Measurable fun a ↦ (κ a).withDensity (g a) := by
  have h : (fun a ↦ (κ a).withDensity (f a)) = fun a ↦ (κ a).withDensity (g a) :=
    funext fun a ↦ MeasureTheory.withDensity_congr_ae (hfg a)
  rw [h]

lemma measurable_withDensity_add (κ η : Kernel α β)
    (hκ : Measurable fun a ↦ (κ a).withDensity (f a))
    (hη : Measurable fun a ↦ (η a).withDensity (f a)) :
    Measurable fun a ↦ ((κ + η) a).withDensity (f a) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs ↦ ?_
  simp only [add_apply, withDensity_add_measure, Measure.add_apply]
  exact ((Measure.measurable_coe hs).comp hκ).add ((Measure.measurable_coe hs).comp hη)

lemma measurable_withDensity_sum [Countable ι] (κ : ι → Kernel α β)
    (hκ : ∀ i, Measurable fun a ↦ (κ i a).withDensity (f a)) :
    Measurable fun a ↦ (Kernel.sum κ a).withDensity (f a) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs ↦ ?_
  simp_rw [sum_apply, withDensity_sum, Measure.sum_apply _ hs]
  exact Measurable.tsum fun i ↦ (Measure.measurable_coe hs).comp (hκ i)

/-- Adding a sectionwise measurable density preserves the weighting domain. -/
lemma measurable_withDensity_add_right {f g : α → β → ℝ≥0∞}
    (hf : Measurable fun a ↦ (κ a).withDensity (f a))
    (hg : Measurable fun a ↦ (κ a).withDensity (g a)) (hg' : ∀ a, Measurable (g a)) :
    Measurable fun a ↦ (κ a).withDensity ((f + g) a) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs ↦ ?_
  have h (a : α) : (κ a).withDensity ((f + g) a) =
      (κ a).withDensity (f a) + (κ a).withDensity (g a) :=
    MeasureTheory.withDensity_add_right (f a) (hg' a)
  simp only [h, Measure.add_apply]
  exact ((Measure.measurable_coe hs).comp hf).add ((Measure.measurable_coe hs).comp hg)

/-- The weighting domain passes to countable sums of sectionwise measurable densities. -/
lemma measurable_withDensity_tsum [Countable ι] {f : ι → α → β → ℝ≥0∞}
    (hf : ∀ i, Measurable fun a ↦ (κ a).withDensity (f i a))
    (hf' : ∀ i a, Measurable (f i a)) :
    Measurable fun a ↦ (κ a).withDensity ((∑' i, f i) a) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs ↦ ?_
  have h (a : α) : (κ a).withDensity ((∑' i, f i) a) =
      Measure.sum (fun i ↦ (κ a).withDensity (f i a)) := by
    rw [Pi.tsum_apply (Pi.summable.mpr fun _ ↦ Pi.summable.mpr fun _ ↦ ENNReal.summable)]
    exact MeasureTheory.withDensity_tsum (fun i ↦ hf' i a)
  simp only [h, Measure.sum_apply _ hs]
  exact Measurable.tsum fun i ↦ (Measure.measurable_coe hs).comp (hf i)

/-- The domain of successive weighting gives the domain of the product of sectionwise measurable
densities. -/
lemma measurable_withDensity_mul {f g : α → β → ℝ≥0∞}
    (hf' : ∀ a, Measurable (f a)) (hg' : ∀ a, Measurable (g a))
    (hg : Measurable fun a ↦ ((κ a).withDensity (f a)).withDensity (g a)) :
    Measurable fun a ↦ (κ a).withDensity (fun b ↦ f a b * g a b) := by
  have h : (fun a ↦ (κ a).withDensity (fun b ↦ f a b * g a b)) =
      fun a ↦ ((κ a).withDensity (f a)).withDensity (g a) :=
    funext fun a ↦ MeasureTheory.withDensity_mul _ (hf' a) (hg' a)
  rwa [h]

/-- Recover the weighting domain from a difference and an almost everywhere smaller,
sectionwise measurable density. -/
lemma measurable_withDensity_of_sub_add {f g : α → β → ℝ≥0∞}
    (hsub : Measurable fun a ↦ (κ a).withDensity (fun b ↦ f a b - g a b))
    (hg : Measurable fun a ↦ (κ a).withDensity (g a))
    (hg' : ∀ a, Measurable (g a)) (hfg : ∀ a, g a ≤ᵐ[κ a] f a) :
    Measurable fun a ↦ (κ a).withDensity (f a) := by
  have h := measurable_withDensity_add_right hsub hg hg'
  refine (measurable_withDensity_congr_ae ?_).mp h
  intro a
  filter_upwards [hfg a] with b hb
  exact tsub_add_cancel_of_le hb

/-- Discharge the domain of a weighted kernel using a supplied proof, an elementary zero or one
case, or the standard s-finite, jointly measurable sufficient condition. -/
macro (name := withDensityMeasurable) &"kernel_withDensity_measurable" : tactic => `(tactic| first
  | done
  | assumption
  | solve
    | simp only [Pi.zero_apply, Pi.one_apply, zero_apply, MeasureTheory.withDensity_zero,
        MeasureTheory.withDensity_one, withDensity_zero_left, MeasureTheory.withDensity_const,
        zero_smul, one_smul, measurable_const, Kernel.measurable]
  | (
    apply ProbabilityTheory.Kernel.measurable_withDensity
    fun_prop (maxSteps := 1000))
  | (
    with_reducible apply ProbabilityTheory.Kernel.measurable_withDensity_const
    fun_prop (maxSteps := 1000))
  | fail "provide a proof that the weighted measures depend measurably on the parameter")

/-- The kernel of weighted measures, defined exactly when those measures depend measurably on
the parameter. The default tactic proves this from s-finiteness and joint measurability, or from
the elementary zero and one cases. -/
noncomputable def withDensity (κ : Kernel α β) (f : α → β → ℝ≥0∞)
    (h : Measurable (fun a ↦ (κ a).withDensity (f a)) := by kernel_withDensity_measurable) :
    Kernel α β :=
  ⟨fun a ↦ (κ a).withDensity (f a), h⟩

@[simp]
protected theorem withDensity_apply (κ : Kernel α β) (f : α → β → ℝ≥0∞)
    (h : Measurable fun a ↦ (κ a).withDensity (f a)) (a : α) :
    withDensity κ f h a = (κ a).withDensity (f a) := rfl

/-- Existence of the specified kernel is equivalent to the constructor's domain. -/
lemma exists_withDensity_iff :
    (∃ η : Kernel α β, ∀ a, η a = (κ a).withDensity (f a)) ↔
      Measurable fun a ↦ (κ a).withDensity (f a) := by
  constructor
  · rintro ⟨η, hη⟩
    exact (show (fun a ↦ η a) = _ from funext hη) ▸ η.measurable
  · intro h
    exact ⟨withDensity κ f h, fun _ ↦ rfl⟩

lemma withDensity_eq_of_apply_eq {η : Kernel α β}
    {h : Measurable fun a ↦ (κ a).withDensity (f a)}
    (hη : ∀ a, η a = (κ a).withDensity (f a)) : withDensity κ f h = η := by
  ext1 a
  exact (hη a).symm

theorem withDensity_apply_of_measurableSet (κ : Kernel α β)
    {h : Measurable fun a ↦ (κ a).withDensity (f a)} (a : α)
    {s : Set β} (hs : MeasurableSet s) :
    withDensity κ f h a s = ∫⁻ b in s, f a b ∂κ a := MeasureTheory.withDensity_apply _ hs

protected theorem withDensity_apply' (κ : Kernel α β)
    {h : Measurable fun a ↦ (κ a).withDensity (f a)} (a : α) [SFinite (κ a)] (s : Set β) :
    withDensity κ f h a s = ∫⁻ b in s, f a b ∂κ a := MeasureTheory.withDensity_apply' _ s

nonrec lemma withDensity_congr_ae (κ : Kernel α β) {f g : α → β → ℝ≥0∞}
    {hf : Measurable fun a ↦ (κ a).withDensity (f a)}
    (hfg : ∀ a, f a =ᵐ[κ a] g a) :
    withDensity κ f hf = withDensity κ g ((measurable_withDensity_congr_ae hfg).mp hf) := by
  ext1 a
  exact withDensity_congr_ae (hfg a)

nonrec lemma withDensity_absolutelyContinuous (f : α → β → ℝ≥0∞)
    {h : Measurable fun a ↦ (κ a).withDensity (f a)} (a : α) :
    Kernel.withDensity κ f h a ≪ κ a := withDensity_absolutelyContinuous _ _

@[simp]
lemma withDensity_one (κ : Kernel α β) :
    Kernel.withDensity κ 1 = κ := by
  ext1 a
  exact MeasureTheory.withDensity_one

@[simp]
lemma withDensity_one' (κ : Kernel α β) :
    Kernel.withDensity κ (fun _ _ ↦ 1) = κ := Kernel.withDensity_one _

@[simp]
lemma withDensity_zero (κ : Kernel α β) :
    Kernel.withDensity κ 0 = 0 := by
  ext1 a
  exact MeasureTheory.withDensity_zero

@[simp]
lemma withDensity_zero' (κ : Kernel α β) :
    Kernel.withDensity κ (fun _ _ ↦ 0) = 0 := Kernel.withDensity_zero _

@[simp]
lemma zero_withDensity (f : α → β → ℝ≥0∞) : withDensity (0 : Kernel α β) f = 0 := by
  ext1 a
  exact withDensity_zero_left _

theorem lintegral_withDensity (κ : Kernel α β)
    {h : Measurable fun a ↦ (κ a).withDensity (f a)} (a : α)
    (hf : Measurable (f a)) {g : β → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ b, g b ∂withDensity κ f h a = ∫⁻ b, f a b * g b ∂κ a := by
  rw [Kernel.withDensity_apply, lintegral_withDensity_eq_lintegral_mul _ hf hg]
  simp_rw [Pi.mul_apply]

theorem integral_withDensity {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : β → E} {a : α} {g : α → β → ℝ≥0}
    {h : Measurable fun a ↦ (κ a).withDensity (fun b ↦ g a b)}
    (hg : Measurable (g a)) :
    ∫ b, f b ∂withDensity κ (fun a b => g a b) h a = ∫ b, g a b • f b ∂κ a := by
  rw [Kernel.withDensity_apply, integral_withDensity_eq_integral_smul]
  exact hg

theorem withDensity_add_left (κ η : Kernel α β) (f : α → β → ℝ≥0∞)
    {hκ : Measurable fun a ↦ (κ a).withDensity (f a)}
    {hη : Measurable fun a ↦ (η a).withDensity (f a)} :
    withDensity (κ + η) f (measurable_withDensity_add κ η hκ hη) =
      withDensity κ f hκ + withDensity η f hη := by
  ext1 a
  exact withDensity_add_measure _ _ _

theorem withDensity_kernel_sum [Countable ι] (κ : ι → Kernel α β) (f : α → β → ℝ≥0∞)
    {hκ : ∀ i, Measurable fun a ↦ (κ i a).withDensity (f a)} :
    withDensity (Kernel.sum κ) f (measurable_withDensity_sum κ hκ) =
      Kernel.sum fun i ↦ withDensity (κ i) f (hκ i) := by
  ext1 a
  exact withDensity_sum (fun n ↦ κ n a) (f a)

/-- Section measurability is enough for addition of densities; the weighted kernels themselves
only need their exact domains. -/
lemma withDensity_add_right {f g : α → β → ℝ≥0∞}
    {hf : Measurable fun a ↦ (κ a).withDensity (f a)}
    {hg : Measurable fun a ↦ (κ a).withDensity (g a)}
    (hg' : ∀ a, Measurable (g a)) :
    withDensity κ (f + g) (measurable_withDensity_add_right hf hg hg') =
      withDensity κ f hf + withDensity κ g hg := by
  ext1 a
  exact MeasureTheory.withDensity_add_right (f a) (hg' a)

lemma withDensity_sub_add_cancel {f g : α → β → ℝ≥0∞}
    {hg : Measurable fun a ↦ (κ a).withDensity (g a)}
    {hsub : Measurable fun a ↦ (κ a).withDensity (fun b ↦ f a b - g a b)}
    (hg' : ∀ a, Measurable (g a)) (hfg : ∀ a, g a ≤ᵐ[κ a] f a) :
    withDensity κ (fun a x ↦ f a x - g a x) hsub + withDensity κ g hg =
      withDensity κ f (measurable_withDensity_of_sub_add hsub hg hg' hfg) := by
  ext1 a
  rw [add_apply, Kernel.withDensity_apply, Kernel.withDensity_apply, Kernel.withDensity_apply,
    ← MeasureTheory.withDensity_add_right _ (hg' a)]
  apply MeasureTheory.withDensity_congr_ae
  filter_upwards [hfg a] with x hx
  exact tsub_add_cancel_of_le hx

/-- A countable sum of sectionwise measurable densities commutes with weighting. -/
theorem withDensity_tsum [Countable ι] (κ : Kernel α β) {f : ι → α → β → ℝ≥0∞}
    {hf : ∀ i, Measurable fun a ↦ (κ a).withDensity (f i a)}
    (hf' : ∀ i a, Measurable (f i a)) :
    withDensity κ (∑' i, f i) (measurable_withDensity_tsum hf hf') =
      Kernel.sum fun i ↦ withDensity κ (f i) (hf i) := by
  ext1 a
  simp only [Kernel.withDensity_apply, sum_apply]
  rw [Pi.tsum_apply (Pi.summable.mpr fun _ ↦ Pi.summable.mpr fun _ ↦ ENNReal.summable)]
  exact MeasureTheory.withDensity_tsum (fun i ↦ hf' i a)

/-- A uniformly bounded density preserves finite kernels on its exact domain. -/
theorem isFiniteKernel_withDensity_of_bounded (κ : Kernel α β) [IsFiniteKernel κ] {B : ℝ≥0∞}
    {h : Measurable fun a ↦ (κ a).withDensity (f a)}
    (hB_top : B ≠ ∞) (hf_B : ∀ a b, f a b ≤ B) : IsFiniteKernel (withDensity κ f h) := by
  refine ⟨⟨B * κ.bound, ENNReal.mul_lt_top hB_top.lt_top κ.bound_lt_top, fun a ↦ ?_⟩⟩
  rw [withDensity_apply_of_measurableSet κ a MeasurableSet.univ]
  calc
    ∫⁻ b in Set.univ, f a b ∂κ a ≤ ∫⁻ _ in Set.univ, B ∂κ a := lintegral_mono (hf_B a)
    _ = B * κ a Set.univ := by simp
    _ ≤ B * κ.bound := by grw [measure_le_bound]

/-- A jointly measurable density preserves s-finiteness of a finite kernel. The density may
have infinite values. -/
theorem isSFiniteKernel_withDensity_of_isFiniteKernel (κ : Kernel α β) [IsFiniteKernel κ]
    (hf : Measurable (Function.uncurry f)) : IsSFiniteKernel (withDensity κ f) := by
  let fs : ℕ → α → β → ℝ≥0∞ := fun n a b ↦ min (f a b) (n + 1) - min (f a b) n
  have hfs (n : ℕ) : Measurable (Function.uncurry (fs n)) := by fun_prop
  have hf_eq_tsum : f = ∑' n, fs n := by
    have h_sum_a : ∀ a, Summable fun n ↦ fs n a :=
      fun _ ↦ Pi.summable.mpr fun _ ↦ ENNReal.summable
    ext a b : 2
    rw [Pi.tsum_apply (Pi.summable.mpr h_sum_a), Pi.tsum_apply (h_sum_a a),
      ENNReal.tsum_eq_liminf_sum_nat]
    have h_finsetSum : ∀ n, ∑ i ∈ Finset.range n, fs i a b = min (f a b) n := fun n ↦ by
      induction n with
      | zero => simp
      | succ n hn =>
        rw [Finset.sum_range_succ, hn]
        simp [fs]
    simp_rw [h_finsetSum]
    refine (Filter.Tendsto.liminf_eq ?_).symm
    simpa using (tendsto_const_nhds.min ENNReal.tendsto_nat_nhds_top :
      Filter.Tendsto (fun n : ℕ ↦ min (f a b) n) Filter.atTop (nhds (min (f a b) ∞)))
  have hsum : Measurable fun a ↦ (κ a).withDensity ((∑' n, fs n) a) := by
    rw [← hf_eq_tsum]
    fun_prop
  have h_eq : withDensity κ f =
      Kernel.sum fun n ↦ withDensity κ (fs n) (measurable_withDensity (hfs n)) := by
    calc
      withDensity κ f = withDensity κ (∑' n, fs n) hsum := by
        ext1 a
        simp only [Kernel.withDensity_apply, hf_eq_tsum]
      _ = _ := withDensity_tsum κ (fun n a ↦ Measurable.of_uncurry_left (hfs n))
  rw [h_eq]
  refine isSFiniteKernel_sum (hκs := fun n ↦ ?_)
  suffices IsFiniteKernel (withDensity κ (fs n) (measurable_withDensity (hfs n))) by
    infer_instance
  refine isFiniteKernel_withDensity_of_bounded κ (B := n + 1) (by finiteness) fun a b ↦ ?_
  exact (tsub_le_self.trans (min_le_right _ _))

/-- Jointly measurable densities preserve s-finiteness, including densities with infinite values.
This is a sufficient condition; the constructor itself only requires measurability of the weighted
measures. -/
nonrec theorem IsSFiniteKernel.withDensity (κ : Kernel α β) [IsSFiniteKernel κ]
    (hf : Measurable (Function.uncurry f)) : IsSFiniteKernel (withDensity κ f) := by
  have hseq (i : ℕ) : Measurable fun a ↦ (seq κ i a).withDensity (f a) := by fun_prop
  have h_eq_sum : withDensity κ f = Kernel.sum fun i ↦ withDensity (seq κ i) f (hseq i) := by
    rw [← withDensity_kernel_sum]
    congr 1
    exact (kernel_sum_seq κ).symm
  rw [h_eq_sum]
  exact isSFiniteKernel_sum (hκs := fun n ↦
    isSFiniteKernel_withDensity_of_isFiniteKernel (seq κ n) hf)

/-- Successive weighting agrees with multiplication for sectionwise measurable densities. -/
nonrec lemma withDensity_mul {f g : α → β → ℝ≥0∞}
    {hf : Measurable fun a ↦ (κ a).withDensity (f a)}
    {hg : Measurable fun a ↦ (withDensity κ f hf a).withDensity (g a)}
    (hf' : ∀ a, Measurable (f a)) (hg' : ∀ a, Measurable (g a)) :
    withDensity κ (fun a b ↦ f a b * g a b) (measurable_withDensity_mul hf' hg' hg) =
      withDensity (withDensity κ f hf) g hg := by
  ext1 a
  exact withDensity_mul _ (hf' a) (hg' a)

end ProbabilityTheory.Kernel
