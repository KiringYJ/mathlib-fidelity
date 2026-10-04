import Mathlib.Probability.CDF
import Mathlib.Probability.Kernel.Disintegration.StandardBorel

/-!
# Conditional kernel CDFs without a public default

These tests check that the construction with the former default, `stieltjesOfMeasurableRat`, is not
public; that a rational conditional kernel CDF of a finite kernel gives a conditional kernel CDF
that agrees with it almost everywhere at every rational; that a conditional kernel CDF forces the
measures `ν a` to be σ-finite and is determined exactly up to null sets, so that
`ProbabilityTheory.Kernel.condKernelCDF`, which requires a finite kernel, is a choice with which
every conditional kernel CDF agrees almost everywhere and which is determined at atoms; and that
the specification and its rational version reject the former default on sets of positive measure.
-/

open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology

noncomputable section

/-! ### The construction with a default value is private -/

/-- error: Unknown identifier `stieltjesOfMeasurableRat` -/
#guard_msgs in
#check stieltjesOfMeasurableRat

/-- error: Unknown identifier `toRatCDF` -/
#guard_msgs in
#check toRatCDF

/-- error: Unknown identifier `defaultRatCDF` -/
#guard_msgs in
#check defaultRatCDF

/-- error: Unknown identifier `isCondKernelCDF_stieltjesOfMeasurableRat` -/
#guard_msgs in
#check isCondKernelCDF_stieltjesOfMeasurableRat

/-! ### Existence and uniqueness -/

section General

variable {α β : Type*} [SigmaAlgebra α] [SigmaAlgebra β] {κ : Kernel α (β × ℝ)}
  {ν : Kernel α β}

-- A rational conditional kernel CDF of a finite kernel gives a conditional kernel CDF that agrees
-- with it at every rational, `(ν a)`-almost everywhere.
example [IsFiniteKernel κ] {f : α × β → ℚ → ℝ} (hf : IsRatCondKernelCDF f κ ν) :
    ∃ g : α × β → StieltjesFunction ℝ, IsCondKernelCDF g κ ν ∧
      ∀ a (q : ℚ), (fun b ↦ g (a, b) q) =ᵐ[ν a] fun b ↦ f (a, b) q :=
  hf.exists_isCondKernelCDF

-- A conditional kernel CDF can only exist when every `ν a` is σ-finite, and two conditional kernel
-- CDFs then agree `(ν a)`-almost everywhere, without a separate σ-finiteness hypothesis.
example {f : α × β → StieltjesFunction ℝ} (hf : IsCondKernelCDF f κ ν) (a : α) :
    SigmaFinite (ν a) :=
  hf.sigmaFinite a

example {f g : α × β → StieltjesFunction ℝ} (hf : IsCondKernelCDF f κ ν)
    (hg : IsCondKernelCDF g κ ν) (a : α) :
    ∀ᵐ b ∂(ν a), f (a, b) = g (a, b) :=
  hf.ae_eq hg a

end General

section StandardBorel

variable {α γ : Type*} [SigmaAlgebra α] [SigmaAlgebra γ] [SigmaAlgebra.CountablyGenerated γ]
  (κ : Kernel α (γ × ℝ)) [IsFiniteKernel κ]

-- `condKernelCDF κ` is a conditional kernel CDF, every conditional kernel CDF agrees with it
-- `fst κ a`-almost everywhere, and its kernel disintegrates `κ`.
example : IsCondKernelCDF (Kernel.condKernelCDF κ) κ (Kernel.fst κ) :=
  Kernel.isCondKernelCDF_condKernelCDF κ

example {f : α × γ → StieltjesFunction ℝ} (hf : IsCondKernelCDF f κ (Kernel.fst κ)) (a : α) :
    ∀ᵐ b ∂(Kernel.fst κ a), f (a, b) = Kernel.condKernelCDF κ (a, b) :=
  hf.ae_eq_condKernelCDF a

example : Kernel.fst κ ⊗ₖ Kernel.condKernelReal κ = κ :=
  Kernel.compProd_fst_condKernelReal κ

-- At each rational, `condKernelCDF κ` is `fst κ a`-almost everywhere the kernel density of the ray.
example (a : α) (q : ℚ) :
    (fun b ↦ Kernel.condKernelCDF κ (a, b) q)
      =ᵐ[Kernel.fst κ a] fun b ↦ Kernel.density κ (Kernel.fst κ) a b (Iic (q : ℝ)) := by
  obtain ⟨g, hg, hg_ae⟩ := (Kernel.isRatCondKernelCDF_density_Iic κ).exists_isCondKernelCDF
  filter_upwards [hg.ae_eq_condKernelCDF a, hg_ae a q] with b hb hb'
  rw [← hb, hb']

end StandardBorel

/-! ### The domain of `condKernelCDF` -/

/--
error: failed to synthesize instance of type class
  IsFiniteKernel (Kernel.const Unit Measure.count)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example : Unit × ℝ → StieltjesFunction ℝ :=
  Kernel.condKernelCDF (Kernel.const Unit (Measure.count : Measure (ℝ × ℝ)))

/-! ### A positive control: a point mass -/

theorem cdf_dirac_apply (y x : ℝ) : cdf (Measure.dirac y) x = if y ≤ x then 1 else 0 := by
  rw [cdf_eq_real, measureReal_def, Measure.dirac_apply' _ measurableSet_Iic]
  by_cases h : y ≤ x <;> simp [h]

/-- The kernel with value `dirac (0, 1)`: its first marginal is `dirac 0`, and its conditional
kernel CDF at `0` is the cdf of `dirac 1`. -/
abbrev κ₀₁ : Kernel Unit (ℝ × ℝ) := Kernel.const Unit (Measure.dirac ((0 : ℝ), (1 : ℝ)))

theorem fst_κ₀₁ : Kernel.fst κ₀₁ () = Measure.dirac 0 := by
  ext s hs
  rw [Kernel.fst_apply' _ _ hs, Kernel.const_apply]
  change Measure.dirac ((0 : ℝ), (1 : ℝ)) (Prod.fst ⁻¹' s) = Measure.dirac 0 s
  rw [Measure.dirac_apply' _ (measurable_fst hs), Measure.dirac_apply' _ hs]
  by_cases h : (0 : ℝ) ∈ s <;> simp [h]

theorem isCondKernelCDF_κ₀₁ :
    IsCondKernelCDF (fun _ : Unit × ℝ ↦ cdf (Measure.dirac (1 : ℝ))) κ₀₁ (Kernel.fst κ₀₁) where
  measurable _ := measurable_const
  integrable _ _ := integrable_const _
  tendsto_atTop_one _ := tendsto_cdf_atTop _
  tendsto_atBot_zero _ := tendsto_cdf_atBot _
  setIntegral _ s hs x := by
    rw [setIntegral_const, fst_κ₀₁, Kernel.const_apply, cdf_eq_real, measureReal_def,
      measureReal_def, measureReal_def, Measure.dirac_apply' _ hs,
      Measure.dirac_apply' _ measurableSet_Iic, Measure.dirac_apply' _ (hs.prod measurableSet_Iic)]
    by_cases h0 : (0 : ℝ) ∈ s <;> by_cases h1 : (1 : ℝ) ≤ x <;> simp [h0, h1]

-- At the atom `0` of the first marginal the conditional kernel CDF is determined: `condKernelCDF`
-- is the cdf of `dirac 1` there, whatever choice it makes on null sets.
example : Kernel.condKernelCDF κ₀₁ ((), 0) = cdf (Measure.dirac (1 : ℝ)) := by
  have h := isCondKernelCDF_κ₀₁.ae_eq_condKernelCDF ()
  rw [fst_κ₀₁, ae_dirac_eq, Filter.eventually_pure] at h
  exact h.symm

/-! ### A conditional kernel CDF is determined only almost everywhere -/

/-- A modification of the conditional kernel CDF of `κ₀₁` away from the atom `0`. -/
def modifiedCDF (p : Unit × ℝ) : StieltjesFunction ℝ :=
  if p.2 = 0 then cdf (Measure.dirac (1 : ℝ)) else cdf (Measure.dirac (5 : ℝ))

-- The modification is again a conditional kernel CDF of `κ₀₁`, although it differs from the cdf of
-- `dirac 1` at every `b ≠ 0`; these points form a null set of the first marginal `dirac 0`.
example : IsCondKernelCDF modifiedCDF κ₀₁ (Kernel.fst κ₀₁) := by
  refine isCondKernelCDF_κ₀₁.congr (fun x ↦ ?_) (fun p ↦ ?_) (fun p ↦ ?_) (fun a ↦ ?_)
  · have : (fun p : Unit × ℝ ↦ modifiedCDF p x) = fun p ↦
        if p.2 = 0 then cdf (Measure.dirac (1 : ℝ)) x else cdf (Measure.dirac (5 : ℝ)) x := by
      funext p
      simp only [modifiedCDF]
      split_ifs <;> rfl
    rw [this]
    exact Measurable.ite ((measurableSet_singleton 0).preimage measurable_snd) measurable_const
      measurable_const
  · simp only [modifiedCDF]
    split_ifs <;> exact tendsto_cdf_atBot _
  · simp only [modifiedCDF]
    split_ifs <;> exact tendsto_cdf_atTop _
  · rw [fst_κ₀₁, ae_dirac_eq, Filter.eventually_pure]
    simp [modifiedCDF]

example : modifiedCDF ((), 5) ≠ cdf (Measure.dirac (1 : ℝ)) := by
  intro h
  have h2 : cdf (Measure.dirac (5 : ℝ)) 2 = cdf (Measure.dirac (1 : ℝ)) 2 := by
    simpa [modifiedCDF] using congrArg (fun F : StieltjesFunction ℝ ↦ F 2) h
  rw [cdf_dirac_apply, cdf_dirac_apply] at h2
  norm_num at h2

/-- Every measurable family of probability cdfs is a conditional kernel CDF of the zero kernel. -/
theorem isCondKernelCDF_zero (F : StieltjesFunction ℝ) (h_bot : Tendsto F atBot (𝓝 0))
    (h_top : Tendsto F atTop (𝓝 1)) :
    IsCondKernelCDF (fun _ : Unit × ℝ ↦ F) (0 : Kernel Unit (ℝ × ℝ))
      (Kernel.fst (0 : Kernel Unit (ℝ × ℝ))) where
  measurable _ := measurable_const
  integrable _ _ := by simp
  tendsto_atTop_one _ := h_top
  tendsto_atBot_zero _ := h_bot
  setIntegral _ _ _ _ := by simp

-- The cdfs of `dirac 0` and `dirac 1` are both conditional kernel CDFs of the zero kernel, and they
-- differ at `0`; uniqueness holds only up to the null sets of the zero marginal.
example : cdf (Measure.dirac (0 : ℝ)) 0 ≠ cdf (Measure.dirac (1 : ℝ)) 0 := by
  rw [cdf_eq_real, cdf_eq_real, measureReal_def, measureReal_def,
    Measure.dirac_apply' _ measurableSet_Iic, Measure.dirac_apply' _ measurableSet_Iic]
  simp

example : ∀ᵐ b ∂(Kernel.fst (0 : Kernel Unit (ℝ × ℝ)) ()),
    (fun _ : Unit × ℝ ↦ cdf (Measure.dirac (0 : ℝ))) ((), b)
      = (fun _ : Unit × ℝ ↦ cdf (Measure.dirac (1 : ℝ))) ((), b) :=
  (isCondKernelCDF_zero _ (tendsto_cdf_atBot _) (tendsto_cdf_atTop _)).ae_eq
    (isCondKernelCDF_zero _ (tendsto_cdf_atBot _) (tendsto_cdf_atTop _)) ()

/-! ### The specification rejects the former default where it matters -/

theorem not_isRatStieltjesPoint_zero {α : Type*} (a : α) :
    ¬ IsRatStieltjesPoint (fun (_ : α) (_ : ℚ) ↦ (0 : ℝ)) a := fun h ↦
  zero_ne_one (tendsto_nhds_unique tendsto_const_nhds h.tendsto_atTop_one)

-- For the zero kernel and `ν = const Unit (dirac 0)`, the zero rational family has every integral
-- property of a rational conditional kernel CDF, but it is a rational cdf nowhere. Only
-- `isRatStieltjesPoint_ae` rejects it, on a set of positive `ν`-measure, where the former public
-- construction substituted the cdf of `dirac 0`; and no conditional kernel CDF exists at all.
example : (∀ (a : Unit) (q : ℚ),
      Integrable (fun b ↦ (fun (_ : Unit × ℝ) (_ : ℚ) ↦ (0 : ℝ)) (a, b) q)
        (Kernel.const Unit (Measure.dirac (0 : ℝ)) a)) ∧
    ∀ (a : Unit) (s : Set ℝ), MeasurableSet s → ∀ q : ℚ,
      ∫ b in s, (fun (_ : Unit × ℝ) (_ : ℚ) ↦ (0 : ℝ)) (a, b) q
          ∂(Kernel.const Unit (Measure.dirac (0 : ℝ)) a)
        = ((0 : Kernel Unit (ℝ × ℝ)) a).real (s ×ˢ Iic (q : ℝ)) :=
  ⟨fun _ _ ↦ integrable_zero _ _ _, fun _ _ _ _ ↦ by simp⟩

example : ¬ IsRatCondKernelCDF (fun (_ : Unit × ℝ) (_ : ℚ) ↦ (0 : ℝ)) (0 : Kernel Unit (ℝ × ℝ))
    (Kernel.const Unit (Measure.dirac (0 : ℝ))) := by
  intro h
  have h0 := (h.isRatStieltjesPoint_ae ()).mono fun b hb ↦ not_isRatStieltjesPoint_zero _ hb
  rw [Kernel.const_apply, Filter.eventually_false_iff_eq_bot, ae_eq_bot] at h0
  exact Measure.dirac_ne_zero h0

example (g : Unit × ℝ → StieltjesFunction ℝ) :
    ¬ IsCondKernelCDF g (0 : Kernel Unit (ℝ × ℝ)) (Kernel.const Unit (Measure.dirac (0 : ℝ))) := by
  intro h
  have h0 (x : ℝ) : g ((), 0) x = 0 := by
    simpa [Kernel.const_apply, integral_dirac] using h.setIntegral () MeasurableSet.univ x
  have h_top := h.tendsto_atTop_one ((), 0)
  rw [show (g ((), 0) : ℝ → ℝ) = fun _ ↦ 0 from funext h0] at h_top
  exact zero_ne_one (tendsto_nhds_unique tendsto_const_nhds h_top)

-- For `const Unit (dirac (0, 1))`, the zero rational family, on which the former public
-- construction returned the cdf of `dirac 0`, is not a rational conditional kernel CDF.
example : ¬ IsRatCondKernelCDF (fun (_ : Unit × ℝ) (_ : ℚ) ↦ (0 : ℝ))
    (Kernel.const Unit (Measure.dirac ((0 : ℝ), (1 : ℝ))))
    (Kernel.fst (Kernel.const Unit (Measure.dirac ((0 : ℝ), (1 : ℝ))))) := by
  intro h
  have h1 := h.setIntegral () MeasurableSet.univ (1 : ℚ)
  rw [Kernel.const_apply, measureReal_def,
    Measure.dirac_apply' _ (MeasurableSet.univ.prod measurableSet_Iic)] at h1
  simp at h1

-- The cdf of `dirac 0` is not a conditional kernel CDF of `const Unit (dirac (0, 1))`: the
-- specification rejects it on a set of positive measure.
example : ¬ IsCondKernelCDF (fun _ : Unit × ℝ ↦ cdf (Measure.dirac (0 : ℝ)))
    (Kernel.const Unit (Measure.dirac ((0 : ℝ), (1 : ℝ))))
    (Kernel.fst (Kernel.const Unit (Measure.dirac ((0 : ℝ), (1 : ℝ))))) := by
  intro h
  have h1 := h.setIntegral () MeasurableSet.univ (0 : ℝ)
  have hcdf : cdf (Measure.dirac (0 : ℝ)) 0 = 1 := by
    rw [cdf_eq_real, measureReal_def, Measure.dirac_apply' _ measurableSet_Iic]
    simp
  rw [Measure.restrict_univ, integral_const, hcdf, Kernel.const_apply] at h1
  simp only [measureReal_def] at h1
  rw [Measure.dirac_apply' _ (MeasurableSet.univ.prod measurableSet_Iic)] at h1
  simp at h1

end
