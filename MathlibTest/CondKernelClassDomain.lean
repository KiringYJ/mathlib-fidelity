import Mathlib.Probability.HasCondDistrib
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.Posterior

/-!
# Conditional kernels without finite measures

These tests check the lemmas about conditional kernels, conditional distributions, and posteriors
that hold on the class of a unique conditional kernel, or for σ-finite or s-finite laws, rather than
for finite measures: the pointwise formula at a point of finite mass of the first marginal, the
representatives of the class, the Bochner integrals against a conditional kernel of a measure with
an s-finite first marginal, the transport of conditional distributions between joint laws, the
conditional distribution of a function of the conditioning variable under a measure that is not
σ-finite, the conditional expectation given an infinite measure with a σ-finite law, the posterior
of an infinite prior, and the composition identities for measures that are not s-finite.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

/-! ### Conditional kernels at a point of finite mass -/

-- A σ-finite first marginal supplies the finiteness at every point.
example (ρ : Measure (ℝ × ℝ)) [SigmaFinite ρ.fst] (η : Kernel ℝ ℝ) [ρ.IsCondKernel η] {x : ℝ}
    (hx : ρ.fst {x} ≠ 0) (s : Set ℝ) :
    η x s = (ρ.fst {x})⁻¹ * ρ ({x} ×ˢ s) :=
  Measure.IsCondKernel.apply_of_ne_zero ρ η hx s

-- Without it, the finiteness at the point is an explicit hypothesis.
example (ρ : Measure (ℝ × ℝ)) (η : Kernel ℝ ℝ) [ρ.IsCondKernel η] {x : ℝ}
    (hx : ρ.fst {x} ≠ 0) (hx_top : ρ.fst {x} ≠ ∞) (s : Set ℝ) :
    η x s = (ρ.fst {x})⁻¹ * ρ ({x} ×ˢ s) :=
  Measure.IsCondKernel.apply_of_ne_zero ρ η hx s hx_top

/--
error: could not synthesize default value for parameter 'hx_top' using tactics
---
error: the mass of a singleton is supplied by default only for a σ-finite measure
ρ : Measure (ℝ × ℝ)
η : Kernel ℝ ℝ
inst✝ : ρ.IsCondKernel η
x : ℝ
hx : ρ.fst {x} ≠ 0
s : Set ℝ
⊢ ρ.fst {x} ≠ ∞
-/
#guard_msgs in
example (ρ : Measure (ℝ × ℝ)) (η : Kernel ℝ ℝ) [ρ.IsCondKernel η] {x : ℝ}
    (hx : ρ.fst {x} ≠ 0) (s : Set ℝ) :
    η x s = (ρ.fst {x})⁻¹ * ρ ({x} ×ˢ s) :=
  Measure.IsCondKernel.apply_of_ne_zero ρ η hx s

example (ρ : Measure (ℝ × ℝ)) (η : Kernel ℝ ℝ) [ρ.IsCondKernel η] (hρ : ∀ a, ρ.fst {a} ≠ 0)
    (hρ_top : ∀ a, ρ.fst {a} ≠ ∞) :
    IsMarkovKernel η :=
  Measure.IsCondKernel.isMarkovKernel ρ η hρ hρ_top

-- The default also supplies the finiteness at every point.
example (ρ : Measure (ℝ × ℝ)) [SigmaFinite ρ.fst] (η : Kernel ℝ ℝ) [ρ.IsCondKernel η]
    (hρ : ∀ a, ρ.fst {a} ≠ 0) :
    IsMarkovKernel η :=
  Measure.IsCondKernel.isMarkovKernel ρ η hρ

-- Counting measure on `ℝ`, which is not σ-finite, composed with a Dirac kernel: every singleton
-- has marginal mass one, so the formula applies at every point.
example (x : ℝ) (s : Set ℝ) :
    Kernel.const ℝ (Measure.dirac (0 : ℝ)) x s =
      (((Measure.count : Measure ℝ) ⊗ₘ Kernel.const ℝ (Measure.dirac (0 : ℝ))).fst {x})⁻¹ *
        ((Measure.count : Measure ℝ) ⊗ₘ Kernel.const ℝ (Measure.dirac (0 : ℝ))) ({x} ×ˢ s) := by
  have : ((Measure.count : Measure ℝ) ⊗ₘ Kernel.const ℝ (Measure.dirac (0 : ℝ))).IsCondKernel
      (Kernel.const ℝ (Measure.dirac (0 : ℝ))) := ⟨inferInstance, by rw [Measure.fst_compProd]⟩
  exact Measure.IsCondKernel.apply_of_ne_zero
    ((Measure.count : Measure ℝ) ⊗ₘ Kernel.const ℝ (Measure.dirac (0 : ℝ)))
    (Kernel.const ℝ (Measure.dirac (0 : ℝ))) (x := x) (by simp) s (by simp)

-- At a point of infinite mass the formula fails for `s = univ`: `dirac 0` disintegrates
-- `∞ • dirac ((), 0)`, while the right side vanishes.
example : ((∞ : ℝ≥0∞) • Measure.dirac ((), (0 : ℝ))).IsCondKernel
      (Kernel.const Unit (Measure.dirac (0 : ℝ))) ∧
    Kernel.const Unit (Measure.dirac (0 : ℝ)) () Set.univ ≠
      (((∞ : ℝ≥0∞) • Measure.dirac ((), (0 : ℝ))).fst {()})⁻¹ *
        ((∞ : ℝ≥0∞) • Measure.dirac ((), (0 : ℝ))) ({()} ×ˢ Set.univ) := by
  have h_fst : ((∞ : ℝ≥0∞) • Measure.dirac ((), (0 : ℝ))).fst = ∞ • Measure.dirac () := by
    rw [Measure.fst, Measure.map_smul _ measurable_fst.aemeasurable,
      Measure.map_dirac' measurable_fst]
  refine ⟨⟨inferInstance, ?_⟩, ?_⟩
  · rw [h_fst, Measure.compProd_smul_left, Measure.dirac_unit_compProd_const,
      Measure.map_dirac' measurable_prodMk_left]
  · simp [h_fst]

/-! ### Representatives of the class -/

variable {α : Type*} {mα : SigmaAlgebra α}

-- A disintegration of a measure with a σ-finite first marginal is a probability measure almost
-- everywhere, so every one represents the class.
example (ρ : Measure (ℝ × ℝ)) [SigmaFinite ρ.fst] (η : Kernel ℝ ℝ) [ρ.IsCondKernel η] :
    ∀ᵐ a ∂ρ.fst, IsProbabilityMeasure (η a) :=
  Measure.IsCondKernel.ae_isProbabilityMeasure ρ η

example (ρ : Measure (ℝ × ℝ)) [ρ.HasUniqueCondKernel] (η : Kernel ℝ ℝ) :
    η ∈ ρ.condKernel ↔ ρ.IsCondKernel η ∧ ∀ᵐ a ∂ρ.fst, IsProbabilityMeasure (η a) :=
  Measure.mem_condKernel_iff_isCondKernel_and_ae_isProbabilityMeasure

-- Every representative disintegrates the measure.
example (ρ : Measure (ℝ × ℝ)) [ρ.HasUniqueCondKernel] (η : Kernel ℝ ℝ) (hη : η ∈ ρ.condKernel) :
    ρ.IsCondKernel η :=
  Measure.isCondKernel_of_mem_condKernel hη

-- No standard Borel space: the class and a σ-finite first marginal suffice.
example {Ω : Type*} [SigmaAlgebra Ω] (ρ : Measure (α × Ω)) [ρ.HasUniqueCondKernel]
    [SigmaFinite ρ.fst] (η : Kernel α Ω) :
    η ∈ ρ.condKernel ↔ ρ.IsCondKernel η :=
  Measure.mem_condKernel_iff

-- On every fiber at which the first marginal is σ-finite, a conditional kernel of a kernel is
-- almost everywhere a probability measure, and its section is a conditional kernel of the measure.
example {β : Type*} {mβ : SigmaAlgebra β} (κ : Kernel α (β × ℝ)) (η : Kernel (α × β) ℝ)
    [κ.IsCondKernel η] (a : α) [SigmaFinite (Kernel.fst κ a)] :
    ∀ᵐ b ∂(Kernel.fst κ a), IsProbabilityMeasure (η (a, b)) :=
  Kernel.IsCondKernel.ae_isProbabilityMeasure κ η a

example {β : Type*} {mβ : SigmaAlgebra β} (κ : Kernel α (β × ℝ)) (η : Kernel (α × β) ℝ)
    [κ.IsCondKernel η] (a : α) :
    (κ a).IsCondKernel (Kernel.sectR η a) :=
  Kernel.IsCondKernel.isCondKernel_sectR κ η a

-- Two conditional kernels of a measure with a σ-finite first marginal agree almost everywhere,
-- with no finiteness of the kernels, and so do two conditional kernels of a kernel on a fiber
-- where the first marginal is σ-finite.
example (ρ : Measure (ℝ × ℝ)) [SigmaFinite ρ.fst] (η η' : Kernel ℝ ℝ) [ρ.IsCondKernel η]
    [ρ.IsCondKernel η'] :
    ∀ᵐ a ∂ρ.fst, η a = η' a :=
  Measure.IsCondKernel.ae_eq η η'

-- On a measurable set, they agree almost everywhere with values in any space.
example {Ω : Type*} [SigmaAlgebra Ω] (ρ : Measure (α × Ω)) [SigmaFinite ρ.fst]
    (η η' : Kernel α Ω) [ρ.IsCondKernel η] [ρ.IsCondKernel η'] {s : Set Ω} (hs : MeasurableSet s) :
    ∀ᵐ a ∂ρ.fst, η a s = η' a s :=
  Measure.IsCondKernel.ae_eq_apply η η' hs

example {β : Type*} {mβ : SigmaAlgebra β} (κ : Kernel α (β × ℝ)) (η η' : Kernel (α × β) ℝ)
    [κ.IsCondKernel η] [κ.IsCondKernel η'] (a : α) [SigmaFinite (Kernel.fst κ a)] :
    ∀ᵐ b ∂(Kernel.fst κ a), η (a, b) = η' (a, b) :=
  Kernel.IsCondKernel.ae_eq η η' a

-- The section over a point of a conditional kernel of a kernel represents the conditional kernel
-- of the measure there.
example {β : Type*} {mβ : SigmaAlgebra β} (κ : Kernel α (β × ℝ)) (η : Kernel (α × β) ℝ)
    [κ.IsCondKernel η] (a : α) [(κ a).HasUniqueCondKernel] [SigmaFinite (Kernel.fst κ a)] :
    Kernel.sectR η a ∈ (κ a).condKernel :=
  Kernel.IsCondKernel.sectR_mem_condKernel a

example {β : Type*} {mβ : SigmaAlgebra β} (κ : Kernel α (β × ℝ)) (a : α) :
    Kernel.fst κ a = (κ a).fst :=
  Kernel.fst_apply_eq_fst κ a

example {β : Type*} {mβ : SigmaAlgebra β} (κ : Kernel α (β × ℝ)) (a : α) :
    Kernel.snd κ a = (κ a).snd :=
  Kernel.snd_apply_eq_snd κ a

-- Instance search passes σ-finiteness and s-finiteness from the first marginal of a kernel at a
-- point to the first marginal of the measure there.
example {β : Type*} {mβ : SigmaAlgebra β} (κ : Kernel α (β × ℝ)) (a : α)
    [SigmaFinite (Kernel.fst κ a)] :
    SigmaFinite (κ a).fst :=
  inferInstance

example {β : Type*} {mβ : SigmaAlgebra β} (κ : Kernel α (β × ℝ)) (a : α)
    [SFinite (Kernel.fst κ a)] :
    SFinite (κ a).fst :=
  inferInstance

-- A kernel disintegrates a measure if its composition-product with the first marginal, in any
-- form, is the measure.
example (μ : Measure ℝ) (κ : Kernel ℝ ℝ) [IsMarkovKernel κ] :
    (μ ⊗ₘ κ).IsCondKernel κ :=
  .of_compProd_eq (Measure.fst_compProd μ κ) rfl

-- Every conditional kernel of a finite kernel represents its conditional kernel.
example {β : Type*} {mβ : SigmaAlgebra β} [SigmaAlgebra.CountablyGenerated β]
    (κ : Kernel α (β × ℝ)) [IsFiniteKernel κ] (η : Kernel (α × β) ℝ) :
    η ∈ Kernel.condKernel κ ↔ κ.IsCondKernel η :=
  Kernel.mem_condKernel_iff

-- An infinite scaling keeps the conditional kernel.
example (ρ : Measure (ℝ × ℝ)) [ρ.HasUniqueCondKernel] [((∞ : ℝ≥0∞) • ρ).HasUniqueCondKernel]
    (η : Kernel ℝ ℝ) :
    η ∈ ((∞ : ℝ≥0∞) • ρ).condKernel ↔ η ∈ ρ.condKernel :=
  Measure.mem_condKernel_smul_iff ENNReal.top_ne_zero

-- A finite scaling keeps a unique conditional kernel, which instance search supplies for a
-- nonnegative real factor.
example (ρ : Measure (ℝ × ℝ)) [ρ.HasUniqueCondKernel] {c : ℝ≥0∞} (hc : c ≠ ∞) :
    (c • ρ).HasUniqueCondKernel :=
  Measure.HasUniqueCondKernel.smul hc

example (ρ : Measure (ℝ × ℝ)) [ρ.HasUniqueCondKernel] (c : NNReal) :
    (c • ρ).HasUniqueCondKernel :=
  inferInstance

-- It does not apply to the factor `∞`, which can make the conditional kernel non-unique.
/--
error: failed to synthesize instance of type class
  (∞ • ρ).HasUniqueCondKernel

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example (ρ : Measure (ℝ × ℝ)) [ρ.HasUniqueCondKernel] :
    ((∞ : ℝ≥0∞) • ρ).HasUniqueCondKernel :=
  inferInstance

/-! ### Integrals against a conditional kernel -/

example (ρ : Measure (ℝ × ℝ)) [SFinite ρ.fst] (η : Kernel ℝ ℝ) [IsSFiniteKernel η]
    [ρ.IsCondKernel η] {f : ℝ × ℝ → ℝ} (hf : Integrable f ρ) :
    ∫ b, ∫ ω, f (b, ω) ∂η b ∂ρ.fst = ∫ x, f x ∂ρ :=
  Measure.integral_condKernel hf

-- For a kernel, only the fiber at the point needs an s-finite first marginal.
example (κ : Kernel ℝ (ℝ × ℝ)) (η : Kernel (ℝ × ℝ) ℝ) [IsSFiniteKernel η] [κ.IsCondKernel η]
    (a : ℝ) [SFinite (Kernel.fst κ a)] {f : ℝ × ℝ → ℝ} (hf : Integrable f (κ a)) :
    ∫ b, ∫ ω, f (b, ω) ∂η (a, b) ∂Kernel.fst κ a = ∫ x, f x ∂κ a :=
  ProbabilityTheory.integral_condKernel a hf

-- The conditional kernel need only be s-finite on the fiber.
example (κ : Kernel ℝ (ℝ × ℝ)) (η : Kernel (ℝ × ℝ) ℝ) [κ.IsCondKernel η] (a : ℝ)
    [SFinite (Kernel.fst κ a)] [IsSFiniteKernel (Kernel.sectR η a)] {f : ℝ × ℝ → ℝ}
    (hf : Integrable f (κ a)) :
    ∫ b, ∫ ω, f (b, ω) ∂η (a, b) ∂Kernel.fst κ a = ∫ x, f x ∂κ a :=
  ProbabilityTheory.integral_condKernel a hf

/-! ### Conditional distributions -/

-- The law of `Y` given itself, for every measure: the joint law of `(Y, Y)` has a unique
-- conditional kernel in a countably generated space.
example (μ : Measure α) (Y : α → ℝ) (hY : AEMeasurable Y μ) :
    Kernel.id ∈ condDistrib Y Y μ :=
  id_mem_condDistrib_self hY

-- Counting measure on `ℝ` is not σ-finite.
example : (Kernel.id : Kernel ℝ ℝ) ∈ condDistrib id id (Measure.count : Measure ℝ) :=
  id_mem_condDistrib_self aemeasurable_id

example (c : ℝ) :
    Kernel.deterministic (fun _ ↦ c) measurable_const ∈
      condDistrib (fun _ ↦ c) id (Measure.count : Measure ℝ) :=
  deterministic_mem_condDistrib_const aemeasurable_id c

-- For a general measurable function, the lemma supplies the class.
example (f : ℝ → ℝ) (hf : Measurable f)
    [((Measure.count : Measure ℝ).map (fun a ↦ (id a, (f ∘ id) a))).HasUniqueCondKernel] :
    Kernel.deterministic f hf ∈ condDistrib (f ∘ id) id (Measure.count : Measure ℝ) :=
  deterministic_mem_condDistrib_comp_self aemeasurable_id hf

example (f : ℝ → ℝ) (hf : Measurable f) :
    ((Measure.count : Measure ℝ).map (fun a ↦ (id a, (f ∘ id) a))).HasUniqueCondKernel :=
  Measure.hasUniqueCondKernel_map_prodMk_comp aemeasurable_id hf

-- A Markov kernel with the defining property represents the class of any joint law that has one.
-- The local instance of the class determines the proof that `condDistrib` takes by default.
example (μ : Measure α) {X Y : α → ℝ} (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    [(μ.map (fun a ↦ (X a, Y a)) (hX.prodMk hY)).HasUniqueCondKernel] (η : Kernel ℝ ℝ)
    [IsMarkovKernel η] (h : μ.map (fun a ↦ (X a, Y a)) = μ.map X ⊗ₘ η) :
    η ∈ condDistrib Y X μ :=
  mem_condDistrib_of_measure_eq_compProd_of_isMarkovKernel hX hY h

-- A kernel with the defining property, for a σ-finite law and no standard Borel space.
example {Ω : Type*} [SigmaAlgebra Ω] (μ : Measure α) {X : α → ℝ} {Y : α → Ω}
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    [(μ.map (fun a ↦ (X a, Y a)) (hX.prodMk hY)).HasUniqueCondKernel] [SigmaFinite (μ.map X hX)]
    (η : Kernel ℝ Ω) [(μ.map X hX).HasCompProd η] :
    η ∈ condDistrib Y X μ ↔ μ.map (fun a ↦ (X a, Y a)) = μ.map X ⊗ₘ η :=
  mem_condDistrib_iff hX hY

-- A representative that is not s-finite: counting measure off the atom of the law of `X`. The
-- composition-product of the law of `X` with it exists, and it has the defining property.
theorem piecewise_count_mem_condDistrib :
    Kernel.piecewise (measurableSet_singleton (0 : ℝ))
        (Kernel.deterministic (fun _ ↦ (0 : ℝ)) measurable_const)
        (Kernel.const ℝ (Measure.count : Measure ℝ)) ∈
      condDistrib (fun _ ↦ (0 : ℝ)) id (Measure.dirac (0 : ℝ)) := by
  refine Kernel.AEClass.mem_of_eventuallyEq
    (deterministic_mem_condDistrib_const aemeasurable_id (0 : ℝ)) ?_
  rw [Measure.map_id, Filter.EventuallyEq, ae_dirac_eq, Filter.eventually_pure]
  simp [Kernel.piecewise_apply]

example (η : Kernel ℝ ℝ) (hη : η ∈ condDistrib (fun _ ↦ (0 : ℝ)) id (Measure.dirac (0 : ℝ))) :
    haveI := hasCompProd_map_of_mem_condDistrib aemeasurable_id aemeasurable_const hη
    (Measure.dirac (0 : ℝ)).map id ⊗ₘ η = (Measure.dirac (0 : ℝ)).map fun a ↦ (id a, (0 : ℝ)) :=
  haveI := hasCompProd_map_of_mem_condDistrib aemeasurable_id aemeasurable_const hη
  compProd_map_condDistrib aemeasurable_id aemeasurable_const hη

-- The law of `X` composed with that representative is the law of `Y`.
example :
    Kernel.piecewise (measurableSet_singleton (0 : ℝ))
        (Kernel.deterministic (fun _ ↦ (0 : ℝ)) measurable_const)
        (Kernel.const ℝ (Measure.count : Measure ℝ)) ∘ₘ (Measure.dirac (0 : ℝ)).map id =
      (Measure.dirac (0 : ℝ)).map fun _ ↦ (0 : ℝ) :=
  condDistrib_comp_map aemeasurable_id aemeasurable_const piecewise_count_mem_condDistrib

-- The pointwise formula for every representative and almost everywhere measurable maps, with the
-- finiteness supplied for a σ-finite law.
example (μ : Measure α) {X Y : α → ℝ} (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    [SigmaFinite (μ.map X hX)] (η : Kernel ℝ ℝ) (hη : η ∈ condDistrib Y X μ) (x : ℝ)
    (hx : μ.map X hX {x} ≠ 0) (s : Set ℝ) :
    η x s = (μ.map X hX {x})⁻¹ * μ.map (fun a ↦ (X a, Y a)) (hX.prodMk hY) ({x} ×ˢ s) :=
  condDistrib_apply_of_ne_zero hX hY hη x hx s

-- A conditional distribution is a representative, for every kernel and a σ-finite law.
example (P : Measure α) {X Y : α → ℝ} (hXY : AEMeasurable (fun a ↦ (X a, Y a)) P)
    [SigmaFinite (P.map X hXY.fst)] (κ : Kernel ℝ ℝ) :
    κ ∈ condDistrib Y X P hXY ↔ HasCondDistrib Y X κ P :=
  mem_condDistrib_iff_hasCondDistrib hXY

-- The class of each joint law suffices to transport membership between them.
example (μ : Measure α) {X X' Y : α → ℝ} (hX : X =ᵐ[μ] X')
    (hXY : AEMeasurable (fun a ↦ (X a, Y a)) μ)
    [(μ.map (fun a ↦ (X a, Y a)) hXY).HasUniqueCondKernel]
    [(μ.map (fun a ↦ (X' a, Y a)) (hXY.congr (hX.prodMk (by rfl)))).HasUniqueCondKernel]
    (η : Kernel ℝ ℝ) :
    η ∈ condDistrib Y X μ hXY ↔ η ∈ condDistrib Y X' μ (hXY.congr (hX.prodMk (by rfl))) :=
  mem_condDistrib_congr_right hX hXY

example (μ : Measure α) {X Y Y' : α → ℝ} (hY : Y =ᵐ[μ] Y')
    (hXY : AEMeasurable (fun a ↦ (X a, Y a)) μ)
    [(μ.map (fun a ↦ (X a, Y a)) hXY).HasUniqueCondKernel]
    [(μ.map (fun a ↦ (X a, Y' a))
      (hXY.congr (Filter.EventuallyEq.rfl.prodMk hY))).HasUniqueCondKernel]
    (η : Kernel ℝ ℝ) :
    η ∈ condDistrib Y X μ hXY ↔
      η ∈ condDistrib Y' X μ (hXY.congr (Filter.EventuallyEq.rfl.prodMk hY)) :=
  mem_condDistrib_congr_left hY hXY

example (μ μ' : Measure α) (h : μ = μ') {X Y : α → ℝ} (hXY : AEMeasurable (fun a ↦ (X a, Y a)) μ)
    [(μ.map (fun a ↦ (X a, Y a)) hXY).HasUniqueCondKernel]
    [(μ'.map (fun a ↦ (X a, Y a)) (h ▸ hXY)).HasUniqueCondKernel] (η : Kernel ℝ ℝ) :
    η ∈ condDistrib Y X μ hXY ↔ η ∈ condDistrib Y X μ' (h ▸ hXY) :=
  mem_condDistrib_congr_measure h hXY

example (ν : Measure ℝ) {f X Y : ℝ → ℝ} (hf : AEMeasurable f ν) (hX : AEMeasurable X (ν.map f))
    (hY : AEMeasurable Y (ν.map f))
    [((ν.map f).map (fun a ↦ (X a, Y a)) (hX.prodMk hY)).HasUniqueCondKernel]
    [(ν.map (fun a ↦ ((X ∘ f) a, (Y ∘ f) a))).HasUniqueCondKernel] (η : Kernel ℝ ℝ) :
    η ∈ condDistrib Y X (ν.map f) ↔ η ∈ condDistrib (Y ∘ f) (X ∘ f) ν :=
  mem_condDistrib_map_iff hf hX hY

-- Scaling the measure by a nonzero factor, which may be infinite, keeps the conditional
-- distribution.
example (μ : Measure α) {X Y : α → ℝ} (hXY : AEMeasurable (fun a ↦ (X a, Y a)) μ)
    [(μ.map (fun a ↦ (X a, Y a)) hXY).HasUniqueCondKernel]
    [(((∞ : ℝ≥0∞) • μ).map (fun a ↦ (X a, Y a)) (hXY.smul_measure ∞)).HasUniqueCondKernel]
    (η : Kernel ℝ ℝ) :
    η ∈ condDistrib Y X ((∞ : ℝ≥0∞) • μ) (hXY.smul_measure ∞) ↔ η ∈ condDistrib Y X μ hXY :=
  mem_condDistrib_smul_iff ENNReal.top_ne_zero hXY

example (μ : Measure ℝ) {X Y : ℝ → ℝ} (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    (h : HasUniqueProduct (volume : Measure ℝ) μ)
    [(((volume : Measure ℝ).prod μ h).map (fun ω ↦ (X ω.2, Y ω.2))).HasUniqueCondKernel]
    [(μ.map (fun a ↦ (X a, Y a)) (hX.prodMk hY)).HasUniqueCondKernel] (η : Kernel ℝ ℝ) :
    η ∈ condDistrib (fun ω ↦ Y ω.2) (fun ω ↦ X ω.2) ((volume : Measure ℝ).prod μ h) ↔
      η ∈ condDistrib Y X μ :=
  mem_condDistrib_snd_prod_iff hX hY volume

-- An infinite factor does not change the conditional distribution either.
example (μ : Measure ℝ) {X Y : ℝ → ℝ} (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    (h : HasUniqueProduct μ (volume : Measure ℝ))
    [((μ.prod (volume : Measure ℝ) h).map (fun ω ↦ (X ω.1, Y ω.1))).HasUniqueCondKernel]
    [(μ.map (fun a ↦ (X a, Y a)) (hX.prodMk hY)).HasUniqueCondKernel] (η : Kernel ℝ ℝ) :
    η ∈ condDistrib (fun ω ↦ Y ω.1) (fun ω ↦ X ω.1) (μ.prod (volume : Measure ℝ) h) ↔
      η ∈ condDistrib Y X μ :=
  mem_condDistrib_fst_prod_iff hX hY volume

-- The integrals against an s-finite representative, for an s-finite law of `X`.
example (μ : Measure α) {X Y : α → ℝ} (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    [(μ.map (fun a ↦ (X a, Y a)) (hX.prodMk hY)).HasUniqueCondKernel] [SFinite (μ.map X hX)]
    (η : Kernel ℝ ℝ) [IsSFiniteKernel η] (hη : η ∈ condDistrib Y X μ) {f : ℝ × ℝ → ℝ}
    (hf : Integrable f (μ.map fun a ↦ (X a, Y a))) :
    Integrable (fun a ↦ ∫ y, f (X a, y) ∂η (X a)) μ :=
  hf.integral_condDistrib hX hY hη

-- The conditional expectation given `X` under an infinite measure whose law of `X` is σ-finite.
example (μ : Measure α) {X Y : α → ℝ} (hX : Measurable X) (hY : Measurable Y)
    [SigmaFinite (μ.map X hX.aemeasurable)] (η : Kernel ℝ ℝ) [IsMarkovKernel η]
    (hη : η ∈ condDistrib Y X μ) {s : Set ℝ} (hs : MeasurableSet s) (hμs : μ (Y ⁻¹' s) ≠ ∞) :
    (fun a ↦ (η (X a)).real s) =ᵐ[μ] μ⟦Y ⁻¹' s | (inferInstance : SigmaAlgebra ℝ).comap X⟧ :=
  condDistrib_ae_eq_condExp hX hY hη hs hμs

example (μ : Measure α) (X : α → ℝ) (hX : Measurable X) :
    SigmaFinite (μ.trim hX.comap_le) ↔ SigmaFinite (μ.map X hX.aemeasurable) :=
  sigmaFinite_trim_comap_iff hX

-- A conditional distribution under a measure that need not be s-finite, for every kernel.
example (P : Measure α) {X Y : α → ℝ} (κ : Kernel ℝ ℝ) (h : HasCondDistrib Y X κ P) {f : ℝ → ℝ}
    (hf : Measurable f) :
    HasCondDistrib (f ∘ Y) X (κ.map f) P :=
  h.comp_left hf

example (P : Measure α) {X : α → ℝ} {Y : α → ℝ × ℝ} (κ : Kernel ℝ (ℝ × ℝ))
    (h : HasCondDistrib Y X κ P) :
    HasCondDistrib (fun a ↦ (Y a).1) X (Kernel.fst κ) P :=
  h.fst

-- Along a measurable equivalence, for every kernel; along a measurable map, on the domain of the
-- composition-product with the law of the image.
example (P : Measure α) {X Y : α → ℝ} (κ : Kernel ℝ ℝ) (h : HasCondDistrib Y X κ P)
    (f : ℝ ≃ᵐ ℝ) :
    HasCondDistrib Y (f ∘ X) (κ.comap f.symm f.symm.measurable) P :=
  h.measurableEquiv_comp_right f

example (P : Measure α) {Y Z : α → ℝ} (κ : Kernel ℝ ℝ) {f : ℝ → ℝ} {hf : Measurable f}
    (h : HasCondDistrib Y Z (κ.comap f hf) P)
    [(P.map (f ∘ Z) (hf.comp_aemeasurable h.aemeasurable_fst)).HasCompProd κ] :
    HasCondDistrib Y (f ∘ Z) κ P :=
  h.comp_right

example (P : Measure α) {X Y Z : α → ℝ} (κ : Kernel ℝ ℝ) (η : Kernel (ℝ × ℝ) ℝ)
    [κ.HasCompProd η] [IsMarkovKernel η]
    (h : HasCondDistrib (fun a ↦ (Y a, Z a)) X (κ ⊗ₖ η) P) :
    HasCondDistrib Z (fun a ↦ (X a, Y a)) η P :=
  h.of_compProd

-- A Markov conditional distribution represents the class of the joint law.
example (P : Measure α) {X Y : α → ℝ} (κ : Kernel ℝ ℝ) [IsMarkovKernel κ]
    (h : HasCondDistrib Y X κ P) [(P.map (fun ω ↦ (X ω, Y ω)) h.aemeasurable).HasUniqueCondKernel] :
    κ ∈ condDistrib Y X P h.aemeasurable :=
  h.mem_condDistrib_of_isMarkovKernel

-- The trajectory kernel represents the conditional distribution of the next point.
example {X : ℕ → Type*} [∀ n, SigmaAlgebra (X n)]
    {κ : (n : ℕ) → Kernel (Π i : Finset.Iic n, X i) (X (n + 1))} [∀ n, IsMarkovKernel (κ n)]
    (μ₀ : Measure (X 0)) [IsProbabilityMeasure μ₀] (a : ℕ) [StandardBorelSpace (X (a + 1))]
    [Nonempty (X (a + 1))] :
    κ a ∈ condDistrib (fun x ↦ x (a + 1)) (Preorder.frestrictLe a) (Kernel.trajMeasure μ₀ κ) :=
  Kernel.mem_condDistrib_trajMeasure

/-! ### The default discharger of `condDistrib`

With a local instance of the class of the joint law, a plain `fun_prop` default fails because the
instance check assigns the proof of measurability first; `fun_prop_default` accepts it. The
reproduction below uses the plain default. -/

/-- A copy of `condDistrib` with the plain `fun_prop` default. -/
def condDistribPlainDefault (μ : Measure α) (X Y : α → ℝ)
    (hXY : AEMeasurable (fun a ↦ (X a, Y a)) μ := by fun_prop)
    [(μ.map (fun a ↦ (X a, Y a)) hXY).HasUniqueCondKernel] :
    Kernel.AEClass (ae (μ.map X hXY.fst)) ℝ :=
  condDistrib Y X μ hXY

/--
error: could not synthesize default value for parameter 'hXY' using tactics
---
error: No goals to be solved
-/
#guard_msgs in
example (μ : Measure α) {X Y : α → ℝ} (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    [(μ.map (fun a ↦ (X a, Y a)) (hX.prodMk hY)).HasUniqueCondKernel] (η : Kernel ℝ ℝ) :
    η ∈ condDistribPlainDefault μ X Y → True :=
  fun _ ↦ trivial

/-! ### Posteriors -/

-- A Markov kernel represents the posterior of any joint law that has a conditional kernel.
example {μ : Measure ℝ} (κ : Kernel ℝ ℝ) [IsMarkovKernel κ]
    [((μ ⊗ₘ κ).map Prod.swap measurable_swap.aemeasurable).HasUniqueCondKernel] (η : Kernel ℝ ℝ)
    [IsMarkovKernel η] :
    η ∈ κ†μ ↔ (κ ∘ₘ μ) ⊗ₘ η = (μ ⊗ₘ κ).map Prod.swap :=
  mem_posterior_iff_of_isMarkovKernel

-- The composition-product with a representative of the posterior exists.
example {μ : Measure ℝ} (κ : Kernel ℝ ℝ) [IsMarkovKernel κ]
    [((μ ⊗ₘ κ).map Prod.swap measurable_swap.aemeasurable).HasUniqueCondKernel] (η : Kernel ℝ ℝ)
    (hη : η ∈ κ†μ) :
    (κ ∘ₘ μ).HasCompProd η :=
  hasCompProd_of_mem_posterior hη

example {μ : Measure ℝ} (κ : Kernel ℝ ℝ) [IsMarkovKernel κ]
    [((μ ⊗ₘ κ).map Prod.swap measurable_swap.aemeasurable).HasUniqueCondKernel] (η : Kernel ℝ ℝ)
    (hη : η ∈ κ†μ) :
    η ∘ₘ κ ∘ₘ μ = μ :=
  posterior_comp_self hη

-- A kernel with the main property, for a σ-finite law of the data.
example {μ : Measure ℝ} (κ : Kernel ℝ ℝ) [IsMarkovKernel κ] [SigmaFinite (κ ∘ₘ μ)]
    (η : Kernel ℝ ℝ) [(κ ∘ₘ μ).HasCompProd η] :
    η ∈ κ†μ ↔ (κ ∘ₘ μ) ⊗ₘ η = (μ ⊗ₘ κ).map Prod.swap :=
  mem_posterior_iff

-- An infinite prior: the posterior of the identity kernel for Lebesgue measure.
example : (Kernel.id : Kernel ℝ ℝ) ∈ (Kernel.id : Kernel ℝ ℝ)†(volume : Measure ℝ) :=
  id_mem_posterior_id volume

-- A prior that is not σ-finite: counting measure on `ℝ`.
example : (Kernel.id : Kernel ℝ ℝ) ∈ (Kernel.id : Kernel ℝ ℝ)†(Measure.count : Measure ℝ) :=
  id_mem_posterior_id Measure.count

-- A deterministic kernel for an infinite prior whose image is σ-finite.
example (f : ℝ → ℝ) (hf : Measurable f) [SigmaFinite ((volume : Measure ℝ).map f)]
    (η : Kernel ℝ ℝ) [IsMarkovKernel η]
    (hη : η ∈ (Kernel.deterministic f hf)†(volume : Measure ℝ)) :
    Kernel.deterministic f hf ∘ₖ η =ᵐ[(volume : Measure ℝ).map f] Kernel.id :=
  deterministic_comp_posterior hf hη

-- The posterior of an infinite prior is absolutely continuous with respect to it, for every
-- representative.
example (κ : Kernel ℝ ℝ) [IsMarkovKernel κ] [SigmaFinite (κ ∘ₘ volume)] {ν : Measure ℝ}
    [SFinite ν] (h_ac : ∀ᵐ ω ∂volume, κ ω ≪ ν) (η : Kernel ℝ ℝ)
    (hη : η ∈ κ†(volume : Measure ℝ)) :
    ∀ᵐ b ∂(κ ∘ₘ volume), η b ≪ volume :=
  absolutelyContinuous_posterior h_ac hη

-- The converse needs only an s-finite law of the data, not an s-finite prior.
example {μ : Measure ℝ} (κ : Kernel ℝ ℝ) [IsFiniteKernel κ] [SFinite (κ ∘ₘ μ)]
    [((μ ⊗ₘ κ).map Prod.swap measurable_swap.aemeasurable).HasUniqueCondKernel]
    (η : Kernel ℝ ℝ) (hη : η ∈ κ†μ) (h_ac : ∀ᵐ b ∂(κ ∘ₘ μ), η b ≪ μ) :
    ∀ᵐ ω ∂μ, κ ω ≪ κ ∘ₘ μ :=
  absolutelyContinuous_of_posterior hη h_ac

example {μ : Measure ℝ} (κ : Kernel ℝ ℝ) [IsFiniteKernel κ] [SFinite (κ ∘ₘ μ)]
    [((μ ⊗ₘ κ).map Prod.swap measurable_swap.aemeasurable).HasUniqueCondKernel]
    (η : Kernel ℝ ℝ) (hη : η ∈ κ†μ) :
    (∀ᵐ b ∂(κ ∘ₘ μ), η b ≪ μ) ↔ ∀ᵐ ω ∂μ, κ ω ≪ κ ∘ₘ μ :=
  absolutelyContinuous_posterior_iff hη

-- In a countable space the posterior has a density with respect to the prior, with no measurable
-- singletons.
example {Ω : Type*} [Countable Ω] [SigmaAlgebra Ω] (κ : Kernel Ω ℝ) [IsFiniteKernel κ]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    [((μ ⊗ₘ κ).map Prod.swap measurable_swap.aemeasurable).HasUniqueCondKernel]
    {η : Kernel ℝ Ω} [IsMarkovKernel η] (hη : η ∈ κ†μ) :
    ∀ᵐ x ∂(κ ∘ₘ μ), η x = μ.withDensity (fun ω ↦ (κ ω).rnDeriv (κ ∘ₘ μ) x) :=
  posterior_eq_withDensity_of_countable κ μ hη

-- The posterior is involutive and contravariant for an infinite prior.
example (κ : Kernel ℝ ℝ) [IsMarkovKernel κ] [SigmaFinite (κ ∘ₘ volume)] (η : Kernel ℝ ℝ)
    [IsMarkovKernel η]
    [((Measure.bind volume κ κ.aemeasurable ⊗ₘ η).map Prod.swap
      measurable_swap.aemeasurable).HasUniqueCondKernel]
    (hη : η ∈ κ†(volume : Measure ℝ)) :
    κ ∈ η†(Measure.bind volume κ κ.aemeasurable) :=
  mem_posterior_posterior hη

example (κ : Kernel ℝ ℝ) [IsMarkovKernel κ] [SigmaFinite (κ ∘ₘ volume)] (η : Kernel ℝ ℝ)
    [IsMarkovKernel η]
    [((Measure.bind volume κ κ.aemeasurable ⊗ₘ η).map Prod.swap
      measurable_swap.aemeasurable).HasUniqueCondKernel]
    [(((volume : Measure ℝ) ⊗ₘ (η ∘ₖ κ)).map Prod.swap
      measurable_swap.aemeasurable).HasUniqueCondKernel]
    (ξ : Kernel ℝ ℝ) [IsMarkovKernel ξ] (hξ : ξ ∈ κ†(volume : Measure ℝ)) (ζ : Kernel ℝ ℝ)
    [IsMarkovKernel ζ] (hζ : ζ ∈ η†(Measure.bind volume κ κ.aemeasurable)) :
    ξ ∘ₖ ζ ∈ (η ∘ₖ κ)†(volume : Measure ℝ) :=
  comp_mem_posterior_comp hξ hζ

/-! ### Composition identities -/

/--
info: Unknown constant `ProbabilityTheory.Kernel.absolutelyContinuous_comp_of_absolutelyContinuous`
-/
#guard_msgs in
#check_failure ProbabilityTheory.Kernel.absolutelyContinuous_comp_of_absolutelyContinuous

/-- info: Unknown identifier `ProbabilityTheory.condDistrib_congr` -/
#guard_msgs in
#check_failure ProbabilityTheory.condDistrib_congr

/-- info: Unknown identifier `ProbabilityTheory.condDistrib_congr_right` -/
#guard_msgs in
#check_failure ProbabilityTheory.condDistrib_congr_right

/-- info: Unknown identifier `ProbabilityTheory.condDistrib_congr_left` -/
#guard_msgs in
#check_failure ProbabilityTheory.condDistrib_congr_left

/-- info: Unknown identifier `ProbabilityTheory.condDistrib_congr_measure` -/
#guard_msgs in
#check_failure ProbabilityTheory.condDistrib_congr_measure

/-- info: Unknown identifier `ProbabilityTheory.condDistrib_map` -/
#guard_msgs in
#check_failure ProbabilityTheory.condDistrib_map

/-- info: Unknown identifier `ProbabilityTheory.condDistrib_fst_prod` -/
#guard_msgs in
#check_failure ProbabilityTheory.condDistrib_fst_prod

/-- info: Unknown identifier `ProbabilityTheory.condDistrib_snd_prod` -/
#guard_msgs in
#check_failure ProbabilityTheory.condDistrib_snd_prod

/-- info: Unknown constant `ProbabilityTheory.Kernel.IsCondKernel.isProbabilityMeasure_ae` -/
#guard_msgs in
#check_failure ProbabilityTheory.Kernel.IsCondKernel.isProbabilityMeasure_ae

/-- info: Unknown constant `ProbabilityTheory.Kernel.IsCondKernel.isCondKernel_comap` -/
#guard_msgs in
#check_failure ProbabilityTheory.Kernel.IsCondKernel.isCondKernel_comap

/-- info: Unknown constant `ProbabilityTheory.Kernel.IsCondKernel.comap_mem_condKernel` -/
#guard_msgs in
#check_failure ProbabilityTheory.Kernel.IsCondKernel.comap_mem_condKernel

/-- info: Unknown constant `ProbabilityTheory.Kernel.comap_mem_condKernel_of_mem` -/
#guard_msgs in
#check_failure ProbabilityTheory.Kernel.comap_mem_condKernel_of_mem

-- No structure on the spaces and no finiteness of the measure or the kernel are needed.
example {β : Type*} {mβ : SigmaAlgebra β} (μ : Measure α) (κ : Kernel α β) {ξ : Measure β}
    [SFinite ξ] (h_ac : ∀ᵐ ω ∂μ, κ ω ≪ ξ) :
    ∀ᵐ ω ∂μ, κ ω ≪ κ ∘ₘ μ :=
  Measure.absolutelyContinuous_comp_of_absolutelyContinuous h_ac

-- In a countable space, with no measurable singletons.
example {Ω : Type*} [Countable Ω] [SigmaAlgebra Ω] (μ : Measure Ω) (κ : Kernel Ω ℝ) :
    ∀ᵐ ω ∂μ, κ ω ≪ κ ∘ₘ μ :=
  Measure.absolutelyContinuous_comp_of_countable

-- Counting measure on `ℝ` is not s-finite.
example (f : ℝ → ℝ) (hf : Measurable f) :
    (Measure.count : Measure ℝ) ⊗ₘ Kernel.deterministic f hf =
      Measure.count.map (fun a ↦ (a, f a)) :=
  Measure.compProd_deterministic hf

example (κ : Kernel ℝ ℝ) [IsSFiniteKernel κ] :
    (Measure.count : Measure ℝ) ⊗ₘ κ = (Kernel.id ×ₖ κ) ∘ₘ Measure.count :=
  Measure.compProd_eq_comp_prod _ κ

example (κ : Kernel ℝ ℝ) [IsSFiniteKernel κ] :
    (Measure.count : Measure ℝ) ⊗ₘ κ = (Kernel.id ∥ₖ κ) ∘ₘ Kernel.copy ℝ ∘ₘ Measure.count :=
  Measure.compProd_eq_parallelComp_comp_copy_comp

example (κ η : Kernel ℝ ℝ) [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    (Kernel.id ∥ₖ η) ∘ₘ ((Measure.count : Measure ℝ) ⊗ₘ κ) = Measure.count ⊗ₘ (η ∘ₖ κ) :=
  Measure.parallelComp_comp_compProd

example (κ : Kernel ℝ ℝ) [IsSFiniteKernel κ] {f : ℝ → ℝ} (hf : Measurable f) :
    (Measure.count : Measure ℝ) ⊗ₘ κ.map f = (Measure.count ⊗ₘ κ).map (Prod.map id f) :=
  Measure.compProd_map hf

-- The image of a kernel for which the composition-product exists, and a kernel that agrees with
-- it almost everywhere.
example (μ : Measure ℝ) (κ : Kernel ℝ ℝ) [μ.HasCompProd κ] {f : ℝ → ℝ} (hf : Measurable f) :
    μ ⊗ₘ κ.map f = (μ ⊗ₘ κ).map (Prod.map id f) :=
  Measure.compProd_map hf

example (μ : Measure ℝ) (κ η : Kernel ℝ ℝ) [μ.HasCompProd κ] (h : κ =ᵐ[μ] η) :
    μ.HasCompProd η :=
  .congr h

example (μ : Measure ℝ) (κ : Kernel ℝ ℝ) [μ.HasCompProd κ] (e : ℝ ≃ᵐ ℝ) :
    (μ.map e e.measurable.aemeasurable).HasCompProd (κ.comap e.symm e.symm.measurable) :=
  .map_measurableEquiv e

-- The lower integral against an image measure, for a function with a measurable almost everywhere
-- majorant with the same integral.
example (μ : Measure ℝ) {g : ℝ → ℝ} (hg : AEMeasurable g μ) {f F : ℝ → ℝ≥0∞} (hF : Measurable F)
    (hfF : f ≤ᵐ[μ.map g hg] F) (h_eq : ∫⁻ b, f b ∂μ.map g hg = ∫⁻ b, F b ∂μ.map g hg) :
    ∫⁻ b, f b ∂μ.map g hg = ∫⁻ a, f (g a) ∂μ :=
  lintegral_map_of_exists_measurable_ge hg ⟨F, hF, hfF, h_eq⟩

example (κ : Kernel ℝ ℝ) (η η' : Kernel (ℝ × ℝ) ℝ) [κ.HasCompProd η]
    (h : ∀ a, ∀ᵐ b ∂(κ a), η (a, b) = η' (a, b)) :
    κ.HasCompProd η' :=
  .congr h

-- Agreement of the measures of the sections of each measurable set suffices.
example (μ : Measure ℝ) (κ η : Kernel ℝ ℝ) [μ.HasCompProd κ]
    (h : ∀ ⦃s : Set (ℝ × ℝ)⦄, MeasurableSet s →
      (fun a ↦ κ a (Prod.mk a ⁻¹' s)) =ᵐ[μ] fun a ↦ η a (Prod.mk a ⁻¹' s)) :
    haveI : μ.HasCompProd η := .congr_sections h
    μ ⊗ₘ κ = μ ⊗ₘ η :=
  haveI : μ.HasCompProd η := .congr_sections h
  Measure.compProd_congr_sections h

example (κ : Kernel ℝ ℝ) (η η' : Kernel (ℝ × ℝ) ℝ) [κ.HasCompProd η]
    (h : ∀ a ⦃s : Set (ℝ × ℝ)⦄, MeasurableSet s →
      (fun b ↦ η (a, b) (Prod.mk b ⁻¹' s)) =ᵐ[κ a] fun b ↦ η' (a, b) (Prod.mk b ⁻¹' s)) :
    haveI : κ.HasCompProd η' := .congr_sections h
    κ ⊗ₖ η = κ ⊗ₖ η' :=
  haveI : κ.HasCompProd η' := .congr_sections h
  Kernel.compProd_congr_sections h

-- A density that is almost everywhere measurable, and finite almost everywhere for only one of the
-- measures, can be divided out.
example (ν ν' : Measure ℝ) {f : ℝ → ℝ≥0∞} (hf : AEMeasurable f (ν + ν'))
    (hf₀ : ∀ᵐ a ∂ν, f a ≠ 0) (hf₀' : ∀ᵐ a ∂ν', f a ≠ 0) (hf_top : ∀ᵐ a ∂ν, f a ≠ ∞)
    (h : ν.withDensity f = ν'.withDensity f) :
    ν = ν' :=
  Measure.eq_of_withDensity_eq hf hf₀ hf₀' hf_top h

example (μ ν : Measure ℝ) (h : μ = ν) (κ : Kernel ℝ ℝ) [μ.HasCompProd κ] [ν.HasCompProd κ] :
    μ ⊗ₘ κ = ν ⊗ₘ κ :=
  Measure.compProd_congr_measure h

example (κ : Kernel ℝ ℝ) [IsMarkovKernel κ] (g : ℝ → ℝ) (hg : Measurable g) :
    κ =ᵐ[(Measure.count : Measure ℝ)] Kernel.deterministic g hg ↔
      ∀ s, MeasurableSet s → ∀ᵐ a ∂(Measure.count : Measure ℝ), g a ∉ s → κ a s = 0 :=
  Kernel.ae_eq_deterministic_iff hg

example {β : Type*} {mβ : SigmaAlgebra β} {ν₁ ν₂ : Measure α} (h : ν₁ = ν₂) {g : α → β}
    (h₁ : AEMeasurable g ν₁) (h₂ : AEMeasurable g ν₂) :
    ν₁.map g h₁ = ν₂.map g h₂ :=
  Measure.map_congr_measure h h₁ h₂

end
