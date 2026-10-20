/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Kexing Ying
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.Probability.Process.Predictable
public import Mathlib.Probability.Process.Stopping

/-!
# Martingales

A family of functions `f : ι → Ω → E` is a martingale with respect to a filtration `ℱ` if `f` is
strongly adapted with respect to `ℱ`, every `f i` is integrable, and for all `i ≤ j`, `f i` is a
conditional expectation of `f j` given `ℱ i` (`MeasureTheory.IsCondExp`), that is,
`μ[f j | ℱ i] = f i`. On the other hand, `f : ι → Ω → E` is a supermartingale with respect to `ℱ`
if `f` is strongly adapted, every `f i` is integrable, and for all `i ≤ j`, `f j` has a conditional
expectation given `ℱ i` that is almost everywhere at most `f i`, that is, `μ[f j | ℱ i] ≤ f i`.
Finally, `f` is a submartingale if it satisfies the reverse inequality `f i ≤ μ[f j | ℱ i]`.

The definitions of supermartingales and submartingales require their conditional expectations to
exist. They do when `μ` is σ-finite on every `ℱ i` (`MeasureTheory.SigmaFiniteFiltration`), for
example for a finite measure. Conditional expectations of integrable functions are unique almost
everywhere, so the inequalities then hold for every conditional expectation
(`MeasureTheory.Supermartingale.isCondExp_ae_le`, `MeasureTheory.Submartingale.ae_le_isCondExp`).
A martingale is its own conditional expectation, so no σ-finiteness is needed for martingales.

### Definitions

* `MeasureTheory.Martingale f ℱ μ`: `f` is a martingale with respect to filtration `ℱ` and
  measure `μ`.
* `MeasureTheory.Supermartingale f ℱ μ`: `f` is a supermartingale with respect to
  filtration `ℱ` and measure `μ`.
* `MeasureTheory.Submartingale f ℱ μ`: `f` is a submartingale with respect to filtration `ℱ` and
  measure `μ`.

### Results

* `MeasureTheory.martingale_of_isCondExp`: strongly adapted conditional expectations of an
  integrable function `f` given the σ-algebras `ℱ i` form a martingale with respect to `ℱ`.
* `MeasureTheory.exists_martingale_isCondExp`: they exist for a σ-finite filtration.

-/

@[expose] public section


open Filter

open scoped NNReal ENNReal MeasureTheory ProbabilityTheory

namespace MeasureTheory

variable {Ω E ι : Type*} [Preorder ι] {m0 : SigmaAlgebra Ω} {μ : Measure Ω}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {f g : ι → Ω → E}
  {ℱ : Filtration ι m0}

/-- A family of functions `f : ι → Ω → E` is a martingale with respect to a filtration `ℱ` if `f`
is strongly adapted with respect to `ℱ`, every `f i` is integrable, and for all `i ≤ j`, `f i` is a
conditional expectation of `f j` given `ℱ i`. -/
def Martingale (f : ι → Ω → E) (ℱ : Filtration ι m0) (μ : Measure Ω) : Prop :=
  StronglyAdapted ℱ f ∧ (∀ i j, i ≤ j → IsCondExp (ℱ i) μ (f j) (f i)) ∧ ∀ i, Integrable (f i) μ

/-- A family of integrable functions `f : ι → Ω → E` is a supermartingale with respect to a
filtration `ℱ` if `f` is strongly adapted with respect to `ℱ` and for all `i ≤ j`, `f j` has a
conditional expectation given `ℱ i` that is almost everywhere at most `f i`. The existence of the
conditional expectation is part of the definition; it is automatic for a σ-finite filtration
(`MeasureTheory.SigmaFiniteFiltration`). -/
def Supermartingale [LE E] (f : ι → Ω → E) (ℱ : Filtration ι m0) (μ : Measure Ω) : Prop :=
  StronglyAdapted ℱ f ∧ (∀ i j, i ≤ j → ∃ g, IsCondExp (ℱ i) μ (f j) g ∧ g ≤ᵐ[μ] f i) ∧
    ∀ i, Integrable (f i) μ

/-- A family of integrable functions `f : ι → Ω → E` is a submartingale with respect to a
filtration `ℱ` if `f` is strongly adapted with respect to `ℱ` and for all `i ≤ j`, `f j` has a
conditional expectation given `ℱ i` that is almost everywhere at least `f i`. The existence of the
conditional expectation is part of the definition; it is automatic for a σ-finite filtration
(`MeasureTheory.SigmaFiniteFiltration`). -/
def Submartingale [LE E] (f : ι → Ω → E) (ℱ : Filtration ι m0) (μ : Measure Ω) : Prop :=
  StronglyAdapted ℱ f ∧ (∀ i j, i ≤ j → ∃ g, IsCondExp (ℱ i) μ (f j) g ∧ f i ≤ᵐ[μ] g) ∧
    ∀ i, Integrable (f i) μ

theorem martingale_const (ℱ : Filtration ι m0) (μ : Measure Ω) [IsFiniteMeasure μ] (x : E) :
    Martingale (fun _ _ => x) ℱ μ :=
  ⟨stronglyAdapted_const ℱ _, fun _ _ _ => isCondExp_const x, fun _ => integrable_const x⟩

theorem martingale_const_fun [OrderBot ι] (ℱ : Filtration ι m0) (μ : Measure Ω)
    {f : Ω → E} (hf : StronglyMeasurable[ℱ ⊥] f) (hfint : Integrable f μ) :
    Martingale (fun _ => f) ℱ μ :=
  ⟨fun _ => hf.mono <| ℱ.mono bot_le,
    fun _ _ _ => isCondExp_self (hf.mono <| ℱ.mono bot_le).aestronglyMeasurable, fun _ => hfint⟩

variable (E) in
theorem martingale_zero (ℱ : Filtration ι m0) (μ : Measure Ω) : Martingale (0 : ι → Ω → E) ℱ μ :=
  ⟨stronglyAdapted_zero E ℱ, fun _ _ _ => IsCondExp.zero, fun _ => integrable_zero _ _ _⟩

namespace Martingale

protected theorem stronglyAdapted (hf : Martingale f ℱ μ) : StronglyAdapted ℱ f :=
  hf.1

protected theorem stronglyMeasurable (hf : Martingale f ℱ μ) (i : ι) :
    StronglyMeasurable[ℱ i] (f i) :=
  hf.stronglyAdapted i

/-- For `i ≤ j`, `f i` is a conditional expectation of `f j` given `ℱ i`. -/
protected theorem isCondExp (hf : Martingale f ℱ μ) {i j : ι} (hij : i ≤ j) :
    IsCondExp (ℱ i) μ (f j) (f i) :=
  hf.2.1 i j hij

protected theorem integrable (hf : Martingale f ℱ μ) (i : ι) : Integrable (f i) μ :=
  hf.2.2 i

/-- For `i ≤ j`, every conditional expectation of `f j` given `ℱ i` is almost everywhere equal to
`f i`. -/
theorem ae_eq_of_isCondExp (hf : Martingale f ℱ μ) {i j : ι} (hij : i ≤ j) {g : Ω → E}
    (hg : IsCondExp (ℱ i) μ (f j) g) : g =ᵐ[μ] f i :=
  hg.ae_eq (ℱ.le i) (hf.integrable j) (hf.isCondExp hij)

protected theorem hasUniqueCondExp (hf : Martingale f ℱ μ) {i j : ι} (hij : i ≤ j) :
    HasUniqueCondExp (ℱ i) μ (f j) :=
  .of_isCondExp (ℱ.le i) (hf.integrable j) (hf.isCondExp hij)

/-- `μ[f j | ℱ i] = f i` for `i ≤ j`. -/
theorem condExp_eq (hf : Martingale f ℱ μ) {i j : ι} (hij : i ≤ j)
    (h : HasUniqueCondExp (ℱ i) μ (f j)) : condExp (ℱ i) μ (f j) h = f i :=
  (hf.isCondExp hij).condExp_eq h

theorem setIntegral_eq (hf : Martingale f ℱ μ) {i j : ι} (hij : i ≤ j) {s : Set Ω}
    (hs : s ∈ ℱ i) : ∫ ω in s, f i ω ∂μ = ∫ ω in s, f j ω ∂μ :=
  (hf.isCondExp hij).setIntegral_eq s hs (hf.integrable j).integrableOn

lemma congr (hf : Martingale f ℱ μ) (hg : StronglyAdapted ℱ g) (h_eq : ∀ t, f t =ᵐ[μ] g t) :
    Martingale g ℱ μ :=
  ⟨hg, fun _ j hij ↦ (hf.isCondExp hij).congr (h_eq j) (h_eq _),
    fun i ↦ (hf.integrable i).congr (h_eq i)⟩

theorem add (hf : Martingale f ℱ μ) (hg : Martingale g ℱ μ) : Martingale (f + g) ℱ μ :=
  ⟨hf.stronglyAdapted.add hg.stronglyAdapted,
    fun _ j hij => (hf.isCondExp hij).add (hg.isCondExp hij) (hf.integrable j) (hg.integrable j),
    fun i => (hf.integrable i).add (hg.integrable i)⟩

theorem neg (hf : Martingale f ℱ μ) : Martingale (-f) ℱ μ :=
  ⟨hf.stronglyAdapted.neg, fun _ _ hij => (hf.isCondExp hij).neg,
    fun i => (hf.integrable i).neg⟩

theorem sub (hf : Martingale f ℱ μ) (hg : Martingale g ℱ μ) : Martingale (f - g) ℱ μ := by
  rw [sub_eq_add_neg]; exact hf.add hg.neg

theorem smul (c : ℝ) (hf : Martingale f ℱ μ) : Martingale (c • f) ℱ μ :=
  ⟨hf.stronglyAdapted.smul c, fun _ _ hij => (hf.isCondExp hij).smul c,
    fun i => (hf.integrable i).smul c⟩

theorem supermartingale [Preorder E] (hf : Martingale f ℱ μ) : Supermartingale f ℱ μ :=
  ⟨hf.1, fun i _ hij => ⟨f i, hf.isCondExp hij, .rfl⟩, hf.integrable⟩

theorem submartingale [Preorder E] (hf : Martingale f ℱ μ) : Submartingale f ℱ μ :=
  ⟨hf.1, fun i _ hij => ⟨f i, hf.isCondExp hij, .rfl⟩, hf.integrable⟩

end Martingale

/-- Strongly adapted conditional expectations of an integrable function `f` given the σ-algebras
`ℱ i` of a filtration form a martingale. -/
theorem martingale_of_isCondExp {f : Ω → E} (hf : Integrable f μ) {g : ι → Ω → E}
    (hg_adapted : StronglyAdapted ℱ g) (hg : ∀ i, IsCondExp (ℱ i) μ f (g i)) :
    Martingale g ℱ μ := by
  refine ⟨hg_adapted, fun i j hij => ⟨(hg i).aestronglyMeasurable,
    fun _ _ _ => ((hg i).integrable hf).integrableOn, fun s hs _ => ?_⟩,
    fun i => (hg i).integrable hf⟩
  rw [(hg i).setIntegral_eq s hs hf.integrableOn,
    (hg j).setIntegral_eq s (ℱ.mono hij hs) hf.integrableOn]

/-- For a σ-finite filtration, an integrable function `f` has strongly adapted conditional
expectations given the σ-algebras `ℱ i`, and they form a martingale. -/
theorem exists_martingale_isCondExp [SigmaFiniteFiltration μ ℱ] {f : Ω → E}
    (hf : Integrable f μ) : ∃ g : ι → Ω → E, Martingale g ℱ μ ∧ ∀ i, IsCondExp (ℱ i) μ f (g i) := by
  choose g hgm hg using fun i ↦ exists_stronglyMeasurable_isCondExp (μ := μ) (ℱ.le i) hf
  exact ⟨g, martingale_of_isCondExp hf hgm hg, hg⟩

theorem martingale_iff [PartialOrder E] :
    Martingale f ℱ μ ↔ Supermartingale f ℱ μ ∧ Submartingale f ℱ μ := by
  refine ⟨fun hf => ⟨hf.supermartingale, hf.submartingale⟩,
    fun ⟨hf₁, hf₂⟩ => ⟨hf₁.1, fun i j hij => ?_, hf₁.2.2⟩⟩
  obtain ⟨g₁, hg₁, hle₁⟩ := hf₁.2.1 i j hij
  obtain ⟨g₂, hg₂, hle₂⟩ := hf₂.2.1 i j hij
  refine hg₁.congr_right ?_
  filter_upwards [hle₁, hle₂, hg₁.ae_eq (ℱ.le i) (hf₁.2.2 j) hg₂] with ω h₁ h₂ h₁₂
  exact le_antisymm h₁ (by rw [h₁₂]; exact h₂)

namespace Supermartingale

protected theorem stronglyAdapted [LE E] (hf : Supermartingale f ℱ μ) : StronglyAdapted ℱ f :=
  hf.1

protected theorem stronglyMeasurable [LE E] (hf : Supermartingale f ℱ μ) (i : ι) :
    StronglyMeasurable[ℱ i] (f i) :=
  hf.stronglyAdapted i

protected theorem integrable [LE E] (hf : Supermartingale f ℱ μ) (i : ι) : Integrable (f i) μ :=
  hf.2.2 i

/-- For `i ≤ j`, `f j` has a conditional expectation given `ℱ i` that is almost everywhere at most
`f i`. -/
theorem exists_isCondExp_ae_le [LE E] (hf : Supermartingale f ℱ μ) {i j : ι} (hij : i ≤ j) :
    ∃ g, IsCondExp (ℱ i) μ (f j) g ∧ g ≤ᵐ[μ] f i :=
  hf.2.1 i j hij

/-- For `i ≤ j`, every conditional expectation of `f j` given `ℱ i` is almost everywhere at most
`f i`. -/
theorem isCondExp_ae_le [Preorder E] (hf : Supermartingale f ℱ μ) {i j : ι} (hij : i ≤ j)
    {g : Ω → E} (hg : IsCondExp (ℱ i) μ (f j) g) : g ≤ᵐ[μ] f i := by
  obtain ⟨g', hg', hle⟩ := hf.exists_isCondExp_ae_le hij
  exact (hg.ae_eq (ℱ.le i) (hf.integrable j) hg').trans_le hle

protected theorem hasUniqueCondExp [LE E] (hf : Supermartingale f ℱ μ) {i j : ι} (hij : i ≤ j) :
    HasUniqueCondExp (ℱ i) μ (f j) :=
  let ⟨_, hg, _⟩ := hf.exists_isCondExp_ae_le hij
  .of_isCondExp (ℱ.le i) (hf.integrable j) hg

/-- `μ[f j | ℱ i] ≤ f i` for `i ≤ j`. -/
theorem condExp_le [LE E] (hf : Supermartingale f ℱ μ) {i j : ι} (hij : i ≤ j)
    (h : HasUniqueCondExp (ℱ i) μ (f j)) : condExp (ℱ i) μ (f j) h ≤ f i := by
  obtain ⟨g, hg, hle⟩ := hf.exists_isCondExp_ae_le hij
  rw [hg.condExp_eq h]
  exact Germ.coe_le.2 hle

theorem setIntegral_le [PartialOrder E] [IsOrderedAddMonoid E] [IsOrderedModule ℝ E]
    [ClosedIciTopology E] {f : ι → Ω → E} (hf : Supermartingale f ℱ μ) {i j : ι} (hij : i ≤ j)
    {s : Set Ω} (hs : s ∈ ℱ i) : ∫ ω in s, f j ω ∂μ ≤ ∫ ω in s, f i ω ∂μ := by
  obtain ⟨g, hg, hle⟩ := hf.exists_isCondExp_ae_le hij
  rw [← hg.setIntegral_eq s hs (hf.integrable j).integrableOn]
  exact setIntegral_mono_ae (hg.integrable (hf.integrable j)).integrableOn
    (hf.integrable i).integrableOn hle

lemma congr [LE E] (hf : Supermartingale f ℱ μ) (hg : StronglyAdapted ℱ g)
    (h_eq : ∀ t, f t =ᵐ[μ] g t) : Supermartingale g ℱ μ := by
  refine ⟨hg, fun i j hij ↦ ?_, fun i ↦ (integrable_congr (h_eq i)).mp (hf.integrable i)⟩
  obtain ⟨k, hk, hle⟩ := hf.exists_isCondExp_ae_le hij
  refine ⟨k, hk.congr_left (h_eq j), ?_⟩
  filter_upwards [hle, h_eq i] with ω h_le h_eq
  rwa [← h_eq]

theorem add [Preorder E] [AddLeftMono E] (hf : Supermartingale f ℱ μ)
    (hg : Supermartingale g ℱ μ) : Supermartingale (f + g) ℱ μ := by
  refine ⟨hf.1.add hg.1, fun i j hij => ?_, fun i => (hf.2.2 i).add (hg.2.2 i)⟩
  obtain ⟨k, hk, hk_le⟩ := hf.exists_isCondExp_ae_le hij
  obtain ⟨k', hk', hk'_le⟩ := hg.exists_isCondExp_ae_le hij
  refine ⟨k + k', hk.add hk' (hf.integrable j) (hg.integrable j), ?_⟩
  filter_upwards [hk_le, hk'_le] with ω h₁ h₂
  exact add_le_add h₁ h₂

theorem add_martingale [Preorder E] [AddLeftMono E]
    (hf : Supermartingale f ℱ μ) (hg : Martingale g ℱ μ) : Supermartingale (f + g) ℱ μ :=
  hf.add hg.supermartingale

theorem neg [Preorder E] [AddLeftMono E] (hf : Supermartingale f ℱ μ) :
    Submartingale (-f) ℱ μ := by
  refine ⟨hf.1.neg, fun i j hij => ?_, fun i => (hf.2.2 i).neg⟩
  obtain ⟨k, hk, hle⟩ := hf.exists_isCondExp_ae_le hij
  refine ⟨-k, hk.neg, ?_⟩
  filter_upwards [hle] with ω hω
  simpa using hω

end Supermartingale

namespace Submartingale

protected theorem stronglyAdapted [LE E] (hf : Submartingale f ℱ μ) : StronglyAdapted ℱ f :=
  hf.1

protected theorem stronglyMeasurable [LE E] (hf : Submartingale f ℱ μ) (i : ι) :
    StronglyMeasurable[ℱ i] (f i) :=
  hf.stronglyAdapted i

protected theorem integrable [LE E] (hf : Submartingale f ℱ μ) (i : ι) : Integrable (f i) μ :=
  hf.2.2 i

/-- For `i ≤ j`, `f j` has a conditional expectation given `ℱ i` that is almost everywhere at least
`f i`. -/
theorem exists_ae_le_isCondExp [LE E] (hf : Submartingale f ℱ μ) {i j : ι} (hij : i ≤ j) :
    ∃ g, IsCondExp (ℱ i) μ (f j) g ∧ f i ≤ᵐ[μ] g :=
  hf.2.1 i j hij

/-- For `i ≤ j`, every conditional expectation of `f j` given `ℱ i` is almost everywhere at least
`f i`. -/
theorem ae_le_isCondExp [Preorder E] (hf : Submartingale f ℱ μ) {i j : ι} (hij : i ≤ j)
    {g : Ω → E} (hg : IsCondExp (ℱ i) μ (f j) g) : f i ≤ᵐ[μ] g := by
  obtain ⟨g', hg', hle⟩ := hf.exists_ae_le_isCondExp hij
  exact hle.trans_eq (hg'.ae_eq (ℱ.le i) (hf.integrable j) hg)

protected theorem hasUniqueCondExp [LE E] (hf : Submartingale f ℱ μ) {i j : ι} (hij : i ≤ j) :
    HasUniqueCondExp (ℱ i) μ (f j) :=
  let ⟨_, hg, _⟩ := hf.exists_ae_le_isCondExp hij
  .of_isCondExp (ℱ.le i) (hf.integrable j) hg

/-- `f i ≤ μ[f j | ℱ i]` for `i ≤ j`. -/
theorem le_condExp [LE E] (hf : Submartingale f ℱ μ) {i j : ι} (hij : i ≤ j)
    (h : HasUniqueCondExp (ℱ i) μ (f j)) : (f i : (ae μ).Germ E) ≤ condExp (ℱ i) μ (f j) h := by
  obtain ⟨g, hg, hle⟩ := hf.exists_ae_le_isCondExp hij
  rw [hg.condExp_eq h]
  exact Germ.coe_le.2 hle

lemma congr [LE E] (hf : Submartingale f ℱ μ) (hg : StronglyAdapted ℱ g)
    (h_eq : ∀ t, f t =ᵐ[μ] g t) : Submartingale g ℱ μ := by
  refine ⟨hg, fun i j hij ↦ ?_, fun i ↦ (integrable_congr (h_eq i)).mp (hf.integrable i)⟩
  obtain ⟨k, hk, hle⟩ := hf.exists_ae_le_isCondExp hij
  refine ⟨k, hk.congr_left (h_eq j), ?_⟩
  filter_upwards [hle, h_eq i] with ω h_le h_eq
  rwa [← h_eq]

theorem add [Preorder E] [AddLeftMono E] (hf : Submartingale f ℱ μ)
    (hg : Submartingale g ℱ μ) : Submartingale (f + g) ℱ μ := by
  refine ⟨hf.1.add hg.1, fun i j hij => ?_, fun i => (hf.2.2 i).add (hg.2.2 i)⟩
  obtain ⟨k, hk, hk_le⟩ := hf.exists_ae_le_isCondExp hij
  obtain ⟨k', hk', hk'_le⟩ := hg.exists_ae_le_isCondExp hij
  refine ⟨k + k', hk.add hk' (hf.integrable j) (hg.integrable j), ?_⟩
  filter_upwards [hk_le, hk'_le] with ω h₁ h₂
  exact add_le_add h₁ h₂

theorem add_martingale [Preorder E] [AddLeftMono E] (hf : Submartingale f ℱ μ)
    (hg : Martingale g ℱ μ) : Submartingale (f + g) ℱ μ :=
  hf.add hg.submartingale

theorem neg [Preorder E] [AddLeftMono E] (hf : Submartingale f ℱ μ) :
    Supermartingale (-f) ℱ μ := by
  refine ⟨hf.1.neg, fun i j hij => ?_, fun i => (hf.2.2 i).neg⟩
  obtain ⟨k, hk, hle⟩ := hf.exists_ae_le_isCondExp hij
  refine ⟨-k, hk.neg, ?_⟩
  filter_upwards [hle] with ω hω
  simpa using hω

/-- The converse of this lemma is `MeasureTheory.submartingale_of_setIntegral_le`. -/
theorem setIntegral_le [PartialOrder E] [IsOrderedAddMonoid E] [IsOrderedModule ℝ E]
    [ClosedIciTopology E] {f : ι → Ω → E} (hf : Submartingale f ℱ μ) {i j : ι} (hij : i ≤ j)
    {s : Set Ω} (hs : s ∈ ℱ i) : ∫ ω in s, f i ω ∂μ ≤ ∫ ω in s, f j ω ∂μ := by
  rw [← neg_le_neg_iff, ← integral_neg, ← integral_neg]
  exact Supermartingale.setIntegral_le hf.neg hij hs

theorem sub_supermartingale [Preorder E] [AddLeftMono E]
    (hf : Submartingale f ℱ μ) (hg : Supermartingale g ℱ μ) : Submartingale (f - g) ℱ μ := by
  rw [sub_eq_add_neg]; exact hf.add hg.neg

theorem sub_martingale [Preorder E] [AddLeftMono E] (hf : Submartingale f ℱ μ)
    (hg : Martingale g ℱ μ) : Submartingale (f - g) ℱ μ :=
  hf.sub_supermartingale hg.supermartingale

/-- The supremum of two submartingales is a submartingale. The conditional expectations of the
supremum exist since the filtration is σ-finite; without σ-finiteness they need not. -/
protected theorem sup [SigmaFiniteFiltration μ ℱ] [Lattice E] [ContinuousSup E] [HasSolidNorm E]
    [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] {f g : ι → Ω → E} (hf : Submartingale f ℱ μ)
    (hg : Submartingale g ℱ μ) : Submartingale (f ⊔ g) ℱ μ := by
  refine ⟨fun i =>
    @StronglyMeasurable.sup _ _ _ _ (ℱ i) _ _ _ (hf.stronglyAdapted i) (hg.stronglyAdapted i),
    fun i j hij => ?_, fun i => Integrable.sup (hf.integrable _) (hg.integrable _)⟩
  have hint : Integrable ((f ⊔ g) j) μ := Integrable.sup (hf.integrable j) (hg.integrable j)
  obtain ⟨k, -, hk⟩ := exists_stronglyMeasurable_isCondExp (ℱ.le i) hint
  refine ⟨k, hk, EventuallyLE.sup_le ?_ ?_⟩
  · obtain ⟨k₁, hk₁, hle₁⟩ := hf.exists_ae_le_isCondExp hij
    exact hle₁.trans (hk₁.mono (ℱ.le i) hk (hf.integrable j) hint
      (.of_forall fun _ => le_sup_left))
  · obtain ⟨k₂, hk₂, hle₂⟩ := hg.exists_ae_le_isCondExp hij
    exact hle₂.trans (hk₂.mono (ℱ.le i) hk (hg.integrable j) hint
      (.of_forall fun _ => le_sup_right))

protected theorem pos [SigmaFiniteFiltration μ ℱ] [Lattice E] [ContinuousSup E] [HasSolidNorm E]
    [IsOrderedAddMonoid E] [IsOrderedModule ℝ E] {f : ι → Ω → E} (hf : Submartingale f ℱ μ) :
    Submartingale (f⁺) ℱ μ :=
  hf.sup (martingale_zero _ _ _).submartingale

end Submartingale

section Submartingale

theorem submartingale_of_setIntegral_le [SigmaFiniteFiltration μ ℱ]
    {f : ι → Ω → ℝ} (hadp : StronglyAdapted ℱ f)
    (hint : ∀ i, Integrable (f i) μ) (hf : ∀ i j : ι,
      i ≤ j → ∀ s : Set Ω, s ∈ ℱ i → ∫ ω in s, f i ω ∂μ ≤ ∫ ω in s, f j ω ∂μ) :
    Submartingale f ℱ μ := by
  refine ⟨hadp, fun i j hij => ?_, hint⟩
  obtain ⟨g, hgm, hg⟩ := exists_stronglyMeasurable_isCondExp (ℱ.le i) (hint j)
  refine ⟨g, hg, ?_⟩
  suffices f i ≤ᵐ[μ.trim (ℱ.le i)] g by exact ae_le_of_ae_le_trim this
  suffices 0 ≤ᵐ[μ.trim (ℱ.le i)] g - f i by
    filter_upwards [this] with x hx
    rwa [← sub_nonneg]
  refine ae_nonneg_of_forall_setIntegral_nonneg
    (((hg.integrable (hint j)).sub (hint i)).trim _ (hgm.sub <| hadp i)) fun s hs _ => ?_
  specialize hf i j hij s hs
  rwa [← setIntegral_trim _ (hgm.sub <| hadp i) hs,
    integral_sub' (hg.integrable (hint j)).integrableOn (hint i).integrableOn, sub_nonneg,
    hg.setIntegral_eq s hs (hint j).integrableOn]

theorem submartingale_of_isCondExp_sub_nonneg [PartialOrder E] [IsOrderedAddMonoid E]
    {f : ι → Ω → E} (hadp : StronglyAdapted ℱ f) (hint : ∀ i, Integrable (f i) μ)
    (hf : ∀ i j, i ≤ j → ∃ g, IsCondExp (ℱ i) μ (f j - f i) g ∧ 0 ≤ᵐ[μ] g) :
    Submartingale f ℱ μ := by
  refine ⟨hadp, fun i j hij => ?_, hint⟩
  obtain ⟨g, hg, hg_nonneg⟩ := hf i j hij
  have h' : IsCondExp (ℱ i) μ (f j) (g + f i) := by
    simpa using hg.add (isCondExp_self (hadp i).aestronglyMeasurable) ((hint j).sub (hint i))
      (hint i)
  refine ⟨g + f i, h', ?_⟩
  filter_upwards [hg_nonneg] with ω hω
  simpa using hω

/-- For `i ≤ j`, every conditional expectation of `f j - f i` given `ℱ i` is almost everywhere
nonnegative. -/
theorem Submartingale.isCondExp_sub_nonneg [PartialOrder E] [IsOrderedAddMonoid E]
    {f : ι → Ω → E} (hf : Submartingale f ℱ μ) {i j : ι} (hij : i ≤ j) {g : Ω → E}
    (hg : IsCondExp (ℱ i) μ (f j - f i) g) : 0 ≤ᵐ[μ] g := by
  have h' : IsCondExp (ℱ i) μ (f j) (g + f i) := by
    simpa using hg.add (isCondExp_self (hf.stronglyAdapted i).aestronglyMeasurable)
      ((hf.integrable j).sub (hf.integrable i)) (hf.integrable i)
  filter_upwards [hf.ae_le_isCondExp hij h'] with ω hω
  simpa using hω

theorem submartingale_iff_isCondExp_sub_nonneg [PartialOrder E] [IsOrderedAddMonoid E]
    {f : ι → Ω → E} :
    Submartingale f ℱ μ ↔ StronglyAdapted ℱ f ∧ (∀ i, Integrable (f i) μ) ∧
      ∀ i j, i ≤ j → ∃ g, IsCondExp (ℱ i) μ (f j - f i) g ∧ 0 ≤ᵐ[μ] g := by
  refine ⟨fun h => ⟨h.stronglyAdapted, h.integrable, fun i j hij => ?_⟩,
    fun ⟨hadp, hint, h⟩ => submartingale_of_isCondExp_sub_nonneg hadp hint h⟩
  obtain ⟨g, hg, -⟩ := h.exists_ae_le_isCondExp hij
  have hg' : IsCondExp (ℱ i) μ (f j - f i) (g - f i) :=
    hg.sub (isCondExp_self (h.stronglyAdapted i).aestronglyMeasurable) (h.integrable j)
      (h.integrable i)
  exact ⟨g - f i, hg', h.isCondExp_sub_nonneg hij hg'⟩

end Submartingale

namespace Supermartingale

theorem sub_submartingale [Preorder E] [AddLeftMono E]
    (hf : Supermartingale f ℱ μ) (hg : Submartingale g ℱ μ) : Supermartingale (f - g) ℱ μ := by
  rw [sub_eq_add_neg]; exact hf.add hg.neg

theorem sub_martingale [Preorder E] [AddLeftMono E]
    (hf : Supermartingale f ℱ μ) (hg : Martingale g ℱ μ) : Supermartingale (f - g) ℱ μ :=
  hf.sub_submartingale hg.submartingale

section

variable {F : Type*} [NormedAddCommGroup F] [PartialOrder F] [NormedSpace ℝ F] [CompleteSpace F]
  [IsOrderedModule ℝ F]

theorem smul_nonneg {f : ι → Ω → F} {c : ℝ} (hc : 0 ≤ c) (hf : Supermartingale f ℱ μ) :
    Supermartingale (c • f) ℱ μ := by
  refine ⟨hf.1.smul c, fun i j hij => ?_, fun i => (hf.2.2 i).smul c⟩
  obtain ⟨g, hg, hle⟩ := hf.exists_isCondExp_ae_le hij
  refine ⟨c • g, hg.smul c, ?_⟩
  filter_upwards [hle] with ω hω
  exact smul_le_smul_of_nonneg_left hω hc

theorem smul_nonpos [IsOrderedAddMonoid F] {f : ι → Ω → F} {c : ℝ}
    (hc : c ≤ 0) (hf : Supermartingale f ℱ μ) :
    Submartingale (c • f) ℱ μ := by
  rw [← neg_neg c, neg_smul]
  exact (hf.smul_nonneg <| neg_nonneg.2 hc).neg

end

end Supermartingale

namespace Submartingale

section

variable {F : Type*} [NormedAddCommGroup F] [PartialOrder F] [IsOrderedAddMonoid F]
  [NormedSpace ℝ F] [CompleteSpace F] [IsOrderedModule ℝ F]

theorem smul_nonneg {f : ι → Ω → F} {c : ℝ} (hc : 0 ≤ c) (hf : Submartingale f ℱ μ) :
    Submartingale (c • f) ℱ μ := by
  rw [← neg_neg (c • f), ← smul_neg]
  exact Supermartingale.neg (hf.neg.smul_nonneg hc)

theorem smul_nonpos {f : ι → Ω → F} {c : ℝ} (hc : c ≤ 0) (hf : Submartingale f ℱ μ) :
    Supermartingale (c • f) ℱ μ := by
  rw [← neg_neg c, neg_smul]
  exact (hf.smul_nonneg <| neg_nonneg.2 hc).neg

end

end Submartingale

section Nat

variable {𝒢 : Filtration ℕ m0}

section SubSuper

section OfSetIntegral

theorem submartingale_of_setIntegral_le_succ [SigmaFiniteFiltration μ 𝒢] {f : ℕ → Ω → ℝ}
    (hadp : StronglyAdapted 𝒢 f) (hint : ∀ i, Integrable (f i) μ)
    (hf : ∀ i, ∀ s : Set Ω, s ∈ 𝒢 i → ∫ ω in s, f i ω ∂μ ≤ ∫ ω in s, f (i + 1) ω ∂μ) :
    Submartingale f 𝒢 μ := by
  refine submartingale_of_setIntegral_le hadp hint fun i j hij s hs => ?_
  induction hij with
  | refl => rfl
  | step hk₁ hk₂ => exact hk₂.trans (hf _ s (𝒢.mono hk₁ hs))

theorem supermartingale_of_setIntegral_succ_le [SigmaFiniteFiltration μ 𝒢] {f : ℕ → Ω → ℝ}
    (hadp : StronglyAdapted 𝒢 f) (hint : ∀ i, Integrable (f i) μ)
    (hf : ∀ i, ∀ s : Set Ω, s ∈ 𝒢 i → ∫ ω in s, f (i + 1) ω ∂μ ≤ ∫ ω in s, f i ω ∂μ) :
    Supermartingale f 𝒢 μ := by
  rw [← neg_neg f]
  refine (submartingale_of_setIntegral_le_succ hadp.neg (fun i => (hint i).neg) ?_).neg
  simpa only [integral_neg, Pi.neg_apply, neg_le_neg_iff]

end OfSetIntegral

section OfSucc

variable [PartialOrder E] [IsOrderedAddMonoid E] [ClosedIciTopology E] [IsOrderedModule ℝ E]

/-- A strongly adapted integrable process `f` such that each `f (i + 1)` has a conditional
expectation given `𝒢 i` at least `f i` is a submartingale, for a σ-finite filtration. -/
theorem submartingale_nat [SigmaFiniteFiltration μ 𝒢] {f : ℕ → Ω → E}
    (hadp : StronglyAdapted 𝒢 f) (hint : ∀ i, Integrable (f i) μ)
    (hf : ∀ i, ∃ g, IsCondExp (𝒢 i) μ (f (i + 1)) g ∧ f i ≤ᵐ[μ] g) :
    Submartingale f 𝒢 μ := by
  refine ⟨hadp, fun i j hij ↦ ?_, hint⟩
  induction j, hij using Nat.le_induction with
  | base => exact ⟨f i, isCondExp_self (hadp i).aestronglyMeasurable, .rfl⟩
  | succ k hik hk =>
    obtain ⟨g, hg, hfg⟩ := hk
    obtain ⟨h, hh, hfh⟩ := hf k
    obtain ⟨q, -, hq⟩ :=
      exists_stronglyMeasurable_isCondExp (𝒢.le i) (hh.integrable (hint (k + 1)))
    exact ⟨q, hh.trans hq (𝒢.mono hik),
      hfg.trans (hg.mono (𝒢.le i) hq (hint k) (hh.integrable (hint (k + 1))) hfh)⟩

/-- A strongly adapted integrable process `f` such that each `f (i + 1)` has a conditional
expectation given `𝒢 i` at most `f i` is a supermartingale, for a σ-finite filtration. -/
theorem supermartingale_nat [SigmaFiniteFiltration μ 𝒢] {f : ℕ → Ω → E}
    (hadp : StronglyAdapted 𝒢 f) (hint : ∀ i, Integrable (f i) μ)
    (hf : ∀ i, ∃ g, IsCondExp (𝒢 i) μ (f (i + 1)) g ∧ g ≤ᵐ[μ] f i) :
    Supermartingale f 𝒢 μ := by
  rw [← neg_neg f]
  refine (submartingale_nat hadp.neg (fun i => (hint i).neg) fun i => ?_).neg
  obtain ⟨g, hg, hle⟩ := hf i
  exact ⟨-g, hg.neg, by filter_upwards [hle] with x hx using neg_le_neg hx⟩

theorem submartingale_of_isCondExp_sub_nonneg_nat [SigmaFiniteFiltration μ 𝒢] {f : ℕ → Ω → E}
    (hadp : StronglyAdapted 𝒢 f) (hint : ∀ i, Integrable (f i) μ)
    (hf : ∀ i, ∃ g, IsCondExp (𝒢 i) μ (f (i + 1) - f i) g ∧ 0 ≤ᵐ[μ] g) :
    Submartingale f 𝒢 μ := by
  refine submartingale_nat hadp hint fun i => ?_
  obtain ⟨g, hg, hg_nonneg⟩ := hf i
  have h' : IsCondExp (𝒢 i) μ (f (i + 1)) (g + f i) := by
    simpa using hg.add (isCondExp_self (hadp i).aestronglyMeasurable)
      ((hint (i + 1)).sub (hint i)) (hint i)
  refine ⟨g + f i, h', ?_⟩
  filter_upwards [hg_nonneg] with ω hω
  simpa using hω

theorem supermartingale_of_isCondExp_sub_nonneg_nat [SigmaFiniteFiltration μ 𝒢] {f : ℕ → Ω → E}
    (hadp : StronglyAdapted 𝒢 f) (hint : ∀ i, Integrable (f i) μ)
    (hf : ∀ i, ∃ g, IsCondExp (𝒢 i) μ (f i - f (i + 1)) g ∧ 0 ≤ᵐ[μ] g) :
    Supermartingale f 𝒢 μ := by
  rw [← neg_neg f]
  refine (submartingale_of_isCondExp_sub_nonneg_nat hadp.neg (fun i => (hint i).neg) ?_).neg
  simpa only [Pi.neg_apply, neg_sub_neg]

end OfSucc

section Preorder

variable [Preorder E]

-- Note that one cannot use `Submartingale.zero_le_of_predictable` to prove the other two
-- corresponding lemmas without imposing more restrictions to the ordering of `E`
/-- A predictable submartingale is a.e. greater than or equal to its initial state. -/
theorem Submartingale.zero_le_of_predictable {f : ℕ → Ω → E}
    (hfmgle : Submartingale f 𝒢 μ) (hfadp : StronglyAdapted 𝒢 fun n => f (n + 1)) (n : ℕ) :
    f 0 ≤ᵐ[μ] f n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    exact ih.trans
      (hfmgle.ae_le_isCondExp k.le_succ (isCondExp_self (hfadp k).aestronglyMeasurable))

/-- A predictable supermartingale is a.e. less than or equal to its initial state. -/
theorem Supermartingale.le_zero_of_predictable {f : ℕ → Ω → E}
    (hfmgle : Supermartingale f 𝒢 μ) (hfadp : StronglyAdapted 𝒢 fun n => f (n + 1))
    (n : ℕ) : f n ≤ᵐ[μ] f 0 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    exact (hfmgle.isCondExp_ae_le k.le_succ
      (isCondExp_self (hfadp k).aestronglyMeasurable)).trans ih

end Preorder

end SubSuper

/-- A strongly adapted integrable process `f` such that each `f i` is a conditional expectation of
`f (i + 1)` given `𝒢 i` is a martingale. -/
theorem martingale_nat {f : ℕ → Ω → E} (hadp : StronglyAdapted 𝒢 f)
    (hint : ∀ i, Integrable (f i) μ) (hf : ∀ i, IsCondExp (𝒢 i) μ (f (i + 1)) (f i)) :
    Martingale f 𝒢 μ := by
  refine ⟨hadp, fun i j hij ↦ ?_, hint⟩
  induction j, hij using Nat.le_induction with
  | base => exact isCondExp_self (hadp i).aestronglyMeasurable
  | succ k hik hk => exact (hf k).trans hk (𝒢.mono hik)

theorem martingale_of_setIntegral_eq_succ {f : ℕ → Ω → E} (hadp : StronglyAdapted 𝒢 f)
    (hint : ∀ i, Integrable (f i) μ)
    (hf : ∀ i, ∀ s : Set Ω, s ∈ 𝒢 i → ∫ ω in s, f i ω ∂μ = ∫ ω in s, f (i + 1) ω ∂μ) :
    Martingale f 𝒢 μ :=
  martingale_nat hadp hint fun n ↦
    ⟨(hadp n).aestronglyMeasurable, fun _ _ _ ↦ (hint n).integrableOn, fun s hs _ ↦ hf n s hs⟩

theorem martingale_of_isCondExp_sub_eq_zero_nat {f : ℕ → Ω → E} (hadp : StronglyAdapted 𝒢 f)
    (hint : ∀ i, Integrable (f i) μ) (hf : ∀ i, IsCondExp (𝒢 i) μ (f (i + 1) - f i) 0) :
    Martingale f 𝒢 μ :=
  martingale_nat hadp hint fun i ↦ by
    simpa using (hf i).add (isCondExp_self (hadp i).aestronglyMeasurable)
      ((hint (i + 1)).sub (hint i)) (hint i)

/-- A predictable martingale is a.e. equal to its initial state. -/
theorem Martingale.eq_zero_of_predictable {f : ℕ → Ω → E} (hfmgle : Martingale f 𝒢 μ)
    (hfadp : StronglyAdapted 𝒢 fun n => f (n + 1)) (n : ℕ) : f n =ᵐ[μ] f 0 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    exact (hfmgle.ae_eq_of_isCondExp k.le_succ
      (isCondExp_self (hfadp k).aestronglyMeasurable)).trans ih

section IsStronglyPredictable

/-- A predictable submartingale is a.e. greater than or equal to its initial state. -/
theorem Submartingale.zero_le_of_predictable' [Preorder E] {f : ℕ → Ω → E}
    (hfmgle : Submartingale f 𝒢 μ) (hf : IsStronglyPredictable 𝒢 f) (n : ℕ) :
    f 0 ≤ᵐ[μ] f n :=
  zero_le_of_predictable hfmgle hf.measurable_add_one n

/-- A predictable supermartingale is a.e. less than or equal to its initial state. -/
theorem Supermartingale.le_zero_of_predictable' [Preorder E] {f : ℕ → Ω → E}
    (hfmgle : Supermartingale f 𝒢 μ) (hfadp : IsStronglyPredictable 𝒢 f) (n : ℕ) :
    f n ≤ᵐ[μ] f 0 :=
  le_zero_of_predictable hfmgle hfadp.measurable_add_one n

/-- A predictable martingale is a.e. equal to its initial state. -/
theorem Martingale.eq_zero_of_predictable' {f : ℕ → Ω → E} (hfmgle : Martingale f 𝒢 μ)
    (hfadp : IsStronglyPredictable 𝒢 f) (n : ℕ) : f n =ᵐ[μ] f 0 :=
  eq_zero_of_predictable hfmgle hfadp.measurable_add_one n

end IsStronglyPredictable

namespace Submartingale

protected theorem integrable_stoppedValue [LE E] {f : ℕ → Ω → E} (hf : Submartingale f 𝒢 μ)
    {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime 𝒢 τ) {N : ℕ} (hbdd : ∀ ω, τ ω ≤ N) :
    Integrable (stoppedValue f τ) μ :=
  integrable_stoppedValue ℕ hτ hf.integrable hbdd

end Submartingale

section SumSMul

variable [PartialOrder E] [IsOrderedModule ℝ E] [ClosedIciTopology E] [IsOrderedAddMonoid E]

theorem Submartingale.sum_smul_sub [SigmaFiniteFiltration μ 𝒢] {R : ℝ}
    {f : ℕ → Ω → E} {ξ : ℕ → Ω → ℝ}
    (hf : Submartingale f 𝒢 μ) (hξ : StronglyAdapted 𝒢 ξ) (hbdd : ∀ n ω, ξ n ω ≤ R)
    (hnonneg : ∀ n ω, 0 ≤ ξ n ω) :
    Submartingale (fun n => ∑ k ∈ Finset.range n, ξ k • (f (k + 1) - f k)) 𝒢 μ := by
  have hξbdd : ∀ i, ∃ C, ∀ ω, ‖ξ i ω‖ ≤ C := fun i =>
    ⟨R, fun ω => (abs_of_nonneg (hnonneg i ω)).trans_le (hbdd i ω)⟩
  choose C hC using hξbdd
  have hint : ∀ m, Integrable (∑ k ∈ Finset.range m, ξ k • (f (k + 1) - f k)) μ := fun m =>
      integrable_finsetSum' _ fun i _ => Integrable.bdd_smul
        ((hf.integrable _).sub (hf.integrable _)) (C i)
        hξ.stronglyMeasurable.aestronglyMeasurable (ae_of_all _ (hC i))
  have hadp : StronglyAdapted 𝒢 fun n => ∑ k ∈ Finset.range n, ξ k • (f (k + 1) - f k) := by
    intro m
    refine Finset.stronglyMeasurable_sum _ fun i hi => ?_
    rw [Finset.mem_range] at hi
    exact (hξ.stronglyMeasurable_le hi.le).smul
      ((hf.stronglyAdapted.stronglyMeasurable_le (Nat.succ_le_of_lt hi)).sub
        (hf.stronglyAdapted.stronglyMeasurable_le hi.le))
  refine submartingale_of_isCondExp_sub_nonneg_nat hadp hint fun i => ?_
  simp only [← Finset.sum_Ico_eq_sub _ (Nat.le_succ _), Nat.succ_eq_add_one,
    Nat.Ico_succ_singleton, Finset.sum_singleton]
  obtain ⟨g, hg, hfg⟩ := hf.exists_ae_le_isCondExp i.le_succ
  have hd : IsCondExp (𝒢 i) μ (f (i + 1) - f i) (g - f i) :=
    hg.sub (isCondExp_self (hf.stronglyAdapted i).aestronglyMeasurable) (hf.integrable _)
      (hf.integrable _)
  refine ⟨ξ i • (g - f i), hd.smul_left (𝒢.le i) (hξ i).aestronglyMeasurable
    (((hf.integrable (i + 1)).sub (hf.integrable i)).bdd_smul (C i)
      hξ.stronglyMeasurable.aestronglyMeasurable (ae_of_all _ (hC i)))
    ((hf.integrable _).sub (hf.integrable _)), ?_⟩
  filter_upwards [hfg] with ω hω
  exact _root_.smul_nonneg (hnonneg i ω) (sub_nonneg.2 hω)

/-- Given a discrete submartingale `f` and a predictable process `ξ` (i.e. `ξ (n + 1)` is strongly
adapted) the process defined by `fun n => ∑ k ∈ Finset.range n, ξ (k + 1) * (f (k + 1) - f k)` is
also a submartingale. -/
theorem Submartingale.sum_smul_sub' [SigmaFiniteFiltration μ 𝒢] {R : ℝ} {ξ : ℕ → Ω → ℝ}
    {f : ℕ → Ω → E} (hf : Submartingale f 𝒢 μ) (hξ : StronglyAdapted 𝒢 fun n => ξ (n + 1))
    (hbdd : ∀ n ω, ξ n ω ≤ R) (hnonneg : ∀ n ω, 0 ≤ ξ n ω) :
    Submartingale (fun n => ∑ k ∈ Finset.range n, ξ (k + 1) • (f (k + 1) - f k)) 𝒢 μ :=
  hf.sum_smul_sub hξ (fun _ => hbdd _) fun _ => hnonneg _

theorem Submartingale.sum_mul_sub [SigmaFiniteFiltration μ 𝒢] {R : ℝ} {ξ f : ℕ → Ω → ℝ}
    (hf : Submartingale f 𝒢 μ) (hξ : StronglyAdapted 𝒢 ξ) (hbdd : ∀ n ω, ξ n ω ≤ R)
    (hnonneg : ∀ n ω, 0 ≤ ξ n ω) :
    Submartingale (fun n => ∑ k ∈ Finset.range n, ξ k * (f (k + 1) - f k)) 𝒢 μ :=
  hf.sum_smul_sub hξ hbdd hnonneg

/-- Given a discrete submartingale `f` and a predictable process `ξ` (i.e. `ξ (n + 1)` is strongly
adapted) the process defined by `fun n => ∑ k ∈ Finset.range n, ξ (k + 1) * (f (k + 1) - f k)` is
also a submartingale. -/
theorem Submartingale.sum_mul_sub' [SigmaFiniteFiltration μ 𝒢] {R : ℝ} {ξ f : ℕ → Ω → ℝ}
    (hf : Submartingale f 𝒢 μ) (hξ : StronglyAdapted 𝒢 fun n => ξ (n + 1))
    (hbdd : ∀ n ω, ξ n ω ≤ R) (hnonneg : ∀ n ω, 0 ≤ ξ n ω) :
    Submartingale (fun n => ∑ k ∈ Finset.range n, ξ (k + 1) * (f (k + 1) - f k)) 𝒢 μ :=
  hf.sum_smul_sub' hξ hbdd hnonneg

end SumSMul

end Nat

end MeasureTheory
