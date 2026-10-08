/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/

module

public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Kernel.CondDistrib

import Mathlib.Probability.Kernel.Composition.Lemmas

/-!
# A predicate for having a specified conditional distribution

We introduce a predicate `HasCondDistrib Y X κ P` stating that the kernel `κ` is a version of the
conditional distribution of `Y` given `X` under the measure `P`.
The statement requires the pair `(X, Y)` to be a.e. measurable and says that its law under `P` is
equal to `(P.map X) ⊗ₘ κ`, the product of the law of `X` under `P` and the kernel `κ`.

## Main definitions

* `HasCondDistrib Y X κ P` : predicate stating that the kernel `κ` is a version of the conditional
  distribution of `Y` given `X` under the measure `P`.

## Main statements

* `ProbabilityTheory.mem_condDistrib_iff_hasCondDistrib`: if the joint law of `(X, Y)` has a
  unique conditional kernel and the law of `X` is σ-finite, a kernel `κ` satisfies
  `HasCondDistrib Y X κ P` exactly when it represents the almost-everywhere class
  `condDistrib Y X P`.

-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

variable {Ω 𝓧 𝓨 𝓩 : Type*} {mΩ : SigmaAlgebra Ω}
  {m𝓧 : SigmaAlgebra 𝓧} {m𝓨 : SigmaAlgebra 𝓨} {m𝓩 : SigmaAlgebra 𝓩}
  {P : Measure Ω} {X : Ω → 𝓧} {Y : Ω → 𝓨} {κ : Kernel 𝓧 𝓨}

/-- Predicate stating that the kernel `κ` is a version of the conditional distribution of `Y` given
`X` under the measure `P`: the composition-product `(P.map X) ⊗ₘ κ` exists and is the law of
`(X, Y)`. Versions are determined only up to `P.map X`-null sets;
`ProbabilityTheory.mem_condDistrib_iff_hasCondDistrib` identifies the versions with the
representatives of the class `condDistrib Y X P` when the law of `X` is σ-finite. -/
@[fun_prop]
structure HasCondDistrib (Y : Ω → 𝓨) (X : Ω → 𝓧) (κ : Kernel 𝓧 𝓨)
    (P : Measure Ω) : Prop where
  protected aemeasurable : AEMeasurable (fun ω ↦ (X ω, Y ω)) P := by fun_prop
  /-- The composition-product of the law of `X` with `κ` exists. -/
  protected hasCompProd : (P.map X aemeasurable.fst).HasCompProd κ := by infer_instance
  protected map_eq :
    haveI := hasCompProd
    P.map (fun ω ↦ (X ω, Y ω)) aemeasurable = P.map X aemeasurable.fst ⊗ₘ κ

attribute [fun_prop] HasCondDistrib.aemeasurable

@[fun_prop]
lemma HasCondDistrib.aemeasurable_fst (h : HasCondDistrib Y X κ P) :
    AEMeasurable X P := h.aemeasurable.fst

@[fun_prop]
lemma HasCondDistrib.aemeasurable_snd (h : HasCondDistrib Y X κ P) :
    AEMeasurable Y P := h.aemeasurable.snd

lemma HasLaw.prodMk_of_hasCondDistrib {Q : Measure 𝓧} [Q.HasCompProd κ]
    (h1 : HasLaw X Q P) (h2 : HasCondDistrib Y X κ P) :
    HasLaw (fun ω ↦ (X ω, Y ω)) (Q ⊗ₘ κ) P where
  aemeasurable := h2.aemeasurable
  map_eq := by simpa only [h1.map_eq] using h2.map_eq

lemma HasCondDistrib.hasLaw_of_const [IsProbabilityMeasure P] {Q : Measure 𝓨}
    (h : HasCondDistrib Y X (Kernel.const 𝓧 Q) P) :
    HasLaw Y Q P where
  aemeasurable := h.aemeasurable_snd
  map_eq := by
    have h_snd : (P.map (fun ω ↦ (X ω, Y ω))).snd = Q := by
      rw [h.map_eq, Measure.snd_compProd]
      simp [Measure.map_apply (hf := h.aemeasurable_fst)]
    rwa [Measure.snd_map_prodMk₀ h.aemeasurable_fst (by fun_prop)] at h_snd

section CondDistrib

/-- A kernel `κ` is a conditional distribution of `Y` given `X` exactly when it represents
`condDistrib Y X P`, if the law of `X` is σ-finite. -/
lemma mem_condDistrib_iff_hasCondDistrib (hXY : AEMeasurable (fun ω ↦ (X ω, Y ω)) P)
    [(P.map (fun ω ↦ (X ω, Y ω)) hXY).HasUniqueCondKernel] [SigmaFinite (P.map X hXY.fst)] :
    κ ∈ condDistrib Y X P hXY ↔ HasCondDistrib Y X κ P := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have := hasCompProd_map_of_mem_condDistrib hXY.fst hXY.snd h
    exact ⟨hXY, this, (compProd_map_condDistrib hXY.fst hXY.snd h).symm⟩
  · have := h.hasCompProd
    exact mem_condDistrib_of_measure_eq_compProd hXY.fst hXY.snd h.map_eq

/-- A conditional distribution of `Y` given `X` represents `condDistrib Y X P`, if the law of `X`
is σ-finite. -/
lemma HasCondDistrib.mem_condDistrib (h : HasCondDistrib Y X κ P)
    [(P.map (fun ω ↦ (X ω, Y ω)) h.aemeasurable).HasUniqueCondKernel]
    [SigmaFinite (P.map X h.aemeasurable.fst)] :
    κ ∈ condDistrib Y X P h.aemeasurable :=
  (mem_condDistrib_iff_hasCondDistrib h.aemeasurable).2 h

/-- A Markov conditional distribution of `Y` given `X` represents `condDistrib Y X P`. Unlike for a
kernel that is not Markov, the class of the joint law suffices. -/
lemma HasCondDistrib.mem_condDistrib_of_isMarkovKernel [IsMarkovKernel κ]
    (h : HasCondDistrib Y X κ P) [(P.map (fun ω ↦ (X ω, Y ω)) h.aemeasurable).HasUniqueCondKernel] :
    κ ∈ condDistrib Y X P h.aemeasurable :=
  mem_condDistrib_of_measure_eq_compProd_of_isMarkovKernel h.aemeasurable_fst h.aemeasurable_snd
    h.map_eq

end CondDistrib

lemma HasCondDistrib.comp_left (h : HasCondDistrib Y X κ P) {f : 𝓨 → 𝓩} (hf : Measurable f) :
    HasCondDistrib (f ∘ Y) X (κ.map f) P := by
  have := h.hasCompProd
  have hpair := h.aemeasurable
  have hout := h.aemeasurable_fst.prodMk
    (h.aemeasurable_snd.comp_aemeasurable hf.aemeasurable)
  have hpmap : Measurable (Prod.map (id : 𝓧 → 𝓧) f) := measurable_id.prodMap hf
  have hcomp := hpair.comp_aemeasurable hpmap.aemeasurable
  have hfun : (fun ω ↦ (X ω, f (Y ω))) =ᵐ[P]
      Prod.map id f ∘ fun ω ↦ (X ω, Y ω) := ae_of_all _ fun _ ↦ rfl
  exact
  { aemeasurable := hout
    map_eq := calc
      P.map (fun ω ↦ (X ω, f (Y ω))) hout =
          (P.map (fun ω ↦ (X ω, Y ω)) hpair).map (Prod.map id f) hpmap.aemeasurable := by
        calc
          _ = P.map (Prod.map id f ∘ fun ω ↦ (X ω, Y ω)) hcomp :=
            Measure.map_congr hfun hout
          _ = _ := (Measure.map_map hpair hpmap.aemeasurable).symm
      _ = (P.map X h.aemeasurable_fst ⊗ₘ κ).map (Prod.map id f) hpmap.aemeasurable := by
        simp only [h.map_eq]
      _ = P.map X h.aemeasurable_fst ⊗ₘ κ.map f hf := (Measure.compProd_map hf).symm }

lemma HasCondDistrib.fst {Y : Ω → 𝓨 × 𝓩} {κ : Kernel 𝓧 (𝓨 × 𝓩)}
    (h : HasCondDistrib Y X κ P) :
    HasCondDistrib (fun ω ↦ (Y ω).1) X κ.fst P := by
  rw [Kernel.fst_eq]
  exact h.comp_left measurable_fst

lemma HasCondDistrib.snd {Y : Ω → 𝓨 × 𝓩} {κ : Kernel 𝓧 (𝓨 × 𝓩)}
    (h : HasCondDistrib Y X κ P) :
    HasCondDistrib (fun ω ↦ (Y ω).2) X κ.snd P := by
  rw [Kernel.snd_eq]
  exact h.comp_left measurable_snd

/-- A conditional distribution of `Y` given `Z` of the form `κ.comap f` gives one of `Y` given
`f ∘ Z`, on the domain of the composition-product of the law of `f ∘ Z` with `κ`, which instance
search supplies for an s-finite `κ`. It does not follow from `h`: let `f` be the identity from the
discrete σ-algebra to the Borel σ-algebra on `ℝ`, `T` a set that is not Borel, `Z` and `Y` the
coordinates, `P` the composition-product of the sum of `∞ • dirac t` over `t ∈ T` with `κ.comap f`,
and `κ` constant at the sum of `dirac u` over `u ∉ T`. Then the measures of the sections of the
diagonal have lower integral `0` and upper integral `∞` against the law of `f ∘ Z`. -/
lemma HasCondDistrib.comp_right {f : 𝓩 → 𝓧}
    {hf : Measurable f} {Z : Ω → 𝓩} (h : HasCondDistrib Y Z (κ.comap f hf) P)
    [(P.map (f ∘ Z) (hf.comp_aemeasurable h.aemeasurable_fst)).HasCompProd κ] :
    HasCondDistrib Y (f ∘ Z) κ P := by
  have := h.hasCompProd
  have hout := (h.aemeasurable_fst.comp_aemeasurable hf.aemeasurable).prodMk
    h.aemeasurable_snd
  have hpmap : Measurable (Prod.map f (id : 𝓨 → 𝓨)) := hf.prodMap measurable_id
  have hcomp := h.aemeasurable.comp_aemeasurable hpmap.aemeasurable
  have hfun : (fun a ↦ ((f ∘ Z) a, Y a)) =ᵐ[P]
      Prod.map f id ∘ fun a ↦ (Z a, Y a) := ae_of_all _ fun _ ↦ rfl
  exact
  { aemeasurable := hout
    map_eq := calc
      P.map (fun a ↦ ((f ∘ Z) a, Y a)) hout =
          (P.map (fun a ↦ (Z a, Y a)) h.aemeasurable).map
            (Prod.map f id) hpmap.aemeasurable := by
        calc
          _ = P.map (Prod.map f id ∘ fun a ↦ (Z a, Y a)) hcomp :=
            Measure.map_congr hfun hout
          _ = _ := (Measure.map_map h.aemeasurable hpmap.aemeasurable).symm
      _ = (P.map Z h.aemeasurable_fst ⊗ₘ κ.comap f hf).map
          (Prod.map f id) hpmap.aemeasurable := by simp only [h.map_eq]
      _ = P.map (f ∘ Z) (hf.comp_aemeasurable h.aemeasurable_fst) ⊗ₘ κ := by
        ext s hs
        obtain ⟨g, hg, hle, heq⟩ := Measure.HasCompProd.exists_measurable_ge_lintegral_eq
          (μ := P.map (f ∘ Z) (hf.comp_aemeasurable h.aemeasurable_fst)) (κ := κ) hs
        rw [Measure.map_apply hs hpmap.aemeasurable, Measure.compProd_apply (hpmap hs),
          Measure.compProd_apply hs]
        rw [← Measure.map_map h.aemeasurable_fst hf.aemeasurable] at heq ⊢
        rw [lintegral_map_of_exists_measurable_ge hf.aemeasurable
          ⟨g, hg, .of_forall hle, heq⟩]
        rfl }

/-- A conditional distribution of `Y` given `X` gives one of `Y` given `f ∘ X` for a measurable
equivalence `f`, along which the domain of the composition-product passes
(`MeasureTheory.Measure.HasCompProd.map_measurableEquiv`). -/
lemma HasCondDistrib.measurableEquiv_comp_right (h : HasCondDistrib Y X κ P) (f : 𝓧 ≃ᵐ 𝓩) :
    HasCondDistrib Y (f ∘ X) (κ.comap f.symm f.symm.measurable) P := by
  have := h.hasCompProd
  have : (P.map (f ∘ X) (f.measurable.comp_aemeasurable h.aemeasurable_fst)).HasCompProd
      (κ.comap f.symm f.symm.measurable) := by
    rw [← Measure.map_map h.aemeasurable_fst f.measurable.aemeasurable]
    exact Measure.HasCompProd.map_measurableEquiv f
  apply HasCondDistrib.comp_right (hf := f.measurable)
  simpa [← Kernel.comap_comp_right]

/-- A conditional distribution of `(Y, Z)` given `X` of the form `κ ⊗ₖ η`, for a Markov kernel
`η`, gives the conditional distribution `η` of `Z` given `(X, Y)`. -/
lemma HasCondDistrib.of_compProd {Z : Ω → 𝓩} {η : Kernel (𝓧 × 𝓨) 𝓩} [κ.HasCompProd η]
    [IsMarkovKernel η] (h : HasCondDistrib (fun a ↦ (Y a, Z a)) X (κ ⊗ₖ η) P) :
    HasCondDistrib Z (fun a ↦ (X a, Y a)) η P := by
  have : (P.map X h.aemeasurable_fst).HasCompProd κ := by
    have h' : (P.map X h.aemeasurable_fst).HasCompProd (κ ⊗ₖ η).fst := h.fst.hasCompProd
    rwa [Kernel.fst_compProd] at h'
  have hZ : AEMeasurable Z P := h.aemeasurable_snd.snd
  have hY : AEMeasurable Y P := h.aemeasurable_snd.fst
  have hX : AEMeasurable X P := h.aemeasurable_fst
  have hXY := hX.prodMk hY
  have hout := hXY.prodMk hZ
  have hassoc : AEMeasurable MeasurableEquiv.prodAssoc.symm
      (P.map (fun a ↦ (X a, (Y a, Z a))) h.aemeasurable) := by fun_prop
  have hcomp := h.aemeasurable.comp_aemeasurable hassoc
  have hfun : (fun a ↦ ((X a, Y a), Z a)) =ᵐ[P]
      MeasurableEquiv.prodAssoc.symm ∘ fun a ↦ (X a, (Y a, Z a)) := ae_of_all _ fun _ ↦ rfl
  refine ⟨hout, inferInstance, ?_⟩
  calc
    P.map (fun a ↦ ((X a, Y a), Z a)) hout =
        (P.map (fun a ↦ (X a, (Y a, Z a))) h.aemeasurable).map
          MeasurableEquiv.prodAssoc.symm (by fun_prop) := by
      calc
        _ = P.map (MeasurableEquiv.prodAssoc.symm ∘ fun a ↦ (X a, (Y a, Z a))) hcomp :=
          Measure.map_congr hfun hout
        _ = _ := (Measure.map_map h.aemeasurable hassoc).symm
    _ = (P.map X hX ⊗ₘ (κ ⊗ₖ η)).map MeasurableEquiv.prodAssoc.symm (by fun_prop) := by
      simp only [h.map_eq]
    _ = (P.map X hX ⊗ₘ κ) ⊗ₘ η := Measure.compProd_assoc
    _ = P.map (fun a ↦ (X a, Y a)) hXY ⊗ₘ η := by
      congr 1
      simpa only [Kernel.fst_compProd] using h.fst.map_eq.symm

end ProbabilityTheory
