/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion, Rémy Degenne, Kexing Ying
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Pull-out property of the conditional expectation

Let `Ω` be endowed with a measurable space structure `mΩ`, and let `m : SigmaAlgebra Ω` such that
`m ≤ mΩ`. Let `μ` be a measure over `Ω`. Let `B : F →L[ℝ] E →L[ℝ] G` a continuous bilinear map,
`f : Ω → F` and `g : Ω → E` such that `fun ω ↦ B (f ω) (g ω)` is integrable, `g` is integrable
and `f` is `AEStronglyMeasurable` with respect to `m`. The **pull-out** property of the conditional
expectation states that if `k` is a conditional expectation of `g` given `m`, then
`fun ω ↦ B (f ω) (k ω)` is a conditional expectation of `fun ω ↦ B (f ω) (g ω)` given `m`. For the
almost everywhere classes, this is `μ[B f g | m] = B f μ[g | m]`.

We specialize this statement to the cases where `B` is scalar multiplication and multiplication.

None of these statements assumes that the measure `μ` is finite, or σ-finite on `m`. The statements
about conditional expectations as a relation (`MeasureTheory.IsCondExp`) assume neither that
conditional expectations exist nor that they are unique. The statements about the classes
`μ[· | m]` take the domains of both sides (`MeasureTheory.HasUniqueCondExp`) as hypotheses.

## Main statements

* `MeasureTheory.IsCondExp.bilin_left`: The pull-out property of the conditional expectation: if
  `k` is a conditional expectation of `g`, then `B f k` is a conditional expectation of `B f g`.
* `MeasureTheory.IsCondExp.bilin_right`: The same property with the `m`-measurable function on the
  right: if `k` is a conditional expectation of `f`, then `B k g` is one of `B f g`.
* `MeasureTheory.IsCondExp.smul_left`, `MeasureTheory.IsCondExp.smul_right`: The pull-out property
  for scalar multiplication: `f • k` is a conditional expectation of `f • g`, and `k • g` is one of
  `f • g`.
* `MeasureTheory.IsCondExp.mul_left`, `MeasureTheory.IsCondExp.mul_right`: The pull-out property
  for multiplication: `f * k` is a conditional expectation of `f * g`, and `k * g` is one of
  `f * g`.
* `MeasureTheory.condExp_bilin_left`, `MeasureTheory.condExp_bilin_right`,
  `MeasureTheory.condExp_smul_left`, `MeasureTheory.condExp_smul_right`,
  `MeasureTheory.condExp_mul_left`, `MeasureTheory.condExp_mul_right`: The same properties for the
  conditional expectation as an almost everywhere class, for example
  `μ[f * g | m] = f * μ[g | m]`.

## Implementation notes

The proof of `IsCondExp.bilin_left` approximates `f` by `m`-simple functions on the `m`-measurable
sets `{‖f‖ ≤ n}`, where it is bounded, and it combines the pieces with the dominated convergence
theorem for conditional expectations (`IsCondExp.of_tendsto`). To let `n` tend to infinity, one
needs that `B f k` is integrable. This follows from the fact that a conditional expectation of an
integrable function does not increase the `L¹` norm, for every measure
(`IsCondExp.integral_norm_le`).

## Tags

conditional expectation, pull-out, bilinear map
-/

public section

open Filter

open scoped ENNReal Topology MeasureTheory

namespace MeasureTheory

variable {Ω : Type*} {m mΩ : SigmaAlgebra Ω} {μ : Measure Ω}
  {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [CompleteSpace G] (B : F →L[ℝ] E →L[ℝ] G)

/-- The pull-out property for an `m`-simple function. Auxiliary lemma for
`IsCondExp.bilin_left`. -/
private theorem isCondExp_bilin_simpleFunc [CompleteSpace E] (hm : m ≤ mΩ)
    (u : @SimpleFunc Ω m F) {g k : Ω → E} (h : IsCondExp m μ g k) (hg : Integrable g μ) :
    IsCondExp m μ (fun ω ↦ B (u ω) (g ω)) (fun ω ↦ B (u ω) (k ω)) := by
  have h_indicator (s : Set Ω) (c : F) (v : Ω → E) :
      (fun ω ↦ B (Set.indicator s (Function.const Ω c) ω) (v ω)) =
        s.indicator (fun ω ↦ B c (v ω)) := by
    ext ω
    by_cases hω : ω ∈ s <;> simp [hω]
  have h_add (u₁ u₂ : @SimpleFunc Ω m F) (v : Ω → E) :
      (fun ω ↦ B ((u₁ + u₂) ω) (v ω)) =
        (fun ω ↦ B (u₁ ω) (v ω)) + fun ω ↦ B (u₂ ω) (v ω) := by
    ext ω
    simp
  refine @SimpleFunc.induction _ _ m _
    (fun v ↦ IsCondExp m μ (fun ω ↦ B (v ω) (g ω)) (fun ω ↦ B (v ω) (k ω)))
    (fun c s hs ↦ ?_) (fun u₁ u₂ _ h₁ h₂ ↦ ?_) u
  · simp only [SimpleFunc.const_zero, SimpleFunc.coe_piecewise, SimpleFunc.coe_const,
      SimpleFunc.coe_zero, Set.piecewise_eq_indicator]
    rw [h_indicator, h_indicator]
    exact (h.comp_continuousLinearMap hg (B c)).indicator hm hs
  · obtain ⟨C₁, hC₁⟩ := @SimpleFunc.exists_forall_norm_le _ _ m _ u₁
    obtain ⟨C₂, hC₂⟩ := @SimpleFunc.exists_forall_norm_le _ _ m _ u₂
    rw [h_add, h_add]
    exact h₁.add h₂
      (B.integrable_of_bilin_of_bdd_left C₁ (u₁.stronglyMeasurable.mono hm).aestronglyMeasurable
        (ae_of_all _ hC₁) hg)
      (B.integrable_of_bilin_of_bdd_left C₂ (u₂.stronglyMeasurable.mono hm).aestronglyMeasurable
        (ae_of_all _ hC₂) hg)

/-- The pull-out property for a bounded `m`-strongly measurable function. Auxiliary lemma for
`IsCondExp.bilin_left`. -/
private theorem isCondExp_bilin_of_norm_le [CompleteSpace E] (hm : m ≤ mΩ) {f : Ω → F}
    {g k : Ω → E} (h : IsCondExp m μ g k) (hf : StronglyMeasurable[m] f) (hg : Integrable g μ)
    {c : ℝ} (hc : 0 ≤ c) (hf_bound : ∀ ω, ‖f ω‖ ≤ c) :
    IsCondExp m μ (fun ω ↦ B (f ω) (g ω)) (fun ω ↦ B (f ω) (k ω)) := by
  have hk : Integrable k μ := h.integrable hg
  have hfs_tendsto (ω : Ω) : Tendsto (hf.approxBounded c · ω) atTop (𝓝 (f ω)) :=
    hf.tendsto_approxBounded_of_norm_le (hf_bound ω)
  have hfs_bound := hf.norm_approxBounded_le hc
  refine IsCondExp.of_tendsto hm (F := fun n ω ↦ B (hf.approxBounded c n ω) (g ω))
    (G := fun n ω ↦ B (hf.approxBounded c n ω) (k ω))
    (fun n ↦ isCondExp_bilin_simpleFunc B hm _ h hg)
    (fun n ↦ B.continuous₂.comp_aestronglyMeasurable₂
      ((hf.approxBounded c n).stronglyMeasurable.mono hm).aestronglyMeasurable hg.1)
    (fun ω ↦ ‖B‖ * c * ‖g ω‖) (hg.norm.const_mul _) (fun n ↦ ae_of_all _ fun ω ↦ ?_)
    (ae_of_all _ fun ω ↦ ?_) (fun ω ↦ ‖B‖ * c * ‖k ω‖) (hk.norm.const_mul _)
    (fun n ↦ ae_of_all _ fun ω ↦ ?_) (ae_of_all _ fun ω ↦ ?_) ?_
  · grw [B.le_opNorm₂, hfs_bound]
  · exact ((by fun_prop : Continuous (fun x ↦ B x (g ω))).tendsto (f ω)).comp (hfs_tendsto ω)
  · grw [B.le_opNorm₂, hfs_bound]
  · exact ((by fun_prop : Continuous (fun x ↦ B x (k ω))).tendsto (f ω)).comp (hfs_tendsto ω)
  · exact B.continuous₂.comp_aestronglyMeasurable₂ hf.aestronglyMeasurable h.aestronglyMeasurable

/-- The pull-out property for an `m`-strongly measurable function. Auxiliary lemma for
`IsCondExp.bilin_left`. -/
private theorem isCondExp_bilin_of_stronglyMeasurable [CompleteSpace E] (hm : m ≤ mΩ)
    {f : Ω → F} {g k : Ω → E} (h : IsCondExp m μ g k) (hf : StronglyMeasurable[m] f)
    (hfg : Integrable (fun ω ↦ B (f ω) (g ω)) μ) (hg : Integrable g μ) :
    IsCondExp m μ (fun ω ↦ B (f ω) (g ω)) (fun ω ↦ B (f ω) (k ω)) := by
  -- the `m`-measurable sets `S n` on which `f` is bounded by `n`, and the truncations of `f`
  let S (n : ℕ) : Set Ω := {ω | ‖f ω‖ ≤ n}
  have hS (n : ℕ) : S n ∈ m := hf.norm.measurable measurableSet_Iic
  have hS_mono : Monotone S := fun n n' hn ω (hω : ‖f ω‖ ≤ n) ↦
    show ‖f ω‖ ≤ n' from hω.trans (Nat.cast_le.2 hn)
  have hS_univ : ⋃ n, S n = Set.univ :=
    Set.eq_univ_of_forall fun ω ↦ Set.mem_iUnion.2 (exists_nat_ge ‖f ω‖)
  have hS_eventually (ω : Ω) : ∀ᶠ n in atTop, ω ∈ S n := by
    obtain ⟨N, hN⟩ := exists_nat_ge ‖f ω‖
    filter_upwards [eventually_ge_atTop N] with n hn
    exact hN.trans (Nat.cast_le.2 hn)
  let f' (n : ℕ) : Ω → F := (S n).indicator f
  have hf'_meas (n : ℕ) : StronglyMeasurable[m] (f' n) := hf.indicator (hS n)
  have hf'_eq (n : ℕ) {ω : Ω} (hω : ω ∈ S n) : f' n ω = f ω := Set.indicator_of_mem hω f
  have hf'_bound (n : ℕ) (ω : Ω) : ‖f' n ω‖ ≤ n := by
    by_cases hω : ω ∈ S n
    · rw [hf'_eq n hω]
      exact hω
    · simp [f', hω]
  -- the truncated functions have conditional expectations, by the bounded case
  have h_piece (n : ℕ) :
      IsCondExp m μ (fun ω ↦ B (f' n ω) (g ω)) (fun ω ↦ B (f' n ω) (k ω)) :=
    isCondExp_bilin_of_norm_le B hm h (hf'_meas n) hg n.cast_nonneg (hf'_bound n)
  have hF_int (n : ℕ) : Integrable (fun ω ↦ B (f' n ω) (g ω)) μ :=
    B.integrable_of_bilin_of_bdd_left n ((hf'_meas n).mono hm).aestronglyMeasurable
      (ae_of_all _ (hf'_bound n)) hg
  have hG_int (n : ℕ) : Integrable (fun ω ↦ B (f' n ω) (k ω)) μ :=
    (h_piece n).integrable (hF_int n)
  have hF_le (n : ℕ) (ω : Ω) : ‖B (f' n ω) (g ω)‖ ≤ ‖B (f ω) (g ω)‖ := by
    by_cases hω : ω ∈ S n <;> simp [f', hω]
  have hG_le (n : ℕ) (ω : Ω) : ‖B (f' n ω) (k ω)‖ ≤ ‖B (f ω) (k ω)‖ := by
    by_cases hω : ω ∈ S n <;> simp [f', hω]
  -- the limit `B f k` is integrable, as the `L¹` norms of the truncations are bounded
  have hψ_int : Integrable (fun ω ↦ B (f ω) (k ω)) μ := by
    refine ⟨B.continuous₂.comp_aestronglyMeasurable₂ (hf.mono hm).aestronglyMeasurable
      (h.aestronglyMeasurable' hm), hasFiniteIntegral_iff_enorm.2 ?_⟩
    calc ∫⁻ ω, ‖B (f ω) (k ω)‖ₑ ∂μ
      _ = ∫⁻ ω in ⋃ n, S n, ‖B (f ω) (k ω)‖ₑ ∂μ := by rw [hS_univ, Measure.restrict_univ]
      _ = ⨆ n, ∫⁻ ω in S n, ‖B (f ω) (k ω)‖ₑ ∂μ :=
        setLIntegral_iUnion_of_directed _ hS_mono.directed_le
      _ ≤ ENNReal.ofReal (∫ ω, ‖B (f ω) (g ω)‖ ∂μ) := by
        refine iSup_le fun n ↦ ?_
        calc ∫⁻ ω in S n, ‖B (f ω) (k ω)‖ₑ ∂μ
          _ = ∫⁻ ω in S n, ‖B (f' n ω) (k ω)‖ₑ ∂μ :=
            setLIntegral_congr_fun (hm (hS n)) fun ω hω ↦ by rw [hf'_eq n hω]
          _ ≤ ∫⁻ ω, ‖B (f' n ω) (k ω)‖ₑ ∂μ := setLIntegral_le_lintegral _ _
          _ = ENNReal.ofReal (∫ ω, ‖B (f' n ω) (k ω)‖ ∂μ) :=
            (ofReal_integral_norm_eq_lintegral_enorm (hG_int n)).symm
          _ ≤ ENNReal.ofReal (∫ ω, ‖B (f' n ω) (g ω)‖ ∂μ) :=
            ENNReal.ofReal_le_ofReal ((h_piece n).integral_norm_le hm (hF_int n))
          _ ≤ ENNReal.ofReal (∫ ω, ‖B (f ω) (g ω)‖ ∂μ) :=
            ENNReal.ofReal_le_ofReal (integral_mono (hF_int n).norm hfg.norm (hF_le n))
      _ < ∞ := ENNReal.ofReal_lt_top
  -- the truncations are eventually equal to `f`, so dominated convergence concludes
  refine IsCondExp.of_tendsto hm (F := fun n ω ↦ B (f' n ω) (g ω))
    (G := fun n ω ↦ B (f' n ω) (k ω)) h_piece (fun n ↦ (hF_int n).1) _ hfg.norm
    (fun n ↦ ae_of_all _ (hF_le n)) (ae_of_all _ fun ω ↦ ?_) _ hψ_int.norm
    (fun n ↦ ae_of_all _ (hG_le n)) (ae_of_all _ fun ω ↦ ?_)
    (B.continuous₂.comp_aestronglyMeasurable₂ hf.aestronglyMeasurable h.aestronglyMeasurable)
  · refine tendsto_const_nhds.congr' ((hS_eventually ω).mono fun n hn ↦ ?_)
    dsimp only
    rw [hf'_eq n hn]
  · refine tendsto_const_nhds.congr' ((hS_eventually ω).mono fun n hn ↦ ?_)
    dsimp only
    rw [hf'_eq n hn]

/-- **Pull-out property** of the conditional expectation: if `k` is a conditional expectation of an
integrable function `g` given `m`, `f` is almost everywhere `m`-strongly measurable and
`B f g` is integrable, then `B f k` is a conditional expectation of `B f g`. No assumption is made
on the measure. -/
theorem IsCondExp.bilin_left [CompleteSpace E] (hm : m ≤ mΩ) {f : Ω → F} {g k : Ω → E}
    (h : IsCondExp m μ g k) (hf : AEStronglyMeasurable[m] f μ)
    (hfg : Integrable (fun ω ↦ B (f ω) (g ω)) μ) (hg : Integrable g μ) :
    IsCondExp m μ (fun ω ↦ B (f ω) (g ω)) (fun ω ↦ B (f ω) (k ω)) := by
  have hfg' : Integrable (fun ω ↦ B (hf.mk f ω) (g ω)) μ :=
    hfg.congr (by filter_upwards [hf.ae_eq_mk] with ω hω; rw [hω])
  exact (isCondExp_bilin_of_stronglyMeasurable B hm h hf.stronglyMeasurable_mk hfg' hg).congr
    (by filter_upwards [hf.ae_eq_mk] with ω hω; rw [hω])
    (by filter_upwards [hf.ae_eq_mk] with ω hω; rw [hω])

/-- **Pull-out property** of the conditional expectation: if `k` is a conditional expectation of an
integrable function `f` given `m`, `g` is almost everywhere `m`-strongly measurable and
`B f g` is integrable, then `B k g` is a conditional expectation of `B f g`. No assumption is made
on the measure. -/
theorem IsCondExp.bilin_right [CompleteSpace F] (hm : m ≤ mΩ) {f k : Ω → F} {g : Ω → E}
    (h : IsCondExp m μ f k) (hg : AEStronglyMeasurable[m] g μ)
    (hfg : Integrable (fun ω ↦ B (f ω) (g ω)) μ) (hf : Integrable f μ) :
    IsCondExp m μ (fun ω ↦ B (f ω) (g ω)) (fun ω ↦ B (k ω) (g ω)) :=
  h.bilin_left B.flip hm hg hfg hf

/-- **Pull-out property** of the conditional expectation: if `k` is a conditional expectation of an
integrable function `g` given `m`, `f` is almost everywhere `m`-strongly measurable and `f • g` is
integrable, then `f • k` is a conditional expectation of `f • g`. -/
theorem IsCondExp.smul_left [CompleteSpace E] (hm : m ≤ mΩ) {f : Ω → ℝ} {g k : Ω → E}
    (h : IsCondExp m μ g k) (hf : AEStronglyMeasurable[m] f μ) (hfg : Integrable (f • g) μ)
    (hg : Integrable g μ) : IsCondExp m μ (f • g) (f • k) :=
  h.bilin_left (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E) hm hf hfg hg

/-- **Pull-out property** of the conditional expectation: if `k` is a conditional expectation of an
integrable function `f` given `m`, `g` is almost everywhere `m`-strongly measurable and `f • g` is
integrable, then `k • g` is a conditional expectation of `f • g`. -/
theorem IsCondExp.smul_right [CompleteSpace E] (hm : m ≤ mΩ) {f k : Ω → ℝ} {g : Ω → E}
    (h : IsCondExp m μ f k) (hg : AEStronglyMeasurable[m] g μ) (hfg : Integrable (f • g) μ)
    (hf : Integrable f μ) : IsCondExp m μ (f • g) (k • g) :=
  h.bilin_right (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E) hm hg hfg hf

/-- **Pull-out property** of the conditional expectation: if `k` is a conditional expectation of an
integrable function `g` given `m`, `f` is almost everywhere `m`-strongly measurable and `f * g` is
integrable, then `f * k` is a conditional expectation of `f * g`. -/
theorem IsCondExp.mul_left (hm : m ≤ mΩ) {f g k : Ω → ℝ} (h : IsCondExp m μ g k)
    (hf : AEStronglyMeasurable[m] f μ) (hfg : Integrable (f * g) μ) (hg : Integrable g μ) :
    IsCondExp m μ (f * g) (f * k) :=
  h.bilin_left (.mul ℝ ℝ) hm hf hfg hg

/-- **Pull-out property** of the conditional expectation: if `k` is a conditional expectation of an
integrable function `f` given `m`, `g` is almost everywhere `m`-strongly measurable and `f * g` is
integrable, then `k * g` is a conditional expectation of `f * g`. -/
theorem IsCondExp.mul_right (hm : m ≤ mΩ) {f g k : Ω → ℝ} (h : IsCondExp m μ f k)
    (hg : AEStronglyMeasurable[m] g μ) (hfg : Integrable (f * g) μ) (hf : Integrable f μ) :
    IsCondExp m μ (f * g) (k * g) :=
  h.bilin_right (.mul ℝ ℝ) hm hg hfg hf

/-! ### The conditional expectation as an almost everywhere class

The class `μ[B f g | m]` of the conditional expectations of `B f g` is the class obtained by
applying `B` to `f` and to the class `μ[g | m]`, for an almost everywhere `m`-strongly measurable
`f`. -/

/-- **Pull-out property** of the conditional expectation as an almost everywhere class:
`μ[B f g | m] = B f μ[g | m]`, where `B` acts on the classes of `f` and `μ[g | m]`. -/
theorem condExp_bilin_left [CompleteSpace E] (hm : m ≤ mΩ) {f : Ω → F} {g : Ω → E}
    (hf : AEStronglyMeasurable[m] f μ) (hfg : Integrable (fun ω ↦ B (f ω) (g ω)) μ)
    (hg : Integrable g μ) (h : HasUniqueCondExp m μ g)
    (h' : HasUniqueCondExp m μ (fun ω ↦ B (f ω) (g ω))) :
    condExp m μ (fun ω ↦ B (f ω) (g ω)) h' =
      Germ.map₂ (fun x y ↦ B x y) (f : (ae μ).Germ F) (condExp m μ g h) := by
  obtain ⟨k, hk⟩ := h.exists_isCondExp
  rw [hk.condExp_eq h, Germ.map₂_coe, (hk.bilin_left B hm hf hfg hg).condExp_eq h']

/-- **Pull-out property** of the conditional expectation as an almost everywhere class:
`μ[B f g | m] = B μ[f | m] g`, where `B` acts on the classes of `μ[f | m]` and `g`. -/
theorem condExp_bilin_right [CompleteSpace F] (hm : m ≤ mΩ) {f : Ω → F} {g : Ω → E}
    (hg : AEStronglyMeasurable[m] g μ) (hfg : Integrable (fun ω ↦ B (f ω) (g ω)) μ)
    (hf : Integrable f μ) (h : HasUniqueCondExp m μ f)
    (h' : HasUniqueCondExp m μ (fun ω ↦ B (f ω) (g ω))) :
    condExp m μ (fun ω ↦ B (f ω) (g ω)) h' =
      Germ.map₂ (fun x y ↦ B x y) (condExp m μ f h) (g : (ae μ).Germ E) := by
  obtain ⟨k, hk⟩ := h.exists_isCondExp
  rw [hk.condExp_eq h, Germ.map₂_coe, (hk.bilin_right B hm hg hfg hf).condExp_eq h']

/-- **Pull-out property** of the conditional expectation as an almost everywhere class:
`μ[f • g | m] = f • μ[g | m]`. -/
theorem condExp_smul_left [CompleteSpace E] (hm : m ≤ mΩ) {f : Ω → ℝ} {g : Ω → E}
    (hf : AEStronglyMeasurable[m] f μ) (hfg : Integrable (f • g) μ) (hg : Integrable g μ)
    (h : HasUniqueCondExp m μ g) (h' : HasUniqueCondExp m μ (f • g)) :
    condExp m μ (f • g) h' = (f : (ae μ).Germ ℝ) • condExp m μ g h := by
  obtain ⟨k, hk⟩ := h.exists_isCondExp
  rw [hk.condExp_eq h, ← Germ.coe_smul', (hk.smul_left hm hf hfg hg).condExp_eq h']

/-- **Pull-out property** of the conditional expectation as an almost everywhere class:
`μ[f • g | m] = μ[f | m] • g`. -/
theorem condExp_smul_right [CompleteSpace E] (hm : m ≤ mΩ) {f : Ω → ℝ} {g : Ω → E}
    (hg : AEStronglyMeasurable[m] g μ) (hfg : Integrable (f • g) μ) (hf : Integrable f μ)
    (h : HasUniqueCondExp m μ f) (h' : HasUniqueCondExp m μ (f • g)) :
    condExp m μ (f • g) h' = condExp m μ f h • (g : (ae μ).Germ E) := by
  obtain ⟨k, hk⟩ := h.exists_isCondExp
  rw [hk.condExp_eq h, ← Germ.coe_smul', (hk.smul_right hm hg hfg hf).condExp_eq h']

/-- **Pull-out property** of the conditional expectation as an almost everywhere class:
`μ[f * g | m] = f * μ[g | m]`. -/
theorem condExp_mul_left (hm : m ≤ mΩ) {f g : Ω → ℝ} (hf : AEStronglyMeasurable[m] f μ)
    (hfg : Integrable (f * g) μ) (hg : Integrable g μ) (h : HasUniqueCondExp m μ g)
    (h' : HasUniqueCondExp m μ (f * g)) :
    condExp m μ (f * g) h' = (f : (ae μ).Germ ℝ) * condExp m μ g h := by
  obtain ⟨k, hk⟩ := h.exists_isCondExp
  rw [hk.condExp_eq h, ← Germ.coe_mul, (hk.mul_left hm hf hfg hg).condExp_eq h']

/-- **Pull-out property** of the conditional expectation as an almost everywhere class:
`μ[f * g | m] = μ[f | m] * g`. -/
theorem condExp_mul_right (hm : m ≤ mΩ) {f g : Ω → ℝ} (hg : AEStronglyMeasurable[m] g μ)
    (hfg : Integrable (f * g) μ) (hf : Integrable f μ) (h : HasUniqueCondExp m μ f)
    (h' : HasUniqueCondExp m μ (f * g)) :
    condExp m μ (f * g) h' = condExp m μ f h * (g : (ae μ).Germ ℝ) := by
  obtain ⟨k, hk⟩ := h.exists_isCondExp
  rw [hk.condExp_eq h, ← Germ.coe_mul, (hk.mul_right hm hg hfg hf).condExp_eq h']

end MeasureTheory
