/-
Copyright (c) 2025 Alastair Irving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alastair Irving, Michael Stoll, Terence Tao
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Multiplicative inverse and iteration of real logarithm

We study the functions `x ↦ (log x)⁻¹` and `x ↦ log (log x)` on the domain where
`log x` is a unit. The singularity statements concern extensions from this domain.
-/

public section

namespace Real

open Filter Asymptotics Bornology Metric Set

open scoped Topology

private theorem isOpen_log_unit : IsOpen {x : ℝ | IsUnit (log x)} :=
  isOpen_iff_mem_nhds.mpr fun _ hx ↦
    (continuousAt_log (log_ne_zero.mp hx.ne_zero).1).eventually (Units.isOpen.mem_nhds hx)

private theorem tendsto_from_log_unit {l L : Filter ℝ} {g : ℝ → ℝ}
    {f : {x : ℝ // IsUnit (log x)} → ℝ}
    (hagrees : ∀ᶠ x in l, ∃ h : IsUnit (log x), g x = f ⟨x, h⟩)
    (hf : Tendsto f (comap Subtype.val l) L) : Tendsto g l L := by
  have hval : Tendsto (Subtype.val : {x : ℝ // IsUnit (log x)} → ℝ)
      (comap Subtype.val l) l := tendsto_comap
  refine (tendsto_comap'_iff (i := Subtype.val) ?_).mp
    (hf.congr' ((hval.eventually hagrees).mono fun _ ⟨_, hx⟩ ↦ hx.symm))
  exact hagrees.mono fun x ⟨hx, _⟩ ↦ ⟨⟨x, hx⟩, rfl⟩

private theorem tendsto_log_at_nonzero_root {x : ℝ} (hx : x ≠ 0) (hlog : log x = 0) :
    Tendsto log (𝓝[≠] x) (𝓝[≠] 0) :=
  hlog ▸ (hasDerivAt_log (hx := hx.isUnit)).tendsto_nhdsNE (inv_ne_zero (ha := hx.isUnit))

/-! ## Derivative of the inverse logarithm -/

private theorem not_continuousAt_inv_log_of_log_eq_zero {g : ℝ → ℝ} {x : ℝ}
    (hx : x ≠ 0) (hlog : log x = 0)
    (hg : ∀ᶠ y in 𝓝[≠] x, ∃ hy : IsUnit (log y), g y = Checked.inv (log y) hy) :
    ¬ ContinuousAt g x := by
  let U := {y : ℝ // IsUnit (log y)}
  let q (y : U) : ℝˣ := y.property.unit
  have hq : Tendsto q (comap Subtype.val (𝓝[≠] x))
      (comap ((↑) : ℝˣ → ℝ) (𝓝[≠] 0)) := by
    apply tendsto_comap_iff.mpr
    simpa only [Function.comp_def, q, IsUnit.unit_spec] using
      (tendsto_log_at_nonzero_root hx hlog).comp
        (tendsto_comap : Tendsto (Subtype.val : U → ℝ) (comap Subtype.val (𝓝[≠] x)) (𝓝[≠] x))
  have h : Tendsto g (𝓝[≠] x) (cobounded ℝ) := by
    apply tendsto_from_log_unit (f := fun y ↦ Checked.inv (log y.val) y.property) hg
    exact tendsto_inv₀_nhdsNE_zero.comp hq
  exact not_continuousAt_of_tendsto h nhdsWithin_le_nhds (disjoint_nhds_cobounded _)

lemma not_continuousAt_inv_log_one {g : ℝ → ℝ}
    (hg : ∀ᶠ y in 𝓝[≠] 1, ∃ hy : IsUnit (log y), g y = Checked.inv (log y) hy) :
    ¬ ContinuousAt g 1 :=
  not_continuousAt_inv_log_of_log_eq_zero one_ne_zero log_one hg

lemma not_continuousAt_inv_log_neg_one {g : ℝ → ℝ}
    (hg : ∀ᶠ y in 𝓝[≠] (-1), ∃ hy : IsUnit (log y), g y = Checked.inv (log y) hy) :
    ¬ ContinuousAt g (-1) :=
  not_continuousAt_inv_log_of_log_eq_zero (by norm_num) (by simp) hg

lemma not_differentiableAt_inv_log_zero {g : ℝ → ℝ}
    (hg : ∀ᶠ y in 𝓝[<] 0, ∃ hy : IsUnit (log y), g y = Checked.inv (log y) hy) :
    ¬ DifferentiableAt ℝ g 0 := by
  intro hd
  let D := {y : ℝ // IsUnit (log y)}
  let l := comap (Subtype.val : D → ℝ) (𝓝[<] 0)
  have hval : Tendsto (Subtype.val : D → ℝ) l (𝓝[<] 0) := tendsto_comap
  have hg₀ : Tendsto g (𝓝[<] 0) (𝓝 0) :=
    tendsto_from_log_unit hg
      ((tendsto_log_nhdsLT_zero.comp hval).fun_inv_tendsto_atBot (h0 := fun y ↦ y.2))
  have hzero := tendsto_nhds_unique (hd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hg₀
  have hyne (y : D) : (y : ℝ) ≠ 0 := (log_ne_zero.mp y.2.ne_zero).1
  let q : D → ({(0 : ℝ)}ᶜ : Set ℝ) := fun y ↦ ⟨y.val, hyne y⟩
  have hq : Tendsto q l (comap Subtype.val (𝓝 0)) :=
    tendsto_comap_iff.mpr (hval.mono_right nhdsWithin_le_nhds)
  have hslope := hd.hasDerivAt.tendsto_slope.comp hq
  have hsign : ∀ᶠ y : D in l, 0 < log y.val * y.val := by
    have hIoo : Ioo (-1 : ℝ) 0 ∈ 𝓝[<] 0 := Ioo_mem_nhdsLT (by norm_num)
    filter_upwards [hval.eventually hIoo] with y hy
    exact mul_pos_of_neg_of_neg (log_neg_eq_log y.val ▸ log_neg (by linarith [hy.2])
      (by linarith [hy.1])) hy.2
  have ht : Tendsto (fun y : D ↦ log y.val * y.val) l (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_log_mul_self_nhdsLT_zero.comp hval, hsign⟩
  have hdiv := ht.fun_inv_tendsto_nhdsGT_zero
    (h0 := fun y ↦ y.2.mul (hyne y).isUnit)
  have hs : Tendsto (fun y : D ↦ slope g 0 y.val (hyne y).symm) l atTop := by
    refine hdiv.congr' ?_
    filter_upwards [hval.eventually hg] with y ⟨_, hgy⟩
    have hunit := (hyne y).isUnit
    have hlog := y.2
    change Checked.inv (log y.val * y.val) (hlog.mul hunit) = slope g 0 y.val (hyne y).symm
    simp only [slope_def_field, hzero, sub_zero, hgy, div_eq_mul_inv₀, mul_inv₀]
  have hrange : range (Subtype.val : D → ℝ) ∈ 𝓝[<] 0 :=
    hg.mono fun x ⟨hx, _⟩ ↦ ⟨⟨x, hx⟩, rfl⟩
  let : NeBot l := NeBot.comap_of_range_mem inferInstance hrange
  exact hslope.not_tendsto (by simp) hs

theorem hasDerivAt_inv_log (x : {x : ℝ // IsUnit (log x)}) :
    HasDerivAt (fun y : {x : ℝ // IsUnit (log x)} ↦ Checked.inv (log y.val) y.2)
      (-(Checked.inv x.val (log_ne_zero.mp x.2.ne_zero).1.isUnit) / log x.val ^ 2)
      x Subtype.val := by
  have hpow : Checked.inv (log x.val ^ 2) (x.2.pow 2) = Checked.inv (log x.val) x.2 ^ 2 :=
    (inv_pow₀ (ha := x.2) 2).symm
  simpa only [div_eq_mul_inv₀, hpow] using!
    (hasDerivAt_log (hx := (log_ne_zero.mp x.2.ne_zero).1.isUnit)).inv x.2

theorem deriv_inv_log_apply (x : {x : ℝ // IsUnit (log x)}) :
    deriv (fun y : {x : ℝ // IsUnit (log x)} ↦ Checked.inv (log y.val) y.2) x Subtype.val =
      -(Checked.inv x.val (log_ne_zero.mp x.2.ne_zero).1.isUnit) / log x.val ^ 2 :=
  (hasDerivAt_inv_log x).deriv isOpen_log_unit.isOpenEmbedding_subtypeVal

@[simp]
theorem deriv_inv_log :
    (fun x : {x : ℝ // IsUnit (log x)} ↦
      deriv (fun y : {x : ℝ // IsUnit (log x)} ↦ Checked.inv (log y.val) y.2) x Subtype.val) =
      fun x ↦ -(Checked.inv x.val (log_ne_zero.mp x.2.ne_zero).1.isUnit) / log x.val ^ 2 :=
  funext deriv_inv_log_apply

theorem differentiableAt_inv_log (x : {x : ℝ // IsUnit (log x)}) :
    DifferentiableAt ℝ (fun y : {x : ℝ // IsUnit (log x)} ↦ Checked.inv (log y.val) y.2)
      x Subtype.val :=
  (hasDerivAt_inv_log x).differentiableAt

theorem differentiable_inv_log :
    Differentiable ℝ (fun y : {x : ℝ // IsUnit (log x)} ↦ Checked.inv (log y.val) y.2)
      Subtype.val :=
  differentiableAt_inv_log

theorem inv_log_isLittleO_one :
    (fun x : {x : ℝ // IsUnit (log x)} ↦ Checked.inv (log x.val) x.2) =o[comap Subtype.val atTop]
      fun _ ↦ (1 : ℝ) := by
  rw [isLittleO_one_iff]
  exact (tendsto_log_atTop.comp tendsto_comap).fun_inv_tendsto_atTop

/-! ## Derivative of the iterated logarithm -/

lemma not_continuousAt_log_log_zero {g : ℝ → ℝ}
    (hg : ∀ᶠ y in 𝓝[≠] (0 : ℝ), IsUnit (log y) ∧ g y = log (log y)) : ¬ ContinuousAt g 0 := by
  have hlog : Tendsto log atBot atTop := by
    convert tendsto_log_atTop.comp tendsto_neg_atBot_atTop using 1
    exact funext fun _ ↦ (log_neg_eq_log _).symm
  refine not_continuousAt_of_tendsto (l₁ := 𝓝[≠] (0 : ℝ)) ?_ nhdsWithin_le_nhds
    (disjoint_nhds_atTop _)
  exact (hlog.comp tendsto_log_nhdsNE_zero).congr'
    (hg.mono fun _ h ↦ h.2.symm)

private theorem not_continuousAt_log_log_of_log_eq_zero {g : ℝ → ℝ} {x : ℝ}
    (hx : x ≠ 0) (hlog : log x = 0)
    (hg : ∀ᶠ y in 𝓝[≠] x, IsUnit (log y) ∧ g y = log (log y)) : ¬ ContinuousAt g x := by
  refine not_continuousAt_of_tendsto (l₁ := 𝓝[≠] x) ?_ nhdsWithin_le_nhds
    (disjoint_nhds_atBot _)
  exact (tendsto_log_nhdsNE_zero.comp
    (tendsto_log_at_nonzero_root hx hlog)).congr' (hg.mono fun _ h ↦ h.2.symm)

lemma not_continuousAt_log_log_one {g : ℝ → ℝ}
    (hg : ∀ᶠ y in 𝓝[≠] (1 : ℝ), IsUnit (log y) ∧ g y = log (log y)) : ¬ ContinuousAt g 1 :=
  not_continuousAt_log_log_of_log_eq_zero one_ne_zero log_one hg

lemma not_continuousAt_log_log_neg_one {g : ℝ → ℝ}
    (hg : ∀ᶠ y in 𝓝[≠] (-1 : ℝ), IsUnit (log y) ∧ g y = log (log y)) : ¬ ContinuousAt g (-1) :=
  not_continuousAt_log_log_of_log_eq_zero (by norm_num) (by simp) hg

theorem hasDerivAt_log_log (x : {x : ℝ // IsUnit (log x)}) :
    HasDerivAt (fun y : {x : ℝ // IsUnit (log x)} ↦ log (log y.val))
      (Checked.inv x.val (log_ne_zero.mp x.2.ne_zero).1.isUnit / log x.val) x Subtype.val := by
  have h := (hasDerivAt_log (hx := (log_ne_zero.mp x.2.ne_zero).1.isUnit)).log (hx := x.2)
  exact h.hasFDerivAt.comp_tendsto Subtype.val
    (continuous_subtype_val.continuousAt.tendsto.prodMap (tendsto_pure_pure ..))

theorem deriv_log_log_apply (x : {x : ℝ // IsUnit (log x)}) :
    deriv (fun y : {x : ℝ // IsUnit (log x)} ↦ log (log y.val)) x Subtype.val =
      Checked.inv x.val (log_ne_zero.mp x.2.ne_zero).1.isUnit / log x.val :=
  (hasDerivAt_log_log x).deriv isOpen_log_unit.isOpenEmbedding_subtypeVal

@[simp]
theorem deriv_log_log :
    (fun x : {x : ℝ // IsUnit (log x)} ↦
      deriv (fun y : {x : ℝ // IsUnit (log x)} ↦ log (log y.val)) x Subtype.val) =
      fun x ↦ Checked.inv x.val (log_ne_zero.mp x.2.ne_zero).1.isUnit / log x.val :=
  funext deriv_log_log_apply

theorem differentiableAt_log_log (x : {x : ℝ // IsUnit (log x)}) :
    DifferentiableAt ℝ (fun y : {x : ℝ // IsUnit (log x)} ↦ log (log y.val))
      x Subtype.val :=
  (hasDerivAt_log_log x).differentiableAt

theorem differentiable_log_log :
    Differentiable ℝ (fun y : {x : ℝ // IsUnit (log x)} ↦ log (log y.val)) Subtype.val :=
  differentiableAt_log_log

theorem one_isLittleO_log_log :
    (fun _ ↦ (1 : ℝ)) =o[comap Subtype.val atTop]
      (fun x : {x : ℝ // IsUnit (log x)} ↦ log (log x.val)) := by
  rw [isLittleO_one_left_iff]
  simpa only [norm_eq_abs, Function.comp_def] using
    (tendsto_abs_atTop_atTop.comp (tendsto_log_atTop.comp tendsto_log_atTop)).comp tendsto_comap

end Real
