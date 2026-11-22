/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Analytic.Linear
public import Mathlib.Analysis.Analytic.Composition
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Analysis.Analytic.ChangeOrigin

/-!
# Uniqueness principle for analytic functions

We show that two analytic functions which coincide around a point coincide on whole connected sets,
in `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`.
-/

public section


variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

open Set

open scoped Topology ENNReal NNReal

/-!
### Uniqueness of power series
If a function `f : E → F` has two representations as power series at a point `x : E`, corresponding
to formal multilinear series `p₁` and `p₂`, then these representations agree term-by-term. That is,
for any `n : ℕ` and `y : E`, `p₁ n (fun i ↦ y) = p₂ n (fun i ↦ y)`. In the one-dimensional case,
when `f : 𝕜 → E`, the continuous multilinear maps `p₁ n` and `p₂ n` are given by
`ContinuousMultilinearMap.mkPiRing`, and hence are determined completely by the value of
`p₁ n (fun i ↦ 1)`, so `p₁ = p₂`. Consequently, the radius of convergence for one series can be
transferred to the other.
-/

section Uniqueness

open ContinuousMultilinearMap

theorem Asymptotics.IsBigO.continuousMultilinearMap_apply_eq_zero {n : ℕ} {p : E [×n]→L[𝕜] F}
    (h : (fun y => p fun _ => y) =O[𝓝 0] fun y => ‖y‖ ^ (n + 1)) (y : E) : (p fun _ => y) = 0 := by
  obtain ⟨c, c_pos, hc⟩ := h.exists_pos
  obtain ⟨t, ht, t_open, z_mem⟩ := eventually_nhds_iff.mp (isBigOWith_iff.mp hc)
  obtain ⟨δ, δ_pos, δε⟩ := (Metric.isOpen_iff.mp t_open) 0 z_mem
  clear h hc z_mem
  rcases n with - | n
  · exact norm_eq_zero.mp (by
      simpa only [fin0_apply_norm, norm_eq_zero, norm_zero, zero_add, pow_one,
        mul_zero, norm_le_zero_iff] using! ht 0 (δε (Metric.mem_ball_self δ_pos)))
  · refine Or.elim (Classical.em (y = 0))
      (fun hy => by simpa only [hy] using! p.map_zero) fun hy => ?_
    replace hy := norm_pos_iff.mpr hy
    refine norm_eq_zero.mp (le_antisymm (le_of_forall_pos_le_add fun ε ε_pos => ?_) (norm_nonneg _))
    have h₀ := _root_.mul_pos c_pos (pow_pos hy (n.succ + 1))
    obtain ⟨k, k_pos, k_norm⟩ := NormedField.exists_norm_lt 𝕜
      (lt_min (mul_pos δ_pos (inv_pos.mpr hy)) (mul_pos ε_pos (inv_pos.mpr h₀)))
    have h₁ : ‖k • y‖ < δ := by
      rw [norm_smul]
      exact inv_mul_cancel_right₀ (hb := hy.ne'.isUnit) δ ▸
        mul_lt_mul_of_pos_right (lt_of_lt_of_le k_norm (min_le_left _ _)) hy
    have h₂ :=
      calc
        ‖p fun _ => k • y‖ ≤ c * ‖k • y‖ ^ (n.succ + 1) := by
          simpa only [norm_pow, _root_.norm_norm] using! ht (k • y) (δε (mem_ball_zero_iff.mpr h₁))
        _ = ‖k‖ ^ n.succ * (‖k‖ * (c * ‖y‖ ^ (n.succ + 1))) := by
          simp only [norm_smul, mul_pow]
          ring
    have h₃ : ‖k‖ * (c * ‖y‖ ^ (n.succ + 1)) < ε :=
      inv_mul_cancel_right₀ (hb := h₀.ne'.isUnit) ε ▸
        mul_lt_mul_of_pos_right (lt_of_lt_of_le k_norm (min_le_right _ _)) h₀
    calc
      ‖p fun _ => y‖ = ‖k⁻¹ ^ n.succ‖ * ‖p fun _ => k • y‖ := by
        have hscale := congr_arg norm
          (p.map_smul_univ (fun _ : Fin n.succ => k⁻¹) fun _ : Fin n.succ => k • y)
        rw [Finset.prod_const, Finset.card_fin] at hscale
        simpa only [inv_smul_smul₀ (ha := (norm_pos_iff.mp k_pos).isUnit), norm_smul] using hscale
      _ ≤ ‖k⁻¹ ^ n.succ‖ * (‖k‖ ^ n.succ * (‖k‖ * (c * ‖y‖ ^ (n.succ + 1)))) := by gcongr
      _ = ‖(k⁻¹ * k) ^ n.succ‖ * (‖k‖ * (c * ‖y‖ ^ (n.succ + 1))) := by
        rw [← mul_assoc]
        simp
      _ ≤ 0 + ε := by
        rw [inv_mul_cancel₀ (ha := (norm_pos_iff.mp k_pos).isUnit)]
        simpa using! h₃.le

/-- If a formal multilinear series represents the zero function on a coordinate domain covering
a neighbourhood of its centre, then its diagonal terms vanish. -/
theorem HasFPowerSeriesAt.apply_eq_zero {D : Type*} {coord : D → E}
    {p : FormalMultilinearSeries 𝕜 E F} {x : D}
    (h : HasFPowerSeriesAt 0 p x coord) (n : ℕ) (y : E)
    (hcover : Set.range coord ∈ 𝓝 (coord x) := by simp) : (p n fun _ => y) = 0 := by
  have h : HasFPowerSeriesAt (0 : E → F) p (coord x) := h.of_comp_domain hcover
  revert y
  refine Nat.strong_induction_on n fun k hk => ?_
  have psum_eq : p.partialSum (k + 1) = fun y => p k fun _ => y := by
    funext z
    refine Finset.sum_eq_single _ (fun b hb hnb => ?_) fun hn => ?_
    · have := Finset.mem_range_succ_iff.mp hb
      simp only [hk b (this.lt_of_ne hnb)]
    · exact False.elim (hn (Finset.mem_range.mpr (lt_add_one k)))
  replace h := h.isBigO_sub_partialSum_pow k.succ
  simp only [psum_eq, zero_sub, Pi.zero_apply, Asymptotics.isBigO_neg_left] at h
  exact h.continuousMultilinearMap_apply_eq_zero

/-- A one-dimensional formal multilinear series representing the zero function on a coordinate
domain covering a neighbourhood of its centre is zero. -/
theorem HasFPowerSeriesAt.eq_zero {D : Type*} {coord : D → 𝕜}
    {p : FormalMultilinearSeries 𝕜 𝕜 E} {x : D}
    (h : HasFPowerSeriesAt 0 p x coord)
    (hcover : Set.range coord ∈ 𝓝 (coord x) := by simp) : p = 0 := by
  ext n
  rw [← mkPiRing_apply_one_eq_self (p n)]
  simp [h.apply_eq_zero n 1 hcover]

/-- One-dimensional formal multilinear series representing the same function are equal when
the coordinate domain covers a neighbourhood of the centre. -/
theorem HasFPowerSeriesAt.eq_formalMultilinearSeries {D : Type*} {coord : D → 𝕜}
    {p₁ p₂ : FormalMultilinearSeries 𝕜 𝕜 E} {f : D → E} {x : D}
    (h₁ : HasFPowerSeriesAt f p₁ x coord) (h₂ : HasFPowerSeriesAt f p₂ x coord)
    (hcover : Set.range coord ∈ 𝓝 (coord x) := by simp) : p₁ = p₂ := by
  obtain ⟨r₁, h₁⟩ := h₁
  obtain ⟨r₂, h₂⟩ := h₂
  have hzero : HasFPowerSeriesAt ((0 : 𝕜 → E) ∘ coord) (p₁ - p₂) x coord := by
    refine ⟨min r₁ r₂, ?_⟩
    simpa only [Function.comp_def, Pi.zero_def, sub_self] using
      (h₁.mono (lt_min h₁.r_pos h₂.r_pos) (min_le_left _ _)).sub
        (h₂.mono (lt_min h₁.r_pos h₂.r_pos) (min_le_right _ _))
  exact sub_eq_zero.mp (hzero.eq_zero hcover)

theorem HasFPowerSeriesAt.eq_formalMultilinearSeries_of_eventually
    {p q : FormalMultilinearSeries 𝕜 𝕜 E} {f g : 𝕜 → E} {x : 𝕜} (hp : HasFPowerSeriesAt f p x)
    (hq : HasFPowerSeriesAt g q x) (heq : ∀ᶠ z in 𝓝 x, f z = g z) : p = q :=
  (hp.congr heq).eq_formalMultilinearSeries hq

/-- A one-dimensional formal multilinear series representing a locally zero function is zero. -/
theorem HasFPowerSeriesAt.eq_zero_of_eventually {p : FormalMultilinearSeries 𝕜 𝕜 E} {f : 𝕜 → E}
    {x : 𝕜} (hp : HasFPowerSeriesAt f p x) (hf : f =ᶠ[𝓝 x] 0) : p = 0 :=
  (hp.congr hf).eq_zero

/-- Two power series representations on a coordinate domain covering a neighbourhood of the
centre may exchange their convergence radii. This can be useful when the formal multilinear series
in one representation has a particularly nice form, but the other has a larger radius. -/
theorem HasFPowerSeriesOnBall.exchange_radius {D : Type*} {coord : D → 𝕜}
    {p₁ p₂ : FormalMultilinearSeries 𝕜 𝕜 E} {f : D → E} {r₁ r₂ : ℝ≥0∞} {x : D}
    (h₁ : HasFPowerSeriesOnBall f p₁ x r₁ coord)
    (h₂ : HasFPowerSeriesOnBall f p₂ x r₂ coord)
    (hcover : Set.range coord ∈ 𝓝 (coord x) := by simp) :
    HasFPowerSeriesOnBall f p₁ x r₂ coord :=
  h₂.hasFPowerSeriesAt.eq_formalMultilinearSeries h₁.hasFPowerSeriesAt hcover ▸ h₂

/-- If a function `f : 𝕜 → E` has power series representation `p` on a ball of some radius and for
each positive radius it has some power series representation, then `p` converges to `f` on the whole
`𝕜`. -/
theorem HasFPowerSeriesOnBall.r_eq_top_of_exists {f : 𝕜 → E} {r : ℝ≥0∞} {x : 𝕜}
    {p : FormalMultilinearSeries 𝕜 𝕜 E} (h : HasFPowerSeriesOnBall f p x r)
    (h' : ∀ (r' : ℝ≥0) (_ : 0 < r'), ∃ p' : FormalMultilinearSeries 𝕜 𝕜 E,
      HasFPowerSeriesOnBall f p' x r') :
    HasFPowerSeriesOnBall f p x ∞ :=
  { r_le := ENNReal.le_of_forall_pos_nnreal_lt fun r hr _ =>
      let ⟨_, hp'⟩ := h' r hr
      (h.exchange_radius hp').r_le
    r_pos := ENNReal.coe_lt_top
    hasSum := fun {y} _ =>
      let ⟨r', hr'⟩ := exists_gt ‖y - x‖₊
      let ⟨_, hp'⟩ := h' r' hr'.ne_bot.bot_lt
      (h.exchange_radius hp').hasSum (y := y) <|
        mem_eball_zero_iff.mpr (ENNReal.coe_lt_coe.2 hr') }

end Uniqueness

namespace AnalyticOnNhd

/-- If an analytic function vanishes around a point, then it is uniformly zero along
a connected set. Superseded by `AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero` which
does not assume completeness of the target space. -/
theorem eqOn_zero_of_preconnected_of_eventuallyEq_zero_aux [CompleteSpace F] {f : E → F} {U : Set E}
    (hf : AnalyticOnNhd 𝕜 f U) (hU : IsPreconnected U)
    {z₀ : E} (h₀ : z₀ ∈ U) (hfz₀ : f =ᶠ[𝓝 z₀] 0) :
    EqOn f 0 U := by
  /- Let `u` be the set of points around which `f` vanishes. It is clearly open. We have to show
    that its limit points in `U` still belong to it, from which the inclusion `U ⊆ u` will follow
    by connectedness. -/
  let u := {x | f =ᶠ[𝓝 x] 0}
  suffices main : closure u ∩ U ⊆ u by
    have Uu : U ⊆ u :=
      hU.subset_of_closure_inter_subset isOpen_setOfPred_eventually_nhds ⟨z₀, h₀, hfz₀⟩ main
    intro z hz
    simpa using mem_of_mem_nhds (Uu hz)
  /- Take a limit point `x`, then a ball `B (x, r)` on which it has a power series expansion, and
    then `y ∈ B (x, r/2) ∩ u`. Then `f` has a power series expansion on `B (y, r/2)` as it is
    contained in `B (x, r)`. All the coefficients in this series expansion vanish, as `f` is zero
    on a neighborhood of `y`. Therefore, `f` is zero on `B (y, r/2)`. As this ball contains `x`,
    it follows that `f` vanishes on a neighborhood of `x`, proving the claim. -/
  rintro x ⟨xu, xU⟩
  rcases hf x xU with ⟨p, r, hp⟩
  obtain ⟨hpos, hle, hadd⟩ : 0 < r / 2 ∧ r / 2 ≤ r ∧ r / 2 + r / 2 = r :=
    ⟨ENNReal.half_pos hp.r_pos.ne', ENNReal.half_le_self, ENNReal.add_halves r⟩
  obtain ⟨y, yu, hxy⟩ : ∃ y ∈ u, edist x y < r / 2 :=
    EMetric.mem_closure_iff.1 xu (r / 2) hpos
  let q := p.changeOrigin (y - x)
  have has_series : HasFPowerSeriesOnBall f q y (r / 2) := by
    have A : (‖y - x‖₊ : ℝ≥0∞) < r / 2 := by rwa [edist_comm, edist_eq_enorm_sub] at hxy
    have := hp.changeOrigin (A.trans_le hle)
    simp only [add_sub_cancel] at this
    apply this.mono hpos
    apply ENNReal.le_sub_of_add_le_left ENNReal.coe_ne_top
    exact (add_le_add_left A.le (r / 2)).trans_eq hadd
  have M : Metric.eball y (r / 2) ∈ 𝓝 x := Metric.isOpen_eball.mem_nhds hxy
  filter_upwards [M] with z hz
  have A : HasSum (fun n : ℕ => q n fun _ : Fin n => z - y) (f z) := has_series.hasSum_sub hz
  have B : HasSum (fun n : ℕ => q n fun _ : Fin n => z - y) 0 := by
    have : HasFPowerSeriesAt 0 q y := has_series.hasFPowerSeriesAt.congr yu
    convert! hasSum_zero (α := F) using 1
    ext n
    exact this.apply_eq_zero n _
  exact HasSum.unique A B

/-- The *identity principle* for analytic functions: If an analytic function vanishes in a whole
neighborhood of a point `z₀`, then it is uniformly zero along a connected set. For a one-dimensional
version assuming only that the function vanishes at some points arbitrarily close to `z₀`, see
`AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero`. -/
theorem eqOn_zero_of_preconnected_of_eventuallyEq_zero {f : E → F} {U : Set E}
    (hf : AnalyticOnNhd 𝕜 f U) (hU : IsPreconnected U)
    {z₀ : E} (h₀ : z₀ ∈ U) (hfz₀ : f =ᶠ[𝓝 z₀] 0) :
    EqOn f 0 U := by
  let F' := UniformSpace.Completion F
  set e : F →L[𝕜] F' := UniformSpace.Completion.toComplL
  have : AnalyticOnNhd 𝕜 (e ∘ f) U := fun x hx => (e.analyticAt _).comp (hf x hx)
  have A : EqOn (e ∘ f) 0 U := by
    apply eqOn_zero_of_preconnected_of_eventuallyEq_zero_aux this hU h₀
    filter_upwards [hfz₀] with x hx
    simp only [hx, Function.comp_apply, Pi.zero_apply, map_zero]
  intro z hz
  have : e (f z) = e 0 := by simpa only using! A hz
  exact UniformSpace.Completion.coe_injective F this

/-- The *identity principle* for analytic functions: If two analytic functions coincide in a whole
neighborhood of a point `z₀`, then they coincide globally along a connected set.
For a one-dimensional version assuming only that the functions coincide at some points
arbitrarily close to `z₀`, see `AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq`. -/
theorem eqOn_of_preconnected_of_eventuallyEq {f g : E → F} {U : Set E} (hf : AnalyticOnNhd 𝕜 f U)
    (hg : AnalyticOnNhd 𝕜 g U) (hU : IsPreconnected U) {z₀ : E} (h₀ : z₀ ∈ U) (hfg : f =ᶠ[𝓝 z₀] g) :
    EqOn f g U := by
  have hfg' : f - g =ᶠ[𝓝 z₀] 0 := hfg.mono fun z h => by simp [h]
  simpa [sub_eq_zero] using! fun z hz =>
    (hf.sub hg).eqOn_zero_of_preconnected_of_eventuallyEq_zero hU h₀ hfg' hz

/-- The *identity principle* for analytic functions: If two analytic functions on a normed space
coincide in a neighborhood of a point `z₀`, then they coincide everywhere.
For a one-dimensional version assuming only that the functions coincide at some points
arbitrarily close to `z₀`, see `AnalyticOnNhd.eq_of_frequently_eq`. -/
theorem eq_of_eventuallyEq {f g : E → F} [PreconnectedSpace E] (hf : AnalyticOnNhd 𝕜 f univ)
    (hg : AnalyticOnNhd 𝕜 g univ) {z₀ : E} (hfg : f =ᶠ[𝓝 z₀] g) : f = g :=
  funext fun x =>
    eqOn_of_preconnected_of_eventuallyEq hf hg isPreconnected_univ (mem_univ z₀) hfg (mem_univ x)

end AnalyticOnNhd
