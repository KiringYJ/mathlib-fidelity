/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Taylor series converges to function on whole ball

In this file we prove that if a function `f` is analytic on the ball of convergence of its Taylor
series, then the series converges to `f` on this ball.
-/

public section

open Filter
open scoped Topology

section Coefficients

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {F : Type*}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  {p : FormalMultilinearSeries 𝕜 𝕜 F} {r : ENNReal}

variable {D : Type*} [TopologicalSpace D] {coord : D → 𝕜} {z : D} {u : D → F}

/-- The termwise scalar derivative of a power series represents a derivative on its original
coordinate domain throughout the ball. -/
theorem HasFPowerSeriesOnBall.exists_hasFPowerSeriesOnBall_deriv
    (h : HasFPowerSeriesOnBall u p z r coord) (hcoord : Continuous coord) :
    ∃ g : D → F, HasFPowerSeriesOnBall g
      ((ContinuousLinearMap.apply 𝕜 F (1 : 𝕜)).compFormalMultilinearSeries p.derivSeries)
      z r coord ∧
      ∀ y : D, coord y - coord z ∈ Metric.eball 0 r → HasDerivAt u (g y) y coord := by
  let evaluate : (𝕜 [×1]→L[𝕜] F) →L[𝕜] F :=
    ContinuousLinearMap.apply 𝕜 F (1 : 𝕜) ∘L
      (continuousMultilinearCurryFin1 𝕜 𝕜 F).toContinuousLinearEquiv.toContinuousLinearMap
  let g (y : D) := evaluate (p.changeOrigin (coord y - coord z) 1)
  refine ⟨g, ?_, ?_⟩
  · have hshift : HasFPowerSeriesOnBall (fun w ↦ p.changeOrigin (w - coord z) 1)
        (p.changeOriginSeries 1) (coord z) r := by
      simpa only [zero_add] using
        ((p.hasFPowerSeriesOnBall_changeOrigin 1
          (h.r_pos.trans_le h.r_le)).mono h.r_pos h.r_le).comp_sub (coord z)
    have he : evaluate.compFormalMultilinearSeries (p.changeOriginSeries 1) =
        (ContinuousLinearMap.apply 𝕜 F (1 : 𝕜)).compFormalMultilinearSeries p.derivSeries := by
      ext n
      rfl
    simpa only [g, he, Function.comp_def, id_eq] using
      (evaluate.comp_hasFPowerSeriesOnBall hshift).comp_domain (g := coord) (x := z)
  · intro y hy
    let v (t : 𝕜) := p.sum (t - coord z)
    have hv : HasFPowerSeriesOnBall v p (coord z) r := by
      simpa only [v, zero_add] using
        ((p.hasFPowerSeriesOnBall (h.r_pos.trans_le h.r_le)).mono h.r_pos h.r_le).comp_sub
          (coord z)
    have hy' : (‖coord y - coord z‖₊ : ENNReal) < r := by
      simpa only [Metric.mem_eball, edist_zero_right, enorm] using hy
    have hd := (hv.changeOrigin hy').hasFPowerSeriesAt.hasDerivAt
    rw [add_sub_cancel] at hd
    have hv₁ : Fin.snoc (α := fun _ : Fin 1 ↦ 𝕜) (0 : Fin 0 → 𝕜) 1 = fun _ ↦ 1 := by
      funext i
      obtain rfl : i = 0 := Fin.eq_zero i
      rfl
    have hdy : HasIteratedDerivAt 1 v (g y) (coord y) := by
      apply HasIteratedDerivAt.one.mpr
      simpa [g, evaluate, hv₁] using hd
    apply HasIteratedDerivAt.one.mp ((hdy.comp_domain hcoord).congr_of_eventuallyEq ?_)
    have hopen : IsOpen {y : D | coord y - coord z ∈ Metric.eball 0 r} :=
      Metric.isOpen_eball.preimage (hcoord.sub continuous_const)
    filter_upwards [hopen.mem_nhds hy] with w hw
    exact (h.hasSum (y := w) hw).tsum_eq.symm

/-- The `n`-th scalar derivative is `n!` times the corresponding Taylor coefficient.
The derivative relation is on the original coordinate domain. -/
theorem HasFPowerSeriesAt.hasIteratedDerivAt_coeff
    (h : HasFPowerSeriesAt u p z coord) (hcoord : Continuous coord) (n : ℕ) :
    HasIteratedDerivAt n u (n.factorial • p.coeff n) z coord := by
  induction n generalizing p u with
  | zero =>
      simpa only [HasIteratedDerivAt.zero, Nat.factorial_zero, one_smul,
        FormalMultilinearSeries.coeff] using
        (h.coeff_zero (1 : Fin 0 → 𝕜)).symm
  | succ n ih =>
      obtain ⟨r, hr⟩ := h
      obtain ⟨g, hg, hd⟩ := hr.exists_hasFPowerSeriesOnBall_deriv hcoord
      have hcenter : coord z - coord z ∈ Metric.eball (0 : 𝕜) r := by simpa using hr.r_pos
      refine ⟨g, hd z hcenter, Or.inr ?_, ?_⟩
      · have hopen : IsOpen {y : D | coord y - coord z ∈ Metric.eball 0 r} :=
          Metric.isOpen_eball.preimage (hcoord.sub continuous_const)
        filter_upwards [hopen.mem_nhds hcenter] with y hy
        exact hd y hy
      · have hgn := ih hg.hasFPowerSeriesAt
        change HasIteratedDerivAt n g (n.factorial • p.derivSeries.coeff n 1) z coord at hgn
        rw [p.derivSeries_coeff_one, ← mul_smul, Nat.mul_comm, ← Nat.factorial_succ] at hgn
        exact hgn

/-- The Taylor remainder on the original domain is a power of the displacement times an
analytic function of that displacement. The polynomial is read directly from the given series. -/
theorem HasFPowerSeriesAt.exists_eventuallyEq_sum_add_pow_smul
    (h : HasFPowerSeriesAt u p z coord) (hcoord : Continuous coord) (n : ℕ) :
    ∃ R : 𝕜 → F, AnalyticAt 𝕜 R 0 ∧ ∀ᶠ y in 𝓝 z,
      u y = (∑ k ∈ Finset.range n, (coord y - coord z) ^ k • p.coeff k) +
        (coord y - coord z) ^ n • R (coord y - coord z) := by
  obtain ⟨ρ, hρ⟩ := h
  let q := FormalMultilinearSeries.fslope^[n] p
  let a (j : ℕ) : F := if j < n then 0 else p.coeff j
  have ha (j : ℕ) (hj : j < n) : a j = 0 := ite_eq_left hj
  have ha' (j : ℕ) : a (j + n) = p.coeff (j + n) :=
    ite_eq_right (Nat.not_lt.mpr (Nat.le_add_left n j))
  have hs : ∀ᶠ w in 𝓝 (0 : 𝕜), HasSum (fun k ↦ w ^ k • p.coeff k) (p.sum w) := by
    simpa only [zero_add] using hasFPowerSeriesAt_iff.mp
      (p.hasFPowerSeriesOnBall (hρ.r_pos.trans_le hρ.r_le)).hasFPowerSeriesAt
  have htail : ∀ᶠ w in 𝓝 (0 : 𝕜),
      HasSum (fun k ↦ w ^ k • q.coeff k) (q.sum w) ∧
      p.sum w = (∑ k ∈ Finset.range n, w ^ k • p.coeff k) + w ^ n • q.sum w := by
    filter_upwards [hs] with w hw
    have hz : ∑ k ∈ Finset.range n, w ^ k • a k = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rw [ha k (Finset.mem_range.mp hk), smul_zero]
    have hshift : HasSum (fun k ↦ w ^ k • a k)
        (p.sum w - ∑ k ∈ Finset.range n, w ^ k • p.coeff k) := by
      apply (hasSum_nat_add_iff' n).mp
      simpa only [Function.comp_def, hz, sub_zero, ha'] using (hasSum_nat_add_iff' n).mpr hw
    obtain ⟨v, hmul, hv⟩ := hshift.exists_hasSum_smul_of_apply_eq_zero ha
    have hvq : HasSum (fun k ↦ w ^ k • q.coeff k) v := by
      simpa only [q, FormalMultilinearSeries.coeff_iterate_fslope, ha'] using hv
    have hq : q.sum w = v := by
      simpa only [FormalMultilinearSeries.sum, FormalMultilinearSeries.apply_eq_pow_smul_coeff]
        using hvq.tsum_eq
    refine ⟨hq.symm ▸ hvq, ?_⟩
    rw [hq, hmul]
    abel
  refine ⟨q.sum, ?_, ?_⟩
  · have hq : HasFPowerSeriesAt q.sum q (0 : 𝕜) := by
      apply hasFPowerSeriesAt_iff.mpr
      simpa only [zero_add] using htail.mono (fun _ hw ↦ hw.1)
    exact hq.analyticAt
  · have ht : Tendsto (fun y ↦ coord y - coord z) (𝓝 z) (𝓝 (0 : 𝕜)) := by
      have hcont : ContinuousAt (fun y ↦ coord y - coord z) z :=
        hcoord.continuousAt.sub continuousAt_const
      simpa only [sub_self] using hcont.tendsto
    filter_upwards [ht.eventually htail, ht.eventually (Metric.eball_mem_nhds 0 hρ.r_pos)]
      with y hy hyn
    exact (hρ.hasSum hyn).tsum_eq.symm.trans hy.2

end Coefficients

variable {𝕜 : Type*} [RCLike 𝕜] {F : Type*}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  {f : 𝕜 → F} {x : 𝕜} {p : FormalMultilinearSeries 𝕜 𝕜 F}

/-- If `f` is analytic on `Bᵣ(x₀)` and its Taylor series converges on this ball, then it converges
to `f`. -/
theorem AnalyticOn.hasFPowerSeriesOnSubball
    {r : ENNReal} (hr_pos : 0 < r) (h : AnalyticOn 𝕜 f (Metric.eball x r))
    (hp : HasFPowerSeriesAt f p x) (hr : r ≤ p.radius) : HasFPowerSeriesOnBall f p x r := by
  rw [Metric.isOpen_eball.analyticOn_iff_analyticOnNhd] at h
  let g (t : 𝕜) := p.sum (t - x)
  have hg : HasFPowerSeriesOnBall g p x p.radius := by
    simpa using (p.hasFPowerSeriesOnBall (by order)).comp_sub x
  have hg' : AnalyticOnNhd 𝕜 g (Metric.eball x p.radius) := by
    simpa using p.analyticOnNhd.comp_sub x
  replace hg' : AnalyticOnNhd 𝕜 g (Metric.eball x r) := hg'.mono (Metric.eball_subset_eball hr)
  apply h.eqOn_of_preconnected_of_eventuallyEq at hg'
  apply (hg.mono hr_pos hr).congr
  symm
  apply hg' (Metric.isConnected_eball hr_pos).isPreconnected (show x ∈ Metric.eball x r by simpa) ?_
  unfold Filter.EventuallyEq Filter.Eventually
  rw [EMetric.mem_nhds_iff]
  obtain ⟨ε, hp⟩ := hp
  exact ⟨ε, hp.r_pos, hp.unique (hg.mono hp.r_pos hp.r_le)⟩

/-- If `f` is analytic on the ball of convergence of its Taylor series, then the series converges
to `f` on this ball. The assumption `RCLike 𝕜` provides the connectedness of the ball.

For example, over the `p`-adic numbers, the indicator function of the unit ball is
analytic everywhere, but it agrees with the sum of its Taylor series only on this unit ball. -/
theorem AnalyticOn.hasFPowerSeriesOnBall :
    HasFPowerSeriesAt f p x → 0 < p.radius → AnalyticOn 𝕜 f (Metric.eball x p.radius) →
    HasFPowerSeriesOnBall f p x p.radius := by
  intro hp hr hs
  exact hs.hasFPowerSeriesOnSubball hr hp le_rfl
