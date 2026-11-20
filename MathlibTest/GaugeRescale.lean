import Mathlib.Analysis.Convex.GaugeRescale

open Set
open scoped Pointwise

noncomputable section

-- The origin is fixed even when no positive dilate of either set contains it.
example : gaugeRescale (∅ : Set ℝ) ∅ ⟨0, zero_mem_gaugeRescaleDomain _ _⟩ = 0 :=
  gaugeRescale_zero _ _

-- A finite target gauge does not supply a missing finite source gauge.
example (t : Set ℝ) : (1 : ℝ) ∉ gaugeRescaleDomain ∅ t := by
  intro h
  obtain ⟨r, hr, y, hy, he⟩ := (h one_ne_zero).1
  exact hy

-- Every positive dilate of the whole line contains one, so its gauge is zero there.
private theorem gauge_univ_one : gauge (univ : Set ℝ) 1 = 0 := by
  rw [gauge_def']
  simp only [mem_univ, exists_prop, and_true]
  exact csInf_Ioi

-- A zero target gauge makes the rescaling undefined at this nonzero point.
example : (1 : ℝ) ∉ gaugeRescaleDomain univ univ :=
  fun h ↦ (h one_ne_zero).2.2 gauge_univ_one

-- A finite source gauge may vanish. With a positive target gauge its image is the origin.
example : ∃ hd : (1 : ℝ) ∈ gaugeRescaleDomain univ (Metric.ball (0 : ℝ) 1),
    gaugeRescale univ (Metric.ball (0 : ℝ) 1) ⟨1, hd⟩ = 0 := by
  have hd := mem_gaugeRescaleDomain (s := (univ : Set ℝ)) (t := Metric.ball 0 1)
    absorbent_univ (absorbent_nhds_zero (Metric.ball_mem_nhds _ one_pos))
    (NormedSpace.isVonNBounded_ball _ _ _) 1
  refine ⟨hd, ?_⟩
  rw [gaugeRescale_of_ne_zero _ one_ne_zero, gauge_univ_one]
  simp
