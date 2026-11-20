/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Analytic.ConvergenceRadius
public import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
# Analytic functions

A function is analytic in one dimension around `0` if it can be written as a converging power series
`Σ pₙ zⁿ`. This definition can be extended to any dimension (even in infinite dimension) by
requiring that `pₙ` is a continuous `n`-multilinear map. In general, `pₙ` is not unique (in two
dimensions, taking `p₂ (x, y) (x', y') = x y'` or `y x'` gives the same map when applied to a
vector `(x, y) (x, y)`). A way to guarantee uniqueness is to take a symmetric `pₙ`, but this is not
always possible in nonzero characteristic (in characteristic 2, the previous example has no
symmetric representative). Therefore, we do not insist on symmetry or uniqueness in the definition,
and we only require the existence of a converging series.

The general framework is important to say that the exponential map on bounded operators on a Banach
space is analytic, as well as the inverse on invertible operators.

## Main definitions

Let `p` be a formal multilinear series from `E` to `F`, i.e., `p n` is a multilinear map on `E^n`
for `n : ℕ`.

* `HasFPowerSeriesOnBall f p x r`: on the ball of center `x` with radius `r`,
  `f (x + y) = ∑'_n pₙ yⁿ`.
* `HasFPowerSeriesAt f p x`: on some ball of center `x` with positive radius, holds
  `HasFPowerSeriesOnBall f p x r`.
* `AnalyticAt 𝕜 f x`: there exists a power series `p` such that holds `HasFPowerSeriesAt f p x`.
* `AnalyticOnNhd 𝕜 f s`: the function `f` is analytic at every point of `s`.

We also define versions of `HasFPowerSeriesOnBall`, `AnalyticAt`, and `AnalyticOnNhd` restricted to
a set, similar to `ContinuousWithinAt`.
See `Mathlib/Analysis/Analytic/Within.lean` for basic properties.

* `AnalyticWithinAt 𝕜 f s x` means a power series at `x` converges to `f` on `𝓝[s ∪ {x}] x`.
* `AnalyticOn 𝕜 f s t` means `∀ x ∈ t, AnalyticWithinAt 𝕜 f s x`.

We develop the basic properties of these notions, notably:
* If a function admits a power series, it is continuous (see
  `HasFPowerSeriesOnBall.continuousOn` and `HasFPowerSeriesAt.continuousAt` and
  `AnalyticAt.continuousAt`).
* In a complete space, the sum of a formal power series with positive radius is well defined on the
  disk of convergence, see `FormalMultilinearSeries.hasFPowerSeriesOnBall`.

-/

@[expose] public section

variable {𝕜 E F G : Type*}

variable [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]

open NNReal Filter ENNReal Set Asymptotics

open scoped Topology Pointwise

/-! ### Expanding a function as a power series -/

section

variable {f g : E → F} {p pf : FormalMultilinearSeries 𝕜 E F} {s t : Set E} {x : E} {r r' : ℝ≥0∞}

/-- A power series on a coordinate ball. Its coefficients act on the ambient vector space `E`,
while `f` is evaluated only at points of its actual domain `D`. -/
structure HasFPowerSeriesOnBall {D : Type*} (f : D → F)
    (p : FormalMultilinearSeries 𝕜 E F) (x : D) (r : ℝ≥0∞)
    (coord : D → E := by exact _root_.id) : Prop where
  r_le : r ≤ p.radius
  r_pos : 0 < r
  hasSum : ∀ {y}, coord y - coord x ∈ Metric.eball (0 : E) r →
    HasSum (fun n : ℕ => p n fun _ : Fin n => coord y - coord x) (f y)

/-- A power series restricted to a subset of its coordinate domain. Convergence is required at
the centre as well as at the specified points of `s`. -/
structure HasFPowerSeriesWithinOnBall {D : Type*} (f : D → F)
    (p : FormalMultilinearSeries 𝕜 E F) (s : Set D) (x : D) (r : ℝ≥0∞)
    (coord : D → E := by exact _root_.id) : Prop where
  /-- `p` converges on `ball 0 r` -/
  r_le : r ≤ p.radius
  /-- The radius of convergence is positive -/
  r_pos : 0 < r
  /-- `p` converges to `f` at points of the coordinate ball lying in `s` or at its centre. -/
  hasSum : ∀ {y}, y ∈ insert x s → coord y - coord x ∈ Metric.eball (0 : E) r →
    HasSum (fun n : ℕ => p n fun _ : Fin n => coord y - coord x) (f y)

/-- A convergent power series expansion at a point of the actual function domain. -/
def HasFPowerSeriesAt {D : Type*} (f : D → F) (p : FormalMultilinearSeries 𝕜 E F)
    (x : D) (coord : D → E := by exact _root_.id) :=
  ∃ r, HasFPowerSeriesOnBall f p x r coord

/-- A convergent power series expansion within a subset of the function domain. -/
def HasFPowerSeriesWithinAt {D : Type*} (f : D → F) (p : FormalMultilinearSeries 𝕜 E F)
    (s : Set D) (x : D) (coord : D → E := by exact _root_.id) :=
  ∃ r, HasFPowerSeriesWithinOnBall f p s x r coord

-- Teach the `bound` tactic that power series have positive radius
attribute [bound_forward] HasFPowerSeriesOnBall.r_pos HasFPowerSeriesWithinOnBall.r_pos

variable (𝕜)

/-- Given a function `f : E → F`, we say that `f` is analytic at `x` if it admits a convergent power
series expansion around `x`. -/
@[fun_prop]
def AnalyticAt {D : Type*} (f : D → F) (x : D) (coord : D → E := by exact _root_.id) :=
  ∃ p : FormalMultilinearSeries 𝕜 E F, HasFPowerSeriesAt f p x coord

/-- `f` is analytic within `s` at `x` if it has a power series at `x` that converges on `𝓝[s] x` -/
def AnalyticWithinAt {D : Type*} (f : D → F) (s : Set D) (x : D)
    (coord : D → E := by exact _root_.id) : Prop :=
  ∃ p : FormalMultilinearSeries 𝕜 E F, HasFPowerSeriesWithinAt f p s x coord

/-- Given a function `f : E → F`, we say that `f` is analytic on a set `s` if it is analytic around
every point of `s`. -/
@[fun_prop]
def AnalyticOnNhd {D : Type*} (f : D → F) (s : Set D) (coord : D → E := by exact _root_.id) :=
  ∀ x, x ∈ s → AnalyticAt 𝕜 f x coord

/-- `f` is analytic within `s` if it is analytic within `s` at each point of `s`.  Note that
this is weaker than `AnalyticOnNhd 𝕜 f s`, as `f` is allowed to be arbitrary outside `s`. -/
def AnalyticOn {D : Type*} (f : D → F) (s : Set D) (coord : D → E := by exact _root_.id) : Prop :=
  ∀ x ∈ s, AnalyticWithinAt 𝕜 f s x coord

/-!
### `HasFPowerSeriesOnBall` and `HasFPowerSeriesWithinOnBall`
-/

variable {𝕜}

theorem HasFPowerSeriesOnBall.hasFPowerSeriesAt {D : Type*}
    {f : D → F} {coord : D → E} {x : D}
    (hf : HasFPowerSeriesOnBall f p x r coord) :
    HasFPowerSeriesAt f p x coord :=
  ⟨r, hf⟩

theorem HasFPowerSeriesAt.analyticAt {D : Type*}
    {f : D → F} {coord : D → E} {x : D}
    (hf : HasFPowerSeriesAt f p x coord) : AnalyticAt 𝕜 f x coord :=
  ⟨p, hf⟩

theorem HasFPowerSeriesOnBall.analyticAt {D : Type*}
    {f : D → F} {coord : D → E} {x : D}
    (hf : HasFPowerSeriesOnBall f p x r coord) : AnalyticAt 𝕜 f x coord :=
  hf.hasFPowerSeriesAt.analyticAt

theorem HasFPowerSeriesWithinOnBall.hasFPowerSeriesWithinAt {D : Type*}
    {f : D → F} {coord : D → E} {x : D} {s : Set D}
    (hf : HasFPowerSeriesWithinOnBall f p s x r coord) : HasFPowerSeriesWithinAt f p s x coord :=
  ⟨r, hf⟩

theorem HasFPowerSeriesWithinAt.analyticWithinAt {D : Type*}
    {f : D → F} {coord : D → E} {x : D} {s : Set D}
    (hf : HasFPowerSeriesWithinAt f p s x coord) :
    AnalyticWithinAt 𝕜 f s x coord := ⟨p, hf⟩

theorem HasFPowerSeriesWithinOnBall.analyticWithinAt {D : Type*}
    {f : D → F} {coord : D → E} {x : D} {s : Set D}
    (hf : HasFPowerSeriesWithinOnBall f p s x r coord) :
    AnalyticWithinAt 𝕜 f s x coord :=
  hf.hasFPowerSeriesWithinAt.analyticWithinAt

/-- Pull back a power series along a map of domains, pulling back its ambient coordinates too. -/
theorem HasFPowerSeriesOnBall.comp_domain {D D' : Type*} {f : D → F} {coord : D → E}
    {g : D' → D} {x : D'} (hf : HasFPowerSeriesOnBall f p (g x) r coord) :
    HasFPowerSeriesOnBall (f ∘ g) p x r (coord ∘ g) where
  r_le := hf.r_le
  r_pos := hf.r_pos
  hasSum hy := hf.hasSum hy

/-- Restrict a power series and its coordinates to a new domain. -/
theorem HasFPowerSeriesWithinOnBall.comp_domain {D D' : Type*} {f : D → F} {coord : D → E}
    {g : D' → D} {x : D'} {s : Set D} {t : Set D'}
    (hf : HasFPowerSeriesWithinOnBall f p s (g x) r coord) (hg : MapsTo g t s) :
    HasFPowerSeriesWithinOnBall (f ∘ g) p t x r (coord ∘ g) where
  r_le := hf.r_le
  r_pos := hf.r_pos
  hasSum hy hdist := hf.hasSum (hg.insert x hy) hdist

theorem HasFPowerSeriesAt.comp_domain {D D' : Type*} {f : D → F} {coord : D → E}
    {g : D' → D} {x : D'} (hf : HasFPowerSeriesAt f p (g x) coord) :
    HasFPowerSeriesAt (f ∘ g) p x (coord ∘ g) := by
  obtain ⟨r, hr⟩ := hf
  exact ⟨r, hr.comp_domain⟩

theorem HasFPowerSeriesWithinAt.comp_domain {D D' : Type*} {f : D → F} {coord : D → E}
    {g : D' → D} {x : D'} {s : Set D} {t : Set D'}
    (hf : HasFPowerSeriesWithinAt f p s (g x) coord) (hg : MapsTo g t s) :
    HasFPowerSeriesWithinAt (f ∘ g) p t x (coord ∘ g) := by
  obtain ⟨r, hr⟩ := hf
  exact ⟨r, hr.comp_domain hg⟩

theorem AnalyticAt.comp_domain {D D' : Type*} {f : D → F} {coord : D → E}
    {g : D' → D} {x : D'} (hf : AnalyticAt 𝕜 f (g x) coord) :
    AnalyticAt 𝕜 (f ∘ g) x (coord ∘ g) := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨p, hp.comp_domain⟩

theorem AnalyticWithinAt.comp_domain {D D' : Type*} {f : D → F} {coord : D → E}
    {g : D' → D} {x : D'} {s : Set D} {t : Set D'}
    (hf : AnalyticWithinAt 𝕜 f s (g x) coord) (hg : MapsTo g t s) :
    AnalyticWithinAt 𝕜 (f ∘ g) t x (coord ∘ g) := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨p, hp.comp_domain hg⟩

/-- A power series on a domain covering a neighbourhood gives a power series for the original
ambient function. No values of the restricted function outside its domain are introduced. -/
theorem HasFPowerSeriesAt.of_comp_domain {D : Type*} {coord : D → E} {x : D}
    (hf : HasFPowerSeriesAt (f ∘ coord) p x coord)
    (hcover : Set.range coord ∈ 𝓝 (coord x)) : HasFPowerSeriesAt f p (coord x) := by
  obtain ⟨r, hr⟩ := hf
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hcover
  let δ : ℝ≥0 := ⟨ε, hε.le⟩
  refine ⟨min r (δ : ℝ≥0∞), ⟨(min_le_left _ _).trans hr.r_le,
    lt_min hr.r_pos (ENNReal.coe_pos.mpr hε), ?_⟩⟩
  intro y hy
  have hyδ : y - coord x ∈ Metric.ball (0 : E) (δ : ℝ) := by
    rw [← Metric.eball_coe]
    exact (Metric.eball_subset_eball (min_le_right _ _)) hy
  have hyball : y ∈ Metric.ball (coord x) ε := by
    change dist (y - coord x) 0 < ε at hyδ
    simpa only [Metric.mem_ball, dist_eq_norm, sub_zero] using hyδ
  obtain ⟨z, hz⟩ := hball hyball
  have hyr : coord z - coord x ∈ Metric.eball (0 : E) r := by
    rw [hz]
    exact (Metric.eball_subset_eball (min_le_left _ _)) hy
  simpa only [Function.comp_def, id_eq, hz] using hr.hasSum hyr

/-- Analyticity of an ambient function can be checked on a domain covering a neighbourhood. -/
theorem AnalyticAt.of_comp_domain {D : Type*} {coord : D → E} {x : D}
    (hf : AnalyticAt 𝕜 (f ∘ coord) x coord)
    (hcover : Set.range coord ∈ 𝓝 (coord x)) : AnalyticAt 𝕜 f (coord x) := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨p, hp.of_comp_domain hcover⟩

/-- If a function `f` has a power series `p` around `x`, then the function `z ↦ f (z - y)` has the
same power series around `x + y`. -/
theorem HasFPowerSeriesOnBall.comp_sub (hf : HasFPowerSeriesOnBall f p x r) (y : E) :
    HasFPowerSeriesOnBall (fun z => f (z - y)) p (x + y) r :=
  { r_le := hf.r_le
    r_pos := hf.r_pos
    hasSum := fun {z} hz => by
      have hshift : (z - y) - x = z - (x + y) := by abel
      simpa only [id_eq, hshift] using
        hf.hasSum (y := z - y) (by simpa only [id_eq, hshift] using hz) }

theorem HasFPowerSeriesWithinOnBall.comp_sub (hf : HasFPowerSeriesWithinOnBall f p s x r) (y : E) :
    HasFPowerSeriesWithinOnBall (fun z ↦ f (z - y)) p (s + {y}) (x + y) r where
  r_le := hf.r_le
  r_pos := hf.r_pos
  hasSum {z} hz1 hz2 := by
    have hmem : z - y ∈ insert x s := by
      rcases mem_insert_iff.mp hz1 with hz | hz
      · apply mem_insert_iff.mpr
        left
        rw [hz]
        abel
      · apply mem_insert_of_mem
        obtain ⟨u, hu, v, hv, huv⟩ := hz
        have hv' : v = y := mem_singleton_iff.mp hv
        subst v
        have hzu : z - y = u := by rw [← huv]; simp
        simpa only [hzu] using hu
    have hshift : (z - y) - x = z - (x + y) := by abel
    simpa only [id_eq, hshift] using hf.hasSum hmem (by simpa only [id_eq, hshift] using hz2)


theorem HasFPowerSeriesAt.comp_sub (hf : HasFPowerSeriesAt f p x) (y : E) :
    HasFPowerSeriesAt (fun z ↦ f (z - y)) p (x + y) := by
  obtain ⟨r, hf⟩ := hf
  exact ⟨r, hf.comp_sub _⟩

theorem HasFPowerSeriesWithinAt.comp_sub (hf : HasFPowerSeriesWithinAt f p s x) (y : E) :
    HasFPowerSeriesWithinAt (fun z ↦ f (z - y)) p (s + {y}) (x + y) := by
  obtain ⟨r, hf⟩ := hf
  exact ⟨r, hf.comp_sub _⟩

theorem AnalyticAt.comp_sub (hf : AnalyticAt 𝕜 f x) (y : E) :
    AnalyticAt 𝕜 (fun z ↦ f (z - y)) (x + y) := by
  obtain ⟨p, hf⟩ := hf
  exact ⟨p, hf.comp_sub _⟩

theorem AnalyticOnNhd.comp_sub (hf : AnalyticOnNhd 𝕜 f s) (y : E) :
    AnalyticOnNhd 𝕜 (fun z ↦ f (z - y)) (s + {y}) := by
  intro x hx
  simp only [add_singleton, image_add_right, mem_preimage] at hx
  rw [show x = (x - y) + y by abel]
  apply (hf (x - y) (by convert hx; abel)).comp_sub

theorem AnalyticWithinAt.comp_sub (hf : AnalyticWithinAt 𝕜 f s x) (y : E) :
    AnalyticWithinAt 𝕜 (fun z ↦ f (z - y)) (s + {y}) (x + y) := by
  obtain ⟨p, hf⟩ := hf
  exact ⟨p, hf.comp_sub _⟩

theorem AnalyticOn.comp_sub (hf : AnalyticOn 𝕜 f s) (y : E) :
    AnalyticOn 𝕜 (fun z ↦ f (z - y)) (s + {y}) := by
  intro x hx
  simp only [add_singleton, image_add_right, mem_preimage] at hx
  rw [show x = (x - y) + y by abel]
  apply (hf (x - y) (by convert hx; abel)).comp_sub

theorem HasFPowerSeriesWithinOnBall.hasSum_sub (hf : HasFPowerSeriesWithinOnBall f p s x r) {y : E}
    (hy : y ∈ (insert x s) ∩ Metric.eball x r) :
    HasSum (fun n : ℕ => p n fun _ => y - x) (f y) := by
  have : y - x ∈ Metric.eball 0 r := by simpa [edist_eq_enorm_sub] using hy.2
  exact hf.hasSum hy.1 this

theorem HasFPowerSeriesOnBall.hasSum_sub (hf : HasFPowerSeriesOnBall f p x r) {y : E}
    (hy : y ∈ Metric.eball x r) : HasSum (fun n : ℕ => p n fun _ => y - x) (f y) := by
  have : y - x ∈ Metric.eball 0 r := by simpa [edist_eq_enorm_sub] using hy
  exact hf.hasSum this

theorem HasFPowerSeriesOnBall.radius_pos {D : Type*}
    {f : D → F} {coord : D → E} {x : D}
    (hf : HasFPowerSeriesOnBall f p x r coord) : 0 < p.radius :=
  lt_of_lt_of_le hf.r_pos hf.r_le

theorem HasFPowerSeriesWithinOnBall.radius_pos {D : Type*}
    {f : D → F} {coord : D → E} {x : D} {s : Set D}
    (hf : HasFPowerSeriesWithinOnBall f p s x r coord) :
    0 < p.radius :=
  lt_of_lt_of_le hf.r_pos hf.r_le

theorem HasFPowerSeriesAt.radius_pos {D : Type*}
    {f : D → F} {coord : D → E} {x : D}
    (hf : HasFPowerSeriesAt f p x coord) : 0 < p.radius :=
  let ⟨_, hr⟩ := hf
  hr.radius_pos

theorem HasFPowerSeriesWithinOnBall.of_le {D : Type*}
    {f : D → F} {coord : D → E} {x : D} {s : Set D}
    (hf : HasFPowerSeriesWithinOnBall f p s x r coord) (r'_pos : 0 < r') (hr : r' ≤ r) :
    HasFPowerSeriesWithinOnBall f p s x r' coord :=
  ⟨le_trans hr hf.1, r'_pos, fun hy h'y => hf.hasSum hy (Metric.eball_subset_eball hr h'y)⟩

theorem HasFPowerSeriesOnBall.mono {D : Type*}
    {f : D → F} {coord : D → E} {x : D}
    (hf : HasFPowerSeriesOnBall f p x r coord) (r'_pos : 0 < r')
    (hr : r' ≤ r) : HasFPowerSeriesOnBall f p x r' coord :=
  ⟨le_trans hr hf.1, r'_pos, fun hy => hf.hasSum (Metric.eball_subset_eball hr hy)⟩

lemma HasFPowerSeriesWithinOnBall.congr {f g : E → F} {p : FormalMultilinearSeries 𝕜 E F}
    {s : Set E} {x : E} {r : ℝ≥0∞} (h : HasFPowerSeriesWithinOnBall f p s x r)
    (h' : EqOn g f (s ∩ Metric.eball x r)) (h'' : g x = f x) :
    HasFPowerSeriesWithinOnBall g p s x r := by
  refine ⟨h.r_le, h.r_pos, ?_⟩
  intro y hy h'y
  convert h.hasSum hy h'y
  simp only [mem_insert_iff] at hy
  rcases hy with rfl | hy
  · simpa using h''
  · apply h'
    refine ⟨hy, ?_⟩
    simpa [edist_eq_enorm_sub] using h'y

/-- Variant of `HasFPowerSeriesWithinOnBall.congr` in which one requests equality on `insert x s`
instead of separating `x` and `s`. -/
lemma HasFPowerSeriesWithinOnBall.congr' {f g : E → F} {p : FormalMultilinearSeries 𝕜 E F}
    {s : Set E} {x : E} {r : ℝ≥0∞} (h : HasFPowerSeriesWithinOnBall f p s x r)
    (h' : EqOn g f (insert x s ∩ Metric.eball x r)) :
    HasFPowerSeriesWithinOnBall g p s x r := by
  refine ⟨h.r_le, h.r_pos, fun {y} hy h'y ↦ ?_⟩
  convert h.hasSum hy h'y
  exact h' ⟨hy, by simpa [edist_eq_enorm_sub] using h'y⟩

lemma HasFPowerSeriesWithinAt.congr {f g : E → F} {p : FormalMultilinearSeries 𝕜 E F} {s : Set E}
    {x : E} (h : HasFPowerSeriesWithinAt f p s x) (h' : g =ᶠ[𝓝[s] x] f) (h'' : g x = f x) :
    HasFPowerSeriesWithinAt g p s x := by
  rcases h with ⟨r, hr⟩
  obtain ⟨ε, εpos, hε⟩ : ∃ ε > 0, Metric.eball x ε ∩ s ⊆ {y | g y = f y} :=
    EMetric.mem_nhdsWithin_iff.1 h'
  let r' := min r ε
  refine ⟨r', ?_⟩
  have := hr.of_le (r' := r') (by simp [r', εpos, hr.r_pos]) (min_le_left _ _)
  apply this.congr _ h''
  intro z hz
  exact hε ⟨Metric.eball_subset_eball (min_le_right _ _) hz.2, hz.1⟩

theorem HasFPowerSeriesOnBall.congr (hf : HasFPowerSeriesOnBall f p x r)
    (hg : EqOn f g (Metric.eball x r)) : HasFPowerSeriesOnBall g p x r :=
  { r_le := hf.r_le
    r_pos := hf.r_pos
    hasSum := fun {y} hy => by
      convert hf.hasSum hy
      apply hg.symm
      simpa [edist_eq_enorm_sub] using hy }

theorem HasFPowerSeriesAt.congr (hf : HasFPowerSeriesAt f p x) (hg : f =ᶠ[𝓝 x] g) :
    HasFPowerSeriesAt g p x := by
  rcases hf with ⟨r₁, h₁⟩
  rcases EMetric.mem_nhds_iff.mp hg with ⟨r₂, h₂pos, h₂⟩
  exact ⟨min r₁ r₂,
    (h₁.mono (lt_min h₁.r_pos h₂pos) inf_le_left).congr
      fun y hy => h₂ (Metric.eball_subset_eball inf_le_right hy)⟩

theorem HasFPowerSeriesWithinOnBall.unique (hf : HasFPowerSeriesWithinOnBall f p s x r)
    (hg : HasFPowerSeriesWithinOnBall g p s x r) :
    (insert x s ∩ Metric.eball x r).EqOn f g := fun _ hy ↦
  (hf.hasSum_sub hy).unique (hg.hasSum_sub hy)

theorem HasFPowerSeriesOnBall.unique (hf : HasFPowerSeriesOnBall f p x r)
    (hg : HasFPowerSeriesOnBall g p x r) : (Metric.eball x r).EqOn f g := fun _ hy ↦
  (hf.hasSum_sub hy).unique (hg.hasSum_sub hy)

protected theorem HasFPowerSeriesWithinAt.eventually (hf : HasFPowerSeriesWithinAt f p s x) :
    ∀ᶠ r : ℝ≥0∞ in 𝓝[>] 0, HasFPowerSeriesWithinOnBall f p s x r :=
  let ⟨_, hr⟩ := hf
  mem_of_superset (Ioo_mem_nhdsGT hr.r_pos) fun _ hr' => hr.of_le hr'.1 hr'.2.le

protected theorem HasFPowerSeriesAt.eventually (hf : HasFPowerSeriesAt f p x) :
    ∀ᶠ r : ℝ≥0∞ in 𝓝[>] 0, HasFPowerSeriesOnBall f p x r :=
  let ⟨_, hr⟩ := hf
  mem_of_superset (Ioo_mem_nhdsGT hr.r_pos) fun _ hr' => hr.mono hr'.1 hr'.2.le

theorem HasFPowerSeriesOnBall.eventually_hasSum (hf : HasFPowerSeriesOnBall f p x r) :
    ∀ᶠ y in 𝓝 0, HasSum (fun n : ℕ => p n fun _ : Fin n => y) (f (x + y)) := by
  filter_upwards [Metric.eball_mem_nhds (0 : E) hf.r_pos] with y hy
  simpa only [id_eq, add_sub_cancel_left] using
    hf.hasSum (y := x + y) (by simpa only [id_eq, add_sub_cancel_left] using hy)

theorem HasFPowerSeriesAt.eventually_hasSum (hf : HasFPowerSeriesAt f p x) :
    ∀ᶠ y in 𝓝 0, HasSum (fun n : ℕ => p n fun _ : Fin n => y) (f (x + y)) :=
  let ⟨_, hr⟩ := hf
  hr.eventually_hasSum

theorem HasFPowerSeriesOnBall.eventually_hasSum_sub (hf : HasFPowerSeriesOnBall f p x r) :
    ∀ᶠ y in 𝓝 x, HasSum (fun n : ℕ => p n fun _ : Fin n => y - x) (f y) := by
  filter_upwards [Metric.eball_mem_nhds x hf.r_pos] with y using hf.hasSum_sub

theorem HasFPowerSeriesAt.eventually_hasSum_sub (hf : HasFPowerSeriesAt f p x) :
    ∀ᶠ y in 𝓝 x, HasSum (fun n : ℕ => p n fun _ : Fin n => y - x) (f y) :=
  let ⟨_, hr⟩ := hf
  hr.eventually_hasSum_sub

theorem HasFPowerSeriesOnBall.eventually_eq_zero
    (hf : HasFPowerSeriesOnBall f (0 : FormalMultilinearSeries 𝕜 E F) x r) :
    ∀ᶠ z in 𝓝 x, f z = 0 := by
  filter_upwards [hf.eventually_hasSum_sub] with z hz using hz.unique hasSum_zero

theorem HasFPowerSeriesAt.eventually_eq_zero
    (hf : HasFPowerSeriesAt f (0 : FormalMultilinearSeries 𝕜 E F) x) : ∀ᶠ z in 𝓝 x, f z = 0 :=
  let ⟨_, hr⟩ := hf
  hr.eventually_eq_zero

@[simp] lemma hasFPowerSeriesWithinOnBall_univ {D : Type*} {f : D → F} {coord : D → E} {x : D} :
    HasFPowerSeriesWithinOnBall f p univ x r coord ↔ HasFPowerSeriesOnBall f p x r coord := by
  constructor
  · intro h
    refine ⟨h.r_le, h.r_pos, fun {y} m ↦ h.hasSum (by simp) m⟩
  · intro h
    exact ⟨h.r_le, h.r_pos, fun {y} _ m => h.hasSum m⟩

@[simp] lemma hasFPowerSeriesWithinAt_univ {D : Type*} {f : D → F} {coord : D → E} {x : D} :
    HasFPowerSeriesWithinAt f p univ x coord ↔ HasFPowerSeriesAt f p x coord := by
  simp only [HasFPowerSeriesWithinAt, hasFPowerSeriesWithinOnBall_univ, HasFPowerSeriesAt]

lemma HasFPowerSeriesWithinOnBall.mono {D : Type*}
    {f : D → F} {coord : D → E} {x : D} {s : Set D} {t : Set D}
    (hf : HasFPowerSeriesWithinOnBall f p s x r coord) (h : t ⊆ s) :
    HasFPowerSeriesWithinOnBall f p t x r coord where
  r_le := hf.r_le
  r_pos := hf.r_pos
  hasSum hy h'y := hf.hasSum (insert_subset_insert h hy) h'y

lemma HasFPowerSeriesOnBall.hasFPowerSeriesWithinOnBall {D : Type*}
    {f : D → F} {coord : D → E} {x : D} {s : Set D}
    (hf : HasFPowerSeriesOnBall f p x r coord) :
    HasFPowerSeriesWithinOnBall f p s x r coord := by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  exact hf.mono (subset_univ _)

lemma HasFPowerSeriesWithinAt.mono {D : Type*}
    {f : D → F} {coord : D → E} {x : D} {s : Set D} {t : Set D}
    (hf : HasFPowerSeriesWithinAt f p s x coord) (h : t ⊆ s) :
    HasFPowerSeriesWithinAt f p t x coord := by
  obtain ⟨r, hp⟩ := hf
  exact ⟨r, hp.mono h⟩

lemma HasFPowerSeriesAt.hasFPowerSeriesWithinAt {D : Type*}
    {f : D → F} {coord : D → E} {x : D} {s : Set D}
    (hf : HasFPowerSeriesAt f p x coord) :
    HasFPowerSeriesWithinAt f p s x coord := by
  rw [← hasFPowerSeriesWithinAt_univ] at hf
  apply hf.mono (subset_univ _)

theorem HasFPowerSeriesWithinAt.mono_of_mem_nhdsWithin
    (h : HasFPowerSeriesWithinAt f p s x) (hst : s ∈ 𝓝[t] x) :
    HasFPowerSeriesWithinAt f p t x := by
  rcases h with ⟨r, hr⟩
  rcases EMetric.mem_nhdsWithin_iff.1 hst with ⟨r', r'_pos, hr'⟩
  refine ⟨min r r', ?_⟩
  have Z := hr.of_le (by simp [r'_pos, hr.r_pos]) (min_le_left r r')
  refine ⟨Z.r_le, Z.r_pos, fun {y} hy h'y ↦ ?_⟩
  apply Z.hasSum ?_ h'y
  simp only [mem_insert_iff] at hy
  rcases hy with rfl | hy
  · simp
  apply mem_insert_of_mem _ (hr' ?_)
  simp only [Metric.mem_eball, edist_eq_enorm_sub, sub_zero, lt_min_iff, mem_inter_iff,
    hy, and_true] at h'y ⊢
  exact h'y.2

lemma hasFPowerSeriesWithinAt_iff_of_nhds (f : E → F) (p : FormalMultilinearSeries 𝕜 E F)
    {U : Set E} (hU : U ∈ 𝓝 x) :
    HasFPowerSeriesWithinAt f p U x ↔ HasFPowerSeriesAt f p x := by
  rw [← hasFPowerSeriesWithinAt_univ]
  exact ⟨fun h ↦ h.mono_of_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds hU),
    fun h ↦ h.mono (subset_univ _)⟩

@[simp] lemma hasFPowerSeriesWithinOnBall_insert_self :
    HasFPowerSeriesWithinOnBall f p (insert x s) x r ↔ HasFPowerSeriesWithinOnBall f p s x r := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩  <;>
  exact ⟨h.r_le, h.r_pos, fun {y} ↦ by simpa only [insert_idem] using h.hasSum (y := y)⟩

@[simp] theorem hasFPowerSeriesWithinAt_insert {y : E} :
    HasFPowerSeriesWithinAt f p (insert y s) x ↔ HasFPowerSeriesWithinAt f p s x := by
  rcases eq_or_ne x y with rfl | hy
  · simp [HasFPowerSeriesWithinAt]
  · refine ⟨fun h ↦ h.mono (subset_insert _ _), fun h ↦ ?_⟩
    apply HasFPowerSeriesWithinAt.mono_of_mem_nhdsWithin h
    rw [nhdsWithin_insert_of_ne hy]
    exact self_mem_nhdsWithin

theorem HasFPowerSeriesWithinOnBall.coeff_zero {D : Type*}
    {f : D → F} {coord : D → E} {x : D} {s : Set D}
    (hf : HasFPowerSeriesWithinOnBall f pf s x r coord)
    (v : Fin 0 → E) : pf 0 v = f x := by
  have v_eq : v = fun i => 0 := Subsingleton.elim _ _
  have zero_mem : (0 : E) ∈ Metric.eball (0 : E) r := by simp [hf.r_pos]
  have : ∀ i, i ≠ 0 → (pf i fun _ => 0) = 0 := by
    intro i hi
    have : 0 < i := pos_iff_ne_zero.2 hi
    exact ContinuousMultilinearMap.map_coord_zero _ (⟨0, this⟩ : Fin i) rfl
  have hx := hf.hasSum (y := x) (by simp) (by simpa only [sub_self] using zero_mem)
  simp only [sub_self] at hx
  have A := hx.unique (hasSum_single _ this)
  simpa [v_eq] using A.symm

theorem HasFPowerSeriesOnBall.coeff_zero {D : Type*}
    {f : D → F} {coord : D → E} {x : D}
    (hf : HasFPowerSeriesOnBall f pf x r coord)
    (v : Fin 0 → E) : pf 0 v = f x := by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  exact hf.coeff_zero v

theorem HasFPowerSeriesWithinAt.coeff_zero {D : Type*}
    {f : D → F} {coord : D → E} {x : D} {s : Set D}
    (hf : HasFPowerSeriesWithinAt f pf s x coord) (v : Fin 0 → E) :
    pf 0 v = f x :=
  let ⟨_, hrf⟩ := hf
  hrf.coeff_zero v

theorem HasFPowerSeriesAt.coeff_zero {D : Type*}
    {f : D → F} {coord : D → E} {x : D}
    (hf : HasFPowerSeriesAt f pf x coord) (v : Fin 0 → E) :
    pf 0 v = f x :=
  let ⟨_, hrf⟩ := hf
  hrf.coeff_zero v

/-!
### Analytic functions
-/

@[simp] theorem analyticOn_empty : AnalyticOn 𝕜 f ∅ := by intro; simp

@[simp] theorem analyticOnNhd_empty : AnalyticOnNhd 𝕜 f ∅ := by intro; simp

@[simp] lemma analyticWithinAt_univ {D : Type*} {f : D → F} {coord : D → E} {x : D} :
    AnalyticWithinAt 𝕜 f univ x coord ↔ AnalyticAt 𝕜 f x coord := by
  simp [AnalyticWithinAt, AnalyticAt]

@[simp] lemma analyticOn_univ {f : E → F} :
    AnalyticOn 𝕜 f univ ↔ AnalyticOnNhd 𝕜 f univ := by
  simp only [AnalyticOn, analyticWithinAt_univ, AnalyticOnNhd]

lemma AnalyticWithinAt.mono {D : Type*}
    {f : D → F} {coord : D → E} {x : D} {s : Set D} {t : Set D}
    (hf : AnalyticWithinAt 𝕜 f s x coord) (h : t ⊆ s) :
    AnalyticWithinAt 𝕜 f t x coord := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨p, hp.mono h⟩

lemma AnalyticAt.analyticWithinAt {D : Type*}
    {f : D → F} {coord : D → E} {x : D} {s : Set D}
    (hf : AnalyticAt 𝕜 f x coord) : AnalyticWithinAt 𝕜 f s x coord := by
  rw [← analyticWithinAt_univ] at hf
  apply hf.mono (subset_univ _)

lemma AnalyticOnNhd.analyticOn {D : Type*}
    {f : D → F} {coord : D → E} {s : Set D}
    (hf : AnalyticOnNhd 𝕜 f s coord) : AnalyticOn 𝕜 f s coord :=
  fun x hx ↦ (hf x hx).analyticWithinAt

lemma AnalyticWithinAt.congr_of_eventuallyEq {f g : E → F} {s : Set E} {x : E}
    (hf : AnalyticWithinAt 𝕜 f s x) (hs : g =ᶠ[𝓝[s] x] f) (hx : g x = f x) :
    AnalyticWithinAt 𝕜 g s x := by
  rcases hf with ⟨p, hp⟩
  exact ⟨p, hp.congr hs hx⟩

lemma AnalyticWithinAt.congr_of_eventuallyEq_insert {f g : E → F} {s : Set E} {x : E}
    (hf : AnalyticWithinAt 𝕜 f s x) (hs : g =ᶠ[𝓝[insert x s] x] f) :
    AnalyticWithinAt 𝕜 g s x := by
  apply hf.congr_of_eventuallyEq (nhdsWithin_mono x (subset_insert x s) hs)
  apply mem_of_mem_nhdsWithin (mem_insert x s) hs

lemma AnalyticWithinAt.congr {f g : E → F} {s : Set E} {x : E}
    (hf : AnalyticWithinAt 𝕜 f s x) (hs : EqOn g f s) (hx : g x = f x) :
    AnalyticWithinAt 𝕜 g s x :=
  hf.congr_of_eventuallyEq hs.eventuallyEq_nhdsWithin hx

lemma AnalyticOn.congr {f g : E → F} {s : Set E}
    (hf : AnalyticOn 𝕜 f s) (hs : EqOn g f s) :
    AnalyticOn 𝕜 g s :=
  fun x m ↦ (hf x m).congr hs (hs m)

lemma analyticOn_congr (hs : EqOn f g s) : AnalyticOn 𝕜 f s ↔ AnalyticOn 𝕜 g s :=
  ⟨fun h ↦ h.congr hs.symm, fun h ↦ h.congr hs⟩

theorem AnalyticAt.congr (hf : AnalyticAt 𝕜 f x) (hg : f =ᶠ[𝓝 x] g) : AnalyticAt 𝕜 g x :=
  let ⟨_, hpf⟩ := hf
  (hpf.congr hg).analyticAt

theorem analyticAt_congr (h : f =ᶠ[𝓝 x] g) : AnalyticAt 𝕜 f x ↔ AnalyticAt 𝕜 g x :=
  ⟨fun hf ↦ hf.congr h, fun hg ↦ hg.congr h.symm⟩

theorem AnalyticOnNhd.mono {s t : Set E} (hf : AnalyticOnNhd 𝕜 f t) (hst : s ⊆ t) :
    AnalyticOnNhd 𝕜 f s :=
  fun z hz => hf z (hst hz)

theorem AnalyticOnNhd.congr' (hf : AnalyticOnNhd 𝕜 f s) (hg : f =ᶠ[𝓝ˢ s] g) :
    AnalyticOnNhd 𝕜 g s :=
  fun z hz => (hf z hz).congr (mem_nhdsSet_iff_forall.mp hg z hz)

theorem analyticOnNhd_congr' (h : f =ᶠ[𝓝ˢ s] g) : AnalyticOnNhd 𝕜 f s ↔ AnalyticOnNhd 𝕜 g s :=
  ⟨fun hf => hf.congr' h, fun hg => hg.congr' h.symm⟩

theorem AnalyticOnNhd.congr (hs : IsOpen s) (hf : AnalyticOnNhd 𝕜 f s) (hg : s.EqOn f g) :
    AnalyticOnNhd 𝕜 g s :=
  hf.congr' <| mem_nhdsSet_iff_forall.mpr
    (fun _ hz => eventuallyEq_iff_exists_mem.mpr ⟨s, hs.mem_nhds hz, hg⟩)

theorem analyticOnNhd_congr (hs : IsOpen s) (h : s.EqOn f g) : AnalyticOnNhd 𝕜 f s ↔
    AnalyticOnNhd 𝕜 g s := ⟨fun hf => hf.congr hs h, fun hg => hg.congr hs h.symm⟩

theorem AnalyticWithinAt.mono_of_mem_nhdsWithin
    (h : AnalyticWithinAt 𝕜 f s x) (hst : s ∈ 𝓝[t] x) : AnalyticWithinAt 𝕜 f t x := by
  rcases h with ⟨p, hp⟩
  exact ⟨p, hp.mono_of_mem_nhdsWithin hst⟩

theorem AnalyticWithinAt.congr_set (h : AnalyticWithinAt 𝕜 f s x) (hst : s =ᶠ[𝓝 x] t) :
    AnalyticWithinAt 𝕜 f t x := by
  refine h.mono_of_mem_nhdsWithin ?_
  simp [← nhdsWithin_eq_iff_eventuallyEqSet.mpr hst, self_mem_nhdsWithin]

lemma AnalyticOn.mono {f : E → F} {s t : Set E} (h : AnalyticOn 𝕜 f t)
    (hs : s ⊆ t) : AnalyticOn 𝕜 f s :=
  fun _ m ↦ (h _ (hs m)).mono hs

@[simp] theorem analyticWithinAt_insert {f : E → F} {s : Set E} {x y : E} :
    AnalyticWithinAt 𝕜 f (insert y s) x ↔ AnalyticWithinAt 𝕜 f s x := by
  simp [AnalyticWithinAt]

lemma AnalyticOn.analyticAt {f : E → F} {z : E} {s : Set E} (hU : s ∈ 𝓝 z)
    (h : AnalyticOn 𝕜 f s) : AnalyticAt 𝕜 f z := by
  obtain ⟨p, hp⟩ := h z (mem_of_mem_nhds hU)
  exact ⟨p, hasFPowerSeriesWithinAt_iff_of_nhds f p hU |>.mp hp⟩

/-!
### Composition with linear maps
-/

/-- If a function `f` has a power series `p` on a ball within a set and `g` is linear,
then `g ∘ f` has the power series `g ∘ p` on the same ball. -/
theorem ContinuousLinearMap.comp_hasFPowerSeriesWithinOnBall {D : Type*}
    {coord : D → E} {f : D → F} {s : Set D} {x : D} (g : F →L[𝕜] G)
    (h : HasFPowerSeriesWithinOnBall f p s x r coord) :
    HasFPowerSeriesWithinOnBall (g ∘ f) (g.compFormalMultilinearSeries p) s x r coord where
  r_le := h.r_le.trans (p.radius_le_radius_continuousLinearMap_comp _)
  r_pos := h.r_pos
  hasSum hy h'y := by
    simpa only [ContinuousLinearMap.compFormalMultilinearSeries_apply,
      ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply] using
      g.hasSum (h.hasSum hy h'y)

/-- If a function `f` has a power series `p` on a ball and `g` is linear, then `g ∘ f` has the
power series `g ∘ p` on the same ball. -/
theorem ContinuousLinearMap.comp_hasFPowerSeriesOnBall {D : Type*}
    {coord : D → E} {f : D → F} {x : D} (g : F →L[𝕜] G)
    (h : HasFPowerSeriesOnBall f p x r coord) :
    HasFPowerSeriesOnBall (g ∘ f) (g.compFormalMultilinearSeries p) x r coord := by
  rw [← hasFPowerSeriesWithinOnBall_univ] at h ⊢
  exact g.comp_hasFPowerSeriesWithinOnBall h

/-- If a function `f` is analytic on a set `s` and `g` is linear, then `g ∘ f` is analytic
on `s`. -/
theorem ContinuousLinearMap.comp_analyticOn (g : F →L[𝕜] G) (h : AnalyticOn 𝕜 f s) :
    AnalyticOn 𝕜 (g ∘ f) s := by
  rintro x hx
  rcases h x hx with ⟨p, r, hp⟩
  exact ⟨g.compFormalMultilinearSeries p, r, g.comp_hasFPowerSeriesWithinOnBall hp⟩

/-- If a function `f` is analytic on a set `s` and `g` is linear, then `g ∘ f` is analytic
on `s`. -/
theorem ContinuousLinearMap.comp_analyticOnNhd
    {s : Set E} (g : F →L[𝕜] G) (h : AnalyticOnNhd 𝕜 f s) :
    AnalyticOnNhd 𝕜 (g ∘ f) s := by
  rintro x hx
  rcases h x hx with ⟨p, r, hp⟩
  exact ⟨g.compFormalMultilinearSeries p, r, g.comp_hasFPowerSeriesOnBall hp⟩

/-!
### Relation between analytic function and the partial sums of its power series
-/

theorem HasFPowerSeriesWithinOnBall.tendsto_partialSum
    (hf : HasFPowerSeriesWithinOnBall f p s x r) {y : E} (hy : y ∈ Metric.eball (0 : E) r)
    (h'y : x + y ∈ insert x s) :
    Tendsto (fun n => p.partialSum n y) atTop (𝓝 (f (x + y))) := by
  have hsum := hf.hasSum (y := x + y) h'y (by simpa only [id_eq, add_sub_cancel_left] using hy)
  simpa only [id_eq, add_sub_cancel_left, FormalMultilinearSeries.partialSum]
    using hsum.tendsto_sum_nat

theorem HasFPowerSeriesOnBall.tendsto_partialSum
    (hf : HasFPowerSeriesOnBall f p x r) {y : E} (hy : y ∈ Metric.eball (0 : E) r) :
    Tendsto (fun n => p.partialSum n y) atTop (𝓝 (f (x + y))) := by
  have hsum := hf.hasSum (y := x + y) (by simpa only [id_eq, add_sub_cancel_left] using hy)
  simpa only [id_eq, add_sub_cancel_left, FormalMultilinearSeries.partialSum]
    using hsum.tendsto_sum_nat

theorem HasFPowerSeriesAt.tendsto_partialSum
    (hf : HasFPowerSeriesAt f p x) :
    ∀ᶠ y in 𝓝 0, Tendsto (fun n => p.partialSum n y) atTop (𝓝 (f (x + y))) := by
  rcases hf with ⟨r, hr⟩
  filter_upwards [Metric.eball_mem_nhds (0 : E) hr.r_pos] with y hy
  exact hr.tendsto_partialSum hy

open Finset in
/-- If a function admits a power series expansion within a ball, then the partial sums
`p.partialSum n z` converge to `f (x + y)` as `n → ∞` and `z → y`. Note that `x + z` doesn't need
to belong to the set where the power series expansion holds. -/
theorem HasFPowerSeriesWithinOnBall.tendsto_partialSum_prod {D : Type*}
    {f : D → F} {coord : D → E} {s : Set D} {x y : D}
    (hf : HasFPowerSeriesWithinOnBall f p s x r coord)
    (hy : coord y - coord x ∈ Metric.eball (0 : E) r) (h'y : y ∈ insert x s) :
    Tendsto (fun (z : ℕ × E) ↦ p.partialSum z.1 z.2)
      (atTop ×ˢ 𝓝 (coord y - coord x)) (𝓝 (f y)) := by
  let w := coord y - coord x
  change Tendsto _ (atTop ×ˢ 𝓝 w) (𝓝 (f y))
  have A : Tendsto (fun (z : ℕ × E) ↦ p.partialSum z.1 w) (atTop ×ˢ 𝓝 w) (𝓝 (f y)) := by
    exact (hf.hasSum h'y hy).tendsto_sum_nat.comp tendsto_fst
  suffices Tendsto (fun (z : ℕ × E) ↦ p.partialSum z.1 z.2 - p.partialSum z.1 w)
    (atTop ×ˢ 𝓝 w) (𝓝 0) by simpa using A.add this
  apply Metric.tendsto_nhds.2 (fun ε εpos ↦ ?_)
  obtain ⟨r', yr', r'r⟩ : ∃ (r' : ℝ≥0), ‖w‖₊ < r' ∧ r' < r := by
    simp at hy
    simpa using ENNReal.lt_iff_exists_nnreal_btwn.1 hy
  have yr'_2 : ‖w‖ < r' := by simpa [← coe_nnnorm] using yr'
  have S : Summable fun n ↦ ‖p n‖ * ↑r' ^ n := p.summable_norm_mul_pow (r'r.trans_le hf.r_le)
  obtain ⟨k, hk⟩ : ∃ k, ∑' (n : ℕ), ‖p (n + k)‖ * ↑r' ^ (n + k) < ε / 4 := by
    have : Tendsto (fun k ↦ ∑' n, ‖p (n + k)‖ * ↑r' ^ (n + k)) atTop (𝓝 0) := by
      apply _root_.tendsto_sum_nat_add (f := fun n ↦ ‖p n‖ * ↑r' ^ n)
    exact ((tendsto_order.1 this).2 _ (by linarith)).exists
  have A : ∀ᶠ (z : ℕ × E) in atTop ×ˢ 𝓝 w,
      dist (p.partialSum k z.2) (p.partialSum k w) < ε / 4 := by
    have : ContinuousAt (fun z ↦ p.partialSum k z) w := (p.partialSum_continuous k).continuousAt
    exact tendsto_snd (Metric.tendsto_nhds.1 this.tendsto (ε / 4) (by linarith))
  have B : ∀ᶠ (z : ℕ × E) in atTop ×ˢ 𝓝 w, ‖z.2‖₊ < r' := by
    suffices ∀ᶠ (z : E) in 𝓝 w, ‖z‖₊ < r' from tendsto_snd this
    have : Metric.ball 0 r' ∈ 𝓝 w := Metric.isOpen_ball.mem_nhds (by simpa using yr'_2)
    filter_upwards [this] with a ha using by simpa [← coe_nnnorm] using ha
  have C : ∀ᶠ (z : ℕ × E) in atTop ×ˢ 𝓝 w, k ≤ z.1 := tendsto_fst (Ici_mem_atTop _)
  filter_upwards [A, B, C]
  rintro ⟨n, z⟩ hz h'z hkn
  simp only [dist_eq_norm, sub_zero] at hz ⊢
  have I (w : E) (hw : ‖w‖₊ < r') : ‖∑ i ∈ Ico k n, p i (fun _ ↦ w)‖ ≤ ε / 4 := calc
    ‖∑ i ∈ Ico k n, p i (fun _ ↦ w)‖
    _ = ‖∑ i ∈ range (n - k), p (i + k) (fun _ ↦ w)‖ := by
        rw [sum_Ico_eq_sum_range]
        congr with i
        rw [add_comm k]
    _ ≤ ∑ i ∈ range (n - k), ‖p (i + k) (fun _ ↦ w)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ range (n - k), ‖p (i + k)‖ * ‖w‖ ^ (i + k) := by
        gcongr with i _hi; exact ((p (i + k)).le_opNorm _).trans_eq (by simp)
    _ ≤ ∑ i ∈ range (n - k), ‖p (i + k)‖ * ↑r' ^ (i + k) := by
        gcongr with i _hi; simpa [← coe_nnnorm] using hw.le
    _ ≤ ∑' i, ‖p (i + k)‖ * ↑r' ^ (i + k) := by
        apply Summable.sum_le_tsum _ (fun i _hi ↦ by positivity)
        apply ((_root_.summable_nat_add_iff k).2 S)
    _ ≤ ε / 4 := hk.le
  calc
  ‖p.partialSum n z - p.partialSum n w‖
  _ = ‖∑ i ∈ range n, p i (fun _ ↦ z) - ∑ i ∈ range n, p i (fun _ ↦ w)‖ := rfl
  _ = ‖(∑ i ∈ range k, p i (fun _ ↦ z) + ∑ i ∈ Ico k n, p i (fun _ ↦ z))
        - (∑ i ∈ range k, p i (fun _ ↦ w) + ∑ i ∈ Ico k n, p i (fun _ ↦ w))‖ := by
    simp [sum_range_add_sum_Ico _ hkn]
  _ = ‖(p.partialSum k z - p.partialSum k w) + (∑ i ∈ Ico k n, p i (fun _ ↦ z))
        + (- ∑ i ∈ Ico k n, p i (fun _ ↦ w))‖ := by
    congr 1
    simp only [FormalMultilinearSeries.partialSum]
    abel
  _ ≤ ‖p.partialSum k z - p.partialSum k w‖ + ‖∑ i ∈ Ico k n, p i (fun _ ↦ z)‖
      + ‖- ∑ i ∈ Ico k n, p i (fun _ ↦ w)‖ := norm_add₃_le
  _ ≤ ε / 4 + ε / 4 + ε / 4 := by
    gcongr
    · exact I _ h'z
    · simp only [norm_neg]; exact I _ yr'
  _ < ε := by linarith

/-- If a function admits a power series on a ball, then the partial sums
`p.partialSum n z` converges to `f (x + y)` as `n → ∞` and `z → y`. -/
theorem HasFPowerSeriesOnBall.tendsto_partialSum_prod {D : Type*}
    {f : D → F} {coord : D → E} {x y : D} (hf : HasFPowerSeriesOnBall f p x r coord)
    (hy : coord y - coord x ∈ Metric.eball (0 : E) r) :
    Tendsto (fun (z : ℕ × E) ↦ p.partialSum z.1 z.2)
      (atTop ×ˢ 𝓝 (coord y - coord x)) (𝓝 (f y)) :=
  (hf.hasFPowerSeriesWithinOnBall (s := univ)).tendsto_partialSum_prod hy (by simp)

/-- If a function admits a power series expansion, then it is exponentially close to the partial
sums of this power series on strict subdisks of the disk of convergence.

This version provides an upper estimate that decreases both in `‖y‖` and `n`. See also
`HasFPowerSeriesWithinOnBall.uniform_geometric_approx` for a weaker version. -/
theorem HasFPowerSeriesWithinOnBall.uniform_geometric_approx' {D : Type*}
    {f : D → F} {coord : D → E} {s : Set D} {x : D} {r' : ℝ≥0}
    (hf : HasFPowerSeriesWithinOnBall f p s x r coord) (h : (r' : ℝ≥0∞) < r) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∃ C > 0, ∀ y
      (hy : coord y - coord x ∈ Metric.ball (0 : E) r'), ∀ n, y ∈ insert x s →
        ‖f y - p.partialSum n (coord y - coord x)‖ ≤
          C * (a * Checked.div ‖coord y - coord x‖ (r' : ℝ)
            ((norm_nonneg _).trans_lt (mem_ball_zero_iff.mp hy)).ne'.isUnit) ^ n := by
  obtain ⟨a, ha, C, hC, hp⟩ : ∃ a ∈ Ioo (0 : ℝ) 1, ∃ C > 0, ∀ n, ‖p n‖ * (r' : ℝ) ^ n ≤ C * a ^ n :=
    p.norm_mul_pow_le_mul_pow_of_lt_radius (h.trans_le hf.r_le)
  have ha1 : a < 1 := ha.2
  refine ⟨a, ha, C / (1 - a), div_pos hC (sub_pos.2 ha.2), fun z hz n ys => ?_⟩
  let y := coord z - coord x
  have hy : y ∈ Metric.ball (0 : E) r' := hz
  have yr' : ‖y‖ < r' := by
    rw [ball_zero_eq] at hy
    exact hy
  have hr'0 : 0 < (r' : ℝ) := (norm_nonneg _).trans_lt yr'
  have : y ∈ Metric.eball (0 : E) r := by
    refine mem_eball_zero_iff.2 (lt_trans ?_ h)
    simpa [enorm] using! yr'
  rw [norm_sub_rev, ← mul_div_right_comm₀]
  have ya : a * (‖y‖ / ↑r') ≤ a :=
    mul_le_of_le_one_right ha.1.le (div_le_one_of_le₀ yr'.le r'.coe_nonneg)
  have hqa : a * (‖y‖ / r') < 1 := ya.trans_lt ha.2
  suffices ‖p.partialSum n y - f z‖ ≤ C * (a * (‖y‖ / r')) ^ n / (1 - a * (‖y‖ / r')) by
    refine this.trans ?_
    have : 0 < a := ha.1
    gcongr
  have hsum : HasSum (fun n ↦ p n fun _ ↦ y) (f z) := hf.hasSum ys this
  apply norm_sub_le_of_geometric_bound_of_hasSum (ya.trans_lt ha.2) _ hsum
  intro n
  calc
    ‖(p n) fun _ : Fin n => y‖
    _ ≤ ‖p n‖ * ∏ _i : Fin n, ‖y‖ := ContinuousMultilinearMap.le_opNorm _ _
    _ = ‖p n‖ * (r' : ℝ) ^ n * (‖y‖ / r') ^ n := by
      simp [field, div_pow₀]
    _ ≤ C * a ^ n * (‖y‖ / r') ^ n := by gcongr ?_ * _; apply hp
    _ ≤ C * (a * (‖y‖ / r')) ^ n := by rw [mul_pow, mul_assoc]

/-- If a function admits a power series expansion, then it is exponentially close to the partial
sums of this power series on strict subdisks of the disk of convergence.

This version provides an upper estimate that decreases both in `‖y‖` and `n`. See also
`HasFPowerSeriesOnBall.uniform_geometric_approx` for a weaker version. -/
theorem HasFPowerSeriesOnBall.uniform_geometric_approx' {r' : ℝ≥0}
    (hf : HasFPowerSeriesOnBall f p x r) (h : (r' : ℝ≥0∞) < r) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∃ C > 0, ∀ y (hy : y ∈ Metric.ball (0 : E) r'), ∀ n,
      ‖f (x + y) - p.partialSum n y‖ ≤ C * (a * Checked.div ‖y‖ (r' : ℝ)
        ((norm_nonneg _).trans_lt (mem_ball_zero_iff.mp hy)).ne'.isUnit) ^ n := by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  obtain ⟨a, ha, C, hC, hp⟩ := hf.uniform_geometric_approx' h
  refine ⟨a, ha, C, hC, ?_⟩
  intro y hy n
  simpa only [id_eq, add_sub_cancel_left] using
    hp (x + y) (by simpa only [id_eq, add_sub_cancel_left] using hy) n (by simp)

/-- If a function admits a power series expansion within a set in a ball, then it is exponentially
close to the partial sums of this power series on strict subdisks of the disk of convergence. -/
theorem HasFPowerSeriesWithinOnBall.uniform_geometric_approx {r' : ℝ≥0}
    (hf : HasFPowerSeriesWithinOnBall f p s x r) (h : (r' : ℝ≥0∞) < r) :
    ∃ a ∈ Ioo (0 : ℝ) 1,
      ∃ C > 0, ∀ y ∈ Metric.ball (0 : E) r', ∀ n, x + y ∈ insert x s →
      ‖f (x + y) - p.partialSum n y‖ ≤ C * a ^ n := by
  obtain ⟨a, ha, C, hC, hp⟩ := hf.uniform_geometric_approx' h
  refine ⟨a, ha, C, hC, fun y hy n ys => ?_⟩
  have hbound := hp (x + y) (by simpa only [id_eq, add_sub_cancel_left] using hy) n ys
  simp only [id_eq, add_sub_cancel_left] at hbound
  apply hbound.trans
  have yr' : ‖y‖ < r' := by rwa [ball_zero_eq] at hy
  have := ha.1.le -- needed to discharge a side goal on the next line
  gcongr
  exact mul_le_of_le_one_right ha.1.le (div_le_one_of_le₀ yr'.le r'.coe_nonneg)

/-- If a function admits a power series expansion, then it is exponentially close to the partial
sums of this power series on strict subdisks of the disk of convergence. -/
theorem HasFPowerSeriesOnBall.uniform_geometric_approx {r' : ℝ≥0}
    (hf : HasFPowerSeriesOnBall f p x r) (h : (r' : ℝ≥0∞) < r) :
    ∃ a ∈ Ioo (0 : ℝ) 1,
      ∃ C > 0, ∀ y ∈ Metric.ball (0 : E) r', ∀ n,
      ‖f (x + y) - p.partialSum n y‖ ≤ C * a ^ n := by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  simpa using hf.uniform_geometric_approx h

/-- Taylor formula for an analytic function within a set, `IsBigO` version. -/
theorem HasFPowerSeriesWithinAt.isBigO_sub_partialSum_pow
    (hf : HasFPowerSeriesWithinAt f p s x) (n : ℕ) :
    (fun y : E => f (x + y) - p.partialSum n y)
      =O[𝓝[(x + ·) ⁻¹' insert x s] 0] fun y => ‖y‖ ^ n := by
  rcases hf with ⟨r, hf⟩
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 hf.r_pos with ⟨r', r'0, h⟩
  replace r'0 : 0 < (r' : ℝ) := mod_cast r'0
  obtain ⟨a, -, C, -, hp⟩ : ∃ a ∈ Ioo (0 : ℝ) 1, ∃ C > 0, ∀ y ∈ Metric.ball (0 : E) r', ∀ n,
      x + y ∈ insert x s → ‖f (x + y) - p.partialSum n y‖ ≤ C * (a * (‖y‖ / r')) ^ n := by
    obtain ⟨a, ha, C, hC, hp⟩ := hf.uniform_geometric_approx' h
    refine ⟨a, ha, C, hC, ?_⟩
    intro y hy n hs
    simpa only [id_eq, add_sub_cancel_left] using
      hp (x + y) (by simpa only [id_eq, add_sub_cancel_left] using hy) n hs
  refine isBigO_iff.2 ⟨C * (a / r') ^ n, ?_⟩
  filter_upwards [inter_mem_nhdsWithin _ (Metric.ball_mem_nhds (0 : E) r'0)] with y hy
  simpa [mul_pow, mul_div_assoc₀, mul_assoc, div_mul_eq_mul_div₀, div_pow₀]
    using hp y hy.2 n (by simpa using hy.1)

/-- Taylor formula for an analytic function, `IsBigO` version. -/
theorem HasFPowerSeriesAt.isBigO_sub_partialSum_pow
    (hf : HasFPowerSeriesAt f p x) (n : ℕ) :
    (fun y : E => f (x + y) - p.partialSum n y) =O[𝓝 0] fun y => ‖y‖ ^ n := by
  rw [← hasFPowerSeriesWithinAt_univ] at hf
  simpa using hf.isBigO_sub_partialSum_pow n

/-- If `f` has formal power series `∑ n, pₙ` in a set, within a ball of radius `r`, then
for `y, z` in any smaller ball, the norm of the difference `f y - f z - p 1 (fun _ ↦ y - z)` is
bounded above by `C * (max ‖y - x‖ ‖z - x‖) * ‖y - z‖`. This lemma formulates this property
using `IsBigO` and `Filter.principal` on `E × E`. -/
theorem HasFPowerSeriesWithinOnBall.isBigO_image_sub_image_sub_deriv_principal
    (hf : HasFPowerSeriesWithinOnBall f p s x r) (hr : r' < r) :
    (fun y : E × E => f y.1 - f y.2 - p 1 fun _ => y.1 - y.2)
      =O[𝓟 (Metric.eball (x, x) r' ∩ ((insert x s) ×ˢ (insert x s)))]
      fun y => ‖y - (x, x)‖ * ‖y.1 - y.2‖ := by
  lift r' to ℝ≥0 using ne_top_of_lt hr
  rcases eq_zero_or_pos r' with (rfl | hr'0)
  · simp only [ENNReal.coe_zero, Metric.eball_zero, empty_inter, principal_empty, isBigO_bot]
  obtain ⟨a, ha, C, hC : 0 < C, hp⟩ :
      ∃ a ∈ Ioo (0 : ℝ) 1, ∃ C > 0, ∀ n : ℕ, ‖p n‖ * (r' : ℝ) ^ n ≤ C * a ^ n :=
    p.norm_mul_pow_le_mul_pow_of_lt_radius (hr.trans_le hf.r_le)
  have hrpos : (0 : ℝ) < r' := NNReal.coe_pos.mpr hr'0
  have ha1 : a < 1 := ha.2
  simp only [← le_div_iff₀ (pow_pos hrpos _)] at hp
  set L : E × E → ℝ := fun y =>
    C * (a / r') ^ 2 * (‖y - (x, x)‖ * ‖y.1 - y.2‖) * (a / (1 - a) ^ 2 + 2 / (1 - a))
  have hL : ∀ y ∈ Metric.eball (x, x) r' ∩ ((insert x s) ×ˢ (insert x s)),
      ‖f y.1 - f y.2 - p 1 fun _ => y.1 - y.2‖ ≤ L y := by
    intro y ⟨hy', ys⟩
    have hy : y ∈ Metric.eball x r ×ˢ Metric.eball x r := by
      rw [Metric.eball_prod_same]
      exact Metric.eball_subset_eball hr.le hy'
    set A : ℕ → F := fun n => (p n fun _ => y.1 - x) - p n fun _ => y.2 - x
    have hA : HasSum (fun n => A (n + 2)) (f y.1 - f y.2 - p 1 fun _ => y.1 - y.2) := by
      convert
        (hasSum_nat_add_iff' 2).2
          ((hf.hasSum_sub ⟨ys.1, hy.1⟩).sub (hf.hasSum_sub ⟨ys.2, hy.2⟩))
      rw [Finset.sum_range_succ, Finset.sum_range_one, hf.coeff_zero, hf.coeff_zero, sub_self,
        zero_add, ← Subsingleton.pi_single_eq (0 : Fin 1) (y.1 - x), Pi.single,
        ← Subsingleton.pi_single_eq (0 : Fin 1) (y.2 - x), Pi.single, ← (p 1).map_update_sub,
        ← Pi.single, Subsingleton.pi_single_eq, sub_sub_sub_cancel_right]
    rw [Metric.mem_eball, edist_eq_enorm_sub, enorm_lt_coe] at hy'
    set B : ℕ → ℝ := fun n => C * (a / r') ^ 2 * (‖y - (x, x)‖ * ‖y.1 - y.2‖) * ((n + 2) * a ^ n)
    have hAB : ∀ n, ‖A (n + 2)‖ ≤ B n := fun n =>
      calc
        ‖A (n + 2)‖ ≤ ‖p (n + 2)‖ * ↑(n + 2) * ‖y - (x, x)‖ ^ (n + 1) * ‖y.1 - y.2‖ := by
          simpa only [Fintype.card_fin, pi_norm_const, Prod.norm_def, Pi.sub_def,
            Prod.fst_sub, Prod.snd_sub, sub_sub_sub_cancel_right] using!
            (p <| n + 2).norm_image_sub_le (fun _ => y.1 - x) fun _ => y.2 - x
        _ = ‖p (n + 2)‖ * ‖y - (x, x)‖ ^ n * (↑(n + 2) * ‖y - (x, x)‖ * ‖y.1 - y.2‖) := by
          rw [pow_succ ‖y - (x, x)‖]
          ring
        _ ≤ C * a ^ (n + 2) / r' ^ (n + 2)
            * r' ^ n * (↑(n + 2) * ‖y - (x, x)‖ * ‖y.1 - y.2‖) := by
          have : 0 < a := ha.1
          gcongr
          · apply hp
          · apply hy'.le
        _ = B n := by
          simp [field, B, pow_succ]
    have hBL : HasSum B (L y) := by
      apply HasSum.mul_left
      simp only [add_mul]
      have : ‖a‖ < 1 := by simp only [Real.norm_eq_abs, abs_of_pos ha.1, ha.2]
      have hval : (↑(Units.oneSub a this) : ℝ) = 1 - a := rfl
      rw [div_eq_mul_inv₀, div_eq_mul_inv₀]
      simpa only [divp, Units.val_inv_eq_inv_val₀, Units.val_pow_eq_pow_val, hval] using
        (hasSum_coe_mul_geometric_of_norm_lt_one this).add
          ((hasSum_geometric_of_norm_lt_one this).mul_left 2)
    exact hA.norm_le_of_bounded hBL hAB
  suffices L =O[𝓟 (Metric.eball (x, x) r' ∩ ((insert x s) ×ˢ (insert x s)))]
      fun y => ‖y - (x, x)‖ * ‖y.1 - y.2‖ from
    .trans (.of_norm_eventuallyLE (eventually_principal.2 hL)) this
  simp_rw [L, mul_right_comm _ (_ * _)]
  exact (isBigO_refl _ _).const_mul_left _

/-- If `f` has formal power series `∑ n, pₙ` on a ball of radius `r`, then for `y, z` in any smaller
ball, the norm of the difference `f y - f z - p 1 (fun _ ↦ y - z)` is bounded above by
`C * (max ‖y - x‖ ‖z - x‖) * ‖y - z‖`. This lemma formulates this property using `IsBigO` and
`Filter.principal` on `E × E`. -/
theorem HasFPowerSeriesOnBall.isBigO_image_sub_image_sub_deriv_principal
    (hf : HasFPowerSeriesOnBall f p x r) (hr : r' < r) :
    (fun y : E × E => f y.1 - f y.2 - p 1 fun _ => y.1 - y.2)
      =O[𝓟 (Metric.eball (x, x) r')] fun y => ‖y - (x, x)‖ * ‖y.1 - y.2‖ := by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  simpa using hf.isBigO_image_sub_image_sub_deriv_principal hr

/-- If `f` has formal power series `∑ n, pₙ` within a set, on a ball of radius `r`, then for `y, z`
in any smaller ball, the norm of the difference `f y - f z - p 1 (fun _ ↦ y - z)` is bounded above
by `C * (max ‖y - x‖ ‖z - x‖) * ‖y - z‖`. -/
theorem HasFPowerSeriesWithinOnBall.image_sub_sub_deriv_le
    (hf : HasFPowerSeriesWithinOnBall f p s x r) (hr : r' < r) :
    ∃ C, ∀ᵉ (y ∈ insert x s ∩ Metric.eball x r') (z ∈ insert x s ∩ Metric.eball x r'),
      ‖f y - f z - p 1 fun _ => y - z‖ ≤ C * max ‖y - x‖ ‖z - x‖ * ‖y - z‖ := by
  have := hf.isBigO_image_sub_image_sub_deriv_principal hr
  simp only [isBigO_principal, mem_inter_iff, Metric.mem_eball, Prod.edist_eq, max_lt_iff, mem_prod,
    norm_mul, Real.norm_eq_abs, abs_norm, and_imp, Prod.forall, mul_assoc] at this ⊢
  rcases this with ⟨C, hC⟩
  exact ⟨C, fun y ys hy z zs hz ↦ hC y z hy hz ys zs⟩

/-- If `f` has formal power series `∑ n, pₙ` on a ball of radius `r`, then for `y, z` in any smaller
ball, the norm of the difference `f y - f z - p 1 (fun _ ↦ y - z)` is bounded above by
`C * (max ‖y - x‖ ‖z - x‖) * ‖y - z‖`. -/
theorem HasFPowerSeriesOnBall.image_sub_sub_deriv_le
    (hf : HasFPowerSeriesOnBall f p x r) (hr : r' < r) :
    ∃ C, ∀ᵉ (y ∈ Metric.eball x r') (z ∈ Metric.eball x r'),
      ‖f y - f z - p 1 fun _ => y - z‖ ≤ C * max ‖y - x‖ ‖z - x‖ * ‖y - z‖ := by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  simpa only [mem_univ, insert_eq_of_mem, univ_inter] using hf.image_sub_sub_deriv_le hr

/-- If `f` has formal power series `∑ n, pₙ` at `x` within a set `s`, then
`f y - f z - p 1 (fun _ ↦ y - z) = O(‖(y, z) - (x, x)‖ * ‖y - z‖)` as `(y, z) → (x, x)`
within `s × s`. -/
theorem HasFPowerSeriesWithinAt.isBigO_image_sub_norm_mul_norm_sub
    (hf : HasFPowerSeriesWithinAt f p s x) :
    (fun y : E × E => f y.1 - f y.2 - p 1 fun _ => y.1 - y.2)
      =O[𝓝[(insert x s) ×ˢ (insert x s)] (x, x)] fun y => ‖y - (x, x)‖ * ‖y.1 - y.2‖ := by
  rcases hf with ⟨r, hf⟩
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 hf.r_pos with ⟨r', r'0, h⟩
  refine (hf.isBigO_image_sub_image_sub_deriv_principal h).mono ?_
  rw [inter_comm]
  exact le_principal_iff.2 (inter_mem_nhdsWithin _ (Metric.eball_mem_nhds _ r'0))

/-- If `f` has formal power series `∑ n, pₙ` at `x`, then
`f y - f z - p 1 (fun _ ↦ y - z) = O(‖(y, z) - (x, x)‖ * ‖y - z‖)` as `(y, z) → (x, x)`.
In particular, `f` is strictly differentiable at `x`. -/
theorem HasFPowerSeriesAt.isBigO_image_sub_norm_mul_norm_sub (hf : HasFPowerSeriesAt f p x) :
    (fun y : E × E => f y.1 - f y.2 - p 1 fun _ => y.1 - y.2) =O[𝓝 (x, x)] fun y =>
      ‖y - (x, x)‖ * ‖y.1 - y.2‖ := by
  rw [← hasFPowerSeriesWithinAt_univ] at hf
  simpa using hf.isBigO_image_sub_norm_mul_norm_sub

/-- If a function admits a power series expansion within a set at `x`, then it is the uniform limit
of the partial sums of this power series on strict subdisks of the disk of convergence, i.e.,
`f (x + y)` is the uniform limit of `p.partialSum n y` there. -/
theorem HasFPowerSeriesWithinOnBall.tendstoUniformlyOn {r' : ℝ≥0}
    (hf : HasFPowerSeriesWithinOnBall f p s x r) (h : (r' : ℝ≥0∞) < r) :
    TendstoUniformlyOn (fun n y => p.partialSum n y) (fun y => f (x + y)) atTop
      ((x + ·) ⁻¹' (insert x s) ∩ Metric.ball (0 : E) r') := by
  obtain ⟨a, ha, C, -, hp⟩ : ∃ a ∈ Ioo (0 : ℝ) 1, ∃ C > 0, ∀ y ∈ Metric.ball (0 : E) r', ∀ n,
    x + y ∈ insert x s → ‖f (x + y) - p.partialSum n y‖ ≤ C * a ^ n := hf.uniform_geometric_approx h
  refine Metric.tendstoUniformlyOn_iff.2 fun ε εpos => ?_
  have L : Tendsto (fun n => (C : ℝ) * a ^ n) atTop (𝓝 ((C : ℝ) * 0)) :=
    tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one ha.1.le ha.2)
  rw [mul_zero] at L
  refine (L.eventually (gt_mem_nhds εpos)).mono fun n hn y hy => ?_
  rw [dist_eq_norm]
  exact (hp y hy.2 n hy.1).trans_lt hn

/-- If a function admits a power series expansion at `x`, then it is the uniform limit of the
partial sums of this power series on strict subdisks of the disk of convergence, i.e., `f (x + y)`
is the uniform limit of `p.partialSum n y` there. -/
theorem HasFPowerSeriesOnBall.tendstoUniformlyOn {r' : ℝ≥0} (hf : HasFPowerSeriesOnBall f p x r)
    (h : (r' : ℝ≥0∞) < r) :
    TendstoUniformlyOn (fun n y => p.partialSum n y) (fun y => f (x + y)) atTop
      (Metric.ball (0 : E) r') := by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  simpa using hf.tendstoUniformlyOn h

/-- If a function admits a power series expansion within a set at `x`, then it is the locally
uniform limit of the partial sums of this power series on the disk of convergence, i.e., `f (x + y)`
is the locally uniform limit of `p.partialSum n y` there. -/
theorem HasFPowerSeriesWithinOnBall.tendstoLocallyUniformlyOn
    (hf : HasFPowerSeriesWithinOnBall f p s x r) :
    TendstoLocallyUniformlyOn (fun n y => p.partialSum n y) (fun y => f (x + y)) atTop
      ((x + ·) ⁻¹' (insert x s) ∩ Metric.eball (0 : E) r) := by
  rw [tendstoLocallyUniformlyOn_iff]
  intro u hu y hy
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 hy.2 with ⟨r', yr', hr'⟩
  have : Metric.eball (0 : E) r' ∈ 𝓝 y := IsOpen.mem_nhds Metric.isOpen_eball yr'
  refine ⟨(x + ·)⁻¹' (insert x s) ∩ Metric.eball (0 : E) r', ?_, ?_⟩
  · rw [nhdsWithin_inter_of_mem']
    · exact inter_mem_nhdsWithin _ this
    · apply mem_nhdsWithin_of_mem_nhds
      apply Filter.mem_of_superset this (Metric.eball_subset_eball hr'.le)
  · simpa [Metric.eball_coe] using hf.tendstoUniformlyOn hr' u hu

/-- If a function admits a power series expansion at `x`, then it is the locally uniform limit of
the partial sums of this power series on the disk of convergence, i.e., `f (x + y)`
is the locally uniform limit of `p.partialSum n y` there. -/
theorem HasFPowerSeriesOnBall.tendstoLocallyUniformlyOn (hf : HasFPowerSeriesOnBall f p x r) :
    TendstoLocallyUniformlyOn (fun n y => p.partialSum n y) (fun y => f (x + y)) atTop
      (Metric.eball (0 : E) r) := by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  simpa using hf.tendstoLocallyUniformlyOn

/-- If a function admits a power series expansion within a set at `x`, then it is the uniform limit
of the partial sums of this power series on strict subdisks of the disk of convergence, i.e., `f y`
is the uniform limit of `p.partialSum n (y - x)` there. -/
theorem HasFPowerSeriesWithinOnBall.tendstoUniformlyOn' {D : Type*}
    {f : D → F} {coord : D → E} {s : Set D} {x : D} {r' : ℝ≥0}
    (hf : HasFPowerSeriesWithinOnBall f p s x r coord) (h : (r' : ℝ≥0∞) < r) :
    TendstoUniformlyOn (fun n y => p.partialSum n (coord y - coord x)) f atTop
      (insert x s ∩ coord ⁻¹' Metric.ball (coord x) r') := by
  obtain ⟨a, ha, C, hC, hp⟩ := hf.uniform_geometric_approx' h
  refine Metric.tendstoUniformlyOn_iff.2 fun ε εpos => ?_
  have L : Tendsto (fun n => C * a ^ n) atTop (𝓝 (C * 0)) :=
    tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one ha.1.le ha.2)
  rw [mul_zero] at L
  refine (L.eventually (gt_mem_nhds εpos)).mono fun n hn y hy => ?_
  have hy₀ : coord y - coord x ∈ Metric.ball (0 : E) r' := by
    simpa only [mem_preimage, Metric.mem_ball, dist_eq_norm, sub_zero] using hy.2
  have hnorm : ‖coord y - coord x‖ < r' := by simpa only [ball_zero_eq, mem_ofPred_eq] using hy₀
  rw [dist_eq_norm]
  apply lt_of_le_of_lt (hp y hy₀ n hy.1) ?_
  apply lt_of_le_of_lt _ hn
  have := ha.1.le
  gcongr
  exact mul_le_of_le_one_right ha.1.le (div_le_one_of_le₀ hnorm.le r'.coe_nonneg)

/-- If a function admits a power series expansion at `x`, then it is the uniform limit of the
partial sums of this power series on strict subdisks of the disk of convergence, i.e., `f y`
is the uniform limit of `p.partialSum n (y - x)` there. -/
theorem HasFPowerSeriesOnBall.tendstoUniformlyOn' {D : Type*}
    {f : D → F} {coord : D → E} {x : D} {r' : ℝ≥0}
    (hf : HasFPowerSeriesOnBall f p x r coord) (h : (r' : ℝ≥0∞) < r) :
    TendstoUniformlyOn (fun n y => p.partialSum n (coord y - coord x)) f atTop
      (coord ⁻¹' Metric.ball (coord x) r') := by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  simpa using hf.tendstoUniformlyOn' h

/-- If a function admits a power series expansion within a set at `x`, then it is the locally
uniform limit of the partial sums of this power series on the disk of convergence, i.e., `f y`
is the locally uniform limit of `p.partialSum n (y - x)` there. -/
theorem HasFPowerSeriesWithinOnBall.tendstoLocallyUniformlyOn' {D : Type*} [TopologicalSpace D]
    {f : D → F} {coord : D → E} {s : Set D} {x : D}
    (hf : HasFPowerSeriesWithinOnBall f p s x r coord)
    (hcoord : Continuous coord := by exact continuous_id) :
    TendstoLocallyUniformlyOn (fun n y => p.partialSum n (coord y - coord x)) f atTop
      (insert x s ∩ coord ⁻¹' Metric.eball (coord x) r) := by
  rw [tendstoLocallyUniformlyOn_iff]
  intro u hu y hy
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 hy.2 with ⟨r', yr', hr'⟩
  have hnbhd : coord ⁻¹' Metric.eball (coord x) r' ∈ 𝓝 y :=
    hcoord.continuousAt.eventually (Metric.isOpen_eball.mem_nhds yr')
  refine ⟨insert x s ∩ coord ⁻¹' Metric.eball (coord x) r', ?_, ?_⟩
  · rw [nhdsWithin_inter_of_mem']
    · exact inter_mem_nhdsWithin _ hnbhd
    · exact mem_nhdsWithin_of_mem_nhds <|
        mem_of_superset hnbhd (preimage_mono (Metric.eball_subset_eball hr'.le))
  · simpa only [Metric.eball_coe] using hf.tendstoUniformlyOn' hr' u hu

/-- If a function admits a power series expansion at `x`, then it is the locally uniform limit of
the partial sums of this power series on the disk of convergence, i.e., `f y`
is the locally uniform limit of `p.partialSum n (y - x)` there. -/
theorem HasFPowerSeriesOnBall.tendstoLocallyUniformlyOn' {D : Type*} [TopologicalSpace D]
    {f : D → F} {coord : D → E} {x : D} (hf : HasFPowerSeriesOnBall f p x r coord)
    (hcoord : Continuous coord := by exact continuous_id) :
    TendstoLocallyUniformlyOn (fun n y => p.partialSum n (coord y - coord x)) f atTop
      (coord ⁻¹' Metric.eball (coord x) r) := by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  simpa using hf.tendstoLocallyUniformlyOn' hcoord

/-- If a function admits a power series expansion within a set on a ball, then it is
continuous there. -/
protected theorem HasFPowerSeriesWithinOnBall.continuousOn {D : Type*} [TopologicalSpace D]
    {f : D → F} {coord : D → E} {s : Set D} {x : D}
    (hf : HasFPowerSeriesWithinOnBall f p s x r coord)
    (hcoord : Continuous coord := by exact continuous_id) :
    ContinuousOn f (insert x s ∩ coord ⁻¹' Metric.eball (coord x) r) :=
  (hf.tendstoLocallyUniformlyOn' hcoord).continuousOn <|
    Frequently.of_forall fun n =>
      ((p.partialSum_continuous n).comp (hcoord.sub continuous_const)).continuousOn

/-- Convergence on a coordinate ball implies continuity when the coordinates are continuous. -/
protected theorem HasFPowerSeriesOnBall.continuousOn {D : Type*} [TopologicalSpace D]
    {f : D → F} {coord : D → E} {x : D} (hf : HasFPowerSeriesOnBall f p x r coord)
    (hcoord : Continuous coord := by exact continuous_id) :
    ContinuousOn f (coord ⁻¹' Metric.eball (coord x) r) := by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf
  simpa using hf.continuousOn hcoord

protected theorem HasFPowerSeriesWithinOnBall.continuousWithinAt_insert {D : Type*}
    [TopologicalSpace D] {f : D → F} {coord : D → E} {s : Set D} {x : D}
    (hf : HasFPowerSeriesWithinOnBall f p s x r coord)
    (hcoord : Continuous coord := by exact continuous_id) :
    ContinuousWithinAt f (insert x s) x := by
  apply ((hf.continuousOn hcoord).continuousWithinAt (x := x)
    (by simp [hf.r_pos])).mono_of_mem_nhdsWithin
  exact inter_mem_nhdsWithin _ (hcoord.continuousAt.eventually (Metric.eball_mem_nhds _ hf.r_pos))

protected theorem HasFPowerSeriesWithinOnBall.continuousWithinAt {D : Type*} [TopologicalSpace D]
    {f : D → F} {coord : D → E} {s : Set D} {x : D}
    (hf : HasFPowerSeriesWithinOnBall f p s x r coord)
    (hcoord : Continuous coord := by exact continuous_id) : ContinuousWithinAt f s x :=
  (hf.continuousWithinAt_insert hcoord).mono (subset_insert x s)

protected theorem HasFPowerSeriesWithinAt.continuousWithinAt_insert {D : Type*} [TopologicalSpace D]
    {f : D → F} {coord : D → E} {s : Set D} {x : D}
    (hf : HasFPowerSeriesWithinAt f p s x coord)
    (hcoord : Continuous coord := by exact continuous_id) :
    ContinuousWithinAt f (insert x s) x := by
  rcases hf with ⟨r, hr⟩
  exact hr.continuousWithinAt_insert hcoord

protected theorem HasFPowerSeriesWithinAt.continuousWithinAt {D : Type*} [TopologicalSpace D]
    {f : D → F} {coord : D → E} {s : Set D} {x : D}
    (hf : HasFPowerSeriesWithinAt f p s x coord)
    (hcoord : Continuous coord := by exact continuous_id) : ContinuousWithinAt f s x :=
  (hf.continuousWithinAt_insert hcoord).mono (subset_insert x s)

protected theorem HasFPowerSeriesAt.continuousAt {D : Type*} [TopologicalSpace D]
    {f : D → F} {coord : D → E} {x : D} (hf : HasFPowerSeriesAt f p x coord)
    (hcoord : Continuous coord := by exact continuous_id) : ContinuousAt f x := by
  obtain ⟨r, hr⟩ := hf
  exact (hr.continuousOn hcoord).continuousAt
    (hcoord.continuousAt.eventually (Metric.eball_mem_nhds _ hr.r_pos))

protected theorem AnalyticWithinAt.continuousWithinAt_insert {D : Type*} [TopologicalSpace D]
    {f : D → F} {coord : D → E} {s : Set D} {x : D}
    (hf : AnalyticWithinAt 𝕜 f s x coord)
    (hcoord : Continuous coord := by exact continuous_id) : ContinuousWithinAt f (insert x s) x :=
  let ⟨_, hp⟩ := hf
  hp.continuousWithinAt_insert hcoord

protected theorem AnalyticWithinAt.continuousWithinAt {D : Type*} [TopologicalSpace D]
    {f : D → F} {coord : D → E} {s : Set D} {x : D}
    (hf : AnalyticWithinAt 𝕜 f s x coord)
    (hcoord : Continuous coord := by exact continuous_id) : ContinuousWithinAt f s x :=
  (hf.continuousWithinAt_insert hcoord).mono (subset_insert x s)

@[fun_prop]
protected theorem AnalyticAt.continuousAt {D : Type*} [TopologicalSpace D]
    {f : D → F} {coord : D → E} {x : D} (hf : AnalyticAt 𝕜 f x coord)
    (hcoord : Continuous coord := by exact continuous_id) : ContinuousAt f x :=
  let ⟨_, hp⟩ := hf
  hp.continuousAt hcoord

protected theorem AnalyticAt.eventually_continuousAt (hf : AnalyticAt 𝕜 f x) :
    ∀ᶠ y in 𝓝 x, ContinuousAt f y := by
  rcases hf with ⟨g, r, hg⟩
  have : Metric.eball x r ∈ 𝓝 x := Metric.eball_mem_nhds _ hg.r_pos
  filter_upwards [this] with y hy
  apply hg.continuousOn.continuousAt
  exact Metric.isOpen_eball.mem_nhds hy

protected theorem AnalyticOnNhd.continuousOn {s : Set E} (hf : AnalyticOnNhd 𝕜 f s) :
    ContinuousOn f s :=
  fun x hx => (hf x hx).continuousAt.continuousWithinAt

protected lemma AnalyticOn.continuousOn {f : E → F} {s : Set E} (h : AnalyticOn 𝕜 f s) :
    ContinuousOn f s :=
  fun x m ↦ (h x m).continuousWithinAt

/-- Analytic everywhere implies continuous -/
theorem AnalyticOnNhd.continuous {f : E → F} (fa : AnalyticOnNhd 𝕜 f univ) : Continuous f := by
  rw [← continuousOn_univ]; exact fa.continuousOn

/-- In a complete space, the sum of a converging power series `p` admits `p` as a power series.
This is not totally obvious as we need to check the convergence of the series. -/
protected theorem FormalMultilinearSeries.hasFPowerSeriesOnBall [CompleteSpace F]
    (p : FormalMultilinearSeries 𝕜 E F) (h : 0 < p.radius) :
    HasFPowerSeriesOnBall p.sum p 0 p.radius :=
  { r_le := le_rfl
    r_pos := h
    hasSum := fun {y} hy => by
      simpa only [id_eq, sub_zero] using p.hasSum (by simpa only [id_eq, sub_zero] using hy) }

theorem HasFPowerSeriesWithinOnBall.sum (h : HasFPowerSeriesWithinOnBall f p s x r) {y : E}
    (h'y : x + y ∈ insert x s) (hy : y ∈ Metric.eball (0 : E) r) : f (x + y) = p.sum y := by
  simpa only [id_eq, add_sub_cancel_left, FormalMultilinearSeries.sum] using
    (h.hasSum (y := x + y) h'y (by simpa only [id_eq, add_sub_cancel_left] using hy)).tsum_eq.symm

theorem HasFPowerSeriesOnBall.sum (h : HasFPowerSeriesOnBall f p x r) {y : E}
    (hy : y ∈ Metric.eball (0 : E) r) : f (x + y) = p.sum y := by
  simpa only [id_eq, add_sub_cancel_left, FormalMultilinearSeries.sum] using
    (h.hasSum (y := x + y) (by simpa only [id_eq, add_sub_cancel_left] using hy)).tsum_eq.symm

/-- The sum of a converging power series is continuous in its disk of convergence. -/
protected theorem FormalMultilinearSeries.continuousOn [CompleteSpace F] :
    ContinuousOn p.sum (Metric.eball 0 p.radius) := by
  rcases eq_zero_or_pos p.radius with h | h
  · simp [h, continuousOn_empty]
  · exact (p.hasFPowerSeriesOnBall h).continuousOn

end

section

open FormalMultilinearSeries

variable {p : FormalMultilinearSeries 𝕜 𝕜 E} {f : 𝕜 → E} {z₀ : 𝕜}

/-- A function `f : 𝕜 → E` has `p` as power series expansion at a point `z₀` iff it is the sum of
`p` in a neighborhood of `z₀`. This makes some proofs easier by hiding the fact that
`HasFPowerSeriesAt` depends on `p.radius`. -/
theorem hasFPowerSeriesAt_iff :
    HasFPowerSeriesAt f p z₀ ↔ ∀ᶠ z in 𝓝 0, HasSum (fun n => z ^ n • p.coeff n) (f (z₀ + z)) := by
  refine ⟨fun hf => ?_, ?_⟩
  · exact hf.eventually_hasSum.mono fun z hz => by
      simpa only [apply_eq_pow_smul_coeff] using hz
  simp only [Metric.eventually_nhds_iff]
  rintro ⟨r, r_pos, h⟩
  refine ⟨p.radius ⊓ r.toNNReal, by simp, ?_, ?_⟩
  · simp only [r_pos.lt, lt_inf_iff, ENNReal.coe_pos, Real.toNNReal_pos, and_true]
    obtain ⟨z, z_pos, le_z⟩ := NormedField.exists_norm_lt 𝕜 r_pos.lt
    have : (‖z‖₊ : ENNReal) ≤ p.radius := by
      simp only [dist_zero_right] at h
      apply FormalMultilinearSeries.le_radius_of_tendsto
      convert! tendsto_norm.comp (h le_z).summable.tendsto_atTop_zero
      simp [norm_smul, mul_comm]
    refine lt_of_lt_of_le ?_ this
    simp only [ENNReal.coe_pos]
    exact zero_lt_iff.mpr (nnnorm_ne_zero_iff.mpr (norm_pos_iff.mp z_pos))
  · intro y hy
    simp only [id_eq, Metric.mem_eball, lt_inf_iff, edist_lt_coe] at hy
    have hyr : dist (y - z₀) 0 < r := by
      simpa only [coe_nndist, Real.coe_toNNReal _ r_pos.le] using
        (NNReal.coe_lt_coe.mpr hy.2)
    have htranslate : z₀ + (y - z₀) = y := by abel
    simpa only [id_eq, apply_eq_pow_smul_coeff, htranslate] using h hyr

theorem hasFPowerSeriesAt_iff' :
    HasFPowerSeriesAt f p z₀ ↔ ∀ᶠ z in 𝓝 z₀, HasSum (fun n => (z - z₀) ^ n • p.coeff n) (f z) := by
  rw [← map_add_left_nhds_zero, eventually_map, hasFPowerSeriesAt_iff]
  simp_rw [add_sub_cancel_left]

end
