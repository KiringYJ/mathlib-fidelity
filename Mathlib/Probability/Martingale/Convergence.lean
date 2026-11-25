/-
Copyright (c) 2022 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Function.UniformIntegrable
public import Mathlib.Probability.Martingale.Upcrossing

/-!

# Martingale convergence theorems

The martingale convergence theorems are a collection of theorems characterizing the convergence
of a martingale provided it satisfies some boundedness conditions. This file contains the
almost everywhere martingale convergence theorem which provides an almost everywhere limit to
an L¹ bounded submartingale. It also contains the L¹ martingale convergence theorem which provides
an L¹ limit to a uniformly integrable submartingale. Finally, it also contains the Lévy upwards
theorems.

A conditional expectation is determined only up to almost everywhere equality, so the statements
about conditional expectations take arbitrary versions: functions `G n` with
`IsCondExp (ℱ n) μ g (G n)`.

## Main results

* `MeasureTheory.Submartingale.ae_tendsto_limitProcess`: the almost everywhere martingale
  convergence theorem: an L¹-bounded submartingale strongly adapted to the filtration `ℱ`
  converges almost everywhere to its limit process.
* `MeasureTheory.Submartingale.memLp_limitProcess`: the limit process of an Lᵖ-bounded
  submartingale is Lᵖ.
* `MeasureTheory.Submartingale.tendsto_eLpNorm_one_limitProcess`: part a of the L¹ martingale
  convergence theorem: a uniformly integrable submartingale strongly adapted to the filtration `ℱ`
  converges almost everywhere and in L¹ to an integrable function which is measurable with respect
  to the σ-algebra `⨆ n, ℱ n`.
* `MeasureTheory.Martingale.isCondExp_of_tendsto_eLpNorm`: if a martingale `f` converges in L¹ to
  `g`, then every `f n` is a conditional expectation of `g` given `ℱ n`, for any measure.
* `MeasureTheory.Martingale.isCondExp_limitProcess`: part b of the L¹ martingale convergence
  theorem: if `f` is a uniformly integrable martingale strongly adapted to the filtration `ℱ`, then
  every `f n` is a conditional expectation given `ℱ n` of the limiting process of `f`.
* `MeasureTheory.Integrable.tendsto_ae_condExp`: part c of the L¹ martingale convergence theorem:
  given an integrable, almost everywhere `⨆ n, ℱ n`-measurable function `g` where `ℱ` is a
  filtration, conditional expectations of `g` given `ℱ n` converge almost everywhere to `g`.
* `MeasureTheory.Integrable.tendsto_eLpNorm_condExp`: part c of the L¹ martingale convergence
  theorem: under the same hypotheses, they converge to `g` in L¹.
* `MeasureTheory.tendsto_ae_condExp` and `MeasureTheory.tendsto_eLpNorm_condExp`: **Lévy's upward
  theorem**: given an integrable function `g`, conditional expectations of `g` given `ℱ n`
  converge almost everywhere and in L¹ to a conditional expectation of `g` given `⨆ n, ℱ n`.

-/

public section


open TopologicalSpace Filter MeasureTheory.Filtration

open scoped NNReal ENNReal MeasureTheory ProbabilityTheory Topology

namespace MeasureTheory

variable {Ω : Type*} {m0 : SigmaAlgebra Ω} {μ : Measure Ω} {ℱ : Filtration ℕ m0}
variable {a b : ℝ} {f : ℕ → Ω → ℝ} {ω : Ω} {R : ℝ≥0}

section AeConvergence

/-!

### Almost everywhere martingale convergence theorem

We will now prove the almost everywhere martingale convergence theorem.

The a.e. martingale convergence theorem states: if `f` is an L¹-bounded `ℱ`-submartingale, then
it converges almost everywhere to an integrable function which is measurable with respect to
the σ-algebra `ℱ∞ := ⨆ n, ℱ n`.

Mathematically, we proceed by first noting that a real sequence $(x_n)$ converges if
(a) $\limsup_{n \to \infty} |x_n| < \infty$, (b) for all $a < b \in \mathbb{Q}$ we have the
number of upcrossings of $(x_n)$ from below $a$ to above $b$ is finite.
Thus, for all $\omega$ satisfying $\limsup_{n \to \infty} |f_n(\omega)| < \infty$ and the number of
upcrossings of $(f_n(\omega))$ from below $a$ to above $b$ is finite for all $a < b \in \mathbb{Q}$,
we have $(f_n(\omega))$ is convergent.

Hence, assuming $(f_n)$ is L¹-bounded, using Fatou's lemma, we have
$$
  \mathbb{E} \limsup_{n \to \infty} |f_n| \le \limsup_{n \to \infty} \mathbb{E}|f_n| < \infty
$$
implying $\limsup_{n \to \infty} |f_n| < \infty$ a.e. Furthermore, by the upcrossing estimate,
the number of upcrossings is finite almost everywhere implying $f$ converges pointwise almost
everywhere.

Thus, denoting $g$ the a.e. limit of $(f_n)$, $g$ is $\mathcal{F}_\infty$-measurable as for all
$n$, $f_n$ is $\mathcal{F}_n$-measurable and $\mathcal{F}_n \le \mathcal{F}_\infty$. Finally, $g$
is integrable as $|g| \le \liminf_{n \to \infty} |f_n|$ so
$$
  \mathbb{E}|g| \le \mathbb{E} \limsup_{n \to \infty} |f_n| \le
    \limsup_{n \to \infty} \mathbb{E}|f_n| < \infty
$$
as required.

In terms of implementation, we have `tendsto_of_no_upcrossings` which shows that
a bounded sequence converges if it does not visit below $a$ and above $b$ infinitely often
for all $a, b ∈ s$ for some dense set $s$. So, we may skip the first step provided we can prove
that the realizations are bounded almost everywhere. Indeed, suppose $|f_n(\omega)|$ is not
bounded, then either $f_n(\omega) \to \pm \infty$ or one of $\limsup f_n(\omega)$ or
$\liminf f_n(\omega)$ equals $\pm \infty$ while the other is finite. But the first case
contradicts $\liminf |f_n(\omega)| < \infty$ while the second case contradicts finite upcrossings.

Furthermore, we introduce `Filtration.limitProcess` which chooses the limiting random variable
of a stochastic process if it exists, otherwise returning 0. Hence, instead of showing an
existence statement, we phrase the a.e. martingale convergence theorem by showing that a
submartingale converges to its `limitProcess` almost everywhere.

-/


/-- If a stochastic process has a finite number of upcrossings from below `a` to above `b`,
then it does not frequently visit both below `a` and above `b`. -/
theorem not_frequently_of_upcrossings_lt_top (hab : a < b) (hω : upcrossings a b f ω ≠ ∞) :
    ¬((∃ᶠ n in atTop, f n ω < a) ∧ ∃ᶠ n in atTop, b < f n ω) := by
  rw [← lt_top_iff_ne_top, upcrossings_lt_top_iff] at hω
  replace hω : ∃ k, ∀ N, upcrossingsBefore a b f N ω < k := by
    obtain ⟨k, hk⟩ := hω
    exact ⟨k + 1, fun N => lt_of_le_of_lt (hk N) k.lt_succ_self⟩
  rintro ⟨h₁, h₂⟩
  rw [frequently_atTop] at h₁ h₂
  refine Classical.not_not.2 hω ?_
  push Not
  intro k
  induction k with
  | zero => simp only [zero_le, exists_const]
  | succ k ih =>
    obtain ⟨N, hN⟩ := ih
    obtain ⟨N₁, hN₁, hN₁'⟩ := h₁ N
    obtain ⟨N₂, hN₂, hN₂'⟩ := h₂ N₁
    exact ⟨N₂ + 1, Nat.succ_le_of_lt <|
      lt_of_le_of_lt hN (upcrossingsBefore_lt_of_exists_upcrossing hab hN₁ hN₁' hN₂ hN₂')⟩

/-- A stochastic process that frequently visits below `a` and above `b` has infinite upcrossings. -/
theorem upcrossings_eq_top_of_frequently_lt (hab : a < b) (h₁ : ∃ᶠ n in atTop, f n ω < a)
    (h₂ : ∃ᶠ n in atTop, b < f n ω) : upcrossings a b f ω = ∞ :=
  by_contradiction fun h => not_frequently_of_upcrossings_lt_top hab h ⟨h₁, h₂⟩

/-- A realization of a stochastic process with bounded upcrossings and bounded limit inferiors is
convergent.

We use the spelling `< ∞` instead of the standard `≠ ∞` in the assumptions since it is not as easy
to change `<` to `≠` under binders. -/
theorem tendsto_of_uncrossing_lt_top (hf₁ : liminf (fun n => (‖f n ω‖₊ : ℝ≥0∞)) atTop < ∞)
    (hf₂ : ∀ a b : ℚ, a < b → upcrossings a b f ω < ∞) :
    ∃ c, Tendsto (fun n => f n ω) atTop (𝓝 c) := by
  by_cases h : IsBoundedUnder (· ≤ ·) atTop fun n => |f n ω|
  · rw [isBoundedUnder_le_abs] at h
    refine tendsto_of_no_upcrossings Rat.denseRange_cast ?_ h.1 h.2
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hab
    exact not_frequently_of_upcrossings_lt_top hab (hf₂ a b (Rat.cast_lt.1 hab)).ne
  · obtain ⟨a, b, hab, h₁, h₂⟩ := ENNReal.exists_upcrossings_of_not_bounded_under hf₁.ne h
    exact
      False.elim ((hf₂ a b hab).ne (upcrossings_eq_top_of_frequently_lt (Rat.cast_lt.2 hab) h₁ h₂))

/-- An L¹-bounded submartingale has bounded upcrossings almost everywhere. -/
theorem Submartingale.upcrossings_ae_lt_top' [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ)
    (hbdd : ∀ n, eLpNorm (f n) 1 μ ≤ R) (hab : a < b) : ∀ᵐ ω ∂μ, upcrossings a b f ω < ∞ := by
  refine ae_lt_top (hf.stronglyAdapted.measurable_upcrossings hab) ?_
  have h₀ : ENNReal.ofReal (b - a) ≠ 0 := (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)).ne'
  have := hf.mul_lintegral_upcrossings_le_lintegral_pos_part a b
  rw [mul_comm, ← ENNReal.le_div_iff_mul_le ⟨h₀, Or.inr ENNReal.ofReal_ne_top⟩] at this
  · refine (lt_of_le_of_lt this (ENNReal.div_lt_top ?_ h₀)).ne
    · have hR' : ∀ n, ∫⁻ ω, ‖f n ω - a‖₊ ∂μ ≤ R + ‖a‖₊ * μ Set.univ := by
        simp_rw [eLpNorm_one_eq_lintegral_enorm] at hbdd
        intro n
        refine (lintegral_mono ?_ : ∫⁻ ω, ‖f n ω - a‖₊ ∂μ ≤ ∫⁻ ω, ‖f n ω‖₊ + ‖a‖₊ ∂μ).trans ?_
        · intro ω
          simp_rw [sub_eq_add_neg, ← nnnorm_neg a, ← ENNReal.coe_add, ENNReal.coe_le_coe]
          exact nnnorm_add_le _ _
        · simp_rw [lintegral_add_right _ measurable_const, lintegral_const]
          exact add_le_add (hbdd _) le_rfl
      refine ne_of_lt (iSup_lt_iff.2 ⟨R + ‖a‖₊ * μ Set.univ, ENNReal.add_lt_top.2
        ⟨ENNReal.coe_lt_top, by finiteness⟩,
        fun n => le_trans ?_ (hR' n)⟩)
      refine lintegral_mono fun ω => ?_
      rw [ENNReal.ofReal_le_iff_le_toReal, ENNReal.coe_toReal, coe_nnnorm]
      · by_cases! hnonneg : 0 ≤ f n ω - a
        · rw [posPart_eq_self.2 hnonneg, Real.norm_eq_abs, abs_of_nonneg hnonneg]
        · rw [posPart_eq_zero.2 hnonneg.le]
          exact norm_nonneg _
      · finiteness

theorem Submartingale.upcrossings_ae_lt_top [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ)
    (hbdd : ∀ n, eLpNorm (f n) 1 μ ≤ R) : ∀ᵐ ω ∂μ, ∀ a b : ℚ, a < b → upcrossings a b f ω < ∞ := by
  simp only [ae_all_iff, eventually_imp_distrib_left]
  rintro a b hab
  exact hf.upcrossings_ae_lt_top' hbdd (Rat.cast_lt.2 hab)

/-- An L¹-bounded submartingale converges almost everywhere. -/
theorem Submartingale.exists_ae_tendsto_of_bdd [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ)
    (hbdd : ∀ n, eLpNorm (f n) 1 μ ≤ R) : ∀ᵐ ω ∂μ, ∃ c, Tendsto (fun n => f n ω) atTop (𝓝 c) := by
  filter_upwards [hf.upcrossings_ae_lt_top hbdd, ae_bdd_liminf_atTop_of_eLpNorm_bdd one_ne_zero
    (fun n => (hf.stronglyMeasurable n).measurable.mono (ℱ.le n) le_rfl) hbdd] with ω h₁ h₂
  exact tendsto_of_uncrossing_lt_top h₂ h₁

theorem Submartingale.exists_ae_trim_tendsto_of_bdd [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ)
    (hbdd : ∀ n, eLpNorm (f n) 1 μ ≤ R) :
    ∀ᵐ ω ∂μ.trim (sSup_le fun _ ⟨_, hn⟩ => hn ▸ ℱ.le _ : ⨆ n, ℱ n ≤ m0),
      ∃ c, Tendsto (fun n => f n ω) atTop (𝓝 c) := by
  let := (⨆ n, ℱ n)
  rw [ae_iff, trim_measurableSet_eq]
  · exact hf.exists_ae_tendsto_of_bdd hbdd
  · exact MeasurableSet.compl <| measurableSet_exists_tendsto
      fun n => (hf.stronglyMeasurable n).measurable.mono (le_sSup ⟨n, rfl⟩) le_rfl

/-- **Almost everywhere martingale convergence theorem**: An L¹-bounded submartingale converges
almost everywhere to a `⨆ n, ℱ n`-measurable function. -/
theorem Submartingale.ae_tendsto_limitProcess [IsFiniteMeasure μ] (hf : Submartingale f ℱ μ)
    (hbdd : ∀ n, eLpNorm (f n) 1 μ ≤ R) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (ℱ.limitProcess f μ ω)) := by
  classical
  suffices
      ∃ g, StronglyMeasurable[⨆ n, ℱ n] g ∧ ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (g ω)) by
    rw [limitProcess, dite_eq_left this]
    exact (Classical.choose_spec this).2
  set g' : Ω → ℝ := fun ω => if h : ∃ c, Tendsto (fun n => f n ω) atTop (𝓝 c) then h.choose else 0
  have hle : ⨆ n, ℱ n ≤ m0 := sSup_le fun m ⟨n, hn⟩ => hn ▸ ℱ.le _
  have hg' : ∀ᵐ ω ∂μ.trim hle, Tendsto (fun n => f n ω) atTop (𝓝 (g' ω)) := by
    filter_upwards [hf.exists_ae_trim_tendsto_of_bdd hbdd] with ω hω
    simp_rw [g', dite_eq_left hω]
    exact hω.choose_spec
  have hg'm : AEStronglyMeasurable[⨆ n, ℱ n] g' (μ.trim hle) :=
    (@aemeasurable_of_tendsto_metrizable_ae' _ _ (⨆ n, ℱ n) _ _ _ _ _ _ _
      (fun n => ((hf.stronglyMeasurable n).measurable.mono (le_sSup ⟨n, rfl⟩ : ℱ n ≤ ⨆ n, ℱ n)
        le_rfl).aemeasurable) hg').aestronglyMeasurable
  obtain ⟨g, hgm, hae⟩ := hg'm
  have hg : ∀ᵐ ω ∂μ.trim hle, Tendsto (fun n => f n ω) atTop (𝓝 (g ω)) := by
    filter_upwards [hae, hg'] with ω hω hg'ω
    exact hω ▸ hg'ω
  exact ⟨g, hgm, measure_eq_zero_of_trim_eq_zero hle hg⟩

/-- The limiting process of an Lᵖ-bounded submartingale is Lᵖ. -/
theorem Submartingale.memLp_limitProcess {p : ℝ≥0∞} (hf : Submartingale f ℱ μ)
    (hbdd : ∀ n, eLpNorm (f n) p μ ≤ R) : MemLp (ℱ.limitProcess f μ) p μ :=
  memLp_limitProcess_of_eLpNorm_bdd
    (fun n => ((hf.stronglyMeasurable n).mono (ℱ.le n)).aestronglyMeasurable) hbdd

end AeConvergence

section L1Convergence

variable {g : Ω → ℝ}

/-!

### L¹ martingale convergence theorem

We will now prove the L¹ martingale convergence theorems.

The L¹ martingale convergence theorem states that:
(a) if `f` is a uniformly integrable (in the probability sense) submartingale strongly adapted to
  the filtration `ℱ`, it converges in L¹ to an integrable function `g` which is measurable with
  respect to `ℱ∞ := ⨆ n, ℱ n` and
(b) if `f` is actually a martingale, every `f n` is a conditional expectation of `g` given `ℱ n`.
(c) Finally, if `h` is integrable and almost everywhere measurable with respect to `ℱ∞`, then
  conditional expectations of `h` given the `ℱ n` converge to `h` almost everywhere and in L¹.

The proof is quite simple. (a) follows directly from the a.e. martingale convergence theorem
and the Vitali convergence theorem as our definition of uniform integrability (in the probability
sense) directly implies L¹-uniform boundedness. We note that our definition of uniform
integrability is slightly non-standard but is equivalent to the usual literary definition. This
equivalence is provided by `MeasureTheory.uniformIntegrable_iff`.

(b) follows since given $n$ and $s \in \mathcal{F}_n$, we have for all $m \ge n$,
$$
  \mathbb{E}f_n\mathbf{1}_s = \mathbb{E}f_m\mathbf{1}_s,
$$
and the right-hand side converges to $\mathbb{E}g\mathbf{1}_s$ as $m \to \infty$ since $f_m$
converges to $g$ in L¹. This holds for any measure.

Finally, to prove (c), we take conditional expectations $f_n$ of $h$ given $\mathcal{F}_n$. Up to
almost everywhere equality, every $f_n$ is $\mathcal{F}_n$-measurable, and then $(f_n)_n$ is a
martingale as its terms are conditional expectations of the same function. Furthermore,
$(f_n)_n$ is uniformly integrable in the probability sense. Indeed, as a single function is
uniformly integrable in the measure theory sense, for all $\epsilon > 0$, there exists some
$\delta > 0$ such that for all measurable set $A$ with $\mu(A) < δ$, we have
$\mathbb{E}|h|\mathbf{1}_A < \epsilon$. So, since for sufficiently large $\lambda$, by the Markov
inequality, we have for all $n$,
$$
  \mu(|f_n| \ge \lambda) \le \lambda^{-1}\mathbb{E}|f_n| \le \lambda^{-1}\mathbb{E}|h| < \delta,
$$
we have for sufficiently large $\lambda$, for all $n$,
$$
  \mathbb{E}|f_n|\mathbf{1}_{|f_n| \ge \lambda} \le
    \mathbb{E}|h|\mathbf{1}_{|f_n| \ge \lambda} < \epsilon,
$$
implying $(f_n)_n$ is uniformly integrable. Now, to prove $f_n \to h$ almost everywhere and in
L¹, it suffices to show that $h = g$ almost everywhere where $g$ is the almost everywhere and L¹
limit of $(f_n)_n$ from part (a) of the theorem. By noting that, for all $s \in \mathcal{F}_n$,
we have
$$
  \mathbb{E}g\mathbf{1}_s = \mathbb{E}f_n\mathbf{1}_s = \mathbb{E}h\mathbf{1}_s
$$
by part (b) and since $f_n$ is a conditional expectation of $h$; the equality also holds for all
$s \in \mathcal{F}_\infty$ by Dynkin's theorem. Thus, as both $h$ and $g$ are almost everywhere
$\mathcal{F}_\infty$-measurable, $h = g$ almost everywhere as required.

Similar to the a.e. martingale convergence theorem, rather than showing the existence of the
limiting process, we phrase the L¹-martingale convergence theorem by proving that a submartingale
does converge in L¹ to its `limitProcess`. However, in contrast to the a.e. martingale convergence
theorem, we do not need to introduce an L¹ version of `Filtration.limitProcess` as the L¹ limit
and the a.e. limit of a submartingale coincide.

-/

/-- If a martingale `f` strongly adapted to `ℱ` converges in L¹ to `g`, then for all `n`, `f n` is a
conditional expectation of `g` given `ℱ n`. The measure `μ` need not be finite. -/
theorem Martingale.isCondExp_of_tendsto_eLpNorm (hf : Martingale f ℱ μ)
    (hgtends : Tendsto (fun n ↦ eLpNorm (f n - g) 1 μ) atTop (𝓝 0)) (n : ℕ) :
    IsCondExp (ℱ n) μ g (f n) where
  aestronglyMeasurable := (hf.stronglyMeasurable n).aestronglyMeasurable
  integrableOn _ _ _ := (hf.integrable n).integrableOn
  setIntegral_eq s hs hgs := by
    have ht : Tendsto (fun m ↦ ∫ ω in s, f m ω ∂μ) atTop (𝓝 (∫ ω in s, g ω ∂μ)) :=
      tendsto_integral_of_L1' g hgs.aestronglyMeasurable
        (.of_forall fun m ↦ (hf.integrable m).restrict)
        (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hgtends (fun _ ↦ zero_le)
          fun _ ↦ eLpNorm_mono_measure _ Measure.restrict_le_self)
    exact tendsto_nhds_unique
      (tendsto_atTop_of_eventually_const fun m hm ↦ (hf.setIntegral_eq hm hs).symm) ht

variable [IsFiniteMeasure μ]

/-- Part a of the **L¹ martingale convergence theorem**: a uniformly integrable submartingale
strongly adapted to the filtration `ℱ` converges a.e. and in L¹ to an integrable function which is
measurable with respect to the σ-algebra `⨆ n, ℱ n`. -/
theorem Submartingale.tendsto_eLpNorm_one_limitProcess (hf : Submartingale f ℱ μ)
    (hunif : UniformIntegrable f 1 μ) :
    Tendsto (fun n => eLpNorm (f n - ℱ.limitProcess f μ) 1 μ) atTop (𝓝 0) := by
  obtain ⟨R, hR⟩ := hunif.2.2
  have hmeas : ∀ n, AEStronglyMeasurable (f n) μ := fun n =>
    ((hf.stronglyMeasurable n).mono (ℱ.le _)).aestronglyMeasurable
  exact tendsto_Lp_finite_of_tendstoInMeasure le_rfl ENNReal.one_ne_top hmeas
    (memLp_limitProcess_of_eLpNorm_bdd hmeas hR) hunif.2.1
    (tendstoInMeasure_of_tendsto_ae hmeas <| hf.ae_tendsto_limitProcess hR)

theorem Submartingale.ae_tendsto_limitProcess_of_uniformIntegrable (hf : Submartingale f ℱ μ)
    (hunif : UniformIntegrable f 1 μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (ℱ.limitProcess f μ ω)) :=
  let ⟨_, hR⟩ := hunif.2.2
  hf.ae_tendsto_limitProcess hR

/-- Part b of the **L¹ martingale convergence theorem**: if `f` is a uniformly integrable martingale
strongly adapted to the filtration `ℱ`, then for all `n`, `f n` is a conditional expectation of its
limiting process given `ℱ n`. -/
theorem Martingale.isCondExp_limitProcess (hf : Martingale f ℱ μ)
    (hbdd : UniformIntegrable f 1 μ) (n : ℕ) : IsCondExp (ℱ n) μ (ℱ.limitProcess f μ) (f n) :=
  hf.isCondExp_of_tendsto_eLpNorm (hf.submartingale.tendsto_eLpNorm_one_limitProcess hbdd) n

/-- Part c of the **L¹ martingale convergence theorem**: given an integrable function `g` which is
almost everywhere measurable with respect to `⨆ n, ℱ n` where `ℱ` is a filtration, conditional
expectations `G n` of `g` given `ℱ n` converge almost everywhere to `g`.

They also converge to `g` in L¹, see `MeasureTheory.Integrable.tendsto_eLpNorm_condExp`. -/
theorem Integrable.tendsto_ae_condExp (hg : Integrable g μ)
    (hgmeas : AEStronglyMeasurable[⨆ n, ℱ n] g μ) {G : ℕ → Ω → ℝ}
    (hG : ∀ n, IsCondExp (ℱ n) μ g (G n)) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ G n ω) atTop (𝓝 (g ω)) := by
  have hle : ⨆ n, ℱ n ≤ m0 := iSup_le ℱ.le
  -- `ℱ n`-strongly measurable versions of the conditional expectations form a martingale
  choose G' hG'm hGG' using fun n ↦ (hG n).aestronglyMeasurable
  have hG' (n : ℕ) : IsCondExp (ℱ n) μ g (G' n) := (hG n).congr_right (hGG' n)
  have hmart : Martingale G' ℱ μ := martingale_of_isCondExp hg hG'm hG'
  have hunif : UniformIntegrable G' 1 μ := hg.uniformIntegrable_condExp_filtration hG'
  obtain ⟨R, hR⟩ := hunif.2.2
  have hlimint : Integrable (ℱ.limitProcess G' μ) μ :=
    (memLp_limitProcess_of_eLpNorm_bdd hunif.1 hR).integrable le_rfl
  -- the limit process has the integrals of `g` over the sets of every `ℱ n`
  have hint (n : ℕ) (s : Set Ω) (hs : s ∈ ℱ n) :
      ∫ ω in s, g ω ∂μ = ∫ ω in s, ℱ.limitProcess G' μ ω ∂μ := by
    rw [← (hG' n).setIntegral_eq s hs hg.integrableOn,
      (hmart.isCondExp_limitProcess hunif n).setIntegral_eq s hs hlimint.integrableOn]
  -- hence over the sets of `⨆ n, ℱ n`, by Dynkin's π-λ theorem
  have hpi : IsPiSystem (⋃ n, ((ℱ n : SigmaAlgebra Ω) : Set (Set Ω))) :=
    isPiSystem_iUnion_of_monotone _ (fun n ↦ (ℱ n).isPiSystem) fun _ _ ↦ ℱ.mono
  have hsup (s : Set Ω) (hs : s ∈ ⨆ n, ℱ n) :
      ∫ ω in s, g ω ∂μ = ∫ ω in s, ℱ.limitProcess G' μ ω ∂μ := by
    induction s, hs
      using SigmaAlgebra.induction_on_inter (SigmaAlgebra.iSup_eq_generateFrom ℱ) hpi with
    | empty => simp only [Measure.restrict_empty, integral_zero_measure]
    | basic s hs =>
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hs
      exact hint n s hn
    | compl t ht ih =>
      rw [setIntegral_compl (hle ht) hg, setIntegral_compl (hle ht) hlimint, ih]
      congr 1
      simpa only [setIntegral_univ] using hint 0 _ (ℱ 0).univ_mem
    | iUnion t ht_disj ht ih =>
      rw [integral_iUnion (fun n ↦ hle (ht n)) ht_disj hg.integrableOn,
        integral_iUnion (fun n ↦ hle (ht n)) ht_disj hlimint.integrableOn]
      exact tsum_congr ih
  -- so the limit process is `g` almost everywhere
  have heq : g =ᵐ[μ] ℱ.limitProcess G' μ :=
    ae_eq_of_forall_setIntegral_eq_of_sigmaFinite' hle (fun _ _ _ ↦ hg.integrableOn)
      (fun _ _ _ ↦ hlimint.integrableOn) (fun s hs _ ↦ hsup s hs) hgmeas
      stronglyMeasurable_limitProcess.aestronglyMeasurable
  filter_upwards [heq, hmart.submartingale.ae_tendsto_limitProcess hR, ae_all_iff.2 hGG'] with
    ω hω hlim hGω
  rw [hω]
  exact hlim.congr fun n ↦ (hGω n).symm

/-- Part c of the **L¹ martingale convergence theorem**: given an integrable function `g` which is
almost everywhere measurable with respect to `⨆ n, ℱ n` where `ℱ` is a filtration, conditional
expectations `G n` of `g` given `ℱ n` converge in L¹ to `g`.

They also converge to `g` almost everywhere, see `MeasureTheory.Integrable.tendsto_ae_condExp`. -/
theorem Integrable.tendsto_eLpNorm_condExp (hg : Integrable g μ)
    (hgmeas : AEStronglyMeasurable[⨆ n, ℱ n] g μ) {G : ℕ → Ω → ℝ}
    (hG : ∀ n, IsCondExp (ℱ n) μ g (G n)) :
    Tendsto (fun n ↦ eLpNorm (G n - g) 1 μ) atTop (𝓝 0) :=
  tendsto_Lp_finite_of_tendstoInMeasure le_rfl ENNReal.one_ne_top
    (fun n ↦ (hG n).aestronglyMeasurable' (ℱ.le n)) (memLp_one_iff_integrable.2 hg)
    (hg.uniformIntegrable_condExp_filtration hG).2.1
    (tendstoInMeasure_of_tendsto_ae (fun n ↦ (hG n).aestronglyMeasurable' (ℱ.le n))
      (hg.tendsto_ae_condExp hgmeas hG))

/-- **Lévy's upward theorem**, almost everywhere version: given an integrable function `g` and a
filtration `ℱ`, conditional expectations `G n` of `g` given `ℱ n` converge almost everywhere to a
conditional expectation `G'` of `g` given `⨆ n, ℱ n`. -/
theorem tendsto_ae_condExp (hg : Integrable g μ) {G : ℕ → Ω → ℝ}
    (hG : ∀ n, IsCondExp (ℱ n) μ g (G n)) {G' : Ω → ℝ} (hG' : IsCondExp (⨆ n, ℱ n) μ g G') :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ G n ω) atTop (𝓝 (G' ω)) := by
  -- every `G n` is also a conditional expectation of `G'` given `ℱ n`
  refine (hG'.integrable hg).tendsto_ae_condExp hG'.aestronglyMeasurable fun n ↦ ?_
  refine ⟨(hG n).aestronglyMeasurable, fun _ _ _ ↦ ((hG n).integrable hg).integrableOn,
    fun s hs _ ↦ ?_⟩
  rw [(hG n).setIntegral_eq s hs hg.integrableOn,
    hG'.setIntegral_eq s (le_iSup (fun n ↦ (ℱ n : SigmaAlgebra Ω)) n hs) hg.integrableOn]

/-- **Lévy's upward theorem**, L¹ version: given an integrable function `g` and a filtration `ℱ`,
conditional expectations `G n` of `g` given `ℱ n` converge in L¹ to a conditional expectation `G'`
of `g` given `⨆ n, ℱ n`. -/
theorem tendsto_eLpNorm_condExp (hg : Integrable g μ) {G : ℕ → Ω → ℝ}
    (hG : ∀ n, IsCondExp (ℱ n) μ g (G n)) {G' : Ω → ℝ} (hG' : IsCondExp (⨆ n, ℱ n) μ g G') :
    Tendsto (fun n ↦ eLpNorm (G n - G') 1 μ) atTop (𝓝 0) :=
  tendsto_Lp_finite_of_tendstoInMeasure le_rfl ENNReal.one_ne_top
    (fun n ↦ (hG n).aestronglyMeasurable' (ℱ.le n))
    (memLp_one_iff_integrable.2 (hG'.integrable hg))
    (hg.uniformIntegrable_condExp_filtration hG).2.1
    (tendstoInMeasure_of_tendsto_ae (fun n ↦ (hG n).aestronglyMeasurable' (ℱ.le n))
      (tendsto_ae_condExp hg hG hG'))

end L1Convergence

end MeasureTheory
