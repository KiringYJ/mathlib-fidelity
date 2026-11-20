/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Data.Set.Pointwise.Support
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Bump functions in finite-dimensional vector spaces

Let `E` be a finite-dimensional real normed vector space. We show that any open set `s` in `E` is
exactly the support of a smooth function taking values in `[0, 1]`,
in `IsOpen.exists_contDiff_support_eq`.

Then we use this construction to construct bump functions with nice behavior, by convolving
the indicator function of `closedBall 0 1` with a function as above with `s = ball 0 D`.
-/

@[expose] public section


noncomputable section

open Set Metric TopologicalSpace Function MeasureTheory Module
  ContinuousLinearMap Filter MeasureTheory.Measure Bornology

open scoped Pointwise Topology NNReal Convolution ContDiff

variable {E : Type*} [NormedAddCommGroup E]

section

variable [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- If a set `s` is a neighborhood of `x`, then there exists a smooth function `f` taking
values in `[0, 1]`, supported in `s` and with `f x = 1`. -/
theorem exists_contDiff_tsupport_subset {s : Set E} {x : E} {n : ℕ∞} (hs : s ∈ 𝓝 x) :
    ∃ f : E → ℝ,
      tsupport f ⊆ s ∧ HasCompactSupport f ∧ ContDiff ℝ n f ∧ range f ⊆ Icc 0 1 ∧ f x = 1 := by
  obtain ⟨d : ℝ, d_pos : 0 < d, hd : Euclidean.closedBall x d ⊆ s⟩ :=
    Euclidean.nhds_basis_closedBall.mem_iff.1 hs
  let c : ContDiffBump (toEuclidean x) :=
    { rIn := d / 2
      rOut := d
      rIn_pos := half_pos d_pos
      rIn_lt_rOut := half_lt_self d_pos }
  let f : E → ℝ := c ∘ toEuclidean
  have f_supp : f.support ⊆ Euclidean.ball x d := by
    intro y hy
    have : toEuclidean y ∈ Function.support c := by
      simpa only [Function.mem_support, Function.comp_apply, Ne] using! hy
    rwa [c.support_eq] at this
  have f_tsupp : tsupport f ⊆ Euclidean.closedBall x d := by
    rw [tsupport, ← Euclidean.closure_ball _ d_pos.ne']
    exact closure_mono f_supp
  refine ⟨f, f_tsupp.trans hd, ?_, ?_, ?_, ?_⟩
  · refine isCompact_of_isClosed_isBounded isClosed_closure ?_
    have : IsBounded (Euclidean.closedBall x d) := Euclidean.isCompact_closedBall.isBounded
    refine this.subset (Euclidean.isClosed_closedBall.closure_subset_iff.2 ?_)
    exact f_supp.trans Euclidean.ball_subset_closedBall
  · apply c.contDiff.comp
    exact ContinuousLinearEquiv.contDiff _
  · rintro t ⟨y, rfl⟩
    exact ⟨c.nonneg, c.le_one⟩
  · apply c.one_of_mem_closedBall
    apply mem_closedBall_self
    exact (half_pos d_pos).le

/-- Given an open set `s` in a finite-dimensional real normed vector space, there exists a smooth
function with values in `[0, 1]` whose support is exactly `s`. -/
theorem IsOpen.exists_contDiff_support_eq {n : ℕ∞} {s : Set E} (hs : IsOpen s) :
    ∃ f : E → ℝ, f.support = s ∧ ContDiff ℝ n f ∧ Set.range f ⊆ Set.Icc 0 1 := by
  /- For any given point `x` in `s`, one can construct a smooth function with support in `s` and
    nonzero at `x`. By second-countability, it follows that we may cover `s` with the supports of
    countably many such functions, say `g i`.
    Then `∑ i, r i • g i` will be the desired function if `r i` is a sequence of positive numbers
    tending quickly enough to zero. Indeed, this ensures that, for any `k ≤ i`, the `k`-th
    derivative of `r i • g i` is bounded by a prescribed (summable) sequence `u i`. From this, the
    summability of the series and of its successive derivatives follows. -/
  rcases eq_empty_or_nonempty s with (rfl | h's)
  · exact
      ⟨fun _ => 0, Function.support_zero, contDiff_const, by
        simp only [range_const, singleton_subset_iff, left_mem_Icc, zero_le_one]⟩
  let ι := { f : E → ℝ // f.support ⊆ s ∧ HasCompactSupport f ∧ ContDiff ℝ ∞ f ∧ range f ⊆ Icc 0 1 }
  obtain ⟨T, T_count, hT⟩ : ∃ T : Set ι, T.Countable ∧ ⋃ f ∈ T, support (f : E → ℝ) = s := by
    have : ⋃ f : ι, (f : E → ℝ).support = s := by
      refine Subset.antisymm (iUnion_subset fun f => f.2.1) ?_
      intro x hx
      rcases exists_contDiff_tsupport_subset (hs.mem_nhds hx) with ⟨f, hf⟩
      let g : ι := ⟨f, (subset_tsupport f).trans hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1⟩
      have : x ∈ support (g : E → ℝ) := by
        simp only [g, hf.2.2.2.2, mem_support, Ne, one_ne_zero, not_false_iff]
      exact mem_iUnion_of_mem _ this
    simp_rw [← this]
    apply isOpen_iUnion_countable
    rintro ⟨f, hf⟩
    exact hf.2.2.1.continuous.isOpen_support
  obtain ⟨g0, hg⟩ : ∃ g0 : ℕ → ι, T = range g0 := by
    apply Countable.exists_eq_range T_count
    rcases eq_empty_or_nonempty T with (rfl | hT)
    · simp only [← hT, mem_empty_iff_false, iUnion_of_empty, iUnion_empty, Set.not_nonempty_empty]
        at h's
    · exact hT
  let g : ℕ → E → ℝ := fun n => (g0 n).1
  have g_s : ∀ n, support (g n) ⊆ s := fun n => (g0 n).2.1
  have s_g : ∀ x ∈ s, ∃ n, x ∈ support (g n) := fun x hx ↦ by
    rw [← hT] at hx
    obtain ⟨i, iT, hi⟩ : ∃ i ∈ T, x ∈ support (i : E → ℝ) := by
      simpa only [mem_iUnion, exists_prop] using! hx
    #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
    (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal
    without the `obtain` on the next line. It is not yet clear whether this is due to defeq
    abuse in Mathlib or a problem in the new canonicalizer; a minimization would help. -/
    obtain ⟨n, hn⟩ := hg ▸ iT
    grind
  have g_smooth : ∀ n, ContDiff ℝ ∞ (g n) := fun n => (g0 n).2.2.2.1
  have g_comp_supp : ∀ n, HasCompactSupport (g n) := fun n => (g0 n).2.2.1
  have g_nonneg : ∀ n x, 0 ≤ g n x := fun n x => ((g0 n).2.2.2.2 (mem_range_self x)).1
  obtain ⟨δ, δpos, c, δc, c_lt⟩ :
      ∃ δ : ℕ → ℝ≥0, (∀ i : ℕ, 0 < δ i) ∧ ∃ c : NNReal, HasSum δ c ∧ c < 1 :=
    NNReal.exists_pos_sum_of_countable one_ne_zero ℕ
  have : ∀ n : ℕ, ∃ r : ℝ, 0 < r ∧ ∀ i ≤ n, ∀ x, ‖iteratedFDeriv ℝ i (r • g n) x‖ ≤ δ n := by
    intro n
    have : ∀ i, ∃ R, ∀ x, ‖iteratedFDeriv ℝ i (fun x => g n x) x‖ ≤ R := by
      intro i
      have : BddAbove (range fun x => ‖iteratedFDeriv ℝ i (fun x : E => g n x) x‖) := by
        apply ((g_smooth n).continuous_iteratedFDeriv
          (mod_cast le_top)).norm.bddAbove_range_of_hasCompactSupport
        apply HasCompactSupport.comp_left _ norm_zero
        apply (g_comp_supp n).iteratedFDeriv
      rcases this with ⟨R, hR⟩
      exact ⟨R, fun x => hR (mem_range_self _)⟩
    choose R hR using this
    let M := max (((Finset.range (n + 1)).image R).max' (by simp)) 1
    have hM : 0 < M := zero_lt_one.trans_le (le_max_right _ _)
    have δnpos : 0 < δ n := δpos n
    have IR : ∀ i ≤ n, R i ≤ M := by
      intro i hi
      refine le_trans ?_ (le_max_left _ _)
      apply Finset.le_max'
      apply Finset.mem_image_of_mem
      simp only [Finset.mem_range]
      lia
    refine ⟨M⁻¹ * δ n, by positivity, fun i hi x => ?_⟩
    calc
      ‖iteratedFDeriv ℝ i ((M⁻¹ * δ n) • g n) x‖ = ‖(M⁻¹ * δ n) • iteratedFDeriv ℝ i (g n) x‖ := by
        rw [iteratedFDeriv_const_smul_apply]
        exact (g_smooth n).contDiffAt.of_le (mod_cast le_top)
      _ = M⁻¹ * δ n * ‖iteratedFDeriv ℝ i (g n) x‖ := by
        rw [norm_smul _ (iteratedFDeriv ℝ i (g n) x), Real.norm_of_nonneg]; positivity
      _ ≤ M⁻¹ * δ n * M := by gcongr; exact (hR i x).trans (IR i hi)
      _ = δ n := by rw [mul_right_comm, inv_mul_cancel₀, one_mul]
  choose r rpos hr using this
  have S : ∀ x, Summable fun n => (r n • g n) x := fun x ↦ by
    refine .of_nnnorm_bounded δc.summable fun n => ?_
    rw [← NNReal.coe_le_coe, coe_nnnorm]
    simpa only [norm_iteratedFDeriv_zero] using! hr n 0 zero_le x
  refine ⟨fun x => ∑' n, (r n • g n) x, ?_, ?_, ?_⟩
  · apply Subset.antisymm
    · intro x hx
      simp only [Pi.smul_apply, smul_eq_mul, mem_support, Ne] at hx
      contrapose hx
      have : ∀ n, g n x = 0 := by
        intro n
        contrapose! hx
        exact g_s n hx
      simp only [this, mul_zero, tsum_zero]
    · intro x hx
      obtain ⟨n, hn⟩ : ∃ n, x ∈ support (g n) := s_g x hx
      have I : 0 < r n * g n x := mul_pos (rpos n) (lt_of_le_of_ne (g_nonneg n x) (Ne.symm hn))
      exact ne_of_gt ((S x).tsum_pos (fun i => mul_nonneg (rpos i).le (g_nonneg i x)) n I)
  · apply ContDiff.of_le _ (show n ≤ ∞ from mod_cast le_top)
    refine
      contDiff_tsum_of_eventually (fun k => (g_smooth k).const_smul (r k))
        (fun k _ => (NNReal.hasSum_coe.2 δc).summable) ?_
    intro i _
    simp only [Nat.cofinite_eq_atTop, Filter.eventually_atTop]
    exact ⟨i, fun n hn x => hr _ _ hn _⟩
  · rintro - ⟨y, rfl⟩
    refine ⟨tsum_nonneg fun n => mul_nonneg (rpos n).le (g_nonneg n y), le_trans ?_ c_lt.le⟩
    have A : HasSum (fun n => (δ n : ℝ)) c := NNReal.hasSum_coe.2 δc
    simp only [Pi.smul_apply, smul_eq_mul, NNReal.val_eq_coe, ← A.tsum_eq]
    apply Summable.tsum_le_tsum _ (S y) A.summable
    intro n
    apply (le_abs_self _).trans
    simpa only [norm_iteratedFDeriv_zero] using! hr n 0 zero_le y

end

section

namespace ExistsContDiffBumpBase

/-- An auxiliary function to construct partitions of unity on finite-dimensional real vector spaces.
It is the characteristic function of the closed unit ball. -/
def φ : E → ℝ :=
  (closedBall (0 : E) 1).indicator fun _ => (1 : ℝ)

variable [NormedSpace ℝ E] [FiniteDimensional ℝ E]

section HelperDefinitions

variable (E)

theorem u_exists :
    ∃ u : E → ℝ,
      ContDiff ℝ ∞ u ∧ (∀ x, u x ∈ Icc (0 : ℝ) 1) ∧ support u = ball 0 1 ∧ ∀ x, u (-x) = u x := by
  have A : IsOpen (ball (0 : E) 1) := isOpen_ball
  obtain ⟨f, f_support, f_smooth, f_range⟩ :
      ∃ f : E → ℝ, f.support = ball (0 : E) 1 ∧ ContDiff ℝ ∞ f ∧ Set.range f ⊆ Set.Icc 0 1 :=
    A.exists_contDiff_support_eq
  have B : ∀ x, f x ∈ Icc (0 : ℝ) 1 := fun x => f_range (mem_range_self x)
  refine ⟨fun x => (f x + f (-x)) / 2, ?_, ?_, ?_, ?_⟩
  · exact (f_smooth.add (f_smooth.comp contDiff_neg)).div_const _
  · intro x
    push _ ∈ _
    constructor
    · linarith [(B x).1, (B (-x)).1]
    · linarith [(B x).2, (B (-x)).2]
  · refine support_eq_iff.2 ⟨fun x hx => ?_, fun x hx => ?_⟩
    · apply ne_of_gt
      have : 0 < f x := by
        apply lt_of_le_of_ne (B x).1 (Ne.symm _)
        rwa [← f_support] at hx
      linarith [(B (-x)).1]
    · have I1 : x ∉ support f := by rwa [f_support]
      have I2 : -x ∉ support f := by
        rw [f_support]
        simpa using hx
      simp only [mem_support, Classical.not_not] at I1 I2
      simp only [I1, I2, add_zero, zero_div]
  · intro x; simp only [add_comm, neg_neg]

variable {E} in
/-- An auxiliary function to construct partitions of unity on finite-dimensional real vector spaces,
which is smooth, symmetric, and with support equal to the unit ball. -/
def u (x : E) : ℝ :=
  Classical.choose (u_exists E) x

theorem u_smooth : ContDiff ℝ ∞ (u : E → ℝ) :=
  (Classical.choose_spec (u_exists E)).1

theorem u_continuous : Continuous (u : E → ℝ) :=
  (u_smooth E).continuous

theorem u_support : support (u : E → ℝ) = ball 0 1 :=
  (Classical.choose_spec (u_exists E)).2.2.1

theorem u_compact_support : HasCompactSupport (u : E → ℝ) := by
  rw [hasCompactSupport_def, u_support, closure_ball (0 : E) one_ne_zero]
  exact isCompact_closedBall _ _

variable {E}

theorem u_nonneg (x : E) : 0 ≤ u x :=
  ((Classical.choose_spec (u_exists E)).2.1 x).1

theorem u_le_one (x : E) : u x ≤ 1 :=
  ((Classical.choose_spec (u_exists E)).2.1 x).2

theorem u_neg (x : E) : u (-x) = u x :=
  (Classical.choose_spec (u_exists E)).2.2.2 x

variable [SigmaAlgebra E] [BorelSpace E]

local notation "μ" => MeasureTheory.Measure.addHaar

variable (E) in
theorem u_int_pos : 0 < ∫ x : E, u x ∂μ := by
  refine (integral_pos_iff_support_of_nonneg u_nonneg ?_).mpr ?_
  · exact (u_continuous E).integrable_of_hasCompactSupport (u_compact_support E)
  · rw [u_support]; exact measure_ball_pos _ _ zero_lt_one

/-- A smooth, symmetric function of integral one, supported on the ball of radius `|D|`. -/
def w (D : ℝ) (hD : IsUnit D) (x : E) : ℝ :=
  Checked.inv ((∫ x : E, u x ∂μ) * |D| ^ finrank ℝ E)
    ((u_int_pos E).ne'.isUnit.mul ((abs_pos.mpr hD.ne_zero).ne'.isUnit.pow _)) • u (D⁻¹ • x)

theorem w_def (D : ℝ) (hD : IsUnit D) :
    (w D hD : E → ℝ) = fun x ↦
      Checked.inv ((∫ x : E, u x ∂μ) * |D| ^ finrank ℝ E)
        (mul_pos (u_int_pos E) (pow_pos (abs_pos.mpr hD.ne_zero) _)).ne'.isUnit • u (D⁻¹ • x) := rfl

theorem w_nonneg (D : ℝ) (hD : IsUnit D) (x : E) : 0 ≤ w D hD x := by
  unfold w
  exact mul_nonneg (inv_nonneg.2 (mul_nonneg (u_int_pos E).le (pow_nonneg (abs_nonneg D) _)))
    (u_nonneg _)

theorem w_mul_φ_nonneg (D : ℝ) (hD : IsUnit D) (x y : E) : 0 ≤ w D hD y * φ (x - y) :=
  mul_nonneg (w_nonneg D hD y) (indicator_nonneg (by simp only [zero_le_one, imp_true_iff]) _)

variable (E)

theorem w_integral {D : ℝ} (hD : IsUnit D) : ∫ x : E, w D hD x ∂μ = 1 := by
  unfold w
  rw [integral_smul, integral_comp_inv_smul μ (u : E → ℝ) D (hR := hD)]
  simp only [abs_pow, smul_eq_mul, mul_comm (|D| ^ finrank ℝ E) (∫ x : E, u x ∂μ),
    inv_mul_cancel₀]

theorem w_support {D : ℝ} (Dpos : 0 < D) :
    support (w D Dpos.ne'.isUnit : E → ℝ) = ball 0 D := by
  have B : D • ball (0 : E) 1 = ball 0 D := by
    rw [smul_unitBall Dpos.ne', Real.norm_of_nonneg Dpos.le]
  have h : 0 < (∫ x : E, u x ∂μ) * |D| ^ finrank ℝ E :=
    mul_pos (u_int_pos E) (pow_pos (abs_pos_of_pos Dpos) _)
  simp only [w_def, smul_eq_mul, support_mul, support_const (inv_ne_zero (ha := h.ne'.isUnit)),
    univ_inter, support_comp_inv_smul₀ Dpos.ne', u_support, B]

theorem w_compact_support {D : ℝ} (Dpos : 0 < D) :
    HasCompactSupport (w D Dpos.ne'.isUnit : E → ℝ) := by
  rw [hasCompactSupport_def, w_support E Dpos, closure_ball (0 : E) Dpos.ne']
  exact isCompact_closedBall _ _

variable {E}

/-- An auxiliary function to construct partitions of unity on finite-dimensional real vector spaces.
It is the convolution between a smooth function of integral `1` supported in the ball of radius `D`,
with the indicator function of the closed unit ball. Therefore, it is smooth, equal to `1` on the
ball of radius `1 - D`, with support equal to the ball of radius `1 + D`. -/
def y (D : ℝ) (hD : IsUnit D) : E → ℝ :=
  w D hD ⋆[lsmul ℝ ℝ, μ] φ

theorem y_neg (D : ℝ) (hD : IsUnit D) (x : E) : y D hD (-x) = y D hD x := by
  apply convolution_neg_of_neg_eq
  · filter_upwards with x
    simp only [w_def, smul_neg, u_neg, smul_eq_mul]
  · filter_upwards with x
    simp only [φ, indicator, mem_closedBall, dist_zero_right, norm_neg]

theorem y_eq_one_of_mem_closedBall {D : ℝ} {x : E} (Dpos : 0 < D)
    (hx : x ∈ closedBall (0 : E) (1 - D)) : y D Dpos.ne'.isUnit x = 1 := by
  change (w D Dpos.ne'.isUnit ⋆[lsmul ℝ ℝ, μ] φ) x = 1
  have B : ∀ y : E, y ∈ ball x D → φ y = 1 := by
    have C : ball x D ⊆ ball 0 1 := by
      apply ball_subset_ball'
      simp only [mem_closedBall] at hx
      linarith only [hx]
    intro y hy
    simp only [φ, indicator, mem_closedBall, ite_eq_left_iff, not_le, zero_ne_one]
    intro h'y
    linarith only [mem_ball.1 (C hy), h'y]
  have Bx : φ x = 1 := B _ (mem_ball_self Dpos)
  have B' : ∀ y, y ∈ ball x D → φ y = φ x := by rw [Bx]; exact B
  rw [convolution_eq_right' _ (le_of_eq (w_support E Dpos)) B']
  simp only [lsmul_apply, smul_eq_mul, integral_mul_const, w_integral E Dpos.ne'.isUnit, Bx,
    one_mul]

theorem y_eq_zero_of_notMem_ball {D : ℝ} {x : E} (Dpos : 0 < D) (hx : x ∉ ball (0 : E) (1 + D)) :
    y D Dpos.ne'.isUnit x = 0 := by
  change (w D Dpos.ne'.isUnit ⋆[lsmul ℝ ℝ, μ] φ) x = 0
  have B : ∀ y, y ∈ ball x D → φ y = 0 := by
    intro y hy
    simp only [φ, indicator, mem_closedBall_zero_iff, ite_eq_right_iff, one_ne_zero]
    intro h'y
    have C : ball y D ⊆ ball 0 (1 + D) := by
      apply ball_subset_ball'
      rw [← dist_zero_right] at h'y
      linarith only [h'y]
    exact hx (C (mem_ball_comm.1 hy))
  have Bx : φ x = 0 := B _ (mem_ball_self Dpos)
  have B' : ∀ y, y ∈ ball x D → φ y = φ x := by rw [Bx]; exact B
  rw [convolution_eq_right' _ (le_of_eq (w_support E Dpos)) B']
  simp only [lsmul_apply, smul_eq_mul, Bx, mul_zero, integral_const]

theorem y_nonneg (D : ℝ) (hD : IsUnit D) (x : E) : 0 ≤ y D hD x :=
  integral_nonneg (w_mul_φ_nonneg D hD x)

theorem y_le_one {D : ℝ} (x : E) (Dpos : 0 < D) : y D Dpos.ne'.isUnit x ≤ 1 := by
  have A : (w D Dpos.ne'.isUnit ⋆[lsmul ℝ ℝ, μ] φ) x ≤
      (w D Dpos.ne'.isUnit ⋆[lsmul ℝ ℝ, μ] 1) x := by
    apply
      convolution_mono_right_of_nonneg _ (w_nonneg D Dpos.ne'.isUnit)
        (indicator_le_self' fun x _ => zero_le_one)
        fun _ => zero_le_one
    refine ((w_compact_support E Dpos).convolutionExists_left _ ?_
      (locallyIntegrable_const (1 : ℝ)) x).integrable
    exact continuous_const.mul ((u_continuous E).comp (by fun_prop))
  have B : (w D Dpos.ne'.isUnit ⋆[lsmul ℝ ℝ, μ] fun _ => (1 : ℝ)) x = 1 := by
    simp only [convolution, mul_one, lsmul_apply, smul_eq_mul, w_integral E Dpos.ne'.isUnit]
  exact A.trans (le_of_eq B)

theorem y_pos_of_mem_ball {D : ℝ} {x : E} (Dpos : 0 < D) (D_lt_one : D < 1)
    (hx : x ∈ ball (0 : E) (1 + D)) : 0 < y D Dpos.ne'.isUnit x := by
  simp only [mem_ball_zero_iff] at hx
  refine (integral_pos_iff_support_of_nonneg (w_mul_φ_nonneg D Dpos.ne'.isUnit x) ?_).2 ?_
  · have F_comp : HasCompactSupport (w D Dpos.ne'.isUnit) := w_compact_support E Dpos
    have B : LocallyIntegrable (φ : E → ℝ) μ :=
      (locallyIntegrable_const _).indicator measurableSet_closedBall
    have C : Continuous (w D Dpos.ne'.isUnit : E → ℝ) :=
      continuous_const.mul ((u_continuous E).comp (by fun_prop))
    exact (F_comp.convolutionExists_left (lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ) C B x).integrable
  · have B : 0 < 1 + D := by linarith
    set z := (D / (1 + D)) • x with hz
    have C : ball z (D * (1 + D - ‖x‖) / (1 + D)) ⊆
        support fun y : E => w D Dpos.ne'.isUnit y * φ (x - y) := by
      intro y hy
      simp only [support_mul, w_support E Dpos]
      simp only [φ, mem_inter_iff, mem_support, Ne, indicator_apply_eq_zero,
        mem_closedBall_zero_iff, one_ne_zero, not_forall, not_false_iff, exists_prop, and_true]
      constructor
      · apply ball_subset_ball' _ hy
        simp only [hz, norm_smul, abs_of_nonneg Dpos.le, abs_of_nonneg B.le, dist_zero_right,
          Real.norm_eq_abs, abs_div]
        field_simp
        linarith only
      · have ID : ‖D / (1 + D) - 1‖ = 1 / (1 + D) := by
          rw [Real.norm_of_nonpos (sub_nonpos.mpr ((div_le_one B).mpr (by linarith)))]
          field
        rw [← mem_closedBall_iff_norm']
        apply closedBall_subset_closedBall' _ (ball_subset_closedBall hy)
        rw [← one_smul ℝ x, dist_eq_norm, hz, ← sub_smul, one_smul, norm_smul, ID]
        rw [div_mul_eq_mul_div₀, one_mul, ← add_div, div_le_one B]
        nlinarith only [mul_nonneg (sub_nonneg.mpr D_lt_one.le) (sub_nonneg.mpr hx.le)]
    apply lt_of_lt_of_le _ (measure_mono C)
    apply measure_ball_pos
    exact div_pos (mul_pos Dpos (by linarith only [hx])) B

variable (E)

/-- A representative of the convolved bumps is smooth on the range of parameters
where the bumps have uniformly bounded support. -/
theorem y_smooth {g : ℝ → E → ℝ}
    (hg : ∀ D ∈ Ioo (0 : ℝ) 1, ∀ hD : IsUnit D, g D = y D hD) :
    ContDiffOn ℝ ∞ (uncurry g) (Ioo (0 : ℝ) 1 ×ˢ (univ : Set E)) := by
  let S := Ioo (0 : ℝ) 1 ×ˢ (univ : Set E)
  let A (D : ℝ) : ℝ := (∫ x : E, u x ∂μ) * |D| ^ finrank ℝ E
  have hA (D : ℝ) (hD : 0 < D) : IsUnit (A D) :=
    (mul_pos (u_int_pos E) (pow_pos (abs_pos_of_pos hD) _)).ne'.isUnit
  let a (D : ℝ) := if hD : 0 < D then Checked.inv (A D) (hA D hD) else 0
  let b (D : ℝ) := if hD : 0 < D then Checked.inv D hD.ne'.isUnit else 0
  let W (D : ℝ) (x : E) := a D * u (b D • x)
  have hW (D : ℝ) (hD : 0 < D) : W D = w D hD.ne'.isUnit := by
    funext x
    simp only [W, a, b, A, dite_eq_left hD, w, smul_eq_mul]
  have hW_smooth : ContDiffOn ℝ ∞ (uncurry W) S := by
    have habs : ContDiffOn ℝ ∞ (fun p : ℝ × E ↦ |p.1|) S :=
      contDiffOn_fst.congr (fun p hp ↦ abs_of_nonneg hp.1.1.le)
    have hA_smooth : ContDiffOn ℝ ∞ (fun p : ℝ × E ↦ A p.1) S :=
      contDiffOn_const.mul (habs.pow _)
    have ha : ContDiffOn ℝ ∞ (fun p : ℝ × E ↦ a p.1) S := by
      apply hA_smooth.inv
      exact fun p hp ↦ ⟨hA p.1 hp.1.1, dite_eq_left hp.1.1⟩
    have hb : ContDiffOn ℝ ∞ (fun p : ℝ × E ↦ b p.1) S := by
      apply contDiffOn_fst.inv
      exact fun p hp ↦ ⟨hp.1.1.ne'.isUnit, dite_eq_left hp.1.1⟩
    exact ha.mul ((u_smooth E).comp_contDiffOn (hb.smul contDiffOn_snd))
  have hsupp (D : ℝ) (x : E) (hD : D ∈ Ioo (0 : ℝ) 1) (hx : x ∉ closedBall 0 1) :
      W D x = 0 := by
    rw [hW D hD.1]
    apply notMem_support.mp
    rw [w_support E hD.1]
    exact fun hx' ↦ hx (ball_subset_closedBall (ball_subset_ball hD.2.le hx'))
  have hind : LocallyIntegrable (φ : E → ℝ) μ :=
    (locallyIntegrable_const _).indicator measurableSet_closedBall
  have h := contDiffOn_convolution_left_with_param (lsmul ℝ ℝ) isOpen_Ioo
    (isCompact_closedBall (0 : E) 1) hsupp hind hW_smooth
  apply h.congr
  rintro ⟨D, x⟩ hx
  change g D x = (W D ⋆[lsmul ℝ ℝ, μ] φ) x
  rw [hg D hx.1 hx.1.1.ne'.isUnit, hW D hx.1.1, y]

theorem y_support {D : ℝ} (Dpos : 0 < D) (D_lt_one : D < 1) :
    support (y D Dpos.ne'.isUnit : E → ℝ) = ball (0 : E) (1 + D) :=
  support_eq_iff.2
    ⟨fun _ hx => (y_pos_of_mem_ball Dpos D_lt_one hx).ne', fun _ hx =>
      y_eq_zero_of_notMem_ball Dpos hx⟩

end HelperDefinitions

instance (priority := 100) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] : HasContDiffBump E := by
  refine ⟨⟨?_⟩⟩
  borelize E
  have hAddOne {r : ℝ} (hr : 1 < r) : 0 < r + 1 := by linarith
  let D (R : Ioi (1 : ℝ)) : ℝ := Checked.div ((R : ℝ) - 1) ((R : ℝ) + 1)
    (hAddOne R.2).ne'.isUnit
  let scale (R : Ioi (1 : ℝ)) : ℝ := Checked.div 2 ((R : ℝ) + 1)
    (hAddOne R.2).ne'.isUnit
  have hDpos (R : Ioi (1 : ℝ)) : 0 < D R :=
    div_pos (sub_pos.mpr R.2) (hAddOne R.2)
  have hDlt (R : Ioi (1 : ℝ)) : D R < 1 := by
    apply (div_lt_one (hAddOne R.2)).mpr
    linarith
  exact
    { toFun := fun R x => if hR : 1 < R then
        y (D ⟨R, hR⟩) (hDpos ⟨R, hR⟩).ne'.isUnit (scale ⟨R, hR⟩ • x) else 0
      mem_Icc := fun R x => by
        push _ ∈ _
        split_ifs with hR
        · exact ⟨y_nonneg _ _ _, y_le_one _ (hDpos ⟨R, hR⟩)⟩
        · simp only [le_refl, zero_le_one, and_self]
      symmetric := fun R x => by
        split_ifs
        · simp only [y_neg, smul_neg]
        · rfl
      smooth := by
        let d (R : ℝ) := if hR : 1 < R then D ⟨R, hR⟩ else 0
        let s (R : ℝ) := if hR : 1 < R then scale ⟨R, hR⟩ else 0
        let g (r : ℝ) (x : E) := if hr : 0 < r then y r hr.ne'.isUnit x else 0
        have hg : ContDiffOn ℝ ∞ (uncurry g) (Ioo (0 : ℝ) 1 ×ˢ (univ : Set E)) :=
          y_smooth E (fun r hr _ ↦ funext fun x ↦ dite_eq_left hr.1)
        have hdiffD : ContDiffOn ℝ ∞ (fun p : ℝ × E ↦ d p.1) (Ioi 1 ×ˢ univ) := by
          apply (contDiffOn_fst.sub contDiffOn_const).div (contDiffOn_fst.add contDiffOn_const)
          exact fun p hp ↦ ⟨(hAddOne hp.1).ne'.isUnit, dite_eq_left hp.1⟩
        have hdiffS : ContDiffOn ℝ ∞ (fun p : ℝ × E ↦ s p.1) (Ioi 1 ×ˢ univ) := by
          apply contDiffOn_const.div (contDiffOn_fst.add contDiffOn_const)
          exact fun p hp ↦ ⟨(hAddOne hp.1).ne'.isUnit, dite_eq_left hp.1⟩
        refine (hg.comp (hdiffD.prodMk (hdiffS.smul contDiffOn_snd)) ?_).congr ?_
        · intro p hp
          have hp' : 1 < p.1 := hp.1
          have hs : D ⟨p.1, hp'⟩ ∈ Ioo (0 : ℝ) 1 := ⟨hDpos _, hDlt _⟩
          exact ⟨by simpa only [d, dite_eq_left hp'] using hs, mem_univ _⟩
        · rintro ⟨R, x⟩ hR
          have hR' : 1 < R := hR.1
          change _ = g (d R) (s R • x)
          simp only [uncurry_apply_pair, d, s, g, dite_eq_left hR',
            dite_eq_left (hDpos ⟨R, hR'⟩)]
      eq_one := fun R hR x hx => by
        have A : 0 < R + 1 := by linarith
        simp only [dite_eq_left hR]
        apply y_eq_one_of_mem_closedBall (hDpos ⟨R, hR⟩)
        simp only [scale, norm_smul, mem_closedBall_zero_iff, Real.norm_eq_abs, abs_div,
          abs_two, abs_of_nonneg A.le]
        calc
          2 / (R + 1) * ‖x‖ ≤ 2 / (R + 1) := mul_le_of_le_one_right (by positivity) hx
          _ = 1 - D ⟨R, hR⟩ := by dsimp [D]; field
      support := fun R hR => by
        have A : 0 < (R + 1) / 2 := by linarith
        have he : scale ⟨R, hR⟩ = ((R + 1) / 2)⁻¹ := by dsimp [scale]; field
        simp only [dite_eq_left hR, he, support_comp_inv_smul₀ A.ne', y_support _ (hDpos ⟨R, hR⟩)
          (hDlt ⟨R, hR⟩), _root_.smul_ball A.ne', Real.norm_of_nonneg A.le, smul_zero]
        refine congrArg (ball (0 : E)) ?_
        dsimp [D]
        field }

end ExistsContDiffBumpBase

end
