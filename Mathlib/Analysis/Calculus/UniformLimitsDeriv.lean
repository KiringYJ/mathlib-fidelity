/-
Copyright (c) 2022 Kevin H. Wilson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin H. Wilson
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Normed.Module.RCLike.Basic
public import Mathlib.Order.Filter.Curry
public import Mathlib.Tactic.ModuleNF

/-!
# Swapping limits and derivatives via uniform convergence

The purpose of this file is to prove that the derivative of the pointwise limit of a sequence of
functions is the pointwise limit of the functions' derivatives when the derivatives converge
_uniformly_. The formal statement appears as `hasFDerivAt_of_tendstoLocallyUniformlyOn`.

## Main statements

* `uniformCauchySeqOnFilter_of_fderiv`: If
    1. `f : ℕ → E → G` is a sequence of functions which have derivatives
       `f' : ℕ → E → (E →L[𝕜] G)` on a neighborhood of `x`,
    2. the functions `f` converge at `x`, and
    3. the derivatives `f'` form a Cauchy sequence uniformly on a neighborhood of `x`,
  then the `f` form a Cauchy sequence _uniformly_ on a neighborhood of `x`
* `hasFDerivAt_of_tendstoUniformlyOnFilter` : Suppose (1), (2), and (3) above are true. Let
  `g` (resp. `g'`) be the limiting function of the `f` (resp. `g'`). Then `f'` is the derivative of
  `g` on a neighborhood of `x`
* `hasFDerivAt_of_tendstoUniformlyOn`: An often-easier-to-use version of the above theorem when
  *all* the derivatives exist and functions converge on a common open set and the derivatives
  converge uniformly there.

Each of the above statements also has variations that support `deriv` instead of `fderiv`.

## Implementation notes

Our technique for proving the main result is the famous "`ε / 3` proof." In words, you can find it
explained, for instance, at [this StackExchange post](https://math.stackexchange.com/questions/214218/uniform-convergence-of-derivatives-tao-14-2-7).
The subtlety is that we want to prove that the difference quotients of `g` converge to `g'`.
The quotients are taken at points distinct from the base point. Let `L` be the pullback of
`𝓝 x` along the inclusion of those points. We want to prove something like:

```
∀ ε > 0, ∃ δ > 0, ∀ y ∈ B_δ(x) ∖ {x}, |y - x|⁻¹ * |(g y - g x) - g' x (y - x)| < ε.
```

To do so, we will need to introduce a pair of quantifiers

```lean
∀ ε > 0, ∃ N, ∀ n ≥ N, ∃ δ > 0, ∀ y ∈ B_δ(x) ∖ {x},
  |y - x|⁻¹ * |(g y - g x) - g' x (y - x)| < ε.
```

So how do we write this in terms of filters? Well, the initial definition of the derivative is

```lean
tendsto (|y - x|⁻¹ * |(g y - g x) - g' x (y - x)|) L (𝓝 0)
```

There are two ways we might introduce `n`. We could do:

```lean
∀ᶠ (n : ℕ) in atTop, Tendsto (|y - x|⁻¹ * |(g y - g x) - g' x (y - x)|) L (𝓝 0)
```

but this is equivalent to the quantifier order `∃ N, ∀ n ≥ N, ∀ ε > 0, ∃ δ > 0, ∀ y ∈ B_δ(x)`,
which _implies_ our desired `∀ ∃ ∀ ∃ ∀` but is _not_ equivalent to it. On the other hand, we might
try

```lean
Tendsto (|y - x|⁻¹ * |(g y - g x) - g' x (y - x)|) (atTop ×ˢ L) (𝓝 0)
```

but this is equivalent to the quantifier order `∀ ε > 0, ∃ N, ∃ δ > 0, ∀ n ≥ N, ∀ y ∈ B_δ(x)`, which
again _implies_ our desired `∀ ∃ ∀ ∃ ∀` but is not equivalent to it.

So to get the quantifier order we want, we need to introduce a new filter construction, which we
call a "curried filter"

```lean
Tendsto (|y - x|⁻¹ * |(g y - g x) - g' x (y - x)|) (atTop.curry L) (𝓝 0)
```

Then the above implications are `Filter.Tendsto.curry` and
`Filter.Tendsto.mono_left Filter.curry_le_prod`. We will use both of these deductions as part of
our proof.

We note that if you loosen the assumptions of the main theorem then the proof becomes quite a bit
easier. In particular, if you assume there is a common neighborhood `s` where all of the three
assumptions of `hasFDerivAt_of_tendstoUniformlyOnFilter` hold and that the `f'` are
continuous, then you can avoid the mean value theorem and much of the work around curried filters.

## Tags

uniform convergence, limits of derivatives
-/

public section


open Filter

open scoped uniformity Filter Topology

section LimitsOfDerivatives

variable {ι : Type*} {l : Filter ι} {E : Type*} [NormedAddCommGroup E] {𝕜 : Type*}
  [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
  [NormedSpace 𝕜 E] {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] {f : ι → E → G}
  {g : E → G} {f' : ι → E → E →L[𝕜] G} {g' : E → E →L[𝕜] G} {x : E}

/-- If a sequence of functions real or complex functions are eventually differentiable on a
neighborhood of `x`, they are Cauchy _at_ `x`, and their derivatives
are a uniform Cauchy sequence in a neighborhood of `x`, then the functions form a uniform Cauchy
sequence in a neighborhood of `x`. -/
theorem uniformCauchySeqOnFilter_of_fderiv (hf' : UniformCauchySeqOnFilter f' l (𝓝 x))
    (hf : ∀ᶠ n : ι × E in l ×ˢ 𝓝 x, HasFDerivAt (f n.1) (f' n.1 n.2) n.2)
    (hfg : Cauchy (map (fun n => f n x) l)) : UniformCauchySeqOnFilter f l (𝓝 x) := by
  let : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 _
  rw [SeminormedAddGroup.uniformCauchySeqOnFilter_iff_tendstoUniformlyOnFilter_zero] at hf' ⊢
  suffices
    TendstoUniformlyOnFilter (fun (n : ι × ι) (z : E) => f n.1 z - f n.2 z - (f n.1 x - f n.2 x)) 0
        (l ×ˢ l) (𝓝 x) ∧
      TendstoUniformlyOnFilter (fun (n : ι × ι) (_ : E) => f n.1 x - f n.2 x) 0 (l ×ˢ l) (𝓝 x) by
    have := this.1.neg.add this.2.neg
    rw [neg_zero, add_zero] at this
    apply this.congr (.of_forall (fun x ↦ by simp; abel))
  constructor
  · -- This inequality follows from the mean value theorem. To apply it, we will need to shrink our
    -- neighborhood to small enough ball
    rw [Metric.tendstoUniformlyOnFilter_iff] at hf' ⊢
    intro ε hε
    have := (tendsto_swap4_prod.eventually (hf.prod_mk hf)).diag_of_prod_right
    obtain ⟨a, b, c, d, e⟩ := eventually_prod_iff.1 ((hf' ε hε).and this)
    obtain ⟨R, hR, hR'⟩ := Metric.nhds_basis_ball.eventually_iff.mp d
    let r := min 1 R
    have hr : 0 < r := by simp [r, hR]
    have hr' : ∀ ⦃y : E⦄, y ∈ Metric.ball x r → c y := fun y hy =>
      hR' (lt_of_lt_of_le (Metric.mem_ball.mp hy) (min_le_right _ _))
    have hxy : ∀ y : E, y ∈ Metric.ball x r → ‖y - x‖ < 1 := by
      intro y hy
      rw [Metric.mem_ball, dist_eq_norm] at hy
      exact lt_of_lt_of_le hy (min_le_left _ _)
    have hxyε : ∀ y : E, y ∈ Metric.ball x r → ε * ‖y - x‖ < ε := by
      intro y hy
      exact (mul_lt_iff_lt_one_right hε.lt).mpr (hxy y hy)
    -- With a small ball in hand, apply the mean value theorem
    refine
      eventually_prod_iff.mpr
        ⟨_, b, (· ∈ Metric.ball x r),
          eventually_mem_set.mpr (Metric.nhds_basis_ball.mem_of_mem hr), fun {n} hn {y} hy => ?_⟩
    simp only [Pi.zero_apply, dist_zero_left, norm_neg_add] at e ⊢
    refine lt_of_le_of_lt ?_ (hxyε y hy)
    exact
      Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
        (fun y hy => ((e hn (hr' hy)).2.1.sub (e hn (hr' hy)).2.2).hasFDerivWithinAt)
        (fun y hy => (e hn (hr' hy)).1.le) (convex_ball x r) (Metric.mem_ball_self hr) hy
  · -- This is just `hfg` run through `eventually_prod_iff`
    refine Metric.tendstoUniformlyOnFilter_iff.mpr fun ε hε => ?_
    obtain ⟨t, ht, ht'⟩ := (Metric.cauchy_iff.mp hfg).2 ε hε
    exact
      eventually_prod_iff.mpr
        ⟨fun n : ι × ι => f n.1 x ∈ t ∧ f n.2 x ∈ t,
          eventually_prod_iff.mpr ⟨_, ht, _, ht, fun {n} hn {n'} hn' => ⟨hn, hn'⟩⟩,
          fun _ => True,
          by simp,
          fun {n} hn {y} _ => by simpa [norm_sub_rev, dist_eq_norm] using ht' _ hn.1 _ hn.2⟩

/-- A variant of the second fundamental theorem of calculus (FTC-2): If a sequence of functions
between real or complex normed spaces are differentiable on a ball centered at `x`, they
form a Cauchy sequence _at_ `x`, and their derivatives are Cauchy uniformly on the ball, then the
functions form a uniform Cauchy sequence on the ball.

NOTE: The fact that we work on a ball is typically all that is necessary to work with power series
and Dirichlet series (our primary use case). However, this can be generalized by replacing the ball
with any connected, bounded, open set and replacing uniform convergence with local uniform
convergence. See `cauchy_map_of_uniformCauchySeqOn_fderiv`.
-/
theorem uniformCauchySeqOn_ball_of_fderiv {r : ℝ} (hf' : UniformCauchySeqOn f' l (Metric.ball x r))
    (hf : ∀ n : ι, ∀ y : E, y ∈ Metric.ball x r → HasFDerivAt (f n) (f' n y) y)
    (hfg : Cauchy (map (fun n => f n x) l)) : UniformCauchySeqOn f l (Metric.ball x r) := by
  let : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 _
  have : NeBot l := (cauchy_map_iff.1 hfg).1
  rcases le_or_gt r 0 with (hr | hr)
  · simp only [Metric.ball_eq_empty.2 hr, UniformCauchySeqOn, Set.mem_empty_iff_false,
      IsEmpty.forall_iff, eventually_const, imp_true_iff]
  rw [SeminormedAddGroup.uniformCauchySeqOn_iff_tendstoUniformlyOn_zero] at hf' ⊢
  suffices
    TendstoUniformlyOn (fun (n : ι × ι) (z : E) => f n.1 z - f n.2 z - (f n.1 x - f n.2 x)) 0
        (l ×ˢ l) (Metric.ball x r) ∧
      TendstoUniformlyOn (fun (n : ι × ι) (_ : E) => f n.1 x - f n.2 x) 0
        (l ×ˢ l) (Metric.ball x r) by
    have := this.1.neg.add this.2.neg
    rw [neg_zero, add_zero] at this
    refine this.congr ?_
    filter_upwards with n z _ using (by simp; abel)
  constructor
  · -- This inequality follows from the mean value theorem
    rw [Metric.tendstoUniformlyOn_iff] at hf' ⊢
    intro ε hε
    obtain ⟨q, hqpos, hq⟩ : ∃ q : ℝ, 0 < q ∧ q * r < ε := by
      simp_rw [mul_comm]
      exact exists_pos_mul_lt hε.lt r
    apply (hf' q hqpos.gt).mono
    intro n hn y hy
    simp_rw [dist_eq_norm, Pi.zero_apply, zero_sub, norm_neg, norm_neg_add] at hn ⊢
    have mvt :=
      Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
        (fun z hz => ((hf n.1 z hz).sub (hf n.2 z hz)).hasFDerivWithinAt) (fun z hz => (hn z hz).le)
        (convex_ball x r) (Metric.mem_ball_self hr) hy
    refine lt_of_le_of_lt mvt ?_
    have : q * ‖y - x‖ < q * r :=
      mul_lt_mul' rfl.le (by simpa only [dist_eq_norm] using Metric.mem_ball.mp hy) (norm_nonneg _)
        hqpos
    exact this.trans hq
  · -- This is just `hfg` run through `eventually_prod_iff`
    refine Metric.tendstoUniformlyOn_iff.mpr fun ε hε => ?_
    obtain ⟨t, ht, ht'⟩ := (Metric.cauchy_iff.mp hfg).2 ε hε
    rw [eventually_prod_iff]
    refine ⟨fun n => f n x ∈ t, ht, fun n => f n x ∈ t, ht, ?_⟩
    intro n hn n' hn' z _
    rw [dist_eq_norm, Pi.zero_apply, zero_sub, norm_neg, ← dist_eq_norm]
    exact ht' _ hn _ hn'

/-- If a sequence of functions between real or complex normed spaces are differentiable on a
preconnected open set, they form a Cauchy sequence _at_ `x`, and their derivatives are Cauchy
uniformly on the set, then the functions form a Cauchy sequence at any point in the set. -/
theorem cauchy_map_of_uniformCauchySeqOn_fderiv {s : Set E} (hs : IsOpen s) (h's : IsPreconnected s)
    (hf' : UniformCauchySeqOn f' l s) (hf : ∀ n : ι, ∀ y : E, y ∈ s → HasFDerivAt (f n) (f' n y) y)
    {x₀ x : E} (hx₀ : x₀ ∈ s) (hx : x ∈ s) (hfg : Cauchy (map (fun n => f n x₀) l)) :
    Cauchy (map (fun n => f n x) l) := by
  have : NeBot l := (cauchy_map_iff.1 hfg).1
  let t := { y | y ∈ s ∧ Cauchy (map (fun n => f n y) l) }
  suffices H : s ⊆ t from (H hx).2
  have A : ∀ x ε, x ∈ t → Metric.ball x ε ⊆ s → Metric.ball x ε ⊆ t := fun x ε xt hx y hy =>
    ⟨hx hy,
      (uniformCauchySeqOn_ball_of_fderiv (hf'.mono hx) (fun n y hy => hf n y (hx hy))
            xt.2).cauchy_map
        hy⟩
  have open_t : IsOpen t := by
    rw [Metric.isOpen_iff]
    intro x hx
    rcases Metric.isOpen_iff.1 hs x hx.1 with ⟨ε, εpos, hε⟩
    exact ⟨ε, εpos, A x ε hx hε⟩
  have st_nonempty : (s ∩ t).Nonempty := ⟨x₀, hx₀, ⟨hx₀, hfg⟩⟩
  suffices H : closure t ∩ s ⊆ t from h's.subset_of_closure_inter_subset open_t st_nonempty H
  rintro x ⟨xt, xs⟩
  obtain ⟨ε, εpos, hε⟩ : ∃ (ε : ℝ), ε > 0 ∧ Metric.ball x ε ⊆ s := Metric.isOpen_iff.1 hs x xs
  obtain ⟨y, yt, hxy⟩ : ∃ (y : E), y ∈ t ∧ dist x y < ε / 2 :=
    Metric.mem_closure_iff.1 xt _ (half_pos εpos)
  have B : Metric.ball y (ε / 2) ⊆ Metric.ball x ε := by
    apply Metric.ball_subset_ball'; rw [dist_comm]; linarith
  exact A y (ε / 2) yt (B.trans hε) (Metric.mem_ball.2 hxy)

/-- If `f_n → g` pointwise and the derivatives `(f_n)' → h` _uniformly_ converge, then
in fact for a fixed `y`, the difference quotients `‖z - y‖⁻¹ • (f_n z - f_n y)` converge
_uniformly_ to `‖z - y‖⁻¹ • (g z - g y)` on the subtype of points distinct from `y`. -/
theorem difference_quotients_converge_uniformly
    {E : Type*} [NormedAddCommGroup E] {𝕜 : Type*} [RCLike 𝕜]
    [NormedSpace 𝕜 E] {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G] {f : ι → E → G}
    {g : E → G} {f' : ι → E → E →L[𝕜] G} {g' : E → E →L[𝕜] G} {x : E}
    (hf' : TendstoUniformlyOnFilter f' g' l (𝓝 x))
    (hf : ∀ᶠ n : ι × E in l ×ˢ 𝓝 x, HasFDerivAt (f n.1) (f' n.1 n.2) n.2)
    (hfg : ∀ᶠ y : E in 𝓝 x, Tendsto (fun n => f n y) l (𝓝 (g y))) :
    TendstoUniformlyOnFilter
      (fun (n : ι) (y : {y : E // y - x ≠ 0}) ↦
        ((Checked.inv ‖(y : E) - x‖ (norm_ne_zero_iff.mpr y.property).isUnit : ℝ) : 𝕜) •
          (f n y - f n x))
      (fun y : {y : E // y - x ≠ 0} ↦
        ((Checked.inv ‖(y : E) - x‖ (norm_ne_zero_iff.mpr y.property).isUnit : ℝ) : 𝕜) •
          (g y - g x)) l (comap Subtype.val (𝓝 x)) := by
  let D := {y : E // y - x ≠ 0}
  let k : Filter D := comap Subtype.val (𝓝 x)
  let q (y : D) : ℝ := Checked.inv ‖(y : E) - x‖ (norm_ne_zero_iff.mpr y.property).isUnit
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 _
  have hv : Tendsto (Subtype.val : D → E) k (𝓝 x) := tendsto_comap
  change TendstoUniformlyOnFilter (fun n (y : D) ↦ (q y : 𝕜) • (f n y - f n x))
    (fun y : D ↦ (q y : 𝕜) • (g y - g x)) l k
  rcases eq_or_ne k ⊥ with hk | hk
  · rw [hk, Metric.tendstoUniformlyOnFilter_iff]
    simp
  let : k.NeBot := ⟨hk⟩
  refine UniformCauchySeqOnFilter.tendstoUniformlyOnFilter_of_tendsto ?_
    (((hv.eventually hfg).and (eventually_const.mpr hfg.self_of_nhds)).mono fun y hy ↦
      (hy.1.sub hy.2).const_smul (q y : 𝕜))
  rw [SeminormedAddGroup.uniformCauchySeqOnFilter_iff_tendstoUniformlyOnFilter_zero]
  rw [Metric.tendstoUniformlyOnFilter_iff]
  have hfg' := hf'.uniformCauchySeqOnFilter
  rw [SeminormedAddGroup.uniformCauchySeqOnFilter_iff_tendstoUniformlyOnFilter_zero] at hfg'
  rw [Metric.tendstoUniformlyOnFilter_iff] at hfg'
  intro ε hε
  obtain ⟨u, hupos, huε⟩ := exists_pos_rat_lt hε
  specialize hfg' (u : ℝ) (by simp [hupos])
  have hpair := (tendsto_swap4_prod.eventually (hf.prod_mk hf)).diag_of_prod_right
  obtain ⟨a, b, c, d, e⟩ := eventually_prod_iff.1 (hfg'.and hpair)
  obtain ⟨r, hr, hr'⟩ := Metric.nhds_basis_ball.eventually_iff.mp d
  rw [eventually_prod_iff]
  refine ⟨a, b, (fun y : D ↦ (y : E) ∈ Metric.ball x r),
    hv.eventually (eventually_mem_set.mpr (Metric.nhds_basis_ball.mem_of_mem hr)), ?_⟩
  intro n hn y hy
  have hyz : 0 < ‖(y : E) - x‖ := norm_pos_iff.mpr y.property
  have hqnorm : ‖(q y : 𝕜)‖ = ‖(y : E) - x‖⁻¹ :=
    (@RCLike.norm_ofReal 𝕜 _ (q y)).trans (abs_of_nonneg (inv_nonneg.mpr hyz.le))
  simp only [Pi.zero_apply, dist_zero_left]
  rw [norm_neg_add, ← smul_sub, norm_smul, hqnorm]
  refine lt_of_le_of_lt ?_ huε
  rw [inv_mul_le_iff₀ hyz, mul_comm, sub_sub_sub_comm]
  simp only [Pi.zero_apply, dist_zero_left, norm_neg_add] at e
  exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z hz ↦ ((e hn (hr' hz)).2.1.sub (e hn (hr' hz)).2.2).hasFDerivWithinAt)
    (fun z hz ↦ (e hn (hr' hz)).1.le) (convex_ball x r) (Metric.mem_ball_self hr) hy

/-- `(d/dx) lim_{n → ∞} f n x = lim_{n → ∞} f' n x` when the `f' n` converge
_uniformly_ to their limit at `x`.

In words the assumptions mean the following:
  * `hf'`: The `f'` converge "uniformly at" `x` to `g'`. This does not mean that the `f' n` even
    converge away from `x`!
  * `hf`: For all `(y, n)` with `y` sufficiently close to `x` and `n` sufficiently large, `f' n` is
    the derivative of `f n`
  * `hfg`: The `f n` converge pointwise to `g` on a neighborhood of `x` -/
theorem hasFDerivAt_of_tendstoUniformlyOnFilter [NeBot l]
    (hf' : TendstoUniformlyOnFilter f' g' l (𝓝 x))
    (hf : ∀ᶠ n : ι × E in l ×ˢ 𝓝 x, HasFDerivAt (f n.1) (f' n.1 n.2) n.2)
    (hfg : ∀ᶠ y in 𝓝 x, Tendsto (fun n => f n y) l (𝓝 (g y))) : HasFDerivAt g (g' x) x := by
  let : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  let D := {y : E // y - x ≠ 0}
  let k : Filter D := comap Subtype.val (𝓝 x)
  let q (y : D) : ℝ := Checked.inv ‖(y : E) - x‖ (norm_ne_zero_iff.mpr y.property).isUnit
  have hpos (y : D) : 0 < ‖(y : E) - x‖ := norm_pos_iff.mpr y.property
  have hq (y : D) (v : G) : ‖(q y : 𝕜) • v‖ = ‖v‖ / ‖(y : E) - x‖ := by
    rw [norm_smul, RCLike.norm_ofReal, div_eq_inv_mul₀]
    exact congrArg (fun t : ℝ ↦ t * ‖v‖) (abs_of_nonneg (inv_nonneg.mpr (hpos y).le))
  apply (hasFDerivAt_iff_tendsto (coord := @id E)).mpr
  change Tendsto (fun y : D ↦ ‖g y - g x - (g' x) (y.val - x)‖ / ‖y.val - x‖) k (𝓝 0)
  suffices h : Tendsto (fun a : ι × D ↦ (q a.2 : 𝕜) •
      (g a.2 - g x - (g' x) (a.2.val - x))) (l.curry k) (𝓝 0) by
    rw [Metric.tendsto_nhds] at h ⊢
    intro ε hε
    have hε' := h ε hε
    rw [eventually_curry_iff] at hε'
    simp only at hε'
    have hk : ∀ᶠ y : D in k, dist ((q y : 𝕜) • (g y - g x - (g' x) (y.val - x))) 0 < ε :=
      eventually_const.mp hε'
    refine hk.mono fun y hy ↦ ?_
    rw [dist_zero_right, hq] at hy
    rw [dist_zero_right, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (norm_nonneg _) (norm_nonneg _))]
    exact hy
  -- Split the error into the approximation of the difference, the differentiation error of
  -- an approximating function, and the variation of the limiting derivative.
  have hsum :
      (fun a : ι × D ↦ (q a.2 : 𝕜) • (g a.2 - g x - (g' x) (a.2.val - x))) =
        ((fun a : ι × D ↦ (q a.2 : 𝕜) • (g a.2 - g x - (f a.1 a.2 - f a.1 x))) +
          (fun a : ι × D ↦ (q a.2 : 𝕜) •
            (f a.1 a.2 - f a.1 x - ((f' a.1 x) a.2 - (f' a.1 x) x)))) +
        (fun a : ι × D ↦ (q a.2 : 𝕜) • (f' a.1 x - g' x) (a.2.val - x)) := by
    ext a
    simp only [Pi.add_apply]
    rw [← smul_add, ← smul_add]
    congr
    simp only [map_sub, sub_add_sub_cancel, FunLike.coe_sub, Pi.sub_apply]
    abel
  rw [hsum, show 𝓝 (0 : G) = 𝓝 (0 + 0 + 0) by simp only [add_zero]]
  refine Tendsto.add (Tendsto.add ?_ ?_) ?_
  · have hu := difference_quotients_converge_uniformly hf' hf hfg
    change TendstoUniformlyOnFilter (fun n (y : D) ↦ (q y : 𝕜) • (f n y - f n x))
      (fun y : D ↦ (q y : 𝕜) • (g y - g x)) l k at hu
    rw [Metric.tendstoUniformlyOnFilter_iff] at hu
    rw [Metric.tendsto_nhds]
    intro ε hε
    apply ((hu ε hε).filter_mono curry_le_prod).mono
    intro n hn
    rw [dist_eq_norm] at hn ⊢
    module_nf at hn ⊢
    exact hn
  · rw [Metric.tendsto_nhds]
    intro ε hε
    rw [eventually_curry_iff]
    refine hf.curry.mono fun n hn ↦ ?_
    have hd := (hasFDerivAt_iff_tendsto (coord := @id E)).mp hn.self_of_nhds
    rw [Metric.tendsto_nhds] at hd
    refine (hd ε hε).mono fun y hy ↦ ?_
    rw [dist_zero_right, hq, ← map_sub]
    rw [dist_zero_right, Real.norm_eq_abs] at hy
    exact (le_abs_self _).trans_lt hy
  · refine Tendsto.mono_left ?_ curry_le_prod
    have h1 : Tendsto (fun n : ι × E ↦ g' n.2 - f' n.1 n.2) (l ×ˢ 𝓝 x) (𝓝 0) := by
      rw [Metric.tendstoUniformlyOnFilter_iff] at hf'
      exact Metric.tendsto_nhds.mpr fun ε hε ↦ by simpa [dist_eq_norm] using hf' ε hε
    have h2 : Tendsto (fun n : ι ↦ g' x - f' n x) l (𝓝 0) := by
      rw [Metric.tendsto_nhds] at h1 ⊢
      exact fun ε hε ↦ (h1 ε hε).curry.mono fun n hn ↦ hn.self_of_nhds
    refine squeeze_zero_norm ?_ (tendsto_zero_iff_norm_tendsto_zero.mp (h2.comp tendsto_fst))
    intro n
    rw [hq, div_le_iff₀ (hpos n.2), Function.comp_apply, norm_sub_rev (g' x) (f' n.1 x)]
    exact (f' n.1 x - g' x).le_opNorm (n.2.val - x)

theorem hasFDerivAt_of_tendstoLocallyUniformlyOn [NeBot l] {s : Set E} (hs : IsOpen s)
    (hf' : TendstoLocallyUniformlyOn f' g' l s) (hf : ∀ n, ∀ x ∈ s, HasFDerivAt (f n) (f' n x) x)
    (hfg : ∀ x ∈ s, Tendsto (fun n => f n x) l (𝓝 (g x))) (hx : x ∈ s) :
    HasFDerivAt g (g' x) x := by
  have h1 : s ∈ 𝓝 x := hs.mem_nhds hx
  have h3 : Set.univ ×ˢ s ∈ l ×ˢ 𝓝 x := by simp only [h1, prod_mem_prod_iff, univ_mem, and_self_iff]
  have h4 : ∀ᶠ n : ι × E in l ×ˢ 𝓝 x, HasFDerivAt (f n.1) (f' n.1 n.2) n.2 :=
    eventually_of_mem h3 fun ⟨n, z⟩ ⟨_, hz⟩ => hf n z hz
  refine hasFDerivAt_of_tendstoUniformlyOnFilter ?_ h4 (eventually_of_mem h1 hfg)
  simpa [IsOpen.nhdsWithin_eq hs hx] using tendstoLocallyUniformlyOn_iff_filter.mp hf' x hx

/-- A slight variant of `hasFDerivAt_of_tendstoLocallyUniformlyOn` with the assumption stated
in terms of `DifferentiableOn` rather than `HasFDerivAt`. This makes a few proofs nicer in
complex analysis where holomorphicity is assumed but the derivative is not known a priori. -/
theorem hasFDerivAt_of_tendsto_locally_uniformly_on' [NeBot l] {s : Set E} (hs : IsOpen s)
    (hf' : TendstoLocallyUniformlyOn (fderiv 𝕜 ∘ f) g' l s) (hf : ∀ n, DifferentiableOn 𝕜 (f n) s)
    (hfg : ∀ x ∈ s, Tendsto (fun n => f n x) l (𝓝 (g x))) (hx : x ∈ s) :
    HasFDerivAt g (g' x) x := by
  refine hasFDerivAt_of_tendstoLocallyUniformlyOn hs hf' (fun n z hz => ?_) hfg hx
  exact ((hf n z hz).differentiableAt (hs.mem_nhds hz)).hasFDerivAt

/-- `(d/dx) lim_{n → ∞} f n x = lim_{n → ∞} f' n x` when the `f' n` converge
_uniformly_ to their limit on an open set containing `x`. -/
theorem hasFDerivAt_of_tendstoUniformlyOn [NeBot l] {s : Set E} (hs : IsOpen s)
    (hf' : TendstoUniformlyOn f' g' l s)
    (hf : ∀ n : ι, ∀ x : E, x ∈ s → HasFDerivAt (f n) (f' n x) x)
    (hfg : ∀ x : E, x ∈ s → Tendsto (fun n => f n x) l (𝓝 (g x))) (hx : x ∈ s) :
    HasFDerivAt g (g' x) x :=
  hasFDerivAt_of_tendstoLocallyUniformlyOn hs hf'.tendstoLocallyUniformlyOn hf hfg hx

/-- `(d/dx) lim_{n → ∞} f n x = lim_{n → ∞} f' n x` when the `f' n` converge
_uniformly_ to their limit. -/
theorem hasFDerivAt_of_tendstoUniformly [NeBot l] (hf' : TendstoUniformly f' g' l)
    (hf : ∀ n : ι, ∀ x : E, HasFDerivAt (f n) (f' n x) x)
    (hfg : ∀ x : E, Tendsto (fun n => f n x) l (𝓝 (g x))) (x : E) : HasFDerivAt g (g' x) x := by
  have hf : ∀ n : ι, ∀ x : E, x ∈ Set.univ → HasFDerivAt (f n) (f' n x) x := by simp [hf]
  have hfg : ∀ x : E, x ∈ Set.univ → Tendsto (fun n => f n x) l (𝓝 (g x)) := by simp [hfg]
  have hf' : TendstoUniformlyOn f' g' l Set.univ := by rwa [tendstoUniformlyOn_univ]
  exact hasFDerivAt_of_tendstoUniformlyOn isOpen_univ hf' hf hfg (Set.mem_univ x)

end LimitsOfDerivatives

section deriv

/-! ### `deriv` versions of above theorems

In this section, we provide `deriv` equivalents of the `fderiv` lemmas in the previous section.
-/


variable {ι : Type*} {l : Filter ι} {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {G : Type*} [NormedAddCommGroup G]
  [NormedSpace 𝕜 G] {f : ι → 𝕜 → G} {g : 𝕜 → G} {f' : ι → 𝕜 → G} {g' : 𝕜 → G} {x : 𝕜}

/-- If our derivatives converge uniformly, then the Fréchet derivatives converge uniformly -/
theorem UniformCauchySeqOnFilter.one_smulRight {l' : Filter 𝕜}
    (hf' : UniformCauchySeqOnFilter f' l l') :
    UniformCauchySeqOnFilter (fun n => fun z => (1 : 𝕜 →L[𝕜] 𝕜).smulRight (f' n z)) l l' := by
  intro u hu
  simpa using hf' _ ((ContinuousLinearMap.smulRightL 𝕜 𝕜 G 1).uniformContinuous hu)

variable [IsRCLikeNormedField 𝕜]

theorem uniformCauchySeqOnFilter_of_deriv (hf' : UniformCauchySeqOnFilter f' l (𝓝 x))
    (hf : ∀ᶠ n : ι × 𝕜 in l ×ˢ 𝓝 x, HasDerivAt (f n.1) (f' n.1 n.2) n.2)
    (hfg : Cauchy (map (fun n => f n x) l)) : UniformCauchySeqOnFilter f l (𝓝 x) := by
  simp_rw [hasDerivAt_iff_hasFDerivAt] at hf
  exact uniformCauchySeqOnFilter_of_fderiv hf'.one_smulRight hf hfg

theorem uniformCauchySeqOn_ball_of_deriv {r : ℝ} (hf' : UniformCauchySeqOn f' l (Metric.ball x r))
    (hf : ∀ n : ι, ∀ y : 𝕜, y ∈ Metric.ball x r → HasDerivAt (f n) (f' n y) y)
    (hfg : Cauchy (map (fun n => f n x) l)) : UniformCauchySeqOn f l (Metric.ball x r) := by
  simp_rw [hasDerivAt_iff_hasFDerivAt] at hf
  have hf' :
    UniformCauchySeqOn (fun n => fun z => (1 : 𝕜 →L[𝕜] 𝕜).smulRight (f' n z)) l
      (Metric.ball x r) :=
    (ContinuousLinearMap.smulRightL 𝕜 𝕜 G 1).uniformContinuous.comp_uniformCauchySeqOn hf'
  exact uniformCauchySeqOn_ball_of_fderiv hf' hf hfg

theorem hasDerivAt_of_tendstoUniformlyOnFilter [NeBot l]
    (hf' : TendstoUniformlyOnFilter f' g' l (𝓝 x))
    (hf : ∀ᶠ n : ι × 𝕜 in l ×ˢ 𝓝 x, HasDerivAt (f n.1) (f' n.1 n.2) n.2)
    (hfg : ∀ᶠ y in 𝓝 x, Tendsto (fun n => f n y) l (𝓝 (g y))) : HasDerivAt g (g' x) x := by
  -- The first part of the proof rewrites `hf` and the goal to be functions so that Lean
  -- can recognize them when we apply `hasFDerivAt_of_tendstoUniformlyOnFilter`
  let F' n z := (1 : 𝕜 →L[𝕜] 𝕜).smulRight (f' n z)
  let G' z := (1 : 𝕜 →L[𝕜] 𝕜).smulRight (g' z)
  simp_rw [hasDerivAt_iff_hasFDerivAt] at hf ⊢
  have hf' : TendstoUniformlyOnFilter F' G' l (𝓝 x) :=
    (ContinuousLinearMap.smulRightL 𝕜 𝕜 G 1).uniformContinuous.comp_tendstoUniformlyOnFilter hf'
  exact hasFDerivAt_of_tendstoUniformlyOnFilter hf' hf hfg

theorem hasDerivAt_of_tendstoLocallyUniformlyOn [NeBot l] {s : Set 𝕜} (hs : IsOpen s)
    (hf' : TendstoLocallyUniformlyOn f' g' l s)
    (hf : ∀ᶠ n in l, ∀ x ∈ s, HasDerivAt (f n) (f' n x) x)
    (hfg : ∀ x ∈ s, Tendsto (fun n => f n x) l (𝓝 (g x))) (hx : x ∈ s) : HasDerivAt g (g' x) x := by
  have h1 : s ∈ 𝓝 x := hs.mem_nhds hx
  have h2 : ∀ᶠ n : ι × 𝕜 in l ×ˢ 𝓝 x, HasDerivAt (f n.1) (f' n.1 n.2) n.2 :=
    eventually_prod_iff.2 ⟨_, hf, fun x => x ∈ s, h1, fun {n} => id⟩
  refine hasDerivAt_of_tendstoUniformlyOnFilter ?_ h2 (eventually_of_mem h1 hfg)
  simpa [IsOpen.nhdsWithin_eq hs hx] using tendstoLocallyUniformlyOn_iff_filter.mp hf' x hx

/-- A slight variant of `hasDerivAt_of_tendstoLocallyUniformlyOn` with the assumption stated in
terms of `DifferentiableOn` rather than `HasDerivAt`. This makes a few proofs nicer in complex
analysis where holomorphicity is assumed but the derivative is not known a priori. -/
theorem hasDerivAt_of_tendsto_locally_uniformly_on' [NeBot l] {s : Set 𝕜} (hs : IsOpen s)
    (hf' : TendstoLocallyUniformlyOn (deriv ∘ f) g' l s)
    (hf : ∀ᶠ n in l, DifferentiableOn 𝕜 (f n) s)
    (hfg : ∀ x ∈ s, Tendsto (fun n => f n x) l (𝓝 (g x))) (hx : x ∈ s) : HasDerivAt g (g' x) x := by
  refine hasDerivAt_of_tendstoLocallyUniformlyOn hs hf' ?_ hfg hx
  filter_upwards [hf] with n h z hz using ((h z hz).differentiableAt (hs.mem_nhds hz)).hasDerivAt

theorem hasDerivAt_of_tendstoUniformlyOn [NeBot l] {s : Set 𝕜} (hs : IsOpen s)
    (hf' : TendstoUniformlyOn f' g' l s)
    (hf : ∀ᶠ n in l, ∀ x : 𝕜, x ∈ s → HasDerivAt (f n) (f' n x) x)
    (hfg : ∀ x : 𝕜, x ∈ s → Tendsto (fun n => f n x) l (𝓝 (g x))) (hx : x ∈ s) :
    HasDerivAt g (g' x) x :=
  hasDerivAt_of_tendstoLocallyUniformlyOn hs hf'.tendstoLocallyUniformlyOn hf hfg hx

theorem hasDerivAt_of_tendstoUniformly [NeBot l] (hf' : TendstoUniformly f' g' l)
    (hf : ∀ᶠ n in l, ∀ x : 𝕜, HasDerivAt (f n) (f' n x) x)
    (hfg : ∀ x : 𝕜, Tendsto (fun n => f n x) l (𝓝 (g x))) (x : 𝕜) : HasDerivAt g (g' x) x := by
  have hf : ∀ᶠ n in l, ∀ x : 𝕜, x ∈ Set.univ → HasDerivAt (f n) (f' n x) x := by
    filter_upwards [hf] with n h x _ using h x
  have hfg : ∀ x : 𝕜, x ∈ Set.univ → Tendsto (fun n => f n x) l (𝓝 (g x)) := by simp [hfg]
  have hf' : TendstoUniformlyOn f' g' l Set.univ := by rwa [tendstoUniformlyOn_univ]
  exact hasDerivAt_of_tendstoUniformlyOn isOpen_univ hf' hf hfg (Set.mem_univ x)

end deriv
