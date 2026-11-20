/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Topology.Algebra.InfiniteSum.UniformOn

/-!
# Differentiability of sum of functions

We prove some `HasSumUniformlyOn` versions of theorems from
`Mathlib.Analysis.NormedSpace.FunctionSeries`.

Alongside this we prove `derivWithin_tsum` which states that the derivative of a series of functions
is the sum of the derivatives, under suitable conditions we also prove an `iteratedDerivWithin`
version.

-/

public section

open Set TopologicalSpace Filter

open scoped Topology NNReal

section UniformlyOn

variable {α β F : Type*} [NormedAddCommGroup F] [CompleteSpace F] {u : α → ℝ}

theorem HasSumUniformlyOn.of_norm_le_summable {f : α → β → F} (hu : Summable u) {s : Set β}
    (hfu : ∀ n x, x ∈ s → ‖f n x‖ ≤ u n) : HasSumUniformlyOn f (fun x ↦ ∑' n, f n x) s := by
  simp [hasSumUniformlyOn_iff_tendstoUniformlyOn, tendstoUniformlyOn_tsum hu hfu]

theorem HasSumUniformlyOn.of_norm_le_summable_eventually {ι : Type*} {f : ι → β → F} {u : ι → ℝ}
    (hu : Summable u) {s : Set β} (hfu : ∀ᶠ n in cofinite, ∀ x ∈ s, ‖f n x‖ ≤ u n) :
    HasSumUniformlyOn f (fun x ↦ ∑' n, f n x) s := by
  simp [hasSumUniformlyOn_iff_tendstoUniformlyOn,
    tendstoUniformlyOn_tsum_of_cofinite_eventually hu hfu]

lemma SummableLocallyUniformlyOn.of_locally_bounded_eventually [TopologicalSpace β]
    [LocallyCompactSpace β] {f : α → β → F} {s : Set β} (hs : IsOpen s)
    (hu : ∀ K ⊆ s, IsCompact K → ∃ u : α → ℝ, Summable u ∧
    ∀ᶠ n in cofinite, ∀ k ∈ K, ‖f n k‖ ≤ u n) : SummableLocallyUniformlyOn f s := by
  apply HasSumLocallyUniformlyOn.summableLocallyUniformlyOn (g := fun x ↦ ∑' n, f n x)
  rw [hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn,
    tendstoLocallyUniformlyOn_iff_forall_isCompact hs]
  intro K hK hKc
  obtain ⟨u, hu1, hu2⟩ := hu K hK hKc
  exact tendstoUniformlyOn_tsum_of_cofinite_eventually hu1 hu2

lemma SummableLocallyUniformlyOn_of_locally_bounded [TopologicalSpace β] [LocallyCompactSpace β]
    {f : α → β → F} {s : Set β} (hs : IsOpen s)
    (hu : ∀ K ⊆ s, IsCompact K → ∃ u : α → ℝ, Summable u ∧ ∀ n, ∀ k ∈ K, ‖f n k‖ ≤ u n) :
    SummableLocallyUniformlyOn f s := by
  apply SummableLocallyUniformlyOn.of_locally_bounded_eventually hs
  intro K hK hKc
  obtain ⟨u, hu1, hu2⟩ := hu K hK hKc
  exact ⟨u, hu1, by filter_upwards using hu2⟩

end UniformlyOn

variable {ι 𝕜 F : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {s : Set 𝕜}

/-- The `derivWithin` of a sum whose derivative is absolutely and uniformly convergent sum on an
open set `s` is the sum of the derivatives of sequence of functions on the open set `s` -/
theorem derivWithin_tsum {f : ι → 𝕜 → F} (hs : IsOpen s) {x : 𝕜} (hx : x ∈ s)
    (hf : ∀ y ∈ s, Summable fun n ↦ f n y)
    (h : SummableLocallyUniformlyOn (fun n ↦ (derivWithin (fun z ↦ f n z) s)) s)
    (hf2 : ∀ n r, r ∈ s → DifferentiableAt 𝕜 (f n) r) :
    derivWithin (fun z ↦ ∑' n, f n z) s x = ∑' n, derivWithin (f n) s x := by
  apply HasDerivWithinAt.derivWithin ?_ (hs.uniqueDiffWithinAt hx)
  apply HasDerivAt.hasDerivWithinAt
  apply hasDerivAt_of_tendstoLocallyUniformlyOn hs _ _ (fun y hy ↦ (hf y hy).hasSum) hx
    (f' := fun n : Finset ι ↦ fun a ↦ ∑ i ∈ n, derivWithin (fun z ↦ f i z) s a)
  · obtain ⟨g, hg⟩ := h
    apply (hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp hg).congr_right
    exact fun _ hb ↦ (hg.tsum_eqOn hb).symm
  · filter_upwards with t r hr using HasDerivAt.fun_sum
      (fun q hq ↦ ((hf2 q r hr).differentiableWithinAt.hasDerivWithinAt.hasDerivAt)
      (hs.mem_nhds hr))

/-- If a sequence of functions `fₙ` is such that `∑ fₙ (z)` is summable for each `z` in an
open set `s`, and for each `1 ≤ k ≤ m`, the series of `k`-th iterated derivatives
`∑ (iteratedDerivWithin k fₙ s) (z)`
is summable locally uniformly on `s`, and each `fₙ` is `m`-times differentiable, then the `m`-th
iterated derivative of the sum is the sum of the `m`-th iterated derivatives. -/
theorem iteratedDerivWithin_tsum {f : ι → 𝕜 → F} (m : ℕ) (hs : IsOpen s)
    {x : 𝕜} (hx : x ∈ s) (hsum : ∀ t ∈ s, Summable (fun n : ι ↦ f n t))
    (h : ∀ k, 1 ≤ k → k ≤ m → SummableLocallyUniformlyOn
      (fun n ↦ (iteratedDerivWithin k (fun z ↦ f n z) s)) s)
    (hf2 : ∀ n k r, k ≤ m → r ∈ s →
      DifferentiableAt 𝕜 (iteratedDerivWithin k (fun z ↦ f n z) s) r) :
    iteratedDerivWithin m (fun z ↦ ∑' n, f n z) s x = ∑' n, iteratedDerivWithin m (f n) s x := by
  induction m generalizing x with
  | zero => simp
  | succ m hm =>
    simp_rw [iteratedDerivWithin_succ]
    rw [← derivWithin_tsum hs hx _ _ (fun n r hr ↦ hf2 n m r (by lia) hr)]
    · exact derivWithin_congr (fun t ht ↦ hm ht (fun k hk1 hkm ↦ h k hk1 (by lia))
          (fun k r e hr he ↦ hf2 k r e (by lia) he)) (hm hx (fun k hk1 hkm ↦ h k hk1 (by lia))
          (fun k r e hr he ↦ hf2 k r e (by lia) he))
    · intro r hr
      by_cases hm2 : m = 0
      · simp [hm2, hsum r hr]
      · exact ((h m (by lia) (by lia)).summable hr).congr (fun _ ↦ by simp)
    · exact SummableLocallyUniformlyOn_congr
        (fun _ _ ht ↦ by rw [iteratedDerivWithin_succ]) (h (m + 1) (by lia) (by lia))

/-- A series on an open scalar domain has the iterated derivatives obtained by summing a family
of successive derivatives, provided the original series is pointwise summable and each
derivative series is locally uniformly summable. -/
theorem hasIteratedDerivAt_tsum_subtype {f : ℕ → ι → s → F} (hs : IsOpen s)
    (hderiv : ∀ k i x, HasDerivAt (f k i) (f (k + 1) i x) x Subtype.val)
    (hsum : ∀ x, Summable fun i ↦ f 0 i x)
    (hlocal : ∀ k, SummableLocallyUniformlyOn (f (k + 1)) (univ : Set s))
    (k : ℕ) (x : s) :
    HasIteratedDerivAt k (fun y : s ↦ ∑' i, f 0 i y) (∑' i, f k i x) x Subtype.val := by
  classical
  let g (k : ℕ) (i : ι) : 𝕜 → F := Function.extend Subtype.val (f k i) 0
  have hagree (k : ℕ) (i : ι) (y : s) : g k i y.val = f k i y :=
    Subtype.val_injective.extend_apply _ _ _
  have hsumAll (k : ℕ) (y : s) : Summable fun i ↦ f k i y := by
    cases k with
    | zero => exact hsum y
    | succ k => exact (hlocal k).summable (mem_univ y)
  have hg (k : ℕ) (i : ι) (y : s) : HasDerivAt (g k i) (g (k + 1) i y.val) y.val := by
    have hy : HasFDerivAt (fun t : s ↦ g k i t.val)
        (ContinuousLinearMap.toSpanSingleton 𝕜 (f (k + 1) i y)) y Subtype.val := by
      simpa only [hagree] using (hderiv k i y).hasFDerivAt
    rw [hagree]
    simpa only [ContinuousLinearMap.toSpanSingleton_apply, one_smul] using
      hasFDerivAt_iff_hasDerivAt.mp (hy.of_restrict (coord := id) (x := y) (hs.mem_nhds y.property))
  have hsucc (k : ℕ) (y : s) :
      HasDerivAt (fun t : s ↦ ∑' i, f k i t) (∑' i, f (k + 1) i y) y Subtype.val := by
    have hlimit : TendstoLocallyUniformlyOn
        (fun t : Finset ι ↦ fun z : 𝕜 ↦ ∑ i ∈ t, g (k + 1) i z)
        (fun z ↦ ∑' i, g (k + 1) i z) atTop s := by
      apply tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe.2
      simp only [hagree]
      obtain ⟨G, hG⟩ := hlocal k
      apply tendstoLocallyUniformlyOn_univ.mp
      exact (hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp hG).congr_right
        (fun _ ht ↦ (hG.tsum_eqOn ht).symm)
    have h : HasDerivAt (fun t : 𝕜 ↦ ∑' i, g k i t)
        (∑' i, g (k + 1) i y.val) y.val :=
      hasDerivAt_of_tendstoLocallyUniformlyOn hs hlimit
        (Eventually.of_forall fun t z hz ↦ HasDerivAt.fun_sum fun i _ ↦ hg k i ⟨z, hz⟩)
        (fun z hz ↦ by
          simpa only [HasSum, SummationFilter.unconditional_filter, hagree k _ ⟨z, hz⟩] using
            (hsumAll k ⟨z, hz⟩).hasSum)
        y.property
    have hpull := h.hasFDerivAt.comp_tendsto (Subtype.val : s → 𝕜)
      (continuous_subtype_val.continuousAt.tendsto.prodMap (tendsto_pure_pure Subtype.val y))
    simpa only [Function.comp_def, id_eq, hagree,
      ContinuousLinearMap.toSpanSingleton_apply, one_smul] using
      (hasFDerivAt_iff_hasDerivAt.mp hpull)
  have hiter (m a : ℕ) :
      HasIteratedDerivAt m (fun t : s ↦ ∑' i, f a i t) (∑' i, f (a + m) i x) x Subtype.val := by
    induction m generalizing a with
    | zero => rfl
    | succ m ih =>
      refine ⟨fun t : s ↦ ∑' i, f (a + 1) i t, hsucc a x, Or.inr (.of_forall (hsucc a)), ?_⟩
      rw [show a + (m + 1) = a + 1 + m by omega]
      exact ih (a + 1)
  simpa only [Nat.zero_add] using hiter k 0
