/-
Copyright (c) 2026 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module


import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Complex.BranchLogRoot
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Analysis.Complex.Order
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.Data.EReal.Inv
public import Mathlib.Tactic.ContinuousFunctionalCalculus

/-!
# Riemann mapping theorem

This file contains partial results towards Riemann Mapping Theorem.
A complete proof is available at https://github.com/leanprover-community/mathlib4/pull/33505,
though it may fail to compile with the latest Mathlib.

It is being brought up to Mathlib code standards and merged in a series of smaller PRs.
For now, all lemmas in this file are strictly weaker than the final theorem,
so they're private.
-/

set_option linter.privateModule false -- TODO: remove when we add the main theorem

open Function Filter Metric Set
open scoped Pointwise Topology

namespace Complex

/-- Proof of the Riemann Mapping Theorem, step 1.

If `U` is an open simply connected subset of `ℂ` that is not the whole `ℂ`,
then there exists a function `f : ℂ → ℂ` such that

- `f` is injective;
- the image `f '' U` isn't dense in `ℂ`;
- `f` is complex differentiable on `U` with nonzero derivative.

E.g., one can choose `a ∉ U`, then take `f z` to be the square root of `z - a`.
-/
theorem exists_injective_not_dense_image_deriv_ne_zero {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsSimplyConnected U) (hU : U ≠ univ) :
    ∃ f : ℂ → ℂ, Injective f ∧ ¬Dense (f '' U) ∧ ∀ z ∈ U, deriv f z ≠ 0 := by
  -- WLOG, `0 ∉ U`, otherwise we choose `a ∉ U` and replace `U` with `-a +ᵥ U`
  wlog hU₀ : 0 ∉ U
  · rw [ne_univ_iff_exists_notMem] at hU
    rcases hU with ⟨a, ha⟩
    specialize this (hUo.vadd (-a)) (by simpa) (by simp [hU])
      (by simpa [mem_vadd_set_iff_neg_vadd_mem])
    rcases this with ⟨f, hf_inj, hf_dense, hdf⟩
    refine ⟨f ∘ (-a + ·), hf_inj.comp (add_right_injective (-a)), ?_, fun z hz ↦ ?_⟩
    · simpa only [← image_vadd, Set.image_image] using! hf_dense
    · simpa [Function.comp_def, deriv_comp_const_add] using hdf (-a + z) (mapsTo_image _ _ hz)
  -- Choose a continuous branch of `√z` on `U`.
  -- This is the function we're looking for.
  rcases exists_continuousOn_pow_eq hUc hUo continuousOn_id (by rwa [image_id]) two_ne_zero
    with ⟨f, hfc, hf_inv⟩
  replace hf_inv : LeftInverse (· ^ 2) f := hf_inv
  -- Then `0 ∉ f '' U`
  have hf₀ : ∀ z ∈ U, f z ≠ 0 := by
    intro z hz hfz
    simpa [hfz, (ne_of_mem_of_not_mem hz hU₀).symm] using hf_inv z
  -- Note that `f` is strictly differentiable at every point of `U`
  -- with derivative `1 / (2 * f z)`.
  have hdf : ∀ z (hz : z ∈ U), HasStrictDerivAt f
      (Checked.inv (2 * f z) (mul_ne_zero two_ne_zero (hf₀ z hz)).isUnit) z := by
    intro z hz
    apply HasStrictDerivAt.of_local_left_inverse
    · exact hfc.continuousAt <| hUo.mem_nhds hz
    · simpa using hasStrictDerivAt_pow 2 (f z)
    · simpa using hf₀ z hz
    · exact .of_forall hf_inv
  -- `f` has a left inverse, so it's injective. Let's show that `f '' U` isn't dense in `ℂ`.
  refine ⟨f, hf_inv.injective, ?_, fun z hz ↦ ?_⟩
  · -- Take a point `x ∈ U`.
    simp only [Dense, not_forall, mem_closure_iff_frequently, not_frequently]
    rcases hUc.nonempty with ⟨x, hx⟩
    -- Show that `-f x` has a neighborhood disjoint with `f '' U`.
    use -f x
    -- Since `f` is strictly differentiable at `x` with nonzero derivative,
    -- `f '' U` is a neighborhood of `f x`.
    have : f '' U ∈ 𝓝 (f x) := by
      rw [← (hdf x hx).map_nhds_eq inv_ne_zero]
      exact Filter.image_mem_map <| hUo.mem_nhds hx
    -- Then `-f '' U` is a neighborhood of `-f x`.
    rw [nhds_neg, eventually_neg]
    -- This neighborhood has to be disjoint with `f '' U`,
    -- because `f a = - f b` implies `a = (f a) ^ 2 = (- f b) ^ 2 = b`, hence `f a = f b = 0`,
    -- which is impossible.
    filter_upwards [this]
    rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    obtain rfl : a = b := by
      rw [← hf_inv b, hab]
      simp [hf_inv a]
    refine hf₀ a ha ?_
    linear_combination hab / 2
  · rw [(hdf z hz).hasDerivAt.deriv]
    exact inv_ne_zero

/-- Proof of the Riemann Mapping Theorem, step 2.

If `U` is an open simply connected subset of `ℂ` which is not the whole field,
then there exists a map `f : ℂ → ℂ` such that

- `f` maps `U` to the unit disk;
- `f` is injective on `U`;
- `f` is differentiable on `U` with nonzero derivative.

Once the proof of the Riemann Mapping Theorem gets merged into Mathlib,
this lemma will be made private.
-/
lemma exists_mapsTo_unitBall_injOn_deriv_ne_zero {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsSimplyConnected U) (hU : U ≠ univ) :
    ∃ f : ℂ → ℂ, MapsTo f U (ball 0 1) ∧ InjOn f U ∧ ∀ z ∈ U, deriv f z ≠ 0 := by
  classical
  -- Take a continuous branch of the square root on `U`.
  -- It is injective, differentiable function on `U`, and `f '' U` isn't dense in `ℂ`.
  rcases exists_injective_not_dense_image_deriv_ne_zero hUo hUc hU with ⟨f, hf_inj, hfd, hdf⟩
  -- Choose a closed ball `Metric.closedBall x ε`, `ε > 0`, that is disjoint with `f '' U`.
  obtain ⟨x, ε, hε₀, hε⟩ : ∃ (x : ℂ) (ε : ℝ), 0 < ε ∧ ∀ a ∈ U, ε < dist (f a) x := by
    simpa [Dense, mem_closure_iff_nhds_basis Metric.nhds_basis_closedBall] using hfd
  have hfx : ∀ z ∈ U, f z ≠ x := fun z hz ↦ by simpa using hε₀.trans (hε z hz)
  -- Extend the restriction of `f` to `U` with a value in `f '' U` so that its range avoids `x`.
  obtain ⟨a, ha⟩ := hUc.nonempty
  let g : ℂ → ℂ := U.piecewise f (fun _ ↦ f a)
  have hg (z : ℂ) : IsUnit (g z - x) := by
    apply Ne.isUnit
    rw [sub_ne_zero]
    by_cases hz : z ∈ U
    · simpa [g, hz] using hfx z hz
    · simpa [g, hz] using hfx a ha
  let G (z : ℂ) := Checked.div (ε : ℂ) (g z - x) (hg z)
  use G
  refine ⟨?mapsTo, ?injOn, ?deriv⟩
  case mapsTo =>
    intro z hz
    rw [mem_ball_zero_iff]
    change ‖Checked.div (ε : ℂ) (g z - x) (hg z)‖ < 1
    rw [norm_div, norm_real, Real.norm_of_nonneg hε₀.le,
      div_lt_one₀ (norm_pos_iff.2 (hg z).ne_zero)]
    simpa [dist_eq_norm, g, hz] using hε z hz
  case injOn =>
    intro z hz w hw heq
    have he : (ε : ℂ) * (g w - x) = (ε : ℂ) * (g z - x) := div_eq_div_iff.mp heq
    apply hf_inj
    simpa [g, hz, hw] using (mul_left_cancel₀ (ofReal_ne_zero.mpr hε₀.ne') he).symm
  case deriv =>
    intro z hz
    have hdz : DifferentiableAt ℂ f z := differentiableAt_of_deriv_ne_zero (hdf z hz)
    have hdg : HasDerivAt g (deriv f z) z := hdz.hasDerivAt.congr_of_eventuallyEq <| by
      filter_upwards [hUo.mem_nhds hz] with y hy
      simp [g, hy]
    let lift (y : ℂ) : {y : ℂ // IsUnit (g y - x)} := ⟨y, hg y⟩
    have hlift : Continuous lift := continuous_id.subtype_mk _
    have hd := (hasDerivAt_const z (ε : ℂ)).div (hdg.sub_const x) (hg z)
    have hcomp := hd.hasFDerivAt.comp_tendsto lift
      (hlift.continuousAt.tendsto.prodMap (tendsto_pure_pure lift z))
    have hG : HasDerivAt G
        ((0 * (g z - x) - (ε : ℂ) * deriv f z) /ₚ ((hg z).unit ^ 2)) z := by
      have h := hcomp.hasDerivAtFilter
      simp only [lift, Function.comp_def, ContinuousLinearMap.toSpanSingleton_apply, one_smul] at h
      exact h
    rw [hG.deriv]
    simp [divp, ofReal_ne_zero.mpr hε₀.ne', hdf z hz]

end Complex
