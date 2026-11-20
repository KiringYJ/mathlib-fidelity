/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.InnerProductSpace.Convex
public import Mathlib.Analysis.Normed.Affine.AddTorsor
public import Mathlib.Analysis.Normed.Module.Extr
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Topology.Order.ExtrClosure

/-!
# Maximum modulus principle

In this file we prove several versions of the maximum modulus principle. There are several
statements that can be called "the maximum modulus principle" for maps between normed complex
spaces. They differ by assumptions on the domain (any space, a nontrivial space, a finite
dimensional space), assumptions on the codomain (any space, a strictly convex space), and by
conclusion (either equality of norms or of the values of the function).

## Main results

### Theorems for any codomain

Consider a function `f : E → F` that is complex differentiable on a set `s`, is continuous on its
closure, and `‖f x‖` has a maximum on `s` at `c`. We prove the following theorems.

- `Complex.norm_eqOn_closedBall_of_isMaxOn`: if `s = Metric.ball c r`, then `‖f x‖ = ‖f c‖` for
  any `x` from the corresponding closed ball;

- `Complex.norm_eq_norm_of_isMaxOn_of_ball_subset`: if `Metric.ball c (dist w c) ⊆ s`, then
  `‖f w‖ = ‖f c‖`;

- `Complex.norm_eqOn_of_isPreconnected_of_isMaxOn`: if `U` is an open (pre)connected set, `f` is
  complex differentiable on `U`, and `‖f x‖` has a maximum on `U` at `c ∈ U`, then `‖f x‖ = ‖f c‖`
  for all `x ∈ U`;

- `Complex.norm_eqOn_closure_of_isPreconnected_of_isMaxOn`: if `s` is open and (pre)connected
  and `c ∈ s`, then `‖f x‖ = ‖f c‖` for all `x ∈ closure s`;

- `Complex.norm_eventually_eq_of_isLocalMax`: if `f` is complex differentiable in a neighborhood
  of `c` and `‖f x‖` has a local maximum at `c`, then `‖f x‖` is locally a constant in a
  neighborhood of `c`.

### Theorems for a strictly convex codomain

If the codomain `F` is a strictly convex space, then in the lemmas from the previous section we can
prove `f w = f c` instead of `‖f w‖ = ‖f c‖`, see
`Complex.eqOn_of_isPreconnected_of_isMaxOn_norm`,
`Complex.eqOn_closure_of_isPreconnected_of_isMaxOn_norm`,
`Complex.eq_of_isMaxOn_of_ball_subset`, `Complex.eqOn_closedBall_of_isMaxOn_norm`, and
`Complex.eventually_eq_of_isLocalMax_norm`.

### Values on the frontier

Finally, we prove some corollaries that relate the (norm of the) values of a function on a set to
its values on the frontier of the set. All these lemmas assume that `E` is a nontrivial space.  In
this section `f g : E → F` are functions that are complex differentiable on a bounded set `s` and
are continuous on its closure. We prove the following theorems.

- `Complex.exists_mem_frontier_isMaxOn_norm`: If `E` is a finite-dimensional space and `s` is a
  nonempty bounded set, then there exists a point `z ∈ frontier s` such that `(‖f ·‖)` takes it
  maximum value on `closure s` at `z`.

- `Complex.norm_le_of_forall_mem_frontier_norm_le`: if `‖f z‖ ≤ C` for all `z ∈ frontier s`, then
  `‖f z‖ ≤ C` for all `z ∈ s`; note that this theorem does not require `E` to be a
  finite-dimensional space.

- `Complex.eqOn_closure_of_eqOn_frontier`: if `f x = g x` on the frontier of `s`, then `f x = g x`
  on `closure s`;

- `Complex.eqOn_of_eqOn_frontier`: if `f x = g x` on the frontier of `s`, then `f x = g x`
  on `s`.

## Tags

maximum modulus principle, complex analysis
-/

public section


open TopologicalSpace Metric Set Filter Function AffineMap Bornology

open scoped Topology Filter NNReal Real

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] {F : Type v} [NormedAddCommGroup F]
  [NormedSpace ℂ F]

local postfix:100 "̂" => UniformSpace.Completion

namespace Complex

/-!
### Auxiliary lemmas

We split the proof into a series of lemmas. First we prove the principle for a function `f : ℂ → F`
with an additional assumption that `F` is a complete space, then drop unneeded assumptions one by
one.

The lemmas with names `*_auxₙ` are considered to be private and should not be used outside of this
file.
-/

theorem norm_max_aux₁ [CompleteSpace F] {f : ℂ → F} {z w : ℂ}
    (hd : DiffContOnCl ℂ f (ball z (dist w z)))
    (hz : IsMaxOn (norm ∘ f) (closedBall z (dist w z)) z) : ‖f w‖ = ‖f z‖ := by
  -- Consider a circle of radius `r = dist w z`.
  set r : ℝ := dist w z
  have hw : w ∈ closedBall z r := mem_closedBall.2 le_rfl
  -- Assume the converse. Since `‖f w‖ ≤ ‖f z‖`, we have `‖f w‖ < ‖f z‖`.
  refine (isMaxOn_iff.1 hz _ hw).antisymm (not_lt.1 ?_)
  rintro hw_lt : ‖f w‖ < ‖f z‖
  have hr : 0 < r := dist_pos.2 (ne_of_apply_ne (norm ∘ f) hw_lt.ne)
  have hzball : z ∈ ball z r := mem_ball_self hr
  have hkernel (θ : ℝ) : deriv (circleMap z r) θ •
      Checked.inv (circleMap z r θ - z) (isUnit_sub_of_mem_sphere_of_mem_ball hzball
        ⟨circleMap z r θ, circleMap_mem_sphere' z r θ⟩) = I := by
    rw [deriv_circleMap, smul_eq_mul, ← circleMap_sub_center z r θ, mul_comm _ I,
      mul_assoc, mul_inv_cancel₀, mul_one]
  have hCauchy : (∫ θ in 0..2 * π, I • f (circleMap z r θ)) = (2 * π * I : ℂ) • f z := by
    simpa only [circleIntegralOn_sphere, ← smul_assoc, hkernel] using
      hd.circleIntegral_sub_inv_smul hzball
  suffices ‖∫ θ in 0..2 * π, I • f (circleMap z r θ)‖ < 2 * π * ‖f z‖ by
    apply this.ne
    simp [hCauchy, norm_smul]
  have hws : w ∈ sphere z |r| := by
    change dist w z = |r|
    rw [abs_of_pos hr]
  rw [← image_circleMap_Ioc] at hws
  obtain ⟨θ₀, hθ₀, hθw⟩ := hws
  calc
    _ ≤ ∫ θ in 0..2 * π, ‖f (circleMap z r θ)‖ := by
      simpa only [norm_smul, norm_I, one_mul] using
        (intervalIntegral.norm_integral_le_integral_norm (f := fun θ ↦ I • f (circleMap z r θ))
          Real.two_pi_pos.le)
    _ < ∫ _ : ℝ in 0..2 * π, ‖f z‖ := by
      refine intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
        Real.two_pi_pos ?_ continuousOn_const (fun θ _ ↦ ?_) ⟨θ₀, Ioc_subset_Icc_self hθ₀, ?_⟩
      · exact (hd.continuousOn_ball.comp (continuous_circleMap _ _).continuousOn fun θ _ ↦
          sphere_subset_closedBall (circleMap_mem_sphere z hr.le θ)).norm
      · exact hz (sphere_subset_closedBall (circleMap_mem_sphere z hr.le θ))
      · simpa only [hθw] using hw_lt
    _ = _ := by simp [intervalIntegral.integral_const, smul_eq_mul]

/-!
Now we drop the assumption `CompleteSpace F` by embedding `F` into its completion.
-/

theorem norm_max_aux₂ {f : ℂ → F} {z w : ℂ} (hd : DiffContOnCl ℂ f (ball z (dist w z)))
    (hz : IsMaxOn (norm ∘ f) (closedBall z (dist w z)) z) : ‖f w‖ = ‖f z‖ := by
  set e : F →L[ℂ] F̂ := UniformSpace.Completion.toComplL
  have he : ∀ x, ‖e x‖ = ‖x‖ := UniformSpace.Completion.norm_coe
  replace hz : IsMaxOn (norm ∘ e ∘ f) (closedBall z (dist w z)) z := by
    simpa only [IsMaxOn, Function.comp_def, he] using hz
  simpa only [he, Function.comp_def]
    using norm_max_aux₁ (e.differentiable.comp_diffContOnCl hd) hz

/-!
Then we replace the assumption `IsMaxOn (norm ∘ f) (Metric.closedBall z r) z` with a seemingly
weaker assumption `IsMaxOn (norm ∘ f) (Metric.ball z r) z`.
-/

theorem norm_max_aux₃ {f : ℂ → F} {z w : ℂ} {r : ℝ} (hr : dist w z = r)
    (hd : DiffContOnCl ℂ f (ball z r)) (hz : IsMaxOn (norm ∘ f) (ball z r) z) : ‖f w‖ = ‖f z‖ := by
  subst r
  rcases eq_or_ne w z with (rfl | hne); · rfl
  rw [← dist_ne_zero] at hne
  exact norm_max_aux₂ hd (closure_ball z hne ▸ hz.closure hd.continuousOn.norm)

/-!
### Maximum modulus principle for any codomain

If we do not assume that the codomain is a strictly convex space, then we can only claim that the
**norm** `‖f x‖` is locally constant.
-/

/-!
Finally, we generalize the theorem from a disk in `ℂ` to a closed ball in any normed space.
-/

/-- **Maximum modulus principle** on a closed ball: if `f : E → F` is continuous on a closed ball,
is complex differentiable on the corresponding open ball, and the norm `‖f w‖` takes its maximum
value on the open ball at its center, then the norm `‖f w‖` is constant on the closed ball. -/
theorem norm_eqOn_closedBall_of_isMaxOn {f : E → F} {z : E} {r : ℝ}
    (hd : DiffContOnCl ℂ f (ball z r)) (hz : IsMaxOn (norm ∘ f) (ball z r) z) :
    EqOn (norm ∘ f) (const E ‖f z‖) (closedBall z r) := by
  intro w hw
  rw [mem_closedBall, dist_comm] at hw
  rcases eq_or_ne z w with (rfl | hne); · rfl
  set e := (lineMap z w : ℂ → E)
  have hde : Differentiable ℂ e := (differentiable_id.smul_const (w - z)).add_const z
  suffices ‖(f ∘ e) (1 : ℂ)‖ = ‖(f ∘ e) (0 : ℂ)‖ by simpa [e]
  have hr : dist (1 : ℂ) 0 = 1 := by simp
  have hball : MapsTo e (ball 0 1) (ball z r) := by
    refine ((lipschitzWith_lineMap z w).mapsTo_ball (mt nndist_eq_zero.1 hne) 0 1).mono
      Subset.rfl ?_
    simpa only [lineMap_apply_zero, mul_one, coe_nndist] using ball_subset_ball hw
  exact norm_max_aux₃ hr (hd.comp hde.diffContOnCl hball)
      (hz.comp_mapsTo hball (lineMap_apply_zero z w))

/-- **Maximum modulus principle**: if `f : E → F` is complex differentiable on a set `s`, the norm
of `f` takes it maximum on `s` at `z`, and `w` is a point such that the closed ball with center `z`
and radius `dist w z` is included in `s`, then `‖f w‖ = ‖f z‖`. -/
theorem norm_eq_norm_of_isMaxOn_of_ball_subset {f : E → F} {s : Set E} {z w : E}
    (hd : DiffContOnCl ℂ f s) (hz : IsMaxOn (norm ∘ f) s z) (hsub : ball z (dist w z) ⊆ s) :
    ‖f w‖ = ‖f z‖ :=
  norm_eqOn_closedBall_of_isMaxOn (hd.mono hsub) (hz.on_subset hsub) (mem_closedBall.2 le_rfl)

/-- **Maximum modulus principle**: if `f : E → F` is complex differentiable in a neighborhood of `c`
and the norm `‖f z‖` has a local maximum at `c`, then `‖f z‖` is locally constant in a neighborhood
of `c`. -/
theorem norm_eventually_eq_of_isLocalMax {f : E → F} {c : E}
    (hd : ∀ᶠ z in 𝓝 c, DifferentiableAt ℂ f z) (hc : IsLocalMax (norm ∘ f) c) :
    ∀ᶠ y in 𝓝 c, ‖f y‖ = ‖f c‖ := by
  rcases nhds_basis_closedBall.eventually_iff.1 (hd.and hc) with ⟨r, hr₀, hr⟩
  exact nhds_basis_closedBall.eventually_iff.2
    ⟨r, hr₀, norm_eqOn_closedBall_of_isMaxOn (DifferentiableOn.diffContOnCl fun x hx =>
        (hr <| closure_ball_subset_closedBall hx).1.differentiableWithinAt) fun x hx =>
      (hr <| ball_subset_closedBall hx).2⟩

theorem isOpen_setOfPred_mem_nhds_and_isMaxOn_norm {f : E → F} {s : Set E}
    (hd : DifferentiableOn ℂ f s) : IsOpen {z | s ∈ 𝓝 z ∧ IsMaxOn (norm ∘ f) s z} := by
  refine isOpen_iff_mem_nhds.2 fun z hz => (eventually_eventually_nhds.2 hz.1).and ?_
  replace hd : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ f w := hd.eventually_differentiableAt hz.1
  exact (norm_eventually_eq_of_isLocalMax hd <| hz.2.isLocalMax hz.1).mono fun x hx y hy =>
    le_trans (hz.2 hy).out hx.ge

@[deprecated (since := "2026-07-09")]
alias isOpen_setOf_mem_nhds_and_isMaxOn_norm := isOpen_setOfPred_mem_nhds_and_isMaxOn_norm

/-- **Maximum modulus principle** on a connected set. Let `U` be a (pre)connected open set in a
complex normed space. Let `f : E → F` be a function that is complex differentiable on `U`. Suppose
that `‖f x‖` takes its maximum value on `U` at `c ∈ U`. Then `‖f x‖ = ‖f c‖` for all `x ∈ U`. -/
theorem norm_eqOn_of_isPreconnected_of_isMaxOn {f : E → F} {U : Set E} {c : E}
    (hc : IsPreconnected U) (ho : IsOpen U) (hd : DifferentiableOn ℂ f U) (hcU : c ∈ U)
    (hm : IsMaxOn (norm ∘ f) U c) : EqOn (norm ∘ f) (const E ‖f c‖) U := by
  set V := U ∩ {z | IsMaxOn (norm ∘ f) U z}
  have hV : ∀ x ∈ V, ‖f x‖ = ‖f c‖ := fun x hx => le_antisymm (hm hx.1) (hx.2 hcU)
  suffices U ⊆ V from fun x hx => hV x (this hx)
  have hVo : IsOpen V := by
    simpa only [ho.mem_nhds_iff, ofPred_and, ofPred_mem_eq]
      using isOpen_setOfPred_mem_nhds_and_isMaxOn_norm hd
  have hVne : (U ∩ V).Nonempty := ⟨c, hcU, hcU, hm⟩
  set W := U ∩ {z | ‖f z‖ ≠ ‖f c‖}
  have hWo : IsOpen W := hd.continuousOn.norm.isOpen_inter_preimage ho isOpen_ne
  have hdVW : Disjoint V W := disjoint_left.mpr fun x hxV hxW => hxW.2 (hV x hxV)
  have hUVW : U ⊆ V ∪ W := fun x hx =>
    (eq_or_ne ‖f x‖ ‖f c‖).imp (fun h => ⟨hx, fun y hy => (hm hy).out.trans_eq h.symm⟩)
      (And.intro hx)
  exact hc.subset_left_of_subset_union hVo hWo hdVW hUVW hVne

/-- **Maximum modulus principle** on a connected set. Let `U` be a (pre)connected open set in a
complex normed space.  Let `f : E → F` be a function that is complex differentiable on `U` and is
continuous on its closure. Suppose that `‖f x‖` takes its maximum value on `U` at `c ∈ U`. Then
`‖f x‖ = ‖f c‖` for all `x ∈ closure U`. -/
theorem norm_eqOn_closure_of_isPreconnected_of_isMaxOn {f : E → F} {U : Set E} {c : E}
    (hc : IsPreconnected U) (ho : IsOpen U) (hd : DiffContOnCl ℂ f U) (hcU : c ∈ U)
    (hm : IsMaxOn (norm ∘ f) U c) : EqOn (norm ∘ f) (const E ‖f c‖) (closure U) :=
  (norm_eqOn_of_isPreconnected_of_isMaxOn hc ho hd.differentiableOn hcU hm).of_subset_closure
    hd.continuousOn.norm continuousOn_const subset_closure Subset.rfl

section StrictConvex

/-!
### The case of a strictly convex codomain

If the codomain `F` is a strictly convex space, then we can claim equalities like `f w = f z`
instead of `‖f w‖ = ‖f z‖`.

Instead of repeating the proof starting with lemmas about integrals, we apply a corresponding lemma
above twice: for `f` and for `(f · + f c)`.  Then we have `‖f w‖ = ‖f z‖` and
`‖f w + f z‖ = ‖f z + f z‖`, thus `‖f w + f z‖ = ‖f w‖ + ‖f z‖`. This is only possible if
`f w = f z`, see `eq_of_norm_eq_of_norm_add_eq`.
-/

variable [StrictConvexSpace ℝ F]

/-- **Maximum modulus principle** on a connected set. Let `U` be a (pre)connected open set in a
complex normed space.  Let `f : E → F` be a function that is complex differentiable on `U`. Suppose
that `‖f x‖` takes its maximum value on `U` at `c ∈ U`. Then `f x = f c` for all `x ∈ U`.

TODO: change assumption from `IsMaxOn` to `IsLocalMax`. -/
theorem eqOn_of_isPreconnected_of_isMaxOn_norm {f : E → F} {U : Set E} {c : E}
    (hc : IsPreconnected U) (ho : IsOpen U) (hd : DifferentiableOn ℂ f U) (hcU : c ∈ U)
    (hm : IsMaxOn (norm ∘ f) U c) : EqOn f (const E (f c)) U := fun x hx =>
  have H₁ : ‖f x‖ = ‖f c‖ := norm_eqOn_of_isPreconnected_of_isMaxOn hc ho hd hcU hm hx
  have H₂ : ‖f x + f c‖ = ‖f c + f c‖ :=
    norm_eqOn_of_isPreconnected_of_isMaxOn hc ho (hd.add_const _) hcU hm.norm_add_self hx
  eq_of_norm_eq_of_norm_add_eq H₁ <| by simp only [H₂, SameRay.rfl.norm_add, H₁, Function.const]

/-- **Maximum modulus principle** on a connected set. Let `U` be a (pre)connected open set in a
complex normed space.  Let `f : E → F` be a function that is complex differentiable on `U` and is
continuous on its closure. Suppose that `‖f x‖` takes its maximum value on `U` at `c ∈ U`. Then
`f x = f c` for all `x ∈ closure U`. -/
theorem eqOn_closure_of_isPreconnected_of_isMaxOn_norm {f : E → F} {U : Set E} {c : E}
    (hc : IsPreconnected U) (ho : IsOpen U) (hd : DiffContOnCl ℂ f U) (hcU : c ∈ U)
    (hm : IsMaxOn (norm ∘ f) U c) : EqOn f (const E (f c)) (closure U) :=
  (eqOn_of_isPreconnected_of_isMaxOn_norm hc ho hd.differentiableOn hcU hm).of_subset_closure
    hd.continuousOn continuousOn_const subset_closure Subset.rfl

/-- **Maximum modulus principle**. Let `f : E → F` be a function between complex normed spaces.
Suppose that the codomain `F` is a strictly convex space, `f` is complex differentiable on a set
`s`, `f` is continuous on the closure of `s`, the norm of `f` takes it maximum on `s` at `z`, and
`w` is a point such that the closed ball with center `z` and radius `dist w z` is included in `s`,
then `f w = f z`. -/
theorem eq_of_isMaxOn_of_ball_subset {f : E → F} {s : Set E} {z w : E} (hd : DiffContOnCl ℂ f s)
    (hz : IsMaxOn (norm ∘ f) s z) (hsub : ball z (dist w z) ⊆ s) : f w = f z :=
  have H₁ : ‖f w‖ = ‖f z‖ := norm_eq_norm_of_isMaxOn_of_ball_subset hd hz hsub
  have H₂ : ‖f w + f z‖ = ‖f z + f z‖ :=
    norm_eq_norm_of_isMaxOn_of_ball_subset (hd.add_const _) hz.norm_add_self hsub
  eq_of_norm_eq_of_norm_add_eq H₁ <| by simp only [H₂, SameRay.rfl.norm_add, H₁]

/-- **Maximum modulus principle** on a closed ball. Suppose that a function `f : E → F` from a
normed complex space to a strictly convex normed complex space has the following properties:

- it is continuous on a closed ball `Metric.closedBall z r`,
- it is complex differentiable on the corresponding open ball;
- the norm `‖f w‖` takes its maximum value on the open ball at its center.

Then `f` is a constant on the closed ball. -/
theorem eqOn_closedBall_of_isMaxOn_norm {f : E → F} {z : E} {r : ℝ}
    (hd : DiffContOnCl ℂ f (ball z r)) (hz : IsMaxOn (norm ∘ f) (ball z r) z) :
    EqOn f (const E (f z)) (closedBall z r) := fun _x hx =>
  eq_of_isMaxOn_of_ball_subset hd hz <| ball_subset_ball hx

/-- If `f` is differentiable on the open unit ball `{z : ℂ | ‖z‖ < 1}`, and `‖f‖` attains a maximum
in this open ball, then `f` is constant. -/
lemma eq_const_of_exists_max {f : E → F} {b : ℝ} (h_an : DifferentiableOn ℂ f (ball 0 b))
    {v : E} (hv : v ∈ ball 0 b) (hv_max : IsMaxOn (norm ∘ f) (ball 0 b) v) :
    Set.EqOn f (Function.const E (f v)) (ball 0 b) :=
  Complex.eqOn_of_isPreconnected_of_isMaxOn_norm (convex_ball 0 b).isPreconnected
    isOpen_ball h_an hv hv_max

/-- If `f` is a function differentiable on the open unit ball, and there exists an `r < 1` such that
any value of `‖f‖` on the open ball is bounded above by some value on the closed ball of radius `r`,
then `f` is constant. -/
lemma eq_const_of_exists_le [ProperSpace E] {f : E → F} {r b : ℝ}
    (h_an : DifferentiableOn ℂ f (ball 0 b)) (hr_nn : 0 ≤ r) (hr_lt : r < b)
    (hr : ∀ z, z ∈ (ball 0 b) → ∃ w, w ∈ closedBall 0 r ∧ ‖f z‖ ≤ ‖f w‖) :
    Set.EqOn f (Function.const E (f 0)) (ball 0 b) := by
  obtain ⟨x, hx_mem, hx_max⟩ := isCompact_closedBall (0 : E) r |>.exists_isMaxOn
    (nonempty_closedBall.mpr hr_nn)
    (h_an.continuousOn.mono <| closedBall_subset_ball hr_lt).norm
  suffices Set.EqOn f (Function.const E (f x)) (ball 0 b) by
    rwa [this (mem_ball_self (hr_nn.trans_lt hr_lt))]
  apply eq_const_of_exists_max h_an (closedBall_subset_ball hr_lt hx_mem) (fun z hz ↦ ?_)
  obtain ⟨w, hw, hw'⟩ := hr z hz
  exact hw'.trans (hx_max hw)

/-- **Maximum modulus principle**: if `f : E → F` is complex differentiable in a neighborhood of `c`
and the norm `‖f z‖` has a local maximum at `c`, then `f` is locally constant in a neighborhood
of `c`. -/
theorem eventually_eq_of_isLocalMax_norm {f : E → F} {c : E}
    (hd : ∀ᶠ z in 𝓝 c, DifferentiableAt ℂ f z) (hc : IsLocalMax (norm ∘ f) c) :
    ∀ᶠ y in 𝓝 c, f y = f c := by
  rcases nhds_basis_closedBall.eventually_iff.1 (hd.and hc) with ⟨r, hr₀, hr⟩
  exact nhds_basis_closedBall.eventually_iff.2
    ⟨r, hr₀, eqOn_closedBall_of_isMaxOn_norm (DifferentiableOn.diffContOnCl fun x hx =>
        (hr <| closure_ball_subset_closedBall hx).1.differentiableWithinAt) fun x hx =>
      (hr <| ball_subset_closedBall hx).2⟩

theorem eventually_eq_or_eq_zero_of_isLocalMin_norm {f : E → ℂ} {c : E}
    (hf : ∀ᶠ z in 𝓝 c, DifferentiableAt ℂ f z) (hc : IsLocalMin (norm ∘ f) c) :
    (∀ᶠ z in 𝓝 c, f z = f c) ∨ f c = 0 := by
  refine or_iff_not_imp_right.mpr fun h => ?_
  have h1 : ∀ᶠ z in 𝓝 c, f z ≠ 0 := hf.self_of_nhds.continuousAt.eventually_ne h
  have hunit : IsUnit (f c) := Ne.isUnit h
  let S : Set E := {z | IsUnit (f z)}
  let g : E → ℂ := Function.extend (Subtype.val : S → E)
    (fun z : S ↦ Checked.inv (f z.val) z.property) 0
  have hg (z : E) (hz : IsUnit (f z)) : g z = Checked.inv (f z) hz :=
    Subtype.val_injective.extend_apply _ _ (⟨z, hz⟩ : S)
  have hmax : IsLocalMax (norm ∘ g) c := by
    filter_upwards [hc, h1] with z hz hne
    simp only [Function.comp_apply, hg z hne.isUnit, hg c hunit, norm_inv]
    exact inv_anti₀ (norm_pos_iff.mpr h) hz
  have hdg : ∀ᶠ z in 𝓝 c, DifferentiableAt ℂ g z := by
    filter_upwards [hf, h1] with z hz hne
    have hmem : S ∈ 𝓝 z := (hz.continuousAt.eventually_ne hne).mono fun _ hw ↦ hw.isUnit
    refine DifferentiableAt.of_restrict (s := S) (x := ⟨z, hne.isUnit⟩) ?_ hmem
    have hfun : (fun y : S ↦ g y.val) = fun y : S ↦ Checked.inv (f y.val) y.property :=
      funext fun y ↦ hg y.val y.property
    rw [hfun]
    exact hz.inv hne.isUnit
  filter_upwards [eventually_eq_of_isLocalMax_norm hdg hmax, h1] with z hz hne
  exact inv_inj₀.mp (by simpa only [hg z hne.isUnit, hg c hunit] using hz)

end StrictConvex

/-!
### Maximum on a set vs maximum on its frontier

In this section we prove corollaries of the maximum modulus principle that relate the values of a
function on a set to its values on the frontier of this set.
-/


variable [Nontrivial E]

/-- **Maximum modulus principle**: if `f : E → F` is complex differentiable on a nonempty bounded
set `U` and is continuous on its closure, then there exists a point `z ∈ frontier U` such that
`(‖f ·‖)` takes it maximum value on `closure U` at `z`. -/
theorem exists_mem_frontier_isMaxOn_norm [FiniteDimensional ℂ E] {f : E → F} {U : Set E}
    (hb : IsBounded U) (hne : U.Nonempty) (hd : DiffContOnCl ℂ f U) :
    ∃ z ∈ frontier U, IsMaxOn (norm ∘ f) (closure U) z := by
  have hc : IsCompact (closure U) := hb.isCompact_closure
  obtain ⟨w, hwU, hle⟩ : ∃ w ∈ closure U, IsMaxOn (norm ∘ f) (closure U) w :=
    hc.exists_isMaxOn hne.closure hd.continuousOn.norm
  rw [closure_eq_interior_union_frontier, mem_union] at hwU
  rcases hwU with hwU | hwU; rotate_left; · exact ⟨w, hwU, hle⟩
  have : interior U ≠ univ := ne_top_of_le_ne_top hc.ne_univ interior_subset_closure
  rcases exists_mem_frontier_infDist_compl_eq_dist hwU this with ⟨z, hzU, hzw⟩
  refine ⟨z, frontier_interior_subset hzU, fun x hx => (hle hx).out.trans_eq ?_⟩
  refine (norm_eq_norm_of_isMaxOn_of_ball_subset hd (hle.on_subset subset_closure) ?_).symm
  rw [dist_comm, ← hzw]
  exact ball_infDist_compl_subset.trans interior_subset

/-- **Maximum modulus principle**: if `f : E → F` is complex differentiable on a bounded set `U` and
`‖f z‖ ≤ C` for any `z ∈ frontier U`, then the same is true for any `z ∈ closure U`. -/
theorem norm_le_of_forall_mem_frontier_norm_le {f : E → F} {U : Set E} (hU : IsBounded U)
    (hd : DiffContOnCl ℂ f U) {C : ℝ} (hC : ∀ z ∈ frontier U, ‖f z‖ ≤ C) {z : E}
    (hz : z ∈ closure U) : ‖f z‖ ≤ C := by
  rw [closure_eq_self_union_frontier, union_comm, mem_union] at hz
  rcases hz with hz | hz; · exact hC z hz
  /- In case of a finite-dimensional domain, one can just apply
    `Complex.exists_mem_frontier_isMaxOn_norm`. To make it work in any Banach space, we restrict
    the function to a line first. -/
  rcases exists_ne z with ⟨w, hne⟩
  set e := (lineMap z w : ℂ → E)
  have hde : Differentiable ℂ e := (differentiable_id.smul_const (w - z)).add_const z
  have he : IsUnit (nndist z w) := (by simpa using hne.symm : nndist z w ≠ 0).isUnit
  have hL : AntilipschitzWith (nndist z w)⁻¹ e := antilipschitzWith_lineMap hne.symm
  replace hd : DiffContOnCl ℂ (f ∘ e) (e ⁻¹' U) :=
    hd.comp hde.diffContOnCl (mapsTo_preimage _ _)
  have h₀ : (0 : ℂ) ∈ e ⁻¹' U := by simpa only [e, mem_preimage, lineMap_apply_zero]
  rcases exists_mem_frontier_isMaxOn_norm (hL.isBounded_preimage hU) ⟨0, h₀⟩ hd with ⟨ζ, hζU, hζ⟩
  calc
    ‖f z‖ = ‖f (e 0)‖ := by simp only [e, lineMap_apply_zero]
    _ ≤ ‖f (e ζ)‖ := hζ (subset_closure h₀)
    _ ≤ C := hC _ (hde.continuous.frontier_preimage_subset _ hζU)

/-- If two complex differentiable functions `f g : E → F` are equal on the boundary of a bounded set
`U`, then they are equal on `closure U`. -/
theorem eqOn_closure_of_eqOn_frontier {f g : E → F} {U : Set E} (hU : IsBounded U)
    (hf : DiffContOnCl ℂ f U) (hg : DiffContOnCl ℂ g U) (hfg : EqOn f g (frontier U)) :
    EqOn f g (closure U) := by
  suffices H : ∀ z ∈ closure U, ‖(f - g) z‖ ≤ 0 by simpa [sub_eq_zero] using! H
  refine fun z hz => norm_le_of_forall_mem_frontier_norm_le hU (hf.sub hg) (fun w hw => ?_) hz
  simp [hfg hw]

/-- If two complex differentiable functions `f g : E → F` are equal on the boundary of a bounded set
`U`, then they are equal on `U`. -/
theorem eqOn_of_eqOn_frontier {f g : E → F} {U : Set E} (hU : IsBounded U) (hf : DiffContOnCl ℂ f U)
    (hg : DiffContOnCl ℂ g U) (hfg : EqOn f g (frontier U)) : EqOn f g U :=
  (eqOn_closure_of_eqOn_frontier hU hf hg hfg).mono subset_closure

end Complex
