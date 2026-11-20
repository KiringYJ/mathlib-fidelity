/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# Schwarz lemma

In this file we prove several versions of the Schwarz lemma.

* `Complex.norm_deriv_le_div_of_mapsTo_ball`. Let `f : ℂ → E` be a complex analytic function
  on an open disk with center `c` and a positive radius `R₁`.
  If `f` sends this ball to a closed ball with center `f c` and radius `R₂`,
  then the norm of the derivative of `f` at `c` is at most the ratio `R₂ / R₁`.

* `Complex.dist_le_div_mul_dist_of_mapsTo_ball`. Let `f : E → F` be a complex analytic function
  on an open ball with center `c` and radius `R₁`.
  If `f` sends this ball to a closed ball with center `f c` and radius `R₂`,
  then for any `z` in the former ball we have `dist (f z) (f c) ≤ (R₂ / R₁) * dist z c`.

* `Complex.norm_deriv_le_one_of_mapsTo_ball`. If `f : ℂ → E` is complex analytic
  on an open disk with center `c` and a positive radius `R₁`,
  and it sends this disk to a closed ball with center `f c` and radius the same radius,
  then the norm of the derivative of `f` at the center of this disk is at most `1`.

* `Complex.dist_le_dist_of_mapsTo_ball`. Let `f : E → F` be a complex analytic function
  on an open ball with center `c`.
  If `f` sends this ball to a closed ball with center `f c` and the same radius,
  then for any `z` in the former ball we have `dist (f z) (f c) ≤ dist z c`.

* `Complex.norm_le_norm_of_mapsTo_ball`:
  Let `f : E → F` be a complex analytic on an open ball with center at the origin.
  If `f` sends this ball to the closed ball with center `0` of the same radius and `f 0 = 0`,
  then for any point `z` of this disk we have `‖f z‖ ≤ ‖z‖`.

## Implementation notes

Traditionally, the Schwarz lemma is formulated for maps `f : ℂ → ℂ`.
We generalize all versions of the lemma to the case of maps to any normed space.
For the versions that don't use `deriv` or `dslope`,
we state it for maps between any two normed spaces.

## TODO

* Prove that any diffeomorphism of the unit disk to itself is a Möbius map.

## Tags

Schwarz lemma
-/

open Metric Set Function Filter

open scoped Topology ComplexConjugate

namespace Complex

/-- An auxiliary lemma for `Complex.dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO`. -/
theorem schwarz_aux {f : ℂ → ℂ} {c z : ℂ} {R₁ R₂ : ℝ} {n : ℕ}
    (hd : DifferentiableOn ℂ f (ball c R₁)) (h_maps : MapsTo f (ball c R₁) (closedBall (f c) R₂))
    (hn : (f · - f c) =o[𝓝 c] (fun w ↦ (w - c) ^ n)) (hz : z ∈ ball c R₁) :
    ‖f z - f c‖ ≤ R₂ * (‖z - c‖ / R₁) ^ (n + 1) := by
  -- By slightly reducing `R₁`, we can assume that `f` is differentiable on `closedBall c R₁`
  -- and it maps this ball to the closed ball in the codomain.
  have hR₁ : 0 < R₁ := nonempty_ball.1 ⟨z, hz⟩
  wlog hd' : DifferentiableOn ℂ f (closedBall c R₁) id ∧
    MapsTo f (closedBall c R₁) (closedBall (f c) R₂) generalizing R₁
  · let l := comap (Subtype.val : Ioi (0 : ℝ) → ℝ) (𝓝[<] R₁)
    have hpos : Ioi (0 : ℝ) ∈ 𝓝[<] R₁ :=
      mem_nhdsWithin_of_mem_nhds (isOpen_Ioi.mem_nhds hR₁)
    have hlarge : Set.range (Subtype.val : Ioi (0 : ℝ) → ℝ) ∈ 𝓝[<] R₁ := by
      simpa only [Subtype.range_val] using hpos
    have hl : l.NeBot := (inferInstance : NeBot (𝓝[<] R₁)).comap_of_range_mem hlarge
    have hval : Tendsto (Subtype.val : Ioi (0 : ℝ) → ℝ) l (𝓝 R₁) :=
      tendsto_comap.mono_right nhdsWithin_le_nhds
    have hconst : Tendsto (fun _ : Ioi (0 : ℝ) ↦ ‖z - c‖) l (𝓝 ‖z - c‖) :=
      tendsto_const_nhds
    have hquot := hconst.div₀ hval (h₀ := fun r ↦ (mem_Ioi.mp r.2).ne'.isUnit)
      (hb := hR₁.ne'.isUnit)
    refine ge_of_tendsto ((hquot.pow (n + 1)).const_mul R₂) ?_
    rw [show l = comap (Subtype.val : Ioi (0 : ℝ) → ℝ) (𝓝[<] R₁) from rfl, eventually_comap]
    filter_upwards [Ioo_mem_nhdsLT (mem_ball_iff_norm.mp hz)] with r ⟨hzr, hrR₁⟩ y hy
    subst r
    exact this (hd.mono (ball_subset_ball hrR₁.le))
      (h_maps.mono_left (ball_subset_ball hrR₁.le)) (mem_ball_iff_norm.mpr hzr) y.2
      ⟨hd.mono (closedBall_subset_ball hrR₁), h_maps.mono_left (closedBall_subset_ball hrR₁)⟩
  -- Cleanup, discard the case `z = c`.
  clear hd h_maps
  rcases hd' with ⟨hd, h_maps⟩
  rcases eq_or_ne z c with rfl | hne
  · simp
  let D : Set ℂ := ({c} : Set ℂ)ᶜ
  have hD : IsOpen D := isClosed_singleton.isOpen_compl
  have hp (w : D) : IsUnit ((w.val - c) ^ (n + 1)) :=
    (sub_ne_zero.mpr w.property).isUnit.pow _
  let p (w : D) := Checked.inv ((w.val - c) ^ (n + 1)) (hp w)
  let Q := Function.extend (Subtype.val : D → ℂ) p 0
  have hQ (w : D) : Q w.val = p w := Subtype.val_injective.extend_apply _ _ _
  have hQd (w : D) : DifferentiableAt ℂ Q w.val := by
    apply DifferentiableAt.of_restrict (s := D) (x := w) ?_ (hD.mem_nhds w.property)
    let q (y : D) : {y : ℂ // IsUnit ((y - c) ^ (n + 1))} := ⟨y.val, hp y⟩
    have hpow : AnalyticAt ℂ (fun y : ℂ ↦ (y - c) ^ (n + 1)) w.val := by fun_prop
    have ha := (hpow.inv (hp w)).comp_domain (g := q) (x := w)
    simpa only [q, Function.comp_def, hQ, p, Checked.inv, id_eq] using
      ha.differentiableAt continuous_subtype_val.continuousAt
  let g (w : ℂ) := Q w * (f w - f c)
  let g' := update g c (limUnder (𝓝[≠] c) g)
  have hdg' : DifferentiableOn ℂ g' (closedBall c R₁) := by
    refine .mono ?_ (subset_insert_sdiff_singleton c _)
    apply differentiableOn_update_limUnder_insert_of_isLittleO
    · exact sdiff_mem_nhdsWithin_compl (closedBall_mem_nhds _ hR₁) _
    · refine .mul ?_ (hd.mono sdiff_subset |>.sub_const _)
      exact fun w hw ↦ (hQd ⟨w, hw.2⟩).differentiableWithinAt
    · have hv : Tendsto (Subtype.val : D → ℂ) (comap Subtype.val (𝓝[≠] c)) (𝓝 c) :=
        tendsto_comap.mono_right nhdsWithin_le_nhds
      refine ((Asymptotics.isBigO_refl p _).mul_isLittleO (hn.comp_tendsto hv)).congr'
        (Eventually.of_forall fun w ↦ ?_) (Eventually.of_forall fun w ↦ ?_)
      · simp [g, hQ]
      · simp only [p, Function.comp_def, pow_succ, mul_inv_rev₀, mul_assoc,
          inv_mul_cancel₀, mul_one]
  have hg' (w : ℂ) (hw : w ≠ c) :
      g' w = Checked.inv ((w - c) ^ (n + 1)) ((sub_ne_zero.mpr hw).isUnit.pow _) *
        (f w - f c) := by
    simp only [g', g, update_of_ne hw, hQ (⟨w, hw⟩ : D), p]
  -- Finally, we apply the maximum modulus principle to this function.
  -- On the sphere `dist w c = R₁`, its norm is bounded by `R₂ / R₁ ^ (n + 1)`,
  -- thus it's bounded by the same constant on the whole closed ball,
  -- in particular, at `w = z`.
  suffices ‖g' z‖ ≤ R₂ / R₁ ^ (n + 1) by
    have hquot : ‖f z - f c‖ / ‖z - c‖ ^ (n + 1) ≤ R₂ / R₁ ^ (n + 1) := by
      simpa only [hg' z hne, inv_mul_eq_div₀, norm_div, norm_pow] using this
    have hz' : 0 < ‖z - c‖ ^ (n + 1) := pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne)) _
    calc
      ‖f z - f c‖ ≤ (R₂ / R₁ ^ (n + 1)) * ‖z - c‖ ^ (n + 1) := (div_le_iff₀ hz').mp hquot
      _ = _ := by rw [div_pow₀]; ring
  refine norm_le_of_forall_mem_frontier_norm_le isBounded_ball (hdg'.diffContOnCl_ball subset_rfl)
    ?_ ?_
  · grw [frontier_ball_subset_sphere]
    intro w hw
    have hwc := ne_of_mem_sphere hw hR₁.ne'
    have hfw : ‖f w - f c‖ ≤ R₂ := by
      simpa [dist_eq_norm] using h_maps (sphere_subset_closedBall hw)
    rw [mem_sphere_iff_norm] at hw
    calc
      ‖g' w‖ = ‖f w - f c‖ / R₁ ^ (n + 1) := by
        simp only [hg' w hwc, inv_mul_eq_div₀, norm_div, norm_pow, hw]
      _ ≤ _ := (div_le_div_iff_of_pos_right (pow_pos hR₁ _)).mpr hfw
  · exact subset_closure hz

public section

section NormedSpace

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
  {R R₁ R₂ : ℝ} {f : E → F} {c z : E}

open AffineMap in
/-- Let `f : E → F` be a complex analytic map
sending an open ball of radius `R₁` to a closed ball of radius `R₂`.
If `f w - f c = o(‖w - c‖ ^ n)`, then for any `z` in the ball in the domain,
we have `dist (f z) (f c) ≤ R₂ * (dist z c / R₁) ^ (n + 1)`.

For `n = 0`, this theorem gives a usual Schwarz lemma,
see `dist_le_div_mul_dist_of_mapsTo_ball` below.
-/
theorem dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO {f : E → F} {c z : E} {R₁ R₂ : ℝ} {n : ℕ}
    (hd : DifferentiableOn ℂ f (ball c R₁)) (h_maps : MapsTo f (ball c R₁) (closedBall (f c) R₂))
    (hn : (f · - f c) =o[𝓝 c] (fun w ↦ ‖w - c‖ ^ n)) (hz : z ∈ ball c R₁) :
    dist (f z) (f c) ≤ R₂ * (dist z c / R₁) ^ (n + 1) := by
  -- Note that `0 < R₁`, `0 ≤ R₂`, then discard the trivial case `f z = f c`.
  have hR₁ : 0 < R₁ := nonempty_ball.mp ⟨_, hz⟩
  have hR₂ : 0 ≤ R₂ := nonempty_closedBall.mp ⟨_, h_maps hz⟩
  rcases eq_or_ne (f z) (f c) with heq | hfne
  · trans 0 <;> [simp [heq]; positivity]
  have hne : z ≠ c := ne_of_apply_ne _ hfne
  -- Let `g : F → ℂ` be a continuous linear function such that `‖g‖ = 1`
  -- and `‖g (f z - f c)‖ = ‖f z - f c‖`.
  rcases exists_dual_vector ℂ _ (norm_sub_eq_zero_iff.not.mpr hfne) with ⟨g, hg, hgf⟩
  -- Consider `h : ℂ → ℂ` given by `h w = g (f (c + w * (z - c)))`.
  set h : ℂ → ℂ := g ∘ f ∘ lineMap c z
  -- This map is differentiable on the ball with center at the origin and radius `R₁ / dist z c`
  -- and it sends this ball to the closed ball with center `h 0 = f c` and radius R₂`.
  have hmaps_line : MapsTo (lineMap c z) (ball (0 : ℂ) (R₁ / dist z c)) (ball c R₁) := by
    intro w hw
    simpa [lt_div_iff₀, hne, dist_comm c] using hw
  have hmaps : MapsTo h (ball 0 (R₁ / dist z c)) (closedBall (h 0) R₂) := by
    refine MapsTo.comp ?_ (h_maps.comp hmaps_line)
    simpa [hg, h] using g.lipschitzWith.mapsTo_closedBall (f c) R₂
  have hdiff : DifferentiableOn ℂ h (ball 0 (R₁ / dist z c)) :=
    g.differentiable.comp_differentiableOn <| hd.comp (lineMap c z).differentiableOn hmaps_line
  -- This map also satisfies `h(w) - h(0) = o(w ^ n)`, thus we can apply the auxiliary lemma above.
  have hn : (h · - h 0) =o[𝓝 0] (fun w ↦ (w - 0) ^ n) := by
    simp only [h, ← map_sub, Function.comp_apply, sub_zero]
    refine (g.isBigO_comp _ _).trans_isLittleO ?_
    rw [← lineMap_apply_zero (k := ℂ) c z] at hn
    refine hn.comp_tendsto ?_ |>.trans_isBigO ?_
    · exact Continuous.tendsto (by fun_prop) 0
    · simpa [Function.comp_def, ← dist_eq_norm_sub, mul_pow, mul_comm]
        using (Asymptotics.isBigO_refl (· ^ n) (𝓝 (0 : ℂ))).norm_left.const_mul_left _
  have hmem : 1 ∈ ball (0 : ℂ) (R₁ / dist z c) := by
    simpa [lt_div_iff₀, hne]
  rw [map_sub] at hgf
  simpa [hgf, h, dist_eq_norm_sub] using schwarz_aux hdiff hmaps hn hmem

/-- The **Schwarz Lemma**. Let `f : E → F` be a complex analytic function
on an open ball with center `c` and radius `R₁`.
If `f` sends this ball to a closed ball with center `f c` and radius `R₂`,
then for any `z` in the former ball we have `dist (f z) (f c) ≤ (R₂ / R₁) * dist z c`.
-/
theorem dist_le_div_mul_dist_of_mapsTo_ball (hd : DifferentiableOn ℂ f (ball c R₁))
    (h_maps : MapsTo f (ball c R₁) (closedBall (f c) R₂)) (hz : z ∈ ball c R₁) :
    dist (f z) (f c) ≤ R₂ / R₁ * dist z c := by
  refine dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO (n := 0) hd h_maps ?_ hz |>.trans_eq ?_
  · simpa using hd.continuousOn.continuousAt
      (ball_mem_nhds _ <| nonempty_ball.mp ⟨_, hz⟩) |>.sub_const (f c)
  · rw [pow_one, ← mul_div_assoc₀, div_mul_eq_mul_div₀]

/-- The **Schwarz Lemma**. Let `f : E → F` be a complex analytic function
on an open ball with center `c` and positive radius `R₁`.
If `f` sends this ball to a closed ball with center `f c` and radius `R₂`,
then the norm of the Fréchet derivative of `f` at `c` is at most `R₂ / R₁`.
-/
theorem norm_fderiv_le_div_of_mapsTo_ball (hd : DifferentiableOn ℂ f (ball c R₁))
    (h_maps : MapsTo f (ball c R₁) (closedBall (f c) R₂)) (h₀ : 0 < R₁) :
    ‖fderiv ℂ f c‖ ≤ R₂ / R₁ := by
  have : 0 ≤ R₂ := nonempty_closedBall.mp <| h_maps.nonempty <| nonempty_ball.mpr h₀
  refine norm_fderiv_le_of_lip' _ (by positivity) ?_
  filter_upwards [ball_mem_nhds _ h₀] with z hz
  simpa [dist_eq_norm_sub] using dist_le_div_mul_dist_of_mapsTo_ball hd h_maps hz

/-- The **Schwarz Lemma**. Let `f : E → F` be a complex analytic function
on an open ball with center `c`.
If `f` sends this ball to a closed ball with center `f c` and the same radius,
then for any `z` in the former ball we have `dist (f z) (f c) ≤ dist z c`.
-/
theorem dist_le_dist_of_mapsTo_ball (hd : DifferentiableOn ℂ f (ball c R))
    (h_maps : MapsTo f (ball c R) (closedBall (f c) R)) (hz : z ∈ ball c R) :
    dist (f z) (f c) ≤ dist z c := by
  simpa [(nonempty_ball.1 ⟨z, hz⟩).ne'] using dist_le_div_mul_dist_of_mapsTo_ball hd h_maps hz

/-- The **Schwarz Lemma**. Let `f : E → F` be a complex analytic function
on an open ball with center `c` and a positive radius.
If `f` sends this ball to a closed ball with center `f c` and the same radius,
then the norm of the Fréchet derivative of `f` at `c` is at most one.
-/
theorem norm_fderiv_le_one_of_mapsTo_ball (hd : DifferentiableOn ℂ f (ball c R))
    (h_maps : MapsTo f (ball c R) (closedBall (f c) R)) (hR : 0 < R) :
    ‖fderiv ℂ f c‖ ≤ 1 := by
  simpa [hR.ne'] using norm_fderiv_le_div_of_mapsTo_ball hd h_maps hR

/-- The **Schwarz Lemma**.
Let `f : E → F` be a complex analytic on an open ball with center at the origin.
If `f` sends this ball to the closed ball with center `0` of the same radius and `f 0 = 0`,
then for any point `z` of this disk we have `‖f z‖ ≤ ‖z‖`. -/
theorem norm_le_norm_of_mapsTo_ball (hd : DifferentiableOn ℂ f (ball 0 R))
    (h_maps : MapsTo f (ball 0 R) (closedBall 0 R)) (h₀ : f 0 = 0) (hz : ‖z‖ < R) :
    ‖f z‖ ≤ ‖z‖ := by
  simpa [h₀] using dist_le_dist_of_mapsTo_ball hd (by rwa [h₀]) (mem_ball_zero_iff.mpr hz)

end NormedSpace

section DimOne

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {R R₁ R₂ : ℝ} {f : ℂ → E}
  {c z z₀ : ℂ}

/-- The **Schwarz Lemma**: if `f : ℂ → E` is complex analytic
on an open disk with center `c` and a positive radius `R₁`,
and it sends this disk to a closed ball with center `f c` and radius `R₂`,
then the norm of the derivative of `f` at `c` is at most the ratio `R₂ / R₁`. -/
theorem norm_deriv_le_div_of_mapsTo_ball (hd : DifferentiableOn ℂ f (ball c R₁))
    (h_maps : MapsTo f (ball c R₁) (closedBall (f c) R₂)) (h₀ : 0 < R₁) :
    ‖deriv f c‖ ≤ R₂ / R₁ := by
  rw [norm_deriv_eq_norm_fderiv]
  exact norm_fderiv_le_div_of_mapsTo_ball hd h_maps h₀

/-- The **Schwarz Lemma**: if `f : ℂ → E` is complex analytic
on an open disk with center `c` and a positive radius `R₁`,
and it sends this disk to a closed ball with center `f c` and radius the same radius,
then the norm of the derivative of `f` at the center of this disk is at most `1`.
-/
theorem norm_deriv_le_one_of_mapsTo_ball (hd : DifferentiableOn ℂ f (ball c R))
    (h_maps : MapsTo f (ball c R) (closedBall (f c) R)) (h₀ : 0 < R) : ‖deriv f c‖ ≤ 1 :=
  (norm_deriv_le_div_of_mapsTo_ball hd h_maps h₀).trans_eq div_self

/-- Two cases of the **Schwarz Lemma** (derivative and distance), merged together.

If `f : ℂ → E` is a complex analytic function on an open ball `ball c R₁`
hat sends it to a closed ball `closedBall (f c) R₂`, then the norm of `dslope f c z`,
which is defined as `(z - c)⁻¹ • (f z - f c)` for `z ≠ c` and as `deriv f c` for `z = c`,
is not greater than the ratio `R₂ / R₁`.
-/
theorem norm_dslope_le_div_of_mapsTo_ball (hd : DifferentiableOn ℂ f (ball c R₁))
    (h_maps : MapsTo f (ball c R₁) (closedBall (f c) R₂)) (hz : z ∈ ball c R₁) :
    ‖dslope f c z‖ ≤ R₂ / R₁ := by
  rcases eq_or_ne z c with rfl | hne
  · simpa using norm_deriv_le_div_of_mapsTo_ball hd h_maps (by simpa using hz)
  · rw [dslope_of_ne _ hne, slope_def_module]
    simp only [norm_smul, norm_inv, inv_mul_eq_div₀]
    refine (div_le_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hne))).2 ?_
    simpa only [dist_eq_norm] using dist_le_div_mul_dist_of_mapsTo_ball hd h_maps hz

/-- Equality case in the **Schwarz Lemma**: in the setup of `norm_dslope_le_div_of_mapsTo_ball`,
if `‖dslope f c z₀‖ = R₂ / R₁` holds at a point in the ball
then the map `f` is affine with slope `dslope f c z₀`.

Note that this lemma requires the codomain to be a strictly convex space.
Indeed, for `E = ℂ × ℂ` there is a counterexample:
the map `f := fun z ↦ (z, z ^ 2)` sends `ball 0 1` to `closedBall 0 1`,
`‖dslope f 0 0‖ = ‖deriv f 0‖ = ‖(1, 0)‖ = 1`, but the map is not an affine map.
-/
theorem affine_of_mapsTo_ball_of_norm_dslope_eq_div [StrictConvexSpace ℝ E]
    (hd : DifferentiableOn ℂ f (ball c R₁))
    (h_maps : Set.MapsTo f (ball c R₁) (closedBall (f c) R₂))
    (h_z₀ : z₀ ∈ ball c R₁) (h_eq : ‖dslope f c z₀‖ = R₂ / R₁) :
    Set.EqOn f (fun z => f c + (z - c) • dslope f c z₀) (ball c R₁) := by
  set e : E →L[ℂ] UniformSpace.Completion E := UniformSpace.Completion.toComplL
  set g := dslope (e ∘ f) c
  rintro z hz
  have h_R₁ : 0 < R₁ := nonempty_ball.mp ⟨_, h_z₀⟩
  have hg' : g = e ∘ dslope f c := by
    ext w
    simp only [g]
    rw [e.dslope_comp, Function.comp_apply]
    rintro rfl
    exact hd.differentiableAt <| ball_mem_nhds _ h_R₁
  have g_le_div : ∀ z ∈ ball c R₁, ‖g z‖ ≤ R₂ / R₁ := fun z hz =>
    norm_dslope_le_div_of_mapsTo_ball (e.differentiable.comp_differentiableOn hd)
      (fun w hw ↦ by simpa [e] using h_maps hw) hz
  have g_max : IsMaxOn (norm ∘ g) (ball c R₁) z₀ :=
    isMaxOn_iff.mpr fun z hz => by simpa [h_eq, hg', e] using g_le_div z hz
  have g_diff : DifferentiableOn ℂ g (ball c R₁) :=
    (differentiableOn_dslope (isOpen_ball.mem_nhds (mem_ball_self h_R₁))).mpr
      (e.differentiable.comp_differentiableOn hd)
  have heq : ‖dslope f c z‖ = ‖dslope f c z₀‖ := by
    simpa [hg', e] using norm_eqOn_of_isPreconnected_of_isMaxOn (convex_ball c R₁).isPreconnected
      isOpen_ball g_diff h_z₀ g_max hz
  have heq_add : ‖dslope f c z + dslope f c z₀‖ = ‖dslope f c z₀ + dslope f c z₀‖ := by
    simpa [hg', e, ← UniformSpace.Completion.coe_add]
      using norm_eqOn_of_isPreconnected_of_isMaxOn (convex_ball c R₁).isPreconnected
        isOpen_ball (g_diff.add_const (g z₀)) h_z₀ g_max.norm_add_self hz
  have : dslope f c z = dslope f c z₀ := eq_of_norm_eq_of_norm_add_eq heq <| by
    simp only [heq, SameRay.rfl.norm_add, heq_add]
  simp [← this]

/-- Equality case in the **Schwarz Lemma**: in the setup of `norm_dslope_le_div_of_mapsTo_ball`,
if there exists a point `z₀` in the ball such that `‖dslope f c z₀‖ = R₂ / R₁`,
then the map `f` is affine with the absolute value of the slope equal to `R₂ / R₁`.

This is an existence version of `affine_of_mapsTo_ball_of_norm_dslope_eq_div` above.

TODO: once the deprecated alias `affine_of_mapsTo_ball_of_exists_norm_dslope_eq_div` is gone,
rename this theorem to `affine_of_mapsTo_ball_of_exists_norm_dslope_eq_div`.
-/
theorem affine_of_mapsTo_ball_of_exists_norm_dslope_eq_div'
    [StrictConvexSpace ℝ E] (hd : DifferentiableOn ℂ f (ball c R₁))
    (h_maps : Set.MapsTo f (ball c R₁) (closedBall (f c) R₂))
    (h_z₀ : ∃ z₀ : ball c R₁, ‖dslope f c z₀.val‖ =
      Checked.div R₂ R₁ (pos_of_mem_ball z₀.2).ne'.isUnit) :
    ∃ C : E, ‖C‖ = Checked.div R₂ R₁ (pos_of_mem_ball h_z₀.choose.2).ne'.isUnit ∧
      Set.EqOn f (fun z => f c + (z - c) • C) (ball c R₁) :=
  ⟨dslope f c h_z₀.choose.val, h_z₀.choose_spec,
    affine_of_mapsTo_ball_of_norm_dslope_eq_div hd h_maps h_z₀.choose.2 h_z₀.choose_spec⟩

end DimOne

end -- public section

end Complex
