/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, David Loeffler
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Geometry.Manifold.Algebra.Structures
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
public import Mathlib.LinearAlgebra.Complex.Determinant
public import Mathlib.RingTheory.Complex
public import Mathlib.RingTheory.Norm.Transitivity

/-!
# Manifold structure on the upper half plane.

In this file we define the complex manifold structure on the upper half-plane, and show it is
invariant under Moebius transformations. We also calculate the derivative, and give an explicit
formula for its Jacobian determinant over `ℝ` (used in proving that the action preserves
a suitable measure).
-/

@[expose] public section

open Filter

open scoped Manifold ContDiff MatrixGroups Topology

variable {n : ℕ∞ω}

namespace UpperHalfPlane

noncomputable instance : ChartedSpace ℂ ℍ :=
  isOpenEmbedding_coe.singletonChartedSpace

instance : IsManifold 𝓘(ℂ) ω ℍ :=
  isOpenEmbedding_coe.isManifold_singleton

/-- The inclusion map `ℍ → ℂ` is a map of `C^n` manifolds. -/
theorem contMDiff_coe : CMDiff n ((↑) : ℍ → ℂ) :=
  fun _ => contMDiffAt_extChartAt

/-- The inclusion map `ℍ → ℂ` is a differentiable map of manifolds. -/
theorem mdifferentiable_coe : MDiff ((↑) : ℍ → ℂ) :=
  contMDiff_coe.mdifferentiable one_ne_zero

lemma contMDiffAt_ofComplex {z : ℂ} (hz : 0 < z.im) : CMDiffAt n ofComplex z := by
  rw [contMDiffAt_iff]
  constructor
  · -- continuity at z
    rw [ContinuousAt, nhds_induced, tendsto_comap_iff]
    refine Tendsto.congr' (eventuallyEq_coe_comp_ofComplex hz).symm ?_
    simpa [ofComplex_apply_of_im_pos hz] using! tendsto_id
  · -- smoothness in local chart
    simpa using! contDiffAt_id.congr_of_eventuallyEq (eventuallyEq_coe_comp_ofComplex hz)

lemma mdifferentiableAt_ofComplex {z : ℂ} (hz : 0 < z.im) : MDiffAt ofComplex z :=
  (contMDiffAt_ofComplex hz).mdifferentiableAt one_ne_zero

lemma contMDiffAt_iff {f : ℍ → ℂ} {τ : ℍ} :
    CMDiffAt n f τ ↔ ContDiffAt ℂ n (f ∘ ofComplex) τ := by
  rw [← contMDiffAt_iff_contDiffAt]
  refine ⟨fun hf ↦ ?_, fun hf ↦ ?_⟩
  · exact (ofComplex_apply τ ▸ hf).comp _ (contMDiffAt_ofComplex τ.im_pos)
  · simpa only [Function.comp_def, ofComplex_apply] using hf.comp τ (contMDiff_coe τ)

lemma mdifferentiableAt_iff {f : ℍ → ℂ} {τ : ℍ} :
    MDiffAt f τ ↔ DifferentiableAt ℂ (f ∘ ofComplex) ↑τ := by
  rw [← mdifferentiableAt_iff_differentiableAt]
  refine ⟨fun hf ↦ ?_, fun hf ↦ ?_⟩
  · exact (ofComplex_apply τ ▸ hf).comp _ (mdifferentiableAt_ofComplex τ.im_pos)
  · simpa only [Function.comp_def, ofComplex_apply] using hf.comp τ (mdifferentiable_coe τ)

lemma mdifferentiable_iff {f : ℍ → ℂ} :
    MDiff f ↔ DifferentiableOn ℂ (f ∘ ofComplex) {z | 0 < z.im} :=
  ⟨fun h z hz ↦ (mdifferentiableAt_iff.mp (h ⟨z, hz⟩)).differentiableWithinAt,
    fun h ⟨z, hz⟩ ↦ mdifferentiableAt_iff.mpr <| (h z hz).differentiableAt
     <| isOpen_upperHalfPlaneSet.mem_nhds hz⟩

lemma contMDiff_num (g : GL (Fin 2) ℝ) : CMDiff n (fun τ : ℍ ↦ num g τ) :=
  (contMDiff_const.mul contMDiff_coe).add contMDiff_const

lemma contMDiff_denom (g : GL (Fin 2) ℝ) : CMDiff n (fun τ : ℍ ↦ denom g τ) :=
  (contMDiff_const.mul contMDiff_coe).add contMDiff_const

lemma contMDiff_inv_denom (g : GL (Fin 2) ℝ) : CMDiff n (fun τ : ℍ ↦ (denom g τ)⁻¹) :=
  (contMDiff_denom g).inv₀ (h := fun τ ↦ (denom_ne_zero g τ).isUnit)

lemma contMDiff_denom_zpow (g : GL (Fin 2) ℝ) (k : ℤ) : CMDiff n (denom g · ^ k : ℍ → ℂ) := by
  cases k with
  | ofNat k =>
    simpa only [Int.ofNat_eq_natCast, zpow_natCast₀] using (contMDiff_denom g).pow k
  | negSucc k =>
    simpa only [zpow_negSucc₀, inv_pow₀] using (contMDiff_inv_denom g).pow (k + 1)

/-- Each element of `GL(2, ℝ)⁺` defines a map of `C ^ n` manifolds `ℍ → ℍ`. -/
lemma contMDiff_smul {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val) : CMDiff n (fun τ : ℍ ↦ g • τ) := by
  intro τ
  refine contMDiffAt_iff_target.mpr ⟨(continuous_const_smul g).continuousAt, ?_⟩
  simpa [glPos_smul_def hg] using! (contMDiff_num g τ).mul (contMDiff_inv_denom g τ)

lemma mdifferentiable_num (g : GL (Fin 2) ℝ) : MDiff (fun τ : ℍ ↦ num g τ) :=
  (contMDiff_num g).mdifferentiable one_ne_zero

lemma mdifferentiable_denom (g : GL (Fin 2) ℝ) : MDiff (fun τ : ℍ ↦ denom g τ) :=
  (contMDiff_denom g).mdifferentiable one_ne_zero

lemma mdifferentiable_denom_zpow (g : GL (Fin 2) ℝ) (k : ℤ) : MDiff (denom g · ^ k : ℍ → ℂ) :=
  (contMDiff_denom_zpow g k).mdifferentiable one_ne_zero

lemma mdifferentiable_inv_denom (g : GL (Fin 2) ℝ) : MDiff (fun τ : ℍ ↦ (denom g τ)⁻¹) :=
  (contMDiff_inv_denom g).mdifferentiable one_ne_zero

/-- Each element of `GL(2, ℝ)⁺` defines a complex-differentiable map `ℍ → ℍ`. -/
lemma mdifferentiable_smul {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val) : MDiff (fun τ : ℍ ↦ g • τ) :=
  (contMDiff_smul hg).mdifferentiable one_ne_zero

lemma eq_zero_of_frequently {f : ℍ → ℂ} (hf : MDiff f) {τ : ℍ} (hτ : ∃ᶠ z in 𝓝[≠] τ, f z = 0) :
    f = 0 := by
  rw [mdifferentiable_iff] at hf
  have := hf.analyticOnNhd isOpen_upperHalfPlaneSet
  ext w
  convert! this.eqOn_zero_of_preconnected_of_frequently_eq_zero (z₀ := ↑τ) ?_ τ.2 ?_ w.im_pos
  · rw [Function.comp_apply, ofComplex_apply]
  · exact (Complex.isConnected_of_upperHalfPlane subset_rfl (by grind)).isPreconnected
  · contrapose! hτ
    rw [eventually_nhdsWithin_iff, ← isOpenEmbedding_coe.map_nhds_eq, eventually_map] at hτ
    rw [eventually_nhdsWithin_iff]
    filter_upwards [hτ] with a ha
    simpa using ha

lemma mul_eq_zero_iff {f g : ℍ → ℂ} (hf : MDiff f) (hg : MDiff g) : f * g = 0 ↔ f = 0 ∨ g = 0 :=
  ⟨fun hfg ↦ (frequently_or_distrib.mp <| .of_forall <| by simpa using congrFun hfg).imp
    (eq_zero_of_frequently (τ := I) hf) (eq_zero_of_frequently hg), by grind⟩

lemma prod_eq_zero_iff {ι : Type*} {f : ι → ℍ → ℂ} {s : Finset ι}
    (hf : ∀ i ∈ s, MDiff (f i)) :
    ∏ i ∈ s, f i = 0 ↔ ∃ i ∈ s, f i = 0 := by
  refine ⟨fun h0 ↦ ?_, fun ⟨i, hi, hi'⟩ ↦ Finset.prod_eq_zero hi hi'⟩
  have : ∃ᶠ τ in 𝓝[≠] I, ∏ i ∈ s, f i τ = 0 := .of_forall <| by simpa using congrFun h0
  simp only [Finset.prod_eq_zero_iff, Finset.frequently_exists] at this
  exact this.imp fun i hi ↦ ⟨hi.1, eq_zero_of_frequently (hf i hi.1) hi.2⟩

section deriv
/-!
## Explicit calculations of the derivative of `τ ↦ g • τ`

TODO: would it be better to reimplement these using `mfderiv` together with a trivialization of
the tangent space of `ℍ`, rather than using `ofComplex` as we currently do? Or would that bring
more pain than gain?

TODO(MR): investigate if using `mvfderiv` can avoid the "pain" above, and be a cleaner design!
-/

section Complex

/-- The derivative of a function defined near an upper-half-plane point can be checked on
its restriction to the upper half-plane. -/
lemma hasDerivAt_of_restrict {f : ℂ → ℂ} {d : ℂ} {τ : ℍ}
    (h : HasDerivAt (fun z : ℍ ↦ f z) d τ ((↑) : ℍ → ℂ)) : HasDerivAt f d (τ : ℂ) := by
  rw [hasDerivAt_iff_hasFDerivAt, hasFDerivAt_iff_isLittleOTVS,
    ← isOpenEmbedding_coe.map_nhds_eq, Asymptotics.isLittleOTVS_map]
  exact h.hasFDerivAt.isLittleOTVS

/-- Derivative of `z ↦ (denom g z) ^ k`: $\frac{d}{dz}[(cz+d)^k] = k \cdot c \cdot (cz+d)^{k-1}$. -/
lemma hasDerivAt_denom_zpow (g : GL (Fin 2) ℝ) (k : ℤ) (τ : ℍ) :
    HasDerivAt (fun z : ℍ ↦ Checked.zpow (denom g z) k
      (fun _ ↦ (denom_ne_zero g z).isUnit))
      ((k : ℂ) * (g 1 0 : ℂ) * Checked.zpow (denom g τ) (k - 1)
        (fun _ ↦ (denom_ne_zero g τ).isUnit)) τ ((↑) : ℍ → ℂ) := by
  have hd : HasDerivAt (fun z : ℂ ↦ denom g z) (g 1 0 : ℂ) (τ : ℂ) := by
    simpa [denom] using (((hasDerivAt_id (τ : ℂ)).const_mul (g 1 0 : ℂ)).add_const (g 1 1 : ℂ))
  let D := {z : ℂ // k < 0 → IsUnit (denom g z)}
  let q (z : ℍ) : D := ⟨z, fun _ ↦ (denom_ne_zero g z).isUnit⟩
  have hq : Continuous q := continuous_coe.subtype_mk _
  have hpull := (hd.zpow k (q τ).property).hasFDerivAt.comp_tendsto q
    (hq.continuousAt.tendsto.prodMap (tendsto_pure_pure q τ))
  have h := hasFDerivAtFilter_iff_hasDerivAtFilter.mp hpull
  unfold HasDerivAt
  by_cases hk : k = 0
  · subst k
    simpa only [q, Function.comp_def, id_eq, zpow_zero₀,
      ContinuousLinearMap.toSpanSingleton_apply, one_smul, dite_true, Int.cast_zero, zero_mul]
      using h
  · simpa only [q, Function.comp_def, id_eq, ContinuousLinearMap.toSpanSingleton_apply,
      one_smul, dite_eq_right hk, mul_right_comm] using h

/-- Derivative of `z ↦ (denom g z) ^ k`:
$\frac{d}{dz}[(cz+d)^k] = k \cdot c \cdot (cz+d)^{k-1}$. -/
lemma deriv_denom_zpow (g : GL (Fin 2) ℝ) (k : ℤ) (τ : ℍ) :
    deriv (fun z : ℍ ↦ Checked.zpow (denom g z) k
      (fun _ ↦ (denom_ne_zero g z).isUnit)) τ ((↑) : ℍ → ℂ) =
      (k : ℂ) * (g 1 0 : ℂ) * Checked.zpow (denom g τ) (k - 1)
        (fun _ ↦ (denom_ne_zero g τ).isUnit) :=
  (hasDerivAt_denom_zpow g k τ).deriv isOpenEmbedding_coe

lemma analyticAt_smul {g : GL (Fin 2) ℝ} (hg : 0 < g.val.det) (τ : ℍ) :
    AnalyticAt ℂ (fun z : ℂ ↦ (↑(g • ofComplex z) : ℂ)) (τ : ℂ) := by
  refine DifferentiableOn.analyticAt (fun z hz ↦ ?_) (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)
  apply DifferentiableAt.differentiableWithinAt
  simpa [mdifferentiableAt_iff] using!
    (mdifferentiable_coe.comp <| (mdifferentiable_smul hg)).mdifferentiableAt (x := ⟨z, hz⟩)

lemma hasStrictDerivAt_smul {g : GL (Fin 2) ℝ} (hg : 0 < g.val.det) (τ : ℍ) :
    HasStrictDerivAt (fun z : ℂ ↦ (↑(g • ofComplex z) : ℂ))
      (Checked.div (g.val.det : ℂ) (denom g τ ^ 2) ((isUnit_denom g τ).pow 2)) (τ : ℂ) := by
  let f (z : ℂ) : ℂ := ↑(g • ofComplex z)
  let d := Checked.div (g.val.det : ℂ) (denom g τ ^ 2) ((isUnit_denom g τ).pow 2)
  have hnum : HasDerivAt (fun z : ℂ ↦ num g z) (g 0 0 : ℂ) (τ : ℂ) := by
    simpa [num] using (((hasDerivAt_id (τ : ℂ)).const_mul (g 0 0 : ℂ)).add_const (g 0 1 : ℂ))
  have hden : HasDerivAt (fun z : ℂ ↦ denom g z) (g 1 0 : ℂ) (τ : ℂ) := by
    simpa [denom] using (((hasDerivAt_id (τ : ℂ)).const_mul (g 1 0 : ℂ)).add_const (g 1 1 : ℂ))
  let D := {z : ℂ | IsUnit (denom g z)}
  let q (z : ℍ) : D := ⟨z, isUnit_denom g z⟩
  have hq : Continuous q := continuous_coe.subtype_mk _
  have hpull := (hnum.div hden (isUnit_denom g τ)).hasFDerivAt.comp_tendsto q
    (hq.continuousAt.tendsto.prodMap (tendsto_pure_pure q τ))
  have hdet : (g 0 0 : ℂ) * denom g τ - num g τ * (g 1 0 : ℂ) = (g.val.det : ℂ) := by
    simp [num, denom, Matrix.det_fin_two]
    ring
  have hunit : (isUnit_denom g τ).unit ^ 2 = ((isUnit_denom g τ).pow 2).unit := Units.ext (by simp)
  have hf (z : ℍ) : f z = num g z /ₚ (isUnit_denom g z).unit := by
    change (↑(g • ofComplex (z : ℂ)) : ℂ) = _
    rw [ofComplex_apply, coe_smul_of_det_pos hg]
    rfl
  have hd : HasDerivAt f d (τ : ℂ) := by
    apply hasDerivAt_of_restrict
    change HasDerivAt (fun z : ℍ ↦ f z)
      ((g.val.det : ℂ) /ₚ ((isUnit_denom g τ).pow 2).unit) τ ((↑) : ℍ → ℂ)
    unfold HasDerivAt
    simpa only [hf, q, Function.comp_def, id_eq, ContinuousLinearMap.toSpanSingleton_apply,
      one_smul, hdet, hunit] using (hasFDerivAtFilter_iff_hasDerivAtFilter.mp hpull)
  have h := (analyticAt_smul hg τ).hasStrictDerivAt
  change HasStrictDerivAt f (deriv f (τ : ℂ)) (τ : ℂ) at h
  rw [hd.deriv] at h
  exact h

lemma deriv_smul {g : GL (Fin 2) ℝ} (hg : 0 < g.val.det) (τ : ℍ) :
    deriv (fun z : ℂ ↦ (↑(g • ofComplex z) : ℂ)) (τ : ℂ) =
      Checked.div (g.val.det : ℂ) (denom g τ ^ 2) ((isUnit_denom g τ).pow 2) :=
  hasStrictDerivAt_smul hg τ |>.hasDerivAt |>.deriv

lemma deriv_smul_ne_zero {g : GL (Fin 2) ℝ} (hg : 0 < g.val.det) (τ : ℍ) :
    deriv (fun z ↦ ↑(g • ofComplex z) : ℂ → ℂ) τ ≠ 0 := by
  rw [deriv_smul hg]
  exact div_ne_zero (by exact_mod_cast hg.ne')

/-- If `f` is meromorphic at `g • τ`, then `z ↦ f (g • z)` is meromorphic at `τ`. -/
lemma meromorphicAt_comp_smul {f : ℍ → ℂ} {τ : ℍ} {g : GL (Fin 2) ℝ} (hg : 0 < g.val.det)
    (hf : MeromorphicAt (fun z ↦ f (ofComplex z)) (↑(g • τ) : ℂ)) :
    MeromorphicAt (fun z ↦ f (g • ofComplex z)) (τ : ℂ) := by
  have : (fun z : ℂ ↦ f (g • ofComplex z)) =
      (fun z ↦ f (ofComplex z)) ∘ (fun z ↦ ↑(g • ofComplex z) : ℂ → ℂ) := by
    ext; simp
  rw [this]
  exact .comp_analyticAt (by simpa using hf) (τ.analyticAt_smul hg)

lemma meromorphicOrderAt_comp_smul {f : ℍ → ℂ} {τ : ℍ} {g : GL (Fin 2) ℝ} (hg : 0 < g.val.det)
    (hf : MeromorphicAt (fun z ↦ f (ofComplex z)) (↑(g • τ) : ℂ)) :
    meromorphicOrderAt (fun z ↦ f (g • ofComplex z)) (τ : ℂ) (meromorphicAt_comp_smul hg hf) =
      meromorphicOrderAt (fun z ↦ f (ofComplex z)) (↑(g • τ) : ℂ) hf := by
  let G z : ℂ := ↑(g • ofComplex z)
  let F z := f (ofComplex z)
  have hF : MeromorphicAt F (G τ) := by simpa [F, G] using hf
  have : (fun z : ℂ ↦ f (g • ofComplex z)) = F ∘ G := by ext; simp [F, G]
  rw [meromorphicOrderAt_congr _ (.of_eq this),
    meromorphicOrderAt_comp_of_deriv_ne_zero hF (τ.analyticAt_smul hg) (τ.deriv_smul_ne_zero hg)]
  congr 1
  simp [G]

end Complex


section Real

/-- `ℝ`-linear map from `ℂ` to itself, which we shall show is the real derivative of the
`GL(2, ℝ)`-action on `ℍ`. -/
noncomputable def smulFDeriv (g : GL (Fin 2) ℝ) (τ : ℍ) : ℂ →L[ℝ] ℂ :=
  (σ g) ∘L (ContinuousLinearMap.toSpanSingleton ℂ
    (Checked.div (g.det.val : ℂ) (denom g τ ^ 2) ((isUnit_denom g τ).pow 2))).restrictScalars ℝ

@[simp]
theorem smulFDeriv_J_mul (g : GL (Fin 2) ℝ) (τ : ℍ) :
    smulFDeriv (J * g) τ = -Complex.conjCLE ∘L smulFDeriv g τ := by
  ext
  by_cases hg : 0 < g.val.det
  · simp [smulFDeriv, σ, hg, hg.not_gt, neg_div₀]
  · simp [smulFDeriv, σ, hg, g.det_ne_zero.lt_or_gt.resolve_right hg, neg_div₀]

/-- Determinant of the derivative of `g : ℍ → ℍ` considered as an `ℝ`-linear map. This is used in
the proof that the action is measure-preserving. Note this formula applies for both orientation-
preserving and orientation-reserving isometries. -/
lemma det_smulFDeriv (g : GL (Fin 2) ℝ) (τ : ℍ) :
    (smulFDeriv g τ).det =
      Checked.div ((SignType.sign g.det.val : ℝ) * g.det.val ^ 2) (‖denom g τ‖ ^ 4)
        ((norm_ne_zero_iff.2 (denom_ne_zero g τ)).isUnit.pow 4) := by
  simp only [smulFDeriv, σ]
  rcases g.det_ne_zero.lt_or_gt with h | h
  · simp [h.not_gt, ContinuousLinearMap.det, LinearMap.det_restrictScalars,
      Algebra.norm_complex_eq, Complex.normSq_eq_norm_sq, ← pow_mul, sign_neg h, neg_div₀]
  · simp [ContinuousLinearMap.det, h, LinearMap.det_restrictScalars,
      Algebra.norm_complex_eq, Complex.normSq_eq_norm_sq, ← pow_mul]

lemma hasStrictFDerivAt_smul (g : GL (Fin 2) ℝ) (τ : ℍ) :
    HasStrictFDerivAt (fun z ↦ ↑(g • ofComplex z) : ℂ → ℂ) (smulFDeriv g τ) τ := by
  wlog hg : 0 < g.det.val generalizing g
  · replace hg := g.det.ne_zero.lt_or_gt.resolve_right hg
    convert! Complex.conjCLE.hasStrictFDerivAt.neg.comp _ (this (J * g) (by simpa))
    · simp [mul_smul, coe_J_smul]
    · ext
      simp
  have := (hasStrictDerivAt_smul hg τ).hasStrictFDerivAt.restrictScalars ℝ
  simp_all [smulFDeriv, σ]

end Real

end deriv

end UpperHalfPlane
