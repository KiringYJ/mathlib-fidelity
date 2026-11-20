/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Normed.Module.Ball.Action
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.Instances.Real
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Tactic.Module

/-!
# Manifold structure on the sphere

This file defines stereographic projection from the sphere in an inner product space `E`, and uses
it to put an analytic manifold structure on the sphere.

## Main results

For a unit vector `v` in `E`, the definition `stereographic` gives the stereographic projection
centred at `v`, an open partial homeomorphism from the sphere to `(ℝ ∙ v)ᗮ` (the orthogonal
complement of `v`). The forward formula is defined off the pole. The reverse chart is defined on
the whole orthogonal complement and sends zero to the antipode.

For finite-dimensional `E`, we then construct an analytic manifold instance on the sphere; the
charts here are obtained by composing the open partial homeomorphisms `stereographic` with arbitrary
isometries from `(ℝ ∙ v)ᗮ` to Euclidean space.

We prove two lemmas about `C^n` maps:
* `contMDiff_coe_sphere` states that the coercion map from the sphere into `E` is analytic;
  this is a useful tool for constructing smooth maps *from* the sphere.
* `contMDiff.codRestrict_sphere` states that a map from a manifold into the sphere is
  `C^m` if its lift to a map to `E` is `C^m`; this is a useful tool for constructing `C^m` maps
  *to* the sphere.

As an application we prove `contMDiffNegSphere`, that the antipodal map is analytic.

Finally, we equip the `Circle` (defined in `Analysis.Complex.Circle` to be the sphere in `ℂ`
centred at `0` of radius `1`) with the following structure:
* a charted space with model space `EuclideanSpace ℝ (Fin 1)` (inherited from `Metric.Sphere`)
* an analytic Lie group with model with corners `𝓡 1`

We furthermore show that `Circle.exp` (defined in `Analysis.Complex.Circle` to be the natural
map `fun t ↦ exp (t * I)` from `ℝ` to `Circle`) is analytic.


## Implementation notes

The model space for the charted space instance is `EuclideanSpace ℝ (Fin n)`, where `n` is a
natural number satisfying the typeclass assumption `[Fact (finrank ℝ E = n + 1)]`.  This may seem a
little awkward, but it is designed to circumvent the problem that the literal expression for the
dimension of the model space (up to definitional equality) determines the type.  If one used the
naive expression `EuclideanSpace ℝ (Fin (finrank ℝ E - 1))` for the model space, then the sphere in
`ℂ` would be a manifold with model space `EuclideanSpace ℝ (Fin (2 - 1))` but not with model space
`EuclideanSpace ℝ (Fin 1)`.

## TODO

Relate the stereographic projection to the inversion of the space.
-/

@[expose] public section


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable section

open Metric Module Function Filter Topology
open scoped Topology

open scoped Manifold ContDiff RealInnerProductSpace

section StereographicProjection

variable (v : E)

/-! ### Construction of the stereographic projection -/


/-- The open domain of the ambient stereographic formula. -/
def stereoDomain : TopologicalSpace.Opens E :=
  ⟨{x | innerSL ℝ v x ≠ 1}, isOpen_ne_fun (innerSL ℝ v).continuous continuous_const⟩

/-- The scalar multiplying the orthogonal projection in stereographic coordinates. -/
def stereoCoeff {v : E} (x : stereoDomain v) : ℝ :=
  Checked.div 2 (1 - innerSL ℝ v x.val) (sub_ne_zero.mpr x.2.symm).isUnit

lemma stereoCoeff_mul {v : E} (x : stereoDomain v) :
    stereoCoeff x * (1 - innerSL ℝ v x.val) = 2 := div_mul_cancel₀ _

/-- Stereographic projection onto the orthogonal complement of v, defined on the complement
of the hyperplane where its denominator vanishes. -/
def stereoToFun (x : stereoDomain v) : (ℝ ∙ v)ᗮ :=
  stereoCoeff x • (ℝ ∙ v)ᗮ.orthogonalProjectionOnto x.val

variable {v}

@[simp] theorem stereoToFun_apply (x : stereoDomain v) :
    stereoToFun v x = stereoCoeff x • (ℝ ∙ v)ᗮ.orthogonalProjectionOnto x.val := rfl

private theorem contMDiff_stereoToFun_comp {A H M : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ A H}
    {n : ℕ∞ω} {f : M → E} (hf : ContMDiff I 𝓘(ℝ, E) n f) (h : ∀ x, f x ∈ stereoDomain v) :
    ContMDiff I 𝓘(ℝ, (ℝ ∙ v)ᗮ) n (fun x ↦ stereoToFun v ⟨f x, h x⟩) := by
  have hd : ContMDiff I 𝓘(ℝ) n (fun x ↦ 1 - innerSL ℝ v (f x)) :=
    contMDiff_const.sub ((innerSL ℝ v).contDiff.contMDiff.comp hf)
  have hi := hd.inv₀ (h := fun x ↦
    (sub_ne_zero.mpr (show innerSL ℝ v (f x) ≠ 1 from h x).symm).isUnit)
  let scale (z : ℝ × (ℝ ∙ v)ᗮ) := (2 * z.1) • z.2
  have hs : ContDiff ℝ n scale := (contDiff_const.mul contDiff_fst).smul contDiff_snd
  simpa only [stereoToFun, stereoCoeff, div_eq_mul_inv₀, scale, Function.comp_def] using!
    hs.contMDiff.comp (hi.prodMk_space
      ((ℝ ∙ v)ᗮ.orthogonalProjectionOnto.contDiff.contMDiff.comp hf))

/-- The forward stereographic formula is smooth on its open domain. -/
theorem contDiffOn_stereoToFun {n : ℕ∞ω} :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, (ℝ ∙ v)ᗮ) n (stereoToFun v) :=
  contMDiff_stereoToFun_comp (f := (Subtype.val : stereoDomain v → E))
    contMDiff_subtype_val (fun x ↦ x.property)

theorem continuousOn_stereoToFun : Continuous (stereoToFun v) :=
  (contDiffOn_stereoToFun (n := 0)).continuous

/-- The scalar in the inverse stereographic formula. Its denominator is positive even at zero. -/
def stereoWeight (w : E) : ℝ :=
  Checked.inv (‖w‖ ^ 2 + 4) (Ne.isUnit (by positivity))

omit [InnerProductSpace ℝ E] in
lemma stereoWeight_mul (w : E) : stereoWeight w * (‖w‖ ^ 2 + 4) = 1 := inv_mul_cancel₀

omit [InnerProductSpace ℝ E] in
private lemma stereoWeight_pos (w : E) : 0 < stereoWeight w :=
  inv_pos.mpr (by positivity)

variable (v) in
/-- Auxiliary function for the construction of the reverse direction of the stereographic
projection.  This is a map from the orthogonal complement of a unit vector `v` in an inner product
space `E` to `E`; we will later prove that it takes values in the unit sphere.

For most purposes, use `stereoInvFun`, not `stereoInvFunAux`. -/
def stereoInvFunAux (w : E) : E :=
  stereoWeight w • ((4 : ℝ) • w + (‖w‖ ^ 2 - 4) • v)

@[simp]
theorem stereoInvFunAux_apply (w : E) :
    stereoInvFunAux v w = stereoWeight w • ((4 : ℝ) • w + (‖w‖ ^ 2 - 4) • v) :=
  rfl

theorem stereoInvFunAux_mem (hv : ‖v‖ = 1) {w : E} (hw : w ∈ (ℝ ∙ v)ᗮ) :
    stereoInvFunAux v w ∈ sphere (0 : E) 1 := by
  have h₁ : (0 : ℝ) < ‖w‖ ^ 2 + 4 := by positivity
  suffices ‖(4 : ℝ) • w + (‖w‖ ^ 2 - 4) • v‖ = ‖w‖ ^ 2 + 4 by
    rw [mem_sphere_zero_iff_norm, stereoInvFunAux_apply, norm_smul, Real.norm_of_nonneg
      (stereoWeight_pos w).le, this, stereoWeight_mul]
  suffices ‖(4 : ℝ) • w + (‖w‖ ^ 2 - 4) • v‖ ^ 2 = (‖w‖ ^ 2 + 4) ^ 2 by
    simpa only [sq_eq_sq_iff_abs_eq_abs, abs_norm, abs_of_pos h₁] using this
  rw [Submodule.mem_orthogonal_singleton_iff_inner_left] at hw
  simp [norm_add_sq_real, norm_smul, inner_smul_left, inner_smul_right, hw, mul_pow,
    Real.norm_eq_abs, hv]
  ring

theorem hasFDerivAt_stereoInvFunAux (v : E) :
    HasFDerivAt (stereoInvFunAux v) (ContinuousLinearMap.id ℝ E) 0 := by
  have h₀ : HasFDerivAt (fun w : E => ‖w‖ ^ 2) (0 : StrongDual ℝ E) 0 := by
    convert! (hasStrictFDerivAt_norm_sq (0 : E)).hasFDerivAt
    simp only [map_zero, smul_zero]
  have h₁ : HasFDerivAt (stereoWeight : E → ℝ) (0 : StrongDual ℝ E) 0 := by
    let d (w : E) := ‖w‖ ^ 2 + 4
    have hd : HasFDerivAt d (0 : StrongDual ℝ E) 0 := h₀.add_const 4
    have hu (w : E) : IsUnit (d w) := Ne.isUnit (by dsimp [d]; positivity)
    apply HasFDerivAt.of_restrict (s := {w | IsUnit (d w)}) (x := ⟨0, hu 0⟩) _
      (Eventually.of_forall hu)
    simpa only [stereoWeight, Checked.inv, ContinuousLinearMap.comp_zero] using! hd.inv (hu 0)
  have h₂ : HasFDerivAt (fun w => (4 : ℝ) • w + (‖w‖ ^ 2 - 4) • v)
      ((4 : ℝ) • ContinuousLinearMap.id ℝ E) 0 := by
    convert!
      ((hasFDerivAt_const (4 : ℝ) 0).smul (hasFDerivAt_id 0)).add
        ((h₀.sub (hasFDerivAt_const (4 : ℝ) 0)).smul (hasFDerivAt_const v 0)) using 1
    ext w
    simp
  convert! h₁.smul h₂ using 1
  ext w
  simp [stereoWeight]

theorem hasFDerivAt_stereoInvFunAux_comp_coe (v : E) :
    HasFDerivAt (stereoInvFunAux v ∘ ((↑) : (ℝ ∙ v)ᗮ → E)) (ℝ ∙ v)ᗮ.subtypeL 0 := by
  have : HasFDerivAt (stereoInvFunAux v) (ContinuousLinearMap.id ℝ E) ((ℝ ∙ v)ᗮ.subtypeL 0) :=
    hasFDerivAt_stereoInvFunAux v
  refine this.comp (0 : (ℝ ∙ v)ᗮ) (by apply ContinuousLinearMap.hasFDerivAt)

theorem contDiff_stereoInvFunAux {m : ℕ∞ω} : ContDiff ℝ m (stereoInvFunAux v) := by
  have h₀ : ContDiff ℝ ω fun w : E => ‖w‖ ^ 2 := contDiff_norm_sq ℝ
  have h₁ : ContDiff ℝ ω (stereoWeight : E → ℝ) :=
    (h₀.add contDiff_const).inv (h := fun w ↦ Ne.isUnit (by positivity))
  have h₂ : ContDiff ℝ ω fun w => (4 : ℝ) • w + (‖w‖ ^ 2 - 4) • v := by
    refine (contDiff_const.smul contDiff_id).add ?_
    exact (h₀.sub contDiff_const).smul contDiff_const
  exact (h₁.smul h₂).of_le le_top

/-- Stereographic projection, reverse direction.  This is a map from the orthogonal complement of a
unit vector `v` in an inner product space `E` to the unit sphere in `E`. -/
def stereoInvFun (hv : ‖v‖ = 1) (w : (ℝ ∙ v)ᗮ) : sphere (0 : E) 1 :=
  ⟨stereoInvFunAux v (w : E), stereoInvFunAux_mem hv w.2⟩

@[simp]
theorem stereoInvFun_apply (hv : ‖v‖ = 1) (w : (ℝ ∙ v)ᗮ) :
    (stereoInvFun hv w : E) = stereoWeight (w : E) •
      ((4 : ℝ) • (w : E) + (‖w‖ ^ 2 - 4) • v) :=
  rfl

open scoped InnerProductSpace in
theorem stereoInvFun_ne_north_pole (hv : ‖v‖ = 1) (w : (ℝ ∙ v)ᗮ) :
    stereoInvFun hv w ≠ (⟨v, by simp [hv]⟩ : sphere (0 : E) 1) := by
  refine Subtype.coe_ne_coe.1 ?_
  rw [← inner_lt_one_iff_real_of_norm_eq_one _ hv]
  · have hw : ⟪v, w⟫_ℝ = 0 := Submodule.mem_orthogonal_singleton_iff_inner_right.mp w.2
    have hw' : stereoWeight (w : E) * (‖(w : E)‖ ^ 2 - 4) < 1 := by
      nlinarith only [stereoWeight_pos (w : E), stereoWeight_mul (w : E)]
    simpa [real_inner_comm, inner_add_right, inner_smul_right, real_inner_self_eq_norm_mul_norm, hw,
      hv] using hw'
  · simpa using stereoInvFunAux_mem hv w.2

theorem continuous_stereoInvFun (hv : ‖v‖ = 1) : Continuous (stereoInvFun hv) :=
  continuous_induced_rng.2
    ((contDiff_stereoInvFunAux (m := 0)).continuous.comp continuous_subtype_val)

lemma mem_stereoDomain_of_ne_pole (hv : ‖v‖ = 1) (x : sphere (0 : E) 1) (hx : x.val ≠ v) :
    x.val ∈ stereoDomain v :=
  fun e ↦ hx (((inner_eq_one_iff_of_norm_eq_one hv (norm_eq_of_mem_sphere x)).mp e).symm)

open scoped InnerProductSpace in
attribute [-simp] AddSubgroupClass.coe_norm in
theorem stereo_left_inv (hv : ‖v‖ = 1) {x : sphere (0 : E) 1} (hx : (x : E) ≠ v) :
    stereoInvFun hv (stereoToFun v ⟨x.val, mem_stereoDomain_of_ne_pole hv x hx⟩) = x := by
  apply Subtype.ext
  -- name two frequently-occurring quantities and write down their basic properties
  set a : ℝ := innerSL _ v x
  set y := (ℝ ∙ v)ᗮ.orthogonalProjectionOnto x
  have split : ↑x = a • v + ↑y := by
    rw [← ((ℝ ∙ v).starProjection_add_starProjection_orthogonal x),
      Submodule.starProjection_unit_singleton ℝ hv x]
    rfl
  have hvy : ⟪v, y⟫_ℝ = 0 := Submodule.mem_orthogonal_singleton_iff_inner_right.mp y.2
  have pythag : 1 = a ^ 2 + ‖y‖ ^ 2 := by
    have hvy' : ⟪a • v, y⟫_ℝ = 0 := by simp only [inner_smul_left, hvy, mul_zero]
    convert! norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hvy' using 2
    · simp [← split]
    · simp [norm_smul, hv, ← sq, sq_abs]
    · exact sq _
  let X : stereoDomain v := ⟨x.val, mem_stereoDomain_of_ne_pole hv x hx⟩
  let t := stereoCoeff X
  let b := ‖t • y‖ ^ 2
  let k := stereoWeight ((t • y : (ℝ ∙ v)ᗮ) : E)
  have ht : t * (1 - a) = 2 := stereoCoeff_mul X
  have hk : k * (b + 4) = 1 := stereoWeight_mul ((t • y : (ℝ ∙ v)ᗮ) : E)
  have hb : b = 2 * t * (1 + a) := by
    calc
      b = t ^ 2 * ‖y‖ ^ 2 := by simp only [b, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      _ = t ^ 2 * (1 - a ^ 2) := by rw [show ‖y‖ ^ 2 = 1 - a ^ 2 by linarith only [pythag]]
      _ = (t * (1 - a)) * (t * (1 + a)) := by ring
      _ = 2 * t * (1 + a) := by rw [ht]; ring
  have hbt : b + 4 = 4 * t := by nlinarith only [ht, hb]
  have hky : k * (4 * t) = 1 := hbt ▸ hk
  have hba : b - 4 = (b + 4) * a := by rw [hbt]; nlinarith only [hb, ht]
  have hkv : k * (b - 4) = a := by rw [hba, ← mul_assoc, hk, one_mul]
  change k • ((4 : ℝ) • ((t • y : (ℝ ∙ v)ᗮ) : E) + (b - 4) • v) = x.val
  calc
    _ = y.val + a • v := by
      simp only [Submodule.coe_smul_of_tower, smul_add, smul_smul, hky, hkv, one_smul]
    _ = x.val := (add_comm ..).trans split.symm

theorem stereo_right_inv (hv : ‖v‖ = 1) (w : (ℝ ∙ v)ᗮ) :
    stereoToFun v ⟨(stereoInvFun hv w).val, mem_stereoDomain_of_ne_pole hv _ (fun e ↦
      stereoInvFun_ne_north_pole hv w (Subtype.ext e))⟩ = w := by
  let z := stereoInvFun hv w
  let X : stereoDomain v := ⟨z.val, mem_stereoDomain_of_ne_pole hv z
    (fun e ↦ stereoInvFun_ne_north_pole hv w (Subtype.ext e))⟩
  let b := ‖(w : E)‖ ^ 2
  let k := stereoWeight (w : E)
  have hk : k * (b + 4) = 1 := stereoWeight_mul _
  have ez : z.val = k • ((4 : ℝ) • (w : E) + (b - 4) • v) := rfl
  have hw : ⟪v, (w : E)⟫ = 0 := Submodule.mem_orthogonal_singleton_iff_inner_right.mp w.2
  have hvv : ⟪v, v⟫ = 1 := by simp [hv]
  have hd : 1 - innerSL ℝ v z.val = 8 * k := by
    rw [ez]
    simp only [map_smul, map_add, innerSL_apply_apply, hw, hvv, smul_eq_mul,
      mul_zero, zero_add, mul_one]
    nlinarith only [hk]
  have hp : (ℝ ∙ v)ᗮ.orthogonalProjectionOnto z.val = (k * 4) • w := by
    rw [ez]
    simp [Submodule.orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero,
      Submodule.orthogonalProjectionOnto_mem_subspace_eq_self, smul_smul]
  have ht : stereoCoeff X * (1 - innerSL ℝ v z.val) = 2 := stereoCoeff_mul X
  rw [hd] at ht
  change stereoCoeff X • (ℝ ∙ v)ᗮ.orthogonalProjectionOnto z.val = w
  rw [hp, smul_smul, show stereoCoeff X * (k * 4) = 1 by nlinarith only [ht], one_smul]

theorem stereoInvFun_injective (hv : ‖v‖ = 1) : Injective (stereoInvFun hv) := by
  intro x y e
  let f (w : (ℝ ∙ v)ᗮ) : stereoDomain v := ⟨(stereoInvFun hv w).val,
    mem_stereoDomain_of_ne_pole hv _ (fun h ↦ stereoInvFun_ne_north_pole hv w (Subtype.ext h))⟩
  have hxy : f x = f y := Subtype.ext (congrArg (Subtype.val : sphere (0 : E) 1 → E) e)
  exact (stereo_right_inv hv x).symm.trans <|
    (congrArg (stereoToFun v) hxy).trans (stereo_right_inv hv y)

theorem invFun_stereoInvFun_apply (hv : ‖v‖ = 1) (x : sphere (0 : E) 1) (hx : x.val ≠ v) :
    invFun (stereoInvFun hv) x = stereoToFun v ⟨x.val, mem_stereoDomain_of_ne_pole hv x hx⟩ := by
  conv_lhs => rw [← stereo_left_inv hv hx]
  exact leftInverse_invFun (stereoInvFun_injective hv) _

/-- Stereographic projection from the unit sphere in `E`, centred at a unit vector `v` in `E`;
this is the version as an open partial homeomorphism. -/
def stereographic (hv : ‖v‖ = 1) : OpenPartialHomeomorph (sphere (0 : E) 1) (ℝ ∙ v)ᗮ where
  toFun := invFun (stereoInvFun hv)
  invFun := stereoInvFun hv
  source := {⟨v, by simp [hv]⟩}ᶜ
  target := Set.univ
  map_source' := by simp
  map_target' {w} _ := fun h => (stereoInvFun_ne_north_pole hv w) (Set.eq_of_mem_singleton h)
  left_inv' x hx := by
    have hne : x.val ≠ v := fun e ↦ hx (Subtype.ext e)
    rw [invFun_stereoInvFun_apply hv x hne]
    exact stereo_left_inv hv hne
  right_inv' w _ := leftInverse_invFun (stereoInvFun_injective hv) w
  open_source := isOpen_compl_singleton
  open_target := isOpen_univ
  continuousOn_toFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    let D := ({⟨v, by simp [hv]⟩}ᶜ : Set (sphere (0 : E) 1))
    have hne (x : D) : x.val.val ≠ v := fun e ↦ x.2 (Subtype.ext e)
    let f (x : D) : stereoDomain v := ⟨x.val.val, mem_stereoDomain_of_ne_pole hv _ (hne x)⟩
    have hf : Continuous f := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    have eq : D.domRestrict (invFun (stereoInvFun hv)) = stereoToFun v ∘ f :=
      funext fun x ↦ invFun_stereoInvFun_apply hv x.val (hne x)
    change Continuous (D.domRestrict (invFun (stereoInvFun hv)))
    rw [eq]
    exact continuousOn_stereoToFun.comp hf
  continuousOn_invFun := (continuous_stereoInvFun hv).continuousOn

theorem stereographic_apply (hv : ‖v‖ = 1) (x : sphere (0 : E) 1) (hx : x.val ≠ v) :
    stereographic hv x = stereoToFun v ⟨x.val, mem_stereoDomain_of_ne_pole hv x hx⟩ :=
  invFun_stereoInvFun_apply hv x hx

private theorem contMDiffOn_stereographic_comp {A H M : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ A H} {n : ℕ∞ω} (hv : ‖v‖ = 1) {f : M → sphere (0 : E) 1}
    (hf : ContMDiff I 𝓘(ℝ, E) n (fun x ↦ (f x).val)) :
    ContMDiffOn I 𝓘(ℝ, (ℝ ∙ v)ᗮ) n (stereographic hv ∘ f) (f ⁻¹' (stereographic hv).source) := by
  have hfc : Continuous f := continuous_induced_rng.mpr hf.continuous
  let U : TopologicalSpace.Opens M :=
    ⟨f ⁻¹' (stereographic hv).source, (stereographic hv).open_source.preimage hfc⟩
  have hne (x : U) : (f x.val).val ≠ v := fun e ↦ x.property (Subtype.ext e)
  have H := contMDiff_stereoToFun_comp (v := v)
    (f := fun x : U ↦ (f x.val).val) (hf.comp contMDiff_subtype_val)
    (fun x ↦ mem_stereoDomain_of_ne_pole hv _ (hne x))
  have eq : (fun x : U ↦ stereographic hv (f x.val)) = _ :=
    funext fun x ↦ stereographic_apply hv _ (hne x)
  rw [← eq] at H
  intro x hx
  exact ((contMDiffAt_subtype_iff (U := U) (f := stereographic hv ∘ f) (x := ⟨x, hx⟩)).mp
    (H ⟨x, hx⟩)).contMDiffWithinAt

@[simp]
theorem stereographic_source (hv : ‖v‖ = 1) : (stereographic hv).source = {⟨v, by simp [hv]⟩}ᶜ :=
  rfl

@[simp]
theorem stereographic_target (hv : ‖v‖ = 1) : (stereographic hv).target = Set.univ :=
  rfl

@[simp]
theorem stereographic_apply_neg (v : sphere (0 : E) 1) :
    stereographic (norm_eq_of_mem_sphere v) (-v) = 0 := by
  have h : (-v).val ≠ v.val := by
    exact fun e ↦ (ne_neg_of_mem_unit_sphere ℝ v).symm (Subtype.ext e)
  rw [stereographic_apply _ _ h]
  simp [Submodule.orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero]

@[simp]
theorem stereographic_neg_apply (v : sphere (0 : E) 1) :
    stereographic (norm_eq_of_mem_sphere (-v)) v = 0 := by
  convert! stereographic_apply_neg (-v)
  ext1
  simp

theorem surjective_stereographic (hv : ‖v‖ = 1) :
    Surjective (stereographic hv) :=
  (stereographic hv).surjective_of_target_eq_univ rfl

@[simp]
theorem range_stereographic_symm (hv : ‖v‖ = 1) (hv' : v ∈ sphere 0 1 := by simpa) :
    Set.range (stereographic hv).symm = {⟨v, hv'⟩}ᶜ := by
  refine le_antisymm ?_ (stereographic hv).symm.target_subset_range
  rintro x ⟨y, rfl⟩
  suffices y ∈ (stereographic hv).target from (fun _ ↦ (stereographic hv).map_target) y this
  simp

lemma isOpenEmbedding_stereographic_symm (hv : ‖v‖ = 1) :
    Topology.IsOpenEmbedding (stereographic hv).symm :=
  (stereographic hv).symm.isOpenEmbedding (by simp)

end StereographicProjection

section ChartedSpace

/-!
### Charted space structure on the sphere

In this section we construct a charted space structure on the unit sphere in a finite-dimensional
real inner product space `E`; that is, we show that it is locally homeomorphic to the Euclidean
space of dimension one less than `E`.

The restriction to finite dimension is for convenience.  The most natural `ChartedSpace`
structure for the sphere uses the stereographic projection from the antipodes of a point as the
canonical chart at this point.  However, the codomain of the stereographic projection constructed
in the previous section is `(ℝ ∙ v)ᗮ`, the orthogonal complement of the vector `v` in `E` which is
the "north pole" of the projection, so a priori these charts all have different codomains.

So it is necessary to prove that these codomains are all continuously linearly equivalent to a
fixed normed space.  This could be proved in general by a simple case of Gram-Schmidt
orthogonalization, but in the finite-dimensional case it follows more easily by dimension-counting.
-/

/-- Variant of the stereographic projection, for the sphere in an `n + 1`-dimensional inner product
space `E`.  This version has codomain the Euclidean space of dimension `n`, and is obtained by
composing the original stereographic projection (`stereographic`) with an arbitrary linear isometry
from `(ℝ ∙ v)ᗮ` to the Euclidean space. -/
def stereographic' (n : ℕ) [Fact (finrank ℝ E = n + 1)] (v : sphere (0 : E) 1) :
    OpenPartialHomeomorph (sphere (0 : E) 1) (EuclideanSpace ℝ (Fin n)) :=
  stereographic (norm_eq_of_mem_sphere v) ≫ₕ
    (OrthonormalBasis.fromOrthogonalSpanSingleton n
            (ne_zero_of_mem_unit_sphere v)).repr.toHomeomorph.toOpenPartialHomeomorph

@[simp]
theorem stereographic'_source {n : ℕ} [Fact (finrank ℝ E = n + 1)] (v : sphere (0 : E) 1) :
    (stereographic' n v).source = {v}ᶜ := by simp [stereographic']

@[simp]
theorem stereographic'_target {n : ℕ} [Fact (finrank ℝ E = n + 1)] (v : sphere (0 : E) 1) :
    (stereographic' n v).target = Set.univ := by simp [stereographic']

/-- The unit sphere in an `n + 1`-dimensional inner product space `E` is a charted space
modelled on the Euclidean space of dimension `n`. -/
instance EuclideanSpace.instChartedSpaceSphere {n : ℕ} [Fact (finrank ℝ E = n + 1)] :
    ChartedSpace (EuclideanSpace ℝ (Fin n)) (sphere (0 : E) 1) where
  atlas := {f | ∃ v : sphere (0 : E) 1, f = stereographic' n v}
  chartAt v := stereographic' n (-v)
  mem_chart_source v := by simpa using ne_neg_of_mem_unit_sphere ℝ v
  chart_mem_atlas v := ⟨-v, rfl⟩

instance (n : ℕ) :
    ChartedSpace (EuclideanSpace ℝ (Fin n)) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
  have := Fact.mk (@finrank_euclideanSpace_fin ℝ _ (n + 1))
  EuclideanSpace.instChartedSpaceSphere

end ChartedSpace

section ContMDiffManifold

open scoped InnerProductSpace

theorem sphere_ext_iff (u v : sphere (0 : E) 1) : u = v ↔ ⟪(u : E), v⟫_ℝ = 1 := by
  simp [Subtype.ext_iff, inner_eq_one_iff_of_norm_eq_one]

theorem stereographic'_symm_apply {n : ℕ} [Fact (finrank ℝ E = n + 1)] (v : sphere (0 : E) 1)
    (x : EuclideanSpace ℝ (Fin n)) :
    ((stereographic' n v).symm x : E) =
      let U : (ℝ ∙ (v : E))ᗮ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
        (OrthonormalBasis.fromOrthogonalSpanSingleton n (ne_zero_of_mem_unit_sphere v)).repr
      stereoWeight (U.symm x : E) • (4 : ℝ) • (U.symm x : E) +
        stereoWeight (U.symm x : E) • (‖(U.symm x : E)‖ ^ 2 - 4) • v.val := by
  simp [stereographic, stereographic', Submodule.norm_coe]

/-! ### Analytic manifold structure on the sphere -/

/-- The unit sphere in an `n + 1`-dimensional inner product space `E` is an analytic manifold,
modelled on the Euclidean space of dimension `n`. -/
instance EuclideanSpace.instIsManifoldSphere
    {n : ℕ} [Fact (finrank ℝ E = n + 1)] :
    IsManifold (𝓡 n) ω (sphere (0 : E) 1) :=
  isManifold_of_contDiffOn (𝓡 n) ω (sphere (0 : E) 1)
    (by
      rintro _ _ ⟨v, rfl⟩ ⟨v', rfl⟩
      let U :=
        (-- Removed type ascription, and this helped for some reason with timeout issues?
            OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ)
            n (ne_zero_of_mem_unit_sphere v)).repr
      let U' :=
        (-- Removed type ascription, and this helped for some reason with timeout issues?
            OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ)
            n (ne_zero_of_mem_unit_sphere v')).repr
      let g := (stereographic' n v).symm.toPartialEquiv.toFun
      have H₂ : ContDiff ℝ ω (fun x ↦ (g x).val) :=
        ((contDiff_stereoInvFunAux (v := v.val)).comp
          (ℝ ∙ (v : E))ᗮ.subtypeL.contDiff).comp U.symm.contDiff
      have H := U'.contDiff.contMDiff.comp_contMDiffOn
        (contMDiffOn_stereographic_comp (f := g) (norm_eq_of_mem_sphere v') H₂.contMDiff)
      simp only [OpenPartialHomeomorph.trans_toPartialEquiv,
        OpenPartialHomeomorph.symm_toPartialEquiv,
        PartialEquiv.trans_source, PartialEquiv.symm_source, stereographic'_target,
        modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.range_id, Set.inter_univ,
        Set.preimage_id_eq, Set.univ_inter, id_eq, stereographic'_source]
      simpa only [stereographic_source] using! H.contDiffOn)

instance (n : ℕ) : IsManifold (𝓡 n) ω (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
  haveI := Fact.mk (@finrank_euclideanSpace_fin ℝ _ (n + 1))
  EuclideanSpace.instIsManifoldSphere

/-- The inclusion map (i.e., `coe`) from the sphere in `E` to `E` is analytic. -/
theorem contMDiff_coe_sphere {m : ℕ∞ω} {n : ℕ} [Fact (finrank ℝ E = n + 1)] :
    ContMDiff (𝓡 n) 𝓘(ℝ, E) m ((↑) : sphere (0 : E) 1 → E) := by
  rw [contMDiff_iff]
  constructor
  · exact continuous_subtype_val
  · intro v _
    let U : _ ≃ₗᵢ[ℝ] _ :=
      (-- Again, partially removing type ascription...
          OrthonormalBasis.fromOrthogonalSpanSingleton
          n (ne_zero_of_mem_unit_sphere (-v))).repr
    exact
      ((contDiff_stereoInvFunAux.comp (ℝ ∙ (-v : E))ᗮ.subtypeL.contDiff).comp
          U.symm.contDiff).contDiffOn

variable {m : ℕ∞ω} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I m M]

/-- If a `C^m` function `f : M → E`, where `M` is some manifold, takes values in the
sphere, then it restricts to a `C^m` function from `M` to the sphere. -/
theorem ContMDiff.codRestrict_sphere {n : ℕ} [Fact (finrank ℝ E = n + 1)] {f : M → E}
    (hf : CMDiff m f) (hf' : ∀ x, f x ∈ sphere (0 : E) 1) :
    CMDiff m (Set.codRestrict _ _ hf' : M → sphere (0 : E) 1) := by
  rw [contMDiff_iff_target]
  refine ⟨continuous_induced_rng.2 hf.continuous, ?_⟩
  intro v
  let U : _ ≃ₗᵢ[ℝ] _ :=
    (-- Again, partially removing type ascription... Weird that this helps!
        OrthonormalBasis.fromOrthogonalSpanSingleton
        n (ne_zero_of_mem_unit_sphere (-v))).repr
  let g := Set.codRestrict f (sphere (0 : E) 1) hf'
  have H := U.contDiff.contMDiff.comp_contMDiffOn (contMDiffOn_stereographic_comp (f := g)
    (norm_eq_of_mem_sphere (-v)) (by exact hf))
  rw [extChartAt_source]
  change ContMDiffOn I (𝓡 n) m (U ∘ stereographic (norm_eq_of_mem_sphere (-v)) ∘ g)
    (g ⁻¹' (stereographic' n (-v)).source)
  simpa only [stereographic'_source, stereographic_source] using! H

/-- The antipodal map is analytic. -/
theorem contMDiff_neg_sphere {m : ℕ∞ω} {n : ℕ} [Fact (finrank ℝ E = n + 1)] :
    CMDiff m fun x : sphere (0 : E) 1 => -x := by
  -- this doesn't elaborate well in term mode
  apply ContMDiff.codRestrict_sphere
  apply contDiff_neg.contMDiff.comp _
  exact contMDiff_coe_sphere

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private lemma stereographic'_neg {n : ℕ} [Fact (finrank ℝ E = n + 1)] (v : sphere (0 : E) 1) :
    stereographic' n (-v) v = 0 := by
  dsimp [stereographic']
  simp only [EmbeddingLike.map_eq_zero_iff]
  apply stereographic_neg_apply

-- Without this option, the lemmas `EmbeddingLike.map_eq_zero_iff` and `Submodule.range_subtype`
-- are not applied by simp below.
set_option backward.isDefEq.respectTransparency false in
/-- Consider the differential of the inclusion of the sphere in `E` at the point `v` as a continuous
linear map from `TangentSpace (𝓡 n) v` to `E`.  The range of this map is the orthogonal complement
of `v` in `E`.
-/
theorem range_mvfderiv_subtypeVal {n : ℕ} [Fact (finrank ℝ E = n + 1)] (v : sphere (0 : E) 1) :
    (mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) v).range = (ℝ ∙ (v : E))ᗮ := by
  rw [((contMDiff_coe_sphere v).mdifferentiableAt one_ne_zero).mvfderiv]
  dsimp [chartAt]
  simp only [mfld_simps]
  let U := (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) n
    (ne_zero_of_mem_unit_sphere (-v))).repr
  suffices
      (fderiv ℝ ((stereoInvFunAux (-v : E) ∘ (↑)) ∘ U.symm) 0).range = (ℝ ∙ (v : E))ᗮ by
    rw [fderivWithin_of_mem_nhds univ_mem]
    change (fderiv ℝ ((stereoInvFunAux (-v : E) ∘ (↑)) ∘ U.symm)
      (stereographic' n (-v) v)).range = _
    rwa [stereographic'_neg]
  have :
    HasFDerivAt (stereoInvFunAux (-v : E) ∘ (Subtype.val : (ℝ ∙ (↑(-v) : E))ᗮ → E))
      (ℝ ∙ (↑(-v) : E))ᗮ.subtypeL (U.symm 0) := by
    convert! hasFDerivAt_stereoInvFunAux_comp_coe (-v : E)
    simp
  convert! congr($((this.comp 0 U.symm.toContinuousLinearEquiv.hasFDerivAt).fderiv).range)
  symm
  convert!
    (U.symm : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] (ℝ ∙ (↑(-v) : E))ᗮ).range_comp
      (ℝ ∙ (↑(-v) : E))ᗮ.subtype using 1
  simp only [Submodule.range_subtype, coe_neg_sphere]
  congr 1
  -- we must show `Submodule.span ℝ {v} = Submodule.span ℝ {-v}`
  apply Submodule.span_eq_span
  · simp only [Set.singleton_subset_iff, SetLike.mem_coe]
    rw [← Submodule.neg_mem_iff]
    exact Submodule.mem_span_singleton_self (-v : E)
  · simp only [Set.singleton_subset_iff, SetLike.mem_coe]
    rw [Submodule.neg_mem_iff]
    exact Submodule.mem_span_singleton_self (v : E)

@[deprecated range_mvfderiv_subtypeVal (since := "2026-08-02")]
theorem range_mfderiv_coe_sphere {n : ℕ} [Fact (finrank ℝ E = n + 1)] (v : sphere (0 : E) 1) :
    (mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) v : TangentSpace (𝓡 n) v →L[ℝ] E).range =
      (ℝ ∙ (v : E))ᗮ := by
  convert! range_mvfderiv_subtypeVal v

/-- Consider the differential of the inclusion of the sphere in `E` at the point `v` as a continuous
linear map from `TangentSpace (𝓡 n) v` to `E`.  This map is injective. -/
theorem injective_mvfderiv_subtypeVal_sphere {n : ℕ} [Fact (finrank ℝ E = n + 1)]
    (v : sphere (0 : E) 1) :
    Injective (mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) v) := by
  rw [((contMDiff_coe_sphere v).mdifferentiableAt one_ne_zero).mvfderiv]
  simp only [chartAt, mfld_simps]
  let U := (OrthonormalBasis.fromOrthogonalSpanSingleton
      (𝕜 := ℝ) n (ne_zero_of_mem_unit_sphere (-v))).repr
  suffices Injective (fderiv ℝ ((stereoInvFunAux (-v : E) ∘ (↑)) ∘ U.symm) 0) by
    change Injective (fderivWithin ℝ ((stereoInvFunAux (-v : E) ∘ (↑)) ∘ U.symm) Set.univ
      (stereographic' n (-v) v))
    rwa [fderivWithin_of_mem_nhds univ_mem, stereographic'_neg]
  have : HasFDerivAt (stereoInvFunAux (-v : E) ∘ (Subtype.val : (ℝ ∙ (↑(-v) : E))ᗮ → E))
      (ℝ ∙ (↑(-v) : E))ᗮ.subtypeL (U.symm 0) := by
    convert! hasFDerivAt_stereoInvFunAux_comp_coe (-v : E)
    -- Otherwise, the lemma `EmbeddingLike.map_eq_zero_iff` is not applied.
    set_option backward.isDefEq.respectTransparency false in
    simp
  have := congr_arg DFunLike.coe <| (this.comp 0 U.symm.toContinuousLinearEquiv.hasFDerivAt).fderiv
  refine Eq.subst this.symm ?_
  rw [ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe]
  set_option backward.isDefEq.respectTransparency false in
  simpa [-Subtype.val_injective] using Subtype.val_injective

@[deprecated injective_mvfderiv_subtypeVal_sphere (since := "2026-08-02")]
theorem mfderiv_coe_sphere_injective {n : ℕ} [Fact (finrank ℝ E = n + 1)] (v : sphere (0 : E) 1) :
    Injective (mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) v) := by
  convert! injective_mvfderiv_subtypeVal_sphere v

end ContMDiffManifold

section Circle

open Complex

/-- Local instance to help the typeclass system to figure out `1 + 1 = 2`. -/
theorem finrank_real_complex_fact' : Fact (finrank ℝ ℂ = 1 + 1) :=
  finrank_real_complex_fact

attribute [local instance] finrank_real_complex_fact'

/-- The unit circle in `ℂ` is a charted space modelled on `EuclideanSpace ℝ (Fin 1)`.  This
follows by definition from the corresponding result for `Metric.Sphere`. -/
instance : ChartedSpace (EuclideanSpace ℝ (Fin 1)) Circle :=
  inferInstanceAs <| ChartedSpace _ (sphere _ _)

instance : IsManifold (𝓡 1) ω Circle :=
  EuclideanSpace.instIsManifoldSphere (E := ℂ)

/-- The unit circle in `ℂ` is an analytic Lie group. -/
instance : LieGroup (𝓡 1) ω Circle where
  contMDiff_mul := by
    apply ContMDiff.codRestrict_sphere
    let c : Circle → ℂ := (↑)
    have h₂ : ContMDiff (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, ℂ) ω fun z : ℂ × ℂ => z.fst * z.snd := by
      rw [contMDiff_iff]
      exact ⟨continuous_mul, fun x y => contDiff_mul.contDiffOn⟩
    -- TODO bug: filling in ω yields an error; expected type has metavariables...
    suffices h₁ : ContMDiff _ _ _ (Prod.map c c) from
      h₂.comp h₁
    apply ContMDiff.prodMap <;> exact contMDiff_coe_sphere
  contMDiff_inv := by
    apply ContMDiff.codRestrict_sphere
    simp only [← Circle.coe_inv, Circle.coe_inv_eq_conj]
    exact Complex.conjCLE.contDiff.contMDiff.comp contMDiff_coe_sphere

/-- The map `fun t ↦ exp (t * I)` from `ℝ` to the unit circle in `ℂ` is analytic. -/
theorem contMDiff_circleExp {m : ℕ∞ω} : CMDiff m Circle.exp :=
  (contDiff_exp.comp (contDiff_id.smul contDiff_const)).contMDiff.codRestrict_sphere _

end Circle
