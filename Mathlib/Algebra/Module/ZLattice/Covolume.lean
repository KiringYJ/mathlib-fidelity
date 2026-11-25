/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.Analysis.BoxIntegral.UnitPartition
public import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Covolume of ℤ-lattices

Let `E` be a finite-dimensional real vector space.

Let `L` be a `ℤ`-lattice `L` defined as a discrete `ℤ`-submodule of `E` that spans `E` over `ℝ`.

## Main definitions and results

* `ZLattice.covolume`: the covolume of `L` defined as the volume of an arbitrary fundamental
  domain of `L`.

* `ZLattice.covolume_eq_measure_fundamentalDomain`: the covolume of `L` does not depend on the
  choice of the fundamental domain of `L`.

* `ZLattice.covolume_eq_det`: if `L` is a lattice in `ℝ^n`, then its covolume is the absolute
  value of the determinant of any `ℤ`-basis of `L`.

* `ZLattice.covolume_div_covolume_eq_relIndex`: Let `L₁` be a sub-`ℤ`-lattice of `L₂`. Then the
  index of `L₁` inside `L₂` is equal to `covolume L₁ / covolume L₂`.

* `ZLattice.covolume.tendsto_card_div_pow`: Let `s` be a bounded measurable set of `ι → ℝ`, then
  the number of points in `s ∩ n⁻¹ • L` divided by `n ^ card ι` tends to `volume s / covolume L`
  when `n : ℕ` tends to infinity.
  See also `ZLattice.covolume.tendsto_card_div_pow'` for a version for `InnerProductSpace ℝ E` and
  `ZLattice.covolume.tendsto_card_div_pow''` for the general version.

* `ZLattice.covolume.tendsto_card_le_div`: Let `X` be a cone in `ι → ℝ` and let `F : (ι → ℝ) → ℝ`
  be a function such that `F (c • x) = c ^ card ι * F x`. Then the number of points `x ∈ X` such
  that `F x ≤ c` divided by `c` tends to `volume {x ∈ X | F x ≤ 1} / covolume L`
  when `c : ℝ` tends to infinity.
  See also `ZLattice.covolume.tendsto_card_le_div'` for a version for `InnerProductSpace ℝ E` and
  `ZLattice.covolume.tendsto_card_le_div''` for the general version.

## Naming convention

Some results are true in the case where the ambient finite-dimensional real vector space is the
pi-space `ι → ℝ` and in the case where it is an `InnerProductSpace`. We use the following
convention: the plain name is for the pi case, for e.g. `volume_image_eq_volume_div_covolume`. For
the same result in the `InnerProductSpace` case, we add a `prime`, for e.g.
`volume_image_eq_volume_div_covolume'`. When the same result exists in the
general case, we had two primes, e.g. `covolume.tendsto_card_div_pow''`.

-/

@[expose] public section

noncomputable section

namespace ZLattice

open Submodule MeasureTheory Module MeasureTheory Module ZSpan

section General

variable {E : Type*} [NormedAddCommGroup E] [SigmaAlgebra E] (L : Submodule ℤ E)

/-- The covolume of a `ℤ`-lattice is the volume of some fundamental domain; see
`ZLattice.covolume_eq_volume` for the proof that the volume does not depend on the choice of
the fundamental domain. -/
def covolume (μ : Measure E := by volume_tac) : ℝ := (addCovolume L E μ).toReal

end General

section Basic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [SigmaAlgebra E] [BorelSpace E]
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
variable (μ : Measure E := by volume_tac) [Measure.IsAddHaarMeasure μ]

set_option backward.privateInPublic true in
theorem covolume_eq_measure_fundamentalDomain {F : Set E} (h : IsAddFundamentalDomain L F μ) :
    covolume L μ = μ.real F := by
  have : MeasurableVAdd L E := (inferInstance : MeasurableVAdd L.toAddSubgroup E)
  have : VAddInvariantMeasure L E μ := (inferInstance : VAddInvariantMeasure L.toAddSubgroup E μ)
  exact congr_arg ENNReal.toReal (h.covolume_eq_volume μ)

set_option backward.privateInPublic true in
theorem covolume_ne_zero : covolume L μ ≠ 0 := by
  rw [covolume_eq_measure_fundamentalDomain L μ (isAddFundamentalDomain (Free.chooseBasis ℤ L) μ),
    measureReal_ne_zero_iff (ne_of_lt _)]
  · exact measure_fundamentalDomain_ne_zero _
  · exact Bornology.IsBounded.measure_lt_top (fundamentalDomain_isBounded _)

set_option backward.privateInPublic true in
theorem covolume_pos : 0 < covolume L μ :=
  lt_of_le_of_ne ENNReal.toReal_nonneg (covolume_ne_zero L μ).symm

set_option backward.privateInPublic true in
theorem covolume_comap {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [SigmaAlgebra F] [BorelSpace F] (ν : Measure F := by volume_tac) [Measure.IsAddHaarMeasure ν]
    {e : F ≃L[ℝ] E} (he : MeasurePreserving e ν μ) :
    covolume (ZLattice.comap ℝ L e.toLinearMap) ν = covolume L μ := by
  rw [covolume_eq_measure_fundamentalDomain _ _ (isAddFundamentalDomain (Free.chooseBasis ℤ L) μ),
    covolume_eq_measure_fundamentalDomain _ _ ((isAddFundamentalDomain
    ((Free.chooseBasis ℤ L).ofZLatticeComap ℝ L e.toLinearEquiv) ν)), ← he.measureReal_preimage
    (fundamentalDomain_measurableSet _).nullMeasurableSet, ← e.image_symm_eq_preimage,
    ← e.symm.coe_toLinearEquiv, map_fundamentalDomain]
  congr!
  ext; simp

set_option backward.privateInPublic true in
theorem covolume_eq_det_mul_measureReal {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ L)
    (b₀ : Basis ι ℝ E) :
    covolume L μ = |b₀.det ((↑) ∘ b)| * μ.real (fundamentalDomain b₀) := by
  rw [covolume_eq_measure_fundamentalDomain L μ (isAddFundamentalDomain b μ),
    measureReal_fundamentalDomain _ _ b₀,
    measureReal_congr (fundamentalDomain_ae_parallelepiped b₀ μ)]
  congr
  ext
  exact b.ofZLatticeBasis_apply ℝ L _

theorem covolume_eq_det {ι : Type*} [Fintype ι] [DecidableEq ι] (L : Submodule ℤ (ι → ℝ))
    [DiscreteTopology L] [IsZLattice ℝ L] (b : Basis ι ℤ L) :
    covolume L = |(Matrix.of ((↑) ∘ b)).det| := by
  rw [covolume_eq_measure_fundamentalDomain L volume (isAddFundamentalDomain b volume),
    volume_real_fundamentalDomain]
  congr
  ext1
  exact b.ofZLatticeBasis_apply ℝ L _

theorem covolume_eq_det_inv {ι : Type*} [Fintype ι] (L : Submodule ℤ (ι → ℝ))
    [DiscreteTopology L] [IsZLattice ℝ L] (b : Basis ι ℤ L) :
    covolume L = Checked.inv |(LinearEquiv.det (b.ofZLatticeBasis ℝ L).equivFun : ℝ)|
      (abs_pos.mpr (LinearEquiv.det (b.ofZLatticeBasis ℝ L).equivFun).ne_zero).ne'.isUnit := by
  classical
  let B := b.ofZLatticeBasis ℝ L
  have hdet : (LinearEquiv.det B.equivFun : ℝ) = B.det (Pi.basisFun ℝ ι) := by
    rw [← Basis.det_basis, LinearEquiv.coe_det]
    rfl
  rw [covolume_eq_det L b, ← Pi.basisFun_det_apply, show (((↑) : L → _) ∘ ⇑b) =
    B by ext; simp [B], ← Basis.det_inv, Units.val_inv_eq_inv_val₀, abs_inv]
  exact inv_inj₀.mpr (congrArg abs ((B.isUnit_det (Pi.basisFun ℝ ι)).unit_spec.trans hdet.symm))

set_option backward.isDefEq.respectTransparency.types false in
/--
Let `L₁` be a sub-`ℤ`-lattice of `L₂`. Then the index of `L₁` inside `L₂` is equal to
`covolume L₁ / covolume L₂`.
-/
theorem covolume_div_covolume_eq_relIndex {ι : Type*} [Fintype ι] (L₁ L₂ : Submodule ℤ (ι → ℝ))
    [DiscreteTopology L₁] [IsZLattice ℝ L₁] [DiscreteTopology L₂] [IsZLattice ℝ L₂] (h : L₁ ≤ L₂) :
    Checked.div (covolume L₁) (covolume L₂) (covolume_ne_zero L₂ volume).isUnit =
      L₁.toAddSubgroup.relIndex L₂.toAddSubgroup := by
  classical
  let b₁ := IsZLattice.basis L₁
  let b₂ := IsZLattice.basis L₂
  rw [AddSubgroup.relIndex_eq_natAbs_det L₁.toAddSubgroup L₂.toAddSubgroup h b₁ b₂,
    Nat.cast_natAbs, Int.cast_abs]
  trans |(b₂.ofZLatticeBasis ℝ).det (b₁.ofZLatticeBasis ℝ)|
  · apply div_eq_iff.2
    rw [covolume_eq_det _ b₁, covolume_eq_det _ b₂, ← Pi.basisFun_det_apply,
      ← Pi.basisFun_det_apply,
      show (((↑) : L₁ → _) ∘ ⇑b₁) = b₁.ofZLatticeBasis ℝ L₁ by ext; simp,
      show (((↑) : L₂ → _) ∘ ⇑b₂) = b₂.ofZLatticeBasis ℝ L₂ by ext; simp,
      mul_comm, ← abs_mul, Basis.det_mul_det]
  · rw [Basis.det_apply, Basis.det_apply, Int.cast_det]
    congr; ext i j
    rw [Matrix.map_apply, Basis.toMatrix_apply, Basis.toMatrix_apply, Basis.ofZLatticeBasis_apply]
    exact (b₂.ofZLatticeBasis_repr_apply ℝ L₂ ⟨b₁ j, h (coe_mem _)⟩ i)

/--
A more general version of `covolume_div_covolume_eq_relIndex`;
see the `Naming conventions` section in the introduction.
-/
theorem covolume_div_covolume_eq_relIndex' {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [SigmaAlgebra E] [BorelSpace E]
    (L₁ L₂ : Submodule ℤ E) [DiscreteTopology L₁] [IsZLattice ℝ L₁] [DiscreteTopology L₂]
    [IsZLattice ℝ L₂] (h : L₁ ≤ L₂) :
    Checked.div (covolume L₁) (covolume L₂) (covolume_ne_zero L₂ volume).isUnit =
      L₁.toAddSubgroup.relIndex L₂.toAddSubgroup := by
  let f := (EuclideanSpace.equiv _ ℝ).symm.trans
    (stdOrthonormalBasis ℝ E).repr.toContinuousLinearEquiv.symm
  have hf : MeasurePreserving f := (stdOrthonormalBasis ℝ E).measurePreserving_repr_symm.comp
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp _).symm
  let M₁ := ZLattice.comap ℝ L₁ f.toLinearMap
  let M₂ := ZLattice.comap ℝ L₂ f.toLinearMap
  have hquot : Checked.div (covolume L₁) (covolume L₂) (covolume_ne_zero L₂ volume).isUnit =
      Checked.div (covolume M₁) (covolume M₂) (covolume_ne_zero M₂ volume).isUnit := by
    apply div_eq_div_iff.2
    rw [covolume_comap L₁ volume volume hf, covolume_comap L₂ volume volume hf]
  rw [hquot, covolume_div_covolume_eq_relIndex M₁ M₂ (fun _ h' ↦ h h')]
  unfold M₁ M₂
  rw [ZLattice.comap_toAddSubgroup,
    ZLattice.comap_toAddSubgroup, Nat.cast_inj, LinearEquiv.toAddMonoidHom_commutes,
    AddSubgroup.comap_equiv_eq_map_symm', AddSubgroup.comap_equiv_eq_map_symm',
    AddSubgroup.relIndex_map_map_of_injective _ _ f.symm.injective]

theorem volume_image_eq_volume_div_covolume {ι : Type*} [Fintype ι] (L : Submodule ℤ (ι → ℝ))
    [DiscreteTopology L] [IsZLattice ℝ L] (b : Basis ι ℤ L) {s : Set (ι → ℝ)} :
    volume ((b.ofZLatticeBasis ℝ L).equivFun '' s) =
      ENNReal.div (volume s) (ENNReal.ofReal (covolume L))
        ⟨ENNReal.ofReal_ne_zero_iff.mpr (covolume_pos L volume),
          Or.inr ENNReal.ofReal_ne_top⟩ := by
  rw [ENNReal.div_eq_inv_mul, LinearEquiv.image_eq_preimage_symm,
    Measure.addHaar_preimage_linearEquiv, LinearEquiv.symm_symm, covolume_eq_det_inv L b,
    ENNReal.ofReal_inv_of_pos (abs_pos.2 (LinearEquiv.det _).ne_zero), inv_inv, LinearEquiv.coe_det]

set_option backward.isDefEq.respectTransparency.types false in
/-- A more general version of `ZLattice.volume_image_eq_volume_div_covolume`;
see the `Naming conventions` section in the introduction. -/
theorem volume_image_eq_volume_div_covolume' {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [SigmaAlgebra E] [BorelSpace E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] {ι : Type*} [Fintype ι]
    (b : Basis ι ℤ L) {s : Set E} (hs : NullMeasurableSet s) :
    volume ((b.ofZLatticeBasis ℝ).equivFun '' s) =
      ENNReal.div (volume s) (ENNReal.ofReal (covolume L))
        ⟨ENNReal.ofReal_ne_zero_iff.mpr (covolume_pos L volume),
          Or.inr ENNReal.ofReal_ne_top⟩ := by
  let e : Fin (finrank ℝ E) ≃ ι :=
    Fintype.equivOfCardEq (by rw [Fintype.card_fin, finrank_eq_card_basis (b.ofZLatticeBasis ℝ)])
  let f := (EuclideanSpace.equiv ι ℝ).symm.trans
    ((stdOrthonormalBasis ℝ E).reindex e).repr.toContinuousLinearEquiv.symm
  have hf : MeasurePreserving f :=
    ((stdOrthonormalBasis ℝ E).reindex e).measurePreserving_repr_symm.comp
      (PiLp.volume_preserving_toLp ι)
  have himage := volume_image_eq_volume_div_covolume
    (ZLattice.comap ℝ L f.toLinearMap) (b.ofZLatticeComap ℝ L f.toLinearEquiv)
    (s := f ⁻¹' s)
  rw [ENNReal.div_eq_inv_mul] at himage ⊢
  rw [← hf.measure_preimage hs, ← (covolume_comap L volume volume hf),
    ← himage, Basis.ofZLatticeBasis_comap, ← f.image_symm_eq_preimage, ← Set.image_comp]
  simp

end Basic

namespace covolume

private theorem toReal_div_ofReal_pos (a : ENNReal) {b : ℝ} (hb : 0 < b) :
    (a / ENNReal.ofReal b).toReal =
      Checked.div a.toReal b hb.ne'.isUnit := by
  have h := ENNReal.toReal_ofReal hb.le
  have hu : IsUnit (ENNReal.ofReal b).toReal := h.symm ▸ hb.ne'.isUnit
  rw [ENNReal.toReal_div _ _ (hb := hu)]
  exact div_eq_div_iff.mpr (congrArg (a.toReal * ·) h.symm)

section General

open Filter Fintype Pointwise BoxIntegral Bornology

open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L]
variable {ι : Type*} [Fintype ι] (b : Basis ι ℤ L)

set_option backward.isDefEq.respectTransparency.types false in
/-- A version of `ZLattice.covolume.tendsto_card_div_pow` for the general case;
see the `Naming convention` section in the introduction. -/
theorem tendsto_card_div_pow'' [FiniteDimensional ℝ E] [SigmaAlgebra E] [BorelSpace E]
    {s : Set E} (hs₁ : IsBounded s) (hs₂ : MeasurableSet s)
    (hs₃ : volume (frontier ((b.ofZLatticeBasis ℝ).equivFun '' s)) = 0) :
    Tendsto (fun n : {n : ℕ // n ≠ 0} ↦
      letI : NeZero n.val := ⟨n.property⟩
      (Nat.card (s ∩ (n.val : ℝ)⁻¹ • L : Set E) : ℝ) / (n.val : ℝ) ^ card ι)
      (comap Subtype.val atTop) (𝓝 (volume.real ((b.ofZLatticeBasis ℝ).equivFun '' s))) := by
  refine Tendsto.congr' ?_
    (tendsto_card_div_pow_atTop_volume ((b.ofZLatticeBasis ℝ).equivFun '' s) ?_ ?_ hs₃)
  · refine Eventually.of_forall fun n ↦ ?_
    have hn : (n.val : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr n.property
    refine congrArg (fun m : ℕ ↦ (m : ℝ) / (n.val : ℝ) ^ card ι) ?_
    refine Nat.card_congr <| ((b.ofZLatticeBasis ℝ).equivFun.toEquiv.subtypeEquiv fun x ↦ ?_).symm
    simp_rw [Set.mem_inter_iff, ← b.ofZLatticeBasis_span ℝ, LinearEquiv.coe_toEquiv,
      Basis.equivFun_apply, Set.mem_image, DFunLike.coe_fn_eq, EmbeddingLike.apply_eq_iff_eq,
      exists_eq_right, and_congr_right_iff, Set.mem_inv_smul_set_iff₀
      hn, ← Finsupp.coe_smul, ← map_smul, SetLike.mem_coe,
      Basis.mem_span_iff_repr_mem, Pi.basisFun_repr, implies_true]
  · rw [← NormedSpace.isVonNBounded_iff ℝ] at hs₁ ⊢
    exact Bornology.IsVonNBounded.image hs₁ ((b.ofZLatticeBasis ℝ).equivFunL : E →L[ℝ] ι → ℝ)
  · exact (b.ofZLatticeBasis ℝ).equivFunL.toHomeomorph.toMeasurableEquiv.measurableSet_image.mpr hs₂

private theorem tendsto_card_le_div''_aux
    {X : Set E} (hX : ∀ ⦃x⦄ ⦃r : ℝ⦄, x ∈ X → 0 < r → r • x ∈ X)
    {F : E → ℝ} (hF₁ : ∀ x ⦃r : ℝ⦄, 0 ≤ r → F (r • x) = r ^ card ι * (F x)) {c : ℝ} (hc : 0 < c) :
    c • {x ∈ X | F x ≤ 1} = {x ∈ X | F x ≤ c ^ card ι} := by
  ext x
  simp_rw [Set.mem_smul_set_iff_inv_smul_mem₀ hc.ne', Set.mem_ofPred_eq, hF₁ _
    (inv_pos_of_pos hc).le, inv_pow₀, inv_mul_le_iff₀ (pow_pos hc _), mul_one, and_congr_left_iff]
  exact fun _ ↦ ⟨fun h ↦ (smul_inv_smul₀ (ha := hc.ne'.isUnit) x) ▸ hX h hc,
    fun h ↦ hX h (inv_pos_of_pos hc)⟩

/-- A version of `ZLattice.covolume.tendsto_card_le_div` for the general case;
see the `Naming conventions` section in the introduction. -/
theorem tendsto_card_le_div'' [FiniteDimensional ℝ E] [SigmaAlgebra E] [BorelSpace E]
    [Nonempty ι] {X : Set E} (hX : ∀ ⦃x⦄ ⦃r : ℝ⦄, x ∈ X → 0 < r → r • x ∈ X)
    {F : E → ℝ} (h₁ : ∀ x ⦃r : ℝ⦄, 0 ≤ r → F (r • x) = r ^ card ι * (F x))
    (h₂ : IsBounded {x ∈ X | F x ≤ 1}) (h₃ : MeasurableSet {x ∈ X | F x ≤ 1})
    (h₄ : volume (frontier ((b.ofZLatticeBasis ℝ L).equivFun '' {x | x ∈ X ∧ F x ≤ 1})) = 0) :
    Tendsto (fun c : {c : ℝ // c ≠ 0} ↦
      Checked.div (Nat.card ({x ∈ X | F x ≤ c.val} ∩ L : Set E) : ℝ) c.val c.property.isUnit)
      (comap Subtype.val atTop)
      (𝓝 (volume.real ((b.ofZLatticeBasis ℝ).equivFun '' {x ∈ X | F x ≤ 1}))) := by
  let Domain := {c : ℝ // c ≠ 0}
  let levelOne := {x ∈ X | F x ≤ 1}
  let image := (b.ofZLatticeBasis ℝ).equivFun '' levelOne
  let lattice := span ℤ (Set.range (Pi.basisFun ℝ ι))
  have hd : 0 < (card ι : ℝ) := Nat.cast_pos.mpr card_pos
  let scale (c : Domain) : ℝ := |c.val| ^ (card ι : ℝ)⁻¹
  have scale_pos (c : Domain) : 0 < scale c := Real.rpow_pos_of_pos (abs_pos.mpr c.property) _
  let embed (c : Domain) : Domain := ⟨scale c, (scale_pos c).ne'⟩
  have hv : Tendsto (Subtype.val : Domain → ℝ) (comap Subtype.val atTop) atTop := tendsto_comap
  have hscale : Tendsto embed (comap Subtype.val atTop) (comap Subtype.val atTop) := by
    apply tendsto_comap_iff.mpr
    change Tendsto scale (comap Subtype.val atTop) atTop
    exact (tendsto_rpow_atTop (inv_pos.mpr hd)).comp (tendsto_abs_atTop_atTop.comp hv)
  refine Tendsto.congr' ?_ <| (tendsto_card_div_pow_atTop_volume'
      image ?_ ?_ h₄ fun x y hx hy ↦ ?_).comp hscale
  · filter_upwards [hv.eventually (eventually_gt_atTop (0 : ℝ))] with c hc
    have ha := scale_pos c
    have hi : (scale c)⁻¹ ≠ 0 := inv_ne_zero
    have hpow : scale c ^ card ι = c.val := by
      change (|c.val| ^ (card ι : ℝ)⁻¹) ^ card ι = c.val
      rw [abs_of_pos hc, ← Real.rpow_natCast, Real.rpow_inv_rpow hc.le hd.ne']
    have hcard : Nat.card (image ∩ (scale c)⁻¹ • lattice : Set (ι → ℝ)) =
        Nat.card ({x ∈ X | F x ≤ c.val} ∩ L : Set E) := by
      refine Eq.symm (Nat.card_congr <| Equiv.subtypeEquiv
        ((b.ofZLatticeBasis ℝ).equivFun.toEquiv.trans (Equiv.smulRight hi)) fun _ ↦ ?_)
      dsimp only [lattice, image, levelOne]
      rw [Set.mem_inter_iff, Set.mem_inter_iff, Equiv.trans_apply, LinearEquiv.coe_toEquiv,
        Equiv.smulRight_apply, Set.smul_mem_smul_set_iff₀ hi,
        ← Set.mem_smul_set_iff_inv_smul_mem₀ ha.ne', ← image_smul_set,
        tendsto_card_le_div''_aux hX h₁ ha, hpow]
      simp_rw [SetLike.mem_coe, Set.mem_image, EmbeddingLike.apply_eq_iff_eq, exists_eq_right,
        and_congr_right_iff, ← b.ofZLatticeBasis_span ℝ, Basis.mem_span_iff_repr_mem,
        Pi.basisFun_repr, Basis.equivFun_apply, implies_true]
    change (Nat.card (image ∩ (scale c)⁻¹ • lattice : Set (ι → ℝ)) : ℝ) / scale c ^ card ι =
      Checked.div (Nat.card ({x ∈ X | F x ≤ c.val} ∩ L : Set E) : ℝ) c.val c.property.isUnit
    apply div_eq_div_iff.mpr
    rw [hpow, hcard]
  · rw [← NormedSpace.isVonNBounded_iff ℝ] at h₂ ⊢
    exact Bornology.IsVonNBounded.image h₂ ((b.ofZLatticeBasis ℝ).equivFunL : E →L[ℝ] ι → ℝ)
  · exact (b.ofZLatticeBasis ℝ).equivFunL.toHomeomorph.toMeasurableEquiv.measurableSet_image.mpr h₃
  · dsimp only [image, levelOne]
    simp_rw [← image_smul_set]
    apply Set.image_mono
    rw [tendsto_card_le_div''_aux hX h₁ hx,
      tendsto_card_le_div''_aux hX h₁ (lt_of_lt_of_le hx hy)]
    exact fun a ⟨ha₁, ha₂⟩ ↦ ⟨ha₁, le_trans ha₂ <| pow_le_pow_left₀ (le_of_lt hx) hy _⟩

end General

section Pi

open Filter Fintype Pointwise Bornology

open scoped Topology

private theorem frontier_equivFun {E : Type*} [AddCommGroup E] [Module ℝ E] {ι : Type*} [Finite ι]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [T2Space E]
    (b : Basis ι ℝ E) (s : Set E) :
    frontier (b.equivFun '' s) = b.equivFun '' (frontier s) := by
  rw [LinearEquiv.image_eq_preimage_symm, LinearEquiv.image_eq_preimage_symm]
  exact (Homeomorph.preimage_frontier b.equivFunL.toHomeomorph.symm s).symm

variable {ι : Type*} [Fintype ι]
variable (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]

theorem tendsto_card_div_pow (b : Basis ι ℤ L) {s : Set (ι → ℝ)} (hs₁ : IsBounded s)
    (hs₂ : MeasurableSet s) (hs₃ : volume (frontier s) = 0) :
    Tendsto (fun n : {n : ℕ // n ≠ 0} ↦
      letI : NeZero n.val := ⟨n.property⟩
      (Nat.card (s ∩ (n.val : ℝ)⁻¹ • L : Set (ι → ℝ)) : ℝ) / (n.val : ℝ) ^ card ι)
      (comap Subtype.val atTop)
      (𝓝 (Checked.div (volume.real s) (covolume L) (covolume_ne_zero L volume).isUnit)) := by
  convert! tendsto_card_div_pow'' b hs₁ hs₂ ?_
  · simp only [measureReal_def]
    rw [volume_image_eq_volume_div_covolume L b, toReal_div_ofReal_pos _ (covolume_pos L volume)]
  · rw [frontier_equivFun, volume_image_eq_volume_div_covolume L b,
      ENNReal.div_eq_mul_inv, hs₃, zero_mul]

theorem tendsto_card_le_div {X : Set (ι → ℝ)} (hX : ∀ ⦃x⦄ ⦃r : ℝ⦄, x ∈ X → 0 < r → r • x ∈ X)
    {F : (ι → ℝ) → ℝ} (h₁ : ∀ x ⦃r : ℝ⦄, 0 ≤ r → F (r • x) = r ^ card ι * (F x))
    (h₂ : IsBounded {x ∈ X | F x ≤ 1}) (h₃ : MeasurableSet {x ∈ X | F x ≤ 1})
    (h₄ : volume (frontier {x | x ∈ X ∧ F x ≤ 1}) = 0) [Nonempty ι] :
    Tendsto (fun c : {c : ℝ // c ≠ 0} ↦ Checked.div
      (Nat.card ({x ∈ X | F x ≤ c.val} ∩ L : Set (ι → ℝ)) : ℝ) c.val c.property.isUnit)
      (comap Subtype.val atTop)
      (𝓝 (Checked.div (volume.real {x ∈ X | F x ≤ 1}) (covolume L)
        (covolume_ne_zero L volume).isUnit)) := by
  let e : Free.ChooseBasisIndex ℤ ↥L ≃ ι := by
    refine Fintype.equivOfCardEq ?_
    rw [← finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ, finrank_fintype_fun_eq_card]
  let b := (Module.Free.chooseBasis ℤ L).reindex e
  convert! tendsto_card_le_div'' b hX h₁ h₂ h₃ ?_
  · simp only [measureReal_def]
    rw [volume_image_eq_volume_div_covolume L b, toReal_div_ofReal_pos _ (covolume_pos L volume)]
  · rw [frontier_equivFun, volume_image_eq_volume_div_covolume L b,
      ENNReal.div_eq_mul_inv, h₄, zero_mul]

end Pi

section InnerProductSpace

open Filter Pointwise Bornology

open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [SigmaAlgebra E] [BorelSpace E]
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

/-- A version of `ZLattice.covolume.tendsto_card_div_pow` for the `InnerProductSpace` case;
see the `Naming convention` section in the introduction. -/
theorem tendsto_card_div_pow' {s : Set E} (hs₁ : IsBounded s) (hs₂ : MeasurableSet s)
    (hs₃ : volume (frontier s) = 0) :
    Tendsto (fun n : {n : ℕ // n ≠ 0} ↦
      letI : NeZero n.val := ⟨n.property⟩
      (Nat.card (s ∩ (n.val : ℝ)⁻¹ • L : Set E) : ℝ) / (n.val : ℝ) ^ finrank ℝ E)
      (comap Subtype.val atTop)
      (𝓝 (Checked.div (volume.real s) (covolume L) (covolume_ne_zero L volume).isUnit)) := by
  let b := Module.Free.chooseBasis ℤ L
  convert! tendsto_card_div_pow'' b hs₁ hs₂ ?_
  · rw [← finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ L]
  · simp only [measureReal_def]
    rw [volume_image_eq_volume_div_covolume' L b hs₂.nullMeasurableSet,
      toReal_div_ofReal_pos _ (covolume_pos L volume)]
  · rw [frontier_equivFun,
      volume_image_eq_volume_div_covolume' L b (NullMeasurableSet.of_null hs₃),
      ENNReal.div_eq_mul_inv, hs₃, zero_mul]

/-- A version of `ZLattice.covolume.tendsto_card_le_div` for the `InnerProductSpace` case;
see the `Naming convention` section in the introduction. -/
theorem tendsto_card_le_div' [Nontrivial E] {X : Set E} {F : E → ℝ}
    (hX : ∀ ⦃x⦄ ⦃r : ℝ⦄, x ∈ X → 0 < r → r • x ∈ X)
    (h₁ : ∀ x ⦃r : ℝ⦄, 0 ≤ r → F (r • x) = r ^ finrank ℝ E * (F x))
    (h₂ : IsBounded {x ∈ X | F x ≤ 1}) (h₃ : MeasurableSet {x ∈ X | F x ≤ 1})
    (h₄ : volume (frontier {x ∈ X | F x ≤ 1}) = 0) :
    Tendsto (fun c : {c : ℝ // c ≠ 0} ↦
      Checked.div (Nat.card ({x ∈ X | F x ≤ c.val} ∩ L : Set E) : ℝ) c.val c.property.isUnit)
      (comap Subtype.val atTop)
      (𝓝 (Checked.div (volume.real {x ∈ X | F x ≤ 1}) (covolume L)
        (covolume_ne_zero L volume).isUnit)) := by
  let b := Module.Free.chooseBasis ℤ L
  convert! tendsto_card_le_div'' b hX ?_ h₂ h₃ ?_
  · simp only [measureReal_def]
    rw [volume_image_eq_volume_div_covolume' L b h₃.nullMeasurableSet,
      toReal_div_ofReal_pos _ (covolume_pos L volume)]
  · have : Nontrivial L := nontrivial_of_finrank_pos <| (ZLattice.rank ℝ L).symm ▸ finrank_pos
    infer_instance
  · rwa [← finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ L]
  · rw [frontier_equivFun,
      volume_image_eq_volume_div_covolume' L b (NullMeasurableSet.of_null h₄),
      ENNReal.div_eq_mul_inv, h₄, zero_mul]

end InnerProductSpace

end covolume

end ZLattice
