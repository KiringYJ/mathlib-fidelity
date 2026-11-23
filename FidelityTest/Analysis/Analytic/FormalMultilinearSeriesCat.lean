import Mathlib.Analysis.Analytic.FormalMultilinearSeriesCat

/-!
# Split morphisms and isomorphisms of topological modules and of formal multilinear series

In `TopModuleCat`, split monomorphisms and epimorphisms are the continuous linear maps with a
continuous linear left or right inverse, and isomorphisms are the continuous linear equivalences.
In `FormalMultilinearSeriesCat`, a morphism splits, or is an isomorphism, exactly when its linear
term does, and the inverse of an isomorphism is its formal left and right inverse.
-/

noncomputable section

open CategoryTheory FormalMultilinearSeriesCat

/-! ### Topological modules -/

example : IsSplitMono (TopModuleCat.ofHom (ContinuousLinearMap.inl ℝ ℝ ℝ)) :=
  (TopModuleCat.isSplitMono_iff_hasLeftInverse _).2 ContinuousLinearMap.HasLeftInverse.inl

/-- The inclusion `ℝ → ℝ × ℝ` is not surjective, so it is not a split epimorphism. -/
example : ¬ IsSplitEpi (TopModuleCat.ofHom (ContinuousLinearMap.inl ℝ ℝ ℝ)) := by
  rw [TopModuleCat.isSplitEpi_iff_hasRightInverse]
  intro h
  obtain ⟨y, hy⟩ := h.surjective ((0 : ℝ), (1 : ℝ))
  simp at hy

example : IsIso (TopModuleCat.ofHom (ContinuousLinearEquiv.neg ℝ (M := ℝ)).toContinuousLinearMap) :=
  (TopModuleCat.isIso_iff_isInvertible _).2 ⟨_, rfl⟩

/-! ### Formal multilinear series -/

/-- The real line with the point `a`. -/
abbrev lineAt (a : ℝ) : FormalMultilinearSeriesCat.{0} ℝ := of ℝ ℝ a

/-- The plane with the origin. -/
abbrev planeAtZero : FormalMultilinearSeriesCat.{0} ℝ := of ℝ (ℝ × ℝ) 0

/-- The translation `y ↦ y + 5`, expanded at `0`. -/
def translate : lineAt 0 ⟶ lineAt 5 := ⟨FormalMultilinearSeries.id ℝ ℝ 5, rfl⟩

/-- The inclusion `ℝ → ℝ × ℝ`, expanded at `0`. -/
def inclusion : lineAt 0 ⟶ planeAtZero :=
  ⟨(ContinuousLinearMap.inl ℝ ℝ ℝ).compFormalMultilinearSeries (FormalMultilinearSeries.id ℝ ℝ 0),
    map_zero (ContinuousLinearMap.inl ℝ ℝ ℝ)⟩

/-- Every formal multilinear series is a morphism into its target pointed at its constant
coefficient. -/
example (p : FormalMultilinearSeries ℝ ℝ ℝ) : (ofSeries p 0).series = p := by
  simp

example : IsSplitMono inclusion :=
  (isSplitMono_iff_hasLeftInverse _).2 ⟨ContinuousLinearMap.fst ℝ ℝ ℝ, fun _ ↦ rfl⟩

example : ¬ IsSplitEpi inclusion := by
  rw [isSplitEpi_iff_hasRightInverse]
  intro h
  obtain ⟨y, hy⟩ := h.surjective ((0 : ℝ), (1 : ℝ))
  exact zero_ne_one (congr_arg Prod.snd hy : (0 : ℝ) = 1)

/-- The linear term of the translation is the identity, so the translation is an isomorphism, even
though its source and target points differ. -/
example : IsIso translate :=
  (isIso_iff_isInvertible _).2 ⟨ContinuousLinearEquiv.refl ℝ ℝ, ContinuousLinearMap.ext fun _ ↦ rfl⟩

/-- The inclusion is not an isomorphism, since its linear term is not surjective. -/
example : ¬ IsIso inclusion := fun _ ↦ by
  have : IsSplitEpi inclusion := inferInstance
  rw [isSplitEpi_iff_hasRightInverse] at this
  obtain ⟨y, hy⟩ := this.surjective ((0 : ℝ), (1 : ℝ))
  exact zero_ne_one (congr_arg Prod.snd hy : (0 : ℝ) = 1)

/-- The inverse of an isomorphism is its formal left inverse. -/
example [IsIso translate] :
    (inv translate).series =
      translate.series.leftInv (ContinuousLinearMap.id ℝ ℝ) (fun _ ↦ rfl) 0 :=
  series_inv_eq_leftInv _ _ _

/-- Composition requires matching basepoints: no morphism into the line with the point `0` has the
identity series at `5` as its series. -/
example : ¬ ∃ f : lineAt 0 ⟶ lineAt 0, f.series = FormalMultilinearSeries.id ℝ ℝ 5 := by
  rintro ⟨f, hf⟩
  have h5 : f.series 0 0 = (5 : ℝ) :=
    (congr_arg (fun p : FormalMultilinearSeries ℝ ℝ ℝ ↦ p 0 0) hf).trans
      (FormalMultilinearSeries.id_apply_zero ℝ ℝ 5 0)
  have h0 : f.series 0 0 = (0 : ℝ) := f.series_coeff_zero
  norm_num [h5] at h0
