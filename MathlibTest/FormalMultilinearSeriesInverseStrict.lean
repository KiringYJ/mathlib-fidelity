import Mathlib.Analysis.Analytic.Inverse

/-!
# Formal one-sided inverses of formal multilinear series

`FormalMultilinearSeries.leftInv` and `FormalMultilinearSeries.rightInv` take a continuous linear
one-sided inverse of the linear term together with the proof that it is one. Formal one-sided
inverses exist exactly when such a linear inverse exists. They need not be unique when the linear
term is not invertible, and the linear inverse selects one of them, which the characterization
theorems identify. When the linear term is invertible, formal left and right inverses with the
same constant coefficient coincide and are unique.
-/

noncomputable section

open FormalMultilinearSeries

/-! ### Missing and invalid evidence -/

/--
error: numerals are data in Lean, but the expected type is a proposition
  Function.RightInverse ⇑(ContinuousLinearMap.id ℝ ℝ) ⇑((continuousMultilinearCurryFin1 ℝ ℝ ℝ) (p 1)) : Prop
-/
#guard_msgs in
example (p : FormalMultilinearSeries ℝ ℝ ℝ) : FormalMultilinearSeries ℝ ℝ ℝ :=
  p.rightInv (ContinuousLinearMap.id ℝ ℝ) 0

/-! The former counterexample: the zero series accepted the identity in place of an inverse of its
linear term, and the result was not a right inverse. The evidence is now unprovable. -/

example : ¬ Function.RightInverse (ContinuousLinearMap.id ℝ ℝ)
    (continuousMultilinearCurryFin1 ℝ ℝ ℝ ((0 : FormalMultilinearSeries ℝ ℝ ℝ) 1)) := by
  intro h
  simpa using h 1

/--
error: unsolved goals
x✝ : ℝ
⊢ 0 = x✝
-/
#guard_msgs in
example : FormalMultilinearSeries ℝ ℝ ℝ :=
  (0 : FormalMultilinearSeries ℝ ℝ ℝ).rightInv (ContinuousLinearMap.id ℝ ℝ) (fun _ ↦ by simp) 0

/-- The zero series has no formal inverse on either side. -/
example : ¬ ∃ q : FormalMultilinearSeries ℝ ℝ ℝ,
    (0 : FormalMultilinearSeries ℝ ℝ ℝ).comp q =
      id ℝ ℝ ((0 : FormalMultilinearSeries ℝ ℝ ℝ) 0 0) := by
  rw [exists_comp_eq_id_iff_hasRightInverse]
  rintro ⟨s, hs⟩
  simpa using hs 1

example (x : ℝ) : ¬ ∃ q : FormalMultilinearSeries ℝ ℝ ℝ,
    q.comp (0 : FormalMultilinearSeries ℝ ℝ ℝ) = id ℝ ℝ x := by
  rw [exists_comp_eq_id_iff_hasLeftInverse]
  rintro ⟨r, hr⟩
  simpa using hr 1

/-! ### Invertible linear term and a nonzero constant coefficient -/

/-- The identity series expanded at `5`. -/
def idAtFive : FormalMultilinearSeries ℝ ℝ ℝ := id ℝ ℝ 5

theorem idAtFive_leftInverse : Function.LeftInverse (ContinuousLinearMap.id ℝ ℝ)
    (continuousMultilinearCurryFin1 ℝ ℝ ℝ (idAtFive 1)) := fun _ ↦ rfl

theorem idAtFive_rightInverse : Function.RightInverse (ContinuousLinearMap.id ℝ ℝ)
    (continuousMultilinearCurryFin1 ℝ ℝ ℝ (idAtFive 1)) := fun _ ↦ rfl

example (x : ℝ) : (idAtFive.leftInv _ idAtFive_leftInverse x).comp idAtFive = id ℝ ℝ x :=
  leftInv_comp _ _ _ _

example (x : ℝ) : idAtFive.comp (idAtFive.rightInv _ idAtFive_rightInverse x) = id ℝ ℝ 5 := by
  rw [comp_rightInv]
  simp only [idAtFive, id_apply_zero]

example (x : ℝ) :
    idAtFive.leftInv _ idAtFive_leftInverse x = idAtFive.rightInv _ idAtFive_rightInverse x :=
  leftInv_eq_rightInv _ _ _ _ _ _

/-- Uniqueness of the formal inverse with a given constant coefficient. -/
example (x : ℝ) (q : FormalMultilinearSeries ℝ ℝ ℝ) (hq : q.comp idAtFive = id ℝ ℝ x) :
    q = idAtFive.leftInv _ idAtFive_leftInverse x := by
  rw [eq_rightInv_of_comp_eq_id_left _ _ idAtFive_rightInverse hq, leftInv_eq_rightInv]

example (x : ℝ) (q : FormalMultilinearSeries ℝ ℝ ℝ) (hq : idAtFive.comp q = id ℝ ℝ (idAtFive 0 0))
    (hx : q 0 0 = x) : q = idAtFive.rightInv _ idAtFive_rightInverse x := by
  rw [eq_leftInv_of_comp_eq_id_right _ _ idAtFive_leftInverse hq hx, leftInv_eq_rightInv]

/-- The evidence is a proposition: different proofs give the same series. -/
example (p : FormalMultilinearSeries ℝ ℝ ℝ) (r : ℝ →L[ℝ] ℝ)
    (hr hr' : Function.LeftInverse r (continuousMultilinearCurryFin1 ℝ ℝ ℝ (p 1))) (x : ℝ) :
    p.leftInv r hr x = p.leftInv r hr' x :=
  rfl

/-- Any continuous linear left inverse supplies the evidence. -/
example (p : FormalMultilinearSeries ℝ ℝ ℝ)
    (h : (continuousMultilinearCurryFin1 ℝ ℝ ℝ (p 1)).HasLeftInverse) (x : ℝ) :
    ∃ (r : ℝ →L[ℝ] ℝ) (hr : Function.LeftInverse r (continuousMultilinearCurryFin1 ℝ ℝ ℝ (p 1))),
      (p.leftInv r hr x).comp p = id ℝ ℝ x := by
  obtain ⟨r, hr⟩ := h
  exact ⟨r, hr, leftInv_comp _ _ _ _⟩

/-! ### Injective linear term that is not surjective -/

/-- The series of the inclusion `ℝ → ℝ × ℝ` at `0`. -/
def inlSeries : FormalMultilinearSeries ℝ ℝ (ℝ × ℝ) :=
  (ContinuousLinearMap.inl ℝ ℝ ℝ).compFormalMultilinearSeries (id ℝ ℝ 0)

theorem fst_leftInverse_inlSeries : Function.LeftInverse (ContinuousLinearMap.fst ℝ ℝ ℝ)
    (continuousMultilinearCurryFin1 ℝ ℝ (ℝ × ℝ) (inlSeries 1)) := fun _ ↦ rfl

theorem fst_add_snd_leftInverse_inlSeries :
    Function.LeftInverse (ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ)
      (continuousMultilinearCurryFin1 ℝ ℝ (ℝ × ℝ) (inlSeries 1)) := fun v ↦ by
  change (ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ) (v, 0) = v
  simp

example : (inlSeries.leftInv _ fst_leftInverse_inlSeries 0).comp inlSeries = id ℝ ℝ 0 :=
  leftInv_comp _ _ _ _

example : (inlSeries.leftInv _ fst_add_snd_leftInverse_inlSeries 0).comp inlSeries = id ℝ ℝ 0 :=
  leftInv_comp _ _ _ _

/-- Formal left inverses of a noninvertible linear term need not be unique. -/
example : inlSeries.leftInv _ fst_leftInverse_inlSeries 0 ≠
    inlSeries.leftInv _ fst_add_snd_leftInverse_inlSeries 0 := by
  intro h
  have := congr_arg (fun q : FormalMultilinearSeries ℝ (ℝ × ℝ) ℝ ↦ q 1 fun _ ↦ ((0 : ℝ), (1 : ℝ)))
    h
  simp at this

/-- The coefficients of the left inverse depend on their vector arguments only through their
images under the chosen linear left inverse, and this characterizes it among formal left inverses
with the same constant coefficient. -/
example : (inlSeries.leftInv _ fst_leftInverse_inlSeries 0).compContinuousLinearMap
      ((continuousMultilinearCurryFin1 ℝ ℝ (ℝ × ℝ) (inlSeries 1)).comp
        (ContinuousLinearMap.fst ℝ ℝ ℝ)) =
    inlSeries.leftInv _ fst_leftInverse_inlSeries 0 :=
  leftInv_compContinuousLinearMap _ _ _ _

example (q : FormalMultilinearSeries ℝ (ℝ × ℝ) ℝ) (hq : q.comp inlSeries = id ℝ ℝ 0)
    (hq' : q.compContinuousLinearMap ((continuousMultilinearCurryFin1 ℝ ℝ (ℝ × ℝ) (inlSeries 1)).comp
      (ContinuousLinearMap.fst ℝ ℝ ℝ)) = q) :
    q = inlSeries.leftInv _ fst_leftInverse_inlSeries 0 :=
  eq_leftInv_of_comp_eq_id_of_compContinuousLinearMap_eq _ _ _ hq hq'

/-- The left inverse is the formal inverse of `r ∘ p` precomposed with `r`. -/
example (p : FormalMultilinearSeries ℝ ℝ (ℝ × ℝ)) {r : ℝ × ℝ →L[ℝ] ℝ}
    (hr : Function.LeftInverse r (continuousMultilinearCurryFin1 ℝ ℝ (ℝ × ℝ) (p 1))) (x : ℝ) :
    p.leftInv r hr x =
      ((r.compFormalMultilinearSeries p).rightInv (ContinuousLinearMap.id ℝ ℝ) (fun v ↦ hr v)
        x).compContinuousLinearMap r :=
  leftInv_eq_rightInv_compFormalMultilinearSeries_compContinuousLinearMap _ _ _ _

/-- A nonsurjective linear term admits no formal right inverse. -/
example : ¬ ∃ q : FormalMultilinearSeries ℝ (ℝ × ℝ) ℝ,
    inlSeries.comp q = id ℝ (ℝ × ℝ) (inlSeries 0 0) := by
  rw [exists_comp_eq_id_iff_hasRightInverse]
  intro h
  obtain ⟨y, hy⟩ := h.surjective ((0 : ℝ), (1 : ℝ))
  simp [inlSeries] at hy

/-- Convergence does not require an invertible linear term. -/
example (p : FormalMultilinearSeries ℝ ℝ (ℝ × ℝ)) (hp : 0 < p.radius) {r : ℝ × ℝ →L[ℝ] ℝ}
    (hr : Function.LeftInverse r (continuousMultilinearCurryFin1 ℝ ℝ (ℝ × ℝ) (p 1))) (x : ℝ) :
    0 < (p.leftInv r hr x).radius :=
  radius_leftInv_pos_of_radius_pos hp

/-! ### Surjective linear term that is not injective -/

/-- The series of the projection `ℝ × ℝ → ℝ` at `0`. -/
def fstSeries : FormalMultilinearSeries ℝ (ℝ × ℝ) ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).compFormalMultilinearSeries (id ℝ (ℝ × ℝ) 0)

theorem inl_rightInverse_fstSeries : Function.RightInverse (ContinuousLinearMap.inl ℝ ℝ ℝ)
    (continuousMultilinearCurryFin1 ℝ (ℝ × ℝ) ℝ (fstSeries 1)) := fun _ ↦ rfl

theorem inl_add_inr_rightInverse_fstSeries :
    Function.RightInverse (ContinuousLinearMap.inl ℝ ℝ ℝ + ContinuousLinearMap.inr ℝ ℝ ℝ)
      (continuousMultilinearCurryFin1 ℝ (ℝ × ℝ) ℝ (fstSeries 1)) := fun v ↦ by
  change ((ContinuousLinearMap.inl ℝ ℝ ℝ + ContinuousLinearMap.inr ℝ ℝ ℝ) v).1 = v
  simp

example : fstSeries.comp (fstSeries.rightInv _ inl_rightInverse_fstSeries 0) =
    id ℝ ℝ (fstSeries 0 0) :=
  comp_rightInv _ _ _ _

/-- Formal right inverses of a noninvertible linear term need not be unique. -/
example : fstSeries.rightInv _ inl_rightInverse_fstSeries 0 ≠
    fstSeries.rightInv _ inl_add_inr_rightInverse_fstSeries 0 := by
  intro h
  have := congr_arg (fun q : FormalMultilinearSeries ℝ ℝ (ℝ × ℝ) ↦ q 1 fun _ ↦ (1 : ℝ)) h
  simp at this

/-- The coefficients of positive order of the right inverse take values in the range of the chosen
linear right inverse, and this characterizes it among formal right inverses with the same constant
coefficient. -/
example {n : ℕ} (hn : 0 < n) (v : Fin n → ℝ) :
    fstSeries.rightInv _ inl_rightInverse_fstSeries 0 n v ∈
      Set.range (ContinuousLinearMap.inl ℝ ℝ ℝ) :=
  rightInv_apply_mem_range _ _ _ _ hn v

example (q : FormalMultilinearSeries ℝ ℝ (ℝ × ℝ)) (hq : fstSeries.comp q = id ℝ ℝ (fstSeries 0 0))
    (hx : q 0 0 = 0) (hrange : ∀ n, 0 < n → ∀ v, q n v ∈ Set.range (ContinuousLinearMap.inl ℝ ℝ ℝ)) :
    q = fstSeries.rightInv _ inl_rightInverse_fstSeries 0 :=
  eq_rightInv_of_comp_eq_id_of_apply_mem_range _ _ _ hq hx hrange

/-- A noninjective linear term admits no formal left inverse. -/
example (x : ℝ × ℝ) : ¬ ∃ q : FormalMultilinearSeries ℝ ℝ (ℝ × ℝ),
    q.comp fstSeries = id ℝ (ℝ × ℝ) x := by
  rw [exists_comp_eq_id_iff_hasLeftInverse]
  intro h
  have := h.injective (a₁ := ((0 : ℝ), (0 : ℝ))) (a₂ := ((0 : ℝ), (1 : ℝ))) (by simp [fstSeries])
  simp at this

/-! ### A zero-dimensional domain -/

/-- The linear term of any series on a zero-dimensional space has a left inverse, although it is not
invertible when the target is nontrivial. -/
example (p : FormalMultilinearSeries ℝ (Fin 0 → ℝ) ℝ) (x : Fin 0 → ℝ) :
    ∃ q : FormalMultilinearSeries ℝ ℝ (Fin 0 → ℝ), q.comp p = id ℝ (Fin 0 → ℝ) x :=
  (exists_comp_eq_id_iff_hasLeftInverse p x).2 ⟨0, fun _ ↦ Subsingleton.elim _ _⟩

example : ¬ ∃ q : FormalMultilinearSeries ℝ ℝ (Fin 0 → ℝ),
    (0 : FormalMultilinearSeries ℝ (Fin 0 → ℝ) ℝ).comp q =
      id ℝ ℝ ((0 : FormalMultilinearSeries ℝ (Fin 0 → ℝ) ℝ) 0 0) := by
  rw [exists_comp_eq_id_iff_hasRightInverse]
  rintro ⟨s, hs⟩
  simpa using hs 1

/-! ### Analytic inverses -/

example {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : OpenPartialHomeomorph E F) {a : E} (h0 : a ∈ f.source)
    {p : FormalMultilinearSeries ℝ E F} (h : HasFPowerSeriesAt f p a) (i : E ≃L[ℝ] F)
    (hp : continuousMultilinearCurryFin1 ℝ E F (p 1) = i) :
    HasFPowerSeriesAt f.symm
      (p.leftInv (i.symm : F →L[ℝ] E) (fun v ↦ by simp [hp]) a) (f a) :=
  f.hasFPowerSeriesAt_symm h0 h _
