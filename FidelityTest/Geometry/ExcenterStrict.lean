import Mathlib.Geometry.Euclidean.Angle.Incenter

/-!
# Strict excenters

These tests ensure that the exsphere, excenter, exradius, touchpoints, and the weights of the
excenter and the touchpoints of a simplex are defined exactly when the excenter exists, that the
tactic `excenter_exists` supplies the routine evidence, and that it does not invent evidence.
-/

open Affine EuclideanGeometry

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-! The characterization of existence through the fallback weights is removed. -/

/-- info: Unknown constant `Affine.Simplex.sum_excenterWeights` -/
#guard_msgs in
#check_failure Affine.Simplex.sum_excenterWeights

/-- info: Unknown constant `Affine.Simplex.sum_excenterWeights_eq_one_iff` -/
#guard_msgs in
#check_failure Affine.Simplex.sum_excenterWeights_eq_one_iff

/-! A segment has no excenter opposite an endpoint, so none can be formed. -/

example (s : Simplex ℝ P 1) : ¬s.ExcenterExists {0} :=
  s.not_excenterExists_singleton 0

/-- error: this excenter needs a proof that it exists, `s.ExcenterExists signs` -/
#guard_msgs (substring := true) in
noncomputable example (s : Simplex ℝ P 1) : P := s.excenter {0}

/-! Excenters with general signs need evidence in three or more dimensions. -/

/-- error: this excenter needs a proof that it exists, `s.ExcenterExists signs` -/
#guard_msgs (substring := true) in
noncomputable example (s : Simplex ℝ P 3) (signs : Finset (Fin 4)) : P := s.excenter signs

/-- error: this excenter needs a proof that it exists, `s.ExcenterExists signs` -/
#guard_msgs (substring := true) in
noncomputable example (s : Simplex ℝ P 3) (signs : Finset (Fin 4)) : ℝ := s.exradius signs

/-- error: this excenter needs a proof that it exists, `s.ExcenterExists signs` -/
#guard_msgs (substring := true) in
noncomputable example (s : Simplex ℝ P 3) (signs : Finset (Fin 4)) (i : Fin 4) : P :=
  s.touchpoint signs i

/-! The weights take the proof explicitly. -/

/--
error: Application type mismatch: The argument
  i
has type
  Fin 4
of sort `Type` but is expected to have type
  s.ExcenterExists signs
of sort `Prop` in the application
  s.excenterWeights signs i
-/
#guard_msgs in
noncomputable example (s : Simplex ℝ P 3) (signs : Finset (Fin 4)) (i : Fin 4) : ℝ :=
  s.excenterWeights signs i

/-! Routine evidence is found. -/

example (s : Simplex ℝ P 3) : s.excenter ∅ = s.incenter := rfl

example (s : Simplex ℝ P 3) : s.excenter Finset.univ = s.incenter := by simp

noncomputable example (s : Simplex ℝ P 3) (i : Fin 4) : P := s.excenter {i}

noncomputable example (s : Simplex ℝ P 3) (i : Fin 4) : P := s.excenter {i}ᶜ

noncomputable example (t : Triangle ℝ P) (signs : Finset (Fin 3)) : P := t.excenter signs

noncomputable example (s : Simplex ℝ P 3) (signs : Finset (Fin 4))
    (h : s.ExcenterExists signs) : P :=
  s.excenter signs

noncomputable example (s : Simplex ℝ P 3) (signs : Finset (Fin 4))
    (h : s.ExcenterExists signs) : P :=
  s.excenter signsᶜ

example (s : Simplex ℝ P 3) (signs : Finset (Fin 4)) (h : s.ExcenterExists signs) (i : Fin 4) :
    dist (s.excenter signs) (s.touchpoint signs i) = s.exradius signs :=
  h.dist_excenter i

/-! Values do not depend on the proof, and the complement gives the same excenter. -/

example (s : Simplex ℝ P 3) (signs : Finset (Fin 4)) (h₁ h₂ : s.ExcenterExists signs) :
    s.excenter signs h₁ = s.excenter signs h₂ :=
  rfl

example (s : Simplex ℝ P 3) (signs : Finset (Fin 4)) (h : s.ExcenterExists signs) :
    s.excenter signsᶜ = s.excenter signs := by
  simp

example (s : Simplex ℝ P 3) (signs : Finset (Fin 4)) (h : s.ExcenterExists signs) :
    ∑ i, s.excenterWeights signs h i = 1 :=
  h.sum_excenterWeights_eq_one

/-! Existence is characterized by the equal-distance property. -/

example (s : Simplex ℝ P 3) {p : P} (hp : p ∈ affineSpan ℝ (Set.range s.points)) :
    (∃ r : ℝ, ∀ i, dist p ((s.faceOpposite i).orthogonalProjectionSpan p) = r) ↔
      ∃ signs, ∃ h : s.ExcenterExists signs, p = s.excenter signs h :=
  s.exists_forall_dist_eq_iff_exists_excenterExists_and_eq_excenter hp
