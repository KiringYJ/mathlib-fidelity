import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Topology.VectorBundle.ContinuousAlternatingMap
import Mathlib.Topology.VectorBundle.Hom

/-!
# Bundle coordinate changes live on the overlap

`Bundle.Trivialization.coordChange e₁ e₂ h₁ h₂` and `Bundle.Trivialization.coordChangeL R e e' hb`
are the coordinate changes between two trivializations at a point of the intersection of their base
sets, and they take the proofs that the point lies there.  The former values outside the overlap
are removed.  Continuity and smoothness of a coordinate change are statements about every map that
agrees with it on the overlap.
-/

open Bundle Set

variable {B F : Type*} [TopologicalSpace B] [TopologicalSpace F]
  {Z : Type*} [TopologicalSpace Z] {proj : Z → B}

/-! The coordinate change takes the base-set memberships. -/

example (e₁ e₂ : Trivialization F proj) {b : B} (h₁ : b ∈ e₁.baseSet) (h₂ : b ∈ e₂.baseSet)
    (x : F) : e₂.coordChange e₁ h₂ h₁ (e₁.coordChange e₂ h₁ h₂ x) = x := by
  rw [Trivialization.coordChange_coordChange, Trivialization.coordChange_same_apply]

example (e₁ e₂ : Trivialization F proj) {b : B} (h₁ : b ∈ e₁.baseSet) (h₂ : b ∈ e₂.baseSet) :
    ⇑(e₁.coordChangeHomeomorph e₂ h₁ h₂) = e₁.coordChange e₂ h₁ h₂ :=
  e₁.coordChangeHomeomorph_coe e₂ h₁ h₂

/--
error: Application type mismatch: The argument
  b
has type
  B
of sort `Type u_1` but is expected to have type
  ?_ ∈ e₁.baseSet
of sort `Prop` in the application
  e₁.coordChange e₂ b
-/
#guard_msgs in
example (e₁ e₂ : Trivialization F proj) (b : B) (x : F) : F := e₁.coordChange e₂ b x

/-! A membership in the first base set does not stand in for one in the second. -/

/--
error: Application type mismatch: The last
  h₁
argument has type
  b ∈ e₁.baseSet
but is expected to have type
  b ∈ e₂.baseSet
in the application
  e₁.coordChange e₂ h₁ h₁
-/
#guard_msgs in
example (e₁ e₂ : Trivialization F proj) {b : B} (h₁ : b ∈ e₁.baseSet) (x : F) : F :=
  e₁.coordChange e₂ h₁ h₁ x

/-! The linear coordinate change takes the overlap. -/

section Linear

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : B → Type*} [∀ b, AddCommMonoid (E b)]
  [∀ b, Module 𝕜 (E b)] {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  [TopologicalSpace (TotalSpace F' E)]

/--
error: Application type mismatch: The argument
  b
has type
  B
of sort `Type u_1` but is expected to have type
  ?_ ∈ e.baseSet ∩ e'.baseSet
of sort `Prop` in the application
  Trivialization.coordChangeL 𝕜 e e' b
-/
#guard_msgs in
example (e e' : Trivialization F' (π F' E)) [e.IsLinear 𝕜] [e'.IsLinear 𝕜] (b : B) :
    F' ≃L[𝕜] F' :=
  e.coordChangeL 𝕜 e' b

/-! The overlap is ordered: `b ∈ e'.baseSet ∩ e.baseSet` is a different hypothesis. -/

/--
error: Application type mismatch: The argument
  hb
has type
  b ∈ e'.baseSet ∩ e.baseSet
but is expected to have type
  ?_ ∈ e.baseSet ∩ e'.baseSet
in the application
  Trivialization.coordChangeL 𝕜 e e' hb
-/
#guard_msgs in
example (e e' : Trivialization F' (π F' E)) [e.IsLinear 𝕜] [e'.IsLinear 𝕜] {b : B}
    (hb : b ∈ e'.baseSet ∩ e.baseSet) : F' ≃L[𝕜] F' :=
  e.coordChangeL 𝕜 e' hb

example (e e' : Trivialization F' (π F' E)) [e.IsLinear 𝕜] [e'.IsLinear 𝕜] {b : B}
    (hb : b ∈ e.baseSet ∩ e'.baseSet) (y : F') :
    e.coordChangeL 𝕜 e' hb y = (e' ⟨b, e.symm b y⟩).2 :=
  e.coordChangeL_apply e' hb y

example (e e' : Trivialization F' (π F' E)) [e.IsLinear 𝕜] [e'.IsLinear 𝕜] {b : B}
    (hb : b ∈ e.baseSet ∩ e'.baseSet) :
    (e.coordChangeL 𝕜 e' hb).symm = e'.coordChangeL 𝕜 e (Set.mem_inter hb.2 hb.1) :=
  e.symm_coordChangeL e' hb

/-! The linear coordinate change is the coordinate change of the underlying trivializations. -/

example (e e' : Trivialization F' (π F' E)) [e.IsLinear 𝕜] [e'.IsLinear 𝕜] {b : B}
    (hb : b ∈ e.baseSet ∩ e'.baseSet) :
    ⇑(e.coordChangeL 𝕜 e' hb) = e.coordChange e' hb.1 hb.2 :=
  e.coe_coordChangeL_eq_coordChange e' hb

/-! Continuity is a statement about every map that agrees with the coordinate change on the
overlap. -/

example [∀ b, TopologicalSpace (E b)] [FiberBundle F' E] [VectorBundle 𝕜 F' E]
    (e e' : Trivialization F' (π F' E)) [MemTrivializationAtlas e] [MemTrivializationAtlas e']
    {φ : B → F' →L[𝕜] F'}
    (hφ : ∀ b (hb : b ∈ e.baseSet ∩ e'.baseSet), φ b = e.coordChangeL 𝕜 e' hb) :
    ContinuousOn φ (e.baseSet ∩ e'.baseSet) :=
  continuousOn_coordChangeL 𝕜 e e' hφ

end Linear

/-! The coordinate changes of the bundles of continuous linear and alternating maps take the
four-fold overlap. -/

section Hom

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁] {E₁ : B → Type*}
  [∀ b, AddCommGroup (E₁ b)] [∀ b, Module 𝕜 (E₁ b)] [TopologicalSpace (TotalSpace F₁ E₁)]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] {E₂ : B → Type*}
  [∀ b, AddCommGroup (E₂ b)] [∀ b, Module 𝕜 (E₂ b)] [TopologicalSpace (TotalSpace F₂ E₂)]
  (e₁ e₁' : Trivialization F₁ (π F₁ E₁)) (e₂ e₂' : Trivialization F₂ (π F₂ E₂))
  [e₁.IsLinear 𝕜] [e₁'.IsLinear 𝕜] [e₂.IsLinear 𝕜] [e₂'.IsLinear 𝕜]

/--
error: Application type mismatch: The argument
  b
has type
  B
of sort `Type u_1` but is expected to have type
  ?_ ∈ e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet)
of sort `Prop` in the application
  Pretrivialization.continuousLinearMapCoordChange (RingHom.id 𝕜) e₁ e₁' e₂ e₂' b
-/
#guard_msgs in
example (b : B) : (F₁ →L[𝕜] F₂) →L[𝕜] F₁ →L[𝕜] F₂ :=
  Pretrivialization.continuousLinearMapCoordChange (RingHom.id 𝕜) e₁ e₁' e₂ e₂' b

/--
error: Application type mismatch: The argument
  b
has type
  B
of sort `Type u_1` but is expected to have type
  ?_ ∈ e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet)
of sort `Prop` in the application
  Pretrivialization.continuousAlternatingMapCoordChange 𝕜 (Fin 2) e₁ e₁' e₂ e₂' b
-/
#guard_msgs in
example (b : B) : (F₁ [⋀^Fin 2]→L[𝕜] F₂) →L[𝕜] F₁ [⋀^Fin 2]→L[𝕜] F₂ :=
  Pretrivialization.continuousAlternatingMapCoordChange 𝕜 (Fin 2) e₁ e₁' e₂ e₂' b

/-! The overlap of the two pretrivializations' base sets does not stand in for the four-fold one
in either order. -/

/--
error: Application type mismatch: The argument
  hb
has type
  b ∈ e₁.baseSet ∩ e₂.baseSet
but is expected to have type
  ?_ ∈ e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet)
in the application
  Pretrivialization.continuousLinearMapCoordChange (RingHom.id 𝕜) e₁ e₁' e₂ e₂' hb
-/
#guard_msgs in
example {b : B} (hb : b ∈ e₁.baseSet ∩ e₂.baseSet) : (F₁ →L[𝕜] F₂) →L[𝕜] F₁ →L[𝕜] F₂ :=
  Pretrivialization.continuousLinearMapCoordChange (RingHom.id 𝕜) e₁ e₁' e₂ e₂' hb

/--
error: Application type mismatch: The argument
  hb
has type
  b ∈ e₁'.baseSet ∩ e₂'.baseSet ∩ (e₁.baseSet ∩ e₂.baseSet)
but is expected to have type
  ?_ ∈ e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet)
in the application
  Pretrivialization.continuousAlternatingMapCoordChange 𝕜 (Fin 2) e₁ e₁' e₂ e₂' hb
-/
#guard_msgs in
example {b : B} (hb : b ∈ e₁'.baseSet ∩ e₂'.baseSet ∩ (e₁.baseSet ∩ e₂.baseSet)) :
    (F₁ [⋀^Fin 2]→L[𝕜] F₂) →L[𝕜] F₁ [⋀^Fin 2]→L[𝕜] F₂ :=
  Pretrivialization.continuousAlternatingMapCoordChange 𝕜 (Fin 2) e₁ e₁' e₂ e₂' hb

end Hom

/-! Smoothness is likewise a statement about every map that agrees with the coordinate change on
the overlap. -/

section Smooth

open scoped Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {EB : Type*} [NormedAddCommGroup EB]
  [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB}
  [ChartedSpace HB B] {E : B → Type*} [∀ b, AddCommMonoid (E b)] [∀ b, Module 𝕜 (E b)]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] [TopologicalSpace (TotalSpace F' E)]
  [∀ b, TopologicalSpace (E b)] [FiberBundle F' E] [VectorBundle 𝕜 F' E] {n : WithTop ℕ∞}
  [ContMDiffVectorBundle n F' E IB]

example (e e' : Trivialization F' (π F' E)) [MemTrivializationAtlas e]
    [MemTrivializationAtlas e'] {φ : B → F' →L[𝕜] F'}
    (hφ : ∀ b (hb : b ∈ e.baseSet ∩ e'.baseSet), φ b = e.coordChangeL 𝕜 e' hb) :
    ContMDiffOn IB 𝓘(𝕜, F' →L[𝕜] F') n φ (e.baseSet ∩ e'.baseSet) :=
  contMDiffOn_coordChangeL e e' hφ

/-! Along a map into both base sets, the coordinate change itself is smooth. -/

example {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] {HM : Type*}
    [TopologicalSpace HM] {IM : ModelWithCorners 𝕜 EM HM} {M : Type*} [TopologicalSpace M]
    [ChartedSpace HM M] (e e' : Trivialization F' (π F' E)) [MemTrivializationAtlas e]
    [MemTrivializationAtlas e'] {f : M → B} (hf : ContMDiff IM IB n f)
    (he : ∀ x, f x ∈ e.baseSet) (he' : ∀ x, f x ∈ e'.baseSet) :
    ContMDiff IM 𝓘(𝕜, F' →L[𝕜] F') n
      (fun y ↦ (e.coordChangeL 𝕜 e' (Set.mem_inter (he y) (he' y)) : F' →L[𝕜] F')) :=
  hf.coordChangeL he he'

end Smooth

/-! The removed fields, the renamed continuity theorem, and the chosen representatives -/

/-- info: Unknown constant `VectorBundle.continuousOn_coordChange'` -/
#guard_msgs in
#check_failure VectorBundle.continuousOn_coordChange'

/-- info: Unknown constant `ContMDiffVectorBundle.contMDiffOn_coordChangeL` -/
#guard_msgs in
#check_failure ContMDiffVectorBundle.contMDiffOn_coordChangeL

/-- info: Unknown identifier `continuousOn_coordChange` -/
#guard_msgs in
#check_failure continuousOn_coordChange

/-- info: Unknown constant `VectorPrebundle.coordChange` -/
#guard_msgs in
#check_failure VectorPrebundle.coordChange

/-- info: Unknown constant `VectorPrebundle.continuousOn_coordChange` -/
#guard_msgs in
#check_failure VectorPrebundle.continuousOn_coordChange

/-- info: Unknown constant `VectorPrebundle.coordChange_apply` -/
#guard_msgs in
#check_failure VectorPrebundle.coordChange_apply

/-- info: Unknown constant `VectorPrebundle.mk_coordChange` -/
#guard_msgs in
#check_failure VectorPrebundle.mk_coordChange

/-- info: Unknown constant `VectorPrebundle.contMDiffCoordChange` -/
#guard_msgs in
#check_failure VectorPrebundle.contMDiffCoordChange

/-- info: Unknown constant `VectorPrebundle.contMDiffOn_contMDiffCoordChange` -/
#guard_msgs in
#check_failure VectorPrebundle.contMDiffOn_contMDiffCoordChange

/-- info: Unknown constant `VectorPrebundle.contMDiffCoordChange_apply` -/
#guard_msgs in
#check_failure VectorPrebundle.contMDiffCoordChange_apply

/-- info: Unknown constant `VectorPrebundle.mk_contMDiffCoordChange` -/
#guard_msgs in
#check_failure VectorPrebundle.mk_contMDiffCoordChange
