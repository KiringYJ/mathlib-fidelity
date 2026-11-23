import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# Strict adjoints of partially defined operators

These tests ensure that the adjoint of a partially defined operator is defined exactly for densely
defined operators, that no `Star` instance takes the adjoint of every operator, and that an
operator whose domain is not dense has many formal adjoints, so no canonical adjoint exists.
-/

open LinearPMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- info: Unknown constant `LinearPMap.adjoint_apply_of_not_dense` -/
#guard_msgs in
#check_failure LinearPMap.adjoint_apply_of_not_dense

/-- info: Unknown constant `LinearPMap.instStar` -/
#guard_msgs in
#check_failure LinearPMap.instStar

/-- info: Unknown constant `LinearPMap.isSelfAdjoint_def` -/
#guard_msgs in
#check_failure LinearPMap.isSelfAdjoint_def

/-- info: Unknown constant `LinearPMap.mem_adjoint_domain_iff` -/
#guard_msgs in
#check_failure LinearPMap.mem_adjoint_domain_iff

/-- info: Unknown constant `LinearPMap.mem_adjoint_domain_of_exists` -/
#guard_msgs in
#check_failure LinearPMap.mem_adjoint_domain_of_exists

/-- info: Unknown constant `IsSelfAdjoint.dense_domain` -/
#guard_msgs in
#check_failure _root_.IsSelfAdjoint.dense_domain

/-- info: Unknown constant `IsSelfAdjoint.isClosed` -/
#guard_msgs in
#check_failure _root_.IsSelfAdjoint.isClosed

/-! The adjoint needs a dense domain. -/

/-- error: Tactic `assumption` failed -/
#guard_msgs (substring := true) in
noncomputable example (T : E →ₗ.[𝕜] F) : F →ₗ.[𝕜] E := T†

noncomputable example (T : E →ₗ.[𝕜] F) (hT : Dense (T.domain : Set E)) : F →ₗ.[𝕜] E := T†

example (T : E →ₗ.[𝕜] F) (hT : Dense (T.domain : Set E)) : T†.IsFormalAdjoint T :=
  adjoint_isFormalAdjoint hT

example (T : E →ₗ.[𝕜] F) (hT : Dense (T.domain : Set E)) : T†.domain = T.adjointDomain := by
  simp

/-! There is no `Star` structure that takes the adjoint of every operator. -/

/-- error: failed to synthesize instance of type class
  Star (E →ₗ.[𝕜] E)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command. -/
#guard_msgs in
noncomputable example (A : E →ₗ.[𝕜] E) : E →ₗ.[𝕜] E := star A

/-! The notation `T†` is also used to print the adjoint. -/

/-- info: fun T hT => T† : (T : E →ₗ.[𝕜] F) → Dense ↑T.domain → F →ₗ.[𝕜] E -/
#guard_msgs in
#check fun (T : E →ₗ.[𝕜] F) (hT : Dense (T.domain : Set E)) ↦ T†

/-! The identity is self-adjoint, and self-adjoint operators are densely defined by
definition. -/

example : ((ContinuousLinearMap.id 𝕜 E).toPMap ⊤).IsSelfAdjoint := by
  have hp : Dense ((⊤ : Submodule 𝕜 E) : Set E) := by simp
  refine ⟨hp, ?_⟩
  rw [ContinuousLinearMap.toPMap_adjoint_eq_adjoint_toPMap_of_dense _ hp,
    ContinuousLinearMap.adjoint_id]

example (A : E →ₗ.[𝕜] E) (hA : A.IsSelfAdjoint) : Dense (A.domain : Set E) :=
  hA.dense_domain

example (A : E →ₗ.[𝕜] E) (hA : A.IsSelfAdjoint) : A.IsClosed :=
  hA.isClosed

/-! An operator defined only at zero on `𝕜` has every operator on `𝕜` as a formal adjoint, so its
adjoint would not be determined. -/

/-- The zero operator on the zero subspace of `𝕜`. -/
private noncomputable def atZero : 𝕜 →ₗ.[𝕜] 𝕜 := ⟨⊥, 0⟩

example : (atZero : 𝕜 →ₗ.[𝕜] 𝕜).IsFormalAdjoint (LinearMap.id.toPMap ⊤) ∧
    (atZero : 𝕜 →ₗ.[𝕜] 𝕜).IsFormalAdjoint (LinearMap.toPMap 0 ⊤) := by
  refine ⟨fun x y ↦ ?_, fun x y ↦ ?_⟩ <;>
  · obtain ⟨x, hx⟩ := x
    obtain rfl := (Submodule.mem_bot 𝕜).1 hx
    simp [atZero]
