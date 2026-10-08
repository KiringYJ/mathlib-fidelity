import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Group.Completion
import Mathlib.Topology.Algebra.UniformField
import Mathlib.Topology.Algebra.UniformRing

/-!
# The completion extension and the operations on a completion take their domains

`UniformSpace.Completion.extension f hf` extends a map `f : α → β` to the completion of `α`,
where `hf` proves that `f` is uniformly continuous and `β` is complete and separated: completeness
supplies the limits that define the extension, and separation makes it the unique uniformly
continuous map that agrees with `f` on `α`.  `UniformSpace.Completion.map f hf` lifts a uniformly
continuous map to the completions; `fun_prop` supplies `hf` for routine maps.  The former value of
the extension of a map that is not uniformly continuous, a constant, is removed, and the operations
on a completion exist for a uniform additive group, a uniformly continuous scalar action, and a
seminormed group; the multiplication exists for a topological ring with a uniform additive group,
and the inverse for a completable field whose inversion is continuous away from zero.
-/

open UniformSpace

/-! The removed names -/

/-- info: Unknown constant `UniformSpace.Completion.inseparable_extension_coe` -/
#guard_msgs in
#check_failure UniformSpace.Completion.inseparable_extension_coe

/-- info: Unknown constant `AbstractCompletion.inseparable_extend_coe` -/
#guard_msgs in
#check_failure AbstractCompletion.inseparable_extend_coe

/-! The full name `AbstractCompletion.extend_def` would elaborate as `Function.extend_def`
applied to `AbstractCompletion`, so the removed lemma is looked up inside its namespace. -/

/-- info: Unknown identifier `extend_def` -/
#guard_msgs in
open AbstractCompletion in
#check_failure extend_def

/-! The extension of inversion to the completion of a field and its lemmas are private. -/

/-- info: Unknown constant `UniformSpace.Completion.hatInv` -/
#guard_msgs in
#check_failure UniformSpace.Completion.hatInv

/-- info: Unknown constant `UniformSpace.Completion.continuous_hatInv` -/
#guard_msgs in
#check_failure UniformSpace.Completion.continuous_hatInv

/-- info: Unknown constant `UniformSpace.Completion.hatInv_extends` -/
#guard_msgs in
#check_failure UniformSpace.Completion.hatInv_extends

/-- info: Unknown constant `UniformSpace.Completion.mul_hatInv_cancel` -/
#guard_msgs in
#check_failure UniformSpace.Completion.mul_hatInv_cancel

/-! The extension needs a proof of uniform continuity; `fun_prop` fails for an arbitrary map. -/

/--
error: could not synthesize default value for parameter 'hf' using tactics
---
error: `fun_prop` was unable to prove `UniformContinuous f`

Issues:
  No theorems found for `f` in order to prove `UniformContinuous fun a => f a`
-/
#guard_msgs in
noncomputable example {α β : Type*} [UniformSpace α] [UniformSpace β] [CompleteSpace β]
    [T0Space β] (f : α → β) : Completion α → β :=
  Completion.extension f

/-! The target must be complete and separated. -/

/--
error: failed to synthesize instance of type class
  CompleteSpace β

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
noncomputable example {α β : Type*} [UniformSpace α] [UniformSpace β] [T0Space β] (f : α → β)
    (hf : UniformContinuous f) : Completion α → β :=
  Completion.extension f hf

/--
error: failed to synthesize instance of type class
  T0Space β

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
noncomputable example {α β : Type*} [UniformSpace α] [UniformSpace β] [CompleteSpace β]
    (f : α → β) (hf : UniformContinuous f) : Completion α → β :=
  Completion.extension f hf

/-! The extension agrees with the function on `α`, and it is the unique uniformly continuous such
map. -/

example {α β : Type*} [UniformSpace α] [UniformSpace β] [CompleteSpace β] [T0Space β]
    {f : α → β} (hf : UniformContinuous f) (a : α) : Completion.extension f hf a = f a :=
  Completion.extension_coe hf a

example {α β : Type*} [UniformSpace α] [UniformSpace β] [CompleteSpace β] [T0Space β]
    {f : α → β} (hf : UniformContinuous f) {g : Completion α → β} (hg : UniformContinuous g)
    (h : ∀ a : α, f a = g a) : Completion.extension f hf = g :=
  Completion.extension_unique hf hg h

/-! The lift to the completions needs uniform continuity and depends only on the function. -/

example {α β : Type*} [UniformSpace α] [UniformSpace β] {f : α → β} (hf : UniformContinuous f)
    (a : α) : Completion.map f hf a = f a :=
  Completion.map_coe hf a

example {α β : Type*} [UniformSpace α] [UniformSpace β] {f g : α → β} (h : f = g)
    (hf : UniformContinuous f) (hg : UniformContinuous g) :
    Completion.map f hf = Completion.map g hg :=
  Completion.map_congr h

/-! `fun_prop` supplies the uniform continuity of routine maps, and fails for an arbitrary one. -/

noncomputable example {α : Type*} [UniformSpace α] [AddGroup α] [IsUniformAddGroup α] :
    Completion α → Completion α :=
  Completion.map (fun a : α ↦ -a)

/--
error: could not synthesize default value for parameter 'hf' using tactics
---
error: `fun_prop` was unable to prove `UniformContinuous f`

Issues:
  No theorems found for `f` in order to prove `UniformContinuous fun a => f a`
-/
#guard_msgs in
noncomputable example {α β : Type*} [UniformSpace α] [UniformSpace β] (f : α → β) :
    Completion α → Completion β :=
  Completion.map f

/-! The completion of a uniform additive group carries the extended operations. -/

example {α : Type*} [UniformSpace α] [AddCommGroup α] [IsUniformAddGroup α] (a b : α) :
    ((a + b : α) : Completion α) = a + b :=
  Completion.coe_add a b

/-! Without a uniform group structure, the completion has no addition. -/

/--
error: failed to synthesize instance of type class
  HAdd (Completion α) (Completion α) ?_

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example {α : Type*} [UniformSpace α] [Add α] (x y : Completion α) : Completion α := x + y

/--
error: failed to synthesize instance of type class
  Neg (Completion α)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example {α : Type*} [UniformSpace α] [Neg α] (x : Completion α) : Completion α := -x

/--
error: failed to synthesize instance of type class
  HSub (Completion α) (Completion α) ?_

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example {α : Type*} [UniformSpace α] [Sub α] (x y : Completion α) : Completion α := x - y

/-! Without a uniformly continuous action, the completion has no scalar action. -/

/--
error: failed to synthesize instance of type class
  HSMul M (Completion X) ?_

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example {M X : Type*} [UniformSpace X] [SMul M X] (c : M) (x : Completion X) : Completion X :=
  c • x

/-! The completion of a seminormed group carries the extended norm. -/

example {E : Type*} [SeminormedAddGroup E] (x : E) : ‖(x : Completion E)‖ = ‖x‖ :=
  Completion.norm_coe x

/-! Without a seminormed group, the completion has no norm. -/

/--
error: failed to synthesize instance of type class
  Norm (Completion E)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example {E : Type*} [UniformSpace E] [Norm E] (x : Completion E) : ℝ := ‖x‖

/-! The completion of a topological ring with a uniform additive group carries the extended
multiplication; without them, the completion has no multiplication. -/

example {α : Type*} [Ring α] [UniformSpace α] [IsTopologicalRing α] [IsUniformAddGroup α]
    (a b : α) : ((a * b : α) : Completion α) = a * b :=
  Completion.coe_mul a b

/--
error: failed to synthesize instance of type class
  HMul (Completion α) (Completion α) ?_

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example {α : Type*} [Ring α] [UniformSpace α] (x y : Completion α) : Completion α := x * y

/-! Each of the two hypotheses is needed. -/

/--
error: failed to synthesize instance of type class
  HMul (Completion α) (Completion α) ?_

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example {α : Type*} [Ring α] [UniformSpace α] [IsTopologicalRing α] (x y : Completion α) :
    Completion α :=
  x * y

/--
error: failed to synthesize instance of type class
  HMul (Completion α) (Completion α) ?_

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example {α : Type*} [Ring α] [UniformSpace α] [IsUniformAddGroup α] (x y : Completion α) :
    Completion α :=
  x * y

/-! A seminormed ring is a routine sufficient condition. -/

noncomputable example {A : Type*} [SeminormedRing A] (x y : Completion A) : Completion A := x * y

/-! The completion of a completable field whose inversion is continuous away from zero carries the
extended inverse; without these hypotheses, the completion has no inverse. -/

example {K : Type*} [Field K] [UniformSpace K] [ContinuousInv₀ K] [CompletableTopField K]
    (x : K) : (x : Completion K)⁻¹ = ((x⁻¹ : K) : Completion K) :=
  Completion.coe_inv x

example {K : Type*} [Field K] [UniformSpace K] [ContinuousInv₀ K] [CompletableTopField K]
    {x : Completion K} (hx : x ≠ 0) : ContinuousAt (fun y : Completion K ↦ y⁻¹) x :=
  continuousAt_inv₀ hx

/--
error: failed to synthesize instance of type class
  Inv (Completion K)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example {K : Type*} [Field K] [UniformSpace K] (x : Completion K) : Completion K := x⁻¹

/-! Each of the two hypotheses is needed. -/

/--
error: failed to synthesize instance of type class
  Inv (Completion K)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example {K : Type*} [Field K] [UniformSpace K] [IsTopologicalDivisionRing K] (x : Completion K) :
    Completion K :=
  x⁻¹

/--
error: failed to synthesize instance of type class
  Inv (Completion K)

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example {K : Type*} [Field K] [UniformSpace K] [CompletableTopField K] (x : Completion K) :
    Completion K :=
  x⁻¹

/-! A normed field is a routine sufficient condition. -/

noncomputable example {K : Type*} [NormedField K] (x : Completion K) : Completion K := x⁻¹
