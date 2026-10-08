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
the extension of a map that is not uniformly continuous, a constant, is removed.  The negation,
addition, subtraction, and multiplication of a completion exist exactly for Cauchy continuous
operations, in particular for a uniform additive group and a topological ring, possibly
non-unital, with a uniform additive group; the scalar action exists for a uniformly continuous
action, the norm for a seminormed group, and the inverse for a completable field whose inversion is
continuous away from zero.
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

/-! The operations exist for Cauchy continuous operations, also outside groups, and they are the
continuous extensions of the operations of `α`. -/

noncomputable example {α : Type*} [UniformSpace α] [Add α] [CauchyContinuousAdd α]
    (x y : Completion α) : Completion α :=
  x + y

example {α : Type*} [UniformSpace α] [Add α] [CauchyContinuousAdd α] (a b : α) :
    ((a + b : α) : Completion α) = a + b :=
  Completion.coe_add a b

example {α : Type*} [UniformSpace α] [Add α] [CauchyContinuousAdd α] :
    Continuous fun p : Completion α × Completion α ↦ p.1 + p.2 :=
  continuous_add

example {α : Type*} [UniformSpace α] [Neg α] [CauchyContinuousNeg α] (a : α) :
    ((-a : α) : Completion α) = -a :=
  Completion.coe_neg a

example {α : Type*} [UniformSpace α] [Neg α] [CauchyContinuousNeg α] :
    Continuous fun x : Completion α ↦ -x :=
  continuous_neg

example {α : Type*} [UniformSpace α] [Sub α] [CauchyContinuousSub α] (a b : α) :
    ((a - b : α) : Completion α) = a - b :=
  Completion.coe_sub a b

example {α : Type*} [UniformSpace α] [Sub α] [CauchyContinuousSub α] :
    Continuous fun p : Completion α × Completion α ↦ p.1 - p.2 :=
  continuous_sub

/-! The operations of a uniform group are Cauchy continuous. -/

example {G : Type*} [UniformSpace G] [Group G] [IsUniformGroup G] : CauchyContinuousMul G :=
  inferInstance

example {G : Type*} [UniformSpace G] [Group G] [IsUniformGroup G] : CauchyContinuousInv G :=
  inferInstance

example {G : Type*} [UniformSpace G] [Group G] [IsUniformGroup G] : CauchyContinuousDiv G :=
  inferInstance

example {G : Type*} [UniformSpace G] [AddGroup G] [IsUniformAddGroup G] : CauchyContinuousAdd G :=
  inferInstance

example {G : Type*} [UniformSpace G] [AddGroup G] [IsUniformAddGroup G] : CauchyContinuousNeg G :=
  inferInstance

example {G : Type*} [UniformSpace G] [AddGroup G] [IsUniformAddGroup G] : CauchyContinuousSub G :=
  inferInstance

/-! The completion of a multiplicative uniform group has a multiplication. -/

noncomputable example {G : Type*} [UniformSpace G] [Group G] [IsUniformGroup G]
    (x y : Completion G) : Completion G :=
  x * y

/-! A Cauchy continuous operation is continuous, and on a complete space a continuous operation is
Cauchy continuous. -/

example {M : Type*} [UniformSpace M] [Mul M] [CauchyContinuousMul M] : ContinuousMul M :=
  CauchyContinuousMul.continuousMul

example {M : Type*} [UniformSpace M] [Neg M] [CauchyContinuousNeg M] : ContinuousNeg M :=
  CauchyContinuousNeg.continuousNeg

example {M : Type*} [UniformSpace M] [Div M] [CauchyContinuousDiv M] : ContinuousDiv M :=
  CauchyContinuousDiv.continuousDiv

example {M : Type*} [UniformSpace M] [Add M] [ContinuousAdd M] [CompleteSpace M] :
    CauchyContinuousAdd M :=
  CauchyContinuousAdd.of_continuousAdd

example {M : Type*} [UniformSpace M] [Inv M] [ContinuousInv M] [CompleteSpace M] :
    CauchyContinuousInv M :=
  CauchyContinuousInv.of_continuousInv

example {M : Type*} [UniformSpace M] [Sub M] [ContinuousSub M] [CompleteSpace M] :
    CauchyContinuousSub M :=
  CauchyContinuousSub.of_continuousSub

/-! A uniformly continuous map is Cauchy continuous, and a Cauchy continuous map is continuous.
Cauchy continuity is preserved by composition, and composing with a uniform inducing map neither
creates nor destroys it. -/

example {α β : Type*} [UniformSpace α] [UniformSpace β] {f : α → β} (hf : UniformContinuous f) :
    Continuous f :=
  hf.cauchyContinuous.continuous

example {α β γ : Type*} [UniformSpace α] [UniformSpace β] [UniformSpace γ] {f : α → β}
    {g : β → γ} (hg : CauchyContinuous g) (hf : CauchyContinuous f) : CauchyContinuous (g ∘ f) :=
  hg.comp hf

example {α β γ : Type*} [UniformSpace α] [UniformSpace β] [UniformSpace γ] {g : β → γ}
    (hg : IsUniformInducing g) {f : α → β} : CauchyContinuous f ↔ CauchyContinuous (g ∘ f) :=
  hg.cauchyContinuous_iff

/-! Along a dense uniform inducing map, a Cauchy continuous map into a complete separated space
extends continuously. -/

example {α β γ : Type*} [UniformSpace α] [UniformSpace β] [UniformSpace γ] [CompleteSpace γ]
    [T0Space γ] {e : α → β} {f : α → γ} (hf : CauchyContinuous f) (he : IsUniformInducing e)
    (hd : DenseRange e) : Continuous ((he.isDenseInducing hd).extend f) :=
  hf.continuous_extend he hd

example {α β γ : Type*} [UniformSpace α] [UniformSpace β] [UniformSpace γ] [CompleteSpace γ]
    [T0Space γ] {e : α → β} {f : α → γ} (hf : CauchyContinuous f) (he : IsUniformInducing e)
    (hd : DenseRange e) (a : α) : (he.isDenseInducing hd).extend f (e a) = f a :=
  hf.extend_eq he hd a

/-! Conversely, a continuous map after a Cauchy continuous map into a complete space is Cauchy
continuous, so for the completion, Cauchy continuity is equivalent to the existence of a continuous
extension. -/

example {α β γ : Type*} [UniformSpace α] [UniformSpace β] [UniformSpace γ] [CompleteSpace β]
    {e : α → β} {g : β → γ} (hg : Continuous g) (he : CauchyContinuous e) :
    CauchyContinuous (g ∘ e) :=
  hg.cauchyContinuous_comp he

example {α γ : Type*} [UniformSpace α] [UniformSpace γ] [CompleteSpace γ] [T0Space γ]
    {f : α → γ} :
    CauchyContinuous f ↔ ∃ g : Completion α → γ, Continuous g ∧ ∀ a : α, g a = f a :=
  Completion.cauchyContinuous_iff_exists_continuous_extension

/-! Without Cauchy continuous operations, the completion has no addition, negation, or
subtraction. -/

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

/-! The multiplication exists for a Cauchy continuous multiplication, in particular for a
topological ring with a uniform additive group, whose multiplication need not be uniformly
continuous, as on `ℝ`; without these hypotheses, the completion has no multiplication. -/

example {α : Type*} [UniformSpace α] [Mul α] [CauchyContinuousMul α] (a b : α) :
    ((a * b : α) : Completion α) = a * b :=
  Completion.coe_mul a b

example {α : Type*} [UniformSpace α] [Mul α] [CauchyContinuousMul α] :
    Continuous fun p : Completion α × Completion α ↦ p.1 * p.2 :=
  continuous_mul

example : CauchyContinuousMul ℝ := inferInstance

/-! Multiplication on `ℝ` is not uniformly continuous: points of `ℝ × ℝ` at distance `δ / 2` near
`(2 / δ, 2 / δ)` have products at distance `1`. -/

example : ¬ UniformContinuous fun p : ℝ × ℝ ↦ p.1 * p.2 := by
  intro h
  obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuous_iff.1 h 1 one_pos
  have hdist : dist ((2 / δ, 2 / δ) : ℝ × ℝ) (2 / δ + δ / 2, 2 / δ) < δ := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    have h1 : 2 / δ - (2 / δ + δ / 2) = -(δ / 2) := by ring
    rw [h1, sub_self, abs_neg, abs_zero, abs_of_pos (show (0 : ℝ) < δ / 2 by positivity)]
    exact max_lt (by linarith) hδ
  have key : dist ((2 / δ) * (2 / δ)) ((2 / δ + δ / 2) * (2 / δ)) < 1 := hd hdist
  have h2 : (2 / δ) * (2 / δ) - (2 / δ + δ / 2) * (2 / δ) = -1 := by
    field_simp
    ring
  rw [Real.dist_eq, h2] at key
  norm_num at key

/-! A non-unital topological ring with a uniform additive group has a Cauchy continuous
multiplication. -/

example {α : Type*} [NonUnitalNonAssocRing α] [UniformSpace α] [IsTopologicalRing α]
    [IsUniformAddGroup α] : CauchyContinuousMul α :=
  inferInstance

noncomputable example {α : Type*} [NonUnitalNonAssocRing α] [UniformSpace α] [IsTopologicalRing α]
    [IsUniformAddGroup α] (x y : Completion α) : Completion α :=
  x * y

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
