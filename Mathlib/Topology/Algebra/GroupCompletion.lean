/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
module

public import Mathlib.Topology.Algebra.CauchyContinuousMul
public import Mathlib.Topology.Algebra.UniformMulAction

/-!
# Completion of topological groups:

This file endows the completion of a topological abelian group with a group structure.
More precisely the instance `UniformSpace.Completion.addGroup` builds an abelian group structure
on the completion of an abelian group endowed with a compatible uniform structure.
Then the instance `UniformSpace.Completion.isUniformAddGroup` proves this group structure is
compatible with the completed uniform structure. The compatibility condition is `IsUniformAddGroup`.

The negation, addition, and subtraction of `UniformSpace.Completion α` are the continuous
extensions of those of `α`; each exists exactly when the operation is Cauchy continuous
(`CauchyContinuousNeg`, `CauchyContinuousAdd`, `CauchyContinuousSub`), which holds in a uniform
additive group.

## Main declarations

Beyond the instances explained above (that don't have to be explicitly invoked),
the main constructions deal with continuous group morphisms.

* `AddMonoidHom.extension`: extends a continuous group morphism from `G`
  to a complete separated group `H` to `Completion G`.
* `AddMonoidHom.completion`: promotes a continuous group morphism
  from `G` to `H` into a continuous group morphism
  from `Completion G` to `Completion H`.
-/

@[expose] public section


noncomputable section

variable {M R α β : Type*}

section Group

open UniformSpace

variable [UniformSpace α]

instance [Zero α] : Zero (Completion α) :=
  ⟨(0 : α)⟩

/-- The negation on the completion: the continuous extension of the negation of `α`
(`UniformSpace.Completion.coe_neg`), which exists exactly when negation is Cauchy continuous. -/
@[nolint unusedArguments]
instance [Neg α] [CauchyContinuousNeg α] : Neg (Completion α) :=
  ⟨Completion.isDenseInducing_coe.extend ((↑) ∘ fun a : α ↦ -a)⟩

/-- The addition on the completion: the continuous extension of the addition of `α`
(`UniformSpace.Completion.coe_add`), which exists exactly when addition is Cauchy continuous. -/
@[nolint unusedArguments]
instance [Add α] [CauchyContinuousAdd α] : Add (Completion α) :=
  ⟨Function.curry <| (Completion.isDenseInducing_coe.prodMap Completion.isDenseInducing_coe).extend
    ((↑) ∘ Function.uncurry fun a b : α ↦ a + b)⟩

/-- The subtraction on the completion: the continuous extension of the subtraction of `α`
(`UniformSpace.Completion.coe_sub`), which exists exactly when subtraction is Cauchy continuous. -/
@[nolint unusedArguments]
instance [Sub α] [CauchyContinuousSub α] : Sub (Completion α) :=
  ⟨Function.curry <| (Completion.isDenseInducing_coe.prodMap Completion.isDenseInducing_coe).extend
    ((↑) ∘ Function.uncurry fun a b : α ↦ a - b)⟩

@[norm_cast]
theorem UniformSpace.Completion.coe_zero [Zero α] : ((0 : α) : Completion α) = 0 :=
  rfl

@[simp] lemma UniformSpace.Completion.coe_eq_zero_iff [Zero α] [T0Space α] {x : α} :
    (x : Completion α) = 0 ↔ x = 0 :=
  Completion.coe_inj

end Group

namespace UniformSpace.Completion

open UniformSpace

section Zero

instance [UniformSpace α] [MonoidWithZero M] [Zero α] [MulActionWithZero M α]
    [UniformContinuousConstSMul M α] : MulActionWithZero M (Completion α) where
  smul_zero := fun r ↦ by rw [← coe_zero, ← coe_smul, MulActionWithZero.smul_zero r]
  zero_smul :=
    ext' (continuous_const_smul _) continuous_const fun a ↦ by
      rw [← coe_smul, zero_smul, coe_zero]

end Zero

section Operations

variable [UniformSpace α]

@[norm_cast]
theorem coe_neg [Neg α] [CauchyContinuousNeg α] (a : α) : ((-a : α) : Completion α) = -a :=
  (((uniformContinuous_coe α).cauchyContinuous.comp cauchyContinuous_neg).extend_eq
    (isUniformInducing_coe α) denseRange_coe a).symm

@[norm_cast]
theorem coe_add [Add α] [CauchyContinuousAdd α] (a b : α) :
    ((a + b : α) : Completion α) = a + b :=
  (((uniformContinuous_coe α).cauchyContinuous.comp cauchyContinuous_add).extend_eq
    ((isUniformInducing_coe α).prod (isUniformInducing_coe α))
    (denseRange_coe.prodMap denseRange_coe) (a, b)).symm

@[norm_cast]
theorem coe_sub [Sub α] [CauchyContinuousSub α] (a b : α) :
    ((a - b : α) : Completion α) = a - b :=
  (((uniformContinuous_coe α).cauchyContinuous.comp cauchyContinuous_sub).extend_eq
    ((isUniformInducing_coe α).prod (isUniformInducing_coe α))
    (denseRange_coe.prodMap denseRange_coe) (a, b)).symm

/-- The negation on the completion is continuous. -/
instance [Neg α] [CauchyContinuousNeg α] : ContinuousNeg (Completion α) where
  continuous_neg := ((uniformContinuous_coe α).cauchyContinuous.comp
    cauchyContinuous_neg).continuous_extend (isUniformInducing_coe α) denseRange_coe

/-- The addition on the completion is continuous. -/
instance [Add α] [CauchyContinuousAdd α] : ContinuousAdd (Completion α) where
  continuous_add := ((uniformContinuous_coe α).cauchyContinuous.comp
    cauchyContinuous_add).continuous_extend ((isUniformInducing_coe α).prod
    (isUniformInducing_coe α)) (denseRange_coe.prodMap denseRange_coe)

/-- The subtraction on the completion is continuous. -/
instance [Sub α] [CauchyContinuousSub α] : ContinuousSub (Completion α) where
  continuous_sub := ((uniformContinuous_coe α).cauchyContinuous.comp
    cauchyContinuous_sub).continuous_extend ((isUniformInducing_coe α).prod
    (isUniformInducing_coe α)) (denseRange_coe.prodMap denseRange_coe)

end Operations

section IsUniformAddGroup

variable [UniformSpace α] [AddGroup α] [IsUniformAddGroup α]

instance : AddMonoid (Completion α) where
  zero_add a :=
    Completion.induction_on a
      (isClosed_eq (continuous_const.add continuous_id) continuous_id) fun a ↦
      show 0 + (a : Completion α) = a by rw [← coe_zero, ← coe_add, zero_add]
  add_zero a :=
    Completion.induction_on a
      (isClosed_eq (continuous_id.add continuous_const) continuous_id) fun a ↦
      show (a : Completion α) + 0 = a by rw [← coe_zero, ← coe_add, add_zero]
  add_assoc := fun a b c ↦
    Completion.induction_on₃ a b c
      (isClosed_eq
        ((continuous_fst.add (continuous_fst.comp continuous_snd)).add
          (continuous_snd.comp continuous_snd))
        (continuous_fst.add
          ((continuous_fst.comp continuous_snd).add (continuous_snd.comp continuous_snd))))
      fun a b c ↦
      show (a : Completion α) + b + c = a + (b + c) by repeat' rw_mod_cast [add_assoc]
  nsmul_zero a :=
    Completion.induction_on a (isClosed_eq (continuous_const_smul _) continuous_const) fun a ↦
      show 0 • (a : Completion α) = 0 by rw [← coe_smul, ← coe_zero, zero_smul]
  nsmul_succ n a :=
    Completion.induction_on a
      (isClosed_eq (continuous_const_smul _) <| (continuous_const_smul _).add continuous_id)
      fun a ↦
      show (n + 1) • (a : Completion α) = n • (a : Completion α) + (a : Completion α) by
        rw [← coe_smul, succ_nsmul, coe_add, coe_smul]

instance : SubNegMonoid (Completion α) where
  sub_eq_add_neg a b :=
    Completion.induction_on₂ a b
      (isClosed_eq (continuous_fst.sub continuous_snd) (continuous_fst.add continuous_snd.neg))
      fun a b ↦ mod_cast congr_arg ((↑) : α → Completion α) (sub_eq_add_neg a b)
  zsmul_zero' a :=
    Completion.induction_on a (isClosed_eq (continuous_const_smul _) continuous_const) fun a ↦
      show (0 : ℤ) • (a : Completion α) = 0 by rw [← coe_smul, ← coe_zero, zero_smul]
  zsmul_succ' n a :=
    Completion.induction_on a
      (isClosed_eq (continuous_const_smul _) <| (continuous_const_smul _).add continuous_id)
      fun a ↦
        show (n.succ : ℤ) • (a : Completion α) = _ by
          rw [← coe_smul, show (n.succ : ℤ) • a = (n : ℤ) • a + a from
            SubNegMonoid.zsmul_succ' n a, coe_add, coe_smul]
  zsmul_neg' n a :=
    Completion.induction_on a
      (isClosed_eq (continuous_const_smul _) <| (continuous_const_smul _).neg) fun a ↦
        show (Int.negSucc n) • (a : Completion α) = _ by
          rw [← coe_smul, show (Int.negSucc n) • a = -((n.succ : ℤ) • a) from
            SubNegMonoid.zsmul_neg' n a, coe_neg, coe_smul]

instance addGroup : AddGroup (Completion α) where
  neg_add_cancel a :=
    Completion.induction_on a
      (isClosed_eq (continuous_neg.add continuous_id) continuous_const)
      fun a ↦
      show -(a : Completion α) + a = 0 by
        rw_mod_cast [neg_add_cancel]
        rfl

instance isUniformAddGroup : IsUniformAddGroup (Completion α) :=
  -- The subtraction of the completion is definitionally `Completion.map₂ Sub.sub _`.
  ⟨uniformContinuous_map₂ uniformContinuous_sub⟩

instance {M} [Monoid M] [DistribMulAction M α] [UniformContinuousConstSMul M α] :
    DistribMulAction M (Completion α) where
  smul_add r x y :=
    induction_on₂ x y
      (isClosed_eq ((continuous_fst.fun_add continuous_snd).fun_const_smul _)
        ((continuous_fst.fun_const_smul _).fun_add (continuous_snd.fun_const_smul _)))
      fun a b ↦ by simp only [← coe_add, ← coe_smul, smul_add]
  smul_zero := fun r ↦ by rw [← coe_zero, ← coe_smul, smul_zero r]

/-- The map from a group to its completion as a group hom. -/
@[simps]
def toCompl : α →+ Completion α where
  toFun := (↑)
  map_add' := coe_add
  map_zero' := coe_zero

theorem continuous_toCompl : Continuous (toCompl : α → Completion α) :=
  continuous_coe α

variable (α) in
theorem isDenseInducing_toCompl : IsDenseInducing (toCompl : α → Completion α) :=
  isDenseInducing_coe

end IsUniformAddGroup

section UniformAddCommGroup

variable [UniformSpace α] [AddCommGroup α] [IsUniformAddGroup α]

instance instAddCommGroup : AddCommGroup (Completion α) :=
  { (inferInstance : AddGroup <| Completion α) with
    add_comm a b :=
      Completion.induction_on₂ a b
        (isClosed_eq (by fun_prop) (by fun_prop))
        fun x y ↦ by
        change (x : Completion α) + ↑y = ↑y + ↑x
        rw [← coe_add, ← coe_add, add_comm] }

instance instModule [Semiring R] [Module R α] [UniformContinuousConstSMul R α] :
    Module R (Completion α) :=
  { (inferInstance : DistribMulAction R <| Completion α),
    (inferInstance : MulActionWithZero R <| Completion α) with
    add_smul := fun a b ↦
      ext' (continuous_const_smul _) ((continuous_const_smul _).add (continuous_const_smul _))
        fun x ↦ by
          rw [← coe_smul, add_smul, coe_add, coe_smul, coe_smul] }

end UniformAddCommGroup

end UniformSpace.Completion

section AddMonoidHom

variable [UniformSpace α] [AddGroup α] [IsUniformAddGroup α] [UniformSpace β] [AddGroup β]
  [IsUniformAddGroup β]

open UniformSpace UniformSpace.Completion

/-- Extension to the completion of a continuous group hom. -/
def AddMonoidHom.extension [CompleteSpace β] [T0Space β] (f : α →+ β) (hf : Continuous f) :
    Completion α →+ β :=
  have hf : UniformContinuous f := uniformContinuous_addMonoidHom_of_continuous hf
  { toFun := Completion.extension f hf
    map_zero' := by rw [← coe_zero, extension_coe hf, f.map_zero]
    map_add' a b :=
      Completion.induction_on₂ a b
        (isClosed_eq (by fun_prop) (by fun_prop))
        fun a b ↦
        show Completion.extension f hf _ =
          Completion.extension f hf _ + Completion.extension f hf _ by
        rw_mod_cast [extension_coe hf, extension_coe hf, extension_coe hf, f.map_add] }

theorem AddMonoidHom.extension_coe [CompleteSpace β] [T0Space β] (f : α →+ β)
    (hf : Continuous f) (a : α) : f.extension hf a = f a :=
  UniformSpace.Completion.extension_coe (uniformContinuous_addMonoidHom_of_continuous hf) a

@[continuity, fun_prop]
theorem AddMonoidHom.continuous_extension [CompleteSpace β] [T0Space β] (f : α →+ β)
    (hf : Continuous f) : Continuous (f.extension hf) :=
  UniformSpace.Completion.continuous_extension (uniformContinuous_addMonoidHom_of_continuous hf)

/-- Completion of a continuous group hom, as a group hom. -/
def AddMonoidHom.completion (f : α →+ β) (hf : Continuous f) : Completion α →+ Completion β :=
  (toCompl.comp f).extension (continuous_toCompl.comp hf)

@[continuity, fun_prop]
theorem AddMonoidHom.continuous_completion (f : α →+ β) (hf : Continuous f) :
    Continuous (AddMonoidHom.completion f hf : Completion α → Completion β) :=
  continuous_map (uniformContinuous_addMonoidHom_of_continuous hf)

@[simp]
theorem AddMonoidHom.completion_coe (f : α →+ β) (hf : Continuous f) (a : α) :
    AddMonoidHom.completion f hf a = f a :=
  map_coe (uniformContinuous_addMonoidHom_of_continuous hf) a

theorem AddMonoidHom.completion_zero :
    AddMonoidHom.completion (0 : α →+ β) continuous_const = 0 := by
  ext x
  refine Completion.induction_on x ?_ ?_
  · apply isClosed_eq (AddMonoidHom.continuous_completion (0 : α →+ β) continuous_const)
    exact continuous_const
  · simp [(0 : α →+ β).completion_coe continuous_const, coe_zero]

theorem AddMonoidHom.completion_add {γ : Type*} [AddCommGroup γ] [UniformSpace γ]
    [IsUniformAddGroup γ] (f g : α →+ γ) (hf : Continuous f) (hg : Continuous g) :
    AddMonoidHom.completion (f + g) (hf.add hg) =
    AddMonoidHom.completion f hf + AddMonoidHom.completion g hg := by
  have hfg := hf.add hg
  ext x
  refine Completion.induction_on x ?_ ?_
  · exact isClosed_eq ((f + g).continuous_completion hfg)
      ((f.continuous_completion hf).add (g.continuous_completion hg))
  · simp [(f + g).completion_coe hfg, coe_add, f.completion_coe hf, g.completion_coe hg]

end AddMonoidHom
