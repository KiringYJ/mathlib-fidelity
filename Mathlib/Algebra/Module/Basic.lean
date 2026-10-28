/-
Copyright (c) 2015 Nathaniel Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.GroupWithZero.Action.Units
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Algebra.Ring.Invertible

/-!
# Further basic results about modules.

-/

public section

assert_not_exists Nonneg.inv Multiset

open Function Set

universe u v

variable {α R M M₂ : Type*}

@[simp]
theorem Units.neg_smul [Ring R] [AddCommGroup M] [Module R M] (u : Rˣ) (x : M) :
    -u • x = -(u • x) := by
  rw [Units.smul_def, Units.val_neg, _root_.neg_smul, Units.smul_def]

@[simp]
theorem invOf_two_smul_add_invOf_two_smul (R) [Semiring R] [AddCommMonoid M] [Module R M]
    [Invertible (2 : R)] (x : M) :
    (⅟2 : R) • x + (⅟2 : R) • x = x :=
  Convex.combo_self invOf_two_add_invOf_two _

theorem map_inv_natCast_smul [AddCommMonoid M] [AddCommMonoid M₂] {F : Type*} [FunLike F M M₂]
    [AddMonoidHomClass F M M₂] (f : F) (R S : Type*)
    [Semiring R] [Semiring S] [Module R M] [Module S M₂] (n : ℕ)
    {hR : IsUnit (n : R)} {hS : IsUnit (n : S)} (x : M) :
    f ((n : R)⁻¹ • x) = (n : S)⁻¹ • f x := by
  change f (hR.unit⁻¹ • x) = hS.unit⁻¹ • f x
  apply MulAction.injective hS.unit
  calc
    hS.unit • f (hR.unit⁻¹ • x) = (n : S) • f (hR.unit⁻¹ • x) := rfl
    _ = f ((n : R) • hR.unit⁻¹ • x) := (map_natCast_smul f R S n _).symm
    _ = f x := congrArg f (smul_inv_smul hR.unit x)
    _ = hS.unit • hS.unit⁻¹ • f x := (smul_inv_smul hS.unit (f x)).symm

theorem map_inv_intCast_smul [AddCommGroup M] [AddCommGroup M₂] {F : Type*} [FunLike F M M₂]
    [AddMonoidHomClass F M M₂] (f : F) (R S : Type*) [Ring R] [Ring S] [Module R M]
    [Module S M₂] (z : ℤ) {hR : IsUnit (z : R)} {hS : IsUnit (z : S)} (x : M) :
    f ((z : R)⁻¹ • x) = (z : S)⁻¹ • f x := by
  change f (hR.unit⁻¹ • x) = hS.unit⁻¹ • f x
  apply MulAction.injective hS.unit
  calc
    hS.unit • f (hR.unit⁻¹ • x) = (z : S) • f (hR.unit⁻¹ • x) := rfl
    _ = f ((z : R) • hR.unit⁻¹ • x) := (map_intCast_smul f R S z _).symm
    _ = f x := congrArg f (smul_inv_smul hR.unit x)
    _ = hS.unit • hS.unit⁻¹ • f x := (smul_inv_smul hS.unit (f x)).symm

/-- Scalar multiplications agree on inverses of natural numbers that are units in both semirings. -/
theorem inv_natCast_smul_eq {E : Type*} (R S : Type*) [AddCommMonoid E] [Semiring R]
    [Semiring S] [Module R E] [Module S E] (n : ℕ)
    {hR : IsUnit (n : R)} {hS : IsUnit (n : S)} (x : E) :
    (n : R)⁻¹ • x = (n : S)⁻¹ • x :=
  map_inv_natCast_smul (AddMonoidHom.id E) R S n x

/-- Scalar multiplications agree on inverses of integers that are units in both rings. -/
theorem inv_intCast_smul_eq {E : Type*} (R S : Type*) [AddCommGroup E] [Ring R]
    [Ring S] [Module R E] [Module S E] (n : ℤ)
    {hR : IsUnit (n : R)} {hS : IsUnit (n : S)} (x : E) :
    (n : R)⁻¹ • x = (n : S)⁻¹ • x :=
  map_inv_intCast_smul (AddMonoidHom.id E) R S n x

/-- A distributive action commutes with the inverse action of an invertible natural scalar. -/
theorem inv_natCast_smul_comm {α E : Type*} (R : Type*) [AddCommMonoid E] [Semiring R]
    [Module R E] [DistribSMul α E] (n : ℕ) {hn : IsUnit (n : R)} (s : α) (x : E) :
    (n : R)⁻¹ • s • x = s • (n : R)⁻¹ • x :=
  (map_inv_natCast_smul (DistribSMul.toAddMonoidHom E s) R R n x).symm

/-- A distributive action commutes with the inverse action of an invertible integer scalar. -/
theorem inv_intCast_smul_comm {α E : Type*} (R : Type*) [AddCommGroup E] [Ring R]
    [Module R E] [DistribSMul α E] (n : ℤ) {hn : IsUnit (n : R)} (s : α) (x : E) :
    (n : R)⁻¹ • s • x = s • (n : R)⁻¹ • x :=
  (map_inv_intCast_smul (DistribSMul.toAddMonoidHom E s) R R n x).symm

namespace Function

lemma support_smul_subset_left [Zero R] [Zero M] [SMulWithZero R M] (f : α → R) (g : α → M) :
    support (f • g) ⊆ support f := fun x hfg hf ↦
  hfg <| by rw [Pi.smul_apply', hf, zero_smul]

-- Changed (2024-01-21): this lemma was generalised;
-- the old version is now called `support_const_smul_subset`.
lemma support_smul_subset_right [Zero M] [SMulZeroClass R M] (f : α → R) (g : α → M) :
    support (f • g) ⊆ support g :=
  fun x hbf hf ↦ hbf <| by rw [Pi.smul_apply', hf, smul_zero]

lemma support_const_smul_of_ne_zero [Semiring R] [IsDomain R] [AddCommMonoid M] [Module R M]
    [Module.IsTorsionFree R M] (c : R) (g : α → M) (hc : c ≠ 0) : support (c • g) = support g :=
  ext fun _ ↦ smul_ne_zero_iff_right hc

lemma support_smul [Semiring R] [IsDomain R] [AddCommMonoid M] [Module R M]
    [Module.IsTorsionFree R M] (f : α → R) (g : α → M) : support (f • g) = support f ∩ support g :=
  ext fun _ => smul_ne_zero_iff

lemma support_const_smul_subset [Zero M] [SMulZeroClass R M] (a : R) (f : α → M) :
    support (a • f) ⊆ support f := support_smul_subset_right (fun _ ↦ a) f

end Function

namespace Set
section SMulZeroClass
variable [Zero M] [SMulZeroClass R M]

lemma indicator_smul_apply (s : Set α) (r : α → R) (f : α → M) (a : α) :
    indicator s (fun a ↦ r a • f a) a = r a • indicator s f a := by
  dsimp only [indicator]
  split_ifs
  exacts [rfl, (smul_zero (r a)).symm]

lemma indicator_smul (s : Set α) (r : α → R) (f : α → M) :
    indicator s (fun a ↦ r a • f a) = fun a ↦ r a • indicator s f a :=
  funext <| indicator_smul_apply s r f

lemma indicator_const_smul_apply (s : Set α) (r : R) (f : α → M) (a : α) :
    indicator s (r • f ·) a = r • indicator s f a :=
  indicator_smul_apply s (fun _ ↦ r) f a

lemma indicator_const_smul (s : Set α) (r : R) (f : α → M) :
    indicator s (r • f ·) = (r • indicator s f ·) :=
  funext <| indicator_const_smul_apply s r f

end SMulZeroClass

section SMulWithZero
variable [Zero R] [Zero M] [SMulWithZero R M]

lemma indicator_smul_apply_left (s : Set α) (r : α → R) (f : α → M) (a : α) :
    indicator s (fun a ↦ r a • f a) a = indicator s r a • f a := by
  dsimp only [indicator]
  split_ifs
  exacts [rfl, (zero_smul _ (f a)).symm]

lemma indicator_smul_left (s : Set α) (r : α → R) (f : α → M) :
    indicator s (fun a ↦ r a • f a) = fun a ↦ indicator s r a • f a :=
  funext <| indicator_smul_apply_left _ _ _

lemma indicator_smul_const_apply (s : Set α) (r : α → R) (m : M) (a : α) :
    indicator s (r · • m) a = indicator s r a • m := indicator_smul_apply_left _ _ _ _

lemma indicator_smul_const (s : Set α) (r : α → R) (m : M) :
    indicator s (r · • m) = (indicator s r · • m) :=
  funext <| indicator_smul_const_apply _ _ _

end SMulWithZero

section MulZeroOneClass

variable [MulZeroOneClass R]

lemma smul_indicator_one_apply (s : Set α) (r : R) (a : α) :
    r • s.indicator (1 : α → R) a = s.indicator (fun _ ↦ r) a := by
  simp_rw [← indicator_const_smul_apply, Pi.one_apply, smul_eq_mul, mul_one]

end MulZeroOneClass
end Set
