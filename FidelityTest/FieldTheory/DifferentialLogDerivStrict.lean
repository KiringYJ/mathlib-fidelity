/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
import Mathlib.FieldTheory.Differential.Liouville

/-!
# Logarithmic derivatives of units

These tests ensure that the logarithmic derivative `Differential.logDeriv a = a′ / a` in a
differential field requires evidence that `a` is a unit, so that `0` no longer has the logarithmic
derivative `0`. The evidence is found from `a ≠ 0` and from `IsUnit a`. A Liouville extension is
stated for nonzero `uᵢ`, both in its hypothesis and in its conclusion.
-/

namespace DifferentialLogDerivStrict

open Differential algebraMap

/-- info: Unknown constant `Differential.logDeriv_zero` -/
#guard_msgs in
#check_failure Differential.logDeriv_zero

/-- info: Unknown constant `Differential.logDeriv_prod_of_eq_zero` -/
#guard_msgs in
#check_failure Differential.logDeriv_prod_of_eq_zero

variable {F : Type*} [Field F] [Differential F]

/-! Without evidence an element has no logarithmic derivative, and `0` has none at all. -/

/--
error: could not synthesize default value for parameter 'ha' using tactics
---
error: an invertibility proof is required
F : Type u_1
inst✝¹ : Field F
inst✝ : Differential F
a : F
⊢ IsUnit a
-/
#guard_msgs in
noncomputable example (a : F) : F := logDeriv a

/--
error: could not synthesize default value for parameter 'ha' using tactics
---
error: an invertibility proof is required
F : Type u_1
inst✝¹ : Field F
inst✝ : Differential F
⊢ IsUnit 0
-/
#guard_msgs in
noncomputable example : F := logDeriv 0

/-! The evidence is found from a nonzero element and from a unit. -/

noncomputable example (a : F) (ha : a ≠ 0) : F := logDeriv a

noncomputable example (a : F) (ha : IsUnit a) : F := logDeriv a

example : logDeriv (1 : F) = 0 := logDeriv_one

example (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    logDeriv (a * b) = logDeriv a + logDeriv b :=
  logDeriv_mul a b

example (a : F) (ha : a ≠ 0) (n : ℕ) : logDeriv (a ^ n) = n * logDeriv a :=
  logDeriv_pow n a

/-! A Liouville extension takes nonzero `uᵢ` and produces nonzero `uᵢ`. -/

variable {K : Type*} [Field K] [Differential K] [Algebra F K] [DifferentialAlgebra F K]

/--
error: Application type mismatch: The argument
  v
has type
  K
of sort `Type u_2` but is expected to have type
  ∀ (x : ι), u x ≠ 0
of sort `Prop` in the application
  IsLiouville.isLiouville a ι c hc u v
-/
#guard_msgs in
example [IsLiouville F K] (a : F) (ι : Type) [Fintype ι] (c : ι → F) (hc : ∀ x, (c x)′ = 0)
    (u : ι → K) (v : K) : True :=
  have := IsLiouville.isLiouville a ι c hc u v
  trivial

example [IsLiouville F K] (a : F) (ι : Type) [Fintype ι] (c : ι → F) (hc : ∀ x, (c x)′ = 0)
    (u : ι → K) (hu : ∀ x, u x ≠ 0) (v : K)
    (h : a = ∑ x, c x * logDeriv (u x) (hu x).isUnit + v′) :
    ∃ (ι₀ : Type) (_ : Fintype ι₀) (c₀ : ι₀ → F) (_ : ∀ x, (c₀ x)′ = 0)
      (u₀ : ι₀ → F) (hu₀ : ∀ x, u₀ x ≠ 0) (v₀ : F),
      a = ∑ x, c₀ x * logDeriv (u₀ x) (hu₀ x).isUnit + v₀′ :=
  IsLiouville.isLiouville a ι c hc u hu v h

end DifferentialLogDerivStrict
