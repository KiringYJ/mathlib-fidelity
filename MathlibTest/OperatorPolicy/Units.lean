/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
import MathlibTest.OperatorPolicy.Import
import Mathlib.Algebra.Group.Units.Basic
example {M : Type*} [Monoid M] : Inv Mˣ := inferInstance
example {M : Type*} [Monoid M] : Div Mˣ := inferInstance
example {M : Type*} [Monoid M] : Pow Mˣ Int := inferInstance
example {G : Type*} [Group G] : Inv G := inferInstance
example {G : Type*} [Group G] : Div G := inferInstance
example {G : Type*} [Group G] : Pow G Int := inferInstance
example : True := by
  fail_if_success have : Div Int := inferInstance
  fail_if_success have : Div Nat := inferInstance
  trivial
