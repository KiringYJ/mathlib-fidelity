/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Lua Viana Reis, Oliver Butterley
-/
module

public import Mathlib.Dynamics.BirkhoffSum.Basic
public import Mathlib.Algebra.Module.Basic

/-!
# Birkhoff average

In this file we define `birkhoffAverage f g n hn x` to be
$$
\frac{1}{n}\sum_{k=0}^{n-1}g(f^{[k]}(x)),
$$
where `f : α → α` is a self-map on some type `α`,
`g : α → M` is a function from `α` to a module over a division semiring `R`,
and `R` is used to formalize division by `n` as `(n : R)⁻¹ • _`.
The average exists when `n` is invertible in `R`, and `hn : IsUnit (n : R)` is that evidence;
in characteristic zero this means `n ≠ 0`. There is no average over the empty orbit segment.

While we need an auxiliary division semiring `R` to define `birkhoffAverage`,
the definition does not depend on the choice of `R`,
see `birkhoffAverage_congr_ring`.

-/

@[expose] public section

open Finset

section birkhoffAverage

variable (R : Type*) {α M : Type*} [DivisionSemiring R] [AddCommMonoid M] [Module R M]

/-- The average value of `g` on the first `n` points of the orbit of `x` under `f`,
i.e. the Birkhoff sum `∑ k ∈ Finset.range n, g (f^[k] x)` divided by `n`.

This average appears in many ergodic theorems
which say that the averages `birkhoffAverage R f g n _ x`
converge to the "space average" `⨍ x, g x ∂μ` as `n → ∞`.

We use an auxiliary `[DivisionSemiring R]` to define division by `n`, which needs the evidence
`hn` that `n` is invertible in `R`.
However, the definition does not depend on the choice of `R`,
see `birkhoffAverage_congr_ring`. -/
noncomputable def birkhoffAverage (f : α → α) (g : α → M) (n : ℕ) (hn : IsUnit (n : R))
    (x : α) : M :=
  (n : R)⁻¹ • birkhoffSum f g n x

theorem birkhoffAverage_one_apply (f : α → α) (g : α → M) {h : IsUnit ((1 : ℕ) : R)} (x : α) :
    birkhoffAverage R f g 1 h x = g x := by
  simp [birkhoffAverage]

@[simp]
theorem birkhoffAverage_one (f : α → α) (g : α → M) {h : IsUnit ((1 : ℕ) : R)} :
    birkhoffAverage R f g 1 h = g :=
  funext <| birkhoffAverage_one_apply R f g

@[deprecated (since := "2026-08-19")] alias birkhoffAverage_one' := birkhoffAverage_one

theorem map_birkhoffAverage (S : Type*) {F N : Type*}
    [DivisionSemiring S] [AddCommMonoid N] [Module S N] [FunLike F M N]
    [AddMonoidHomClass F M N] (g' : F) (f : α → α) (g : α → M) (n : ℕ) {hR : IsUnit (n : R)}
    (hS : IsUnit (n : S)) (x : α) :
    g' (birkhoffAverage R f g n hR x) = birkhoffAverage S f (g' ∘ g) n hS x := by
  simp only [birkhoffAverage, ← map_birkhoffSum]
  exact map_inv_natCast_smul g' R S n (hR := hR) (hS := hS) _

theorem map_comp_birkhoffAverage (S : Type*) {F N : Type*}
    [DivisionSemiring S] [AddCommMonoid N] [Module S N] [FunLike F M N]
    [AddMonoidHomClass F M N] (g' : F) (f : α → α) (g : α → M) (n : ℕ) {hR : IsUnit (n : R)}
    (hS : IsUnit (n : S)) :
    ⇑g' ∘ birkhoffAverage R f g n hR = birkhoffAverage S f (g' ∘ g) n hS :=
  funext <| map_birkhoffAverage R S g' f g n hS

theorem birkhoffAverage_apply_congr_ring (S : Type*) [DivisionSemiring S] [Module S M]
    (f : α → α) (g : α → M) (n : ℕ) {hR : IsUnit (n : R)} (hS : IsUnit (n : S)) (x : α) :
    birkhoffAverage R f g n hR x = birkhoffAverage S f g n hS x :=
  map_birkhoffAverage R S (AddMonoidHom.id M) f g n hS x

theorem birkhoffAverage_congr_ring (S : Type*) [DivisionSemiring S] [Module S M]
    (f : α → α) (g : α → M) (n : ℕ) {hR : IsUnit (n : R)} (hS : IsUnit (n : S)) :
    birkhoffAverage R f g n hR = birkhoffAverage S f g n hS :=
  funext <| birkhoffAverage_apply_congr_ring R S f g n hS

@[deprecated (since := "2026-08-19")] alias birkhoffAverage_congr_ring':= birkhoffAverage_congr_ring

theorem Function.IsFixedPt.birkhoffAverage_eq {f : α → α} {x : α} (h : IsFixedPt f x)
    (g : α → M) {n : ℕ} {hn : IsUnit (n : R)} : birkhoffAverage R f g n hn x = g x := by
  rw [birkhoffAverage, h.birkhoffSum_eq, ← Nat.cast_smul_eq_nsmul R, smul_smul, inv_mul_cancel₀,
    one_smul]

lemma birkhoffAverage_add_apply {f : α → α} {g g' : α → M} (n : ℕ) {hn : IsUnit (n : R)}
    (x : α) : birkhoffAverage R f (g + g') n hn x =
      birkhoffAverage R f g n hn x + birkhoffAverage R f g' n hn x := by
  simp [birkhoffAverage, birkhoffSum, sum_add_distrib, smul_add]

@[deprecated (since := "2026-08-19")] alias birkhoffSum_add' := birkhoffSum_add_apply

lemma birkhoffAverage_add {f : α → α} {g g' : α → M} (n : ℕ) {hn : IsUnit (n : R)} :
    birkhoffAverage R f (g + g') n hn =
      birkhoffAverage R f g n hn + birkhoffAverage R f g' n hn :=
  funext <| birkhoffAverage_add_apply R n

/-- If a function `g` is invariant under a function `f` (i.e., `g ∘ f = g`), then the Birkhoff
average of `g` over `f` for `n` iterations is equal to `g x` at every point `x`. -/
theorem birkhoffAverage_apply_of_comp_eq {f : α → α} {g : α → M} (h : g ∘ f = g)
    {n : ℕ} {hn : IsUnit (n : R)} (x : α) : birkhoffAverage R f g n hn x = g x := by
  suffices (n : R)⁻¹ • n • g x = g x by simpa [birkhoffAverage, birkhoffSum_of_comp_eq h]
  rw [← Nat.cast_smul_eq_nsmul R, smul_smul, inv_mul_cancel₀, one_smul]

/-- If a function `g` is invariant under a function `f` (i.e., `g ∘ f = g`), then the Birkhoff
average of `g` over `f` for `n` iterations is equal to `g`. -/
theorem birkhoffAverage_of_comp_eq {f : α → α} {g : α → M} (h : g ∘ f = g)
    {n : ℕ} {hn : IsUnit (n : R)} : birkhoffAverage R f g n hn = g :=
  funext <| birkhoffAverage_apply_of_comp_eq R h

end birkhoffAverage

section AddCommGroup

variable {R : Type*} {α M : Type*} [DivisionSemiring R] [AddCommGroup M] [Module R M]

lemma birkhoffAverage_neg_apply {f : α → α} {g : α → M} (n : ℕ) {hn : IsUnit (n : R)} (x : α) :
    birkhoffAverage R f (-g) n hn x = -birkhoffAverage R f g n hn x := by
  simp [birkhoffAverage, birkhoffSum]

lemma birkhoffAverage_neg {f : α → α} {g : α → M} (n : ℕ) {hn : IsUnit (n : R)} :
    birkhoffAverage R f (-g) n hn = -birkhoffAverage R f g n hn :=
  funext <| birkhoffAverage_neg_apply n

lemma birkhoffAverage_sub_apply {f : α → α} {g g' : α → M} (n : ℕ) {hn : IsUnit (n : R)}
    (x : α) : birkhoffAverage R f (g - g') n hn x =
      birkhoffAverage R f g n hn x - birkhoffAverage R f g' n hn x := by
  simp [birkhoffAverage, birkhoffSum, smul_sub]

lemma birkhoffAverage_sub {f : α → α} {g g' : α → M} (n : ℕ) {hn : IsUnit (n : R)} :
    birkhoffAverage R f (g - g') n hn =
      birkhoffAverage R f g n hn - birkhoffAverage R f g' n hn :=
  funext <| birkhoffAverage_sub_apply n

/-- Birkhoff average is "almost invariant" under `f`:
the difference between `birkhoffAverage R f g n hn (f x)` and `birkhoffAverage R f g n hn x`
is equal to `(n : R)⁻¹ • (g (f^[n] x) - g x)`. -/
theorem birkhoffAverage_apply_sub_birkhoffAverage (f : α → α) (g : α → M) (n : ℕ)
    {hn : IsUnit (n : R)} (x : α) :
    birkhoffAverage R f g n hn (f x) - birkhoffAverage R f g n hn x =
      (n : R)⁻¹ • (g (f^[n] x) - g x) := by
  simp only [birkhoffAverage, birkhoffSum_apply_sub_birkhoffSum, ← smul_sub]

/-- Birkhoff average is "almost invariant" under `f`:
the difference between `birkhoffAverage R f g n hn ∘ f` and `birkhoffAverage R f g n hn`
is equal to `(n : R)⁻¹ • (g ∘ f^[n] - g)`. -/
theorem birkhoffAverage_comp_sub_birkhoffAverage (f : α → α) (g : α → M) (n : ℕ)
    {hn : IsUnit (n : R)} :
    birkhoffAverage R f g n hn ∘ f - birkhoffAverage R f g n hn =
      (n : R)⁻¹ • (g ∘ f^[n] - g) :=
  funext <| birkhoffAverage_apply_sub_birkhoffAverage f g n

end AddCommGroup
