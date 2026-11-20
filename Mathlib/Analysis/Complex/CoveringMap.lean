/-
Copyright (c) 2026 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Mathlib.Topology.Algebra.Group.Units
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Topology.Covering.Quotient
public import Mathlib.Topology.GDelta.MetrizableSpace
public import Mathlib.Topology.LocalAtTarget

/-!
# Covering maps involving the complex plane

In this file, we show that `Complex.exp` and `(· ^ n)` (for `n ≠ 0`) are a covering map on `{0}ᶜ`.
We also show that any complex polynomial is a covering map on the set of regular values.
-/

public section

open Topology

namespace Complex

theorem isAddQuotientCoveringMap_exp :
    IsAddQuotientCoveringMap (fun z : ℂ ↦ (⟨_, z.exp_ne_zero⟩ : {z : ℂ // z ≠ 0}))
      (AddSubgroup.zmultiples (2 * Real.pi * I)) := by
  refine Topology.IsQuotientMap.isAddQuotientCoveringMap_of_addSubgroup ?_
    _ ⟨NormedSpace.discreteTopology_zmultiples _⟩ fun {z _} ↦ ?_
  · refine IsOpenMap.isQuotientMap ?_ (by fun_prop) fun z ↦ ⟨_, Subtype.ext (exp_log z.2)⟩
    exact (IsOpen.isOpenEmbedding_subtypeVal isClosed_singleton.1).isOpenMap_iff.mpr isOpenMap_exp
  · simp_rw [Subtype.ext_iff, eq_comm (a := exp z), exp_eq_exp_iff_exists_int,
      AddSubgroup.mem_zmultiples_iff, eq_add_neg_iff_add_eq, eq_comm, add_comm, zsmul_eq_mul]

/-- `exp : ℂ → ℂ \ {0}` is a covering map. -/
theorem isCoveringMap_exp : IsCoveringMap fun z : ℂ ↦ (⟨_, z.exp_ne_zero⟩ : {z : ℂ // z ≠ 0}) :=
  isAddQuotientCoveringMap_exp.isCoveringMap

theorem isCoveringMapOn_exp : IsCoveringMapOn Complex.exp {0}ᶜ :=
  .of_isCoveringMap_subtype (by simp) _ isCoveringMap_exp

end Complex

section

open Polynomial

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [ProperSpace 𝕜]

theorem Polynomial.isCoveringMapOn_eval (p : 𝕜[X]) :
    IsCoveringMapOn p.eval (p.eval '' {k | p.derivative.eval k = 0})ᶜ := by
  refine p.isClosedMap_eval.isCoveringMapOn_of_isLocalHomeomorphOn (fun x hx ↦ ?_)
    fun x hx ↦ ⟨_, ((p.hasStrictDerivAt x).hasStrictFDerivAt_equiv
      fun h ↦ hx ⟨x, h, rfl⟩).mem_toOpenPartialHomeomorph_source, by simp⟩
  obtain rfl | ne := eq_or_ne p (C x)
  · simp at hx
  · simpa only [preimage_eval_singleton ne] using rootSet_finite ..

theorem isCoveringMapOn_npow (n : ℕ) (hn : (n : 𝕜) ≠ 0) :
    IsCoveringMapOn (fun x : 𝕜 ↦ x ^ n) {0}ᶜ := by
  convert! (X ^ n).isCoveringMapOn_eval.mono fun x' h ↦ _ with x
  · simp
  · assumption
  · simpa [derivative_X_pow, hn, show n ≠ 0 by aesop] using fun _ ↦ Ne.symm h

/-- `(· ^ n) : 𝕜 \ {0} → 𝕜 \ {0}` is a covering map (if `n ≠ 0` in `𝕜`). -/
theorem isCoveringMap_npow (n : ℕ) (hn : (n : 𝕜) ≠ 0) :
    IsCoveringMap fun x : {x : 𝕜 // x ≠ 0} ↦ (⟨x ^ n, pow_ne_zero n x.2⟩ : {x : 𝕜 // x ≠ 0}) := by
  convert!
    (isCoveringMapOn_npow n hn).isCoveringMap_restrictPreimage.comp_homeomorph
      (.setCongr (s := {x | x ≠ 0}) _) using 1
  ext; simp [show n ≠ 0 by aesop]

/-- `(· ^ n) : 𝕜 \ {0} → 𝕜 \ {0}` is a covering map (if `n ≠ 0` in `𝕜`). -/
theorem isCoveringMap_zpow (n : ℤ) (hn : (n : 𝕜) ≠ 0) :
    IsCoveringMap fun x : {x : 𝕜 // x ≠ 0} ↦ (⟨x ^ n, zpow_ne_zero n x.2⟩ : {x : 𝕜 // x ≠ 0}) := by
  obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg
  · exact isCoveringMap_npow n (by simpa using hn)
  · have hn' : (n : 𝕜) ≠ 0 := by simpa using hn
    convert (isCoveringMap_npow n hn').homeomorph_comp (Homeomorph.inv₀ 𝕜) using 1
    funext x
    apply Subtype.ext
    exact zpow_neg₀ x.property (n : ℤ)

theorem isCoveringMapOn_zpow (n : ℤ) (hn : (n : 𝕜) ≠ 0) :
    IsCoveringMapOn (fun x : {x : 𝕜 // n < 0 → x ≠ 0} ↦
      Checked.zpow (x : 𝕜) n (fun h ↦ (x.property h).isUnit)) {0}ᶜ := by
  obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg
  · let e : {x : 𝕜 // (n : ℤ) < 0 → x ≠ 0} ≃ₜ 𝕜 :=
      (Homeomorph.setCongr (s := {x : 𝕜 | (n : ℤ) < 0 → x ≠ 0}) (t := Set.univ) (by
        ext x
        simp)).trans (Homeomorph.Set.univ 𝕜)
    exact (isCoveringMapOn_npow n (by simpa using hn)).comp_homeomorph e
  · have hn' : n ≠ 0 := by
      rintro rfl
      simp at hn
    have hneg : -(n : ℤ) < 0 := by omega
    let e : {x : 𝕜 // -(n : ℤ) < 0 → x ≠ 0} ≃ₜ {x : 𝕜 // x ≠ 0} :=
      Homeomorph.setCongr (Set.ext fun x ↦ by
        change (-(n : ℤ) < 0 → x ≠ 0) ↔ x ≠ 0
        exact ⟨fun hx ↦ hx hneg, fun hx _ ↦ hx⟩)
    refine .of_isCoveringMap_subtype isClosed_singleton.isOpen_compl (fun x ↦ ?_) ?_
    · simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
        zpow_ne_zero (-(n : ℤ)) (x.property hneg)
    · exact (isCoveringMap_zpow (-(n : ℤ)) hn).comp_homeomorph e

attribute [-instance] Units.mulAction'

theorem isQuotientCoveringMap_npow (n : ℕ) (hn : (n : 𝕜) ≠ 0)
    (surj : (fun x : 𝕜 ↦ x ^ n).Surjective) :
    IsQuotientCoveringMap (fun x : 𝕜ˣ ↦ x ^ n) (powMonoidHom (α := 𝕜ˣ) n).ker := by
  rw [← rootsOfUnity_eq_ker]
  have : NeZero n := ⟨by aesop⟩
  have := ((isClosedMap_pow 𝕜 n).restrictPreimage {0}ᶜ).isQuotientMap
    (by fun_prop) (.restrictPreimage _ surj)
  have : IsQuotientMap fun x : 𝕜ˣ ↦ x ^ n := by
    let e := unitsHomeomorphNeZero (G₀ := 𝕜)
    convert! (e.symm.isQuotientMap.comp this).comp (e.trans (.ofEqSubtypes _)).isQuotientMap
    · exact (e.left_inv _).symm
    · ext; simp [NeZero.ne]
  refine this.isQuotientCoveringMap_of_subgroup _
    (Set.Finite.isDiscrete <| inferInstanceAs (Finite (rootsOfUnity ..))) ?_
  simp [mul_pow, mul_inv_eq_one, eq_comm]

protected theorem Complex.isQuotientCoveringMap_npow (n : ℕ) [NeZero n] :
    IsQuotientCoveringMap (fun z : ℂˣ ↦ z ^ n) (powMonoidHom (α := ℂˣ) n).ker :=
  isQuotientCoveringMap_npow n (by simp [NeZero.ne]) fun _ ↦ ⟨_, cpow_nat_inv_pow _ (NeZero.ne n)⟩

theorem isQuotientCoveringMap_zpow (n : ℤ) (hn : (n : 𝕜) ≠ 0)
    (surj : (fun x : 𝕜ˣ ↦ x ^ n).Surjective) :
    IsQuotientCoveringMap (fun x : 𝕜ˣ ↦ x ^ n) (zpowGroupHom (α := 𝕜ˣ) n).ker := by
  have surjPow {k : ℕ} (hk : (k : 𝕜) ≠ 0) (h : (fun x : 𝕜ˣ ↦ x ^ k).Surjective) :
      (fun x : 𝕜 ↦ x ^ k).Surjective := by
    intro y
    by_cases hy : y = 0
    · have hk' : k ≠ 0 := by rintro rfl; simp at hk
      exact ⟨0, by simp [hy, hk']⟩
    · obtain ⟨x, hx⟩ := h (Units.mk0 y hy)
      exact ⟨x, by simpa using congrArg Units.val hx⟩
  obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg
  · exact isQuotientCoveringMap_npow n (by simpa using hn) (surjPow (by simpa using hn) (by
      simpa using surj))
  · have hn' : (n : 𝕜) ≠ 0 := by simpa using hn
    have hs : (fun x : 𝕜ˣ ↦ x ^ n).Surjective := by
      intro y
      obtain ⟨x, hx⟩ := surj y⁻¹
      exact ⟨x, by simpa [zpow_neg] using congrArg Inv.inv hx⟩
    rw [show (zpowGroupHom (α := 𝕜ˣ) (-n)).ker = (powMonoidHom n).ker by ext; simp]
    convert (isQuotientCoveringMap_npow n hn' (surjPow hn' hs)).homeomorph_comp (.inv 𝕜ˣ) using 1
    funext x
    simp [zpow_neg]

end
