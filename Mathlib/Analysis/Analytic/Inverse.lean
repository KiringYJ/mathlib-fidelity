/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Analytic.Composition
public import Mathlib.Analysis.Analytic.Linear
public import Mathlib.Tactic.Positivity
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.OneSidedInverse

/-!

# Inverse of analytic functions

We construct formal left and right inverses of a formal multilinear series whose linear term has a
continuous linear left or right inverse, we prove that they coincide when the linear term is
invertible and study their properties (notably convergence). We deduce that the inverse of an
analytic open partial homeomorphism is analytic.

A formal left inverse of `p : FormalMultilinearSeries 𝕜 E F` with constant coefficient `x` is a
series `q` with `q.comp p = id 𝕜 E x`, and a formal right inverse of `p` with constant coefficient
`x` is a series `q` with `p.comp q = id 𝕜 F (p 0 0)` and `q 0 0 = x`. They exist exactly when the
linear term `p₁` of `p` has a continuous linear left, respectively right, inverse: comparing linear
terms shows that this is necessary, and the constructions below take such a linear inverse as
data. Formal one-sided inverses need not be unique when `p₁` is not invertible, and the linear
inverse selects one of them. When `p₁` is invertible, a formal left inverse and a formal right
inverse with the same constant coefficient coincide, so both constructions give the unique formal
inverse with that constant coefficient.

## Main statements

* `p.leftInv r hr x`: the formal left inverse of the formal multilinear series `p`, with constant
  coefficient `x`, constructed from a continuous linear left inverse `r` of `p₁`.
* `p.rightInv s hs x`: the formal right inverse of the formal multilinear series `p`, with constant
  coefficient `x`, constructed from a continuous linear right inverse `s` of `p₁`.
* `p.leftInv_comp` says that `p.leftInv r hr x` is indeed a left inverse to `p`.
* `p.comp_rightInv` says that `p.rightInv s hs x` is indeed a right inverse to `p`.
* `p.exists_comp_eq_id_iff_hasLeftInverse` and `p.exists_comp_eq_id_iff_hasRightInverse`:
  formal one-sided inverses exist exactly when `p₁` has a continuous linear one-sided inverse.
* `p.eq_leftInv_of_comp_eq_id_of_compContinuousLinearMap_eq` and
  `p.eq_rightInv_of_comp_eq_id_of_apply_mem_range` characterize the two constructions among the
  formal one-sided inverses with a given constant coefficient.
* `p.leftInv_eq_rightInv`: the two inverses coincide when `p₁` has both one-sided inverses, and
  `p.eq_rightInv_of_comp_eq_id_left`, `p.eq_leftInv_of_comp_eq_id_right` show that they are then
  unique.
* `p.radius_rightInv_pos_of_radius_pos`, `p.radius_leftInv_pos_of_radius_pos`: if a power series
  has a positive radius of convergence, then so do `p.rightInv s hs x` and `p.leftInv r hr x`.
  Other formal one-sided inverses need not converge when `p₁` is not invertible.

* `OpenPartialHomeomorph.hasFPowerSeriesAt_symm` shows that, if an open partial homeomorph has a
  power series `p` at a point `a` and `p₁` has a continuous linear left inverse `r`, then the
  inverse also has a power series at the image point, given by `p.leftInv r hr a`.
-/

@[expose] public section

open scoped Topology ENNReal

open Finset Filter

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

namespace FormalMultilinearSeries

/-! ### The left inverse of a formal multilinear series -/


/-- The formal left inverse of a formal multilinear series `p` constructed from a continuous linear
left inverse `r` of its linear term `p₁`, with constant coefficient `x`, so that
`(p.leftInv r hr x).comp p = id 𝕜 E x` (`leftInv_comp`).

The `n`-th term in `q ∘ p` is `∑ qₖ (p_{j₁}, ..., p_{jₖ})` over `j₁ + ... + jₖ = n`. In this
expression, `qₙ` appears only once, in `qₙ (p₁, ..., p₁)`. The `n`-th term of the left inverse is
defined inductively in terms of the previous ones so that this term compensates the rest of the sum,
using `r` to recover the arguments of `qₙ` from their images under `p₁`.

Formal left inverses of `p` exist exactly when `p₁` has a continuous linear left inverse
(`exists_comp_eq_id_iff_hasLeftInverse`). They are not unique in general, and different left
inverses of a noninvertible `p₁` give different formal left inverses. This one is the unique formal
left inverse with constant coefficient `x` whose coefficients depend on their vector arguments only
through their images under `r` (`leftInv_compContinuousLinearMap`,
`eq_leftInv_of_comp_eq_id_of_compContinuousLinearMap_eq`). When `p₁` is invertible, `r` is its
inverse and `p.leftInv r hr x` is the unique formal left inverse with constant coefficient `x`
(`eq_rightInv_of_comp_eq_id_left`, `leftInv_eq_rightInv`).

The construction uses only the coefficients of `p` of positive order (`leftInv_removeZero`): as in
`FormalMultilinearSeries.comp`, the constant coefficient of `p` is the point at which the left
inverse is expanded.
-/
@[nolint unusedArguments]
noncomputable def leftInv (p : FormalMultilinearSeries 𝕜 E F) (r : F →L[𝕜] E)
    (hr : Function.LeftInverse r (continuousMultilinearCurryFin1 𝕜 E F (p 1))) (x : E) :
    FormalMultilinearSeries 𝕜 F E
  | 0 => ContinuousMultilinearMap.uncurry0 𝕜 _ x
  | 1 => (continuousMultilinearCurryFin1 𝕜 F E).symm r
  | n + 2 =>
    -∑ c : { c : Composition (n + 2) // c.length < n + 2 },
        (leftInv p r hr x (c : Composition (n + 2)).length).compAlongComposition
          (p.compContinuousLinearMap r) c

@[simp]
theorem leftInv_coeff_zero (p : FormalMultilinearSeries 𝕜 E F) (r : F →L[𝕜] E)
    (hr : Function.LeftInverse r (continuousMultilinearCurryFin1 𝕜 E F (p 1))) (x : E) :
    p.leftInv r hr x 0 = ContinuousMultilinearMap.uncurry0 𝕜 _ x := by rw [leftInv]

@[simp]
theorem leftInv_coeff_one (p : FormalMultilinearSeries 𝕜 E F) (r : F →L[𝕜] E)
    (hr : Function.LeftInverse r (continuousMultilinearCurryFin1 𝕜 E F (p 1))) (x : E) :
    p.leftInv r hr x 1 = (continuousMultilinearCurryFin1 𝕜 F E).symm r := by rw [leftInv]

/-- The left inverse does not depend on the zeroth coefficient of a formal multilinear
series. -/
theorem leftInv_removeZero (p : FormalMultilinearSeries 𝕜 E F) (r : F →L[𝕜] E)
    (hr : Function.LeftInverse r (continuousMultilinearCurryFin1 𝕜 E F (p.removeZero 1)))
    (hr' : Function.LeftInverse r (continuousMultilinearCurryFin1 𝕜 E F (p 1))) (x : E) :
    p.removeZero.leftInv r hr x = p.leftInv r hr' x := by
  ext1 n
  induction n using Nat.strong_induction_on with | _ n IH
  match n with
  | 0 => simp -- if one replaces `simp` with `refl`, the proof times out in the kernel.
  | 1 => simp -- TODO: why?
  | n + 2 =>
    simp only [leftInv, neg_inj]
    refine Finset.sum_congr rfl fun c cuniv => ?_
    rcases c with ⟨c, hc⟩
    ext v
    simp [IH _ hc]

/-- The left inverse to a formal multilinear series is indeed a left inverse. -/
theorem leftInv_comp (p : FormalMultilinearSeries 𝕜 E F) (r : F →L[𝕜] E)
    (hr : Function.LeftInverse r (continuousMultilinearCurryFin1 𝕜 E F (p 1))) (x : E) :
    (leftInv p r hr x).comp p = id 𝕜 E x := by
  obtain ⟨L, hL⟩ : ∃ L, continuousMultilinearCurryFin1 𝕜 E F (p 1) = L := ⟨_, rfl⟩
  have h : p 1 = (continuousMultilinearCurryFin1 𝕜 E F).symm L := by simp [← hL]
  have hr' : ∀ v, r (L v) = v := by rw [← hL]; exact hr
  ext n v
  match n with
  | 0 =>
    simp only [comp_coeff_zero', leftInv_coeff_zero, ContinuousMultilinearMap.uncurry0_apply,
      id_apply_zero]
  | 1 =>
    simp only [leftInv_coeff_one, comp_coeff_one, h, id_apply_one,
      continuousMultilinearCurryFin1_symm_apply, hr']
  | n + 2 =>
    have A :
      (Finset.univ : Finset (Composition (n + 2))) =
        {c | Composition.length c < n + 2}.toFinset ∪ {Composition.ones (n + 2)} := by
      refine Subset.antisymm (fun c _ => ?_) (subset_univ _)
      by_cases! h : c.length < n + 2
      · simp [h]
      · simp [Composition.eq_ones_iff_le_length.2 h]
    have B :
      Disjoint ({c | Composition.length c < n + 2} : Set (Composition (n + 2))).toFinset
        {Composition.ones (n + 2)} := by
      simp
    have C :
      ((p.leftInv r hr x (Composition.ones (n + 2)).length)
          fun j : Fin (Composition.ones n.succ.succ).length =>
          p 1 fun _ => v ((Fin.castLE (Composition.length_le _)) j)) =
        p.leftInv r hr x (n + 2) fun j : Fin (n + 2) => p 1 fun _ => v j := by
      apply FormalMultilinearSeries.congr _ (Composition.ones_length _) fun j hj1 hj2 => ?_
      exact FormalMultilinearSeries.congr _ rfl fun k _ _ => by congr
    have D :
      (p.leftInv r hr x (n + 2) fun j : Fin (n + 2) => p 1 fun _ => v j) =
        -∑ c ∈ {c : Composition (n + 2) | c.length < n + 2}.toFinset,
            (p.leftInv r hr x c.length) (p.applyComposition c v) := by
      simp only [leftInv, _root_.neg_apply, neg_inj, _root_.sum_apply]
      convert!
        (sum_toFinset_eq_subtype (fun c : Composition (n + 2) => c.length < n + 2)
              (fun c : Composition (n + 2) =>
                (ContinuousMultilinearMap.compAlongComposition
                    (p.compContinuousLinearMap r) c (p.leftInv r hr x c.length))
                  fun j : Fin (n + 2) => p 1 fun _ : Fin 1 => v j)).symm.trans
          _
      simp only [compContinuousLinearMap_applyComposition,
        ContinuousMultilinearMap.compAlongComposition_apply]
      congr
      ext c
      congr
      ext k
      simp [h, hr']
    simp [FormalMultilinearSeries.comp, A, Finset.sum_union B,
      applyComposition_ones, C, D, -Set.toFinset_ofPred, -Finset.union_singleton]

/-- The coefficients of the left inverse depend on their vector arguments only through their images
under `r`: the left inverse is unchanged by precomposition with the continuous linear projection
`p₁ ∘ r` onto the range of `p₁` along the kernel of `r`. -/
theorem leftInv_compContinuousLinearMap (p : FormalMultilinearSeries 𝕜 E F) (r : F →L[𝕜] E)
    (hr : Function.LeftInverse r (continuousMultilinearCurryFin1 𝕜 E F (p 1))) (x : E) :
    (p.leftInv r hr x).compContinuousLinearMap
        ((continuousMultilinearCurryFin1 𝕜 E F (p 1)).comp r) =
      p.leftInv r hr x := by
  have hr' (w : F) : r (continuousMultilinearCurryFin1 𝕜 E F (p 1) (r w)) = r w := hr (r w)
  ext n w
  match n with
  | 0 =>
    simp only [compContinuousLinearMap_apply, leftInv_coeff_zero,
      ContinuousMultilinearMap.uncurry0_apply]
  | 1 =>
    simp only [compContinuousLinearMap_apply, leftInv_coeff_one,
      continuousMultilinearCurryFin1_symm_apply, Function.comp_apply,
      ContinuousLinearMap.comp_apply, hr']
  | n + 2 =>
    simp only [compContinuousLinearMap_apply, leftInv, _root_.neg_apply, _root_.sum_apply,
      ContinuousMultilinearMap.compAlongComposition_apply,
      compContinuousLinearMap_applyComposition]
    have hw : r ∘ (continuousMultilinearCurryFin1 𝕜 E F (p 1)).comp r ∘ w = r ∘ w := by
      ext k
      simp only [Function.comp_apply, ContinuousLinearMap.coe_comp, hr']
    rw [hw]

/-! ### The right inverse of a formal multilinear series -/


/-- The formal right inverse of a formal multilinear series `p` constructed from a continuous linear
right inverse `s` of its linear term `p₁`, with constant coefficient `x`, so that
`p.comp (p.rightInv s hs x) = id 𝕜 F (p 0 0)` (`comp_rightInv`).

The `n`-th term in `p ∘ q` is `∑ pₖ (q_{j₁}, ..., q_{jₖ})` over `j₁ + ... + jₖ = n`. In this
expression, `qₙ` appears only once, in `p₁ (qₙ)`. The `n`-th term of the right inverse is defined
inductively in terms of the previous ones so that this term compensates the rest of the sum, using
`s` to choose `qₙ` from the required value of `p₁ (qₙ)`.

Formal right inverses of `p` exist exactly when `p₁` has a continuous linear right inverse
(`exists_comp_eq_id_iff_hasRightInverse`). They are not unique in general, and different right
inverses of a noninvertible `p₁` give different formal right inverses. This one is the unique
formal right inverse with constant coefficient `x` whose coefficients of positive order take values
in the range of `s` (`rightInv_apply_mem_range`, `eq_rightInv_of_comp_eq_id_of_apply_mem_range`).
When `p₁` is invertible, `s` is its inverse and `p.rightInv s hs x` is the unique formal right
inverse with constant coefficient `x` (`eq_leftInv_of_comp_eq_id_right`, `leftInv_eq_rightInv`).

The construction uses only the coefficients of `p` of positive order (`rightInv_removeZero`).
-/
@[nolint unusedArguments]
noncomputable def rightInv (p : FormalMultilinearSeries 𝕜 E F) (s : F →L[𝕜] E)
    (hs : Function.RightInverse s (continuousMultilinearCurryFin1 𝕜 E F (p 1))) (x : E) :
    FormalMultilinearSeries 𝕜 F E
  | 0 => ContinuousMultilinearMap.uncurry0 𝕜 _ x
  | 1 => (continuousMultilinearCurryFin1 𝕜 F E).symm s
  | n + 2 =>
    let q : FormalMultilinearSeries 𝕜 F E := fun k => if k < n + 2 then rightInv p s hs x k else 0;
    -s.compContinuousMultilinearMap ((p.comp q) (n + 2))

@[simp]
theorem rightInv_coeff_zero (p : FormalMultilinearSeries 𝕜 E F) (s : F →L[𝕜] E)
    (hs : Function.RightInverse s (continuousMultilinearCurryFin1 𝕜 E F (p 1))) (x : E) :
    p.rightInv s hs x 0 = ContinuousMultilinearMap.uncurry0 𝕜 _ x := by rw [rightInv]

@[simp]
theorem rightInv_coeff_one (p : FormalMultilinearSeries 𝕜 E F) (s : F →L[𝕜] E)
    (hs : Function.RightInverse s (continuousMultilinearCurryFin1 𝕜 E F (p 1))) (x : E) :
    p.rightInv s hs x 1 = (continuousMultilinearCurryFin1 𝕜 F E).symm s := by rw [rightInv]

set_option backward.isDefEq.respectTransparency false in
/-- The right inverse does not depend on the zeroth coefficient of a formal multilinear
series. -/
theorem rightInv_removeZero (p : FormalMultilinearSeries 𝕜 E F) (s : F →L[𝕜] E)
    (hs : Function.RightInverse s (continuousMultilinearCurryFin1 𝕜 E F (p.removeZero 1)))
    (hs' : Function.RightInverse s (continuousMultilinearCurryFin1 𝕜 E F (p 1))) (x : E) :
    p.removeZero.rightInv s hs x = p.rightInv s hs' x := by
  ext1 n
  induction n using Nat.strong_induction_on with | _ n IH
  match n with
  | 0 => simp only [rightInv_coeff_zero]
  | 1 => simp only [rightInv_coeff_one]
  | n + 2 =>
    simp only [rightInv, neg_inj]
    rw [removeZero_comp_of_pos _ _ (add_pos_of_nonneg_of_pos n.zero_le zero_lt_two)]
    congr (config := { closePost := false }) 2 with k
    by_cases hk : k < n + 2 <;> simp [hk, IH]

theorem comp_rightInv_aux1 {n : ℕ} (hn : 0 < n) (p : FormalMultilinearSeries 𝕜 E F)
    (q : FormalMultilinearSeries 𝕜 F E) (v : Fin n → F) :
    p.comp q n v =
      ∑ c ∈ {c : Composition n | 1 < c.length}.toFinset,
          p c.length (q.applyComposition c v) + p 1 fun _ => q n v := by
  have A :
    (Finset.univ : Finset (Composition n)) =
      {c | 1 < Composition.length c}.toFinset ∪ {Composition.single n hn} := by
    refine Subset.antisymm (fun c _ => ?_) (subset_univ _)
    by_cases h : 1 < c.length
    · simp [h]
    · have : c.length = 1 := by
        refine (eq_iff_le_not_lt.2 ⟨?_, h⟩).symm; exact c.length_pos_of_pos hn
      rw [← Composition.eq_single_iff_length hn] at this
      simp [this]
  have B :
    Disjoint ({c | 1 < Composition.length c} : Set (Composition n)).toFinset
      {Composition.single n hn} := by
    simp
  have C :
    p (Composition.single n hn).length (q.applyComposition (Composition.single n hn) v) =
      p 1 fun _ : Fin 1 => q n v := by
    apply p.congr (Composition.single_length hn) fun j hj1 _ => ?_
    simp [applyComposition_single]
  simp [FormalMultilinearSeries.comp, A, Finset.sum_union B, C, -Set.toFinset_ofPred,
    -add_right_inj, -Composition.single_length, -Finset.union_singleton]

theorem comp_rightInv_aux2 (p : FormalMultilinearSeries 𝕜 E F) (s : F →L[𝕜] E)
    (hs : Function.RightInverse s (continuousMultilinearCurryFin1 𝕜 E F (p 1))) (x : E) (n : ℕ)
    (v : Fin (n + 2) → F) :
    ∑ c ∈ {c : Composition (n + 2) | 1 < c.length}.toFinset,
        p c.length (applyComposition (fun k : ℕ => ite (k < n + 2) (p.rightInv s hs x k) 0) c v) =
      ∑ c ∈ {c : Composition (n + 2) | 1 < c.length}.toFinset,
        p c.length ((p.rightInv s hs x).applyComposition c v) := by
  have N : 0 < n + 2 := by simp
  refine sum_congr rfl fun c hc => p.congr rfl fun j hj1 hj2 => ?_
  have : ∀ k, c.blocksFun k < n + 2 := by
    simp only [Set.mem_toFinset (s := {c : Composition (n + 2) | 1 < c.length}),
      Set.mem_ofPred_eq] at hc
    simp [← Composition.ne_single_iff N, Composition.eq_single_iff_length, ne_of_gt hc]
  simp [applyComposition, this]

set_option backward.isDefEq.respectTransparency false in
/-- The right inverse to a formal multilinear series is indeed a right inverse. -/
theorem comp_rightInv (p : FormalMultilinearSeries 𝕜 E F) (s : F →L[𝕜] E)
    (hs : Function.RightInverse s (continuousMultilinearCurryFin1 𝕜 E F (p 1))) (x : E) :
    p.comp (rightInv p s hs x) = id 𝕜 F (p 0 0) := by
  obtain ⟨L, hL⟩ : ∃ L, continuousMultilinearCurryFin1 𝕜 E F (p 1) = L := ⟨_, rfl⟩
  have h : p 1 = (continuousMultilinearCurryFin1 𝕜 E F).symm L := by simp [← hL]
  have hs' : ∀ w, L (s w) = w := by rw [← hL]; exact hs
  ext (n v)
  match n with
  | 0 =>
    simp only [comp_coeff_zero', Matrix.zero_empty, id_apply_zero]
    congr
    ext i
    exact i.elim0
  | 1 =>
    simp only [comp_coeff_one, h, rightInv_coeff_one, id_apply_one,
      continuousMultilinearCurryFin1_symm_apply, hs']
  | n + 2 =>
    have N : 0 < n + 2 := by simp
    simp [comp_rightInv_aux1 N, h, rightInv, comp_rightInv_aux2, hs', -Set.toFinset_ofPred]

set_option backward.isDefEq.respectTransparency false in
theorem rightInv_coeff (p : FormalMultilinearSeries 𝕜 E F) (s : F →L[𝕜] E)
    (hs : Function.RightInverse s (continuousMultilinearCurryFin1 𝕜 E F (p 1))) (x : E)
    (n : ℕ) (hn : 2 ≤ n) :
    p.rightInv s hs x n =
      -s.compContinuousMultilinearMap
          (∑ c ∈ ({c | 1 < Composition.length c}.toFinset : Finset (Composition n)),
            p.compAlongComposition (p.rightInv s hs x) c) := by
  match n with
  | 0 => exact False.elim (zero_lt_two.not_ge hn)
  | 1 => exact False.elim (one_lt_two.not_ge hn)
  | n + 2 =>
    simp only [rightInv, neg_inj]
    congr (config := { closePost := false }) 1
    ext v
    have N : 0 < n + 2 := by simp
    have : ((p 1) fun _ : Fin 1 => 0) = 0 := ContinuousMultilinearMap.map_zero _
    simp [comp_rightInv_aux1 N, this, comp_rightInv_aux2, -Set.toFinset_ofPred]

/-- The coefficients of positive order of the right inverse take values in the range of `s`. -/
theorem rightInv_apply_mem_range (p : FormalMultilinearSeries 𝕜 E F) (s : F →L[𝕜] E)
    (hs : Function.RightInverse s (continuousMultilinearCurryFin1 𝕜 E F (p 1))) (x : E)
    {n : ℕ} (hn : 0 < n) (v : Fin n → F) : p.rightInv s hs x n v ∈ Set.range s := by
  match n with
  | 1 => exact ⟨v 0, by simp⟩
  | n + 2 =>
    rw [rightInv_coeff p s hs x (n + 2) (by lia), _root_.neg_apply,
      ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply, ← map_neg]
    exact Set.mem_range_self _

/-! ### Existence, coincidence and uniqueness of formal inverses -/


/-- A formal left inverse of `p` coincides with a formal right inverse of `p` that has the same
constant coefficient. -/
theorem eq_of_comp_eq_id_of_comp_eq_id (p : FormalMultilinearSeries 𝕜 E F)
    {q q' : FormalMultilinearSeries 𝕜 F E} {x : E} (hq : q.comp p = id 𝕜 E x)
    (hq' : p.comp q' = id 𝕜 F (p 0 0)) (hx : q' 0 0 = x) : q = q' :=
  calc
    q = q.comp (id 𝕜 F (p 0 0)) := (comp_id q _).symm
    _ = q.comp (p.comp q') := by rw [hq']
    _ = (q.comp p).comp q' := (comp_assoc _ _ _).symm
    _ = (id 𝕜 E x).comp q' := by rw [hq]
    _ = q' := id_comp' q' x 0 hx.symm

/-- The formal left and right inverses of `p` with the same constant coefficient coincide. The two
hypotheses together say that `p₁` is invertible, with inverse `r = r ∘ p₁ ∘ s = s`. -/
theorem leftInv_eq_rightInv (p : FormalMultilinearSeries 𝕜 E F) (r : F →L[𝕜] E)
    (hr : Function.LeftInverse r (continuousMultilinearCurryFin1 𝕜 E F (p 1))) (s : F →L[𝕜] E)
    (hs : Function.RightInverse s (continuousMultilinearCurryFin1 𝕜 E F (p 1))) (x : E) :
    leftInv p r hr x = rightInv p s hs x :=
  p.eq_of_comp_eq_id_of_comp_eq_id (leftInv_comp p r hr x) (comp_rightInv p s hs x) (by simp)

/-- If the linear term of `p` has a continuous linear right inverse `s`, then every formal left
inverse of `p` is the formal right inverse constructed from `s`. When the linear term is
invertible, this is the uniqueness of the formal inverse with a given constant coefficient. -/
theorem eq_rightInv_of_comp_eq_id_left (p : FormalMultilinearSeries 𝕜 E F) (s : F →L[𝕜] E)
    (hs : Function.RightInverse s (continuousMultilinearCurryFin1 𝕜 E F (p 1))) {x : E}
    {q : FormalMultilinearSeries 𝕜 F E} (hq : q.comp p = id 𝕜 E x) :
    q = p.rightInv s hs x :=
  p.eq_of_comp_eq_id_of_comp_eq_id hq (comp_rightInv p s hs x) (by simp)

/-- If the linear term of `p` has a continuous linear left inverse `r`, then every formal right
inverse of `p` with constant coefficient `x` is the formal left inverse constructed from `r`. When
the linear term is invertible, this is the uniqueness of the formal inverse with a given constant
coefficient. -/
theorem eq_leftInv_of_comp_eq_id_right (p : FormalMultilinearSeries 𝕜 E F) (r : F →L[𝕜] E)
    (hr : Function.LeftInverse r (continuousMultilinearCurryFin1 𝕜 E F (p 1))) {x : E}
    {q : FormalMultilinearSeries 𝕜 F E} (hq : p.comp q = id 𝕜 F (p 0 0)) (hx : q 0 0 = x) :
    q = p.leftInv r hr x :=
  (p.eq_of_comp_eq_id_of_comp_eq_id (leftInv_comp p r hr x) hq hx).symm

/-- The formal left inverse constructed from `r` is the formal inverse of `r ∘ p`, whose linear
term is the identity, precomposed with `r`. -/
theorem leftInv_eq_rightInv_compFormalMultilinearSeries_compContinuousLinearMap
    (p : FormalMultilinearSeries 𝕜 E F) (r : F →L[𝕜] E)
    (hr : Function.LeftInverse r (continuousMultilinearCurryFin1 𝕜 E F (p 1))) (x : E) :
    p.leftInv r hr x =
      ((r.compFormalMultilinearSeries p).rightInv (ContinuousLinearMap.id 𝕜 E) (fun v ↦ hr v)
        x).compContinuousLinearMap r := by
  have hQ : ((p.leftInv r hr x).compContinuousLinearMap
      (continuousMultilinearCurryFin1 𝕜 E F (p 1))).comp (r.compFormalMultilinearSeries p) =
      id 𝕜 E x := by
    rw [comp_compFormalMultilinearSeries, compContinuousLinearMap_comp,
      leftInv_compContinuousLinearMap, leftInv_comp]
  rw [← eq_rightInv_of_comp_eq_id_left _ _ (fun v ↦ hr v) hQ, compContinuousLinearMap_comp,
    leftInv_compContinuousLinearMap]

/-- The formal left inverse constructed from `r` is the only formal left inverse with constant
coefficient `x` whose coefficients depend on their vector arguments only through their images
under `r`, that is, which is unchanged by precomposition with `p₁ ∘ r`. -/
theorem eq_leftInv_of_comp_eq_id_of_compContinuousLinearMap_eq (p : FormalMultilinearSeries 𝕜 E F)
    (r : F →L[𝕜] E) (hr : Function.LeftInverse r (continuousMultilinearCurryFin1 𝕜 E F (p 1)))
    {x : E} {q : FormalMultilinearSeries 𝕜 F E} (hq : q.comp p = id 𝕜 E x)
    (hq' : q.compContinuousLinearMap ((continuousMultilinearCurryFin1 𝕜 E F (p 1)).comp r) = q) :
    q = p.leftInv r hr x := by
  have hP : Function.RightInverse (ContinuousLinearMap.id 𝕜 E)
      (continuousMultilinearCurryFin1 𝕜 E E ((r.compFormalMultilinearSeries p) 1)) := fun v ↦ hr v
  have hQ : (q.compContinuousLinearMap (continuousMultilinearCurryFin1 𝕜 E F (p 1))).comp
      (r.compFormalMultilinearSeries p) = id 𝕜 E x := by
    rw [comp_compFormalMultilinearSeries, compContinuousLinearMap_comp, hq', hq]
  rw [leftInv_eq_rightInv_compFormalMultilinearSeries_compContinuousLinearMap p r hr x,
    ← eq_rightInv_of_comp_eq_id_left _ _ hP hQ, compContinuousLinearMap_comp, hq']

/-- The formal right inverse constructed from `s` is the only formal right inverse with constant
coefficient `x` whose coefficients of positive order take values in the range of `s`. -/
theorem eq_rightInv_of_comp_eq_id_of_apply_mem_range (p : FormalMultilinearSeries 𝕜 E F)
    (s : F →L[𝕜] E) (hs : Function.RightInverse s (continuousMultilinearCurryFin1 𝕜 E F (p 1)))
    {x : E} {q : FormalMultilinearSeries 𝕜 F E} (hq : p.comp q = id 𝕜 F (p 0 0))
    (hx : q 0 0 = x) (hrange : ∀ n, 0 < n → ∀ v, q n v ∈ Set.range s) :
    q = p.rightInv s hs x := by
  have hproj {y : E} (hy : y ∈ Set.range s) :
      s (continuousMultilinearCurryFin1 𝕜 E F (p 1) y) = y := by
    obtain ⟨w, rfl⟩ := hy
    rw [hs w]
  have heq : p.comp q = p.comp (p.rightInv s hs x) := hq.trans (comp_rightInv p s hs x).symm
  ext1 n
  induction n using Nat.strong_induction_on with | _ n IH
  match n with
  | 0 =>
    ext v
    rw [Subsingleton.elim v 0, hx]
    simp
  | n + 1 =>
    ext v
    have N : 0 < n + 1 := n.succ_pos
    rw [← hproj (hrange _ N v), ← hproj (rightInv_apply_mem_range p s hs x N v)]
    congr 1
    have h1 := congr_arg (fun t : FormalMultilinearSeries 𝕜 F F ↦ t (n + 1) v) heq
    simp only [comp_rightInv_aux1 N] at h1
    have hsum : ∑ c ∈ {c : Composition (n + 1) | 1 < c.length}.toFinset,
          p c.length (q.applyComposition c v) =
        ∑ c ∈ {c : Composition (n + 1) | 1 < c.length}.toFinset,
          p c.length ((p.rightInv s hs x).applyComposition c v) := by
      refine sum_congr rfl fun c hc => p.congr rfl fun j hj1 hj2 => ?_
      have : ∀ k, c.blocksFun k < n + 1 := by
        simp only [Set.mem_toFinset (s := {c : Composition (n + 1) | 1 < c.length}),
          Set.mem_ofPred_eq] at hc
        refine (Composition.ne_single_iff N).1 ?_
        simp [Composition.eq_single_iff_length, ne_of_gt hc]
      simp [applyComposition, IH _ (this _)]
    rw [hsum, add_right_inj] at h1
    simpa [Matrix.vec_single_eq_const] using h1

/-- A formal multilinear series has a formal left inverse, with any prescribed constant
coefficient, if and only if its linear term has a continuous linear left inverse. -/
theorem exists_comp_eq_id_iff_hasLeftInverse (p : FormalMultilinearSeries 𝕜 E F) (x : E) :
    (∃ q : FormalMultilinearSeries 𝕜 F E, q.comp p = id 𝕜 E x) ↔
      (continuousMultilinearCurryFin1 𝕜 E F (p 1)).HasLeftInverse := by
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨continuousMultilinearCurryFin1 𝕜 F E (q 1), fun v ↦ ?_⟩
    have := congr_arg (fun t ↦ t 1 fun _ ↦ v) hq
    simpa [comp_coeff_one, Matrix.vec_single_eq_const] using this
  · rintro ⟨r, hr⟩
    exact ⟨p.leftInv r hr x, leftInv_comp p r hr x⟩

/-- A formal multilinear series has a formal right inverse if and only if its linear term has a
continuous linear right inverse. -/
theorem exists_comp_eq_id_iff_hasRightInverse (p : FormalMultilinearSeries 𝕜 E F) :
    (∃ q : FormalMultilinearSeries 𝕜 F E, p.comp q = id 𝕜 F (p 0 0)) ↔
      (continuousMultilinearCurryFin1 𝕜 E F (p 1)).HasRightInverse := by
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨continuousMultilinearCurryFin1 𝕜 F E (q 1), fun w ↦ ?_⟩
    have := congr_arg (fun t ↦ t 1 fun _ ↦ w) hq
    simpa [comp_coeff_one, Matrix.vec_single_eq_const] using this
  · rintro ⟨s, hs⟩
    exact ⟨p.rightInv s hs 0, comp_rightInv p s hs 0⟩

/-!
### Convergence of the inverse of a power series

Assume that `p` is a convergent multilinear series with invertible linear term `p₁`, and let `q`
be its (left or right) inverse. Using the left-inverse formula gives
$$
q_n = - (p_1)^{-n} \sum_{k=0}^{n-1} \sum_{i_1 + \dotsc + i_k = n} q_k (p_{i_1}, \dotsc, p_{i_k}),
$$
where `(p₁)^{-n}` stands for precomposition with `p₁⁻¹` in each of the `n` variables.
Assume for simplicity that we are in dimension `1` and `p₁ = 1`. In the formula for `qₙ`, the term
`q_{n-1}` appears with a multiplicity of `n-1` (choosing the index `i_j` for which `i_j = 2` while
all the other indices are equal to `1`), which indicates that `qₙ` might grow like `n!`. This is
bad for summability properties.

It turns out that the right-inverse formula is better behaved, and should instead be used for this
kind of estimate. It reads
$$
q_n = - (p_1)^{-1} \sum_{k=2}^n \sum_{i_1 + \dotsc + i_k = n} p_k (q_{i_1}, \dotsc, q_{i_k}).
$$
Here, `q_{n-1}` can only appear in the term with `k = 2`, and it only appears twice, so there is
hope this formula can lead to an at most geometric behavior. For the one-sided inverses
constructed above, `p₁⁻¹` is replaced by the chosen linear inverse `r` or `s`: the estimate below
only uses `s`, and `radius_leftInv_pos_of_radius_pos` reduces left inverses to right inverses.

Let `Qₙ = ‖qₙ‖`. Bounding `‖pₖ‖` with `C r^k` gives an inequality
$$
Q_n ≤ C' \sum_{k=2}^n r^k \sum_{i_1 + \dotsc + i_k = n} Q_{i_1} \dotsm Q_{i_k}.
$$

This formula is not enough to prove by naive induction on `n` a bound of the form `Qₙ ≤ D R^n`.
However, assuming that the inequality above were an equality, one could get a formula for the
generating series of the `Qₙ`:

$$
\begin{align}
Q(z) & := \sum Q_n z^n = Q_1 z + C' \sum_{2 \leq k \leq n} \sum_{i_1 + \dotsc + i_k = n}
  (r z^{i_1} Q_{i_1}) \dotsm (r z^{i_k} Q_{i_k})
\\ & = Q_1 z + C' \sum_{k = 2}^\infty (\sum_{i_1 \geq 1} r z^{i_1} Q_{i_1})
  \dotsm (\sum_{i_k \geq 1} r z^{i_k} Q_{i_k})
\\ & = Q_1 z + C' \sum_{k = 2}^\infty (r Q(z))^k
= Q_1 z + C' (r Q(z))^2 / (1 - r Q(z)).
\end{align}
$$

One can solve this formula explicitly. The solution is analytic in a neighborhood of `0` in `ℂ`,
hence its coefficients grow at most geometrically (by a contour integral argument), and therefore
the original `Qₙ`, which are bounded by these ones, are also at most geometric.

This classical argument is not really satisfactory, as it requires an a priori bound on a complex
analytic function. Another option would be to compute explicitly its terms (with binomial
coefficients) to obtain an explicit geometric bound, but this would be very painful.

Instead, we will use the above intuition, but in a slightly different form, with finite sums and an
induction. I learnt this trick in [poeschel2017siegelsternberg]. Let
$S_n = \sum_{k=1}^n Q_k a^k$ (where `a` is a positive real parameter to be chosen suitably small).
The above computation but with finite sums shows that

$$
S_n \leq Q_1 a + C' \sum_{k=2}^n (r S_{n-1})^k.
$$

In particular, $S_n \leq Q_1 a + C' (r S_{n-1})^2 / (1- r S_{n-1})$.
Assume that $S_{n-1} \leq K a$, where `K > Q₁` is fixed and `a` is small enough so that
`r K a ≤ 1/2` (to control the denominator). Then this equation gives a bound
$S_n \leq Q_1 a + 2 C' r^2 K^2 a^2$.
If `a` is small enough, this is bounded by `K a` as the second term is quadratic in `a`, and
therefore negligible.

By induction, we deduce `Sₙ ≤ K a` for all `n`, which gives in particular the fact that `aⁿ Qₙ`
remains bounded.
-/


/-- First technical lemma to control the growth of coefficients of the inverse. Bound the explicit
expression for `∑_{k<n+1} aᵏ Qₖ` in terms of a sum of powers of the same sum one step before,
in a general abstract setup. -/
theorem radius_right_inv_pos_of_radius_pos_aux1 (n : ℕ) (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) {r a : ℝ}
    (hr : 0 ≤ r) (ha : 0 ≤ a) :
    ∑ k ∈ Ico 2 (n + 1),
        a ^ k *
          ∑ c ∈ ({c | 1 < Composition.length c}.toFinset : Finset (Composition k)),
            r ^ c.length * ∏ j, p (c.blocksFun j) ≤
      ∑ j ∈ Ico 2 (n + 1), r ^ j * (∑ k ∈ Ico 1 n, a ^ k * p k) ^ j :=
  calc
    ∑ k ∈ Ico 2 (n + 1),
          a ^ k *
            ∑ c ∈ ({c | 1 < Composition.length c}.toFinset : Finset (Composition k)),
              r ^ c.length * ∏ j, p (c.blocksFun j) =
        ∑ k ∈ Ico 2 (n + 1),
          ∑ c ∈ ({c | 1 < Composition.length c}.toFinset : Finset (Composition k)),
            ∏ j, r * (a ^ c.blocksFun j * p (c.blocksFun j)) := by
      simp_rw [mul_sum]
      congr! with k _ c
      rw [prod_mul_distrib, prod_mul_distrib, prod_pow_eq_pow_sum, Composition.sum_blocksFun,
        prod_const, card_fin]
      ring
    _ ≤
        ∑ d ∈ compPartialSumTarget 2 (n + 1) n,
          ∏ j : Fin d.2.length, r * (a ^ d.2.blocksFun j * p (d.2.blocksFun j)) := by
      rw [sum_sigma']
      gcongr
      · intro x _ _
        exact prod_nonneg fun j _ ↦ (by positivity [ha, hp (x.snd.blocksFun j)])
      rintro ⟨k, c⟩ hd
      simp only [Set.mem_toFinset (s := {c | 1 < Composition.length c}), mem_Ico, mem_sigma,
        Set.mem_ofPred_eq] at hd
      simp only [mem_compPartialSumTarget_iff]
      refine ⟨hd.2, c.length_le.trans_lt hd.1.2, fun j => ?_⟩
      have : c ≠ Composition.single k (zero_lt_two.trans_le hd.1.1) := by
        simp [Composition.eq_single_iff_length, ne_of_gt hd.2]
      rw [Composition.ne_single_iff] at this
      exact (this j).trans_le (Nat.lt_succ_iff.mp hd.1.2)
    _ = ∑ e ∈ compPartialSumSource 2 (n + 1) n, ∏ j : Fin e.1, r * (a ^ e.2 j * p (e.2 j)) := by
      symm
      apply compChangeOfVariables_sum
      rintro ⟨k, blocksFun⟩ H
      have K : (compChangeOfVariables 2 (n + 1) n ⟨k, blocksFun⟩ H).snd.length = k := by simp
      congr 2 <;> try rw [K]
      rw [Fin.heq_fun_iff K.symm]
      intro j
      rw [compChangeOfVariables_blocksFun]
    _ = ∑ j ∈ Ico 2 (n + 1), r ^ j * (∑ k ∈ Ico 1 n, a ^ k * p k) ^ j := by
      rw [compPartialSumSource,
        ← sum_sigma' (Ico 2 (n + 1))
          (fun k : ℕ => (Fintype.piFinset fun _ : Fin k => Ico 1 n : Finset (Fin k → ℕ)))
          (fun n e => ∏ j : Fin n, r * (a ^ e j * p (e j)))]
      congr! with j
      simp only [← @MultilinearMap.mkPiAlgebra_apply ℝ (Fin j) _ ℝ]
      simp only [←
        MultilinearMap.map_sum_finset (MultilinearMap.mkPiAlgebra ℝ (Fin j) ℝ) fun _ (m : ℕ) =>
          r * (a ^ m * p m)]
      simp only [MultilinearMap.mkPiAlgebra_apply]
      simp [prod_const, ← mul_sum, mul_pow]

/-- Second technical lemma to control the growth of coefficients of the inverse. Bound the explicit
expression for `∑_{k<n+1} aᵏ Qₖ` in terms of a sum of powers of the same sum one step before,
in the specific setup we are interesting in, by reducing to the general bound in
`radius_rightInv_pos_of_radius_pos_aux1`. -/
theorem radius_rightInv_pos_of_radius_pos_aux2 {x : E} {n : ℕ} (hn : 2 ≤ n + 1)
    (p : FormalMultilinearSeries 𝕜 E F) (s : F →L[𝕜] E)
    (hs : Function.RightInverse s (continuousMultilinearCurryFin1 𝕜 E F (p 1))) {r a C : ℝ}
    (hr : 0 ≤ r) (ha : 0 ≤ a) (hC : 0 ≤ C) (hp : ∀ n, ‖p n‖ ≤ C * r ^ n) :
    ∑ k ∈ Ico 1 (n + 1), a ^ k * ‖p.rightInv s hs x k‖ ≤
      ‖s‖ * a +
        ‖s‖ * C *
          ∑ k ∈ Ico 2 (n + 1), (r * ∑ j ∈ Ico 1 n, a ^ j * ‖p.rightInv s hs x j‖) ^ k :=
  let I := ‖s‖
  calc
    ∑ k ∈ Ico 1 (n + 1), a ^ k * ‖p.rightInv s hs x k‖ =
        a * I + ∑ k ∈ Ico 2 (n + 1), a ^ k * ‖p.rightInv s hs x k‖ := by
      simp only [I, LinearIsometryEquiv.norm_map, pow_one, rightInv_coeff_one,
        show Ico (1 : ℕ) 2 = {1} from Nat.Ico_succ_singleton 1,
        sum_singleton, ← sum_Ico_consecutive _ one_le_two hn]
    _ =
        a * I +
          ∑ k ∈ Ico 2 (n + 1),
            a ^ k *
              ‖s.compContinuousMultilinearMap
                  (∑ c ∈ ({c | 1 < Composition.length c}.toFinset : Finset (Composition k)),
                    p.compAlongComposition (p.rightInv s hs x) c)‖ := by
      congr! 2 with j hj
      rw [rightInv_coeff _ _ _ _ _ (mem_Ico.1 hj).1, norm_neg]
    _ ≤
        a * ‖s‖ +
          ∑ k ∈ Ico 2 (n + 1),
            a ^ k *
              (I *
                ∑ c ∈ ({c | 1 < Composition.length c}.toFinset : Finset (Composition k)),
                  C * r ^ c.length * ∏ j, ‖p.rightInv s hs x (c.blocksFun j)‖) := by
      gcongr with j
      apply (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans
      gcongr
      apply (norm_sum_le _ _).trans
      gcongr
      apply (compAlongComposition_norm _ _ _).trans
      gcongr
      apply hp
    _ = I * a + I * C * ∑ k ∈ Ico 2 (n + 1), a ^ k *
          ∑ c ∈ ({c | 1 < Composition.length c}.toFinset : Finset (Composition k)),
            r ^ c.length * ∏ j, ‖p.rightInv s hs x (c.blocksFun j)‖ := by
      simp_rw [I, mul_assoc C, ← mul_sum, ← mul_assoc, mul_comm _ ‖s‖,
        mul_assoc, ← mul_sum, ← mul_assoc, mul_comm _ C, mul_assoc, ← mul_sum]
      ring
    _ ≤ I * a + I * C *
        ∑ k ∈ Ico 2 (n + 1), (r * ∑ j ∈ Ico 1 n, a ^ j * ‖p.rightInv s hs x j‖) ^ k := by
      gcongr _ + _ * _ * ?_
      simp_rw [mul_pow]
      apply
        radius_right_inv_pos_of_radius_pos_aux1 n (fun k => ‖p.rightInv s hs x k‖)
          (fun k => norm_nonneg _) hr ha

/-- If a formal multilinear series has a positive radius of convergence, then so does its formal
right inverse `p.rightInv s hs x`. When the linear term of `p` is not invertible, other formal right
inverses of `p` can have radius zero. -/
theorem radius_rightInv_pos_of_radius_pos
    {p : FormalMultilinearSeries 𝕜 E F} {s : F →L[𝕜] E}
    {hs : Function.RightInverse s (continuousMultilinearCurryFin1 𝕜 E F (p 1))} {x : E}
    (hp : 0 < p.radius) : 0 < (p.rightInv s hs x).radius := by
  obtain ⟨C, r, Cpos, rpos, ple⟩ :
    ∃ (C r : _) (_ : 0 < C) (_ : 0 < r), ∀ n : ℕ, ‖p n‖ ≤ C * r ^ n :=
    le_mul_pow_of_radius_pos p hp
  let I := ‖s‖
  -- choose `a` small enough to make sure that `∑_{k ≤ n} aᵏ Qₖ` will be controllable by
  -- induction
  obtain ⟨a, apos, ha1, ha2⟩ :
    ∃ (a : _) (apos : 0 < a),
      2 * I * C * r ^ 2 * (I + 1) ^ 2 * a ≤ 1 ∧ r * (I + 1) * a ≤ 1 / 2 := by
    have :
      Tendsto (fun a => 2 * I * C * r ^ 2 * (I + 1) ^ 2 * a) (𝓝 0)
        (𝓝 (2 * I * C * r ^ 2 * (I + 1) ^ 2 * 0)) :=
      tendsto_const_nhds.mul tendsto_id
    have A : ∀ᶠ a in 𝓝 0, 2 * I * C * r ^ 2 * (I + 1) ^ 2 * a < 1 := by
      apply (tendsto_order.1 this).2; simp [zero_lt_one]
    have : Tendsto (fun a => r * (I + 1) * a) (𝓝 0) (𝓝 (r * (I + 1) * 0)) :=
      tendsto_const_nhds.mul tendsto_id
    have B : ∀ᶠ a in 𝓝 0, r * (I + 1) * a < 1 / 2 := by
      apply (tendsto_order.1 this).2; simp
    have C : ∀ᶠ a in 𝓝[>] (0 : ℝ), (0 : ℝ) < a := by
      filter_upwards [self_mem_nhdsWithin] with _ ha using ha
    rcases (C.and ((A.and B).filter_mono inf_le_left)).exists with ⟨a, ha⟩
    exact ⟨a, ha.1, ha.2.1.le, ha.2.2.le⟩
  -- check by induction that the partial sums are suitably bounded, using the choice of `a` and the
  -- inductive control from Lemma `radius_rightInv_pos_of_radius_pos_aux2`.
  let S n := ∑ k ∈ Ico 1 n, a ^ k * ‖p.rightInv s hs x k‖
  have IRec : ∀ n, 1 ≤ n → S n ≤ (I + 1) * a := by
    apply Nat.le_induction
    · simp only [S]
      rw [Ico_eq_empty_of_le (le_refl 1), sum_empty]
      positivity
    · intro n one_le_n hn
      have In : 2 ≤ n + 1 := by lia
      have rSn : r * S n ≤ 1 / 2 :=
        calc
          r * S n ≤ r * ((I + 1) * a) := by gcongr
          _ ≤ 1 / 2 := by rwa [← mul_assoc]
      calc
        S (n + 1) ≤ I * a + I * C * ∑ k ∈ Ico 2 (n + 1), (r * S n) ^ k :=
          radius_rightInv_pos_of_radius_pos_aux2 In p s hs rpos.le apos.le Cpos.le ple
        _ = I * a + I * C * (((r * S n) ^ 2 - (r * S n) ^ (n + 1)) / (1 - r * S n)) := by
          rw [geom_sum_Ico' _ In]; exact ne_of_lt (rSn.trans_lt (by norm_num))
        _ ≤ I * a + I * C * ((r * S n) ^ 2 / (1 / 2)) := by
          gcongr
          · simp only [sub_le_self_iff]
            positivity
          · linarith only [rSn]
        _ = I * a + 2 * I * C * (r * S n) ^ 2 := by ring
        _ ≤ I * a + 2 * I * C * (r * ((I + 1) * a)) ^ 2 := by gcongr
        _ = (I + 2 * I * C * r ^ 2 * (I + 1) ^ 2 * a) * a := by ring
        _ ≤ (I + 1) * a := by gcongr
  -- conclude that all coefficients satisfy `aⁿ Qₙ ≤ (I + 1) a`.
  let a' : NNReal := ⟨a, apos.le⟩
  suffices H : (a' : ENNReal) ≤ (p.rightInv s hs x).radius by
    apply lt_of_lt_of_le _ H
    -- Prior to https://github.com/leanprover/lean4/pull/2734, this was `exact_mod_cast apos`.
    simpa only [ENNReal.coe_pos]
  apply le_radius_of_eventually_le _ ((I + 1) * a)
  filter_upwards [Ici_mem_atTop 1] with n (hn : 1 ≤ n)
  calc
    ‖p.rightInv s hs x n‖ * (a' : ℝ) ^ n = a ^ n * ‖p.rightInv s hs x n‖ := mul_comm _ _
    _ ≤ ∑ k ∈ Ico 1 (n + 1), a ^ k * ‖p.rightInv s hs x k‖ :=
      (haveI : ∀ k ∈ Ico 1 (n + 1), 0 ≤ a ^ k * ‖p.rightInv s hs x k‖ := fun k _ => by positivity
      single_le_sum this (by simp [hn]))
    _ ≤ (I + 1) * a := IRec (n + 1) (by simp)

/-- If a formal multilinear series has a positive radius of convergence, then so does its formal
left inverse `p.leftInv r hr x`: by
`leftInv_eq_rightInv_compFormalMultilinearSeries_compContinuousLinearMap`, it is a formal right
inverse of `r ∘ p` precomposed with `r`. When the linear term of `p` is not invertible, other
formal left inverses of `p` can have radius zero. -/
theorem radius_leftInv_pos_of_radius_pos
    {p : FormalMultilinearSeries 𝕜 E F} {r : F →L[𝕜] E}
    {hr : Function.LeftInverse r (continuousMultilinearCurryFin1 𝕜 E F (p 1))} {x : E}
    (hp : 0 < p.radius) : 0 < (p.leftInv r hr x).radius := by
  rw [leftInv_eq_rightInv_compFormalMultilinearSeries_compContinuousLinearMap p r hr x]
  have hQ_pos : 0 < ((r.compFormalMultilinearSeries p).rightInv (ContinuousLinearMap.id 𝕜 E)
      (fun v ↦ hr v) x).radius :=
    radius_rightInv_pos_of_radius_pos (hp.trans_le (p.radius_le_radius_continuousLinearMap_comp r))
  exact (ENNReal.div_pos hQ_pos.ne' enorm_ne_top).trans_le
    (div_le_radius_compContinuousLinearMap _ r)

end FormalMultilinearSeries

/-!
### The inverse of an analytic open partial homeomorphism is analytic
-/

open FormalMultilinearSeries

lemma HasFPowerSeriesAt.tendsto_partialSum_prod_of_comp
    {f : E → G} {q : FormalMultilinearSeries 𝕜 F G}
    {p : FormalMultilinearSeries 𝕜 E F} {x : E}
    (hf : HasFPowerSeriesAt f (q.comp p) x) (hq : 0 < q.radius) (hp : 0 < p.radius) :
    ∀ᶠ y in 𝓝 0, Tendsto (fun (a : ℕ × ℕ) ↦ q.partialSum a.1 (p.partialSum a.2 y
      - p 0 (fun _ ↦ 0))) atTop (𝓝 (f (x + y))) := by
  rcases hf with ⟨r0, h0⟩
  rcases q.comp_summable_nnreal p hq hp with ⟨r1, r1_pos : 0 < r1, hr1⟩
  let r : ℝ≥0∞ := min r0 r1
  have : Metric.eball (0 : E) r ∈ 𝓝 0 :=
    Metric.eball_mem_nhds 0 (lt_min h0.r_pos (by exact_mod_cast r1_pos))
  filter_upwards [this] with y hy
  have hy0 : y ∈ Metric.eball 0 r0 := Metric.eball_subset_eball (min_le_left _ _) hy
  have A : HasSum (fun i : Σ n, Composition n => q.compAlongComposition p i.2 fun _j => y)
      (f (x + y)) := by
    have cau : CauchySeq fun s : Finset (Σ n, Composition n) =>
        ∑ i ∈ s, q.compAlongComposition p i.2 fun _j => y := by
      apply cauchySeq_finset_of_norm_bounded (NNReal.summable_coe.2 hr1) _
      simp only [coe_nnnorm, NNReal.coe_mul, NNReal.coe_pow]
      rintro ⟨n, c⟩
      calc
        ‖(compAlongComposition q p c) fun _j : Fin n => y‖ ≤
            ‖compAlongComposition q p c‖ * ∏ _j : Fin n, ‖y‖ := by
          apply ContinuousMultilinearMap.le_opNorm
        _ ≤ ‖compAlongComposition q p c‖ * (r1 : ℝ) ^ n := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          rw [Finset.prod_const, Finset.card_fin]
          gcongr
          rw [Metric.mem_eball, edist_zero_right] at hy
          have := le_trans (le_of_lt hy) (min_le_right _ _)
          rwa [enorm_le_coe, ← NNReal.coe_le_coe, coe_nnnorm] at this
    apply HasSum.of_sigma (fun b ↦ hasSum_fintype _) ?_ cau
    simpa [FormalMultilinearSeries.comp] using h0.hasSum hy0
  have B : Tendsto (fun (n : ℕ × ℕ) => ∑ i ∈ compPartialSumTarget 0 n.1 n.2,
      q.compAlongComposition p i.2 fun _j => y) atTop (𝓝 (f (x + y))) := by
    apply Tendsto.comp A compPartialSumTarget_tendsto_prod_atTop
  have C : Tendsto (fun (n : ℕ × ℕ) => q.partialSum n.1 (∑ a ∈ Finset.Ico 1 n.2, p a fun _b ↦ y))
      atTop (𝓝 (f (x + y))) := by simpa [comp_partialSum] using B
  apply C.congr'
  filter_upwards [Ici_mem_atTop (0, 1)]
  rintro ⟨-, n⟩ ⟨-, (hn : 1 ≤ n)⟩
  congr
  rw [partialSum, eq_sub_iff_add_eq', Finset.range_eq_Ico,
        Finset.sum_eq_sum_Ico_succ_bot hn]
  congr with i
  exact i.elim0

lemma HasFPowerSeriesAt.eventually_hasSum_of_comp {f : E → F} {g : F → G}
    {q : FormalMultilinearSeries 𝕜 F G} {p : FormalMultilinearSeries 𝕜 E F} {x : E}
    (hgf : HasFPowerSeriesAt (g ∘ f) (q.comp p) x) (hf : HasFPowerSeriesAt f p x)
    (hq : 0 < q.radius) :
    ∀ᶠ y in 𝓝 0, HasSum (fun n : ℕ => q n fun _ : Fin n => (f (x + y) - f x)) (g (f (x + y))) := by
  have : ∀ᶠ y in 𝓝 (0 : E), f (x + y) - f x ∈ Metric.eball 0 q.radius := by
    have A : ContinuousAt (fun y ↦ f (x + y) - f x) 0 := by
      apply ContinuousAt.sub _ continuousAt_const
      exact hf.continuousAt.comp_of_eq (by fun_prop) (by simp)
    have B : Metric.eball 0 q.radius ∈ 𝓝 (f (x + 0) - f x) := by
      simpa using Metric.eball_mem_nhds _ hq
    exact A.preimage_mem_nhds B
  filter_upwards [hgf.tendsto_partialSum_prod_of_comp hq (hf.radius_pos),
    hf.tendsto_partialSum, this] with y hy h'y h''y
  have L : Tendsto (fun n ↦ q.partialSum n (f (x + y) - f x)) atTop (𝓝 (g (f (x + y)))) := by
    apply (closed_nhds_basis (g (f (x + y)))).tendsto_right_iff.2
    rintro u ⟨hu, u_closed⟩
    simp only [id_eq, eventually_atTop]
    rcases mem_nhds_iff.1 hu with ⟨v, vu, v_open, hv⟩
    obtain ⟨a₀, b₀, hab⟩ : ∃ a₀ b₀, ∀ (a b : ℕ), a₀ ≤ a → b₀ ≤ b →
        q.partialSum a (p.partialSum b y - (p 0) fun _ ↦ 0) ∈ v := by
      simpa using hy (v_open.mem_nhds hv)
    refine ⟨a₀, fun a ha ↦ ?_⟩
    have : Tendsto (fun b ↦ q.partialSum a (p.partialSum b y - (p 0) fun _ ↦ 0)) atTop
        (𝓝 (q.partialSum a (f (x + y) - f x))) := by
      have : ContinuousAt (q.partialSum a) (f (x + y) - f x) :=
        (partialSum_continuous q a).continuousAt
      apply this.tendsto.comp
      apply Tendsto.sub h'y
      convert! tendsto_const_nhds
      exact (HasFPowerSeriesAt.coeff_zero hf fun _ ↦ 0).symm
    apply u_closed.mem_of_tendsto this
    filter_upwards [Ici_mem_atTop b₀] with b hb using vu (hab _ _ ha hb)
  have C : CauchySeq (fun (s : Finset ℕ) ↦ ∑ n ∈ s, q n fun _ : Fin n => (f (x + y) - f x)) := by
    have Z := q.summable_norm_apply (x := f (x + y) - f x) h''y
    exact cauchySeq_finset_of_norm_bounded Z (fun i ↦ le_rfl)
  exact tendsto_nhds_of_cauchySeq_of_subseq C tendsto_finset_range L

/-- If an open partial homeomorphism `f` is defined at `a` and has a power series expansion `p`
there whose linear term has a continuous linear left inverse `r`, then `f.symm` has a power series
expansion at `f a`, given by the formal left inverse `p.leftInv r hr a`.

Only a left inverse is assumed; the chain rule applied to `f ∘ f.symm`, the identity near `f a`,
then shows that `r` is also a right inverse of the linear term. -/
theorem OpenPartialHomeomorph.hasFPowerSeriesAt_symm (f : OpenPartialHomeomorph E F) {a : E}
    (h0 : a ∈ f.source) {p : FormalMultilinearSeries 𝕜 E F} (h : HasFPowerSeriesAt f p a)
    {r : F →L[𝕜] E} (hr : Function.LeftInverse r (continuousMultilinearCurryFin1 𝕜 E F (p 1))) :
    HasFPowerSeriesAt f.symm (p.leftInv r hr a) (f a) := by
  have A : HasFPowerSeriesAt (f.symm ∘ f) ((p.leftInv r hr a).comp p) a := by
    have : HasFPowerSeriesAt (ContinuousLinearMap.id 𝕜 E) ((p.leftInv r hr a).comp p) a := by
      rw [leftInv_comp]
      exact (ContinuousLinearMap.id 𝕜 E).hasFPowerSeriesAt a
    apply this.congr
    filter_upwards [f.open_source.mem_nhds h0] with x hx using by simp [hx]
  have B : ∀ᶠ (y : E) in 𝓝 0, HasSum (fun n ↦ (p.leftInv r hr a n) fun _ ↦ f (a + y) - f a)
      (f.symm (f (a + y))) := by
    simpa using! A.eventually_hasSum_of_comp h (radius_leftInv_pos_of_radius_pos h.radius_pos)
  have C : ∀ᶠ (y : E) in 𝓝 a, HasSum (fun n ↦ (p.leftInv r hr a n) fun _ ↦ f y - f a)
      (f.symm (f y)) := by
    rw [← sub_eq_zero_of_eq (a := a) rfl] at B
    have : ContinuousAt (fun x ↦ x - a) a := by fun_prop
    simpa using! this.preimage_mem_nhds B
  have D : ∀ᶠ (y : E) in 𝓝 (f.symm (f a)),
      HasSum (fun n ↦ (p.leftInv r hr a n) fun _ ↦ f y - f a) y := by
    simp only [h0, OpenPartialHomeomorph.left_inv]
    filter_upwards [C, f.open_source.mem_nhds h0] with x hx h'x
    simpa [h'x] using! hx
  have E : ∀ᶠ z in 𝓝 (f a), HasSum (fun n ↦ (p.leftInv r hr a n) fun _ ↦ f (f.symm z) - f a)
      (f.symm z) := by
    have : ContinuousAt f.symm (f a) := f.continuousAt_symm (f.map_source h0)
    exact this D
  have F : ∀ᶠ z in 𝓝 (f a), HasSum (fun n ↦ (p.leftInv r hr a n) fun _ ↦ z - f a)
      (f.symm z) := by
    filter_upwards [f.open_target.mem_nhds (f.map_source h0), E] with z hz h'z
    simpa [hz] using! h'z
  rcases EMetric.mem_nhds_iff.1 F with ⟨ρ, ρ_pos, hρ⟩
  refine ⟨min ρ (p.leftInv r hr a).radius, min_le_right _ _,
    lt_min ρ_pos (radius_leftInv_pos_of_radius_pos h.radius_pos), fun {y} hy ↦ ?_⟩
  have : y + f a ∈ Metric.eball (f a) ρ := by
    simp only [Metric.mem_eball, edist_eq_enorm_sub, sub_zero, lt_min_iff,
      add_sub_cancel_right] at hy ⊢
    exact hy.1
  simpa [add_comm] using! hρ this
