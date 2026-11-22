/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
public import Mathlib.Analysis.PSeries
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Convergence of `p`-series on lattices

Let `E` be a finite dimensional normed `ℝ`-space, and `L` a discrete subgroup of `E` of rank `d`.
We show that `∑ z ∈ L, z ≠ x, ‖z - x‖ʳ` is convergent for `r < -d`.

## Main results
- `ZLattice.summable_norm_rpow`: `∑ z ∈ L, z ≠ 0, ‖z‖ʳ` converges when `r < -d`.
- `ZLattice.summable_norm_sub_rpow`: `∑ z ∈ L, z ≠ x, ‖z - x‖ʳ` converges when `r < -d`.
- `ZLattice.tsum_norm_rpow_le`:
  `∑ z ∈ L, z ≠ 0, ‖z‖ʳ ≤ Aʳ * ∑ k : ℕ, (k + 1)ᵈ⁺ʳ⁻¹` for some `A > 0`
  depending only on `L`.

-/

@[expose] public section

noncomputable section

open Module

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E] {L : Submodule ℤ E} [DiscreteTopology L]
variable {ι : Type*} (b : Basis ι ℤ L)

namespace ZLattice

lemma exists_forall_abs_repr_le_norm :
    ∃ (ε : ℝ), 0 < ε ∧ ∀ (x : L), ∀ i, ε * |b.repr x i| ≤ ‖x‖ := by
  wlog H : IsZLattice ℝ L
  · let E' := Submodule.span ℝ (L : Set E)
    let L' : Submodule ℤ E' := ZLattice.comap ℝ L E'.subtype
    have inst : DiscreteTopology L' :=
      comap_discreteTopology _ _ (by fun_prop) Subtype.val_injective
    let e : L' ≃ₗ[ℤ] L := Submodule.comapSubtypeEquivOfLe (p := L) (q := E'.restrictScalars ℤ)
      Submodule.subset_span
    have inst : IsZLattice ℝ L' :=
      ⟨Submodule.map_injective_of_injective E'.subtype_injective (by simp [E', L'])⟩
    obtain ⟨ε, hε, H⟩ := this (b.map e.symm) inst
    exact ⟨ε, hε, fun x i ↦ by simpa using! H ⟨⟨x.1, Submodule.subset_span x.2⟩, x.2⟩ i⟩
  have : Finite ι := Module.Finite.finite_basis b
  let b' : Basis ι ℝ E := Basis.ofZLatticeBasis ℝ L b
  let e := ((b'.repr ≪≫ₗ Finsupp.linearEquivFunOnFinite _ _ _).toContinuousLinearEquiv (𝕜 := ℝ))
  have := e.continuous.1 (Set.univ.pi fun _ ↦ Set.Ioo (-1) 1)
    (isOpen_set_pi Set.finite_univ fun _ _ ↦ isOpen_Ioo)
  obtain ⟨ε, hε, hε'⟩ := Metric.isOpen_iff.mp this 0 (by simp)
  refine ⟨ε / 2, by positivity, fun x i ↦ ?_⟩
  by_cases hx : x = 0
  · simp [hx]
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hx : ‖x‖ ≠ 0 := hxpos.ne'
  have hscaled : (ε / 2) • ‖x‖⁻¹ • (x : E) ∈ Metric.ball (0 : E) ε := by
    rw [Metric.mem_ball, dist_zero_right, norm_smul, norm_smul, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos (by positivity : 0 < ε / 2),
      abs_of_pos (inv_pos_of_pos hxpos)]
    have hcancel : ‖x‖⁻¹ * ‖(x : E)‖ = 1 := by rw [Submodule.norm_coe, inv_mul_cancel₀]
    rw [hcancel, mul_one]
    exact half_lt_self hε
  have : |ε / 2 * (‖↑x‖⁻¹ * (b.repr x) i)| < 1 := by
    simpa [e, b', ← abs_lt] using! @hε' ((ε / 2) • ‖x‖⁻¹ • x) hscaled i trivial
  rw [abs_mul, abs_mul, abs_of_pos (inv_pos_of_pos hxpos),
    abs_of_pos (by positivity : 0 < ε / 2), mul_left_comm, inv_mul_lt_iff₀ hxpos,
    mul_one, ← Int.cast_abs] at this
  exact this.le

/--
Given a basis of a (possibly not full rank) `ℤ`-lattice, there exists a `ε > 0` such that
`|b.repr x i| < n` for all `‖x‖ < n * ε` (i.e. `b.repr x i = O(x)` depending only on `b`).
This is an arbitrary choice of such an `ε`.
-/
def normBound {ι : Type*} (b : Basis ι ℤ L) : ℝ :=
  (exists_forall_abs_repr_le_norm b).choose

lemma normBound_pos {ι : Type*} (b : Basis ι ℤ L) : 0 < normBound b :=
  (exists_forall_abs_repr_le_norm b).choose_spec.1

lemma normBound_spec {ι : Type*} (b : Basis ι ℤ L) (x : L) (i : ι) :
    normBound b * |b.repr x i| ≤ ‖x‖ :=
  (exists_forall_abs_repr_le_norm b).choose_spec.2 x i

lemma abs_repr_le {ι : Type*} (b : Basis ι ℤ L) (x : L) (i : ι) :
    |b.repr x i| ≤ Checked.inv (normBound b) (normBound_pos b).ne'.isUnit * ‖x‖ := by
  rw [le_inv_mul_iff₀ (normBound_pos b)]
  exact normBound_spec b x i

lemma abs_repr_lt_of_norm_lt {ι : Type*} (b : Basis ι ℤ L) (x : L) (n : ℕ)
    (hxn : ‖x‖ < normBound b * n) (i : ι) : |b.repr x i| < n := by
  refine Int.cast_lt.mp ((abs_repr_le b x i).trans_lt ?_)
  rwa [inv_mul_lt_iff₀ (normBound_pos b)]

lemma le_norm_of_le_abs_repr {ι : Type*} (b : Basis ι ℤ L) (x : L) (n : ℕ) (i : ι)
    (hi : n ≤ |b.repr x i|) : normBound b * n ≤ ‖x‖ := by
  contrapose! hi
  exact abs_repr_lt_of_norm_lt b x n hi i

open Finset in
lemma sum_piFinset_Icc_rpow_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℤ L) {d : ℕ} (hd : d = Fintype.card ι)
    (n : ℕ) (r : ℝ) (hr : r < -d) :
    ∑ p ∈ (Fintype.piFinset fun _ : ι ↦ Icc (-n : ℤ) n).erase 0, ‖∑ i, p i • b i‖ ^ r ≤
      2 * d * 3 ^ (d - 1) * normBound b ^ r * ∑' k : ℕ, ((k : ℝ) + 1) ^ (d - 1 + r) := by
  let s (n : ℕ) := Fintype.piFinset fun i : ι ↦ Icc (-n : ℤ) n
  subst hd
  set d := Fintype.card ι
  have hr' : r < 0 := hr.trans_le (by linarith)
  by_cases hd : d = 0
  · let : IsEmpty ι := Fintype.card_eq_zero_iff.mp hd
    have hzero : (s n).erase 0 = ∅ := by
      ext p
      simp [Subsingleton.elim p (0 : ι → ℤ)]
    change (∑ p ∈ (s n).erase 0, ‖∑ i, p i • b i‖ ^ r) ≤ _
    simp only [hzero, Finset.sum_empty, hd, Nat.cast_zero, mul_zero, zero_mul, le_refl]
  replace hd : 1 ≤ d := by rwa [Nat.one_le_iff_ne_zero]
  have hs0 : s 0 = {0} := by ext; simp [s, funext_iff]
  have hs {a b : ℕ} (ha : a ≤ b) : s a ⊆ s b := by grind
  have hse : Monotone fun n ↦ (s n).erase 0 := fun _ _ h ↦ erase_subset_erase _ (hs h)
  have hse0 : (s 0).erase 0 = ∅ := by simp [hs0]
  have hsdiff (k : ℕ) : (s (k + 1)).erase 0 \ (s k).erase 0 = s (k + 1) \ s k := by
    ext p
    by_cases h : p = 0
    · subst p
      simp [s]
    · simp [h]
  have (k : ℕ) : #(s (k + 1) \ s k) ≤ 2 * d * (2 * k + 3) ^ (d - 1) := by
    simp only [le_add_iff_nonneg_right, zero_le, hs, card_sdiff_of_subset, s, Fintype.card_piFinset,
      Int.card_Icc, prod_const]
    grind [abs_pow_sub_pow_le (α := ℤ) (2 * k + 3) (2 * k + 1) d]
  let ε := normBound b
  have hε : 0 < ε := normBound_pos b
  calc ∑ p ∈ (s n).erase 0, ‖∑ i, p i • b i‖ ^ r
      = ∑ k ∈ range n, ∑ p ∈ (s (k + 1) \ s k), ‖∑ i, p i • b i‖ ^ r := by
        simp only [Finset.sum_eq_sum_range_sdiff _ hse, hse0, sum_empty, zero_add, hsdiff]
    _ ≤ ∑ k ∈ range n, ∑ p ∈ (s (k + 1) \ s k), ((k + 1) * ε) ^ r := by
        gcongr ∑ k ∈ Finset.range n, ∑ p ∈ (s (k + 1) \ s k), ?_ with k hk v hv
        rw [← Nat.cast_one, ← Nat.cast_add]
        refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ hr'.le
        obtain ⟨j, hj⟩ : ∃ i, v i ∉ Icc (-k : ℤ) k := by simpa [s] using (mem_sdiff.mp hv).2
        refine mul_comm _ ε ▸ le_norm_of_le_abs_repr b _ _ j ?_
        suffices ↑k + 1 ≤ |v j| by simpa [Finsupp.single_apply] using this
        by_contra! H
        rw [Int.lt_add_one_iff, abs_le, ← Finset.mem_Icc] at H
        exact hj H
    _ ≤ ∑ k ∈ range n, ↑(2 * d * (3 * (k + 1)) ^ (d - 1)) * ((k + 1) * ε) ^ r := by
        simp only [sum_const, nsmul_eq_mul]
        gcongr with k hk
        refine (this _).trans ?_
        gcongr
        lia
    _ = 2 * d * 3 ^ (d - 1) * ε ^ r * ∑ k ∈ range n, (k + 1) ^ (d - 1) * (k + 1 : ℝ) ^ r := by
        simp_rw [Finset.mul_sum]
        congr with k
        push_cast
        rw [Real.mul_rpow (by positivity) (by positivity), mul_pow]
        group
    _ = 2 * d * 3 ^ (d - 1) * ε ^ r * ∑ k ∈ range n, (↑(k + 1) : ℝ) ^ (d - 1 + r) := by
        congr with k
        rw [← Real.rpow_natCast, ← Real.rpow_add (by positivity), Nat.cast_sub hd]
        norm_cast
    _ ≤ 2 * d * 3 ^ (d - 1) * ε ^ r * ∑' k : ℕ, ((k : ℝ) + 1) ^ (d - 1 + r) := by
        simp_rw [Nat.cast_add, Nat.cast_one]
        gcongr
        refine Summable.sum_le_tsum _ (fun _ _ ↦ by positivity) ?_
        simpa only [Nat.cast_add, Nat.cast_one] using
          (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by linarith : d - 1 + r < -1))

variable (L)

lemma exists_finsetSum_norm_rpow_le_tsum :
    ∃ A > (0 : ℝ), ∀ r < (-Module.finrank ℤ L : ℝ), ∀ s : Finset L, 0 ∉ s →
      ∑ z ∈ s, ‖z‖ ^ r ≤ A ^ r * ∑' k : ℕ, ((k : ℝ) + 1) ^ (Module.finrank ℤ L - 1 + r) := by
  cases subsingleton_or_nontrivial L
  · refine ⟨1, zero_lt_one, fun r hr s ↦ ?_⟩
    intro hs
    have hs' : s = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro z hz
      exact hs (Subsingleton.elim z 0 ▸ hz)
    simpa [hs'] using tsum_nonneg (g := fun k : ℕ ↦ ((k : ℝ) + 1) ^
      (Module.finrank ℤ L - 1 + r)) fun _ ↦ by positivity
  classical
  let I : Type _ := Module.Free.ChooseBasisIndex ℤ L
  have : Fintype I := inferInstance
  let b : Basis I ℤ L := Module.Free.chooseBasis ℤ L
  simp_rw [Module.finrank_eq_card_basis b]
  set d := Fintype.card I
  have hd : d ≠ 0 := by simp [d]
  let ε := normBound b
  obtain ⟨A, hA, B, hB, H⟩ : ∃ A > (0 : ℝ), ∃ B > (0 : ℝ), ∀ r < (-d : ℝ),
      ∀ s : Finset L, 0 ∉ s →
        ∑ z ∈ s, ‖z‖ ^ r ≤ A * B ^ r * ∑' k : ℕ, ((k : ℝ) + 1) ^ (d - 1 + r) := by
    refine ⟨2 * d * 3 ^ (d - 1), by positivity, ε, normBound_pos b, fun r hr u h₀ ↦ ?_⟩
    let e : (I → ℤ) ≃ₗ[ℤ] L := (b.repr ≪≫ₗ Finsupp.linearEquivFunOnFinite _ _ _).symm
    obtain ⟨u, rfl⟩ : ∃ u' : Finset _, u = u'.image e.toEmbedding :=
      ⟨u.image e.symm.toEmbedding, Finset.coe_injective
        (by simpa using (e.image_symm_image _).symm)⟩
    have hu₀ : 0 ∉ u := fun h ↦ h₀ (Finset.mem_image.mpr ⟨0, h, by simp⟩)
    dsimp
    simp only [EmbeddingLike.apply_eq_iff_eq, implies_true, Set.injOn_of_eq_iff_eq,
      Finset.sum_image, ge_iff_le]
    obtain ⟨n, hn⟩ : ∃ n : ℕ, u ⊆ Fintype.piFinset fun _ : I ↦ Finset.Icc (-n : ℤ) n := by
      obtain ⟨r, hr, hr'⟩ := u.finite_toSet.isCompact.isBounded.subset_closedBall_lt 0 0
      refine ⟨⌊r⌋.toNat, fun x hx ↦ ?_⟩
      have hr'' : ⌊r⌋ ⊔ 0 = ⌊r⌋ := by rw [sup_eq_left]; positivity
      have := hr' hx
      simp only [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hr.le,
        Int.norm_eq_abs, ← Int.cast_abs, ← Int.le_floor] at this
      simpa only [Int.ofNat_toNat, Fintype.mem_piFinset, Finset.mem_Icc, ← abs_le, hr'']
    have hn' : u ⊆ (Fintype.piFinset fun _ : I ↦ Finset.Icc (-n : ℤ) n).erase 0 :=
      fun p hp ↦ Finset.mem_erase.mpr ⟨fun h ↦ hu₀ (h ▸ hp), hn hp⟩
    refine (Finset.sum_le_sum_of_subset_of_nonneg hn' (by intros; positivity)).trans ?_
    simp only [Submodule.norm_coe]
    convert! sum_piFinset_Icc_rpow_le b rfl n r hr with x
    simp [e, Finsupp.linearCombination]
  by_cases hA' : A ≤ 1
  · refine ⟨B, hB, fun r hr s hs ↦ (H r hr s hs).trans ?_⟩
    rw [mul_assoc]
    exact mul_le_of_le_one_left (mul_nonneg (by positivity) (by positivity)) hA'
  · refine ⟨A⁻¹ * B, mul_pos (inv_pos.mpr hA) hB, fun r hr s hs ↦ (H r hr s hs).trans ?_⟩
    rw [Real.mul_rpow (inv_pos.mpr hA).le hB.le, mul_assoc, mul_assoc]
    gcongr
    rw [← Real.rpow_neg_one, ← Real.rpow_mul hA.le]
    refine Real.self_le_rpow_of_one_le (not_le.mp hA').le ?_
    simp only [neg_mul, one_mul, le_neg (b := r)]
    refine hr.le.trans ?_
    simpa [Nat.one_le_iff_ne_zero]

/--
Let `L` be a lattice with (possibly non-full) rank `d`, and `r : ℝ` such that `d < r`.
Then `∑ z ∈ L, z ≠ 0, ‖z‖⁻ʳ ≤ A⁻ʳ * ∑ k : ℕ, (k + 1)ᵈ⁻ʳ⁻¹`
for some `A > 0` depending only on `L`.
This is an arbitrary choice of `A`. See `ZLattice.tsum_norm_rpow_le`.
-/
def tsumNormRPowBound : ℝ :=
  (exists_finsetSum_norm_rpow_le_tsum L).choose

lemma tsumNormRPowBound_pos : 0 < tsumNormRPowBound L :=
  (exists_finsetSum_norm_rpow_le_tsum L).choose_spec.1

lemma tsumNormRPowBound_spec (r : ℝ) (h : r < -Module.finrank ℤ L) (s : Finset L)
    (hs : 0 ∉ s) :
    ∑ z ∈ s, ‖z‖ ^ r ≤
      tsumNormRPowBound L ^ r * ∑' k : ℕ, ((k : ℝ) + 1) ^ (Module.finrank ℤ L - 1 + r) :=
  (exists_finsetSum_norm_rpow_le_tsum L).choose_spec.2 r h s hs

private lemma sum_norm_rpow_le (r : ℝ) (h : r < -Module.finrank ℤ L)
    (s : Finset {z : L // (z : E) ≠ 0}) :
    ∑ z ∈ s, ‖(z.1 : E)‖ ^ r ≤
      tsumNormRPowBound L ^ r * ∑' k : ℕ, ((k : ℝ) + 1) ^ (Module.finrank ℤ L - 1 + r) := by
  let e : {z : L // (z : E) ≠ 0} ↪ L := ⟨Subtype.val, Subtype.val_injective⟩
  have hs : (0 : L) ∉ s.map e := by
    intro hs
    obtain ⟨z, _, hz⟩ := Finset.mem_map.mp hs
    change z.1 = (0 : L) at hz
    exact z.2 (by simpa using congrArg (fun x : L ↦ (x : E)) hz)
  have H := tsumNormRPowBound_spec L r h (s.map e) hs
  rw [Finset.sum_map] at H
  exact H

/-- If `L` is a `ℤ`-lattice with rank `d` in `E`, then the sum of `‖z‖ʳ` over its nonzero
points converges when `r < -d`. -/
lemma summable_norm_rpow (r : ℝ) (hr : r < -Module.finrank ℤ L) :
    Summable fun z : {z : L // (z : E) ≠ 0} ↦ ‖(z.1 : E)‖ ^ r :=
  summable_of_sum_le (fun _ ↦ by positivity) (sum_norm_rpow_le L r hr)

/-- The sum over the nonzero lattice points is bounded by the scaled positive-index `p`-series. -/
lemma tsum_norm_rpow_le (r : ℝ) (hr : r < -Module.finrank ℤ L) :
    ∑' z : {z : L // (z : E) ≠ 0}, ‖(z.1 : E)‖ ^ r ≤
      tsumNormRPowBound L ^ r * ∑' k : ℕ, ((k : ℝ) + 1) ^ (Module.finrank ℤ L - 1 + r) :=
  Summable.tsum_le_of_sum_le (summable_norm_rpow L r hr) (sum_norm_rpow_le L r hr)

set_option backward.isDefEq.respectTransparency false in
lemma summable_norm_sub_rpow (r : ℝ) (hr : r < -Module.finrank ℤ L) (x : E) :
    Summable fun z : {z : L // (z : E) ≠ x} ↦ ‖(z.1 : E) - x‖ ^ r := by
  let s : Set L := {z | (z : E) ≠ 0}
  let t : Set L := {z | (z : E) ≠ x}
  have hs : Summable (s.indicator fun z : L ↦ ‖(z : E)‖ ^ r) :=
    (summable_subtype_iff_indicator (s := s)).mp (summable_norm_rpow L r hr)
  apply (summable_subtype_iff_indicator (s := t) (f := fun z : L ↦ ‖(z : E) - x‖ ^ r)).mpr
  refine Summable.of_norm_bounded_eventually (.mul_left ((1 / 2 : ℝ) ^ r) hs) ?_
  have H : IsClosed (X := E) L := L.toAddSubgroup.isClosed_of_discreteTopology
  refine ((Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
    (Metric.isBounded_closedBall (x := (0 : E)) (r := 2 * ‖x‖)) H).preimage_embedding
    (.subtype _)).subset ?_
  intro z hz
  by_cases hz₀ : (z : E) = 0
  · have hz' : z = 0 := Subtype.ext hz₀
    simp [hz']
  by_cases hzx : (z : E) = x
  · simpa [hzx, two_mul] using z.2
  have hneg : r < 0 := hr.trans_le (neg_nonpos.mpr (Nat.cast_nonneg _))
  have hpos₁ : 0 < ‖(z : E) - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzx)
  have hpos₂ : 0 < ‖(z : E)‖ := norm_pos_iff.mpr hz₀
  have hc : (0 : ℝ) < 1 / 2 := by norm_num
  have hbound : ‖(z : E) - x‖ < (1 / 2) * ‖(z : E)‖ := by
    apply (Real.rpow_lt_rpow_iff_of_neg (mul_pos hc hpos₂) hpos₁ hneg).mp
    rw [Real.mul_rpow hc.le hpos₂.le]
    simpa only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le,
      Set.indicator_of_mem (show z ∈ s from hz₀), Set.indicator_of_mem (show z ∈ t from hzx),
      Real.norm_of_nonneg (Real.rpow_nonneg hpos₁.le r)] using hz
  have h := (norm_sub_norm_le _ _).trans_lt hbound
  refine ⟨?_, z.2⟩
  change (z : E) ∈ Metric.closedBall (0 : E) (2 * ‖x‖)
  simpa only [Metric.mem_closedBall, dist_zero_right] using
    (show ‖(z : E)‖ ≤ 2 * ‖x‖ by linarith)

lemma summable_norm_sub_zpow (n : ℤ) (hn : n < -Module.finrank ℤ L) (x : E) :
    Summable fun z : {z : L // (z : E) ≠ x} ↦
      Checked.zpow ‖(z.1 : E) - x‖ n
        (fun _ ↦ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr z.2)).isUnit) := by
  refine (summable_norm_sub_rpow L n (by exact_mod_cast hn) x).congr ?_
  intro z
  exact Real.rpow_intCast _ _ (h := fun _ ↦ norm_ne_zero_iff.mpr (sub_ne_zero.mpr z.2))

lemma summable_norm_zpow (n : ℤ) (hn : n < -Module.finrank ℤ L) :
    Summable fun z : {z : L // (z : E) ≠ 0} ↦
      Checked.zpow ‖(z.1 : E)‖ n (fun _ ↦ (norm_ne_zero_iff.mpr z.2).isUnit) := by
  simpa only [sub_zero] using summable_norm_sub_zpow L n hn 0

lemma summable_norm_sub_inv_pow (n : ℕ) (hn : Module.finrank ℤ L < n) (x : E) :
    Summable fun z : {z : L // (z : E) ≠ x} ↦
      Checked.inv ‖(z.1 : E) - x‖ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr z.2)).isUnit ^ n := by
  refine (summable_norm_sub_zpow L (-n) (by gcongr) x).congr ?_
  intro z
  have hz : ‖(z.1 : E) - x‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr z.2)
  rw [zpow_neg₀ hz]
  exact (inv_pow₀ (ha := hz.isUnit) n).symm

lemma summable_norm_pow_inv (n : ℕ) (hn : Module.finrank ℤ L < n) :
    Summable fun z : {z : L // (z : E) ≠ 0} ↦
      Checked.inv ‖(z.1 : E)‖ (norm_ne_zero_iff.mpr z.2).isUnit ^ n := by
  simpa only [sub_zero] using summable_norm_sub_inv_pow L n hn 0

end ZLattice
