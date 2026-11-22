/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Analysis.BoxIntegral.Integrability
public import Mathlib.Analysis.BoxIntegral.Partition.Measure
public import Mathlib.Analysis.BoxIntegral.Partition.Tagged

/-!
# Unit Partition

Fix `n` a positive integer. `BoxIntegral.unitPartition.box` are boxes in `ι → ℝ` obtained by
dividing the unit box uniformly into boxes of side length `1 / n` and translating the boxes by
vectors `ν : ι → ℤ`.

Let `B` be a `BoxIntegral`. A `unitPartition.box` is admissible for `B` (more precisely its index is
admissible) if it is contained in `B`. There are finitely many admissible `unitPartition.box` for
`B` and thus we can form the corresponding tagged prepartition, see
`BoxIntegral.unitPartition.prepartition` (note that each `unitPartition.box` comes with its
tag situated at its "upper most" vertex). If `B` satisfies `hasIntegralVertices`, that
is its vertices are in `ι → ℤ`, then the corresponding prepartition is actually a partition.

## Main definitions and results

* `BoxIntegral.hasIntegralVertices`: a `Prop` that states that the vertices of the box have
  coordinates in `ℤ`

* `BoxIntegral.unitPartition.box`: a `BoxIntegral`, indexed by `ν : ι → ℤ`, with vertices
  `ν i / n` and of side length `1 / n`.

* `BoxIntegral.unitPartition.admissibleIndex`: For `B : BoxIntegral.Box`, the set of indices of
  `unitPartition.box` that are subsets of `B`. This is a finite set.

* `BoxIntegral.unitPartition.prepartition_isPartition`: For `B : BoxIntegral.Box`, if `B`
  has integral vertices, then the prepartition of `unitPartition.box` admissible for `B` is a
  partition of `B`.

* `tendsto_tsum_div_pow_atTop_integral`: let `s` be a bounded, measurable set of `ι → ℝ`
  whose frontier has zero volume and let `F` be a continuous function. Then the limit as `n → ∞`
  of `∑ F x / n ^ card ι`, where the sum is over the points in `s ∩ n⁻¹ • (ι → ℤ)`, tends to the
  integral of `F` over `s`.

* `tendsto_card_div_pow_atTop_volume`: let `s` be a bounded, measurable set of `ι → ℝ` whose
  frontier has zero volume. Then the limit as `n → ∞` of `card (s ∩ n⁻¹ • (ι → ℤ)) / n ^ card ι`
  tends to the volume of `s`.

* `tendsto_card_div_pow_atTop_volume'`: a version of `tendsto_card_div_pow_atTop_volume` where we
  assume in addition that `x • s ⊆ y • s` whenever `0 < x ≤ y`. Then we get the same limit
  `card (s ∩ x⁻¹ • (ι → ℤ)) / x ^ card ι → volume s` but the limit is over a real variable `x`.

-/

@[expose] public section

noncomputable section

variable {ι : Type*}

open scoped Topology

section hasIntegralVertices

open Bornology

/-- A `BoxIntegral.Box` has integral vertices if its vertices have coordinates in `ℤ`. -/
def BoxIntegral.hasIntegralVertices (B : Box ι) : Prop :=
  ∃ l u : ι → ℤ, (∀ i, B.lower i = l i) ∧ (∀ i, B.upper i = u i)

/-- Any bounded set is contained in a `BoxIntegral.Box` with integral vertices. -/
theorem BoxIntegral.le_hasIntegralVertices_of_isBounded [Finite ι] {s : Set (ι → ℝ)}
    (h : IsBounded s) :
    ∃ B : BoxIntegral.Box ι, hasIntegralVertices B ∧ s ≤ B := by
  have := Fintype.ofFinite ι
  obtain ⟨R, hR₁, hR₂⟩ := IsBounded.subset_ball_lt h 0 0
  let C : ℕ := ⌈R⌉₊
  have hC := Nat.ceil_pos.mpr hR₁
  let I : Box ι := Box.mk (fun _ ↦ -C) (fun _ ↦ C)
    (fun _ ↦ by simp [C, neg_lt_self_iff, Nat.cast_pos, hC])
  refine ⟨I, ⟨fun _ ↦ - C, fun _ ↦ C, fun i ↦ (Int.cast_neg_natCast C).symm, fun _ ↦ rfl⟩,
    le_trans hR₂ ?_⟩
  suffices Metric.ball (0 : ι → ℝ) C ≤ I from
    le_trans (Metric.ball_subset_ball (Nat.le_ceil R)) this
  intro x hx
  simp_rw [C, mem_ball_zero_iff, pi_norm_lt_iff (Nat.cast_pos.mpr hC),
    Real.norm_eq_abs, abs_lt] at hx
  exact fun i ↦ ⟨(hx i).1, le_of_lt (hx i).2⟩

end hasIntegralVertices

namespace BoxIntegral.unitPartition

open Bornology MeasureTheory Fintype BoxIntegral

variable (n : ℕ)

/-- A `BoxIntegral`, indexed by a positive integer `n` and `ν : ι → ℤ`, with corners `ν i / n`
and of side length `1 / n`. -/
def box [NeZero n] (ν : ι → ℤ) : Box ι where
  lower := fun i ↦ (ν i : ℝ) / (n : ℝ)
  upper := fun i ↦ ((ν i : ℝ) + 1) / (n : ℝ)
  lower_lt_upper := fun _ ↦ by simp [add_div, n.pos_of_neZero]

@[simp]
theorem box_lower [NeZero n] (ν : ι → ℤ) :
    (box n ν).lower = fun i ↦ (ν i : ℝ) / (n : ℝ) := rfl

@[simp]
theorem box_upper [NeZero n] (ν : ι → ℤ) :
    (box n ν).upper = fun i ↦ ((ν i : ℝ) + 1) / (n : ℝ) := rfl

variable {n} in
@[simp]
theorem mem_box_iff [NeZero n] {ν : ι → ℤ} {x : ι → ℝ} :
    x ∈ box n ν ↔ ∀ i, (ν i : ℝ) / (n : ℝ) < x i ∧ x i ≤ ((ν i : ℝ) + 1) / (n : ℝ) := by
  simp_rw [Box.mem_def, box, Set.mem_Ioc]

variable {n} in
theorem mem_box_iff' [NeZero n] {ν : ι → ℤ} {x : ι → ℝ} :
    x ∈ box n ν ↔ ∀ i, ν i < n * x i ∧ n * x i ≤ ν i + 1 := by
  have h : 0 < (n : ℝ) := Nat.cast_pos.mpr <| n.pos_of_neZero
  simp_rw [mem_box_iff, ← _root_.le_div_iff₀' h, ← div_lt_iff₀' h]

variable [NeZero n]

/-- The tag of (the index of) a `unitPartition.box`. -/
abbrev tag (ν : ι → ℤ) : ι → ℝ := fun i ↦ ((ν i : ℝ) + 1) / (n : ℝ)

@[simp]
theorem tag_apply (ν : ι → ℤ) (i : ι) : tag n ν i = ((ν i : ℝ) + 1) / (n : ℝ) := rfl

theorem tag_mem (ν : ι → ℤ) : tag n ν ∈ box n ν :=
  mem_box_iff.mpr fun i ↦ ⟨(box n ν).lower_lt_upper i, le_rfl⟩

/-- For `x : ι → ℝ`, its index is the index of the unique `unitPartition.box` to which
it belongs. -/
def index (x : ι → ℝ) (i : ι) : ℤ := ⌈n * x i⌉ - 1

@[simp]
theorem index_apply (m : ℕ) {x : ι → ℝ} (i : ι) :
    index m x i = ⌈m * x i⌉ - 1 := rfl

variable {n} in
theorem mem_box_iff_index {x : ι → ℝ} {ν : ι → ℤ} :
    x ∈ box n ν ↔ index n x = ν := by
  simp_rw [mem_box_iff', funext_iff, index_apply, sub_eq_iff_eq_add, Int.ceil_eq_iff,
    Int.cast_add, Int.cast_one, add_sub_cancel_right]

@[simp]
theorem index_tag (ν : ι → ℤ) :
    index n (tag n ν) = ν := mem_box_iff_index.mp (tag_mem n ν)

theorem tag_injective : Function.Injective (fun ν : ι → ℤ ↦ tag n ν) := by
  intro a b h
  simpa only [index_tag] using congrArg (index n) h

variable {n} in
theorem disjoint {ν ν' : ι → ℤ} :
    ν ≠ ν' ↔ Disjoint (box n ν).toSet (box n ν').toSet := by
  rw [not_iff_comm, Set.not_disjoint_iff]
  refine ⟨fun ⟨x, hx, hx'⟩ ↦ ?_, fun h ↦ ⟨tag n ν, tag_mem n ν, h ▸ tag_mem n ν⟩⟩
  rw [← mem_box_iff_index.mp hx, ← mem_box_iff_index.mp hx']

theorem box_injective : Function.Injective (fun ν : ι → ℤ ↦ box n ν) := by
  intro _ _ h
  contrapose! h
  exact Box.ne_of_disjoint_coe (disjoint.mp h)

lemma box.upper_sub_lower (ν : ι → ℤ) (i : ι) :
    (box n ν).upper i - (box n ν).lower i = 1 / (n : ℝ) := by
  simp_rw [box, add_div, add_sub_cancel_left]

section fintype

variable [Fintype ι]

theorem diam_boxIcc (ν : ι → ℤ) :
    Metric.diam (Box.Icc (box n ν)) ≤ 1 / (n : ℝ) := by
  rw [BoxIntegral.Box.Icc_eq_pi]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) <| Metric.ediam_pi_le_of_le fun i ↦ ?_
  simp_rw [Real.ediam_Icc, box.upper_sub_lower, le_rfl]

@[simp]
theorem volume_box (ν : ι → ℤ) :
    volume (box n ν : Set (ι → ℝ)) = ENNReal.div 1 ((n : ENNReal) ^ card ι) := by
  simp_rw [volume_pi, BoxIntegral.Box.coe_eq_pi, Measure.pi_pi, Real.volume_Ioc,
    box.upper_sub_lower, Finset.prod_const, ENNReal.ofReal_div_of_pos (Nat.cast_pos.mpr
    n.pos_of_neZero), ENNReal.ofReal_one, ENNReal.ofReal_natCast, ENNReal.one_div, ENNReal.inv_pow,
    Finset.card_univ]

theorem setFinite_index {s : Set (ι → ℝ)} (hs₁ : NullMeasurableSet s) (hs₂ : volume s ≠ ⊤) :
    Set.Finite {ν : ι → ℤ | ↑(box n ν) ⊆ s} := by
  refine (Measure.finite_const_le_meas_of_disjoint_iUnion₀ volume
    (ε := ENNReal.div 1 ((n : ENNReal) ^ card ι))
    (by simp) (As := fun ν : ι → ℤ ↦ (box n ν) ∩ s) (fun ν ↦ ?_) (fun _ _ h ↦ ?_) ?_).subset
      (fun _ hν ↦ ?_)
  · refine NullMeasurableSet.inter ?_ hs₁
    exact (box n ν).measurableSet_coe.nullMeasurableSet
  · exact ((Disjoint.inter_right _ (disjoint.mp h)).inter_left _).aedisjoint
  · exact lt_top_iff_ne_top.mp <| measure_lt_top_of_subset
      (by simp only [Set.iUnion_subset_iff, Set.inter_subset_right, implies_true]) hs₂
  · rw [Set.mem_ofPred, Set.inter_eq_self_of_subset_left hν, volume_box]

/-- For `B : BoxIntegral.Box`, the set of indices of `unitPartition.box` that are subsets of `B`.
This is a finite set. These boxes cover `B` if it has integral vertices, see
`unitPartition.prepartition_isPartition`. -/
def admissibleIndex (B : Box ι) : Finset (ι → ℤ) := by
  refine (setFinite_index n B.measurableSet_coe.nullMeasurableSet ?_).toFinset
  exact lt_top_iff_ne_top.mp (IsBounded.measure_lt_top B.isBounded)

variable {n} in
theorem mem_admissibleIndex_iff {B : Box ι} {ν : ι → ℤ} :
    ν ∈ admissibleIndex n B ↔ box n ν ≤ B := by
  rw [admissibleIndex, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Box.coe_subset_coe]

open scoped Classical in
/-- For `B : BoxIntegral.Box`, the `TaggedPrepartition` formed by the set of all
`unitPartition.box` whose index is `B`-admissible. -/
def prepartition (B : Box ι) : TaggedPrepartition B where
  boxes := Finset.image (fun ν ↦ box n ν) (admissibleIndex n B)
  le_of_mem' _ hI := by
    obtain ⟨_, hν, rfl⟩ := Finset.mem_image.mp hI
    exact mem_admissibleIndex_iff.mp hν
  pairwiseDisjoint _ hI₁ _ hI₂ h := by
    obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hI₁
    obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hI₂
    exact disjoint.mp fun x ↦ h (congrArg (box n) x)
  tag I :=
    if hI : ∃ ν ∈ admissibleIndex n B, I = box n ν then tag n hI.choose else B.exists_mem.choose
  tag_mem_Icc I := by
    by_cases hI : ∃ ν ∈ admissibleIndex n B, I = box n ν
    · simp_rw [dite_eq_left hI]
      exact Box.coe_subset_Icc <| (mem_admissibleIndex_iff.mp hI.choose_spec.1) (tag_mem n _)
    · simp_rw [dite_eq_right hI]
      exact Box.coe_subset_Icc B.exists_mem.choose_spec

set_option backward.isDefEq.respectTransparency.types false in
variable {n} in
@[simp]
theorem mem_prepartition_iff {B I : Box ι} :
    I ∈ prepartition n B ↔ ∃ ν ∈ admissibleIndex n B, box n ν = I := by
  classical
  rw [prepartition, TaggedPrepartition.mem_mk, Prepartition.mem_mk, Finset.mem_image]

variable {n} in
theorem mem_prepartition_boxes_iff {B I : Box ι} :
    I ∈ (prepartition n B).boxes ↔ ∃ ν ∈ admissibleIndex n B, box n ν = I :=
  mem_prepartition_iff

theorem prepartition_tag {ν : ι → ℤ} {B : Box ι} (hν : ν ∈ admissibleIndex n B) :
    (prepartition n B).tag (box n ν) = tag n ν := by
  dsimp only [prepartition]
  have h : ∃ ν' ∈ admissibleIndex n B, box n ν = box n ν' := ⟨ν, hν, rfl⟩
  rw [dite_eq_left h, (tag_injective n).eq_iff, ← (box_injective n).eq_iff]
  exact h.choose_spec.2.symm

theorem box_index_tag_eq_self {B I : Box ι} (hI : I ∈ (prepartition n B).boxes) :
    box n (index n ((prepartition n B).tag I)) = I := by
  obtain ⟨ν, hν, rfl⟩ := mem_prepartition_boxes_iff.mp hI
  rw [prepartition_tag n hν, index_tag]

theorem prepartition_isHenstock (B : Box ι) :
    (prepartition n B).IsHenstock := by
  intro _ hI
  obtain ⟨ν, hν, rfl⟩ := mem_prepartition_iff.mp hI
  rw [prepartition_tag n hν]
  exact Box.coe_subset_Icc (tag_mem _ _)

theorem prepartition_isSubordinate (B : Box ι) {r : ℝ} (hr : 0 < r) (hn : 1 / (n : ℝ) ≤ r) :
    (prepartition n B).IsSubordinate (fun _ ↦ ⟨r, hr⟩) := by
  intro _ hI
  obtain ⟨ν, hν, rfl⟩ := mem_prepartition_iff.mp hI
  refine fun _ h ↦ le_trans (Metric.dist_le_diam_of_mem (Box.isBounded_Icc _) h ?_) ?_
  · rw [prepartition_tag n hν]
    exact Box.coe_subset_Icc (tag_mem _ _)
  · exact le_trans (diam_boxIcc n ν) hn

private theorem mem_admissibleIndex_of_mem_box_aux₁ (x : ℝ) (a : ℤ) :
    a < x ↔ a ≤ ((⌈n * x⌉ : ℝ) - 1) / (n : ℝ) := by
  have h : 0 < (n : ℝ) := Nat.cast_pos.mpr <| n.pos_of_neZero
  rw [le_div_iff₀' h, le_sub_iff_add_le,
    show (n : ℝ) * a + 1 = (n * a + 1 : ℤ) by norm_cast,
    Int.cast_le, Int.add_one_le_iff, Int.lt_ceil, Int.cast_mul, Int.cast_natCast,
    mul_lt_mul_iff_right₀ h]

private theorem mem_admissibleIndex_of_mem_box_aux₂ (x : ℝ) (a : ℤ) :
    x ≤ a ↔ ((⌈n * x⌉ : ℝ) - 1 + 1) / (n : ℝ) ≤ a := by
  have h : 0 < (n : ℝ) := Nat.cast_pos.mpr <| n.pos_of_neZero
  rw [sub_add_cancel, div_le_iff₀' h,
    show (n : ℝ) * a = (n * a : ℤ) by norm_cast,
    Int.cast_le, Int.ceil_le, Int.cast_mul, Int.cast_natCast, mul_le_mul_iff_right₀ h]

/-- If `B : BoxIntegral.Box` has integral vertices and contains the point `x`, then the index of
`x` is admissible for `B`. -/
theorem mem_admissibleIndex_of_mem_box {B : Box ι} (hB : hasIntegralVertices B) {x : ι → ℝ}
    (hx : x ∈ B) : index n x ∈ admissibleIndex n B := by
  obtain ⟨l, u, hl, hu⟩ := hB
  simp_rw [mem_admissibleIndex_iff, Box.le_iff_bounds, box_lower, box_upper, Pi.le_def,
    index_apply, hl, hu, ← forall_and]
  push_cast
  refine fun i ↦ ⟨?_, ?_⟩
  · exact (mem_admissibleIndex_of_mem_box_aux₁ n (x i) (l i)).mp ((hl i) ▸ (hx i).1)
  · exact (mem_admissibleIndex_of_mem_box_aux₂ n (x i) (u i)).mp ((hu i) ▸ (hx i).2)

/-- If `B : BoxIntegral.Box` has integral vertices, then `prepartition n B` is a partition of
`B`. -/
theorem prepartition_isPartition {B : Box ι} (hB : hasIntegralVertices B) :
    (prepartition n B).IsPartition := by
  refine fun x hx ↦ ⟨box n (index n x), ?_, mem_box_iff_index.mpr rfl⟩
  rw [TaggedPrepartition.mem_toPrepartition, mem_prepartition_iff]
  exact ⟨index n x, mem_admissibleIndex_of_mem_box n hB hx, rfl⟩

end fintype

open Submodule

open scoped Pointwise

variable (c : ℝ) (s : Set (ι → ℝ)) (F : (ι → ℝ) → ℝ)

-- The image of `ι → ℤ` inside `ι → ℝ`
local notation "L" => span ℤ (Set.range (Pi.basisFun ℝ ι))

section finite

variable [Finite ι]

variable {n} in
theorem mem_smul_span_iff {v : ι → ℝ} :
    v ∈ (n : ℝ)⁻¹ • L ↔ ∀ i, n * v i ∈ Set.range (algebraMap ℤ ℝ) := by
  have := Fintype.ofFinite ι
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  change v ∈ (↑((n : ℝ)⁻¹ • L) : Set (ι → ℝ)) ↔ _
  rw [coe_pointwise_smul, Set.mem_inv_smul_set_iff₀ hn]
  change (n : ℝ) • v ∈ L ↔ _
  simp only [Module.Basis.mem_span_iff_repr_mem, Pi.basisFun_repr, Pi.smul_apply, smul_eq_mul]

theorem tag_mem_smul_span (ν : ι → ℤ) :
    tag n ν ∈ (n : ℝ)⁻¹ • L := by
  refine mem_smul_span_iff.mpr fun i ↦ ⟨ν i + 1, ?_⟩
  change ((ν i + 1 : ℤ) : ℝ) = (n : ℝ) * tag n ν i
  rw [tag_apply, mul_div_cancel₀, Int.cast_add, Int.cast_one]

theorem tag_index_eq_self_of_mem_smul_span {x : ι → ℝ} (hx : x ∈ (n : ℝ)⁻¹ • L) :
    tag n (index n x) = x := by
  rw [mem_smul_span_iff] at hx
  ext i
  obtain ⟨a, ha⟩ : ∃ a : ℤ, (a : ℝ) = n * x i := hx i
  rw [tag_apply, index_apply, Int.cast_sub, Int.cast_one, sub_add_cancel, ← ha, Int.ceil_intCast]
  exact div_eq_iff.mpr (ha.trans (mul_comm _ _))

theorem eq_of_mem_smul_span_of_index_eq_index {x y : ι → ℝ} (hx : x ∈ (n : ℝ)⁻¹ • L)
    (hy : y ∈ (n : ℝ)⁻¹ • L) (h : index n x = index n y) : x = y := by
  rw [← tag_index_eq_self_of_mem_smul_span n hx, ← tag_index_eq_self_of_mem_smul_span n hy, h]

private def tendsto_card_div_pow₁ {c : ℝ} (hc : c ≠ 0) :
    ↑(s ∩ c⁻¹ • L) ≃ ↑(c • s ∩ L) :=
  Equiv.subtypeEquiv (Equiv.smulRight hc) (fun x ↦ by
    simp_rw [Set.mem_inter_iff, Equiv.smulRight_apply, Set.smul_mem_smul_set_iff₀ hc,
      ← Set.mem_inv_smul_set_iff₀ hc])

private theorem tendsto_card_div_pow₂ (hs₁ : IsBounded s)
    (hs₄ : ∀ ⦃x y : ℝ⦄, 0 < x → x ≤ y → x • s ⊆ y • s) {x y : ℝ} (hx : 0 < x) (hy : x ≤ y) :
    Nat.card ↑(s ∩ x⁻¹ • L) ≤ Nat.card ↑(s ∩ y⁻¹ • L) := by
  have := Fintype.ofFinite ι
  rw [Nat.card_congr (tendsto_card_div_pow₁ s hx.ne'),
      Nat.card_congr (tendsto_card_div_pow₁ s (hx.trans_le hy).ne')]
  refine Nat.card_mono ?_ ?_
  · exact ZSpan.setFinite_inter _ (IsBounded.smul₀ hs₁ y)
  · exact Set.inter_subset_inter_left _ <| hs₄ hx hy

end finite

section fintype

variable [Fintype ι]

theorem integralSum_eq_tsum_div {B : Box ι} (hB : hasIntegralVertices B) (hs₀ : s ≤ B) :
    integralSum (Set.indicator s F) (BoxAdditiveMap.toSMul (Measure.toBoxAdditive volume))
      (prepartition n B) = (∑' x : ↑(s ∩ (n : ℝ)⁻¹ • L), F x) / (n : ℝ) ^ card ι := by
  classical
  unfold integralSum
  have : Fintype ↑(s ∩ (n : ℝ)⁻¹ • L) := by
    apply Set.Finite.fintype
    have hi : (n : ℝ)⁻¹ ≠ 0 := inv_ne_zero
    rw [← coe_pointwise_smul, ZSpan.smul _ hi]
    exact ZSpan.setFinite_inter _ (B.isBounded.subset hs₀)
  rw [tsum_fintype, Finset.sum_set_coe, Finset.sum_div, eq_comm]
  simp_rw [Set.indicator_apply, apply_ite, BoxAdditiveMap.toSMul_apply, Measure.toBoxAdditive_apply,
    smul_eq_mul, mul_zero, Finset.sum_ite, Finset.sum_const_zero, add_zero]
  refine Finset.sum_bij (fun x _ ↦ box n (index n x)) (fun _ hx ↦ Finset.mem_filter.mpr ?_)
    (fun _ hx _ hy h ↦ ?_) (fun I hI ↦ ?_) (fun _ hx ↦ ?_)
  · rw [Set.mem_toFinset] at hx
    refine ⟨mem_prepartition_boxes_iff.mpr
      ⟨index n _, mem_admissibleIndex_of_mem_box n hB (hs₀ hx.1), rfl⟩, ?_⟩
    simp_rw [prepartition_tag n (mem_admissibleIndex_of_mem_box n hB (hs₀ hx.1)),
      tag_index_eq_self_of_mem_smul_span n hx.2, hx.1]
  · rw [Set.mem_toFinset] at hx hy
    exact eq_of_mem_smul_span_of_index_eq_index n hx.2 hy.2 (box_injective n h)
  · rw [Finset.mem_filter] at hI
    refine ⟨(prepartition n B).tag I, Set.mem_toFinset.mpr ⟨hI.2, ?_⟩, box_index_tag_eq_self n hI.1⟩
    rw [← box_index_tag_eq_self n hI.1, prepartition_tag n
      (mem_admissibleIndex_of_mem_box n hB (hs₀ hI.2))]
    exact tag_mem_smul_span _ _
  · rw [Set.mem_toFinset] at hx
    have hden : IsUnit (((n : ENNReal) ^ card ι).toReal) := by
      simp only [ENNReal.toReal_pow, ENNReal.toReal_natCast]
      exact (pow_pos (Nat.cast_pos.mpr n.pos_of_neZero) _).ne'.isUnit
    simp only [measureReal_def, volume_box,
      prepartition_tag n (mem_admissibleIndex_of_mem_box n hB (hs₀ hx.1)),
      tag_index_eq_self_of_mem_smul_span n hx.2, ENNReal.toReal_div _ _ (hb := hden),
      ENNReal.toReal_one, ENNReal.toReal_pow, ENNReal.toReal_natCast]
    rw [mul_comm_div₀, one_mul]

open Filter

/-- Let `s` be a bounded, measurable set of `ι → ℝ` whose frontier has zero volume and let `F`
be continuous. As the positive integers `n` tend to infinity, the sum of `F x / n ^ card ι`
over the points `x ∈ s ∩ n⁻¹ • (ι → ℤ)` tends to the integral of `F` over `s`. -/
theorem _root_.tendsto_tsum_div_pow_atTop_integral (hF : Continuous F) (hs₁ : IsBounded s)
    (hs₂ : MeasurableSet s) (hs₃ : volume (frontier s) = 0) :
    Tendsto (fun k : {n : ℕ // n ≠ 0} ↦
      letI : NeZero k.val := ⟨k.property⟩
      (∑' x : ↑(s ∩ (k.val : ℝ)⁻¹ • L), F x) / (k.val : ℝ) ^ card ι)
      (comap Subtype.val atTop) (nhds (∫ x in s, F x)) := by
  obtain ⟨B, hB, hs₀⟩ := le_hasIntegralVertices_of_isBounded hs₁
  refine Metric.tendsto_nhds.mpr fun ε hε ↦ ?_
  have h₁ : ∃ C, ∀ x ∈ Box.Icc B, ‖Set.indicator s F x‖ ≤ C := by
    obtain ⟨C₀, h₀⟩ := (Box.isCompact_Icc B).exists_bound_of_continuousOn hF.continuousOn
    refine ⟨max 0 C₀, fun x hx ↦ ?_⟩
    rw [Set.indicator]
    split_ifs with hs
    · exact le_max_of_le_right (h₀ x hx)
    · exact norm_zero.trans_le <| le_max_left 0 _
  have h₂ : ∀ᵐ x, ContinuousAt (s.indicator F) x := by
    filter_upwards [compl_mem_ae_iff.mpr hs₃] with _ h
      using (hF.continuousOn).continuousAt_indicator h
  obtain ⟨r, hr₁, hr₂⟩ := (hasIntegral_iff.mp <|
      AEContinuous.hasBoxIntegral (volume : Measure (ι → ℝ)) h₁ h₂
        IntegrationParams.Riemann) (ε / 2) (half_pos hε)
  have hrpos : 0 < (r 0 0 : ℝ) := (r 0 0).prop
  have hv : Tendsto (Subtype.val : {n : ℕ // n ≠ 0} → ℕ)
      (comap Subtype.val atTop) atTop := tendsto_comap
  filter_upwards [hv.eventually (eventually_ge_atTop ⌈(r 0 0 : ℝ)⁻¹⌉₊)] with k hk
  obtain ⟨n, hn₀⟩ := k
  let : NeZero n := ⟨hn₀⟩
  have hn : ⌈(r 0 0 : ℝ)⁻¹⌉₊ ≤ n := hk
  refine lt_of_le_of_lt ?_ (half_lt_self_iff.mpr hε)
  rw [← integralSum_eq_tsum_div _ s F hB hs₀, ← Measure.restrict_restrict_of_subset hs₀,
    ← integral_indicator hs₂]
  refine hr₂ 0 _ ⟨?_, fun _ ↦ ?_, fun h ↦ ?_, fun h ↦ ?_⟩ (prepartition_isPartition _ hB)
  · rw [show r 0 = fun _ ↦ r 0 0 from funext_iff.mpr (hr₁ 0 rfl)]
    apply prepartition_isSubordinate n B
    rw [one_div₀, inv_le_comm₀ (mod_cast (Nat.pos_of_neZero n)) hrpos]
    exact le_trans (Nat.le_ceil _) (Nat.cast_le.mpr hn)
  · exact prepartition_isHenstock n B
  · simp only [IntegrationParams.Riemann, Bool.false_eq_true] at h
  · simp only [IntegrationParams.Riemann, Bool.false_eq_true] at h

/-- Let `s` be a bounded, measurable set of `ι → ℝ` whose frontier has zero volume. As the
positive integers `n` tend to infinity, `card (s ∩ n⁻¹ • (ι → ℤ)) / n ^ card ι` tends to the
volume of `s`. This is a special case of `tendsto_tsum_div_pow_atTop_integral` with `F = 1`. -/
theorem _root_.tendsto_card_div_pow_atTop_volume (hs₁ : IsBounded s)
    (hs₂ : MeasurableSet s) (hs₃ : volume (frontier s) = 0) :
    Tendsto (fun k : {n : ℕ // n ≠ 0} ↦
      letI : NeZero k.val := ⟨k.property⟩
      (Nat.card ↑(s ∩ (k.val : ℝ)⁻¹ • L) : ℝ) / (k.val : ℝ) ^ card ι)
      (comap Subtype.val atTop) (𝓝 (volume.real s)) := by
  simpa only [tsum_const, nsmul_eq_mul, setIntegral_const, smul_eq_mul, mul_one] using
    tendsto_tsum_div_pow_atTop_integral s (fun _ ↦ (1 : ℝ)) continuous_const hs₁ hs₂ hs₃

/-- A version of `tendsto_card_div_pow_atTop_volume` for a nonzero real variable. -/
theorem _root_.tendsto_card_div_pow_atTop_volume' (hs₁ : IsBounded s)
    (hs₂ : MeasurableSet s) (hs₃ : volume (frontier s) = 0)
    (hs₄ : ∀ ⦃x y : ℝ⦄, 0 < x → x ≤ y → x • s ⊆ y • s) :
    Tendsto (fun x : {x : ℝ // x ≠ 0} ↦
      letI : NeZero x.val := ⟨x.property⟩
      (Nat.card ↑(s ∩ x.val⁻¹ • L) : ℝ) / x.val ^ card ι)
      (comap Subtype.val atTop) (𝓝 (volume.real s)) := by
  -- Above one, both natural roundings are nonzero.
  let Tail := {x : ℝ // 1 ≤ x}
  let Grid := {n : ℕ // n ≠ 0}
  let l : Filter Tail := comap Subtype.val atTop
  have hv : Tendsto (fun x : Tail ↦ x.val) l atTop := tendsto_comap
  have pos (x : Tail) : 0 < x.val := zero_lt_one.trans_le x.property
  let toNonzero (x : Tail) : {x : ℝ // x ≠ 0} := ⟨x.val, (pos x).ne'⟩
  have hnonzero : Tendsto toNonzero l (comap Subtype.val atTop) := tendsto_comap_iff.mpr hv
  have nz (k : Grid) : (k.val : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr k.property
  let count (a : ℝ) (ha : a ≠ 0) : ℝ := Nat.card ↑(s ∩ Checked.inv a ha.isUnit • L)
  let quotient (v : ℝ) (x : Tail) : ℝ :=
    Checked.div v (x.val ^ card ι) ((pos x).ne'.isUnit.pow _)
  have mono {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
      count a ha.ne' ≤ count b (ha.trans_le hab).ne' :=
    Nat.cast_le.mpr (tendsto_card_div_pow₂ s hs₁ hs₄ ha hab)
  have quotient_mono {u v : ℝ} (h : u ≤ v) (x : Tail) : quotient u x ≤ quotient v x :=
    (div_le_div_iff_of_pos_right (pow_pos (pos x) _)).mpr h
  have rounded (k : Tail → Grid) (hk : Tendsto (fun x ↦ (k x).val) l atTop)
      (hr : Tendsto (fun x ↦ Checked.div ((k x).val : ℝ) x.val (pos x).ne'.isUnit) l (𝓝 1)) :
      Tendsto (fun x ↦ quotient (count _ (nz (k x))) x) l (𝓝 (volume.real s)) := by
    have hk' : Tendsto k l (comap Subtype.val atTop) := tendsto_comap_iff.mpr hk
    have h := ((tendsto_card_div_pow_atTop_volume s hs₁ hs₂ hs₃).comp hk').mul
      (hr.pow (card ι))
    simp only [one_pow, mul_one] at h
    refine h.congr' (Eventually.of_forall fun x ↦ ?_)
    let a : ℝ := (k x).val
    let b : ℝ := x.val
    have ha : a ≠ 0 := nz (k x)
    have hb : b ≠ 0 := (pos x).ne'
    change count a ha / a ^ card ι * (a / b) ^ card ι = count a ha / b ^ card ι
    rw [div_pow₀, ← mul_div_assoc₀, div_mul_cancel₀]
  let lo (x : Tail) : Grid := ⟨⌊x.val⌋₊, (Nat.floor_pos.mpr x.property).ne'⟩
  let hi (x : Tail) : Grid := ⟨⌈x.val⌉₊, (Nat.ceil_pos.mpr (pos x)).ne'⟩
  have hlo (x : Tail) : ((lo x).val : ℝ) ≤ x.val := Nat.floor_le (pos x).le
  have hhi (x : Tail) : x.val ≤ ((hi x).val : ℝ) := Nat.le_ceil _
  have hlo_tendsto : Tendsto (fun x : Tail ↦ (lo x).val) l atTop :=
    (tendsto_nat_floor_atTop (α := ℝ)).comp hv
  have hhi_tendsto : Tendsto (fun x : Tail ↦ (hi x).val) l atTop :=
    (tendsto_nat_ceil_atTop (α := ℝ)).comp hv
  have hlo_ratio :
      Tendsto (fun x : Tail ↦ Checked.div ((lo x).val : ℝ) x.val (pos x).ne'.isUnit) l (𝓝 1) := by
    simpa only [Function.comp_def, toNonzero, lo] using
      (tendsto_nat_floor_div_atTop (R := ℝ)).comp hnonzero
  have hhi_ratio :
      Tendsto (fun x : Tail ↦ Checked.div ((hi x).val : ℝ) x.val (pos x).ne'.isUnit) l (𝓝 1) := by
    simpa only [Function.comp_def, toNonzero, hi] using
      (tendsto_nat_ceil_div_atTop (R := ℝ)).comp hnonzero
  have low := rounded lo hlo_tendsto hlo_ratio
  have high := rounded hi hhi_tendsto hhi_ratio
  have hlim : Tendsto (fun x : Tail ↦ quotient (count x.val (pos x).ne') x)
      l (𝓝 (volume.real s)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' low high
      (Eventually.of_forall fun x ↦
        quotient_mono (mono (Nat.cast_pos.mpr (Nat.floor_pos.mpr x.property)) (hlo x)) x)
      (Eventually.of_forall fun x ↦ quotient_mono (mono (pos x) (hhi x)) x)
  intro U hU
  obtain ⟨P, hP, hPU⟩ := hlim hU
  refine ⟨P ∩ Set.Ici 1, inter_mem hP (Ici_mem_atTop 1), ?_⟩
  intro x hx
  exact @hPU ⟨x.val, hx.2⟩ hx.1

end fintype

end BoxIntegral.unitPartition
