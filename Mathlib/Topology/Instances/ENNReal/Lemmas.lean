/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Basic.ENNReal.BigOperators
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import Mathlib.Topology.Instances.NNReal.Lemmas
public import Mathlib.Topology.MetricSpace.ProperSpace.Real
public import Mathlib.Topology.MetricSpace.Pseudo.Real
public import Mathlib.Topology.Metrizable.Uniformity
public import Mathlib.Topology.Order.LiminfLimsup

/-!
# Topology on extended non-negative reals
-/

@[expose] public section

noncomputable section

open Filter Function Metric Set Topology
open scoped Finset ENNReal NNReal

variable {α : Type*} {β : Type*} {γ : Type*}

namespace ENNReal

variable {a b : ℝ≥0∞} {r : ℝ≥0} {x : ℝ≥0∞} {ε : ℝ≥0∞}

section TopologicalSpace

open TopologicalSpace

theorem isOpen_ne_top : IsOpen { a : ℝ≥0∞ | a ≠ ∞ } := isOpen_ne

theorem isOpen_Ico_zero : IsOpen (Ico 0 b) := by
  rw [ENNReal.Ico_eq_Iio]
  exact isOpen_Iio

theorem coe_range_mem_nhds : range ((↑) : ℝ≥0 → ℝ≥0∞) ∈ 𝓝 (r : ℝ≥0∞) :=
  IsOpen.mem_nhds isOpenEmbedding_coe.isOpen_range <| mem_range_self _

@[fun_prop]
theorem continuous_coe : Continuous ((↑) : ℝ≥0 → ℝ≥0∞) :=
  isEmbedding_coe.continuous

lemma tendsto_coe_toNNReal {a : ℝ≥0∞} (ha : a ≠ ⊤) : Tendsto (↑) (𝓝 a.toNNReal) (𝓝 a) := by
  nth_rewrite 2 [← coe_toNNReal ha]
  exact continuous_coe.tendsto _

theorem continuous_coe_iff {α} [TopologicalSpace α] {f : α → ℝ≥0} :
    (Continuous fun a => (f a : ℝ≥0∞)) ↔ Continuous f :=
  isEmbedding_coe.continuous_iff.symm

theorem nhds_coe {r : ℝ≥0} : 𝓝 (r : ℝ≥0∞) = (𝓝 r).map (↑) :=
  (isOpenEmbedding_coe.map_nhds_eq r).symm

theorem tendsto_nhds_coe_iff {α : Type*} {l : Filter α} {x : ℝ≥0} {f : ℝ≥0∞ → α} :
    Tendsto f (𝓝 ↑x) l ↔ Tendsto (f ∘ (↑) : ℝ≥0 → α) (𝓝 x) l := by
  rw [nhds_coe, tendsto_map'_iff]

theorem continuousAt_coe_iff {α : Type*} [TopologicalSpace α] {x : ℝ≥0} {f : ℝ≥0∞ → α} :
    ContinuousAt f ↑x ↔ ContinuousAt (f ∘ (↑) : ℝ≥0 → α) x :=
  tendsto_nhds_coe_iff

theorem continuous_ofReal : Continuous ENNReal.ofReal :=
  (continuous_coe_iff.2 continuous_id).comp continuous_real_toNNReal

theorem tendsto_ofReal {f : Filter α} {m : α → ℝ} {a : ℝ} (h : Tendsto m f (𝓝 a)) :
    Tendsto (fun a => ENNReal.ofReal (m a)) f (𝓝 (ENNReal.ofReal a)) :=
  (continuous_ofReal.tendsto a).comp h

theorem tendsto_toNNReal {a : ℝ≥0∞} (ha : a ≠ ∞) :
    Tendsto ENNReal.toNNReal (𝓝 a) (𝓝 a.toNNReal) := by
  lift a to ℝ≥0 using ha
  rw [nhds_coe, tendsto_map'_iff]
  exact tendsto_id

theorem tendsto_toNNReal_iff {f : α → ℝ≥0∞} {u : Filter α} (ha : a ≠ ∞) (hf : ∀ x, f x ≠ ∞) :
    Tendsto (ENNReal.toNNReal ∘ f) u (𝓝 (a.toNNReal)) ↔ Tendsto f u (𝓝 a) := by
  refine ⟨fun h => ?_, fun h => (ENNReal.tendsto_toNNReal ha).comp h⟩
  rw [← coe_comp_toNNReal_comp hf]
  exact (tendsto_coe_toNNReal ha).comp h

theorem tendsto_toNNReal_iff' {f : α → ℝ≥0∞} {u : Filter α} {a : ℝ≥0} (hf : ∀ x, f x ≠ ∞) :
    Tendsto (ENNReal.toNNReal ∘ f) u (𝓝 a) ↔ Tendsto f u (𝓝 a) := by
  rw [← toNNReal_coe a]
  exact tendsto_toNNReal_iff coe_ne_top hf

theorem eventuallyEq_of_toReal_eventuallyEq {l : Filter α} {f g : α → ℝ≥0∞}
    (hfi : ∀ᶠ x in l, f x ≠ ∞) (hgi : ∀ᶠ x in l, g x ≠ ∞)
    (hfg : (fun x => (f x).toReal) =ᶠ[l] fun x => (g x).toReal) : f =ᶠ[l] g := by
  filter_upwards [hfi, hgi, hfg] with _ hfx hgx _
  rwa [← ENNReal.toReal_eq_toReal_iff' hfx hgx]

theorem continuousOn_toNNReal : ContinuousOn ENNReal.toNNReal { a | a ≠ ∞ } := fun _a ha =>
  ContinuousAt.continuousWithinAt (tendsto_toNNReal ha)

theorem tendsto_toReal {a : ℝ≥0∞} (ha : a ≠ ∞) : Tendsto ENNReal.toReal (𝓝 a) (𝓝 a.toReal) :=
  NNReal.tendsto_coe.2 <| tendsto_toNNReal ha

lemma continuousOn_toReal : ContinuousOn ENNReal.toReal { a | a ≠ ∞ } :=
  NNReal.continuous_coe.comp_continuousOn continuousOn_toNNReal

lemma continuousAt_toReal (hx : x ≠ ∞) : ContinuousAt ENNReal.toReal x :=
  continuousOn_toReal.continuousAt (isOpen_ne_top.mem_nhds_iff.mpr hx)

/-- The set of finite `ℝ≥0∞` numbers is homeomorphic to `ℝ≥0`. -/
def neTopHomeomorphNNReal : { a | a ≠ ∞ } ≃ₜ ℝ≥0 where
  toEquiv := neTopEquivNNReal
  continuous_toFun := continuousOn_iff_continuous_domRestrict.1 continuousOn_toNNReal
  continuous_invFun := continuous_coe.subtype_mk _

/-- The set of finite `ℝ≥0∞` numbers is homeomorphic to `ℝ≥0`. -/
def ltTopHomeomorphNNReal : { a | a < ∞ } ≃ₜ ℝ≥0 := by
  refine (Homeomorph.setCongr ?_).trans neTopHomeomorphNNReal
  simp only [lt_top_iff_ne_top]

theorem nhds_top : 𝓝 ∞ = ⨅ (a) (_ : a ≠ ∞), 𝓟 (Ioi a) :=
  nhds_top_order.trans <| by simp [lt_top_iff_ne_top, Ioi]

theorem nhds_top' : 𝓝 ∞ = ⨅ r : ℝ≥0, 𝓟 (Ioi ↑r) :=
  nhds_top.trans <| iInf_ne_top _

theorem nhds_top_basis : (𝓝 ∞).HasBasis (fun a => a < ∞) fun a => Ioi a :=
  _root_.nhds_top_basis

theorem tendsto_nhds_top_iff_nnreal {m : α → ℝ≥0∞} {f : Filter α} :
    Tendsto m f (𝓝 ∞) ↔ ∀ x : ℝ≥0, ∀ᶠ a in f, ↑x < m a := by
  simp only [nhds_top', tendsto_iInf, tendsto_principal, mem_Ioi]

theorem tendsto_nhds_top_iff_nat {m : α → ℝ≥0∞} {f : Filter α} :
    Tendsto m f (𝓝 ∞) ↔ ∀ n : ℕ, ∀ᶠ a in f, ↑n < m a :=
  tendsto_nhds_top_iff_nnreal.trans
    ⟨fun h n => by simpa only [ENNReal.coe_natCast] using h n, fun h x =>
      let ⟨n, hn⟩ := exists_nat_gt x
      (h n).mono fun _ => lt_trans <| by rwa [← ENNReal.coe_natCast, coe_lt_coe]⟩

theorem tendsto_nhds_top {m : α → ℝ≥0∞} {f : Filter α} (h : ∀ n : ℕ, ∀ᶠ a in f, ↑n < m a) :
    Tendsto m f (𝓝 ∞) :=
  tendsto_nhds_top_iff_nat.2 h

theorem tendsto_nat_nhds_top : Tendsto (fun n : ℕ => ↑n) atTop (𝓝 ∞) :=
  tendsto_nhds_top fun n =>
    mem_atTop_sets.2 ⟨n + 1, fun _m hm => mem_ofPred.2 <| Nat.cast_lt.2 <| Nat.lt_of_succ_le hm⟩

@[simp, norm_cast]
theorem tendsto_coe_nhds_top {f : α → ℝ≥0} {l : Filter α} :
    Tendsto (fun x => (f x : ℝ≥0∞)) l (𝓝 ∞) ↔ Tendsto f l atTop := by
  rw [tendsto_nhds_top_iff_nnreal, atTop_basis_Ioi.tendsto_right_iff]; simp

@[simp]
theorem tendsto_ofReal_nhds_top {f : α → ℝ} {l : Filter α} :
    Tendsto (fun x ↦ ENNReal.ofReal (f x)) l (𝓝 ∞) ↔ Tendsto f l atTop :=
  tendsto_coe_nhds_top.trans Real.tendsto_toNNReal_atTop_iff

theorem tendsto_ofReal_atTop : Tendsto ENNReal.ofReal atTop (𝓝 ∞) :=
  tendsto_ofReal_nhds_top.2 tendsto_id

theorem nhds_zero : 𝓝 (0 : ℝ≥0∞) = ⨅ (a) (_ : a ≠ 0), 𝓟 (Iio a) :=
  nhds_bot_order.trans <| by simp [pos_iff_ne_zero, Iio]

theorem nhds_zero_basis : (𝓝 (0 : ℝ≥0∞)).HasBasis (fun a : ℝ≥0∞ => 0 < a) fun a => Iio a :=
  nhds_bot_basis

theorem nhds_zero_basis_Iic : (𝓝 (0 : ℝ≥0∞)).HasBasis (fun a : ℝ≥0∞ => 0 < a) Iic :=
  nhds_bot_basis_Iic

-- TODO: add a TC for `≠ ∞`?
@[instance]
theorem nhdsGT_coe_neBot {r : ℝ≥0} : (𝓝[>] (r : ℝ≥0∞)).NeBot :=
  nhdsGT_neBot_of_exists_gt ⟨∞, ENNReal.coe_lt_top⟩

@[instance] theorem nhdsGT_zero_neBot : (𝓝[>] (0 : ℝ≥0∞)).NeBot := nhdsGT_coe_neBot

@[instance] theorem nhdsGT_one_neBot : (𝓝[>] (1 : ℝ≥0∞)).NeBot := nhdsGT_coe_neBot

@[instance] theorem nhdsGT_nat_neBot (n : ℕ) : (𝓝[>] (n : ℝ≥0∞)).NeBot := nhdsGT_coe_neBot

@[instance]
theorem nhdsGT_ofNat_neBot (n : ℕ) [n.AtLeastTwo] : (𝓝[>] (OfNat.ofNat n : ℝ≥0∞)).NeBot :=
  nhdsGT_coe_neBot

@[instance]
theorem nhdsLT_neBot [NeZero x] : (𝓝[<] x).NeBot :=
  nhdsLT_neBot_of_exists_lt ⟨0, NeZero.pos x⟩

/-- Closed intervals `Set.Icc (monus x ε) (x + ε)`, `ε ≠ 0`, form a basis of neighborhoods of an
extended nonnegative real number `x ≠ ∞`. We use `Set.Icc` instead of `Set.Ioo` because this way the
statement works for `x = 0`.
-/
theorem hasBasis_nhds_of_ne_top' (xt : x ≠ ∞) :
    (𝓝 x).HasBasis (· ≠ 0) (fun ε => Icc (monus x ε) (x + ε)) := by
  rcases eq_zero_or_pos x with rfl | x0
  · simp_rw [zero_monus, zero_add, ← bot_eq_zero, Icc_bot, ← bot_lt_iff_ne_bot]
    exact nhds_bot_basis_Iic
  · refine (nhds_basis_Ioo' ⟨_, x0⟩ ⟨_, xt.lt_top⟩).to_hasBasis ?_ fun ε ε0 => ?_
    · rintro ⟨a, b⟩ ⟨ha, hb⟩
      rcases exists_between (monus_pos_of_lt ha) with ⟨ε, ε0, hε⟩
      rcases lt_iff_exists_add_pos_lt.1 hb with ⟨δ, δ0, hδ⟩
      refine ⟨min ε δ, (lt_min ε0 (coe_pos.2 δ0)).ne', Icc_subset_Ioo ?_ ?_⟩
      · exact lt_monus_comm.2 ((min_le_left _ _).trans_lt hε)
      · grw [min_le_right]
        exact hδ
    · exact ⟨(monus x ε, x + ε), ⟨ENNReal.monus_lt_self xt x0.ne' ε0,
        lt_add_right xt ε0⟩, Ioo_subset_Icc_self⟩

theorem hasBasis_nhds_of_ne_top (xt : x ≠ ∞) :
    (𝓝 x).HasBasis (0 < ·) (fun ε => Icc (monus x ε) (x + ε)) := by
  simpa only [pos_iff_ne_zero] using hasBasis_nhds_of_ne_top' xt

theorem Icc_mem_nhds (xt : x ≠ ∞) (ε0 : ε ≠ 0) : Icc (monus x ε) (x + ε) ∈ 𝓝 x :=
  (hasBasis_nhds_of_ne_top' xt).mem_of_mem ε0

theorem nhds_of_ne_top (xt : x ≠ ∞) : 𝓝 x = ⨅ ε > 0, 𝓟 (Icc (monus x ε) (x + ε)) :=
  (hasBasis_nhds_of_ne_top xt).eq_biInf

theorem biInf_le_nhds : ∀ x : ℝ≥0∞, ⨅ ε > 0, 𝓟 (Icc (monus x ε) (x + ε)) ≤ 𝓝 x
  | ∞ => iInf₂_le_of_le 1 one_pos <| by
    simpa only [← coe_one, top_monus_coe, top_add, Icc_self, principal_singleton] using
      pure_le_nhds _
  | (x : ℝ≥0) => (nhds_of_ne_top coe_ne_top).ge

protected theorem tendsto_nhds_of_Icc {f : Filter α} {u : α → ℝ≥0∞} {a : ℝ≥0∞}
    (h : ∀ ε > 0, ∀ᶠ x in f, u x ∈ Icc (monus a ε) (a + ε)) : Tendsto u f (𝓝 a) := by
  refine Tendsto.mono_right ?_ (biInf_le_nhds _)
  simpa only [tendsto_iInf, tendsto_principal]

/-- Characterization of neighborhoods for `ℝ≥0∞` numbers. See also `tendsto_order`
for a version with strict inequalities. -/
protected theorem tendsto_nhds {f : Filter α} {u : α → ℝ≥0∞} {a : ℝ≥0∞} (ha : a ≠ ∞) :
    Tendsto u f (𝓝 a) ↔ ∀ ε > 0, ∀ᶠ x in f, u x ∈ Icc (monus a ε) (a + ε) := by
  simp only [nhds_of_ne_top ha, tendsto_iInf, tendsto_principal]

protected theorem tendsto_nhds_zero {f : Filter α} {u : α → ℝ≥0∞} :
    Tendsto u f (𝓝 0) ↔ ∀ ε > 0, ∀ᶠ x in f, u x ≤ ε :=
  nhds_zero_basis_Iic.tendsto_right_iff

theorem tendsto_const_monus_nhds_zero_iff {l : Filter α} {f : α → ℝ≥0∞} {a : ℝ≥0∞} (ha : a ≠ ∞)
    (hfa : ∀ n, f n ≤ a) :
    Tendsto (fun n ↦ monus a (f n)) l (𝓝 0) ↔ Tendsto (fun n ↦ f n) l (𝓝 a) := by
  rw [ENNReal.tendsto_nhds_zero, ENNReal.tendsto_nhds ha]
  refine ⟨fun h ε hε ↦ ?_, fun h ε hε ↦ ?_⟩
  · filter_upwards [h ε hε] with n hn
    refine ⟨?_, (hfa n).trans (le_add_right le_rfl)⟩
    rw [monus_le_iff] at hn ⊢
    rwa [add_comm]
  · filter_upwards [h ε hε] with n hn
    have hN_left := hn.1
    rw [monus_le_iff] at hN_left ⊢
    rwa [add_comm]

protected theorem tendsto_atTop [Nonempty β] [SemilatticeSup β] {f : β → ℝ≥0∞} {a : ℝ≥0∞}
    (ha : a ≠ ∞) : Tendsto f atTop (𝓝 a) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, f n ∈ Icc (monus a ε) (a + ε) :=
  .trans (atTop_basis.tendsto_iff (hasBasis_nhds_of_ne_top ha)) (by simp only [true_and]; rfl)

protected theorem tendsto_atTop_zero [Nonempty β] [SemilatticeSup β] {f : β → ℝ≥0∞} :
    Tendsto f atTop (𝓝 0) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, f n ≤ ε :=
  .trans (atTop_basis.tendsto_iff nhds_zero_basis_Iic) (by simp only [true_and]; rfl)

theorem tendsto_atTop_zero_iff_le_of_antitone {β : Type*} [Nonempty β] [SemilatticeSup β]
    {f : β → ℝ≥0∞} (hf : Antitone f) :
    Filter.Tendsto f Filter.atTop (𝓝 0) ↔ ∀ ε, 0 < ε → ∃ n : β, f n ≤ ε := by
  rw [ENNReal.tendsto_atTop_zero]
  refine ⟨fun h ↦ fun ε hε ↦ ?_, fun h ↦ fun ε hε ↦ ?_⟩
  · obtain ⟨n, hn⟩ := h ε hε
    exact ⟨n, hn n le_rfl⟩
  · obtain ⟨n, hn⟩ := h ε hε
    exact ⟨n, fun m hm ↦ (hf hm).trans hn⟩

theorem tendsto_atTop_zero_iff_lt_of_antitone {β : Type*} [Nonempty β] [SemilatticeSup β]
    {f : β → ℝ≥0∞} (hf : Antitone f) :
    Filter.Tendsto f Filter.atTop (𝓝 0) ↔ ∀ ε, 0 < ε → ∃ n : β, f n < ε := by
  rw [ENNReal.tendsto_atTop_zero_iff_le_of_antitone hf]
  constructor <;> intro h ε hε
  · obtain ⟨δ, hδ, hδε⟩ := exists_between hε
    obtain ⟨n, hn⟩ := h δ hδ
    exact ⟨n, hn.trans_lt hδε⟩
  · obtain ⟨n, hn⟩ := h ε hε
    exact ⟨n, hn.le⟩

theorem tendsto_monus : ∀ {a b : ℝ≥0∞}, (a ≠ ∞ ∨ b ≠ ∞) →
    Tendsto (fun p : ℝ≥0∞ × ℝ≥0∞ => monus p.1 p.2) (𝓝 (a, b)) (𝓝 (monus a b))
  | ∞, ∞, h => by simp only [ne_eq, not_true_eq_false, or_self] at h
  | ∞, (b : ℝ≥0), _ => by
    rw [top_monus_coe, tendsto_nhds_top_iff_nnreal]
    refine fun x => ((lt_mem_nhds <| @coe_lt_top (b + 1 + x)).prod_nhds
      (ge_mem_nhds <| coe_lt_coe.2 <| lt_add_one b)).mono fun y hy => ?_
    grw [lt_monus_iff_add_lt_left, hy.2]
    exact hy.1
  | (a : ℝ≥0), ∞, _ => by
    rw [monus_top]
    refine (tendsto_pure.2 ?_).mono_right (pure_le_nhds _)
    exact ((gt_mem_nhds <| coe_lt_coe.2 <| lt_add_one a).prod_nhds
      (lt_mem_nhds <| @coe_lt_top (a + 1))).mono fun x hx =>
        monus_eq_zero_iff_le.2 (hx.1.trans hx.2).le
  | (a : ℝ≥0), (b : ℝ≥0), _ => by
    simp only [nhds_coe_coe, tendsto_map'_iff, ← ENNReal.coe_monus, Function.comp_def, tendsto_coe]
    exact continuous_sub.tendsto (a, b)

protected theorem Tendsto.monus {f : Filter α} {ma : α → ℝ≥0∞} {mb : α → ℝ≥0∞} {a b : ℝ≥0∞}
    (hma : Tendsto ma f (𝓝 a)) (hmb : Tendsto mb f (𝓝 b)) (h : a ≠ ∞ ∨ b ≠ ∞) :
    Tendsto (fun a => monus (ma a) (mb a)) f (𝓝 (monus a b)) :=
  Tendsto.comp (ENNReal.tendsto_monus h) (hma.prodMk_nhds hmb)

protected theorem tendsto_mul (ha : a ≠ 0 ∨ b ≠ ∞) (hb : b ≠ 0 ∨ a ≠ ∞) :
    Tendsto (fun p : ℝ≥0∞ × ℝ≥0∞ => p.1 * p.2) (𝓝 (a, b)) (𝓝 (a * b)) := by
  have ht : ∀ b : ℝ≥0∞, b ≠ 0 →
      Tendsto (fun p : ℝ≥0∞ × ℝ≥0∞ => p.1 * p.2) (𝓝 (∞, b)) (𝓝 ∞) := fun b hb => by
    refine tendsto_nhds_top_iff_nnreal.2 fun n => ?_
    rcases lt_iff_exists_nnreal_btwn.1 (pos_iff_ne_zero.2 hb) with ⟨ε, hε, hεb⟩
    have he₀ : (ε : ℝ≥0∞) ≠ 0 := hε.ne'
    have hfin : (n : ℝ≥0∞) * (ε : ℝ≥0∞)⁻¹ ≠ ∞ :=
      ENNReal.mul_ne_top coe_ne_top (ENNReal.inv_ne_top.2 he₀)
    have hc : ∀ᶠ c : ℝ≥0∞ × ℝ≥0∞ in 𝓝 (∞, b),
        (n : ℝ≥0∞) * (ε : ℝ≥0∞)⁻¹ < c.1 ∧ (ε : ℝ≥0∞) < c.2 :=
      (lt_mem_nhds hfin.lt_top).prod_nhds (lt_mem_nhds hεb)
    refine hc.mono fun c h => ?_
    calc
      (n : ℝ≥0∞) = ((n : ℝ≥0∞) * (ε : ℝ≥0∞)⁻¹) * ε := by
        rw [mul_assoc, ENNReal.inv_mul_cancel he₀ coe_ne_top, mul_one]
      _ < c.1 * c.2 := mul_lt_mul h.1 h.2
  induction a with
  | top => simp only [ne_eq, or_false, not_true_eq_false] at hb; simp [ht b hb, top_mul hb]
  | coe a =>
    induction b with
    | top =>
      simp only [ne_eq, or_false, not_true_eq_false] at ha
      simpa [Function.comp_def, mul_comm, mul_top ha]
        using (ht a ha).comp (continuous_swap.tendsto (ofNNReal a, ∞))
    | coe b =>
      simp only [nhds_coe_coe, ← coe_mul, tendsto_coe, tendsto_map'_iff, Function.comp_def,
        tendsto_mul]

protected theorem Tendsto.mul {f : Filter α} {ma : α → ℝ≥0∞} {mb : α → ℝ≥0∞} {a b : ℝ≥0∞}
    (hma : Tendsto ma f (𝓝 a)) (ha : a ≠ 0 ∨ b ≠ ∞) (hmb : Tendsto mb f (𝓝 b))
    (hb : b ≠ 0 ∨ a ≠ ∞) : Tendsto (fun a => ma a * mb a) f (𝓝 (a * b)) :=
  show Tendsto ((fun p : ℝ≥0∞ × ℝ≥0∞ => p.1 * p.2) ∘ fun a => (ma a, mb a)) f (𝓝 (a * b)) from
    Tendsto.comp (ENNReal.tendsto_mul ha hb) (hma.prodMk_nhds hmb)

theorem _root_.ContinuousOn.ennreal_mul [TopologicalSpace α] {f g : α → ℝ≥0∞} {s : Set α}
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) (h₁ : ∀ x ∈ s, f x ≠ 0 ∨ g x ≠ ∞)
    (h₂ : ∀ x ∈ s, g x ≠ 0 ∨ f x ≠ ∞) : ContinuousOn (fun x => f x * g x) s := fun x hx =>
  ENNReal.Tendsto.mul (hf x hx) (h₁ x hx) (hg x hx) (h₂ x hx)

theorem _root_.Continuous.ennreal_mul [TopologicalSpace α] {f g : α → ℝ≥0∞} (hf : Continuous f)
    (hg : Continuous g) (h₁ : ∀ x, f x ≠ 0 ∨ g x ≠ ∞) (h₂ : ∀ x, g x ≠ 0 ∨ f x ≠ ∞) :
    Continuous fun x => f x * g x :=
  continuous_iff_continuousAt.2 fun x =>
    ENNReal.Tendsto.mul hf.continuousAt (h₁ x) hg.continuousAt (h₂ x)

protected theorem Tendsto.const_mul {f : Filter α} {m : α → ℝ≥0∞} {a b : ℝ≥0∞}
    (hm : Tendsto m f (𝓝 b)) (hb : b ≠ 0 ∨ a ≠ ∞) : Tendsto (fun b => a * m b) f (𝓝 (a * b)) :=
  by_cases (fun (this : a = 0) => by simp [this, tendsto_const_nhds]) fun ha : a ≠ 0 =>
    ENNReal.Tendsto.mul tendsto_const_nhds (Or.inl ha) hm hb

protected theorem Tendsto.mul_const {f : Filter α} {m : α → ℝ≥0∞} {a b : ℝ≥0∞}
    (hm : Tendsto m f (𝓝 a)) (ha : a ≠ 0 ∨ b ≠ ∞) : Tendsto (fun x => m x * b) f (𝓝 (a * b)) := by
  simpa only [mul_comm] using ENNReal.Tendsto.const_mul hm ha

theorem tendsto_finsetProd_of_ne_top {ι : Type*} {f : ι → α → ℝ≥0∞} {x : Filter α} {a : ι → ℝ≥0∞}
    (s : Finset ι) (h : ∀ i ∈ s, Tendsto (f i) x (𝓝 (a i))) (h' : ∀ i ∈ s, a i ≠ ∞) :
    Tendsto (fun b => ∏ c ∈ s, f c b) x (𝓝 (∏ c ∈ s, a c)) := by
  classical
  induction s using Finset.induction with
  | empty => simp [tendsto_const_nhds]
  | insert _ _ has IH =>
    simp only [Finset.prod_insert has]
    apply Tendsto.mul (h _ (Finset.mem_insert_self _ _))
    · right
      exact prod_ne_top fun i hi => h' _ (Finset.mem_insert_of_mem hi)
    · exact IH (fun i hi => h _ (Finset.mem_insert_of_mem hi)) fun i hi =>
        h' _ (Finset.mem_insert_of_mem hi)
    · exact Or.inr (h' _ (Finset.mem_insert_self _ _))

@[deprecated (since := "2026-04-08")]
alias tendsto_finset_prod_of_ne_top := tendsto_finsetProd_of_ne_top

protected theorem continuousAt_const_mul {a b : ℝ≥0∞} (h : a ≠ ∞ ∨ b ≠ 0) :
    ContinuousAt (a * ·) b :=
  Tendsto.const_mul tendsto_id h.symm

protected theorem continuousAt_mul_const {a b : ℝ≥0∞} (h : a ≠ ∞ ∨ b ≠ 0) :
    ContinuousAt (fun x => x * a) b :=
  Tendsto.mul_const tendsto_id h.symm

@[fun_prop]
protected theorem continuous_const_mul {a : ℝ≥0∞} (ha : a ≠ ∞) : Continuous (a * ·) :=
  continuous_iff_continuousAt.2 fun _ => ENNReal.continuousAt_const_mul (Or.inl ha)

@[fun_prop]
protected theorem continuous_mul_const {a : ℝ≥0∞} (ha : a ≠ ∞) : Continuous fun x => x * a :=
  continuous_iff_continuousAt.2 fun _ => ENNReal.continuousAt_mul_const (Or.inl ha)

@[fun_prop]
protected theorem continuous_div_const (c : ℝ≥0∞) (hc₀ : c ≠ 0) (hct : c ≠ ∞) :
    Continuous fun x : ℝ≥0∞ => ENNReal.div x c ⟨hc₀, Or.inr hct⟩ :=
  ENNReal.continuous_mul_const (ENNReal.inv_ne_top.2 hc₀)

@[fun_prop]
protected theorem continuous_divInf_const (c : ℝ≥0∞) (hc₀ : c ≠ 0) :
    Continuous fun x : ℝ≥0∞ => ENNReal.divInf x c :=
  ENNReal.continuous_mul_const (ENNReal.inv_ne_top.2 hc₀)

@[continuity, fun_prop]
protected theorem continuous_pow (n : ℕ) : Continuous fun a : ℝ≥0∞ => a ^ n := by
  induction n with
  | zero => simp [continuous_const]
  | succ n IH =>
    simp_rw [pow_add, pow_one, continuous_iff_continuousAt]
    intro x
    refine ENNReal.Tendsto.mul (IH.tendsto _) ?_ tendsto_id ?_ <;> by_cases H : x = 0
    · simp only [H, zero_ne_top, Ne, or_true, not_false_iff]
    · exact Or.inl fun h => H (eq_zero_of_pow_eq_zero h)
    · simp only [H, pow_eq_top_iff, zero_ne_top, false_or, not_true, Ne,
        not_false_iff, false_and]
    · simp only [H, true_or, Ne, not_false_iff]

theorem continuousOn_monus :
    ContinuousOn (fun p : ℝ≥0∞ × ℝ≥0∞ => monus p.fst p.snd) { p : ℝ≥0∞ × ℝ≥0∞ | p ≠ ⟨∞, ∞⟩ } := by
  rw [ContinuousOn]
  rintro ⟨x, y⟩ hp
  simp only [Ne, Set.mem_ofPred_eq, Prod.mk_inj] at hp
  exact tendsto_nhdsWithin_of_tendsto_nhds (tendsto_monus (not_and_or.mp hp))

theorem continuous_monus_left {a : ℝ≥0∞} (a_ne_top : a ≠ ∞) : Continuous (monus a) := by
  change Continuous (Function.uncurry monus ∘ (a, ·))
  refine continuousOn_monus.comp_continuous (.prodMk_right a) fun x => ?_
  simp only [a_ne_top, Ne, mem_ofPred_eq, Prod.mk_inj, false_and, not_false_iff]

theorem continuous_nnreal_monus {a : ℝ≥0} : Continuous fun x : ℝ≥0∞ => monus a x :=
  continuous_monus_left coe_ne_top

theorem continuousOn_monus_left (a : ℝ≥0∞) : ContinuousOn (monus a) { x : ℝ≥0∞ | x ≠ ∞ } := by
  change ContinuousOn (Function.uncurry monus ∘ (a, ·)) _
  apply continuousOn_monus.comp (by fun_prop)
  rintro _ h (_ | _)
  exact h none_eq_top

theorem continuous_monus_right (a : ℝ≥0∞) : Continuous fun x : ℝ≥0∞ => monus x a := by
  by_cases a_infty : a = ∞
  · simp [a_infty, continuous_const, monus_eq_zero_of_le]
  · change Continuous (Function.uncurry monus ∘ (·, a))
    apply continuousOn_monus.comp_continuous (by fun_prop)
    intro x
    simp only [a_infty, Ne, mem_ofPred_eq, Prod.mk_inj, and_false, not_false_iff]

protected theorem Tendsto.pow {f : Filter α} {m : α → ℝ≥0∞} {a : ℝ≥0∞} {n : ℕ}
    (hm : Tendsto m f (𝓝 a)) : Tendsto (fun x => m x ^ n) f (𝓝 (a ^ n)) :=
  ((ENNReal.continuous_pow n).tendsto a).comp hm

theorem le_of_forall_lt_one_mul_le {x y : ℝ≥0∞} (h : ∀ a < 1, a * x ≤ y) : x ≤ y := by
  have : Tendsto (· * x) (𝓝[<] 1) (𝓝 (1 * x)) :=
    (ENNReal.continuousAt_mul_const (Or.inr one_ne_zero)).mono_left inf_le_left
  rw [one_mul] at this
  exact le_of_tendsto this (eventually_nhdsWithin_iff.2 <| Eventually.of_forall h)

theorem inv_limsup {ι : Sort _} {x : ι → ℝ≥0∞} {l : Filter ι} :
    (limsup x l)⁻¹ = liminf (fun i => (x i)⁻¹) l :=
  OrderIso.invENNReal.limsup_apply

theorem inv_liminf {ι : Sort _} {x : ι → ℝ≥0∞} {l : Filter ι} :
    (liminf x l)⁻¹ = limsup (fun i => (x i)⁻¹) l :=
  OrderIso.invENNReal.liminf_apply

@[fun_prop]
protected theorem continuous_zpow : ∀ n : ℤ, Continuous (· ^ n : ℝ≥0∞ → ℝ≥0∞)
  | (n : ℕ) => by
      simpa only [ENNReal.zpow_natCast] using ENNReal.continuous_pow n
  | .negSucc n => by
      simpa only [ENNReal.zpow_negSucc] using (ENNReal.continuous_pow (n + 1)).fun_inv

protected theorem Tendsto.extendedDiv {f : Filter α} {u v : α → ℝ≥0∞} {a b : ℝ≥0∞}
    (hu : Tendsto u f (𝓝 a)) (hv : Tendsto v f (𝓝 b))
    (huv : ∀ i, (u i ≠ 0 ∨ v i ≠ 0) ∧ (u i ≠ ∞ ∨ v i ≠ ∞))
    (hab : (a ≠ 0 ∨ b ≠ 0) ∧ (a ≠ ∞ ∨ b ≠ ∞)) :
    Tendsto (fun i => extendedDiv (u i) (v i) (huv i)) f (𝓝 (extendedDiv a b hab)) := by
  change Tendsto (fun i => u i * (v i)⁻¹) f (𝓝 (a * b⁻¹))
  apply ENNReal.Tendsto.mul hu _ (tendsto_inv_iff.2 hv) _
  · simpa using hab.1
  · simpa only [ENNReal.inv_ne_zero] using hab.2.symm

protected theorem Tendsto.div {f : Filter α} {u v : α → ℝ≥0∞} {a b : ℝ≥0∞}
    (hu : Tendsto u f (𝓝 a)) (hv : Tendsto v f (𝓝 b))
    (huv : ∀ i, v i ≠ 0 ∧ (u i ≠ ∞ ∨ v i ≠ ∞)) (hab : b ≠ 0 ∧ (a ≠ ∞ ∨ b ≠ ∞)) :
    Tendsto (fun i => ENNReal.div (u i) (v i) (huv i)) f (𝓝 (ENNReal.div a b hab)) :=
  ENNReal.Tendsto.extendedDiv hu hv
    (fun i => ⟨Or.inr (huv i).1, (huv i).2⟩) ⟨Or.inr hab.1, hab.2⟩

@[fun_prop]
protected theorem continuous_extendedDiv :
    Continuous (fun p : {p : ℝ≥0∞ × ℝ≥0∞ //
      (p.1 ≠ 0 ∨ p.2 ≠ 0) ∧ (p.1 ≠ ∞ ∨ p.2 ≠ ∞)} =>
      extendedDiv p.val.1 p.val.2 p.property) := by
  apply continuous_iff_continuousAt.2
  intro p
  exact ENNReal.Tendsto.extendedDiv
    ((continuous_fst.comp continuous_subtype_val).tendsto p)
    ((continuous_snd.comp continuous_subtype_val).tendsto p)
    (fun q => q.property) p.property

@[fun_prop]
protected theorem continuous_div :
    Continuous (fun p : {p : ℝ≥0∞ × ℝ≥0∞ // p.2 ≠ 0 ∧ (p.1 ≠ ∞ ∨ p.2 ≠ ∞)} =>
      ENNReal.div p.val.1 p.val.2 p.property) := by
  apply continuous_iff_continuousAt.2
  intro p
  exact ENNReal.Tendsto.div
    ((continuous_fst.comp continuous_subtype_val).tendsto p)
    ((continuous_snd.comp continuous_subtype_val).tendsto p)
    (fun q => q.property) p.property

/-- Any function agreeing with ordinary division on pairs of positive finite inputs fails to be
continuous at `(0, 0)` and `(∞, ∞)`. The paths `(c * t, t)` have different limiting quotients
as the positive finite multiplier `c` varies. -/
theorem not_continuousAt_div_endpoint (F : ℝ≥0∞ × ℝ≥0∞ → ℝ≥0∞)
    (hF : ∀ a b : ℝ≥0∞, 0 < a → a < ∞ → ∀ (hb : 0 < b) (hbt : b < ∞),
      F (a, b) = div a b ⟨hb.ne', Or.inr hbt.ne⟩)
    (x : ℝ≥0∞) (hx : x = 0 ∨ x = ∞) : ¬ ContinuousAt F (x, x) := by
  let s := Ioo (0 : ℝ≥0∞) ∞
  have : NeBot (𝓝[s] x) := by
    rcases hx with rfl | rfl
    · exact left_nhdsWithin_Ioo_neBot ENNReal.zero_lt_top
    · exact right_nhdsWithin_Ioo_neBot ENNReal.zero_lt_top
  intro hcont
  have hlim (c : ℝ≥0∞) (hc₀ : c ≠ 0) (hct : c ≠ ∞) : F (x, x) = c := by
    have hcx : c * x = x := by
      rcases hx with rfl | rfl
      · exact mul_zero _
      · exact mul_top hc₀
    have ht : Tendsto (fun t : ℝ≥0∞ => t) (𝓝[s] x) (𝓝 x) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hp : Tendsto (fun t => (c * t, t)) (𝓝[s] x) (𝓝 (x, x)) := by
      simpa only [hcx] using
        (((ENNReal.continuous_const_mul hct).tendsto x).mono_left
          nhdsWithin_le_nhds).prodMk_nhds ht
    have he : (fun _ : ℝ≥0∞ => c) =ᶠ[𝓝[s] x] fun t => F (c * t, t) :=
      (show ∀ᶠ t in 𝓝[s] x, t ∈ s from self_mem_nhdsWithin).mono fun t ht => by
        change c = F (c * t, t)
        rw [hF _ _ (ENNReal.mul_pos hc₀ ht.1.ne') (mul_lt_top hct.lt_top ht.2) ht.1 ht.2,
          ENNReal.mul_div_cancel_right ht.1.ne' ht.2.ne]
    exact tendsto_nhds_unique (hcont.tendsto.comp hp) (tendsto_const_nhds.congr' he)
  exact ENNReal.one_lt_two.ne <| (hlim 1 one_ne_zero one_ne_top).symm.trans
    (hlim 2 two_ne_zero ofNat_ne_top)

protected theorem Tendsto.divInf {f : Filter α} {u v : α → ℝ≥0∞} {a b : ℝ≥0∞}
    (hu : Tendsto u f (𝓝 a)) (hv : Tendsto v f (𝓝 b)) (hab : (a ≠ 0 ∨ b ≠ 0) ∧ (a ≠ ∞ ∨ b ≠ ∞)) :
    Tendsto (fun i => divInf (u i) (v i)) f (𝓝 (divInf a b)) := by
  change Tendsto (fun i => u i * (v i)⁻¹) f (𝓝 (a * b⁻¹))
  apply ENNReal.Tendsto.mul hu _ (tendsto_inv_iff.2 hv) _
  · simpa using hab.1
  · simpa only [ENNReal.inv_ne_zero] using hab.2.symm

protected theorem Tendsto.const_divInf {f : Filter α} {m : α → ℝ≥0∞} {a b : ℝ≥0∞}
    (hm : Tendsto m f (𝓝 b)) (hb : b ≠ ∞ ∨ a ≠ ∞) :
    Tendsto (fun i => divInf a (m i)) f (𝓝 (divInf a b)) := by
  change Tendsto (fun i => a * (m i)⁻¹) f (𝓝 (a * b⁻¹))
  apply ENNReal.Tendsto.const_mul (tendsto_inv_iff.2 hm)
  simpa using hb

protected theorem Tendsto.divInf_const {f : Filter α} {m : α → ℝ≥0∞} {a b : ℝ≥0∞}
    (hm : Tendsto m f (𝓝 a)) (ha : a ≠ 0 ∨ b ≠ 0) :
    Tendsto (fun i => divInf (m i) b) f (𝓝 (divInf a b)) := by
  change Tendsto (fun i => m i * b⁻¹) f (𝓝 (a * b⁻¹))
  apply ENNReal.Tendsto.mul_const hm
  simpa using ha

protected theorem tendsto_inv_nat_nhds_zero : Tendsto (fun n : ℕ => (n : ℝ≥0∞)⁻¹) atTop (𝓝 0) :=
  ENNReal.inv_top ▸ tendsto_inv_iff.2 tendsto_nat_nhds_top

protected theorem tendsto_coe_monus {b : ℝ≥0∞} :
    Tendsto (fun b : ℝ≥0∞ => monus r b) (𝓝 b) (𝓝 (monus r b)) :=
  continuous_nnreal_monus.tendsto _

theorem exists_countable_dense_no_zero_top :
    ∃ s : Set ℝ≥0∞, s.Countable ∧ Dense s ∧ 0 ∉ s ∧ ∞ ∉ s := by
  obtain ⟨s, s_count, s_dense, hs⟩ :
    ∃ s : Set ℝ≥0∞, s.Countable ∧ Dense s ∧ (∀ x, IsBot x → x ∉ s) ∧ ∀ x, IsTop x → x ∉ s :=
    exists_countable_dense_no_bot_top ℝ≥0∞
  exact ⟨s, s_count, s_dense, fun h => hs.1 0 (by simp) h, fun h => hs.2 ∞ (by simp) h⟩

end TopologicalSpace

section Liminf

theorem exists_frequently_lt_of_liminf_ne_top {ι : Type*} {l : Filter ι} {x : ι → ℝ}
    (hx : liminf (fun n => (Real.nnabs (x n) : ℝ≥0∞)) l ≠ ∞) : ∃ R, ∃ᶠ n in l, x n < R := by
  by_contra! h
  refine hx (ENNReal.eq_top_of_forall_nnreal_le fun r => le_limsInf_of_le (by isBoundedDefault) ?_)
  simp only [eventually_map, ENNReal.coe_le_coe]
  filter_upwards [h r] with i hi using hi.trans (le_abs_self (x i))

theorem exists_frequently_lt_of_liminf_ne_top' {ι : Type*} {l : Filter ι} {x : ι → ℝ}
    (hx : liminf (fun n => (Real.nnabs (x n) : ℝ≥0∞)) l ≠ ∞) : ∃ R, ∃ᶠ n in l, R < x n := by
  by_contra! h
  refine hx (ENNReal.eq_top_of_forall_nnreal_le fun r => le_limsInf_of_le (by isBoundedDefault) ?_)
  simp only [eventually_map, ENNReal.coe_le_coe]
  filter_upwards [h (-r)] with i hi using (le_neg.1 hi).trans (neg_le_abs _)

theorem exists_upcrossings_of_not_bounded_under {ι : Type*} {l : Filter ι} {x : ι → ℝ}
    (hf : liminf (fun i => (Real.nnabs (x i) : ℝ≥0∞)) l ≠ ∞)
    (hbdd : ¬IsBoundedUnder (· ≤ ·) l fun i => |x i|) :
    ∃ a b : ℚ, a < b ∧ (∃ᶠ i in l, x i < a) ∧ ∃ᶠ i in l, ↑b < x i := by
  rw [isBoundedUnder_le_abs, not_and_or] at hbdd
  obtain hbdd | hbdd := hbdd
  · obtain ⟨R, hR⟩ := exists_frequently_lt_of_liminf_ne_top hf
    obtain ⟨q, hq⟩ := exists_rat_gt R
    refine ⟨q, q + 1, (lt_add_iff_pos_right _).2 zero_lt_one, ?_, ?_⟩
    · refine fun hcon => hR ?_
      filter_upwards [hcon] with x hx using not_lt.2 (lt_of_lt_of_le hq (not_lt.1 hx)).le
    · simp only [IsBoundedUnder, IsBounded, eventually_map, not_exists] at hbdd
      refine fun hcon => hbdd ↑(q + 1) ?_
      filter_upwards [hcon] with x hx using not_lt.1 hx
  · obtain ⟨R, hR⟩ := exists_frequently_lt_of_liminf_ne_top' hf
    obtain ⟨q, hq⟩ := exists_rat_lt R
    refine ⟨q - 1, q, (sub_lt_self_iff _).2 zero_lt_one, ?_, ?_⟩
    · simp only [IsBoundedUnder, IsBounded, eventually_map, not_exists] at hbdd
      refine fun hcon => hbdd ↑(q - 1) ?_
      filter_upwards [hcon] with x hx using not_lt.1 hx
    · refine fun hcon => hR ?_
      filter_upwards [hcon] with x hx using not_lt.2 ((not_lt.1 hx).trans hq.le)

end Liminf

theorem tendsto_toReal_iff {ι} {fi : Filter ι} {f : ι → ℝ≥0∞} (hf : ∀ i, f i ≠ ∞) {x : ℝ≥0∞}
    (hx : x ≠ ∞) : Tendsto (fun n => (f n).toReal) fi (𝓝 x.toReal) ↔ Tendsto f fi (𝓝 x) := by
  lift f to ι → ℝ≥0 using hf
  lift x to ℝ≥0 using hx
  simp [tendsto_coe]

theorem tendsto_toReal_zero_iff {ι} {fi : Filter ι} {f : ι → ℝ≥0∞}
    (hf : ∀ i, f i ≠ ∞ := by finiteness) :
    Tendsto (fun n ↦ (f n).toReal) fi (𝓝 0) ↔ Tendsto f fi (𝓝 0) := by
  rw [← ENNReal.toReal_zero, tendsto_toReal_iff hf ENNReal.zero_ne_top]

end ENNReal

section

variable [EMetricSpace β]

open ENNReal Filter

/-- In an emetric ball, the distance between points is everywhere finite -/
theorem edist_ne_top_of_mem_ball {a : β} {r : ℝ≥0∞} (x y : eball a r) : edist x.1 y.1 ≠ ∞ :=
  ne_of_lt <|
    calc
      edist x y ≤ edist a x + edist a y := edist_triangle_left x.1 y.1 a
      _ < r + r := by rw [edist_comm a x, edist_comm a y]; exact ENNReal.add_lt_add x.2 y.2
      _ ≤ ∞ := le_top

/-- Each ball in an extended metric space gives us a metric space, as the edist
is everywhere finite. -/
@[instance_reducible]
def metricSpaceEMetricBall (a : β) (r : ℝ≥0∞) : MetricSpace (eball a r) :=
  EMetricSpace.toMetricSpace edist_ne_top_of_mem_ball

theorem nhds_eq_nhds_emetric_ball (a x : β) (r : ℝ≥0∞) (h : x ∈ eball a r) :
    𝓝 x = map ((↑) : eball a r → β) (𝓝 ⟨x, h⟩) :=
  (map_nhds_subtype_coe_eq_nhds _ <| isOpen_eball.mem_nhds h).symm

end

section

variable [PseudoEMetricSpace α]

open EMetric

theorem tendsto_iff_edist_tendsto_0 {l : Filter β} {f : β → α} {y : α} :
    Tendsto f l (𝓝 y) ↔ Tendsto (fun x => edist (f x) y) l (𝓝 0) := by
  simp only [Metric.nhds_basis_eball.tendsto_right_iff, Metric.mem_eball,
    @tendsto_order ℝ≥0∞ β _ _, forall_prop_of_false ENNReal.not_lt_zero, forall_const, true_and]

/-- Yet another metric characterization of Cauchy sequences on integers. This one is often the
most efficient. -/
theorem EMetric.cauchySeq_iff_le_tendsto_0 [Nonempty β] [SemilatticeSup β] {s : β → α} :
    CauchySeq s ↔ ∃ b : β → ℝ≥0∞, (∀ n m N : β, N ≤ n → N ≤ m → edist (s n) (s m) ≤ b N) ∧
      Tendsto b atTop (𝓝 0) := EMetric.cauchySeq_iff.trans <| by
  constructor
  · intro hs
    /- `s` is Cauchy sequence. Let `b n` be the diameter of the set `s '' Set.Ici n`. -/
    refine ⟨fun N => Metric.ediam (s '' Ici N), fun n m N hn hm => ?_, ?_⟩
    -- Prove that it bounds the distances of points in the Cauchy sequence
    · exact Metric.edist_le_ediam_of_mem (mem_image_of_mem _ hn) (mem_image_of_mem _ hm)
    -- Prove that it tends to `0`, by using the Cauchy property of `s`
    · refine ENNReal.tendsto_nhds_zero.2 fun ε ε0 => ?_
      rcases hs ε ε0 with ⟨N, hN⟩
      refine (eventually_ge_atTop N).mono fun n hn => Metric.ediam_le ?_
      rintro _ ⟨k, hk, rfl⟩ _ ⟨l, hl, rfl⟩
      exact (hN _ (hn.trans hk) _ (hn.trans hl)).le
  · rintro ⟨b, ⟨b_bound, b_lim⟩⟩ ε εpos
    have : ∀ᶠ n in atTop, b n < ε := b_lim.eventually (gt_mem_nhds εpos)
    rcases this.exists with ⟨N, hN⟩
    refine ⟨N, fun m hm n hn => ?_⟩
    calc edist (s m) (s n) ≤ b N := b_bound m n N hm hn
    _ < ε := hN

theorem continuous_of_le_add_edist {f : α → ℝ≥0∞} (C : ℝ≥0∞) (hC : C ≠ ∞)
    (h : ∀ x y, f x ≤ f y + C * edist x y) : Continuous f := by
  refine continuous_iff_continuousAt.2 fun x => ENNReal.tendsto_nhds_of_Icc fun ε ε0 => ?_
  rcases ENNReal.exists_nnreal_pos_mul_lt hC ε0.ne' with ⟨δ, δ0, hδ⟩
  rw [mul_comm] at hδ
  filter_upwards [Metric.closedEBall_mem_nhds x (ENNReal.coe_pos.2 δ0)] with y hy
  refine ⟨ENNReal.monus_le_iff.2 <| (h x y).trans ?_, (h y x).trans ?_⟩ <;>
    grw [← hδ.le] <;> gcongr
  exacts [Metric.mem_closedEBall'.1 hy, Metric.mem_closedEBall.1 hy]

theorem continuous_edist : Continuous fun p : α × α => edist p.1 p.2 := by
  apply continuous_of_le_add_edist 2 (by decide)
  rintro ⟨x, y⟩ ⟨x', y'⟩
  calc
    edist x y ≤ edist x x' + edist x' y' + edist y' y := edist_triangle4 _ _ _ _
    _ = edist x' y' + (edist x x' + edist y y') := by rw [edist_comm y y']; abel
    _ ≤ edist x' y' + (edist (x, y) (x', y') + edist (x, y) (x', y')) := by
      gcongr <;> apply_rules [le_max_left, le_max_right]
    _ = edist x' y' + 2 * edist (x, y) (x', y') := by rw [← mul_two, mul_comm]

@[continuity, fun_prop]
theorem Continuous.edist [TopologicalSpace β] {f g : β → α} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun b => edist (f b) (g b) :=
  continuous_edist.comp (hf.prodMk hg :)

theorem Filter.Tendsto.edist {f g : β → α} {x : Filter β} {a b : α} (hf : Tendsto f x (𝓝 a))
    (hg : Tendsto g x (𝓝 b)) : Tendsto (fun x => edist (f x) (g x)) x (𝓝 (edist a b)) :=
  (continuous_edist.tendsto (a, b)).comp (hf.prodMk_nhds hg)

theorem Metric.isClosed_closedEBall {a : α} {r : ℝ≥0∞} : IsClosed (closedEBall a r) :=
  isClosed_le (by fun_prop) continuous_const

@[simp]
theorem Metric.ediam_closure (s : Set α) : ediam (closure s) = ediam s := by
  refine le_antisymm (ediam_le fun x hx y hy => ?_) (ediam_mono subset_closure)
  have : edist x y ∈ closure (Iic (ediam s)) :=
    map_mem_closure₂ continuous_edist hx hy fun x hx y hy => edist_le_ediam_of_mem hx hy
  rwa [closure_Iic] at this

@[simp]
theorem Metric.diam_closure {α : Type*} [PseudoMetricSpace α] (s : Set α) :
    Metric.diam (closure s) = diam s := by simp only [Metric.diam, Metric.ediam_closure]

theorem isClosed_setOfPred_lipschitzOnWith {α β} [PseudoEMetricSpace α] [PseudoEMetricSpace β]
    (K : ℝ≥0)
    (s : Set α) : IsClosed { f : α → β | LipschitzOnWith K f s } := by
  simp only [LipschitzOnWith, ofPred_forall]
  refine isClosed_biInter fun x _ => isClosed_biInter fun y _ => isClosed_le ?_ ?_
  exacts [.edist (continuous_apply x) (continuous_apply y), continuous_const]

@[deprecated (since := "2026-07-09")]
alias isClosed_setOf_lipschitzOnWith := isClosed_setOfPred_lipschitzOnWith

theorem isClosed_setOfPred_lipschitzWith {α β} [PseudoEMetricSpace α] [PseudoEMetricSpace β]
    (K : ℝ≥0) :
    IsClosed { f : α → β | LipschitzWith K f } := by
  simp only [← lipschitzOnWith_univ, isClosed_setOfPred_lipschitzOnWith]

@[deprecated (since := "2026-07-09")]
alias isClosed_setOf_lipschitzWith := isClosed_setOfPred_lipschitzWith

protected lemma LipschitzOnWith.closure [PseudoEMetricSpace β] {f : α → β} {s : Set α} {K : ℝ≥0}
    (hcont : ContinuousOn f (closure s)) (hf : LipschitzOnWith K f s) :
    LipschitzOnWith K f (closure s) := by
  have := ENNReal.continuous_const_mul (ENNReal.coe_ne_top (r := K))
  refine fun x hx ↦ le_on_closure (fun y hy ↦ le_on_closure (fun x hx ↦ hf hx hy) ?_ ?_ hx) ?_ ?_
  all_goals fun_prop

lemma lipschitzOnWith_closure_iff [PseudoEMetricSpace β] {f : α → β} {s : Set α} {K : ℝ≥0}
    (hcont : ContinuousOn f (closure s)) :
    LipschitzOnWith K f (closure s) ↔ LipschitzOnWith K f s :=
  ⟨fun hf ↦ hf.mono subset_closure, LipschitzOnWith.closure hcont⟩

namespace Real

/-- For a bounded set `s : Set ℝ`, its `ediam` is equal to `sSup s - sInf s` reinterpreted as
`ℝ≥0∞`. -/
theorem ediam_eq {s : Set ℝ} (h : Bornology.IsBounded s) :
    Metric.ediam s = ENNReal.ofReal (sSup s - sInf s) := by
  rcases eq_empty_or_nonempty s with (rfl | hne)
  · simp
  refine le_antisymm (Metric.ediam_le_of_forall_dist_le fun x hx y hy => ?_) ?_
  · exact Real.dist_le_of_mem_Icc (h.subset_Icc_sInf_sSup hx) (h.subset_Icc_sInf_sSup hy)
  · apply ENNReal.ofReal_le_of_le_toReal
    rw [← Metric.diam, ← Metric.diam_closure]
    calc sSup s - sInf s ≤ dist (sSup s) (sInf s) := le_abs_self _
    _ ≤ Metric.diam (closure s) := dist_le_diam_of_mem h.closure (csSup_mem_closure hne h.bddAbove)
        (csInf_mem_closure hne h.bddBelow)

/-- For a bounded set `s : Set ℝ`, its `Metric.diam` is equal to `sSup s - sInf s`. -/
theorem diam_eq {s : Set ℝ} (h : Bornology.IsBounded s) : Metric.diam s = sSup s - sInf s := by
  rw [Metric.diam, Real.ediam_eq h, ENNReal.toReal_ofReal]
  exact sub_nonneg.2 (Real.sInf_le_sSup s h.bddBelow h.bddAbove)

@[simp]
theorem ediam_Ioo (a b : ℝ) : Metric.ediam (Ioo a b) = ENNReal.ofReal (b - a) := by
  rcases le_or_gt b a with (h | h)
  · simp [h]
  · rw [Real.ediam_eq (isBounded_Ioo _ _), csSup_Ioo h, csInf_Ioo h]

@[simp]
theorem ediam_Icc (a b : ℝ) : Metric.ediam (Icc a b) = ENNReal.ofReal (b - a) := by
  rcases le_or_gt a b with (h | h)
  · rw [Real.ediam_eq (isBounded_Icc _ _), csSup_Icc h, csInf_Icc h]
  · simp [h, h.le]

@[simp]
theorem ediam_Ico (a b : ℝ) : Metric.ediam (Ico a b) = ENNReal.ofReal (b - a) :=
  le_antisymm (ediam_Icc a b ▸ ediam_mono Ico_subset_Icc_self)
    (ediam_Ioo a b ▸ ediam_mono Ioo_subset_Ico_self)

@[simp]
theorem ediam_Ioc (a b : ℝ) : Metric.ediam (Ioc a b) = ENNReal.ofReal (b - a) :=
  le_antisymm (ediam_Icc a b ▸ ediam_mono Ioc_subset_Icc_self)
    (ediam_Ioo a b ▸ ediam_mono Ioo_subset_Ioc_self)

theorem diam_Icc {a b : ℝ} (h : a ≤ b) : Metric.diam (Icc a b) = b - a := by
  simp [Metric.diam, ENNReal.toReal_ofReal (sub_nonneg.2 h)]

theorem diam_Ico {a b : ℝ} (h : a ≤ b) : Metric.diam (Ico a b) = b - a := by
  simp [Metric.diam, ENNReal.toReal_ofReal (sub_nonneg.2 h)]

theorem diam_Ioc {a b : ℝ} (h : a ≤ b) : Metric.diam (Ioc a b) = b - a := by
  simp [Metric.diam, ENNReal.toReal_ofReal (sub_nonneg.2 h)]

theorem diam_Ioo {a b : ℝ} (h : a ≤ b) : Metric.diam (Ioo a b) = b - a := by
  simp [Metric.diam, ENNReal.toReal_ofReal (sub_nonneg.2 h)]

end Real

end

namespace ENNReal

section truncateToReal

/-- With truncation level `t`, the truncated cast `ℝ≥0∞ → ℝ` is given by `x ↦ (min t x).toReal`.
Unlike `ENNReal.toReal`, this cast is continuous and monotone when `t ≠ ∞`. -/
noncomputable def truncateToReal (t x : ℝ≥0∞) : ℝ := (min t x).toReal

lemma truncateToReal_eq_toReal {t x : ℝ≥0∞} (t_ne_top : t ≠ ∞) (x_le : x ≤ t) :
    truncateToReal t x = x.toReal := by
  have x_lt_top : x < ∞ := lt_of_le_of_lt x_le t_ne_top.lt_top
  have obs : min t x ≠ ∞ := by
    simp_all only [ne_eq, min_eq_top, false_and, not_false_eq_true]
  exact (ENNReal.toReal_eq_toReal_iff' obs x_lt_top.ne).mpr (min_eq_right x_le)

lemma truncateToReal_le {t : ℝ≥0∞} (t_ne_top : t ≠ ∞) {x : ℝ≥0∞} :
    truncateToReal t x ≤ t.toReal := by
  rw [truncateToReal]
  gcongr
  exact min_le_left t x

lemma truncateToReal_nonneg {t x : ℝ≥0∞} : 0 ≤ truncateToReal t x := toReal_nonneg

/-- The truncated cast `ENNReal.truncateToReal t : ℝ≥0∞ → ℝ` is monotone when `t ≠ ∞`. -/
lemma monotone_truncateToReal {t : ℝ≥0∞} (t_ne_top : t ≠ ∞) : Monotone (truncateToReal t) := by
  intro x y x_le_y
  simp only [truncateToReal]
  gcongr
  exact ne_top_of_le_ne_top t_ne_top (min_le_left _ _)

/-- The truncated cast `ENNReal.truncateToReal t : ℝ≥0∞ → ℝ` is continuous when `t ≠ ∞`. -/
@[fun_prop]
lemma continuous_truncateToReal {t : ℝ≥0∞} (t_ne_top : t ≠ ∞) : Continuous (truncateToReal t) := by
  apply continuousOn_toReal.comp_continuous (by fun_prop)
  simp [t_ne_top]

end truncateToReal

section LimsupLiminf

variable {ι : Type*} {f : Filter ι} {u v : ι → ℝ≥0∞}

lemma limsup_monus_const (F : Filter ι) (f : ι → ℝ≥0∞) (c : ℝ≥0∞) :
    Filter.limsup (fun i ↦ monus (f i) c) F = monus (Filter.limsup f F) c := by
  rcases F.eq_or_neBot with rfl | _
  · simp
  · exact (Monotone.map_limsSup_of_continuousAt (F := F.map f) (f := fun (x : ℝ≥0∞) ↦ monus x c)
    (fun _ _ h ↦ monus_le_monus h le_rfl) (continuous_monus_right c).continuousAt).symm

lemma liminf_monus_const (F : Filter ι) [NeBot F] (f : ι → ℝ≥0∞) (c : ℝ≥0∞) :
    Filter.liminf (fun i ↦ monus (f i) c) F = monus (Filter.liminf f F) c :=
  (Monotone.map_limsInf_of_continuousAt (F := F.map f) (f := fun (x : ℝ≥0∞) ↦ monus x c)
    (fun _ _ h ↦ monus_le_monus h le_rfl) (continuous_monus_right c).continuousAt).symm

lemma limsup_const_monus (F : Filter ι) (f : ι → ℝ≥0∞) {c : ℝ≥0∞} (c_ne_top : c ≠ ∞) :
    Filter.limsup (fun i ↦ monus c (f i)) F = monus c (Filter.liminf f F) := by
  rcases F.eq_or_neBot with rfl | _
  · simp
  · exact (Antitone.map_limsInf_of_continuousAt (F := F.map f) (f := fun (x : ℝ≥0∞) ↦ monus c x)
    (fun _ _ h ↦ monus_le_monus le_rfl h) (continuous_monus_left c_ne_top).continuousAt).symm

lemma liminf_const_monus (F : Filter ι) [NeBot F] (f : ι → ℝ≥0∞) {c : ℝ≥0∞} (c_ne_top : c ≠ ∞) :
    Filter.liminf (fun i ↦ monus c (f i)) F = monus c (Filter.limsup f F) :=
  (Antitone.map_limsSup_of_continuousAt (F := F.map f) (f := fun (x : ℝ≥0∞) ↦ monus c x)
    (fun _ _ h ↦ monus_le_monus le_rfl h) (continuous_monus_left c_ne_top).continuousAt).symm

lemma le_limsup_mul : limsup u f * liminf v f ≤ limsup (u * v) f :=
  mul_le_of_forall_lt fun a a_u b b_v ↦ (le_limsup_iff).2 fun c c_ab ↦
    Frequently.mono (Frequently.and_eventually ((frequently_lt_of_lt_limsup) a_u)
    ((eventually_lt_of_lt_liminf) b_v)) fun _ ab_x ↦ c_ab.trans (mul_lt_mul ab_x.1 ab_x.2)

/-- See also `ENNReal.limsup_mul_le`. -/
lemma limsup_mul_le' (h : limsup u f ≠ 0 ∨ limsup v f ≠ ∞) (h' : limsup u f ≠ ∞ ∨ limsup v f ≠ 0) :
    limsup (u * v) f ≤ limsup u f * limsup v f := by
  refine le_mul_of_forall_lt h h' fun a a_u b b_v ↦ (limsup_le_iff).2 fun c c_ab ↦ ?_
  filter_upwards [eventually_lt_of_limsup_lt a_u, eventually_lt_of_limsup_lt b_v] with x a_x b_x
  exact (mul_lt_mul a_x b_x).trans c_ab

lemma le_liminf_mul : liminf u f * liminf v f ≤ liminf (u * v) f := by
  refine mul_le_of_forall_lt fun a a_u b b_v ↦ (le_liminf_iff).2 fun c c_ab ↦ ?_
  filter_upwards [eventually_lt_of_lt_liminf a_u, eventually_lt_of_lt_liminf b_v] with x a_x b_x
  exact c_ab.trans (mul_lt_mul a_x b_x)

lemma liminf_mul_le (h : limsup u f ≠ 0 ∨ liminf v f ≠ ∞) (h' : limsup u f ≠ ∞ ∨ liminf v f ≠ 0) :
    liminf (u * v) f ≤ limsup u f * liminf v f :=
  le_mul_of_forall_lt h h' fun a a_u b b_v ↦ (liminf_le_iff).2 fun c c_ab ↦
    Frequently.mono (((frequently_lt_of_liminf_lt) b_v).and_eventually
    ((eventually_lt_of_limsup_lt) a_u)) fun _ ab_x ↦ (mul_lt_mul ab_x.2 ab_x.1).trans c_ab

/-- If `u : ι → ℝ≥0∞` is bounded, then we have `liminf (toReal ∘ u) = toReal (liminf u)`. -/
lemma liminf_toReal_eq [NeBot f] {b : ℝ≥0∞} (b_ne_top : b ≠ ∞) (le_b : ∀ᶠ i in f, u i ≤ b) :
    f.liminf (fun i ↦ (u i).toReal) = (f.liminf u).toReal := by
  have liminf_le : f.liminf u ≤ b := by
    apply liminf_le_of_le ⟨0, by simp⟩
    intro y h
    obtain ⟨i, hi⟩ := (Eventually.and h le_b).exists
    exact hi.1.trans hi.2
  have aux : ∀ᶠ i in f, (u i).toReal = ENNReal.truncateToReal b (u i) := by
    filter_upwards [le_b] with i i_le_b
    simp only [truncateToReal_eq_toReal b_ne_top i_le_b]
  have aux' : (f.liminf u).toReal = ENNReal.truncateToReal b (f.liminf u) := by
    rw [truncateToReal_eq_toReal b_ne_top liminf_le]
  simp_rw [liminf_congr aux, aux']
  have key := Monotone.map_liminf_of_continuousAt (F := f) (monotone_truncateToReal b_ne_top) u
          (continuous_truncateToReal b_ne_top).continuousAt
          (IsBoundedUnder.isCoboundedUnder_ge ⟨b, by simpa only [eventually_map] using le_b⟩)
          ⟨0, Eventually.of_forall (by simp)⟩
  rw [key]
  rfl

/-- If `u : ι → ℝ≥0∞` is bounded, then we have `liminf (toReal ∘ u) = toReal (liminf u)`. -/
lemma limsup_toReal_eq [NeBot f] {b : ℝ≥0∞} (b_ne_top : b ≠ ∞) (le_b : ∀ᶠ i in f, u i ≤ b) :
    f.limsup (fun i ↦ (u i).toReal) = (f.limsup u).toReal := by
  have aux : ∀ᶠ i in f, (u i).toReal = ENNReal.truncateToReal b (u i) := by
    filter_upwards [le_b] with i i_le_b
    simp only [truncateToReal_eq_toReal b_ne_top i_le_b]
  have aux' : (f.limsup u).toReal = ENNReal.truncateToReal b (f.limsup u) := by
    rw [truncateToReal_eq_toReal b_ne_top (limsup_le_of_le ⟨0, by simp⟩ le_b)]
  simp_rw [limsup_congr aux, aux']
  have key := Monotone.map_limsup_of_continuousAt (F := f) (monotone_truncateToReal b_ne_top) u
          (continuous_truncateToReal b_ne_top).continuousAt
          ⟨b, by simpa only [eventually_map] using le_b⟩
          (IsBoundedUnder.isCoboundedUnder_le ⟨0, Eventually.of_forall (by simp)⟩)
  rw [key]
  rfl

@[simp, norm_cast]
lemma ofNNReal_limsup {u : ι → ℝ≥0} (hf : f.IsBoundedUnder (· ≤ ·) u) :
    limsup u f = limsup (fun i ↦ (u i : ℝ≥0∞)) f := by
  refine eq_of_forall_nnreal_le_iff fun r ↦ ?_
  rw [coe_le_coe, le_limsup_iff, le_limsup_iff]
  simp [forall_ennreal]

@[simp, norm_cast]
lemma ofNNReal_liminf {u : ι → ℝ≥0} (hf : f.IsCoboundedUnder (· ≥ ·) u) :
    liminf u f = liminf (fun i ↦ (u i : ℝ≥0∞)) f := by
  refine eq_of_forall_nnreal_le_iff fun r ↦ ?_
  rw [coe_le_coe, le_liminf_iff, le_liminf_iff]
  simp [forall_ennreal]

theorem liminf_add_of_right_tendsto_zero {u : Filter ι} {g : ι → ℝ≥0∞} (hg : u.Tendsto g (𝓝 0))
    (f : ι → ℝ≥0∞) : u.liminf (f + g) = u.liminf f := by
  refine le_antisymm ?_ <| liminf_le_liminf <| .of_forall <| by simp
  refine liminf_le_of_le (by isBoundedDefault) fun b hb ↦ ?_
  rw [Filter.le_liminf_iff']
  rintro a hab
  filter_upwards [hb, ENNReal.tendsto_nhds_zero.1 hg _ <| lt_min (monus_pos_of_lt hab) one_pos]
    with i hfg hg
  exact ENNReal.le_of_add_le_add_right (hg.trans_lt <| by simp).ne <|
    (add_le_of_le_monus_left_of_le hab.le <| hg.trans <| min_le_left ..).trans hfg

theorem liminf_add_of_left_tendsto_zero {u : Filter ι} {f : ι → ℝ≥0∞} (hf : u.Tendsto f (𝓝 0))
    (g : ι → ℝ≥0∞) : u.liminf (f + g) = u.liminf g := by
  rw [add_comm, liminf_add_of_right_tendsto_zero hf]

theorem limsup_add_of_right_tendsto_zero {u : Filter ι} {g : ι → ℝ≥0∞} (hg : u.Tendsto g (𝓝 0))
    (f : ι → ℝ≥0∞) : u.limsup (f + g) = u.limsup f := by
  refine le_antisymm ?_ <| limsup_le_limsup <| .of_forall <| by simp
  refine le_limsup_of_le (by isBoundedDefault) fun b hb ↦ ?_
  rw [Filter.limsup_le_iff']
  rintro a hba
  filter_upwards [hb, ENNReal.tendsto_nhds_zero.1 hg _ <| monus_pos_of_lt hba] with i hf hg
  calc f i + g i
    _ ≤ b + g i := by gcongr
    _ ≤ a := add_le_of_le_monus_left_of_le hba.le hg

theorem limsup_add_of_left_tendsto_zero {u : Filter ι} {f : ι → ℝ≥0∞} (hf : u.Tendsto f (𝓝 0))
    (g : ι → ℝ≥0∞) : u.limsup (f + g) = u.limsup g := by
  rw [add_comm, limsup_add_of_right_tendsto_zero hf]

end LimsupLiminf

end ENNReal -- namespace

lemma Dense.lipschitzWith_extend {α β : Type*}
    [PseudoEMetricSpace α] [EMetricSpace β] [CompleteSpace β]
    {s : Set α} (hs : Dense s) {f : s → β} {K : ℝ≥0} (hf : LipschitzWith K f) :
    LipschitzWith K (hs.extend f) := by
  have : IsClosed {p : α × α | edist (hs.extend f p.1) (hs.extend f p.2) ≤ K * edist p.1 p.2} := by
    have : Continuous (hs.extend f) := (hs.uniformContinuous_extend hf.uniformContinuous).continuous
    apply isClosed_le (by fun_prop)
    exact (ENNReal.continuous_const_mul (by simp)).comp (by fun_prop)
  have : Dense {p : α × α | edist (hs.extend f p.1) (hs.extend f p.2) ≤ K * edist p.1 p.2} := by
    apply (hs.prod hs).mono
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    have Ax : hs.extend f x = f ⟨x, hx⟩ := hs.extend_eq hf.continuous ⟨x, hx⟩
    have Ay : hs.extend f y = f ⟨y, hy⟩ := hs.extend_eq hf.continuous ⟨y, hy⟩
    simp only [Set.mem_ofPred_eq, Ax, Ay]
    exact hf ⟨x, hx⟩ ⟨y, hy⟩
  simpa only [Dense, IsClosed.closure_eq, Set.mem_ofPred_eq, Prod.forall] using! this
