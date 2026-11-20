/-
Copyright (c) 2022 Benjamin Davidson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Davidson, Devon Tuma, Eric Rodriguez, Oliver Nash
-/
module

public import Mathlib.Order.Filter.AtTopBot.Field
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Order.Group

/-!
# Topologies on linear ordered fields

In this file we prove that a linear ordered field with order topology has continuous multiplication
and division (apart from zero in the denominator). We also prove theorems like
`Filter.Tendsto.mul_atTop`: if `f` tends to a positive number and `g` tends to positive infinity,
then `f * g` tends to positive infinity.

Inversion is defined on the invertible elements. The limits of `x ↦ x⁻¹` are stated on the subtype
`{x : 𝕜 | IsUnit x}`, with the filters at infinity and near zero pulled back along the coercion;
the composite lemmas such as `Filter.Tendsto.inv_tendsto_atTop` hold for functions with invertible
values on any type, in particular on the subtype of points where a function is invertible.
-/

public section


open Set Filter TopologicalSpace Function
open scoped Pointwise Topology
open OrderDual (toDual ofDual)

section Semifield

variable {𝕜 α : Type*} [Semifield 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜]
  {l : Filter α} {f g : α → 𝕜}

/-- In a linearly ordered semifield with the order topology, if `f` tends to `Filter.atTop` and `g`
tends to a positive constant `C` then `f * g` tends to `Filter.atTop`. -/
theorem Filter.Tendsto.atTop_mul_pos {C : 𝕜} (hC : 0 < C) (hf : Tendsto f l atTop)
    (hg : Tendsto g l (𝓝 C)) : Tendsto (fun x => f x * g x) l atTop := by
  refine tendsto_atTop_mono' _ ?_ (hf.atTop_mul_const (half_pos hC))
  filter_upwards [hg.eventually (lt_mem_nhds (half_lt_self hC)), hf.eventually_ge_atTop 0] with x hg
    hf using mul_le_mul_of_nonneg_left hg.le hf

-- TODO: after removing this deprecated alias,
-- rename `Filter.Tendsto.atTop_mul'` to `Filter.Tendsto.atTop_mul`.
-- Same for the other 3 similar aliases below.
/-- In a linearly ordered semifield with the order topology, if `f` tends to a positive constant `C`
and `g` tends to `Filter.atTop` then `f * g` tends to `Filter.atTop`. -/
theorem Filter.Tendsto.pos_mul_atTop {C : 𝕜} (hC : 0 < C) (hf : Tendsto f l (𝓝 C))
    (hg : Tendsto g l atTop) : Tendsto (fun x => f x * g x) l atTop := by
  simpa only [mul_comm] using hg.atTop_mul_pos hC hf

/-- Inversion maps the filter at positive infinity, restricted to the invertible elements, to the
right neighbourhood of zero. -/
@[simp]
lemma inv_atTop₀ :
    map (fun x : {x : 𝕜 // IsUnit x} ↦ Checked.inv (x : 𝕜) x.2) (comap Subtype.val atTop) =
      𝓝[>] 0 := by
  have himg (a : 𝕜) (ha : 0 < a) :
      (fun x : {x : 𝕜 // IsUnit x} ↦ Checked.inv (x : 𝕜) x.2) '' (Subtype.val ⁻¹' Ioi a) =
        Ioo 0 a⁻¹ := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx0 : 0 < (x : 𝕜) := ha.trans hx
      exact ⟨inv_pos_of_pos hx0, (inv_lt_inv₀ hx0 ha).2 hx⟩
    · rintro ⟨hy0, hya⟩
      exact ⟨⟨y⁻¹, (inv_pos_of_pos hy0).ne'.isUnit⟩, (lt_inv_comm₀ ha hy0).2 hya, inv_inv₀ y⟩
  refine (((atTop_basis_Ioi' (0 : 𝕜)).comap Subtype.val).map _).eq_of_same_basis ?_
  refine (nhdsGT_basis (0 : 𝕜)).to_hasBasis (fun b hb ↦ ⟨b⁻¹, inv_pos_of_pos hb, ?_⟩)
    fun a ha ↦ ⟨a⁻¹, inv_pos_of_pos ha, (himg a ha).symm.subset⟩
  rw [himg _ (inv_pos_of_pos hb), inv_inv₀]

/-- Inversion maps the right neighbourhood of zero, restricted to the invertible elements, to the
filter at positive infinity. -/
@[simp]
lemma inv_nhdsGT_zero :
    map (fun x : {x : 𝕜 // IsUnit x} ↦ Checked.inv (x : 𝕜) x.2) (comap Subtype.val (𝓝[>] 0)) =
      atTop := by
  have himg (a : 𝕜) (ha : 0 < a) :
      (fun x : {x : 𝕜 // IsUnit x} ↦ Checked.inv (x : 𝕜) x.2) '' (Subtype.val ⁻¹' Ioo 0 a) =
        Ioi a⁻¹ := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (inv_lt_inv₀ ha hx.1).2 hx.2
    · intro hy
      have hy0 : 0 < y := (inv_pos_of_pos ha).trans hy
      exact ⟨⟨y⁻¹, (inv_pos_of_pos hy0).ne'.isUnit⟩,
        ⟨inv_pos_of_pos hy0, (inv_lt_comm₀ hy0 ha).2 hy⟩, inv_inv₀ y⟩
  refine (((nhdsGT_basis (0 : 𝕜)).comap Subtype.val).map _).eq_of_same_basis ?_
  refine (atTop_basis_Ioi' (0 : 𝕜)).to_hasBasis (fun b hb ↦ ⟨b⁻¹, inv_pos_of_pos hb, ?_⟩)
    fun a ha ↦ ⟨a⁻¹, inv_pos_of_pos ha, (himg a ha).symm.subset⟩
  rw [himg _ (inv_pos_of_pos hb), inv_inv₀]

/-- The function `x ↦ x⁻¹` tends to `+∞` on the right of `0`. -/
theorem tendsto_inv_nhdsGT_zero :
    Tendsto (fun x : {x : 𝕜 | IsUnit x} ↦ Checked.inv (x : 𝕜) x.2)
      (comap Subtype.val (𝓝[>] 0)) atTop :=
  inv_nhdsGT_zero.le

/-- The function `r ↦ r⁻¹` tends to `0` on the right as `r → +∞`. -/
theorem tendsto_inv_atTop_nhdsGT_zero :
    Tendsto (fun x : {x : 𝕜 | IsUnit x} ↦ Checked.inv (x : 𝕜) x.2)
      (comap Subtype.val atTop) (𝓝[>] 0) :=
  inv_atTop₀.le

theorem tendsto_nhdsGT_zero_of_comp_inv_tendsto_atTop {f : 𝕜 → α}
    (h : Tendsto (fun x : {x : 𝕜 | IsUnit x} ↦ f (Checked.inv (x : 𝕜) x.2))
      (comap Subtype.val atTop) l) :
    Tendsto f (𝓝[>] 0) l := by
  rw [← inv_atTop₀, tendsto_map'_iff]
  exact h

theorem tendsto_inv_atTop_zero :
    Tendsto (fun x : {x : 𝕜 | IsUnit x} ↦ Checked.inv (x : 𝕜) x.2)
      (comap Subtype.val atTop) (𝓝 0) :=
  tendsto_inv_atTop_nhdsGT_zero.mono_right inf_le_left

theorem Filter.Tendsto.fun_inv_tendsto_atTop {h0 : ∀ x, IsUnit (f x)} (h : Tendsto f l atTop) :
    Tendsto (fun x ↦ Checked.inv (f x) (h0 x)) l (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (tendsto_comap_iff.mpr h :
    Tendsto (fun x ↦ (⟨f x, h0 x⟩ : {x : 𝕜 | IsUnit x})) l (comap Subtype.val atTop))

theorem Filter.Tendsto.inv_tendsto_atTop {h0 : IsUnit f} (h : Tendsto f l atTop) :
    Tendsto f⁻¹ l (𝓝 0) := by
  rw [funext (Pi.inv_apply₀ f)]
  exact h.fun_inv_tendsto_atTop

theorem Filter.Tendsto.fun_inv_tendsto_nhdsGT_zero {h0 : ∀ x, IsUnit (f x)}
    (h : Tendsto f l (𝓝[>] 0)) : Tendsto (fun x ↦ Checked.inv (f x) (h0 x)) l atTop :=
  tendsto_inv_nhdsGT_zero.comp (tendsto_comap_iff.mpr h :
    Tendsto (fun x ↦ (⟨f x, h0 x⟩ : {x : 𝕜 | IsUnit x})) l (comap Subtype.val (𝓝[>] 0)))

theorem Filter.Tendsto.inv_tendsto_nhdsGT_zero {h0 : IsUnit f} (h : Tendsto f l (𝓝[>] 0)) :
    Tendsto f⁻¹ l atTop := by
  rw [funext (Pi.inv_apply₀ f)]
  exact h.fun_inv_tendsto_nhdsGT_zero

/-- The function `x^(-n)` tends to `0` at `+∞` for any positive natural `n`.
A version for positive real powers exists as `tendsto_rpow_neg_atTop`. -/
theorem tendsto_pow_neg_atTop {n : ℕ} (hn : n ≠ 0) :
    Tendsto (fun x : {x : 𝕜 | IsUnit x} ↦ Checked.zpow (x : 𝕜) (-(n : ℤ)) fun _ ↦ x.2)
      (comap Subtype.val atTop) (𝓝 0) := by
  have h : Tendsto (fun x : {x : 𝕜 | IsUnit x} ↦ (x : 𝕜) ^ n) (comap Subtype.val atTop) atTop :=
    (tendsto_pow_atTop hn).comp tendsto_comap
  refine (h.fun_inv_tendsto_atTop (h0 := fun x ↦ x.2.pow n)).congr fun x ↦ ?_
  simp only [zpow_neg₀ x.2.ne_zero, zpow_natCast₀]

theorem tendsto_zpow_atTop_zero {n : ℤ} (hn : n < 0) :
    Tendsto (fun x : {x : 𝕜 | IsUnit x} ↦ Checked.zpow (x : 𝕜) n fun _ ↦ x.2)
      (comap Subtype.val atTop) (𝓝 0) := by
  lift -n to ℕ using le_of_lt (neg_pos.mpr hn) with N h
  have hN : N ≠ 0 := by omega
  obtain rfl : n = -(N : ℤ) := by omega
  exact tendsto_pow_neg_atTop hN

-- see Note [lower instance priority]
instance (priority := 100) IsStrictOrderedRing.toContinuousInv₀ [ContinuousMul 𝕜] :
    ContinuousInv₀ 𝕜 := .of_nhds_one <| tendsto_order.2 <| by
  have hval := continuous_subtype_val.tendsto (⟨1, isUnit_one⟩ : {y : 𝕜 | IsUnit y})
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨x', hmid, h₁⟩ := exists_between (max_lt (zero_lt_one : (0 : 𝕜) < 1) hx)
    have h₀ : 0 < x' := (le_max_left 0 x).trans_lt hmid
    have hxx' : x ≤ x' := (le_max_right 0 x).trans hmid.le
    filter_upwards [hval.eventually (Ioo_mem_nhds one_pos ((one_lt_inv₀ h₀).2 h₁))] with y hy
    exact hxx'.trans_lt (lt_inv_of_lt_inv₀ hy.1 hy.2)
  · filter_upwards [hval.eventually (Ioi_mem_nhds (inv_lt_one_of_one_lt₀ hx))] with y hy
    exact inv_lt_of_inv_lt₀ (zero_lt_one.trans hx) hy

end Semifield

/-- If a (possibly non-unital and/or non-associative) ring `R` admits a submultiplicative
nonnegative norm `norm : R → 𝕜`, where `𝕜` is a linear ordered field, and the open balls
`{ x | norm x < ε }`, `ε > 0`, form a basis of neighborhoods of zero, then `R` is a topological
ring. -/
theorem IsTopologicalRing.of_norm {R 𝕜 : Type*} [NonUnitalNonAssocRing R]
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [TopologicalSpace R] [IsTopologicalAddGroup R] (norm : R → 𝕜)
    (norm_nonneg : ∀ x, 0 ≤ norm x) (norm_mul_le : ∀ x y, norm (x * y) ≤ norm x * norm y)
    (nhds_basis : (𝓝 (0 : R)).HasBasis ((0 : 𝕜) < ·) (fun ε ↦ { x | norm x < ε })) :
    IsTopologicalRing R := by
  have h0 : ∀ f : R → R, ∀ c ≥ (0 : 𝕜), (∀ x, norm (f x) ≤ c * norm x) →
      Tendsto f (𝓝 0) (𝓝 0) := by
    refine fun f c c0 hf ↦ (nhds_basis.tendsto_iff nhds_basis).2 fun ε ε0 ↦ ?_
    rcases exists_pos_mul_lt ε0 c with ⟨δ, δ0, hδ⟩
    refine ⟨δ, δ0, fun x hx ↦ (hf _).trans_lt ?_⟩
    exact (mul_le_mul_of_nonneg_left (le_of_lt hx) c0).trans_lt hδ
  apply IsTopologicalRing.of_addGroup_of_nhds_zero
  case hmul =>
    refine ((nhds_basis.prod nhds_basis).tendsto_iff nhds_basis).2 fun ε ε0 ↦ ?_
    refine ⟨(1, ε), ⟨one_pos, ε0⟩, fun (x, y) ⟨hx, hy⟩ => ?_⟩
    simp only at *
    calc norm (x * y) ≤ norm x * norm y := norm_mul_le _ _
    _ < ε := (mul_le_of_le_one_left (norm_nonneg _) hx.le).trans_lt hy
  case hmul_left => exact fun x => h0 _ (norm x) (norm_nonneg _) (norm_mul_le x)
  case hmul_right =>
    exact fun y => h0 (· * y) (norm y) (norm_nonneg y) fun x =>
      (norm_mul_le x y).trans_eq (mul_comm _ _)

variable {𝕜 α : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜]
  {l : Filter α} {f g : α → 𝕜}

-- see Note [lower instance priority]
instance (priority := 100) IsStrictOrderedRing.topologicalRing : IsTopologicalRing 𝕜 :=
  .of_norm abs abs_nonneg (fun _ _ ↦ (abs_mul _ _).le) <| by
    simpa using nhds_basis_abs_sub_lt (0 : 𝕜)

/-- In a linearly ordered field with the order topology, if `f` tends to `Filter.atTop` and `g`
tends to a negative constant `C` then `f * g` tends to `Filter.atBot`. -/
theorem Filter.Tendsto.atTop_mul_neg {C : 𝕜} (hC : C < 0) (hf : Tendsto f l atTop)
    (hg : Tendsto g l (𝓝 C)) : Tendsto (fun x => f x * g x) l atBot := by
  have := hf.atTop_mul_pos (neg_pos.2 hC) hg.neg
  simpa only [Function.comp_def, neg_mul_eq_mul_neg, neg_neg] using
    tendsto_neg_atTop_atBot.comp this

/-- In a linearly ordered field with the order topology, if `f` tends to a negative constant `C` and
`g` tends to `Filter.atTop` then `f * g` tends to `Filter.atBot`. -/
theorem Filter.Tendsto.neg_mul_atTop {C : 𝕜} (hC : C < 0) (hf : Tendsto f l (𝓝 C))
    (hg : Tendsto g l atTop) : Tendsto (fun x => f x * g x) l atBot := by
  simpa only [mul_comm] using hg.atTop_mul_neg hC hf

/-- In a linearly ordered field with the order topology, if `f` tends to `Filter.atBot` and `g`
tends to a positive constant `C` then `f * g` tends to `Filter.atBot`. -/
theorem Filter.Tendsto.atBot_mul_pos {C : 𝕜} (hC : 0 < C) (hf : Tendsto f l atBot)
    (hg : Tendsto g l (𝓝 C)) : Tendsto (fun x => f x * g x) l atBot := by
  have := (tendsto_neg_atBot_atTop.comp hf).atTop_mul_pos hC hg
  simpa [Function.comp_def] using tendsto_neg_atTop_atBot.comp this

/-- In a linearly ordered field with the order topology, if `f` tends to `Filter.atBot` and `g`
tends to a negative constant `C` then `f * g` tends to `Filter.atTop`. -/
theorem Filter.Tendsto.atBot_mul_neg {C : 𝕜} (hC : C < 0) (hf : Tendsto f l atBot)
    (hg : Tendsto g l (𝓝 C)) : Tendsto (fun x => f x * g x) l atTop := by
  have := (tendsto_neg_atBot_atTop.comp hf).atTop_mul_neg hC hg
  simpa [Function.comp_def] using tendsto_neg_atBot_atTop.comp this

/-- In a linearly ordered field with the order topology, if `f` tends to a positive constant `C` and
`g` tends to `Filter.atBot` then `f * g` tends to `Filter.atBot`. -/
theorem Filter.Tendsto.pos_mul_atBot {C : 𝕜} (hC : 0 < C) (hf : Tendsto f l (𝓝 C))
    (hg : Tendsto g l atBot) : Tendsto (fun x => f x * g x) l atBot := by
  simpa only [mul_comm] using hg.atBot_mul_pos hC hf

/-- In a linearly ordered field with the order topology, if `f` tends to a negative constant `C` and
`g` tends to `Filter.atBot` then `f * g` tends to `Filter.atTop`. -/
theorem Filter.Tendsto.neg_mul_atBot {C : 𝕜} (hC : C < 0) (hf : Tendsto f l (𝓝 C))
    (hg : Tendsto g l atBot) : Tendsto (fun x => f x * g x) l atTop := by
  simpa only [mul_comm] using hg.atBot_mul_neg hC hf

/-- Inversion maps the filter at negative infinity, restricted to the invertible elements, to the
left neighbourhood of zero. -/
@[simp]
lemma inv_atBot₀ :
    map (fun x : {x : 𝕜 // IsUnit x} ↦ Checked.inv (x : 𝕜) x.2) (comap Subtype.val atBot) =
      𝓝[<] 0 := by
  have himg (a : 𝕜) (ha : a < 0) :
      (fun x : {x : 𝕜 // IsUnit x} ↦ Checked.inv (x : 𝕜) x.2) '' (Subtype.val ⁻¹' Iio a) =
        Ioo a⁻¹ 0 := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx0 : (x : 𝕜) < 0 := (show (x : 𝕜) < a from hx).trans ha
      exact ⟨(inv_lt_inv_of_neg ha hx0).2 hx, inv_neg''.2 hx0⟩
    · rintro ⟨hay, hy0⟩
      exact ⟨⟨y⁻¹, (inv_neg''.2 hy0).ne.isUnit⟩, (inv_lt_of_neg hy0 ha).2 hay, inv_inv₀ y⟩
  refine (((atBot_basis_Iio' (0 : 𝕜)).comap Subtype.val).map _).eq_of_same_basis ?_
  refine (nhdsLT_basis (0 : 𝕜)).to_hasBasis (fun b hb ↦ ⟨b⁻¹, inv_neg''.2 hb, ?_⟩)
    fun a ha ↦ ⟨a⁻¹, inv_neg''.2 ha, (himg a ha).symm.subset⟩
  rw [himg _ (inv_neg''.2 hb), inv_inv₀]

/-- Inversion maps the left neighbourhood of zero, restricted to the invertible elements, to the
filter at negative infinity. -/
@[simp]
lemma inv_nhdsLT_zero :
    map (fun x : {x : 𝕜 // IsUnit x} ↦ Checked.inv (x : 𝕜) x.2) (comap Subtype.val (𝓝[<] 0)) =
      atBot := by
  have himg (a : 𝕜) (ha : a < 0) :
      (fun x : {x : 𝕜 // IsUnit x} ↦ Checked.inv (x : 𝕜) x.2) '' (Subtype.val ⁻¹' Ioo a 0) =
        Iio a⁻¹ := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (inv_lt_inv_of_neg hx.2 ha).2 hx.1
    · intro hy
      have hy0 : y < 0 := hy.trans (inv_neg''.2 ha)
      exact ⟨⟨y⁻¹, (inv_neg''.2 hy0).ne.isUnit⟩,
        ⟨(lt_inv_of_neg ha hy0).2 hy, inv_neg''.2 hy0⟩, inv_inv₀ y⟩
  refine (((nhdsLT_basis (0 : 𝕜)).comap Subtype.val).map _).eq_of_same_basis ?_
  refine (atBot_basis_Iio' (0 : 𝕜)).to_hasBasis (fun b hb ↦ ⟨b⁻¹, inv_neg''.2 hb, ?_⟩)
    fun a ha ↦ ⟨a⁻¹, inv_neg''.2 ha, (himg a ha).symm.subset⟩
  rw [himg _ (inv_neg''.2 hb), inv_inv₀]

/-- The function `x ↦ x⁻¹` tends to `-∞` on the left of `0`. -/
theorem tendsto_inv_nhdsLT_zero :
    Tendsto (fun x : {x : 𝕜 | IsUnit x} ↦ Checked.inv (x : 𝕜) x.2)
      (comap Subtype.val (𝓝[<] 0)) atBot :=
  inv_nhdsLT_zero.le

theorem tendsto_nhdsLT_zero_of_comp_inv_tendsto_atBot {f : 𝕜 → α}
    (h : Tendsto (fun x : {x : 𝕜 | IsUnit x} ↦ f (Checked.inv (x : 𝕜) x.2))
      (comap Subtype.val atBot) l) : Tendsto f (𝓝[<] 0) l := by
  rw [← inv_atBot₀, tendsto_map'_iff]
  exact h

/-- The function `r ↦ r⁻¹` tends to `0` on the left as `r → -∞`. -/
theorem tendsto_inv_atBot_nhdsLT_zero :
    Tendsto (fun x : {x : 𝕜 | IsUnit x} ↦ Checked.inv (x : 𝕜) x.2)
      (comap Subtype.val atBot) (𝓝[<] 0) :=
  inv_atBot₀.le

theorem tendsto_inv_atBot_zero :
    Tendsto (fun x : {x : 𝕜 | IsUnit x} ↦ Checked.inv (x : 𝕜) x.2)
      (comap Subtype.val atBot) (𝓝 0) :=
  tendsto_inv_atBot_nhdsLT_zero.mono_right inf_le_left

theorem Filter.Tendsto.fun_inv_tendsto_atBot {h0 : ∀ x, IsUnit (f x)} (h : Tendsto f l atBot) :
    Tendsto (fun x ↦ Checked.inv (f x) (h0 x)) l (𝓝 0) :=
  tendsto_inv_atBot_zero.comp (tendsto_comap_iff.mpr h :
    Tendsto (fun x ↦ (⟨f x, h0 x⟩ : {x : 𝕜 | IsUnit x})) l (comap Subtype.val atBot))

theorem Filter.Tendsto.inv_tendsto_atBot {h0 : IsUnit f} (h : Tendsto f l atBot) :
    Tendsto f⁻¹ l (𝓝 0) := by
  rw [funext (Pi.inv_apply₀ f)]
  exact h.fun_inv_tendsto_atBot

theorem Filter.Tendsto.fun_inv_tendsto_nhdsLT_zero {h0 : ∀ x, IsUnit (f x)}
    (h : Tendsto f l (𝓝[<] 0)) : Tendsto (fun x ↦ Checked.inv (f x) (h0 x)) l atBot :=
  tendsto_inv_nhdsLT_zero.comp (tendsto_comap_iff.mpr h :
    Tendsto (fun x ↦ (⟨f x, h0 x⟩ : {x : 𝕜 | IsUnit x})) l (comap Subtype.val (𝓝[<] 0)))

theorem Filter.Tendsto.inv_tendsto_nhdsLT_zero {h0 : IsUnit f} (h : Tendsto f l (𝓝[<] 0)) :
    Tendsto f⁻¹ l atBot := by
  rw [funext (Pi.inv_apply₀ f)]
  exact h.fun_inv_tendsto_nhdsLT_zero

theorem Filter.Tendsto.div_atTop {a : 𝕜} {h₀ : ∀ x, IsUnit (g x)} (h : Tendsto f l (𝓝 a))
    (hg : Tendsto g l atTop) : Tendsto (fun x => Checked.div (f x) (g x) (h₀ x)) l (𝓝 0) := by
  simpa only [div_eq_mul_inv₀, mul_zero] using h.mul (hg.fun_inv_tendsto_atTop (h0 := h₀))

theorem Filter.Tendsto.div_atBot {a : 𝕜} {h₀ : ∀ x, IsUnit (g x)} (h : Tendsto f l (𝓝 a))
    (hg : Tendsto g l atBot) : Tendsto (fun x => Checked.div (f x) (g x) (h₀ x)) l (𝓝 0) := by
  simpa only [div_eq_mul_inv₀, mul_zero] using h.mul (hg.fun_inv_tendsto_atBot (h0 := h₀))

lemma Filter.Tendsto.const_div_atTop {h₀ : ∀ x, IsUnit (g x)} (hg : Tendsto g l atTop) (r : 𝕜) :
    Tendsto (fun n ↦ Checked.div r (g n) (h₀ n)) l (𝓝 0) :=
  tendsto_const_nhds.div_atTop hg

lemma Filter.Tendsto.const_div_atBot {h₀ : ∀ x, IsUnit (g x)} (hg : Tendsto g l atBot) (r : 𝕜) :
    Tendsto (fun n ↦ Checked.div r (g n) (h₀ n)) l (𝓝 0) :=
  tendsto_const_nhds.div_atBot hg

/-- If `g` tends to zero and there exists a constant `C : 𝕜` such that eventually `|f x| ≤ C`,
  then the product `f * g` tends to zero. -/
theorem bdd_le_mul_tendsto_zero' {f g : α → 𝕜} (C : 𝕜) (hf : ∀ᶠ x in l, |f x| ≤ C)
    (hg : Tendsto g l (𝓝 0)) : Tendsto (fun x ↦ f x * g x) l (𝓝 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  have hC : Tendsto (fun x ↦ |C * g x|) l (𝓝 0) := by
    convert! (hg.const_mul C).abs
    simp_rw [mul_zero, abs_zero]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hC
  · filter_upwards [hf] with x _ using abs_nonneg _
  · filter_upwards [hf] with x hx
    simp only [comp_apply, abs_mul]
    exact mul_le_mul_of_nonneg_right (hx.trans (le_abs_self C)) (abs_nonneg _)

/-- If `g` tends to zero and there exist constants `b B : 𝕜` such that eventually `b ≤ f x| ≤ B`,
  then the product `f * g` tends to zero. -/
theorem bdd_le_mul_tendsto_zero {f g : α → 𝕜} {b B : 𝕜} (hb : ∀ᶠ x in l, b ≤ f x)
    (hB : ∀ᶠ x in l, f x ≤ B) (hg : Tendsto g l (𝓝 0)) :
    Tendsto (fun x ↦ f x * g x) l (𝓝 0) := by
  set C := max |b| |B|
  have hbC : -C ≤ b := neg_le.mpr (le_max_of_le_left (neg_le_abs b))
  have hBC : B ≤ C := le_max_of_le_right (le_abs_self B)
  apply bdd_le_mul_tendsto_zero' C _ hg
  filter_upwards [hb, hB]
  exact fun x hbx hBx ↦ abs_le.mpr ⟨hbC.trans hbx, hBx.trans hBC⟩

/-- If `g` tends to `atTop` and there exist constants `b B : 𝕜` such that eventually
  `b ≤ f x| ≤ B`, then the quotient `f / g` tends to zero. -/
theorem tendsto_bdd_div_atTop_nhds_zero {f g : α → 𝕜} {b B : 𝕜} {h₀ : ∀ x, IsUnit (g x)}
    (hb : ∀ᶠ x in l, b ≤ f x) (hB : ∀ᶠ x in l, f x ≤ B) (hg : Tendsto g l atTop) :
    Tendsto (fun x => Checked.div (f x) (g x) (h₀ x)) l (𝓝 0) := by
  simpa only [div_eq_mul_inv₀] using
    bdd_le_mul_tendsto_zero hb hB (hg.fun_inv_tendsto_atTop (h0 := h₀))

theorem tendsto_const_mul_zpow_atTop_zero {n : ℤ} {c : 𝕜} (hn : n < 0) :
    Tendsto (fun x : {x : 𝕜 | IsUnit x} ↦ c * Checked.zpow (x : 𝕜) n fun _ ↦ x.2)
      (comap Subtype.val atTop) (𝓝 0) :=
  mul_zero c ▸ Filter.Tendsto.const_mul c (tendsto_zpow_atTop_zero hn)

theorem tendsto_const_mul_pow_nhds_iff' {n : ℕ} {c d : 𝕜} :
    Tendsto (fun x : 𝕜 => c * x ^ n) atTop (𝓝 d) ↔ (c = 0 ∨ n = 0) ∧ c = d := by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp [tendsto_const_nhds_iff]
  rcases lt_trichotomy c 0 with (hc | rfl | hc)
  · have := tendsto_const_mul_pow_atBot_iff.2 ⟨hn, hc⟩
    simp [not_tendsto_nhds_of_tendsto_atBot this, hc.ne, hn]
  · simp [tendsto_const_nhds_iff]
  · have := tendsto_const_mul_pow_atTop_iff.2 ⟨hn, hc⟩
    simp [not_tendsto_nhds_of_tendsto_atTop this, hc.ne', hn]

theorem tendsto_const_mul_pow_nhds_iff {n : ℕ} {c d : 𝕜} (hc : c ≠ 0) :
    Tendsto (fun x : 𝕜 => c * x ^ n) atTop (𝓝 d) ↔ n = 0 ∧ c = d := by
  simp [tendsto_const_mul_pow_nhds_iff', hc]

/-- The integer power is taken on the invertible elements, where it is defined for every
exponent; the filter at `+∞` restricts to them without loss, since every positive element is
invertible. -/
theorem tendsto_const_mul_zpow_atTop_nhds_iff {n : ℤ} {c d : 𝕜} (hc : c ≠ 0) :
    Tendsto (fun x : {x : 𝕜 | IsUnit x} ↦ c * Checked.zpow (x : 𝕜) n fun _ ↦ x.2)
      (comap Subtype.val atTop) (𝓝 d) ↔ n = 0 ∧ c = d ∨ n < 0 ∧ d = 0 := by
  have hrange : range (Subtype.val : {x : 𝕜 | IsUnit x} → 𝕜) ∈ (atTop : Filter 𝕜) :=
    mem_of_superset (Ioi_mem_atTop 0) fun y hy ↦ ⟨⟨y, (ne_of_gt hy).isUnit⟩, rfl⟩
  have : (comap (Subtype.val : {x : 𝕜 | IsUnit x} → 𝕜) atTop).NeBot :=
    atTop_neBot.comap_of_range_mem hrange
  refine ⟨fun h => ?_, fun h => ?_⟩
  · cases n with
    | ofNat n =>
      left
      have h' : Tendsto (fun x : 𝕜 => c * x ^ n) atTop (𝓝 d) := by
        rw [← tendsto_comap'_iff hrange]
        simpa only [Int.ofNat_eq_natCast, zpow_natCast₀, Function.comp_def] using h
      simpa [tendsto_const_mul_pow_nhds_iff hc] using h'
    | negSucc n =>
      have hn := Int.negSucc_lt_zero n
      exact Or.inr ⟨hn, tendsto_nhds_unique h (tendsto_const_mul_zpow_atTop_zero hn)⟩
  · rcases h with ⟨rfl, rfl⟩ | h
    · simp only [zpow_zero₀, mul_one]
      exact tendsto_const_nhds
    · exact h.2.symm ▸ tendsto_const_mul_zpow_atTop_zero h.1

instance (priority := 100) IsStrictOrderedRing.toIsTopologicalDivisionRing :
    IsTopologicalDivisionRing 𝕜 := ⟨⟩

-- TODO: generalize to a `GroupWithZero`
theorem comap_mulLeft_nhdsGT_zero {x : 𝕜} (hx : 0 < x) : comap (x * ·) (𝓝[>] 0) = 𝓝[>] 0 := by
  rw [nhdsWithin, comap_inf, comap_principal, preimage_const_mul_Ioi₀ _ hx, zero_div]
  congr 1
  refine ((Homeomorph.mulLeft₀ x hx.ne').comap_nhds_eq _).trans ?_
  simp

theorem eventually_nhdsGT_zero_mul_left {x : 𝕜} (hx : 0 < x) {p : 𝕜 → Prop}
    (h : ∀ᶠ ε in 𝓝[>] 0, p ε) : ∀ᶠ ε in 𝓝[>] 0, p (x * ε) := by
  rw [← comap_mulLeft_nhdsGT_zero hx]
  exact h.comap fun ε => x * ε
