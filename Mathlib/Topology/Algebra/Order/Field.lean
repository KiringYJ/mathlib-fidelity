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

/-- Inversion sends the unit part of the filter at positive infinity to the right
neighbourhood of zero. No value of the inverse at zero is used. -/
@[simp]
lemma inv_atTop₀ :
    map (fun u : 𝕜ˣ ↦ (↑u⁻¹ : 𝕜))
      (comap (fun u : 𝕜ˣ ↦ (u : 𝕜)) atTop) = 𝓝[>] 0 := by
  have hb : (atTop : Filter 𝕜).HasBasis
      (fun u : 𝕜ˣ ↦ 0 < (u : 𝕜)) (fun u ↦ Ioi (u : 𝕜)) :=
    (atTop_basis_Ioi' (0 : 𝕜)).to_hasBasis
      (fun a ha ↦ ⟨Units.mk0 a ha.ne', ha, Subset.rfl⟩)
      (fun u hu ↦ ⟨(u : 𝕜), hu, Subset.rfl⟩)
  have hn : (𝓝[>] (0 : 𝕜)).HasBasis
      (fun u : 𝕜ˣ ↦ 0 < (u : 𝕜)) (fun u ↦ Ioo 0 (u : 𝕜)) :=
    (nhdsGT_basis (0 : 𝕜)).to_hasBasis
      (fun a ha ↦ ⟨Units.mk0 a ha.ne', ha, Subset.rfl⟩)
      (fun u hu ↦ ⟨(u : 𝕜), hu, Subset.rfl⟩)
  apply (((hb.comap (fun u : 𝕜ˣ ↦ (u : 𝕜))).map
    (fun u : 𝕜ˣ ↦ (↑u⁻¹ : 𝕜))).comp_surjective
      (inv_surjective : Function.Surjective (Inv.inv : 𝕜ˣ → 𝕜ˣ))).eq_of_same_basis
  apply hn.congr
  · intro u
    exact (Units.inv_pos u).symm
  · intro u hu
    ext y
    symm
    constructor
    · rintro ⟨v, hv, rfl⟩
      have hvpos : 0 < (v : 𝕜) := ((Units.inv_pos u).mpr hu).trans hv
      exact ⟨(Units.inv_pos v).mpr hvpos,
        by simpa only [inv_inv] using (Units.inv_lt_inv (u := v) (v := u⁻¹) hvpos
          ((Units.inv_pos u).mpr hu)).mpr hv⟩
    · intro hy
      refine ⟨(Units.mk0 y hy.1.ne')⁻¹, ?_, ?_⟩
      · exact (Units.inv_lt_inv (u := u) (v := Units.mk0 y hy.1.ne') hu hy.1).mpr hy.2
      · simp

@[simp]
lemma inv_nhdsGT_zero :
    map (fun u : 𝕜ˣ ↦ (↑u⁻¹ : 𝕜))
      (comap (fun u : 𝕜ˣ ↦ (u : 𝕜)) (𝓝[>] 0)) = atTop := by
  have hb : (atTop : Filter 𝕜).HasBasis
      (fun u : 𝕜ˣ ↦ 0 < (u : 𝕜)) (fun u ↦ Ioi (u : 𝕜)) :=
    (atTop_basis_Ioi' (0 : 𝕜)).to_hasBasis
      (fun a ha ↦ ⟨Units.mk0 a ha.ne', ha, Subset.rfl⟩)
      (fun u hu ↦ ⟨(u : 𝕜), hu, Subset.rfl⟩)
  have hn : (𝓝[>] (0 : 𝕜)).HasBasis
      (fun u : 𝕜ˣ ↦ 0 < (u : 𝕜)) (fun u ↦ Ioo 0 (u : 𝕜)) :=
    (nhdsGT_basis (0 : 𝕜)).to_hasBasis
      (fun a ha ↦ ⟨Units.mk0 a ha.ne', ha, Subset.rfl⟩)
      (fun u hu ↦ ⟨(u : 𝕜), hu, Subset.rfl⟩)
  apply (((hn.comap (fun u : 𝕜ˣ ↦ (u : 𝕜))).map
    (fun u : 𝕜ˣ ↦ (↑u⁻¹ : 𝕜))).comp_surjective
      (inv_surjective : Function.Surjective (Inv.inv : 𝕜ˣ → 𝕜ˣ))).eq_of_same_basis
  apply hb.congr
  · intro u
    exact (Units.inv_pos u).symm
  · intro u hu
    ext y
    symm
    constructor
    · rintro ⟨v, hv, rfl⟩
      simpa only [inv_inv, Set.mem_Ioi] using
        (Units.inv_lt_inv (u := u⁻¹) (v := v) ((Units.inv_pos u).mpr hu) hv.1).mpr hv.2
    · intro hy
      have hypos : 0 < y := hu.trans hy
      refine ⟨(Units.mk0 y hypos.ne')⁻¹, ?_, ?_⟩
      · exact ⟨(Units.inv_pos _).mpr hypos, (Units.inv_lt_inv (u := Units.mk0 y hypos.ne') (v := u) hypos hu).mpr hy⟩
      · simp

/-- The function `x ↦ x⁻¹` tends to `+∞` on the right of `0`. -/
theorem tendsto_inv_nhdsGT_zero :
    Tendsto (fun u : 𝕜ˣ ↦ (↑u⁻¹ : 𝕜))
      (comap (fun u : 𝕜ˣ ↦ (u : 𝕜)) (𝓝[>] 0)) atTop :=
  inv_nhdsGT_zero.le

/-- The inverse on units tends to zero from the right at positive infinity. -/
theorem tendsto_inv_atTop_nhdsGT_zero :
    Tendsto (fun u : 𝕜ˣ ↦ (↑u⁻¹ : 𝕜))
      (comap (fun u : 𝕜ˣ ↦ (u : 𝕜)) atTop) (𝓝[>] 0) :=
  inv_atTop₀.le

theorem tendsto_nhdsGT_zero_of_comp_inv_tendsto_atTop {f : 𝕜 → α}
    (h : Tendsto (fun u : 𝕜ˣ ↦ f (↑u⁻¹ : 𝕜))
      (comap (fun u : 𝕜ˣ ↦ (u : 𝕜)) atTop) l) :
    Tendsto f (𝓝[>] 0) l := by
  rw [← inv_atTop₀, tendsto_map'_iff]
  exact h

theorem tendsto_inv_atTop_zero :
    Tendsto (fun u : 𝕜ˣ ↦ (↑u⁻¹ : 𝕜))
      (comap (fun u : 𝕜ˣ ↦ (u : 𝕜)) atTop) (𝓝 0) :=
  tendsto_inv_atTop_nhdsGT_zero.mono_right inf_le_left

theorem Filter.Tendsto.inv_tendsto_atTop {f : α → 𝕜ˣ}
    (h : Tendsto (fun x ↦ (f x : 𝕜)) l atTop) :
    Tendsto (fun x ↦ (↑(f x)⁻¹ : 𝕜)) l (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (tendsto_comap_iff.mpr h)

theorem Filter.Tendsto.inv_tendsto_nhdsGT_zero {f : α → 𝕜ˣ}
    (h : Tendsto (fun x ↦ (f x : 𝕜)) l (𝓝[>] 0)) :
    Tendsto (fun x ↦ (↑(f x)⁻¹ : 𝕜)) l atTop :=
  tendsto_inv_nhdsGT_zero.comp (tendsto_comap_iff.mpr h)

/-- The function `x^(-n)` tends to `0` at `+∞` for any positive natural `n`.
A version for positive real powers exists as `tendsto_rpow_neg_atTop`. -/
theorem tendsto_pow_neg_atTop {n : ℕ} (hn : n ≠ 0) :
    Tendsto (fun x : 𝕜ˣ => (↑(x ^ (-(n : ℤ))) : 𝕜))
      (comap (fun u : 𝕜ˣ ↦ (u : 𝕜)) atTop) (𝓝 0) := by
  have h : Tendsto (fun u : 𝕜ˣ ↦ (↑(u ^ n) : 𝕜))
      (comap (fun u : 𝕜ˣ ↦ (u : 𝕜)) atTop) atTop := by
    simpa only [Units.val_pow_eq_pow_val, Function.comp_def] using
      (tendsto_pow_atTop (α := 𝕜) hn).comp tendsto_comap
  simpa only [zpow_neg, zpow_natCast] using h.inv_tendsto_atTop

theorem tendsto_zpow_atTop_zero {n : ℤ} (hn : n < 0) :
    Tendsto (fun x : 𝕜ˣ => (↑(x ^ n) : 𝕜))
      (comap (fun u : 𝕜ˣ ↦ (u : 𝕜)) atTop) (𝓝 0) := by
  lift -n to ℕ using le_of_lt (neg_pos.mpr hn) with N h
  have hN : N ≠ 0 := by omega
  have hn' : n = -(N : ℤ) := by omega
  rw [hn']
  exact tendsto_pow_neg_atTop hN

-- see Note [lower instance priority]
instance (priority := 100) IsStrictOrderedRing.toContinuousInv₀ [ContinuousMul 𝕜] :
    ContinuousInv₀ 𝕜 := .of_nhds_one <| tendsto_order.2 <| by
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨x', hmid, h₁⟩ := exists_between (max_lt (zero_lt_one : (0 : 𝕜) < 1) hx)
    have h₀ : 0 < x' := (le_max_left 0 x).trans_lt hmid
    have hxx' : x ≤ x' := (le_max_right 0 x).trans hmid.le
    let u := Units.mk0 x' h₀.ne'
    have hu : 1 < (↑u⁻¹ : 𝕜) := by
      simpa only [mul_one] using (Units.lt_inv_mul_iff (u := u) h₀).mpr h₁
    filter_upwards [(continuous_subtype_val.tendsto
      (⟨1, isUnit_one⟩ : {y : 𝕜 | IsUnit y})).eventually (Ioo_mem_nhds one_pos hu)]
      with y hy
    apply hxx'.trans_lt
    simpa only [inv_inv, Units.val_mk0] using
      (Units.inv_lt_inv (u := u⁻¹) (v := y.property.unit)
        ((Units.inv_pos u).mpr h₀) hy.1).mpr hy.2
  · let u := Units.mk0 x (zero_lt_one.trans hx).ne'
    have hu : (↑u⁻¹ : 𝕜) < 1 := by
      simpa only [mul_one] using
        (Units.inv_mul_lt_iff (u := u) (zero_lt_one.trans hx)).mpr hx
    filter_upwards [(continuous_subtype_val.tendsto
      (⟨1, isUnit_one⟩ : {y : 𝕜 | IsUnit y})).eventually (Ioi_mem_nhds hu)] with y hy
    have hypos : 0 < y.val := ((Units.inv_pos u).mpr (zero_lt_one.trans hx)).trans hy
    simpa only [inv_inv, Units.val_mk0] using
      (Units.inv_lt_inv (u := y.property.unit) (v := u⁻¹)
        hypos ((Units.inv_pos u).mpr (zero_lt_one.trans hx))).mpr hy

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

@[simp]
lemma inv_atBot₀ :
    map (fun u : 𝕜ˣ ↦ (↑u⁻¹ : 𝕜))
      (comap (fun u : 𝕜ˣ ↦ (u : 𝕜)) atBot) = 𝓝[<] 0 := by
  have hi (u v : 𝕜ˣ) (hu : (u : 𝕜) < 0) (hv : (v : 𝕜) < 0) :
      (↑u⁻¹ : 𝕜) < ↑v⁻¹ ↔ (v : 𝕜) < u := by
    simpa only [inv_neg, Units.val_neg, neg_lt_neg_iff] using
      (Units.inv_lt_inv (u := -v) (v := -u) (neg_pos.mpr hv) (neg_pos.mpr hu))
  have hb : (atBot : Filter 𝕜).HasBasis
      (fun u : 𝕜ˣ ↦ (u : 𝕜) < 0) (fun u ↦ Iio (u : 𝕜)) :=
    (atBot_basis_Iio' (0 : 𝕜)).to_hasBasis
      (fun a ha ↦ ⟨Units.mk0 a ha.ne, ha, Subset.rfl⟩)
      (fun u hu ↦ ⟨(u : 𝕜), hu, Subset.rfl⟩)
  have hn : (𝓝[<] (0 : 𝕜)).HasBasis
      (fun u : 𝕜ˣ ↦ (u : 𝕜) < 0) (fun u ↦ Ioo (u : 𝕜) 0) :=
    (nhdsLT_basis (0 : 𝕜)).to_hasBasis
      (fun a ha ↦ ⟨Units.mk0 a ha.ne, ha, Subset.rfl⟩)
      (fun u hu ↦ ⟨(u : 𝕜), hu, Subset.rfl⟩)
  apply (((hb.comap (fun u : 𝕜ˣ ↦ (u : 𝕜))).map
    (fun u : 𝕜ˣ ↦ (↑u⁻¹ : 𝕜))).comp_surjective
      (inv_surjective : Function.Surjective (Inv.inv : 𝕜ˣ → 𝕜ˣ))).eq_of_same_basis
  apply hn.congr
  · intro u
    exact (Units.inv_neg u).symm
  · intro u hu
    ext y
    symm
    constructor
    · rintro ⟨v, hv, rfl⟩
      have hvneg : (v : 𝕜) < 0 := hv.trans ((Units.inv_neg u).mpr hu)
      exact ⟨by simpa only [inv_inv] using (hi (u⁻¹) v ((Units.inv_neg u).mpr hu) hvneg).mpr hv,
        (Units.inv_neg v).mpr hvneg⟩
    · intro hy
      refine ⟨(Units.mk0 y hy.2.ne)⁻¹, ?_, by simp⟩
      exact (hi (Units.mk0 y hy.2.ne) u hy.2 hu).mpr hy.1

@[simp]
lemma inv_nhdsLT_zero :
    map (fun u : 𝕜ˣ ↦ (↑u⁻¹ : 𝕜))
      (comap (fun u : 𝕜ˣ ↦ (u : 𝕜)) (𝓝[<] 0)) = atBot := by
  have hi (u v : 𝕜ˣ) (hu : (u : 𝕜) < 0) (hv : (v : 𝕜) < 0) :
      (↑u⁻¹ : 𝕜) < ↑v⁻¹ ↔ (v : 𝕜) < u := by
    simpa only [inv_neg, Units.val_neg, neg_lt_neg_iff] using
      (Units.inv_lt_inv (u := -v) (v := -u) (neg_pos.mpr hv) (neg_pos.mpr hu))
  have hb : (atBot : Filter 𝕜).HasBasis
      (fun u : 𝕜ˣ ↦ (u : 𝕜) < 0) (fun u ↦ Iio (u : 𝕜)) :=
    (atBot_basis_Iio' (0 : 𝕜)).to_hasBasis
      (fun a ha ↦ ⟨Units.mk0 a ha.ne, ha, Subset.rfl⟩)
      (fun u hu ↦ ⟨(u : 𝕜), hu, Subset.rfl⟩)
  have hn : (𝓝[<] (0 : 𝕜)).HasBasis
      (fun u : 𝕜ˣ ↦ (u : 𝕜) < 0) (fun u ↦ Ioo (u : 𝕜) 0) :=
    (nhdsLT_basis (0 : 𝕜)).to_hasBasis
      (fun a ha ↦ ⟨Units.mk0 a ha.ne, ha, Subset.rfl⟩)
      (fun u hu ↦ ⟨(u : 𝕜), hu, Subset.rfl⟩)
  apply (((hn.comap (fun u : 𝕜ˣ ↦ (u : 𝕜))).map
    (fun u : 𝕜ˣ ↦ (↑u⁻¹ : 𝕜))).comp_surjective
      (inv_surjective : Function.Surjective (Inv.inv : 𝕜ˣ → 𝕜ˣ))).eq_of_same_basis
  apply hb.congr
  · intro u
    exact (Units.inv_neg u).symm
  · intro u hu
    ext y
    symm
    constructor
    · rintro ⟨v, hv, rfl⟩
      simpa only [inv_inv, Set.mem_Iio] using
        (hi v (u⁻¹) hv.2 ((Units.inv_neg u).mpr hu)).mpr hv.1
    · intro hy
      have hyneg : y < 0 := hy.trans hu
      refine ⟨(Units.mk0 y hyneg.ne)⁻¹, ⟨?_, (Units.inv_neg _).mpr hyneg⟩, by simp⟩
      exact (hi u (Units.mk0 y hyneg.ne) hu hyneg).mpr hy

theorem tendsto_inv_nhdsLT_zero :
    Tendsto (fun u : 𝕜ˣ ↦ (↑u⁻¹ : 𝕜))
      (comap (fun u : 𝕜ˣ ↦ (u : 𝕜)) (𝓝[<] 0)) atBot := inv_nhdsLT_zero.le

theorem tendsto_nhdsLT_zero_of_comp_inv_tendsto_atBot {f : 𝕜 → α}
    (h : Tendsto (fun u : 𝕜ˣ ↦ f (↑u⁻¹ : 𝕜))
      (comap (fun u : 𝕜ˣ ↦ (u : 𝕜)) atBot) l) : Tendsto f (𝓝[<] 0) l := by
  rw [← inv_atBot₀, tendsto_map'_iff]
  exact h

theorem tendsto_inv_atBot_nhdsLT_zero :
    Tendsto (fun u : 𝕜ˣ ↦ (↑u⁻¹ : 𝕜))
      (comap (fun u : 𝕜ˣ ↦ (u : 𝕜)) atBot) (𝓝[<] 0) := inv_atBot₀.le

theorem tendsto_inv_atBot_zero :
    Tendsto (fun u : 𝕜ˣ ↦ (↑u⁻¹ : 𝕜))
      (comap (fun u : 𝕜ˣ ↦ (u : 𝕜)) atBot) (𝓝 0) :=
  tendsto_inv_atBot_nhdsLT_zero.mono_right inf_le_left

theorem Filter.Tendsto.div_atTop {a : 𝕜} {g : α → 𝕜ˣ}
    (h : Tendsto f l (𝓝 a)) (hg : Tendsto (fun x ↦ (g x : 𝕜)) l atTop) :
    Tendsto (fun x => f x /ₚ g x) l (𝓝 0) := by
  simpa only [mul_zero, divp, Function.comp_def] using h.mul
    (tendsto_inv_atTop_zero.comp (tendsto_comap_iff.mpr hg))

lemma Filter.Tendsto.const_div_atTop {g : α → 𝕜ˣ}
    (hg : Tendsto (fun x ↦ (g x : 𝕜)) l atTop) (r : 𝕜) :
    Tendsto (fun n ↦ r /ₚ g n) l (𝓝 0) :=
  tendsto_const_nhds.div_atTop hg

theorem Filter.Tendsto.div_atBot {a : 𝕜} {g : α → 𝕜ˣ}
    (h : Tendsto f l (𝓝 a)) (hg : Tendsto (fun x ↦ (g x : 𝕜)) l atBot) :
    Tendsto (fun x => f x /ₚ g x) l (𝓝 0) := by
  simpa only [mul_zero, divp, Function.comp_def] using h.mul
    (tendsto_inv_atBot_zero.comp (tendsto_comap_iff.mpr hg))

lemma Filter.Tendsto.const_div_atBot {g : α → 𝕜ˣ}
    (hg : Tendsto (fun x ↦ (g x : 𝕜)) l atBot) (r : 𝕜) :
    Tendsto (fun n ↦ r /ₚ g n) l (𝓝 0) :=
  tendsto_const_nhds.div_atBot hg

theorem Filter.Tendsto.inv_tendsto_atBot {f : α → 𝕜ˣ}
    (h : Tendsto (fun x ↦ (f x : 𝕜)) l atBot) :
    Tendsto (fun x ↦ (↑(f x)⁻¹ : 𝕜)) l (𝓝 0) :=
  tendsto_inv_atBot_zero.comp (tendsto_comap_iff.mpr h)

theorem Filter.Tendsto.inv_tendsto_nhdsLT_zero {f : α → 𝕜ˣ}
    (h : Tendsto (fun x ↦ (f x : 𝕜)) l (𝓝[<] 0)) :
    Tendsto (fun x ↦ (↑(f x)⁻¹ : 𝕜)) l atBot :=
  tendsto_inv_nhdsLT_zero.comp (tendsto_comap_iff.mpr h)

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
theorem tendsto_bdd_div_atTop_nhds_zero {f : α → 𝕜} {g : α → 𝕜ˣ} {b B : 𝕜}
    (hb : ∀ᶠ x in l, b ≤ f x) (hB : ∀ᶠ x in l, f x ≤ B) (hg : Tendsto (fun x ↦ (g x : 𝕜)) l atTop) :
    Tendsto (fun x => f x /ₚ g x) l (𝓝 0) := by
  exact bdd_le_mul_tendsto_zero hb hB hg.inv_tendsto_atTop

theorem tendsto_const_mul_zpow_atTop_zero {n : ℤ} {c : 𝕜} (hn : n < 0) :
    Tendsto (fun x : 𝕜ˣ => c * (↑(x ^ n) : 𝕜))
      (comap (fun u : 𝕜ˣ ↦ (u : 𝕜)) atTop) (𝓝 0) :=
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

theorem tendsto_const_mul_zpow_atTop_nhds_iff {n : ℤ} {c d : 𝕜} (hc : c ≠ 0) :
    Tendsto (fun x : 𝕜 => c * x ^ n) atTop (𝓝 d) ↔ n = 0 ∧ c = d ∨ n < 0 ∧ d = 0 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · cases n with
    | ofNat n =>
      left
      simpa [tendsto_const_mul_pow_nhds_iff hc] using h
    | negSucc n =>
      have hn := Int.negSucc_lt_zero n
      exact Or.inr ⟨hn, tendsto_nhds_unique h (tendsto_const_mul_zpow_atTop_zero hn)⟩
  · rcases h with h | h
    · simp only [h.left, h.right, zpow_zero, mul_one]
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
