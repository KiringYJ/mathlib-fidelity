/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Johannes Hölzl, Yury Kudryashov, Patrick Massot
-/
module

public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Order.Filter.AtTopBot.Archimedean
public import Mathlib.Order.Iterate
public import Mathlib.Topology.Algebra.Algebra
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Topology.Instances.Rat

/-!
# A collection of specific limit computations

This file, by design, is independent of `NormedSpace` in the import hierarchy.  It contains
important specific limit computations in metric spaces, in ordered rings/fields, and in specific
instances of these such as `ℝ`, `ℝ≥0` and `ℝ≥0∞`.
-/

@[expose] public section

assert_not_exists Module.Basis NormedSpace

noncomputable section

open Set Function Filter Finset Metric Nat uniformity NNReal ENNReal

open scoped Topology

variable {α : Type*} {β : Type*} {ι : Type*}

/-!
### Quotients with a vanishing denominator

A sequence such as `n ↦ (n : 𝕜)⁻¹` is defined only where its denominator is nonzero. Its limit is
stated on that exact domain, the subtype `{n : ℕ // n ≠ 0}` (in general `{x // g x ≠ 0}`), with the
filter `comap Subtype.val atTop` pulled back along the inclusion. Lemmas about a general quotient
`fun x ↦ f x / g x` take the invertibility of every value `g x` as evidence; they apply to a
quotient defined only where `g x ≠ 0` through the subtype `{x // g x ≠ 0}` and the filter
`comap Subtype.val l`.
-/

/-- The nonzero natural numbers are unbounded, so `comap Subtype.val atTop` is nontrivial on
them. -/
instance Filter.comap_val_ne_zero_atTop_neBot :
    (comap (Subtype.val : {n : ℕ // n ≠ 0} → ℕ) atTop).NeBot :=
  atTop_neBot.comap_of_range_mem (by
    rw [Subtype.range_coe_subtype]
    exact eventually_ne_atTop 0)

theorem NNRat.tendsto_inv_atTop_nhds_zero_nat :
    Tendsto (fun n : {n : ℕ // n ≠ 0} ↦ ((n : ℕ) : ℚ≥0)⁻¹) (comap Subtype.val atTop) (𝓝 0) :=
  (tendsto_natCast_atTop_atTop.comp tendsto_comap).fun_inv_tendsto_atTop
    (h0 := fun n : {n : ℕ // n ≠ 0} ↦ (Nat.cast_ne_zero.2 n.2).isUnit)

theorem NNRat.tendsto_algebraMap_inv_atTop_nhds_zero_nat (𝕜 : Type*) [Semiring 𝕜]
    [Algebra ℚ≥0 𝕜] [TopologicalSpace 𝕜] [ContinuousSMul ℚ≥0 𝕜] :
    Tendsto (algebraMap ℚ≥0 𝕜 ∘ fun n : {n : ℕ // n ≠ 0} ↦ ((n : ℕ) : ℚ≥0)⁻¹)
      (comap Subtype.val atTop) (𝓝 0) := by
  convert! (continuous_algebraMap ℚ≥0 𝕜).continuousAt.tendsto.comp tendsto_inv_atTop_nhds_zero_nat
  rw [map_zero]

theorem tendsto_inv_atTop_nhds_zero_nat {𝕜 : Type*} [DivisionSemiring 𝕜] [CharZero 𝕜]
    [TopologicalSpace 𝕜] [ContinuousSMul ℚ≥0 𝕜] :
    Tendsto (fun n : {n : ℕ // n ≠ 0} ↦ ((n : ℕ) : 𝕜)⁻¹) (comap Subtype.val atTop) (𝓝 0) := by
  convert! NNRat.tendsto_algebraMap_inv_atTop_nhds_zero_nat 𝕜
  simp

theorem tendsto_const_div_atTop_nhds_zero_nat {𝕜 : Type*} [DivisionSemiring 𝕜] [CharZero 𝕜]
    [TopologicalSpace 𝕜] [ContinuousSMul ℚ≥0 𝕜] [ContinuousMul 𝕜] (C : 𝕜) :
    Tendsto (fun n : {n : ℕ // n ≠ 0} ↦
      Checked.div C ((n : ℕ) : 𝕜) (Nat.cast_ne_zero.2 n.2).isUnit)
      (comap Subtype.val atTop) (𝓝 0) := by
  simpa only [mul_zero, div_eq_mul_inv₀] using
    (tendsto_const_nhds (x := C)).mul tendsto_inv_atTop_nhds_zero_nat

theorem tendsto_one_div_atTop_nhds_zero_nat {𝕜 : Type*} [DivisionSemiring 𝕜] [CharZero 𝕜]
    [TopologicalSpace 𝕜] [ContinuousSMul ℚ≥0 𝕜] :
    Tendsto (fun n : {n : ℕ // n ≠ 0} ↦
      Checked.div 1 ((n : ℕ) : 𝕜) (Nat.cast_ne_zero.2 n.2).isUnit)
      (comap Subtype.val atTop) (𝓝 0) := by
  simpa only [one_div₀] using tendsto_inv_atTop_nhds_zero_nat (𝕜 := 𝕜)

theorem EReal.tendsto_const_div_atTop_nhds_zero_nat {C : EReal} (h : C ≠ ⊥) (h' : C ≠ ⊤) :
    Tendsto (fun n : {n : ℕ // n ≠ 0} ↦ C / ((n : ℕ) : EReal)) (comap Subtype.val atTop)
      (𝓝 0) := by
  lift C to ℝ using ⟨h', h⟩
  have : (fun n : {n : ℕ // n ≠ 0} ↦ (C : EReal) / ((n : ℕ) : EReal)) =
      fun n : {n : ℕ // n ≠ 0} ↦ ((C / ((n : ℕ) : ℝ) : ℝ) : EReal) := by
    ext n
    exact (EReal.coe_div C ((n : ℕ) : ℝ) (hb := (Nat.cast_ne_zero.2 n.2).isUnit)).symm
  rw [this, ← coe_zero, tendsto_coe]
  exact _root_.tendsto_const_div_atTop_nhds_zero_nat C

theorem tendsto_one_div_add_atTop_nhds_zero_nat {𝕜 : Type*} [DivisionSemiring 𝕜] [CharZero 𝕜]
    [TopologicalSpace 𝕜] [ContinuousSMul ℚ≥0 𝕜] :
    Tendsto (fun n : ℕ ↦ Checked.div 1 ((n : 𝕜) + 1) (Nat.cast_add_one_ne_zero n).isUnit)
      atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ ↦ (⟨n + 1, n.succ_ne_zero⟩ : {n : ℕ // n ≠ 0})) atTop
      (comap Subtype.val atTop) := tendsto_comap_iff.2 (tendsto_add_atTop_nat 1)
  simpa [Function.comp_def] using (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := 𝕜)).comp h

theorem tendsto_algebraMap_inv_atTop_nhds_zero_nat {𝕜 : Type*} (A : Type*)
    [Semifield 𝕜] [CharZero 𝕜] [TopologicalSpace 𝕜] [ContinuousSMul ℚ≥0 𝕜]
    [Semiring A] [Algebra 𝕜 A] [TopologicalSpace A] [ContinuousSMul 𝕜 A] :
    Tendsto (algebraMap 𝕜 A ∘ fun n : {n : ℕ // n ≠ 0} ↦ ((n : ℕ) : 𝕜)⁻¹)
      (comap Subtype.val atTop) (𝓝 0) := by
  convert! (continuous_algebraMap 𝕜 A).continuousAt.tendsto.comp tendsto_inv_atTop_nhds_zero_nat
  rw [map_zero]

/-- To compute a limit along `comap Subtype.val atTop` on a subtype of `ℕ`, it suffices to compute
it on its nonzero indices. -/
private lemma tendsto_comap_val_atTop_of_ne_zero {p : ℕ → Prop} {β : Type*}
    {u : {n : ℕ // p n} → β} {l : Filter β}
    (h : Tendsto (fun n : {n : ℕ // p n ∧ n ≠ 0} ↦ u ⟨n, n.2.1⟩) (comap Subtype.val atTop) l) :
    Tendsto u (comap Subtype.val atTop) l := by
  have hr : range (fun n : {n : ℕ // p n ∧ n ≠ 0} ↦ (⟨n, n.2.1⟩ : {n : ℕ // p n})) ∈
      comap Subtype.val atTop := by
    refine mem_of_superset (preimage_mem_comap (eventually_ne_atTop 0)) ?_
    rintro ⟨n, hn⟩ (h0 : n ≠ 0)
    exact ⟨⟨n, hn, h0⟩, rfl⟩
  rw [← tendsto_comap'_iff hr, comap_comap]
  exact h

/-- On the nonzero indices of a subtype of `ℕ`, the inverses of the indices tend to `0`. -/
private lemma tendsto_inv_atTop_nhds_zero_nat_of_ne_zero {𝕜 : Type*} [DivisionSemiring 𝕜]
    [CharZero 𝕜] [TopologicalSpace 𝕜] [ContinuousSMul ℚ≥0 𝕜] {p : ℕ → Prop} :
    Tendsto (fun n : {n : ℕ // p n ∧ n ≠ 0} ↦
        Checked.inv ((n : ℕ) : 𝕜) (Nat.cast_ne_zero.2 n.2.2).isUnit)
      (comap Subtype.val atTop) (𝓝 0) := by
  have h : Tendsto (fun n : {n : ℕ // p n ∧ n ≠ 0} ↦ (⟨n, n.2.2⟩ : {n : ℕ // n ≠ 0}))
      (comap Subtype.val atTop) (comap Subtype.val atTop) := by
    rw [tendsto_comap_iff]
    exact tendsto_comap
  exact tendsto_inv_atTop_nhds_zero_nat.comp h

/-- The limit of `n / (n + x)` is 1, for any constant `x` (valid in `ℝ` or any topological division
algebra over `ℚ≥0`, e.g., `ℂ`). The quotient is taken on the indices `n` with `n + x ≠ 0`. -/
theorem tendsto_natCast_div_add_atTop {𝕜 : Type*} [DivisionSemiring 𝕜] [TopologicalSpace 𝕜]
    [CharZero 𝕜] [ContinuousSMul ℚ≥0 𝕜] [IsTopologicalSemiring 𝕜] [ContinuousInv₀ 𝕜] (x : 𝕜) :
    Tendsto (fun n : {n : ℕ // (n : 𝕜) + x ≠ 0} ↦
        Checked.div ((n : ℕ) : 𝕜) ((n : ℕ) + x) n.2.isUnit)
      (comap Subtype.val atTop) (𝓝 1) := by
  refine tendsto_comap_val_atTop_of_ne_zero ?_
  -- On the nonzero indices, `n / (n + x)` is the inverse of `1 + x * n⁻¹ = (n + x) * n⁻¹`.
  have key : ∀ n : {n : ℕ // (n : 𝕜) + x ≠ 0 ∧ n ≠ 0},
      1 + x * Checked.inv ((n : ℕ) : 𝕜) (Nat.cast_ne_zero.2 n.2.2).isUnit =
        ((n : ℕ) + x) * Checked.inv ((n : ℕ) : 𝕜) (Nat.cast_ne_zero.2 n.2.2).isUnit :=
    fun n ↦ by rw [add_mul, mul_inv_cancel₀]
  have hu : ∀ n : {n : ℕ // (n : 𝕜) + x ≠ 0 ∧ n ≠ 0},
      IsUnit (1 + x * Checked.inv ((n : ℕ) : 𝕜) (Nat.cast_ne_zero.2 n.2.2).isUnit) :=
    fun n ↦ key n ▸ n.2.1.isUnit.mul (IsUnit.inv₀ _)
  have hb : IsUnit (1 + x * 0 : 𝕜) := by simp
  have hlim := (((tendsto_const_nhds (x := x)).mul
    tendsto_inv_atTop_nhds_zero_nat_of_ne_zero).const_add (1 : 𝕜)).inv₀ (h0 := hu) (ha := hb)
  convert hlim using 2 with n
  · symm
    apply inv_eq_of_mul_eq_one_right₀
    rw [key n, div_eq_mul_inv₀, mul_assoc, ← mul_assoc (Checked.inv ((n : ℕ) : 𝕜) _),
      inv_mul_cancel₀, one_mul, mul_inv_cancel₀]
  · simp

/-- The limit of `(a + c * k) / (b + d * k)` is `c / d` for `d ≠ 0`; the quotient is taken on the
indices `k` with `b + d * k ≠ 0`. -/
theorem tendsto_add_mul_div_add_mul_atTop_nhds {𝕜 : Type*} [Semifield 𝕜] [CharZero 𝕜]
    [TopologicalSpace 𝕜] [ContinuousSMul ℚ≥0 𝕜] [IsTopologicalSemiring 𝕜] [ContinuousInv₀ 𝕜]
    (a b c : 𝕜) {d : 𝕜} (hd : d ≠ 0) :
    Tendsto (fun k : {k : ℕ // b + d * k ≠ 0} ↦
        Checked.div (a + c * (k : ℕ)) (b + d * (k : ℕ)) k.2.isUnit)
      (comap Subtype.val atTop) (𝓝 (c / d)) := by
  refine tendsto_comap_val_atTop_of_ne_zero ?_
  -- On the nonzero indices, divide the numerator and the denominator by `k`.
  have key : ∀ (e f : 𝕜) (k : {k : ℕ // b + d * k ≠ 0 ∧ k ≠ 0}),
      e * Checked.inv ((k : ℕ) : 𝕜) (Nat.cast_ne_zero.2 k.2.2).isUnit + f =
        (e + f * (k : ℕ)) * Checked.inv ((k : ℕ) : 𝕜) (Nat.cast_ne_zero.2 k.2.2).isUnit :=
    fun e f k ↦ by rw [add_mul, mul_assoc, mul_inv_cancel₀, mul_one]
  have hu : ∀ k : {k : ℕ // b + d * k ≠ 0 ∧ k ≠ 0},
      IsUnit (b * Checked.inv ((k : ℕ) : 𝕜) (Nat.cast_ne_zero.2 k.2.2).isUnit + d) :=
    fun k ↦ key b d k ▸ k.2.1.isUnit.mul (IsUnit.inv₀ _)
  have hinv := tendsto_inv_atTop_nhds_zero_nat_of_ne_zero (𝕜 := 𝕜) (p := fun k ↦ b + d * k ≠ 0)
  have hb : IsUnit (b * 0 + d) := by simpa using hd.isUnit
  have hlim := (((tendsto_const_nhds (x := a)).mul hinv).add_const c).div₀
    (((tendsto_const_nhds (x := b)).mul hinv).add_const d) (h₀ := hu) (hb := hb)
  convert hlim using 2 with k
  · rw [_root_.eq_div_iff, key b d k, ← mul_assoc, div_mul_cancel₀, key a c k]
  · simp

/-- For any positive `m : ℕ`, `((n % m : ℕ) : ℝ) / (n : ℝ)` tends to `0` as `n` tends to `∞`; the
quotient is taken on the nonzero indices. -/
theorem tendsto_mod_div_atTop_nhds_zero_nat {m : ℕ} (hm : 0 < m) :
    Tendsto (fun n : {n : ℕ // n ≠ 0} ↦ (((n : ℕ) % m : ℕ) : ℝ) / ((n : ℕ) : ℝ))
      (comap Subtype.val atTop) (𝓝 0) :=
  tendsto_bdd_div_atTop_nhds_zero
    (h₀ := fun n : {n : ℕ // n ≠ 0} ↦ (Nat.cast_ne_zero.2 n.2).isUnit)
    (.of_forall fun _ ↦ Nat.cast_nonneg _)
    (.of_forall fun n ↦ cast_le.mpr (mod_lt n hm).le)
    (tendsto_natCast_atTop_atTop.comp tendsto_comap)

/-- If `a ≠ 0`, `(a * x + c)⁻¹` tends to `0` as `x` tends to `∞`; the inverse is taken where
`a * x + c ≠ 0`. -/
theorem tendsto_mul_add_inv_atTop_nhds_zero (a c : ℝ) (ha : a ≠ 0) :
    Tendsto (fun x : {x : ℝ // a * x + c ≠ 0} ↦ Checked.inv (a * x + c) x.2.isUnit)
      (comap Subtype.val atTop) (𝓝 0) := by
  have h : Tendsto (fun x : {x : ℝ // a * x + c ≠ 0} ↦ (x : ℝ)) (comap Subtype.val atTop) atTop :=
    tendsto_comap
  obtain ha' | ha' := lt_or_gt_of_ne ha
  · exact (tendsto_atBot_add_const_right _ c (h.const_mul_atTop_of_neg ha')).fun_inv_tendsto_atBot
      (h0 := fun x : {x : ℝ // a * x + c ≠ 0} ↦ x.2.isUnit)
  · exact (tendsto_atTop_add_const_right _ c (h.const_mul_atTop ha')).fun_inv_tendsto_atTop
      (h0 := fun x : {x : ℝ // a * x + c ≠ 0} ↦ x.2.isUnit)

/-- If `g` is eventually nonzero, the checked quotient `f x / g x` eventually exists and
satisfies `(f x / g x) * g x = f x`. -/
theorem Filter.EventuallyEq.div_mul_cancel {α G : Type*} [GroupWithZero G] {f g : α → G}
    {l : Filter α} (hg : Tendsto g l (𝓟 {0}ᶜ)) :
    ∀ᶠ x in l, ∃ h : IsUnit (g x), Checked.div (f x) (g x) h * g x = f x := by
  filter_upwards [hg.eventually_mem (mem_principal_self ({0} : Set G)ᶜ)] with x hx
  have hx' : g x ≠ 0 := hx
  exact ⟨hx'.isUnit, div_mul_cancel₀ _⟩

/-- If `g` tends to `∞`, the checked quotient `f x / g x` eventually exists and cancels. -/
theorem Filter.EventuallyEq.div_mul_cancel_atTop {α K : Type*}
    [DivisionSemiring K] [LinearOrder K] [IsStrictOrderedRing K]
    {f g : α → K} {l : Filter α} (hg : Tendsto g l atTop) :
    ∀ᶠ x in l, ∃ h : IsUnit (g x), Checked.div (f x) (g x) h * g x = f x :=
  div_mul_cancel <| hg.mono_right <| le_principal_iff.mpr <|
    mem_of_superset (Ioi_mem_atTop 0) fun _ hx ↦ ne_of_gt hx

/-- If when `x` tends to `∞`, `g` tends to `∞` and `f x / g x` tends to a positive
  constant, then `f` tends to `∞`. -/
theorem Filter.Tendsto.num {α K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [TopologicalSpace K] [OrderTopology K]
    {f g : α → K} {hgUnit : ∀ x, IsUnit (g x)} {l : Filter α} (hg : Tendsto g l atTop) {a : K}
    (ha : 0 < a) (hlim : Tendsto (fun x => Checked.div (f x) (g x) (hgUnit x)) l (𝓝 a)) :
    Tendsto f l atTop :=
  (hlim.pos_mul_atTop ha hg).congr fun x ↦ div_mul_cancel₀ (f x)

/-- If when `x` tends to `∞`, `f` tends to `∞` and `f x / g x` tends to a positive
  constant, then `g` tends to `∞`. -/
theorem Filter.Tendsto.den {α K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [TopologicalSpace K] [OrderTopology K]
    {f g : α → K} {hgUnit : ∀ x, IsUnit (g x)} {l : Filter α} (hf : Tendsto f l atTop) {a : K}
    (ha : 0 < a) (hlim : Tendsto (fun x => Checked.div (f x) (g x) (hgUnit x)) l (𝓝 a)) :
    Tendsto g l atTop := by
  have h2a : 0 < 2 * a := by positivity
  refine tendsto_atTop_mono' l ?_ (hf.atTop_div_const h2a)
  filter_upwards [hlim.eventually (gt_mem_nhds (by linarith : a < 2 * a)),
    hlim.eventually (lt_mem_nhds ha), hf.eventually_gt_atTop 0] with x hx2 hx0 hf0
  have hg0 : 0 < g x := (div_pos_iff_of_pos_left hf0).1 hx0
  rw [div_le_iff₀ h2a]
  rw [div_lt_iff₀ hg0] at hx2
  linarith

/-- If when `x` tends to `∞`, `f x / g x` tends to a positive constant, then `f` tends to `∞` if
  and only if `g` tends to `∞`. -/
theorem Filter.Tendsto.num_atTop_iff_den_atTop {α K : Type*}
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] [TopologicalSpace K]
    [OrderTopology K] {f g : α → K} {hgUnit : ∀ x, IsUnit (g x)} {l : Filter α} {a : K}
    (ha : 0 < a) (hlim : Tendsto (fun x => Checked.div (f x) (g x) (hgUnit x)) l (𝓝 a)) :
    Tendsto f l atTop ↔ Tendsto g l atTop :=
  ⟨fun hf ↦ hf.den ha hlim, fun hg ↦ hg.num ha hlim⟩

/-! ### Powers -/


theorem tendsto_add_one_pow_atTop_atTop_of_pos
    [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] [Archimedean α] {r : α}
    (h : 0 < r) : Tendsto (fun n : ℕ ↦ (r + 1) ^ n) atTop atTop :=
  tendsto_atTop_atTop_of_monotone' (pow_right_mono₀ <| le_add_of_nonneg_left h.le) <|
    not_bddAbove_iff.2 fun _ ↦ Set.exists_range_iff.2 <| add_one_pow_unbounded_of_pos _ h

theorem tendsto_pow_atTop_atTop_of_one_lt
    [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] [ExistsAddOfLE α] [Archimedean α] {r : α}
    (h : 1 < r) : Tendsto (fun n : ℕ ↦ r ^ n) atTop atTop := by
  obtain ⟨r, r0, rfl⟩ := exists_pos_add_of_lt' h
  rw [add_comm]
  exact tendsto_add_one_pow_atTop_atTop_of_pos r0

theorem tendsto_pow_atTop_nhds_zero_of_lt_one {𝕜 : Type*}
    [Semifield 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [ExistsAddOfLE 𝕜] [Archimedean 𝕜]
    [TopologicalSpace 𝕜] [OrderTopology 𝕜] {r : 𝕜} (h₁ : 0 ≤ r) (h₂ : r < 1) :
    Tendsto (fun n : ℕ ↦ r ^ n) atTop (𝓝 0) :=
  h₁.eq_or_lt.elim
    (fun hr ↦ (tendsto_add_atTop_iff_nat 1).mp <| by
      simp [_root_.pow_succ, ← hr])
    (fun hr ↦
      have := (one_lt_inv₀ hr).2 h₂ |> tendsto_pow_atTop_atTop_of_one_lt
      (this.fun_inv_tendsto_atTop (h0 := fun n ↦ hr.ne'.isUnit.inv₀.pow n)).congr
        fun n ↦ by simp)

@[simp] theorem tendsto_pow_atTop_nhds_zero_iff {𝕜 : Type*}
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [Archimedean 𝕜]
    [TopologicalSpace 𝕜] [OrderTopology 𝕜] {r : 𝕜} :
    Tendsto (fun n : ℕ ↦ r ^ n) atTop (𝓝 0) ↔ |r| < 1 := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  refine ⟨fun h ↦ by_contra (fun hr_le ↦ ?_), fun h ↦ ?_⟩
  · by_cases hr : 1 = |r|
    · replace h : Tendsto (fun n : ℕ ↦ |r| ^ n) atTop (𝓝 0) := by simpa only [← abs_pow, h]
      simp only [hr.symm, one_pow] at h
      exact zero_ne_one <| tendsto_nhds_unique h tendsto_const_nhds
    · apply @not_tendsto_nhds_of_tendsto_atTop 𝕜 ℕ _ _ _ _ atTop _ (fun n ↦ |r| ^ n) _ 0 _
      · refine (pow_right_strictMono₀ <| lt_of_le_of_ne (le_of_not_gt hr_le)
          hr).monotone.tendsto_atTop_atTop (fun b ↦ ?_)
        obtain ⟨n, hn⟩ := (pow_unbounded_of_one_lt b (lt_of_le_of_ne (le_of_not_gt hr_le) hr))
        exact ⟨n, le_of_lt hn⟩
      · simpa only [← abs_pow]
  · simpa only [← abs_pow] using! (tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg r)) h

theorem tendsto_pow_atTop_nhdsWithin_zero_of_lt_one {𝕜 : Type*}
    [Semifield 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [ExistsAddOfLE 𝕜]
    [Archimedean 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜] {r : 𝕜} (h₁ : 0 < r) (h₂ : r < 1) :
    Tendsto (fun n : ℕ ↦ r ^ n) atTop (𝓝[>] 0) :=
  tendsto_inf.2
    ⟨tendsto_pow_atTop_nhds_zero_of_lt_one h₁.le h₂,
      tendsto_principal.2 <| Eventually.of_forall fun _ ↦ pow_pos h₁ _⟩

theorem uniformity_basis_dist_pow_of_lt_one {α : Type*} [PseudoMetricSpace α] {r : ℝ} (h₀ : 0 < r)
    (h₁ : r < 1) :
    (uniformity α).HasBasis (fun _ : ℕ ↦ True) fun k ↦ { p : α × α | dist p.1 p.2 < r ^ k } :=
  Metric.mk_uniformity_basis (fun _ _ ↦ pow_pos h₀ _) fun _ ε0 ↦
    (exists_pow_lt_of_lt_one ε0 h₁).imp fun _ hk ↦ ⟨trivial, hk.le⟩

theorem geom_lt {u : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c) {n : ℕ} (hn : 0 < n)
    (h : ∀ k < n, c * u k < u (k + 1)) : c ^ n * u 0 < u n := by
  apply (monotone_mul_left_of_nonneg hc).seq_pos_lt_seq_of_le_of_lt hn _ _ h
  · simp
  · simp [_root_.pow_succ', mul_assoc]

theorem geom_le {u : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c) (n : ℕ) (h : ∀ k < n, c * u k ≤ u (k + 1)) :
    c ^ n * u 0 ≤ u n := by
  apply (monotone_mul_left_of_nonneg hc).seq_le_seq n _ _ h <;>
    simp [_root_.pow_succ', mul_assoc]

theorem lt_geom {u : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c) {n : ℕ} (hn : 0 < n)
    (h : ∀ k < n, u (k + 1) < c * u k) : u n < c ^ n * u 0 := by
  apply (monotone_mul_left_of_nonneg hc).seq_pos_lt_seq_of_lt_of_le hn _ h _
  · simp
  · simp [_root_.pow_succ', mul_assoc]

theorem le_geom {u : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c) (n : ℕ) (h : ∀ k < n, u (k + 1) ≤ c * u k) :
    u n ≤ c ^ n * u 0 := by
  apply (monotone_mul_left_of_nonneg hc).seq_le_seq n _ h _ <;>
    simp [_root_.pow_succ', mul_assoc]

/-- If a sequence `v` of real numbers satisfies `k * v n ≤ v (n+1)` with `1 < k`,
then it goes to +∞. -/
theorem tendsto_atTop_of_geom_le {v : ℕ → ℝ} {c : ℝ} (h₀ : 0 < v 0) (hc : 1 < c)
    (hu : ∀ n, c * v n ≤ v (n + 1)) : Tendsto v atTop atTop :=
  (tendsto_atTop_mono fun n ↦ geom_le (zero_le_one.trans hc.le) n fun k _ ↦ hu k) <|
    (tendsto_pow_atTop_atTop_of_one_lt hc).atTop_mul_const h₀

theorem NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one {r : ℝ≥0} (hr : r < 1) :
    Tendsto (fun n : ℕ ↦ r ^ n) atTop (𝓝 0) :=
  NNReal.tendsto_coe.1 <| by
    simp only [NNReal.coe_pow, NNReal.coe_zero,
      _root_.tendsto_pow_atTop_nhds_zero_of_lt_one r.coe_nonneg hr]

@[simp]
protected theorem NNReal.tendsto_pow_atTop_nhds_zero_iff {r : ℝ≥0} :
    Tendsto (fun n : ℕ => r ^ n) atTop (𝓝 0) ↔ r < 1 :=
  ⟨fun h => by simpa [coe_pow, coe_zero, abs_eq, coe_lt_one, val_eq_coe] using
    tendsto_pow_atTop_nhds_zero_iff.mp <| tendsto_coe.mpr h, tendsto_pow_atTop_nhds_zero_of_lt_one⟩

theorem ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one {r : ℝ≥0∞} (hr : r < 1) :
    Tendsto (fun n : ℕ ↦ r ^ n) atTop (𝓝 0) := by
  rcases ENNReal.lt_iff_exists_coe.1 hr with ⟨r, rfl, hr'⟩
  rw [← ENNReal.coe_zero]
  norm_cast at *
  apply NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hr

@[simp]
protected theorem ENNReal.tendsto_pow_atTop_nhds_zero_iff {r : ℝ≥0∞} :
    Tendsto (fun n : ℕ => r ^ n) atTop (𝓝 0) ↔ r < 1 := by
  refine ⟨fun h ↦ ?_, tendsto_pow_atTop_nhds_zero_of_lt_one⟩
  lift r to NNReal
  · refine fun hr ↦ top_ne_zero (tendsto_nhds_unique (EventuallyEq.tendsto ?_) (hr ▸ h))
    exact eventually_atTop.mpr ⟨1, fun _ hn ↦ pow_eq_top_iff.mpr ⟨rfl, Nat.pos_iff_ne_zero.mp hn⟩⟩
  rw [← coe_zero] at h
  norm_cast at h ⊢
  exact NNReal.tendsto_pow_atTop_nhds_zero_iff.mp h

@[simp]
protected theorem ENNReal.tendsto_pow_atTop_nhds_top_iff {r : ℝ≥0∞} :
    Tendsto (fun n ↦ r ^ n) atTop (𝓝 ∞) ↔ 1 < r := by
  refine ⟨?_, ?_⟩
  · contrapose!
    intro r_le_one h_tends
    specialize h_tends (Ioi_mem_nhds one_lt_top)
    simp only [Filter.mem_map, mem_atTop_sets, Set.mem_preimage, Set.mem_Ioi] at h_tends
    obtain ⟨n, hn⟩ := h_tends
    exact lt_irrefl _ <| lt_of_lt_of_le (hn n le_rfl) <| pow_le_one₀ zero_le r_le_one
  · intro r_gt_one
    have obs := @Tendsto.inv ℝ≥0∞ ℕ _ _ _ (fun n ↦ (r⁻¹) ^ n) atTop 0
    simp only [ENNReal.tendsto_pow_atTop_nhds_zero_iff, inv_zero] at obs
    simpa [← ENNReal.inv_pow] using obs <| ENNReal.inv_lt_one.mpr r_gt_one

lemma ENNReal.eq_zero_of_le_mul_pow {x r : ℝ≥0∞} {ε : ℝ≥0} (hr : r < 1)
    (h : ∀ n : ℕ, x ≤ ε * r ^ n) : x = 0 := by
  rw [← nonpos_iff_eq_zero]
  refine ge_of_tendsto' (f := fun (n : ℕ) ↦ ε * r ^ n) (x := atTop) ?_ h
  rw [← mul_zero (M₀ := ℝ≥0∞) (a := ε)]
  exact Tendsto.const_mul (tendsto_pow_atTop_nhds_zero_of_lt_one hr) (Or.inr coe_ne_top)

/-! ### Geometric series -/

section Geometric

theorem hasSum_geometric_of_lt_one {r : ℝ} (h₁ : 0 ≤ r) (h₂ : r < 1) :
    HasSum (fun n : ℕ ↦ r ^ n) (1 - r)⁻¹ :=
  have : r ≠ 1 := ne_of_lt h₂
  have : Tendsto (fun n ↦ (r ^ n - 1) * (r - 1)⁻¹) atTop (𝓝 ((0 - 1) * (r - 1)⁻¹)) :=
    ((tendsto_pow_atTop_nhds_zero_of_lt_one h₁ h₂).sub tendsto_const_nhds).mul tendsto_const_nhds
  (hasSum_iff_tendsto_nat_of_nonneg (pow_nonneg h₁) _).mpr <| by
    have hlim : (0 - 1) * (r - 1)⁻¹ = (1 - r)⁻¹ := by
      rw [zero_sub, neg_one_mul, neg_inv₀]
      simp only [neg_sub]
    rw [← hlim]
    refine this.congr fun n ↦ ?_
    rw [geom_sum_eq ‹r ≠ 1›]
    rfl

theorem summable_geometric_of_lt_one {r : ℝ} (h₁ : 0 ≤ r) (h₂ : r < 1) :
    Summable fun n : ℕ ↦ r ^ n :=
  ⟨_, hasSum_geometric_of_lt_one h₁ h₂⟩


theorem tsum_geometric_of_lt_one {r : ℝ} (h₁ : 0 ≤ r) (h₂ : r < 1) : ∑' n : ℕ, r ^ n = (1 - r)⁻¹ :=
  (hasSum_geometric_of_lt_one h₁ h₂).tsum_eq

theorem hasSum_geometric_two : HasSum (fun n : ℕ ↦ ((1 : ℝ) / 2) ^ n) 2 := by
  convert! hasSum_geometric_of_lt_one _ _ <;> norm_num

theorem summable_geometric_two : Summable fun n : ℕ ↦ ((1 : ℝ) / 2) ^ n :=
  ⟨_, hasSum_geometric_two⟩

theorem summable_geometric_two_encode {ι : Type*} [Encodable ι] :
    Summable fun i : ι ↦ (1 / 2 : ℝ) ^ Encodable.encode i :=
  summable_geometric_two.comp_injective Encodable.encode_injective

theorem tsum_geometric_two : (∑' n : ℕ, ((1 : ℝ) / 2) ^ n) = 2 :=
  hasSum_geometric_two.tsum_eq

theorem sum_geometric_two_le (n : ℕ) : (∑ i ∈ range n, (1 / (2 : ℝ)) ^ i) ≤ 2 := by
  have : ∀ i, 0 ≤ (1 / (2 : ℝ)) ^ i := by
    intro i
    apply pow_nonneg
    norm_num
  convert! summable_geometric_two.sum_le_tsum (range n) (fun i _ ↦ this i)
  exact tsum_geometric_two.symm

theorem tsum_geometric_inv_two : (∑' n : ℕ, (2 : ℝ)⁻¹ ^ n) = 2 := by
  simpa only [one_div₀] using tsum_geometric_two

/-- The sum of `2⁻¹ ^ i` for `n ≤ i` equals `2 * 2⁻¹ ^ n`. -/
theorem tsum_geometric_inv_two_ge (n : ℕ) :
    (∑' i, ite (n ≤ i) ((2 : ℝ)⁻¹ ^ i) 0) = 2 * 2⁻¹ ^ n := by
  have A : Summable fun i : ℕ ↦ ite (n ≤ i) ((2⁻¹ : ℝ) ^ i) 0 := by
    simpa only [← piecewise_eq_indicator, one_div₀]
      using! summable_geometric_two.indicator {i | n ≤ i}
  have B : ((Finset.range n).sum fun i : ℕ ↦ ite (n ≤ i) ((2⁻¹ : ℝ) ^ i) 0) = 0 :=
    Finset.sum_eq_zero fun i hi ↦
      ite_eq_right_iff.2 fun h ↦ (lt_irrefl _ ((Finset.mem_range.1 hi).trans_le h)).elim
  simp [-inv_pow₀, ← Summable.sum_add_tsum_nat_add n A, B, pow_add, _root_.tsum_mul_right,
    tsum_geometric_inv_two]

theorem hasSum_geometric_two' (a : ℝ) : HasSum (fun n : ℕ ↦ a / 2 / 2 ^ n) a := by
  convert!
    HasSum.mul_left (a / 2)
      (hasSum_geometric_of_lt_one (le_of_lt one_half_pos) one_half_lt_one) using 1
  · funext n
    simp only [one_div₀, inv_pow₀]
    rfl
  · norm_num

theorem summable_geometric_two' (a : ℝ) : Summable fun n : ℕ ↦ a / 2 / 2 ^ n :=
  ⟨a, hasSum_geometric_two' a⟩

theorem tsum_geometric_two' (a : ℝ) : ∑' n : ℕ, a / 2 / 2 ^ n = a :=
  (hasSum_geometric_two' a).tsum_eq

/-- **Sum of a Geometric Series** -/
theorem NNReal.hasSum_geometric {r : ℝ≥0} (hr : r < 1) : HasSum (fun n : ℕ ↦ r ^ n) (1 - r)⁻¹ := by
  apply NNReal.hasSum_coe.1
  push_cast
  simp only [NNReal.coe_sub (le_of_lt hr), NNReal.coe_one]
  exact hasSum_geometric_of_lt_one r.coe_nonneg hr

theorem NNReal.summable_geometric {r : ℝ≥0} (hr : r < 1) : Summable fun n : ℕ ↦ r ^ n :=
  ⟨_, NNReal.hasSum_geometric hr⟩

theorem NNReal.tsum_geometric {r : ℝ≥0} (hr : r < 1) : ∑' n : ℕ, r ^ n = (1 - r)⁻¹ :=
  (NNReal.hasSum_geometric hr).tsum_eq

@[deprecated (since := "2026-03-18")] alias tsum_geometric_nnreal := NNReal.tsum_geometric

/-- The series `pow r` converges to the reciprocal of `ENNReal.monus 1 r`.
It is finite when `r < 1` and equals `∞` when `1 ≤ r`. -/
@[simp]
theorem ENNReal.tsum_geometric (r : ℝ≥0∞) : ∑' n : ℕ, r ^ n = (monus 1 r)⁻¹ := by
  rcases lt_or_ge r 1 with hr | hr
  · rcases ENNReal.lt_iff_exists_coe.1 hr with ⟨r, rfl, hr'⟩
    norm_cast at *
    convert! ENNReal.tsum_coe_eq (NNReal.hasSum_geometric hr)
    rw [ENNReal.coe_inv (hr := (ne_of_gt <| tsub_pos_iff_lt.2 hr).isUnit), coe_monus, coe_one]
  · rw [monus_eq_zero_of_le hr, ENNReal.inv_zero, ENNReal.tsum_eq_iSup_nat, iSup_eq_top]
    refine fun a ha ↦
      (ENNReal.exists_nat_gt (lt_top_iff_ne_top.1 ha)).imp fun n hn ↦ lt_of_lt_of_le hn ?_
    calc
      (n : ℝ≥0∞) = ∑ i ∈ range n, 1 := by rw [sum_const, nsmul_one, card_range]
      _ ≤ ∑ i ∈ range n, r ^ i := by gcongr; apply one_le_pow₀ hr

theorem ENNReal.tsum_geometric_add_one (r : ℝ≥0∞) : ∑' n : ℕ, r ^ (n + 1) = r * (monus 1 r)⁻¹ := by
  simp only [_root_.pow_succ', ENNReal.tsum_mul_left, ENNReal.tsum_geometric]

lemma ENNReal.tsum_two_zpow_neg_add_one :
    ∑' m : ℕ, 2 ^ (-1 - m : ℤ) = (1 : ℝ≥0∞) := by
  simp_rw [neg_sub_left, ENNReal.zpow_neg, ← Nat.cast_one (R := ℤ), ← Nat.cast_add,
    ENNReal.zpow_natCast, ENNReal.inv_pow, ENNReal.tsum_geometric_add_one,
    one_monus_inv_two, inv_inv]
  exact ENNReal.inv_mul_cancel (Ne.symm (NeZero.ne' 2)) (Ne.symm top_ne_ofNat)

open Encodable

protected lemma ENNReal.tsum_geometric_two : ∑' n, (2⁻¹ : ℝ≥0∞) ^ n = 2 := by simp

lemma ENNReal.tsum_geometric_two_encode_le_two {ι : Type*} [Encodable ι] :
    ∑' i : ι, (2⁻¹ : ℝ≥0∞) ^ encode i ≤ 2 :=
  (ENNReal.tsum_comp_le_tsum_of_injective encode_injective _).trans_eq ENNReal.tsum_geometric_two

lemma tsum_geometric_lt_top {r : ℝ≥0∞} : ∑' n, r ^ n < ∞ ↔ r < 1 := by simp

lemma tsum_geometric_encode_lt_top {r : ℝ≥0∞} (hr : r < 1) {ι : Type*} [Encodable ι] :
    ∑' i : ι, (r : ℝ≥0∞) ^ encode i < ∞ :=
  (ENNReal.tsum_comp_le_tsum_of_injective encode_injective _).trans_lt <| by simpa

end Geometric

/-!
### Sequences with geometrically decaying distance in metric spaces

In this paragraph, we discuss sequences in metric spaces or emetric spaces for which the distance
between two consecutive terms decays geometrically. We show that such sequences are Cauchy
sequences, and bound their distances to the limit. We also discuss series with geometrically
decaying terms.
-/


section EDistLeGeometric

variable [PseudoEMetricSpace α] (r C : ℝ≥0∞) (hr : r < 1) (hC : C ≠ ⊤) {f : ℕ → α}
  (hu : ∀ n, edist (f n) (f (n + 1)) ≤ C * r ^ n)

include hr hC hu in
/-- If `edist (f n) (f (n+1))` is bounded by `C * r^n`, `C ≠ ∞`, `r < 1`,
then `f` is a Cauchy sequence. -/
theorem cauchySeq_of_edist_le_geometric : CauchySeq f := by
  refine cauchySeq_of_edist_le_of_tsum_ne_top _ hu ?_
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
  exact ENNReal.mul_ne_top hC (ENNReal.inv_ne_top.2 (ENNReal.monus_pos_of_lt hr).ne')

include hu in
/-- If `edist (f n) (f (n+1))` is bounded by `C * r^n`, then the distance from
`f n` to the limit of `f` is bounded by the sum of the geometric tail. -/
theorem edist_le_of_edist_le_geometric_of_tendsto {a : α} (ha : Tendsto f atTop (𝓝 a)) (n : ℕ) :
    edist (f n) a ≤ C * r ^ n * ∑' m : ℕ, r ^ m := by
  simpa only [pow_add, ← mul_assoc, ENNReal.tsum_mul_left] using
    edist_le_tsum_of_edist_le_of_tendsto _ hu ha n

include hu in
/-- If `edist (f n) (f (n+1))` is bounded by `C * r^n`, then the distance from
`f 0` to the limit of `f` is bounded by the sum of the geometric series. -/
theorem edist_le_of_edist_le_geometric_of_tendsto₀ {a : α} (ha : Tendsto f atTop (𝓝 a)) :
    edist (f 0) a ≤ C * ∑' m : ℕ, r ^ m := by
  simpa only [_root_.pow_zero, mul_one] using edist_le_of_edist_le_geometric_of_tendsto r C hu ha 0

end EDistLeGeometric

section EDistLeGeometricTwo

theorem ENNReal.isUnit_two_pow (n : ℕ) : IsUnit ((2 : ℝ≥0∞) ^ n) :=
  (ENNReal.isUnit_iff.2 ⟨two_ne_zero, ENNReal.ofNat_ne_top⟩ : IsUnit (2 : ℝ≥0∞)).pow n

variable [PseudoEMetricSpace α] (C : ℝ≥0∞) (hC : C ≠ ⊤) {f : ℕ → α}
  (hu : ∀ n, edist (f n) (f (n + 1)) ≤ ENNReal.div C (2 ^ n)
    ⟨(ENNReal.isUnit_iff.1 (ENNReal.isUnit_two_pow n)).1,
      Or.inr (ENNReal.isUnit_iff.1 (ENNReal.isUnit_two_pow n)).2⟩)
  {a : α} (ha : Tendsto f atTop (𝓝 a))

include hC hu in
/-- If `edist (f n) (f (n+1))` is bounded by `C * 2^-n`, then `f` is a Cauchy sequence. -/
theorem cauchySeq_of_edist_le_geometric_two : CauchySeq f := by
  simp only [ENNReal.div_eq_mul_inv, ENNReal.inv_pow] at hu
  refine cauchySeq_of_edist_le_geometric 2⁻¹ C ?_ hC hu
  simp

include hu ha in
/-- If `edist (f n) (f (n+1))` is bounded by `C * 2^-n`, then the distance from
`f n` to the limit of `f` is bounded above by `2 * C * 2^-n`. -/
theorem edist_le_of_edist_le_geometric_two_of_tendsto (n : ℕ) :
    edist (f n) a ≤ ENNReal.div (2 * C) (2 ^ n)
      ⟨(ENNReal.isUnit_iff.1 (ENNReal.isUnit_two_pow n)).1,
        Or.inr (ENNReal.isUnit_iff.1 (ENNReal.isUnit_two_pow n)).2⟩ := by
  simp only [ENNReal.div_eq_mul_inv, ENNReal.inv_pow] at hu
  calc
    _ ≤ C * (2⁻¹ : ℝ≥0∞) ^ n * ∑' m : ℕ, (2⁻¹ : ℝ≥0∞) ^ m :=
      edist_le_of_edist_le_geometric_of_tendsto 2⁻¹ C hu ha n
    _ = _ := by
      rw [ENNReal.tsum_geometric_two, ENNReal.div_eq_mul_inv, ENNReal.inv_pow]
      ac_rfl

include hu ha in
/-- If `edist (f n) (f (n+1))` is bounded by `C * 2^-n`, then the distance from
`f 0` to the limit of `f` is bounded above by `2 * C`. -/
theorem edist_le_of_edist_le_geometric_two_of_tendsto₀ : edist (f 0) a ≤ 2 * C := by
  simpa only [_root_.pow_zero, ENNReal.div_one] using
    edist_le_of_edist_le_geometric_two_of_tendsto C hu ha 0

end EDistLeGeometricTwo

section LeGeometric

variable [PseudoMetricSpace α] {r C : ℝ} {f : ℕ → α}

section
variable (hr : r < 1) (hu : ∀ n, dist (f n) (f (n + 1)) ≤ C * r ^ n)
include hr hu

/-- If `dist (f n) (f (n+1))` is bounded by `C * r^n`, `r < 1`, then `f` is a Cauchy sequence. -/
theorem aux_hasSum_of_le_geometric : HasSum (fun n : ℕ ↦ C * r ^ n) (C / (1 - r)) := by
  rcases sign_cases_of_C_mul_pow_nonneg fun n ↦ dist_nonneg.trans (hu n) with (rfl | ⟨_, r₀⟩)
  · simp [hasSum_zero]
  · exact (hasSum_geometric_of_lt_one r₀ hr).mul_left C

variable (r C)

/-- If `dist (f n) (f (n+1))` is bounded by `C * r^n`, `r < 1`, then `f` is a Cauchy sequence.
Note that this lemma does not assume `0 ≤ C` or `0 ≤ r`. -/
theorem cauchySeq_of_le_geometric : CauchySeq f :=
  cauchySeq_of_dist_le_of_summable _ hu ⟨_, aux_hasSum_of_le_geometric hr hu⟩

/-- If `dist (f n) (f (n+1))` is bounded by `C * r^n`, `r < 1`, then the distance from
`f n` to the limit of `f` is bounded above by `C * r^n / (1 - r)`. -/
theorem dist_le_of_le_geometric_of_tendsto₀ {a : α} (ha : Tendsto f atTop (𝓝 a)) :
    dist (f 0) a ≤ C / (1 - r) :=
  (aux_hasSum_of_le_geometric hr hu).tsum_eq ▸
    dist_le_tsum_of_dist_le_of_tendsto₀ _ hu ⟨_, aux_hasSum_of_le_geometric hr hu⟩ ha

/-- If `dist (f n) (f (n+1))` is bounded by `C * r^n`, `r < 1`, then the distance from
`f 0` to the limit of `f` is bounded above by `C / (1 - r)`. -/
theorem dist_le_of_le_geometric_of_tendsto {a : α} (ha : Tendsto f atTop (𝓝 a)) (n : ℕ) :
    dist (f n) a ≤ C * r ^ n / (1 - r) := by
  have := aux_hasSum_of_le_geometric hr hu
  convert! dist_le_tsum_of_dist_le_of_tendsto _ hu ⟨_, this⟩ ha n
  simp only [pow_add, mul_left_comm C]
  rw [mul_div_right_comm₀, mul_comm]
  exact (this.mul_left _).tsum_eq.symm

end

variable (hu₂ : ∀ n, dist (f n) (f (n + 1)) ≤ C / 2 / 2 ^ n)
include hu₂

/-- If `dist (f n) (f (n+1))` is bounded by `(C / 2) / 2^n`, then `f` is a Cauchy sequence. -/
theorem cauchySeq_of_le_geometric_two : CauchySeq f :=
  cauchySeq_of_dist_le_of_summable _ hu₂ <| ⟨_, hasSum_geometric_two' C⟩

/-- If `dist (f n) (f (n+1))` is bounded by `(C / 2) / 2^n`, then the distance from
`f 0` to the limit of `f` is bounded above by `C`. -/
theorem dist_le_of_le_geometric_two_of_tendsto₀ {a : α} (ha : Tendsto f atTop (𝓝 a)) :
    dist (f 0) a ≤ C :=
  tsum_geometric_two' C ▸ dist_le_tsum_of_dist_le_of_tendsto₀ _ hu₂ (summable_geometric_two' C) ha

/-- If `dist (f n) (f (n+1))` is bounded by `(C / 2) / 2^n`, then the distance from
`f n` to the limit of `f` is bounded above by `C / 2^n`. -/
theorem dist_le_of_le_geometric_two_of_tendsto {a : α} (ha : Tendsto f atTop (𝓝 a)) (n : ℕ) :
    dist (f n) a ≤ C / 2 ^ n := by
  convert! dist_le_tsum_of_dist_le_of_tendsto _ hu₂ (summable_geometric_two' C) ha n
  rw [← ((hasSum_geometric_two' C).div_const (2 ^ n)).tsum_eq]
  congr 1 with m
  simp only [add_comm n, pow_add, div_div₀, mul_assoc]

end LeGeometric

/-! ### Summability tests based on comparison with geometric series -/


/-- A series whose terms are bounded by the terms of a converging geometric series converges. -/
theorem summable_one_div_pow_of_le {m : ℝ} {f : ℕ → ℕ} (hm : 1 < m) (fi : ∀ i, i ≤ f i) :
    Summable fun i ↦ 1 / m ^ f i := by
  refine .of_nonneg_of_le (fun a ↦ by positivity) (fun a ↦ ?_)
      (summable_geometric_of_lt_one (one_div_nonneg.mpr (zero_le_one.trans hm.le))
        ((one_div_lt (zero_lt_one.trans hm) zero_lt_one).mpr (one_div_one₀.le.trans_lt hm)))
  rw [div_pow₀, one_pow]
  refine (one_div_le_one_div ?_ ?_).mpr (pow_right_mono₀ hm.le (fi a)) <;>
    exact pow_pos (zero_lt_one.trans hm) _

/-! ### Positive sequences with small sums on countable types -/


/-- For any positive `ε`, define on an encodable type a positive sequence with sum less than `ε` -/
def posSumOfEncodable {ε : ℝ} (hε : 0 < ε) (ι) [Encodable ι] :
    { ε' : ι → ℝ // (∀ i, 0 < ε' i) ∧ ∃ c, HasSum ε' c ∧ c ≤ ε } := by
  let f n := ε / 2 / 2 ^ n
  have hf : HasSum f ε := hasSum_geometric_two' _
  have f0 : ∀ n, 0 < f n := fun n ↦ div_pos (half_pos hε) (pow_pos zero_lt_two _)
  refine ⟨f ∘ Encodable.encode, fun i ↦ f0 _, ?_⟩
  rcases hf.summable.comp_injective (@Encodable.encode_injective ι _) with ⟨c, hg⟩
  refine ⟨c, hg, hasSum_le_inj _ (@Encodable.encode_injective ι _) ?_ ?_ hg hf⟩
  · intro i _
    exact le_of_lt (f0 _)
  · intro n
    exact le_rfl

theorem Set.Countable.exists_pos_hasSum_le {ι : Type*} {s : Set ι} (hs : s.Countable) {ε : ℝ}
    (hε : 0 < ε) : ∃ ε' : ι → ℝ, (∀ i, 0 < ε' i) ∧ ∃ c, HasSum (fun i : s ↦ ε' i) c ∧ c ≤ ε := by
  classical
  have := hs.toEncodable
  rcases posSumOfEncodable hε s with ⟨f, hf0, ⟨c, hfc, hcε⟩⟩
  refine ⟨fun i ↦ if h : i ∈ s then f ⟨i, h⟩ else 1, fun i ↦ ?_, ⟨c, ?_, hcε⟩⟩
  · conv_rhs => simp
    split_ifs
    exacts [hf0 _, zero_lt_one]
  · simpa only [Subtype.coe_prop, dite_eq_left, Subtype.coe_eta]

theorem Set.Countable.exists_pos_forall_sum_le {ι : Type*} {s : Set ι} (hs : s.Countable) {ε : ℝ}
    (hε : 0 < ε) : ∃ ε' : ι → ℝ,
    (∀ i, 0 < ε' i) ∧ ∀ t : Finset ι, ↑t ⊆ s → ∑ i ∈ t, ε' i ≤ ε := by
  classical
  rcases hs.exists_pos_hasSum_le hε with ⟨ε', hpos, c, hε'c, hcε⟩
  refine ⟨ε', hpos, fun t ht ↦ ?_⟩
  rw [← sum_subtype_of_mem _ ht]
  refine (sum_le_hasSum _ ?_ hε'c).trans hcε
  exact fun _ _ ↦ (hpos _).le

namespace NNReal

theorem exists_pos_sum_of_countable {ε : ℝ≥0} (hε : ε ≠ 0) (ι) [Countable ι] :
    ∃ ε' : ι → ℝ≥0, (∀ i, 0 < ε' i) ∧ ∃ c, HasSum ε' c ∧ c < ε := by
  cases nonempty_encodable ι
  obtain ⟨a, a0, aε⟩ := exists_between (pos_iff_ne_zero.2 hε)
  obtain ⟨ε', hε', c, hc, hcε⟩ := posSumOfEncodable a0 ι
  exact
    ⟨fun i ↦ ⟨ε' i, (hε' i).le⟩, fun i ↦ NNReal.coe_lt_coe.1 <| hε' i,
      ⟨c, hasSum_le (fun i ↦ (hε' i).le) hasSum_zero hc⟩, NNReal.hasSum_coe.1 hc,
      aε.trans_le' <| NNReal.coe_le_coe.1 hcε⟩

end NNReal

namespace ENNReal

theorem exists_pos_sum_of_countable {ε : ℝ≥0∞} (hε : ε ≠ 0) (ι) [Countable ι] :
    ∃ ε' : ι → ℝ≥0, (∀ i, 0 < ε' i) ∧ (∑' i, (ε' i : ℝ≥0∞)) < ε := by
  rcases exists_between (pos_iff_ne_zero.2 hε) with ⟨r, h0r, hrε⟩
  rcases lt_iff_exists_coe.1 hrε with ⟨x, rfl, _⟩
  rcases NNReal.exists_pos_sum_of_countable (coe_pos.1 h0r).ne' ι with ⟨ε', hp, c, hc, hcr⟩
  exact ⟨ε', hp, (ENNReal.tsum_coe_eq hc).symm ▸ lt_trans (coe_lt_coe.2 hcr) hrε⟩

theorem exists_pos_sum_of_countable' {ε : ℝ≥0∞} (hε : ε ≠ 0) (ι) [Countable ι] :
    ∃ ε' : ι → ℝ≥0∞, (∀ i, 0 < ε' i) ∧ ∑' i, ε' i < ε :=
  let ⟨δ, δpos, hδ⟩ := exists_pos_sum_of_countable hε ι
  ⟨fun i ↦ δ i, fun i ↦ ENNReal.coe_pos.2 (δpos i), hδ⟩

theorem exists_pos_tsum_mul_lt_of_countable {ε : ℝ≥0∞} (hε : ε ≠ 0) {ι} [Countable ι] (w : ι → ℝ≥0∞)
    (hw : ∀ i, w i ≠ ∞) : ∃ δ : ι → ℝ≥0, (∀ i, 0 < δ i) ∧ (∑' i, (w i * δ i : ℝ≥0∞)) < ε := by
  lift w to ι → ℝ≥0 using hw
  rcases exists_pos_sum_of_countable hε ι with ⟨δ', Hpos, Hsum⟩
  have : ∀ i, 0 < max 1 (w i) := fun i ↦ zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨fun i ↦ δ' i / max 1 (w i), fun i ↦ div_pos (Hpos _) (this i), ?_⟩
  refine lt_of_le_of_lt (ENNReal.tsum_le_tsum fun i ↦ ?_) Hsum
  rw [coe_div (hr := (this i).ne'.isUnit)]
  let b : ℝ≥0 := max 1 (w i)
  have hb : (b : ℝ≥0∞) ≠ 0 := coe_ne_zero.2 (this i).ne'
  have hwb : (w i : ℝ≥0∞) ≤ (b : ℝ≥0∞) := coe_le_coe.2 (le_max_right 1 (w i))
  calc
    _ ≤ (b : ℝ≥0∞) * ((δ' i : ℝ≥0∞) / (b : ℝ≥0∞)) := mul_le_mul_left hwb _
    _ ≤ _ := ENNReal.mul_div_le _

end ENNReal

/-!
### Factorial
-/


theorem factorial_tendsto_atTop : Tendsto Nat.factorial atTop atTop :=
  tendsto_atTop_atTop_of_monotone (fun _ _ ↦ Nat.factorial_le) fun n ↦ ⟨n, n.self_le_factorial⟩

private theorem real_self_pow_ne_zero (n : ℕ) : (n : ℝ) ^ n ≠ 0 := by
  cases n with
  | zero => simp
  | succ n => exact pow_ne_zero _ (Nat.cast_ne_zero.2 n.succ_ne_zero)

theorem tendsto_factorial_div_pow_self_atTop :
    Tendsto (fun n : ℕ ↦ Checked.div (n ! : ℝ) ((n : ℝ) ^ n)
      (by exact (real_self_pow_ne_zero n).isUnit)) atTop (𝓝 0) := by
  -- On the nonzero indices, `n ! / n ^ n ≤ 1 / n`.
  refine (tendsto_comap'_iff (i := (Subtype.val : {n : ℕ // n ≠ 0} → ℕ)) (by
    rw [Subtype.range_coe_subtype]
    exact eventually_ne_atTop 0)).1 ?_
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_const_div_atTop_nhds_zero_nat 1) (fun n ↦ by dsimp; positivity) fun n ↦ ?_
  obtain ⟨n, hn⟩ := n
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have hk : (k + 1)! * (k + 1) ≤ (k + 1) ^ (k + 1) := by
    rw [_root_.pow_succ]
    refine Nat.mul_le_mul_right _ ?_
    rw [← Nat.descFactorial_self, Nat.descFactorial_succ, Nat.add_sub_cancel_left, one_mul]
    exact Nat.descFactorial_le_pow _ _
  dsimp
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
  exact_mod_cast hk

/-!
### Ceil and floor
-/


section

theorem tendsto_nat_floor_atTop {α : Type*}
    [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] [FloorSemiring α] :
    Tendsto (fun x : α ↦ ⌊x⌋₊) atTop atTop :=
  Nat.floor_mono.tendsto_atTop_atTop fun x ↦ ⟨max 0 (x + 1), by simp [Nat.le_floor_iff]⟩

lemma tendsto_nat_ceil_atTop {α : Type*}
    [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] [FloorSemiring α] :
    Tendsto (fun x : α ↦ ⌈x⌉₊) atTop atTop := by
  refine Nat.ceil_mono.tendsto_atTop_atTop (fun x ↦ ⟨x, ?_⟩)
  simp only [Nat.ceil_natCast, le_refl]

lemma tendsto_nat_floor_mul_atTop {α : Type _}
    [Semifield α] [LinearOrder α] [IsStrictOrderedRing α] [FloorSemiring α]
    [Archimedean α] (a : α) (ha : 0 < a) : Tendsto (fun (x : ℕ) => ⌊a * x⌋₊) atTop atTop :=
  Tendsto.comp tendsto_nat_floor_atTop
    <| Tendsto.const_mul_atTop ha tendsto_natCast_atTop_atTop

variable {R : Type*} [TopologicalSpace R] [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [OrderTopology R] [FloorRing R]

/-- The quotient `⌊a * x⌋₊ / x` tends to `a`; it is taken on the nonzero `x`. -/
theorem tendsto_nat_floor_mul_div_atTop {a : R} (ha : 0 ≤ a) :
    Tendsto (fun x : {x : R // x ≠ 0} ↦ Checked.div (⌊a * (x : R)⌋₊ : R) (x : R) x.2.isUnit)
      (comap Subtype.val atTop) (𝓝 a) := by
  have hx : Tendsto (fun x : {x : R // x ≠ 0} ↦ (x : R)) (comap Subtype.val atTop) atTop :=
    tendsto_comap
  have A : Tendsto (fun x : {x : R // x ≠ 0} ↦ a - Checked.inv (x : R) x.2.isUnit)
      (comap Subtype.val atTop) (𝓝 (a - 0)) :=
    tendsto_const_nhds.sub (hx.fun_inv_tendsto_atTop (h0 := fun x : {x : R // x ≠ 0} ↦ x.2.isUnit))
  rw [sub_zero] at A
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' A tendsto_const_nhds
  · filter_upwards [hx.eventually_ge_atTop 1] with x hx1
    rw [le_div_iff₀ (zero_lt_one.trans_le hx1), _root_.sub_mul, inv_mul_cancel₀]
    have := Nat.lt_floor_add_one (a * x)
    linarith
  · filter_upwards [hx.eventually_ge_atTop 1] with x hx1
    have hx0 : (0 : R) < x := zero_lt_one.trans_le hx1
    rw [div_le_iff₀ hx0]
    simp [Nat.floor_le (mul_nonneg ha hx0.le)]

/-- The quotient `⌊x⌋₊ / x` tends to `1`; it is taken on the nonzero `x`. -/
theorem tendsto_nat_floor_div_atTop :
    Tendsto (fun x : {x : R // x ≠ 0} ↦ Checked.div (⌊(x : R)⌋₊ : R) (x : R) x.2.isUnit)
      (comap Subtype.val atTop) (𝓝 1) := by
  simpa using tendsto_nat_floor_mul_div_atTop (zero_le_one' R)

/-- The quotient `⌈a * x⌉₊ / x` tends to `a`; it is taken on the nonzero `x`. -/
theorem tendsto_nat_ceil_mul_div_atTop {a : R} (ha : 0 ≤ a) :
    Tendsto (fun x : {x : R // x ≠ 0} ↦ Checked.div (⌈a * (x : R)⌉₊ : R) (x : R) x.2.isUnit)
      (comap Subtype.val atTop) (𝓝 a) := by
  have hx : Tendsto (fun x : {x : R // x ≠ 0} ↦ (x : R)) (comap Subtype.val atTop) atTop :=
    tendsto_comap
  have A : Tendsto (fun x : {x : R // x ≠ 0} ↦ a + Checked.inv (x : R) x.2.isUnit)
      (comap Subtype.val atTop) (𝓝 (a + 0)) :=
    tendsto_const_nhds.add (hx.fun_inv_tendsto_atTop (h0 := fun x : {x : R // x ≠ 0} ↦ x.2.isUnit))
  rw [add_zero] at A
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds A
  · filter_upwards [hx.eventually_ge_atTop 1] with x hx1
    rw [le_div_iff₀ (zero_lt_one.trans_le hx1)]
    exact Nat.le_ceil _
  · filter_upwards [hx.eventually_ge_atTop 1] with x hx1
    have hx0 : (0 : R) < x := zero_lt_one.trans_le hx1
    rw [div_le_iff₀ hx0, add_mul, inv_mul_cancel₀]
    exact (Nat.ceil_lt_add_one (mul_nonneg ha hx0.le)).le

/-- The quotient `⌈x⌉₊ / x` tends to `1`; it is taken on the nonzero `x`. -/
theorem tendsto_nat_ceil_div_atTop :
    Tendsto (fun x : {x : R // x ≠ 0} ↦ Checked.div (⌈(x : R)⌉₊ : R) (x : R) x.2.isUnit)
      (comap Subtype.val atTop) (𝓝 1) := by
  simpa using tendsto_nat_ceil_mul_div_atTop (zero_le_one' R)

lemma Nat.tendsto_div_const_atTop {n : ℕ} (hn : n ≠ 0) :
    Tendsto (fun a => Nat.euclideanDiv a n hn) atTop atTop := by
  rw [Tendsto, map_div_atTop_eq_nat n hn.bot_lt]

end
