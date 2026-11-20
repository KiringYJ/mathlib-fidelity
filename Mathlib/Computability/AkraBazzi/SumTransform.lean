/-
Copyright (c) 2023 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Computability.AkraBazzi.GrowsPolynomially
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

import Mathlib.Analysis.SpecialFunctions.Log.InvLog
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Tactic.Positivity

/-!
# Akra-Bazzi theorem: the sum transform

We develop further preliminaries required for the theorem, up to the sum transform.

## Main definitions and results

* `AkraBazziRecurrence T g a b r`: the predicate stating that `T : ℕ → ℝ` satisfies an Akra-Bazzi
  recurrence with parameters `g`, `a`, `b` and `r` as above, together with basic bounds on `r i n`
  and positivity of `T`.
* `AkraBazziRecurrence.smoothingFn`: the smoothing function $\varepsilon(x) = 1 / \log x$ used in
  the inductive estimates, along with monotonicity, differentiability, and asymptotic properties.
* `AkraBazziRecurrence.p`: the unique Akra–Bazzi exponent characterized by $\sum_i a_i\,(b_i)^p = 1$
  and supporting analytical lemmas such as continuity and injectivity of the defining sum.
* `AkraBazziRecurrence.sumTransform`: the transformation that turns a function `g` into
  `n^p * ∑ u ∈ Finset.Ico n₀ n, g u / u^(p+1)` and its eventual comparison with multiples of `g n`.
* `AkraBazziRecurrence.asympBound`: the asymptotic bound satisfied by an Akra-Bazzi recurrence,
  namely `n^p (1 + ∑ g(u) / u^(p+1))`, together with positivity statements along the branches
  `r i n`.


## References

* Mohamad Akra and Louay Bazzi, On the solution of linear recurrence equations
* Tom Leighton, Notes on better master theorems for divide-and-conquer recurrences
* Manuel Eberl, Asymptotic reasoning in a proof assistant

-/

@[expose] public section

open Finset Real Filter Asymptotics
open scoped Topology

/-!
### Definition of Akra-Bazzi recurrences

This section defines the predicate `AkraBazziRecurrence T g a b r` which states that `T`
satisfies the recurrence relation
`T(n) = ∑_{i=0}^{k-1} a_i T(r_i(n)) + g(n)`
with appropriate conditions on the various parameters.
-/

namespace AkraBazziRecurrence

/-- Natural indices at which the reciprocal logarithmic error scale is defined. -/
abbrev LogNat := {n : ℕ // IsUnit (log (n : ℝ))}

/-- The perturbation scale of an Akra–Bazzi recurrence. -/
noncomputable def logError (n : LogNat) : ℝ :=
  Checked.div (n.val : ℝ) (log (n.val : ℝ) ^ 2) (n.2.pow 2)

lemma logError_nonneg (n : LogNat) : 0 ≤ logError n :=
  div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)

lemma eventually_logNat : ∀ᶠ n : ℕ in atTop, IsUnit (log (n : ℝ)) :=
  (eventually_gt_atTop 1).mono fun n hn ↦ (log_pos (by exact_mod_cast hn)).ne'.isUnit

end AkraBazziRecurrence

/-- An Akra-Bazzi recurrence is a function that satisfies the recurrence
`T n = (∑ i, a i * T (r i n)) + g n`. -/
structure AkraBazziRecurrence {α : Type*} [Fintype α] [Nonempty α]
    (T : ℕ → ℝ) (g : ℝ → ℝ) (a : α → ℝ) (b : α → ℝ) (r : α → ℕ → ℕ) where
  /-- Point below which the recurrence is in the base case -/
  n₀ : ℕ
  /-- `n₀` is always positive -/
  n₀_gt_zero : 0 < n₀
  /-- The coefficients `a i` are positive. -/
  a_pos : ∀ i, 0 < a i
  /-- The coefficients `b i` are positive. -/
  b_pos : ∀ i, 0 < b i
  /-- The coefficients `b i` are less than 1. -/
  b_lt_one : ∀ i, b i < 1
  /-- `g` is nonnegative -/
  g_nonneg : ∀ x ≥ 0, 0 ≤ g x
  /-- `g` grows polynomially -/
  g_grows_poly : AkraBazziRecurrence.GrowsPolynomially g
  /-- The actual recurrence -/
  h_rec (n : ℕ) (hn₀ : n₀ ≤ n) : T n = (∑ i, a i * T (r i n)) + g n
  /-- Base case: `T(n) > 0` whenever `n < n₀` -/
  T_gt_zero' (n : ℕ) (hn : n < n₀) : 0 < T n
  /-- The functions `r i` always reduce `n`. -/
  r_lt_n : ∀ i n, n₀ ≤ n → r i n < n
  /-- The functions `r i` approximate the values `b i * n`. -/
  dist_r_b : ∀ i, (fun n : AkraBazziRecurrence.LogNat ↦ (r i n.val : ℝ) - b i * n.val)
    =o[comap Subtype.val atTop] AkraBazziRecurrence.logError

namespace AkraBazziRecurrence

section min_max

variable {α : Type*} [Finite α] [Nonempty α]

/-- Smallest `b i` -/
noncomputable def min_bi (b : α → ℝ) : α :=
  Classical.choose <| Finite.exists_min b

/-- Largest `b i` -/
noncomputable def max_bi (b : α → ℝ) : α :=
  Classical.choose <| Finite.exists_max b

@[aesop safe apply]
lemma min_bi_le {b : α → ℝ} (i : α) : b (min_bi b) ≤ b i :=
  Classical.choose_spec (Finite.exists_min b) i

@[aesop safe apply]
lemma max_bi_le {b : α → ℝ} (i : α) : b i ≤ b (max_bi b) :=
  Classical.choose_spec (Finite.exists_max b) i

end min_max

lemma isLittleO_self_div_log_id :
    logError =o[comap Subtype.val atTop] fun n : LogNat ↦ (n.val : ℝ) := by
  have hn : Tendsto (fun n : LogNat ↦ (n.val : ℝ)) (comap Subtype.val atTop) atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_comap
  have ht := (tendsto_pow_atTop (by decide : 2 ≠ 0)).comp (tendsto_log_atTop.comp hn)
  have hi := ht.fun_inv_tendsto_atTop (h0 := fun n : LogNat ↦ n.2.pow 2)
  unfold logError
  simpa only [div_eq_mul_inv₀, mul_one] using!
    (isBigO_refl (fun n : LogNat ↦ (n.val : ℝ)) _).mul_isLittleO ((isLittleO_one_iff ℝ).mpr hi)

variable {α : Type*} [Fintype α] {T : ℕ → ℝ} {g : ℝ → ℝ} {a b : α → ℝ} {r : α → ℕ → ℕ}
variable [Nonempty α] (R : AkraBazziRecurrence T g a b r)
section
include R

lemma dist_r_b' : ∀ᶠ n : LogNat in comap Subtype.val atTop, ∀ i,
    ‖(r i n.val : ℝ) - b i * n.val‖ ≤ logError n := by
  rw [Filter.eventually_all]
  intro i
  exact (R.dist_r_b i).eventuallyLE.mono fun n h ↦ by
    simpa only [Real.norm_of_nonneg (logError_nonneg n)] using h

lemma eventually_b_le_r : ∀ᶠ n : LogNat in comap Subtype.val atTop, ∀ i,
    b i * n.val - logError n ≤ r i n.val := by
  filter_upwards [R.dist_r_b'] with n hn i
  have hb := le_abs_self (b i * n.val - r i n.val)
  rw [abs_sub_comm, ← Real.norm_eq_abs] at hb
  linarith [hn i]

lemma eventually_r_le_b : ∀ᶠ n : LogNat in comap Subtype.val atTop, ∀ i,
    r i n.val ≤ b i * n.val + logError n := by
  filter_upwards [R.dist_r_b'] with n hn i
  linarith [Real.le_norm_self ((r i n.val : ℝ) - b i * n.val), hn i]

lemma eventually_r_lt_n : ∀ᶠ (n : ℕ) in atTop, ∀ i, r i n < n := by
  filter_upwards [eventually_ge_atTop R.n₀] with n hn i using R.r_lt_n i n hn

lemma eventually_bi_mul_le_r : ∀ᶠ (n : ℕ) in atTop, ∀ i, (b (min_bi b) / 2) * n ≤ r i n := by
  have gt_zero : 0 < b (min_bi b) := R.b_pos (min_bi b)
  have hlo := isLittleO_self_div_log_id
  rw [Asymptotics.isLittleO_iff] at hlo
  have hlo' := hlo (by positivity : 0 < b (min_bi b) / 2)
  apply (eventually_comap_val_iff eventually_logNat).1
  filter_upwards [hlo', R.eventually_b_le_r] with n hn hn' i
  simp only [Real.norm_of_nonneg (by positivity : 0 ≤ (n.val : ℝ))] at hn
  calc b (min_bi b) / 2 * n.val
    _ = b (min_bi b) * n.val - b (min_bi b) / 2 * n.val := by ring
    _ ≤ b (min_bi b) * n.val - ‖logError n‖ := by gcongr
    _ ≤ b i * n.val - ‖logError n‖ := by gcongr; aesop
    _ = b i * n.val - logError n := by
      rw [Real.norm_of_nonneg (logError_nonneg n)]
    _ ≤ r i n.val := hn' i

lemma bi_min_div_two_lt_one : b (min_bi b) / 2 < 1 := by
  have gt_zero : 0 < b (min_bi b) := R.b_pos (min_bi b)
  calc b (min_bi b) / 2
    _ < b (min_bi b) := by aesop (add safe apply div_two_lt_of_pos)
    _ < 1 := R.b_lt_one _

lemma bi_min_div_two_pos : 0 < b (min_bi b) / 2 := div_pos (R.b_pos _) (by simp)

lemma exists_eventually_const_mul_le_r :
    ∃ c ∈ Set.Ioo (0 : ℝ) 1, ∀ᶠ (n : ℕ) in atTop, ∀ i, c * n ≤ r i n := by
  have gt_zero : 0 < b (min_bi b) := R.b_pos (min_bi b)
  exact ⟨b (min_bi b) / 2, ⟨⟨by positivity, R.bi_min_div_two_lt_one⟩, R.eventually_bi_mul_le_r⟩⟩

lemma eventually_r_ge (C : ℝ) : ∀ᶠ (n : ℕ) in atTop, ∀ i, C ≤ r i n := by
  obtain ⟨c, hc_mem, hc⟩ := R.exists_eventually_const_mul_le_r
  have h₁ := hc_mem.1
  filter_upwards [eventually_ge_atTop ⌈C / c⌉₊, hc] with n hn₁ hn₂ i
  calc C
    _ = c * (C / c) := by
      rw [div_eq_inv_mul₀, ← mul_assoc, mul_inv_cancel₀, one_mul]
    _ ≤ c * ⌈C / c⌉₊ := by gcongr; simp [Nat.le_ceil]
    _ ≤ c * n := by gcongr
    _ ≤ r i n := hn₂ i

lemma tendsto_atTop_r (i : α) : Tendsto (r i) atTop atTop := by
  rw [tendsto_atTop]
  intro b
  have := R.eventually_r_ge b
  rw [Filter.eventually_all] at this
  exact_mod_cast this i

lemma tendsto_atTop_r_real (i : α) : Tendsto (fun n => (r i n : ℝ)) atTop atTop :=
  Tendsto.comp tendsto_natCast_atTop_atTop (R.tendsto_atTop_r i)

lemma exists_eventually_r_le_const_mul :
    ∃ c ∈ Set.Ioo (0 : ℝ) 1, ∀ᶠ (n : ℕ) in atTop, ∀ i, r i n ≤ c * n := by
  let c := b (max_bi b) + (1 - b (max_bi b)) / 2
  have h_max_bi_pos : 0 < b (max_bi b) := R.b_pos _
  have h_max_bi_lt_one : 0 < 1 - b (max_bi b) := by
    have : b (max_bi b) < 1 := R.b_lt_one _
    linarith
  have hc_pos : 0 < c := by positivity
  have h₁ : 0 < (1 - b (max_bi b)) / 2 := by positivity
  have hc_lt_one : c < 1 :=
    calc b (max_bi b) + (1 - b (max_bi b)) / 2
      _ = b (max_bi b) * (1 / 2) + 1 / 2 := by ring
      _ < 1 * (1 / 2) + 1 / 2 := by gcongr; exact R.b_lt_one _
      _ = 1 := by norm_num
  refine ⟨c, ⟨hc_pos, hc_lt_one⟩, ?_⟩
  have hlo := isLittleO_self_div_log_id
  rw [Asymptotics.isLittleO_iff] at hlo
  have hlo' := hlo h₁
  apply (eventually_comap_val_iff eventually_logNat).1
  filter_upwards [hlo', R.eventually_r_le_b] with n hn hn'
  intro i
  simp only [Real.norm_of_nonneg (logError_nonneg n),
    Real.norm_of_nonneg (Nat.cast_nonneg n.val)] at hn
  calc r i n.val ≤ b i * n.val + logError n := by exact hn' i
             _ ≤ b i * n.val + (1 - b (max_bi b)) / 2 * n.val := by gcongr
             _ = (b i + (1 - b (max_bi b)) / 2) * n.val := by ring
             _ ≤ (b (max_bi b) + (1 - b (max_bi b)) / 2) * n.val := by gcongr; exact max_bi_le _

lemma eventually_r_pos : ∀ᶠ (n : ℕ) in atTop, ∀ i, 0 < r i n := by
  rw [Filter.eventually_all]
  exact fun i => (R.tendsto_atTop_r i).eventually_gt_atTop 0

lemma eventually_log_b_mul_pos : ∀ᶠ (n : ℕ) in atTop, ∀ i, 0 < log (b i * n) := by
  rw [Filter.eventually_all]
  intro i
  have h : Tendsto (fun (n : ℕ) => log (b i * n)) atTop atTop :=
    Tendsto.comp tendsto_log_atTop
      <| Tendsto.const_mul_atTop (b_pos R i) tendsto_natCast_atTop_atTop
  exact h.eventually_gt_atTop 0

@[aesop safe apply] lemma T_pos (n : ℕ) : 0 < T n := by
  induction n using Nat.strongRecOn with
  | ind n h_ind =>
    cases lt_or_ge n R.n₀ with
    | inl hn => exact R.T_gt_zero' n hn -- n < R.n₀
    | inr hn => -- R.n₀ ≤ n
      rw [R.h_rec n hn]
      have := R.g_nonneg
      refine add_pos_of_pos_of_nonneg (Finset.sum_pos ?sum_elems univ_nonempty) (by simp_all)
      exact fun i _ => mul_pos (R.a_pos i) <| h_ind _ (R.r_lt_n i _ hn)

@[aesop safe apply]
lemma T_nonneg (n : ℕ) : 0 ≤ T n := le_of_lt <| R.T_pos n

end

/-!
### Smoothing function

We define `ε` as the "smoothing function" `fun n => 1 / log n`, which will be used in the form of a
factor of `1 ± ε n` needed to make the induction step go through.

This is its own definition to make it easier to switch to a different smoothing function.
For example, choosing `1 / log n ^ δ` for a suitable choice of `δ` leads to a slightly tighter
theorem at the price of a more complicated proof.

This part of the file then proves several properties of this function that will be needed later in
the proof.
-/

/-- Real arguments on which the reciprocal logarithm is defined. -/
abbrev SmoothingDomain := {x : ℝ // IsUnit (log x)}

/-- The reciprocal logarithm used to smooth the inductive estimates. -/
noncomputable def smoothingFn (x : SmoothingDomain) : ℝ := Checked.inv (log x.val) x.2

local notation "ε" => smoothingFn
local notation "L" => (comap (Subtype.val : SmoothingDomain → ℝ) atTop)

lemma isOpen_smoothingDomain : IsOpen {x : ℝ | IsUnit (log x)} :=
  isOpen_iff_mem_nhds.mpr fun _ hx ↦
    (continuousAt_log (log_ne_zero.mp hx.ne_zero).1).eventually (Units.isOpen.mem_nhds hx)

lemma one_add_smoothingFn_le_two {x : SmoothingDomain} (hx : exp 1 ≤ x.val) : 1 + ε x ≤ 2 := by
  have h : 1 ≤ log x.val := by simpa using log_le_log (exp_pos 1) hx
  simpa [smoothingFn, ← one_add_one_eq_two] using
    add_le_add_left ((inv_le_one₀ (zero_lt_one.trans_le h)).mpr h) 1

lemma tendsto_smoothingFn_zero : Tendsto ε L (𝓝 0) :=
  (tendsto_log_atTop.comp tendsto_comap).fun_inv_tendsto_atTop (h0 := fun x ↦ x.2)

lemma isLittleO_smoothingFn_one : ε =o[L] (fun _ => (1 : ℝ)) :=
  (isLittleO_one_iff ℝ).mpr tendsto_smoothingFn_zero

lemma isEquivalent_one_add_smoothingFn_one : (fun x => 1 + ε x) ~[L] (fun _ => (1 : ℝ)) :=
  IsEquivalent.add_isLittleO IsEquivalent.refl isLittleO_smoothingFn_one

lemma isEquivalent_one_sub_smoothingFn_one : (fun x => 1 - ε x) ~[L] (fun _ => (1 : ℝ)) :=
  IsEquivalent.sub_isLittleO IsEquivalent.refl isLittleO_smoothingFn_one

private lemma growsPolynomially_of_tendsto_one {D : Type*} {coord : D → ℝ} {f : D → ℝ}
    (h : Tendsto f (comap coord atTop) (𝓝 1)) : GrowsPolynomially f coord := by
  have H := h.eventually (Ioo_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1) (by norm_num : (1 : ℝ) < 2))
  rw [eventually_comap] at H
  intro b hb
  refine ⟨1 / 4, by norm_num, 4, by norm_num, ?_⟩
  filter_upwards [tendsto_comap.eventually H, tendsto_comap.eventually
    ((tendsto_id.const_mul_atTop hb.1).eventually_forall_ge_atTop H)] with x hx hu
  intro u hU
  have h₁ := hx x rfl
  have h₂ := hu (coord u) hU.1 u rfl
  constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2]

lemma growsPolynomially_one_sub_smoothingFn :
    GrowsPolynomially (fun x => 1 - ε x) Subtype.val :=
  growsPolynomially_of_tendsto_one isEquivalent_one_sub_smoothingFn_one.tendsto_const

lemma growsPolynomially_one_add_smoothingFn :
    GrowsPolynomially (fun x => 1 + ε x) Subtype.val :=
  growsPolynomially_of_tendsto_one isEquivalent_one_add_smoothingFn_one.tendsto_const

lemma eventually_one_sub_smoothingFn_gt_const_real (c : ℝ) (hc : c < 1) :
    ∀ᶠ x in L, c < 1 - ε x :=
  isEquivalent_one_sub_smoothingFn_one.tendsto_const.eventually_const_lt hc

lemma eventually_logDomain {ι : Type*} {l : Filter ι} {v : ι → ℝ} {P : SmoothingDomain → Prop}
    (hv : Tendsto v l atTop) (h : ∀ᶠ x in L, P x) :
    ∀ᶠ i in l, ∀ hi : IsUnit (log (v i)), P ⟨v i, hi⟩ :=
  (hv.eventually (eventually_comap.mp h)).mono fun _ hi hu ↦ hi ⟨_, hu⟩ rfl

lemma eventually_one_sub_smoothingFn_gt_const (c : ℝ) (hc : c < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ hn, c < 1 - ε ⟨(n : ℝ), hn⟩ :=
  eventually_logDomain tendsto_natCast_atTop_atTop
    (eventually_one_sub_smoothingFn_gt_const_real c hc)

lemma eventually_one_sub_smoothingFn_pos_real : ∀ᶠ x in L, 0 < 1 - ε x :=
  eventually_one_sub_smoothingFn_gt_const_real 0 zero_lt_one

lemma eventually_one_sub_smoothingFn_pos :
    ∀ᶠ n : ℕ in atTop, ∀ hn, 0 < 1 - ε ⟨(n : ℝ), hn⟩ :=
  eventually_one_sub_smoothingFn_gt_const 0 zero_lt_one

lemma eventually_one_sub_smoothingFn_nonneg :
    ∀ᶠ n : ℕ in atTop, ∀ hn, 0 ≤ 1 - ε ⟨(n : ℝ), hn⟩ :=
  eventually_one_sub_smoothingFn_pos.mono fun _ hi hn ↦ (hi hn).le

include R in
lemma eventually_one_sub_smoothingFn_r_pos :
    ∀ᶠ n : ℕ in atTop, ∀ i, ∀ hn, 0 < 1 - ε ⟨(r i n : ℝ), hn⟩ := by
  rw [Filter.eventually_all]
  exact fun i ↦ (R.tendsto_atTop_r i).eventually eventually_one_sub_smoothingFn_pos

lemma hasDerivAt_smoothingFn (x : SmoothingDomain) :
    HasDerivAt ε (-(Checked.inv x.val (log_ne_zero.mp x.2.ne_zero).1.isUnit) / log x.val ^ 2)
      x Subtype.val := hasDerivAt_inv_log x

@[aesop safe apply]
lemma differentiableAt_smoothingFn (x : SmoothingDomain) : DifferentiableAt ℝ ε x Subtype.val :=
  (hasDerivAt_smoothingFn x).differentiableAt

@[aesop safe apply]
lemma differentiableAt_one_sub_smoothingFn (x : SmoothingDomain) :
    DifferentiableAt ℝ (fun z => 1 - ε z) x Subtype.val :=
  ((hasDerivAt_smoothingFn x).hasFDerivAt.const_sub 1).differentiableAt

lemma differentiableOn_one_sub_smoothingFn :
    DifferentiableOn ℝ (fun z => 1 - ε z) Set.univ Subtype.val :=
  fun x _ ↦
    ((hasDerivAt_smoothingFn x).hasFDerivAt.const_sub 1).hasFDerivWithinAt.differentiableWithinAt

@[aesop safe apply]
lemma differentiableAt_one_add_smoothingFn (x : SmoothingDomain) :
    DifferentiableAt ℝ (fun z => 1 + ε z) x Subtype.val :=
  ((hasDerivAt_smoothingFn x).hasFDerivAt.const_add 1).differentiableAt

lemma differentiableOn_one_add_smoothingFn :
    DifferentiableOn ℝ (fun z => 1 + ε z) Set.univ Subtype.val :=
  fun x _ ↦
    ((hasDerivAt_smoothingFn x).hasFDerivAt.const_add 1).hasFDerivWithinAt.differentiableWithinAt

lemma deriv_smoothingFn (x : SmoothingDomain) :
    deriv ε x Subtype.val =
      -(Checked.inv x.val (log_ne_zero.mp x.2.ne_zero).1.isUnit) / log x.val ^ 2 :=
  deriv_inv_log_apply x

lemma isLittleO_deriv_smoothingFn :
    (fun x ↦ deriv ε x Subtype.val) =o[L]
      fun x : SmoothingDomain ↦ Checked.inv x.val (log_ne_zero.mp x.2.ne_zero).1.isUnit := by
  have h : (fun x ↦ ε x ^ 2) =o[L] (fun _ ↦ (1 : ℝ)) :=
    (isLittleO_one_iff ℝ).mpr (by simpa using tendsto_smoothingFn_zero.pow 2)
  have H := (isBigO_refl (fun x : SmoothingDomain ↦
    Checked.inv x.val (log_ne_zero.mp x.2.ne_zero).1.isUnit) L).mul_isLittleO h
  simpa only [deriv_smoothingFn, div_eq_mul_inv₀, inv_pow₀, neg_mul, smoothingFn, mul_one] using
    H.neg_left

lemma eventually_deriv_one_sub_smoothingFn :
    (fun x ↦ deriv (fun z => 1 - ε z) x Subtype.val) =ᶠ[L] fun x ↦
      Checked.inv x.val (log_ne_zero.mp x.2.ne_zero).1.isUnit / (log x.val ^ 2) :=
  Eventually.of_forall fun x ↦ by
    simpa [neg_div₀] using
      (((hasDerivAt_smoothingFn x).hasFDerivAt.const_sub 1).hasDerivAt.deriv
        isOpen_smoothingDomain.isOpenEmbedding_subtypeVal)

lemma eventually_deriv_one_add_smoothingFn :
    (fun x ↦ deriv (fun z => 1 + ε z) x Subtype.val) =ᶠ[L] fun x ↦
      -(Checked.inv x.val (log_ne_zero.mp x.2.ne_zero).1.isUnit) / (log x.val ^ 2) :=
  Eventually.of_forall fun x ↦ by
    simpa using (((hasDerivAt_smoothingFn x).hasFDerivAt.const_add 1).hasDerivAt.deriv
      isOpen_smoothingDomain.isOpenEmbedding_subtypeVal)

lemma isLittleO_deriv_one_sub_smoothingFn :
    (fun x ↦ deriv (fun z => 1 - ε z) x Subtype.val) =o[L]
      fun x : SmoothingDomain ↦ Checked.inv x.val (log_ne_zero.mp x.2.ne_zero).1.isUnit := by
  apply isLittleO_deriv_smoothingFn.neg_left.congr' _ (EventuallyEq.refl _ _)
  exact eventually_deriv_one_sub_smoothingFn.symm.mono fun x hx ↦ by
    simpa [deriv_smoothingFn, neg_div₀] using hx

lemma isLittleO_deriv_one_add_smoothingFn :
    (fun x ↦ deriv (fun z => 1 + ε z) x Subtype.val) =o[L]
      fun x : SmoothingDomain ↦ Checked.inv x.val (log_ne_zero.mp x.2.ne_zero).1.isUnit := by
  apply isLittleO_deriv_smoothingFn.congr' _ (EventuallyEq.refl _ _)
  exact eventually_deriv_one_add_smoothingFn.symm.mono fun x hx ↦ by
    simpa [deriv_smoothingFn] using hx

lemma eventually_one_add_smoothingFn_pos :
    ∀ᶠ n : ℕ in atTop, ∀ hn, 0 < 1 + ε ⟨(n : ℝ), hn⟩ :=
  eventually_logDomain tendsto_natCast_atTop_atTop
    (isEquivalent_one_add_smoothingFn_one.tendsto_const.eventually_const_lt zero_lt_one)

include R in
lemma eventually_one_add_smoothingFn_r_pos :
    ∀ᶠ n : ℕ in atTop, ∀ i, ∀ hn, 0 < 1 + ε ⟨(r i n : ℝ), hn⟩ := by
  rw [Filter.eventually_all]
  exact fun i ↦ (R.tendsto_atTop_r i).eventually eventually_one_add_smoothingFn_pos

lemma eventually_one_add_smoothingFn_nonneg :
    ∀ᶠ n : ℕ in atTop, ∀ hn, 0 ≤ 1 + ε ⟨(n : ℝ), hn⟩ :=
  eventually_one_add_smoothingFn_pos.mono fun _ hi hn ↦ (hi hn).le

lemma strictAntiOn_smoothingFn : StrictAntiOn ε (Subtype.val ⁻¹' Set.Ioi 1) := by
  intro x hx y hy hxy
  exact inv_lt_inv₀ (log_pos hy) (log_pos hx) |>.mpr (log_lt_log (zero_lt_one.trans hx) hxy)

lemma strictMonoOn_one_sub_smoothingFn :
    StrictMonoOn (fun x => 1 - ε x) (Subtype.val ⁻¹' Set.Ioi 1) := by
  simpa only [sub_eq_add_neg] using strictAntiOn_smoothingFn.neg.const_add 1

lemma strictAntiOn_one_add_smoothingFn :
    StrictAntiOn (fun x => 1 + ε x) (Subtype.val ⁻¹' Set.Ioi 1) :=
  strictAntiOn_smoothingFn.const_add 1

section
include R

/-- Indices where the smoothing factor at both the parent and the scaled argument is defined. -/
abbrev SmoothingPair (d : ℝ) := {n : ℕ // IsUnit (log (n : ℝ)) ∧ IsUnit (log (d * n))}

lemma isEquivalent_smoothingFn_sub_self (i : α) :
    (fun n : SmoothingPair (b i) ↦ ε ⟨b i * n.val, n.2.2⟩ - ε ⟨n.val, n.2.1⟩)
      ~[comap Subtype.val atTop] fun n ↦ Checked.div (-log (b i)) (log (n.val : ℝ) ^ 2)
        (n.2.1.pow 2) := by
  let D := SmoothingPair (b i)
  let l := comap (Subtype.val : D → ℕ) atTop
  have hcast : Tendsto (fun n : D ↦ (n.val : ℝ)) l atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_comap
  have hlog (n : D) : log (b i * n.val) = log (b i) + log n.val :=
    log_mul (R.b_pos i).ne' (log_ne_zero.mp n.2.1.ne_zero).1
  have hE : (fun n : D ↦ log (b i * n.val)) ~[l] fun n ↦ log n.val := by
    simpa only [hlog, add_comm (log (b i)), Function.comp_def] using!
      (IsEquivalent.add_isLittleO (IsEquivalent.refl (u := fun n : D ↦ log n.val))
        ((isLittleO_const_log_atTop (c := log (b i))).comp_tendsto hcast))
  have heq (n : D) : ε ⟨b i * n.val, n.2.2⟩ - ε ⟨n.val, n.2.1⟩ =
      Checked.div (-log (b i)) (log (b i * n.val) * log n.val) (n.2.2.mul n.2.1) := by
    rw [smoothingFn, smoothingFn, inv_sub_inv]
    congr 1
    change log (n.val : ℝ) - log (b i * n.val) = -log (b i)
    linarith [hlog n]
  simp only [heq, pow_two]
  exact IsEquivalent.refl.div (hv := fun n : D ↦ n.2.2.mul n.2.1)
    (hw := fun n : D ↦ n.2.1.mul n.2.1) (hE.mul IsEquivalent.refl)

lemma isTheta_smoothingFn_sub_self (i : α) :
    (fun n : SmoothingPair (b i) ↦ ε ⟨b i * n.val, n.2.2⟩ - ε ⟨n.val, n.2.1⟩)
      =Θ[comap Subtype.val atTop] fun n ↦ Checked.inv (log (n.val : ℝ) ^ 2)
        (n.2.1.pow 2) := by
  have hb : -log (b i) ≠ 0 := neg_ne_zero.mpr
    (log_ne_zero_of_pos_of_ne_one (R.b_pos i) (R.b_lt_one i).ne)
  exact (R.isEquivalent_smoothingFn_sub_self i).isTheta.trans <|
    (isTheta_refl _ _).const_mul_left hb

/-!
### Akra-Bazzi exponent `p`

Every Akra-Bazzi recurrence has an associated exponent, denoted by `p : ℝ`, such that
`∑ a_i b_i^p = 1`. This section shows the existence and uniqueness of this exponent `p` for any
`R : AkraBazziRecurrence`. These results are used in the next section to define the asymptotic
bound expression. -/

@[continuity, fun_prop]
lemma continuous_sumCoeffsExp : Continuous (fun (p : ℝ) => ∑ i, a i * (b i) ^ p) := by
  refine continuous_finsetSum Finset.univ fun i _ => Continuous.mul (by fun_prop) ?_
  exact Continuous.rpow continuous_const continuous_id (fun x => Or.inl (ne_of_gt (R.b_pos i)))

lemma strictAnti_sumCoeffsExp : StrictAnti (fun (p : ℝ) => ∑ i, a i * (b i) ^ p) := by
  rw [← Finset.sum_fn]
  refine Finset.sum_induction_nonempty _ _ (fun _ _ => StrictAnti.add) univ_nonempty ?terms
  refine fun i _ => StrictAnti.const_mul ?_ (R.a_pos i)
  exact Real.strictAnti_rpow_of_base_lt_one (R.b_pos i) (R.b_lt_one i)

lemma tendsto_zero_sumCoeffsExp : Tendsto (fun (p : ℝ) => ∑ i, a i * (b i) ^ p) atTop (𝓝 0) := by
  have h₁ : Finset.univ.sum (fun _ : α => (0 : ℝ)) = 0 := by simp
  rw [← h₁]
  refine tendsto_finsetSum (univ : Finset α) (fun i _ => ?_)
  rw [← mul_zero (a i)]
  refine Tendsto.mul (by simp) <| tendsto_rpow_atTop_of_base_lt_one _ ?_ (R.b_lt_one i)
  have := R.b_pos i
  linarith

lemma tendsto_atTop_sumCoeffsExp : Tendsto (fun (p : ℝ) => ∑ i, a i * (b i) ^ p) atBot atTop := by
  have h₁ : Tendsto (fun p : ℝ => (a (max_bi b) : ℝ) * b (max_bi b) ^ p) atBot atTop :=
    Tendsto.const_mul_atTop (R.a_pos (max_bi b)) <| tendsto_rpow_atBot_of_base_lt_one _
      (by have := R.b_pos (max_bi b); linarith) (R.b_lt_one _)
  refine tendsto_atTop_mono (fun p => ?_) h₁
  refine Finset.single_le_sum (f := fun i => (a i : ℝ) * b i ^ p) (fun i _ => ?_) (mem_univ _)
  positivity [R.a_pos i, R.b_pos i]

lemma one_mem_range_sumCoeffsExp : 1 ∈ Set.range (fun (p : ℝ) => ∑ i, a i * (b i) ^ p) := by
  refine mem_range_of_exists_le_of_exists_ge R.continuous_sumCoeffsExp ?le_one ?ge_one
  case le_one =>
    exact R.tendsto_zero_sumCoeffsExp.eventually_le_const zero_lt_one |>.exists
  case ge_one =>
    exact R.tendsto_atTop_sumCoeffsExp.eventually_ge_atTop _ |>.exists

/-- The function x ↦ ∑ a_i b_i^x is injective. This implies the uniqueness of `p`. -/
lemma injective_sumCoeffsExp : Function.Injective (fun (p : ℝ) => ∑ i, a i * (b i) ^ p) :=
    R.strictAnti_sumCoeffsExp.injective

end

variable (a b) in
/-- The exponent `p` associated with a particular Akra-Bazzi recurrence. -/
noncomputable irreducible_def p : ℝ := Function.invFun (fun (p : ℝ) => ∑ i, a i * (b i) ^ p) 1

include R in
-- Cannot be @[simp] because `T`, `g`, `r`, and `R` cannot be inferred by `simp`.
lemma sumCoeffsExp_p_eq_one : ∑ i, a i * (b i) ^ p a b = 1 := by
  simp only [p]
  exact Function.invFun_eq (by rw [← Set.mem_range]; exact R.one_mem_range_sumCoeffsExp)

/-!
### The sum transform

This section defines the "sum transform" of a function `g` as
`n ^ p * ∑ u ∈ Finset.Ico n₀ n, g u / u ^ (p + 1)`, with the sum indexed by those `u` for which
the denominator is nonzero. It defines `asympBound` by adding `n ^ p` to the transform with
lower endpoint zero. Here, the exponent `p` is the one established in the previous section.

Several properties of the sum transform are then proven.
-/

/-- The indices in the interval with nonzero denominator in the sum transform. -/
noncomputable def sumTransformIndices (p : ℝ) (n₀ n : ℕ) :
    Finset {u : ℕ // (u : ℝ) ^ (p + 1) ≠ 0} :=
  (Ico n₀ n).preimage Subtype.val Subtype.val_injective.injOn

private lemma mem_sumTransformIndices {p : ℝ} {n₀ n : ℕ}
    {u : {u : ℕ // (u : ℝ) ^ (p + 1) ≠ 0}} :
    u ∈ sumTransformIndices p n₀ n ↔ n₀ ≤ u.val ∧ u.val < n :=
  mem_preimage.trans mem_Ico

private lemma card_sumTransformIndices {p : ℝ} {n₀ n : ℕ} (hn₀ : 0 < n₀) :
    #(sumTransformIndices p n₀ n) = n - n₀ := by
  classical
  rw [sumTransformIndices, card_preimage, filter_eq_self.2 ?_, Nat.card_Ico]
  intro u hu
  have hu' : 0 < (u : ℝ) := by exact_mod_cast hn₀.trans_le (mem_Ico.mp hu).1
  exact ⟨⟨u, (rpow_pos_of_pos hu' _).ne'⟩, rfl⟩

private lemma sumTransformDenominator_pos (p : ℝ)
    (u : {u : ℕ // (u : ℝ) ^ (p + 1) ≠ 0}) : 0 < (u.val : ℝ) ^ (p + 1) :=
  lt_of_le_of_ne (rpow_nonneg (Nat.cast_nonneg _) _) u.property.symm

/-- The sum of `g u / u ^ (p + 1)` over the indices in `[n₀, n)` with nonzero denominator.
The term at `u = 0` contributes `g 0` precisely when it lies in the interval and `p + 1 = 0`. -/
noncomputable def sumTransformSum (p : ℝ) (g : ℝ → ℝ) (n₀ n : ℕ) : ℝ :=
  ∑ u ∈ sumTransformIndices p n₀ n,
    Checked.div (g u.val) ((u.val : ℝ) ^ (p + 1)) u.property.isUnit

lemma sumTransformSum_nonneg (p : ℝ) (g : ℝ → ℝ) (hg : ∀ x ≥ 0, 0 ≤ g x) (n₀ n : ℕ) :
    0 ≤ sumTransformSum p g n₀ n := by
  unfold sumTransformSum
  exact sum_nonneg fun u _ ↦ div_nonneg (hg u.val (Nat.cast_nonneg _))
    (sumTransformDenominator_pos p u).le

lemma sumTransformSum_add_adjacent (p : ℝ) (g : ℝ → ℝ) {n₀ m n : ℕ}
    (hn₀ : n₀ ≤ m) (hm : m ≤ n) :
    sumTransformSum p g n₀ m + sumTransformSum p g m n = sumTransformSum p g n₀ n := by
  classical
  unfold sumTransformSum sumTransformIndices
  rw [← sum_union (disjoint_preimage (Ico_disjoint_Ico_consecutive n₀ m n))]
  congr 1
  ext u
  simp only [mem_union, mem_preimage]
  rw [← mem_union, Ico_union_Ico_eq_Ico hn₀ hm]

/-- The sum transform multiplies the supported sum by `n ^ p`. -/
noncomputable def sumTransform (p : ℝ) (g : ℝ → ℝ) (n₀ n : ℕ) :=
  n ^ p * sumTransformSum p g n₀ n

lemma sumTransform_def {p : ℝ} {g : ℝ → ℝ} {n₀ n : ℕ} :
    sumTransform p g n₀ n = n ^ p * sumTransformSum p g n₀ n := rfl


variable (g) (a) (b)
/-- The asymptotic bound is `n ^ p` times one plus the supported sum below `n`. -/
noncomputable def asympBound (n : ℕ) : ℝ := n ^ p a b + sumTransform (p a b) g 0 n

lemma asympBound_def {α} [Fintype α] (a b : α → ℝ) {n : ℕ} :
    asympBound g a b n = n ^ p a b + sumTransform (p a b) g 0 n := rfl

variable {g} {a} {b}

lemma asympBound_def' {α} [Fintype α] (a b : α → ℝ) {n : ℕ} :
    asympBound g a b n = n ^ p a b * (1 + sumTransformSum (p a b) g 0 n) := by
  simp [asympBound_def, sumTransform, mul_add, mul_one]

section
include R

lemma asympBound_pos (n : ℕ) (hn : 0 < n) : 0 < asympBound g a b n := by
  rw [asympBound_def']
  exact mul_pos (rpow_pos_of_pos (by exact_mod_cast hn) _)
    (add_pos_of_pos_of_nonneg zero_lt_one (sumTransformSum_nonneg _ _ R.g_nonneg _ _))

lemma eventually_asympBound_pos : ∀ᶠ (n : ℕ) in atTop, 0 < asympBound g a b n := by
  filter_upwards [eventually_gt_atTop 0] with n hn using R.asympBound_pos n hn

lemma eventually_asympBound_r_pos : ∀ᶠ (n : ℕ) in atTop, ∀ i, 0 < asympBound g a b (r i n) := by
  rw [Filter.eventually_all]
  exact fun i => (R.tendsto_atTop_r i).eventually R.eventually_asympBound_pos

omit R in
private lemma rpow_bounds {c n u : ℝ} (hc : 0 < c) (hn : 0 < n)
    (hlo : c * n ≤ u) (hhi : u ≤ n) (q : ℝ) :
    min (c ^ q) 1 * n ^ q ≤ u ^ q ∧ u ^ q ≤ max (c ^ q) 1 * n ^ q := by
  have hnq : 0 ≤ n ^ q := (rpow_pos_of_pos hn q).le
  have hcn : 0 < c * n := mul_pos hc hn
  have hu := hcn.trans_le hlo
  rcases le_or_gt 0 q with hq | hq
  · constructor
    · calc
        _ ≤ c ^ q * n ^ q := mul_le_mul_of_nonneg_right (min_le_left _ _) hnq
        _ = (c * n) ^ q := (mul_rpow hc.le hn.le).symm
        _ ≤ _ := rpow_le_rpow hcn.le hlo hq
    · calc
        _ ≤ n ^ q := rpow_le_rpow hu.le hhi hq
        _ = 1 * n ^ q := (one_mul _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hnq
  · constructor
    · calc
        _ ≤ 1 * n ^ q := mul_le_mul_of_nonneg_right (min_le_right _ _) hnq
        _ = n ^ q := one_mul _
        _ ≤ _ := rpow_le_rpow_of_nonpos hu hhi hq.le
    · calc
        _ ≤ (c * n) ^ q := rpow_le_rpow_of_nonpos hcn hlo hq.le
        _ = c ^ q * n ^ q := mul_rpow hc.le hn.le
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hnq

omit R in
private lemma sumTransform_scale {n c : ℝ} (hn : 0 < n) (hc : 0 < c) (p x : ℝ) :
    n ^ p * n * (x / (c * n ^ (p + 1))) = x / c := by
  rw [← Real.rpow_add_one hn.ne' p]
  field_simp [(rpow_pos_of_pos hn (p + 1)).ne', hc.ne']

lemma eventually_atTop_sumTransform_le :
    ∃ C > 0, ∀ᶠ (n : ℕ) in atTop, ∀ i, sumTransform (p a b) g (r i n) n ≤ C * g n := by
  obtain ⟨c, hc, hr⟩ := R.exists_eventually_const_mul_le_r
  obtain ⟨A, hA, hbound⟩ := R.g_grows_poly.eventually_atTop_le_nat hc
  let q := p a b + 1
  let d := min (c ^ q) 1
  have hd : 0 < d := lt_min (rpow_pos_of_pos hc.1 q) zero_lt_one
  refine ⟨A / d, div_pos hA hd, ?_⟩
  filter_upwards [hr, hbound, R.eventually_r_pos, eventually_gt_atTop 0] with n hnlo hgn hrpos hn i
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hden : 0 < d * (n : ℝ) ^ q := mul_pos hd (rpow_pos_of_pos hn' q)
  have hg : 0 ≤ A * g n := mul_nonneg hA.le (R.g_nonneg n (Nat.cast_nonneg _))
  have hterm (u : {u : ℕ // (u : ℝ) ^ (p a b + 1) ≠ 0})
      (hu : u ∈ sumTransformIndices (p a b) (r i n) n) :
      Checked.div (g u.val) ((u.val : ℝ) ^ q) u.property.isUnit ≤
        A * g n / (d * (n : ℝ) ^ q) := by
    obtain ⟨hlo, hhi⟩ := mem_sumTransformIndices.mp hu
    have hseg : (u.val : ℝ) ∈ Set.Icc (c * (n : ℝ)) n :=
      ⟨(hnlo i).trans (by exact_mod_cast hlo), by exact_mod_cast hhi.le⟩
    exact (div_le_div_of_nonneg_right (hgn _ hseg) (sumTransformDenominator_pos _ u).le).trans
      (div_le_div_of_nonneg_left hg hden (rpow_bounds hc.1 hn' hseg.1 hseg.2 q).1)
  have hcard : (#(sumTransformIndices (p a b) (r i n) n) : ℝ) ≤ n := by
    rw [card_sumTransformIndices (hrpos i)]
    exact_mod_cast Nat.sub_le n (r i n)
  calc
    sumTransform (p a b) g (r i n) n ≤
        n ^ p a b * (#(sumTransformIndices (p a b) (r i n) n) *
          (A * g n / (d * (n : ℝ) ^ q))) := by
      apply mul_le_mul_of_nonneg_left _ (rpow_nonneg (Nat.cast_nonneg n) _)
      simpa only [sumTransformSum, nsmul_eq_mul] using sum_le_card_nsmul _ _ _ hterm
    _ ≤ n ^ p a b * (n * (A * g n / (d * (n : ℝ) ^ q))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hcard (div_nonneg hg hden.le))
        (rpow_nonneg hn'.le _)
    _ = (A / d) * g n := by
      rw [← mul_assoc, sumTransform_scale hn' hd]
      exact (div_mul_eq_mul_div₀ _ _ _).symm

lemma eventually_atTop_sumTransform_ge :
    ∃ C > 0, ∀ᶠ (n : ℕ) in atTop, ∀ i, C * g n ≤ sumTransform (p a b) g (r i n) n := by
  obtain ⟨c, hc, hr⟩ := R.exists_eventually_const_mul_le_r
  obtain ⟨A, hA, hbound⟩ := R.g_grows_poly.eventually_atTop_ge_nat hc
  obtain ⟨b', hb', hr'⟩ := R.exists_eventually_r_le_const_mul
  let q := p a b + 1
  let d := max (c ^ q) 1
  have hd : 0 < d := zero_lt_one.trans_le (le_max_right _ _)
  have hb₀ : 0 < 1 - b' := sub_pos.mpr hb'.2
  refine ⟨((1 - b') * A) / d, div_pos (mul_pos hb₀ hA) hd, ?_⟩
  filter_upwards [hr, hbound, hr', R.eventually_r_pos, R.eventually_r_lt_n, eventually_gt_atTop 0]
    with n hnlo hgn hnhi hrpos hrlt hn i
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hden : 0 < d * (n : ℝ) ^ q := mul_pos hd (rpow_pos_of_pos hn' q)
  have hg : 0 ≤ A * g n := mul_nonneg hA.le (R.g_nonneg n (Nat.cast_nonneg _))
  have hterm (u : {u : ℕ // (u : ℝ) ^ (p a b + 1) ≠ 0})
      (hu : u ∈ sumTransformIndices (p a b) (r i n) n) :
      A * g n / (d * (n : ℝ) ^ q) ≤
        Checked.div (g u.val) ((u.val : ℝ) ^ q) u.property.isUnit := by
    obtain ⟨hlo, hhi⟩ := mem_sumTransformIndices.mp hu
    have hseg : (u.val : ℝ) ∈ Set.Icc (c * (n : ℝ)) n :=
      ⟨(hnlo i).trans (by exact_mod_cast hlo), by exact_mod_cast hhi.le⟩
    have hu_pos : 0 < (u.val : ℝ) ^ q := sumTransformDenominator_pos _ u
    exact (div_le_div_of_nonneg_left hg hu_pos (rpow_bounds hc.1 hn' hseg.1 hseg.2 q).2).trans
      (div_le_div_of_nonneg_right (hgn _ hseg) hu_pos.le)
  have hcard : (n : ℝ) * (1 - b') ≤ #(sumTransformIndices (p a b) (r i n) n) := by
    rw [card_sumTransformIndices (hrpos i), Nat.cast_sub (hrlt i).le]
    have h := hnhi i
    rw [mul_sub, mul_one, mul_comm (n : ℝ) b']
    exact sub_le_sub_left h _
  calc
    ((1 - b') * A / d) * g n =
        n ^ p a b * n * ((1 - b') * A * g n / (d * (n : ℝ) ^ q)) := by
      rw [sumTransform_scale hn' hd]
      exact div_mul_eq_mul_div₀ _ _ _
    _ = n ^ p a b * (n * (1 - b') * (A * g n / (d * (n : ℝ) ^ q))) := by
      simp only [div_eq_mul_inv₀]
      ring
    _ ≤ n ^ p a b * (#(sumTransformIndices (p a b) (r i n) n) *
          (A * g n / (d * (n : ℝ) ^ q))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hcard (div_nonneg hg hden.le))
        (rpow_nonneg hn'.le _)
    _ ≤ sumTransform (p a b) g (r i n) n := by
      apply mul_le_mul_of_nonneg_left _ (rpow_nonneg (Nat.cast_nonneg n) _)
      simpa only [sumTransformSum, nsmul_eq_mul] using card_nsmul_le_sum _ _ _ hterm

end

end AkraBazziRecurrence
