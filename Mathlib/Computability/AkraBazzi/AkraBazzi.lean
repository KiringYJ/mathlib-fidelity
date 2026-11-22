/-
Copyright (c) 2023 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Computability.AkraBazzi.SumTransform
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Divide-and-conquer recurrences and the Akra-Bazzi theorem

A divide-and-conquer recurrence is a function `T : ℕ → ℝ` that satisfies a recurrence relation of
the form `T(n) = ∑_{i=0}^{k-1} a_i T(r_i(n)) + g(n)` for sufficiently large `n`, where `r_i(n)` is
a function such that `‖r_i(n) - b_i n‖ ∈ o(n / (log n)^2)` for every `i`, the coefficients `a_i`
are positive, and the coefficients `b_i` are real numbers in `(0, 1)`. (This assumption can be
relaxed to `O(n / (log n)^(1+ε))`, for some `ε > 0`; we leave this as future work.) These
recurrences arise mainly in the analysis of divide-and-conquer algorithms such as mergesort or
Strassen's algorithm for matrix multiplication. This class of algorithms works by dividing an
instance of the problem of size `n`, into `k` smaller instances, where the `i`-th instance is of
size roughly `b_i n`, and calling itself recursively on those smaller instances. `T(n)` then
represents the running time of the algorithm, and `g(n)` represents the running time required to
divide the instance and process the answers produced by the recursive calls. Since virtually all
such algorithms produce instances that are only approximately of size `b_i n` (they must round up
or down, at the very least), we allow the instance sizes to be given by a function `r_i(n)` that
approximates `b_i n`.

The Akra-Bazzi theorem gives the asymptotic order of such a recurrence: it states that
`T(n) ∈ Θ(n^p (1 + ∑_u g(u) / u^{p+1}))`,
where `p` is the unique real number such that `∑ a_i b_i^p = 1`. The sum includes the indices
`0 ≤ u < n` with nonzero denominator. Thus the index zero contributes when `n > 0` and `p = -1`.

## Main definitions and results

* `isTheta_asympBound`: The main result stating that
  `T(n) ∈ Θ(n^p (1 + ∑_u g(u) / u^{p+1}))`

## Implementation

Note that the original version of the Akra–Bazzi theorem uses an integral rather than the sum in
the above expression, and first considers the `T : ℝ → ℝ` case before moving on to `ℕ → ℝ`. We
prove the version with a sum here, as it is simpler and more relevant for algorithms.

## TODO

* Relax the assumption described in the introduction from `o(n / (log n)^2)` to
  `O(n / (log n)^(1+ε))`, for some `ε > 0`.
* Specialize this theorem to the very common case where the recurrence is of the form
  `T(n) = ℓT(r_i(n)) + g(n)`
  where `g(n) ∈ Θ(n^t)` for some `t`. (This is often called the "master theorem" in the literature.)
* Add the original version of the theorem with an integral instead of a sum.

## References

* Mohamad Akra and Louay Bazzi, On the solution of linear recurrence equations
* Tom Leighton, Notes on better master theorems for divide-and-conquer recurrences
* Manuel Eberl, Asymptotic reasoning in a proof assistant

-/

public section

open Finset Real Filter Asymptotics
open scoped Topology

namespace AkraBazziRecurrence

variable {α : Type*} [Fintype α] {T : ℕ → ℝ} {g : ℝ → ℝ} {a b : α → ℝ} {r : α → ℕ → ℕ}
variable [Nonempty α] (R : AkraBazziRecurrence T g a b r)


local notation "ε" => smoothingFn


/-!
### Technical lemmas

The next several lemmas are technical results leading up to `rpow_p_mul_one_sub_smoothingFn_le` and
`rpow_p_mul_one_add_smoothingFn_ge`, which are key steps in the main proof.
-/

local notation "L" => (comap (Subtype.val : SmoothingDomain → ℝ) atTop)

private noncomputable def smoothedPower (p t : ℝ) (x : SmoothingDomain) : ℝ :=
  x.val ^ p * (1 + t * ε x)

private lemma deriv_smoothedPower (p t : ℝ) :
    (fun x ↦ deriv (smoothedPower p t) x Subtype.val) =ᶠ[L]
      fun x ↦ x.val ^ (p - 1) * (p * (1 + t * ε x) - t * ε x ^ 2) := by
  filter_upwards [tendsto_comap.eventually (eventually_gt_atTop (0 : ℝ))] with x hx
  have hr : HasDerivAt (fun y : SmoothingDomain ↦ y.val ^ p) (p * x.val ^ (p - 1)) x Subtype.val :=
    HasFDerivAtFilter.comp_tendsto (hasDerivAt_rpow_const (Or.inl hx.ne') (p := p)) Subtype.val
      ((continuous_subtype_val.tendsto x).prodMap (tendsto_pure_pure ..))
  have hd := (hasDerivAt_smoothingFn x).const_mul t
  have hsum : HasDerivAt (fun y ↦ 1 + t * ε y) _ x Subtype.val :=
    (hd.hasFDerivAt.const_add 1).hasDerivAt
  have d := (hr.mul hsum continuous_subtype_val.continuousAt).deriv
    isOpen_smoothingDomain.isOpenEmbedding_subtypeVal
  have hpow : x.val ^ p = x.val ^ (p - 1) * x.val := by
    rw [← Real.rpow_add_one hx.ne', sub_add_cancel]
  change deriv (smoothedPower p t) x Subtype.val = _
  calc
    _ = _ := d
    _ = _ := by
      simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, one_mul]
      unfold smoothingFn
      rw [hpow]
      field_simp
      ring

private lemma isEquivalent_deriv_smoothedPower {p : ℝ} (hp : p ≠ 0) (t : ℝ) :
    (fun x ↦ deriv (smoothedPower p t) x Subtype.val) ~[L] fun x ↦ p * x.val ^ (p - 1) := by
  have h : Tendsto (fun x ↦ p * (1 + t * ε x) - t * ε x ^ 2) L (𝓝 p) := by
    simpa using (((tendsto_const_nhds (x := (1 : ℝ))).add
      (tendsto_smoothingFn_zero.const_mul t)).const_mul p).sub
      ((tendsto_smoothingFn_zero.pow 2).const_mul t)
  have he := (isEquivalent_const_iff_tendsto hp).mpr h
  refine (deriv_smoothedPower p t).isEquivalent.trans ?_
  simpa only [Pi.mul_def, Function.const_def, mul_comm p] using!
    (IsEquivalent.refl (u := fun x : SmoothingDomain ↦ x.val ^ (p - 1))).mul he

private lemma growsPolynomially_norm_deriv_smoothedPower (p t : ℝ) (ht : |t| = 1) :
    GrowsPolynomially (fun x ↦ ‖deriv (smoothedPower p t) x Subtype.val‖) Subtype.val := by
  rcases eq_or_ne p 0 with rfl | hp
  · let g (x : ℝ) := x * (log x) ^ 2
    have hg : GrowsPolynomially g :=
      growsPolynomially_id.mul (growsPolynomially_log.pow 2 ((eventually_ge_atTop 1).mono
        fun _ hx ↦ log_nonneg hx))
    let i (x : SmoothingDomain) : {y // g y ≠ 0} :=
      ⟨x.val, mul_ne_zero (log_ne_zero.mp x.2.ne_zero).1 (pow_ne_zero 2 x.2.ne_zero)⟩
    apply GrowsPolynomially.congr_on (g := fun x : SmoothingDomain ↦
      Checked.inv (g x.val) (i x).2.isUnit)
    · filter_upwards [deriv_smoothedPower 0 t, tendsto_comap.eventually
        (eventually_gt_atTop (1 : ℝ))] with x hd hx
      have hx' : 0 < x.val := zero_lt_one.trans hx
      have hl := log_pos hx
      simp only [hd, zero_sub, Real.rpow_neg_one _ (hx := hx'.ne'.isUnit), zero_mul,
        Real.norm_eq_abs, abs_mul, abs_neg, ht, one_mul, abs_pow, abs_inv, abs_of_pos hx',
        smoothingFn, abs_of_pos hl, g, mul_inv₀, inv_pow₀, mul_comm]
    · exact hg.inv.comp_domain i
  · refine ((growsPolynomially_rpow (p - 1)).comp_domain
      (Subtype.val : SmoothingDomain → ℝ)).of_isTheta_on
      ?_ (Eventually.of_forall fun _ ↦ norm_nonneg _)
    exact (isEquivalent_deriv_smoothedPower hp t).isTheta.norm_left.trans
      ((isTheta_refl _ _).const_mul_left hp)

lemma eventually_deriv_rpow_p_mul_one_sub_smoothingFn (p : ℝ) :
    (fun x ↦ deriv (fun z : SmoothingDomain ↦ z.val ^ p * (1 - ε z)) x Subtype.val)
      =ᶠ[L] fun z ↦ p * z.val ^ (p - 1) * (1 - ε z) +
        Checked.div (z.val ^ (p - 1)) (log z.val ^ 2) (z.2.pow 2) := by
  filter_upwards [deriv_smoothedPower p (-1)] with x hx
  simpa +unfoldPartialApp only [smoothedPower, neg_one_mul, ← sub_eq_add_neg, sub_neg_eq_add,
    smoothingFn,
    div_eq_mul_inv₀, inv_pow₀, mul_add, mul_left_comm, mul_comm, mul_assoc] using hx

lemma eventually_deriv_rpow_p_mul_one_add_smoothingFn (p : ℝ) :
    (fun x ↦ deriv (fun z : SmoothingDomain ↦ z.val ^ p * (1 + ε z)) x Subtype.val)
      =ᶠ[L] fun z ↦ p * z.val ^ (p - 1) * (1 + ε z) -
        Checked.div (z.val ^ (p - 1)) (log z.val ^ 2) (z.2.pow 2) := by
  filter_upwards [deriv_smoothedPower p 1] with x hx
  simpa +unfoldPartialApp only [smoothedPower, one_mul, smoothingFn, div_eq_mul_inv₀, inv_pow₀,
    mul_sub,
    mul_left_comm, mul_comm, mul_assoc] using hx

lemma isEquivalent_deriv_rpow_p_mul_one_sub_smoothingFn {p : ℝ} (hp : p ≠ 0) :
    (fun x ↦ deriv (fun z : SmoothingDomain ↦ z.val ^ p * (1 - ε z)) x Subtype.val)
      ~[L] fun z ↦ p * z.val ^ (p - 1) := by
  simpa +unfoldPartialApp only [smoothedPower, neg_one_mul, ← sub_eq_add_neg] using
    isEquivalent_deriv_smoothedPower hp (-1)

lemma isEquivalent_deriv_rpow_p_mul_one_add_smoothingFn {p : ℝ} (hp : p ≠ 0) :
    (fun x ↦ deriv (fun z : SmoothingDomain ↦ z.val ^ p * (1 + ε z)) x Subtype.val)
      ~[L] fun z ↦ p * z.val ^ (p - 1) := by
  simpa +unfoldPartialApp only [smoothedPower, one_mul] using isEquivalent_deriv_smoothedPower hp 1

lemma isTheta_deriv_rpow_p_mul_one_sub_smoothingFn {p : ℝ} (hp : p ≠ 0) :
    (fun x ↦ ‖deriv (fun z : SmoothingDomain ↦ z.val ^ p * (1 - ε z)) x Subtype.val‖)
      =Θ[L] fun z ↦ z.val ^ (p - 1) :=
  (isEquivalent_deriv_rpow_p_mul_one_sub_smoothingFn hp).isTheta.norm_left.trans
    ((isTheta_refl _ _).const_mul_left hp)

lemma isTheta_deriv_rpow_p_mul_one_add_smoothingFn {p : ℝ} (hp : p ≠ 0) :
    (fun x ↦ ‖deriv (fun z : SmoothingDomain ↦ z.val ^ p * (1 + ε z)) x Subtype.val‖)
      =Θ[L] fun z ↦ z.val ^ (p - 1) :=
  (isEquivalent_deriv_rpow_p_mul_one_add_smoothingFn hp).isTheta.norm_left.trans
    ((isTheta_refl _ _).const_mul_left hp)

lemma growsPolynomially_deriv_rpow_p_mul_one_sub_smoothingFn (p : ℝ) :
    GrowsPolynomially (fun x ↦ ‖deriv (fun z : SmoothingDomain ↦ z.val ^ p * (1 - ε z)) x
      Subtype.val‖) Subtype.val := by
  simpa +unfoldPartialApp only [smoothedPower, neg_one_mul, ← sub_eq_add_neg] using
    growsPolynomially_norm_deriv_smoothedPower p (-1) (by norm_num)

lemma growsPolynomially_deriv_rpow_p_mul_one_add_smoothingFn (p : ℝ) :
    GrowsPolynomially (fun x ↦ ‖deriv (fun z : SmoothingDomain ↦ z.val ^ p * (1 + ε z)) x
      Subtype.val‖) Subtype.val := by
  simpa +unfoldPartialApp only [smoothedPower, one_mul] using
    growsPolynomially_norm_deriv_smoothedPower p 1 (by norm_num)

include R

lemma isBigO_apply_r_sub_b (q : ℝ → ℝ) (hq_diff : DifferentiableOn ℝ q (Set.Ioi 1))
    (hq_poly : GrowsPolynomially fun x => ‖deriv q x‖) (i : α) :
    (fun n => q (r i n) - q (b i * n)) =O[atTop] fun n => (deriv q n) * (r i n - b i * n) := by
  let b' := b (min_bi b) / 2
  have hb_pos : 0 < b' := by have := R.b_pos (min_bi b); positivity
  have hb_lt_one : b' < 1 := calc b (min_bi b) / 2
    _ < b (min_bi b) := div_two_lt_of_pos (R.b_pos (min_bi b))
    _ < 1 := R.b_lt_one (min_bi b)
  have hb : b' ∈ Set.Ioo 0 1 := ⟨hb_pos, hb_lt_one⟩
  have hb' (i) : b' ≤ b i := calc b (min_bi b) / 2
    _ ≤ b i / 2 := by gcongr; aesop
    _ ≤ b i := le_of_lt <| div_two_lt_of_pos (R.b_pos i)
  obtain ⟨c₁, _, c₂, _, hq_poly⟩ := (GrowsPolynomially.ambient_iff.mp hq_poly) b' hb
  rw [isBigO_iff]
  refine ⟨c₂, ?_⟩
  have h_tendsto : Tendsto (fun x => b' * x) atTop atTop :=
    Tendsto.const_mul_atTop hb_pos tendsto_id
  filter_upwards [hq_poly.natCast_atTop, R.eventually_bi_mul_le_r, eventually_ge_atTop R.n₀,
                  eventually_gt_atTop 0, (h_tendsto.eventually_gt_atTop 1).natCast_atTop] with
    n hn h_bi_le_r h_ge_n₀ h_n_pos h_bn
  rw [norm_mul, ← mul_assoc]
  refine Convex.norm_image_sub_le_of_norm_deriv_le
    (s := Set.Icc (b' * n) n) (fun z hz => ?diff) (fun z hz => (hn z hz).2)
    (convex_Icc _ _) ?mem_Icc <| ⟨h_bi_le_r i, by exact_mod_cast (le_of_lt (R.r_lt_n i n h_ge_n₀))⟩
  case diff =>
    refine hq_diff.differentiableAt (Ioi_mem_nhds ?_)
    calc 1 < b' * n := h_bn
         _ ≤ z := hz.1
  case mem_Icc =>
    refine ⟨by gcongr; exact hb' i, ?_⟩
    calc b i * n ≤ 1 * n := by gcongr; exact le_of_lt <| R.b_lt_one i
                 _ = n := by simp

/-- After division by the parent power and multiplication by the squared logarithm, the
perturbation in the branch power tends to zero and the smoothing correction tends to
`t * (b i) ^ (p a b) * (-log (b i))`. Its sign gives both branch inequalities. -/
private lemma tendsto_scaled_smoothing_difference (i : α) (t : ℝ) :
    let D := {n : ℕ // IsUnit (log (n : ℝ)) ∧ IsUnit (log (r i n : ℝ))}
    let l := comap (Subtype.val : D → ℕ) atTop
    Tendsto (fun n : D ↦
      let x := (n.val : ℝ)
      let y := (r i n.val : ℝ)
      have hx : x ≠ 0 := (log_ne_zero.mp n.2.1.ne_zero).1
      (((y / x) ^ (p a b) * (1 + t * ε ⟨y, n.2.2⟩) -
        (b i) ^ (p a b) * (1 + t * ε ⟨x, n.2.1⟩)) * log x ^ 2))
      l (𝓝 (t * (b i) ^ (p a b) * (-log (b i)))) := by
  let D := {n : ℕ // IsUnit (log (n : ℝ)) ∧ IsUnit (log (r i n : ℝ))}
  let l := comap (Subtype.val : D → ℕ) atTop
  let x (n : D) : ℝ := n.val
  let y (n : D) : ℝ := r i n.val
  have hx (n : D) : x n ≠ 0 := (log_ne_zero.mp n.2.1.ne_zero).1
  have hy (n : D) : y n ≠ 0 := (log_ne_zero.mp n.2.2.ne_zero).1
  let c (n : D) := Checked.div (y n) (x n) (hx n).isUnit
  let ex (n : D) := ε ⟨x n, n.2.1⟩
  let ey (n : D) := ε ⟨y n, n.2.2⟩
  let j (n : D) : LogNat := ⟨n.val, n.2.1⟩
  have hj : Tendsto j l (comap Subtype.val atTop) := tendsto_comap_iff.mpr tendsto_comap
  have he₁ : Tendsto ex l (𝓝 0) := tendsto_smoothingFn_zero.comp
    (tendsto_comap_iff.mpr (tendsto_natCast_atTop_atTop.comp tendsto_comap))
  have he₂ : Tendsto ey l (𝓝 0) := tendsto_smoothingFn_zero.comp
    (tendsto_comap_iff.mpr ((R.tendsto_atTop_r_real i).comp tendsto_comap))
  -- Normalize the branch error by the parent size.
  have hsmall : (fun n ↦ c n - b i) =o[l] fun n ↦ ex n ^ 2 := by
    have h := ((R.dist_r_b i).comp_tendsto hj).mul_isBigO
      (isBigO_refl (fun n : D ↦ Checked.inv (x n) (hx n).isUnit) l)
    apply h.congr
    · intro n
      change (y n - b i * x n) * (x n)⁻¹ = c n - b i
      simp only [c, sub_mul, mul_assoc, mul_inv_cancel₀, mul_one, div_eq_mul_inv₀]
    · intro n
      change Checked.div (x n) (log (x n) ^ 2) (n.2.1.pow 2) * (x n)⁻¹ =
        Checked.inv (log (x n)) n.2.1 ^ 2
      rw [inv_pow₀, div_eq_mul_inv₀, mul_right_comm, mul_inv_cancel₀, one_mul]
  have hsquare : Tendsto (fun n ↦ ex n ^ 2) l (𝓝 0) := by simpa using he₁.pow 2
  have hc : Tendsto c l (𝓝 (b i)) := by
    simpa using (hsmall.tendsto_zero_of_tendsto hsquare).add_const (b i)
  have hder := hasDerivAt_rpow_const (p := p a b) (Or.inl (R.b_pos i).ne')
  have hpow := (hder.isBigO_sub.comp_tendsto hc).trans_isLittleO hsmall
  have hpowlim : Tendsto (fun n ↦ (c n ^ p a b - (b i) ^ p a b) * log (x n) ^ 2) l (𝓝 0) := by
    have h := hpow.tendsto_div_nhds_zero (hg := fun n ↦ ((n.2.1).inv₀).pow 2)
    simpa only [Function.comp_def, id_eq, ex, smoothingFn, inv_pow₀, div_inv_eq_mul₀] using! h
  have hclog := (continuousAt_log (R.b_pos i).ne').tendsto.comp hc
  -- The change in the reciprocal logarithm has leading coefficient -log (b i).
  have hshift : Tendsto (fun n ↦ (ey n - ex n) * log (x n) ^ 2) l (𝓝 (-log (b i))) := by
    have h := hclog.neg.mul ((tendsto_const_nhds (x := (1 : ℝ))).sub (hclog.mul he₂))
    refine (by simpa using h : Tendsto (fun n ↦ -log (c n) * (1 - log (c n) * ey n)) l
      (𝓝 (-log (b i)))).congr fun n ↦ ?_
    have hlog : log (c n) = log (y n) - log (x n) := log_div (hy n)
    change -log (c n) * (1 - log (c n) * Checked.inv (log (y n)) n.2.2) =
      (Checked.inv (log (y n)) n.2.2 - Checked.inv (log (x n)) n.2.1) * log (x n) ^ 2
    rw [hlog]
    field_simp
    ring
  have ht := (hpowlim.mul ((tendsto_const_nhds (x := (1 : ℝ))).add (he₂.const_mul t))).add
    (hshift.const_mul (t * (b i) ^ (p a b)))
  refine (by simpa using ht : Tendsto (fun n ↦
    (c n ^ p a b - (b i) ^ p a b) * log (x n) ^ 2 * (1 + t * ey n) +
      t * (b i) ^ p a b * ((ey n - ex n) * log (x n) ^ 2)) l
      (𝓝 (t * (b i) ^ p a b * (-log (b i))))).congr fun n ↦ ?_
  change _ = (c n ^ p a b * (1 + t * ey n) - (b i) ^ p a b * (1 + t * ex n)) * log (x n) ^ 2
  ring

private lemma eventually_smoothed_brackets (i : α) :
    ∀ᶠ n : ℕ in atTop, ∀ (hn : IsUnit (log (n : ℝ))) (hr : IsUnit (log (r i n : ℝ))),
      (r i n : ℝ) ^ p a b * (1 - ε ⟨r i n, hr⟩) ≤
        (b i) ^ p a b * n ^ p a b * (1 - ε ⟨n, hn⟩) ∧
      (b i) ^ p a b * n ^ p a b * (1 + ε ⟨n, hn⟩) ≤
        (r i n : ℝ) ^ p a b * (1 + ε ⟨r i n, hr⟩) := by
  have hb := R.b_pos i
  have hlog : 0 < -log (b i) := neg_pos.mpr (log_neg hb (R.b_lt_one i))
  have hpow : 0 < (b i) ^ p a b := rpow_pos_of_pos hb _
  have hm := (R.tendsto_scaled_smoothing_difference i (-1)).eventually_lt_const
    (mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos neg_one_lt_zero hpow) hlog)
  have hp := (R.tendsto_scaled_smoothing_difference i 1).eventually_const_lt
    (show 0 < (1 : ℝ) * (b i) ^ p a b * (-log (b i)) by positivity)
  filter_upwards [eventually_comap.mp (hm.and hp)] with n hh hn hr
  obtain ⟨hm, hp⟩ := hh ⟨n, hn, hr⟩ rfl
  have hx : (n : ℝ) ≠ 0 := (log_ne_zero.mp hn.ne_zero).1
  have hnp : 0 < (n : ℝ) ^ p a b := rpow_pos_of_pos ((Nat.cast_nonneg n).lt_of_ne' hx) _
  have hlp := sq_pos_of_ne_zero hn.ne_zero
  dsimp only at hm hp
  simp only [neg_one_mul, ← sub_eq_add_neg, one_mul] at hm hp
  have hm' := sub_nonpos.mp (neg_of_mul_neg_left hm hlp.le).le
  have hp' := sub_nonneg.mp ((mul_pos_iff_of_pos_right hlp).mp hp).le
  have hc : (((r i n : ℝ) / (n : ℝ)) ^ p a b) * (n : ℝ) ^ p a b = (r i n : ℝ) ^ p a b := by
    rw [div_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _) _, div_mul_cancel₀]
  constructor
  · simpa only [mul_right_comm _ _ ((n : ℝ) ^ p a b), hc] using
      mul_le_mul_of_nonneg_right hm' hnp.le
  · simpa only [mul_right_comm _ _ ((n : ℝ) ^ p a b), hc] using
      mul_le_mul_of_nonneg_right hp' hnp.le

lemma rpow_p_mul_one_sub_smoothingFn_le :
    ∀ᶠ n : ℕ in atTop, ∀ i, ∀ (hn : IsUnit (log (n : ℝ))) (hr : IsUnit (log (r i n : ℝ))),
      (r i n : ℝ) ^ p a b * (1 - ε ⟨r i n, hr⟩) ≤
        (b i) ^ p a b * n ^ p a b * (1 - ε ⟨n, hn⟩) := by
  rw [Filter.eventually_all]
  exact fun i ↦ (R.eventually_smoothed_brackets i).mono fun _ h hn hr ↦ (h hn hr).1

lemma rpow_p_mul_one_add_smoothingFn_ge :
    ∀ᶠ n : ℕ in atTop, ∀ i, ∀ (hn : IsUnit (log (n : ℝ))) (hr : IsUnit (log (r i n : ℝ))),
      (b i) ^ p a b * n ^ p a b * (1 + ε ⟨n, hn⟩) ≤
        (r i n : ℝ) ^ p a b * (1 + ε ⟨r i n, hr⟩) := by
  rw [Filter.eventually_all]
  exact fun i ↦ (R.eventually_smoothed_brackets i).mono fun _ h hn hr ↦ (h hn hr).2

/-!
### Main proof

This final section proves the Akra-Bazzi theorem.
-/

local notation "Lₙ" => comap (Subtype.val : LogNat → ℕ) atTop

omit R in
private lemma isBigO_logNat_induction {F G : LogNat → ℝ}
    (hF : ∀ᶠ n : ℕ in atTop, ∀ hn, 0 ≤ F ⟨n, hn⟩)
    (hG : ∀ᶠ n : ℕ in atTop, ∀ hn, 0 < G ⟨n, hn⟩)
    (hstep : ∀ᶠ n₀ : ℕ in atTop, ∃ C₀, ∀ᶠ n : ℕ in atTop, ∀ hn, ∀ C ≥ C₀,
      (∀ m ∈ Ico n₀ n, ∀ hm, F ⟨m, hm⟩ ≤ C * G ⟨m, hm⟩) → F ⟨n, hn⟩ ≤ C * G ⟨n, hn⟩) :
    F =O[Lₙ] G := by
  obtain ⟨k, hk⟩ := eventually_atTop.mp eventually_logNat
  let lift (n : ℕ) : LogNat := ⟨n + k, hk _ (by omega)⟩
  have hshift := tendsto_add_atTop_nat k
  have h : (F ∘ lift) =O[atTop] (G ∘ lift) := by
    refine isBigO_nat_atTop_induction_of_eventually_pos ?_ ?_ ?_
    · refine (hshift.eventually hF).mono fun n hn ↦ ?_
      exact hn (lift n).2
    · refine (hshift.eventually hG).mono fun n hn ↦ ?_
      exact hn (lift n).2
    · filter_upwards [hshift.eventually hstep] with n₀ hn₀
      obtain ⟨C₀, hn₀⟩ := hn₀
      refine ⟨C₀, (hshift.eventually hn₀).mono fun n hn C hC hind ↦ ?_⟩
      refine hn (lift n).2 C hC fun m hm hdom ↦ ?_
      obtain ⟨hmlo, hmhi⟩ := mem_Ico.mp hm
      have he : lift (m - k) = ⟨m, hdom⟩ := Subtype.ext (Nat.sub_add_cancel (by omega))
      simpa only [Function.comp_apply, he] using hind (m - k) (mem_Ico.mpr ⟨by omega, by omega⟩)
  obtain ⟨C, hC⟩ := isBigO_iff.mp h
  refine IsBigO.of_bound C (eventually_comap.2 ?_)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hC
  apply eventually_atTop.mpr
  refine ⟨N + k, fun n hn m hm ↦ ?_⟩
  have he : lift (n - k) = m := Subtype.ext ((Nat.sub_add_cancel (by omega)).trans hm.symm)
  simpa only [Function.comp_apply, he] using hN (n - k) (by omega)

omit R [Nonempty α] in
private lemma asympBound_sub_sumTransform {m n : ℕ} (h : m ≤ n) :
    n ^ p a b * (1 + sumTransformSum (p a b) g 0 m) =
      asympBound g a b n - sumTransform (p a b) g m n := by
  rw [asympBound_def', sumTransform_def,
    ← sumTransformSum_add_adjacent (p a b) g (Nat.zero_le m) h]
  ring

omit R in
private lemma nat_le_mul_of_ceil_div_le {c : ℝ} (hc : 0 < c) {m n : ℕ}
    (h : ⌈(m : ℝ) / c⌉₊ ≤ n) : (m : ℝ) ≤ c * n := by
  have h' : (m : ℝ) / c ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast h)
  simpa only [mul_comm (n : ℝ) c] using (div_le_iff₀ hc).mp h'

/-- The factor `1 - ε n` in the upper bound makes the induction step possible. -/
lemma T_isBigO_smoothingFn_mul_asympBound :
    (fun n : LogNat ↦ T n.val) =O[Lₙ]
      (fun n : LogNat ↦ (1 - ε ⟨(n.val : ℝ), n.2⟩) * asympBound g a b n.val) := by
  refine isBigO_logNat_induction (.of_forall fun n _ ↦ R.T_nonneg n) ?_ ?_
  · filter_upwards [R.eventually_asympBound_pos, eventually_one_sub_smoothingFn_pos]
      with n hA hε hn
    exact mul_pos (hε hn) hA
  let b' := b (min_bi b) / 2
  have hb' : 0 < b' := R.bi_min_div_two_pos
  obtain ⟨c, hc, hsum⟩ := R.eventually_atTop_sumTransform_ge
  filter_upwards [eventually_ge_atTop R.n₀, eventually_forall_ge_atTop.mpr eventually_logNat]
    with n₀ hn₀ hdomain
  refine ⟨2 / c, ?_⟩
  filter_upwards [eventually_ge_atTop n₀, R.rpow_p_mul_one_sub_smoothingFn_le, hsum,
    eventually_one_sub_smoothingFn_gt_const (1 / 2) (by norm_num), R.eventually_bi_mul_le_r,
    eventually_ge_atTop ⌈(n₀ : ℝ) / b'⌉₊] with n hn hpower hsum hε hr hceil
  have hnr (i : α) : n₀ ≤ r i n := by
    exact_mod_cast (nat_le_mul_of_ceil_div_le hb' hceil).trans (hr i)
  have hrn (i : α) : r i n < n := R.r_lt_n i n (hn₀.trans hn)
  intro hd C hC hind
  let e := 1 - ε ⟨(n : ℝ), hd⟩
  let er (i : α) := 1 - ε ⟨(r i n : ℝ), hdomain _ (hnr i)⟩
  have he : (1 / 2 : ℝ) < e := hε hd
  have he₀ : 0 ≤ e := by linarith
  have hC₀ : 0 ≤ C := (div_pos (by norm_num) hc).le.trans hC
  have hg₀ : 0 ≤ g n := R.g_nonneg n (Nat.cast_nonneg _)
  have hbranch (i : α) :
      a i * T (r i n) ≤ (a i * (b i) ^ p a b) *
        (C * e * (asympBound g a b n - c * g n)) := by
    let S := 1 + sumTransformSum (p a b) g 0 (r i n)
    have hS : 0 ≤ S := add_nonneg zero_le_one (sumTransformSum_nonneg _ _ R.g_nonneg _ _)
    have h₁ := hind (r i n) (mem_Ico.mpr ⟨hnr i, hrn i⟩) (hdomain _ (hnr i))
    have h₂ : (r i n : ℝ) ^ p a b * er i ≤ (b i) ^ p a b * n ^ p a b * e :=
      hpower i hd (hdomain _ (hnr i))
    have h₃ := asympBound_sub_sumTransform (g := g) (a := a) (b := b) (hrn i).le
    calc
      _ ≤ a i * (C * (er i * asympBound g a b (r i n))) :=
        mul_le_mul_of_nonneg_left h₁ (R.a_pos i).le
      _ = (a i * C) * ((r i n : ℝ) ^ p a b * er i) * S := by
        rw [asympBound_def']
        dsimp only [S]
        ring
      _ ≤ (a i * C) * ((b i) ^ p a b * n ^ p a b * e) * S :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h₂
          (mul_nonneg (R.a_pos i).le hC₀)) hS
      _ = (a i * (b i) ^ p a b) *
          (C * e * (asympBound g a b n - sumTransform (p a b) g (r i n) n)) := by
        rw [← h₃]
        dsimp only [S]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (sub_le_sub_left (hsum i) _) (mul_nonneg hC₀ he₀))
        (mul_nonneg (R.a_pos i).le (rpow_nonneg (R.b_pos i).le _))
  have hbudget : 1 ≤ C * c * e := by
    calc
      1 = (2 / c) * c * (1 / 2) := by rw [div_mul_cancel₀]; norm_num
      _ ≤ C * c * (1 / 2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hc.le) (by norm_num)
      _ ≤ _ := mul_le_mul_of_nonneg_left he.le (mul_nonneg hC₀ hc.le)
  calc
    T n = (∑ i, a i * T (r i n)) + g n := R.h_rec n (hn₀.trans hn)
    _ ≤ (∑ i, (a i * (b i) ^ p a b) * (C * e * (asympBound g a b n - c * g n))) + g n :=
      add_le_add_left (sum_le_sum fun i _ ↦ hbranch i) _
    _ = C * e * asympBound g a b n + (1 - C * c * e) * g n := by
      rw [← sum_mul, R.sumCoeffsExp_p_eq_one, one_mul]
      ring
    _ ≤ C * (e * asympBound g a b n) := by
      linarith only [mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hbudget) hg₀]

/-- The factor `1 + ε n` in the lower bound makes the induction step possible. -/
lemma smoothingFn_mul_asympBound_isBigO_T :
    (fun n : LogNat ↦ (1 + ε ⟨(n.val : ℝ), n.2⟩) * asympBound g a b n.val) =O[Lₙ]
      (fun n : LogNat ↦ T n.val) := by
  refine isBigO_logNat_induction ?_ (.of_forall fun n _ ↦ R.T_pos n) ?_
  · filter_upwards [R.eventually_asympBound_pos, eventually_one_add_smoothingFn_pos]
      with n hA hε hn
    exact (mul_pos (hε hn) hA).le
  let b' := b (min_bi b) / 2
  have hb' : 0 < b' := R.bi_min_div_two_pos
  obtain ⟨c, hc, hsum⟩ := R.eventually_atTop_sumTransform_le
  filter_upwards [eventually_ge_atTop R.n₀, eventually_forall_ge_atTop.mpr eventually_logNat]
    with n₀ hn₀ hdomain
  refine ⟨2 * c, ?_⟩
  filter_upwards [eventually_ge_atTop n₀, R.rpow_p_mul_one_add_smoothingFn_ge, hsum,
    eventually_one_add_smoothingFn_pos, R.eventually_bi_mul_le_r,
    eventually_ge_atTop ⌈(n₀ : ℝ) / b'⌉₊, eventually_ge_atTop ⌈exp 1⌉₊]
    with n hn hpower hsum hε hr hceil hexp
  have hnr (i : α) : n₀ ≤ r i n := by
    exact_mod_cast (nat_le_mul_of_ceil_div_le hb' hceil).trans (hr i)
  have hrn (i : α) : r i n < n := R.r_lt_n i n (hn₀.trans hn)
  intro hd C hC hind
  let e := 1 + ε ⟨(n : ℝ), hd⟩
  let er (i : α) := 1 + ε ⟨(r i n : ℝ), hdomain _ (hnr i)⟩
  have hexp' : exp 1 ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hexp)
  have he₂ : e ≤ 2 := one_add_smoothingFn_le_two (x := ⟨(n : ℝ), hd⟩) hexp'
  have he₀ : 0 ≤ e := (hε hd).le
  have hg₀ : 0 ≤ g n := R.g_nonneg n (Nat.cast_nonneg _)
  have hbranch (i : α) :
      (a i * (b i) ^ p a b) * (e * (asympBound g a b n - c * g n)) ≤
        a i * (C * T (r i n)) := by
    let S := 1 + sumTransformSum (p a b) g 0 (r i n)
    have hS : 0 ≤ S := add_nonneg zero_le_one (sumTransformSum_nonneg _ _ R.g_nonneg _ _)
    have h₁ := hind (r i n) (mem_Ico.mpr ⟨hnr i, hrn i⟩) (hdomain _ (hnr i))
    have h₂ : (b i) ^ p a b * n ^ p a b * e ≤ (r i n : ℝ) ^ p a b * er i :=
      hpower i hd (hdomain _ (hnr i))
    have h₃ := asympBound_sub_sumTransform (g := g) (a := a) (b := b) (hrn i).le
    calc
      _ ≤ (a i * (b i) ^ p a b) *
          (e * (asympBound g a b n - sumTransform (p a b) g (r i n) n)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (sub_le_sub_left (hsum i) _) he₀)
          (mul_nonneg (R.a_pos i).le (rpow_nonneg (R.b_pos i).le _))
      _ = a i * ((b i) ^ p a b * n ^ p a b * e) * S := by
        rw [← h₃]
        dsimp only [S]
        ring
      _ ≤ a i * ((r i n : ℝ) ^ p a b * er i) * S :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h₂ (R.a_pos i).le) hS
      _ = a i * (er i * asympBound g a b (r i n)) := by
        rw [asympBound_def']
        dsimp only [S]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h₁ (R.a_pos i).le
  have hbudget : c * e ≤ C :=
    (mul_le_mul_of_nonneg_left he₂ hc.le).trans (by simpa [mul_comm] using hC)
  calc
    e * asympBound g a b n ≤ e * (asympBound g a b n - c * g n) + C * g n := by
      have := mul_nonneg (sub_nonneg.mpr hbudget) hg₀
      linarith only [show e * (asympBound g a b n - c * g n) + C * g n =
        e * asympBound g a b n + (C - c * e) * g n by ring, this]
    _ = (∑ i, (a i * (b i) ^ p a b) * (e * (asympBound g a b n - c * g n))) + C * g n := by
      rw [← sum_mul, R.sumCoeffsExp_p_eq_one, one_mul]
    _ ≤ (∑ i, a i * (C * T (r i n))) + C * g n :=
      add_le_add_left (sum_le_sum fun i _ ↦ hbranch i) _
    _ = C * T n := by
      rw [R.h_rec n (hn₀.trans hn), mul_add, mul_sum]
      congr 1
      exact sum_congr rfl fun _ _ ↦ by ring

omit R in
private lemma map_logNat_atTop : map (Subtype.val : LogNat → ℕ) Lₙ = atTop :=
  map_comap_of_mem (eventually_logNat.mono fun n hn ↦ ⟨⟨n, hn⟩, rfl⟩)

omit R in
private lemma tendsto_logNat_smoothing :
    Tendsto (fun n : LogNat ↦ ε ⟨(n.val : ℝ), n.2⟩) Lₙ (𝓝 0) :=
  tendsto_smoothingFn_zero.comp
    (tendsto_comap_iff.2 (tendsto_natCast_atTop_atTop.comp tendsto_comap))

/-- The upper bound in the Akra–Bazzi theorem. -/
theorem isBigO_asympBound : T =O[atTop] asympBound g a b := by
  rw [← map_logNat_atTop, isBigO_map]
  refine R.T_isBigO_smoothingFn_mul_asympBound.trans ?_
  have ht : Tendsto (fun n : LogNat ↦ 1 - ε ⟨(n.val : ℝ), n.2⟩) Lₙ (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_logNat_smoothing
  simpa only [one_mul, Function.comp_apply, Function.const_apply] using!
    (isBigO_const_of_tendsto ht one_ne_zero).mul (isBigO_refl (asympBound g a b ∘ Subtype.val) Lₙ)

/-- The lower bound in the Akra–Bazzi theorem. -/
theorem isBigO_symm_asympBound : asympBound g a b =O[atTop] T := by
  rw [← map_logNat_atTop, isBigO_map]
  refine IsBigO.trans ?_ R.smoothingFn_mul_asympBound_isBigO_T
  have ht : Tendsto (fun n : LogNat ↦ 1 + ε ⟨(n.val : ℝ), n.2⟩) Lₙ (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add tendsto_logNat_smoothing
  have h := (isEquivalent_const_iff_tendsto one_ne_zero).2 ht
  simpa only [one_mul, Function.comp_apply, Function.const_apply] using!
    h.symm.isBigO.mul (isBigO_refl (asympBound g a b ∘ Subtype.val) Lₙ)

/-- The Akra–Bazzi theorem gives the asymptotic order of the recurrence. -/
theorem isTheta_asympBound : T =Θ[atTop] asympBound g a b :=
  ⟨R.isBigO_asympBound, R.isBigO_symm_asympBound⟩

end AkraBazziRecurrence
