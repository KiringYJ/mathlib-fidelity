/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Calculus.LogDeriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.ZPow
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Logarithmic Derivatives

The logarithmic derivative is the quotient of a uniquely determined derivative by the
function value at a point where that value is a unit. This file gives its calculus rules.

-/

@[expose] public section

noncomputable section

open Filter Function Set

open scoped Topology

variable {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedAlgebra 𝕜 𝕜']

/-- Equal values and derivatives give equal logarithmic derivatives on their common domain. -/
private lemma logDeriv_congr_of_eq {f g : 𝕜 → 𝕜'} {x : 𝕜}
    {hdf : ∃! d, HasDerivAt f d x} {hdg : ∃! d, HasDerivAt g d x}
    {hf : IsUnit (f x)} {hg : IsUnit (g x)} (hv : f x = g x)
    (hd : deriv f x = deriv g x) : logDeriv f x id hdf hf = logDeriv g x id hdg hg := by
  rw [logDeriv_apply, logDeriv_apply, hd]
  exact (show ∀ (a b : 𝕜') (ha : IsUnit a) (hb : IsUnit b), a = b →
    Checked.div (deriv g x) a ha = Checked.div (deriv g x) b hb from
    fun a b ha hb h ↦ by subst b; rfl) _ _ hf hg hv

/-- Functions agreeing near `x` have equal logarithmic derivatives at `x` on their common domain. -/
lemma logDeriv_congr {f g : 𝕜 → 𝕜'} {x : 𝕜}
    {hdf : ∃! d, HasDerivAt f d x} {hdg : ∃! d, HasDerivAt g d x}
    {hf : IsUnit (f x)} {hg : IsUnit (g x)} (h : f =ᶠ[𝓝 x] g) :
    logDeriv f x id hdf hf = logDeriv g x id hdg hg :=
  logDeriv_congr_of_eq h.eq_of_nhds h.deriv_eq

/-- Functions agreeing near `x` have equal logarithmic derivatives wherever both exist near `x`. -/
lemma logDeriv_congr_nhds {f g : 𝕜 → 𝕜'} {x : 𝕜} (h : f =ᶠ[𝓝 x] g) :
    ∀ᶠ y in 𝓝 x, ∀ (hdf : ∃! d, HasDerivAt f d y) (hdg : ∃! d, HasDerivAt g d y)
      (hf : IsUnit (f y)) (hg : IsUnit (g y)), logDeriv f y id hdf hf = logDeriv g y id hdg hg := by
  filter_upwards [h, h.deriv] with y hy hdy hdf hdg hf hg
  exact logDeriv_congr_of_eq hy hdy

/--
If two functions agree in a punctured neighborhood of `x`, then so do their logarithmic derivatives.
-/
lemma logDeriv_congr_nhdsNE {f g : 𝕜 → 𝕜'} {x : 𝕜} (h : f =ᶠ[𝓝[≠] x] g) :
    ∀ᶠ y in 𝓝[≠] x, ∀ (hdf : ∃! d, HasDerivAt f d y) (hdg : ∃! d, HasDerivAt g d y)
      (hf : IsUnit (f y)) (hg : IsUnit (g y)), logDeriv f y id hdf hf = logDeriv g y id hdg hg := by
  filter_upwards [h, h.nhdsNE_deriv] with y hy hdy hdf hdg hf hg
  exact logDeriv_congr_of_eq hy hdy

/--
If two functions agree on a codiscrete subset of an open set `U`, then so do their logarithmic
derivatives.
-/
theorem logDeriv_congr_codiscreteWithin {f g : 𝕜 → 𝕜'} {U : Set 𝕜} (hU : IsOpen U)
    (h : f =ᶠ[codiscreteWithin U] g) :
    ∀ᶠ y in codiscreteWithin U,
      ∀ (hdf : ∃! d, HasDerivAt f d y) (hdg : ∃! d, HasDerivAt g d y)
        (hf : IsUnit (f y)) (hg : IsUnit (g y)),
          logDeriv f y id hdf hf = logDeriv g y id hdg hg := by
  refine mem_codiscreteWithin_iff_forall_mem_nhdsNE.2 fun x hx ↦ ?_
  refine mem_of_superset (logDeriv_congr_nhdsNE ?_) Set.subset_union_left
  filter_upwards [mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 h x hx,
    nhdsWithin_le_nhds (hU.mem_nhds hx)] with z hz hzU
  exact hz.resolve_right (not_not_intro hzU)

/--
If two functions agree on a codiscrete subset of `𝕜`, then so do their logarithmic derivatives.
-/
theorem logDeriv_congr_codiscrete {f g : 𝕜 → 𝕜'} (h : f =ᶠ[codiscrete 𝕜] g) :
    ∀ᶠ y in codiscrete 𝕜, ∀ (hdf : ∃! d, HasDerivAt f d y) (hdg : ∃! d, HasDerivAt g d y)
      (hf : IsUnit (f y)) (hg : IsUnit (g y)), logDeriv f y id hdf hf = logDeriv g y id hdg hg :=
  logDeriv_congr_codiscreteWithin isOpen_univ h

@[simp]
theorem logDeriv_id (x : 𝕜) {hx : IsUnit x} :
    logDeriv id x id (hasDerivAt_id x).existsUnique_hasDerivAt hx = 1 / x :=
  logDeriv_eq (hasDerivAt_id x)

@[simp] theorem logDeriv_id' (x : 𝕜) {hx : IsUnit x} :
    logDeriv (·) x id (hasDerivAt_id x).existsUnique_hasDerivAt hx = 1 / x := logDeriv_id x

@[simp]
theorem logDeriv_const (a : 𝕜') (x : 𝕜) {ha : IsUnit a} :
    logDeriv (fun _ : 𝕜 ↦ a) x id (hasDerivAt_const x a).existsUnique_hasDerivAt ha = 0 := by
  rw [logDeriv_eq (hasDerivAt_const x a)]
  exact zero_div a

@[to_fun logDeriv_fun_mul]
theorem logDeriv_mul {f g : 𝕜 → 𝕜'} (x : 𝕜) {hf : IsUnit (f x)} {hg : IsUnit (g x)}
    (hdf : DifferentiableAt 𝕜 f x) (hdg : DifferentiableAt 𝕜 g x) :
    logDeriv (f * g) x id (hdf.hasDerivAt.mul hdg.hasDerivAt).existsUnique_hasDerivAt (hf.mul hg) =
      logDeriv f x id hdf.existsUnique_hasDerivAt hf +
        logDeriv g x id hdg.existsUnique_hasDerivAt hg := by
  rw [logDeriv_eq (hdf.hasDerivAt.mul hdg.hasDerivAt), logDeriv_apply, logDeriv_apply]
  change (deriv f x * g x + f x * deriv g x) / (f x * g x) = deriv f x / f x + deriv g x / g x
  field_simp

/-- The logarithmic derivative of the quotient on the domain where its denominator is a unit. -/
theorem logDeriv_div {f g : 𝕜 → 𝕜'} (x : 𝕜) {hf : IsUnit (f x)} {hg : IsUnit (g x)}
    (hdf : DifferentiableAt 𝕜 f x) (hdg : DifferentiableAt 𝕜 g x)
    {hquot : ∃! d, HasDerivAt (fun y : {y : 𝕜 | IsUnit (g y)} ↦ Checked.div (f y) (g y) y.2)
      d ⟨x, hg⟩ Subtype.val} :
    logDeriv (fun y : {y : 𝕜 | IsUnit (g y)} ↦ Checked.div (f y) (g y) y.2) ⟨x, hg⟩ Subtype.val
        hquot (hf.div₀ hg) =
      logDeriv f x id hdf.existsUnique_hasDerivAt hf -
        logDeriv g x id hdg.existsUnique_hasDerivAt hg := by
  have hq' : HasDerivAt (fun y : {y : 𝕜 | IsUnit (g y)} ↦ Checked.div (f y) (g y) y.2)
      ((deriv f x * g x - f x * deriv g x) /ₚ (hg.unit ^ 2)) ⟨x, hg⟩ Subtype.val :=
    hdf.hasDerivAt.div hdg.hasDerivAt hg
  rw [logDeriv_eq hq', logDeriv_apply, logDeriv_apply]
  have hq := hf.div₀ hg
  have hsq := hg.pow 2
  have hp : hg.unit ^ 2 = hsq.unit := by
    apply Units.ext
    simp
  rw [hp]
  change (((deriv f x * g x - f x * deriv g x) / g x ^ 2) / (f x / g x)) =
    deriv f x / f x - deriv g x / g x
  field_simp

theorem logDeriv_mul_const {f : 𝕜 → 𝕜'} (x : 𝕜) (a : 𝕜') {ha : IsUnit a} {hf : IsUnit (f x)}
    (hd : DifferentiableAt 𝕜 f x) :
    logDeriv (fun z ↦ f z * a) x id
        (hd.hasDerivAt.mul_const a).existsUnique_hasDerivAt (hf.mul ha) =
      logDeriv f x id hd.existsUnique_hasDerivAt hf := by
  rw [logDeriv_eq (hd.hasDerivAt.mul_const a), logDeriv_apply]
  change deriv f x * a / (f x * a) = deriv f x / f x
  field_simp

theorem logDeriv_const_mul {f : 𝕜 → 𝕜'} (x : 𝕜) (a : 𝕜') {ha : IsUnit a} {hf : IsUnit (f x)}
    (hd : DifferentiableAt 𝕜 f x) :
    logDeriv (fun z ↦ a * f z) x id
        (hd.hasDerivAt.const_mul a).existsUnique_hasDerivAt (ha.mul hf) =
      logDeriv f x id hd.existsUnique_hasDerivAt hf := by
  rw [logDeriv_eq (hd.hasDerivAt.const_mul a), logDeriv_apply]
  change a * deriv f x / (a * f x) = deriv f x / f x
  field_simp

/-- The logarithmic derivative of a finite product is the sum of the logarithmic derivatives. -/
@[to_fun logDeriv_fun_prod]
theorem logDeriv_prod {ι : Type*} {s : Finset ι} {f : ι → 𝕜 → 𝕜'} {x : 𝕜} (hf : ∀ i ∈ s, f i x ≠ 0)
    (hd : ∀ i ∈ s, DifferentiableAt 𝕜 (f i) x) :
    logDeriv (∏ i ∈ s, f i) x id (DifferentiableAt.finsetProd hd).existsUnique_hasDerivAt
        (by rw [Finset.prod_apply, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]; exact hf) =
      ∑ i ∈ s.attach, logDeriv (f i) x id (hd i i.2).existsUnique_hasDerivAt (hf i i.2).isUnit := by
  classical
  have hp : IsUnit (∏ i ∈ s, f i x) :=
    (Finset.prod_ne_zero_iff.mpr hf).isUnit
  rw [logDeriv_eq (HasDerivAt.finsetProd fun i hi ↦ (hd i hi).hasDerivAt)]
  simp only [Finset.prod_apply, smul_eq_mul]
  simp_rw [logDeriv_apply, div_eq_mul_inv₀]
  rw [Finset.sum_mul, ← Finset.sum_attach]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hi := (hf i i.2).isUnit
  have hr : IsUnit (∏ j ∈ s.erase i, f j x) := by
    exact (Finset.prod_ne_zero_iff.mpr fun j hj ↦ hf j (Finset.mem_of_mem_erase hj)).isUnit
  have he := Finset.prod_erase_mul s (fun j ↦ f j x) i.2
  field_simp
  rw [← he]
  ring

/-- The integer-power rule on the common domain of the two logarithmic derivatives. -/
lemma logDeriv_fun_zpow {f : 𝕜 → 𝕜'} {x : 𝕜} {hf : IsUnit (f x)}
    (hdf : DifferentiableAt 𝕜 f x) (n : ℤ)
    {hpow : ∃! d, HasDerivAt
      (fun y : {y : 𝕜 // n < 0 → IsUnit (f y)} ↦ Checked.zpow (f y) n y.2)
      d (⟨x, fun _ ↦ hf⟩ : {y : 𝕜 // n < 0 → IsUnit (f y)}) Subtype.val} :
    logDeriv (fun y : {y : 𝕜 // n < 0 → IsUnit (f y)} ↦ Checked.zpow (f y) n y.2)
        ⟨x, fun _ ↦ hf⟩ Subtype.val hpow (hf.zpow₀ n) =
      n * logDeriv f x id hdf.existsUnique_hasDerivAt hf := by
  have hp := hdf.hasDerivAt.zpow (coord := id) n (fun _ ↦ hf)
  change HasDerivAt _ _ _ Subtype.val at hp
  rw [logDeriv_eq hp, logDeriv_apply]
  by_cases hn : n = 0
  · simp [hn]
  simp only [dite_eq_right hn]
  change (n * (f x) ^ (n - 1) * deriv f x) / (f x) ^ n = n * (deriv f x / f x)
  have hn' := hf.zpow₀ n
  rw [zpow_sub_one₀ hf.ne_zero]
  field_simp

lemma logDeriv_fun_pow {f : 𝕜 → 𝕜'} {x : 𝕜} {hf : IsUnit (f x)}
    (hdf : DifferentiableAt 𝕜 f x) (n : ℕ) :
    logDeriv (fun y ↦ f y ^ n) x id (hdf.hasDerivAt.fun_pow n).existsUnique_hasDerivAt (hf.pow n) =
      n * logDeriv f x id hdf.existsUnique_hasDerivAt hf := by
  rw [logDeriv_eq (coord := id) (hdf.hasDerivAt.fun_pow n), logDeriv_apply]
  change (n * f x ^ (n - 1) * deriv f x) / f x ^ n = n * (deriv f x / f x)
  cases n with
  | zero => simp
  | succ n =>
    simp only [Nat.add_sub_cancel, Nat.cast_succ, pow_succ]
    field_simp

@[simp]
lemma logDeriv_zpow {x : 𝕜} {hx : IsUnit x} (n : ℤ) :
    logDeriv (fun y : {y : 𝕜 // n < 0 → IsUnit y} ↦ Checked.zpow y.val n y.2)
      ⟨x, fun _ ↦ hx⟩ Subtype.val
      ((hasDerivAt_zpow n ⟨x, fun _ ↦ hx⟩).existsUnique_hasDerivAt
        (isOpen_zpow_domain n).isOpenEmbedding_subtypeVal) (hx.zpow₀ n) = (n : 𝕜) / x := by
  rw [logDeriv_eq (hasDerivAt_zpow n ⟨x, fun _ ↦ hx⟩)]
  by_cases hn : n = 0
  · simp [hn]
  simp only [dite_eq_right hn]
  change (n * x ^ (n - 1)) / x ^ n = (n : 𝕜) / x
  have hn' := hx.zpow₀ n
  rw [zpow_sub_one₀ hx.ne_zero]
  field_simp

@[simp]
lemma logDeriv_pow (x : 𝕜) {hx : x ≠ 0} (n : ℕ) :
    logDeriv (· ^ n) x id ((hasDerivAt_id x).fun_pow n).existsUnique_hasDerivAt (hx.isUnit.pow n) =
      (n : 𝕜) / x := by
  have h := logDeriv_fun_pow (f := id) (x := x) (hf := hx.isUnit) differentiableAt_id n
  rw [logDeriv_id, ← mul_div_assoc₀, mul_one] at h
  exact h

@[simp] lemma logDeriv_inv (x : 𝕜ˣ) :
    logDeriv (fun y : 𝕜ˣ ↦ (↑y⁻¹ : 𝕜)) x Units.val
        ((hasDerivAt_inv x).existsUnique_hasDerivAt Units.isOpenEmbedding_val) (x⁻¹).isUnit =
      -1 / (x : 𝕜) := by
  rw [logDeriv_eq (hasDerivAt_inv x)]
  have hi := (x⁻¹).isUnit
  rw [neg_div₀, pow_two, mul_div_cancel_right₀]
  rw [neg_div₀, one_div₀, inv_eq_val_inv_of_eq_val₀ x rfl]

@[to_fun logDeriv_fun_comp]
theorem logDeriv_comp {f : 𝕜' → 𝕜'} {g : 𝕜 → 𝕜'} {x : 𝕜} (hf : DifferentiableAt 𝕜' f (g x))
    (hg : DifferentiableAt 𝕜 g x) {hv : IsUnit (f (g x))} :
    logDeriv (f ∘ g) x id (hf.hasDerivAt.comp x hg.hasDerivAt).existsUnique_hasDerivAt hv =
      logDeriv f (g x) id hf.existsUnique_hasDerivAt hv * deriv g x := by
  rw [logDeriv_eq (hf.hasDerivAt.comp x hg.hasDerivAt), logDeriv_apply]
  exact (div_mul_eq_mul_div₀ _ _ _).symm

@[simp] theorem logDeriv_neg (f : 𝕜 → 𝕜') (x : 𝕜) {hu : f x ≠ 0}
    (hd : DifferentiableAt 𝕜 f x) :
    logDeriv (fun y ↦ -f y) x id hd.hasDerivAt.fun_neg.existsUnique_hasDerivAt hu.isUnit.neg =
      logDeriv f x id hd.existsUnique_hasDerivAt hu.isUnit := by
  rw [logDeriv_eq (coord := id) hd.hasDerivAt.fun_neg, logDeriv_apply]
  exact neg_div_neg_eq₀ _ _

@[simp] theorem logDeriv_comp_neg (f : 𝕜 → 𝕜') (x : 𝕜) {hu : IsUnit (f (-x))}
    (hd : DifferentiableAt 𝕜 f (-x)) :
    logDeriv (fun y ↦ f (-y)) x id
        (hd.hasDerivAt.scomp x (hasDerivAt_neg x)).existsUnique_hasDerivAt hu =
      -logDeriv f (-x) id hd.existsUnique_hasDerivAt hu := by
  rw [logDeriv_eq (f := fun y ↦ f (-y)) (hd.hasDerivAt.scomp x (hasDerivAt_neg x)), logDeriv_apply]
  simp [neg_div₀]

lemma logDeriv_eqOn_iff [IsRCLikeNormedField 𝕜] {f g : 𝕜 → 𝕜'} {s : Set 𝕜}
    (hf : DifferentiableOn 𝕜 f s) (hg : DifferentiableOn 𝕜 g s)
    (hs2 : IsOpen s) (hsc : IsPreconnected s) (hgn : ∀ x ∈ s, g x ≠ 0) (hfn : ∀ x ∈ s, f x ≠ 0) :
    (∀ x : s, logDeriv f x.val id
        ((hf x x.2).differentiableAt (hs2.mem_nhds x.2)).existsUnique_hasDerivAt
          (hfn x x.2).isUnit =
      logDeriv g x.val id
        ((hg x x.2).differentiableAt (hs2.mem_nhds x.2)).existsUnique_hasDerivAt
          (hgn x x.2).isUnit) ↔
      ∃ z : 𝕜', z ≠ 0 ∧ EqOn f (z • g) s := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨t, ht⟩
  · simpa using ⟨1, one_ne_zero⟩
  · constructor
    · intro h
      let q (y : s) : 𝕜' := Checked.div (f y) (g y) (hgn y y.2).isUnit
      let r : s → {y : 𝕜 | IsUnit (g y)} := fun y ↦ ⟨y, (hgn y y.2).isUnit⟩
      have hr : Continuous r := continuous_subtype_val.subtype_mk _
      have hq (y : s) : HasDerivAt q 0 y Subtype.val := by
        have hdf := ((hf y y.2).differentiableAt (hs2.mem_nhds y.2)).hasDerivAt
        have hdg := ((hg y y.2).differentiableAt (hs2.mem_nhds y.2)).hasDerivAt
        have hq' : HasFDerivAt q (ContinuousLinearMap.toSpanSingleton 𝕜
            ((deriv f y * g y - f y * deriv g y) /ₚ ((hgn y y.2).isUnit.unit ^ 2)))
            y Subtype.val :=
          (hdf.div hdg (hgn y y.2).isUnit).hasFDerivAt.comp_tendsto r
            (hr.continuousAt.tendsto.prodMap (tendsto_pure_pure ..))
        have hy := h y
        rw [logDeriv_apply, logDeriv_apply] at hy
        have hfy := (hfn y y.2).isUnit
        have hgy := (hgn y y.2).isUnit
        change deriv f y / f y = deriv g y / g y at hy
        have hz : deriv f y * g y - f y * deriv g y = 0 :=
          sub_eq_zero.mpr (div_eq_div_iff.mp hy |>.trans (mul_comm _ _))
        simpa only [hz, divp, zero_mul, ContinuousLinearMap.toSpanSingleton_apply,
          one_smul] using hq'.hasDerivAt
      let := Subtype.preconnectedSpace hsc
      let := IsRCLikeNormedField.rclike 𝕜
      have hcoord := hs2.isOpenEmbedding_subtypeVal
      obtain ⟨a, ha⟩ := isOpen_univ.exists_is_const_of_deriv_eq_zero
        (s := (Set.univ : Set s)) isPreconnected_univ
        (fun y _ ↦ (hq y).hasFDerivAt.hasFDerivWithinAt.differentiableWithinAt)
        (fun y _ ↦ (hq y).deriv hcoord) hcoord
      have hta : q ⟨t, ht⟩ = a := ha ⟨t, ht⟩ (Set.mem_univ _)
      have hat : IsUnit (q ⟨t, ht⟩) := (hfn t ht).isUnit.div₀ (hgn t ht).isUnit
      refine ⟨a, hta ▸ hat.ne_zero, fun y hy ↦ ?_⟩
      have hgy := (hgn y hy).isUnit
      exact div_eq_iff.mp (ha ⟨y, hy⟩ (Set.mem_univ _))
    · rintro ⟨z, hz0, hz⟩ x
      have hz' : f =ᶠ[𝓝 (x : 𝕜)] (fun y ↦ z * g y) :=
        mem_of_superset (hs2.mem_nhds x.2) fun _ hy ↦ hz hy
      have hdg := (hg x x.2).differentiableAt (hs2.mem_nhds x.2)
      exact (logDeriv_congr hz').trans
        (logDeriv_const_mul (x : 𝕜) z (ha := hz0.isUnit) (hf := (hgn x x.2).isUnit) hdg)


/-- At a simple zero of an analytic function, the logarithmic residue
`(w - x) * logDeriv f w` tends to 1. -/
theorem AnalyticAt.tendsto_mul_logDeriv_simple_zero [CompleteSpace 𝕜]
    {f : 𝕜 → 𝕜} {x : 𝕜}
    (hf : AnalyticAt 𝕜 f x) (hfx : f x = 0) (hf' : deriv f x ≠ 0) :
    Tendsto (fun w : {w : 𝕜 // DifferentiableAt 𝕜 f w ∧ IsUnit (f w)} ↦
      (w.val - x) * logDeriv f w.val id w.2.1.existsUnique_hasDerivAt w.2.2)
      (comap Subtype.val (𝓝 x)) (𝓝 1) := by
  let D := {w : 𝕜 // DifferentiableAt 𝕜 f w ∧ IsUnit (f w)}
  have hx (w : D) : x ≠ w.val := fun h ↦ w.2.2.ne_zero (h ▸ hfx)
  let q : D → ({x}ᶜ : Set 𝕜) := fun w ↦ ⟨w.val, (hx w).symm⟩
  have hq : Tendsto q (comap Subtype.val (𝓝 x)) (comap Subtype.val (𝓝 x)) :=
    tendsto_comap_iff.2 tendsto_comap
  have hs := hf.differentiableAt.hasDerivAt.tendsto_slope.comp hq
  have hv (w : D) : IsUnit (slope f x w.val (hx w)) := by
    have hw := (sub_ne_zero.mpr (hx w).symm).isUnit
    rw [slope_def_field, hfx, sub_zero]
    exact w.2.2.div₀ hw
  have hd := hf.deriv.continuousAt.tendsto.comp
    (tendsto_comap : Tendsto (Subtype.val : D → 𝕜) (comap Subtype.val (𝓝 x)) (𝓝 x))
  have hp := hd.div₀ (h₀ := hv) (hb := hf'.isUnit) hs
  rw [div_self] at hp
  refine hp.congr fun w ↦ ?_
  rw [logDeriv_apply]
  have hw := (sub_ne_zero.mpr (hx w).symm).isUnit
  have hfw := w.2.2
  change deriv f w.val / slope f x w.val (hx w) = (w.val - x) * (deriv f w.val / f w.val)
  simp only [slope_def_field, hfx, sub_zero, div_div_eq_mul_div₀]
  rw [mul_comm, mul_div_assoc₀]
