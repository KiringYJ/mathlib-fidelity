/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.MellinTransform

/-!
# Abstract functional equations for Mellin transforms

This file formalises a general version of an argument used to prove functional equations for
zeta and L-functions.

### FE-pairs

We define a *weak FE-pair* to be a pair of functions `f, g` on the reals which are locally
integrable on `(0, ∞)`, have the form "constant" + "rapidly decaying term" at `∞`, and satisfy a
functional equation of the form

`f (1 / x) = ε * x ^ k * g x`

for some constants `k ∈ ℝ` and `ε ∈ ℂ`. (Modular forms give rise to natural examples
with `k` being the weight and `ε` the global root number; hence the notation.) We could arrange
`ε = 1` by scaling `g`; but this is inconvenient in applications so we set things up more generally.

A *strong FE-pair* is a weak FE-pair where the constant terms of `f` and `g` at `∞` are both 0.

The main property of these pairs is the following: if `f`, `g` are a weak FE-pair, with constant
terms `f₀` and `g₀` at `∞`, then the Mellin transforms `Λ` and `Λ'` of `f - f₀` and `g - g₀`
respectively both have meromorphic continuation and satisfy a functional equation of the form

`Λ (k - s) = ε * Λ' s`.

The poles (and their residues) are explicitly given in terms of `f₀` and `g₀`; in particular, if
`(f, g)` are a strong FE-pair, then the Mellin transforms of `f` and `g` are entire functions.

### Main definitions and results

See the sections *Main theorems on weak FE-pairs* and
*Main theorems on strong FE-pairs* below.

* Weak FE pairs:
  - `WeakFEPair.Λ₀`: an entire function of `s : ℂ`
  - `WeakFEPair.Λ`: the continued transform on its exact regular domain
  - `WeakFEPair.differentiable_Λ₀`: `Λ₀` is entire
  - `WeakFEPair.differentiableAt_Λ`: `Λ` is differentiable on its regular domain
  - `WeakFEPair.hasMellin`: for `k < re s`, `Λ s` equals the Mellin transform of `f - f₀`
  - `WeakFEPair.functional_equation₀`: the functional equation for `Λ₀`
  - `WeakFEPair.functional_equation`: the functional equation for `Λ`
  - `WeakFEPair.Λ_residue_k`: computation of the residue at `k`
  - `WeakFEPair.Λ_residue_zero`: computation of the residue at `0`.

* Strong FE pairs:
  - `IsStrongFEPair.differentiable_Λ`: `Λ` is entire
  - `IsStrongFEPair.hasMellin`: `Λ` is everywhere equal to the Mellin transform of `f`
-/

@[expose] public section


/- TODO: Consider extending the results to allow functional equations of the form
`f (N / x) = (const) • x ^ k • g x` for a real parameter `0 < N`. This could be done either by
generalising the existing proofs in situ, or by a separate wrapper `FEPairWithLevel` which just
applies a scaling factor to `f` and `g` to reduce to the `N = 1` case.
-/

noncomputable section

open Real Complex Filter Asymptotics Set MeasureTheory

open scoped Topology

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]

/-!
## Definitions and symmetry
-/

/-- A structure designed to hold the hypotheses for the Mellin-functional-equation argument
(most general version: rapid decay at `∞` up to constant terms) -/
structure WeakFEPair where
  /-- The functions whose Mellin transform we study -/
  (f g : ℝ → E)
  /-- Weight (exponent in the functional equation) -/
  (k : ℝ)
  /-- Root number -/
  (ε : ℂ)
  /-- Constant terms at `∞` -/
  (f₀ g₀ : E)
  (hf_int : LocallyIntegrableOn f (Ioi 0))
  (hg_int : LocallyIntegrableOn g (Ioi 0))
  (hk : 0 < k)
  (hε : ε ≠ 0)
  (h_feq : ∀ (x : ℝ) (hx : 0 < x),
    f (Checked.div 1 x hx.ne'.isUnit) = (ε * ↑(x ^ k)) • g x)
  (hf_top (r : ℝ) : (f · - f₀) =O[atTop] (· ^ r))
  (hg_top (r : ℝ) : (g · - g₀) =O[atTop] (· ^ r))

variable {E}

/-- A *strong FE-pair* is a weak FE-pair in which `f₀` and `g₀` are zero. -/
structure IsStrongFEPair (P : WeakFEPair E) : Prop where
  hf₀ : P.f₀ = 0
  hg₀ : P.g₀ = 0

section symmetry

/-- Reformulated functional equation with `f` and `g` interchanged. -/
lemma WeakFEPair.h_feq' (P : WeakFEPair E) (x : ℝ) (hx : 0 < x) :
    P.g (1 / x) = ((Checked.inv P.ε P.hε.isUnit) * ↑(x ^ P.k)) • P.f x := by
  have hpos : 0 < 1 / x := one_div_pos.mpr hx
  have h := P.h_feq (1 / x) hpos
  rw [one_div_one_div₀ (ha := hx.ne'.isUnit)] at h
  rw [h, ← mul_smul]
  have hcoef : (Checked.inv P.ε P.hε.isUnit * ↑(x ^ P.k)) *
      (P.ε * ↑((1 / x) ^ P.k)) = 1 := by
    rw [one_div₀, inv_rpow hx.le, ofReal_inv]
    field [P.hε, (rpow_pos_of_pos hx _).ne']
  rw [hcoef, one_smul]

/-- The hypotheses are symmetric in `f` and `g`, with the constant `ε` replaced by `ε⁻¹`. -/
@[simps]
def WeakFEPair.symm (P : WeakFEPair E) : WeakFEPair E where
  f := P.g
  g := P.f
  k := P.k
  ε := (Checked.inv P.ε P.hε.isUnit)
  f₀ := P.g₀
  g₀ := P.f₀
  hf_int := P.hg_int
  hg_int := P.hf_int
  hf_top := P.hg_top
  hg_top := P.hf_top
  hε := inv_ne_zero (ha := P.hε.isUnit)
  hk := P.hk
  h_feq  := P.h_feq'

@[simp] lemma isStrongFEPair_symm {P : WeakFEPair E} :
    IsStrongFEPair P.symm ↔ IsStrongFEPair P where
  mp h := ⟨h.hg₀, h.hf₀⟩
  mpr h := ⟨h.hg₀, h.hf₀⟩

lemma IsStrongFEPair.symm {P : WeakFEPair E} (hP : IsStrongFEPair P) :
    IsStrongFEPair P.symm := isStrongFEPair_symm.2 hP

end symmetry

namespace WeakFEPair

variable (P : WeakFEPair E)

/-!
## Auxiliary results I: lemmas on asymptotics
-/

/-- As `x → 0`, we have `f x = x ^ (-P.k) • constant` up to a rapidly decaying error. -/
lemma hf_zero (r : ℝ) :
    (fun x ↦ P.f x - (P.ε * ↑(x ^ (-P.k))) • P.g₀) =O[𝓝[>] 0] (· ^ r) := by
  have := (P.hg_top (-(r + P.k))).comp_tendsto tendsto_inv_nhdsGT_zero
  simp_rw [IsBigO, IsBigOWith, eventually_comap, eventually_nhdsWithin_iff] at this
  simp_rw [IsBigO, IsBigOWith, eventually_nhdsWithin_iff]
  obtain ⟨C, hC⟩ := this
  use ‖P.ε‖ * C
  filter_upwards [hC] with x hC' (hx : 0 < x)
  have h_nv2 : ↑(x ^ P.k) ≠ (0 : ℂ) := ofReal_ne_zero.mpr (rpow_pos_of_pos hx _).ne'
  have h_nv : (Checked.inv P.ε P.hε.isUnit) * ↑(x ^ P.k) ≠ 0 := mul_ne_zero P.symm.hε h_nv2
  specialize hC' hx ⟨x, hx.ne'.isUnit⟩ rfl
  simp_rw [Function.comp_apply, ← one_div₀, P.h_feq' _ hx] at hC'
  rw [← ((mul_inv_cancel₀ (ha := h_nv.isUnit)).symm ▸ one_smul ℂ P.g₀ :),
    mul_smul _ _ P.g₀, ← smul_sub, norm_smul] at hC'
  have hpow : IsUnit (x ^ P.k) := (rpow_pos_of_pos hx _).ne'.isUnit
  have hcoef : Checked.inv ((Checked.inv P.ε P.hε.isUnit) * ↑(x ^ P.k)) h_nv.isUnit =
      P.ε * ↑(x ^ (-P.k)) := by
    simp only [mul_inv_rev₀, inv_inv₀, rpow_neg hx.le P.k (hxy := hpow), ofReal_inv, mul_comm]
  have hscale : (1 / x) ^ (-(r + P.k)) = x ^ (r + P.k) := by
    rw [one_div₀, ← rpow_neg_eq_inv_rpow x _ (hx := hx.ne'.isUnit), neg_neg]
  have hε : ‖P.ε‖ ≠ 0 := norm_ne_zero_iff.mpr P.hε
  have hnorm : ‖(Checked.inv P.ε P.hε.isUnit) * ↑(x ^ P.k)‖ =
      Checked.inv ‖P.ε‖ hε.isUnit * x ^ P.k := by
    rw [norm_mul, norm_inv, norm_real, norm_of_nonneg (rpow_pos_of_pos hx _).le]
  rw [hcoef, hscale, hnorm, norm_of_nonneg (rpow_pos_of_pos hx (r + P.k)).le, rpow_add hx] at hC'
  rw [norm_of_nonneg (rpow_pos_of_pos hx r).le]
  have hden : 0 < Checked.inv ‖P.ε‖ hε.isUnit * x ^ P.k :=
    mul_pos (inv_pos.mpr (norm_pos_iff.mpr P.hε)) (rpow_pos_of_pos hx _)
  convert (le_div_iff₀' hden).mpr hC' using 1
  field [hε, hpow.ne_zero]

/-- Power asymptotic for `f - f₀` as `x → 0`. -/
lemma hf_zero' : (fun x : ℝ ↦ P.f x - P.f₀) =O[𝓝[>] 0] (· ^ (-P.k)) := by
  simp_rw [← fun x ↦ sub_add_sub_cancel (P.f x) ((P.ε * ↑(x ^ (-P.k))) • P.g₀) P.f₀]
  refine (P.hf_zero _).add (IsBigO.sub ?_ ?_)
  · rw [← isBigO_norm_norm]
    simp_rw [mul_smul, norm_smul, mul_comm _ ‖P.g₀‖, ← mul_assoc, norm_real]
    apply (isBigO_refl _ _).const_mul_left
  · refine IsBigO.of_bound ‖P.f₀‖ (eventually_nhdsWithin_iff.mpr ?_)
    filter_upwards [eventually_le_nhds zero_lt_one] with x hx' (hx : 0 < x)
    apply le_mul_of_one_le_right (norm_nonneg _)
    rw [norm_of_nonneg (rpow_pos_of_pos hx _).le, rpow_neg hx.le]
    exact (one_le_inv₀ (rpow_pos_of_pos hx _)).2 (rpow_le_one hx.le hx' P.hk.le)

private theorem functional_equation_aux (s : ℂ) :
    mellin (fun t : Ioi (0 : ℝ) ↦ P.f t.val) (P.k - s) =
      P.ε • mellin (fun t : Ioi (0 : ℝ) ↦ P.g t.val) s := by
  -- Substitute inversion on the actual positive integration domain.
  have step1 := mellin_comp_inv (fun t : Ioi (0 : ℝ) ↦ P.g t.val) (-s)
  simp only [neg_neg] at step1
  -- introduce a power of `t` to match the hypothesis `P.h_feq`
  have step2 := mellin_cpow_smul
    (fun t : Ioi (0 : ℝ) ↦ P.g (Checked.inv t.val t.property.ne'.isUnit))
    (P.k - s) (-P.k)
  rw [← sub_eq_add_neg, sub_right_comm, sub_self, zero_sub, step1] at step2
  -- put in the constant `P.ε`
  have step3 := mellin_const_smul (fun t : Ioi (0 : ℝ) ↦
    (t.val : ℂ) ^ (-P.k : ℂ) • P.g (Checked.inv t.val t.property.ne'.isUnit)) (P.k - s) P.ε
  rw [step2] at step3
  rw [← step3]
  -- now the integrand matches `P.h_feq'` on `Ioi 0`, so we can apply `setIntegral_congr_fun`
  apply integral_congr_ae
  filter_upwards [] with t
  have ht : 0 < t.val := t.property
  simp_rw [← one_div₀, P.h_feq' t.val ht, ← mul_smul]
  -- some simple `cpow` arithmetic to finish
  have ht0 : (t.val : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  have hpow : (t.val : ℂ) ^ (P.k : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (.inl ht0)
  have hε : IsUnit P.ε := P.hε.isUnit
  have hunit : IsUnit ((t.val : ℂ) ^ (P.k : ℂ)) := hpow.isUnit
  rw [cpow_neg (t.val : ℂ) (P.k : ℂ) (hxy := hunit), ofReal_cpow (le_of_lt ht)]
  match_scalars
  symm
  calc
    _ = (t.val : ℂ) ^ ((P.k : ℂ) - s - 1) * (P.ε * P.ε⁻¹) *
        (((t.val : ℂ) ^ (P.k : ℂ))⁻¹ * (t.val : ℂ) ^ (P.k : ℂ)) := by ac_rfl
    _ = _ := by simp only [mul_inv_cancel₀, inv_mul_cancel₀, mul_one]

end WeakFEPair

namespace IsStrongFEPair

variable {P : WeakFEPair E} (hP : IsStrongFEPair P)
include hP

/-- As `x → ∞`, `f x` decays faster than any power of `x`. -/
lemma hf_top (r : ℝ) : P.f =O[atTop] (· ^ r) := by
  simpa [hP.hf₀] using P.hf_top r

/-- As `x → 0`, `f x` decays faster than any power of `x`. -/
lemma hf_zero (r : ℝ) : P.f =O[𝓝[>] 0] (· ^ r) := by
  simpa using (hP.hg₀ ▸ P.hf_zero r :)

/-- The Mellin transform of `P.f` is globally convergent. Private since it is superseded by
`IsStrongFEPair.hasMellin` below, which also identifies its Mellin transform as `P.Λ`. -/
private theorem mellinConvergent (s : ℂ) :
    MellinConvergent (fun t : Ioi (0 : ℝ) ↦ P.f t.val) s :=
  let ⟨_, ht⟩ := exists_gt s.re
  let ⟨_, hu⟩ := exists_lt s.re
  mellinConvergent_of_isBigO_rpow P.hf_int (hP.hf_top _) ht (hP.hf_zero _) hu

/-- The Mellin transform of `P.f` is globally convergent. Private since it is superseded by
`IsStrongFEPair.differentiable_Λ` below. -/
private theorem differentiable_mellin :
    Differentiable ℂ (mellin (fun t : Ioi (0 : ℝ) ↦ P.f t.val)) := fun s ↦
  let ⟨_, ht⟩ := exists_gt s.re
  let ⟨_, hu⟩ := exists_lt s.re
  mellin_differentiableAt_of_isBigO_rpow P.hf_int (hP.hf_top _) ht (hP.hf_zero _) hu

end IsStrongFEPair

namespace WeakFEPair

variable (P : WeakFEPair E)

/-!
## Auxiliary results II: building a strong FE-pair from a weak FE-pair
-/

/-- Piecewise modified version of `f` with optimal asymptotics. We deliberately choose intervals
which don't quite join up, so the function is `0` at `x = 1`, in order to maintain symmetry;
there is no "good" choice of value at `1`. -/
def f_modif : ℝ → E :=
  (Ioi 1).indicator (fun x ↦ P.f x - P.f₀) +
  (Ioo 0 1).indicator (fun x ↦ P.f x - (P.ε * ↑(x ^ (-P.k))) • P.g₀)

/-- Piecewise modified version of `g` with optimal asymptotics. -/
def g_modif : ℝ → E :=
  (Ioi 1).indicator (fun x ↦ P.g x - P.g₀) +
  (Ioo 0 1).indicator (fun x ↦ P.g x - ((Checked.inv P.ε P.hε.isUnit) * ↑(x ^ (-P.k))) • P.f₀)

lemma hf_modif_int :
    LocallyIntegrableOn P.f_modif (Ioi 0) := by
  have : LocallyIntegrableOn (fun x : ℝ ↦ (P.ε * ↑(x ^ (-P.k))) • P.g₀) (Ioi 0) := by
    refine ContinuousOn.locallyIntegrableOn ?_ measurableSet_Ioi
    refine continuousOn_of_forall_continuousAt (fun x (hx : 0 < x) ↦ ?_)
    have : x ≠ 0 ∨ 0 ≤ -P.k := Or.inl hx.ne'
    fun_prop
  refine LocallyIntegrableOn.add (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · obtain ⟨s, hs, hs'⟩ := P.hf_int.sub (locallyIntegrableOn_const _) x hx
    exact ⟨s, hs, hs'.indicator measurableSet_Ioi⟩
  · obtain ⟨s, hs, hs'⟩ := P.hf_int.sub this x hx
    exact ⟨s, hs, hs'.indicator measurableSet_Ioo⟩

lemma hf_modif_FE (x : ℝ) (hx : 0 < x) :
    P.f_modif (1 / x) = (P.ε * ↑(x ^ P.k)) • P.g_modif x := by
  rcases lt_trichotomy 1 x with hx' | rfl | hx'
  · have : 1 / x < 1 := by rwa [one_div_lt hx one_pos, div_one₀]
    rw [f_modif, Pi.add_apply, indicator_of_notMem (notMem_Ioi.mpr this.le),
      zero_add, indicator_of_mem (mem_Ioo.mpr ⟨div_pos one_pos hx, this⟩), g_modif, Pi.add_apply,
      indicator_of_mem (mem_Ioi.mpr hx'), indicator_of_notMem
      (notMem_Ioo_of_ge hx'.le), add_zero, P.h_feq _ hx, smul_sub]
    have hp : IsUnit (x ^ P.k) := (rpow_pos_of_pos hx P.k).ne'.isUnit
    simp only [one_div₀, inv_rpow hx.le, rpow_neg hx.le P.k (hxy := hp), inv_inv₀]
  · simp [f_modif, g_modif]
  · have : 1 < 1 / x := by rwa [lt_one_div one_pos hx, div_one₀]
    rw [f_modif, Pi.add_apply, indicator_of_mem (mem_Ioi.mpr this),
      indicator_of_notMem (notMem_Ioo_of_ge this.le), g_modif, Pi.add_apply,
      indicator_of_notMem (notMem_Ioi.mpr hx'.le),
      indicator_of_mem (mem_Ioo.mpr ⟨hx, hx'⟩), P.h_feq _ hx]
    have hε := P.hε.isUnit
    have hp : IsUnit (x ^ P.k) := (rpow_pos_of_pos hx P.k).ne'.isUnit
    have hpc : IsUnit ((x ^ P.k : ℝ) : ℂ) := (ofReal_ne_zero.mpr hp.ne_zero).isUnit
    have hfactor : (P.ε * ↑(x ^ P.k)) * (P.ε⁻¹ * (↑(x ^ P.k) : ℂ)⁻¹) = 1 := by
      calc
        _ = (P.ε * P.ε⁻¹) * ((↑(x ^ P.k) : ℂ) * (↑(x ^ P.k) : ℂ)⁻¹) := by ac_rfl
        _ = 1 := by simp only [mul_inv_cancel₀, mul_one]
    simp only [add_zero, zero_add, smul_sub, smul_smul, rpow_neg hx.le P.k (hxy := hp),
      ofReal_inv, hfactor, one_smul]

lemma hf_modif_top (r : ℝ) :
    (fun x ↦ P.f_modif x - 0) =O[atTop] fun x ↦ x ^ r := by
  refine (P.hf_top r).congr' ?_ .rfl
  filter_upwards [eventually_gt_atTop 1] with x hx
  simp [f_modif, mem_Ioi.mpr hx, notMem_Ioo_of_ge hx.le]

/-- Given a weak FE-pair `(f, g)`, modify it into a strong FE-pair by subtracting suitable
correction terms from `f` and `g`.

(See `WeakFEPair.isStrongFEPair_toStrongFEPair` for the proof that this is actually a strong
FE-pair.) -/
def toStrongFEPair : WeakFEPair E where
  f := P.f_modif
  g := P.symm.f_modif
  k := P.k
  ε := P.ε
  f₀ := 0
  g₀ := 0
  hf_int := P.hf_modif_int
  hg_int := P.symm.hf_modif_int
  h_feq := P.hf_modif_FE
  hε := P.hε
  hk := P.hk
  hf_top := P.hf_modif_top
  hg_top := P.symm.hf_modif_top

lemma isStrongFEPair_toStrongFEPair : IsStrongFEPair P.toStrongFEPair where
  hf₀ := rfl
  hg₀ := rfl

/-- Alternative form for the difference between `f - f₀` and its modified term. -/
lemma f_modif_aux1 : EqOn (fun x ↦ P.f_modif x - P.f x + P.f₀)
    ((Ioo 0 1).indicator (fun x : ℝ ↦ P.f₀ - (P.ε * ↑(x ^ (-P.k))) • P.g₀)
    + ({1} : Set ℝ).indicator (fun _ ↦ P.f₀ - P.f 1)) (Ioi 0) := by
  intro x (hx : 0 < x)
  simp_rw [f_modif, Pi.add_apply]
  rcases lt_trichotomy x 1 with hx' | rfl | hx'
  · simp_rw [indicator_of_notMem (notMem_Ioi.mpr hx'.le), indicator_of_mem (mem_Ioo.mpr ⟨hx, hx'⟩),
      indicator_of_notMem (mem_singleton_iff.not.mpr hx'.ne)]
    abel
  · simp [add_comm, sub_eq_add_neg]
  · simp_rw [indicator_of_mem (mem_Ioi.mpr hx'), indicator_of_notMem (notMem_Ioo_of_ge hx'.le),
      indicator_of_notMem (mem_singleton_iff.not.mpr hx'.ne')]
    abel

/-- An entire function which differs from the Mellin transform of `f - f₀`, where defined, by a
correction term of the form `A / s + B / (k - s)`. -/
def Λ₀ : ℂ → E := mellin (fun t : Ioi (0 : ℝ) ↦ P.f_modif t.val)

open Classical in
/-- The continued Mellin transform on its exact regular domain. A vanishing residue contributes
zero without forming a reciprocal at the corresponding removable singularity. -/
def Λ (s : {s : ℂ // (s ≠ 0 ∨ P.f₀ = 0) ∧ (s ≠ P.k ∨ P.ε • P.g₀ = 0)}) : E :=
  P.Λ₀ s.val -
    (if hf : P.f₀ = 0 then 0 else
      Checked.inv s.val (s.property.1.resolve_right hf).isUnit • P.f₀) +
    (if hg : P.ε • P.g₀ = 0 then 0 else
      Checked.inv (s.val - P.k)
        (sub_ne_zero.mpr (s.property.2.resolve_right hg)).isUnit • (P.ε • P.g₀))

open Classical in
lemma Λ₀_eq (s : {s : ℂ // (s ≠ 0 ∨ P.f₀ = 0) ∧
    (s ≠ P.k ∨ P.ε • P.g₀ = 0)}) :
    P.Λ₀ s.val = P.Λ s +
      (if hf : P.f₀ = 0 then 0 else
        Checked.inv s.val (s.property.1.resolve_right hf).isUnit • P.f₀) -
      (if hg : P.ε • P.g₀ = 0 then 0 else
        Checked.inv (s.val - P.k)
          (sub_ne_zero.mpr (s.property.2.resolve_right hg)).isUnit • (P.ε • P.g₀)) := by
  unfold Λ
  abel

open Classical in
lemma symm_Λ₀_eq (s : {s : ℂ // (s ≠ 0 ∨ P.symm.f₀ = 0) ∧
    (s ≠ P.symm.k ∨ P.symm.ε • P.symm.g₀ = 0)}) :
    P.symm.Λ₀ s.val = P.symm.Λ s +
      (if hf : P.g₀ = 0 then 0 else
        Checked.inv s.val (s.property.1.resolve_right hf).isUnit • P.g₀) -
      (if hg : (Checked.inv P.ε P.hε.isUnit) • P.f₀ = 0 then 0 else
        Checked.inv (s.val - P.k)
          (sub_ne_zero.mpr (s.property.2.resolve_right hg)).isUnit •
            ((Checked.inv P.ε P.hε.isUnit) • P.f₀)) :=
  P.symm.Λ₀_eq s

/-- Away from both distinguished points, the continued transform has its usual principal-part
formula, irrespective of which of the residues vanish. -/
lemma Λ_eq_of_ne (s : {s : ℂ // (s ≠ 0 ∨ P.f₀ = 0) ∧ (s ≠ P.k ∨ P.ε • P.g₀ = 0)})
    (hs : s.val ≠ 0) (hsk : s.val ≠ P.k) :
    P.Λ s = P.Λ₀ s.val - Checked.inv s.val hs.isUnit • P.f₀ +
      Checked.inv (s.val - P.k) (sub_ne_zero.mpr hsk).isUnit • (P.ε • P.g₀) := by
  by_cases hf : P.f₀ = 0 <;> by_cases hg : P.ε • P.g₀ = 0 <;> simp [Λ, hf, hg]

/-- Compute the Mellin transform of the modifying term used to kill off the constants at
`0` and `∞`. -/
lemma f_modif_aux2 [CompleteSpace E]
    {s : {s : ℂ // (s ≠ 0 ∨ P.f₀ = 0) ∧ (s ≠ P.k ∨ P.ε • P.g₀ = 0)}}
    (hs : P.k < re s.val) :
    mellin (fun x : Ioi (0 : ℝ) ↦ P.f_modif x.val - P.f x.val + P.f₀) s.val =
      P.Λ₀ s.val - P.Λ s := by
  have hs0 : s.val ≠ 0 := by
    intro he
    simpa [he] using P.hk.trans hs
  have hsk : s.val ≠ P.k := by
    intro he
    simp [he] at hs
  rw [P.Λ_eq_of_ne s hs0 hsk,
    mellin_eq_integral (fun x : ℝ ↦ P.f_modif x - P.f x + P.f₀) s.val]
  have h_re1 : -1 < re (s.val - 1) := by simpa using P.hk.trans hs
  have h_re2 : -1 < re (s.val - P.k - 1) := by simpa using hs
  calc
  _ = ∫ (x : ℝ) in Ioi 0, (x : ℂ) ^ (s.val - 1) •
      ((Ioo 0 1).indicator (fun t : ℝ ↦ P.f₀ - (P.ε * ↑(t ^ (-P.k))) • P.g₀) x
      + ({1} : Set ℝ).indicator (fun _ ↦ P.f₀ - P.f 1) x) :=
    setIntegral_congr_fun measurableSet_Ioi (fun x hx ↦ by simp [f_modif_aux1 P hx])
  _ = ∫ (x : ℝ) in Ioi 0, (x : ℂ) ^ (s.val - 1) • ((Ioo 0 1).indicator
      (fun t : ℝ ↦ P.f₀ - (P.ε * ↑(t ^ (-P.k))) • P.g₀) x) := by
    refine setIntegral_congr_ae measurableSet_Ioi (eventually_of_mem (U := {1}ᶜ)
        (compl_mem_ae_iff.mpr (subsingleton_singleton.measure_zero _)) (fun x hx _ ↦ ?_))
    rw [indicator_of_notMem hx, add_zero]
  _ = ∫ (x : ℝ) in Ioc 0 1, (x : ℂ) ^ (s.val - 1) • (P.f₀ - (P.ε * ↑(x ^ (-P.k))) • P.g₀) := by
    simp_rw [← indicator_smul, setIntegral_indicator measurableSet_Ioo,
      inter_eq_right.mpr Ioo_subset_Ioi_self, integral_Ioc_eq_integral_Ioo]
  _ = ∫ x : ℝ in Ioc 0 1, ((x : ℂ) ^ (s.val - 1) • P.f₀ -
        P.ε • (x : ℂ) ^ (s.val - P.k - 1) • P.g₀) := by
    refine setIntegral_congr_fun measurableSet_Ioc (fun x ⟨hx, _⟩ ↦ ?_)
    rw [ofReal_cpow hx.le, ofReal_neg, smul_sub, ← mul_smul, mul_comm, mul_assoc, mul_smul,
      mul_comm, ← cpow_add _ _ (ofReal_ne_zero.mpr hx.ne'), ← sub_eq_add_neg, sub_right_comm]
  _ = (∫ (x : ℝ) in Ioc 0 1, (x : ℂ) ^ (s.val - 1)) • P.f₀
        - P.ε • (∫ (x : ℝ) in Ioc 0 1, (x : ℂ) ^ (s.val - P.k - 1)) • P.g₀ := by
    rw [integral_sub, integral_smul, integral_smul_const, integral_smul_const]
    · apply Integrable.smul_const
      rw [← IntegrableOn, ← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
      exact intervalIntegral.intervalIntegrable_cpow' h_re1
    · refine (Integrable.smul_const ?_ _).smul _
      rw [← IntegrableOn, ← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
      exact intervalIntegral.intervalIntegrable_cpow' h_re2
  _ = _ := by
    simp_rw [← intervalIntegral.integral_of_le zero_le_one]
    simp [integral_cpow (.inl h_re1), integral_cpow (.inl h_re2), hs0,
      sub_ne_zero.mpr hsk, div_eq_mul_inv₀]
    module
/-!
## Main theorems on weak FE-pairs
-/

theorem differentiable_Λ₀ : Differentiable ℂ P.Λ₀ :=
  P.isStrongFEPair_toStrongFEPair.differentiable_mellin

theorem differentiableAt_Λ
    (s : {s : ℂ // (s ≠ 0 ∨ P.f₀ = 0) ∧ (s ≠ P.k ∨ P.ε • P.g₀ = 0)}) :
    DifferentiableAt ℂ P.Λ s Subtype.val := by
  classical
  let D := {s : ℂ // (s ≠ 0 ∨ P.f₀ = 0) ∧ (s ≠ P.k ∨ P.ε • P.g₀ = 0)}
  have hprincipal (a : ℂ) (c : E) (h : ∀ t : D, t.val ≠ a ∨ c = 0) :
      DifferentiableAt ℂ (fun t : D ↦ if hc : c = 0 then 0 else
        Checked.inv (t.val - a) (sub_ne_zero.mpr ((h t).resolve_right hc)).isUnit • c)
        s Subtype.val := by
    by_cases hc : c = 0
    · simp only [dite_eq_left hc]
      exact ⟨0, .of_isLittleOTVS <| (Asymptotics.IsLittleOTVS.zero _ _).congr_left
        fun _ ↦ by simp⟩
    · simp only [dite_eq_right hc]
      let u : D → ℂˣ := fun t ↦
        (sub_ne_zero.mpr ((h t).resolve_right hc)).isUnit.unit
      have hcoord : HasFDerivAt (fun t : D ↦ t.val - a)
          (ContinuousLinearMap.id ℂ ℂ) s Subtype.val := by
        refine .of_isLittleOTVS <| (Asymptotics.IsLittleOTVS.zero _ _).congr_left ?_
        intro p
        simp only [ContinuousLinearMap.id_apply, Pi.zero_apply]
        abel
      have hinv := (hasFDerivAt_inv' (𝕜 := ℂ) (u s)).comp s
        (f := u) (by simpa only [u, Function.comp_def, IsUnit.unit_spec] using hcoord)
        continuousAt_subtype_val Units.isOpenEmbedding_val.isEmbedding
      have hterm := ((ContinuousLinearMap.id ℂ ℂ).smulRight c).hasFDerivAt.comp s hinv
        continuousAt_subtype_val Topology.IsEmbedding.id
      simpa only [u, Checked.inv, Function.comp_def, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.id_apply] using hterm.differentiableAt
  obtain ⟨f', hf'⟩ := P.differentiable_Λ₀ s.val
  have h0 : DifferentiableAt ℂ (fun t : D ↦ P.Λ₀ t.val) s Subtype.val := by
    refine ⟨f', ?_⟩
    change HasFDerivAtFilter (fun t : D ↦ P.Λ₀ t.val) f' (𝓝 s ×ˢ pure s) (fun t ↦ t.val)
    simpa only [Function.comp_def, id_eq] using
      hf'.comp_tendsto Subtype.val
        (continuousAt_subtype_val.tendsto.prodMap (tendsto_pure_pure ..))
  have hfirst : DifferentiableAt ℂ (fun t : D ↦ if hf : P.f₀ = 0 then 0 else
      Checked.inv t.val (t.property.1.resolve_right hf).isUnit • P.f₀) s Subtype.val := by
    simpa only [sub_zero] using hprincipal 0 P.f₀ (fun t ↦ t.property.1)
  exact (h0.sub hfirst).add (hprincipal P.k (P.ε • P.g₀) (fun t ↦ t.property.2))

/-- Relation between `Λ s` and the Mellin transform of `f - f₀`, where the latter is defined.
(Compare `IsStrongFEPair.hasMellin` for a version without assumptions on `s.re` assuming the
FE-pair is strong.) -/
theorem hasMellin [CompleteSpace E]
    {s : {s : ℂ // (s ≠ 0 ∨ P.f₀ = 0) ∧ (s ≠ P.k ∨ P.ε • P.g₀ = 0)}}
    (hs : P.k < s.val.re) :
    HasMellin (fun t : Ioi (0 : ℝ) ↦ P.f t.val - P.f₀) s.val (P.Λ s) := by
  have hc1 : MellinConvergent (fun t : Ioi (0 : ℝ) ↦ P.f t.val - P.f₀) s.val :=
    let ⟨_, ht⟩ := exists_gt s.val.re
    mellinConvergent_of_isBigO_rpow (P.hf_int.sub (locallyIntegrableOn_const _)) (P.hf_top _) ht
      P.hf_zero' hs
  refine ⟨hc1, ?_⟩
  have hc2 : MellinConvergent (fun t : Ioi (0 : ℝ) ↦ P.f_modif t.val) s.val :=
    P.isStrongFEPair_toStrongFEPair.mellinConvergent s.val
  have hc3 := P.f_modif_aux2 hs
  have hm := (hasMellin_sub hc2 hc1).2
  have hfun : (fun t : Ioi (0 : ℝ) ↦ P.f_modif t.val - (P.f t.val - P.f₀)) =
      (fun t : Ioi (0 : ℝ) ↦ P.f_modif t.val - P.f t.val + P.f₀) := by
    funext t
    abel
  rw [hfun, hc3] at hm
  exact (sub_right_inj.mp hm).symm

/-- Functional equation formulated for `Λ₀`. -/
theorem functional_equation₀ (s : ℂ) : P.Λ₀ (P.k - s) = P.ε • P.symm.Λ₀ s :=
  P.toStrongFEPair.functional_equation_aux s

/-- Reflection sends the symmetric transform's regular domain to the original regular domain. -/
lemma symm_domain {s : ℂ}
    (hs : (s ≠ 0 ∨ P.g₀ = 0) ∧
      (s ≠ P.k ∨ (Checked.inv P.ε P.hε.isUnit) • P.f₀ = 0)) :
    (P.k - s ≠ 0 ∨ P.f₀ = 0) ∧ (P.k - s ≠ P.k ∨ P.ε • P.g₀ = 0) := by
  constructor
  · rcases hs.2 with hs | hf
    · exact Or.inl (sub_ne_zero.mpr hs.symm)
    · exact Or.inr ((smul_eq_zero.mp hf).resolve_left (inv_ne_zero (ha := P.hε.isUnit)))
  · rcases hs.1 with hs | hg
    · left
      intro he
      apply hs
      linear_combination -he
    · exact Or.inr (by rw [hg, smul_zero])

/-- Reflection carries the exact regular domain of the symmetric transform to that of the
original transform, and the completed transforms satisfy the functional equation there. -/
theorem functional_equation
    (s : {s : ℂ // (s ≠ 0 ∨ P.symm.f₀ = 0) ∧
      (s ≠ P.symm.k ∨ P.symm.ε • P.symm.g₀ = 0)}) :
    P.Λ ⟨P.k - s.val, P.symm_domain s.property⟩ = P.ε • P.symm.Λ s := by
  have hε : IsUnit P.ε := P.hε.isUnit
  have hεinv : Checked.inv P.ε hε ≠ 0 := inv_ne_zero
  have hinv_s : (P.k : ℂ) - s.val = -(s.val - P.k) := by ring
  have hfactor (z : ℂ) : P.ε * (z * Checked.inv P.ε hε) = z := by
    rw [mul_left_comm, mul_inv_cancel₀, mul_one]
  simp only [Λ]
  rw [P.functional_equation₀]
  by_cases hf : P.f₀ = 0 <;> by_cases hg : P.g₀ = 0
  all_goals
    simp [symm, hf, hg, P.hε, hεinv, smul_add, smul_sub]
  all_goals
    simp only [hinv_s, inv_neg₀, neg_smul, ← mul_smul, hfactor]
    module

/-- The residue of `Λ` at `s = k` is equal to `ε • g₀`. The limit is taken on the actual
regular domain, which contains a punctured neighbourhood of `k`. -/
theorem Λ_residue_k :
    Tendsto (fun s : {s : ℂ // (s ≠ 0 ∨ P.f₀ = 0) ∧ (s ≠ P.k ∨ P.ε • P.g₀ = 0)} ↦
      (s.val - P.k) • P.Λ s) (comap Subtype.val (𝓝[≠] (P.k : ℂ)))
      (𝓝 (P.ε • P.g₀)) := by
  classical
  let D := {s : ℂ // (s ≠ 0 ∨ P.f₀ = 0) ∧ (s ≠ P.k ∨ P.ε • P.g₀ = 0)}
  let L : Filter D := comap Subtype.val (𝓝[≠] (P.k : ℂ))
  have hbase : Tendsto (Subtype.val : D → ℂ) L (𝓝 (P.k : ℂ)) :=
    tendsto_comap.mono_right nhdsWithin_le_nhds
  have hentire : Tendsto (fun s : D ↦ (s.val - P.k) • P.Λ₀ s.val) L (𝓝 (0 : E)) := by
    simpa only [sub_self, zero_smul, Function.comp_apply] using
      (hbase.sub_const (P.k : ℂ)).smul (P.differentiable_Λ₀.continuous.tendsto _ |>.comp hbase)
  have hfirst : Tendsto (fun s : D ↦ (s.val - P.k) •
      (if hf : P.f₀ = 0 then 0 else
        Checked.inv s.val (s.property.1.resolve_right hf).isUnit • P.f₀)) L (𝓝 (0 : E)) := by
    by_cases hf : P.f₀ = 0
    · simpa only [dite_eq_left hf, smul_zero] using (tendsto_const_nhds (x := (0 : E)) :
        Tendsto (fun _ : D ↦ (0 : E)) L (𝓝 0))
    · simp only [dite_eq_right hf]
      have hu (s : D) : IsUnit s.val := (s.property.1.resolve_right hf).isUnit
      have hi := hbase.inv₀ (h0 := hu) (ha := (ofReal_ne_zero.mpr P.hk.ne').isUnit)
      simpa only [sub_self, zero_smul] using
        (hbase.sub_const (P.k : ℂ)).smul (hi.smul_const P.f₀)
  have hsecond : Tendsto (fun s : D ↦ (s.val - P.k) •
      (if hg : P.ε • P.g₀ = 0 then 0 else
        Checked.inv (s.val - P.k)
          (sub_ne_zero.mpr (s.property.2.resolve_right hg)).isUnit • (P.ε • P.g₀)))
      L (𝓝 (P.ε • P.g₀)) := by
    by_cases hg : P.ε • P.g₀ = 0
    · simpa [hg] using (tendsto_const_nhds (x := (0 : E)) :
        Tendsto (fun _ : D ↦ (0 : E)) L (𝓝 0))
    · simp only [dite_eq_right hg]
      convert (tendsto_const_nhds (x := P.ε • P.g₀) :
        Tendsto (fun _ : D ↦ P.ε • P.g₀) L (𝓝 _)) using 1
      funext s
      simp only [smul_smul, mul_inv_cancel_left₀]
  simpa only [Λ, smul_add, smul_sub, sub_zero, zero_add] using (hentire.sub hfirst).add hsecond

/-- The residue of `Λ` at `s = 0` is equal to `-f₀`, with the limit taken on its actual
regular domain. -/
theorem Λ_residue_zero :
    Tendsto (fun s : {s : ℂ // (s ≠ 0 ∨ P.f₀ = 0) ∧ (s ≠ P.k ∨ P.ε • P.g₀ = 0)} ↦
      s.val • P.Λ s) (comap Subtype.val (𝓝[≠] (0 : ℂ))) (𝓝 (-P.f₀)) := by
  classical
  let D := {s : ℂ // (s ≠ 0 ∨ P.f₀ = 0) ∧ (s ≠ P.k ∨ P.ε • P.g₀ = 0)}
  let L : Filter D := comap Subtype.val (𝓝[≠] (0 : ℂ))
  have hbase : Tendsto (Subtype.val : D → ℂ) L (𝓝 (0 : ℂ)) :=
    tendsto_comap.mono_right nhdsWithin_le_nhds
  have hentire : Tendsto (fun s : D ↦ s.val • P.Λ₀ s.val) L (𝓝 (0 : E)) := by
    simpa only [zero_smul, Function.comp_apply] using
      hbase.smul (P.differentiable_Λ₀.continuous.tendsto _ |>.comp hbase)
  have hfirst : Tendsto (fun s : D ↦ s.val •
      (if hf : P.f₀ = 0 then 0 else
        Checked.inv s.val (s.property.1.resolve_right hf).isUnit • P.f₀)) L (𝓝 P.f₀) := by
    by_cases hf : P.f₀ = 0
    · simpa [hf] using (tendsto_const_nhds (x := (0 : E)) :
        Tendsto (fun _ : D ↦ (0 : E)) L (𝓝 0))
    · simp only [dite_eq_right hf]
      convert (tendsto_const_nhds (x := P.f₀) :
        Tendsto (fun _ : D ↦ P.f₀) L (𝓝 _)) using 1
      funext s
      simp only [smul_smul, mul_inv_cancel₀, one_smul]
  have hsecond : Tendsto (fun s : D ↦ s.val •
      (if hg : P.ε • P.g₀ = 0 then 0 else
        Checked.inv (s.val - P.k)
          (sub_ne_zero.mpr (s.property.2.resolve_right hg)).isUnit • (P.ε • P.g₀)))
      L (𝓝 (0 : E)) := by
    by_cases hg : P.ε • P.g₀ = 0
    · simpa only [dite_eq_left hg, smul_zero] using (tendsto_const_nhds (x := (0 : E)) :
        Tendsto (fun _ : D ↦ (0 : E)) L (𝓝 0))
    · simp only [dite_eq_right hg]
      have hu (s : D) : IsUnit (s.val - P.k) :=
        (sub_ne_zero.mpr (s.property.2.resolve_right hg)).isUnit
      have hk : IsUnit ((0 : ℂ) - P.k) := by
        simpa only [zero_sub] using (ofReal_ne_zero.mpr P.hk.ne').isUnit.neg
      have hi := (hbase.sub_const (P.k : ℂ)).inv₀ (h0 := hu) (ha := hk)
      simpa only [zero_smul] using hbase.smul (hi.smul_const (P.ε • P.g₀))
  simpa only [Λ, smul_add, smul_sub, zero_sub, add_zero] using (hentire.sub hfirst).add hsecond

end WeakFEPair

namespace IsStrongFEPair
/-!
## Main theorems on strong FE-pairs
-/

open WeakFEPair

variable {P : WeakFEPair E} (hP : IsStrongFEPair P)
include hP

/-- For strong FE-pairs, `P.Λ` is everywhere equal to the Mellin transform of `P.f`. -/
lemma Λ_eq (s : {s : ℂ // (s ≠ 0 ∨ P.f₀ = 0) ∧ (s ≠ P.k ∨ P.ε • P.g₀ = 0)}) :
    P.Λ s = mellin (fun t : Ioi (0 : ℝ) ↦ P.f t.val) s.val := by
  simp only [Λ, hP.hf₀, hP.hg₀, smul_zero, dite_true, sub_zero, add_zero]
  rw [Λ₀, mellin_eq_integral, mellin_eq_integral]
  simp only [f_modif, hP.hf₀, sub_zero, hP.hg₀, smul_zero]
  refine integral_congr_ae <| (ae_restrict_iff' measurableSet_Ioi).mpr ?_
  filter_upwards [compl_mem_ae_iff.mpr (Subsingleton.measure_zero (s := {1}) (by simp) _)]
    with t (ht₁ : t ≠ 1) (ht₀ : 0 < t)
  by_cases ht : t < 1 <;> [rw [add_comm] ; skip] <;>
  rw [Pi.add_apply, indicator_of_mem (by grind), indicator_of_notMem (by grind), add_zero]

/-- For a strong FE-pair the entire transform is the Mellin transform of its positive-source
function, since both residue corrections vanish. -/
lemma Λ₀_eq : P.Λ₀ = mellin (fun t : Ioi (0 : ℝ) ↦ P.f t.val) := by
  funext s
  have h := hP.Λ_eq ⟨s, Or.inr hP.hf₀, Or.inr (by rw [hP.hg₀, smul_zero])⟩
  simpa only [WeakFEPair.Λ, hP.hf₀, hP.hg₀, smul_zero, dite_true,
    sub_zero, add_zero] using h

/-- The symmetric entire transform of a strong FE-pair is the Mellin transform of `g`. -/
lemma symm_Λ₀_eq : P.symm.Λ₀ = mellin (fun t : Ioi (0 : ℝ) ↦ P.g t.val) :=
  hP.symm.Λ₀_eq

lemma symm_Λ_eq
    (s : {s : ℂ // (s ≠ 0 ∨ P.symm.f₀ = 0) ∧
      (s ≠ P.symm.k ∨ P.symm.ε • P.symm.g₀ = 0)}) :
    P.symm.Λ s = mellin (fun t : Ioi (0 : ℝ) ↦ P.g t.val) s.val :=
  hP.symm.Λ_eq s

/-- The Mellin transform of `f` is well-defined and equal to `P.Λ s`, for all `s`. -/
theorem hasMellin (s : ℂ) :
    HasMellin (fun t : Ioi (0 : ℝ) ↦ P.f t.val) s
      (P.Λ ⟨s, Or.inr hP.hf₀, Or.inr (by rw [hP.hg₀, smul_zero])⟩) :=
  ⟨hP.mellinConvergent s,
    (hP.Λ_eq ⟨s, Or.inr hP.hf₀, Or.inr (by rw [hP.hg₀, smul_zero])⟩).symm⟩

/-- If `P` is a strong FE pair, then `P.Λ` is entire. -/
theorem differentiable_Λ :
    Differentiable ℂ (fun s : ℂ ↦
      P.Λ ⟨s, Or.inr hP.hf₀, Or.inr (by rw [hP.hg₀, smul_zero])⟩) := by
  simpa only [hP.Λ_eq] using hP.differentiable_mellin

end IsStrongFEPair
