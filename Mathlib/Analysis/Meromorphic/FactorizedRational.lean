/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Meromorphic.Divisor
public import Mathlib.Analysis.Meromorphic.IsolatedZeros
public import Mathlib.Analysis.Meromorphic.NormalForm
public import Mathlib.Analysis.Meromorphic.TrailingCoefficient
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Factorized Rational Functions

A finite integer divisor prescribes the powers of the linear factors of a rational function.
Its positive multiplicities form the numerator, and its negative multiplicities form the
denominator. Scalar evaluation is defined exactly where the prescribed multiplicity is
nonnegative. The order at every point, including poles, is its prescribed multiplicity.
-/

public section

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {U : Set 𝕜}

open Filter Function Real Set
open scoped Topology

namespace Function.FactorizedRational

section Field

variable {K : Type*} [Field K]

/-- The product of the indicated nonnegative powers of the linear factors. -/
def polynomialPart (s : Finset K) (n : K → ℕ) (x : K) : K :=
  ∏ u ∈ s, (x - u) ^ n u

/-- A product of polynomial factors is nonzero at a point exactly when that point has zero
multiplicity. -/
theorem polynomialPart_ne_zero_iff (s : Finset K) (n : K → ℕ) (x : K) :
    polynomialPart s n x ≠ 0 ↔ x ∈ s → n x = 0 := by
  rw [polynomialPart, Finset.prod_ne_zero_iff]
  constructor
  · intro h hx
    by_contra hn
    exact h x hx (by simp [hn])
  · intro h u hu
    by_cases he : x = u
    · subst u
      simp [h hu]
    · exact pow_ne_zero _ (sub_ne_zero.mpr he)

/-- The numerator of the rational function with prescribed finite divisor. -/
noncomputable def numerator (d : K → ℤ) (hd : d.support.Finite) : K → K :=
  polynomialPart hd.toFinset (fun u ↦ (d u).toNat)

/-- The denominator formed from the negative multiplicities of the divisor. -/
noncomputable def denominator (d : K → ℤ) (hd : d.support.Finite) : K → K :=
  polynomialPart hd.toFinset (fun u ↦ (-d u).toNat)

theorem denominator_ne_zero_iff {d : K → ℤ} (hd : d.support.Finite) (x : K) :
    denominator d hd x ≠ 0 ↔ 0 ≤ d x := by
  rw [denominator, polynomialPart_ne_zero_iff]
  simp only [Finite.mem_toFinset, mem_support]
  omega

theorem numerator_ne_zero_iff {d : K → ℤ} (hd : d.support.Finite) (x : K) :
    numerator d hd x ≠ 0 ↔ d x ≤ 0 := by
  rw [numerator, polynomialPart_ne_zero_iff]
  simp only [Finite.mem_toFinset, mem_support]
  omega

/-- Scalar evaluation exists exactly away from the prescribed negative multiplicities. -/
noncomputable def eval (d : K → ℤ) (hd : d.support.Finite) (x : {x // 0 ≤ d x}) : K :=
  Checked.div (numerator d hd x) (denominator d hd x)
    ((denominator_ne_zero_iff hd (x : K)).mpr x.property).isUnit

/-- A point outside the divisor support has a nonzero rational value. -/
theorem eval_ne_zero {d : K → ℤ} (hd : d.support.Finite) (x : {x // 0 ≤ d x}) (hx : d x = 0) :
    eval d hd x ≠ 0 :=
  div_ne_zero ((numerator_ne_zero_iff hd (x : K)).mpr hx.le)

/-- The unit remaining after removing the factor at the center has this scalar value. -/
noncomputable def leadingValue (d : K → ℤ) (hd : d.support.Finite) (x : K) : K := by
  classical
  let s := hd.toFinset.erase x
  have h : polynomialPart s (fun u ↦ (-d u).toNat) x ≠ 0 :=
    (polynomialPart_ne_zero_iff _ _ _).mpr fun hx ↦ (Finset.notMem_erase _ _ hx).elim
  exact Checked.div (polynomialPart s (fun u ↦ (d u).toNat) x)
    (polynomialPart s (fun u ↦ (-d u).toNat) x) h.isUnit

theorem leadingValue_ne_zero (d : K → ℤ) (hd : d.support.Finite) (x : K) :
    leadingValue d hd x ≠ 0 := by
  classical
  apply div_ne_zero
  exact (polynomialPart_ne_zero_iff _ _ _).mpr fun hx ↦ (Finset.notMem_erase _ _ hx).elim

private theorem polynomialPart_extract [DecidableEq K] (s : Finset K) (n : K → ℕ) (x : K)
    (h : x ∉ s → n x = 0) :
    ∀ z : K, polynomialPart s n z = (z - x) ^ n x * polynomialPart (s.erase x) n z := by
  classical
  intro z
  by_cases hx : x ∈ s
  · exact (s.mul_prod_erase (fun u ↦ (z - u) ^ n u) hx).symm
  · simp [h hx, Finset.erase_eq_of_notMem hx]

private theorem div_centered_powers (c a b v : K) (hc : c ≠ 0) (hv : b * v = 1) (d : ℤ)
    (h : IsUnit (c ^ (-d).toNat * b)) :
    Checked.div (c ^ d.toNat * a) (c ^ (-d).toNat * b) h =
    Checked.zpow c d (fun _ ↦ hc.isUnit) * (a * v) := by
  apply div_eq_iff.mpr
  have hpow : Checked.zpow c d (fun _ ↦ hc.isUnit) * c ^ (-d).toNat = c ^ d.toNat := by
    let u := hc.isUnit.unit
    rw [hc.isUnit.zpow_eq_val_unit_zpow]
    have he : (d + ((-d).toNat : ℤ)) = (d.toNat : ℤ) := by omega
    have hp := congrArg (fun z : ℤ ↦ (↑(u ^ z) : K)) he
    simpa only [zpow_add, Units.val_mul, zpow_natCast, Units.val_pow_eq_pow_val, u,
      IsUnit.unit_spec] using hp
  calc
    _ = (Checked.zpow c d (fun _ ↦ hc.isUnit) * c ^ (-d).toNat) * a * (b * v) := by
      rw [hpow, hv, mul_one]
    _ = _ := by ac_rfl

end Field

private theorem analyticAt_polynomialPart (s : Finset 𝕜) (n : 𝕜 → ℕ) (x : 𝕜) :
    AnalyticAt 𝕜 (polynomialPart s n) x :=
  s.analyticAt_fun_prod fun u _ ↦ (analyticAt_id.sub analyticAt_const).pow (n u)

/-- The order of a polynomial product at a point is its multiplicity in that product. -/
private theorem analyticOrderAt_polynomialPart (s : Finset 𝕜) (n : 𝕜 → ℕ) (x : 𝕜)
    (hx : x ∉ s → n x = 0) :
    analyticOrderAt (polynomialPart s n) x (analyticAt_polynomialPart s n x) = n x := by
  classical
  by_cases h : x ∈ s
  · have he : polynomialPart s n =
        ((· - x) ^ n x) * polynomialPart (s.erase x) n := by
      funext t
      exact (s.mul_prod_erase (fun u ↦ (t - u) ^ n u) h).symm
    have hg := analyticAt_polynomialPart (s.erase x) n x
    have hn : polynomialPart (s.erase x) n x ≠ 0 :=
      (polynomialPart_ne_zero_iff _ _ _).mpr fun hx ↦ (Finset.notMem_erase x s hx).elim
    have hc : AnalyticAt 𝕜 (fun z ↦ z - x) x := analyticAt_id.sub analyticAt_const
    rw [analyticOrderAt_congr _ (.of_eq he), analyticOrderAt_mul (hc.pow (n x)) hg,
      analyticOrderAt_centeredMonomial,
      hg.analyticOrderAt_eq_zero.mpr hn, add_zero]
  · rw [hx h]
    exact (analyticAt_polynomialPart s n x).analyticOrderAt_eq_zero.mpr
      ((polynomialPart_ne_zero_iff _ _ _).mpr fun hs ↦ (h hs).elim)

private theorem analyticOrderAt_numerator {d : 𝕜 → ℤ} (hd : d.support.Finite) (x : 𝕜) :
    analyticOrderAt (numerator d hd) x (analyticAt_polynomialPart _ _ _) = (d x).toNat := by
  apply analyticOrderAt_polynomialPart
  intro hx
  have he : d x = 0 := by simpa only [Finite.mem_toFinset, mem_support, not_not] using hx
  simp [he]

private theorem analyticOrderAt_denominator {d : 𝕜 → ℤ} (hd : d.support.Finite) (x : 𝕜) :
    analyticOrderAt (denominator d hd) x (analyticAt_polynomialPart _ _ _) = (-d x).toNat := by
  apply analyticOrderAt_polynomialPart
  intro hx
  have he : d x = 0 := by simpa only [Finite.mem_toFinset, mem_support, not_not] using hx
  simp [he]

/-- A factorized rational function is normalized at every point, including each of its poles. -/
theorem meromorphicNFOn {d : 𝕜 → ℤ} (hd : d.support.Finite) (U : Set 𝕜) :
    MeromorphicNFOn (eval d hd) U Subtype.val := by
  intro x _
  have ha : AnalyticAt 𝕜 (numerator d hd) x := analyticAt_polynomialPart _ _ _
  have hb : AnalyticAt 𝕜 (denominator d hd) x := analyticAt_polynomialPart _ _ _
  have hn : ¬ denominator d hd =ᶠ[𝓝 x] 0 := by
    intro h
    have ho := (analyticOrderAt_eq_top hb).mpr h
    rw [analyticOrderAt_denominator hd x] at ho
    exact ENat.natCast_ne_top _ ho
  have hcop (hb : denominator d hd x = 0) : numerator d hd x ≠ 0 := by
    apply (numerator_ne_zero_iff hd x).mpr
    exact (lt_of_not_ge (fun h ↦ (denominator_ne_zero_iff hd x).mpr h hb)).le
  apply (ha.meromorphicNFAt_div hb hn hcop).congr_subtype
    (Set.ext (denominator_ne_zero_iff hd))
  exact fun _ _ ↦ rfl

/-- The valuation of the scalar representative, including at an excluded pole. -/
theorem meromorphicOrderAt_eq {d : 𝕜 → ℤ} (hd : d.support.Finite) (x : 𝕜) :
    meromorphicOrderAt (eval d hd) x ((meromorphicNFOn hd univ trivial).meromorphicAt) = d x := by
  have ha : AnalyticAt 𝕜 (numerator d hd) x := analyticAt_polynomialPart _ _ _
  have hb : AnalyticAt 𝕜 (denominator d hd) x := analyticAt_polynomialPart _ _ _
  have hmer := (meromorphicNFOn hd univ (z := x) trivial).meromorphicAt
  have hc : range (fun y : {t : 𝕜 | IsUnit (denominator d hd t)} ↦ _root_.id y.val) ∈ 𝓝[≠] x := by
    filter_upwards [hmer.1] with t ⟨y, hyt⟩
    exact ⟨⟨y, ((denominator_ne_zero_iff hd y).mpr y.property).isUnit⟩, hyt⟩
  have h := hmer.order_eq_of_eventuallyEq (ha.meromorphicAt.div hb.meromorphicAt hc)
    (.of_forall fun t ⟨a, ha⟩ ⟨b, hb⟩ hat hbt ↦ by
      obtain rfl : a = b := hat.trans hbt.symm
      rfl)
  simp only [meromorphicOrderAt_div ha.meromorphicAt hb.meromorphicAt hc,
    ha.meromorphicOrderAt_eq, hb.meromorphicOrderAt_eq, analyticOrderAt_numerator,
    analyticOrderAt_denominator, ENat.map_natCast, WithTop.checked_sub_coe] at h
  exact h.trans (congrArg ((↑) : ℤ → WithTop ℤ)
    (show ((d x).toNat : ℤ) - (-d x).toNat = d x by omega))

/-- A factorized rational function realizes its prescribed finite divisor. -/
theorem divisor {U : Set 𝕜} {d : locallyFinsuppWithin U ℤ} (hd : d.support.Finite)
    {h : ∀ z (hz : z ∈ U), meromorphicOrderAt (eval d hd) z
      ((meromorphicNFOn hd U hz).meromorphicAt) ≠ ⊤} :
    MeromorphicOn.divisor (eval d hd) U h = d := by
  ext z
  by_cases hz : z ∈ U
  · exact_mod_cast (MeromorphicOn.coe_divisor_apply ((meromorphicNFOn hd U).meromorphicOn)
      hz (h := h)).trans (meromorphicOrderAt_eq hd z)
  · simp [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hz]

/-- The leading coefficient is the quotient obtained by removing the factor at the center. -/
theorem meromorphicTrailingCoeffAt_factorizedRational {d : 𝕜 → ℤ} (hd : d.support.Finite) (x : 𝕜)
    {h : meromorphicOrderAt (eval d hd) x ((meromorphicNFOn hd univ trivial).meromorphicAt) ≠ ⊤} :
    meromorphicTrailingCoeffAt (eval d hd) x h = leadingValue d hd x := by
  classical
  let s := hd.toFinset.erase x
  let a := polynomialPart s (fun u ↦ (d u).toNat)
  let b := polynomialPart s (fun u ↦ (-d u).toNat)
  have ha : AnalyticAt 𝕜 a x := analyticAt_polynomialPart _ _ _
  have hb : AnalyticAt 𝕜 b x := analyticAt_polynomialPart _ _ _
  have hbx : b x ≠ 0 :=
    (polynomialPart_ne_zero_iff _ _ _).mpr fun hx ↦ (Finset.notMem_erase _ _ hx).elim
  obtain ⟨v, hv, hbv⟩ := hb.exists_mul_eq_one hbx.isUnit
  have hx' (hx : x ∉ hd.toFinset) : d x = 0 := by
    simpa only [Finite.mem_toFinset, mem_support, not_not] using hx
  have hA := polynomialPart_extract hd.toFinset (fun u ↦ (d u).toNat) x
    (fun h ↦ by simp [hx' h])
  have hB := polynomialPart_extract hd.toFinset (fun u ↦ (-d u).toNat) x
    (fun h ↦ by simp [hx' h])
  have hm := (meromorphicNFOn hd univ (z := x) trivial).meromorphicAt
  have ho : (meromorphicOrderAt (eval d hd) x hm).untop h = d x :=
    (WithTop.untop_eq_iff _).mpr (meromorphicOrderAt_eq hd x)
  have hfactor : meromorphicTrailingCoeffAt (eval d hd) x h = (a * v) x := by
    apply (ha.mul hv).meromorphicTrailingCoeffAt_of_eq_nhdsNE hm h
    filter_upwards [tendsto_comap.eventually (hbv.filter_mono nhdsWithin_le_nhds)] with y hy
    intro hyx
    rw [ho]
    have hd' : IsUnit (((y : 𝕜) - x) ^ (-d x).toNat * b y) := by
      rw [← hB]
      exact ((denominator_ne_zero_iff hd y).mpr y.property).isUnit
    have hp := div_centered_powers ((y : 𝕜) - x) (a y) (b y) (v y)
      (sub_ne_zero.mpr hyx) hy (d x) hd'
    change Checked.div (numerator d hd y) (denominator d hd y) _ = _
    apply div_eq_iff.mpr
    change numerator d hd y = _ * denominator d hd y
    rw [show numerator d hd y = _ from hA y, show denominator d hd y = _ from hB y]
    exact div_eq_iff.mp hp
  rw [hfactor]
  change a x * v x = Checked.div (a x) (b x) _
  apply eq_div_iff.mpr
  rw [mul_assoc, mul_comm (v x), hbv.self_of_nhds, mul_one]

/-- Off the support the trailing coefficient is the ordinary scalar value. -/
theorem meromorphicTrailingCoeffAt_factorizedRational_off_support {d : 𝕜 → ℤ} {x : 𝕜}
    (hd : d.support.Finite) (hx : d x = 0)
    {h : meromorphicOrderAt (eval d hd) x ((meromorphicNFOn hd univ trivial).meromorphicAt) ≠ ⊤} :
    meromorphicTrailingCoeffAt (eval d hd) x h = eval d hd ⟨x, hx.ge⟩ := by
  classical
  rw [meromorphicTrailingCoeffAt_factorizedRational]
  have hmem : x ∉ hd.toFinset := by simp [hx]
  simp only [leadingValue, Finset.erase_eq_of_notMem hmem, eval, numerator, denominator]

private theorem log_norm_polynomialPart (s : Finset 𝕜) (n : 𝕜 → ℕ) {x : 𝕜} (hx : x ∉ s) :
    log ‖polynomialPart s n x‖ = ∑ u ∈ s, n u * log ‖x - u‖ := by
  rw [polynomialPart, norm_prod, log_prod]
  · simp only [norm_pow, log_pow]
  · intro u hu
    exact norm_ne_zero_iff.mpr (pow_ne_zero _ (sub_ne_zero.mpr (fun he ↦ hx (he ▸ hu))))

/-- Removing the central factor gives the logarithm of the norm of the leading value. -/
theorem log_norm_leadingValue {d : 𝕜 → ℤ} (hd : d.support.Finite) (x : 𝕜) :
    log ‖leadingValue d hd x‖ = ∑ᶠ u, (d u : ℝ) * log ‖x - u‖ := by
  classical
  let s := hd.toFinset.erase x
  have hx : x ∉ s := Finset.notMem_erase _ _
  have ha : polynomialPart s (fun u ↦ (d u).toNat) x ≠ 0 :=
    (polynomialPart_ne_zero_iff _ _ _).mpr fun h ↦ (hx h).elim
  have hs : (fun u ↦ (d u : ℝ) * log ‖x - u‖).support ⊆ s := by
    intro u hu
    refine Finset.mem_erase.mpr ⟨?_, ?_⟩
    · intro he
      subst u
      exact hu (by simp)
    · apply hd.mem_toFinset.mpr
      intro h
      exact hu (by simp [h])
  rw [leadingValue, norm_div, log_div (norm_ne_zero_iff.mpr ha),
    log_norm_polynomialPart s _ hx, log_norm_polynomialPart s _ hx,
    ← Finset.sum_sub_distrib, finsum_eq_sum_of_support_subset _ hs]
  apply Finset.sum_congr rfl
  intro u _
  rw [← sub_mul]
  congr 1
  exact_mod_cast (show ((d u).toNat : ℤ) - (-d u).toNat = d u by omega)

/-- The logarithmic norm of the trailing coefficient is the finite sum of the prescribed
multiplicities times the logarithmic distances. -/
theorem log_norm_meromorphicTrailingCoeffAt {d : 𝕜 → ℤ} (hd : d.support.Finite) (x : 𝕜)
    {h : meromorphicOrderAt (eval d hd) x ((meromorphicNFOn hd univ trivial).meromorphicAt) ≠ ⊤} :
    log ‖meromorphicTrailingCoeffAt (eval d hd) x h‖ = ∑ᶠ u, (d u : ℝ) * log ‖x - u‖ := by
  rw [meromorphicTrailingCoeffAt_factorizedRational, log_norm_leadingValue]

end Function.FactorizedRational

open Function.FactorizedRational

/-!
## Elimination of Zeros and Poles

This section shows that every meromorphic function with finitely many zeros and poles is equivalent,
modulo equality on codiscrete sets, to the product of a factorized rational function and an analytic
function without zeros.

We provide analogous results for functions of the form `log ‖meromorphic‖`.
-/

private theorem exists_analytic_extension_on {U S : Set 𝕜}
    (hS : ∀ x, S ∈ 𝓝[≠] x) (hUS : Uᶜ ⊆ S) (q : S → E)
    (H : ∀ x ∈ U, ∃ a : 𝕜 → E, AnalyticAt 𝕜 a x ∧ a x ≠ 0 ∧
      ∀ᶠ y in 𝓝[≠] x, ∀ hy : y ∈ S, a y = q ⟨y, hy⟩) :
    ∃ G : 𝕜 → E, AnalyticOnNhd 𝕜 G U ∧ (∀ x ∈ U, G x ≠ 0) ∧
      ∀ᶠ x in codiscreteWithin U, ∀ hx : x ∈ S, G x = q ⟨x, hx⟩ := by
  classical
  choose a ha using H
  let G (x : 𝕜) : E := if hx : x ∈ U then a x hx x else q ⟨x, hUS hx⟩
  have hloc (x : 𝕜) (hx : x ∈ U) : G =ᶠ[𝓝 x] a x hx := by
    have he := eventually_eventually_nhds.mpr (eventually_nhdsWithin_iff.mp (ha x hx).2.2)
    filter_upwards [he, (ha x hx).1.eventually_continuousAt] with y hy hcont
    by_cases hyx : y = x
    · subst y
      simp [G, hx]
    by_cases hyU : y ∈ U
    · have hne : ∀ᶠ z in 𝓝 y, z ≠ x := isOpen_ne.mem_nhds hyx
      have heq : a y hyU =ᶠ[𝓝[≠] y] a x hx := by
        filter_upwards [(ha y hyU).2.2, hS y, hy.filter_mono nhdsWithin_le_nhds,
          hne.filter_mono nhdsWithin_le_nhds] with z hz hzS hz' hzx
        exact (hz hzS).trans (hz' hzx hzS).symm
      have heval := tendsto_nhds_unique_of_eventuallyEq
        (ha y hyU).1.continuousAt.continuousWithinAt hcont.continuousWithinAt heq
      simpa [G, hyU] using heval
    · exact (dite_eq_right hyU).trans (hy.self_of_nhds hyx (hUS hyU)).symm
  refine ⟨G, fun x hx ↦ (ha x hx).1.congr (hloc x hx).symm, ?_, ?_⟩
  · intro x hx
    simpa [G, hx] using (ha x hx).2.1
  · apply eventually_codiscreteWithin_iff_forall_eventually_nhdsNE.mpr
    intro x hx
    filter_upwards [(hloc x hx).filter_mono nhdsWithin_le_nhds, (ha x hx).2.2] with y hy he
    exact fun _ hyS ↦ hy.trans (he hyS)

/--
If `f` is meromorphic on an open set `U`, if `f` is nowhere locally constant zero, and if the
support of the divisor of `f` is finite, then there exists an analytic function `g` on `U` without
zeros such that `f` is equivalent, modulo equality on codiscrete sets, to the product of `g` and the
factorized rational function associated with the divisor of `f`.
-/
theorem MeromorphicOn.extract_zeros_poles {f : 𝕜 → E} (h₁f : MeromorphicOn f U)
    (h₂f : ∀ z (hz : z ∈ U), meromorphicOrderAt f z (h₁f z hz) ≠ ⊤)
    (h₃f : (divisor f U h₂f).support.Finite) :
    ∃ g : 𝕜 → E, AnalyticOnNhd 𝕜 g U ∧ (∀ u : U, g u ≠ 0) ∧
      ∀ᶠ z in codiscreteWithin U, ∃ hz : divisor f U h₂f z = 0,
        f z = Function.FactorizedRational.eval (divisor f U h₂f) h₃f ⟨z, hz.ge⟩ • g z := by
  let d := divisor f U h₂f
  let S := {z : 𝕜 | d z = 0}
  let R := Function.FactorizedRational.eval d h₃f
  have hS (x : 𝕜) : S ∈ 𝓝[≠] x := by
    filter_upwards [(nhdsNE_le_cofinite x) h₃f.compl_mem_cofinite] with y hy
    exact not_not.mp hy
  have hUS : Uᶜ ⊆ S := fun z hz ↦ d.apply_eq_zero_of_notMem hz
  let u (z : S) := ((eval_ne_zero h₃f ⟨z.val, z.property.ge⟩ z.property).isUnit).unit
  let q (z : S) := (u z)⁻¹ • f z
  have H (x : 𝕜) (hx : x ∈ U) : ∃ a : 𝕜 → E, AnalyticAt 𝕜 a x ∧ a x ≠ 0 ∧
      ∀ᶠ y in 𝓝[≠] x, ∀ hy : y ∈ S, a y = q ⟨y, hy⟩ := by
    let hR := (Function.FactorizedRational.meromorphicNFOn h₃f univ (z := x) trivial).meromorphicAt
    have hor : meromorphicOrderAt R x hR = (d x : ℤ) := meromorphicOrderAt_eq h₃f x
    have hrfin : meromorphicOrderAt R x hR ≠ ⊤ := hor.trans_ne WithTop.coe_ne_top
    obtain ⟨B, hB, hBx, hRB⟩ := hR.exists_analytic_factor hrfin
    obtain ⟨A, hA, hAx, hfA⟩ := (h₁f x hx).exists_analytic_factor (h₂f x hx)
    obtain ⟨v, hv, hvB⟩ := hB.exists_mul_eq_one hBx.isUnit
    have hvx : v x ≠ 0 := right_ne_zero_of_mul_eq_one hvB.self_of_nhds
    refine ⟨v • A, hv.smul hA, smul_ne_zero hvx hAx, ?_⟩
    have ho : (meromorphicOrderAt R x hR).untop hrfin =
        (meromorphicOrderAt f x (h₁f x hx)).untop (h₂f x hx) := by
      apply WithTop.coe_injective
      rw [WithTop.coe_untop, WithTop.coe_untop, hor]
      exact coe_divisor_apply h₁f hx
    filter_upwards [eventually_comap.mp hRB, eventually_comap.mp hfA,
      hvB.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with y hR' hf' hv' hyx
    intro hy
    let z : S := ⟨y, hy⟩
    let w : {y : 𝕜 | 0 ≤ d y} := ⟨y, hy.ge⟩
    have hR'' := hR' w rfl hyx
    have hf'' := hf' y rfl hyx
    change v y • A y = (u z)⁻¹ • f y
    apply MulAction.injective (u z)
    change u z • (v y • A y) = u z • ((u z)⁻¹ • f y)
    rw [smul_inv_smul]
    change (↑(u z) : 𝕜) • (v y • A y) = f y
    have hvu : (u z : 𝕜) = R w := IsUnit.unit_spec _
    change R w = Checked.zpow (y - x) ((meromorphicOrderAt R x hR).untop hrfin)
      (fun _ ↦ (sub_ne_zero.mpr hyx).isUnit) * B y at hR''
    change f y = Checked.zpow (y - x) ((meromorphicOrderAt f x (h₁f x hx)).untop (h₂f x hx))
      (fun _ ↦ (sub_ne_zero.mpr hyx).isUnit) • A y at hf''
    rw [hvu, hR'', ho, hf'', ← mul_smul, mul_assoc, hv', mul_one]
  obtain ⟨G, hG, hGx, hq⟩ := exists_analytic_extension_on hS hUS q H
  refine ⟨G, hG, fun z ↦ hGx z z.property, ?_⟩
  filter_upwards [hq, d.eq_zero_codiscreteWithin] with y hy hdy
  have h : d y = 0 := hdy
  refine ⟨h, ?_⟩
  rw [hy h]
  exact (smul_inv_smul (u ⟨y, h⟩) (f y)).symm

/--
In the setting of `MeromorphicOn.extract_zeros_poles`, the function `log ‖f‖` is equivalent, modulo
equality on codiscrete subsets, to `∑ᶠ u, (divisor f U u * log ‖· - u‖) + log ‖g ·‖`.
-/
theorem MeromorphicOn.extract_zeros_poles_log {f g : 𝕜 → E} {D : Function.locallyFinsuppWithin U ℤ}
    {hD : D.support.Finite} (hg : ∀ u : U, g u ≠ 0)
    (h : ∀ᶠ z in codiscreteWithin U, ∃ hz : D z = 0,
      f z = Function.FactorizedRational.eval D hD ⟨z, hz.ge⟩ • g z) :
    (log ‖f ·‖) =ᶠ[codiscreteWithin U] ∑ᶠ u, (D u * log ‖· - u‖) + (log ‖g ·‖) := by
  classical
  have hs : (fun u ↦ (fun z : 𝕜 ↦ (D u : ℝ) * log ‖z - u‖)).support ⊆ hD.toFinset := by
    intro u hu
    apply hD.mem_toFinset.mpr
    intro hd
    exact hu (by ext; simp [hd])
  rw [finsum_eq_sum_of_support_subset _ hs]
  filter_upwards [h, self_mem_codiscreteWithin U] with z ⟨hz, he⟩ hzU
  have hm := (Function.FactorizedRational.meromorphicNFOn hD univ (z := z) trivial).meromorphicAt
  have hfin : meromorphicOrderAt _ z hm ≠ ⊤ :=
    (meromorphicOrderAt_eq hD z).trans_ne WithTop.coe_ne_top
  have hcoef := meromorphicTrailingCoeffAt_factorizedRational_off_support hD hz (h := hfin)
  have hlog := log_norm_meromorphicTrailingCoeffAt hD z (h := hfin)
  rw [hcoef, finsum_eq_sum_of_support_subset (s := hD.toFinset) _ (by
    intro u hu
    apply hD.mem_toFinset.mpr
    intro hd
    exact hu (by simp [hd]))] at hlog
  rw [he, norm_smul, log_mul (norm_ne_zero_iff.mpr (eval_ne_zero hD _ hz))
    (norm_ne_zero_iff.mpr (hg ⟨z, hzU⟩)), hlog]
  simp

/-- If a meromorphic function agrees codiscretely with a factorized rational function
times an analytic unit, its leading coefficient is the product of their leading values. -/
theorem MeromorphicOn.meromorphicTrailingCoeffAt_extract_zeros_poles {x : 𝕜} {f g : 𝕜 → E}
    {d : 𝕜 → ℤ} (hd : d.support.Finite) (hx : x ∈ U) (hacc : AccPt x (𝓟 U))
    (hf : MeromorphicAt f x) (hg : AnalyticAt 𝕜 g x) (hgx : g x ≠ 0)
    (he : ∀ᶠ z in codiscreteWithin U, ∃ hz : d z = 0,
      f z = Function.FactorizedRational.eval d hd ⟨z, hz.ge⟩ • g z)
    {h : meromorphicOrderAt f x hf ≠ ⊤} :
    meromorphicTrailingCoeffAt f x h = leadingValue d hd x • g x := by
  let R := Function.FactorizedRational.eval d hd
  have ha : AnalyticAt 𝕜 (numerator d hd) x := analyticAt_polynomialPart _ _ _
  have hb : AnalyticAt 𝕜 (denominator d hd) x := analyticAt_polynomialPart _ _ _
  have hclear : denominator d hd • f =ᶠ[𝓝[≠] x] numerator d hd • g := by
    apply (hb.meromorphicAt.smul hf).eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin
      (ha.meromorphicAt.smul hg.meromorphicAt) hx hacc
    filter_upwards [he] with y ⟨hy, hfy⟩
    have hn := (denominator_ne_zero_iff hd y).mpr hy.ge
    change denominator d hd y • f y = numerator d hd y • g y
    rw [hfy, ← mul_smul]
    rw [mul_comm (denominator d hd y), show Function.FactorizedRational.eval d hd ⟨y, hy.ge⟩ *
      denominator d hd y = numerator d hd y from div_mul_cancel₀ _]
  have hR := (Function.FactorizedRational.meromorphicNFOn hd univ (z := x) trivial).meromorphicAt
  have hfin : meromorphicOrderAt R x hR ≠ ⊤ :=
    (meromorphicOrderAt_eq hd x).trans_ne WithTop.coe_ne_top
  obtain ⟨B, hB, hBx, hRB⟩ := hR.exists_analytic_factor hfin
  have hBval : meromorphicTrailingCoeffAt R x hfin = B x :=
    hB.meromorphicTrailingCoeffAt_of_eq_nhdsNE hR hfin hRB
  have ho : (meromorphicOrderAt R x hR).untop hfin = d x :=
    (WithTop.untop_eq_iff _).mpr (meromorphicOrderAt_eq hd x)
  have ht : ∀ᶠ y in 𝓝[≠] x, ∀ hne : y ≠ x, f y =
      Checked.zpow (y - x) (d x) (fun _ ↦ (sub_ne_zero.mpr hne).isUnit) • (B y • g y) := by
    filter_upwards [hclear, eventually_comap.mp hRB, (nhdsNE_le_cofinite x) hd.compl_mem_cofinite]
      with y hy hR' hyS
    intro hne
    have hz : d y = 0 := not_not.mp hyS
    have hn := (denominator_ne_zero_iff hd y).mpr hz.ge
    have hval := hR' ⟨y, hz.ge⟩ rfl hne
    rw [ho] at hval
    have hval' : R ⟨y, hz.ge⟩ = Checked.zpow (y - x) (d x)
        (fun _ ↦ (sub_ne_zero.mpr hne).isUnit) * B y := hval
    rw [← mul_smul, ← hval']
    apply (smul_right_inj hn).mp
    rw [← mul_smul, mul_comm (denominator d hd y),
      show R ⟨y, hz.ge⟩ * denominator d hd y = numerator d hd y from div_mul_cancel₀ _]
    exact hy
  have hcoef : meromorphicTrailingCoeffAt f x h = B x • g x := by
    apply (hB.smul hg).meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE
      (n := d x) (smul_ne_zero hBx hgx)
    filter_upwards [tendsto_comap.eventually (eventually_nhdsWithin_iff.mp ht)] with z hz
    exact hz z.property z.property
  rw [hcoef, ← hBval]
  exact congrArg (· • g x) (meromorphicTrailingCoeffAt_factorizedRational hd x)

/-- The logarithm of the leading norm splits into the contributions of the finite divisor
and the analytic unit at the center. -/
theorem MeromorphicOn.log_norm_meromorphicTrailingCoeffAt_extract_zeros_poles
    {x : 𝕜} {f g : 𝕜 → E} {d : 𝕜 → ℤ} (hd : d.support.Finite) (hx : x ∈ U) (hacc : AccPt x (𝓟 U))
    (hf : MeromorphicAt f x) (hg : AnalyticAt 𝕜 g x) (hgx : g x ≠ 0)
    (he : ∀ᶠ z in codiscreteWithin U, ∃ hz : d z = 0,
      f z = Function.FactorizedRational.eval d hd ⟨z, hz.ge⟩ • g z)
    {h : meromorphicOrderAt f x hf ≠ ⊤} :
    log ‖meromorphicTrailingCoeffAt f x h‖ = ∑ᶠ u, (d u : ℝ) * log ‖x - u‖ + log ‖g x‖ := by
  rw [MeromorphicOn.meromorphicTrailingCoeffAt_extract_zeros_poles hd hx hacc hf hg hgx he,
    norm_smul, log_mul (norm_ne_zero_iff.mpr (leadingValue_ne_zero d hd x))
    (norm_ne_zero_iff.mpr hgx), log_norm_leadingValue]
