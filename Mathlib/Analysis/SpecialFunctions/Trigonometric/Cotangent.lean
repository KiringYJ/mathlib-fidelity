/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
public import Mathlib.Analysis.Complex.UpperHalfPlane.Exp
public import Mathlib.Analysis.Complex.IntegerCompl
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd
public import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable
public import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn

/-!
# Cotangent

This file contains lemmas about the cotangent function, including useful series expansions.
In particular, we prove that
`π * cot (π * z) = π * I - 2 * π * I * ∑' n : ℕ, Complex.exp (2 * π * I * z) ^ n`
as well as the infinite sum representation of cotangent (also known as the Mittag-Leffler
expansion): `π * cot (π * z) = 1 / z + ∑' n : ℕ+, (1 / (z - n) + 1 / (z + n))`.
-/

public section

open Real Complex

open scoped UpperHalfPlane

local notation "ℂ_ℤ" => integerComplement

local notation "ℍₒ" => UpperHalfPlane.upperHalfPlaneSet

private lemma exp_sub_eq_mul_one_sub_exp (z : ℂ) :
    exp (-z * I) - exp (z * I) = exp (-(z * I)) * (1 - exp (2 * I * z)) := by
  rw [mul_sub, mul_one, ← Complex.exp_add, neg_mul]
  congr 2
  ring

private lemma I_mul_one_sub_exp_ne_zero {z : ℂ} (hz : sin z ≠ 0) :
    I * (1 - exp (2 * I * z)) ≠ 0 := by
  intro he
  have hsub := (mul_eq_zero.mp he).resolve_left I_ne_zero
  apply hz
  rw [Complex.sin, exp_sub_eq_mul_one_sub_exp, hsub, mul_zero, zero_mul, zero_div]

lemma Complex.cot_eq_exp_ratio (z : ℂ) {hz : sin z ≠ 0} :
    cot z hz = Checked.div (Complex.exp (2 * I * z) + 1) (I * (1 - Complex.exp (2 * I * z)))
      (by exact (I_mul_one_sub_exp_ne_zero hz).isUnit) := by
  rw [Complex.cot, div_eq_div_iff, Complex.sin, Complex.cos]
  have h1 : exp (z * I) + exp (-z * I) = exp (-(z * I)) * (exp (2 * I * z) + 1) := by
    rw [mul_add, ← Complex.exp_add]
    ring_nf
  rw [h1, exp_sub_eq_mul_one_sub_exp]
  ring

/-- The version one probably wants to use more. -/
lemma Complex.cot_pi_eq_exp_ratio (z : ℂ) {hz : sin (π * z) ≠ 0} :
    cot (π * z) hz = Checked.div (Complex.exp (2 * π * I * z) + 1)
      (I * (1 - Complex.exp (2 * π * I * z))) (by
        have h : 2 * I * ((π : ℂ) * z) = 2 * π * I * z := by ring
        simpa only [h] using (I_mul_one_sub_exp_ne_zero hz).isUnit) := by
  have h : 2 * I * ((π : ℂ) * z) = 2 * π * I * z := by ring
  simpa only [h] using cot_eq_exp_ratio (π * z) (hz := hz)

/-- `sin π z` is non vanishing on the complement of the integers in `ℂ`. -/
theorem sin_pi_mul_ne_zero {x : ℂ} (hx : x ∈ ℂ_ℤ) : Complex.sin (π * x) ≠ 0 := by
  apply Complex.sin_ne_zero_iff.2
  intro k h
  apply hx
  refine ⟨k, mul_left_cancel₀ (ofReal_ne_zero.mpr Real.pi_ne_zero) ?_⟩
  simpa only [mul_comm (π : ℂ) (k : ℂ)] using h.symm

/-- This is the version one probably wants, which is why the pi's are there. -/
theorem pi_mul_cot_pi_q_exp (z : ℍ) :
    π * cot (π * z) (sin_pi_mul_ne_zero (UpperHalfPlane.coe_mem_integerComplement z)) =
      π * I - 2 * π * I * ∑' n : ℕ, Complex.exp (2 * π * I * z) ^ n := by
  let q := exp (2 * π * I * (z : ℂ))
  have hq : ‖q‖ < 1 := UpperHalfPlane.norm_exp_two_pi_I_lt_one z
  have hu := isUnit_one_sub_of_norm_lt_one hq
  have hi := I_ne_zero.isUnit
  have h1 : π * ((q + 1) / (I * (1 - q))) = -π * I * ((q + 1) * (1 - q)⁻¹) := by
    rw [div_eq_mul_inv₀, mul_inv₀, inv_I]
    ring
  rw [cot_pi_eq_exp_ratio]
  change π * ((q + 1) / (I * (1 - q))) = π * I - 2 * π * I * ∑' n : ℕ, q ^ n
  rw [h1, (tsum_geometric_of_norm_lt_one hq).symm, add_comm (q : ℂ), geom_series_mul_one_add q hq]
  ring

section MittagLeffler

open Filter Function

open scoped Topology Nat Complex

variable {x : ℂ} {Z : Set ℂ}

/-- The main term in the infinite product for sine. -/
noncomputable abbrev sineTerm (x : ℂ) (n : ℕ) : ℂ := -x ^ 2 / ((n : ℂ) + 1) ^ 2

lemma sineTerm_ne_zero {x : ℂ} (hx : x ∈ ℂ_ℤ) (n : ℕ) : 1 + sineTerm x n ≠ 0 := by
  have hn := (Nat.cast_add_one_ne_zero (R := ℂ) n).isUnit.pow 2
  intro hz
  have h := (div_eq_iff.mp (eq_neg_of_add_eq_zero_right hz))
  apply integerComplement_pow_two_ne_pow_two hx ((n : ℤ) + 1)
  simpa only [Int.cast_add, Int.cast_natCast, Int.cast_one, neg_one_mul, neg_inj] using h

lemma tendsto_euler_sin_prod' (h0 : x ≠ 0) :
    Tendsto (fun n : ℕ ↦ ∏ i ∈ Finset.range n, (1 + sineTerm x i)) atTop
    (𝓝 (sin (π * x) / (π * x))) := by
  have h := ((ofReal_ne_zero.mpr Real.pi_ne_zero).isUnit.mul h0.isUnit)
  refine ((tendsto_euler_sin_prod x).div_const₀ (π * x) (hy := h)).congr fun n ↦ ?_
  simp [sineTerm, neg_div₀, sub_eq_add_neg]

private lemma summable_norm_div_add_one_sq (c : ℂ) :
    Summable (fun n : ℕ ↦ ‖c‖ / ‖(n : ℂ) + 1‖ ^ 2) := by
  let q (n : ℕ) : {n : ℕ // n + 1 ≠ 0} := ⟨n, Nat.succ_ne_zero n⟩
  have hq : Function.Injective q := fun _ _ h ↦ congrArg Subtype.val h
  simpa only [Function.comp_def, q, Nat.cast_one, norm_div, norm_pow] using
    (summable_pow_div_add c 2 1 Nat.one_lt_two).comp_injective hq

lemma multipliable_sineTerm (x : ℂ) : Multipliable fun i ↦ (1 + sineTerm x i) := by
  apply multipliable_one_add_of_summable
  refine (summable_norm_div_add_one_sq (-(x ^ 2))).congr fun n ↦ ?_
  dsimp only [sineTerm]
  simp only [norm_div, norm_pow]

/-- Euler's normalized sine product. Its value at zero is the product of constant terms. -/
noncomputable def sineProduct (x : ℂ) : ℂ := ∏' i : ℕ, (1 + sineTerm x i)

@[simp] lemma sineProduct_zero : sineProduct 0 = 1 := by
  simp [sineProduct, sineTerm]

lemma euler_sineTerm_tprod (hx : x ≠ 0) :
    sineProduct x = Complex.sin (π * x) / (π * x) := by
  unfold sineProduct
  rw [← Multipliable.hasProd_iff (multipliable_sineTerm x),
    Multipliable.hasProd_iff_tendsto_nat (multipliable_sineTerm x)]
  exact tendsto_euler_sin_prod' hx

private lemma sineTerm_bound_aux (hZ : IsCompact Z) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ j z, z ∈ Z → ‖sineTerm z j‖ ≤ u j := by
  have hf : ContinuousOn (fun x : ℂ => ‖-x ^ 2‖) Z := by
    fun_prop
  obtain ⟨s, hs⟩ := bddAbove_def.mp (IsCompact.bddAbove_image hZ hf)
  refine ⟨fun n : ℕ => ‖(s : ℂ) / ((n : ℂ) + 1) ^ 2‖, ?_, ?_⟩
  · simpa only [norm_div, norm_pow] using summable_norm_div_add_one_sq (s : ℂ)
  · simp only [norm_neg, norm_pow, Set.mem_image, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, sineTerm, norm_div, norm_real, norm_eq_abs] at *
    intro n x hx
    gcongr
    apply le_trans (hs x hx) (le_abs_self s)

lemma multipliableUniformlyOn_euler_sin_prod_on_compact (hZC : IsCompact Z) :
    MultipliableUniformlyOn (fun n : ℕ => fun z : ℂ => (1 + sineTerm z n)) Z := by
  obtain ⟨u, hu, hu2⟩ := sineTerm_bound_aux hZC
  refine Summable.multipliableUniformlyOn_nat_one_add hZC hu ?_ ?_
  · filter_upwards with n z hz using hu2 n z hz
  · fun_prop

lemma HasProdUniformlyOn_sineTerm_prod_on_compact (hZC : IsCompact Z) :
    HasProdUniformlyOn (fun n : ℕ => fun z : ℂ => (1 + sineTerm z n))
      sineProduct Z :=
  (multipliableUniformlyOn_euler_sin_prod_on_compact hZC).hasProdUniformlyOn

lemma HasProdLocallyUniformlyOn_euler_sin_prod :
    HasProdLocallyUniformlyOn (fun n : ℕ => fun z : ℂ => (1 + sineTerm z n)) sineProduct ℂ_ℤ := by
  apply hasProdLocallyUniformlyOn_of_forall_compact Complex.isOpen_compl_range_intCast
  exact fun _ _ hZC => HasProdUniformlyOn_sineTerm_prod_on_compact hZC

private lemma differentiable_sineTerm_prod (n : ℕ) :
    Differentiable ℂ (fun z : ℂ ↦ ∏ j ∈ Finset.range n, (1 + sineTerm z j)) := by
  fun_prop

private lemma isUnit_sineTerm_prod (hx : x ∈ ℂ_ℤ) (n : ℕ) :
    IsUnit (∏ j ∈ Finset.range n, (1 + sineTerm x j)) :=
  (Finset.prod_ne_zero_iff.mpr fun j _ ↦ sineTerm_ne_zero hx j).isUnit

private lemma differentiableAt_sineProduct (hx : x ∈ ℂ_ℤ) : DifferentiableAt ℂ sineProduct x := by
  have ht := HasProdLocallyUniformlyOn_euler_sin_prod.tendstoLocallyUniformlyOn_finsetRange
  have hd := ht.differentiableOn
    (Eventually.of_forall fun n ↦ (differentiable_sineTerm_prod n).differentiableOn)
    isOpen_compl_range_intCast
  exact (hd x hx).differentiableAt (isOpen_compl_range_intCast.mem_nhds hx)

private lemma isUnit_sineProduct (hx : x ∈ ℂ_ℤ) : IsUnit (sineProduct x) := by
  rw [euler_sineTerm_tprod (integerComplement.ne_zero hx)]
  exact (sin_pi_mul_ne_zero hx).isUnit.div₀
    ((ofReal_ne_zero.mpr Real.pi_ne_zero).isUnit.mul (integerComplement.ne_zero hx).isUnit)

/-- A representative agreeing with cotangent on its domain is smooth there. -/
lemma cot_pi_mul_contDiffWithinAt (k : ℕ∞) (hx : x ∈ ℂ_ℤ) {f : ℂ → ℂ}
    (hf : ∀ y (hy : y ∈ ℂ_ℤ), f y = (↑π * y).cot (sin_pi_mul_ne_zero hy)) :
    ContDiffWithinAt ℂ k f ℂ_ℤ x := by
  have h : ContDiffOn ℂ k f ℂ_ℤ := by
    refine ContDiffOn.div (f := fun y : ℂ ↦ Complex.cos (π * y))
      (g := fun y : ℂ ↦ Complex.sin (π * y))
      (by fun_prop) (by fun_prop) ?_
    exact fun y hy ↦ ⟨(sin_pi_mul_ne_zero hy).isUnit, hf y hy⟩
  exact h x hx

set_option maxHeartbeats 500000 in -- Elaborating the finite-product derivative witnesses.
lemma tendsto_logDeriv_euler_sin_div (hx : x ∈ ℂ_ℤ) :
    Tendsto (fun n : ℕ ↦ logDeriv (fun z ↦ ∏ j ∈ Finset.range n, (1 + sineTerm z j)) x id
        (by exact ((differentiable_sineTerm_prod n) x).existsUnique_hasDerivAt)
        (by exact isUnit_sineTerm_prod hx n)) atTop
      (𝓝 (logDeriv sineProduct x id
        (by exact (differentiableAt_sineProduct hx).existsUnique_hasDerivAt)
        (by exact isUnit_sineProduct hx))) := by
  let G (n : ℕ) (z : ℂ) := ∏ j ∈ Finset.range n, (1 + sineTerm z j)
  have hF : TendstoLocallyUniformlyOn G sineProduct atTop ℂ_ℤ :=
    HasProdLocallyUniformlyOn_euler_sin_prod.tendstoLocallyUniformlyOn_finsetRange
  have hdiff : ∀ᶠ n in atTop, DifferentiableOn ℂ (G n) ℂ_ℤ :=
    .of_forall fun n ↦ (differentiable_sineTerm_prod n).differentiableOn
  have hd := ((hF.deriv hdiff Complex.isOpen_compl_range_intCast).tendsto_at hx)
  have h := hd.div₀ (hF.tendsto_at hx) (h₀ := isUnit_sineTerm_prod hx) (hb := isUnit_sineProduct hx)
  simpa only [logDeriv_apply, Function.comp_def, G] using h

lemma logDeriv_sin_div_eq_cot (hz : x ∈ ℂ_ℤ) :
    logDeriv sineProduct x id (by exact (differentiableAt_sineProduct hz).existsUnique_hasDerivAt)
        (by exact isUnit_sineProduct hz) =
      π * cot (π * x) (sin_pi_mul_ne_zero hz) -
        Checked.div 1 x (integerComplement.ne_zero hz).isUnit := by
  let p (z : ℂ) := sin ((π : ℂ) * z)
  let d (z : ℂ) := (π : ℂ) * z
  let U := {z : ℂ | IsUnit (d z)}
  have hπ : IsUnit (π : ℂ) := (ofReal_ne_zero.mpr Real.pi_ne_zero).isUnit
  have hx : IsUnit x := (integerComplement.ne_zero hz).isUnit
  have hdx : IsUnit (d x) := hπ.mul hx
  have hpx : IsUnit (p x) := (sin_pi_mul_ne_zero hz).isUnit
  let x₀ : U := ⟨x, hdx⟩
  let Q (y : U) := Checked.div (p y) (d y) y.2
  have hd : HasDerivAt d π x := by simpa [d] using (hasDerivAt_id x).const_mul (π : ℂ)
  have hp : HasDerivAt p (cos (π * x) * π) x :=
    (hasDerivAt_sin (π * x)).comp (coord' := id) x hd
  let c := (cos (π * x) * π * d x - p x * π) /ₚ (hdx.unit ^ 2)
  have hQ : HasDerivAt Q c x₀ Subtype.val := hp.div hd hdx
  have hU : IsOpen U := Units.isOpen.preimage (continuous_const.mul continuous_id)
  have he (y : U) : sineProduct y = Q y := by
    have hy : (y : ℂ) ≠ 0 := fun h ↦ y.2.ne_zero (by simp [d, h])
    exact euler_sineTerm_tprod hy
  have hres : HasFDerivAt (fun y : U ↦ sineProduct y) (ContinuousLinearMap.toSpanSingleton ℂ c)
      x₀ Subtype.val := by
    rw [funext he]
    exact hQ.hasFDerivAt
  have hP : HasDerivAt sineProduct c x := by
    have h := HasFDerivAt.of_restrict (f := sineProduct) (coord := id) (x := x₀)
      hres (hU.mem_nhds hdx)
    simpa only [ContinuousLinearMap.toSpanSingleton_apply, one_smul] using h.hasDerivAt
  have hQu := hpx.div₀ hdx
  have hQd := hQ.existsUnique_hasDerivAt hU.isOpenEmbedding_subtypeVal
  have hcmp : logDeriv sineProduct x id (differentiableAt_sineProduct hz).existsUnique_hasDerivAt
        (isUnit_sineProduct hz) = logDeriv Q x₀ Subtype.val hQd hQu := by
    rw [logDeriv_eq hP, logDeriv_eq hQ]
    have hdiv (v w : ℂ) (hv : IsUnit v) (hw : IsUnit w) (h : v = w) :
        Checked.div c v hv = Checked.div c w hw := by subst w; rfl
    exact hdiv _ _ _ _ (he x₀)
  rw [hcmp, logDeriv_div x (hf := hpx) (hg := hdx) hp.differentiableAt hd.differentiableAt
    (hquot := hQd),
    logDeriv_eq hp, logDeriv_eq hd]
  have hden : (π : ℂ) / ((π : ℂ) * x) = 1 / x := by
    apply div_eq_div_iff.mpr
    rw [one_mul]
  change (cos (π * x) * π) / sin (π * x) - (π : ℂ) / ((π : ℂ) * x) = _
  rw [hden, Complex.cot, ← mul_div_assoc₀, mul_comm (Complex.cos (π * x))]

private lemma add_natCast_ne_zero_of_mem_integerComplement (hx : x ∈ ℂ_ℤ) (n : ℕ) :
    x + (n : ℂ) ≠ 0 := by
  simpa only [Int.cast_natCast] using integerComplement_add_ne_zero hx (n : ℤ)

private lemma sub_natCast_ne_zero_of_mem_integerComplement (hx : x ∈ ℂ_ℤ) (n : ℕ) :
    x - (n : ℂ) ≠ 0 := by
  simpa only [sub_eq_add_neg, Int.cast_neg, Int.cast_natCast] using
    integerComplement_add_ne_zero hx (-(n : ℤ))

private lemma add_succ_ne_zero_of_mem_integerComplement (hx : x ∈ ℂ_ℤ) (n : ℕ) :
    x + (n + 1 : ℂ) ≠ 0 := by
  simpa only [Nat.cast_add, Nat.cast_one] using
    add_natCast_ne_zero_of_mem_integerComplement hx (n + 1)

private lemma sub_succ_ne_zero_of_mem_integerComplement (hx : x ∈ ℂ_ℤ) (n : ℕ) :
    x - (n + 1 : ℂ) ≠ 0 := by
  simpa only [Nat.cast_add, Nat.cast_one] using
    sub_natCast_ne_zero_of_mem_integerComplement hx (n + 1)

macro_rules
  | `(tactic| checked_nonzero) => `(tactic|
      solve
      | (apply add_succ_ne_zero_of_mem_integerComplement; assumption)
      | (apply sub_succ_ne_zero_of_mem_integerComplement; assumption)
      | (apply add_natCast_ne_zero_of_mem_integerComplement; assumption)
      | (apply sub_natCast_ne_zero_of_mem_integerComplement; assumption)
      | (apply integerComplement_add_ne_zero; assumption)
      | (apply integerComplement.ne_zero; assumption)
      | (apply sin_pi_mul_ne_zero; assumption))

/-- The term in the infinite sum expansion of cot. -/
noncomputable abbrev cotTerm (x : ℂ) (n : ℕ)
    (_h₁ : x - (n + 1 : ℂ) ≠ 0 := by checked_nonzero)
    (_h₂ : x + (n + 1 : ℂ) ≠ 0 := by checked_nonzero) : ℂ :=
  1 / (x - (n + 1)) + 1 / (x + (n + 1))

lemma logDeriv_sineTerm_eq_cotTerm (hx : x ∈ ℂ_ℤ) (i : ℕ) :
    logDeriv (fun (z : ℂ) ↦ 1 + sineTerm z i) x id
        (by exact (show DifferentiableAt ℂ (fun (z : ℂ) ↦ 1 + sineTerm z i) x by
          fun_prop).existsUnique_hasDerivAt) (sineTerm_ne_zero hx i).isUnit = cotTerm x i := by
  have h₁ := sub_succ_ne_zero_of_mem_integerComplement hx i
  have h₂ := add_succ_ne_zero_of_mem_integerComplement hx i
  have hden := (Nat.cast_add_one_ne_zero (R := ℂ) i).isUnit.pow 2
  have hD₀ := (((hasDerivAt_id x).fun_pow 2).fun_neg.div_const ((i + 1 : ℂ) ^ 2)
    (hd := hden)).const_add 1
  have hD : HasDerivAt (fun z : ℂ ↦ 1 + sineTerm z i) (-2 * x / (i + 1 : ℂ) ^ 2) x := by
    simpa only [sineTerm, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one, neg_mul] using hD₀
  rw [logDeriv_eq hD]
  unfold cotTerm sineTerm
  field_simp
  ring

lemma logDeriv_prod_sineTerm_eq_sum_cotTerm (hx : x ∈ ℂ_ℤ) (n : ℕ) :
    logDeriv (fun (z : ℂ) ↦ ∏ j ∈ Finset.range n, (1 + sineTerm z j)) x id
        (by exact (differentiable_sineTerm_prod n x).existsUnique_hasDerivAt)
        (by exact isUnit_sineTerm_prod hx n) =
      ∑ j ∈ Finset.range n, cotTerm x j := by
  refine (logDeriv_fun_prod (s := Finset.range n) (x := x)
    (f := fun i z ↦ 1 + sineTerm z i) (fun i _ ↦ sineTerm_ne_zero hx i)
    (fun i _ ↦ by fun_prop)).trans ?_
  calc
    _ = ∑ j ∈ (Finset.range n).attach, cotTerm x j.val :=
      Finset.sum_congr rfl fun j _ ↦ logDeriv_sineTerm_eq_cotTerm hx j.val
    _ = _ := Finset.sum_attach (Finset.range n) (fun j : ℕ ↦ cotTerm x j
      (sub_succ_ne_zero_of_mem_integerComplement hx j)
      (add_succ_ne_zero_of_mem_integerComplement hx j))

lemma tendsto_logDeriv_euler_cot_sub (hx : x ∈ ℂ_ℤ) :
    Tendsto (fun n : ℕ => ∑ j ∈ Finset.range n, cotTerm x j) atTop
    (𝓝 <| π * cot (π * x) - 1 / x) := by
  simp_rw [← logDeriv_sin_div_eq_cot hx, ← logDeriv_prod_sineTerm_eq_sum_cotTerm hx]
  simpa using tendsto_logDeriv_euler_sin_div hx

lemma cotTerm_identity (hz : x ∈ ℂ_ℤ) (n : ℕ) :
    cotTerm x n = 2 * x * (1 / ((x + (n + 1)) * (x - (n + 1)))) := by
  have h₁ := (sub_succ_ne_zero_of_mem_integerComplement hz n).isUnit
  have h₂ := (add_succ_ne_zero_of_mem_integerComplement hz n).isUnit
  unfold cotTerm
  field_simp
  ring

private lemma natCast_add_one_injective : Function.Injective (fun n : ℕ ↦ (n : ℤ) + 1) := by
  intro n m h
  exact_mod_cast (add_right_cancel h : (n : ℤ) = m)

lemma summable_cotTerm (hz : x ∈ ℂ_ℤ) : Summable fun n ↦ cotTerm x n := by
  rw [funext fun n ↦ cotTerm_identity hz n]
  apply Summable.mul_left
  have h := EisensteinSeries.summable_linear_sub_mul_linear_add x 1 1
    (fun n : ℕ ↦ (n : ℤ) + 1) natCast_add_one_injective
    (hprod := fun n ↦ by
      simpa only [Int.cast_one, one_mul, Int.cast_add, Int.cast_natCast] using
        (sub_succ_ne_zero_of_mem_integerComplement hz n).isUnit.mul
          (add_succ_ne_zero_of_mem_integerComplement hz n).isUnit)
  simpa only [Int.cast_one, one_mul, mul_one, Int.cast_add, Int.cast_natCast, one_div₀, mul_comm]
    using h

lemma cot_series_rep' (hz : x ∈ ℂ_ℤ) : π * cot (π * x) - 1 / x =
    ∑' n : ℕ, (1 / (x - (n + 1)) + 1 / (x + (n + 1))) := by
  rw [HasSum.tsum_eq]
  apply (Summable.hasSum_iff_tendsto_nat (summable_cotTerm hz)).mpr
    (tendsto_logDeriv_euler_cot_sub hz)

/-- The cotangent infinite sum representation. -/
theorem cot_series_rep (hz : x ∈ ℂ_ℤ) :
    π * cot (π * x) = 1 / x + ∑' n : ℕ+, (1 / (x - n) + 1 / (x + n)) := by
  have h0 := tsum_pnat_eq_tsum_succ (f := fun n ↦ 1 / (x - n) + 1 / (x + n))
  have h1 := cot_series_rep' hz
  simp only [one_div₀, Nat.cast_add, Nat.cast_one] at *
  rw [h0, ← h1]
  ring

end MittagLeffler

section iteratedDeriv

open Filter Set
open scoped Nat Topology

private noncomputable def cotReciprocalPower (k : ℕ) (n : ℤ) (z : ℂ_ℤ) : ℂ :=
  Checked.zpow (z.val + n) (-((k + 1 : ℕ) : ℤ))
    (fun _ ↦ (integerComplement_add_ne_zero z.property n).isUnit)

private lemma cotReciprocalPower_eq_div (k : ℕ) (n : ℤ) (z : ℂ_ℤ) :
    cotReciprocalPower k n z =
      Checked.div 1 ((z.val + n) ^ (k + 1))
        ((integerComplement_add_ne_zero z.property n).isUnit.pow _) := by
  simp only [cotReciprocalPower, zpow_neg₀ (integerComplement_add_ne_zero z.property n),
    zpow_natCast₀, one_div₀]

private noncomputable def cotDerivativeTerm (k : ℕ) (n : ℤ) (z : ℂ_ℤ) : ℂ :=
  (-1) ^ k * k ! * cotReciprocalPower k n z

private lemma hasDerivAt_cotDerivativeTerm (k : ℕ) (n : ℤ) (z : ℂ_ℤ) :
    HasDerivAt (cotDerivativeTerm k n) (cotDerivativeTerm (k + 1) n z) z Subtype.val := by
  let m : ℤ := -((k + 1 : ℕ) : ℤ)
  let q (y : ℂ_ℤ) : {u : ℂ // m < 0 → IsUnit u} :=
    ⟨y.val + n, fun _ ↦ (integerComplement_add_ne_zero y.property n).isUnit⟩
  have hlinear : HasDerivAt (Subtype.val ∘ q) 1 z Subtype.val := by
    have h := ((hasDerivAt_id z.val).add_const (n : ℂ)).hasFDerivAt.comp_tendsto Subtype.val
      (continuous_subtype_val.continuousAt.tendsto.prodMap (tendsto_pure_pure Subtype.val z))
    simpa only [q, Function.comp_def, id_eq, ContinuousLinearMap.toSpanSingleton_apply, one_smul]
      using hasFDerivAt_iff_hasDerivAt.mp h
  have hpower := (hasDerivAt_zpow m (q z)).comp (h := q) z hlinear
    continuous_subtype_val.continuousAt Topology.IsEmbedding.subtypeVal
  have hm : m ≠ 0 := by dsimp [m]; omega
  have hm' : m - 1 = -((k + 1 + 1 : ℕ) : ℤ) := by dsimp [m]; omega
  have hmcast : (m : ℂ) = -((k : ℂ) + 1) := by
    exact_mod_cast (show m = -((k : ℤ) + 1) by dsimp [m])
  have hcoeff : ((-1 : ℂ) ^ k * k !) * (m : ℂ) = (-1) ^ (k + 1) * (k + 1) ! := by
    rw [hmcast, pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
    ring
  change HasDerivAt (fun y : ℂ_ℤ ↦ cotDerivativeTerm k n y) _ z Subtype.val
  simpa only [cotDerivativeTerm, cotReciprocalPower, Function.comp_def, q, dite_eq_right hm,
    mul_one, ← mul_assoc, hcoeff, hm'] using hpower.const_mul ((-1 : ℂ) ^ k * k !)

private lemma norm_cotDerivativeTerm (k : ℕ) (n : ℤ) (z : ℂ_ℤ) :
    ‖cotDerivativeTerm k n z‖ = (k ! : ℝ) * ‖z.val + n‖ ^ (-((k + 1 : ℕ) : ℝ)) := by
  have hpow := Real.rpow_intCast ‖z.val + n‖ (-((k + 1 : ℕ) : ℤ))
    (h := fun _ ↦ norm_ne_zero_iff.mpr (integerComplement_add_ne_zero z.property n))
  simp only [cotDerivativeTerm, cotReciprocalPower, norm_mul, norm_pow, norm_neg, norm_one,
    one_pow, one_mul, Complex.norm_natCast, norm_zpow, ← hpow, Int.cast_neg, Int.cast_natCast]

/-- The zero term is taken separately, and opposite nonzero shifts are paired. -/
private noncomputable def cotSeriesTerm (k : ℕ) : ℕ → ℂ_ℤ → ℂ
  | 0 => cotDerivativeTerm k 0
  | n + 1 => fun z ↦ cotDerivativeTerm k (-(n + 1 : ℤ)) z + cotDerivativeTerm k (n + 1) z

private lemma hasDerivAt_cotSeriesTerm (k n : ℕ) (z : ℂ_ℤ) :
    HasDerivAt (cotSeriesTerm k n) (cotSeriesTerm (k + 1) n z) z Subtype.val := by
  cases n with
  | zero => exact hasDerivAt_cotDerivativeTerm k 0 z
  | succ n =>
    have h := (hasDerivAt_cotDerivativeTerm k (-(n + 1 : ℤ)) z).hasFDerivAt.add
      (hasDerivAt_cotDerivativeTerm k (n + 1) z).hasFDerivAt
    simpa only [cotSeriesTerm, hasDerivAt_iff_hasFDerivAt,
      ContinuousLinearMap.toSpanSingleton_add, Pi.add_def] using h

private lemma cotSeriesTerm_zero_zero (z : ℂ_ℤ) :
    cotSeriesTerm 0 0 z = Checked.div 1 z.val (integerComplement.ne_zero z.property).isUnit := by
  simp only [cotSeriesTerm, cotDerivativeTerm, cotReciprocalPower_eq_div, pow_zero,
    Nat.factorial_zero, Nat.cast_one, one_mul, Int.cast_zero, add_zero, Nat.zero_add, pow_one]

private lemma cotSeriesTerm_zero_succ (n : ℕ) (z : ℂ_ℤ) :
    cotSeriesTerm 0 (n + 1) z = cotTerm z.val n
      (sub_succ_ne_zero_of_mem_integerComplement z.property n)
      (add_succ_ne_zero_of_mem_integerComplement z.property n) := by
  simp only [cotSeriesTerm, cotDerivativeTerm, cotReciprocalPower_eq_div, cotTerm, pow_zero,
    Nat.factorial_zero, Nat.cast_one, one_mul, Int.cast_add, Int.cast_one, Int.cast_natCast,
    Int.cast_neg, Nat.zero_add, pow_one, sub_eq_add_neg]

private lemma summable_cotSeriesTerm_zero (z : ℂ_ℤ) :
    Summable (fun n ↦ cotSeriesTerm 0 n z) := by
  apply (summable_nat_add_iff 1).mp
  simpa only [cotSeriesTerm_zero_succ] using summable_cotTerm z.property

set_option maxHeartbeats 1000000 in -- Normalizing cast norms and real powers in the compact bound.
private lemma summableLocallyUniformlyOn_cotSeriesTerm {k : ℕ} (hk : 1 ≤ k) :
    SummableLocallyUniformlyOn (cotSeriesTerm k) (univ : Set ℂ_ℤ) := by
  let : LocallyCompactSpace ℂ_ℤ :=
    Complex.isOpen_compl_range_intCast.isOpenEmbedding_subtypeVal.locallyCompactSpace
  apply SummableLocallyUniformlyOn.of_locally_bounded_eventually isOpen_univ
  intro K _ hK
  obtain ⟨M, hM⟩ := hK.bddAbove_image (continuous_norm.comp continuous_subtype_val).continuousOn
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * M)
  let p : ℝ := -((k + 1 : ℕ) : ℝ)
  have hp : p < -1 := by
    have hk' : (1 : ℝ) < ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < k + 1)
    dsimp [p]; linarith
  refine ⟨fun n : ℕ ↦ ((k ! : ℝ) * (2 * (1 / 2 : ℝ) ^ p)) * (n : ℝ) ^ p,
    (summable_nat_rpow.mpr hp).mul_left _, ?_⟩
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_ge_atTop (N + 1)] with n hn z hz
  cases n with
  | zero => omega
  | succ n =>
    have hlarge : 2 * M < ((n + 1 : ℕ) : ℝ) :=
      hN.trans_le (by exact_mod_cast (by omega : N ≤ n + 1))
    have hzM : ‖z.val‖ ≤ M := hM ⟨z, hz, rfl⟩
    have hterm (d : ℤ) (hd : ‖(d : ℂ)‖ = ((n + 1 : ℕ) : ℝ)) :
        ‖cotDerivativeTerm k d z‖ ≤
          (k ! : ℝ) * ((1 / 2 : ℝ) ^ p * ((n + 1 : ℕ) : ℝ) ^ p) := by
      have htri : ‖(d : ℂ)‖ ≤ ‖z.val + (d : ℂ)‖ + ‖z.val‖ := by
        simpa only [add_sub_cancel_left] using norm_sub_le (z.val + (d : ℂ)) z.val
      have hsub : (1 / 2 : ℝ) * ((n + 1 : ℕ) : ℝ) ≤ ‖z.val + (d : ℂ)‖ := by
        rw [hd] at htri
        linarith
      rw [norm_cotDerivativeTerm]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [← Real.mul_rpow (by positivity) (by positivity)]
      exact Real.rpow_le_rpow_of_nonpos (by positivity) hsub (hp.le.trans (by norm_num))
    have hnorm : ‖((n + 1 : ℤ) : ℂ)‖ = ((n + 1 : ℕ) : ℝ) := by
      rw [← Int.natCast_succ, Int.cast_natCast, Complex.norm_natCast]
    have hpos := hterm (n + 1) hnorm
    have hneg := hterm (-(n + 1 : ℤ)) (by simpa only [Int.cast_neg, norm_neg] using hnorm)
    exact (norm_add_le _ _).trans ((add_le_add hneg hpos).trans_eq (by ring))

private lemma summable_cotReciprocalPower {k : ℕ} (hk : 1 ≤ k) (z : ℂ_ℤ) :
    Summable (fun n : ℤ ↦ cotReciprocalPower k n z) := by
  have h := EisensteinSeries.linear_right_summable z.val 1
    (k := ((k + 1 : ℕ) : ℤ)) (by omega) id Function.injective_id
    (hpower := fun n ↦ by
      simpa only [Int.cast_one, one_mul, id_eq, zpow_natCast₀] using
        (integerComplement_add_ne_zero z.property n).isUnit.pow (k + 1))
  refine h.congr fun n ↦ ?_
  simp only [id_eq, Int.cast_one, one_mul, zpow_natCast₀, cotReciprocalPower_eq_div, one_div₀]

set_option maxHeartbeats 1000000 in -- Reindexing the integer and natural derivative sums.
private lemma tsum_cotSeriesTerm {k : ℕ} (hk : 1 ≤ k) (z : ℂ_ℤ) :
    (∑' n : ℕ, cotSeriesTerm k n z) = (-1) ^ k * k ! * ∑' n : ℤ, cotReciprocalPower k n z := by
  let A : ℂ := (-1) ^ k * (k.factorial : ℂ)
  let f (n : ℤ) : ℂ := cotReciprocalPower k n z
  let p (n : ℕ) : ℂ := f (n + 1)
  let q (n : ℕ) : ℂ := f (-(n + 1 : ℤ))
  have hsum : Summable f := summable_cotReciprocalPower hk z
  have hpos : Summable p :=
    hsum.comp_injective natCast_add_one_injective
  have hneg : Summable q :=
    hsum.comp_injective (neg_injective.comp natCast_add_one_injective)
  have h : Summable (fun n : ℕ ↦ cotSeriesTerm k n z) :=
    (summableLocallyUniformlyOn_cotSeriesTerm hk).summable (mem_univ z)
  have hZ : (∑' n : ℤ, f n) = (∑' n : ℕ, p n) + f 0 + ∑' n : ℕ, q n :=
    tsum_of_add_one_of_neg_add_one hpos hneg
  change (∑' n : ℕ, cotSeriesTerm k n z) = A * ∑' n : ℤ, f n
  calc
    _ = cotSeriesTerm k 0 z + ∑' n : ℕ, cotSeriesTerm k (n + 1) z := h.tsum_eq_zero_add
    _ = A * f 0 + ∑' n : ℕ, (A * q n + A * p n) := rfl
    _ = A * f 0 + (A * (∑' n : ℕ, q n) + A * ∑' n : ℕ, p n) := by
      rw [Summable.tsum_add (hneg.mul_left A) (hpos.mul_left A), tsum_mul_left, tsum_mul_left]
    _ = _ := by
      simp only [hZ, mul_add]
      ac_rfl

/-- The series expansion of the iterated derivative of `π cot (π z)` on the complement of
the integers. -/
theorem hasIteratedDerivAt_cot_pi_mul {k : ℕ} (hk : 1 ≤ k) (z : ℂ_ℤ) :
    HasIteratedDerivAt k (fun y : ℂ_ℤ ↦ π * cot (π * y.val) (sin_pi_mul_ne_zero y.property))
      ((-1) ^ k * k ! * ∑' n : ℤ, Checked.div 1 ((z.val + n) ^ (k + 1))
        ((integerComplement_add_ne_zero z.property n).isUnit.pow _)) z Subtype.val := by
  have h := hasIteratedDerivAt_tsum_subtype (s := ℂ_ℤ) (f := cotSeriesTerm)
    Complex.isOpen_compl_range_intCast hasDerivAt_cotSeriesTerm summable_cotSeriesTerm_zero
    (fun j ↦ summableLocallyUniformlyOn_cotSeriesTerm (k := j + 1) (by omega)) k z
  rw [tsum_cotSeriesTerm hk, tsum_congr (fun n ↦ cotReciprocalPower_eq_div k n z)] at h
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun y ↦ ?_)
  change π * cot (π * y.val) (sin_pi_mul_ne_zero y.property) = ∑' i, cotSeriesTerm 0 i y
  rw [(summable_cotSeriesTerm_zero y).tsum_eq_zero_add, cotSeriesTerm_zero_zero]
  simp only [cotSeriesTerm_zero_succ, cotTerm]
  exact (sub_eq_iff_eq_add'.mp (cot_series_rep' y.property))

end iteratedDeriv
