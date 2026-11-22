/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Complex.SummableUniformlyOn
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
public import Mathlib.NumberTheory.ModularForms.LevelOne.Basic
public import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
public import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.LinearCombination

/-!
# Eisenstein series q-expansions

We give the q-expansion of Eisenstein series of weight `k` and level 1. In particular, we prove
`EisensteinSeries.q_expansion_bernoulli` which says that for even `k` with `3 ≤ k`
Eisenstein series can be written as `1 - (2k / bernoulli k) ∑' n, σ_{k-1}(n) q^n` where
`q = exp(2πiz)` and `σ_{k-1}(n)` is the sum of the `(k-1)`-th powers of the divisors of `n`.
We need `k` to be even so that the Eisenstein series are non-zero and we require `k ≥ 3` so that
the series converges absolutely.

We also identify the q-expansion coefficients as a `PowerSeries` via
`EisensteinSeries.E_qExpansion_coeff`, and use this to prove that the normalised Eisenstein series
is non-zero (`EisensteinSeries.E_ne_zero`).

The proof relies on the identity
`∑' n : ℤ, 1 / (z + n) ^ (k + 1) = ((-2πi)^(k+1) / k!) ∑' n : ℕ, n^k q^n` which comes from
differentiating the expansion of `π cot(πz)` in terms of exponentials. Since our Eisenstein series
are defined as sums over coprime integer pairs, we also need to relate these to sums over all pairs
of integers, which is done in `tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries`. This then
gives the q-expansion with a Riemann zeta factor, which we simplify using the formula for
`ζ(k)` in terms of Bernoulli numbers to get the final result.

-/

public section

open Set Metric TopologicalSpace Function Filter Complex ArithmeticFunction
  ModularForm EisensteinSeries

open scoped Real Nat ArithmeticFunction.sigma Topology

open UpperHalfPlane hiding I

local notation "ℍₒ" => upperHalfPlaneSet

private lemma iteratedDerivWithin_cexp_aux (k m : ℕ) (p : ℝ) {hp : IsUnit (p : ℂ)}
    {S : Set ℂ} (hs : IsOpen S) :
    EqOn (iteratedDerivWithin k (fun s : ℂ ↦ cexp (2 * π * I * m * s / (p : ℂ))) S)
    (fun s ↦ (2 * π * I * m / (p : ℂ)) ^ k * cexp (2 * π * I * m * s / (p : ℂ))) S := by
  apply EqOn.trans (iteratedDerivWithin_of_isOpen hs)
  intro x hx
  have : (fun s ↦ cexp (2 * π * I * m * s / (p : ℂ))) =
      fun s ↦ cexp (((2 * π * I * m) / (p : ℂ)) * s) := by
    ext z
    ring_nf
  simp only [this, iteratedDeriv_cexp_const_mul]
  ring_nf

private lemma aux_IsBigO_mul (k l : ℕ) (p : ℝ) {hp : IsUnit (p : ℂ)} {f : ℕ → ℂ}
    (hf : f =O[atTop] fun n ↦ ((n ^ l) : ℝ)) :
    (fun n ↦ f n * (2 * π * I * n / (p : ℂ)) ^ k) =O[atTop] fun n ↦ (↑(n ^ (l + k)) : ℝ) := by
  have h0 : (fun n : ℕ ↦ (2 * π * I * n / (p : ℂ)) ^ k) =O[atTop] fun n ↦ ((n ^ k) : ℝ) := by
    have h1 : (fun n : ℕ ↦ (2 * π * I * n / (p : ℂ)) ^ k) =
        fun n : ℕ ↦ ((2 * π * I / (p : ℂ)) ^ k) * n ^ k := by
      ext z
      ring
    rw [h1]
    simpa only [Nat.cast_pow, Complex.ofReal_pow, Complex.ofReal_natCast] using!
      isBigO_ofReal_right.mp (Asymptotics.isBigO_const_mul_self
        ((2 * π * I / (p : ℂ)) ^ k) (fun (n : ℕ) ↦ (↑(n ^ k) : ℝ)) atTop)
  push_cast
  convert! hf.mul h0
  ring

open BoundedContinuousFunction in
/-- The infinite sum of `k`-th iterated derivative of the complex exponential multiplied by a
function that grows polynomially is absolutely and uniformly convergent. -/
theorem summableLocallyUniformlyOn_iteratedDerivWithin_smul_cexp (k l : ℕ) {f : ℕ → ℂ} {p : ℝ}
    (hp : 0 < p) (hf : f =O[atTop] (fun n ↦ ((n ^ l) : ℝ))) :
    SummableLocallyUniformlyOn (fun n ↦ (f n) •
      iteratedDerivWithin k (fun z ↦ cexp (Checked.div (2 * π * I * z) (p : ℂ)
        (Complex.ofReal_ne_zero.mpr hp.ne').isUnit) ^ n) ℍₒ) ℍₒ := by
  have hpu := (Complex.ofReal_ne_zero.mpr hp.ne').isUnit
  apply SummableLocallyUniformlyOn_of_locally_bounded isOpen_upperHalfPlaneSet
  intro K hK hKc
  have : CompactSpace K := isCompact_univ_iff.mp (isCompact_iff_isCompact_univ.mp hKc)
  let c : ContinuousMap K ℂ := ⟨fun r : K ↦ Complex.exp (2 * π * I * r / (p : ℂ)), by fun_prop⟩
  let r : ℝ := ‖mkOfCompact c‖
  have hr : ‖r‖ < 1 := by
    simp only [norm_norm, r, norm_lt_iff_of_compact Real.zero_lt_one, mkOfCompact_apply,
      ContinuousMap.coe_mk, c]
    intro x
    have h1 : cexp (2 * π * I * ((x : ℂ) / (p : ℂ))) = cexp (2 * π * I * x / (p : ℂ)) := by
      ring_nf
    have hx : 0 < (x : ℂ).im := hK x.property
    have hx' : 0 < (((x : ℂ) / (p : ℂ) : ℂ)).im := by
      rw [Complex.div_ofReal_im]
      exact div_pos hx hp
    simpa using h1 ▸ norm_exp_two_pi_I_lt_one ⟨((x : ℂ) / (p : ℂ)), hx'⟩
  have hpabs : IsUnit |p| := (abs_pos.mpr hp.ne').isUnit
  refine ⟨fun n ↦ ‖f n‖ * (Checked.div (2 * π * n) |p| hpabs) ^ k * |r| ^ n, by
    simpa using (summable_norm_mul_geometric_of_norm_lt_one' hr
      (Asymptotics.isBigO_norm_left.mpr (aux_IsBigO_mul k l p (hp := hpu) hf))), fun n z hz ↦ ?_⟩
  have h0 := pow_le_pow_left₀ (norm_nonneg _) (norm_coe_le_norm (mkOfCompact c) ⟨z, hz⟩) n
  simp only [norm_mkOfCompact, mkOfCompact_apply, ContinuousMap.coe_mk, ← exp_nsmul', Pi.smul_apply,
    iteratedDerivWithin_cexp_aux k n p (hp := hpu) isOpen_upperHalfPlaneSet (hK hz), smul_eq_mul,
    norm_mul, norm_pow, Complex.norm_div, norm_ofNat, norm_real, Real.norm_eq_abs, norm_I, mul_one,
    norm_natCast, abs_norm, ge_iff_le, Real.abs_pi, r, c] at *
  rw [← mul_assoc]
  gcongr
  · exact (div_pow₀ _ _ _).le
  · simpa only [exp_nsmul' z (2 * π * I) p (hp := hpu), norm_pow] using! h0

/-- This is a version of `summableLocallyUniformlyOn_iteratedDerivWithin_smul_cexp` for level one
and q-expansion coefficients all `1`. -/
theorem summableLocallyUniformlyOn_iteratedDerivWithin_cexp (k : ℕ) :
    SummableLocallyUniformlyOn
      (fun n ↦ iteratedDerivWithin k (fun z ↦ cexp (2 * π * I * z) ^ n) ℍₒ) ℍₒ := by
  have h0 : (fun n : ℕ ↦ (1 : ℂ)) =O[atTop] fun n ↦ ((n ^ 1) : ℝ) := by
    simp only [Asymptotics.isBigO_iff, norm_one, norm_pow, Real.norm_natCast, eventually_atTop]
    exact ⟨1, 1, fun b hb ↦ by norm_cast; simp [hb]⟩
  simpa using summableLocallyUniformlyOn_iteratedDerivWithin_smul_cexp k 1 (p := 1)
    (by norm_num) h0

lemma differentiableAt_iteratedDerivWithin_cexp (n a : ℕ) {s : Set ℂ} (hs : IsOpen s)
    {r : ℂ} (hr : r ∈ s) : DifferentiableAt ℂ
      (iteratedDerivWithin a (fun z ↦ cexp (2 * π * I * z) ^ n) s) r := by
  apply DifferentiableOn.differentiableAt _ (hs.mem_nhds hr)
  suffices DifferentiableOn ℂ (iteratedDeriv a (fun z ↦ cexp (2 * π * I * z) ^ n)) s by
    apply this.congr (iteratedDerivWithin_of_isOpen hs)
  fun_prop

lemma iteratedDerivWithin_tsum_cexp_eq (k : ℕ) (z : ℍ) :
    iteratedDerivWithin k (fun z ↦ ∑' n : ℕ, cexp (2 * π * I * z) ^ n) ℍₒ z =
    ∑' n : ℕ, iteratedDerivWithin k (fun s : ℂ ↦ cexp (2 * π * I * s) ^ n) ℍₒ z := by
  rw [iteratedDerivWithin_tsum k isOpen_upperHalfPlaneSet (by simpa using z.2)]
  · exact fun x hx ↦ summable_geometric_iff_norm_lt_one.mpr
      (UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨x, hx⟩)
  · exact fun n _ _ ↦ summableLocallyUniformlyOn_iteratedDerivWithin_cexp n
  · exact fun n l z hl hz ↦ differentiableAt_iteratedDerivWithin_cexp n l
      isOpen_upperHalfPlaneSet hz

lemma contDiffOn_tsum_cexp (k : ℕ∞) :
    ContDiffOn ℂ k (fun z : ℂ ↦ ∑' n : ℕ, cexp (2 * π * I * z) ^ n) ℍₒ :=
  contDiffOn_of_differentiableOn_deriv fun m _ z hz ↦
  (((summableLocallyUniformlyOn_iteratedDerivWithin_cexp m).differentiableOn
  isOpen_upperHalfPlaneSet (fun n _ hz ↦ differentiableAt_iteratedDerivWithin_cexp n m
  isOpen_upperHalfPlaneSet hz)) z hz).congr (fun z hz ↦ iteratedDerivWithin_tsum_cexp_eq m ⟨z, hz⟩)
  (iteratedDerivWithin_tsum_cexp_eq m ⟨z, hz⟩)

private lemma iteratedDerivWithin_tsum_exp_aux_eq {k : ℕ} (hk : 1 ≤ k) (z : ℍ) :
    iteratedDerivWithin k (fun z ↦ ((π * I) -
    (2 * π * I) * ∑' n : ℕ, cexp (2 * π * I * z) ^ n)) ℍₒ z =
    -(2 * π * I) ^ (k + 1) * ∑' n : ℕ, n ^ k * cexp (2 * π * I * z) ^ n := by
  have : iteratedDerivWithin k (fun z ↦ ((π * I) -
    (2 * π * I) * ∑' n : ℕ, cexp (2 * π * I * z) ^ n)) ℍₒ z =
    -(2 * π * I) * ∑' n : ℕ, iteratedDerivWithin k (fun s : ℂ ↦ cexp (2 * π * I * s) ^ n) ℍₒ z := by
    rw [iteratedDerivWithin_const_sub hk, iteratedDerivWithin_fun_neg,
      iteratedDerivWithin_const_mul (by simpa using z.2) (isOpen_upperHalfPlaneSet.uniqueDiffOn)]
    · simp only [iteratedDerivWithin_tsum_cexp_eq, neg_mul]
    · exact (contDiffOn_tsum_cexp k).contDiffWithinAt (by simpa using z.2)
  have h : -(2 * π * I * (2 * π * I) ^ k) * ∑' (n : ℕ), n ^ k * cexp (2 * π * I * z) ^ n =
        -(2 * π * I) * ∑' n : ℕ, (2 * π * I * n) ^ k * cexp (2 * π * I * z) ^ n := by
    simp_rw [← tsum_mul_left]
    congr
    ext y
    ring
  simp only [this, neg_mul, pow_succ', h, neg_inj, mul_eq_mul_left_iff, mul_eq_zero,
    OfNat.ofNat_ne_zero, ofReal_eq_zero, Real.pi_ne_zero, or_self, I_ne_zero, or_false]
  congr
  ext n
  have := exp_nsmul' (p := 1) (hp := isUnit_one) (a := 2 * π * I) (n := n)
  simp_rw [div_one₀] at this
  simpa [this, UpperHalfPlane.coe] using
    iteratedDerivWithin_cexp_aux k n 1 (hp := by simp) isOpen_upperHalfPlaneSet z.2

private lemma hasIteratedDerivAt_subtype_of_contDiffOn {s : Set ℂ} (hs : IsOpen s)
    (k : ℕ) {f : ℂ → ℂ} (hf : ContDiffOn ℂ (k : ℕ∞) f s) (z : s) :
    HasIteratedDerivAt k (fun y : s ↦ f y.val) (iteratedDerivWithin k f s z.val)
      z Subtype.val := by
  induction k generalizing f with
  | zero => simp only [HasIteratedDerivAt.zero, iteratedDerivWithin_zero]
  | succ k ih =>
    have hderiv (y : s) : HasDerivAt (fun w : s ↦ f w.val) (derivWithin f s y.val)
        y Subtype.val := by
      have h := ((hf.differentiableOn (by simp) y.val y.property).hasDerivWithinAt.hasDerivAt
        (hs.mem_nhds y.property)).hasFDerivAt.comp_tendsto Subtype.val
        (continuous_subtype_val.continuousAt.tendsto.prodMap (tendsto_pure_pure Subtype.val y))
      simpa only [Function.comp_def, id_eq, ContinuousLinearMap.toSpanSingleton_apply, one_smul]
        using hasFDerivAt_iff_hasDerivAt.mp h
    rw [iteratedDerivWithin_succ']
    exact ⟨fun y : s ↦ derivWithin f s y.val, hderiv z, Or.inr (.of_forall hderiv),
      ih (hf.derivWithin hs.uniqueDiffOn (by simp))⟩

/-- This is one key identity relating infinite series to q-expansions which shows that
`∑' n, 1 / (z + n) ^ (k + 1) = ((-2 π I) ^ (k + 1) / k !) * ∑' n, n ^ k q ^n` where
`q = cexp (2 π I z)`. -/
theorem EisensteinSeries.qExpansion_identity {k : ℕ} (hk : 1 ≤ k) (z : ℍ) :
    (∑' n : ℤ, Checked.div 1 (((z : ℂ) + n) ^ (k + 1))
      ((integerComplement_add_ne_zero z.coe_mem_integerComplement n).isUnit.pow _)) =
      Checked.div ((-2 * π * I) ^ (k + 1)) (k ! : ℂ)
        (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)).isUnit *
      ∑' n : ℕ, n ^ k * cexp (2 * π * I * z) ^ n := by
  let z₀ : ℍₒ := ⟨z, z.im_pos⟩
  let q (y : ℍₒ) : integerComplement := ⟨y.val, coe_mem_integerComplement ⟨y.val, y.property⟩⟩
  let F (y : ℂ) : ℂ := π * I - (2 * π * I) * ∑' n : ℕ, cexp (2 * π * I * y) ^ n
  let A : ℂ := ∑' n : ℤ, Checked.div 1 (((z : ℂ) + n) ^ (k + 1))
    ((integerComplement_add_ne_zero z.coe_mem_integerComplement n).isUnit.pow _)
  let B : ℂ := ∑' n : ℕ, n ^ k * cexp (2 * π * I * z) ^ n
  have hF : ContDiffOn ℂ (k : ℕ∞) F ℍₒ :=
    contDiffOn_const.sub (contDiffOn_const.mul (contDiffOn_tsum_cexp k))
  have hleft : HasIteratedDerivAt k (fun y : ℍₒ ↦ F y.val) ((-1) ^ k * k ! * A)
      z₀ Subtype.val := by
    have h := (hasIteratedDerivAt_cot_pi_mul hk (q z₀)).comp_domain (g := q)
      (continuous_subtype_val.subtype_mk _)
    exact h.congr_of_eventuallyEq
      (.of_forall fun y ↦ (pi_mul_cot_pi_q_exp ⟨y.val, y.property⟩).symm)
  have heq : (-1) ^ k * k ! * A = -(2 * π * I) ^ (k + 1) * B :=
    (hleft.unique
      (hasIteratedDerivAt_subtype_of_contDiffOn isOpen_upperHalfPlaneSet k hF z₀)
      isOpen_upperHalfPlaneSet.isOpenEmbedding_subtypeVal).trans
        (iteratedDerivWithin_tsum_exp_aux_eq hk z)
  have hfact : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hneg : ((-1 : ℂ) ^ k) ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  change A = Checked.div ((-2 * π * I) ^ (k + 1)) (k ! : ℂ) hfact.isUnit * B
  apply mul_left_cancel₀ (mul_ne_zero hneg hfact)
  rw [heq]
  have hpow : (-2 * π * I : ℂ) ^ (k + 1) = (-1) ^ (k + 1) * (2 * π * I) ^ (k + 1) := by
    rw [← mul_pow]
    congr 1
    ring
  have hsign : (-1 : ℂ) ^ k * (-1) ^ (k + 1) = -1 := by
    rw [← pow_add, show k + (k + 1) = 2 * k + 1 by omega, pow_succ, pow_mul]
    norm_num
  rw [hpow]
  calc
    -(2 * π * I) ^ (k + 1) * B = ((-1) ^ k * (-1) ^ (k + 1)) * (2 * π * I) ^ (k + 1) * B := by
      rw [hsign]
      ring
    _ = _ := by field_simp

lemma summable_pow_mul_cexp (k : ℕ) (e : ℕ+) (z : ℍ) :
    Summable fun c : ℕ ↦ (c : ℂ) ^ k * cexp (2 * π * I * e * z) ^ c := by
  have he : 0 < (e * (z : ℂ)).im := by
    simpa using z.2
  apply ((summableLocallyUniformlyOn_iteratedDerivWithin_smul_cexp 0 k (p := 1)
    (f := fun n ↦ (n ^ k : ℂ)) (by norm_num)
    (by simp [← Complex.isBigO_ofReal_right, Asymptotics.isBigO_refl])).summable he).congr
  intro n
  simp only [ofReal_one, div_one₀, iteratedDerivWithin_zero, Pi.smul_apply, smul_eq_mul, mul_assoc]

/-- This is a version of `EisensteinSeries.qExpansion_identity` for positive naturals,
which shows that  `∑' n, 1 / (z + n) ^ (k + 1) = ((-2 π I) ^ (k + 1) / k !) * ∑' n : ℕ+, n ^ k q ^n`
where `q = cexp (2 π I z)`. -/
theorem EisensteinSeries.qExpansion_identity_pnat {k : ℕ} (hk : 1 ≤ k) (z : ℍ) :
    (∑' n : ℤ, Checked.div 1 (((z : ℂ) + n) ^ (k + 1))
      ((integerComplement_add_ne_zero z.coe_mem_integerComplement n).isUnit.pow _)) =
      Checked.div ((-2 * π * I) ^ (k + 1)) (k ! : ℂ)
        (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)).isUnit *
      ∑' n : ℕ+, n ^ k * cexp (2 * π * I * z) ^ (n : ℕ) := by
  rw [EisensteinSeries.qExpansion_identity hk z, ← tsum_zero_pnat_eq_tsum_nat]
  · simp [show k ≠ 0 by grind]
  · apply (summable_pow_mul_cexp k 1 z).congr
    simp

lemma summable_eisSummand {k : ℕ} (hk : 3 ≤ k) (z : ℍ) :
    Summable (fun v : {v : Fin 2 → ℤ // v ≠ 0} ↦ eisSummand k v z (fun _ ↦ v.property)) :=
  summable_norm_iff.mp (summable_norm_eisSummand (by exact_mod_cast hk) z)

lemma eisensteinPair_ne_zero {a b : ℤ} (h : a ≠ 0 ∨ b ≠ 0) :
    (![a, b] : Fin 2 → ℤ) ≠ 0 := by
  intro hv
  rcases h with h | h
  · exact h (by simpa using congrFun hv (0 : Fin 2))
  · exact h (by simpa using congrFun hv (1 : Fin 2))

/-- A nonzero lattice vector has either zero first coordinate and a nonzero second coordinate,
or a nonzero first coordinate and an arbitrary second coordinate. -/
private def nonzeroLatticeEquiv :
    {v : Fin 2 → ℤ // v ≠ 0} ≃ ({d : ℤ // d ≠ 0} ⊕ ({c : ℤ // c ≠ 0} × ℤ)) where
  toFun v := if h : v.val 0 = 0 then
    .inl ⟨v.val 1, fun h₁ ↦ v.property (by
      ext i
      fin_cases i <;> assumption)⟩
    else .inr (⟨v.val 0, h⟩, v.val 1)
  invFun := Sum.elim (fun d ↦ ⟨![0, d.val], eisensteinPair_ne_zero (.inr d.property)⟩)
    (fun a ↦ ⟨![a.1.val, a.2], eisensteinPair_ne_zero (.inl a.1.property)⟩)
  left_inv := by
    rintro ⟨v, hv⟩
    dsimp
    split_ifs with h
    · apply Subtype.ext
      ext i
      fin_cases i <;> simp [h]
    · apply Subtype.ext
      ext i
      fin_cases i <;> simp
  right_inv := by
    rintro (d | ⟨a, d⟩)
    · simp
    · simp [a.property]

lemma summable_prod_eisSummand {k : ℕ} (hk : 3 ≤ k) (z : ℍ) :
    Summable (fun p : {c : ℤ // c ≠ 0} × ℤ ↦
      eisSummand k ![p.1.val, p.2] z (fun _ ↦ eisensteinPair_ne_zero (.inl p.1.property))) := by
  let q (p : {c : ℤ // c ≠ 0} × ℤ) : {v : Fin 2 → ℤ // v ≠ 0} :=
    ⟨![p.1.val, p.2], eisensteinPair_ne_zero (.inl p.1.property)⟩
  have hq : Function.Injective q := by
    intro a b h
    have he : ![a.1.val, a.2] = ![b.1.val, b.2] :=
      congrArg (fun v : {v : Fin 2 → ℤ // v ≠ 0} ↦ v.val) h
    exact Prod.ext (Subtype.ext (congrFun he 0)) (congrFun he 1)
  change Summable ((fun v : {v : Fin 2 → ℤ // v ≠ 0} ↦ eisSummand k v z (fun _ ↦ v.2)) ∘ q)
  exact (summable_eisSummand hk z).comp_injective hq

private lemma tsum_nonzeroLattice_partition {f : {v : Fin 2 → ℤ // v ≠ 0} → ℂ}
    (hf : Summable f) :
    (∑' v, f v) =
      (∑' d : {d : ℤ // d ≠ 0}, f ⟨![0, d.val], eisensteinPair_ne_zero (.inr d.2)⟩) +
      ∑' c : {c : ℤ // c ≠ 0}, ∑' d : ℤ,
        f ⟨![c.val, d], eisensteinPair_ne_zero (.inl c.2)⟩ := by
  let e := nonzeroLatticeEquiv
  let h := f ∘ e.symm
  have hh : Summable h := hf.comp_injective e.symm.injective
  have h₀ : Summable (h ∘ Sum.inl) := hh.comp_injective Sum.inl_injective
  have h₁ : Summable (h ∘ Sum.inr) := hh.comp_injective Sum.inr_injective
  calc
    _ = ∑' v, h v := (e.symm.tsum_eq f).symm
    _ = (∑' d, h (.inl d)) + ∑' p, h (.inr p) := Summable.tsum_sum h₀ h₁
    _ = _ := congrArg ((∑' d, h (.inl d)) + ·) h₁.tsum_prod

lemma tsum_eisSummand_eq_tsum_sigma_mul_cexp_pow {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) (z : ℍ) :
    (∑' v : {v : Fin 2 → ℤ // v ≠ 0}, eisSummand k v z (fun _ ↦ v.property)) =
      2 * riemannZeta k (hs := by exact_mod_cast (by omega : k ≠ 1)) +
      2 * Checked.div ((-2 * π * I) ^ k) ((k - 1)! : ℂ)
        (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (k - 1))).isUnit *
        ∑' (n : ℕ+), σ (k - 1) n * cexp (2 * π * I * z) ^ (n : ℕ) := by
  let f (v : {v : Fin 2 → ℤ // v ≠ 0}) := eisSummand (k : ℤ) v z (fun _ ↦ v.property)
  let g (c : {c : ℤ // c ≠ 0}) (d : ℤ) := eisSummand (k : ℤ) ![c.val, d] z
    (fun _ ↦ eisensteinPair_ne_zero (.inl c.property))
  let L (d : {d : ℤ // d ≠ 0}) := eisSummand (k : ℤ) ![0, d.val] z
    (fun _ ↦ eisensteinPair_ne_zero (.inr d.property))
  have hg : Summable (Function.uncurry g) := summable_prod_eisSummand hk z
  have hsum : (∑' v, f v) = (∑' d, L d) + ∑' c, ∑' d, g c d :=
    tsum_nonzeroLattice_partition (summable_eisSummand hk z)
  have hzero : (∑' d, L d) = 2 * riemannZeta k (hs := by exact_mod_cast (by omega : k ≠ 1)) := by
    rw [two_mul_riemannZeta_eq_tsum_int_inv_pow_of_even (by omega) hk2]
    refine tsum_congr fun d ↦ ?_
    simp only [L, eisSummand_nat_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Int.cast_zero, zero_mul, zero_add]
  let pos (n : ℕ+) : {c : ℤ // c ≠ 0} :=
    ⟨(n : ℕ), by exact_mod_cast n.pos.ne'⟩
  let neg (n : ℕ+) : {c : ℤ // c ≠ 0} :=
    ⟨-((n : ℕ) : ℤ), neg_ne_zero.mpr (by exact_mod_cast n.pos.ne')⟩
  have hneg (n : ℕ+) : (∑' d, g (neg n) d) = ∑' d, g (pos n) d := by
    nth_rewrite 1 [← tsum_comp_neg]
    refine tsum_congr fun d ↦ ?_
    simp only [g, pos, neg, eisSummand_nat_eq, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, Int.cast_neg, neg_mul,
      ← neg_add, hk2.neg_pow]
  have hpair : (∑' c, ∑' d, g c d) = 2 * ∑' n : ℕ+, ∑' d, g (pos n) d := by
    have hadd :
        (∑' n : ℕ+, ((∑' d, g (pos n) d) + (∑' d, g (neg n) d))) =
          ∑' c, ∑' d, g c d := (hg.prod.hasSum.int_pos_add_neg).tsum_eq
    rw [← hadd, ← tsum_mul_left]
    refine tsum_congr fun n ↦ ?_
    rw [hneg, two_mul]
  have hshift : k - 1 + 1 = k := by omega
  let A := Checked.div ((-2 * π * I) ^ k) ((k - 1)! : ℂ)
    (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (k - 1))).isUnit
  have hrow (m : ℕ+) : (∑' d, g (pos m) d) =
      A * ∑' n : ℕ+, (n : ℂ) ^ (k - 1) * cexp (2 * π * I * z) ^ (m * n : ℕ) := by
    let w : ℍ := ⟨m * z, by simpa using z.2⟩
    have H := qExpansion_identity_pnat (k := k - 1) (by omega) w
    simp only [hshift, one_div₀] at H
    calc
      _ = A * ∑' n : ℕ+, (n : ℂ) ^ (k - 1) * cexp (2 * π * I * w) ^ (n : ℕ) := by
        simpa only [g, pos, eisSummand_nat_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_fin_one, Int.cast_natCast, w, A] using H
      _ = _ := congrArg (A * ·) (tsum_congr fun n ↦ by
        simp only [w, ← Complex.exp_nat_mul]
        congr 2
        push_cast
        ring)
  have hrows : (∑' m : ℕ+, ∑' d, g (pos m) d) =
      A * ∑' n : ℕ+, σ (k - 1) n * cexp (2 * π * I * z) ^ (n : ℕ) := by
    simp only [hrow, tsum_mul_left,
      tsum_prod_pow_eq_tsum_sigma (k - 1) (norm_exp_two_pi_I_lt_one z)]
  change (∑' v, f v) = _
  rw [hsum, hzero, hpair, hrows, ← mul_assoc (2 : ℂ) A]

private def gammaSetDivGcdSigmaEquivPNat :
    {v : Fin 2 → ℤ // v ≠ 0} ≃ Σ n : ℕ+, gammaSet 1 (n : ℕ) 0 where
  toFun v := ⟨⟨finGcdMap v.val, Nat.pos_of_ne_zero
    (fun h ↦ v.property (finGcdMap_eq_zero_iff.mp h))⟩, ⟨v.val,
      (gammaSet_one_mem_iff _ v.val).mpr rfl⟩⟩
  invFun a := ⟨a.2.val, gammaSet_ne_zero a.2 a.1.pos.ne'⟩
  left_inv := fun _ ↦ rfl
  right_inv := by
    rintro ⟨⟨n, hn⟩, ⟨v, hv⟩⟩
    have he : finGcdMap v = n := hv.2
    subst n
    rfl

lemma eisSummand_of_gammaSet_eq_divIntMap (k : ℤ) (z : ℍ) {n : ℕ} [NeZero n]
    (v : gammaSet 1 n 0) :
    eisSummand k v z (fun _ ↦ gammaSet_ne_zero v (NeZero.ne n)) =
      Checked.zpow (n : ℂ) (-k) (fun _ ↦ (Nat.cast_ne_zero.mpr (NeZero.ne n)).isUnit) *
        eisSummand k (gammaSetDivGcdEquiv n v) z
          (fun _ ↦ gammaSet_ne_zero (gammaSetDivGcdEquiv n v) one_ne_zero) := by
  have hv := gammaSet_eq_gcd_mul_divIntMap v.property
  have hcoord (i : Fin 2) : (v.val i : ℂ) = (n : ℂ) * ((divIntMap n v.val i : ℤ) : ℂ) := by
    exact_mod_cast (show v.val i = (n : ℤ) * divIntMap n v.val i by
      simpa only [Pi.smul_apply, nsmul_eq_mul] using congrFun hv i)
  have hlinear : (v.val 0 : ℂ) * z + v.val 1 =
      (n : ℂ) * ((divIntMap n v.val 0 : ℂ) * z + (divIntMap n v.val 1 : ℂ)) := by
    rw [hcoord 0, hcoord 1, mul_add, mul_assoc]
  simp only [eisSummand, gammaSetDivGcdEquiv_eq, hlinear, mul_zpow₀]

lemma tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries {k : ℕ} (hk : 3 ≤ k) (z : ℍ) :
    (∑' v : {v : Fin 2 → ℤ // v ≠ 0}, eisSummand k v z (fun _ ↦ v.property)) =
      riemannZeta k (hs := by exact_mod_cast (by omega : k ≠ 1)) *
        eisensteinSeries (N := 1) 0 k z := by
  let s (v : {v : Fin 2 → ℤ // v ≠ 0}) := eisSummand (k : ℤ) v z (fun _ ↦ v.property)
  let e := gammaSetDivGcdSigmaEquivPNat
  have hs : Summable s := summable_norm_iff.mp (summable_norm_eisSummand (by exact_mod_cast hk) z)
  have he : Summable (s ∘ e.symm) := hs.comp_injective e.symm.injective
  change (∑' v, s v) = _
  rw [← e.symm.tsum_eq s]
  change (∑' p, (s ∘ e.symm) p) = _
  rw [he.tsum_sigma, zeta_nat_eq_tsum_of_gt_one (by omega : 1 < k),
    ← tsum_mul_right]
  refine tsum_congr fun n ↦ ?_
  have : NeZero (n : ℕ) := ⟨n.pos.ne'⟩
  have hn : (((n : ℕ) : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr n.pos.ne'
  let a := Checked.inv (((n : ℕ) : ℂ) ^ k) (hn.isUnit.pow k)
  let f (v : gammaSet 1 1 0) :=
    eisSummand k v z (fun _ ↦ gammaSet_ne_zero v one_ne_zero)
  calc
    _ = ∑' v : gammaSet 1 (n : ℕ) 0, a * f (gammaSetDivGcdEquiv (n : ℕ) v) := by
      refine tsum_congr fun v ↦ ?_
      change eisSummand (k : ℤ) v z (fun _ ↦ gammaSet_ne_zero v n.pos.ne') = _
      rw [eisSummand_of_gammaSet_eq_divIntMap (k : ℤ) z v]
      simp only [zpow_neg₀ hn, zpow_natCast₀, a, f]
    _ = _ := by
      rw [tsum_mul_left, (gammaSetDivGcdEquiv (n : ℕ)).tsum_eq f]
      simp only [a, f, eisensteinSeries, one_div₀]

lemma riemannZeta_nat_isUnit {k : ℕ} (hk : 1 < k) :
    IsUnit (riemannZeta k (hs := by exact_mod_cast hk.ne')) := by
  have h : 1 < (k : ℂ).re := by
    have hk' : (1 : ℝ) < k := by exact_mod_cast hk
    simpa using hk'
  exact (riemannZeta_ne_zero_of_one_lt_re h).isUnit

lemma bernoulli_nat_isUnit {k : ℕ} (hk : k ≠ 0) (he : Even k) :
    IsUnit (bernoulli k : ℂ) := by
  obtain ⟨j, rfl⟩ := even_iff_exists_two_mul.mp he
  have h := riemannZeta_two_mul_nat (k := j) (by omega)
  apply Ne.isUnit
  intro hB
  simp only [hB, mul_zero, zero_div] at h
  exact (riemannZeta_nat_isUnit (k := 2 * j) (by omega)).ne_zero
    (by simpa only [Nat.cast_mul, Nat.cast_two] using h)

/-- The q-expansion of the normalized Eisenstein series of level one in terms of the Riemann
zeta value. -/
lemma EisensteinSeries.q_expansion_riemannZeta {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) (z : ℍ) :
    E hk z = 1 + Checked.div ((-2 * π * I) ^ k)
      (riemannZeta k (hs := by exact_mod_cast (by omega : k ≠ 1)) * ((k - 1)! : ℂ))
      ((riemannZeta_nat_isUnit (by omega : 1 < k)).mul
        (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (k - 1))).isUnit) *
      ∑' n : ℕ+, σ (k - 1) n * cexp (2 * π * I * z) ^ (n : ℕ) := by
  rw [show E hk z = (1 / 2 : ℂ) • eisensteinSeriesSIF (N := 1) 0 k z from rfl,
    smul_eq_mul, eisensteinSeriesSIF_apply]
  have h := (tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries hk z).symm.trans
    (tsum_eisSummand_eq_tsum_sigma_mul_cexp_pow hk hk2 z)
  have hz := (riemannZeta_nat_isUnit (by omega : 1 < k)).ne_zero
  have hfn : ((k - 1)! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (k - 1))
  field_simp at h ⊢
  linear_combination h

private lemma eisensteinSeries_coeff_identity {k : ℕ} (hk : 1 < k) (hk2 : Even k) :
    Checked.div ((-2 * π * I) ^ k)
      (riemannZeta k (hs := by exact_mod_cast hk.ne') * ((k - 1)! : ℂ))
      ((riemannZeta_nat_isUnit hk).mul
        (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (k - 1))).isUnit) =
        -Checked.div (2 * k : ℂ) (bernoulli k : ℂ) (bernoulli_nat_isUnit (by omega) hk2) := by
  obtain ⟨m, rfl⟩ := even_iff_exists_two_mul.mp hk2
  have hmpos : 0 < m := by omega
  have hsucc : 2 * m - 1 + 1 = 2 * m := Nat.sub_add_cancel (by omega)
  have hfact : ((2 * m)! : ℂ) = ((2 * m : ℕ) : ℂ) * ((2 * m - 1)! : ℂ) := by
    exact_mod_cast (show (2 * m)! = (2 * m) * (2 * m - 1)! from
      (congrArg Nat.factorial hsucc.symm).trans (by rw [Nat.factorial_succ, hsucc]))
  let Z := riemannZeta ((2 * m : ℕ) : ℂ) (hs := by exact_mod_cast hk.ne')
  have hZ : Z * ((2 * m)! : ℂ) =
      (-1) ^ (m + 1) * (2 : ℂ) ^ (2 * m - 1) * π ^ (2 * m) * bernoulli (2 * m) := by
    apply (eq_div_iff (hb := (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (2 * m))).isUnit)).mp
    simpa only [Z, Nat.cast_mul, Nat.cast_two] using riemannZeta_two_mul_nat hmpos.ne'
  have hpow : (-2 * π * I : ℂ) ^ (2 * m) =
      (-1) ^ m * (2 : ℂ) ^ (2 * m) * π ^ (2 * m) := by
    have he : Even (2 * m) := ⟨m, by omega⟩
    rw [mul_pow, mul_pow, he.neg_pow, pow_mul I, I_sq]
    ring
  have htwo : (2 : ℂ) ^ (2 * m) = 2 * 2 ^ (2 * m - 1) := by
    calc
      (2 : ℂ) ^ (2 * m) = 2 ^ (2 * m - 1 + 1) := by rw [hsucc]
      _ = _ := by rw [pow_succ']
  rw [← neg_div₀, div_eq_div_iff]
  change (-2 * π * I : ℂ) ^ (2 * m) * bernoulli (2 * m) =
    -(2 * ((2 * m : ℕ) : ℂ)) * (Z * ((2 * m - 1)! : ℂ))
  calc
    _ = -(2 : ℂ) * (Z * ((2 * m)! : ℂ)) := by
      rw [hpow, htwo, hZ, pow_succ]
      ring
    _ = _ := by rw [hfact]; ring

/-- The q-expansion of the normalized Eisenstein series of level one in terms of the Bernoulli
number. -/
lemma EisensteinSeries.q_expansion_bernoulli {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) (z : ℍ) :
    E hk z = 1 - Checked.div (2 * k : ℂ) (bernoulli k : ℂ) (bernoulli_nat_isUnit (by omega) hk2) *
      ∑' n : ℕ+, σ (k - 1) n * cexp (2 * π * I * z) ^ (n : ℕ) := by
  rw [q_expansion_riemannZeta hk hk2 z, eisensteinSeries_coeff_identity (by omega) hk2,
    neg_mul, ← sub_eq_add_neg]

section NonZero

open ModularFormClass


/-- Summability of the divisor-sum q-expansion series `∑ σ_{k-1}(n) q^n`. -/
lemma EisensteinSeries.summable_sigma_mul_cexp_pow {k : ℕ} (hk : 1 ≤ k) (z : ℍ) :
    Summable fun n : ℕ ↦ (σ (k - 1) n : ℂ) * cexp (2 * π * I * z) ^ n := by
  apply Summable.of_norm_bounded
    (summable_norm_pow_mul_geometric_of_norm_lt_one k (norm_exp_two_pi_I_lt_one z))
  intro n
  simp only [norm_mul, Complex.norm_natCast, norm_pow]
  gcongr
  exact_mod_cast (ArithmeticFunction.sigma_le_pow_succ (k - 1) n).trans_eq (by congr 1; omega)

/-- The q-expansion coefficients of the normalised Eisenstein series `E k`: the constant term is
`1` and for `m ≥ 1` the `m`-th coefficient is `-(2k / B_k) * σ_{k-1}(m)` where `B_k` is the
`k`-th Bernoulli number. -/
lemma EisensteinSeries.E_qExpansion_coeff {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) (m : ℕ) :
    (qExpansion 1 (E hk)).coeff m =
    if m = 0 then 1 else
      -Checked.div (2 * k : ℂ) (bernoulli k : ℂ) (bernoulli_nat_isUnit (by omega) hk2) *
        (σ (k - 1) m) := by
  set β : ℂ := -Checked.div (2 * k : ℂ) (bernoulli k : ℂ) (bernoulli_nat_isUnit (by omega) hk2)
  set c : ℕ → ℂ := fun m ↦ if m = 0 then 1 else β * ↑(σ (k - 1) m)
  suffices ∀ τ : ℍ, HasSum (fun m ↦ c m • Function.Periodic.qParam (1 : ℝ) τ ^ m) (E hk τ) from
    (ModularFormClass.qExpansion_coeff_unique one_pos one_mem_strictPeriods_SL this m).symm
  intro τ
  have hS : Summable fun n : ℕ ↦ (σ (k - 1) (n + 1) : ℂ) * cexp (2 * π * I * τ) ^ (n + 1) :=
    (summable_nat_add_iff 1).mpr (summable_sigma_mul_cexp_pow (by omega) τ)
  rw [← hasSum_nat_add_iff' 1]
  simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, smul_eq_mul, Finset.range_one,
    ite_mul, one_mul, Finset.sum_singleton, pow_zero, c]
  have hval : E hk τ - 1 = β * ∑' n : ℕ, (σ (k - 1) (n + 1)) * cexp (2 * π * I * τ) ^ (n + 1) := by
    have := q_expansion_bernoulli hk hk2 τ
    rw [this, ← tsum_pnat_eq_tsum_succ (f := fun n ↦ (σ (k - 1) n : ℂ) * cexp (2 * π * I * τ) ^ n)]
    ring
  rw [hval]
  convert! (hS.mul_left β).hasSum using 1
  · funext n
    simp only [Periodic.qParam, ofReal_one, div_one₀, mul_assoc]
  · rw [tsum_mul_left]

/-- The q-expansion constant coefficient of the normalised Eisenstein series `E k` is `1`. -/
lemma EisensteinSeries.E_qExpansion_coeff_zero {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) :
    (qExpansion 1 (E hk)).coeff 0 = 1 := by
  simpa using E_qExpansion_coeff hk hk2 0

/-- Normalised Eisenstein series of even weight `k ≥ 3` are non-zero. -/
theorem EisensteinSeries.E_ne_zero {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) : E hk ≠ 0 :=
  fun h ↦ one_ne_zero <| (E_qExpansion_coeff_zero hk hk2).symm.trans (by simp [h, qExpansion_zero])

/-- The normalised Eisenstein series `E k` tends to `1` at `i∞`. -/
theorem EisensteinSeries.tendsto_E_atImInfty {k : ℕ} (hk : 3 ≤ k := by norm_num)
    (hk2 : Even k := by norm_num) : Tendsto (E hk : ℍ → ℂ) atImInfty (𝓝 1) := by
  simpa [E_qExpansion_coeff_zero hk hk2] using
    ModularFormClass.tendsto_atImInfty (E hk) one_pos one_mem_strictPeriods_SL

end NonZero
