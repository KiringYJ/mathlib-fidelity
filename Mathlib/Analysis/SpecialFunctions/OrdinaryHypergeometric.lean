/-
Copyright (c) 2024 Edward Watine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edward Watine
-/
module

public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Ordinary hypergeometric series in a topological algebra

The Gauss series has coefficients `(a)ₙ (b)ₙ / (n! (c)ₙ)`, where `(a)ₙ` is the ascending
Pochhammer symbol. Each coefficient requires both of its original denominators to be nonzero;
a zero numerator does not remove either obligation. The full series requires these conditions
at every index. In particular, its scalar field has characteristic zero and its lower parameter
avoids the nonpositive integers.

`ordinaryHypergeometric`, denoted `₂F₁`, evaluates the series in natural index order only with
evidence of convergence. Its `HasSum` theorem certifies the use of the underlying conditional
summation operation; conditional convergence at a boundary point is allowed. It agrees with
`FormalMultilinearSeries.sum` wherever the series is unconditionally summable. This file does not
define analytic continuation outside the convergence domain.

An upper nonpositive integer makes a valid Gauss series terminate. The separately specified
polynomial extension at a lower nonpositive integer is not a value of the raw coefficient
formula: DLMF (15.2.5) and (15.2.6) give distinct parameter-limit interpretations there.

## References

* [DLMF §15.2](https://dlmf.nist.gov/15.2), particularly (15.2.1) and (15.2.4)–(15.2.6).

## Tags

hypergeometric, gaussian, ordinary
-/

@[expose] public section

open Nat FormalMultilinearSeries

section Field

variable {𝕂 : Type*} [Field 𝕂]

/-- The exact factorial domain of a full Gauss series is characteristic zero. A single
coefficient only needs the nonvanishing of its own factorial. -/
theorem ordinaryHypergeometric_factorial_domain_iff :
    (∀ n : ℕ, (n ! : 𝕂) ≠ 0) ↔ CharZero 𝕂 := by
  constructor
  · intro hf
    exact charZero_of_inj_zero fun n hn => by
      cases n with
      | zero => rfl
      | succ n =>
          exact False.elim (hf (n + 1) (by simp [factorial_succ, cast_mul, hn]))
  · intro h
    let := h
    exact fun n => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)

/-- The lower Pochhammer denominators are nonzero at every index exactly when the lower
parameter avoids the nonpositive integers. This equivalence does not assume characteristic zero. -/
theorem ordinaryHypergeometric_pochhammer_domain_iff (c : 𝕂) :
    (∀ n : ℕ, (ascPochhammer 𝕂 n).eval c ≠ 0) ↔ ∀ k : ℕ, c ≠ -k := by
  constructor
  · intro hc k hk
    apply hc (k + 1)
    exact (ascPochhammer_eval_eq_zero_iff _ _).mpr ⟨k, by omega, by simp [hk]⟩
  · intro hc n hn
    obtain ⟨k, _, hk⟩ := (ascPochhammer_eval_eq_zero_iff _ _).mp hn
    exact hc k (by simpa only [neg_neg] using congrArg Neg.neg hk.symm)

/-- Nonvanishing of the lower Pochhammer denominators from the usual parameter condition. -/
theorem ordinaryHypergeometricSeries_pochhammer_ne_zero {c : 𝕂}
    (hc : ∀ k : ℕ, c ≠ -k) (n : ℕ) : (ascPochhammer 𝕂 n).eval c ≠ 0 :=
  (ordinaryHypergeometric_pochhammer_domain_iff c).mpr hc n

/-- A coefficient of the ordinary hypergeometric series, with both original denominator
obligations. This definition also applies to individual coefficients in positive characteristic. -/
noncomputable abbrev ordinaryHypergeometricCoefficient (a b c : 𝕂) (n : ℕ)
    (hn : (n ! : 𝕂) ≠ 0 := by checked_nonzero)
    (hc : (ascPochhammer 𝕂 n).eval c ≠ 0 := by checked_nonzero) : 𝕂 :=
  (n ! : 𝕂)⁻¹ * (ascPochhammer 𝕂 n).eval a * (ascPochhammer 𝕂 n).eval b *
    ((ascPochhammer 𝕂 n).eval c)⁻¹

theorem ordinaryHypergeometricCoefficient_ne_zero_iff (a b c : 𝕂) (n : ℕ)
    {hn : (n ! : 𝕂) ≠ 0} {hc : (ascPochhammer 𝕂 n).eval c ≠ 0} :
    ordinaryHypergeometricCoefficient a b c n hn hc ≠ 0 ↔
      (ascPochhammer 𝕂 n).eval a ≠ 0 ∧ (ascPochhammer 𝕂 n).eval b ≠ 0 := by
  have hni : (n ! : 𝕂)⁻¹ ≠ 0 := hn.isUnit.inv₀.ne_zero
  have hci : ((ascPochhammer 𝕂 n).eval c)⁻¹ ≠ 0 := hc.isUnit.inv₀.ne_zero
  simp only [ordinaryHypergeometricCoefficient, mul_ne_zero_iff]
  constructor
  · intro h
    exact ⟨h.1.1.2, h.1.2⟩
  · rintro ⟨ha, hb⟩
    exact ⟨⟨⟨hni, ha⟩, hb⟩, hci⟩

/-- Nonvanishing of the next coefficient supplies the nonzero upper factors required by
the inverse coefficient ratio. -/
theorem ordinaryHypergeometricCoefficient_succ_ne_zero (a b c : 𝕂) (n : ℕ)
    {hn : ((n + 1)! : 𝕂) ≠ 0} {hc : (ascPochhammer 𝕂 (n + 1)).eval c ≠ 0}
    (h : ordinaryHypergeometricCoefficient a b c (n + 1) hn hc ≠ 0) :
    a + n ≠ 0 ∧ b + n ≠ 0 := by
  rw [ordinaryHypergeometricCoefficient_ne_zero_iff, ascPochhammer_succ_eval,
    ascPochhammer_succ_eval] at h
  exact ⟨(mul_ne_zero_iff.mp h.1).2, (mul_ne_zero_iff.mp h.2).2⟩

variable (𝔸 : Type*) [Ring 𝔸] [Algebra 𝕂 𝔸] [TopologicalSpace 𝔸]
  [IsTopologicalRing 𝔸]

/-- The full ordinary hypergeometric formal series, defined exactly when every factorial and
lower Pochhammer denominator is nonzero. -/
noncomputable def ordinaryHypergeometricSeries (a b c : 𝕂)
    (hf : ∀ n : ℕ, (n ! : 𝕂) ≠ 0) (hc : ∀ n : ℕ, (ascPochhammer 𝕂 n).eval c ≠ 0) :
    FormalMultilinearSeries 𝕂 𝔸 𝔸 :=
  ofScalars 𝔸 (fun n => ordinaryHypergeometricCoefficient a b c n (hf n) (hc n))

variable {𝔸} (a b c : 𝕂)
  (hf : ∀ n : ℕ, (n ! : 𝕂) ≠ 0) (hc : ∀ n : ℕ, (ascPochhammer 𝕂 n).eval c ≠ 0)

/-- A summable Gauss series in a Hausdorff algebra has a unique sum in natural index order. -/
theorem ordinaryHypergeometric_existsUnique_hasSum [T2Space 𝔸] (x : 𝔸)
    (hx : Summable (fun n => ordinaryHypergeometricSeries 𝔸 a b c hf hc n (fun _ => x))
      (SummationFilter.conditional ℕ)) :
    ∃! v, HasSum (fun n => ordinaryHypergeometricSeries 𝔸 a b c hf hc n (fun _ => x)) v
      (SummationFilter.conditional ℕ) :=
  hx.elim fun v hv => ⟨v, hv, fun _ hw => hw.unique hv⟩

/-- The ordinary hypergeometric function is the unique sum of the Gauss series in natural index
order. Summability includes convergent boundary values and terminating series. -/
noncomputable def ordinaryHypergeometric [T2Space 𝔸] (x : 𝔸)
    (hx : Summable (fun n => ordinaryHypergeometricSeries 𝔸 a b c hf hc n (fun _ => x))
      (SummationFilter.conditional ℕ)) : 𝔸 :=
  (ordinaryHypergeometric_existsUnique_hasSum a b c hf hc x hx).exists.choose

@[inherit_doc]
notation "₂F₁" => ordinaryHypergeometric

theorem ordinaryHypergeometric_hasSum [T2Space 𝔸] (x : 𝔸)
    (hx : Summable (fun n => ordinaryHypergeometricSeries 𝔸 a b c hf hc n (fun _ => x))
      (SummationFilter.conditional ℕ)) :
    HasSum (fun n => ordinaryHypergeometricSeries 𝔸 a b c hf hc n (fun _ => x))
      (₂F₁ a b c hf hc x hx) (SummationFilter.conditional ℕ) :=
  (ordinaryHypergeometric_existsUnique_hasSum a b c hf hc x hx).exists.choose_spec

/-- The value is the limit of the ordinary finite partial sums. -/
theorem ordinaryHypergeometric_tendsto_sum_range [T2Space 𝔸] (x : 𝔸)
    (hx : Summable (fun n => ordinaryHypergeometricSeries 𝔸 a b c hf hc n (fun _ => x))
      (SummationFilter.conditional ℕ)) :
    Filter.Tendsto (fun N => ∑ n ∈ Finset.range N,
      ordinaryHypergeometricSeries 𝔸 a b c hf hc n (fun _ => x)) Filter.atTop
      (nhds (₂F₁ a b c hf hc x hx)) := by
  simpa only [HasSum, SummationFilter.conditional_filter_eq_map_range,
    Filter.tendsto_map'_iff, Function.comp_def] using
    ordinaryHypergeometric_hasSum a b c hf hc x hx

/-- On the domain of unconditional convergence, the natural-order series agrees with the
formal multilinear series sum. -/
theorem ordinaryHypergeometric_eq_sum [T2Space 𝔸] (x : 𝔸)
    (hx : Summable (fun n => ordinaryHypergeometricSeries 𝔸 a b c hf hc n (fun _ => x))) :
    ₂F₁ a b c hf hc x (hx.mono_filter (SummationFilter.conditional ℕ).le_atTop) =
      (ordinaryHypergeometricSeries 𝔸 a b c hf hc).sum x :=
  (ordinaryHypergeometric_hasSum a b c hf hc x
    (hx.mono_filter (SummationFilter.conditional ℕ).le_atTop)).tsum_eq.symm.trans
      (tsum_eq_of_summable_unconditional hx)

theorem ordinaryHypergeometricSeries_apply_eq (x : 𝔸) (n : ℕ) :
    (ordinaryHypergeometricSeries 𝔸 a b c hf hc n fun _ => x) =
      ordinaryHypergeometricCoefficient a b c n (hf n) (hc n) • x ^ n := by
  rw [ordinaryHypergeometricSeries, ofScalars_apply_eq]

/-- This naming follows the convention of `NormedSpace.expSeries_apply_eq'`. -/
theorem ordinaryHypergeometricSeries_apply_eq' (x : 𝔸) :
    (fun n => ordinaryHypergeometricSeries 𝔸 a b c hf hc n fun _ => x) =
      fun n => ordinaryHypergeometricCoefficient a b c n (hf n) (hc n) • x ^ n := by
  rw [ordinaryHypergeometricSeries, ofScalars_apply_eq']

/-- The coefficient formula for the sum, on the domain of unconditional convergence. -/
theorem ordinaryHypergeometric_sum_eq (x : 𝔸)
    (_hx : Summable (fun n => ordinaryHypergeometricSeries 𝔸 a b c hf hc n (fun _ => x))) :
    (ordinaryHypergeometricSeries 𝔸 a b c hf hc).sum x =
      ∑' n : ℕ, ordinaryHypergeometricCoefficient a b c n (hf n) (hc n) • x ^ n :=
  tsum_congr fun n => ordinaryHypergeometricSeries_apply_eq a b c hf hc x n

theorem ordinaryHypergeometric_eq_tsum [T2Space 𝔸] (x : 𝔸)
    (hx : Summable (fun n => ordinaryHypergeometricSeries 𝔸 a b c hf hc n (fun _ => x))
      (SummationFilter.conditional ℕ)) :
    ₂F₁ a b c hf hc x hx =
      ∑'[SummationFilter.conditional ℕ] n : ℕ,
        ordinaryHypergeometricCoefficient a b c n (hf n) (hc n) • x ^ n :=
  (ordinaryHypergeometric_hasSum a b c hf hc x hx).tsum_eq.symm.trans <|
    tsum_congr fun n => ordinaryHypergeometricSeries_apply_eq a b c hf hc x n

theorem ordinaryHypergeometricSeries_apply_zero (n : ℕ) :
    ordinaryHypergeometricSeries 𝔸 a b c hf hc n (fun _ => 0) =
      Pi.single (M := fun _ => 𝔸) 0 1 n := by
  rw [ordinaryHypergeometricSeries, ofScalars_apply_eq, ordinaryHypergeometricCoefficient]
  cases n <;> simp

/-- The series at zero sums to its constant coefficient in natural index order. -/
theorem ordinaryHypergeometric_hasSum_zero :
    HasSum (fun n => ordinaryHypergeometricSeries 𝔸 a b c hf hc n (fun _ => 0)) 1
      (SummationFilter.conditional ℕ) := by
  simp only [ordinaryHypergeometricSeries_apply_zero]
  simpa only [Pi.single_eq_same] using
    (hasSum_single (L := SummationFilter.conditional ℕ) (f := Pi.single 0 (1 : 𝔸)) 0
      (fun k hk => by simp [hk]))

theorem ordinaryHypergeometric_summable_zero :
    Summable (fun n => ordinaryHypergeometricSeries 𝔸 a b c hf hc n (fun _ => 0))
      (SummationFilter.conditional ℕ) :=
  (ordinaryHypergeometric_hasSum_zero a b c hf hc).summable

@[simp]
theorem ordinaryHypergeometric_zero [T2Space 𝔸]
    {hx : Summable (fun n => ordinaryHypergeometricSeries 𝔸 a b c hf hc n (fun _ => 0))
      (SummationFilter.conditional ℕ)} :
    ₂F₁ a b c hf hc (0 : 𝔸) hx = 1 := by
  exact (ordinaryHypergeometric_hasSum a b c hf hc 0 hx).unique
    (ordinaryHypergeometric_hasSum_zero a b c hf hc)

theorem ordinaryHypergeometricSeries_symm :
    ordinaryHypergeometricSeries 𝔸 a b c hf hc = ordinaryHypergeometricSeries 𝔸 b a c hf hc := by
  unfold ordinaryHypergeometricSeries ordinaryHypergeometricCoefficient
  simp [mul_assoc, mul_left_comm]

/-- An upper nonpositive integer makes the later terms of a valid Gauss series vanish.
The lower parameter is still required to satisfy every denominator obligation. -/
lemma ordinaryHypergeometricSeries_eq_zero_of_neg_nat {n k : ℕ} (hab : k = -a ∨ k = -b)
    (hk : k < n) : ordinaryHypergeometricSeries 𝔸 a b c hf hc n = 0 := by
  rw [ordinaryHypergeometricSeries, ofScalars]
  rcases hab with h | h
  all_goals
    ext
    simp [(ascPochhammer_eval_eq_zero_iff n _).2 ⟨k, hk, h⟩]

end Field

section RCLike

open Filter Real Nat

open scoped Topology

variable {𝕂 : Type*} (𝔸 : Type*) [RCLike 𝕂] [NormedDivisionRing 𝔸] [NormedAlgebra 𝕂 𝔸]
  (a b c : 𝕂) (hf : ∀ n : ℕ, (n ! : 𝕂) ≠ 0)
  (hc : ∀ n : ℕ, (ascPochhammer 𝕂 n).eval c ≠ 0)

theorem ordinaryHypergeometric_radius_top_of_neg_nat₁ {k : ℕ} :
    (ordinaryHypergeometricSeries 𝔸 (-(k : 𝕂)) b c hf hc).radius = ⊤ := by
  refine FormalMultilinearSeries.radius_eq_top_of_forall_image_add_eq_zero _ (1 + k) fun n ↦ ?_
  exact ordinaryHypergeometricSeries_eq_zero_of_neg_nat (-(k : 𝕂)) b c hf hc
    (k := k) (Or.inl (neg_neg _).symm) (by omega)

theorem ordinaryHypergeometric_radius_top_of_neg_nat₂ {k : ℕ} :
    (ordinaryHypergeometricSeries 𝔸 a (-(k : 𝕂)) c hf hc).radius = ⊤ := by
  rw [ordinaryHypergeometricSeries_symm]
  exact ordinaryHypergeometric_radius_top_of_neg_nat₁ 𝔸 a c hf hc

/-- A valid Gauss-series term vanishes precisely when an upper Pochhammer factor vanishes. -/
lemma ordinaryHypergeometricSeries_eq_zero_iff (n : ℕ) :
    ordinaryHypergeometricSeries 𝔸 a b c hf hc n = 0 ↔ ∃ k < n, k = -a ∨ k = -b := by
  rw [ordinaryHypergeometricSeries, ofScalars_eq_zero]
  have heq : ordinaryHypergeometricCoefficient a b c n (hf n) (hc n) = 0 ↔
      (ascPochhammer 𝕂 n).eval a = 0 ∨ (ascPochhammer 𝕂 n).eval b = 0 := by
    constructor
    · intro hzero
      by_contra h
      push Not at h
      exact ((ordinaryHypergeometricCoefficient_ne_zero_iff a b c n).mpr h) hzero
    · intro hzero
      by_contra h
      have hab := (ordinaryHypergeometricCoefficient_ne_zero_iff a b c n).mp h
      exact hzero.elim hab.1 hab.2
  rw [heq, ascPochhammer_eval_eq_zero_iff, ascPochhammer_eval_eq_zero_iff]
  constructor
  · rintro (⟨k, hk, ha⟩ | ⟨k, hk, hb⟩)
    · exact ⟨k, hk, Or.inl ha⟩
    · exact ⟨k, hk, Or.inr hb⟩
  · rintro ⟨k, hk, ha | hb⟩
    · exact Or.inl ⟨k, hk, ha⟩
    · exact Or.inr ⟨k, hk, hb⟩

/-- The inverse coefficient ratio on its exact domain: the next coefficient is nonzero.
In particular, the upper factors at the next index cannot vanish. -/
theorem ordinaryHypergeometricSeries_norm_div_succ_norm (n : ℕ)
    {hnext : ordinaryHypergeometricCoefficient a b c n.succ (hf _) (hc _) ≠ 0} :
    Checked.div ‖ordinaryHypergeometricCoefficient a b c n (hf _) (hc _)‖
        ‖ordinaryHypergeometricCoefficient a b c n.succ (hf _) (hc _)‖
        (norm_ne_zero_iff.mpr hnext).isUnit =
      Checked.inv ‖a + n‖
          (norm_ne_zero_iff.mpr
            (ordinaryHypergeometricCoefficient_succ_ne_zero a b c n hnext).1).isUnit *
        Checked.inv ‖b + n‖
          (norm_ne_zero_iff.mpr
            (ordinaryHypergeometricCoefficient_succ_ne_zero a b c n hnext).2).isUnit *
        ‖c + n‖ * ‖1 + (n : 𝕂)‖ := by
  have hab := (ordinaryHypergeometricCoefficient_ne_zero_iff a b c n.succ).mp hnext
  rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval] at hab
  obtain ⟨ha, ha'⟩ := mul_ne_zero_iff.mp hab.1
  obtain ⟨hb, hb'⟩ := mul_ne_zero_iff.mp hab.2
  have hc' : c + n ≠ 0 :=
    (mul_ne_zero_iff.mp (by simpa only [ascPochhammer_succ_eval] using hc (n + 1))).2
  have hratio :
      ordinaryHypergeometricCoefficient a b c n (hf _) (hc _) /
          ordinaryHypergeometricCoefficient a b c n.succ (hf _) (hc _) =
        (c + n) / (a + n) * ((1 + (n : 𝕂)) / (b + n)) := by
    simp only [ordinaryHypergeometricCoefficient, factorial_succ, cast_mul, cast_add,
      cast_one, ascPochhammer_succ_eval]
    field_simp
    ring
  calc
    _ = ‖ordinaryHypergeometricCoefficient a b c n (hf _) (hc _) /
          ordinaryHypergeometricCoefficient a b c n.succ (hf _) (hc _)‖ :=
      (norm_div _ _).symm
    _ = ‖(c + n) / (a + n) * ((1 + (n : 𝕂)) / (b + n))‖ := congrArg norm hratio
    _ = _ := by
      simp only [norm_mul, norm_inv, div_eq_mul_inv₀]
      ring

/-- A valid Gauss series has radius one when neither upper parameter is a nonpositive integer. -/
theorem ordinaryHypergeometricSeries_radius_eq_one
    (hab : ∀ k : ℕ, ↑k ≠ -a ∧ ↑k ≠ -b) :
    (ordinaryHypergeometricSeries 𝔸 a b c hf hc).radius = 1 := by
  have ha (n : ℕ) : (ascPochhammer 𝕂 n).eval a ≠ 0 := by
    intro h
    obtain ⟨k, _, hk⟩ := (ascPochhammer_eval_eq_zero_iff _ _).mp h
    exact (hab k).1 hk
  have hb (n : ℕ) : (ascPochhammer 𝕂 n).eval b ≠ 0 := by
    intro h
    obtain ⟨k, _, hk⟩ := (ascPochhammer_eval_eq_zero_iff _ _).mp h
    exact (hab k).2 hk
  have hcoeff (n : ℕ) : ordinaryHypergeometricCoefficient a b c n (hf _) (hc _) ≠ 0 :=
    (ordinaryHypergeometricCoefficient_ne_zero_iff a b c n).mpr ⟨ha n, hb n⟩
  have ha' (n : ℕ) : a + n ≠ 0 :=
    (ordinaryHypergeometricCoefficient_succ_ne_zero a b c n (hcoeff (n + 1))).1
  have hb' (n : ℕ) : b + n ≠ 0 :=
    (ordinaryHypergeometricCoefficient_succ_ne_zero a b c n (hcoeff (n + 1))).2
  have hquotient (u v : 𝕂) (hv : ∀ n : ℕ, v + n ≠ 0) :
      Tendsto (fun n : ℕ => Checked.div (u + n) (v + n) (hv n).isUnit) atTop (𝓝 1) := by
    apply (tendsto_comap_val_iff (p := fun n : ℕ => v + n ≠ 0)
      (Eventually.of_forall hv)).mp
    let φ : {n : ℕ // v + n ≠ 0} → {n : ℕ // v + 1 * n ≠ 0} :=
      fun n => ⟨n.1, by simpa only [one_mul] using n.2⟩
    have hφ : Tendsto φ (comap Subtype.val atTop) (comap Subtype.val atTop) :=
      tendsto_comap_iff.mpr tendsto_comap
    simpa only [φ, one_mul, div_one₀, Function.comp_def] using
      (tendsto_add_mul_div_add_mul_atTop_nhds u v (1 : 𝕂) (d := 1) one_ne_zero).comp hφ
  have hlim := (hquotient c a ha').mul (hquotient 1 b hb')
  simp only [one_mul] at hlim
  change (ofScalars 𝔸 (fun n => ordinaryHypergeometricCoefficient a b c n (hf _) (hc _))).radius = 1
  refine ofScalars_radius_eq_of_tendsto 𝔸 _ one_ne_zero
    (Eventually.frequently (Eventually.of_forall hcoeff)) ?_
  have hnorm := hlim.norm
  simp only [norm_one] at hnorm
  apply (hnorm.comp tendsto_comap).congr'
  filter_upwards [] with n
  dsimp only [Function.comp_def]
  rw [ordinaryHypergeometricSeries_norm_div_succ_norm a b c hf hc n.1
    (hnext := hcoeff n.1.succ)]
  simp only [norm_mul, norm_inv, div_eq_mul_inv₀]
  ring

end RCLike
