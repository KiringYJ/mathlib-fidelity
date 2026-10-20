/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.Probability.Moments.Variance

/-!
# Conditional variance

Given a measure `μ` on a σ-algebra `m₀` and a σ-algebra `m`, a function `v` is a conditional
variance of a real-valued random variable `X` given `m`, written `IsCondVar m μ X v`, when it is a
conditional expectation of `(X - g) ^ 2` for a conditional expectation `g` of `X`, both given `m`.
For an integrable `X` and a sub-σ-algebra `m`, the conditional expectations of `X` agree almost
everywhere, so the choice of `g` does not matter (`ProbabilityTheory.isCondVar_iff`). For an `X`
outside `L²` the relation can hold for every constant `v`; see `ProbabilityTheory.IsCondVar`.

A conditional variance is determined only up to almost everywhere equality. The conditional
variance `Var[X; μ | m] = condVar m μ X` is therefore the almost everywhere class of the
conditional variances of `X`, a germ along `ae μ`. A function `v` represents it, written
`v ∈ Var[X; μ | m]`, exactly when `IsCondVar m μ X v` (`ProbabilityTheory.mem_condVar_iff`), and
`Var[X; μ | m] = μ[(X - g) ^ 2 | m]` for each representative `g` of `μ[X | m]`
(`ProbabilityTheory.condVar_eq_condExp`).

## Domain

`condVar m μ X` takes a proof of `HasCondVar m μ X`: the conditional expectation `μ[X | m]` exists
and is unique almost everywhere, and so is the conditional expectation of `(X - g) ^ 2` for each of
its representatives `g`. This is the exact domain of the formula
`Var[X | m] = E[(X - E[X | m]) ^ 2 | m]`. The tactic `has_cond_var` finds it from a hypothesis or
from the sufficient condition `HasCondVar.of_memLp`: an integrable, square-integrable `X` and a
sub-σ-algebra `m` on which `μ` is σ-finite, which instance search finds, for example from a finite
measure. A known conditional variance of such an `X` also supplies the domain, without
σ-finiteness (`HasCondVar.of_isCondVar`).

## Main definitions

* `ProbabilityTheory.IsCondVar m μ X v`: `v` is a conditional variance of `X` given `m`.
* `ProbabilityTheory.HasCondVar m μ X`: `X` has a conditional variance given `m`, unique almost
  everywhere. This is the exact domain of `condVar`.
* `ProbabilityTheory.condVar m μ X`, with notation `Var[X; μ | m]`, and `Var[X | m]` for the
  measure `volume`: the almost everywhere class of the conditional variances of `X`.

## Main results

* `ProbabilityTheory.IsCondVar.ae_eq`: the conditional variances of an integrable,
  square-integrable random variable given a sub-σ-algebra agree almost everywhere.
* `ProbabilityTheory.isCondVar_condExp_sq_sub_sq_condExp`: if `g` and `k` are conditional
  expectations of `X` and `X ^ 2`, then `k - g ^ 2` is a conditional variance of `X`; for the
  classes, `Var[X; μ | m] = μ[X ^ 2 | m] - μ[X | m] ^ 2`
  (`ProbabilityTheory.condVar_eq_condExp_sq_sub_sq_condExp`).
* `ProbabilityTheory.IsCondVar.integral_add_variance`: the law of total variance.

The statements about conditional variances as a relation do not assume that the measure is
σ-finite on the sub-σ-algebra. Only the statements for the trivial σ-algebra and the law of total
variance assume a finite or a probability measure, which their means and variances require.

## TODO

Define the Lebesgue conditional variance, from the Lebesgue conditional expectation
`MeasureTheory.condLExp`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω : Type*}

section Definitions

/-- A function `v` is a conditional variance of the real-valued random variable `X` given the
σ-algebra `m` with respect to the measure `μ`: it is a conditional expectation of `(X - g) ^ 2` for
a conditional expectation `g` of `X`, both given `m`.

For an integrable `X` and a sub-σ-algebra `m`, this holds for every conditional expectation `g` of
`X` as soon as it holds for one (`ProbabilityTheory.isCondVar_iff`). For an integrable,
square-integrable `X`, a conditional variance is the textbook one. Like `MeasureTheory.IsCondExp`,
the relation constrains `v` only on the sets of `m` on which `(X - g) ^ 2` is integrable: given `⊥`
and Lebesgue measure on `(0, 1]`, every constant, even a negative one, is a conditional variance of
`x ↦ x ^ (-1 / 2 : ℝ)`, whose variance is `∞`. See `ProbabilityTheory.HasCondVar` for the random
variables whose conditional variance is unique. -/
def IsCondVar (m : SigmaAlgebra Ω) {m₀ : SigmaAlgebra Ω} (μ : Measure[m₀] Ω) (X v : Ω → ℝ) :
    Prop :=
  ∃ g, IsCondExp m μ X g ∧ IsCondExp m μ (fun ω ↦ (X ω - g ω) ^ 2) v

/-- The random variable `X` has a conditional variance given `m` with respect to `μ` that is unique
almost everywhere: its conditional expectation exists and is unique almost everywhere, and so is
the conditional expectation of `(X - g) ^ 2` for each conditional expectation `g` of `X`.

This is the exact domain of `ProbabilityTheory.condVar`, the domain of the formula
`Var[X | m] = E[(X - E[X | m]) ^ 2 | m]`. The tactic `has_cond_var` derives it from the sufficient
condition `ProbabilityTheory.HasCondVar.of_memLp`. -/
structure HasCondVar (m : SigmaAlgebra Ω) {m₀ : SigmaAlgebra Ω} (μ : Measure[m₀] Ω)
    (X : Ω → ℝ) : Prop where
  /-- The conditional expectation of `X` exists and is unique almost everywhere. -/
  hasUniqueCondExp : HasUniqueCondExp m μ X
  /-- For each conditional expectation `g` of `X`, the conditional expectation of `(X - g) ^ 2`
  exists and is unique almost everywhere. -/
  hasUniqueCondExp_sub_sq ⦃g : Ω → ℝ⦄ :
    IsCondExp m μ X g → HasUniqueCondExp m μ (fun ω ↦ (X ω - g ω) ^ 2)

end Definitions

variable {m₀ m : SigmaAlgebra Ω} {μ : Measure[m₀] Ω} {X Y g k v v' : Ω → ℝ} {s : Set Ω}

/-- For a conditional expectation `g` of an integrable, square-integrable `X` given a sub-σ-algebra,
`(X - g) ^ 2` is integrable. -/
theorem _root_.MeasureTheory.IsCondExp.integrable_sub_sq (hm : m ≤ m₀) (hg : IsCondExp m μ X g)
    (hX : Integrable X μ) (hX₂ : MemLp X 2 μ) : Integrable (fun ω ↦ (X ω - g ω) ^ 2) μ :=
  (hX₂.sub (hg.memLp one_le_two hm hX hX₂)).integrable_sq

/-! ### Conditional variances as a relation -/

/-- When the conditional expectations of `X` agree almost everywhere, the conditional variances of
`X` are the conditional expectations of `(X - g) ^ 2` for any conditional expectation `g` of `X`. -/
private theorem isCondVar_iff_of_ae_eq (hg : IsCondExp m μ X g)
    (h_uniq : ∀ g', IsCondExp m μ X g' → g' =ᵐ[μ] g) :
    IsCondVar m μ X v ↔ IsCondExp m μ (fun ω ↦ (X ω - g ω) ^ 2) v := by
  refine ⟨fun ⟨g', hg', hv⟩ ↦ hv.congr_left ?_, fun hv ↦ ⟨g, hg, hv⟩⟩
  filter_upwards [h_uniq g' hg'] with ω hω
  rw [hω]

/-- Given a conditional expectation `g` of an integrable `X` given a sub-σ-algebra, the conditional
variances of `X` are the conditional expectations of `(X - g) ^ 2`: the choice of the conditional
expectation in `ProbabilityTheory.IsCondVar` does not matter. -/
theorem isCondVar_iff (hm : m ≤ m₀) (hX : Integrable X μ) (hg : IsCondExp m μ X g) :
    IsCondVar m μ X v ↔ IsCondExp m μ (fun ω ↦ (X ω - g ω) ^ 2) v :=
  isCondVar_iff_of_ae_eq hg fun _ hg' ↦ hg'.ae_eq hm hX hg

namespace IsCondVar

theorem congr_left (h : IsCondVar m μ X v) (hXY : X =ᵐ[μ] Y) : IsCondVar m μ Y v := by
  obtain ⟨g, hg, hv⟩ := h
  refine ⟨g, hg.congr_left hXY, hv.congr_left ?_⟩
  filter_upwards [hXY] with ω hω
  rw [hω]

theorem congr_right (h : IsCondVar m μ X v) (hv : v =ᵐ[μ] v') : IsCondVar m μ X v' :=
  let ⟨g, hg, hgv⟩ := h
  ⟨g, hg, hgv.congr_right hv⟩

theorem congr (h : IsCondVar m μ X v) (hXY : X =ᵐ[μ] Y) (hv : v =ᵐ[μ] v') :
    IsCondVar m μ Y v' :=
  (h.congr_left hXY).congr_right hv

/-- A conditional variance given `m` is almost everywhere `m`-strongly measurable. -/
theorem aestronglyMeasurable (h : IsCondVar m μ X v) : AEStronglyMeasurable[m] v μ :=
  let ⟨_, _, hv⟩ := h
  hv.aestronglyMeasurable

/-- A conditional variance of an integrable `X` given a sub-σ-algebra is a conditional expectation
of `(X - g) ^ 2` for every conditional expectation `g` of `X`. -/
theorem isCondExp_sub_sq (hm : m ≤ m₀) (h : IsCondVar m μ X v) (hX : Integrable X μ)
    (hg : IsCondExp m μ X g) : IsCondExp m μ (fun ω ↦ (X ω - g ω) ^ 2) v :=
  (isCondVar_iff hm hX hg).1 h

/-- Two conditional variances of an integrable, square-integrable `X` given a sub-σ-algebra agree
almost everywhere. No σ-finiteness is needed. -/
theorem ae_eq (hm : m ≤ m₀) (hX : Integrable X μ) (hX₂ : MemLp X 2 μ) (h₁ : IsCondVar m μ X v)
    (h₂ : IsCondVar m μ X v') : v =ᵐ[μ] v' := by
  obtain ⟨g, hg, hv⟩ := h₁
  exact hv.ae_eq hm (hg.integrable_sub_sq hm hX hX₂) (h₂.isCondExp_sub_sq hm hX hg)

/-- A conditional variance of an integrable, square-integrable `X` given a sub-σ-algebra is
integrable. -/
theorem integrable (hm : m ≤ m₀) (h : IsCondVar m μ X v) (hX : Integrable X μ)
    (hX₂ : MemLp X 2 μ) : Integrable v μ :=
  let ⟨_, hg, hv⟩ := h
  hv.integrable (hg.integrable_sub_sq hm hX hX₂)

/-- A conditional variance of an integrable, square-integrable `X` given a sub-σ-algebra is
nonnegative almost everywhere. -/
theorem nonneg (hm : m ≤ m₀) (h : IsCondVar m μ X v) (hX : Integrable X μ) (hX₂ : MemLp X 2 μ) :
    0 ≤ᵐ[μ] v :=
  let ⟨_, hg, hv⟩ := h
  hv.nonneg hm (hg.integrable_sub_sq hm hX hX₂) (.of_forall fun _ ↦ sq_nonneg _)

/-- The integral of a conditional variance of an integrable `X` is the integral of `(X - g) ^ 2`,
the variance of `X` around a conditional expectation `g` of `X`. -/
theorem integral_eq (hm : m ≤ m₀) (h : IsCondVar m μ X v) (hX : Integrable X μ)
    (hg : IsCondExp m μ X g) (hXg : Integrable (fun ω ↦ (X ω - g ω) ^ 2) μ) :
    ∫ ω, v ω ∂μ = ∫ ω, (X ω - g ω) ^ 2 ∂μ :=
  (h.isCondExp_sub_sq hm hX hg).integral_eq hXg

/-- The integral of a conditional variance of an integrable `X` over a set of `m` is the integral
of `(X - g) ^ 2` over that set, for a conditional expectation `g` of `X`. -/
theorem setIntegral_eq (hm : m ≤ m₀) (h : IsCondVar m μ X v) (hX : Integrable X μ)
    (hg : IsCondExp m μ X g) (hs : s ∈ m) (hXg : IntegrableOn (fun ω ↦ (X ω - g ω) ^ 2) s μ) :
    ∫ ω in s, v ω ∂μ = ∫ ω in s, (X ω - g ω) ^ 2 ∂μ :=
  (h.isCondExp_sub_sq hm hX hg).setIntegral_eq s hs hXg

theorem smul (h : IsCondVar m μ X v) (c : ℝ) : IsCondVar m μ (c • X) (c ^ 2 • v) := by
  obtain ⟨g, hg, hv⟩ := h
  refine ⟨c • g, hg.smul c, (hv.smul (c ^ 2)).congr_left (.of_forall fun ω ↦ ?_)⟩
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem neg (h : IsCondVar m μ X v) : IsCondVar m μ (-X) v := by
  obtain ⟨g, hg, hv⟩ := h
  refine ⟨-g, hg.neg, hv.congr_left (.of_forall fun ω ↦ ?_)⟩
  simp only [Pi.neg_apply]
  ring

end IsCondVar

/-- The conditional variance of an almost everywhere `m`-strongly measurable random variable given
`m` is zero. -/
theorem isCondVar_zero_of_aestronglyMeasurable (hX : AEStronglyMeasurable[m] X μ) :
    IsCondVar m μ X 0 :=
  ⟨X, isCondExp_self hX, IsCondExp.zero.congr_left (.of_forall fun _ ↦ by simp)⟩

-- `(· ^ 2)` is a postfix operator called `_sq` in lemma names, but
-- `isCondVar_condExp_sq_sub_condExp_sq` is a bit ridiculous, so we exceptionally denote it by `sq_`
-- as if it were a prefix.
/-- If `g` is a conditional expectation of an integrable, square-integrable `X` and `k` one of
`X ^ 2`, given a sub-σ-algebra, then `k - g ^ 2` is a conditional variance of `X`: the conditional
variance is the conditional second moment minus the square of the conditional mean. No
σ-finiteness is needed. -/
theorem isCondVar_condExp_sq_sub_sq_condExp (hm : m ≤ m₀) (hX : Integrable X μ)
    (hX₂ : MemLp X 2 μ) (hg : IsCondExp m μ X g) (hk : IsCondExp m μ (X ^ 2) k) :
    IsCondVar m μ X (k - g ^ 2) := by
  have hg₂ : MemLp g 2 μ := hg.memLp one_le_two hm hX hX₂
  have hX_sq : Integrable (X ^ 2) μ := hX₂.integrable_sq
  have hXg : Integrable (X * g) μ := hX₂.integrable_mul hg₂
  -- pull-out property: `g * g` is a conditional expectation of `X * g`
  have h_mul : IsCondExp m μ (X * g) (g * g) := hg.mul_right hm hg.aestronglyMeasurable hXg hX
  have h_sq : IsCondExp m μ (g ^ 2) (g ^ 2) := isCondExp_self (hg.aestronglyMeasurable.pow 2)
  have h := (hk.sub (h_mul.smul (2 : ℝ)) hX_sq (hXg.smul (2 : ℝ))).add h_sq
    (hX_sq.sub (hXg.smul (2 : ℝ))) hg₂.integrable_sq
  refine ⟨g, hg, h.congr (.of_forall fun ω ↦ ?_) (.of_forall fun ω ↦ ?_)⟩
  all_goals
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, Pi.pow_apply, smul_eq_mul]
    ring

namespace IsCondVar

/-- A conditional variance of an integrable, square-integrable `X` given a sub-σ-algebra is at most
a conditional expectation of `X ^ 2`. -/
theorem ae_le_condExp_sq (hm : m ≤ m₀) (h : IsCondVar m μ X v) (hX : Integrable X μ)
    (hX₂ : MemLp X 2 μ) (hk : IsCondExp m μ (X ^ 2) k) : v ≤ᵐ[μ] k := by
  obtain ⟨g, hg, -⟩ := id h
  filter_upwards [h.ae_eq hm hX hX₂ (isCondVar_condExp_sq_sub_sq_condExp hm hX hX₂ hg hk)]
    with ω hω
  rw [hω, Pi.sub_apply, Pi.pow_apply]
  exact sub_le_self _ (sq_nonneg _)

/-- **Law of total variance**: for a probability measure, the integral of a conditional variance
of a square-integrable `X` plus the variance of a conditional expectation of `X` is the variance of
`X`. -/
theorem integral_add_variance (hm : m ≤ m₀) [IsProbabilityMeasure μ] (h : IsCondVar m μ X v)
    (hX₂ : MemLp X 2 μ) (hg : IsCondExp m μ X g) :
    ∫ ω, v ω ∂μ + Var[g; μ] = Var[X; μ] := by
  have hX : Integrable X μ := hX₂.integrable one_le_two
  have hX_sq : Integrable (X ^ 2) μ := hX₂.integrable_sq
  have hg₂ : MemLp g 2 μ := hg.memLp one_le_two hm hX hX₂
  obtain ⟨k, -, hk⟩ := exists_stronglyMeasurable_isCondExp hm hX_sq
  rw [integral_congr_ae (h.ae_eq hm hX hX₂ (isCondVar_condExp_sq_sub_sq_condExp hm hX hX₂ hg hk))]
  simp only [Pi.sub_apply]
  rw [integral_sub (g := g ^ 2) (hk.integrable hX_sq) hg₂.integrable_sq,
    hk.integral_eq hX_sq, variance_eq_sub hg₂, variance_eq_sub hX₂, hg.integral_eq hX]
  ring

end IsCondVar

/-- Given the trivial σ-algebra, the conditional variance of a square-integrable random variable
for a finite measure is the constant function equal to the mean of its square deviation from its
mean. -/
theorem isCondVar_bot [IsFiniteMeasure μ] (hX : MemLp X 2 μ) :
    IsCondVar ⊥ μ X fun _ ↦ ⨍ ω, (X ω - ⨍ ω', X ω' ∂μ) ^ 2 ∂μ := by
  refine ⟨fun _ ↦ ⨍ ω, X ω ∂μ, ?_, ?_⟩
  · simpa only [average_eq] using isCondExp_bot (hX.integrable one_le_two)
  · simpa only [average_eq, Pi.sub_apply] using
      isCondExp_bot (μ := μ) (hX.sub (memLp_const (⨍ ω, X ω ∂μ))).integrable_sq

/-! ### The domain -/

namespace HasCondVar

/-- A random variable in the domain has a conditional variance. -/
theorem exists_isCondVar (h : HasCondVar m μ X) : ∃ v, IsCondVar m μ X v :=
  let ⟨g, hg⟩ := h.hasUniqueCondExp.exists_isCondExp
  let ⟨v, hv⟩ := (h.hasUniqueCondExp_sub_sq hg).exists_isCondExp
  ⟨v, g, hg, hv⟩

/-- Two conditional variances of a random variable in the domain agree almost everywhere. -/
theorem ae_eq_of_isCondVar (h : HasCondVar m μ X) (h₁ : IsCondVar m μ X v)
    (h₂ : IsCondVar m μ X v') : v =ᵐ[μ] v' := by
  obtain ⟨g, hg, hv⟩ := h₁
  exact (h.hasUniqueCondExp_sub_sq hg).ae_eq_of_isCondExp hv
    ((isCondVar_iff_of_ae_eq hg fun _ hg' ↦ h.hasUniqueCondExp.ae_eq_of_isCondExp hg' hg).1 h₂)

theorem congr (h : HasCondVar m μ X) (hXY : X =ᵐ[μ] Y) : HasCondVar m μ Y where
  hasUniqueCondExp := h.hasUniqueCondExp.congr hXY
  hasUniqueCondExp_sub_sq g hg := by
    refine (h.hasUniqueCondExp_sub_sq (hg.congr_left hXY.symm)).congr ?_
    filter_upwards [hXY] with ω hω
    rw [hω]

/-- A conditional variance of an integrable, square-integrable random variable given a
sub-σ-algebra makes it unique. No σ-finiteness is needed. -/
theorem of_isCondVar (hm : m ≤ m₀) (hX : Integrable X μ) (hX₂ : MemLp X 2 μ)
    (hv : IsCondVar m μ X v) : HasCondVar m μ X := by
  obtain ⟨g, hg, -⟩ := id hv
  exact ⟨.of_isCondExp hm hX hg, fun g' hg' ↦ .of_isCondExp hm (hg'.integrable_sub_sq hm hX hX₂)
    (hv.isCondExp_sub_sq hm hX hg')⟩

/-- An integrable, square-integrable random variable has a conditional variance given a
sub-σ-algebra on which the measure is σ-finite, unique almost everywhere. -/
theorem of_memLp (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)] (hX : Integrable X μ)
    (hX₂ : MemLp X 2 μ) : HasCondVar m μ X := by
  obtain ⟨g, -, hg⟩ := exists_stronglyMeasurable_isCondExp hm hX
  obtain ⟨v, -, hv⟩ := exists_stronglyMeasurable_isCondExp hm (hg.integrable_sub_sq hm hX hX₂)
  exact of_isCondVar hm hX hX₂ ⟨g, hg, hv⟩

end HasCondVar

/-- `has_cond_var` proves `HasCondVar m μ X`, the domain of the conditional variance
`Var[X; μ | m]`: it tries a hypothesis, then `HasCondVar.of_memLp`. It proves the sub-σ-algebra
hypothesis with `sub_sigma_algebra`, finds the σ-finiteness by instance search, takes the
square-integrability from a hypothesis, and proves the integrability with `integrability` or, for a
finite measure, from the square-integrability. Later files extend it with `macro_rules`. -/
syntax (name := hasCondVar) "has_cond_var" : tactic

macro_rules
  | `(tactic| has_cond_var) => `(tactic| first
    | done
    | assumption
    | exact ProbabilityTheory.HasCondVar.of_memLp (by sub_sigma_algebra) (by integrability)
        (by assumption)
    | exact ProbabilityTheory.HasCondVar.of_memLp (by sub_sigma_algebra)
        (MeasureTheory.MemLp.integrable one_le_two (by assumption)) (by assumption)
    | fail "this random variable needs a proof `HasCondVar m μ X` that it has a conditional \
        variance given `m`, unique almost everywhere, for example from its integrability, its \
        square-integrability and the σ-finiteness of `μ` on `m`")

/-! ### The conditional variance as an almost everywhere class -/

/-- Some germ along `ae μ` is represented by a conditional variance of `X`. By the uniqueness in
`HasCondVar m μ X`, such a germ is unique. -/
theorem exists_germ_isCondVar (h : HasCondVar m μ X) :
    ∃ φ : (ae μ).Germ ℝ, ∃ v, IsCondVar m μ X v ∧ v ∈ φ :=
  let ⟨v, hv⟩ := h.exists_isCondVar
  ⟨v, v, hv, Germ.coe_mem v⟩

variable (m) in
/-- The conditional variance of the real-valued random variable `X` given the σ-algebra `m` with
respect to `μ`, with notation `Var[X; μ | m]`, and `Var[X | m]` for the measure `volume`: the almost
everywhere class of the conditional variances of `X`, as a germ along `ae μ`. A function `v`
represents it, written `v ∈ Var[X; μ | m]`, exactly when it is a conditional variance of `X`
(`ProbabilityTheory.mem_condVar_iff`), and `Var[X; μ | m] = μ[(X - g) ^ 2 | m]` for each
representative `g` of `μ[X | m]` (`ProbabilityTheory.condVar_eq_condExp`).

It takes a proof of `HasCondVar m μ X`, its exact domain, which the tactic `has_cond_var` finds for
an integrable, square-integrable `X` and a sub-σ-algebra on which `μ` is σ-finite. -/
noncomputable def condVar (μ : Measure[m₀] Ω) (X : Ω → ℝ)
    (h : HasCondVar m μ X := by has_cond_var) : (ae μ).Germ ℝ :=
  (exists_germ_isCondVar h).choose

@[inherit_doc ProbabilityTheory.condVar]
scoped macro:max "Var[" X:term "; " μ:term " | " m:term "]" : term =>
  `(ProbabilityTheory.condVar $m $μ $X)

@[inherit_doc ProbabilityTheory.condVar]
scoped macro:max "Var[" X:term " | " m:term "]" : term =>
  `(ProbabilityTheory.condVar $m MeasureTheory.MeasureSpace.volume $X)

/-- Unexpander for the `Var[X; μ | m]` notation. -/
@[app_unexpander ProbabilityTheory.condVar]
meta def condVarUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $m $μ $X $_) => `(Var[$X; $μ | $m])
  | _ => throw ()

/-- info: fun h ↦ Var[X; μ | m] : HasCondVar m μ X → (ae μ).Germ ℝ -/
#guard_msgs in
#check fun h : HasCondVar m μ X ↦ Var[X; μ | m]

/-- Every conditional variance of `X` represents `Var[X; μ | m]`. -/
theorem IsCondVar.mem_condVar (h : HasCondVar m μ X) (hv : IsCondVar m μ X v) :
    v ∈ condVar m μ X h := by
  obtain ⟨v', hv', hv'_mem⟩ := (exists_germ_isCondVar h).choose_spec
  exact Germ.mem_of_eventuallyEq hv'_mem (h.ae_eq_of_isCondVar hv' hv)

/-- Every representative of `Var[X; μ | m]` is a conditional variance of `X`. -/
theorem isCondVar_of_mem_condVar (h : HasCondVar m μ X) (hv : v ∈ condVar m μ X h) :
    IsCondVar m μ X v := by
  obtain ⟨v', hv', hv'_mem⟩ := (exists_germ_isCondVar h).choose_spec
  exact hv'.congr_right (Germ.eventuallyEq_of_mem hv'_mem hv)

/-- The representatives of `Var[X; μ | m]` are the conditional variances of `X`. -/
theorem mem_condVar_iff (h : HasCondVar m μ X) : v ∈ condVar m μ X h ↔ IsCondVar m μ X v :=
  ⟨isCondVar_of_mem_condVar h, fun hv ↦ hv.mem_condVar h⟩

/-- `Var[X; μ | m]` is the class of any conditional variance of `X`. -/
theorem IsCondVar.condVar_eq (h : HasCondVar m μ X) (hv : IsCondVar m μ X v) :
    condVar m μ X h = v :=
  Germ.eq_coe_of_mem (hv.mem_condVar h)

/-- `Var[X; μ | m] = μ[(X - g) ^ 2 | m]` for each conditional expectation `g` of `X`, that is, for
each representative `g` of `μ[X | m]`. -/
theorem condVar_eq_condExp (h : HasCondVar m μ X) (hg : IsCondExp m μ X g) :
    condVar m μ X h = condExp m μ (fun ω ↦ (X ω - g ω) ^ 2) (h.hasUniqueCondExp_sub_sq hg) := by
  obtain ⟨v, hv⟩ := (h.hasUniqueCondExp_sub_sq hg).exists_isCondExp
  rw [IsCondVar.condVar_eq h ⟨g, hg, hv⟩, hv.condExp_eq]

theorem condVar_congr_ae (h : HasCondVar m μ X) (hXY : X =ᵐ[μ] Y) :
    condVar m μ X h = condVar m μ Y (h.congr hXY) := by
  obtain ⟨v, hv⟩ := h.exists_isCondVar
  rw [hv.condVar_eq h, (hv.congr_left hXY).condVar_eq]

/-- The conditional variance of an almost everywhere `m`-strongly measurable random variable given
`m` is zero. -/
theorem condVar_eq_zero_of_aestronglyMeasurable (h : HasCondVar m μ X)
    (hX : AEStronglyMeasurable[m] X μ) : condVar m μ X h = 0 :=
  (isCondVar_zero_of_aestronglyMeasurable hX).condVar_eq h

@[simp]
theorem condVar_zero (h : HasCondVar m μ 0) : condVar m μ 0 h = 0 :=
  condVar_eq_zero_of_aestronglyMeasurable h aestronglyMeasurable_zero

@[simp]
theorem condVar_const (c : ℝ) (h : HasCondVar m μ fun _ ↦ c) : condVar m μ (fun _ ↦ c) h = 0 :=
  condVar_eq_zero_of_aestronglyMeasurable h aestronglyMeasurable_const

/-- `Var[X; μ | m] = μ[X ^ 2 | m] - μ[X | m] ^ 2`: the conditional variance is the conditional
second moment minus the square of the conditional mean. -/
theorem condVar_eq_condExp_sq_sub_sq_condExp (hm : m ≤ m₀) (hX : Integrable X μ)
    (hX₂ : MemLp X 2 μ) (h : HasCondVar m μ X) (h₂ : HasUniqueCondExp m μ (X ^ 2)) :
    condVar m μ X h = condExp m μ (X ^ 2) h₂ - condExp m μ X h.hasUniqueCondExp ^ 2 := by
  obtain ⟨g, hg⟩ := h.hasUniqueCondExp.exists_isCondExp
  obtain ⟨k, hk⟩ := h₂.exists_isCondExp
  rw [hg.condExp_eq, hk.condExp_eq, ← Germ.coe_pow, ← Germ.coe_sub,
    (isCondVar_condExp_sq_sub_sq_condExp hm hX hX₂ hg hk).condVar_eq]

/-- `Var[X; μ | m] ≤ μ[X ^ 2 | m]`. -/
theorem condVar_le_condExp_sq (hm : m ≤ m₀) (hX : Integrable X μ) (hX₂ : MemLp X 2 μ)
    (h : HasCondVar m μ X) (h₂ : HasUniqueCondExp m μ (X ^ 2)) :
    condVar m μ X h ≤ condExp m μ (X ^ 2) h₂ := by
  obtain ⟨v, hv⟩ := h.exists_isCondVar
  obtain ⟨k, hk⟩ := h₂.exists_isCondExp
  rw [hv.condVar_eq h, hk.condExp_eq]
  exact Germ.coe_le.2 (hv.ae_le_condExp_sq hm hX hX₂ hk)

/-- Given the trivial σ-algebra, the conditional variance of a square-integrable random variable for
a probability measure is its variance. -/
@[simp]
theorem condVar_bot [IsProbabilityMeasure μ] (hX : MemLp X 2 μ) (h : HasCondVar ⊥ μ X) :
    condVar ⊥ μ X h = (Var[X; μ] : (ae μ).Germ ℝ) := by
  rw [(isCondVar_bot hX).condVar_eq h]
  simp only [average_eq_integral, variance_eq_integral hX.aemeasurable]
  rfl

theorem condVar_smul (c : ℝ) (h : HasCondVar m μ X) (h' : HasCondVar m μ (c • X)) :
    condVar m μ (c • X) h' = c ^ 2 • condVar m μ X h := by
  obtain ⟨v, hv⟩ := h.exists_isCondVar
  rw [hv.condVar_eq h, ← Germ.coe_smul, (hv.smul c).condVar_eq h']

theorem condVar_neg (h : HasCondVar m μ X) (h' : HasCondVar m μ (-X)) :
    condVar m μ (-X) h' = condVar m μ X h := by
  obtain ⟨v, hv⟩ := h.exists_isCondVar
  rw [hv.condVar_eq h, hv.neg.condVar_eq h']

end ProbabilityTheory
