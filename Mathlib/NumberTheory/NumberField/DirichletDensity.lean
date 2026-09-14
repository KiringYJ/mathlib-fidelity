/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Riccardo Brasca, Xavier Roblot
-/
module

public import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-!
# Dirichlet density of a set of prime ideals

Let `K` be a number field. Given a set `S` of nonzero prime ideals of `𝓞 K`, its Dirichlet
density is
$$
\delta(S) = \lim_{s \to 1^+}
  \frac{\sum_{\mathfrak p \in S} \operatorname{N} \mathfrak p^{-s}}
    {\sum_{\mathfrak p} \operatorname{N} \mathfrak p^{-s}},
$$
when this limit exists. The sum in the denominator runs over all nonzero prime ideals of `𝓞 K`.

This is captured by the predicate `HasDirichletDensity S δ`, stating that the ratio tends to `δ`.
The type `DirichletDensity S` carries a real number together with such a proof; it is empty when no
density exists and a subsingleton because limits in `ℝ` are unique.

## Main results

* `NumberField.Set.primeIdealZetaSum_le_card_of_finite` — for a finite `S`, the partial sum is
  bounded above by the number of elements of `S`.
* `NumberField.Set.hasDirichletDensity_empty` — the empty set has Dirichlet density `0`.
* `NumberField.Set.DirichletDensity` — the subsingleton type of certified densities of a set.
* `NumberField.Set.HasDirichletDensity.nonneg` — a Dirichlet density is nonnegative.
* `NumberField.Set.HasDirichletDensity.le_one` — a Dirichlet density is at most `1`.

-/

public section

noncomputable section

open Filter IsDedekindDomain Set

open scoped Topology

namespace NumberField.Set

open NumberField

variable {K : Type*} [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))

/-- The partial Dirichlet series $\sum_{\mathfrak p \in S} \operatorname{N} \mathfrak p^{-s}$. -/
def primeIdealZetaSum (S : Set (HeightOneSpectrum (𝓞 K))) (s : ℝ) : ℝ :=
  ∑' 𝔭 : S, (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s)

theorem primeIdealZetaSum_def (s : ℝ) :
    S.primeIdealZetaSum s = ∑' 𝔭 : S, (Ideal.absNorm 𝔭.1.asIdeal : ℝ) ^ (-s) := by rfl

theorem primeIdealZetaSum_nonneg (s : ℝ) :
    0 ≤ S.primeIdealZetaSum s :=
  tsum_nonneg fun _ ↦ by positivity

variable {S} in
/-- For a finite set `S` of prime ideals, the partial sum
$\sum_{\mathfrak p \in S} \operatorname{N} \mathfrak p^{-s}$ is bounded above by the number of
elements of `S`. -/
theorem primeIdealZetaSum_le_card_of_finite (hS : S.Finite) {s : ℝ} (hs : 0 ≤ s) :
    S.primeIdealZetaSum s ≤ S.ncard := by
  replace hS := hS.to_subtype
  grw [primeIdealZetaSum_def, Real.rpow_le_one_of_one_le_of_nonpos] <;>
  simp [Summable.of_finite, Nat.one_le_iff_ne_zero,
    Ideal.absNorm_eq_zero_iff, hs, HeightOneSpectrum.ne_bot]

/-- `S` has Dirichlet density `δ` when the ratio of the partial sum over `S` to the sum over all
nonzero prime ideals,
$$
\frac{\sum_{\mathfrak p \in S} \operatorname{N} \mathfrak p^{-s}}
  {\sum_{\mathfrak p} \operatorname{N} \mathfrak p^{-s}},
$$
tends to `δ` as $s \to 1^+$. -/
def HasDirichletDensity (δ : ℝ) : Prop :=
  Tendsto (fun s : ℝ ↦ S.primeIdealZetaSum s /
    primeIdealZetaSum (univ : Set (HeightOneSpectrum (𝓞 K))) s) (𝓝[>] 1) (𝓝 δ)

variable {S}

/-- A set has at most one Dirichlet density. -/
theorem HasDirichletDensity.unique {δ ε : ℝ} (hδ : S.HasDirichletDensity δ)
    (hε : S.HasDirichletDensity ε) : δ = ε :=
  tendsto_nhds_unique hδ hε

/-- The type of Dirichlet densities of `S`. It is empty when no density exists and contains at most
one element. Keeping the witness in `Type` avoids extracting it from propositional existence. -/
abbrev DirichletDensity (S : Set (HeightOneSpectrum (𝓞 K))) :=
  {δ : ℝ // S.HasDirichletDensity δ}

instance : Subsingleton (DirichletDensity S) where
  allEq d e := Subtype.ext (d.property.unique e.property)

/-- Bundle a real number known to be the Dirichlet density of `S`. -/
protected abbrev HasDirichletDensity.toDirichletDensity {δ : ℝ}
    (h : S.HasDirichletDensity δ) : DirichletDensity S :=
  ⟨δ, h⟩

namespace DirichletDensity

/-- A certified Dirichlet density satisfies the ordinary relational predicate. -/
protected theorem hasDirichletDensity (d : DirichletDensity S) :
    S.HasDirichletDensity (d : ℝ) :=
  d.property

end DirichletDensity

/-- Coercing a bundled Dirichlet density to `ℝ` returns the certified value. -/
@[simp]
theorem coe_toDirichletDensity {δ : ℝ} (h : S.HasDirichletDensity δ) :
    (h.toDirichletDensity : ℝ) = δ :=
  rfl

/-- The certified-density fiber is nonempty exactly when some Dirichlet density exists. -/
theorem nonempty_dirichletDensity_iff :
    Nonempty (DirichletDensity S) ↔ ∃ δ, S.HasDirichletDensity δ :=
  nonempty_subtype

/-- The empty set has Dirichlet density `0`. -/
theorem hasDirichletDensity_empty :
    HasDirichletDensity (∅ : Set (HeightOneSpectrum (𝓞 K))) 0 := by
  simp [HasDirichletDensity, primeIdealZetaSum_def]

/-- The Dirichlet density is nonnegative. -/
theorem HasDirichletDensity.nonneg {δ : ℝ} (h : S.HasDirichletDensity δ) :
    0 ≤ δ :=
  ge_of_tendsto h <| Eventually.of_forall fun s ↦
    div_nonneg (S.primeIdealZetaSum_nonneg s) (univ.primeIdealZetaSum_nonneg s)

/-- The Dirichlet density is at most `1`. -/
theorem HasDirichletDensity.le_one {δ : ℝ} (h : S.HasDirichletDensity δ) :
    δ ≤ 1 := by
  refine le_of_tendsto h (Eventually.of_forall fun s ↦ ?_)
  rw [primeIdealZetaSum_def, primeIdealZetaSum_def,
    tsum_univ fun 𝔭 : HeightOneSpectrum (𝓞 K) ↦ (𝔭.asIdeal.absNorm : ℝ) ^ (-s)]
  by_cases hs : Summable fun 𝔭 : HeightOneSpectrum (𝓞 K) ↦ (𝔭.asIdeal.absNorm : ℝ) ^ (-s)
  · exact div_le_one_of_le₀ (hs.tsum_subtype_le _ S (fun _ ↦ by positivity))
      (tsum_nonneg fun _ ↦ by positivity)
  · grw [tsum_eq_zero_of_not_summable hs, div_zero, zero_le_one]

end NumberField.Set
