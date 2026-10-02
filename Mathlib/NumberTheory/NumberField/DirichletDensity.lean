/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Riccardo Brasca, Xavier Roblot
-/
module

public import Mathlib.NumberTheory.NumberField.DedekindZeta

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
The series converge and the denominator is positive for every `s > 1`.
`Mathlib.NumberTheory.NumberField.DirichletDensity.Asymptotics` proves equivalence with the
logarithmic normalization and that finite sets have density zero.

## Main results

* `NumberField.Set.summable_primeIdealZeta` — the series over all nonzero prime ideals converges
  for `s > 1`.
* `NumberField.Set.primeIdealZetaSum_univ_pos` — its sum is positive for `s > 1`.
* `NumberField.Set.primeIdealZetaSum_le_card_of_finite` — for a finite `S`, the partial sum is
  bounded above by the number of elements of `S`.
* `NumberField.Set.hasDirichletDensity_empty` — the empty set has Dirichlet density `0`.
* `NumberField.Set.hasDirichletDensity_univ` — the full set has Dirichlet density `1`.
* `NumberField.Set.DirichletDensity` — the subsingleton type of certified densities of a set.
* `NumberField.Set.HasDirichletDensity.nonneg` — a Dirichlet density is nonnegative.
* `NumberField.Set.HasDirichletDensity.le_one` — a Dirichlet density is at most `1`.

-/

public section

noncomputable section

open Filter IsDedekindDomain Set

open scoped Topology
open scoped nonZeroDivisors

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

variable (K) in
/-- The series of inverse norm powers over nonzero prime ideals converges for `s > 1`. -/
theorem summable_primeIdealZeta {s : ℝ} (hs : 1 < s) :
    Summable (fun 𝔭 : HeightOneSpectrum (𝓞 K) ↦ (𝔭.asIdeal.absNorm : ℝ) ^ (-s)) := by
  let f : HeightOneSpectrum (𝓞 K) → (Ideal (𝓞 K))⁰ := fun 𝔭 ↦
    ⟨𝔭.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr 𝔭.ne_bot⟩
  have hf : Function.Injective f := fun _ _ h ↦
    HeightOneSpectrum.asIdeal_injective (congrArg Subtype.val h)
  exact (summable_absNorm_rpow K hs).comp_injective (i := f) hf

/-- Restricting the prime-ideal series to any set preserves convergence for `s > 1`. -/
theorem summable_primeIdealZetaSum {s : ℝ} (hs : 1 < s) :
    Summable (fun 𝔭 : S ↦ (𝔭.1.asIdeal.absNorm : ℝ) ^ (-s)) :=
  (summable_primeIdealZeta K hs).subtype S

variable {S} in
/-- A nonempty set of prime ideals has a positive sum for `s > 1`. -/
theorem primeIdealZetaSum_pos (hS : S.Nonempty) {s : ℝ} (hs : 1 < s) :
    0 < S.primeIdealZetaSum s := by
  obtain ⟨𝔭, h𝔭⟩ := hS
  refine (summable_primeIdealZetaSum S hs).tsum_pos (fun _ ↦ by positivity) ⟨𝔭, h𝔭⟩
    (Real.rpow_pos_of_pos ?_ _)
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr 𝔭.ne_bot)

variable (K) in
/-- The denominator in the Dirichlet-density ratio is positive for `s > 1`. -/
theorem primeIdealZetaSum_univ_pos {s : ℝ} (hs : 1 < s) :
    0 < primeIdealZetaSum (univ : Set (HeightOneSpectrum (𝓞 K))) s := by
  obtain ⟨𝔭, -⟩ := (HeightOneSpectrum.ideal_ne_top_iff_exists
    (RingOfIntegers.not_isField K) (⊥ : Ideal (𝓞 K))).mp bot_ne_top
  exact primeIdealZetaSum_pos ⟨𝔭, mem_univ _⟩ hs

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
@[expose] def HasDirichletDensity (δ : ℝ) : Prop :=
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

/-- The set of all nonzero prime ideals has Dirichlet density `1`. -/
theorem hasDirichletDensity_univ :
    HasDirichletDensity (univ : Set (HeightOneSpectrum (𝓞 K))) 1 := by
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (div_self (primeIdealZetaSum_univ_pos K hs).ne').symm

/-- The Dirichlet density is nonnegative. -/
theorem HasDirichletDensity.nonneg {δ : ℝ} (h : S.HasDirichletDensity δ) :
    0 ≤ δ :=
  ge_of_tendsto h <| Eventually.of_forall fun s ↦
    div_nonneg (S.primeIdealZetaSum_nonneg s) (univ.primeIdealZetaSum_nonneg s)

/-- The Dirichlet density is at most `1`. -/
theorem HasDirichletDensity.le_one {δ : ℝ} (h : S.HasDirichletDensity δ) :
    δ ≤ 1 := by
  refine le_of_tendsto h ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  apply (div_le_one (primeIdealZetaSum_univ_pos K hs)).mpr
  rw [primeIdealZetaSum_def, primeIdealZetaSum_def,
    tsum_univ fun 𝔭 : HeightOneSpectrum (𝓞 K) ↦ (𝔭.asIdeal.absNorm : ℝ) ^ (-s)]
  exact (summable_primeIdealZeta K hs).tsum_subtype_le _ S (fun _ ↦ by positivity)

end NumberField.Set
