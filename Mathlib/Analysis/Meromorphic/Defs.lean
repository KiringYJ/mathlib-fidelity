/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module

public import Mathlib.Analysis.Analytic.Constructions

/-!
# Meromorphy on a punctured neighborhood

A function on a domain over a normed field is meromorphic at an ambient point if the
domain covers a punctured neighborhood and a power of the local coordinate clears the
singularity there. A value at the point is unnecessary.
-/

@[expose] public section

open Filter Set
open scoped Topology

variable {𝕜 E D : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Meromorphy of a function on a domain that covers a punctured neighborhood of `x`.
The analytic numerator agrees with the cleared function throughout that punctured germ. -/
@[fun_prop]
def MeromorphicAt (f : D → E) (x : 𝕜) (coord : D → 𝕜 := by exact _root_.id) : Prop :=
  range coord ∈ 𝓝[≠] x ∧ ∃ (n : ℕ) (g : 𝕜 → E), AnalyticAt 𝕜 g x ∧
    ∀ᶠ y in comap coord (𝓝[≠] x), (coord y - x) ^ n • f y = g (coord y)

/-- For an ambient function one can choose the clearing power large enough that the
cleared function itself is analytic even at the center. -/
theorem MeromorphicAt.iff_exists_analyticAt_pow_smul {f : 𝕜 → E} {x : 𝕜} :
    MeromorphicAt f x ↔ ∃ n : ℕ, AnalyticAt 𝕜 (fun z ↦ (z - x) ^ n • f z) x := by
  constructor
  · rintro ⟨_, n, g, hg, he⟩
    have he' : ∀ᶠ y in 𝓝[≠] x, (y - x) ^ n • f y = g y := by simpa using he
    have hc : AnalyticAt 𝕜 (fun z ↦ z - x) x := analyticAt_id.sub analyticAt_const
    refine ⟨n + 1, (hc.fun_smul hg).congr ?_⟩
    filter_upwards [eventually_nhdsWithin_iff.mp he'] with y hy
    by_cases h : y = x
    · simp [h]
    · rw [pow_succ', mul_smul, hy h]
  · rintro ⟨n, hn⟩
    exact ⟨by simp, n, _, hn, .of_forall fun _ ↦ rfl⟩

/-- A parametrized neighborhood sees only the numerator identity near the puncture. -/
theorem MeromorphicAt.congr_domain {f g : D → E} {coord : D → 𝕜} {x : 𝕜}
    (hf : MeromorphicAt f x coord) (he : f =ᶠ[comap coord (𝓝[≠] x)] g) :
    MeromorphicAt g x coord := by
  obtain ⟨hc, n, a, ha, hfa⟩ := hf
  exact ⟨hc, n, a, ha, hfa.mp (he.mono fun y hy h ↦ hy ▸ h)⟩

/-- Restriction to a domain that still covers a punctured neighborhood. -/
theorem MeromorphicAt.comp_domain {D' : Type*} {f : D → E} {coord : D → 𝕜} {x : 𝕜}
    (hf : MeromorphicAt f x coord) (j : D' → D) (hc : range (coord ∘ j) ∈ 𝓝[≠] x) :
    MeromorphicAt (f ∘ j) x (coord ∘ j) := by
  obtain ⟨_, n, a, ha, he⟩ := hf
  refine ⟨hc, n, a, ha, ?_⟩
  rw [← comap_comap]
  exact tendsto_comap.eventually he

namespace MeromorphicAt

variable {coord : D → 𝕜} {x : 𝕜}

/-- Regularity at the center of a punctured meromorphic germ means that it has an
analytic extension across that point. -/
def IsRegular (f : D → E) (x : 𝕜) (coord : D → 𝕜 := by exact _root_.id) : Prop :=
  ∃ g : 𝕜 → E, AnalyticAt 𝕜 g x ∧ f =ᶠ[comap coord (𝓝[≠] x)] g ∘ coord

/-- The canonical value at a regular or removable point of a meromorphic germ. -/
noncomputable def value {f : D → E} (_hf : MeromorphicAt f x coord)
    (hr : IsRegular f x coord) : E :=
  hr.choose x

/-- Every analytic extension gives the same regular value. -/
theorem value_eq {f : D → E} (hf : MeromorphicAt f x coord) (hr : IsRegular f x coord)
    {g : 𝕜 → E} (hg : AnalyticAt 𝕜 g x) (he : f =ᶠ[comap coord (𝓝[≠] x)] g ∘ coord) :
    hf.value hr = g x := by
  have : (comap coord (𝓝[≠] x)).NeBot :=
    (inferInstance : (𝓝[≠] x).NeBot).comap_of_range_mem hf.1
  have ht : Tendsto coord (comap coord (𝓝[≠] x)) (𝓝 x) :=
    tendsto_comap.mono_right nhdsWithin_le_nhds
  exact tendsto_nhds_unique_of_eventuallyEq (hr.choose_spec.1.continuousAt.tendsto.comp ht)
    (hg.continuousAt.tendsto.comp ht) (hr.choose_spec.2.symm.trans he)

/-- On the punctured neighborhood a meromorphic function is an integer power of the
local coordinate times an analytic function. -/
theorem iff_eventuallyEq_zpow_smul_analyticAt {f : D → E} :
    MeromorphicAt f x coord ↔ range coord ∈ 𝓝[≠] x ∧
      ∃ (n : ℤ) (g : 𝕜 → E), AnalyticAt 𝕜 g x ∧
        ∀ᶠ y in comap coord (𝓝[≠] x), ∀ h : coord y ≠ x,
          f y = Checked.zpow (coord y - x) n
            (fun _ ↦ (sub_ne_zero.mpr h).isUnit) • g (coord y) := by
  constructor
  · rintro ⟨hc, m, g, hg, he⟩
    refine ⟨hc, -(m : ℤ), g, hg, he.mono fun y hy h ↦ ?_⟩
    let u := (sub_ne_zero.mpr h).isUnit.unit
    rw [(sub_ne_zero.mpr h).isUnit.zpow_eq_val_unit_zpow, zpow_neg, zpow_natCast, ← hy]
    simpa only [Units.smul_def, Units.val_pow_eq_pow_val, u, IsUnit.unit_spec] using
      (inv_smul_smul (u ^ m) (f y)).symm
  · rintro ⟨hc, n, g, hg, he⟩
    have hcoord : ∀ᶠ y in comap coord (𝓝[≠] x), coord y ≠ x :=
      tendsto_comap.eventually self_mem_nhdsWithin
    cases n with
    | ofNat n =>
      have hd : AnalyticAt 𝕜 (fun z ↦ z - x) x := analyticAt_id.sub analyticAt_const
      refine ⟨hc, 0, _, (hd.pow n).fun_smul hg, ?_⟩
      filter_upwards [hcoord, he] with y hy h
      have h' : f y = (coord y - x) ^ n • g (coord y) := by
        simpa only [Int.ofNat_eq_natCast, zpow_natCast₀] using h hy
      simpa only [pow_zero, one_smul, Pi.pow_apply] using h'
    | negSucc n =>
      refine ⟨hc, n + 1, g, hg, ?_⟩
      filter_upwards [hcoord, he] with y hy h
      rw [h hy, zpow_negSucc₀, smul_inv_smul₀]

@[to_fun (attr := fun_prop)]
theorem add {f g : D → E} (hf : MeromorphicAt f x coord) (hg : MeromorphicAt g x coord) :
    MeromorphicAt (f + g) x coord := by
  obtain ⟨hc, m, a, ha, he⟩ := hf
  obtain ⟨_, n, b, hb, he'⟩ := hg
  have hd : AnalyticAt 𝕜 (fun z ↦ z - x) x := analyticAt_id.sub analyticAt_const
  refine ⟨hc, m + n, _, ((hd.pow n).fun_smul ha).add ((hd.pow m).fun_smul hb), ?_⟩
  filter_upwards [he, he'] with y hy hy'
  simp only [Pi.add_apply, Pi.pow_apply, ← hy, ← hy', ← mul_smul, ← pow_add,
    smul_add, Nat.add_comm n m]

variable {R : Type*} [NormedRing R] [NormedAlgebra 𝕜 R] [Module R E] [IsBoundedSMul R E]
  [IsScalarTower 𝕜 R E]

@[to_fun (attr := fun_prop)]
theorem smul {f : D → R} {g : D → E} (hf : MeromorphicAt f x coord)
    (hg : MeromorphicAt g x coord) : MeromorphicAt (f • g) x coord := by
  obtain ⟨hc, m, a, ha, he⟩ := hf
  obtain ⟨_, n, b, hb, he'⟩ := hg
  refine ⟨hc, m + n, _, ha.smul hb, ?_⟩
  filter_upwards [he, he'] with y hy hy'
  simp only [Pi.smul_apply', ← hy, ← hy', smul_smul_smul_comm, smul_eq_mul, pow_add]

@[to_fun (attr := fun_prop)]
theorem mul {f g : D → R} (hf : MeromorphicAt f x coord) (hg : MeromorphicAt g x coord) :
    MeromorphicAt (f * g) x coord := by simpa using hf.smul hg

@[to_fun (attr := fun_prop)]
theorem pow {f : D → R} (hf : MeromorphicAt f x coord) (n : ℕ) :
    MeromorphicAt (f ^ n) x coord := by
  induction n with
  | zero =>
    refine ⟨hf.1, 0, 1, analyticAt_const, .of_forall fun y ↦ ?_⟩
    simp
  | succ n ih => simpa only [pow_succ] using ih.mul hf

end MeromorphicAt
