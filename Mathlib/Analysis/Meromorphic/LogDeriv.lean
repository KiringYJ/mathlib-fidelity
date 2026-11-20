/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Meromorphic.Order

/-!
# Meromorphic API for the Logarithmic Derivative
-/

@[expose] public section

open Filter Function Set Topology

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  {f g : 𝕜 → 𝕜'} {x : 𝕜} {U : Set 𝕜}

/-!
## Arithmetic on Codiscrete Sets

The pointwise lemma `logDeriv_mul` requires differentiability and nonvanishing of the factors at the
point in question. For meromorphic functions whose order is nowhere `⊤`, both conditions hold away
from a codiscrete set, turning the pointwise arithmetic into arithmetic of codiscrete equivalence
classes.
-/

/--
The logarithmic derivative converts products into sums: away from a codiscrete subset of `U`, the
logarithmic derivative of a product of two meromorphic functions is the sum of the logarithmic
derivatives.
-/
theorem MeromorphicOn.logDeriv_mul_eventuallyEq (hf : MeromorphicOn f U) (hg : MeromorphicOn g U)
    (h'f : ∀ x (hx : x ∈ U), meromorphicOrderAt f x (hf x hx) ≠ ⊤)
    (h'g : ∀ x (hx : x ∈ U), meromorphicOrderAt g x (hg x hx) ≠ ⊤) :
    ∀ᶠ y in codiscreteWithin U, ∃ (df : DifferentiableAt 𝕜 f y) (dg : DifferentiableAt 𝕜 g y)
      (uf : IsUnit (f y)) (ug : IsUnit (g y)),
      logDeriv (f * g) y id (df.hasDerivAt.mul dg.hasDerivAt).existsUnique_hasDerivAt (uf.mul ug) =
        logDeriv f y id df.existsUnique_hasDerivAt uf +
          logDeriv g y id dg.existsUnique_hasDerivAt ug := by
  filter_upwards [hf.analyticAt_mem_codiscreteWithin, hg.analyticAt_mem_codiscreteWithin,
    hf.eventually_codiscreteWithin_apply_ne_zero h'f,
    hg.eventually_codiscreteWithin_apply_ne_zero h'g]
    with y hf hg uf ug
  exact ⟨hf.differentiableAt, hg.differentiableAt, uf.isUnit, ug.isUnit,
    logDeriv_mul y hf.differentiableAt hg.differentiableAt⟩

/-- The product rule holds on a codiscrete set of common regular, nonzero points. -/
theorem Meromorphic.logDeriv_mul_eventuallyEq (hf : Meromorphic f) (hg : Meromorphic g)
    (h'f : ∀ x, meromorphicOrderAt f x (hf x) ≠ ⊤)
    (h'g : ∀ x, meromorphicOrderAt g x (hg x) ≠ ⊤) :
    ∀ᶠ y in codiscrete 𝕜, ∃ (df : DifferentiableAt 𝕜 f y) (dg : DifferentiableAt 𝕜 g y)
      (uf : IsUnit (f y)) (ug : IsUnit (g y)),
      logDeriv (f * g) y id (df.hasDerivAt.mul dg.hasDerivAt).existsUnique_hasDerivAt (uf.mul ug) =
        logDeriv f y id df.existsUnique_hasDerivAt uf +
          logDeriv g y id dg.existsUnique_hasDerivAt ug :=
  hf.meromorphicOn.logDeriv_mul_eventuallyEq hg.meromorphicOn (fun x _ ↦ h'f x) (fun x _ ↦ h'g x)

/--
The logarithmic derivative converts products into sums: away from a codiscrete subset of `U`, the
logarithmic derivative of a finite product of meromorphic functions is the sum of the logarithmic
derivatives.
-/
theorem MeromorphicOn.logDeriv_prod_eventuallyEq {ι : Type*} {s : Finset ι} {F : ι → 𝕜 → 𝕜'}
    (h : ∀ i ∈ s, MeromorphicOn (F i) U)
    (h' : ∀ i (hi : i ∈ s) x (hx : x ∈ U), meromorphicOrderAt (F i) x (h i hi x hx) ≠ ⊤) :
    ∀ᶠ y in codiscreteWithin U, ∃ (df : ∀ i ∈ s, DifferentiableAt 𝕜 (F i) y)
      (uf : ∀ i ∈ s, F i y ≠ 0),
      logDeriv (∏ i ∈ s, F i) y id (DifferentiableAt.finsetProd df).existsUnique_hasDerivAt
          (by rw [Finset.prod_apply, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]; exact uf) =
        ∑ i ∈ s.attach,
          logDeriv (F i) y id (df i i.2).existsUnique_hasDerivAt (uf i i.2).isUnit := by
  have hA := (eventually_all_finset s).2 fun i hi ↦ (h i hi).analyticAt_mem_codiscreteWithin
  have hN := (eventually_all_finset s).2 fun i hi ↦
    (h i hi).eventually_codiscreteWithin_apply_ne_zero (h' i hi)
  filter_upwards [hA, hN] with y hd hu
  exact ⟨fun i hi ↦ (hd i hi).differentiableAt, hu,
    logDeriv_prod hu (fun i hi ↦ (hd i hi).differentiableAt)⟩

/-- On a codiscrete set the logarithmic derivative of a finite product equals the sum
of the logarithmic derivatives of its factors. -/
theorem Meromorphic.logDeriv_prod_eventuallyEq {ι : Type*} {s : Finset ι} {F : ι → 𝕜 → 𝕜'}
    (h : ∀ i ∈ s, Meromorphic (F i))
    (h' : ∀ i (hi : i ∈ s) x, meromorphicOrderAt (F i) x (h i hi x) ≠ ⊤) :
    ∀ᶠ y in codiscrete 𝕜, ∃ (df : ∀ i ∈ s, DifferentiableAt 𝕜 (F i) y)
      (uf : ∀ i ∈ s, F i y ≠ 0),
      logDeriv (∏ i ∈ s, F i) y id (DifferentiableAt.finsetProd df).existsUnique_hasDerivAt
          (by rw [Finset.prod_apply, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]; exact uf) =
        ∑ i ∈ s.attach, logDeriv (F i) y id (df i i.2).existsUnique_hasDerivAt (uf i i.2).isUnit :=
  MeromorphicOn.logDeriv_prod_eventuallyEq (fun i hi ↦ (h i hi).meromorphicOn)
    (fun i hi x _ ↦ h' i hi x)

/--
The logarithmic derivative converts products into sums: away from a codiscrete subset of `U`, the
logarithmic derivative of a finite product of meromorphic functions is the sum of the logarithmic
derivatives.
-/
theorem MeromorphicOn.logDeriv_finprod_eventuallyEq {ι : Type*} {F : ι → 𝕜 → 𝕜'}
    (hF : (mulSupport F).Finite) (h : ∀ i, MeromorphicOn (F i) U)
    (h' : ∀ i x (hx : x ∈ U), meromorphicOrderAt (F i) x (h i x hx) ≠ ⊤) :
    ∀ᶠ y in codiscreteWithin U, ∃ (df : ∀ i ∈ hF.toFinset, DifferentiableAt 𝕜 (F i) y)
      (uf : ∀ i ∈ hF.toFinset, F i y ≠ 0) (dp : DifferentiableAt 𝕜 (∏ᶠ i, F i) y)
      (up : IsUnit ((∏ᶠ i, F i) y)),
      logDeriv (∏ᶠ i, F i) y id dp.existsUnique_hasDerivAt up =
        ∑ i ∈ hF.toFinset.attach,
          logDeriv (F i) y id (df i i.2).existsUnique_hasDerivAt (uf i i.2).isUnit := by
  rw [finprod_eq_prod F hF]
  filter_upwards [MeromorphicOn.logDeriv_prod_eventuallyEq (s := hF.toFinset)
    (fun i _ ↦ h i) (fun i _ ↦ h' i)] with y ⟨df, uf, hp⟩
  exact ⟨df, uf, DifferentiableAt.finsetProd df,
    by rw [Finset.prod_apply]; exact (Finset.prod_ne_zero_iff.mpr uf).isUnit, hp⟩

/-- A product of finite multiplicative support obeys the logarithmic derivative rule
on a codiscrete set. -/
theorem Meromorphic.logDeriv_finprod_eventuallyEq {ι : Type*} {F : ι → 𝕜 → 𝕜'}
    (hF : (mulSupport F).Finite) (h : ∀ i, Meromorphic (F i))
    (h' : ∀ i x, meromorphicOrderAt (F i) x (h i x) ≠ ⊤) :
    ∀ᶠ y in codiscrete 𝕜, ∃ (df : ∀ i ∈ hF.toFinset, DifferentiableAt 𝕜 (F i) y)
      (uf : ∀ i ∈ hF.toFinset, F i y ≠ 0) (dp : DifferentiableAt 𝕜 (∏ᶠ i, F i) y)
      (up : IsUnit ((∏ᶠ i, F i) y)),
      logDeriv (∏ᶠ i, F i) y id dp.existsUnique_hasDerivAt up =
        ∑ i ∈ hF.toFinset.attach,
          logDeriv (F i) y id (df i i.2).existsUnique_hasDerivAt (uf i i.2).isUnit :=
  MeromorphicOn.logDeriv_finprod_eventuallyEq hF (fun i ↦ (h i).meromorphicOn) (fun i x _ ↦ h' i x)

/-- The logarithmic derivative of an integer power at common nonzero regular points. -/
theorem MeromorphicOn.logDeriv_zpow_eventuallyEq (hf : MeromorphicOn f U) (n : ℤ)
    (hn : ∀ x (hx : x ∈ U), meromorphicOrderAt f x (hf x hx) ≠ ⊤) :
    ∀ᶠ y in codiscreteWithin U, ∃ (df : DifferentiableAt 𝕜 f y) (uf : IsUnit (f y))
      (dp : ∃! d, HasDerivAt (fun z : {z : 𝕜 | n < 0 → IsUnit (f z)} ↦ Checked.zpow (f z) n z.2)
        d ⟨y, fun _ ↦ uf⟩ Subtype.val),
      logDeriv (fun z : {z : 𝕜 | n < 0 → IsUnit (f z)} ↦ Checked.zpow (f z) n z.2)
        ⟨y, fun _ ↦ uf⟩ Subtype.val dp (uf.zpow₀ n) =
          n * logDeriv f y id df.existsUnique_hasDerivAt uf := by
  filter_upwards [hf.analyticAt_mem_codiscreteWithin,
    hf.eventually_codiscreteWithin_apply_ne_zero hn]
    with y hd hu
  have hp := hd.differentiableAt.hasDerivAt.zpow (coord := id) n (fun _ ↦ hu.isUnit)
  have hmem : {z : 𝕜 | n < 0 → IsUnit (f z)} ∈ 𝓝 y :=
    (hd.continuousAt.eventually_ne hu).mono fun z hz _ ↦ hz.isUnit
  have dp := hp.existsUnique_hasDerivAt_of_mem_nhds IsEmbedding.subtypeVal
    (by change range (Subtype.val : {z : 𝕜 | n < 0 → IsUnit (f z)} → 𝕜) ∈ 𝓝 y
        rwa [Subtype.range_coe])
  exact ⟨hd.differentiableAt, hu.isUnit, dp, logDeriv_fun_zpow hd.differentiableAt n⟩

/-- The logarithmic derivative of an integer power at common nonzero regular points. -/
theorem Meromorphic.logDeriv_zpow_eventuallyEq (hf : Meromorphic f) (n : ℤ)
    (hn : ∀ x, meromorphicOrderAt f x (hf x) ≠ ⊤) :
    ∀ᶠ y in codiscrete 𝕜, ∃ (df : DifferentiableAt 𝕜 f y) (uf : IsUnit (f y))
      (dp : ∃! d, HasDerivAt (fun z : {z : 𝕜 | n < 0 → IsUnit (f z)} ↦ Checked.zpow (f z) n z.2)
        d ⟨y, fun _ ↦ uf⟩ Subtype.val),
      logDeriv (fun z : {z : 𝕜 | n < 0 → IsUnit (f z)} ↦ Checked.zpow (f z) n z.2)
        ⟨y, fun _ ↦ uf⟩ Subtype.val dp (uf.zpow₀ n) =
          n * logDeriv f y id df.existsUnique_hasDerivAt uf :=
  hf.meromorphicOn.logDeriv_zpow_eventuallyEq n (fun x _ ↦ hn x)

/-- The logarithmic derivative of a finite weighted product. The numerator and denominator
use the positive and negative multiplicities, so the scalar domain only excludes a zero
of a factor with a negative exponent. -/
theorem MeromorphicOn.logDeriv_finprod_zpow_eventuallyEq {ι : Type*} {F : ι → 𝕜 → 𝕜'} {d : ι → ℤ}
    (hd : (support d).Finite) (h : ∀ i, MeromorphicOn (F i) U)
    (h' : ∀ i x (hx : x ∈ U), meromorphicOrderAt (F i) x (h i x hx) ≠ ⊤) :
    let A := ∏ i ∈ hd.toFinset, (F i) ^ (d i).toNat
    let B := ∏ i ∈ hd.toFinset, (F i) ^ (-d i).toNat
    let Q := fun z : {z : 𝕜 | IsUnit (B z)} ↦ Checked.div (A z) (B z) z.property
    ∀ᶠ y in codiscreteWithin U, ∃ (df : ∀ i ∈ hd.toFinset, DifferentiableAt 𝕜 (F i) y)
      (uf : ∀ i ∈ hd.toFinset, IsUnit (F i y)) (hb : IsUnit (B y))
      (dq : ∃! v, HasDerivAt Q v ⟨y, hb⟩ Subtype.val) (uq : IsUnit (Q ⟨y, hb⟩)),
      logDeriv Q ⟨y, hb⟩ Subtype.val dq uq = ∑ i ∈ hd.toFinset.attach,
        (d i : 𝕜') *
          logDeriv (F i) y id (df i i.property).existsUnique_hasDerivAt (uf i i.property) := by
  intro A B Q
  have hA := (eventually_all_finset hd.toFinset).mpr fun i _ ↦ (h i).analyticAt_mem_codiscreteWithin
  have hN := (eventually_all_finset hd.toFinset).mpr fun i _ ↦
    (h i).eventually_codiscreteWithin_apply_ne_zero (h' i)
  filter_upwards [hA, hN] with y hy hny
  have df (i) (hi : i ∈ hd.toFinset) := (hy i hi).differentiableAt
  have uf (i) (hi : i ∈ hd.toFinset) := (hny i hi).isUnit
  let P (n : ι → ℕ) := ∏ i ∈ hd.toFinset, (F i) ^ n i
  have dp (n : ι → ℕ) : DifferentiableAt 𝕜 (P n) y := DifferentiableAt.finsetProd
    (fun i hi ↦ (df i hi).pow (n i))
  have up (n : ι → ℕ) : IsUnit (P n y) := by
    change IsUnit ((∏ i ∈ hd.toFinset, F i ^ n i) y)
    rw [Finset.prod_apply, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
    exact fun i hi ↦ pow_ne_zero _ (hny i hi)
  have lp (n : ι → ℕ) : logDeriv (P n) y id (dp n).existsUnique_hasDerivAt (up n) =
      ∑ i ∈ hd.toFinset.attach, (n i : 𝕜') *
        logDeriv (F i) y id (df i i.property).existsUnique_hasDerivAt (uf i i.property) := by
    apply (logDeriv_prod (f := fun i ↦ (F i) ^ n i) (fun i hi ↦ pow_ne_zero _ (hny i hi))
      (fun i hi ↦ (df i hi).pow (n i))).trans
    apply Finset.sum_congr rfl
    exact fun i _ ↦ logDeriv_fun_pow (df i i.property) (n i)
  let pos := fun i ↦ (d i).toNat
  let neg := fun i ↦ (-d i).toNat
  have hq := (dp pos).hasDerivAt.div (dp neg).hasDerivAt (up neg)
  have hmem : {x : 𝕜 | IsUnit (B x)} ∈ 𝓝 y :=
    ((dp neg).continuousAt.eventually_ne (up neg).ne_zero).mono (fun _ h ↦ h.isUnit)
  have dq := hq.existsUnique_hasDerivAt_of_mem_nhds IsEmbedding.subtypeVal (by
    change range (Subtype.val : {z : 𝕜 | IsUnit (B z)} → 𝕜) ∈ 𝓝 y
    rwa [Subtype.range_coe])
  refine ⟨df, uf, up neg, dq, (up pos).div₀ (up neg), ?_⟩
  apply (logDeriv_div y (dp pos) (dp neg)).trans
  rw [lp pos, lp neg, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← sub_mul]
  congr 1
  have hi : (pos i : ℤ) - neg i = d i := by dsimp [pos, neg]; omega
  simpa only [Int.cast_sub, Int.cast_natCast] using congrArg (Int.cast : ℤ → 𝕜') hi

/-- The weighted-product rule for meromorphic functions on the entire field. -/
theorem Meromorphic.logDeriv_finprod_zpow_eventuallyEq {ι : Type*} {F : ι → 𝕜 → 𝕜'} {d : ι → ℤ}
    (hd : (support d).Finite) (h : ∀ i, Meromorphic (F i))
    (h' : ∀ i x, meromorphicOrderAt (F i) x (h i x) ≠ ⊤) :
    let A := ∏ i ∈ hd.toFinset, (F i) ^ (d i).toNat
    let B := ∏ i ∈ hd.toFinset, (F i) ^ (-d i).toNat
    let Q := fun z : {z : 𝕜 | IsUnit (B z)} ↦ Checked.div (A z) (B z) z.property
    ∀ᶠ y in codiscrete 𝕜, ∃ (df : ∀ i ∈ hd.toFinset, DifferentiableAt 𝕜 (F i) y)
      (uf : ∀ i ∈ hd.toFinset, IsUnit (F i y)) (hb : IsUnit (B y))
      (dq : ∃! v, HasDerivAt Q v ⟨y, hb⟩ Subtype.val) (uq : IsUnit (Q ⟨y, hb⟩)),
      logDeriv Q ⟨y, hb⟩ Subtype.val dq uq = ∑ i ∈ hd.toFinset.attach,
        (d i : 𝕜') *
          logDeriv (F i) y id (df i i.property).existsUnique_hasDerivAt (uf i i.property) :=
  MeromorphicOn.logDeriv_finprod_zpow_eventuallyEq hd (fun i ↦ (h i).meromorphicOn)
    (fun i x _ ↦ h' i x)
