/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Topology.Algebra.InfiniteSum.UniformOn

/-!
# The Logarithmic derivative of an infinite product

We show that if we have an infinite product of functions `f` that is locally uniformly convergent,
then the logarithmic derivative of the product is the sum of the logarithmic derivatives of the
individual functions.

-/

public section

open Complex Filter

open scoped Topology

theorem logDeriv_tprod_eq_tsum {ι : Type*} {s : Set ℂ} (hs : IsOpen s) {x : ℂ} (hx : x ∈ s)
    {f : ι → ℂ → ℂ} (hf : ∀ i, f i x ≠ 0) (hd : ∀ i, DifferentiableOn ℂ (f i) s)
    (hm : Summable fun i ↦ logDeriv (f i) x id
      ((hd i x hx).differentiableAt (hs.mem_nhds hx)).existsUnique_hasDerivAt (hf i).isUnit)
    (htend : MultipliableLocallyUniformlyOn f s)
    {hnez : IsUnit (∏' i, f i x)} {hderiv : ∃! d, HasDerivAt (∏' i, f i ·) d x} :
    logDeriv (∏' i, f i ·) x id hderiv hnez = ∑' i, logDeriv (f i) x id
      ((hd i x hx).differentiableAt (hs.mem_nhds hx)).existsUnique_hasDerivAt (hf i).isUnit := by
  rw [Eq.comm, ← hm.hasSum_iff]
  have hdiff (b : Finset ι) : DifferentiableOn ℂ (fun y ↦ ∏ i ∈ b, f i y) s := by
    fun_prop
  let q (b : Finset ι) : {b : Finset ι //
      DifferentiableAt ℂ (fun y ↦ ∏ i ∈ b, f i y) x ∧ IsUnit (∏ i ∈ b, f i x)} :=
    ⟨b, (hdiff b x hx).differentiableAt (hs.mem_nhds hx),
      (Finset.prod_ne_zero_iff.mpr fun i _ ↦ hf i).isUnit⟩
  have hq : Tendsto q atTop (comap Subtype.val atTop) := tendsto_comap_iff.mpr tendsto_id
  refine ((logDeriv_tendsto hs hx htend.hasProdLocallyUniformlyOn (.of_forall hdiff)
    (hgd := hderiv) (hg := hnez)).comp hq).congr fun b ↦ ?_
  change logDeriv (fun y ↦ ∏ i ∈ b, f i y) x id _ _ = _
  refine (logDeriv_fun_prod (s := b) (f := f) (x := x) (fun i _ ↦ hf i)
    (fun i _ ↦ (hd i x hx).differentiableAt (hs.mem_nhds hx))).trans ?_
  exact Finset.sum_attach b (fun i ↦ logDeriv (f i) x id
    ((hd i x hx).differentiableAt (hs.mem_nhds hx)).existsUnique_hasDerivAt (hf i).isUnit)
