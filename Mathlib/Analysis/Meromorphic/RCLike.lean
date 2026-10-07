/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Analysis.RCLike.Basic

/-!
# Meromorphic Functions over the Real and Complex Numbers

This file gathers results on meromorphic functions specifict to the real and complex numbers.
-/

public section

open Set

variable
  {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/--
If `f` is meromorphic function on `ℝ` or `ℂ`, then there exists a point where a meromorphic function
`f` has finite order iff `f` has finite order at every point.
-/
theorem Meromorphic.exists_meromorphicOrderAt_ne_top_iff_forall {f : 𝕜 → E} (hf : Meromorphic f) :
    (∃ u, meromorphicOrderAt f u ≠ ⊤) ↔ (∀ u, meromorphicOrderAt f u ≠ ⊤) := by
  simpa using (meromorphicOn_univ.2 hf).exists_meromorphicOrderAt_ne_top_iff_forall isConnected_univ

/--
If `f` is meromorphic function on `ℝ` or `ℂ` and has infinite order at some point, then `f` vanishes
on a codiscrete set.
-/
theorem Meromorphic.eventuallyEq_zero_of_meromorphicOrderAt_eq_top {f : 𝕜 → E} (hf : Meromorphic f)
    {x : 𝕜} (h : meromorphicOrderAt f x = ⊤) :
    f =ᶠ[Filter.codiscrete 𝕜] 0 := by
  have h' (u : 𝕜) : meromorphicOrderAt f u = ⊤ := by
    by_contra hu
    exact hf.exists_meromorphicOrderAt_ne_top_iff_forall.1 ⟨u, hu⟩ x h
  filter_upwards [(meromorphicOn_univ.2 hf).analyticAt_mem_codiscreteWithin] with z hz
  rw [Pi.zero_apply]
  refine ((analyticOrderAt_eq_top hz).1 ?_).self_of_nhds
  simpa [hz.meromorphicOrderAt_eq] using h' z
