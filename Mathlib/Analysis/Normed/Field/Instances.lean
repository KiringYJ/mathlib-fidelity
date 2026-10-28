/-
Copyright (c) 2025 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll, Patrick Massot, Anatole Dedecker
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Order.Filter.IsBounded
public import Mathlib.Topology.Algebra.UniformField

/-!
# A normed field is a completable topological field
-/

public section

open SeminormedAddGroup IsUniformAddGroup Filter

variable {F : Type*} [NormedField F]

instance NormedField.instCompletableTopField : CompletableTopField F where
  nice f hc hn := by
    obtain ⟨δ, δ_pos, hδ⟩ := (disjoint_nhds_zero ..).mp <| disjoint_iff.mpr hn
    have h₀ : {x : F | IsUnit x} ∈ f :=
      hδ.mono fun y hy ↦ (norm_pos_iff.mp (δ_pos.trans_le hy)).isUnit
    have g_bdd : (comap (Subtype.val : {x : F | IsUnit x} → F) f).IsBoundedUnder (· ≤ ·)
        (fun x ↦ ‖Checked.inv (x : F) x.2‖) :=
      ⟨δ⁻¹, eventually_comap.mpr <| hδ.mono fun y hy x hx ↦ by
        subst hx
        change ‖Checked.inv (x : F) x.2‖ ≤ δ⁻¹
        rw [norm_inv]
        exact (inv_le_inv₀ (δ_pos.trans_le hy) δ_pos).mpr hy⟩
    have hg : Tendsto (fun p : {x : F | IsUnit x} × {x : F | IsUnit x} ↦ (p.2 : F) - p.1)
        (comap Subtype.val f ×ˢ comap Subtype.val f) (𝓝 0) :=
      ((cauchy_iff_tendsto_swapped f).mp hc).2.comp (tendsto_comap.prodMap tendsto_comap)
    rw [cauchy_map_iff_tendsto]
    refine ⟨hc.1.comap_of_range_mem (by rwa [Subtype.range_coe]), ?_⟩
    refine Tendsto.congr (fun p ↦ inv_sub_inv'.symm) ?_
    refine .zero_mul_isBoundedUnder_le ?_ (tendsto_snd.isBoundedUnder_comp g_bdd)
    exact isBoundedUnder_le_mul_tendsto_zero (tendsto_fst.isBoundedUnder_comp g_bdd) hg
