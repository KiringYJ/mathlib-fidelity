/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Topology.Algebra.Group.Order

/-!
# Conversion lemmas

The main procedure of the `compute_asymptotics` tactic is able to compute limits of functions at
`atTop` filter. This file contains lemmas we use to reduce other asymptotic goals to
the case `Tendsto f atTop l`.

## Main theorems

This file contains the following lemmas:
* `tendsto_nhdsGT_of_tendsto_atTop` for `Tendsto f (𝓝[>] c) l`
* `tendsto_nhdsLT_of_tendsto_atTop` for `Tendsto f (𝓝[<] c) l`
* `tendsto_nhdsNE_of_tendsto_atTop` for `Tendsto f (𝓝[≠] c) l`
* `isBigO_of_div_tendsto_atTop` and `isBigO_of_div_tendsto_atBot` for `f =O[l] g`

We also use lemmas from other files:
* `tendsto_comp_neg_atTop_iff` for `Tendsto f atBot l`
* `IsLittleO.of_tendsto_div_atBot` and `IsLittleO.of_tendsto_div_atTop` for `f =o[l] g`
* `isEquivalent_of_tendsto_one` for `f ∼ g`
-/

public section

open Filter Asymptotics

open scoped Topology

namespace Tactic.ComputeAsymptotics

variable {α 𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜]
  [OrderTopology 𝕜] {l : Filter α} (f : 𝕜 → α) (c : 𝕜)

/-! The inverse `x⁻¹` exists on the invertible elements, so the hypotheses below are stated on
`{x : 𝕜 | IsUnit x}` along `comap Subtype.val atTop`, as
`tendsto_nhdsGT_zero_of_comp_inv_tendsto_atTop` is. -/

theorem tendsto_nhdsGT_of_tendsto_atTop
    (h : Tendsto (fun x : {x : 𝕜 | IsUnit x} ↦ f (c + Checked.inv (x : 𝕜) x.2))
      (comap Subtype.val atTop) l) :
    Tendsto f (𝓝[>] c) l := by
  have h₀ := tendsto_nhdsGT_zero_of_comp_inv_tendsto_atTop (f := fun y ↦ f (c + y)) h
  rw [← add_zero c, ← Filter.map_add_left_nhdsGT, tendsto_map'_iff]
  exact h₀

theorem tendsto_nhdsLT_of_tendsto_atTop
    (h : Tendsto (fun x : {x : 𝕜 | IsUnit x} ↦ f (c - Checked.inv (x : 𝕜) x.2))
      (comap Subtype.val atTop) l) :
    Tendsto f (𝓝[<] c) l := by
  have h₀ := tendsto_nhdsGT_zero_of_comp_inv_tendsto_atTop (f := fun y ↦ f (c - y)) h
  rw [← sub_zero c, ← Filter.map_subLeft_nhdsGT, tendsto_map'_iff]
  exact h₀

theorem tendsto_nhdsNE_of_tendsto_atTop
    (h_neg : Tendsto (fun x : {x : 𝕜 | IsUnit x} ↦ f (c - Checked.inv (x : 𝕜) x.2))
      (comap Subtype.val atTop) l)
    (h_pos : Tendsto (fun x : {x : 𝕜 | IsUnit x} ↦ f (c + Checked.inv (x : 𝕜) x.2))
      (comap Subtype.val atTop) l) :
    Tendsto f (𝓝[≠] c) l := by
  simpa [Tendsto, ← nhdsLT_sup_nhdsGT] using
    ⟨tendsto_nhdsLT_of_tendsto_atTop _ _ h_neg, tendsto_nhdsGT_of_tendsto_atTop _ _ h_pos⟩

theorem tendsto_nhdsNE_of_tendsto_atTop_nhds_of_eq [TopologicalSpace α] {a b : α}
    (h_neg : Tendsto (fun x : {x : 𝕜 | IsUnit x} ↦ f (c - Checked.inv (x : 𝕜) x.2))
      (comap Subtype.val atTop) (𝓝 a))
    (h_pos : Tendsto (fun x : {x : 𝕜 | IsUnit x} ↦ f (c + Checked.inv (x : 𝕜) x.2))
      (comap Subtype.val atTop) (𝓝 b))
    (h_eq : a = b) :
    Tendsto f (𝓝[≠] c) (𝓝 a) := by
  apply tendsto_nhdsNE_of_tendsto_atTop _ _ h_neg
  convert! h_pos

theorem isBigOWith_of_tendsto_top {C : ℝ} {f g : ℝ → ℝ} {l : Filter ℝ} {hf : ∀ x, IsUnit (f x)}
    (h : Tendsto (fun x ↦ Checked.div (g x) (f x) (hf x)) l atTop) (hC : 0 < C) :
    IsBigOWith C l f g :=
  Asymptotics.IsLittleO.forall_isBigOWith (.of_tendsto_div_atTop h) hC

theorem isBigOWith_of_tendsto_bot {C : ℝ} {f g : ℝ → ℝ} {l : Filter ℝ} {hf : ∀ x, IsUnit (f x)}
    (h : Tendsto (fun x ↦ Checked.div (g x) (f x) (hf x)) l atBot) (hC : 0 < C) :
    IsBigOWith C l f g :=
  Asymptotics.IsLittleO.forall_isBigOWith (.of_tendsto_div_atBot h) hC

theorem isBigO_of_div_tendsto_atTop {f g : ℝ → ℝ} {l : Filter ℝ} {hf : ∀ x, IsUnit (f x)}
    (h : Tendsto (fun x ↦ Checked.div (g x) (f x) (hf x)) l atTop) :
    f =O[l] g :=
  Asymptotics.IsLittleO.isBigO (.of_tendsto_div_atTop h)

theorem isBigO_of_div_tendsto_atBot {f g : ℝ → ℝ} {l : Filter ℝ} {hf : ∀ x, IsUnit (f x)}
    (h : Tendsto (fun x ↦ Checked.div (g x) (f x) (hf x)) l atBot) :
    f =O[l] g :=
  Asymptotics.IsLittleO.isBigO (.of_tendsto_div_atBot h)

end Tactic.ComputeAsymptotics
