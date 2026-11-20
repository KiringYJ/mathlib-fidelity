/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.TangentCone.Basic
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Tangent cone points as limits of sequences

This file contains a few ways to describe `tangentConeAt`
as the set of limits of certain sequences.

In many cases, one can generalize results about the tangent cone
by using `mem_tangentConeAt_of_seq` and `exists_fun_of_mem_tangentConeAt`
instead of these lemmas.
-/

public section

open Filter
open scoped Topology

/-- In a vector space with first countable topology, a vector `y` belongs to `tangentConeAt 𝕜 s x`
if and only if there exist sequences `c n` and `d n` such that

- `d n` tends to zero as `n → ∞`;
- `x + d n ∈ s` for sufficiently large `n`;
- `c n • d n` tends to `y` as `n → ∞`.

See `mem_tangentConeAt_of_seq` and `exists_fun_of_mem_tangentConeAt`
for versions of two implications of this theorem that don't assume first countable topology. -/
theorem mem_tangentConeAt_iff_exists_seq {R E : Type*} [AddCommGroup E] [SMul R E]
    [TopologicalSpace E] [FirstCountableTopology E] {s : Set E} {x y : E} :
    y ∈ tangentConeAt R s x ↔ ∃ (c : ℕ → R) (d : ℕ → E), Tendsto d atTop (𝓝 0) ∧
      (∀ᶠ n in atTop, x + d n ∈ s) ∧ Tendsto (fun n ↦ c n • d n) atTop (𝓝 y) := by
  constructor
  · intro h
    simp only [tangentConeAt_def, Set.mem_ofPred, ← map₂_smul, ← map_prod_eq_map₂, ClusterPt,
      ← neBot_inf_comap_iff_map'] at h
    rcases @exists_seq_tendsto _ _ _ h with ⟨cd, hcd⟩
    simp only [tendsto_inf, tendsto_comap_iff, tendsto_prod_iff', tendsto_nhdsWithin_iff] at hcd
    exact ⟨Prod.fst ∘ cd, Prod.snd ∘ cd, hcd.2.2.1, hcd.2.2.2, hcd.1⟩
  · rintro ⟨c, d, hd₀, hds, hcd⟩
    exact mem_tangentConeAt_of_seq atTop c d hd₀ hds hcd

section
variable {𝕜 E : Type*} [NormedDivisionRing 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E] [ContinuousSMul 𝕜 E] {s : Set E} {x y : E} {r : 𝕜}

/-- Auxiliary lemma ensuring that, under the assumptions from an old definition of the tangent cone,
the sequence `d` tends to 0 at infinity. -/
theorem tangentConeAt.lim_zero {α : Type*} (l : Filter α) {c : α → 𝕜} {d : α → E} {y : E}
    (hc : Tendsto (fun n => ‖c n‖) l atTop) (hd : Tendsto (fun n => c n • d n) l (𝓝 y)) :
    Tendsto d l (𝓝 0) := by
  have hne := eventually_ne_of_tendsto_norm_atTop hc 0
  apply (tendsto_comap_val_iff hne).1
  let D := {n : α // c n ≠ 0}
  let u (n : D) : 𝕜ˣ := n.2.isUnit.unit
  have hu : Tendsto u (comap Subtype.val l)
      (comap (fun v : 𝕜ˣ ↦ (v : 𝕜)) (Bornology.cobounded 𝕜)) := by
    rw [tendsto_comap_iff]
    simpa only [Function.comp_def, u, IsUnit.unit_spec] using
      (tendsto_norm_atTop_iff_cobounded.mp hc).comp
        (tendsto_comap (f := (Subtype.val : D → α)))
  have h := (tendsto_inv₀_cobounded.comp hu).smul (hd.comp tendsto_comap)
  rw [zero_smul] at h
  refine h.congr fun n ↦ ?_
  simp only [Function.comp_def, u, Units.val_inv_eq_inv_val₀, IsUnit.unit_spec, inv_smul_smul₀]

theorem mem_tangentConeAt_of_pow_smul (hr₀ : r ≠ 0) (hr : ‖r‖ < 1)
    (hs : ∀ᶠ n : ℕ in atTop, x + r ^ n • y ∈ s) :
    y ∈ tangentConeAt 𝕜 s x := by
  refine mem_tangentConeAt_of_add_smul_mem
    (tendsto_nhdsWithin_iff.mpr ⟨tendsto_pow_atTop_nhds_zero_of_norm_lt_one hr, ?_⟩) hs
  simp [hr₀]

end

/-- In a normed space over a nontrivially normed field,
a point `y` belongs to the tangent cone of a set `s` at `x`
iff there exists a sequence of scalars `c n` and a sequence of points `d n` such that

- `‖c n‖ → ∞` as `n → ∞`;
- `x + d n ∈ s` for sufficiently large `n`;
- `c n • d n` tends to `y`.

Before https://github.com/leanprover-community/mathlib4/pull/34127,
the right-hand side of this equivalence was the definition of the tangent cone.

In most cases, `exists_fun_of_mem_tangentConeAt` and/or `mem_tangentConeAt_of_seq`
can be used to generalize a proof using this lemma to topological vector spaces.
-/
theorem mem_tangentConeAt_iff_exists_seq_norm_tendsto_atTop {𝕜 E : Type*}
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {s : Set E} {x y : E} :
    y ∈ tangentConeAt 𝕜 s x ↔
      ∃ (c : ℕ → 𝕜) (d : ℕ → E), Tendsto (‖c ·‖) atTop atTop ∧ (∀ᶠ n in atTop, x + d n ∈ s) ∧
        Tendsto (fun n ↦ c n • d n) atTop (𝓝 y) := by
  constructor
  · rcases eq_or_ne y 0 with rfl | hy₀
    · rw [zero_mem_tangentConeAt_iff]
      intro hx
      obtain ⟨c, hc⟩ := NormedField.exists_lt_norm 𝕜 1
      have (n : ℕ) : ∃ d : E, x + d ∈ s ∧ ‖d‖ < (1 / (2 * ‖c‖)) ^ n := by
        rw [Metric.mem_closure_iff] at hx
        rcases hx ((1 / (2 * ‖c‖)) ^ n) (by positivity) with ⟨v, hvs, hv⟩
        use v - x
        simp_all [dist_eq_norm_sub']
      choose d hds hd using this
      refine ⟨(c ^ ·), d, ?tendsto_c, .of_forall hds, ?tendsto_cd⟩
      case tendsto_c =>
        simp only [norm_pow]
        exact tendsto_pow_atTop_atTop_of_one_lt hc
      case tendsto_cd =>
        rw [atTop_basis.tendsto_iff (Metric.nhds_basis_ball_pow one_half_pos one_half_lt_one)]
        refine fun N _ ↦ ⟨N, trivial, fun n hn ↦ ?_⟩
        rw [Set.mem_Ici] at hn
        suffices ‖c‖ ^ n * ‖d n‖ < 1 / (2 ^ N) by simpa [norm_smul]
        rw [← lt_div_iff₀' (by positivity)]
        refine (hd n).trans_le ?_
        grw [hn]
        · simp only [div_eq_mul_inv₀, one_mul, inv_pow₀, mul_pow, mul_inv₀]
          exact le_rfl
        · norm_num1
    · rw [mem_tangentConeAt_iff_exists_seq]
      rintro ⟨c, d, hd₀, hds, hcd⟩
      refine ⟨c, d, ?_, hds, hcd⟩
      replace hd₀ := hd₀.norm
      have hd₀' : ∀ᶠ n in .atTop, d n ≠ 0 :=
        hcd.eventually_ne hy₀ |>.mono fun _ ↦ right_ne_zero_of_smul
      let D := {n : ℕ // d n ≠ 0}
      let l := comap (Subtype.val : D → ℕ) atTop
      have hco : Tendsto (Subtype.val : D → ℕ) l atTop := tendsto_comap
      have hp : Tendsto (fun n : D ↦ ‖d n‖) l (𝓝[>] (0 : ℝ)) := by
        apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
        · simpa only [Function.comp_def, norm_zero] using hd₀.comp hco
        · exact .of_forall fun n ↦ norm_pos_iff.mpr n.2
      have hi := hp.fun_inv_tendsto_nhdsGT_zero
        (h0 := fun n ↦ (norm_ne_zero_iff.mpr n.2).isUnit)
      have hprod : Tendsto (fun n : D ↦ ‖c n‖ * ‖d n‖) l (𝓝 ‖y‖) := by
        simpa only [Function.comp_def, norm_smul] using hcd.norm.comp hco
      apply (tendsto_comap_val_iff hd₀').1
      refine (hprod.pos_mul_atTop (norm_pos_iff.mpr hy₀) hi).congr fun n ↦ ?_
      simp only [mul_assoc, mul_inv_cancel₀, mul_one]
  · rintro ⟨c, d, hc, hds, hcd⟩
    exact mem_tangentConeAt_of_seq atTop c d (tangentConeAt.lim_zero atTop hc hcd) hds hcd
