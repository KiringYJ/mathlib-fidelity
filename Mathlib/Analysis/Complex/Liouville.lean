/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Normed.Module.Completion

/-!
# Liouville's theorem

In this file we prove Liouville's theorem: if `f : E → F` is complex differentiable on the whole
space and its range is bounded, then the function is a constant. Various versions of this theorem
are formalized in `Differentiable.apply_eq_apply_of_bounded`,
`Differentiable.exists_const_forall_eq_of_bounded`, and
`Differentiable.exists_eq_const_of_bounded`.

The proof is based on the Cauchy integral formula for the derivative of an analytic function, see
`Complex.deriv_eq_smul_circleIntegral`.
-/

public section

open TopologicalSpace Metric Set Filter Function Bornology

open scoped Topology Filter NNReal Real

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] {F : Type v} [NormedAddCommGroup F]
  [NormedSpace ℂ F]

local postfix:100 "̂" => UniformSpace.Completion

namespace Complex

/-- **Cauchy's estimate for derivatives**:  If `f` is complex differentiable on an open disc of
radius `R > 0`, is continuous on its closure, and its values on the boundary circle of this disc
are bounded from above by `C`, then the norm of its `n`-th derivative at the center is at most
`n.factorial * C / R ^ n`. -/
theorem norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le [CompleteSpace F] {c : ℂ} {R C : ℝ}
    {f : ℂ → F} (n : ℕ) (hR : 0 < R) (hf : DiffContOnCl ℂ f (ball c R))
    (hC : ∀ z ∈ sphere c R, ‖f z‖ ≤ C) :
    ‖iteratedDeriv n f c‖ ≤ n.factorial * C / R ^ n := by
  let integrand (z : sphere c |R|) : F :=
    Checked.div 1 ((z.val - c) ^ (n + 1))
      ((isUnit_sub_center_of_mem_sphere hR.ne'.isUnit z).pow _) • f z.val
  have hp (z : sphere c |R|) : ‖integrand z‖ ≤ C / R ^ (n + 1) := by
    have hz : (z : ℂ) ∈ sphere c R := by simpa only [abs_of_pos hR] using z.property
    have hnorm : ‖z.val - c‖ = R := mem_sphere_iff_norm.mp hz
    simp only [integrand, one_div₀, norm_smul, norm_inv, norm_pow, hnorm, inv_mul_eq_div₀]
    exact (div_le_div_iff_of_pos_right (pow_pos hR _)).mpr (hC z hz)
  have hconst : ‖(2 * π * I : ℂ)‖ = 2 * π := by simp
  have hconst₀ : IsUnit (2 * π * I : ℂ) :=
    (norm_ne_zero_iff.mp (hconst.symm ▸ Real.two_pi_pos.ne')).isUnit
  have hfac : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hCauchy : circleIntegralOn integrand c R =
      (2 * π * I / (n.factorial : ℂ)) • iteratedDeriv n f c :=
    hf.circleIntegral_one_div_sub_center_pow_smul hR n
  have hq : iteratedDeriv n f c =
      n.factorial • (2 * π * I : ℂ)⁻¹ • circleIntegralOn integrand c R := by
    have he : (n.factorial : ℂ) * (2 * π * I : ℂ)⁻¹ * (2 * π * I / (n.factorial : ℂ)) = 1 := by
      field_simp
    rw [hCauchy, ← Nat.cast_smul_eq_nsmul ℂ, ← mul_smul, ← mul_smul, he, one_smul]
  have hbound : ‖circleIntegralOn integrand c R‖ ≤ 2 * π * R * (C / R ^ (n + 1)) := by
    calc
      _ ≤ R * (C / R ^ (n + 1)) * |2 * π - 0| := by
        rw [circleIntegralOn_sphere]
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro θ _
        have hθ : ‖deriv (circleMap c R) θ‖ = R := by
          rw [deriv_circleMap, norm_mul, norm_I, mul_one, norm_circleMap_zero, abs_of_pos hR]
        rw [norm_smul, hθ]
        exact mul_le_mul_of_nonneg_left (hp _) hR.le
      _ = _ := by rw [sub_zero, abs_of_pos Real.two_pi_pos]; ac_rfl
  have hbound' : ‖(2 * π * I : ℂ)⁻¹ • circleIntegralOn integrand c R‖ ≤ R * (C / R ^ (n + 1)) := by
    have hnorm₀ : 0 < ‖(2 * π * I : ℂ)‖ := hconst.symm ▸ Real.two_pi_pos
    have hInv : ‖(2 * π * I : ℂ)⁻¹‖ = (2 * π)⁻¹ := calc
      _ = ‖(2 * π * I : ℂ)‖⁻¹ := norm_inv _
      _ = _ := inv_inj₀.mpr hconst
    rw [norm_smul, hInv, inv_mul_eq_div₀, div_le_iff₀ Real.two_pi_pos]
    exact hbound.trans_eq (by ring)
  calc
    ‖iteratedDeriv n f c‖ = n.factorial * ‖(2 * π * I : ℂ)⁻¹ • circleIntegralOn integrand c R‖ := by
      rw [hq, RCLike.norm_nsmul (K := ℂ), nsmul_eq_mul]
    _ ≤ n.factorial * (R * (C / (R ^ (n + 1)))) := by
      exact mul_le_mul_of_nonneg_left hbound' (by positivity)
    _ = n.factorial * C / R ^ n := by
      field_simp
      rw [pow_succ]
      ring

private theorem norm_deriv_le_aux [CompleteSpace F] {c : ℂ} {R C : ℝ} {f : ℂ → F} (hR : 0 < R)
    (hf : DiffContOnCl ℂ f (ball c R)) (hC : ∀ z ∈ sphere c R, ‖f z‖ ≤ C) :
    ‖deriv f c‖ ≤ C / R := by
  simpa only [iteratedDeriv_one, Nat.factorial_one, Nat.cast_one, one_mul, pow_one] using
    norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 1 hR hf hC

private theorem norm_deriv_le_via_embedding {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℂ G] [CompleteSpace G] (e : F →L[ℂ] G) (hnorm : ∀ x : F, ‖e x‖ = ‖x‖)
    {c : ℂ} {R C : ℝ} {f : ℂ → F} (hR : 0 < R)
    (hd : DiffContOnCl ℂ f (ball c R)) (hC : ∀ z ∈ sphere c R, ‖f z‖ ≤ C) :
    ‖deriv f c‖ ≤ C / R := by
  have hf : HasDerivAt f (deriv f c) c :=
    (hd.differentiableAt isOpen_ball (mem_ball_self hR)).hasDerivAt
  have he : HasFDerivAt (e : F → G) e (f c) := e.hasFDerivAt
  have hcomp : HasDerivAt (e ∘ f) (e (deriv f c)) c := he.comp_hasDerivAt c hf
  have hd' : DiffContOnCl ℂ (e ∘ f) (ball c R) := e.differentiable.comp_diffContOnCl hd
  have hC' (z : ℂ) (hz : z ∈ sphere c R) : ‖(e ∘ f) z‖ ≤ C :=
    (hnorm (f z)).trans_le (hC z hz)
  have heq : deriv (e ∘ f) c = e (deriv f c) := hcomp.deriv Topology.IsOpenEmbedding.id
  calc
    ‖deriv f c‖ = ‖e (deriv f c)‖ := (hnorm _).symm
    _ = ‖deriv (e ∘ f) c‖ := congrArg (fun w : G ↦ ‖w‖) heq.symm
    _ ≤ C / R := norm_deriv_le_aux hR hd' hC'

/-- **Cauchy's estimate for the first order derivative**: If `f` is complex differentiable on an
open disc of radius `R > 0`, is continuous on its closure, and its values on the boundary circle
of this disc are bounded from above by `C`, then the norm of its derivative at the center is at
most `C / R`. Note that this theorem does not require the completeness of the codomain of `f`. In
contrast, the completeness is needed for `norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`. -/
theorem norm_deriv_le_of_forall_mem_sphere_norm_le {c : ℂ} {R C : ℝ} {f : ℂ → F} (hR : 0 < R)
    (hd : DiffContOnCl ℂ f (ball c R)) (hC : ∀ z ∈ sphere c R, ‖f z‖ ≤ C) :
    ‖deriv f c‖ ≤ C / R :=
  norm_deriv_le_via_embedding (G := F̂) UniformSpace.Completion.toComplL
    UniformSpace.Completion.norm_coe hR hd hC

/-- An auxiliary lemma for Liouville's theorem `Differentiable.apply_eq_apply_of_bounded`. -/
theorem liouville_theorem_aux {f : ℂ → F} (hf : Differentiable ℂ f) (hb : IsBounded (range f))
    (z w : ℂ) : f z = f w := by
  suffices ∀ c, deriv f c = 0 from is_const_of_deriv_eq_zero hf this z w
  clear z w; intro c
  obtain ⟨C, C₀, hC⟩ : ∃ C > (0 : ℝ), ∀ z, ‖f z‖ ≤ C := by
    rcases isBounded_iff_forall_norm_le.1 hb with ⟨C, hC⟩
    exact
      ⟨max C 1, lt_max_iff.2 (Or.inr zero_lt_one), fun z =>
        (hC (f z) (mem_range_self _)).trans (le_max_left _ _)⟩
  refine norm_le_zero_iff.1 (le_of_forall_gt_imp_ge_of_dense fun ε ε₀ => ?_)
  calc
    ‖deriv f c‖ ≤ C / (C / ε) :=
      norm_deriv_le_of_forall_mem_sphere_norm_le (div_pos C₀ ε₀) hf.diffContOnCl fun z _ => hC z
    _ = ε := div_div_cancel₀

end Complex

namespace Differentiable

open Complex

/-- **Liouville's theorem**: a complex differentiable bounded function `f : E → F` is a constant. -/
theorem apply_eq_apply_of_bounded {f : E → F} (hf : Differentiable ℂ f) (hb : IsBounded (range f))
    (z w : E) : f z = f w := by
  set g : ℂ → F := f ∘ fun t : ℂ => t • (w - z) + z
  suffices g 0 = g 1 by simpa [g]
  apply liouville_theorem_aux
  exacts [hf.comp ((differentiable_id.smul_const (w - z)).add_const z),
    hb.subset (range_comp_subset_range _ _)]

/-- **Liouville's theorem**: a complex differentiable bounded function is a constant. -/
theorem exists_const_forall_eq_of_bounded {f : E → F} (hf : Differentiable ℂ f)
    (hb : IsBounded (range f)) : ∃ c, ∀ z, f z = c :=
  ⟨f 0, fun _ => hf.apply_eq_apply_of_bounded hb _ _⟩

/-- **Liouville's theorem**: a complex differentiable bounded function is a constant. -/
theorem exists_eq_const_of_bounded {f : E → F} (hf : Differentiable ℂ f)
    (hb : IsBounded (range f)) : ∃ c, f = const E c :=
  (hf.exists_const_forall_eq_of_bounded hb).imp fun _ => funext

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- A corollary of Liouville's theorem where the function tends to a finite value at infinity
(i.e., along `Filter.cocompact`, which in proper spaces coincides with `Bornology.cobounded`). -/
theorem eq_const_of_tendsto_cocompact [Nontrivial E] {f : E → F} (hf : Differentiable ℂ f) {c : F}
    (hb : Tendsto f (cocompact E) (𝓝 c)) : f = Function.const E c := by
  have h_bdd : Bornology.IsBounded (Set.range f) := by
    obtain ⟨s, hs, hs_bdd⟩ := Metric.exists_isBounded_image_of_tendsto hb
    obtain ⟨t, ht, hts⟩ := mem_cocompact.mp hs
    apply ht.image hf.continuous |>.isBounded.union hs_bdd |>.subset
    simpa [Set.image_union, Set.image_univ] using! Set.image_mono <| calc
      Set.univ = t ∪ tᶜ := t.union_compl_self.symm
      _        ⊆ t ∪ s  := by gcongr
  obtain ⟨c', hc'⟩ := hf.exists_eq_const_of_bounded h_bdd
  convert hc'
  exact tendsto_nhds_unique_of_forall hb tendsto_const_nhds (by simp [hc'])

/-- A corollary of Liouville's theorem where the function tends to a finite value at infinity
(i.e., along `Filter.cocompact`, which in proper spaces coincides with `Bornology.cobounded`). -/
theorem apply_eq_of_tendsto_cocompact [Nontrivial E] {f : E → F} (hf : Differentiable ℂ f) {c : F}
    (x : E) (hb : Tendsto f (cocompact E) (𝓝 c)) : f x = c :=
  congr($(hf.eq_const_of_tendsto_cocompact hb) x)

end Differentiable
