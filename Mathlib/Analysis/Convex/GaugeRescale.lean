/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Convex.Gauge
public import Mathlib.Analysis.Normed.Module.Convex
/-!
# "Gauge rescale" homeomorphism between convex sets

Given two convex von Neumann bounded neighbourhoods of the origin
in a real topological vector space,
we construct a homeomorphism `gaugeRescaleHomeomorph`
that sends the interior, the closure, and the frontier of one set
to the interior, the closure, and the frontier of the other set.
-/

@[expose] public section

open Metric Bornology Filter Set
open scoped NNReal Topology Pointwise

noncomputable section

section Module

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The domain of radial gauge rescaling. The origin is always fixed. Elsewhere both real
gauges must be finite and the target gauge must be nonzero. -/
def gaugeRescaleDomain (s t : Set E) : Set E :=
  {x | x ≠ 0 → {r : ℝ | 0 < r ∧ x ∈ r • s}.Nonempty ∧
    {r : ℝ | 0 < r ∧ x ∈ r • t}.Nonempty ∧ gauge t x ≠ 0}

@[simp] theorem zero_mem_gaugeRescaleDomain (s t : Set E) :
    (0 : E) ∈ gaugeRescaleDomain s t := fun h ↦ (h rfl).elim

/-- Rescale on a ray by the quotient of the source and target gauges away from the origin. -/
def gaugeRescale (s t : Set E) (x : gaugeRescaleDomain s t) : E := by
  classical
  exact if hx : x.val = 0 then 0 else
    Checked.div (gauge s x.val) (gauge t x.val) (x.property hx).2.2.isUnit • x.val

@[simp] theorem gaugeRescale_zero (s t : Set E) :
    gaugeRescale s t ⟨0, zero_mem_gaugeRescaleDomain s t⟩ = 0 := by simp [gaugeRescale]

theorem gaugeRescale_of_ne_zero {s t : Set E} (x : gaugeRescaleDomain s t) (hx : x.val ≠ 0) :
    gaugeRescale s t x = Checked.div (gauge s x.val) (gauge t x.val)
      (x.property hx).2.2.isUnit • x.val := dite_eq_right hx

private theorem gauge_dilations_smul {s : Set E} {x : E} {c : ℝ} (hc : 0 < c)
    (h : {r : ℝ | 0 < r ∧ x ∈ r • s}.Nonempty) :
    {r : ℝ | 0 < r ∧ c • x ∈ r • s}.Nonempty := by
  obtain ⟨r, hr, y, hy, he⟩ := h
  exact ⟨c * r, mul_pos hc hr, y, hy, (mul_smul c r y).trans (congrArg (c • ·) he)⟩

theorem smul_mem_gaugeRescaleDomain {s t : Set E} {x : E} (hx : x ∈ gaugeRescaleDomain s t)
    {c : ℝ} (hc : 0 ≤ c) : c • x ∈ gaugeRescaleDomain s t := by
  intro hn
  have hc' : c ≠ 0 := fun e ↦ hn (by rw [e, zero_smul])
  have hx' : x ≠ 0 := fun e ↦ hn (by rw [e, smul_zero])
  obtain ⟨hs, ht, hp⟩ := hx hx'
  refine ⟨gauge_dilations_smul (lt_of_le_of_ne hc hc'.symm) hs,
    gauge_dilations_smul (lt_of_le_of_ne hc hc'.symm) ht, ?_⟩
  rw [gauge_smul_of_nonneg hc, smul_eq_mul]
  exact mul_ne_zero hc' hp

theorem gaugeRescale_smul (s t : Set E) {c : ℝ} (hc : 0 ≤ c) (x : gaugeRescaleDomain s t) :
    gaugeRescale s t ⟨c • x.val, smul_mem_gaugeRescaleDomain x.property hc⟩ =
      c • gaugeRescale s t x := by
  rcases x with ⟨x, hd⟩
  rcases eq_or_ne c 0 with rfl | hc'
  · simp
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hcx := smul_ne_zero hc' hx
  rw [gaugeRescale_of_ne_zero _ hcx, gaugeRescale_of_ne_zero _ hx]
  simp only [gauge_smul_of_nonneg hc, smul_eq_mul, smul_smul]
  have hcancel : Checked.div (c * gauge s x) (c * gauge t x)
      (mul_ne_zero hc' (hd hx).2.2).isUnit =
        Checked.div (gauge s x) (gauge t x) (hd hx).2.2.isUnit := by
    apply div_eq_iff.mpr
    rw [mul_left_comm, div_mul_cancel₀]
  rw [hcancel, mul_comm]

private theorem gauge_zero_of_zero_mem {s : Set E} (hs : (0 : E) ∈ s) : gauge s 0 = 0 := by
  rw [gauge_def']
  simp only [smul_zero, hs, exists_prop, and_true]
  exact csInf_Ioi

/-- Whenever the source gauge at the input and the target gauge at its image are finite,
the image has exactly the prescribed gauge. The two origin conditions matter only when the
corresponding argument vanishes. -/
theorem gauge_gaugeRescale {s t : Set E} (x : gaugeRescaleDomain s t)
    (hs₀ : x.val = 0 → (0 : E) ∈ s) (ht₀ : gaugeRescale s t x = 0 → (0 : E) ∈ t) :
    gauge t (gaugeRescale s t x) = gauge s x.val := by
  rcases x with ⟨x, hd⟩
  rcases eq_or_ne x 0 with rfl | hx
  · rw [gaugeRescale_zero, gauge_zero_of_zero_mem (hs₀ rfl),
      gauge_zero_of_zero_mem (ht₀ (gaugeRescale_zero s t))]
  obtain ⟨hs, ht, hp⟩ := hd hx
  have hsn : 0 ≤ gauge s x := (isGLB_gauge hs).2 (fun _ hr ↦ hr.1.le)
  have htn : 0 ≤ gauge t x := (isGLB_gauge ht).2 (fun _ hr ↦ hr.1.le)
  by_cases hzero : gauge s x = 0
  · have him : gaugeRescale s t ⟨x, hd⟩ = 0 := by rw [gaugeRescale_of_ne_zero _ hx, hzero]; simp
    rw [him, gauge_zero_of_zero_mem (ht₀ him), hzero]
  · rw [gaugeRescale_of_ne_zero _ hx, gauge_smul_of_nonneg (div_nonneg hsn htn), smul_eq_mul,
      div_mul_cancel₀]

theorem gaugeRescale_self_apply {s : Set E} (x : gaugeRescaleDomain s s) :
    gaugeRescale s s x = x.val := by
  rcases x with ⟨x, hd⟩
  rcases eq_or_ne x 0 with rfl | hx
  · exact gaugeRescale_zero _ _
  · rw [gaugeRescale_of_ne_zero _ hx, div_self, one_smul]

theorem gaugeRescale_gaugeRescale {s t u : Set E} {x : E}
    (hst : x ∈ gaugeRescaleDomain s t) (hsu : x ∈ gaugeRescaleDomain s u)
    (him : gaugeRescale s t ⟨x, hst⟩ ∈ gaugeRescaleDomain t u) :
    gaugeRescale t u ⟨gaugeRescale s t ⟨x, hst⟩, him⟩ = gaugeRescale s u ⟨x, hsu⟩ := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  let c := Checked.div (gauge s x) (gauge t x) (hst hx).2.2.isUnit
  have hc : 0 ≤ c := div_nonneg (gauge_nonneg _) (gauge_nonneg _)
  have htu : x ∈ gaugeRescaleDomain t u := fun hn ↦ ⟨(hst hn).2.1, (hsu hn).2⟩
  calc
    _ = gaugeRescale t u ⟨c • x, smul_mem_gaugeRescaleDomain htu hc⟩ :=
      congrArg (gaugeRescale t u) (Subtype.ext (gaugeRescale_of_ne_zero _ hx))
    _ = c • gaugeRescale t u ⟨x, htu⟩ := gaugeRescale_smul t u hc ⟨x, htu⟩
    _ = _ := by
      rw [gaugeRescale_of_ne_zero _ hx, gaugeRescale_of_ne_zero _ hx, smul_smul]
      congr 1
      symm
      apply div_eq_iff.mpr
      rw [mul_assoc, div_mul_cancel₀]
      exact (div_mul_cancel₀ _).symm

variable [TopologicalSpace E]

section
variable [T1Space E]

/-- Absorbent sets have finite gauges everywhere. Boundedness of the target makes its gauge
positive at every nonzero point, so the whole space is admissible. -/
theorem mem_gaugeRescaleDomain {s t : Set E} (hsa : Absorbent ℝ s) (hta : Absorbent ℝ t)
    (htb : IsVonNBounded ℝ t) (x : E) : x ∈ gaugeRescaleDomain s t :=
  fun hx ↦ ⟨hsa.gauge_set_nonempty, hta.gauge_set_nonempty, ((gauge_pos hta htb).mpr hx).ne'⟩

theorem gaugeRescale_self {s : Set E} (hsa : Absorbent ℝ s) (hsb : IsVonNBounded ℝ s) :
    (fun x ↦ gaugeRescale s s ⟨x, mem_gaugeRescaleDomain hsa hsa hsb x⟩) = id :=
  funext fun _ ↦ gaugeRescale_self_apply _

/-- Radial gauge rescaling as an equivalence of the ambient space. -/
def gaugeRescaleEquiv (s t : Set E) (hsa : Absorbent ℝ s) (hsb : IsVonNBounded ℝ s)
    (hta : Absorbent ℝ t) (htb : IsVonNBounded ℝ t) : E ≃ E where
  toFun x := gaugeRescale s t ⟨x, mem_gaugeRescaleDomain hsa hta htb x⟩
  invFun x := gaugeRescale t s ⟨x, mem_gaugeRescaleDomain hta hsa hsb x⟩
  left_inv x := (gaugeRescale_gaugeRescale _ (mem_gaugeRescaleDomain hsa hsa hsb x) _).trans
    (gaugeRescale_self_apply _)
  right_inv x := (gaugeRescale_gaugeRescale _ (mem_gaugeRescaleDomain hta hta htb x) _).trans
    (gaugeRescale_self_apply _)

end

variable [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] {s t : Set E}

theorem mapsTo_gaugeRescale_interior (h₀ : t ∈ 𝓝 0) (hc : Convex ℝ t) :
    MapsTo (gaugeRescale s t) (Subtype.val ⁻¹' interior s) (interior t) := by
  intro x hx
  apply (gauge_lt_one_iff_mem_interior hc h₀).mp
  rw [gauge_gaugeRescale x (fun he ↦ he ▸ interior_subset hx) (fun _ ↦ mem_of_mem_nhds h₀)]
  exact interior_subset_gauge_lt_one _ hx

theorem mapsTo_gaugeRescale_closure {s t : Set E} (hsc : Convex ℝ s) (hs₀ : s ∈ 𝓝 0)
    (htc : Convex ℝ t) (ht₀ : 0 ∈ t) (hta : Absorbent ℝ t) :
    MapsTo (gaugeRescale s t) (Subtype.val ⁻¹' closure s) (closure t) := by
  intro x hx
  apply mem_closure_of_gauge_le_one htc ht₀ hta
  rw [gauge_gaugeRescale x (fun _ ↦ mem_of_mem_nhds hs₀) (fun _ ↦ ht₀)]
  exact (gauge_le_one_iff_mem_closure hsc hs₀).mpr hx

variable [T1Space E]

theorem continuous_gaugeRescale {s t : Set E} (hs : Convex ℝ s) (hs₀ : s ∈ 𝓝 0)
    (ht : Convex ℝ t) (ht₀ : t ∈ 𝓝 0) (htb : IsVonNBounded ℝ t) :
    Continuous (fun x ↦ gaugeRescale s t
      ⟨x, mem_gaugeRescaleDomain (absorbent_nhds_zero hs₀) (absorbent_nhds_zero ht₀) htb x⟩) := by
  let H := mem_gaugeRescaleDomain (absorbent_nhds_zero hs₀) (absorbent_nhds_zero ht₀) htb
  let F (x : E) := gaugeRescale s t ⟨x, H x⟩
  change Continuous F
  refine continuous_iff_continuousAt.mpr fun x ↦ ?_
  rcases eq_or_ne x 0 with rfl | hx
  · change Tendsto F (𝓝 0) (𝓝 (gaugeRescale s t ⟨0, H 0⟩))
    rw [gaugeRescale_zero]
    nth_rewrite 2 [← comap_gauge_nhds_zero htb ht₀]
    rw [tendsto_comap_iff]
    have he : gauge t ∘ F = gauge s := funext fun y ↦
      gauge_gaugeRescale ⟨y, H y⟩ (fun _ ↦ mem_of_mem_nhds hs₀) (fun _ ↦ mem_of_mem_nhds ht₀)
    rw [he]
    exact tendsto_gauge_nhds_zero hs₀
  · let U := {z : E | z ≠ 0}
    have hxU : x ∈ U := hx
    apply ContinuousWithinAt.continuousAt _ (isOpen_ne.mem_nhds hx)
    apply (continuousWithinAt_iff_continuousAt_domRestrict F hxU).mpr
    have h₁ : Continuous fun z : U ↦ gauge s z.val :=
      (continuous_gauge hs hs₀).comp continuous_subtype_val
    have h₂ : Continuous fun z : U ↦ gauge t z.val :=
      (continuous_gauge ht ht₀).comp continuous_subtype_val
    have he : U.domRestrict F = fun z : U ↦
        Checked.div (gauge s z.val) (gauge t z.val) ((H z) z.property).2.2.isUnit • z.val :=
      funext fun z : U ↦ gaugeRescale_of_ne_zero ⟨z.val, H z.val⟩ z.property
    rw [he]
    exact ((h₁.div₀ (h₀ := fun z : U ↦ ((H z.val) z.property).2.2.isUnit) h₂).smul
      continuous_subtype_val).continuousAt

/-- `gaugeRescale` bundled as a `Homeomorph`. -/
def gaugeRescaleHomeomorph (s t : Set E)
    (hsc : Convex ℝ s) (hs₀ : s ∈ 𝓝 0) (hsb : IsVonNBounded ℝ s)
    (htc : Convex ℝ t) (ht₀ : t ∈ 𝓝 0) (htb : IsVonNBounded ℝ t) : E ≃ₜ E where
  toEquiv := gaugeRescaleEquiv s t (absorbent_nhds_zero hs₀) hsb (absorbent_nhds_zero ht₀) htb
  continuous_toFun := continuous_gaugeRescale hsc hs₀ htc ht₀ htb
  continuous_invFun := continuous_gaugeRescale htc ht₀ hsc hs₀ hsb

theorem image_gaugeRescaleHomeomorph_interior {s t : Set E}
    (hsc : Convex ℝ s) (hs₀ : s ∈ 𝓝 0) (hsb : IsVonNBounded ℝ s)
    (htc : Convex ℝ t) (ht₀ : t ∈ 𝓝 0) (htb : IsVonNBounded ℝ t) :
    gaugeRescaleHomeomorph s t hsc hs₀ hsb htc ht₀ htb '' interior s = interior t := by
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact mapsTo_gaugeRescale_interior ht₀ htc (x := ⟨x, _⟩) hx
  · rw [← Homeomorph.preimage_symm, ← image_subset_iff]
    rintro _ ⟨x, hx, rfl⟩
    exact mapsTo_gaugeRescale_interior hs₀ hsc (x := ⟨x, _⟩) hx

theorem image_gaugeRescaleHomeomorph_closure {s t : Set E}
    (hsc : Convex ℝ s) (hs₀ : s ∈ 𝓝 0) (hsb : IsVonNBounded ℝ s)
    (htc : Convex ℝ t) (ht₀ : t ∈ 𝓝 0) (htb : IsVonNBounded ℝ t) :
    gaugeRescaleHomeomorph s t hsc hs₀ hsb htc ht₀ htb '' closure s = closure t := by
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact mapsTo_gaugeRescale_closure hsc hs₀ htc (mem_of_mem_nhds ht₀)
      (absorbent_nhds_zero ht₀) (x := ⟨x, _⟩) hx
  · rw [← Homeomorph.preimage_symm, ← image_subset_iff]
    rintro _ ⟨x, hx, rfl⟩
    exact mapsTo_gaugeRescale_closure htc ht₀ hsc (mem_of_mem_nhds hs₀)
      (absorbent_nhds_zero hs₀) (x := ⟨x, _⟩) hx

/-- Given two convex bounded sets in a topological vector space with nonempty interiors,
there exists a homeomorphism of the ambient space
that sends the interior, the closure, and the frontier of one set
to the interior, the closure, and the frontier of the other set.

In particular, if both `s` and `t` are open set or both `s` and `t` are closed sets,
then `e` maps `s` to `t`. -/
theorem exists_homeomorph_image_eq {s t : Set E}
    (hsc : Convex ℝ s) (hsne : (interior s).Nonempty) (hsb : IsVonNBounded ℝ s)
    (hst : Convex ℝ t) (htne : (interior t).Nonempty) (htb : IsVonNBounded ℝ t) :
    ∃ e : E ≃ₜ E, e '' interior s = interior t ∧ e '' closure s = closure t ∧
      e '' frontier s = frontier t := by
  rsuffices ⟨e, h₁, h₂⟩ : ∃ e : E ≃ₜ E, e '' interior s = interior t ∧ e '' closure s = closure t
  · refine ⟨e, h₁, h₂, ?_⟩
    simp_rw [← closure_sdiff_interior, image_sdiff e.injective, h₁, h₂]
  rcases hsne with ⟨x, hx⟩
  rcases htne with ⟨y, hy⟩
  set h : E ≃ₜ E := by
    apply gaugeRescaleHomeomorph (-x +ᵥ s) (-y +ᵥ t) <;>
      simp [← mem_interior_iff_mem_nhds, interior_vadd, mem_vadd_set_iff_neg_vadd_mem, *]
  refine ⟨.trans (.addLeft (-x)) <| h.trans <| .addLeft y, ?_, ?_⟩
  · calc
      (fun a ↦ y + h (-x + a)) '' interior s = y +ᵥ h '' interior (-x +ᵥ s) := by
        simp_rw [interior_vadd, ← image_vadd, image_image, vadd_eq_add]
      _ = _ := by rw [image_gaugeRescaleHomeomorph_interior, interior_vadd, vadd_neg_vadd]
  · calc
      (fun a ↦ y + h (-x + a)) '' closure s = y +ᵥ h '' closure (-x +ᵥ s) := by
        simp_rw [closure_vadd, ← image_vadd, image_image, vadd_eq_add]
      _ = _ := by rw [image_gaugeRescaleHomeomorph_closure, closure_vadd, vadd_neg_vadd]

end Module

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- If `s` is a convex bounded set with a nonempty interior in a real normed space,
then there is a homeomorphism of the ambient space to itself
that sends the interior of `s` to the unit open ball
and the closure of `s` to the unit closed ball. -/
theorem exists_homeomorph_image_interior_closure_frontier_eq_unitBall {s : Set E}
    (hc : Convex ℝ s) (hne : (interior s).Nonempty) (hb : IsBounded s) :
    ∃ h : E ≃ₜ E, h '' interior s = ball 0 1 ∧ h '' closure s = closedBall 0 1 ∧
      h '' frontier s = sphere 0 1 := by
  simpa [isOpen_ball.interior_eq, closure_ball, frontier_ball]
    using exists_homeomorph_image_eq hc hne (NormedSpace.isVonNBounded_of_isBounded _ hb)
    (convex_ball 0 1) (by simp [isOpen_ball.interior_eq]) (NormedSpace.isVonNBounded_ball _ _ _)
