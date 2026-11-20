/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Slope of a differentiable function

Given a function `f : 𝕜 → E` from a nontrivially normed field to a normed space over this field,
`dslope f a b` is defined as `slope f a b = (b - a)⁻¹ • (f b - f a)` for `a ≠ b` and as `deriv f a`
for `a = b`.

In this file we define `dslope` and prove some basic lemmas about its continuity and
differentiability.
-/

@[expose] public section

open scoped Topology Filter

open Function Set Filter

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

open scoped Classical in
/-- `dslope f a b` is defined as `slope f a b = (b - a)⁻¹ • (f b - f a)` for `a ≠ b` and
`deriv f a` for `a = b`. -/
noncomputable def dslope (f : 𝕜 → E) (a b : 𝕜) : E :=
  if h : b = a then deriv f a else slope f a b (Ne.symm h)

@[simp]
theorem dslope_same (f : 𝕜 → E) (a : 𝕜) : dslope f a a = deriv f a := by
  simp [dslope]

variable {f : 𝕜 → E} {a b : 𝕜} {s : Set 𝕜}

theorem dslope_of_ne (f : 𝕜 → E) (h : b ≠ a) : dslope f a b = slope f a b h.symm := by
  simp [dslope, h]

theorem ContinuousLinearMap.dslope_comp {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (f : E →L[𝕜] F) (g : 𝕜 → E) (a b : 𝕜) (H : a = b → DifferentiableAt 𝕜 g a) :
    dslope (f ∘ g) a b = f (dslope g a b) := by
  rcases eq_or_ne b a with (rfl | hne)
  · simp only [dslope_same]
    exact (f.hasFDerivAt.comp_hasDerivAt b (H rfl).hasDerivAt).deriv
  · simpa only [dslope_of_ne _ hne] using! f.toLinearMap.slope_comp g a b (hab := hne.symm)

/-- On its genuine punctured domain, the derivative extension agrees with the slope. -/
theorem dslope_eq_slope (f : 𝕜 → E) (a : 𝕜) :
    (fun y : ↥({a}ᶜ : Set 𝕜) ↦ dslope f a y) =
      fun y : ↥({a}ᶜ : Set 𝕜) ↦ slope f a y (Ne.symm y.2) :=
  funext fun y : ↥({a}ᶜ : Set 𝕜) ↦ dslope_of_ne f y.2

@[simp]
theorem sub_smul_dslope (f : 𝕜 → E) (a b : 𝕜) : (b - a) • dslope f a b = f b - f a := by
  rcases eq_or_ne b a with (rfl | hne) <;> simp [dslope_of_ne, *]

theorem dslope_sub_smul_of_ne (f : 𝕜 → E) (h : b ≠ a) :
    dslope (fun x => (x - a) • f x) a b = f b := by
  rw [dslope_of_ne _ h, slope_sub_smul _ h.symm]

theorem eqOn_dslope_sub_smul (f : 𝕜 → E) (a : 𝕜) :
    EqOn (dslope (fun x => (x - a) • f x) a) f {a}ᶜ := fun _ => dslope_sub_smul_of_ne f

theorem dslope_sub_smul [DecidableEq 𝕜] (f : 𝕜 → E) (a : 𝕜) :
    dslope (fun x => (x - a) • f x) a = update f a (deriv (fun x => (x - a) • f x) a) :=
  eq_update_iff.2 ⟨dslope_same _ _, eqOn_dslope_sub_smul f a⟩

@[simp]
theorem continuousAt_dslope_same : ContinuousAt (dslope f a) a ↔ DifferentiableAt 𝕜 f a := by
  have hmap : map ((↑) : ↥({a}ᶜ : Set 𝕜) → 𝕜) (comap (↑) (𝓝 a)) = 𝓝[≠] a := by
    rw [map_comap, Subtype.range_coe]
    rfl
  rw [← continuousWithinAt_compl_self, ContinuousWithinAt, dslope_same,
    ← hasDerivAt_deriv_iff, hasDerivAt_iff_tendsto_slope, ← hmap, tendsto_map'_iff]
  change Tendsto (fun y : ↥({a}ᶜ : Set 𝕜) ↦ dslope f a y) _ _ ↔ _
  rw [dslope_eq_slope]

theorem ContinuousWithinAt.of_dslope (h : ContinuousWithinAt (dslope f a) s b) :
    ContinuousWithinAt f s b := by
  have : ContinuousWithinAt (fun x => (x - a) • dslope f a x + f a) s b :=
    ((continuousWithinAt_id.sub continuousWithinAt_const).smul h).add continuousWithinAt_const
  simpa only [sub_smul_dslope, sub_add_cancel] using this

theorem ContinuousAt.of_dslope (h : ContinuousAt (dslope f a) b) : ContinuousAt f b :=
  (continuousWithinAt_univ _ _).1 h.continuousWithinAt.of_dslope

theorem ContinuousOn.of_dslope (h : ContinuousOn (dslope f a) s) : ContinuousOn f s := fun x hx =>
  (h x hx).of_dslope

theorem continuousWithinAt_dslope_of_ne (h : b ≠ a) :
    ContinuousWithinAt (dslope f a) s b ↔ ContinuousWithinAt f s b := by
  refine ⟨ContinuousWithinAt.of_dslope, fun hc => ?_⟩
  let U := {y : 𝕜 | IsUnit (y - a)}
  let z : U := ⟨b, (sub_ne_zero.mpr h).isUnit⟩
  have hopen : IsOpen U := Units.isOpen.preimage (continuous_id.sub continuous_const)
  have hinv : Continuous (fun y : U ↦ Checked.inv ((y : 𝕜) - a) y.2) :=
    (continuous_subtype_val.sub continuous_const).fun_inv₀ (h0 := fun y : U ↦ y.2)
  have hEq : (fun y : U ↦ Checked.inv ((y : 𝕜) - a) y.2 • (f y - f a)) =
      fun y : U ↦ dslope f a y := by
    funext y
    rw [dslope_of_ne f (fun hy ↦ y.2.ne_zero (sub_eq_zero.mpr hy)), slope_def_module]
  have hlocal : ContinuousWithinAt (fun y : U ↦ dslope f a y) (Subtype.val ⁻¹' s) z := by
    rw [← hEq]
    exact hinv.continuousWithinAt.smul
      ((hc.comp continuous_subtype_val.continuousWithinAt (fun _ hy ↦ hy)).sub
        continuousWithinAt_const)
  change Tendsto (dslope f a) (𝓝[s] b) (𝓝 (dslope f a b))
  rw [← hopen.isOpenEmbedding_subtypeVal.map_nhdsWithin_preimage_eq s z, tendsto_map'_iff]
  exact hlocal

theorem continuousAt_dslope_of_ne (h : b ≠ a) : ContinuousAt (dslope f a) b ↔ ContinuousAt f b := by
  simp only [← continuousWithinAt_univ, continuousWithinAt_dslope_of_ne h]

theorem continuousOn_dslope (h : s ∈ 𝓝 a) :
    ContinuousOn (dslope f a) s ↔ ContinuousOn f s ∧ DifferentiableAt 𝕜 f a := by
  refine ⟨fun hc => ⟨hc.of_dslope, continuousAt_dslope_same.1 <| hc.continuousAt h⟩, ?_⟩
  rintro ⟨hc, hd⟩ x hx
  rcases eq_or_ne x a with (rfl | hne)
  exacts [(continuousAt_dslope_same.2 hd).continuousWithinAt,
    (continuousWithinAt_dslope_of_ne hne).2 (hc x hx)]

theorem DifferentiableWithinAt.of_dslope (h : DifferentiableWithinAt 𝕜 (dslope f a) s b) :
    DifferentiableWithinAt 𝕜 f s b := by
  have heq : (fun y ↦ (y - a) • dslope f a y + f a) = f :=
    funext fun y ↦ by rw [sub_smul_dslope, sub_add_cancel]
  rw [← heq]
  exact ((differentiableWithinAt_id.sub_const a).fun_smul h).add_const (f a)

theorem DifferentiableAt.of_dslope (h : DifferentiableAt 𝕜 (dslope f a) b) :
    DifferentiableAt 𝕜 f b :=
  differentiableWithinAt_univ.1 h.differentiableWithinAt.of_dslope

theorem DifferentiableOn.of_dslope (h : DifferentiableOn 𝕜 (dslope f a) s) :
    DifferentiableOn 𝕜 f s := fun x hx => (h x hx).of_dslope

theorem differentiableWithinAt_dslope_of_ne (h : b ≠ a) :
    DifferentiableWithinAt 𝕜 (dslope f a) s b ↔ DifferentiableWithinAt 𝕜 f s b := by
  refine ⟨DifferentiableWithinAt.of_dslope, fun hd => ?_⟩
  let U := {y : 𝕜 | IsUnit (y - a)}
  let z : U := ⟨b, (sub_ne_zero.mpr h).isUnit⟩
  have hopen : IsOpen U := Units.isOpen.preimage (continuous_id.sub continuous_const)
  have hi := ((differentiableWithinAt_id (𝕜 := 𝕜) (s := s) (x := b)).sub_const a)
    |>.hasFDerivWithinAt.inv z.2
  have hf : HasFDerivWithinAt (fun y : U ↦ f y) (fderivWithin 𝕜 f s b)
      (Subtype.val ⁻¹' s) z (fun y ↦ (y : 𝕜)) := by
    exact HasFDerivAtFilter.comp_tendsto hd.hasFDerivWithinAt Subtype.val
      ((continuous_subtype_val.continuousWithinAt.tendsto_nhdsWithin (fun _ hy ↦ hy)).prodMap
        (tendsto_pure_pure ..))
  let B : 𝕜 →L[𝕜] E →L[𝕜] E := ContinuousLinearMap.lsmul 𝕜 𝕜
  have hlocal := (B.hasFDerivWithinAt_of_bilinear hi (hf.sub_const (f a))
    continuous_subtype_val.continuousWithinAt).differentiableWithinAt
  have hEq : (fun y : U ↦ Checked.inv ((y : 𝕜) - a) y.2 • (f y - f a)) =
      fun y : U ↦ dslope f a y := by
    funext y
    rw [dslope_of_ne f (fun hy ↦ y.2.ne_zero (sub_eq_zero.mpr hy)), slope_def_module]
  change DifferentiableWithinAt 𝕜
    (fun y : U ↦ Checked.inv ((y : 𝕜) - a) y.2 • (f y - f a))
    (Subtype.val ⁻¹' s) z (fun y ↦ (y : 𝕜)) at hlocal
  rw [hEq] at hlocal
  obtain ⟨g', hg'⟩ := hlocal
  refine ⟨g', ?_⟩
  rw [hasFDerivWithinAt_iff_isLittleOTVS,
    ← hopen.isOpenEmbedding_subtypeVal.map_nhdsWithin_preimage_eq s z, Asymptotics.isLittleOTVS_map]
  exact hg'.isLittleOTVS

theorem differentiableOn_dslope_of_notMem (h : a ∉ s) :
    DifferentiableOn 𝕜 (dslope f a) s ↔ DifferentiableOn 𝕜 f s :=
  forall_congr' fun _ =>
    forall_congr' fun hx => differentiableWithinAt_dslope_of_ne <| ne_of_mem_of_not_mem hx h

theorem differentiableAt_dslope_of_ne (h : b ≠ a) :
    DifferentiableAt 𝕜 (dslope f a) b ↔ DifferentiableAt 𝕜 f b := by
  simp only [← differentiableWithinAt_univ, differentiableWithinAt_dslope_of_ne h]

lemma sub_smul_dslope_of_zero {f : 𝕜 → E} {a : 𝕜} (hf : f a = 0) (b : 𝕜) :
    (b - a) • dslope f a b = f b := by
  simp [hf]

lemma pow_sub_smul_iterate_dslope_of_zero {f : 𝕜 → E} {a : 𝕜} (n : ℕ)
    (hf : ∀ k < n, (Function.swap dslope a)^[k] f a = 0) (b : 𝕜) :
    (b - a) ^ n • (Function.swap dslope a)^[n] f b = f b := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', pow_succ, mul_smul,
      sub_smul_dslope_of_zero (hf n n.lt_succ_self), ih (by grind)]
