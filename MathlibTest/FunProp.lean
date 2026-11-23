import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.SigmaAlgebra.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! # Main test file for fun_prop

Use this file for `fun_prop` tests that depend on mathlib
`fun_prop_dev` is for unit and synthetic tests avoiding mathlib.
-/

open Filter Set
open scoped Topology

private noncomputable def foo (x : {x : ℝ // IsUnit x}) : ℝ :=
  Checked.div (x.val ^ 2 * (Real.log x.val) ^ 2 - Real.exp x.val) x.val x.property

example : ContinuousOn foo Set.univ := by
  have : ContinuousOn (Subtype.val : {x : ℝ // IsUnit x} → ℝ) Set.univ :=
    continuous_subtype_val.continuousOn
  unfold foo
  fun_prop (disch := aesop)

example (y : {x : ℝ // IsUnit x}) : ContinuousAt foo y := by
  have : ContinuousAt Subtype.val y := continuous_subtype_val.continuousAt
  unfold foo
  fun_prop (disch := first | exact y.property.ne_zero | exact Subtype.property _)

example : DifferentiableOn ℝ foo (Subtype.val ⁻¹' ({0}ᶜ : Set ℝ)) Subtype.val := by
  have hn : DifferentiableOn ℝ (fun x ↦ x ^ 2 * (Real.log x) ^ 2 - Real.exp x)
      ({0}ᶜ : Set ℝ) := by
    fun_prop (disch := exact fun _ hx ↦ hx)
  exact hn.div (by fun_prop) (fun _ hx ↦ Ne.isUnit hx)

example (y : {x : ℝ // IsUnit x}) : DifferentiableAt ℝ foo y Subtype.val := by
  have hn : DifferentiableAt ℝ (fun x ↦ x ^ 2 * (Real.log x) ^ 2 - Real.exp x) y.val := by
    fun_prop (disch := exact y.property.ne_zero)
  exact hn.div (by fun_prop) y.property

-- The smoothness predicates use ambient representatives of a restricted quotient.
example {n} (q : ℝ → ℝ)
    (hq : ∀ x ∈ ({0}ᶜ : Set ℝ), ∃ hx : IsUnit x, q x = Checked.div (Real.exp x) x hx) :
    ContDiffOn ℝ n (fun x ↦ x * (Real.log x) ^ 2 - q x) ({0}ᶜ : Set ℝ) := by
  have : ContDiffOn ℝ n q ({0}ᶜ : Set ℝ) :=
    ContDiffOn.div (by fun_prop) (by fun_prop) hq
  fun_prop (disch := aesop)

example {n} {y : ℝ} (hy : y ≠ 0) (q : ℝ → ℝ)
    (hq : ∀ᶠ x in nhds y, ∃ hx : IsUnit x, q x = Checked.div (Real.exp x) x hx) :
    ContDiffAt ℝ n (fun x ↦ x * (Real.log x) ^ 2 - q x) y := by
  have : ContDiffAt ℝ n q y := ContDiffAt.div (by fun_prop) (by fun_prop) hq
  fun_prop (disch := aesop)

example : Continuous fun ((x, _, _) : ℝ × ℝ × ℝ) ↦ x := by fun_prop
example : Continuous fun ((_, y, _) : ℝ × ℝ × ℝ) ↦ y := by fun_prop
example : Continuous fun ((_, _, z) : ℝ × ℝ × ℝ) ↦ z := by fun_prop

-- This theorem is meant to work together with `measurable_of_continuousOn_compl_singleton`
-- Unification of `(hf : ContinuousOn f {a}ᶜ)` with this theorem determines the point `a` to be `0`
@[fun_prop]
theorem ContinuousOn.log' : ContinuousOn Real.log {0}ᶜ := ContinuousOn.log (by fun_prop) (by aesop)

-- Notice that no theorems about measurability of log are used. It is inferred from continuity.
example : Measurable Real.log := by fun_prop

example : Measurable foo := by
  fun_prop (disch := aesop) [foo]

-- Notice that no theorems about measurability of log are used. It is inferred from continuity.
example (μ : MeasureTheory.Measure {x : ℝ // IsUnit x}) : AEMeasurable foo μ := by
  fun_prop (maxTransitionDepth := 2) (disch := aesop) [foo]

private def TNum (i : Fin 4) (t : ℝ) : ℝ :=
  ![1, 1 - t, t, t * (1 - t)] i

private def TDen (i : Fin 4) (t : ℝ) : ℝ :=
  ![1 + (1 - t) + t * (1 - t), 1 + (1 - t) + t,
    (1 - t) + t + t * (1 - t), 1 + t + t * (1 - t)] i

private theorem TDen_isUnit (i : Fin 4) (t : Set.Icc (0 : ℝ) 1) : IsUnit (TDen i t.val) := by
  apply (ne_of_gt ?_).isUnit
  have hmul := mul_nonneg t.2.1 (sub_nonneg.mpr t.2.2)
  fin_cases i <;> dsimp [TDen] <;> linarith [t.2.1, t.2.2]

private noncomputable def T (t : Set.Icc (0 : ℝ) 1) : ℝ :=
  ∑ i : Fin 4, Checked.div (TNum i t.val) (TDen i t.val) (TDen_isUnit i t)

private theorem continuousOn_T : ContinuousOn T Set.univ := by
  have : ContinuousOn (Subtype.val : Set.Icc (0 : ℝ) 1 → ℝ) Set.univ :=
    continuous_subtype_val.continuousOn
  have hterm (i : Fin 4) : ContinuousOn (fun t : Set.Icc (0 : ℝ) 1 ↦
      Checked.div (TNum i t.val) (TDen i t.val) (TDen_isUnit i t)) Set.univ := by
    have hu (t : Set.Icc (0 : ℝ) 1) := TDen_isUnit i t
    fin_cases i <;> dsimp [TNum, TDen] at hu ⊢ <;> fun_prop (disch := exact hu)
  unfold T
  fun_prop (disch := exact fun i _ ↦ hterm i)

example : DifferentiableOn ℝ T Set.univ Subtype.val := by
  have hterm (i : Fin 4) : DifferentiableOn ℝ (fun t : Set.Icc (0 : ℝ) 1 ↦
      Checked.div (TNum i t.val) (TDen i t.val) (TDen_isUnit i t)) Set.univ Subtype.val := by
    have hn : Differentiable ℝ (fun t ↦ TNum i t) := by
      fin_cases i <;> dsimp [TNum] <;> fun_prop
    have hd : Differentiable ℝ (fun t ↦ TDen i t) := by
      fin_cases i <;> dsimp [TDen] <;> fun_prop
    intro t _
    rw [differentiableWithinAt_univ]
    obtain ⟨d, h⟩ := (hn t.val).div (hd t.val) (TDen_isUnit i t)
    have hj : Continuous (fun x : Set.Icc (0 : ℝ) 1 ↦
        (⟨x.val, TDen_isUnit i x⟩ : {x : ℝ // IsUnit (TDen i x)})) :=
      continuous_subtype_val.subtype_mk _
    exact ⟨d, .of_isLittleOTVS (h.isLittleOTVS.comp_tendsto hj.continuousAt)⟩
  unfold T
  fun_prop (disch := exact fun i _ ↦ hterm i)

example {n} (q : Fin 4 → ℝ → ℝ)
    (hq : ∀ i t (ht : t ∈ Set.Icc (0 : ℝ) 1),
      q i t = Checked.div (TNum i t) (TDen i t) (TDen_isUnit i ⟨t, ht⟩)) :
    ContDiffOn ℝ n (fun t ↦ ∑ i, q i t) (Set.Icc 0 1) := by
  have hterm (i : Fin 4) : ContDiffOn ℝ n (q i) (Set.Icc 0 1) := by
    have hn : ContDiffOn ℝ n (fun t ↦ TNum i t) (Set.Icc 0 1) := by
      fin_cases i <;> dsimp [TNum] <;> fun_prop
    have hd : ContDiffOn ℝ n (fun t ↦ TDen i t) (Set.Icc 0 1) := by
      fin_cases i <;> dsimp [TDen] <;> fun_prop
    exact hn.div hd (fun t ht ↦ ⟨TDen_isUnit i ⟨t, ht⟩, hq i t ht⟩)
  fun_prop (disch := exact fun i _ ↦ hterm i)

example : Measurable T := by
  have : Continuous T := continuousOn_univ.mp continuousOn_T
  fun_prop

example (μ : MeasureTheory.Measure (Set.Icc (0 : ℝ) 1)) : AEMeasurable T μ := by
  have : Continuous T := continuousOn_univ.mp continuousOn_T
  fun_prop

example (z : ℂ) : MeromorphicAt (fun t ↦ Complex.cosh t) z := by
  fun_prop

example (z : ℂ) : MeromorphicAt (fun t ↦ Complex.cosh (2 * t)) z := by
  fun_prop

/-! ### `MeromorphicOn` -/

section MeromorphicOn

variable {U : Set ℂ} {f g : ℂ → ℂ}

example : MeromorphicOn (fun z ↦ z) U := by fun_prop

example (c : ℂ) : MeromorphicOn (fun _ ↦ c) U := by fun_prop

example (hf : MeromorphicOn f U) (hg : MeromorphicOn g U)
    (h : ∀ x ∈ U, range (fun z : {z // IsUnit (g z)} ↦ z.val) ∈ 𝓝[≠] x) :
    MeromorphicOn (fun z : {z // IsUnit (g z)} ↦
      f z * Checked.inv (g z) z.property + Checked.div (f z) (g z) z.property +
        -(3 * g z ^ 2)) U Subtype.val := by
  have hp : MeromorphicOn (fun z ↦ -(3 * g z ^ 2)) U := by fun_prop
  intro x hx
  have hfx : MeromorphicAt (fun z : {z // IsUnit (g z)} ↦ f z) x Subtype.val :=
    (hf x hx).comp_domain Subtype.val (h x hx)
  have hpx : MeromorphicAt (fun z : {z // IsUnit (g z)} ↦ -(3 * g z ^ 2)) x Subtype.val :=
    (hp x hx).comp_domain Subtype.val (h x hx)
  have hi : MeromorphicAt (fun z : {z // IsUnit (g z)} ↦ Checked.inv (g z) z.property)
      x Subtype.val := (hg x hx).inv (h x hx)
  have hd : MeromorphicAt (fun z : {z // IsUnit (g z)} ↦ Checked.div (f z) (g z) z.property)
      x Subtype.val := (hf x hx).div (hg x hx) (h x hx)
  exact ((hfx.fun_mul hi).fun_add hd).fun_add hpx

-- Analytic leaves are reached through the `AnalyticOnNhd.meromorphicOn` transition.
example :
    MeromorphicOn (fun z : {z : ℂ // IsUnit (z ^ 2 - 1)} ↦
      Checked.div (Complex.exp z) (z.val ^ 2 - 1) z.property) U (id ∘ Subtype.val) := by
  have hn : MeromorphicOn Complex.exp U :=
    AnalyticOnNhd.meromorphicOn (by fun_prop)
  have hd : MeromorphicOn (fun z ↦ z ^ 2 - 1 : ℂ → ℂ) U := by fun_prop
  apply hn.div hd
  intro x _
  have avoid (a : ℂ) : ∀ᶠ y in 𝓝[≠] x, y ≠ a := by
    by_cases hx : x = a
    · subst x
      exact self_mem_nhdsWithin
    · exact mem_nhdsWithin_of_mem_nhds (isOpen_compl_singleton.mem_nhds hx)
  filter_upwards [avoid 1, avoid (-1)] with y hy₁ hy₂
  exact ⟨⟨y, (sub_ne_zero.mpr (sq_ne_one_iff.mpr ⟨hy₁, hy₂⟩)).isUnit⟩, rfl⟩

example (hf : Meromorphic f) : MeromorphicOn (fun z ↦ f z + Complex.sin z) U := by
  have : MeromorphicOn f U := hf.meromorphicOn
  have : MeromorphicOn Complex.sin U := AnalyticOnNhd.meromorphicOn (by fun_prop)
  fun_prop

-- Composition: the outer function must be the meromorphic one.
example (hf : Meromorphic f) : MeromorphicOn (fun z ↦ f (z ^ 2 + 1)) U := by fun_prop

example (N : Finset ℕ) (F : ℕ → ℂ → ℂ) (h : ∀ n ∈ N, MeromorphicOn (F n) U) :
    MeromorphicOn (fun z ↦ ∑ n ∈ N, F n z) U := by fun_prop

example (hf : MeromorphicOn f U) (hn : ∀ x ∈ U, ∀ᶠ y in nhdsWithin x {x}ᶜ, f y ≠ 0) :
    MeromorphicOn (fun z : {z // DifferentiableAt ℂ f z ∧ IsUnit (f z)} ↦
      logDeriv f z.val id z.property.1.existsUnique_hasDerivAt z.property.2) U Subtype.val := by
  fun_prop (disch := assumption)

private abbrev GammaRegular := {z : ℂ // ∀ n : ℕ, z ≠ -n}

-- Evaluate the two sections on their common regular domain before forming the checked quotient.
example
    (hc : ∀ x ∈ U, range (fun z : {z : GammaRegular //
      IsUnit (Complex.digamma z.val z.property)} ↦ z.val.val) ∈ 𝓝[≠] x) :
    MeromorphicOn (fun z : {z : GammaRegular // IsUnit (Complex.digamma z.val z.property)} ↦
      Checked.div (Complex.Gamma z.val.val) (Complex.digamma z.val.val z.val.property)
        z.property) U ((Subtype.val : GammaRegular → ℂ) ∘ Subtype.val) := by
  have hreg (x : ℂ) (hx : x ∈ U) : range (Subtype.val : GammaRegular → ℂ) ∈ 𝓝[≠] x :=
    mem_of_superset (hc x hx) (range_comp_subset_range Subtype.val Subtype.val)
  have hG : MeromorphicOn (fun z : GammaRegular ↦ Complex.Gamma z.val) U Subtype.val := by
    intro x hx
    let lift (z : GammaRegular) : Complex.meromorphicGamma.regularLocus :=
      ⟨⟨z.val, mem_univ _⟩, (Complex.mem_regularLocus_meromorphicGamma_iff _).2 z.property⟩
    exact ((MeromorphicSection.meromorphicOn_eval Complex.meromorphicGamma x (mem_univ _)).comp_domain
      lift (hreg x hx)).congr_domain (.of_forall fun z ↦ Complex.eval_meromorphicGamma z.property)
  have hD : MeromorphicOn (fun z : GammaRegular ↦ Complex.digamma z.val z.property)
      U Subtype.val := by
    intro x hx
    let lift (z : GammaRegular) : Complex.meromorphicDigamma.regularLocus :=
      ⟨⟨z.val, mem_univ _⟩, Complex.mem_regularLocus_meromorphicDigamma z.property⟩
    exact ((MeromorphicSection.meromorphicOn_eval Complex.meromorphicDigamma x (mem_univ _)).comp_domain
      lift (hreg x hx)).congr_domain (.of_forall fun z ↦ Complex.eval_meromorphicDigamma z.property)
  exact hG.div hD hc

example (h : ∀ z ∈ U, ∀ n : ℕ, z ^ 2 + 1 ≠ -n) :
    MeromorphicOn (fun z ↦ Complex.Gamma (z ^ 2 + 1)) U := by
  intro z hz
  apply AnalyticAt.meromorphicAt
  have hinner : AnalyticAt ℂ (fun w : ℂ ↦ w ^ 2 + 1) z := by fun_prop
  exact (Complex.analyticAt_Gamma (h z hz)).comp
    (f := fun w : ℂ ↦ w ^ 2 + 1) (x := z) hinner

end MeromorphicOn

private theorem t1 : (5: ℕ) + (1 : ℕ∞) ≤ (12 : WithTop ℕ∞) := by norm_cast

example {f : ℝ → ℝ} (hf : ContDiff ℝ 12 f) :
    Differentiable ℝ (iteratedDeriv 5 (fun x ↦ f (2 * (f (x + x))) + x)) := by
  fun_prop (disch := exact t1)

-- This example used to panic due to loose bvars before #31001.
-- TODO: this still fails because `fun_prop` cannot use `hl`.
/--
error: `fun_prop` was unable to prove `MeasureTheory.AEStronglyMeasurable l.prod μ`

Issues:
  No theorems found for `f` in order to prove `MeasureTheory.AEStronglyMeasurable (fun a => f a) μ`
-/
#guard_msgs in
example {α : Type*} {m₀ : SigmaAlgebra α} {μ : MeasureTheory.Measure α} {M : Type*}
    [CommMonoid M] [TopologicalSpace M] [ContinuousMul M] (l : Multiset (α → M))
    (hl : ∀ f ∈ l, MeasureTheory.AEStronglyMeasurable f μ) :
    MeasureTheory.AEStronglyMeasurable l.prod μ := by
  fun_prop

/-! Test that `fun_prop` should work on `→` and `∀` -/

attribute [fun_prop] Measurable.imp Measurable.forall

example {α : Type*} [SigmaAlgebra α] {p q : α → Prop} (hp : Measurable p) (hq : Measurable q) :
    Measurable fun x => p x → q x := by
  fun_prop

example {α ι : Type*} [SigmaAlgebra α] [Countable ι] {p : ι → α → Prop}
    (hp : ∀ i, Measurable (p i)) : Measurable fun x => ∀ i, p i x := by
  fun_prop
