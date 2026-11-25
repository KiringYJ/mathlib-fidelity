/-
Copyright (c) 2024 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Heather Macbeth
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Analysis.InnerProductSpace.NormPow
public import Mathlib.Data.Finset.Interval
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Gagliardo-Nirenberg-Sobolev inequality

In this file we prove the Gagliardo-Nirenberg-Sobolev inequality.
This states that for compactly supported `C¹`-functions between finite-dimensional vector spaces,
we can bound the `L^p`-norm of `u` by the `L^q` norm of the derivative of `u`.
The bound is up to a constant that is independent of the function `u`.
Let `n` be the dimension of the domain.

The main step in the proof, which we dubbed the "grid-lines lemma" below, is a complicated
inductive argument that involves manipulating an `n+1`-fold iterated integral and a product of
`n+2` factors. In each step, one pushes one of the integral inside (all but one of)
the factors of the product using Hölder's inequality. The precise formulation of the induction
hypothesis (`MeasureTheory.GridLines.T_insert_le_T_lmarginal_singleton`) is tricky,
and none of the 5 sources we referenced stated it.

In the formalization we use the operation `MeasureTheory.lmarginal` to work with the iterated
integrals, and use `MeasureTheory.lmarginal_insert'` to conveniently push one of the integrals
inside. The Hölder's inequality step is done using `ENNReal.lintegral_mul_prod_norm_pow_le`.

The conclusions of the main results below are an estimation up to a constant multiple.
We don't really care about this constant, other than that it only depends on some pieces of data,
typically `E`, `μ`, `p` and sometimes also the codomain of `u` or the support of `u`.
We state these constants as separate definitions.

## Main results

* `MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq`:
  The bound holds for `1 ≤ p`, `0 < n` and `q⁻¹ = p⁻¹ - n⁻¹`
* `MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_le`:
  The bound holds when `1 ≤ p < n`, `0 ≤ q` and `p⁻¹ - n⁻¹ ≤ q⁻¹`.
  Note that in this case the constant depends on the support of `u`.

Potentially also useful:
* `MeasureTheory.eLpNorm_le_eLpNorm_fderiv_one`: this is the inequality for `q = 1`.
  In this version, the codomain can be an arbitrary Banach space.
* `MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq_inner`: in this version,
  the codomain is assumed to be a Hilbert space, without restrictions on its dimension.
-/

@[expose] public section

open scoped ENNReal NNReal
open Set Function Finset MeasureTheory Measure Filter

noncomputable section

variable {ι : Type*}

local prefix:max "#" => Fintype.card

/-! ## The grid-lines lemma -/

variable {A : ι → Type*} [∀ i, SigmaAlgebra (A i)]
  (μ : ∀ i, Measure (A i))

namespace MeasureTheory

section DecidableEq

variable [DecidableEq ι]

namespace GridLines

/-- The "grid-lines operation" (not a standard name) which is central in the inductive proof of the
Sobolev inequality.

For a finite dependent product `Π i : ι, A i` of sigma-finite measure spaces, a finite set `s` of
indices from `ι`, and a (later assumed nonnegative) real number `p`, this operation acts on a
function `f` from `Π i, A i` into the extended nonnegative reals.  The operation is to partially
integrate, in the `s` co-ordinates, the function whose value at `x : Π i, A i` is obtained by
multiplying a certain power of `f` with the product, for each co-ordinate `i` in `s`, of a certain
power of the integral of `f` along the "grid line" in the `i` direction through `x`.

We are most interested in this operation when the set `s` is the universe in `ι`, but as a proxy for
"induction on dimension" we define it for a general set `s` of co-ordinates: the `s`-grid-lines
operation on a function `f` which is constant along the co-ordinates in `sᶜ` is morally (that is, up
to type-theoretic nonsense) the same thing as the universe-grid-lines operation on the associated
function on the "lower-dimensional" space `Π i : s, A i`. -/
def T (p : ℝ) (f : (∀ i, A i) → ℝ≥0∞) (s : Finset ι) : (∀ i, A i) → ℝ≥0∞ :=
  ∫⋯∫⁻_s, f ^ (1 - (s.card - 1 : ℝ) * p) * ∏ i ∈ s, (∫⋯∫⁻_{i}, f ∂μ) ^ p ∂μ

variable {p : ℝ}

@[simp] lemma T_univ [Fintype ι] [∀ i, SigmaFinite (μ i)] (f : (∀ i, A i) → ℝ≥0∞) (x : ∀ i, A i) :
    T μ p f univ x =
    ∫⁻ (x : ∀ i, A i), (f x ^ (1 - (#ι - 1 : ℝ) * p)
    * ∏ i : ι, (∫⁻ t : A i, f (update x i t) ∂(μ i)) ^ p) ∂(.pi μ) := by
  simp [T, lmarginal_singleton]

@[simp] lemma T_empty (f : (∀ i, A i) → ℝ≥0∞) (x : ∀ i, A i) :
    T μ p f ∅ x = f x ^ (1 + p) := by
  simp [T]

/-- The main inductive step in the grid-lines lemma for the Gagliardo-Nirenberg-Sobolev inequality.

The grid-lines operation `GridLines.T` on a nonnegative function on a finitary product type is
less than or equal to the grid-lines operation of its partial integral in one co-ordinate
(the latter intuitively considered as a function on a space "one dimension down"). -/
theorem T_insert_le_T_lmarginal_singleton [∀ i, SigmaFinite (μ i)] (hp₀ : 0 ≤ p) (s : Finset ι)
    (hp : (s.card : ℝ) * p ≤ 1)
    (i : ι) (hi : i ∉ s) {f : (∀ i, A i) → ℝ≥0∞} (hf : Measurable f) :
    T μ p f (insert i s) ≤ T μ p (∫⋯∫⁻_{i}, f ∂μ) s := by
  /- The proof is a tricky computation that relies on Hölder's inequality at its heart.
  The left-hand-side is an `|s|+1`-times iterated integral. Let `xᵢ` denote the `i`-th variable.
  We first push the integral over the `i`-th variable as the
  innermost integral. This is done in a single step with `MeasureTheory.lmarginal_insert'`,
  but in fact hides a repeated application of Fubini's theorem.
  The integrand is a product of `|s|+2` factors, in `|s|+1` of them we integrate over one
  additional variable. We split off the factor that integrates over `xᵢ`,
  and apply Hölder's inequality to the remaining factors (whose powers sum exactly to 1).
  After reordering factors, and combining two factors into one we obtain the right-hand side. -/
  calc T μ p f (insert i s)
      = ∫⋯∫⁻_insert i s,
            f ^ (1 - (s.card : ℝ) * p) * ∏ j ∈ insert i s, (∫⋯∫⁻_{j}, f ∂μ) ^ p ∂μ := by
          -- unfold `T` and reformulate the exponents
          simp_rw [T, card_insert_of_notMem hi]
          congr!
          push_cast
          ring
    _ = ∫⋯∫⁻_s, (fun x ↦ ∫⁻ (t : A i),
            (f (update x i t) ^ (1 - (s.card : ℝ) * p)
            * ∏ j ∈ insert i s, (∫⋯∫⁻_{j}, f ∂μ) (update x i t) ^ p) ∂(μ i)) ∂μ := by
          -- pull out the integral over `xᵢ`
          rw [lmarginal_insert' _ _ hi]
          · simp only [Pi.mul_apply, Pi.pow_apply, Finset.prod_apply]
          · change Measurable (fun x ↦ _)
            simp only [Pi.mul_apply, Pi.pow_apply, Finset.prod_apply]
            refine (hf.pow_const _).mul <| Finset.measurable_fun_prod _ ?_
            exact fun _ _ ↦ hf.lmarginal μ |>.pow_const _
    _ ≤ T μ p (∫⋯∫⁻_{i}, f ∂μ) s := lmarginal_mono (s := s) (fun x ↦ ?_)
  -- The remainder of the computation happens within an `|s|`-fold iterated integral
  simp only [Pi.mul_apply, Pi.pow_apply, Finset.prod_apply]
  set X := update x i
  have hF₁ : ∀ {j : ι}, Measurable fun t ↦ (∫⋯∫⁻_{j}, f ∂μ) (X t) :=
    fun {_} ↦ hf.lmarginal μ |>.comp <| measurable_update _
  have hF₀ : Measurable fun t ↦ f (X t) := hf.comp <| measurable_update _
  let k : ℝ := s.card
  have hk' : 0 ≤ 1 - k * p := by linarith only [hp]
  calc ∫⁻ t, f (X t) ^ (1 - k * p)
          * ∏ j ∈ insert i s, (∫⋯∫⁻_{j}, f ∂μ) (X t) ^ p ∂(μ i)
      = ∫⁻ t, (∫⋯∫⁻_{i}, f ∂μ) (X t) ^ p * (f (X t) ^ (1 - k * p)
          * ∏ j ∈ s, ((∫⋯∫⁻_{j}, f ∂μ) (X t) ^ p)) ∂(μ i) := by
              -- rewrite integrand so that `(∫⋯∫⁻_insert i s, f ∂μ) ^ p` comes first
              clear_value X
              congr! 2 with t
              simp_rw [prod_insert hi]
              ring_nf
    _ = (∫⋯∫⁻_{i}, f ∂μ) x ^ p *
          ∫⁻ t, f (X t) ^ (1 - k * p) * ∏ j ∈ s, ((∫⋯∫⁻_{j}, f ∂μ) (X t)) ^ p ∂(μ i) := by
              -- pull out this constant factor
              have : ∀ t, (∫⋯∫⁻_{i}, f ∂μ) (X t) = (∫⋯∫⁻_{i}, f ∂μ) x := by
                intro t
                rw [lmarginal_update_of_mem]
                exact Iff.mpr Finset.mem_singleton rfl
              simp_rw [this]
              rw [lintegral_const_mul]
              exact (hF₀.pow_const _).mul <| Finset.measurable_fun_prod _ fun _ _ ↦ hF₁.pow_const _
    _ ≤ (∫⋯∫⁻_{i}, f ∂μ) x ^ p *
          ((∫⁻ t, f (X t) ∂μ i) ^ (1 - k * p)
          * ∏ j ∈ s, (∫⁻ t, (∫⋯∫⁻_{j}, f ∂μ) (X t) ∂μ i) ^ p) := by
              -- apply Hölder's inequality
              gcongr
              apply ENNReal.lintegral_mul_prod_norm_pow_le
              · exact hF₀.aemeasurable
              · intros
                exact hF₁.aemeasurable
              · simp only [sum_const, nsmul_eq_mul]
                ring
              · exact hk'
              · exact fun _ _ ↦ hp₀
    _ = (∫⋯∫⁻_{i}, f ∂μ) x ^ p *
          ((∫⋯∫⁻_{i}, f ∂μ) x ^ (1 - k * p) * ∏ j ∈ s, (∫⋯∫⁻_{i, j}, f ∂μ) x ^ p) := by
              -- absorb the newly-created integrals into `∫⋯∫`
              congr! 2
              · rw [lmarginal_singleton]
              refine prod_congr rfl fun j hj => ?_
              have hi' : i ∉ ({j} : Finset ι) := by
                simp only [Finset.mem_singleton] at hj ⊢
                exact fun h ↦ hi (h ▸ hj)
              rw [lmarginal_insert _ hf hi']
    _ = (∫⋯∫⁻_{i}, f ∂μ) x ^ (p + (1 - k * p)) * ∏ j ∈ s, (∫⋯∫⁻_{i, j}, f ∂μ) x ^ p := by
              -- combine two `(∫⋯∫⁻_insert i s, f ∂μ) x` terms
              rw [ENNReal.rpow_add_of_nonneg]
              · ring
              · exact hp₀
              · exact hk'
    _ ≤ (∫⋯∫⁻_{i}, f ∂μ) x ^ (1 - (s.card - 1 : ℝ) * p) *
          ∏ j ∈ s, (∫⋯∫⁻_{j}, (∫⋯∫⁻_{i}, f ∂μ) ∂μ) x ^ p := by
              -- identify the result with the RHS integrand
              congr! 2 with j hj
              · ring
              · congr! 1
                rw [← lmarginal_union μ f hf]
                · congr
                  rw [Finset.union_comm]
                  rfl
                · rw [Finset.disjoint_singleton]
                  exact fun h ↦ hi (h ▸ hj)

/-- Auxiliary result for the grid-lines lemma.  Given a nonnegative function on a finitary product
type indexed by `ι`, and a set `s` in `ι`, consider partially integrating over the variables in
`sᶜ` and performing the "grid-lines operation" (see `GridLines.T`) to the resulting function in the
variables `s`.  This theorem states that this operation decreases as the number of grid-lines taken
increases. -/
theorem T_lmarginal_antitone [Fintype ι] [∀ i, SigmaFinite (μ i)]
    (hp₀ : 0 ≤ p) (hp : (#ι - 1 : ℝ) * p ≤ 1) {f : (∀ i, A i) → ℝ≥0∞} (hf : Measurable f) :
    Antitone (fun s ↦ T μ p (∫⋯∫⁻_sᶜ, f ∂μ) s) := by
  -- Reformulate (by induction): a function is decreasing on `Finset ι` if it decreases under the
  -- insertion of any element to any set.
  rw [Finset.antitone_iff_forall_insert_le]
  intro s i hi
  -- apply the lemma designed to encapsulate the inductive step
  convert! T_insert_le_T_lmarginal_singleton μ hp₀ s ?_ i hi (hf.lmarginal μ) using 2
  · rw [← lmarginal_union μ f hf]
    · rw [← insert_compl_insert hi]
      rfl
    rw [Finset.disjoint_singleton_left, notMem_compl]
    exact mem_insert_self i s
  · -- the main nontrivial point is to check that an exponent `p` satisfying `0 ≤ p` and
    -- `(#ι - 1) * p ≤ 1` is in the valid range for the inductive-step lemma
    refine le_trans ?_ hp
    gcongr
    suffices (s.card : ℝ) + 1 ≤ #ι by linarith
    rw [← card_add_card_compl s]
    norm_cast
    gcongr
    have hi' : sᶜ.Nonempty := ⟨i, by rwa [Finset.mem_compl]⟩
    rwa [← card_pos] at hi'

end GridLines

/-- The "grid-lines lemma" (not a standard name), stated with a general parameter `p` as the
exponent.  Compare with `lintegral_prod_lintegral_pow_le`.

For any finite dependent product `Π i : ι, A i` of sigma-finite measure spaces, for any
nonnegative real number `p` such that `(#ι - 1) * p ≤ 1`, for any function `f` from `Π i, A i` into
the extended nonnegative reals, we consider an associated "grid-lines quantity", the integral of an
associated function from `Π i, A i` into the extended nonnegative reals.  The value of this function
at `x : Π i, A i` is obtained by multiplying a certain power of `f` with the product, for each
co-ordinate `i`, of a certain power of the integral of `f` along the "grid line" in the `i`
direction through `x`.

This lemma bounds the Lebesgue integral of the grid-lines quantity by a power of the Lebesgue
integral of `f`. -/
theorem lintegral_mul_prod_lintegral_pow_le
    [Fintype ι] [∀ i, SigmaFinite (μ i)] {p : ℝ} (hp₀ : 0 ≤ p)
    (hp : (#ι - 1 : ℝ) * p ≤ 1) {f : (∀ i : ι, A i) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ^ (1 - (#ι - 1 : ℝ) * p) * ∏ i, (∫⁻ xᵢ, f (update x i xᵢ) ∂μ i) ^ p ∂.pi μ
    ≤ (∫⁻ x, f x ∂.pi μ) ^ (1 + p) := by
  cases isEmpty_or_nonempty (∀ i, A i)
  · simp
  inhabit ∀ i, A i
  have H : (∅ : Finset ι) ≤ Finset.univ := Finset.empty_subset _
  simpa [lmarginal_univ] using GridLines.T_lmarginal_antitone μ hp₀ hp hf H default

/-- Special case of the grid-lines lemma `lintegral_mul_prod_lintegral_pow_le`, taking the extremal
exponent `p = (#ι - 1)⁻¹`. -/
theorem lintegral_prod_lintegral_pow_le [Fintype ι] [∀ i, SigmaFinite (μ i)]
    {p : ℝ} (hp : Real.HolderConjugate #ι p)
    {f} (hf : Measurable f) :
    ∫⁻ x, ∏ i, (∫⁻ xᵢ, f (update x i xᵢ) ∂μ i) ^ ((1 : ℝ) / (#ι - 1 : ℝ)) ∂.pi μ
    ≤ (∫⁻ x, f x ∂.pi μ) ^ p := by
  have : Nontrivial ι :=
    Fintype.one_lt_card_iff_nontrivial.mp (by exact_mod_cast hp.lt)
  have h0 : (1 : ℝ) < #ι := by norm_cast; exact Fintype.one_lt_card
  have h1 : (0 : ℝ) < #ι - 1 := by linarith
  have h2 : 0 ≤ ((1 : ℝ) / (#ι - 1 : ℝ)) := by positivity
  have h3 : (#ι - 1 : ℝ) * ((1 : ℝ) / (#ι - 1 : ℝ)) = 1 := mul_div_cancel₀ _
  have h4 : p = 1 + 1 / ((#ι : ℝ) - 1) := by
    calc
      p = ((#ι - 1 : ℝ) + 1) / ((#ι : ℝ) - 1) := by rw [sub_add_cancel]; exact hp.conjugate_eq
      _ = 1 + 1 / ((#ι : ℝ) - 1) := by rw [add_div, div_self]
  simpa only [h3, sub_self, ENNReal.rpow_zero, one_mul, ← h4] using
    lintegral_mul_prod_lintegral_pow_le μ h2 h3.le hf

end DecidableEq

/-! ## The Gagliardo-Nirenberg-Sobolev inequality -/

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The **Gagliardo-Nirenberg-Sobolev inequality**.  Let `u` be a continuously differentiable
compactly-supported function `u` on `ℝⁿ`, for `n ≥ 2`.  (More literally we encode `ℝⁿ` as
`ι → ℝ` where `n := #ι` is finite and at least 2.)  Then the Lebesgue integral of the pointwise
expression `|u x| ^ (n / (n - 1))` is bounded above by the `n / (n - 1)`-th power of the Lebesgue
integral of the Fréchet derivative of `u`.

For a basis-free version, see `lintegral_pow_le_pow_lintegral_fderiv`. -/
theorem lintegral_pow_le_pow_lintegral_fderiv_aux [Fintype ι]
    {p : ℝ} (hp : Real.HolderConjugate #ι p)
    {u : (ι → ℝ) → F} (hu : ContDiff ℝ 1 u)
    (h2u : HasCompactSupport u) :
    ∫⁻ x, ‖u x‖ₑ ^ p ≤ (∫⁻ x, ‖fderiv ℝ u x id‖ₑ) ^ p := by
  classical
  /- For a function `f` in one variable and `t ∈ ℝ` we have
  `|f(t)| = `|∫_{-∞}^t Df(s)∂s| ≤ ∫_ℝ |Df(s)| ∂s` where we use the fundamental theorem of calculus.
  For each `x ∈ ℝⁿ` we let `u` vary in one of the `n` coordinates and apply the inequality above.
  By taking the product over these `n` factors, raising them to the power `(n-1)⁻¹` and integrating,
  we get the inequality `∫ |u| ^ (n/(n-1)) ≤ ∫ x, ∏ i, (∫ xᵢ, |Du(update x i xᵢ)|)^(n-1)⁻¹`.
  The result then follows from the grid-lines lemma. -/
  have : (1 : ℝ) ≤ ↑#ι - 1 := by
    have hι : (2 : ℝ) ≤ #ι := by exact_mod_cast hp.lt
    linarith
  calc ∫⁻ x, ‖u x‖ₑ ^ p
      = ∫⁻ x, (‖u x‖ₑ ^ (1 / (#ι - 1 : ℝ))) ^ (#ι : ℝ) := by
        -- a little algebraic manipulation of the exponent
        congr! 2 with x
        rw [← ENNReal.rpow_mul, one_div_mul_eq_div₀]
        exact congrArg (fun r : ℝ ↦ ‖u x‖ₑ ^ r) hp.conjugate_eq
    _ = ∫⁻ x, ∏ _i : ι, ‖u x‖ₑ ^ (1 / (#ι - 1 : ℝ)) := by
        -- express the left-hand integrand as a product of identical factors
        congr! 2 with x
        simp_rw [prod_const]
        norm_cast
    _ ≤ ∫⁻ x, ∏ i, (∫⁻ xᵢ, ‖fderiv ℝ u (update x i xᵢ) id‖ₑ) ^ ((1 : ℝ) / (#ι - 1 : ℝ)) := ?_
    _ ≤ (∫⁻ x, ‖fderiv ℝ u x id‖ₑ) ^ p := by
        -- apply the grid-lines lemma
        rw [volume_pi]
        exact lintegral_prod_lintegral_pow_le _ hp
          (f := fun x : ι → ℝ ↦ ‖fderiv ℝ u x id‖ₑ) (by fun_prop)
  -- we estimate |u x| using the fundamental theorem of calculus.
  apply lintegral_mono
  intro x
  apply Finset.prod_le_prod
  intro i _
  apply ENNReal.rpow_le_rpow _ (by positivity)
  calc ‖u x‖ₑ
    _ ≤ ∫⁻ xᵢ in Iic (x i), ‖deriv (u ∘ update x i) xᵢ id‖ₑ := by
        apply le_trans (by simp) (HasCompactSupport.enorm_le_lintegral_Ici_deriv _ _ _)
        · exact hu.comp (by convert! contDiff_update 1 x i)
        · exact h2u.comp_isClosedEmbedding (isClosedEmbedding_update x i)
    _ ≤ ∫⁻ xᵢ, ‖fderiv ℝ u (update x i xᵢ) id‖ₑ := ?_
  apply lintegral_mono' Measure.restrict_le_self
  intro y
  -- bound the derivative which appears
  calc ‖deriv (u ∘ update x i) y id‖ₑ =
      ‖(fderiv ℝ u (update x i y) id) (deriv (update x i) y id)‖ₑ := by
        rw [fderiv_comp_deriv _ (hu.differentiable one_ne_zero).differentiableAt
          (hasDerivAt_update x i y).differentiableAt]
    _ ≤ ‖fderiv ℝ u (update x i y) id‖ₑ * ‖deriv (update x i) y id‖ₑ :=
      ContinuousLinearMap.le_opENorm _ _
    _ ≤ ‖fderiv ℝ u (update x i y) id‖ₑ := by simp [deriv_update, Pi.enorm_single]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [SigmaAlgebra E] [BorelSpace E]
  [FiniteDimensional ℝ E] (μ : Measure E) [IsAddHaarMeasure μ]

open Module

/-- The constant factor occurring in the conclusion of `lintegral_pow_le_pow_lintegral_fderiv`.
It only depends on `E`, `μ` and `p`.
It is determined by the ratio of the measures on `E` and `ℝⁿ` and
the operator norm of a chosen equivalence `E ≃ ℝⁿ` (raised to suitable powers involving `p`). -/
irreducible_def lintegralPowLePowLIntegralFDerivConst (p : ℝ) : ℝ≥0 := by
  let ι := Fin (finrank ℝ E)
  have : finrank ℝ E = finrank ℝ (ι → ℝ) := by
    rw [finrank_fintype_fun_eq_card, Fintype.card_fin (finrank ℝ E)]
  let e : E ≃L[ℝ] ι → ℝ := ContinuousLinearEquiv.ofFinrankEq this
  let c := addHaarScalarFactor μ
    ((volume : Measure (ι → ℝ)).map e.symm e.symm.continuous.measurable.aemeasurable)
  have hc : 0 < c := addHaarScalarFactor_pos_of_isAddHaarMeasure ..
  exact (c * ‖(e.symm : (ι → ℝ) →L[ℝ] E)‖₊ ^ p) *
    Checked.inv (c ^ p) (NNReal.rpow_pos hc).ne'.isUnit

/-- The **Gagliardo-Nirenberg-Sobolev inequality**.  Let `u` be a continuously differentiable
compactly-supported function `u` on a normed space `E` of finite dimension `n ≥ 2`, equipped
with Haar measure. Then the Lebesgue integral of the pointwise expression
`|u x| ^ (n / (n - 1))` is bounded above by a constant times the `n / (n - 1)`-th power of the
Lebesgue integral of the Fréchet derivative of `u`. -/
theorem lintegral_pow_le_pow_lintegral_fderiv {u : E → F}
    (hu : ContDiff ℝ 1 u) (h2u : HasCompactSupport u)
    {p : ℝ} (hp : Real.HolderConjugate (finrank ℝ E) p) :
    ∫⁻ x, ‖u x‖ₑ ^ p ∂μ ≤
      lintegralPowLePowLIntegralFDerivConst μ p * (∫⁻ x, ‖fderiv ℝ u x id‖ₑ ∂μ) ^ p := by
  /- We reduce to the case where `E` is `ℝⁿ`, for which we have already proved the result using
  an explicit basis in `MeasureTheory.lintegral_pow_le_pow_lintegral_fderiv_aux`.
  This proof is not too hard, but takes quite some steps, reasoning about the equivalence
  `e : E ≃ ℝⁿ`, relating the measures on each sides of the equivalence,
  and estimating the derivative using the chain rule. -/
  set C := lintegralPowLePowLIntegralFDerivConst μ p
  let ι := Fin (finrank ℝ E)
  have hιcard : #ι = finrank ℝ E := Fintype.card_fin (finrank ℝ E)
  have : finrank ℝ E = finrank ℝ (ι → ℝ) := by simp [hιcard]
  let e : E ≃L[ℝ] ι → ℝ := ContinuousLinearEquiv.ofFinrankEq this
  have hp : Real.HolderConjugate #ι p := by rwa [hιcard]
  have h0p : 0 ≤ p := hp.symm.nonneg
  let c := addHaarScalarFactor μ
    ((volume : Measure (ι → ℝ)).map e.symm e.symm.continuous.measurable.aemeasurable)
  have hc : 0 < c := addHaarScalarFactor_pos_of_isAddHaarMeasure ..
  have h2c : μ = c • ((volume : Measure (ι → ℝ)).map e.symm
      e.symm.continuous.measurable.aemeasurable) := isAddLeftInvariant_eq_smul ..
  have h3c : (c : ℝ≥0∞) ≠ 0 := by simp_rw [ne_eq, ENNReal.coe_eq_zero, hc.ne', not_false_eq_true]
  have h0C : C = (c * ‖(e.symm : (ι → ℝ) →L[ℝ] E)‖₊ ^ p) *
      Checked.inv (c ^ p) (NNReal.rpow_pos hc).ne'.isUnit := by
    simp only [C, c, e, ι, lintegralPowLePowLIntegralFDerivConst]
  have hC : C * c ^ p = c * ‖(e.symm : (ι → ℝ) →L[ℝ] E)‖₊ ^ p := by
    rw [h0C, inv_mul_cancel_right₀]
  simp only [h2c, ENNReal.smul_def, lintegral_smul_measure, smul_eq_mul]
  let v : (ι → ℝ) → F := u ∘ e.symm
  have hv : ContDiff ℝ 1 v := hu.comp e.symm.contDiff
  have h2v : HasCompactSupport v := h2u.comp_homeomorph e.symm.toHomeomorph
  have :=
  calc ∫⁻ x, ‖u x‖ₑ ^ p ∂(volume : Measure (ι → ℝ)).map e.symm
        e.symm.continuous.measurable.aemeasurable
      = ∫⁻ y, ‖v y‖ₑ ^ p := by
        refine lintegral_map ?_ e.symm.continuous.measurable
        borelize F
        exact hu.continuous.measurable.nnnorm.coe_nnreal_ennreal.pow_const _
    _ ≤ (∫⁻ y, ‖fderiv ℝ v y id‖ₑ) ^ p := lintegral_pow_le_pow_lintegral_fderiv_aux hp hv h2v
    _ = (∫⁻ y, ‖(fderiv ℝ u (e.symm y) id).comp (fderiv ℝ e.symm y id)‖ₑ) ^ p := by
        apply congrArg (fun t : ℝ≥0∞ ↦ t ^ p)
        apply lintegral_congr
        intro y
        rw [show fderiv ℝ v y id =
          (fderiv ℝ u (e.symm y) id).comp (fderiv ℝ e.symm y id) from
            fderiv_comp y (hu.differentiable one_ne_zero (e.symm y)) e.symm.differentiableAt]
    _ ≤ (∫⁻ y, ‖fderiv ℝ u (e.symm y) id‖ₑ * ‖(e.symm : (ι → ℝ) →L[ℝ] E)‖ₑ) ^ p := by
        refine ENNReal.rpow_le_rpow (lintegral_mono fun y ↦ ?_) h0p
        rw [e.symm.fderiv]
        apply ContinuousLinearMap.opENorm_comp_le
    _ = (‖(e.symm : (ι → ℝ) →L[ℝ] E)‖ₑ * ∫⁻ y, ‖fderiv ℝ u (e.symm y) id‖ₑ) ^ p := by
        rw [lintegral_mul_const, mul_comm]
        fun_prop
    _ = (‖(e.symm : (ι → ℝ) →L[ℝ] E)‖₊ ^ p : ℝ≥0) * (∫⁻ y, ‖fderiv ℝ u (e.symm y) id‖ₑ) ^ p := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ h0p, enorm_eq_nnnorm, ← ENNReal.coe_rpow_of_nonneg _ h0p]
    _ = (‖(e.symm : (ι → ℝ) →L[ℝ] E)‖₊ ^ p : ℝ≥0)
        * (∫⁻ x, ‖fderiv ℝ u x id‖ₑ ∂(volume : Measure (ι → ℝ)).map e.symm
          e.symm.continuous.measurable.aemeasurable) ^ p := by
        congr
        rw [lintegral_map _ e.symm.continuous.measurable]
        fun_prop
  rw [← ENNReal.mul_le_mul_iff_right h3c ENNReal.coe_ne_top, ← mul_assoc, ← ENNReal.coe_mul, ← hC,
    ENNReal.coe_mul] at this
  rw [ENNReal.mul_rpow_of_nonneg _ _ h0p, ← mul_assoc, ← ENNReal.coe_rpow_of_ne_zero hc.ne']
  exact this

/-- The constant factor occurring in the conclusion of `eLpNorm_le_eLpNorm_fderiv_one`.
It only depends on `E`, `μ` and `p`. -/
irreducible_def eLpNormLESNormFDerivOneConst (p : ℝ) (hp : p ≠ 0) : ℝ≥0 :=
  lintegralPowLePowLIntegralFDerivConst μ p ^ Checked.inv p hp.isUnit

/-- The **Gagliardo-Nirenberg-Sobolev inequality**.  Let `u` be a continuously differentiable
compactly-supported function `u` on a normed space `E` of finite dimension `n ≥ 2`, equipped
with Haar measure. Then the `Lᵖ` norm of `u`, where `p := n / (n - 1)`, is bounded above by
a constant times the `L¹` norm of the Fréchet derivative of `u`. -/
theorem eLpNorm_le_eLpNorm_fderiv_one {u : E → F} (hu : ContDiff ℝ 1 u) (h2u : HasCompactSupport u)
    {p : ℝ≥0} (hp : NNReal.HolderConjugate (finrank ℝ E) p) :
    eLpNorm u p μ ≤ eLpNormLESNormFDerivOneConst μ p hp.coe.symm.pos.ne' *
      eLpNorm (fun x ↦ fderiv ℝ u x id) 1 μ := by
  have h0p : 0 < (p : ℝ) := hp.coe.symm.pos
  rw [eLpNorm_one_eq_lintegral_enorm,
    ← ENNReal.rpow_le_rpow_iff h0p, ENNReal.mul_rpow_of_nonneg _ _ h0p.le,
    ← ENNReal.coe_rpow_of_nonneg _ h0p.le, eLpNormLESNormFDerivOneConst, ← NNReal.rpow_mul,
    eLpNorm_nnreal_pow_eq_lintegral hp.symm.pos.ne',
    inv_mul_cancel₀ (ha := h0p.ne'.isUnit), NNReal.rpow_one]
  exact lintegral_pow_le_pow_lintegral_fderiv μ hu h2u hp.coe

/-- The constant factor occurring in the conclusion of `eLpNorm_le_eLpNorm_fderiv_of_eq_inner`.
It only depends on `E`, `μ` and `p`. -/
def eLpNormLESNormFDerivOfEqInnerConst (p : ℝ) (hn : 1 < finrank ℝ E)
    (hp : p ≠ (finrank ℝ E : ℝ)) : ℝ≥0 :=
  let n := finrank ℝ E
  let h₀ : (1 : ℝ≥0) < n := by exact_mod_cast hn
  let n' := NNReal.conjExponent n h₀
  let hc : NNReal.HolderConjugate n n' := .conjExponent h₀
  eLpNormLESNormFDerivOneConst μ n' hc.coe.symm.pos.ne' *
    (Checked.div (p * (n - 1)) (n - p) (sub_ne_zero.mpr hp.symm).isUnit).toNNReal

variable {F' : Type*} [NormedAddCommGroup F'] [InnerProductSpace ℝ F']

/-- The **Gagliardo-Nirenberg-Sobolev inequality**.  Let `u` be a continuously differentiable
compactly-supported function `u` on a normed space `E` of finite dimension `n`, equipped
with Haar measure, let `1 ≤ p < n` and let `p' > 0` satisfy `p'⁻¹ = p⁻¹ - n⁻¹`.
Then the `Lᵖ'` norm of `u` is bounded above by a constant times the `Lᵖ` norm of
the Fréchet derivative of `u`.

Note: The codomain of `u` needs to be a Hilbert space.
-/
theorem eLpNorm_le_eLpNorm_fderiv_of_eq_inner {u : E → F'}
    (hu : ContDiff ℝ 1 u) (h2u : HasCompactSupport u)
    {p p' : ℝ≥0} (hp : 1 ≤ p) (h2p : p < finrank ℝ E) (hp'0 : p' ≠ 0)
    (hp' : Checked.inv (p' : ℝ) (NNReal.coe_ne_zero.mpr hp'0).isUnit =
      Checked.inv (p : ℝ) (NNReal.coe_ne_zero.mpr (zero_lt_one.trans_le hp).ne').isUnit -
      Checked.inv (finrank ℝ E : ℝ)
        (Nat.cast_ne_zero.mpr (Nat.one_lt_cast.mp (hp.trans_lt h2p)).pos.ne').isUnit) :
    eLpNorm u p' μ ≤ eLpNormLESNormFDerivOfEqInnerConst μ p
      (Nat.one_lt_cast.mp (hp.trans_lt h2p)) ((NNReal.coe_lt_coe.mpr h2p).ne) *
      eLpNorm (fun x ↦ fderiv ℝ u x id) p μ := by
  /- Here we derive the GNS-inequality for `p ≥ 1` from the version with `p = 1`.
  For `p > 1` we apply the previous version to the function `|u|^γ` for a suitably chosen `γ`.
  The proof requires that `x ↦ |x|^p` is smooth in the codomain, so we require that it is a
  Hilbert space. -/
  let n := finrank ℝ E
  have h1n : (1 : ℝ≥0) < n := hp.trans_lt h2p
  let n' := NNReal.conjExponent n h1n
  have hn : NNReal.HolderConjugate n n' := .conjExponent h1n
  have h0p : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have h0n : 0 < (n : ℝ) := hn.coe.pos
  have h2n : (0 : ℝ) < n - 1 := hn.coe.sub_one_pos
  have hnp : (0 : ℝ) < n - p := sub_pos.mpr (NNReal.coe_lt_coe.mpr h2p)
  have hp'R : (p' : ℝ) = (p : ℝ) * n / ((n : ℝ) - p) := by
    apply eq_div_iff.mpr
    have h := hp'
    field_simp at h
    linear_combination -h
  rcases hp.eq_or_lt with rfl | hp
  -- the case `p = 1`
  · have he : p' = n' := by
      apply NNReal.coe_injective
      calc
        (p' : ℝ) = (n : ℝ) / ((n : ℝ) - 1) := by simpa only [NNReal.coe_one, one_mul] using hp'R
        _ = (n' : ℝ) := by simpa only [NNReal.coe_natCast] using hn.coe.conjugate_eq.symm
    simpa [he, eLpNormLESNormFDerivOfEqInnerConst, n', n] using
      eLpNorm_le_eLpNorm_fderiv_one μ hu h2u hn
  -- the case `p > 1`
  have hpR : (1 : ℝ) < p := NNReal.coe_lt_coe.mpr hp
  let q := Real.conjExponent p hpR.ne'
  have hq : Real.HolderConjugate p q := .conjExponent hpR
  have h2q : 1 / (n' : ℝ) - 1 / q = 1 / (p' : ℝ) := by
    simp only [one_div₀, hp', ← hq.one_sub_inv, ← hn.coe.one_sub_inv, sub_sub_sub_cancel_left,
      NNReal.coe_natCast, n]
  let γ : ℝ≥0 := .mk ((p : ℝ) * ((n : ℝ) - 1) / ((n : ℝ) - p)) (by positivity)
  have h0γ : (γ : ℝ) = (p : ℝ) * ((n : ℝ) - 1) / ((n : ℝ) - p) := rfl
  have h1γ : 1 < (γ : ℝ) := by
    rwa [h0γ, one_lt_div hnp, mul_sub, mul_one, sub_lt_sub_iff_right, lt_mul_iff_one_lt_left]
    exact hn.coe.pos
  have h2γ : γ * n' = p' := by
    apply NNReal.coe_injective
    rw [NNReal.coe_mul, h0γ, hn.coe.conjugate_eq, hp'R]
    simp only [NNReal.coe_natCast]
    field
  have h3γ : ((γ : ℝ) - 1) * q = p' := by
    rw [h0γ, hq.conjugate_eq, hp'R]
    field
  have h4γ : (γ : ℝ) ≠ 0 := (zero_lt_one.trans h1γ).ne'
  by_cases h3u : ∫⁻ x, ‖u x‖ₑ ^ (p' : ℝ) ∂μ = 0
  · rw [eLpNorm_nnreal_eq_lintegral hp'0, h3u, ENNReal.zero_rpow_of_pos] <;> positivity
  have h4u : ∫⁻ x, ‖u x‖ₑ ^ (p' : ℝ) ∂μ ≠ ∞ := by
    refine lintegral_rpow_enorm_lt_top_of_eLpNorm'_lt_top
      ((NNReal.coe_pos.trans pos_iff_ne_zero).mpr hp'0) ?_ |>.ne
    rw [← eLpNorm_nnreal_eq_eLpNorm' hp'0]
    exact hu.continuous.memLp_of_hasCompactSupport (μ := μ) h2u |>.eLpNorm_lt_top
  have h5u : (∫⁻ x, ‖u x‖ₑ ^ (p' : ℝ) ∂μ) ^ (1 / q) ≠ 0 :=
    ENNReal.rpow_pos (pos_iff_ne_zero.mpr h3u) h4u |>.ne'
  have h6u : (∫⁻ x, ‖u x‖ₑ ^ (p' : ℝ) ∂μ) ^ (1 / q) ≠ ∞ := by finiteness
  have h7u := hu.continuous -- for fun_prop
  let v : E → ℝ := fun x ↦ ‖u x‖ ^ (γ : ℝ)
  have hv : ContDiff ℝ 1 v := hu.norm_rpow h1γ
  have h2v : HasCompactSupport v := h2u.norm.rpow_const h4γ
  set C := eLpNormLESNormFDerivOneConst μ n' hn.coe.symm.pos.ne'
  have :=
  calc (∫⁻ x, ‖u x‖ₑ ^ (p' : ℝ) ∂μ) ^ (1 / (n' : ℝ)) = eLpNorm v n' μ := by
        rw [← h2γ, eLpNorm_nnreal_eq_lintegral hn.symm.pos.ne']
        simp (discharger := positivity) [v, Real.enorm_rpow_of_nonneg, ENNReal.rpow_mul]
    _ ≤ C * eLpNorm (fun x ↦ fderiv ℝ v x id) 1 μ := eLpNorm_le_eLpNorm_fderiv_one μ hv h2v hn
    _ = C * ∫⁻ x, ‖fderiv ℝ v x id‖ₑ ∂μ := by rw [eLpNorm_one_eq_lintegral_enorm]
    _ ≤ C * γ * ∫⁻ x, ‖u x‖ₑ ^ ((γ : ℝ) - 1) * ‖fderiv ℝ u x id‖ₑ ∂μ := by
      rw [mul_assoc, ← lintegral_const_mul γ]
      · gcongr
        simp_rw [← mul_assoc]
        exact enorm_fderiv_norm_rpow_le (hu.differentiable one_ne_zero) h1γ
      dsimp [enorm]
      fun_prop
    _ ≤ C * γ * ((∫⁻ x, ‖u x‖ₑ ^ (p' : ℝ) ∂μ) ^ (1 / q) *
        (∫⁻ x, ‖fderiv ℝ u x id‖ₑ ^ (p : ℝ) ∂μ) ^ (1 / (p : ℝ))) := by
        gcongr
        convert!
          ENNReal.lintegral_mul_le_Lp_mul_Lq μ (.symm <| .conjExponent <| show 1 < (p : ℝ) from hp)
            ?_ ?_ using 5
        · simp [γ, n, q, ← ENNReal.rpow_mul, ← h3γ]
        · borelize F'
          fun_prop
        · fun_prop
    _ = C * γ * (∫⁻ x, ‖fderiv ℝ u x id‖ₑ ^ (p : ℝ) ∂μ) ^ (1 / (p : ℝ)) *
      (∫⁻ x, ‖u x‖ₑ ^ (p' : ℝ) ∂μ) ^ (1 / q) := by ring
  calc
    eLpNorm u p' μ
      = (∫⁻ x, ‖u x‖ₑ ^ (p' : ℝ) ∂μ) ^ (1 / (p' : ℝ)) := eLpNorm_nnreal_eq_lintegral hp'0
    _ ≤ C * γ * (∫⁻ x, ‖fderiv ℝ u x id‖ₑ ^ (p : ℝ) ∂μ) ^ (1 / (p : ℝ)) := by
      rwa [← h2q, ENNReal.rpow_sub _ _ h3u h4u, ENNReal.div_le_iff h5u h6u]
    _ = eLpNormLESNormFDerivOfEqInnerConst μ p
          (Nat.one_lt_cast.mp h1n) ((NNReal.coe_lt_coe.mpr h2p).ne) *
          eLpNorm (fun x ↦ fderiv ℝ u x id) (↑p) μ := by
      suffices (C : ℝ) * γ = eLpNormLESNormFDerivOfEqInnerConst μ p
          (Nat.one_lt_cast.mp h1n) ((NNReal.coe_lt_coe.mpr h2p).ne) by
        rw [eLpNorm_nnreal_eq_lintegral h0p]
        congr
        norm_cast at this ⊢
      simp_rw [eLpNormLESNormFDerivOfEqInnerConst, γ]
      refold_let n n' C
      rw [NNReal.coe_mul, NNReal.coe_mk, Real.coe_toNNReal', mul_eq_mul_left_iff, eq_comm,
        max_eq_left_iff]
      left
      positivity

variable (F) in
/-- The constant factor occurring in the conclusion of `eLpNorm_le_eLpNorm_fderiv_of_eq`.
It only depends on `E`, `F`, `μ` and `p`. -/
irreducible_def SNormLESNormFDerivOfEqConst [FiniteDimensional ℝ F] (p : ℝ)
    (hn : 1 < finrank ℝ E) (hp : p ≠ (finrank ℝ E : ℝ)) : ℝ≥0 :=
  let F' := EuclideanSpace ℝ <| Fin <| finrank ℝ F
  let e : F ≃L[ℝ] F' := toEuclidean
  ‖(e.symm : F' →L[ℝ] F)‖₊ * eLpNormLESNormFDerivOfEqInnerConst μ p hn hp *
    ‖(e : F →L[ℝ] F')‖₊

/-- The **Gagliardo-Nirenberg-Sobolev inequality**.  Let `u` be a continuously differentiable
compactly-supported function `u` on a normed space `E` of finite dimension `n`, equipped
with Haar measure, let `1 ≤ p < n` and let `p' > 0` satisfy `p'⁻¹ = p⁻¹ - n⁻¹`.
Then the `Lᵖ'` norm of `u` is bounded above by a constant times the `Lᵖ` norm of
the Fréchet derivative of `u`.

This is the version where the codomain of `u` is a finite-dimensional normed space.
-/
theorem eLpNorm_le_eLpNorm_fderiv_of_eq [FiniteDimensional ℝ F]
    {u : E → F} (hu : ContDiff ℝ 1 u) (h2u : HasCompactSupport u)
    {p p' : ℝ≥0} (hp : 1 ≤ p) (h2p : p < finrank ℝ E) (hp'0 : p' ≠ 0)
    (hp' : Checked.inv (p' : ℝ) (NNReal.coe_ne_zero.mpr hp'0).isUnit =
      Checked.inv (p : ℝ) (NNReal.coe_ne_zero.mpr (zero_lt_one.trans_le hp).ne').isUnit -
      Checked.inv (finrank ℝ E : ℝ)
        (Nat.cast_ne_zero.mpr (Nat.one_lt_cast.mp (hp.trans_lt h2p)).pos.ne').isUnit) :
    eLpNorm u p' μ ≤ SNormLESNormFDerivOfEqConst F μ p
      (Nat.one_lt_cast.mp (hp.trans_lt h2p)) ((NNReal.coe_lt_coe.mpr h2p).ne) *
      eLpNorm (fun x ↦ fderiv ℝ u x id) p μ := by
  /- Here we reduce the GNS-inequality with a Hilbert space as codomain to the case with a
  finite-dimensional normed space as codomain, by transferring the result along the equivalence
  `F ≃ ℝᵐ`. -/
  let F' := EuclideanSpace ℝ <| Fin <| finrank ℝ F
  let e : F ≃L[ℝ] F' := toEuclidean
  let C₁ : ℝ≥0 := ‖(e.symm : F' →L[ℝ] F)‖₊
  let hn : 1 < finrank ℝ E := Nat.one_lt_cast.mp (hp.trans_lt h2p)
  let hp_ne : (p : ℝ) ≠ finrank ℝ E := (NNReal.coe_lt_coe.mpr h2p).ne
  let C : ℝ≥0 := eLpNormLESNormFDerivOfEqInnerConst μ p hn hp_ne
  let C₂ : ℝ≥0 := ‖(e : F →L[ℝ] F')‖₊
  let v := e ∘ u
  have hv : ContDiff ℝ 1 v := e.contDiff.comp hu
  have h2v : HasCompactSupport v := h2u.comp_left e.map_zero
  have hvBound := eLpNorm_le_eLpNorm_fderiv_of_eq_inner μ hv h2v hp h2p hp'0 hp'
  have h4v : ∀ x, ‖fderiv ℝ v x id‖₊ ≤ C₂ * ‖fderiv ℝ u x id‖₊ := fun x ↦ calc
    ‖fderiv ℝ v x id‖₊
      = ‖(fderiv ℝ e (u x) id).comp (fderiv ℝ u x id)‖₊ := by
      rw [fderiv_comp x e.differentiableAt (hu.differentiable one_ne_zero x)]
    _ ≤ ‖fderiv ℝ e (u x) id‖₊ * ‖fderiv ℝ u x id‖₊ :=
      (fderiv ℝ e (u x) id).opNNNorm_comp_le (fderiv ℝ u x id)
    _ = C₂ * ‖fderiv ℝ u x id‖₊ := by rw [e.fderiv]
  calc eLpNorm u p' μ
      = eLpNorm (e.symm ∘ v) p' μ := by simp_rw [v, Function.comp_def, e.symm_apply_apply]
    _ ≤ C₁ • eLpNorm v p' μ := by
      apply eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul
      exact Eventually.of_forall (fun x ↦ (e.symm : F' →L[ℝ] F).le_opNNNorm _)
    _ = C₁ * eLpNorm v p' μ := rfl
    _ ≤ C₁ * C * eLpNorm (fun x ↦ fderiv ℝ v x id) p μ := by
      rw [mul_assoc]
      exact mul_le_mul_right hvBound _
    _ ≤ C₁ * C * (C₂ * eLpNorm (fun x ↦ fderiv ℝ u x id) p μ) := by
      exact mul_le_mul_right
        (eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul (Eventually.of_forall h4v) p) _
    _ = SNormLESNormFDerivOfEqConst F μ p hn hp_ne * eLpNorm (fun x ↦ fderiv ℝ u x id) p μ := by
      simp only [SNormLESNormFDerivOfEqConst, C₂, C₁, C, e, ENNReal.coe_mul, mul_assoc]

variable (F) in
/-- The constant factor occurring in the conclusion of `eLpNorm_le_eLpNorm_fderiv_of_le`.
It only depends on `E`, `F`, `μ`, `s`, `p` and `q`. -/
irreducible_def eLpNormLESNormFDerivOfLeConst [FiniteDimensional ℝ F] (s : Set E) (p q : ℝ≥0)
    (hp0 : p ≠ 0) (hn : 1 < finrank ℝ E) (h2p : p < finrank ℝ E) (hq0 : q ≠ 0) : ℝ≥0 :=
  (μ s).toNNReal ^ (Checked.inv (q : ℝ) (NNReal.coe_ne_zero.mpr hq0).isUnit -
    (Checked.inv (p : ℝ) (NNReal.coe_ne_zero.mpr hp0).isUnit -
      Checked.inv (finrank ℝ E : ℝ) (Nat.cast_ne_zero.mpr hn.pos.ne').isUnit)) *
    SNormLESNormFDerivOfEqConst F μ p hn ((NNReal.coe_lt_coe.mpr h2p).ne)

/-- The **Gagliardo-Nirenberg-Sobolev inequality**.  Let `u` be a continuously differentiable
function `u` supported in a bounded set `s` in a normed space `E` of finite dimension
`n`, equipped with Haar measure, and let `1 ≤ p < n` and `0 < q ≤ (p⁻¹ - n⁻¹)⁻¹`.
Then the `L^q` norm of `u` is bounded above by a constant times the `Lᵖ` norm of
the Fréchet derivative of `u`.

Note: The codomain of `u` needs to be a finite-dimensional normed space.
-/
theorem eLpNorm_le_eLpNorm_fderiv_of_le [FiniteDimensional ℝ F]
    {u : E → F} {s : Set E} (hu : ContDiff ℝ 1 u) (h2u : u.support ⊆ s)
    {p q : ℝ≥0} (hp : 1 ≤ p) (h2p : p < finrank ℝ E) (hq0 : q ≠ 0)
    (hpq : Checked.inv (p : ℝ) (NNReal.coe_ne_zero.mpr (zero_lt_one.trans_le hp).ne').isUnit -
      Checked.inv (finrank ℝ E : ℝ)
        (Nat.cast_ne_zero.mpr (Nat.one_lt_cast.mp (hp.trans_lt h2p)).pos.ne').isUnit ≤
      Checked.inv (q : ℝ) (NNReal.coe_ne_zero.mpr hq0).isUnit)
    (hs : Bornology.IsBounded s) :
    eLpNorm u q μ ≤ eLpNormLESNormFDerivOfLeConst F μ s p q
      (zero_lt_one.trans_le hp).ne' (Nat.one_lt_cast.mp (hp.trans_lt h2p)) h2p hq0 *
      eLpNorm (fun x ↦ fderiv ℝ u x id) p μ := by
  have hp₀ : 0 < p := zero_lt_one.trans_le hp
  have hn : 1 < finrank ℝ E := Nat.one_lt_cast.mp (hp.trans_lt h2p)
  have hn₀ : (0 : ℝ≥0) < finrank ℝ E := Nat.cast_pos.mpr hn.pos
  have hlt : (finrank ℝ E : ℝ≥0)⁻¹ < p⁻¹ := (inv_lt_inv₀ hn₀ hp₀).mpr h2p
  have hpos : 0 < p⁻¹ - (finrank ℝ E : ℝ≥0)⁻¹ := tsub_pos_of_lt hlt
  let p' : ℝ≥0 := Checked.inv (p⁻¹ - (finrank ℝ E : ℝ≥0)⁻¹) hpos.ne'.isUnit
  have hp'₀ : 0 < p' := inv_pos.mpr hpos
  have hp' : (p' : ℝ)⁻¹ = (p : ℝ)⁻¹ - (finrank ℝ E : ℝ)⁻¹ := by
    rw [← NNReal.coe_inv p' (hr := hp'₀.ne'.isUnit)]
    simp only [p', inv_inv₀, NNReal.coe_sub hlt.le, NNReal.coe_inv, NNReal.coe_natCast]
  have hqp' : (q : ℝ≥0∞) ≤ p' := by
    have H : (p' : ℝ)⁻¹ ≤ (q : ℝ)⁻¹ := hp'.trans_le hpq
    exact_mod_cast (inv_le_inv₀ (NNReal.coe_pos.mpr hp'₀)
      (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hq0))).mp H
  have hqR : IsUnit (q : ℝ) := (NNReal.coe_ne_zero.mpr hq0).isUnit
  have hp'R : IsUnit (p' : ℝ) := (NNReal.coe_ne_zero.mpr hp'₀.ne').isUnit
  set t := (μ s).toNNReal ^ (1 / (q : ℝ) - 1 / (p' : ℝ))
  let C := SNormLESNormFDerivOfEqConst F μ p hn ((NNReal.coe_lt_coe.mpr h2p).ne)
  calc eLpNorm u q μ
      = eLpNorm u q (μ.restrict s) := by rw [eLpNorm_restrict_eq_of_support_subset h2u]
    _ ≤ eLpNorm u p' (μ.restrict s) * t := by
        convert! eLpNorm_le_eLpNorm_mul_rpow_measure_univ hqp' hu.continuous.aestronglyMeasurable
        rw [ENNReal.coe_rpow_of_nonneg]
        · simp only [ENNReal.coe_toNNReal hs.measure_lt_top.ne, Measure.restrict_apply_univ,
            one_div₀, ENNReal.toReal_inv (q : ℝ≥0∞) (ha := hqR),
            ENNReal.toReal_inv (p' : ℝ≥0∞) (ha := hp'R), ENNReal.coe_toReal]
        · simpa only [one_div₀, hp', sub_nonneg] using hpq
    _ = eLpNorm u p' μ * t := by rw [eLpNorm_restrict_eq_of_support_subset h2u]
    _ ≤ (C * eLpNorm (fun x ↦ fderiv ℝ u x id) p μ) * t := by
        have h2u' : HasCompactSupport u := by
          apply HasCompactSupport.of_support_subset_isCompact hs.isCompact_closure
          exact h2u.trans subset_closure
        exact mul_le_mul_left (eLpNorm_le_eLpNorm_fderiv_of_eq μ hu h2u' hp h2p hp'₀.ne' hp') _
    _ = eLpNormLESNormFDerivOfLeConst F μ s p q hp₀.ne' hn h2p hq0 *
        eLpNorm (fun x ↦ fderiv ℝ u x id) p μ := by
      simp_rw [eLpNormLESNormFDerivOfLeConst, ENNReal.coe_mul, t, one_div₀, hp']; ring

/-- The **Gagliardo-Nirenberg-Sobolev inequality**.  Let `u` be a continuously differentiable
function `u` supported in a bounded set `s` in a normed space `E` of finite dimension
`n`, equipped with Haar measure, and let `1 ≤ p < n`.
Then the `Lᵖ` norm of `u` is bounded above by a constant times the `Lᵖ` norm of
the Fréchet derivative of `u`.

Note: The codomain of `u` needs to be a finite-dimensional normed space.
-/
theorem eLpNorm_le_eLpNorm_fderiv [FiniteDimensional ℝ F]
    {u : E → F} {s : Set E} (hu : ContDiff ℝ 1 u) (h2u : u.support ⊆ s)
    {p : ℝ≥0} (hp : 1 ≤ p) (h2p : p < finrank ℝ E) (hs : Bornology.IsBounded s) :
    eLpNorm u p μ ≤ eLpNormLESNormFDerivOfLeConst F μ s p p
      (zero_lt_one.trans_le hp).ne' (Nat.one_lt_cast.mp (hp.trans_lt h2p)) h2p
      (zero_lt_one.trans_le hp).ne' * eLpNorm (fun x ↦ fderiv ℝ u x id) p μ := by
  refine eLpNorm_le_eLpNorm_fderiv_of_le μ hu h2u hp h2p (zero_lt_one.trans_le hp).ne' ?_ hs
  exact sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg _))

end MeasureTheory
