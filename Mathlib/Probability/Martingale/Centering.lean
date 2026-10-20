/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Martingale.Basic

/-!
# Centering lemma for stochastic processes

Any `ℕ`-indexed stochastic process `f` which is strongly adapted to a filtration `ℱ` and integrable
can be written as the sum of a martingale and a predictable process, when the measure `μ` is
σ-finite on the filtration. This result is also known as **Doob's decomposition theorem**. The
predictable part at time `n` is the sum `∑ i ∈ Finset.range n, μ[f (i + 1) - f i | ℱ i]` of the
conditional expectations of the increments of `f`, and the martingale part is the difference of `f`
and the predictable part.

A conditional expectation is determined only up to almost everywhere equality, and so is the
decomposition, while a process is a function. The two parts are therefore built from a process `g`
such that each `g i` is a conditional expectation of the increment `f (i + 1) - f i` given `ℱ i`
(`MeasureTheory.IsCondExp`), and `g` is a parameter of the definitions and of the theorems. Two
such choices of `g` give parts that agree almost everywhere at each time
(`MeasureTheory.predictablePart_ae_eq`, `MeasureTheory.martingalePart_ae_eq`). Strongly adapted
choices exist when `μ` is σ-finite on the filtration
(`MeasureTheory.exists_stronglyAdapted_isCondExp_increment`); once `g` is given, no σ-finiteness is
needed.

## Main definitions

* `MeasureTheory.predictablePart g`: the partial sums `fun n ↦ ∑ i ∈ Finset.range n, g i` of `g`,
  the predictable part of the decomposition built from `g`.
* `MeasureTheory.martingalePart f g`: the martingale part `fun n ↦ f n - predictablePart g n`, so
  that `f = martingalePart f g + predictablePart g`.

## Main statements

* `MeasureTheory.stronglyAdapted_predictablePart`: `fun n ↦ predictablePart g (n + 1)` is strongly
  adapted for a strongly adapted `g`. That is, `predictablePart g` is predictable
  (`MeasureTheory.isStronglyPredictable_predictablePart`).
* `MeasureTheory.martingale_martingalePart`: `martingalePart f g` is a martingale.
* `MeasureTheory.predictablePart_ae_eq`: the predictable part does not depend, up to almost
  everywhere equality, on the choice of `g`.
* `MeasureTheory.predictablePart_add_ae_eq`, `MeasureTheory.martingalePart_add_ae_eq`: the
  decomposition is unique: for a martingale `f` and a predictable integrable process `u` vanishing
  at `0`, the predictable and martingale parts of `f + u` are almost everywhere `u` and `f`.

-/

@[expose] public section


open Filter

open scoped NNReal ENNReal MeasureTheory ProbabilityTheory

namespace MeasureTheory

variable {Ω E : Type*} {m0 : SigmaAlgebra Ω} {μ : Measure Ω} [NormedAddCommGroup E]
  {f f' g g' : ℕ → Ω → E} {ℱ : Filtration ℕ m0}

/-- The partial sums `predictablePart g n = ∑ i ∈ Finset.range n, g i` of a process `g`. When each
`g i` is a conditional expectation of the increment `f (i + 1) - f i` of a process `f` given `ℱ i`,
this is the predictable part of the Doob decomposition of `f` with respect to the filtration `ℱ`;
it is predictable for a strongly adapted `g`
(`MeasureTheory.isStronglyPredictable_predictablePart`). A conditional expectation is determined
only up to almost everywhere equality, so `g` is a parameter rather than a choice made here. See
`martingalePart` for the martingale part. -/
def predictablePart (g : ℕ → Ω → E) : ℕ → Ω → E := fun n ↦ ∑ i ∈ Finset.range n, g i

/-- The difference `martingalePart f g n = f n - predictablePart g n`. When each `g i` is a
conditional expectation of the increment `f (i + 1) - f i` given `ℱ i`, this is the martingale part
of the Doob decomposition of `f` with respect to the filtration `ℱ`; it is a martingale for a
strongly adapted integrable `f` and a strongly adapted `g`
(`MeasureTheory.martingale_martingalePart`). See `predictablePart` for the predictable part. -/
def martingalePart (f g : ℕ → Ω → E) : ℕ → Ω → E := fun n ↦ f n - predictablePart g n

@[simp]
theorem predictablePart_zero : predictablePart g 0 = 0 := by
  simp [predictablePart]

theorem predictablePart_add_one (n : ℕ) :
    predictablePart g (n + 1) = predictablePart g n + g n := by
  simp [predictablePart, Finset.sum_range_succ]

theorem predictablePart_add :
    predictablePart (g + g') = predictablePart g + predictablePart g' := by
  ext1 n
  simp [predictablePart, Finset.sum_add_distrib]

@[simp]
lemma martingalePart_zero : martingalePart f g 0 = f 0 := by
  simp [martingalePart]

lemma martingalePart_add :
    martingalePart (f + f') (g + g') = martingalePart f g + martingalePart f' g' := by
  ext1 n
  simp only [martingalePart, predictablePart_add, Pi.add_apply]
  abel

theorem martingalePart_add_predictablePart (f g : ℕ → Ω → E) :
    martingalePart f g + predictablePart g = f :=
  sub_add_cancel _ _

theorem martingalePart_eq_sum :
    martingalePart f g = fun n ↦ f 0 + ∑ i ∈ Finset.range n, (f (i + 1) - f i - g i) := by
  unfold martingalePart predictablePart
  ext1 n
  rw [Finset.eq_sum_range_sub f n, ← add_sub, ← Finset.sum_sub_distrib]

/-- For a strongly adapted `g`, `predictablePart g (n + 1)` is `ℱ n`-strongly measurable: the
predictable part is predictable. -/
theorem stronglyAdapted_predictablePart (hg : StronglyAdapted ℱ g) :
    StronglyAdapted ℱ fun n ↦ predictablePart g (n + 1) :=
  fun _ ↦ Finset.stronglyMeasurable_sum _ fun _ hi ↦
    hg.stronglyMeasurable_le (Finset.mem_range_succ_iff.mp hi)

/-- The predictable part built from a strongly adapted `g` is a predictable process. -/
lemma isStronglyPredictable_predictablePart (hg : StronglyAdapted ℱ g) :
    IsStronglyPredictable ℱ (predictablePart g) :=
  IsStronglyPredictable.of_measurable_add_one
    (by rw [predictablePart_zero]; exact stronglyMeasurable_zero)
    (stronglyAdapted_predictablePart hg)

theorem stronglyAdapted_predictablePart' (hg : StronglyAdapted ℱ g) :
    StronglyAdapted ℱ (predictablePart g) :=
  fun _ ↦ Finset.stronglyMeasurable_sum _ fun _ hi ↦
    hg.stronglyMeasurable_le (Finset.mem_range_le hi)

theorem stronglyAdapted_martingalePart (hf : StronglyAdapted ℱ f) (hg : StronglyAdapted ℱ g) :
    StronglyAdapted ℱ (martingalePart f g) :=
  hf.sub (stronglyAdapted_predictablePart' hg)

theorem integrable_predictablePart (hg_int : ∀ i, Integrable (g i) μ) (n : ℕ) :
    Integrable (predictablePart g n) μ :=
  integrable_finsetSum' _ fun i _ ↦ hg_int i

theorem integrable_martingalePart (hf_int : ∀ n, Integrable (f n) μ)
    (hg_int : ∀ i, Integrable (g i) μ) (n : ℕ) : Integrable (martingalePart f g n) μ :=
  (hf_int n).sub (integrable_predictablePart hg_int n)

variable [NormedSpace ℝ E]

theorem predictablePart_smul (c : ℝ) : predictablePart (c • g) = c • predictablePart g := by
  ext1 n
  simp [predictablePart, Finset.smul_sum]

lemma martingalePart_smul (c : ℝ) : martingalePart (c • f) (c • g) = c • martingalePart f g := by
  ext1 n
  simp [martingalePart, predictablePart_smul, smul_sub]

variable [CompleteSpace E]

/-- For a σ-finite filtration, the increments `f (i + 1) - f i` of an integrable process `f` have
strongly adapted conditional expectations given `ℱ i`, from which its Doob decomposition is built
(`MeasureTheory.martingale_martingalePart`). -/
theorem exists_stronglyAdapted_isCondExp_increment [SigmaFiniteFiltration μ ℱ]
    (hf_int : ∀ n, Integrable (f n) μ) :
    ∃ g : ℕ → Ω → E, StronglyAdapted ℱ g ∧ ∀ i, IsCondExp (ℱ i) μ (f (i + 1) - f i) (g i) := by
  choose g hgm hg using fun i ↦
    exists_stronglyMeasurable_isCondExp (μ := μ) (ℱ.le i) ((hf_int (i + 1)).sub (hf_int i))
  exact ⟨g, hgm, hg⟩

/-- If `g` and `g'` are conditional expectations of the increments of integrable processes `f` and
`f'`, then `g + g'` are conditional expectations of the increments of `f + f'`. The decomposition
of `f + f'` built from `g + g'` is the sum of those of `f` and `f'`
(`MeasureTheory.predictablePart_add`, `MeasureTheory.martingalePart_add`). -/
theorem isCondExp_increment_add (hf_int : ∀ n, Integrable (f n) μ)
    (hf'_int : ∀ n, Integrable (f' n) μ) (hg : ∀ i, IsCondExp (ℱ i) μ (f (i + 1) - f i) (g i))
    (hg' : ∀ i, IsCondExp (ℱ i) μ (f' (i + 1) - f' i) (g' i)) (i : ℕ) :
    IsCondExp (ℱ i) μ ((f + f') (i + 1) - (f + f') i) ((g + g') i) := by
  have h : (f + f') (i + 1) - (f + f') i = f (i + 1) - f i + (f' (i + 1) - f' i) := by
    simp only [Pi.add_apply]
    abel
  rw [h, Pi.add_apply]
  exact (hg i).add (hg' i) ((hf_int _).sub (hf_int _)) ((hf'_int _).sub (hf'_int _))

/-- If `g` are conditional expectations of the increments of a process `f`, then `c • g` are
conditional expectations of the increments of `c • f`. The decomposition of `c • f` built from
`c • g` is `c` times that of `f` (`MeasureTheory.predictablePart_smul`,
`MeasureTheory.martingalePart_smul`). -/
theorem isCondExp_increment_smul (c : ℝ) (hg : ∀ i, IsCondExp (ℱ i) μ (f (i + 1) - f i) (g i))
    (i : ℕ) : IsCondExp (ℱ i) μ ((c • f) (i + 1) - (c • f) i) ((c • g) i) := by
  simp only [Pi.smul_apply, ← smul_sub]
  exact (hg i).smul c

/-- The predictable part does not depend, up to almost everywhere equality, on the conditional
expectations of the increments that it is built from. -/
theorem predictablePart_ae_eq (hf_int : ∀ n, Integrable (f n) μ)
    (hg : ∀ i, IsCondExp (ℱ i) μ (f (i + 1) - f i) (g i))
    (hg' : ∀ i, IsCondExp (ℱ i) μ (f (i + 1) - f i) (g' i)) (n : ℕ) :
    predictablePart g n =ᵐ[μ] predictablePart g' n :=
  eventuallyEq_sum fun i _ ↦ (hg i).ae_eq (ℱ.le i) ((hf_int _).sub (hf_int _)) (hg' i)

/-- The martingale part does not depend, up to almost everywhere equality, on the conditional
expectations of the increments that it is built from. -/
theorem martingalePart_ae_eq (hf_int : ∀ n, Integrable (f n) μ)
    (hg : ∀ i, IsCondExp (ℱ i) μ (f (i + 1) - f i) (g i))
    (hg' : ∀ i, IsCondExp (ℱ i) μ (f (i + 1) - f i) (g' i)) (n : ℕ) :
    martingalePart f g n =ᵐ[μ] martingalePart f g' n := by
  filter_upwards [predictablePart_ae_eq hf_int hg hg' n] with ω hω
  simp [martingalePart, hω]

/-- **Doob's decomposition theorem**: the martingale part of a strongly adapted integrable process
`f`, built from strongly adapted conditional expectations `g i` of its increments `f (i + 1) - f i`
given `ℱ i`, is a martingale. Such `g` exist for a σ-finite filtration
(`MeasureTheory.exists_stronglyAdapted_isCondExp_increment`). -/
theorem martingale_martingalePart
    (hf : StronglyAdapted ℱ f) (hf_int : ∀ n, Integrable (f n) μ) (hgm : StronglyAdapted ℱ g)
    (hg : ∀ i, IsCondExp (ℱ i) μ (f (i + 1) - f i) (g i)) :
    Martingale (martingalePart f g) ℱ μ := by
  have hg_int (i : ℕ) : Integrable (g i) μ := (hg i).integrable ((hf_int _).sub (hf_int _))
  refine martingale_of_isCondExp_sub_eq_zero_nat (stronglyAdapted_martingalePart hf hgm)
    (integrable_martingalePart hf_int hg_int) fun i ↦ ?_
  have h : martingalePart f g (i + 1) - martingalePart f g i = f (i + 1) - f i - g i := by
    simp only [martingalePart, predictablePart_add_one]
    abel
  have h' := (hg i).sub (isCondExp_self (hgm i).aestronglyMeasurable) ((hf_int _).sub (hf_int _))
    (hg_int i)
  rw [sub_self (g i)] at h'
  rwa [h]

/-- The increments of a martingale have conditional expectation zero. -/
private theorem Martingale.isCondExp_increment (hf : Martingale f ℱ μ) (i : ℕ) :
    IsCondExp (ℱ i) μ (f (i + 1) - f i) 0 := by
  have h := (hf.isCondExp i.le_succ).sub
    (isCondExp_self (hf.stronglyMeasurable i).aestronglyMeasurable) (hf.integrable _)
    (hf.integrable _)
  rwa [sub_self (f i)] at h

/-- The predictable part of a martingale vanishes almost everywhere. -/
lemma Martingale.predictablePart_eq_zero (hf : Martingale f ℱ μ)
    (hg : ∀ i, IsCondExp (ℱ i) μ (f (i + 1) - f i) (g i)) (n : ℕ) :
    predictablePart g n =ᵐ[μ] 0 := by
  rw [predictablePart, ← Finset.sum_const_zero (s := Finset.range n)]
  exact eventuallyEq_sum fun i _ ↦ (hg i).ae_eq (ℱ.le i)
    ((hf.integrable _).sub (hf.integrable _)) (Martingale.isCondExp_increment hf i)

/-- The martingale part of a martingale is almost everywhere the martingale. -/
lemma Martingale.martingalePart_eq (hf : Martingale f ℱ μ)
    (hg : ∀ i, IsCondExp (ℱ i) μ (f (i + 1) - f i) (g i)) (n : ℕ) :
    martingalePart f g n =ᵐ[μ] f n := by
  filter_upwards [hf.predictablePart_eq_zero hg n] with ω hω
  simp [martingalePart, hω]

/-- The predictable part of a submartingale is almost everywhere monotone. -/
lemma Submartingale.monotone_predictablePart [PartialOrder E] [IsOrderedAddMonoid E]
    (hf : Submartingale f ℱ μ) (hg : ∀ i, IsCondExp (ℱ i) μ (f (i + 1) - f i) (g i)) :
    ∀ᵐ ω ∂μ, Monotone (predictablePart g · ω) := by
  filter_upwards [ae_all_iff.2 fun n ↦ hf.isCondExp_sub_nonneg n.le_succ (hg n)] with ω hω
  refine monotone_nat_of_le_succ fun n ↦ ?_
  rw [predictablePart_add_one, Pi.add_apply]
  exact le_add_of_nonneg_right (hω n)

/-- The predictable part of a submartingale is almost everywhere nonnegative. -/
lemma Submartingale.predictablePart_nonneg [PartialOrder E] [IsOrderedAddMonoid E]
    (hf : Submartingale f ℱ μ) (hg : ∀ i, IsCondExp (ℱ i) μ (f (i + 1) - f i) (g i)) :
    ∀ᵐ ω ∂μ, ∀ n, 0 ≤ predictablePart g n ω := by
  filter_upwards [hf.monotone_predictablePart hg] with ω hω n
  simpa [predictablePart_zero] using hω (Nat.zero_le n)

/-- The predictable part of a predictable integrable process `f` is almost everywhere `f - f 0`. -/
lemma IsStronglyPredictable.predictablePart_eq (hf : IsStronglyPredictable ℱ f)
    (hf_int : ∀ n, Integrable (f n) μ) (hg : ∀ i, IsCondExp (ℱ i) μ (f (i + 1) - f i) (g i))
    (n : ℕ) : predictablePart g n =ᵐ[μ] f n - f 0 := by
  simp only [predictablePart, ← Finset.sum_range_sub]
  exact eventuallyEq_sum fun i _ ↦ (hg i).ae_eq (ℱ.le i) ((hf_int _).sub (hf_int _))
    (isCondExp_self ((hf.measurable_add_one i).sub (hf.stronglyAdapted i)).aestronglyMeasurable)

/-- The martingale part of a predictable integrable process `f` is almost everywhere `f 0`. -/
lemma IsStronglyPredictable.martingalePart_eq (hf : IsStronglyPredictable ℱ f)
    (hf_int : ∀ n, Integrable (f n) μ) (hg : ∀ i, IsCondExp (ℱ i) μ (f (i + 1) - f i) (g i))
    (n : ℕ) : martingalePart f g n =ᵐ[μ] f 0 := by
  filter_upwards [hf.predictablePart_eq hf_int hg n] with ω hω
  simp [martingalePart, hω]

-- The following two lemmas demonstrate the essential uniqueness of the decomposition
/-- For a martingale `f` and a predictable integrable process `u` with `u 0 = 0`, the predictable
part of `f + u`, built from any conditional expectations of its increments, is almost everywhere
`u`. -/
theorem predictablePart_add_ae_eq {u : ℕ → Ω → E} (hf : Martingale f ℱ μ)
    (hu : StronglyAdapted ℱ fun n ↦ u (n + 1)) (hu0 : u 0 = 0)
    (hu_int : ∀ n, Integrable (u n) μ)
    (hg : ∀ i, IsCondExp (ℱ i) μ ((f + u) (i + 1) - (f + u) i) (g i)) (n : ℕ) :
    predictablePart g n =ᵐ[μ] u n := by
  have hu_pred : IsStronglyPredictable ℱ u :=
    .of_measurable_add_one (hu0 ▸ stronglyMeasurable_zero) hu
  have hv (i : ℕ) : IsCondExp (ℱ i) μ ((f + u) (i + 1) - (f + u) i) (u (i + 1) - u i) := by
    have h : (f + u) (i + 1) - (f + u) i = f (i + 1) - f i + (u (i + 1) - u i) := by
      simp only [Pi.add_apply]
      abel
    have h' := (Martingale.isCondExp_increment hf i).add
      (isCondExp_self ((hu i).sub (hu_pred.stronglyAdapted i)).aestronglyMeasurable)
      ((hf.integrable _).sub (hf.integrable _)) ((hu_int _).sub (hu_int _))
    rw [zero_add (u (i + 1) - u i)] at h'
    rwa [h]
  have h_sum : predictablePart (fun i ↦ u (i + 1) - u i) n = u n := by
    simp only [predictablePart, Finset.sum_range_sub, hu0, sub_zero]
  filter_upwards [predictablePart_ae_eq (fun n ↦ (hf.integrable n).add (hu_int n)) hg hv n]
    with ω hω
  rw [hω, h_sum]

/-- For a martingale `f` and a predictable integrable process `u` with `u 0 = 0`, the martingale
part of `f + u`, built from any conditional expectations of its increments, is almost everywhere
`f`. -/
theorem martingalePart_add_ae_eq {u : ℕ → Ω → E} (hf : Martingale f ℱ μ)
    (hu : StronglyAdapted ℱ fun n ↦ u (n + 1)) (hu0 : u 0 = 0)
    (hu_int : ∀ n, Integrable (u n) μ)
    (hg : ∀ i, IsCondExp (ℱ i) μ ((f + u) (i + 1) - (f + u) i) (g i)) (n : ℕ) :
    martingalePart (f + u) g n =ᵐ[μ] f n := by
  filter_upwards [predictablePart_add_ae_eq hf hu hu0 hu_int hg n] with ω hω
  simp [martingalePart, hω]

section Difference

/-- If the increments of an integrable process `f` are almost everywhere bounded in norm by `R`,
then so are those of its predictable part. -/
theorem predictablePart_bdd_difference {R : ℝ} (hf_int : ∀ n, Integrable (f n) μ)
    (hg : ∀ i, IsCondExp (ℱ i) μ (f (i + 1) - f i) (g i))
    (hbdd : ∀ᵐ ω ∂μ, ∀ i, ‖f (i + 1) ω - f i ω‖ ≤ R) :
    ∀ᵐ ω ∂μ, ∀ i, ‖predictablePart g (i + 1) ω - predictablePart g i ω‖ ≤ R := by
  simp_rw [predictablePart_add_one, Pi.add_apply, add_sub_cancel_left]
  exact ae_all_iff.2 fun i ↦
    (hg i).ae_norm_le_const (ℱ.le i) ((hf_int _).sub (hf_int _)) (ae_all_iff.1 hbdd i)

/-- If the increments of an integrable process `f` are almost everywhere bounded in norm by `R`,
then those of its martingale part are bounded by `2 * R`. -/
theorem martingalePart_bdd_difference {R : ℝ} (hf_int : ∀ n, Integrable (f n) μ)
    (hg : ∀ i, IsCondExp (ℱ i) μ (f (i + 1) - f i) (g i))
    (hbdd : ∀ᵐ ω ∂μ, ∀ i, ‖f (i + 1) ω - f i ω‖ ≤ R) :
    ∀ᵐ ω ∂μ, ∀ i, ‖martingalePart f g (i + 1) ω - martingalePart f g i ω‖ ≤ 2 * R := by
  filter_upwards [hbdd, predictablePart_bdd_difference hf_int hg hbdd] with ω hω₁ hω₂ i
  simpa [two_mul, martingalePart, sub_sub_sub_comm] using
    (norm_sub_le _ _).trans (add_le_add (hω₁ i) (hω₂ i))

end Difference

end MeasureTheory
