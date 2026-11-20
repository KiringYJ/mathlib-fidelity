/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn

/-!
# Weierstrass function: a function that is continuous everywhere but differentiable nowhere

This file defines the real-valued Weierstrass function as

$$f(x) = \sum_{n=0}^\infty a^n \cos (b^n\pi x)$$

and prove that it is continuous everywhere but differentiable nowhere for $a \in (0, 1)$, and
a positive odd integer $b$ such that

$$ab > 1 + \frac{3}{2}\pi$$

which is the original bound given by Karl Weierstrass. There is a better bound $ab \ge 1$ given by
[G. H. Hardy][hardyweierstrass] with a less elementary proof, which is not implemented here.

## References

* [Weierstrass, Karl, *Über continuirliche Functionen eines reellen Arguments, die für keinen Werth
  des letzeren einen bestimmten Differentialquotienten besitzen*][weierstrass1895]
* [G. H. Hardy, *Weierstrass's Non-Differentiable Function*][hardyweierstrass]

-/

@[expose] public section

namespace NowhereDifferentiable
open Real Topology Filter

/-!
### Definition

For real parameter $a$ and $b$, define the Weierstrass function as
$$f(x) = \sum_{n=0}^\infty a^n \cos (b^n\pi x)$$
-/

noncomputable def weierstrass (a b x : ℝ) := ∑' n, a ^ n * cos (b ^ n * π * x)

/-!
### Continuity

We show that for $a \in (0, 1)$, the summation in the definition is uniformly convergent,
each term is uniformly continuous, and therefore Weierstrass function is uniformly continuous.
-/

theorem hasSumUniformlyOn_weierstrass {a : ℝ} (ha : a ∈ Set.Ioo 0 1) (b : ℝ) :
    HasSumUniformlyOn (fun n x ↦ a ^ n * cos (b ^ n * π * x)) (weierstrass a b) Set.univ := by
  refine .of_norm_le_summable (summable_geometric_of_abs_lt_one (r := |a|) (by grind)) ?_
  intro n x _
  simpa using mul_le_mul_of_nonneg_left (abs_cos_le_one (b ^ n * π * x)) (abs_nonneg (a ^ n))

theorem tendstoUniformly_weierstrass {a : ℝ} (ha : a ∈ Set.Ioo 0 1) (b : ℝ) :
    TendstoUniformly (fun s x ↦ ∑ n ∈ s, a ^ n * cos (b ^ n * π * x))
    (weierstrass a b) atTop := by
  rw [← tendstoUniformlyOn_univ]
  exact (hasSumUniformlyOn_weierstrass ha b).tendstoUniformlyOn

theorem summable_weierstrass {a : ℝ} (ha : a ∈ Set.Ioo 0 1) (b x : ℝ) :
    Summable fun n ↦ a ^ n * cos (b ^ n * π * x) :=
  (hasSumUniformlyOn_weierstrass ha b).summableUniformlyOn.summable (Set.mem_univ x)

theorem uniformContinuous_weierstrass {a : ℝ} (ha : a ∈ Set.Ioo 0 1) (b : ℝ) :
    UniformContinuous (weierstrass a b) := by
  apply (tendstoUniformly_weierstrass ha b).uniformContinuous
  refine .of_forall fun s ↦ s.uniformContinuous_sum fun n _ ↦ ?_
  exact (lipschitzWith_cos.uniformContinuous.comp (uniformContinuous_id.const_mul' _)).const_mul' _

/-!
### Non-differentiability

To show that Weierstrass function $f(x)$ is not differentiable at any $x$, we choose a sequence
$\{x_m\}$ such that, as $m\to\infty$
- $\{x_m\}$ converges to $x$
- The slope $(f(x_m) - f(x)) / (x_m - x)$ grows unbounded,
   which means the derivative $f'(x)$ cannot exist.
-/

/-- The approximating sequence has term $x_m = \lfloor b^m x + 3/2 \rfloor / b^m$ when $b^m ≠ 0$. -/
noncomputable
abbrev seq (b x : ℝ) (m : ℕ) (hb : IsUnit (b ^ m) := by checked_unit) : ℝ :=
  Checked.div (⌊b ^ m * x + 3 / 2⌋ : ℝ) (b ^ m) hb

theorem seq_mul_pow {b : ℝ} (hb : b ≠ 0) (x : ℝ) (m : ℕ) :
    seq b x m * b ^ m = ⌊b ^ m * x + 2⁻¹⌋ + 1 := by
  rw [seq, div_mul_cancel₀]
  norm_cast
  rw [← Int.floor_add_one, add_assoc]
  norm_num

/-!
Show that $x_m \in (x, x + 3 / (2b^m)]$, and it tends to $x$ by squeeze theorem.
-/

theorem lt_seq {b : ℝ} (hb : 0 < b) (x : ℝ) (m : ℕ) : x < seq b x m := by
  rw [seq, lt_div_iff₀' (pow_pos hb m)]
  linarith [Int.sub_one_lt_floor (b ^ m * x + 3 / 2)]

theorem le_seq {b : ℝ} (hb : 0 < b) (x : ℝ) (m : ℕ) : x ≤ seq b x m := (lt_seq hb x m).le

theorem seq_le {b : ℝ} (hb : 0 < b) (x : ℝ) (m : ℕ) : seq b x m ≤ x + (3 / 2) * b⁻¹ ^ m := by
  rw [seq, div_le_iff₀ (pow_pos hb m), add_mul, mul_assoc, inv_pow₀,
    inv_mul_cancel₀, mul_one, mul_comm x]
  exact Int.floor_le _

theorem tendsto_seq {b : ℝ} (hb : 1 < b) (x : ℝ) :
    Tendsto (fun m ↦ seq b x m ((zero_lt_one.trans hb).ne'.isUnit.pow m)) atTop (𝓝 x) := by
  have hb0 : 0 < b := lt_trans (by norm_num) hb
  refine tendsto_const_nhds.squeeze ?_ (le_seq hb0 x) (seq_le hb0 x)
  rw [show 𝓝 x = 𝓝 (x + (3 / 2) * 0) by simp]
  refine tendsto_const_nhds.add (Tendsto.const_mul _ ?_)
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by simpa [inv_lt_one₀ hb0])

theorem tendsto_seq_sub_inv {b : ℝ} (hb : 1 < b) (x : ℝ) :
    Tendsto (fun m ↦ Checked.inv (seq b x m ((zero_lt_one.trans hb).ne'.isUnit.pow m) - x)
      (sub_pos.mpr (lt_seq (zero_lt_one.trans hb) x m)).ne'.isUnit) atTop atTop := by
  refine .fun_inv_tendsto_nhdsGT_zero <| tendsto_nhdsWithin_iff.mpr ⟨?_, .of_forall ?_⟩
  · simpa using (tendsto_seq hb x |>.sub_const x)
  · simpa using lt_seq (zero_lt_one.trans hb) x

/-!
To estimate the slope $(f(x_m) - f(x)) / (x_m - x)$, we break the infinite sum in
$f(x_m) - f(x)$ into two parts $f(x_m) - f(x) = A + B$, where

$$ A = ∑_{n=0}^{m-1} a^n (\cos(b^n\pi x_m) - \cos(b^n\pi x)) $$
$$ B = ∑_{n=m}^{\infty} a^n (\cos(b^n\pi x_m) - \cos(b^n\pi x)) $$
-/

/-- The partial sum has upper bound in absolute value $|A| \le |x_m - x| \pi (ab)^m / (ab - 1)$ -/
theorem weierstrass_partial {a : ℝ} (ha : 0 < a) {b : ℕ} (hab : 1 < a * b) (x : ℝ) (m : ℕ) :
    let xₘ := seq b x m ((pos_of_mul_pos_right (zero_lt_one.trans hab) ha.le).ne'.isUnit.pow m)
    |∑ n ∈ Finset.range m, a ^ n * (cos (b ^ n * π * xₘ) - cos (b ^ n * π * x))| ≤
      |xₘ - x| * (π / (a * b - 1) * (a * b) ^ m) := by
  intro xₘ
  grw [Finset.abs_sum_le_sum_abs]
  simp_rw [abs_mul, abs_pow, abs_of_nonneg ha.le]
  apply le_trans <| Finset.sum_le_sum fun n _ ↦
    mul_le_mul_of_nonneg_left (abs_cos_sub_cos_le _ _) (pow_nonneg ha.le _)
  have (n : ℕ) : a ^ n * |b ^ n * π * xₘ - b ^ n * π * x| =
      (a * b) ^ n * (π * |xₘ - x|) := by
    simp_rw [← mul_sub, abs_mul, abs_pow, mul_pow]
    rw [abs_of_nonneg pi_nonneg, abs_of_nonneg b.cast_nonneg]
    ring
  simp_rw [this, ← Finset.sum_mul, geom_sum_eq hab.ne.symm]
  calc
    _ ≤ (a * b) ^ m / (a * b - 1) * (π * |xₘ - x|) :=
      mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (sub_le_self _ zero_le_one) (sub_nonneg.mpr hab.le))
        (mul_nonneg pi_nonneg (abs_nonneg _))
    _ = _ := by
      simp only [div_eq_mul_inv₀]
      ring

/-- The remainder has lower bound in absolute value $|B| \ge |x_m - x| 2 (ab)^m / 3$ -/
theorem weierstrass_remainder {a : ℝ} (ha : 0 < a) {b : ℕ} (hb : Odd b) {x : ℝ} {m : ℕ} :
    let xₘ := seq b x m ((Nat.cast_pos.mpr hb.pos : (0 : ℝ) < b).ne'.isUnit.pow m)
    (hsum : Summable fun n ↦
      a ^ (n + m) * (cos (b ^ (n + m) * π * xₘ) - cos (b ^ (n + m) * π * x))) →
    |xₘ - x| * (2 / 3 * (a * b) ^ m) ≤
      |∑' n, a ^ (n + m) * (cos (b ^ (n + m) * π * xₘ) - cos (b ^ (n + m) * π * x))| := by
  intro xₘ hsum
  have hb0' : (0 : ℝ) < b := Nat.cast_pos.mpr hb.pos
  -- We are going to show that all terms in the sum have the same sign,
  -- and we only need to use the first term to get the lower bound
  trans a ^ m * (1 + cos ((b ^ m * x - ⌊b ^ m * x + 2⁻¹⌋) * π))
  · -- Show that the first term (after simplification) satisfies the bound
    suffices a ^ m * (2 / 3 * b ^ m * |xₘ - x|) ≤
        a ^ m * (1 + cos ((b ^ m * x - ⌊b ^ m * x + 2⁻¹⌋) * π)) by
      convert! this using 1
      ring
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg ha.le _)
    trans 1
    · rw [abs_of_nonneg (sub_nonneg.mpr (le_seq hb0' x m))]
      calc
        _ ≤ 2 / 3 * b ^ m * ((3 / 2) * (b : ℝ)⁻¹ ^ m) :=
          mul_le_mul_of_nonneg_left (sub_le_iff_le_add'.mpr (seq_le hb0' x m)) (by positivity)
        _ = 1 := by
          rw [inv_pow₀, mul_mul_mul_comm, mul_inv_cancel₀, mul_one]
          norm_num
    · rw [le_add_iff_nonneg_right]
      refine cos_nonneg_of_mem_Icc (Set.mem_Icc.mpr ⟨?_, ?_⟩)
      · grw [Int.floor_le]
        apply le_of_eq
        simp only [div_eq_mul_inv₀]
        ring
      · grw [← Int.sub_one_lt_floor]
        apply le_of_eq
        ring
  -- Show that the first cos in each term is always ±1
  have h1 (n : ℕ) : cos (b ^ (n + m) * π * xₘ) = - (-1) ^ (⌊b ^ m * x + 2⁻¹⌋) :=
    calc
      _ = cos ((b ^ n * (⌊b ^ m * x + 2⁻¹⌋ + 1) : ℤ) * π) := by
        push_cast
        rw [← seq_mul_pow hb0'.ne' x m]
        congr 1
        ring
      _ = ((-1) ^ b ^ n) ^ (⌊b ^ m * x + 2⁻¹⌋) * (-1) ^ b ^ n := by
        rw [cos_int_mul_pi, mul_add_one, zpow_add₀ (by simp), zpow_mul₀ (by simp)]
        norm_cast
      _ = _ := by
        simp [Odd.neg_one_pow (show Odd (b ^ n) from hb.pow)]
  -- Show that the second cos in each term is always ±cos(...)
  have h2 (n : ℕ) : cos (b ^ (n + m) * π * x) =
      (-1) ^ (⌊b ^ m * x + 2⁻¹⌋) * cos (b ^ n * (b ^ m * x - ⌊b ^ m * x + 2⁻¹⌋) * π) :=
    calc
      _ = cos (b ^ n * (b ^ m * x - ⌊b ^ m * x + 2⁻¹⌋) * π +
          (b ^ n * (⌊b ^ m * x + 2⁻¹⌋) : ℤ) * π) := by
        push_cast
        ring_nf
      _ = ((-1) ^ b ^ n) ^ (⌊b ^ m * x + 2⁻¹⌋) *
          cos (b ^ n * (b ^ m * x - ⌊b ^ m * x + 2⁻¹⌋) * π) := by
        rw [cos_add_int_mul_pi, zpow_mul₀ (by simp)]
        norm_cast
      _ = _ := by
        simp [Odd.neg_one_pow (show Odd (b ^ n) from hb.pow)]
  -- Show that all terms have the same sign, and the first term agrees with the one we previously
  -- assumed
  have h3 (n : ℕ) : a ^ (n + m) * (cos (b ^ (n + m) * π * xₘ) - cos (b ^ (n + m) * π * x))
      = - (-1) ^ (⌊b ^ m * x + 2⁻¹⌋) *
        (a ^ (n + m) * (1 + cos (b ^ n * (b ^ m * x - ⌊b ^ m * x + 2⁻¹⌋) * π))) := by
    rw [h1, h2]
    ring
  simp_rw [h3, tsum_mul_left] at ⊢ hsum
  rw [summable_mul_left_iff (by grind [zpow_ne_zero])] at hsum
  rw [abs_mul, abs_neg, abs_neg_one_zpow, one_mul]
  have h (n : ℕ) : 0 ≤ a ^ (n + m) * (1 + cos (b ^ n * (b ^ m * x - ⌊b ^ m * x + 2⁻¹⌋) * π)) := by
    apply mul_nonneg (by positivity)
    grind [neg_one_le_cos]
  -- extract first term
  rw [abs_of_nonneg (tsum_nonneg h), Summable.tsum_eq_zero_add hsum]
  simpa using tsum_nonneg (fun n ↦ h (n + 1))

/-!
With bounds for $|A|$ and $|B|$ found, we have

$$ |f(x_m) - f(x)| = |A + B| \ge |B| - |A| \ge
  |x_m - x| (ab)^m \left(\frac{2}{3} - \frac{\pi}{ab - 1}\right) $$

It is obvious that $|f(x_m) - f(x)| / |x_m - x|$ grows exponentially and gives no limit for the
derivative.
-/

theorem weierstrass_slope {a : ℝ} (ha : a ∈ Set.Ioo 0 1) {b : ℕ} (hb : Odd b) (hab : 1 < a * b)
    (x : ℝ) (m : ℕ) :
    let xₘ := seq b x m ((Nat.cast_pos.mpr hb.pos : (0 : ℝ) < b).ne'.isUnit.pow m)
    |xₘ - x| * ((2 / 3 - π / (a * b - 1)) * (a * b) ^ m) ≤
      |weierstrass a b xₘ - weierstrass a b x| := by
  intro xₘ
  simp_rw [weierstrass]
  have hsseq := summable_weierstrass ha b xₘ
  have hsx := summable_weierstrass ha b x
  have hsum := hsseq.sub hsx
  rw [← hsseq.tsum_sub hsx]
  simp_rw [← mul_sub] at ⊢ hsum
  rw [← hsum.sum_add_tsum_nat_add m]
  have hsum_shift := (summable_nat_add_iff m).mpr hsum
  rw [add_comm]
  refine le_trans ?_ (abs_sub_abs_le_abs_add _ _)
  rw [sub_mul, mul_sub]
  exact sub_le_sub (weierstrass_remainder ha.1 hb hsum_shift) (weierstrass_partial ha.1 hab x m)

theorem not_differentiableAt_weierstrass
    {a : ℝ} (ha : a ∈ Set.Ioo 0 1) {b : ℕ} (hb : Odd b) (hab : 3 / 2 * π + 1 < a * b) (x : ℝ) :
    ¬ DifferentiableAt ℝ (weierstrass a b) x := by
  have hb0' : (0 : ℝ) < b := Nat.cast_pos.mpr hb.pos
  have hb1 : (1 : ℝ) < b := by
    contrapose! hab with hb1
    calc
      a * b ≤ 1 := by bound [ha.2]
      1 ≤ 3 / 2 * π + 1 := by simp [pi_nonneg]
  have hab' : 1 < a * b := lt_trans (lt_add_of_pos_left _ (mul_pos (by norm_num) pi_pos)) hab
  by_contra!
  obtain ⟨f', h⟩ := this
  let d (m : ℕ) := seq b x m - x
  have hd (m : ℕ) : 0 < d m := sub_pos.mpr (lt_seq hb0' x m)
  let c (m : ℕ) : {c : ℝ // c ≠ 0} :=
    ⟨Checked.inv (d m) (hd m).ne'.isUnit, (inv_pos_of_pos (hd m)).ne'⟩
  have hc : Tendsto c atTop (comap Subtype.val atTop) :=
    tendsto_comap_iff.mpr (tendsto_seq_sub_inv hb1 x)
  have : Tendsto (fun m ↦ Checked.inv (d m) (hd m).ne'.isUnit *
      (weierstrass a b (seq b x m) - weierstrass a b x)) atTop (𝓝 (f' 1)) := by
    refine ((h.lim_real 1).comp hc).congr fun m ↦ ?_
    simp [c, d, smul_eq_mul]
  have h := (continuous_abs.tendsto _).comp this
  contrapose! h
  apply not_tendsto_nhds_of_tendsto_atTop
  -- To show the absolute value of slope tends to ∞, it suffices to show its lower bound does.
  suffices Tendsto ((2 / 3 - π / (a * b - 1)) * (a * b) ^ ·) atTop atTop by
    refine tendsto_atTop_mono (fun m ↦ ?_) this
    rw [Function.comp_apply, abs_mul, abs_inv]
    rw [le_inv_mul_iff₀ (abs_pos.mpr (hd m).ne')]
    exact weierstrass_slope ha hb hab' x m
  have hpos : 0 < 2 / 3 - π / (a * b - 1) := by
    rw [sub_pos, div_lt_iff₀ (by simpa using hab'), ← div_lt_iff₀' (by norm_num), lt_sub_iff_add_lt]
    convert! hab using 1
    field_simp
  exact (tendsto_const_nhds_iff.mpr rfl).pos_mul_atTop hpos (tendsto_pow_atTop_atTop_of_one_lt hab')

/-- A concrete example of $a$ and $b$ to show that the condition is not vacuous. -/
theorem not_differentiableAt_weierstrass_seven (x : ℝ) :
    ¬ DifferentiableAt ℝ (weierstrass 0.9 7) x := by
  apply not_differentiableAt_weierstrass (by norm_num) (by decide)
  grw [pi_lt_d2]
  norm_num

theorem exists_uniformContinuous_and_not_differentiableAt :
    ∃ f : ℝ → ℝ, UniformContinuous f ∧ ∀ x, ¬ DifferentiableAt ℝ f x :=
  ⟨weierstrass 0.9 7, uniformContinuous_weierstrass (by norm_num) _,
    not_differentiableAt_weierstrass_seven⟩

end NowhereDifferentiable
