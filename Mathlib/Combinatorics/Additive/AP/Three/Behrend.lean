/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.InnerProductSpace.Convex
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Combinatorics.Additive.AP.Three.Defs
public import Mathlib.Combinatorics.Pigeonhole

/-!
# Behrend's bound on Roth numbers

This file proves Behrend's lower bound on Roth numbers. This says that we can find a subset of
`{1, ..., n}` of size `n / exp (O (sqrt (log n)))` which does not contain arithmetic progressions of
length `3`.

The idea is that the sphere (in the `n`-dimensional Euclidean space) doesn't contain arithmetic
progressions (literally) because the corresponding ball is strictly convex. Thus we can take
integer points on that sphere and map them onto `ℕ` in a way that preserves arithmetic progressions
(`Behrend.map`).

## Main declarations

* `Behrend.sphere`: The intersection of the Euclidean sphere with the positive integer quadrant.
  This is the set that we will map on `ℕ`.
* `Behrend.map`: Given a natural number `d`, `Behrend.map d : ℕⁿ → ℕ` reads off the coordinates as
  digits in base `d`.
* `Behrend.card_sphere_le_rothNumberNat`: Implicit lower bound on Roth numbers in terms of
  `Behrend.sphere`.
* `Behrend.roth_lower_bound`: Behrend's explicit lower bound on Roth numbers.

## References

* [Bryan Gillespie, *Behrend’s Construction*]
  (http://www.epsilonsmall.com/resources/behrends-construction/behrend.pdf)
* Behrend, F. A., "On sets of integers which contain no three terms in arithmetical progression"
* [Wikipedia, *Salem-Spencer set*](https://en.wikipedia.org/wiki/Salem–Spencer_set)

## Tags

3AP-free, Salem-Spencer, Behrend construction, arithmetic progression, sphere, strictly convex
-/

@[expose] public section

assert_not_exists IsConformalMap Conformal

open Nat hiding log
open Finset Metric Real WithLp
open scoped Pointwise

/-- The frontier of a closed strictly convex set only contains trivial arithmetic progressions.
The idea is that an arithmetic progression is contained on a line and the frontier of a strictly
convex set does not contain lines. -/
lemma threeAPFree_frontier {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [TopologicalSpace E]
    [AddCommMonoid E] [Module 𝕜 E] {s : Set E} (hs₀ : IsClosed s) (hs₁ : StrictConvex 𝕜 s) :
    ThreeAPFree (frontier s) := by
  intro a ha b hb c hc habc
  obtain rfl : (1 / 2 : 𝕜) • a + (1 / 2 : 𝕜) • c = b := by
    rw [← smul_add, habc, smul_add, ← add_smul, add_halves, one_smul]
  have hac :=
    hs₁.eq (hs₀.frontier_subset ha) (hs₀.frontier_subset hc) one_half_pos one_half_pos
      (add_halves _) hb.2
  simp only [hac, ← add_smul, add_halves, one_smul]

lemma threeAPFree_sphere {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [StrictConvexSpace ℝ E] (x : E) (r : ℝ) : ThreeAPFree (sphere x r) := by
  obtain rfl | hr := eq_or_ne r 0
  · rw [sphere_zero]
    exact threeAPFree_singleton _
  · convert! threeAPFree_frontier isClosed_closedBall (strictConvex_closedBall ℝ x r)
    exact (frontier_closedBall _ hr).symm

namespace Behrend

variable {n d k N : ℕ} {x : Fin n → ℕ}

/-!
### Turning the sphere into 3AP-free set

We define `Behrend.sphere`, the intersection of the $L^2$ sphere with the positive quadrant of
integer points. Because the $L^2$ closed ball is strictly convex, the $L^2$ sphere and
`Behrend.sphere` are 3AP-free (`threeAPFree_sphere`). Then we can turn this set in
`Fin n → ℕ` into a set in `ℕ` using `Behrend.map`, which preserves `ThreeAPFree` because it is
an additive monoid homomorphism.
-/


/-- The box `{0, ..., d - 1}^n` as a `Finset`. -/
def box (n d : ℕ) : Finset (Fin n → ℕ) :=
  Fintype.piFinset fun _ => range d

theorem mem_box : x ∈ box n d ↔ ∀ i, x i < d := by simp only [box, Fintype.mem_piFinset, mem_range]

@[simp]
theorem card_box : #(box n d) = d ^ n := by simp [box]

@[simp]
theorem box_zero : box (n + 1) 0 = ∅ := by simp [box]

/-- The intersection of the sphere of radius `√k` with the integer points in the positive
quadrant. -/
def sphere (n d k : ℕ) : Finset (Fin n → ℕ) := {x ∈ box n d | ∑ i, x i ^ 2 = k}

theorem sphere_zero_subset : sphere n d 0 ⊆ 0 := fun x => by simp [sphere, funext_iff]

@[simp]
theorem sphere_zero_right (n k : ℕ) : sphere (n + 1) 0 k = ∅ := by simp [sphere]

theorem sphere_subset_box : sphere n d k ⊆ box n d :=
  filter_subset _ _

theorem norm_of_mem_sphere {x : Fin n → ℕ} (hx : x ∈ sphere n d k) :
    ‖toLp 2 ((↑) ∘ x : Fin n → ℝ)‖ = √↑k := by
  rw [EuclideanSpace.norm_eq]
  dsimp
  simp_rw [abs_cast, ← cast_pow, ← cast_sum, (mem_filter.1 hx).2]

theorem sphere_subset_preimage_metric_sphere : (sphere n d k : Set (Fin n → ℕ)) ⊆
    (fun x : Fin n → ℕ => toLp 2 ((↑) ∘ x : Fin n → ℝ)) ⁻¹'
      Metric.sphere (0 : PiLp 2 fun _ : Fin n => ℝ) (√↑k) :=
  fun x hx => by rw [Set.mem_preimage, mem_sphere_zero_iff_norm, norm_of_mem_sphere hx]

/-- The map that appears in Behrend's bound on Roth numbers. -/
@[simps]
def map (d : ℕ) : (Fin n → ℕ) →+ ℕ where
  toFun a := ∑ i, a i * d ^ (i : ℕ)
  map_zero' := by simp_rw [Pi.zero_apply, zero_mul, sum_const_zero]
  map_add' a b := by simp_rw [Pi.add_apply, add_mul, sum_add_distrib]

theorem map_zero (d : ℕ) (a : Fin 0 → ℕ) : map d a = 0 := by simp [map]

theorem map_succ (a : Fin (n + 1) → ℕ) :
    map d a = a 0 + (∑ x : Fin n, a x.succ * d ^ (x : ℕ)) * d := by
  simp [map, Fin.sum_univ_succ, _root_.pow_succ, ← mul_assoc, ← sum_mul]

theorem map_succ' (a : Fin (n + 1) → ℕ) : map d a = a 0 + map d (a ∘ Fin.succ) * d :=
  map_succ _

set_option backward.defeqAttrib.useBackward true in
theorem map_monotone (d : ℕ) : Monotone (map d : (Fin n → ℕ) → ℕ) := fun x y h => by
  dsimp; exact sum_le_sum fun i _ => Nat.mul_le_mul_right _ <| h i

theorem map_mod (a : Fin n.succ → ℕ) : map d a % d = a 0 % d := by
  rw [map_succ, Nat.add_mul_mod_self_right]

theorem map_eq_iff {x₁ x₂ : Fin n.succ → ℕ} (hx₁ : ∀ i, x₁ i < d) (hx₂ : ∀ i, x₂ i < d) :
    map d x₁ = map d x₂ ↔ x₁ 0 = x₂ 0 ∧ map d (x₁ ∘ Fin.succ) = map d (x₂ ∘ Fin.succ) := by
  refine ⟨fun h => ?_, fun h => by rw [map_succ', map_succ', h.1, h.2]⟩
  have : x₁ 0 = x₂ 0 := by
    rw [← mod_eq_of_lt (hx₁ _), ← map_mod, ← mod_eq_of_lt (hx₂ _), ← map_mod, h]
  rw [map_succ, map_succ, this, add_right_inj, mul_eq_mul_right_iff] at h
  exact ⟨this, h.resolve_right (pos_of_gt (hx₁ 0)).ne'⟩

theorem map_injOn : {x : Fin n → ℕ | ∀ i, x i < d}.InjOn (map d) := by
  intro x₁ hx₁ x₂ hx₂ h
  induction n with
  | zero => simp [eq_iff_true_of_subsingleton]
  | succ n ih =>
    ext i
    have x := (map_eq_iff hx₁ hx₂).1 h
    exact Fin.cases x.1 (congr_fun <| ih (fun _ => hx₁ _) (fun _ => hx₂ _) x.2) i

theorem map_le_of_mem_box (hx : x ∈ box n d) :
    map (2 * d - 1) x ≤ ∑ i : Fin n, (d - 1) * (2 * d - 1) ^ (i : ℕ) :=
  map_monotone (2 * d - 1) fun _ => Nat.le_sub_one_of_lt <| mem_box.1 hx _

nonrec theorem threeAPFree_sphere : ThreeAPFree (sphere n d k : Set (Fin n → ℕ)) := by
  set f : (Fin n → ℕ) →+ EuclideanSpace ℝ (Fin n) :=
    { toFun := fun f => toLp 2 (((↑) : ℕ → ℝ) ∘ f)
      map_zero' := PiLp.ext fun _ => cast_zero
      map_add' := fun _ _ => PiLp.ext fun _ => cast_add _ _ }
  refine ThreeAPFree.of_image (AddHomClass.isAddFreimanHom f (Set.mapsTo_image _ _))
    ((toLp_injective 2).comp_injOn cast_injective.comp_left.injOn) (Set.subset_univ _) ?_
  refine (threeAPFree_sphere 0 (√↑k)).mono (Set.image_subset_iff.2 fun x => ?_)
  rw [Set.mem_preimage, mem_sphere_zero_iff_norm]
  exact norm_of_mem_sphere

theorem threeAPFree_image_sphere :
    ThreeAPFree ((sphere n d k).image (map (2 * d - 1)) : Set ℕ) := by
  rw [coe_image]
  apply ThreeAPFree.image' (α := Fin n → ℕ) (β := ℕ) (s := sphere n d k) (map (2 * d - 1))
    (map_injOn.mono _) threeAPFree_sphere
  rw [Set.add_subset_iff]
  rintro a ha b hb i
  have hai := mem_box.1 (sphere_subset_box ha) i
  have hbi := mem_box.1 (sphere_subset_box hb) i
  rw [lt_tsub_iff_right, ← succ_le_iff, two_mul]
  exact (add_add_add_comm _ _ 1 1).trans_le (_root_.add_le_add hai hbi)

theorem sum_sq_le_of_mem_box (hx : x ∈ box n d) : ∑ i : Fin n, x i ^ 2 ≤ n * (d - 1) ^ 2 := by
  rw [mem_box] at hx
  have : ∀ i, x i ^ 2 ≤ (d - 1) ^ 2 := fun i =>
    Nat.pow_le_pow_left (Nat.le_sub_one_of_lt (hx i)) _
  exact (sum_le_card_nsmul univ _ _ fun i _ => this i).trans (by rw [Finset.card_fin, smul_eq_mul])

theorem sum_eq : (∑ i : Fin n, d * (2 * d + 1) ^ (i : ℕ)) = ((2 * d + 1) ^ n - 1) / 2 := by
  refine (Nat.div_eq_of_eq_mul_left zero_lt_two ?_).symm
  rw [← sum_range fun i => d * (2 * d + 1) ^ (i : ℕ), ← mul_sum, mul_right_comm, mul_comm d, ←
    geom_sum_mul_add, add_tsub_cancel_right, mul_comm]

theorem sum_lt : (∑ i : Fin n, d * (2 * d + 1) ^ (i : ℕ)) < (2 * d + 1) ^ n :=
  sum_eq.trans_lt <| (Nat.div_le_self _ 2).trans_lt <| pred_lt (pow_pos (succ_pos _) _).ne'

theorem card_sphere_le_rothNumberNat (n d k : ℕ) :
    #(sphere n d k) ≤ rothNumberNat ((2 * d - 1) ^ n) := by
  cases n
  · dsimp; refine (card_le_univ _).trans_eq ?_; rfl
  cases d
  · simp
  apply threeAPFree_image_sphere.le_rothNumberNat _ _ (card_image_of_injOn _)
  · simp only [mem_image, and_imp, forall_exists_index,
      sphere, mem_filter]
    rintro _ x hx _ rfl
    exact (map_le_of_mem_box hx).trans_lt sum_lt
  apply map_injOn.mono fun x => ?_
  simp only [mem_coe, sphere, mem_filter, mem_box, and_imp, two_mul]
  exact fun h _ i => (h i).trans_le le_self_add

/-!
### Optimization

Now that we know how to turn the integer points of any sphere into a 3AP-free set, we find a
sphere containing many integer points by the pigeonhole principle. This gives us an implicit bound
that we then optimize by tweaking the parameters. The (almost) optimal parameters are
`Behrend.nValue` and `Behrend.dValue`.
-/


theorem exists_large_sphere_aux (n d : ℕ) : ∃ k ∈ range (n * (d - 1) ^ 2 + 1),
    (↑(d ^ n) / ((n * (d - 1) ^ 2 :) + 1) : ℝ) ≤ #(sphere n d k) := by
  refine exists_le_card_fiber_of_nsmul_le_card_of_maps_to (fun x hx => ?_) nonempty_range_add_one ?_
  · rw [mem_range, Nat.lt_succ_iff]
    exact sum_sq_le_of_mem_box hx
  · rw [card_range, nsmul_eq_mul, cast_add_one, card_box, mul_comm]
    exact (le_div_iff₀ (cast_add_one_pos _)).mp le_rfl

lemma sphereDenominator_pos (hn : 0 < n) (hd : 0 < d) : 0 < ((n * d ^ 2 : ℕ) : ℝ) :=
  Nat.cast_pos.2 (Nat.mul_pos hn (pow_pos hd _))

theorem exists_large_sphere (n d : ℕ) (hn : 0 < n) (hd : 0 < d) :
    ∃ k, Checked.div ((d ^ n : ℕ) : ℝ) ((n * d ^ 2 : ℕ) : ℝ)
      (sphereDenominator_pos hn hd).ne'.isUnit ≤ #(sphere n d k) := by
  obtain ⟨k, -, hk⟩ := exists_large_sphere_aux n d
  refine ⟨k, (div_le_div_of_nonneg_left (by positivity) (cast_add_one_pos _) ?_).trans hk⟩
  simp only [← le_sub_iff_add_le', cast_mul, ← mul_sub, cast_pow, cast_sub hd, sub_sq, one_pow,
    cast_one, mul_one, sub_add, sub_sub_self]
  apply one_le_mul_of_one_le_of_one_le
  · rwa [one_le_cast]
  rw [_root_.le_sub_iff_add_le]
  norm_num
  exact one_le_cast.2 hd

theorem bound_aux' (n d : ℕ) (hn : 0 < n) (hd : 0 < d) :
    Checked.div ((d ^ n : ℕ) : ℝ) ((n * d ^ 2 : ℕ) : ℝ)
      (sphereDenominator_pos hn hd).ne'.isUnit ≤ rothNumberNat ((2 * d - 1) ^ n) :=
  let ⟨_, h⟩ := exists_large_sphere n d hn hd
  h.trans <| cast_le.2 <| card_sphere_le_rothNumberNat _ _ _

theorem bound_aux (hd : d ≠ 0) (hn : 2 ≤ n) :
    Checked.div ((d : ℝ) ^ (n - 2)) (n : ℝ)
      (Nat.cast_ne_zero.mpr (show n ≠ 0 by omega)).isUnit ≤ rothNumberNat ((2 * d - 1) ^ n) := by
  have hn₀ : 0 < n := by omega
  have hd₀ := Nat.pos_of_ne_zero hd
  have H := (div_le_iff₀ (sphereDenominator_pos hn₀ hd₀)).1 (bound_aux' n d hn₀ hd₀)
  have hnum : ((d ^ n : ℕ) : ℝ) = (d : ℝ) ^ (n - 2) * (d : ℝ) ^ 2 := by
    rw [Nat.cast_pow, ← _root_.pow_add, Nat.sub_add_cancel hn]
  rw [hnum, Nat.cast_mul, Nat.cast_pow, ← mul_assoc] at H
  apply (div_le_iff₀ (Nat.cast_pos.2 hn₀ : (0 : ℝ) < n)).2
  exact (mul_le_mul_iff_left₀ (pow_pos (Nat.cast_pos.2 hd₀ : (0 : ℝ) < d) 2)).mp H

open scoped Filter Topology

open Real

lemma one_sub_two_div_exp_pos : 0 < (1 : ℝ) - 2 / exp 1 :=
  sub_pos.2 ((div_lt_one (exp_pos 1)).2 exp_one_gt_two)

local notation "B" => Checked.div (2 : ℝ) (1 - 2 / exp 1) one_sub_two_div_exp_pos.ne'.isUnit

section NumericalBounds

theorem log_two_mul_two_le_sqrt_log_eight : log 2 * 2 ≤ √(log 8) := by
  rw [show (8 : ℝ) = 2 ^ 3 by norm_num1, Real.log_pow, Nat.cast_ofNat]
  apply le_sqrt_of_sq_le
  rw [mul_pow, sq (log 2), mul_assoc, mul_comm]
  gcongr
  linarith only [log_two_lt_d9.le]

theorem two_div_one_sub_two_div_e_le_eight : B ≤ 8 := by
  apply (div_le_iff₀ one_sub_two_div_exp_pos).2
  apply (mul_le_mul_iff_left₀ (exp_pos 1)).mp
  rw [mul_assoc (8 : ℝ), sub_mul, one_mul, div_mul_cancel₀]
  linarith only [exp_one_gt_d9]

theorem le_sqrt_log (hN : 4096 ≤ N) : log B * (69 / 50) ≤ √(log ↑N) := by
  calc
    _ ≤ log ((2 : ℝ) ^ 3) * (69 / 50) := by
      apply mul_le_mul_of_nonneg_right _ (by norm_num)
      apply log_le_log (div_pos zero_lt_two one_sub_two_div_exp_pos)
      simpa only [show (2 : ℝ) ^ 3 = 8 by norm_num] using two_div_one_sub_two_div_e_le_eight
    _ ≤ √(log (2 ^ 12)) := by
      simp only [Real.log_pow, Nat.cast_ofNat]
      apply le_sqrt_of_sq_le
      nlinarith [log_two_lt_d9, log_two_gt_d9]
    _ ≤ √(log ↑N) := by
      gcongr
      exact mod_cast hN

theorem exp_neg_two_mul_le {x : ℝ} (hx : 0 < x) : exp (-2 * x) < exp (2 - ⌈x⌉₊) / ⌈x⌉₊ := by
  have h₁ := ceil_lt_add_one hx.le
  have h₂ : 1 - x ≤ 2 - ⌈x⌉₊ := by linarith
  calc
    _ ≤ exp (1 - x) / (x + 1) := ?_
    _ ≤ exp (2 - ⌈x⌉₊) / (x + 1) := by gcongr
    _ < _ := by gcongr
  rw [le_div_iff₀ (add_pos hx zero_lt_one), ← le_div_iff₀' (exp_pos _), ← exp_sub, neg_mul,
    sub_neg_eq_add, two_mul, sub_add_add_cancel, add_comm _ x]
  exact le_trans (le_add_of_nonneg_right zero_le_one) (add_one_le_exp _)

theorem div_lt_floor {x : ℝ} (hx : B ≤ x) : x / exp 1 < (⌊x / 2⌋₊ : ℝ) := by
  have h := (div_le_iff₀ one_sub_two_div_exp_pos).1 hx
  rw [mul_sub, mul_one, ← mul_div_assoc₀, mul_comm x 2, mul_div_assoc₀] at h
  refine lt_of_le_of_lt ?_ (sub_one_lt_floor (x / 2))
  have hx₂ : x / 2 * 2 = x := div_mul_cancel₀ x
  linarith only [h, hx₂]

theorem ceil_lt_mul {x : ℝ} (hx : 50 / 19 ≤ x) : (⌈x⌉₊ : ℝ) < 1.38 * x := by
  refine (ceil_lt_add_one ((show (0 : ℝ) ≤ 50 / 19 by norm_num).trans hx)).trans_le ?_
  have h := (div_le_iff₀ (show (0 : ℝ) < 19 by norm_num)).1 hx
  linarith

end NumericalBounds

/-- The (almost) optimal value of `n` in `Behrend.bound_aux`. -/
noncomputable def nValue (N : ℕ) : ℕ :=
  ⌈√(log N)⌉₊

theorem nValue_pos (hN : 2 ≤ N) : 0 < nValue N :=
  ceil_pos.2 <| Real.sqrt_pos.2 <| log_pos <| one_lt_cast.2 <| hN

/-- The positive real root used to choose the digit bound. -/
noncomputable abbrev dimRoot (N : ℕ) (hN : 2 ≤ N) : ℝ :=
  (N : ℝ) ^ Checked.inv (nValue N : ℝ) (Nat.cast_ne_zero.mpr (nValue_pos hN).ne').isUnit

/-- The (almost) optimal value of `d` in `Behrend.bound_aux`. -/
noncomputable def dValue (N : ℕ) (hN : 2 ≤ N) : ℕ := ⌊dimRoot N hN / 2⌋₊

private lemma dimRoot_pos (hN : 2 ≤ N) : 0 < dimRoot N hN :=
  rpow_pos_of_pos (Nat.cast_pos.2 (show 0 < N by omega)) _

private lemma log_dimRoot_mul (hN : 2 ≤ N) :
    log (dimRoot N hN) * (nValue N : ℝ) = log (N : ℝ) := by
  have h : (0 : ℝ) < N := Nat.cast_pos.2 (by omega)
  rw [dimRoot, log_rpow h, mul_right_comm, inv_mul_cancel₀, one_mul]

private lemma dimRoot_pow (hN : 2 ≤ N) : dimRoot N hN ^ nValue N = (N : ℝ) := by
  rw [dimRoot, ← rpow_natCast, ← rpow_mul (Nat.cast_nonneg N), inv_mul_cancel₀, rpow_one]

theorem three_le_nValue (hN : 64 ≤ N) : 3 ≤ nValue N := by
  rw [nValue, ← lt_iff_add_one_le, lt_ceil, cast_two]
  apply lt_sqrt_of_sq_lt
  have : (2 : ℝ) ^ ((6 : ℕ) : ℝ) ≤ N := by
    rw [rpow_natCast]
    exact (cast_le.2 hN).trans' (by norm_num1)
  apply lt_of_lt_of_le _ (log_le_log (rpow_pos_of_pos zero_lt_two _) this)
  rw [log_rpow zero_lt_two, ← div_lt_iff₀']
  · exact log_two_gt_d9.trans_le' (by norm_num1)
  · norm_num1

theorem dValue_pos (hN₃ : 8 ≤ N) : 0 < dValue N (by omega) := by
  have h₂ : 2 ≤ N := by omega
  have hN₀ : (0 : ℝ) < N := Nat.cast_pos.2 (by omega)
  have h₁ : (1 : ℝ) ≤ N := Nat.one_le_cast.2 (by omega)
  have hn : (0 : ℝ) < nValue N := Nat.cast_pos.2 (nValue_pos h₂)
  change 0 < ⌊dimRoot N h₂ / 2⌋₊
  rw [floor_pos, le_div_iff₀ (show (0 : ℝ) < 2 by norm_num), one_mul,
    ← log_le_log_iff zero_lt_two (dimRoot_pos h₂)]
  apply (mul_le_mul_iff_left₀ hn).mp
  rw [log_dimRoot_mul]
  have hc : (nValue N : ℝ) ≤ 2 * √(log N) := by
    apply (ceil_lt_add_one (sqrt_nonneg _)).le.trans
    rw [two_mul, add_le_add_iff_left]
    apply le_sqrt_of_sq_le
    rw [one_pow, le_log_iff_exp_le hN₀]
    exact (exp_one_lt_d9.le.trans <| by norm_num).trans (Nat.cast_le.2 hN₃)
  have hs : log 2 * 2 ≤ √(log N) :=
    log_two_mul_two_le_sqrt_log_eight.trans
      (Real.sqrt_le_sqrt (log_le_log (by norm_num) (by exact_mod_cast hN₃)))
  calc
    _ ≤ log 2 * (2 * √(log N)) :=
      mul_le_mul_of_nonneg_left hc (log_nonneg one_le_two)
    _ = (log 2 * 2) * √(log N) := (mul_assoc _ _ _).symm
    _ ≤ √(log N) * √(log N) := mul_le_mul_of_nonneg_right hs (sqrt_nonneg _)
    _ = _ := by rw [← sq, Real.sq_sqrt (log_nonneg h₁)]

theorem le_N (hN : 2 ≤ N) : (2 * dValue N hN - 1) ^ nValue N ≤ N := by
  have hf : (dValue N hN : ℝ) ≤ dimRoot N hN / 2 :=
    floor_le (div_nonneg (dimRoot_pos hN).le zero_le_two)
  have hi : (2 : ℝ) * dValue N hN ≤ dimRoot N hN := by
    rw [mul_comm]
    exact (le_div_iff₀ (show (0 : ℝ) < 2 by norm_num)).1 hf
  apply (Nat.pow_le_pow_left (Nat.sub_le (2 * dValue N hN) 1) (nValue N)).trans
  have H : ((2 : ℝ) * dValue N hN) ^ nValue N ≤ (N : ℝ) := calc
    _ ≤ dimRoot N hN ^ nValue N :=
      pow_le_pow_left₀ (mul_nonneg zero_le_two (Nat.cast_nonneg _)) hi _
    _ = _ := dimRoot_pow hN
  exact_mod_cast H

theorem bound (hN : 4096 ≤ N) :
    dimRoot N (by omega) / exp 1 < dValue N (by omega) := by
  have h₂ : 2 ≤ N := by omega
  change dimRoot N h₂ / exp 1 < (⌊dimRoot N h₂ / 2⌋₊ : ℝ)
  apply div_lt_floor
  apply (log_le_log_iff (div_pos zero_lt_two one_sub_two_div_exp_pos) (dimRoot_pos h₂)).1
  apply (mul_le_mul_iff_left₀ (Nat.cast_pos.2 (nValue_pos h₂) : (0 : ℝ) < nValue N)).mp
  rw [log_dimRoot_mul]
  have hc : (50 / 19 : ℝ) ≤ √(log N) := by
    apply le_sqrt_of_sq_le
    have h₁₂ : (12 : ℕ) * log 2 ≤ log N := by
      rw [← log_rpow zero_lt_two, rpow_natCast]
      exact log_le_log (by positivity) (mod_cast hN)
    refine le_trans ?_ h₁₂
    rw [← div_le_iff₀']
    · exact log_two_gt_d9.le.trans' (by norm_num1)
    · norm_num1
  have hB : 1 ≤ B := by
    apply (le_div_iff₀ one_sub_two_div_exp_pos).2
    rw [one_mul]
    have he : 0 ≤ (2 : ℝ) / exp 1 := div_nonneg zero_le_two (exp_pos 1).le
    linarith only [he]
  calc
    _ ≤ log B * (1.38 * √(log N)) :=
      mul_le_mul_of_nonneg_left (ceil_lt_mul hc).le (log_nonneg hB)
    _ = (log B * (69 / 50)) * √(log N) := by
      rw [mul_assoc, show (1.38 : ℝ) = 69 / 50 by norm_num]
    _ ≤ √(log N) * √(log N) :=
      mul_le_mul_of_nonneg_right (le_sqrt_log hN) (sqrt_nonneg _)
    _ = _ := by rw [← sq, Real.sq_sqrt (log_nonneg (Nat.one_le_cast.2 (by omega : 1 ≤ N)))]

theorem roth_lower_bound_explicit (hN : 4096 ≤ N) :
    (N : ℝ) * exp (-4 * √(log N)) < rothNumberNat N := by
  have h₂ : 2 ≤ N := by omega
  let n := nValue N
  let d := dValue N h₂
  let r := dimRoot N h₂
  let s := √(log (N : ℝ))
  have hn : (0 : ℝ) < n := Nat.cast_pos.2 (nValue_pos h₂)
  have hd : 0 < d := dValue_pos (by omega : 8 ≤ N)
  have hn₂ : 2 < n := three_le_nValue (by omega : 64 ≤ N)
  have hN₀ : (0 : ℝ) < N := Nat.cast_pos.2 (by omega)
  have hlog : 0 < log (N : ℝ) := log_pos (Nat.one_lt_cast.2 h₂)
  have hs : 0 < s := Real.sqrt_pos.2 hlog
  have hs₂ : s ^ 2 = log (N : ℝ) := Real.sq_sqrt hlog.le
  have hsn : s ≤ (n : ℝ) := le_ceil _
  have hr : 0 < r := dimRoot_pos h₂
  have hrn : log r * (n : ℝ) = log (N : ℝ) := log_dimRoot_mul h₂
  have hrs : log r ≤ s := by
    apply (mul_le_mul_iff_left₀ hn).mp
    rw [hrn, ← hs₂, sq]
    exact mul_le_mul_of_nonneg_left hsn hs.le
  have he : exp (-2 * s) * (n : ℝ) ≤ exp (2 - (n : ℝ)) :=
    (le_div_iff₀ hn).1 (exp_neg_two_mul_le hs).le
  have hel := log_le_log (mul_pos (exp_pos _) hn) he
  simp only [log_mul (exp_pos (-2 * s)).ne' hn.ne', log_exp] at hel
  have hq : 0 < r / exp 1 := div_pos hr (exp_pos _)
  have hrd : r / exp 1 < (d : ℝ) := bound hN
  calc
    (N : ℝ) * exp (-4 * s) ≤ ((r / exp 1) ^ (n - 2)) / (n : ℝ) := by
      apply (le_div_iff₀ hn).2
      apply (log_le_log_iff (mul_pos (mul_pos hN₀ (exp_pos _)) hn) (pow_pos hq _)).1
      rw [log_mul (mul_pos hN₀ (exp_pos (-4 * s))).ne' hn.ne',
        log_mul hN₀.ne' (exp_pos (-4 * s)).ne', Real.log_pow, log_div hr.ne',
        Nat.cast_sub hn₂.le]
      simp only [log_exp, Nat.cast_ofNat]
      nlinarith only [hrn, hrs, hel]
    _ < (d : ℝ) ^ (n - 2) / (n : ℝ) := by
      apply (div_lt_div_iff_of_pos_right hn).2
      exact pow_lt_pow_left₀ hrd hq.le (Nat.sub_ne_zero_of_lt hn₂)
    _ ≤ rothNumberNat ((2 * d - 1) ^ n) := bound_aux hd.ne' hn₂.le
    _ ≤ rothNumberNat N := by exact_mod_cast rothNumberNat.mono (le_N h₂)

theorem exp_four_lt : exp 4 < 64 := by
  rw [show (64 : ℝ) = 2 ^ ((6 : ℕ) : ℝ) by rw [rpow_natCast]; norm_num1,
    ← lt_log_iff_exp_lt (rpow_pos_of_pos zero_lt_two _), log_rpow zero_lt_two, ← div_lt_iff₀']
  · exact log_two_gt_d9.trans_le' (by norm_num1)
  · simp

theorem four_zero_nine_six_lt_exp_sixteen : 4096 < exp 16 := by
  rw [← log_lt_iff_lt_exp (show (0 : ℝ) < 4096 by simp), show (4096 : ℝ) = 2 ^ 12 by norm_cast,
    ← rpow_natCast, log_rpow zero_lt_two, cast_ofNat]
  linarith [log_two_lt_d9]

theorem lower_bound_le_one' (hN : 2 ≤ N) (hN' : N ≤ 4096) :
    (N : ℝ) * exp (-4 * √(log N)) ≤ 1 := by
  rw [← log_le_log_iff (mul_pos (cast_pos.2 (zero_lt_two.trans_le hN)) (exp_pos _)) zero_lt_one,
    log_one, log_mul (cast_pos.2 (zero_lt_two.trans_le hN)).ne' (exp_pos _).ne', log_exp, neg_mul, ←
    sub_eq_add_neg, sub_nonpos, ←
    div_le_iff₀ (Real.sqrt_pos.2 <| log_pos <| one_lt_cast.2 <| one_lt_two.trans_le hN), div_sqrt,
    sqrt_le_left zero_le_four, log_le_iff_le_exp (cast_pos.2 (zero_lt_two.trans_le hN))]
  norm_num1
  apply le_trans _ four_zero_nine_six_lt_exp_sixteen.le
  exact mod_cast hN'

theorem lower_bound_le_one (hN : 1 ≤ N) (hN' : N ≤ 4096) :
    (N : ℝ) * exp (-4 * √(log N)) ≤ 1 := by
  obtain rfl | hN := hN.eq_or_lt
  · simp
  · exact lower_bound_le_one' hN hN'

theorem roth_lower_bound : (N : ℝ) * exp (-4 * √(log N)) ≤ rothNumberNat N := by
  obtain rfl | hN := Nat.eq_zero_or_pos N
  · simp
  obtain h₁ | h₁ := le_or_gt 4096 N
  · exact (roth_lower_bound_explicit h₁).le
  · apply (lower_bound_le_one hN h₁.le).trans
    simpa using! rothNumberNat.monotone hN

end Behrend
