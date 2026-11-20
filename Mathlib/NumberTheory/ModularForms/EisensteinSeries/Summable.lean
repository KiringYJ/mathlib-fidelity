/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
public import Mathlib.Analysis.PSeries
public import Mathlib.Order.Interval.Finset.Box
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Topology.Bornology.BoundedOperation

/-!
# Summability of Eisenstein series

We gather results about the summability of Eisenstein series, particularly
the summability of the Eisenstein series summands, which are used in the proof of the
boundedness of Eisenstein series at infinity.
-/

@[expose] public section
noncomputable section

open Complex UpperHalfPlane Set Finset Topology Filter Asymptotics

open scoped UpperHalfPlane Topology Nat

variable (z : ℍ)

namespace EisensteinSeries

lemma norm_eq_max_natAbs (x : Fin 2 → ℤ) : ‖x‖ = max (x 0).natAbs (x 1).natAbs := by
  rw [← coe_nnnorm, ← NNReal.coe_natCast, NNReal.coe_inj, Nat.cast_max]
  refine eq_of_forall_ge_iff fun c ↦ ?_
  simp only [pi_nnnorm_le_iff, Fin.forall_fin_two, max_le_iff, NNReal.natCast_natAbs]

lemma norm_symm (x y : ℤ) : ‖![x, y]‖ = ‖![y, x]‖ := by
  simp [EisensteinSeries.norm_eq_max_natAbs, max_comm]

theorem abs_le_left_of_norm (m n : ℤ) : |n| ≤ ‖![n, m]‖ := by
  simp only [EisensteinSeries.norm_eq_max_natAbs, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Nat.cast_max, le_sup_iff]
  left
  rw [Int.abs_eq_natAbs]
  exact le_refl _

theorem abs_le_right_of_norm (m n : ℤ) : |m| ≤ ‖![n, m]‖ := by
  simp only [EisensteinSeries.norm_eq_max_natAbs, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Nat.cast_max, le_sup_iff]
  right
  rw [Int.abs_eq_natAbs]
  exact le_refl _

lemma abs_norm_eq_max_natAbs (n : ℕ) : ‖![1, (n + 1 : ℤ)]‖ = n + 1 := by
  simp only [EisensteinSeries.norm_eq_max_natAbs, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  norm_cast

lemma abs_norm_eq_max_natAbs_neg (n : ℕ) : ‖![1, -(n + 1 : ℤ)]‖ = n + 1 := by
  simp only [EisensteinSeries.norm_eq_max_natAbs, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  norm_cast

section bounding_functions

/-- Auxiliary function used for bounding Eisenstein series, defined as
  `z.im ^ 2 / (z.re ^ 2 + z.im ^ 2)`. -/
def r1 : ℝ := z.im ^ 2 / (z.re ^ 2 + z.im ^ 2)

lemma r1_eq : r1 z = 1 / ((z.re / z.im) ^ 2 + 1) := by
  have him := z.im_pos
  unfold r1
  field_simp

lemma r1_pos : 0 < r1 z := by
  dsimp only [r1]
  positivity

/-- For `c, d ∈ ℝ` with `1 ≤ d ^ 2`, we have `r1 z ≤ |c * z + d| ^ 2`. -/
lemma r1_aux_bound (c : ℝ) {d : ℝ} (hd : 1 ≤ d ^ 2) :
    r1 z ≤ (c * z.re + d) ^ 2 + (c * z.im) ^ 2 := by
  have H1 : (c * z.re + d) ^ 2 + (c * z.im) ^ 2 =
    c ^ 2 * (z.re ^ 2 + z.im ^ 2) + d * 2 * c * z.re + d ^ 2 := by ring
  have H2 : (c ^ 2 * (z.re ^ 2 + z.im ^ 2) + d * 2 * c * z.re + d ^ 2) * (z.re ^ 2 + z.im ^ 2)
    - z.im ^ 2 = (c * (z.re ^ 2 + z.im ^ 2) + d * z.re) ^ 2 + (d ^ 2 - 1) * z.im ^ 2 := by ring
  rw [r1, H1, div_le_iff₀ (by positivity), ← sub_nonneg, H2]
  exact add_nonneg (sq_nonneg _) (mul_nonneg (sub_nonneg.mpr hd) (sq_nonneg _))

/-- This function is used to give an upper bound on the summands in Eisenstein series; it is
defined by `z ↦ min z.im √(z.im ^ 2 / (z.re ^ 2 + z.im ^ 2))`. -/
def r : ℝ := min z.im √(r1 z)

lemma r_pos : 0 < r z := by
  simp only [r, lt_min_iff, im_pos, Real.sqrt_pos, r1_pos, and_self]

lemma r_lower_bound_on_verticalStrip {A B : ℝ} (h : 0 < B) (hz : z ∈ verticalStrip A B) :
    r ⟨⟨A, B⟩, h⟩ ≤ r z := by
  apply min_le_min hz.2
  gcongr
  simp only [r1_eq, div_pow₀, one_div₀]
  rw [inv_le_inv₀ (by positivity) (by positivity), add_le_add_iff_right, ← even_two.pow_abs]
  gcongr
  exacts [hz.1, hz.2]

lemma auxbound1 {c : ℝ} (d : ℝ) (hc : 1 ≤ c ^ 2) : r z ≤ ‖c * (z : ℂ) + d‖ := by
  rcases z with ⟨z, hz⟩
  have H1 : z.im ≤ √((c * z.re + d) ^ 2 + (c * z).im ^ 2) := by
    rw [Real.le_sqrt' hz, im_ofReal_mul, mul_pow]
    exact (le_mul_of_one_le_left (sq_nonneg _) hc).trans <| le_add_of_nonneg_left (sq_nonneg _)
  simpa only [r, norm_def, normSq_apply, add_re, re_ofReal_mul, coe_re, ← pow_two, add_im, mul_im,
    coe_im, ofReal_im, zero_mul, add_zero, min_le_iff] using! Or.inl H1

lemma auxbound2 (c : ℝ) {d : ℝ} (hd : 1 ≤ d ^ 2) : r z ≤ ‖c * (z : ℂ) + d‖ := by
  have H1 : √(r1 z) ≤ √((c * z.re + d) ^ 2 + (c * z.im) ^ 2) :=
    (Real.sqrt_le_sqrt_iff (by positivity)).mpr (r1_aux_bound _ _ hd)
  simpa only [r, norm_def, normSq_apply, add_re, re_ofReal_mul, coe_re, ofReal_re, ← pow_two,
    add_im, im_ofReal_mul, coe_im, ofReal_im, add_zero, min_le_iff] using Or.inr H1

lemma div_max_sq_ge_one (x : Fin 2 → ℤ) (hx : x ≠ 0) :
    1 ≤ (x 0 / ‖x‖) ^ 2 ∨ 1 ≤ (x 1 / ‖x‖) ^ 2 := by
  refine (max_choice (x 0).natAbs (x 1).natAbs).imp (fun H0 ↦ ?_) (fun H1 ↦ ?_)
  · have : x 0 ≠ 0 := by
      rwa [← norm_ne_zero_iff, norm_eq_max_natAbs, H0, Nat.cast_ne_zero, Int.natAbs_ne_zero] at hx
    simp only [norm_eq_max_natAbs, H0, Nat.cast_natAbs, Int.cast_abs, div_pow₀, sq_abs, div_self,
      le_refl]
  · have : x 1 ≠ 0 := by
      rwa [← norm_ne_zero_iff, norm_eq_max_natAbs, H1, Nat.cast_ne_zero, Int.natAbs_ne_zero] at hx
    simp only [norm_eq_max_natAbs, H1, Nat.cast_natAbs, Int.cast_abs, div_pow₀, sq_abs, div_self,
      le_refl]

lemma r_mul_max_le {x : Fin 2 → ℤ} (hx : x ≠ 0) : r z * ‖x‖ ≤ ‖x 0 * (z : ℂ) + x 1‖ := by
  have hn0 : ‖x‖ ≠ 0 := by rwa [norm_ne_zero_iff]
  have h11 : x 0 * (z : ℂ) + x 1 = (x 0 / ‖x‖ * z + x 1 / ‖x‖) * ‖x‖ := by
    rw [div_mul_eq_mul_div₀, ← add_div, div_mul_cancel₀]
  rw [h11, norm_mul, norm_real, norm_norm]
  gcongr
  · rcases div_max_sq_ge_one x hx with H1 | H2
    · simpa only [ofReal_div _ _ (hs := hn0.isUnit), ofReal_intCast] using
        auxbound1 z (x 1 / ‖x‖) H1
    · simpa only [ofReal_div _ _ (hs := hn0.isUnit), ofReal_intCast] using
        auxbound2 z (x 0 / ‖x‖) H2

/-- Upper bound for the summand `|c * z + d| ^ (-k)`, as a product of a function of `z` and a
function of `c, d`. -/
lemma summand_bound {k : ℝ} (hk : 0 ≤ k) (x : Fin 2 → ℤ) :
    ‖x 0 * (z : ℂ) + x 1‖ ^ (-k) ≤ (r z) ^ (-k) * ‖x‖ ^ (-k) := by
  by_cases hx : x = 0
  · simp only [hx, Pi.zero_apply, Int.cast_zero, zero_mul, add_zero, norm_zero]
    by_cases h : -k = 0
    · rw [h, Real.rpow_zero, Real.rpow_zero, one_mul]
    · rw [Real.zero_rpow h, mul_zero]
  · rw [← Real.mul_rpow (r_pos _).le (norm_nonneg _)]
    exact Real.rpow_le_rpow_of_nonpos (mul_pos (r_pos _) (norm_pos_iff.mpr hx)) (r_mul_max_le z hx)
      (neg_nonpos.mpr hk)

variable {z} in
lemma summand_bound_of_mem_verticalStrip {k : ℝ} (hk : 0 ≤ k) (x : Fin 2 → ℤ)
    {A B : ℝ} (hB : 0 < B) (hz : z ∈ verticalStrip A B) :
    ‖x 0 * (z : ℂ) + x 1‖ ^ (-k) ≤ r ⟨⟨A, B⟩, hB⟩ ^ (-k) * ‖x‖ ^ (-k) := by
  refine (summand_bound z hk x).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  exact Real.rpow_le_rpow_of_nonpos (r_pos _) (r_lower_bound_on_verticalStrip z hB hz)
    (neg_nonpos.mpr hk)

lemma linear_isTheta_right_add (c e : ℤ) (z : ℂ) :
    (fun d : ℤ ↦ c * z + d + e) =Θ[cofinite] fun n ↦ (n : ℝ) := by
  apply IsTheta.add_isLittleO <;>
  [refine Asymptotics.IsLittleO.add_isTheta ?_ (Int.cast_complex_isTheta_cast_real); skip] <;>
  simpa [-Int.cofinite_eq] using
    .inr <| tendsto_norm_comp_cofinite_atTop_of_isClosedEmbedding Int.isClosedEmbedding_coe_real

lemma linear_isTheta_left (d : ℤ) {z : ℂ} (hz : z ≠ 0) :
    (fun (c : ℤ) ↦ (c * z + d)) =Θ[cofinite] fun n ↦ (n : ℝ) := by
  apply IsTheta.add_isLittleO
  · simp_rw [mul_comm]
    apply Asymptotics.IsTheta.const_mul_left hz Int.cast_complex_isTheta_cast_real
  · simp only [isLittleO_const_left, Int.cast_eq_zero,
      tendsto_norm_comp_cofinite_atTop_of_isClosedEmbedding Int.isClosedEmbedding_coe_real, or_true]

/-! Inverse estimates use a coordinate map from the actual domain. A punctured lattice,
or an intersection of several denominator domains, is obtained by taking a subtype and
its inclusion. No value is assigned at a pole. -/

lemma linear_inv_isBigO_right_add (c e : ℤ) (z : ℂ) {D : Type*} {l : Filter D}
    (d : D → ℤ) (hd : Tendsto d l cofinite)
    {hlinear : ∀ x, IsUnit (c * z + d x + e)} {hcast : ∀ x, IsUnit (d x : ℝ)} :
    (fun x ↦ Checked.inv (c * z + d x + e) (hlinear x)) =O[l]
      fun x ↦ Checked.inv (d x : ℝ) (hcast x) :=
  ((linear_isTheta_right_add c e z).comp_tendsto hd).inv.isBigO

lemma linear_inv_isBigO_right (c : ℤ) (z : ℂ) {D : Type*} {l : Filter D}
    (d : D → ℤ) (hd : Tendsto d l cofinite)
    {hlinear : ∀ x, IsUnit (c * z + d x)} {hcast : ∀ x, IsUnit (d x : ℝ)} :
    (fun x ↦ Checked.inv (c * z + d x) (hlinear x)) =O[l]
      fun x ↦ Checked.inv (d x : ℝ) (hcast x) := by
  have h : (fun n : ℤ ↦ c * z + n) =Θ[cofinite] (fun n ↦ (n : ℝ)) := by
    simpa only [Int.cast_zero, add_zero] using linear_isTheta_right_add c 0 z
  exact (h.comp_tendsto hd).inv.isBigO

lemma linear_inv_isBigO_left (d : ℤ) {z : ℂ} (hz : z ≠ 0) {D : Type*} {l : Filter D}
    (c : D → ℤ) (hc : Tendsto c l cofinite)
    {hlinear : ∀ x, IsUnit (c x * z + d)} {hcast : ∀ x, IsUnit (c x : ℝ)} :
    (fun x ↦ Checked.inv (c x * z + d) (hlinear x)) =O[l]
      fun x ↦ Checked.inv (c x : ℝ) (hcast x) :=
  ((linear_isTheta_left d hz).comp_tendsto hc).inv.isBigO

lemma tendsto_zero_inv_linear (z : ℂ) (b : ℤ) {D : Type*} {l : Filter D}
    (d : D → ℕ) (hd : Tendsto d l atTop)
    {hlinear : ∀ x, IsUnit ((b : ℂ) * z + d x)} :
    Tendsto (fun x ↦ Checked.div 1 ((b : ℂ) * z + d x) (hlinear x)) l (𝓝 0) := by
  have hlin : Tendsto (fun x ↦ (b : ℂ) * z + d x) l (Bornology.cobounded ℂ) :=
    (tendsto_const_add_cobounded _).comp (tendsto_natCast_atTop_cobounded.comp hd)
  have hu : Tendsto (fun x ↦ (hlinear x).unit) l
      (comap (fun u : ℂˣ ↦ (u : ℂ)) (Bornology.cobounded ℂ)) := by
    apply tendsto_comap_iff.mpr
    simpa only [Function.comp_def, IsUnit.unit_spec] using hlin
  simpa only [Checked.div, one_divp, Function.comp_def] using tendsto_inv₀_cobounded.comp hu

lemma tendsto_zero_inv_linear_sub (z : ℂ) (b : ℤ) {D : Type*} {l : Filter D}
    (d : D → ℕ) (hd : Tendsto d l atTop)
    {hlinear : ∀ x, IsUnit ((b : ℂ) * z - d x)} :
    Tendsto (fun x ↦ Checked.div 1 ((b : ℂ) * z - d x) (hlinear x)) l (𝓝 0) := by
  have hlin : Tendsto (fun x ↦ (b : ℂ) * z - d x) l (Bornology.cobounded ℂ) :=
    (tendsto_const_sub_cobounded _).comp (tendsto_natCast_atTop_cobounded.comp hd)
  have hu : Tendsto (fun x ↦ (hlinear x).unit) l
      (comap (fun u : ℂˣ ↦ (u : ℂ)) (Bornology.cobounded ℂ)) := by
    apply tendsto_comap_iff.mpr
    simpa only [Function.comp_def, IsUnit.unit_spec] using hlin
  simpa only [Checked.div, one_divp, Function.comp_def] using tendsto_inv₀_cobounded.comp hu

end bounding_functions

/-- The function `ℤ ^ 2 → ℝ` given by `x ↦ ‖x‖ ^ (-k)` is summable if `2 < k`. We prove this by
splitting into boxes using `Finset.box`. -/
lemma summable_one_div_norm_rpow {k : ℝ} (hk : 2 < k) :
    Summable fun (x : Fin 2 → ℤ) ↦ ‖x‖ ^ (-k) := by
  rw [← (finTwoArrowEquiv _).symm.summable_iff, summable_partition _ Int.existsUnique_mem_box]
  · simp only [finTwoArrowEquiv_symm_apply, Function.comp_def]
    refine ⟨fun n ↦ (hasSum_fintype (β := box (α := ℤ × ℤ) n) _).summable, ?_⟩
    suffices Summable fun n : ℕ ↦ ∑' (_ : box (α := ℤ × ℤ) n), (n : ℝ) ^ (-k) by
      refine this.congr fun n ↦ tsum_congr fun p ↦ ?_
      simp only [← Int.mem_box.mp p.2, Nat.cast_max, norm_eq_max_natAbs, Matrix.cons_val_zero,
        Matrix.cons_val_one]
    simp only [tsum_fintype, univ_eq_attach, sum_const, card_attach, nsmul_eq_mul]
    apply ((Real.summable_nat_rpow.mpr (by linarith : 1 - k < -1)).mul_left
      8).of_norm_bounded_eventually_nat
    filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    rw [Int.card_box hn.ne', Real.norm_of_nonneg (by positivity), sub_eq_add_neg,
      Real.rpow_add (Nat.cast_pos.mpr hn), Real.rpow_one, Nat.cast_mul, Nat.cast_ofNat, mul_assoc]
  · exact fun n ↦ Real.rpow_nonneg (norm_nonneg _) _

/-- An inverse with a summable power bound is summable on its actual domain. The comparison
omits the coordinate zero, whose preimage is finite and is restored in the conclusion. -/
lemma summable_inv_of_isBigO_rpow_inv {α : Type*} [NormedField α] [CompleteSpace α]
    {D : Type*} {f : D → α} {a : ℝ} (hab : 1 < a)
    (n : D → ℤ) (hn : Function.Injective n) {hf : ∀ x, IsUnit (f x)}
    (hbound : (fun x : {x // n x ≠ 0} ↦ Checked.inv (f x) (hf x)) =O[cofinite]
      fun x : {x // n x ≠ 0} ↦ Checked.inv (|(n x : ℝ)| ^ a)
        (Real.rpow_pos_of_pos (abs_pos.mpr (Int.cast_ne_zero.mpr x.2)) a).ne'.isUnit) :
    Summable fun x ↦ Checked.inv (f x) (hf x) := by
  have hs : {x | n x = 0}.Finite :=
    (Set.finite_singleton (0 : ℤ)).preimage (fun _ _ _ _ h ↦ hn h)
  apply hs.summable_compl_iff.mp
  apply summable_of_isBigO (g := fun x : {x // n x ≠ 0} ↦
    Checked.inv (|(n x : ℝ)| ^ a)
      (Real.rpow_pos_of_pos (abs_pos.mpr (Int.cast_ne_zero.mpr x.2)) a).ne'.isUnit) ?_ hbound
  refine ((Real.summable_abs_int_rpow hab).comp_injective
    (hn.comp Subtype.coe_injective)).congr fun x ↦ ?_
  exact Real.rpow_neg (abs_nonneg _) a

/-- For `2 ≤ k`, the inverse power of `c z + d` is summable on any injectively indexed
integer domain on which the denominator is invertible. -/
lemma linear_right_summable (z : ℂ) (c : ℤ) {k : ℤ} (hk : 2 ≤ k)
    {D : Type*} (d : D → ℤ) (hd : Function.Injective d)
    {hpower : ∀ x, IsUnit (Checked.zpow (c * z + d x) k (by intro h; omega))} :
    Summable fun x ↦ Checked.inv
      (Checked.zpow (c * z + d x) k (by intro h; omega)) (hpower x) := by
  apply summable_inv_of_isBigO_rpow_inv (a := k) (by norm_cast) d hd
  lift k to ℕ using by lia
  have hlinear (x : {x // d x ≠ 0}) : IsUnit (c * z + d x) :=
    (isUnit_pow_iff (by omega : k ≠ 0)).mp (hpower x)
  have hcast (x : {x // d x ≠ 0}) : IsUnit (d x : ℝ) :=
    (Int.cast_ne_zero.mpr x.2).isUnit
  simpa only [zpow_natCast₀, Int.cast_natCast, Real.rpow_natCast, inv_pow₀, abs_inv] using
    (linear_inv_isBigO_right c z (fun x : {x // d x ≠ 0} ↦ d x)
      (hd.comp Subtype.coe_injective).tendsto_cofinite
      (hlinear := hlinear) (hcast := hcast)).abs_right.pow k

/-- For `2 ≤ k` and nonzero `z`, the inverse power of `c z + d` is summable on any
injectively indexed integer domain on which the denominator is invertible. -/
lemma linear_left_summable {z : ℂ} (hz : z ≠ 0) (d : ℤ) {k : ℤ} (hk : 2 ≤ k)
    {D : Type*} (c : D → ℤ) (hc : Function.Injective c)
    {hpower : ∀ x, IsUnit (Checked.zpow (c x * z + d) k (by intro h; omega))} :
    Summable fun x ↦ Checked.inv
      (Checked.zpow (c x * z + d) k (by intro h; omega)) (hpower x) := by
  apply summable_inv_of_isBigO_rpow_inv (a := k) (by norm_cast) c hc
  lift k to ℕ using (by lia)
  have hlinear (x : {x // c x ≠ 0}) : IsUnit (c x * z + d) :=
    (isUnit_pow_iff (by omega : k ≠ 0)).mp (hpower x)
  have hcast (x : {x // c x ≠ 0}) : IsUnit (c x : ℝ) :=
    (Int.cast_ne_zero.mpr x.2).isUnit
  simpa only [zpow_natCast₀, Int.cast_natCast, Real.rpow_natCast, inv_pow₀, abs_inv] using
    (linear_inv_isBigO_left d hz (fun x : {x // c x ≠ 0} ↦ c x)
      (hc.comp Subtype.coe_injective).tendsto_cofinite
      (hlinear := hlinear) (hcast := hcast)).abs_right.pow k

lemma summable_linear_sub_mul_linear_add (z : ℂ) (c₁ c₂ : ℤ)
    {D : Type*} (n : D → ℤ) (hn : Function.Injective n)
    {hprod : ∀ x, IsUnit ((c₁ * z - n x) * (c₂ * z + n x))} :
    Summable fun x ↦ Checked.inv ((c₁ * z - n x) * (c₂ * z + n x)) (hprod x) := by
  apply summable_inv_of_isBigO_rpow_inv (a := 2) (by norm_cast) n hn
  have h₁ (x : {x // n x ≠ 0}) : IsUnit (c₁ * z - n x) :=
    ((Commute.all _ _).isUnit_mul_iff.mp (hprod x)).1
  have h₂ (x : {x // n x ≠ 0}) : IsUnit (c₂ * z + n x) :=
    ((Commute.all _ _).isUnit_mul_iff.mp (hprod x)).2
  have hcast (x : {x // n x ≠ 0}) : IsUnit (n x : ℝ) :=
    (Int.cast_ne_zero.mpr x.2).isUnit
  have hneg : Function.Injective (fun x : {x // n x ≠ 0} ↦ -n x) :=
    neg_injective.comp (hn.comp Subtype.coe_injective)
  have hleft := linear_inv_isBigO_right c₁ z (fun x : {x // n x ≠ 0} ↦ -n x)
    hneg.tendsto_cofinite
    (hlinear := fun x ↦ by simpa only [Int.cast_neg, ← sub_eq_add_neg] using h₁ x)
    (hcast := fun x ↦ by simpa only [Int.cast_neg] using (hcast x).neg)
  have hright := linear_inv_isBigO_right c₂ z (fun x : {x // n x ≠ 0} ↦ n x)
    (hn.comp Subtype.coe_injective).tendsto_cofinite (hlinear := h₂) (hcast := hcast)
  simpa only [Real.rpow_two, pow_two, mul_inv₀, Int.cast_neg, sub_eq_add_neg,
    inv_neg₀, abs_inv, abs_neg] using hleft.abs_right.mul hright.abs_right

lemma summable_linear_right_add_one_mul_linear_right (z : ℂ) (c₁ c₂ : ℤ)
    {D : Type*} (n : D → ℤ) (hn : Function.Injective n)
    {hprod : ∀ x, IsUnit ((c₁ * z + n x + 1) * (c₂ * z + n x))} :
    Summable fun x ↦ Checked.inv ((c₁ * z + n x + 1) * (c₂ * z + n x)) (hprod x) := by
  apply summable_inv_of_isBigO_rpow_inv (a := 2) (by norm_cast) n hn
  have h₁ (x : {x // n x ≠ 0}) : IsUnit (c₁ * z + n x + 1) :=
    ((Commute.all _ _).isUnit_mul_iff.mp (hprod x)).1
  have h₂ (x : {x // n x ≠ 0}) : IsUnit (c₂ * z + n x) :=
    ((Commute.all _ _).isUnit_mul_iff.mp (hprod x)).2
  have hcast (x : {x // n x ≠ 0}) : IsUnit (n x : ℝ) :=
    (Int.cast_ne_zero.mpr x.2).isUnit
  have hleft := linear_inv_isBigO_right_add c₁ 1 z (fun x : {x // n x ≠ 0} ↦ n x)
    (hn.comp Subtype.coe_injective).tendsto_cofinite
    (hlinear := fun x ↦ by simpa only [Int.cast_one] using h₁ x) (hcast := hcast)
  have hright := linear_inv_isBigO_right c₂ z (fun x : {x // n x ≠ 0} ↦ n x)
    (hn.comp Subtype.coe_injective).tendsto_cofinite (hlinear := h₂) (hcast := hcast)
  simpa only [Real.rpow_two, pow_two, mul_inv₀, abs_inv, Int.cast_one] using
    hleft.abs_right.mul hright.abs_right

lemma summable_linear_left_mul_linear_left {z : ℂ} (hz : z ≠ 0) (c₁ c₂ : ℤ)
    {D : Type*} (n : D → ℤ) (hn : Function.Injective n)
    {hprod : ∀ x, IsUnit ((n x * z + c₁) * (n x * z + c₂))} :
    Summable fun x ↦ Checked.inv ((n x * z + c₁) * (n x * z + c₂)) (hprod x) := by
  apply summable_inv_of_isBigO_rpow_inv (a := 2) (by norm_cast) n hn
  have h₁ (x : {x // n x ≠ 0}) : IsUnit (n x * z + c₁) :=
    ((Commute.all _ _).isUnit_mul_iff.mp (hprod x)).1
  have h₂ (x : {x // n x ≠ 0}) : IsUnit (n x * z + c₂) :=
    ((Commute.all _ _).isUnit_mul_iff.mp (hprod x)).2
  have hcast (x : {x // n x ≠ 0}) : IsUnit (n x : ℝ) :=
    (Int.cast_ne_zero.mpr x.2).isUnit
  have hleft := linear_inv_isBigO_left c₁ hz (fun x : {x // n x ≠ 0} ↦ n x)
    (hn.comp Subtype.coe_injective).tendsto_cofinite (hlinear := h₁) (hcast := hcast)
  have hright := linear_inv_isBigO_left c₂ hz (fun x : {x // n x ≠ 0} ↦ n x)
    (hn.comp Subtype.coe_injective).tendsto_cofinite (hlinear := h₂) (hcast := hcast)
  simpa only [Real.rpow_two, pow_two, mul_inv₀, abs_inv, Int.cast_one] using
    hleft.abs_right.mul hright.abs_right

private lemma aux_isBigO_linear (z : ℍ) (a b : ℤ) {D : Type*}
    (m : D → Fin 2 → ℤ) (l : Filter D)
    {hlinear : ∀ x, IsUnit (((m x 0 : ℂ) + a) * z + m x 1 + b)}
    {hnorm : ∀ x, IsUnit ‖![m x 0 + a, m x 1 + b]‖} :
    (fun x ↦ Checked.inv (((m x 0 : ℂ) + a) * z + m x 1 + b) (hlinear x)) =O[l]
    fun x ↦ Checked.inv ‖![m x 0 + a, m x 1 + b]‖ (hnorm x) := by
  rw [Asymptotics.isBigO_iff]
  have h0 : z ∈ verticalStrip |z.re| (z.im) := by simp [mem_verticalStrip_iff]
  have hr := r_pos ⟨⟨|z.re|, z.im⟩, z.2⟩
  use (r ⟨⟨|z.re|, z.im⟩, z.2⟩)⁻¹
  filter_upwards with x
  have hx : ![m x 0 + a, m x 1 + b] ≠ 0 := norm_ne_zero_iff.mp (hnorm x).ne_zero
  have hbound : r ⟨⟨|z.re|, z.im⟩, z.2⟩ * ‖![m x 0 + a, m x 1 + b]‖ ≤
      ‖((m x 0 : ℂ) + a) * z + m x 1 + b‖ := by
    refine (mul_le_mul_of_nonneg_right (r_lower_bound_on_verticalStrip z z.2 h0)
      (norm_nonneg _)).trans ?_
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Int.cast_add, add_assoc] using r_mul_max_le z hx
  simp only [norm_inv, norm_norm]
  have hunit := hr.ne'.isUnit.mul (hnorm x)
  rw [← mul_inv₀ (hab := hunit)]
  exact (inv_le_inv₀ (norm_pos_iff.mpr (hlinear x).ne_zero)
    (mul_pos hr (norm_pos_iff.mpr hx))).mpr hbound

lemma isLittleO_const_left_of_properSpace_of_discreteTopology
    {α : Type*} (a : α) [NormedAddCommGroup α] [DiscreteTopology α]
    [ProperSpace α] : (fun _ : α ↦ a) =o[cofinite] (‖·‖) := by
  simpa [isLittleO_const_left, Function.comp_def] using
    .inr <| tendsto_norm_comp_cofinite_atTop_of_isClosedEmbedding IsClosedEmbedding.id

lemma vec_add_const_isTheta (a b : ℤ) {D : Type*} {l : Filter D}
    (m : D → Fin 2 → ℤ) (hm : Tendsto m l cofinite)
    {hshift : ∀ x, IsUnit ‖![m x 0 + a, m x 1 + b]‖}
    {hnorm : ∀ x, IsUnit ‖m x‖} :
    (fun x ↦ Checked.inv ‖![m x 0 + a, m x 1 + b]‖ (hshift x)) =Θ[l]
      (fun x ↦ Checked.inv ‖m x‖ (hnorm x)) := by
  have (x : Fin 2 → ℤ) : ![x 0 + a, x 1 + b] = x + ![a, b] := List.ofFn_inj.mp rfl
  apply IsTheta.inv
  have h : (fun x : Fin 2 → ℤ ↦ x + ![a, b]) =Θ[cofinite] (fun x ↦ x) :=
    IsTheta.add_isLittleO isTheta_rfl
      (isLittleO_const_left_of_properSpace_of_discreteTopology ![a, b]).of_norm_right
  simpa only [Function.comp_def, this] using (h.norm_left.norm_right.comp_tendsto hm)

lemma isBigO_linear_add_const_vec (z : ℍ) (a b : ℤ) {D : Type*} {l : Filter D}
    (m : D → Fin 2 → ℤ) (hm : Tendsto m l cofinite)
    {hlinear : ∀ x, IsUnit (((m x 0 : ℂ) + a) * z + m x 1 + b)}
    {hnorm : ∀ x, IsUnit ‖m x‖} :
    (fun x ↦ Checked.inv (((m x 0 : ℂ) + a) * z + m x 1 + b) (hlinear x)) =O[l]
      (fun x ↦ Checked.inv ‖m x‖ (hnorm x)) := by
  have hshift (x : D) : IsUnit ‖![m x 0 + a, m x 1 + b]‖ := by
    apply IsUnit.mk0
    rw [norm_ne_zero_iff]
    intro hx
    have ha : m x 0 + a = 0 := by simpa using congrFun hx 0
    have hb : m x 1 + b = 0 := by simpa using congrFun hx 1
    apply (hlinear x).ne_zero
    calc
      ((m x 0 : ℂ) + a) * z + m x 1 + b =
          ((m x 0 + a : ℤ) : ℂ) * z + ((m x 1 + b : ℤ) : ℂ) := by
        push_cast
        ring
      _ = 0 := by simp [ha, hb]
  exact (aux_isBigO_linear z a b m l (hnorm := hshift)).trans
    (vec_add_const_isTheta a b m hm (hshift := hshift)).isBigO

/-- A function on an injectively indexed lattice domain with a power bound of exponent
greater than two is summable. The comparison is only taken at nonzero lattice coordinates. -/
lemma summable_of_isBigO_rpow_norm {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {D : Type*} {f : D → E} {a : ℝ} (hab : 2 < a)
    (m : D → Fin 2 → ℤ) (hm : Function.Injective m)
    (hf : (fun x : {x // m x ≠ 0} ↦ f x) =O[cofinite]
      fun x : {x // m x ≠ 0} ↦ Checked.inv (‖m x‖ ^ a)
        (Real.rpow_pos_of_pos (norm_pos_iff.mpr x.2) a).ne'.isUnit) : Summable f := by
  have hs : {x | m x = 0}.Finite :=
    (Set.finite_singleton (0 : Fin 2 → ℤ)).preimage (fun _ _ _ _ h ↦ hm h)
  apply hs.summable_compl_iff.mp
  apply summable_of_isBigO (g := fun x : {x // m x ≠ 0} ↦ Checked.inv (‖m x‖ ^ a)
    (Real.rpow_pos_of_pos (norm_pos_iff.mpr x.2) a).ne'.isUnit) ?_ hf
  refine ((summable_one_div_norm_rpow hab).comp_injective
    (hm.comp Subtype.coe_injective)).congr fun x ↦ ?_
  exact Real.rpow_neg (norm_nonneg (m x)) a

end EisensteinSeries
