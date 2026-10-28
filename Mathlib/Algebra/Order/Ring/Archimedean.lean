/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang, Violeta Hernández Palacios
-/
module

public import Mathlib.Algebra.Order.Archimedean.Class
public import Mathlib.Algebra.Order.Group.DenselyOrdered
public import Mathlib.Algebra.Order.Ring.Basic
public import Mathlib.Algebra.Order.Hom.Ring
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Archimedean classes of a linearly ordered ring

The archimedean classes of a linearly ordered ring can be given the structure of an `AddCommMonoid`,
by defining

* `0 = mk 1`
* `mk x + mk y = mk (x * y)`

For a linearly ordered field, we can define a negative as

* `-mk x = mk x⁻¹` for `x ≠ 0`, and `-⊤ = ⊤` for the class `⊤ = mk 0`

which turns them into a `LinearOrderedAddCommGroupWithTop`.

## Implementation notes

We give Archimedean class an additive structure, rather than a multiplicative one, for the following
reasons:

* In the ring version of Hahn embedding theorem, the subtype `FiniteArchimedeanClass R` of non-top
  elements in `ArchimedeanClass R` naturally becomes the additive abelian group for the ring
  `ℝ⟦FiniteArchimedeanClass R⟧`.
* The order we defined on `ArchimedeanClass R` matches the order on `AddValuation`, rather than the
  one on `Valuation`.
-/

@[expose] public section

variable {R S : Type*} [LinearOrder R] [LinearOrder S]

namespace ArchimedeanClass
section Ring
variable [CommRing R]

section IsOrderedRing
variable [IsStrictOrderedRing R]

instance : Zero (ArchimedeanClass R) where
  zero := mk 1

@[simp] theorem mk_one : mk (1 : R) = 0 := rfl

@[simp] lemma top_ne_zero : (⊤ : ArchimedeanClass R) ≠ 0 := by simp [← mk_one]
@[simp] lemma zero_ne_top : 0 ≠ (⊤ : ArchimedeanClass R) := top_ne_zero.symm

private theorem mk_mul_le_of_le {x₁ y₁ x₂ y₂ : R} (hx : mk x₁ ≤ mk x₂) (hy : mk y₁ ≤ mk y₂) :
    mk (x₁ * y₁) ≤ mk (x₂ * y₂) := by
  obtain ⟨m, hm⟩ := hx
  obtain ⟨n, hn⟩ := hy
  use m * n
  convert mul_le_mul hm hn (abs_nonneg _) (nsmul_nonneg (abs_nonneg _) _) <;>
    simp_rw [ArchimedeanOrder.val_of, abs_mul]
  ring

/-- Multiplication in `R` transfers to addition in `ArchimedeanClass R`. -/
instance : Add (ArchimedeanClass R) where
  add := lift₂ (fun x y ↦ .mk <| x * y) fun _ _ _ _ hx hy ↦ by
    exact (mk_mul_le_of_le hx.le hy.le).antisymm (mk_mul_le_of_le hx.ge hy.ge)

@[simp] theorem mk_mul (x y : R) : mk (x * y) = mk x + mk y := rfl

instance : SMul ℕ (ArchimedeanClass R) where
  smul n := lift (fun x ↦ mk (x ^ n)) fun x y h ↦ by
    induction n with
    | zero => simp
    | succ n IH => simp_rw [pow_succ, mk_mul, IH, h]

@[simp] theorem mk_pow (n : ℕ) (x : R) : mk (x ^ n) = n • mk x := rfl

instance : AddCommMagma (ArchimedeanClass R) where
  add_comm x y := by
    induction x with | mk x
    induction y with | mk y
    rw [← mk_mul, mul_comm, mk_mul]

private theorem zero_add' (x : ArchimedeanClass R) : 0 + x = x := by
  induction x with | mk x
  rw [← mk_one, ← mk_mul, one_mul]

private theorem add_assoc' (x y z : ArchimedeanClass R) : x + y + z = x + (y + z) := by
  induction x with | mk x
  induction y with | mk y
  induction z with | mk z
  simp_rw [← mk_mul, mul_assoc]

instance : AddCommMonoid (ArchimedeanClass R) where
  add_assoc := private add_assoc'
  zero_add := private zero_add'
  add_zero x := private add_comm x _ ▸ zero_add' x
  nsmul_zero x := by induction x with | mk x => rw [← mk_pow, pow_zero, mk_one]
  nsmul_succ n x := by induction x with | mk x => rw [← mk_pow, pow_succ, mk_mul, mk_pow]

instance : IsOrderedAddMonoid (ArchimedeanClass R) where
  add_le_add_left x y h z := by
    induction x with | mk x
    induction y with | mk y
    induction z with | mk z
    rw [← mk_mul, ← mk_mul]
    exact mk_mul_le_of_le h le_rfl

lemma isAddRegular_mk {x : R} (hx : x ≠ 0) : IsAddRegular (mk x) := by
  rw [← isAddLeftRegular_iff_isAddRegular]
  rintro y z hyz
  induction y with | mk y =>
  induction z with | mk z =>
  simpa [← mk_mul, mk_eq_mk, mul_left_comm _ (|x|), abs_pos.2 hx] using hyz

noncomputable instance : LinearOrderedAddCommMonoidWithTop (ArchimedeanClass R) where
  top_add' x := by induction x with | mk x => rw [← mk_zero, ← mk_mul, zero_mul]
  isAddLeftRegular_of_ne_top x := by induction x with | mk x => simp +contextual [isAddRegular_mk]

variable (R) in
/-- `ArchimedeanClass.mk` defines an `AddValuation` on the ring `R`. -/
noncomputable def addValuation : AddValuation R (ArchimedeanClass R) := AddValuation.of mk
  rfl rfl min_le_mk_add mk_mul

@[simp] theorem addValuation_apply (a : R) : addValuation R a = mk a := rfl

variable {S : Type*} [LinearOrder S] [CommRing S] [IsStrictOrderedRing S]

@[simp]
theorem orderHom_zero (f : S →+o R) : orderHom f 0 = mk (f 1) := by
  rw [← mk_one, orderHom_mk]

@[simp]
theorem mk_eq_zero_of_archimedean [Archimedean S] {x : S} (h : x ≠ 0) : mk x = 0 :=
  mk_eq_mk_of_archimedean h one_ne_zero

theorem eq_zero_or_top_of_archimedean [Archimedean S] (x : ArchimedeanClass S) : x = 0 ∨ x = ⊤ := by
  induction x with | mk x
  obtain rfl | h := eq_or_ne x 0 <;> simp_all

/-- See `mk_map_of_archimedean'` for a version taking `M →+*o R`. -/
theorem mk_map_of_archimedean [Archimedean S] (f : S →+o R) {x : S} (h : x ≠ 0) :
    mk (f x) = mk (f 1) := by
  rw [← orderHom_mk, mk_eq_zero_of_archimedean h, orderHom_zero]

/-- See `mk_map_of_archimedean` for a version taking `M →+o R`. -/
theorem mk_map_of_archimedean' [Archimedean S] (f : S →+*o R) {x : S} (h : x ≠ 0) :
    mk (f x) = 0 := by
  simpa using mk_map_of_archimedean f.toOrderAddMonoidHom h

theorem mk_le_mk_add_of_archimedean [Archimedean S] (f : S →+*o R) (x : R) (y : S) :
    mk x ≤ mk (f y) + mk x := by
  obtain rfl | hy := eq_or_ne y 0
  · simp
  · rw [mk_map_of_archimedean' f hy, zero_add]

theorem mk_le_add_mk_of_archimedean [Archimedean S] (f : S →+*o R) (x : R) (y : S) :
    mk x ≤ mk x + mk (f y) := by
  rw [add_comm]
  exact mk_le_mk_add_of_archimedean f x y

theorem mk_map_nonneg_of_archimedean [Archimedean S] (f : S →+*o R) (y : S) : 0 ≤ mk (f y) := by
  simpa using mk_le_mk_add_of_archimedean f 1 y

theorem lt_of_pos_of_archimedean [Archimedean S] (f : S →+*o R)
    {x : R} (hx : 0 < mk x) {y : S} (hy : 0 < y) : x < f y := by
  apply lt_of_mk_lt_mk_of_nonneg
  · rwa [mk_map_of_archimedean' f hy.ne']
  · simpa using f.monotone' hy.le

theorem lt_of_neg_of_archimedean [Archimedean S] (f : S →+*o R)
    {x : R} (hx : 0 < mk x) {y : S} (hy : y < 0) : f y < x := by
  apply lt_of_mk_lt_mk_of_nonpos
  · rwa [mk_map_of_archimedean' f hy.ne]
  · simpa using f.monotone' hy.le

@[simp]
theorem mk_intCast {n : ℤ} (h : n ≠ 0) : mk (n : S) = 0 := by
  obtain _ | _ := subsingleton_or_nontrivial S
  · exact Subsingleton.allEq ..
  · exact mk_map_of_archimedean' ⟨Int.castRingHom S, fun _ ↦ by simp⟩ h

theorem mk_intCast_nonneg (n : ℤ) : 0 ≤ mk (n : S) := by
  obtain rfl | hn := eq_or_ne n 0
  · simp
  · rw [mk_intCast hn]

@[simp]
theorem mk_natCast {n : ℕ} : n ≠ 0 → mk (n : S) = 0 :=
  mod_cast mk_intCast (n := n)

@[simp]
theorem mk_ofNat {n : ℕ} [n.AtLeastTwo] : mk (ofNat(n) : S) = 0 :=
  mod_cast mk_intCast (n := n) (mod_cast NeZero.ne n)

theorem mk_natCast_nonneg (n : ℕ) : 0 ≤ mk (n : S) :=
  mod_cast mk_intCast_nonneg n

theorem exists_nat_ge_of_mk_nonneg {x : R} (hx : 0 ≤ mk x) : ∃ n : ℕ, x ≤ n := by
  obtain ⟨n, hn⟩ := hx
  refine ⟨n, le_of_abs_le ?_⟩
  simpa using hn

theorem exists_nat_gt_of_mk_nonneg {x : R} (hx : 0 ≤ mk x) : ∃ n : ℕ, x < n := by
  obtain ⟨n, hn⟩ := exists_nat_ge_of_mk_nonneg hx
  refine ⟨n + 1, hn.trans_lt ?_⟩
  simp

theorem exists_int_ge_of_mk_nonneg {x : R} (hx : 0 ≤ mk x) : ∃ n : ℤ, x ≤ n := by
  obtain ⟨n, hn⟩ := exists_nat_ge_of_mk_nonneg hx
  exact ⟨n, mod_cast hn⟩

theorem exists_int_gt_of_mk_nonneg {x : R} (hx : 0 ≤ mk x) : ∃ n : ℤ, x < n := by
  obtain ⟨n, hn⟩ := exists_nat_gt_of_mk_nonneg hx
  exact ⟨n, mod_cast hn⟩

theorem exists_int_le_of_mk_nonneg {x : R} (hx : 0 ≤ mk x) : ∃ n : ℤ, n ≤ x := by
  obtain ⟨n, hn⟩ := exists_nat_ge_of_mk_nonneg (mk_neg x ▸ hx)
  use -n
  simpa [neg_le]

theorem exists_int_lt_of_mk_nonneg {x : R} (hx : 0 ≤ mk x) : ∃ n : ℤ, n < x := by
  obtain ⟨n, hn⟩ := exists_nat_gt_of_mk_nonneg (mk_neg x ▸ hx)
  use -n
  simpa [neg_lt]

theorem mk_nonneg_of_le_of_le_of_archimedean [Archimedean S] (f : S →+*o R) {x : R} {r s : S}
    (hr : f r ≤ x) (hs : x ≤ f s) : 0 ≤ mk x := by
  apply (min_le_mk_of_le_of_le hr hs).trans'
  simp [mk_map_nonneg_of_archimedean]

end IsOrderedRing

section IsStrictOrderedRing
variable [IsStrictOrderedRing R]

theorem add_left_cancel_of_ne_top {x y z : ArchimedeanClass R} (hx : x ≠ ⊤) (h : x + y = x + z) :
    y = z := by
  simp_all

theorem add_right_cancel_of_ne_top {x y z : ArchimedeanClass R} (hx : x ≠ ⊤) (h : y + x = z + x) :
    y = z := by
  simp_rw [← add_comm x] at h
  exact add_left_cancel_of_ne_top hx h

theorem mk_le_mk_iff_denselyOrdered [Ring S] [IsStrictOrderedRing S]
    [DenselyOrdered R] [Archimedean R] {x y : S} (f : R →+* S) (hf : StrictMono f) :
    mk x ≤ mk y ↔ ∃ q : R, 0 < f q ∧ f q * |y| ≤ |x| := by
  have H {q} : 0 < f q ↔ 0 < q := by simpa using hf.lt_iff_lt (a := 0)
  constructor
  · rintro ⟨(_ | n), hn⟩
    · simp_all [exists_zero_lt]
    · obtain ⟨q, hq₀, hq⟩ := exists_nsmul_lt_of_pos (one_pos (α := R)) (n + 1)
      refine ⟨q, H.2 hq₀, le_of_mul_le_mul_left ?_ n.cast_add_one_pos⟩
      simpa [← mul_assoc] using mul_le_mul (hf hq).le hn (abs_nonneg y) (by simp)
  · rintro ⟨q, hq₀, hq⟩
    have hq₀' := H.1 hq₀
    obtain ⟨n, hn⟩ := exists_lt_nsmul hq₀' 1
    refine ⟨n, le_of_mul_le_mul_left ?_ hq₀⟩
    have h : 0 ≤ f (n • q) := by
      rw [← f.map_zero]
      exact hf.monotone (nsmul_nonneg hq₀'.le n)
    simpa [mul_comm, mul_assoc] using mul_le_mul (hf hn).le hq (mul_nonneg hq₀.le (abs_nonneg y)) h

end IsStrictOrderedRing
end Ring

section Field
variable [Field R] [IsOrderedRing R]

/-- Negation of Archimedean classes: `-mk x = mk x⁻¹` for `x ≠ 0` (`ArchimedeanClass.mk_inv`).
The top class `⊤ = mk 0` has no invertible representative; its negation is `⊤`, the convention
`neg_top` of `LinearOrderedAddCommGroupWithTop`. -/
noncomputable instance : Neg (ArchimedeanClass R) where
  neg := lift (fun x ↦ if hx : x = 0 then ⊤ else mk x⁻¹) fun x y h ↦ by
    obtain rfl | hx := eq_or_ne x 0
    · obtain rfl : y = 0 := by simpa using h.symm
      rfl
    have hy : y ≠ 0 := by
      rintro rfl
      exact hx (by simpa using h)
    rw [dite_eq_right hx, dite_eq_right hy]
    have hx' : mk x ≠ ⊤ := by simpa using hx
    apply add_left_cancel_of_ne_top hx'
    nth_rw 2 [h]
    rw [← mk_mul, ← mk_mul, mul_inv_cancel₀, mul_inv_cancel₀]

@[simp] theorem mk_inv (x : R) {hx : IsUnit x} : mk x⁻¹ = -mk x := by
  change mk x⁻¹ = if hx : x = 0 then ⊤ else mk x⁻¹
  rw [dite_eq_right hx.ne_zero]

/-- Integer multiples of Archimedean classes, from natural multiples and negation. -/
noncomputable instance : SMul ℤ (ArchimedeanClass R) where
  smul := zsmulRec (· • ·)

noncomputable instance : LinearOrderedAddCommGroupWithTop (ArchimedeanClass R) where
  neg_top := dite_eq_left rfl
  top_add' := by simp
  add_neg_cancel_of_ne_top x h := by
    induction x with | mk x
    have hx : x ≠ 0 := mk_eq_top_iff.not.1 h
    rw [← mk_inv x (hx := hx.isUnit), ← mk_mul, mul_inv_cancel₀, mk_one]
  zsmul_zero' x := zero_nsmul x
  zsmul_succ' n x := succ_nsmul x n
  zsmul_neg' _ _ := rfl

@[simp] theorem mk_zpow (n : ℤ) (x : R) {h : n < 0 → IsUnit x} : mk (x ^ n) = n • mk x := by
  cases n with
  | ofNat k => exact mk_pow k x
  | negSucc k =>
    rw [zpow_negSucc₀, mk_inv, mk_pow]
    rfl

@[simp]
theorem mk_div (x y : R) {hy : IsUnit y} : mk (x / y) = mk x - mk y := by
  rw [div_eq_mul_inv₀, mk_mul, mk_inv]
  exact (sub_eq_add_neg _ _).symm

@[simp]
theorem mk_ratCast {q : ℚ} (h : q ≠ 0) : mk (q : R) = 0 := by
  simpa using mk_map_of_archimedean ⟨(Rat.castHom R).toAddMonoidHom, fun _ ↦ by simp⟩ h

theorem mk_ratCast_nonneg (q : ℚ) : 0 ≤ mk (q : R) := by
  obtain rfl | hn := eq_or_ne q 0
  · simp
  · rw [mk_ratCast hn]

theorem mk_le_mk_iff_ratCast {x y : R} : mk x ≤ mk y ↔ ∃ q : ℚ, 0 < q ∧ q * |y| ≤ |x| := by
  simpa using mk_le_mk_iff_denselyOrdered (Rat.castHom _) Rat.cast_strictMono (x := x)

end Field
end ArchimedeanClass
