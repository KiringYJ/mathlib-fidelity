/-
Copyright (c) 2014 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Leonardo de Moura, Mario Carneiro, Floris van Doorn
-/
module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Order.Field.Checked
public import Mathlib.Algebra.Order.Field.Halves
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.Order.GroupWithZero.OrderIso
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Data.Set.Monotone
public import Mathlib.Order.Bounds.OrderIso
public import Mathlib.Tactic.Positivity.Core

/-!
# Lemmas about (linear) ordered (semi)fields
-/

@[expose] public section


open Function OrderDual

variable {α β : Type*}

section PartialOrderedSemifield

variable [Semifield α] [PartialOrder α] [PosMulReflectLT α] {a b c d e : α} {m n : ℤ}
variable {haUnit : IsUnit a} {hbUnit : IsUnit b} {hcUnit : IsUnit c}
  {hdUnit : IsUnit d} {heUnit : IsUnit e}

attribute [local instance] PosMulReflectLT.toMulPosReflectLT

/-!
### Relating one division and involving `1`
-/

@[bound]
theorem le_div_self (ha : 0 ≤ a) (hb₀ : 0 < b) (hb₁ : b ≤ 1) : a ≤ a / b := by
  simpa only [Checked.div_one] using
    Checked.div_le_div_of_nonneg_left (ha := hbUnit) (hb := isUnit_one) ha hb₀ hb₁

theorem one_le_div (hb : 0 < b) : 1 ≤ a / b ↔ b ≤ a := by rw [Checked.le_div_iff hb, one_mul]

theorem div_le_one (hb : 0 < b) : a / b ≤ 1 ↔ a ≤ b := by rw [Checked.div_le_iff hb, one_mul]

theorem one_lt_div (hb : 0 < b) : 1 < a / b ↔ b < a := by rw [Checked.lt_div_iff hb, one_mul]

theorem div_lt_one (hb : 0 < b) : a / b < 1 ↔ a < b := by rw [Checked.div_lt_iff hb, one_mul]

theorem one_div_le (ha : 0 < a) (hb : 0 < b) : 1 / a ≤ b ↔ 1 / b ≤ a := by
  rw [Checked.div_le_iff ha, Checked.div_le_iff hb, mul_comm]

theorem one_div_lt (ha : 0 < a) (hb : 0 < b) : 1 / a < b ↔ 1 / b < a := by
  rw [Checked.div_lt_iff ha, Checked.div_lt_iff hb, mul_comm]

theorem le_one_div (ha : 0 < a) (hb : 0 < b) : a ≤ 1 / b ↔ b ≤ 1 / a := by
  rw [Checked.le_div_iff hb, Checked.le_div_iff ha, mul_comm]

theorem lt_one_div (ha : 0 < a) (hb : 0 < b) : a < 1 / b ↔ b < 1 / a := by
  rw [Checked.lt_div_iff hb, Checked.lt_div_iff ha, mul_comm]

@[bound] lemma Bound.one_lt_div_of_pos_of_lt (b0 : 0 < b) : b < a → 1 < a / b := (one_lt_div b0).mpr

@[bound] lemma Bound.div_lt_one_of_pos_of_lt (b0 : 0 < b) : a < b → a / b < 1 := (div_lt_one b0).mpr

/-!
### Relating two divisions, involving `1`
-/

theorem one_div_le_one_div_of_le (ha : 0 < a) (h : a ≤ b) : 1 / b ≤ 1 / a := by
  simpa only [Checked.one_div] using
    (Checked.inv_le_inv (ha := hbUnit) (hb := haUnit) (ha.trans_le h) ha).mpr h

theorem one_div_lt_one_div_of_lt (ha : 0 < a) (h : a < b) : 1 / b < 1 / a := by
  simpa only [Checked.one_div] using
    (Checked.inv_lt_inv (ha := hbUnit) (hb := haUnit) (ha.trans h) ha).mpr h

theorem le_of_one_div_le_one_div (ha : 0 < a) (h : 1 / a ≤ 1 / b) : b ≤ a := by
  have hb : 0 < b := (Checked.inv_pos (ha := hbUnit)).mp <|
    lt_of_lt_of_le ((Checked.inv_pos (ha := haUnit)).mpr ha)
      (by simpa only [Checked.one_div] using h)
  exact (Checked.inv_le_inv ha hb).mp (by simpa only [Checked.one_div] using h)

theorem lt_of_one_div_lt_one_div (ha : 0 < a) (h : 1 / a < 1 / b) : b < a := by
  have hb : 0 < b := (Checked.inv_pos (ha := hbUnit)).mp <|
    lt_trans ((Checked.inv_pos (ha := haUnit)).mpr ha)
      (by simpa only [Checked.one_div] using h)
  exact (Checked.inv_lt_inv ha hb).mp (by simpa only [Checked.one_div] using h)

variable [IsStrictOrderedRing α]

@[bound]
theorem div_le_self (ha : 0 ≤ a) (hb : 1 ≤ b) : a / b ≤ a := by
  simpa only [Checked.div_one] using
    Checked.div_le_div_of_nonneg_left (ha := isUnit_one) (hb := hbUnit) ha zero_lt_one hb

@[bound]
theorem div_lt_self (ha : 0 < a) (hb : 1 < b) : a / b < a := by
  simpa only [Checked.div_one] using
    Checked.div_lt_div_of_pos_left (ha := isUnit_one) (hb := hbUnit) ha zero_lt_one hb

omit [IsStrictOrderedRing α] in
/-- For the single implications with fewer assumptions, see `one_div_le_one_div_of_le` and
  `le_of_one_div_le_one_div` -/
theorem one_div_le_one_div (ha : 0 < a) (hb : 0 < b) : 1 / a ≤ 1 / b ↔ b ≤ a :=
  by simpa only [Checked.one_div] using (Checked.inv_le_inv ha hb)

omit [IsStrictOrderedRing α] in
/-- For the single implications with fewer assumptions, see `one_div_lt_one_div_of_lt` and
  `lt_of_one_div_lt_one_div` -/
theorem one_div_lt_one_div (ha : 0 < a) (hb : 0 < b) : 1 / a < 1 / b ↔ b < a :=
  by simpa only [Checked.one_div] using (Checked.inv_lt_inv ha hb)

omit [IsStrictOrderedRing α] in
theorem one_lt_one_div (h1 : 0 < a) (h2 : a < 1) : 1 < 1 / a := by
  exact (one_lt_div h1).mpr h2

omit [IsStrictOrderedRing α] in
theorem one_le_one_div (h1 : 0 < a) (h2 : a ≤ 1) : 1 ≤ 1 / a := by
  exact (one_le_div h1).mpr h2

/-!
### Results about halving.
The equalities also hold in semifields of characteristic `0`.
-/

/-!
### Miscellaneous lemmas
-/

@[simp] lemma div_pos_iff_of_pos_left (ha : 0 < a) : 0 < a / b ↔ 0 < b := by
  simp only [Checked.div_eq_mul_inv, mul_pos_iff_of_pos_left ha, Checked.inv_pos]

@[simp] lemma div_pos_iff_of_pos_right (hb : 0 < b) : 0 < a / b ↔ 0 < a := by
  simp only [Checked.div_eq_mul_inv, mul_pos_iff_of_pos_right (Checked.inv_pos.2 hb)]

omit [IsStrictOrderedRing α] in
theorem div_mul_le_div_mul_of_div_le_div (h : a / b ≤ c / d) (he : 0 ≤ e) :
    a / (b * e) ≤ c / (d * e) := by
  have hb : (hbUnit.mul heUnit).unit = heUnit.unit * hbUnit.unit := Units.ext (mul_comm b e)
  have hd : (hdUnit.mul heUnit).unit = heUnit.unit * hdUnit.unit := Units.ext (mul_comm d e)
  change a /ₚ (hbUnit.mul heUnit).unit ≤ c /ₚ (hdUnit.mul heUnit).unit
  rw [hb, hd, ← divp_divp_eq_divp_mul, ← divp_divp_eq_divp_mul]
  exact divp_le_divp_of_nonneg_right h he

omit [IsStrictOrderedRing α] in
theorem mul_le_mul_of_mul_div_le (h : a * (b / c) ≤ d) (hc : 0 < c) : b * a ≤ d * c := by
  have hd : Checked.div (a * b) c hcUnit ≤ d := by
    simpa only [Checked.div, divp, mul_assoc] using h
  simpa only [mul_comm b a] using (Checked.div_le_iff hc).mp hd

omit [IsStrictOrderedRing α] in
lemma monotone_div_right_of_nonneg (ha : 0 ≤ a) :
    Monotone (fun b : α => Checked.div b a haUnit) :=
  fun _b _c hbc ↦ Checked.div_le_div_of_nonneg_right hbc ha

omit [IsStrictOrderedRing α] in
lemma strictMono_div_right_of_pos (ha : 0 < a) :
    StrictMono (fun b : α => Checked.div b a haUnit) :=
  fun _b _c hbc ↦ Checked.div_lt_div_of_pos_right hbc ha

omit [IsStrictOrderedRing α] in
theorem Monotone.div_const {β : Type*} [Preorder β] {f : β → α} (hf : Monotone f)
    {c : α} {hcUnit : IsUnit c}
    (hc : 0 ≤ c) : Monotone fun x => f x / c :=
  (monotone_div_right_of_nonneg (haUnit := hcUnit) hc).comp hf

omit [IsStrictOrderedRing α] in
theorem StrictMono.div_const {β : Type*} [Preorder β] {f : β → α} (hf : StrictMono f)
    {c : α} {hcUnit : IsUnit c}
    (hc : 0 < c) : StrictMono fun x => f x / c := by
  exact (strictMono_div_right_of_pos (haUnit := hcUnit) hc).comp hf

omit [IsStrictOrderedRing α] in
theorem one_div_strictAnti :
    StrictAnti (fun x : Set.Ioi (0 : α) =>
      Checked.div (1 : α) (x : α) (GroupWithZero.isUnit_of_ne_zero x.property.ne')) := by
  intro x y hxy
  have h : Checked.inv (y : α) (GroupWithZero.isUnit_of_ne_zero y.property.ne') <
      Checked.inv (x : α) (GroupWithZero.isUnit_of_ne_zero x.property.ne') :=
    (Checked.inv_lt_inv y.property x.property).mpr hxy
  simpa only [Checked.one_div] using h

theorem one_div_pow_le_one_div_pow_of_le (a1 : 1 ≤ a) {m n : ℕ} (mn : m ≤ n) :
    1 / a ^ n ≤ 1 / a ^ m := by
  refine (one_div_le_one_div ?_ ?_).mpr (pow_right_mono₀ a1 mn) <;>
    exact pow_pos (zero_lt_one.trans_le a1) _

theorem one_div_pow_lt_one_div_pow_of_lt (a1 : 1 < a) {m n : ℕ} (mn : m < n) :
    1 / a ^ n < 1 / a ^ m := by
  refine (one_div_lt_one_div ?_ ?_).2 (pow_lt_pow_right₀ a1 mn) <;>
    exact pow_pos (zero_lt_one.trans a1) _

theorem one_div_pow_anti (a1 : 1 ≤ a) : Antitone fun n : ℕ => 1 / a ^ n := fun _ _ =>
  one_div_pow_le_one_div_pow_of_le (haUnit := haUnit) a1

theorem one_div_pow_strictAnti (a1 : 1 < a) : StrictAnti fun n : ℕ => 1 / a ^ n := fun _ _ =>
  one_div_pow_lt_one_div_pow_of_lt (haUnit := haUnit) a1

omit [IsStrictOrderedRing α] in
theorem inv_strictAnti :
    StrictAnti (fun x : Set.Ioi (0 : α) =>
      Checked.inv (x : α) (GroupWithZero.isUnit_of_ne_zero x.property.ne')) := by
  intro x y hxy
  exact (Checked.inv_lt_inv y.property x.property).2 hxy

theorem inv_pow_le_inv_pow_of_le (a1 : 1 ≤ a) {m n : ℕ} (mn : m ≤ n) : (a ^ n)⁻¹ ≤ (a ^ m)⁻¹ := by
  simpa only [Checked.one_div] using
    one_div_pow_le_one_div_pow_of_le (haUnit := haUnit) a1 mn

theorem inv_pow_lt_inv_pow_of_lt (a1 : 1 < a) {m n : ℕ} (mn : m < n) : (a ^ n)⁻¹ < (a ^ m)⁻¹ := by
  simpa only [Checked.one_div] using
    one_div_pow_lt_one_div_pow_of_lt (haUnit := haUnit) a1 mn

theorem inv_pow_anti (a1 : 1 ≤ a) : Antitone fun n : ℕ => (a ^ n)⁻¹ := fun _ _ =>
  inv_pow_le_inv_pow_of_le (haUnit := haUnit) a1

theorem inv_pow_strictAnti (a1 : 1 < a) : StrictAnti fun n : ℕ => (a ^ n)⁻¹ := fun _ _ =>
  inv_pow_lt_inv_pow_of_lt (haUnit := haUnit) a1

theorem le_iff_forall_one_lt_le_mul₀ {α : Type*}
    [Semifield α] [LinearOrder α] [IsStrictOrderedRing α]
    {a b : α} (hb : 0 ≤ b) : a ≤ b ↔ ∀ ε, 1 < ε → a ≤ b * ε := by
  refine ⟨fun h _ hε ↦ h.trans <| le_mul_of_one_le_right hb hε.le, fun h ↦ ?_⟩
  obtain rfl | hb := hb.eq_or_lt
  · simp_rw [zero_mul] at h
    exact h 2 one_lt_two
  refine le_of_forall_gt_imp_ge_of_dense fun x hbx => ?_
  let u := Units.mk0 b hb.ne'
  calc
    a ≤ b * (x /ₚ u) := h _ ((one_lt_divp (u := u) hb).mpr hbx)
    _ = x := by rw [mul_comm]; exact divp_mul_cancel x u

theorem div_nat_le_self_of_nonnneg (ha : 0 ≤ a) (n : ℕ) (hn : n ≠ 0) : a / n ≤ a :=
  div_le_self ha (n.one_le_cast_iff_ne_zero.mpr hn)

theorem div_nat_lt_self_of_pos_of_two_le (ha : 0 < a) {n : ℕ} (hn : 2 ≤ n) :
    Checked.div a (n : α)
      (GroupWithZero.isUnit_of_ne_zero (Nat.cast_ne_zero.mpr (by omega))) < a :=
  div_lt_self ha (n.one_lt_cast.mpr hn)

/-! ### Results about `IsGLB` -/


theorem IsGLB.mul_left {s : Set α} (ha : 0 ≤ a) (hs : IsGLB s b) :
    IsGLB ((fun b => a * b) '' s) (a * b) := by
  rcases lt_or_eq_of_le ha with (ha | rfl)
  · exact (OrderIso.mulLeft₀ _ ha).isGLB_image'.2 hs
  · simp_rw [zero_mul]
    rw [hs.nonempty.image_const]
    exact isGLB_singleton

theorem IsGLB.mul_right {s : Set α} (ha : 0 ≤ a) (hs : IsGLB s b) :
    IsGLB ((fun b => b * a) '' s) (b * a) := by simpa [mul_comm] using hs.mul_left ha

/-! ### Results about `IsLUB` -/


theorem IsLUB.mul_left {s : Set α} (ha : 0 ≤ a) (hs : IsLUB s b) :
    IsLUB ((fun b => a * b) '' s) (a * b) := by
  obtain ha | rfl := ha.lt_or_eq
  · exact (OrderIso.mulLeft₀ _ ha).isLUB_image'.2 hs
  · simp_rw [zero_mul]
    obtain rfl | ne := s.eq_empty_or_nonempty
    · simp only [Set.image_empty, isLUB_empty_iff] at hs ⊢
      have hb := hs (b + b)
      rw [le_add_iff_nonneg_right] at hb
      exact hs.mono hb
    rw [ne.image_const]
    exact isLUB_singleton

theorem IsLUB.mul_right {s : Set α} (ha : 0 ≤ a) (hs : IsLUB s b) :
    IsLUB ((fun b => b * a) '' s) (b * a) := by simpa [mul_comm] using hs.mul_left ha

end PartialOrderedSemifield

section LinearOrderedSemifield

variable {α : Type*} [Semifield α] [LinearOrder α] [IsStrictOrderedRing α] {a b c : α}
variable {haUnit : IsUnit a} {hbUnit : IsUnit b} {hcUnit : IsUnit c}

theorem exists_pos_mul_lt {a : α} (h : 0 < a) (b : α) : ∃ c : α, 0 < c ∧ b * c < a := by
  have hd : 0 < max (b + 1) 1 := lt_max_iff.2 (Or.inr zero_lt_one)
  let u := Units.mk0 (max (b + 1) 1) hd.ne'
  refine ⟨a /ₚ u, divp_pos h hd, ?_⟩
  apply (mul_lt_mul_iff_of_pos_right hd).mp
  change (b * (a /ₚ u)) * (u : α) < a * (u : α)
  have hb : b * a < a * (u : α) := by
    rw [mul_comm b]
    exact mul_lt_mul_of_pos_left (lt_max_iff.2 (Or.inl (lt_add_one b))) h
  simpa only [mul_assoc, divp_mul_cancel] using hb

theorem exists_pos_lt_mul {a : α} (h : 0 < a) (b : α) : ∃ c : α, 0 < c ∧ b < c * a := by
  obtain ⟨c, hc, hbc⟩ := exists_pos_mul_lt h b
  let u := Units.mk0 c hc.ne'
  refine ⟨↑u⁻¹, (Units.inv_pos u).mpr hc, ?_⟩
  apply (Units.lt_inv_mul_iff (u := u) hc).mpr
  simpa only [u, Units.val_mk0, mul_comm c b] using hbc

theorem min_div_div_right {c : α} {hcUnit : IsUnit c} (hc : 0 ≤ c) (a b : α) :
    min (a / c) (b / c) = min a b / c :=
  (monotone_div_right_of_nonneg hc).map_min.symm

theorem max_div_div_right {c : α} {hcUnit : IsUnit c} (hc : 0 ≤ c) (a b : α) :
    max (a / c) (b / c) = max a b / c :=
  (monotone_div_right_of_nonneg hc).map_max.symm

end LinearOrderedSemifield

section PartialOrderedField

variable [Field α] [PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α]
  {a b c d : α}
variable {haUnit : IsUnit a} {hbUnit : IsUnit b} {hcUnit : IsUnit c} {hdUnit : IsUnit d}

attribute [local instance] PosMulReflectLT.toMulPosReflectLT

/-! ### Lemmas about pos, nonneg, nonpos, neg -/

/-- A version of `inv_lt_zero` which holds with different assumptions. In particular, the type
must be a field, not just a `GroupWithZero`, but the order assumptions replace `LinearOrder` and
`PosMulMono` with `PartialOrder`, `IsStrictOrderedRing` and `PosMulReflectLT`. Thus neither version
is more general than the other. This one applies, for instance, to `ℂ`. -/
@[simp] theorem inv_lt_zero' : a⁻¹ < 0 ↔ a < 0 := by
  simpa only [_root_.inv_neg, Units.val_neg, neg_pos, IsUnit.unit_spec, Checked.inv] using
    Units.inv_pos (-haUnit.unit)

/-- A version of `inv_nonpos` which holds with different assumptions. In particular, the type
must be a field, not just a `GroupWithZero`, but the order assumptions replace `LinearOrder` and
`PosMulMono` with `PartialOrder`, `IsStrictOrderedRing` and `PosMulReflectLT`. Thus neither version
is more general than the other. This one applies, for instance, to `ℂ`. -/
@[simp] theorem inv_nonpos' : a⁻¹ ≤ 0 ↔ a ≤ 0 := by
  simp only [le_iff_eq_or_lt, Checked.inv_ne_zero, haUnit.ne_zero, false_or, inv_lt_zero']

theorem div_nonneg_of_nonpos (ha : a ≤ 0) (hb : b ≤ 0) : 0 ≤ a / b :=
  Checked.div_eq_mul_inv a b ▸ mul_nonneg_of_nonpos_of_nonpos ha (inv_nonpos'.2 hb)

theorem div_pos_of_neg_of_neg (ha : a < 0) (hb : b < 0) : 0 < a / b :=
  Checked.div_eq_mul_inv a b ▸ mul_pos_of_neg_of_neg ha (inv_lt_zero'.2 hb)

theorem div_neg_of_neg_of_pos (ha : a < 0) (hb : 0 < b) : a / b < 0 :=
  Checked.div_eq_mul_inv a b ▸ mul_neg_of_neg_of_pos ha (Checked.inv_pos.2 hb)

theorem div_neg_of_pos_of_neg (ha : 0 < a) (hb : b < 0) : a / b < 0 :=
  Checked.div_eq_mul_inv a b ▸ mul_neg_of_pos_of_neg ha (inv_lt_zero'.2 hb)

/-! ### Relating one division with another term -/

theorem div_le_iff_of_neg (hc : c < 0) : b / c ≤ a ↔ a * c ≤ b where
  mp h := by
    simpa only [Checked.div_mul_cancel] using mul_le_mul_of_nonpos_right h hc.le
  mpr h := by
    have h' := mul_le_mul_of_nonpos_right h ((inv_lt_zero' (haUnit := hcUnit)).mpr hc).le
    simpa only [Checked.div_eq_mul_inv, mul_assoc, Checked.mul_inv_cancel, mul_one] using h'

theorem div_le_iff_of_neg' (hc : c < 0) : b / c ≤ a ↔ c * a ≤ b := by
  rw [mul_comm, div_le_iff_of_neg hc]

theorem le_div_iff_of_neg (hc : c < 0) : a ≤ b / c ↔ b ≤ a * c where
  mp h := by
    simpa only [Checked.div_mul_cancel] using mul_le_mul_of_nonpos_right h hc.le
  mpr h := by
    have h' := mul_le_mul_of_nonpos_right h ((inv_lt_zero' (haUnit := hcUnit)).mpr hc).le
    simpa only [Checked.div_eq_mul_inv, mul_assoc, Checked.mul_inv_cancel, mul_one] using h'

theorem le_div_iff_of_neg' (hc : c < 0) : a ≤ b / c ↔ b ≤ c * a := by
  rw [mul_comm, le_div_iff_of_neg hc]

theorem div_lt_iff_of_neg (hc : c < 0) : b / c < a ↔ a * c < b where
  mp h := by
    simpa only [Checked.div_mul_cancel] using mul_lt_mul_of_neg_right h hc
  mpr h := by
    have h' := mul_lt_mul_of_neg_right h ((inv_lt_zero' (haUnit := hcUnit)).mpr hc)
    simpa only [Checked.div_eq_mul_inv, mul_assoc, Checked.mul_inv_cancel, mul_one] using h'

theorem div_lt_iff_of_neg' (hc : c < 0) : b / c < a ↔ c * a < b := by
  rw [mul_comm, div_lt_iff_of_neg hc]

theorem lt_div_iff_of_neg (hc : c < 0) : a < b / c ↔ b < a * c where
  mp h := by
    simpa only [Checked.div_mul_cancel] using mul_lt_mul_of_neg_right h hc
  mpr h := by
    have h' := mul_lt_mul_of_neg_right h ((inv_lt_zero' (haUnit := hcUnit)).mpr hc)
    simpa only [Checked.div_eq_mul_inv, mul_assoc, Checked.mul_inv_cancel, mul_one] using h'

theorem lt_div_iff_of_neg' (hc : c < 0) : a < b / c ↔ b < c * a := by
  rw [mul_comm, lt_div_iff_of_neg hc]

theorem div_le_one_of_ge (h : b ≤ a) (hb : b ≤ 0) : a / b ≤ 1 := by
  have hb0 : b < 0 := lt_of_le_of_ne hb hbUnit.ne_zero
  apply (div_le_iff_of_neg hb0).mpr
  simpa only [one_mul] using h

/-! ### Bi-implications of inequalities using inversions -/

theorem inv_le_inv_of_neg (ha : a < 0) (hb : b < 0) : a⁻¹ ≤ b⁻¹ ↔ b ≤ a := by
  rw [← Checked.one_div a, div_le_iff_of_neg ha, mul_comm]
  change Checked.div a b hbUnit ≤ 1 ↔ b ≤ a
  rw [div_le_iff_of_neg hb, one_mul]

theorem inv_le_of_neg (ha : a < 0) (hb : b < 0) : a⁻¹ ≤ b ↔ b⁻¹ ≤ a := by
  rw [← Checked.one_div a, ← Checked.one_div b,
    div_le_iff_of_neg ha, div_le_iff_of_neg hb, mul_comm]

theorem le_inv_of_neg (ha : a < 0) (hb : b < 0) : a ≤ b⁻¹ ↔ b ≤ a⁻¹ := by
  rw [← Checked.one_div a, ← Checked.one_div b,
    le_div_iff_of_neg hb, le_div_iff_of_neg ha, mul_comm]

theorem inv_lt_inv_of_neg (ha : a < 0) (hb : b < 0) : a⁻¹ < b⁻¹ ↔ b < a := by
  rw [← Checked.one_div a, div_lt_iff_of_neg ha, mul_comm]
  change Checked.div a b hbUnit < 1 ↔ b < a
  rw [div_lt_iff_of_neg hb, one_mul]

theorem inv_lt_of_neg (ha : a < 0) (hb : b < 0) : a⁻¹ < b ↔ b⁻¹ < a := by
  rw [← Checked.one_div a, ← Checked.one_div b,
    div_lt_iff_of_neg ha, div_lt_iff_of_neg hb, mul_comm]

theorem lt_inv_of_neg (ha : a < 0) (hb : b < 0) : a < b⁻¹ ↔ b < a⁻¹ := by
  rw [← Checked.one_div a, ← Checked.one_div b,
    lt_div_iff_of_neg hb, lt_div_iff_of_neg ha, mul_comm]

/-!
### Monotonicity results involving inversion
-/


theorem sub_inv_antitone_Ioi :
    Antitone (fun x : Set.Ioi c =>
      Checked.inv (x.val - c) (GroupWithZero.isUnit_of_ne_zero (sub_pos.mpr x.property).ne')) := by
  intro x y hxy
  exact (Checked.inv_le_inv (sub_pos.mpr y.property) (sub_pos.mpr x.property)).mpr
    (sub_le_sub_right (show (x : α) ≤ (y : α) from hxy) c)

theorem sub_inv_antitone_Iio :
    Antitone (fun x : Set.Iio c =>
      Checked.inv (x.val - c) (GroupWithZero.isUnit_of_ne_zero (sub_neg.mpr x.property).ne)) := by
  intro x y hxy
  exact (inv_le_inv_of_neg (sub_neg.mpr y.property) (sub_neg.mpr x.property)).mpr
    (sub_le_sub_right (show (x : α) ≤ (y : α) from hxy) c)

theorem sub_inv_antitone_Icc_right (ha : c < a) :
    Antitone (fun x : Set.Icc a b => Checked.inv (x.val - c)
      (GroupWithZero.isUnit_of_ne_zero (sub_pos.mpr (ha.trans_le x.property.1)).ne')) := by
  intro x y hxy
  exact (Checked.inv_le_inv (sub_pos.mpr (ha.trans_le y.property.1))
    (sub_pos.mpr (ha.trans_le x.property.1))).mpr
      (sub_le_sub_right (show (x : α) ≤ (y : α) from hxy) c)

theorem sub_inv_antitone_Icc_left (hb : b < c) :
    Antitone (fun x : Set.Icc a b => Checked.inv (x.val - c)
      (GroupWithZero.isUnit_of_ne_zero (sub_neg.mpr (x.property.2.trans_lt hb)).ne)) := by
  intro x y hxy
  exact (inv_le_inv_of_neg (sub_neg.mpr (y.property.2.trans_lt hb))
    (sub_neg.mpr (x.property.2.trans_lt hb))).mpr
      (sub_le_sub_right (show (x : α) ≤ (y : α) from hxy) c)

omit [IsStrictOrderedRing α] in
theorem inv_antitone_Ioi :
    Antitone (fun x : Set.Ioi (0 : α) =>
      Checked.inv (x : α) (GroupWithZero.isUnit_of_ne_zero x.property.ne')) := by
  intro x y hxy
  exact (Checked.inv_le_inv y.property x.property).mpr hxy

theorem inv_antitone_Iio :
    Antitone (fun x : Set.Iio (0 : α) =>
      Checked.inv (x : α) (GroupWithZero.isUnit_of_ne_zero x.property.ne)) := by
  intro x y hxy
  exact (inv_le_inv_of_neg y.property x.property).mpr hxy

omit [IsStrictOrderedRing α] in
theorem inv_antitone_Icc_right (ha : 0 < a) :
    Antitone (fun x : Set.Icc a b =>
      Checked.inv (x : α) (GroupWithZero.isUnit_of_ne_zero (ha.trans_le x.property.1).ne')) := by
  intro x y hxy
  exact (Checked.inv_le_inv (ha.trans_le y.property.1) (ha.trans_le x.property.1)).mpr hxy

theorem inv_antitone_Icc_left (hb : b < 0) :
    Antitone (fun x : Set.Icc a b =>
      Checked.inv (x : α) (GroupWithZero.isUnit_of_ne_zero (x.property.2.trans_lt hb).ne)) := by
  intro x y hxy
  exact (inv_le_inv_of_neg (y.property.2.trans_lt hb) (x.property.2.trans_lt hb)).mpr hxy

/-! ### Relating two divisions -/


theorem div_le_div_of_nonpos_of_le (hc : c ≤ 0) (h : b ≤ a) : a / c ≤ b / c := by
  rw [Checked.div_eq_mul_inv a c, Checked.div_eq_mul_inv b c]
  exact mul_le_mul_of_nonpos_right h (inv_nonpos'.2 hc)

theorem div_lt_div_of_neg_of_lt (hc : c < 0) (h : b < a) : a / c < b / c := by
  rw [Checked.div_eq_mul_inv a c, Checked.div_eq_mul_inv b c]
  exact mul_lt_mul_of_neg_right h (inv_lt_zero'.2 hc)

theorem div_le_div_right_of_neg (hc : c < 0) : a / c ≤ b / c ↔ b ≤ a := by
  rw [div_le_iff_of_neg hc, Checked.div_mul_cancel _ c hcUnit]

theorem div_lt_div_right_of_neg (hc : c < 0) : a / c < b / c ↔ b < a := by
  rw [div_lt_iff_of_neg hc, Checked.div_mul_cancel _ c hcUnit]

/-! ### Relating one division and involving `1` -/


theorem one_le_div_of_neg (hb : b < 0) : 1 ≤ a / b ↔ a ≤ b := by rw [le_div_iff_of_neg hb, one_mul]

theorem div_le_one_of_neg (hb : b < 0) : a / b ≤ 1 ↔ b ≤ a := by rw [div_le_iff_of_neg hb, one_mul]

theorem one_lt_div_of_neg (hb : b < 0) : 1 < a / b ↔ a < b := by rw [lt_div_iff_of_neg hb, one_mul]

theorem div_lt_one_of_neg (hb : b < 0) : a / b < 1 ↔ b < a := by rw [div_lt_iff_of_neg hb, one_mul]

theorem one_div_le_of_neg (ha : a < 0) (hb : b < 0) : 1 / a ≤ b ↔ 1 / b ≤ a := by
  simpa using inv_le_of_neg ha hb

theorem one_div_lt_of_neg (ha : a < 0) (hb : b < 0) : 1 / a < b ↔ 1 / b < a := by
  simpa using inv_lt_of_neg ha hb

theorem le_one_div_of_neg (ha : a < 0) (hb : b < 0) : a ≤ 1 / b ↔ b ≤ 1 / a := by
  simpa using le_inv_of_neg ha hb

theorem lt_one_div_of_neg (ha : a < 0) (hb : b < 0) : a < 1 / b ↔ b < 1 / a := by
  simpa using lt_inv_of_neg ha hb

/-! ### Relating two divisions, involving `1` -/


theorem one_div_le_one_div_of_neg_of_le (hb : b < 0) (h : a ≤ b) : 1 / b ≤ 1 / a := by
  simpa only [Checked.one_div] using
    (inv_le_inv_of_neg (haUnit := hbUnit) (hbUnit := haUnit) hb (h.trans_lt hb)).mpr h

theorem one_div_lt_one_div_of_neg_of_lt (hb : b < 0) (h : a < b) : 1 / b < 1 / a := by
  simpa only [Checked.one_div] using
    (inv_lt_inv_of_neg (haUnit := hbUnit) (hbUnit := haUnit) hb (h.trans hb)).mpr h

theorem le_of_neg_of_one_div_le_one_div (hb : b < 0) (h : 1 / a ≤ 1 / b) : b ≤ a := by
  have ha : a < 0 := inv_lt_zero'.mp <|
    lt_of_le_of_lt (by simpa only [Checked.one_div] using h) (inv_lt_zero'.mpr hb)
  exact (inv_le_inv_of_neg ha hb).mp (by simpa only [Checked.one_div] using h)

theorem lt_of_neg_of_one_div_lt_one_div (hb : b < 0) (h : 1 / a < 1 / b) : b < a := by
  have ha : a < 0 := inv_lt_zero'.mp <|
    lt_trans (by simpa only [Checked.one_div] using h) (inv_lt_zero'.mpr hb)
  exact (inv_lt_inv_of_neg ha hb).mp (by simpa only [Checked.one_div] using h)

/-- For the single implications with fewer assumptions, see `one_div_lt_one_div_of_neg_of_lt` and
  `lt_of_one_div_lt_one_div` -/
theorem one_div_le_one_div_of_neg (ha : a < 0) (hb : b < 0) : 1 / a ≤ 1 / b ↔ b ≤ a := by
  simpa [Checked.one_div] using inv_le_inv_of_neg ha hb

/-- For the single implications with fewer assumptions, see `one_div_lt_one_div_of_lt` and
  `lt_of_one_div_lt_one_div` -/
theorem one_div_lt_one_div_of_neg (ha : a < 0) (hb : b < 0) : 1 / a < 1 / b ↔ b < a := by
  simpa [Checked.one_div] using inv_lt_inv_of_neg ha hb

theorem one_div_lt_neg_one (h1 : a < 0) (h2 : -1 < a) : 1 / a < -1 := by
  rw [div_lt_iff_of_neg h1, neg_one_mul, neg_lt]
  exact h2

theorem one_div_le_neg_one (h1 : a < 0) (h2 : -1 ≤ a) : 1 / a ≤ -1 := by
  rw [div_le_iff_of_neg h1, neg_one_mul, neg_le]
  exact h2

/-! ### Results about halving -/

theorem add_sub_div_two_lt (h : a < b) : a + (b - a) / 2 < b := by
  have hh := half_lt_self (sub_pos.mpr h)
  simpa only [add_comm] using (lt_sub_iff_add_lt.mp hh)

lemma one_sub_one_div_pos_of_two_le (a2 : 2 ≤ a) : 0 < 1 - Checked.div 1 a haUnit := by
  have hdiv : Checked.div 1 a haUnit ≤ Checked.div (1 : α) 2 :=
    Checked.div_le_div_of_nonneg_left zero_le_one zero_lt_two a2
  exact sub_pos.mpr (hdiv.trans_lt one_half_lt_one)

/-- An inequality involving `2`, with the reciprocal's positive domain explicit. -/
theorem sub_one_div_inv_le_two (a2 : 2 ≤ a) :
    Checked.inv (1 - Checked.div 1 a haUnit)
      (GroupWithZero.isUnit_of_ne_zero (one_sub_one_div_pos_of_two_le a2).ne') ≤ 2 := by
  rw [← Checked.one_div]
  apply (Checked.div_le_iff (one_sub_one_div_pos_of_two_le a2)).mpr
  have hdiv : Checked.div 1 a haUnit ≤ Checked.div (1 : α) 2 :=
    Checked.div_le_div_of_nonneg_left zero_le_one zero_lt_two a2
  have hsmall : 2 * Checked.div 1 a haUnit ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hdiv ((zero_lt_two' α).le)
    simpa only [Checked.one_div, Checked.mul_inv_cancel] using h
  rw [mul_sub, mul_one, le_sub_iff_add_le]
  simpa only [add_comm] using (add_le_add_left hsmall 1).trans_eq one_add_one_eq_two

/-! ### Miscellaneous lemmas -/


omit [PosMulReflectLT α] in
theorem mul_sub_mul_div_mul_neg_iff :
    (a * d - b * c) / (c * d) < 0 ↔ a / c < b / d := by
  have hu : (hcUnit.mul hdUnit).unit = hcUnit.unit * hdUnit.unit := Units.ext rfl
  have hf : Checked.div (a * d - b * c) (c * d) (hcUnit.mul hdUnit) =
      Checked.div a c hcUnit - Checked.div b d hdUnit := by
    change (a * d - b * c) /ₚ (hcUnit.mul hdUnit).unit = _
    rw [hu]
    simpa only [Checked.div, IsUnit.unit_spec, mul_comm b c] using
      (Units.divp_sub_divp a b hcUnit.unit hdUnit.unit).symm
  rw [hf, sub_lt_zero]

omit [PosMulReflectLT α] in
theorem mul_sub_mul_div_mul_nonpos_iff :
    (a * d - b * c) / (c * d) ≤ 0 ↔ a / c ≤ b / d := by
  have hu : (hcUnit.mul hdUnit).unit = hcUnit.unit * hdUnit.unit := Units.ext rfl
  have hf : Checked.div (a * d - b * c) (c * d) (hcUnit.mul hdUnit) =
      Checked.div a c hcUnit - Checked.div b d hdUnit := by
    change (a * d - b * c) /ₚ (hcUnit.mul hdUnit).unit = _
    rw [hu]
    simpa only [Checked.div, IsUnit.unit_spec, mul_comm b c] using
      (Units.divp_sub_divp a b hcUnit.unit hdUnit.unit).symm
  rw [hf, sub_nonpos]

alias ⟨div_lt_div_of_mul_sub_mul_div_neg, mul_sub_mul_div_mul_neg⟩ := mul_sub_mul_div_mul_neg_iff

alias ⟨div_le_div_of_mul_sub_mul_div_nonpos, mul_sub_mul_div_mul_nonpos⟩ :=
  mul_sub_mul_div_mul_nonpos_iff

theorem exists_add_lt_and_pos_of_lt (h : b < a) : ∃ c, b + c < a ∧ 0 < c :=
  ⟨(a - b) / 2, add_sub_div_two_lt h, Checked.div_pos (sub_pos_of_lt h) zero_lt_two⟩

end PartialOrderedField

section LinearOrderedField

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] {a b c d : α} {n : ℤ}
variable {haUnit : IsUnit a} {hbUnit : IsUnit b} {hcUnit : IsUnit c} {hdUnit : IsUnit d}

theorem div_pos_iff : 0 < a / b ↔ 0 < a ∧ 0 < b ∨ a < 0 ∧ b < 0 := by
  simp only [Checked.div_eq_mul_inv, mul_pos_iff, Checked.inv_pos, inv_lt_zero']

theorem div_neg_iff : a / b < 0 ↔ 0 < a ∧ b < 0 ∨ a < 0 ∧ 0 < b := by
  simp only [Checked.div_eq_mul_inv, mul_neg_iff, Checked.inv_pos, inv_lt_zero']

theorem div_nonneg_iff : 0 ≤ a / b ↔ 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0 := by
  simp only [Checked.div_eq_mul_inv, mul_nonneg_iff, Checked.inv_nonneg, inv_nonpos']

theorem div_nonpos_iff : a / b ≤ 0 ↔ 0 ≤ a ∧ b ≤ 0 ∨ a ≤ 0 ∧ 0 ≤ b := by
  simp only [Checked.div_eq_mul_inv, mul_nonpos_iff, Checked.inv_nonneg, inv_nonpos']

theorem one_lt_div_iff : 1 < a / b ↔ 0 < b ∧ b < a ∨ b < 0 ∧ a < b := by
  rcases hbUnit.ne_zero.lt_or_gt with hb | hb
  · simp [hb, hb.not_gt, one_lt_div_of_neg]
  · simp [hb, hb.not_gt, one_lt_div]

theorem one_le_div_iff : 1 ≤ a / b ↔ 0 < b ∧ b ≤ a ∨ b < 0 ∧ a ≤ b := by
  rcases hbUnit.ne_zero.lt_or_gt with hb | hb
  · simp [hb, hb.not_gt, one_le_div_of_neg]
  · simp [hb, hb.not_gt, one_le_div]

theorem div_lt_one_iff : a / b < 1 ↔ 0 < b ∧ a < b ∨ b < 0 ∧ b < a := by
  rcases hbUnit.ne_zero.lt_or_gt with hb | hb
  · simp [hb, hb.not_gt, div_lt_one_of_neg]
  · simp [hb, hb.not_gt, div_lt_one]

theorem div_le_one_iff : a / b ≤ 1 ↔ 0 < b ∧ a ≤ b ∨ b < 0 ∧ b ≤ a := by
  rcases hbUnit.ne_zero.lt_or_gt with hb | hb
  · simp [hb, hb.not_gt, div_le_one_of_neg]
  · simp [hb, hb.not_gt, div_le_one]

theorem le_of_forall_sub_le (h : ∀ ε > 0, b - ε ≤ a) : b ≤ a := by
  contrapose! h
  simpa only [@and_comm ((0 : α) < _), lt_sub_iff_add_lt, gt_iff_lt] using
    exists_add_lt_and_pos_of_lt h

private lemma exists_lt_mul_left_of_nonneg {a b c : α} (ha : 0 ≤ a) (hc : 0 ≤ c) (h : c < a * b) :
    ∃ a' ∈ Set.Ico 0 a, c < a' * b := by
  have hb : 0 < b := pos_of_mul_pos_right (hc.trans_lt h) ha
  obtain ⟨a', ha', a_a'⟩ := exists_between ((Checked.div_lt_iff (a := c) (b := a)
    (hc := GroupWithZero.isUnit_of_ne_zero hb.ne') hb).2 h)
  refine ⟨a', ⟨?_, a_a'⟩, ?_⟩
  · exact (Checked.div_nonneg (hb := GroupWithZero.isUnit_of_ne_zero hb.ne') hc hb.le).trans ha'.le
  · exact (Checked.div_lt_iff (a := c) (hc := GroupWithZero.isUnit_of_ne_zero hb.ne') hb).1 ha'

private lemma exists_lt_mul_right_of_nonneg {a b c : α} (ha : 0 ≤ a) (hc : 0 ≤ c) (h : c < a * b) :
    ∃ b' ∈ Set.Ico 0 b, c < a * b' := by
  have hb : 0 < b := pos_of_mul_pos_right (hc.trans_lt h) ha
  simp_rw [mul_comm a] at h ⊢
  exact exists_lt_mul_left_of_nonneg hb.le hc h

private lemma exists_mul_left_lt₀ {a b c : α} (hc : a * b < c) : ∃ a' > a, a' * b < c := by
  rcases le_or_gt b 0 with hb | hb
  · obtain ⟨a', ha'⟩ := exists_gt a
    exact ⟨a', ha', hc.trans_le' (antitone_mul_right hb ha'.le)⟩
  · obtain ⟨a', ha', hc'⟩ := exists_between ((Checked.lt_div_iff (a := a) (b := c)
      (hc := GroupWithZero.isUnit_of_ne_zero hb.ne') hb).2 hc)
    refine ⟨a', ha', ?_⟩
    exact (Checked.lt_div_iff (a := a') (hc := GroupWithZero.isUnit_of_ne_zero hb.ne') hb).1 hc'

private lemma exists_mul_right_lt₀ {a b c : α} (hc : a * b < c) : ∃ b' > b, a * b' < c := by
  simp_rw [mul_comm a] at hc ⊢; exact exists_mul_left_lt₀ hc

lemma le_mul_of_forall_lt₀ {a b c : α} (h : ∀ a' > a, ∀ b' > b, c ≤ a' * b') : c ≤ a * b := by
  refine le_of_forall_gt_imp_ge_of_dense fun d hd ↦ ?_
  obtain ⟨a', ha', hd⟩ := exists_mul_left_lt₀ hd
  obtain ⟨b', hb', hd⟩ := exists_mul_right_lt₀ hd
  exact (h a' ha' b' hb').trans hd.le

lemma mul_le_of_forall_lt_of_nonneg {a b c : α} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (h : ∀ a' ≥ 0, a' < a → ∀ b' ≥ 0, b' < b → a' * b' ≤ c) : a * b ≤ c := by
  refine le_of_forall_lt_imp_le_of_dense fun d d_ab ↦ ?_
  rcases lt_or_ge d 0 with hd | hd
  · exact hd.le.trans hc
  obtain ⟨a', ha', d_ab⟩ := exists_lt_mul_left_of_nonneg ha hd d_ab
  obtain ⟨b', hb', d_ab⟩ := exists_lt_mul_right_of_nonneg ha'.1 hd d_ab
  exact d_ab.le.trans (h a' ha'.1 ha'.2 b' hb'.1 hb'.2)

  -- surely there is an easier proof of this, or we already have something like it somewhere.
  -- It doesn't even need `α` to be a field, so it doesn't belong in this file.
theorem mul_self_inj_of_nonneg {α : Type*} [CommRing α] [NoZeroDivisors α] [PartialOrder α]
    [IsStrictOrderedRing α] {a b : α} (a0 : 0 ≤ a) (b0 : 0 ≤ b) :
    a * a = b * b ↔ a = b := by
  have := fun h ↦ le_antisymm (neg_nonneg.mp h) b0
  grind [sq_sub_sq, mul_eq_zero, add_eq_zero_iff_eq_neg]

theorem min_div_div_right_of_nonpos (hc : c ≤ 0) (a b : α) :
    min (a / c) (b / c) = max a b / c :=
  Eq.symm <| Antitone.map_max fun _ _ => div_le_div_of_nonpos_of_le hc

theorem max_div_div_right_of_nonpos (hc : c ≤ 0) (a b : α) :
    max (a / c) (b / c) = min a b / c :=
  Eq.symm <| Antitone.map_min fun _ _ => div_le_div_of_nonpos_of_le hc

@[simp, grind =]
theorem abs_inv (a : α) (ha : IsUnit a) :
    |Checked.inv a ha| = Checked.inv |a| (ha.map (absHom : α →*₀ α)) := by
  have hu : Units.map (absHom : α →*₀ α).toMonoidHom ha.unit =
      (ha.map (absHom : α →*₀ α)).unit := Units.ext rfl
  exact congrArg (fun u : αˣ => (↑u⁻¹ : α)) hu

@[grind =]
theorem abs_div (a b : α) (hb : IsUnit b) :
    |Checked.div a b hb| = Checked.div |a| |b| (hb.map (absHom : α →*₀ α)) := by
  change |a * Checked.inv b hb| = |a| * Checked.inv |b| (hb.map (absHom : α →*₀ α))
  rw [abs_mul, abs_inv b hb]

theorem abs_one_div (a : α) (ha : IsUnit a) :
    |Checked.div 1 a ha| = Checked.div 1 |a| (ha.map (absHom : α →*₀ α)) := by
  rw [abs_div, abs_one]

theorem uniform_continuous_npow_on_bounded (B : α) {ε : α} (hε : 0 < ε) (n : ℕ) :
    ∃ δ > 0, ∀ q r : α, |r| ≤ B → |q - r| ≤ δ → |q ^ n - r ^ n| < ε := by
  wlog! B_pos : 0 < B generalizing B
  · have ⟨δ, δ_pos, cont⟩ := this 1 zero_lt_one
    exact ⟨δ, δ_pos, fun q r hr ↦ cont q r (hr.trans (B_pos.trans zero_le_one))⟩
  have pos : 0 < 1 + (n : α) * (B + 1) ^ (n - 1) :=
    zero_lt_one.trans_le <| le_add_of_nonneg_right <|
    mul_nonneg n.cast_nonneg <| (pow_pos (B_pos.trans <| lt_add_of_pos_right _ zero_lt_one) _).le
  refine ⟨min 1 (ε / (1 + (n : α) * (B + 1) ^ (n - 1))),
    lt_min zero_lt_one (Checked.div_pos hε pos),
    fun q r hr hqr ↦ (abs_pow_sub_pow_le ..).trans_lt ?_⟩
  rw [le_inf_iff, Checked.le_div_iff pos, mul_one_add, ← mul_assoc] at hqr
  obtain h | h := (abs_nonneg (q - r)).eq_or_lt
  · simpa only [← h, zero_mul] using hε
  refine (lt_of_le_of_lt ?_ <| lt_add_of_pos_left _ h).trans_le hqr.2
  gcongr
  · exact mul_nonneg (abs_nonneg _) n.cast_nonneg
  · exact (abs_nonneg _).trans le_sup_left
  refine max_le ?_ (hr.trans <| le_add_of_nonneg_right zero_le_one)
  exact add_sub_cancel r q ▸ (abs_add_le ..).trans (add_le_add hr hqr.1)

lemma two_mul_le_add_mul_sq {ε : α} (hε : 0 < ε) :
    2 * a * b ≤ ε * a ^ 2 + ε⁻¹ * b ^ 2 := by
  have h : 2 * (ε * a) * b ≤ (ε * a) ^ 2 + b ^ 2 := two_mul_le_add_sq (ε * a) b
  calc 2 * a * b
  _ = 2 * a * b * (ε * ε⁻¹) := by
    rw [Checked.mul_inv_cancel ε (GroupWithZero.isUnit_of_ne_zero hε.ne'), mul_one]
  _ = (2 * (ε * a) * b) * ε⁻¹ := by simp_rw [mul_assoc, mul_comm ε, mul_assoc]
  _ ≤ ((ε * a) ^ 2 + b ^ 2) * ε⁻¹ := by gcongr; exact Checked.inv_nonneg.mpr hε.le
  _ = ε * a ^ 2 + ε⁻¹ * b ^ 2 := by
    let i := Checked.inv ε (GroupWithZero.isUnit_of_ne_zero hε.ne')
    have hi : ε * i = 1 := Checked.mul_inv_cancel ε _
    change ((ε * a) ^ 2 + b ^ 2) * i = ε * a ^ 2 + i * b ^ 2
    rw [add_mul, mul_pow, mul_right_comm (ε ^ 2) (a ^ 2) i, mul_comm (b ^ 2) i]
    rw [pow_two ε, mul_assoc ε ε i, hi, mul_one]

end LinearOrderedField

namespace Mathlib.Meta.Positivity
open Lean Meta Qq

/-- Positivity of division with an already checked unit denominator. -/
@[positivity Checked.div _ _ _]
meta def evalDiv : PositivityExt where eval {u α} zα pα? e := do
  unless e.isAppOfArity ``Checked.div 5 do throwError "not checked division"
  let _a ← synthInstanceQ q(GroupWithZero $α)
  assumeInstancesCommute
  let .app (.app (.app _ (a : Q($α))) (b : Q($α))) (hb : Q(IsUnit $b)) := e
    | throwError "not checked division"
  haveI' : $e =Q Checked.div $a $b $hb := ⟨⟩
  match (dependent := true) pα? with
  | none =>
    match ← catchNone (core zα pα? a) with
    | .nonzero pa => pure (.nonzero q(Checked.div_ne_zero (hb := $hb) $pa))
    | _ => pure .none
  | some pα =>
    let ra ← catchNone (core zα pα a)
    let fallback : Strictness zα e (some pα) := match ra with
      | .positive pa => .nonzero q(Checked.div_ne_zero (hb := $hb) (ne_of_gt $pa))
      | .nonzero pa => .nonzero q(Checked.div_ne_zero (hb := $hb) $pa)
      | _ => .none
    orElse fallback do
      let _a ← synthInstanceQ q(PosMulReflectLT $α)
      assumeInstancesCommute
      let rb ← catchNone (core zα pα b)
      match ra, rb with
      | .positive pa, .positive pb =>
        pure (.positive q(Checked.div_pos (hb := $hb) $pa $pb))
      | .positive pa, .nonnegative pb =>
        pure (.nonnegative q(Checked.div_nonneg (hb := $hb) (le_of_lt $pa) $pb))
      | .nonnegative pa, .positive pb =>
        pure (.nonnegative q(Checked.div_nonneg (hb := $hb) $pa (le_of_lt $pb)))
      | .nonnegative pa, .nonnegative pb =>
        pure (.nonnegative q(Checked.div_nonneg (hb := $hb) $pa $pb))
      | _, _ => pure .none

/-- Positivity of inversion with an already checked unit witness. -/
@[positivity Checked.inv _ _]
meta def evalInv : PositivityExt where eval {u α} zα pα? e := do
  unless e.isAppOfArity ``Checked.inv 4 do throwError "not checked inversion"
  let _a ← synthInstanceQ q(GroupWithZero $α)
  assumeInstancesCommute
  let .app (.app _ (a : Q($α))) (ha : Q(IsUnit $a)) := e
    | throwError "not checked inversion"
  haveI' : $e =Q Checked.inv $a $ha := ⟨⟩
  match (dependent := true) pα? with
  | none => pure (.nonzero q(Checked.inv_ne_zero (ha := $ha)))
  | some pα =>
    orElse (.nonzero q(Checked.inv_ne_zero (ha := $ha))) do
      let _a ← synthInstanceQ q(PosMulReflectLT $α)
      assumeInstancesCommute
      match ← catchNone (core zα pα a) with
      | .positive pa => pure (.positive q((Checked.inv_pos (ha := $ha)).mpr $pa))
      | .nonnegative pa => pure (.nonnegative q((Checked.inv_nonneg (ha := $ha)).mpr $pa))
      | _ => pure .none

end Mathlib.Meta.Positivity
