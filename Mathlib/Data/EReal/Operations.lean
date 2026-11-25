/-
Copyright (c) 2019 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Mathlib.Data.EReal.Basic

/-!
# Addition, negation, subtraction and multiplication on extended real numbers

Addition and multiplication in `EReal` are problematic in the presence of `±∞`, but negation has
a natural definition and satisfies the usual properties. In particular, it is an order-reversing
isomorphism.

The construction of `EReal` as `WithBot (WithTop ℝ)` endows a `LinearOrderedAddCommMonoid` structure
on it. However, addition is badly behaved at `(⊥, ⊤)` and `(⊤, ⊥)`, so this cannot be upgraded to a
group structure. Our choice is that `⊥ + ⊤ = ⊤ + ⊥ = ⊥`, to make sure that the exponential and
logarithm between `EReal` and `ℝ≥0∞` respect the operations. Note that the convention `0 * ∞ = 0`
on `ℝ≥0∞` is enforced by measure theory. The signed difference `x - y = x + (-y)` requires a proof
that the two operands are not
equal infinities.

There is also a `CommMonoidWithZero` structure on `EReal`, but `Mathlib/Data/EReal/Basic.lean` only
provides `MulZeroOneClass` because a proof of associativity by hand would have 125 cases.
The `CommMonoidWithZero` instance is instead delivered in `Mathlib/Data/EReal/Inv.lean`.

We define `0 * x = x * 0 = 0` for any `x`, with the other cases defined non-ambiguously.
This does not distribute with addition, as `⊥ = ⊥ + ⊤ = 1 * ⊥ + (-1) * ⊥ ≠ (1 - 1) * ⊥ = 0 * ⊥ = 0`.
Distributivity `x * (y + z) = x * y + x * z` is recovered in the case where either `0 ≤ x < ⊤`,
see `EReal.left_distrib_of_nonneg_of_ne_top`, or `0 ≤ y, z`. See `EReal.left_distrib_of_nonneg`
(similarly for right distributivity).
-/

@[expose] public section

open ENNReal NNReal

noncomputable section

namespace EReal

/-! ### Addition -/

@[simp]
theorem add_bot (x : EReal) : x + ⊥ = ⊥ :=
  WithBot.add_bot _

@[simp]
theorem bot_add (x : EReal) : ⊥ + x = ⊥ :=
  WithBot.bot_add _

@[simp]
theorem add_eq_bot_iff {x y : EReal} : x + y = ⊥ ↔ x = ⊥ ∨ y = ⊥ :=
  WithBot.add_eq_bot

lemma add_ne_bot_iff {x y : EReal} : x + y ≠ ⊥ ↔ x ≠ ⊥ ∧ y ≠ ⊥ := WithBot.add_ne_bot

@[simp]
theorem bot_lt_add_iff {x y : EReal} : ⊥ < x + y ↔ ⊥ < x ∧ ⊥ < y := by
  simp [bot_lt_iff_ne_bot]

@[simp]
theorem top_add_top : (⊤ : EReal) + ⊤ = ⊤ :=
  rfl

@[simp]
theorem top_add_coe (x : ℝ) : (⊤ : EReal) + x = ⊤ :=
  rfl

/-- For any extended real number `x` which is not `⊥`, the sum of `⊤` and `x` is equal to `⊤`. -/
@[simp]
theorem top_add_of_ne_bot {x : EReal} (h : x ≠ ⊥) : ⊤ + x = ⊤ := by
  induction x
  · exfalso; exact h (Eq.refl ⊥)
  · exact top_add_coe _
  · exact top_add_top

/-- For any extended real number `x` which is not `⊥`, the sum of `x` and `⊤` is equal to `⊤`. -/
@[simp]
theorem add_top_of_ne_bot {x : EReal} (h : x ≠ ⊥) : x + ⊤ = ⊤ := by
  rw [add_comm, top_add_of_ne_bot h]

@[grind =]
theorem add_eq_top_iff {x y : EReal} : x + y = ⊤ ↔ (x = ⊤ ∧ y ≠ ⊥) ∨ (x ≠ ⊥ ∧ y = ⊤) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · cases x <;> cases y <;> simp_all [← coe_add]
  · obtain ⟨rfl, h⟩ | ⟨h, rfl⟩ := h <;> simp [h]

/-- For any extended real number `x`, the sum of `⊤` and `x` is equal to `⊤`
if and only if `x` is not `⊥`. -/
theorem top_add_iff_ne_bot {x : EReal} : ⊤ + x = ⊤ ↔ x ≠ ⊥ := by
  simp +contextual [add_eq_top_iff]

/-- For any extended real number `x`, the sum of `x` and `⊤` is equal to `⊤`
if and only if `x` is not `⊥`. -/
theorem add_top_iff_ne_bot {x : EReal} : x + ⊤ = ⊤ ↔ x ≠ ⊥ := by rw [add_comm, top_add_iff_ne_bot]

protected theorem add_pos_of_pos_of_nonneg {a b : EReal} (ha : 0 < a) (hb : 0 ≤ b) : 0 < a + b :=
  add_comm a b ▸ Right.add_pos_of_nonneg_of_pos hb ha

/-- For any two extended real numbers `a` and `b`, if both `a` and `b` are greater than `0`,
then their sum is also greater than `0`. -/
protected theorem add_pos {a b : EReal} (ha : 0 < a) (hb : 0 < b) : 0 < a + b :=
  Right.add_pos_of_nonneg_of_pos ha.le hb

@[simp]
theorem coe_add_top (x : ℝ) : (x : EReal) + ⊤ = ⊤ :=
  rfl

theorem toReal_add {x y : EReal} (hx : x ≠ ⊤) (h'x : x ≠ ⊥) (hy : y ≠ ⊤) (h'y : y ≠ ⊥) :
    toReal (x + y) = toReal x + toReal y := by
  lift x to ℝ using ⟨hx, h'x⟩
  lift y to ℝ using ⟨hy, h'y⟩
  rfl

lemma toENNReal_add {x y : EReal} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x + y).toENNReal = x.toENNReal + y.toENNReal := by
  induction x <;> induction y <;> try {· simp_all}
  norm_cast
  simp_rw [real_coe_toENNReal]
  simp_all [ENNReal.ofReal_add]

lemma toENNReal_add_le {x y : EReal} : (x + y).toENNReal ≤ x.toENNReal + y.toENNReal := by
  induction x <;> induction y <;> try {· simp}
  exact ENNReal.ofReal_add_le

theorem addLECancellable_coe (x : ℝ) : AddLECancellable (x : EReal)
  | _, ⊤, _ => le_top
  | ⊥, _, _ => bot_le
  | ⊤, (z : ℝ), h => by simp only [coe_add_top, ← coe_add, top_le_iff, coe_ne_top] at h
  | _, ⊥, h => by simpa using h
  | (y : ℝ), (z : ℝ), h => by
    simpa only [← coe_add, EReal.coe_le_coe_iff, add_le_add_iff_left] using h

-- TODO: add `MulLECancellable.strictMono*` etc
theorem add_lt_add_right_coe {x y : EReal} (h : x < y) (z : ℝ) : x + z < y + z :=
  not_le.1 <| mt (addLECancellable_coe z).add_le_add_iff_right.1 h.not_ge

theorem add_lt_add_left_coe {x y : EReal} (h : x < y) (z : ℝ) : (z : EReal) + x < z + y := by
  simpa [add_comm] using add_lt_add_right_coe h z

theorem add_lt_add {x y z t : EReal} (h1 : x < y) (h2 : z < t) : x + z < y + t := by
  rcases eq_or_ne x ⊥ with (rfl | hx)
  · simp [h1, bot_le.trans_lt h2]
  · lift x to ℝ using ⟨h1.ne_top, hx⟩
    calc (x : EReal) + z < x + t := add_lt_add_left_coe h2 _
    _ ≤ y + t := by gcongr

theorem add_lt_add_of_lt_of_le' {x y z t : EReal} (h : x < y) (h' : z ≤ t) (hbot : t ≠ ⊥)
    (htop : t = ⊤ → z = ⊤ → x = ⊥) : x + z < y + t := by
  rcases h'.eq_or_lt with (rfl | hlt)
  · rcases eq_or_ne z ⊤ with (rfl | hz)
    · obtain rfl := htop rfl rfl
      simpa
    lift z to ℝ using ⟨hz, hbot⟩
    exact add_lt_add_right_coe h z
  · exact add_lt_add h hlt

/-- See also `EReal.add_lt_add_of_lt_of_le'` for a version with weaker but less convenient
assumptions. -/
theorem add_lt_add_of_lt_of_le {x y z t : EReal} (h : x < y) (h' : z ≤ t) (hz : z ≠ ⊥)
    (ht : t ≠ ⊤) : x + z < y + t :=
  add_lt_add_of_lt_of_le' h h' (ne_bot_of_le_ne_bot hz h') fun ht' => (ht ht').elim

theorem add_lt_top {x y : EReal} (hx : x ≠ ⊤) (hy : y ≠ ⊤) : x + y < ⊤ :=
  add_lt_add hx.lt_top hy.lt_top

lemma add_ne_top {x y : EReal} (hx : x ≠ ⊤) (hy : y ≠ ⊤) : x + y ≠ ⊤ :=
  lt_top_iff_ne_top.mp <| add_lt_top hx hy

lemma add_ne_top_iff_ne_top₂ {x y : EReal} (hx : x ≠ ⊥) (hy : y ≠ ⊥) :
    x + y ≠ ⊤ ↔ x ≠ ⊤ ∧ y ≠ ⊤ := by
  simp [add_eq_top_iff, *]

lemma add_eq_top_iff_eq_top_left {x y : EReal} (hy : y ≠ ⊥) (hy' : y ≠ ⊤) :
    x + y = ⊤ ↔ x = ⊤ := by
  simp [add_eq_top_iff, *]

lemma add_ne_top_iff_ne_top_left {x y : EReal} (hy : y ≠ ⊥) (hy' : y ≠ ⊤) :
    x + y ≠ ⊤ ↔ x ≠ ⊤ := add_eq_top_iff_eq_top_left hy hy' |>.ne

lemma add_eq_top_iff_eq_top_right {x y : EReal} (hx : x ≠ ⊥) (hx' : x ≠ ⊤) :
    x + y = ⊤ ↔ y = ⊤ := add_comm x y ▸ add_eq_top_iff_eq_top_left hx hx'

lemma add_ne_top_iff_ne_top_right {x y : EReal} (hx : x ≠ ⊥) (hx' : x ≠ ⊤) :
    x + y ≠ ⊤ ↔ y ≠ ⊤ := add_eq_top_iff_eq_top_right hx hx' |>.ne

@[deprecated (since := "2026-07-02")] alias add_ne_top_iff_of_ne_bot_of_ne_top :=
  add_ne_top_iff_ne_top_left

@[simp] lemma add_coe_eq_top_iff {x : EReal} {y : ℝ} : x + y = ⊤ ↔ x = ⊤ := by
  simp [add_eq_top_iff_eq_top_left]

@[simp] lemma coe_add_eq_top_iff {x : ℝ} {y : EReal} : x + y = ⊤ ↔ y = ⊤ := by
  simp [add_eq_top_iff_eq_top_right]

/-! ### Negation -/

/-- negation on `EReal` -/
protected def neg : EReal → EReal
  | ⊥ => ⊤
  | ⊤ => ⊥
  | (x : ℝ) => (-x : ℝ)

instance : Neg EReal := ⟨EReal.neg⟩

instance : NegZeroClass EReal where
  neg_zero := congr_arg Real.toEReal neg_zero

instance : SMul ℤ EReal := ⟨zsmulRec (· • ·)⟩

/-- Domain of the signed difference. Opposite infinities are allowed. -/
def SubDomain (a b : EReal) : Prop :=
  (a ≠ ⊤ ∨ b ≠ ⊤) ∧ (a ≠ ⊥ ∨ b ≠ ⊥)

theorem subDomain_coe_ennreal (a b : ℝ≥0∞) :
    SubDomain a.toEReal b.toEReal ↔ a ≠ ⊤ ∨ b ≠ ⊤ := by
  simp [SubDomain]

/-- Solve elementary domain obligations only. Use `EReal.sub a b h` for
witnesses requiring a mathematical argument. -/
syntax (name := solveERealSubDomain) "ereal_sub_domain" : tactic

set_option linter.style.setOption false in
-- Bound the search used when elaborating a default domain witness.
macro_rules
  | `(tactic| ereal_sub_domain) => `(tactic|
      first
      | done
      | (set_option maxHeartbeats 4000 in
          solve
          | assumption
          | simp_all [EReal.SubDomain]
          | (constructor <;> solve
              | assumption
              | (left; solve | assumption | simp_all)
              | (right; solve | assumption | simp_all))
          | fail "extended-real subtraction excludes equal infinities"))

/-- Signed difference; neither diagonal infinity has a value. -/
protected def sub (a b : EReal) (_h : SubDomain a b := by ereal_sub_domain) : EReal :=
  a + -b

theorem sub_eq_add_neg {a b : EReal} (h : SubDomain a b) :
    EReal.sub a b h = a + -b := rfl

@[simp]
theorem neg_top : -(⊤ : EReal) = ⊥ :=
  rfl

@[simp]
theorem neg_bot : -(⊥ : EReal) = ⊤ :=
  rfl

@[simp, norm_cast] theorem coe_neg (x : ℝ) : (↑(-x) : EReal) = -↑x := rfl

@[simp, norm_cast] theorem coe_sub (x y : ℝ) :
    (↑(x - y) : EReal) = (x : EReal) - (y : EReal) := rfl

@[norm_cast]
theorem coe_zsmul (n : ℤ) (x : ℝ) : (↑(n • x) : EReal) = n • (x : EReal) := by
  let f : ℝ →+ EReal := ⟨⟨(↑), coe_zero⟩, coe_add⟩
  cases n with
  | ofNat k =>
    change f ((k : ℤ) • x) = k • f x
    rw [natCast_zsmul, map_nsmul]
  | negSucc k =>
    change f (Int.negSucc k • x) = -((k + 1) • f x)
    rw [negSucc_zsmul]
    exact (coe_neg _).trans (congrArg Neg.neg (f.map_nsmul (k + 1) x))

instance : InvolutiveNeg EReal where
  neg_neg a :=
    match a with
    | ⊥ => rfl
    | ⊤ => rfl
    | (a : ℝ) => congr_arg Real.toEReal (neg_neg a)

@[simp]
theorem toReal_neg_eq : ∀ {a : EReal}, toReal (-a) = -toReal a
  | ⊤ => by simp
  | ⊥ => by simp
  | (x : ℝ) => rfl

@[simp]
theorem neg_eq_top_iff {x : EReal} : -x = ⊤ ↔ x = ⊥ :=
  neg_injective.eq_iff' rfl

@[simp]
theorem neg_eq_bot_iff {x : EReal} : -x = ⊥ ↔ x = ⊤ :=
  neg_injective.eq_iff' rfl

@[simp]
theorem neg_eq_zero_iff {x : EReal} : -x = 0 ↔ x = 0 :=
  neg_injective.eq_iff' neg_zero

theorem neg_strictAnti : StrictAnti (- · : EReal → EReal) :=
  WithBot.strictAnti_iff.2 ⟨WithTop.strictAnti_iff.2
    ⟨coe_strictMono.comp_strictAnti fun _ _ => neg_lt_neg, fun _ => bot_lt_coe _⟩,
      WithTop.forall.2 ⟨bot_lt_top, fun _ => coe_lt_top _⟩⟩

@[simp] theorem neg_le_neg_iff {a b : EReal} : -a ≤ -b ↔ b ≤ a := neg_strictAnti.le_iff_ge

@[simp] theorem neg_lt_neg_iff {a b : EReal} : -a < -b ↔ b < a := neg_strictAnti.lt_iff_gt

/-- `-a ≤ b` if and only if `-b ≤ a` on `EReal`. -/
protected theorem neg_le {a b : EReal} : -a ≤ b ↔ -b ≤ a := by
  rw [← neg_le_neg_iff, neg_neg]

/-- If `-a ≤ b` then `-b ≤ a` on `EReal`. -/
protected theorem neg_le_of_neg_le {a b : EReal} (h : -a ≤ b) : -b ≤ a := EReal.neg_le.mp h

/-- `a ≤ -b` if and only if `b ≤ -a` on `EReal`. -/
protected theorem le_neg {a b : EReal} : a ≤ -b ↔ b ≤ -a := by
  rw [← neg_le_neg_iff, neg_neg]

/-- If `a ≤ -b` then `b ≤ -a` on `EReal`. -/
protected theorem le_neg_of_le_neg {a b : EReal} (h : a ≤ -b) : b ≤ -a := EReal.le_neg.mp h

/-- `-a < b` if and only if `-b < a` on `EReal`. -/
theorem neg_lt_comm {a b : EReal} : -a < b ↔ -b < a := by rw [← neg_lt_neg_iff, neg_neg]

/-- If `-a < b` then `-b < a` on `EReal`. -/
protected theorem neg_lt_of_neg_lt {a b : EReal} (h : -a < b) : -b < a := neg_lt_comm.mp h

/-- `-a < b` if and only if `-b < a` on `EReal`. -/
theorem lt_neg_comm {a b : EReal} : a < -b ↔ b < -a := by
  rw [← neg_lt_neg_iff, neg_neg]

@[simp] protected theorem neg_lt_zero {a : EReal} : -a < 0 ↔ 0 < a := by rw [neg_lt_comm, neg_zero]
@[simp] protected theorem neg_le_zero {a : EReal} : -a ≤ 0 ↔ 0 ≤ a := by rw [EReal.neg_le, neg_zero]
@[simp] protected theorem neg_pos {a : EReal} : 0 < -a ↔ a < 0 := by rw [lt_neg_comm, neg_zero]
@[simp] protected theorem neg_nonneg {a : EReal} : 0 ≤ -a ↔ a ≤ 0 := by rw [EReal.le_neg, neg_zero]

/-- If `a < -b` then `b < -a` on `EReal`. -/
protected theorem lt_neg_of_lt_neg {a b : EReal} (h : a < -b) : b < -a := lt_neg_comm.mp h

/-- Negation as an order reversing isomorphism on `EReal`. -/
def negOrderIso : EReal ≃o ERealᵒᵈ :=
  { Equiv.neg EReal with
    toFun := fun x => OrderDual.toDual (-x)
    invFun := fun x => -OrderDual.ofDual x
    map_rel_iff' := neg_le_neg_iff }

lemma neg_add {x y : EReal} (h1 : x ≠ ⊥ ∨ y ≠ ⊤) (h2 : x ≠ ⊤ ∨ y ≠ ⊥) :
    -(x + y) = -x + -y := by
  cases x <;> cases y <;> first
    | rfl
    | simp_all [← coe_add, ← coe_neg, add_comm]

lemma neg_sub {x y : EReal} (h : SubDomain x y) :
    -(EReal.sub x y h) = -x + y := by
  obtain ⟨ht, hb⟩ := h
  change -(x + -y) = _
  rw [neg_add (by simpa using hb) (by simpa using ht), neg_neg]

/-- Induction principle for `EReal`s splitting into cases `↑(x : ℝ≥0∞)` and `-↑(x : ℝ≥0∞)`.
In the latter case, we additionally assume `0 < x`. -/
@[elab_as_elim]
def recENNReal {motive : EReal → Sort*} (coe : ∀ x : ℝ≥0∞, motive x)
    (neg_coe : ∀ x : ℝ≥0∞, 0 < x → motive (-x)) (x : EReal) : motive x :=
  if hx : 0 ≤ x then coe_toENNReal hx ▸ coe _
  else
    haveI H₁ : 0 < -x := by simpa using hx
    haveI H₂ : x = -(-x).toENNReal := by rw [coe_toENNReal H₁.le, neg_neg]
    H₂ ▸ neg_coe _ <| by positivity

@[simp]
theorem recENNReal_coe_ennreal {motive : EReal → Sort*} (coe : ∀ x : ℝ≥0∞, motive x)
    (neg_coe : ∀ x : ℝ≥0∞, 0 < x → motive (-x)) (x : ℝ≥0∞) : recENNReal coe neg_coe x = coe x := by
  suffices ∀ y : EReal, x = y → (recENNReal coe neg_coe y : motive y) ≍ coe x from
    heq_iff_eq.mp (this x rfl)
  intro y hy
  have H₁ : 0 ≤ y := hy ▸ coe_ennreal_nonneg x
  obtain rfl : y.toENNReal = x := by simp [← hy]
  simp [recENNReal, H₁]

/-! ### Signed subtraction -/

@[simp] theorem sub_zero (a : EReal) : a - 0 = a := by simp [EReal.sub]
@[simp] theorem zero_sub (a : EReal) : 0 - a = -a := by simp [EReal.sub]

@[simp] theorem bot_sub (x : EReal) (hx : x ≠ ⊥) : ⊥ - x = ⊥ := bot_add _
@[simp] theorem sub_top (x : EReal) (hx : x ≠ ⊤) : x - ⊤ = ⊥ := add_bot _
@[simp] theorem top_sub_bot : (⊤ : EReal) - ⊥ = ⊤ := rfl
@[simp] theorem top_sub_coe (x : ℝ) : (⊤ : EReal) - (x : EReal) = ⊤ := rfl
@[simp] theorem coe_sub_bot (x : ℝ) : (x : EReal) - ⊥ = ⊤ := rfl

@[simp] lemma sub_bot {x : EReal} (h : x ≠ ⊥) : x - ⊥ = ⊤ := by
  cases x <;> first | rfl | contradiction

@[simp] lemma top_sub {x : EReal} (h : x ≠ ⊤) : ⊤ - x = ⊤ := by
  cases x <;> first | rfl | contradiction

@[simp] lemma sub_self {x : EReal} (ht : x ≠ ⊤) (hb : x ≠ ⊥) : x - x = 0 := by
  lift x to ℝ using ⟨ht, hb⟩
  simp [← coe_sub]

lemma sub_self_le_zero {x : EReal} (h : SubDomain x x) : x - x ≤ 0 := by
  obtain ⟨ht, hb⟩ := h
  rw [sub_self (ht.elim id id) (hb.elim id id)]

lemma sub_nonneg {x y : EReal} (h : SubDomain x y) : 0 ≤ x - y ↔ y ≤ x := by
  obtain ⟨ht, hb⟩ := h
  cases x <;> cases y <;> first
    | exact (ht.elim id id rfl).elim
    | exact (hb.elim id id rfl).elim
    | simp_all [← EReal.coe_sub]

lemma sub_nonpos {x y : EReal} (h : SubDomain x y) : x - y ≤ 0 ↔ x ≤ y := by
  obtain ⟨ht, hb⟩ := h
  cases x <;> cases y <;> first
    | exact (ht.elim id id rfl).elim
    | exact (hb.elim id id rfl).elim
    | simp_all [← EReal.coe_sub]

lemma sub_pos {x y : EReal} (h : SubDomain x y) : 0 < x - y ↔ y < x :=
  lt_iff_lt_of_le_iff_le (sub_nonpos h)

lemma sub_neg {x y : EReal} (h : SubDomain x y) : x - y < 0 ↔ x < y :=
  lt_iff_lt_of_le_iff_le (sub_nonneg h)

theorem sub_le_sub {x y z t : EReal} (h : x ≤ y) (h' : t ≤ z)
    (hl : SubDomain x z) (hr : SubDomain y t) : x - z ≤ y - t :=
  add_le_add h (neg_le_neg_iff.2 h')

theorem sub_lt_sub_of_lt_of_le {x y z t : EReal} (h : x < y) (h' : z ≤ t)
    (hz : z ≠ ⊥) (ht : t ≠ ⊤) :
    EReal.sub x t ⟨.inl h.ne_top, .inr (ne_bot_of_le_ne_bot hz h')⟩ <
      EReal.sub y z ⟨.inr (ne_top_of_le_ne_top ht h'), .inl h.ne_bot⟩ :=
  add_lt_add_of_lt_of_le h (neg_le_neg_iff.2 h') (by simp [ht]) (by simp [hz])

theorem coe_real_ereal_eq_coe_toNNReal_sub_coe_toNNReal (x : ℝ) :
    (x : EReal) =
      ((Real.toNNReal x : ℝ) : EReal) - ((Real.toNNReal (-x) : ℝ) : EReal) := by
  rw [← coe_sub]
  congr 1
  rcases le_total 0 x with hx | hx
  · simp [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx)]
  · simp [max_eq_right hx, max_eq_left (neg_nonneg.mpr hx)]

theorem toReal_sub {x y : EReal} (hx : x ≠ ⊤) (h'x : x ≠ ⊥)
    (hy : y ≠ ⊤) (h'y : y ≠ ⊥) : toReal (x - y) = toReal x - toReal y := by
  lift x to ℝ using ⟨hx, h'x⟩
  lift y to ℝ using ⟨hy, h'y⟩
  rfl

lemma toENNReal_sub {x y : EReal} (hy : 0 ≤ y) (h : SubDomain x y) :
    (x - y).toENNReal = ENNReal.monus x.toENNReal y.toENNReal := by
  obtain ⟨ht, hb⟩ := h
  cases x <;> cases y <;> first
    | exact (ht.elim id id rfl).elim
    | simp_all [← coe_sub, ENNReal.ofReal_monus]

lemma add_sub_add_comm {a b c d : EReal} (h1 : c ≠ ⊥ ∨ d ≠ ⊤)
    (h2 : c ≠ ⊤ ∨ d ≠ ⊥) (hs : SubDomain (a + b) (c + d))
    (hac : SubDomain a c) (hbd : SubDomain b d) :
    a + b - (c + d) = (a - c) + (b - d) := by
  simp only [EReal.sub, neg_add h1 h2]
  ac_rfl

lemma add_sub_cancel_right {a : EReal} {b : ℝ} : a + b - (b : EReal) = a := by
  change (a + ↑b) + -↑b = a
  rw [add_assoc, ← coe_neg, ← coe_add, add_neg_cancel, coe_zero, add_zero]

lemma add_sub_cancel_left {a : EReal} {b : ℝ} : b + a - (b : EReal) = a := by
  simpa only [EReal.sub, add_comm (b : EReal) a] using
    (add_sub_cancel_right (a := a) (b := b))

lemma sub_add_cancel {a : EReal} {b : ℝ} : a - (b : EReal) + b = a := by
  change (a + -↑b) + ↑b = a
  rw [add_assoc, ← coe_neg, ← coe_add, neg_add_cancel, coe_zero, add_zero]

lemma sub_add_cancel_right {a : EReal} {b : ℝ} : (b : EReal) - (a + b) = -a := by
  change ↑b + -(a + ↑b) = -a
  rw [neg_add (.inr (coe_ne_top b)) (.inr (coe_ne_bot b)), add_left_comm,
    ← coe_neg, ← coe_add, add_neg_cancel, coe_zero, add_zero]

lemma sub_add_cancel_left {a : EReal} {b : ℝ} : (b : EReal) - (b + a) = -a := by
  simpa only [EReal.sub, add_comm (b : EReal) a] using
    (sub_add_cancel_right (a := a) (b := b))

lemma le_sub_iff_add_le {a b c : EReal} (h : SubDomain c b) :
    a ≤ c - b ↔ a + b ≤ c := by
  obtain ⟨ht, hb⟩ := h
  cases b with
  | bot => simp [sub_bot (hb.resolve_right (by simp))]
  | coe b => rw [← (addLECancellable_coe b).add_le_add_iff_right, sub_add_cancel]
  | top =>
    have hc : c ≠ ⊤ := ht.resolve_right (by simp)
    rw [sub_top _ hc, le_bot_iff]
    constructor
    · rintro rfl
      simp
    · intro ha
      by_contra hn
      exact hc (top_unique ((add_top_of_ne_bot hn) ▸ ha))

lemma sub_le_iff_le_add {a b c : EReal} (h : SubDomain a b)
    (h₁ : b ≠ ⊥ ∨ c ≠ ⊤) (h₂ : b ≠ ⊤ ∨ c ≠ ⊥) :
    a - b ≤ c ↔ a ≤ c + b := by
  have hd : SubDomain c (-b) := by
    simpa [SubDomain, or_comm] using And.intro h₁ h₂
  simpa only [EReal.sub, neg_neg] using
    (le_sub_iff_add_le (a := a) hd).symm

protected theorem lt_sub_iff_add_lt {a b c : EReal} (h : SubDomain a b)
    (h₁ : b ≠ ⊥ ∨ c ≠ ⊤) (h₂ : b ≠ ⊤ ∨ c ≠ ⊥) :
    c < a - b ↔ c + b < a :=
  lt_iff_lt_of_le_iff_le (sub_le_iff_le_add h h₁ h₂)

theorem sub_le_of_le_add {a b c : EReal} (hd : SubDomain a c)
    (h : a ≤ b + c) : a - c ≤ b := by
  cases c with
  | bot =>
    obtain rfl : a = ⊥ := by simpa using h
    exact (hd.2.resolve_left (by simp) rfl).elim
  | coe c => exact (sub_le_iff_le_add hd (.inl (coe_ne_bot c)) (.inl (coe_ne_top c))).2 h
  | top => rw [sub_top _ (hd.1.resolve_right (by simp))]; exact bot_le

theorem sub_le_of_le_add' {a b c : EReal} (hd : SubDomain a b)
    (h : a ≤ b + c) : a - b ≤ c :=
  sub_le_of_le_add hd (add_comm b c ▸ h)

lemma add_le_of_le_sub {a b c : EReal} (hd : SubDomain b c)
    (h : a ≤ b - c) : a + c ≤ b := (le_sub_iff_add_le hd).1 h

lemma sub_lt_iff {a b c : EReal} (hd : SubDomain c b) :
    c - b < a ↔ c < a + b :=
  lt_iff_lt_of_le_iff_le (le_sub_iff_add_le hd)

lemma add_lt_of_lt_sub {a b c : EReal} (hd : SubDomain b c)
    (h : a < b - c) : a + c < b := by
  contrapose! h
  exact sub_le_of_le_add hd h

lemma sub_lt_of_lt_add {a b c : EReal} (hd : SubDomain a c)
    (h : a < b + c) : a - c < b :=
  (sub_lt_iff hd).2 h

lemma sub_lt_of_lt_add' {a b c : EReal} (hd : SubDomain a b)
    (h : a < b + c) : a - b < c :=
  sub_lt_of_lt_add hd (add_comm b c ▸ h)

lemma sub_lt_sub_of_le_of_gt {x y z t : EReal} (h : x ≤ y) (h' : z < t)
    (hx_top : x ≠ ⊤) (hy_bot : y ≠ ⊥) :
    EReal.sub x t ⟨.inl hx_top, .inr h'.ne_bot⟩ <
      EReal.sub y z ⟨.inr h'.ne_top, .inl hy_bot⟩ := by
  change x + -t < y + -z
  rw [add_comm x, add_comm y]
  exact add_lt_add_of_lt_of_le' (neg_lt_neg_iff.2 h') h hy_bot fun _ hx ↦ (hx_top hx).elim

/-! ### Addition and order -/

set_option backward.isDefEq.respectTransparency false in
lemma le_of_forall_lt_iff_le {x y : EReal} : (∀ z : ℝ, x < z → y ≤ z) ↔ y ≤ x := by
  refine ⟨fun h ↦ WithBot.le_of_forall_lt_iff_le.1 ?_, fun h _ x_z ↦ h.trans x_z.le⟩
  rw [WithTop.forall]
  aesop

set_option backward.isDefEq.respectTransparency false in
lemma ge_of_forall_gt_iff_ge {x y : EReal} : (∀ z : ℝ, z < y → z ≤ x) ↔ y ≤ x := by
  refine ⟨fun h ↦ WithBot.ge_of_forall_gt_iff_ge.1 ?_, fun h _ x_z ↦ x_z.le.trans h⟩
  rw [WithTop.forall]
  aesop

private lemma exists_lt_add_left {a b c : EReal} (hc : c < a + b) :
    ∃ a' < a, c < a' + b := by
  have hb : b ≠ ⊥ := by
    rintro rfl
    simp at hc
  have hd : SubDomain c b := ⟨.inl hc.ne_top, .inr hb⟩
  obtain ⟨a', hca', ha'⟩ := exists_between (sub_lt_of_lt_add hd hc)
  exact ⟨a', ha', (sub_lt_iff hd).1 hca'⟩


private lemma exists_lt_add_right {a b c : EReal} (hc : c < a + b) : ∃ b' < b, c < a + b' := by
  simp_rw [add_comm a] at hc ⊢; exact exists_lt_add_left hc

lemma add_le_of_forall_lt {a b c : EReal} (h : ∀ a' < a, ∀ b' < b, a' + b' ≤ c) : a + b ≤ c := by
  refine le_of_forall_lt_imp_le_of_dense fun d hd ↦ ?_
  obtain ⟨a', ha', hd⟩ := exists_lt_add_left hd
  obtain ⟨b', hb', hd⟩ := exists_lt_add_right hd
  exact hd.le.trans (h _ ha' _ hb')

lemma le_add_of_forall_gt {a b c : EReal} (h₁ : a ≠ ⊥ ∨ b ≠ ⊤) (h₂ : a ≠ ⊤ ∨ b ≠ ⊥)
    (h : ∀ a' > a, ∀ b' > b, c ≤ a' + b') : c ≤ a + b := by
  rw [← neg_le_neg_iff, neg_add h₁ h₂]
  refine add_le_of_forall_lt fun a' ha' b' hb' ↦ EReal.le_neg_of_le_neg ?_
  rw [neg_add (.inr hb'.ne_top) (.inl ha'.ne_top)]
  exact h _ (EReal.lt_neg_of_lt_neg ha') _ (EReal.lt_neg_of_lt_neg hb')

lemma _root_.ENNReal.toEReal_sub {x y : ℝ≥0∞} (hy_top : y ≠ ∞) (h_le : y ≤ x) :
    (ENNReal.monus x y).toEReal =
      EReal.sub x.toEReal y.toEReal
        ⟨.inr (by simpa using hy_top), .inr (coe_ennreal_ne_bot _)⟩ := by
  lift y to ℝ≥0 using hy_top
  cases x with
  | top => simp [coe_nnreal_eq_coe_real]
  | coe x =>
    simp only [← ENNReal.coe_monus, coe_nnreal_eq_coe_real,
      NNReal.coe_sub (mod_cast h_le), coe_sub]

/-! ### Multiplication -/

@[simp] lemma top_mul_top : (⊤ : EReal) * ⊤ = ⊤ := rfl

@[simp] lemma top_mul_bot : (⊤ : EReal) * ⊥ = ⊥ := rfl

@[simp] lemma bot_mul_top : (⊥ : EReal) * ⊤ = ⊥ := rfl

@[simp] lemma bot_mul_bot : (⊥ : EReal) * ⊥ = ⊤ := rfl

lemma coe_mul_top_of_pos {x : ℝ} (h : 0 < x) : (x : EReal) * ⊤ = ⊤ :=
  ite_eq_left h

lemma coe_mul_top_of_neg {x : ℝ} (h : x < 0) : (x : EReal) * ⊤ = ⊥ :=
  (ite_eq_right h.not_gt).trans (ite_eq_right h.ne)

lemma top_mul_coe_of_pos {x : ℝ} (h : 0 < x) : (⊤ : EReal) * x = ⊤ :=
  ite_eq_left h

lemma top_mul_coe_of_neg {x : ℝ} (h : x < 0) : (⊤ : EReal) * x = ⊥ :=
  (ite_eq_right h.not_gt).trans (ite_eq_right h.ne)

lemma mul_top_of_pos : ∀ {x : EReal}, 0 < x → x * ⊤ = ⊤
  | ⊥, h => absurd h not_lt_bot
  | (x : ℝ), h => coe_mul_top_of_pos (EReal.coe_pos.1 h)
  | ⊤, _ => rfl

lemma mul_top_of_neg : ∀ {x : EReal}, x < 0 → x * ⊤ = ⊥
  | ⊥, _ => rfl
  | (x : ℝ), h => coe_mul_top_of_neg (EReal.coe_neg'.1 h)
  | ⊤, h => absurd h not_top_lt

lemma top_mul_of_pos {x : EReal} (h : 0 < x) : ⊤ * x = ⊤ := by
  rw [EReal.mul_comm]
  exact mul_top_of_pos h

lemma top_mul_of_neg {x : EReal} (h : x < 0) : ⊤ * x = ⊥ := by
  rw [EReal.mul_comm]
  exact mul_top_of_neg h

lemma top_mul_coe_ennreal {x : ℝ≥0∞} (hx : x ≠ 0) : ⊤ * (x : EReal) = ⊤ :=
  top_mul_of_pos <| coe_ennreal_pos.mpr <| pos_iff_ne_zero.mpr hx

lemma coe_ennreal_mul_top {x : ℝ≥0∞} (hx : x ≠ 0) : (x : EReal) * ⊤ = ⊤ := by
  rw [EReal.mul_comm, top_mul_coe_ennreal hx]

lemma coe_mul_bot_of_pos {x : ℝ} (h : 0 < x) : (x : EReal) * ⊥ = ⊥ :=
  ite_eq_left h

lemma coe_mul_bot_of_neg {x : ℝ} (h : x < 0) : (x : EReal) * ⊥ = ⊤ :=
  (ite_eq_right h.not_gt).trans (ite_eq_right h.ne)

lemma bot_mul_coe_of_pos {x : ℝ} (h : 0 < x) : (⊥ : EReal) * x = ⊥ :=
  ite_eq_left h

lemma bot_mul_coe_of_neg {x : ℝ} (h : x < 0) : (⊥ : EReal) * x = ⊤ :=
  (ite_eq_right h.not_gt).trans (ite_eq_right h.ne)

lemma mul_bot_of_pos : ∀ {x : EReal}, 0 < x → x * ⊥ = ⊥
  | ⊥, h => absurd h not_lt_bot
  | (x : ℝ), h => coe_mul_bot_of_pos (EReal.coe_pos.1 h)
  | ⊤, _ => rfl

lemma mul_bot_of_neg : ∀ {x : EReal}, x < 0 → x * ⊥ = ⊤
  | ⊥, _ => rfl
  | (x : ℝ), h => coe_mul_bot_of_neg (EReal.coe_neg'.1 h)
  | ⊤, h => absurd h not_top_lt

lemma bot_mul_of_pos {x : EReal} (h : 0 < x) : ⊥ * x = ⊥ := by
  rw [EReal.mul_comm]
  exact mul_bot_of_pos h

lemma bot_mul_of_neg {x : EReal} (h : x < 0) : ⊥ * x = ⊤ := by
  rw [EReal.mul_comm]
  exact mul_bot_of_neg h

lemma toReal_mul {x y : EReal} : toReal (x * y) = toReal x * toReal y := by
  induction x, y using induction₂_symm with
  | top_zero | zero_bot | top_top | top_bot | bot_bot => simp
  | symm h => rwa [mul_comm, EReal.mul_comm]
  | coe_coe => norm_cast
  | top_pos _ h => simp [top_mul_coe_of_pos h]
  | top_neg _ h => simp [top_mul_coe_of_neg h]
  | pos_bot _ h => simp [coe_mul_bot_of_pos h]
  | neg_bot _ h => simp [coe_mul_bot_of_neg h]

instance : NoZeroDivisors EReal where
  eq_zero_or_eq_zero_of_mul_eq_zero := by
    intro a b h
    contrapose! h
    cases a <;> cases b <;> try {· simp_all [← EReal.coe_mul]}
    · rcases lt_or_gt_of_ne h.2 with (h | h)
        <;> simp [EReal.bot_mul_of_neg, EReal.bot_mul_of_pos, h]
    · rcases lt_or_gt_of_ne h.1 with (h | h)
        <;> simp [EReal.mul_bot_of_pos, EReal.mul_bot_of_neg, h]
    · rcases lt_or_gt_of_ne h.1 with (h | h)
        <;> simp [EReal.mul_top_of_neg, EReal.mul_top_of_pos, h]
    · rcases lt_or_gt_of_ne h.2 with (h | h)
        <;> simp [EReal.top_mul_of_pos, EReal.top_mul_of_neg, h]

lemma mul_pos_iff {a b : EReal} : 0 < a * b ↔ 0 < a ∧ 0 < b ∨ a < 0 ∧ b < 0 := by
  induction a, b using EReal.induction₂_symm with
  | symm h => simp [EReal.mul_comm, h, and_comm]
  | top_top => simp
  | top_pos _ hx => simp [EReal.top_mul_coe_of_pos hx, hx]
  | top_zero => simp
  | top_neg _ hx => simp [hx, EReal.top_mul_coe_of_neg hx, le_of_lt]
  | top_bot => simp
  | pos_bot _ hx => simp [hx, EReal.coe_mul_bot_of_pos hx, le_of_lt]
  | coe_coe x y => simp [← coe_mul, _root_.mul_pos_iff]
  | zero_bot => simp
  | neg_bot _ hx => simp [hx, EReal.coe_mul_bot_of_neg hx]
  | bot_bot => simp

lemma mul_nonneg_iff {a b : EReal} : 0 ≤ a * b ↔ 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0 := by
  simp_rw [le_iff_lt_or_eq, mul_pos_iff, zero_eq_mul (a := a)]
  rcases lt_trichotomy a 0 with (h | h | h) <;> rcases lt_trichotomy b 0 with (h' | h' | h')
    <;> simp only [h, h', true_or, true_and, or_true, and_true] <;> tauto

protected lemma mul_nonneg {a b : EReal} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b :=
  mul_nonneg_iff.mpr <| .inl ⟨ha, hb⟩

/-- The product of two positive extended real numbers is positive. -/
protected lemma mul_pos {a b : EReal} (ha : 0 < a) (hb : 0 < b) : 0 < a * b :=
  mul_pos_iff.mpr (Or.inl ⟨ha, hb⟩)

/-- Induct on two ereals by performing case splits on the sign of one whenever the other is
infinite. This version eliminates some cases by assuming that `P x y` implies `P (-x) y` for all
`x`, `y`. -/
@[elab_as_elim]
lemma induction₂_neg_left {P : EReal → EReal → Prop} (neg_left : ∀ {x y}, P x y → P (-x) y)
    (top_top : P ⊤ ⊤) (top_pos : ∀ x : ℝ, 0 < x → P ⊤ x)
    (top_zero : P ⊤ 0) (top_neg : ∀ x : ℝ, x < 0 → P ⊤ x) (top_bot : P ⊤ ⊥)
    (zero_top : P 0 ⊤) (zero_bot : P 0 ⊥)
    (pos_top : ∀ x : ℝ, 0 < x → P x ⊤) (pos_bot : ∀ x : ℝ, 0 < x → P x ⊥)
    (coe_coe : ∀ x y : ℝ, P x y) : ∀ x y, P x y :=
  have : ∀ y, (∀ x : ℝ, 0 < x → P x y) → ∀ x : ℝ, x < 0 → P x y := fun _ h x hx =>
    neg_neg (x : EReal) ▸ neg_left <| h _ (neg_pos_of_neg hx)
  @induction₂ P top_top top_pos top_zero top_neg top_bot pos_top pos_bot zero_top
    coe_coe zero_bot (this _ pos_top) (this _ pos_bot) (neg_left top_top)
    (fun x hx => neg_left <| top_pos x hx) (neg_left top_zero)
    (fun x hx => neg_left <| top_neg x hx) (neg_left top_bot)

/-- Induct on two ereals by performing case splits on the sign of one whenever the other is
infinite. This version eliminates some cases by assuming that `P` is symmetric and `P x y` implies
`P (-x) y` for all `x`, `y`. -/
@[elab_as_elim]
lemma induction₂_symm_neg {P : EReal → EReal → Prop}
    (symm : ∀ {x y}, P x y → P y x)
    (neg_left : ∀ {x y}, P x y → P (-x) y) (top_top : P ⊤ ⊤)
    (top_pos : ∀ x : ℝ, 0 < x → P ⊤ x) (top_zero : P ⊤ 0) (coe_coe : ∀ x y : ℝ, P x y) :
    ∀ x y, P x y :=
  have neg_right : ∀ {x y}, P x y → P x (-y) := fun h => symm <| neg_left <| symm h
  have : ∀ x, (∀ y : ℝ, 0 < y → P x y) → ∀ y : ℝ, y < 0 → P x y := fun _ h y hy =>
    neg_neg (y : EReal) ▸ neg_right (h _ (neg_pos_of_neg hy))
  @induction₂_neg_left P neg_left top_top top_pos top_zero (this _ top_pos) (neg_right top_top)
    (symm top_zero) (symm <| neg_left top_zero) (fun x hx => symm <| top_pos x hx)
    (fun x hx => symm <| neg_left <| top_pos x hx) coe_coe

protected lemma neg_mul (x y : EReal) : -x * y = -(x * y) := by
  induction x, y using induction₂_neg_left with
  | top_zero | zero_top | zero_bot => simp only [zero_mul, mul_zero, neg_zero]
  | top_top | top_bot => rfl
  | neg_left h => rw [h, neg_neg, neg_neg]
  | coe_coe => norm_cast; exact neg_mul _ _
  | top_pos _ h => rw [top_mul_coe_of_pos h, neg_top, bot_mul_coe_of_pos h]
  | pos_top _ h => rw [coe_mul_top_of_pos h, neg_top, ← coe_neg,
    coe_mul_top_of_neg (neg_neg_of_pos h)]
  | top_neg _ h => rw [top_mul_coe_of_neg h, neg_top, bot_mul_coe_of_neg h, neg_bot]
  | pos_bot _ h => rw [coe_mul_bot_of_pos h, neg_bot, ← coe_neg,
    coe_mul_bot_of_neg (neg_neg_of_pos h)]

instance : HasDistribNeg EReal where
  neg_mul := EReal.neg_mul
  mul_neg := fun x y => by
    rw [x.mul_comm, x.mul_comm]
    exact y.neg_mul x

lemma mul_neg_iff {a b : EReal} : a * b < 0 ↔ 0 < a ∧ b < 0 ∨ a < 0 ∧ 0 < b := by
  nth_rw 1 [← neg_zero]
  rw [lt_neg_comm, ← mul_neg a, mul_pos_iff, neg_lt_comm, lt_neg_comm, neg_zero]

lemma mul_nonpos_iff {a b : EReal} : a * b ≤ 0 ↔ 0 ≤ a ∧ b ≤ 0 ∨ a ≤ 0 ∧ 0 ≤ b := by
  nth_rw 1 [← neg_zero]
  rw [EReal.le_neg, ← mul_neg, mul_nonneg_iff, EReal.neg_le, EReal.le_neg, neg_zero]

lemma mul_eq_top (a b : EReal) :
    a * b = ⊤ ↔ (a = ⊥ ∧ b < 0) ∨ (a < 0 ∧ b = ⊥) ∨ (a = ⊤ ∧ 0 < b) ∨ (0 < a ∧ b = ⊤) := by
  induction a, b using EReal.induction₂_symm with
  | symm h => grind [EReal.mul_comm]
  | top_top => simp
  | top_pos _ hx => simp [EReal.top_mul_coe_of_pos hx, hx]
  | top_zero => simp
  | top_neg _ hx => simp [hx.le, EReal.top_mul_coe_of_neg hx]
  | top_bot => simp
  | pos_bot _ hx => simp [hx.le, EReal.coe_mul_bot_of_pos hx]
  | coe_coe x y =>
    simpa only [EReal.coe_ne_bot, EReal.coe_neg', false_and, and_false, EReal.coe_ne_top,
      EReal.coe_pos, or_self, iff_false, EReal.coe_mul] using! EReal.coe_ne_top _
  | zero_bot => simp
  | neg_bot _ hx => simp [hx, EReal.coe_mul_bot_of_neg hx]
  | bot_bot => simp

lemma mul_ne_top (a b : EReal) :
    a * b ≠ ⊤ ↔ (a ≠ ⊥ ∨ 0 ≤ b) ∧ (0 ≤ a ∨ b ≠ ⊥) ∧ (a ≠ ⊤ ∨ b ≤ 0) ∧ (a ≤ 0 ∨ b ≠ ⊤) := by
  rw [ne_eq, mul_eq_top]
  -- push the negation while keeping the disjunctions, that is converting `¬(p ∧ q)` into `¬p ∨ ¬q`
  -- rather than `p → ¬q`, since we already have disjunctions in the rhs
  push +distrib Not
  rfl

lemma mul_eq_bot (a b : EReal) :
    a * b = ⊥ ↔ (a = ⊥ ∧ 0 < b) ∨ (0 < a ∧ b = ⊥) ∨ (a = ⊤ ∧ b < 0) ∨ (a < 0 ∧ b = ⊤) := by
  rw [← neg_eq_top_iff, ← EReal.neg_mul, mul_eq_top, neg_eq_bot_iff, neg_eq_top_iff,
    neg_lt_comm, lt_neg_comm, neg_zero]
  tauto

lemma mul_ne_bot (a b : EReal) :
    a * b ≠ ⊥ ↔ (a ≠ ⊥ ∨ b ≤ 0) ∧ (a ≤ 0 ∨ b ≠ ⊥) ∧ (a ≠ ⊤ ∨ 0 ≤ b) ∧ (0 ≤ a ∨ b ≠ ⊤) := by
  rw [ne_eq, mul_eq_bot]
  push +distrib Not
  rfl

/-- `EReal.toENNReal` is multiplicative. For the version with the nonnegativity
hypothesis on the second variable, see `EReal.toENNReal_mul'`. -/
lemma toENNReal_mul {x y : EReal} (hx : 0 ≤ x) :
    (x * y).toENNReal = x.toENNReal * y.toENNReal := by
  induction x <;> induction y
    <;> try {· simp_all [mul_nonpos_iff, ofReal_mul, ← coe_mul]}
  · rcases eq_or_lt_of_le hx with (hx | hx)
    · simp [← hx]
    · simp_all [mul_top_of_pos hx]
  · rename_i a
    rcases lt_trichotomy a 0 with (ha | ha | ha)
    · simp_all [le_of_lt, top_mul_of_neg (EReal.coe_neg'.mpr ha)]
    · simp [ha]
    · simp_all [top_mul_of_pos (EReal.coe_pos.mpr ha)]

/-- `EReal.toENNReal` is multiplicative. For the version with the nonnegativity
hypothesis on the first variable, see `EReal.toENNReal_mul`. -/
lemma toENNReal_mul' {x y : EReal} (hy : 0 ≤ y) :
    (x * y).toENNReal = x.toENNReal * y.toENNReal := by
  rw [EReal.mul_comm, toENNReal_mul hy, mul_comm]

lemma right_distrib_of_nonneg {a b c : EReal} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) * c = a * c + b * c := by
  lift a to ℝ≥0∞ using ha
  lift b to ℝ≥0∞ using hb
  cases c using recENNReal with
  | coe c => exact_mod_cast add_mul a b c
  | neg_coe c hc =>
    simp only [mul_neg, ← coe_ennreal_add, ← coe_ennreal_mul, add_mul]
    rw [coe_ennreal_add, EReal.neg_add (.inl (coe_ennreal_ne_bot _))
      (.inr (coe_ennreal_ne_bot _))]

lemma left_distrib_of_nonneg {a b c : EReal} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    c * (a + b) = c * a + c * b := by
  nth_rewrite 1 [EReal.mul_comm]; nth_rewrite 2 [EReal.mul_comm]; nth_rewrite 3 [EReal.mul_comm]
  exact right_distrib_of_nonneg ha hb

theorem SubDomain.of_nonneg_of_nonpos {b c : EReal} (hb : 0 ≤ b) (hc : c ≤ 0) :
    SubDomain b c :=
  ⟨.inr (ne_top_of_le_ne_top (by simp) hc), .inl (ne_bot_of_le_ne_bot (by simp) hb)⟩

theorem SubDomain.mul_of_nonneg_of_nonpos (a : EReal) {b c : EReal}
    (hb : 0 ≤ b) (hc : c ≤ 0) : SubDomain (a * b) (a * c) := by
  rcases le_total 0 a with ha | ha
  · exact SubDomain.of_nonneg_of_nonpos (mul_nonneg_iff.2 (.inl ⟨ha, hb⟩))
      (mul_nonpos_iff.2 (.inl ⟨ha, hc⟩))
  · have h := SubDomain.of_nonneg_of_nonpos (mul_nonneg_iff.2 (.inr ⟨ha, hc⟩))
      (mul_nonpos_iff.2 (.inr ⟨ha, hb⟩))
    exact ⟨h.1.symm, h.2.symm⟩

lemma mul_sub_of_nonneg_of_nonpos {a b c : EReal} (hb : 0 ≤ b) (hc : c ≤ 0) :
    a * EReal.sub b c (SubDomain.of_nonneg_of_nonpos hb hc) =
      EReal.sub (a * b) (a * c) (SubDomain.mul_of_nonneg_of_nonpos a hb hc) := by
  change a * (b + -c) = a * b + -(a * c)
  rw [left_distrib_of_nonneg hb (by simpa), mul_neg]

lemma left_distrib_of_nonneg_of_ne_top {x : EReal} (hx_nonneg : 0 ≤ x)
    (hx_ne_top : x ≠ ⊤) (y z : EReal) :
    x * (y + z) = x * y + x * z := by
  cases hx_nonneg.eq_or_lt' with
  | inl hx0 => simp [hx0]
  | inr hx0 =>
  lift x to ℝ using ⟨hx_ne_top, hx0.ne_bot⟩
  cases y <;> cases z <;>
    simp [mul_bot_of_pos hx0, mul_top_of_pos hx0, ← coe_mul, ← coe_add, mul_add]

lemma right_distrib_of_nonneg_of_ne_top {x : EReal} (hx_nonneg : 0 ≤ x)
    (hx_ne_top : x ≠ ⊤) (y z : EReal) :
    (y + z) * x = y * x + z * x := by
  simpa only [EReal.mul_comm] using left_distrib_of_nonneg_of_ne_top hx_nonneg hx_ne_top y z

theorem SubDomain.mul_left {a b c : EReal} (h : SubDomain b c) (ha : 0 ≤ a) (ha' : a ≠ ⊤) :
    SubDomain (a * b) (a * c) := by
  have hab : a ≠ ⊥ := ne_bot_of_le_ne_bot (by simp) ha
  simp only [SubDomain, mul_ne_top, mul_ne_bot, ha, true_or, true_and] at *
  tauto

lemma mul_sub_of_nonneg_of_ne_top {a b c : EReal} (ha : 0 ≤ a) (ha' : a ≠ ⊤)
    (hd : SubDomain b c) :
    a * (b - c) = EReal.sub (a * b) (a * c) (hd.mul_left ha ha') := by
  change a * (b + -c) = a * b + -(a * c)
  rw [left_distrib_of_nonneg_of_ne_top ha ha', mul_neg]

lemma sub_mul_of_nonneg_of_ne_top {a b c : EReal} (ha : 0 ≤ a) (ha' : a ≠ ⊤)
    (hd : SubDomain b c) :
    (b - c) * a =
      EReal.sub (b * a) (c * a) (by simpa only [EReal.mul_comm] using hd.mul_left ha ha') := by
  change (b + -c) * a = b * a + -(c * a)
  rw [right_distrib_of_nonneg_of_ne_top ha ha', neg_mul]

@[simp]
lemma nsmul_eq_mul (n : ℕ) (x : EReal) : n • x = n * x := by
  induction n with
  | zero => rw [zero_smul, Nat.cast_zero, zero_mul]
  | succ n ih =>
    rw [succ_nsmul, ih, Nat.cast_succ]
    convert! (EReal.right_distrib_of_nonneg _ _).symm <;> simp

end EReal

namespace Mathlib.Meta.Positivity

open Lean Meta Qq Function

/-- Extension for the `positivity` tactic: sum of two `EReal`s. -/
@[positivity (_ + _ : EReal)]
meta def evalERealAdd : PositivityExt where eval {u α} zα pα? e :=
  match pα? with | none => pure .none | some pα => do
  match u, α, e with
  | 0, ~q(EReal), ~q($a + $b) =>
    assertInstancesCommute
    match ← core zα pα a with
    | .positive pa =>
      match (← core zα pα b).toNonneg with
      | some pb => pure (.positive q(EReal.add_pos_of_pos_of_nonneg $pa $pb))
      | _ => pure .none
    | .nonnegative pa =>
      match ← core zα pα b with
      | .positive pb => pure (.positive q(Right.add_pos_of_nonneg_of_pos $pa $pb))
      | .nonnegative pb => pure (.nonnegative q(add_nonneg $pa $pb))
      | _ => pure .none
    | _ => pure .none
  | _, _, _ => throwError "not a sum of 2 `EReal`s"

/-- Extension for the `positivity` tactic: product of two `EReal`s. -/
@[positivity (_ * _ : EReal)]
meta def evalERealMul : PositivityExt where eval {u α} zα pα? e :=
  match pα? with | none => pure .none | some pα => do
  match u, α, e with
  | 0, ~q(EReal), ~q($a * $b) =>
    assertInstancesCommute
    match ← core zα pα a with
    | .positive pa =>
      match ← core zα pα b with
      | .positive pb => pure <| .positive q(EReal.mul_pos $pa $pb)
      | .nonnegative pb => pure <| .nonnegative q(EReal.mul_nonneg (le_of_lt $pa) $pb)
      | .nonzero pb => pure <| .nonzero q(mul_ne_zero (ne_of_gt $pa) $pb)
      | _ => pure .none
    | .nonnegative pa =>
      match (← core zα pα b).toNonneg with
      | some pb => pure (.nonnegative q(EReal.mul_nonneg $pa $pb))
      | none => pure .none
    | .nonzero pa =>
      match (← core zα pα b).toNonzero with
      | some pb => pure (.nonzero q(mul_ne_zero $pa $pb))
      | none => pure .none
    | _ => pure .none
  | _, _, _ => throwError "not a product of 2 `EReal`s"

end Mathlib.Meta.Positivity
