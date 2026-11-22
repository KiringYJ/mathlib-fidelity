/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Robert Y. Lewis
-/
module

public import Mathlib.Algebra.Order.CauSeq.Basic
public import Mathlib.Algebra.Ring.Action.Rat
public import Mathlib.Tactic.FastInstance

/-!
# Cauchy completion

This file generalizes the Cauchy completion of `(ℚ, abs)` to the completion of a ring
with absolute value.
-/

@[expose] public section


namespace CauSeq.Completion

open CauSeq

section

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
variable {β : Type*} [Ring β] (abv : β → α) [IsAbsoluteValue abv]

-- TODO: rename this to `CauSeq.Completion` instead of `CauSeq.Completion.Cauchy`.
/-- The Cauchy completion of a ring with absolute value. -/
def Cauchy :=
  @Quotient (CauSeq _ abv) CauSeq.equiv

variable {abv}

/-- The map from Cauchy sequences into the Cauchy completion. -/
def mk : CauSeq _ abv → Cauchy abv :=
  Quotient.mk''

@[simp]
theorem mk_eq_mk (f : CauSeq _ abv) : @Eq (Cauchy abv) ⟦f⟧ (mk f) :=
  rfl

theorem mk_eq {f g : CauSeq _ abv} : mk f = mk g ↔ LimZero (f - g) :=
  Quotient.eq

/-- The map from the original ring into the Cauchy completion. -/
def ofRat (x : β) : Cauchy abv :=
  mk (const abv x)

instance : Zero (Cauchy abv) :=
  ⟨ofRat 0⟩

instance : One (Cauchy abv) :=
  ⟨ofRat 1⟩

instance : Inhabited (Cauchy abv) :=
  ⟨0⟩

theorem ofRat_zero : (ofRat 0 : Cauchy abv) = 0 :=
  rfl

theorem ofRat_one : (ofRat 1 : Cauchy abv) = 1 :=
  rfl

@[simp]
theorem mk_eq_zero {f : CauSeq _ abv} : mk f = 0 ↔ LimZero f := by
  have : mk f = 0 ↔ LimZero (f - 0) := Quotient.eq
  rwa [sub_zero] at this

instance : Add (Cauchy abv) :=
  ⟨(Quotient.map₂ (· + ·)) fun _ _ hf _ _ hg => add_equiv_add hf hg⟩

@[simp]
theorem mk_add (f g : CauSeq β abv) : mk f + mk g = mk (f + g) :=
  rfl

instance : Neg (Cauchy abv) :=
  ⟨(Quotient.map Neg.neg) fun _ _ hf => neg_equiv_neg hf⟩

@[simp]
theorem mk_neg (f : CauSeq β abv) : -mk f = mk (-f) :=
  rfl

instance : Mul (Cauchy abv) :=
  ⟨(Quotient.map₂ (· * ·)) fun _ _ hf _ _ hg => mul_equiv_mul hf hg⟩

@[simp]
theorem mk_mul (f g : CauSeq β abv) : mk f * mk g = mk (f * g) :=
  rfl

instance : Sub (Cauchy abv) :=
  ⟨(Quotient.map₂ Sub.sub) fun _ _ hf _ _ hg => sub_equiv_sub hf hg⟩

@[simp]
theorem mk_sub (f g : CauSeq β abv) : mk f - mk g = mk (f - g) :=
  rfl

instance {γ : Type*} [SMul γ β] [IsScalarTower γ β β] : SMul γ (Cauchy abv) :=
  ⟨fun c => (Quotient.map (c • ·)) fun _ _ hf => smul_equiv_smul _ hf⟩

@[simp]
theorem mk_smul {γ : Type*} [SMul γ β] [IsScalarTower γ β β] (c : γ) (f : CauSeq β abv) :
    c • mk f = mk (c • f) :=
  rfl

instance : Pow (Cauchy abv) ℕ :=
  ⟨fun x n => Quotient.map (· ^ n) (fun _ _ hf => pow_equiv_pow hf _) x⟩

@[simp]
theorem mk_pow (n : ℕ) (f : CauSeq β abv) : mk f ^ n = mk (f ^ n) :=
  rfl

instance : NatCast (Cauchy abv) :=
  ⟨fun n => mk n⟩

instance : IntCast (Cauchy abv) :=
  ⟨fun n => mk n⟩

@[simp]
theorem ofRat_natCast (n : ℕ) : (ofRat n : Cauchy abv) = n :=
  rfl

@[simp]
theorem ofRat_intCast (z : ℤ) : (ofRat z : Cauchy abv) = z :=
  rfl

theorem ofRat_add (x y : β) :
    ofRat (x + y) = (ofRat x + ofRat y : Cauchy abv) :=
  congr_arg mk (const_add _ _)

theorem ofRat_neg (x : β) : ofRat (-x) = (-ofRat x : Cauchy abv) :=
  congr_arg mk (const_neg _)

theorem ofRat_mul (x y : β) :
    ofRat (x * y) = (ofRat x * ofRat y : Cauchy abv) :=
  congr_arg mk (const_mul _ _)

theorem ofRat_injective : Function.Injective (ofRat : β → Cauchy abv) := fun x y h => by
  simpa [ofRat, mk_eq, ← const_sub, const_limZero, sub_eq_zero] using h

instance Cauchy.ring : Ring (Cauchy abv) := fast_instance%
  Function.Surjective.ring mk Quotient.mk'_surjective rfl rfl
    (fun _ _ => (mk_add _ _).symm) (fun _ _ => (mk_mul _ _).symm) (fun _ => (mk_neg _).symm)
    (fun _ _ => (mk_sub _ _).symm) (fun _ _ => (mk_smul _ _).symm) (fun _ _ => (mk_smul _ _).symm)
    (fun _ _ => (mk_pow _ _).symm) (fun _ => rfl) fun _ => rfl

/-- `CauSeq.Completion.ofRat` as a `RingHom` -/
@[simps]
def ofRatRingHom : β →+* (Cauchy abv) where
  toFun := ofRat
  map_zero' := ofRat_zero
  map_one' := ofRat_one
  map_add' := ofRat_add
  map_mul' := ofRat_mul

theorem ofRat_sub (x y : β) : ofRat (x - y) = (ofRat x - ofRat y : Cauchy abv) :=
  congr_arg mk (const_sub _ _)

noncomputable instance Cauchy.instNonTrivial [Nontrivial β] : Nontrivial (Cauchy abv) :=
  ofRat_injective.nontrivial

instance Cauchy.charZero [CharZero β] : CharZero (Cauchy abv) where
  cast_injective m n h := Nat.cast_injective (R := β) <|
    ofRat_injective (abv := abv) <| by
      simpa only [ofRat_natCast] using h

end

section

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
variable {β : Type*} [CommRing β] {abv : β → α} [IsAbsoluteValue abv]

instance Cauchy.commRing : CommRing (Cauchy abv) := fast_instance%
  Function.Surjective.commRing mk Quotient.mk'_surjective rfl rfl
    (fun _ _ => (mk_add _ _).symm) (fun _ _ => (mk_mul _ _).symm) (fun _ => (mk_neg _).symm)
    (fun _ _ => (mk_sub _ _).symm) (fun _ _ => (mk_smul _ _).symm) (fun _ _ => (mk_smul _ _).symm)
    (fun _ _ => (mk_pow _ _).symm) (fun _ => rfl) fun _ => rfl

end

section

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
variable {β : Type*} [DivisionRing β] {abv : β → α} [IsAbsoluteValue abv]

/-- A sequence with nonzero limit determines a unit of the Cauchy completion. Its inverse is
represented by the reciprocal of a nonzero tail, with no inversion at zero entries. -/
noncomputable def mkUnit (f : CauSeq β abv) (hf : ¬LimZero f) : (Cauchy abv)ˣ where
  val := mk f
  inv := mk (inv f hf)
  val_inv := by
    rw [mk_mul]
    exact mk_eq.mpr (CauSeq.mul_inv_cancel hf)
  inv_val := by
    rw [mk_mul]
    exact mk_eq.mpr (CauSeq.inv_mul_cancel hf)

@[simp] theorem val_mkUnit (f : CauSeq β abv) (hf : ¬LimZero f) :
    (mkUnit f hf : Cauchy abv) = mk f := rfl

theorem mkUnit_eq {f g : CauSeq β abv} (hf : ¬LimZero f) (hg : ¬LimZero g)
    (h : f ≈ g) : mkUnit f hf = mkUnit g hg :=
  Units.ext (mk_eq.mpr h)

@[simp] theorem inv_mk {f : CauSeq β abv} {h : IsUnit (mk f)} :
    (mk f)⁻¹ = mk (inv f fun hl ↦ h.ne_zero (mk_eq_zero.mpr hl)) :=
  inv_eq_val_inv_of_eq_val₀ (mkUnit f _) rfl

theorem cau_seq_zero_ne_one : ¬(0 : CauSeq _ abv) ≈ 1 := fun h ↦
  have : LimZero (1 - 0 : CauSeq _ abv) := Setoid.symm h
  have : LimZero (1 : CauSeq _ abv) := by simpa
  one_ne_zero <| const_limZero.1 this

theorem zero_ne_one : (0 : (Cauchy abv)) ≠ 1 := fun h => cau_seq_zero_ne_one <| mk_eq.1 h

/-- A Cauchy completion of characteristic zero has a base of characteristic zero. -/
theorem _root_.CharZero.of_cauchy [CharZero (Cauchy abv)] : CharZero β :=
  CharZero.of_map_natCast (ofRat : β → Cauchy abv) ofRat_natCast

private theorem smul_eq_ofRat_mul {γ : Type*} [SMul γ β] [IsScalarTower γ β β] (c : γ) (q : β)
    (hc : ∀ b : β, c • b = q * b) (x : Cauchy abv) : c • x = ofRat q * x := by
  induction x using Quotient.inductionOn with
  | _ f =>
    change c • mk f = mk (const abv q) * mk f
    rw [mk_smul, mk_mul]
    apply congrArg mk
    ext n
    exact hc (f n)

/-- The Cauchy completion forms a division ring. In characteristic zero, its rational embeddings
are the images of those of `β`, and its rational actions are the coefficientwise ones. -/
noncomputable instance Cauchy.divisionRing : DivisionRing (Cauchy abv) where
  __ := Cauchy.ring
  __ := Cauchy.instNonTrivial
  isUnit_of_ne_zero {x} := Quotient.inductionOn x fun f hf ↦
    ⟨mkUnit f (fun h ↦ hf (mk_eq_zero.mpr h)), rfl⟩
  nnratCastOfCharZero _ q :=
    haveI := CharZero.of_cauchy (abv := abv)
    ofRat q
  nnratCastOfCharZero_mul_den _ q := by
    have := CharZero.of_cauchy (abv := abv)
    rw [← ofRat_natCast, ← ofRat_natCast, ← ofRat_mul, NNRat.cast_mul_den]
  nnqsmulOfCharZero _ q x :=
    haveI := CharZero.of_cauchy (abv := abv)
    q • x
  nnqsmulOfCharZero_eq_mul _ q x := by
    have := CharZero.of_cauchy (abv := abv)
    exact smul_eq_ofRat_mul q (q : β) (NNRat.smul_def q) x
  ratCastOfCharZero _ q :=
    haveI := CharZero.of_cauchy (abv := abv)
    ofRat q
  ratCastOfCharZero_mul_den _ q := by
    have := CharZero.of_cauchy (abv := abv)
    rw [← ofRat_natCast, ← ofRat_intCast, ← ofRat_mul, Rat.cast_mul_den]
  qsmulOfCharZero _ q x :=
    haveI := CharZero.of_cauchy (abv := abv)
    q • x
  qsmulOfCharZero_eq_mul _ q x := by
    have := CharZero.of_cauchy (abv := abv)
    exact smul_eq_ofRat_mul q (q : β) (Rat.smul_def q) x

theorem ofRat_inv (x : β) {hx : IsUnit x} :
    ofRat x⁻¹ = Checked.inv (ofRat x : Cauchy abv) (hx.map (ofRatRingHom (abv := abv))) :=
  map_inv₀ (ofRatRingHom (abv := abv)) x

lemma ofRat_div (x y : β) {hy : IsUnit y} :
    ofRat (x / y) =
      Checked.div (ofRat x) (ofRat y : Cauchy abv) (hy.map (ofRatRingHom (abv := abv))) :=
  map_div₀ (ofRatRingHom (abv := abv)) x y

@[simp, norm_cast] lemma ofRat_nnratCast [CharZero β] (q : ℚ≥0) :
    ofRat (q : β) = (q : Cauchy abv) := rfl

@[simp, norm_cast] lemma ofRat_ratCast [CharZero β] (q : ℚ) :
    ofRat (q : β) = (q : Cauchy abv) := rfl

/-- Show the first 10 items of a representative of this equivalence class of Cauchy sequences.

The representative chosen is the one passed in the VM to `Quot.mk`, so two Cauchy sequences
converging to the same number may be printed differently.
-/
unsafe instance [Repr β] : Repr (Cauchy abv) where
  reprPrec r _ :=
    let N := 10
    let seq := r.unquot
    "(sorry /- " ++ Std.Format.joinSep ((List.range N).map <| repr ∘ seq) ", " ++ ", ... -/)"

end

section

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
variable {β : Type*} [Field β] {abv : β → α} [IsAbsoluteValue abv]

/-- The Cauchy completion forms a field. -/
noncomputable instance Cauchy.field : Field (Cauchy abv) :=
  { Cauchy.divisionRing, Cauchy.commRing with }

end

end CauSeq.Completion

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

namespace CauSeq

section

variable (β : Type*) [Ring β] (abv : β → α) [IsAbsoluteValue abv]

/-- A class stating that a ring with an absolute value is complete, i.e. every Cauchy
sequence has a limit. -/
class IsComplete : Prop where
  /-- Every Cauchy sequence has a limit. -/
  isComplete : ∀ s : CauSeq β abv, ∃ b : β, s ≈ const abv b

end

section

variable {β : Type*} [Ring β] {abv : β → α} [IsAbsoluteValue abv]
variable [IsComplete β abv]

theorem complete : ∀ s : CauSeq β abv, ∃ b : β, s ≈ const abv b :=
  IsComplete.isComplete

/-- The limit of a Cauchy sequence in a complete ring. Chosen non-computably. -/
noncomputable def lim (s : CauSeq β abv) : β :=
  Classical.choose (complete s)

theorem equiv_lim (s : CauSeq β abv) : s ≈ const abv (lim s) :=
  Classical.choose_spec (complete s)

theorem eq_lim_of_const_equiv {f : CauSeq β abv} {x : β} (h : CauSeq.const abv x ≈ f) : x = lim f :=
  const_equiv.mp <| Setoid.trans h <| equiv_lim f

theorem lim_eq_of_equiv_const {f : CauSeq β abv} {x : β} (h : f ≈ CauSeq.const abv x) : lim f = x :=
  (eq_lim_of_const_equiv <| Setoid.symm h).symm

theorem lim_eq_lim_of_equiv {f g : CauSeq β abv} (h : f ≈ g) : lim f = lim g :=
  lim_eq_of_equiv_const <| Setoid.trans h <| equiv_lim g

@[simp]
theorem lim_const (x : β) : lim (const abv x) = x :=
  lim_eq_of_equiv_const <| Setoid.refl _

theorem lim_add (f g : CauSeq β abv) : lim f + lim g = lim (f + g) :=
  eq_lim_of_const_equiv <|
    show LimZero (const abv (lim f + lim g) - (f + g)) by
      rw [const_add, add_sub_add_comm]
      exact add_limZero (Setoid.symm (equiv_lim f)) (Setoid.symm (equiv_lim g))

theorem lim_mul_lim (f g : CauSeq β abv) : lim f * lim g = lim (f * g) :=
  eq_lim_of_const_equiv <|
    show LimZero (const abv (lim f * lim g) - f * g) by
      have h :
        const abv (lim f * lim g) - f * g =
          (const abv (lim f) - f) * g + const abv (lim f) * (const abv (lim g) - g) := by
              apply Subtype.ext
              rw [coe_add]
              simp [sub_mul, mul_sub]
      rw [h]
      exact
        add_limZero (mul_limZero_left _ (Setoid.symm (equiv_lim _)))
          (mul_limZero_right _ (Setoid.symm (equiv_lim _)))

theorem lim_mul (f : CauSeq β abv) (x : β) : lim f * x = lim (f * const abv x) := by
  rw [← lim_mul_lim, lim_const]

theorem lim_neg (f : CauSeq β abv) : lim (-f) = -lim f :=
  lim_eq_of_equiv_const
    (show LimZero (-f - const abv (-lim f)) by
      rw [const_neg, sub_neg_eq_add, add_comm, ← sub_eq_add_neg]
      exact Setoid.symm (equiv_lim f))

theorem lim_sub (f g : CauSeq β abv) : lim f - lim g = lim (f - g) := by
  rw [sub_eq_add_neg, sub_eq_add_neg, ← lim_neg, lim_add f (-g)]

theorem lim_eq_zero_iff (f : CauSeq β abv) : lim f = 0 ↔ LimZero f :=
  ⟨fun h => by
    have hf := equiv_lim f
    rw [h] at hf
    exact (limZero_congr hf).mpr (const_limZero.mpr rfl),
   fun h => by
    have h₁ : f = f - const abv 0 := ext fun n => by simp
    rw [h₁] at h
    exact lim_eq_of_equiv_const h⟩

end

section

variable {β : Type*} [DivisionRing β] {abv : β → α} [IsAbsoluteValue abv] [IsComplete β abv]

theorem lim_inv {f : CauSeq β abv} (hf : ¬LimZero f) :
    lim (inv f hf) = Checked.inv (lim f) (Ne.isUnit (mt (lim_eq_zero_iff f).mp hf)) := by
  apply eq_inv_of_mul_eq_one_left₀
  rw [lim_mul_lim]
  exact (lim_eq_lim_of_equiv (CauSeq.inv_mul_cancel hf)).trans (lim_const 1)

end

section

variable [IsComplete α abs]

theorem lim_le {f : CauSeq α abs} {x : α} (h : f ≤ CauSeq.const abs x) : lim f ≤ x :=
  CauSeq.const_le.1 <| CauSeq.le_of_eq_of_le (Setoid.symm (equiv_lim f)) h

theorem le_lim {f : CauSeq α abs} {x : α} (h : CauSeq.const abs x ≤ f) : x ≤ lim f :=
  CauSeq.const_le.1 <| CauSeq.le_of_le_of_eq h (equiv_lim f)

theorem lt_lim {f : CauSeq α abs} {x : α} (h : CauSeq.const abs x < f) : x < lim f :=
  CauSeq.const_lt.1 <| CauSeq.lt_of_lt_of_eq h (equiv_lim f)

theorem lim_lt {f : CauSeq α abs} {x : α} (h : f < CauSeq.const abs x) : lim f < x :=
  CauSeq.const_lt.1 <| CauSeq.lt_of_eq_of_lt (Setoid.symm (equiv_lim f)) h

end

end CauSeq
