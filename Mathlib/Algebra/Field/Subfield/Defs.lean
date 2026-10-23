/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Data.Rat.Cast.Defs

/-!
# Subfields

Let `K` be a division ring, for example a field.
This file defines the "bundled" subfield type `Subfield K`, a type
whose terms correspond to subfields of `K`. Note we do not require the "subfields" to be
commutative, so they are really sub-division rings / skew fields. This is the preferred way to talk
about subfields in mathlib. Unbundled subfields (`s : Set K` and `IsSubfield s`)
are not in this file, and they will ultimately be deprecated.

We prove that subfields are a complete lattice, and that you can `map` (pushforward) and
`comap` (pull back) them along ring homomorphisms.

We define the `closure` construction from `Set K` to `Subfield K`, sending a subset of `K`
to the subfield it generates, and prove that it is a Galois insertion.

## Main definitions

Notation used here:

`(K : Type u) [DivisionRing K] (L : Type u) [DivisionRing L] (f g : K →+* L)`
`(A : Subfield K) (B : Subfield L) (s : Set K)`

* `Subfield K` : the type of subfields of a division ring `K`.

## Implementation notes

A subfield is implemented as a subring closed under inversion of ambient units.

Lattice inclusion (e.g. `≤` and `⊓`) is used rather than set notation (`⊆` and `∩`), although
`∈` is defined as membership of a subfield's underlying set.

## Tags
subfield, subfields
-/

@[expose] public section


universe u v w

variable {K : Type u}
variable [DivisionRing K]

/-- `SubfieldClass S K` states `S` is a type of subsets `s ⊆ K` closed under field operations. -/
class SubfieldClass (S K : Type*) [DivisionRing K] [SetLike S K] : Prop
    extends SubringClass S K where
  /-- The inverse of an ambient unit belonging to the subfield also belongs to it. -/
  unit_inv_mem : ∀ {s : S} {u : Kˣ}, (u : K) ∈ s → (↑u⁻¹ : K) ∈ s

namespace SubfieldClass

variable (S : Type*) [SetLike S K] [h : SubfieldClass S K]

variable {S}

/-- A subfield is closed under inversion of units. -/
theorem inv_mem {s : S} {u : Kˣ} (hu : (u : K) ∈ s) : (↑u⁻¹ : K) ∈ s :=
  SubfieldClass.unit_inv_mem hu

/-- Mixed division stays in a subfield when the numerator and unit denominator belong to it. -/
theorem divp_mem {s : S} {x : K} {u : Kˣ} (hx : x ∈ s) (hu : (u : K) ∈ s) : x /ₚ u ∈ s :=
  mul_mem hx (inv_mem hu)

/-- Checked rational evaluation lies in every subfield. -/
theorem rat_eval_mem (s : S) (q : ℚ) (hd : (q.den : K) ≠ 0) : Rat.eval q hd ∈ s :=
  divp_mem (intCast_mem s q.num) (natCast_mem s q.den)

/-- Checked nonnegative rational evaluation lies in every subfield. -/
theorem nnrat_eval_mem (s : S) (q : ℚ≥0) (hd : (q.den : K) ≠ 0) : NNRat.eval q hd ∈ s :=
  divp_mem (natCast_mem s q.num) (natCast_mem s q.den)

/-- Integer powers of units belonging to a subfield belong to it. -/
theorem zpow_mem {s : S} {u : Kˣ} (hu : (u : K) ∈ s) (n : ℤ) : (↑(u ^ n) : K) ∈ s := by
  cases n with
  | ofNat n => simpa using pow_mem hu n
  | negSucc n => simpa [zpow_negSucc] using pow_mem (inv_mem hu) (n + 1)

/-- A subfield inherits the property that each nonzero element is a unit. -/
instance (priority := 75) toDivisionRing (s : S) : DivisionRing s where
  toRing := SubringClass.toRing s
  exists_pair_ne := ⟨0, 1, fun h => zero_ne_one (congrArg Subtype.val h)⟩
  isUnit_of_ne_zero {a} ha := by
    have ha' : (a : K) ≠ 0 := fun h => ha (Subtype.ext h)
    let u := Units.mk0 (a : K) ha'
    let b : s := ⟨↑u⁻¹, inv_mem (u := u) a.property⟩
    exact ⟨⟨a, b, Subtype.ext u.mul_inv, Subtype.ext u.inv_mul⟩, rfl⟩

/-- A subfield of a commutative field inherits its field structure. -/
instance (priority := 75) toField {K} [Field K] [SetLike S K] [SubfieldClass S K] (s : S) :
    Field s where
  toCommRing := SubringClass.toCommRing s
  __ := SubfieldClass.toDivisionRing s

end SubfieldClass

/-- `Subfield R` is the type of subfields of `R`. A subfield of `R` is a subset `s` that is a
  multiplicative submonoid and an additive subgroup. Note in particular that it shares the
  same 0 and 1 as R. -/
@[stacks 09FD "second part"]
structure Subfield (K : Type u) [DivisionRing K] extends Subring K where
  /-- A subfield is closed under multiplicative inverses. -/
  inv_mem' : ∀ u : Kˣ, (u : K) ∈ carrier → (↑u⁻¹ : K) ∈ carrier

/-- Reinterpret a `Subfield` as a `Subring`. -/
add_decl_doc Subfield.toSubring

namespace Subfield

/-- The underlying `AddSubgroup` of a subfield. -/
@[reducible]
def toAddSubgroup (s : Subfield K) : AddSubgroup K :=
  { s.toSubring.toAddSubgroup with }

instance : SetLike (Subfield K) K where
  coe s := s.carrier
  coe_injective p q h := by cases p; cases q; congr; exact SetLike.ext' h

instance : PartialOrder (Subfield K) := .ofSetLike (Subfield K) K

instance : SubfieldClass (Subfield K) K where
  add_mem {s} := s.add_mem'
  zero_mem s := s.zero_mem'
  neg_mem {s} := s.neg_mem'
  mul_mem {s} := s.mul_mem'
  one_mem s := s.one_mem'
  unit_inv_mem {s} := s.inv_mem' _

theorem mem_carrier {s : Subfield K} {x : K} : x ∈ s.carrier ↔ x ∈ s :=
  Iff.rfl

@[simp]
theorem mem_mk {S : Subring K} {x : K} (h) : x ∈ (⟨S, h⟩ : Subfield K) ↔ x ∈ S :=
  Iff.rfl

@[simp]
theorem coe_set_mk (S : Subring K) (h) : ((⟨S, h⟩ : Subfield K) : Set K) = S :=
  rfl

@[simp]
theorem mk_le_mk {S S' : Subring K} (h h') : (⟨S, h⟩ : Subfield K) ≤ (⟨S', h'⟩ : Subfield K) ↔
    S ≤ S' :=
  Iff.rfl

/-- Two subfields are equal if they have the same elements. -/
@[ext]
theorem ext {S T : Subfield K} (h : ∀ x, x ∈ S ↔ x ∈ T) : S = T :=
  SetLike.ext h

/-- Copy of a subfield with a new `carrier` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (S : Subfield K) (s : Set K) (hs : s = ↑S) : Subfield K :=
  { S.toSubring.copy s hs with
    carrier := s
    inv_mem' := hs.symm ▸ S.inv_mem' }

@[simp, norm_cast]
theorem coe_copy (S : Subfield K) (s : Set K) (hs : s = ↑S) : (S.copy s hs : Set K) = s :=
  rfl

theorem copy_eq (S : Subfield K) (s : Set K) (hs : s = ↑S) : S.copy s hs = S :=
  SetLike.coe_injective hs

@[simp]
theorem coe_toSubring (s : Subfield K) : (s.toSubring : Set K) = s :=
  rfl

@[simp]
theorem mem_toSubring (s : Subfield K) (x : K) : x ∈ s.toSubring ↔ x ∈ s :=
  Iff.rfl

end Subfield

/-- A `Subring` containing inverses is a `Subfield`. -/
def Subring.toSubfield (s : Subring K)
    (hinv : ∀ u : Kˣ, (u : K) ∈ s → (↑u⁻¹ : K) ∈ s) : Subfield K :=
  { s with inv_mem' := hinv }

namespace Subfield

variable (s : Subfield K)

section DerivedFromSubfieldClass

/-- A subfield contains the field's 1. -/
protected theorem one_mem : (1 : K) ∈ s :=
  one_mem s

/-- A subfield contains the field's 0. -/
protected theorem zero_mem : (0 : K) ∈ s :=
  zero_mem s

/-- A subfield is closed under multiplication. -/
protected theorem mul_mem {x y : K} : x ∈ s → y ∈ s → x * y ∈ s :=
  mul_mem

/-- A subfield is closed under addition. -/
protected theorem add_mem {x y : K} : x ∈ s → y ∈ s → x + y ∈ s :=
  add_mem

/-- A subfield is closed under negation. -/
protected theorem neg_mem {x : K} : x ∈ s → -x ∈ s :=
  neg_mem

/-- A subfield is closed under subtraction. -/
protected theorem sub_mem {x y : K} : x ∈ s → y ∈ s → x - y ∈ s :=
  sub_mem

/-- A subfield is closed under inverses. -/
protected theorem inv_mem {u : Kˣ} : (u : K) ∈ s → (↑u⁻¹ : K) ∈ s :=
  SubfieldClass.inv_mem

/-- A subfield is closed under division. -/
protected theorem divp_mem {x : K} {u : Kˣ} : x ∈ s → (u : K) ∈ s → x /ₚ u ∈ s :=
  SubfieldClass.divp_mem

protected theorem pow_mem {x : K} (hx : x ∈ s) (n : ℕ) : x ^ n ∈ s :=
  pow_mem hx n

protected theorem zsmul_mem {x : K} (hx : x ∈ s) (n : ℤ) : n • x ∈ s :=
  zsmul_mem hx n

protected theorem intCast_mem (n : ℤ) : (n : K) ∈ s := intCast_mem s n

protected theorem zpow_mem {u : Kˣ} (hu : (u : K) ∈ s) (n : ℤ) : (↑(u ^ n) : K) ∈ s :=
  SubfieldClass.zpow_mem hu n

instance : Ring s :=
  s.toSubring.toRing

instance toDivisionRing (s : Subfield K) : DivisionRing s := SubfieldClass.toDivisionRing s

instance toField {K} [Field K] (s : Subfield K) : Field s := SubfieldClass.toField s

@[simp, norm_cast]
theorem coe_add (x y : s) : (↑(x + y) : K) = ↑x + ↑y :=
  rfl

@[simp, norm_cast]
theorem coe_sub (x y : s) : (↑(x - y) : K) = ↑x - ↑y :=
  rfl

@[simp, norm_cast]
theorem coe_neg (x : s) : (↑(-x) : K) = -↑x :=
  rfl

@[simp, norm_cast]
theorem coe_mul (x y : s) : (↑(x * y) : K) = ↑x * ↑y :=
  rfl

@[simp, norm_cast]
theorem coe_zero : ((0 : s) : K) = 0 :=
  rfl

@[simp, norm_cast]
theorem coe_one : ((1 : s) : K) = 1 :=
  rfl

end DerivedFromSubfieldClass

/-- The embedding from a subfield of the field `K` to `K`. -/
def subtype (s : Subfield K) : s →+* K :=
  { s.toSubmonoid.subtype, s.toAddSubgroup.subtype with toFun := (↑) }

@[simp]
lemma subtype_apply {s : Subfield K} (x : s) :
    s.subtype x = x := rfl

lemma subtype_injective (s : Subfield K) :
    Function.Injective s.subtype :=
  Subtype.coe_injective

@[simp]
theorem coe_subtype : ⇑(s.subtype) = ((↑) : s → K) :=
  rfl

variable (K) in
theorem toSubring_subtype_eq_subtype (S : Subfield K) :
    S.toSubring.subtype = S.subtype :=
  rfl

/-! ### Partial order -/


theorem mem_toSubmonoid {s : Subfield K} {x : K} : x ∈ s.toSubmonoid ↔ x ∈ s :=
  Iff.rfl

@[simp]
theorem coe_toSubmonoid : (s.toSubmonoid : Set K) = s :=
  rfl

theorem mem_toAddSubgroup {s : Subfield K} {x : K} : x ∈ s.toAddSubgroup ↔ x ∈ s :=
  Iff.rfl

@[simp]
theorem coe_toAddSubgroup : (s.toAddSubgroup : Set K) = s :=
  rfl

end Subfield
