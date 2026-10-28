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

A subfield is implemented as a subring closed under inversion of its invertible elements,
that is of its nonzero elements.

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
  /-- A subfield contains the inverse of each of its invertible elements. -/
  inv_mem : ∀ {s : S} {x : K} {hx : IsUnit x}, x ∈ s → x⁻¹ ∈ s

attribute [aesop 90% (rule_sets := [SetLike])] SubfieldClass.inv_mem

namespace SubfieldClass

variable {S : Type*} [SetLike S K] [SubfieldClass S K]

/-- A subfield is closed under division by its invertible elements. -/
@[aesop 90% (rule_sets := [SetLike])]
theorem div_mem {s : S} {x y : K} {hyUnit : IsUnit y} (hx : x ∈ s) (hy : y ∈ s) : x / y ∈ s := by
  rw [div_eq_mul_inv₀ x y]
  exact mul_mem hx (inv_mem hy)

/-- A subfield is closed under integer powers. A negative power requires an invertible base. -/
@[aesop 90% (rule_sets := [SetLike])]
theorem zpow_mem {s : S} {x : K} (hx : x ∈ s) (n : ℤ) {h : n < 0 → IsUnit x} : x ^ n ∈ s := by
  cases n with
  | ofNat n => simpa using pow_mem hx n
  | negSucc n =>
    rw [zpow_negSucc₀ x n]
    exact inv_mem (pow_mem hx (n + 1))

/-- Checked rational evaluation lies in every subfield. -/
theorem rat_eval_mem (s : S) (q : ℚ) (hd : (q.den : K) ≠ 0) : Rat.eval q hd ∈ s :=
  div_mem (hyUnit := hd.isUnit) (intCast_mem s q.num) (natCast_mem s q.den)

/-- Checked nonnegative rational evaluation lies in every subfield. -/
theorem nnrat_eval_mem (s : S) (q : ℚ≥0) (hd : (q.den : K) ≠ 0) : NNRat.eval q hd ∈ s :=
  div_mem (hyUnit := hd.isUnit) (natCast_mem s q.num) (natCast_mem s q.den)

/-- In characteristic zero, the embedding of a rational lies in every subfield. -/
@[simp, aesop safe (rule_sets := [SetLike])]
theorem ratCast_mem [CharZero K] (s : S) (q : ℚ) : (q : K) ∈ s := by
  rw [Rat.cast_eq_eval q (Nat.cast_ne_zero.mpr q.den_nz)]
  exact rat_eval_mem s q _

/-- In characteristic zero, the embedding of a nonnegative rational lies in every subfield. -/
@[simp, aesop safe (rule_sets := [SetLike])]
theorem nnratCast_mem [CharZero K] (s : S) (q : ℚ≥0) : (q : K) ∈ s := by
  rw [NNRat.cast_eq_eval q (Nat.cast_ne_zero.mpr q.den_ne_zero)]
  exact nnrat_eval_mem s q _

/-- A division ring has characteristic zero if one of its subfields has. -/
theorem charZero_of_subtype (s : S) [CharZero s] : CharZero K :=
  CharZero.of_injective_map_natCast (Subtype.val : s → K) Subtype.val_injective fun _ => rfl

/-- A subfield inherits the property that each nonzero element is a unit. In characteristic
zero, its rational embeddings and the actions of `ℚ≥0` and `ℚ` are those of the ambient division
ring. -/
instance (priority := 75) toDivisionRing (s : S) : DivisionRing s where
  toRing := SubringClass.toRing s
  exists_pair_ne := ⟨0, 1, fun h => zero_ne_one (congrArg Subtype.val h)⟩
  isUnit_of_ne_zero {a} ha := by
    have ha' : (a : K) ≠ 0 := fun h => ha (Subtype.ext h)
    exact ⟨⟨a, ⟨(a : K)⁻¹, inv_mem a.property⟩,
      Subtype.ext mul_inv_cancel₀, Subtype.ext inv_mul_cancel₀⟩, rfl⟩
  nnratCastOfCharZero h q :=
    haveI := charZero_of_subtype s
    ⟨q, nnratCast_mem s q⟩
  nnratCastOfCharZero_mul_den h q :=
    haveI := charZero_of_subtype s
    Subtype.ext (NNRat.cast_mul_den q)
  ratCastOfCharZero h q :=
    haveI := charZero_of_subtype s
    ⟨q, ratCast_mem s q⟩
  ratCastOfCharZero_mul_den h q :=
    haveI := charZero_of_subtype s
    Subtype.ext (Rat.cast_mul_den q)
  nnqsmulOfCharZero h q a :=
    haveI := charZero_of_subtype s
    ⟨q • (a : K), by
      rw [show q • (a : K) = (q : K) * a from DivisionSemiring.nnqsmulOfCharZero_eq_mul _ q _]
      exact mul_mem (nnratCast_mem s q) a.2⟩
  nnqsmulOfCharZero_eq_mul h q a :=
    haveI := charZero_of_subtype s
    Subtype.ext (DivisionSemiring.nnqsmulOfCharZero_eq_mul _ q (a : K))
  qsmulOfCharZero h q a :=
    haveI := charZero_of_subtype s
    ⟨q • (a : K), by
      rw [show q • (a : K) = (q : K) * a from DivisionRing.qsmulOfCharZero_eq_mul _ q _]
      exact mul_mem (ratCast_mem s q) a.2⟩
  qsmulOfCharZero_eq_mul h q a :=
    haveI := charZero_of_subtype s
    Subtype.ext (DivisionRing.qsmulOfCharZero_eq_mul _ q (a : K))

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
  /-- A subfield is closed under multiplicative inverses of its invertible elements. -/
  inv_mem' : ∀ {x : K} {hx : IsUnit x}, x ∈ carrier → x⁻¹ ∈ carrier

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
  inv_mem {s} := s.inv_mem'

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

/-- A `Subring` containing inverses of its invertible elements is a `Subfield`. -/
def Subring.toSubfield (s : Subring K)
    (hinv : ∀ {x : K} {hx : IsUnit x}, x ∈ s → x⁻¹ ∈ s) : Subfield K :=
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
protected theorem inv_mem {x : K} {hx : IsUnit x} : x ∈ s → x⁻¹ ∈ s :=
  SubfieldClass.inv_mem

/-- A subfield is closed under division. -/
protected theorem div_mem {x y : K} {hyUnit : IsUnit y} : x ∈ s → y ∈ s → x / y ∈ s :=
  SubfieldClass.div_mem

protected theorem pow_mem {x : K} (hx : x ∈ s) (n : ℕ) : x ^ n ∈ s :=
  pow_mem hx n

protected theorem zsmul_mem {x : K} (hx : x ∈ s) (n : ℤ) : n • x ∈ s :=
  zsmul_mem hx n

protected theorem intCast_mem (n : ℤ) : (n : K) ∈ s := intCast_mem s n

protected theorem zpow_mem {x : K} (hx : x ∈ s) (n : ℤ) {h : n < 0 → IsUnit x} : x ^ n ∈ s :=
  SubfieldClass.zpow_mem hx n

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
theorem coe_div (x y : s) {hy : IsUnit y} : (↑(x / y) : K) = ↑x / ↑y :=
  map_div₀ (SubringClass.subtype s) x y

@[simp, norm_cast]
theorem coe_inv (x : s) {hx : IsUnit x} : (↑x⁻¹ : K) = (↑x)⁻¹ :=
  map_inv₀ (SubringClass.subtype s) x

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
