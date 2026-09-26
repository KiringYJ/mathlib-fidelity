/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Ring.Archimedean
public import Mathlib.Algebra.Ring.Subring.Order
public import Mathlib.Order.Quotient
public import Mathlib.RingTheory.Valuation.ValuationSubring

import Mathlib.Algebra.Order.Archimedean.Real.Hom

/-!
# Standard part function

The standard part maps finite elements of a linearly ordered field to real numbers through the
Archimedean residue field. When the field contains an explicitly embedded copy of the reals,
the standard part is the unique real number whose difference from the input is infinitesimal.

Let `K` be a linearly ordered field. The subset of finite elements (i.e. those bounded by a natural
number) is a `ValuationSubring`, which means we can construct its residue field
`FiniteResidueField`, roughly corresponding to the finite elements quotiented by infinitesimals.
This field inherits a `LinearOrder` instance, which makes it into an Archimedean linearly ordered
field, meaning we can uniquely embed it in the reals.

The ordered ring homomorphism `ArchimedeanClass.stdPart : FiniteElement K →+*o ℝ` uses this unique
embedding. Its input type excludes infinite elements, and its kernel consists of infinitesimals.
Use the ordinary homomorphism laws for arithmetic on finite elements. Inverses are available for
units of the ring of finite elements, via `map_units_inv`; finite elements need not form a field.
This construction generalizes the standard part on `Hyperreal`.

## References

* https://en.wikipedia.org/wiki/Standard_part_function
-/

@[expose] public noncomputable section

namespace ArchimedeanClass
variable
  {K : Type*} [LinearOrder K] [Field K] [IsOrderedRing K] {x y : K}
  {R : Type*} [LinearOrder R] [CommRing R] [IsStrictOrderedRing R] [Archimedean R]

/-! ### Finite residue field -/

variable (K) in
/-- The valuation subring of elements in non-negative Archimedean classes, i.e. elements bounded by
some natural number. -/
def FiniteElement : Type _ :=
  (addValuation K).toValuation.valuationSubring
deriving CommRing, IsDomain, ValuationRing, LinearOrder, IsStrictOrderedRing

namespace FiniteElement

@[simp] theorem val_zero : (0 : FiniteElement K).1 = 0 := rfl
@[simp] theorem val_one : (1 : FiniteElement K).1 = 1 := rfl
@[simp] theorem val_neg (x : FiniteElement K) : (-x).1 = -x.1 := rfl
@[simp] theorem val_add (x y : FiniteElement K) : (x + y).1 = x.1 + y.1 := rfl
@[simp] theorem val_sub (x y : FiniteElement K) : (x - y).1 = x.1 - y.1 := rfl
@[simp] theorem val_mul (x y : FiniteElement K) : (x * y).1 = x.1 * y.1 := rfl

@[ext] theorem ext {x y : FiniteElement K} (h : x.1 = y.1) : x = y := Subtype.ext h

/-- The constructor for `FiniteElement`. -/
protected def mk (x : K) (h : 0 ≤ mk x) : FiniteElement K := ⟨x, h⟩

@[simp] theorem mk_zero : FiniteElement.mk (0 : K) (by simp) = 0 := rfl
@[simp] theorem mk_one : FiniteElement.mk (1 : K) (by simp) = 1 := rfl
@[simp] theorem mk_natCast (n : ℕ) : FiniteElement.mk (n : K) (mk_natCast_nonneg n) = n := rfl
@[simp] theorem mk_intCast (n : ℤ) : FiniteElement.mk (n : K) (mk_intCast_nonneg n) = n := rfl

@[simp]
theorem neg_mk {x : K} (h : 0 ≤ mk x) :
    -FiniteElement.mk x h = FiniteElement.mk (-x) (by rwa [mk_neg]) :=
  rfl

@[simp]
theorem mk_add_mk (x y : K) (hx hy) :
    .mk x hx + .mk y hy = FiniteElement.mk (x + y) ((le_min hx hy).trans <| min_le_mk_add ..) :=
  rfl

@[simp]
theorem mk_sub_mk (x y : K) (hx hy) :
    .mk x hx - .mk y hy = FiniteElement.mk (x - y) ((le_min hx hy).trans <| min_le_mk_sub ..) :=
  rfl

@[simp]
theorem mk_mul_mk (x y : K) (hx hy) :
    .mk x hx * .mk y hy = FiniteElement.mk (x * y) (add_nonneg hx hy) :=
  rfl

@[simp]
theorem mk_le_mk (x y : K) (hx hy) : FiniteElement.mk x hx ≤ .mk y hy ↔ x ≤ y :=
  .rfl

@[simp]
theorem mk_lt_mk (x y : K) (hx hy) : FiniteElement.mk x hx < .mk y hy ↔ x < y :=
  .rfl

theorem not_isUnit_iff_mk_pos {x : FiniteElement K} : ¬ IsUnit x ↔ 0 < mk x.1 :=
  Valuation.Integer.not_isUnit_iff_valuation_lt_one

theorem isUnit_iff_mk_eq_zero {x : FiniteElement K} : IsUnit x ↔ mk x.1 = 0 := by
  rw [← not_iff_not, not_isUnit_iff_mk_pos, lt_iff_not_ge, x.2.ge_iff_eq']

instance : RatCast (FiniteElement K) where
  ratCast q := .mk q (mk_ratCast_nonneg q)

@[simp] theorem mk_ratCast (q : ℚ) : FiniteElement.mk (q : K) (mk_ratCast_nonneg q) = q := rfl

@[no_expose]
instance : FloorRing (FiniteElement K) :=
  .ofBounded _ fun x ↦ by
    obtain ⟨n, hn⟩ := x.2
    refine ⟨n, (le_abs_self x).trans ?_⟩
    simpa using! hn

/-- Lift an ordered ring homomorphism from an Archimedean ring to the finite elements of `K`. -/
def ofArchimedean (f : R →+*o K) : R →+*o FiniteElement K where
  toFun r := .mk (f r) (mk_map_nonneg_of_archimedean f r)
  map_zero' := Subtype.ext (map_zero f)
  map_one' := Subtype.ext (map_one f)
  map_add' x y := Subtype.ext (map_add f x y)
  map_mul' x y := Subtype.ext (map_mul f x y)
  monotone' _ _ h := f.monotone' h

@[simp]
theorem val_ofArchimedean (f : R →+*o K) (r : R) : (ofArchimedean f r).1 = f r := rfl

end FiniteElement

set_option backward.isDefEq.respectTransparency.types false in
variable (K) in
/-- The residue field of `FiniteElement`. This quotient inherits an order from `K`,
which makes it into a linearly ordered Archimedean field. -/
def FiniteResidueField : Type _ :=
  IsLocalRing.ResidueField (FiniteElement K)
deriving Field

namespace FiniteResidueField

set_option backward.isDefEq.respectTransparency.types false in
instance ordConnected_preimage_mk' : ∀ x, Set.OrdConnected <| Quotient.mk
    (Submodule.quotientRel (IsLocalRing.maximalIdeal (FiniteElement K))) ⁻¹' {x} := by
  refine fun x ↦ ⟨?_⟩
  rintro x rfl y hy z ⟨hxz, hzy⟩
  have := hxz.trans hzy
  rw [Set.mem_preimage, Set.mem_singleton_iff, Quotient.eq, Submodule.quotientRel_def,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, FiniteElement.not_isUnit_iff_mk_pos] at hy ⊢
  apply hy.trans_le (mk_antitoneOn _ _ _) <;> simpa

set_option backward.isDefEq.respectTransparency.types false in
instance : LinearOrder (FiniteResidueField K) :=
  haveI := Classical.decRel fun x y : FiniteElement K ↦
    letI := Submodule.quotientRel (IsLocalRing.maximalIdeal (FiniteElement K))
    x ≈ y
  inferInstanceAs <| LinearOrder (Quotient _)

set_option backward.isDefEq.respectTransparency.types false in
/-- The quotient map from finite elements on the field to the associated residue field. -/
def mk : FiniteElement K →+*o FiniteResidueField K where
  monotone' _ _ h := Quotient.mk_monotone h
  __ := IsLocalRing.residue (FiniteElement K)

@[induction_eliminator]
theorem ind {motive : FiniteResidueField K → Prop} (mk : ∀ x, motive (mk x)) : ∀ x, motive x :=
  Quotient.ind mk

instance ordConnected_preimage_mk :
    ∀ x, Set.OrdConnected (mk ⁻¹' ({x} : Set (FiniteResidueField K))) :=
  ordConnected_preimage_mk'

set_option backward.isDefEq.respectTransparency false in
theorem mk_eq_mk {x y : FiniteElement K} : mk x = mk y ↔ 0 < ArchimedeanClass.mk (x.1 - y.1) := by
  apply Quotient.eq.trans
  rw [Submodule.quotientRel_def, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    FiniteElement.not_isUnit_iff_mk_pos, AddSubgroupClass.coe_sub]

theorem mk_eq_zero {x : FiniteElement K} : mk x = 0 ↔ 0 < ArchimedeanClass.mk x.1 := by
  apply mk_eq_mk.trans
  simp

theorem mk_ne_zero {x : FiniteElement K} : mk x ≠ 0 ↔ ArchimedeanClass.mk x.1 = 0 := by
  rw [ne_eq, mk_eq_zero, not_lt, x.2.ge_iff_eq']

theorem mk_le_mk {x y : FiniteElement K} : mk x ≤ mk y ↔ x ≤ y ∨ mk x = mk y := by
  refine (Quotient.mk_le_mk (H := ordConnected_preimage_mk')).trans ?_
  rw [← Quotient.eq_iff_equiv]
  rfl

theorem mk_lt_mk {x y : FiniteElement K} : mk x < mk y ↔ x < y ∧ mk x ≠ mk y := by
  refine (Quotient.mk_lt_mk (H := ordConnected_preimage_mk')).trans ?_
  rw [← Quotient.eq_iff_equiv]
  rfl

theorem lt_of_mk_lt_mk {x y : FiniteElement K} (h : mk x < mk y) : x < y :=
  (mk_lt_mk.1 h).1

private theorem mul_le_mul_of_nonneg_left' {x y z : FiniteResidueField K} (h : x ≤ y) (hz : 0 ≤ z) :
    z * x ≤ z * y := by
  induction x with | mk x
  induction y with | mk y
  induction z with | mk z
  rw [← map_mul, ← map_mul]
  rw [← map_zero mk] at hz
  rw [mk_le_mk] at h hz ⊢
  grind [mul_le_mul_of_nonneg_left]

instance : IsOrderedRing (FiniteResidueField K) where
  zero_le_one := mk.monotone' zero_le_one
  add_le_add_left x y h z := by
    induction x with | mk x
    induction y with | mk y
    induction z with | mk z
    obtain h | h := mk_le_mk.1 h
    · exact mk.monotone' <| add_le_add_left h _
    · rw [h]
  mul_le_mul_of_nonneg_left _ hx _ _ h := mul_le_mul_of_nonneg_left' h hx
  mul_le_mul_of_nonneg_right x hx y z h := by
    simp_rw [mul_comm _ x]
    exact mul_le_mul_of_nonneg_left' h hx

instance : Archimedean (FiniteResidueField K) where
  arch x y hy := by
    induction x with | mk x
    induction y with | mk y
    obtain hx | hx := le_or_gt (mk x) 0
    · use 0
      rwa [zero_nsmul]
    · obtain ⟨n, hn⟩ := ((mk_ne_zero.1 hy.ne').trans (mk_ne_zero.1 hx.ne').symm).le
      refine ⟨n, mk.monotone' ?_⟩
      change x.1 ≤ n • y.1
      convert! ← hn
      · exact abs_of_pos <| lt_of_mk_lt_mk hx
      · exact abs_of_pos <| lt_of_mk_lt_mk hy

@[simp]
theorem mk_ratCast (q : ℚ) : mk (q : FiniteElement K) = q := by
  change mk (FiniteElement.mk ..) = _
  cases q with | div n d hd
  rw [← mul_left_inj' (c := ↑d) (mod_cast hd), ← map_natCast mk d, ← map_mul,
    ← FiniteElement.mk_natCast, FiniteElement.mk_mul_mk]
  simp_all

/-- An embedding from an Archimedean ring into `K` induces an embedding into
`FiniteResidueField K`. -/
def ofArchimedean (f : R →+*o K) : R →+*o FiniteResidueField K :=
  mk.comp (FiniteElement.ofArchimedean f)

theorem ofArchimedean_apply (f : R →+*o K) (r : R) :
    ofArchimedean f r = mk (FiniteElement.ofArchimedean f r) :=
  rfl

theorem ofArchimedean_injective (f : R →+*o K) : Function.Injective (ofArchimedean f) := by
  rw [injective_iff_map_eq_zero]
  intro r hr
  contrapose! hr
  rw [ofArchimedean_apply, mk_ne_zero]
  exact mk_map_of_archimedean' f hr

@[simp]
theorem ofArchimedean_inj (f : R →+*o K) {x y : R} :
    ofArchimedean f x = ofArchimedean f y ↔ x = y :=
  (ofArchimedean_injective f).eq_iff

end FiniteResidueField

/-! ### Standard part -/

/-- The standard part on finite elements, obtained from the residue field's unique ordered
embedding into `ℝ`. Its kernel is the ideal of infinitesimals. -/
@[no_expose]
def stdPart : FiniteElement K →+*o ℝ :=
  OrderRingHom.comp Classical.ofNonempty FiniteResidueField.mk

theorem stdPart_apply (f : FiniteResidueField K →+*o ℝ) (x : FiniteElement K) :
    stdPart x = f (FiniteResidueField.mk x) := by
  change (Classical.ofNonempty : FiniteResidueField K →+*o ℝ) (FiniteResidueField.mk x) = _
  congr 1
  exact Subsingleton.elim _ _

@[simp]
theorem stdPart_eq_zero {x : FiniteElement K} : stdPart x = 0 ↔ 0 < mk x.1 := by
  rw [stdPart_apply Classical.ofNonempty, map_eq_zero, FiniteResidueField.mk_eq_zero]

theorem stdPart_ne_zero {x : FiniteElement K} : stdPart x ≠ 0 ↔ mk x.1 = 0 := by
  rw [ne_eq, stdPart_eq_zero, not_lt, x.2.ge_iff_eq']

/-- A finite element has nonzero standard part exactly when it is a unit in the ring of finite
elements, so its inverse is finite as well. -/
theorem stdPart_ne_zero_iff_isUnit {x : FiniteElement K} : stdPart x ≠ 0 ↔ IsUnit x := by
  rw [stdPart_ne_zero, FiniteElement.isUnit_iff_mk_eq_zero]

theorem stdPart_add_eq_right {x y : FiniteElement K} (hx : 0 < mk x.1) :
    stdPart (x + y) = stdPart y := by
  rw [map_add, stdPart_eq_zero.2 hx, zero_add]

theorem stdPart_add_eq_left {x y : FiniteElement K} (hy : 0 < mk y.1) :
    stdPart (x + y) = stdPart x := by
  rw [add_comm, stdPart_add_eq_right hy]

theorem stdPart_sub_eq_right {x y : FiniteElement K} (hx : 0 < mk x.1) :
    stdPart (x - y) = -stdPart y := by
  rw [map_sub, stdPart_eq_zero.2 hx, zero_sub]

theorem stdPart_sub_eq_left {x y : FiniteElement K} (hy : 0 < mk y.1) :
    stdPart (x - y) = stdPart x := by
  rw [map_sub, stdPart_eq_zero.2 hy, sub_zero]

@[simp]
theorem stdPart_ratCast (q : ℚ) : stdPart (q : FiniteElement K) = q := by
  rw [stdPart_apply Classical.ofNonempty, FiniteResidueField.mk_ratCast, map_ratCast]

@[simp]
theorem stdPart_map_real (f : ℝ →+*o K) (r : ℝ) :
    stdPart (FiniteElement.ofArchimedean f r) = r := by
  change (Classical.ofNonempty : FiniteResidueField K →+*o ℝ)
    (FiniteResidueField.ofArchimedean f r) = r
  exact r.ringHom_apply <| OrderRingHom.comp _ (FiniteResidueField.ofArchimedean f)

@[simp]
theorem stdPart_real (x : FiniteElement ℝ) : stdPart x = x.1 := by
  have hx : FiniteElement.ofArchimedean (OrderRingHom.id ℝ) x.1 = x := Subtype.ext rfl
  simpa only [hx] using stdPart_map_real (OrderRingHom.id ℝ) x.1

theorem ofArchimedean_stdPart (f : ℝ →+*o K) (x : FiniteElement K) :
    FiniteResidueField.ofArchimedean f (stdPart x) = FiniteResidueField.mk x := by
  rw [stdPart_apply Classical.ofNonempty, ← OrderRingHom.comp_apply, OrderRingHom.apply_eq_self]

/-- The standard part of `x` is the unique real `r` such that `x - f r` is infinitesimal. -/
theorem mk_sub_pos_iff (f : ℝ →+*o K) {x : FiniteElement K} {r : ℝ} :
    0 < mk (x.1 - f r) ↔ stdPart x = r := by
  refine (FiniteResidueField.mk_eq_zero
    (x := x - FiniteElement.ofArchimedean f r)).symm.trans ?_
  rw [map_sub, ← FiniteResidueField.ofArchimedean_apply, ← ofArchimedean_stdPart f x,
    sub_eq_zero, FiniteResidueField.ofArchimedean_inj f]

theorem mk_sub_stdPart_pos (f : ℝ →+*o K) (x : FiniteElement K) :
    0 < mk (x.1 - f (stdPart x)) :=
  (mk_sub_pos_iff f).2 rfl

theorem lt_of_lt_stdPart (f : ℝ →+*o K) {x : FiniteElement K} {r : ℝ}
    (h : r < stdPart x) : f r < x.1 := by
  rw [← sub_lt_sub_iff_right (c := f (stdPart x)), ← map_sub]
  apply lt_of_mk_lt_mk_of_nonpos
  · rw [mk_map_of_archimedean', mk_sub_pos_iff f]
    rw [ne_eq, sub_eq_zero]
    exact h.ne
  · simpa using f.monotone' h.le

theorem lt_of_stdPart_lt (f : ℝ →+*o K) {x : FiniteElement K} {r : ℝ}
    (h : stdPart x < r) : x.1 < f r := by
  have h' : -r < stdPart (-x) := by simpa using neg_lt_neg h
  simpa using lt_of_lt_stdPart (x := -x) f h'

theorem stdPart_le_of_le (f : ℝ →+*o K) {x : FiniteElement K} {r : ℝ}
    (h : x.1 ≤ f r) : stdPart x ≤ r :=
  le_imp_le_iff_lt_imp_lt.2 (lt_of_lt_stdPart f) h

theorem le_stdPart_of_le (f : ℝ →+*o K) {x : FiniteElement K} {r : ℝ}
    (h : f r ≤ x.1) : r ≤ stdPart x :=
  le_imp_le_iff_lt_imp_lt.2 (lt_of_stdPart_lt f) h

theorem stdPart_eq (f : ℝ →+*o K) {x : FiniteElement K} {r : ℝ}
    (hl : ∀ s < r, f s ≤ x.1) (hr : ∀ s > r, x.1 ≤ f s) : stdPart x = r := by
  obtain h | rfl | h := lt_trichotomy (stdPart x) r
  · obtain ⟨s, hs, hs'⟩ := exists_between h
    cases (le_stdPart_of_le f (hl _ hs')).not_gt hs
  · rfl
  · obtain ⟨s, hs, hs'⟩ := exists_between h
    cases (stdPart_le_of_le f (hr _ hs)).not_gt hs'

/-- The standard part is the greatest lower bound of the strict upper real cut. -/
theorem isGLB_stdPart (f : ℝ →+*o K) (x : FiniteElement K) :
    IsGLB {r : ℝ | x.1 < f r} (stdPart x) := by
  constructor
  · intro r hr
    exact stdPart_le_of_le f hr.le
  · intro a ha
    by_contra! h
    obtain ⟨r, hr, hra⟩ := exists_between h
    exact (ha (lt_of_stdPart_lt f hr)).not_gt hra

/-- The standard part is the least upper bound of the strict lower real cut. -/
theorem isLUB_stdPart (f : ℝ →+*o K) (x : FiniteElement K) :
    IsLUB {r : ℝ | f r < x.1} (stdPart x) := by
  constructor
  · intro r hr
    exact le_stdPart_of_le f hr.le
  · intro a ha
    by_contra! h
    obtain ⟨r, har, hr⟩ := exists_between h
    exact (ha (lt_of_lt_stdPart f hr)).not_gt har

theorem stdPart_eq_sInf (f : ℝ →+*o K) (x : FiniteElement K) :
    stdPart x = sInf {r : ℝ | x.1 < f r} :=
  ((isGLB_stdPart f x).csInf_eq ⟨stdPart x + 1, lt_of_stdPart_lt f (lt_add_one _)⟩).symm

theorem stdPart_eq_sSup (f : ℝ →+*o K) (x : FiniteElement K) :
    stdPart x = sSup {r : ℝ | f r < x.1} :=
  ((isLUB_stdPart f x).csSup_eq ⟨stdPart x - 1, lt_of_lt_stdPart f (sub_one_lt _)⟩).symm

end ArchimedeanClass
