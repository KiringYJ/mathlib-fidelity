/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.FieldTheory.RatFunc.Defs
public import Mathlib.RingTheory.Algebraic.Integral

/-!
# The field structure of rational functions

## Main definitions
Working with rational functions as polynomials:
- `RatFunc.instField` provides a field structure

You can use `IsFractionRing` API to treat `RatFunc` as the field of fractions of polynomials:
* `algebraMap K[X] (RatFunc K)` maps polynomials to rational functions
* `IsFractionRing.algEquiv` maps other fields of fractions of `K[X]` to `RatFunc K`.

In particular:
* `FractionRing.algEquiv K[X] (RatFunc K)` maps the generic field of
  fraction construction to `RatFunc K`. Combine this with `AlgEquiv.restrictScalars` to change
  the `FractionRing K[X] ≃ₐ[K[X]] RatFunc K` to `FractionRing K[X] ≃ₐ[K] RatFunc K`.

Working with rational functions as fractions:
- `RatFunc.num` and `RatFunc.denom` give the numerator and denominator.
  These values are chosen to be coprime and such that `RatFunc.denom` is monic.

Lifting homomorphisms of polynomials to other types, by mapping and dividing, as long
as the homomorphism retains the non-zero-divisor property:
- `RatFunc.liftMonoidWithZeroHom` lifts a `K[X] →*₀ G₀` to
  a `RatFunc K →*₀ G₀`, where `[CommRing K] [CommGroupWithZero G₀]`
- `RatFunc.liftRingHom` lifts a `K[X] →+* L` to a `RatFunc K →+* L`,
  where `[CommRing K] [Field L]`
- `RatFunc.liftAlgHom` lifts a `K[X] →ₐ[S] L` to a `RatFunc K →ₐ[S] L`,
  where `[CommRing K] [Field L] [CommSemiring S] [Algebra S K[X]] [Algebra S L]`

This is satisfied by injective homs.

We also have lifting homomorphisms of polynomials to other polynomials,
with the same condition on retaining the non-zero-divisor property across the map:
- `RatFunc.map` lifts `K[X] →* R[X]` when `[CommRing K] [CommRing R]`
- `RatFunc.mapRingHom` lifts `K[X] →+* R[X]` when `[CommRing K] [CommRing R]`
- `RatFunc.mapAlgHom` lifts `K[X] →ₐ[S] R[X]` when
  `[CommRing K] [IsDomain K] [CommRing R] [IsDomain R]`
-/

@[expose] public section

universe u v

noncomputable section

open scoped nonZeroDivisors Polynomial

variable {K : Type u}

namespace RatFunc

section Field

variable [CommRing K]

/-- The zero rational function. -/
protected irreducible_def zero : RatFunc K :=
  ⟨0⟩

instance : Zero (RatFunc K) :=
  ⟨RatFunc.zero⟩

theorem ofFractionRing_zero : (ofFractionRing 0 : RatFunc K) = 0 :=
  zero_def.symm

/-- Addition of rational functions. -/
protected irreducible_def add : RatFunc K → RatFunc K → RatFunc K
  | ⟨p⟩, ⟨q⟩ => ⟨p + q⟩

instance : Add (RatFunc K) :=
  ⟨RatFunc.add⟩

theorem ofFractionRing_add (p q : FractionRing K[X]) :
    ofFractionRing (p + q) = ofFractionRing p + ofFractionRing q :=
  (add_def _ _).symm

/-- Subtraction of rational functions. -/
protected irreducible_def sub : RatFunc K → RatFunc K → RatFunc K
  | ⟨p⟩, ⟨q⟩ => ⟨p - q⟩

instance : Sub (RatFunc K) :=
  ⟨RatFunc.sub⟩

theorem ofFractionRing_sub (p q : FractionRing K[X]) :
    ofFractionRing (p - q) = ofFractionRing p - ofFractionRing q :=
  (sub_def _ _).symm

/-- Additive inverse of a rational function. -/
protected irreducible_def neg : RatFunc K → RatFunc K
  | ⟨p⟩ => ⟨-p⟩

instance : Neg (RatFunc K) :=
  ⟨RatFunc.neg⟩

theorem ofFractionRing_neg (p : FractionRing K[X]) :
    ofFractionRing (-p) = -ofFractionRing p :=
  (neg_def _).symm

/-- The multiplicative unit of rational functions. -/
protected irreducible_def one : RatFunc K :=
  ⟨1⟩

instance : One (RatFunc K) :=
  ⟨RatFunc.one⟩

theorem ofFractionRing_one : (ofFractionRing 1 : RatFunc K) = 1 :=
  one_def.symm

/-- Multiplication of rational functions. -/
protected irreducible_def mul : RatFunc K → RatFunc K → RatFunc K
  | ⟨p⟩, ⟨q⟩ => ⟨p * q⟩

instance : Mul (RatFunc K) :=
  ⟨RatFunc.mul⟩

theorem ofFractionRing_mul (p q : FractionRing K[X]) :
    ofFractionRing (p * q) = ofFractionRing p * ofFractionRing q :=
  (mul_def _ _).symm

section SMul

variable {R : Type*}

/-- Scalar multiplication of rational functions. -/
protected irreducible_def smul [SMul R (FractionRing K[X])] : R → RatFunc K → RatFunc K
  | r, ⟨p⟩ => ⟨r • p⟩

instance [SMul R (FractionRing K[X])] : SMul R (RatFunc K) :=
  ⟨RatFunc.smul⟩

theorem ofFractionRing_smul [SMul R (FractionRing K[X])] (c : R) (p : FractionRing K[X]) :
    ofFractionRing (c • p) = c • ofFractionRing p :=
  (smul_def _ _).symm

theorem toFractionRing_smul [SMul R (FractionRing K[X])] (c : R) (p : RatFunc K) :
    toFractionRing (c • p) = c • toFractionRing p := by
  cases p
  rw [← ofFractionRing_smul]

theorem smul_eq_C_smul (x : RatFunc K) (r : K) : r • x = Polynomial.C r • x := by
  obtain ⟨x⟩ := x
  induction x using Localization.induction_on
  rw [← ofFractionRing_smul, ← ofFractionRing_smul, Localization.smul_mk,
    Localization.smul_mk, smul_eq_mul, Polynomial.smul_eq_C_mul]

section IsDomain

variable [IsDomain K]
variable [Monoid R] [DistribMulAction R K[X]]
variable [IsScalarTower R K[X] K[X]]

theorem mk_smul (c : R) (p q : K[X]) {hq : q ≠ 0} :
    RatFunc.mk (c • p) q = c • RatFunc.mk p q := by
  rw [mk_eq_localization_mk, mk_eq_localization_mk, ← Localization.smul_mk, ← ofFractionRing_smul]

instance : IsScalarTower R K[X] (RatFunc K) :=
  ⟨fun c p q => q.induction_on' fun q r _ => by rw [← mk_smul, smul_assoc, mk_smul, mk_smul]⟩

end IsDomain

end SMul

variable (K)

instance [Subsingleton K] : Subsingleton (RatFunc K) :=
  toFractionRing_injective.subsingleton

instance : Inhabited (RatFunc K) :=
  ⟨0⟩

instance instNontrivial [Nontrivial K] : Nontrivial (RatFunc K) :=
  ofFractionRing_injective.nontrivial

/-- `RatFunc K` is isomorphic to the field of fractions of `K[X]`, as rings.

This is an auxiliary definition; `simp`-normal form is `IsLocalization.algEquiv`.
-/
@[simps apply]
def toFractionRingRingEquiv : RatFunc K ≃+* FractionRing K[X] where
  toFun := toFractionRing
  invFun := ofFractionRing
  map_add' := fun ⟨_⟩ ⟨_⟩ => by simp [← ofFractionRing_add]
  map_mul' := fun ⟨_⟩ ⟨_⟩ => by simp [← ofFractionRing_mul]

end Field

section TacticInterlude

/-- Solve equations for `RatFunc K` by working in `FractionRing K[X]`. -/
macro "frac_tac" : tactic => `(tactic|
  · repeat (rintro (⟨⟩ : RatFunc _))
    try simp only [← ofFractionRing_zero, ← ofFractionRing_add, ← ofFractionRing_sub,
      ← ofFractionRing_neg, ← ofFractionRing_one, ← ofFractionRing_mul,
      add_assoc, zero_add, add_zero, mul_assoc, mul_zero, mul_one, mul_add,
      add_comm, add_left_comm, mul_comm, mul_left_comm, sub_eq_add_neg,
      add_mul, zero_mul, one_mul, neg_mul, mul_neg, add_neg_cancel])

/-- Solve equations for `RatFunc K` by applying `RatFunc.induction_on`. -/
macro "smul_tac" : tactic => `(tactic|
    repeat
      (first
        | rintro (⟨⟩ : RatFunc _)
        | intro) <;>
    simp_rw [← ofFractionRing_smul] <;>
    simp only [add_comm, mul_comm, zero_smul, succ_nsmul, zsmul_eq_mul, mul_add, mul_one, mul_zero,
      neg_add, mul_neg,
      Int.cast_zero, Int.cast_add, Int.cast_one,
      Int.cast_negSucc, Int.cast_natCast, Nat.cast_succ,
      Localization.mk_zero, Localization.add_mk_self, Localization.neg_mk,
      ofFractionRing_zero, ← ofFractionRing_add, ← ofFractionRing_neg])

end TacticInterlude

section CommRing

variable (K) [CommRing K]
/-- `RatFunc K` is a commutative monoid.

This is an intermediate step on the way to the full instance `RatFunc.instCommRing`.
-/
@[instance_reducible]
def instCommMonoid : CommMonoid (RatFunc K) where
  mul_assoc := by frac_tac
  mul_comm := by frac_tac
  one_mul := by frac_tac
  mul_one := by frac_tac
  npow := npowRec

/-- `RatFunc K` is an additive commutative group.

This is an intermediate step on the way to the full instance `RatFunc.instCommRing`.
-/
@[instance_reducible]
def instAddCommGroup : AddCommGroup (RatFunc K) where
  add_assoc := by frac_tac
  add_comm := by frac_tac
  zero_add := by frac_tac
  add_zero := by frac_tac
  neg_add_cancel := by frac_tac
  sub_eq_add_neg := by frac_tac
  nsmul_zero := by smul_tac
  nsmul_succ _ := by smul_tac
  zsmul_zero' := by smul_tac
  zsmul_succ' _ := by smul_tac
  zsmul_neg' _ := by smul_tac

instance instCommRing : CommRing (RatFunc K) :=
  { instCommMonoid K, instAddCommGroup K with
    zero_mul := by frac_tac
    mul_zero := by frac_tac
    left_distrib := by frac_tac
    right_distrib := by frac_tac
    npow := npowRec }

variable {K}

section LiftHom

open RatFunc

variable {G₀ L R S F : Type*} [CommGroupWithZero G₀] [Field L] [CommRing R] [CommRing S]
variable [FunLike F R[X] S[X]]

open scoped Classical in
/-- Lift a monoid homomorphism that maps polynomials `φ : R[X] →* S[X]`
to a `RatFunc R →* RatFunc S`,
on the condition that `φ` maps non-zero-divisors to non-zero-divisors,
by mapping both the numerator and denominator and quotienting them. -/
def map [MonoidHomClass F R[X] S[X]] (φ : F) (hφ : R[X]⁰ ≤ S[X]⁰.comap φ) :
    RatFunc R →* RatFunc S where
  toFun f :=
    RatFunc.liftOn f
      (fun n d => if h : φ d ∈ S[X]⁰ then ofFractionRing (Localization.mk (φ n) ⟨φ d, h⟩) else 0)
      fun {p q p' q'} hq hq' h => by
      simp only [Submonoid.mem_comap.mp (hφ hq), Submonoid.mem_comap.mp (hφ hq'),
        dite_eq_left, ofFractionRing.injEq, Localization.mk_eq_mk_iff]
      refine Localization.r_of_eq ?_
      simpa only [map_mul] using congr_arg φ h
  map_one' := by
    simp_rw [← ofFractionRing_one, ← Localization.mk_one, liftOn_ofFractionRing_mk,
      OneMemClass.coe_one, map_one, OneMemClass.one_mem, dite_true, ofFractionRing.injEq,
      Localization.mk_one, Localization.mk_eq_monoidOf_mk', Submonoid.LocalizationMap.mk'_self]
  map_mul' x y := by
    obtain ⟨x⟩ := x; obtain ⟨y⟩ := y
    cases x using Localization.induction_on with | _ pq
    cases y using Localization.induction_on with | _ p'q'
    obtain ⟨p, q⟩ := pq
    obtain ⟨p', q'⟩ := p'q'
    have hq : φ q ∈ S[X]⁰ := hφ q.prop
    have hq' : φ q' ∈ S[X]⁰ := hφ q'.prop
    have hqq' : φ ↑(q * q') ∈ S[X]⁰ := by simpa using Submonoid.mul_mem _ hq hq'
    simp_rw [← ofFractionRing_mul, Localization.mk_mul, liftOn_ofFractionRing_mk, dite_eq_left hq,
      dite_eq_left hq', dite_eq_left hqq', ← ofFractionRing_mul, Submonoid.coe_mul, map_mul,
      Localization.mk_mul, Submonoid.mk_mul_mk]

theorem map_apply_ofFractionRing_mk [MonoidHomClass F R[X] S[X]] (φ : F)
    (hφ : R[X]⁰ ≤ S[X]⁰.comap φ) (n : R[X]) (d : R[X]⁰) :
    map φ hφ (ofFractionRing (Localization.mk n d)) =
      ofFractionRing (Localization.mk (φ n) ⟨φ d, hφ d.prop⟩) := by
  simp only [map, MonoidHom.coe_mk, OneHom.coe_mk, liftOn_ofFractionRing_mk,
    Submonoid.mem_comap.mp (hφ d.2), ↓reduceDIte]

theorem map_injective [MonoidHomClass F R[X] S[X]] (φ : F) (hφ : R[X]⁰ ≤ S[X]⁰.comap φ)
    (hf : Function.Injective φ) : Function.Injective (map φ hφ) := by
  rintro ⟨x⟩ ⟨y⟩ h
  induction x using Localization.induction_on
  induction y using Localization.induction_on
  simpa only [map_apply_ofFractionRing_mk, ofFractionRing_injective.eq_iff,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists, mul_cancel_left_coe_nonZeroDivisors,
    exists_const, ← map_mul, hf.eq_iff] using h

set_option backward.isDefEq.respectTransparency.types false in
/-- Lift a ring homomorphism that maps polynomials `φ : R[X] →+* S[X]`
to a `RatFunc R →+* RatFunc S`,
on the condition that `φ` maps non-zero-divisors to non-zero-divisors,
by mapping both the numerator and denominator and quotienting them. -/
def mapRingHom [RingHomClass F R[X] S[X]] (φ : F) (hφ : R[X]⁰ ≤ S[X]⁰.comap φ) :
    RatFunc R →+* RatFunc S :=
  { map φ hφ with
    map_zero' := by
      simp_rw [MonoidHom.toFun_eq_coe, ← ofFractionRing_zero, ← Localization.mk_zero (1 : R[X]⁰),
        ← Localization.mk_zero (1 : S[X]⁰), map_apply_ofFractionRing_mk, map_zero,
        Localization.mk_eq_mk', IsLocalization.mk'_zero]
    map_add' := by
      rintro ⟨x⟩ ⟨y⟩
      induction x using Localization.induction_on
      induction y using Localization.induction_on
      · simp only [← ofFractionRing_add, Localization.add_mk, map_add, map_mul,
          MonoidHom.toFun_eq_coe, map_apply_ofFractionRing_mk, Submonoid.coe_mul,
          -- We have to specify `S[X]⁰` to `mk_mul_mk`, otherwise it will try to rewrite
          -- the wrong occurrence.
          Submonoid.mk_mul_mk S[X]⁰] }

theorem coe_mapRingHom_eq_coe_map [RingHomClass F R[X] S[X]] (φ : F) (hφ : R[X]⁰ ≤ S[X]⁰.comap φ) :
    (mapRingHom φ hφ : RatFunc R → RatFunc S) = map φ hφ :=
  rfl

-- TODO: Generalize to `FunLike` classes,
/-- Lift a monoid with zero homomorphism `R[X] →*₀ G₀` to a `RatFunc R →*₀ G₀`
on the condition that `φ` maps non-zero-divisors to non-zero-divisors,
by mapping both the numerator and denominator and quotienting them. -/
def liftMonoidWithZeroHom (φ : R[X] →*₀ G₀) (hφ : R[X]⁰ ≤ G₀⁰.comap φ) : RatFunc R →*₀ G₀ where
  toFun f :=
    Localization.liftOn (toFractionRing f)
      (fun p q => Checked.div (φ p) (φ q) (nonZeroDivisors.ne_zero (hφ q.2)).isUnit)
      fun {p p'} {q q'} h => by
        obtain ⟨c, hc⟩ := Localization.r_iff_exists.mp h
        have h' : (q' : R[X]) * p = q * p' := mul_cancel_left_coe_nonZeroDivisors.mp hc
        rw [div_eq_div_iff, ← map_mul, ← map_mul, mul_comm p, h', mul_comm]
  map_one' := by
    simp_rw [← ofFractionRing_one, ← Localization.mk_one, Localization.liftOn_mk,
      OneMemClass.coe_one, map_one, div_one₀]
  map_mul' x y := by
    obtain ⟨x⟩ := x
    obtain ⟨y⟩ := y
    cases x using Localization.induction_on
    cases y using Localization.induction_on
    rw [← ofFractionRing_mul, Localization.mk_mul]
    simp only [Localization.liftOn_mk, div_mul_div_comm₀, map_mul, Submonoid.coe_mul]
  map_zero' := by
    simp_rw [← ofFractionRing_zero, ← Localization.mk_zero (1 : R[X]⁰), Localization.liftOn_mk,
      map_zero, zero_div]

theorem liftMonoidWithZeroHom_apply_ofFractionRing_mk (φ : R[X] →*₀ G₀) (hφ : R[X]⁰ ≤ G₀⁰.comap φ)
    (n : R[X]) (d : R[X]⁰) :
    liftMonoidWithZeroHom φ hφ (ofFractionRing (Localization.mk n d)) =
      Checked.div (φ n) (φ d) (nonZeroDivisors.ne_zero (hφ d.2)).isUnit :=
  rfl

theorem liftMonoidWithZeroHom_injective (φ : R[X] →*₀ G₀) (hφ : Function.Injective φ)
    (hφ' : R[X]⁰ ≤ G₀⁰.comap φ := nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hφ) :
    Function.Injective (liftMonoidWithZeroHom φ hφ') := by
  rintro ⟨x⟩ ⟨y⟩
  cases x using Localization.induction_on
  cases y using Localization.induction_on with | _ a'
  simp_rw [liftMonoidWithZeroHom_apply_ofFractionRing_mk]
  intro h
  congr 1
  refine Localization.mk_eq_mk_iff.mpr (Localization.r_of_eq (M := R[X]) ?_)
  have := mul_eq_mul_of_div_eq_div _ _ h
  rwa [← map_mul, ← map_mul, hφ.eq_iff, mul_comm, mul_comm a'.fst] at this

set_option backward.isDefEq.respectTransparency.types false in
/-- Lift an injective ring homomorphism `R[X] →+* L` to a `RatFunc R →+* L`
by mapping both the numerator and denominator and quotienting them. -/
def liftRingHom (φ : R[X] →+* L) (hφ : R[X]⁰ ≤ L⁰.comap φ) : RatFunc R →+* L :=
  { liftMonoidWithZeroHom φ.toMonoidWithZeroHom hφ with
    map_add' := fun x y => by
      simp only [ZeroHom.toFun_eq_coe, MonoidWithZeroHom.toZeroHom_coe]
      cases subsingleton_or_nontrivial R
      · rw [Subsingleton.elim (x + y) y, Subsingleton.elim x 0, map_zero, zero_add]
      obtain ⟨x⟩ := x
      obtain ⟨y⟩ := y
      cases x using Localization.induction_on with | _ pq
      cases y using Localization.induction_on with | _ p'q'
      obtain ⟨p, q⟩ := pq
      obtain ⟨p', q'⟩ := p'q'
      rw [← ofFractionRing_add, Localization.add_mk]
      simp only [RingHom.toMonoidWithZeroHom_eq_coe,
        liftMonoidWithZeroHom_apply_ofFractionRing_mk]
      rw [div_add_div, div_eq_div_iff, mul_comm _ p, mul_comm _ p', mul_comm _ (φ p'), add_comm]
      simp only [map_add, map_mul, Submonoid.coe_mul] }

theorem liftRingHom_apply_ofFractionRing_mk (φ : R[X] →+* L) (hφ : R[X]⁰ ≤ L⁰.comap φ) (n : R[X])
    (d : R[X]⁰) : liftRingHom φ hφ (ofFractionRing (Localization.mk n d)) =
      Checked.div (φ n) (φ d) (nonZeroDivisors.ne_zero (hφ d.2)).isUnit :=
  rfl

@[simp]
lemma liftRingHom_ofFractionRing_algebraMap
    (φ : R[X] →+* L) (hφ : R[X]⁰ ≤ L⁰.comap φ) (x : R[X]) :
    RatFunc.liftRingHom φ hφ (ofFractionRing <| algebraMap R[X] _ x) = φ x := by
  rw [← Localization.mk_one_eq_algebraMap, liftRingHom_apply_ofFractionRing_mk]
  simp

theorem liftRingHom_injective (φ : R[X] →+* L) (hφ : Function.Injective φ)
    (hφ' : R[X]⁰ ≤ L⁰.comap φ := nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hφ) :
    Function.Injective (liftRingHom φ hφ') :=
  liftMonoidWithZeroHom_injective _ hφ

end LiftHom

variable (K)

@[stacks 09FK]
instance instField [IsDomain K] : Field (RatFunc K) where
  isUnit_of_ne_zero {x} hx := by
    obtain ⟨p⟩ := x
    exact (Ne.isUnit fun hp ↦ hx (by rw [hp, ofFractionRing_zero])).map
      (toFractionRingRingEquiv K).symm

variable {K} in
theorem ofFractionRing_inv [IsDomain K] (p : FractionRing K[X]) {hp : IsUnit p} :
    ofFractionRing p⁻¹ = Checked.inv (ofFractionRing p) (hp.map (toFractionRingRingEquiv K).symm) :=
  map_inv₀ (toFractionRingRingEquiv K).symm p

variable {K} in
theorem ofFractionRing_div [IsDomain K] (p q : FractionRing K[X]) {hq : IsUnit q} :
    ofFractionRing (p / q) =
      Checked.div (ofFractionRing p) (ofFractionRing q) (hq.map (toFractionRingRingEquiv K).symm) :=
  map_div₀ (toFractionRingRingEquiv K).symm p q

section IsFractionRing

/-! ### `RatFunc` as field of fractions of `Polynomial` -/

section IsDomain

variable [IsDomain K]

instance (R : Type*) [CommSemiring R] [Algebra R K[X]] : Algebra R (RatFunc K) where
  algebraMap :=
  { toFun x := RatFunc.mk (algebraMap _ _ x) 1
    map_add' x y := by simp only [mk_one', map_add, ofFractionRing_add]
    map_mul' x y := by simp only [mk_one', map_mul, ofFractionRing_mul]
    map_one' := by simp only [mk_one', map_one, ofFractionRing_one]
    map_zero' := by simp only [mk_one', map_zero, ofFractionRing_zero] }
  smul_def' c x := by
    induction x using RatFunc.induction_on' with | _ p q hq
    rw [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, mk_one', ← mk_smul,
      mk_def_of_ne (c • p), mk_def_of_ne p, ← ofFractionRing_mul,
      IsLocalization.mul_mk'_eq_mk'_of_mul, Algebra.smul_def]
  commutes' _ _ := mul_comm _ _

variable {K}

/-- The coercion from polynomials to rational functions, implemented as the algebra map from a
domain to its field of fractions -/
@[coe]
def coePolynomial (P : Polynomial K) : RatFunc K := algebraMap _ _ P

instance : Coe (Polynomial K) (RatFunc K) := ⟨coePolynomial⟩

theorem mk_one (x : K[X]) : RatFunc.mk x 1 = algebraMap _ _ x :=
  rfl

theorem ofFractionRing_algebraMap (x : K[X]) :
    ofFractionRing (algebraMap _ (FractionRing K[X]) x) = algebraMap _ _ x := by
  rw [← mk_one, mk_one']

variable (K) in
/--
The equivalence between `RatFunc K` and the field of fractions of `K[X]`
-/
@[simps! apply]
def toFractionRingAlgEquiv (R : Type*) [CommSemiring R] [Algebra R K[X]] :
    RatFunc K ≃ₐ[R] FractionRing K[X] where
  __ := RatFunc.toFractionRingRingEquiv K
  commutes' r := by
    change (RatFunc.mk (algebraMap R K[X] r) 1).toFractionRing = _
    rw [mk_one']; rfl

variable (K) in
/-- `RatFunc K` is the field of fractions of the polynomials over `K`. -/
instance : IsFractionRing K[X] (RatFunc K) where
  map_units y := by
    rw [← ofFractionRing_algebraMap]
    exact (toFractionRingRingEquiv K).symm.toRingHom.isUnit_map (IsLocalization.map_units _ y)
  exists_of_eq {x y} := by
    rw [← ofFractionRing_algebraMap, ← ofFractionRing_algebraMap]
    exact fun h ↦ IsLocalization.exists_of_eq ((toFractionRingRingEquiv K).symm.injective h)
  surj := by
    rintro ⟨z⟩
    convert! IsLocalization.surj K[X]⁰ z
    simp only [← ofFractionRing_algebraMap, ← ofFractionRing_mul,
      ofFractionRing.injEq]

@[simp]
theorem mk_eq_div (p q : K[X]) {hq : q ≠ 0} :
    RatFunc.mk p q = algebraMap _ _ p / algebraMap _ _ q := by
  simp only [mk_eq_div', ofFractionRing_div, ofFractionRing_algebraMap]

@[simp]
theorem div_smul {R} [Monoid R] [DistribMulAction R K[X]] [IsScalarTower R K[X] K[X]] (c : R)
    (p q : K[X]) {hq : IsUnit (algebraMap K[X] (RatFunc K) q)} :
    algebraMap _ (RatFunc K) (c • p) / algebraMap _ _ q =
      c • (algebraMap _ _ p / algebraMap _ _ q) := by
  have hq' : q ≠ 0 := fun h ↦ hq.ne_zero (by rw [h, map_zero])
  rw [← mk_eq_div (hq := hq'), mk_smul, mk_eq_div]

theorem algebraMap_apply {R : Type*} [CommSemiring R] [Algebra R K[X]] (x : R) :
    algebraMap R (RatFunc K) x = algebraMap _ _ (algebraMap R K[X] x) / algebraMap K[X] _ 1 := by
  rw [← mk_eq_div]
  rfl

/-- A rational function `p / q` is mapped to `φ p / φ q`. The quotient on the right exists
because `φ` maps nonzero divisors to nonzero divisors. -/
theorem map_apply_div {R F : Type*} [CommRing R] [IsDomain R]
    [FunLike F K[X] R[X]] [MonoidHomClass F K[X] R[X]]
    (φ : F) (hφ : K[X]⁰ ≤ R[X]⁰.comap φ) (p q : K[X])
    {hq : IsUnit (algebraMap K[X] (RatFunc K) q)} :
    map φ hφ (algebraMap _ _ p / algebraMap _ _ q) =
      Checked.div (algebraMap _ _ (φ p)) (algebraMap _ _ (φ q))
        (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (hφ
          (mem_nonZeroDivisors_of_ne_zero fun h ↦ hq.ne_zero (by rw [h, map_zero])))).isUnit := by
  have hq' : q ≠ 0 := fun h ↦ hq.ne_zero (by rw [h, map_zero])
  have hφq : φ q ≠ 0 := nonZeroDivisors.ne_zero (hφ (mem_nonZeroDivisors_of_ne_zero hq'))
  rw [← mk_eq_div (hq := hq'), mk_eq_localization_mk, map_apply_ofFractionRing_mk,
    ← mk_eq_div (hq := hφq), mk_eq_localization_mk]

@[simp]
theorem map_apply_algebraMap {R F : Type*} [CommRing R] [IsDomain R]
    [FunLike F K[X] R[X]] [MonoidHomClass F K[X] R[X]]
    (φ : F) (hφ : K[X]⁰ ≤ R[X]⁰.comap φ) (p : K[X]) :
    map φ hφ (algebraMap K[X] (RatFunc K) p) = algebraMap R[X] (RatFunc R) (φ p) := by
  simpa only [map_one, div_one₀] using map_apply_div φ hφ p 1 (hq := isUnit_one.map _)

/-- The lift of `φ` maps `p / q` to `φ p / φ q`. The quotient on the right exists because `φ`
maps nonzero divisors to nonzero divisors. -/
theorem liftMonoidWithZeroHom_apply_div {L : Type*} [CommGroupWithZero L]
    (φ : MonoidWithZeroHom K[X] L) (hφ : K[X]⁰ ≤ L⁰.comap φ) (p q : K[X])
    {hq : IsUnit (algebraMap K[X] (RatFunc K) q)} :
    liftMonoidWithZeroHom φ hφ (algebraMap _ _ p / algebraMap _ _ q) =
      Checked.div (φ p) (φ q) (nonZeroDivisors.ne_zero
        (hφ (mem_nonZeroDivisors_of_ne_zero fun h ↦ hq.ne_zero (by rw [h, map_zero])))).isUnit := by
  have hq' : q ≠ 0 := fun h ↦ hq.ne_zero (by rw [h, map_zero])
  rw [← mk_eq_div (hq := hq'), mk_eq_localization_mk, liftMonoidWithZeroHom_apply_ofFractionRing_mk]

@[simp]
theorem liftMonoidWithZeroHom_apply_div' {L : Type*} [CommGroupWithZero L]
    (φ : MonoidWithZeroHom K[X] L) (hφ : K[X]⁰ ≤ L⁰.comap φ) (p q : K[X])
    {hq : IsUnit (liftMonoidWithZeroHom φ hφ (algebraMap _ _ q))} :
    liftMonoidWithZeroHom φ hφ (algebraMap _ _ p) / liftMonoidWithZeroHom φ hφ (algebraMap _ _ q) =
      Checked.div (φ p) (φ q) (nonZeroDivisors.ne_zero (hφ (mem_nonZeroDivisors_of_ne_zero
        fun h ↦ hq.ne_zero (by rw [h, map_zero, map_zero])))).isUnit := by
  have hq' : q ≠ 0 := fun h ↦ hq.ne_zero (by rw [h, map_zero, map_zero])
  have hq'' : IsUnit (algebraMap K[X] (RatFunc K) q) := by checked_unit
  rw [← map_div₀ (liftMonoidWithZeroHom φ hφ) _ _ (hb := hq''), liftMonoidWithZeroHom_apply_div]

theorem liftRingHom_apply_div {L : Type*} [Field L] (φ : K[X] →+* L) (hφ : K[X]⁰ ≤ L⁰.comap φ)
    (p q : K[X]) {hq : IsUnit (algebraMap K[X] (RatFunc K) q)} :
    liftRingHom φ hφ (algebraMap _ _ p / algebraMap _ _ q) =
      Checked.div (φ p) (φ q) (nonZeroDivisors.ne_zero
        (hφ (mem_nonZeroDivisors_of_ne_zero fun h ↦ hq.ne_zero (by rw [h, map_zero])))).isUnit :=
  liftMonoidWithZeroHom_apply_div φ.toMonoidWithZeroHom hφ p q

theorem liftRingHom_apply_div' {L : Type*} [Field L] (φ : K[X] →+* L) (hφ : K[X]⁰ ≤ L⁰.comap φ)
    (p q : K[X]) {hq : IsUnit (liftRingHom φ hφ (algebraMap _ _ q))} :
    liftRingHom φ hφ (algebraMap _ _ p) / liftRingHom φ hφ (algebraMap _ _ q) =
      Checked.div (φ p) (φ q) (nonZeroDivisors.ne_zero (hφ (mem_nonZeroDivisors_of_ne_zero
        fun h ↦ hq.ne_zero (by rw [h, map_zero, map_zero])))).isUnit :=
  liftMonoidWithZeroHom_apply_div' φ.toMonoidWithZeroHom hφ p q

@[simp]
lemma liftRingHom_algebraMap {L : Type*} [Field L] (φ : K[X] →+* L) (hφ : K[X]⁰ ≤ L⁰.comap φ)
    (x : K[X]) : liftRingHom φ hφ (algebraMap K[X] _ x) = φ x := by
  rw [← ofFractionRing_algebraMap, liftRingHom_ofFractionRing_algebraMap]

@[simp]
lemma liftRingHom_comp_algebraMap {L : Type*} [Field L] (φ : K[X] →+* L) (hφ : K[X]⁰ ≤ L⁰.comap φ) :
    (liftRingHom φ hφ).comp (algebraMap K[X] _) = φ :=
  RingHom.ext fun _ ↦ liftRingHom_algebraMap _ hφ _

variable (K)

theorem ofFractionRing_comp_algebraMap :
    ofFractionRing ∘ algebraMap K[X] (FractionRing K[X]) = algebraMap _ _ :=
  funext ofFractionRing_algebraMap

theorem algebraMap_injective : Function.Injective (algebraMap K[X] (RatFunc K)) := by
  rw [← ofFractionRing_comp_algebraMap]
  exact ofFractionRing_injective.comp (IsFractionRing.injective _ _)

variable {K}

section LiftAlgHom

variable {L R S : Type*} [Field L] [CommRing R] [IsDomain R] [CommSemiring S] [Algebra S K[X]]
  [Algebra S L] [Algebra S R[X]] (φ : K[X] →ₐ[S] L) (hφ : K[X]⁰ ≤ L⁰.comap φ)

/-- Lift an algebra homomorphism that maps polynomials `φ : K[X] →ₐ[S] R[X]`
to a `RatFunc K →ₐ[S] RatFunc R`,
on the condition that `φ` maps non-zero-divisors to non-zero-divisors,
by mapping both the numerator and denominator and quotienting them. -/
def mapAlgHom (φ : K[X] →ₐ[S] R[X]) (hφ : K[X]⁰ ≤ R[X]⁰.comap φ) : RatFunc K →ₐ[S] RatFunc R :=
  { mapRingHom φ hφ with
    commutes' := fun r => by
      simp_rw [RingHom.toFun_eq_coe, coe_mapRingHom_eq_coe_map, algebraMap_apply r, map_apply_div,
        map_one, AlgHom.commutes] }

theorem coe_mapAlgHom_eq_coe_map (φ : K[X] →ₐ[S] R[X]) (hφ : K[X]⁰ ≤ R[X]⁰.comap φ) :
    (mapAlgHom φ hφ : RatFunc K → RatFunc R) = map φ hφ :=
  rfl

/-- Lift an injective algebra homomorphism `K[X] →ₐ[S] L` to a `RatFunc K →ₐ[S] L`
by mapping both the numerator and denominator and quotienting them. -/
def liftAlgHom : RatFunc K →ₐ[S] L :=
  { liftRingHom φ.toRingHom hφ with
    commutes' := fun r => by
      simp_rw [RingHom.toFun_eq_coe, AlgHom.toRingHom_eq_coe, algebraMap_apply r,
        liftRingHom_apply_div, AlgHom.coe_toRingHom, map_one, div_one₀, AlgHom.commutes] }

theorem liftAlgHom_apply_ofFractionRing_mk (n : K[X]) (d : K[X]⁰) :
    liftAlgHom φ hφ (ofFractionRing (Localization.mk n d)) =
      Checked.div (φ n) (φ d) (nonZeroDivisors.ne_zero (hφ d.2)).isUnit :=
  rfl

theorem liftAlgHom_injective (φ : K[X] →ₐ[S] L) (hφ : Function.Injective φ)
    (hφ' : K[X]⁰ ≤ L⁰.comap φ := nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ hφ) :
    Function.Injective (liftAlgHom φ hφ') :=
  liftMonoidWithZeroHom_injective _ hφ

@[simp]
theorem liftAlgHom_apply_div' (p q : K[X]) {hq : IsUnit (liftAlgHom φ hφ (algebraMap _ _ q))} :
    liftAlgHom φ hφ (algebraMap _ _ p) / liftAlgHom φ hφ (algebraMap _ _ q) =
      Checked.div (φ p) (φ q) (nonZeroDivisors.ne_zero (hφ (mem_nonZeroDivisors_of_ne_zero
        fun h ↦ hq.ne_zero (by rw [h, map_zero, map_zero])))).isUnit :=
  liftMonoidWithZeroHom_apply_div' φ.toRingHom.toMonoidWithZeroHom hφ p q

theorem liftAlgHom_apply_div (p q : K[X]) {hq : IsUnit (algebraMap K[X] (RatFunc K) q)} :
    liftAlgHom φ hφ (algebraMap _ _ p / algebraMap _ _ q) =
      Checked.div (φ p) (φ q) (nonZeroDivisors.ne_zero
        (hφ (mem_nonZeroDivisors_of_ne_zero fun h ↦ hq.ne_zero (by rw [h, map_zero])))).isUnit :=
  liftMonoidWithZeroHom_apply_div φ.toRingHom.toMonoidWithZeroHom hφ p q

end LiftAlgHom

theorem algebraMap_ne_zero {x : K[X]} (hx : x ≠ 0) : algebraMap K[X] (RatFunc K) x ≠ 0 := by
  simpa

@[simp]
theorem liftOn_div {P : Sort v} (p q : K[X]) {hq : IsUnit (algebraMap K[X] (RatFunc K) q)}
    (f : K[X] → K[X] → P)
    (H' : ∀ {p q p' q'} (_hq : q ≠ 0) (_hq' : q' ≠ 0), q' * p = q * p' → f p q = f p' q')
    (H : ∀ {p q p' q'} (_hq : q ∈ K[X]⁰) (_hq' : q' ∈ K[X]⁰), q' * p = q * p' → f p q = f p' q' :=
      fun {_ _ _ _} hq hq' h => H' (nonZeroDivisors.ne_zero hq) (nonZeroDivisors.ne_zero hq') h) :
    (RatFunc.liftOn (algebraMap _ (RatFunc K) p / algebraMap _ _ q)) f @H = f p q := by
  rw [← mk_eq_div (hq := fun h ↦ hq.ne_zero (by rw [h, map_zero])), liftOn_mk _ _ f @H']

@[simp]
theorem liftOn'_div {P : Sort v} (p q : K[X]) {hq : IsUnit (algebraMap K[X] (RatFunc K) q)}
    (f : K[X] → K[X] → P) (H) :
    (RatFunc.liftOn' (algebraMap _ (RatFunc K) p / algebraMap _ _ q)) f @H = f p q := by
  rw [← mk_eq_div (hq := fun h ↦ hq.ne_zero (by rw [h, map_zero])), liftOn'_mk]

/-- Induction principle for `RatFunc K`: if `f p q : P (p / q)` for all `p q : K[X]`,
then `P` holds on all elements of `RatFunc K`.

See also `induction_on'`, which is a recursion principle defined in terms of `RatFunc.mk`.
-/
protected theorem induction_on {P : RatFunc K → Prop} (x : RatFunc K)
    (f : ∀ (p q : K[X]) (_ : q ≠ 0), P (algebraMap _ (RatFunc K) p / algebraMap _ _ q)) : P x :=
  x.induction_on' fun p q hq => by simpa using f p q hq

theorem ofFractionRing_mk' (x : K[X]) (y : K[X]⁰) :
    ofFractionRing (IsLocalization.mk' _ x y) =
      IsLocalization.mk' (RatFunc K) x y := by
  have hy : (y : K[X]) ≠ 0 := nonZeroDivisors.ne_zero y.2
  rw [IsFractionRing.mk'_eq_div, IsFractionRing.mk'_eq_div, ← mk_eq_div' (hq := hy),
    ← mk_eq_div (hq := hy)]

theorem mk_eq_mk' (f : Polynomial K) {g : Polynomial K} (hg : g ≠ 0) :
    RatFunc.mk f g = IsLocalization.mk' (RatFunc K) f
      ⟨g, mem_nonZeroDivisors_iff_ne_zero.2 hg⟩ := by
  simp only [mk_eq_div, IsFractionRing.mk'_eq_div]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
theorem ofFractionRing_eq :
    (ofFractionRing : FractionRing K[X] → RatFunc K) = IsLocalization.algEquiv K[X]⁰ _ _ :=
  funext fun x =>
    Localization.induction_on x fun x => by
      simp only [Localization.mk_eq_mk'_apply, ofFractionRing_mk', IsLocalization.algEquiv_apply,
        IsLocalization.map_mk', RingHom.id_apply]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
theorem toFractionRing_eq :
    (toFractionRing : RatFunc K → FractionRing K[X]) = IsLocalization.algEquiv K[X]⁰ _ _ :=
  funext fun ⟨x⟩ =>
    Localization.induction_on x fun x => by
      simp only [Localization.mk_eq_mk'_apply, ofFractionRing_mk', IsLocalization.algEquiv_apply,
        IsLocalization.map_mk', RingHom.id_apply]

@[simp]
theorem toFractionRingRingEquiv_symm_eq :
    (toFractionRingRingEquiv K).symm = (IsLocalization.algEquiv K[X]⁰ _ _).toRingEquiv := by
  ext x
  simp [toFractionRingRingEquiv, ofFractionRing_eq]

section lift

/-
As `RatFunc R` is a one-field-struct, we need to specialize the following instances of
`FractionRing`.
-/

variable (R L : Type*) [CommRing R] [Field L] [IsDomain R] [Algebra R[X] L] [FaithfulSMul R[X] L]

/-- `FractionRing.liftAlgebra` specialized to `RatFunc R`.

This is a scoped instance because it creates a diamond when `L = RatFunc R`. -/
scoped instance liftAlgebra : Algebra (RatFunc R) L :=
  RingHom.toAlgebra (IsFractionRing.lift (FaithfulSMul.algebraMap_injective R[X] _))

/-- `FractionRing.isScalarTower_liftAlgebra` specialized to `RatFunc R`. -/
instance isScalarTower_liftAlgebra :
    IsScalarTower R[X] (RatFunc R) L :=
  IsScalarTower.of_algebraMap_eq fun x =>
    (IsFractionRing.lift_algebraMap (FaithfulSMul.algebraMap_injective R[X] L) x).symm

attribute [local instance] Polynomial.algebra

/-- `FractionRing.instFaithfulSMul` specialized to `RatFunc R`. -/
instance faithfulSMul (K E : Type*) [Field K] [Field E] [Algebra K E]
    [FaithfulSMul K E] : FaithfulSMul K[X] (RatFunc E) :=
  (faithfulSMul_iff_algebraMap_injective ..).mpr <|
    (IsFractionRing.injective E[X] _).comp
      (Polynomial.map_injective _ <| FaithfulSMul.algebraMap_injective K E)

section rank

attribute [local instance] Polynomial.algebra

variable (k K : Type*) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]

theorem rank_ratFunc_ratFunc : Module.rank (RatFunc k) (RatFunc K) = Module.rank k K := by
  rw [Algebra.IsAlgebraic.rank_of_isFractionRing k[X] (RatFunc k) K[X] (RatFunc K),
    rank_polynomial_polynomial]

theorem finrank_ratFunc_ratFunc : Module.finrank (RatFunc k) (RatFunc K) = Module.finrank k K := by
  by_cases hf : Module.Finite (RatFunc k) (RatFunc K)
  · have hrank := rank_ratFunc_ratFunc k K
    rw [← Module.finrank_eq_rank] at hrank
    exact (Module.finrank_eq_of_rank_eq hrank.symm).symm
  · have hf' : ¬ Module.Finite k K := by
      rwa [← Module.rank_lt_aleph0_iff, ← rank_ratFunc_ratFunc, Module.rank_lt_aleph0_iff]
    rw [Module.finrank_of_not_finite hf, Module.finrank_of_not_finite hf']

end rank

end lift

section IsScalarTower

/-- Let `RatFunc A / A[X] / R / R₀` be a tower. If `A[X] / R / R₀` is a scalar tower
then so is `RatFunc A / R / R₀`. -/
instance (R₀ R A : Type*) [CommSemiring R₀] [CommSemiring R] [CommRing A] [IsDomain A]
    [Algebra R₀ A[X]] [SMul R₀ R] [Algebra R A[X]] [IsScalarTower R₀ R A[X]] :
    IsScalarTower R₀ R (RatFunc A) := IsScalarTower.to₁₂₄ _ _ A[X] _

/-- Let `K / RatFunc A / A[X] / R` be a tower. If `K / A[X] / R` is a scalar tower
then so is `K / RatFunc A / R`. -/
instance (R A K : Type*) [CommRing A] [IsDomain A] [Field K] [Algebra A[X] K]
    [FaithfulSMul A[X] K] [CommSemiring R] [Algebra R A[X]] [SMul R K] [IsScalarTower R A[X] K] :
    IsScalarTower R (RatFunc A) K :=
  IsScalarTower.to₁₃₄ _ A[X] _ _

/-- Let `K / k / RatFunc A / A[X]` be a tower. If `K / k / A[X]` is a scalar tower
then so is `K / k / RatFunc A`. -/
instance (A k K : Type*) [CommRing A] [IsDomain A] [Field k] [Field K] [Algebra A[X] k]
    [Algebra A[X] K] [SMul k K] [FaithfulSMul A[X] k] [FaithfulSMul A[X] K]
    [IsScalarTower A[X] k K] : IsScalarTower (RatFunc A) k K where
  smul_assoc a b c := by
    induction a using RatFunc.induction_on with | f p q hq =>
    rw [← smul_right_inj hq]
    simp_rw [← smul_assoc, Algebra.smul_def q]
    field_simp [hq]
    simp

end IsScalarTower

end IsDomain

end IsFractionRing

end CommRing

section NumDenom

/-! ### Numerator and denominator -/

open GCDMonoid Polynomial

variable [Field K]

open scoped Classical in
/-- `RatFunc.numDenom` are numerator and denominator of a rational function over a field,
normalized such that the denominator is monic. -/
def numDenom (x : RatFunc K) : K[X] × K[X] :=
  x.liftOn'
    (fun p q =>
      if hq : q = 0 then ⟨0, 1⟩
      else
        let r := gcd p q
        ⟨Polynomial.C (Checked.inv (q / r).leadingCoeff
            (leadingCoeff_ne_zero.mpr (right_div_gcd_ne_zero hq)).isUnit) * (p / r),
          Polynomial.C (Checked.inv (q / r).leadingCoeff
            (leadingCoeff_ne_zero.mpr (right_div_gcd_ne_zero hq)).isUnit) * (q / r)⟩)
  (by
      intro p q a hq ha
      dsimp only
      rw [dite_eq_right hq, dite_eq_right (mul_ne_zero ha hq)]
      have ha' : a.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr ha
      have hainv : a.leadingCoeff⁻¹ ≠ 0 := inv_ne_zero
      have hg : gcd (a * p) (a * q) = Polynomial.C a.leadingCoeff⁻¹ * a * gcd p q := by
        rw [gcd_mul_left, normalize_apply a, Polynomial.coe_normUnit,
          CommGroupWithZero.coe_normUnit _ ha', mul_comm a]
      have hdivp : Polynomial.C a.leadingCoeff⁻¹ * gcd p q ∣ p :=
        (C_mul_dvd hainv).mpr (gcd_dvd_left p q)
      have hdivq : Polynomial.C a.leadingCoeff⁻¹ * gcd p q ∣ q :=
        (C_mul_dvd hainv).mpr (gcd_dvd_right p q)
      have hp' : a * p / gcd (a * p) (a * q) = Polynomial.C a.leadingCoeff * (p / gcd p q) := by
        rw [hg, mul_comm _ a, mul_assoc, EuclideanDomain.mul_div_mul_cancel ha hdivp,
          div_C_mul (ha := hainv.isUnit), inv_inv₀]
      have hq' : a * q / gcd (a * p) (a * q) = Polynomial.C a.leadingCoeff * (q / gcd p q) := by
        rw [hg, mul_comm _ a, mul_assoc, EuclideanDomain.mul_div_mul_cancel ha hdivq,
          div_C_mul (ha := hainv.isUnit), inv_inv₀]
      have hqg : (q / gcd p q).leadingCoeff ≠ 0 :=
        leadingCoeff_ne_zero.mpr (right_div_gcd_ne_zero hq)
      have key : ∀ X : K[X], Polynomial.C (a.leadingCoeff * (q / gcd p q).leadingCoeff)⁻¹ *
          (Polynomial.C a.leadingCoeff * X) = Polynomial.C (q / gcd p q).leadingCoeff⁻¹ * X := by
        intro X
        rw [← mul_assoc, ← Polynomial.C_mul, mul_inv₀, mul_comm a.leadingCoeff⁻¹, mul_assoc,
          inv_mul_cancel₀, mul_one]
      simp only [hp', hq', leadingCoeff_mul, leadingCoeff_C, key])

open scoped Classical in
@[simp]
theorem numDenom_div (p : K[X]) {q : K[X]} (hq : q ≠ 0) :
    numDenom (algebraMap _ _ p / algebraMap _ _ q) =
      (Polynomial.C (Checked.inv (q / gcd p q).leadingCoeff
          (leadingCoeff_ne_zero.mpr (right_div_gcd_ne_zero hq)).isUnit) * (p / gcd p q),
        Polynomial.C (Checked.inv (q / gcd p q).leadingCoeff
          (leadingCoeff_ne_zero.mpr (right_div_gcd_ne_zero hq)).isUnit) * (q / gcd p q)) := by
  rw [numDenom, liftOn'_div, dite_eq_right hq]

/-- `RatFunc.num` is the numerator of a rational function,
normalized such that the denominator is monic. -/
def num (x : RatFunc K) : K[X] :=
  x.numDenom.1

open scoped Classical in
@[simp]
theorem num_div (p q : K[X]) {hq : IsUnit (algebraMap K[X] (RatFunc K) q)} :
    num (algebraMap _ _ p / algebraMap _ _ q) =
      Polynomial.C (Checked.inv (q / gcd p q).leadingCoeff (leadingCoeff_ne_zero.mpr
        (right_div_gcd_ne_zero fun h ↦ hq.ne_zero (by rw [h, map_zero]))).isUnit) *
        (p / gcd p q) := by
  rw [num, numDenom_div _ fun h ↦ hq.ne_zero (by rw [h, map_zero])]

@[simp]
theorem num_zero : num (0 : RatFunc K) = 0 := by
  convert! num_div (0 : K[X]) 1 (hq := isUnit_one.map _) <;> simp

@[simp]
theorem num_one : num (1 : RatFunc K) = 1 := by
  convert! num_div (1 : K[X]) 1 (hq := isUnit_one.map _) <;> simp

@[simp]
theorem num_algebraMap (p : K[X]) : num (algebraMap _ _ p) = p := by
  convert! num_div p 1 (hq := isUnit_one.map _) <;> simp

open scoped Classical in
@[simp] private theorem div_gcd_dvd_left (p q : K[X]) : p / gcd p q ∣ p :=
  EuclideanDomain.div_dvd_of_dvd (gcd_dvd_left p q)

theorem num_div_dvd (p : K[X]) {q : K[X]} (hq : q ≠ 0) :
    num (algebraMap _ _ p / algebraMap _ _ q) ∣ p := by
  classical
  rw [num_div _ q, C_mul_dvd inv_ne_zero]
  exact div_gcd_dvd_left p q

open scoped Classical in
/-- The normalized numerator of `p / q`, expressed in terms of `gcd p q`, divides `p`. -/
theorem num_div_dvd' (p : K[X]) {q : K[X]} (hq : q ≠ 0) :
    C (Checked.inv (q / gcd p q).leadingCoeff
      (leadingCoeff_ne_zero.mpr (right_div_gcd_ne_zero hq)).isUnit) * (p / gcd p q) ∣ p := by
  rw [C_mul_dvd inv_ne_zero]
  exact div_gcd_dvd_left p q

/-- `RatFunc.denom` is the denominator of a rational function,
normalized such that it is monic. -/
def denom (x : RatFunc K) : K[X] :=
  x.numDenom.2

open scoped Classical in
@[simp]
theorem denom_div (p : K[X]) {q : K[X]} (hq : q ≠ 0) :
    denom (algebraMap _ _ p / algebraMap _ _ q) =
      Polynomial.C (Checked.inv (q / gcd p q).leadingCoeff
        (leadingCoeff_ne_zero.mpr (right_div_gcd_ne_zero hq)).isUnit) * (q / gcd p q) := by
  rw [denom, numDenom_div _ hq]

theorem monic_denom (x : RatFunc K) : (denom x).Monic := by
  classical
  induction x using RatFunc.induction_on with
  | f p q hq =>
    rw [denom_div p hq, mul_comm]
    exact Polynomial.monic_mul_leadingCoeff_inv (right_div_gcd_ne_zero hq)

theorem denom_ne_zero (x : RatFunc K) : denom x ≠ 0 :=
  (monic_denom x).ne_zero

/- Evidence rule: the denominator of a rational function is nonzero, so the quotient
`algebraMap _ _ x.num / algebraMap _ _ x.denom` elaborates without explicit evidence. -/
macro_rules | `(tactic| checked_nonzero) => `(tactic|
    solve
    | assumption
    | (apply RatFunc.denom_ne_zero))

@[simp]
theorem denom_zero : denom (0 : RatFunc K) = 1 := by
  convert! denom_div (0 : K[X]) one_ne_zero <;> simp

@[simp]
theorem denom_one : denom (1 : RatFunc K) = 1 := by
  convert! denom_div (1 : K[X]) one_ne_zero <;> simp

@[simp]
theorem denom_algebraMap (p : K[X]) : denom (algebraMap _ (RatFunc K) p) = 1 := by
  convert! denom_div p one_ne_zero <;> simp

@[simp]
theorem denom_div_dvd (p q : K[X]) {hq : IsUnit (algebraMap K[X] (RatFunc K) q)} :
    denom (algebraMap _ _ p / algebraMap _ _ q) ∣ q := by
  classical
  rw [denom_div _ fun h ↦ hq.ne_zero (by rw [h, map_zero]), C_mul_dvd inv_ne_zero]
  exact EuclideanDomain.div_dvd_of_dvd (gcd_dvd_right p q)

@[simp]
theorem num_div_denom (x : RatFunc K) : algebraMap _ _ (num x) / algebraMap _ _ (denom x) = x := by
  classical
  induction x using RatFunc.induction_on with | _ p q hq
  simp only [num_div, denom_div p hq, map_mul]
  rw [mul_div_mul_left, div_eq_div_iff, ← map_mul, ← map_mul, mul_comm _ q,
    ← EuclideanDomain.mul_div_assoc _ (gcd_dvd_right p q),
    ← EuclideanDomain.mul_div_assoc _ (gcd_dvd_left p q), mul_comm]

theorem isCoprime_num_denom (x : RatFunc K) : IsCoprime x.num x.denom := by
  classical
  induction x using RatFunc.induction_on with | _ p q hq
  rw [num_div, denom_div _ hq]
  exact (isCoprime_mul_unit_left
    ((leadingCoeff_ne_zero.2 <| right_div_gcd_ne_zero hq).isUnit.inv₀.map C) _ _).2
      (isCoprime_div_gcd_div_gcd hq)

@[simp]
theorem num_eq_zero_iff {x : RatFunc K} : num x = 0 ↔ x = 0 :=
  ⟨fun h => by rw [← num_div_denom x, h, map_zero, zero_div], fun h => h.symm ▸ num_zero⟩

theorem num_ne_zero {x : RatFunc K} (hx : x ≠ 0) : num x ≠ 0 :=
  mt num_eq_zero_iff.mp hx

theorem num_mul_eq_mul_denom_iff {x : RatFunc K} {p q : K[X]} (hq : q ≠ 0) :
    x.num * q = p * x.denom ↔ x = algebraMap _ _ p / algebraMap _ _ q := by
  rw [← (algebraMap_injective K).eq_iff, eq_div_iff]
  conv_rhs => rw [← num_div_denom x]
  rw [map_mul, map_mul, div_mul_eq_mul_div₀, div_eq_iff]

theorem num_denom_add (x y : RatFunc K) :
    (x + y).num * (x.denom * y.denom) = (x.num * y.denom + x.denom * y.num) * (x + y).denom :=
  (num_mul_eq_mul_denom_iff (mul_ne_zero (denom_ne_zero x) (denom_ne_zero y))).mpr <| by
    conv_lhs => rw [← num_div_denom x, ← num_div_denom y]
    rw [div_add_div]
    simp only [map_mul, map_add]

theorem num_denom_neg (x : RatFunc K) : (-x).num * x.denom = -x.num * (-x).denom := by
  rw [num_mul_eq_mul_denom_iff (denom_ne_zero x), map_neg, neg_div₀, num_div_denom]

theorem num_denom_mul (x y : RatFunc K) :
    (x * y).num * (x.denom * y.denom) = x.num * y.num * (x * y).denom :=
  (num_mul_eq_mul_denom_iff (mul_ne_zero (denom_ne_zero x) (denom_ne_zero y))).mpr <| by
    conv_lhs => rw [← num_div_denom x, ← num_div_denom y, div_mul_div_comm₀]
    simp only [map_mul]

theorem num_dvd {x : RatFunc K} {p : K[X]} (hp : p ≠ 0) :
    num x ∣ p ↔ ∃ (q : K[X]) (_ : q ≠ 0), x = algebraMap _ _ p / algebraMap _ _ q := by
  constructor
  · rintro ⟨q, rfl⟩
    obtain ⟨_hx, hq⟩ := mul_ne_zero_iff.mp hp
    refine ⟨denom x * q, mul_ne_zero (denom_ne_zero x) hq, ?_⟩
    simp only [map_mul, mul_div_mul_right, num_div_denom]
  · rintro ⟨q, hq, rfl⟩
    exact num_div_dvd p hq

theorem denom_dvd {x : RatFunc K} {q : K[X]} (hq : q ≠ 0) :
    denom x ∣ q ↔ ∃ p : K[X], x = algebraMap _ _ p / algebraMap _ _ q := by
  constructor
  · rintro ⟨p, rfl⟩
    refine ⟨num x * p, ?_⟩
    simp only [map_mul, mul_div_mul_right, num_div_denom]
  · rintro ⟨p, rfl⟩
    exact denom_div_dvd p q

theorem num_mul_dvd (x y : RatFunc K) : num (x * y) ∣ num x * num y := by
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  rw [num_dvd (mul_ne_zero (num_ne_zero hx) (num_ne_zero hy))]
  refine ⟨x.denom * y.denom, mul_ne_zero (denom_ne_zero x) (denom_ne_zero y), ?_⟩
  conv_lhs => rw [← num_div_denom x, ← num_div_denom y, div_mul_div_comm₀]
  simp only [map_mul]

theorem denom_mul_dvd (x y : RatFunc K) : denom (x * y) ∣ denom x * denom y := by
  rw [denom_dvd (mul_ne_zero (denom_ne_zero x) (denom_ne_zero y))]
  refine ⟨x.num * y.num, ?_⟩
  conv_lhs => rw [← num_div_denom x, ← num_div_denom y, div_mul_div_comm₀]
  simp only [map_mul]

theorem denom_add_dvd (x y : RatFunc K) : denom (x + y) ∣ denom x * denom y := by
  rw [denom_dvd (mul_ne_zero (denom_ne_zero x) (denom_ne_zero y))]
  refine ⟨x.num * y.denom + x.denom * y.num, ?_⟩
  conv_lhs => rw [← num_div_denom x, ← num_div_denom y]
  rw [div_add_div]
  simp only [map_mul, map_add]

theorem num_inv_dvd {x : RatFunc K} (hx : x ≠ 0) : num x⁻¹ ∣ denom x := by
  rw [num_dvd x.denom_ne_zero]
  refine ⟨x.num, num_ne_zero hx, ?_⟩
  rw [eq_div_iff, div_eq_iff.mp (num_div_denom x), inv_mul_cancel_left₀]

theorem denom_inv_dvd {x : RatFunc K} (hx : x ≠ 0) : denom x⁻¹ ∣ num x := by
  rw [denom_dvd (num_ne_zero hx)]
  refine ⟨x.denom, ?_⟩
  rw [eq_div_iff, div_eq_iff.mp (num_div_denom x), inv_mul_cancel_left₀]

theorem associated_num_inv {x : RatFunc K} (hx : x ≠ 0) : Associated (num x⁻¹) (denom x) := by
  apply associated_of_dvd_dvd (num_inv_dvd hx)
  convert! denom_inv_dvd (x := x⁻¹) inv_ne_zero
  rw [inv_inv₀]

theorem associated_denom_inv {x : RatFunc K} (hx : x ≠ 0) : Associated (denom x⁻¹) (num x) := by
  apply Associated.symm
  convert! associated_num_inv (x := x⁻¹) inv_ne_zero
  rw [inv_inv₀]

theorem map_denom_ne_zero {L F : Type*} [Zero L] [FunLike F K[X] L] [ZeroHomClass F K[X] L]
    (φ : F) (hφ : Function.Injective φ) (f : RatFunc K) : φ f.denom ≠ 0 := fun H =>
  (denom_ne_zero f) ((map_eq_zero_iff φ hφ).mp H)

theorem map_apply {R F : Type*} [CommRing R] [IsDomain R]
    [FunLike F K[X] R[X]] [MonoidHomClass F K[X] R[X]] (φ : F)
    (hφ : K[X]⁰ ≤ R[X]⁰.comap φ) (f : RatFunc K) :
    map φ hφ f = Checked.div (algebraMap _ _ (φ f.num)) (algebraMap _ _ (φ f.denom))
      (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
        (hφ (mem_nonZeroDivisors_of_ne_zero f.denom_ne_zero))).isUnit := by
  conv_lhs => rw [← num_div_denom f]
  rw [map_apply_div]

theorem liftMonoidWithZeroHom_apply {L : Type*} [CommGroupWithZero L] (φ : K[X] →*₀ L)
    (hφ : K[X]⁰ ≤ L⁰.comap φ) (f : RatFunc K) :
    liftMonoidWithZeroHom φ hφ f = Checked.div (φ f.num) (φ f.denom)
      (nonZeroDivisors.ne_zero (hφ (mem_nonZeroDivisors_of_ne_zero f.denom_ne_zero))).isUnit := by
  conv_lhs => rw [← num_div_denom f]
  rw [liftMonoidWithZeroHom_apply_div]

theorem liftRingHom_apply {L : Type*} [Field L] (φ : K[X] →+* L) (hφ : K[X]⁰ ≤ L⁰.comap φ)
    (f : RatFunc K) : liftRingHom φ hφ f = Checked.div (φ f.num) (φ f.denom)
      (nonZeroDivisors.ne_zero (hφ (mem_nonZeroDivisors_of_ne_zero f.denom_ne_zero))).isUnit :=
  liftMonoidWithZeroHom_apply φ.toMonoidWithZeroHom hφ f

theorem liftAlgHom_apply {L S : Type*} [Field L] [CommSemiring S] [Algebra S K[X]] [Algebra S L]
    (φ : K[X] →ₐ[S] L) (hφ : K[X]⁰ ≤ L⁰.comap φ) (f : RatFunc K) :
    liftAlgHom φ hφ f = Checked.div (φ f.num) (φ f.denom)
      (nonZeroDivisors.ne_zero (hφ (mem_nonZeroDivisors_of_ne_zero f.denom_ne_zero))).isUnit :=
  liftMonoidWithZeroHom_apply φ.toRingHom.toMonoidWithZeroHom hφ f

theorem num_mul_denom_add_denom_mul_num_ne_zero {x y : RatFunc K} (hxy : x + y ≠ 0) :
    x.num * y.denom + x.denom * y.num ≠ 0 := by
  intro h_zero
  have h := num_denom_add x y
  rw [h_zero, zero_mul] at h
  exact (mul_ne_zero (num_ne_zero hxy) (mul_ne_zero x.denom_ne_zero y.denom_ne_zero)) h

end NumDenom

section Char

instance [Field K] {p : ℕ} [CharP K p] : CharP (RatFunc K) p :=
  charP_of_injective_algebraMap' K p

instance [Field K] {p : ℕ} [ExpChar K p] : ExpChar (RatFunc K) p :=
  ExpChar.of_injective_algebraMap' K p

instance [Field K] [CharZero K] : CharZero (RatFunc K) :=
  Algebra.charZero_of_charZero K _

end Char

end RatFunc
