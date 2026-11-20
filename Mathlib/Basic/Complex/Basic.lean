/-
Copyright (c) 2017 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Mario Carneiro
-/
module

public import Mathlib.Algebra.Ring.CharZero
public import Mathlib.Algebra.Ring.Torsion
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Set.UnorderedInterval
public import Mathlib.Tactic.Ring
public import Mathlib.Util.Qq

/-!
# The complex numbers

The complex numbers are modelled as ℝ^2 in the obvious way and it is shown that they form a field
of characteristic zero. For the result that the complex numbers are algebraically closed, see
`Complex.isAlgClosed` in `Mathlib.Analysis.Complex.Polynomial.Basic`.
-/

@[expose] public section

assert_not_exists Multiset Algebra

open Set Function

/-! ### Definition and basic arithmetic -/


/-- Complex numbers consist of two `Real`s: a real part `re` and an imaginary part `im`. -/
@[wikidata Q11567]
structure Complex : Type where
  /-- The real part of a complex number. -/
  re : ℝ
  /-- The imaginary part of a complex number. -/
  im : ℝ

@[inherit_doc] notation "ℂ" => Complex

namespace Complex

open scoped ComplexConjugate

noncomputable instance : DecidableEq ℂ :=
  Classical.decEq _

/-- The equivalence between the complex numbers and `ℝ × ℝ`. -/
@[simps apply]
def equivRealProd : ℂ ≃ ℝ × ℝ where
  toFun z := ⟨z.re, z.im⟩
  invFun p := ⟨p.1, p.2⟩

@[simp]
theorem eta : ∀ z : ℂ, Complex.mk z.re z.im = z
  | ⟨_, _⟩ => rfl

-- We only mark this lemma with `ext` *locally* to avoid it applying whenever terms of `ℂ` appear.
theorem ext : ∀ {z w : ℂ}, z.re = w.re → z.im = w.im → z = w
  | ⟨_, _⟩, ⟨_, _⟩, rfl, rfl => rfl

attribute [local ext] Complex.ext

lemma «forall» {p : ℂ → Prop} : (∀ x, p x) ↔ ∀ a b, p ⟨a, b⟩ := by aesop
lemma «exists» {p : ℂ → Prop} : (∃ x, p x) ↔ ∃ a b, p ⟨a, b⟩ := by aesop

theorem re_surjective : Surjective re := fun x => ⟨⟨x, 0⟩, rfl⟩

theorem im_surjective : Surjective im := fun y => ⟨⟨0, y⟩, rfl⟩

@[simp]
theorem range_re : range re = univ :=
  re_surjective.range_eq

@[simp]
theorem range_im : range im = univ :=
  im_surjective.range_eq

/-- The natural inclusion of the real numbers into the complex numbers. -/
@[coe, instance_reducible]
def ofReal (r : ℝ) : ℂ :=
  ⟨r, 0⟩
instance : Coe ℝ ℂ :=
  ⟨ofReal⟩

@[simp, norm_cast]
theorem ofReal_re (r : ℝ) : Complex.re (r : ℂ) = r :=
  rfl

@[simp, norm_cast]
theorem ofReal_im (r : ℝ) : (r : ℂ).im = 0 :=
  rfl

theorem ofReal_def (r : ℝ) : (r : ℂ) = ⟨r, 0⟩ :=
  rfl

@[simp, norm_cast]
theorem ofReal_inj {z w : ℝ} : (z : ℂ) = w ↔ z = w :=
  ⟨congrArg re, by apply congrArg⟩

theorem ofReal_injective : Function.Injective ((↑) : ℝ → ℂ) := fun _ _ => congrArg re

instance canLift : CanLift ℂ ℝ (↑) fun z => z.im = 0 where
  prf z hz := ⟨z.re, ext rfl hz.symm⟩

/-- The product of a set on the real axis and a set on the imaginary axis of the complex plane,
denoted by `s ×ℂ t`. -/
def reProdIm (s t : Set ℝ) : Set ℂ :=
  re ⁻¹' s ∩ im ⁻¹' t

@[inherit_doc]
infixl:72 " ×ℂ " => reProdIm

theorem mem_reProdIm {z : ℂ} {s t : Set ℝ} : z ∈ s ×ℂ t ↔ z.re ∈ s ∧ z.im ∈ t :=
  Iff.rfl

instance : Zero ℂ :=
  ⟨(0 : ℝ)⟩

instance : Inhabited ℂ :=
  ⟨0⟩

@[simp]
theorem zero_re : (0 : ℂ).re = 0 :=
  rfl

@[simp]
theorem zero_im : (0 : ℂ).im = 0 :=
  rfl

@[simp, norm_cast]
theorem ofReal_zero : ((0 : ℝ) : ℂ) = 0 :=
  rfl

@[simp]
theorem ofReal_eq_zero {z : ℝ} : (z : ℂ) = 0 ↔ z = 0 :=
  ofReal_inj

theorem ofReal_ne_zero {z : ℝ} : (z : ℂ) ≠ 0 ↔ z ≠ 0 :=
  not_congr ofReal_eq_zero

instance : One ℂ :=
  ⟨(1 : ℝ)⟩

@[simp]
theorem one_re : (1 : ℂ).re = 1 :=
  rfl

@[simp]
theorem one_im : (1 : ℂ).im = 0 :=
  rfl

@[simp, norm_cast]
theorem ofReal_one : ((1 : ℝ) : ℂ) = 1 :=
  rfl

@[simp]
theorem ofReal_eq_one {z : ℝ} : (z : ℂ) = 1 ↔ z = 1 :=
  ofReal_inj

theorem ofReal_ne_one {z : ℝ} : (z : ℂ) ≠ 1 ↔ z ≠ 1 :=
  not_congr ofReal_eq_one

instance : Add ℂ :=
  ⟨fun z w => ⟨z.re + w.re, z.im + w.im⟩⟩

@[simp]
theorem add_re (z w : ℂ) : (z + w).re = z.re + w.re :=
  rfl

@[simp]
theorem add_im (z w : ℂ) : (z + w).im = z.im + w.im :=
  rfl

@[simp, norm_cast]
theorem ofReal_add (r s : ℝ) : ((r + s : ℝ) : ℂ) = r + s :=
  Complex.ext_iff.2 <| by simp [ofReal]

instance : Neg ℂ :=
  ⟨fun z => ⟨-z.re, -z.im⟩⟩

@[simp]
theorem neg_re (z : ℂ) : (-z).re = -z.re :=
  rfl

@[simp]
theorem neg_im (z : ℂ) : (-z).im = -z.im :=
  rfl

@[simp, norm_cast]
theorem ofReal_neg (r : ℝ) : ((-r : ℝ) : ℂ) = -r :=
  Complex.ext_iff.2 <| by simp [ofReal]

instance : Sub ℂ :=
  ⟨fun z w => ⟨z.re - w.re, z.im - w.im⟩⟩

/--
`mulAux` is an auxiliary definition for defining multiplication and scalar multiplication on `ℂ`
in such a way that `real_smul {x : ℝ} {z : ℂ} : x • z = x * z` holds definitionally.
This makes sure that `Module.restrictScalars ℝ ℂ ℂ = Complex.instModule` definitionally.
-/
@[no_expose]
def mulAux {R : Type*} [SMul R ℝ] (re : R) (im : ℝ) (z : ℂ) : ℂ :=
  ⟨re • z.re - im * z.im, re • z.im + im * z.re⟩

instance : Mul ℂ :=
  ⟨fun z w => mulAux z.re z.im w⟩

theorem mk_mul_mk (x₁ x₂ y₁ y₂ : ℝ) :
    (⟨x₁, y₁⟩ : ℂ) * ⟨x₂, y₂⟩ = ⟨x₁ * x₂ - y₁ * y₂, x₁ * y₂ + y₁ * x₂⟩ := (rfl)

@[simp]
theorem mul_re (z w : ℂ) : (z * w).re = z.re * w.re - z.im * w.im :=
  (rfl)

@[simp]
theorem mul_im (z w : ℂ) : (z * w).im = z.re * w.im + z.im * w.re :=
  (rfl)

@[simp, norm_cast]
theorem ofReal_mul (r s : ℝ) : ((r * s : ℝ) : ℂ) = r * s :=
  Complex.ext_iff.2 <| by simp [ofReal]

theorem re_ofReal_mul (r : ℝ) (z : ℂ) : (r * z).re = r * z.re := by simp [ofReal]

theorem im_ofReal_mul (r : ℝ) (z : ℂ) : (r * z).im = r * z.im := by simp [ofReal]

lemma re_mul_ofReal (z : ℂ) (r : ℝ) : (z * r).re = z.re * r := by simp [ofReal]
lemma im_mul_ofReal (z : ℂ) (r : ℝ) : (z * r).im = z.im * r := by simp [ofReal]

theorem ofReal_mul' (r : ℝ) (z : ℂ) : ↑r * z = ⟨r * z.re, r * z.im⟩ :=
  ext (re_ofReal_mul _ _) (im_ofReal_mul _ _)

/-! ### The imaginary unit, `I` -/


/-- The imaginary unit. -/
def I : ℂ :=
  ⟨0, 1⟩

@[simp]
theorem I_re : I.re = 0 :=
  rfl

@[simp]
theorem I_im : I.im = 1 :=
  rfl

@[simp]
theorem I_mul_I : I * I = -1 :=
  Complex.ext_iff.2 <| by simp

theorem I_mul (z : ℂ) : I * z = ⟨-z.im, z.re⟩ :=
  Complex.ext_iff.2 <| by simp

@[simp] lemma I_ne_zero : (I : ℂ) ≠ 0 := mt (congr_arg im) zero_ne_one.symm

theorem mk_eq_add_mul_I (a b : ℝ) : Complex.mk a b = a + b * I :=
  Complex.ext_iff.2 <| by simp [ofReal]

@[simp]
theorem re_add_im (z : ℂ) : (z.re : ℂ) + z.im * I = z :=
  Complex.ext_iff.2 <| by simp [ofReal]

theorem mul_I_re (z : ℂ) : (z * I).re = -z.im := by simp

theorem mul_I_im (z : ℂ) : (z * I).im = z.re := by simp

theorem I_mul_re (z : ℂ) : (I * z).re = -z.im := by simp

theorem I_mul_im (z : ℂ) : (I * z).im = z.re := by simp

@[simp]
theorem equivRealProd_symm_apply (p : ℝ × ℝ) : equivRealProd.symm p = p.1 + p.2 * I := by
  ext <;> simp [Complex.equivRealProd, ofReal]

/-- The natural `AddEquiv` from `ℂ` to `ℝ × ℝ`. -/
@[simps! +simpRhs apply symm_apply_re symm_apply_im]
def equivRealProdAddHom : ℂ ≃+ ℝ × ℝ :=
  { equivRealProd with map_add' := by simp }

theorem equivRealProdAddHom_symm_apply (p : ℝ × ℝ) :
    equivRealProdAddHom.symm p = p.1 + p.2 * I := equivRealProd_symm_apply p

/-! ### Commutative ring instance and lemmas -/


/-- We use a nonstandard formula for the `ℕ` and `ℤ` actions to make sure there is no
diamond from the other actions they inherit through the `ℝ`-action on `ℂ` and action transitivity
defined in `Mathlib.LinearAlgebra.Complex.Module`. -/
instance : Nontrivial ℂ :=
  domain_nontrivial re rfl rfl

namespace SMul

-- instance made scoped to avoid situations like instance synthesis
-- of `SMul ℂ ℂ` trying to proceed via `SMul ℂ ℝ`.
/-- Scalar multiplication by `R` on `ℝ` extends to `ℂ`. This is used here and in
`Mathlib/LinearAlgebra/Complex/Module.lean` to transfer instances from `ℝ` to `ℂ`, but is not
needed outside, so we make it scoped. -/
scoped instance instSMulRealComplex {R : Type*} [SMul R ℝ] : SMul R ℂ where
  smul r x := mulAux r 0 x

end SMul

open scoped Complex.SMul

section SMul

variable {R : Type*} [SMul R ℝ]

theorem smul_re (r : R) (z : ℂ) : (r • z).re = r • z.re :=
  show r • z.re - 0 * z.im = r • z.re by simp

theorem smul_im (r : R) (z : ℂ) : (r • z).im = r • z.im :=
  show r • z.im + 0 * z.re = r • z.im by simp

@[simp]
theorem real_smul {x : ℝ} {z : ℂ} : x • z = x * z :=
  rfl

end SMul

instance addCommGroup : AddCommGroup ℂ where
  zsmul_zero' := by intros; ext <;> simp [smul_re, smul_im]
  nsmul_zero := by intros; ext <;> simp [smul_re, smul_im]
  nsmul_succ := by intros; ext <;> simp [smul_re, smul_im] <;> ring
  zsmul_succ' := by intros; ext <;> simp [smul_re, smul_im] <;> ring
  zsmul_neg' := by intros; ext <;> simp [smul_re, smul_im] <;> ring
  add_assoc := by intros; ext <;> simp <;> ring
  zero_add := by intros; ext <;> simp
  add_zero := by intros; ext <;> simp
  add_comm := by intros; ext <;> simp <;> ring
  neg_add_cancel := by intros; ext <;> simp

/-! ### Casts -/

instance instNatCast : NatCast ℂ where natCast n := ofReal n
instance instIntCast : IntCast ℂ where intCast n := ofReal n

@[simp, norm_cast] lemma ofReal_ofNat (n : ℕ) [n.AtLeastTwo] : ofReal ofNat(n) = ofNat(n) := rfl
@[simp, norm_cast] lemma ofReal_natCast (n : ℕ) : ofReal n = n := rfl
@[simp, norm_cast] lemma ofReal_intCast (n : ℤ) : ofReal n = n := rfl

@[simp] lemma re_ofNat (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : ℂ).re = ofNat(n) := rfl
@[simp] lemma im_ofNat (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : ℂ).im = 0 := rfl
@[simp, norm_cast] lemma natCast_re (n : ℕ) : (n : ℂ).re = n := rfl
@[simp, norm_cast] lemma natCast_im (n : ℕ) : (n : ℂ).im = 0 := rfl
@[simp, norm_cast] lemma intCast_re (n : ℤ) : (n : ℂ).re = n := rfl
@[simp, norm_cast] lemma intCast_im (n : ℤ) : (n : ℂ).im = 0 := rfl


/-! ### Ring structure -/

instance addGroupWithOne : AddGroupWithOne ℂ :=
  { Complex.addCommGroup with
    natCast_zero := by ext <;> simp
    natCast_succ _ := by ext <;> simp
    intCast_ofNat _ := by ext <;> simp
    intCast_negSucc _ := by ext <;> simp }

instance commRing : CommRing ℂ :=
  { addGroupWithOne with
    npow := @npowRec _ ⟨(1 : ℂ)⟩ ⟨(· * ·)⟩
    add_comm := by intros; ext <;> simp <;> ring
    left_distrib := by intros; ext <;> simp [mul_re, mul_im] <;> ring
    right_distrib := by intros; ext <;> simp [mul_re, mul_im] <;> ring
    zero_mul := by intros; ext <;> simp
    mul_zero := by intros; ext <;> simp
    mul_assoc := by intros; ext <;> simp <;> ring
    one_mul := by intros; ext <;> simp
    mul_one := by intros; ext <;> simp
    mul_comm := by intros; ext <;> simp <;> ring }

section computable_shortcuts

/-- This shortcut instance ensures we do not find `Ring` via the noncomputable
`Complex.instNormedField` instance. -/
instance : Ring ℂ :=
  delta% inferInstance

/-- This shortcut instance ensures we do not find `NonUnitalCommRing` via the noncomputable
`instCommCStarAlgebraComplex` instance. -/
instance : NonUnitalCommRing ℂ :=
  delta% inferInstance

/-- This shortcut instance ensures we do not find `CommSemiring` via the noncomputable
`Complex.instNormedField` instance. -/
instance : CommSemiring ℂ :=
  delta% inferInstance

/-- This shortcut instance ensures we do not find `Semiring` via the noncomputable
`Complex.instNormedField` instance. -/
instance : Semiring ℂ :=
  delta% inferInstance

/-- This shortcut instance ensures we do not find `AddCommMonoid` via the noncomputable
`Complex.instNormedField` instance. -/
instance : AddCommMonoid ℂ :=
  delta% inferInstance

end computable_shortcuts

/-- The "real part" map, considered as an additive group homomorphism. -/
def reAddGroupHom : ℂ →+ ℝ where
  toFun := re
  map_zero' := zero_re
  map_add' := add_re

@[simp]
theorem coe_reAddGroupHom : (reAddGroupHom : ℂ → ℝ) = re :=
  rfl

/-- The "imaginary part" map, considered as an additive group homomorphism. -/
def imAddGroupHom : ℂ →+ ℝ where
  toFun := im
  map_zero' := zero_im
  map_add' := add_im

@[simp]
theorem coe_imAddGroupHom : (imAddGroupHom : ℂ → ℝ) = im :=
  rfl

lemma re_nsmul (n : ℕ) (z : ℂ) : (n • z).re = n • z.re := smul_re ..
lemma im_nsmul (n : ℕ) (z : ℂ) : (n • z).im = n • z.im := smul_im ..
lemma re_zsmul (n : ℤ) (z : ℂ) : (n • z).re = n • z.re := smul_re ..
lemma im_zsmul (n : ℤ) (z : ℂ) : (n • z).im = n • z.im := smul_im ..
@[simp] lemma re_nnqsmul (q : ℚ≥0) (z : ℂ) : (q • z).re = q • z.re := smul_re ..
@[simp] lemma im_nnqsmul (q : ℚ≥0) (z : ℂ) : (q • z).im = q • z.im := smul_im ..
@[simp] lemma re_qsmul (q : ℚ) (z : ℂ) : (q • z).re = q • z.re := smul_re ..
@[simp] lemma im_qsmul (q : ℚ) (z : ℂ) : (q • z).im = q • z.im := smul_im ..

@[norm_cast] lemma ofReal_nsmul (n : ℕ) (r : ℝ) : ↑(n • r) = n • (r : ℂ) := by simp

@[norm_cast] lemma ofReal_zsmul (n : ℤ) (r : ℝ) : ↑(n • r) = n • (r : ℂ) := by simp

/-! ### Complex conjugation -/


/-- This defines the complex conjugate as the `star` operation of the `StarRing ℂ`. It
is recommended to use the ring endomorphism version `starRingEnd`, available under the
notation `conj` in the scope `ComplexConjugate`. -/
instance : StarRing ℂ where
  star z := ⟨z.re, -z.im⟩
  star_involutive x := by simp only [eta, neg_neg]
  star_mul a b := by ext <;> simp [add_comm] <;> ring
  star_add a b := by ext <;> simp [add_comm]

@[simp]
theorem conj_re (z : ℂ) : (conj z).re = z.re :=
  rfl

@[simp]
theorem conj_im (z : ℂ) : (conj z).im = -z.im :=
  rfl

@[simp]
theorem conj_ofReal (r : ℝ) : conj (r : ℂ) = r :=
  Complex.ext_iff.2 <| by simp

@[simp]
theorem conj_I : conj I = -I :=
  Complex.ext_iff.2 <| by simp

theorem conj_natCast (n : ℕ) : conj (n : ℂ) = n := map_natCast _ _

theorem conj_ofNat (n : ℕ) [n.AtLeastTwo] : conj (ofNat(n) : ℂ) = ofNat(n) :=
  map_ofNat _ _

theorem conj_neg_I : conj (-I) = I := by simp

theorem conj_eq_iff_real {z : ℂ} : conj z = z ↔ ∃ r : ℝ, z = r :=
  ⟨fun h => ⟨z.re, ext rfl <| eq_zero_of_neg_eq (congr_arg im h)⟩, fun ⟨h, e⟩ => by
    rw [e, conj_ofReal]⟩

theorem conj_eq_iff_re {z : ℂ} : conj z = z ↔ (z.re : ℂ) = z :=
  conj_eq_iff_real.trans ⟨by rintro ⟨r, rfl⟩; simp [ofReal], fun h => ⟨_, h.symm⟩⟩

theorem conj_eq_iff_im {z : ℂ} : conj z = z ↔ z.im = 0 :=
  ⟨fun h => add_self_eq_zero.mp (neg_eq_iff_add_eq_zero.mp (congr_arg im h)), fun h =>
    ext rfl (neg_eq_iff_add_eq_zero.mpr (add_self_eq_zero.mpr h))⟩

@[simp]
theorem star_def : (Star.star : ℂ → ℂ) = conj :=
  rfl

/-! ### Norm squared -/


/-- The norm squared function. -/
@[pp_nodot]
def normSq : ℂ →*₀ ℝ where
  toFun z := z.re * z.re + z.im * z.im
  map_zero' := by simp
  map_one' := by simp
  map_mul' z w := by
    simp only [mul_re, mul_im]
    ring

theorem normSq_apply (z : ℂ) : normSq z = z.re * z.re + z.im * z.im :=
  rfl

@[simp]
theorem normSq_ofReal (r : ℝ) : normSq r = r * r := by
  simp [normSq, ofReal]

@[simp]
theorem normSq_natCast (n : ℕ) : normSq n = n * n := normSq_ofReal _

@[simp]
theorem normSq_intCast (z : ℤ) : normSq z = z * z := normSq_ofReal _

@[simp]
theorem normSq_ofNat (n : ℕ) [n.AtLeastTwo] :
    normSq (ofNat(n) : ℂ) = ofNat(n) * ofNat(n) :=
  normSq_natCast _

@[simp]
theorem normSq_mk (x y : ℝ) : normSq ⟨x, y⟩ = x * x + y * y :=
  rfl

theorem normSq_add_mul_I (x y : ℝ) : normSq (x + y * I) = x ^ 2 + y ^ 2 := by
  rw [← mk_eq_add_mul_I, normSq_mk, sq, sq]

theorem normSq_eq_conj_mul_self {z : ℂ} : (normSq z : ℂ) = conj z * z := by
  ext <;> simp [normSq, mul_comm, ofReal]

theorem normSq_zero : normSq 0 = 0 := by simp

theorem normSq_one : normSq 1 = 1 := by simp

@[simp]
theorem normSq_I : normSq I = 1 := by simp [normSq]

theorem normSq_nonneg (z : ℂ) : 0 ≤ normSq z :=
  add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

theorem normSq_eq_zero {z : ℂ} : normSq z = 0 ↔ z = 0 :=
  ⟨fun h =>
    ext (eq_zero_of_mul_self_add_mul_self_eq_zero h)
      (eq_zero_of_mul_self_add_mul_self_eq_zero <| (add_comm _ _).trans h),
    fun h => h.symm ▸ normSq_zero⟩

@[simp]
theorem normSq_pos {z : ℂ} : 0 < normSq z ↔ z ≠ 0 :=
  (normSq_nonneg z).lt_iff_ne.trans <| not_congr (eq_comm.trans normSq_eq_zero)

@[simp]
theorem normSq_neg (z : ℂ) : normSq (-z) = normSq z := by simp [normSq]

@[simp]
theorem normSq_conj (z : ℂ) : normSq (conj z) = normSq z := by simp [normSq]

theorem normSq_mul (z w : ℂ) : normSq (z * w) = normSq z * normSq w :=
  normSq.map_mul z w

theorem normSq_add (z w : ℂ) : normSq (z + w) = normSq z + normSq w + 2 * (z * conj w).re := by
  simp [normSq]; ring

theorem re_sq_le_normSq (z : ℂ) : z.re * z.re ≤ normSq z :=
  le_add_of_nonneg_right (mul_self_nonneg _)

theorem im_sq_le_normSq (z : ℂ) : z.im * z.im ≤ normSq z :=
  le_add_of_nonneg_left (mul_self_nonneg _)

theorem mul_conj (z : ℂ) : z * conj z = normSq z :=
  Complex.ext_iff.2 <| by simp [normSq, mul_comm, sub_eq_neg_add, add_comm, ofReal]

theorem add_conj (z : ℂ) : z + conj z = (2 * z.re : ℝ) :=
  Complex.ext_iff.2 <| by simp [two_mul, ofReal]

/-- The coercion `ℝ → ℂ` as a `RingHom`. -/
@[instance_reducible]
def ofRealHom : ℝ →+* ℂ where
  toFun x := (x : ℂ)
  map_one' := ofReal_one
  map_zero' := ofReal_zero
  map_mul' := ofReal_mul
  map_add' := ofReal_add

@[simp] lemma ofRealHom_eq_coe (r : ℝ) : ofRealHom r = r := rfl

variable {α : Type*}

@[simp] lemma ofReal_comp_add (f g : α → ℝ) : ofReal ∘ (f + g) = ofReal ∘ f + ofReal ∘ g :=
  map_comp_add ofRealHom ..

@[simp] lemma ofReal_comp_sub (f g : α → ℝ) : ofReal ∘ (f - g) = ofReal ∘ f - ofReal ∘ g :=
  map_comp_sub ofRealHom ..

@[simp] lemma ofReal_comp_neg (f : α → ℝ) : ofReal ∘ (-f) = -(ofReal ∘ f) :=
  map_comp_neg ofRealHom _

lemma ofReal_comp_nsmul (n : ℕ) (f : α → ℝ) : ofReal ∘ (n • f) = n • (ofReal ∘ f) :=
  map_comp_nsmul ofRealHom ..

lemma ofReal_comp_zsmul (n : ℤ) (f : α → ℝ) : ofReal ∘ (n • f) = n • (ofReal ∘ f) :=
  map_comp_zsmul ofRealHom ..

@[simp] lemma ofReal_comp_mul (f g : α → ℝ) : ofReal ∘ (f * g) = ofReal ∘ f * ofReal ∘ g :=
  map_comp_mul ofRealHom ..

@[simp] lemma ofReal_comp_pow (f : α → ℝ) (n : ℕ) : ofReal ∘ (f ^ n) = (ofReal ∘ f) ^ n :=
  map_comp_pow ofRealHom ..

@[simp]
theorem I_sq : I ^ 2 = -1 := by rw [sq, I_mul_I]

@[simp]
lemma I_pow_three : I ^ 3 = -I := by rw [pow_succ, I_sq, neg_one_mul]

@[simp]
theorem I_pow_four : I ^ 4 = 1 := by rw [(by simp : 4 = 2 * 2), pow_mul, I_sq, neg_one_sq]

lemma I_pow_eq_pow_mod (n : ℕ) : I ^ n = I ^ (n % 4) := by
  conv_lhs => rw [← Nat.div_add_mod n 4]
  simp [pow_add, pow_mul, I_pow_four]

open Qq in
/-- Reduce `Complex.I ^ n` to `Complex.I ^ (n % 4)` when `n` is a literal natural number at
least `4`. Combined with `Nat.reduceMod` this normalises every literal power of `I` to one of
`I ^ 0`, `I ^ 1`, `I ^ 2`, `I ^ 3`, which the existing `@[simp]` lemmas dispatch. -/
simproc I_pow_eq_pow_mod' (I ^ _) := .ofQ fun u a e =>
  match u, a, e with
  | 1, ~q(ℂ), ~q(I ^ ($n : ℕ)) => do
    let some n' := n.nat? | return .continue
    if n' < 4 then return .continue
    -- we don't reduce `n % 4`, further, since `Nat.reduceMod` will handle that
    return .visit <| .mk q(I ^ ($n % 4)) <| .some q(I_pow_eq_pow_mod $n)
  | _, _, _ => return .continue

@[simp]
theorem sub_re (z w : ℂ) : (z - w).re = z.re - w.re :=
  rfl

@[simp]
theorem sub_im (z w : ℂ) : (z - w).im = z.im - w.im :=
  rfl

@[simp, norm_cast]
theorem ofReal_sub (r s : ℝ) : ((r - s : ℝ) : ℂ) = r - s :=
  Complex.ext_iff.2 <| by simp [ofReal]

@[simp, norm_cast]
theorem ofReal_pow (r : ℝ) (n : ℕ) : ((r ^ n : ℝ) : ℂ) = (r : ℂ) ^ n := by
  induction n <;> simp [*, ofReal_mul, pow_succ]

theorem sub_conj (z : ℂ) : z - conj z = (2 * z.im : ℝ) * I :=
  Complex.ext_iff.2 <| by simp [two_mul, sub_eq_add_neg, ofReal]

theorem normSq_sub (z w : ℂ) : normSq (z - w) = normSq z + normSq w - 2 * (z * conj w).re := by
  rw [sub_eq_add_neg, normSq_add]
  simp only [map_neg, mul_neg, neg_re, normSq_neg]
  ring

/-! ### Inversion -/


/-- Every nonzero complex number is a unit, using conjugation and its nonzero norm square. The
rational embeddings factor through `ℝ`, and the actions of `ℚ≥0` and `ℚ` are the componentwise
ones, so that they agree definitionally with `Complex.instModule`. -/
instance instField : Field ℂ where
  __ := commRing
  __ := (inferInstance : Nontrivial ℂ)
  isUnit_of_ne_zero {z} hz := by
    let u : ℝˣ := Units.mk0 (normSq z) (normSq_eq_zero.not.mpr hz)
    have h : z * (conj z * ((↑u⁻¹ : ℝ) : ℂ)) = 1 := by
      rw [← mul_assoc, mul_conj, ← ofReal_mul,
        show normSq z * (↑u⁻¹ : ℝ) = 1 from u.mul_inv, ofReal_one]
    exact ⟨⟨z, conj z * ((↑u⁻¹ : ℝ) : ℂ), h, by rw [mul_comm]; exact h⟩, rfl⟩
  nnratCastOfCharZero _ q := ((q : ℝ) : ℂ)
  nnratCastOfCharZero_mul_den _ q := by
    rw [← ofReal_natCast, ← ofReal_mul, NNRat.cast_mul_den, ofReal_natCast]
  ratCastOfCharZero _ q := ((q : ℝ) : ℂ)
  ratCastOfCharZero_mul_den _ q := by
    rw [← ofReal_natCast, ← ofReal_mul, Rat.cast_mul_den, ofReal_intCast]
  nnqsmulOfCharZero _ q z := q • z
  nnqsmulOfCharZero_eq_mul _ q z := by
    apply Complex.ext <;> simp [smul_re, smul_im, NNRat.smul_def]
  qsmulOfCharZero _ q z := q • z
  qsmulOfCharZero_eq_mul _ q z := by
    apply Complex.ext <;> simp [smul_re, smul_im, Rat.smul_def]

instance instCharZero : CharZero ℂ :=
  charZero_of_inj_zero fun n h => by rwa [← ofReal_natCast, ofReal_eq_zero, Nat.cast_eq_zero] at h

@[simp, norm_cast]
lemma ofReal_nnratCast (q : ℚ≥0) : ofReal q = q := map_nnratCast ofRealHom q

@[simp, norm_cast]
lemma ofReal_ratCast (q : ℚ) : ofReal q = q := map_ratCast ofRealHom q

@[simp, norm_cast]
lemma re_nnratCast (q : ℚ≥0) : (q : ℂ).re = q := by rw [← ofReal_nnratCast]; rfl

@[simp, norm_cast]
lemma im_nnratCast (q : ℚ≥0) : (q : ℂ).im = 0 := by rw [← ofReal_nnratCast]; rfl

@[simp, norm_cast]
lemma ratCast_re (q : ℚ) : (q : ℂ).re = q := by rw [← ofReal_ratCast]; rfl

@[simp, norm_cast]
lemma ratCast_im (q : ℚ) : (q : ℂ).im = 0 := by rw [← ofReal_ratCast]; rfl

@[simp]
theorem normSq_ratCast (q : ℚ) : normSq q = q * q := by
  rw [← ofReal_ratCast, normSq_ofReal]

@[simp, norm_cast]
lemma ofReal_ofScientific (m : ℕ) (s : Bool) (e : ℕ) :
    ofReal (OfScientific.ofScientific m s e : ℝ) = OfScientific.ofScientific m s e :=
  ofReal_nnratCast _

@[simp]
lemma re_ofScientific (m : ℕ) (s : Bool) (e : ℕ) :
    (OfScientific.ofScientific m s e : ℂ).re = OfScientific.ofScientific m s e := by
  rw [← ofReal_ofScientific]
  rfl

@[simp]
lemma im_ofScientific (m : ℕ) (s : Bool) (e : ℕ) :
    (OfScientific.ofScientific m s e : ℂ).im = 0 := by
  rw [← ofReal_ofScientific]
  rfl

/-! The evidence search `checked_nonzero` also uses that `I` is nonzero, and that the coercion of a
nonzero real number and the norm square of a nonzero complex number are nonzero. -/

macro_rules | `(tactic| checked_nonzero) => `(tactic|
    solve
    | assumption
    | (with_reducible exact Complex.I_ne_zero)
    | ((with_reducible apply Complex.ofReal_ne_zero.mpr); checked_nonzero)
    | ((with_reducible apply Complex.normSq_eq_zero.not.mpr); checked_nonzero))

theorem inv_def (z : ℂ) {hz : IsUnit z} : z⁻¹ = conj z * ((normSq z)⁻¹ : ℝ) :=
  inv_eq_of_mul_eq_one_right₀ <| by
    rw [← mul_assoc, mul_conj, ← ofReal_mul, mul_inv_cancel₀, ofReal_one]

@[simp]
theorem inv_re (z : ℂ) {hz : IsUnit z} : z⁻¹.re = z.re / normSq z := by
  simp [inv_def, div_eq_mul_inv₀]

@[simp]
theorem inv_im (z : ℂ) {hz : IsUnit z} : z⁻¹.im = -z.im / normSq z := by
  simp [inv_def, div_eq_mul_inv₀]

@[simp, norm_cast]
theorem ofReal_inv (r : ℝ) {hr : IsUnit r} : ((r⁻¹ : ℝ) : ℂ) = (r : ℂ)⁻¹ :=
  map_inv₀ ofRealHom r

lemma div_re (z w : ℂ) {hw : IsUnit w} :
    (z / w).re = z.re * w.re / normSq w + z.im * w.im / normSq w := by
  simp [div_eq_mul_inv₀, mul_assoc, sub_eq_add_neg]

lemma div_im (z w : ℂ) {hw : IsUnit w} :
    (z / w).im = z.im * w.re / normSq w - z.re * w.im / normSq w := by
  simp [div_eq_mul_inv₀, mul_assoc, sub_eq_add_neg, add_comm]

@[simp, norm_cast]
lemma ofReal_nnqsmul (q : ℚ≥0) (r : ℝ) : ofReal (q • r) = q • r :=
  Complex.ext_iff.2 <| by simp [ofReal]

@[simp, norm_cast]
lemma ofReal_qsmul (q : ℚ) (r : ℝ) : ofReal (q • r) = q • r := Complex.ext_iff.2 <| by simp [ofReal]

theorem conj_inv (x : ℂ) {hx : IsUnit x} : conj x⁻¹ = (conj x)⁻¹ :=
  star_inv₀ x

@[simp, norm_cast]
theorem ofReal_div (r s : ℝ) {hs : IsUnit s} : ((r / s : ℝ) : ℂ) = r / s :=
  map_div₀ ofRealHom r s

@[simp, norm_cast]
theorem ofReal_zpow (r : ℝ) (n : ℤ) {h : n < 0 → IsUnit r} :
    ((r ^ n : ℝ) : ℂ) = (r : ℂ) ^ n :=
  map_zpow₀ ofRealHom r n

@[simp]
theorem div_I (z : ℂ) : z / I = -(z * I) :=
  div_eq_iff_mul_eq.2 <| by simp [mul_assoc]

@[simp]
theorem inv_I : I⁻¹ = -I := by
  rw [inv_eq_one_div₀, div_I, one_mul]

lemma I_zpow_eq_zpow_mod (m : ℤ) : I ^ m = I ^ (m % 4) := by
  have hI : IsUnit I := I_ne_zero.isUnit
  have hfour : hI.unit ^ (4 : ℤ) = 1 := by
    rw [zpow_ofNat]
    exact Units.ext <| by simp
  rw [hI.zpow_eq_val_unit_zpow, hI.zpow_eq_val_unit_zpow, zpow_eq_zpow_emod m hfour]

open Qq in
/-- Reduce a literal integer power of `Complex.I` modulo four. -/
simproc I_zpow_eq_zpow_mod' (Checked.zpow I _ _) := .ofQ fun u a e =>
  match u, a, e with
  | 1, ~q(ℂ), ~q(Checked.zpow I $n $_hi) => do
    let some m ← Lean.Meta.getIntValue? n | return .continue
    if 0 ≤ m ∧ m < 4 then return .continue
    return .visit <| .mk q(Checked.zpow I ($n % 4) (fun _ ↦ I_ne_zero.isUnit)) <|
      .some q(I_zpow_eq_zpow_mod $n)
  | _, _, _ => return .continue

theorem normSq_inv (z : ℂ) {hz : IsUnit z} : normSq z⁻¹ = (normSq z)⁻¹ :=
  map_inv₀ normSq z

theorem normSq_div (z w : ℂ) {hw : IsUnit w} : normSq (z / w) = normSq z / normSq w :=
  map_div₀ normSq z w

lemma div_ofReal (z : ℂ) (x : ℝ) {hx : IsUnit (x : ℂ)} : z / x = ⟨z.re / x, z.im / x⟩ :=
  div_eq_iff_mul_eq.2 <| Complex.ext (by simp) (by simp)

lemma div_natCast (z : ℂ) (n : ℕ) {hn : IsUnit (n : ℂ)} : z / n = ⟨z.re / n, z.im / n⟩ :=
  div_ofReal z n

lemma div_intCast (z : ℂ) (n : ℤ) {hn : IsUnit (n : ℂ)} : z / n = ⟨z.re / n, z.im / n⟩ :=
  div_ofReal z n

lemma div_ratCast (z : ℂ) (x : ℚ) {hx : IsUnit (x : ℂ)} : z / x = ⟨z.re / x, z.im / x⟩ :=
  div_ofReal z x

lemma div_ofNat (z : ℂ) (n : ℕ) [n.AtLeastTwo] :
    z / ofNat(n) = ⟨z.re / ofNat(n), z.im / ofNat(n)⟩ :=
  div_natCast z n

@[simp] lemma div_ofReal_re (z : ℂ) (x : ℝ) {hx : IsUnit (x : ℂ)} : (z / x).re = z.re / x := by
  rw [div_ofReal]

@[simp] lemma div_ofReal_im (z : ℂ) (x : ℝ) {hx : IsUnit (x : ℂ)} : (z / x).im = z.im / x := by
  rw [div_ofReal]

@[simp] lemma div_natCast_re (z : ℂ) (n : ℕ) {hn : IsUnit (n : ℂ)} : (z / n).re = z.re / n := by
  rw [div_natCast]

@[simp] lemma div_natCast_im (z : ℂ) (n : ℕ) {hn : IsUnit (n : ℂ)} : (z / n).im = z.im / n := by
  rw [div_natCast]

@[simp] lemma div_intCast_re (z : ℂ) (n : ℤ) {hn : IsUnit (n : ℂ)} : (z / n).re = z.re / n := by
  rw [div_intCast]

@[simp] lemma div_intCast_im (z : ℂ) (n : ℤ) {hn : IsUnit (n : ℂ)} : (z / n).im = z.im / n := by
  rw [div_intCast]

@[simp] lemma div_ratCast_re (z : ℂ) (x : ℚ) {hx : IsUnit (x : ℂ)} : (z / x).re = z.re / x := by
  rw [div_ratCast]

@[simp] lemma div_ratCast_im (z : ℂ) (x : ℚ) {hx : IsUnit (x : ℂ)} : (z / x).im = z.im / x := by
  rw [div_ratCast]

@[simp]
lemma div_ofNat_re (z : ℂ) (n : ℕ) [n.AtLeastTwo] :
    (z / ofNat(n)).re = z.re / ofNat(n) := div_natCast_re z n

@[simp]
lemma div_ofNat_im (z : ℂ) (n : ℕ) [n.AtLeastTwo] :
    (z / ofNat(n)).im = z.im / ofNat(n) := div_natCast_im z n

/-! ### Characteristic zero -/


instance instIsAddTorsionFree : IsAddTorsionFree ℂ := IsDomain.instIsAddTorsionFreeOfCharZero _

/-- A complex number `z` plus its conjugate `conj z` is `2` times its real part. -/
theorem re_eq_add_conj (z : ℂ) : (z.re : ℂ) = (z + conj z) / 2 := by
  simp only [add_conj, ofReal_mul, ofReal_ofNat, mul_div_cancel_left₀ (z.re : ℂ)]

/-- A complex number `z` minus its conjugate `conj z` is `2i` times its imaginary part. -/
theorem im_eq_sub_conj (z : ℂ) : (z.im : ℂ) = (z - conj z) / (2 * I) := by
  simp only [sub_conj, ofReal_mul, ofReal_ofNat, mul_right_comm, mul_div_cancel_left₀]

/-- Show the imaginary number ⟨x, y⟩ as an `"x + y*I"` string

Note that the Real numbers used for x and y will show as Cauchy sequences due to the way Real
numbers are represented.
-/
unsafe instance instRepr : Repr ℂ where
  reprPrec f p :=
    (if p > 65 then (Std.Format.bracket "(" · ")") else (·)) <|
      reprPrec f.re 65 ++ " + " ++ reprPrec f.im 70 ++ "*I"

section reProdIm

/-- The preimage under `equivRealProd` of `s ×ˢ t` is `s ×ℂ t`. -/
lemma preimage_equivRealProd_prod (s t : Set ℝ) : equivRealProd ⁻¹' (s ×ˢ t) = s ×ℂ t := rfl

/-- The inequality `s × t ⊆ s₁ × t₁` holds in `ℂ` iff it holds in `ℝ × ℝ`. -/
lemma reProdIm_subset_iff {s s₁ t t₁ : Set ℝ} : s ×ℂ t ⊆ s₁ ×ℂ t₁ ↔ s ×ˢ t ⊆ s₁ ×ˢ t₁ := by
  rw [← @preimage_equivRealProd_prod s t, ← @preimage_equivRealProd_prod s₁ t₁]
  exact Equiv.preimage_subset equivRealProd _ _

/-- If `s ⊆ s₁ ⊆ ℝ` and `t ⊆ t₁ ⊆ ℝ`, then `s × t ⊆ s₁ × t₁` in `ℂ`. -/
lemma reProdIm_subset_iff' {s s₁ t t₁ : Set ℝ} :
    s ×ℂ t ⊆ s₁ ×ℂ t₁ ↔ s ⊆ s₁ ∧ t ⊆ t₁ ∨ s = ∅ ∨ t = ∅ := by
  convert! prod_subset_prod_iff
  exact reProdIm_subset_iff

variable {s t : Set ℝ}

@[simp] lemma reProdIm_nonempty : (s ×ℂ t).Nonempty ↔ s.Nonempty ∧ t.Nonempty := by
  simp [Set.Nonempty, reProdIm, Complex.exists]

@[simp] lemma reProdIm_eq_empty : s ×ℂ t = ∅ ↔ s = ∅ ∨ t = ∅ := by
  simp [← not_nonempty_iff_eq_empty, reProdIm_nonempty, -not_and, not_and_or]

end reProdIm

open scoped Interval

section Rectangle

/-- A `Rectangle` is an axis-parallel rectangle with corners `z` and `w`. -/
def Rectangle (z w : ℂ) : Set ℂ := [[z.re, w.re]] ×ℂ [[z.im, w.im]]

end Rectangle

section Segments

/-- A real segment `[a₁, a₂]` translated by `b * I` is the complex line segment. -/
lemma horizontalSegment_eq (a₁ a₂ b : ℝ) :
    (fun (x : ℝ) ↦ x + b * I) '' [[a₁, a₂]] = [[a₁, a₂]] ×ℂ {b} := by
  rw [← preimage_equivRealProd_prod]
  ext x
  constructor
  · intro hx
    obtain ⟨x₁, hx₁, hx₁'⟩ := hx
    simp [← hx₁', mem_preimage, mem_prod, hx₁]
  · intro hx
    obtain ⟨x₁, hx₁, hx₁', hx₁''⟩ := hx
    refine ⟨x.re, x₁, by simp⟩

/-- A vertical segment `[b₁, b₂]` translated by `a` is the complex line segment. -/
lemma verticalSegment_eq (a b₁ b₂ : ℝ) :
    (fun (y : ℝ) ↦ a + y * I) '' [[b₁, b₂]] = {a} ×ℂ [[b₁, b₂]] := by
  rw [← preimage_equivRealProd_prod]
  ext x
  constructor
  · intro hx
    obtain ⟨x₁, hx₁, hx₁'⟩ := hx
    simp [← hx₁', mem_preimage, mem_prod, hx₁]
  · intro hx
    simp only [equivRealProd_apply, singleton_prod, mem_image, Prod.mk.injEq,
      exists_eq_right_right, mem_preimage] at hx
    obtain ⟨x₁, hx₁, hx₁', hx₁''⟩ := hx
    refine ⟨x.im, x₁, by simp⟩

end Segments

end Complex
