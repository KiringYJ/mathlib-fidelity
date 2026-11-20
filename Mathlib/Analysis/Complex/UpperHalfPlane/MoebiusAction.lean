/-
Copyright (c) 2021 Alex Kontorovich and Heather Macbeth and Marc Masdeu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Heather Macbeth, Marc Masdeu
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective

/-!
# Group action on the upper half-plane

We equip the upper half-plane with the structure of a `GL (Fin 2) ℝ` action by fractional linear
transformations (composing with complex conjugation when needed to extend the action from the
positive-determinant subgroup, so that `!![-1, 0; 0, 1]` acts as `z ↦ -conj z`.)
-/

@[expose] public section

noncomputable section

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane
open scoped MatrixGroups ComplexConjugate

namespace UpperHalfPlane

/-- Numerator of the formula for a fractional linear transformation -/
def num (g : GL (Fin 2) ℝ) (z : ℂ) : ℂ := g 0 0 * z + g 0 1

/-- Denominator of the formula for a fractional linear transformation -/
def denom (g : GL (Fin 2) ℝ) (z : ℂ) : ℂ := g 1 0 * z + g 1 1

@[simp]
lemma num_neg (g : GL (Fin 2) ℝ) (z : ℂ) : num (-g) z = -(num g z) := by
  simp [num]; ring

@[simp]
lemma denom_neg (g : GL (Fin 2) ℝ) (z : ℂ) : denom (-g) z = -(denom g z) := by
  simp [denom]; ring

theorem linear_ne_zero_of_im {cd : Fin 2 → ℝ} {z : ℂ} (hz : z.im ≠ 0) (h : cd ≠ 0) :
    (cd 0 : ℂ) * z + cd 1 ≠ 0 := by
  contrapose h
  have : cd 0 = 0 := by
    -- we will need this twice
    apply_fun Complex.im at h
    simpa only [Complex.add_im, Complex.mul_im, Complex.ofReal_im, zero_mul, add_zero,
      Complex.zero_im, mul_eq_zero, hz, or_false] using! h
  simp only [this, zero_mul, Complex.ofReal_zero, zero_add, Complex.ofReal_eq_zero] at h
  ext i
  fin_cases i <;> assumption

theorem linear_ne_zero {cd : Fin 2 → ℝ} (τ : ℍ) (h : cd ≠ 0) :
    (cd 0 : ℂ) * τ + cd 1 ≠ 0 :=
  linear_ne_zero_of_im τ.im_ne_zero h

theorem denom_ne_zero_of_im (g : GL (Fin 2) ℝ) {z : ℂ} (hz : z.im ≠ 0) : denom g z ≠ 0 := by
  refine linear_ne_zero_of_im hz fun H ↦ g.det.ne_zero ?_
  simp [Matrix.det_fin_two, H]

@[simp]
theorem denom_ne_zero (g : GL (Fin 2) ℝ) (z : ℍ) : denom g z ≠ 0 :=
  denom_ne_zero_of_im g z.im_ne_zero

theorem isUnit_denom (g : GL (Fin 2) ℝ) (z : ℍ) : IsUnit (denom g z) :=
  (denom_ne_zero g z).isUnit

theorem normSq_denom_pos (g : GL (Fin 2) ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    0 < Complex.normSq (denom g z) :=
  Complex.normSq_pos.mpr (denom_ne_zero_of_im g hz)

theorem normSq_denom_ne_zero (g : GL (Fin 2) ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    Complex.normSq (denom g z) ≠ 0 :=
  ne_of_gt (normSq_denom_pos g hz)

lemma denom_cocycle (g h : GL (Fin 2) ℝ) {z : ℂ} {hh : IsUnit (denom h z)} :
    denom (g * h) z = denom g (num h z / denom h z) * denom h z := by
  change _ = ((g 1 0 : ℂ) * (num h z / denom h z) + (g 1 1 : ℂ)) * denom h z
  field_simp
  simp only [denom, Units.val_mul, mul_apply, Fin.sum_univ_succ, Finset.univ_unique,
    Fin.default_eq_zero, Finset.sum_singleton, Fin.succ_zero_eq_one, Complex.ofReal_add,
    Complex.ofReal_mul, num]
  ring

private lemma num_cocycle (g h : GL (Fin 2) ℝ) {z : ℂ} {hh : IsUnit (denom h z)} :
    num (g * h) z = num g (num h z / denom h z) * denom h z := by
  change _ = ((g 0 0 : ℂ) * (num h z / denom h z) + (g 0 1 : ℂ)) * denom h z
  field_simp
  simp only [denom, Units.val_mul, mul_apply, Fin.sum_univ_succ, Finset.univ_unique,
    Fin.default_eq_zero, Finset.sum_singleton, Fin.succ_zero_eq_one, Complex.ofReal_add,
    Complex.ofReal_mul, num]
  ring

lemma moebius_im (g : GL (Fin 2) ℝ) (z : ℂ) {hg : IsUnit (denom g z)} :
    (num g z / denom g z).im = Checked.div (g.det.val * z.im) (Complex.normSq (denom g z))
      (Complex.normSq_pos.mpr hg.ne_zero).ne'.isUnit := by
  simp only [num, denom, Complex.div_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero, Complex.add_re, Complex.mul_re, sub_zero, ← sub_div,
    GeneralLinearGroup.val_det_apply, g.1.det_fin_two]
  ring

/-- Automorphism of `ℂ`: the identity if `0 < det g` and conjugation otherwise. -/
noncomputable def σ (g : GL (Fin 2) ℝ) : ℂ ≃A[ℝ] ℂ :=
  if 0 < g.det.val then .refl ℝ ℂ else Complex.conjCAE

lemma σ_conj (g : GL (Fin 2) ℝ) (z : ℂ) : σ g (conj z) = conj (σ g z) := by
  simp only [σ]
  split_ifs <;> simp

@[simp]
lemma σ_ofReal (g : GL (Fin 2) ℝ) (y : ℝ) : σ g y = y := by
  simp only [σ]
  split_ifs <;> simp

lemma σ_num (g h : GL (Fin 2) ℝ) (z : ℂ) : σ g (num h z) = num h (σ g z) := by
  simp [num]

lemma σ_denom (g h : GL (Fin 2) ℝ) (z : ℂ) : σ g (denom h z) = denom h (σ g z) := by
  simp [denom]

@[simp]
lemma σ_neg (g : GL (Fin 2) ℝ) : σ (-g) = σ g := by
  simp [σ, det_neg]

@[simp]
lemma σ_sq (g : GL (Fin 2) ℝ) (z : ℂ) : σ g (σ g z) = z := by
  simp only [σ]
  split_ifs <;> simp

lemma σ_im_ne_zero {g z} : (σ g z).im ≠ 0 ↔ z.im ≠ 0 := by
  simp only [σ]
  split_ifs <;> simp

lemma σ_mul (g g' : GL (Fin 2) ℝ) (z : ℂ) : σ (g * g') z = σ g (σ g' z) := by
  simp only [σ, map_mul, Units.val_mul]
  rcases g.det_ne_zero.lt_or_gt with (h | h) <;>
  rcases g'.det_ne_zero.lt_or_gt with (h' | h')
  · simp [mul_pos_of_neg_of_neg h h', h.not_gt, h'.not_gt]
  · simp [(mul_neg_of_neg_of_pos h h').not_gt, h.not_gt, h']
  · simp [(mul_neg_of_pos_of_neg h h').not_gt, h, h'.not_gt]
  · simp [mul_pos h h', h, h']

lemma σ_mul_comm (g h : GL (Fin 2) ℝ) (z : ℂ) : σ g (σ h z) = σ h (σ g z) := by
  simp only [σ]
  split_ifs <;> simp

@[simp] lemma norm_σ (g : GL (Fin 2) ℝ) (z : ℂ) : ‖σ g z‖ = ‖z‖ := by
  simp only [σ]
  split_ifs <;> simp

/-- Fractional linear transformation, also known as the Moebius transformation -/
def smulAux' (g : GL (Fin 2) ℝ) (z : ℂ) (hg : IsUnit (denom g z) := by checked_unit) : ℂ :=
  σ g (num g z / denom g z)

lemma smulAux'_im (g : GL (Fin 2) ℝ) (z : ℂ) {hg : IsUnit (denom g z)} :
    (smulAux' g z hg).im = Checked.div (|g.det.val| * z.im) (Complex.normSq (denom g z))
      (Complex.normSq_pos.mpr hg.ne_zero).ne'.isUnit := by
  simp only [smulAux', σ]
  split_ifs with h <;>
  [rw [abs_of_pos h]; rw [abs_of_nonpos (not_lt.mp h)]] <;>
  simpa only [Complex.conjCAE_apply, Complex.star_def, Complex.conj_im,
     neg_mul, neg_div₀, neg_inj] using! moebius_im g z (hg := hg)

/-- Fractional linear transformation, also known as the Moebius transformation -/
def smulAux (g : GL (Fin 2) ℝ) (z : ℍ) : ℍ :=
  mk (smulAux' g z (isUnit_denom g z)) <| by
    rw [smulAux'_im]
    exact div_pos (mul_pos (abs_pos.mpr g.det.ne_zero) z.im_pos) (normSq_denom_pos _ z.im_ne_zero)

lemma denom_cocycle' (g h : GL (Fin 2) ℝ) (z : ℍ) :
    denom (g * h) z = σ h (denom g (smulAux h z)) * denom h z := by
  simpa only [smulAux, coe_mk, smulAux', σ_denom, σ_sq] using
    denom_cocycle g h (hh := isUnit_denom h z)

theorem mul_smul' (g h : GL (Fin 2) ℝ) (z : ℍ) :
    smulAux (g * h) z = smulAux g (smulAux h z) := by
  have him (u : ℂ) (hu : u.im ≠ 0) :
      (Checked.div (num h u) (denom h u) (denom_ne_zero_of_im h hu).isUnit).im ≠ 0 := by
    rw [moebius_im]
    exact div_ne_zero (mul_ne_zero h.det_ne_zero hu)
  have hcompose (u : ℂ) (hu : u.im ≠ 0) :
      Checked.div (num (g * h) u) (denom (g * h) u) (denom_ne_zero_of_im (g * h) hu).isUnit =
        let w := Checked.div (num h u) (denom h u) (denom_ne_zero_of_im h hu).isUnit
        Checked.div (num g w) (denom g w) (denom_ne_zero_of_im g (him u hu)).isUnit := by
    dsimp only
    rw [div_eq_div_iff, num_cocycle (hh := (denom_ne_zero_of_im h hu).isUnit),
      denom_cocycle (hh := (denom_ne_zero_of_im h hu).isUnit)]
    ring
  ext : 1
  simp only [smulAux, coe_mk, smulAux', map_div₀, σ_num, σ_denom, σ_mul]
  exact hcompose (σ g (σ h z)) (by simpa only [σ_im_ne_zero] using! z.im_ne_zero)

/-- Action of `GL (Fin 2) ℝ` on the upper half-plane, with `GL(2, ℝ)⁺` acting by Moebius
transformations in the usual way, extended to all of `GL (Fin 2) ℝ` using complex conjugation. -/
instance glAction : MulAction (GL (Fin 2) ℝ) ℍ where
  smul := smulAux
  one_smul z := by
    change smulAux 1 z = z
    simp [smulAux, smulAux', num, denom, σ]
  mul_smul := mul_smul'

lemma coe_smul (g : GL (Fin 2) ℝ) (z : ℍ) :
    ↑(g • z) = σ g (Checked.div (num g z) (denom g z) (isUnit_denom g z)) := rfl

lemma coe_smul_of_det_pos {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val) (z : ℍ) :
    ↑(g • z) = Checked.div (num g z) (denom g z) (isUnit_denom g z) := by
  rw [coe_smul, σ, ite_eq_left hg, ContinuousAlgEquiv.refl_apply]

lemma denom_cocycle_σ (g h : GL (Fin 2) ℝ) (z : ℍ) :
    denom (g * h) z = σ h (denom g ↑(h • z)) * denom h z :=
  denom_cocycle' g h z

lemma glPos_smul_def {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val) (z : ℍ) :
    g • z = ⟨Checked.div (num g z) (denom g z) (isUnit_denom g z),
      coe_smul_of_det_pos hg z ▸ (g • z).im_pos⟩ := by
  ext; simp [coe_smul_of_det_pos hg]

section GLAction
variable (g : GL (Fin 2) ℝ) (z : ℍ)

theorem re_smul : (g • z).re = (Checked.div (num g z) (denom g z) (isUnit_denom g z)).re := by
  change (smulAux' g z (isUnit_denom g z)).re = _
  simp +contextual [smulAux', σ, DFunLike.ite_apply, apply_ite, Complex.div_re]

theorem im_smul : (g • z).im = |(Checked.div (num g z) (denom g z) (isUnit_denom g z)).im| := by
  change (smulAux' g z (isUnit_denom g z)).im = _
  simp only [smulAux', σ, DFunLike.ite_apply, ContinuousAlgEquiv.refl_apply, apply_ite, moebius_im,
     Complex.conjCAE_apply, Complex.conj_im, ← neg_div₀, ← neg_mul, abs_div, abs_mul,
    abs_of_pos (show 0 < (z : ℂ).im from z.coe_im ▸ z.im_pos),
    abs_of_nonneg <| Complex.normSq_nonneg _]
  split_ifs with h <;> [rw [abs_of_pos h]; rw [abs_of_nonpos (not_lt.mp h)]]

lemma im_smul_eq_div_normSq : (g • z).im =
    Checked.div (|g.det.val| * z.im) (Complex.normSq (denom g z))
      (normSq_denom_ne_zero g z.im_ne_zero).isUnit :=
  smulAux'_im g z (hg := isUnit_denom g z)

theorem c_mul_im_sq_le_normSq_denom : (g 1 0 * z.im) ^ 2 ≤ Complex.normSq (denom g z) := by
  set c := g 1 0
  set d := g 1 1
  calc
    (c * z.im) ^ 2 ≤ (c * z.im) ^ 2 + (c * z.re + d) ^ 2 := by nlinarith
    _ = Complex.normSq (denom g z) := by simp [denom, Complex.normSq]; ring

@[simp]
theorem neg_smul : -g • z = g • z := by
  ext1
  simp [coe_smul, neg_div_neg_eq₀]

@[simp]
lemma num_one : num 1 z = z := by simp [num]

@[simp]
lemma denom_one : denom 1 z = 1 := by
  simp [denom]

@[simp]
theorem num_scalar (u : ℝˣ) (z : ℍ) : num (.scalar (Fin 2) u) z = u * z := by
  simp [num]

@[simp]
theorem denom_scalar (u : ℝˣ) (z : ℍ) : denom (.scalar (Fin 2) u) z = u := by
  simp [denom]

@[simp]
theorem glScalar_smul (u : ℝˣ) (z : ℍ) :
    GeneralLinearGroup.scalar (Fin 2) u • z = z := by
  rw [glPos_smul_def]
  · simp
  · simp [sq_pos_iff]

instance : MulAction.IsPretransitive (GL (Fin 2) ℝ) ℍ where
  exists_smul_eq z w := by
    set m : Matrix (Fin 2) (Fin 2) ℝ := !![w.im, z.im * w.re - w.im * z.re; 0, z.im]
    refine ⟨.mkOfDetNeZero m <| by simp [m, im_ne_zero], ?_⟩
    ext
    simp [coe_smul_of_det_pos, im_pos, num, denom, m, Complex.ext_iff]

end GLAction

section PGLAction

instance : MulAction PGL(2, ℝ) ℍ :=
  Matrix.ProjGenLinGroup.mulActionOfGL glScalar_smul

@[simp]
theorem pglMk_smul (g : GL (Fin 2) ℝ) (z : ℍ) :
    ProjGenLinGroup.mk g • z = g • z :=
  ProjGenLinGroup.mk_smul ..

instance : MulAction.IsPretransitive PGL(2, ℝ) ℍ :=
  .of_smul_eq .mk <| pglMk_smul _ _

end PGLAction

section SLAction

noncomputable instance SLAction {R : Type*} [CommRing R] [Algebra R ℝ] : MulAction SL(2, R) ℍ :=
  MulAction.compHom ℍ <| SpecialLinearGroup.mapGL ℝ

private theorem isUnit_sl_denom {R : Type*} [CommRing R] [Algebra R ℝ]
    (g : SL(2, R)) (z : ℍ) :
    IsUnit ((algebraMap R ℝ (g 1 0) : ℂ) * (z : ℂ) + (algebraMap R ℝ (g 1 1) : ℂ)) :=
  isUnit_denom (SpecialLinearGroup.mapGL ℝ g) z

theorem coe_specialLinearGroup_apply {R : Type*} [CommRing R] [Algebra R ℝ] (g : SL(2, R)) (z : ℍ) :
    ↑(g • z) =
      Checked.div ((algebraMap R ℝ (g 0 0) : ℂ) * z + (algebraMap R ℝ (g 0 1) : ℂ))
        ((algebraMap R ℝ (g 1 0) : ℂ) * z + (algebraMap R ℝ (g 1 1) : ℂ))
        (by exact isUnit_sl_denom g z) := by
  rw [MulAction.compHom_smul_def, coe_smul_of_det_pos (by simp)]
  rfl

theorem specialLinearGroup_apply {R : Type*} [CommRing R] [Algebra R ℝ] (g : SL(2, R)) (z : ℍ) :
    g • z = mk
      (Checked.div ((algebraMap R ℝ (g 0 0) : ℂ) * z + (algebraMap R ℝ (g 0 1) : ℂ))
        ((algebraMap R ℝ (g 1 0) : ℂ) * z + (algebraMap R ℝ (g 1 1) : ℂ))
        (by exact isUnit_sl_denom g z))
      (by
        have hp : 0 < (↑(g • z) : ℂ).im := (g • z).im_pos
        exact coe_specialLinearGroup_apply g z ▸ hp) := by
  ext; simp [coe_specialLinearGroup_apply]

/-! these next few lemmas are *not* flagged `@simp` because of the constructors on the RHS;
instead we use the versions with coercions to `ℂ` as simp lemmas instead. -/

theorem modular_S_smul (z : ℍ) :
    ModularGroup.S • z = mk (Checked.inv (-z : ℂ) z.ne_zero.isUnit.neg) z.im_inv_neg_coe_pos := by
  rw [specialLinearGroup_apply]
  simp [ModularGroup.S, neg_div₀, inv_neg₀, one_div₀]

theorem modular_T_zpow_smul (z : ℍ) (n : ℤ) : ModularGroup.T ^ n • z = (n : ℝ) +ᵥ z := by
  rw [UpperHalfPlane.ext_iff, coe_vadd, add_comm, coe_specialLinearGroup_apply]
  simp [ModularGroup.coe_T_zpow,
    of_apply, cons_val_zero, Complex.ofReal_one, one_mul, cons_val_one,
    zero_mul, zero_add, div_one₀]

theorem modular_T_smul (z : ℍ) : ModularGroup.T • z = (1 : ℝ) +ᵥ z := by
  simpa only [zpow_one, Int.cast_one] using modular_T_zpow_smul z 1

set_option backward.isDefEq.respectTransparency false in
theorem exists_SL2_smul_eq_of_apply_zero_one_eq_zero (g : SL(2, ℝ)) (hc : g 1 0 = 0) :
    ∃ (u : { x : ℝ // 0 < x }) (v : ℝ), (g • · : ℍ → ℍ) = (v +ᵥ ·) ∘ (u • ·) := by
  obtain ⟨a, b, ha, rfl⟩ := g.fin_two_exists_eq_mk_of_apply_zero_one_eq_zero hc
  refine ⟨⟨_, mul_self_pos.mpr ha⟩, b * a, ?_⟩
  ext1 ⟨z, hz⟩; ext1
  have ha' := (Complex.ofReal_ne_zero.mpr ha).isUnit
  suffices ↑a * z * a + b * a = b * a + a * a * z by
    simpa [specialLinearGroup_apply, add_mul, div_inv_eq_mul₀]
  ring

set_option backward.isDefEq.respectTransparency false in
theorem exists_SL2_smul_eq_of_apply_zero_one_ne_zero (g : SL(2, ℝ)) (hc : g 1 0 ≠ 0) :
    ∃ (u : { x : ℝ // 0 < x }) (v w : ℝ),
      (g • · : ℍ → ℍ) =
        (w +ᵥ ·) ∘ (ModularGroup.S • · : ℍ → ℍ) ∘ (v +ᵥ · : ℍ → ℍ) ∘ (u • · : ℍ → ℍ) := by
  have h_denom (z : ℍ) := denom_ne_zero g z
  induction g using Matrix.SpecialLinearGroup.fin_two_induction with | _ a b c d h => ?_
  replace hc : c ≠ 0 := by simpa using! hc
  refine ⟨⟨_, mul_self_pos.mpr hc⟩, c * d, a / c, ?_⟩
  ext1 ⟨z, hz⟩; ext1
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have hd' : ↑c * z + d ≠ 0 := by simpa [denom] using h_denom ⟨z, hz⟩
  have hq : IsUnit (c * d + ↑c * ↑c * z : ℂ) := by
    convert hc'.isUnit.mul hd'.isUnit using 1
    ring
  suffices (↑a * z + b) / (↑c * z + d) = a / c - (c * d + ↑c * ↑c * z)⁻¹ by
    simpa [modular_S_smul, coe_specialLinearGroup_apply]
  replace h : (a * d - b * c : ℂ) = (1 : ℂ) := by norm_cast
  have hp : IsUnit ((c : ℂ) * ((c : ℂ) * z + d)) := hc'.isUnit.mul hd'.isUnit
  have heq : (c * d + ↑c * ↑c * z : ℂ) = (c : ℂ) * ((c : ℂ) * z + d) := by ring
  have hinv : (c * d + ↑c * ↑c * z : ℂ)⁻¹ * ((c : ℂ) * ((c : ℂ) * z + d)) = 1 := by
    rw [← heq, inv_mul_cancel₀]
  apply mul_right_cancel₀ hp.ne_zero
  calc
    _ = (↑a * z + b) * (c : ℂ) := by
      rw [← mul_assoc, div_mul_eq_mul_div₀, div_mul_cancel₀]
    _ = (a : ℂ) * ((c : ℂ) * z + d) - 1 := by linear_combination -h
    _ = _ := by rw [sub_mul, hinv, ← mul_assoc, div_mul_cancel₀]

end SLAction

section toSL2R

private theorem sqrt_im_isUnit (z : ℍ) : IsUnit (√z.im) :=
  (Real.sqrt_ne_zero'.mpr z.im_pos).isUnit

/-- Map from `ℍ` to `SL(2, ℝ)`, giving a continuous section of the map `g ↦ g • I`. -/
noncomputable def toSL2R (z : ℍ) : SL(2, ℝ) :=
  ⟨!![√z.im, Checked.div z.re (√z.im) (by exact sqrt_im_isUnit z);
      0, Checked.div 1 (√z.im) (by exact sqrt_im_isUnit z)], by simp [one_div₀]⟩

lemma toSL2R_apply (z : ℍ) : z.toSL2R =
    ⟨!![√z.im, Checked.div z.re (√z.im) (by exact sqrt_im_isUnit z);
        0, Checked.div 1 (√z.im) (by exact sqrt_im_isUnit z)], by simp [one_div₀]⟩ := rfl

@[simp] lemma coe_toSL2R (z : ℍ) : z.toSL2R =
    !![√z.im, Checked.div z.re (√z.im) (by exact sqrt_im_isUnit z);
       0, Checked.div 1 (√z.im) (by exact sqrt_im_isUnit z)] := rfl

@[simp] lemma toSL2R_smul_I (z : ℍ) : z.toSL2R • I = z := by
  have : √z.im ≠ (0 : ℂ) := by simpa [Real.sqrt_ne_zero'] using z.im_pos
  ext
  suffices z.re / √z.im + √z.im * Complex.I = z * (↑√z.im)⁻¹ by
    rw [coe_specialLinearGroup_apply, div_eq_iff]
    simpa [add_comm]
  rw [div_add' (hc := this.isUnit), mul_right_comm, ← Complex.ofReal_mul,
    ← Real.sqrt_mul z.im_pos.le, Real.sqrt_mul_self z.im_pos.le, re_add_im, div_eq_mul_inv₀]

/-- `SL(2, ℝ)` acts transitively on the upper half-plane. -/
instance isPretransitiveSL2R : MulAction.IsPretransitive SL(2, ℝ) ℍ :=
  .of_orbit fun z ↦ ⟨_, toSL2R_smul_I z⟩

/-- `GL(2, ℝ)` acts transitively on the upper half-plane. -/
instance isPretransitiveGL2R : MulAction.IsPretransitive (GL (Fin 2) ℝ) ℍ :=
  .of_smul_eq ((↑) : SL(2, ℝ) → _) fun {g z} ↦ (MulAction.compHom_smul_def _ g z).symm

end toSL2R

section J

/-- The matrix `[-1, 0; 0, 1]`, which defines an anti-holomorphic involution of `ℍ` via
`τ ↦ -conj τ`. -/
def J : GL (Fin 2) ℝ := .mkOfDetNeZero !![-1, 0; 0, 1] (by simp)

lemma coe_J_smul (τ : ℍ) : (↑(J • τ) : ℂ) = -conj ↑τ := by
  simp [UpperHalfPlane.coe_smul, σ, J, show ¬(1 : ℝ) < 0 by simp, num, denom]

@[simp] lemma val_J : J.val = !![-1, 0; 0, 1] := rfl

@[simp] lemma J_sq : J ^ 2 = 1 := by ext; simp [J, sq, Matrix.one_fin_two]

@[simp] lemma det_J : J.det = -1 := by ext; simp [J]

@[simp] lemma sigma_J : σ J = Complex.conjCAE := by simp [σ, J]

@[simp] lemma denom_J (τ : ℂ) : denom J τ = 1 := by simp [J, denom]

@[simp]
lemma denom_J_mul (g : GL (Fin 2) ℝ) (τ : ℂ) : denom (J * g) τ = denom g τ := by
  simp [denom, vecMul, vecHead, vecTail]

end J

end UpperHalfPlane

namespace ModularGroup -- results specific to `SL(2, ℤ)`
-- TODO: Move these elsewhere, maybe somewhere in the algebra or number theory hierarchies?

section ModularScalarTowers

/-- Canonical embedding of `SL(2, ℤ)` into `GL(2, ℝ)⁺`. -/
@[deprecated "use GL(2, ℝ)" (since := "2026-04-29")]
def coe (g : SL(2, ℤ)) : GL(2, ℝ)⁺ := ((g : SL(2, ℝ)) : GL(2, ℝ)⁺)

@[deprecated "use GL(2, ℝ)" (since := "2026-04-29")]
lemma coe_inj (a b : SL(2, ℤ)) : coe a = coe b ↔ a = b := by
  refine ⟨fun h ↦ a.ext b fun i j ↦ ?_, congr_arg _⟩
  simp only [Subtype.ext_iff, GeneralLinearGroup.ext_iff] at h
  simpa [coe] using h i j

/-- Canonical embedding of `SL(2, ℤ)` into `GL(2, ℝ)⁺`, bundled as a group hom. -/
@[deprecated "use GL(2, ℝ)" (since := "2026-04-29")]
def coeHom : SL(2, ℤ) →* GL(2, ℝ)⁺ := toGLPos.comp <| map <| Int.castRingHom _

@[deprecated "use GL(2, ℝ)" (since := "2026-04-29")]
lemma coeHom_apply (g : SL(2, ℤ)) : coeHom g = coe g := rfl

@[deprecated "use GL(2, ℝ)" (since := "2026-04-29")]
theorem coe_apply_complex {g : SL(2, ℤ)} {i j : Fin 2} :
    (Units.val <| Subtype.val <| coe g) i j = (Subtype.val g i j : ℂ) :=
  rfl

@[deprecated "use GL(2, ℝ)" (since := "2026-04-29")]
theorem det_coe {g : SL(2, ℤ)} : det (Units.val <| Subtype.val <| coe g) = 1 := by
  simp only [SpecialLinearGroup.coe_GLPos_coe_GL_coe_matrix, SpecialLinearGroup.det_coe, coe]

@[deprecated "use GL(2, ℝ)" (since := "2026-04-29")]
lemma coe_one : coe 1 = 1 := by
  simp only [coe, map_one]

/-- Multiplication action of `SL(2, ℤ)` on `GL(2, ℝ)⁺`. -/
@[reducible, deprecated "use GL(2, ℝ)" (since := "2026-04-29")]
def SLOnGLPos : SMul SL(2, ℤ) GL(2, ℝ)⁺ :=
  ⟨fun s g => s * g⟩

attribute [local instance] SLOnGLPos

@[deprecated "use GL(2, ℝ)" (since := "2026-04-29")]
theorem SLOnGLPos_smul_apply (s : SL(2, ℤ)) (g : GL(2, ℝ)⁺) (z : ℍ) :
    (s • g) • z = ((s : GL(2, ℝ)⁺) * g) • z :=
  rfl

@[deprecated "use GL(2, ℝ)" (since := "2026-04-29")]
lemma SL_to_GL_tower : IsScalarTower SL(2, ℤ) GL(2, ℝ)⁺ ℍ where
  smul_assoc s g z := by
    simp only [SLOnGLPos_smul_apply]
    apply mul_smul'

end ModularScalarTowers

section SLModularAction

variable (g : SL(2, ℤ)) (z : ℍ)

@[simp]
theorem sl_moeb : g • z = (g : GL (Fin 2) ℝ) • z := rfl

@[simp high]
theorem SL_neg_smul : -g • z = g • z := by
  rw [sl_moeb, ← z.neg_smul]
  congr 1 with i j
  simp [toGL]

theorem im_smul_eq_div_normSq : (g • z).im = z.im / Complex.normSq (denom g z) := by
  simpa using z.im_smul_eq_div_normSq g

theorem denom_apply : denom g z = g 1 0 * z + g 1 1 := rfl

set_option backward.isDefEq.respectTransparency false in
@[simp] lemma denom_S : denom S z = z := by simp [S, denom_apply]

end SLModularAction

end ModularGroup
