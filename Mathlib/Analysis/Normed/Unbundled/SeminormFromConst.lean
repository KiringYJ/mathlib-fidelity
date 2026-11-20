/-
Copyright (c) 2024 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
module

public import Mathlib.Analysis.Normed.Unbundled.AlgebraNorm
public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm

/-!
# SeminormFromConst


In this file, we prove [BGR, Proposition 1.3.2/2][bosch-guntzer-remmert]. Starting from a
power-multiplicative seminorm `f` on a commutative ring `R` and an element `c` with `f c ≠ 0`, we
create a new power-multiplicative seminorm for which `c` is multiplicative.

## Main Definitions

* `seminormFromConst'` : the real-valued function sending `x ∈ R` to the limit of
  `(f (x * c^n))/((f c)^n)`.
* `seminormFromConst` : the function `seminormFromConst'` as a `RingSeminorm` on `R`.


## Main Results
* `seminormFromConst_isNonarchimedean` : the function `seminormFromConst' c f hc`
  is nonarchimedean when `f` is nonarchimedean.
* `seminormFromConst_isPowMul` : the function `seminormFromConst' c f hc`
  is power-multiplicative.
* `seminormFromConst_const_mul` : for every `x : R`, `seminormFromConst' c f hc (c * x)`
  equals the product `seminormFromConst' c f hc c * seminormFromConst' c f hc x`.

## References
* [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert]

## Tags

SeminormFromConst, Seminorm, Nonarchimedean
-/

@[expose] public section

noncomputable section

open Filter

open scoped Topology

section Ring

variable {R : Type*} [CommRing R] (c : R) (f : RingSeminorm R)
variable (hc : f c ≠ 0)

/-- For a ring seminorm `f` and an element `c` with `f c ≠ 0`, the sequence
given by `(f (x * c^n))/((f c)^n)`. -/
def seminormFromConst_seq (x : R) : ℕ → ℝ := fun n ↦
  Checked.div (f (x * c ^ n)) (f c ^ n) (pow_ne_zero n hc).isUnit

lemma seminormFromConst_seq_def (x : R) :
    seminormFromConst_seq c f hc x = fun n ↦
      Checked.div (f (x * c ^ n)) (f c ^ n) (pow_ne_zero n hc).isUnit := rfl

/-- The terms in the normalized sequence are nonnegative. -/
theorem seminormFromConst_seq_nonneg (x : R) : 0 ≤ seminormFromConst_seq c f hc x :=
  fun n ↦ div_nonneg (apply_nonneg f (x * c ^ n)) (pow_nonneg (apply_nonneg f c) n)

/-- The image of `seminormFromConst_seq c f x` is bounded below by zero. -/
theorem seminormFromConst_bddBelow (x : R) :
    BddBelow (Set.range (seminormFromConst_seq c f hc x)) := by
  use 0
  rintro r ⟨n, rfl⟩
  exact seminormFromConst_seq_nonneg c f hc x n

variable {f}

/-- The normalized sequence at zero is the constant sequence zero. -/
theorem seminormFromConst_seq_zero (hf : f 0 = 0) : seminormFromConst_seq c f hc 0 = 0 := by
  rw [seminormFromConst_seq_def]
  ext n
  rw [zero_mul, hf, zero_div, Pi.zero_apply]

variable {c}
variable (hpm : IsPowMul f)
include hpm hc

/-- Every term of positive index of the normalized sequence at one is one. -/
theorem seminormFromConst_seq_one (n : ℕ) (hn : 1 ≤ n) : seminormFromConst_seq c f hc 1 n = 1 := by
  simp only [seminormFromConst_seq, one_mul, hpm _ hn, div_self]

/-- The normalized sequence is antitone. -/
theorem seminormFromConst_seq_antitone (x : R) : Antitone (seminormFromConst_seq c f hc x) := by
  intro m n hmn
  rcases hmn.eq_or_lt with rfl | hlt
  · exact le_rfl
  have hc_pos : 0 < f c := lt_of_le_of_ne (apply_nonneg f _) hc.symm
  have h1 : 1 ≤ n - m := Nat.one_le_iff_ne_zero.mpr (Nat.sub_ne_zero_of_lt hlt)
  have hnum : f (x * c ^ n) ≤ f (x * c ^ m) * f c ^ (n - m) := by
    rw [← hpm c h1]
    simpa only [mul_assoc, ← pow_add, Nat.add_sub_of_le hmn] using
      map_mul_le_mul f (x * c ^ m) (c ^ (n - m))
  simp only [seminormFromConst_seq, div_le_div_iff₀ (pow_pos hc_pos n) (pow_pos hc_pos m)]
  calc
    _ ≤ (f (x * c ^ m) * f c ^ (n - m)) * f c ^ m :=
      mul_le_mul_of_nonneg_right hnum (pow_nonneg hc_pos.le _)
    _ = _ := by rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hmn]

/-- The real-valued function sending `x ∈ R` to the limit of `(f (x * c^n))/((f c)^n)`. -/
def seminormFromConst' (c : R) (f : RingSeminorm R) (hc : f c ≠ 0) (x : R) : ℝ :=
  iInf (seminormFromConst_seq c f hc x)

/-- The infimum of the normalized sequence is its limit at infinity. -/
theorem tendsto_seminormFromConst_seq_atTop (x : R) :
    Tendsto (seminormFromConst_seq c f hc x) atTop (𝓝 (seminormFromConst' c f hc x)) :=
  tendsto_atTop_ciInf (seminormFromConst_seq_antitone hc hpm x)
    (seminormFromConst_bddBelow c f hc x)

theorem seminormFromConst_one : seminormFromConst' c f hc 1 = 1 := by
  apply tendsto_nhds_unique_of_eventuallyEq (tendsto_seminormFromConst_seq_atTop hc hpm 1)
    tendsto_const_nhds
  simp only [EventuallyEq, eventually_atTop]
  exact ⟨1, seminormFromConst_seq_one hc hpm⟩

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- The function `seminormFromConst` is a `RingSeminorm` on `R`. -/
def seminormFromConst : RingSeminorm R where
  toFun     := seminormFromConst' c f hc
  map_zero' := tendsto_nhds_unique (tendsto_seminormFromConst_seq_atTop hc hpm 0)
    (by simpa [seminormFromConst_seq_zero c hc (map_zero _)] using! tendsto_const_nhds)
  add_le' x y := by
    apply le_of_tendsto_of_tendsto' (tendsto_seminormFromConst_seq_atTop hc hpm (x + y)) <|
      (tendsto_seminormFromConst_seq_atTop hc hpm x).add
        (tendsto_seminormFromConst_seq_atTop hc hpm y)
    intro n
    have h_add : f ((x + y) * c ^ n) ≤ f (x * c ^ n) + f (y * c ^ n) := by
      simp only [add_mul, map_add_le_add f _ _]
    simp only [seminormFromConst_seq, ← add_div]
    gcongr
  neg' x := by
    apply tendsto_nhds_unique_of_eventuallyEq (tendsto_seminormFromConst_seq_atTop hc hpm (-x))
      (tendsto_seminormFromConst_seq_atTop hc hpm x)
    simp only [EventuallyEq, eventually_atTop]
    use 0
    simp only [seminormFromConst_seq, neg_mul, map_neg_eq_map, zero_le, implies_true]
  mul_le' x y := by
    have hlim : Tendsto (fun n ↦ seminormFromConst_seq c f hc (x * y) (2 * n)) atTop
        (𝓝 (seminormFromConst' c f hc (x * y))) := by
      apply (tendsto_seminormFromConst_seq_atTop hc hpm (x * y)).comp
        (tendsto_atTop_atTop_of_monotone (fun _ _ hnm ↦ by
          simp only [mul_le_mul_iff_right₀, Nat.succ_pos', hnm]) _)
      · rintro n; use n; lia
    refine le_of_tendsto_of_tendsto' hlim ((tendsto_seminormFromConst_seq_atTop hc hpm x).mul
      (tendsto_seminormFromConst_seq_atTop hc hpm y)) (fun n ↦ ?_)
    simp only [seminormFromConst_seq]
    simp only [div_mul_div_comm₀, ← pow_add, two_mul,
      div_le_div_iff_of_pos_right (pow_pos (lt_of_le_of_ne (apply_nonneg f _) hc.symm) _)]
    rw [pow_add,
      ← mul_assoc, mul_comm (x * y), ← mul_assoc, mul_assoc, mul_comm (c ^ n)]
    exact map_mul_le_mul f (x * c ^ n) (y * c ^ n)

theorem seminormFromConst_def (x : R) :
    seminormFromConst hc hpm x = seminormFromConst' c f hc x :=
  rfl

theorem seminormFromConst_one_le : seminormFromConst' c f hc 1 ≤ 1 :=
  le_of_eq (seminormFromConst_one hc hpm)

theorem seminormFromConst_isNonarchimedean (hna : IsNonarchimedean f) :
    IsNonarchimedean (seminormFromConst' c f hc) := fun x y ↦ by
  apply le_of_tendsto_of_tendsto' (tendsto_seminormFromConst_seq_atTop hc hpm (x + y)) <|
    (tendsto_seminormFromConst_seq_atTop hc hpm x).max
      (tendsto_seminormFromConst_seq_atTop hc hpm y)
  intro n
  have hmax : f ((x + y) * c ^ n) ≤ max (f (x * c ^ n)) (f (y * c ^ n)) := by
    simp only [add_mul, hna _ _]
  rw [le_max_iff] at hmax ⊢
  unfold seminormFromConst_seq
  apply hmax.imp <;> intro <;> gcongr

theorem seminormFromConst_isPowMul : IsPowMul (seminormFromConst' c f hc) := fun x m hm ↦ by
  simp only [seminormFromConst']
  have hlim : Tendsto (fun n ↦ seminormFromConst_seq c f hc (x ^ m) (m * n)) atTop
      (𝓝 (seminormFromConst' c f hc (x ^ m))) := by
    apply (tendsto_seminormFromConst_seq_atTop hc hpm (x ^ m)).comp
      (tendsto_atTop_atTop_of_monotone (fun _ _ hnk ↦ mul_le_mul_right hnk m) _)
    rintro n; use n; exact le_mul_of_one_le_left' hm
  refine tendsto_nhds_unique_of_forall hlim
    ((tendsto_seminormFromConst_seq_atTop hc hpm x).pow m) fun n ↦ ?_
  simp only [seminormFromConst_seq, div_pow₀, ← hpm _ hm, ← pow_mul, mul_pow, mul_comm m n]

/-- The normalized seminorm is bounded above by `f`. -/
theorem seminormFromConst_le_seminorm (x : R) : seminormFromConst' c f hc x ≤ f x := by
  apply le_of_tendsto (tendsto_seminormFromConst_seq_atTop hc hpm x)
  simp only [eventually_atTop]
  use 1
  intro n hn
  rw [seminormFromConst_seq, div_le_iff₀ (by positivity), ← hpm c hn]
  exact map_mul_le_mul ..

/-- At any element that is multiplicative for `f`, the normalized seminorm agrees with `f`. -/
theorem seminormFromConst_apply_of_isMul {x : R} (hx : ∀ y : R, f (x * y) = f x * f y) :
    seminormFromConst' c f hc x = f x :=
  have hlim : Tendsto (seminormFromConst_seq c f hc x) atTop (𝓝 (f x)) := by
    have hseq : seminormFromConst_seq c f hc x = fun _n ↦ f x := by
      ext n
      by_cases hn : n = 0
      · simp only [seminormFromConst_seq, hn, pow_zero, mul_one, div_one₀]
      · simp only [seminormFromConst_seq, hx (c ^ n), hpm _ (Nat.one_le_iff_ne_zero.mpr hn),
          mul_div_cancel_right₀]
    rw [hseq]
    exact tendsto_const_nhds
  tendsto_nhds_unique (tendsto_seminormFromConst_seq_atTop hc hpm x) hlim

/-- Every multiplicative element for `f` is multiplicative for the normalized seminorm. -/
theorem seminormFromConst_isMul_of_isMul {x : R} (hx : ∀ y : R, f (x * y) = f x * f y) (y : R) :
    seminormFromConst' c f hc (x * y) =
      seminormFromConst' c f hc x * seminormFromConst' c f hc y :=
  have hlim : Tendsto (seminormFromConst_seq c f hc (x * y)) atTop
      (𝓝 (seminormFromConst' c f hc x * seminormFromConst' c f hc y)) := by
    rw [seminormFromConst_apply_of_isMul hc hpm hx]
    have hseq : seminormFromConst_seq c f hc (x * y) =
        fun n ↦ f x * seminormFromConst_seq c f hc y n := by
      ext n
      simp only [seminormFromConst_seq, mul_assoc, hx, mul_div_assoc₀]
    simpa [hseq] using (tendsto_seminormFromConst_seq_atTop hc hpm y).const_mul _
  tendsto_nhds_unique (tendsto_seminormFromConst_seq_atTop hc hpm (x * y)) hlim

theorem seminormFromConst_apply_c : seminormFromConst' c f hc c = f c :=
  have hlim : Tendsto (seminormFromConst_seq c f hc c) atTop (𝓝 (f c)) := by
    have hseq : seminormFromConst_seq c f hc c = fun _n ↦ f c := by
      ext n
      simp only [seminormFromConst_seq]
      rw [mul_comm, ← pow_succ, hpm _ le_add_self, pow_succ, mul_comm, mul_div_cancel_right₀]
    rw [hseq]
    exact tendsto_const_nhds
  tendsto_nhds_unique (tendsto_seminormFromConst_seq_atTop hc hpm c) hlim

theorem seminormFromConst_const_mul (x : R) :
    seminormFromConst' c f hc (c * x) =
      seminormFromConst' c f hc c * seminormFromConst' c f hc x := by
  have hlim : Tendsto (fun n ↦ seminormFromConst_seq c f hc x (n + 1)) atTop
      (𝓝 (seminormFromConst' c f hc x)) := by
    apply (tendsto_seminormFromConst_seq_atTop hc hpm x).comp
      (tendsto_atTop_atTop_of_monotone add_left_mono _)
    rintro n; use n; lia
  rw [seminormFromConst_apply_c hc hpm]
  apply tendsto_nhds_unique (tendsto_seminormFromConst_seq_atTop hc hpm (c * x))
  have hterm : seminormFromConst_seq c f hc (c * x) =
      fun n ↦ f c * seminormFromConst_seq c f hc x (n + 1) := by
    ext n
    have harg : (c * x) * c ^ n = x * c ^ (n + 1) := by rw [pow_succ]; ac_rfl
    simp only [seminormFromConst_seq, harg, ← mul_div_assoc₀, div_eq_div_iff, pow_succ (f c)]
    ring
  simpa [hterm] using tendsto_const_nhds.mul hlim

end Ring

section Field

variable {F K : Type*} [NormedField F] [Field K] [Algebra F K]

/-- If `K` is a field, the function `seminormFromConst` is a `RingNorm` on `K`. -/
@[simps!]
def normFromConst {k : K} {g : RingSeminorm K} (hg_k : g k ≠ 0)
    (hg_pm : IsPowMul g) : RingNorm K :=
  (seminormFromConst hg_k hg_pm).toRingNorm (RingSeminorm.ne_zero_iff.mpr
    ⟨k, by rwa [seminormFromConst_def hg_k, seminormFromConst_apply_c hg_k hg_pm]⟩)

theorem seminormFromConstRingNormOfField_def {k : K} {g : RingSeminorm K}
    (hg_k : g k ≠ 0) (hg_pm : IsPowMul g) (x : K) :
    normFromConst hg_k hg_pm x = seminormFromConst' k g hg_k x := rfl

/-- If `K` is a field, `seminormFromConst` applied to an `AlgebraNorm` is an `AlgebraNorm`. -/
@[simps!]
def algNormFromConst {k : K} {g : AlgebraNorm F K} (hg_k : g k ≠ 0) (hg_pm : IsPowMul g) :
    AlgebraNorm F K where
  __ := normFromConst hg_k hg_pm
  smul' x y := by
    have hx : g (algebraMap F K x) = ‖x‖ := by
      have hg1 : g 1 = 1 := by simpa [map_ne_zero_iff_ne_zero, sq] using hg_pm 1 one_le_two
      rw [Algebra.algebraMap_eq_smul_one, map_smul_eq_mul, hg1, mul_one]
    have hy y : g (algebraMap F K x * y) = g (algebraMap F K x) * g y := by
      rw [← Algebra.smul_def, map_smul_eq_mul, hx]
    simp [Algebra.smul_def, seminormFromConst_isMul_of_isMul hg_k hg_pm hy y,
      seminormFromConst_apply_of_isMul hg_k hg_pm hy, hx]

theorem algNormFromConst_def {k x : K} {g : AlgebraNorm F K} (hg_k : g k ≠ 0) (hg_pm : IsPowMul g) :
    algNormFromConst hg_k hg_pm x = seminormFromConst hg_k hg_pm x :=
  rfl

end Field
