/-
Copyright (c) 2025 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
module

public import Mathlib.Geometry.Euclidean.Triangle

/-!
# IMO 2001 Q5

Let `ABC` be a triangle. Let `AP` bisect `∠BAC` and let `BQ` bisect `∠ABC`, with `P` on `BC` and
`Q` on `AC`. If `AB + BP = AQ + QB` and `∠BAC = 60°`, what are the angles of the triangle?

## Solution

We follow the solution from https://web.evanchen.cc/exams/IMO-2001-notes.pdf.

Let `x = ∠ABQ = ∠QBC`; it must be in `(0°, 60°)`. By angle chasing and the law of sines we derive
```
1 + sin 30° / sin (150° - 2x) = (sin x + sin 60°) / sin (120° - x)
```
Solving this equation gives `x = 40°`, yielding `∠ABC = 80°` and `∠ACB = 40°`.
-/

@[expose] public section

open Affine EuclideanGeometry
open scoped Real

variable {V X : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace X] [NormedAddTorsor V X]

noncomputable section

namespace Imo2001Q5

lemma not_collinear_of_angle_eq_pi_div_three {a b c : X} {hba : b ≠ a} {hca : c ≠ a}
    (h : angle b a c hba hca = π / 3) : ¬Collinear ℝ ({b, a, c} : Set X) := by
  intro hc
  obtain ⟨_, _, hs⟩ :=
    ((collinear_iff_eq_or_eq_or_sin_eq_zero.mp hc).resolve_left hba).resolve_left hca
  rw [h] at hs
  exact (Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos])
    (by linarith [Real.pi_pos])).ne' hs

lemma ne_vertex_of_wbtw_of_not_collinear {a b c p : X}
    (h : ¬Collinear ℝ ({a, b, c} : Set X)) (hp : Wbtw ℝ a p c) : p ≠ b := by
  rintro rfl
  exact h hp.collinear

variable (X) in
/-- The problem's configuration. -/
structure Setup where
  (A B C P Q : X)
  A_ne_B : A ≠ B
  A_ne_C : A ≠ C
  BAC_eq : angle B A C A_ne_B.symm A_ne_C.symm = π / 3
  P_on_BC : Wbtw ℝ B P C
  Q_on_AC : Wbtw ℝ A Q C
  AP_bisect_BAC :
    let hpa := ne_vertex_of_wbtw_of_not_collinear (not_collinear_of_angle_eq_pi_div_three BAC_eq)
      P_on_BC
    angle B A P A_ne_B.symm hpa = angle P A C hpa A_ne_C.symm
  BQ_bisect_ABC :
    let hnc := not_collinear_of_angle_eq_pi_div_three BAC_eq
    let hqb := ne_vertex_of_wbtw_of_not_collinear (by rwa [Set.insert_comm A B] :
      ¬Collinear ℝ ({A, B, C} : Set X)) Q_on_AC
    angle A B Q A_ne_B hqb = angle Q B C hqb (ne₁₃_of_not_collinear hnc).symm
  dist_sum : dist A B + dist B P = dist A Q + dist Q B

namespace Setup

variable (s : Setup X)

/-! ### Nondegeneracy properties and values of angles -/

lemma not_collinear_BAC : ¬Collinear ℝ {s.B, s.A, s.C} :=
  not_collinear_of_angle_eq_pi_div_three s.BAC_eq

lemma B_ne_C : s.B ≠ s.C := ne₁₃_of_not_collinear s.not_collinear_BAC

lemma P_ne_A : s.P ≠ s.A := ne_vertex_of_wbtw_of_not_collinear s.not_collinear_BAC s.P_on_BC

lemma Q_ne_B : s.Q ≠ s.B :=
  ne_vertex_of_wbtw_of_not_collinear (by rw [Set.insert_comm s.A s.B]; exact s.not_collinear_BAC)
    s.Q_on_AC

lemma BAP_eq : angle s.B s.A s.P s.A_ne_B.symm s.P_ne_A = π / 6 := by
  have h := angle_add_of_ne_of_ne s.A_ne_B s.A_ne_C (hpa := s.P_ne_A) s.P_on_BC
  rw [← s.AP_bisect_BAC, s.BAC_eq] at h
  linarith

lemma PAC_eq : angle s.P s.A s.C s.P_ne_A s.A_ne_C.symm = π / 6 :=
  s.AP_bisect_BAC.symm.trans s.BAP_eq

lemma P_ne_B : s.P ≠ s.B := by
  intro hp
  have hz : angle s.B s.A s.P s.A_ne_B.symm s.P_ne_A = 0 :=
    angle_eq_zero_iff_eq_and_ne_or_sbtw.2 (Or.inl ⟨hp.symm, s.A_ne_B.symm⟩)
  linarith [s.BAP_eq, Real.pi_pos]

lemma P_ne_C : s.P ≠ s.C := by
  intro hp
  have hz : angle s.P s.A s.C s.P_ne_A s.A_ne_C.symm = 0 :=
    angle_eq_zero_iff_eq_and_ne_or_sbtw.2 (Or.inl ⟨hp, s.P_ne_A⟩)
  linarith [s.PAC_eq, Real.pi_pos]

lemma sbtw_BPC : Sbtw ℝ s.B s.P s.C := ⟨s.P_on_BC, s.P_ne_B, s.P_ne_C⟩

lemma BPC_eq : angle s.B s.P s.C s.P_ne_B.symm s.P_ne_C.symm = π :=
  s.sbtw_BPC.angle₁₂₃_eq_pi

/-- `x = ∠ABQ = ∠QBC`. This is the main angle in the solution and it suffices to show
this is `2 * π / 9`. -/
def x : ℝ := angle s.A s.B s.Q s.A_ne_B s.Q_ne_B

lemma ABQ_eq : angle s.A s.B s.Q s.A_ne_B s.Q_ne_B = s.x := rfl

lemma QBC_eq : angle s.Q s.B s.C s.Q_ne_B s.B_ne_C.symm = s.x :=
  s.BQ_bisect_ABC.symm.trans s.ABQ_eq

lemma ABC_eq : angle s.A s.B s.C s.A_ne_B s.B_ne_C.symm = 2 * s.x := by
  have h := angle_add_of_ne_of_ne s.A_ne_B.symm s.B_ne_C (hpa := s.Q_ne_B) s.Q_on_AC
  rw [s.ABQ_eq, s.QBC_eq] at h
  linarith

lemma x_pos : 0 < s.x := by
  have h : ¬Collinear ℝ ({s.A, s.B, s.C} : Set X) := by
    rw [Set.insert_comm s.A s.B]
    exact s.not_collinear_BAC
  have hp := angle_pos_of_not_collinear h
  rw [s.ABC_eq] at hp
  linarith

lemma Q_ne_A : s.Q ≠ s.A := by
  intro hq
  have hz : angle s.A s.B s.Q s.A_ne_B s.Q_ne_B = 0 :=
    angle_eq_zero_iff_eq_and_ne_or_sbtw.2 (Or.inl ⟨hq.symm, s.A_ne_B⟩)
  linarith [s.ABQ_eq, s.x_pos]

lemma Q_ne_C : s.Q ≠ s.C := by
  intro hq
  have hz : angle s.Q s.B s.C s.Q_ne_B s.B_ne_C.symm = 0 :=
    angle_eq_zero_iff_eq_and_ne_or_sbtw.2 (Or.inl ⟨hq, s.Q_ne_B⟩)
  linarith [s.QBC_eq, s.x_pos]

lemma sbtw_AQC : Sbtw ℝ s.A s.Q s.C := ⟨s.Q_on_AC, s.Q_ne_A, s.Q_ne_C⟩

lemma AQC_eq : angle s.A s.Q s.C s.Q_ne_A.symm s.Q_ne_C.symm = π :=
  s.sbtw_AQC.angle₁₂₃_eq_pi

lemma ACB_eq : angle s.A s.C s.B s.A_ne_C s.B_ne_C = 2 * π / 3 - 2 * s.x := by
  have h := angle_add_angle_add_angle_eq_pi s.A s.B_ne_C (hp₃₁ := s.A_ne_C) (hp₃₂ := s.A_ne_B)
  rw [angle_comm s.C s.B s.A, s.ABC_eq, s.BAC_eq] at h
  linarith

lemma x_lt_pi_div_three : s.x < π / 3 := by
  have h : ¬Collinear ℝ ({s.A, s.C, s.B} : Set X) := by
    rw [Set.pair_comm s.C s.B, Set.insert_comm s.A s.B]
    exact s.not_collinear_BAC
  have hp := angle_pos_of_not_collinear h
  rw [s.ACB_eq] at hp
  linarith

lemma APB_eq : angle s.A s.P s.B s.P_ne_A.symm s.P_ne_B.symm = 5 * π / 6 - 2 * s.x := by
  have h := angle_add_angle_add_angle_eq_pi s.P s.A_ne_B (hp₃₁ := s.P_ne_B) (hp₃₂ := s.P_ne_A)
  rw [s.BAP_eq, angle_comm s.P s.B s.A,
    s.sbtw_BPC.angle_eq_right s.A (hp₁p₂ := s.A_ne_B), s.ABC_eq] at h
  linarith

lemma AQB_eq : angle s.A s.Q s.B s.Q_ne_A.symm s.Q_ne_B.symm = 2 * π / 3 - s.x := by
  have h := angle_add_angle_add_angle_eq_pi s.Q s.A_ne_B (hp₃₁ := s.Q_ne_B) (hp₃₂ := s.Q_ne_A)
  rw [s.sbtw_AQC.angle_eq_right s.B (hp₁p₂ := s.A_ne_B.symm), s.BAC_eq,
    angle_comm s.Q s.B s.A, s.ABQ_eq] at h
  linarith

/-- A macro for applying the bounds on `x`, `x_pos` and `x_lt_pi_div_three`. -/
macro (name := bx) "bx" : tactic => `(tactic| linarith [s.x_pos, s.x_lt_pi_div_three])

/-! ### Trigonometric reduction using the law of sines -/

lemma sin_APB_pos : 0 < Real.sin (5 * π / 6 - 2 * s.x) := by
  apply Real.sin_pos_of_pos_of_lt_pi <;> bx

lemma sin_AQB_pos : 0 < Real.sin (2 * π / 3 - s.x) := by
  apply Real.sin_pos_of_pos_of_lt_pi <;> bx

/-- `dist B P` in terms of `dist A B`. -/
lemma BP_by_AB :
    dist s.B s.P = Checked.div (Real.sin (π / 6)) (Real.sin (5 * π / 6 - 2 * s.x))
      s.sin_APB_pos.ne'.isUnit * dist s.A s.B := by
  rw [div_mul_eq_mul_div₀, eq_div_iff, mul_comm (dist s.B s.P)]
  have h := law_sin s.A s.P s.B (hp₁₂ := s.P_ne_A.symm) (hp₃₂ := s.P_ne_B.symm)
    (hp₃₁ := s.A_ne_B.symm)
  simpa only [s.APB_eq, s.BAP_eq, dist_comm s.P s.B, dist_comm s.B s.A] using h

/-- `dist A Q` in terms of `dist A B`. -/
lemma AQ_by_AB :
    dist s.A s.Q = Checked.div (Real.sin s.x) (Real.sin (2 * π / 3 - s.x))
      s.sin_AQB_pos.ne'.isUnit * dist s.A s.B := by
  rw [div_mul_eq_mul_div₀, eq_div_iff, mul_comm (dist s.A s.Q)]
  have h := law_sin s.Q s.B s.A (hp₁₂ := s.Q_ne_B) (hp₃₂ := s.A_ne_B)
    (hp₃₁ := s.Q_ne_A.symm)
  rw [angle_comm s.Q s.B s.A, s.ABQ_eq, s.AQB_eq, dist_comm s.B s.A] at h
  exact h.symm

/-- `dist Q B` in terms of `dist A B`. -/
lemma QB_by_AB :
    dist s.Q s.B = Checked.div (Real.sin (π / 3)) (Real.sin (2 * π / 3 - s.x))
      s.sin_AQB_pos.ne'.isUnit * dist s.A s.B := by
  rw [div_mul_eq_mul_div₀, eq_div_iff, mul_comm (dist s.Q s.B)]
  have h := law_sin s.A s.Q s.B (hp₁₂ := s.Q_ne_A.symm) (hp₃₂ := s.Q_ne_B.symm)
    (hp₃₁ := s.A_ne_B.symm)
  rw [s.AQB_eq, s.sbtw_AQC.angle_eq_right s.B (hp₁p₂ := s.A_ne_B.symm), s.BAC_eq,
    dist_comm s.B s.A] at h
  exact h

/-- The key trigonometric equation for `x`. -/
lemma key_x_equation :
    1 + Checked.div (Real.sin (π / 6)) (Real.sin (5 * π / 6 - 2 * s.x))
      s.sin_APB_pos.ne'.isUnit =
    Checked.div (Real.sin s.x + Real.sin (π / 3)) (Real.sin (2 * π / 3 - s.x))
      s.sin_AQB_pos.ne'.isUnit := by
  have := s.dist_sum
  rw [s.BP_by_AB, ← one_add_mul, s.AQ_by_AB, s.QB_by_AB, ← add_mul, ← add_div] at this
  exact mul_right_cancel₀ (dist_ne_zero.mpr s.A_ne_B) this

/-! ### Solving the trigonometric equation -/

lemma x_eq : s.x = 2 * π / 9 := by
  let y := s.x / 2
  let t := y + π / 6
  let w := 5 * π / 6 - 2 * s.x
  have cross := s.key_x_equation
  rw [one_add_div, div_eq_div_iff] at cross
  change (Real.sin w + Real.sin (π / 6)) * Real.sin (2 * π / 3 - s.x) =
    (Real.sin s.x + Real.sin (π / 3)) * Real.sin w at cross
  have hden : Real.sin (2 * π / 3 - s.x) = 2 * Real.sin t * Real.cos t := by
    rw [show 2 * π / 3 - s.x = π - 2 * t by dsimp [t, y]; ring,
      Real.sin_pi_sub, Real.sin_two_mul]
  have hnum : Real.sin s.x + Real.sin (π / 3) = 2 * Real.sin t * Real.cos (y - π / 6) := by
    rw [Real.sin_add_sin, show (s.x + π / 3) / 2 = t by dsimp [t, y]; ring,
      show (s.x - π / 3) / 2 = y - π / 6 by dsimp [y]; ring]
  have ht : 0 < Real.sin t := by
    apply Real.sin_pos_of_pos_of_lt_pi <;> dsimp [t, y] <;> bx
  rw [hden, hnum, Real.sin_pi_div_six] at cross
  have hc : (Real.sin w + 1 / 2) * Real.cos t = Real.cos (y - π / 6) * Real.sin w := by
    apply mul_left_cancel₀ (mul_ne_zero two_ne_zero ht.ne')
    linear_combination cross
  have hd : Real.cos (y - π / 6) - Real.cos t = Real.sin y := by
    dsimp only [t]
    rw [← Real.two_mul_sin_mul_sin, Real.sin_pi_div_six]
    ring
  have work : 2 * Real.sin y * Real.sin w = Real.cos t := by
    linear_combination -2 * hc - (2 * Real.sin w) * hd
  rw [Real.two_mul_sin_mul_sin,
    show y - w = 5 * y + π / 6 - π by dsimp [y, w]; ring, Real.cos_sub_pi,
    show y + w = π - (3 * y + π / 6) by dsimp [y, w]; ring, Real.cos_pi_sub] at work
  have hprod : Real.cos (3 * y + π / 6) * (2 * Real.cos (2 * y) - 1) = 0 := by
    have hsum := Real.cos_add_cos (y + π / 6) (5 * y + π / 6)
    rw [show (y + π / 6 + (5 * y + π / 6)) / 2 = 3 * y + π / 6 by ring,
      show (y + π / 6 - (5 * y + π / 6)) / 2 = -(2 * y) by ring, Real.cos_neg] at hsum
    change -Real.cos (5 * y + π / 6) - -Real.cos (3 * y + π / 6) =
      Real.cos (y + π / 6) at work
    linear_combination -hsum - work
  have hne : 2 * Real.cos (2 * y) - 1 ≠ 0 := by
    intro he
    have htwo : 2 * y = s.x := by dsimp [y]; ring
    rw [htwo] at he
    have hcos : Real.cos s.x = Real.cos (π / 3) := by rw [Real.cos_pi_div_three]; linarith
    exact s.x_lt_pi_div_three.ne (Real.injOn_cos ⟨s.x_pos.le, by bx⟩
      ⟨by positivity, by bound⟩ hcos)
  have hz := ((mul_eq_zero.1 hprod).resolve_right hne).trans Real.cos_pi_div_two.symm
  have he := Real.injOn_cos ⟨by dsimp [y]; bx, by dsimp [y]; bx⟩
    ⟨by positivity, by bound⟩ hz
  dsimp [y] at he
  linarith

end Setup

theorem result (s : Setup X) : angle s.A s.B s.C s.A_ne_B s.B_ne_C.symm = 4 * π / 9 ∧
    angle s.A s.C s.B s.A_ne_C s.B_ne_C = 2 * π / 9 := by
  rw [s.ABC_eq, s.ACB_eq, s.x_eq]; constructor <;> ring

end Imo2001Q5
