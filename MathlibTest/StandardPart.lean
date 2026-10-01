import Mathlib.Analysis.Real.Hyperreal

/-!
# Standard parts of finite elements

These tests ensure that the standard-part homomorphism accepts exactly finite elements, preserves
their ring operations, and does not silently assign values to infinite hyperreals.
-/

open ArchimedeanClass Hyperreal

open scoped Hyperreal

noncomputable section

example (x y : FiniteElement ℝ*) : FiniteElement ℝ* :=
  x * y - x

example (x y : FiniteElement ℝ*) : stdPart (x + y) = stdPart x + stdPart y := by
  exact map_add stdPart x y

example (x y : FiniteElement ℝ*) : stdPart (x * y) = stdPart x * stdPart y := by
  exact map_mul stdPart x y

example (r : ℝ) : stdPart (FiniteElement.ofArchimedean coeRingHom r) = r := by
  simp

example (r : ℝ) (h : 0 ≤ mk (r : ℝ*)) : stdPart (FiniteElement.mk (r : ℝ*) h) = r := by
  simp

example (r s : ℝ) (h : 0 ≤ mk ((r + s : ℝ) : ℝ*)) :
    stdPart (FiniteElement.mk ((r + s : ℝ) : ℝ*) h) = r + s := by
  simp

example : stdPart (FiniteElement.mk ε archimedeanClassMk_epsilon_pos.le) = 0 := by
  simp

set_option linter.unusedVariables false in
example : True := by
  fail_if_success
    let _r : ℝ := stdPart ω
  trivial

example : ¬ ∃ x : FiniteElement ℝ*, x.1 = ω := by
  rintro ⟨x, hx⟩
  have hfinite : 0 ≤ mk ω := hx ▸ x.2
  exact (not_le_of_gt archimedeanClassMk_omega_neg) hfinite

example :
    stdPart (FiniteElement.mk ε archimedeanClassMk_epsilon_pos.le) = 0 ↔ 0 < mk ε :=
  stdPart_eq_zero

example :
    0 < mk (ε - coeRingHom 0) ↔
      stdPart (FiniteElement.mk ε archimedeanClassMk_epsilon_pos.le) = 0 :=
  mk_sub_pos_iff coeRingHom (x := FiniteElement.mk ε archimedeanClassMk_epsilon_pos.le)

example (u : (FiniteElement ℝ*)ˣ) :
    stdPart (↑u⁻¹ : FiniteElement ℝ*) = (stdPart (u : FiniteElement ℝ*))⁻¹ :=
  map_units_inv stdPart u

example (x : FiniteElement ℝ*) (u : (FiniteElement ℝ*)ˣ) :
    stdPart (x * (↑u⁻¹ : FiniteElement ℝ*)) =
      stdPart x / stdPart (u : FiniteElement ℝ*) := by
  rw [div_eq_mul_inv, map_mul, map_units_inv]

example (u : (FiniteElement ℝ*)ˣ) : stdPart (u : FiniteElement ℝ*) ≠ 0 :=
  stdPart_ne_zero_iff_isUnit.mpr u.isUnit

example : ¬ IsUnit (FiniteElement.mk ε archimedeanClassMk_epsilon_pos.le) :=
  FiniteElement.not_isUnit_iff_mk_pos.2 archimedeanClassMk_epsilon_pos

example : ¬ ∃ x : FiniteElement ℝ*, x.1 = ε⁻¹ := by
  rintro ⟨x, hx⟩
  have hfinite : 0 ≤ mk ε⁻¹ := hx ▸ x.2
  rw [inv_epsilon] at hfinite
  exact (not_le_of_gt archimedeanClassMk_omega_neg) hfinite

example :
    sSup {r : ℝ | (r : ℝ*) < ε} = 0 ∧ 0 ∈ {r : ℝ | (r : ℝ*) < ε} := by
  constructor
  · have h := stdPart_eq_sSup coeRingHom
      (FiniteElement.mk ε archimedeanClassMk_epsilon_pos.le)
    rw [stdPart_epsilon] at h
    exact h.symm
  · exact epsilon_pos

example :
    sInf {r : ℝ | -ε < (r : ℝ*)} = 0 ∧ 0 ∈ {r : ℝ | -ε < (r : ℝ*)} := by
  constructor
  · have h := stdPart_eq_sInf coeRingHom
      (-FiniteElement.mk ε archimedeanClassMk_epsilon_pos.le)
    rw [map_neg, stdPart_epsilon, neg_zero] at h
    exact h.symm
  · simp

example (q : ℚ) : stdPart (q : FiniteElement ℝ*) = q := by
  simp

example : stdPart (0 : FiniteElement ℝ*) = 0 ∧ stdPart (1 : FiniteElement ℝ*) = 1 := by
  simp

example : True := by
  fail_if_success
    let _inst : Inv (FiniteElement ℝ*) := inferInstance
  trivial
