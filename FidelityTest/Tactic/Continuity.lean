import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.ContinuousMap.Basic

/-! The local inverse and quotient APIs allow a denominator that vanishes outside the unit locus. -/

section LocalInverse

open Filter
open scoped Topology

private noncomputable def positivePart (x : ℝ) : ℝ := max x 0

private lemma continuous_positivePart : Continuous positivePart :=
  continuous_id.max continuous_const

private lemma positivePart_two : positivePart 2 = 2 :=
  max_eq_left (show (0 : ℝ) ≤ 2 by norm_num)

private lemma isUnit_positivePart_two : IsUnit (positivePart 2) := by
  rw [positivePart_two]
  exact (show (2 : ℝ) ≠ 0 by norm_num).isUnit

example : ¬IsUnit (positivePart (-1)) := by simp [positivePart]

example (s : Set ℝ) :
    ContinuousWithinAt
      (fun x : {x // IsUnit (positivePart x)} ↦ Checked.inv (positivePart x.val) x.property)
      (Subtype.val ⁻¹' s) ⟨2, isUnit_positivePart_two⟩ :=
  continuous_positivePart.continuousWithinAt.fun_inv₀_restrict isUnit_positivePart_two

example (s : Set ℝ) :
    ContinuousOn
      (fun x : {x // IsUnit (positivePart x)} ↦ Checked.div 1 (positivePart x.val) x.property)
      (Subtype.val ⁻¹' s) :=
  continuous_const.continuousOn.div₀_restrict continuous_positivePart.continuousOn

example : Tendsto
    (fun x : {x // IsUnit (positivePart x)} ↦ Checked.div 1 (positivePart x.val) x.property)
    (comap Subtype.val (𝓝 (2 : ℝ))) (𝓝 (1 / 2)) := by
  have hg : Tendsto positivePart (𝓝 (2 : ℝ)) (𝓝 (2 : ℝ)) := by
    simpa only [positivePart_two] using (continuous_positivePart.continuousAt (x := (2 : ℝ))).tendsto
  exact (tendsto_const_nhds (x := (1 : ℝ))).div₀_restrict hg

end LocalInverse
