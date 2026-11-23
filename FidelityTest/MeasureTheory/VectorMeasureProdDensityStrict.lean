import Mathlib.MeasureTheory.VectorMeasure.Prod
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Strict products and densities of vector measures

These tests ensure that the product of two vector measures is formed only when it exists, and that
vector measures with a density take the integrability of the density, so that neither falls back to
the zero measure.
-/

open MeasureTheory VectorMeasure

/-- info: Unknown constant `MeasureTheory.VectorMeasure.prod_eq_zero_of_not_hasProd` -/
#guard_msgs in
#check_failure MeasureTheory.VectorMeasure.prod_eq_zero_of_not_hasProd

variable {X Y E F G : Type*} [SigmaAlgebra X] [SigmaAlgebra Y]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-! The product needs its existence. -/

/--
error: failed to synthesize instance of type class
  μ.HasProd ν B
-/
#guard_msgs (substring := true) in
noncomputable example (μ : VectorMeasure X E) (ν : VectorMeasure Y F) (B : E →L[ℝ] F →L[ℝ] G) :
    VectorMeasure (X × Y) G :=
  μ.prod ν B

/-- A factor of finite variation and a complete target supply the product. -/
noncomputable example [CompleteSpace G] (μ : VectorMeasure X E) (ν : VectorMeasure Y F)
    [IsFiniteMeasure μ.variation] (B : E →L[ℝ] F →L[ℝ] G) : VectorMeasure (X × Y) G :=
  μ.prod ν B

/-! A density needs its integrability. -/

/--
error: Type mismatch
  volume.withDensityᵥ f
has type
  Integrable f volume → VectorMeasure ℝ ℝ
but is expected to have type
  VectorMeasure ℝ ℝ
-/
#guard_msgs in
noncomputable example (f : ℝ → ℝ) : VectorMeasure ℝ ℝ := volume.withDensityᵥ f

/-- The constant function `1` is not integrable for Lebesgue measure on `ℝ`, so it has no vector
measure with density; its former vector measure was `0`. -/
example : ¬Integrable (fun _ : ℝ ↦ (1 : ℝ)) volume := by
  rw [integrable_const_iff]
  rintro (h | h)
  · exact one_ne_zero h
  · exact measure_ne_top volume Set.univ Real.volume_univ

/-- An integrable density gives the integral on every measurable set. -/
example {μ : Measure X} (f : X → ℝ) (hf : Integrable f μ) {s : Set X} (hs : MeasurableSet s) :
    μ.withDensityᵥ f hf s = ∫ x in s, f x ∂μ :=
  withDensityᵥ_apply hf hs
