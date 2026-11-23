module
import Mathlib

/-! Test that rational casting preserves scientific literals. -/

example (m e : ℕ) (s : Bool) :
    ((OfScientific.ofScientific m s e : ℚ) : ℝ) = (OfScientific.ofScientific m s e : ℝ) :=
  Rat.cast_ofScientific m s e
