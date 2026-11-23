import Mathlib.Geometry.Euclidean.Inversion.Basic

noncomputable section

open EuclideanGeometry

example (c x : ℝ) (R : ℝ) (hx : x ≠ c) :
    inversion c R x = inversion c R x hx := rfl

example (c x : ℝ) (hx : x ≠ c) : inversion c 0 x hx = c :=
  inversion_zero_radius c x

example (c : ℝ) (R : ℝ) (hR : R ≠ 0) :
    Function.Involutive (inversionEquiv c hR) :=
  inversion_involutive c hR

/--
warning: aesop: failed to prove the goal after exhaustive search.
---
error: could not synthesize default value for parameter 'hx' using tactics
---
error: unsolved goals
⊢ False
-/
#guard_msgs in
example : ℝ := inversion (0 : ℝ) 1 0
