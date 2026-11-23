import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Projection

/-!
# Left inverses of injective linear maps as canonical data

These tests ensure that no chosen linear left inverse is public. An injective map has left
inverses, every left inverse is the projection along its kernel, a complement of the range, and
the projection along a given complement is the unique left inverse vanishing on it; the extension
of functionals from a subspace takes the complement on which it vanishes.
-/

open Function

/-- info: Unknown constant `LinearMap.leftInverse` -/
#guard_msgs in
#check_failure LinearMap.leftInverse

/-- info: Unknown constant `LinearMap.leftInverse_apply` -/
#guard_msgs in
#check_failure LinearMap.leftInverse_apply

/-- info: Unknown constant `Subspace.quotEquivAnnihilator` -/
#guard_msgs in
#check_failure Subspace.quotEquivAnnihilator

variable {K V W : Type*} [DivisionRing K]
  [AddCommGroup V] [AddCommGroup W] [Module K V] [Module K W]

/-! An injective map has a left inverse, and a nontrivial domain rules one out for the zero map. -/

example (f : V →ₗ[K] W) (hf : Injective f) : ∃ g : W →ₗ[K] V, g ∘ₗ f = LinearMap.id :=
  f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hf)

example [Nontrivial V] : ¬ ∃ g : W →ₗ[K] V, g.comp (0 : V →ₗ[K] W) = LinearMap.id := by
  rintro ⟨g, hg⟩
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  have h := LinearMap.congr_fun hg x
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, map_zero, LinearMap.id_apply] at h
  exact hx h.symm

/-! Every left inverse is the projection along its kernel. -/

example (f : V →ₗ[K] W) (hf : Injective f) (g : W →ₗ[K] V) (hg : g ∘ₗ f = LinearMap.id) :
    g = LinearMap.linearProjOfIsCompl (LinearMap.ker g) f hf
      (LinearMap.isCompl_range_ker_of_comp_eq_id f hg) :=
  LinearMap.eq_linearProjOfIsCompl_ker f hf hg

/-- Distinct left inverses of the same inclusion have distinct kernels. -/
example : ∃ g h : (ℚ × ℚ) →ₗ[ℚ] ℚ,
    g.comp (LinearMap.inl ℚ ℚ ℚ) = LinearMap.id ∧
    h.comp (LinearMap.inl ℚ ℚ ℚ) = LinearMap.id ∧ g ≠ h := by
  refine ⟨LinearMap.fst ℚ ℚ ℚ, LinearMap.fst ℚ ℚ ℚ + LinearMap.snd ℚ ℚ ℚ,
    by ext; simp, by ext; simp, ?_⟩
  intro h
  have := LinearMap.congr_fun h (0, 1)
  norm_num at this

/-! The extension of a functional on a subspace vanishes on the given complement. -/

example {F : Type*} [Field F] [Module F V] (U q : Subspace F V) (h : IsCompl U q)
    (φ : Module.Dual F U) (x : V) (hx : x ∈ q) : U.dualLift q h φ x = 0 :=
  Subspace.dualLift_of_mem_complement h hx

example {F : Type*} [Field F] [Module F V] (U q : Subspace F V) (h : IsCompl U q)
    (φ : Module.Dual F U) (u : U) : U.dualLift q h φ u = φ u :=
  Subspace.dualLift_of_subtype h u
