import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Prod

/-!
# Chosen linear left inverses

The constructor requires injectivity, including for zero maps. A zero-dimensional domain is
admissible, and the choice of a left inverse does not assert uniqueness away from the range.
-/

noncomputable section

open Function

variable {K V W : Type*} [DivisionRing K]
  [AddCommGroup V] [AddCommGroup W] [Module K V] [Module K W]

/--
error: Type mismatch
  f.leftInverse
has type
  Injective ⇑f → ℚ →ₗ[ℚ] ℚ
but is expected to have type
  ℚ →ₗ[ℚ] ℚ
-/
#guard_msgs in
example (f : ℚ →ₗ[ℚ] ℚ) : ℚ →ₗ[ℚ] ℚ := f.leftInverse

/--
error: Type mismatch
  h
has type
  True
but is expected to have type
  a = b
-/
#guard_msgs in
example : ℚ →ₗ[ℚ] ℚ := (0 : ℚ →ₗ[ℚ] ℚ).leftInverse (by
  intro a b h
  simp only [LinearMap.zero_apply] at h
  exact h)

example (f : V →ₗ[K] W) (hf hg : Injective f) : f.leftInverse hf = f.leftInverse hg := rfl

example (f : V →ₗ[K] W) (hf : Injective f) (x : V) :
    f.leftInverse hf (f x) = x := by
  rw [LinearMap.leftInverse_apply]

example (f : V →ₗ[K] W) (hf : Injective f) :
    (f.leftInverse hf).comp f = LinearMap.id := by
  rw [LinearMap.leftInverse_comp]

-- The zero map on a subsingleton domain is injective and has a left inverse.
example [Subsingleton V] (x : V) :
    (0 : V →ₗ[K] W).leftInverse (fun _ _ _ ↦ Subsingleton.elim _ _) 0 = x := by
  exact Subsingleton.elim _ _

-- An injective map need not be surjective: inclusion into a product is admissible.
example (x : K) :
    (LinearMap.inl K K K).leftInverse (by intro a b h; exact congrArg Prod.fst h)
      (x, 0) = x := by
  exact LinearMap.leftInverse_apply _ _

-- A nontrivial domain rules out a left inverse of the zero map mathematically.
example [Nontrivial V] : ¬ ∃ g : W →ₗ[K] V, g.comp (0 : V →ₗ[K] W) = LinearMap.id := by
  rintro ⟨g, hg⟩
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  have h := LinearMap.congr_fun hg x
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, map_zero, LinearMap.id_apply] at h
  exact hx h.symm

-- Distinct left inverses of the same inclusion remain possible.
example : ∃ g h : (ℚ × ℚ) →ₗ[ℚ] ℚ,
    g.comp (LinearMap.inl ℚ ℚ ℚ) = LinearMap.id ∧
    h.comp (LinearMap.inl ℚ ℚ ℚ) = LinearMap.id ∧ g ≠ h := by
  refine ⟨LinearMap.fst ℚ ℚ ℚ, LinearMap.fst ℚ ℚ ℚ + LinearMap.snd ℚ ℚ ℚ,
    by ext; simp, by ext; simp, ?_⟩
  intro h
  have := LinearMap.congr_fun h (0, 1)
  norm_num at this
