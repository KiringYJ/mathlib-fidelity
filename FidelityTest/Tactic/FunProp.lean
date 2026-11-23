import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Meromorphic.Basic

/-! Test `fun_prop` on checked meromorphic operations. -/

open Filter Set
open scoped Topology

variable {U : Set ℂ}

-- The checked reciprocal must be defined throughout a punctured neighborhood.
example {D : Type*} {coord : D → ℂ} {g : D → ℂ} (hg : MeromorphicOn g U coord)
    (h : ∀ x ∈ U, range (fun z : {z // IsUnit (g z)} ↦ coord z.val) ∈ 𝓝[≠] x) :
    MeromorphicOn (fun z : {z // IsUnit (g z)} ↦ Checked.inv (g z) z.property) U
      (coord ∘ Subtype.val) := by
  fun_prop (disch := assumption)

example {D : Type*} {coord : D → ℂ} {f g : D → ℂ}
    (hf : MeromorphicOn f U coord) (hg : MeromorphicOn g U coord)
    (h : ∀ x ∈ U, range (fun z : {z // IsUnit (g z)} ↦ coord z.val) ∈ 𝓝[≠] x) :
    MeromorphicOn (fun z : {z // IsUnit (g z)} ↦ Checked.div (f z) (g z) z.property) U
      (coord ∘ Subtype.val) := by
  fun_prop (disch := assumption)
