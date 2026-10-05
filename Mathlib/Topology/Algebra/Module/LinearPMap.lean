/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.LinearAlgebra.LinearPMap
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Algebra.Module.Equiv

/-!
# Partially defined linear operators over topological vector spaces

We define basic notions of partially defined linear operators, which we call unbounded operators
for short.
In this file we prove all elementary properties of unbounded operators that do not assume that the
underlying spaces are normed.

## Main definitions

* `LinearPMap.IsClosed`: An unbounded operator is closed iff its graph is closed.
* `LinearPMap.IsClosable`: An unbounded operator is closable iff the closure of its graph is a
  graph.
* `LinearPMap.closure`: For a closable unbounded operator `f : LinearPMap R E F` the closure is
  the smallest closed extension of `f`. It takes the proof that `f` is closable: the closure of the
  graph of an operator that is not closable is not a graph.
* `LinearPMap.HasCore`: a submodule contained in the domain is a core if restricting to the core
  does not lose information about the unbounded operator.

## Main statements

* `LinearPMap.isClosable_iff_exists_closed_extension`: an unbounded operator is closable iff it has
  a closed extension.
* `LinearPMap.IsClosable.existsUnique`: there exists a unique closure
* `LinearPMap.closureHasCore`: the domain of a closable `f` is a core of its closure

## References

* [J. Weidmann, *Linear Operators in Hilbert Spaces*][weidmann_linear]

## Tags

Unbounded operators, closed operators
-/

@[expose] public section

variable {R E F : Type*}
variable [CommRing R] [AddCommGroup E] [AddCommGroup F]
variable [Module R E] [Module R F]
variable [TopologicalSpace E] [TopologicalSpace F]

namespace LinearPMap

/-! ### Closed and closable operators -/

section Basic

/-- An unbounded operator is closed iff its graph is closed. -/
def IsClosed (f : E →ₗ.[R] F) : Prop :=
  _root_.IsClosed (f.graph : Set (E × F))

variable [ContinuousAdd E] [ContinuousAdd F]
variable [TopologicalSpace R] [ContinuousSMul R E] [ContinuousSMul R F]

/-- An unbounded operator is closable iff the closure of its graph is a graph. -/
def IsClosable (f : E →ₗ.[R] F) : Prop :=
  ∃ f' : E →ₗ.[R] F, f.graph.topologicalClosure = f'.graph

/-- A closed operator is trivially closable. -/
theorem IsClosed.isClosable {f : E →ₗ.[R] F} (hf : f.IsClosed) : f.IsClosable :=
  ⟨f, hf.submodule_topologicalClosure_eq⟩

/-- If `g` has a closable extension `f`, then `g` itself is closable. -/
theorem IsClosable.leIsClosable {f g : E →ₗ.[R] F} (hf : f.IsClosable) (hfg : g ≤ f) :
    g.IsClosable := by
  obtain ⟨f', hf⟩ := hf
  have : g.graph.topologicalClosure ≤ f'.graph := by
    rw [← hf]
    exact Submodule.topologicalClosure_mono (le_graph_of_le hfg)
  use g.graph.topologicalClosure.toLinearPMap
  rw [Submodule.toLinearPMap_graph_eq]
  exact fun _ hx hx' => f'.graph_fst_eq_zero_snd (this hx) hx'

/-- The closure is unique. -/
theorem IsClosable.existsUnique {f : E →ₗ.[R] F} (hf : f.IsClosable) :
    ∃! f' : E →ₗ.[R] F, f.graph.topologicalClosure = f'.graph := by
  refine existsUnique_of_exists_of_unique hf fun _ _ hy₁ hy₂ => eq_of_eq_graph ?_
  rw [← hy₁, ← hy₂]

/-- The closure of a closable operator `f`: the operator whose graph is the closure of the graph
of `f`, which is unique (`IsClosable.existsUnique`). An operator that is not closable has no
closure, since the closure of its graph is not a graph. -/
noncomputable def closure (f : E →ₗ.[R] F) (hf : f.IsClosable) : E →ₗ.[R] F :=
  hf.choose

/-- The closure (as a submodule) of the graph is equal to the graph of the closure
  (as a `LinearPMap`). -/
theorem IsClosable.graph_closure_eq_closure_graph {f : E →ₗ.[R] F} (hf : f.IsClosable) :
    f.graph.topologicalClosure = (f.closure hf).graph :=
  hf.choose_spec

/-- A `LinearPMap` is contained in its closure. -/
theorem le_closure (f : E →ₗ.[R] F) (hf : f.IsClosable) : f ≤ f.closure hf := by
  refine le_of_le_graph ?_
  rw [← hf.graph_closure_eq_closure_graph]
  exact (graph f).le_topologicalClosure

theorem IsClosable.closure_mono {f g : E →ₗ.[R] F} (hg : g.IsClosable) (h : f ≤ g) :
    f.closure (hg.leIsClosable h) ≤ g.closure hg := by
  refine le_of_le_graph ?_
  rw [← (hg.leIsClosable h).graph_closure_eq_closure_graph]
  rw [← hg.graph_closure_eq_closure_graph]
  exact Submodule.topologicalClosure_mono (le_graph_of_le h)

/-- If `f` is closable, then the closure is closed. -/
theorem IsClosable.closure_isClosed {f : E →ₗ.[R] F} (hf : f.IsClosable) :
    (f.closure hf).IsClosed := by
  rw [IsClosed, ← hf.graph_closure_eq_closure_graph]
  exact f.graph.isClosed_topologicalClosure

/-- If `f` is closable, then the closure is closable. -/
theorem IsClosable.closureIsClosable {f : E →ₗ.[R] F} (hf : f.IsClosable) :
    (f.closure hf).IsClosable :=
  hf.closure_isClosed.isClosable

theorem isClosable_iff_exists_closed_extension {f : E →ₗ.[R] F} :
    f.IsClosable ↔ ∃ g : E →ₗ.[R] F, g.IsClosed ∧ f ≤ g :=
  ⟨fun h => ⟨f.closure h, h.closure_isClosed, f.le_closure h⟩, fun ⟨_, hg, h⟩ =>
    hg.isClosable.leIsClosable h⟩

/-! ### The core of a linear operator -/


/-- A submodule `S` is a core of `f` if the restriction of `f` to `S` is closable and its closure
is `f`. -/
structure HasCore (f : E →ₗ.[R] F) (S : Submodule R E) : Prop where
  le_domain : S ≤ f.domain
  isClosable : (f.domRestrict S).IsClosable
  closure_eq : (f.domRestrict S).closure isClosable = f

theorem hasCore_def {f : E →ₗ.[R] F} {S : Submodule R E} (h : f.HasCore S) :
    (f.domRestrict S).closure h.isClosable = f :=
  h.closure_eq

/-- For every closable unbounded operator `f` the submodule `f.domain` is a core of its
closure. -/
theorem closureHasCore (f : E →ₗ.[R] F) (hf : f.IsClosable) :
    (f.closure hf).HasCore f.domain := by
  have heq : (f.closure hf).domRestrict f.domain = f := by
    ext x h1 h2
    · simp only [domRestrict_domain, Submodule.mem_inf, and_iff_left_iff_imp]
      intro hx
      exact (f.le_closure hf).1 hx
    let z : (f.closure hf).domain := ⟨x, (f.le_closure hf).1 h2⟩
    have hyz : x = z := rfl
    rw [(f.le_closure hf).2 hyz]
    exact domRestrict_apply hyz
  refine ⟨(f.le_closure hf).1, by rw [heq]; exact hf, ?_⟩
  simp only [heq]

end Basic

/-! ### Topological properties of the inverse -/

section Inverse

variable {f : E →ₗ.[R] F}

/-- The inverse of `f : LinearPMap` is closed if and only if `f` is closed. -/
theorem inverse_closed_iff (hf : f.ker = ⊥) : f.inverse.IsClosed ↔ f.IsClosed := by
  rw [IsClosed, inverse_graph hf]
  exact (ContinuousLinearEquiv.prodComm R E F).isClosed_image

variable [ContinuousAdd E] [ContinuousAdd F]
variable [TopologicalSpace R] [ContinuousSMul R E] [ContinuousSMul R F]

/-- If `f` is invertible and closable as well as its closure being invertible, then
the graph of the inverse of the closure is given by the closure of the graph of the inverse. -/
theorem closure_inverse_graph (hf : f.ker = ⊥) (hf' : f.IsClosable)
    (hcf : (f.closure hf').ker = ⊥) :
    (f.closure hf').inverse.graph = f.inverse.graph.topologicalClosure := by
  rw [inverse_graph hf, inverse_graph hcf, ← hf'.graph_closure_eq_closure_graph]
  apply SetLike.ext'
  simp only [Submodule.topologicalClosure_coe, Submodule.map_coe, LinearEquiv.coe_coe,
    LinearEquiv.prodComm_apply]
  apply (image_closure_subset_closure_image continuous_swap).antisymm
  have h1 := (LinearEquiv.prodComm R E F).toEquiv.image_eq_preimage_symm f.graph
  have h2 := (LinearEquiv.prodComm R E F).toEquiv.image_eq_preimage_symm (_root_.closure f.graph)
  simp only [LinearEquiv.coe_toEquiv, LinearEquiv.prodComm_apply] at h1 h2
  rw [h1, h2]
  apply continuous_swap.closure_preimage_subset

/-- Assuming that `f` is invertible and closable, then the closure is invertible if and only
if the inverse of `f` is closable. -/
theorem inverse_isClosable_iff (hf : f.ker = ⊥) (hf' : f.IsClosable) :
    f.inverse.IsClosable ↔ (f.closure hf').ker = ⊥ := by
  constructor
  · intro ⟨f', h⟩
    rw [LinearPMap.ker_eq_bot']
    intro ⟨x, hx⟩ hx'
    simp only [Submodule.mk_eq_zero]
    rw [eq_comm, image_iff] at hx'
    have : (0, x) ∈ graph f' := by
      rw [← h, inverse_graph hf]
      rw [← hf'.graph_closure_eq_closure_graph, ← SetLike.mem_coe,
        Submodule.topologicalClosure_coe] at hx'
      apply image_closure_subset_closure_image continuous_swap
      simp only [Set.mem_image, Prod.exists, Prod.swap_prod_mk, Prod.mk.injEq]
      exact ⟨x, 0, hx', rfl, rfl⟩
    exact graph_fst_eq_zero_snd f' this rfl
  · intro h
    use (f.closure hf').inverse
    exact (closure_inverse_graph hf hf' h).symm

/-- If `f` is invertible and closable, then taking the closure and the inverse commute. -/
theorem inverse_closure (hf : f.ker = ⊥) (hf' : f.IsClosable) (hcf : (f.closure hf').ker = ⊥) :
    f.inverse.closure ((inverse_isClosable_iff hf hf').mpr hcf) = (f.closure hf').inverse := by
  apply eq_of_eq_graph
  rw [closure_inverse_graph hf hf' hcf,
    ((inverse_isClosable_iff hf hf').mpr hcf).graph_closure_eq_closure_graph]

end Inverse

end LinearPMap
