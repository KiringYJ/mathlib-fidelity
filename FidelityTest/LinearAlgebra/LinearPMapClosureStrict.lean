import Mathlib.Topology.Algebra.Module.LinearPMap
import Mathlib.Analysis.Normed.Module.Basic

/-!
# The closure of a partial operator needs closability

These tests ensure that `LinearPMap.closure` takes the proof that the operator is closable, so that
an operator that is not closable no longer has itself as its closure.
-/

/-- info: Unknown constant `LinearPMap.closure_def'` -/
#guard_msgs in
#check_failure LinearPMap.closure_def'

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/--
error: Type mismatch
  f.closure
has type
  f.IsClosable → E →ₗ.[ℝ] F
but is expected to have type
  E →ₗ.[ℝ] F
-/
#guard_msgs in
noncomputable example (f : E →ₗ.[ℝ] F) : E →ₗ.[ℝ] F := f.closure

/-- The closure of a closable operator is a closed extension of it. -/
example (f : E →ₗ.[ℝ] F) (hf : f.IsClosable) : f ≤ f.closure hf ∧ (f.closure hf).IsClosed :=
  ⟨f.le_closure hf, hf.closure_isClosed⟩

/-- A closed operator is its own closure. -/
example (f : E →ₗ.[ℝ] F) (hf : f.IsClosed) : f.closure hf.isClosable = f :=
  LinearPMap.eq_of_eq_graph (hf.isClosable.graph_closure_eq_closure_graph.symm.trans
    hf.submodule_topologicalClosure_eq)

/-- The domain of a closable operator is a core of its closure. -/
example (f : E →ₗ.[ℝ] F) (hf : f.IsClosable) : (f.closure hf).HasCore f.domain :=
  f.closureHasCore hf
