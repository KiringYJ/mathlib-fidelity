import Mathlib.Combinatorics.Matroid.Loop

/-!
# Strict fundamental circuits and cocircuits

These tests ensure that the fundamental circuit of `e` and `I` is defined exactly when `I` is
independent and `e` is in the closure of `I` but not in `I`, and the fundamental cocircuit of `e`
and `B` exactly when `B` is spanning, `e ∈ B`, and `B \ {e}` is not spanning, so that the former
values `{e}` and `insert e I`, which need not be circuits, are no longer returned.
-/

open Matroid Set

variable {α : Type*} {M : Matroid α} {B I : Set α} {e f : α}

/-- info: Unknown constant `Matroid.fundCircuit_eq_of_mem` -/
#guard_msgs in
#check_failure Matroid.fundCircuit_eq_of_mem

/-- info: Unknown constant `Matroid.fundCircuit_eq_of_notMem_ground` -/
#guard_msgs in
#check_failure Matroid.fundCircuit_eq_of_notMem_ground

/-- info: Unknown constant `Matroid.fundCocircuit_eq_of_notMem` -/
#guard_msgs in
#check_failure Matroid.fundCocircuit_eq_of_notMem

/-- info: Unknown constant `Matroid.fundCocircuit_eq_of_notMem_ground` -/
#guard_msgs in
#check_failure Matroid.fundCocircuit_eq_of_notMem_ground

/-- info: Unknown constant `Matroid.fundCircuit_restrict_univ` -/
#guard_msgs in
#check_failure Matroid.fundCircuit_restrict_univ

/-- info: Unknown constant `Matroid.Indep.fundCircuit_isCircuit` -/
#guard_msgs in
#check_failure Matroid.Indep.fundCircuit_isCircuit

/-- info: Unknown constant `Matroid.IsBase.fundCircuit_isCircuit` -/
#guard_msgs in
#check_failure Matroid.IsBase.fundCircuit_isCircuit

/-! The fundamental circuit needs its data. -/

/--
error: Type mismatch
  M.fundCircuit e I
has type
  M.FundCircuitExists e I → Set α
but is expected to have type
  Set α
-/
#guard_msgs in
example (M : Matroid α) (e : α) (I : Set α) : Set α := M.fundCircuit e I

/-- An element of `I` has no fundamental circuit with `I`; its former value was `{e}`. -/
example (he : e ∈ I) : ¬M.FundCircuitExists e I := fun h ↦ h.notMem he

/-- An element outside the closure of `I` has none either; its former value was `insert e I`. -/
example (he : e ∉ M.closure I) : ¬M.FundCircuitExists e I := fun h ↦ he h.mem_closure

/-! Fundamental circuits and cocircuits of a base. -/

example (hB : M.IsBase B) (heE : e ∈ M.E) (heB : e ∉ B) :
    M.IsCircuit (M.fundCircuit e B (hB.fundCircuitExists heE heB)) :=
  fundCircuit_isCircuit _

example (hB : M.IsBase B) (he : e ∈ B) :
    M.IsCocircuit (M.fundCocircuit e B (hB.fundCocircuitExists he)) ∧
      M.fundCocircuit e B (hB.fundCocircuitExists he) ∩ B = {e} :=
  ⟨fundCocircuit_isCocircuit _, fundCocircuit_inter_eq _⟩

example (hB : M.IsBase B) (he : e ∈ M.E \ B) (hf : f ∈ B) :
    e ∈ M.fundCocircuit f B (hB.fundCocircuitExists hf) ↔
      f ∈ M.fundCircuit e B (hB.fundCircuitExists he.1 he.2) :=
  hB.mem_fundCocircuit_iff_mem_fundCircuit he hf
