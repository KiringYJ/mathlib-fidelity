/-
Copyright (c) 2025 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
module

public import Mathlib.Combinatorics.Matroid.Closure

/-!
# Matroid IsCircuits

A 'Circuit' of a matroid `M` is a minimal set `C` that is dependent in `M`.
A matroid is determined by its set of circuits, and often the circuits
offer a more compact description of a matroid than the collection of independent sets or bases.
In matroids arising from graphs, circuits correspond to graphical cycles.

## Main Declarations

* `Matroid.IsCircuit M C` means that `C` is minimally dependent in `M`.
* For an `Indep`endent set `I` whose closure contains an element `e ∉ I`,
  `Matroid.fundCircuit M e I` is the unique circuit contained in `insert e I`.
* `Matroid.Indep.fundCircuit_isCircuit` states that `Matroid.fundCircuit M e I` is indeed a circuit.
* `Matroid.IsCircuit.eq_fundCircuit_of_subset` states that `Matroid.fundCircuit M e I` is the
  unique circuit contained in `insert e I`.
* `Matroid.dep_iff_superset_isCircuit` states that the dependent subsets of the ground set
  are precisely those that contain a circuit.
* `Matroid.ext_isCircuit` : a matroid is determined by its collection of circuits.
* `Matroid.IsCircuit.strong_multi_elimination` : the strong circuit elimination rule for an
  infinite collection of circuits.
* `Matroid.IsCircuit.strong_elimination` : the strong circuit elimination rule for two circuits.
* `Matroid.finitary_iff_forall_isCircuit_finite` : finitary matroids are precisely those whose
  circuits are all finite.
* `Matroid.IsCocircuit M C` means that `C` is minimally dependent in `M✶`,
  or equivalently that `M.E \ C` is a hyperplane of `M`.
* `Matroid.fundCircuit M e I h` is the unique circuit contained in `insert e I`, for an independent
  set `I` and `e ∈ M.closure I \ I`, which `h : M.FundCircuitExists e I` states.
* `Matroid.fundCocircuit M e B h` is the unique cocircuit that intersects the spanning set `B`
  precisely in the element `e`, for `e ∈ B` such that `B \ {e}` is not spanning, which
  `h : M.FundCocircuitExists e B` states; for a base `B` this holds for every `e ∈ B`.
* `Matroid.IsBase.mem_fundCocircuit_iff_mem_fundCircuit` : `e` is in the fundamental circuit
  for `B` and `f` iff `f` is in the fundamental cocircuit for `B` and `e`.

## Implementation Details

`Matroid.fundCircuit M e I h` is defined exactly when `I` is independent and
`e ∈ M.closure I \ I`: then `insert e I` is dependent and contains a unique circuit. Otherwise
`insert e I` contains no circuit through `e`, or several, so the operation takes this evidence.
-/

@[expose] public section

variable {α : Type*} {M : Matroid α} {C C' I X Y R : Set α} {e f x : α}

open Set

namespace Matroid

/-- `M.IsCircuit C` means that `C` is a minimal dependent set in `M`. -/
def IsCircuit (M : Matroid α) := Minimal M.Dep

lemma isCircuit_def : M.IsCircuit C ↔ Minimal M.Dep C := Iff.rfl

lemma IsCircuit.dep (hC : M.IsCircuit C) : M.Dep C :=
  hC.prop

lemma IsCircuit.not_indep (hC : M.IsCircuit C) : ¬ M.Indep C :=
  hC.dep.not_indep

lemma IsCircuit.minimal (hC : M.IsCircuit C) : Minimal M.Dep C :=
  hC

@[aesop unsafe 20% (rule_sets := [Matroid])]
lemma IsCircuit.subset_ground (hC : M.IsCircuit C) : C ⊆ M.E :=
  hC.dep.subset_ground

lemma IsCircuit.nonempty (hC : M.IsCircuit C) : C.Nonempty :=
  hC.dep.nonempty

lemma empty_not_isCircuit (M : Matroid α) : ¬M.IsCircuit ∅ :=
  fun h ↦ by simpa using h.nonempty

lemma isCircuit_iff : M.IsCircuit C ↔ M.Dep C ∧ ∀ ⦃D⦄, M.Dep D → D ⊆ C → D = C := by
  simp_rw [isCircuit_def, minimal_subset_iff, eq_comm (a := C)]

lemma IsCircuit.ssubset_indep (hC : M.IsCircuit C) (hXC : X ⊂ C) : M.Indep X := by
  rw [← not_dep_iff (hXC.subset.trans hC.subset_ground)]
  exact fun h ↦ hXC.ne ((isCircuit_iff.1 hC).2 h hXC.subset)

lemma IsCircuit.minimal_not_indep (hC : M.IsCircuit C) : Minimal (¬ M.Indep ·) C := by
  simp_rw [minimal_iff_forall_ssubset, and_iff_right hC.not_indep, not_not]
  exact fun ⦃t⦄ a ↦ ssubset_indep hC a

lemma isCircuit_iff_minimal_not_indep (hCE : C ⊆ M.E) : M.IsCircuit C ↔ Minimal (¬ M.Indep ·) C :=
  ⟨IsCircuit.minimal_not_indep, fun h ↦ ⟨(not_indep_iff hCE).1 h.prop,
    fun _ hJ hJC ↦ (h.eq_of_superset hJ.not_indep hJC).le⟩⟩

lemma IsCircuit.sdiff_singleton_indep (hC : M.IsCircuit C) (he : e ∈ C) : M.Indep (C \ {e}) :=
  hC.ssubset_indep (sdiff_singleton_ssubset.2 he)

@[deprecated (since := "2026-06-03")]
alias IsCircuit.diff_singleton_indep := IsCircuit.sdiff_singleton_indep

lemma isCircuit_iff_forall_ssubset : M.IsCircuit C ↔ M.Dep C ∧ ∀ ⦃I⦄, I ⊂ C → M.Indep I := by
  rw [IsCircuit, minimal_iff_forall_ssubset, and_congr_right_iff]
  exact fun h ↦ ⟨fun h' I hIC ↦ ((not_dep_iff (hIC.subset.trans h.subset_ground)).1 (h' hIC)),
    fun h I hIC ↦ (h hIC).not_dep⟩

lemma isCircuit_antichain : IsAntichain (· ⊆ ·) (Set.ofPred M.IsCircuit) :=
  fun _ hC _ hC' hne hss ↦ hne <| (IsCircuit.minimal hC').eq_of_subset hC.dep hss

lemma IsCircuit.eq_of_not_indep_subset (hC : M.IsCircuit C) (hX : ¬ M.Indep X) (hXC : X ⊆ C) :
    X = C :=
  eq_of_le_of_not_lt hXC (hX ∘ hC.ssubset_indep)

lemma IsCircuit.eq_of_dep_subset (hC : M.IsCircuit C) (hX : M.Dep X) (hXC : X ⊆ C) : X = C :=
  hC.eq_of_not_indep_subset hX.not_indep hXC

lemma IsCircuit.not_ssubset (hC : M.IsCircuit C) (hC' : M.IsCircuit C') : ¬C' ⊂ C :=
  fun h' ↦ h'.ne (hC.eq_of_dep_subset hC'.dep h'.subset)

lemma IsCircuit.eq_of_subset_isCircuit (hC : M.IsCircuit C) (hC' : M.IsCircuit C') (h : C ⊆ C') :
    C = C' :=
  hC'.eq_of_dep_subset hC.dep h

lemma IsCircuit.eq_of_superset_isCircuit (hC : M.IsCircuit C) (hC' : M.IsCircuit C') (h : C' ⊆ C) :
    C = C' :=
  (hC'.eq_of_subset_isCircuit hC h).symm

lemma isCircuit_iff_dep_forall_sdiff_singleton_indep :
    M.IsCircuit C ↔ M.Dep C ∧ ∀ e ∈ C, M.Indep (C \ {e}) := by
  wlog hCE : C ⊆ M.E
  · exact iff_of_false (hCE ∘ IsCircuit.subset_ground) (fun h ↦ hCE h.1.subset_ground)
  simp [isCircuit_iff_minimal_not_indep hCE, ← not_indep_iff hCE,
    minimal_iff_forall_sdiff_singleton (P := (¬ M.Indep ·))
    (fun _ _ hY hYX hX ↦ hY <| hX.subset hYX)]

@[deprecated (since := "2026-06-03")]
alias isCircuit_iff_dep_forall_diff_singleton_indep :=
  isCircuit_iff_dep_forall_sdiff_singleton_indep

/-! ### Independence and bases -/

lemma Indep.insert_isCircuit_of_forall (hI : M.Indep I) (heI : e ∉ I) (he : e ∈ M.closure I)
    (h : ∀ f ∈ I, e ∉ M.closure (I \ {f})) : M.IsCircuit (insert e I) := by
  rw [isCircuit_iff_dep_forall_sdiff_singleton_indep, hI.insert_dep_iff, and_iff_right ⟨he, heI⟩]
  rintro f (rfl | hfI)
  · simpa [heI]
  rw [← insert_sdiff_singleton_comm (by rintro rfl; contradiction),
    (hI.sdiff _).insert_indep_iff_of_notMem (by simp [heI])]
  exact ⟨mem_ground_of_mem_closure he, h f hfI⟩

lemma Indep.insert_isCircuit_of_forall_of_nontrivial (hI : M.Indep I) (hInt : I.Nontrivial)
    (he : e ∈ M.closure I) (h : ∀ f ∈ I, e ∉ M.closure (I \ {f})) : M.IsCircuit (insert e I) := by
  refine hI.insert_isCircuit_of_forall (fun heI ↦ ?_) he h
  obtain ⟨f, hf, hne⟩ := hInt.exists_ne e
  exact h f hf (mem_closure_of_mem' _ (by simp [heI, hne.symm]))

lemma IsCircuit.sdiff_singleton_isBasis (hC : M.IsCircuit C) (he : e ∈ C) :
    M.IsBasis (C \ {e}) C := by
  nth_rw 2 [← insert_eq_of_mem he]
  rw [← insert_sdiff_singleton, (hC.sdiff_singleton_indep he).isBasis_insert_iff,
    insert_sdiff_singleton, insert_eq_of_mem he]
  exact Or.inl hC.dep

@[deprecated (since := "2026-06-03")]
alias IsCircuit.diff_singleton_isBasis := IsCircuit.sdiff_singleton_isBasis

lemma IsCircuit.isBasis_iff_eq_sdiff_singleton (hC : M.IsCircuit C) :
    M.IsBasis I C ↔ ∃ e ∈ C, I = C \ {e} := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨e, he⟩ := exists_of_ssubset
      (h.subset.ssubset_of_ne (by rintro rfl; exact hC.dep.not_indep h.indep))
    exact ⟨e, he.1, h.eq_of_subset_indep (hC.sdiff_singleton_indep he.1)
      (subset_sdiff_singleton h.subset he.2) sdiff_subset⟩
  rintro ⟨e, he, rfl⟩
  exact hC.sdiff_singleton_isBasis he

@[deprecated (since := "2026-06-03")]
alias IsCircuit.isBasis_iff_eq_diff_singleton := IsCircuit.isBasis_iff_eq_sdiff_singleton

lemma IsCircuit.isBasis_iff_insert_eq (hC : M.IsCircuit C) :
    M.IsBasis I C ↔ ∃ e ∈ C \ I, C = insert e I := by
  rw [hC.isBasis_iff_eq_sdiff_singleton]
  refine ⟨fun ⟨e, he, hI⟩ ↦ ⟨e, ⟨he, fun heI ↦ (hI.subset heI).2 rfl⟩, ?_⟩,
    fun ⟨e, he, hC⟩ ↦ ⟨e, he.1, ?_⟩⟩
  · rw [hI, insert_sdiff_singleton, insert_eq_of_mem he]
  rw [hC, insert_sdiff_self_of_notMem he.2]

/-! ### Restriction -/

lemma IsCircuit.isCircuit_restrict_of_subset (hC : M.IsCircuit C) (hCR : C ⊆ R) :
    (M ↾ R).IsCircuit C := by
  simp_rw [isCircuit_iff, restrict_dep_iff, dep_iff, and_imp] at *
  exact ⟨⟨hC.1.1, hCR⟩, fun I hI _ hIC ↦ hC.2 hI (hIC.trans hC.1.2) hIC⟩

lemma restrict_isCircuit_iff (hR : R ⊆ M.E := by aesop_mat) :
    (M ↾ R).IsCircuit C ↔ M.IsCircuit C ∧ C ⊆ R := by
  refine ⟨?_, fun h ↦ h.1.isCircuit_restrict_of_subset h.2⟩
  simp_rw [isCircuit_iff, restrict_dep_iff, and_imp, dep_iff]
  exact fun hC hCR h ↦ ⟨⟨⟨hC,hCR.trans hR⟩,fun I hI hIC ↦ h hI.1 (hIC.trans hCR) hIC⟩,hCR⟩

/-! ### Fundamental IsCircuits -/

/-- The data for the fundamental circuit of `e` and `I`: `I` is independent and `e` is in the
closure of `I` but not in `I`. Then `insert e I` is dependent and contains a unique circuit,
`M.fundCircuit e I`. -/
structure FundCircuitExists (M : Matroid α) (e : α) (I : Set α) : Prop where
  /-- The set is independent. -/
  indep : M.Indep I
  /-- The element is in the closure of the set. -/
  mem_closure : e ∈ M.closure I
  /-- The element is not in the set. -/
  notMem : e ∉ I

lemma Indep.fundCircuitExists_iff (hI : M.Indep I) :
    M.FundCircuitExists e I ↔ e ∈ M.closure I ∧ e ∉ I :=
  ⟨fun h ↦ ⟨h.mem_closure, h.notMem⟩, fun h ↦ ⟨hI, h.1, h.2⟩⟩

lemma IsBase.fundCircuitExists {B : Set α} (hB : M.IsBase B) (heE : e ∈ M.E) (heB : e ∉ B) :
    M.FundCircuitExists e B :=
  ⟨hB.indep, by rwa [hB.closure_eq], heB⟩

lemma FundCircuitExists.mem_ground (h : M.FundCircuitExists e I) : e ∈ M.E :=
  mem_ground_of_mem_closure h.mem_closure

/-- For an independent set `I` and some `e ∈ M.closure I \ I`, which `h` states,
`M.fundCircuit e I h` is the unique circuit contained in `insert e I`.
For the fact that this is a circuit, see `Matroid.fundCircuit_isCircuit`,
and the fact that it is unique, see `Matroid.IsCircuit.eq_fundCircuit_of_subset`. -/
@[nolint unusedArguments]
def fundCircuit (M : Matroid α) (e : α) (I : Set α) (_h : M.FundCircuitExists e I) : Set α :=
  insert e (⋂₀ {J | J ⊆ I ∧ e ∈ M.closure J})

lemma fundCircuit_eq_sInter (h : M.FundCircuitExists e I) :
    M.fundCircuit e I h = insert e (⋂₀ {J | J ⊆ I ∧ e ∈ M.closure J}) :=
  rfl

lemma fundCircuit_subset_insert (h : M.FundCircuitExists e I) :
    M.fundCircuit e I h ⊆ insert e I :=
  insert_subset_insert (sInter_subset_of_mem ⟨Subset.rfl, h.mem_closure⟩)

lemma fundCircuit_subset_ground (h : M.FundCircuitExists e I) : M.fundCircuit e I h ⊆ M.E :=
  (fundCircuit_subset_insert h).trans (insert_subset h.mem_ground h.indep.subset_ground)

lemma mem_fundCircuit (h : M.FundCircuitExists e I) : e ∈ M.fundCircuit e I h :=
  mem_insert ..

lemma fundCircuit_sdiff_eq_inter (h : M.FundCircuitExists e I) :
    (M.fundCircuit e I h) \ {e} = (M.fundCircuit e I h) ∩ I :=
  (subset_inter sdiff_subset (by simp [fundCircuit_subset_insert h])).antisymm
    (subset_sdiff_singleton inter_subset_left (by simp [h.notMem]))

@[deprecated (since := "2026-06-03")] alias fundCircuit_diff_eq_inter := fundCircuit_sdiff_eq_inter

lemma fundCircuit_isCircuit (h : M.FundCircuitExists e I) :
    M.IsCircuit (M.fundCircuit e I h) := by
  have aux : ⋂₀ {J | J ⊆ I ∧ e ∈ M.closure J} ⊆ I :=
    sInter_subset_of_mem ⟨Subset.rfl, h.mem_closure⟩
  rw [fundCircuit_eq_sInter h]
  refine (h.indep.subset aux).insert_isCircuit_of_forall ?_ ?_ ?_
  · simp [show ∃ x ⊆ I, e ∈ M.closure x ∧ e ∉ x from ⟨I, by simp [h.mem_closure, h.notMem]⟩]
  · rw [h.indep.closure_sInter_eq_biInter_closure_of_forall_subset ⟨I, by simp [h.mem_closure]⟩
      (by simp +contextual)]
    simp
  simp only [mem_sInter, mem_ofPred_eq, and_imp]
  exact fun f hf hecl ↦ (hf _ (sdiff_subset.trans aux) hecl).2 rfl

lemma mem_fundCircuit_iff (h : M.FundCircuitExists e I) :
    x ∈ M.fundCircuit e I h ↔ M.Indep (insert e I \ {x}) := by
  obtain rfl | hne := eq_or_ne x e
  · simp [h.indep.sdiff, mem_fundCircuit]
  suffices (∀ t ⊆ I, e ∈ M.closure t → x ∈ t) ↔ e ∉ M.closure (I \ {x}) by
    simpa [fundCircuit_eq_sInter h, hne, ← insert_sdiff_singleton_comm hne.symm,
      (h.indep.sdiff _).insert_indep_iff, h.mem_ground, h.notMem]
  refine ⟨fun h hecl ↦ (h _ sdiff_subset hecl).2 rfl, fun h J hJ heJ ↦ by_contra fun hxJ ↦ h ?_⟩
  exact M.closure_subset_closure (subset_sdiff_singleton hJ hxJ) heJ

/-- A circuit contained in `insert e I` for an independent set `I` contains `e`, and `e` is then
in the closure of `I` but not in `I`. -/
lemma IsCircuit.fundCircuitExists_of_subset (hC : M.IsCircuit C) (hI : M.Indep I)
    (hCs : C ⊆ insert e I) : M.FundCircuitExists e I := by
  obtain hCI | ⟨heC, hCeI⟩ := subset_insert_iff.1 hCs
  · exact (hC.not_indep (hI.subset hCI)).elim
  refine ⟨hI, M.closure_subset_closure hCeI ((hC.sdiff_singleton_isBasis heC).subset_closure heC),
    fun heI ↦ hC.not_indep (hI.subset (hCs.trans (by simp [heI])))⟩

/-- For `I` independent, `M.fundCircuit e I` is the only circuit contained in `insert e I`. -/
lemma IsCircuit.eq_fundCircuit_of_subset (hC : M.IsCircuit C) (hI : M.Indep I)
    (hCs : C ⊆ insert e I) : C = M.fundCircuit e I (hC.fundCircuitExists_of_subset hI hCs) := by
  have h := hC.fundCircuitExists_of_subset hI hCs
  obtain hCI | ⟨heC, hCeI⟩ := subset_insert_iff.1 hCs
  · exact (hC.not_indep (hI.subset hCI)).elim
  suffices hss : M.fundCircuit e I h ⊆ C from
    hC.eq_of_superset_isCircuit (fundCircuit_isCircuit h) hss
  have heCcl := (hC.sdiff_singleton_isBasis heC).subset_closure heC
  rw [fundCircuit_eq_sInter h]
  refine insert_subset heC <| (sInter_subset_of_mem (t := C \ {e}) ?_).trans sdiff_subset
  exact ⟨hCeI, heCcl⟩

lemma FundCircuitExists.restrict {R : Set α} (h : M.FundCircuitExists e I) (hIR : I ⊆ R)
    (heR : e ∈ R) : (M ↾ R).FundCircuitExists e I := by
  refine ⟨(restrict_indep_iff).2 ⟨h.indep, hIR⟩, ?_, h.notMem⟩
  rw [restrict_closure_eq', inter_eq_self_of_subset_left hIR]
  exact .inl ⟨h.mem_closure, heR⟩

lemma fundCircuit_restrict {R : Set α} (h : M.FundCircuitExists e I) (hIR : I ⊆ R)
    (heR : e ∈ R) (hR : R ⊆ M.E) :
    (M ↾ R).fundCircuit e I (h.restrict hIR heR) = M.fundCircuit e I h := by
  simp_rw [fundCircuit_eq_sInter]
  congr 2
  ext J
  simp only [mem_ofPred_eq, and_congr_right_iff]
  intro hJI
  rw [restrict_closure_eq _ (hJI.trans hIR) hR]
  simp [heR]

/-! ### Dependence -/

lemma Dep.exists_isCircuit_subset (hX : M.Dep X) : ∃ C, C ⊆ X ∧ M.IsCircuit C := by
  obtain ⟨I, hI⟩ := M.exists_isBasis X
  obtain ⟨e, heX, heI⟩ := exists_of_ssubset
    (hI.subset.ssubset_of_ne (by rintro rfl; exact hI.indep.not_dep hX))
  have h : M.FundCircuitExists e I := ⟨hI.indep, hI.subset_closure heX, heI⟩
  exact ⟨M.fundCircuit e I h, (fundCircuit_subset_insert h).trans (insert_subset heX hI.subset),
    fundCircuit_isCircuit h⟩

lemma dep_iff_superset_isCircuit (hX : X ⊆ M.E := by aesop_mat) :
    M.Dep X ↔ ∃ C, C ⊆ X ∧ M.IsCircuit C :=
  ⟨Dep.exists_isCircuit_subset, fun ⟨C, hCX, hC⟩ ↦ hC.dep.superset hCX⟩

/-- A version of `Matroid.dep_iff_superset_isCircuit` that has the ground-set hypothesis
as part of the equivalence, rather than a hypothesis. -/
lemma dep_iff_superset_isCircuit' : M.Dep X ↔ (∃ C, C ⊆ X ∧ M.IsCircuit C) ∧ X ⊆ M.E :=
  ⟨fun h ↦ ⟨h.exists_isCircuit_subset, h.subset_ground⟩,
    fun ⟨⟨C, hCX, hC⟩, h⟩ ↦ hC.dep.superset hCX⟩

/-- A version of `Matroid.indep_iff_forall_subset_not_isCircuit` that has the ground-set
hypothesis as part of the equivalence, rather than a hypothesis. -/
lemma indep_iff_forall_subset_not_isCircuit' :
    M.Indep I ↔ (∀ C, C ⊆ I → ¬M.IsCircuit C) ∧ I ⊆ M.E := by
  simp_rw [indep_iff_not_dep, dep_iff_superset_isCircuit']
  aesop

lemma indep_iff_forall_subset_not_isCircuit (hI : I ⊆ M.E := by aesop_mat) :
    M.Indep I ↔ ∀ C, C ⊆ I → ¬M.IsCircuit C := by
  rw [indep_iff_forall_subset_not_isCircuit', and_iff_left hI]

/-! ### Closure -/

lemma IsCircuit.closure_sdiff_singleton_eq (hC : M.IsCircuit C) (e : α) :
    M.closure (C \ {e}) = M.closure C :=
  (em (e ∈ C)).elim
    (fun he ↦ by rw [(hC.sdiff_singleton_isBasis he).closure_eq_closure])
    (fun he ↦ by rw [sdiff_singleton_eq_self he])

@[deprecated (since := "2026-06-03")]
alias IsCircuit.closure_diff_singleton_eq := IsCircuit.closure_sdiff_singleton_eq

lemma IsCircuit.subset_closure_sdiff_singleton (hC : M.IsCircuit C) (e : α) :
    C ⊆ M.closure (C \ {e}) := by
  rw [hC.closure_sdiff_singleton_eq]
  exact M.subset_closure _ hC.subset_ground

@[deprecated (since := "2026-06-03")]
alias IsCircuit.subset_closure_diff_singleton := IsCircuit.subset_closure_sdiff_singleton

lemma IsCircuit.mem_closure_sdiff_singleton_of_mem (hC : M.IsCircuit C) (heC : e ∈ C) :
    e ∈ M.closure (C \ {e}) :=
  hC.subset_closure_sdiff_singleton e heC

@[deprecated (since := "2026-06-03")]
alias IsCircuit.mem_closure_diff_singleton_of_mem := IsCircuit.mem_closure_sdiff_singleton_of_mem

lemma exists_isCircuit_of_mem_closure (he : e ∈ M.closure X) (heX : e ∉ X) :
    ∃ C ⊆ insert e X, M.IsCircuit C ∧ e ∈ C :=
  let ⟨I, hI⟩ := M.exists_isBasis' X
  have h : M.FundCircuitExists e I :=
    ⟨hI.indep, by rwa [hI.closure_eq_closure], notMem_subset hI.subset heX⟩
  ⟨_, (fundCircuit_subset_insert h).trans (insert_subset_insert hI.subset),
    fundCircuit_isCircuit h, mem_fundCircuit h⟩

lemma mem_closure_iff_exists_isCircuit (he : e ∉ X) :
    e ∈ M.closure X ↔ ∃ C ⊆ insert e X, M.IsCircuit C ∧ e ∈ C :=
  ⟨fun h ↦ exists_isCircuit_of_mem_closure h he, fun ⟨C, hCX, hC, heC⟩ ↦ mem_of_mem_of_subset
    (hC.mem_closure_sdiff_singleton_of_mem heC) (M.closure_subset_closure (by simpa))⟩

/-! ### Extensionality -/

lemma ext_isCircuit {M₁ M₂ : Matroid α} (hE : M₁.E = M₂.E)
    (h : ∀ ⦃C⦄, C ⊆ M₁.E → (M₁.IsCircuit C ↔ M₂.IsCircuit C)) : M₁ = M₂ := by
  have h' {C} : M₁.IsCircuit C ↔ M₂.IsCircuit C :=
    (em (C ⊆ M₁.E)).elim (h (C := C)) (fun hC ↦ iff_of_false (mt IsCircuit.subset_ground hC)
      (mt IsCircuit.subset_ground fun hss ↦ hC (hss.trans_eq hE.symm)))
  refine ext_indep hE fun I hI ↦ ?_
  simp_rw [indep_iff_forall_subset_not_isCircuit hI, h',
    indep_iff_forall_subset_not_isCircuit (hI.trans_eq hE)]

/-- A stronger version of `Matroid.ext_isCircuit`:
two matroids on the same ground set are equal if no circuit of one is independent in the other. -/
lemma ext_isCircuit_not_indep {M₁ M₂ : Matroid α} (hE : M₁.E = M₂.E)
    (h₁ : ∀ C, M₁.IsCircuit C → ¬ M₂.Indep C) (h₂ : ∀ C, M₂.IsCircuit C → ¬ M₁.Indep C) :
    M₁ = M₂ := by
  refine ext_isCircuit hE fun C hCE ↦ ⟨fun hC ↦ ?_, fun hC ↦ ?_⟩
  · obtain ⟨C', hC'C, hC'⟩ := ((not_indep_iff (by rwa [← hE])).1 (h₁ C hC)).exists_isCircuit_subset
    rwa [← hC.eq_of_not_indep_subset (h₂ C' hC') hC'C]
  obtain ⟨C', hC'C, hC'⟩ := ((not_indep_iff hCE).1 (h₂ C hC)).exists_isCircuit_subset
  rwa [← hC.eq_of_not_indep_subset (h₁ C' hC') hC'C]

lemma ext_iff_isCircuit {M₁ M₂ : Matroid α} :
    M₁ = M₂ ↔ M₁.E = M₂.E ∧ ∀ C, M₁.IsCircuit C ↔ M₂.IsCircuit C :=
  ⟨fun h ↦ by simp [h], fun h ↦ ext_isCircuit h.1 fun C hC ↦ h.2 (C := C)⟩

section Elimination

/-! ### Circuit Elimination -/

variable {ι : Type*} {J C₀ C₁ C₂ : Set α}

/-- A version of `Matroid.IsCircuit.strong_multi_elimination` that is phrased using insertion. -/
lemma IsCircuit.strong_multi_elimination_insert (x : ι → α) (I : ι → Set α) (z : α)
    (hxI : ∀ i, x i ∉ I i) (hC : ∀ i, M.IsCircuit (insert (x i) (I i)))
    (hJx : M.IsCircuit (J ∪ range x)) (hzJ : z ∈ J) (hzI : ∀ i, z ∉ I i) :
    ∃ C' ⊆ J ∪ ⋃ i, I i, M.IsCircuit C' ∧ z ∈ C' := by
  -- we may assume that `ι` is nonempty, and it suffices to show that
  -- `z` is spanned by the union of the `I` and `J \ {z}`.
  obtain hι | hι := isEmpty_or_nonempty ι
  · exact ⟨J, by simp, by simpa [range_eq_empty] using hJx, hzJ⟩
  suffices hcl : z ∈ M.closure ((⋃ i, I i) ∪ (J \ {z})) by
    rw [mem_closure_iff_exists_isCircuit (by simp [hzI])] at hcl
    obtain ⟨C', hC'ss, hC', hzC'⟩ := hcl
    refine ⟨C', ?_, hC', hzC'⟩
    rwa [union_comm, ← insert_union, insert_sdiff_singleton, insert_eq_of_mem hzJ] at hC'ss
  have hC' (i) : M.closure (I i) = M.closure (insert (x i) (I i)) := by
    simpa [sdiff_singleton_eq_self (hxI _)] using (hC i).closure_sdiff_singleton_eq (x i)
  -- This is true because each `I i` spans `x i` and `(range x) ∪ (J \ {z})` spans `z`.
  rw [closure_union_congr_left <| closure_iUnion_congr _ _ hC',
    iUnion_insert_eq_range_union_iUnion, union_right_comm]
  refine mem_of_mem_of_subset (hJx.mem_closure_sdiff_singleton_of_mem (.inl hzJ))
    (M.closure_subset_closure (subset_trans ?_ subset_union_left))
  rw [union_sdiff_distrib, union_comm]
  exact union_subset_union_left _ sdiff_subset

/-- A generalization of the strong circuit elimination axiom `Matroid.IsCircuit.strong_elimination`
to an infinite collection of circuits.

It states that, given a circuit `C₀`, an arbitrary collection `C : ι → Set α` of circuits,
an element `x i` of `C₀ ∩ C i` for each `i`, and an element `z ∈ C₀` outside all the `C i`,
the union of `C₀` and the `C i` contains a circuit containing `z` but none of the `x i`.

This is one of the axioms when defining infinite matroids via circuits.

TODO : A similar statement will hold even when all mentions of `z` are removed. -/
lemma IsCircuit.strong_multi_elimination (hC₀ : M.IsCircuit C₀) (x : ι → α) (C : ι → Set α) (z : α)
    (hC : ∀ i, M.IsCircuit (C i)) (h_mem_C₀ : ∀ i, x i ∈ C₀) (h_mem : ∀ i, x i ∈ C i)
    (h_unique : ∀ ⦃i i'⦄, x i ∈ C i' → i = i') (hzC₀ : z ∈ C₀) (hzC : ∀ i, z ∉ C i) :
    ∃ C' ⊆ (C₀ ∪ ⋃ i, C i) \ range x, M.IsCircuit C' ∧ z ∈ C' := by
  have hwin := IsCircuit.strong_multi_elimination_insert (M := M) x (fun i ↦ (C i \ {x i}))
    (J := C₀ \ range x) (z := z) (by simp) (fun i ↦ ?_) ?_ ⟨hzC₀, ?_⟩ ?_
  · obtain ⟨C', hC'ss, hC', hzC'⟩ := hwin
    refine ⟨C', hC'ss.trans ?_, hC', hzC'⟩
    refine union_subset (sdiff_subset_sdiff_left subset_union_left)
      (iUnion_subset fun i ↦ subset_sdiff.2
        ⟨sdiff_subset.trans (subset_union_of_subset_right (subset_iUnion ..) _), ?_⟩)
    rw [disjoint_iff_forall_ne]
    rintro _ he _ ⟨j, hj, rfl⟩ rfl
    obtain rfl : j = i := h_unique he.1
    simp at he
  · simpa [insert_eq_of_mem (h_mem i)] using hC i
  · rwa [sdiff_union_self, union_eq_self_of_subset_right]
    rintro _ ⟨i, hi, rfl⟩
    exact h_mem_C₀ i
  · rintro ⟨i, hi, rfl⟩
    exact hzC _ (h_mem i)
  simp only [mem_sdiff, mem_singleton_iff, not_and, not_not]
  exact fun i hzi ↦ (hzC i hzi).elim

/-- A version of `Circuit.strong_multi_elimination` where the collection of circuits is
a `Set (Set α)` and the distinguished elements are a `Set α`, rather than both being indexed. -/
lemma IsCircuit.strong_multi_elimination_set (hC₀ : M.IsCircuit C₀) (X : Set α) (S : Set (Set α))
    (z : α) (hCS : ∀ C ∈ S, M.IsCircuit C) (hXC₀ : X ⊆ C₀) (hX : ∀ x ∈ X, ∃ C ∈ S, C ∩ X = {x})
    (hzC₀ : z ∈ C₀) (hz : ∀ C ∈ S, z ∉ C) : ∃ C' ⊆ (C₀ ∪ ⋃₀ S) \ X, M.IsCircuit C' ∧ z ∈ C' := by
  choose! C hC using hX
  simp only [forall_and] at hC
  have hwin := hC₀.strong_multi_elimination (fun x : X ↦ x) (fun x ↦ C x) z ?_ ?_ ?_ ?_ hzC₀ ?_
  · obtain ⟨C', hC'ss, hC', hz⟩ := hwin
    refine ⟨C', hC'ss.trans (sdiff_subset_sdiff (union_subset_union_right _ ?_) (by simp)), hC', hz⟩
    simpa using fun e heX ↦ (subset_sUnion_of_mem (hC.1 e heX))
  · simpa using fun e heX ↦ hCS _ <| hC.1 e heX
  · simpa using fun e heX ↦ hXC₀ heX
  · simp only [Subtype.forall, ← singleton_subset_iff (s := C _)]
    exact fun e heX ↦ by simp [← hC.2 e heX]
  · simp only [Subtype.forall, Subtype.mk.injEq]
    refine fun e heX f hfX hef ↦ ?_
    simpa [hC.2 f hfX] using subset_inter (singleton_subset_iff.2 hef) (singleton_subset_iff.2 heX)
  simpa using fun e heX heC ↦ hz _ (hC.1 e heX) heC

/-- The strong isCircuit elimination axiom. For any pair of distinct circuits `C₁, C₂` and all
`e ∈ C₁ ∩ C₂` and `f ∈ C₁ \ C₂`, there is a circuit `C` with `f ∈ C ⊆ (C₁ ∪ C₂) \ {e}`. -/
lemma IsCircuit.strong_elimination (hC₁ : M.IsCircuit C₁) (hC₂ : M.IsCircuit C₂) (heC₁ : e ∈ C₁)
    (heC₂ : e ∈ C₂) (hfC₁ : f ∈ C₁) (hfC₂ : f ∉ C₂) :
    ∃ C ⊆ (C₁ ∪ C₂) \ {e}, M.IsCircuit C ∧ f ∈ C := by
  obtain ⟨C, hCs, hC, hfC⟩ := hC₁.strong_multi_elimination (fun i : Unit ↦ e) (fun _ ↦ C₂) f
    (by simpa) (by simpa) (by simpa) (by simp) (by simpa) (by simpa)
  exact ⟨C, hCs.trans (sdiff_subset_sdiff (by simp) (by simp)), hC, hfC⟩

/-- The circuit elimination axiom : for any pair of distinct circuits `C₁, C₂` and any `e`,
some circuit is contained in `(C₁ ∪ C₂) \ {e}`.

This is one of the axioms when defining a finitary matroid via circuits;
as an axiom, it is usually stated with the extra assumption that `e ∈ C₁ ∩ C₂`. -/
lemma IsCircuit.elimination (hC₁ : M.IsCircuit C₁) (hC₂ : M.IsCircuit C₂) (h : C₁ ≠ C₂) (e : α) :
    ∃ C ⊆ (C₁ ∪ C₂) \ {e}, M.IsCircuit C := by
  have hnss : ¬ (C₁ ⊆ C₂) := fun hss ↦ h <| hC₁.eq_of_subset_isCircuit hC₂ hss
  obtain ⟨f, hf₁, hf₂⟩ := not_subset.1 hnss
  by_cases he₁ : e ∈ C₁
  · by_cases he₂ : e ∈ C₂
    · obtain ⟨C, hC, hC', -⟩ := hC₁.strong_elimination hC₂ he₁ he₂ hf₁ hf₂
      exact ⟨C, hC, hC'⟩
    exact ⟨C₂, subset_sdiff_singleton subset_union_right he₂, hC₂⟩
  exact ⟨C₁, subset_sdiff_singleton subset_union_left he₁, hC₁⟩

end Elimination

/-! ### Finitary Matroids -/
section Finitary

lemma IsCircuit.finite [Finitary M] (hC : M.IsCircuit C) : C.Finite := by
  have hi := hC.dep.not_indep
  rw [indep_iff_forall_finite_subset_indep] at hi; push Not at hi
  obtain ⟨J, hJC, hJfin, hJ⟩ := hi
  rwa [← hC.eq_of_not_indep_subset hJ hJC]

lemma finitary_iff_forall_isCircuit_finite : M.Finitary ↔ ∀ C, M.IsCircuit C → C.Finite := by
  refine ⟨fun _ _ ↦ IsCircuit.finite, fun h ↦
    ⟨fun I hI ↦ indep_iff_not_dep.2 ⟨fun hd ↦ ?_,fun x hx ↦ ?_⟩⟩⟩
  · obtain ⟨C, hCI, hC⟩ := hd.exists_isCircuit_subset
    exact hC.dep.not_indep <| hI _ hCI (h C hC)
  simpa using (hI {x} (by simpa) (finite_singleton _)).subset_ground

/-- In a finitary matroid, every element spanned by a set `X` is in fact
spanned by a finite independent subset of `X`. -/
lemma exists_mem_finite_closure_of_mem_closure [M.Finitary] (he : e ∈ M.closure X) :
    ∃ I ⊆ X, I.Finite ∧ M.Indep I ∧ e ∈ M.closure I := by
  by_cases heY : e ∈ X
  · obtain ⟨J, hJ⟩ := M.exists_isBasis {e}
    exact ⟨J, hJ.subset.trans (by simpa), (finite_singleton e).subset hJ.subset, hJ.indep,
      by simpa using hJ.subset_closure⟩
  obtain ⟨C, hCs, hC, heC⟩ := exists_isCircuit_of_mem_closure he heY
  exact ⟨C \ {e}, by simpa, hC.finite.sdiff, hC.sdiff_singleton_indep heC,
    hC.mem_closure_sdiff_singleton_of_mem heC⟩

/-- In a finitary matroid, each finite set `X` spanned by a set `Y` is in fact
spanned by a finite independent subset of `Y`. -/
lemma exists_subset_finite_closure_of_subset_closure [M.Finitary] (hX : X.Finite)
    (hXY : X ⊆ M.closure Y) : ∃ I ⊆ Y, I.Finite ∧ M.Indep I ∧ X ⊆ M.closure I := by
  suffices aux : ∃ T ⊆ Y, T.Finite ∧ X ⊆ M.closure T by
    obtain ⟨T, hT, hTfin, hXT⟩ := aux
    obtain ⟨I, hI⟩ := M.exists_isBasis' T
    exact ⟨_, hI.subset.trans hT, hTfin.subset hI.subset, hI.indep, by rwa [hI.closure_eq_closure]⟩
  refine Finite.induction_on_subset X hX ⟨∅, by simp⟩ (fun {e Z} heX _ heZ ⟨T, hTY, hTfin, hT⟩ ↦ ?_)
  obtain ⟨S, hSY, hSfin, -, heS⟩ := exists_mem_finite_closure_of_mem_closure (hXY heX)
  exact ⟨S ∪ T, union_subset hSY hTY, hSfin.union hTfin, insert_subset
    (M.closure_mono subset_union_left heS) (hT.trans (M.closure_mono subset_union_right))⟩

end Finitary

/-! ### IsCocircuits -/
section IsCocircuit

variable {K B : Set α}

/-- A cocircuit is a circuit of the dual matroid,
or equivalently the complement of a hyperplane. -/
abbrev IsCocircuit (M : Matroid α) (K : Set α) : Prop := M✶.IsCircuit K

lemma isCocircuit_def : M.IsCocircuit K ↔ M✶.IsCircuit K := Iff.rfl

lemma IsCocircuit.isCircuit (hK : M.IsCocircuit K) : M✶.IsCircuit K :=
  hK

lemma IsCircuit.isCocircuit (hC : M.IsCircuit C) : M✶.IsCocircuit C := by
  rwa [isCocircuit_def, dual_dual]

lemma IsCocircuit.nonempty (hC : M.IsCocircuit C) : C.Nonempty :=
  hC.isCircuit.nonempty

@[aesop unsafe 10% (rule_sets := [Matroid])]
lemma IsCocircuit.subset_ground (hC : M.IsCocircuit C) : C ⊆ M.E :=
  hC.isCircuit.subset_ground

@[simp] lemma dual_isCocircuit_iff : M✶.IsCocircuit C ↔ M.IsCircuit C := by
  rw [isCocircuit_def, dual_dual]

lemma coindep_iff_forall_subset_not_isCocircuit :
    M.Coindep X ↔ (∀ K, K ⊆ X → ¬M.IsCocircuit K) ∧ X ⊆ M.E :=
  indep_iff_forall_subset_not_isCircuit'

/-- A cocircuit is a minimal set that intersects every base. -/
lemma isCocircuit_iff_minimal :
    M.IsCocircuit K ↔ Minimal (fun X ↦ ∀ B, M.IsBase B → (X ∩ B).Nonempty) K := by
  have aux : M✶.Dep = fun X ↦ (∀ B, M.IsBase B → (X ∩ B).Nonempty) ∧ X ⊆ M.E := by
    ext; apply dual_dep_iff_forall
  rw [isCocircuit_def, isCircuit_def, aux, iff_comm]
  refine minimal_iff_minimal_of_imp_of_forall (fun _ h ↦ h.1) fun X hX ↦
    ⟨X ∩ M.E, inter_subset_left, fun B hB ↦ ?_, inter_subset_right⟩
  rw [inter_assoc, inter_eq_self_of_subset_right hB.subset_ground]
  exact hX B hB

/-- A cocircuit is a minimal set whose complement is nonspanning. -/
lemma isCocircuit_iff_minimal_compl_nonspanning :
    M.IsCocircuit K ↔ Minimal (fun X ↦ ¬ M.Spanning (M.E \ X)) K := by
  convert! isCocircuit_iff_minimal with K
  rw [spanning_iff_exists_isBase_subset]
  simp_rw [not_exists, subset_sdiff, not_and, not_disjoint_iff_nonempty_inter, ← and_imp,
    and_iff_left_of_imp IsBase.subset_ground, inter_comm K]

/-- For an element `e` of a base `B`, the complement of the closure of `B \ {e}` is a cocircuit. -/
lemma IsBase.compl_closure_sdiff_singleton_isCocircuit (hB : M.IsBase B) (he : e ∈ B) :
    M.IsCocircuit (M.E \ M.closure (B \ {e})) := by
  rw [isCocircuit_iff_minimal_compl_nonspanning, minimal_subset_iff,
    sdiff_sdiff_cancel_left (M.closure_subset_ground _),
    closure_spanning_iff (sdiff_subset.trans hB.subset_ground)]
  have hB' := (isBase_iff_minimal_spanning.1 hB)
  refine ⟨fun hsp ↦ hB'.notMem_of_prop_sdiff_singleton hsp he, fun X hX hXss ↦ hXss.antisymm' ?_⟩
  rw [sdiff_subset_comm]
  refine fun f hf ↦ by_contra fun fcl ↦ hX ?_
  rw [subset_sdiff] at hXss
  suffices hsp : M.IsBase (insert f (B \ {e})) by
    refine hsp.spanning.superset <| insert_subset hf <|
      (M.subset_closure _ (sdiff_subset.trans hB.subset_ground)).trans ?_
    rw [subset_sdiff, and_iff_left hXss.2.symm]
    apply closure_subset_ground
  exact hB.exchange_base_of_notMem_closure he fcl

@[deprecated (since := "2026-06-03")]
alias IsBase.compl_closure_diff_singleton_isCocircuit :=
  IsBase.compl_closure_sdiff_singleton_isCocircuit

/-- A version of `Matroid.isCocircuit_iff_minimal_compl_nonspanning` with a support assumption
in the minimality. -/
lemma isCocircuit_iff_minimal_compl_nonspanning' :
    M.IsCocircuit K ↔ Minimal (fun X ↦ ¬ M.Spanning (M.E \ X) ∧ X ⊆ M.E) K := by
  rw [isCocircuit_iff_minimal_compl_nonspanning]
  exact minimal_iff_minimal_of_imp_of_forall (fun _ h ↦ h.1)
    (fun X hX ↦ ⟨X ∩ M.E, inter_subset_left, by rwa [sdiff_inter_self_eq_sdiff],
      inter_subset_right⟩)

/-- A cocircuit and a circuit cannot meet in exactly one element. -/
lemma IsCircuit.inter_isCocircuit_ne_singleton (hC : M.IsCircuit C) (hK : M.IsCocircuit K) :
    C ∩ K ≠ {e} := by
  intro he
  have heC : e ∈ C := (he.symm.subset rfl).1
  simp_rw [isCocircuit_iff_minimal_compl_nonspanning, minimal_iff_forall_ssubset, not_not] at hK
  have' hKe := hK.2 (t := K \ {e}) (sdiff_singleton_ssubset.2 (he.symm.subset rfl).2)
  apply hK.1
  rw [spanning_iff_ground_subset_closure]
  nth_rw 1 [← hKe.closure_eq, sdiff_sdiff_eq_sdiff_union]
  · refine (M.closure_subset_closure (subset_union_left (t := C))).trans ?_
    rw [union_assoc, singleton_union, insert_eq_of_mem heC, ← closure_union_congr_right
      (hC.closure_sdiff_singleton_eq e), union_eq_self_of_subset_right]
    rw [← he, sdiff_self_inter]
    exact sdiff_subset_sdiff_left hC.subset_ground
  rw [← he]
  exact inter_subset_left.trans hC.subset_ground

lemma IsCircuit.isCocircuit_inter_nontrivial (hC : M.IsCircuit C) (hK : M.IsCocircuit K)
    (hCK : (C ∩ K).Nonempty) : (C ∩ K).Nontrivial := by
  obtain ⟨e, heCK⟩ := hCK
  rw [nontrivial_iff_ne_singleton heCK]
  exact hC.inter_isCocircuit_ne_singleton hK

lemma IsCircuit.isCocircuit_disjoint_or_nontrivial_inter (hC : M.IsCircuit C)
    (hK : M.IsCocircuit K) : Disjoint C K ∨ (C ∩ K).Nontrivial := by
  rw [or_iff_not_imp_left, disjoint_iff_inter_eq_empty, ← ne_eq, ← nonempty_iff_ne_empty]
  exact hC.isCocircuit_inter_nontrivial hK

lemma dual_rankPos_iff_exists_isCircuit : M✶.RankPos ↔ ∃ C, M.IsCircuit C := by
  rw [rankPos_iff, dual_isBase_iff, sdiff_empty, not_iff_comm, not_exists,
    ← ground_indep_iff_isBase, indep_iff_forall_subset_not_isCircuit]
  exact ⟨fun h C _ ↦ h C, fun h C hC ↦ h C hC.subset_ground hC⟩

lemma IsCircuit.dual_rankPos (hC : M.IsCircuit C) : M✶.RankPos :=
  dual_rankPos_iff_exists_isCircuit.mpr ⟨C, hC⟩

lemma exists_isCircuit [RankPos M✶] : ∃ C, M.IsCircuit C :=
  dual_rankPos_iff_exists_isCircuit.1 (by assumption)

lemma rankPos_iff_exists_isCocircuit : M.RankPos ↔ ∃ K, M.IsCocircuit K := by
  rw [← dual_dual M, dual_rankPos_iff_exists_isCircuit, dual_dual M]

/-- The data for the fundamental cocircuit of `e` and `B`: `B` is spanning, `e ∈ B`, and `B \ {e}`
is not spanning. For a base `B`, this holds for every `e ∈ B`. -/
structure FundCocircuitExists (M : Matroid α) (e : α) (B : Set α) : Prop where
  /-- The set is spanning. -/
  spanning : M.Spanning B
  /-- The element is in the set. -/
  mem : e ∈ B
  /-- The set without the element is not spanning. -/
  not_spanning_sdiff : ¬ M.Spanning (B \ {e})

lemma IsBase.fundCocircuitExists {B : Set α} (hB : M.IsBase B) (he : e ∈ B) :
    M.FundCocircuitExists e B := by
  refine ⟨hB.spanning, he, fun h ↦ ?_⟩
  have hB' : M.IsBase (B \ {e}) := h.isBase_of_indep (hB.indep.subset sdiff_subset)
  have : e ∈ B \ {e} := (hB'.eq_of_subset_isBase hB sdiff_subset).symm ▸ he
  exact this.2 rfl

lemma FundCocircuitExists.dual {B : Set α} (h : M.FundCocircuitExists e B) :
    M✶.FundCircuitExists e (M✶.E \ B) := by
  have hBE : B ⊆ M.E := h.spanning.subset_ground
  have heE : e ∈ M.E := hBE h.mem
  have hcoind : M✶.Indep (M.E \ B) := by
    rw [← coindep_def, coindep_iff_compl_spanning, sdiff_sdiff_cancel_left hBE]
    exact h.spanning
  have hsub : insert e (M.E \ B) ⊆ M.E := insert_subset heE sdiff_subset
  refine ⟨by simpa using hcoind, ?_, by simp [h.mem]⟩
  rw [dual_ground, hcoind.mem_closure_iff_of_notMem (by simp [h.mem])]
  refine ⟨fun hi ↦ h.not_spanning_sdiff ?_, hsub⟩
  rw [← coindep_def, coindep_iff_compl_spanning hsub] at hi
  have hset : M.E \ insert e (M.E \ B) = B \ {e} := by
    ext x
    simp only [mem_sdiff, mem_insert_iff, mem_singleton_iff, not_or, not_and, not_not]
    exact ⟨fun ⟨hxE, hxe, hxB⟩ ↦ ⟨hxB hxE, hxe⟩, fun ⟨hxB, hxe⟩ ↦ ⟨hBE hxB, hxe, fun _ ↦ hxB⟩⟩
  rwa [hset] at hi

/-- The fundamental cocircuit for `B` and `e`, which `h : M.FundCocircuitExists e B` states
is defined: the unique cocircuit `K` of `M` for which `K ∩ B = {e}`. -/
def fundCocircuit (M : Matroid α) (e : α) (B : Set α) (h : M.FundCocircuitExists e B) : Set α :=
  M✶.fundCircuit e (M✶.E \ B) h.dual

lemma fundCocircuit_isCocircuit {B : Set α} (h : M.FundCocircuitExists e B) :
    M.IsCocircuit (M.fundCocircuit e B h) :=
  fundCircuit_isCircuit h.dual

lemma mem_fundCocircuit {B : Set α} (h : M.FundCocircuitExists e B) :
    e ∈ M.fundCocircuit e B h :=
  mem_insert _ _

lemma fundCocircuit_subset_insert_compl {B : Set α} (h : M.FundCocircuitExists e B) :
    M.fundCocircuit e B h ⊆ insert e (M.E \ B) :=
  fundCircuit_subset_insert h.dual

lemma fundCocircuit_inter_eq {B : Set α} (h : M.FundCocircuitExists e B) :
    (M.fundCocircuit e B h) ∩ B = {e} := by
  refine subset_antisymm ?_ (singleton_subset_iff.2 ⟨mem_fundCocircuit h, h.mem⟩)
  refine (inter_subset_inter_left _ (fundCocircuit_subset_insert_compl h)).trans ?_
  simp +contextual

/-- For every element `e` of an independent set `I`,
there is a cocircuit whose intersection with `I` is `{e}`. -/
lemma Indep.exists_isCocircuit_inter_eq_mem (hI : M.Indep I) (heI : e ∈ I) :
    ∃ K, M.IsCocircuit K ∧ K ∩ I = {e} := by
  obtain ⟨B, hB, hIB⟩ := hI.exists_isBase_superset
  have h := hB.fundCocircuitExists (hIB heI)
  refine ⟨M.fundCocircuit e B h, fundCocircuit_isCocircuit h, ?_⟩
  rw [subset_antisymm_iff, subset_inter_iff, singleton_subset_iff, and_iff_right
    (mem_fundCocircuit h), singleton_subset_iff, and_iff_left heI, ← fundCocircuit_inter_eq h]
  exact inter_subset_inter_right _ hIB

/-- Fundamental circuits and cocircuits of a base `B` play dual roles: for `e ∉ B` and `f ∈ B`,
`e` belongs to the fundamental cocircuit for `B` and `f` if and only if
`f` belongs to the fundamental circuit for `e` and `B`. -/
lemma IsBase.mem_fundCocircuit_iff_mem_fundCircuit {e f : α} (hB : M.IsBase B)
    (he : e ∈ M.E \ B) (hf : f ∈ B) :
    e ∈ M.fundCocircuit f B (hB.fundCocircuitExists hf) ↔
      f ∈ M.fundCircuit e B (hB.fundCircuitExists he.1 he.2) := by
  have hB' : M✶.IsBase (M✶.E \ B) := hB.compl_isBase_dual
  have hfE : f ∈ M.E := hB.subset_ground hf
  obtain ⟨heE, heB⟩ := he
  have hne : e ≠ f := by rintro rfl; exact heB hf
  rw [fundCocircuit, mem_fundCircuit_iff, mem_fundCircuit_iff]
  have hfeq : M✶.E \ (M✶.E \ B) = B := by
    simp [sdiff_sdiff_cancel_left hB.subset_ground]
  constructor
  · intro h
    have hB'' : M.IsBase (M.E \ (insert f (M✶.E \ B) \ {e})) :=
      (hB'.exchange_isBase_of_indep' ⟨heE, heB⟩ (by simp [hfE, hf]) h).compl_isBase_of_dual
    refine hB''.indep.subset ?_
    simp only [dual_ground, sdiff_singleton_subset_iff]
    rw [sdiff_sdiff_right, inter_eq_self_of_subset_right (by simpa), union_singleton, insert_comm,
      ← union_singleton (s := M.E \ B), ← Set.sdiff_sdiff,
      sdiff_sdiff_cancel_left hB.subset_ground]
    simp [hf]
  · intro h
    have hB'' : M.IsBase (insert e B \ {f}) := hB.exchange_isBase_of_indep' hf heB h
    have := hB''.compl_isBase_dual.indep
    refine this.subset ?_
    simp only [dual_ground]
    intro x hx
    simp only [mem_sdiff, mem_insert_iff, mem_singleton_iff] at hx ⊢
    grind

end IsCocircuit

end Matroid
