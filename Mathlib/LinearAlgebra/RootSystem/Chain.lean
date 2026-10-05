/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas
public import Mathlib.Order.Interval.Set.OrdConnectedLinear

/-!
# Chains of roots

Given roots `α` and `β`, the `α`-chain through `β` is the set of roots of the form `α + z • β`
for an integer `z`. This is known as a "root chain" and also a "root string". For linearly
independent roots in finite crystallographic root pairings, these chains are always unbroken, i.e.,
of the form: `β - q • α, ..., β - α, β, β + α, ..., β + p • α` for natural numbers `p`, `q`, and the
length, `p + q` is at most 3.

## Main definitions / results:
* `RootPairing.chainTopCoeff`: the largest natural number `p` such that `β + p • α` is a root, the
  natural number `p` in the chain `β - q • α, ..., β - α, β, β + α, ..., β + p • α`
* `RootPairing.chainBotCoeff`: the largest natural number `q` such that `β - q • α` is a root, the
  natural number `q` in the chain `β - q • α, ..., β - α, β, β + α, ..., β + p • α`
* `RootPairing.root_add_zsmul_mem_range_iff`: every chain is an interval (aka unbroken).
* `RootPairing.chainBotCoeff_add_chainTopCoeff_le`: every chain has length at most three.

-/

@[expose] public section

noncomputable section

open FaithfulSMul Function Set

variable {ι R M N : Type*} [Finite ι] [CommRing R] [CharZero R] [IsDomain R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

namespace RootPairing

variable {P : RootPairing ι R M N} [P.IsCrystallographic] {i j : ι}

/-- Note that it is often more convenient to use `RootPairing.root_add_zsmul_mem_range_iff` than
to invoke this lemma directly. -/
lemma setOfPred_root_add_zsmul_eq_Icc_of_linearIndependent
    (h : LinearIndependent R ![P.root i, P.root j]) :
    ∃ᵉ (q ≤ 0) (p ≥ 0), {z : ℤ | P.root j + z • P.root i ∈ range P.root} = Icc q p := by
  replace h := LinearIndependent.pair_iff.mp <| h.restrict_scalars' ℤ
  set S : Set ℤ := {z | P.root j + z • P.root i ∈ range P.root} with S_def
  have hS₀ : 0 ∈ S := by simp [S]
  have h_fin : S.Finite := by
    suffices Injective (fun z : S ↦ z.property.choose) from Finite.of_injective _ this
    intro ⟨z, hz⟩ ⟨z', hz'⟩ hzz
    have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
    have : IsAddTorsionFree M := .of_isTorsionFree R M
    have : z • P.root i = z' • P.root i := by
      rwa [← add_right_inj (P.root j), ← hz.choose_spec, ← hz'.choose_spec, P.root.injective.eq_iff]
    exact Subtype.ext <| smul_left_injective ℤ (P.ne_zero i) this
  have h_ne : S.Nonempty := ⟨0, by simp [S_def]⟩
  refine ⟨sInf S, csInf_le h_fin.bddBelow hS₀, sSup S, le_csSup h_fin.bddAbove hS₀,
    (h_ne.eq_Icc_iff_int h_fin.bddBelow h_fin.bddAbove).mpr fun r ⟨k, hk⟩ s ⟨l, hl⟩ hrs ↦ ?_⟩
  by_contra! contra
  have hki_notMem : P.root k + P.root i ∉ range P.root := by
    replace hk : P.root k + P.root i = P.root j + (r + 1) • P.root i := by rw [hk]; module
    replace contra : r + 1 ∉ S := hrs.notMem_of_mem_left <| by simp [contra]
    simpa only [hk, S_def, mem_ofPred_eq, S] using contra
  have hki_ne : P.root k ≠ -P.root i := by
    rw [hk]
    contrapose! h
    replace h : r • P.root i = - P.root j - P.root i := by rw [← sub_eq_of_eq_add h.symm]; module
    exact ⟨r + 1, 1, by simp [add_smul, h], by lia⟩
  have hli_notMem : P.root l - P.root i ∉ range P.root := by
    replace hl : P.root l - P.root i = P.root j + (s - 1) • P.root i := by rw [hl]; module
    replace contra : s - 1 ∉ S := hrs.notMem_of_mem_left <| by simp [lt_sub_right_of_add_lt contra]
    simpa only [hl, S_def, mem_ofPred_eq, S] using contra
  have hli_ne : P.root l ≠ P.root i := by
    rw [hl]
    contrapose! h
    replace h : s • P.root i = P.root i - P.root j := by rw [← sub_eq_of_eq_add h.symm]; module
    exact ⟨s - 1, 1, by simp [sub_smul, h], by lia⟩
  have h₁ : 0 ≤ P.pairingIn ℤ k i := by
    have := P.root_add_root_mem_of_pairingIn_neg (i := k) (j := i)
    contrapose! this
    exact ⟨this, hki_ne, hki_notMem⟩
  have h₂ : P.pairingIn ℤ k i = P.pairingIn ℤ j i + r * 2 := by
    apply algebraMap_injective ℤ R
    rw [algebraMap_pairingIn, map_add, map_mul, algebraMap_pairingIn, ← root_coroot'_eq_pairing, hk]
    simp
  have h₃ : P.pairingIn ℤ l i ≤ 0 := by
    have := P.root_sub_root_mem_of_pairingIn_pos (i := l) (j := i)
    contrapose! this
    exact ⟨this, fun x ↦ hli_ne (congrArg P.root x), hli_notMem⟩
  have h₄ : P.pairingIn ℤ l i = P.pairingIn ℤ j i + s * 2 := by
    apply algebraMap_injective ℤ R
    rw [algebraMap_pairingIn, map_add, map_mul, algebraMap_pairingIn, ← root_coroot'_eq_pairing, hl]
    simp
  lia

@[deprecated (since := "2026-07-09")]
alias setOf_root_add_zsmul_eq_Icc_of_linearIndependent :=
  setOfPred_root_add_zsmul_eq_Icc_of_linearIndependent

variable (i j)

/-- The largest natural number `p` such that `β + p • α` is a root, where `α = P.root i` and
`β = P.root j`. Only finitely many roots lie on the line through `β` in the direction of `α`, so it
exists for every pair of roots. If `α` and `β` are linearly independent, the `α`-chain through `β`
is the unbroken string `β - q • α, ..., β - α, β, β + α, ..., β + p • α`
(`RootPairing.root_add_zsmul_mem_range_iff`). -/
def chainTopCoeff : ℕ :=
  sSup {n : ℕ | P.root j + n • P.root i ∈ range P.root}

/-- The largest natural number `q` such that `β - q • α` is a root, where `α = P.root i` and
`β = P.root j`. Only finitely many roots lie on the line through `β` in the direction of `α`, so it
exists for every pair of roots. If `α` and `β` are linearly independent, the `α`-chain through `β`
is the unbroken string `β - q • α, ..., β - α, β, β + α, ..., β + p • α`
(`RootPairing.root_add_zsmul_mem_range_iff`). -/
def chainBotCoeff : ℕ :=
  sSup {n : ℕ | P.root j - n • P.root i ∈ range P.root}

variable {i j}

section

omit [Finite ι] [CharZero R] [IsDomain R] [P.IsCrystallographic]

lemma chainTopCoeff_eq_sSup :
    P.chainTopCoeff i j = sSup {k | P.root j + k • P.root i ∈ range P.root} :=
  rfl

lemma chainBotCoeff_eq_sSup :
    P.chainBotCoeff i j = sSup {k | P.root j - k • P.root i ∈ range P.root} :=
  rfl

@[simp]
lemma chainTopCoeff_reflectionPerm_left :
    P.chainTopCoeff (P.reflectionPerm i i) j = P.chainBotCoeff i j := by
  simp [chainTopCoeff, chainBotCoeff, root_reflectionPerm, reflection_apply_self, smul_neg,
    ← sub_eq_add_neg]

@[simp]
lemma chainBotCoeff_reflectionPerm_left :
    P.chainBotCoeff (P.reflectionPerm i i) j = P.chainTopCoeff i j := by
  simp [chainTopCoeff, chainBotCoeff, root_reflectionPerm, reflection_apply_self, smul_neg]

@[simp]
lemma chainTopCoeff_reflectionPerm_right :
    P.chainTopCoeff i (P.reflectionPerm j j) = P.chainBotCoeff i j := by
  simp only [chainTopCoeff, chainBotCoeff, root_reflectionPerm, reflection_apply_self]
  congr 1
  ext n
  rw [mem_ofPred_eq, mem_ofPred_eq, ← neg_mem_range_root_iff, neg_add, neg_neg, ← sub_eq_add_neg]

@[simp]
lemma chainBotCoeff_reflectionPerm_right :
    P.chainBotCoeff i (P.reflectionPerm j j) = P.chainTopCoeff i j := by
  simp only [chainTopCoeff, chainBotCoeff, root_reflectionPerm, reflection_apply_self]
  congr 1
  ext n
  rw [mem_ofPred_eq, mem_ofPred_eq, ← neg_mem_range_root_iff, neg_sub, sub_neg_eq_add, add_comm]

end

section General

omit [P.IsCrystallographic]

/-- Only finitely many roots lie on the line through `P.root j` in the direction of `P.root i`. -/
lemma finite_setOfPred_root_add_zsmul_mem :
    {z : ℤ | P.root j + z • P.root i ∈ range P.root}.Finite := by
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  have : IsAddTorsionFree M := .of_isTorsionFree R M
  exact Set.Finite.preimage (f := fun z : ℤ ↦ P.root j + z • P.root i)
    (fun z _ z' _ h ↦ smul_left_injective ℤ (P.ne_zero i) (add_left_cancel h)) (finite_range _)

lemma bddAbove_setOfPred_root_add_nsmul_mem :
    BddAbove {n : ℕ | P.root j + n • P.root i ∈ range P.root} := by
  obtain ⟨b, hb⟩ := (P.finite_setOfPred_root_add_zsmul_mem (i := i) (j := j)).bddAbove
  refine ⟨b.toNat, fun n hn ↦ ?_⟩
  have := hb (show (n : ℤ) ∈ {z : ℤ | P.root j + z • P.root i ∈ range P.root} by
    simpa [natCast_zsmul] using hn)
  lia

lemma bddAbove_setOfPred_root_sub_nsmul_mem :
    BddAbove {n : ℕ | P.root j - n • P.root i ∈ range P.root} := by
  simpa [root_reflectionPerm, reflection_apply_self, smul_neg, ← sub_eq_add_neg] using
    P.bddAbove_setOfPred_root_add_nsmul_mem (i := P.reflectionPerm i i) (j := j)

lemma root_add_chainTopCoeff_nsmul_mem_range :
    P.root j + P.chainTopCoeff i j • P.root i ∈ range P.root :=
  Nat.sSup_mem ⟨0, by simp⟩ P.bddAbove_setOfPred_root_add_nsmul_mem

lemma root_sub_chainBotCoeff_nsmul_mem_range :
    P.root j - P.chainBotCoeff i j • P.root i ∈ range P.root :=
  Nat.sSup_mem ⟨0, by simp⟩ P.bddAbove_setOfPred_root_sub_nsmul_mem

lemma le_chainTopCoeff_of_root_add_nsmul_mem_range {n : ℕ}
    (h : P.root j + n • P.root i ∈ range P.root) : n ≤ P.chainTopCoeff i j :=
  le_csSup P.bddAbove_setOfPred_root_add_nsmul_mem h

lemma le_chainBotCoeff_of_root_sub_nsmul_mem_range {n : ℕ}
    (h : P.root j - n • P.root i ∈ range P.root) : n ≤ P.chainBotCoeff i j :=
  le_csSup P.bddAbove_setOfPred_root_sub_nsmul_mem h

/-- `P.chainTopCoeff i j` is the largest integer `z` such that `P.root j + z • P.root i` is a
root. -/
lemma coe_chainTopCoeff_eq_sSup :
    P.chainTopCoeff i j = sSup {z : ℤ | P.root j + z • P.root i ∈ range P.root} := by
  set S := {z : ℤ | P.root j + z • P.root i ∈ range P.root}
  have hS : S.Finite := P.finite_setOfPred_root_add_zsmul_mem
  have h0 : (0 : ℤ) ∈ S := by simp [S]
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (le_csSup hS.bddAbove h0)
  have hmS : (m : ℤ) ∈ S := hm ▸ Int.csSup_mem ⟨0, h0⟩ hS.bddAbove
  rw [hm, Nat.cast_inj]
  refine le_antisymm (csSup_le ⟨0, by simp⟩ fun n hn ↦ ?_)
    (P.le_chainTopCoeff_of_root_add_nsmul_mem_range (by simpa [S, natCast_zsmul] using hmS))
  have := le_csSup hS.bddAbove (show (n : ℤ) ∈ S by simpa [S, natCast_zsmul] using hn)
  rw [hm] at this
  exact_mod_cast this

/-- `P.chainBotCoeff i j` is the largest integer `z` such that `P.root j - z • P.root i` is a
root. -/
lemma coe_chainBotCoeff_eq_sSup :
    P.chainBotCoeff i j = sSup {z : ℤ | P.root j - z • P.root i ∈ range P.root} := by
  rw [← chainTopCoeff_reflectionPerm_left, coe_chainTopCoeff_eq_sSup]
  simp [root_reflectionPerm, reflection_apply_self, smul_neg, ← sub_eq_add_neg]

lemma one_le_chainTopCoeff_of_root_add_mem (h : P.root i + P.root j ∈ range P.root) :
    1 ≤ P.chainTopCoeff i j :=
  P.le_chainTopCoeff_of_root_add_nsmul_mem_range (by rwa [one_smul, add_comm])

lemma one_le_chainBotCoeff_of_root_add_mem (h : P.root i - P.root j ∈ range P.root) :
    1 ≤ P.chainBotCoeff i j :=
  P.le_chainBotCoeff_of_root_sub_nsmul_mem_range (by rwa [one_smul, ← neg_mem_range_root_iff,
    neg_sub])

lemma chainBotCoeff_of_add {k : ι} (hk : P.root k = P.root j + P.root i) :
    P.chainBotCoeff i k = P.chainBotCoeff i j + 1 := by
  apply Nat.cast_injective (R := ℤ)
  rw [Nat.cast_add, Nat.cast_one, coe_chainBotCoeff_eq_sSup, coe_chainBotCoeff_eq_sSup]
  have (z : ℤ) : P.root k - z • P.root i = P.root j - (z - 1) • P.root i := by rw [hk]; module
  replace this : {z : ℤ | P.root k - z • P.root i ∈ range P.root} =
      OrderIso.addRight 1 '' {n | P.root j - n • P.root i ∈ range P.root} := by
    simp [this, sub_eq_add_neg]
  have bdd : BddAbove {z : ℤ | P.root j - z • P.root i ∈ range P.root} := by
    have := (P.finite_setOfPred_root_add_zsmul_mem (i := P.reflectionPerm i i) (j := j)).bddAbove
    simpa [root_reflectionPerm, reflection_apply_self, smul_neg, ← sub_eq_add_neg] using this
  rw [this, ← OrderIso.map_csSup' _ ⟨0, by simp⟩ bdd, OrderIso.addRight_apply]

lemma chainTopCoeff_of_sub {k : ι} (hk : P.root k = P.root j - P.root i) :
    P.chainTopCoeff i k = P.chainTopCoeff i j + 1 := by
  rw [← chainBotCoeff_reflectionPerm_left, ← chainBotCoeff_reflectionPerm_left]
  exact chainBotCoeff_of_add (by simp [hk, root_reflectionPerm, reflection_apply_self,
    sub_eq_add_neg])

lemma chainTopCoeff_of_add {k : ι} (hk : P.root k = P.root j + P.root i) :
    P.chainTopCoeff i j = P.chainTopCoeff i k + 1 :=
  chainTopCoeff_of_sub (by rw [hk, add_sub_cancel_right])

end General

section LinearIndependent

variable (h : LinearIndependent R ![P.root i, P.root j])
include h

lemma root_add_nsmul_mem_range_iff_le_chainTopCoeff {n : ℕ} :
    P.root j + n • P.root i ∈ range P.root ↔ n ≤ P.chainTopCoeff i j := by
  refine ⟨P.le_chainTopCoeff_of_root_add_nsmul_mem_range, fun hn ↦ ?_⟩
  obtain ⟨q, hq, p, -, hS⟩ := P.setOfPred_root_add_zsmul_eq_Icc_of_linearIndependent h
  have htop : (P.chainTopCoeff i j : ℤ) ∈ Icc q p := by
    rw [← hS]
    simpa [natCast_zsmul] using P.root_add_chainTopCoeff_nsmul_mem_range (i := i) (j := j)
  have : (n : ℤ) ∈ {z : ℤ | P.root j + z • P.root i ∈ range P.root} := by
    rw [hS]
    exact ⟨by lia, by have := htop.2; lia⟩
  simpa [natCast_zsmul] using this

lemma root_sub_nsmul_mem_range_iff_le_chainBotCoeff {n : ℕ} :
    P.root j - n • P.root i ∈ range P.root ↔ n ≤ P.chainBotCoeff i j := by
  let := P.indexNeg
  have h' : LinearIndependent R ![P.root (-i), P.root j] := by simpa
  have := P.root_add_nsmul_mem_range_iff_le_chainTopCoeff h' (n := n)
  simpa [smul_neg, ← sub_eq_add_neg] using this

lemma Iic_chainTopCoeff_eq :
    Iic (P.chainTopCoeff i j) = {k | P.root j + k • P.root i ∈ range P.root} := by
  ext; simp [← P.root_add_nsmul_mem_range_iff_le_chainTopCoeff h]

lemma Iic_chainBotCoeff_eq :
    Iic (P.chainBotCoeff i j) = {k | P.root j - k • P.root i ∈ range P.root} := by
  ext; simp [← P.root_sub_nsmul_mem_range_iff_le_chainBotCoeff h]

lemma root_add_zsmul_mem_range_iff {z : ℤ} :
    P.root j + z • P.root i ∈ range P.root ↔
      z ∈ Icc (-P.chainBotCoeff i j : ℤ) (P.chainTopCoeff i j) := by
  rcases z.eq_nat_or_neg with ⟨n, rfl | rfl⟩
  · simp [P.root_add_nsmul_mem_range_iff_le_chainTopCoeff h]
  · simp [P.root_sub_nsmul_mem_range_iff_le_chainBotCoeff h, ← sub_eq_add_neg]

lemma root_sub_zsmul_mem_range_iff {z : ℤ} :
    P.root j - z • P.root i ∈ range P.root ↔
      z ∈ Icc (-P.chainTopCoeff i j : ℤ) (P.chainBotCoeff i j) := by
  rw [sub_eq_add_neg, ← neg_smul, P.root_add_zsmul_mem_range_iff h, mem_Icc, mem_Icc]
  grind

lemma setOfPred_root_add_zsmul_mem_eq_Icc :
    {k : ℤ | P.root j + k • P.root i ∈ range P.root} =
      Icc (-P.chainBotCoeff i j : ℤ) (P.chainTopCoeff i j) := by
  ext; simp [← P.root_add_zsmul_mem_range_iff h]

@[deprecated (since := "2026-07-09")]
alias setOf_root_add_zsmul_mem_eq_Icc := setOfPred_root_add_zsmul_mem_eq_Icc

lemma setOfPred_root_sub_zsmul_mem_eq_Icc :
    {k : ℤ | P.root j - k • P.root i ∈ range P.root} =
      Icc (-P.chainTopCoeff i j : ℤ) (P.chainBotCoeff i j) := by
  ext; rw [← root_sub_zsmul_mem_range_iff h, mem_ofPred_eq]

@[deprecated (since := "2026-07-09")]
alias setOf_root_sub_zsmul_mem_eq_Icc := setOfPred_root_sub_zsmul_mem_eq_Icc

lemma chainBotCoeff_eq_zero_iff :
    P.chainBotCoeff i j = 0 ↔ P.root j - P.root i ∉ range P.root := by
  rw [← one_smul ℕ (P.root i), P.root_sub_nsmul_mem_range_iff_le_chainBotCoeff h, not_le,
    Nat.lt_one_iff]

lemma chainTopCoeff_eq_zero_iff :
    P.chainTopCoeff i j = 0 ↔ P.root j + P.root i ∉ range P.root := by
  rw [← one_smul ℕ (P.root i), P.root_add_nsmul_mem_range_iff_le_chainTopCoeff h, not_le,
    Nat.lt_one_iff]

end LinearIndependent

section Idx

omit [P.IsCrystallographic]

variable (i j)

/-- The index of the root `β + p • α`, where `α = P.root i`, `β = P.root j`, and
`p = P.chainTopCoeff i j`: the top of the `α`-chain through `β` when `α` and `β` are linearly
independent. It is unique since `P.root` is injective. -/
def chainTopIdx : ι :=
  (P.root_add_chainTopCoeff_nsmul_mem_range (i := i) (j := j)).choose

/-- The index of the root `β - q • α`, where `α = P.root i`, `β = P.root j`, and
`q = P.chainBotCoeff i j`: the bottom of the `α`-chain through `β` when `α` and `β` are linearly
independent. It is unique since `P.root` is injective. -/
def chainBotIdx : ι :=
  (P.root_sub_chainBotCoeff_nsmul_mem_range (i := i) (j := j)).choose

variable {i j}

@[simp]
lemma root_chainTopIdx :
    P.root (P.chainTopIdx i j) = P.root j + P.chainTopCoeff i j • P.root i :=
  (P.root_add_chainTopCoeff_nsmul_mem_range (i := i) (j := j)).choose_spec

@[simp]
lemma root_chainBotIdx :
    P.root (P.chainBotIdx i j) = P.root j - P.chainBotCoeff i j • P.root i :=
  (P.root_sub_chainBotCoeff_nsmul_mem_range (i := i) (j := j)).choose_spec

@[simp]
lemma chainTopCoeff_chainTopIdx :
    P.chainTopCoeff i (P.chainTopIdx i j) = 0 := by
  have h := P.root_add_chainTopCoeff_nsmul_mem_range (i := i) (j := P.chainTopIdx i j)
  rw [root_chainTopIdx, add_assoc, ← add_smul] at h
  have := P.le_chainTopCoeff_of_root_add_nsmul_mem_range h
  lia

@[simp]
lemma chainBotCoeff_chainTopIdx :
    P.chainBotCoeff i (P.chainTopIdx i j) = P.chainBotCoeff i j + P.chainTopCoeff i j := by
  apply le_antisymm
  · have h := P.root_sub_chainBotCoeff_nsmul_mem_range (i := i) (j := P.chainTopIdx i j)
    rw [root_chainTopIdx] at h
    rcases le_or_gt (P.chainBotCoeff i (P.chainTopIdx i j)) (P.chainTopCoeff i j) with hb | hb
    · lia
    · have h' : P.root j - (P.chainBotCoeff i (P.chainTopIdx i j) - P.chainTopCoeff i j) •
          P.root i ∈ range P.root := by
        rw [sub_nsmul _ hb.le]
        convert h using 1
        abel
      have := P.le_chainBotCoeff_of_root_sub_nsmul_mem_range h'
      lia
  · apply P.le_chainBotCoeff_of_root_sub_nsmul_mem_range
    rw [root_chainTopIdx, add_smul]
    convert P.root_sub_chainBotCoeff_nsmul_mem_range (i := i) (j := j) using 1
    abel

end Idx

lemma chainBotCoeff_sub_chainTopCoeff :
    P.chainBotCoeff i j - P.chainTopCoeff i j = P.pairingIn ℤ j i := by
  suffices ∀ i j, (P.chainBotCoeff i j : ℤ) - P.chainTopCoeff i j ≤ P.pairingIn ℤ j i by
    refine le_antisymm (this i j) ?_
    specialize this (P.reflectionPerm i i) j
    simp only [chainBotCoeff_reflectionPerm_left, chainTopCoeff_reflectionPerm_left,
      pairingIn_reflectionPerm_self_right] at this
    lia
  intro i j
  have h₁ : P.reflection i (P.root <| P.chainBotIdx i j) =
      P.root j + ((P.chainBotCoeff i j : ℤ) - P.pairingIn ℤ j i) • P.root i := by
    simp [reflection_apply_root, ← P.algebraMap_pairingIn ℤ]
    module
  have h₂ : P.reflection i (P.root <| P.chainBotIdx i j) ∈ range P.root := by
    rw [← root_reflectionPerm]
    exact mem_range_self _
  rw [h₁] at h₂
  have := le_csSup P.finite_setOfPred_root_add_zsmul_mem.bddAbove h₂
  rw [← coe_chainTopCoeff_eq_sSup] at this
  lia

lemma chainTopCoeff_sub_chainBotCoeff :
    P.chainTopCoeff i j - P.chainBotCoeff i j = -P.pairingIn ℤ j i := by
  rw [← chainBotCoeff_sub_chainTopCoeff, neg_sub]

lemma chainBotCoeff_add_chainTopCoeff_eq_pairingIn_chainTopIdx :
    P.chainBotCoeff i j + P.chainTopCoeff i j = P.pairingIn ℤ (P.chainTopIdx i j) i := by
  calc (P.chainBotCoeff i j + P.chainTopCoeff i j : ℤ)
    _ = P.chainBotCoeff i (P.chainTopIdx i j) := by simp
    _ = P.chainBotCoeff i (P.chainTopIdx i j) - P.chainTopCoeff i (P.chainTopIdx i j) := by simp
    _ = P.pairingIn ℤ (P.chainTopIdx i j) i := by rw [P.chainBotCoeff_sub_chainTopCoeff]

lemma chainBotCoeff_add_chainTopCoeff_le_three [P.IsReduced] :
    P.chainBotCoeff i j + P.chainTopCoeff i j ≤ 3 := by
  rw [← Int.ofNat_le, Nat.cast_add, Nat.cast_ofNat,
    chainBotCoeff_add_chainTopCoeff_eq_pairingIn_chainTopIdx]
  have := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed i (P.chainTopIdx i j)
  aesop

end RootPairing
