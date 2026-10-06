/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.PNat.Basic
public import Mathlib.Dynamics.PeriodicPts.Defs
public import Mathlib.Order.Lattice.Nat

/-!
# Extra lemmas about periodic points
-/

public section

open Nat Set

namespace Function
variable {α : Type*} {f : α → α} {x : α}

open Function (Commute)

theorem directed_ptsOfPeriod_pnat (f : α → α) : Directed (· ⊆ ·) fun n : ℕ+ => ptsOfPeriod f n :=
  fun m n => ⟨m * n, fun _ hx => hx.mul_const n, fun _ hx => hx.const_mul m⟩

variable (f) in
theorem bijOn_periodicPts : BijOn f (periodicPts f) (periodicPts f) :=
  iUnion_pnat_ptsOfPeriod f ▸
    bijOn_iUnion_of_directed (directed_ptsOfPeriod_pnat f) fun i => bijOn_ptsOfPeriod f i.pos

theorem minimalPeriod_eq_prime_iff {p : ℕ} [hp : Fact p.Prime] (hx : x ∈ periodicPts f) :
    minimalPeriod f x = p ↔ IsPeriodicPt f p x ∧ ¬IsFixedPt f x := by
  rw [isPeriodicPt_iff_minimalPeriod_dvd hx, Nat.dvd_prime hp.out,
    ← (minimalPeriod_eq_one_iff_isFixedPt hx).not, or_and_right, and_not_self_iff, false_or,
    iff_self_and]
  exact fun h ↦ ne_of_eq_of_ne h hp.out.ne_one

theorem minimalPeriod_eq_sInf_n_pos_IsPeriodicPt (hx : x ∈ periodicPts f) :
    minimalPeriod f x = sInf { n > 0 | IsPeriodicPt f n x } :=
  (le_csInf hx fun _ hn => IsPeriodicPt.minimalPeriod_le hn.1 hn.2).antisymm
    (Nat.sInf_le ⟨minimalPeriod_pos hx, isPeriodicPt_minimalPeriod f x hx⟩)

/-- The backward direction of `minimalPeriod_eq_prime_iff`. -/
theorem minimalPeriod_eq_prime {p : ℕ} [hp : Fact p.Prime] (hper : IsPeriodicPt f p x)
    (hfix : ¬IsFixedPt f x) : minimalPeriod f x (mk_mem_periodicPts hp.out.pos hper) = p :=
  (minimalPeriod_eq_prime_iff _).mpr ⟨hper, hfix⟩

theorem minimalPeriod_eq_prime_pow {p k : ℕ} [hp : Fact p.Prime] (hk : ¬IsPeriodicPt f (p ^ k) x)
    (hk1 : IsPeriodicPt f (p ^ (k + 1)) x) :
    minimalPeriod f x (mk_mem_periodicPts (Nat.pow_pos hp.out.pos) hk1) = p ^ (k + 1) := by
  apply Nat.eq_prime_pow_of_dvd_least_prime_pow hp.out <;>
    rwa [← isPeriodicPt_iff_minimalPeriod_dvd]

theorem Commute.minimalPeriod_of_comp_dvd_mul {g : α → α} (h : Commute f g)
    (hf : x ∈ periodicPts f) (hg : x ∈ periodicPts g) :
    minimalPeriod (f ∘ g) x (h.comp_mem_periodicPts hf hg) ∣
      minimalPeriod f x * minimalPeriod g x :=
  dvd_trans (h.minimalPeriod_of_comp_dvd_lcm hf hg) (Nat.lcm_dvd_mul _ _)

theorem Commute.minimalPeriod_of_comp_eq_mul_of_coprime {g : α → α} (h : Commute f g)
    (hf : x ∈ periodicPts f) (hg : x ∈ periodicPts g)
    (hco : Coprime (minimalPeriod f x) (minimalPeriod g x)) :
    minimalPeriod (f ∘ g) x (h.comp_mem_periodicPts hf hg) =
      minimalPeriod f x * minimalPeriod g x := by
  have hfg := h.comp_mem_periodicPts hf hg
  refine (h.minimalPeriod_of_comp_dvd_mul hf hg).antisymm (hco.mul_dvd_of_dvd_of_dvd ?_ ?_)
  · refine hco.dvd_of_dvd_mul_right
      ((IsPeriodicPt.left_of_comp h ?_ ?_).minimalPeriod_dvd hf)
    · exact (isPeriodicPt_minimalPeriod _ _ hfg).mul_const _
    · exact (isPeriodicPt_minimalPeriod _ _ hg).const_mul _
  · refine hco.symm.dvd_of_dvd_mul_right
      ((IsPeriodicPt.left_of_comp h.symm ?_ ?_).minimalPeriod_dvd hg)
    · rw [← h.comp_eq]
      exact (isPeriodicPt_minimalPeriod _ _ hfg).mul_const _
    · exact (isPeriodicPt_minimalPeriod _ _ hf).const_mul _

section Fintype

open Fintype

theorem minimalPeriod_le_card [Fintype α] (hx : x ∈ periodicPts f) :
    minimalPeriod f x ≤ card α := by
  rw [← periodicOrbit_length hx]
  exact List.Nodup.length_le_card (nodup_periodicOrbit hx)

theorem isPeriodicPt_factorial_card_of_mem_periodicPts [Fintype α] (h : x ∈ periodicPts f) :
    IsPeriodicPt f (card α)! x :=
  (isPeriodicPt_iff_minimalPeriod_dvd h).mpr
    (Nat.dvd_factorial (minimalPeriod_pos h) (minimalPeriod_le_card h))

theorem mem_periodicPts_iff_isPeriodicPt_factorial_card [Fintype α] :
    x ∈ periodicPts f ↔ IsPeriodicPt f (card α)! x where
  mp := isPeriodicPt_factorial_card_of_mem_periodicPts
  mpr h := mk_mem_periodicPts (Nat.factorial_pos _) h

theorem Injective.mem_periodicPts [Finite α] (h : Injective f) (x : α) : x ∈ periodicPts f := by
  obtain ⟨m, n, heq, hne⟩ : ∃ m n, f^[m] x = f^[n] x ∧ m ≠ n := by
    simpa [Injective] using not_injective_infinite_finite (f^[·] x)
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact mk_mem_periodicPts (by lia) (iterate_cancel h heq.symm)
  · exact mk_mem_periodicPts (by lia) (iterate_cancel h heq)

theorem injective_iff_periodicPts_eq_univ [Finite α] : Injective f ↔ periodicPts f = univ := by
  refine ⟨fun h ↦ eq_univ_iff_forall.mpr h.mem_periodicPts, fun h ↦ ?_⟩
  rw [Finite.injective_iff_surjective, ← range_eq_univ, ← univ_subset_iff, ← h]
  apply periodicPts_subset_range

theorem injective_iff_iterate_factorial_card_eq_id [Fintype α] :
    Injective f ↔ f^[(card α)!] = id := by
  simp only [injective_iff_periodicPts_eq_univ, mem_periodicPts_iff_isPeriodicPt_factorial_card,
    funext_iff, eq_univ_iff_forall, IsPeriodicPt, id, IsFixedPt]

end Fintype

end Function

namespace Function

section Prod

variable {α β : Type*} {f : α → α} {g : β → β} {x : α × β} {m n : ℕ}

theorem mem_periodicPts_prodMap :
    x ∈ periodicPts (Prod.map f g) ↔ x.1 ∈ periodicPts f ∧ x.2 ∈ periodicPts g := by
  refine ⟨fun ⟨n, hn, hx⟩ => ?_, fun ⟨⟨m, hm, h1⟩, ⟨n, hn, h2⟩⟩ => ?_⟩
  · rw [isPeriodicPt_prodMap] at hx
    exact ⟨⟨n, hn, hx.1⟩, ⟨n, hn, hx.2⟩⟩
  · exact ⟨Nat.lcm m n, Nat.lcm_pos hm hn, (isPeriodicPt_prodMap _).2
      ⟨h1.trans_dvd (Nat.dvd_lcm_left _ _), h2.trans_dvd (Nat.dvd_lcm_right _ _)⟩⟩

theorem minimalPeriod_prodMap (hx : x ∈ periodicPts (Prod.map f g)) :
    minimalPeriod (Prod.map f g) x =
      (minimalPeriod f x.1 (mem_periodicPts_prodMap.1 hx).1).lcm
        (minimalPeriod g x.2 (mem_periodicPts_prodMap.1 hx).2) :=
  Nat.dvd_right_iff_eq.1 fun n => by
    rw [← isPeriodicPt_iff_minimalPeriod_dvd hx, Nat.lcm_dvd_iff,
      ← isPeriodicPt_iff_minimalPeriod_dvd, ← isPeriodicPt_iff_minimalPeriod_dvd,
      isPeriodicPt_prodMap]

theorem minimalPeriod_fst_dvd (hx : x ∈ periodicPts (Prod.map f g)) :
    minimalPeriod f x.1 (mem_periodicPts_prodMap.1 hx).1 ∣ minimalPeriod (Prod.map f g) x := by
  rw [minimalPeriod_prodMap hx]; exact Nat.dvd_lcm_left _ _

theorem minimalPeriod_snd_dvd (hx : x ∈ periodicPts (Prod.map f g)) :
    minimalPeriod g x.2 (mem_periodicPts_prodMap.1 hx).2 ∣ minimalPeriod (Prod.map f g) x := by
  rw [minimalPeriod_prodMap hx]; exact Nat.dvd_lcm_right _ _

end Prod

section Pi

variable {ι : Type*} {α : ι → Type*} {f : ∀ i, α i → α i} {x : ∀ i, α i}

theorem apply_mem_periodicPts_piMap (hx : x ∈ periodicPts (Pi.map f)) (i : ι) :
    x i ∈ periodicPts (f i) :=
  let ⟨n, hn, hx⟩ := hx
  ⟨n, hn, isPeriodicPt_piMap.1 hx i⟩

/-- This `sInf` can be regarded as a generalized version of LCM
for possibly infinite sets and types. -/
theorem minimalPeriod_piMap (hx : x ∈ periodicPts (Pi.map f)) :
    minimalPeriod (Pi.map f) x =
      sInf { n > 0 | ∀ i, minimalPeriod (f i) (x i) (apply_mem_periodicPts_piMap hx i) ∣ n } := by
  rw [minimalPeriod_eq_sInf_n_pos_IsPeriodicPt hx]
  congr 1
  ext n
  simp only [Set.mem_ofPred_eq, isPeriodicPt_piMap]
  exact and_congr_right fun _ => forall_congr' fun i =>
    isPeriodicPt_iff_minimalPeriod_dvd (apply_mem_periodicPts_piMap hx i)

theorem minimalPeriod_piMap_fintype [Fintype ι] (hx : x ∈ periodicPts (Pi.map f)) :
    minimalPeriod (Pi.map f) x =
      Finset.univ.lcm (fun i => minimalPeriod (f i) (x i) (apply_mem_periodicPts_piMap hx i)) :=
  Nat.dvd_right_iff_eq.1 fun n => by
    rw [← isPeriodicPt_iff_minimalPeriod_dvd hx, isPeriodicPt_piMap, Finset.lcm_dvd_iff]
    simp only [Finset.mem_univ, true_imp_iff]
    exact forall_congr' fun i =>
      isPeriodicPt_iff_minimalPeriod_dvd (apply_mem_periodicPts_piMap hx i)

theorem minimalPeriod_single_dvd_minimalPeriod_piMap (hx : x ∈ periodicPts (Pi.map f)) (i : ι) :
    minimalPeriod (f i) (x i) (apply_mem_periodicPts_piMap hx i) ∣
      minimalPeriod (Pi.map f) x :=
  (isPeriodicPt_piMap.1 (isPeriodicPt_minimalPeriod _ x hx) i).minimalPeriod_dvd _

end Pi

end Function
