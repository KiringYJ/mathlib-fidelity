/-
Copyright (c) 2026 Emlis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emlis
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.ContinuedFractions.Determinant

/-!
# Euler continued fraction

This file formalizes a transformation on generalized continued fractions over a field `K`.
It defines a map sending a generalized continued fraction to an equivalent Euler continued
fraction obtained by an explicit transformation of its coefficient stream.

## Main definitions

* `GenContFract.IsEuler` : predicate for a generalized continued fraction to be an Euler
  continued fraction.
* `GenContFract.euler` : constructs a generalized continued fraction from a head term `h`
  and a coefficient stream `ρ`.
* `GenContFract.toEuler` : transforms a generalized continued fraction whose denominators are
  units to an Euler continued fraction.

## Main results

* `convs_euler` : explicit formula for convergents of an Euler continued fraction.
* `convs_eq_sum_of_forall_le` : the convergents as a sum of the differences of consecutive
  convergents, which the determinant formula computes.
* `convs_toEuler` : equivalence of convergents between a generalized continued fraction
  and its corresponding Euler continued fraction.

## References

* https://en.wikipedia.org/wiki/Euler%27s_continued_fraction_formula
* [Wall, H.S., *Analytic Theory of Continued Fractions*][wall2018analytic]

-/

public section

namespace GenContFract

variable {K : Type*} [Field K]

variable {n : ℕ} {h : K} {ρ : Stream'.Seq K} {g : GenContFract K}

/-- An *Euler continued fraction* is a generalized continued fraction of the form
$$
  h + \cfrac{\rho_0}
            {1 - \cfrac{\rho_1}
                       {1 + \rho_1 - \cfrac{\rho_2}
                                           {1 + \rho_2 - \cfrac{\rho_3}
                                                               {1 + \rho_3 - \dots}}}}
$$ -/
def IsEuler (g : GenContFract K) : Prop :=
  ∀ (n : ℕ) (aₙ bₙ : K), g.s.get? n = some ⟨aₙ, bₙ⟩ -> if n = 0 then bₙ = 1 else aₙ + bₙ = 1

/-- `euler h ρ` constructs an Euler continued fraction whose coefficients are obtained
from the stream `ρ` with head term `h`. -/
def euler (h : K) (ρ : Stream'.Seq K) : GenContFract K :=
  ⟨h, ρ.enum.map fun (n, ρ) => n.casesOn ⟨ρ, 1⟩ fun _ => ⟨-ρ, 1 + ρ⟩⟩

/-- `toEuler g hB` is the Euler continued fraction equivalent to `g`, where `ρ₀` = `a₀ / b₀` and
`ρₙ` = `- aₙ * Bₙ₋₁ / Bₙ₊₁` for `n > 0`. It exists when all denominators `Bₙ` of `g` are units,
which `hB` asserts; the coefficient `ρ₀` is computed as `a₀ / B₁`, since `B₁ = b₀`. -/
noncomputable def toEuler (g : GenContFract K) (hB : ∀ n, IsUnit (g.dens n)) : GenContFract K :=
  euler g.h <| g.s.enum.map fun (n, ⟨a, _⟩) =>
    n.casesOn (Checked.div a (g.dens 1) (hB 1)) fun n' =>
      Checked.div (- a * g.dens n') (g.dens (n' + 2)) (hB (n' + 2))

section Translation

open Stream'.Seq

@[simp]
theorem terminatedAt_euler : (euler h ρ).TerminatedAt n ↔ ρ.TerminatedAt n := by
  simp [euler, TerminatedAt, Stream'.Seq.TerminatedAt]

theorem exists_euler_s_of_not_terminatedAt_zero
    (not_terminatedAt_zero : ¬ρ.TerminatedAt 0) :
    ∃ a, (euler h ρ).s.get? 0 = some ⟨a, 1⟩ := by
  simpa [euler] using Option.ne_none_iff_exists'.mp not_terminatedAt_zero

theorem exists_euler_s_of_not_terminatedAt_succ
    (not_terminatedAt_n_succ : ¬ρ.TerminatedAt (n + 1)) :
    ∃ a, (euler h ρ).s.get? (n + 1) = some ⟨-a, 1 + a⟩ := by
  simpa [euler] using Option.ne_none_iff_exists'.mp not_terminatedAt_n_succ

@[simp]
theorem isEuler_euler : IsEuler (euler h ρ) := by
  intro n a b hn
  rcases n with _ | n'
  · simp [euler] at hn; simp [hn]
  · replace hn : ∃ ρₙ, ρ.get? (n' + 1) = some ρₙ ∧ -ρₙ = a ∧ 1 + ρₙ = b := by simp_all [euler]
    obtain ⟨ρ, _, rfl, rfl⟩ := hn
    simp

/-- This lemma shows that `IsEuler g` means that `g` is an Euler continued fraction in the sense
that there exists coefficients `ρ` such that `g = euler g.h ρ`.

It is not derived from `IsEuler.toEuler` because that lemma depends on `dens_eq_one`,
which itself requires this lemma to extract the coefficients. -/
private theorem IsEuler.exists_euler (h : g.IsEuler) : ∃ ρ, euler g.h ρ = g := by
  simp only [eq_comm]
  use g.s.enum.map fun (n, ⟨a, b⟩) => n.casesOn a fun _ => -a
  ext n ⟨a, b⟩
  · rfl
  match n with
  | 0 =>
    suffices g.s.get? 0 = some ⟨a, b⟩ ↔
      ∃ ab, g.s.get? 0 = some ab ∧ ab.a = a ∧ 1 = b by
      simpa [euler]
    refine ⟨fun h' => by grind [h 0 a b h'], ?_⟩
    rintro ⟨⟨a, b⟩, h', rfl, rfl⟩
    grind [h 0 a b h']
  | n' + 1 =>
    suffices g.s.get? (n' + 1) = some ⟨a, b⟩ ↔
      ∃ ab, g.s.get? (n' + 1) = some ab ∧ ab.a = a ∧ 1 + -ab.a = b by
      simpa [euler]
    refine ⟨fun h' => by grind [h (n' + 1) a b h'], ?_⟩
    rintro ⟨⟨a, b⟩, h', rfl, rfl⟩
    grind [h (n' + 1) a b h']

theorem isEuler_iff_exists_euler : IsEuler g ↔ ∃ ρ, euler g.h ρ = g :=
  ⟨IsEuler.exists_euler, fun ⟨_, hρ⟩ => hρ ▸ isEuler_euler⟩

@[simp]
theorem isEuler_toEuler {hB : ∀ n, IsUnit (g.dens n)} : IsEuler (toEuler g hB) := isEuler_euler

@[simp]
theorem terminatedAt_toEuler {hB : ∀ n, IsUnit (g.dens n)} :
    (g.toEuler hB).TerminatedAt n ↔ g.TerminatedAt n := by
  rw [toEuler, terminatedAt_euler, TerminatedAt]
  simp [Stream'.Seq.TerminatedAt]

theorem euler_s_zero : (euler h ρ).s.get? 0 = (ρ.get? 0).map fun ρ => ⟨ρ, 1⟩ := by
  simp only [euler, map_get?, get?_enum]
  rcases ρ.get? 0 with _ | _ <;> simp

theorem euler_s_succ : (euler h ρ).s.get? (n + 1) = (ρ.get? (n + 1)).map fun ρ => ⟨-ρ, 1 + ρ⟩ := by
  simp only [euler, map_get?, get?_enum]
  rcases ρ.get? (n + 1) with _ | _ <;> simp

theorem toEuler_s_zero {hB : ∀ n, IsUnit (g.dens n)} :
    (toEuler g hB).s.get? 0 =
      (g.s.get? 0).map fun ⟨a, _⟩ => ⟨Checked.div a (g.dens 1) (hB 1), 1⟩ := by
  simp [toEuler, euler_s_zero]
  congr

theorem toEuler_s_succ {hB : ∀ n, IsUnit (g.dens n)} :
    (toEuler g hB).s.get? (n + 1) =
      (g.s.get? (n + 1)).map fun ⟨a, _⟩ =>
        ⟨Checked.div (a * g.dens n) (g.dens (n + 2)) (hB (n + 2)),
          1 - Checked.div (a * g.dens n) (g.dens (n + 2)) (hB (n + 2))⟩ := by
  simp only [toEuler, neg_mul, map_get?, get?_enum, Option.map_map, euler_s_succ]
  congr
  ext
  simp [neg_div₀, sub_eq_add_neg]

end Translation

@[simp]
theorem euler_h : (euler h ρ).h = h := by rfl

@[simp]
theorem toEuler_h {hB : ∀ n, IsUnit (g.dens n)} : (g.toEuler hB).h = g.h := by rfl

@[simp]
theorem partNum_euler_zero : (euler h ρ).partNums.get? 0 = ρ.get? 0 := by
  rw [partNums, @Stream'.Seq.map_get?, euler_s_zero]
  rcases ρ.get? 0 with _ | _ <;> simp

@[simp]
theorem partDen_euler_zero : (euler h ρ).partDens.get? 0 = (ρ.get? 0).map (fun _ => 1) := by
  rw [partDens, @Stream'.Seq.map_get?, euler_s_zero]
  rcases ρ.get? 0 with _ | _ <;> simp

@[simp]
theorem partNum_euler_succ : (euler h ρ).partNums.get? (n + 1) = (ρ.get? (n + 1)).map (- ·) := by
  rw [partNums, @Stream'.Seq.map_get?, euler_s_succ]
  rcases ρ.get? (n + 1) with _ | _ <;> simp

@[simp]
theorem partDen_euler_succ : (euler h ρ).partDens.get? (n + 1) = (ρ.get? (n + 1)).map (1 + ·) := by
  rw [partDens, @Stream'.Seq.map_get?, euler_s_succ]
  rcases ρ.get? (n + 1) with _ | _ <;> simp

private theorem dens_euler_one : (euler h ρ).dens 1 = 1 :=
  Decidable.em ((euler h ρ).TerminatedAt 0) |>.elim
    (fun terminatedAt_zero =>
      (dens_stable_of_terminated zero_le_one <| terminatedAt_zero) ▸ zeroth_den_eq_one)
    (fun not_terminatedAt_zero =>
      first_den_eq <| exists_euler_s_of_not_terminatedAt_zero
        (terminatedAt_euler (K := K) |>.eq ▸ not_terminatedAt_zero) |>.choose_spec)

/-- The denominators of an Euler continued fraction are all 1. -/
@[simp]
theorem IsEuler.dens_eq_one (h : g.IsEuler) : g.dens n = 1 := by
  obtain ⟨ρ, hρ⟩ := h.exists_euler
  rw [← hρ]
  set g := euler g.h ρ
  induction n using Nat.strong_induction_on with | h n ih =>
  match n with
  | 0 => exact zeroth_den_eq_one
  | n + 1 =>
  rcases Decidable.em <| g.TerminatedAt n with terminatedAt_n | not_terminatedAt_n
  · simpa only [dens_stable_of_terminated n.le_succ terminatedAt_n] using ih n n.lt_add_one
  rw [terminatedAt_euler] at not_terminatedAt_n
  match n with
  | 0 => exact dens_euler_one
  | n + 1 =>
  obtain ⟨a, s_n_succ_eq⟩ : ∃ a, g.s.get? (n + 1) = some ⟨-a, 1 + a⟩ :=
    exists_euler_s_of_not_terminatedAt_succ not_terminatedAt_n
  simp [dens_recurrence s_n_succ_eq, ih, add_assoc]

private theorem nums_euler_aux : (euler h ρ).nums (n + 1) - (euler h ρ).nums n =
    ∏ j ∈ Finset.range (n + 1), (ρ.get? j).getD 0 := by
  have det := determinant (g := euler h ρ) (n := n)
  simp only [isEuler_euler, IsEuler.dens_eq_one, mul_one, one_mul] at det
  rw [← neg_sub, det, Finset.prod_range_succ', Finset.prod_range_succ']
  simp only [partNum_euler_succ, partNum_euler_zero, mul_neg, neg_neg]
  congr; ext n'
  rcases ρ.get? (n' + 1) with _ | _ <;> simp

/-- The numerators of an Euler continued fraction are given by the formula
$$
  A_n = h + \sum_{i = 0}^{n - 1} \prod_{j = 0}^i \rho_j
$$ -/
theorem nums_euler :
    (euler h ρ).nums n =
      h + ∑ i ∈ Finset.range n, ∏ j ∈ Finset.range (i + 1), (ρ.get? j).getD 0 := by
  simp only [← nums_euler_aux (h := h)]
  erw [Finset.sum_range_sub, zeroth_num_eq_h, euler_h, add_sub_cancel]

/-- **Euler's continued fraction formula**: the convergents of an Euler continued fraction
are given by the formula
$$
  \dfrac{A_n}{B_n} = h + \sum_{i = 0}^{n - 1} \prod_{j = 0}^i \rho_j
$$
for example:
- `A₀ / B₀ = h`
- `A₁ / B₁ = h + ρ₀`
- `A₂ / B₂ = h + ρ₀ + ρ₀ * ρ₁`
- `Aₙ / Bₙ = h + ρ₀ + ρ₀ * ρ₁ + ρ₀ * ρ₁ * ρ₂ + ... + ρ₀ * ρ₁ * ρ₂ * ... * ρₙ₋₁` -/
@[wikidata Q5361532]
theorem convs_euler :
    (euler h ρ).convs n =
      h + ∑ i ∈ Finset.range n, ∏ j ∈ Finset.range (i + 1), (ρ.get? j).getD 0 := by
  simp [convs, nums_euler]

/-- The transformation `toEuler` is idempotent. -/
@[simp]
protected theorem IsEuler.toEuler {hB : ∀ n, IsUnit (g.dens n)} (hg : g.IsEuler) :
    g.toEuler hB = g := by
  ext n : 2
  · rfl
  match n with
  | 0 =>
    rw [toEuler_s_zero]
    rcases hs : g.s.get? 0 with _ | ⟨a₀, b₀⟩
    · rfl
    · have hb₀ : b₀ = 1 := by simpa using hg 0 a₀ b₀ hs
      simp [hb₀, hg.dens_eq_one]
  | n' + 1 =>
    rw [toEuler_s_succ]
    rcases hs : g.s.get? (n' + 1) with _ | ⟨a, b⟩
    · rfl
    · have hab : a + b = 1 := by simpa using hg (n' + 1) a b hs
      simp [hg.dens_eq_one, ← hab]

/-- The convergents of `g` as a sum of the differences of consecutive convergents, which the
determinant formula computes. The `i`th term is a quotient by `Bᵢ * Bᵢ₊₁`; it is taken for
`i < n`, where `hB` gives its evidence. -/
theorem convs_eq_sum_of_forall_le (hB : ∀ m ≤ n, g.dens m ≠ 0) :
    g.convs n (hB n le_rfl).isUnit = g.h + ∑ i : Fin n,
      Checked.div (- (∏ j ∈ Finset.range (i + 1), -(g.partNums.get? j).getD 0))
        (g.dens i * g.dens (i + 1)) ((hB i i.2.le).isUnit.mul (hB (i + 1) i.2).isUnit) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [← add_assoc, ← ih fun m hm ↦ hB m (Nat.le_succ_of_le hm), ← determinant,
      conv_eq_num_div_den, conv_eq_num_div_den, eq_comm, div_add_div, div_eq_div_iff]
    ring

theorem _root_.SimpContFract.convs_eq_sum_of_forall_le {s : SimpContFract K}
    (not_terminatedAt_n : ¬(↑s : GenContFract K).TerminatedAt n)
    (hB : ∀ m ≤ n, (↑s : GenContFract K).dens m ≠ 0) :
    (↑s : GenContFract K).convs n (hB n le_rfl).isUnit = (↑s : GenContFract K).h +
      ∑ i : Fin n, Checked.div ((-1) ^ (i : ℕ))
        ((↑s : GenContFract K).dens i * (↑s : GenContFract K).dens (i + 1))
        ((hB i i.2.le).isUnit.mul (hB (i + 1) i.2).isUnit) := by
  rw [GenContFract.convs_eq_sum_of_forall_le hB, add_left_cancel_iff]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  calc
    _ = -∏ j ∈ Finset.range (i + 1), (-1 : K) := neg_inj.mpr <| Finset.prod_congr rfl fun j hj => by
      have hjn : j ≤ n := by have := Finset.mem_range.1 hj; have := i.2; omega
      obtain ⟨gp, s_ith_eq⟩ : ∃ gp, (↑s : GenContFract K).s.get? j = some gp :=
        Option.ne_none_iff_exists'.1 <| mt (terminated_stable hjn) ‹_›
      rw [partNum_eq_s_a s_ith_eq, s.property j gp.a <| partNum_eq_s_a s_ith_eq, Option.getD_some]
    _ = (-1) ^ (i : ℕ) := by simp [pow_succ]

/-- The transformation `toEuler` preserves the convergents. -/
theorem convs_toEuler {hB : ∀ m, IsUnit (g.dens m)} (m : ℕ) :
    (g.toEuler hB).convs m = g.convs m (hB m) := by
  obtain ⟨ρ, hρ⟩ := isEuler_toEuler (hB := hB) |>.exists_euler
  rw [toEuler_h] at hρ
  have hj_zero : (ρ.get? 0).getD 0 =
      Checked.div ((g.partNums.get? 0).getD 0) (g.dens 1) (hB 1) := by
    have h := toEuler_s_zero (hB := hB)
    rw [← hρ, euler_s_zero] at h
    rcases hs : g.s.get? 0 with _ | ⟨a₀, b₀⟩
    · rw [hs, Option.map_none, Option.map_eq_none_iff] at h
      rw [h, partNum_none_iff_s_none.mpr hs]
      simp
    · rw [hs, Option.map_some, Option.map_eq_some_iff] at h
      obtain ⟨r, hr, hr'⟩ := h
      simp only [Pair.mk.injEq, and_true] at hr'
      rw [hr, partNum_eq_s_a hs, Option.getD_some, Option.getD_some, hr']
  have hj_succ (j : ℕ) : (ρ.get? (j + 1)).getD 0 = Checked.div
      (-(g.partNums.get? (j + 1)).getD 0 * g.dens j) (g.dens (j + 2)) (hB (j + 2)) := by
    have h := toEuler_s_succ (n := j) (hB := hB)
    rw [← hρ, euler_s_succ] at h
    rcases hs : g.s.get? (j + 1) with _ | ⟨a, b⟩
    · rw [hs, Option.map_none, Option.map_eq_none_iff] at h
      rw [h, partNum_none_iff_s_none.mpr hs]
      simp
    · rw [hs, Option.map_some, Option.map_eq_some_iff] at h
      obtain ⟨r, hr, hr'⟩ := h
      simp only [Pair.mk.injEq] at hr'
      rw [hr, partNum_eq_s_a hs, Option.getD_some, Option.getD_some, neg_mul, neg_div₀,
        ← hr'.1, neg_neg]
  have hP (i : ℕ) : (∏ j ∈ Finset.range (i + 1), (ρ.get? j).getD 0) * (g.dens i * g.dens (i + 1)) =
      -∏ j ∈ Finset.range (i + 1), -(g.partNums.get? j).getD 0 := by
    induction i with
    | zero =>
      rw [Finset.prod_range_one, Finset.prod_range_one, hj_zero, zeroth_den_eq_one, one_mul,
        div_mul_cancel₀, neg_neg]
    | succ i ih =>
      have h1 : (ρ.get? (i + 1)).getD 0 * g.dens (i + 2) =
          -(g.partNums.get? (i + 1)).getD 0 * g.dens i := by
        rw [hj_succ, div_mul_cancel₀]
      rw [Finset.prod_range_succ, Finset.prod_range_succ (fun j ↦ -(g.partNums.get? j).getD 0)]
      calc (∏ j ∈ Finset.range (i + 1), (ρ.get? j).getD 0) * (ρ.get? (i + 1)).getD 0 *
            (g.dens (i + 1) * g.dens (i + 1 + 1))
          = (∏ j ∈ Finset.range (i + 1), (ρ.get? j).getD 0) * g.dens (i + 1) *
            ((ρ.get? (i + 1)).getD 0 * g.dens (i + 2)) := by ring
        _ = (∏ j ∈ Finset.range (i + 1), (ρ.get? j).getD 0) * (g.dens i * g.dens (i + 1)) *
            -(g.partNums.get? (i + 1)).getD 0 := by rw [h1]; ring
        _ = _ := by rw [ih]; ring
  simp only [← hρ]
  rw [convs_euler, convs_eq_sum_of_forall_le fun k _ ↦ (hB k).ne_zero, add_left_cancel_iff,
    Finset.sum_range]
  exact Finset.sum_congr rfl fun i _ ↦ eq_div_iff.mpr (hP i)

end GenContFract
