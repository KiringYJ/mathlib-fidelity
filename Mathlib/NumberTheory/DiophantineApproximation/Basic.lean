/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Geißer, Michael Stoll
-/
module

public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.RingTheory.Int.Basic
public import Mathlib.Tactic.Basic

/-!
# Diophantine Approximation

The first part of this file gives proofs of various versions of
**Dirichlet's approximation theorem** and its important consequence that when $\xi$ is an
irrational real number, then there are infinitely many rationals $x/y$ (in lowest terms)
such that
$$\left|\xi - \frac{x}{y}\right| < \frac{1}{y^2} \,.$$
The proof is based on the pigeonhole principle.

The second part of the file gives a proof of **Legendre's Theorem** on rational approximation,
which states that if $\xi$ is a real number and $x/y$ is a rational number such that
$$\left|\xi - \frac{x}{y}\right| < \frac{1}{2y^2} \,,$$
then $x/y$ must be a convergent of the continued fraction expansion of $\xi$.

## Main statements

The main results are three variants of Dirichlet's approximation theorem:
* `Real.exists_int_int_abs_mul_sub_le`, which states that for all real `ξ` and natural `0 < n`,
  there are integers `j` and `k` with `0 < k ≤ n` and `|k*ξ - j| ≤ 1/(n+1)`,
* `Real.exists_nat_abs_mul_sub_round_le`, which replaces `j` by `round(k*ξ)` and uses
  a natural number `k`,
* `Real.exists_rat_abs_sub_le_and_den_le`, which says that there is a rational number `q`
  satisfying `|ξ - q| ≤ 1/((n+1)*q.den)` and `q.den ≤ n`,

and
* `Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational`, which states that
  for irrational `ξ`, the set `{q : ℚ | |ξ - q| < 1/q.den^2}` is infinite.

We also show a converse,
* `Rat.finite_rat_abs_sub_lt_one_div_den_sq`, which states that the set above is finite
  when `ξ` is a rational number.

Both statements are combined to give an equivalence,
`Real.infinite_rat_abs_sub_lt_one_div_den_sq_iff_irrational`.

There are two versions of Legendre's Theorem. One, `Real.exists_rat_eq_convergent`, uses
`Real.convergent`, a simple recursive definition of the convergents that is also defined
in this file, whereas the other, `Real.exists_convs_eq_rat` defined in the file
`Mathlib/NumberTheory/DiophantineApproximation/ContinuedFractions.lean`, uses
`GenContFract.convs` of `GenContFract.of ξ`.

## Implementation notes

We use the namespace `Real` for the results on real numbers and `Rat` for the results
on rational numbers. We introduce a secondary namespace `Real.ContfracLegendre`
to separate off a definition and some technical auxiliary lemmas used in the proof
of Legendre's Theorem. For remarks on the proof of Legendre's Theorem, see below.

## References

<https://en.wikipedia.org/wiki/Dirichlet%27s_approximation_theorem>
<https://de.wikipedia.org/wiki/Kettenbruch> (The German Wikipedia page on continued
fractions is much more extensive than the English one.)

## Tags

Diophantine approximation, Dirichlet's approximation theorem, continued fraction
-/

@[expose] public section


namespace Real

section Dirichlet

/-!
### Dirichlet's approximation theorem

We show that for any real number `ξ` and positive natural `n`, there is a fraction `q`
such that `q.den ≤ n` and `|ξ - q| ≤ 1/((n+1)*q.den)`.
-/


open Finset Int

/-- *Dirichlet's approximation theorem:*
For any real number `ξ` and positive natural `n`, there are integers `j` and `k`,
with `0 < k ≤ n` and `|k*ξ - j| ≤ 1/(n+1)`.

See also `Real.exists_nat_abs_mul_sub_round_le`. -/
theorem exists_int_int_abs_mul_sub_le (ξ : ℝ) {n : ℕ} (n_pos : 0 < n) :
    ∃ j k : ℤ, 0 < k ∧ k ≤ n ∧ |↑k * ξ - j| ≤ 1 / (n + 1) := by
  let f : ℤ → ℤ := fun m => ⌊fract (ξ * m) * (n + 1)⌋
  have hn : 0 < (n : ℝ) + 1 := mod_cast Nat.succ_pos _
  have hfu := fun m : ℤ => mul_lt_of_lt_one_left hn <| fract_lt_one (ξ * ↑m)
  conv in |_| ≤ _ => rw [mul_comm, le_div_iff₀ hn, ← abs_of_pos hn, ← abs_mul]
  let D := Icc (0 : ℤ) n
  by_cases! H : ∃ m ∈ D, f m = n
  · obtain ⟨m, hm, hf⟩ := H
    have hf' : ((n : ℤ) : ℝ) ≤ fract (ξ * m) * (n + 1) := hf ▸ floor_le (fract (ξ * m) * (n + 1))
    have hm₀ : 0 < m := by
      have hf₀ : f 0 = 0 := by
        simp only [f, cast_zero, mul_zero, fract_zero, zero_mul, floor_zero]
      refine Ne.lt_of_le (fun h => n_pos.ne ?_) (mem_Icc.mp hm).1
      exact mod_cast hf₀.symm.trans (h.symm ▸ hf : f 0 = n)
    refine ⟨⌊ξ * m⌋ + 1, m, hm₀, (mem_Icc.mp hm).2, ?_⟩
    rw [cast_add, ← sub_sub, sub_mul, cast_one, one_mul, abs_le]
    refine
      ⟨le_sub_iff_add_le.mpr ?_, sub_le_iff_le_add.mpr <| le_of_lt <| (hfu m).trans <| lt_one_add _⟩
    simpa only [neg_add_cancel_comm_assoc] using! hf'
  · have hD : #(Ico (0 : ℤ) n) < #D := by rw [card_Icc, card_Ico]; exact lt_add_one n
    have hfu' : ∀ m, f m ≤ n := fun m => lt_add_one_iff.mp (floor_lt.mpr (mod_cast hfu m))
    have hwd : ∀ m : ℤ, m ∈ D → f m ∈ Ico (0 : ℤ) n := fun x hx =>
      mem_Ico.mpr
        ⟨floor_nonneg.mpr (mul_nonneg (fract_nonneg (ξ * x)) hn.le), Ne.lt_of_le (H x hx) (hfu' x)⟩
    obtain ⟨x, hx, y, hy, x_lt_y, hxy⟩ : ∃ x ∈ D, ∃ y ∈ D, x < y ∧ f x = f y := by
      obtain ⟨x, hx, y, hy, x_ne_y, hxy⟩ := exists_ne_map_eq_of_card_lt_of_maps_to hD hwd
      rcases lt_trichotomy x y with (h | h | h)
      exacts [⟨x, hx, y, hy, h, hxy⟩, False.elim (x_ne_y h), ⟨y, hy, x, hx, h, hxy.symm⟩]
    refine
      ⟨⌊ξ * y⌋ - ⌊ξ * x⌋, y - x, sub_pos_of_lt x_lt_y,
        sub_le_iff_le_add.mpr <| le_add_of_le_of_nonneg (mem_Icc.mp hy).2 (mem_Icc.mp hx).1, ?_⟩
    convert_to! |fract (ξ * y) * (n + 1) - fract (ξ * x) * (n + 1)| ≤ 1
    · congr; push_cast; simp only [fract]; ring
    exact (abs_sub_lt_one_of_floor_eq_floor hxy.symm).le

/-- *Dirichlet's approximation theorem:*
For any real number `ξ` and positive natural `n`, there is a natural number `k`,
with `0 < k ≤ n` such that `|k*ξ - round(k*ξ)| ≤ 1/(n+1)`.
-/
theorem exists_nat_abs_mul_sub_round_le (ξ : ℝ) {n : ℕ} (n_pos : 0 < n) :
    ∃ k : ℕ, 0 < k ∧ k ≤ n ∧ |↑k * ξ - round (↑k * ξ)| ≤ 1 / (n + 1) := by
  obtain ⟨j, k, hk₀, hk₁, h⟩ := exists_int_int_abs_mul_sub_le ξ n_pos
  have hk := toNat_of_nonneg hk₀.le
  rw [← hk] at hk₀ hk₁ h
  exact ⟨k.toNat, natCast_pos.mp hk₀, Nat.cast_le.mp hk₁, (round_le (↑k.toNat * ξ) j).trans h⟩

/-- *Dirichlet's approximation theorem:*
For any real number `ξ` and positive natural `n`, there is a fraction `q`
such that `q.den ≤ n` and `|ξ - q| ≤ 1/((n+1)*q.den)`.

See also `AddCircle.exists_norm_nsmul_le`. -/
theorem exists_rat_abs_sub_le_and_den_le (ξ : ℝ) {n : ℕ} (n_pos : 0 < n) :
    ∃ q : ℚ, |ξ - q| ≤ 1 / ((n + 1) * q.den) ∧ q.den ≤ n := by
  obtain ⟨j, k, hk₀, hk₁, h⟩ := exists_int_int_abs_mul_sub_le ξ n_pos
  have hk₀' : (0 : ℝ) < k := Int.cast_pos.mpr hk₀
  have hden : ((j / k : ℚ).den : ℤ) ≤ k := by
    have hk : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg hk₀.le
    have hkn : k.toNat ≠ 0 := by omega
    have hq : (j / k : ℚ) = Rat.fraction j k.toNat hkn := by
      rw [Rat.fraction_eq_div]
      congr 1
      exact_mod_cast hk.symm
    rw [hq]
    exact (Int.ofNat_le.mpr (Nat.le_of_dvd (by omega) (Rat.den_dvd j k.toNat hkn))).trans hk.le
  refine ⟨j / k, ?_, Nat.cast_le.mp (hden.trans hk₁)⟩
  have hd : (0 : ℝ) < ((j / k : ℚ).den : ℝ) := Nat.cast_pos.mpr (Rat.pos _)
  have hdk : (((j / k : ℚ).den : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hden
  have hn : (0 : ℝ) < n + 1 := by positivity
  simp only [Rat.cast_div, Rat.cast_intCast]
  calc |ξ - (j : ℝ) / k| = |(k : ℝ) * ξ - j| / k := by
        have e : (k : ℝ) * ξ - j = k * (ξ - j / k) := by rw [mul_sub, mul_div_cancel₀]
        rw [e, abs_mul, abs_of_pos hk₀', mul_div_cancel_left₀]
    _ ≤ 1 / (n + 1) / k := by gcongr
    _ = 1 / ((n + 1) * k) := div_div₀
    _ ≤ 1 / ((n + 1) * ((j / k : ℚ).den : ℝ)) := by gcongr

end Dirichlet

section RatApprox

/-!
### Infinitely many good approximations to irrational numbers

We show that an irrational real number `ξ` has infinitely many "good rational approximations",
i.e., fractions `x/y` in lowest terms such that `|ξ - x/y| < 1/y^2`.
-/


open Set

/-- Given any rational approximation `q` to the irrational real number `ξ`, there is
a good rational approximation `q'` such that `|ξ - q'| < |ξ - q|`. -/
theorem exists_rat_abs_sub_lt_and_lt_of_irrational {ξ : ℝ} (hξ : Irrational ξ) (q : ℚ) :
    ∃ q' : ℚ, |ξ - q'| < 1 / (q'.den : ℝ) ^ 2 ∧ |ξ - q'| < |ξ - q| := by
  have h := abs_pos.mpr (sub_ne_zero.mpr <| Irrational.ne_rat hξ q)
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / |ξ - q|)
  have m_pos : (0 : ℝ) < m := (one_div_pos.mpr h).trans hm
  obtain ⟨q', hbd, hden⟩ := exists_rat_abs_sub_le_and_den_le ξ (Nat.cast_pos.mp m_pos)
  have den_pos : (0 : ℝ) < q'.den := Nat.cast_pos.mpr q'.pos
  have md_pos := mul_pos (add_pos m_pos zero_lt_one) den_pos
  refine
    ⟨q', lt_of_le_of_lt hbd ?_,
      lt_of_le_of_lt hbd <|
        (one_div_lt md_pos h).mpr <|
          hm.trans <|
            lt_of_lt_of_le (lt_add_one _) <|
              (le_mul_iff_one_le_right <| add_pos m_pos zero_lt_one).mpr <|
                mod_cast (q'.pos : 1 ≤ q'.den)⟩
  refine one_div_lt_one_div_of_lt (pow_pos den_pos 2) ?_
  rw [sq, mul_lt_mul_iff_left₀ den_pos]
  exact lt_add_of_le_of_pos (Nat.cast_le.mpr hden) zero_lt_one

/-- If `ξ` is an irrational real number, then there are infinitely many good
rational approximations to `ξ`. -/
theorem infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational {ξ : ℝ} (hξ : Irrational ξ) :
    {q : ℚ | |ξ - q| < 1 / (q.den : ℝ) ^ 2}.Infinite := by
  refine Or.resolve_left (Set.finite_or_infinite _) fun h => ?_
  obtain ⟨q, _, hq⟩ :=
    exists_min_image {q : ℚ | |ξ - q| < 1 / (q.den : ℝ) ^ 2} (fun q => |ξ - q|) h
      ⟨⌊ξ⌋, by simp [abs_of_nonneg, Int.fract_lt_one]⟩
  obtain ⟨q', hmem, hbetter⟩ := exists_rat_abs_sub_lt_and_lt_of_irrational hξ q
  exact lt_irrefl _ (lt_of_le_of_lt (hq q' hmem) hbetter)

end RatApprox

end Real

namespace Rat

/-!
### Finitely many good approximations to rational numbers

We now show that a rational number `ξ` has only finitely many good rational
approximations.
-/


open Set

/-- If `ξ` is rational, then the good rational approximations to `ξ` have bounded
numerator and denominator. -/
theorem den_le_and_le_num_le_of_sub_lt_one_div_den_sq {ξ q : ℚ}
    (h : |ξ - q| < 1 / (q.den : ℚ) ^ 2) :
    q.den ≤ ξ.den ∧ ⌈ξ * q.den⌉ - 1 ≤ q.num ∧ q.num ≤ ⌊ξ * q.den⌋ + 1 := by
  have hq₀ : (0 : ℚ) < q.den := Nat.cast_pos.mpr q.pos
  replace h : |ξ * q.den - q.num| < 1 / q.den := by
    rw [← mul_lt_mul_iff_left₀ hq₀] at h
    conv_lhs at h => rw [← abs_of_pos hq₀, ← abs_mul, sub_mul, mul_den_eq_num]
    have e : (1 : ℚ) / (q.den : ℚ) ^ 2 * q.den = 1 / q.den := by field_simp; ring
    rwa [e] at h
  constructor
  · rcases eq_or_ne ξ q with (rfl | H)
    · exact le_rfl
    · have hξ₀ : (0 : ℚ) < ξ.den := Nat.cast_pos.mpr ξ.pos
      -- over the common denominator, the numerator of `ξ * q.den - q.num` is a nonzero integer
      have hnz : (1 : ℚ) ≤ |((ξ.num * q.den - q.num * ξ.den : ℤ) : ℚ)| := by
        exact_mod_cast Int.one_le_abs (sub_ne_zero_of_ne <| mt Rat.eq_iff_mul_eq_mul.mpr H)
      have key : |((ξ.num * q.den - q.num * ξ.den : ℤ) : ℚ)| = |ξ * q.den - q.num| * ξ.den := by
        rw [← abs_of_pos hξ₀, ← abs_mul]
        congr 1
        push_cast
        rw [sub_mul, mul_right_comm ξ, Rat.mul_den_eq_num]
      refine Nat.cast_le.mp ((one_lt_div hq₀).mp ?_).le
      calc (1 : ℚ) ≤ |((ξ.num * q.den - q.num * ξ.den : ℤ) : ℚ)| := hnz
        _ = |ξ * q.den - q.num| * ξ.den := key
        _ < 1 / q.den * ξ.den := by gcongr
        _ = ξ.den / q.den := by rw [div_mul_eq_mul_div₀, one_mul]
  · have h1 : (1 : ℚ) / q.den ≤ 1 := by
      rw [div_le_one hq₀]
      exact_mod_cast q.pos
    obtain ⟨h₁, h₂⟩ := abs_sub_lt_iff.mp (h.trans_le h1)
    rw [sub_lt_iff_lt_add, add_comm] at h₁ h₂
    rw [← sub_lt_iff_lt_add] at h₂
    norm_cast at h₁ h₂
    exact
      ⟨sub_le_iff_le_add.mpr (Int.ceil_le.mpr h₁.le), sub_le_iff_le_add.mp (Int.le_floor.mpr h₂.le)⟩

/-- A rational number has only finitely many good rational approximations. -/
theorem finite_rat_abs_sub_lt_one_div_den_sq (ξ : ℚ) :
    {q : ℚ | |ξ - q| < 1 / (q.den : ℚ) ^ 2}.Finite := by
  let f : ℚ → ℤ × ℕ := fun q => (q.num, q.den)
  set s := {q : ℚ | |ξ - q| < 1 / (q.den : ℚ) ^ 2}
  have hinj : Function.Injective f := by
    intro a b hab
    simp only [f, Prod.mk_inj] at hab
    exact Rat.ext hab.1 hab.2
  have H : f '' s ⊆ ⋃ (y : ℕ) (_ : y ∈ Ioc 0 ξ.den), Icc (⌈ξ * y⌉ - 1) (⌊ξ * y⌋ + 1) ×ˢ {y} := by
    intro xy hxy
    simp only [mem_image] at hxy
    obtain ⟨q, hq₁, hq₂⟩ := hxy
    obtain ⟨hd, hn⟩ := den_le_and_le_num_le_of_sub_lt_one_div_den_sq hq₁
    simp_rw [mem_iUnion]
    refine ⟨q.den, Set.mem_Ioc.mpr ⟨q.pos, hd⟩, ?_⟩
    simp only [prod_singleton, mem_image, mem_Icc]
    exact ⟨q.num, hn, hq₂⟩
  refine (Finite.subset ?_ H).of_finite_image hinj.injOn
  exact Finite.biUnion (finite_Ioc _ _) fun x _ => Finite.prod (finite_Icc _ _) (finite_singleton _)

end Rat

/-- The set of good rational approximations to a real number `ξ` is infinite if and only if
`ξ` is irrational. -/
theorem Real.infinite_rat_abs_sub_lt_one_div_den_sq_iff_irrational (ξ : ℝ) :
    {q : ℚ | |ξ - q| < 1 / (q.den : ℝ) ^ 2}.Infinite ↔ Irrational ξ := by
  refine
    ⟨fun h => (irrational_iff_ne_rational ξ).mpr fun a b hb => ?_,
      Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational⟩
  contrapose! h
  convert! Rat.finite_rat_abs_sub_lt_one_div_den_sq ((a : ℚ) / b) with q
  have e₁ : (a : ℝ) / b = ((a / b : ℚ) : ℝ) := by simp only [Rat.cast_div, Rat.cast_intCast]
  have e₂ : (1 : ℝ) / (q.den : ℝ) ^ 2 = ((1 / (q.den : ℚ) ^ 2 : ℚ) : ℝ) := by
    simp only [Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_natCast]
  rw [h, e₁, e₂, ← Rat.cast_sub, ← Rat.cast_abs, Rat.cast_lt]

/-!
### Legendre's Theorem on Rational Approximation

We prove **Legendre's Theorem** on rational approximation: If $\xi$ is a real number and
$x/y$ is a rational number such that $|\xi - x/y| < 1/(2y^2)$,
then $x/y$ is a convergent of the continued fraction expansion of $\xi$.

The proof is by induction. However, the induction proof does not work with the
statement as given, since the assumption is too weak to imply the corresponding
statement for the application of the induction hypothesis. This can be remedied
by making the statement slightly stronger. Namely, we assume that $|\xi - x/y| < 1/(y(2y-1))$
when $y \ge 2$ and $-\frac{1}{2} < \xi - x < 1$ when $y = 1$.
-/


section Convergent

namespace Real

open Int

/-!
### Convergents: definition and API lemmas
-/


/-- The recursion defining `Real.convergent`, together with the fact that the convergents of `ξ`
are at least `⌊ξ⌋`. That fact makes the inverse in the recursion step exist: the convergents of
`(fract ξ)⁻¹ > 1` are at least `⌊(fract ξ)⁻¹⌋ ≥ 1`. -/
noncomputable def convergentAux : (ξ : ℝ) → ℕ → {q : ℚ // (⌊ξ⌋ : ℚ) ≤ q}
  | ξ, 0 => ⟨⌊ξ⌋, le_rfl⟩
  | ξ, n + 1 =>
    if h : fract ξ = 0 then ⟨⌊ξ⌋, le_rfl⟩
    else
      have one_le : (1 : ℚ) ≤ (convergentAux (fract ξ)⁻¹ n).1 := by
        refine le_trans ?_ (convergentAux (fract ξ)⁻¹ n).2
        have h₀ : 0 < fract ξ := (fract_nonneg ξ).lt_of_ne' h
        exact_mod_cast le_floor.mpr (by
          rw [Int.cast_one, one_le_inv₀ h₀]
          exact (fract_lt_one ξ).le)
      ⟨⌊ξ⌋ + (convergentAux (fract ξ)⁻¹ n).1⁻¹,
        le_add_of_nonneg_right (inv_nonneg.mpr (zero_le_one.trans one_le))⟩

/-- We give a direct recursive definition of the convergents of the continued fraction
expansion of a real number `ξ`. The main reason for that is that we want to have the
convergents as rational numbers; the versions `(GenContFract.of ξ).convs` and
`(GenContFract.of ξ).convs'` always give something of the same type as `ξ`.
We can then also use dot notation `ξ.convergent n`.
Another minor reason is that this demonstrates that the proof
of Legendre's theorem does not need anything beyond this definition.
We provide a proof that this definition agrees with the other one;
see `Real.convs_eq_convergent`.
The zeroth convergent is `⌊ξ⌋`; the `(n + 1)`th convergent is `⌊ξ⌋` if `ξ` is an integer, and
`⌊ξ⌋ + 1 / c` otherwise, where `c` is the `n`th convergent of `(fract ξ)⁻¹`, which is at least
one (see `Real.convergent_succ`). For a rational `ξ`, the convergents are hence eventually
constant. -/
noncomputable def convergent (ξ : ℝ) (n : ℕ) : ℚ :=
  (convergentAux ξ n).1

/-- The convergents of `ξ` are at least `⌊ξ⌋`. -/
theorem floor_le_convergent (ξ : ℝ) (n : ℕ) : (⌊ξ⌋ : ℚ) ≤ ξ.convergent n :=
  (convergentAux ξ n).2

/-- The convergents of the inverse of the fractional part of a non-integer are at least one. -/
theorem one_le_convergent_inv_fract {ξ : ℝ} (h : fract ξ ≠ 0) (n : ℕ) :
    1 ≤ (fract ξ)⁻¹.convergent n := by
  refine le_trans ?_ (floor_le_convergent _ n)
  have h₀ : 0 < fract ξ := (fract_nonneg ξ).lt_of_ne' h
  exact_mod_cast le_floor.mpr (by
    rw [Int.cast_one, one_le_inv₀ h₀]
    exact (fract_lt_one ξ).le)

/-- The zeroth convergent of `ξ` is `⌊ξ⌋`. -/
@[simp]
theorem convergent_zero (ξ : ℝ) : ξ.convergent 0 = ⌊ξ⌋ :=
  rfl

/-- The `(n+1)`th convergent of a non-integer `ξ` is given by the `n`th convergent of
`1/(fract ξ)`. -/
@[simp]
theorem convergent_succ (ξ : ℝ) (n : ℕ) (h : fract ξ ≠ 0) :
    ξ.convergent (n + 1) = ⌊ξ⌋ + Checked.inv ((fract ξ)⁻¹.convergent n)
      (zero_lt_one.trans_le (one_le_convergent_inv_fract h n)).ne'.isUnit := by
  simp only [convergent, convergentAux, h, dite_false]

/-- The `(n+1)`th convergent of an integer `ξ` is `⌊ξ⌋`. -/
@[simp]
theorem convergent_succ_of_fract_eq_zero (ξ : ℝ) (n : ℕ) (h : fract ξ = 0) :
    ξ.convergent (n + 1) = ⌊ξ⌋ := by
  simp only [convergent, convergentAux, h, dite_true]

/-- All convergents of `0` are zero. -/
@[simp]
theorem convergent_of_zero (n : ℕ) : convergent 0 n = 0 := by
  cases n
  · simp only [convergent_zero, floor_zero, cast_zero]
  · simp only [convergent_succ_of_fract_eq_zero _ _ fract_zero, floor_zero, cast_zero]

/-- If `ξ` is an integer, all its convergents equal `ξ`. -/
@[simp]
theorem convergent_of_int {ξ : ℤ} (n : ℕ) : convergent ξ n = ξ := by
  cases n
  · simp only [convergent_zero, floor_intCast]
  · simp only [convergent_succ_of_fract_eq_zero _ _ (fract_intCast ξ), floor_intCast]

end Real

end Convergent

/-!
### The key technical condition for the induction proof
-/


namespace Real

open Int

-- this is not `private`, as it is used in the public `exists_rat_eq_convergent'` below.
/-- Define the technical condition to be used as assumption in the inductive proof. The quotient
`u / v` and the inverse in the last condition exist when `v * (2 * v - 1)` is a unit, that is,
when `v ≠ 0`; this evidence is part of the condition. -/
def ContfracLegendre.Ass (ξ : ℝ) (u v : ℤ) : Prop :=
  IsCoprime u v ∧ (v = 1 → (-(1 / 2) : ℝ) < ξ - u) ∧
    ∃ _ : IsUnit ((v : ℝ) * (2 * v - 1)), |ξ - u / v| < ((v : ℝ) * (2 * v - 1))⁻¹

/-- The denominator `v` in the technical condition is nonzero. -/
theorem ContfracLegendre.Ass.den_ne_zero {ξ : ℝ} {u v : ℤ} (h : ContfracLegendre.Ass ξ u v) :
    v ≠ 0 := by
  obtain ⟨-, -, hv, -⟩ := h
  exact_mod_cast (isUnit_of_mul_isUnit_left hv).ne_zero

-- ### Auxiliary lemmas
-- This saves a few lines below, as it is frequently needed.
private theorem aux₀ {v : ℤ} (hv : 0 < v) : (0 : ℝ) < v ∧ (0 : ℝ) < 2 * v - 1 :=
  ⟨cast_pos.mpr hv, by norm_cast; lia⟩

-- In the following, we assume that `ass ξ u v` holds and `v ≥ 2`.
variable {ξ : ℝ} {u v : ℤ}

section
variable (hv : 2 ≤ v) (h : ContfracLegendre.Ass ξ u v)
include hv h

-- The fractional part of `ξ` is positive.
private theorem aux₁ : 0 < fract ξ := by
  have hv₀ : (0 : ℝ) < v := cast_pos.mpr (zero_lt_two.trans_le hv)
  obtain ⟨hv₁, hv₂⟩ := aux₀ (zero_lt_two.trans_le hv)
  obtain ⟨hcop, _, _, h⟩ := h
  refine fract_pos.mpr fun hf => ?_
  rw [hf] at h
  have H : (2 * v - 1 : ℝ) < 1 := by
    refine (mul_lt_iff_lt_one_right hv₀).1 ((inv_lt_inv₀ hv₀ (mul_pos hv₁ hv₂)).1 (h.trans_le' ?_))
    have h' : (⌊ξ⌋ : ℝ) - u / v = (⌊ξ⌋ * v - u) / v := by field_simp
    rw [h', abs_div]
    simp only [abs_of_pos hv₀]
    rw [← one_div₀, div_le_div_iff_of_pos_right hv₀]
    norm_cast
    rw [← zero_add (1 : ℤ), add_one_le_iff, abs_pos, sub_ne_zero]
    rintro rfl
    cases isUnit_iff.mp (isCoprime_self.mp (IsCoprime.mul_left_iff.mp hcop).2) <;> lia
  norm_cast at H
  linarith only [hv, H]

-- An auxiliary lemma for the inductive step.
private theorem aux₂ : 0 < u - ⌊ξ⌋ * v ∧ u - ⌊ξ⌋ * v < v := by
  obtain ⟨hcop, _, _, h⟩ := h
  obtain ⟨hv₀, hv₀'⟩ := aux₀ (zero_lt_two.trans_le hv)
  have hv₁ : 0 < 2 * v - 1 := by linarith only [hv]
  rw [← one_div₀, lt_div_iff₀ (mul_pos hv₀ hv₀'), ← abs_of_pos (mul_pos hv₀ hv₀'), ← abs_mul,
    sub_mul, ← mul_assoc, ← mul_assoc, div_mul_cancel₀, abs_sub_comm, abs_lt,
    lt_sub_iff_add_lt, sub_lt_iff_lt_add, mul_assoc] at h
  have hu₀ : 0 ≤ u - ⌊ξ⌋ * v := by
    refine (mul_nonneg_iff_of_pos_right hv₁).mp ?_
    rw [← sub_one_lt_iff, zero_sub]
    replace h := h.1
    rw [← lt_sub_iff_add_lt, ← mul_assoc, ← sub_mul] at h
    exact mod_cast
      h.trans_le
        ((mul_le_mul_iff_left₀ <| hv₀').mpr <|
          (sub_le_sub_iff_left (u : ℝ)).mpr ((mul_le_mul_iff_left₀ hv₀).mpr (floor_le ξ)))
  have hu₁ : u - ⌊ξ⌋ * v ≤ v := by
    refine _root_.le_of_mul_le_mul_right (le_of_lt_add_one ?_) hv₁
    replace h := h.2
    rw [← sub_lt_iff_lt_add, ← mul_assoc, ← sub_mul, ← add_lt_add_iff_right (v * (2 * v - 1) : ℝ),
      add_comm (1 : ℝ)] at h
    have :=
      flip mul_lt_mul_of_pos_right hv₀' <| (sub_lt_sub_iff_left (u : ℝ)).mpr <|
          flip mul_lt_mul_of_pos_right hv₀ <| sub_right_lt_of_lt_add <| lt_floor_add_one ξ
    rw [sub_mul ξ, one_mul, ← sub_add, add_mul] at this
    exact mod_cast this.trans h
  have huv_cop : IsCoprime (u - ⌊ξ⌋ * v) v := by
    rwa [sub_eq_add_neg, ← neg_mul, IsCoprime.add_mul_right_left_iff]
  refine ⟨lt_of_le_of_ne' hu₀ fun hf => ?_, lt_of_le_of_ne hu₁ fun hf => ?_⟩ <;>
    · rw [hf] at huv_cop
      simp only [isCoprime_zero_left, isCoprime_self, isUnit_iff] at huv_cop
      rcases huv_cop with huv_cop | huv_cop <;> linarith only [hv, huv_cop]

-- The key step: the relevant inequality persists in the inductive step. This is the last
-- condition of `ContfracLegendre.Ass` for `(fract ξ)⁻¹`, `v` and `u - ⌊ξ⌋ * v`.
private theorem aux₃ :
    ∃ _ : IsUnit (((u - ⌊ξ⌋ * v : ℤ) : ℝ) * (2 * ((u - ⌊ξ⌋ * v : ℤ) : ℝ) - 1)),
      |Checked.inv (fract ξ) (aux₁ hv h).ne'.isUnit - (v : ℝ) / ((u - ⌊ξ⌋ * v : ℤ) : ℝ)| <
        (((u - ⌊ξ⌋ * v : ℤ) : ℝ) * (2 * ((u - ⌊ξ⌋ * v : ℤ) : ℝ) - 1))⁻¹ := by
  obtain ⟨hu₀, huv⟩ := aux₂ hv h
  have hξ₀ := aux₁ hv h
  set u' := u - ⌊ξ⌋ * v with hu'
  have hu'ℝ : (u' : ℝ) = u - ⌊ξ⌋ * v := mod_cast hu'
  replace hu'ℝ := (eq_sub_iff_add_eq.mp hu'ℝ).symm
  obtain ⟨Hu, Hu'⟩ := aux₀ hu₀
  obtain ⟨Hv, Hv'⟩ := aux₀ (zero_lt_two.trans_le hv)
  refine ⟨(mul_pos Hu Hu').ne'.isUnit, ?_⟩
  have H₁ := div_pos (div_pos Hv Hu) hξ₀
  obtain ⟨-, -, -, h⟩ := h
  have h' : |fract ξ - u' / v| < ((v : ℝ) * (2 * v - 1))⁻¹ := by
    rwa [hu'ℝ, add_div, mul_div_cancel_right₀, ← sub_sub, sub_right_comm] at h
  have H : (2 * u' - 1 : ℝ) ≤ (2 * v - 1) * fract ξ := by
    replace h := (abs_lt.mp h).1
    have : (2 * (v : ℝ) - 1) * (-((v : ℝ) * (2 * v - 1))⁻¹ + u' / v) = 2 * u' - (1 + u') / v := by
      field
    rw [hu'ℝ, add_div, mul_div_cancel_right₀, ← sub_sub, sub_right_comm, self_sub_floor,
      lt_sub_iff_add_lt, ← mul_lt_mul_iff_right₀ Hv', this] at h
    refine LE.le.trans ?_ h.le
    rw [sub_le_sub_iff_left, div_le_one Hv, add_comm]
    exact mod_cast huv
  calc
    |(fract ξ)⁻¹ - v / u'| = |(fract ξ - u' / v) * (v / u' / fract ξ)| := by
      rw [abs_sub_comm]; congr 1; field
    _ = |fract ξ - u' / v| * (v / u' / fract ξ) := by rw [abs_mul, abs_of_pos H₁]
    _ < ((v : ℝ) * (2 * v - 1))⁻¹ * (v / u' / fract ξ) := by gcongr
    _ = (u' * ((2 * v - 1) * fract ξ))⁻¹ := by field
    _ ≤ (u' * (2 * u' - 1) : ℝ)⁻¹ := by gcongr

-- The conditions `ass ξ u v` persist in the inductive step.
private theorem invariant :
    ContfracLegendre.Ass (Checked.inv (fract ξ) (aux₁ hv h).ne'.isUnit) v (u - ⌊ξ⌋ * v) := by
  refine ⟨?_, fun huv => ?_, aux₃ hv h⟩
  · rw [sub_eq_add_neg, ← neg_mul, isCoprime_comm, IsCoprime.add_mul_right_left_iff]
    exact h.1
  · obtain ⟨hv₀, hv₀'⟩ := aux₀ (zero_lt_two.trans_le hv)
    have Hv : (v * (2 * v - 1) : ℝ)⁻¹ + (v : ℝ)⁻¹ = 2 / (2 * v - 1) := by
      field
    have Huv : (u / v : ℝ) = ⌊ξ⌋ + (v : ℝ)⁻¹ := by
      rw [sub_eq_iff_eq_add'.mp huv]
      field_simp
      push_cast
      ring
    obtain ⟨_, h₂⟩ := h.2.2
    have h' := (abs_sub_lt_iff.mp h₂).1
    rw [Huv, ← sub_sub, sub_lt_iff_lt_add, self_sub_floor, Hv] at h'
    rwa [lt_sub_iff_add_lt', (by ring : (v : ℝ) + -(1 / 2) = (2 * v - 1) / 2),
      lt_inv_comm₀ (div_pos hv₀' zero_lt_two) (aux₁ hv h), inv_div₀]

end

/-!
### The main result
-/


/-- The technical version of *Legendre's Theorem*. The quotient `u / v` exists since the
technical condition implies `v ≠ 0`. -/
theorem exists_rat_eq_convergent' {v : ℕ} (h : ContfracLegendre.Ass ξ u v) :
    ∃ n, Checked.div (u : ℚ) (v : ℚ)
      (Nat.cast_ne_zero.mpr (by exact_mod_cast h.den_ne_zero)).isUnit = ξ.convergent n := by
  induction v using Nat.strong_induction_on generalizing ξ u with | h v ih => ?_
  rcases lt_trichotomy v 1 with (ht | rfl | ht)
  · -- the denominator is nonzero
    exact absurd (Nat.lt_one_iff.mp ht) (by exact_mod_cast h.den_ne_zero)
  · simp only [Nat.cast_one, div_one₀]
    obtain ⟨_, h₁, _, h₂⟩ := h
    rcases le_or_gt (u : ℝ) ξ with ht | ht
    · use 0
      rw [convergent_zero, Rat.intCast_inj, eq_comm, floor_eq_iff]
      convert! And.intro ht (sub_lt_iff_lt_add'.mp (abs_lt.mp h₂).2) <;> norm_num
    · replace h₁ := lt_sub_iff_add_lt'.mp (h₁ rfl)
      have hξ₁ : ⌊ξ⌋ = u - 1 := by
        rw [floor_eq_iff, cast_sub, cast_one, sub_add_cancel]
        exact ⟨(((sub_lt_sub_iff_left _).mpr one_half_lt_one).trans h₁).le, ht⟩
      rcases eq_or_ne ξ ⌊ξ⌋ with Hξ | Hξ
      · rw [Hξ, hξ₁, cast_sub, cast_one, ← sub_eq_add_neg, sub_lt_sub_iff_left] at h₁
        exact False.elim (lt_irrefl _ <| h₁.trans one_half_lt_one)
      · have hf : fract ξ ≠ 0 := (fract_pos.mpr Hξ).ne'
        have hξ₂ : ⌊(fract ξ)⁻¹⌋ = 1 := by
          rw [floor_eq_iff, cast_one, le_inv_comm₀ zero_lt_one (fract_pos.mpr Hξ), inv_one₀,
            one_add_one_eq_two, inv_lt_comm₀ (fract_pos.mpr Hξ) zero_lt_two]
          refine ⟨(fract_lt_one ξ).le, ?_⟩
          rw [fract, hξ₁, cast_sub, cast_one, lt_sub_iff_add_lt', sub_add]
          convert! h₁ using 1
          rw [sub_eq_add_neg]
          norm_num
        use 1
        rw [convergent_succ _ _ hf]
        simp only [convergent_zero, hξ₁, hξ₂, cast_sub, cast_one, inv_one₀, sub_add_cancel]
  · have hv₂ : (2 : ℤ) ≤ v := Nat.cast_le.mpr ht
    obtain ⟨huv₀, huv₁⟩ := aux₂ hv₂ h
    have hξ₀ := aux₁ hv₂ h
    have huv₁' : (u - ⌊ξ⌋ * v).toNat < v := by zify; rwa [toNat_of_nonneg huv₀.le]
    have inv : ContfracLegendre.Ass (fract ξ)⁻¹ v (u - ⌊ξ⌋ * ↑v).toNat :=
      (toNat_of_nonneg huv₀.le).symm ▸ invariant hv₂ h
    obtain ⟨n, hn⟩ := ih (u - ⌊ξ⌋ * v).toNat huv₁' inv
    use n + 1
    have hw : (((u - ⌊ξ⌋ * v).toNat : ℕ) : ℚ) = ((u - ⌊ξ⌋ * v : ℤ) : ℚ) := by
      exact_mod_cast toNat_of_nonneg huv₀.le
    have hc : (fract ξ)⁻¹.convergent n = (v : ℚ) / ((u - ⌊ξ⌋ * v : ℤ) : ℚ) := by
      rw [← hn]
      simp only [hw, cast_natCast]
    rw [convergent_succ _ _ hξ₀.ne']
    simp only [hc, inv_div₀, cast_sub, cast_mul, cast_natCast]
    rw [sub_div, mul_div_cancel_right₀, add_sub_cancel]

/-- The main result, *Legendre's Theorem* on rational approximation:
if `ξ` is a real number and `q` is a rational number such that `|ξ - q| < 1/(2*q.den^2)`,
then `q` is a convergent of the continued fraction expansion of `ξ`.
This version uses `Real.convergent`. -/
theorem exists_rat_eq_convergent {q : ℚ} (h : |ξ - q| < 1 / (2 * (q.den : ℝ) ^ 2)) :
    ∃ n, q = ξ.convergent n := by
  refine q.num_div_den ▸ exists_rat_eq_convergent' ⟨?_, fun hd => ?_, ?_⟩
  · exact isCoprime_iff_nat_coprime.mpr (natAbs_natCast q.den ▸ q.reduced)
  · have hq₁ : q.den = 1 := Nat.cast_eq_one.mp hd
    have hq : (q : ℝ) = q.num := by exact_mod_cast (q.den_eq_one_iff.mp hq₁).symm
    simp only [hq₁, Nat.cast_one, one_pow, mul_one] at h
    simpa only [hq] using (abs_lt.mp h).1
  · obtain ⟨hq₀, hq₁⟩ := aux₀ (Nat.cast_pos.mpr q.pos)
    replace hq₁ := mul_pos hq₀ hq₁
    refine ⟨hq₁.ne'.isUnit, ?_⟩
    simp only [cast_natCast] at hq₀ hq₁ ⊢
    rw [← Rat.cast_def]
    refine h.trans ?_
    rw [← one_div₀]
    refine (one_div_lt_one_div (by positivity) hq₁).mpr ?_
    nlinarith

end Real
