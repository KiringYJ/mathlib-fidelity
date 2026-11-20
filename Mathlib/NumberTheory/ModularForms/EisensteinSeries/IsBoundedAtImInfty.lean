/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Defs
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable
public import Mathlib.NumberTheory.ModularForms.Identities

/-!
# Boundedness of Eisenstein series

We show that Eisenstein series of weight `k` and level `Γ(N)` with congruence condition
`a : Fin 2 → ZMod N` are bounded at infinity.

## Outline of argument

We need to bound the value of the Eisenstein series (acted on by `A : SL(2,ℤ)`)
at a given point `z` in the upper half plane. Since these are modular forms of level `Γ(N)`,
it suffices to prove this for `z ∈ verticalStrip N z.im`.

We can then, first observe that the slash action just changes our `a` to `(a ᵥ* A)` and
we then use our bounds for Eisenstein series in these vertical strips to get the result.
-/

public section

noncomputable section

open ModularForm UpperHalfPlane Matrix SlashInvariantForm CongruenceSubgroup

open scoped MatrixGroups

namespace EisensteinSeries

lemma summable_norm_eisSummand {k : ℤ} (hk : 3 ≤ k) (z : ℍ) :
    Summable fun x : {x : Fin 2 → ℤ // x ≠ 0} ↦ ‖eisSummand k x z (fun _ ↦ x.property)‖ := by
  have hk' : (2 : ℝ) < k := by norm_cast
  apply (((summable_one_div_norm_rpow hk').subtype (fun x ↦ x ≠ 0)).mul_left
      (r z ^ (-k : ℝ))).of_nonneg_of_le
    (fun _ ↦ norm_nonneg _)
  intro b
  have hpow := Real.rpow_intCast ‖(b.val 0 : ℂ) * z + b.val 1‖ (-k)
    (h := fun _ ↦ norm_ne_zero_iff.mpr (eisSummand_base_ne_zero b.property z))
  simpa only [Function.comp_apply, eisSummand, norm_zpow, ← hpow, Int.cast_neg] using
    summand_bound z (show 0 ≤ (k : ℝ) by positivity) b.val

/-- The norm of the restricted sum is less than the full sum of the norms. -/
lemma norm_le_tsum_norm (N : ℕ) (a : Fin 2 → ZMod N) (k : ℤ) (hk : 3 ≤ k) (z : ℍ) :
    ‖eisensteinSeries a k z‖ ≤
      ∑' x : {x : Fin 2 → ℤ // x ≠ 0}, ‖eisSummand k x z (fun _ ↦ x.property)‖ := by
  let q (x : gammaSet N 1 a) : {x : Fin 2 → ℤ // x ≠ 0} := ⟨x.val, gammaSet_ne_zero x one_ne_zero⟩
  have hq : Function.Injective q := fun _ _ h ↦
    Subtype.ext (congrArg (fun x : {x : Fin 2 → ℤ // x ≠ 0} ↦ x.val) h)
  have hs := summable_norm_eisSummand hk z
  have hsq := hs.comp_injective hq
  exact (norm_tsum_le_tsum_norm hsq).trans
    (hsq.tsum_le_tsum_of_inj q hq (fun _ _ ↦ norm_nonneg _) (fun _ ↦ le_rfl) hs)

/-- Eisenstein series are bounded at infinity. -/
theorem isBoundedAtImInfty_eisensteinSeriesSIF {N : ℕ} [NeZero N] (a : Fin 2 → ZMod N) {k : ℤ}
    (hk : 3 ≤ k) (A : SL(2, ℤ)) : IsBoundedAtImInfty (eisensteinSeriesSIF a k ∣[k] A) := by
  simp_rw [UpperHalfPlane.isBoundedAtImInfty_iff, eisensteinSeriesSIF] at *
  refine ⟨∑' x : {x : Fin 2 → ℤ // x ≠ 0},
    r ⟨⟨N, 2⟩, Nat.ofNat_pos⟩ ^ (-k : ℝ) * ‖x.val‖ ^ (-k : ℝ), 2, ?_⟩
  intro z hz
  obtain ⟨n, hn⟩ := (ModularGroup_T_zpow_mem_verticalStrip z (NeZero.pos N))
  rw [SlashInvariantForm.coe_mk, eisensteinSeries_slash_apply, ← eisensteinSeriesSIF_apply,
    ← T_zpow_width_invariant N k n (eisensteinSeriesSIF (a ᵥ* A) k) z]
  apply le_trans (norm_le_tsum_norm N (a ᵥ* A) k hk _)
  have hk' : (2 : ℝ) < k := by norm_cast
  apply (summable_norm_eisSummand hk _).tsum_le_tsum _
  · exact ((summable_one_div_norm_rpow hk').subtype (fun x ↦ x ≠ 0)).mul_left
      (r ⟨⟨N, 2⟩, Nat.ofNat_pos⟩ ^ (-k : ℝ))
  · intro x
    have hpow (w : ℍ) := Real.rpow_intCast ‖(x.val 0 : ℂ) * w + x.val 1‖ (-k)
      (h := fun _ ↦ norm_ne_zero_iff.mpr (eisSummand_base_ne_zero x.property w))
    simpa only [eisSummand, norm_zpow, ← hpow, Int.cast_neg] using
      summand_bound_of_mem_verticalStrip (lt_trans two_pos hk').le x.val two_pos
        (verticalStrip_anti_right N hz hn)

end EisensteinSeries
