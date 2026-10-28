/-
Copyright (c) 2021 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Super-Polynomial Function Decay

This file defines a predicate `Asymptotics.SuperpolynomialDecay f` for a function satisfying
one of the following equivalent definitions (the definition is in terms of the first condition):

* `x ^ n * f` tends to `𝓝 0` for all (or sufficiently large) naturals `n`
* `|x ^ n * f|` tends to `𝓝 0` for all naturals `n` (`superpolynomialDecay_iff_abs_tendsto_zero`)
* `|x ^ n * f|` is bounded for all naturals `n` (`superpolynomialDecay_iff_abs_isBoundedUnder`)
* `f` is `o(x ^ c)` for all integers `c` (`superpolynomialDecay_iff_isLittleO`)
* `f` is `O(x ^ c)` for all integers `c` (`superpolynomialDecay_iff_isBigO`)

These conditions are all equivalent to conditions in terms of polynomials, replacing `x ^ c` with
  `p(x)` or `p(x)⁻¹` as appropriate, since asymptotically `p(x)` behaves like `X ^ p.natDegree`.
These further equivalences are not proven in mathlib but would be good future projects.

The definition of superpolynomial decay for `f : α → β` is relative to a parameter `k : α → β`.
Super-polynomial decay then means `f x` decays faster than `(k x) ^ c` for all integers `c`.
Equivalently `f x` decays faster than `p.eval (k x)` for all polynomials `p : β[X]`.
The definition is also relative to a filter `l : Filter α` where the decay rate is compared.

When the map `k` is given by `n ↦ ↑n : ℕ → ℝ` this defines negligible functions:
https://en.wikipedia.org/wiki/Negligible_function

When the map `k` is given by `(r₁,...,rₙ) ↦ r₁*...*rₙ : ℝⁿ → ℝ` this is equivalent
  to the definition of rapidly decreasing functions given here:
https://ncatlab.org/nlab/show/rapidly+decreasing+function

## Main statements

* `SuperpolynomialDecay.polynomial_mul` says that if `f(x)` is negligible,
    then so is `p(x) * f(x)` for any polynomial `p`.
* `superpolynomialDecay_iff_zpow_tendsto_zero` gives an equivalence between definitions in terms
    of decaying faster than `k(x) ^ n` for all naturals `n` or `k(x) ^ c` for all integer `c`.
-/

@[expose] public section


namespace Asymptotics

open Polynomial

open scoped Topology

open Filter

/-- `f` has superpolynomial decay in parameter `k` along filter `l` if
  `k ^ n * f` tends to zero at `l` for all naturals `n` -/
def SuperpolynomialDecay {α β : Type*} [TopologicalSpace β] [CommSemiring β] (l : Filter α)
    (k : α → β) (f : α → β) :=
  ∀ n : ℕ, Tendsto (fun a : α => k a ^ n * f a) l (𝓝 0)

variable {α β : Type*} {l : Filter α} {k : α → β} {f g g' : α → β}

section CommSemiring

variable [TopologicalSpace β] [CommSemiring β]

theorem SuperpolynomialDecay.congr' (hf : SuperpolynomialDecay l k f) (hfg : f =ᶠ[l] g) :
    SuperpolynomialDecay l k g := fun z =>
  (hf z).congr' (EventuallyEq.mul (EventuallyEq.refl l _) hfg)

theorem SuperpolynomialDecay.congr (hf : SuperpolynomialDecay l k f) (hfg : ∀ x, f x = g x) :
    SuperpolynomialDecay l k g := fun z =>
  (hf z).congr fun x => (congr_arg fun a => k x ^ z * a) <| hfg x

@[simp]
theorem superpolynomialDecay_zero (l : Filter α) (k : α → β) : SuperpolynomialDecay l k 0 :=
  fun z => by simpa only [Pi.zero_apply, mul_zero] using tendsto_const_nhds

theorem SuperpolynomialDecay.add [ContinuousAdd β] (hf : SuperpolynomialDecay l k f)
    (hg : SuperpolynomialDecay l k g) : SuperpolynomialDecay l k (f + g) := fun z => by
  simpa only [mul_add, add_zero, Pi.add_apply] using (hf z).add (hg z)

theorem SuperpolynomialDecay.mul [ContinuousMul β] (hf : SuperpolynomialDecay l k f)
    (hg : SuperpolynomialDecay l k g) : SuperpolynomialDecay l k (f * g) := fun z => by
  simpa only [mul_assoc, one_mul, mul_zero, pow_zero] using! (hf z).mul (hg 0)

theorem SuperpolynomialDecay.mul_const [ContinuousMul β] (hf : SuperpolynomialDecay l k f) (c : β) :
    SuperpolynomialDecay l k fun n => f n * c := fun z => by
  simpa only [← mul_assoc, zero_mul] using Tendsto.mul_const c (hf z)

theorem SuperpolynomialDecay.const_mul [ContinuousMul β] (hf : SuperpolynomialDecay l k f) (c : β) :
    SuperpolynomialDecay l k fun n => c * f n :=
  (hf.mul_const c).congr fun _ => mul_comm _ _

theorem SuperpolynomialDecay.param_mul (hf : SuperpolynomialDecay l k f) :
    SuperpolynomialDecay l k (k * f) := fun z =>
  tendsto_nhds.2 fun s hs hs0 =>
    l.sets_of_superset ((tendsto_nhds.1 (hf <| z + 1)) s hs hs0) fun x hx => by
      simpa only [Set.mem_preimage, Pi.mul_apply, ← mul_assoc, ← pow_succ] using hx

theorem SuperpolynomialDecay.mul_param (hf : SuperpolynomialDecay l k f) :
    SuperpolynomialDecay l k (f * k) :=
  hf.param_mul.congr fun _ => mul_comm _ _

theorem SuperpolynomialDecay.param_pow_mul (hf : SuperpolynomialDecay l k f) (n : ℕ) :
    SuperpolynomialDecay l k (k ^ n * f) := by
  induction n with
  | zero => simpa only [one_mul, pow_zero] using hf
  | succ n hn => simpa only [pow_succ', mul_assoc] using hn.param_mul

theorem SuperpolynomialDecay.mul_param_pow (hf : SuperpolynomialDecay l k f) (n : ℕ) :
    SuperpolynomialDecay l k (f * k ^ n) :=
  (hf.param_pow_mul n).congr fun _ => mul_comm _ _

theorem SuperpolynomialDecay.polynomial_mul [ContinuousAdd β] [ContinuousMul β]
    (hf : SuperpolynomialDecay l k f) (p : β[X]) :
    SuperpolynomialDecay l k fun x => (p.eval <| k x) * f x :=
  Polynomial.induction_on' p (fun p q hp hq => by simpa [add_mul] using! hp.add hq) fun n c => by
    simpa [mul_assoc] using! (hf.param_pow_mul n).const_mul c

theorem SuperpolynomialDecay.mul_polynomial [ContinuousAdd β] [ContinuousMul β]
    (hf : SuperpolynomialDecay l k f) (p : β[X]) :
    SuperpolynomialDecay l k fun x => f x * (p.eval <| k x) :=
  (hf.polynomial_mul p).congr fun _ => mul_comm _ _

end CommSemiring

section OrderedCommSemiring

variable [TopologicalSpace β] [CommSemiring β] [PartialOrder β] [IsOrderedRing β] [OrderTopology β]

theorem SuperpolynomialDecay.trans_eventuallyLE (hk : 0 ≤ᶠ[l] k) (hg : SuperpolynomialDecay l k g)
    (hg' : SuperpolynomialDecay l k g') (hfg : g ≤ᶠ[l] f) (hfg' : f ≤ᶠ[l] g') :
    SuperpolynomialDecay l k f := fun z =>
  tendsto_of_tendsto_of_tendsto_of_le_of_le' (hg z) (hg' z)
    (by filter_upwards [hfg, hk] with x hx (hx' : 0 ≤ k x) using by gcongr)
    (by filter_upwards [hfg', hk] with x hx (hx' : 0 ≤ k x) using by gcongr)

end OrderedCommSemiring

section LinearOrderedCommRing

variable [TopologicalSpace β] [CommRing β] [LinearOrder β] [IsStrictOrderedRing β] [OrderTopology β]
variable (l k f)

theorem superpolynomialDecay_iff_abs_tendsto_zero :
    SuperpolynomialDecay l k f ↔ ∀ n : ℕ, Tendsto (fun a : α => |k a ^ n * f a|) l (𝓝 0) :=
  ⟨fun h z => (tendsto_zero_iff_abs_tendsto_zero _).1 (h z), fun h z =>
    (tendsto_zero_iff_abs_tendsto_zero _).2 (h z)⟩

theorem superpolynomialDecay_iff_superpolynomialDecay_abs :
    SuperpolynomialDecay l k f ↔ SuperpolynomialDecay l (fun a => |k a|) fun a => |f a| :=
  (superpolynomialDecay_iff_abs_tendsto_zero l k f).trans
    (by simp_rw [SuperpolynomialDecay, abs_mul, abs_pow])

variable {l k f}

theorem SuperpolynomialDecay.trans_eventually_abs_le (hf : SuperpolynomialDecay l k f)
    (hfg : abs ∘ g ≤ᶠ[l] abs ∘ f) : SuperpolynomialDecay l k g := by
  rw [superpolynomialDecay_iff_abs_tendsto_zero] at hf ⊢
  refine fun z =>
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hf z)
      (Eventually.of_forall fun x => abs_nonneg _) (hfg.mono fun x hx => ?_)
  calc
    |k x ^ z * g x| = |k x ^ z| * |g x| := abs_mul (k x ^ z) (g x)
    _ ≤ |k x ^ z| * |f x| := by gcongr _ * ?_; exact hx
    _ = |k x ^ z * f x| := (abs_mul (k x ^ z) (f x)).symm

theorem SuperpolynomialDecay.trans_abs_le (hf : SuperpolynomialDecay l k f)
    (hfg : ∀ x, |g x| ≤ |f x|) : SuperpolynomialDecay l k g :=
  hf.trans_eventually_abs_le (Eventually.of_forall hfg)

end LinearOrderedCommRing

section Field

variable [TopologicalSpace β] [Field β] (l k f)

theorem superpolynomialDecay_mul_const_iff [ContinuousMul β] {c : β} (hc0 : c ≠ 0) :
    (SuperpolynomialDecay l k fun n => f n * c) ↔ SuperpolynomialDecay l k f :=
  ⟨fun h => (h.mul_const c⁻¹).congr fun x => by simp [mul_assoc], fun h => h.mul_const c⟩

theorem superpolynomialDecay_const_mul_iff [ContinuousMul β] {c : β} (hc0 : c ≠ 0) :
    (SuperpolynomialDecay l k fun n => c * f n) ↔ SuperpolynomialDecay l k f :=
  ⟨fun h => (h.const_mul c⁻¹).congr fun x => by simp [← mul_assoc], fun h => h.const_mul c⟩

end Field

section LinearOrderedField

variable [TopologicalSpace β] [Field β] [LinearOrder β] [IsStrictOrderedRing β] [OrderTopology β]
variable (f)

theorem superpolynomialDecay_iff_abs_isBoundedUnder (hk : Tendsto k l atTop) :
    SuperpolynomialDecay l k f ↔
    ∀ z : ℕ, IsBoundedUnder (· ≤ ·) l fun a : α => |k a ^ z * f a| := by
  refine
    ⟨fun h z => Tendsto.isBoundedUnder_le (Tendsto.abs (h z)), fun h =>
      (superpolynomialDecay_iff_abs_tendsto_zero l k f).2 fun z => ?_⟩
  obtain ⟨m, hm⟩ := h (z + 1)
  -- Where `k` does not vanish, which is eventually, `k a ^ z * f a` is
  -- `(k a)⁻¹ * (k a ^ (z + 1) * f a)`.
  rw [← Filter.tendsto_comap_val_iff (hk.eventually_ne_atTop 0)]
  have h1 : Tendsto (fun _ : {a // k a ≠ 0} => (0 : β)) (comap Subtype.val l) (𝓝 0) :=
    tendsto_const_nhds
  have h2 : Tendsto (fun a : {a // k a ≠ 0} => |Checked.inv (k a) a.2.isUnit| * m)
      (comap Subtype.val l) (𝓝 0) := by
    have h := ((tendsto_zero_iff_abs_tendsto_zero _).1
      ((hk.comp (tendsto_comap (f := (Subtype.val : {a // k a ≠ 0} → α)))).fun_inv_tendsto_atTop
        (h0 := fun a : {a // k a ≠ 0} => a.2.isUnit))).mul_const m
    rwa [zero_mul] at h
  refine
    tendsto_of_tendsto_of_tendsto_of_le_of_le' h1 h2 (Eventually.of_forall fun x => abs_nonneg _)
      ?_
  filter_upwards [tendsto_comap.eventually (eventually_map.1 hm)] with a ha
  refine Eq.trans_le ?_ (mul_le_mul_of_nonneg_left ha <| abs_nonneg _)
  rw [← abs_mul, ← mul_assoc, pow_succ', ← mul_assoc, inv_mul_cancel₀, one_mul]

/-- For negative exponents, the power `k a ^ z` is taken on the subtype `{a // k a ≠ 0}` where it
is defined, with the filter `comap Subtype.val l`. -/
theorem superpolynomialDecay_iff_zpow_tendsto_zero (hk : Tendsto k l atTop) :
    SuperpolynomialDecay l k f ↔ ∀ z : ℤ,
      Tendsto (fun a : {a // k a ≠ 0} => Checked.zpow (k a) z (fun _ => a.2.isUnit) * f a)
        (comap Subtype.val l) (𝓝 0) := by
  refine ⟨fun h z => ?_, fun h n => ?_⟩
  · by_cases! hz : 0 ≤ z
    · lift z to ℕ using hz
      simpa [Function.comp_def] using (h z).comp tendsto_comap
    · have hu : Tendsto (fun a : {a // k a ≠ 0} => (⟨k a, a.2.isUnit⟩ : {x : β | IsUnit x}))
          (comap Subtype.val l) (comap Subtype.val atTop) :=
        tendsto_comap_iff.mpr (hk.comp tendsto_comap)
      have h₁ : Tendsto (fun a : {a // k a ≠ 0} => Checked.zpow (k a) z (fun _ => a.2.isUnit))
          (comap Subtype.val l) (𝓝 0) :=
        (tendsto_zpow_atTop_zero hz).comp hu
      have h₂ : Tendsto (fun a : {a // k a ≠ 0} => f a) (comap Subtype.val l) (𝓝 0) := by
        simpa [Function.comp_def] using (h 0).comp tendsto_comap
      have h₃ := h₁.mul h₂
      rwa [mul_zero] at h₃
  · rw [← Filter.tendsto_comap_val_iff (hk.eventually_ne_atTop 0)]
    simpa using h n

variable {f}

theorem SuperpolynomialDecay.param_zpow_mul (hk : Tendsto k l atTop)
    (hf : SuperpolynomialDecay l k f) (z : ℤ) {hkz : ∀ a, z < 0 → IsUnit (k a)} :
    SuperpolynomialDecay l k fun a => Checked.zpow (k a) z (hkz a) * f a := by
  rw [superpolynomialDecay_iff_zpow_tendsto_zero _ hk] at hf ⊢
  refine fun z' => (hf <| z' + z).congr fun a => ?_
  simp [zpow_add₀ a.2, mul_assoc]

theorem SuperpolynomialDecay.mul_param_zpow (hk : Tendsto k l atTop)
    (hf : SuperpolynomialDecay l k f) (z : ℤ) {hkz : ∀ a, z < 0 → IsUnit (k a)} :
    SuperpolynomialDecay l k fun a => f a * Checked.zpow (k a) z (hkz a) :=
  (hf.param_zpow_mul hk z (hkz := hkz)).congr fun _ => mul_comm _ _

theorem SuperpolynomialDecay.inv_param_mul {hk0 : IsUnit k} (hk : Tendsto k l atTop)
    (hf : SuperpolynomialDecay l k f) : SuperpolynomialDecay l k (k⁻¹ * f) := by
  have hka : ∀ a, IsUnit (k a) := Pi.isUnit_iff.mp hk0
  refine (hf.param_zpow_mul hk (-1) (hkz := fun a _ => hka a)).congr fun a => ?_
  rw [Pi.mul_apply, Pi.inv_apply₀, zpow_neg_one₀]

theorem SuperpolynomialDecay.param_inv_mul {hk0 : IsUnit k} (hk : Tendsto k l atTop)
    (hf : SuperpolynomialDecay l k f) : SuperpolynomialDecay l k (f * k⁻¹) :=
  (hf.inv_param_mul hk).congr fun _ => mul_comm _ _

variable (f)

theorem superpolynomialDecay_param_mul_iff (hk : Tendsto k l atTop) :
    SuperpolynomialDecay l k (k * f) ↔ SuperpolynomialDecay l k f := by
  refine ⟨fun h => h.trans_eventually_abs_le ((hk.eventually_ge_atTop 1).mono fun x hx => ?_),
    fun h => h.param_mul⟩
  simp only [Function.comp_apply, Pi.mul_apply, abs_mul]
  exact le_mul_of_one_le_left (abs_nonneg _) (hx.trans (le_abs_self _))

theorem superpolynomialDecay_mul_param_iff (hk : Tendsto k l atTop) :
    SuperpolynomialDecay l k (f * k) ↔ SuperpolynomialDecay l k f := by
  simpa [mul_comm k] using superpolynomialDecay_param_mul_iff f hk

theorem superpolynomialDecay_param_pow_mul_iff (hk : Tendsto k l atTop) (n : ℕ) :
    SuperpolynomialDecay l k (k ^ n * f) ↔ SuperpolynomialDecay l k f := by
  induction n with
  | zero => simp
  | succ n hn =>
    simpa [pow_succ, ← mul_comm k, mul_assoc,
      superpolynomialDecay_param_mul_iff (k ^ n * f) hk] using hn

theorem superpolynomialDecay_mul_param_pow_iff (hk : Tendsto k l atTop) (n : ℕ) :
    SuperpolynomialDecay l k (f * k ^ n) ↔ SuperpolynomialDecay l k f := by
  simpa [mul_comm f] using superpolynomialDecay_param_pow_mul_iff f hk n

end LinearOrderedField

section NormedLinearOrderedField

variable [NormedField β]
variable (l k f)

theorem superpolynomialDecay_iff_norm_tendsto_zero :
    SuperpolynomialDecay l k f ↔ ∀ n : ℕ, Tendsto (fun a : α => ‖k a ^ n * f a‖) l (𝓝 0) :=
  ⟨fun h z => tendsto_zero_iff_norm_tendsto_zero.1 (h z), fun h z =>
    tendsto_zero_iff_norm_tendsto_zero.2 (h z)⟩

theorem superpolynomialDecay_iff_superpolynomialDecay_norm :
    SuperpolynomialDecay l k f ↔ SuperpolynomialDecay l (fun a => ‖k a‖) fun a => ‖f a‖ :=
  (superpolynomialDecay_iff_norm_tendsto_zero l k f).trans (by simp [SuperpolynomialDecay])

variable {l k}
variable [LinearOrder β] [IsStrictOrderedRing β] [OrderTopology β]

/-- The powers `k a ^ z` are taken on the subtype `{a // k a ≠ 0}` where they are defined, with
the filter `comap Subtype.val l`. -/
theorem superpolynomialDecay_iff_isBigO (hk : Tendsto k l atTop) :
    SuperpolynomialDecay l k f ↔ ∀ z : ℤ, (fun a : {a // k a ≠ 0} => f a) =O[comap Subtype.val l]
      fun a => Checked.zpow (k a) z (fun _ => a.2.isUnit) := by
  refine (superpolynomialDecay_iff_zpow_tendsto_zero f hk).trans ⟨fun h z => ?_, fun h z => ?_⟩
  · refine ((isBigO_refl (fun a : {a // k a ≠ 0} => Checked.zpow (k a) z (fun _ => a.2.isUnit))
      _).mul ((h (-z)).isBigO_one β)).congr (fun a => ?_) fun a => mul_one _
    rw [← mul_assoc, ← zpow_add₀ a.2]
    simp
  · suffices (fun a : {a // k a ≠ 0} => Checked.zpow (k a) z (fun _ => a.2.isUnit) * f a)
        =O[comap Subtype.val l] fun a => Checked.inv (k a) a.2.isUnit from
      IsBigO.trans_tendsto this
        ((hk.comp tendsto_comap).fun_inv_tendsto_atTop (h0 := fun a : {a // k a ≠ 0} => a.2.isUnit))
    refine ((isBigO_refl (fun a : {a // k a ≠ 0} => Checked.zpow (k a) z (fun _ => a.2.isUnit))
      _).mul (h (-(z + 1)))).trans ?_
    refine .of_bound' <| Eventually.of_forall fun a => ?_
    simp [← zpow_add₀ a.2]

/-- The powers `k a ^ z` are taken on the subtype `{a // k a ≠ 0}` where they are defined, with
the filter `comap Subtype.val l`. -/
theorem superpolynomialDecay_iff_isLittleO (hk : Tendsto k l atTop) :
    SuperpolynomialDecay l k f ↔ ∀ z : ℤ, (fun a : {a // k a ≠ 0} => f a) =o[comap Subtype.val l]
      fun a => Checked.zpow (k a) z (fun _ => a.2.isUnit) := by
  refine ⟨fun h z => ?_, fun h => (superpolynomialDecay_iff_isBigO f hk).2 fun z => (h z).isBigO⟩
  have h1 : (fun _ : {a // k a ≠ 0} => (1 : β)) =o[comap Subtype.val l] fun a => k a := by
    refine isLittleO_of_tendsto (fun a h => absurd h a.2) ?_
    refine (Filter.tendsto_comap_val_iff (Eventually.of_forall fun x => x.2)
      (F := fun a : {a // k a ≠ 0} => Checked.div 1 (k a) a.2.isUnit)).2 ?_
    simpa [one_div₀] using (hk.comp tendsto_comap).fun_inv_tendsto_atTop
      (h0 := fun a : {a // k a ≠ 0} => a.2.isUnit)
  have h2 : (fun a : {a // k a ≠ 0} => f a) =o[comap Subtype.val l]
      fun a => k a * Checked.zpow (k a) (z - 1) (fun _ => a.2.isUnit) := by
    simpa using h1.mul_isBigO ((superpolynomialDecay_iff_isBigO f hk).1 h (z - 1))
  refine h2.trans_isBigO <| IsBigO.of_bound' <| Eventually.of_forall fun a => le_of_eq ?_
  simp [← zpow_one_add₀ a.2]

end NormedLinearOrderedField

end Asymptotics
