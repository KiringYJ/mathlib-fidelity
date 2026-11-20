/-
Copyright (c) 2023 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Algebra.Order.ToIntervalMod
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Interval.Set.Group

/-!
# Akra-Bazzi theorem: the polynomial growth condition

This file defines and develops an API for the polynomial growth condition that appears in the
statement of the Akra-Bazzi theorem: for the theorem to hold, the function `g` must
satisfy the condition that `c₁ g(n) ≤ g(u) ≤ c₂ g(n)`, for `u` between `b*n` and `n` for any
constant `b ∈ (0,1)`.

## Implementation notes

Our definition requires that the condition hold for any `b ∈ (0,1)`. This is equivalent to requiring
it only for `b = 1 / 2` (or any other particular value in `(0, 1)`). While this could, in principle,
make it harder to prove that a particular function grows polynomially, this issue does not seem to
arise in practice.

-/

@[expose] public section

open Real Filter Asymptotics
open scoped Topology

namespace AkraBazziRecurrence

/-- The growth condition that the function `g` must satisfy for the Akra-Bazzi theorem to apply.
It roughly states that `c₁ g(n) ≤ g(u) ≤ c₂ g(n)`, for `u` between `b * n` and `n`, for any
constant `b ∈ (0, 1)`. For a function on a domain `D`, the bounds compare two points of `D`
using their real coordinates. -/
def GrowsPolynomially {D : Type*} (f : D → ℝ) (coord : D → ℝ := by exact id) : Prop :=
  ∀ b ∈ Set.Ioo 0 1, ∃ c₁ > 0, ∃ c₂ > 0,
    ∀ᶠ x in comap coord atTop, ∀ u : D, coord u ∈ Set.Icc (b * coord x) (coord x) →
      f u ∈ Set.Icc (c₁ * f x) (c₂ * f x)

namespace GrowsPolynomially

/-- On the ambient real line the growth bound uses the usual filter at infinity. -/
lemma ambient_iff {f : ℝ → ℝ} : GrowsPolynomially f ↔
    ∀ b ∈ Set.Ioo 0 1, ∃ c₁ > 0, ∃ c₂ > 0,
      ∀ᶠ x in atTop, ∀ u ∈ Set.Icc (b * x) x, f u ∈ Set.Icc (c₁ * f x) (c₂ * f x) := by
  simp only [GrowsPolynomially, comap_id, id_eq]

/-- Pull back a growth bound to another index domain with the induced coordinates. -/
lemma comp_domain {D D' : Type*} {coord : D → ℝ} {f : D → ℝ} (hf : GrowsPolynomially f coord)
    (i : D' → D) : GrowsPolynomially (f ∘ i) (coord ∘ i) := by
  intro b hb
  obtain ⟨a, ha, d, hd, H⟩ := hf b hb
  have hi : Tendsto i (comap (coord ∘ i) atTop) (comap coord atTop) :=
    tendsto_comap_iff.mpr tendsto_comap
  exact ⟨a, ha, d, hd, (hi.eventually H).mono fun _ hx u hu ↦ hx (i u) hu⟩

/-- Transfer a growth bound back to an ambient function when its values agree on a tail
contained in the domain. -/
lemma of_eventuallyEq_on {s : Set ℝ} {g : s → ℝ} {f : ℝ → ℝ} (hg : GrowsPolynomially g Subtype.val)
    (hs : ∀ᶠ x in atTop, x ∈ s) (he : ∀ᶠ x in atTop, ∀ h : x ∈ s, g ⟨x, h⟩ = f x) :
    GrowsPolynomially f := by
  rw [ambient_iff]
  intro b hb
  obtain ⟨a, ha, d, hd, H⟩ := hg b hb
  rw [eventually_comap] at H
  have htail := (tendsto_id.const_mul_atTop hb.1).eventually_forall_ge_atTop (hs.and he)
  refine ⟨a, ha, d, hd, ?_⟩
  filter_upwards [H, hs, he, htail] with x hx hxs hxe hU
  intro u hu
  obtain ⟨hus, hue⟩ := hU u hu.1
  simpa only [hxe hxs, hue hus] using hx ⟨x, hxs⟩ rfl ⟨u, hus⟩ hu

lemma congr_of_eventuallyEq {f g : ℝ → ℝ} (hfg : f =ᶠ[atTop] g) (hg : GrowsPolynomially g) :
    GrowsPolynomially f := by
  rw [GrowsPolynomially.ambient_iff]
  intro b hb
  have hg' := (GrowsPolynomially.ambient_iff.mp hg) b hb
  obtain ⟨c₁, hc₁_mem, c₂, hc₂_mem, hg'⟩ := hg'
  refine ⟨c₁, hc₁_mem, c₂, hc₂_mem, ?_⟩
  filter_upwards [hg', (tendsto_id.const_mul_atTop hb.1).eventually_forall_ge_atTop hfg, hfg]
    with x hx₁ hx₂ hx₃
  intro u hu
  rw [hx₂ u hu.1, hx₃]
  exact hx₁ u hu

lemma iff_eventuallyEq {f g : ℝ → ℝ} (h : f =ᶠ[atTop] g) :
    GrowsPolynomially f ↔ GrowsPolynomially g :=
  ⟨fun hf => congr_of_eventuallyEq h.symm hf, fun hg => congr_of_eventuallyEq h hg⟩

variable {f : ℝ → ℝ}

lemma eventually_atTop_le {b : ℝ} (hb : b ∈ Set.Ioo 0 1) (hf : GrowsPolynomially f) :
    ∃ c > 0, ∀ᶠ x in atTop, ∀ u ∈ Set.Icc (b * x) x, f u ≤ c * f x := by
  obtain ⟨c₁, _, c₂, hc₂, h⟩ := (GrowsPolynomially.ambient_iff.mp hf) b hb
  refine ⟨c₂, hc₂, ?_⟩
  filter_upwards [h]
  exact fun _ H u hu => (H u hu).2

lemma eventually_atTop_le_nat {b : ℝ} (hb : b ∈ Set.Ioo 0 1) (hf : GrowsPolynomially f) :
    ∃ c > 0, ∀ᶠ (n : ℕ) in atTop, ∀ u ∈ Set.Icc (b * n) n, f u ≤ c * f n := by
  obtain ⟨c, hc_mem, hc⟩ := hf.eventually_atTop_le hb
  exact ⟨c, hc_mem, hc.natCast_atTop⟩

lemma eventually_atTop_ge {b : ℝ} (hb : b ∈ Set.Ioo 0 1) (hf : GrowsPolynomially f) :
    ∃ c > 0, ∀ᶠ x in atTop, ∀ u ∈ Set.Icc (b * x) x, c * f x ≤ f u := by
  obtain ⟨c₁, hc₁, c₂, _, h⟩ := (GrowsPolynomially.ambient_iff.mp hf) b hb
  refine ⟨c₁, hc₁, ?_⟩
  filter_upwards [h]
  exact fun _ H u hu => (H u hu).1

lemma eventually_atTop_ge_nat {b : ℝ} (hb : b ∈ Set.Ioo 0 1) (hf : GrowsPolynomially f) :
    ∃ c > 0, ∀ᶠ (n : ℕ) in atTop, ∀ u ∈ Set.Icc (b * n) n, c * f n ≤ f u := by
  obtain ⟨c, hc_mem, hc⟩ := hf.eventually_atTop_ge hb
  exact ⟨c, hc_mem, hc.natCast_atTop⟩

private lemma forall_ge_of_half_interval {x : ℝ} (hx : 1 ≤ x) {P : ℝ → Prop} (h₀ : P x)
    (step : ∀ y ≥ x, ∀ u ∈ Set.Icc ((1 / 2 : ℝ) * y) y, P u → P y) :
    ∀ y ≥ x, P y := by
  have H (n : ℕ) : ∀ y ≥ x, y ≤ x + (n : ℝ) → P y := by
    induction n with
    | zero =>
      intro y hy h
      have e : y = x := le_antisymm (by simpa using h) hy
      simpa only [e] using h₀
    | succ n ih =>
      intro y hy h
      by_cases h' : y ≤ x + n
      · exact ih y hy h'
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
      rw [Nat.cast_succ] at h
      have h₂ : y ≤ 2 * (x + n) := by linarith
      apply step y hy (x + n) ⟨?_, (lt_of_not_ge h').le⟩
        (ih _ (by linarith) le_rfl)
      calc
        (1 / 2 : ℝ) * y ≤ (1 / 2) * (2 * (x + n)) :=
          mul_le_mul_of_nonneg_left h₂ (by norm_num)
        _ = x + n := by
          rw [← mul_assoc, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_mul]
  intro y hy
  obtain ⟨n, hn⟩ := exists_nat_gt (y - x)
  exact H n y hy (by linarith)

lemma eventually_atTop_zero_or_pos_or_neg (hf : GrowsPolynomially f) :
    (∀ᶠ x in atTop, f x = 0) ∨ (∀ᶠ x in atTop, 0 < f x) ∨
      (∀ᶠ x in atTop, f x < 0) := by
  obtain ⟨a, ha, d, hd, H⟩ := (ambient_iff.mp hf) (1 / 2) (by norm_num)
  obtain ⟨T, hT⟩ := eventually_atTop.mp H
  let x := max T 1
  have extend (P : ℝ → Prop) (h₀ : P (f x))
      (hs : ∀ v w : ℝ, w ∈ Set.Icc (a * v) (d * v) → P w → P v) :
      ∀ᶠ y in atTop, P (f y) := by
    refine eventually_atTop.mpr ⟨x, forall_ge_of_half_interval (le_max_right T 1) h₀ ?_⟩
    intro y hy u hu hPu
    exact hs _ _ (hT y ((le_max_left T 1).trans hy) u hu) hPu
  rcases lt_trichotomy (f x) 0 with h | h | h
  · right; right
    apply extend (· < 0) h
    intro v w hw hw'
    by_contra! hv
    exact hw'.not_ge ((mul_nonneg ha.le hv).trans hw.1)
  · left
    apply extend (· = 0) h
    intro v w hw hw'
    rcases lt_trichotomy v 0 with hv | hv | hv
    · linarith only [hw', hw.2, mul_neg_of_pos_of_neg hd hv]
    · exact hv
    · linarith only [hw', hw.1, mul_pos ha hv]
  · right; left
    apply extend (0 < ·) h
    intro v w hw hw'
    by_contra! hv
    exact hw'.not_ge (hw.2.trans (mul_nonpos_of_nonneg_of_nonpos hd.le hv))

lemma eventually_zero_of_frequently_zero (hf : GrowsPolynomially f)
    (hz : ∃ᶠ x in atTop, f x = 0) : ∀ᶠ x in atTop, f x = 0 := by
  rcases hf.eventually_atTop_zero_or_pos_or_neg with h | h | h
  · exact h
  · exact False.elim (hz (h.mono fun _ hx => hx.ne'))
  · exact False.elim (hz (h.mono fun _ hx => hx.ne))

lemma eventually_atTop_nonneg_or_nonpos (hf : GrowsPolynomially f) :
    (∀ᶠ x in atTop, 0 ≤ f x) ∨ (∀ᶠ x in atTop, f x ≤ 0) := by
  rcases hf.eventually_atTop_zero_or_pos_or_neg with h | h | h
  · exact Or.inl (h.mono fun _ hx => hx.ge)
  · exact Or.inl (h.mono fun _ hx => hx.le)
  · exact Or.inr (h.mono fun _ hx => hx.le)

protected lemma neg {f : ℝ → ℝ} (hf : GrowsPolynomially f) : GrowsPolynomially (-f) := by
  rw [GrowsPolynomially.ambient_iff]
  intro b hb
  obtain ⟨c₁, hc₁_mem, c₂, hc₂_mem, hf⟩ := (GrowsPolynomially.ambient_iff.mp hf) b hb
  refine ⟨c₂, hc₂_mem, c₁, hc₁_mem, ?_⟩
  filter_upwards [hf] with x hx
  intro u hu
  simp only [Pi.neg_apply, Set.neg_mem_Icc_iff, neg_mul_eq_mul_neg, neg_neg]
  exact hx u hu

protected lemma neg_iff {f : ℝ → ℝ} : GrowsPolynomially f ↔ GrowsPolynomially (-f) :=
  ⟨fun hf => hf.neg, fun hf => by rw [← neg_neg f]; exact hf.neg⟩

protected lemma abs {D : Type*} {coord : D → ℝ} {f : D → ℝ} (hf : GrowsPolynomially f coord) :
    GrowsPolynomially (fun x => |f x|) coord := by
  intro b hb
  obtain ⟨a, ha, d, hd, H⟩ := hf b hb
  refine ⟨min a d, lt_min ha hd, max a d, lt_max_of_lt_left ha, ?_⟩
  filter_upwards [H] with x hx u hu
  have h := hx u hu
  rcases le_or_gt 0 (f x) with hfx | hfx
  · have hfu := (mul_nonneg ha.le hfx).trans h.1
    rw [abs_of_nonneg hfx, abs_of_nonneg hfu]
    exact ⟨(mul_le_mul_of_nonneg_right (min_le_left ..) hfx).trans h.1,
      h.2.trans (mul_le_mul_of_nonneg_right (le_max_right ..) hfx)⟩
  · have hfu := h.2.trans (mul_nonpos_of_nonneg_of_nonpos hd.le hfx.le)
    rw [abs_of_neg hfx, abs_of_nonpos hfu, mul_neg, mul_neg]
    exact ⟨neg_le_neg (h.2.trans (mul_le_mul_of_nonpos_right (min_le_right ..) hfx.le)),
      neg_le_neg ((mul_le_mul_of_nonpos_right (le_max_left ..) hfx.le).trans h.1)⟩

protected lemma norm {D : Type*} {coord : D → ℝ} {f : D → ℝ} (hf : GrowsPolynomially f coord) :
    GrowsPolynomially (fun x => ‖f x‖) coord := by
  simpa only [Real.norm_eq_abs] using hf.abs

lemma congr_on {D : Type*} {coord : D → ℝ} {f g : D → ℝ}
    (h : f =ᶠ[comap coord atTop] g) (hg : GrowsPolynomially g coord) :
    GrowsPolynomially f coord := by
  intro b hb
  obtain ⟨a, ha, d, hd, H⟩ := hg b hb
  change ∀ᶠ x in comap coord atTop, f x = g x at h
  rw [eventually_comap] at h
  refine ⟨a, ha, d, hd, ?_⟩
  filter_upwards [H, tendsto_comap.eventually h, tendsto_comap.eventually
    ((tendsto_id.const_mul_atTop hb.1).eventually_forall_ge_atTop h)] with x hx h₁ h₂ u hu
  rw [h₁ x rfl, h₂ (coord u) hu.1 u rfl]
  exact hx u hu

end GrowsPolynomially

variable {f : ℝ → ℝ}

lemma growsPolynomially_const {c : ℝ} : GrowsPolynomially (fun _ : ℝ => c) := by
  refine fun _ _ => ⟨1, by norm_num, 1, by norm_num, ?_⟩
  filter_upwards [] with x
  simp

lemma growsPolynomially_id : GrowsPolynomially (fun x => x) := by
  rw [GrowsPolynomially.ambient_iff]
  intro b hb
  refine ⟨b, hb.1, ?_⟩
  refine ⟨1, by norm_num, ?_⟩
  filter_upwards with x u hu
  simp only [one_mul, Set.mem_Icc]
  exact ⟨hu.1, hu.2⟩

protected lemma GrowsPolynomially.mul {f g : ℝ → ℝ} (hf : GrowsPolynomially f)
    (hg : GrowsPolynomially g) : GrowsPolynomially fun x => f x * g x := by
  suffices GrowsPolynomially fun x => |f x| * |g x| by
    cases eventually_atTop_nonneg_or_nonpos hf with
    | inl hf' =>
      cases eventually_atTop_nonneg_or_nonpos hg with
      | inl hg' =>
        have hmain : (fun x => f x * g x) =ᶠ[atTop] fun x => |f x| * |g x| := by
          filter_upwards [hf', hg'] with x hx₁ hx₂
          rw [abs_of_nonneg hx₁, abs_of_nonneg hx₂]
        rwa [iff_eventuallyEq hmain]
      | inr hg' =>
        have hmain : (fun x => f x * g x) =ᶠ[atTop] fun x => -|f x| * |g x| := by
          filter_upwards [hf', hg'] with x hx₁ hx₂
          simp [abs_of_nonneg hx₁, abs_of_nonpos hx₂]
        simp only [iff_eventuallyEq hmain, neg_mul]
        exact this.neg
    | inr hf' =>
      cases eventually_atTop_nonneg_or_nonpos hg with
      | inl hg' =>
        have hmain : (fun x => f x * g x) =ᶠ[atTop] fun x => -|f x| * |g x| := by
          filter_upwards [hf', hg'] with x hx₁ hx₂
          rw [abs_of_nonpos hx₁, abs_of_nonneg hx₂, neg_neg]
        simp only [iff_eventuallyEq hmain, neg_mul]
        exact this.neg
      | inr hg' =>
        have hmain : (fun x => f x * g x) =ᶠ[atTop] fun x => |f x| * |g x| := by
          filter_upwards [hf', hg'] with x hx₁ hx₂
          simp [abs_of_nonpos hx₁, abs_of_nonpos hx₂]
        simp only [iff_eventuallyEq hmain]
        exact this
  rw [GrowsPolynomially.ambient_iff]
  intro b hb
  have hf := (GrowsPolynomially.ambient_iff.mp hf.abs) b hb
  have hg := (GrowsPolynomially.ambient_iff.mp hg.abs) b hb
  obtain ⟨c₁, hc₁_mem, c₂, hc₂_mem, hf⟩ := hf
  obtain ⟨c₃, hc₃_mem, c₄, hc₄_mem, hg⟩ := hg
  refine ⟨c₁ * c₃, by change 0 < c₁ * c₃; positivity, ?_⟩
  refine ⟨c₂ * c₄, by change 0 < c₂ * c₄; positivity, ?_⟩
  filter_upwards [hf, hg] with x hf hg
  intro u hu
  refine ⟨?lb, ?ub⟩
  case lb => calc
    c₁ * c₃ * (|f x| * |g x|) = (c₁ * |f x|) * (c₃ * |g x|) := by ring
    _ ≤ |f u| * |g u| := by
           gcongr
           · exact (hf u hu).1
           · exact (hg u hu).1
  case ub => calc
    |f u| * |g u| ≤ (c₂ * |f x|) * (c₄ * |g x|) := by
           gcongr
           · exact (hf u hu).2
           · exact (hg u hu).2
    _ = c₂ * c₄ * (|f x| * |g x|) := by ring

lemma GrowsPolynomially.const_mul {f : ℝ → ℝ} {c : ℝ} (hf : GrowsPolynomially f) :
    GrowsPolynomially fun x => c * f x :=
  GrowsPolynomially.mul growsPolynomially_const hf

protected lemma GrowsPolynomially.add {f g : ℝ → ℝ} (hf : GrowsPolynomially f)
    (hg : GrowsPolynomially g) (hf' : 0 ≤ᶠ[atTop] f) (hg' : 0 ≤ᶠ[atTop] g) :
    GrowsPolynomially fun x => f x + g x := by
  rw [GrowsPolynomially.ambient_iff]
  intro b hb
  have hf := (GrowsPolynomially.ambient_iff.mp hf) b hb
  have hg := (GrowsPolynomially.ambient_iff.mp hg) b hb
  obtain ⟨c₁, hc₁_mem, c₂, hc₂_mem, hf⟩ := hf
  obtain ⟨c₃, hc₃_mem, c₄, _, hg⟩ := hg
  refine ⟨min c₁ c₃, by change 0 < min c₁ c₃; positivity, ?_⟩
  refine ⟨max c₂ c₄, by change 0 < max c₂ c₄; positivity, ?_⟩
  filter_upwards [hf, hg,
                  (tendsto_id.const_mul_atTop hb.1).eventually_forall_ge_atTop hf',
                  (tendsto_id.const_mul_atTop hb.1).eventually_forall_ge_atTop hg',
                  eventually_ge_atTop 0] with x hf hg hf' hg' hx_pos
  intro u hu
  have hbx : b * x ≤ x := calc
    b * x ≤ 1 * x := by gcongr; exact le_of_lt hb.2
        _ = x := by ring
  have fx_nonneg : 0 ≤ f x := hf' x hbx
  have gx_nonneg : 0 ≤ g x := hg' x hbx
  refine ⟨?lb, ?ub⟩
  case lb => calc
    min c₁ c₃ * (f x + g x) = min c₁ c₃ * f x + min c₁ c₃ * g x := by simp only [mul_add]
      _ ≤ c₁ * f x + c₃ * g x := by
              gcongr
              · exact min_le_left _ _
              · exact min_le_right _ _
      _ ≤ f u + g u := by
              gcongr
              · exact (hf u hu).1
              · exact (hg u hu).1
  case ub => calc
    max c₂ c₄ * (f x + g x) = max c₂ c₄ * f x + max c₂ c₄ * g x := by simp only [mul_add]
      _ ≥ c₂ * f x + c₄ * g x := by gcongr
                                    · exact le_max_left _ _
                                    · exact le_max_right _ _
      _ ≥ f u + g u := by gcongr
                          · exact (hf u hu).2
                          · exact (hg u hu).2

lemma GrowsPolynomially.of_isTheta_on {D : Type*} {coord : D → ℝ} {f g : D → ℝ}
    (hg : GrowsPolynomially g coord) (hf : f =Θ[comap coord atTop] g)
    (hf' : ∀ᶠ x in comap coord atTop, 0 ≤ f x) : GrowsPolynomially f coord := by
  intro b hb
  have below {P : D → Prop} (h : ∀ᶠ x in comap coord atTop, P x) :
      ∀ᶠ x in comap coord atTop, ∀ u, b * coord x ≤ coord u → P u := by
    rw [eventually_comap] at h
    filter_upwards [tendsto_comap.eventually
      ((tendsto_id.const_mul_atTop hb.1).eventually_forall_ge_atTop h)] with x hx u hu
    exact hx _ hu u rfl
  have hf_lb := isBigO_iff''.mp hf.isBigO_symm
  have hf_ub := isBigO_iff'.mp hf.isBigO
  obtain ⟨c₁, hc₁_pos : 0 < c₁, hf_lb⟩ := hf_lb
  obtain ⟨c₂, hc₂_pos : 0 < c₂, hf_ub⟩ := hf_ub
  have hg := hg.norm b hb
  obtain ⟨c₃, hc₃_pos : 0 < c₃, hg⟩ := hg
  obtain ⟨c₄, hc₄_pos : 0 < c₄, hg⟩ := hg
  have h_lb_pos : 0 < c₁ * c₂⁻¹ * c₃ := by positivity
  have h_ub_pos : 0 < c₂ * c₄ * c₁⁻¹ := by positivity
  refine ⟨c₁ * c₂⁻¹ * c₃, h_lb_pos, ?_⟩
  refine ⟨c₂ * c₄ * c₁⁻¹, h_ub_pos, ?_⟩
  have c₂_cancel : c₂⁻¹ * c₂ = 1 := inv_mul_cancel₀
  have c₁_cancel : c₁⁻¹ * c₁ = 1 := inv_mul_cancel₀
  filter_upwards [below hf', below hf_lb, below hf_ub, hg,
    tendsto_comap.eventually (eventually_ge_atTop (0 : ℝ))] with x hf_pos h_lb h_ub hg_bound hx_pos
  intro u hu
  have hbx : b * coord x ≤ coord x := mul_le_of_le_one_left hx_pos hb.2.le
  refine ⟨?lb, ?ub⟩
  case lb => calc
    c₁ * c₂⁻¹ * c₃ * f x ≤ c₁ * c₂⁻¹ * c₃ * (c₂ * ‖g x‖) := by
          rw [← Real.norm_of_nonneg (hf_pos x hbx)]; gcongr; exact h_ub x hbx
      _ = (c₂⁻¹ * c₂) * c₁ * (c₃ * ‖g x‖) := by ring
      _ = c₁ * (c₃ * ‖g x‖) := by simp [c₂_cancel]
      _ ≤ c₁ * ‖g u‖ := by gcongr; exact (hg_bound u hu).1
      _ ≤ f u := by
          rw [← Real.norm_of_nonneg (hf_pos u hu.1)]
          exact h_lb u hu.1
  case ub => calc
    f u ≤ c₂ * ‖g u‖ := by rw [← Real.norm_of_nonneg (hf_pos u hu.1)]; exact h_ub u hu.1
      _ ≤ c₂ * (c₄ * ‖g x‖) := by gcongr; exact (hg_bound u hu).2
      _ = c₂ * c₄ * (c₁⁻¹ * c₁) * ‖g x‖ := by simp [c₁_cancel]; ring
      _ = c₂ * c₄ * c₁⁻¹ * (c₁ * ‖g x‖) := by ring
      _ ≤ c₂ * c₄ * c₁⁻¹ * f x := by
                gcongr
                rw [← Real.norm_of_nonneg (hf_pos x hbx)]
                exact h_lb x hbx

lemma GrowsPolynomially.of_isTheta {f g : ℝ → ℝ} (hg : GrowsPolynomially g) (hf : f =Θ[atTop] g)
    (hf' : ∀ᶠ x in atTop, 0 ≤ f x) : GrowsPolynomially f :=
  hg.of_isTheta_on (by rwa [comap_id]) (by rwa [comap_id])

private lemma growsPolynomially_add_of_isLittleO_of_nonneg {f g : ℝ → ℝ} (hf : GrowsPolynomially f)
    (hfg : g =o[atTop] f) (hs : ∀ᶠ x in atTop, 0 ≤ f x) :
    GrowsPolynomially (f + g) := by
  have he : (f + g) ~[atTop] f := by
    change (f + g - f) =o[atTop] f
    simpa using hfg
  apply GrowsPolynomially.of_isTheta hf he.isTheta
  have H := (isLittleO_iff.mp hfg) (c := 1) zero_lt_one
  filter_upwards [hs, H] with x hx h
  change 0 ≤ f x + g x
  have hg : |g x| ≤ f x := by
    simpa only [one_mul, Real.norm_of_nonneg hx, Real.norm_eq_abs] using h
  linarith only [hg, neg_abs_le (g x)]

lemma GrowsPolynomially.add_isLittleO {f g : ℝ → ℝ} (hf : GrowsPolynomially f)
    (hfg : g =o[atTop] f) : GrowsPolynomially fun x => f x + g x := by
  change GrowsPolynomially (f + g)
  rcases hf.eventually_atTop_nonneg_or_nonpos with hs | hs
  · exact growsPolynomially_add_of_isLittleO_of_nonneg hf hfg hs
  · have hs' : ∀ᶠ x in atTop, 0 ≤ (-f) x :=
      hs.mono fun _ hx => neg_nonneg.mpr hx
    have H := growsPolynomially_add_of_isLittleO_of_nonneg hf.neg hfg.neg_left.neg_right hs'
    have e : f + g = -((-f) + (-g)) := by abel
    rw [e]
    exact H.neg

private lemma growsPolynomially_of_abs_on {D : Set ℝ} {F : D → ℝ}
    (hs : (∀ᶠ x in atTop, ∀ h : x ∈ D, 0 ≤ F ⟨x, h⟩) ∨
          (∀ᶠ x in atTop, ∀ h : x ∈ D, F ⟨x, h⟩ ≤ 0))
    (H : GrowsPolynomially (fun x ↦ |F x|) Subtype.val) : GrowsPolynomially F Subtype.val := by
  intro b hb
  obtain ⟨a, ha, d, hd, H⟩ := H b hb
  rcases hs with hs | hs
  · refine ⟨a, ha, d, hd, ?_⟩
    filter_upwards [H, tendsto_comap.eventually hs, tendsto_comap.eventually
      ((tendsto_id.const_mul_atTop hb.1).eventually_forall_ge_atTop hs)] with x H hx hu
    intro u hI
    simpa only [abs_of_nonneg (hx x.property),
      abs_of_nonneg (hu u.val hI.1 u.property)] using H u hI
  · refine ⟨d, hd, a, ha, ?_⟩
    filter_upwards [H, tendsto_comap.eventually hs, tendsto_comap.eventually
      ((tendsto_id.const_mul_atTop hb.1).eventually_forall_ge_atTop hs)] with x H hx hu
    intro u hI
    have h := H u hI
    simp only [Set.mem_Icc, abs_of_nonpos (hx x.property),
      abs_of_nonpos (hu u.val hI.1 u.property), mul_neg, neg_le_neg_iff] at h
    exact ⟨h.2, h.1⟩

protected lemma GrowsPolynomially.div {f g : ℝ → ℝ}
    (hf : GrowsPolynomially f) (hg : GrowsPolynomially g) :
    GrowsPolynomially (fun x : {x // g x ≠ 0} ↦ Checked.div (f x.val) (g x.val) x.2.isUnit)
      Subtype.val := by
  apply growsPolynomially_of_abs_on
  · rcases hf.eventually_atTop_nonneg_or_nonpos with h | h <;>
      rcases hg.eventually_atTop_nonneg_or_nonpos with k | k
    · left
      filter_upwards [h, k] with x hx kx
      exact fun _ => div_nonneg hx kx
    · right
      filter_upwards [h, k] with x hx kx
      exact fun _ => div_nonpos_of_nonneg_of_nonpos hx kx
    · right
      filter_upwards [h, k] with x hx kx
      exact fun _ => div_nonpos_of_nonpos_of_nonneg hx kx
    · left
      filter_upwards [h, k] with x hx kx
      exact fun _ => div_nonneg_of_nonpos hx kx
  · intro t ht
    obtain ⟨a, ha, b, hb, H⟩ := (GrowsPolynomially.ambient_iff.mp hf.abs) t ht
    obtain ⟨c, hc, d, hd, K⟩ := (GrowsPolynomially.ambient_iff.mp hg.abs) t ht
    refine ⟨a / d, div_pos ha hd, b / c, div_pos hb hc, ?_⟩
    filter_upwards [tendsto_comap.eventually H,
      tendsto_comap.eventually K] with x H K
    intro u hu
    have hx₀ : g x.val ≠ 0 := x.property
    have hu₀ : g u.val ≠ 0 := u.property
    have vx := abs_pos.mpr hx₀
    have vu := abs_pos.mpr hu₀
    have h := H u.val hu
    have k := K u.val hu
    constructor
    · simp only [abs_div, div_mul_div_comm₀]
      exact (div_le_div_iff₀ (mul_pos hd vx) vu).2
        (mul_le_mul h.1 k.2 vu.le (abs_nonneg _))
    · simp only [abs_div, div_mul_div_comm₀]
      exact (div_le_div_iff₀ vu (mul_pos hc vx)).2
        (mul_le_mul h.2 k.1 (mul_nonneg hc.le vx.le) (mul_nonneg hb.le (abs_nonneg _)))

protected lemma GrowsPolynomially.inv {f : ℝ → ℝ} (hf : GrowsPolynomially f) :
    GrowsPolynomially (fun x : {x // f x ≠ 0} ↦ Checked.inv (f x.val) x.2.isUnit) Subtype.val := by
  simpa only [one_div₀] using (growsPolynomially_const (c := (1 : ℝ))).div hf

protected lemma GrowsPolynomially.rpow (p : ℝ) (hf : GrowsPolynomially f)
    (hf_nonneg : ∀ᶠ x in atTop, 0 ≤ f x) : GrowsPolynomially fun x => (f x) ^ p := by
  rw [GrowsPolynomially.ambient_iff]
  intro b hb
  obtain ⟨c₁, (hc₁_mem : 0 < c₁), c₂, hc₂_mem, hfnew⟩ := (GrowsPolynomially.ambient_iff.mp hf) b hb
  have hc₁p : 0 < c₁ ^ p := Real.rpow_pos_of_pos hc₁_mem _
  have hc₂p : 0 < c₂ ^ p := Real.rpow_pos_of_pos hc₂_mem _
  cases le_or_gt 0 p with
  | inl => -- 0 ≤ p
    refine ⟨c₁^p, hc₁p, ?_⟩
    refine ⟨c₂^p, hc₂p, ?_⟩
    filter_upwards [eventually_gt_atTop 0, hfnew, hf_nonneg,
        (tendsto_id.const_mul_atTop hb.1).eventually_forall_ge_atTop hf_nonneg]
        with x _ hf₁ hf_nonneg hf_nonneg₂
    intro u hu
    have fu_nonneg : 0 ≤ f u := hf_nonneg₂ u hu.1
    refine ⟨?lb, ?ub⟩
    case lb => calc
      c₁ ^ p * (f x) ^ p = (c₁ * f x) ^ p := by rw [mul_rpow (le_of_lt hc₁_mem) hf_nonneg]
        _ ≤ _ := by gcongr; exact (hf₁ u hu).1
    case ub => calc
      (f u) ^ p ≤ (c₂ * f x) ^ p := by gcongr; exact (hf₁ u hu).2
        _ = _ := by rw [← mul_rpow (le_of_lt hc₂_mem) hf_nonneg]
  | inr hp => -- p < 0
    match hf.eventually_atTop_zero_or_pos_or_neg with
    | .inl hzero => -- eventually zero
      refine ⟨1, by norm_num, 1, by norm_num, ?_⟩
      filter_upwards [hzero, hfnew] with x hx hx'
      intro u hu
      simp only [hx, zero_rpow (ne_of_lt hp), mul_zero,
        Set.Icc_self, Set.mem_singleton_iff]
      simp only [hx, mul_zero, Set.Icc_self, Set.mem_singleton_iff] at hx'
      rw [hx' u hu, zero_rpow (ne_of_lt hp)]
    | .inr (.inl hpos) => -- eventually positive
      refine ⟨c₂^p, hc₂p, ?_⟩
      refine ⟨c₁^p, hc₁p, ?_⟩
      filter_upwards [eventually_gt_atTop 0, hfnew, hpos,
          (tendsto_id.const_mul_atTop hb.1).eventually_forall_ge_atTop hpos]
          with x _ hf₁ hf_pos hf_pos₂
      intro u hu
      refine ⟨?lb, ?ub⟩
      case lb => calc
        c₂ ^ p * (f x) ^ p = (c₂ * f x) ^ p := by rw [mul_rpow (le_of_lt hc₂_mem) (le_of_lt hf_pos)]
          _ ≤ _ := rpow_le_rpow_of_nonpos (hf_pos₂ u hu.1) (hf₁ u hu).2 (le_of_lt hp)
      case ub => calc
        (f u) ^ p ≤ (c₁ * f x) ^ p := by
              exact rpow_le_rpow_of_nonpos (by positivity) (hf₁ u hu).1 (le_of_lt hp)
          _ = _ := by rw [← mul_rpow (le_of_lt hc₁_mem) (le_of_lt hf_pos)]
    | .inr (.inr hneg) => -- eventually negative (which is impossible)
      have : ∀ᶠ (_ : ℝ) in atTop, False := by
        filter_upwards [hf_nonneg, hneg] with x hx hx'; linarith
      rw [Filter.eventually_false_iff_eq_bot] at this
      exact False.elim <| atTop_neBot.ne this

protected lemma GrowsPolynomially.pow (p : ℕ) (hf : GrowsPolynomially f)
    (hf_nonneg : ∀ᶠ x in atTop, 0 ≤ f x) : GrowsPolynomially fun x => (f x) ^ p := by
  simp_rw [← rpow_natCast]
  exact hf.rpow p hf_nonneg

protected lemma GrowsPolynomially.zpow (p : ℤ) (hf : GrowsPolynomially f)
    (hf_nonneg : ∀ᶠ x in atTop, 0 ≤ f x) :
    GrowsPolynomially (fun x : {x // p < 0 → IsUnit (f x)} ↦ Checked.zpow (f x.val) p x.2)
      Subtype.val := by
  have h (x : {x // p < 0 → IsUnit (f x)}) :
      (f x.val) ^ (p : ℝ) = Checked.zpow (f x.val) p x.2 :=
    Real.rpow_intCast _ _ (h := fun hp ↦ (x.2 hp).ne_zero)
  simpa only [Function.comp_def, id_eq, h] using
    (hf.rpow (p : ℝ) hf_nonneg).comp_domain (Subtype.val : {x // p < 0 → IsUnit (f x)} → ℝ)

lemma growsPolynomially_rpow (p : ℝ) : GrowsPolynomially fun x => x ^ p :=
  growsPolynomially_id.rpow p (eventually_ge_atTop 0)

lemma growsPolynomially_pow (p : ℕ) : GrowsPolynomially fun x => x ^ p :=
  growsPolynomially_id.pow p (eventually_ge_atTop 0)

lemma growsPolynomially_zpow (p : ℤ) :
    GrowsPolynomially (fun x : {x : ℝ // p < 0 → IsUnit x} ↦ Checked.zpow x.val p x.2)
      Subtype.val :=
  growsPolynomially_id.zpow p (eventually_ge_atTop 0)

lemma growsPolynomially_log : GrowsPolynomially Real.log := by
  rw [GrowsPolynomially.ambient_iff]
  intro b hb
  have hb₀ : 0 < b := hb.1
  refine ⟨1 / 2, by norm_num, ?_⟩
  refine ⟨1, by norm_num, ?_⟩
  have h_tendsto : Tendsto (fun x => 1 / 2 * Real.log x) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num) Real.tendsto_log_atTop
  filter_upwards [eventually_gt_atTop 1,
                  (tendsto_id.const_mul_atTop hb.1).eventually_forall_ge_atTop
                    <| h_tendsto.eventually (eventually_gt_atTop (-Real.log b))] with x hx_pos hx
  intro u hu
  refine ⟨?lb, ?ub⟩
  case lb => calc
    1 / 2 * Real.log x = Real.log x + (-1 / 2) * Real.log x := by ring
      _ ≤ Real.log x + Real.log b := by
        have hbx : b * x ≤ x := mul_le_of_le_one_left (zero_le_one.trans hx_pos.le) (le_of_lt hb.2)
        linarith [hx x hbx]
      _ = Real.log (b * x) := by rw [← Real.log_mul (by positivity) (by positivity), mul_comm]
      _ ≤ Real.log u := by gcongr; exact hu.1
  case ub =>
    rw [one_mul]
    gcongr
    · calc 0 < b * x := by positivity
         _ ≤ u := by exact hu.1
    · exact hu.2

lemma GrowsPolynomially.of_isEquivalent {f g : ℝ → ℝ} (hg : GrowsPolynomially g)
    (hf : f ~[atTop] g) : GrowsPolynomially f := by
  have : f = g + (f - g) := by ext; simp
  rw [this]
  exact add_isLittleO hg hf

lemma GrowsPolynomially.of_isEquivalent_const {f : ℝ → ℝ} {c : ℝ} (hf : f ~[atTop] fun _ => c) :
    GrowsPolynomially f :=
  of_isEquivalent growsPolynomially_const hf

end AkraBazziRecurrence
