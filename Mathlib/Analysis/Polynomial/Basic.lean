/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Devon Tuma
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Limits related to polynomial and rational functions

This file proves basic facts about limits of polynomial and rational functions.
The main result is `Polynomial.isEquivalent_atTop_lead`, which states that for
any polynomial `P` of degree `n` with leading coefficient `a`, the corresponding
polynomial function is equivalent to `a * x^n` as `x` goes to +∞.

We can then use this result to prove various limits for polynomial and rational
functions, depending on the degrees and leading coefficients of the considered
polynomials.
-/

public section


open Filter Finset Asymptotics

open Asymptotics Polynomial

open scoped Topology

namespace Polynomial

variable {𝕜 : Type*} [NormedField 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] (P Q : 𝕜[X])

theorem eventually_atTop_not_isRoot (hP : P ≠ 0) : ∀ᶠ x in atTop, ¬P.IsRoot x :=
  atTop_le_cofinite <| (finite_setOfPred_isRoot hP).compl_mem_cofinite

theorem eventually_atBot_not_isRoot (hP : P ≠ 0) : ∀ᶠ x in atBot, ¬P.IsRoot x :=
  atBot_le_cofinite <| (finite_setOfPred_isRoot hP).compl_mem_cofinite

variable [OrderTopology 𝕜]

section PolynomialAtTop

theorem isEquivalent_atTop_lead :
    (fun x => eval x P) ~[atTop] fun x => P.leadingCoeff * x ^ P.natDegree := by
  by_cases h : P = 0
  · simp [h, IsEquivalent.refl]
  · simp only [Polynomial.eval_eq_sum_range, sum_range_succ]
    exact
      IsLittleO.add_isEquivalent
        (IsLittleO.fun_sum fun i hi =>
          IsLittleO.const_mul_left
            ((IsLittleO.const_mul_right fun hz => h <| leadingCoeff_eq_zero.mp hz) <|
              isLittleO_pow_pow_atTop_of_lt (mem_range.mp hi))
            _)
        IsEquivalent.refl

theorem tendsto_atTop_of_leadingCoeff_nonneg (hdeg : 0 < P.degree) (hnng : 0 ≤ P.leadingCoeff) :
    Tendsto (fun x => eval x P) atTop atTop :=
  P.isEquivalent_atTop_lead.symm.tendsto_atTop <|
    tendsto_const_mul_pow_atTop (natDegree_pos_iff_degree_pos.2 hdeg).ne' <|
      hnng.lt_of_ne' <| leadingCoeff_ne_zero.mpr <| ne_zero_of_degree_gt hdeg

theorem tendsto_atTop_iff_leadingCoeff_nonneg :
    Tendsto (fun x => eval x P) atTop atTop ↔ 0 < P.degree ∧ 0 ≤ P.leadingCoeff := by
  refine ⟨fun h => ?_, fun h => tendsto_atTop_of_leadingCoeff_nonneg P h.1 h.2⟩
  have : Tendsto (fun x => P.leadingCoeff * x ^ P.natDegree) atTop atTop :=
    (isEquivalent_atTop_lead P).tendsto_atTop h
  rw [tendsto_const_mul_pow_atTop_iff, ← pos_iff_ne_zero, natDegree_pos_iff_degree_pos] at this
  exact ⟨this.1, this.2.le⟩

theorem tendsto_atBot_iff_leadingCoeff_nonpos :
    Tendsto (fun x => eval x P) atTop atBot ↔ 0 < P.degree ∧ P.leadingCoeff ≤ 0 := by
  simp only [← tendsto_neg_atTop_iff, ← eval_neg, tendsto_atTop_iff_leadingCoeff_nonneg,
    degree_neg, leadingCoeff_neg, neg_nonneg]

theorem tendsto_atBot_of_leadingCoeff_nonpos (hdeg : 0 < P.degree) (hnps : P.leadingCoeff ≤ 0) :
    Tendsto (fun x => eval x P) atTop atBot :=
  P.tendsto_atBot_iff_leadingCoeff_nonpos.2 ⟨hdeg, hnps⟩

theorem abs_tendsto_atTop (hdeg : 0 < P.degree) :
    Tendsto (fun x => abs <| eval x P) atTop atTop := by
  rcases le_total 0 P.leadingCoeff with hP | hP
  · exact tendsto_abs_atTop_atTop.comp (P.tendsto_atTop_of_leadingCoeff_nonneg hdeg hP)
  · exact tendsto_abs_atBot_atTop.comp (P.tendsto_atBot_of_leadingCoeff_nonpos hdeg hP)

theorem isBoundedUnder_abs_atTop_iff :
    (IsBoundedUnder (· ≤ ·) atTop fun x => |eval x P|) ↔ P.degree ≤ 0 := by
  refine ⟨fun h => ?_, fun h => ⟨|P.coeff 0|, eventually_map.mpr (Eventually.of_forall
    (forall_imp (fun _ => le_of_eq) fun x => congr_arg abs <| _root_.trans (congr_arg (eval x)
    (eq_C_of_degree_le_zero h)) eval_C))⟩⟩
  contrapose! h
  exact not_isBoundedUnder_of_tendsto_atTop (abs_tendsto_atTop P h)

theorem abs_tendsto_atTop_iff : Tendsto (fun x => abs <| eval x P) atTop atTop ↔ 0 < P.degree :=
  ⟨fun h ↦ not_le.mp (mt (isBoundedUnder_abs_atTop_iff P).mpr
    (not_isBoundedUnder_of_tendsto_atTop h)), abs_tendsto_atTop P⟩

theorem tendsto_nhds_iff {c : 𝕜} :
    Tendsto (fun x => eval x P) atTop (𝓝 c) ↔ P.leadingCoeff = c ∧ P.degree ≤ 0 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := P.isEquivalent_atTop_lead.tendsto_nhds h
    by_cases hP : P.leadingCoeff = 0
    · simp only [hP, zero_mul, tendsto_const_nhds_iff] at this
      exact ⟨_root_.trans hP this, by simp [leadingCoeff_eq_zero.1 hP]⟩
    · rw [tendsto_const_mul_pow_nhds_iff hP, natDegree_eq_zero_iff_degree_le_zero] at this
      exact this.symm
  · refine P.isEquivalent_atTop_lead.symm.tendsto_nhds ?_
    have : P.natDegree = 0 := natDegree_eq_zero_iff_degree_le_zero.2 h.2
    simp only [h.1, this, pow_zero, mul_one]
    exact tendsto_const_nhds

end PolynomialAtTop

section PolynomialAtBot

theorem isEquivalent_atBot_lead : P.eval ~[atBot] (P.leadingCoeff * · ^ P.natDegree) := by
  convert! (P.comp (-X)).isEquivalent_atTop_lead.comp_tendsto tendsto_neg_atBot_atTop using 2
  · simp
  · rw [Function.comp_apply, comp_neg_X_leadingCoeff_eq, ← mul_rotate]
    simp [natDegree_comp, ← mul_pow, mul_comm]

theorem abs_tendsto_atBot (hdeg : 0 < P.degree) : Tendsto (|P.eval ·|) atBot atTop := by
  convert! ((P.comp (-X)).abs_tendsto_atTop (by simp [hdeg])).comp tendsto_neg_atBot_atTop using 2
  simp

theorem isBoundedUnder_abs_atBot_iff :
    (IsBoundedUnder (· ≤ ·) atBot (|P.eval ·|)) ↔ P.degree ≤ 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨|P.coeff 0|, eventually_map.mpr (Eventually.of_forall
    (forall_imp (fun _ ↦ le_of_eq) fun x ↦ congr_arg abs <| _root_.trans (congr_arg (eval x)
    (eq_C_of_degree_le_zero h)) eval_C))⟩⟩
  contrapose! h
  exact not_isBoundedUnder_of_tendsto_atTop (abs_tendsto_atBot P h)

theorem abs_tendsto_atBot_iff : Tendsto (|P.eval ·|) atBot atTop ↔ 0 < P.degree :=
  ⟨fun h ↦ not_le.mp (mt (isBoundedUnder_abs_atBot_iff P).mpr
    (not_isBoundedUnder_of_tendsto_atTop h)), abs_tendsto_atBot P⟩

end PolynomialAtBot

section PolynomialDiv

omit [OrderTopology 𝕜] in
private theorem isEquivalent_div_lead {ι : Type*} {l : Filter ι} {u : ι → 𝕜}
    {hQ : IsUnit Q.leadingCoeff} (hu : ∀ᶠ x in l, IsUnit (u x))
    (hq : ∀ x, Q.eval (u x) ≠ 0)
    (hz : ∀ x, (P.natDegree : ℤ) - Q.natDegree < 0 → IsUnit (u x))
    (hp' : (fun x ↦ P.eval (u x)) ~[l] fun x ↦ P.leadingCoeff * u x ^ P.natDegree)
    (hq' : (fun x ↦ Q.eval (u x)) ~[l] fun x ↦ Q.leadingCoeff * u x ^ Q.natDegree) :
    (fun x ↦ Checked.div (P.eval (u x)) (Q.eval (u x)) (hq x).isUnit) ~[l]
      fun x ↦ P.leadingCoeff / Q.leadingCoeff *
        Checked.zpow (u x) ((P.natDegree : ℤ) - Q.natDegree) (hz x) := by
  let v := (Subtype.val : {x // IsUnit (u x)} → ι)
  have hr : Set.range v ∈ l := hu.mono fun x hx ↦ ⟨⟨x, hx⟩, rfl⟩
  rw [← map_comap_of_mem hr, isEquivalent_map]
  refine ((hp'.comp_tendsto (tendsto_comap (f := v))).div
    (hv := fun x ↦ (hq (v x)).isUnit) (hw := fun x ↦ hQ.mul (x.2.pow _))
    (hq'.comp_tendsto tendsto_comap)).trans ?_
  apply EventuallyEq.isEquivalent
  exact Eventually.of_forall fun x ↦ by
    simp [v, zpow_sub₀ x.2.ne_zero, div_mul_div_comm₀]

/-- At infinity the quotient is equivalent to the ratio of the leading monomials,
on the common domain of the quotient and the integer power. -/
theorem isEquivalent_atTop_div {hQ : IsUnit Q.leadingCoeff} :
    (fun x : {x : 𝕜 // Q.eval x ≠ 0 ∧ ((P.natDegree : ℤ) - Q.natDegree < 0 → IsUnit x)} ↦
      Checked.div (P.eval x.val) (Q.eval x.val) x.2.1.isUnit) ~[comap Subtype.val atTop]
      fun x ↦ P.leadingCoeff / Q.leadingCoeff *
        Checked.zpow (x : 𝕜) ((P.natDegree : ℤ) - Q.natDegree) x.2.2 :=
  isEquivalent_div_lead P Q (tendsto_comap.eventually ((eventually_gt_atTop 0).mono
    fun _ hx ↦ hx.ne'.isUnit)) (fun x ↦ x.2.1) (fun x ↦ x.2.2)
    (P.isEquivalent_atTop_lead.comp_tendsto tendsto_comap)
    (Q.isEquivalent_atTop_lead.comp_tendsto tendsto_comap)

theorem isEquivalent_atBot_div {hQ : IsUnit Q.leadingCoeff} :
    (fun x : {x : 𝕜 // Q.eval x ≠ 0 ∧ ((P.natDegree : ℤ) - Q.natDegree < 0 → IsUnit x)} ↦
      Checked.div (P.eval x.val) (Q.eval x.val) x.2.1.isUnit) ~[comap Subtype.val atBot]
      fun x ↦ P.leadingCoeff / Q.leadingCoeff *
        Checked.zpow (x : 𝕜) ((P.natDegree : ℤ) - Q.natDegree) x.2.2 :=
  isEquivalent_div_lead P Q (tendsto_comap.eventually ((eventually_lt_atBot 0).mono
    fun _ hx ↦ hx.ne.isUnit)) (fun x ↦ x.2.1) (fun x ↦ x.2.2)
    (P.isEquivalent_atBot_lead.comp_tendsto tendsto_comap)
    (Q.isEquivalent_atBot_lead.comp_tendsto tendsto_comap)

private theorem map_comap_subtype_of_eventually {α : Type*} {l : Filter α} {p r : α → Prop}
    (h : ∀ x, r x → p x) (hr : ∀ᶠ x in l, r x) :
    Filter.map (fun x : Subtype r ↦ (⟨x, h x x.2⟩ : Subtype p)) (comap Subtype.val l) =
      comap Subtype.val l := by
  let i := fun x : Subtype r ↦ (⟨x, h x x.2⟩ : Subtype p)
  change Filter.map i _ = _
  have heq : comap (Subtype.val : Subtype r → α) l = comap i (comap Subtype.val l) :=
    (comap_comap (m := i) (n := Subtype.val)).symm
  rw [heq]
  apply map_comap_of_mem
  filter_upwards [tendsto_comap.eventually hr] with x hx
  exact ⟨⟨x, hx⟩, Subtype.ext rfl⟩

private theorem div_tendsto_atTop_iff_lead {hQ : IsUnit Q.leadingCoeff} {L : Filter 𝕜}
    (hL : ∀ {f g : {x // Q.eval x ≠ 0 ∧ IsUnit x} → 𝕜},
      f ~[comap Subtype.val atTop] g →
      (Tendsto f (comap Subtype.val atTop) L ↔ Tendsto g (comap Subtype.val atTop) L)) :
    Tendsto (fun x : {x // Q.eval x ≠ 0} ↦ Checked.div (P.eval x.val) (Q.eval x.val) x.2.isUnit)
      (comap Subtype.val atTop) L ↔
    Tendsto (fun x : {x : 𝕜 // IsUnit x} ↦ P.leadingCoeff / Q.leadingCoeff *
      Checked.zpow (x : 𝕜) ((P.natDegree : ℤ) - Q.natDegree) fun _ ↦ x.2)
      (comap Subtype.val atTop) L := by
  have hr : ∀ᶠ x in atTop, Q.eval x ≠ 0 ∧ IsUnit x :=
    (Q.eventually_atTop_not_isRoot (leadingCoeff_ne_zero.mp hQ.ne_zero)).and
      ((eventually_gt_atTop 0).mono fun _ hx ↦ hx.ne'.isUnit)
  rw [← map_comap_subtype_of_eventually (fun _ h ↦ h.1) hr,
    ← map_comap_subtype_of_eventually (fun _ h ↦ h.2) hr, tendsto_map'_iff, tendsto_map'_iff]
  apply hL
  exact isEquivalent_div_lead P Q (Eventually.of_forall fun x ↦ x.2.2)
    (fun x ↦ x.2.1) (fun x _ ↦ x.2.2) (P.isEquivalent_atTop_lead.comp_tendsto tendsto_comap)
    (Q.isEquivalent_atTop_lead.comp_tendsto tendsto_comap)

theorem div_tendsto_atTop_zero_of_degree_lt (hdeg : P.degree < Q.degree) :
    Tendsto (fun x : {x // Q.eval x ≠ 0} ↦ Checked.div (P.eval x.val) (Q.eval x.val) x.2.isUnit)
      (comap Subtype.val atTop) (𝓝 0) := by
  by_cases hP : P = 0
  · subst P
    simpa using (tendsto_const_nhds (x := (0 : 𝕜)))
  have hQ := (leadingCoeff_ne_zero.mpr (ne_zero_of_degree_gt hdeg)).isUnit
  apply (div_tendsto_atTop_iff_lead P Q (hQ := hQ) fun h ↦ h.tendsto_nhds_iff).2
  exact tendsto_const_mul_zpow_atTop_zero (by have := natDegree_lt_natDegree hP hdeg; omega)

theorem div_tendsto_atTop_zero_iff_degree_lt (hQ : Q ≠ 0) :
    Tendsto (fun x : {x // Q.eval x ≠ 0} ↦ Checked.div (P.eval x.val) (Q.eval x.val) x.2.isUnit)
      (comap Subtype.val atTop) (𝓝 0) ↔ P.degree < Q.degree := by
  refine ⟨fun h ↦ ?_, div_tendsto_atTop_zero_of_degree_lt P Q⟩
  by_cases hP : P = 0
  · simpa [hP] using (bot_lt_iff_ne_bot.mpr (degree_ne_bot.mpr hQ))
  have hu := (leadingCoeff_ne_zero.mpr hQ).isUnit
  have hc : P.leadingCoeff / Q.leadingCoeff ≠ 0 := div_ne_zero (leadingCoeff_ne_zero.mpr hP)
  have hlim := (div_tendsto_atTop_iff_lead P Q (hQ := hu) fun e ↦ e.tendsto_nhds_iff).1 h
  rcases (tendsto_const_mul_zpow_atTop_nhds_iff hc).1 hlim with h | h
  · exact (hc h.2).elim
  · exact degree_lt_degree (by omega)

theorem div_tendsto_atTop_leadingCoeff_div_of_degree_eq (hdeg : P.degree = Q.degree)
    {hQ : IsUnit Q.leadingCoeff} :
    Tendsto (fun x : {x // Q.eval x ≠ 0} ↦ Checked.div (P.eval x.val) (Q.eval x.val) x.2.isUnit)
      (comap Subtype.val atTop) (𝓝 (P.leadingCoeff / Q.leadingCoeff)) := by
  apply (div_tendsto_atTop_iff_lead P Q (hQ := hQ) fun h ↦ h.tendsto_nhds_iff).2
  simpa [natDegree_eq_natDegree hdeg] using
    (tendsto_const_nhds (x := P.leadingCoeff / Q.leadingCoeff))

theorem div_tendsto_atTop_of_degree_gt' (hdeg : Q.degree < P.degree)
    {hQ : IsUnit Q.leadingCoeff} (hpos : 0 < P.leadingCoeff / Q.leadingCoeff) :
    Tendsto (fun x : {x // Q.eval x ≠ 0} ↦ Checked.div (P.eval x.val) (Q.eval x.val) x.2.isUnit)
      (comap Subtype.val atTop) atTop := by
  have hd := natDegree_lt_natDegree (leadingCoeff_ne_zero.mp hQ.ne_zero) hdeg
  apply (div_tendsto_atTop_iff_lead P Q (hQ := hQ) fun h ↦ h.tendsto_atTop_iff).2
  exact ((tendsto_zpow_atTop_atTop (by omega : 0 < (P.natDegree : ℤ) - Q.natDegree)).comp
    tendsto_comap).const_mul_atTop hpos

theorem div_tendsto_atTop_of_degree_gt (hdeg : Q.degree < P.degree) {hQ : IsUnit Q.leadingCoeff}
    (hnng : 0 ≤ P.leadingCoeff / Q.leadingCoeff) :
    Tendsto (fun x : {x // Q.eval x ≠ 0} ↦ Checked.div (P.eval x.val) (Q.eval x.val) x.2.isUnit)
      (comap Subtype.val atTop) atTop :=
  div_tendsto_atTop_of_degree_gt' P Q hdeg (hnng.lt_of_ne' (div_ne_zero
    (leadingCoeff_ne_zero.mpr (ne_zero_of_degree_gt hdeg))))

theorem div_tendsto_atBot_of_degree_gt' (hdeg : Q.degree < P.degree)
    {hQ : IsUnit Q.leadingCoeff} (hneg : P.leadingCoeff / Q.leadingCoeff < 0) :
    Tendsto (fun x : {x // Q.eval x ≠ 0} ↦ Checked.div (P.eval x.val) (Q.eval x.val) x.2.isUnit)
      (comap Subtype.val atTop) atBot := by
  have hd := natDegree_lt_natDegree (leadingCoeff_ne_zero.mp hQ.ne_zero) hdeg
  apply (div_tendsto_atTop_iff_lead P Q (hQ := hQ) fun h ↦ h.tendsto_atBot_iff).2
  exact ((tendsto_zpow_atTop_atTop (by omega : 0 < (P.natDegree : ℤ) - Q.natDegree)).comp
    tendsto_comap).const_mul_atTop_of_neg hneg

theorem div_tendsto_atBot_of_degree_gt (hdeg : Q.degree < P.degree) {hQ : IsUnit Q.leadingCoeff}
    (hnps : P.leadingCoeff / Q.leadingCoeff ≤ 0) :
    Tendsto (fun x : {x // Q.eval x ≠ 0} ↦ Checked.div (P.eval x.val) (Q.eval x.val) x.2.isUnit)
      (comap Subtype.val atTop) atBot :=
  div_tendsto_atBot_of_degree_gt' P Q hdeg (hnps.lt_of_ne (div_ne_zero
    (leadingCoeff_ne_zero.mpr (ne_zero_of_degree_gt hdeg))))

theorem abs_div_tendsto_atTop_atTop_of_degree_gt (hdeg : Q.degree < P.degree) (hQ : Q ≠ 0) :
    Tendsto (fun x : {x // Q.eval x ≠ 0} ↦ |Checked.div (P.eval x.val) (Q.eval x.val) x.2.isUnit|)
      (comap Subtype.val atTop) atTop := by
  have hu := (leadingCoeff_ne_zero.mpr hQ).isUnit
  rcases le_total 0 (P.leadingCoeff / Q.leadingCoeff) with h | h
  · exact tendsto_abs_atTop_atTop.comp (P.div_tendsto_atTop_of_degree_gt Q hdeg h)
  · exact tendsto_abs_atBot_atTop.comp (P.div_tendsto_atBot_of_degree_gt Q hdeg h)

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [OrderTopology 𝕜] in
private theorem tendsto_div_comp_neg_X {l l' L : Filter 𝕜} {f : 𝕜 → 𝕜}
    (hn : Tendsto (fun x : 𝕜 ↦ -x) l l')
    (h : Tendsto (fun x : {x // (Q.comp (-X)).eval x ≠ 0} ↦
      f (Checked.div ((P.comp (-X)).eval x.val) ((Q.comp (-X)).eval x.val) x.2.isUnit))
      (comap Subtype.val l') L) :
    Tendsto (fun x : {x // Q.eval x ≠ 0} ↦ f (Checked.div (P.eval x.val) (Q.eval x.val) x.2.isUnit))
      (comap Subtype.val l) L := by
  let i := fun x : {x // Q.eval x ≠ 0} ↦
    (⟨-(x : 𝕜), by simpa using x.2⟩ : {x // (Q.comp (-X)).eval x ≠ 0})
  have hi : Tendsto i (comap Subtype.val l) (comap Subtype.val l') :=
    tendsto_comap_iff.mpr (hn.comp tendsto_comap)
  simpa [i, Function.comp_def] using h.comp hi

theorem div_tendsto_atBot_zero_of_degree_lt (hdeg : P.degree < Q.degree) :
    Tendsto (fun x : {x // Q.eval x ≠ 0} ↦ Checked.div (P.eval x.val) (Q.eval x.val) x.2.isUnit)
      (comap Subtype.val atBot) (𝓝 0) := by
  apply tendsto_div_comp_neg_X P Q (f := id) tendsto_neg_atBot_atTop
  exact div_tendsto_atTop_zero_of_degree_lt _ _ (by simpa using hdeg)

theorem div_tendsto_atBot_zero_iff_degree_lt (hQ : Q ≠ 0) :
    Tendsto (fun x : {x // Q.eval x ≠ 0} ↦ Checked.div (P.eval x.val) (Q.eval x.val) x.2.isUnit)
      (comap Subtype.val atBot) (𝓝 0) ↔ P.degree < Q.degree := by
  refine ⟨fun h ↦ ?_, div_tendsto_atBot_zero_of_degree_lt P Q⟩
  rw [← P.degree_comp_neg_X, ← Q.degree_comp_neg_X]
  apply (div_tendsto_atTop_zero_iff_degree_lt _ _ (by simp [comp_eq_zero_iff, hQ])).1
  apply tendsto_div_comp_neg_X _ _ (f := id) tendsto_neg_atTop_atBot
  let T (p q : 𝕜[X]) := Tendsto
    (fun x : {x // q.eval x ≠ 0} ↦ Checked.div (p.eval x.val) (q.eval x.val) x.2.isUnit)
    (comap Subtype.val atBot) (𝓝 0)
  change T ((P.comp (-X)).comp (-X)) ((Q.comp (-X)).comp (-X))
  simpa only [comp_neg_X_comp_neg_X] using (show T P Q from h)

theorem div_tendsto_atBot_leadingCoeff_div_of_degree_eq (hdeg : P.degree = Q.degree)
    {hQ : IsUnit Q.leadingCoeff} :
    Tendsto (fun x : {x // Q.eval x ≠ 0} ↦ Checked.div (P.eval x.val) (Q.eval x.val) x.2.isUnit)
      (comap Subtype.val atBot) (𝓝 (P.leadingCoeff / Q.leadingCoeff)) := by
  refine (isEquivalent_div_lead P Q (hQ := hQ)
    (tendsto_comap.eventually ((eventually_lt_atBot 0).mono fun _ hx ↦ hx.ne.isUnit))
    (fun x ↦ x.2) (fun _ hz ↦ False.elim (by simp [natDegree_eq_natDegree hdeg] at hz))
    (P.isEquivalent_atBot_lead.comp_tendsto tendsto_comap)
    (Q.isEquivalent_atBot_lead.comp_tendsto tendsto_comap)).symm.tendsto_nhds ?_
  simpa [natDegree_eq_natDegree hdeg] using
    (tendsto_const_nhds (x := P.leadingCoeff / Q.leadingCoeff))

theorem abs_div_tendsto_atBot_atTop_of_degree_gt (hdeg : Q.degree < P.degree) (hQ : Q ≠ 0) :
    Tendsto (fun x : {x // Q.eval x ≠ 0} ↦ |Checked.div (P.eval x.val) (Q.eval x.val) x.2.isUnit|)
      (comap Subtype.val atBot) atTop := by
  apply tendsto_div_comp_neg_X P Q (f := abs) tendsto_neg_atBot_atTop
  exact abs_div_tendsto_atTop_atTop_of_degree_gt _ _ (by simpa using hdeg)
    (by simp [comp_eq_zero_iff, hQ])

end PolynomialDiv

theorem isLittleO_atTop_of_degree_lt (h : P.degree < Q.degree) : P.eval =o[atTop] Q.eval := by
  by_cases hp : P = 0
  · simp [hp]
  · have hq : Q ≠ 0 := ne_zero_of_degree_ge_degree h.le hp
    have hPQ : ∀ᶠ x in atTop, Q.eval x = 0 → P.eval x = 0 :=
      mem_of_superset (eventually_atTop_not_isRoot Q hq) fun x h h' ↦ absurd h' h
    exact isLittleO_of_tendsto' hPQ (div_tendsto_atTop_zero_of_degree_lt P Q h)

theorem isLittleO_atBot_of_degree_lt (h : P.degree < Q.degree) : P.eval =o[atBot] Q.eval := by
  rw [← P.degree_comp_neg_X, ← Q.degree_comp_neg_X] at h
  convert! (isLittleO_atTop_of_degree_lt _ _ h).comp_tendsto tendsto_neg_atBot_atTop using 2
  all_goals simp

theorem isBigO_atTop_of_degree_le (h : P.degree ≤ Q.degree) : P.eval =O[atTop] Q.eval := by
  by_cases hp : P = 0
  · simpa [hp] using isBigO_zero Q.eval atTop
  · have hq : Q ≠ 0 := ne_zero_of_degree_ge_degree h hp
    have hPQ : ∀ᶠ x in atTop, Q.eval x = 0 → P.eval x = 0 :=
      mem_of_superset (eventually_atTop_not_isRoot Q hq) fun x h h' ↦ absurd h' h
    rcases le_iff_lt_or_eq.mp h with h | h
    · exact isBigO_of_div_tendsto_nhds hPQ 0 (div_tendsto_atTop_zero_of_degree_lt P Q h)
    · exact isBigO_of_div_tendsto_nhds hPQ _ (div_tendsto_atTop_leadingCoeff_div_of_degree_eq P Q h
        (hQ := (leadingCoeff_ne_zero.mpr hq).isUnit))

theorem isBigO_atBot_of_degree_le (h : P.degree ≤ Q.degree) : P.eval =O[atBot] Q.eval := by
  rw [← P.degree_comp_neg_X, ← Q.degree_comp_neg_X] at h
  convert! (isBigO_atTop_of_degree_le _ _ h).comp_tendsto tendsto_neg_atBot_atTop using 2
  all_goals simp

section Cobounded

open Bornology

variable {R : Type*} [NormedRing R] [NormMulClass R] {P Q : R[X]}

lemma isEquivalent_cobounded_leading_monomial :
    P.eval ~[cobounded R] (P.leadingCoeff * · ^ P.natDegree) := by
  by_cases h : P = 0
  · simp [h, IsEquivalent.refl]
  · simp only [eval_eq_sum_range, sum_range_succ]
    exact (IsLittleO.fun_sum fun i hi ↦
      ((isLittleO_pow_pow_cobounded_of_lt (mem_range.mp hi)).const_mul_right
        (leadingCoeff_ne_zero.mpr h)).const_mul_left _).add_isEquivalent .refl

theorem isLittleO_cobounded_of_degree_lt (h : P.degree < Q.degree) :
    P.eval =o[cobounded R] Q.eval := by
  by_cases hP : P = 0
  · simp [hP]
  · refine isEquivalent_cobounded_leading_monomial.trans_isLittleO <|
      ((IsLittleO.const_mul_right ?_ ?_).const_mul_left _).trans_isEquivalent
        isEquivalent_cobounded_leading_monomial.symm
    · exact leadingCoeff_ne_zero.mpr (ne_zero_of_degree_gt h)
    · exact isLittleO_pow_pow_cobounded_of_lt (natDegree_lt_natDegree hP h)

theorem isBigO_cobounded_of_degree_le (h : P.degree ≤ Q.degree) :
    P.eval =O[cobounded R] Q.eval := by
  by_cases hQ : Q.leadingCoeff = 0
  · aesop
  · refine isEquivalent_cobounded_leading_monomial.trans_isBigO <|
      ((IsBigO.const_mul_right hQ ?_).const_mul_left _).trans_isEquivalent
        isEquivalent_cobounded_leading_monomial.symm
    exact isBigO_pow_pow_cobounded_of_le (natDegree_le_natDegree h)

end Cobounded

/-- If `deg Q < deg P`, there are only finitely many integers `x` where `|P(x)| ≤ |Q(x)|`. -/
lemma finite_abs_eval_le_of_degree_lt {P Q : ℤ[X]} (h : Q.degree < P.degree) :
    {x | |P.eval x| ≤ |Q.eval x|}.Finite := by
  have o := isLittleO_cobounded_of_degree_lt h
  rw [IsOrderBornology.cobounded_eq, ← Int.cofinite_eq] at o
  have nr := eventually_cofinite_not_isRoot (ne_zero_of_degree_gt h)
  have key := o.eventuallyLT_norm_of_eventually_pos (nr.congr (.of_forall (by simp)))
  simp_rw [eventually_cofinite, not_lt, Int.norm_eq_abs] at key
  norm_cast at key

/-- If `Q(x) ∣ P(x)` at infinitely many integers `x` and `Q` is monic, `Q ∣ P`. -/
theorem dvd_of_infinite_eval_dvd_eval
    {P Q : ℤ[X]} (mQ : Q.Monic) (h : {a | Q.eval a ∣ P.eval a}.Infinite) : Q ∣ P := by
  have eqR := modByMonic_add_div P mQ
  have degR := degree_modByMonic_lt P mQ
  rw [← modByMonic_eq_zero_iff_dvd mQ]
  set R := P %ₘ Q
  apply eq_zero_of_infinite_isRoot
  refine (h.sdiff (finite_abs_eval_le_of_degree_lt degR)).mono fun x mx ↦ ?_
  simp only [Set.mem_sdiff, Set.mem_ofPred_eq, not_le] at mx
  rw [← eqR, eval_add, eval_mul, Int.dvd_add_self_mul, ← abs_dvd] at mx
  exact Int.eq_zero_of_abs_lt_dvd mx.1 mx.2

end Polynomial
