/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Meromorphic.FactorizedRational
public import Mathlib.Analysis.Meromorphic.RCLike
public import Mathlib.Analysis.Meromorphic.Section
public import Mathlib.Analysis.Normed.Module.Connected

/-!
# Canonical Decomposition

A meromorphic function of finite order on a closed disk has only finitely many zeros and poles
there. Its interior divisor prescribes a finite product of canonical factors, each of norm one
on the boundary circle. Removing this product leaves a normalized meromorphic remainder with
the original boundary divisor. Its scalar domain includes every point of the disk except for
the boundary poles.

The extended canonical decomposition also removes the boundary divisor as a factorized rational
function. The resulting remainder is analytic and nowhere zero on the closed disk. Its values at
zeros and poles of the original function are determined by their leading coefficients.

See Page 160f of [Lang, *Introduction to Complex Hyperbolic Spaces*][MR886677] for a detailed
discussion.
-/

@[expose] public section

namespace Complex

open Filter Function MeromorphicOn MeromorphicSection Metric Real Set TopologicalSpace

open scoped ComplexConjugate Topology

variable {R : ℝ} {w : ℂ}

/-!
## Canonical Factors

For `w ∈ ball 0 R` the inverse Blaschke factor has a simple pole at `w`, no zeros on
the open disk, and norm one on the boundary circle. The meromorphic section is defined
for every nonzero real parameter `R`.
-/

/-- The denominator of the canonical factor is nonzero in every stalk. -/
theorem canonicalFactorDenominator_nonvanishing (R : ℝ) (w : ℂ) (hR : R ≠ 0) :
    (ofAnalyticOn (U := ⊤) (fun z : ℂ ↦ (R : ℂ) * (z - w)) (fun _ _ ↦ by fun_prop)).Nonvanishing :=
  nonvanishing_of_preconnected _ isPreconnected_univ (Set.mem_univ (w + 1)) (by simp [hR])

/-- The canonical factor as a meromorphic section on the complex plane. -/
noncomputable def canonicalFactor (R : ℝ) (w : ℂ) (hR : R ≠ 0 := by checked_nonzero) :
    MeromorphicSection (⊤ : Opens ℂ) :=
  ofAnalyticOn (U := ⊤) (fun z : ℂ ↦ (R : ℂ) ^ 2 - conj w * z) (fun _ _ ↦ by fun_prop) /ₚ
    unit (ofAnalyticOn (fun z : ℂ ↦ (R : ℂ) * (z - w)) (fun _ _ ↦ by fun_prop))
      (canonicalFactorDenominator_nonvanishing R w hR)

/-- The canonical factor satisfies its defining quotient identity in every stalk. -/
theorem germ_canonicalFactor_mul_denominator {hR : R ≠ 0} (z : ℂ) :
    germ ⟨z, mem_univ z⟩ (canonicalFactor R w hR) *
        MeromorphicGerm.ofAnalytic
          (AnalyticGerm.ofFun (fun y : ℂ ↦ (R : ℂ) * (y - w)) (by fun_prop)) =
      MeromorphicGerm.ofAnalytic (AnalyticGerm.ofFun (fun y : ℂ ↦ (R : ℂ) ^ 2 - conj w * y)
        (by fun_prop)) := by
  let a := AnalyticGerm.ofFun (z := z) (fun y : ℂ ↦ (R : ℂ) ^ 2 - conj w * y) (by fun_prop)
  let b := AnalyticGerm.ofFun (z := z) (fun y : ℂ ↦ (R : ℂ) * (y - w)) (by fun_prop)
  have hb : MeromorphicGerm.ofAnalytic b ≠ 0 :=
    canonicalFactorDenominator_nonvanishing R w hR ⟨z, mem_univ z⟩
  change Checked.div (MeromorphicGerm.ofAnalytic a) (MeromorphicGerm.ofAnalytic b) hb.isUnit *
    MeromorphicGerm.ofAnalytic b = MeromorphicGerm.ofAnalytic a
  exact div_mul_cancel₀ _

/-- Away from the denominator's zero, the canonical factor is regular. -/
theorem mem_regularLocus_canonicalFactor_of_ne {hR : R ≠ 0} {z : ℂ} (hz : z ≠ w) :
    (⟨z, mem_univ z⟩ : (⊤ : Opens ℂ)) ∈ regularLocus (canonicalFactor R w hR) := by
  let a := AnalyticGerm.ofFun (fun y : ℂ ↦ (R : ℂ) ^ 2 - conj w * y) (z := z) (by fun_prop)
  let b := AnalyticGerm.ofFun (fun y : ℂ ↦ (R : ℂ) * (y - w)) (z := z) (by fun_prop)
  have hb : AnalyticGerm.eval b ≠ 0 := mul_ne_zero (ofReal_ne_zero.mpr hR) (sub_ne_zero.mpr hz)
  apply (MeromorphicGerm.div_mem_regularSubring_iff (a := a) (b := b)
    (MeromorphicGerm.ofAnalytic_ne_zero.mp (canonicalFactorDenominator_nonvanishing R w hR
      ⟨z, mem_univ z⟩)) (fun h ↦ (hb h).elim)).mpr hb

/-- The scalar value away from the center is the usual quotient. -/
theorem canonicalFactor_apply {hR : R ≠ 0} {z : ℂ} (hz : z ≠ w) :
    eval (canonicalFactor R w hR) ⟨⟨z, mem_univ z⟩, mem_regularLocus_canonicalFactor_of_ne hz⟩ =
      Checked.div ((R : ℂ) ^ 2 - conj w * z) ((R : ℂ) * (z - w))
        (mul_ne_zero (ofReal_ne_zero.mpr hR) (sub_ne_zero.mpr hz)).isUnit :=
  MeromorphicGerm.eval_eq_div_of_mul_eq _ (germ_canonicalFactor_mul_denominator z)
    (mul_ne_zero (ofReal_ne_zero.mpr hR) (sub_ne_zero.mpr hz))

/-- When the numerator also vanishes at the center, the canonical factor is the
constant meromorphic section with value `-conj w / R`. -/
theorem canonicalFactor_of_center_eq {hR : R ≠ 0} (h : (R : ℂ) ^ 2 = conj w * w) :
    canonicalFactor R w hR = ofAnalyticOn (fun _ : ℂ ↦ Checked.div (-conj w) (R : ℂ)
      (ofReal_ne_zero.mpr hR).isUnit) (fun _ _ ↦ analyticAt_const) := by
  let c := Checked.div (-conj w) (R : ℂ) (ofReal_ne_zero.mpr hR).isUnit
  have hc : c * (R : ℂ) = -conj w := div_mul_cancel₀ _
  apply Subtype.ext
  funext x
  apply mul_right_cancel₀ (canonicalFactorDenominator_nonvanishing R w hR x)
  apply (germ_canonicalFactor_mul_denominator (hR := hR) (w := w) (x : ℂ)).trans
  change MeromorphicGerm.ofAnalytic _ =
    MeromorphicGerm.ofAnalytic (AnalyticGerm.ofFun (fun _ : ℂ ↦ c) analyticAt_const) *
      MeromorphicGerm.ofAnalytic (AnalyticGerm.ofFun (fun y : ℂ ↦ (R : ℂ) * (y - w)) (by fun_prop))
  rw [← map_mul]
  apply congrArg MeromorphicGerm.ofAnalytic
  apply AnalyticGerm.ofFun_eq_iff.mpr
  · apply Filter.Eventually.of_forall
    intro y
    change (R : ℂ) ^ 2 - conj w * y = c * ((R : ℂ) * (y - w))
    rw [h, ← mul_assoc, hc]
    ring
  · fun_prop

/-- The center is a genuine pole unless numerator and denominator cancel. -/
theorem mem_regularLocus_canonicalFactor_center_iff {hR : R ≠ 0} :
    (⟨w, mem_univ w⟩ : (⊤ : Opens ℂ)) ∈ regularLocus (canonicalFactor R w hR) ↔
      (R : ℂ) ^ 2 = conj w * w := by
  constructor
  · intro hreg
    obtain ⟨v, hv⟩ := hreg
    have he := germ_canonicalFactor_mul_denominator (R := R) (w := w) (hR := hR) w
    rw [← hv, ← map_mul] at he
    have hh := congrArg AnalyticGerm.eval (MeromorphicGerm.ofAnalytic_injective he)
    apply sub_eq_zero.mp
    simpa only [map_mul, AnalyticGerm.eval_ofFun, sub_self, mul_zero] using hh.symm
  · intro hzero
    rw [canonicalFactor_of_center_eq hzero]
    exact mem_regularLocus_ofAnalyticOn _ _ _

/-!
### Regularity properties
-/

/-- The scalar function of the canonical section is meromorphic on the plane. -/
theorem meromorphic_canonicalFactor (R : ℝ) (w : ℂ) {hR : R ≠ 0} :
    Meromorphic (canonicalFactor R w hR).eval (fun y ↦ (y.val : ℂ)) :=
  fun x ↦ (canonicalFactor R w hR).meromorphicOn_eval x (mem_univ x)

/-- The canonical scalar function has normal form at every point. -/
theorem meromorphicNFOn_canonicalFactor (R : ℝ) (w : ℂ) {hR : R ≠ 0} :
    MeromorphicNFOn (canonicalFactor R w hR).eval univ (fun y ↦ (y.val : ℂ)) :=
  (canonicalFactor R w hR).meromorphicNFOn_eval

/-- The canonical factor is analytic throughout its actual regular locus. -/
theorem analyticOnNhd_canonicalFactor (R : ℝ) (w : ℂ) {hR : R ≠ 0} :
    AnalyticOnNhd ℂ (canonicalFactor R w hR).eval univ (fun y ↦ (y.val : ℂ)) :=
  fun y _ ↦ ((meromorphicNFOn_canonicalFactor R w (hR := hR))
    (z := (y.val : ℂ)) (mem_univ _)).analyticAt_of_mem

/-- Orders of the canonical section are computed as the difference of the two analytic orders. -/
theorem order_canonicalFactor_eq (R : ℝ) (w z : ℂ) {hR : R ≠ 0} :
    meromorphicOrderAt (canonicalFactor R w hR).eval z (meromorphic_canonicalFactor R w z) =
      (analyticOrderAt (fun y : ℂ ↦ (R : ℂ) ^ 2 - conj w * y) z (by fun_prop)).map (↑· : ℕ → ℤ) -
      (analyticOrderAt (fun y : ℂ ↦ (R : ℂ) * (y - w)) z (by fun_prop)).map (↑· : ℕ → ℤ) := by
  let a := AnalyticGerm.ofFun (z := z) (fun y : ℂ ↦ (R : ℂ) ^ 2 - conj w * y) (by fun_prop)
  let b := AnalyticGerm.ofFun (z := z) (fun y : ℂ ↦ (R : ℂ) * (y - w)) (by fun_prop)
  have hb : b ≠ 0 := MeromorphicGerm.ofAnalytic_ne_zero.mp
    (canonicalFactorDenominator_nonvanishing R w hR ⟨z, mem_univ z⟩)
  have he : germ ⟨z, mem_univ z⟩ (canonicalFactor R w hR) =
      Checked.div (MeromorphicGerm.ofAnalytic a) (MeromorphicGerm.ofAnalytic b)
        (MeromorphicGerm.ofAnalytic_ne_zero.mpr hb).isUnit :=
    eq_div_iff.mpr (germ_canonicalFactor_mul_denominator z)
  rw [(canonicalFactor R w hR).order_eval ⟨z, mem_univ z⟩, he, MeromorphicGerm.order_div a b hb]
  simp only [a, b, AnalyticGerm.order_ofFun]

private theorem canonicalFactor_numerator_ne_zero {z : ℂ} (hw : w ∈ ball 0 R)
    (hz : z ∈ closedBall 0 R) : (R : ℂ) ^ 2 - conj w * z ≠ 0 := by
  have hR := pos_of_mem_ball hw
  simp only [mem_ball, dist_zero_right, mem_closedBall] at hw hz
  suffices ‖conj w * z‖ < ‖(R : ℂ) ^ 2‖ by grind
  suffices ‖w‖ * ‖z‖ < R * R by simpa [sq]
  grw [hz]
  gcongr

/-- The factor of an interior point has a simple pole at that point. -/
theorem meromorphicOrderAt_canonicalFactor (hw : w ∈ ball 0 R) :
    meromorphicOrderAt (canonicalFactor R w (pos_of_mem_ball hw).ne').eval w
      (meromorphic_canonicalFactor R w w) = -1 := by
  have ha : AnalyticAt ℂ (fun y : ℂ ↦ (R : ℂ) ^ 2 - conj w * y) w := by fun_prop
  have hb : AnalyticAt ℂ (fun y : ℂ ↦ y - w) w := analyticAt_id.sub analyticAt_const
  have hc : AnalyticAt ℂ (fun _ : ℂ ↦ (R : ℂ)) w := analyticAt_const
  rw [order_canonicalFactor_eq R w w, ha.analyticOrderAt_eq_zero.mpr
    (canonicalFactor_numerator_ne_zero hw (ball_subset_closedBall hw))]
  have hmul := analyticOrderAt_mul hc hb
  change analyticOrderAt (fun y ↦ (R : ℂ) * (y - w)) w _ = _ at hmul
  rw [hmul, hc.analyticOrderAt_eq_zero.mpr (ofReal_ne_zero.mpr (pos_of_mem_ball hw).ne'),
    analyticOrderAt_id_sub_const_self]
  simp

/-!
### Values of Canonical Factors
-/

/-- The factor does not vanish at a regular point of the closed disk. -/
theorem canonicalFactor_ne_zero {z : ℂ} (hw : w ∈ ball 0 R) (hz : z ∈ closedBall 0 R)
    (hzw : z ≠ w) :
    eval (canonicalFactor R w (pos_of_mem_ball hw).ne')
      ⟨⟨z, mem_univ z⟩, mem_regularLocus_canonicalFactor_of_ne hzw⟩ ≠ 0 := by
  rw [canonicalFactor_apply hzw]
  exact div_ne_zero (canonicalFactor_numerator_ne_zero hw hz)

/-- The canonical factor has unit norm on the boundary circle. -/
theorem norm_canonicalFactor_eval_circle_eq_one {z : ℂ} (hw : w ∈ ball 0 R) (hz : z ∈ sphere 0 R) :
    ‖eval (canonicalFactor R w (pos_of_mem_ball hw).ne') ⟨⟨z, mem_univ z⟩,
      mem_regularLocus_canonicalFactor_of_ne
        (fun h ↦ (sphere_disjoint_ball.notMem_of_mem_left hz) (h ▸ hw))⟩‖ = 1 := by
  have hR := pos_of_mem_ball hw
  have hzw : z ≠ w := fun h ↦ sphere_disjoint_ball.notMem_of_mem_left hz (h ▸ hw)
  rw [canonicalFactor_apply hzw, norm_div, div_eq_iff, one_mul]
  obtain rfl := by simpa [mem_sphere_zero_iff_norm] using hz
  rw [← ofReal_pow, ← normSq_eq_norm_sq, normSq_eq_conj_mul_self, ← sub_mul, mul_comm _ z]
  simp [← map_sub]

/-!
### Orders and Divisors
-/

/-- Each canonical factor is a unit of the ring of global meromorphic sections. -/
theorem canonicalFactor_nonvanishing (R : ℝ) (w : ℂ) {hR : R ≠ 0} :
    (canonicalFactor R w hR).Nonvanishing := by
  let A := fun z : ℂ ↦ (R : ℂ) ^ 2 - conj w * z
  have ha : AnalyticOnNhd ℂ A univ := fun _ _ ↦ by dsimp [A]; fun_prop
  have hne := nonvanishing_of_preconnected (U := ⊤) ha isPreconnected_univ (mem_univ 0)
    (show A 0 ≠ 0 by simp [A, hR])
  intro x hx
  apply hne x
  have he := germ_canonicalFactor_mul_denominator (R := R) (w := w) (hR := hR) (x : ℂ)
  change germ x (canonicalFactor R w hR) * _ = germ x (ofAnalyticOn A ha) at he
  rw [hx, zero_mul] at he
  exact he.symm

/-- Canonical factors have finite order at every point of the plane. -/
theorem meromorphicOrderAt_canonicalFactor_ne_top (R : ℝ) (w z : ℂ) {hR : R ≠ 0} :
    meromorphicOrderAt (canonicalFactor R w hR).eval z (meromorphic_canonicalFactor R w z) ≠ ⊤ := by
  rw [order_canonicalFactor_eq]
  let A := fun y : ℂ ↦ (R : ℂ) ^ 2 - conj w * y
  let B := fun y : ℂ ↦ (R : ℂ) * (y - w)
  have ha : AnalyticOnNhd ℂ A univ := fun _ _ ↦ by dsimp [A]; fun_prop
  have hb : AnalyticOnNhd ℂ B univ := fun _ _ ↦ by dsimp [B]; fun_prop
  have hna := AnalyticGerm.ofFun_ne_zero_of_preconnected ha isPreconnected_univ (mem_univ z)
    (mem_univ 0) (by simp [A, hR])
  have hnb := AnalyticGerm.ofFun_ne_zero_of_preconnected hb isPreconnected_univ (mem_univ z)
    (mem_univ (w + 1)) (by simp [B, hR])
  have hfinite (f : ℂ → ℂ) (h : AnalyticAt ℂ f z) (hn : AnalyticGerm.ofFun f h ≠ 0) :
      analyticOrderAt f z h ≠ ⊤ := by
    rw [← AnalyticGerm.order_ofFun]
    exact mt (AnalyticGerm.order_eq_top_iff _).mp hn
  have hA := hfinite A (ha z trivial) hna
  have hB := hfinite B (hb z trivial) hnb
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hA
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hB
  change (analyticOrderAt A z _).map (↑· : ℕ → ℤ) - (analyticOrderAt B z _).map (↑· : ℕ → ℤ) ≠ ⊤
  rw [← hm, ← hn, ENat.map_natCast, ENat.map_natCast, ← WithTop.LinearOrderedAddCommGroup.coe_sub]
  exact WithTop.coe_ne_top

/-- In the open disk, the canonical factor has divisor minus the point mass at its pole. -/
theorem divisor_canonicalFactor (hw : w ∈ ball 0 R)
    {hf : MeromorphicOn (canonicalFactor R w (pos_of_mem_ball hw).ne').eval (ball 0 R)
      (fun z ↦ (z.val : ℂ))}
    {h : ∀ z (hz : z ∈ ball 0 R), meromorphicOrderAt _ z (hf z hz) ≠ ⊤} :
    MeromorphicOn.divisor _ (ball 0 R) h =
      -(Function.locallyFinsuppWithin.single w 1).restrict (Set.subset_univ (ball 0 R)) := by
  ext z
  by_cases hz : z ∈ ball 0 R
  · have h₂ := MeromorphicOn.coe_divisor_apply hf hz (h := h)
    by_cases hzw : z = w
    · subst z
      rw [meromorphicOrderAt_canonicalFactor hw] at h₂
      have he : MeromorphicOn.divisor _ (ball 0 R) h w = -1 := by
        apply WithTop.coe_injective
        exact h₂
      simp [he, Function.locallyFinsuppWithin.restrict_apply, hw]
    · have ha : AnalyticAt ℂ (fun y : ℂ ↦ (R : ℂ) ^ 2 - conj w * y) z := by fun_prop
      have hb : AnalyticAt ℂ (fun y : ℂ ↦ (R : ℂ) * (y - w)) z := by fun_prop
      rw [order_canonicalFactor_eq, ha.analyticOrderAt_eq_zero.mpr
        (canonicalFactor_numerator_ne_zero hw (ball_subset_closedBall hz)),
        hb.analyticOrderAt_eq_zero.mpr (mul_ne_zero (ofReal_ne_zero.mpr (pos_of_mem_ball hw).ne')
          (sub_ne_zero.mpr hzw)), ENat.map_zero, Nat.cast_zero, WithTop.coe_zero, sub_zero] at h₂
      have he : MeromorphicOn.divisor _ (ball 0 R) h z = 0 := by exact_mod_cast h₂
      simp [he, hzw, Function.locallyFinsuppWithin.restrict_apply, hz]
  · simp [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hz]

/-- Interior factors with their prescribed integer multiplicities form a unit of the global
ring of meromorphic sections. Only points in the finite support enter the product. -/
noncomputable def canonicalProduct {R : ℝ} (D : Function.locallyFinsuppWithin (ball (0 : ℂ) R) ℤ)
    (hD : D.support.Finite) : (MeromorphicSection (⊤ : Opens ℂ))ˣ :=
  ∏ u ∈ hD.toFinset.attach,
    let hw := D.supportWithinDomain (hD.mem_toFinset.mp u.property)
    let hR := (pos_of_mem_ball hw).ne'
    (unit (canonicalFactor R u hR) (canonicalFactor_nonvanishing R u (hR := hR))) ^ (-D u)

/-- The order of a product of canonical units is the weighted sum of their stalk orders. -/
theorem order_canonicalProduct {R : ℝ} (D : Function.locallyFinsuppWithin (ball (0 : ℂ) R) ℤ)
    (hD : D.support.Finite) (x : ℂ) :
    MeromorphicGerm.order (germ ⟨x, mem_univ x⟩ (canonicalProduct D hD).val) =
      ∑ u ∈ hD.toFinset.attach,
        let hw := D.supportWithinDomain (hD.mem_toFinset.mp u.property)
        (-D u : ℤ) * MeromorphicGerm.order
          (germ ⟨x, mem_univ x⟩ (canonicalFactor R u (pos_of_mem_ball hw).ne')) := by
  let k := germ (U := ⊤) ⟨x, mem_univ x⟩
  let F (u : hD.toFinset) : (MeromorphicSection (⊤ : Opens ℂ))ˣ :=
    let hw := D.supportWithinDomain (hD.mem_toFinset.mp u.property)
    unit (canonicalFactor R u (pos_of_mem_ball hw).ne') (canonicalFactor_nonvanishing R u)
  have hprod (s : Finset hD.toFinset) :
      MeromorphicGerm.order (k (↑(∏ u ∈ s, (F u) ^ (-D u)) : MeromorphicSection ⊤)) =
        ∑ u ∈ s, (-D u : ℤ) * MeromorphicGerm.order (k (F u).val) := by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert u s hu ih =>
      rw [Finset.prod_insert hu, Units.val_mul, map_mul, MeromorphicGerm.order_mul, ih,
        Finset.sum_insert hu]
      congr 1
      change MeromorphicGerm.order ((Units.map k.toMonoidHom (F u ^ (-D u))).val) = _
      rw [map_zpow, MeromorphicGerm.order_unit_zpow]
      rfl
  exact hprod hD.toFinset.attach

/-- On the closed disk the order of a canonical factor is minus the point mass at its center. -/
theorem order_canonicalFactor_on_closedBall {R : ℝ} {w z : ℂ} (hw : w ∈ ball 0 R)
    (hz : z ∈ closedBall 0 R) :
    MeromorphicGerm.order (germ ⟨z, mem_univ z⟩ (canonicalFactor R w (pos_of_mem_ball hw).ne')) =
      if z = w then -1 else 0 := by
  rw [← (canonicalFactor R w (pos_of_mem_ball hw).ne').order_eval ⟨z, mem_univ z⟩]
  by_cases hzw : z = w
  · subst z
    exact (meromorphicOrderAt_canonicalFactor hw).trans (ite_eq_left rfl).symm
  · rw [ite_eq_right hzw, order_canonicalFactor_eq]
    have hA : AnalyticAt ℂ (fun y : ℂ ↦ (R : ℂ) ^ 2 - conj w * y) z := by fun_prop
    have hB : AnalyticAt ℂ (fun y : ℂ ↦ (R : ℂ) * (y - w)) z := by fun_prop
    rw [hA.analyticOrderAt_eq_zero.mpr (canonicalFactor_numerator_ne_zero hw hz),
      hB.analyticOrderAt_eq_zero.mpr (mul_ne_zero (ofReal_ne_zero.mpr (pos_of_mem_ball hw).ne')
        (sub_ne_zero.mpr hzw)), ENat.map_zero]
    rfl

/-- The canonical product realizes its prescribed order at every point of the closed disk.
It therefore has order zero along the boundary. -/
theorem order_canonicalProduct_on_closedBall {R : ℝ}
    (D : Function.locallyFinsuppWithin (ball (0 : ℂ) R) ℤ)
    (hD : D.support.Finite) {z : ℂ} (hz : z ∈ closedBall 0 R) :
    MeromorphicGerm.order (germ ⟨z, mem_univ z⟩ (canonicalProduct D hD).val) = D z := by
  classical
  rw [order_canonicalProduct]
  calc
    _ = ∑ u ∈ hD.toFinset.attach, (if z = (u : ℂ) then (D u : WithTop ℤ) else 0) := by
      apply Finset.sum_congr rfl
      intro u _
      have hw := D.supportWithinDomain (hD.mem_toFinset.mp u.property)
      change (-D u : ℤ) * MeromorphicGerm.order
        (germ ⟨z, mem_univ z⟩ (canonicalFactor R u (pos_of_mem_ball hw).ne')) = _
      rw [order_canonicalFactor_on_closedBall hw hz]
      by_cases he : z = (u : ℂ)
      · rw [ite_eq_left he, ite_eq_left he]
        exact congrArg ((↑) : ℤ → WithTop ℤ) (show -(D u) * (-1) = D u by ring)
      · simp only [ite_eq_right he, mul_zero]
    _ = D z := by
      rw [Finset.sum_attach hD.toFinset fun u ↦ if z = u then (D u : WithTop ℤ) else 0,
        Finset.sum_ite_eq]
      by_cases he : z ∈ hD.toFinset
      · simp [he]
      · have hzero : D z = 0 := by
          simpa only [Finite.mem_toFinset, Function.mem_support, not_not] using he
        simp [he, hzero]

/-! ## Canonical decomposition -/

/-- A regular section and a regular inverse evaluate to reciprocals. -/
private theorem eval_unit_mul_inv (u : (MeromorphicSection (⊤ : Opens ℂ))ˣ) (x : (⊤ : Opens ℂ))
    (hp : x ∈ regularLocus u.val) (hq : x ∈ regularLocus u.inv) :
    u.val.eval ⟨x, hp⟩ * u.inv.eval ⟨x, hq⟩ = 1 := by
  have h : (⟨germ x u.val, hp⟩ : MeromorphicGerm.regularSubring (x : ℂ)) *
      ⟨germ x u.inv, hq⟩ = 1 := by
    apply Subtype.ext
    change germ x u.val * germ x u.inv = 1
    rw [← map_mul, u.val_inv, map_one]
  change MeromorphicGerm.eval ⟨germ x u.val, hp⟩ * MeromorphicGerm.eval ⟨germ x u.inv, hq⟩ = 1
  simpa only [map_mul, map_one] using congrArg (MeromorphicGerm.eval (z := (x : ℂ))) h



private theorem exists_normalized_section_quotient
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {U : Set ℂ} {f : ℂ → E} (hf : MeromorphicOn f U)
    (u : (MeromorphicSection (⊤ : Opens ℂ))ˣ) :
    ∃ (T : Set ℂ) (G : T → E), ∃ hG : MeromorphicNFOn G U Subtype.val,
      (∀ x (hx : x ∈ U), meromorphicOrderAt G x (hG.meromorphicOn x hx) =
        meromorphicOrderAt f x (hf x hx) - MeromorphicGerm.order (germ ⟨x, mem_univ x⟩ u.val)) ∧
      ∀ᶠ y in Filter.codiscreteWithin U,
        ∃ (hy : y ∈ T) (hp : (⟨y, mem_univ y⟩ : (⊤ : Opens ℂ)) ∈ u.val.regularLocus),
        f y = (u.val.eval ⟨⟨y, mem_univ y⟩, hp⟩) • G ⟨y, hy⟩ := by
  let S := {y : ℂ | (⟨y, mem_univ y⟩ : (⊤ : Opens ℂ)) ∈ u.inv.regularLocus}
  let j := fun y : S ↦ (⟨⟨y, mem_univ y.val⟩, y.property⟩ : u.inv.regularLocus)
  let q := u.inv.eval ∘ j
  let F := q • (f ∘ (Subtype.val : S → ℂ))
  have hS (x : ℂ) : S ∈ 𝓝[≠] x := by
    filter_upwards [(u.inv.meromorphicOn_eval x (mem_univ x)).1] with y ⟨a, ha⟩
    have he : a.val = (⟨y, mem_univ y⟩ : (⊤ : Opens ℂ)) := Subtype.ext ha
    change (⟨y, mem_univ y⟩ : (⊤ : Opens ℂ)) ∈ u.inv.regularLocus
    exact he ▸ a.property
  have hq (x : ℂ) : MeromorphicAt q x Subtype.val := by
    apply (u.inv.meromorphicOn_eval x (mem_univ x)).comp_domain j
    change range (Subtype.val : S → ℂ) ∈ 𝓝[≠] x
    simpa only [Subtype.range_coe] using hS x
  have hF : MeromorphicOn F U Subtype.val := by
    intro x hx
    apply (hq x).smul
    apply (hf x hx).comp_domain (coord := _root_.id) (Subtype.val : S → ℂ)
    simpa only [Function.id_comp, Subtype.range_coe] using hS x
  obtain ⟨T, G, hG, _, _, _, he⟩ := hF.exists_normalForm_on_domain
  refine ⟨T, G, hG, ?_, ?_⟩
  · intro x hx
    have hFG := (hG.meromorphicOn x hx).order_eq_of_eventuallyEq (hF x hx) (by
      filter_upwards [he x hx] with y hy
      rintro ⟨a, ha⟩ ⟨b, hb⟩ rfl hb'
      obtain rfl : b = a := hb'
      exact hy ha hb)
    have hqOrder : meromorphicOrderAt q x (hq x) =
        MeromorphicGerm.order (germ ⟨x, mem_univ x⟩ u.inv) :=
      ((u.inv.meromorphicOn_eval x (mem_univ x)).order_comp_domain j
        (by change Set.range (Subtype.val : S → ℂ) ∈ 𝓝[≠] x; simpa using hS x)).trans
          (u.inv.order_eval ⟨x, mem_univ x⟩)
    let k := germ (U := (⊤ : Opens ℂ)) ⟨x, mem_univ x⟩
    have hi : k u.inv = (↑(Units.map k.toMonoidHom u)⁻¹ : MeromorphicGerm x) := rfl
    rw [hFG, (hq x).order_smul_comp_domain (hf x hx), hqOrder, hi, MeromorphicGerm.order_unit_inv]
    rw [sub_eq_add_neg, add_comm]
    rfl
  · apply eventually_codiscreteWithin_iff_forall_eventually_nhdsNE.mpr
    intro x hx
    filter_upwards [he x hx, hS x, (hG.meromorphicOn x hx).1,
      (u.val.meromorphicOn_eval x (mem_univ x)).1] with y hye hys ⟨t, ht⟩ ⟨a, ha⟩
    intro _
    have hyt : y ∈ T := ht ▸ t.property
    have hya : (⟨y, mem_univ y⟩ : (⊤ : Opens ℂ)) ∈ u.val.regularLocus :=
      (Subtype.ext ha : a.val = ⟨y, mem_univ y⟩) ▸ a.property
    refine ⟨hyt, hya, ?_⟩
    rw [hye hyt hys]
    change f y = u.val.eval ⟨⟨y, mem_univ y⟩, hya⟩ • (u.inv.eval ⟨⟨y, mem_univ y⟩, hys⟩ • f y)
    rw [← mul_smul, eval_unit_mul_inv, one_smul]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : ℂ → E}

/-- The unit of meromorphic sections prescribed by the interior divisor of a disk. -/
noncomputable def _root_.MeromorphicOn.canonicalFactorProduct
    (hf : MeromorphicOn f (closedBall (0 : ℂ) R))
    (h : ∀ x (hx : x ∈ closedBall (0 : ℂ) R), meromorphicOrderAt f x (hf x hx) ≠ ⊤) :
    (MeromorphicSection (⊤ : Opens ℂ))ˣ :=
  canonicalProduct (divisor f (ball (0 : ℂ) R) (hf := hf.mono_set ball_subset_closedBall)
    (fun x hx ↦ h x (ball_subset_closedBall hx))) hf.divisor_ball_support_finite

/-- A canonical decomposition removes the interior divisor by a Blaschke product.
The normalized remainder contains a point of the closed disk in its scalar domain exactly
when it is regular there. Its remaining orders are prescribed by the boundary divisor. -/
structure CanonicalDecomp (f : ℂ → E) {T : Set ℂ} (g : T → E) (R : ℝ) : Prop where
  /-- The original function is meromorphic on the closed disk. -/
  meromorphicOn : MeromorphicOn f (closedBall (0 : ℂ) R)
  /-- The order of the original function is finite on the closed disk. -/
  meromorphicOrderAt_ne_top : ∀ x (hx : x ∈ closedBall (0 : ℂ) R),
    meromorphicOrderAt f x (meromorphicOn x hx) ≠ ⊤
  /-- The scalar remainder is normalized at each point of the disk. -/
  meromorphicNFOn : MeromorphicNFOn g (closedBall (0 : ℂ) R) Subtype.val
  /-- The only zeros and poles left are those of the original function on the boundary. -/
  order_eq : ∀ x (hx : x ∈ closedBall (0 : ℂ) R),
    meromorphicOrderAt g x (meromorphicNFOn.meromorphicOn x hx) =
      divisor f (sphere (0 : ℂ) R) (hf := meromorphicOn.mono_set sphere_subset_closedBall)
        (fun z hz ↦ meromorphicOrderAt_ne_top z (sphere_subset_closedBall hz)) x
  /-- The proposed factors agree with the original function on a codiscrete subset. -/
  eventuallyEq : ∀ᶠ x in codiscreteWithin (closedBall (0 : ℂ) R),
    ∃ (hx : x ∈ T) (hp : (⟨x, mem_univ x⟩ : (⊤ : Opens ℂ)) ∈
      (meromorphicOn.canonicalFactorProduct meromorphicOrderAt_ne_top).val.regularLocus),
      f x = (meromorphicOn.canonicalFactorProduct meromorphicOrderAt_ne_top).val.eval
        ⟨⟨x, mem_univ x⟩, hp⟩ • g ⟨x, hx⟩

variable {T : Set ℂ} {g : T → E}

/-- The restriction of the original function to the interior has finite order. -/
lemma CanonicalDecomp.meromorphicOrderAt_ne_top_ball (D : CanonicalDecomp f g R) :
    ∀ z (hz : z ∈ ball (0 : ℂ) R), meromorphicOrderAt f z
      ((D.meromorphicOn.mono_set ball_subset_closedBall) z hz) ≠ ⊤ :=
  fun z hz ↦ D.meromorphicOrderAt_ne_top z (ball_subset_closedBall hz)

/-- The restriction of the original function to the boundary has finite order. -/
lemma CanonicalDecomp.meromorphicOrderAt_ne_top_sphere (D : CanonicalDecomp f g R) :
    ∀ z (hz : z ∈ sphere (0 : ℂ) R), meromorphicOrderAt f z
      ((D.meromorphicOn.mono_set sphere_subset_closedBall) z hz) ≠ ⊤ :=
  fun z hz ↦ D.meromorphicOrderAt_ne_top z (sphere_subset_closedBall hz)

/-- The scalar remainder is defined at precisely the points of nonnegative boundary order. -/
theorem CanonicalDecomp.mem_domain_iff (D : CanonicalDecomp f g R) {x : ℂ}
    (hx : x ∈ closedBall (0 : ℂ) R) :
    x ∈ T ↔ 0 ≤ divisor f (sphere (0 : ℂ) R) D.meromorphicOrderAt_ne_top_sphere x := by
  have hf := D.meromorphicNFOn hx
  have hm : x ∈ T ↔ x ∈ range (Subtype.val : T → ℂ) := by simp
  refine hm.trans (hf.mem_range_iff.trans
    (hf.meromorphicAt.meromorphicOrderAt_nonneg_iff.symm.trans ?_))
  rw [D.order_eq x hx]
  exact_mod_cast Iff.rfl

/-- Every interior point belongs to the scalar domain and the remainder is nonzero there. -/
theorem CanonicalDecomp.ne_zero (D : CanonicalDecomp f g R) {x : ℂ} (hx : x ∈ ball (0 : ℂ) R) :
    ∃ h : x ∈ T, g ⟨x, h⟩ ≠ 0 := by
  have hc := ball_subset_closedBall hx
  have hns : x ∉ sphere (0 : ℂ) R := fun hs ↦ (mem_ball.mp hx).ne (mem_sphere.mp hs)
  have hz := (divisor f (sphere (0 : ℂ) R)
    D.meromorphicOrderAt_ne_top_sphere).apply_eq_zero_of_notMem hns
  have ht := (D.mem_domain_iff hc).mpr hz.ge
  refine ⟨ht, ((D.meromorphicNFOn hc).order_eq_zero_iff_value_ne_zero (y := ⟨x, ht⟩) rfl).mp ?_⟩
  rw [D.order_eq x hc, hz, WithTop.coe_zero]

/-- A meromorphic function of finite order admits a canonical decomposition. -/
theorem _root_.MeromorphicOn.exists_canonicalDecomp (hf : MeromorphicOn f (closedBall (0 : ℂ) R))
    (h : ∀ x (hx : x ∈ closedBall (0 : ℂ) R), meromorphicOrderAt f x (hf x hx) ≠ ⊤) :
    ∃ (T : Set ℂ) (g : T → E), CanonicalDecomp f g R := by
  obtain ⟨T, g, hg, ho, he⟩ := exists_normalized_section_quotient hf (hf.canonicalFactorProduct h)
  refine ⟨T, g, hf, h, hg, fun x hx ↦ (ho x hx).trans ?_, he⟩
  rw [MeromorphicOn.canonicalFactorProduct, order_canonicalProduct_on_closedBall _ _ hx]
  rcases lt_or_eq_of_le (mem_closedBall.mp hx) with hi | hs
  · have hib : x ∈ ball (0 : ℂ) R := mem_ball.mpr hi
    have hns : x ∉ sphere (0 : ℂ) R := fun hs ↦ hi.ne (mem_sphere.mp hs)
    rw [locallyFinsuppWithin.apply_eq_zero_of_notMem _ hns, ← coe_divisor_apply
      (h := fun z hz ↦ h z (ball_subset_closedBall hz)) (hf.mono_set ball_subset_closedBall) hib]
    exact_mod_cast sub_self _
  · have hnb : x ∉ ball (0 : ℂ) R := fun hi ↦ (mem_ball.mp hi).ne hs
    rw [locallyFinsuppWithin.apply_eq_zero_of_notMem _ hnb, WithTop.coe_zero, sub_zero,
      coe_divisor_apply (hf.mono_set sphere_subset_closedBall) (mem_sphere.mpr hs)]

/-- The normalized remainder has finite order at every point of the closed disk. -/
lemma CanonicalDecomp.meromorphicOrderAt_ne_top_closedBall (D : CanonicalDecomp f g R) :
    ∀ z (hz : z ∈ closedBall (0 : ℂ) R),
      meromorphicOrderAt g z (D.meromorphicNFOn.meromorphicOn z hz) ≠ ⊤ :=
  fun z hz ↦ (D.order_eq z hz).trans_ne WithTop.coe_ne_top

/-- The divisor of the normalized remainder is the boundary divisor of the original function. -/
theorem CanonicalDecomp.divisor_eq_divisor (D : CanonicalDecomp f g R) (x : ℂ) :
    divisor g (closedBall (0 : ℂ) R) D.meromorphicOrderAt_ne_top_closedBall x =
      divisor f (sphere (0 : ℂ) R) D.meromorphicOrderAt_ne_top_sphere x := by
  by_cases hx : x ∈ closedBall (0 : ℂ) R
  · exact_mod_cast (coe_divisor_apply D.meromorphicNFOn.meromorphicOn hx
      (h := D.meromorphicOrderAt_ne_top_closedBall)).trans (D.order_eq x hx)
  · rw [locallyFinsuppWithin.apply_eq_zero_of_notMem _ hx,
      locallyFinsuppWithin.apply_eq_zero_of_notMem _ (fun h ↦ hx (sphere_subset_closedBall h))]

/-! ## Extended canonical decomposition -/

/-- An injective coordinate presentation admits an ambient representative with the same
punctured germs. The values chosen off the coordinate range are used only in this proof. -/
private theorem exists_ambient_representative {V : Set ℂ} {A : Type*} {c : A → ℂ}
    (hc : Injective c) {s : A → E} (hs : MeromorphicOn s V c) :
    ∃ F : ℂ → E, ∃ hF : MeromorphicOn F V, (∀ a, F (c a) = s a) ∧
      ∀ x (hx : x ∈ V), meromorphicOrderAt F x (hF x hx) = meromorphicOrderAt s x (hs x hx) := by
  classical
  let F := Function.extend c s (0 : ℂ → E)
  have hv (a : A) : F (c a) = s a := hc.extend_apply _ _ a
  have hF (x : ℂ) (hx : x ∈ V) : MeromorphicAt F x := by
    obtain ⟨hr, n, a, ha, he⟩ := hs x hx
    refine ⟨by simp, n, a, ha, ?_⟩
    rw [comap_id]
    filter_upwards [hr, eventually_comap.mp he] with y hyr hy
    obtain ⟨t, rfl⟩ := hyr
    exact (congrArg ((c t - x) ^ n • ·) (hv t)).trans (hy t rfl)
  refine ⟨F, hF, hv, fun x hx ↦ (hF x hx).order_eq_of_eventuallyEq (hs x hx) ?_⟩
  exact .of_forall fun _ _ b h₁ h₂ ↦ (congrArg F (h₁.trans h₂.symm)).trans (hv b)

/-- The boundary powers in an extended disk decomposition are evaluated as a factorized
rational function on the complement of their poles. The Blaschke product accounts for
interior orders, and the remaining factor is analytic and nowhere zero on the closed disk. -/
structure ECanonicalDecomp (f h : ℂ → E) (R : ℝ) : Prop where
  /-- The original function is meromorphic on the closed disk. -/
  meromorphicOn : MeromorphicOn f (closedBall (0 : ℂ) R)
  /-- The order of the original function is finite on the closed disk. -/
  meromorphicOrderAt_ne_top : ∀ x (hx : x ∈ closedBall (0 : ℂ) R),
    meromorphicOrderAt f x (meromorphicOn x hx) ≠ ⊤
  /-- The remainder is analytic at each point of the closed disk. -/
  analyticOnNhd : AnalyticOnNhd ℂ h (closedBall (0 : ℂ) R)
  /-- The remainder is nonzero throughout the closed disk. -/
  ne_zero : ∀ x ∈ closedBall (0 : ℂ) R, h x ≠ 0
  /-- Off a discrete subset all factors have scalar values and their product agrees with `f`. -/
  eventuallyEq :
    let d := divisor f (sphere (0 : ℂ) R) (hf := meromorphicOn.mono_set sphere_subset_closedBall)
      (fun z hz ↦ meromorphicOrderAt_ne_top z (sphere_subset_closedBall hz))
    let P := meromorphicOn.canonicalFactorProduct meromorphicOrderAt_ne_top
    ∀ᶠ x in codiscreteWithin (closedBall (0 : ℂ) R),
      ∃ (hp : (⟨x, mem_univ x⟩ : (⊤ : Opens ℂ)) ∈ P.val.regularLocus) (hd : d x = 0),
        f x = (P.val.eval ⟨⟨x, mem_univ x⟩, hp⟩ *
          FactorizedRational.eval d divisor_sphere_support_finite ⟨x, hd.ge⟩) • h x

variable {h : ℂ → E}

/-- The original function in an extended decomposition has finite order in the open disk. -/
lemma ECanonicalDecomp.meromorphicOrderAt_ne_top_ball (D : ECanonicalDecomp f h R) :
    ∀ z (hz : z ∈ ball (0 : ℂ) R), meromorphicOrderAt f z
      ((D.meromorphicOn.mono_set ball_subset_closedBall) z hz) ≠ ⊤ :=
  fun z hz ↦ D.meromorphicOrderAt_ne_top z (ball_subset_closedBall hz)

/-- The original function in an extended decomposition has finite order on the circle. -/
lemma ECanonicalDecomp.meromorphicOrderAt_ne_top_sphere (D : ECanonicalDecomp f h R) :
    ∀ z (hz : z ∈ sphere (0 : ℂ) R), meromorphicOrderAt f z
      ((D.meromorphicOn.mono_set sphere_subset_closedBall) z hz) ≠ ⊤ :=
  fun z hz ↦ D.meromorphicOrderAt_ne_top z (sphere_subset_closedBall hz)

/-- Every meromorphic function of finite order on the closed disk has an extended canonical
decomposition, including when the original function has poles on the boundary. -/
theorem _root_.MeromorphicOn.exists_ecanonicalDecomp (hf : MeromorphicOn f (closedBall (0 : ℂ) R))
    (hfin : ∀ x (hx : x ∈ closedBall (0 : ℂ) R), meromorphicOrderAt f x (hf x hx) ≠ ⊤) :
    ∃ h, ECanonicalDecomp f h R := by
  obtain ⟨T, g, D⟩ := hf.exists_canonicalDecomp hfin
  obtain ⟨G, hG, hv, ho⟩ :=
    exists_ambient_representative Subtype.val_injective D.meromorphicNFOn.meromorphicOn
  have hGfin (x : ℂ) (hx : x ∈ closedBall (0 : ℂ) R) :
      meromorphicOrderAt G x (hG x hx) ≠ ⊤ :=
    (ho x hx).trans_ne (D.meromorphicOrderAt_ne_top_closedBall x hx)
  let b := divisor f (sphere (0 : ℂ) R) D.meromorphicOrderAt_ne_top_sphere
  have he : (divisor G (closedBall (0 : ℂ) R) hGfin : ℂ → ℤ) = b := by
    funext x
    rw [divisor_congr (h₂ := D.meromorphicOrderAt_ne_top_closedBall) ho]
    exact D.divisor_eq_divisor x
  have hb : b.support.Finite := divisor_sphere_support_finite
  obtain ⟨h, ha, hn, hh⟩ := hG.extract_zeros_poles hGfin
    ((divisor G (closedBall (0 : ℂ) R) hGfin).finiteSupport (isCompact_closedBall _ _))
  have hh' : ∀ᶠ x in codiscreteWithin (closedBall (0 : ℂ) R), ∃ hx : b x = 0,
      G x = FactorizedRational.eval b hb ⟨x, hx.ge⟩ • h x := by
    have transfer {d₁ d₂ : ℂ → ℤ} (e : d₁ = d₂) {hf₁ : d₁.support.Finite}
        {hf₂ : d₂.support.Finite}
        (h₁ : ∀ᶠ x in codiscreteWithin (closedBall (0 : ℂ) R), ∃ hx : d₁ x = 0,
          G x = FactorizedRational.eval d₁ hf₁ ⟨x, hx.ge⟩ • h x) :
        ∀ᶠ x in codiscreteWithin (closedBall (0 : ℂ) R), ∃ hx : d₂ x = 0,
          G x = FactorizedRational.eval d₂ hf₂ ⟨x, hx.ge⟩ • h x := by
      subst d₂
      exact h₁
    exact transfer he hh
  refine ⟨h, hf, hfin, ha, fun x hx ↦ hn ⟨x, hx⟩, ?_⟩
  filter_upwards [D.eventuallyEq, hh'] with x ⟨ht, hp, hx⟩ ⟨hd, hhx⟩
  refine ⟨hp, hd, ?_⟩
  rw [hx, ← hv ⟨x, ht⟩, hhx, mul_smul]

/-! ## Leading coefficients and scalar values -/

/-- The scalar presentation of a meromorphic section unit has finite order everywhere. -/
theorem order_sectionUnit_ne_top (u : (MeromorphicSection (⊤ : Opens ℂ))ˣ) (x : ℂ) :
    meromorphicOrderAt u.val.eval x (u.val.meromorphicOn_eval x (mem_univ x)) ≠ ⊤ := by
  rw [u.val.order_eval ⟨x, mem_univ x⟩]
  intro ht
  have he := congrArg MeromorphicGerm.order (congrArg (germ (U := ⊤) ⟨x, mem_univ x⟩) u.val_inv)
  rw [map_mul, MeromorphicGerm.order_mul, ht, top_add, map_one, MeromorphicGerm.order_one] at he
  exact WithTop.zero_ne_top he.symm

private theorem trailingCoeff_eq_of_rep {A : Type*} {c : A → ℂ} {s : A → E} {F : ℂ → E}
    (hs : MeromorphicAt s w c) (hF : MeromorphicAt F w) (he : ∀ a, F (c a) = s a)
    {hn : meromorphicOrderAt s w hs ≠ ⊤} {hn' : meromorphicOrderAt F w hF ≠ ⊤} :
    meromorphicTrailingCoeffAt s w hn = meromorphicTrailingCoeffAt F w hn' :=
  hs.trailingCoeff_eq_of_eventuallyEq hF
    (.of_forall fun _ a _ ha hb ↦ (he a).symm.trans (congrArg F (ha.trans hb.symm)))

private theorem eval_mul_at {p q : MeromorphicSection (⊤ : Opens ℂ)} (x : (⊤ : Opens ℂ))
    (hp : x ∈ p.regularLocus) (hq : x ∈ q.regularLocus) (hpq : x ∈ (p * q).regularLocus) :
    (p * q).eval ⟨x, hpq⟩ = p.eval ⟨x, hp⟩ * q.eval ⟨x, hq⟩ := by
  exact map_mul (MeromorphicGerm.eval (z := (x : ℂ)))
    (⟨germ x p, hp⟩ : MeromorphicGerm.regularSubring (x : ℂ)) ⟨germ x q, hq⟩

private noncomputable def sectionLeadingUnit (x : ℂ) (u : (MeromorphicSection (⊤ : Opens ℂ))ˣ) :
    ℂˣ :=
  ((u.val.meromorphicOn_eval x (mem_univ x)).meromorphicTrailingCoeffAt_ne_zero
    (order_sectionUnit_ne_top u x)).isUnit.unit

private theorem val_sectionLeadingUnit (x : ℂ) (u : (MeromorphicSection (⊤ : Opens ℂ))ˣ) :
    (sectionLeadingUnit x u : ℂ) = meromorphicTrailingCoeffAt u.val.eval x
      (order_sectionUnit_ne_top u x) := IsUnit.unit_spec _

/-- The leading coefficient at a point is multiplicative on nonzero meromorphic sections.
It is computed on the regular scalar locus even when the point itself is a pole. -/
noncomputable def meromorphicLeadingUnit (x : ℂ) : (MeromorphicSection (⊤ : Opens ℂ))ˣ →* ℂˣ where
  toFun u := ((u.val.meromorphicOn_eval x (mem_univ x)).meromorphicTrailingCoeffAt_ne_zero
    (order_sectionUnit_ne_top u x)).isUnit.unit
  map_one' := by
    change sectionLeadingUnit x 1 = 1
    apply Units.ext
    rw [val_sectionLeadingUnit]
    let s := (1 : MeromorphicSection (⊤ : Opens ℂ))
    have hm := s.meromorphicOn_eval x (mem_univ x)
    have h₁ : meromorphicOrderAt (fun _ : ℂ ↦ (1 : ℂ)) x analyticAt_const.meromorphicAt ≠ ⊤ :=
      analyticAt_const.meromorphicOrderAt_ne_top_of_ne_zero one_ne_zero
    have ht := trailingCoeff_eq_of_rep hm analyticAt_const.meromorphicAt (F := fun _ ↦ 1)
      (hn := order_sectionUnit_ne_top 1 x) (hn' := h₁)
      (fun y ↦ (map_one (MeromorphicGerm.eval (z := (y.val : ℂ)))).symm)
    exact ht.trans (analyticAt_const.meromorphicTrailingCoeffAt_of_ne_zero one_ne_zero)
  map_mul' u v := by
    change sectionLeadingUnit x (u*v) = sectionLeadingUnit x u * sectionLeadingUnit x v
    let p := u.val
    let q := v.val
    obtain ⟨F, hF, hvF, hoF⟩ := exists_ambient_representative
      (Subtype.val_injective.comp Subtype.val_injective) p.meromorphicOn_eval
    obtain ⟨G, hG, hvG, hoG⟩ := exists_ambient_representative
      (Subtype.val_injective.comp Subtype.val_injective) q.meromorphicOn_eval
    have hx : x ∈ (⊤ : Opens ℂ) := mem_univ x
    have hF₀ := (hoF x hx).trans_ne (order_sectionUnit_ne_top u x)
    have hG₀ := (hoG x hx).trans_ne (order_sectionUnit_ne_top v x)
    have hFG : MeromorphicAt (F * G) x := (hF x hx).mul (hG x hx)
    have hFG₀ : meromorphicOrderAt (F * G) x hFG ≠ ⊤ := by
      rw [meromorphicOrderAt_mul (hF x hx) (hG x hx)]
      exact WithTop.add_ne_top.2 ⟨hF₀, hG₀⟩
    apply Units.ext
    rw [Units.val_mul, val_sectionLeadingUnit, val_sectionLeadingUnit, val_sectionLeadingUnit,
      trailingCoeff_eq_of_rep (p.meromorphicOn_eval x hx) (hF x hx) hvF (hn' := hF₀),
      trailingCoeff_eq_of_rep (q.meromorphicOn_eval x hx) (hG x hx) hvG (hn' := hG₀),
      ← MeromorphicAt.meromorphicTrailingCoeffAt_mul (hF x hx) (hG x hx) hF₀ hG₀ (h := hFG₀)]
    apply ((p*q).meromorphicOn_eval x hx).trailingCoeff_eq_of_eventuallyEq hFG
    filter_upwards [(p.meromorphicOn_eval x hx).1, (q.meromorphicOn_eval x hx).1]
      with t ⟨a, ha⟩ ⟨b, hb⟩
    rintro y z hy rfl
    have hpa : a.val = y.val := Subtype.ext (ha.trans hy.symm)
    have hqb : b.val = y.val := Subtype.ext (hb.trans hy.symm)
    change (p * q).eval y = F _ * G _
    have haF : F z = p.eval a := (congrArg F (show (a.val : ℂ) = z from ha).symm).trans (hvF a)
    have hbG : G z = q.eval b := (congrArg G (show (b.val : ℂ) = z from hb).symm).trans (hvG b)
    rw [haF, hbG]
    exact (eval_mul_at y.val (hpa ▸ a.property) (hqb ▸ b.property) y.property).trans
      (congrArg₂ (· * ·) (congrArg p.eval (Subtype.ext hpa.symm))
        (congrArg q.eval (Subtype.ext hqb.symm)))

/-- The leading unit of the disk product is a finite product of the leading units of its
individual factors with their prescribed signed multiplicities. -/
theorem meromorphicLeadingUnit_canonicalProduct
    (d : locallyFinsuppWithin (ball (0 : ℂ) R) ℤ) (hd : d.support.Finite) (x : ℂ) :
    meromorphicLeadingUnit x (canonicalProduct d hd) =
      ∏ u ∈ hd.toFinset.attach,
        let hu := d.supportWithinDomain (hd.mem_toFinset.mp u.property)
        (meromorphicLeadingUnit x (unit (canonicalFactor R u (pos_of_mem_ball hu).ne')
          (canonicalFactor_nonvanishing R u))) ^ (-d u) := by
  simp only [canonicalProduct, map_prod, map_zpow]

private theorem trailingCoeff_eq_normal_value {A : Type*} {c : A → ℂ} {s : A → E}
    (hs : MeromorphicNFAt s w c) {a : A} (ha : c a = w)
    (ho : meromorphicOrderAt s w hs.meromorphicAt = 0) :
    meromorphicTrailingCoeffAt s w (ho.trans_ne WithTop.zero_ne_top) = s a := by
  obtain ⟨F, hF, he⟩ := hs.mem_range_iff.mp ⟨a, ha⟩
  have hv := (hs.value_eq a ha).trans (hs.meromorphicAt.value_eq _ hF he)
  refine Eq.trans (hF.meromorphicTrailingCoeffAt_of_eq_nhdsNE hs.meromorphicAt _ ?_) hv.symm
  filter_upwards [he] with y hy
  intro hn
  have hs₀ : (meromorphicOrderAt s w hs.meromorphicAt).untop
      (ho.trans_ne WithTop.zero_ne_top) = (0 : ℤ) :=
    (WithTop.untop_eq_iff _).mpr ho
  rw [hs₀, zpow_zero₀, one_smul]
  exact hy

/-- In a disk of positive radius the leading value of the original function is the product
of the leading values of its interior and boundary factors and its analytic remainder. -/
theorem ECanonicalDecomp.eq_smul_meromorphicTrailingCoeffAt (D : ECanonicalDecomp f h R)
    (hw : w ∈ closedBall (0 : ℂ) R) (hR : 0 < R) :
    let b := divisor f (sphere (0 : ℂ) R) D.meromorphicOrderAt_ne_top_sphere
    let P := D.meromorphicOn.canonicalFactorProduct D.meromorphicOrderAt_ne_top
    let v := (FactorizedRational.leadingValue_ne_zero b divisor_sphere_support_finite w).isUnit.unit
    h w = (meromorphicLeadingUnit w P * v)⁻¹ •
      meromorphicTrailingCoeffAt f w (D.meromorphicOrderAt_ne_top w hw) := by
  let b := divisor f (sphere (0 : ℂ) R) D.meromorphicOrderAt_ne_top_sphere
  have hb : b.support.Finite := divisor_sphere_support_finite
  let P := D.meromorphicOn.canonicalFactorProduct D.meromorphicOrderAt_ne_top
  let q := FactorizedRational.eval b hb
  let v := (FactorizedRational.leadingValue_ne_zero b hb w).isUnit.unit
  let u := meromorphicLeadingUnit w P
  change h w = (u * v)⁻¹ • meromorphicTrailingCoeffAt f w _
  apply MulAction.injective (u * v)
  change (u * v) • h w = (u * v) • ((u * v)⁻¹ • meromorphicTrailingCoeffAt f w _)
  rw [smul_inv_smul]
  obtain ⟨F, hF, hvF, hoF⟩ := exists_ambient_representative
    (Subtype.val_injective.comp Subtype.val_injective) P.val.meromorphicOn_eval
  have hq : MeromorphicOn q univ Subtype.val :=
    (FactorizedRational.meromorphicNFOn hb univ).meromorphicOn
  obtain ⟨Q, hQ, hvQ, hoQ⟩ := exists_ambient_representative Subtype.val_injective hq
  have hF₀ := (hoF w (mem_univ w)).trans_ne (order_sectionUnit_ne_top P w)
  have hq₀ : meromorphicOrderAt q w (hq w (mem_univ w)) ≠ ⊤ :=
    (FactorizedRational.meromorphicOrderAt_eq hb w).trans_ne WithTop.coe_ne_top
  have hQ₀ := (hoQ w (mem_univ w)).trans_ne hq₀
  have hW : MeromorphicAt (F * Q) w := (hF w (mem_univ w)).mul (hQ w (mem_univ w))
  have hW₀ : meromorphicOrderAt (F * Q) w hW ≠ ⊤ := by
    rw [meromorphicOrderAt_mul (hF w (mem_univ w)) (hQ w (mem_univ w))]
    exact WithTop.add_ne_top.2 ⟨hF₀, hQ₀⟩
  have hh := D.analyticOnNhd w hw
  have hh₀ := hh.meromorphicOrderAt_ne_top_of_ne_zero (D.ne_zero w hw)
  have hprod : meromorphicOrderAt ((F * Q) • h) w (hW.smul hh.meromorphicAt) ≠ ⊤ := by
    rw [meromorphicOrderAt_smul hW hh.meromorphicAt]
    exact WithTop.add_ne_top.2 ⟨hW₀, hh₀⟩
  have he : f =ᶠ[𝓝[≠] w] (F * Q) • h := by
    apply (D.meromorphicOn w hw).eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect
      (hW.smul hh.meromorphicAt) hw
    · rw [← closure_ball _ hR.ne']
      exact isOpen_ball.perfect_closure.2
    · filter_upwards [D.eventuallyEq] with y ⟨hp, hd, hy⟩
      exact hy.trans (congrArg (· • h y) (congrArg₂ (· * ·)
        (hvF ⟨⟨y, mem_univ y⟩, hp⟩).symm (hvQ ⟨y, hd.ge⟩).symm))
  rw [meromorphicTrailingCoeffAt_congr_nhdsNE he (h₂ := hprod),
    hW.meromorphicTrailingCoeffAt_smul hh.meromorphicAt hW₀ hh₀,
    (hF w (mem_univ w)).meromorphicTrailingCoeffAt_mul (hQ w (mem_univ w)) hF₀ hQ₀,
    hh.meromorphicTrailingCoeffAt_of_ne_zero (D.ne_zero w hw),
    ← trailingCoeff_eq_of_rep (P.val.meromorphicOn_eval w (mem_univ w)) (hF w (mem_univ w))
      hvF (hn := order_sectionUnit_ne_top P w),
    ← trailingCoeff_eq_of_rep (hq w (mem_univ w)) (hQ w (mem_univ w)) hvQ (hn := hq₀),
    FactorizedRational.meromorphicTrailingCoeffAt_factorizedRational hb w]
  change ((u : ℂ) * (v : ℂ)) • h w = _
  rw [show (u : ℂ) = _ from val_sectionLeadingUnit w P, show (v : ℂ) = _ from IsUnit.unit_spec _]

/-- At a point of order zero a section takes values in the nonzero complex numbers. -/
noncomputable def _root_.MeromorphicSection.evalUnit {U : Opens ℂ} (s : MeromorphicSection U)
    (x : U) (ho : meromorphicOrderAt s.eval (x : ℂ) (s.meromorphicOn_eval x x.property) = 0) :
    ℂˣ :=
  let hr := (s.mem_regularLocus_iff_order_nonneg x).mpr ho.ge
  (((s.meromorphicNFOn_eval x.property).order_eq_zero_iff_value_ne_zero
    (y := ⟨x, hr⟩) rfl).mp ho).isUnit.unit

/-- The leading unit of an order-zero section is its ordinary nonzero scalar value. -/
theorem meromorphicLeadingUnit_eq_evalUnit (u : (MeromorphicSection (⊤ : Opens ℂ))ˣ) (x : ℂ)
    (ho : meromorphicOrderAt u.val.eval x (u.val.meromorphicOn_eval x (mem_univ x)) = 0) :
    meromorphicLeadingUnit x u = u.val.evalUnit ⟨x, mem_univ x⟩ ho := by
  apply Units.ext
  change (sectionLeadingUnit x u : ℂ) = _
  rw [val_sectionLeadingUnit]
  let p : (⊤ : Opens ℂ) := ⟨x, mem_univ x⟩
  let hr := (u.val.mem_regularLocus_iff_order_nonneg p).mpr ho.ge
  exact (trailingCoeff_eq_normal_value (u.val.meromorphicNFOn_eval p.property)
    (a := ⟨p, hr⟩) rfl ho).trans (IsUnit.unit_spec _).symm

/-- At a point where the original function has order zero, its interior factor is a unit
of the local analytic ring. -/
theorem ECanonicalDecomp.order_canonicalFactorProduct_of_order_zero (D : ECanonicalDecomp f h R)
    (hw : w ∈ closedBall (0 : ℂ) R) (ho : meromorphicOrderAt f w (D.meromorphicOn w hw) = 0) :
    let P := D.meromorphicOn.canonicalFactorProduct D.meromorphicOrderAt_ne_top
    meromorphicOrderAt P.val.eval w (P.val.meromorphicOn_eval w (mem_univ w)) = 0 := by
  dsimp only
  rw [MeromorphicSection.order_eval _ ⟨w, mem_univ w⟩, MeromorphicOn.canonicalFactorProduct,
    order_canonicalProduct_on_closedBall _ _ hw, divisor_apply_eq_zero ho, WithTop.coe_zero]

/-- At an order-zero point the extended decomposition can be evaluated with the ordinary
nonzero values of both the Blaschke product and the boundary rational function. -/
theorem ECanonicalDecomp.eq_smul_meromorphicTrailingCoeffAt_of_meromorphicOrderAt
    (D : ECanonicalDecomp f h R) (hw : w ∈ closedBall (0 : ℂ) R)
    (ho : meromorphicOrderAt f w (D.meromorphicOn w hw) = 0) (hR : 0 < R) :
    let b := divisor f (sphere (0 : ℂ) R) D.meromorphicOrderAt_ne_top_sphere
    let P := D.meromorphicOn.canonicalFactorProduct D.meromorphicOrderAt_ne_top
    let hb : b w = 0 := divisor_apply_eq_zero ho
    let v :=
      (FactorizedRational.eval_ne_zero divisor_sphere_support_finite ⟨w, hb.ge⟩ hb).isUnit.unit
    h w = (P.val.evalUnit ⟨w, mem_univ w⟩
      (D.order_canonicalFactorProduct_of_order_zero hw ho) * v)⁻¹ • meromorphicTrailingCoeffAt f w
        (D.meromorphicOrderAt_ne_top w hw) := by
  let b := divisor f (sphere (0 : ℂ) R) D.meromorphicOrderAt_ne_top_sphere
  have hB : b.support.Finite := divisor_sphere_support_finite
  have hb : b w = 0 := divisor_apply_eq_zero ho
  have hn : meromorphicOrderAt (FactorizedRational.eval b hB) w
      ((FactorizedRational.meromorphicNFOn hB univ (z := w) trivial).meromorphicAt) ≠ ⊤ :=
    (FactorizedRational.meromorphicOrderAt_eq hB w).trans_ne WithTop.coe_ne_top
  have he : (FactorizedRational.leadingValue_ne_zero b hB w).isUnit.unit =
      (FactorizedRational.eval_ne_zero hB ⟨w, hb.ge⟩ hb).isUnit.unit := by
    apply Units.ext
    rw [IsUnit.unit_spec, IsUnit.unit_spec,
      ← FactorizedRational.meromorphicTrailingCoeffAt_factorizedRational hB w (h := hn),
      FactorizedRational.meromorphicTrailingCoeffAt_factorizedRational_off_support hB hb]
  exact (D.eq_smul_meromorphicTrailingCoeffAt hw hR).trans (by
    rw [he, meromorphicLeadingUnit_eq_evalUnit _ _
      (D.order_canonicalFactorProduct_of_order_zero hw ho)])

private noncomputable def logNormUnit : ℂˣ →* Multiplicative ℝ where
  toFun u := Multiplicative.ofAdd (log ‖(u : ℂ)‖)
  map_one' := by change Multiplicative.ofAdd (log ‖(1 : ℂ)‖) = _; simp
  map_mul' u v := congrArg Multiplicative.ofAdd (by
    change log ‖(u : ℂ) * (v : ℂ)‖ = log ‖(u : ℂ)‖ + log ‖(v : ℂ)‖
    rw [norm_mul, log_mul (norm_ne_zero_iff.mpr u.ne_zero) (norm_ne_zero_iff.mpr v.ne_zero)])

private theorem log_norm_canonicalProduct_leading (d : locallyFinsuppWithin (ball (0 : ℂ) R) ℤ)
    (hd : d.support.Finite) (x : ℂ) :
    log ‖(meromorphicLeadingUnit x (canonicalProduct d hd) : ℂ)‖ =
      -∑ u ∈ hd.toFinset.attach,
        let hu := d.supportWithinDomain (hd.mem_toFinset.mp u.property)
        (d u : ℝ) * log ‖(meromorphicLeadingUnit x
          (unit (canonicalFactor R u (pos_of_mem_ball hu).ne')
          (canonicalFactor_nonvanishing R u)) : ℂ)‖ := by
  change (logNormUnit (meromorphicLeadingUnit x (canonicalProduct d hd))).toAdd = _
  rw [meromorphicLeadingUnit_canonicalProduct, map_prod, toAdd_prod,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro u _
  dsimp only
  rw [map_zpow, toAdd_zpow, zsmul_eq_mul, Int.cast_neg, neg_mul]
  rfl

/-- The log norm of the analytic remainder is the log norm of the leading coefficient of
the original function, corrected by the interior canonical factors and the boundary divisor.
Leading values make this identity valid at zeros and poles as well as at regular nonzero points. -/
theorem ECanonicalDecomp.log_norm_eq (D : ECanonicalDecomp f h R)
    (hw : w ∈ closedBall (0 : ℂ) R) (hR : 0 < R) :
    let d := divisor f (ball (0 : ℂ) R) D.meromorphicOrderAt_ne_top_ball
    let b := divisor f (sphere (0 : ℂ) R) D.meromorphicOrderAt_ne_top_sphere
    let hd : d.support.Finite := D.meromorphicOn.divisor_ball_support_finite
    log ‖h w‖ =
      (∑ u ∈ hd.toFinset.attach,
        let hu := d.supportWithinDomain (hd.mem_toFinset.mp u.property)
        (d u : ℝ) * log ‖(meromorphicLeadingUnit w
          (unit (canonicalFactor R u (pos_of_mem_ball hu).ne')
          (canonicalFactor_nonvanishing R u)) : ℂ)‖) -
        (∑ᶠ i, (b i : ℝ) * log ‖w - i‖) +
          log ‖meromorphicTrailingCoeffAt f w (D.meromorphicOrderAt_ne_top w hw)‖ := by
  let d := divisor f (ball (0 : ℂ) R) D.meromorphicOrderAt_ne_top_ball
  have hd : d.support.Finite := D.meromorphicOn.divisor_ball_support_finite
  let b := divisor f (sphere (0 : ℂ) R) D.meromorphicOrderAt_ne_top_sphere
  have hb : b.support.Finite := divisor_sphere_support_finite
  let u := meromorphicLeadingUnit w (canonicalProduct d hd)
  let v := (FactorizedRational.leadingValue_ne_zero b hb w).isUnit.unit
  have he : (u * v) • h w = meromorphicTrailingCoeffAt f w (D.meromorphicOrderAt_ne_top w hw) := by
    rw [D.eq_smul_meromorphicTrailingCoeffAt hw hR]
    exact smul_inv_smul _ _
  have hlog := congrArg (fun y : E ↦ log ‖y‖) he
  change log ‖((u : ℂ) * (v : ℂ)) • h w‖ = _ at hlog
  rw [norm_smul, norm_mul, log_mul (mul_ne_zero (norm_ne_zero_iff.mpr u.ne_zero)
      (norm_ne_zero_iff.mpr v.ne_zero)) (norm_ne_zero_iff.mpr (D.ne_zero w hw)),
    log_mul (norm_ne_zero_iff.mpr u.ne_zero) (norm_ne_zero_iff.mpr v.ne_zero),
    show (v : ℂ) = FactorizedRational.leadingValue b hb w from IsUnit.unit_spec _,
    FactorizedRational.log_norm_leadingValue, show log ‖(u : ℂ)‖ = _ from
      log_norm_canonicalProduct_leading d hd w] at hlog
  dsimp only
  linarith

/-- At an order-zero point, every interior factor in the log formula may be evaluated as
an ordinary complex number. The finite support omits the center of any factor with exponent zero. -/
theorem ECanonicalDecomp.log_norm_eq_of_order_zero (D : ECanonicalDecomp f h R)
    (hw : w ∈ closedBall (0 : ℂ) R) (ho : meromorphicOrderAt f w (D.meromorphicOn w hw) = 0)
    (hR : 0 < R) :
    let d := divisor f (ball (0 : ℂ) R) D.meromorphicOrderAt_ne_top_ball
    let b := divisor f (sphere (0 : ℂ) R) D.meromorphicOrderAt_ne_top_sphere
    let hd : d.support.Finite := D.meromorphicOn.divisor_ball_support_finite
    let hw₀ : d w = 0 := divisor_apply_eq_zero ho
    log ‖h w‖ =
      (∑ u ∈ hd.toFinset.attach,
        let hwu : w ≠ (u : ℂ) := fun e ↦ (hd.mem_toFinset.mp u.property) (e ▸ hw₀)
        (d u : ℝ) * log ‖(canonicalFactor R u hR.ne').eval
          ⟨⟨w, mem_univ w⟩, mem_regularLocus_canonicalFactor_of_ne hwu⟩‖) -
        (∑ᶠ i, (b i : ℝ) * log ‖w - i‖) +
          log ‖meromorphicTrailingCoeffAt f w (D.meromorphicOrderAt_ne_top w hw)‖ := by
  let d := divisor f (ball (0 : ℂ) R) D.meromorphicOrderAt_ne_top_ball
  have hd : d.support.Finite := D.meromorphicOn.divisor_ball_support_finite
  have hw₀ : d w = 0 := divisor_apply_eq_zero ho
  refine (D.log_norm_eq hw hR).trans ?_
  dsimp only
  apply congrArg (· + _)
  apply congrArg (· - _)
  apply Finset.sum_congr rfl
  intro u _
  have hu := d.supportWithinDomain (hd.mem_toFinset.mp u.property)
  have hwu : w ≠ (u : ℂ) := fun e ↦ (hd.mem_toFinset.mp u.property) (e ▸ hw₀)
  let s := canonicalFactor R u hR.ne'
  let v := unit s (canonicalFactor_nonvanishing R u)
  have hs : meromorphicOrderAt s.eval w (s.meromorphicOn_eval w (mem_univ w)) = 0 :=
    (s.order_eval ⟨w, mem_univ w⟩).trans
      ((order_canonicalFactor_on_closedBall hu hw).trans (ite_eq_right hwu))
  apply congrArg ((d u : ℝ) * ·)
  apply congrArg (fun z : ℂ ↦ log ‖z‖)
  exact (val_sectionLeadingUnit w v).trans
    (trailingCoeff_eq_normal_value (s.meromorphicNFOn_eval (mem_univ w))
      (a := ⟨⟨w, mem_univ w⟩, mem_regularLocus_canonicalFactor_of_ne hwu⟩) rfl hs)

end Complex
