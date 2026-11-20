/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Meromorphic.Germ

/-!
# Order of a meromorphic germ

The order of a fraction of analytic germs is the order of its numerator minus the finite
order of its denominator. The zero germ has infinite order.
-/

@[expose] public noncomputable section

open Filter
open scoped Topology

namespace AnalyticGerm

variable {z : ℂ}

/-- The vanishing order of an analytic germ. -/
def order (a : AnalyticGerm z) : ℕ∞ :=
  analyticOrderAt a.property.choose z a.property.choose_spec.1

@[simp] theorem order_ofFun (f : ℂ → ℂ) (hf : AnalyticAt ℂ f z) :
    order (ofFun f hf) = analyticOrderAt f z hf :=
  analyticOrderAt_congr _ (Germ.coe_eq.mp (ofFun f hf).property.choose_spec.2)

theorem order_eq_top_iff (a : AnalyticGerm z) : order a = ⊤ ↔ a = 0 := by
  obtain ⟨f, hf, he⟩ := a.property
  obtain rfl : a = ofFun f hf := Subtype.ext he.symm
  rw [order_ofFun, analyticOrderAt_eq_top hf]
  exact (ofFun_eq_iff (hf := hf) (hg := analyticAt_const (v := (0 : ℂ)))).symm

theorem order_eq_zero_iff (a : AnalyticGerm z) : order a = 0 ↔ eval a ≠ 0 := by
  obtain ⟨f, hf, he⟩ := a.property
  obtain rfl : a = ofFun f hf := Subtype.ext he.symm
  rw [order_ofFun, eval_ofFun, hf.analyticOrderAt_eq_zero]

@[simp] theorem order_mul (a b : AnalyticGerm z) : order (a * b) = order a + order b := by
  obtain ⟨f, hf, he⟩ := a.property
  obtain ⟨g, hg, he'⟩ := b.property
  obtain rfl : a = ofFun f hf := Subtype.ext he.symm
  obtain rfl : b = ofFun g hg := Subtype.ext he'.symm
  rw [← ofFun_mul, order_ofFun, order_ofFun, order_ofFun, analyticOrderAt_mul]

@[simp] theorem order_coordinate_pow (n : ℕ) : order (coordinate z ^ n) = n := by
  change order (ofFun ((· - z) ^ n) ((analyticAt_id.sub analyticAt_const).pow n)) = n
  rw [order_ofFun, analyticOrderAt_centeredMonomial]

/-- An analytic germ of finite order is the corresponding power of the local
coordinate times an analytic unit. -/
theorem exists_unit_of_order_eq {a : AnalyticGerm z} {n : ℕ} (h : a.order = n) :
    ∃ u : (AnalyticGerm z)ˣ, a = coordinate z ^ n * u := by
  obtain ⟨f, hf, he⟩ := a.property
  obtain rfl : a = ofFun f hf := Subtype.ext he.symm
  rw [order_ofFun] at h
  obtain ⟨g, hg, hn, hfg⟩ := hf.analyticOrderAt_eq_natCast.mp h
  let u := ((isUnit_iff_eval_ne_zero (ofFun g hg)).mpr hn).unit
  refine ⟨u, ?_⟩
  rw [show (u : AnalyticGerm z) = ofFun g hg from IsUnit.unit_spec _]
  have hc : AnalyticAt ℂ (fun y ↦ y - z) z := analyticAt_id.sub analyticAt_const
  exact (ofFun_eq_iff (hf := hf) (hg := (hc.pow n).mul hg)).mpr hfg

end AnalyticGerm

namespace MeromorphicGerm

variable {z : ℂ}

/-- The integer order of a meromorphic germ, with infinite order for the zero germ. -/
def order (s : MeromorphicGerm z) : WithTop ℤ :=
  Localization.liftOn s
    (fun a b ↦ a.order.map (↑· : ℕ → ℤ) - (b : AnalyticGerm z).order.map (↑· : ℕ → ℤ)) (by
      intro a c b d h
      have he := (Localization.r_iff_of_le_nonZeroDivisors le_rfl a c b d).mp h
      have hb := mem_nonZeroDivisors_iff_ne_zero.mp b.property
      have hd := mem_nonZeroDivisors_iff_ne_zero.mp d.property
      obtain ⟨nb, hnb⟩ := ENat.ne_top_iff_exists.mp (mt (AnalyticGerm.order_eq_top_iff _).mp hb)
      obtain ⟨nd, hnd⟩ := ENat.ne_top_iff_exists.mp (mt (AnalyticGerm.order_eq_top_iff _).mp hd)
      by_cases ha : a = 0
      · have hc : c = 0 := (mul_eq_zero.mp (by simpa [ha] using he.symm)).resolve_left hb
        rw [ha, hc, (AnalyticGerm.order_eq_top_iff _).mpr rfl, ← hnb, ← hnd]
        simp
      · have hc : c ≠ 0 := fun hc ↦ mul_ne_zero ha hd (by simpa [hc] using he)
        obtain ⟨na, hna⟩ := ENat.ne_top_iff_exists.mp (mt (AnalyticGerm.order_eq_top_iff _).mp ha)
        obtain ⟨nc, hnc⟩ := ENat.ne_top_iff_exists.mp (mt (AnalyticGerm.order_eq_top_iff _).mp hc)
        have ho := congrArg AnalyticGerm.order he
        simp only [AnalyticGerm.order_mul, ← hna, ← hnb, ← hnc, ← hnd, ← Nat.cast_add,
          Nat.cast_inj] at ho
        simp only [← hna, ← hnb, ← hnc, ← hnd, ENat.map_natCast]
        exact congrArg ((↑) : ℤ → WithTop ℤ) (show (na : ℤ) - nb = nc - nd by omega))

/-- The order of an analytic fraction is independent of its presentation. -/
theorem order_div (a b : AnalyticGerm z) (hb : b ≠ 0) :
    order (Checked.div (ofAnalytic a) (ofAnalytic b) (ofAnalytic_ne_zero.mpr hb).isUnit) =
      a.order.map (↑· : ℕ → ℤ) - b.order.map (↑· : ℕ → ℤ) := by
  let d : nonZeroDivisors (AnalyticGerm z) := ⟨b, mem_nonZeroDivisors_iff_ne_zero.mpr hb⟩
  exact (congrArg order (FractionRing.mk_eq_div (r := a) (s := d))).symm

open WithTop.LinearOrderedAddCommGroup

private theorem order_mk (a : AnalyticGerm z) (b : nonZeroDivisors (AnalyticGerm z)) :
    order (Localization.mk a b) = a.order.map (↑· : ℕ → ℤ) -
      (b : AnalyticGerm z).order.map (↑· : ℕ → ℤ) := by
  rw [FractionRing.mk_eq_div]
  exact order_div a b (mem_nonZeroDivisors_iff_ne_zero.mp b.property)

@[simp] theorem order_mul (p q : MeromorphicGerm z) : order (p * q) = order p + order q := by
  induction p, q using Localization.induction_on₂ with
  | H a b =>
    obtain ⟨a, c⟩ := a
    obtain ⟨b, d⟩ := b
    rw [Localization.mk_mul, order_mk, order_mk, order_mk]
    have hf (s : nonZeroDivisors (AnalyticGerm z)) : (s : AnalyticGerm z).order ≠ ⊤ :=
      mt (AnalyticGerm.order_eq_top_iff _).mp (mem_nonZeroDivisors_iff_ne_zero.mp s.property)
    obtain ⟨i, hi⟩ := ENat.ne_top_iff_exists.mp (hf c)
    obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.mp (hf d)
    simp only [Submonoid.coe_mul, AnalyticGerm.order_mul, ← hi, ← hj]
    cases a.order with
    | top => cases b.order <;> simp only [top_add, ENat.map_top, top_sub]
    | coe n =>
      cases b.order with
      | top => simp only [add_top, ENat.map_top, top_sub]
      | coe m =>
        simp only [← Nat.cast_add, ENat.map_natCast]
        exact congrArg ((↑) : ℤ → WithTop ℤ)
          (show ((n + m : ℕ) : ℤ) - ((i + j : ℕ) : ℤ) = (n : ℤ) - i + ((m : ℤ) - j) by omega)
@[simp] theorem order_one : order (1 : MeromorphicGerm z) = 0 := by
  have h := order_div (1 : AnalyticGerm z) 1 one_ne_zero
  have ho : (1 : AnalyticGerm z).order = 0 :=
    (AnalyticGerm.order_eq_zero_iff _).mpr (by simp)
  simpa only [map_one, div_one₀, ho, ENat.map_zero, Nat.cast_zero, WithTop.coe_zero,
    sub_zero] using h

@[simp] theorem order_unit_inv (u : (MeromorphicGerm z)ˣ) :
    order (↑u⁻¹ : MeromorphicGerm z) = -order (↑u : MeromorphicGerm z) := by
  have h := order_mul (↑u : MeromorphicGerm z) ↑u⁻¹
  rw [show (↑u : MeromorphicGerm z) * ↑u⁻¹ = 1 from u.val_inv, order_one] at h
  cases h₁ : order (↑u : MeromorphicGerm z) <;> cases h₂ : order (↑u⁻¹ : MeromorphicGerm z) <;>
    simp [h₁, h₂, ← WithTop.coe_add, ← coe_neg] at h ⊢
  omega

@[simp] theorem order_pow (p : MeromorphicGerm z) (n : ℕ) : order (p ^ n) = n • order p := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, order_mul, ih, succ_nsmul]

/-- The order of an integer power of a nonzero germ is the exponent times its order. -/
theorem order_unit_zpow (u : (MeromorphicGerm z)ˣ) (n : ℤ) :
    order (↑(u ^ n) : MeromorphicGerm z) = n * order (↑u : MeromorphicGerm z) := by
  have hu : order (↑u : MeromorphicGerm z) ≠ ⊤ := by
    intro ht
    have h := order_mul (↑u : MeromorphicGerm z) ↑u⁻¹
    rw [show (↑u : MeromorphicGerm z) * ↑u⁻¹ = 1 from u.val_inv, order_one, ht, top_add] at h
    exact WithTop.zero_ne_top h
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hu
  cases n with
  | ofNat k =>
    simp only [Int.ofNat_eq_natCast, zpow_natCast, Units.val_pow_eq_pow_val, order_pow, ← hm]
    exact congrArg ((↑) : ℤ → WithTop ℤ) (nsmul_eq_mul k m)
  | negSucc k =>
    rw [zpow_negSucc, order_unit_inv, Units.val_pow_eq_pow_val, order_pow, ← hm]
    exact congrArg ((↑) : ℤ → WithTop ℤ)
      (show -((k + 1) • m) = (Int.negSucc k : ℤ) * m by simp [Int.negSucc_eq]; ring)

/-- The analytic image of the field of meromorphic germs is precisely the valuation ring
of germs of nonnegative order. -/
theorem mem_regularSubring_iff_order_nonneg (q : MeromorphicGerm z) :
    q ∈ regularSubring z ↔ 0 ≤ order q := by
  induction q using Localization.induction_on with
  | H p =>
    obtain ⟨a, b⟩ := p
    have hb := mem_nonZeroDivisors_iff_ne_zero.mp b.property
    rw [FractionRing.mk_eq_div]
    let q := Checked.div (ofAnalytic a) (ofAnalytic b) (ofAnalytic_ne_zero.mpr hb).isUnit
    change q ∈ regularSubring z ↔ 0 ≤ order q
    dsimp only [q]
    rw [order_div a b hb]
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (mt (AnalyticGerm.order_eq_top_iff _).mp hb)
    constructor
    · rintro ⟨c, hc⟩
      have he : c * b = a := ofAnalytic_injective (by rw [map_mul]; exact eq_div_iff.mp hc)
      rw [← he, AnalyticGerm.order_mul, ← hm]
      cases c.order with
      | top => simp
      | coe n =>
        simp only [← Nat.cast_add, ENat.map_natCast]
        exact_mod_cast (by omega : (0 : ℤ) ≤ (n + m : ℕ) - (m : ℤ))
    · intro h
      by_cases ha : a = 0
      · subst a
        simpa only [map_zero, zero_div] using (regularSubring z).zero_mem
      obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (mt (AnalyticGerm.order_eq_top_iff _).mp ha)
      have hmn : m ≤ n := by
        rw [← hn, ← hm, ENat.map_natCast, ENat.map_natCast] at h
        exact_mod_cast (show (m : ℤ) ≤ n from sub_nonneg.mp (by exact_mod_cast h))
      obtain ⟨u, hu⟩ := AnalyticGerm.exists_unit_of_order_eq hn.symm
      obtain ⟨v, hv⟩ := AnalyticGerm.exists_unit_of_order_eq hm.symm
      refine ⟨AnalyticGerm.coordinate z ^ (n - m) * u * (↑v⁻¹ : AnalyticGerm z), eq_div_iff.mpr ?_⟩
      rw [← map_mul]
      apply congrArg ofAnalytic
      rw [hu, hv]
      calc
        _ = (AnalyticGerm.coordinate z ^ (n - m) * AnalyticGerm.coordinate z ^ m) * u *
            ((↑v⁻¹ : AnalyticGerm z) * v) := by ac_rfl
        _ = _ := by rw [show (↑v⁻¹ : AnalyticGerm z) * v = 1 from v.inv_val, mul_one,
          ← pow_add, Nat.sub_add_cancel hmn]

end MeromorphicGerm
