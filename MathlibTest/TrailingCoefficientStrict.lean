import Mathlib.Analysis.Complex.ValueDistribution.Cartan
import Mathlib.Analysis.Complex.ValueDistribution.FirstMainTheorem

/-!
# The trailing coefficient takes finite order

`meromorphicTrailingCoeffAt f x h` is the trailing coefficient of a function `f` that is
meromorphic at `x`, where `h` proves that the order of `f` at `x` is finite. A function that
vanishes on a punctured neighborhood of `x` has order `⊤` there and no nonzero coefficient, so it
has no trailing coefficient. The first main theorem takes finite order at the center, Jensen's
formula takes it at every point of the disk, and Cartan's formula takes it at the center for
`f - a` for every `a`.
-/

open Real ValueDistribution

/-! The former values outside the domain are removed. -/

/-- info: Unknown identifier `meromorphicTrailingCoeffAt_of_not_MeromorphicAt` -/
#guard_msgs in
#check_failure meromorphicTrailingCoeffAt_of_not_MeromorphicAt

/-- info: Unknown constant `MeromorphicAt.meromorphicTrailingCoeffAt_of_order_eq_top` -/
#guard_msgs in
#check_failure MeromorphicAt.meromorphicTrailingCoeffAt_of_order_eq_top

/-! The trailing coefficient needs a proof that the order is finite. -/

/--
error: Type mismatch
  meromorphicTrailingCoeffAt f x
has type
  meromorphicOrderAt f x ?_ ≠ ⊤ → ℂ
but is expected to have type
  ℂ
-/
#guard_msgs in
example (f : ℂ → ℂ) (x : ℂ) : ℂ := meromorphicTrailingCoeffAt f x

/-! The zero function has infinite order and hence no trailing coefficient. -/

example (x : ℂ) : meromorphicOrderAt (fun _ : ℂ ↦ (0 : ℂ)) x = ⊤ := by
  classical
  simp [meromorphicOrderAt_const]

/-! Finiteness comes from the order API. -/

example (x : ℂ) :
    meromorphicTrailingCoeffAt (fun _ : ℂ ↦ (2 : ℂ)) x
      ((analyticAt_const (v := (2 : ℂ))).meromorphicOrderAt_ne_top_of_ne_zero two_ne_zero) = 2 :=
  meromorphicTrailingCoeffAt_const

example [DecidableEq ℂ] (x y : ℂ) :
    meromorphicTrailingCoeffAt (· - y) x meromorphicOrderAt_id_sub_const_ne_top =
      if x = y then 1 else x - y :=
  meromorphicTrailingCoeffAt_id_sub_const

example {f : ℂ → ℂ} {x : ℂ} (hf : MeromorphicAt f x) (h : meromorphicOrderAt f x hf ≠ ⊤) :
    meromorphicTrailingCoeffAt f x h ≠ 0 :=
  hf.meromorphicTrailingCoeffAt_ne_zero h

/-! The inverse of a function of finite order has finite order. -/

example {f : ℂ → ℂ} {x : ℂ} (hf : MeromorphicAt f x) (h : meromorphicOrderAt f x hf ≠ ⊤) :
    meromorphicOrderAt f⁻¹ x hf.inv ≠ ⊤ := by
  rwa [meromorphicOrderAt_inv hf, ne_eq, LinearOrderedAddCommGroupWithTop.neg_eq_top]

example {f : ℂ → ℂ} {x : ℂ} (hf : MeromorphicAt f x) (h : meromorphicOrderAt f x hf ≠ ⊤)
    (h' : meromorphicOrderAt f⁻¹ x hf.inv ≠ ⊤) :
    meromorphicTrailingCoeffAt f⁻¹ x h' = (meromorphicTrailingCoeffAt f x h)⁻¹ :=
  meromorphicTrailingCoeffAt_inv h

/-! The first main theorem takes finite order at the origin. -/

example {f : ℂ → ℂ} {R : ℝ} (hf : Meromorphic f) (h₀ : meromorphicOrderAt f 0 ≠ ⊤) (hR : R ≠ 0) :
    (characteristic f ⊤ hf) R - (characteristic f⁻¹ ⊤ hf.inv) R =
      Real.log ‖meromorphicTrailingCoeffAt f 0 h₀‖ :=
  characteristic_sub_characteristic_inv_of_ne_zero hf h₀ hR

/-! The qualitative first main theorem and the monotonicity of the characteristic function hold
for every meromorphic function, including the constants. -/

example : (characteristic (fun _ : ℂ ↦ (0 : ℂ)) ⊤ - characteristic (fun _ : ℂ ↦ (0 : ℂ))⁻¹ ⊤)
    =O[Filter.atTop] (1 : ℝ → ℝ) :=
  isBigO_characteristic_sub_characteristic_inv (by fun_prop)

example : MonotoneOn (characteristic (fun _ : ℂ ↦ (1 : ℂ)) ⊤) (Set.Ioi 0) :=
  characteristic_monotoneOn (by fun_prop)

/-! Cartan's formula takes finite order of `f - a` at the origin for every `a`. -/

example {f : ℂ → ℂ} {R : ℝ} (h : Meromorphic f) (hfin : ∀ a, meromorphicOrderAt (f · - a) 0 ≠ ⊤)
    (hR : R ≠ 0) :
    (characteristic f ⊤ h) R = circleAverage (fun a ↦ logCounting f a h
        (frequently_coe_ne_of_meromorphicOrderAt_sub_ne_top h (hfin a)) R) 0 1
      + circleAverage (fun a ↦ Real.log ‖meromorphicTrailingCoeffAt (f · - a) 0 (hfin a)‖) 0 1 :=
  characteristic_top_eq_circleAverage_add_circleAverage h hfin hR
