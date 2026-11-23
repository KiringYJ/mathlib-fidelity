import Mathlib.Analysis.Complex.ValueDistribution.Cartan
import Mathlib.Analysis.Complex.ValueDistribution.FirstMainTheorem

/-!
# The trailing coefficient takes finite order

`meromorphicTrailingCoeffAt f x h` is the trailing coefficient of a function `f` that is
meromorphic at `x`, where `h` proves that the order of `f` at `x` is finite. A function that
vanishes on a punctured neighborhood of `x` has order `⊤` there and no nonzero coefficient, so it
has no trailing coefficient. The first main theorem compares the pole and zero characteristics
for a function with finite order at the origin. Jensen's formula takes finite order at every point
of the disk, and Cartan's formula takes it at the center for `f - a` for every `a`.
-/

open Real ValueDistribution Filter
open scoped Topology

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

/-! The inverse on the unit locus of a function of finite order has finite order. -/

private lemma unitLocus_mem_nhdsNE (f : ℂ → ℂ) (x : ℂ) (hf : MeromorphicAt f x)
    (h : meromorphicOrderAt f x hf ≠ ⊤) :
    Set.range (Subtype.val : {z : ℂ // IsUnit (f z)} → ℂ) ∈ 𝓝[≠] x :=
  ((meromorphicOrderAt_ne_top_iff_eventually_ne_zero hf).mp h).mono
    fun z hz ↦ ⟨⟨z, hz.isUnit⟩, rfl⟩

example {f : ℂ → ℂ} {x : ℂ} (hf : MeromorphicAt f x) (h : meromorphicOrderAt f x hf ≠ ⊤) :
    ∃ hc : Set.range (Subtype.val : {z : ℂ // IsUnit (f z)} → ℂ) ∈ 𝓝[≠] x,
      meromorphicOrderAt (fun z : {z : ℂ // IsUnit (f z)} ↦ Checked.inv (f z.val) z.property)
        x (hf.inv (coord := id) hc) ≠ ⊤ := by
  have hc := unitLocus_mem_nhdsNE f x hf h
  refine ⟨hc, ?_⟩
  have hn : -meromorphicOrderAt f x hf ≠ ⊤ := by
    simpa only [ne_eq, LinearOrderedAddCommGroupWithTop.neg_eq_top] using h
  exact (meromorphicOrderAt_inv (coord := id) hf hc).trans_ne hn

example {f : ℂ → ℂ} {x : ℂ} (hf : MeromorphicAt f x) (h : meromorphicOrderAt f x hf ≠ ⊤)
    (hi : MeromorphicAt (fun z : {z : ℂ // IsUnit (f z)} ↦ Checked.inv (f z.val) z.property)
      x Subtype.val) (h' : meromorphicOrderAt _ x hi ≠ ⊤) :
    meromorphicTrailingCoeffAt _ x h' = Checked.inv (meromorphicTrailingCoeffAt f x h)
      (hf.meromorphicTrailingCoeffAt_ne_zero h).isUnit :=
  meromorphicTrailingCoeffAt_inv (f := f) (coord := id) hf h

/-! The first main theorem takes finite order at the origin. -/

private lemma frequently_coe_ne_zero_of_finite_order (f : ℂ → ℂ) (hf : Meromorphic f)
    (h₀ : meromorphicOrderAt f (0 : ℂ) (hf (0 : ℂ)) ≠ ⊤) :
    ∀ z : ℂ, ∃ᶠ w in 𝓝[≠] z, (f w : WithTop ℂ) ≠ 0 := fun z ↦
  (frequently_coe_ne_zero_iff (hf z)).2
    (hf.exists_meromorphicOrderAt_ne_top_iff_forall.1 ⟨0, h₀⟩ z)

example {f : ℂ → ℂ} {R : ℝ} (hf : Meromorphic f)
    (h₀ : meromorphicOrderAt f (0 : ℂ) (hf (0 : ℂ)) ≠ ⊤)
    (hR : R ≠ 0) :
    ∃ ha : ∀ z : ℂ, ∃ᶠ w in 𝓝[≠] z, (f w : WithTop ℂ) ≠ 0,
      characteristic f ⊤ hf (frequently_coe_ne_top f) R -
        characteristic f 0 hf ha R (fun e ↦ (hR e).elim) =
        Real.log ‖meromorphicTrailingCoeffAt f (0 : ℂ) h₀‖ := by
  have ha := frequently_coe_ne_zero_of_finite_order f hf h₀
  exact ⟨ha, characteristic_sub_characteristic_zero_of_ne_zero hf ha hR⟩

/-! A nonzero constant satisfies the domain of the qualitative first main theorem. -/

example :
    let f := fun _ : ℂ ↦ (1 : ℂ)
    let hf : Meromorphic f := by fun_prop
    let ha : ∀ z : ℂ, ∃ᶠ w in 𝓝[≠] z, (f w : WithTop ℂ) ≠ 0 :=
      fun _ ↦ .of_forall fun _ ↦ by simp [f]
    (fun r : Set.Ioi (0 : ℝ) ↦ characteristic f ⊤ hf (frequently_coe_ne_top f) r -
      characteristic f 0 hf ha r (fun e ↦ (r.property.ne' e).elim)) =O[comap Subtype.val atTop]
      (1 : Set.Ioi (0 : ℝ) → ℝ) :=
  isBigO_characteristic_sub_characteristic_zero _ _

/-! The zero function lies outside the domain of the zero characteristic, also at positive radius. -/

/--
error: could not synthesize default value for parameter 'ha' using tactics
---
error: the function must take the value on no punctured neighborhood; only for ⊤ is this supplied by default
⊢ ∀ (z : ℂ), ∃ᶠ (w : ℂ) in 𝓝[≠] z, ↑0 ≠ 0
-/
#guard_msgs in
noncomputable example : ℝ := characteristic (fun _ : ℂ ↦ (0 : ℂ)) 0 (r := 1)
  (hr := fun e ↦ (one_ne_zero e).elim)

example : MonotoneOn (characteristic (fun _ : ℂ ↦ (1 : ℂ)) ⊤) (Set.Ioi 0) :=
  characteristic_monotoneOn (by fun_prop)

/-! Cartan's formula takes finite order of `f - a` at the origin for every `a`. -/

example {f : ℂ → ℂ} {R : ℝ} (h : Meromorphic f)
    (hfin : ∀ a : ℂ, meromorphicOrderAt (f · - a) (0 : ℂ) (h.fun_sub (.const a) 0) ≠ ⊤)
    (hR : R ≠ 0) :
    (characteristic f ⊤ h) R = circleAverage (fun a ↦ logCounting f a h
        (frequently_coe_ne_of_meromorphicOrderAt_sub_ne_top h (hfin a)) R) 0 1
      + circleAverage (fun a ↦ Real.log ‖meromorphicTrailingCoeffAt (f · - a) 0 (hfin a)‖) 0 1 :=
  characteristic_top_eq_circleAverage_add_circleAverage h hfin hR
