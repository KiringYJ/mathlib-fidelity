import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Meromorphic.NormalForm

/-!
# The normal-form conversions take meromorphy

`toMeromorphicNFAt f x hf` and `toMeromorphicNFOn f U hf` convert a function that is meromorphic at
`x`, respectively on `U`, to normal form, and `fun_prop` supplies the meromorphy proof by default.
At poles the normalized functions have no scalar argument in their domain.
-/

/-- info: Unknown identifier `toMeromorphicNFAt_of_not_meromorphicAt` -/
#guard_msgs in
#check_failure toMeromorphicNFAt_of_not_meromorphicAt

/-- info: Unknown identifier `toMeromorphicNFOn_of_not_meromorphicOn` -/
#guard_msgs in
#check_failure toMeromorphicNFOn_of_not_meromorphicOn

/-! The default argument finds meromorphy in the context. -/

example {f : ℂ → ℂ} {x : ℂ} (hf : MeromorphicAt f x) :
    MeromorphicNFAt (toMeromorphicNFAt f x) x Subtype.val :=
  meromorphicNFAt_toMeromorphicNFAt

example {f : ℂ → ℂ} {U : Set ℂ} (hf : MeromorphicOn f U) :
    MeromorphicNFOn (toMeromorphicNFOn f U) U Subtype.val :=
  meromorphicNFOn_toMeromorphicNFOn f U

example {f : ℂ → ℂ} {x : ℂ} (hf : MeromorphicAt f x) (hp : meromorphicOrderAt f x hf < 0) :
    x ∉ meromorphicNFAtDomain f x := fun hx ↦
  hp.not_ge (hf.meromorphicOrderAt_nonneg_iff.mpr (hx rfl))

example {f : ℂ → ℂ} {x : ℂ} (hf : AnalyticAt ℂ f x) :
    toMeromorphicNFAt f x hf.meromorphicAt ⟨x, fun _ ↦ ⟨f, hf, .refl _ _⟩⟩ = f x :=
  (toMeromorphicNFAt_apply_center hf.meromorphicAt _).trans
    (hf.meromorphicAt.value_eq _ hf (.refl _ _))

/-! Without meromorphy, the conversion cannot be formed. -/

/--
error: could not synthesize default value for parameter 'hf' using tactics
---
error: `fun_prop` was unable to prove `MeromorphicAt f x id`

Issues:
  No theorems found for `f` in order to prove `MeromorphicAt (fun a => f a) x id`
-/
#guard_msgs in
noncomputable example (f : ℂ → ℂ) (x : ℂ) : meromorphicNFAtDomain f x → ℂ := toMeromorphicNFAt f x

/-! A meromorphic function agrees with its normal form outside a discrete set. -/

example {f : ℂ → ℂ} {U : Set ℂ} (hf : MeromorphicOn f U) :
    ∀ᶠ y in Filter.codiscreteWithin U, ∃ h : y ∈ meromorphicNFOnDomain f U,
      f y = toMeromorphicNFOn f U hf ⟨y, h⟩ :=
  toMeromorphicNFOn_eqOn_codiscrete hf

example {f : ℂ → ℂ} {x : ℂ} (hf : MeromorphicAt f x) :
    meromorphicOrderAt (toMeromorphicNFAt f x hf) x meromorphicNFAt_toMeromorphicNFAt.meromorphicAt = meromorphicOrderAt f x hf :=
  meromorphicOrderAt_toMeromorphicNFAt hf
