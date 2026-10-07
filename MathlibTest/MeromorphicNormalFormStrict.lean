import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Meromorphic.NormalForm

/-!
# The normal-form conversions take meromorphy

`toMeromorphicNFAt f x hf` and `toMeromorphicNFOn f U hf` convert a function that is meromorphic at
`x`, respectively on `U`, to normal form, and `fun_prop` supplies the meromorphy proof by default.
The former zero function for a function that is not meromorphic is removed.
-/

/-- info: Unknown identifier `toMeromorphicNFAt_of_not_meromorphicAt` -/
#guard_msgs in
#check_failure toMeromorphicNFAt_of_not_meromorphicAt

/-- info: Unknown identifier `toMeromorphicNFOn_of_not_meromorphicOn` -/
#guard_msgs in
#check_failure toMeromorphicNFOn_of_not_meromorphicOn

/-! The default argument finds meromorphy in the context. -/

example {f : ℂ → ℂ} {x : ℂ} (hf : MeromorphicAt f x) :
    MeromorphicNFAt (toMeromorphicNFAt f x) x :=
  meromorphicNFAt_toMeromorphicNFAt

example {f : ℂ → ℂ} {U : Set ℂ} (hf : MeromorphicOn f U) :
    MeromorphicNFOn (toMeromorphicNFOn f U) U :=
  meromorphicNFOn_toMeromorphicNFOn f U

/-! Without meromorphy, the conversion cannot be formed. -/

/--
error: could not synthesize default value for parameter 'hf' using tactics
---
error: `fun_prop` was unable to prove `MeromorphicAt f x`

Issues:
  No theorems found for `f` in order to prove `MeromorphicAt (fun a => f a) x`
-/
#guard_msgs in
noncomputable example (f : ℂ → ℂ) (x : ℂ) : ℂ → ℂ := toMeromorphicNFAt f x

/-! A meromorphic function agrees with its normal form outside a discrete set. -/

example {f : ℂ → ℂ} {U : Set ℂ} (hf : MeromorphicOn f U) :
    f =ᶠ[Filter.codiscreteWithin U] toMeromorphicNFOn f U hf :=
  toMeromorphicNFOn_eqOn_codiscrete hf

example {f : ℂ → ℂ} {x : ℂ} (hf : MeromorphicAt f x) :
    meromorphicOrderAt (toMeromorphicNFAt f x hf) x = meromorphicOrderAt f x hf :=
  hf.meromorphicOrderAt_toMeromorphicNFAt
