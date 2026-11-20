module
import Mathlib

/-! Test that `simp` can prove some lemmas about derivatives. -/

open Real

@[local simp] private theorem deriv_real_fun_pow (f : ℝ → ℝ) (x : ℝ)
    (hf : DifferentiableAt ℝ f x id) (n : ℕ) :
    deriv (fun y ↦ f y ^ n) x id = n * f x ^ (n - 1) * deriv f x id := by
  simpa only [Pi.pow_def] using deriv_pow hf n

attribute [local simp] deriv_const_add_id

example : deriv Real.exp = Real.exp := by simp

example (x : ℝ) : fderivWithin ℝ (0 : ℝ → ℝ) (Set.Ici 0) x = 0 := by simp

example (x : ℝ) : deriv (fun x => cos x + 2 * sin x) x id = -sin x + 2 * cos x := by
  have h : DifferentiableAt ℝ (fun y ↦ (2 : ℝ) * sin y) x id := by fun_prop
  simp [h]

example (x : ℝ) :
    deriv (fun x ↦ cos (sin x) * exp x) x id = (cos (sin x) - sin (sin x) * cos x) * exp x := by
  simp
  ring

example (x : ℝ) : deriv (HAdd.hAdd (3 : ℝ)) x id = 1 := by
  simp

example (x : ℝ) : deriv (HSub.hSub (3 : ℝ)) x id = -1 := by
  simp

example (x : ℝ) : deriv (HMul.hMul (3 : ℝ)) x id = 3 := by
  simp

example (x : ℝˣ) :
    deriv (fun y : ℝˣ ↦ 3 /ₚ y) x (fun y ↦ (y : ℝ)) = -3 /ₚ (x ^ 2) := by
  simp

example (x : ℝ) : deriv (HPow.hPow (3 : ℝ)) x id = log 3 * 3 ^ x := by
  simp

example {x : ℝ} : deriv (fun x => (3 + x) * 2) x id = 2 := by
  simp

example {x : ℝ} : deriv (fun x => (3 - x) * 2) x id = -2 := by
  simp

example {x : ℝ} : deriv (fun x => (3 * x) * 2) x id = 6 := by
  simp
  ring

example (x : ℝˣ) :
    deriv (fun y : ℝˣ ↦ (3 /ₚ y) * 2) x (fun y ↦ (y : ℝ)) = -6 /ₚ (x ^ 2) := by
  have h := (((hasDerivAt_inv x).const_mul (3 : ℝ)).mul_const 2).deriv Units.isOpenEmbedding_val
  simp only [divp, ← inv_pow, Units.val_pow_eq_pow_val, h]
  ring

example {x : ℝ} : deriv (fun x => (3 ^ x : ℝ) * 2) x id = 2 * Real.log 3 * 3 ^ x := by
  simp
  ring

/- for more complicated examples (with more nested functions) you need to increase the
`maxDischargeDepth`. -/

example (x : ℝ) :
    deriv (fun x ↦ sin (sin (sin x)) + sin x) x id =
    cos (sin (sin x)) * (cos (sin x) * cos x) + cos x := by
  simp (maxDischargeDepth := 3)

example (x : ℝ) :
    deriv (fun x ↦ sin (sin (sin x)) ^ 10 + sin x) x id =
    10 * sin (sin (sin x)) ^ 9 * (cos (sin (sin x)) * (cos (sin x) * cos x)) + cos x := by
  have h : DifferentiableAt ℝ (fun y ↦ sin (sin (sin y)) ^ (10 : ℕ)) x id := by fun_prop
  simp (maxDischargeDepth := 4) [h]
