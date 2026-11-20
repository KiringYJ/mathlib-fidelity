import Mathlib.Analysis.Complex.ValueDistribution.Cartan
import Mathlib.Analysis.Complex.ValueDistribution.FirstMainTheorem

/-!
# The proximity function takes the domain of the counting function

`ValueDistribution.proximity f a hf ha` is the proximity function of Nevanlinna theory.  It takes a
proof `hf` that `f` is meromorphic and, for a finite value `a`, a proof `ha` that `f` takes `a` on
no punctured neighborhood: the arguments of `ValueDistribution.logCounting` and of the
characteristic function, which is their sum.  For `a = ⊤` the condition `ha` holds for every
function and is supplied by default, so that the proximity function for the poles of a meromorphic
function is evaluated as `(proximity f ⊤) r`.  On this domain `f` takes a finite value `a` at only
finitely many points of each circle and the integrand is circle integrable.  A continuous function
that is not meromorphic, such as complex conjugation, cannot be given to `proximity`; the circle
average of `log⁺ ‖f ·‖` remains available for it.
-/

open Real ValueDistribution

/-! Without meromorphy, the proximity function cannot be formed. -/

/--
error: could not synthesize default value for parameter '_hf' using tactics
---
error: `fun_prop` was unable to prove `Meromorphic f id`

Issues:
  No theorems found for `f` in order to prove `Meromorphic (fun a => f a) id`
-/
#guard_msgs in
noncomputable example (f : ℂ → ℂ) : ℝ → ℝ := proximity f ⊤

/--
error: could not synthesize default value for parameter '_hf' using tactics
---
error: `fun_prop` was unable to prove `Meromorphic (⇑(starRingEnd ℂ)) id`

Issues:
  No theorems found for `starRingEnd` in order to prove `Meromorphic (fun a => (starRingEnd ℂ) a) id`
-/
#guard_msgs in
noncomputable example : ℝ → ℝ := proximity (starRingEnd ℂ) ⊤

/-! Both proofs precede the radius. -/

noncomputable example {f : ℂ → ℂ} (hf : Meromorphic f) (r : ℝ) : ℝ := (proximity f ⊤) r

/-! A finite value needs that `f` takes it on no punctured neighborhood. -/

/--
error: could not synthesize default value for parameter '_ha' using tactics
---
error: the function must take the value on no punctured neighborhood; only for ⊤ is this supplied by default
f : ℂ → ℂ
hf : Meromorphic f id
a : ℂ
⊢ ∀ (z : ℂ), ∃ᶠ (w : ℂ) in nhdsWithin z {z}ᶜ, ↑(f w) ≠ ↑a
-/
#guard_msgs in
noncomputable example {f : ℂ → ℂ} (hf : Meromorphic f) (a : ℂ) : ℝ := proximity f a hf (r := 1)

/-! Within the domain, the proximity function is the circle average of the integrand. -/

example {f : ℂ → ℂ} (hf : Meromorphic f) :
    proximity f ⊤ = circleAverage (log⁺ ‖f ·‖) 0 :=
  proximity_top

example {f : ℂ → ℂ} (hf : Meromorphic f) {a : ℂ}
    (ha : ∀ z, ∃ᶠ w in nhdsWithin z {z}ᶜ, (f w : WithTop ℂ) ≠ a) (r : ℝ) (hr : r ≠ 0) :
    proximity f a hf ha r = circleAverage (fun z ↦ max 0 (-log ‖f z - a‖)) 0 r :=
  proximity_coe (fun e ↦ (hr e).elim)

example {f : ℂ → ℂ} (hf : Meromorphic f) :
    proximity f ⊤ = circleAverage (log⁺ ‖f ·‖) 0 := rfl

/-! The logarithmic counting function and the characteristic function share the default argument
for the value. -/

/--
error: could not synthesize default value for parameter 'ha' using tactics
---
error: the function must take the value on no punctured neighborhood; only for ⊤ is this supplied by default
f : ℂ → ℂ
hf : Meromorphic f id
a : ℂ
⊢ ∀ (z : ℂ), ∃ᶠ (w : ℂ) in nhdsWithin z {z}ᶜ, ↑(f w) ≠ ↑a
-/
#guard_msgs in
noncomputable example {f : ℂ → ℂ} (hf : Meromorphic f) (a : ℂ) : ℝ → ℝ := logCounting f a

/--
error: could not synthesize default value for parameter 'ha' using tactics
---
error: the function must take the value on no punctured neighborhood; only for ⊤ is this supplied by default
f : ℂ → ℂ
hf : Meromorphic f id
a : ℂ
⊢ ∀ (z : ℂ), ∃ᶠ (w : ℂ) in nhdsWithin z {z}ᶜ, ↑(f w) ≠ ↑a
-/
#guard_msgs in
noncomputable example {f : ℂ → ℂ} (hf : Meromorphic f) (a : ℂ) : ℝ := characteristic f a hf (r := 1)

noncomputable example {f : ℂ → ℂ} (hf : Meromorphic f) : ℝ → ℝ :=
  logCounting f ⊤ + characteristic f ⊤

/-! On the domain, the value is taken at finitely many points of each circle and the integrand is
circle integrable, so the conventions of the integrand do not matter. -/

example {f : ℂ → ℂ} (hf : Meromorphic f) {a : ℂ}
    (ha : ∀ z, ∃ᶠ w in nhdsWithin z {z}ᶜ, (f w : WithTop ℂ) ≠ a) (r : ℝ) :
    (Metric.sphere (0 : ℂ) |r| ∩ {w | f w = a}).Finite :=
  finite_sphere_inter_setOf_eq hf ha r

example {f : ℂ → ℂ} (hf : Meromorphic f) (a : ℂ)
    (ha : ∀ z, ∃ᶠ w in nhdsWithin z {z}ᶜ, (f w : WithTop ℂ) ≠ a) (r : ℝ) :
    CircleIntegrableOn (fun z : {z : ℂ | f z ≠ a} ↦ log⁺ (Checked.inv ‖f z - a‖
      (norm_ne_zero_iff.mpr (sub_ne_zero.mpr z.property)).isUnit)) 0 r :=
  circleIntegrable_posLog_norm_sub_inv hf a ha r

/-! A target equal to the center value is inadmissible at radius zero, even for a nonconstant germ. -/

/--
error: could not synthesize default value for parameter 'hr' using tactics
---
error: at radius zero, the center value must differ from the target
f : ℂ → ℂ
hf : Meromorphic f id
ha : ∀ (z : ℂ), ∃ᶠ (w : ℂ) in nhdsWithin z {z}ᶜ, ↑(f w) ≠ ↑(f 0)
⊢ 0 = 0 → ↑(f 0) ≠ ↑(f 0)
-/
#guard_msgs in
noncomputable example (f : ℂ → ℂ) (hf : Meromorphic f)
    (ha : ∀ z, ∃ᶠ w in nhdsWithin z {z}ᶜ, (f w : WithTop ℂ) ≠ f 0) : ℝ :=
  proximity f (f 0) hf ha 0

/-! At radius zero a finite target requires a nonzero distance at the center. -/

example {f : ℂ → ℂ} (hf : Meromorphic f) : (proximity f ⊤) 0 = log⁺ ‖f 0‖ := proximity_top_eval_zero

example {f : ℂ → ℂ} (hf : Meromorphic f) {a : ℂ}
    (ha : ∀ z, ∃ᶠ w in nhdsWithin z {z}ᶜ, (f w : WithTop ℂ) ≠ a) (hn : f 0 ≠ a) :
    proximity f a hf ha 0 (fun _ ↦ WithTop.coe_injective.ne_iff.mpr hn) =
      log⁺ (Checked.inv ‖f 0 - a‖ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hn)).isUnit) :=
  proximity_coe_eval_zero hn

example {f : ℂ → ℂ} (hf : Meromorphic f) {a : WithTop ℂ}
    (ha : ∀ z, ∃ᶠ w in nhdsWithin z {z}ᶜ, (f w : WithTop ℂ) ≠ a)
    (r : ℝ) (hr : r = 0 → (f 0 : WithTop ℂ) ≠ a) :
    characteristic f a hf ha r hr = proximity f a hf ha r hr + logCounting f a hf ha r := rfl

example {f : ℂ → ℂ} (hf : Meromorphic f)
    (ha : ∀ z, ∃ᶠ w in nhdsWithin z {z}ᶜ, (f w : WithTop ℂ) ≠ 0) (r : ℝ) (hr : r ≠ 0) :
    proximity f 0 hf ha r = (2 * π)⁻¹ • intervalIntegral.integralSubtypeOn
      (fun θ : {θ : ℝ | f (circleMap 0 r θ) ≠ 0} ↦
        log⁺ ‖Checked.inv (f (circleMap 0 r θ.val)) θ.property.isUnit‖) 0 (2 * π) :=
  proximity_inv hf ha r fun h ↦ (hr h).elim

/-! An entire function has a continuous proximity function for the poles. -/

example : Continuous (proximity (fun z : ℂ ↦ z) ⊤) :=
  continuous_proximity_top continuous_id

example : Continuous (proximity (fun z : ℂ ↦ z) ⊤) := by
  fun_prop
