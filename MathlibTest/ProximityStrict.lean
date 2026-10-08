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
error: `fun_prop` was unable to prove `Meromorphic f`

Issues:
  No theorems found for `f` in order to prove `Meromorphic fun a => f a`
-/
#guard_msgs in
noncomputable example (f : ℂ → ℂ) : ℝ → ℝ := proximity f ⊤

/--
error: could not synthesize default value for parameter '_hf' using tactics
---
error: `fun_prop` was unable to prove `Meromorphic ⇑(starRingEnd ℂ)`

Issues:
  No theorems found for `starRingEnd` in order to prove `Meromorphic fun a => (starRingEnd ℂ) a`
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
hf : Meromorphic f
a : ℂ
⊢ ∀ (z : ℂ), ∃ᶠ (w : ℂ) in nhdsWithin z {z}ᶜ, ↑(f w) ≠ ↑a
-/
#guard_msgs in
noncomputable example {f : ℂ → ℂ} (hf : Meromorphic f) (a : ℂ) : ℝ → ℝ := proximity f a

/-! Within the domain, the proximity function is the circle average of the integrand. -/

example {f : ℂ → ℂ} (hf : Meromorphic f) :
    proximity f ⊤ = circleAverage (log⁺ ‖f ·‖) 0 :=
  proximity_top

example {f : ℂ → ℂ} (hf : Meromorphic f) {a : ℂ}
    (ha : ∀ z, ∃ᶠ w in nhdsWithin z {z}ᶜ, (f w : WithTop ℂ) ≠ a) :
    proximity f a hf ha = circleAverage (log⁺ ‖f · - a‖⁻¹) 0 :=
  proximity_coe

-- The two cases of the value are definitional.
example {f : ℂ → ℂ} (hf : Meromorphic f) :
    proximity f ⊤ = circleAverage (log⁺ ‖f ·‖) 0 :=
  rfl

example {f : ℂ → ℂ} (hf : Meromorphic f) {a : ℂ}
    (ha : ∀ z, ∃ᶠ w in nhdsWithin z {z}ᶜ, (f w : WithTop ℂ) ≠ a) :
    proximity f a hf ha = circleAverage (log⁺ ‖f · - a‖⁻¹) 0 :=
  rfl

/-! The logarithmic counting function and the characteristic function share the default argument
for the value. -/

/--
error: could not synthesize default value for parameter 'ha' using tactics
---
error: the function must take the value on no punctured neighborhood; only for ⊤ is this supplied by default
f : ℂ → ℂ
hf : Meromorphic f
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
hf : Meromorphic f
a : ℂ
⊢ ∀ (z : ℂ), ∃ᶠ (w : ℂ) in nhdsWithin z {z}ᶜ, ↑(f w) ≠ ↑a
-/
#guard_msgs in
noncomputable example {f : ℂ → ℂ} (hf : Meromorphic f) (a : ℂ) : ℝ → ℝ := characteristic f a

noncomputable example {f : ℂ → ℂ} (hf : Meromorphic f) : ℝ → ℝ :=
  logCounting f ⊤ + characteristic f ⊤

/-! On the domain, the value is taken at finitely many points of each circle and the integrand is
circle integrable, so the conventions of the integrand do not matter. -/

example {f : ℂ → ℂ} (hf : Meromorphic f) {a : ℂ}
    (ha : ∀ z, ∃ᶠ w in nhdsWithin z {z}ᶜ, (f w : WithTop ℂ) ≠ a) (r : ℝ) :
    (Metric.sphere (0 : ℂ) |r| ∩ {w | f w = a}).Finite :=
  finite_sphere_inter_setOf_eq hf ha r

example {f : ℂ → ℂ} (hf : Meromorphic f) (a : ℂ) (r : ℝ) :
    CircleIntegrable (fun z ↦ log⁺ ‖f z - a‖⁻¹) 0 r :=
  circleIntegrable_posLog_norm_sub_inv hf a r

/-! At radius `0`, the proximity function is the integrand at the center. -/

example {f : ℂ → ℂ} (hf : Meromorphic f) : (proximity f ⊤) 0 = log⁺ ‖f 0‖ :=
  proximity_top_eval_zero

example {f : ℂ → ℂ} (hf : Meromorphic f) {a : ℂ}
    (ha : ∀ z, ∃ᶠ w in nhdsWithin z {z}ᶜ, (f w : WithTop ℂ) ≠ a) :
    proximity f a hf ha 0 = log⁺ ‖f 0 - a‖⁻¹ :=
  proximity_coe_eval_zero

/-! The characteristic function is the sum of the proximity function and the logarithmic counting
function, with the same arguments. -/

example {f : ℂ → ℂ} (hf : Meromorphic f) {a : WithTop ℂ}
    (ha : ∀ z, ∃ᶠ w in nhdsWithin z {z}ᶜ, (f w : WithTop ℂ) ≠ a) :
    characteristic f a hf ha = proximity f a hf ha + logCounting f a hf ha :=
  rfl

/-! The proximity function of `f⁻¹` at `⊤` is that of `f` at `0`. -/

example {f : ℂ → ℂ} (hf : Meromorphic f)
    (ha : ∀ z, ∃ᶠ w in nhdsWithin z {z}ᶜ, (f w : WithTop ℂ) ≠ 0) :
    proximity f⁻¹ ⊤ hf.inv = proximity f 0 hf ha :=
  proximity_inv hf ha

/-! An entire function has a continuous proximity function for the poles. -/

example : Continuous (proximity (fun z : ℂ ↦ z) ⊤) :=
  continuous_proximity_top continuous_id

example : Continuous (proximity (fun z : ℂ ↦ z) ⊤) := by
  fun_prop
