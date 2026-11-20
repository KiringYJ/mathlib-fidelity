/-
Copyright (c) 2024 Geoffrey Irving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Irving
-/
module

public import Mathlib.Analysis.Analytic.Composition
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Calculus.Deriv.ZPow
public import Mathlib.Analysis.Calculus.IteratedDeriv.ConvergenceOnBall
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# Various complex special functions are analytic

`log` is analytic on its slit plane by the analytic inverse theorem for `exp`.
The corresponding `cpow` is analytic there by composition.
-/

public section

open Complex Filter Set
open scoped Topology Nat

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f g : E → ℂ} {z : ℂ} {x : E} {s : Set E}

/-- `log` is analytic away from nonpositive reals -/
@[fun_prop]
theorem analyticAt_clog (m : z ∈ slitPlane) : AnalyticAt ℂ log z := by
  let u := (Complex.exp_ne_zero (log z)).isUnit.unit
  apply Complex.expOpenPartialHomeomorph.analyticAt_symm
    (i := ContinuousLinearEquiv.unitsEquivAut ℂ u) m analyticAt_cexp
  change fderiv ℂ Complex.exp (log z) = _
  rw [(Complex.hasDerivAt_exp (log z)).hasFDerivAt.fderiv]
  ext
  simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.unitsEquivAut_apply,
    ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, u, IsUnit.unit_spec]

/-- `log` is analytic away from nonpositive reals -/
@[fun_prop]
theorem AnalyticAt.clog (fa : AnalyticAt ℂ f x) (m : f x ∈ slitPlane) :
    AnalyticAt ℂ (fun z ↦ log (f z)) x :=
  (analyticAt_clog m).comp fa

theorem AnalyticWithinAt.clog (fa : AnalyticWithinAt ℂ f s x) (m : f x ∈ slitPlane) :
    AnalyticWithinAt ℂ (fun z ↦ log (f z)) s x :=
  (analyticAt_clog m).comp_analyticWithinAt fa

/-- `log` is analytic away from nonpositive reals -/
theorem AnalyticOnNhd.clog (fs : AnalyticOnNhd ℂ f s) (m : ∀ z ∈ s, f z ∈ slitPlane) :
    AnalyticOnNhd ℂ (fun z ↦ log (f z)) s :=
  fun z n ↦ (analyticAt_clog (m z n)).comp (fs z n)

theorem AnalyticOn.clog (fs : AnalyticOn ℂ f s) (m : ∀ z ∈ s, f z ∈ slitPlane) :
    AnalyticOn ℂ (fun z ↦ log (f z)) s :=
  fun z n ↦ (analyticAt_clog (m z n)).analyticWithinAt.comp (fs z n) m

/-- `f z ^ g z` is analytic if `f z` is not a nonpositive real -/
theorem AnalyticWithinAt.cpow (fa : AnalyticWithinAt ℂ f s x) (ga : AnalyticWithinAt ℂ g s x)
    (m : f x ∈ slitPlane) : AnalyticWithinAt ℂ (fun z ↦ f z ^ g z) s x := by
  have e : (fun z ↦ f z ^ g z) =ᶠ[𝓝[insert x s] x] fun z ↦ exp (log (f z) * g z) := by
    filter_upwards [(fa.continuousWithinAt_insert.eventually_ne (slitPlane_ne_zero m))]
    intro z fz
    simp only [fz, cpow_def, ite_false]
  apply AnalyticWithinAt.congr_of_eventuallyEq_insert _ e
  exact ((fa.clog m).mul ga).cexp

/-- `f z ^ g z` is analytic if `f z` is not a nonpositive real -/
@[fun_prop]
theorem AnalyticAt.cpow (fa : AnalyticAt ℂ f x) (ga : AnalyticAt ℂ g x)
    (m : f x ∈ slitPlane) : AnalyticAt ℂ (fun z ↦ f z ^ g z) x := by
  rw [← analyticWithinAt_univ] at fa ga ⊢
  exact fa.cpow ga m

/-- `f z ^ g z` is analytic if `f z` avoids nonpositive reals -/
theorem AnalyticOn.cpow (fs : AnalyticOn ℂ f s) (gs : AnalyticOn ℂ g s)
    (m : ∀ z ∈ s, f z ∈ slitPlane) : AnalyticOn ℂ (fun z ↦ f z ^ g z) s :=
  fun z n ↦ (fs z n).cpow (gs z n) (m z n)

/-- `f z ^ g z` is analytic if `f z` avoids nonpositive reals -/
theorem AnalyticOnNhd.cpow (fs : AnalyticOnNhd ℂ f s) (gs : AnalyticOnNhd ℂ g s)
    (m : ∀ z ∈ s, f z ∈ slitPlane) : AnalyticOnNhd ℂ (fun z ↦ f z ^ g z) s :=
  fun z n ↦ (fs z n).cpow (gs z n) (m z n)

section ReOfReal

variable {f : ℂ → ℂ} {s : Set ℝ} {x : ℝ}

@[fun_prop]
lemma AnalyticAt.re_ofReal (hf : AnalyticAt ℂ f x) :
    AnalyticAt ℝ (fun x : ℝ ↦ (f x).re) x :=
  (Complex.reCLM.analyticAt _).comp (hf.restrictScalars.comp (Complex.ofRealCLM.analyticAt _))

@[fun_prop]
lemma AnalyticAt.im_ofReal (hf : AnalyticAt ℂ f x) :
    AnalyticAt ℝ (fun x : ℝ ↦ (f x).im) x :=
  (Complex.imCLM.analyticAt _).comp (hf.restrictScalars.comp (Complex.ofRealCLM.analyticAt _))

lemma AnalyticWithinAt.re_ofReal (hf : AnalyticWithinAt ℂ f (ofReal '' s) x) :
    AnalyticWithinAt ℝ (fun x : ℝ ↦ (f x).re) s x :=
  ((Complex.reCLM.analyticWithinAt _ _).comp hf.restrictScalars (mapsTo_image f _)).comp
    (Complex.ofRealCLM.analyticWithinAt _ _) (mapsTo_image ofReal s)

lemma AnalyticWithinAt.im_ofReal (hf : AnalyticWithinAt ℂ f (ofReal '' s) x) :
    AnalyticWithinAt ℝ (fun x : ℝ ↦ (f x).im) s x :=
  ((Complex.imCLM.analyticWithinAt _ _).comp hf.restrictScalars (mapsTo_image f _)).comp
    (Complex.ofRealCLM.analyticWithinAt _ _) (mapsTo_image ofReal s)

lemma AnalyticOn.re_ofReal (hf : AnalyticOn ℂ f (ofReal '' s)) :
    AnalyticOn ℝ (fun x : ℝ ↦ (f x).re) s :=
  ((Complex.reCLM.analyticOn _).comp hf.restrictScalars (mapsTo_image f _)).comp
    (Complex.ofRealCLM.analyticOn _) (mapsTo_image ofReal s)

lemma AnalyticOn.im_ofReal (hf : AnalyticOn ℂ f (ofReal '' s)) :
    AnalyticOn ℝ (fun x : ℝ ↦ (f x).im) s :=
  ((Complex.imCLM.analyticOn _).comp hf.restrictScalars (mapsTo_image f _)).comp
    (Complex.ofRealCLM.analyticOn _) (mapsTo_image ofReal s)

lemma AnalyticOnNhd.re_ofReal (hf : AnalyticOnNhd ℂ f (ofReal '' s)) :
    AnalyticOnNhd ℝ (fun x : ℝ ↦ (f x).re) s :=
  ((Complex.reCLM.analyticOnNhd _).comp hf.restrictScalars (mapsTo_image f _)).comp
    (Complex.ofRealCLM.analyticOnNhd _) (mapsTo_image ofReal s)

lemma AnalyticOnNhd.im_ofReal (hf : AnalyticOnNhd ℂ f (ofReal '' s)) :
    AnalyticOnNhd ℝ (fun x : ℝ ↦ (f x).im) s :=
  ((Complex.imCLM.analyticOnNhd _).comp hf.restrictScalars (mapsTo_image f _)).comp
    (Complex.ofRealCLM.analyticOnNhd _) (mapsTo_image ofReal s)

end ReOfReal

section Real

variable {f : ℝ → ℝ} {s : Set ℝ} {x : ℝ}

@[fun_prop]
lemma analyticAt_log (hx : 0 < x) : AnalyticAt ℝ Real.log x := by
  have : Real.log = fun x : ℝ ↦ (Complex.log x).re := by ext x; exact (Complex.log_ofReal_re x).symm
  rw [this]
  refine AnalyticAt.re_ofReal <| analyticAt_clog ?_
  simp [hx]

lemma analyticOnNhd_log : AnalyticOnNhd ℝ Real.log (Set.Ioi 0) := fun _ hx ↦ analyticAt_log hx

lemma analyticOn_log : AnalyticOn ℝ Real.log (Set.Ioi 0) := analyticOnNhd_log.analyticOn

@[fun_prop]
lemma AnalyticAt.log (fa : AnalyticAt ℝ f x) (m : 0 < f x) :
    AnalyticAt ℝ (fun z ↦ Real.log (f z)) x :=
  (analyticAt_log m).comp fa

lemma AnalyticWithinAt.log (fa : AnalyticWithinAt ℝ f s x) (m : 0 < f x) :
    AnalyticWithinAt ℝ (fun z ↦ Real.log (f z)) s x :=
  (analyticAt_log m).comp_analyticWithinAt fa

lemma AnalyticOnNhd.log (fs : AnalyticOnNhd ℝ f s) (m : ∀ x ∈ s, 0 < f x) :
    AnalyticOnNhd ℝ (fun z ↦ Real.log (f z)) s :=
  fun z n ↦ (analyticAt_log (m z n)).comp (fs z n)

lemma AnalyticOn.log (fs : AnalyticOn ℝ f s) (m : ∀ x ∈ s, 0 < f x) :
    AnalyticOn ℝ (fun z ↦ Real.log (f z)) s :=
  fun z n ↦ (analyticAt_log (m z n)).analyticWithinAt.comp (fs z n) m

/-- The higher derivatives of the logarithm on its slit plane. -/
theorem iteratedDeriv_succ_log {n : ℕ} (x : slitPlane) :
    HasIteratedDerivAt (n + 1) (fun z : slitPlane ↦ log z)
      ((-1 : ℂ) ^ n * n.factorial *
        Checked.zpow (x : ℂ) (-(n : ℤ) - 1) (fun _ ↦ (slitPlane_ne_zero x.property).isUnit))
      x Subtype.val := by
  let u (z : slitPlane) : ℂˣ := (slitPlane_ne_zero z.property).isUnit.unit
  let g (z : slitPlane) : ℂ := ↑((u z)⁻¹)
  have hu : Continuous u := Units.isOpenEmbedding_val.isEmbedding.isInducing.continuous_iff.mpr
    (by simpa only [u, Function.comp_def, IsUnit.unit_spec] using continuous_subtype_val)
  have hder (z : slitPlane) : HasDerivAt (fun z : slitPlane ↦ log z) (g z) z Subtype.val := by
    have hz : (z : ℂ) ≠ 0 := slitPlane_ne_zero z.property
    have h : HasFDerivAt (fun z : slitPlane ↦ log z)
        (ContinuousLinearMap.toSpanSingleton ℂ ((z : ℂ)⁻¹)) z Subtype.val :=
      (Complex.hasDerivAt_log z.property).hasFDerivAt.comp_tendsto Subtype.val
        (continuous_subtype_val.continuousAt.tendsto.prodMap (tendsto_pure_pure ..))
    simpa only [g, u, Units.val_inv_eq_inv_val₀, IsUnit.unit_spec,
      ContinuousLinearMap.toSpanSingleton_apply, one_smul]
      using h.hasDerivAt
  refine ⟨g, hder x, Or.inr (Eventually.of_forall hder), ?_⟩
  have h := (hasIteratedDerivAt_inv n (u x)).comp_domain hu
  have hn : -1 - (n : ℤ) = -(n : ℤ) - 1 := by omega
  simpa only [g, u, Function.comp_def, IsUnit.unit_spec, hn,
    ← IsUnit.zpow_eq_val_unit_zpow] using h

/-- The degree-zero coefficient of the series for `log (1 + x)` is zero. The coefficient
in degree `n + 1` is `(-1)^n / (n + 1)`. -/
noncomputable def logSeriesCoefficient {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜] (n : ℕ) : 𝕜 :=
  match n with
  | 0 => 0
  | k + 1 => (-1) ^ k / (k + 1)

theorem hasFPowerSeriesAt_clog_one :
    HasFPowerSeriesAt log (.ofScalars (𝕜 := ℂ) ℂ logSeriesCoefficient) 1 := by
  obtain ⟨p, hp⟩ := analyticAt_clog one_mem_slitPlane
  let x : slitPlane := ⟨1, one_mem_slitPlane⟩
  have hpx := hp.comp_domain (g := Subtype.val) (x := x)
  have hcoeff (n : ℕ) : p.coeff n = logSeriesCoefficient n := by
    cases n with
    | zero =>
        exact (hp.coeff_zero (1 : Fin 0 → ℂ)).trans log_one
    | succ n =>
        have hj := hpx.hasIteratedDerivAt_coeff continuous_subtype_val (n + 1)
        have h := hj.unique (iteratedDeriv_succ_log (n := n) x)
          isOpen_slitPlane.isOpenEmbedding_subtypeVal
        have hn : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
        change p.coeff (n + 1) = (-1 : ℂ) ^ n / (n + 1)
        apply eq_div_iff.mpr
        apply mul_right_cancel₀ hn
        simpa only [x, Subtype.coe_mk, one_zpow₀, mul_one, one_mul, ← Nat.cast_smul_eq_nsmul ℂ,
          smul_eq_mul, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
          mul_assoc, mul_comm, mul_left_comm] using h
  have he : p = FormalMultilinearSeries.ofScalars ℂ logSeriesCoefficient := by
    refine FormalMultilinearSeries.ext fun n ↦ ?_
    rw [← ContinuousMultilinearMap.mkPiRing_apply_one_eq_self (p n),
      ← ContinuousMultilinearMap.mkPiRing_apply_one_eq_self
        (FormalMultilinearSeries.ofScalars ℂ logSeriesCoefficient n)]
    have h := (hcoeff n).trans FormalMultilinearSeries.coeff_ofScalars.symm
    exact congrArg (ContinuousMultilinearMap.mkPiRing ℂ (Fin n)) h
  exact he ▸ hp

theorem hasFPowerSeriesAt_clog_one_add :
    HasFPowerSeriesAt (fun x ↦ log (1 + x)) (.ofScalars (𝕜 := ℂ) ℂ logSeriesCoefficient) 0 := by
  convert HasFPowerSeriesAt.comp_sub hasFPowerSeriesAt_clog_one (-1) using 3 <;> ring

private lemma ofReal_logSeriesCoefficient (n : ℕ) :
    (logSeriesCoefficient (𝕜 := ℝ) n : ℂ) = logSeriesCoefficient (𝕜 := ℂ) n := by
  cases n <;> simp [logSeriesCoefficient, Complex.ofReal_div]

theorem hasFPowerSeriesAt_log_one :
    HasFPowerSeriesAt Real.log (.ofScalars (𝕜 := ℝ) ℝ logSeriesCoefficient) 1 := by
  obtain ⟨r, hp⟩ := hasFPowerSeriesAt_clog_one
  have h : HasFPowerSeriesOnBall log
      ((FormalMultilinearSeries.ofScalars (𝕜 := ℂ) ℂ logSeriesCoefficient).restrictScalars ℝ)
      (ofRealCLM 1) r := by
    simpa using hp.restrictScalars
  convert ((reCLM.comp_hasFPowerSeriesOnBall h.compContinuousLinearMap).congr
    (fun x _ ↦ log_ofReal_re x)).hasFPowerSeriesAt
  ext n
  simp only [ContinuousLinearMap.compFormalMultilinearSeries_apply,
    ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
    FormalMultilinearSeries.compContinuousLinearMap_apply]
  simp [← ofReal_logSeriesCoefficient]

theorem hasFPowerSeriesAt_log_one_add :
    HasFPowerSeriesAt (fun x ↦ Real.log (1 + x))
      (.ofScalars (𝕜 := ℝ) ℝ logSeriesCoefficient) 0 := by
  convert HasFPowerSeriesAt.comp_sub hasFPowerSeriesAt_log_one (-1) using 3 <;> ring

end Real
