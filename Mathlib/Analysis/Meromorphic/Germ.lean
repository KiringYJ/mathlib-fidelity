/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module

public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Topology.Germ

/-!
# Analytic and meromorphic germs

Analytic germs at a complex point form an integral domain. Its fraction field is the
field of meromorphic germs: denominators must be nonzero as germs, but may vanish at
the base point. The analytic image is the subring of regular germs, and evaluation
at the base point is defined only on this subring.
-/

@[expose] public section

open Filter
open scoped Topology

noncomputable section

/-- The subring of germs represented by a function analytic at the base point. -/
def analyticGermSubring (z : ℂ) : Subring (Germ (𝓝 z) ℂ) where
  carrier := {g | ∃ f : ℂ → ℂ, AnalyticAt ℂ f z ∧ (f : Germ (𝓝 z) ℂ) = g}
  zero_mem' := ⟨0, analyticAt_const, rfl⟩
  one_mem' := ⟨1, analyticAt_const, rfl⟩
  add_mem' := by
    rintro a b ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f + g, hf.add hg, rfl⟩
  mul_mem' := by
    rintro a b ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f * g, hf.mul hg, rfl⟩
  neg_mem' := by
    rintro a ⟨f, hf, rfl⟩
    exact ⟨-f, hf.neg, rfl⟩

/-- The ring of analytic germs at a complex point. -/
abbrev AnalyticGerm (z : ℂ) : Type := ↥(analyticGermSubring z)

namespace AnalyticGerm

variable {z : ℂ}

/-- The germ of an analytic function. -/
def ofFun (f : ℂ → ℂ) (hf : AnalyticAt ℂ f z) : AnalyticGerm z :=
  ⟨(f : Germ (𝓝 z) ℂ), f, hf, rfl⟩

@[simp] theorem ofFun_zero : ofFun (0 : ℂ → ℂ) (analyticAt_const (𝕜 := ℂ)) =
    (0 : AnalyticGerm z) := rfl

@[simp] theorem ofFun_one : ofFun (1 : ℂ → ℂ) (analyticAt_const (𝕜 := ℂ)) =
    (1 : AnalyticGerm z) := rfl

@[simp] theorem ofFun_add (f g : ℂ → ℂ) (hf : AnalyticAt ℂ f z)
    (hg : AnalyticAt ℂ g z) : ofFun (f + g) (hf.add hg) = ofFun f hf + ofFun g hg := rfl

@[simp] theorem ofFun_mul (f g : ℂ → ℂ) (hf : AnalyticAt ℂ f z)
    (hg : AnalyticAt ℂ g z) : ofFun (f * g) (hf.mul hg) = ofFun f hf * ofFun g hg := rfl

@[simp] theorem ofFun_neg (f : ℂ → ℂ) (hf : AnalyticAt ℂ f z) :
    ofFun (-f) hf.neg = -ofFun f hf := rfl

theorem ofFun_eq_iff {f g : ℂ → ℂ} {hf : AnalyticAt ℂ f z}
    {hg : AnalyticAt ℂ g z} : ofFun f hf = ofFun g hg ↔ f =ᶠ[𝓝 z] g := by
  rw [Subtype.ext_iff]
  exact Germ.coe_eq

/-- If an analytic function on a connected set takes a nonzero value anywhere on
that set, its germ at each point is nonzero. -/
theorem ofFun_ne_zero_of_preconnected {U : Set ℂ} {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U)
    (hU : IsPreconnected U) (hz : z ∈ U) {w : ℂ} (hw : w ∈ U) (hn : f w ≠ 0) :
    ofFun f (hf z hz) ≠ 0 := by
  intro h
  have he : f =ᶠ[𝓝 z] 0 := (ofFun_eq_iff (hf := hf z hz)
    (hg := analyticAt_const (v := (0 : ℂ)))).mp h
  exact hn (hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hU hz he hw)

/-- The germ of an analytic function on an open domain. Values away from the
domain enter only an anonymous representative of the quotient and do not affect the germ. -/
def ofDomain (U : Set ℂ) (hU : IsOpen U) (f : U → ℂ) (x : U)
    (hf : AnalyticAt ℂ f x Subtype.val) : AnalyticGerm (x : ℂ) :=
  ofFun (Function.extend Subtype.val f 0) (by
    apply AnalyticAt.of_comp_domain (coord := Subtype.val) (x := x)
    · convert hf using 1
      exact funext fun y ↦ Subtype.val_injective.extend_apply _ _ y
    · simpa only [Subtype.range_coe] using hU.mem_nhds x.property)

/-- An open-domain germ agrees with an ambient analytic germ exactly when their
functions agree near the point in the actual domain. -/
theorem ofDomain_eq_ofFun_iff (U : Set ℂ) (hU : IsOpen U) (f : U → ℂ) (x : U)
    (hf : AnalyticAt ℂ f x Subtype.val) (g : ℂ → ℂ) (hg : AnalyticAt ℂ g (x : ℂ)) :
    ofDomain U hU f x hf = ofFun g hg ↔ f =ᶠ[𝓝 x] fun y ↦ g y := by
  rw [ofDomain, ofFun_eq_iff,
    ← map_nhds_subtype_coe_eq_nhds x.property (hU.mem_nhds x.property)]
  simp only [Filter.EventuallyEq, Filter.eventually_map, Subtype.val_injective.extend_apply]

/-- The open-domain germ depends only on the local function, not its presentation. -/
theorem ofDomain_eq_iff (U : Set ℂ) (hU : IsOpen U) (f g : U → ℂ) (x : U)
    (hf : AnalyticAt ℂ f x Subtype.val) (hg : AnalyticAt ℂ g x Subtype.val) :
    ofDomain U hU f x hf = ofDomain U hU g x hg ↔ f =ᶠ[𝓝 x] g := by
  rw [ofDomain, ofDomain, ofFun_eq_iff,
    ← map_nhds_subtype_coe_eq_nhds x.property (hU.mem_nhds x.property)]
  simp only [Filter.EventuallyEq, Filter.eventually_map, Subtype.val_injective.extend_apply]

/-- Evaluation of an analytic germ is independent of its representative. -/
def eval : AnalyticGerm z →+* ℂ :=
  Germ.valueRingHom.comp (analyticGermSubring z).subtype

@[simp] theorem eval_ofFun (f : ℂ → ℂ) (hf : AnalyticAt ℂ f z) :
    eval (ofFun f hf) = f z := rfl

@[simp] theorem eval_ofDomain (U : Set ℂ) (hU : IsOpen U) (f : U → ℂ) (x : U)
    (hf : AnalyticAt ℂ f x Subtype.val) : eval (ofDomain U hU f x hf) = f x :=
  Subtype.val_injective.extend_apply _ _ _

/-- An analytic germ is a unit precisely when its value at the center is nonzero. -/
theorem isUnit_iff_eval_ne_zero (a : AnalyticGerm z) : IsUnit a ↔ eval a ≠ 0 := by
  constructor
  · exact fun h ↦ (h.map eval).ne_zero
  · obtain ⟨f, hf, he⟩ := a.property
    obtain rfl : a = ofFun f hf := Subtype.ext he.symm
    intro h
    obtain ⟨g, hg, heq⟩ := hf.exists_mul_eq_one h.isUnit
    apply isUnit_iff_exists_inv.mpr
    exact ⟨ofFun g hg, (ofFun_eq_iff (hf := hf.mul hg)
      (hg := analyticAt_const (v := (1 : ℂ)))).mpr heq⟩

instance : NoZeroDivisors (AnalyticGerm z) where
  eq_zero_or_eq_zero_of_mul_eq_zero := by
    rintro ⟨a, f, hf, rfl⟩ ⟨b, g, hg, rfl⟩ h
    have hfg : ∀ᶠ w in 𝓝 z, f w * g w = 0 :=
      Germ.coe_eq.mp (congrArg Subtype.val h)
    rcases hf.eventually_eq_zero_or_eventually_ne_zero with hf0 | hf0
    · exact Or.inl (Subtype.ext (Germ.coe_eq.mpr hf0))
    · right
      apply Subtype.ext
      apply Germ.coe_eq.mpr
      apply hg.frequently_zero_iff_eventually_zero.mp
      apply Filter.Eventually.frequently
      filter_upwards [hfg.filter_mono nhdsWithin_le_nhds, hf0] with w hw hfw
      exact (mul_eq_zero.mp hw).resolve_left hfw

instance : IsDomain (AnalyticGerm z) := NoZeroDivisors.to_isDomain _

/-- The local coordinate, vanishing at the base point but nonzero as a germ. -/
def coordinate (z : ℂ) : AnalyticGerm z :=
  ofFun (fun w ↦ w - z) (analyticAt_id.sub analyticAt_const)

@[simp] theorem eval_coordinate (z : ℂ) : eval (coordinate z) = 0 := sub_self z

theorem coordinate_ne_zero (z : ℂ) : coordinate z ≠ 0 := by
  intro h
  have hz : ∀ᶠ w in 𝓝 z, w - z = 0 := Germ.coe_eq.mp (congrArg Subtype.val h)
  have hne : ∀ᶠ w in 𝓝[≠] z, w ≠ z := self_mem_nhdsWithin
  have : ∀ᶠ w in 𝓝[≠] z, False := by
    filter_upwards [hz.filter_mono nhdsWithin_le_nhds, hne] with w hw hn
    exact hn (sub_eq_zero.mp hw)
  obtain ⟨w, hw⟩ := this.exists
  exact hw

/-- The derivative relation on analytic germs, expressed using local analytic functions and
their actual derivatives. Representatives occur only as propositional witnesses. -/
def HasDeriv (g dg : AnalyticGerm z) : Prop :=
  ∃ (f f' : ℂ → ℂ) (hf : AnalyticAt ℂ f z) (hf' : AnalyticAt ℂ f' z),
    ofFun f hf = g ∧ ofFun f' hf' = dg ∧ ∀ᶠ w in 𝓝 z, HasDerivAt f (f' w) w

theorem HasDeriv.unique {g dg₁ dg₂ : AnalyticGerm z}
    (h₁ : HasDeriv g dg₁) (h₂ : HasDeriv g dg₂) : dg₁ = dg₂ := by
  obtain ⟨f₁, f₁', hf₁, hf₁', hg₁, hd₁, hder₁⟩ := h₁
  obtain ⟨f₂, f₂', hf₂, hf₂', hg₂, hd₂, hder₂⟩ := h₂
  have hfg : f₁ =ᶠ[𝓝 z] f₂ := ofFun_eq_iff.mp (hg₁.trans hg₂.symm)
  rw [← hd₁, ← hd₂, ofFun_eq_iff]
  filter_upwards [hfg.deriv, hder₁, hder₂] with w hw hdw₁ hdw₂
  exact hdw₁.deriv.symm.trans (hw.trans hdw₂.deriv)

theorem existsUnique_hasDeriv (g : AnalyticGerm z) : ∃! dg, HasDeriv g dg := by
  obtain ⟨f, hf, heq⟩ := g.property
  have hg : ofFun f hf = g := Subtype.ext heq
  have h : HasDeriv g (ofFun (_root_.deriv f) hf.deriv) :=
    ⟨f, _root_.deriv f, hf, hf.deriv, hg, rfl,
      hf.eventually_analyticAt.mono fun w hw ↦ hw.differentiableAt.hasDerivAt⟩
  exact ⟨_, h, fun dg hdg ↦ hdg.unique h⟩

/-- Differentiation is a total operation on analytic germs; its specification determines
a unique germ, without choosing an exported representative or an off-domain derivative value. -/
def deriv (g : AnalyticGerm z) : AnalyticGerm z :=
  (existsUnique_hasDeriv g).exists.choose

theorem hasDeriv_deriv (g : AnalyticGerm z) : HasDeriv g (deriv g) :=
  (existsUnique_hasDeriv g).exists.choose_spec

theorem deriv_eq {g dg : AnalyticGerm z} (h : HasDeriv g dg) : deriv g = dg :=
  (hasDeriv_deriv g).unique h

@[simp] theorem deriv_ofFun (f : ℂ → ℂ) (hf : AnalyticAt ℂ f z) :
    deriv (ofFun f hf) = ofFun (_root_.deriv f) hf.deriv :=
  deriv_eq ⟨f, _root_.deriv f, hf, hf.deriv, rfl, rfl,
    hf.eventually_analyticAt.mono fun w hw ↦ hw.differentiableAt.hasDerivAt⟩

/-- Iterated differentiation of an analytic germ. -/
def iteratedDeriv (n : ℕ) (g : AnalyticGerm z) : AnalyticGerm z := deriv^[n] g

@[simp] theorem iteratedDeriv_zero (g : AnalyticGerm z) : iteratedDeriv 0 g = g := rfl

theorem iteratedDeriv_ofFun (n : ℕ) (f : ℂ → ℂ) (hf : AnalyticAt ℂ f z) :
    iteratedDeriv n (ofFun f hf) = ofFun (_root_.deriv^[n] f) (hf.iterated_deriv n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa only [iteratedDeriv, Function.iterate_succ', Function.comp_apply, deriv_ofFun] using
      congrArg deriv ih

theorem eval_iteratedDeriv_ofFun (n : ℕ) (f : ℂ → ℂ) (hf : AnalyticAt ℂ f z) :
    eval (iteratedDeriv n (ofFun f hf)) = _root_.iteratedDeriv n f z := by
  rw [iteratedDeriv_ofFun, eval_ofFun, _root_.iteratedDeriv_eq_iterate]

/-- The value of an iterated germ derivative is factorial times its analytic coefficient. -/
theorem eval_iteratedDeriv_eq_factorial_mul {f : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ} (hp : HasFPowerSeriesAt f p z) (n : ℕ) :
    eval (iteratedDeriv n (ofFun f hp.analyticAt)) =
      (n.factorial : ℂ) * p n (fun _ ↦ 1) := by
  rw [eval_iteratedDeriv_ofFun, _root_.iteratedDeriv_eq_iteratedFDeriv]
  obtain ⟨r, hr⟩ := hp
  simpa only [nsmul_eq_mul] using (hr.factorial_smul (1 : ℂ) n).symm

/-- The factorial coefficient formula for a function on an actual open domain. -/
theorem eval_iteratedDeriv_ofDomain_eq_factorial_mul (U : Set ℂ) (hU : IsOpen U)
    (f : U → ℂ) (x : U) {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hp : HasFPowerSeriesAt f p x Subtype.val) (n : ℕ) :
    eval (iteratedDeriv n (ofDomain U hU f x ⟨p, hp⟩)) =
      (n.factorial : ℂ) * p n (fun _ ↦ 1) := by
  let F : ℂ → ℂ := Function.extend Subtype.val f 0
  have hF (y : U) : F y = f y := Subtype.val_injective.extend_apply _ _ _
  have hFp : HasFPowerSeriesAt F p (x : ℂ) := by
    apply HasFPowerSeriesAt.of_comp_domain (coord := Subtype.val) (x := x)
    · simpa only [Function.comp_def, hF] using hp
    · simpa only [Subtype.range_coe] using hU.mem_nhds x.property
  have heq : ofDomain U hU f x ⟨p, hp⟩ = ofFun F ⟨p, hFp⟩ := rfl
  rw [heq, eval_iteratedDeriv_eq_factorial_mul hFp]

/-- Germ derivatives of an open-domain analytic function satisfy the actual-domain derivative
relation, including every finite order at the base point. -/
theorem hasIteratedDerivAt_ofDomain (U : Set ℂ) (hU : IsOpen U) (f : U → ℂ) (x : U)
    (hf : AnalyticAt ℂ f x Subtype.val) (n : ℕ) :
    HasIteratedDerivAt n f (eval (iteratedDeriv n (ofDomain U hU f x hf))) x Subtype.val := by
  let F : ℂ → ℂ := Function.extend Subtype.val f 0
  have hF (y : U) : F y = f y := Subtype.val_injective.extend_apply _ _ _
  have hFa : AnalyticAt ℂ F (x : ℂ) := by
    apply AnalyticAt.of_comp_domain (coord := Subtype.val) (x := x)
    · simpa only [Function.comp_def, hF] using hf
    · simpa only [Subtype.range_coe] using hU.mem_nhds x.property
  have heq : ofDomain U hU f x hf = ofFun F hFa := rfl
  rw [heq, eval_iteratedDeriv_ofFun]
  simpa only [Function.comp_def, hF, id_eq] using
    (hFa.hasIteratedDerivAt n).comp_domain (g := (Subtype.val : U → ℂ)) continuous_subtype_val

@[simp] theorem eval_deriv_ofDomain (U : Set ℂ) (hU : IsOpen U) (f : U → ℂ) (x : U)
    (hf : AnalyticAt ℂ f x Subtype.val) :
    eval (deriv (ofDomain U hU f x hf)) = _root_.deriv f x Subtype.val := by
  have h := HasIteratedDerivAt.one.mp (hasIteratedDerivAt_ofDomain U hU f x hf 1)
  exact (h.deriv hU.isOpenEmbedding_subtypeVal).symm

end AnalyticGerm

/-- Meromorphic germs are fractions of analytic germs. -/
abbrev MeromorphicGerm (z : ℂ) := FractionRing (AnalyticGerm z)

namespace MeromorphicGerm

variable {z : ℂ}

/-- The inclusion of analytic germs in meromorphic germs. -/
def ofAnalytic : AnalyticGerm z →+* MeromorphicGerm z := algebraMap _ _

theorem ofAnalytic_injective : Function.Injective (ofAnalytic (z := z)) :=
  IsFractionRing.injective _ _

@[simp] theorem ofAnalytic_ne_zero {f : AnalyticGerm z} :
    ofAnalytic f ≠ 0 ↔ f ≠ 0 :=
  ofAnalytic_injective.ne_iff' (map_zero ofAnalytic)

/-- Regular meromorphic germs are precisely those represented by an analytic germ. -/
def regularSubring (z : ℂ) : Subring (MeromorphicGerm z) := ofAnalytic.range

/-- The analytic ring is isomorphic to the regular subring of its fraction field. -/
def analyticEquivRegular (z : ℂ) : AnalyticGerm z ≃+* regularSubring z :=
  RingEquiv.ofBijective ofAnalytic.rangeRestrict
    ⟨fun _ _ h ↦ ofAnalytic_injective (congrArg Subtype.val h),
      RingHom.rangeRestrict_surjective _⟩

/-- Evaluation is defined on regular germs, including removable singularities. -/
def eval : regularSubring z →+* ℂ :=
  AnalyticGerm.eval.comp (analyticEquivRegular z).symm.toRingHom

/-- If numerator and denominator do not vanish together at the center, their quotient
is regular exactly when the denominator has a nonzero value there. -/
theorem div_mem_regularSubring_iff {a b : AnalyticGerm z} (hb : b ≠ 0)
    (h : AnalyticGerm.eval b = 0 → AnalyticGerm.eval a ≠ 0) :
    Checked.div (ofAnalytic a) (ofAnalytic b) (ofAnalytic_ne_zero.mpr hb).isUnit ∈
      regularSubring z ↔ AnalyticGerm.eval b ≠ 0 := by
  constructor
  · rintro ⟨u, hu⟩ hz
    have he : u * b = a := ofAnalytic_injective (by rw [map_mul]; exact eq_div_iff.mp hu)
    apply h hz
    rw [← he, map_mul, hz, mul_zero]
  · intro hz
    let u := ((AnalyticGerm.isUnit_iff_eval_ne_zero b).mpr hz).unit
    refine ⟨a * ↑u⁻¹, eq_div_iff.mpr ?_⟩
    rw [← map_mul, mul_assoc, show (↑u⁻¹ : AnalyticGerm z) * b = 1 from u.inv_val, mul_one]

@[simp] theorem eval_ofAnalytic (f : AnalyticGerm z) :
    eval (analyticEquivRegular z f) = AnalyticGerm.eval f := by
  simp [eval]

/-- Evaluation preserves the defining multiplication identity of a regular fraction,
even at a common zero of its numerator and denominator. -/
theorem eval_mul_eq_of_mul_eq {a b : AnalyticGerm z} {q : MeromorphicGerm z}
    (hq : q ∈ regularSubring z) (h : q * ofAnalytic b = ofAnalytic a) :
    eval ⟨q, hq⟩ * AnalyticGerm.eval b = AnalyticGerm.eval a := by
  have he : (⟨q, hq⟩ : regularSubring z) * analyticEquivRegular z b = analyticEquivRegular z a :=
    Subtype.ext h
  simpa only [map_mul, eval_ofAnalytic] using congrArg eval he

/-- Evaluation of a regular fraction agrees with scalar division when its denominator
is nonzero at the base point. -/
theorem eval_eq_div_of_mul_eq {a b : AnalyticGerm z} {q : MeromorphicGerm z}
    (hq : q ∈ regularSubring z) (h : q * ofAnalytic b = ofAnalytic a)
    (hb : AnalyticGerm.eval b ≠ 0) :
    eval ⟨q, hq⟩ = Checked.div (AnalyticGerm.eval a) (AnalyticGerm.eval b) hb.isUnit :=
  eq_div_iff.mpr (eval_mul_eq_of_mul_eq hq h)

/-- A nonzero analytic germ cancels even if its value at the base point is zero. -/
theorem div_self (f : AnalyticGerm z) (hf : f ≠ 0) :
    Checked.div (ofAnalytic f) (ofAnalytic f) (ofAnalytic_ne_zero.mpr hf).isUnit = 1 :=
  _root_.div_self

/-- An inverse of a vanishing analytic germ cannot be regular. -/
theorem not_regular_of_mul_eq_one {f : AnalyticGerm z} {g : MeromorphicGerm z}
    (hf : AnalyticGerm.eval f = 0) (hfg : ofAnalytic f * g = 1) :
    g ∉ regularSubring z := by
  rintro ⟨a, rfl⟩
  have ha : f * a = 1 := ofAnalytic_injective (by simpa using hfg)
  have he := congrArg AnalyticGerm.eval ha
  simp [map_mul, hf] at he

end MeromorphicGerm
