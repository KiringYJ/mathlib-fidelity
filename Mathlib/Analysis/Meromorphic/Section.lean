/-
Copyright (c) 2026 Yi-Jing Tseng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi-Jing Tseng
-/
module

public import Mathlib.Analysis.Meromorphic.Germ
public import Mathlib.Topology.Sets.Opens

/-!
# Compatible sections of meromorphic germs

A meromorphic section on an open set assigns a meromorphic germ to each point.
Locally, one pair of analytic functions represents all these germs. The denominator
is nonzero as a germ at every point of the neighborhood; its value may vanish.

Sections form a commutative ring, including on disconnected open sets. Evaluation
is restricted to points where the section's germ belongs to the analytic subring.
-/

@[expose] public section

open TopologicalSpace
open AnalyticGerm MeromorphicGerm

noncomputable section

/-- A family of germs is compatible if one analytic fraction represents all nearby stalks.
The multiplication identity specifies the quotient without evaluating a denominator at a pole. -/
def MeromorphicSectionCompatible (U : Opens ℂ) (s : (x : U) → MeromorphicGerm x) : Prop :=
  ∀ x : U, ∃ V : Set ℂ, IsOpen V ∧ (x : ℂ) ∈ V ∧ V ⊆ U ∧
    ∃ f g : ℂ → ℂ, ∃ hf : AnalyticOnNhd ℂ f V, ∃ hg : AnalyticOnNhd ℂ g V,
      (∀ (y : U) (hy : (y : ℂ) ∈ V), ofFun g (hg y hy) ≠ 0) ∧
      ∀ (y : U) (hy : (y : ℂ) ∈ V),
        ofAnalytic (ofFun f (hf y hy)) = s y * ofAnalytic (ofFun g (hg y hy))

namespace MeromorphicSectionCompatible

variable {U : Opens ℂ} {s t : (x : U) → MeromorphicGerm x}

theorem zero : MeromorphicSectionCompatible U 0 := by
  intro x
  refine ⟨U, U.isOpen, x.property, Set.Subset.rfl, 0, 1,
    fun _ _ ↦ analyticAt_const, fun _ _ ↦ analyticAt_const, ?_, ?_⟩
  · intros; simp
  · intros; simp

theorem one : MeromorphicSectionCompatible U 1 := by
  intro x
  refine ⟨U, U.isOpen, x.property, Set.Subset.rfl, 1, 1,
    fun _ _ ↦ analyticAt_const, fun _ _ ↦ analyticAt_const, ?_, ?_⟩
  · intros; simp
  · intros; simp

theorem neg (hs : MeromorphicSectionCompatible U s) :
    MeromorphicSectionCompatible U (-s) := by
  intro x
  obtain ⟨V, hV, hx, hVU, f, g, hf, hg, hgn, he⟩ := hs x
  refine ⟨V, hV, hx, hVU, -f, g, fun y hy ↦ (hf y hy).neg, hg, hgn, ?_⟩
  intro y hy
  rw [ofFun_neg f (hf y hy), map_neg, he y hy, Pi.neg_apply, neg_mul]

theorem mul (hs : MeromorphicSectionCompatible U s)
    (ht : MeromorphicSectionCompatible U t) : MeromorphicSectionCompatible U (s * t) := by
  intro x
  obtain ⟨V, hV, hxV, hVU, f, g, hf, hg, hgn, he⟩ := hs x
  obtain ⟨W, hW, hxW, hWU, a, b, ha, hb, hbn, hk⟩ := ht x
  refine ⟨V ∩ W, hV.inter hW, ⟨hxV, hxW⟩, fun y hy ↦ hVU hy.1,
    f * a, g * b, fun y hy ↦ (hf y hy.1).mul (ha y hy.2),
    fun y hy ↦ (hg y hy.1).mul (hb y hy.2), ?_, ?_⟩
  · intro y hy
    exact mul_ne_zero (hgn y hy.1) (hbn y hy.2)
  · intro y hy
    rw [ofFun_mul f a (hf y hy.1) (ha y hy.2), ofFun_mul g b (hg y hy.1) (hb y hy.2)]
    simp only [map_mul, Pi.mul_apply]
    rw [he y hy.1, hk y hy.2]
    exact mul_mul_mul_comm _ _ _ _

theorem add (hs : MeromorphicSectionCompatible U s)
    (ht : MeromorphicSectionCompatible U t) : MeromorphicSectionCompatible U (s + t) := by
  intro x
  obtain ⟨V, hV, hxV, hVU, f, g, hf, hg, hgn, he⟩ := hs x
  obtain ⟨W, hW, hxW, hWU, a, b, ha, hb, hbn, hk⟩ := ht x
  refine ⟨V ∩ W, hV.inter hW, ⟨hxV, hxW⟩, fun y hy ↦ hVU hy.1,
    f * b + a * g, g * b,
    fun y hy ↦ ((hf y hy.1).mul (hb y hy.2)).add ((ha y hy.2).mul (hg y hy.1)),
    fun y hy ↦ (hg y hy.1).mul (hb y hy.2), ?_, ?_⟩
  · intro y hy
    exact mul_ne_zero (hgn y hy.1) (hbn y hy.2)
  · intro y hy
    rw [ofFun_add (f * b) (a * g) ((hf y hy.1).mul (hb y hy.2)) ((ha y hy.2).mul (hg y hy.1)),
      ofFun_mul f b (hf y hy.1) (hb y hy.2), ofFun_mul a g (ha y hy.2) (hg y hy.1),
      ofFun_mul g b (hg y hy.1) (hb y hy.2)]
    simp only [map_add, map_mul, Pi.add_apply]
    rw [he y hy.1, hk y hy.2]
    rw [add_mul]
    congr 1 <;> ac_rfl

/-- A stalkwise inverse of a compatible section is compatible. Its local fraction
is obtained by exchanging numerator and denominator. -/
theorem inverse (hs : MeromorphicSectionCompatible U s)
    (hst : ∀ x, s x * t x = 1) : MeromorphicSectionCompatible U t := by
  intro x
  obtain ⟨V, hV, hx, hVU, f, g, hf, hg, hgn, he⟩ := hs x
  refine ⟨V, hV, hx, hVU, g, f, hg, hf, ?_, ?_⟩
  · intro y hy hfy
    have hsy : s y ≠ 0 := by
      intro hzero
      simpa [hzero] using hst y
    have hgy : ofAnalytic (ofFun g (hg y hy)) ≠ 0 := by
      intro hzero
      apply hgn y hy
      apply ofAnalytic_injective
      simpa using hzero
    apply mul_ne_zero hsy hgy
    rw [← he y hy, hfy, map_zero]
  · intro y hy
    rw [he y hy, ← mul_assoc, mul_comm (t y) (s y), hst y, one_mul]

end MeromorphicSectionCompatible

/-- The subring of compatible families of meromorphic germs on an open set. -/
def meromorphicSectionSubring (U : Opens ℂ) : Subring ((x : U) → MeromorphicGerm x) where
  carrier := {s | MeromorphicSectionCompatible U s}
  zero_mem' := MeromorphicSectionCompatible.zero
  one_mem' := MeromorphicSectionCompatible.one
  add_mem' := MeromorphicSectionCompatible.add
  mul_mem' := MeromorphicSectionCompatible.mul
  neg_mem' := MeromorphicSectionCompatible.neg

/-- A meromorphic section is a compatible family of meromorphic germs. -/
abbrev MeromorphicSection (U : Opens ℂ) : Type := ↥(meromorphicSectionSubring U)

namespace MeromorphicSection

variable {U : Opens ℂ}

/-- An analytic function on an open set gives a meromorphic section. Only its
germs on the open set enter this construction. -/
def ofAnalyticOn (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f U) : MeromorphicSection U :=
  ⟨fun x ↦ ofAnalytic (ofFun f (hf x x.property)), by
    intro x
    refine ⟨U, U.isOpen, x.property, Set.Subset.rfl, f, 1, hf,
      fun _ _ ↦ analyticAt_const, ?_, ?_⟩
    · intros; simp
    · intros; simp⟩

/-- The ring homomorphism taking a section to its germ at a point. -/
def germ (x : U) : MeromorphicSection U →+* MeromorphicGerm x :=
  (Pi.evalRingHom _ x).comp (meromorphicSectionSubring U).subtype

@[simp] theorem germ_ofAnalyticOn (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f U) (x : U) :
    germ x (ofAnalyticOn f hf) = ofAnalytic (ofFun f (hf x x.property)) := rfl

/-- A function analytic on its open domain defines a regular meromorphic section. -/
def ofAnalyticDomain (f : U → ℂ) (hf : ∀ x : U, AnalyticAt ℂ f x Subtype.val) :
    MeromorphicSection U :=
  ⟨fun x ↦ ofAnalytic (ofDomain U U.isOpen f x (hf x)), by
    let F : ℂ → ℂ := Function.extend Subtype.val f 0
    have hF (y : U) : F y = f y := Subtype.val_injective.extend_apply _ _ y
    have ha : AnalyticOnNhd ℂ F U := by
      intro z hz
      apply AnalyticAt.of_comp_domain (coord := Subtype.val) (x := (⟨z, hz⟩ : U))
      · simpa only [Function.comp_def, hF] using hf ⟨z, hz⟩
      · change Set.range (Subtype.val : ↥(U : Set ℂ) → ℂ) ∈ nhds z
        simpa only [Subtype.range_coe] using U.isOpen.mem_nhds hz
    exact (ofAnalyticOn F ha).property⟩

@[simp] theorem germ_ofAnalyticDomain (f : U → ℂ) (hf : ∀ x : U, AnalyticAt ℂ f x Subtype.val)
    (x : U) : germ x (ofAnalyticDomain f hf) = ofAnalytic (ofDomain U U.isOpen f x (hf x)) := rfl

/-- Restriction of a meromorphic section to a smaller open domain. -/
def restrict {V : Opens ℂ} (hVU : V ≤ U) : MeromorphicSection U →+* MeromorphicSection V where
  toFun s := ⟨fun x ↦ germ ⟨x, hVU x.property⟩ s, by
    intro x
    obtain ⟨W, hW, hx, _, f, g, hf, hg, hgn, he⟩ := s.property ⟨x, hVU x.property⟩
    refine ⟨W ∩ V, hW.inter V.isOpen, ⟨hx, x.property⟩, Set.inter_subset_right,
      f, g, hf.mono Set.inter_subset_left, hg.mono Set.inter_subset_left, ?_, ?_⟩
    · exact fun y hy ↦ hgn ⟨y, hVU y.property⟩ hy.1
    · exact fun y hy ↦ he ⟨y, hVU y.property⟩ hy.1⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem germ_restrict {V : Opens ℂ} (hVU : V ≤ U) (s : MeromorphicSection U) (x : V) :
    germ x (restrict hVU s) = germ ⟨x, hVU x.property⟩ s := rfl

/-- Compatible meromorphic sections on an open cover glue to a section of the union. -/
def glue {ι : Type*} (V : ι → Opens ℂ) (hVU : ∀ i, V i ≤ U)
    (hcover : ∀ x : U, ∃ i, (x : ℂ) ∈ V i) (s : ∀ i, MeromorphicSection (V i))
    (hagree : ∀ i j (z : ℂ) (hi : z ∈ V i) (hj : z ∈ V j),
      germ ⟨z, hi⟩ (s i) = germ ⟨z, hj⟩ (s j)) : MeromorphicSection U :=
  ⟨fun x ↦ germ ⟨x, (hcover x).choose_spec⟩ (s (hcover x).choose), by
    intro x
    obtain ⟨i, hi⟩ := hcover x
    obtain ⟨W, hW, hx, hWV, f, g, hf, hg, hgn, he⟩ := (s i).property ⟨x, hi⟩
    refine ⟨W, hW, hx, hWV.trans (hVU i), f, g, hf, hg, ?_, ?_⟩
    · exact fun y hy ↦ hgn ⟨y, hWV hy⟩ hy
    · intro y hy
      exact (he ⟨y, hWV hy⟩ hy).trans (congrArg (· * ofAnalytic (ofFun g (hg y hy)))
        (hagree i (hcover y).choose y (hWV hy) (hcover y).choose_spec))⟩

/-- The glued section agrees with the local section on any chart containing the point. -/
theorem germ_glue {ι : Type*} (V : ι → Opens ℂ) (hVU : ∀ i, V i ≤ U)
    (hcover : ∀ x : U, ∃ i, (x : ℂ) ∈ V i) (s : ∀ i, MeromorphicSection (V i))
    (hagree : ∀ i j (z : ℂ) (hi : z ∈ V i) (hj : z ∈ V j),
      germ ⟨z, hi⟩ (s i) = germ ⟨z, hj⟩ (s j))
    (x : U) (i : ι) (hx : (x : ℂ) ∈ V i) :
    germ x (glue V hVU hcover s hagree) = germ ⟨x, hx⟩ (s i) :=
  hagree (hcover x).choose i x (hcover x).choose_spec hx

/-- Points where the section has an analytic germ, including removable singularities. -/
def regularLocus (s : MeromorphicSection U) : Set U :=
  {x | germ x s ∈ regularSubring x}

/-- The complex value of a section at a point of its regular locus. -/
def eval (s : MeromorphicSection U) (x : regularLocus s) : ℂ :=
  MeromorphicGerm.eval ⟨germ x.val s, x.property⟩

theorem mem_regularLocus_ofAnalyticOn (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f U)
    (x : U) : x ∈ regularLocus (ofAnalyticOn f hf) :=
  ⟨ofFun f (hf x x.property), rfl⟩

@[simp] theorem eval_ofAnalyticOn (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f U) (x : U) :
    eval (ofAnalyticOn f hf) ⟨x, mem_regularLocus_ofAnalyticOn f hf x⟩ = f x := by
  change MeromorphicGerm.eval
    (MeromorphicGerm.analyticEquivRegular x (ofFun f (hf x x.property))) = f x
  simp

/-- The exact stalkwise condition for invertibility of a meromorphic section. -/
def Nonvanishing (s : MeromorphicSection U) : Prop := ∀ x : U, germ x s ≠ 0

/-- On a connected open set a single nonzero value proves that the analytic
denominator is nonzero as a germ everywhere. -/
theorem nonvanishing_of_preconnected {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U)
    (hU : IsPreconnected (U : Set ℂ)) {w : ℂ} (hw : w ∈ U) (hn : f w ≠ 0) :
    (ofAnalyticOn f hf).Nonvanishing := fun x ↦
  ofAnalytic_ne_zero.mpr (ofFun_ne_zero_of_preconnected hf hU x.property hw hn)

/-- A section with a nonzero germ at every point is a unit. This condition does
not require the regular value to be nonzero, and permits poles of the inverse. -/
def unit (s : MeromorphicSection U) (hs : s.Nonvanishing) : (MeromorphicSection U)ˣ where
  val := s
  inv := ⟨fun x ↦ ↑((Units.mk0 (germ x s) (hs x))⁻¹),
    s.property.inverse (fun x ↦ (Units.mk0 (germ x s) (hs x)).val_inv)⟩
  val_inv := Subtype.ext (funext fun x ↦ (Units.mk0 (germ x s) (hs x)).val_inv)
  inv_val := Subtype.ext (funext fun x ↦ (Units.mk0 (germ x s) (hs x)).inv_val)

theorem isUnit_iff (s : MeromorphicSection U) : IsUnit s ↔ s.Nonvanishing := by
  constructor
  · intro hs x
    exact (hs.map (germ x)).ne_zero
  · intro hs
    exact (unit s hs).isUnit

/-- The fraction of two analytic functions on an open domain. The denominator can vanish
at individual points and must have a nonzero germ at every point of the domain. -/
def ofAnalyticFraction (f g : U → ℂ) (hf : ∀ x : U, AnalyticAt ℂ f x Subtype.val)
    (hg : ∀ x : U, AnalyticAt ℂ g x Subtype.val)
    (hn : ∀ x : U, ofDomain U U.isOpen g x (hg x) ≠ 0) : MeromorphicSection U :=
  ofAnalyticDomain f hf * ↑(unit (ofAnalyticDomain g hg) (fun x ↦ ofAnalytic_ne_zero.mpr (hn x)))⁻¹

@[simp] theorem germ_ofAnalyticFraction (f g : U → ℂ) (hf : ∀ x : U, AnalyticAt ℂ f x Subtype.val)
    (hg : ∀ x : U, AnalyticAt ℂ g x Subtype.val)
    (hn : ∀ x : U, ofDomain U U.isOpen g x (hg x) ≠ 0) (x : U) :
    germ x (ofAnalyticFraction f g hf hg hn) =
      Checked.div (ofAnalytic (ofDomain U U.isOpen f x (hf x)))
        (ofAnalytic (ofDomain U U.isOpen g x (hg x))) (ofAnalytic_ne_zero.mpr (hn x)).isUnit := rfl

end MeromorphicSection
