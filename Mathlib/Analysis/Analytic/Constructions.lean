/-
Copyright (c) 2023 Geoffrey Irving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler, Geoffrey Irving, Stefan Kebekus
-/
module

public import Mathlib.Analysis.Analytic.Composition
public import Mathlib.Analysis.Analytic.Linear
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.Analysis.Analytic.OfScalars

/-!
# Various ways to combine analytic functions

We show that the following are analytic:

1. Cartesian products of analytic functions
2. Arithmetic on analytic functions: `mul`, `smul`, `inv`, `div`
3. Finite sums and products: `Finset.sum`, `Finset.prod`
-/

@[expose] public section

noncomputable section

open scoped Topology Ring
open Filter Asymptotics ENNReal NNReal

variable {α : Type*}
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F]
  [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedAddCommGroup H]
  [NormedSpace 𝕜 H]

variable {A : Type*} [NormedRing A] [NormedAlgebra 𝕜 A]
variable {𝕝 : Type*} [NormedDivisionRing 𝕝] [NormedAlgebra 𝕜 𝕝]

/-!
### Constants are analytic
-/

theorem hasFPowerSeriesOnBall_const {c : F} {e : E} :
    HasFPowerSeriesOnBall (fun _ => c) (constFormalMultilinearSeries 𝕜 E c) e ⊤ := by
  refine ⟨by simp, WithTop.top_pos, fun _ => hasSum_single 0 fun n hn => ?_⟩
  simp [constFormalMultilinearSeries_apply_of_nonzero hn]

theorem hasFPowerSeriesAt_const {c : F} {e : E} :
    HasFPowerSeriesAt (fun _ => c) (constFormalMultilinearSeries 𝕜 E c) e :=
  ⟨⊤, hasFPowerSeriesOnBall_const⟩

@[fun_prop]
theorem analyticAt_const {v : F} {x : E} : AnalyticAt 𝕜 (fun _ => v) x :=
  ⟨constFormalMultilinearSeries 𝕜 E v, hasFPowerSeriesAt_const⟩

/-- Special case of `analyticAt_const`, required for `fun_prop` to work. -/
@[fun_prop] theorem analyticAt_zero {x : E} :
    AnalyticAt 𝕜 (0 : E → F) x := analyticAt_const

@[fun_prop]
theorem analyticOnNhd_const {v : F} {s : Set E} : AnalyticOnNhd 𝕜 (fun _ => v) s :=
  fun _ _ => analyticAt_const

theorem analyticWithinAt_const {v : F} {s : Set E} {x : E} : AnalyticWithinAt 𝕜 (fun _ => v) s x :=
  analyticAt_const.analyticWithinAt

theorem analyticOn_const {v : F} {s : Set E} : AnalyticOn 𝕜 (fun _ => v) s :=
  analyticOnNhd_const.analyticOn

/-!
### Addition, negation, subtraction, scalar multiplication
-/

section

variable {f g : E → F} {pf pg : FormalMultilinearSeries 𝕜 E F} {s : Set E} {x : E} {r : ℝ≥0∞}
  {R : Type*} [NormedRing R] [Module R F] [IsBoundedSMul R F] [SMulCommClass 𝕜 R F] {c : R}

theorem HasFPowerSeriesWithinOnBall.add {D : Type*}
    {coord : D → E} {f g : D → F} {s : Set D} {x : D}
    (hf : HasFPowerSeriesWithinOnBall f pf s x r coord)
    (hg : HasFPowerSeriesWithinOnBall g pg s x r coord) :
    HasFPowerSeriesWithinOnBall (f + g) (pf + pg) s x r coord :=
  { r_le := le_trans (le_min_iff.2 ⟨hf.r_le, hg.r_le⟩) (pf.min_radius_le_radius_add pg)
    r_pos := hf.r_pos
    hasSum := fun hy h'y => (hf.hasSum hy h'y).add (hg.hasSum hy h'y) }

theorem HasFPowerSeriesOnBall.add {D : Type*} {coord : D → E} {f g : D → F} {x : D}
    (hf : HasFPowerSeriesOnBall f pf x r coord)
    (hg : HasFPowerSeriesOnBall g pg x r coord) :
    HasFPowerSeriesOnBall (f + g) (pf + pg) x r coord :=
  { r_le := le_trans (le_min_iff.2 ⟨hf.r_le, hg.r_le⟩) (pf.min_radius_le_radius_add pg)
    r_pos := hf.r_pos
    hasSum := fun hy => (hf.hasSum hy).add (hg.hasSum hy) }

theorem HasFPowerSeriesWithinAt.add
    (hf : HasFPowerSeriesWithinAt f pf s x) (hg : HasFPowerSeriesWithinAt g pg s x) :
    HasFPowerSeriesWithinAt (f + g) (pf + pg) s x := by
  rcases (hf.eventually.and hg.eventually).exists with ⟨r, hr⟩
  exact ⟨r, hr.1.add hr.2⟩

theorem HasFPowerSeriesAt.add {D : Type*} {coord : D → E} {f g : D → F} {x : D}
    (hf : HasFPowerSeriesAt f pf x coord) (hg : HasFPowerSeriesAt g pg x coord) :
    HasFPowerSeriesAt (f + g) (pf + pg) x coord := by
  obtain ⟨rf, hf⟩ := hf
  obtain ⟨rg, hg⟩ := hg
  have hpos : 0 < min rf rg := lt_min hf.r_pos hg.r_pos
  exact ⟨min rf rg, (hf.mono hpos (min_le_left _ _)).add (hg.mono hpos (min_le_right _ _))⟩

theorem AnalyticWithinAt.add (hf : AnalyticWithinAt 𝕜 f s x) (hg : AnalyticWithinAt 𝕜 g s x) :
    AnalyticWithinAt 𝕜 (f + g) s x :=
  let ⟨_, hpf⟩ := hf
  let ⟨_, hqf⟩ := hg
  (hpf.add hqf).analyticWithinAt

@[to_fun (attr := fun_prop)]
theorem AnalyticAt.add {D : Type*} {coord : D → E} {f g : D → F} {x : D}
    (hf : AnalyticAt 𝕜 f x coord) (hg : AnalyticAt 𝕜 g x coord) :
    AnalyticAt 𝕜 (f + g) x coord :=
  let ⟨_, hpf⟩ := hf
  let ⟨_, hqf⟩ := hg
  (hpf.add hqf).analyticAt

theorem AnalyticOn.add (hf : AnalyticOn 𝕜 f s) (hg : AnalyticOn 𝕜 g s) :
    AnalyticOn 𝕜 (f + g) s :=
  fun z hz => (hf z hz).add (hg z hz)

@[to_fun (attr := fun_prop)]
theorem AnalyticOnNhd.add (hf : AnalyticOnNhd 𝕜 f s) (hg : AnalyticOnNhd 𝕜 g s) :
    AnalyticOnNhd 𝕜 (f + g) s :=
  fun z hz => (hf z hz).add (hg z hz)

theorem HasFPowerSeriesWithinOnBall.neg {D : Type*}
    {coord : D → E} {f : D → F} {s : Set D} {x : D}
    (hf : HasFPowerSeriesWithinOnBall f pf s x r coord) :
    HasFPowerSeriesWithinOnBall (-f) (-pf) s x r coord :=
  { r_le := by
      rw [pf.radius_neg]
      exact hf.r_le
    r_pos := hf.r_pos
    hasSum := fun hy h'y => (hf.hasSum hy h'y).neg }

theorem HasFPowerSeriesOnBall.neg {D : Type*}
    {coord : D → E} {f : D → F} {x : D} (hf : HasFPowerSeriesOnBall f pf x r coord) :
    HasFPowerSeriesOnBall (-f) (-pf) x r coord :=
  { r_le := by
      rw [pf.radius_neg]
      exact hf.r_le
    r_pos := hf.r_pos
    hasSum := fun hy => (hf.hasSum hy).neg }

theorem HasFPowerSeriesWithinAt.neg (hf : HasFPowerSeriesWithinAt f pf s x) :
    HasFPowerSeriesWithinAt (-f) (-pf) s x :=
  let ⟨_, hrf⟩ := hf
  hrf.neg.hasFPowerSeriesWithinAt

theorem HasFPowerSeriesAt.neg (hf : HasFPowerSeriesAt f pf x) : HasFPowerSeriesAt (-f) (-pf) x :=
  let ⟨_, hrf⟩ := hf
  hrf.neg.hasFPowerSeriesAt

theorem AnalyticWithinAt.neg (hf : AnalyticWithinAt 𝕜 f s x) : AnalyticWithinAt 𝕜 (-f) s x :=
  let ⟨_, hpf⟩ := hf
  hpf.neg.analyticWithinAt

@[to_fun (attr := fun_prop)]
theorem AnalyticAt.neg (hf : AnalyticAt 𝕜 f x) : AnalyticAt 𝕜 (-f) x :=
  let ⟨_, hpf⟩ := hf
  hpf.neg.analyticAt

@[simp] lemma analyticAt_neg : AnalyticAt 𝕜 (-f) x ↔ AnalyticAt 𝕜 f x where
  mp hf := by simpa using hf.neg
  mpr := .neg

theorem AnalyticOn.neg (hf : AnalyticOn 𝕜 f s) : AnalyticOn 𝕜 (-f) s :=
  fun z hz ↦ (hf z hz).neg

@[to_fun (attr := fun_prop)]
theorem AnalyticOnNhd.neg (hf : AnalyticOnNhd 𝕜 f s) : AnalyticOnNhd 𝕜 (-f) s :=
  fun z hz ↦ (hf z hz).neg

theorem HasFPowerSeriesWithinOnBall.sub {D : Type*}
    {coord : D → E} {f g : D → F} {s : Set D} {x : D}
    (hf : HasFPowerSeriesWithinOnBall f pf s x r coord)
    (hg : HasFPowerSeriesWithinOnBall g pg s x r coord) :
    HasFPowerSeriesWithinOnBall (f - g) (pf - pg) s x r coord := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem HasFPowerSeriesOnBall.sub {D : Type*}
    {coord : D → E} {f g : D → F} {x : D}
    (hf : HasFPowerSeriesOnBall f pf x r coord)
    (hg : HasFPowerSeriesOnBall g pg x r coord) :
    HasFPowerSeriesOnBall (f - g) (pf - pg) x r coord := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem HasFPowerSeriesWithinAt.sub
    (hf : HasFPowerSeriesWithinAt f pf s x) (hg : HasFPowerSeriesWithinAt g pg s x) :
    HasFPowerSeriesWithinAt (f - g) (pf - pg) s x := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem HasFPowerSeriesAt.sub {D : Type*} {coord : D → E} {f g : D → F} {x : D}
    (hf : HasFPowerSeriesAt f pf x coord) (hg : HasFPowerSeriesAt g pg x coord) :
    HasFPowerSeriesAt (f - g) (pf - pg) x coord := by
  obtain ⟨rf, hf⟩ := hf
  obtain ⟨rg, hg⟩ := hg
  have hpos : 0 < min rf rg := lt_min hf.r_pos hg.r_pos
  exact ⟨min rf rg, (hf.mono hpos (min_le_left _ _)).sub (hg.mono hpos (min_le_right _ _))⟩

theorem AnalyticWithinAt.sub (hf : AnalyticWithinAt 𝕜 f s x) (hg : AnalyticWithinAt 𝕜 g s x) :
    AnalyticWithinAt 𝕜 (f - g) s x := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

@[to_fun (attr := fun_prop)]
theorem AnalyticAt.sub {D : Type*} {coord : D → E} {f g : D → F} {x : D}
    (hf : AnalyticAt 𝕜 f x coord) (hg : AnalyticAt 𝕜 g x coord) :
    AnalyticAt 𝕜 (f - g) x coord :=
  let ⟨_, hpf⟩ := hf
  let ⟨_, hqf⟩ := hg
  (hpf.sub hqf).analyticAt

theorem AnalyticOn.sub (hf : AnalyticOn 𝕜 f s) (hg : AnalyticOn 𝕜 g s) :
    AnalyticOn 𝕜 (f - g) s :=
  fun z hz => (hf z hz).sub (hg z hz)

@[to_fun (attr := fun_prop)]
theorem AnalyticOnNhd.sub (hf : AnalyticOnNhd 𝕜 f s) (hg : AnalyticOnNhd 𝕜 g s) :
    AnalyticOnNhd 𝕜 (f - g) s :=
  fun z hz => (hf z hz).sub (hg z hz)

theorem HasFPowerSeriesWithinOnBall.const_smul {D : Type*}
    {coord : D → E} {f : D → F} {s : Set D} {x : D}
    (hf : HasFPowerSeriesWithinOnBall f pf s x r coord) :
    HasFPowerSeriesWithinOnBall (c • f) (c • pf) s x r coord where
  r_le := le_trans hf.r_le pf.radius_le_smul
  r_pos := hf.r_pos
  hasSum := fun hy h'y => (hf.hasSum hy h'y).const_smul _

theorem HasFPowerSeriesOnBall.const_smul {D : Type*}
    {coord : D → E} {f : D → F} {x : D}
    (hf : HasFPowerSeriesOnBall f pf x r coord) :
    HasFPowerSeriesOnBall (c • f) (c • pf) x r coord where
  r_le := le_trans hf.r_le pf.radius_le_smul
  r_pos := hf.r_pos
  hasSum := fun hy => (hf.hasSum hy).const_smul _

theorem HasFPowerSeriesWithinAt.const_smul (hf : HasFPowerSeriesWithinAt f pf s x) :
    HasFPowerSeriesWithinAt (c • f) (c • pf) s x :=
  let ⟨_, hrf⟩ := hf
  hrf.const_smul.hasFPowerSeriesWithinAt

theorem HasFPowerSeriesAt.const_smul (hf : HasFPowerSeriesAt f pf x) :
    HasFPowerSeriesAt (c • f) (c • pf) x :=
  let ⟨_, hrf⟩ := hf
  hrf.const_smul.hasFPowerSeriesAt

theorem AnalyticWithinAt.const_smul (hf : AnalyticWithinAt 𝕜 f s x) :
    AnalyticWithinAt 𝕜 (c • f) s x :=
  let ⟨_, hpf⟩ := hf
  hpf.const_smul.analyticWithinAt

@[to_fun (attr := fun_prop)]
theorem AnalyticAt.const_smul (hf : AnalyticAt 𝕜 f x) : AnalyticAt 𝕜 (c • f) x :=
  let ⟨_, hpf⟩ := hf
  hpf.const_smul.analyticAt

@[to_fun]
theorem AnalyticOn.const_smul (hf : AnalyticOn 𝕜 f s) : AnalyticOn 𝕜 (c • f) s :=
  fun x hx ↦ (hf x hx).const_smul

@[to_fun (attr := fun_prop)]
theorem AnalyticOnNhd.const_smul (hf : AnalyticOnNhd 𝕜 f s) : AnalyticOnNhd 𝕜 (c • f) s :=
  fun x hx ↦ (hf x hx).const_smul

lemma AnalyticWithinAt.div_const {f : E → 𝕝} (hf : AnalyticWithinAt 𝕜 f s x) {c : 𝕝ˣ} :
    AnalyticWithinAt 𝕜 (fun y ↦ f y /ₚ c) s x := by
  simpa only [divp, Pi.smul_def, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op] using
    hf.const_smul (R := 𝕝ᵐᵒᵖ) (c := MulOpposite.op (↑c⁻¹ : 𝕝))

@[fun_prop]
lemma AnalyticAt.div_const {f : E → 𝕝} (hf : AnalyticAt 𝕜 f x) {c : 𝕝ˣ} :
    AnalyticAt 𝕜 (fun y ↦ f y /ₚ c) x := by
  simpa only [divp, Pi.smul_def, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op] using
    hf.const_smul (R := 𝕝ᵐᵒᵖ) (c := MulOpposite.op (↑c⁻¹ : 𝕝))

lemma AnalyticOn.div_const {f : E → 𝕝} (hf : AnalyticOn 𝕜 f s) {c : 𝕝ˣ} :
    AnalyticOn 𝕜 (fun y ↦ f y /ₚ c) s := by
  simpa only [divp, Pi.smul_def, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op] using
    hf.const_smul (R := 𝕝ᵐᵒᵖ) (c := MulOpposite.op (↑c⁻¹ : 𝕝))

@[fun_prop]
lemma AnalyticOnNhd.div_const {f : E → 𝕝} (hf : AnalyticOnNhd 𝕜 f s) {c : 𝕝ˣ} :
    AnalyticOnNhd 𝕜 (fun y ↦ f y /ₚ c) s := by
  simpa only [divp, Pi.smul_def, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op] using
    hf.const_smul (R := 𝕝ᵐᵒᵖ) (c := MulOpposite.op (↑c⁻¹ : 𝕝))

end

/-!
### Cartesian products are analytic
-/

/-- The radius of the Cartesian product of two formal series is the minimum of their radii. -/
lemma FormalMultilinearSeries.radius_prod_eq_min
    (p : FormalMultilinearSeries 𝕜 E F) (q : FormalMultilinearSeries 𝕜 E G) :
    (p.prod q).radius = min p.radius q.radius := by
  apply le_antisymm
  · refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
    rw [le_min_iff]
    have := (p.prod q).isLittleO_one_of_lt_radius hr
    constructor
    all_goals
      apply FormalMultilinearSeries.le_radius_of_isBigO
      refine (isBigO_of_le _ fun n ↦ ?_).trans this.isBigO
      rw [norm_mul, norm_norm, norm_mul, norm_norm]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      rw [FormalMultilinearSeries.prod, ContinuousMultilinearMap.opNorm_prod]
    · apply le_max_left
    · apply le_max_right
  · refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
    rw [lt_min_iff] at hr
    have := ((p.isLittleO_one_of_lt_radius hr.1).add
      (q.isLittleO_one_of_lt_radius hr.2)).isBigO
    refine (p.prod q).le_radius_of_isBigO ((isBigO_of_le _ fun n ↦ ?_).trans this)
    rw [norm_mul, norm_norm, ← add_mul, norm_mul]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    rw [FormalMultilinearSeries.prod, ContinuousMultilinearMap.opNorm_prod]
    refine (max_le_add_of_nonneg (norm_nonneg _) (norm_nonneg _)).trans ?_
    apply Real.le_norm_self

lemma HasFPowerSeriesWithinOnBall.prod {D : Type*}
    {coord : D → E} {e : D} {f : D → F} {g : D → G} {r s : ℝ≥0∞} {t : Set D}
    {p : FormalMultilinearSeries 𝕜 E F} {q : FormalMultilinearSeries 𝕜 E G}
    (hf : HasFPowerSeriesWithinOnBall (coord := coord) f p t e r)
    (hg : HasFPowerSeriesWithinOnBall (coord := coord) g q t e s) :
    HasFPowerSeriesWithinOnBall (coord := coord) (fun x ↦ (f x, g x)) (p.prod q) t e (min r s) where
  r_le := by
    rw [p.radius_prod_eq_min]
    exact min_le_min hf.r_le hg.r_le
  r_pos := lt_min hf.r_pos hg.r_pos
  hasSum := by
    intro y h'y hy
    simp_rw [FormalMultilinearSeries.prod, ContinuousMultilinearMap.prod_apply]
    refine (hf.hasSum h'y ?_).prodMk (hg.hasSum h'y ?_)
    · exact Metric.mem_eball.mpr (lt_of_lt_of_le hy (min_le_left _ _))
    · exact Metric.mem_eball.mpr (lt_of_lt_of_le hy (min_le_right _ _))

lemma HasFPowerSeriesOnBall.prod {D : Type*}
    {coord : D → E} {e : D} {f : D → F} {g : D → G} {r s : ℝ≥0∞}
    {p : FormalMultilinearSeries 𝕜 E F} {q : FormalMultilinearSeries 𝕜 E G}
    (hf : HasFPowerSeriesOnBall (coord := coord) f p e r)
    (hg : HasFPowerSeriesOnBall (coord := coord) g q e s) :
    HasFPowerSeriesOnBall (coord := coord) (fun x ↦ (f x, g x)) (p.prod q) e (min r s) := by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf hg ⊢
  exact hf.prod hg

lemma HasFPowerSeriesWithinAt.prod {D : Type*}
    {coord : D → E} {e : D} {f : D → F} {g : D → G} {s : Set D}
    {p : FormalMultilinearSeries 𝕜 E F} {q : FormalMultilinearSeries 𝕜 E G}
    (hf : HasFPowerSeriesWithinAt (coord := coord) f p s e)
    (hg : HasFPowerSeriesWithinAt (coord := coord) g q s e) :
    HasFPowerSeriesWithinAt (coord := coord) (fun x ↦ (f x, g x)) (p.prod q) s e := by
  rcases hf with ⟨_, hf⟩
  rcases hg with ⟨_, hg⟩
  exact ⟨_, hf.prod hg⟩

lemma HasFPowerSeriesAt.prod {D : Type*} {coord : D → E} {e : D} {f : D → F} {g : D → G}
    {p : FormalMultilinearSeries 𝕜 E F} {q : FormalMultilinearSeries 𝕜 E G}
    (hf : HasFPowerSeriesAt (coord := coord) f p e)
    (hg : HasFPowerSeriesAt (coord := coord) g q e) :
    HasFPowerSeriesAt (coord := coord) (fun x ↦ (f x, g x)) (p.prod q) e := by
  rcases hf with ⟨_, hf⟩
  rcases hg with ⟨_, hg⟩
  exact ⟨_, hf.prod hg⟩

/-- The Cartesian product of analytic functions is analytic. -/
lemma AnalyticWithinAt.prod {D : Type*} {coord : D → E} {e : D} {f : D → F} {g : D → G} {s : Set D}
    (hf : AnalyticWithinAt (coord := coord) 𝕜 f s e)
    (hg : AnalyticWithinAt (coord := coord) 𝕜 g s e) :
    AnalyticWithinAt (coord := coord) 𝕜 (fun x ↦ (f x, g x)) s e := by
  rcases hf with ⟨_, hf⟩
  rcases hg with ⟨_, hg⟩
  exact ⟨_, hf.prod hg⟩

/-- The Cartesian product of analytic functions is analytic. -/
@[fun_prop]
lemma AnalyticAt.prod {D : Type*} {coord : D → E} {e : D} {f : D → F} {g : D → G}
    (hf : AnalyticAt (coord := coord) 𝕜 f e) (hg : AnalyticAt (coord := coord) 𝕜 g e) :
    AnalyticAt (coord := coord) 𝕜 (fun x ↦ (f x, g x)) e := by
  rcases hf with ⟨_, hf⟩
  rcases hg with ⟨_, hg⟩
  exact ⟨_, hf.prod hg⟩

/-- The Cartesian product of analytic functions within a set is analytic. -/
lemma AnalyticOn.prod {D : Type*} {coord : D → E} {f : D → F} {g : D → G} {s : Set D}
    (hf : AnalyticOn (coord := coord) 𝕜 f s) (hg : AnalyticOn (coord := coord) 𝕜 g s) :
    AnalyticOn (coord := coord) 𝕜 (fun x ↦ (f x, g x)) s :=
  fun x hx ↦ (hf x hx).prod (hg x hx)

/-- The Cartesian product of analytic functions is analytic. -/
@[fun_prop]
lemma AnalyticOnNhd.prod {D : Type*} {coord : D → E} {f : D → F} {g : D → G} {s : Set D}
    (hf : AnalyticOnNhd (coord := coord) 𝕜 f s) (hg : AnalyticOnNhd (coord := coord) 𝕜 g s) :
    AnalyticOnNhd (coord := coord) 𝕜 (fun x ↦ (f x, g x)) s :=
  fun x hx ↦ (hf x hx).prod (hg x hx)

/-- `AnalyticAt.comp` for functions on product spaces -/
theorem AnalyticAt.comp₂ {h : F × G → H} {f : E → F} {g : E → G} {x : E}
    (ha : AnalyticAt 𝕜 h (f x, g x)) (fa : AnalyticAt 𝕜 f x)
    (ga : AnalyticAt 𝕜 g x) :
    AnalyticAt 𝕜 (fun x ↦ h (f x, g x)) x :=
  AnalyticAt.comp ha (fa.prod ga)

/-- `AnalyticWithinAt.comp` for functions on product spaces -/
theorem AnalyticWithinAt.comp₂ {h : F × G → H} {f : E → F} {g : E → G} {s : Set (F × G)}
    {t : Set E} {x : E}
    (ha : AnalyticWithinAt 𝕜 h s (f x, g x)) (fa : AnalyticWithinAt 𝕜 f t x)
    (ga : AnalyticWithinAt 𝕜 g t x) (hf : Set.MapsTo (fun y ↦ (f y, g y)) t s) :
    AnalyticWithinAt 𝕜 (fun x ↦ h (f x, g x)) t x :=
  AnalyticWithinAt.comp ha (fa.prod ga) hf

/-- `AnalyticAt.comp_analyticWithinAt` for functions on product spaces -/
theorem AnalyticAt.comp₂_analyticWithinAt
    {h : F × G → H} {f : E → F} {g : E → G} {x : E} {s : Set E}
    (ha : AnalyticAt 𝕜 h (f x, g x)) (fa : AnalyticWithinAt 𝕜 f s x)
    (ga : AnalyticWithinAt 𝕜 g s x) :
    AnalyticWithinAt 𝕜 (fun x ↦ h (f x, g x)) s x :=
  AnalyticAt.comp_analyticWithinAt ha (fa.prod ga)

/-- `AnalyticOnNhd.comp` for functions on product spaces -/
theorem AnalyticOnNhd.comp₂ {h : F × G → H} {f : E → F} {g : E → G} {s : Set (F × G)} {t : Set E}
    (ha : AnalyticOnNhd 𝕜 h s) (fa : AnalyticOnNhd 𝕜 f t) (ga : AnalyticOnNhd 𝕜 g t)
    (m : ∀ x, x ∈ t → (f x, g x) ∈ s) : AnalyticOnNhd 𝕜 (fun x ↦ h (f x, g x)) t :=
  fun _ xt ↦ (ha _ (m _ xt)).comp₂ (fa _ xt) (ga _ xt)

/-- `AnalyticOn.comp` for functions on product spaces -/
theorem AnalyticOn.comp₂ {h : F × G → H} {f : E → F} {g : E → G} {s : Set (F × G)}
    {t : Set E}
    (ha : AnalyticOn 𝕜 h s) (fa : AnalyticOn 𝕜 f t)
    (ga : AnalyticOn 𝕜 g t) (m : Set.MapsTo (fun y ↦ (f y, g y)) t s) :
    AnalyticOn 𝕜 (fun x ↦ h (f x, g x)) t :=
  fun x hx ↦ (ha _ (m hx)).comp₂ (fa x hx) (ga x hx) m

/-- Analytic functions on products are analytic in the first coordinate -/
theorem AnalyticAt.curry_left {f : E × F → G} {p : E × F} (fa : AnalyticAt 𝕜 f p) :
    AnalyticAt 𝕜 (fun x ↦ f (x, p.2)) p.1 :=
  AnalyticAt.comp₂ fa analyticAt_id analyticAt_const
alias AnalyticAt.along_fst := AnalyticAt.curry_left

theorem AnalyticWithinAt.curry_left
    {f : E × F → G} {s : Set (E × F)} {p : E × F} (fa : AnalyticWithinAt 𝕜 f s p) :
    AnalyticWithinAt 𝕜 (fun x ↦ f (x, p.2)) {x | (x, p.2) ∈ s} p.1 :=
  AnalyticWithinAt.comp₂ fa analyticWithinAt_id analyticWithinAt_const (fun _ hx ↦ hx)

/-- Analytic functions on products are analytic in the second coordinate -/
theorem AnalyticAt.curry_right {f : E × F → G} {p : E × F} (fa : AnalyticAt 𝕜 f p) :
    AnalyticAt 𝕜 (fun y ↦ f (p.1, y)) p.2 :=
  AnalyticAt.comp₂ fa analyticAt_const analyticAt_id
alias AnalyticAt.along_snd := AnalyticAt.curry_right

theorem AnalyticWithinAt.curry_right
    {f : E × F → G} {s : Set (E × F)} {p : E × F} (fa : AnalyticWithinAt 𝕜 f s p) :
    AnalyticWithinAt 𝕜 (fun y ↦ f (p.1, y)) {y | (p.1, y) ∈ s} p.2 :=
  AnalyticWithinAt.comp₂ fa analyticWithinAt_const analyticWithinAt_id (fun _ hx ↦ hx)

/-- Analytic functions on products are analytic in the first coordinate -/
theorem AnalyticOnNhd.curry_left {f : E × F → G} {s : Set (E × F)} {y : F}
    (fa : AnalyticOnNhd 𝕜 f s) :
    AnalyticOnNhd 𝕜 (fun x ↦ f (x, y)) {x | (x, y) ∈ s} :=
  fun x m ↦ (fa (x, y) m).curry_left
alias AnalyticOnNhd.along_fst := AnalyticOnNhd.curry_left

theorem AnalyticOn.curry_left
    {f : E × F → G} {s : Set (E × F)} {y : F} (fa : AnalyticOn 𝕜 f s) :
    AnalyticOn 𝕜 (fun x ↦ f (x, y)) {x | (x, y) ∈ s} :=
  fun x m ↦ (fa (x, y) m).curry_left

/-- Analytic functions on products are analytic in the second coordinate -/
theorem AnalyticOnNhd.curry_right {f : E × F → G} {x : E} {s : Set (E × F)}
    (fa : AnalyticOnNhd 𝕜 f s) :
    AnalyticOnNhd 𝕜 (fun y ↦ f (x, y)) {y | (x, y) ∈ s} :=
  fun y m ↦ (fa (x, y) m).curry_right
alias AnalyticOnNhd.along_snd := AnalyticOnNhd.curry_right

theorem AnalyticOn.curry_right
    {f : E × F → G} {x : E} {s : Set (E × F)} (fa : AnalyticOn 𝕜 f s) :
    AnalyticOn 𝕜 (fun y ↦ f (x, y)) {y | (x, y) ∈ s} :=
  fun y m ↦ (fa (x, y) m).curry_right

/-!
### Analyticity in Pi spaces

In this section, `f : Π i, E → Fm i` is a family of functions, i.e., each `f i` is a function,
from `E` to a space `Fm i`. We discuss whether the family as a whole is analytic as a function
of `x : E`, i.e., whether `x ↦ (f 1 x, ..., f n x)` is analytic from `E` to the product space
`Π i, Fm i`. This function is denoted either by `fun x ↦ (fun i ↦ f i x)`, or `fun x i ↦ f i x`,
or `fun x ↦ (f ⬝ x)`. We use the latter spelling in the statements, for readability purposes.
-/

section

variable {ι : Type*} [Fintype ι] {e : E} {Fm : ι → Type*}
    [∀ i, NormedAddCommGroup (Fm i)] [∀ i, NormedSpace 𝕜 (Fm i)]
    {f : Π i, E → Fm i} {s : Set E} {r : ℝ≥0∞}
    {p : Π i, FormalMultilinearSeries 𝕜 E (Fm i)}

lemma FormalMultilinearSeries.radius_pi_le (p : Π i, FormalMultilinearSeries 𝕜 E (Fm i)) (i : ι) :
    (FormalMultilinearSeries.pi p).radius ≤ (p i).radius := by
  apply le_of_forall_nnreal_lt (fun r' hr' ↦ ?_)
  obtain ⟨C, -, hC⟩ : ∃ C > 0, ∀ n, ‖pi p n‖ * ↑r' ^ n ≤ C := norm_mul_pow_le_of_lt_radius _ hr'
  apply le_radius_of_bound _ C (fun n ↦ ?_)
  apply le_trans _ (hC n)
  gcongr
  rw [pi, ContinuousMultilinearMap.opNorm_pi]
  exact norm_le_pi_norm (fun i ↦ p i n) i

lemma FormalMultilinearSeries.le_radius_pi (h : ∀ i, r ≤ (p i).radius) :
    r ≤ (FormalMultilinearSeries.pi p).radius := by
  apply le_of_forall_nnreal_lt (fun r' hr' ↦ ?_)
  have I i : ∃ C > 0, ∀ n, ‖p i n‖ * (r' : ℝ) ^ n ≤ C :=
    norm_mul_pow_le_of_lt_radius _ (hr'.trans_le (h i))
  choose C C_pos hC using I
  obtain ⟨D, D_nonneg, hD⟩ : ∃ D ≥ 0, ∀ i, C i ≤ D :=
    ⟨∑ i, C i, Finset.sum_nonneg (fun i _ ↦ (C_pos i).le),
      fun i ↦ Finset.single_le_sum (fun j _ ↦ (C_pos j).le) (Finset.mem_univ _)⟩
  apply le_radius_of_bound _ D (fun n ↦ ?_)
  rcases le_or_gt ((r' : ℝ) ^ n) 0 with hr' | hr'
  · exact le_trans (mul_nonpos_of_nonneg_of_nonpos (by positivity) hr') D_nonneg
  · simp only [pi]
    rw [← le_div_iff₀ hr', ContinuousMultilinearMap.opNorm_pi,
      pi_norm_le_iff_of_nonneg (by positivity)]
    intro i
    exact (le_div_iff₀ hr').2 ((hC i n).trans (hD i))

lemma FormalMultilinearSeries.radius_pi_eq_iInf :
    (FormalMultilinearSeries.pi p).radius = ⨅ i, (p i).radius := by
  refine le_antisymm (by simp [radius_pi_le]) ?_
  apply le_of_forall_nnreal_lt (fun r' hr' ↦ ?_)
  exact le_radius_pi (fun i ↦ le_iInf_iff.1 hr'.le i)

/-- If each function in a finite family has a power series within a ball, then so does the
family as a whole. Note that the positivity assumption on the radius is only needed when
the family is empty. -/
lemma HasFPowerSeriesWithinOnBall.pi
    (hf : ∀ i, HasFPowerSeriesWithinOnBall (f i) (p i) s e r) (hr : 0 < r) :
    HasFPowerSeriesWithinOnBall (fun x ↦ (f · x)) (FormalMultilinearSeries.pi p) s e r where
  r_le := by
    apply FormalMultilinearSeries.le_radius_pi (fun i ↦ ?_)
    exact (hf i).r_le
  r_pos := hr
  hasSum {_} m hy := Pi.hasSum.2 (fun i ↦ (hf i).hasSum m hy)

lemma hasFPowerSeriesWithinOnBall_pi_iff (hr : 0 < r) :
    HasFPowerSeriesWithinOnBall (fun x ↦ (f · x)) (FormalMultilinearSeries.pi p) s e r ↔
      ∀ i, HasFPowerSeriesWithinOnBall (f i) (p i) s e r where
  mp h i :=
    ⟨h.r_le.trans (FormalMultilinearSeries.radius_pi_le _ _), hr,
      fun m hy ↦ Pi.hasSum.1 (h.hasSum m hy) i⟩
  mpr h := .pi h hr

lemma HasFPowerSeriesOnBall.pi
    (hf : ∀ i, HasFPowerSeriesOnBall (f i) (p i) e r) (hr : 0 < r) :
    HasFPowerSeriesOnBall (fun x ↦ (f · x)) (FormalMultilinearSeries.pi p) e r := by
  simp_rw [← hasFPowerSeriesWithinOnBall_univ] at hf ⊢
  exact HasFPowerSeriesWithinOnBall.pi hf hr

lemma hasFPowerSeriesOnBall_pi_iff (hr : 0 < r) :
    HasFPowerSeriesOnBall (fun x ↦ (f · x)) (FormalMultilinearSeries.pi p) e r ↔
      ∀ i, HasFPowerSeriesOnBall (f i) (p i) e r := by
  simp_rw [← hasFPowerSeriesWithinOnBall_univ]
  exact hasFPowerSeriesWithinOnBall_pi_iff hr

lemma HasFPowerSeriesWithinAt.pi
    (hf : ∀ i, HasFPowerSeriesWithinAt (f i) (p i) s e) :
    HasFPowerSeriesWithinAt (fun x ↦ (f · x)) (FormalMultilinearSeries.pi p) s e := by
  have : ∀ᶠ r in 𝓝[>] 0, ∀ i, HasFPowerSeriesWithinOnBall (f i) (p i) s e r :=
    eventually_all.mpr (fun i ↦ (hf i).eventually)
  obtain ⟨r, hr, r_pos⟩ := (this.and self_mem_nhdsWithin).exists
  exact ⟨r, HasFPowerSeriesWithinOnBall.pi hr r_pos⟩

lemma hasFPowerSeriesWithinAt_pi_iff :
    HasFPowerSeriesWithinAt (fun x ↦ (f · x)) (FormalMultilinearSeries.pi p) s e ↔
      ∀ i, HasFPowerSeriesWithinAt (f i) (p i) s e := by
  refine ⟨fun h i ↦ ?_, fun h ↦ .pi h⟩
  obtain ⟨r, hr⟩ := h
  exact ⟨r, (hasFPowerSeriesWithinOnBall_pi_iff hr.r_pos).1 hr i⟩

lemma HasFPowerSeriesAt.pi
    (hf : ∀ i, HasFPowerSeriesAt (f i) (p i) e) :
    HasFPowerSeriesAt (fun x ↦ (f · x)) (FormalMultilinearSeries.pi p) e := by
  simp_rw [← hasFPowerSeriesWithinAt_univ] at hf ⊢
  exact HasFPowerSeriesWithinAt.pi hf

lemma hasFPowerSeriesAt_pi_iff :
    HasFPowerSeriesAt (fun x ↦ (f · x)) (FormalMultilinearSeries.pi p) e ↔
      ∀ i, HasFPowerSeriesAt (f i) (p i) e := by
  simp_rw [← hasFPowerSeriesWithinAt_univ]
  exact hasFPowerSeriesWithinAt_pi_iff

lemma AnalyticWithinAt.pi (hf : ∀ i, AnalyticWithinAt 𝕜 (f i) s e) :
    AnalyticWithinAt 𝕜 (fun x ↦ (f · x)) s e := by
  choose p hp using hf
  exact ⟨FormalMultilinearSeries.pi p, HasFPowerSeriesWithinAt.pi hp⟩

lemma analyticWithinAt_pi_iff :
    AnalyticWithinAt 𝕜 (fun x ↦ (f · x)) s e ↔ ∀ i, AnalyticWithinAt 𝕜 (f i) s e := by
  refine ⟨fun h i ↦ ?_, fun h ↦ .pi h⟩
  exact ((ContinuousLinearMap.proj (R := 𝕜) i).analyticAt _).comp_analyticWithinAt h

lemma AnalyticAt.pi (hf : ∀ i, AnalyticAt 𝕜 (f i) e) :
    AnalyticAt 𝕜 (fun x ↦ (f · x)) e := by
  simp_rw [← analyticWithinAt_univ] at hf ⊢
  exact AnalyticWithinAt.pi hf

lemma analyticAt_pi_iff :
    AnalyticAt 𝕜 (fun x ↦ (f · x)) e ↔ ∀ i, AnalyticAt 𝕜 (f i) e := by
  simp_rw [← analyticWithinAt_univ]
  exact analyticWithinAt_pi_iff

lemma AnalyticOn.pi (hf : ∀ i, AnalyticOn 𝕜 (f i) s) :
    AnalyticOn 𝕜 (fun x ↦ (f · x)) s :=
  fun x hx ↦ AnalyticWithinAt.pi (fun i ↦ hf i x hx)

lemma analyticOn_pi_iff :
    AnalyticOn 𝕜 (fun x ↦ (f · x)) s ↔ ∀ i, AnalyticOn 𝕜 (f i) s :=
  ⟨fun h i x hx ↦ analyticWithinAt_pi_iff.1 (h x hx) i, fun h ↦ .pi h⟩

lemma AnalyticOnNhd.pi (hf : ∀ i, AnalyticOnNhd 𝕜 (f i) s) :
    AnalyticOnNhd 𝕜 (fun x ↦ (f · x)) s :=
  fun x hx ↦ AnalyticAt.pi (fun i ↦ hf i x hx)

lemma analyticOnNhd_pi_iff :
    AnalyticOnNhd 𝕜 (fun x ↦ (f · x)) s ↔ ∀ i, AnalyticOnNhd 𝕜 (f i) s :=
  ⟨fun h i x hx ↦ analyticAt_pi_iff.1 (h x hx) i, fun h ↦ .pi h⟩

end

/-!
### Arithmetic on analytic functions
-/

/-- Scalar multiplication is analytic (jointly in both variables). The statement is a little
pedantic to allow towers of field extensions. -/
@[fun_prop]
lemma analyticAt_smul [Module A E] [IsBoundedSMul A E] [IsScalarTower 𝕜 A E] (z : A × E) :
    AnalyticAt 𝕜 (fun x : A × E ↦ x.1 • x.2) z :=
  (ContinuousLinearMap.lsmul 𝕜 A).analyticAt_bilinear z

/-- Multiplication in a normed algebra over `𝕜` is analytic. -/
@[fun_prop]
lemma analyticAt_mul (z : A × A) : AnalyticAt 𝕜 (fun x : A × A ↦ x.1 * x.2) z :=
  analyticAt_smul z

/-- Scalar multiplication preserves analyticity on an embedded domain. -/
lemma AnalyticWithinAt.smul {D : Type*} [TopologicalSpace D] {coord : D → E}
    [Module A F] [IsBoundedSMul A F] [IsScalarTower 𝕜 A F]
    {f : D → A} {g : D → F} {s : Set D} {z : D}
    (hf : AnalyticWithinAt 𝕜 f s z coord) (hg : AnalyticWithinAt 𝕜 g s z coord)
    (hcoord : Topology.IsEmbedding coord := by exact Topology.IsEmbedding.id) :
    AnalyticWithinAt 𝕜 (f • g) s z coord :=
  (analyticAt_smul _).comp_analyticWithinAt (hf.prod hg) hcoord Topology.IsEmbedding.id

/-- Scalar multiplication preserves analyticity on an embedded domain. -/
@[to_fun (attr := fun_prop)]
lemma AnalyticAt.smul {D : Type*} [TopologicalSpace D] {coord : D → E}
    [Module A F] [IsBoundedSMul A F] [IsScalarTower 𝕜 A F]
    {f : D → A} {g : D → F} {z : D}
    (hf : AnalyticAt 𝕜 f z coord) (hg : AnalyticAt 𝕜 g z coord)
    (hcoord : Topology.IsEmbedding coord := by exact Topology.IsEmbedding.id) :
    AnalyticAt 𝕜 (f • g) z coord :=
  (analyticAt_smul _).comp (hf.prod hg) hcoord Topology.IsEmbedding.id

/-- Scalar multiplication preserves analyticity on an embedded domain. -/
lemma AnalyticOn.smul {D : Type*} [TopologicalSpace D] {coord : D → E}
    [Module A F] [IsBoundedSMul A F] [IsScalarTower 𝕜 A F]
    {f : D → A} {g : D → F} {s : Set D}
    (hf : AnalyticOn 𝕜 f s coord) (hg : AnalyticOn 𝕜 g s coord)
    (hcoord : Topology.IsEmbedding coord := by exact Topology.IsEmbedding.id) :
    AnalyticOn 𝕜 (f • g) s coord :=
  fun z hz ↦ (hf z hz).smul (hg z hz) hcoord

/-- Scalar multiplication preserves analyticity on an embedded domain. -/
@[fun_prop]
lemma AnalyticOnNhd.smul {D : Type*} [TopologicalSpace D] {coord : D → E}
    [Module A F] [IsBoundedSMul A F] [IsScalarTower 𝕜 A F]
    {f : D → A} {g : D → F} {s : Set D}
    (hf : AnalyticOnNhd 𝕜 f s coord) (hg : AnalyticOnNhd 𝕜 g s coord)
    (hcoord : Topology.IsEmbedding coord := by exact Topology.IsEmbedding.id) :
    AnalyticOnNhd 𝕜 (f • g) s coord :=
  fun z hz ↦ (hf z hz).smul (hg z hz) hcoord

/-- Multiplication preserves analyticity on an embedded domain. -/
lemma AnalyticWithinAt.mul {D : Type*} [TopologicalSpace D] {coord : D → E}
    {f g : D → A} {s : Set D} {z : D}
    (hf : AnalyticWithinAt 𝕜 f s z coord) (hg : AnalyticWithinAt 𝕜 g s z coord)
    (hcoord : Topology.IsEmbedding coord := by exact Topology.IsEmbedding.id) :
    AnalyticWithinAt 𝕜 (f * g) s z coord :=
  (analyticAt_mul _).comp_analyticWithinAt (hf.prod hg) hcoord Topology.IsEmbedding.id

/-- Multiplication preserves analyticity on an embedded domain. -/
@[to_fun (attr := fun_prop)]
lemma AnalyticAt.mul {D : Type*} [TopologicalSpace D] {coord : D → E}
    {f g : D → A} {z : D}
    (hf : AnalyticAt 𝕜 f z coord) (hg : AnalyticAt 𝕜 g z coord)
    (hcoord : Topology.IsEmbedding coord := by exact Topology.IsEmbedding.id) :
    AnalyticAt 𝕜 (f * g) z coord :=
  hf.smul hg hcoord

/-- Multiplication preserves analyticity on an embedded domain. -/
lemma AnalyticOn.mul {D : Type*} [TopologicalSpace D] {coord : D → E}
    {f g : D → A} {s : Set D}
    (hf : AnalyticOn 𝕜 f s coord) (hg : AnalyticOn 𝕜 g s coord)
    (hcoord : Topology.IsEmbedding coord := by exact Topology.IsEmbedding.id) :
    AnalyticOn 𝕜 (f * g) s coord :=
  hf.smul hg hcoord

/-- Multiplication preserves analyticity on an embedded domain. -/
@[fun_prop]
lemma AnalyticOnNhd.mul {D : Type*} [TopologicalSpace D] {coord : D → E}
    {f g : D → A} {s : Set D}
    (hf : AnalyticOnNhd 𝕜 f s coord) (hg : AnalyticOnNhd 𝕜 g s coord)
    (hcoord : Topology.IsEmbedding coord := by exact Topology.IsEmbedding.id) :
    AnalyticOnNhd 𝕜 (f * g) s coord :=
  hf.smul hg hcoord

/-- Powers of analytic functions (into a normed `𝕜`-algebra) are analytic. -/
@[to_fun]
lemma AnalyticWithinAt.pow {f : E → A} {z : E} {s : Set E} (hf : AnalyticWithinAt 𝕜 f s z)
    (n : ℕ) :
    AnalyticWithinAt 𝕜 (f ^ n) s z := by
  induction n with
  | zero =>
    simp only [pow_zero]
    apply analyticWithinAt_const
  | succ m hm =>
    simp only [pow_succ]
    exact hm.mul hf

/-- Powers of analytic functions (into a normed `𝕜`-algebra) are analytic. -/
@[to_fun (attr := fun_prop)]
lemma AnalyticAt.pow {f : E → A} {z : E} (hf : AnalyticAt 𝕜 f z) (n : ℕ) :
    AnalyticAt 𝕜 (f ^ n) z := by
  rw [← analyticWithinAt_univ] at hf ⊢
  exact hf.pow n

/-- Powers of analytic functions (into a normed `𝕜`-algebra) are analytic. -/
@[to_fun]
lemma AnalyticOn.pow {f : E → A} {s : Set E} (hf : AnalyticOn 𝕜 f s) (n : ℕ) :
    AnalyticOn 𝕜 (f ^ n) s :=
  fun _ m ↦ (hf _ m).pow n

/-- Powers of analytic functions (into a normed `𝕜`-algebra) are analytic. -/
@[to_fun (attr := fun_prop)]
lemma AnalyticOnNhd.pow {f : E → A} {s : Set E} (hf : AnalyticOnNhd 𝕜 f s) (n : ℕ) :
    AnalyticOnNhd 𝕜 (f ^ n) s :=
  fun _ m ↦ (hf _ m).pow n

/-- Nonnegative integer powers of an analytic function are analytic, including at its zeros. -/
lemma AnalyticWithinAt.zpow_nonneg {f : E → 𝕝} {z : E} {s : Set E} {n : ℤ}
    (hf : AnalyticWithinAt 𝕜 f s z) (hn : 0 ≤ n) :
    AnalyticWithinAt 𝕜
      (fun y ↦ Checked.zpow (f y) n (fun h ↦ (not_lt_of_ge hn h).elim)) s z := by
  lift n to ℕ using hn
  simpa only [zpow_natCast₀, Pi.pow_def] using hf.pow n

/-- Nonnegative integer powers of an analytic function are analytic, including at its zeros. -/
lemma AnalyticAt.zpow_nonneg {f : E → 𝕝} {z : E} {n : ℤ}
    (hf : AnalyticAt 𝕜 f z) (hn : 0 ≤ n) :
    AnalyticAt 𝕜
      (fun y ↦ Checked.zpow (f y) n (fun h ↦ (not_lt_of_ge hn h).elim)) z := by
  lift n to ℕ using hn
  simpa only [zpow_natCast₀, Pi.pow_def] using hf.pow n

/-- Nonnegative integer powers of an analytic function are analytic, including at its zeros. -/
lemma AnalyticOn.zpow_nonneg {f : E → 𝕝} {s : Set E} {n : ℤ}
    (hf : AnalyticOn 𝕜 f s) (hn : 0 ≤ n) :
    AnalyticOn 𝕜
      (fun y ↦ Checked.zpow (f y) n (fun h ↦ (not_lt_of_ge hn h).elim)) s := by
  lift n to ℕ using hn
  simpa only [zpow_natCast₀, Pi.pow_def] using hf.pow n

/-- Nonnegative integer powers of an analytic function are analytic, including at its zeros. -/
lemma AnalyticOnNhd.zpow_nonneg {f : E → 𝕝} {s : Set E} {n : ℤ}
    (hf : AnalyticOnNhd 𝕜 f s) (hn : 0 ≤ n) :
    AnalyticOnNhd 𝕜
      (fun y ↦ Checked.zpow (f y) n (fun h ↦ (not_lt_of_ge hn h).elim)) s := by
  lift n to ℕ using hn
  simpa only [zpow_natCast₀, Pi.pow_def] using hf.pow n

/-!
### Composition with a linear map
-/

section compContinuousLinearMap

variable {u : E →L[𝕜] F} {f : F → G} {pf : FormalMultilinearSeries 𝕜 F G} {s : Set F} {x : E}
  {r : ℝ≥0∞}

theorem HasFPowerSeriesWithinOnBall.compContinuousLinearMap
    (hf : HasFPowerSeriesWithinOnBall f pf s (u x) r) :
    HasFPowerSeriesWithinOnBall (f ∘ u) (pf.compContinuousLinearMap u) (u ⁻¹' s) x
      (r / ‖u‖ₑ) where
  r_le := by
    calc
      _ ≤ (pf.radius / ‖u‖ₑ) := ENNReal.div_le_div_right hf.r_le _
      _ ≤ _ := pf.div_le_radius_compContinuousLinearMap _
  r_pos := by
    simp only [ENNReal.div_pos_iff, ne_eq, enorm_ne_top, not_false_eq_true, and_true]
    exact pos_iff_ne_zero.mp hf.r_pos
  hasSum {y} hy1 hy2 := by
    have hmem : u y ∈ Set.insert (u x) s := by
      rcases hy1 with rfl | hy1
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ hy1
    have hsmall : u y - u x ∈ Metric.eball (0 : F) r := by
      rw [← map_sub]
      simp only [Metric.eball, edist_zero_right, Set.mem_ofPred_eq] at hy2 ⊢
      exact lt_of_le_of_lt (ContinuousLinearMap.le_opENorm _ _) (mul_lt_of_lt_div' hy2)
    simpa only [FormalMultilinearSeries.compContinuousLinearMap_apply, map_sub,
      Function.comp_def, id_eq] using hf.hasSum hmem hsmall

theorem HasFPowerSeriesOnBall.compContinuousLinearMap (hf : HasFPowerSeriesOnBall f pf (u x) r) :
    HasFPowerSeriesOnBall (f ∘ u) (pf.compContinuousLinearMap u) x (r / ‖u‖ₑ) := by
  rw [← hasFPowerSeriesWithinOnBall_univ] at hf ⊢
  exact hf.compContinuousLinearMap

theorem HasFPowerSeriesAt.compContinuousLinearMap (hf : HasFPowerSeriesAt f pf (u x)) :
    HasFPowerSeriesAt (f ∘ u) (pf.compContinuousLinearMap u) x :=
  let ⟨r, hr⟩ := hf
  ⟨(r / ‖u‖ₑ), hr.compContinuousLinearMap⟩

theorem HasFPowerSeriesWithinAt.compContinuousLinearMap
    (hf : HasFPowerSeriesWithinAt f pf s (u x)) :
    HasFPowerSeriesWithinAt (f ∘ u) (pf.compContinuousLinearMap u) (u ⁻¹' s) x :=
  let ⟨r, hr⟩ := hf
  ⟨(r / ‖u‖ₑ), hr.compContinuousLinearMap⟩

theorem AnalyticAt.compContinuousLinearMap (hf : AnalyticAt 𝕜 f (u x)) :
    AnalyticAt 𝕜 (f ∘ u) x :=
  let ⟨p, hp⟩ := hf
  ⟨p.compContinuousLinearMap u, hp.compContinuousLinearMap⟩

theorem AnalyticAtWithin.compContinuousLinearMap (hf : AnalyticWithinAt 𝕜 f s (u x)) :
    AnalyticWithinAt 𝕜 (f ∘ u) (u ⁻¹' s) x :=
  let ⟨p, hp⟩ := hf
  ⟨p.compContinuousLinearMap u, hp.compContinuousLinearMap⟩

theorem AnalyticOn.compContinuousLinearMap (hf : AnalyticOn 𝕜 f s) :
    AnalyticOn 𝕜 (f ∘ u) (u ⁻¹' s) := fun x hx =>
  AnalyticAtWithin.compContinuousLinearMap (hf (u x) hx)

theorem AnalyticOnNhd.compContinuousLinearMap (hf : AnalyticOnNhd 𝕜 f s) :
    AnalyticOnNhd 𝕜 (f ∘ u) (u ⁻¹' s) := fun x hx =>
  AnalyticAt.compContinuousLinearMap (hf (u x) hx)

end compContinuousLinearMap

/-!
### Restriction of scalars
-/

section

variable {𝕜' : Type*} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']
  [NormedSpace 𝕜' E] [IsScalarTower 𝕜 𝕜' E]
  [NormedSpace 𝕜' F] [IsScalarTower 𝕜 𝕜' F]
  {D : Type*} {coord : D → E} {f : D → F} {p : FormalMultilinearSeries 𝕜' E F}
  {x : D} {s : Set D} {r : ℝ≥0∞}

lemma HasFPowerSeriesWithinOnBall.restrictScalars
    (hf : HasFPowerSeriesWithinOnBall f p s x r coord) :
    HasFPowerSeriesWithinOnBall f (p.restrictScalars 𝕜) s x r coord :=
  ⟨hf.r_le.trans (FormalMultilinearSeries.radius_le_of_le (fun n ↦ by simp)), hf.r_pos, hf.hasSum⟩

lemma HasFPowerSeriesOnBall.restrictScalars (hf : HasFPowerSeriesOnBall f p x r coord) :
    HasFPowerSeriesOnBall f (p.restrictScalars 𝕜) x r coord :=
  ⟨hf.r_le.trans (FormalMultilinearSeries.radius_le_of_le (fun n ↦ by simp)), hf.r_pos, hf.hasSum⟩

lemma HasFPowerSeriesWithinAt.restrictScalars (hf : HasFPowerSeriesWithinAt f p s x coord) :
    HasFPowerSeriesWithinAt f (p.restrictScalars 𝕜) s x coord := by
  rcases hf with ⟨r, hr⟩
  exact ⟨r, hr.restrictScalars⟩

lemma HasFPowerSeriesAt.restrictScalars (hf : HasFPowerSeriesAt f p x coord) :
    HasFPowerSeriesAt f (p.restrictScalars 𝕜) x coord := by
  rcases hf with ⟨r, hr⟩
  exact ⟨r, hr.restrictScalars⟩

lemma AnalyticWithinAt.restrictScalars (hf : AnalyticWithinAt 𝕜' f s x coord) :
    AnalyticWithinAt 𝕜 f s x coord := by
  rcases hf with ⟨p, hp⟩
  exact ⟨p.restrictScalars 𝕜, hp.restrictScalars⟩

lemma AnalyticAt.restrictScalars (hf : AnalyticAt 𝕜' f x coord) :
    AnalyticAt 𝕜 f x coord := by
  rcases hf with ⟨p, hp⟩
  exact ⟨p.restrictScalars 𝕜, hp.restrictScalars⟩

lemma AnalyticOn.restrictScalars (hf : AnalyticOn 𝕜' f s coord) :
    AnalyticOn 𝕜 f s coord :=
  fun x hx ↦ (hf x hx).restrictScalars

lemma AnalyticOnNhd.restrictScalars (hf : AnalyticOnNhd 𝕜' f s coord) :
    AnalyticOnNhd 𝕜 f s coord :=
  fun x hx ↦ (hf x hx).restrictScalars

end


/-!
### Inversion is analytic
-/

section Geometric
variable (𝕜 A)

/-- The geometric series `1 + x + x ^ 2 + ...` as a `FormalMultilinearSeries`. -/
def formalMultilinearSeries_geometric : FormalMultilinearSeries 𝕜 A A :=
  fun n ↦ ContinuousMultilinearMap.mkPiAlgebraFin 𝕜 n A

/-- The geometric series as an `ofScalars` series. -/
theorem formalMultilinearSeries_geometric_eq_ofScalars :
    formalMultilinearSeries_geometric 𝕜 A =
      FormalMultilinearSeries.ofScalars A fun _ ↦ (1 : 𝕜) := by
  simp_rw [FormalMultilinearSeries.ext_iff, FormalMultilinearSeries.ofScalars,
    formalMultilinearSeries_geometric, one_smul, implies_true]

lemma formalMultilinearSeries_geometric_apply_norm_le (n : ℕ) :
    ‖formalMultilinearSeries_geometric 𝕜 A n‖ ≤ max 1 ‖(1 : A)‖ :=
  ContinuousMultilinearMap.norm_mkPiAlgebraFin_le

lemma formalMultilinearSeries_geometric_apply_norm [NormOneClass A] (n : ℕ) :
    ‖formalMultilinearSeries_geometric 𝕜 A n‖ = 1 :=
  ContinuousMultilinearMap.norm_mkPiAlgebraFin

lemma one_le_formalMultilinearSeries_geometric_radius :
    1 ≤ (formalMultilinearSeries_geometric 𝕜 A).radius := by
  convert!
    formalMultilinearSeries_geometric_eq_ofScalars 𝕜 A ▸
      FormalMultilinearSeries.inv_le_ofScalars_radius_of_tendsto (𝕜 := 𝕜) A
        (fun _ : ℕ => (1 : 𝕜)) one_ne_zero
        (by simpa using tendsto_const_nhds (x := (1 : ℝ)))
  simp

lemma formalMultilinearSeries_geometric_radius [NormOneClass A] :
    (formalMultilinearSeries_geometric 𝕜 A).radius = 1 :=
  formalMultilinearSeries_geometric_eq_ofScalars 𝕜 A ▸
    FormalMultilinearSeries.ofScalars_radius_eq_of_tendsto (𝕜 := 𝕜) A
      (fun _ : ℕ => (1 : 𝕜)) one_ne_zero
      (Filter.Eventually.of_forall (fun _ : ℕ => (one_ne_zero : (1 : 𝕜) ≠ 0))).frequently
      (by simpa using tendsto_const_nhds (x := (1 : ℝ)))

lemma hasFPowerSeriesOnBall_inverse_one_sub [HasSummableGeomSeries A] :
    HasFPowerSeriesOnBall
      (fun x : {x : A | IsUnit (1 - x)} ↦ (↑x.property.unit⁻¹ : A))
      (formalMultilinearSeries_geometric 𝕜 A)
      ⟨0, by simp⟩ 1 Subtype.val := by
  constructor
  · exact one_le_formalMultilinearSeries_geometric_radius 𝕜 A
  · exact one_pos
  · intro y hy
    have hy' : ‖(y : A)‖ < 1 := by
      simpa only [sub_zero, Metric.mem_eball, edist_dist, dist_zero_right, ofReal_lt_one] using hy
    have hu : y.property.unit = Units.oneSub (y : A) hy' := Units.ext rfl
    simpa only [sub_zero, hu, formalMultilinearSeries_geometric,
      ContinuousMultilinearMap.mkPiAlgebraFin_apply, List.ofFn_const, List.prod_replicate] using
      hasSum_geom_series_inverse (y : A) hy'

@[fun_prop]
lemma analyticAt_inverse_one_sub [HasSummableGeomSeries A] :
    AnalyticAt 𝕜 (fun x : {x : A | IsUnit (1 - x)} ↦ (↑x.property.unit⁻¹ : A))
      ⟨0, by simp⟩ Subtype.val :=
  ⟨_, ⟨_, hasFPowerSeriesOnBall_inverse_one_sub 𝕜 A⟩⟩

/-- The alternating geometric series `1 - x + x ^ 2 - ...` as a `FormalMultilinearSeries`. -/
def alternatingGeometricSeries : FormalMultilinearSeries 𝕜 A A :=
  .ofScalars A fun n ↦ (-1 : 𝕜) ^ n

lemma alternatingGeometricSeries_eq_formalMultilinearSeries_geometric_comp_neg :
    alternatingGeometricSeries 𝕜 A =
    (formalMultilinearSeries_geometric 𝕜 A).compContinuousLinearMap
      (-ContinuousLinearMap.id 𝕜 A) := by
  simp [formalMultilinearSeries_geometric_eq_ofScalars, alternatingGeometricSeries,
    FormalMultilinearSeries.ofScalars_comp_neg_id]

lemma alternatingGeometricSeries_apply_norm_le (n : ℕ) :
    ‖alternatingGeometricSeries 𝕜 A n‖ ≤ max 1 ‖(1 : A)‖ := by
  simpa [alternatingGeometricSeries] using
    ContinuousMultilinearMap.norm_mkPiAlgebraFin_le

lemma alternatingGeometricSeries_apply_norm [NormOneClass A] (n : ℕ) :
    ‖alternatingGeometricSeries 𝕜 A n‖ = 1 := by
  simp [alternatingGeometricSeries]

lemma one_le_alternatingGeometricSeries_radius [Nontrivial A] :
    1 ≤ (alternatingGeometricSeries 𝕜 A).radius := by
  simpa only [FormalMultilinearSeries.radius_compNeg,
    alternatingGeometricSeries_eq_formalMultilinearSeries_geometric_comp_neg]
    using one_le_formalMultilinearSeries_geometric_radius 𝕜 A

lemma alternatingGeometricSeries_radius [NormOneClass A] :
    (alternatingGeometricSeries 𝕜 A).radius = 1 :=
  FormalMultilinearSeries.ofScalars_radius_eq_of_tendsto (𝕜 := 𝕜) A
    (fun n : ℕ => (-1 : 𝕜) ^ n) one_ne_zero
    (Filter.Eventually.of_forall (fun n : ℕ => pow_ne_zero n (neg_ne_zero.mpr
      (one_ne_zero : (1 : 𝕜) ≠ 0)))).frequently
    (by simpa using tendsto_const_nhds (x := (1 : ℝ)))

lemma hasFPowerSeriesOnBall_inverse_one_add [HasSummableGeomSeries A] [Nontrivial A] :
    HasFPowerSeriesOnBall
      (fun x : {x : A | IsUnit (1 + x)} ↦ (↑x.property.unit⁻¹ : A))
      (alternatingGeometricSeries 𝕜 A)
      ⟨0, by simp⟩ 1 Subtype.val := by
  constructor
  · exact one_le_alternatingGeometricSeries_radius 𝕜 A
  · exact one_pos
  · intro y hy
    have hy' : ‖-(y : A)‖ < 1 := by
      simpa only [norm_neg, sub_zero, Metric.mem_eball, edist_dist, dist_zero_right,
        ofReal_lt_one] using hy
    have hu : y.property.unit = Units.oneSub (-(y : A)) hy' := by
      apply Units.ext
      simp only [IsUnit.unit_spec, Units.oneSub, sub_neg_eq_add]
    simpa [sub_zero, hu, alternatingGeometricSeries_eq_formalMultilinearSeries_geometric_comp_neg,
      FormalMultilinearSeries.compContinuousLinearMap_apply, formalMultilinearSeries_geometric,
      ContinuousMultilinearMap.mkPiAlgebraFin_apply, Function.comp_def] using
      hasSum_geom_series_inverse (-(y : A)) hy'

@[fun_prop]
lemma analyticAt_inverse_one_add [HasSummableGeomSeries A] [Nontrivial A] :
    AnalyticAt 𝕜 (fun x : {x : A | IsUnit (1 + x)} ↦ (↑x.property.unit⁻¹ : A))
      ⟨0, by simp⟩ Subtype.val :=
  ⟨_, ⟨_, hasFPowerSeriesOnBall_inverse_one_add 𝕜 A⟩⟩

end Geometric

/-- Inversion is analytic on the group of units, with the algebra as ambient coordinates. -/
@[fun_prop]
lemma analyticAt_inverse [HasSummableGeomSeries A] (z : Aˣ) :
    AnalyticAt 𝕜 (fun y : Aˣ ↦ (↑y⁻¹ : A)) z Units.val := by
  let g : Aˣ → {a : A | IsUnit (1 - a)} := fun y ↦
    ⟨1 - (↑z⁻¹ : A) * y, by
      simpa only [Set.mem_ofPred_eq, _root_.sub_sub_cancel, Units.val_mul]
        using (z⁻¹ * y).isUnit⟩
  have h3 : AnalyticAt 𝕜 (fun y : Aˣ ↦ 1 - (↑z⁻¹ : A) * y) z Units.val :=
    (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)).comp_domain (g := Units.val)
  have hg : AnalyticAt 𝕜
      (fun a : {a : A | IsUnit (1 - a)} ↦ (↑a.property.unit⁻¹ : A)) (g z) Subtype.val := by
    have hz : g z = ⟨0, by simp⟩ := by
      apply Subtype.ext
      simp [g]
    rw [hz]
    exact analyticAt_inverse_one_sub 𝕜 A
  have h2 := hg.comp h3 Units.isOpenEmbedding_val.isEmbedding Topology.IsEmbedding.subtypeVal
  have h := (analyticAt_id.mul (analyticAt_const (v := (↑z⁻¹ : A)))).comp h2
    Units.isOpenEmbedding_val.isEmbedding Topology.IsEmbedding.id
  have heq : (fun y : Aˣ ↦ (↑(g y).property.unit⁻¹ : A) * ↑z⁻¹) =
      (fun y : Aˣ ↦ (↑y⁻¹ : A)) := by
    funext y
    have hu : (g y).property.unit = z⁻¹ * y := by
      apply Units.ext
      simp only [IsUnit.unit_spec, g, _root_.sub_sub_cancel, Units.val_mul]
    simp only [hu, mul_inv_rev, inv_inv, Units.val_mul, mul_assoc, Units.mul_inv, mul_one]
  simpa only [Function.comp_def, Pi.mul_apply, id_eq, heq] using h

lemma analyticOnNhd_inverse [HasSummableGeomSeries A] :
    AnalyticOnNhd 𝕜 (fun y : Aˣ ↦ (↑y⁻¹ : A)) Set.univ Units.val :=
  fun y _ ↦ analyticAt_inverse y

variable (𝕜 𝕝) in
lemma hasFPowerSeriesOnBall_inv_one_sub :
    HasFPowerSeriesOnBall
      (fun x : {x : 𝕝 | IsUnit (1 - x)} ↦ (↑x.property.unit⁻¹ : 𝕝))
      (formalMultilinearSeries_geometric 𝕜 𝕝)
      ⟨0, by simp⟩ 1 Subtype.val :=
  hasFPowerSeriesOnBall_inverse_one_sub 𝕜 𝕝

variable (𝕝) in
@[fun_prop]
lemma analyticAt_inv_one_sub :
    AnalyticAt 𝕜 (fun x : {x : 𝕝 | IsUnit (1 - x)} ↦ (↑x.property.unit⁻¹ : 𝕝))
      ⟨0, by simp⟩ Subtype.val :=
  analyticAt_inverse_one_sub 𝕜 𝕝

variable (𝕜 𝕝) in
lemma hasFPowerSeriesOnBall_inv_one_add :
    HasFPowerSeriesOnBall
      (fun x : {x : 𝕝 | IsUnit (1 + x)} ↦ (↑x.property.unit⁻¹ : 𝕝))
      (alternatingGeometricSeries 𝕜 𝕝)
      ⟨0, by simp⟩ 1 Subtype.val :=
  hasFPowerSeriesOnBall_inverse_one_add 𝕜 𝕝

variable (𝕝) in
@[fun_prop]
lemma analyticAt_inv_one_add :
    AnalyticAt 𝕜 (fun x : {x : 𝕝 | IsUnit (1 + x)} ↦ (↑x.property.unit⁻¹ : 𝕝))
      ⟨0, by simp⟩ Subtype.val :=
  analyticAt_inverse_one_add 𝕜 𝕝

/-- The inverse of a normed field extension is analytic on its units. -/
@[fun_prop]
lemma analyticAt_inv (z : 𝕝ˣ) :
    AnalyticAt 𝕜 (fun y : 𝕝ˣ ↦ (↑y⁻¹ : 𝕝)) z Units.val :=
  analyticAt_inverse z

@[fun_prop]
lemma analyticOnNhd_inv :
    AnalyticOnNhd 𝕜 (fun z : 𝕝ˣ ↦ (↑z⁻¹ : 𝕝)) Set.univ Units.val :=
  fun z _ ↦ analyticAt_inv z

lemma analyticOn_inv :
    AnalyticOn 𝕜 (fun z : 𝕝ˣ ↦ (↑z⁻¹ : 𝕝)) Set.univ Units.val :=
  analyticOnNhd_inv.analyticOn

theorem AnalyticWithinAt.inv {f : E → 𝕝} {x : E} {s : Set E}
    (fa : AnalyticWithinAt 𝕜 f s x) (f0 : IsUnit (f x)) :
    AnalyticWithinAt 𝕜
      (fun y : {y : E | IsUnit (f y)} ↦ (↑y.property.unit⁻¹ : 𝕝))
      (Subtype.val ⁻¹' s) ⟨x, f0⟩ Subtype.val := by
  have h := fa.comp_domain (g := (Subtype.val : {y : E | IsUnit (f y)} → E))
    (x := ⟨x, f0⟩) (t := Subtype.val ⁻¹' s) (fun _ hy => hy)
  exact (analyticAt_inv f0.unit).comp_analyticWithinAt
    (f := fun y : {y : E | IsUnit (f y)} ↦ y.property.unit) h
    Topology.IsEmbedding.subtypeVal Units.isOpenEmbedding_val.isEmbedding

/-- Analytic inversion is defined on the exact invertibility locus of the function. -/
theorem AnalyticAt.inv {f : E → 𝕝} {x : E}
    (fa : AnalyticAt 𝕜 f x) (f0 : IsUnit (f x)) :
    AnalyticAt 𝕜 (fun y : {y : E | IsUnit (f y)} ↦ (↑y.property.unit⁻¹ : 𝕝))
      ⟨x, f0⟩ Subtype.val := by
  have h := fa.comp_domain (g := (Subtype.val : {y : E | IsUnit (f y)} → E))
    (x := ⟨x, f0⟩)
  exact (analyticAt_inv f0.unit).comp
    (f := fun y : {y : E | IsUnit (f y)} ↦ y.property.unit) h
    Topology.IsEmbedding.subtypeVal Units.isOpenEmbedding_val.isEmbedding

/-- An analytic function that is a unit at the center has an analytic reciprocal germ there. -/
theorem AnalyticAt.exists_mul_eq_one {f : E → 𝕝} {x : E}
    (hf : AnalyticAt 𝕜 f x) (hu : IsUnit (f x)) :
    ∃ g : E → 𝕝, AnalyticAt 𝕜 g x ∧ ∀ᶠ y in 𝓝 x, f y * g y = 1 := by
  let V := {y : E | IsUnit (f y)}
  let k : V → 𝕝 := fun y ↦ ↑y.property.unit⁻¹
  let g : E → 𝕝 := Function.extend Subtype.val k 0
  have hg (y : V) : g y = k y := Subtype.val_injective.extend_apply _ _ y
  have hV : V ∈ 𝓝 x := hf.continuousAt.eventually (Units.isOpen.mem_nhds hu)
  refine ⟨g, AnalyticAt.of_comp_domain (coord := Subtype.val) (x := (⟨x, hu⟩ : V)) ?_ ?_, ?_⟩
  · simpa only [Function.comp_def, hg, k] using hf.inv hu
  · simpa only [Subtype.range_coe] using hV
  · filter_upwards [hV] with y hy
    rw [show g y = k ⟨y, hy⟩ from hg ⟨y, hy⟩]
    exact hy.unit.val_inv

theorem AnalyticOn.inv {f : E → 𝕝} {s : Set E} (fa : AnalyticOn 𝕜 f s) :
    AnalyticOn 𝕜 (fun y : {y : E | IsUnit (f y)} ↦ (↑y.property.unit⁻¹ : 𝕝))
      (Subtype.val ⁻¹' s) Subtype.val :=
  fun x hx ↦ (fa x.val hx).inv x.property

theorem AnalyticOnNhd.inv {f : E → 𝕝} {s : Set E} (fa : AnalyticOnNhd 𝕜 f s) :
    AnalyticOnNhd 𝕜 (fun y : {y : E | IsUnit (f y)} ↦ (↑y.property.unit⁻¹ : 𝕝))
      (Subtype.val ⁻¹' s) Subtype.val :=
  fun x hx ↦ (fa x.val hx).inv x.property

/-- Integer powers of an analytic function are analytic on the exact exponent-dependent domain. -/
lemma AnalyticWithinAt.zpow {f : E → 𝕝} {z : E} {s : Set E} {n : ℤ}
    (hf : AnalyticWithinAt 𝕜 f s z) (hz : n < 0 → IsUnit (f z)) :
    AnalyticWithinAt 𝕜
      (fun y : {y : E | n < 0 → IsUnit (f y)} ↦ Checked.zpow (f y.val) n y.property)
      (Subtype.val ⁻¹' s) ⟨z, hz⟩ Subtype.val := by
  cases n with
  | ofNat n =>
    have hp : AnalyticWithinAt 𝕜 (fun y ↦ f y ^ n) s z := by
      simpa only [Pi.pow_def] using hf.pow n
    simpa only [Checked.zpow, Function.comp_def, id_eq] using
      hp.comp_domain (x := ⟨z, hz⟩)
        (g := (Subtype.val : {y : E | Int.ofNat n < 0 → IsUnit (f y)} → E))
        (t := Subtype.val ⁻¹' s) (fun _ hy => hy)
  | negSucc n =>
    let g : {y : E | Int.negSucc n < 0 → IsUnit (f y)} →
        {y : E | IsUnit (f y ^ (n + 1))} := fun y ↦
      ⟨y.val, (y.property (Int.negSucc_lt_zero n)).pow (n + 1)⟩
    have hp : AnalyticWithinAt 𝕜 (fun y ↦ f y ^ (n + 1)) s z := by
      simpa only [Pi.pow_def] using hf.pow (n + 1)
    have h := (hp.inv ((hz (Int.negSucc_lt_zero n)).pow (n + 1))).comp_domain
      (g := g) (x := ⟨z, hz⟩) (t := Subtype.val ⁻¹' s) (fun _ hy => hy)
    have hu (y : {y : E | Int.negSucc n < 0 → IsUnit (f y)}) :
        (g y).property.unit = (y.property (Int.negSucc_lt_zero n)).unit ^ (n + 1) :=
      Units.ext rfl
    simpa only [Checked.zpow, zpow_negSucc, Function.comp_def, hu, g, Set.preimage] using h

/-- Integer powers of an analytic function are analytic on the exact exponent-dependent domain. -/
lemma AnalyticAt.zpow {f : E → 𝕝} {z : E} {n : ℤ}
    (hf : AnalyticAt 𝕜 f z) (hz : n < 0 → IsUnit (f z)) :
    AnalyticAt 𝕜
      (fun y : {y : E | n < 0 → IsUnit (f y)} ↦ Checked.zpow (f y.val) n y.property)
      ⟨z, hz⟩ Subtype.val := by
  cases n with
  | ofNat n =>
    have hp : AnalyticAt 𝕜 (fun y ↦ f y ^ n) z := by
      simpa only [Pi.pow_def] using hf.pow n
    simpa only [Checked.zpow, Function.comp_def, id_eq] using
      hp.comp_domain (x := ⟨z, hz⟩)
        (g := (Subtype.val : {y : E | Int.ofNat n < 0 → IsUnit (f y)} → E))
  | negSucc n =>
    let g : {y : E | Int.negSucc n < 0 → IsUnit (f y)} →
        {y : E | IsUnit (f y ^ (n + 1))} := fun y ↦
      ⟨y.val, (y.property (Int.negSucc_lt_zero n)).pow (n + 1)⟩
    have hp : AnalyticAt 𝕜 (fun y ↦ f y ^ (n + 1)) z := by
      simpa only [Pi.pow_def] using hf.pow (n + 1)
    have h := (hp.inv ((hz (Int.negSucc_lt_zero n)).pow (n + 1))).comp_domain
      (g := g) (x := ⟨z, hz⟩)
    have hu (y : {y : E | Int.negSucc n < 0 → IsUnit (f y)}) :
        (g y).property.unit = (y.property (Int.negSucc_lt_zero n)).unit ^ (n + 1) :=
      Units.ext rfl
    simpa only [Checked.zpow, zpow_negSucc, Function.comp_def, hu, g, Set.preimage] using h

lemma AnalyticOn.zpow {f : E → 𝕝} {s : Set E} {n : ℤ} (hf : AnalyticOn 𝕜 f s) :
    AnalyticOn 𝕜
      (fun y : {y : E | n < 0 → IsUnit (f y)} ↦ Checked.zpow (f y.val) n y.property)
      (Subtype.val ⁻¹' s) Subtype.val :=
  fun y hy ↦ (hf y.val hy).zpow y.property

lemma AnalyticOnNhd.zpow {f : E → 𝕝} {s : Set E} {n : ℤ} (hf : AnalyticOnNhd 𝕜 f s) :
    AnalyticOnNhd 𝕜
      (fun y : {y : E | n < 0 → IsUnit (f y)} ↦ Checked.zpow (f y.val) n y.property)
      (Subtype.val ⁻¹' s) Subtype.val :=
  fun y hy ↦ (hf y.val hy).zpow y.property

/-- A function is analytic at a point iff it is analytic after scalar
  multiplication with a non-vanishing analytic function. -/
theorem analyticAt_iff_analytic_fun_smul [Module 𝕝 F] [IsBoundedSMul 𝕝 F] [IsScalarTower 𝕜 𝕝 F]
    {f : E → 𝕝} {g : E → F} {z : E} (h₁f : AnalyticAt 𝕜 f z) (h₂f : f z ≠ 0) :
    AnalyticAt 𝕜 g z ↔ AnalyticAt 𝕜 (fun z ↦ f z • g z) z := by
  constructor
  · exact fun a ↦ h₁f.smul a
  · intro hprod
    have hz : IsUnit (f z) := isUnit_iff_ne_zero.mpr h₂f
    have hlocal := (h₁f.inv hz).smul
      (hprod.comp_domain (g := (Subtype.val : {y : E | IsUnit (f y)} → E)) (x := ⟨z, hz⟩))
      Topology.IsEmbedding.subtypeVal
    apply AnalyticAt.of_comp_domain (coord := (Subtype.val : {y : E | IsUnit (f y)} → E))
      (x := ⟨z, hz⟩)
    · simpa only [Function.comp_def, Pi.smul_def', smul_smul, IsUnit.val_inv_mul, one_smul]
        using hlocal
    · rw [Subtype.range_val]
      exact h₁f.continuousAt.preimage_mem_nhds (Units.isOpen.mem_nhds hz)

/-- A function is analytic at a point iff it is analytic after scalar
  multiplication with a non-vanishing analytic function. -/
theorem analyticAt_iff_analytic_smul [Module 𝕝 F] [IsBoundedSMul 𝕝 F] [IsScalarTower 𝕜 𝕝 F]
    {f : E → 𝕝} {g : E → F} {z : E} (h₁f : AnalyticAt 𝕜 f z) (h₂f : f z ≠ 0) :
    AnalyticAt 𝕜 g z ↔ AnalyticAt 𝕜 (f • g) z :=
  analyticAt_iff_analytic_fun_smul h₁f h₂f

/-- A function is analytic at a point iff it is analytic after multiplication
with a non-vanishing analytic function. -/
@[to_fun analyticAt_iff_analytic_fun_mul]
theorem analyticAt_iff_analytic_mul {f g : E → 𝕝} {z : E} (h₁f : AnalyticAt 𝕜 f z)
    (h₂f : f z ≠ 0) :
    AnalyticAt 𝕜 g z ↔ AnalyticAt 𝕜 (f * g) z := by
  simp_rw [← smul_eq_mul]
  exact analyticAt_iff_analytic_smul h₁f h₂f

/-- Analytic division on the exact invertibility locus of the denominator. -/
theorem AnalyticWithinAt.div {f g : E → 𝕝} {s : Set E} {x : E}
    (fa : AnalyticWithinAt 𝕜 f s x) (ga : AnalyticWithinAt 𝕜 g s x) (g0 : IsUnit (g x)) :
    AnalyticWithinAt 𝕜 (fun y : {y : E | IsUnit (g y)} ↦ f y.val /ₚ y.property.unit)
      (Subtype.val ⁻¹' s) ⟨x, g0⟩ Subtype.val := by
  have hf := fa.comp_domain (g := (Subtype.val : {y : E | IsUnit (g y)} → E))
    (x := ⟨x, g0⟩) (t := Subtype.val ⁻¹' s) (fun _ hy => hy)
  exact hf.mul (ga.inv g0) Topology.IsEmbedding.subtypeVal

/-- Analytic division on the exact invertibility locus of the denominator. -/
theorem AnalyticAt.div {f g : E → 𝕝} {x : E}
    (fa : AnalyticAt 𝕜 f x) (ga : AnalyticAt 𝕜 g x) (g0 : IsUnit (g x)) :
    AnalyticAt 𝕜 (fun y : {y : E | IsUnit (g y)} ↦ f y.val /ₚ y.property.unit)
      ⟨x, g0⟩ Subtype.val := by
  have hf := fa.comp_domain (g := (Subtype.val : {y : E | IsUnit (g y)} → E))
    (x := ⟨x, g0⟩)
  exact hf.mul (ga.inv g0) Topology.IsEmbedding.subtypeVal

/-- Analytic division on the exact invertibility locus of the denominator. -/
theorem AnalyticOn.div {f g : E → 𝕝} {s : Set E}
    (fa : AnalyticOn 𝕜 f s) (ga : AnalyticOn 𝕜 g s) :
    AnalyticOn 𝕜 (fun y : {y : E | IsUnit (g y)} ↦ f y.val /ₚ y.property.unit)
      (Subtype.val ⁻¹' s) Subtype.val :=
  fun y hy ↦ (fa y.val hy).div (ga y.val hy) y.property

/-- Analytic division on the exact invertibility locus of the denominator. -/
theorem AnalyticOnNhd.div {f g : E → 𝕝} {s : Set E}
    (fa : AnalyticOnNhd 𝕜 f s) (ga : AnalyticOnNhd 𝕜 g s) :
    AnalyticOnNhd 𝕜 (fun y : {y : E | IsUnit (g y)} ↦ f y.val /ₚ y.property.unit)
      (Subtype.val ⁻¹' s) Subtype.val :=
  fun y hy ↦ (fa y.val hy).div (ga y.val hy) y.property

/-!
### Finite sums and products of analytic functions
-/

/-- Finite sums of analytic functions are analytic -/
@[to_fun Finset.analyticWithinAt_fun_sum]
theorem Finset.analyticWithinAt_sum {f : α → E → F} {c : E} {s : Set E}
    (N : Finset α) (h : ∀ n ∈ N, AnalyticWithinAt 𝕜 (f n) s c) :
    AnalyticWithinAt 𝕜 (∑ n ∈ N, f n) s c := by
  classical
  induction N using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    exact analyticWithinAt_const
  | insert a B aB hB =>
    simp_rw [Finset.sum_insert aB]
    simp only [Finset.mem_insert] at h
    exact (h a (Or.inl rfl)).add (hB fun b m ↦ h b (Or.inr m))

/-- Finite sums of analytic functions are analytic -/
@[to_fun (attr := fun_prop) Finset.analyticAt_fun_sum]
theorem Finset.analyticAt_sum {f : α → E → F} {c : E}
    (N : Finset α) (h : ∀ n ∈ N, AnalyticAt 𝕜 (f n) c) :
    AnalyticAt 𝕜 (∑ n ∈ N, f n) c := by
  simp_rw [← analyticWithinAt_univ] at h ⊢
  exact N.analyticWithinAt_sum h

/-- Finite sums of analytic functions are analytic -/
@[to_fun Finset.analyticOn_fun_sum]
theorem Finset.analyticOn_sum {f : α → E → F} {s : Set E}
    (N : Finset α) (h : ∀ n ∈ N, AnalyticOn 𝕜 (f n) s) :
    AnalyticOn 𝕜 (∑ n ∈ N, f n) s :=
  fun z zs ↦ N.analyticWithinAt_sum (fun n m ↦ h n m z zs)

/-- Finite sums of analytic functions are analytic -/
@[to_fun (attr := fun_prop) Finset.analyticOnNhd_fun_sum]
theorem Finset.analyticOnNhd_sum {f : α → E → F} {s : Set E}
    (N : Finset α) (h : ∀ n ∈ N, AnalyticOnNhd 𝕜 (f n) s) :
    AnalyticOnNhd 𝕜 (∑ n ∈ N, f n) s :=
  fun z zs ↦ N.analyticAt_sum (fun n m ↦ h n m z zs)

/-- Finite products of analytic functions are analytic -/
theorem Finset.analyticWithinAt_fun_prod {A : Type*} [NormedCommRing A] [NormedAlgebra 𝕜 A]
    {f : α → E → A} {c : E} {s : Set E} (N : Finset α) (h : ∀ n ∈ N, AnalyticWithinAt 𝕜 (f n) s c) :
    AnalyticWithinAt 𝕜 (fun z ↦ ∏ n ∈ N, f n z) s c := by
  classical
  induction N using Finset.induction with
  | empty =>
    simp only [Finset.prod_empty]
    exact analyticWithinAt_const
  | insert a B aB hB =>
    simp_rw [Finset.prod_insert aB]
    simp only [Finset.mem_insert] at h
    exact (h a (Or.inl rfl)).mul (hB fun b m ↦ h b (Or.inr m))

/-- Finite products of analytic functions are analytic -/
theorem Finset.analyticWithinAt_prod {A : Type*} [NormedCommRing A] [NormedAlgebra 𝕜 A]
    {f : α → E → A} {c : E} {s : Set E} (N : Finset α) (h : ∀ n ∈ N, AnalyticWithinAt 𝕜 (f n) s c) :
    AnalyticWithinAt 𝕜 (∏ n ∈ N, f n) s c := by
  convert! N.analyticWithinAt_fun_prod h
  simp

/-- Finite products of analytic functions are analytic -/
@[fun_prop]
theorem Finset.analyticAt_fun_prod {A : Type*} [NormedCommRing A] [NormedAlgebra 𝕜 A]
    {f : α → E → A} {c : E} (N : Finset α) (h : ∀ n ∈ N, AnalyticAt 𝕜 (f n) c) :
    AnalyticAt 𝕜 (fun z ↦ ∏ n ∈ N, f n z) c := by
  simp_rw [← analyticWithinAt_univ] at h ⊢
  exact N.analyticWithinAt_fun_prod h

/-- Finite products of analytic functions are analytic -/
@[fun_prop]
theorem Finset.analyticAt_prod {α : Type*} {A : Type*} [NormedCommRing A] [NormedAlgebra 𝕜 A]
    {f : α → E → A} {c : E} (N : Finset α) (h : ∀ n ∈ N, AnalyticAt 𝕜 (f n) c) :
    AnalyticAt 𝕜 (∏ n ∈ N, f n) c := by
  convert! N.analyticAt_fun_prod h
  simp

/-- Finite products of analytic functions are analytic -/
theorem Finset.analyticOn_fun_prod {A : Type*} [NormedCommRing A] [NormedAlgebra 𝕜 A]
    {f : α → E → A} {s : Set E} (N : Finset α) (h : ∀ n ∈ N, AnalyticOn 𝕜 (f n) s) :
    AnalyticOn 𝕜 (fun z ↦ ∏ n ∈ N, f n z) s :=
  fun z zs ↦ N.analyticWithinAt_fun_prod (fun n m ↦ h n m z zs)

/-- Finite products of analytic functions are analytic -/
theorem Finset.analyticOn_prod {A : Type*} [NormedCommRing A] [NormedAlgebra 𝕜 A]
    {f : α → E → A} {s : Set E} (N : Finset α) (h : ∀ n ∈ N, AnalyticOn 𝕜 (f n) s) :
    AnalyticOn 𝕜 (∏ n ∈ N, f n) s :=
  fun z zs ↦ N.analyticWithinAt_prod (fun n m ↦ h n m z zs)

/-- Finite products of analytic functions are analytic -/
@[fun_prop]
theorem Finset.analyticOnNhd_fun_prod {A : Type*} [NormedCommRing A] [NormedAlgebra 𝕜 A]
    {f : α → E → A} {s : Set E} (N : Finset α) (h : ∀ n ∈ N, AnalyticOnNhd 𝕜 (f n) s) :
    AnalyticOnNhd 𝕜 (fun z ↦ ∏ n ∈ N, f n z) s :=
  fun z zs ↦ N.analyticAt_fun_prod (fun n m ↦ h n m z zs)

/-- Finite products of analytic functions are analytic -/
@[fun_prop]
theorem Finset.analyticOnNhd_prod {A : Type*} [NormedCommRing A] [NormedAlgebra 𝕜 A]
    {f : α → E → A} {s : Set E} (N : Finset α) (h : ∀ n ∈ N, AnalyticOnNhd 𝕜 (f n) s) :
    AnalyticOnNhd 𝕜 (∏ n ∈ N, f n) s :=
  fun z zs ↦ N.analyticAt_prod (fun n m ↦ h n m z zs)

/-- Finproducts of analytic functions are analytic -/
@[fun_prop]
theorem analyticAt_finprod {α : Type*} {A : Type*} [NormedCommRing A] [NormedAlgebra 𝕜 A]
    {f : α → E → A} {c : E} (h : ∀ a, AnalyticAt 𝕜 (f a) c) :
    AnalyticAt 𝕜 (∏ᶠ n, f n) c := by
  by_cases hf : (Function.mulSupport f).Finite
  · simp_all [finprod_eq_prod _ hf, Finset.analyticAt_prod]
  · rw [finprod_of_infinite_mulSupport hf]
    apply analyticAt_const

/-!
### Unshifting
-/

section

variable {f : E → (E →L[𝕜] F)} {pf : FormalMultilinearSeries 𝕜 E (E →L[𝕜] F)} {s : Set E} {x : E}
  {r : ℝ≥0∞} {z : F}

theorem HasFPowerSeriesWithinOnBall.unshift (hf : HasFPowerSeriesWithinOnBall f pf s x r) :
    HasFPowerSeriesWithinOnBall (fun y ↦ z + f y (y - x)) (pf.unshift z) s x r where
  r_le := by
    rw [FormalMultilinearSeries.radius_unshift]
    exact hf.r_le
  r_pos := hf.r_pos
  hasSum := by
    intro y hy h'y
    apply HasSum.zero_add
    simp only [FormalMultilinearSeries.unshift, Nat.succ_eq_add_one,
      continuousMultilinearCurryRightEquiv_symm_apply']
    exact (ContinuousLinearMap.apply 𝕜 F (y - x)).hasSum (hf.hasSum hy h'y)

theorem HasFPowerSeriesOnBall.unshift (hf : HasFPowerSeriesOnBall f pf x r) :
    HasFPowerSeriesOnBall (fun y ↦ z + f y (y - x)) (pf.unshift z) x r where
  r_le := by
    rw [FormalMultilinearSeries.radius_unshift]
    exact hf.r_le
  r_pos := hf.r_pos
  hasSum := by
    intro y hy
    apply HasSum.zero_add
    simp only [FormalMultilinearSeries.unshift, Nat.succ_eq_add_one,
      continuousMultilinearCurryRightEquiv_symm_apply']
    exact (ContinuousLinearMap.apply 𝕜 F (y - x)).hasSum (hf.hasSum hy)

theorem HasFPowerSeriesWithinAt.unshift (hf : HasFPowerSeriesWithinAt f pf s x) :
    HasFPowerSeriesWithinAt (fun y ↦ z + f y (y - x)) (pf.unshift z) s x :=
  let ⟨_, hrf⟩ := hf
  hrf.unshift.hasFPowerSeriesWithinAt

end
