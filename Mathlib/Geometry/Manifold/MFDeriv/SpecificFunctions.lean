/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
public import Mathlib.Geometry.Manifold.Notation

/-!
# Differentiability of specific functions

In this file, we establish differentiability results for
- continuous linear maps and continuous linear equivalences
- the identity
- constant functions
- products
- arithmetic operations (such as addition and scalar multiplication).

-/

public section

noncomputable section

open scoped Manifold
open Bundle Set Topology

section SpecificFunctions

/-! ### Differentiability of specific functions -/

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  -- declare a charted space `M` over the pair `(E, H)`.
  {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type*}
  [TopologicalSpace M] [ChartedSpace H M]
  -- declare a charted space `M'` over the pair `(E', H')`.
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  -- declare a charted space `M''` over the pair `(E'', H'')`.
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''} {M'' : Type*}
  [TopologicalSpace M''] [ChartedSpace H'' M'']
  -- declare a charted space `N` over the pair `(F, G)`.
  {F : Type*}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type*} [TopologicalSpace G]
  {J : ModelWithCorners 𝕜 F G} {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  -- declare a charted space `N'` over the pair `(F', G')`.
  {F' : Type*}
  [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] {G' : Type*} [TopologicalSpace G']
  {J' : ModelWithCorners 𝕜 F' G'} {N' : Type*} [TopologicalSpace N'] [ChartedSpace G' N']

namespace ContinuousLinearMap

variable (f : E →L[𝕜] E') {s : Set E} {x : E}

protected theorem hasMFDerivWithinAt : HasMFDerivAt[s] f x f :=
  f.hasFDerivWithinAt.hasMFDerivWithinAt

protected theorem hasMFDerivAt : HasMFDerivAt% f x f :=
  f.hasFDerivAt.hasMFDerivAt

protected theorem mdifferentiableWithinAt : MDiffAt[s] f x :=
  f.differentiableWithinAt.mdifferentiableWithinAt

protected theorem mdifferentiableOn : MDiff[s] f :=
  f.differentiableOn.mdifferentiableOn

protected theorem mdifferentiableAt : MDiffAt f x :=
  f.differentiableAt.mdifferentiableAt

protected theorem mdifferentiable : MDiff f :=
  f.differentiable.mdifferentiable

theorem mfderiv_eq : mfderiv% f x = f :=
  f.hasMFDerivAt.mfderiv

theorem mfderivWithin_eq (hs : UniqueMDiffAt[s] x) : mfderiv[s] f x = f :=
  f.hasMFDerivWithinAt.mfderivWithin hs

end ContinuousLinearMap

namespace ContinuousLinearEquiv

variable (f : E ≃L[𝕜] E') {s : Set E} {x : E}

protected theorem hasMFDerivWithinAt : HasMFDerivAt[s] f x (f : E →L[𝕜] E') :=
  f.hasFDerivWithinAt.hasMFDerivWithinAt

protected theorem hasMFDerivAt : HasMFDerivAt% f x (f : E →L[𝕜] E') :=
  f.hasFDerivAt.hasMFDerivAt

protected theorem mdifferentiableWithinAt : MDiffAt[s] f x :=
  f.differentiableWithinAt.mdifferentiableWithinAt

protected theorem mdifferentiableOn : MDiff[s] f :=
  f.differentiableOn.mdifferentiableOn

protected theorem mdifferentiableAt : MDiffAt f x :=
  f.differentiableAt.mdifferentiableAt

protected theorem mdifferentiable : MDiff f :=
  f.differentiable.mdifferentiable

theorem mfderiv_eq : mfderiv% f x = (f : E →L[𝕜] E') :=
  f.hasMFDerivAt.mfderiv

theorem mfderivWithin_eq (hs : UniqueMDiffAt[s] x) :
    mfderiv[s] f x = (f : E →L[𝕜] E') :=
  f.hasMFDerivWithinAt.mfderivWithin hs

end ContinuousLinearEquiv

variable {s : Set M} {x : M}

section id

/-! #### Identity -/

theorem hasMFDerivAt_id (x : M) :
    HasMFDerivAt% (@id M) x (ContinuousLinearMap.id 𝕜 (TangentSpace% x)) := by
  refine ⟨continuousAt_id, ?_⟩
  have : ∀ᶠ y in 𝓝[range I] (extChartAt I x) x, (extChartAt I x ∘ (extChartAt I x).symm) y = y := by
    apply Filter.mem_of_superset (extChartAt_target_mem_nhdsWithin x)
    mfld_set_tac
  apply HasFDerivWithinAt.congr_of_eventuallyEq (hasFDerivWithinAt_id _ _) this
  simp only [mfld_simps]

theorem hasMFDerivWithinAt_id (s : Set M) (x : M) :
    HasMFDerivAt[s] (@id M) x (ContinuousLinearMap.id 𝕜 (TangentSpace% x)) :=
  (hasMFDerivAt_id x).hasMFDerivWithinAt

theorem mdifferentiableAt_id : MDiffAt (@id M) x :=
  (hasMFDerivAt_id x).mdifferentiableAt

theorem mdifferentiableWithinAt_id : MDiffAt[s] (@id M) x :=
  mdifferentiableAt_id.mdifferentiableWithinAt

theorem mdifferentiable_id : MDiff (@id M) := fun _ ↦ mdifferentiableAt_id

theorem mdifferentiableOn_id : MDiff[s] (@id M) :=
  mdifferentiable_id.mdifferentiableOn

@[simp, mfld_simps]
theorem mfderiv_id : mfderiv% (@id M) x = ContinuousLinearMap.id 𝕜 (TangentSpace% x) :=
  (hasMFDerivAt_id x).mfderiv

theorem mfderivWithin_id (hxs : UniqueMDiffAt[s] x) :
    mfderiv[s] (@id M) x = ContinuousLinearMap.id 𝕜 (TangentSpace% x) := by
  rw [MDifferentiable.mfderivWithin mdifferentiableAt_id hxs]
  exact mfderiv_id

@[simp, mfld_simps]
theorem tangentMap_id : tangentMap% (@id M) = id := by ext1 ⟨x, v⟩; simp [tangentMap]

theorem tangentMapWithin_id {p : TangentBundle I M} (hs : UniqueMDiffAt[s] p.proj) :
    tangentMap[s] (id : M → M) p = p := by
  simp only [tangentMapWithin, id]
  rw [mfderivWithin_id]
  · rcases p with ⟨⟩; rfl
  · exact hs

end id

section Const

/-! #### Constants -/


variable {c : M'}

theorem hasMFDerivAt_const (c : M') (x : M) :
    HasMFDerivAt% (fun _ : M ↦ c) x (0 : TangentSpace% x →L[𝕜] TangentSpace% c) :=
  ⟨by fun_prop, by simp [Function.comp_def, hasFDerivWithinAt_const]⟩

theorem hasMFDerivWithinAt_const (c : M') (s : Set M) (x : M) :
    HasMFDerivAt[s] (fun _ : M ↦ c) x (0 : TangentSpace% x →L[𝕜] TangentSpace% c) :=
  (hasMFDerivAt_const c x).hasMFDerivWithinAt

theorem mdifferentiableAt_const : MDiffAt (fun _ : M ↦ c) x :=
  (hasMFDerivAt_const c x).mdifferentiableAt

theorem mdifferentiableWithinAt_const : MDiffAt[s] (fun _ : M ↦ c) x :=
  mdifferentiableAt_const.mdifferentiableWithinAt

theorem mdifferentiable_const : MDiff fun _ : M ↦ c := fun _ ↦ mdifferentiableAt_const

theorem mdifferentiableOn_const : MDiff[s] (fun _ : M ↦ c) :=
  mdifferentiable_const.mdifferentiableOn

@[simp, mfld_simps]
theorem mfderiv_const :
    mfderiv% (fun _ : M ↦ c) x = (0 : TangentSpace% x →L[𝕜] TangentSpace% c) :=
  (hasMFDerivAt_const c x).mfderiv

theorem mfderivWithin_const :
    mfderiv[s] (fun _ : M ↦ c) x = (0 : TangentSpace% x →L[𝕜] TangentSpace% c) :=
  (hasMFDerivWithinAt_const _ _ _).mfderivWithin_eq_zero

end Const

section Prod

/-! ### Operations on the product of two manifolds -/

theorem MDifferentiableWithinAt.prodMk {f : M → M'} {g : M → M''}
    (hf : MDiffAt[s] f x) (hg : MDiffAt[s] g x) :
    MDiffAt[s] (fun x ↦ (f x, g x)) x :=
  ⟨hf.1.prodMk hg.1, hf.2.prodMk hg.2⟩

/-- If `f` and `g` have derivatives `df` and `dg` within `s` at `x`, respectively,
then `x ↦ (f x, g x)` has derivative `df.prod dg` within `s`. -/
theorem HasMFDerivWithinAt.prodMk {f : M → M'} {g : M → M''}
    {df : TangentSpace% x →L[𝕜] TangentSpace% (f x)} (hf : HasMFDerivAt[s] f x df)
    {dg : TangentSpace% x →L[𝕜] TangentSpace% (g x)} (hg : HasMFDerivAt[s] g x dg) :
    HasMFDerivAt[s] (fun y ↦ (f y, g y)) x (df.prod dg) :=
  ⟨hf.1.prodMk hg.1, hf.2.prodMk hg.2⟩

lemma mfderivWithin_prodMk {f : M → M'} {g : M → M''} (hf : MDiffAt[s] f x) (hg : MDiffAt[s] g x)
    (hs : UniqueMDiffAt[s] x) :
    mfderiv[s] (fun x ↦ (f x, g x)) x = (mfderiv[s] f x).prod (mfderiv[s] g x) :=
  (hf.hasMFDerivWithinAt.prodMk hg.hasMFDerivWithinAt).mfderivWithin hs

lemma mfderiv_prodMk {f : M → M'} {g : M → M''} (hf : MDiffAt f x) (hg : MDiffAt g x) :
    mfderiv% (fun x ↦ (f x, g x)) x = (mfderiv% f x).prod (mfderiv% g x) := by
  simp_rw [← mfderivWithin_univ]
  exact mfderivWithin_prodMk hf.mdifferentiableWithinAt hg.mdifferentiableWithinAt
    (uniqueMDiffWithinAt_univ I)

theorem MDifferentiableAt.prodMk {f : M → M'} {g : M → M''} (hf : MDiffAt f x) (hg : MDiffAt g x) :
    MDiffAt (fun x ↦ (f x, g x)) x :=
  ⟨hf.1.prodMk hg.1, hf.2.prodMk hg.2⟩

/-- If `f` and `g` have derivatives `df` and `dg` at `x`, respectively,
then `x ↦ (f x, g x)` has derivative `df.prod dg`. -/
theorem HasMFDerivAt.prodMk {f : M → M'} {g : M → M''}
    {df : TangentSpace% x →L[𝕜] TangentSpace% (f x)} (hf : HasMFDerivAt% f x df)
    {dg : TangentSpace% x →L[𝕜] TangentSpace% (g x)} (hg : HasMFDerivAt% g x dg) :
    HasMFDerivAt% (fun y ↦ (f y, g y)) x (df.prod dg) :=
  ⟨hf.1.prodMk hg.1, hf.2.prodMk hg.2⟩

theorem MDifferentiableWithinAt.prodMk_space {f : M → E'} {g : M → E''}
    (hf : MDiffAt[s] f x) (hg : MDiffAt[s] g x) :
    MDifferentiableWithinAt I 𝓘(𝕜, E' × E'') (fun x ↦ (f x, g x)) s x :=
  ⟨hf.1.prodMk hg.1, hf.2.prodMk hg.2⟩

theorem MDifferentiableAt.prodMk_space {f : M → E'} {g : M → E''}
    (hf : MDiffAt f x) (hg : MDiffAt g x) :
    MDifferentiableAt I 𝓘(𝕜, E' × E'') (fun x ↦ (f x, g x)) x :=
  ⟨hf.1.prodMk hg.1, hf.2.prodMk hg.2⟩

theorem MDifferentiableOn.prodMk {f : M → M'} {g : M → M''} (hf : MDiff[s] f) (hg : MDiff[s] g) :
    MDiff[s] (fun x ↦ (f x, g x)) := fun x hx ↦ (hf x hx).prodMk (hg x hx)

theorem MDifferentiable.prodMk {f : M → M'} {g : M → M''} (hf : MDiff f) (hg : MDiff g) :
    MDiff fun x ↦ (f x, g x) := fun x ↦ (hf x).prodMk (hg x)

theorem MDifferentiableOn.prodMk_space {f : M → E'} {g : M → E''}
    (hf : MDiff[s] f) (hg : MDiff[s] g) :
    MDifferentiableOn I 𝓘(𝕜, E' × E'') (fun x ↦ (f x, g x)) s :=
  fun x hx ↦ (hf x hx).prodMk_space (hg x hx)

theorem MDifferentiable.prodMk_space {f : M → E'} {g : M → E''} (hf : MDiff f) (hg : MDiff g) :
    MDifferentiable I 𝓘(𝕜, E' × E'') fun x ↦ (f x, g x) :=
fun x ↦ (hf x).prodMk_space (hg x)

theorem hasMFDerivAt_fst (x : M × M') :
    HasMFDerivAt% (@Prod.fst M M') x
      (ContinuousLinearMap.fst 𝕜 (TangentSpace% x.1) (TangentSpace% x.2)) := by
  refine ⟨continuous_fst.continuousAt, ?_⟩
  have :
    ∀ᶠ y in 𝓝[range (I.prod I')] extChartAt (I.prod I') x x,
      (extChartAt I x.1 ∘ Prod.fst ∘ (extChartAt (I.prod I') x).symm) y = y.1 := by
    /- porting note: was
    apply Filter.mem_of_superset (extChartAt_target_mem_nhdsWithin (I.prod I') x)
    mfld_set_tac
    -/
    filter_upwards [extChartAt_target_mem_nhdsWithin x] with y hy
    rw [extChartAt_prod] at hy
    exact (extChartAt I x.1).right_inv hy.1
  apply HasFDerivWithinAt.congr_of_eventuallyEq hasFDerivWithinAt_fst this
  -- Porting note: next line was `simp only [mfld_simps]`
  exact (extChartAt I x.1).right_inv <| (extChartAt I x.1).map_source (mem_extChartAt_source _)

theorem hasMFDerivWithinAt_fst (s : Set (M × M')) (x : M × M') :
    HasMFDerivAt[s] (@Prod.fst M M') x
      (ContinuousLinearMap.fst 𝕜 (TangentSpace% x.1) (TangentSpace% x.2)) :=
  (hasMFDerivAt_fst x).hasMFDerivWithinAt

theorem mdifferentiableAt_fst {x : M × M'} : MDiffAt (@Prod.fst M M') x :=
  (hasMFDerivAt_fst x).mdifferentiableAt

theorem mdifferentiableWithinAt_fst {s : Set (M × M')} {x : M × M'} :
    MDiffAt[s] (@Prod.fst M M') x :=
  mdifferentiableAt_fst.mdifferentiableWithinAt

theorem mdifferentiable_fst : MDiff (@Prod.fst M M') := fun _ ↦ mdifferentiableAt_fst

theorem mdifferentiableOn_fst {s : Set (M × M')} : MDiff[s] (@Prod.fst M M') :=
  mdifferentiable_fst.mdifferentiableOn

@[simp, mfld_simps]
theorem mfderiv_fst {x : M × M'} :
    mfderiv% (@Prod.fst M M') x =
      ContinuousLinearMap.fst 𝕜 (TangentSpace% x.1) (TangentSpace% x.2) :=
  (hasMFDerivAt_fst x).mfderiv

theorem mfderivWithin_fst {s : Set (M × M')} {x : M × M'}
    (hxs : UniqueMDiffAt[s] x) :
    mfderiv[s] (@Prod.fst M M') x =
      ContinuousLinearMap.fst 𝕜 (TangentSpace% x.1) (TangentSpace% x.2) := by
  rw [MDifferentiable.mfderivWithin mdifferentiableAt_fst hxs]; exact mfderiv_fst

@[simp, mfld_simps]
theorem tangentMap_prodFst {p : TangentBundle (I.prod I') (M × M')} :
    tangentMap% (@Prod.fst M M') p = ⟨p.proj.1, p.2.1⟩ := by
  simp [tangentMap]; rfl

theorem tangentMapWithin_prodFst {s : Set (M × M')} {p : TangentBundle (I.prod I') (M × M')}
    (hs : UniqueMDiffAt[s] p.proj) :
    tangentMap[s] (@Prod.fst M M') p = ⟨p.proj.1, p.2.1⟩ := by
  simp only [tangentMapWithin]
  rw [mfderivWithin_fst]
  · rcases p with ⟨⟩; rfl
  · exact hs

theorem hasMFDerivAt_snd (x : M × M') :
    HasMFDerivAt% (@Prod.snd M M') x
      (ContinuousLinearMap.snd 𝕜 (TangentSpace% x.1) (TangentSpace% x.2)) := by
  refine ⟨continuous_snd.continuousAt, ?_⟩
  have :
    ∀ᶠ y in 𝓝[range (I.prod I')] extChartAt (I.prod I') x x,
      (extChartAt I' x.2 ∘ Prod.snd ∘ (extChartAt (I.prod I') x).symm) y = y.2 := by
    /- porting note: was
    apply Filter.mem_of_superset (extChartAt_target_mem_nhdsWithin (I.prod I') x)
    mfld_set_tac
    -/
    filter_upwards [extChartAt_target_mem_nhdsWithin x] with y hy
    rw [extChartAt_prod] at hy
    exact (extChartAt I' x.2).right_inv hy.2
  apply HasFDerivWithinAt.congr_of_eventuallyEq hasFDerivWithinAt_snd this
  -- Porting note: the next line was `simp only [mfld_simps]`
  exact (extChartAt I' x.2).right_inv <| (extChartAt I' x.2).map_source (mem_extChartAt_source _)

theorem hasMFDerivWithinAt_snd (s : Set (M × M')) (x : M × M') :
    HasMFDerivAt[s] (@Prod.snd M M') x
      (ContinuousLinearMap.snd 𝕜 (TangentSpace% x.1) (TangentSpace% x.2)) :=
  (hasMFDerivAt_snd x).hasMFDerivWithinAt

theorem mdifferentiableAt_snd {x : M × M'} : MDiffAt (@Prod.snd M M') x :=
  (hasMFDerivAt_snd x).mdifferentiableAt

theorem mdifferentiableWithinAt_snd {s : Set (M × M')} {x : M × M'} :
    MDiffAt[s] (@Prod.snd M M') x := mdifferentiableAt_snd.mdifferentiableWithinAt

theorem mdifferentiable_snd : MDiff (@Prod.snd M M') := fun _ ↦ mdifferentiableAt_snd

theorem mdifferentiableOn_snd {s : Set (M × M')} : MDiff[s] (@Prod.snd M M') :=
  mdifferentiable_snd.mdifferentiableOn

@[simp, mfld_simps]
theorem mfderiv_snd {x : M × M'} :
    mfderiv% (@Prod.snd M M') x =
      ContinuousLinearMap.snd 𝕜 (TangentSpace% x.1) (TangentSpace% x.2) :=
  (hasMFDerivAt_snd x).mfderiv

theorem mfderivWithin_snd {s : Set (M × M')} {x : M × M'}
    (hxs : UniqueMDiffAt[s] x) :
    mfderiv[s] (@Prod.snd M M') x =
      ContinuousLinearMap.snd 𝕜 (TangentSpace% x.1) (TangentSpace% x.2) := by
  rw [MDifferentiable.mfderivWithin mdifferentiableAt_snd hxs]; exact mfderiv_snd

theorem MDifferentiableWithinAt.fst {f : N → M × M'} {s : Set N} {x : N}
    (hf : MDiffAt[s] f x) : MDiffAt[s] (fun x ↦ (f x).1) x :=
  mdifferentiableAt_fst.comp_mdifferentiableWithinAt x hf

theorem MDifferentiableAt.fst {f : N → M × M'} {x : N} (hf : MDiffAt f x) :
    MDiffAt (fun x ↦ (f x).1) x :=
  mdifferentiableAt_fst.comp x hf

theorem MDifferentiable.fst {f : N → M × M'} (hf : MDiff f) : MDiff fun x ↦ (f x).1 :=
  mdifferentiable_fst.comp hf

theorem MDifferentiableWithinAt.snd {f : N → M × M'} {s : Set N} {x : N} (hf : MDiffAt[s] f x) :
    MDiffAt[s] (fun x ↦ (f x).2) x :=
  mdifferentiableAt_snd.comp_mdifferentiableWithinAt x hf

theorem MDifferentiableAt.snd {f : N → M × M'} {x : N} (hf : MDiffAt f x) :
    MDiffAt (fun x ↦ (f x).2) x :=
  mdifferentiableAt_snd.comp x hf

theorem MDifferentiable.snd {f : N → M × M'} (hf : MDiff f) : MDiff fun x ↦ (f x).2 :=
  mdifferentiable_snd.comp hf

theorem mdifferentiableWithinAt_prod_iff (f : M → M' × N') :
    MDiffAt[s] f x ↔ MDiffAt[s] (Prod.fst ∘ f) x ∧ MDiffAt[s] (Prod.snd ∘ f) x :=
  ⟨fun h ↦ ⟨h.fst, h.snd⟩, fun h ↦ h.1.prodMk h.2⟩

section prod_module

-- `F₁` and `F₂` are normed spaces.
variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {s : Set M} {x : M}

theorem mdifferentiableWithinAt_prod_module_iff (f : M → F₁ × F₂) :
    MDifferentiableWithinAt I 𝓘(𝕜, F₁ × F₂) f s x ↔
      MDiffAt[s] (Prod.fst ∘ f) x ∧ MDiffAt[s] (Prod.snd ∘ f) x := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact mdifferentiableWithinAt_prod_iff f

theorem mdifferentiableAt_prod_iff (f : M → M' × N') :
    MDiffAt f x ↔ MDiffAt (Prod.fst ∘ f) x ∧ MDiffAt (Prod.snd ∘ f) x := by
  simp_rw [← mdifferentiableWithinAt_univ]; exact mdifferentiableWithinAt_prod_iff f

theorem mdifferentiableAt_prod_module_iff (f : M → F₁ × F₂) :
    MDifferentiableAt I 𝓘(𝕜, F₁ × F₂) f x ↔
      MDiffAt (Prod.fst ∘ f) x ∧ MDiffAt (Prod.snd ∘ f) x := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact mdifferentiableAt_prod_iff f

theorem mdifferentiableOn_prod_iff (f : M → M' × N') :
    MDiff[s] f ↔ MDiff[s] (Prod.fst ∘ f) ∧ MDiff[s] (Prod.snd ∘ f) :=
  ⟨fun h ↦ ⟨fun x hx ↦ ((mdifferentiableWithinAt_prod_iff f).1 (h x hx)).1,
      fun x hx ↦ ((mdifferentiableWithinAt_prod_iff f).1 (h x hx)).2⟩,
    fun h x hx ↦ (mdifferentiableWithinAt_prod_iff f).2 ⟨h.1 x hx, h.2 x hx⟩⟩

theorem mdifferentiableOn_prod_module_iff (f : M → F₁ × F₂) :
    MDifferentiableOn I 𝓘(𝕜, F₁ × F₂) f s ↔ MDiff[s] (Prod.fst ∘ f) ∧ MDiff[s] (Prod.snd ∘ f) := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact mdifferentiableOn_prod_iff f

theorem mdifferentiable_prod_iff (f : M → M' × N') :
    MDiff f ↔ MDiff (Prod.fst ∘ f) ∧ MDiff (Prod.snd ∘ f) :=
  ⟨fun h ↦ ⟨h.fst, h.snd⟩, fun h ↦ by convert! h.1.prodMk h.2⟩

theorem mdifferentiable_prod_module_iff (f : M → F₁ × F₂) :
    MDifferentiable I 𝓘(𝕜, F₁ × F₂) f ↔ MDiff (Prod.fst ∘ f) ∧ MDiff (Prod.snd ∘ f) := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact mdifferentiable_prod_iff f

end prod_module


section prodMap

variable {f : M → M'} {g : N → N'} {r : Set N} {y : N}

/-- The product map of two `C^n` functions within a set at a point is `C^n`
within the product set at the product point. -/
theorem MDifferentiableWithinAt.prodMap' {p : M × N}
    (hf : MDiffAt[s] f p.1) (hg : MDiffAt[r] g p.2) :
    MDiffAt[s ×ˢ r] (Prod.map f g) p :=
  (hf.comp p mdifferentiableWithinAt_fst (prod_subset_preimage_fst _ _)).prodMk <|
    hg.comp p mdifferentiableWithinAt_snd (prod_subset_preimage_snd _ _)

theorem MDifferentiableWithinAt.prodMap (hf : MDiffAt[s] f x) (hg : MDiffAt[r] g y) :
    MDiffAt[s ×ˢ r] (Prod.map f g) (x, y) :=
  hf.prodMap' hg

theorem MDifferentiableAt.prodMap (hf : MDiffAt f x) (hg : MDiffAt g y) :
    MDiffAt (Prod.map f g) (x, y) := by
  rw [← mdifferentiableWithinAt_univ] at *
  convert! hf.prodMap hg
  exact univ_prod_univ.symm

/-- Variant of `MDifferentiableAt.prod_map` in which the point in the product is given as `p`
instead of a pair `(x, y)`. -/
theorem MDifferentiableAt.prodMap' {p : M × N}
    (hf : MDiffAt f p.1) (hg : MDiffAt g p.2) : MDiffAt (Prod.map f g) p :=
  hf.prodMap hg

theorem MDifferentiableOn.prodMap (hf : MDiff[s] f) (hg : MDiff[r] g) :
    MDiff[s ×ˢ r] (Prod.map f g) :=
  (hf.comp mdifferentiableOn_fst (prod_subset_preimage_fst _ _)).prodMk <|
    hg.comp mdifferentiableOn_snd (prod_subset_preimage_snd _ _)

theorem MDifferentiable.prodMap (hf : MDiff f) (hg : MDiff g) : MDiff (Prod.map f g) := fun p ↦
  (hf p.1).prodMap' (hg p.2)

lemma HasMFDerivWithinAt.prodMap {s : Set <| M × M'} {p : M × M'} {f : M → N} {g : M' → N'}
    {df : TangentSpace% p.1 →L[𝕜] TangentSpace% (f p.1)}
    (hf : HasMFDerivAt[Prod.fst '' s] f p.1 df)
    {dg : TangentSpace% p.2 →L[𝕜] TangentSpace% (g p.2)}
    (hg : HasMFDerivAt[Prod.snd '' s] g p.2 dg) :
    HasMFDerivAt[s] (Prod.map f g) p (df.prodMap dg) := by
  refine ⟨hf.1.prodMap hg.1 |>.mono (by grind), ?_⟩
  have better : ((extChartAt (I.prod I') p).symm ⁻¹' s ∩ range ↑(I.prod I')) ⊆
      ((extChartAt I p.1).symm ⁻¹' (Prod.fst '' s) ∩ range I) ×ˢ
        ((extChartAt I' p.2).symm ⁻¹' (Prod.snd '' s) ∩ range I') := by
    simp only [mfld_simps]
    rw [range_prodMap, I.toPartialEquiv.prod_symm, (chartAt H p.1).toPartialEquiv.prod_symm]
    intro p₀ ⟨hp₀, ⟨hp₁₁, hp₁₂⟩⟩
    exact ⟨⟨by simp_all; grind, by assumption⟩, ⟨by simp_all; grind, by assumption⟩⟩
  rw [writtenInExtChartAt_prod]
  apply HasFDerivWithinAt.mono ?_ better
  apply HasFDerivWithinAt.prodMap
  exacts [hf.2.mono (fst_image_prod_subset ..), hg.2.mono (snd_image_prod_subset ..)]

set_option backward.isDefEq.respectTransparency false in
lemma HasMFDerivAt.prodMap {p : M × M'} {f : M → N} {g : M' → N'}
    {df : TangentSpace% p.1 →L[𝕜] TangentSpace% (f p.1)} (hf : HasMFDerivAt% f p.1 df)
    {dg : TangentSpace% p.2 →L[𝕜] TangentSpace% (g p.2)} (hg : HasMFDerivAt% g p.2 dg) :
    HasMFDerivAt% (Prod.map f g) p
      ((mfderiv% f p.1).prodMap (mfderiv% g p.2)) := by
  simp_rw [← hasMFDerivWithinAt_univ, ← mfderivWithin_univ, ← univ_prod_univ]
  convert! hf.hasMFDerivWithinAt.prodMap hg.hasMFDerivWithinAt
  · rw [mfderivWithin_univ]; exact hf.mfderiv
  · rw [mfderivWithin_univ]; exact hg.mfderiv

-- Note: this lemma does not apply easily to an arbitrary subset `s ⊆ M × M'` as
-- unique differentiability on `(Prod.fst '' s)` and `(Prod.snd '' s)` does not imply
-- unique differentiability on `s`: a priori, `(Prod.fst '' s) × (Prod.fst '' s)`
-- could be a strict superset of `s`.
lemma mfderivWithin_prodMap {p : M × M'} {t : Set M'} {f : M → N} {g : M' → N'}
    (hf : MDiffAt[s] f p.1) (hg : MDiffAt[t] g p.2)
    (hs : UniqueMDiffAt[s] p.1) (ht : UniqueMDiffAt[t] p.2) :
    mfderiv[s ×ˢ t] (Prod.map f g) p = (mfderiv[s] f p.1).prodMap (mfderiv[t] g p.2) := by
  have hf' : HasMFDerivAt[Prod.fst '' s ×ˢ t] f p.1 (mfderiv[s] f p.1) :=
    hf.hasMFDerivWithinAt.mono (by grind)
  have hg' : HasMFDerivAt[Prod.snd '' s ×ˢ t] g p.2 (mfderiv[t] g p.2) :=
    hg.hasMFDerivWithinAt.mono (by grind)
  exact (hf'.prodMap hg').mfderivWithin (hs.prod ht)

lemma mfderiv_prodMap {p : M × M'} {f : M → N} {g : M' → N'}
    (hf : MDiffAt f p.1) (hg : MDiffAt g p.2) :
    mfderiv% (Prod.map f g) p = (mfderiv% f p.1).prodMap (mfderiv% g p.2) := by
  simp_rw [← mfderivWithin_univ, ← univ_prod_univ]
  exact mfderivWithin_prodMap hf.mdifferentiableWithinAt hg.mdifferentiableWithinAt
    (uniqueMDiffWithinAt_univ I) (uniqueMDiffWithinAt_univ I')

end prodMap

@[simp, mfld_simps]
theorem tangentMap_prodSnd {p : TangentBundle (I.prod I') (M × M')} :
    tangentMap% (@Prod.snd M M') p = ⟨p.proj.2, p.2.2⟩ := by
  simp [tangentMap]; rfl

theorem tangentMapWithin_prodSnd {s : Set (M × M')} {p : TangentBundle (I.prod I') (M × M')}
    (hs : UniqueMDiffAt[s] p.proj) :
    tangentMap[s] (@Prod.snd M M') p = ⟨p.proj.2, p.2.2⟩ := by
  simp only [tangentMapWithin]
  rw [mfderivWithin_snd hs]
  rcases p with ⟨⟩; rfl

-- Kept as an alias for discoverability.
alias MDifferentiableAt.mfderiv_prod := mfderiv_prodMk

theorem mfderiv_prod_left {x₀ : M} {y₀ : M'} :
    mfderiv% (fun (x : M) ↦ (x, y₀)) x₀ =
      ContinuousLinearMap.inl 𝕜 (TangentSpace% x₀) (TangentSpace% y₀) := by
  refine (mdifferentiableAt_id.mfderiv_prod mdifferentiableAt_const).trans ?_
  rw [mfderiv_id, mfderiv_const, ContinuousLinearMap.inl]

-- TODO: better error when the type of x is left open
theorem tangentMap_prod_left {p : TangentBundle I M} {y₀ : M'} :
    tangentMap% (fun (x : M) ↦ (x, y₀)) p = ⟨(p.1, y₀), (p.2, 0)⟩ := by
  simp only [tangentMap, mfderiv_prod_left]
  rfl

theorem mfderiv_prod_right {x₀ : M} {y₀ : M'} :
    mfderiv% (fun (y : M') ↦ (x₀, y)) y₀ =
      ContinuousLinearMap.inr 𝕜 (TangentSpace% x₀) (TangentSpace% y₀) := by
  refine (mdifferentiableAt_const.mfderiv_prod mdifferentiableAt_id).trans ?_
  rw [mfderiv_id, mfderiv_const, ContinuousLinearMap.inr]

theorem tangentMap_prod_right {p : TangentBundle I' M'} {x₀ : M} :
    tangentMap% (fun (y : M') ↦ (x₀, y)) p = ⟨(x₀, p.1), (0, p.2)⟩ := by
  simp only [tangentMap, mfderiv_prod_right]
  rfl

/-- The total derivative of a function in two variables is the sum of the partial derivatives.
  Note that to state this (without casts) we need to be able to see through the definition of
  `TangentSpace`. -/
theorem mfderiv_prod_eq_add {f : M × M' → M''} {p : M × M'}
    (hf : MDiffAt f p) :
    mfderiv% f p =
        mfderiv% (fun z : M × M' ↦ f (z.1, p.2)) p +
        mfderiv% (fun z : M × M' ↦ f (p.1, z.2)) p := by
  erw [mfderiv_comp_of_eq hf (mdifferentiableAt_fst.prodMk mdifferentiableAt_const) rfl,
    mfderiv_comp_of_eq hf (mdifferentiableAt_const.prodMk mdifferentiableAt_snd) rfl,
    ← ContinuousLinearMap.comp_add,
    mdifferentiableAt_fst.mfderiv_prod mdifferentiableAt_const,
    mdifferentiableAt_const.mfderiv_prod mdifferentiableAt_snd, mfderiv_fst,
    mfderiv_snd, mfderiv_const, mfderiv_const]
  symm
  convert! ContinuousLinearMap.comp_id <| mfderiv% f (p.1, p.2)
  exact ContinuousLinearMap.coprod_inl_inr

/-- The total derivative of a function in two variables is the sum of the partial derivatives.
  Note that to state this (without casts) we need to be able to see through the definition of
  `TangentSpace`. Version in terms of the one-variable derivatives. -/
theorem mfderiv_prod_eq_add_comp {f : M × M' → M''} {p : M × M'} (hf : MDiffAt f p) :
    mfderiv% f p =
        (mfderiv% (fun z : M ↦ f (z, p.2)) p.1) ∘L (id (ContinuousLinearMap.fst 𝕜 E E') :
          (TangentSpace% p) →L[𝕜] (TangentSpace% p.1)) +
        (mfderiv% (fun z : M' ↦ f (p.1, z)) p.2) ∘L (id (ContinuousLinearMap.snd 𝕜 E E') :
          (TangentSpace% p) →L[𝕜] (TangentSpace% p.2)) := by
  rw [mfderiv_prod_eq_add hf]
  congr
  · have : (fun z : M × M' ↦ f (z.1, p.2)) = (fun z : M ↦ f (z, p.2)) ∘ Prod.fst := rfl
    rw [this, mfderiv_comp (I' := I)]
    · simp only [mfderiv_fst]
      rfl
    · exact hf.comp _ (mdifferentiableAt_id.prodMk mdifferentiableAt_const)
    · exact mdifferentiableAt_fst
  · have : (fun z : M × M' ↦ f (p.1, z.2)) = (fun z : M' ↦ f (p.1, z)) ∘ Prod.snd := rfl
    rw [this, mfderiv_comp (I' := I')]
    · simp only [mfderiv_snd]
      rfl
    · exact hf.comp _ (mdifferentiableAt_const.prodMk mdifferentiableAt_id)
    · exact mdifferentiableAt_snd

/-- The total derivative of a function in two variables is the sum of the partial derivatives.
  Note that to state this (without casts) we need to be able to see through the definition of
  `TangentSpace`. Version in terms of the one-variable derivatives. -/
theorem mfderiv_prod_eq_add_apply {f : M × M' → M''} {p : M × M'} {v : TangentSpace% p}
    (hf : MDiffAt f p) :
    mfderiv% f p v =
      mfderiv% (fun z : M ↦ f (z, p.2)) p.1 v.1 + mfderiv% (fun z : M' ↦ f (p.1, z)) p.2 v.2 := by
  rw [mfderiv_prod_eq_add_comp hf]
  rfl

end Prod

section disjointUnion

variable {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M'] {p : M ⊕ M'}

/-- In extended charts at `p`, `Sum.swap` looks like the identity near `p`. -/
lemma writtenInExtChartAt_sumSwap_eventuallyEq_id :
    writtenInExtChartAt I I p Sum.swap =ᶠ[𝓝[range I] (I <| chartAt H p p)] id := by
  cases p with
    | inl x =>
      let t := I.symm ⁻¹' (chartAt H x).target ∩ range I
      have : EqOn (writtenInExtChartAt I I (Sum.inl x) (@Sum.swap M M')) id t := by
        intro y hy
        simp only [writtenInExtChartAt, extChartAt, Sum.swap_inl,
          ChartedSpace.sum_chartAt_inl, ChartedSpace.sum_chartAt_inr]
        dsimp
        rw [Sum.inr_injective.extend_apply, (chartAt H x).right_inv (by grind)]
        exact I.right_inv (by grind)
      apply Filter.eventually_of_mem ?_ this
      rw [Filter.inter_mem_iff]
      refine ⟨I.continuousWithinAt_symm.preimage_mem_nhdsWithin ?_, self_mem_nhdsWithin⟩
      exact (chartAt H x).open_target.mem_nhds (by simp)
    | inr x =>
      let t := I.symm ⁻¹' (chartAt H x).target ∩ range I
      have : EqOn (writtenInExtChartAt I I (Sum.inr x) (@Sum.swap M M')) id t := by
        intro y hy
        simp only [writtenInExtChartAt, extChartAt, Sum.swap_inr,
          ChartedSpace.sum_chartAt_inl, ChartedSpace.sum_chartAt_inr]
        dsimp
        rw [Sum.inl_injective.extend_apply, (chartAt H x).right_inv (by grind)]
        exact I.right_inv (by grind)
      apply Filter.eventually_of_mem ?_ this
      rw [Filter.inter_mem_iff]
      refine ⟨I.continuousWithinAt_symm.preimage_mem_nhdsWithin ?_, self_mem_nhdsWithin⟩
      exact (chartAt H x).open_target.mem_nhds (by simp)

theorem hasMFDerivAt_sumSwap :
    HasMFDerivAt% (@Sum.swap M M') p (ContinuousLinearMap.id 𝕜 (TangentSpace% p)) := by
  refine ⟨by fun_prop, ?_⟩
  apply (hasFDerivWithinAt_id _ (range I)).congr_of_eventuallyEq
  · exact writtenInExtChartAt_sumSwap_eventuallyEq_id
  · simp only [mfld_simps]
    cases p <;> simp

@[simp]
theorem mfderivWithin_sumSwap {s : Set (M ⊕ M')} (hs : UniqueMDiffAt[s] p) :
    mfderiv[s] (@Sum.swap M M') p = ContinuousLinearMap.id 𝕜 (TangentSpace% p) :=
  hasMFDerivAt_sumSwap.hasMFDerivWithinAt.mfderivWithin hs

@[simp]
theorem mfderiv_sumSwap :
    mfderiv% (@Sum.swap M M') p = ContinuousLinearMap.id 𝕜 (TangentSpace% p) := by
  simpa [mfderivWithin_univ] using (mfderivWithin_sumSwap (uniqueMDiffWithinAt_univ I))

variable {f : M → N} {q : M} {q' : M'}

lemma writtenInExtChartAt_sumInl_eventuallyEq_id :
    (writtenInExtChartAt I I q (@Sum.inl M M')) =ᶠ[𝓝[Set.range I] (extChartAt I q q)] id := by
  have hmem : I.symm ⁻¹'
      (chartAt H q).target ∩ Set.range I ∈ 𝓝[Set.range I] (extChartAt I q q) := by
    rw [← I.image_eq (chartAt H q).target]
    exact (chartAt H q).extend_image_target_mem_nhds (mem_chart_source H q)
  filter_upwards [hmem] with y hy
  rcases hy with ⟨hyT, ⟨z, rfl⟩⟩
  simp [writtenInExtChartAt, extChartAt, ChartedSpace.sum_chartAt_inl,
    Sum.inl_injective.extend_apply <| chartAt H q,
    (chartAt H q).right_inv (by simpa [Set.mem_preimage, I.left_inv] using hyT)]

lemma writtenInExtChartAt_sumInr_eventuallyEq_id :
    (writtenInExtChartAt I I q' (@Sum.inr M M')) =ᶠ[𝓝[Set.range I] (extChartAt I q' q')] id := by
  have hmem : I.symm ⁻¹'
      (chartAt H q').target ∩ Set.range I ∈ 𝓝[Set.range I] (extChartAt I q' q') := by
    rw [← I.image_eq (chartAt H q').target]
    exact (chartAt H q').extend_image_target_mem_nhds (mem_chart_source H q')
  filter_upwards [hmem] with y hy
  rcases hy with ⟨hyT, ⟨z, rfl⟩⟩
  simp [writtenInExtChartAt, extChartAt, ChartedSpace.sum_chartAt_inr,
    Sum.inr_injective.extend_apply <| chartAt H q',
    (chartAt H q').right_inv (by simpa [Set.mem_preimage, I.left_inv] using hyT)]

theorem hasMFDerivWithinAt_inl :
    HasMFDerivAt[s] (@Sum.inl M M') q (ContinuousLinearMap.id 𝕜 (TangentSpace% q)) := by
  refine ⟨by fun_prop, ?_⟩
  have : (writtenInExtChartAt I I q (@Sum.inl M M'))
      =ᶠ[𝓝[(extChartAt I q).symm ⁻¹' s ∩ Set.range I] (extChartAt I q q)] id :=
    writtenInExtChartAt_sumInl_eventuallyEq_id.filter_mono (nhdsWithin_mono _ (fun _y hy ↦ hy.2))
  exact (hasFDerivWithinAt_id (extChartAt I q q) _).congr_of_eventuallyEq this
    (by simp [writtenInExtChartAt, extChartAt])

set_option backward.isDefEq.respectTransparency false in
theorem hasMFDerivAt_inl :
    HasMFDerivAt% (@Sum.inl M M') q (ContinuousLinearMap.id 𝕜 (TangentSpace% p)) := by
  simpa [HasMFDerivAt, hasMFDerivWithinAt_univ] using! hasMFDerivWithinAt_inl (s := Set.univ)

theorem hasMFDerivWithinAt_inr {t : Set M'} :
    HasMFDerivAt[t] (@Sum.inr M M') q' (ContinuousLinearMap.id 𝕜 (TangentSpace% q')) := by
  refine ⟨by fun_prop, ?_⟩
  have : (writtenInExtChartAt I I q' (@Sum.inr M M'))
      =ᶠ[𝓝[(extChartAt I q').symm ⁻¹' t ∩ Set.range I] (extChartAt I q' q')] id :=
    writtenInExtChartAt_sumInr_eventuallyEq_id.filter_mono (nhdsWithin_mono _ (fun _y hy ↦ hy.2))
  exact (hasFDerivWithinAt_id (extChartAt I q' q') _).congr_of_eventuallyEq this
    (by simp [writtenInExtChartAt, extChartAt])

set_option backward.isDefEq.respectTransparency false in
theorem hasMFDerivAt_inr :
    HasMFDerivAt% (@Sum.inr M M') q' (ContinuousLinearMap.id 𝕜 (TangentSpace% p)) := by
  simpa [HasMFDerivAt, hasMFDerivWithinAt_univ] using! hasMFDerivWithinAt_inr (t := Set.univ)

theorem mfderivWithin_sumInl (hU : UniqueMDiffAt[s] q) :
    mfderiv[s] (@Sum.inl M M') q = ContinuousLinearMap.id 𝕜 (TangentSpace% p) :=
  hasMFDerivWithinAt_inl.mfderivWithin hU

theorem mfderiv_sumInl :
    mfderiv% (@Sum.inl M M') q = ContinuousLinearMap.id 𝕜 (TangentSpace% p) := by
  simpa [mfderivWithin_univ] using (mfderivWithin_sumInl (uniqueMDiffWithinAt_univ I))

theorem mfderivWithin_sumInr {t : Set M'} (hU : UniqueMDiffAt[t] q') :
    mfderiv[t] (@Sum.inr M M') q' = ContinuousLinearMap.id 𝕜 (TangentSpace% q') :=
  hasMFDerivWithinAt_inr.mfderivWithin hU

theorem mfderiv_sumInr :
    mfderiv% (@Sum.inr M M') q' = ContinuousLinearMap.id 𝕜 (TangentSpace% q') := by
  simpa [mfderivWithin_univ] using (mfderivWithin_sumInr (uniqueMDiffWithinAt_univ I))

end disjointUnion

section Arithmetic

/-! #### Arithmetic

Note that in the `HasMFDerivAt` lemmas there is an abuse of the defeq between `E'` and
`TangentSpace 𝓘(𝕜, E') (f z)` (similarly for `g',F',p',q'`). In general this defeq is not
canonical, but in this case (the tangent space of a vector space) it is canonical.
-/

section Group

variable {z : M} {f g : M → E'} {f' g' : TangentSpace% z →L[𝕜] E'}

theorem HasMFDerivWithinAt.add {s : Set M}
    (hf : HasMFDerivAt[s] f z f') (hg : HasMFDerivAt[s] g z g') :
    HasMFDerivAt[s] (f + g) z (f' + g') :=
  ⟨hf.1.add hg.1, hf.2.add hg.2⟩

theorem HasMFDerivAt.add (hf : HasMFDerivAt% f z f') (hg : HasMFDerivAt% g z g') :
    HasMFDerivAt% (f + g) z (f' + g') :=
  ⟨hf.1.add hg.1, hf.2.add hg.2⟩

theorem MDifferentiableWithinAt.add {s : Set M} (hf : MDiffAt[s] f z) (hg : MDiffAt[s] g z) :
    MDiffAt[s] (f + g) z :=
  (hf.hasMFDerivWithinAt.add hg.hasMFDerivWithinAt).mdifferentiableWithinAt

theorem MDifferentiableAt.add (hf : MDiffAt f z) (hg : MDiffAt g z) : MDiffAt (f + g) z :=
  (hf.hasMFDerivAt.add hg.hasMFDerivAt).mdifferentiableAt

theorem MDifferentiableOn.add {s : Set M} (hf : MDiff[s] f) (hg : MDiff[s] g) : MDiff[s] (f + g) :=
  fun x hx ↦ (hf x hx).add (hg x hx)

theorem MDifferentiable.add (hf : MDiff f) (hg : MDiff g) : MDiff (f + g) :=
  fun x ↦ (hf x).add (hg x)

-- TODO: this lemma (and others below) uses the identification of tangent spaces silently
-- Deprecate all these lemmas in favour of a version using `mvfderiv(Within)`
-- Porting note: forcing types using `by exact`
theorem mfderiv_add (hf : MDiffAt f z) (hg : MDiffAt g z) :
    (mfderiv% (f + g) z : TangentSpace% z →L[𝕜] E') =
      (by exact mfderiv% f z) + (by exact mfderiv% g z) :=
  (hf.hasMFDerivAt.add hg.hasMFDerivAt).mfderiv

theorem mfderivWithin_add (hf : MDiffAt[s] f z) (hg : MDiffAt[s] g z)
    (hs : UniqueMDiffAt[s] z) :
    (mfderiv[s] (f + g) z : TangentSpace% z →L[𝕜] E') =
      (by exact mfderiv[s] f z) + (by exact mfderiv[s] g z) :=
  (hf.hasMFDerivWithinAt.add hg.hasMFDerivWithinAt).mfderivWithin hs

section sum
variable {ι : Type*} {t : Finset ι} {f : ι → M → E'} {f' : ι → TangentSpace% z →L[𝕜] E'}

lemma HasMFDerivWithinAt.sum (hf : ∀ i ∈ t, HasMFDerivAt[s] (f i) z (f' i)) :
    HasMFDerivAt[s] (∑ i ∈ t, f i) z (∑ i ∈ t, f' i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using! hasMFDerivWithinAt_const ..
  | insert i s hi IH => grind [HasMFDerivWithinAt.add]

set_option backward.isDefEq.respectTransparency false in
lemma HasMFDerivAt.sum (hf : ∀ i ∈ t, HasMFDerivAt% (f i) z (f' i)) :
    HasMFDerivAt% (∑ i ∈ t, f i) z (∑ i ∈ t, f' i) := by
  simp_all only [← hasMFDerivWithinAt_univ]
  exact HasMFDerivWithinAt.sum hf

lemma MDifferentiableWithinAt.sum
    (hf : ∀ i ∈ t, MDiffAt[s] (f i) z) : MDiffAt[s] (∑ i ∈ t, f i) z :=
  (HasMFDerivWithinAt.sum fun i hi ↦ (hf i hi).hasMFDerivWithinAt).mdifferentiableWithinAt

lemma MDifferentiableAt.sum (hf : ∀ i ∈ t, MDiffAt (f i) z) : MDiffAt (∑ i ∈ t, f i) z := by
  simp_all only [← mdifferentiableWithinAt_univ]
  exact .sum hf

lemma MDifferentiableOn.sum (hf : ∀ i ∈ t, MDiff[s] (f i)) : MDiff[s] (∑ i ∈ t, f i) :=
  fun z hz ↦ .sum fun i hi ↦ hf i hi z hz

lemma MDifferentiable.sum (hf : ∀ i ∈ t, MDiff (f i)) : MDiff (∑ i ∈ t, f i) :=
  fun z ↦ .sum fun i hi ↦ hf i hi z

end sum

theorem HasMFDerivWithinAt.const_smul (hf : HasMFDerivAt[s] f z f') (a : 𝕜) :
    HasMFDerivAt[s] (a • f) z (a • f') :=
  ⟨hf.1.const_smul a, hf.2.const_smul a⟩

theorem HasMFDerivAt.const_smul (hf : HasMFDerivAt% f z f') (s : 𝕜) :
    HasMFDerivAt% (s • f) z (s • f') :=
  ⟨hf.1.const_smul s, hf.2.const_smul s⟩

theorem MDifferentiableWithinAt.const_smul (hf : MDiffAt[s] f z) (a : 𝕜) : MDiffAt[s] (a • f) z :=
  (hf.hasMFDerivWithinAt.const_smul a).mdifferentiableWithinAt

theorem MDifferentiableAt.const_smul (hf : MDiffAt f z) (s : 𝕜) : MDiffAt (s • f) z :=
  (hf.hasMFDerivAt.const_smul s).mdifferentiableAt

theorem MDifferentiableOn.const_smul (a : 𝕜) (hf : MDiff[s] f) : MDiff[s] (a • f) :=
  fun x hx ↦ (hf x hx).const_smul a

theorem MDifferentiable.const_smul (s : 𝕜) (hf : MDiff f) : MDiff (s • f) :=
  fun x ↦ (hf x).const_smul s

theorem const_smul_mfderiv (hf : MDiffAt f z) (s : 𝕜) : mfderiv% (s • f) z = s • mfderiv% f z :=
  (hf.hasMFDerivAt.const_smul s).mfderiv

theorem HasMFDerivWithinAt.neg {s : Set M} (hf : HasMFDerivAt[s] f z f') :
    HasMFDerivAt[s] (-f) z (-f') :=
  ⟨hf.1.neg, hf.2.neg⟩

theorem HasMFDerivAt.neg (hf : HasMFDerivAt% f z f') : HasMFDerivAt% (-f) z (-f') :=
  ⟨hf.1.neg, hf.2.neg⟩

set_option backward.isDefEq.respectTransparency false in
theorem hasMFDerivAt_neg : HasMFDerivAt% (-f) z (-f') ↔ HasMFDerivAt% f z f' :=
  ⟨fun hf ↦ by convert! hf.neg <;> rw [neg_neg], fun hf ↦ hf.neg⟩

theorem MDifferentiableWithinAt.neg {s : Set M} (hf : MDiffAt[s] f z) : MDiffAt[s] (-f) z :=
  (hf.hasMFDerivWithinAt.neg).mdifferentiableWithinAt

theorem MDifferentiableAt.neg (hf : MDiffAt f z) : MDiffAt (-f) z :=
  hf.hasMFDerivAt.neg.mdifferentiableAt

theorem MDifferentiableOn.neg {s : Set M} (hf : MDiff[s] f) : MDiff[s] (-f) :=
  fun x hx ↦ (hf x hx).neg

theorem mdifferentiableWithinAt_neg : MDiffAt[s] (-f) z ↔ MDiffAt[s] f z :=
  ⟨fun hf ↦ by convert hf.neg; rw [neg_neg], fun hf ↦ hf.neg⟩

theorem mdifferentiableAt_neg : MDiffAt (-f) z ↔ MDiffAt f z :=
  ⟨fun hf ↦ by convert! hf.neg; rw [neg_neg], fun hf ↦ hf.neg⟩

theorem MDifferentiable.neg (hf : MDiff f) : MDiff (-f) := fun x ↦ (hf x).neg

set_option backward.isDefEq.respectTransparency false in
theorem mfderivWithin_neg (hs : UniqueMDiffAt[s] x) :
    mfderiv[s] (-f) x = -mfderiv[s] f x := by
  simp_rw [mfderivWithin]
  by_cases hf : MDiffAt[s] f x
  · exact hf.hasMFDerivWithinAt.neg.mfderivWithin hs
  · rw [ite_eq_right hf]; rw [← mdifferentiableWithinAt_neg] at hf; rw [ite_eq_right hf, neg_zero]

theorem mfderiv_neg : mfderiv% (-f) x = -mfderiv% f x := by
  rw [← mfderivWithin_univ, mfderivWithin_neg (uniqueMDiffWithinAt_univ I), mfderivWithin_univ]

theorem HasMFDerivWithinAt.sub (hf : HasMFDerivAt[s] f z f') (hg : HasMFDerivAt[s] g z g') :
    HasMFDerivAt[s] (f - g) z (f' - g') :=
  ⟨hf.1.sub hg.1, hf.2.sub hg.2⟩

theorem HasMFDerivAt.sub (hf : HasMFDerivAt% f z f') (hg : HasMFDerivAt% g z g') :
    HasMFDerivAt% (f - g) z (f' - g') :=
  ⟨hf.1.sub hg.1, hf.2.sub hg.2⟩

theorem MDifferentiableWithinAt.sub (hf : MDiffAt[s] f z) (hg : MDiffAt[s] g z) :
    MDiffAt[s] (f - g) z :=
  (hf.hasMFDerivWithinAt.sub hg.hasMFDerivWithinAt).mdifferentiableWithinAt

theorem MDifferentiableAt.sub (hf : MDiffAt f z) (hg : MDiffAt g z) : MDiffAt (f - g) z :=
  (hf.hasMFDerivAt.sub hg.hasMFDerivAt).mdifferentiableAt

theorem MDifferentiableOn.sub (hf : MDiff[s] f) (hg : MDiff[s] g) :
    MDiff[s] (f - g) :=
  fun x hx ↦ (hf x hx).sub (hg x hx)

theorem MDifferentiable.sub (hf : MDiff f) (hg : MDiff g) : MDiff (f - g) :=
  fun x ↦ (hf x).sub (hg x)

theorem mfderivWithin_sub (hf : MDiffAt[s] f z) (hg : MDiffAt[s] g z)
    (hs : UniqueMDiffAt[s] z) :
    (mfderiv[s] (f - g) z : TangentSpace% z →L[𝕜] E') =
      (by exact mfderiv[s] f z) - (by exact mfderiv[s] g z) :=
  (hf.hasMFDerivWithinAt.sub hg.hasMFDerivWithinAt).mfderivWithin hs

theorem mfderiv_sub (hf : MDiffAt f z) (hg : MDiffAt g z) :
    (mfderiv% (f - g) z : TangentSpace% z →L[𝕜] E') =
      (by exact mfderiv% f z) - (by exact mfderiv% g z) :=
  (hf.hasMFDerivAt.sub hg.hasMFDerivAt).mfderiv

end Group

section AlgebraOverRing
open scoped RightActions

variable {z : M} {F' : Type*} [NormedRing F'] [NormedAlgebra 𝕜 F'] {p q : M → F'}
  {p' q' : TangentSpace% z →L[𝕜] F'}

theorem HasMFDerivWithinAt.mul' (hp : HasMFDerivWithinAt I 𝓘(𝕜, F') p s z p')
    (hq : HasMFDerivWithinAt I 𝓘(𝕜, F') q s z q') :
    HasMFDerivWithinAt I 𝓘(𝕜, F') (p * q) s z (p z • q' + p' <• q z : E →L[𝕜] F') :=
  ⟨hp.1.mul hq.1, by simpa only [mfld_simps] using! hp.2.mul' hq.2⟩

theorem HasMFDerivAt.mul' (hp : HasMFDerivAt I 𝓘(𝕜, F') p z p')
    (hq : HasMFDerivAt I 𝓘(𝕜, F') q z q') :
    HasMFDerivAt I 𝓘(𝕜, F') (p * q) z (p z • q' + p' <• q z : E →L[𝕜] F') :=
  hasMFDerivWithinAt_univ.mp <| hp.hasMFDerivWithinAt.mul' hq.hasMFDerivWithinAt

theorem MDifferentiableWithinAt.mul (hp : MDifferentiableWithinAt I 𝓘(𝕜, F') p s z)
    (hq : MDifferentiableWithinAt I 𝓘(𝕜, F') q s z) :
    MDifferentiableWithinAt I 𝓘(𝕜, F') (p * q) s z :=
  (hp.hasMFDerivWithinAt.mul' hq.hasMFDerivWithinAt).mdifferentiableWithinAt

theorem MDifferentiableAt.mul (hp : MDifferentiableAt I 𝓘(𝕜, F') p z)
    (hq : MDifferentiableAt I 𝓘(𝕜, F') q z) : MDifferentiableAt I 𝓘(𝕜, F') (p * q) z :=
  (hp.hasMFDerivAt.mul' hq.hasMFDerivAt).mdifferentiableAt

theorem MDifferentiableOn.mul (hp : MDifferentiableOn I 𝓘(𝕜, F') p s)
    (hq : MDifferentiableOn I 𝓘(𝕜, F') q s) : MDifferentiableOn I 𝓘(𝕜, F') (p * q) s :=
  fun x hx ↦ (hp x hx).mul <| hq x hx

theorem MDifferentiable.mul (hp : MDifferentiable I 𝓘(𝕜, F') p)
    (hq : MDifferentiable I 𝓘(𝕜, F') q) : MDifferentiable I 𝓘(𝕜, F') (p * q) :=
  fun x ↦ (hp x).mul (hq x)

theorem MDifferentiableWithinAt.pow (hp : MDifferentiableWithinAt I 𝓘(𝕜, F') p s z)
    (n : ℕ) : MDifferentiableWithinAt I 𝓘(𝕜, F') (p ^ n) s z := by
  induction n with
  | zero => simpa [pow_zero] using! mdifferentiableWithinAt_const
  | succ n hn => simpa [pow_succ] using! hn.mul hp

theorem MDifferentiableAt.pow (hp : MDifferentiableAt I 𝓘(𝕜, F') p z) (n : ℕ) :
    MDifferentiableAt I 𝓘(𝕜, F') (p ^ n) z :=
  mdifferentiableWithinAt_univ.mp (hp.mdifferentiableWithinAt.pow n)

theorem MDifferentiableOn.pow (hp : MDifferentiableOn I 𝓘(𝕜, F') p s) (n : ℕ) :
    MDifferentiableOn I 𝓘(𝕜, F') (p ^ n) s := fun x hx ↦ (hp x hx).pow n

theorem MDifferentiable.pow (hp : MDifferentiable I 𝓘(𝕜, F') p) (n : ℕ) :
    MDifferentiable I 𝓘(𝕜, F') (p ^ n) := fun x ↦ (hp x).pow n

end AlgebraOverRing

section AlgebraOverCommRing

variable {z : M} {F' : Type*} [NormedCommRing F'] [NormedAlgebra 𝕜 F'] {p q : M → F'}
  {p' q' : TangentSpace% z →L[𝕜] F'}

set_option backward.isDefEq.respectTransparency false in
theorem HasMFDerivWithinAt.mul (hp : HasMFDerivWithinAt I 𝓘(𝕜, F') p s z p')
    (hq : HasMFDerivWithinAt I 𝓘(𝕜, F') q s z q') :
    HasMFDerivWithinAt I 𝓘(𝕜, F') (p * q) s z (p z • q' + q z • p' : E →L[𝕜] F') := by
  convert! hp.mul' hq; ext _; apply mul_comm

theorem HasMFDerivAt.mul (hp : HasMFDerivAt I 𝓘(𝕜, F') p z p')
    (hq : HasMFDerivAt I 𝓘(𝕜, F') q z q') :
    HasMFDerivAt I 𝓘(𝕜, F') (p * q) z (p z • q' + q z • p' : E →L[𝕜] F') :=
  hasMFDerivWithinAt_univ.mp <| hp.hasMFDerivWithinAt.mul hq.hasMFDerivWithinAt

section prod
variable {ι : Type*} {t : Finset ι} {f : ι → M → F'} {f' : ι → TangentSpace% z →L[𝕜] F'}

set_option backward.isDefEq.respectTransparency false in
lemma HasMFDerivWithinAt.prod [DecidableEq ι]
    (hf : ∀ i ∈ t, HasMFDerivWithinAt I 𝓘(𝕜, F') (f i) s z (f' i)) :
    HasMFDerivWithinAt I 𝓘(𝕜, F') (∏ i ∈ t, f i) s z
      (∑ i ∈ t, (∏ j ∈ t.erase i, f j z) • (f' i)) := by
  induction t using Finset.induction_on with
  | empty => simpa using! hasMFDerivWithinAt_const ..
  | insert i t hi IH =>
    rw [t.sum_insert hi, t.erase_insert hi, t.prod_insert hi, add_comm]
    rw [t.forall_mem_insert] at hf
    convert! hf.1.mul (IH hf.2) using 2
    · simp only [t.smul_sum, ← mul_smul]
      refine t.sum_congr rfl (fun j hj ↦ ?_)
      rw [t.erase_insert_of_ne (by grind), Finset.prod_insert (by grind)]
    · simp

set_option backward.isDefEq.respectTransparency false in
lemma HasMFDerivAt.prod [DecidableEq ι]
    (hf : ∀ i ∈ t, HasMFDerivAt I 𝓘(𝕜, F') (f i) z (f' i)) :
    HasMFDerivAt I 𝓘(𝕜, F') (∏ i ∈ t, f i) z (∑ i ∈ t, (∏ j ∈ t.erase i, f j z) • (f' i)) := by
  simp_all only [← hasMFDerivWithinAt_univ]
  exact HasMFDerivWithinAt.prod hf

lemma MDifferentiableWithinAt.prod
    (hf : ∀ i ∈ t, MDifferentiableWithinAt I 𝓘(𝕜, F') (f i) s z) :
    MDifferentiableWithinAt I 𝓘(𝕜, F') (∏ i ∈ t, f i) s z := by
  -- `by classical exact` to avoid needing a `DecidableEq` argument
  classical exact (HasMFDerivWithinAt.prod
    fun i hi ↦ (hf i hi).hasMFDerivWithinAt).mdifferentiableWithinAt

lemma MDifferentiableAt.prod (hf : ∀ i ∈ t, MDifferentiableAt I 𝓘(𝕜, F') (f i) z) :
    MDifferentiableAt I 𝓘(𝕜, F') (∏ i ∈ t, f i) z := by
  simp_all only [← mdifferentiableWithinAt_univ]
  exact MDifferentiableWithinAt.prod hf

lemma MDifferentiableOn.prod (hf : ∀ i ∈ t, MDifferentiableOn I 𝓘(𝕜, F') (f i) s) :
    MDifferentiableOn I 𝓘(𝕜, F') (∏ i ∈ t, f i) s :=
  fun z hz ↦ .prod fun i hi ↦ hf i hi z hz

lemma MDifferentiable.prod (hf : ∀ i ∈ t, MDifferentiable I 𝓘(𝕜, F') (f i)) :
    MDifferentiable I 𝓘(𝕜, F') (∏ i ∈ t, f i) :=
  fun z ↦ .prod fun i hi ↦ hf i hi z

end prod

end AlgebraOverCommRing

section DivisionRing

open scoped RightActions
open Filter

variable {z : M} {F' : Type*} [NormedDivisionRing F'] [NormedAlgebra 𝕜 F']
  {p q r : M → F'} {p' q' : TangentSpace I z →L[𝕜] F'}

private theorem hasMFDerivWithinAt_iff_sourceChart {f : M → F'}
    {f' : TangentSpace I z →L[𝕜] F'} :
    HasMFDerivWithinAt I 𝓘(𝕜, F') f s z f' ↔
      HasFDerivWithinAt (f ∘ (extChartAt I z).symm) (f' ∘L (tangentSpaceCastModel I z).symm)
        ((extChartAt I z).symm ⁻¹' s ∩ range I) (extChartAt I z z) := by
  unfold HasMFDerivWithinAt writtenInExtChartAt
  rw [extChartAt_model_space_eq_id]
  apply and_iff_right_of_imp
  intro h
  change Tendsto f (𝓝[s] z) (𝓝 (f z))
  rw [← map_extChartAt_symm_nhdsWithin (I := I) z, tendsto_map'_iff]
  have hcont : ContinuousWithinAt (f ∘ (extChartAt I z).symm)
      ((extChartAt I z).symm ⁻¹' s ∩ range I) (extChartAt I z z) :=
    h.continuousWithinAt continuousWithinAt_id
  rw [ContinuousWithinAt] at hcont
  simpa only [Function.comp_def, extChartAt_to_inv] using hcont

private theorem hasFDerivWithinAt_of_domain_agreement {A : Set E} {f : A → F'} {g : E → F'}
    {f' : E →L[𝕜] F'} {u : A} {S : Set E}
    (hf : HasFDerivWithinAt f f' (Subtype.val ⁻¹' S) u Subtype.val)
    (hA : A ∈ 𝓝[S] (u : E))
    (hEq : f =ᶠ[𝓝[Subtype.val ⁻¹' S] u] (g ∘ Subtype.val))
    (hu : f u = g u) : HasFDerivWithinAt g f' S (u : E) := by
  let i : A → E := Subtype.val
  have hpull : 𝓝[i ⁻¹' S] u = comap i (𝓝[S] (u : E)) := by
    rw [nhdsWithin, nhdsWithin, nhds_subtype, comap_inf, comap_principal]
  have hpush : map i (𝓝[i ⁻¹' S] u) = 𝓝[S] (u : E) := by
    rw [hpull, subtype_coe_map_comap, inf_eq_left.2 (le_principal_iff.2 hA)]
  rw [hasFDerivWithinAt_iff_isLittleOTVS, ← hpush, Asymptotics.isLittleOTVS_map]
  refine hf.isLittleOTVS.congr' ?_ .rfl
  filter_upwards [hEq] with w hw
  change f w = g (i w) at hw
  change f w - f u - _ = g (i w) - g (i u) - _
  rw [hw, hu]
  rfl

/-- A checked operation in the source chart supplies a manifold derivative whenever a function
agrees with that operation on the relevant neighborhood. -/
private theorem hasMFDerivWithinAt_of_local_chart {valid : M → Prop}
    {f : {y : M // valid y} → F'} {f' : TangentSpace I z →L[𝕜] F'} {hz : valid z}
    (hf : let chart := extChartAt I z
      HasFDerivWithinAt (fun u : {u : E // valid (chart.symm u)} ↦ f ⟨chart.symm u, u.property⟩)
        (f' ∘L (tangentSpaceCastModel I z).symm)
        (Subtype.val ⁻¹' (chart.symm ⁻¹' s ∩ range I))
        ⟨chart z, by
          change valid ((extChartAt I z).symm (extChartAt I z z))
          rwa [extChartAt_to_inv]⟩ Subtype.val)
    (hr : ∀ᶠ y in 𝓝[insert z s] z, ∃ hy : valid y, r y = f ⟨y, hy⟩) :
    HasMFDerivWithinAt I 𝓘(𝕜, F') r s z f' := by
  let chart := extChartAt I z
  let S : Set E := chart.symm ⁻¹' s ∩ range I
  let U : Set E := {u | valid (chart.symm u)}
  let u : U := ⟨chart z, by
    change valid ((extChartAt I z).symm (extChartAt I z z))
    rwa [extChartAt_to_inv]⟩
  let i : U → E := Subtype.val
  have h : ∀ᶠ u in 𝓝[S] chart z, ∃ hu : valid (chart.symm u), r (chart.symm u) = f ⟨_, hu⟩ :=
    extChartAt_preimage_mem_nhdsWithin (I := I)
      (hr.filter_mono (nhdsWithin_mono _ (subset_insert _ _)))
  have hU : U ∈ 𝓝[S] chart z := h.mono (fun _ hu ↦ hu.choose)
  have hi : Tendsto i (𝓝[i ⁻¹' S] u) (𝓝[S] chart z) :=
    continuous_subtype_val.continuousWithinAt.tendsto_nhdsWithin (fun _ hv ↦ hv)
  apply hasMFDerivWithinAt_iff_sourceChart.2
  refine hasFDerivWithinAt_of_domain_agreement hf hU
    ((hi.eventually h).mono fun _ hu ↦ hu.choose_spec.symm) ?_
  obtain ⟨h, he⟩ := mem_of_mem_nhdsWithin (mem_insert z s) hr
  simpa only [chart, Function.comp_apply, extChartAt_to_inv] using he.symm

/-- A function locally equal to the checked inverse has the inverse derivative within the set. -/
lemma HasMFDerivWithinAt.inv' (hp : HasMFDerivWithinAt I 𝓘(𝕜, F') p s z p')
    {hu : IsUnit (p z)} (hr : ∀ᶠ y in 𝓝[insert z s] z,
      ∃ hy : IsUnit (p y), r y = Checked.inv (p y) hy) :
    HasMFDerivWithinAt I 𝓘(𝕜, F') r s z
      (-((Checked.inv (p z) hu) •> p' <• (Checked.inv (p z) hu)) : E →L[𝕜] F') := by
  apply hasMFDerivWithinAt_of_local_chart (hz := hu)
    (f := fun y : {y : M // IsUnit (p y)} ↦ Checked.inv (p y) y.property) _ hr
  let chart := extChartAt I z
  let P : E → F' := p ∘ chart.symm
  have hz : IsUnit (P (chart z)) := by
    simpa only [P, chart, Function.comp_def, extChartAt_to_inv] using hu
  have hval : P (chart z) = p z := by simp only [P, chart, Function.comp_def, extChartAt_to_inv]
  have hunit : hz.unit = hu.unit := Units.ext (hz.unit_spec.trans (hval.trans hu.unit_spec.symm))
  have hinv : (↑hz.unit⁻¹ : F') = Checked.inv (p z) hu :=
    congrArg (fun u : F'ˣ ↦ (↑u⁻¹ : F')) hunit
  have h := (hasMFDerivWithinAt_iff_sourceChart.1 hp).inv hz
  have hcoeff :
      (-ContinuousLinearMap.mulLeftRight 𝕜 F' (Checked.inv (p z) hu) (Checked.inv (p z) hu)).comp
        (p' ∘L (tangentSpaceCastModel I z).symm.toContinuousLinearMap) =
      (-((Checked.inv (p z) hu) •> p' <• (Checked.inv (p z) hu))) ∘L
        (tangentSpaceCastModel I z).symm.toContinuousLinearMap := by
    ext w
    rfl
  rw [hinv, hcoeff] at h
  exact h

lemma HasMFDerivAt.inv' (hp : HasMFDerivAt I 𝓘(𝕜, F') p z p')
    {hu : IsUnit (p z)} (hr : ∀ᶠ y in 𝓝 z, ∃ hy : IsUnit (p y), r y = Checked.inv (p y) hy) :
    HasMFDerivAt I 𝓘(𝕜, F') r z
      (-((Checked.inv (p z) hu) •> p' <• (Checked.inv (p z) hu)) : E →L[𝕜] F') :=
  hasMFDerivWithinAt_univ.mp <| hp.hasMFDerivWithinAt.inv' (hu := hu)
    (by simpa only [insert_eq_of_mem (mem_univ z), nhdsWithin_univ] using hr)

lemma MDifferentiableWithinAt.inv (hp : MDifferentiableWithinAt I 𝓘(𝕜, F') p s z)
    (hr : ∀ᶠ y in 𝓝[insert z s] z, ∃ hy : IsUnit (p y), r y = Checked.inv (p y) hy) :
    MDifferentiableWithinAt I 𝓘(𝕜, F') r s z := by
  have hu : IsUnit (p z) := (mem_of_mem_nhdsWithin (mem_insert z s) hr).choose
  exact (hp.hasMFDerivWithinAt.inv' (hu := hu) hr).mdifferentiableWithinAt

lemma MDifferentiableAt.inv (hp : MDifferentiableAt I 𝓘(𝕜, F') p z)
    (hr : ∀ᶠ y in 𝓝 z, ∃ hy : IsUnit (p y), r y = Checked.inv (p y) hy) :
    MDifferentiableAt I 𝓘(𝕜, F') r z :=
  mdifferentiableWithinAt_univ.mp <| hp.mdifferentiableWithinAt.inv
    (by simpa only [insert_eq_of_mem (mem_univ z), nhdsWithin_univ] using hr)

theorem MDifferentiableOn.inv (hp : MDifferentiableOn I 𝓘(𝕜, F') p s)
    (hr : ∀ y ∈ s, ∃ hy : IsUnit (p y), r y = Checked.inv (p y) hy) :
    MDifferentiableOn I 𝓘(𝕜, F') r s := fun x hx ↦ (hp x hx).inv
  (by simpa only [insert_eq_of_mem hx] using (eventually_nhdsWithin_iff.2 (.of_forall (hr ·))))

theorem MDifferentiable.inv (hp : MDifferentiable I 𝓘(𝕜, F') p) {h : ∀ y, IsUnit (p y)} :
    MDifferentiable I 𝓘(𝕜, F') (fun y ↦ Checked.inv (p y) (h y)) :=
  fun x ↦ (hp x).inv (.of_forall fun y ↦ ⟨h y, rfl⟩)

/-- The derivative of a right quotient in a normed division ring. -/
lemma HasMFDerivWithinAt.div' (hp : HasMFDerivWithinAt I 𝓘(𝕜, F') p s z p')
    (hq : HasMFDerivWithinAt I 𝓘(𝕜, F') q s z q') {hu : IsUnit (q z)}
    (hr : ∀ᶠ y in 𝓝[insert z s] z, ∃ hy : IsUnit (q y), r y = Checked.div (p y) (q y) hy) :
    HasMFDerivWithinAt I 𝓘(𝕜, F') r s z
      (p z • (-((Checked.inv (q z) hu) •> q' <• (Checked.inv (q z) hu))) +
        p' <• (Checked.inv (q z) hu) : E →L[𝕜] F') := by
  apply hasMFDerivWithinAt_of_local_chart (hz := hu)
    (f := fun y : {y : M // IsUnit (q y)} ↦ Checked.div (p y) (q y) y.property) _ hr
  let chart := extChartAt I z
  let S : Set E := chart.symm ⁻¹' s ∩ range I
  let P : E → F' := p ∘ chart.symm
  let Q : E → F' := q ∘ chart.symm
  let D : Set E := {u | IsUnit (Q u)}
  let i : D → E := Subtype.val
  have hz : IsUnit (Q (chart z)) := by
    simpa only [Q, chart, Function.comp_def, extChartAt_to_inv] using hu
  let u : D := ⟨chart z, hz⟩
  have hi : Tendsto i (𝓝[i ⁻¹' S] u) (𝓝[S] chart z) :=
    continuous_subtype_val.continuousWithinAt.tendsto_nhdsWithin (fun _ hv ↦ hv)
  have hpD := HasFDerivAtFilter.comp_tendsto (hasMFDerivWithinAt_iff_sourceChart.1 hp)
    i (hi.prodMap (tendsto_pure_pure i u))
  have hqD := (hasMFDerivWithinAt_iff_sourceChart.1 hq).inv hz
  have hval : Q (chart z) = q z := by simp only [Q, chart, Function.comp_def, extChartAt_to_inv]
  have hunit : hz.unit = hu.unit := Units.ext (hz.unit_spec.trans (hval.trans hu.unit_spec.symm))
  have hinv : (↑hz.unit⁻¹ : F') = Checked.inv (q z) hu :=
    congrArg (fun t : F'ˣ ↦ (↑t⁻¹ : F')) hunit
  have hP : P (chart z) = p z := by simp only [P, chart, Function.comp_def, extChartAt_to_inv]
  have h := HasFDerivWithinAt.mul' hpD hqD continuous_subtype_val.continuousWithinAt
  change HasFDerivWithinAt _ (P (chart z) • _ + _ <• (↑hz.unit⁻¹ : F')) _ _ _ at h
  let v := Checked.inv (q z) hu
  let c := (tangentSpaceCastModel I z).symm.toContinuousLinearMap
  have hcoeff :
      p z • ((-ContinuousLinearMap.mulLeftRight 𝕜 F' v v).comp (q' ∘L c)) +
        (p' ∘L c) <• v =
      ((p z • (-(v •> q' <• v)) + p' <• v) : E →L[𝕜] F') ∘L c := by
    ext w
    rfl
  rw [hP, hinv, hcoeff] at h
  exact h

lemma MDifferentiableWithinAt.div (hp : MDifferentiableWithinAt I 𝓘(𝕜, F') p s z)
    (hq : MDifferentiableWithinAt I 𝓘(𝕜, F') q s z)
    (hr : ∀ᶠ y in 𝓝[insert z s] z, ∃ hy : IsUnit (q y), r y = Checked.div (p y) (q y) hy) :
    MDifferentiableWithinAt I 𝓘(𝕜, F') r s z := by
  have hu : IsUnit (q z) := (mem_of_mem_nhdsWithin (mem_insert z s) hr).choose
  exact (hp.hasMFDerivWithinAt.div' hq.hasMFDerivWithinAt (hu := hu) hr).mdifferentiableWithinAt

lemma MDifferentiableAt.div (hp : MDifferentiableAt I 𝓘(𝕜, F') p z)
    (hq : MDifferentiableAt I 𝓘(𝕜, F') q z)
    (hr : ∀ᶠ y in 𝓝 z, ∃ hy : IsUnit (q y), r y = Checked.div (p y) (q y) hy) :
    MDifferentiableAt I 𝓘(𝕜, F') r z :=
  mdifferentiableWithinAt_univ.mp <| hp.mdifferentiableWithinAt.div hq.mdifferentiableWithinAt
    (by simpa only [insert_eq_of_mem (mem_univ z), nhdsWithin_univ] using hr)

lemma MDifferentiableOn.div (hp : MDifferentiableOn I 𝓘(𝕜, F') p s)
    (hq : MDifferentiableOn I 𝓘(𝕜, F') q s)
    (hr : ∀ y ∈ s, ∃ hy : IsUnit (q y), r y = Checked.div (p y) (q y) hy) :
    MDifferentiableOn I 𝓘(𝕜, F') r s := fun x hx ↦ (hp x hx).div (hq x hx)
  (by simpa only [insert_eq_of_mem hx] using (eventually_nhdsWithin_iff.2 (.of_forall (hr ·))))

lemma MDifferentiable.div (hp : MDifferentiable I 𝓘(𝕜, F') p) (hq : MDifferentiable I 𝓘(𝕜, F') q)
    {h : ∀ y, IsUnit (q y)} :
    MDifferentiable I 𝓘(𝕜, F') (fun y ↦ Checked.div (p y) (q y) (h y)) :=
  fun x ↦ (hp x).div (hq x) (.of_forall fun y ↦ ⟨h y, rfl⟩)

end DivisionRing

section Field

open scoped RightActions
open Filter

variable {z : M} {F' : Type*} [NormedField F'] [NormedAlgebra 𝕜 F'] {p q r : M → F'}
  {p' q' : TangentSpace I z →L[𝕜] F'}

lemma HasMFDerivWithinAt.inv (hp : HasMFDerivWithinAt I 𝓘(𝕜, F') p s z p')
    {hu : IsUnit (p z)} (hr : ∀ᶠ y in 𝓝[insert z s] z,
      ∃ hy : IsUnit (p y), r y = Checked.inv (p y) hy) :
    HasMFDerivWithinAt I 𝓘(𝕜, F') r s z
      (-(Checked.inv (p z ^ 2) (hu.pow 2)) • p' : E →L[𝕜] F') := by
  have hcoeff : (-(Checked.inv (p z ^ 2) (hu.pow 2)) • p' : E →L[𝕜] F') =
      -((Checked.inv (p z) hu) •> p' <• (Checked.inv (p z) hu)) := by
    ext w
    rw [← inv_pow₀ (ha := hu) 2]
    change -(Checked.inv (p z) hu ^ 2) * p' w =
      -(Checked.inv (p z) hu * p' w * Checked.inv (p z) hu)
    ring
  rw [hcoeff]
  exact hp.inv' hr

lemma HasMFDerivAt.inv (hp : HasMFDerivAt I 𝓘(𝕜, F') p z p')
    {hu : IsUnit (p z)} (hr : ∀ᶠ y in 𝓝 z, ∃ hy : IsUnit (p y), r y = Checked.inv (p y) hy) :
    HasMFDerivAt I 𝓘(𝕜, F') r z
      (-(Checked.inv (p z ^ 2) (hu.pow 2)) • p' : E →L[𝕜] F') :=
  hasMFDerivWithinAt_univ.mp <| hp.hasMFDerivWithinAt.inv (hu := hu)
    (by simpa only [insert_eq_of_mem (mem_univ z), nhdsWithin_univ] using hr)

lemma HasMFDerivWithinAt.div (hp : HasMFDerivWithinAt I 𝓘(𝕜, F') p s z p')
    (hq : HasMFDerivWithinAt I 𝓘(𝕜, F') q s z q') {hu : IsUnit (q z)}
    (hr : ∀ᶠ y in 𝓝[insert z s] z, ∃ hy : IsUnit (q y), r y = Checked.div (p y) (q y) hy) :
    HasMFDerivWithinAt I 𝓘(𝕜, F') r s z
      ((Checked.inv (q z) hu) • p' - (Checked.div (p z) (q z ^ 2) (hu.pow 2)) • q' :
        E →L[𝕜] F') := by
  have hcoeff :
      ((Checked.inv (q z) hu) • p' - (Checked.div (p z) (q z ^ 2) (hu.pow 2)) • q' :
        E →L[𝕜] F') =
      p z • (-((Checked.inv (q z) hu) •> q' <• (Checked.inv (q z) hu))) +
        p' <• (Checked.inv (q z) hu) := by
    ext w
    rw [div_eq_mul_inv₀, ← inv_pow₀ (ha := hu) 2]
    change Checked.inv (q z) hu * p' w - (p z * Checked.inv (q z) hu ^ 2) * q' w =
      p z * -(Checked.inv (q z) hu * q' w * Checked.inv (q z) hu) + p' w * Checked.inv (q z) hu
    ring
  rw [hcoeff]
  exact hp.div' hq hr

lemma HasMFDerivAt.div (hp : HasMFDerivAt I 𝓘(𝕜, F') p z p')
    (hq : HasMFDerivAt I 𝓘(𝕜, F') q z q') {hu : IsUnit (q z)}
    (hr : ∀ᶠ y in 𝓝 z, ∃ hy : IsUnit (q y), r y = Checked.div (p y) (q y) hy) :
    HasMFDerivAt I 𝓘(𝕜, F') r z
      ((Checked.inv (q z) hu) • p' - (Checked.div (p z) (q z ^ 2) (hu.pow 2)) • q' :
        E →L[𝕜] F') :=
  hasMFDerivWithinAt_univ.mp <| hp.hasMFDerivWithinAt.div hq.hasMFDerivWithinAt (hu := hu)
    (by simpa only [insert_eq_of_mem (mem_univ z), nhdsWithin_univ] using hr)

end Field

end Arithmetic

end SpecificFunctions
