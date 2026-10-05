/-
Copyright (c) 2026 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Exact.Sequence
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The index of a linear map

In this file we define the index of a Fredholm linear map between vector spaces and provide some
basic API.

A linear map between vector spaces over a division ring is Fredholm if its kernel and cokernel are
finite-dimensional, and its index is then `dim ker - dim coker`. The index is defined exactly for
Fredholm maps: otherwise one of the dimensions is infinite.

## Main definitions / results:

* `LinearMap.IsFredholm`: the kernel and cokernel are finite-dimensional.
* `LinearMap.index`: the index of a Fredholm linear map, with sign convention
  `index = dim ker - dim coker`.
* `LinearMap.index_comp`: the index is additive under composition.

## References

* J. H. Shapiro, *Algebraic Fredholm theory*, lecture notes (2011), Definitions 4.1 and 4.11 and
  Theorem 5.1.

-/

noncomputable section

namespace LinearMap

open Function Module

variable {M N P : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
variable {k : Type*} [DivisionRing k] [Module k M] [Module k N] [Module k P]

/-- A linear map between vector spaces is Fredholm if its kernel and cokernel are
finite-dimensional. -/
@[mk_iff]
public structure IsFredholm (f : M →ₗ[k] N) : Prop where
  /-- The kernel is finite-dimensional. -/
  finiteDimensional_ker : FiniteDimensional k f.ker
  /-- The cokernel is finite-dimensional. -/
  finiteDimensional_coker : FiniteDimensional k (N ⧸ f.range)

/-- The index of a Fredholm linear map with sign convention `index = dim ker - dim coker`. -/
@[nolint unusedArguments]
public def index (f : M →ₗ[k] N) (_hf : f.IsFredholm) : ℤ :=
  finrank k f.ker - finrank k (N ⧸ f.range)

variable {f : M →ₗ[k] N}

public lemma index_eq_finrank_sub (hf : f.IsFredholm) :
    f.index hf = finrank k f.ker - finrank k (N ⧸ f.range) := by
  rfl

public lemma IsFredholm.of_finiteDimensional [FiniteDimensional k M] [FiniteDimensional k N]
    (f : M →ₗ[k] N) : f.IsFredholm :=
  ⟨inferInstance, inferInstance⟩

@[simp] public lemma index_zero (h : (0 : M →ₗ[k] N).IsFredholm) :
    (0 : M →ₗ[k] N).index h = finrank k M - finrank k N := by
  rw [index_eq_finrank_sub, ker_zero, range_zero]
  simpa using (Submodule.quotEquivOfEqBot _ rfl).finrank_eq

public lemma IsFredholm.of_injective (hf : Injective f) [FiniteDimensional k (N ⧸ f.range)] :
    f.IsFredholm where
  finiteDimensional_ker := by rw [ker_eq_bot.2 hf]; infer_instance
  finiteDimensional_coker := inferInstance

public lemma index_of_injective (hf : Injective f) (h : f.IsFredholm) :
    f.index h = - finrank k (N ⧸ f.range) := by
  simpa [index_eq_finrank_sub] using ker_eq_bot.2 hf ▸ finrank_bot _ _

@[simp] public lemma index_subtype {S : Submodule k M} (h : S.subtype.IsFredholm) :
    S.subtype.index h = - finrank k (M ⧸ S) := by
  rw [index_of_injective S.injective_subtype, S.range_subtype]

public lemma IsFredholm.of_surjective (hf : Surjective f) [FiniteDimensional k f.ker] :
    f.IsFredholm where
  finiteDimensional_ker := inferInstance
  finiteDimensional_coker := by rw [range_eq_top.mpr hf]; infer_instance

public lemma index_of_surjective (hf : Surjective f) (h : f.IsFredholm) :
    f.index h = finrank k f.ker := by
  rw [index_eq_finrank_sub, range_eq_top.mpr hf]
  simp [finrank_eq_zero_of_subsingleton]

@[simp] public lemma index_mkQ {S : Submodule k M} (h : S.mkQ.IsFredholm) :
    S.mkQ.index h = finrank k S := by
  rw [index_of_surjective S.mkQ_surjective, S.ker_mkQ]

@[simp] public lemma index_projectionOnto {S T : Submodule k M} (hST : IsCompl S T)
    (h : (S.projectionOnto T hST).IsFredholm) :
    (S.projectionOnto T hST).index h = finrank k T := by
  rw [index_of_surjective (Submodule.projectionOnto_surjective hST), Submodule.ker_projectionOnto]

public lemma IsFredholm.of_bijective (hf : Bijective f) : f.IsFredholm :=
  have : FiniteDimensional k f.ker := by rw [ker_eq_bot.2 hf.injective]; infer_instance
  .of_surjective hf.surjective

public lemma index_of_bijective (hf : Bijective f) (h : f.IsFredholm) :
    f.index h = 0 := by
  rw [index_of_surjective hf.surjective, ker_eq_bot.mpr hf.injective, finrank_bot, Nat.cast_zero]

@[simp] public lemma index_id (h : (id : M →ₗ[k] M).IsFredholm) :
    (id : M →ₗ[k] M).index h = 0 :=
  index_of_bijective bijective_id h

@[simp] public lemma _root_.LinearEquiv.index_eq_zero {e : M ≃ₗ[k] N}
    (h : e.toLinearMap.IsFredholm) : e.toLinearMap.index h = 0 :=
  index_of_bijective e.bijective h

public lemma IsFredholm.neg (hf : f.IsFredholm) : (-f).IsFredholm := by
  obtain ⟨h₁, h₂⟩ := hf
  exact ⟨by rwa [ker_neg], by rwa [range_neg]⟩

@[simp] public lemma index_neg (hf : f.IsFredholm) :
    (-f).index hf.neg = f.index hf := by
  rw [index_eq_finrank_sub, index_eq_finrank_sub, ker_neg, range_neg]

public lemma index_eq_of_finiteDimensional [FiniteDimensional k M] [FiniteDimensional k N]
    (h : f.IsFredholm) : f.index h = finrank k M - finrank k N := by
  -- `0 → f.ker → M → N → f.coker → 0`
  rw [index_eq_finrank_sub]
  have h₁ := f.range.finrank_quotient_add_finrank
  have h₂ := f.quotKerEquivRange.finrank_eq
  have h₃ := f.ker.finrank_quotient_add_finrank
  lia

open Submodule in
/-- The composition of Fredholm maps is Fredholm. -/
public lemma IsFredholm.comp {g : N →ₗ[k] P} (hg : g.IsFredholm) (hf : f.IsFredholm) :
    (g ∘ₗ f).IsFredholm := by
  obtain ⟨_, _⟩ := hf
  obtain ⟨_, _⟩ := hg
  exact ⟨by rw [ker_comp]; infer_instance, by rw [range_comp]; infer_instance⟩

set_option backward.isDefEq.respectTransparency.types false in
open Submodule in
@[simp] public lemma index_comp {g : N →ₗ[k] P} (hg : g.IsFredholm) (hf : f.IsFredholm) :
    (g ∘ₗ f).index (hg.comp hf) = g.index hg + f.index hf := by
  -- `0 → f.ker → (g ∘ₗ f).ker → g.ker → f.coker → (g ∘ₗ f).coker → g.coker → 0`
  have hgf := hg.comp hf
  obtain ⟨_, _⟩ := hf
  obtain ⟨_, _⟩ := hg
  obtain ⟨_, _⟩ := hgf
  have aux : f.range ≤ comap g (g ∘ₗ f).range := by rw [← map_le_iff_le_comap, range_comp]
  let f₀ : f.ker →ₗ[k] (g ∘ₗ f).ker := inclusion <| ker_le_ker_comp f g
  let f₁ : (g ∘ₗ f).ker →ₗ[k] g.ker := f.restrict <| by simp
  let f₂ : g.ker →ₗ[k] N ⧸ f.range := f.range.mkQ ∘ₗ g.ker.subtype
  let f₃ : (N ⧸ f.range) →ₗ[k] P ⧸ (g ∘ₗ f).range := f.range.mapQ (g ∘ₗ f).range g aux
  let f₄ : (P ⧸ (g ∘ₗ f).range) →ₗ[k] P ⧸ g.range := factor <| range_comp_le_range f g
  have h₀ : Injective f₀ := inclusion_injective _
  have h₁ : Exact f₀ f₁ := by rw [exact_iff]; simp [f₀, f₁, ker_restrict, range_inclusion]
  have h₂ : Exact f₁ f₂ := by rw [exact_iff]; simp [f₁, f₂, ker_comp, map_comap_eq]
  have h₃ : Exact f₂ f₃ := by rw [exact_iff]; simp [f₂, f₃, range_comp, ker_mapQ, comap_map_eq]
  have h₄ : Exact f₃ f₄ := by rw [exact_iff]; simp [f₃, f₄, factor, ker_mapQ, range_mapQ]
  have h₅ : Surjective f₄ := factor_surjective _
  grind [index, sum_neg_one_pow_finrank_eq_zero_of_exact_six f₀ f₁ f₂ f₃ f₄ h₀ h₁ h₂ h₃ h₄ h₅]

end LinearMap

section Field

namespace LinearMap

open Module

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]
variable {k : Type*} [Field k] [Module k M] [Module k N] {f : M →ₗ[k] N}

public lemma IsFredholm.smul (hf : f.IsFredholm) {t : k} (ht : t ≠ 0) : (t • f).IsFredholm := by
  obtain ⟨h₁, h₂⟩ := hf
  exact ⟨by rwa [ker_smul _ _ ht], by rwa [range_smul _ _ ht]⟩

public lemma index_smul (hf : f.IsFredholm) {t : k} (ht : t ≠ 0) :
    (t • f).index (hf.smul ht) = f.index hf := by
  rw [index_eq_finrank_sub, index_eq_finrank_sub, ker_smul _ _ ht, range_smul _ _ ht]

end LinearMap

end Field
