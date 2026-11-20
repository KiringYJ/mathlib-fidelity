/-
Copyright (c) 2022 Jiale Miao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiale Miao, Kevin Buzzard, Alexander Bentkamp
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Gram-Schmidt Orthogonalization and Orthonormalization

In this file we introduce Gram-Schmidt Orthogonalization and Orthonormalization.

The Gram-Schmidt process takes a set of vectors as input
and outputs a set of orthogonal vectors which have the same span.

## Main results

- `gramSchmidt`: the Gram-Schmidt process
- `gramSchmidt_orthogonal`: `gramSchmidt` produces an orthogonal system of vectors.
- `span_gramSchmidt`: `gramSchmidt` preserves span of vectors.
- `gramSchmidt_linearIndependent`: if the input vectors of `gramSchmidt` are linearly independent,
  then so are the output vectors.
- `gramSchmidt_ne_zero`: if the input vectors of `gramSchmidt` are linearly independent,
  then the output vectors are non-zero.
- `gramSchmidtBasis`: the basis produced by the Gram-Schmidt process when given a basis as input
- `gramSchmidtNormed`:
  the normalized `gramSchmidt` process, i.e each vector in `gramSchmidtNormed` has unit length
- `gramSchmidt_orthonormal`: `gramSchmidtNormed` produces an orthonormal system of vectors.
- `gramSchmidtOrthonormalBasis`: orthonormal basis constructed by the Gram-Schmidt process from
  an indexed set of vectors of the right size
-/

@[expose] public section


open Finset Submodule Module

variable (𝕜 : Type*) {E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι]

attribute [local instance] IsWellOrder.toHasWellFounded

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

namespace InnerProductSpace

/-- The Gram-Schmidt process takes a set of vectors as input
and outputs a set of orthogonal vectors which have the same span. -/
noncomputable def gramSchmidt [WellFoundedLT ι] (f : ι → E) (n : ι) : E :=
  f n - ∑ i : Iio n, (𝕜 ∙ gramSchmidt f i).starProjection (f n)
termination_by n
decreasing_by exact mem_Iio.1 i.2

variable [WellFoundedLT ι]

/-- This lemma uses `∑ i in` instead of `∑ i :`. -/
theorem gramSchmidt_def (f : ι → E) (n : ι) :
    gramSchmidt 𝕜 f n = f n - ∑ i ∈ Iio n, (𝕜 ∙ gramSchmidt 𝕜 f i).starProjection (f n) := by
  rw [← sum_attach, attach_eq_univ, gramSchmidt]

theorem gramSchmidt_def' (f : ι → E) (n : ι) :
    f n = gramSchmidt 𝕜 f n + ∑ i ∈ Iio n, (𝕜 ∙ gramSchmidt 𝕜 f i).starProjection (f n) := by
  rw [gramSchmidt_def, sub_add_cancel]

open scoped Classical in
theorem gramSchmidt_def'' (f : ι → E) (n : ι) :
    f n = gramSchmidt 𝕜 f n + ∑ i ∈ Iio n,
      if hi : gramSchmidt 𝕜 f i = 0 then 0 else
        Checked.div ⟪gramSchmidt 𝕜 f i, f n⟫ ((‖gramSchmidt 𝕜 f i‖ ^ 2 : ℝ) : 𝕜)
          (RCLike.ofReal_ne_zero.mpr
            (pow_ne_zero 2 (norm_ne_zero_iff.mpr hi))).isUnit • gramSchmidt 𝕜 f i := by
  simpa only [starProjection_singleton] using gramSchmidt_def' 𝕜 f n

@[simp]
theorem gramSchmidt_bot {ι : Type*} [LinearOrder ι] [LocallyFiniteOrder ι] [OrderBot ι]
    [WellFoundedLT ι] (f : ι → E) : gramSchmidt 𝕜 f ⊥ = f ⊥ := by
  rw [gramSchmidt_def, Iio_eq_Ico, Finset.Ico_self, Finset.sum_empty, sub_zero]

@[simp]
theorem gramSchmidt_zero (n : ι) : gramSchmidt 𝕜 (0 : ι → E) n = 0 := by rw [gramSchmidt_def]; simp

/-- **Gram-Schmidt Orthogonalisation**:
`gramSchmidt` produces an orthogonal system of vectors. -/
theorem gramSchmidt_orthogonal (f : ι → E) {a b : ι} (h₀ : a ≠ b) :
    ⟪gramSchmidt 𝕜 f a, gramSchmidt 𝕜 f b⟫ = 0 := by
  suffices ∀ a b : ι, a < b → ⟪gramSchmidt 𝕜 f a, gramSchmidt 𝕜 f b⟫ = 0 by
    rcases h₀.lt_or_gt with ha | hb
    · exact this _ _ ha
    · rw [inner_eq_zero_symm]
      exact this _ _ hb
  clear h₀ a b
  intro a b h₀
  revert a
  apply wellFounded_lt.induction b
  intro b ih a h₀
  simp only [gramSchmidt_def 𝕜 f b, inner_sub_right, inner_sum]
  rw [Finset.sum_eq_single_of_mem a (Finset.mem_Iio.mpr h₀)]
  · rw [← inner_starProjection_left_eq_right,
      starProjection_eq_self_iff.mpr (mem_span_singleton_self _), sub_self]
  intro i hi hia
  have horth : ⟪gramSchmidt 𝕜 f a, gramSchmidt 𝕜 f i⟫ = 0 := by
    rcases hia.lt_or_gt with hia₁ | hia₂
    · rw [inner_eq_zero_symm]
      exact ih a h₀ i hia₁
    · exact ih i (mem_Iio.1 hi) a hia₂
  rw [← inner_starProjection_left_eq_right]
  have hmem := mem_orthogonal_singleton_iff_inner_left.mpr horth
  simp [starProjection_apply, orthogonalProjectionOnto_apply_of_mem_orthogonal hmem]

/-- This is another version of `gramSchmidt_orthogonal` using `Pairwise` instead. -/
theorem gramSchmidt_pairwise_orthogonal (f : ι → E) :
    Pairwise fun a b => ⟪gramSchmidt 𝕜 f a, gramSchmidt 𝕜 f b⟫ = 0 := fun _ _ =>
  gramSchmidt_orthogonal 𝕜 f

theorem gramSchmidt_inv_triangular (v : ι → E) {i j : ι} (hij : i < j) :
    ⟪gramSchmidt 𝕜 v j, v i⟫ = 0 := by
  rw [gramSchmidt_def' 𝕜 v]
  simp only [inner_add_right, inner_sum]
  set b : ι → E := gramSchmidt 𝕜 v
  convert! zero_add (0 : 𝕜)
  · exact gramSchmidt_orthogonal 𝕜 v hij.ne'
  apply Finset.sum_eq_zero
  rintro k hki'
  have hki : k < i := by simpa using hki'
  have : ⟪b j, b k⟫ = 0 := gramSchmidt_orthogonal 𝕜 v (hki.trans hij).ne'
  rcases mem_span_singleton.mp ((𝕜 ∙ b k).starProjection_apply_mem (v i)) with ⟨c, hc⟩
  rw [← hc, inner_smul_right, this, mul_zero]

open Submodule Set

theorem mem_span_gramSchmidt (f : ι → E) {i j : ι} (hij : i ≤ j) :
    f i ∈ span 𝕜 (gramSchmidt 𝕜 f '' Set.Iic j) := by
  rw [gramSchmidt_def' 𝕜 f i]
  exact Submodule.add_mem _ (subset_span <| mem_image_of_mem _ hij)
    (Submodule.sum_mem _ fun k hk =>
      ((span_singleton_le_iff_mem (gramSchmidt 𝕜 f k)
        (span 𝕜 (gramSchmidt 𝕜 f '' Set.Iic j))).mpr <| subset_span <|
          mem_image_of_mem (gramSchmidt 𝕜 f) <| (Finset.mem_Iio.1 hk).le.trans hij)
        ((𝕜 ∙ gramSchmidt 𝕜 f k).starProjection_apply_mem (f i)))

theorem gramSchmidt_mem_span (f : ι → E) :
    ∀ {j i}, i ≤ j → gramSchmidt 𝕜 f i ∈ span 𝕜 (f '' Set.Iic j) := by
  intro j i hij
  rw [gramSchmidt_def 𝕜 f i]
  refine Submodule.sub_mem _ (subset_span (mem_image_of_mem _ hij))
    (Submodule.sum_mem _ fun k hk => ?_)
  let hkj : k < j := (Finset.mem_Iio.1 hk).trans_le hij
  exact ((span_singleton_le_iff_mem _ _).mpr <|
    span_mono (image_mono <| Set.Iic_subset_Iic.2 hkj.le) <| gramSchmidt_mem_span _ le_rfl)
    ((𝕜 ∙ gramSchmidt 𝕜 f k).starProjection_apply_mem (f i))
termination_by j => j

theorem span_gramSchmidt_Iic (f : ι → E) (c : ι) :
    span 𝕜 (gramSchmidt 𝕜 f '' Set.Iic c) = span 𝕜 (f '' Set.Iic c) :=
  span_eq_span (Set.image_subset_iff.2 fun _ => gramSchmidt_mem_span _ _) <|
    Set.image_subset_iff.2 fun _ => mem_span_gramSchmidt _ _

theorem span_gramSchmidt_Iio (f : ι → E) (c : ι) :
    span 𝕜 (gramSchmidt 𝕜 f '' Set.Iio c) = span 𝕜 (f '' Set.Iio c) :=
  span_eq_span (Set.image_subset_iff.2 fun _ hi =>
    span_mono (image_mono <| Iic_subset_Iio.2 hi) <| gramSchmidt_mem_span _ _ le_rfl) <|
      Set.image_subset_iff.2 fun _ hi =>
        span_mono (image_mono <| Iic_subset_Iio.2 hi) <| mem_span_gramSchmidt _ _ le_rfl

/-- `gramSchmidt` preserves span of vectors. -/
theorem span_gramSchmidt (f : ι → E) : span 𝕜 (range (gramSchmidt 𝕜 f)) = span 𝕜 (range f) :=
  span_eq_span (range_subset_iff.2 fun _ =>
    span_mono (image_subset_range _ _) <| gramSchmidt_mem_span _ _ le_rfl) <|
      range_subset_iff.2 fun _ =>
        span_mono (image_subset_range _ _) <| mem_span_gramSchmidt _ _ le_rfl

/-- If given an orthogonal set of vectors, `gramSchmidt` fixes its input. -/
theorem gramSchmidt_of_orthogonal {f : ι → E} (hf : Pairwise (⟪f ·, f ·⟫ = 0)) :
    gramSchmidt 𝕜 f = f := by
  ext i
  rw [gramSchmidt_def]
  trans f i - 0
  · congr
    apply Finset.sum_eq_zero
    intro j hj
    rw [Submodule.starProjection_apply, Submodule.coe_eq_zero]
    suffices span 𝕜 (f '' Set.Iic j) ⟂ 𝕜 ∙ f i by
      apply orthogonalProjectionOnto_apply_of_mem_orthogonal
      rw [mem_orthogonal_singleton_iff_inner_left, ← mem_orthogonal_singleton_iff_inner_right]
      exact this (gramSchmidt_mem_span 𝕜 f (le_refl j))
    rw [isOrtho_span]
    rintro u ⟨k, hk, rfl⟩ v (rfl : v = f i)
    apply hf
    exact (lt_of_le_of_lt hk (Finset.mem_Iio.mp hj)).ne
  · simp

variable {𝕜}

theorem gramSchmidt_ne_zero_coe {f : ι → E} (n : ι)
    (h₀ : LinearIndependent 𝕜 (f ∘ ((↑) : Set.Iic n → ι))) : gramSchmidt 𝕜 f n ≠ 0 := by
  by_contra h
  have h₁ : f n ∈ span 𝕜 (f '' Set.Iio n) := by
    rw [← span_gramSchmidt_Iio 𝕜 f n, gramSchmidt_def' 𝕜 f, h, zero_add]
    apply Submodule.sum_mem _ _
    intro a ha
    exact ((span_singleton_le_iff_mem (gramSchmidt 𝕜 f a)
      (span 𝕜 (gramSchmidt 𝕜 f '' Set.Iio n))).mpr <|
        subset_span ⟨a, Finset.mem_Iio.mp ha, rfl⟩)
      ((𝕜 ∙ gramSchmidt 𝕜 f a).starProjection_apply_mem (f n))
  have h₂ : (f ∘ ((↑) : Set.Iic n → ι)) ⟨n, le_refl n⟩ ∈
      span 𝕜 (f ∘ ((↑) : Set.Iic n → ι) '' Set.Iio ⟨n, le_refl n⟩) := by
    rw [Set.image_comp]
    simpa using h₁
  apply LinearIndependent.notMem_span_image h₀ _ h₂
  simp only [Set.mem_Iio, lt_self_iff_false, not_false_iff]

/-- If the input vectors of `gramSchmidt` are linearly independent,
then the output vectors are non-zero. -/
theorem gramSchmidt_ne_zero {f : ι → E} (n : ι) (h₀ : LinearIndependent 𝕜 f) :
    gramSchmidt 𝕜 f n ≠ 0 :=
  gramSchmidt_ne_zero_coe _ (LinearIndependent.comp h₀ _ Subtype.coe_injective)

/-- `gramSchmidt` produces a triangular matrix of vectors when given a basis. -/
theorem gramSchmidt_triangular {i j : ι} (hij : i < j) (b : Basis ι 𝕜 E) :
    b.repr (gramSchmidt 𝕜 b i) j = 0 := by
  have : gramSchmidt 𝕜 b i ∈ span 𝕜 (gramSchmidt 𝕜 b '' Set.Iio j) :=
    subset_span ((Set.mem_image _ _ _).2 ⟨i, hij, rfl⟩)
  have : gramSchmidt 𝕜 b i ∈ span 𝕜 (b '' Set.Iio j) := by rwa [← span_gramSchmidt_Iio 𝕜 b j]
  have : ↑(b.repr (gramSchmidt 𝕜 b i)).support ⊆ Set.Iio j :=
    Basis.repr_support_subset_of_mem_span b (Set.Iio j) this
  exact (Finsupp.mem_supported' _ _).1 ((Finsupp.mem_supported 𝕜 _).2 this) j Set.self_notMem_Iio

/-- `gramSchmidt` produces linearly independent vectors when given linearly independent vectors. -/
theorem gramSchmidt_linearIndependent {f : ι → E} (h₀ : LinearIndependent 𝕜 f) :
    LinearIndependent 𝕜 (gramSchmidt 𝕜 f) :=
  linearIndependent_of_ne_zero_of_inner_eq_zero (fun _ => gramSchmidt_ne_zero _ h₀) fun _ _ =>
    gramSchmidt_orthogonal 𝕜 f

/-- When given a basis, `gramSchmidt` produces a basis. -/
noncomputable def gramSchmidtBasis (b : Basis ι 𝕜 E) : Basis ι 𝕜 E :=
  Basis.mk (gramSchmidt_linearIndependent b.linearIndependent)
    ((span_gramSchmidt 𝕜 b).trans b.span_eq).ge

theorem coe_gramSchmidtBasis (b : Basis ι 𝕜 E) : (gramSchmidtBasis b : ι → E) = gramSchmidt 𝕜 b :=
  Basis.coe_mk _ _

variable (𝕜) in
/-- Normalize the nonzero vectors produced by `gramSchmidt`. The index records the exact
domain of normalization, including when the original family is linearly dependent. -/
noncomputable def gramSchmidtNormed (f : ι → E)
    (n : {i // gramSchmidt 𝕜 f i ≠ 0}) : E :=
  Checked.inv (‖gramSchmidt 𝕜 f n‖ : 𝕜)
    (RCLike.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr n.2)).isUnit • gramSchmidt 𝕜 f n

theorem gramSchmidtNormed_unit_length' {f : ι → E} (n : {i // gramSchmidt 𝕜 f i ≠ 0}) :
    ‖gramSchmidtNormed 𝕜 f n‖ = 1 := by
  simp [gramSchmidtNormed, norm_smul]

theorem gramSchmidtNormed_unit_length_coe {f : ι → E} (n : ι)
    (h₀ : LinearIndependent 𝕜 (f ∘ ((↑) : Set.Iic n → ι))) :
    ‖gramSchmidtNormed 𝕜 f ⟨n, gramSchmidt_ne_zero_coe n h₀⟩‖ = 1 :=
  gramSchmidtNormed_unit_length' _

theorem gramSchmidtNormed_unit_length {f : ι → E} (n : ι) (h₀ : LinearIndependent 𝕜 f) :
    ‖gramSchmidtNormed 𝕜 f ⟨n, gramSchmidt_ne_zero n h₀⟩‖ = 1 :=
  gramSchmidtNormed_unit_length' _

/-- **Gram-Schmidt Orthonormalization**:
the nonzero vectors produced by `gramSchmidt` form an orthonormal family after normalization. -/
theorem gramSchmidtNormed_orthonormal' (f : ι → E) :
    Orthonormal 𝕜 (gramSchmidtNormed 𝕜 f) := by
  refine ⟨gramSchmidtNormed_unit_length', ?_⟩
  rintro i j (hij : ¬_)
  rw [Subtype.ext_iff] at hij
  simp [gramSchmidtNormed, inner_smul_left, inner_smul_right, gramSchmidt_orthogonal 𝕜 f hij]

/-- **Gram-Schmidt Orthonormalization**:
normalizing the orthogonalization of a linearly independent family keeps every original index. -/
theorem gramSchmidtNormed_orthonormal {f : ι → E} (h₀ : LinearIndependent 𝕜 f) :
    Orthonormal 𝕜 (fun i ↦ gramSchmidtNormed 𝕜 f ⟨i, gramSchmidt_ne_zero i h₀⟩) :=
  (gramSchmidtNormed_orthonormal' f).comp _ (fun _ _ h ↦ congrArg Subtype.val h)

open Submodule Set

theorem span_gramSchmidtNormed (f : ι → E) (s : Set ι) :
    span 𝕜 (gramSchmidtNormed 𝕜 f '' (Subtype.val ⁻¹' s)) =
      span 𝕜 (gramSchmidt 𝕜 f '' s) := by
  refine span_eq_span
    (Set.image_subset_iff.2 fun i hi => smul_mem _ _ <| subset_span <| mem_image_of_mem _ hi)
    (Set.image_subset_iff.2 fun i hi => ?_)
  change gramSchmidt 𝕜 f i ∈ span 𝕜 (gramSchmidtNormed 𝕜 f '' (Subtype.val ⁻¹' s))
  by_cases h : gramSchmidt 𝕜 f i = 0
  · rw [h]
    exact zero_mem _
  · have hi' : gramSchmidt 𝕜 f i =
        (‖gramSchmidt 𝕜 f i‖ : 𝕜) • gramSchmidtNormed 𝕜 f ⟨i, h⟩ := by
      simp [gramSchmidtNormed, smul_smul]
    rw [hi']
    exact smul_mem _ _ (subset_span ⟨⟨i, h⟩, hi, rfl⟩)

theorem span_gramSchmidtNormed_range (f : ι → E) :
    span 𝕜 (range (gramSchmidtNormed 𝕜 f)) = span 𝕜 (range (gramSchmidt 𝕜 f)) := by
  simpa only [preimage_univ, image_univ] using span_gramSchmidtNormed f univ

/-- `gramSchmidtNormed` produces linearly independent vectors when given linearly independent
vectors. -/
theorem gramSchmidtNormed_linearIndependent {f : ι → E} (h₀ : LinearIndependent 𝕜 f) :
    LinearIndependent 𝕜 (fun i ↦ gramSchmidtNormed 𝕜 f ⟨i, gramSchmidt_ne_zero i h₀⟩) :=
  (gramSchmidtNormed_orthonormal h₀).linearIndependent

section OrthonormalBasis

variable [Fintype ι] [FiniteDimensional 𝕜 E] (h : finrank 𝕜 E = Fintype.card ι) (f : ι → E)

/-- Given an indexed family `f : ι → E` of vectors in an inner product space `E`, for which the
size of the index set is the dimension of `E`, produce an orthonormal basis for `E` which agrees
with the orthonormal set produced by the Gram-Schmidt orthonormalization process on the elements of
`ι` for which this process gives a nonzero number. -/
noncomputable def gramSchmidtOrthonormalBasis : OrthonormalBasis ι 𝕜 E :=
  ((gramSchmidtNormed_orthonormal' f).exists_orthonormalBasis_extension_of_card_eq h).choose

theorem gramSchmidtOrthonormalBasis_apply {f : ι → E} {i : ι} (hi : gramSchmidt 𝕜 f i ≠ 0) :
    gramSchmidtOrthonormalBasis h f i = gramSchmidtNormed 𝕜 f ⟨i, hi⟩ :=
  ((gramSchmidtNormed_orthonormal' f).exists_orthonormalBasis_extension_of_card_eq h).choose_spec
    ⟨i, hi⟩

theorem gramSchmidtOrthonormalBasis_apply_of_orthogonal {f : ι → E}
    (hf : Pairwise fun i j => ⟪f i, f j⟫ = 0) {i : ι} (hi : f i ≠ 0) :
    gramSchmidtOrthonormalBasis h f i = (‖f i‖⁻¹ : 𝕜) • f i := by
  have hi' : gramSchmidt 𝕜 f i ≠ 0 := by
    simpa only [gramSchmidt_of_orthogonal 𝕜 hf] using hi
  simpa only [gramSchmidtNormed, gramSchmidt_of_orthogonal 𝕜 hf, RCLike.ofReal_inv] using
    gramSchmidtOrthonormalBasis_apply h hi'

theorem inner_gramSchmidtOrthonormalBasis_eq_zero {f : ι → E} {i : ι}
    (hi : gramSchmidt 𝕜 f i = 0) (j : ι) : ⟪gramSchmidtOrthonormalBasis h f i, f j⟫ = 0 := by
  rw [← mem_orthogonal_singleton_iff_inner_right]
  suffices span 𝕜 (gramSchmidt 𝕜 f '' Set.Iic j) ⟂ 𝕜 ∙ gramSchmidtOrthonormalBasis h f i from
    this (mem_span_gramSchmidt 𝕜 f le_rfl)
  rw [isOrtho_span]
  rintro u ⟨k, _, rfl⟩ v (rfl : v = _)
  by_cases hk : gramSchmidt 𝕜 f k = 0
  · rw [hk, inner_zero_left]
  have : k ≠ i := by
    rintro rfl
    exact hk hi
  have hnorm : gramSchmidt 𝕜 f k =
      (‖gramSchmidt 𝕜 f k‖ : 𝕜) • gramSchmidtOrthonormalBasis h f k := by
    rw [gramSchmidtOrthonormalBasis_apply h hk]
    simp [gramSchmidtNormed, smul_smul]
  rw [hnorm, inner_smul_left, (gramSchmidtOrthonormalBasis h f).orthonormal.2 this, mul_zero]

theorem gramSchmidtOrthonormalBasis_inv_triangular {i j : ι} (hij : i < j) :
    ⟪gramSchmidtOrthonormalBasis h f j, f i⟫ = 0 := by
  by_cases hi : gramSchmidt 𝕜 f j = 0
  · rw [inner_gramSchmidtOrthonormalBasis_eq_zero h hi]
  · simp [gramSchmidtOrthonormalBasis_apply h hi, gramSchmidtNormed, inner_smul_left,
      gramSchmidt_inv_triangular 𝕜 f hij]

theorem gramSchmidtOrthonormalBasis_inv_triangular' {i j : ι} (hij : i < j) :
    (gramSchmidtOrthonormalBasis h f).repr (f i) j = 0 := by
  simpa [OrthonormalBasis.repr_apply_apply] using gramSchmidtOrthonormalBasis_inv_triangular h f hij

/-- Given an indexed family `f : ι → E` of vectors in an inner product space `E`, for which the
size of the index set is the dimension of `E`, the matrix of coefficients of `f` with respect to the
orthonormal basis `gramSchmidtOrthonormalBasis` constructed from `f` is upper-triangular. -/
theorem gramSchmidtOrthonormalBasis_inv_isUpperTriangular :
    ((gramSchmidtOrthonormalBasis h f).toBasis.toMatrix f).IsUpperTriangular := fun _ _ =>
  gramSchmidtOrthonormalBasis_inv_triangular' h f

@[deprecated (since := "2026-07-30")]
alias gramSchmidtOrthonormalBasis_inv_blockTriangular :=
  gramSchmidtOrthonormalBasis_inv_isUpperTriangular

theorem gramSchmidtOrthonormalBasis_det [DecidableEq ι] :
    (gramSchmidtOrthonormalBasis h f).toBasis.det f =
      ∏ i, ⟪gramSchmidtOrthonormalBasis h f i, f i⟫ := by
  convert! Matrix.det_of_isUpperTriangular (gramSchmidtOrthonormalBasis_inv_isUpperTriangular h f)
  exact ((gramSchmidtOrthonormalBasis h f).repr_apply_apply (f _) _).symm

end OrthonormalBasis

end InnerProductSpace
