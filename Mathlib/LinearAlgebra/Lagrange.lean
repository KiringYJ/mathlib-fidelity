/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Wrenna Robson
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Pi
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.RingTheory.Polynomial.Basic

/-!
# Lagrange interpolation

## Main definitions
* In everything that follows, `s : Finset ι` is a finite set of indices, with `v : ι → F` an
  indexing of the field over some type. We call the image of `v` on `s` the interpolation nodes,
  though strictly unique nodes are only defined when `v` is injective on `s`.
* `Lagrange.basisDivisor x y hxy`, with `x y : F` and `hxy : x ≠ y`. These are the normalised
  irreducible factors of the Lagrange basis polynomials. They evaluate to `1` at `x` and `0` at
  `y`.
* `Lagrange.basis s v i hvi` with `i : ι`: the Lagrange basis polynomial that evaluates to `1` at
  `v i` and `0` at `v j` for `j ∈ s` with `j ≠ i`. It is defined when no other index of `s` has
  the node `v i`, that is `hvi : ∀ ⦃j⦄, j ∈ s → v i = v j → i = j`, which makes its denominator
  `∏ j ∈ s.erase i, (v i - v j)` invertible. When `v` is injective on `s` (`hvs : Set.InjOn v s`)
  and `hi : i ∈ s`, `hvs hi` is such evidence.
* `Lagrange.interpolate s v hvs r`, where `hvs : Set.InjOn v s` and `r : ι → F` is a function from
  the fintype to the field: the Lagrange interpolant that evaluates to `r i` at `v i` for all
  `i ∈ s`. The `r i` are the _values_ associated with the _nodes_ `v i`.

## Implementation notes

Quotients by differences of nodes use the checked inverse and division of the field, so each
construction takes as an argument the distinctness of the nodes whose differences it inverts. A
sum over `s` of terms that need such a quotient for their own index is indexed by `s` itself
(`∑ i : s, …`), and the evidence is taken from the membership `i.2 : ↑i ∈ s`.
-/

@[expose] public section


open Polynomial

section PolynomialDetermination

namespace Polynomial

variable {R : Type*} [CommRing R] [IsDomain R] {f g : R[X]}

section Finset

open Function Fintype
open scoped Finset

variable (s : Finset R)

theorem eq_zero_of_degree_lt_of_eval_finset_eq_zero (degree_f_lt : f.degree < #s)
    (eval_f : ∀ x ∈ s, f.eval x = 0) : f = 0 := by
  rw [← mem_degreeLT] at degree_f_lt
  simp_rw [eval_eq_sum_degreeLTEquiv degree_f_lt] at eval_f
  rw [← degreeLTEquiv_eq_zero_iff_eq_zero degree_f_lt]
  exact
    Matrix.eq_zero_of_forall_index_sum_mul_pow_eq_zero
      (Injective.comp (Embedding.subtype _).inj' (equivFinOfCardEq (card_coe _)).symm.injective)
      fun _ => eval_f _ (Finset.coe_mem _)

theorem eq_of_degree_sub_lt_of_eval_finset_eq (degree_fg_lt : (f - g).degree < #s)
    (eval_fg : ∀ x ∈ s, f.eval x = g.eval x) : f = g := by
  rw [← sub_eq_zero]
  refine eq_zero_of_degree_lt_of_eval_finset_eq_zero _ degree_fg_lt ?_
  simp_rw [eval_sub, sub_eq_zero]
  exact eval_fg

theorem eq_of_degrees_lt_of_eval_finset_eq (degree_f_lt : f.degree < #s)
    (degree_g_lt : g.degree < #s) (eval_fg : ∀ x ∈ s, f.eval x = g.eval x) : f = g := by
  rw [← mem_degreeLT] at degree_f_lt degree_g_lt
  refine eq_of_degree_sub_lt_of_eval_finset_eq _ ?_ eval_fg
  rw [← mem_degreeLT]; exact Submodule.sub_mem _ degree_f_lt degree_g_lt

/--
Two polynomials, with the same degree and leading coefficient, which have the same evaluation
on a set of distinct values with cardinality equal to the degree, are equal.
-/
theorem eq_of_degree_le_of_eval_finset_eq
    (h_deg_le : f.degree ≤ #s)
    (h_deg_eq : f.degree = g.degree)
    (hlc : f.leadingCoeff = g.leadingCoeff)
    (h_eval : ∀ x ∈ s, f.eval x = g.eval x) :
    f = g := by
  rcases eq_or_ne f 0 with rfl | hf
  · rwa [degree_zero, eq_comm, degree_eq_bot, eq_comm] at h_deg_eq
  · exact eq_of_degree_sub_lt_of_eval_finset_eq s
      (lt_of_lt_of_le (degree_sub_lt_left h_deg_eq hf hlc) h_deg_le) h_eval

end Finset

section Indexed

open Finset

variable {ι : Type*} {v : ι → R} (s : Finset ι)

theorem eq_zero_of_degree_lt_of_eval_index_eq_zero (hvs : Set.InjOn v s)
    (degree_f_lt : f.degree < #s) (eval_f : ∀ i ∈ s, f.eval (v i) = 0) : f = 0 := by
  classical
    rw [← card_image_of_injOn hvs] at degree_f_lt
    refine eq_zero_of_degree_lt_of_eval_finset_eq_zero _ degree_f_lt ?_
    intro x hx
    rcases mem_image.mp hx with ⟨_, hj, rfl⟩
    exact eval_f _ hj

theorem eq_of_degree_sub_lt_of_eval_index_eq (hvs : Set.InjOn v s)
    (degree_fg_lt : (f - g).degree < #s) (eval_fg : ∀ i ∈ s, f.eval (v i) = g.eval (v i)) :
    f = g := by
  rw [← sub_eq_zero]
  refine eq_zero_of_degree_lt_of_eval_index_eq_zero _ hvs degree_fg_lt ?_
  simp_rw [eval_sub, sub_eq_zero]
  exact eval_fg

theorem eq_of_degrees_lt_of_eval_index_eq (hvs : Set.InjOn v s) (degree_f_lt : f.degree < #s)
    (degree_g_lt : g.degree < #s) (eval_fg : ∀ i ∈ s, f.eval (v i) = g.eval (v i)) : f = g := by
  refine eq_of_degree_sub_lt_of_eval_index_eq _ hvs ?_ eval_fg
  rw [← mem_degreeLT] at degree_f_lt degree_g_lt ⊢
  exact Submodule.sub_mem _ degree_f_lt degree_g_lt

theorem eq_of_degree_le_of_eval_index_eq (hvs : Set.InjOn v s)
    (h_deg_le : f.degree ≤ #s)
    (h_deg_eq : f.degree = g.degree)
    (hlc : f.leadingCoeff = g.leadingCoeff)
    (h_eval : ∀ i ∈ s, f.eval (v i) = g.eval (v i)) : f = g := by
  rcases eq_or_ne f 0 with rfl | hf
  · rwa [degree_zero, eq_comm, degree_eq_bot, eq_comm] at h_deg_eq
  · exact eq_of_degree_sub_lt_of_eval_index_eq s hvs
      (lt_of_lt_of_le (degree_sub_lt_left h_deg_eq hf hlc) h_deg_le)
      h_eval

end Indexed

end Polynomial

end PolynomialDetermination

noncomputable section

namespace Lagrange

open Polynomial

section BasisDivisor
variable {F : Type*} [Field F]
variable {x y : F}

/-- `basisDivisor x y hxy`, for distinct `x` and `y`, is the unique polynomial of degree at most
one that evaluates to `1` at `x` and to `0` at `y`, namely `(X - y) / (x - y)`. Such polynomials
are the building blocks for the Lagrange interpolants. -/
def basisDivisor (x y : F) (hxy : x ≠ y) : F[X] :=
  C (Checked.inv (x - y) (sub_ne_zero_of_ne hxy).isUnit) * (X - C y)

theorem basisDivisor_ne_zero {hxy : x ≠ y} : basisDivisor x y hxy ≠ 0 :=
  mul_ne_zero (C_ne_zero.2 inv_ne_zero) (X_sub_C_ne_zero y)

theorem degree_basisDivisor_of_ne {hxy : x ≠ y} : (basisDivisor x y hxy).degree = 1 := by
  rw [basisDivisor, degree_mul, degree_X_sub_C, degree_C inv_ne_zero, zero_add]

theorem natDegree_basisDivisor_of_ne {hxy : x ≠ y} : (basisDivisor x y hxy).natDegree = 1 :=
  natDegree_eq_of_degree_eq_some degree_basisDivisor_of_ne

@[simp]
theorem eval_basisDivisor_right {hxy : x ≠ y} : eval y (basisDivisor x y hxy) = 0 := by
  simp only [basisDivisor, eval_mul, eval_C, eval_sub, eval_X, sub_self, mul_zero]

@[simp]
theorem eval_basisDivisor_left_of_ne {hxy : x ≠ y} : eval x (basisDivisor x y hxy) = 1 := by
  simp only [basisDivisor, eval_mul, eval_C, eval_sub, eval_X]
  exact inv_mul_cancel₀

end BasisDivisor

section Basis

variable {F : Type*} [Field F] {ι : Type*} [DecidableEq ι]
variable {s : Finset ι} {v : ι → F} {i j : ι}

open Finset

/-- If no other index of `s` has the node `v i`, the product of the differences between `v i` and
the nodes of the other indices of `s` is invertible. It is the denominator of the Lagrange basis
polynomial `Lagrange.basis s v i` and of the nodal weight `Lagrange.nodalWeight s v i`. -/
theorem isUnit_prod_sub (hvi : ∀ ⦃j⦄, j ∈ s → v i = v j → i = j) :
    IsUnit (∏ j ∈ s.erase i, (v i - v j)) :=
  IsUnit.prod_iff.2 fun _ hj =>
    (sub_ne_zero_of_ne fun h => ne_of_mem_erase hj (hvi (mem_of_mem_erase hj) h).symm).isUnit

/-- The Lagrange basis polynomial `∏ j ∈ s.erase i, (X - v j) / (v i - v j)` of the index `i` for
the nodes `v j`, `j ∈ s`. It is defined when no other index of `s` has the node `v i` (`hvi`),
which makes its denominator `∏ j ∈ s.erase i, (v i - v j)` invertible; when `v` is injective on
`s` and `hi : i ∈ s`, `hvs hi` is such evidence. It evaluates to `1` at `v i` and to `0` at `v j`
for the other indices `j ∈ s`. -/
protected def basis (s : Finset ι) (v : ι → F) (i : ι)
    (hvi : ∀ ⦃j⦄, j ∈ s → v i = v j → i = j) : F[X] :=
  C (Checked.inv (∏ j ∈ s.erase i, (v i - v j)) (isUnit_prod_sub hvi)) *
    ∏ j ∈ s.erase i, (X - C (v j))

@[simp]
theorem basis_empty {hvi : ∀ ⦃j⦄, j ∈ (∅ : Finset ι) → v i = v j → i = j} :
    Lagrange.basis ∅ v i hvi = 1 := by
  simp only [Lagrange.basis, erase_empty, prod_empty, inv_one₀, map_one, one_mul]

@[simp]
theorem basis_singleton (i : ι) {hvi : ∀ ⦃j⦄, j ∈ ({i} : Finset ι) → v i = v j → i = j} :
    Lagrange.basis {i} v i hvi = 1 := by
  simp only [Lagrange.basis, erase_singleton, prod_empty, inv_one₀, map_one, one_mul]

@[simp]
theorem basis_pair_left {hvi : ∀ ⦃k⦄, k ∈ ({i, j} : Finset ι) → v i = v k → i = k}
    (hij : i ≠ j) :
    Lagrange.basis {i, j} v i hvi =
      basisDivisor (v i) (v j) fun h => hij (hvi (mem_insert_of_mem (mem_singleton_self j)) h) := by
  simp only [Lagrange.basis, basisDivisor, erase_insert_eq_erase,
    erase_eq_of_notMem (notMem_singleton.2 hij), prod_singleton]

@[simp]
theorem basis_pair_right {hvj : ∀ ⦃k⦄, k ∈ ({i, j} : Finset ι) → v j = v k → j = k}
    (hij : i ≠ j) :
    Lagrange.basis {i, j} v j hvj =
      basisDivisor (v j) (v i) fun h => hij (hvj (mem_insert_self i {j}) h).symm := by
  simp only [Lagrange.basis, basisDivisor, erase_insert_of_ne hij, erase_singleton, insert_empty,
    prod_singleton]

theorem basis_ne_zero {hvi : ∀ ⦃j⦄, j ∈ s → v i = v j → i = j} : Lagrange.basis s v i hvi ≠ 0 :=
  mul_ne_zero (C_ne_zero.2 inv_ne_zero) (monic_prod_X_sub_C v (s.erase i)).ne_zero

@[simp]
theorem eval_basis_self {hvi : ∀ ⦃j⦄, j ∈ s → v i = v j → i = j} :
    (Lagrange.basis s v i hvi).eval (v i) = 1 := by
  simp only [Lagrange.basis, eval_mul, eval_C, eval_prod, eval_sub, eval_X]
  exact inv_mul_cancel₀

@[simp]
theorem eval_basis_of_ne {hvi : ∀ ⦃k⦄, k ∈ s → v i = v k → i = k} (hij : i ≠ j) (hj : j ∈ s) :
    (Lagrange.basis s v i hvi).eval (v j) = 0 := by
  rw [Lagrange.basis, eval_mul, eval_prod]
  refine mul_eq_zero_of_right _ (prod_eq_zero (mem_erase.2 ⟨hij.symm, hj⟩) ?_)
  rw [eval_sub, eval_X, eval_C, sub_self]

@[simp]
theorem natDegree_basis {hvi : ∀ ⦃j⦄, j ∈ s → v i = v j → i = j} (hi : i ∈ s) :
    (Lagrange.basis s v i hvi).natDegree = #s - 1 := by
  rw [Lagrange.basis, natDegree_C_mul inv_ne_zero,
    natDegree_prod_of_monic (h := fun j _ => monic_X_sub_C (v j))]
  simp only [natDegree_X_sub_C, sum_const, smul_eq_mul, mul_one, card_erase_of_mem hi]

theorem degree_basis {hvi : ∀ ⦃j⦄, j ∈ s → v i = v j → i = j} (hi : i ∈ s) :
    (Lagrange.basis s v i hvi).degree = ↑(#s - 1) := by
  rw [degree_eq_natDegree basis_ne_zero, natDegree_basis hi]

theorem sum_basis (hvs : Set.InjOn v s) (hs : s.Nonempty) :
    ∑ j : s, Lagrange.basis s v j (hvs j.2) = 1 := by
  refine eq_of_degrees_lt_of_eval_index_eq s hvs (lt_of_le_of_lt (degree_sum_le _ _) ?_) ?_ ?_
  · rw [Nat.cast_withBot, Finset.sup_lt_iff (WithBot.bot_lt_coe #s)]
    intro i _
    rw [degree_basis i.2, Nat.cast_withBot, WithBot.coe_lt_coe]
    exact Nat.pred_lt (card_ne_zero_of_mem i.2)
  · rw [degree_one, ← WithBot.coe_zero, Nat.cast_withBot, WithBot.coe_lt_coe]
    exact Nonempty.card_pos hs
  · intro i hi
    rw [eval_finsetSum, eval_one, ← add_sum_erase _ _ (mem_univ (⟨i, hi⟩ : s)), eval_basis_self,
      add_eq_left]
    exact sum_eq_zero fun j hj => eval_basis_of_ne (fun h => ne_of_mem_erase hj (Subtype.ext h)) hi

theorem basisDivisor_add_symm {x y : F} {hxy : x ≠ y} :
    basisDivisor x y hxy + basisDivisor y x hxy.symm = 1 := by
  have hxy' : x - y ≠ 0 := sub_ne_zero_of_ne hxy
  have hyx' : y - x ≠ 0 := sub_ne_zero_of_ne hxy.symm
  have hinv : (y - x)⁻¹ = -(x - y)⁻¹ := by
    apply inv_eq_of_mul_eq_one_right₀
    rw [mul_neg, ← neg_mul, neg_sub, mul_inv_cancel₀]
  have h : C (x - y)⁻¹ * (C x - C y) = 1 := by
    rw [← C_sub, ← C_mul, inv_mul_cancel₀, C_1]
  simp only [basisDivisor]
  rw [hinv, map_neg, ← h]
  ring

theorem leadingCoeff_basis {hvi : ∀ ⦃j⦄, j ∈ s → v i = v j → i = j} :
    (Lagrange.basis s v i hvi).leadingCoeff =
      Checked.inv (∏ j ∈ s.erase i, (v i - v j)) (isUnit_prod_sub hvi) := by
  rw [Lagrange.basis, leadingCoeff_mul, leadingCoeff_C, (monic_prod_X_sub_C v _).leadingCoeff,
    mul_one]

end Basis

section Interpolate

variable {F : Type*} [Field F] {ι : Type*} [DecidableEq ι]
variable {s t : Finset ι} {i j : ι} {v : ι → F} (r r' : ι → F)

open Finset

/-- Lagrange interpolation: given a finset `s : Finset ι`, a nodal map `v : ι → F` injective on
`s` (`hvs`) and a value function `r : ι → F`, `interpolate s v hvs r` is the unique
polynomial of degree `< #s` that takes value `r i` on `v i` for all `i` in `s`. The injectivity
of `v` on `s` is the domain of the Lagrange basis polynomials of the indices of `s`. -/
@[simps]
def interpolate (s : Finset ι) (v : ι → F) (hvs : Set.InjOn v s) : (ι → F) →ₗ[F] F[X] where
  toFun r := ∑ i : s, C (r i) * Lagrange.basis s v i (hvs i.2)
  map_add' f g := by
    simp only [Pi.add_apply, C_add, add_mul, Finset.sum_add_distrib]
  map_smul' c f := by
    simp_rw [Finset.smul_sum, C_mul', smul_smul, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]

theorem interpolate_empty {hvs : Set.InjOn v (∅ : Finset ι)} : interpolate ∅ v hvs r = 0 := by
  rw [interpolate_apply]
  exact Fintype.sum_empty _

theorem interpolate_singleton {hvs : Set.InjOn v ({i} : Finset ι)} :
    interpolate {i} v hvs r = C (r i) := by
  rw [interpolate_apply, Fintype.sum_eq_single ⟨i, mem_singleton_self i⟩ fun j hj =>
    absurd (Subtype.ext (mem_singleton.1 j.2)) hj, basis_singleton, mul_one]

theorem interpolate_one {hvs : Set.InjOn v s} (hs : s.Nonempty) : interpolate s v hvs 1 = 1 := by
  simp_rw [interpolate_apply, Pi.one_apply, map_one, one_mul]
  exact sum_basis hvs hs

theorem eval_interpolate_at_node {hvs : Set.InjOn v s} (hi : i ∈ s) :
    eval (v i) (interpolate s v hvs r) = r i := by
  rw [interpolate_apply, eval_finsetSum, ← add_sum_erase _ _ (mem_univ (⟨i, hi⟩ : s))]
  simp_rw [eval_mul, eval_C, eval_basis_self, mul_one, add_eq_left]
  refine sum_eq_zero fun j H => ?_
  rw [eval_basis_of_ne (fun h => ne_of_mem_erase H (Subtype.ext h)) hi, mul_zero]

theorem degree_interpolate_le {hvs : Set.InjOn v s} :
    (interpolate s v hvs r).degree ≤ ↑(#s - 1) := by
  refine (degree_sum_le _ _).trans ?_
  rw [Finset.sup_le_iff]
  intro i _
  rw [degree_mul, degree_basis i.2]
  by_cases hr : r i = 0
  · simpa only [hr, map_zero, degree_zero, WithBot.bot_add] using bot_le
  · rw [degree_C hr, zero_add]

theorem degree_interpolate_lt {hvs : Set.InjOn v s} : (interpolate s v hvs r).degree < #s := by
  rw [Nat.cast_withBot]
  rcases eq_empty_or_nonempty s with (rfl | h)
  · rw [interpolate_empty, degree_zero, card_empty]
    exact WithBot.bot_lt_coe _
  · refine lt_of_le_of_lt (degree_interpolate_le _) ?_
    rw [Nat.cast_withBot, WithBot.coe_lt_coe]
    exact Nat.sub_lt (Nonempty.card_pos h) zero_lt_one

theorem degree_interpolate_erase_lt {hvs : Set.InjOn v (s.erase i)} (hi : i ∈ s) :
    (interpolate (s.erase i) v hvs r).degree < ↑(#s - 1) := by
  rw [← Finset.card_erase_of_mem hi]
  exact degree_interpolate_lt _

theorem values_eq_on_of_interpolate_eq {hvs : Set.InjOn v s}
    (hrr' : interpolate s v hvs r = interpolate s v hvs r') : ∀ i ∈ s, r i = r' i := fun _ hi => by
  rw [← eval_interpolate_at_node (hvs := hvs) r hi, hrr', eval_interpolate_at_node r' hi]

theorem interpolate_eq_of_values_eq_on {hvs : Set.InjOn v s} (hrr' : ∀ i ∈ s, r i = r' i) :
    interpolate s v hvs r = interpolate s v hvs r' :=
  sum_congr rfl fun i _ => by rw [hrr' _ i.2]

theorem interpolate_eq_iff_values_eq_on {hvs : Set.InjOn v s} :
    interpolate s v hvs r = interpolate s v hvs r' ↔ ∀ i ∈ s, r i = r' i :=
  ⟨values_eq_on_of_interpolate_eq _ _, interpolate_eq_of_values_eq_on _ _⟩

theorem eq_interpolate {f : F[X]} (hvs : Set.InjOn v s) (degree_f_lt : f.degree < #s) :
    f = interpolate s v hvs fun i => f.eval (v i) :=
  eq_of_degrees_lt_of_eval_index_eq _ hvs degree_f_lt (degree_interpolate_lt _) fun _ hi =>
    (eval_interpolate_at_node (fun x ↦ eval (v x) f) hi).symm

theorem eq_interpolate_of_eval_eq {f : F[X]} (hvs : Set.InjOn v s) (degree_f_lt : f.degree < #s)
    (eval_f : ∀ i ∈ s, f.eval (v i) = r i) : f = interpolate s v hvs r := by
  rw [eq_interpolate hvs degree_f_lt]
  exact interpolate_eq_of_values_eq_on _ _ eval_f

/-- This is the characteristic property of the interpolation: the interpolation is the
unique polynomial of `degree < Fintype.card ι` which takes the value of the `r i` on the `v i`.
-/
theorem eq_interpolate_iff {f : F[X]} (hvs : Set.InjOn v s) :
    (f.degree < #s ∧ ∀ i ∈ s, eval (v i) f = r i) ↔ f = interpolate s v hvs r := by
  constructor <;> intro h
  · exact eq_interpolate_of_eval_eq _ hvs h.1 h.2
  · rw [h]
    exact ⟨degree_interpolate_lt _, fun _ hi => eval_interpolate_at_node _ hi⟩

/-- Lagrange interpolation induces isomorphism between functions from `s`
and polynomials of degree less than `Fintype.card ι`. -/
def funEquivDegreeLT (hvs : Set.InjOn v s) : degreeLT F #s ≃ₗ[F] s → F where
  toFun f i := f.1.eval (v i)
  map_add' _ _ := funext fun _ => eval_add
  map_smul' c f := funext <| by simp
  invFun r :=
    ⟨interpolate s v hvs fun x => if hx : x ∈ s then r ⟨x, hx⟩ else 0,
      mem_degreeLT.2 <| degree_interpolate_lt _⟩
  left_inv := by
    rintro ⟨f, hf⟩
    simp only [Subtype.mk_eq_mk, dite_eq_ite]
    rw [mem_degreeLT] at hf
    conv => rhs; rw [eq_interpolate hvs hf]
    exact interpolate_eq_of_values_eq_on _ _ fun _ hi => ite_eq_left hi
  right_inv := by
    intro f
    ext ⟨i, hi⟩
    simp only [eval_interpolate_at_node _ hi]
    exact dite_eq_left hi

theorem interpolate_eq_sum_interpolate_insert_sdiff {hvt : Set.InjOn v t} (hs : s.Nonempty)
    (hst : s ⊆ t) :
    interpolate t v hvt r = ∑ i : s,
      interpolate (insert (i : ι) (t \ s)) v
          (hvt.mono (insert_subset_iff.2 ⟨hst i.2, sdiff_subset⟩)) r *
        Lagrange.basis s v i ((hvt.mono hst) i.2) := by
  symm
  refine eq_interpolate_of_eval_eq _ hvt (lt_of_le_of_lt (degree_sum_le _ _) ?_) fun i hi => ?_
  · simp_rw [Nat.cast_withBot, Finset.sup_lt_iff (WithBot.bot_lt_coe #t), degree_mul]
    intro i _
    have hs : 1 ≤ #s := Nonempty.card_pos ⟨_, i.2⟩
    have hst' : #s ≤ #t := card_le_card hst
    have H : #t = 1 + (#t - #s) + (#s - 1) := by
      rw [add_assoc, tsub_add_tsub_cancel hst' hs, ← add_tsub_assoc_of_le (hs.trans hst'),
        Nat.succ_add_sub_one, zero_add]
    rw [degree_basis i.2, H, WithBot.coe_add, Nat.cast_withBot,
      WithBot.add_lt_add_iff_right (@WithBot.coe_ne_bot _ (#s - 1))]
    convert! degree_interpolate_lt _
    rw [card_insert_of_notMem (notMem_sdiff_of_mem_right i.2), card_sdiff_of_subset hst, add_comm]
  · simp_rw [eval_finsetSum, eval_mul]
    by_cases hi' : i ∈ s
    · rw [← add_sum_erase _ _ (mem_univ (⟨i, hi'⟩ : s))]
      simp_rw [eval_basis_self, mul_one]
      rw [eval_interpolate_at_node _ (mem_insert_self _ _), add_eq_left]
      refine sum_eq_zero fun j hj => ?_
      rw [eval_basis_of_ne (fun h => ne_of_mem_erase hj (Subtype.ext h)) hi', mul_zero]
    · have H : (∑ j : s, eval (v i) (Lagrange.basis s v j ((hvt.mono hst) j.2))) = 1 := by
        rw [← eval_finsetSum, sum_basis (hvt.mono hst) hs, eval_one]
      rw [← mul_one (r i), ← H, mul_sum]
      refine sum_congr rfl fun j _ => ?_
      congr
      exact eval_interpolate_at_node _ (mem_insert.mpr (Or.inr (mem_sdiff.mpr ⟨hi, hi'⟩)))

theorem interpolate_eq_add_interpolate_erase {hvs : Set.InjOn v s} (hi : i ∈ s) (hj : j ∈ s)
    (hij : i ≠ j) :
    interpolate s v hvs r =
      interpolate (s.erase j) v (hvs.mono (erase_subset j s)) r *
          basisDivisor (v i) (v j) ((hvs.ne_iff hi hj).2 hij) +
        interpolate (s.erase i) v (hvs.mono (erase_subset i s)) r *
          basisDivisor (v j) (v i) ((hvs.ne_iff hj hi).2 hij.symm) := by
  have hsub : ({i, j} : Finset ι) ⊆ s := insert_subset_iff.mpr ⟨hi, singleton_subset_iff.mpr hj⟩
  have hi' : insert i (s \ {i, j}) = s.erase j := by
    rw [sdiff_insert_insert_of_mem_of_notMem hi (notMem_singleton.mpr hij),
      sdiff_singleton_eq_erase]
  have hj' : insert j (s \ {i, j}) = s.erase i := by
    rw [pair_comm, sdiff_insert_insert_of_mem_of_notMem hj (notMem_singleton.mpr hij.symm),
      sdiff_singleton_eq_erase]
  rw [interpolate_eq_sum_interpolate_insert_sdiff _ ⟨i, mem_insert_self i {j}⟩ hsub,
    Fintype.sum_eq_add ⟨i, mem_insert_self i {j}⟩ ⟨j, mem_insert_of_mem (mem_singleton_self j)⟩
      (fun h => hij (congrArg Subtype.val h)) ?_]
  · simp only [basis_pair_left hij, basis_pair_right hij, hi', hj']
  · rintro ⟨k, hk⟩ ⟨hki, hkj⟩
    rcases mem_insert.mp hk with rfl | hk
    · exact absurd rfl hki
    · rw [mem_singleton] at hk
      subst hk
      exact absurd rfl hkj

theorem interpolate_eq_sum {hvs : Set.InjOn v s} : interpolate s v hvs r =
    ∑ i : s, C (Checked.div (r i) (∏ j ∈ s.erase i, (v i - v j)) (isUnit_prod_sub (hvs i.2))) *
      ∏ j ∈ s.erase i, (X - C (v j)) := by
  simp only [interpolate_apply, Lagrange.basis, div_eq_mul_inv₀, map_mul, mul_assoc]

theorem iterate_derivative_interpolate {hvs : Set.InjOn v s} {k : ℕ} (hk : k < #s) :
    derivative^[k] (interpolate s v hvs r) =
      k.factorial * ∑ i : s,
        C (Checked.div (r i) (∏ j ∈ s.erase i, (v i - v j)) (isUnit_prod_sub (hvs i.2))) *
          ∑ t ∈ (s.erase i).powersetCard (#s - (k + 1)), ∏ a ∈ t, (X - C (v a)) := by
  classical
  simp_rw [interpolate_eq_sum, iterate_derivative_sum, iterate_derivative_C_mul,
    mul_sum (univ : Finset s), ← mul_assoc, mul_comm (k.factorial : F[X]), mul_assoc]
  congr! 2 with i hi
  have hi' := i.2
  have hvs' := hvs.mono (coe_subset.mpr (erase_subset (i : ι) s))
  calc
    derivative^[k] (∏ j ∈ s.erase i, (X - C (v j))) =
    derivative^[k] (∏ vj ∈ (s.erase i).image v, (X - C vj)) := by rw [Finset.prod_image hvs']
    _ = k.factorial * ∑ t ∈ ((s.erase i).image v).powersetCard (#s - (k + 1)),
          ∏ va ∈ t, (X - C va) := by
        grind [iterate_derivative_prod_X_sub_C]
    _ = k.factorial * ∑ t ∈ (s.erase i).powersetCard (#s - (k + 1)), ∏ a ∈ t, (X - C (v a)) := by
        rw [powersetCard_eq_filter, powerset_image, eq_comm]
        congrm k.factorial * ?_
        refine sum_nbij (·.image v) (fun a ha ↦ ?hi) ?i_inj (fun t ht ↦ ?i_surj) fun a ha ↦ ?h
        case hi => grind [card_image_of_injOn, hvs'.mono]
        case i_inj => exact (image_injOn_powerset_of_injOn hvs').mono (by grind)
        case i_surj => grind [card_image_of_injOn, hvs'.mono]
        case h => exact eq_comm.mp <| prod_image <| by grind [hvs'.mono]

theorem eval_iterate_derivative_eq_sum (hvs : Set.InjOn v s) {P : Polynomial F} (hP : P.degree < #s)
    {k : ℕ} (hk : k < #s) (x : F) :
    (derivative^[k] P).eval x =
      k.factorial * ∑ i : s,
        Checked.div (P.eval (v i)) (∏ j ∈ s.erase i, (v i - v j)) (isUnit_prod_sub (hvs i.2)) *
          ∑ t ∈ (s.erase i).powersetCard (#s - (k + 1)), ∏ a ∈ t, (x - v a) := by
  nth_rewrite 1 [eq_interpolate hvs hP, iterate_derivative_interpolate _ hk]
  simp [eval_finsetSum, eval_prod]

theorem coeff_eq_sum
    (hvs : Set.InjOn v s) {P : Polynomial F} (hP : P.degree < #s) :
    P.coeff (#s - 1) = ∑ i : s,
      Checked.div (P.eval (v i)) (∏ j ∈ s.erase i, (v i - v j)) (isUnit_prod_sub (hvs i.2)) := by
  nth_rewrite 1 [eq_interpolate hvs hP, interpolate_apply, finsetSum_coeff]
  congr! with i hi
  rw [coeff_C_mul, ← natDegree_basis (hvi := hvs i.2) i.2, ← leadingCoeff, leadingCoeff_basis]
  rfl

theorem leadingCoeff_eq_sum
    (hvs : Set.InjOn v s) {P : Polynomial F} (hP : #s = P.degree + 1) :
    P.leadingCoeff = ∑ i : s,
      Checked.div (P.eval (v i)) (∏ j ∈ s.erase i, (v i - v j)) (isUnit_prod_sub (hvs i.2)) := by
  lift P.degree to ℕ using (by contrapose! hP; simp [hP]) with deg hdeg
  rw [← WithBot.coe_one, ← WithBot.coe_add] at hP
  replace hP : #s = deg + 1 := WithBot.coe_eq_coe.mp hP
  have hdegree : P.degree = ↑(#s - 1) := hdeg.symm.trans (WithBot.coe_eq_coe.mpr (by grind))
  rw [leadingCoeff, natDegree_eq_of_degree_eq_some hdegree]
  exact coeff_eq_sum hvs (by rw [hdegree]; norm_cast; lia)

lemma _root_.Polynomial.exists_eval_eq_iff {ι : Type*} [Finite ι] (x y : ι → F) :
    (∃ q : F[X], ∀ i, q.eval (x i) = y i) ↔ ∀ i j, x i = x j → y i = y j := by
  refine ⟨fun ⟨q, hq⟩ i j hij ↦ by rw [← hq, ← hq, hij], fun hwd ↦ ?_⟩
  classical
  have : Fintype ι := Fintype.ofFinite ι
  have hinj : Set.InjOn (fun d : F ↦ d) (Finset.univ.image x) := Function.injective_id.injOn
  set v : F → F := fun z ↦ if h : ∃ i, x i = z then y h.choose else 0 with v_def
  refine ⟨Lagrange.interpolate (Finset.univ.image x) (fun d : F ↦ d) hinj v, fun i ↦ ?_⟩
  have hi : x i ∈ Finset.univ.image x := Finset.mem_image_of_mem x (Finset.mem_univ i)
  rw [Lagrange.eval_interpolate_at_node (v := fun d : F ↦ d) _ hi, v_def]
  simp only
  split_ifs with h
  · exact hwd _ _ h.choose_spec
  · aesop

end Interpolate

section Nodal

variable {R : Type*} [CommRing R] {ι : Type*}
variable {s : Finset ι} {v : ι → R}

open Finset Polynomial

/-- `nodal s v` is the unique monic polynomial whose roots are the nodes defined by `v` and `s`.

That is, the roots of `nodal s v` are exactly the image of `v` on `s`,
with appropriate multiplicity.

We can use `nodal` to define the barycentric forms of the evaluated interpolant.
-/
def nodal (s : Finset ι) (v : ι → R) : R[X] :=
  ∏ i ∈ s, (X - C (v i))

theorem nodal_eq (s : Finset ι) (v : ι → R) : nodal s v = ∏ i ∈ s, (X - C (v i)) :=
  rfl

@[simp]
theorem nodal_empty : nodal ∅ v = 1 := by
  rfl

@[simp]
theorem natDegree_nodal [Nontrivial R] : (nodal s v).natDegree = #s := by
  simp_rw [nodal, natDegree_prod_of_monic (h := fun i _ => monic_X_sub_C (v i)),
    natDegree_X_sub_C, sum_const, smul_eq_mul, mul_one]

theorem nodal_ne_zero [Nontrivial R] : nodal s v ≠ 0 := by
  rcases s.eq_empty_or_nonempty with (rfl | h)
  · exact one_ne_zero
  · apply ne_zero_of_natDegree_gt (n := 0)
    simp only [natDegree_nodal, h.card_pos]

@[simp]
theorem degree_nodal [Nontrivial R] : (nodal s v).degree = #s := by
  simp_rw [degree_eq_natDegree nodal_ne_zero, natDegree_nodal]

theorem nodal_monic : (nodal s v).Monic :=
  monic_prod_of_monic s (fun i ↦ X - C (v i)) fun i _ ↦ monic_X_sub_C (v i)

theorem eval_nodal {x : R} : (nodal s v).eval x = ∏ i ∈ s, (x - v i) := by
  simp_rw [nodal, eval_prod, eval_sub, eval_X, eval_C]

theorem eval_nodal_at_node {i : ι} (hi : i ∈ s) : eval (v i) (nodal s v) = 0 := by
  rw [eval_nodal]
  exact s.prod_eq_zero hi (sub_self (v i))

theorem eval_nodal_not_at_node [Nontrivial R] [NoZeroDivisors R] {x : R}
    (hx : ∀ i ∈ s, x ≠ v i) : eval x (nodal s v) ≠ 0 := by
  simp_rw [nodal, eval_prod, prod_ne_zero_iff, eval_sub, eval_X, eval_C, sub_ne_zero]
  exact hx

theorem nodal_eq_mul_nodal_erase [DecidableEq ι] {i : ι} (hi : i ∈ s) :
    nodal s v = (X - C (v i)) * nodal (s.erase i) v := by
    simp_rw [nodal, Finset.mul_prod_erase _ (fun x => X - C (v x)) hi]

theorem X_sub_C_dvd_nodal (v : ι → R) {i : ι} (hi : i ∈ s) : X - C (v i) ∣ nodal s v := by
  classical
  exact ⟨nodal (s.erase i) v, nodal_eq_mul_nodal_erase hi⟩

theorem nodal_insert_eq_nodal [DecidableEq ι] {i : ι} (hi : i ∉ s) :
    nodal (insert i s) v = (X - C (v i)) * nodal s v := by
  simp_rw [nodal, prod_insert hi]

theorem derivative_nodal [DecidableEq ι] :
    derivative (nodal s v) = ∑ i ∈ s, nodal (s.erase i) v := by
  refine s.induction_on ?_ fun i t hit IH => ?_
  · rw [nodal_empty, derivative_one, sum_empty]
  · rw [nodal_insert_eq_nodal hit, derivative_mul, IH, derivative_sub, derivative_X, derivative_C,
      sub_zero, one_mul, sum_insert hit, mul_sum, erase_insert hit, add_right_inj]
    refine sum_congr rfl fun j hjt => ?_
    rw [t.erase_insert_of_ne (ne_of_mem_of_not_mem hjt hit).symm,
      nodal_insert_eq_nodal (mem_of_mem_erase.mt hit)]

theorem eval_nodal_derivative_eval_node_eq [DecidableEq ι] {i : ι} (hi : i ∈ s) :
    eval (v i) (derivative (nodal s v)) = eval (v i) (nodal (s.erase i) v) := by
  rw [derivative_nodal, eval_finsetSum, ← add_sum_erase _ _ hi, add_eq_left]
  exact sum_eq_zero fun j hj => (eval_nodal_at_node (mem_erase.mpr ⟨(mem_erase.mp hj).1.symm, hi⟩))

/-- The vanishing polynomial on a multiplicative subgroup is of the form X ^ n - 1. -/
@[simp] theorem nodal_subgroup_eq_X_pow_card_sub_one [IsDomain R]
    (G : Subgroup Rˣ) [Fintype G] :
    nodal (G : Set Rˣ).toFinset ((↑) : Rˣ → R) = X ^ (Fintype.card G) - 1 := by
  have h : degree (1 : R[X]) < degree ((X : R[X]) ^ Fintype.card G) := by simp [Fintype.card_pos]
  apply eq_of_degree_le_of_eval_index_eq (v := ((↑) : Rˣ → R)) (G : Set Rˣ).toFinset
  · exact Units.val_injective.injOn
  · simp
  · rw [degree_sub_eq_left_of_degree_lt h, degree_nodal, Set.toFinset_card, degree_pow, degree_X,
      nsmul_eq_mul, mul_one, Nat.cast_inj]
    exact rfl
  · rw [nodal_monic, leadingCoeff_sub_of_degree_lt h, monic_X_pow]
  · intro i hi
    rw [eval_nodal_at_node hi]
    replace hi : i ∈ G := by simpa using hi
    obtain ⟨g, rfl⟩ : ∃ g : G, g.val = i := ⟨⟨i, hi⟩, rfl⟩
    simp [← Units.val_pow_eq_pow_val, ← Subgroup.coe_pow G]

end Nodal

section NodalWeight

variable {F : Type*} [Field F] {ι : Type*} [DecidableEq ι]
variable {s : Finset ι} {v : ι → F} {i : ι}

open Finset

/-- The nodal weight `(∏ j ∈ s.erase i, (v i - v j))⁻¹` of the index `i` for the nodes `v j`,
`j ∈ s`, that is the barycentric weight of the node `v i`. It is defined when no other index of
`s` has the node `v i` (`hvi`); when `v` is injective on `s` and `hi : i ∈ s`, `hvs hi` is such
evidence. -/
def nodalWeight (s : Finset ι) (v : ι → F) (i : ι) (hvi : ∀ ⦃j⦄, j ∈ s → v i = v j → i = j) :
    F :=
  Checked.inv (∏ j ∈ s.erase i, (v i - v j)) (isUnit_prod_sub hvi)

theorem nodalWeight_eq_eval_nodal_erase_inv {hvi : ∀ ⦃j⦄, j ∈ s → v i = v j → i = j} :
    nodalWeight s v i hvi = Checked.inv (eval (v i) (nodal (s.erase i) v))
      (by rw [eval_nodal]; exact isUnit_prod_sub hvi) := by
  simp only [nodalWeight, eval_nodal]

theorem nodal_erase_eq_nodal_div (hi : i ∈ s) :
    nodal (s.erase i) v = nodal s v / (X - C (v i)) := by
  rw [nodal_eq_mul_nodal_erase hi, MulDivCancelClass.mul_div_cancel_left₀ _ (X_sub_C_ne_zero _)]

theorem nodalWeight_eq_eval_derivative_nodal {hvi : ∀ ⦃j⦄, j ∈ s → v i = v j → i = j}
    (hi : i ∈ s) :
    nodalWeight s v i hvi = Checked.inv (eval (v i) (Polynomial.derivative (nodal s v)))
      (by rw [eval_nodal_derivative_eval_node_eq hi, eval_nodal]; exact isUnit_prod_sub hvi) := by
  simp only [nodalWeight, eval_nodal_derivative_eval_node_eq hi, eval_nodal]

theorem nodalWeight_ne_zero {hvi : ∀ ⦃j⦄, j ∈ s → v i = v j → i = j} :
    nodalWeight s v i hvi ≠ 0 :=
  inv_ne_zero

end NodalWeight

section LagrangeBarycentric

variable {F : Type*} [Field F] {ι : Type*} [DecidableEq ι]
variable {s : Finset ι} {v : ι → F} (r : ι → F) {i : ι} {x : F}

open Finset

theorem basis_eq_prod_sub_inv_mul_nodal_div {hvi : ∀ ⦃j⦄, j ∈ s → v i = v j → i = j}
    (hi : i ∈ s) :
    Lagrange.basis s v i hvi = C (nodalWeight s v i hvi) * (nodal s v / (X - C (v i))) := by
  rw [← nodal_erase_eq_nodal_div hi, Lagrange.basis, nodalWeight, nodal]

theorem eval_basis_not_at_node {hvi : ∀ ⦃j⦄, j ∈ s → v i = v j → i = j} (hi : i ∈ s)
    (hxi : x ≠ v i) :
    eval x (Lagrange.basis s v i hvi) = eval x (nodal s v) *
      (nodalWeight s v i hvi * Checked.inv (x - v i) (sub_ne_zero_of_ne hxi).isUnit) := by
  have hxi' : x - v i ≠ 0 := sub_ne_zero_of_ne hxi
  rw [mul_comm, basis_eq_prod_sub_inv_mul_nodal_div hi, eval_mul, eval_C, ←
    nodal_erase_eq_nodal_div hi, eval_nodal, eval_nodal, mul_assoc, ← mul_prod_erase _ _ hi, ←
    mul_assoc (x - v i)⁻¹, inv_mul_cancel₀, one_mul]

theorem interpolate_eq_nodalWeight_mul_nodal_div_X_sub_C {hvs : Set.InjOn v s} :
    interpolate s v hvs r =
      ∑ i : s, C (nodalWeight s v i (hvs i.2)) * (nodal s v / (X - C (v i))) * C (r i) :=
  sum_congr rfl fun j _ => by rw [mul_comm, basis_eq_prod_sub_inv_mul_nodal_div j.2]

/-- This is the first barycentric form of the Lagrange interpolant. -/
theorem eval_interpolate_not_at_node {hvs : Set.InjOn v s} (hx : ∀ i ∈ s, x ≠ v i) :
    eval x (interpolate s v hvs r) =
      eval x (nodal s v) * ∑ i : s, nodalWeight s v i (hvs i.2) *
        Checked.inv (x - v i) (sub_ne_zero_of_ne (hx i i.2)).isUnit * r i := by
  simp_rw [interpolate_apply, mul_sum, eval_finsetSum, eval_mul, eval_C]
  refine sum_congr rfl fun i _ => ?_
  rw [← mul_assoc, mul_comm, eval_basis_not_at_node i.2 (hx _ i.2)]

theorem sum_nodalWeight_mul_inv_sub_ne_zero (hvs : Set.InjOn v s) (hx : ∀ i ∈ s, x ≠ v i)
    (hs : s.Nonempty) :
    (∑ i : s, nodalWeight s v i (hvs i.2) *
      Checked.inv (x - v i) (sub_ne_zero_of_ne (hx i i.2)).isUnit) ≠ 0 :=
  @right_ne_zero_of_mul_eq_one _ _ _ (eval x (nodal s v)) _ <| by
    simpa only [Pi.one_apply, interpolate_one hs, eval_one, mul_one] using
      (eval_interpolate_not_at_node (hvs := hvs) 1 hx).symm

/-- This is the second barycentric form of the Lagrange interpolant. -/
theorem eval_interpolate_not_at_node' {hvs : Set.InjOn v s} (hs : s.Nonempty)
    (hx : ∀ i ∈ s, x ≠ v i) :
    eval x (interpolate s v hvs r) =
      Checked.div
        (∑ i : s, nodalWeight s v i (hvs i.2) *
          Checked.inv (x - v i) (sub_ne_zero_of_ne (hx i i.2)).isUnit * r i)
        (∑ i : s, nodalWeight s v i (hvs i.2) *
          Checked.inv (x - v i) (sub_ne_zero_of_ne (hx i i.2)).isUnit)
        (sum_nodalWeight_mul_inv_sub_ne_zero hvs hx hs).isUnit := by
  have h1 := (eval_interpolate_not_at_node (hvs := hvs) 1 hx).symm
  simp only [Pi.one_apply, interpolate_one hs, eval_one, mul_one] at h1
  rw [eq_div_iff, eval_interpolate_not_at_node r hx, mul_right_comm, h1, one_mul]

end LagrangeBarycentric

end Lagrange
