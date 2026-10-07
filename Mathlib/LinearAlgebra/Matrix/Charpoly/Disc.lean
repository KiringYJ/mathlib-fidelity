/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.RingTheory.Polynomial.Resultant.Basic


/-!
# The discriminant of a matrix
-/

@[expose] public section

open Polynomial

namespace Matrix

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

/-- The discriminant of a matrix is the discriminant of its characteristic polynomial. Since the
characteristic polynomial is monic, this is the product of the squared differences of the
eigenvalues, counted with multiplicity, in a splitting field. A `0 × 0` matrix has no eigenvalues,
and its discriminant is the empty product `1`, as is the discriminant of every matrix over the zero
ring, where `1 = 0`; these are the cases where the characteristic polynomial is constant. -/
noncomputable def discr (A : Matrix n n R) : R :=
  if h : 0 < A.charpoly.natDegree then A.charpoly.discr h else 1

@[simp]
lemma discr_conj (g : GL n R) (m : Matrix n n R) : (g.val * m * g.val⁻¹).discr = m.discr := by
  simp [discr]

@[simp]
lemma discr_conj' (g : GL n R) (m : Matrix n n R) : (g.val⁻¹ * m * g.val).discr = m.discr := by
  simp [discr]

lemma discr_of_card_eq_two (A : Matrix n n R) (hn : Fintype.card n = 2) :
    A.discr = A.trace ^ 2 - 4 * A.det := by
  nontriviality R
  have hdeg : A.charpoly.degree = 2 := by simp [charpoly_degree_eq_dim, hn]
  rw [discr, dite_eq_left (natDegree_pos_iff_degree_pos.mpr (by rw [hdeg]; norm_num)),
    Polynomial.discr_of_degree_eq_two hdeg]
  simp [A.charpoly_of_card_eq_two hn]

lemma discr_fin_two (A : Matrix (Fin 2) (Fin 2) R) :
    A.discr = A.trace ^ 2 - 4 * A.det :=
  A.discr_of_card_eq_two <| Fintype.card_fin _

end Matrix
