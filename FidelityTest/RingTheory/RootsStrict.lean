import Mathlib.Algebra.CubicDiscriminant
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.RingTheory.Polynomial.SmallDegreeVieta
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Finite root multisets take the nonvanishing of the polynomial

`p.roots hp` is the multiset of roots of a nonzero polynomial `p`, counted with multiplicity, and
`p.aroots S hp`, `p.rootSet S hp`, `nthRoots n a h`, `nthRootsFinset n a h`, and `Cubic.roots`
take the same domain; `nonzero_tac` finds the proof. Every element is a root of the zero
polynomial, so its zero locus `{x | IsRoot 0 x}` is the whole ring and there is no finite root
multiset of `0`.
-/

open Polynomial

/-! The lemmas that stated the empty value at the zero polynomial are removed. -/

/-- info: Unknown identifier `roots_zero` -/
#guard_msgs in
#check_failure roots_zero

/-- info: Unknown identifier `aroots_zero` -/
#guard_msgs in
#check_failure aroots_zero

/-- info: Unknown identifier `rootSet_zero` -/
#guard_msgs in
#check_failure rootSet_zero

/-- info: Unknown identifier `mem_roots'` -/
#guard_msgs in
#check_failure mem_roots'

/-- info: Unknown identifier `mem_aroots'` -/
#guard_msgs in
#check_failure mem_aroots'

/-- info: Unknown identifier `mem_rootSet'` -/
#guard_msgs in
#check_failure mem_rootSet'

/-- info: Unknown identifier `mem_rootSet_of_ne` -/
#guard_msgs in
#check_failure mem_rootSet_of_ne

/-- info: Unknown identifier `ne_zero_of_mem_roots` -/
#guard_msgs in
#check_failure ne_zero_of_mem_roots

/-- info: Unknown identifier `ne_zero_of_mem_rootSet` -/
#guard_msgs in
#check_failure ne_zero_of_mem_rootSet

/-- info: Unknown identifier `roots_list_prod` -/
#guard_msgs in
#check_failure roots_list_prod

/-- info: Unknown identifier `roots_multiset_prod` -/
#guard_msgs in
#check_failure roots_multiset_prod

/-! The default discharger handles hypotheses, positive degree, irreducibility, `NeZero p`,
monic polynomials, products, powers, maps along ring homomorphisms out of a field, `X ^ n - C a`
for `n ≠ 0`, quadratics and cubics with a nonzero leading coefficient, and minimal polynomials of
integral elements. -/

example (p : ℤ[X]) (hp : p ≠ 0) (a : ℤ) : a ∈ p.roots ↔ p.IsRoot a := mem_roots hp

example (p q : ℤ[X]) (hp : p ≠ 0) (hq : q ≠ 0) : (p * q).roots = p.roots + q.roots :=
  roots_mul (mul_ne_zero hp hq)

example (a : ℤ) : (X - C a).roots = {a} := roots_X_sub_C a

example (p : ℚ[X]) (hp : 0 < p.degree) (a : ℚ) : a ∈ p.roots ↔ p.IsRoot a := by simp

example (p : ℚ[X]) (hp : Irreducible p) : (p.roots).card ≤ p.natDegree := card_roots' p

example (p : ℚ[X]) [NeZero p] : (p.rootSet ℚ).Finite := rootSet_finite p ℚ _

example (p : ℚ[X]) (hp : p ≠ 0) (x : ℚ) : x ∈ p.rootSet ℚ ↔ aeval x p = 0 := mem_rootSet

example (n : ℕ) [NeZero n] (ζ : ℤ) : ζ ∈ nthRoots n (1 : ℤ) ↔ ζ ^ n = 1 := mem_nthRoots'

example (n : ℕ) (hn : 0 < n) (ζ : ℤ) : ζ ∈ nthRootsFinset n (1 : ℤ) ↔ ζ ^ n = 1 :=
  mem_nthRootsFinset'

example (P : Cubic ℚ) (ha : P.a ≠ 0) : P.roots = P.toPoly.roots := rfl

example (P : Cubic ℚ) (ha : P.a ≠ 0) (φ : ℚ →+* ℚ) :
    (Cubic.map φ P).roots = (P.toPoly.map φ).roots :=
  Cubic.map_roots

noncomputable example (a b c : ℚ) (ha : a ≠ 0) : Multiset ℚ := (C a * X ^ 2 + C b * X + C c).roots

noncomputable example (K : Type*) [Field K] [Algebra ℚ K] [Algebra.IsAlgebraic ℚ K] (x : K) :
    Multiset K :=
  (minpoly ℚ x).aroots K

/-! Without a proof that the polynomial is nonzero, there is no root multiset. -/

/--
error: could not synthesize default value for parameter 'hp' using tactics
---
error: the polynomial must be nonzero
p : ℤ[X]
⊢ p ≠ 0
-/
#guard_msgs in
noncomputable example (p : ℤ[X]) : Multiset ℤ := p.roots

/--
error: could not synthesize default value for parameter 'h' using tactics
---
error: the polynomial must be nonzero
n : ℕ
⊢ X ^ n - C 1 ≠ 0
-/
#guard_msgs in
noncomputable example (n : ℕ) : Multiset ℤ := nthRoots n 1

/-! The zero polynomial vanishes everywhere. -/

example (a : ℤ) : (0 : ℤ[X]).IsRoot a := by simp
