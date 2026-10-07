/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker, Johan Commelin
-/
module

public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Finite.Lemmas
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.Order.Filter.TendstoCofinite

/-!
# Theory of univariate polynomials

We define the multiset of roots of a polynomial, and prove basic results about it.

## Main definitions

* `Polynomial.roots p`: The multiset containing all the roots of a nonzero polynomial `p`,
  including their multiplicities. It takes a proof that `p` is nonzero, which `nonzero_tac`
  supplies by default.
* `Polynomial.rootSet p E`: The set of distinct roots in an algebra `E` of a polynomial `p` whose
  image in `E[X]` is nonzero.

## Main statements

* `Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C`: If a polynomial has as many roots as its
  degree, it can be written as the product of its leading coefficient with `∏ (X - a)` where `a`
  ranges through its roots.

-/

@[expose] public section

assert_not_exists Ideal

open Multiset Finset

noncomputable section

namespace Polynomial

universe u v w z

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

section CommRing

variable [CommRing R] [IsDomain R] {p q : R[X]}

section Roots

/-- `roots p` noncomputably gives a multiset containing all the roots of the nonzero polynomial
`p`, including their multiplicities. The zero polynomial vanishes everywhere, with infinite
multiplicity, and has no finite multiset of roots. The proof `hp` that `p` is nonzero can usually
be omitted, see `nonzero_tac`. -/
noncomputable def roots (p : R[X]) (hp : p ≠ 0 := by nonzero_tac) : Multiset R :=
  haveI := Classical.decEq R
  Classical.choose (exists_multiset_roots hp)

theorem roots_def [DecidableEq R] (p : R[X]) (hp : p ≠ 0) :
    p.roots = Classical.choose (exists_multiset_roots hp) := by
  rename_i iR
  obtain rfl := Subsingleton.elim iR (Classical.decEq R)
  rfl

theorem card_roots (hp0 : p ≠ 0) : (Multiset.card (roots p) : WithBot ℕ) ≤ degree p := by
  classical
  rw [roots_def p hp0]
  exact (Classical.choose_spec (exists_multiset_roots hp0)).1

theorem card_roots' (p : R[X]) {hp : p ≠ 0} : Multiset.card (p.roots hp) ≤ natDegree p :=
  WithBot.coe_le_coe.1 (le_trans (card_roots hp) (le_of_eq <| degree_eq_natDegree hp))

omit [IsDomain R] in
/-- A polynomial of positive degree minus a constant is nonzero. -/
theorem sub_C_ne_zero_of_degree_pos {p : R[X]} (hp0 : 0 < degree p) (a : R) : p - C a ≠ 0 :=
  mt sub_eq_zero.1 fun h => not_le_of_gt hp0 <| h.symm ▸ degree_C_le

macro_rules
  | `(tactic| nonzero_core) => `(tactic|
    ((with_reducible_and_instances apply Polynomial.sub_C_ne_zero_of_degree_pos);
      with_reducible_and_instances assumption))

theorem card_roots_sub_C {p : R[X]} {a : R} (hp0 : 0 < degree p) :
    haveI := sub_C_ne_zero_of_degree_pos hp0 a
    (Multiset.card (p - C a).roots : WithBot ℕ) ≤ degree p :=
  calc
    (Multiset.card ((p - C a).roots (sub_C_ne_zero_of_degree_pos hp0 a)) : WithBot ℕ) ≤
        degree (p - C a) :=
      card_roots _
    _ = degree p := by rw [sub_eq_add_neg, ← C_neg]; exact degree_add_C hp0

theorem card_roots_sub_C' {p : R[X]} {a : R} (hp0 : 0 < degree p) :
    haveI := sub_C_ne_zero_of_degree_pos hp0 a
    Multiset.card (p - C a).roots ≤ natDegree p :=
  WithBot.coe_le_coe.1
    (le_trans (card_roots_sub_C hp0)
      (le_of_eq <| degree_eq_natDegree fun h => by simp_all))

@[simp]
theorem count_roots [DecidableEq R] (p : R[X]) (hp : p ≠ 0) :
    p.roots.count a = rootMultiplicity a p := by
  rw [roots_def p hp]
  exact (Classical.choose_spec (exists_multiset_roots hp)).2 a

@[simp]
theorem mem_roots (hp : p ≠ 0) : a ∈ p.roots ↔ IsRoot p a := by
  classical
  rw [← count_pos, count_roots p hp, rootMultiplicity_pos hp]

theorem isRoot_of_mem_roots {hp : p ≠ 0} (h : a ∈ p.roots hp) : IsRoot p a :=
  (mem_roots hp).1 h

theorem roots_eq_zero_iff_isRoot_eq_bot (hp0 : p ≠ 0) : p.roots = 0 ↔ p.IsRoot = ⊥ := by
  refine ⟨fun h ↦ ?_, fun h ↦ eq_zero_of_forall_notMem fun x hx ↦ h ▸ mem_roots hp0 |>.mp hx⟩
  ext a
  simp only [Pi.bot_apply, Prop.bot_eq_false, mem_roots hp0 |>.not.mp <| by simp [h]]

theorem mem_roots_map_of_injective [Semiring S] {p : S[X]} {f : S →+* R}
    (hf : Function.Injective f) {x : R} (hp : p ≠ 0) :
    haveI := (Polynomial.map_ne_zero_iff hf).mpr hp
    x ∈ (p.map f).roots ↔ p.eval₂ f x = 0 := by
  rw [mem_roots ((Polynomial.map_ne_zero_iff hf).mpr hp), IsRoot, eval_map]

lemma mem_roots_iff_aeval_eq_zero {x : R} (w : p ≠ 0) : x ∈ roots p ↔ aeval x p = 0 := by
  rw [mem_roots w, IsRoot.def, aeval_def, Algebra.algebraMap_self, eval₂_eq_eval_map, map_id]

theorem card_le_degree_of_subset_roots {p : R[X]} {Z : Finset R} {hp : p ≠ 0}
    (h : Z.val ⊆ p.roots hp) : #Z ≤ p.natDegree :=
  (Multiset.card_le_card (Finset.val_le_iff_val_subset.2 h)).trans (Polynomial.card_roots' p)

theorem finite_setOfPred_isRoot {p : R[X]} (hp : p ≠ 0) : Set.Finite { x | IsRoot p x } := by
  classical
  simpa only [← Finset.setOfPred_mem, Multiset.mem_toFinset, mem_roots hp]
    using p.roots.toFinset.finite_toSet

@[deprecated (since := "2026-07-09")] alias finite_setOf_isRoot := finite_setOfPred_isRoot

/-- Nonzero polynomials have no roots away from a finite set. -/
lemma eventually_cofinite_not_isRoot {p : R[X]} (hp : p ≠ 0) :
    ∀ᶠ x in Filter.cofinite, ¬p.IsRoot x :=
  (finite_setOfPred_isRoot hp).compl_mem_cofinite

/-- Nonzero polynomials are nonzero away from a finite set. -/
lemma eventually_eval_ne_zero_cofinite {p : R[X]} (hp : p ≠ 0) :
    ∀ᶠ x in Filter.cofinite, p.eval x ≠ 0 :=
  eventually_cofinite_not_isRoot hp

theorem eq_zero_of_infinite_isRoot (p : R[X]) (h : Set.Infinite { x | IsRoot p x }) : p = 0 :=
  not_imp_comm.mp finite_setOfPred_isRoot h

theorem exists_max_root [LinearOrder R] (p : R[X]) (hp : p ≠ 0) : ∃ x₀, ∀ x, p.IsRoot x → x ≤ x₀ :=
  Set.exists_upper_bound_image _ _ <| finite_setOfPred_isRoot hp

theorem exists_min_root [LinearOrder R] (p : R[X]) (hp : p ≠ 0) : ∃ x₀, ∀ x, p.IsRoot x → x₀ ≤ x :=
  Set.exists_lower_bound_image _ _ <| finite_setOfPred_isRoot hp

theorem eq_of_infinite_eval_eq (p q : R[X]) (h : Set.Infinite { x | eval x p = eval x q }) :
    p = q := by
  rw [← sub_eq_zero]
  apply eq_zero_of_infinite_isRoot
  simpa only [IsRoot, eval_sub, sub_eq_zero]

/-- Non-constant polynomials have finite fibres, provided the coefficients are a domain. -/
lemma tendstoCofinite_of_natDegree_ne_zero {R : Type} [CommRing R] [IsDomain R] (p : R[X])
    (hp : p.natDegree ≠ 0) : Filter.TendstoCofinite p.eval := by
  rw [Filter.tendstoCofinite_iff_finite_preimage_singleton]
  intro x
  by_contra! hx
  obtain ⟨rfl⟩ : p = C x := p.eq_of_infinite_eval_eq (C x) (by simpa)
  simp at hp

theorem roots_mul {p q : R[X]} (hpq : p * q ≠ 0) :
    haveI := left_ne_zero_of_mul hpq
    haveI := right_ne_zero_of_mul hpq
    (p * q).roots = p.roots + q.roots := by
  classical
  exact Multiset.ext.mpr fun r => by
    rw [count_add, count_roots _ hpq, count_roots _ (left_ne_zero_of_mul hpq),
      count_roots _ (right_ne_zero_of_mul hpq), rootMultiplicity_mul hpq]

theorem roots.le_of_dvd (h : q ≠ 0) (hpq : p ∣ q) :
    roots p (ne_zero_of_dvd_ne_zero h hpq) ≤ roots q := by
  obtain ⟨k, rfl⟩ := hpq
  exact Multiset.le_iff_exists_add.mpr ⟨k.roots (right_ne_zero_of_mul h), roots_mul h⟩

theorem mem_roots_sub_C {p : R[X]} {a x : R} (hp0 : 0 < degree p) :
    haveI := sub_C_ne_zero_of_degree_pos hp0 a
    x ∈ (p - C a).roots ↔ p.eval x = a := by
  rw [mem_roots (sub_C_ne_zero_of_degree_pos hp0 a), IsRoot.def, eval_sub, eval_C, sub_eq_zero]

@[simp]
theorem roots_X_sub_C (r : R) : roots (X - C r) = {r} := by
  classical
  ext s
  rw [count_roots _ (X_sub_C_ne_zero r), rootMultiplicity_X_sub_C, count_singleton]

@[simp]
theorem roots_X_add_C (r : R) : roots (X + C r) = {-r} := by simpa using roots_X_sub_C (-r)

@[simp]
theorem roots_X : roots (X : R[X]) = {0} := by simpa using roots_X_sub_C (0 : R)

@[simp]
theorem roots_C (x : R) {h : C x ≠ 0} : (C x).roots h = 0 := by
  classical
  exact Multiset.ext.mpr fun r => by
    rw [count_roots _ h, count_zero, rootMultiplicity_eq_zero (not_isRoot_C _ _ (C_ne_zero.1 h))]

@[simp]
theorem roots_one : (1 : R[X]).roots = 0 :=
  roots_C 1

@[simp]
theorem roots_C_mul (p : R[X]) {h : C a * p ≠ 0} :
    (C a * p).roots h = p.roots (right_ne_zero_of_mul h) := by
  rw [roots_mul h, roots_C, zero_add]

theorem _root_.Associated.roots_eq {p q : R[X]} (h : Associated p q) {hp : p ≠ 0} :
    p.roots hp = q.roots (h.ne_zero_iff.1 hp) := by
  rcases h with ⟨u, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, (u : R[X]) = C c := ⟨_, eq_C_of_degree_eq_zero (degree_coe_units u)⟩
  simp only [hc, mul_comm p, roots_C_mul]

@[simp]
theorem roots_smul_nonzero (p : R[X]) {h : a • p ≠ 0} :
    (a • p).roots h = p.roots (right_ne_zero_of_smul h) := by
  simp only [smul_eq_C_mul, roots_C_mul]

@[simp]
lemma roots_neg (p : R[X]) {h : -p ≠ 0} : (-p).roots h = p.roots (neg_ne_zero.1 h) := by
  simp only [← neg_one_smul R p, roots_smul_nonzero]

@[simp]
theorem map_roots_comp_C_mul_X_add_C (p : R[X]) (a b : R) (ha : IsUnit a)
    {h : p.comp (C a * X + C b) ≠ 0} :
    ((p.comp (C a * X + C b)).roots h).map (fun x ↦ a * x + b) =
      p.roots (ne_zero_of_comp_ne_zero h) := by
  classical
  have hp := ne_zero_of_comp_ne_zero h
  set f := fun x ↦ a * x + b
  have hf : Function.Bijective f :=
    (AddGroup.addRight_bijective b).comp (IsUnit.isUnit_iff_mulLeft_bijective.mp ha)
  rw [Multiset.ext]
  intro x
  obtain ⟨x, rfl⟩ := hf.surjective x
  rw [count_roots _ hp, count_map_eq_count' f _ hf.injective, count_roots _ h,
    rootMultiplicity_comp_C_mul_X_add_C p a b x ha]

open scoped Ring in
theorem roots_comp_C_mul_X_add_C (p : R[X]) (a b : R) (ha : IsUnit a)
    {h : p.comp (C a * X + C b) ≠ 0} :
    (p.comp (C a * X + C b)).roots h =
      (p.roots (ne_zero_of_comp_ne_zero h)).map (fun x ↦ a⁻¹ʳ * (x - b)) := by
  conv_rhs => rw [← p.map_roots_comp_C_mul_X_add_C a b ha (h := h)]
  simp [← mul_assoc, Ring.inverse_mul_cancel a ha]

@[simp]
theorem roots_comp_neg_X (p : R[X]) {h : p.comp (-X) ≠ 0} :
    (p.comp (-X)).roots h = (p.roots (ne_zero_of_comp_ne_zero h)).map fun x ↦ -x := by
  have e : C (-1 : R) * X + C 0 = -X := by simp
  have h' : p.comp (C (-1 : R) * X + C 0) ≠ 0 := by rwa [e]
  have key := map_roots_comp_C_mul_X_add_C p (-1) 0 isUnit_neg_one (h := h')
  simp only [e, neg_one_mul, add_zero] at key
  rw [← key, Multiset.map_map]
  simp

@[simp]
theorem roots_C_mul_X_sub_C_of_IsUnit (b : R) (a : Rˣ) {h : C (a : R) * X - C b ≠ 0} :
    (C (a : R) * X - C b).roots h = {a⁻¹ * b} := by
  have e : C (↑a⁻¹ : R) * (C (a : R) * X - C b) = X - C (↑a⁻¹ * b) := by
    rw [mul_sub, ← mul_assoc, ← C_mul, ← C_mul, Units.inv_mul, C_1, one_mul]
  have h' : C (↑a⁻¹ : R) * (C (a : R) * X - C b) ≠ 0 := by
    rw [e]
    exact X_sub_C_ne_zero _
  rw [← roots_C_mul (C (a : R) * X - C b) (h := h')]
  simp only [e, roots_X_sub_C]

@[simp]
theorem roots_C_mul_X_add_C_of_IsUnit (b : R) (a : Rˣ) {h : C (a : R) * X + C b ≠ 0} :
    (C (a : R) * X + C b).roots h = {-(a⁻¹ * b)} := by
  have e : C (a : R) * X + C b = C (a : R) * X - C (-b) := by rw [C_neg, sub_neg_eq_add]
  simp only [e, roots_C_mul_X_sub_C_of_IsUnit, mul_neg]

theorem roots_prod {ι : Type*} (f : ι → R[X]) (s : Finset ι) (h : ∀ i ∈ s, f i ≠ 0) :
    haveI := Finset.prod_ne_zero_iff.mpr h
    (s.prod f).roots = ∑ i ∈ s.attach, (f i).roots (h i i.2) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    have hs : ∀ j ∈ s, f j ≠ 0 := fun j hj ↦ h j (Finset.mem_insert_of_mem hj)
    simp only [Finset.prod_insert hi]
    rw [roots_mul (mul_ne_zero (h i (Finset.mem_insert_self i s)) (Finset.prod_ne_zero_iff.mpr hs)),
      ih hs, Finset.attach_insert, Finset.sum_insert (by simp [hi]),
      Finset.sum_image (by intro x _ y _ hxy; exact Subtype.ext (Subtype.mk.inj hxy))]

@[simp]
theorem roots_pow (p : R[X]) (hp : p ≠ 0) (n : ℕ) : (p ^ n).roots = n • p.roots := by
  induction n with
  | zero => simp only [pow_zero, roots_one, zero_smul]
  | succ n ihn =>
    have h1 : p ^ n * p ≠ 0 := mul_ne_zero (pow_ne_zero _ hp) hp
    simp only [pow_succ]
    rw [roots_mul h1, ihn, add_smul, one_smul]

theorem roots_X_pow (n : ℕ) : (X ^ n : R[X]).roots = n • ({0} : Multiset R) := by
  rw [roots_pow X X_ne_zero, roots_X]

theorem roots_C_mul_X_pow (ha : a ≠ 0) (n : ℕ) :
    haveI := mul_ne_zero (C_ne_zero.2 ha) (pow_ne_zero n X_ne_zero)
    Polynomial.roots (C a * X ^ n) = n • ({0} : Multiset R) := by
  rw [roots_C_mul, roots_X_pow]

@[simp]
theorem roots_monomial (ha : a ≠ 0) (n : ℕ) :
    haveI := (monomial_eq_zero_iff a n).not.2 ha
    (monomial n a).roots = n • ({0} : Multiset R) := by
  simp only [← C_mul_X_pow_eq_monomial, roots_C_mul, roots_X_pow]

theorem roots_prod_X_sub_C (s : Finset R) : (s.prod fun a => X - C a).roots = s.val := by
  rw [roots_prod (fun a => X - C a) s fun a _ => X_sub_C_ne_zero a]
  simp only [roots_X_sub_C]
  rw [Finset.sum_attach s (fun a => ({a} : Multiset R)), Finset.sum_eq_multiset_sum,
    Multiset.sum_map_singleton]

@[simp]
theorem roots_multiset_prod_X_sub_C (s : Multiset R) :
    haveI := (monic_multiset_prod_of_monic s (fun a => X - C a)
      fun a _ => monic_X_sub_C a).ne_zero
    (s.map fun a => X - C a).prod.roots = s := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have hs :=
      (monic_multiset_prod_of_monic s (fun a => X - C a) fun a _ => monic_X_sub_C a).ne_zero
    simp only [Multiset.map_cons, Multiset.prod_cons]
    rw [roots_mul (mul_ne_zero (X_sub_C_ne_zero a) hs), roots_X_sub_C, ih, Multiset.singleton_add]

theorem roots_ofMultiset (s : Multiset R) :
    haveI : ofMultiset s ≠ 0 := by
      rw [ofMultiset_apply]
      exact (monic_multiset_prod_of_monic s (fun a => X - C a)
        fun a _ => monic_X_sub_C a).ne_zero
    (ofMultiset s).roots = s := by
  simp only [ofMultiset_apply, roots_multiset_prod_X_sub_C]

variable (R) in
theorem ofMultiset_injective : Function.Injective (ofMultiset (R := R)) := fun s t h ↦ by
  rw [← roots_ofMultiset s, ← roots_ofMultiset t]
  simp only [h]

theorem card_roots_X_pow_sub_C {n : ℕ} (hn : 0 < n) (a : R) :
    haveI := X_pow_sub_C_ne_zero hn a
    Multiset.card (roots ((X : R[X]) ^ n - C a)) ≤ n :=
  WithBot.coe_le_coe.1 <|
    calc
      (Multiset.card (roots ((X : R[X]) ^ n - C a) (X_pow_sub_C_ne_zero hn a)) : WithBot ℕ) ≤
          degree ((X : R[X]) ^ n - C a) :=
        card_roots (X_pow_sub_C_ne_zero hn a)
      _ = n := degree_X_pow_sub_C hn a

theorem roots_eq_of_degree_le_card_of_ne_zero {S : Finset R}
    (hS : ∀ x ∈ S, p.eval x = 0) (hcard : p.degree ≤ S.card) (hp : p ≠ 0) : p.roots = S.val := by
  refine (Multiset.eq_of_le_of_card_le ?_ ?_).symm
  · exact (Finset.val_le_iff_val_subset.mpr (fun x hx ↦ (p.mem_roots hp).mpr (hS x hx)))
  · simpa using (p.card_roots hp).trans hcard

theorem roots_eq_of_degree_eq_card {S : Finset R}
    (hS : ∀ x ∈ S, p.eval x = 0) (hcard : S.card = p.degree) {hp : p ≠ 0} : p.roots hp = S.val :=
  roots_eq_of_degree_le_card_of_ne_zero hS (by grind) hp

theorem roots_eq_of_natDegree_le_card_of_ne_zero {S : Finset R}
    (hS : ∀ x ∈ S, p.eval x = 0) (hcard : p.natDegree ≤ S.card) (hp : p ≠ 0) : p.roots = S.val :=
  roots_eq_of_degree_le_card_of_ne_zero hS (degree_le_of_natDegree_le hcard) hp

section NthRoots

/-- `nthRoots n a` noncomputably returns the solutions to `x ^ n = a`, with the multiplicities of
the roots of `X ^ n - C a`. It takes a proof that `X ^ n - C a` is nonzero, that is, that `n ≠ 0` or
`a ≠ 1`: for `n = 0` and `a = 1` every element is a solution. The proof can usually be omitted, see
`nonzero_tac`. -/
def nthRoots (n : ℕ) (a : R) (h : (X : R[X]) ^ n - C a ≠ 0 := by nonzero_tac) : Multiset R :=
  roots ((X : R[X]) ^ n - C a) h

/-- Membership in `nthRoots n a` for any proof of its domain; `mem_nthRoots` takes `0 < n`, from
which `nonzero_tac` finds the domain. -/
@[simp]
theorem mem_nthRoots' {n : ℕ} {a x : R} {h : (X : R[X]) ^ n - C a ≠ 0} :
    x ∈ nthRoots n a h ↔ x ^ n = a := by
  rw [nthRoots, mem_roots h, IsRoot.def, eval_sub, eval_C, eval_pow, eval_X, sub_eq_zero]

theorem mem_nthRoots {n : ℕ} (hn : 0 < n) {a x : R} : x ∈ nthRoots n a ↔ x ^ n = a :=
  mem_nthRoots'

@[simp]
theorem nthRoots_zero (r : R) {h : (X : R[X]) ^ 0 - C r ≠ 0} : nthRoots 0 r h = 0 := by
  simp only [nthRoots, pow_zero, ← C_1, ← C_sub, roots_C]

@[simp]
theorem nthRoots_zero_right {R} [CommRing R] [IsDomain R] (n : ℕ)
    {h : (X : R[X]) ^ n - C 0 ≠ 0} : nthRoots n (0 : R) h = Multiset.replicate n 0 := by
  simp only [nthRoots, C.map_zero, sub_zero]
  rw [roots_pow X X_ne_zero, roots_X, Multiset.nsmul_singleton]

theorem card_nthRoots (n : ℕ) (a : R) {h : (X : R[X]) ^ n - C a ≠ 0} :
    Multiset.card (nthRoots n a h) ≤ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [← Nat.cast_le (α := WithBot ℕ), ← degree_X_pow_sub_C hn a]
  exact card_roots h

@[simp]
theorem nthRoots_two_eq_zero_iff {r : R} : nthRoots 2 r = 0 ↔ ¬IsSquare r := by
  simp_rw [isSquare_iff_exists_sq, eq_zero_iff_forall_notMem, mem_nthRoots (by simp : 0 < 2),
    ← not_exists, eq_comm]

/-- The multiset `nthRoots ↑n a` as a Finset. Previously `nthRootsFinset n` was defined to be
`nthRoots n (1 : R)` as a Finset. That situation can be recovered by setting `a` to be `(1 : R)`.
Like `nthRoots`, it takes a proof that `X ^ n - C a` is nonzero, see `nonzero_tac`. -/
def nthRootsFinset (n : ℕ) {R : Type*} (a : R) [CommRing R] [IsDomain R]
    (h : (X : R[X]) ^ n - C a ≠ 0 := by nonzero_tac) : Finset R :=
  haveI := Classical.decEq R
  Multiset.toFinset (nthRoots n a h)

lemma nthRootsFinset_def (n : ℕ) {R : Type*} (a : R) [CommRing R] [IsDomain R] [DecidableEq R]
    (h : (X : R[X]) ^ n - C a ≠ 0) :
    nthRootsFinset n a h = Multiset.toFinset (nthRoots n a h) := by
  unfold nthRootsFinset
  convert! rfl

/-- Membership in `nthRootsFinset n a` for any proof of its domain; `mem_nthRootsFinset` takes
`0 < n`, from which `nonzero_tac` finds the domain. -/
@[simp]
theorem mem_nthRootsFinset' {n : ℕ} {a x : R} {h : (X : R[X]) ^ n - C a ≠ 0} :
    x ∈ nthRootsFinset n a h ↔ x ^ (n : ℕ) = a := by
  classical
  rw [nthRootsFinset_def _ _ h, mem_toFinset, mem_nthRoots']

theorem mem_nthRootsFinset {n : ℕ} (h : 0 < n) (a : R) {x : R} :
    x ∈ nthRootsFinset n a ↔ x ^ (n : ℕ) = a :=
  mem_nthRootsFinset'

@[simp]
theorem nthRootsFinset_zero (a : R) {h : (X : R[X]) ^ 0 - C a ≠ 0} : nthRootsFinset 0 a h = ∅ := by
  classical simp [nthRootsFinset_def _ _ h]

theorem pos_of_mem_nthRootsFinset {η a : R} {h : (X : R[X]) ^ n - C a ≠ 0}
    (hη : η ∈ nthRootsFinset n a h) : 0 < n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp at hη
  · exact hn

theorem map_mem_nthRootsFinset {S F : Type*} [CommRing S] [IsDomain S] [FunLike F R S]
    [MonoidHomClass F R S] {a : R} {x : R} {h : (X : R[X]) ^ n - C a ≠ 0}
    (hx : x ∈ nthRootsFinset n a h) (f : F) :
    haveI := X_pow_sub_C_ne_zero (pos_of_mem_nthRootsFinset hx) (f a)
    f x ∈ nthRootsFinset n (f a) := by
  have hn := pos_of_mem_nthRootsFinset hx
  rw [mem_nthRootsFinset hn, ← map_pow, (mem_nthRootsFinset hn a).1 hx]

theorem map_mem_nthRootsFinset_one {S F : Type*} [CommRing S] [IsDomain S] [FunLike F R S]
    [RingHomClass F R S] {x : R} {h : (X : R[X]) ^ n - C 1 ≠ 0} (hx : x ∈ nthRootsFinset n 1 h)
    (f : F) :
    haveI := X_pow_sub_C_ne_zero (pos_of_mem_nthRootsFinset hx) (1 : S)
    f x ∈ nthRootsFinset n 1 := by
  have hn := pos_of_mem_nthRootsFinset hx
  rw [mem_nthRootsFinset hn, ← map_pow, (mem_nthRootsFinset hn (1 : R)).1 hx, map_one]

theorem mul_mem_nthRootsFinset {η₁ η₂ : R} {a₁ a₂ : R} {h₁ : (X : R[X]) ^ n - C a₁ ≠ 0}
    {h₂ : (X : R[X]) ^ n - C a₂ ≠ 0} (hη₁ : η₁ ∈ nthRootsFinset n a₁ h₁)
    (hη₂ : η₂ ∈ nthRootsFinset n a₂ h₂) :
    haveI := X_pow_sub_C_ne_zero (pos_of_mem_nthRootsFinset hη₁) (a₁ * a₂)
    η₁ * η₂ ∈ nthRootsFinset n (a₁ * a₂) := by
  have hn := pos_of_mem_nthRootsFinset hη₁
  rw [mem_nthRootsFinset hn] at hη₁ hη₂ ⊢
  rw [mul_pow, hη₁, hη₂]

theorem ne_zero_of_mem_nthRootsFinset {η : R} {a : R} (ha : a ≠ 0) {h : (X : R[X]) ^ n - C a ≠ 0}
    (hη : η ∈ nthRootsFinset n a h) : η ≠ 0 := by
  rintro rfl
  have hn := pos_of_mem_nthRootsFinset hη
  rw [mem_nthRootsFinset hn, zero_pow hn.ne'] at hη
  exact ha hη.symm

theorem one_mem_nthRootsFinset (hn : 0 < n) : 1 ∈ nthRootsFinset n (1 : R) := by
  rw [mem_nthRootsFinset hn, one_pow]

lemma nthRoots_two_one : Polynomial.nthRoots 2 (1 : R) = {-1,1} := by
  have h₁ : (X ^ 2 - C 1 : R[X]) = (X + C 1) * (X - C 1) := by simp [← sq_sub_sq]
  have h₂ : (X + C 1) * (X - C 1 : R[X]) ≠ 0 := mul_ne_zero (X_add_C_ne_zero 1) (X_sub_C_ne_zero 1)
  simp only [nthRoots, h₁]
  rw [roots_mul h₂, roots_X_add_C, roots_X_sub_C]; rfl

end NthRoots

theorem zero_of_eval_zero [Infinite R] (p : R[X]) (h : ∀ x, p.eval x = 0) : p = 0 := by
  classical
  by_contra hp
  refine @Fintype.false R _ ?_
  exact ⟨p.roots.toFinset, fun x => Multiset.mem_toFinset.mpr ((mem_roots hp).mpr (h _))⟩

theorem funext [Infinite R] {p q : R[X]} (ext : ∀ r : R, p.eval r = q.eval r) : p = q := by
  rw [← sub_eq_zero]
  apply zero_of_eval_zero
  intro x
  rw [eval_sub, sub_eq_zero, ext]

variable [CommRing T]

/-- Given a polynomial `p` with coefficients in a ring `T` and a `T`-algebra `S`, `aroots p S` is
the multiset of roots of `p` regarded as a polynomial over `S`. It takes a proof that the image of
`p` in `S[X]` is nonzero, which `nonzero_tac` supplies by default. -/
noncomputable abbrev aroots (p : T[X]) (S) [CommRing S] [IsDomain S] [Algebra T S]
    (hp : p.map (algebraMap T S) ≠ 0 := by nonzero_tac) : Multiset S :=
  (p.map (algebraMap T S)).roots hp

theorem aroots_def (p : T[X]) (S) [CommRing S] [IsDomain S] [Algebra T S]
    (hp : p.map (algebraMap T S) ≠ 0) : p.aroots S hp = (p.map (algebraMap T S)).roots hp :=
  rfl

theorem mem_aroots [CommRing S] [IsDomain S] [Algebra T S] {p : T[X]} {a : S}
    {hp : p.map (algebraMap T S) ≠ 0} : a ∈ p.aroots S hp ↔ aeval a p = 0 := by
  rw [aroots_def, mem_roots hp, IsRoot.def, ← eval₂_eq_eval_map, aeval_def]

theorem aroots_mul [IsDomain T] [CommRing S] [IsDomain S] [Algebra T S]
    [Module.IsTorsionFree T S] {p q : T[X]} (hpq : p * q ≠ 0) :
    haveI hinj := FaithfulSMul.algebraMap_injective T S
    haveI := (Polynomial.map_ne_zero_iff hinj).2 hpq
    haveI := (Polynomial.map_ne_zero_iff hinj).2 (left_ne_zero_of_mul hpq)
    haveI := (Polynomial.map_ne_zero_iff hinj).2 (right_ne_zero_of_mul hpq)
    (p * q).aroots S = p.aroots S + q.aroots S := by
  have hinj := FaithfulSMul.algebraMap_injective T S
  have h : p.map (algebraMap T S) * q.map (algebraMap T S) ≠ 0 := by
    rw [← Polynomial.map_mul]
    exact (Polynomial.map_ne_zero_iff hinj).2 hpq
  simp only [aroots_def, Polynomial.map_mul]
  exact roots_mul h

@[simp]
theorem aroots_X_sub_C [CommRing S] [IsDomain S] [Algebra T S]
    (r : T) : aroots (X - C r) S = {algebraMap T S r} := by
  simp only [aroots_def, Polynomial.map_sub, map_X, map_C, roots_X_sub_C]

@[simp]
theorem aroots_X [CommRing S] [IsDomain S] [Algebra T S] :
    aroots (X : T[X]) S = {0} := by
  simp only [aroots_def, map_X, roots_X]

@[simp]
theorem aroots_C [CommRing S] [IsDomain S] [Algebra T S] (a : T)
    {h : (C a).map (algebraMap T S) ≠ 0} : (C a).aroots S h = 0 := by
  simp only [aroots_def, map_C, roots_C]

@[simp]
theorem aroots_one [CommRing S] [IsDomain S] [Algebra T S] :
    (1 : T[X]).aroots S = 0 := by
  simp only [aroots_def, Polynomial.map_one, roots_one]

@[simp]
theorem aroots_neg [CommRing S] [IsDomain S] [Algebra T S] (p : T[X])
    {h : (-p).map (algebraMap T S) ≠ 0} :
    haveI : p.map (algebraMap T S) ≠ 0 := by simpa [Polynomial.map_neg] using h
    (-p).aroots S h = p.aroots S := by
  simp only [aroots_def, Polynomial.map_neg, roots_neg]

@[simp]
theorem aroots_C_mul [CommRing S] [IsDomain S] [Algebra T S] {a : T} (p : T[X])
    {h : (C a * p).map (algebraMap T S) ≠ 0} :
    haveI : p.map (algebraMap T S) ≠ 0 := by
      rw [Polynomial.map_mul] at h
      exact right_ne_zero_of_mul h
    (C a * p).aroots S h = p.aroots S := by
  simp only [aroots_def, Polynomial.map_mul, map_C, roots_C_mul]

@[simp]
theorem aroots_smul_nonzero [CommRing S] [IsDomain S] [Algebra T S] {a : T} (p : T[X])
    {h : (a • p).map (algebraMap T S) ≠ 0} :
    haveI : p.map (algebraMap T S) ≠ 0 := by
      rw [smul_eq_C_mul, Polynomial.map_mul] at h
      exact right_ne_zero_of_mul h
    (a • p).aroots S h = p.aroots S := by
  simp only [smul_eq_C_mul, aroots_C_mul]

@[simp]
theorem aroots_pow [CommRing S] [IsDomain S] [Algebra T S] (p : T[X])
    (hp : p.map (algebraMap T S) ≠ 0) (n : ℕ) :
    haveI : (p ^ n).map (algebraMap T S) ≠ 0 := by
      rw [Polynomial.map_pow]
      exact pow_ne_zero n hp
    (p ^ n).aroots S = n • p.aroots S := by
  simp only [aroots_def, Polynomial.map_pow]
  exact roots_pow _ hp n

theorem aroots_X_pow [CommRing S] [IsDomain S] [Algebra T S] (n : ℕ) :
    (X ^ n : T[X]).aroots S = n • ({0} : Multiset S) := by
  simp only [aroots_def, Polynomial.map_pow, map_X]
  exact roots_X_pow n

theorem aroots_C_mul_X_pow [CommRing S] [IsDomain S] [Algebra T S] {a : T} (n : ℕ)
    {h : (C a * X ^ n : T[X]).map (algebraMap T S) ≠ 0} :
    (C a * X ^ n : T[X]).aroots S h = n • ({0} : Multiset S) := by
  rw [aroots_C_mul, aroots_X_pow]

@[simp]
theorem aroots_monomial [CommRing S] [IsDomain S] [Algebra T S] {a : T} (n : ℕ)
    {h : (monomial n a).map (algebraMap T S) ≠ 0} :
    (monomial n a).aroots S h = n • ({0} : Multiset S) := by
  simp only [← C_mul_X_pow_eq_monomial]
  exact aroots_C_mul_X_pow n

variable (R S) in
@[simp]
theorem aroots_map (p : T[X]) [CommRing S] [Algebra T S] [Algebra S R] [Algebra T R]
    [IsScalarTower T S R] {h : (p.map (algebraMap T S)).map (algebraMap S R) ≠ 0} :
    haveI : p.map (algebraMap T R) ≠ 0 := by
      rwa [map_map, ← IsScalarTower.algebraMap_eq] at h
    (p.map (algebraMap T S)).aroots R h = p.aroots R := by
  simp only [aroots_def, map_map, ← IsScalarTower.algebraMap_eq]

/-- The set of distinct roots in `S` of a polynomial `p` whose image in `S[X]` is nonzero, the
support of `p.aroots S`. The zero locus `{x | aeval x p = 0}` of an arbitrary polynomial needs no
such proof.

If you have a non-separable polynomial, use `Polynomial.aroots` for the multiset
where multiple roots have the appropriate multiplicity. -/
def rootSet (p : T[X]) (S) [CommRing S] [IsDomain S] [Algebra T S]
    (hp : p.map (algebraMap T S) ≠ 0 := by nonzero_tac) : Set S :=
  haveI := Classical.decEq S
  (p.aroots S hp).toFinset

theorem rootSet_def (p : T[X]) (S) [CommRing S] [IsDomain S] [Algebra T S] [DecidableEq S]
    (hp : p.map (algebraMap T S) ≠ 0) : p.rootSet S hp = (p.aroots S hp).toFinset := by
  rw [rootSet]
  convert! rfl

@[simp]
theorem rootSet_C [CommRing S] [IsDomain S] [Algebra T S] (a : T)
    {h : (C a).map (algebraMap T S) ≠ 0} : (C a).rootSet S h = ∅ := by
  classical
  rw [rootSet_def, aroots_C, Multiset.toFinset_zero, Finset.coe_empty]

@[simp]
theorem rootSet_one (S) [CommRing S] [IsDomain S] [Algebra T S] : (1 : T[X]).rootSet S = ∅ := by
  classical
  rw [rootSet_def, aroots_one, Multiset.toFinset_zero, Finset.coe_empty]

@[simp]
theorem rootSet_neg (p : T[X]) (S) [CommRing S] [IsDomain S] [Algebra T S]
    {h : (-p).map (algebraMap T S) ≠ 0} :
    haveI : p.map (algebraMap T S) ≠ 0 := by simpa [Polynomial.map_neg] using h
    (-p).rootSet S h = p.rootSet S := by
  simp only [rootSet, aroots_neg]

instance rootSetFintype (p : T[X]) (S : Type*) [CommRing S] [IsDomain S] [Algebra T S]
    (hp : p.map (algebraMap T S) ≠ 0) : Fintype (p.rootSet S hp) :=
  FinsetCoe.fintype _

theorem rootSet_finite (p : T[X]) (S : Type*) [CommRing S] [IsDomain S] [Algebra T S]
    (hp : p.map (algebraMap T S) ≠ 0) : (p.rootSet S hp).Finite :=
  Set.toFinite _

variable (T R) in
@[simp]
theorem rootSet_map [CommRing S] (p : S[X]) [Algebra S T] [Algebra T R] [Algebra S R]
    [IsScalarTower S T R] {h : (p.map (algebraMap S T)).map (algebraMap T R) ≠ 0} :
    haveI : p.map (algebraMap S R) ≠ 0 := by
      rwa [map_map, ← IsScalarTower.algebraMap_eq] at h
    (p.map (algebraMap S T)).rootSet R h = p.rootSet R := by
  classical
  rw [rootSet_def, rootSet_def, aroots_map]

/-- The set of roots of all polynomials of bounded degree, with coefficients in a finite set and
nonzero image under `m`, is finite. -/
theorem bUnion_roots_finite {R S : Type*} [Semiring R] [CommRing S] [IsDomain S] [DecidableEq S]
    (m : R →+* S) (d : ℕ) {U : Set R} (h : U.Finite) :
    (⋃ (f : R[X]) (hf : f.natDegree ≤ d ∧ (∀ i, f.coeff i ∈ U) ∧ f.map m ≠ 0),
        (((f.map m).roots hf.2.2).toFinset : Set S)).Finite :=
  Set.Finite.biUnion'
    (by
      -- We prove that the set of polynomials under consideration is finite because its
      -- image by the injective map `π` is finite
      let π : R[X] → Fin (d + 1) → R := fun f i => f.coeff i
      refine ((Set.Finite.pi fun _ => h).subset <| ?_).of_finite_image (?_ : Set.InjOn π _)
      · exact Set.image_subset_iff.2 fun f hf i _ => hf.2.1 i
      · refine fun x hx y hy hxy => (ext_iff_natDegree_le hx.1 hy.1).2 fun i hi => ?_
        exact id congr_fun hxy ⟨i, Nat.lt_succ_of_le hi⟩)
    fun _ _ => Finset.finite_toSet _

theorem mem_rootSet {p : T[X]} {S : Type*} [CommRing S] [IsDomain S] [Algebra T S] {a : S}
    {hp : p.map (algebraMap T S) ≠ 0} : a ∈ p.rootSet S hp ↔ aeval a p = 0 := by
  classical
  rw [rootSet_def, Finset.mem_coe, mem_toFinset, mem_aroots]

theorem preimage_eval_singleton (hp : p ≠ C a) :
    haveI : (p - C a).map (algebraMap R R) ≠ 0 := by
      rw [Algebra.algebraMap_self, map_id]
      exact sub_ne_zero.2 hp
    p.eval ⁻¹' {a} = (p - C a).rootSet R := by
  ext; simp [mem_rootSet, sub_eq_zero]

theorem Monic.mem_rootSet {p : T[X]} (hp : Monic p) {S : Type*} [CommRing S] [IsDomain S]
    [Algebra T S] {a : S} : a ∈ p.rootSet S ↔ aeval a p = 0 :=
  Polynomial.mem_rootSet

theorem rootSet_maps_to' {p : T[X]} {S S'} [CommRing S] [IsDomain S] [Algebra T S] [CommRing S']
    [IsDomain S'] [Algebra T S'] {hS : p.map (algebraMap T S) ≠ 0}
    (hS' : p.map (algebraMap T S') ≠ 0) (f : S →ₐ[T] S') :
    (p.rootSet S hS).MapsTo f (p.rootSet S' hS') := fun x hx => by
  rw [mem_rootSet] at hx ⊢
  rw [aeval_algHom, AlgHom.comp_apply, hx, _root_.map_zero]

theorem aeval_eq_zero_of_mem_rootSet {p : T[X]} [CommRing S] [IsDomain S] [Algebra T S] {a : S}
    {hp : p.map (algebraMap T S) ≠ 0} (hx : a ∈ p.rootSet S hp) : aeval a p = 0 :=
  mem_rootSet.1 hx

lemma rootSet_mapsTo {p : T[X]} [IsDomain T] {S S' : Type*} [CommRing S] [IsDomain S] [Algebra T S]
    [CommRing S'] [IsDomain S'] [Algebra T S'] [Module.IsTorsionFree T S']
    {hS : p.map (algebraMap T S) ≠ 0} (f : S →ₐ[T] S') :
    haveI := (Polynomial.map_ne_zero_iff (FaithfulSMul.algebraMap_injective T S')).2
      (ne_zero_of_map_ne_zero hS)
    (p.rootSet S hS).MapsTo f (p.rootSet S') :=
  rootSet_maps_to' _ f

theorem mem_rootSet_of_injective [CommRing S] {p : S[X]} [Algebra S R]
    (h : Function.Injective (algebraMap S R)) {x : R} (hp : p ≠ 0) :
    haveI := (Polynomial.map_ne_zero_iff h).2 hp
    x ∈ p.rootSet R ↔ aeval x p = 0 :=
  mem_rootSet

@[simp]
theorem nthRootsFinset_toSet {n : ℕ} (h : 0 < n) (a : R) :
    nthRootsFinset n a = {r | r ^ n = a} := by
  ext x
  simp_all

theorem smul_mem_rootSet [CommRing S] [Algebra S R] {G : Type*}
    [Monoid G] [MulSemiringAction G R] [SMulCommClass G S R] {f : S[X]}
    {hf : f.map (algebraMap S R) ≠ 0} (g : G) {x : R} (hx : x ∈ f.rootSet R hf) :
    g • x ∈ f.rootSet R hf := by
  simp [mem_rootSet, aeval_smul, aeval_eq_zero_of_mem_rootSet hx]

theorem smul_mem_rootSet_iff_of_isUnit [CommRing S] [Algebra S R] {G : Type*}
    [Monoid G] [MulSemiringAction G R] [SMulCommClass G S R] {f : S[X]}
    {hf : f.map (algebraMap S R) ≠ 0} {g : G} (hg : IsUnit g) {x : R} :
    g • x ∈ f.rootSet R hf ↔ x ∈ f.rootSet R hf := by
  refine ⟨?_, smul_mem_rootSet g⟩
  obtain ⟨g, rfl⟩ := hg
  exact fun hx ↦ inv_smul_smul g x ▸ smul_mem_rootSet _ hx

theorem smul_mem_rootSet_iff [CommRing S] [Algebra S R] {G : Type*}
    [Group G] [MulSemiringAction G R] [SMulCommClass G S R] {f : S[X]}
    {hf : f.map (algebraMap S R) ≠ 0} {g : G} {x : R} :
    g • x ∈ f.rootSet R hf ↔ x ∈ f.rootSet R hf :=
  smul_mem_rootSet_iff_of_isUnit (Group.isUnit g)

instance [CommRing S] [Algebra S R] (G : Type*)
    [Monoid G] [MulSemiringAction G R] [SMulCommClass G S R] (f : S[X])
    (hf : f.map (algebraMap S R) ≠ 0) :
    MulAction G (f.rootSet R hf) where
  smul g x := ⟨g • x.1, smul_mem_rootSet g x.2⟩
  one_smul x := Subtype.ext (one_smul G x.1)
  mul_smul g h x := Subtype.ext (mul_smul g h x.1)

@[simp]
theorem rootSet.coe_smul [CommRing S] [Algebra S R] {G : Type*}
    [Monoid G] [MulSemiringAction G R] [SMulCommClass G S R] {f : S[X]}
    {hf : f.map (algebraMap S R) ≠ 0} (g : G) (x : f.rootSet R hf) :
    (g • x : f.rootSet R hf) = g • (x : R) :=
  rfl

instance [CommRing S] [Algebra S R] (G H : Type*)
    [Monoid G] [MulSemiringAction G R] [SMulCommClass G S R]
    [Monoid H] [MulSemiringAction H R] [SMulCommClass H S R]
    [SMulCommClass G H R] (f : S[X]) (hf : f.map (algebraMap S R) ≠ 0) :
    SMulCommClass G H (f.rootSet R hf) where
  smul_comm _ _ _ := Subtype.ext <| smul_comm _ _ _

instance [CommRing S] [Algebra S R] (G H : Type*)
    [Monoid G] [MulSemiringAction G R] [SMulCommClass G S R]
    [Monoid H] [MulSemiringAction H R] [SMulCommClass H S R]
    [SMul G H] [IsScalarTower G H R] (f : S[X]) (hf : f.map (algebraMap S R) ≠ 0) :
    IsScalarTower G H (f.rootSet R hf) where
  smul_assoc _ _ _ := Subtype.ext <| smul_assoc _ _ _

end Roots

lemma eq_zero_of_natDegree_lt_card_of_eval_eq_zero {R} [CommRing R] [IsDomain R]
    (p : R[X]) {ι} [Fintype ι] {f : ι → R} (hf : Function.Injective f)
    (heval : ∀ i, p.eval (f i) = 0) (hcard : natDegree p < Fintype.card ι) : p = 0 := by
  classical
  by_contra hp
  refine lt_irrefl #p.roots.toFinset ?_
  calc
    #p.roots.toFinset ≤ Multiset.card p.roots := Multiset.toFinset_card_le _
    _ ≤ natDegree p := Polynomial.card_roots' p
    _ < Fintype.card ι := hcard
    _ = Fintype.card (Set.range f) := (Set.card_range_of_injective hf).symm
    _ = #(Finset.univ.image f) := by rw [← Set.toFinset_card, Set.toFinset_range]
    _ ≤ #p.roots.toFinset := Finset.card_mono ?_
  intro _
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Multiset.mem_toFinset, mem_roots hp,
    IsRoot.def, forall_exists_index]
  rintro x rfl
  exact heval _

lemma eq_of_natDegree_lt_card_of_eval_eq {R} [CommRing R] [IsDomain R]
    (p q : R[X]) {ι} [Fintype ι] {f : ι → R} (hf : Function.Injective f)
    (heval : ∀ i : ι, eval (f i) p = eval (f i) q)
    (hcard : max p.natDegree q.natDegree < Fintype.card ι) : p = q := by
  rw [← sub_eq_zero]
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hf
  · simpa [sub_eq_zero]
  · grind [natDegree_sub_le]

lemma eq_zero_of_natDegree_lt_card_of_eval_eq_zero' {R} [CommRing R] [IsDomain R]
    (p : R[X]) (s : Finset R) (heval : ∀ i ∈ s, p.eval i = 0) (hcard : natDegree p < #s) :
    p = 0 :=
  eq_zero_of_natDegree_lt_card_of_eval_eq_zero p Subtype.val_injective
    (fun i : s ↦ heval i i.prop) (hcard.trans_eq (Fintype.card_coe s).symm)

lemma eq_of_natDegree_lt_card_of_eval_eq' {R} [CommRing R] [IsDomain R]
    (p q : R[X]) (s : Finset R) (heval : ∀ i ∈ s, p.eval i = q.eval i)
    (hcard : max p.natDegree q.natDegree < #s) : p = q :=
  eq_of_natDegree_lt_card_of_eval_eq p q Subtype.val_injective
    (fun i : s ↦ heval i i.prop) (hcard.trans_eq (Fintype.card_coe s).symm)

open Cardinal in
lemma eq_zero_of_forall_eval_zero_of_natDegree_lt_card
    (f : R[X]) (hf : ∀ r, f.eval r = 0) (hfR : f.natDegree < #R) : f = 0 := by
  obtain hR | hR := finite_or_infinite R
  · have := Fintype.ofFinite R
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero f Function.injective_id hf
    simpa only [mk_fintype, Nat.cast_lt] using hfR
  · exact zero_of_eval_zero _ hf

open Cardinal in
lemma exists_eval_ne_zero_of_natDegree_lt_card (f : R[X]) (hf : f ≠ 0) (hfR : f.natDegree < #R) :
    ∃ r, f.eval r ≠ 0 := by
  contrapose! hf
  exact eq_zero_of_forall_eval_zero_of_natDegree_lt_card f hf hfR

section

omit [IsDomain R]

theorem monic_multisetProd_X_sub_C (s : Multiset R) : Monic (s.map fun a => X - C a).prod :=
  monic_multiset_prod_of_monic _ _ fun a _ => monic_X_sub_C a

theorem monic_prod_X_sub_C {α : Type*} (b : α → R) (s : Finset α) :
    Monic (∏ a ∈ s, (X - C (b a))) :=
  monic_prod_of_monic _ _ fun a _ => monic_X_sub_C (b a)

theorem monic_finprod_X_sub_C {α : Type*} (b : α → R) : Monic (∏ᶠ k, (X - C (b k))) :=
  monic_finprod_of_monic _ _ fun a _ => monic_X_sub_C (b a)

end

theorem prod_multiset_root_eq_finset_root [DecidableEq R] (hp : p ≠ 0) :
    (p.roots.map fun a => X - C a).prod =
      p.roots.toFinset.prod fun a => (X - C a) ^ rootMultiplicity a p := by
  simp only [count_roots p hp, Finset.prod_multiset_map_count]

/-- The product `∏ (X - a)` for `a` inside the multiset `p.roots` divides `p`. -/
theorem prod_multiset_X_sub_C_dvd (p : R[X]) {hp : p ≠ 0} :
    ((p.roots hp).map fun a => X - C a).prod ∣ p := by
  classical
  rw [← map_dvd_map _ (IsFractionRing.injective R <| FractionRing R)
    (monic_multisetProd_X_sub_C p.roots)]
  rw [prod_multiset_root_eq_finset_root hp, Polynomial.map_prod]
  refine Finset.prod_dvd_of_coprime (fun a _ b _ h => ?_) fun a _ => ?_
  · simp_rw [Polynomial.map_pow, Polynomial.map_sub, map_C, map_X]
    exact (pairwise_coprime_X_sub_C (IsFractionRing.injective R <| FractionRing R) h).pow
  · exact Polynomial.map_dvd _ (pow_rootMultiplicity_dvd p a hp)

/-- A Galois connection. -/
theorem _root_.Multiset.prod_X_sub_C_dvd_iff_le_roots {p : R[X]} (hp : p ≠ 0) (s : Multiset R) :
    (s.map fun a => X - C a).prod ∣ p ↔ s ≤ p.roots := by
  classical exact
  ⟨fun h =>
    Multiset.le_iff_count.2 fun r => by
      rw [count_roots p hp, le_rootMultiplicity_iff hp, ← Multiset.prod_replicate, ←
        Multiset.map_replicate fun a => X - C a, ← Multiset.filter_eq]
      exact (Multiset.prod_dvd_prod_of_le <| Multiset.map_le_map <| s.filter_le _).trans h,
    fun h =>
    (Multiset.prod_dvd_prod_of_le <| Multiset.map_le_map h).trans p.prod_multiset_X_sub_C_dvd⟩

theorem exists_prod_multiset_X_sub_C_mul (p : R[X]) (hp : p ≠ 0) :
    ∃ q, ∃ hq : q ≠ 0,
      (p.roots.map fun a => X - C a).prod * q = p ∧
        Multiset.card p.roots + q.natDegree = p.natDegree ∧ q.roots = 0 := by
  obtain ⟨q, he⟩ := p.prod_multiset_X_sub_C_dvd (hp := hp)
  have hq : q ≠ 0 := by
    rintro rfl
    rw [mul_zero] at he
    exact hp he
  refine ⟨q, hq, he.symm, ?_, ?_⟩
  · conv_rhs => rw [he]
    rw [(monic_multisetProd_X_sub_C p.roots).natDegree_mul' hq,
      natDegree_multiset_prod_X_sub_C_eq_card]
  · have hprod := mul_ne_zero (monic_multisetProd_X_sub_C (p.roots hp)).ne_zero hq
    have key : p.roots hp = (((p.roots hp).map fun a => X - C a).prod * q).roots hprod := by
      simp only [← he]
    rw [roots_mul hprod, roots_multiset_prod_X_sub_C] at key
    exact add_eq_left.1 key.symm

/-- A polynomial `p` that has as many roots as its degree
can be written `p = p.leadingCoeff * ∏(X - a)`, for `a` in `p.roots`. -/
theorem C_leadingCoeff_mul_prod_multiset_X_sub_C {hp : p ≠ 0}
    (hroots : Multiset.card (p.roots hp) = p.natDegree) :
    C p.leadingCoeff * (p.roots.map fun a => X - C a).prod = p :=
  (eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le (monic_multisetProd_X_sub_C p.roots)
      p.prod_multiset_X_sub_C_dvd
      ((natDegree_multiset_prod_X_sub_C_eq_card _).trans hroots).ge).symm

/-- A monic polynomial `p` that has as many roots as its degree
can be written `p = ∏(X - a)`, for `a` in `p.roots`. -/
theorem prod_multiset_X_sub_C_of_monic_of_roots_card_eq (hp : p.Monic)
    (hroots : Multiset.card p.roots = p.natDegree) : (p.roots.map fun a => X - C a).prod = p := by
  convert! C_leadingCoeff_mul_prod_multiset_X_sub_C hroots
  rw [hp.leadingCoeff, C_1, one_mul]

theorem Monic.isUnit_leadingCoeff_of_dvd {a p : R[X]} (hp : Monic p) (hap : a ∣ p) :
    IsUnit a.leadingCoeff :=
  isUnit_of_dvd_one (by simpa only [hp.leadingCoeff] using leadingCoeff_dvd_leadingCoeff hap)

theorem card_roots_le_one_of_irreducible (hirr : Irreducible p) :
    (p.roots hirr.ne_zero).card ≤ 1 := by
  obtain hp | ⟨x, hx⟩ := (p.roots hirr.ne_zero).empty_or_exists_mem
  · simp [hp]
  convert! p.card_roots' (hp := hirr.ne_zero)
  exact (natDegree_eq_of_degree_eq_some <| degree_eq_one_of_irreducible_of_root hirr <|
    isRoot_of_mem_roots hx).symm

theorem roots_eq_zero_of_irreducible_of_natDegree_ne_one (hirr : Irreducible p)
    (hdeg : p.natDegree ≠ 1) : p.roots hirr.ne_zero = 0 := by
  by_contra hroots
  have ⟨x, hx⟩ := exists_mem_of_ne_zero hroots
  exact hdeg <| natDegree_eq_of_degree_eq_some <|
    degree_eq_one_of_irreducible_of_root hirr ((mem_roots hirr.ne_zero).mp hx)

/-- To check a monic polynomial is irreducible, it suffices to check only for
divisors that have smaller degree.

See also: `Polynomial.Monic.irreducible_iff_natDegree`.
-/
theorem Monic.irreducible_iff_degree_lt (p_monic : Monic p) (p_1 : p ≠ 1) :
    Irreducible p ↔ ∀ q, degree q ≤ ↑(p.natDegree / 2) → q ∣ p → IsUnit q := by
  simp only [p_monic.irreducible_iff_lt_natDegree_lt p_1, Finset.mem_Ioc, and_imp,
    natDegree_pos_iff_degree_pos, natDegree_le_iff_degree_le]
  constructor
  · rintro h q deg_le dvd
    by_contra q_unit
    have := degree_pos_of_not_isUnit_of_dvd_monic p_monic q_unit dvd
    have hu := p_monic.isUnit_leadingCoeff_of_dvd dvd
    refine (h _ (monic_of_isUnit_leadingCoeff_inv_smul hu) ?_ ?_ (dvd_trans ?_ dvd)).elim
    · rwa [degree_smul_of_smul_regular _ (IsSMulRegular.all _)]
    · rwa [degree_smul_of_smul_regular _ (IsSMulRegular.all _)]
    · rw [Units.smul_def, Polynomial.smul_eq_C_mul, (isUnit_C.mpr (Units.isUnit _)).mul_left_dvd]
  · rintro h q _ deg_pos deg_le dvd
    exact deg_pos.ne' <| degree_eq_zero_of_isUnit (h q deg_le dvd)

end CommRing

section

variable {A B : Type*} [CommRing A] [CommRing B]

theorem le_rootMultiplicity_map {p : A[X]} {f : A →+* B} (hmap : map f p ≠ 0) (a : A) :
    rootMultiplicity a p (ne_zero_of_map_ne_zero hmap) ≤ rootMultiplicity (f a) (p.map f) := by
  rw [le_rootMultiplicity_iff hmap]
  refine _root_.trans ?_ (_root_.map_dvd (mapRingHom f)
    (pow_rootMultiplicity_dvd p a (ne_zero_of_map_ne_zero hmap)))
  rw [map_pow, map_sub, coe_mapRingHom, map_X, map_C]

theorem eq_rootMultiplicity_map {p : A[X]} {f : A →+* B} (hf : Function.Injective f)
    {hp : p ≠ 0} (a : A) :
    rootMultiplicity a p =
      rootMultiplicity (f a) (p.map f) ((Polynomial.map_ne_zero_iff hf).2 hp) := by
  apply le_antisymm (le_rootMultiplicity_map ((Polynomial.map_ne_zero_iff hf).mpr hp) a)
  rw [le_rootMultiplicity_iff hp, ← map_dvd_map f hf ((monic_X_sub_C a).pow _),
    Polynomial.map_pow, Polynomial.map_sub, map_X, map_C]
  apply pow_rootMultiplicity_dvd

theorem count_map_roots [IsDomain A] [DecidableEq B] {p : A[X]} {f : A →+* B} (hmap : map f p ≠ 0)
    (b : B) :
    haveI := ne_zero_of_map_ne_zero hmap
    (p.roots.map f).count b ≤ rootMultiplicity b (p.map f) := by
  rw [le_rootMultiplicity_iff hmap, ← Multiset.prod_replicate, ←
    Multiset.map_replicate fun a => X - C a]
  rw [← Multiset.filter_eq]
  refine
    (Multiset.prod_dvd_prod_of_le <| Multiset.map_le_map <| Multiset.filter_le (Eq b) _).trans ?_
  convert! Polynomial.map_dvd f (p.prod_multiset_X_sub_C_dvd (hp := ne_zero_of_map_ne_zero hmap))
  simp only [Polynomial.map_multiset_prod, Multiset.map_map, Function.comp_apply,
    Polynomial.map_sub, map_X, map_C]

theorem count_map_roots_of_injective [IsDomain A] [DecidableEq B] (p : A[X]) {f : A →+* B}
    (hf : Function.Injective f) (hp : p ≠ 0) (b : B) :
    (p.roots.map f).count b ≤ rootMultiplicity b (p.map f) ((Polynomial.map_ne_zero_iff hf).2 hp) :=
  count_map_roots ((Polynomial.map_ne_zero_iff hf).mpr hp) b

theorem map_roots_le [IsDomain A] [IsDomain B] {p : A[X]} {f : A →+* B} (h : p.map f ≠ 0) :
    haveI := ne_zero_of_map_ne_zero h
    p.roots.map f ≤ (p.map f).roots := by
  classical
  exact Multiset.le_iff_count.2 fun b => by
    rw [count_roots _ h]
    apply count_map_roots h

theorem map_roots_le_of_injective [IsDomain A] [IsDomain B] (p : A[X]) {f : A →+* B}
    (hf : Function.Injective f) (hp : p ≠ 0) :
    haveI := (Polynomial.map_ne_zero_iff hf).mpr hp
    p.roots.map f ≤ (p.map f).roots :=
  map_roots_le ((Polynomial.map_ne_zero_iff hf).mpr hp)

theorem card_roots_map_le_degree {A B : Type*} [Semiring A] [CommRing B] [IsDomain B]
    {f : A →+* B} (p : A[X]) (hpm0 : p.map f ≠ 0) : ((p.map f).roots hpm0).card ≤ p.degree :=
  card_roots hpm0 |>.trans degree_map_le

theorem card_roots_map_le_natDegree {A B : Type*} [Semiring A] [CommRing B] [IsDomain B]
    {f : A →+* B} (p : A[X]) {hpm0 : p.map f ≠ 0} : ((p.map f).roots hpm0).card ≤ p.natDegree :=
  card_roots' _ |>.trans natDegree_map_le

theorem ncard_rootSet_le (p : A[X]) (B : Type*) [CommRing B] [IsDomain B] [Algebra A B]
    {hp : p.map (algebraMap A B) ≠ 0} : Set.ncard (p.rootSet B hp) ≤ p.natDegree := by
  classical
  grw [rootSet, Set.ncard_coe_finset, Multiset.toFinset_card_le]
  exact p.card_roots_map_le_natDegree

theorem filter_roots_map_range_eq_map_roots [IsDomain A] [IsDomain B] {f : A →+* B}
    [DecidablePred (· ∈ f.range)] (hf : Function.Injective f) (p : A[X]) (hp : p ≠ 0) :
    haveI := (Polynomial.map_ne_zero_iff hf).2 hp
    (p.map f).roots.filter (· ∈ f.range) = p.roots.map f := by
  classical
  have hpm : p.map f ≠ 0 := (Polynomial.map_ne_zero_iff hf).2 hp
  ext b
  rw [Multiset.count_filter]
  split_ifs with h
  · obtain ⟨a, rfl⟩ := h
    rw [count_roots _ hpm, Multiset.count_map_eq_count' _ _ hf, count_roots _ hp,
      eq_rootMultiplicity_map hf]
  · refine (Multiset.count_eq_zero.mpr fun h' ↦ h ?_).symm
    exact Exists.imp (fun _ ↦ And.right) <| Multiset.mem_map.mp h'

theorem card_roots_le_map [IsDomain A] [IsDomain B] {p : A[X]} {f : A →+* B} (h : p.map f ≠ 0) :
    haveI := ne_zero_of_map_ne_zero h
    Multiset.card p.roots ≤ Multiset.card (p.map f).roots := by
  rw [← (p.roots (ne_zero_of_map_ne_zero h)).card_map f]
  exact Multiset.card_le_card (map_roots_le h)

theorem card_roots_le_map_of_injective [IsDomain A] [IsDomain B] {p : A[X]} {f : A →+* B}
    (hf : Function.Injective f) (hp : p ≠ 0) :
    haveI := (Polynomial.map_ne_zero_iff hf).mpr hp
    Multiset.card p.roots ≤ Multiset.card (p.map f).roots :=
  card_roots_le_map ((Polynomial.map_ne_zero_iff hf).mpr hp)

theorem roots_map_of_injective_of_card_eq_natDegree [IsDomain A] [IsDomain B] {p : A[X]}
    {f : A →+* B} (hf : Function.Injective f) {hp : p ≠ 0}
    (hroots : Multiset.card (p.roots hp) = p.natDegree) :
    haveI := (Polynomial.map_ne_zero_iff hf).mpr hp
    p.roots.map f = (p.map f).roots := by
  apply Multiset.eq_of_le_of_card_le (map_roots_le_of_injective p hf hp)
  simpa only [Multiset.card_map, hroots] using card_roots_map_le_natDegree p

theorem roots_map_of_map_ne_zero_of_card_eq_natDegree [IsDomain A] [IsDomain B] {p : A[X]}
    (f : A →+* B) (h : p.map f ≠ 0)
    (hroots : (p.roots (ne_zero_of_map_ne_zero h)).card = p.natDegree) :
    haveI := ne_zero_of_map_ne_zero h
    p.roots.map f = (p.map f).roots :=
  eq_of_le_of_card_le (map_roots_le h) <| by
    simpa only [Multiset.card_map, hroots] using card_roots_map_le_natDegree p

theorem Monic.roots_map_of_card_eq_natDegree [IsDomain A] [IsDomain B] {p : A[X]} (hm : p.Monic)
    (f : A →+* B) (hroots : p.roots.card = p.natDegree) : p.roots.map f = (p.map f).roots :=
  roots_map_of_map_ne_zero_of_card_eq_natDegree f (map_monic_ne_zero hm) hroots

end

end Polynomial
