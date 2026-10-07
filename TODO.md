# Mathematical fidelity and API hygiene backlog

This file records completed migrations and unresolved audit candidates under the strict-domain,
representation, public-notation, and function-presentation policies in `FORK_DESIGN.md`.  A checked
item records a completed migration or an explicit classification decision.  An unchecked item is
only a hypothesis to investigate: neither its diagnosis nor its proposed replacement is approved
until it passes the fidelity gate below.  Imperative wording in a candidate heading names the
suspected problem; it does not authorize that particular repair.

Mathematical fidelity is not the same as partiality or proof-carrying syntax.  A total operation may
be a genuine extended invariant, an order-theoretic operation, or a choice operator whose input
carries existence evidence, whose theorems prove the specifying property, and whose specification
determines a unique value.  When the specification determines its object only up to an
equivalence, such as almost-everywhere equality, the public object is the equivalence class, not a
chosen representative (`FORK_DESIGN.md`).  A no-witness branch is still a fallback governed by the
transitional-only rule below, unless it occurs only in a private witness for a Prop-valued
existence statement.  Conversely, adding a proof
argument proves only that the chosen hypothesis is sufficient; it does not show that the hypothesis
is the exact mathematical domain.
Even a coherent total operation is not faithful under an ordinary name or notation when that surface
invites a different standard mathematical reading.  Notation, discoverability, theorem duplication,
and tactic transparency are secondary API-quality questions, but names and notation become fidelity
issues when they obscure the represented object or change how a statement is naturally read.

The list is grouped by estimated effort for investigation, prototyping, and any migration that is
later accepted.  Bucket placement is provisional; entries within one bucket are not finely ranked
without a dependency prototype.  Effort does not measure mathematical importance:

- **S**: a bounded declaration or theorem family with an existing strict substrate; normally a few
  files.
- **M**: one coherent subsystem, with statement and consumer migration or a local design decision.
- **L**: a cross-module API with notation, instances, or many downstream consumers; stage the work.
- **XL**: foundational hierarchy or ubiquitous notation; prototype first and migrate in slices.

Before promoting an unchecked candidate to an implementation task:

1. state the intended object by a specifying or universal property, not by the current
   implementation or proposed carrier;
2. determine its exact domain and separate necessary conditions from convenient sufficient
   hypotheses supplied by typeclasses or automation;
3. classify the current total behavior as a genuine total invariant, explicitly sourced convention,
   choice of a unique value, chosen representative of an equivalence class, checked projection, or
   semantically unsupported fallback; a chosen representative is replaced by its class, and a
   fallback does not remain as a permanent public extension; when identifiable mathematical
   literature uses the same total convention for the same inputs and degenerate cases, audit it as
   an independent total mathematical object with its own specifying properties; record the
   bibliographic citation and exact definition, theorem, or page--a more explicit name, source-code
   docstring, or convenient theorem is not enough;
4. test positive, negative, degenerate, characteristic-sensitive, and nonunique examples so that a
   strict facade does not exclude valid mathematics or manufacture canonicity;
5. audit whether the proposed name and notation communicate that exact object without inviting a
   standard but different reading, then choose among a relation, extended-valued invariant,
   canonical value, equivalence class, subtype, proof argument, or explicit partiality type; and
6. prototype real consumers and record the candidate as accepted, reframed, rejected, or still
   unknown before scheduling a migration.

For an accepted strict-partiality migration, preserve a proved bridge on the valid domain and remove
the fallback from the public surface rather than merely renaming it.  A total extension may remain
only as a private transitional implementation helper when the public boundary proves that its
fallback is unreachable or that the result is independent of it.  Record its consumers and removal
condition, and remove it before declaring the migration complete.  A private construction used only
as the witness of a Prop-valued existence statement, to which no public definition unfolds, is not
such a helper and needs no removal condition.  Audit statements that exploit the branch, add
negative tests for the actual boundary, and run the affected downstream checks at the final source
state.

This transitional-only rule is the canonical policy in `FORK_DESIGN.md`.  A literature-supported
total object is reviewed on its own mathematics; it is not a permanent extension of the partial
operation.

## S -- bounded candidates and completed corrections

- [x] **Correct the stale `Measure.map` module overview.**
  The overview now describes pushforward only along an a.e.-measurable map and no longer documents
  an invalid-domain fallback.

- [x] **Replace `parabolicEigenvalue` with a relational eigenvalue API.**
  `Matrix.IsParabolic.eigenvalue_unique` proves over every field that any two eigenvalues are equal,
  without asserting that an eigenvalue exists.  When two is nonzero,
  `hasEigenvalue_trace_div_two` supplies existence and `hasEigenvalue_iff_eq_trace_div_two`
  characterizes the eigenvalue using the standard `HasEigenvalue` predicate.  The former Matrix and
  general-linear-group scalar wrappers have been removed, so split characteristic-two cases can
  supply their own eigenvalue evidence without a trace-based choice being imposed.

- [x] **Represent Dirichlet density by its subsingleton fiber.**
  `HasDirichletDensity S δ` is the ordinary relational API, while `DirichletDensity S` is the
  subtype of certified real values and is a subsingleton by uniqueness of limits.  No zero-default
  or choice-based real-valued projection is retained.  The remaining analytic specification is
  tracked separately under the M candidates.

- [x] **Restrict number-field heights to algebraic inputs and fix their documentation.**
  `NumberField.absMulHeight₁ x hx` and `absLogHeight₁ x hx` require `hx : IsIntegral ℚ x`,
  expressing algebraicity over `ℚ`. The degree-normalized formula is unchanged on that domain,
  and the nonalgebraic fallback is removed. Positivity and zero/one simplification lemmas support
  the logarithmic operation and boundary inputs. Tests cover number-field elements, nonintegral
  rationals, proof independence, and the exclusion of a transcendental rational-function generator.

- [x] **Remove the pole-only branch from `riemannZeta_ne_zero_of_one_le_re`.**
  The theorem now requires `s ≠ 1` and directly specializes Dirichlet L-function nonvanishing
  away from the pole. The zero-set consumer supplies this evidence, and a regression test rejects
  the former invocation using only `1 ≤ s.re`. Strict zeta/L-series evaluation remains separate
  under the L backlog.

- [x] **Put `ArchimedeanClass.stdPart` on finite elements.**
  The canonical ordered ring homomorphism `stdPart : FiniteElement K →+*o ℝ` has no ambient
  extension or fallback. Its kernel consists exactly of infinitesimals; arithmetic and unit
  inversion use the generic homomorphism laws. `IsGLB`/`IsLUB` specify the strict real cuts, with
  `sInf`/`sSup` equalities derived using nonempty witnesses. Hyperreal convergence supplies finite
  inputs, and the infinite-value theorem `stdPart_omega` is removed. Tests cover closure, real
  embeddings, infinitesimals, units, excluded infinite inputs, and cut endpoint behavior.

- [x] **Require `1 < q` for `ArithmeticFunction.ofPowerSeries`.**
  `ofPowerSeries q hq` requires `hq : 1 < q` and is the formal Dirichlet series `f(q⁻ˢ)`: its value
  at `qᵏ` is the `k`-th coefficient of `f`, and it vanishes away from the powers of `q`.  This is
  the exact domain: `k ↦ qᵏ` is injective exactly when `1 < q`, there is no Dirichlet series
  `0⁻ˢ`, and for nontrivial `R` no `R`-algebra map sends `X` to `1⁻ˢ = 1`, because `1 - X` is a
  unit.  The former branch substituted `X ↦ 0` for every `q ≤ 1`, which disagrees with `f(1)` even
  for polynomials; the algebra-hom laws and `ofPowerSeries_apply_one` relied on it.  The
  Euler-product theorem takes `∀ i, 1 < q i` beside `Northcott q`, and prime powers supply the
  evidence through `IsPrimePow.one_lt`.  The only other consumer, the elliptic local Euler factor,
  is migrated by the M item on finite residue fields.  Tests cover the rejected bases, a composite
  base, proof independence, and rewriting.

- [x] **Give `Nat.maxPrimeFac` its actual domain.**
  `Nat.maxPrimeFac n hn` requires `hn : 1 < n` and computes the last element of the nonempty
  prime-factor list without a fallback. `exists_isGreatest_prime_dvd_iff` characterizes this exact
  domain: zero has unbounded prime divisors and one has none. The theorem family uses the same
  domain, with fixed points exactly the primes. Tests cover computation, rejected inputs, and
  rewriting with independently supplied domain proofs.

- [x] **Require nonzero mass for `FiniteMeasure.normalize`.**
  `FiniteMeasure.normalize μ hμ` requires `hμ : μ ≠ 0`, its exact domain: `eq_normalize_iff`
  characterizes the result as the unique probability measure `P` with `μ.mass • P = μ`. The
  arbitrary-Dirac branch and the `[Nonempty Ω]` assumption it needed are removed. The default
  discharger `finite_measure_ne_zero` uses local hypotheses, including ones about all members of a
  family, and `NeZero` instances, and refuses to choose an undetermined measure. Convergence to a
  nonzero limit is characterized along the indices where the finite measures are nonzero, using
  `continuous_normalize` on the nonzero finite measures and continuity of scalar multiplication.
  Tests cover rejected and misleading evidence, ambient instances, proof independence, and a
  portmanteau transfer from probability measures to finite measures.

- [x] **Give `ProbabilityTheory.cdf` its exact domain.**
  `cdf μ` requires `[IsFiniteMeasureOnIic μ]`, finiteness of every ray `Iic x`, and is the
  Stieltjes function `x ↦ μ.real (Iic x)`.  This is exactly the domain on which the formula gives a
  real-valued Stieltjes function generating `μ`; the cdf is then the unique such function with
  limit 0 at -∞ (Siegrist, *Probability, Mathematical Statistics, and Stochastic Processes*,
  §3.9), and `cdf_measure_stieltjesFunction` with `eq_of_cdf` makes `μ ↦ cdf μ` a bijection onto
  the Stieltjes functions with limit 0 at -∞.  When some ray has infinite measure, a locally finite
  measure determines its Stieltjes functions only up to an additive constant; Folland,
  *Real analysis*, 2nd ed., Theorem 1.16, normalizes `F(0) = 0` there.  Finite measures, for which
  Folland, §1.5, calls the function the (cumulative) distribution function, are those with bounded
  cdf.  Infinite measures such as Lebesgue measure on `[0, ∞)` are included, as in Isabelle's
  `cdf_interval_measure` and in Karamata's Tauberian theorem (Bingham--Goldie--Teugels,
  *Regular variation*, Theorem 1.7.1).  The class `IsFiniteMeasureOnIic` is new; finite measures
  supply it automatically, and it is closed under restriction, sums, and `ℝ≥0` multiples.
  On `ℝ`, restrictions of measures that are finite on compact sets to `Ici a` or `Ioi a` supply it
  as well, and the class implies local finiteness, hence σ-finiteness.  The
  former definition applied `condCDF` to the product with a Dirac measure for every measure.  It
  returned the cdf of `(μ univ)⁻¹ • μ` for a finite nonzero measure and still returned a
  probability cdf for a zero or non-finite measure, so `cdf_le_one`, `tendsto_cdf_atTop`, and the
  instance `IsProbabilityMeasure (cdf μ).measure` held for every measure.  The first now assumes
  `IsZeroOrProbabilityMeasure μ` and the other two `IsProbabilityMeasure μ`; statements about the
  total mass assume `IsFiniteMeasure μ`.  The definition no longer depends on `condCDF`.  The
  `SFinite` instances of the gamma, exponential, and Pareto measures, added for the former
  `[SFinite μ]` argument of `cdf` and without other users, are removed.  Tests cover locally
  finite, sigma-finite, s-finite, and infinite-ray exclusions, an infinite measure that is finite
  on rays, finite- and probability-only statements, unnormalized values, proof independence, and
  rewriting.

- [x] **Require primitivity for `DirichletCharacter.rootNumber`.**
  `rootNumber χ hχ` requires `hχ : IsPrimitive χ` and retains the nonzero-modulus hypothesis.
  The functional equation supplies its existing primitivity proof, and the modulus-one root
  number remains one. No unrestricted root-number wrapper is retained. Tests distinguish missing
  primitivity, a nonprimitive character at positive modulus, and primitive modulus zero;
  the operation continues to use the original character and modulus, not an induced character.

## M -- subsystem audit candidates

- [x] **Complete the analytic specification of number-field Dirichlet density.**
  `LSeriesSummable_dedekindZeta` and `summable_absNorm_rpow` establish convergence from the
  existing ideal-counting asymptotic. The prime-ideal series and every subseries converge for
  real `s > 1`, and nonempty sets have positive sums. `HasDirichletDensity.le_one` uses these
  facts instead of a nonsummable-to-zero branch; the full set has density one.
  `dedekindZeta_re_eq_tsum` identifies the norm-counting series with the sum over nonzero ideals.
  Finite prime sieving and dominated convergence prove `log_dedekindZeta_eq_tsum`, the
  logarithmic Euler product. The logarithmic remainder is bounded by twice the prime-ideal
  sum at two. Combined with the positive residue and its pole limit, this proves
  `tendsto_primeIdealZetaSum_div_log` and `hasDirichletDensity_iff_tendsto_div_log`, connecting
  the ratio definition to the standard logarithmic normalization. Finite sets have density
  zero. The relational API and certified-density fiber are preserved, and regression tests
  cover normalization, complement decomposition, finite sets, and independence from values
  outside the right-hand germ. The separate public convergence-domain audit for
  `primeIdealZetaSum` remains explicitly tracked under the XL `tsum`/`tprod` item below; this
  analytic completion does not classify unrestricted evaluation as a strict operation.

- [x] **Make finite multiplicity a checked projection.**
  `multiplicity a b h` in `Mathlib/RingTheory/Multiplicity.lean` takes `h : FiniteMultiplicity a b`
  and is the largest `n` with `a ^ n ∣ b`; `emultiplicity` remains the total invariant in `ℕ∞`.  The
  lemmas that stated the value `0` at infinite multiplicity
  (`multiplicity_eq_zero_of_not_finiteMultiplicity`, `multiplicity_zero`, and
  `emultiplicity_eq_iff_multiplicity_eq_of_ne_zero`, with their aliases) are removed, and
  `multiplicity_add_of_gt`, `multiplicity_sub_of_gt`, `multiplicity_add_eq_min`, and
  `multiplicity_eq_zero_of_coprime` take the finiteness of every multiplicity they mention.  The
  `p`-adic valuations take their domains: `padicValNat p n` and `padicValInt p z` need `p ≠ 1` and a
  nonzero argument, and `padicValRat p q` needs `p ≠ 1` and `q ≠ 0`.  The default discharger
  `padic_val_tac` finds these from hypotheses, linear arithmetic, primality, `NeZero`, and
  `positivity`; other files extend it through `padic_val_core`.  `Nat.maxPowDvdDiv` takes
  `1 < p ∧ n ≠ 0`, and `padicValNat_zero_right`, `padicValNat_one_left`, `padicValInt.zero`, and
  `padicValRat.zero` are removed.  Statements that need a valuation at a possibly zero argument
  quantify over its nonvanishing, as `padicValNat_dvd_iff` does with
  `∀ ha : a ≠ 0, n ≤ padicValNat p a`, and the lemmas of `Mathlib/NumberTheory/Multiplicity.lean`
  state the nonvanishing they derive with `haveI`.  Multiplicities at nonzero ideals of a Dedekind
  domain carry `HeightOneSpectrum.finiteMultiplicity`, and the Frobenius polynomial of
  `Mathlib/RingTheory/WittVector/Frobenius.lean` uses `padicValNat` and needs `p` prime.
  `Nat.divMaxPow` and `padicNorm` stay total: for `p ≤ 1` or `n = 0` every power of `p` dividing `n`
  gives the quotient `n`, the norm of `0` is `0`, and for `p = 1` every power of `p` is `1`.
  `Nat.factorization` keeps its value `0` at `0` (entry "Put finite factorization data on nonzero
  inputs") and no longer inherits it from the valuation.  Tests cover the removed names, the
  discharger, and the failures at `0` and at `p = 1`.

- [x] **Make the additive `p`-adic valuations on `ℚ_[p]` and `ℤ_[p]` domain-bearing.**
  `Padic.valuation x hx` in `Mathlib/NumberTheory/Padics/PadicNumbers.lean` and
  `PadicInt.valuation x hx` in `Mathlib/NumberTheory/Padics/PadicIntegers.lean` take `hx : x ≠ 0`,
  which `padic_val_tac` supplies by default, and `PadicSeq.valuation f hf` takes `hf : ¬f ≈ 0`.  The
  valuation of `0` is `⊤`: `Padic.addValuationDef`, with values in `WithTop ℤ`, is now defined on
  the quotient itself, `Padic.addValuation` bundles it, and `Padic.valuation` is its integer value
  at a nonzero element.  `Padic.valuation_zero` and `PadicInt.valuation_zero` are removed;
  `le_valuation_add`, `valuation_inv`, `valuation_pow`, `valuation_zpow`,
  `norm_le_one_iff_val_nonneg`, and `PadicInt.valuation_coe_nonneg`, which held at `0` only through
  the value `0`, take nonzero arguments, and `PadicInt.valuation_natCast` is new.  `padic_val_tac`
  gains rules for casts of nonzero elements, products, powers, integer powers, and inverses.
  `Padic.mulValuation` keeps its value `0` at `0`, the zero of `ℤᵐ⁰`, as every valuation does.  The
  consumers are `PadicInt.unitCoeff`, the discrete valuation ring and fraction field structures of
  `ℤ_[p]`, `PadicInt.appr`, the Mahler basis, and the divided powers of `ℤ_[p]`.  Tests are in
  `MathlibTest/PadicValuationStrict.lean`.

- [x] **Require monicity for polynomial division-by-monic notation.**
  `Polynomial.divByMonic` and `Polynomial.modByMonic` in `Mathlib/Algebra/Polynomial/Div.lean` take
  `hq : q.Monic`, reusing `divModByMonicAux`, so `p /ₘ q` and `p %ₘ q` have no value at a divisor
  that is not monic; unexpanders keep printing them as notation without the proof.  The extensible
  default discharger `monic_tac` finds the proof from a hypothesis, for `X`, `1`, `X - C a`, and
  `X + C a`, and for products, powers, images under `Polynomial.map`, and finite products of
  polynomials that it proves monic; its rules unify only at reducible and instance transparency, so
  that it fails fast on concrete polynomials, and it never assigns an undetermined divisor.  Later
  files add `monic_core` rules for the minimal polynomial of an integral element, characteristic
  polynomials, cyclotomic polynomials, the polynomial of an `IsAdjoinRootMonic` presentation, and
  `q * C (leadingCoeff q)⁻¹` for `q ≠ 0` over a field.  `divByMonic_eq_of_not_monic`,
  `modByMonic_eq_of_not_monic`, `divByMonic_zero`, and `modByMonic_zero` are removed, and the lemmas
  that held for every divisor through those values take its monicity, as explicit hypotheses
  (`modByMonic_add_div`, `modByMonic_eq_sub_mul_div`, `degree_divByMonic_le`,
  `degree_modByMonic_le_left`) or as implicit ones where it occurs on the left-hand side.
  `minpoly.aeval_modByMonic_minpoly` takes the monicity of the minimal polynomial as such an
  implicit hypothesis, so that it stays a simp lemma.  The polynomial division and remainder over a
  field in `Mathlib/Algebra/Polynomial/FieldDivision.lean` state `p / 0 = 0` and `p % 0 = p`
  explicitly, as the `EuclideanDomain` interface requires (see "Classify inverse and division
  semantics"), and `div_def` and `mod_def` take `q ≠ 0`.  Tests cover the removed names, the
  printing, every discharger rule, the field values at `0`, and the failures for a divisor that is
  not monic, for a hypothesis about another concrete polynomial, and for an undetermined divisor.

- [x] **Give `Polynomial.rootMultiplicity` its domain.**
  `rootMultiplicity a p hp` in `Mathlib/Algebra/Polynomial/Div.lean` takes `hp : p ≠ 0` and is
  `multiplicity (X - C a) p` for the finiteness given by `finiteMultiplicity_X_sub_C`.  Every power
  of `X - C a` divides `0`, so the zero polynomial has no largest one; `emultiplicity (X - C a) p`
  is the total invariant, `⊤` at `0` and `rootMultiplicity a p` otherwise
  (`emultiplicity_X_sub_C_eq_rootMultiplicity`).  The extensible default discharger `nonzero_tac`
  finds the proof from a hypothesis, through `monic_core` for polynomials over a nontrivial ring,
  and for products and powers over a ring without zero divisors; its rules unify only at reducible
  and instance transparency, and it never assigns an undetermined polynomial.
  `rootMultiplicity_zero` and `rootMultiplicity_pos'` are removed, `rootMultiplicity_eq_zero_iff`
  states `rootMultiplicity x p = 0 ↔ ¬IsRoot p x`, and `rootMultiplicity_pos` is a simp lemma.  The
  lemmas that held through the value at `0` take `p ≠ 0` or the nonvanishing of a derivative, an
  evaluation, a composition, an image, or a Hilbert polynomial, from which
  `ne_zero_of_derivative_ne_zero`, `ne_zero_of_eval_ne_zero`, `ne_zero_of_comp_ne_zero`,
  `ne_zero_of_map_ne_zero`, and `ne_zero_of_hilbertPoly_ne_zero` recover `p ≠ 0`.  The derivative of
  a nonzero polynomial with a root whose multiplicity is a non-zero-divisor is nonzero
  (`derivative_ne_zero_of_root_of_mem_nonZeroDivisors`, `derivative_ne_zero_of_root`), and the
  formulas for its multiplicity there use that proof.
  `rootMultiplicity_sub_one_le_derivative_rootMultiplicity` is removed in favor of its `_of_ne_zero`
  form, which needs only a nonzero derivative, and the stale `docPrime` exception for
  `rootMultiplicity_pos'` is removed.  `count_roots` takes `p ≠ 0` (see "Exclude the zero polynomial
  from finite root multisets"), and `Polynomial.derivRootWeight` uses the multiplicity only where
  `P` does not vanish at `z`, hence `P ≠ 0`.  Tests cover the removed names, the discharger with its
  transparency and its failure over a ring with zero divisors, the simp lemma, the infinite
  multiplicity at `0`, and the failures.

- [x] **Exclude the zero polynomial from finite root multisets.**
  `Polynomial.roots p hp` in `Mathlib/Algebra/Polynomial/Roots.lean` takes `hp : p ≠ 0`, which
  `nonzero_tac` supplies by default.  `aroots p S hp` and `rootSet p S hp` take
  `hp : p.map (algebraMap T S) ≠ 0`, `nthRoots n a h` and `nthRootsFinset n a h` take
  `h : X ^ n - C a ≠ 0`, and `Cubic.roots` takes `P.toPoly ≠ 0`.  Every element is a root of the
  zero polynomial, whose zero locus `{x | IsRoot 0 x}` is the whole ring, so it has no finite root
  multiset.  `roots_zero`, `aroots_zero`, `rootSet_zero`, `mem_roots'`, `mem_aroots'`,
  `mem_rootSet'`, `mem_rootSet_of_ne`, `mem_roots_sub_C'`, `ne_zero_of_mem_roots`,
  `ne_zero_of_mem_rootSet`, `roots_list_prod`, `roots_multiset_prod`,
  `roots_eq_zero_iff_eq_zero_or_isRoot_eq_bot`, and `rightInverse_ofMultiset_roots` are removed;
  `mem_roots` (a simp lemma again), `mem_aroots`, and `mem_rootSet` state the root condition alone,
  and `roots_prod` sums over the nonzero factors.  `nonzero_tac` gains rules for a hypothesis of
  positive degree or irreducibility, a `NeZero p` instance, images under maps out of a field,
  `X ^ n - C a` with `n ≠ 0`, `p - C a` with `0 < degree p`, separable, expanded, quadratic, and
  cubic polynomials, and minimal polynomials in integral extensions, of power-basis generators, and
  of conjugacy classes.  Statements that read the empty value at `0` take the domain or a hypothesis
  that implies it, among them Vieta's formulas, `Splits.eq_prod_roots` and its relatives, the
  resultant as a product over roots, the Rolle bounds on the roots of a derivative (which need
  `derivative p ≠ 0`), the Mahler measure as a product over roots, the norm and trace of a generator
  as a product and a sum over roots (which need integrality), and the Morse permutation results.
  `Polynomial.IsSplittingField` keeps its semantics, the smallest field extension over which `f`
  splits: its generation field takes `f ≠ 0`, and a new field states that the splitting field of `0`
  is the base field, as minimality gives; `IsNormalClosure` adjoins the roots of the minimal
  polynomials of the integral elements, which is what the empty root set of `minpoly F x = 0`
  expressed.  The action of `Polynomial.Gal p` on roots takes `[NeZero p]`, alongside its splitting
  hypothesis, and `Gal.ext` quantifies over `p ≠ 0`, so that it still covers the trivial group
  `Gal 0`.  `natSepDegree` and `primitiveRoots` keep their values at `0` by explicit conventions,
  recorded below.  Tests are in `MathlibTest/RootsStrict.lean`.

- [x] **Decide the separable degree of the zero polynomial.**
  `Polynomial.natSepDegree f hf` in `Mathlib/FieldTheory/SeparableDegree.lean` takes `hf : f ≠ 0`,
  which `nonzero_tac` supplies by default.  It counts the distinct roots of `f` in its splitting
  field, and the zero polynomial has no finite set of roots and no separable contraction, so its
  former value `0` was a convention, not a count.  `natSepDegree_zero` and `natSepDegree_of_ne_zero`
  are removed: `natSepDegree_def` unfolds the count, and `natSepDegree_congr` rewrites the
  polynomial together with its proof.  `natSepDegree_le_natDegree`, `natSepDegree_eq_zero_iff`,
  `natSepDegree_mul`, `natSepDegree_pow`, `natSepDegree_expand`, `natSepDegree_map`, and
  `natSepDegree_C` take nonzero polynomials, `natSepDegree_mul_eq_iff` loses its disjunct
  `f = 0 ∧ g = 0`, and the separable contraction lemmas derive the nonvanishing
  (`IsSeparableContraction.ne_zero`).  The characterizations through minimal polynomials, such as
  `minpoly.natSepDegree_eq_one_iff_pow_mem`, `isPurelyInseparable_iff_natSepDegree_eq_one`, and
  `mem_perfectClosure_iff_natSepDegree_eq_one`, state
  `∃ hx : IsIntegral F x, (minpoly F x).natSepDegree (minpoly.ne_zero hx) = 1`, which the former
  value `0` at a nonintegral element expressed, and `perfectField_iff_splits_of_natSepDegree_eq_one`
  quantifies over nonzero polynomials.  Tests are in `MathlibTest/NatSepDegreeStrict.lean`.

- [ ] **Give `primitiveRoots` and the modified cyclotomic polynomial the domain `n ≠ 0`.**
  `primitiveRoots k R` in `Mathlib/RingTheory/RootsOfUnity/PrimitiveRoots.lean` is `∅` at `k = 0`
  (`primitiveRoots_zero`), now by an explicit case of the definition rather than through the empty
  root multiset of the zero polynomial, and `IsPrimitiveRoot.card_primitiveRoots` holds there as
  `#∅ = φ 0`.  `IsPrimitiveRoot ζ 0` holds exactly for the `ζ` none of whose positive powers is `1`,
  which form no finite set in general (in `ℚ`, every element except `1` and `-1`), so `∅` is not the
  set of primitive `0`-th roots of unity.  Require `NeZero k` and propagate the domain to
  `Polynomial.cyclotomic'`, the product of `X - C μ` over `primitiveRoots n R`, which is `1` at
  `n = 0` (`cyclotomic'_zero`), and decide whether `Polynomial.cyclotomic 0 R = 1`
  (`cyclotomic_zero`) is justified independently.

- [x] **Identify `Polynomial.natDegree` as the supremum of the support.**
  `natDegree p` is the supremum in `ℕ` of the exponents with nonzero coefficient
  (`natDegree_eq_support_sup`, from `supDegree_eq_natDegree`), for every `p`: the degree of a
  nonzero polynomial, and `0`, the supremum of the empty set, which in `ℕ` is its least element, for
  `p = 0`.  The degree of the zero polynomial is conventionally `-∞` or left undefined, and
  `degree 0 = ⊥` keeps that convention; the zero value of `natDegree` is therefore justified as the
  supremum, as for `Nat.findGreatest`, not as a degree.  The audit of the theorem statements
  supports this reading: the lattice-type statements that hold at `0` without a hypothesis
  (`natDegree_le_iff_coeff_eq_zero`, the bounds `natDegree_add_le`, `natDegree_mul_le`,
  `natDegree_pow_le`, and `natDegree_comp_le`, the values `natDegree_C` and `natDegree_monomial`)
  are statements about the supremum of the support, the statements that need `p ≠ 0` (strict upper
  bounds, `natDegree_mul`, `natDegree_mul_X`, attainment, and `natDegree_lt_iff_degree_lt`) are
  exactly those where a supremum of an empty set behaves differently, and
  `MvPolynomial.totalDegree`, `MvPolynomial.degreeOf`, and `MonomialOrder.degree` are defined as
  suprema of supports in the same way.  Requiring `p ≠ 0` would add hypotheses to about 500
  statements without visible zero guards, including lattice statements that are true at `0`.  The
  docstrings of `natDegree` and of `Mathlib/Algebra/Polynomial/Degree/Defs.lean` now describe the
  supremum.  `natTrailingDegree`, whose value `0` at `0` is not an infimum, and the statements that
  read `natDegree` as a degree at `0` are recorded below.

- [x] **Give `Polynomial.natTrailingDegree` its domain.**
  `natTrailingDegree p hp` in `Mathlib/Algebra/Polynomial/Degree/TrailingDegree.lean` takes
  `hp : p ≠ 0`, which `assumption` supplies by default, and `trailingDegree` stays the total
  invariant in `ℕ∞`, with `trailingDegree 0 = ⊤`.  `natTrailingDegree_zero`,
  `trailingDegree_eq_iff_natTrailingDegree_eq_of_pos`, and the equivalence
  `coeff_natTrailingDegree_eq_zero` are removed, and `natTrailingDegree_eq_zero` and
  `natTrailingDegree_ne_zero` no longer carry the disjunct `p = 0`.  `trailingCoeff`, `nextCoeffUp`,
  and `Polynomial.mirror` stay total with value `0` at `0`, where every coefficient is `0`;
  `trailingCoeff_of_ne_zero`, `nextCoeffUp_of_ne_zero`, and `mirror_of_ne_zero` unfold them.
  `nextCoeffUp p` is the coefficient of `X ^ (natTrailingDegree p + 1)` for every nonzero `p`: its
  former guard `natTrailingDegree p = 0`, which mirrored the guard of `nextCoeff` for constants,
  also gave `0` for nonconstant polynomials with a nonzero constant coefficient, such as `1 + X`.
  `LinearMap.nilRank`, `LinearMap.IsNilRegular`, `LieModule.rank`, and `LieModule.IsRegular` require
  a nontrivial base ring, as their docstrings already assumed, since the characteristic polynomial
  over the zero ring is `0`.  `rootMultiplicity_eq_natTrailingDegree` takes `p ≠ 0` (see "Give
  `Polynomial.rootMultiplicity` its domain"), and `isUnitTrinomial_iff'` states that `p * p.mirror`
  is nonzero.  Tests cover the removed name, the default proof, and the total invariants at `0`.

- [x] **Audit constructions that feed `natDegree` of a possibly zero polynomial into a formula.**
  `Polynomial.discr f hf` in `Mathlib/RingTheory/Polynomial/Resultant/Basic.lean` takes
  `hf : 0 < f.natDegree`.  For `f` of degree `n` with leading coefficient `a`, the discriminant is
  `a ^ (2 * n - 2)` times the product of the squared differences of the roots, which for `n = 0`
  would be `a⁻¹ ^ 2`; the Wikipedia article "Discriminant" (section "Low degrees") records no common
  convention for a constant polynomial, while the discriminant of a linear polynomial is commonly
  `1` (`discr_of_degree_eq_one`).  `discr_C`, which gave `1` for every constant including `0`, is
  removed.  `Matrix.discr` is `1` when the characteristic polynomial is constant: for a `0 × 0`
  matrix this is the empty product of the squared differences of the eigenvalues, the discriminant
  of the monic polynomial `1`, and over the zero ring `1 = 0`.  `RatFunc.intDegree x hx` in
  `Mathlib/FieldTheory/RatFunc/Degree.lean` takes `hx : x ≠ 0`: the zero rational function has
  degree `⊥`, as the zero polynomial does, not `0`.  `intDegree_zero` is removed, `intDegree_C` and
  `intDegree_polynomial` take the nonvanishing of the constant and of the polynomial, the lemmas
  that held at `0` through the value `0` (`intDegree_inv`, `intDegree_neg`, and `intDegree_add_le`)
  take nonzero arguments, and the valuation at infinity passes its case `r ≠ 0` to `intDegree`.  The
  other constructions keep their values at `0`, which do not depend on the degree they use:
  `reverse`, `eraseLead`, `scaleRoots`, `integralNormalization`, and `homogenize p n` are `0` at
  `0`, since every coefficient of `0` vanishes, and `mirror` is `0` by an explicit case.
  `nextCoeff p` is the coefficient one below the leading one, `0` for a constant, where that index
  would be negative.  The default degrees of `Polynomial.resultant` are formal degrees, with which
  the resultant of the constant `0` and `g` is `0 ^ n` (`resultant_zero_left_deg`), as for any
  constant, and `resultant_self` is stated with them.  `natDegree_derivative_le` and the other
  statements with natural subtraction are statements about the supremum of the support, which hold
  at `0`.  Tests are in `MathlibTest/IntDegreeDiscrStrict.lean`.

- [x] **Make scheme order of vanishing carry its point and function domains.**
  `AlgebraicGeometry.Scheme.ord f z hz` takes `hz : coheight z = 1`, the condition that `ordHom`
  already required, and takes values in `WithTop ℤ`: as for a discrete valuation, the order of `0`
  is `⊤`, and every nonzero rational function has an integer order (`ord_eq_top_iff`,
  `ord_eq_iff`).  The former integer-valued definition returned `0` for the zero rational function
  and at every point that is not of codimension one: `ord_zero` stated `ord 0 = 0` and now gives
  `⊤`, and `ord_eq_zero_of_coheight_neq_one`, which exposed the point fallback, is removed with
  `ord_eq_ordHom_of_coheight_eq_one`, which unfolded the former definition.  With `⊤` for zero,
  `ord_mul`, `ord_add`, and `ord_le_smul` hold without nonvanishing hypotheses, while the
  comparisons with `ordHom` keep them.  The module has no
  consumers.  Tests cover the removed lemma, the missing point condition, the order of zero, and
  multiplicativity.

- [x] **Unify strict nilpotency invariants.**
  The nilpotency invariants take nilpotency evidence: `nilpotencyClass x hx` takes
  `hx : IsNilpotent x`, `Group.nilpotencyClass G` takes `[Group.IsNilpotent G]`, and
  `LieModule.nilpotencyLength L M` and `lowerCentralSeriesLast R L M` take
  `[LieModule.IsNilpotent L M]`.  Each is the least index at which the powers, the upper central
  series, or the lower central series reach their limit, which exists exactly for a nilpotent
  object; an extended natural invariant with value `⊤` for a nonnilpotent object is not adopted,
  since every consumer works with nilpotent objects.  The former definitions returned `0` for a
  nonnilpotent object (`isNilpotent_of_pos_nilpotencyClass`, `pos_nilpotencyClass_iff`, and
  `Group.nilpotencyClass_of_not_nilpotent`, removed; `pos_nilpotencyClass` gives the positivity),
  so that `IsNilpotent.exp (1 : ℚ)` was `0`.  `IsNilpotent.exp a ha` takes the nilpotency of `a`,
  and its lemmas, the exponential of a nilpotent Lie derivation, and the group lemmas that split on
  nilpotency (`nilpotencyClass_quotient_center`, `nilpotencyClass_le_of_upperCentralSeries_eq`,
  and `upperCentralSeries.StrictMonoOn`) take it.  Tests cover the removed names, the
  exponential of a nonnilpotent element, the class of a nonnilpotent group, and the zero element.

- [x] **Require injectivity for `LinearMap.leftInverse`.**
  `LinearMap.leftInverse f hf` chooses a linear left inverse using `hf : Function.Injective f`,
  with no noninjective fallback. `exists_leftInverse_iff_injective` characterizes this exact domain
  over a division ring, including subsingleton domains. The composition and application laws take
  the same evidence; the choice is not asserted to be unique away from the range. Subspace
  complements, dual extensions, Maschke's theorem, and continuous inverses supply their existing
  injectivity proofs. Tests cover missing and invalid evidence, zero-dimensional domains,
  nonsurjective inclusions, proof independence, rewriting, and nonuniqueness of left inverses.

- [x] **Replace the chosen left inverse of `LinearMap.leftInverse` by canonical data.**
  The chosen left inverse `LinearMap.leftInverse` and its lemmas `leftInverse_comp` and
  `leftInverse_apply` are removed.  The left inverses of an injective `f` are exposed as a relation
  with an existence statement, `exists_leftInverse_of_injective`, and as the object determined by
  its specification: `LinearMap.linearProjOfIsCompl q f hf h`, the projection along a complement
  `q` of the range, is the unique left inverse vanishing on `q` (`eq_linearProjOfIsCompl`), and
  every left inverse is the projection along its kernel (`isCompl_range_ker_of_comp_eq_id` and
  `eq_linearProjOfIsCompl_ker`), so the left inverses correspond to the complements of the range.
  `Subspace.dualLift W q h` extends a functional by zero on a complement `q` of `W`, and
  `dualEquivDual`, `quotDualEquivAnnihilator`, and `dualQuotDistrib` take the complement;
  `Subspace.quotEquivAnnihilator`, an isomorphism built from chosen bases, is removed, and
  `finrank_add_finrank_dualAnnihilator_eq` follows from `dualQuotEquivDualAnnihilator`.
  `leftInverseOfInjectiveOfIsClosedRange` is the inverse of `equivRange`, the unique left inverse
  on the range, and Maschke's theorem and the subspace complements obtain a left inverse from the
  existence statement.  Tests cover the removed names, the existence and characterization of left
  inverses, two left inverses with distinct kernels, and the dual lift.

- [x] **Replace chosen continuous one-sided inverses and complements by canonical data.**
  `ContinuousLinearMap.HasLeftInverse.leftInverse`, `HasRightInverse.rightInverse`,
  `HasLeftInverse.complement`, `Submodule.ClosedComplemented.complement`, and
  `ContinuousLinearMap.antilipschitzConstantOfInjectiveOfIsClosedRange` were `Classical.choose`
  representatives of existence statements; they are removed with their specifications
  (`leftInverse_leftInverse`, `rightInverse_rightInverse`,
  `ContinuousLinearEquiv.leftInverse_hasLeftInverse`,
  `ContinuousLinearEquiv.rightInverse_hasRightInverse`, `isClosed_complement`, `isCompl_complement`,
  `isTopCompl_complement`, and `antilipschitz_antilipschitzConstantOfInjectiveOfIsClosedRange`).  A
  continuous left inverse of `f` is determined only on the range of `f` and a continuous right
  inverse only up to its kernel, so the canonical data take a topological complement.
  `HasLeftInverse.leftInverseOfIsTopCompl` is the continuous left inverse vanishing on a topological
  complement of the range: the left inverse `LinearMap.linearProjOfIsCompl` of the underlying linear
  map, which is continuous because it factors through any continuous left inverse and the continuous
  projection.  `HasRightInverse.rightInverseOfIsTopCompl` is the continuous right inverse with
  values in a topological complement of the kernel: the inverse of the restriction of `f`, which is
  the projection of any continuous right inverse along the kernel.  Each is the only one-sided
  inverse with that property (`eq_leftInverseOfIsTopCompl`, `eq_rightInverseOfIsTopCompl`), and
  every continuous left inverse is the one attached to its kernel and every continuous right inverse
  the one attached to its range (`eq_leftInverseOfIsTopCompl_ker`,
  `eq_rightInverseOfIsTopCompl_range`).  The anti-Lipschitz constant of an injective operator with
  closed range between Banach spaces is the norm of its inverse on the range
  (`antilipschitz_leftInverseOfInjectiveOfIsClosedRange`), which is the least such constant
  (`nnnorm_leftInverseOfInjectiveOfIsClosedRange_le`).

- [x] **Replace chosen witnesses of local presentations and immersions by explicit data.**
  `LiftSourceTargetPropertyAt.localPresentationAt`, `domChart`, `codChart`, and their lemmas in
  `Mathlib/Geometry/Manifold/LocalSourceTargetProperty.lean` are removed: a proof obtains a
  `LocalPresentationAt`, whose charts are data, from the existence statement
  `LiftSourceTargetPropertyAt`.  Likewise the chosen charts and equivalences of
  `IsImmersionAtOfComplement` and `IsSubmersionAtOfComplement` (`domChart`, `codChart`, `equiv`, and
  `writtenInCharts`) and the chosen complements `IsImmersionAt.complement`,
  `IsImmersion.complement`, `IsSubmersionAt.complement`, and `IsSubmersion.complement`, with their
  instances and charts, are removed from `Mathlib/Geometry/Manifold/Immersion.lean` and
  `Mathlib/Geometry/Manifold/Submersion.lean`; the proofs obtain the complement, the charts, and the
  equivalence.  The statements about the charts of a presentation take the charts and the
  equivalence explicitly: `map_target_subset_target`, `target_subset_preimage_target`,
  `image_target_subset_target`, `continuousOn_of_eqOn`, and `contMDiffOn_of_eqOn` replace the
  versions stated with the chosen charts, among them `continuousOn` and `contMDiffOn`.
  `smallComplement`, which shrinks a given complement `F` into the universe of the model space,
  stays, since it depends only on `F`.  Tests are in `MathlibTest/ManifoldPresentationStrict.lean`.

- [x] **Bundle admissible root pairs for root-chain data.**
  `RootPairing.chainTopCoeff i j` and `chainBotCoeff i j` are the largest natural numbers `p` and
  `q` such that `β + p • α` and `β - q • α` are roots, for `α = P.root i` and `β = P.root j`.  Only
  finitely many roots lie on the line through `β` in the direction of `α`
  (`finite_setOfPred_root_add_zsmul_mem`), so this extremal specification determines a value for
  every pair of roots, and linear independence, which the item proposed to bundle, is not the
  domain.  For linearly independent roots these are the ends of the unbroken `α`-chain through `β`
  (`root_add_zsmul_mem_range_iff`), and independence remains a hypothesis only of the interval
  statements.  The former definitions chose the ends of that chain under independence and returned
  `0` otherwise, and `chainTopIdx` and `chainBotIdx` returned `j`: for every root, `α - 2 • α = -α`
  is a root, but `chainBotCoeff i i` was `0`.  The lemmas stating these values,
  `chainTopCoeff_of_not_linearIndependent` and `chainBotCoeff_of_not_linearIndependent`, are
  removed.  `chainBotCoeff_sub_chainTopCoeff`, which gives `q - p = ⟨β, α^∨⟩` through the
  reflection in `α`, `chainBotCoeff_of_add`, `chainTopCoeff_of_sub`, `chainTopCoeff_of_add`, the
  integer characterizations `coe_chainTopCoeff_eq_sSup` and `coe_chainBotCoeff_eq_sSup`, and
  `chainBotCoeff_add_chainTopCoeff_eq_pairingIn_chainTopIdx` no longer assume independence, and
  `one_le_chainTopCoeff_of_root_add_mem` and `one_le_chainBotCoeff_of_root_add_mem` no longer assume
  a reduced pairing.  `chainTopIdx` and `chainBotIdx` are the indices of the roots `β + p • α` and
  `β - q • α`, unique since `P.root` is injective.  `chainBotCoeff_eq_zero_iff` and
  `chainTopCoeff_eq_zero_iff` take the independence under which `q = 0` and `p = 0` mean that
  `β - α` and `β + α` are not roots, and `Base.chainBotCoeff_eq_zero` takes `i ≠ j`.  Several Geck
  construction lemmas lost hypotheses that only the former definitions used.  Tests cover the
  removed names, a root and itself, the reflection identity, the unbroken chain, and the top of the
  chain.

- [x] **Require a nonzero direction for Lie-algebra root chains.**
  `LieModule.chainTopCoeff α β hα` and `chainBotCoeff` take `hα : α ≠ 0`: the largest `n` such that
  `i • α + β` is a weight for every `i ≤ n` exists only in a nonzero direction, since for `α = 0`
  every `n` has this property.  `chainTop` and `chainBot` take the same hypothesis, and
  `LieAlgebra.IsKilling.chainLength α β hα` takes a nonzero root `hα : α.IsNonZero`, which
  `Weight.IsNonZero.coe_ne_zero` states as a nonzero function for the chain functions.  The former
  definitions returned `0` for `α = 0` (`chainTopCoeff_zero`, `chainBotCoeff_zero`,
  `chainTop_zero`, `chainBot_zero`, `chainLength_of_isZero`, and `chainLength_zero`, removed), and
  the lemmas of the root-system construction that split on `α.IsZero`, such as
  `chainLength_nsmul`, `apply_coroot_eq_cast`, and `chainBotCoeff_add_chainTopCoeff`, take a nonzero
  root.  Tests cover the removed names, the missing hypothesis, the end of a chain, and the chain
  length and coroot pairing.

- [x] **Require `ExcenterExists` for excenter geometry.**
  `Affine.Simplex.exsphere`, `excenter`, `exradius`, and `touchpoint` take
  `h : s.ExcenterExists signs`, as do the barycentric coordinates `excenterWeights` and
  `touchpointWeights`.  This is the exact domain:
  `exists_forall_signedInfDist_eq_iff_excenterExists_and_eq_excenter` shows that a point of the
  affine span has signed distances to the faces with the signs `signs` and a common absolute value
  exactly when the excenter exists and the point is the excenter, and the exsphere is the sphere
  about it that is tangent to the faces.  The former definitions applied the normalized weights
  `(∑ i, w i)⁻¹ • w` for every `signs`.  When the sum vanishes they are zero, the affine combination
  with zero weights is the point `Classical.choice` that `Finset.affineCombination` uses as its
  base, and the radius `|0⁻¹|` is zero, so a nonexistent excenter was an arbitrary point with an
  exsphere of radius zero; `sum_excenterWeights` and `sum_excenterWeights_eq_one_iff`
  characterized existence through the zero weights and are removed, while
  `ExcenterExists.sum_excenterWeights_eq_one` remains.  The default discharger `excenter_exists`
  supplies the proof from a local hypothesis, for the insphere, for triangles
  (`Affine.Triangle.excenterExists`), and for the exsphere opposite a vertex in two or more
  dimensions, also for complements, so most statements keep their form; it never assigns the
  simplex or the indices.  `not_excenterExists_singleton` records that a segment has no excenter
  opposite an endpoint, so that case genuinely needs two dimensions.  Lemmas that held for every
  `signs` only through the fallback, such as `exradius_nonneg` and the membership of touchpoints in
  the faces, take the hypothesis; the `_map`, `_restrict`, `_reindex`, and `_compl` lemmas transfer
  it, and the existence characterizations conclude `∃ h, p = s.excenter signs h`.  Tests cover the
  removed lemmas, the segment, the failure of the discharger for general indices in three
  dimensions, the explicit proof for the weights, routine evidence, proof independence,
  complements, and the existence characterization.

- [x] **Make Newton iteration preserve derivative invertibility.**
  `Polynomial.newtonMap P x h` takes `h : IsUnit (aeval x (derivative P))` and is
  `x - h.unit⁻¹ * aeval x P`.  Over a field this is exactly where the Newton step
  `x ↦ x - P(x) / P'(x)` is defined.  In a ring with nonunits the quotient can also exist at a
  nonunit, as for `P = 2 * X` over `ℤ` at `1`, but no consumer steps there, so the definition takes
  the unit.  The former definition multiplied by `Ring.inverse`, which is zero at a non-unit, so it
  returned `x` there: at `0` the derivative of `X ^ 2 + 1` over `ℚ` vanishes, and `0` was a fixed
  point of Newton's map without being a root.  `newtonMap_apply_of_not_isUnit` is removed,
  `newtonMap_apply_of_isUnit` became the definition, and the fixed-point lemmas
  `newtonMap_eq_self_of_aeval_eq_zero` and `newtonMap_eq_self_iff` replace
  `isFixedPt_newtonMap_of_aeval_eq_zero` and `isFixedPt_newtonMap_of_isUnit_iff`.  A unit
  derivative need not survive a step: the step of `X ^ 2 + 1` over `ℚ` from `1` reaches `0`.  It
  does when `P(x)` is nilpotent, since the step changes `x` by a nilpotent element
  (`isNilpotent_newtonMap_sub`) and `P(x) ^ 2` divides the new value of `P`
  (`aeval_sq_dvd_aeval_newtonMap`).  Newton iteration therefore runs on
  `Polynomial.NewtonDomain P S`, the points where `P` is nilpotent and `P'` a unit, through the
  self-map `NewtonDomain.step`; over a field these are the simple roots of `P`.  The iteration
  lemmas, renamed `NewtonDomain.isNilpotent_iterate_step_sub` and
  `NewtonDomain.aeval_pow_two_pow_dvd_aeval_iterate_step`, are stated there, and
  `existsUnique_nilpotent_sub_and_aeval_eq_zero`, used by the Jordan-Chevalley decomposition, keeps
  its statement.  Iteration with explicit failure outside such an invariant set has no consumer and
  is not provided.  Tests cover the removed names, the spurious fixed point, computed steps,
  including one that leaves the units, the fixed-point characterization, and iteration on the
  domain.

- [x] **Put `Function.minimalPeriod` and `Function.periodicOrbit` on periodic points.**
  A point that never returns has no least positive period, so it has no minimal period, and its
  orbit is not a cycle; the minimal period of a periodic point is its least positive period.
  `Function.minimalPeriod f x hx` and `Function.periodicOrbit f x hx` take `hx : x ∈ periodicPts f`,
  found by the default discharger `periodic_pt` from a local hypothesis or from a periodic point of
  positive period, which never chooses the map or the point.  The periods of a periodic point are
  the multiples of its minimal period (`isPeriodicPt_iff_minimalPeriod_dvd`), and
  `minimalPeriod_eq_iff` characterizes it.  The statements of the former convention are removed:
  `minimalPeriod_eq_zero_of_notMem_periodicPts`, `minimalPeriod_pos_iff_mem_periodicPts`,
  `minimalPeriod_eq_zero_iff_notMem_periodicPts`, `periodicOrbit_eq_nil_iff_not_periodic_pt`, and
  `periodicOrbit_eq_nil_of_not_periodic_pt`; `minimalPeriod_pos_of_mem_periodicPts` is now
  `minimalPeriod_pos`, and `minimalPeriod_iterate_eq_div_gcd'` is merged into
  `minimalPeriod_iterate_eq_div_gcd`.  The lemmas that held for every point because of the value
  `0`, such as `iterate_minimalPeriod`, `isPeriodicPt_iff_minimalPeriod_dvd`,
  `minimalPeriod_eq_minimalPeriod_iff`, `nodup_periodicOrbit`, `periodicOrbit_chain`,
  `minimalPeriod_prodMap`, and `minimalPeriod_piMap`, take the periodicity they need;
  `iterate_mem_periodicPts`, `mem_periodicPts_iterate`, `Commute.comp_mem_periodicPts`,
  `mem_periodicPts_prodMap`, and `apply_mem_periodicPts_piMap` supply it.  `orderOf` and
  `MulAction.period` keep the value `0` for an element of infinite order and for a point that does
  not return, which is the open question of the `[L]` item on zero-encoded element order below:
  `orderOf x` is the minimal period of `1` under `(x * ·)` when `x` has finite order and `0`
  otherwise, and `MulAction.period m a` is the minimal period of `a` under `(m • ·)` when `a`
  returns and `0` otherwise; for a group action it is the order of `m` relative to the stabilizer of
  `a`, which Delgado, Ventura, and Zakharov also set to `0` when no positive power of `m` fixes `a`
  (arXiv:2105.03798, Section 2).  Both remain the generators of the return times
  (`orderOf_dvd_iff_pow_eq_one`, `pow_smul_eq_iff_period_dvd`), and the orbit and quotient
  equivalences with `ZMod`, the transfer homomorphism, and the focal subgroup theorem use
  `MulAction.period`.  Tests cover the removed names, a point of the successor map, which has no
  periodic orbit, the discharger, and the retained zero of `MulAction.period` and `addOrderOf`.

- [x] **Use extended graph distance and girth until finiteness is proved.**
  `SimpleGraph.dist G u v h`, `SimpleGraph.girth G h`, and `SimpleGraph.diam G h` take
  `h : G.Reachable u v`, `h : ¬G.IsAcyclic`, and `h : G.ediam ≠ ⊤`, which are their exact domains:
  the extended distance of two vertices that are not reachable from each other, the extended girth
  of an acyclic graph, and the extended diameter of a disconnected graph or of one with unbounded
  distances are `⊤`, which has no value in `ℕ`.  `edist`, `egirth`, and `ediam` remain the total
  invariants, and `Reachable.coe_dist_eq_edist`, `coe_girth`, and `coe_diam` identify the natural
  values with them.  The former definitions truncated the extended invariants, so two vertices that
  are not reachable from each other were at distance `0`, like equal vertices, an acyclic graph had
  girth `0`, which no graph with a cycle has, and the empty graph on two vertices had diameter `0`,
  like a single vertex.  The lemmas stating these values, `dist_eq_zero_iff_eq_or_not_reachable`,
  `dist_eq_zero_of_not_reachable`, `nonempty_of_pos_dist`, `dist_ne_zero_iff_ne_and_reachable`,
  `Reachable.of_dist_ne_zero`, `exists_walk_of_dist_ne_zero`, `dist_bot`, `girth_eq_zero`,
  `IsAcyclic.girth_eq_zero`, `girth_bot`, `diam_eq_zero_of_not_connected`,
  `diam_eq_zero_of_ediam_eq_top`, `ediam_ne_top_of_diam_ne_zero`, `diam_eq_zero_iff_ediam_eq_top`,
  and `connected_iff_diam_ne_zero`, are removed.  `Reachable.dist_triangle_left` and
  `Reachable.dist_triangle_right`, which needed only one of the two reachabilities because of the
  fallback, are replaced by `dist_triangle`, `Reachable.dist_eq_zero_iff` by `dist_eq_zero_iff`,
  `diam_ne_zero_of_ediam_ne_top` by `diam_ne_zero`, and `diam_anti_of_ediam_ne_top` by
  `diam_anti`; `Adj.diff_dist_adj` takes the reachability it formerly omitted.  Trees and forests
  are still two-colored by the parity of the distance to a vertex of each component.  Tests cover
  the removed names, the missing evidence, the empty and complete graphs, the triangle inequality,
  and the two-coloring of trees.

- [x] **Replace the unbounded fallback in `SimpleGraph.cliqueNum`.**
  `SimpleGraph.cliqueNum G : ℕ∞` is the supremum of the sizes of the finite cliques of `G`, and
  `indepNum G`, which had the same fallback, is the clique number of the complement.  This is the
  order-theoretic supremum, as `chromaticNumber : ℕ∞` is the infimum of the admissible numbers of
  colors, not a fallback: it is `⊤` exactly when `G` has arbitrarily large finite cliques
  (`cliqueNum_eq_top_iff`), for instance an infinite clique, a finite value is the size of a
  clique (`exists_isNClique_of_cliqueNum_eq`), and a graph with finitely many vertices has a
  finite clique number (`cliqueNum_ne_top`).  The former definitions took `sSup` in `ℕ` without
  boundedness, so a graph with arbitrarily large finite cliques had clique number `0`;
  `exists_isNClique_cliqueNum` then produced the empty `0`-clique, and `cliqueNum_top` stated
  `(⊤ : SimpleGraph α).cliqueNum = Nat.card α` for infinite `α` because both sides were `0`.  Now
  `cliqueNum_top` gives `ENat.card α` for every `α`; `IsClique.card_le_cliqueNum`,
  `IsIndepSet.card_le_indepNum`, `cliqueNum_bot`, `cliqueNum_ne_zero` (formerly
  `cliqueNum_ne_zero_of_finite`), and `cliqueNum_induce_le` no longer assume finitely many
  vertices; `exists_isNClique_cliqueNum` and `exists_isNIndepSet_indepNum` are replaced by
  `exists_isNClique_of_cliqueNum_eq` and `exists_isNIndepSet_of_indepNum_eq`; and
  `eq_top_of_enatCard_le_cliqueNum` assumes `Finite α`, without which it fails for the complete
  graph on `ℕ` with one edge removed.  No natural-valued projection is exposed: statements about
  finite graphs use `cliqueNum_ne_top` and equalities `G.cliqueNum = n`.  Tests cover the removed
  names, the complete and empty graphs on `ℕ`, that counterexample, attainment of finite values,
  and the comparison with the chromatic number.

- [x] **Require `n ≠ 1` for `Nat.minFac`.**
  `Nat.minFac n hn` takes `hn : n ≠ 1`, the exact domain of the least prime factor: `1` has no prime
  factor, while every prime divides `0`, so `minFac_zero` still gives `2`.  The literature has no
  common value at `1` (OEIS A020639 uses `1`, G. Tenenbaum, *Introduction to Analytic and
  Probabilistic Number Theory*, 3rd ed., Notation, p. xxiii, uses `+∞`), so no value is chosen.  The
  default discharger `minFac_tac` finds the side condition as a local hypothesis, by linear
  arithmetic, from the primality of `n`, or by evaluating a closed term, and it never chooses `n`.
  The statements of the former value `minFac 1 = 1` are removed (`minFac_one`, `minFac_eq_one_iff`,
  and `minFac_prime_iff`), and `le_minFac` and `le_minFac'` lose their disjunct `n = 1`.
  `minFac_dvd`, `minFac_pos`, `minFac_eq`, `prime_def_minFac`, `coprime_of_lt_minFac`, and
  `gcd_eq_one_of_lt_minFac` take `n ≠ 1`; `minFac_le`, `minFac_le_div`, and `minFac_sq_le_self` take
  `1 < n` instead of `0 < n`; `minFac_le_of_dvd` obtains `n ≠ 1` from its divisor
  (`ne_one_of_two_le_of_dvd`); and `minFac_eq_two_iff`, `pow_minFac`, and `Prime.pow_minFac` read
  the side condition off their left-hand sides.  `PosNum.minFac` and `Num.minFac`, which also
  returned `1` at `1`, take the same hypothesis.  The `norm_num` extension evaluates `minFac` only
  off `1` (its helper `MinFacHelper` now records `1 < n` and a lower bound for the divisors), the
  `primeFactorsList` simproc and the decision procedures for `Nat.Prime` and `IsPrimePow` treat `1`
  separately, and `isPrimePow_nat_iff_bounded_log_minFac` takes `1 < n`.
  `Subgroup.normal_of_index_eq_minFac_card` and the cyclic Sylow lemmas
  `IsCyclic.normalizer_le_centralizer` and `IsCyclic.isComplement'` in
  `Mathlib/GroupTheory/Transfer.lean` assume `Nat.card G ≠ 1`, which excludes only the trivial
  group, the von Mangoldt function uses the least prime factor of a prime power, and the least prime
  factor `LucasLehmer.q p` of a Mersenne number takes `p ≠ 1` (`mersenne_eq_one_iff`).  Tests cover
  the removed names, the missing evidence, the least prime factor of `0`, evaluation, and the
  discharger.

- [x] **Give `Nat.log` and `Nat.clog` their extremal domains.**
  `Nat.log b n` takes `1 < b` and `n ≠ 0`, exactly the inputs for which a largest `k` with
  `b ^ k ≤ n` exists: for `b ≤ 1` every `k` satisfies the inequality when `n ≠ 0`, and for `n = 0`
  none does.  `Nat.clog b n` takes `1 < b ∨ n ≤ 1`, exactly the inputs for which a least `k` with
  `n ≤ b ^ k` exists; it is `0` for `n ≤ 1`.  Neither the floor logarithm of `0` nor a logarithm in
  base `0` or `1` has a standard value, so none is chosen.  The default discharger `nat_log_tac`
  finds the side conditions as local hypotheses, by linear arithmetic, or by evaluating a closed
  term, and never chooses the base or the argument.  The statements of the former fallback values
  are removed (`log_of_left_le_one`, `log_zero_left`, `log_zero_right`, `log_one_left`,
  `clog_of_left_le_one`, `clog_zero_left`, and `clog_one_left`), together with `log_lt_of_lt_pow'`,
  `pow_log_le_add_one`, `log_eq_one_iff'`, and the monotonicity statements `log_monotone`,
  `log_antitone_left`, and `clog_antitone_left`, whose functions are not total; `clog_monotone` is
  stated for `1 < b`.  `log_eq_zero_iff`, `log_pos_iff`, `log_eq_iff`, and the bounds take the
  domain, `log_eq_zero_iff` and `log_eq_one_iff` lose their disjuncts for `b ≤ 1`, and the lemmas
  whose left-hand sides carry the side conditions read them off the term.  `Int.log b r` and
  `Int.clog b r`, defined from `Nat.log` and `Nat.clog`, take `1 < b` and `0 < r`: for `r ≤ 0` no
  power of `b` is at most `r`, and every power of `b` is at least `r`.  Their fallback statements
  (`log_of_left_le_one`, `log_of_right_le_zero`, `log_zero_left`, `log_zero_right`, `log_one_left`,
  and their `clog` counterparts) are removed, `clog_inv` and `log_inv` hold on positive elements,
  and `Real.floor_logb_natCast`, `Real.ceil_logb_natCast`, `Real.natFloor_logb_natCast`,
  `Real.natCeil_logb_natCast`, and `Real.natLog_le_logb` take the same conditions.  Legendre's
  formula and the carry formulas for binomial coefficients (`Nat.Prime.emultiplicity_factorial`,
  `Nat.Prime.emultiplicity_choose`, `padicValNat_factorial`, `padicValNat_choose`, and their
  variants) take a bound `n < p ^ b` instead of `log p n < b`; `padicValNat_le_nat_log` takes
  `1 < p` and `n ≠ 0`, `padicValRat_two_harmonic`, `Nat.max_log_padicValNat_succ_eq_log_succ`, and
  `factorization_lcmUpto` take `n ≠ 0`, and `lcmUpto_eq_prod_pow_log` and `psi_eq_sum_mul_log_prime`
  range over `(primesLE n).attach`, whose membership proofs supply the side conditions.  The
  `norm_num` extensions evaluate the logarithms on their domains.  Tests cover the removed names,
  the missing evidence for each side condition, evaluation, and the integer logarithm.

- [x] **Identify `Nat.findGreatest` as a supremum in `ℕ`.**
  `Nat.findGreatest P n` is the supremum in `ℕ` of `{m | m ≤ n ∧ P m}`, for every `P`
  (`isLUB_findGreatest` and `findGreatest_eq_sSup` in `Mathlib/Order/Lattice/Nat.lean`), and the
  supremum is the greatest element exactly when some `m ≤ n` satisfies `P`
  (`isGreatest_findGreatest`).  Its value `0` when no `m ≤ n` satisfies `P` is therefore not a
  sentinel but the least upper bound of the empty set, which in an ordered set is its least element
  (B. A. Davey and H. A. Priestley, *Introduction to Lattices and Order*); the docstring of
  `Nat.findGreatest` now says so.  No proof-carrying greatest-witness operation is added: the
  supremum is the greatest witness whenever one exists, and the extrema defined through it,
  `ruzsaSzemerediNumber` and `mulRothNumber`, are suprema over families that contain the empty graph
  or set, so they are attained (`ruzsaSzemerediNumber_spec`, `mulRothNumber_spec`).  The docstring
  of `ruzsaSzemerediNumber`, which described a maximal number of edges although the definition
  counts triangles, now describes triangles; each edge of a locally linear graph lies in exactly one
  triangle, so the maximal number of edges is three times the number.

- [x] **Require eventual constancy for monotone-sequence limits.**
  `monotonicSequenceLimitIndex a h` and `monotonicSequenceLimit a h` take
  `h : ∃ n, ∀ m, n ≤ m → a n = a m`, which is the exact domain: the index is the least `n` from
  which `a` is constant (`Nat.find`), and a sequence that is not eventually constant has no such
  `n`.  The former `sInf` of the empty set made the index `0` and the limit `a 0` for every sequence
  that is not eventually constant, such as the identity of `ℕ`.  Well-foundedness now only supplies
  the evidence (`WellFoundedGT.monotone_chain_condition`), so `le_monotonicSequenceLimit` and
  `iSup_eq_monotonicSequenceLimit` and `ciSup_eq_monotonicSequenceLimit` (formerly prefixed by
  `WellFoundedGT.`) hold for every eventually constant sequence, the last without a boundedness
  hypothesis; `monotonicSequenceLimit_eq` and `monotonicSequenceLimitIndex_le` characterize the
  index.  The only consumer, the index of a generalized eigenspace, had the same fallback,
  documented as "not meaningful" off its domain: `Module.End.maxUnifEigenspaceIndex f μ h` and
  `maxGenEigenspaceIndex f μ h` take `h : ∃ k : ℕ, f.genEigenspace μ k = f.genEigenspace μ ⊤` and
  are the least such `k`, `exists_genEigenspace_eq_top` supplies `h` for a Noetherian module, and
  `genEigenspace_top_eq_maxUnifEigenspaceIndex` and `maxGenEigenspace_eq` hold for every `h`.
  `genEigenspace_finrank_eq_top` gives the finite-dimensional bound directly, and the Lie-algebra
  consumers obtain their exponents from `exists_genEigenspace_eq_top` or use the maximal
  generalized eigenspace itself.  Tests cover the removed names, the identity of `ℕ`, the limit and
  index of an eventually constant sequence, the well-founded case, and the eigenspace index.

- [x] **Put fundamental circuits and cocircuits on their admissible data.**
  `Matroid.fundCircuit M e I h` takes `h : M.FundCircuitExists e I`: `I` is independent and `e` is
  in the closure of `I` but not in `I`.  Then `insert e I` is dependent and contains a unique
  circuit, which contains `e` (`fundCircuit_isCircuit`, `IsCircuit.eq_fundCircuit_of_subset`); for
  `e ∈ I` or `e ∉ M.closure I` the set `insert e I` is independent and contains no circuit.
  `Matroid.fundCocircuit M e B h` takes the dual data `h : M.FundCocircuitExists e B`: `B` is
  spanning, `e ∈ B`, and `B \ {e}` is not spanning, so that a unique cocircuit meets `B` exactly in
  `e` (`fundCocircuit_isCocircuit`, `fundCocircuit_inter_eq`); for a base `B` this holds for every
  `e ∈ B` (`IsBase.fundCocircuitExists`), and `FundCocircuitExists.dual` gives the fundamental
  circuit data in the dual matroid.  The former definitions returned `{e}` for `e ∈ I` or `e ∉ M.E`
  and `insert e I` for `e ∈ M.E \ M.closure I`, which are not circuits
  (`fundCircuit_eq_of_mem`, `fundCircuit_eq_of_notMem_ground`, `fundCocircuit_eq_of_notMem`, and
  `fundCocircuit_eq_of_notMem_ground`, removed), and `IsBase.mem_fundCocircuit_iff_mem_fundCircuit`
  held for all `e` and `f` through these values; it now takes `e ∈ M.E \ B` and `f ∈ B`.
  `Indep.fundCircuit_isCircuit`, `Indep.mem_fundCircuit_iff`, and `IsBase.fundCircuit_isCircuit`
  became `fundCircuit_isCircuit` and `mem_fundCircuit_iff` on the evidence, which
  `IsBase.fundCircuitExists`, `IsCircuit.fundCircuitExists_of_subset`, and
  `FundCircuitExists.restrict` supply; `fundCircuit_restrict_univ` is removed.  Tests cover the
  removed names, the missing evidence, the two degenerate cases, and the fundamental circuits and
  cocircuits of a base.

- [ ] **Put bundle coordinate changes on chart overlaps.**
  `Bundle.Trivialization.coordChange` in
  `Mathlib/Topology/FiberBundle/Trivialization.lean:754` accepts every base point even though its
  identity, composition, and continuity theorems require membership in the relevant base sets; the
  proof-carrying `coordChangeHomeomorph` at line 795 is the existing strict substrate.  The analogous
  `coordChangeL` in `Mathlib/Topology/VectorBundle/Basic.lean:266` returns the identity outside the
  overlap.  Make the ordinary coordinate-change operations take overlap evidence or a point in the
  overlap.  Keep ambient representatives private, including technical trivialization inverses, and
  only when every exported statement proves that values outside the base set are irrelevant.

- [x] **Identify the exact event contract for conditional probability.**
  `ProbabilityTheory.cond μ s hs` takes `hs : IsConditionable μ s`: `s` is null-measurable and has
  positive finite measure.  This is the event contract of conditional probability given an event of
  positive probability (A. N. Kolmogorov, *Foundations of the Theory of Probability*, Chapter I,
  §4), with the same formula for any measure on a set of positive finite measure.  Null-measurable
  sets are the events of the completion, and conditioning on one agrees with conditioning on its
  measurable hull (`cond_toMeasurable_eq`).  Other sets are not conditioned through `toMeasurable`:
  no literature defines that interpretation, and the formula is not concentrated on such a set (for
  a Bernstein set `B ⊆ [0, 1]`, conditioning Lebesgue measure on `[0, 1] \ B` gives `B` probability
  `1`).  The former definition returned `0` on null sets and sets of infinite measure
  (`cond_empty`, `cond_eq_zero`, and `cond_eq_zero_of_meas_eq_zero`, removed) and was a probability
  measure only under separate hypotheses (`cond_isProbabilityMeasure_of_finite` and
  `cond_isProbabilityMeasure`, replaced by the instance `isProbabilityMeasure_cond`).  The notations
  `μ[|s]` and `μ[t | s]` find the evidence with the bounded discharger `conditionable`, from a
  hypothesis, from the measurability and the positive finite measure of `s`, or for a finite
  measure.  `cond_apply'`, `cond_cond_eq_cond_inter'`, `cond_mul_eq_inter'`, and `ae_cond_mem₀`
  merge into their unprimed forms, which hold for every event `t` once `s` is conditionable.
  `uniformOn s hs` takes the conditionability of the counting measure on `s`, which
  `isConditionable_count_iff` characterizes as a finite nonempty measurable set; the lemmas stating
  its former value `0` (`uniformOn_empty_meas`, `uniformOn_eq_zero`, `uniformOn_eq_zero'`, and
  `finite_of_uniformOn_ne_zero`) are removed, and the law of total probability, the disjoint union,
  and the product formula take the conditionability of their parts.  `pdf.IsUniform X s P μ`
  includes the conditionability of `μ` on `s`, so no random variable is uniform on a set of measure
  `0` or `∞` (`pdf_eq_zero_of_measure_eq_zero_or_top`, removed).  `Measure.toFinite` normalizes its
  finite measure directly, the conditional independence lemmas take the conditionability of the
  conditioning events, and the singleton conditional expectation lemmas take a set of positive
  measure.  Tests cover the removed names, the missing evidence, the empty set, an infinite
  measure, the counting measure on an infinite set, and a uniform distribution on the real line.

- [x] **Give `condCDF` its exact domain.**
  `condCDF ρ` requires `[HasUniqueCondCDF ρ]`: some `F` satisfies `IsCondCDF ρ F`, and any two such
  families agree `ρ.fst`-a.e.  `IsCondCDF ρ F` says that every `F a` is the cdf of a probability
  measure, that `a ↦ F a x` is measurable, and that `∫⁻ a in s, ENNReal.ofReal (F a x) ∂ρ.fst` is
  `ρ (s ×ˢ Iic x)` for every measurable `s` and every real `x`.  Such a family is determined only up
  to `ρ.fst`-null sets, the version freedom of `condDistrib`, and the item on almost-everywhere
  classes below makes `condCDF ρ` their class, which every conditional cdf represents
  (`IsCondCDF.mem_condCDF`).  A finite measure is only a sufficient condition:
  `hasUniqueCondCDF_of_sigmaFinite_fst` supplies the class whenever `ρ.fst` is σ-finite, for
  instance for `volume.prod (gaussianReal 0 1)`, whose conditional cdf is a.e. the standard Gaussian
  cdf; `Measure.prod.instSigmaFiniteFst` finds the σ-finite first marginal of every product of a
  σ-finite measure with a finite measure, and `instSigmaFiniteSnd` does the same for second
  marginals.  Chang and Pollard, *Conditioning as disintegration*, Statistica Neerlandica 51 (1997),
  disintegrate a σ-finite measure with respect to a σ-finite mixing measure (Definition 1, p. 292);
  for such a measure with a disintegration, the disintegrating measures can be taken to be
  probabilities exactly when the image measure is σ-finite and serves as the mixing measure
  (p. 292 and Theorem 2, p. 294).  On paper, the class consists exactly of the `ρ` whose first
  marginal is semi-finite and whose ray measures `ρ.IicSnd x` all have densities with respect to
  it.  A set of positive measure all of whose measurable subsets have measure 0 or ∞ exists exactly
  when `ρ.fst` is not semi-finite; there the ray identity sees only where `F a x` is positive, so a
  solution, if one exists, can be replaced on that set by `(F a t + F a (t - 1)) / 2` and is not
  unique.  An s-finite measure is σ-finite exactly when it is semi-finite, and `ρ.fst` is s-finite
  when `ρ` is, so for s-finite `ρ` the class holds exactly when `ρ.fst` is σ-finite.  These
  characterizations are paper proofs; Lean proves the σ-finite instance and two examples in
  `Counterexamples/CondCDF.lean`.  Planar Lebesgue measure is σ-finite, but its first marginal is
  `∞ • volume`, and every probability cdf that is positive everywhere is, as a constant family, a
  conditional cdf of it, so the class fails.  The image of counting measure on `ℝ` under
  `a ↦ (a, 0)` lies in the class although its first marginal, counting measure, is not σ-finite;
  it is not s-finite, and it is why the domain is a class rather than `[SigmaFinite ρ.fst]`.  The
  former definition accepted every `ρ`.  It applied `stieltjesOfMeasurableRat` to the
  Radon--Nikodym derivatives of the rational ray measures with respect to `ρ.fst`, which replaces
  the family at every `a` where it is not a rational cdf by the cdf of `dirac 0`.  For planar
  Lebesgue measure every ray measure equals the marginal, so it returned the cdf of `dirac 0` for
  every `a` and violated the ray identity, while `condCDF_le_one`, both limits, and the instance
  `IsProbabilityMeasure (condCDF ρ a).measure` held for every `ρ`.  The existence proof multiplies
  `ρ` by a positive integrable function of the first coordinate, which makes it finite without
  changing the ray derivatives, and applies the finite-kernel existence statement of `CDFToKernel`
  to its Radon--Nikodym derivatives.  That construction and its lemmas are private to
  `CondCDF.lean` and serve only the existence proof; `condCDF` is obtained from the existence
  statement and does not unfold to them.  `IsCondCDF.integrable`, `setIntegral`, `integral`,
  `isCondKernelCDF`, and `ofReal_ae_eq_rnDeriv` hold for every conditional cdf.  The
  Bochner-integral and kernel statements keep `IsFiniteMeasure ρ` as a hypothesis, which the
  finite-kernel disintegration in `StandardBorel` supplies.  Tests cover the rejected measures,
  routine evidence, an infinite measure in the domain, the zero measure, null-set modifications,
  proof independence, and rewriting.

- [ ] **Identify the exact domain of `Measure.condKernel` and `condDistrib`.**
  `Measure.condKernel` in `Mathlib/Probability/Kernel/Disintegration/StandardBorel.lean:429` and
  `condDistrib` in `Mathlib/Probability/Kernel/CondDistrib.lean:77` require a finite measure, which
  is a sufficient condition; `condExpKernel` and `posterior` have the same finite-measure domain.
  The conditional-cdf result above does not transfer automatically, because a Markov
  disintegration along `ρ.fst` and the ray identity diverge outside σ-finite marginals, as two
  paper computations show.  On `Unit × ℝ`, `∞ • dirac ((), 0)` has the unique Markov
  disintegration `dirac 0`, although every cdf that is positive exactly on `[0, ∞)` satisfies the
  ray identity.  Conversely, on `ℝ × ℝ` the sum over `a : ℝ` of
  `(dirac a).prod (gaussianReal 0 1)`, plus the image of Lebesgue measure on `[0, 1]` under
  `(·, 0)`, has the unique conditional cdf of `gaussianReal 0 1` but no disintegration along its
  first marginal, since it gives `univ ×ˢ {0}` mass one.  First fix the specification, including
  whether a σ-finite measure equivalent to the marginal may serve as the mixing measure (Chang and
  Pollard, Definition 1), then its exact domain.  The composition-product in `IsCondKernel` now has
  its exact domain (item below), so a disintegration no longer fails merely because an input is not
  s-finite, and a conditional kernel need not be s-finite.

- [x] **Give parametric distributions their parameter domains.**
  `gammaMeasure a r ha hr`, `expMeasure r hr`, `paretoMeasure t r ht hr`, and
  `betaMeasure α β hα hβ` take proofs that their parameters are positive, and
  `geometricMeasure p hp` takes `hp : p ≠ 0`; the densities `gammaPDFReal`, `exponentialPDFReal`,
  `paretoPDFReal`, `betaPDFReal`, and their `ℝ≥0∞`-valued versions take the same proofs, as does the
  beta normalizing constant `beta`, whose total formula `Γ(α) Γ(β) / Γ(α + β)` gave
  `beta (-1) (1 / 2) = 0` from the zero value of `Real.Gamma` at its pole `-1`, although the beta
  function has a pole there.  These are the exact domains: `x ^ (a - 1) * exp (-(r * x))` on
  `(0, ∞)`, `exp (-(r * x))` on `[0, ∞)`, `x ^ (-(r + 1))` on `[t, ∞)`, and
  `x ^ (α - 1) * (1 - x) ^ (β - 1)` on `(0, 1)` are integrable exactly for positive parameters, and
  the masses `(1 - p) ^ n * p` sum to one exactly when `p ≠ 0`.  Siegrist, *Probability,
  Mathematical Statistics, and Stochastic Processes*, defines the distributions for these parameters
  in §5.8 (with scale `1 / r`), §14.2, §5.36, §5.17, and §11.3; the last takes `p ∈ (0, 1]` and
  counts the failures before the first success on `ℕ`, so the degenerate
  `geometricMeasure 1 hp = dirac 0` is retained.  The densities specify the distributions, so a
  degenerate limit such as a shape-zero gamma distribution at `dirac 0` would be a separate object
  with its own specification and source.  Invalid gamma, exponential, and beta parameters previously
  gave the zero measure or an infinite measure, while mathlib's powers of negative bases gave
  `paretoMeasure t r` with `t < 0`, `r < 0`, and `0 < cos (r * π)` the mass `cos (r * π) ^ 2`:
  `paretoMeasure (-1) (-2)` was the probability measure with density `-2 * x` on `[-1, 0]`.
  `geometricMeasure 0` was `dirac 0`, which made `IsProbabilityMeasure (geometricMeasure p)` an
  instance for every `p`.  `IsProbabilityMeasure` is now a global instance for each family, so the
  `cdf` formulas no longer supply it with `haveI`, and `isProbabilityMeasureBeta` is renamed
  `isProbabilityMeasure_betaMeasure`.  As for `PMF.binomial p h n`, the proofs are explicit
  arguments without a default discharger, which would capture the set in `gammaMeasure a r s` and
  the point in `gammaPDFReal a r x`.  Tests cover missing and nonnegative-only evidence, instance
  search, the degenerate geometric distribution, proof independence, and rewriting.

- [x] **Classify the zero-scale Gaussian and Cauchy cases.**
  The degenerate Gaussian distribution `gaussianReal μ 0 = dirac μ` is retained.  Bogachev,
  *Gaussian measures* (AMS, 1998), Definition 1.1.1, calls a Borel probability measure on `ℝ`
  Gaussian if it is a Dirac measure or has a normal density, and assigns variance zero to the
  Dirac case; Siegrist, *Probability, Mathematical Statistics, and Stochastic Processes*, §5.6,
  treats a constant as normal with variance zero where convenient and notes that the density and
  distribution function formulas do not hold for it.  `charFun_gaussianReal` specifies
  `gaussianReal μ v` for every `v`, and the degenerate case is load-bearing: `IsGaussian` requires
  the image under the zero functional to be `gaussianReal 0 0`, and a pre-Brownian motion has law
  `gaussianReal 0 0` at time zero.  A Dirac measure has no Lebesgue density, so
  `gaussianPDFReal μ v hv` and `gaussianPDF μ v hv` take `hv : v ≠ 0`, and the zero values at
  `v = 0` with their simp lemmas `gaussianPDFReal_zero_var` and `gaussianPDF_zero_var` are
  removed.  `rnDeriv_gaussianReal` takes the same proof, and `rnDeriv_gaussianReal_zero_var` states
  that the Radon--Nikodym derivative of the degenerate distribution vanishes.  The joint
  measurability lemmas `Measurable.gaussianPDFReal` and `Measurable.gaussianPDF` take the nonzero
  variance pointwise and replace the uncurried versions, and `measurable_gaussianReal` splits at
  `v = 0`.  For `γ = 0` the Cauchy density formula vanishes away from `x₀`, so no probability
  measure has it as a density, and the law of `x₀ + γ Z` for a standard Cauchy `Z` is the point
  mass at `x₀`.  No checked source calls that law a Cauchy distribution: Siegrist, §5.32, requires
  a positive scale, and Samorodnitsky--Taqqu, *Stable non-Gaussian random processes* (1994), allow
  scale zero for stable laws in Definition 1.1.6 but give the Cauchy distribution `S₁(σ, 0, μ)` by
  its density (1.1.13).  As for a shape-zero gamma distribution, the point mass would be a
  separate object with its own specification and source.  `cauchyMeasure x₀ γ hγ`,
  `cauchyPDFReal x₀ γ hγ`, and `cauchyPDF x₀ γ hγ` therefore take `hγ : γ ≠ 0`.  The Dirac branch,
  `cauchyMeasure_zero_scale`, and the zero-density simp lemmas are removed;
  `cauchyMeasure_of_scale_ne_zero` is removed because `cauchyMeasure` now unfolds to the measure
  with density `cauchyPDF x₀ γ hγ`; and `cauchyPDF_pos` is renamed `cauchyPDFReal_pos` after its
  statement.  Tests cover missing and nonnegative-only evidence, the unprovable zero-scale
  obligation, the retained degenerate Gaussian distribution with its atom, characteristic
  function, zero-map image, and `IsGaussian` instance, both Radon--Nikodym derivatives,
  measurability automation, proof independence, and rewriting.

- [x] **Require a positive semidefinite covariance matrix for `multivariateGaussian`.**
  `multivariateGaussian μ S hS` takes `hS : S.PosSemidef`, which includes symmetry.  It is the
  Gaussian measure with mean `μ` and covariance matrix `S`: the `ν` with `IsGaussian ν`,
  `ν[id] = μ`, and `covarianceBilin ν x y = x ⬝ᵥ S *ᵥ y`, unique by `IsGaussian.ext`.  This is the
  exact domain, because `isPosSemidef_covarianceBilin` makes every covariance matrix symmetric and
  positive semidefinite and `covarianceBilin_multivariateGaussian` attains each such `S`.  The
  formula `exp (⟪t, μ⟫ * I - t ⬝ᵥ S *ᵥ t / 2)` for the characteristic function only sees the
  symmetric part of `S`, so it cannot replace the covariance as the specification: for
  `S = !![1, 1; -1, 1]` it is the characteristic function of `multivariateGaussian μ 1 _`, while no
  measure has covariance matrix `S`.  The former definition applied `CFC.sqrt` to every matrix,
  and its `cfcₙ` junk value zero made `multivariateGaussian μ S` the Dirac measure `dirac μ`, whose
  covariance is zero, for every `S` that is not positive semidefinite, that one included.  Singular
  `S` are retained: Siegrist, *Probability, Mathematical Statistics, and Stochastic Processes*,
  §5.7, notes that for a singular `A` the covariance `A Aᵀ` of `μ + A Z` is "only positive
  semi-definite" and the distribution degenerate, and its general definition ("A Further
  Generalization") asks every `a · X` to be univariate normal, constants included, as `IsGaussian`
  does.  The new simp lemma `multivariateGaussian_zero_cov` gives `dirac μ` for the zero matrix, as
  `gaussianReal_zero_var` does in one dimension, and the covariance matrix of Brownian motion at
  finitely many times is singular whenever they include zero.
  `multivariateGaussian_of_not_posSemidef` is removed.  `isGaussian_multivariateGaussian` and
  `integral_id_multivariateGaussian` with its primed form, which held for every `S` through the
  Dirac branch, now take `hS` and are stated for `multivariateGaussian μ S hS`, as are the
  covariance, variance, marginal, characteristic-function, and restriction theorems, which already
  assumed `hS`; `multivariateGaussian_zero_one` uses `PosSemidef.one`.  The composition-style
  `Measurable.multivariateGaussian` takes the proofs pointwise and replaces the uncurried
  `measurable_multivariateGaussian`, which asserted joint measurability over all matrices;
  `fun_prop` still proves it on the subtype of positive semidefinite matrices.  As for the
  parametric distributions, the proof is explicit, without a default discharger, which would take
  the set in `multivariateGaussian μ S s` as a proof.  The Brownian projective family supplies its
  existing `posSemidef_covMatrix`.  The definition still applies `CFC.sqrt`, but only to positive
  semidefinite matrices, where `CFC.sqrt_mul_sqrt_self` holds, and `Measurable.multivariateGaussian`
  is proved through `CFC.measurable_sqrt`; the L item on continuous functional calculus records
  both as consumers.  The module TODO on trace-class operators now asks for positivity.  Tests
  cover missing and symmetric-only evidence; an indefinite and a nonsymmetric matrix, neither of
  which is the covariance matrix of a measure, and the characteristic function of the latter;
  uniqueness given the mean and the covariance matrix; the zero matrix; Brownian motion at time
  zero; instances; measurability automation; proof independence; and rewriting.

- [x] **Keep the `dirac 0` default of `stieltjesOfMeasurableRat` out of the public API.**
  `IsRatCondKernelCDF.exists_isCondKernelCDF` in
  `Mathlib/Probability/Kernel/Disintegration/CDFToKernel.lean` is the public boundary: for a finite
  kernel `κ`, a rational conditional kernel CDF `f` gives a conditional kernel CDF that agrees with
  `f` `ν a`-a.e. at every rational.  `IsCondKernelCDF.ae_eq` proves that two conditional kernel CDFs
  agree `ν a`-a.e., `IsCondKernelCDF.congr` that a measurable modification by probability cdfs on
  null sets is again one, and `IsCondKernelCDF.sigmaFinite` that one exists only when every `ν a` is
  σ-finite.  `defaultRatCDF`, `toRatCDF`, and `stieltjesOfMeasurableRat` moved from
  `MeasurableStieltjes.lean` into that file as private declarations, with the lemmas that the
  existence proof uses; the other lemmas about them are removed.  They form a representative
  constructor that serves only as the witness of the existence statement, so they stay private
  without a removal condition.  `IsRatStieltjesPoint`, `IsMeasurableRatCDF`, and the checked
  extension `IsMeasurableRatCDF.stieltjesFunction` stay public.  The construction replaced `f a` by
  the rational cdf of `dirac 0` wherever `IsRatStieltjesPoint f a` failed and took no measure, so
  for `f = 0` it returned the cdf of `dirac 0` at every `a`.  `stieltjesOfMeasurableRat_eq` exposed
  that default, and the bound, limit, and probability lemmas, including the global instance
  `instIsProbabilityMeasure_stieltjesOfMeasurableRat`, held for every measurable `f` only through
  it.  Its statements in `CDFToKernel` all assumed `IsRatCondKernelCDF`, which confines the default
  to null sets, so no downstream public object exposed it on a set of positive measure; but
  `condKernelCDF` unfolded to it on null sets, and for the zero kernel `κ : Kernel Unit (ℝ × ℝ)` it
  gave `condKernelCDF κ ((), 0) 0 = 1`.  `Kernel.condKernelCDF` no longer unfolds to it: the item
  on almost-everywhere classes below makes it the class of the conditional kernel CDFs, which
  `IsCondKernelCDF.ae_eq` determines up to `fst κ a`-null sets, and the private `condKernelReal`,
  from which the witness of `Kernel.exists_isMarkovKernel_isCondKernel` is built when `α` is
  uncountable, takes its conditional kernel CDF from the same statement.  The existence proof for
  `condCDF` takes its
  conditional kernel CDF from the same statement, so the private `condCDFAux` is removed.  The next
  item treats the arbitrary point of `borelMarkovFromReal` in the same way, and the
  conditional-kernel item above records the open domain question, which also concerns
  `[IsFiniteKernel κ]`.  Tests cover the private names, existence, σ-finiteness, uniqueness, the
  domain of `condKernelCDF`, its density version, its value at the atom of
  `const Unit (dirac (0, 1))`, and a modification on the null set of that kernel; both conditional
  kernel CDFs of the zero kernel; the zero rational family, which fails only
  `isRatStieltjesPoint_ae` for the zero kernel with respect to `const Unit (dirac 0)`, where no
  conditional kernel CDF exists; and the rejection of the zero rational family and of the cdf of
  `dirac 0` for `const Unit (dirac (0, 1))`.

- [x] **Keep the arbitrary point of `borelMarkovFromReal` out of the public API.**
  `Kernel.exists_isMarkovKernel_isCondKernel` and `Measure.exists_isMarkovKernel_isCondKernel` in
  `Mathlib/Probability/Kernel/Disintegration/StandardBorel.lean` are the public boundary: a finite
  kernel `κ : Kernel α (β × Ω)`, where `Ω` is a nonempty standard Borel space and `α` is countable
  or `β` is countably generated, and a finite measure on `α × Ω` are disintegrated by Markov
  kernels.  `Kernel.condKernel` and `Measure.condKernel` are obtained from these statements: the
  item on almost-everywhere classes below makes them the classes of the disintegrating Markov
  kernels, which `Kernel.IsCondKernel.ae_eq` and `Measure.IsCondKernel.ae_eq` determine up to
  `fst κ a`- and `ρ.fst`-null sets.  `borelMarkovFromReal Ω η` pulls `η a` back along
  `embeddingReal Ω` where `η a` gives the complement of its range measure zero, and pulls back the
  Dirac mass at the image of `Classical.ofNonempty : Ω` elsewhere.  `borelMarkovFromReal_apply` and
  `borelMarkovFromReal_apply'` exposed that branch for every `η`, and the instance
  `instIsMarkovKernelBorelMarkovFromReal` held for every Markov `η` only through it.  In
  `condKernelBorel` and `condKernelUnitBorel` the branch acted only on `fst κ a`-null sets (`h_ae`
  in `compProd_fst_borelMarkovFromReal_eq_comapRight_compProd`), so no conditional kernel built
  from it exposed the branch on a set of positive measure, but `Kernel.condKernel` and
  `Measure.condKernel` unfolded to it there, and `Measure.condKernel_apply` exposed that unfolding.
  As a function of an arbitrary `η` the construction has a fallback branch, but it now only builds
  witnesses: it and the lemmas that the existence proofs use are private to `StandardBorel.lean`,
  and no public definition unfolds to them.  The boundary proves representative independence: the
  public classes do not depend on the witness, since `Kernel.IsCondKernel.ae_eq` and
  `Measure.IsCondKernel.ae_eq` determine every disintegrating kernel up to null sets.  As for the
  construction behind `condKernelCDF`, the resolved audit "An explicit default does not justify a
  public mathematical operation" below therefore lets them stay private without a removal
  condition.
  The `_apply` lemmas, the finite-kernel instance, `condKernelBorel`, `condKernelUnitBorel` and
  their instances, `Measure.condKernel_apply`, and the `irreducible_def` equations
  `Kernel.condKernel_def` and `Measure.condKernel_def` are removed, and the s-finite and Markov
  instances became private lemmas.  For countable `α` the existence proof still glues the
  conditional kernels of the measures `κ a`, but `Kernel.condKernel` no longer unfolds to that
  gluing.  The finite-measure and finite-kernel domains are unchanged; the conditional-kernel item
  above records the open domain question.  Tests cover the names that exposed the branch, including
  the instances and the `_def` equations; both existence statements; `Kernel.condKernel` for a
  countable `α` and for a countably generated `β`; the Markov representatives of both classes;
  almost-everywhere uniqueness; the value of every representative of `Measure.condKernel` at the
  atom of `dirac (0, 1)`; two representatives that differ off the atom; the rejection of the
  constant kernel `dirac 0`; and the finite-measure and finite-kernel domains.

- [x] **Replace integration-facing `ContinuousMap.mkD` with an a.e.-continuous-family interface.**
  `ContinuousMap.mkD` and `ContinuousMapZero.mkD`, which replaced a noncontinuous function by a
  fallback, are removed together with their lemmas and the `mkD` lemmas of
  `Mathlib/Topology/CompactOpen.lean`, of `Mathlib/MeasureTheory/SpecificCodomains/`, and of the
  continuous functional calculus.  An almost everywhere continuous family `f : X → Y → E` is
  represented by a bundled `F : X → C(Y, E)` with `∀ᵐ x ∂μ, ⇑(F x) = f x`:
  `ContinuousMap.exists_eventually_coe_eq_iff` (and its `C(Y, E)₀` version, which adds `f x 0 = 0`)
  shows that such representatives exist exactly for almost everywhere continuous families, and
  `eventuallyEq_of_eventually_coe_eq` that any two agree almost everywhere, so the class does not
  depend on the representative.  Strong measurability and integrability remain separate hypotheses
  or follow from joint continuity (`aeStronglyMeasurable_of_uncurry` and its restricted variants)
  and a bound (`hasFiniteIntegral_of_ae_coe_eq_of_bound`).  `cfc_apply_of_coe_eq` and
  `cfcₙ_apply_of_coe_eq` replace `cfc_apply_mkD` and `cfcₙ_apply_mkD`; the primed integral lemmas of
  `Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Integral.lean` take the
  representative, its specification, and its integrability, and the unprimed ones keep their
  statements.  Tests cover the removed names, the existence and uniqueness of representatives, an
  empty domain, measurability, and the functional calculus.

- [x] **Prevent impossible regularity requests from becoming zero operators.**
  The operators on `𝓓^{n}_{K}(E, F)` and `𝓓^{n}(Ω, F)` take their regularity inequality, which
  the discharger `regularity_le` finds from a hypothesis, for smooth maps (`le_top`), for equal
  regularities, and for numerals: `ContDiffMapSupportedIn.fderivLM`, `fderivCLM`, and
  `TestFunction.fderivCLM` take `k + 1 ≤ n`, `iteratedFDerivLM` takes `k + i ≤ n`, the structure
  maps `structureMapLM` and `structureMapCLM` and the seminorms `N[𝕜]_{K, n, i}` take `i ≤ n`, the
  inclusions `monoLM`, `monoCLM`, and `TestFunction.monoCLM` take `n₂ ≤ n₁` and the inclusion of
  the compact or open sets, and `TestFunction.lineDerivCLM` and `Distribution.lineDerivCLM` take
  `k + 1 ≤ n`.  The former operators were the zero map when the inequality failed
  (`fderivLM_apply_of_gt`, `fderivCLM_apply_of_gt`, `iteratedFDerivLM_apply_of_gt`,
  `monoLM_eq_zero`, `monoCLM_eq_zero`, `TestFunction.fderivCLM_apply_of_gt`,
  `TestFunction.lineDerivCLM_apply_of_gt`, and `TestFunction.monoCLM_eq_zero`, removed), and the
  seminorms of order `i > n` were `0` (`seminorm_eq_bot_of_gt`, removed).  The `_apply` lemmas
  state the derivatives and inclusions without a case split, and the `_apply_of_le` and
  `_top_apply` variants merge into them.  The topology of `𝓓^{n}_{K}(E, F)` is the infimum over
  the structure maps of order `i ≤ n`, the seminorm family `seminormFamily` and the sup seminorms
  are indexed by these orders, and `continuous_iff_comp_order_le` merges into
  `continuous_iff_comp`.  An operator applied to a function takes its inequality explicitly or is
  parenthesized, as in `(fderivCLM 𝕜 ⊤ ⊤) f`.  Tests cover the removed names, an impossible
  derivative, line derivative, seminorm, and inclusion, and the inequalities found for smooth maps,
  numerals, and hypotheses.

- [x] **Make integration against a kernel take its integrability.**
  `ContDiffMapSupportedIn.integralAgainstBilinLM` and `integralAgainstBilinCLM` take
  `hφ : IntegrableOn φ K μ`, `TestFunction.integralAgainstBilinCLM` takes
  `hφ : LocallyIntegrableOn φ Ω μ`, and `Distribution.ofFun Ω f μ n hf` takes the local
  integrability of `f`; without it they were the zero map
  (`TestFunction.integralAgainstBilinCLM_eq_zero`, `Distribution.ofFun_eq_zero`, and
  `Distribution.ofFun_apply_eq_ite`, removed).  The `_apply` lemmas state the integral without a
  case split, the former `_eq_integral` lemmas merging into them, and `ofFun_add`, `ofFun_neg`, and
  `ofFun_smul` take the local integrability of the summands.  `SchwartzMap.smulLeftCLM F g hg`,
  `TemperedDistribution.smulLeftCLM F g hg`, and the Fourier multipliers
  `SchwartzMap.fourierMultiplierCLM F g hg` and `TemperedDistribution.fourierMultiplierCLM F g hg`
  take the temperate growth of the multiplier, found by `fun_prop` by default, and were the zero map
  without it; an operator applied to a function takes its evidence explicitly or is parenthesized,
  as in `(smulLeftCLM F g) f`.  The sum lemmas `smulLeftCLM_sum` and `fourierMultiplierCLM_sum`
  assume the temperate growth of every member of the family rather than only of the summed ones: the
  exact form needs a sum over `s.attach`, and every consumer sums over `Finset.univ`, where the two
  agree.  `Measure.integrablePower μ` takes `[μ.HasTemperateGrowth]` and is the least natural
  exponent `l` for which `(1 + ‖x‖) ^ (-l)` is integrable (`integrablePower_le`), instead of a
  chosen exponent and `0` without temperate growth.  Tests cover the removed names, a multiplier
  without temperate growth, multipliers found by `fun_prop`, and the least integrable exponent.

- [x] **Require a dense domain for `LinearPMap.adjoint`.**
  `LinearPMap.adjoint T hT` takes `hT : Dense (T.domain : Set E)`, the exact domain of a
  single-valued adjoint: without density the values `⟪y, T x⟫` determine `T† y` only up to the
  orthogonal complement of the domain, and the operator defined only at zero on `𝕜` has both the
  identity and zero as formal adjoints on its adjoint domain.  The former definition returned the
  zero map on `T.adjointDomain` for an operator whose domain is not dense
  (`adjoint_apply_of_not_dense`, removed), and the instance `Star (E →ₗ.[𝕜] E)` took that adjoint of
  every operator; `IsSelfAdjoint.dense_domain` derived density from the junk value.  The instance is
  removed, and `LinearPMap.IsSelfAdjoint A` states that `A` has dense domain and is its own adjoint,
  so `dense_domain`, `adjoint_eq`, and `isClosed` follow from it.  The scoped notation `T†` takes
  the density proof from the local hypotheses and prints the adjoint.  The continuous extension
  `adjointDomainMkCLMExtend` used in the construction also takes the density proof; it is built with
  `ContinuousLinearMap.extend`, whose fallback is recorded below.  The adjoint domain is still
  defined for every `T`, and `mem_adjointDomain_iff` and `mem_adjointDomain_of_exists` replace the
  lemmas `mem_adjoint_domain_iff` and `mem_adjoint_domain_of_exists` stated through `T†.domain`.
  Tests cover the removed names, the failure without density, the missing `Star` instance, the
  notation, self-adjointness of the identity, and the operator defined only at zero.

- [x] **Require dense uniformly inducing embeddings for `ContinuousLinearMap.extend`.**
  `ContinuousLinearMap.extend f e h_dense h_e` takes the density of the range of `e` and its uniform
  inducing property, under which the continuous extension of `f` along `e` exists and is unique
  (`extend_eq`, `extend_unique`); the former definition returned the zero map without them.  The
  consumers pass the evidence: `LinearPMap.adjointDomainMkCLMExtend` (the inclusion of the dense
  domain), the extensions of integrals from simple functions to `L¹` (`setToL1'`, `setToL1`, and
  `L1.integralCLM'`), the extension to a completion, and `opNorm_extend_le`.
  `LinearMap.compLeftInverse` and `LinearMap.extendOfNorm`, which were the zero map without the
  norm estimate `‖f x‖ ≤ C * ‖e x‖` and, for `extendOfNorm`, without the density of the range, take
  the estimate and the density; `compLeftInverse_apply_of_bdd` is renamed `compLeftInverse_apply`,
  and the isometric extensions pass the evidence.  Tests cover the renamed lemma, the missing
  evidence, and the extension along the identity.

- [x] **Make the closure of a partial operator require closability.**
  `LinearPMap.closure f hf` takes `hf : f.IsClosable` and is the operator whose graph is the
  closure of the graph of `f`, unique by `IsClosable.existsUnique`.  The former definition returned
  `f` itself for an operator that is not closable (`closure_def'`, removed with `closure_def`,
  which stated the chosen closure), although the closure of its graph is not a graph, and
  `le_closure` and `closureHasCore` held for every operator through that value; both take the
  closability.  `HasCore f S` states that the restriction of `f` to `S` is closable and that its
  closure is `f`, and the inverse lemmas take the closability of `f` in their statements.  Tests
  cover the removed name, the missing evidence, a closed extension, a closed operator, and the
  core.

- [ ] **Give completion extension its full existence and uniqueness contract.**
  `Mathlib/Topology/UniformSpace/Completion.lean:224` evaluates at an arbitrarily selected point
  when the function is not uniformly continuous.  Uniform continuity removes that branch but does
  not by itself make a continuous extension into the original codomain exist: the continuity
  theorem at line 242 also assumes `CompleteSpace β`, and uniqueness needs the relevant separation
  hypothesis.
  Use completeness as a convenient sufficient interface or carry exact pointwise limit
  existence/uniqueness; do not present uniform continuity alone as the mathematical domain.

- [x] **Make vector-measure products and densities conditional constructions.**
  `VectorMeasure.prod μ ν B` takes `[HasProd μ ν B]`: a vector measure with `B (μ s) (ν t)` on the
  measurable rectangles exists, and it is then unique (`prod_eq_of_forall_apply_prod`), so the
  definition chooses a unique value; finite variation of either factor and a complete target supply
  the instance.  The former definition returned `0` when no product exists
  (`prod_eq_zero_of_not_hasProd`, removed), and `map_prod_swap` and `integral_prod_swap` held for
  every pair through that value; they now assume `HasProd`, as do the scalar Fubini theorems
  `integral_prod_smul`, `integral_prod_smul_symm`, `integral_integral_smul`, and
  `integral_integral_smul_symm`, which allowed an incomplete target.
  `VectorMeasure.withDensity μ f B hf` and `Measure.withDensityᵥ μ f hf`, which returned `0` for a
  nonintegrable `f`, take the integrability of `f`, which is the exact domain: the integral is
  defined on every measurable set exactly when it is defined on the whole space.  Lemmas such as
  `withDensityᵥ_neg`, `withDensityᵥ_smul`, `WithDensityᵥEq.congr_ae`,
  `withDensityᵥ_absolutelyContinuous`, `withDensity_congr`, and `variation_WithDensity_le`, which
  held for every `f` through that value, take the integrability.  The signed Lebesgue decomposition
  states `s.singularPart μ + μ.withDensityᵥ (s.rnDeriv μ) _ = s` with the integrability of the
  Radon--Nikodym derivative; `haveLebesgueDecomposition_mk`, `eq_singularPart`, and `eq_rnDeriv`
  take an integrable density instead of admitting a nonintegrable one through the fallback; and the
  integration-by-parts formula for functions of bounded variation passes the integrability of the
  one-sided limits.  Tests cover the removed lemma, the missing product and integrability, a
  nonintegrable density, and the routine instances.

- [x] **Define the intended domain of generalized `InformationTheory.klDiv`.**
  `klDiv μ ν` takes σ-finite measures `[SigmaFinite μ] [SigmaFinite ν]` and is the I-divergence
  `∫⁻ x, ENNReal.ofReal (klFun (μ.rnDeriv ν x).toReal) ∂ν` if `μ ≪ ν`, with
  `klFun t = t * log t + 1 - t`, and `∞` otherwise.  This is Csiszár's I-divergence of σ-finite
  measures, the `φ`-divergence for `φ t = t * log t - t + 1` (I. Csiszár and F. Matúš, *Generalized
  minimizers of convex integral functionals, Bregman distance, Pythagorean identities*, Kybernetika
  48 (2012), Appendix C, eq. (44), whose standing measure is σ-finite, §1.A), and `∞` off absolute
  continuity is the f-divergence convention, since `φ t / t → ∞`.  The literature measures the
  divergence against a σ-finite reference measure; for σ-finite measures the Radon--Nikodym
  derivative exists and is finite almost everywhere, and the nonnegative integrand needs no
  integrability condition.  The former definition was
  `ENNReal.ofReal (∫ x, llr μ ν x ∂μ + ν.real univ - μ.real univ)` for `μ ≪ ν` with integrable
  log-likelihood ratio, for all measures.  The mass correction agrees with the I-divergence when `ν`
  is finite, but for `ν` of infinite mass `ν.real univ` is `0`, so the divergence of `0` from
  Lebesgue measure, or from counting measure on `ℕ`, was `0` instead of `∞`.  That formula is now
  `klDiv_of_ac_of_integrable` for finite measures, with `klDiv_of_not_integrable`,
  `klDiv_eq_top_iff`, `klDiv_ne_top_iff`, `klDiv_ne_top`, and `klDiv_eq_integral_klFun`, which
  also assume finite measures; `klDiv_eq_lintegral_klFun`, `klDiv_eq_lintegral_klFun_of_ac`, and
  `klDiv_of_not_ac` hold for σ-finite measures, and `klDiv_zero_left`, formerly for finite `ν`,
  gives `ν univ` for every σ-finite `ν`.  The chain rule and data-processing inequalities keep their
  finite-measure hypotheses.  Tests cover the missing σ-finiteness, the divergence of `0` from
  Lebesgue and counting measure, the finite-measure formula, and the divergence of a measure from
  itself.

- [x] **Make `LinearMap.index` carry Fredholm-style finiteness.**
  `LinearMap.index f hf` is defined for linear maps between vector spaces over a division ring that
  are Fredholm, `hf : f.IsFredholm`: the kernel and cokernel are finite-dimensional, and the index
  is `dim ker - dim coker` (J. H. Shapiro, *Algebraic Fredholm theory*, lecture notes, 2011,
  Definitions 4.1 and 4.11; Theorem 5.1 is the composition rule).  The former definition subtracted
  `finrank`s over any ring, so an infinite-dimensional kernel or cokernel counted as `0`: the zero
  map from an infinite-dimensional space to `0` had index `0`.  Division rings are the intended
  scope, since there dimension, rank, and length agree; over general rings they give different
  indices for the same map (multiplication by `2` on `ℤ` has rank index `0` and length index `-1`),
  so a rank- or length-based index would be a separate object, and the ring-level lemmas
  `index_of_subsingleton` and those under `StrongRankCondition` are removed.  The lemmas take
  `IsFredholm` evidence, and constructors supply it for finite-dimensional spaces, injective and
  surjective maps with finite-dimensional cokernel and kernel, bijections, negation, nonzero
  scalars, and compositions.  A topological Fredholm operator is Fredholm as a linear map
  (`ContinuousLinearMap.IsFredholm.toLinearMap`), `ContinuousLinearMap.index T hT` is its index,
  `IsFredholm.index_comp` keeps the composition rule, and the local constancy of the index is
  stated on the subtype of Fredholm operators (`continuous_index`) instead of as continuity of a
  total function.  Tests cover the zero map from an infinite-dimensional space, the removed names,
  and composition.

- [x] **Define the intended module-level and vector-space Euler characteristics separately.**
  `GradedObject.eulerChar c X hX` takes `hX : GradedObject.HasFiniteRank X`: every object has finite
  rank and only finitely many objects have nonzero rank.  This is the domain of the alternating sum
  of ranks: finite support of the `finrank` summands rather than finite support of the objects,
  since torsion modules have genuine rank `0`, and finite rank of every object, since an object of
  infinite rank has no rank to add.  The ring is required to satisfy `HasRankNullity`, so that rank
  is additive on short exact sequences, as over division rings and commutative domains; over `ℤ`
  this is the alternating sum of ranks of abelian groups used for the Euler characteristic of a
  space.  The homological wrappers take the same evidence for the terms or for the homology.  The
  former definition took `finsum` of the signed `finrank`s over any ring, so a graded module with
  infinite rank support had Euler characteristic `0` and an object of infinite rank contributed
  `0`.  The value is now a finite sum over the finite rank support, and
  `eulerChar_eq_sum_finSet_of_finrankSupport_subset` computes it over any finite set containing
  that support.  Over a division ring `hasFiniteRank_iff_finiteDimensional` identifies the domain
  with finite total dimension, so the Euler characteristic is the alternating sum of dimensions of
  a graded vector space of finite total dimension.  The module overview's claim that every module
  not free of finite rank received `0` was false (`ℚ` has `finrank` one over `ℤ`) and is replaced by
  this description.  The file has no consumers.  Tests cover a graded vector space, an infinite
  rank support, an object of infinite rank, and the vector-space characterization.

- [x] **Require a finite residue field for elliptic local factors.**
  `WeierstrassCurve.localPolynomial`, `localPowerSeries`, and `localEulerFactor` require
  `[Finite (IsLocalRing.ResidueField R)]`.  Serre, *Facteurs locaux des fonctions zêta des variétés
  algébriques*, Sém. Delange--Pisot--Poitou 11 (1969/70), Exp. 19, defines the local polynomial
  as `det(1 - πT)` on the inertia invariants, where the geometric Frobenius `π` is the inverse of
  the canonical Frobenius generator, which he defines for a finite residue field (§2.2, (13)); this
  covers every reduction type, and the Euler factor substitutes `Nv⁻ˢ` with `Nv = Card(k(v))`
  (§1.2).  For an infinite residue field `q` was `0`, so the Euler factor reached the
  `ofPowerSeries` fallback and was `1`, and the good-reduction coefficients were not the local
  factor of any place.  Completeness of `R` is not required.  The completed integers of a ring with
  finite quotients have a finite residue field, identified with `A ⧸ v` by
  `adicCompletionIntegers.quotientAlgEquivResidueField`, so its size is the absolute norm and
  `WeierstrassCurve.LFunction` needs no new residue-field hypothesis.  `Finite W.Point` over a
  finite ring makes the point count a count of a finite type.

- [x] **Require an elliptic curve for elliptic local factors.**
  The local factors, `WeierstrassCurve.LFunction`, and `WeierstrassCurve.LSeries` also require
  `[W.IsElliptic]`.  The local polynomial applies its formula to `W.minimal R`, a
  `Classical.choose`, and for a singular curve the minimal models need not agree: for the nodal
  cubic `y² + xy = x³` every integral model is minimal, and the model and its rescaling by a
  uniformizer have multiplicative and additive reduction, so the local polynomial had degree one
  or zero depending on the choice.  Serre's local factors are those of an elliptic curve (§2.4,
  (16) and (17)).  `(W.baseChange A).IsElliptic` is an instance, so the global L-function needs only
  `[W.IsElliptic]`.

- [x] **Prove that elliptic local factors do not depend on the chosen minimal model.**
  `WeierstrassCurve.localPolynomial` applies its formula to `W.minimal R`, a `Classical.choose`.
  For an elliptic curve a change of variables between two minimal Weierstrass equations has
  `u ∈ Rˣ` and `r, s, t ∈ R` (`variableChange_integral_of_isMinimal`): minimality makes the
  discriminant valuations equal, and `Δ ≠ 0` then forces `v(u) = 1`.  Such a change preserves the
  reduction type, including the splitting of `nodePolynomial`, which transforms by `T ↦ uT + s` up
  to the unit `u⁶`, and the number of points of the reduction, through
  `Affine.Point.variableChangeEquiv`.  Hence `localPolynomial_eq_of_isMinimal` computes the local
  polynomial from any minimal Weierstrass equation, so the chosen model is only a representative,
  and the local polynomial, Euler factor, L-function, and L-series are invariant under changes of
  variables.

- [x] **Compare elliptic local factors over `R` and its completion, and audit the split criterion.**
  `localPolynomial_baseChange_adicCompletion`, `localPowerSeries_baseChange_adicCompletion`, and
  `localEulerFactor_baseChange_adicCompletion` prove equality over an arbitrary discrete valuation
  ring with finite residue field and its actual adic completion.  Minimality survives completion
  by density: a change of variables yielding an integral equation can be approximated over the
  original fraction field with the same discriminant valuation.  The canonical residue-field
  isomorphism preserves the reduction type and point count.
  `hasSplitMultiplicativeReduction_iff_exists_tangentSlopes` proves that, at a singular point of a
  multiplicative reduction, splitting of `nodePolynomial` is equivalent to two distinct rational
  tangent slopes, including in characteristics 2 and 3.  Tate, *The arithmetic of elliptic curves*
  (1974), §2, p. 182, (9), identifies the smooth locus with the torus using the ratio of the tangent
  lines; §6, p. 191, identifies it with the connected component of the special fibre.  This agrees
  with Serre's split torus and the factors `1 - T` and `1 + T` (§2.4(b), (17)).  The rational node's
  existence and the algebraic-group/Néron-model identifications are source-audited geometric facts;
  the formalization proves the tangent criterion at a given singular point, not those geometric
  constructions.  Regression tests cover split and nonsplit nodes over both `ZMod 2` and `ZMod 3`,
  a translated node, and the failure of the criterion when `c₄ = 0`.

- [x] **Make analytic and meromorphic orders domain-bearing.**
  `analyticOrderAt f z₀ hf` in `Mathlib/Analysis/Analytic/Order.lean` takes
  `hf : AnalyticAt 𝕜 f z₀`, and `meromorphicOrderAt f x hf` in
  `Mathlib/Analysis/Meromorphic/Order.lean` takes `hf : MeromorphicAt f x`; `fun_prop` supplies both
  by default.  Neither has a value outside its domain, and a function that vanishes locally has
  order `⊤`.  The natural-number order `analyticOrderNatAt`, which sent infinite order to `0`, is
  removed with its lemmas; `AnalyticAt.analyticOrderAt_ne_top` states finite order with a natural
  number `n` and the equation `analyticOrderAt f z₀ hf = n`.  The fallback lemmas
  `analyticOrderAt_of_not_analyticAt`, `meromorphicOrderAt_of_not_meromorphicAt`, the
  hypothesis-free `analyticOrderAt_eq_zero` and `analyticOrderAt_ne_zero`,
  `meromorphicAt_of_meromorphicOrderAt_ne_zero`, and `analyticOrderAt_smul_eq_top_of_left`,
  `analyticOrderAt_mul_eq_top_of_left`, and their right versions are removed, and the lemmas that
  held only through the fallback take the analyticity or meromorphy hypothesis.  An order term
  carries its proof, so a rewrite of the function or the point inside it goes through
  `analyticOrderAt_congr`, `meromorphicOrderAt_congr`, or `congr`.  Statements quantified over a set
  name the membership binder, as in `∀ u (hu : u ∈ U), meromorphicOrderAt f u (hf u hu) ≠ ⊤`: the
  hypothesis of an anonymous `∀ u ∈ U` binder is not in scope for the default argument.  With
  `MeromorphicOn.meromorphicAt`, `fun_prop` derives `MeromorphicAt f x` from `MeromorphicOn f U` and
  `x ∈ U`.  Tests cover the removed names, the default argument, the failure without a hypothesis,
  and infinite order.

- [ ] **Make the divisor of a meromorphic function domain-bearing.**
  `MeromorphicOn.divisor f U` in `Mathlib/Analysis/Meromorphic/Divisor.lean` is `0` when `f` is not
  meromorphic on `U` (`divisor_eq_zero_of_not_meromorphicOn`) and, through `WithTop.untop₀`, at the
  points where `f` vanishes locally, whose order is `⊤`.  The divisor is defined for a function that
  is meromorphic on `U` and has finite order at every point of `U`.  Take these as arguments and
  migrate the consumers: `divisor_const`, `divisor_inv`, and `divisor_const_smul` hold without
  hypotheses only through these values, and the logarithmic counting function, the characteristic
  function, Jensen's formula `MeromorphicOn.circleAverage_log_norm`, and the canonical
  decompositions of `Mathlib/Analysis/Complex/CanonicalDecomposition.lean` use the divisor.

- [ ] **Make the trailing coefficient and the normal-form conversions domain-bearing.**
  `meromorphicTrailingCoeffAt f x` in `Mathlib/Analysis/Meromorphic/TrailingCoefficient.lean` is `0`
  when `f` is not meromorphic at `x` (`meromorphicTrailingCoeffAt_of_not_MeromorphicAt`) and when
  `f` vanishes locally at `x` (`MeromorphicAt.meromorphicTrailingCoeffAt_of_order_eq_top`), where no
  coefficient is nonzero.  `toMeromorphicNFAt f x` and `toMeromorphicNFOn f U` in
  `Mathlib/Analysis/Meromorphic/NormalForm.lean` are the zero function when `f` is not meromorphic
  (`toMeromorphicNFAt_of_not_meromorphicAt`, `toMeromorphicNFOn_of_not_meromorphicOn`).  Lemmas such
  as `meromorphicTrailingCoeffAt_inv`, `meromorphicTrailingCoeffAt_neg`, and the translation lemmas
  hold without hypotheses only through these values.  Take meromorphy, and finite order for the
  trailing coefficient, as arguments, and migrate the consumers, including
  `circleIntegrable_log_meromorphicTrailingCoeffAt` in
  `Mathlib/Analysis/Complex/ValueDistribution/Cartan.lean`, which covers non-meromorphic functions
  through these values.

## L -- staged cross-module audit candidates

- [ ] **Put matroid closure on subsets of the ground set.**
  `Matroid.closure` in `Mathlib/Combinatorics/Matroid/Closure.lean:135` deliberately extends closure
  to every `Set α` by replacing `X` with `X ∩ M.E`; the module describes off-ground inputs as junk,
  and the resulting operation is not extensive on all `Set α`.  Reuse `Matroid.subtypeClosure` at
  line 116 to make the ordinary closure domain-bearing, or prototype an equally faithful proof-last
  interface.  Keep the intersection convention private unless literature supports it as a public
  closure operation.  The current surface has roughly 258 `M.closure` matching lines across
  nine maintained files, so migrate the closure theorem family and its rank, minor, circuit, and loop
  consumers as one staged change.

- [ ] **Require integrality for `minpoly`.**
  `Mathlib/FieldTheory/Minpoly/Basic.lean:41` assigns polynomial zero to a nonintegral element;
  `minpoly.aeval` at line 89 then states unconditionally that every element is a root of its minimal
  polynomial.  Put `IsIntegral` in the ordinary construction and theorem family.  If the zero branch
  is temporarily needed to implement bridges, keep it private and prove it unreachable at the
  public boundary.

- [ ] **Replace finite separable/inseparable degree projections outside their domains.**
  `Field.finSepDegree` in `Mathlib/FieldTheory/SeparableDegree.lean:141` uses `Nat.card` even for a
  nonalgebraic extension, and `Field.finInsepDegree` in
  `Mathlib/FieldTheory/SeparableClosure.lean:281` inherits `finrank`'s infinite-to-zero behavior.
  Require the correct algebraicity/finite-degree evidence or expose cardinal-valued invariants.

- [ ] **Make rational-function evaluation reject poles.**
  `RatFunc.eval` in `Mathlib/FieldTheory/RatFunc/AsPolynomial.lean:143` evaluates a pole to zero and
  consequently fails ring laws there.  Require regularity/denominator nonzeroness at the point, while
  respecting reduced-rational-function rather than source-expression semantics.

- [ ] **Put finite factorization data on nonzero inputs.**
  `Nat.factorization` in `Mathlib/Data/Nat/Factorization/Defs.lean:50` gives zero multiplicities at
  zero, and `Nat.primeFactors` in `Mathlib/Data/Nat/PrimeFin.lean:37` gives the empty set although
  every prime divides zero.  The generic `factorization` and `normalizedFactors` in
  `Mathlib/RingTheory/UniqueFactorizationDomain/Finsupp.lean:32` and
  `Mathlib/RingTheory/UniqueFactorizationDomain/NormalizedFactors.lean:35` likewise return empty
  data at zero.  Use a nonzero carrier or explicit failure for finite lists/counts; keep units
  admissible with empty factorization.  `Associates.factors` returns `⊤` at zero
  (`Mathlib/RingTheory/UniqueFactorizationDomain/FactorSet.lean:223`), which is a useful internal
  extended-value precedent but not literature evidence for a public convention.  `Nat.ordProj` and
  `Nat.ordCompl` in `Mathlib/Data/Nat/Factorization/Defs.lean` inherit the convention, with
  `ordProj 0 p = 1` and `ordCompl 0 p = 0`; their lemmas without a nonzero hypothesis, such as
  `Nat.ordProj_pos` and `Nat.factorization_ordCompl`, hold at `0` through it and move with this
  migration.

- [ ] **Migrate natural cardinalities away from infinity-to-zero.**
  `Nat.card` in `Mathlib/SetTheory/Cardinal/Finite.lean:41` and `Set.ncard` in
  `Mathlib/Data/Set/Card.lean:613` return zero on infinite inputs.  Require `Finite α`/`s.Finite` for
  natural values and use `ENat.card`/`Set.encard` globally.

- [ ] **Make lossy extended-value conversions checked and keep zero fallbacks private.**
  `ENat.toNat` (`Mathlib/Data/ENat/Basic.lean:118`), `Cardinal.toNat`
  (`Mathlib/SetTheory/Cardinal/ToNat.lean:31`), and `ENNReal.toNNReal`/`toReal`
  (`Mathlib/Basic/ENNReal/Basic.lean:225`) send infinity to zero.  Provide proof-bearing finite
  conversions and keep infinity-to-zero maps private; a more explicit public name does not prevent
  their accidental use as genuine conversions.

- [ ] **Separate chosen preimages from true inverses and true extensions.**
  `Function.invFun` in `Mathlib/Logic/Function/Basic.lean:526` picks an arbitrary element outside
  the range and a chosen preimage for noninjective maps.  Use equivalences/bijections for inverse
  functions.  A chosen-preimage construction may remain public only as a separately sourced
  mathematical choice operator, not as an inverse fallback.
  `Function.extend` in the same file at line 835 explicitly takes an outside-range fallback, but
  explicitness alone does not make it a faithful extension.  Without `g.FactorsThrough f` it chooses
  one representative's `g`-value for a fiber and cannot agree with every original `g`-value on that
  fiber.  Require `FactorsThrough` for
  the ordinary extension name.  Keep an unrestricted chosen-representative construction private
  unless literature treats that choice operation itself as the intended public object.

- [ ] **Make subgroup indices finite only with evidence.**
  `Subgroup.index` and `Subgroup.relIndex` in `Mathlib/GroupTheory/Index.lean:57` and `:64` return
  zero for infinite index.  Keep a cardinal/extended index globally and require finite index for the
  natural projection.

- [ ] **Require prime and finite local data for ramification and inertia degrees.**
  `Ideal.ramificationIdx` and `Ideal.inertiaDeg` in
  `Mathlib/RingTheory/RamificationInertia/Ramification.lean:52` and
  `Mathlib/RingTheory/RamificationInertia/Inertia.lean:44` return zero for nonprime ideals and also
  collapse infinite length/rank.  Carry primality plus the appropriate finiteness evidence, or keep
  an extended-valued invariant.

- [ ] **Put affine combinations on affine weights.**
  `Finset.affineCombination` in `Mathlib/LinearAlgebra/AffineSpace/Combination.lean:348` accepts
  arbitrary weights and chooses a base point; only weights summing to one give the intrinsic affine
  combination.  Use the affine-weight hyperplane or a sum-one proof.  A basepoint-dependent operation
  is public only if independently supported as a mathematical construction, not merely because it
  can be given a descriptive name.

- [ ] **Separate pointwise vector-field pullback from regularity theorems.**
  `VectorField.mpullbackWithin`/`mpullback` in
  `Mathlib/Geometry/Manifold/VectorField/Pullback.lean:100` and `:107` return zero when the
  derivative is noninvertible.  `mlieBracketWithin`/`mlieBracket` in
  `Mathlib/Geometry/Manifold/VectorField/LieBracket.lean:63` and `:73` accept fields without the
  differentiability needed by the mathematical bracket.  For one point and one target vector, the
  exact contract is existence and uniqueness of a vector related by the derivative; the derivative
  need not be an isomorphism.  An invertible derivative gives a pullback operator for every target
  vector, and a local diffeomorphism is a still stronger convenient facade.  Keep these pointwise,
  operator-level, local-regularity, and globally differentiable interfaces distinct, and put bracket
  regularity in the theorem or bundled object that actually uses it.

- [ ] **Audit and strictify local-frame/trivialization evaluation at its public boundary.**
  `IsLocalFrameOn.coeff` in
  `Mathlib/Geometry/Manifold/VectorBundle/LocalFrame.lean:186` returns zero outside the frame's set;
  pretrivializations/trivializations in `Mathlib/Topology/FiberBundle/Trivialization.lean:69` also
  expose chosen ambient values.  Require base-set membership for ordinary coordinate/evaluation
  names.  Keep globally defined implementation representatives private and only behind proofs that
  their off-domain values cannot affect public results.

- [ ] **Audit the choice-based `Filter.lim` projection and its theorem boundaries.**
  `Filter.lim` and `Filter.limUnder` in `Mathlib/Topology/Defs/Filter.lean:255` and `:260` use
  `Classical.epsilon` and choose a point satisfying the limit relation when one exists.  This is a
  choice projection, not by itself a false mathematical statement.  Inventory whether any public
  theorem omits convergence, separation, or nontrivial-filter hypotheses.  Retaining the ordinary
  `lim` name for a value at nonconvergent filters additionally requires literature using the same
  total convention; otherwise expose the choice only behind existence evidence and keep any
  fallback private.  Audit `IsDenseInducing.extend`/`extendFrom` under the same distinction between
  a chosen representative and a claimed canonical extension.

- [x] **Make measure pushforward require a.e. measurability.**
  `Measure.map` now takes a proof of a.e. measurability, normally synthesized by `fun_prop`, and
  `Measure.mapₗ` likewise requires measurability.  The arbitrary-Dirac and zero fallbacks were
  removed rather than retained under ordinary mathematical names.  The migration covers the
  existing ecosystem together with `Measure.bind`, `Measure.prod`, `FiniteMeasure.map`,
  `ProbabilityMeasure.map`, conditional-law APIs, and kernel map wrappers.  Negative tests ensure
  arbitrary functions cannot recover the former behavior, while proof-indexed congruence,
  measurable-set-first `map_apply`, and a.e.-measurable `map_map` preserve routine ergonomics.

- [x] **Separate unique product measures from iterated and primitive constructions.**
  `IsProductMeasure` records the measurable rectangle law; ordinary `Measure.prod` requires
  `HasUniqueProduct`. Sigma-finite, zero, and singleton cases supply routine evidence.
  `Measure.primitiveProd` constructs the maximal product for arbitrary factors, while
  `Measure.productBySections` uses scalar section measurability and retains the s-finite Tonelli theory.
  Finite/probability interfaces use the unique product, and genuinely s-finite consumers select
  the iterated construction explicitly. The formal infinity-scaled Lebesgue counterexample
  separates the constructions and disproves uniqueness from s-finiteness alone.

- [x] **Require one-sided linear inverses for formal multilinear one-sided inverses.**
  `FormalMultilinearSeries.leftInv p r hr x` and `rightInv p s hs x` take a continuous linear left,
  respectively right, inverse of the linear term `p₁` with `Function.LeftInverse` or
  `Function.RightInverse` evidence, replacing an equivalence `i` that only the inverse laws tied to
  `p 1`; the zero-series counterexample is no longer constructible. Comparing linear terms gives the
  exact existence domains, `exists_comp_eq_id_iff_hasLeftInverse` and
  `exists_comp_eq_id_iff_hasRightInverse` through `ContinuousLinearMap.HasLeftInverse` and
  `HasRightInverse`, so an invertible linear term is not required. Both predicates now live in
  `Mathlib/Topology/Algebra/Module/ContinuousLinearMap/OneSidedInverse.lean`, split from the
  finite-dimensional and Banach criteria so that analytic modules need not import those. One-sided
  inverses of a noninvertible linear term need not be unique, and the linear inverse selects one,
  characterized among the formal one-sided inverses with the given constant coefficient: the left
  inverse is the one whose coefficients depend on their vector arguments only through their images
  under `r` (`leftInv_compContinuousLinearMap`,
  `eq_leftInv_of_comp_eq_id_of_compContinuousLinearMap_eq`), and the right inverse the one whose
  coefficients of positive order take values in the range of `s` (`rightInv_apply_mem_range`,
  `eq_rightInv_of_comp_eq_id_of_apply_mem_range`). With both linear inverses, `leftInv_eq_rightInv`,
  `eq_rightInv_of_comp_eq_id_left`, and `eq_leftInv_of_comp_eq_id_right` give coincidence and
  uniqueness for each constant coefficient. The constructed inverses converge when `p` does, left
  inverses of split injective linear terms included, although other formal one-sided inverses of a
  noninvertible linear term can have radius zero. `OpenPartialHomeomorph.hasFPowerSeriesAt_symm`
  assumes only a continuous linear left inverse, which its conclusion then shows to be two-sided.
  Tests cover missing and invalid evidence, the former counterexample, nonzero constants, injective
  and surjective noninvertible linear terms with nonunique inverses, a zero-dimensional domain,
  proof independence, the characterizations, uniqueness, convergence, and the analytic inverse.

- [x] **Classify formal multilinear composition as composition at matching basepoints.**
  `FormalMultilinearSeries.comp` reads the outer series as an expansion at the constant coefficient
  `p 0 0` of the inner series; a formal series does not record its own expansion point. For real
  finite-dimensional spaces, on the diagonal and at each finite order, this is the composition of
  jets of Kolář, Michor, and Slovák, *Natural operations in differential geometry*, §12.3, in the
  coordinates of §12.6, where the target of the inner jet is the source of the outer one; over a
  general field and normed spaces it is the same convention as `HasFPowerSeriesAt.comp`. Every pair
  of series is composable in this sense, so the ignored inner constant is not a fallback and no
  zero-constant condition applies; `HasFPowerSeriesAt.comp`, `HasFiniteFPowerSeriesAt.comp`,
  `CPolynomialAt.comp`, and the inverse theory all use matching basepoints. Substitution into a
  series expanded at the same origin is a different operation: it would re-expand the outer series
  around `p 0 0`, as `FormalMultilinearSeries.changeOrigin` does within the ball of convergence,
  and in general disagrees with `comp`, already for polynomials. `id 𝕜 E x` is the expansion of the
  identity at `x`, a right identity for every `x` and a left identity exactly for a matching
  constant. The documentation now states this convention, and tests pin a matched analytic
  composition, independence from the inner constant, the polynomial substitution example, and the
  identity laws.

- [ ] **Make `NormedSpace.exp` require its algebra and convergence context.**
  `Mathlib/Analysis/Normed/Algebra/Exponential.lean:127` returns one if no `Algebra ℚ 𝔸`
  exists and otherwise delegates to a power-series sum without encoding summability in the
  operation.  Require the scalar-algebra data and the analytic conditions actually used.

- [ ] **Make ordinary L-series evaluation conditional on summability.**
  `LSeries` in `Mathlib/NumberTheory/LSeries/Basic.lean:164` inherits zero for nonsummable series
  from `tsum`.  Use `LSeriesHasSum`/`LSeriesSummable` at the public evaluation boundary and audit
  specializations, including zeta at its pole.

- [ ] **Strictify the separate box-integral ecosystem.**
  `BoxIntegral.integral` in `Mathlib/Analysis/BoxIntegral/Basic.lean:176` returns zero for a
  nonintegrable function.  Make integrability for the chosen integration parameters part of the
  ordinary operation.

- [ ] **Separate finite `lpNorm`/variance from extended or nonexistent values.**
  `MeasureTheory.lpNorm` in `Mathlib/MeasureTheory/Function/LpSeminorm/Defs.lean:142` maps
  non-a.e.-strongly-measurable or infinite-norm functions to zero.  `ProbabilityTheory.variance` in
  `Mathlib/Probability/Moments/Variance.lean:64` maps infinite variance to zero and centers through
  totalized expectation.  Use `MemLp`/moment hypotheses for finite values and design extended values
  without a junk mean.

- [x] **Replace chosen conditional kernels and conditional cdfs by their almost-everywhere
  classes.**
  The specification of a conditional kernel, `ρ.fst ⊗ₘ η = ρ` or `fst κ ⊗ₖ η = κ`, determines `η`
  only up to `ρ.fst`-null sets, respectively up to `fst κ a`-null sets for every `a`, and the same
  holds for conditional cdfs.  `Kernel.AEClass l β` in `Mathlib/Probability/Kernel/AEClass.lean` is
  the type of kernels modulo eventual equality along a filter `l`, with a membership of
  representatives, and every class has a representative.  `Measure.condKernel ρ` is the class
  along `ae ρ.fst` and `Kernel.condKernel κ` the class along `(fst κ).fiberwiseAE` of the Markov
  kernels that disintegrate; each is obtained from a class-level existence statement whose solution
  is unique, and a Markov representative exists.  Finite conditional kernels with values in a
  countably generated space are unique almost everywhere (`IsCondKernel.ae_eq`), so a finite kernel
  represents these classes exactly when it satisfies `IsCondKernel` (`mem_condKernel_iff`).
  `condDistrib Y X μ` is the class along `ae (μ.map X)` of the conditional kernel of the joint law,
  and a finite kernel represents it exactly when it satisfies `HasCondDistrib`
  (`mem_condDistrib_iff_hasCondDistrib`).  `posterior κ μ` is the class along `ae (κ ∘ₘ μ)` of the
  conditional kernel of the joint law with swapped coordinates.  `condExpKernel μ hm` now takes the
  proof `hm : m ≤ mΩ` that `m` is a sub-σ-algebra and is the class along `ae (μ.trim hm)` of the
  kernels that disintegrate the diagonal law.  The Markov instances of the former chosen kernels,
  their measurability lemmas, their `_apply` and `_eq` equations, and the lemmas comparing a kernel
  with a chosen one are removed; `Kernel.comap_mem_condKernel_of_mem` replaces
  `Kernel.condKernel_apply_eq_condKernel`.  In `Integral.lean`, `Unique.lean`, `CondDistrib.lean`,
  `Condexp.lean`, `Posterior.lean`, `BayesEstimator.lean`, and `IonescuTulcea/Traj.lean`, statements
  about the classes hold for every representative, statements about the values of a representative
  hold for every Markov representative or, where the proof allows, for every finite or s-finite one,
  and the integrals of `Integral.lean` hold for every s-finite kernel that satisfies
  `IsCondKernel`.  Lemmas whose conclusion became a membership are named accordingly, for example
  `id_mem_condDistrib_self` and `id_mem_posterior_id`.  Conditional independence, the conditionally
  sub-Gaussian moment generating function, and `ZeroOne.lean` quantify over the representatives of
  `condExpKernel μ hm`; since kernel independence and `Kernel.HasSubgaussianMGF` are invariant under
  almost-everywhere equality, `condIndep_iff_of_mem` and its variants and
  `hasCondSubgaussianMGF_iff_of_mem` reduce them to any single representative.
  `condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight`, which compared two chosen kernels, became
  the membership statement `condIndepFun_iff_prodMkRight_mem_condDistrib`, and
  `IsArgminEstimator.of_mem` checks an argmin estimator on one representative of the posterior.
  The conditional cdfs were done first: `condCDF ρ` is the germ along `ae ρ.fst` of the
  conditional cdfs and `Kernel.condKernelCDF κ` their germ along `(fst κ).fiberwiseAE`, the filter
  of properties that hold `fst κ a`-almost everywhere for every `a`.  `Filter.Germ` has a
  membership of representatives (`Mathlib/Order/Filter/Germ/Representative.lean`), each germ is
  obtained from a germ-level existence statement whose solution is unique, the lemmas about the
  chosen representatives are stated for every solution of `IsCondCDF` or `IsCondKernelCDF`, and
  `condKernelReal` and `condKernelUnitReal`, which serve only existence proofs, are private.  The
  finite-measure and finite-kernel domains are unchanged; the item on the exact domain of
  `Measure.condKernel` and `condDistrib` above keeps that question open.  Tests cover the removed
  surfaces, membership, the existence and uniqueness of representatives, the value of every
  representative at an atom, two representatives that differ off the atom, the rejection by every
  class of a kernel that is wrong on a set of positive measure, the identity kernel as the
  conditional expectation kernel given the full σ-algebra, the reduction of conditional independence
  and of the conditionally sub-Gaussian property to one representative, and the sub-σ-algebra and
  finite-measure domains.

- [x] **Stop choosing an argmin estimator from its existence.**
  `HasArgminEstimator.argminEstimator` in `Mathlib/Probability/Decision/BayesEstimator.lean` took
  `Classical.choose` of `HasArgminEstimator.exists_isArgminEstimator`.  The argmin estimators of a
  problem need not agree almost everywhere, so they do not even form an equivalence class, and
  `h.argminEstimator` presented one of them as data attached to the problem, a canonical choice
  that the specification does not provide; `FORK_DESIGN.md` states that existence does not turn a
  chosen witness into canonical data.  It and `isArgminEstimator_argminEstimator` are removed.
  `HasArgminEstimator.bayesRisk_eq`, their only consumer, obtains an argmin estimator from the
  existence statement, and constructions from an argmin estimator, such as
  `IsArgminEstimator.kernel`, take it as an argument.  Tests pin the removed names and compute the
  Bayes risk without a chosen estimator.

- [ ] **Replace chosen almost-everywhere representatives elsewhere in measure theory by their
  classes.**
  `Measure.rnDeriv` in `Mathlib/MeasureTheory/Measure/Decomposition/Lebesgue.lean:80` chooses a
  representative from the Lebesgue decomposition, and `condExp` in
  `Mathlib/MeasureTheory/Function/ConditionalExpectation/Basic.lean:102` takes
  `AEStronglyMeasurable.mk` of `condExpL1`; both objects are determined only almost everywhere.
  Audit them, their signed and vector-measure variants, and other public `Classical.choose` or
  `AEStronglyMeasurable.mk` representatives under the equivalence-class rule of `FORK_DESIGN.md`,
  coordinating with the domain items for conditional expectations and Radon--Nikodym data below.
  `Kernel.density` is a `limsup` formula rather than a choice and is outside this item.

- [ ] **Make conditional expectations carry their measure-theoretic hypotheses.**
  `condExp` in `Mathlib/MeasureTheory/Function/ConditionalExpectation/Basic.lean:102` and
  `condLExp` in `Mathlib/MeasureTheory/Function/ConditionalLExpectation.lean:73` return zero when the
  sigma algebra is not subordinate or the restricted measure is not sigma-finite; `condExp`
  additionally returns zero when integrability fails.  Preserve `condLExp`'s genuine extended
  nonnegative values, bundle the sigma-algebra/measure evidence, and require integrability only for
  the finite Bochner-valued construction.

- [x] **Require measurable random variables for conditional distributions.**
  `ProbabilityTheory.condDistrib` now requires joint a.e. measurability of `fun a ↦ (X a, Y a)`,
  normally synthesized by `fun_prop`; the conditional distribution is the class of its versions,
  which may differ on null conditioning fibres.

- [x] **Require measurability in `Kernel.map`.**
  `Kernel.map` now takes a measurability proof, normally synthesized by `fun_prop`; the zero fallback
  and the separate `mapOfMeasurable` constructor were removed.

- [x] **Give the kernel products their exact domains.**
  `μ ⊗ₘ κ`, `κ ⊗ₖ η`, `κ ∥ₖ η`, and `κ ×ₖ η` integrate the measures of sections:
  `(μ ⊗ₘ κ) s = ∫⁻ a, κ a (Prod.mk a ⁻¹' s) ∂μ` on measurable `s`, `(κ ⊗ₖ η) a = κ a ⊗ₘ sectR η a`,
  `(κ ∥ₖ η) x = κ x.1 ⊗ₘ const β (η x.2)`, and `κ ×ₖ η = κ ⊗ₖ prodMkRight β η`.  They were zero
  unless both inputs were s-finite, a sufficient condition rather than the domain: on `ℝ`,
  `count ⊗ₘ const ℝ (dirac 0)` is counting measure on the horizontal axis although counting measure
  is not s-finite, and on a space with measurable singletons `dirac x ⊗ₘ κ` exists for every `κ`.  A
  section-measure function need not be measurable, and for such a function `∫⁻` is the lower
  integral, so the section integrals determine a value without a convention exactly when, for every
  measurable set, the measures of its sections have a measurable majorant with the same integral,
  that is, equal lower and upper integrals.  `Measure.HasCompProd μ κ` is that class; the section
  integrals are then countably additive (`HasCompProd.lintegral_iUnion`), hence the values of a
  unique measure, and `μ ⊗ₘ κ` is defined from them.  Countable additivity of the lower integrals
  alone is not taken as the domain: outside the class the value depends on choosing the lower
  integral, and Tonelli's theorem is not known there.  `Kernel.HasCompProd κ η` and
  `Kernel.HasParallelComp κ η` ask for the pointwise class and measurability of the section
  integrals in the point.  `κ ×ₖ η` takes the domain `κ.HasCompProd (prodMkRight β η)`, which can be
  strictly larger than that of `(κ ∥ₖ η) ∘ₖ copy α` (paper proof): on `Bool`, let `κ true` be
  Lebesgue measure, `η false = Σ_{t ∈ T} dirac t` for a set `T ⊆ [0, 1]` that is not Lebesgue
  measurable, and the other values zero; then `κ ×ₖ η` exists, but `κ ∥ₖ η` does not, because
  against `volume ⊗ₘ const ℝ (η false)` the section-measure function of the diagonal is the
  indicator of `T`, whose lower and upper integrals are the inner and outer measures of `T`.  The
  class contains every input whose section-measure functions are almost everywhere measurable
  (`HasCompProd.of_aemeasurable`), and instance search finds it for an s-finite kernel and every
  measure, for two s-finite kernels in the kernel products, for zero kernels and measures, and for
  Dirac and counting measures on spaces with measurable singletons (`Measure.hasCompProd_count`).
  One s-finite kernel is not enough (paper proofs): with `ν = Σ_{t ∈ T} dirac t` for a non-Borel
  `T ⊆ ℝ`, the section integrals of `const ℝ ν ⊗ₖ deterministic (fun p ↦ decide (p.1 = p.2))` and of
  `Kernel.id ⊗ₖ const (ℝ × ℝ) ν` on the diagonal are the indicator of `T`, which is not measurable.
  The fallback lemmas `Kernel.compProd_of_not_isSFiniteKernel_left` and `_right`,
  `parallelComp_of_not_isSFiniteKernel_left` and `_right`, `prod_of_not_isSFiniteKernel_left` and
  `_right`, `Measure.compProd_of_not_sfinite`, and `Measure.compProd_of_not_isSFiniteKernel` are
  removed, and the instances `IsSFiniteKernel (κ ⊗ₖ η)`, `IsSFiniteKernel (κ ∥ₖ η)`,
  `IsSFiniteKernel (κ ×ₖ η)`, and `SFinite (μ ⊗ₘ κ)`, which held for every input only through the
  zero value, now assume s-finite inputs: `count ⊗ₘ const ℝ (dirac 0)` is not s-finite.
  `IsCondKernel` now carries the domain of its composition-product, and
  `IsCondKernel.isSFiniteKernel`, proved from the fallback, is removed because it is false: the
  kernel that is counting measure at `0` and `dirac 0` elsewhere is a conditional kernel of a
  nonzero measure and is not s-finite (`Counterexamples/KernelCompProd.lean`).  `IsDeterministic κ`
  now carries `κ.HasParallelComp κ`, and its s-finiteness, formerly derived through the fallback, is
  proved from the defining equation: on rectangles it gives `κ a (s ∩ t) = κ a s * κ a t`
  (`IsDeterministic.measure_inter_eq_mul`), so every value is a zero-one measure, possibly zero, or
  `∞` times a zero-one probability measure, and the kernel is the sum of the finite kernel
  `s ↦ min (κ a s) 1` and countably many copies of it restricted to the points of infinite total
  mass.  `partialTraj κ` and `lmarginalPartialTraj κ` take `∀ n, IsSFiniteKernel (κ n)`, a
  sufficient condition recorded below.  Lemmas that held for arbitrary inputs only through the zero
  value assume s-finite inputs or the domain classes.  Lemmas that need only the section integrals
  hold on the domains, such as `compProd_apply`, `compProd_apply_prod`, `compProd_congr`,
  `compProd_eq_zero_iff`, `Kernel.fst_compProd`, `Measure.snd_compProd`, `parallelComp_comp_copy`,
  the almost-everywhere lemmas, `AbsolutelyContinuous.compProd` and its variants `_left`, `_right`,
  and `_of_compProd`, `absolutelyContinuous_compProd_left_iff`, and
  `mutuallySingular_of_mutuallySingular_compProd`, since a section integral vanishes exactly when
  the measures of the sections vanish almost everywhere (`HasCompProd.lintegral_eq_zero_iff`), and
  `mutuallySingular_compProd_left_iff` takes the domain classes in place of an s-finite kernel.
  `Measure.fst_compProd` and the absolute-continuity and mutual-singularity criteria for finite
  kernels no longer assume `SFinite μ`.  Staton, *Commutative semantics for probabilistic
  programming* (ESOP 2017), Lemma 3, composes s-finite kernels and remarks that measurability in the
  parameter is the obstacle to dropping s-finiteness; Vákár and Ong, *On S-finite measures and
  kernels* (arXiv:1810.01837), Theorem 1, credit the closure of s-finite kernels under composition
  to Staton.  Tests cover the removed names, the enforced domains, the instances that stay
  conditional, routine evidence, values outside s-finite inputs, almost-everywhere statements on the
  domains, proof independence, and rewriting.

- [ ] **Give `partialTraj` its exact domain.**
  `ProbabilityTheory.Kernel.partialTraj κ a b` in
  `Mathlib/Probability/Kernel/IonescuTulcea/PartialTraj.lean` iterates the products
  `Kernel.id ×ₖ (κ k).map (piSingleton k)` for `a ≤ k < b` and takes `∀ n, IsSFiniteKernel (κ n)`,
  which supplies every step but is only sufficient: only the steps with `a ≤ k < b` are used, and
  each needs only the domain of its product.  Decide whether an interface for the exact domain is
  worth having, given that the Ionescu-Tulcea theorem uses Markov kernels.

- [ ] **Give `Measure.productBySections` its exact domain or merge it into `⊗ₘ`.**
  `productBySections μ ν h` takes `h : HasAEMeasurableSectionMeasures μ ν`, which is sufficient but
  not necessary: for counting measure `μ` on `ℝ` and `ν = Σ_{t ∈ T} dirac t` with `T` not Borel,
  `μ.HasCompProd (Kernel.const ℝ ν)` holds (`Measure.hasCompProd_count`), while the section-measure
  function of the diagonal is the indicator of `T`, which is not almost everywhere measurable for
  counting measure, whose only null set is empty.  The section integrals of `productBySections μ ν`
  are those of `μ ⊗ₘ Kernel.const α ν`, whose domain `μ.HasCompProd (Kernel.const α ν)` is exact.
  Decide whether to define `productBySections` through `⊗ₘ` or to retire it, and migrate its Tonelli
  theory and consumers.

- [ ] **Give `Kernel.withDensity` its exact domain.**
  `Kernel.withDensity κ f` in `Mathlib/Probability/Kernel/WithDensity.lean:48` takes
  `[IsSFiniteKernel κ]` and is zero when `Function.uncurry f` is not measurable
  (`withDensity_of_not_measurable`).  Determine the exact domain on which the measures
  `(κ a).withDensity (f a)` form a kernel, separate it from the convenient sufficient conditions,
  and remove the fallback.

- [x] **Prove Tonelli's theorem on the exact domain of `μ ⊗ₘ κ` and drop surplus s-finiteness.**
  `Measure.lintegral_compProd` proves `∫⁻ x, f x ∂(μ ⊗ₘ κ) = ∫⁻ a, ∫⁻ b, f (a, b) ∂κ a ∂μ` for
  measurable `f` on `μ.HasCompProd κ`, and `HasCompProd.exists_measurable_ge_lintegral_lintegral_eq`
  gives the section integrals `a ↦ ∫⁻ b, f (a, b) ∂κ a` a measurable majorant with the same
  integral; both are in `Mathlib/Probability/Kernel/Composition/MeasureCompProd/Defs.lean`, with
  `Measure.setLIntegral_compProd`.  For a simple function the weighted sum of the majorants of its
  level sets is one, because `∫⁻` is superadditive (`le_lintegral_add`) and
  `c * ∫⁻ h ≤ ∫⁻ c * h` (`lintegral_const_mul_le`) for every function `h`.  For the approximations
  `SimpleFunc.eapprox f n` the infima `⨅ m ≥ n, G m` of the majorants `G m` of their section
  integrals are increasing measurable majorants with the same integrals, to which monotone
  convergence applies, although it fails for the lower integrals of functions that are not
  measurable.  For a function that need not be measurable, `lintegral_compProd_le` bounds its
  integral against `μ ⊗ₘ κ` by the iterated integral, with equality when it has a measurable
  majorant with the same integral (`lintegral_compProd_of_exists_measurable_ge`).
  `Kernel.lintegral_compProd`, `lintegral_compProd'`, `lintegral_compProd₀`,
  `setLIntegral_compProd` and its `univ` variants, `lintegral_parallelComp`, and `lintegral_prod`
  hold on `κ.HasCompProd η`, `κ.HasParallelComp η`, and `κ.HasCompProd (prodMkRight β η)`.
  Instances close the domain of `μ ⊗ₘ κ` under `μ + ν` and `c • μ`, with the pointwise minimum of
  the majorants or the majorant itself, because `∫⁻` is additive and homogeneous in the measure for
  every function; under `Measure.sum` of a countable family, with the pointwise infimum of the
  majorants; and under `κ + η` and `Kernel.sum` of a countable family, with the sum of the
  majorants.  The domain is not closed under uncountable sums (paper proof): for a set `T ⊆ ℝ` that
  is not Borel, every `dirac t` has a composition-product with the constant kernel of
  `Σ_{u ∉ T} dirac u`, but against `Σ_{t ∈ T} dirac t` the measures of the sections of the diagonal
  form the indicator of `Tᶜ`, whose integral is `0`, and a measurable majorant `g` with integral
  `0` would make `T = {g < 1}` Borel.  So `Measure.compProd_sum_left` takes the domain of the sum
  as an assumption.  The kernel domain `κ.HasCompProd η` is closed under sums of `κ`
  (`Kernel.hasCompProd_add_left`, `Kernel.hasCompProd_sum_left`).  `μ.HasCompProd (κ ⊗ₖ η)`
  follows from `μ.HasCompProd κ`, `κ.HasCompProd η`, and `(μ ⊗ₘ κ).HasCompProd η`, which an
  s-finite `η` supplies (`Measure.hasCompProd_compProd`): the measures of the sections are the
  section integrals of `F p = η p (Prod.mk p ⁻¹' s')`, the section integrals of a majorant of `F`
  against `μ ⊗ₘ κ` have a measurable majorant, and `lintegral_compProd_le` closes the inequalities.
  Without the domain of `(μ ⊗ₘ κ) ⊗ₘ η` the conclusion can fail (paper proof in the docstring of
  the instance).  On the domains hold `Measure.compProd_add_left`, `compProd_smul_left`,
  `compProd_add_right`, and `compProd_sum_right`, moved to `Defs.lean` beside their instances; the
  kernel `compProd_add_left` and `compProd_sum_left`; `Measure.compProd_assoc` and
  `compProd_assoc'`; and `Kernel.fst_prod` and `snd_prod`.  `Measure.compProd_const_apply_prod`,
  `Kernel.prod_apply_prod`, and `Kernel.parallelComp_apply_prod` give a rectangle the product of the
  measures of its sides on the domains, also for sides that are not measurable: a majorant of the
  measures of the sections of a measurable superset of the rectangle is at least `ν t` on a
  measurable superset of `s`.  The swaps `Kernel.lintegral_prod_symm` and
  `lintegral_parallelComp_symm` keep s-finite kernels, a sufficient condition for changing the order
  of integration that the domains do not replace: the constant kernels of counting measure on `ℝ`
  and of Lebesgue measure on `[0, 1]` satisfy `κ.HasCompProd (prodMkRight β η)` and
  `κ.HasParallelComp η`, and the indicator of the diagonal integrates to `0` against their product
  and to `1` in the other order.  `compProd_eq_sum_compProd`, `IsSFiniteKernel.compProd`, and the
  instances `SFinite (μ ⊗ₘ κ)` keep s-finiteness for their s-finite decompositions.  Consumers whose
  s-finiteness only fed the former lemmas hold on more inputs: `Measure.comp_compProd_comm` on the
  domain classes; `compProd_withDensity`, `withDensity_compProd`,
  `withDensity_compProd_withDensity`, and the sub-Gaussian `Kernel.HasSubgaussianMGF.add_compProd`,
  `add_comp`, and `integrable_exp_add_compProd` without an s-finite measure; and the Lebesgue
  integrals against a conditional kernel in `Disintegration/Integral.lean` without a finite `κ` or
  `ρ` or an s-finite `η`.  The items below record the lemmas that still assume more.  Tests in
  `MathlibTest/CompProdTonelliStrict.lean` cover the theorems against counting measure and the
  constant kernel of counting measure on `ℝ`, which are not s-finite, the closure instances, the
  uncountable sum that instance search does not cover, associativity on the domains, and
  rectangles.

- [ ] **Characterize `HasCompProd` against a σ-finite measure by almost everywhere measurability.**
  For σ-finite `μ`, `μ.HasCompProd κ` should hold exactly when the measures
  `h a = κ a (Prod.mk a ⁻¹' s)` of the sections of every measurable set `s` are `μ`-almost
  everywhere measurable, the sufficient condition of `HasCompProd.of_aemeasurable` (paper proof).
  The measurable sets on which `h` agrees almost everywhere with a measurable function are closed
  under countable unions, so they have a largest element `C` up to null sets, measured by a finite
  measure equivalent to `μ`.  A measurable `D ⊆ Cᶜ` with `μ D > 0` and `∫⁻ a in D, h a ∂μ < ∞`
  cannot exist: the majorant for `s ∩ D ×ˢ univ` and a measurable minorant of `D.indicator h` with
  the same integral (`exists_measurable_le_lintegral_eq`) agree almost everywhere, which would
  enlarge `C`.  The measurable minorants of `h` have an almost everywhere largest element `g`, again
  by σ-finiteness, and `∫⁻ a in D, h a ∂μ = ∫⁻ a in D, g a ∂μ` for every measurable `D`.  Applied
  to `D = Cᶜ ∩ A n ∩ {g ≤ n}` for sets `A n` of finite measure that exhaust the space, this gives
  `g = ∞`, and so `h = ∞`, almost everywhere on `Cᶜ`; hence `h` agrees almost everywhere with the
  measurable function that is its witness on `C` and `∞` on `Cᶜ`.  Then `ξ.HasCompProd κ` for every
  `ξ ≪ μ`, which would let `AbsolutelyContinuous.mutuallySingular_compProd_iff`,
  `mutuallySingular_compProd_iff`, `absolutelyContinuous_compProd_of_compProd`, and
  `absolutelyContinuous_compProd_iff` in
  `Mathlib/Probability/Kernel/Composition/MeasureCompProd.lean` replace their s-finite kernels by
  domain classes: they apply `compProd_add_left` to Lebesgue decompositions of the σ-finite `μ` and
  `ν`, whose parts are absolutely continuous with respect to `μ` or `ν`.  The last two also need
  `μ.HasCompProd η`, since `μ ⊗ₘ η` occurs without `μ ≪ ν`, and `mutuallySingular_compProd_iff`
  needs the domains for the `ξ` it quantifies over.  Without
  σ-finiteness the domain does not pass to `ξ ≪ μ`, not even to `ξ ≤ μ`: counting measure on `ℝ`
  has a composition-product with the constant kernel of `Σ_{t ∈ T} dirac t` for every `T`
  (`hasCompProd_count`), but against Lebesgue measure, which is at most counting measure, the
  measures of the sections of the diagonal form the indicator of `T`, whose lower and upper
  integrals differ when `T ⊆ [0, 1]` is not Lebesgue measurable.  Nor does s-finiteness suffice for
  the characterization (paper proof, using Lusin's theorem that analytic sets are Lebesgue
  measurable): `∞ • volume.restrict (Icc 0 1)` has a composition-product with the constant kernel of
  `Σ_{t ∈ T} dirac t + count`, whose measures of the sections of a measurable set are positive
  exactly on its projection, while against the equivalent finite measure the measures of the
  sections of the diagonal form `1 + T.indicator 1`, which is not almost everywhere measurable.

- [ ] **Restate the remaining kernel composition lemmas on their domains.**
  Several lemmas in `Mathlib/Probability/Kernel/Composition/` still assume s-finite kernels although
  their proofs use only section integrals.  In `CompProd.lean`, `Kernel.compProd_add_right` and
  `compProd_sum_right` need instances closing `κ.HasCompProd η` under sums of `η`: pointwise,
  `sectR (η + η') a` is `sectR η a + sectR η' a`, whose composition-product with `κ a` exists by
  `Measure.hasCompProd_add_right`, and `Measure.compProd_add_right` makes the section integrals of
  the sum the sums of the section integrals, which are measurable in the point.
  `compProd_restrict`, `compProd_restrict_left`, and `compProd_restrict_right` need the domain for
  restrictions to a measurable set `D`, for which the majorant for `s ∩ D ×ˢ univ` on `D` and `∞`
  off `D` is a majorant, and `comapRight_compProd_id_prod` the domain for `comapRight`, whose
  sections are sections of the measurable image under `id × f`.  `Kernel.compProd_assoc` should
  hold on `κ.HasCompProd η`, `η.HasCompProd (ξ.comap MeasurableEquiv.prodAssoc _)`, and
  `(κ ⊗ₖ η).HasCompProd ξ`, by `Measure.compProd_assoc` at each point (sketch); without such
  domains its section integrals need not be measurable in the point.  `Kernel.comap_prod` in
  `Prod.lean` uses only `prod_apply'` and needs the domain for `comap`.  The other s-finite lemmas
  of `Prod.lean`, `ParallelComp.lean`, `KernelLemmas.lean`, `Lemmas.lean`, `MeasureComp.lean`, and
  `WithDensity.lean` in the same directory go through `productBySections`, a change of the order of
  integration, or the measurability of integrals against s-finite kernels; audit them with the
  `productBySections` item above.

- [ ] **Prove Fubini's theorem for the Bochner integral on the domain of `μ ⊗ₘ κ`.**
  `Measure.integral_compProd`, `setIntegral_compProd`, `integrable_compProd_iff`, and
  `AEStronglyMeasurable.ae_of_compProd` in
  `Mathlib/Probability/Kernel/Composition/IntegralCompProd.lean` assume `SFinite μ` and an s-finite
  `κ`, and pass through the kernel composition-product of `Kernel.const Unit μ`, whose versions
  assume s-finite kernels.  Their statements involve `a ↦ ∫ b, f (a, b) ∂κ a` and
  `a ↦ ∫ b, ‖f (a, b)‖ ∂κ a`, which are almost everywhere strongly measurable for an s-finite `κ`;
  on `μ.HasCompProd κ` only the lower integrals of the section integrals of measurable functions are
  controlled, through their majorants.  Determine the statements that hold on the domain, and
  whether `SFinite μ` is needed when `κ` is s-finite, before weakening the assumptions.

- [ ] **Formalize the counterexamples recorded for the composition-product domain.**
  The docstrings of `Measure.hasCompProd_sum_left` and `Measure.hasCompProd_compProd` in
  `Mathlib/Probability/Kernel/Composition/` and the items above state as paper proofs that the
  domain fails for an uncountable sum of Dirac measures; that `μ.HasCompProd (κ ⊗ₖ η)` can fail
  without the domain of `(μ ⊗ₘ κ) ⊗ₘ η`; that the constant kernels of counting measure on `ℝ` and
  of Lebesgue measure on `[0, 1]` have a product against which the order of integration cannot be
  changed; and that the domain does not pass from counting measure to Lebesgue measure.  Each needs
  a set that is not Borel, which exists by counting with
  `SigmaAlgebra.cardinal_measurableSet_le_continuum`, or one that is not Lebesgue measurable;
  `Counterexamples/KernelCompProd.lean` is the precedent.

- [ ] **Make Radon--Nikodym data conditional on decomposition existence.**
  `Measure.rnDeriv` and `Measure.singularPart` in
  `Mathlib/MeasureTheory/Measure/Decomposition/Lebesgue.lean:80` and `:73` return zero without
  `HaveLebesgueDecomposition μ ν`.  Require that evidence or return a bundled decomposition; apply
  the same review to signed and complex vector-measure wrappers.  `IsCondCDF.ofReal_ae_eq_rnDeriv`
  and the private existence proof for `condCDF` take `rnDeriv` only of ray measures with respect to
  a σ-finite `ρ.fst`, where the decomposition exists, so they can supply the evidence.

- [ ] **Move continuous functional calculus to its checked core.**
  `cfc` and `cfcₙ` in
  `Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Unital.lean:307` and
  `Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/NonUnital.lean:215` return zero when
  the element predicate or continuity conditions fail (and,
  nonunital, when `f 0 ≠ 0`).  Make `cfcHom`/`cfcₙHom` the strict substrate and automate the
  real obligations at the primary interface.  `multivariateGaussian` applies `CFC.sqrt` only to
  positive semidefinite matrices: once the square root takes `0 ≤ S`, it passes `hS.nonneg` and
  drops `@[nolint unusedArguments]`, and `Measurable.multivariateGaussian`, now proved through
  `CFC.measurable_sqrt`, needs measurability on the positive cone, where `CFC.continuousOn_sqrt`
  applies.

- [ ] **Remove fake zeros at Gamma poles.**
  `Complex.Gamma` and `Real.Gamma` in
  `Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean:287` and `:402` return zero at nonpositive
  integer poles.  Use pole-excluding inputs or a meromorphic-function object; do not retain a
  pointwise pole value publicly without literature using that convention.

- [ ] **Separate ordinary hypergeometric functions from convergence/pole fallbacks.**
  `ordinaryHypergeometric` in
  `Mathlib/Analysis/SpecialFunctions/OrdinaryHypergeometric.lean:81` is zero when its defining series
  is nonsummable.  At a denominator pole `c = -k`, totalized division instead makes later
  coefficients zero and manufactures a spurious terminating polynomial with infinite convergence
  radius (lines 130 and 160); it does not make the whole function identically zero.  Require
  convergence and pole avoidance, and separately verify the analytic-continuation domain of the
  regularized hypergeometric API before using it as the total object.

- [ ] **Represent the Weierstrass function as meromorphic at lattice points.**
  `PeriodPair.weierstrassP` in
  `Mathlib/Analysis/SpecialFunctions/Elliptic/Weierstrass.lean:268` evaluates lattice poles as zero,
  and `deriv_weierstrassP` at line 593 is globally true only because derivative and function junk
  values coincide.  Expose ordinary evaluation away from the lattice and state global results at the
  meromorphic-function level.

- [ ] **Require normality for ordinal fixed-point enumerators.**
  `Ordinal.nfp` and `Ordinal.deriv` in `Mathlib/SetTheory/Ordinal/FixedPoint.lean:246` and `:325`
  accept arbitrary functions although their names promise fixed-point enumeration; several theorems
  depending on junk values are already deprecated.  Put normality/continuity evidence in the named
  interface and retain generic transfinite iteration under a distinct name.

## XL -- foundational audit candidates; no migration is authorized

- [ ] **Classify inverse and division semantics before prototyping any hierarchy split.**
  Follow the deferred acceptance criteria in `FORK_DESIGN.md`; this item does not authorize a
  production migration.  First decide where total inversion is independently meaningful algebraic
  structure, where literature supports a total convention guarded by theorem hypotheses, and where an
  unsupported branch leaks into a claimed mathematical result.  A proof-bearing inverse is not
  automatically more faithful than a total inverse, and the audit must state the equations and
  universal properties each interface is intended to preserve.  The inventory must include scalar
  inverse/division by zero, negative powers, rational casts, simplifier/tactic behavior, and
  `Matrix.inv` in `Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean:169`, which returns zero
  when the determinant is not a unit.  Treat matrix inversion, scalar field inversion, units, and
  Euclidean quotient/remainder as separate mathematical contracts: `EuclideanDomain` requires
  `a / 0 = 0` and derives `a % 0 = a` in
  `Mathlib/Algebra/EuclideanDomain/Defs.lean:159` and `:152`, respectively, while a nonzero
  Euclidean divisor need not be a unit and its quotient is not exact field division.

- [ ] **Separate natural monus from partial subtraction and predecessor.**
  `Nat.sub` returns zero when the subtrahend is larger, and `Nat.pred 0 = 0`; the current source
  calls these results garbage values in `Mathlib/Data/Nat/PSub.lean:15`.  Truncated subtraction is a
  legitimate monus operation with order-theoretic laws, but exposing it as ordinary `Nat.sub` and
  `a - b` makes it easy to read a theorem as partial or group subtraction while silently truncating
  outside `b ≤ a`.  Make `Nat.psub`/`Nat.ppred`, defined at lines 44 and 32, or proof-bearing
  wrappers the ordinary subtraction/predecessor boundary.  If literature supports monus as the
  intended mathematical object, expose it under the literature's name and notation; otherwise keep
  the truncating operation private.  Remove the ordinary subtraction surface because it invites the
  wrong mathematical reading even when monus itself is independently justified.  Audit and migrate
  theorem statements whose natural reading currently depends on that ambiguous surface.

- [ ] **Base conditional extrema on exact `IsLUB`/`IsGLB` existence.**
  `ConditionallyCompleteLattice` in
  `Mathlib/Order/ConditionallyCompleteLattice/Defs.lean:46` supplies total `sSup`/`sInf` although
  the generic specification uses nonempty bounded sets.  Those hypotheses are sufficient, not the
  exact domain: `ConditionallyCompleteLinearOrderBot` makes `sSup ∅ = ⊥`, and
  `isLUB_csSup'` proves the correct empty case from boundedness alone.  Prototype an interface whose
  core evidence is `IsLUB s a` or `IsGLB s a`, with constructors for the applicable bounded,
  nonempty, bottom, and top cases.  Audit only genuinely unsupported cases; complete-lattice extrema
  and canonical empty extrema are not defects.

- [ ] **Replace `Module.finrank`'s infinite-to-zero convention.**
  `Module.finrank` in `Mathlib/LinearAlgebra/Dimension/Finrank.lean:62` is
  `Cardinal.toNat (Module.rank R M)` and occurs across roughly 179 maintained Lean files.
  Natural-valued rank needs finite-rank evidence; keep cardinal rank globally.  Migrate
  `AffineSubspace.finDim` (`Mathlib/LinearAlgebra/AffineSpace/Dimension.lean:51`) and other derived
  invariants without conflating finite rank with finite generation over general semirings.

- [ ] **Keep derivative relations primary and audit value projections separately.**
  `fderivWithin`/`fderiv` (`Mathlib/Analysis/Calculus/FDeriv/Defs.lean:151`, `:160`),
  `derivWithin`/`deriv` (`Mathlib/Analysis/Calculus/Deriv/Basic.lean:145`, `:153`), and
  `lineDerivWithin`/`lineDeriv`
  (`Mathlib/Analysis/Calculus/LineDeriv/Basic.lean:100`, `:108`) return zero at nondifferentiable
  points; within-set derivatives can also be nonunique.  The faithful
  general object is already the `Has*Deriv*` relation, including settings where several ambient maps
  satisfy it.  Preserve that relational API.  Audit value-returning projections and theorems for
  accidental reliance on the zero branch; offer a canonical value only when existence and the
  relevant uniqueness are established.  Treat `UniqueDiffWithinAt` as a common sufficient
  hypothesis, not the definition of every legitimate within-set derivative.

- [ ] **Separate integrability from existence of a target-valued Bochner integral.**
  `MeasureTheory.integral` in `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:158` returns zero
  when the function is nonintegrable or the target is incomplete.  `CompleteSpace` is a standard
  sufficient condition for the general construction, but not an exact necessity for every
  individual function: an integrable simple function has a target-valued integral given by a finite
  sum even in an incomplete target.  Keep
  `Integrable` and target-valued existence distinct, audit theorems that use the fallback, and
  prototype an existence-certified integral before deciding whether notation or expectation APIs
  should change.  The lower Lebesgue integral is not part of this candidate.

- [ ] **Audit `tsum`/`tprod` choice projections against `HasSum`/`HasProd`.**
  `tsum` and `tprod` in `Mathlib/Topology/Algebra/InfiniteSum/Defs.lean:132` and `:142` return zero
  and one when `HasSum`/`HasProd` fails, with additional uniqueness concerns in nonseparated spaces.
  `HasSum`/`HasProd` are already the faithful relational cores, while `tsum`/`tprod` are total value
  projections.  Identify theorem statements or consumers that actually exploit fallback or
  nonuniqueness; do not infer that every syntactically unguarded term is a false statement.  Keeping
  zero or one under ordinary infinite-sum/product names outside the convergence domain requires
  literature using those exact conventions.  Without it, keep the fallback only in a private
  implementation helper whose branch cannot reach public statements, and make the relational or
  summable boundary mathematician-facing.
  Coordinate any accepted slice with dependent series, power-series evaluation, and the separate
  `finsum`-based Euler-characteristic audit.
  In particular, the analytic Dirichlet-density work above proves convergence and denominator
  positivity on its right-hand germ, but `NumberField.Set.primeIdealZetaSum` still has an
  unrestricted real input. Audit its public projection against its exact convergence domain.
  The sufficient condition `s > 1` is not the exact domain for every subset: finite sets converge
  for every real `s`. Preserve the established density relation and normalization theorems when
  selecting a domain-bearing projection.

- [ ] **Reassess public `finsum`/`finprod` totalization on infinite support.**
  Their names and source docstrings disclose the zero/one result outside finite support, but that is
  not literature evidence for treating those values as finite sums or products.  Find mathematical
  sources using the same convention under the same operators.  Without such evidence, require finite
  support at the public boundary and keep any total fallback private; audit `eulerChar` and other
  consumers independently rather than inheriting the implementation convention.

- [ ] **Audit special-function extensions family by family.**
  `Real.log` (`Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:44`) is absolute-value log off zero
  and zero at zero; `Real.sqrt` (`Mathlib/Analysis/Real/Sqrt.lean:112`) is zero on negatives;
  `Real.arcsin`/`arccos` (`Mathlib/Analysis/SpecialFunctions/Trigonometric/Inverse.lean:35`, `:276`)
  clamp outside `[-1,1]`; and `Real.rpow` (`Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:35`)
  totalizes zero/negative-base cases under ordinary notation.  `Complex.log` and `Complex.arg` in
  `Mathlib/Analysis/SpecialFunctions/Complex/Log.lean:30` and
  `Mathlib/Analysis/SpecialFunctions/Complex/Arg.lean:30` assign zero at zero.  These are not one
  domain problem: `Real.log` is intentionally `log |x|` on nonzero reals and preserves
  multiplicative laws, while valid real powers of a nonpositive base depend on the exponent
  (integral powers and positive powers of zero are genuine cases).  Record each function's
  specifying laws, branch choices, and degenerate cases before proposing constrained carriers or
  renames.  The source's description of `Real.log` as an "unconventional extension" is not evidence
  for retaining it publicly.  A total definition needs matching literature for the same real/complex
  domain and must be specified as an independent mathematical object; otherwise its fallback is only
  a private transitional bridge.  Preserve the useful algebraic and analytic theorem families in
  either design.

## Representation fidelity lint -- total objects whose representation changes the semantics

These are not undefined-operation-to-junk-value defects.  The represented object is mathematically
legitimate, but its inherited instances, indexing convention, or container shape can differ from
the standard object suggested by informal notation.  Keep this lint separate from strict-partiality
migrations: require names, types, documentation, and theorem statements to identify which object is
actually formalized, and provide a literature-supported facade when downstream mathematics uses
another standard representation.

- [x] **[S] Distinguish finite product metric spaces from Euclidean space.**
  `Fin n → ℝ` carries the sup metric of `Mathlib/Topology/MetricSpace/Pseudo/Pi.lean`, and
  `EuclideanSpace ℝ (Fin n)`, which is `PiLp 2`, the Euclidean one.  An audit of `Mathlib`,
  `Archive`, and `Counterexamples` for declarations and docstrings that call a bare Pi type
  `Fin n → ℝ` or `ι → ℝ` Euclidean while using its metric, norm, balls, or spheres found no such
  statement.  The Euclidean balls, spheres, and disks of
  `Mathlib/Topology/Category/TopCat/Sphere.lean`, `Archive/Hairer.lean`, and the Behrend
  construction live in `EuclideanSpace` or `PiLp 2`;
  `Mathlib/Geometry/Euclidean/Volume/Measure.lean`, `Mathlib/MeasureTheory/Order/UpperLower.lean`,
  and `Archive/Wiedijk100Theorems/AreaOfACircle.lean` name the sup metric where they use it; and the
  box integral, the order-connected sets of `Mathlib/Analysis/Normed/Order/UpperLower.lean`, and the
  Gagliardo--Nirenberg--Sobolev inequality use `ι → ℝ` as coordinate vectors without a Euclidean
  metric claim.  No lint is added: a lexical check cannot tell these product-metric and coordinate
  uses from a misread, and the audit found no instance for it to catch.

- [x] **[S--M] Identify the zero-padded singular-value sequence with the `s`-numbers.**
  `LinearMap.singularValues T` in `Mathlib/Analysis/InnerProductSpace/SingularValues.lean` is the
  sequence of `s`-numbers of `T`, indexed from `0`.  The axioms of A. Pietsch, *s-Numbers of
  operators in Banach spaces*, Studia Math. 51 (1974), 201--223, assign to every operator a
  nonincreasing sequence `s₁(T) ≥ s₂(T) ≥ ⋯ ≥ 0` indexed by all positive integers, with `sₙ(T) = 0`
  whenever `rank T < n`, and on operators between Hilbert spaces all `s`-numbers coincide with the
  singular values (A. Pietsch, *Eigenvalues and s-Numbers*, Cambridge University Press, 1987,
  2.11.9).  The values after the rank are therefore `s`-numbers, not padding, and the module
  documentation now cites this instead of calling them junk values.  The downstream statements
  already name their index sets: `support_singularValues` and `card_support_singularValues` put the
  positive values on `Finset.range (finrank 𝕜 T.range)`,
  `injective_iff_forall_lt_finrank_singularValues_pos` quantifies over `i < finrank 𝕜 E`, and
  `normDet_eq_prod_singularValues` multiplies over `Finset.range (finrank 𝕜 U)`.

- [ ] **[L] Distinguish zero-encoded element order from an extended order.**
  `orderOf` and `addOrderOf` in `Mathlib/GroupTheory/OrderOfElement.lean:178` encode infinite order as
  zero.  The encoding is lossless because every finite order is positive and
  `orderOf_eq_zero_iff` at line 211 characterizes the sentinel, but losslessness alone does not make
  zero the literature-standard mathematical value of infinite order.  Find literature using this
  exact convention before retaining the ordinary name; otherwise use an extended-valued invariant
  and require `IsOfFinOrder`/`IsOfFinAddOrder` for a natural-valued projection.  Keep the zero
  encoding private rather than exporting a second public order operation merely for implementation
  convenience.  Since `Function.minimalPeriod` takes a proof of periodicity, `orderOf x` is defined
  by cases on `IsOfFinOrder x`, and `MulAction.period` and `AddAction.period` share the zero
  encoding for a point that does not return.  J. Delgado, E. Ventura, and A. Zakharov, *Relative
  order and spectrum in free and related groups*, arXiv:2105.03798, Section 2 and Remark 2.12, use
  this convention: the order of an element of infinite order is `0`, and so is the order of `g`
  relative to a subgroup `H` (for the stabilizer of a point, its period) when no positive power of
  `g` lies in `H`.

## Deferred API hygiene -- subordinate to mathematical fidelity

The remaining notation, presentation, and proof-maintenance candidates are not mathematical
fidelity work unless a concrete statement is naturally misread or changes meaning.  Do not schedule
them ahead of unresolved mathematical-domain and representation questions merely to make the API
more uniform, searchable, generated, or tactic-independent.

### Notation and term-structure hygiene -- valid terms with misleading surface syntax

These entries are not mathematical-unsoundness or strict-partiality findings.  They track syntax
that impersonates a general Lean application form, hides the declaration head or a meaningful
mathematical choice, cannot be found through the apparent identifier, or requires noncompositional
parser and delaborator behavior.  A notation is not defective merely because it uses brackets or
Unicode: conventional mathematical operators and literals remain appropriate when their operands
have stable roles and a searchable named declaration remains available.

- [x] **[S] Remove the unused `Integrable[𝓐]` explicit-instance escape hatch.**
  The σ-algebra binder of `MeasureTheory.Integrable` is named `mα`, so a σ-algebra other than the
  one inferred from the measure is passed as the named argument `Integrable (mα := m) f μ`, and the
  scoped notation `Integrable[m]`, which had no consumer, is removed.  A test checks the named
  argument and that `Integrable[m] f μ` is no longer integrability syntax.

- [x] **[S--M] Remove the `P[X]` expectation macro that competes with element lookup.**
  The scoped macro of `Mathlib/Probability/Notation.lean`, which read any term followed by `[` as an
  integral against that term, is removed.  Its uses are the named integral `∫ ω, X ω ∂P`, which
  keeps the measure `P` explicit; `𝔼[X]` integrates against `volume` and is not a replacement.  A
  mean is the real integral, coerced where a complex value is needed, and `P[id]` is `∫ x, x ∂P`, so
  the lemmas that differed from another only by `id` are removed:
  `ContinuousLinearMap.integral_comp_id_comm'`, `ContinuousLinearEquiv.integral_comp_id_comm'`,
  `integral_id_multivariateGaussian'`, and `BrownianReal.integral_id_projectiveFamily'`.  A test
  checks that an invalid list lookup is reported as a lookup error and that a measure followed by a
  bracket is an element lookup rather than an expectation.

- [x] **[S] Remove the exported Diophantine proof-DSL surface.**
  The symbolic forms `D∧`, `D∨`, `D∃`, `D&`, `D.`, `D=`, `D+`, `D*`, `D≤`, `D<`, `D-`, `D∣`, `D%`,
  and `D≡` of the closure lemmas in `Mathlib/NumberTheory/Dioph.lean` are file-local notation
  instead of scoped notation, since the long subtraction, remainder, division, Pell, and power
  constructions of that file read better with them than with nested named lemmas; the unused `D≠`
  and `D/` are removed.  The logical grouping of each construction is checked by elaboration: every
  compact expression is ascribed the set-builder statement it denotes, or is transported to one by
  `Dioph.ext` with an explicit `show`.  The scoped prefix `&` for `Fin2.ofNat'` stays, because the
  statements of public theorems such as `pell_dioph` use it.  A test checks that the forms are not
  exported and that the named lemmas remain the interface.

- [x] **[M] Give `ordProj` and `ordCompl` searchable declaration heads.**
  `Nat.ordProj n p` is `p ^ n.factorization p`, the factor at `p` of the prime factorization of `n`,
  and `Nat.ordCompl n p` is `n / n.ordProj p`; they are declarations in
  `Mathlib/Data/Nat/Factorization/Defs.lean` with the defining lemmas `Nat.ordProj_def` and
  `Nat.ordCompl_def`, and the bracket notations `ordProj[p] n` and `ordCompl[p] n` are removed.  The
  argument order follows `n.factorization p`.  For a nonprime `p` the value `1` is the empty factor
  of the factorization, which `Nat.ordProj_of_not_prime` states; the value at `n = 0` follows the
  zero factorization of `0` and is recorded with the factorization entry.  A test checks the
  declarations and that the bracket forms no longer parse.

- [x] **[M] Give pair affine span a searchable head without asserting nondegeneracy.**
  The notation `line[k, p₁, p₂]` is removed, and its 191 occurrences in 18 files are the affine span
  `affineSpan k {p₁, p₂}`, whose head is searchable, whose pair lemmas are already named
  `…_affineSpan_pair`, and which is the point `{p₁}` when `p₁ = p₂`.  A separate pair-span
  declaration would duplicate the `affineSpan` API without adding content, so none is introduced,
  and no unqualified affine-line declaration is added.  The downstream comparison favors removal:
  the replacement costs only parentheses in application arguments, mainly in Euclidean geometry, and
  the docstrings of the pair lemmas that called these spans lines now describe affine spans.  A test
  checks that the affine span of a pair is displayed as such.

- [x] **[M] Make `RatFunc K` canonical over the colliding `K⟮X⟯` notation.**
  The scoped notation `K⟮X⟯` for `RatFunc K` is removed, and its 378 occurrences in nine files are
  `RatFunc K`.  The brackets `F⟮x₁, ..., xₙ⟯` are only `IntermediateField.adjoin`, so `K⟮X⟯` is the
  subfield generated by the variable, as in `RatFunc.adjoin_X : K⟮(X : RatFunc K)⟯ = ⊤`; the
  annotation now only selects `RatFunc.X` over `Polynomial.X`.  The `RatFunc` scope stays in use for
  the scoped instance `RatFunc.liftAlgebra`.  A test checks that `K⟮X⟯` is an intermediate field.

- [ ] **[L] Replace expected-type-driven `↧X` category bundling with visible heads.**
  `Mathlib/CategoryTheory/ConcreteCategory/Notation.lean:18`--`:35` and `:82`--`:101` infer a
  declaration named `FooCat.of` from the expected type, assume that the carrier is its final explicit
  argument, and elaborate the same visible `↧X` differently as `CommRingCat.of X`, `ModuleCat.of R X`,
  or another environment-discovered head.  The spelling has roughly 919 textual hits across 259
  maintained files.  Make the category-specific `.of` applications canonical, remove the generic
  environment search, and retain only explicit category-specific assistance if a downstream
  prototype shows that ordinary application cannot provide acceptable inference or diagnostics.

- [ ] **[L] Evaluate bracketed explicit-instance facades against ordinary explicit structure APIs.**
  The topology family in `Mathlib/Topology/Defs/Basic.lean:192`--`:210` and
  `Mathlib/Topology/UniformSpace/Defs.lean:206`--`:212`, `:629`--`:637` includes `IsOpen[t]`,
  `closure[t]`, `Continuous[t₁, t₂]`, `𝓤[u]`, and `UniformContinuous[u₁, u₂]`.  The measure-theory
  family includes `Measurable[𝓐, 𝓑]` at
  `Mathlib/MeasureTheory/SigmaAlgebra/Defs.lean:841`--`:845`, the strong and a.e. predicates at
  `Mathlib/MeasureTheory/Function/StronglyMeasurable/Basic.lean:72`--`:73`,
  `Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean:75`--`:77`, and
  `Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean:409`--`:415`, plus the explicit `Measure` and
  `Kernel` types at `Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean:77`--`:83` and
  `Mathlib/Probability/Kernel/Defs.lean:51`--`:70`.  These forms expose meaningful structures but
  encode them through a bespoke `Predicate[structure]` or `Type[structure]` application convention;
  together the spellings have roughly 568 textual hits across 87 maintained files.  This is a
  compositionality and discoverability candidate, not a mathematical-fidelity defect: the visible
  bracket argument does expose the selected structure.  Prototype stable binder names and ordinary
  named arguments, membership, projections, or explicitly parameterized relations/types against
  real consumers.  Remove custom delaborators only if the replacement preserves readability,
  nesting, elaboration, and diagnostics.  Preserve unsuffixed ambient predicates where one instance
  genuinely is ambient.

- [ ] **[L] Disambiguate the two `R[M]` monoid-algebra parsers.**
  `Mathlib/Algebra/MonoidAlgebra/Defs.lean:90`--`:123` installs the identical generic
  `term noWs "[" term "]"` grammar for `AddMonoidAlgebra R M` and `MonoidAlgebra R M`, selected only
  by scope.  Opening both scopes already produces the checked `Ambiguous term` failures in
  `MathlibTest/Algebra/MonoidAlgebra/Defs.lean:4`--`:45`.  Keep the two named type constructors as
  canonical heads; if conventional bracket notation remains, give it one deterministic elaboration
  rule or two syntactically distinct forms rather than parallel hidden heads.

- [ ] **[L] Retire the identifier-shaped manifold elaborator dialect.**
  `Mathlib/Geometry/Manifold/Notation.lean:838`--`:1013` makes bracket punctuation switch apparent
  heads such as `MDiffAt`, `MDiff`, `CMDiffAt`, `mfderiv`, `HasMFDerivAt`, `tangentMap`, and
  `UniqueMDiff` to different `*Within*` or `*On` declarations, while a custom search inspects
  expression types to recover the source and target models.  The bracketed forms alone have roughly
  1,104 textual hits across 37 maintained files.  Migrate to the existing named manifold APIs and a
  compositional mechanism for synthesizing routine model arguments; preserve their improved
  diagnostics without making an alternate identifier language the primary public syntax.

### Function-presentation hygiene -- one fact with curried and tuple views

These entries are not objections to `Function.curry`, `Function.uncurry`, `↿f`, or the
normalization lemmas that make them usable.  They track cases where beta/eta-equivalent
presentation has produced manually maintained declarations that appear to be separate
mathematical facts.  Keep a product or dependent-sum argument when it is the actual mathematical
domain, and keep structured curry/uncurry results when topology, measurability, boundedness,
linearity, or another invariant adds hypotheses or preservation content.

- [x] **[M] Share tuple/curried implementations without presuming one public theorem name.**
  The curried views keep their own names, since their left-hand sides `f x.1 x.2` and `f x` are
  different rewrite targets, and each is a direct application of its tuple-function version: the
  `prod_*'` pairs in `Mathlib/Algebra/BigOperators/Group/Finset/Sigma.lean` and
  `Mathlib/Data/Fintype/BigOperators.lean` already were, and `Finset.expect_product'` and
  `Multipliable.tprod_prod_uncurry` (with `Summable.tsum_prod_uncurry`) now are.  The docstrings of
  `Finset.prod_product_right'` and `Fintype.prod_prod_type_right'` and their additive versions,
  which called the curried view uncurried, are corrected, and the latter no longer cites a
  nonexistent `Finset` name.  `prod_sigma` and `prod_sigma'` keep both statements: the `Sigma` type
  is the dependent indexing domain of the double product, not a presentation of a pair.

- [x] **[M] Audit bare bridge families for generated proofs and useful orientations.**
  Each family keeps the views that have distinct consumers or rewrite targets.  `Set.image_prod`,
  `Set.image_uncurry_prod`, and `Set.image2_curry` rewrite three different input forms, and
  `Set.image2_curry` is now the symmetric of `Set.image_prod` instead of a `simp` proof under a
  transparency option.  `Finset.image₂_curry` and `Finset.image_uncurry_product` are definitional
  `simp` lemmas for the inputs `curry f` and `uncurry f`.  `Filter.map_prod_eq_map₂'` had no
  consumer and restated `Filter.map₂_curry` in the other orientation, so it is removed and
  `Filter.map₂_curry` follows from `Filter.map_prod_eq_map₂`.  `uniformContinuous₂_curry` and
  `Primrec₂.uncurry`/`Primrec₂.curry` are the only bridges between the two-argument predicates and
  the predicates on pairs, and the `Pi` and `Sigma` `curry`/`uncurry` lemmas in
  `Mathlib/Algebra/Group/Pi/Lemmas.lean` and `Mathlib/Algebra/Notation/Pi/Basic.lean` are
  definitional `simp` lemmas for the two directions, which a generator would not shorten; these are
  kept.

- [ ] **[L] Prototype one product-measure and iterated-integral theorem layer, then collapse
  duplicate presentations.**
  `Mathlib/MeasureTheory/Measure/ProductBySections.lean:55`--`:60` explicitly says that many results
  are proved twice for `α → β → γ` and `α × β → γ`, with both spellings justified there by
  elaboration convenience.  Concrete pairs include `ae_ae_eq_curry_of_prod` and
  `ae_ae_eq_of_ae_eq_uncurry` at lines 342--348, the a.e.-measurable inner-integral families at
  lines 967--987, and `lintegral_productBySections`/`lintegral_lintegral` plus their symmetric
  versions at lines 1004--1078.  The same duplication occurs for measurable inner integrals in
  `Mathlib/MeasureTheory/Measure/ProductMeasure.lean:92`--`:129`, Bochner inner integrals and
  Fubini statements in `Mathlib/MeasureTheory/Integral/Prod.lean:69`--`:93` and `:461`--`:497`, and
  vector-measure inner integrals in `Mathlib/MeasureTheory/VectorMeasure/Prod.lean:229`--`:256`.
  Prototype the canonical statement for each family against current elaboration-sensitive
  consumers, taking account of whether the product is the actual domain and which equality
  orientation is the useful rewrite normal form.  Make the other spelling a documentation/search
  view or an inline transport through `Function.curry`/`Function.uncurry`, not another hand-written
  proof.  If compatibility still requires a named entry, generate the exact transport mechanically
  under the compatibility policy.  Preserve genuine Tonelli, Fubini, measurability, integrability,
  and change-of-order results; migrate consumers together and negative-scan only the hand-maintained
  duplicate proofs and any names the prototype actually retires.

- [ ] **[L] Add an elaborated-statement lint for redundant presentation declarations.**
  A 2026-09-12 source scan found 621 curry/uncurry-named declaration lines in 114 files among all
  9,108 tracked Lean files.  Here a named line begins with an optional `protected`, `private`, or
  `noncomputable` modifier followed by `def`, `abbrev`, `theorem`, or `lemma`, and its declared
  identifier contains case-insensitive `curry`, `curried`, `currying`, or `uncurr*`; this lexical
  query was rerun at the final documentation state.  Suffixes and textual call counts alone were too
  noisy to classify the matches.
  Prototype an audit lint that transports quantified integrands to a common typed binder domain,
  normalizes the bare `Function.curry`/`Function.uncurry`, `Sigma.curry`/`Sigma.uncurry`, and
  recursive `↿f` views, and optionally recognizes equality symmetry before comparing propositions.
  Beta/eta conversion alone cannot match the advertised positive controls because their binder
  types differ, and some paired integral theorems reverse equality orientation.  Require the lint to
  emit a checkable transport proof and report candidates rather than errors.  Use the
  measure/integral and big-operator pairs above as positive controls.  Negative controls include
  `ContinuousMap.uncurry` and `Homeomorph.curry` in
  `Mathlib/Topology/CompactOpen.lean:430`--`:471` and `:556`, the multilinear and continuous
  multilinear equivalences in `Mathlib/LinearAlgebra/Multilinear/Curry.lean` and
  `Mathlib/Analysis/Normed/Module/Multilinear/Curry.lean`, categorical closed-structure currying,
  and genuine product, tensor, direct-sum, finite-support, or dependent-sum domains.  Companion
  normalization lemmas for an admitted structured construction inherit that construction's
  exclusion.  Run the lint in audit mode over the inherited tree; consider a diff-scoped warning
  only after all positive and negative controls are classified without false equivalences.

### Proof and API-boundary hygiene -- rewrites that depend on extra transparency

`erw` is logically sound, but its success where `rw` fails can expose a missing public rewrite
lemma, a coercion or representation boundary, or definitional-equality dependence in downstream
proofs.  Treat each occurrence as API-debt evidence to classify, not as proof that every occurrence
has the same root cause.  Repair the exposed interface or proof normal form before mechanically
changing the tactic.

- [ ] **[L] Classify `erw` invocations and repair demonstrated API boundaries.**
  The current maintained Lean trees contain 430 tactic invocations across 191 files (426 across 189
  `Mathlib/` files).  Several sites suggest an API or definitional-equality problem:
  `Mathlib/AlgebraicGeometry/ValuativeCriterion.lean:167`--`:171` tentatively attributes its `erw`
  to a `map_top` composition mismatch; `Mathlib/RingTheory/QuasiFinite/Weakly.lean:204` says its use
  should disappear when `Ideal.map` stops taking hom classes; and
  `Mathlib/RingTheory/Ideal/IsPrincipal.lean:110`--`:113` explains that the rewrite sees through an
  equality between two subtype presentations.  Inventory the occurrences by missing lemma,
  coercion/representation mismatch, category-composition defeq abuse, and genuine elaborator
  limitation.  For each family, add the natural public lemma or stable normal form and migrate its
  consumers to `rw`, `simp`, `change`, or an explicit equality transport that records the intended
  boundary.  Use `Mathlib/Tactic/CategoryTheory/CheckCompositions.lean:20` where applicable to
  diagnose possible composition discrepancies, without treating its report as proof of an API
  defect.  Remove an `erw` only when the replacement exposes a better stable boundary; otherwise
  retain it.  Negative-scan only the specific sites or families an accepted migration retires.
  Exclude documentation, the `erw?` implementation, and diagnostic fixtures such as
  `MathlibTest/Tactic/ErwQuestion.lean`, which intentionally demonstrate `rw` failure followed by
  `erw` success.

## Resolved and corrected classification audits

The 2026-09-13 classification pass resolved the families below against the strict-domain and
compositional-notation contracts.  A checked item records a classification decision, not completion
of any open migration task that it references.  A 2026-09-15 correction pass found that the earlier
audit sometimes inferred an exact domain from a convenient sufficient hypothesis or treated every
total projection as junk.  The unchecked entries above were revised where a concrete counterexample
was found, and none should inherit validation merely from the earlier scan:

- [x] **Matroid closure needs a strict ordinary boundary.**  Intersecting with `M.E` is an intentional
  implementation convention, but the ordinary `closure` name does not identify that extension and
  the module already provides the domain-bearing `subtypeClosure`.  The L task above records the
  canonical migration.
- [x] **Local bundle representatives split at the exported coordinate API.**  Globally defined
  trivialization representatives may exist privately when every semantic statement proves
  independence from their values outside the base sets.  Ordinary `coordChange` operations expose
  those values under a mathematical name, so the M task above moves their overlap into the public
  domain and keeps the ambient representatives out of the public API.
- [x] **Computational decoders and searches are excluded by default.**  Explicit `getD`, `headI`, tape
  blanks, parser defaults, and noncanonical decoders belong to computational representation
  contracts.  Reopen a case only when it is exported as a checked mathematical inverse or primary
  mathematical workflow.
- [x] **Witness choice alone is not a defect when the chosen value is unique.**
  `LinearIndependent.repr` in `Mathlib/LinearAlgebra/LinearIndependent/Defs.lean:462` is the
  positive control: its input carries both linear independence and span membership and the
  implementation is the inverse of a proved linear equivalence, so the specification determines
  the value.  Continue to flag reachable invalid branches or names asserting unsupported
  uniqueness.  A chosen representative of an object determined only up to an equivalence is not
  covered: the 2026-10-05 equivalence-class rule of `FORK_DESIGN.md` replaces it by the class, so
  the chosen left inverse of `LinearMap.leftInverse` is an open item above, and the chosen
  conditional kernels have become their almost-everywhere classes.  `Function.invFun` and
  `Function.extend` remain separate audit candidates: first distinguish a legitimate chosen
  preimage or representative from a name or theorem that falsely asserts inverse laws.
- [x] **An explicit default does not justify a public mathematical operation.**  A technical
  representative constructor may remain only privately behind a proved boundary that makes its
  fallback unreachable or proves representative independence.  The integration-facing
  `ContinuousMap.mkD` was removed in favour of bundled representatives with an almost everywhere
  specification (entry above).
- [x] **Conditional expectation and probability brackets are conventional secondary surfaces.**
  `μ[f | 𝓐]`, `μ[|s]`, and `μ[t | s]` have stable named expansions, preserve nesting, and elaborate
  correctly when both scopes are active.  Keep the notation; the construction contract of `condExp`
  remains a separate audit candidate, and `ProbabilityTheory.cond` takes the null-measurable event
  contract recorded above, which the notation finds with the `conditionable` discharger.
- [x] **The audited Unicode and indexed shortcuts remain admissible.**  `πₓ`/`πₘ`, `⦋m⦌ₙ`,
  generated intermediate fields, and `Mᵐ⁰` expose stable operands and expand through documented
  named structures or functor operations; the truncated-simplex proof is routine and can also be
  supplied explicitly.  Search inconvenience alone does not justify migration.
- [x] **The shared field delimiters and Diophantine DSL split into distinct outcomes.**  Keep
  `F⟮x₁, ..., xₙ⟯` as the conventional secondary surface for `IntermediateField.adjoin`, migrate the
  colliding rational-function `K⟮X⟯` surface to `RatFunc K`, and remove or localize the exported
  `Dioph` proof dialect as recorded in the notation tasks above.

## Audit coverage and limits

The 2026-09-11 pass searched the then-current source across 9,063 Lean files (about 1.93
million lines) in `Mathlib/`, `MathlibTest/`, `Archive/`, `Counterexamples/`, and `Wanted/`.
Candidate generation included explicit junk/arbitrary-value language, choice without witnesses,
lossy `.toNat`/`.toReal`/`.unzeroD` conversions, zero/one branches, conditional suprema/infima, `erw`
invocations, and failure lemmas for summability, integrability, differentiability, measurability,
and finiteness.
Selected public definitions were then inspected, but the scan did not prove that every proposed
replacement used the exact mathematical object or domain.

Those repository scans did not establish external mathematical usage for fallback conventions.
Consequently, no fallback discovered by them is approved as a public extension.  An item may instead
propose an independently specified total mathematical object only after recording the required
literature citation and exact matching convention.

The scan deliberately excluded `.lake/`, `Cache/`, generated dependencies, and ordinary test-only or
metaprogramming defaults.  It is historical candidate-generation evidence, not a validated inventory
of defects and not a declaration-by-declaration completeness result.  A mathematically misleading
abstraction can have no textual marker, while a zero branch or `Classical.choose` can implement a
well-defined internal construction without justifying its public mathematical name.  New findings
may be inserted as evidence-backed unchecked candidates; promote them to implementation only after
the fidelity gate above, then group accepted work by coherent migration effort rather than discovery
date.

A separate 2026-09-11 notation pass inspected 5,641 term-syntax declaration lines in the same 9,063
Lean files and manually classified 52 identifier-attached bracket declarations, together with
explicit-instance expansions, custom elaborators, delaborators, and representative consumers.  It
promotes only families with a hidden ordinary/instance argument, a missing or ambiguous declaration
head, or a concrete parser collision.  Conventional polynomial, algebraic-adjoin, tensor, valuation,
expectation, variance, and literal notations were screened rather than added automatically when
their operands and named APIs remained compositional and discoverable.

A 2026-09-12 function-presentation pass scanned all 9,108 tracked Lean files, including the 9,076
files in `Mathlib/`, `MathlibTest/`, `Archive/`, `Counterexamples/`, and `Wanted/`.  The pass
inspected 621 curry/uncurry-named declaration lines in 114 files, together with tuple-function
versus curried-function binders, primed theorem pairs, and source comments that explicitly describe
duplicated presentations.  The only named hit outside `Mathlib/` was the unfolding fixture at
`MathlibTest/FunPropMinimal.lean`; no non-`Mathlib/` public theorem family was promoted.  The scan
manually separated beta/eta transport from structured topology, measurability, multilinearity,
category theory, finite-support, and genuine product or dependent-sum mathematics.  It cannot prove
the absence of arbitrarily named equivalent theorems with no presentation marker.  The proposed
elaborated-statement lint remains an audit experiment: it must first handle typed binder transport,
equality orientation, attributes, and theorem-search value without identifying merely equivalent
presentations as redundant APIs.
