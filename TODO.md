# Mathematical fidelity and API hygiene backlog

This file records completed migrations and unresolved audit candidates under the strict-domain,
representation, public-notation, and function-presentation policies in `FORK_DESIGN.md`.  A checked
item records a completed migration or an explicit classification decision.  An unchecked item is
only a hypothesis to investigate: neither its diagnosis nor its proposed replacement is approved
until it passes the fidelity gate below.  Imperative wording in a candidate heading names the
suspected problem; it does not authorize that particular repair.

Mathematical fidelity is not the same as partiality or proof-carrying syntax.  A total operation may
be a genuine extended invariant, an order-theoretic operation, or a choice operator whose input
carries existence evidence and whose theorems prove the specifying property.  A no-witness branch
is still a fallback governed by the transitional-only rule below.  Conversely, adding a proof
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
   choice/representative, checked projection, or semantically unsupported fallback; a fallback does
   not remain as a permanent public extension; when identifiable mathematical literature uses the
   same total convention for the same inputs and degenerate cases, audit it as an independent total
   mathematical object with its own specifying properties; record the bibliographic citation and
   exact definition, theorem, or page--a more explicit name, source-code docstring, or convenient
   theorem is not enough;
4. test positive, negative, degenerate, characteristic-sensitive, and nonunique examples so that a
   strict facade does not exclude valid mathematics or manufacture canonicity;
5. audit whether the proposed name and notation communicate that exact object without inviting a
   standard but different reading, then choose among a relation, extended-valued invariant,
   canonical value, representative, subtype, proof argument, or explicit partiality type; and
6. prototype real consumers and record the candidate as accepted, reframed, rejected, or still
   unknown before scheduling a migration.

For an accepted strict-partiality migration, preserve a proved bridge on the valid domain and remove
the fallback from the public surface rather than merely renaming it.  A total extension may remain
only as a private transitional implementation helper when the public boundary proves that its
fallback is unreachable or that the result is independent of it.  Record its consumers and removal
condition, and remove it before declaring the migration complete.  Audit statements that exploit the
branch, add negative tests for the actual boundary, and run the affected downstream checks at the
final source state.

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

- [ ] **Restrict number-field heights to algebraic inputs and fix their documentation.**
  `absMulHeight₁` and `absLogHeight₁` in
  `Mathlib/NumberTheory/Height/NumberField.lean:137` and `:146` map a nonalgebraic element to
  multiplicative height one and logarithmic height zero.  Require `IsIntegral ℚ x` (or an
  algebraic-number carrier); also correct the multiplicative docstring, which currently says its
  fallback is zero.

- [x] **Remove the pole-only branch from `riemannZeta_ne_zero_of_one_le_re`.**
  The theorem now requires `s ≠ 1` and directly specializes Dirichlet L-function nonvanishing
  away from the pole. The zero-set consumer supplies this evidence, and a regression test rejects
  the former invocation using only `1 ≤ s.re`. Strict zeta/L-series evaluation remains separate
  under the L backlog.

- [ ] **Put `ArchimedeanClass.stdPart` on finite elements.**
  `Mathlib/Algebra/Order/Ring/StandardPart.lean:273` maps infinite inputs to zero, conflating them
  with infinitesimals in results such as `stdPart_eq_zero`.  Use the existing `FiniteElement K`
  domain.  Remove the ambient zero extension from the public surface unless matching mathematical
  literature is found; if implementation still needs it, keep it private behind finite-input proofs.

- [ ] **Require `1 < q` for `ArithmeticFunction.ofPowerSeries`.**
  `Mathlib/NumberTheory/ArithmeticFunction/LFunction.lean:66` uses the constant coefficient when
  `q ≤ 1`; algebra-hom laws intentionally exploit that branch.  Put the injective-power
  hypothesis in the constructor.  Do not export the constant-coefficient branch as a replacement
  operation without literature giving it that mathematical interpretation.

- [x] **Give `Nat.maxPrimeFac` its actual domain.**
  `Nat.maxPrimeFac n hn` requires `hn : 1 < n` and computes the last element of the nonempty
  prime-factor list without a fallback. `exists_isGreatest_prime_dvd_iff` characterizes this exact
  domain: zero has unbounded prime divisors and one has none. The theorem family uses the same
  domain, with fixed points exactly the primes. Tests cover computation, rejected inputs, and
  rewriting with independently supplied domain proofs.

- [ ] **Require nonzero mass for `FiniteMeasure.normalize`.**
  `FiniteMeasure.normalize` in
  `Mathlib/MeasureTheory/Measure/ProbabilityMeasure.lean:468` returns an arbitrary Dirac probability
  measure when the input measure has mass zero.  Put `μ ≠ 0` at the ordinary normalization boundary;
  do not retain the arbitrary-Dirac branch as a public operation.  A private implementation helper is
  acceptable only when nonzero-mass evidence makes the branch unreachable.

- [ ] **Require primitivity for `DirichletCharacter.rootNumber`.**
  `Mathlib/NumberTheory/LSeries/DirichletContinuation.lean:272` exposes the primitive-character
  Gauss-sum formula for every character and documents the nonprimitive result as junk.  Require
  `IsPrimitive χ` for the ordinary root number.  Keep the unrestricted expression public as a
  separate Gauss-sum formula only if literature uses it as such; otherwise keep it private.  Do not
  conflate it with the separate root number obtained from an induced primitive character.

## M -- subsystem audit candidates

- [ ] **Complete the analytic specification of number-field Dirichlet density.**
  `primeIdealZetaSum` and `HasDirichletDensity` in
  `Mathlib/NumberTheory/NumberField/DirichletDensity.lean:55` and `:83` still use real `tsum` and
  division, while `HasDirichletDensity.le_one` branches on summability at `:144` and reaches the
  nonsummable-to-zero fallback at `:147`.  Prove summability of the all-prime series for every real
  `s > 1`, deduce summability for subsets and strict positivity of the denominator, and remove
  fallback-dependent proof branches.  Establish the prime-sum asymptotic against
  `log (1 / (s - 1))`, or an equivalent bridge through the Dedekind zeta Euler product, so the
  ratio definition is connected to the standard logarithmic normalizations.  Reuse
  `NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT` as available residue evidence, but do not
  treat it alone as the missing prime-sum theorem.  Decide the public boundary of
  `primeIdealZetaSum` together with the XL `tsum`/`tprod` audit; keep `HasDirichletDensity` as the
  relational normal form and do not reopen the completed density-fiber migration.

- [ ] **Make finite multiplicity a checked projection.**
  `Mathlib/RingTheory/Multiplicity.lean:47` defines `multiplicity` as
  `(emultiplicity a b).toNat`, so infinite multiplicity becomes zero.  Keep `emultiplicity` as the
  faithful invariant and require `FiniteMultiplicity` for a natural-valued projection.  Migrate
  derived natural-valued consumers such as `padicValNat`, identified with `multiplicity` in
  `Mathlib/NumberTheory/Padics/PadicVal/Defs.lean:49`; in particular,
  `padicValNat_zero_right` in `Mathlib/Data/Nat/MaxPowDiv.lean:106` is the same infinite-to-zero case.

- [ ] **Require monicity for polynomial division-by-monic notation.**
  `Polynomial.divByMonic` and `Polynomial.modByMonic` in
  `Mathlib/Algebra/Polynomial/Div.lean:132` and `:137` accept a nonmonic divisor and return quotient
  zero and the original dividend.  Thread `q.Monic` through `/ₘ` and `%ₘ`, reusing
  `divModByMonicAux`.

- [ ] **Exclude the zero polynomial from finite root multisets and multiplicities.**
  `Polynomial.roots` in `Mathlib/Algebra/Polynomial/Roots.lean:58` gives the empty multiset at zero
  (line 71), while `Polynomial.rootMultiplicity` in
  `Mathlib/Algebra/Polynomial/Div.lean:498` returns zero even though a largest dividing power does
  not exist.  Require `p ≠ 0` for finite root multisets and finite multiplicities, retaining infinity
  where appropriate.  Ordinary set-valued root loci may remain defined for arbitrary polynomials.

- [ ] **Audit the zero-polynomial convention in `Polynomial.natDegree`.**
  `Polynomial.degree` and `Polynomial.natDegree` in
  `Mathlib/Algebra/Polynomial/Degree/Defs.lean:48` and `:52` respectively retain `⊥` and project the
  zero polynomial to zero.  The different name and documentation identify a natural-valued
  projection, but they do not establish that the zero convention is standard mathematical usage.
  Find literature using this convention before retaining it as a public invariant; otherwise
  require nonzeroness at the natural-valued boundary and keep the projection fallback private.
  Audit actual theorem statements rather than treating every internal use as paper-facing degree
  notation.

- [ ] **Make scheme order of vanishing carry its point and function domains.**
  `AlgebraicGeometry.Scheme.ord` in `Mathlib/AlgebraicGeometry/OrderOfVanishing.lean:52` returns
  zero for the zero rational function and for points not of codimension one.  Reuse `ordHom` for the
  point condition and expose nonzeroness or an infinity-preserving codomain.

- [ ] **Unify strict nilpotency invariants.**
  `Mathlib/RingTheory/Nilpotent/Defs.lean:78`, `Mathlib/GroupTheory/Nilpotent.lean:530`, and
  `Mathlib/Algebra/Lie/Nilpotent.lean:389` assign zero to nonnilpotent objects; `IsNilpotent.exp` and
  `LieModule.lowerCentralSeriesLast` inherit misleading values.  Require nilpotency evidence or use
  an extended natural invariant, then migrate the element, group, and Lie families coherently.

- [ ] **Require injectivity for `LinearMap.leftInverse`.**
  `Mathlib/LinearAlgebra/Basis/VectorSpace.lean:266` returns the zero map for a noninjective linear
  map.  Make the constructor consume injectivity or splitting data, and remove the zero-default
  extension from the public surface.

- [ ] **Bundle admissible root pairs for root-chain data.**
  `RootPairing.chainTopCoeff`, `chainBotCoeff`, `chainTopIdx`, and `chainBotIdx` in
  `Mathlib/LinearAlgebra/RootSystem/Chain.lean:110`, `:120`, `:366`, and `:377` return zero or the
  input index when the two roots are not linearly independent.  Take the independence proof once in
  a bundled admissible pair.

- [ ] **Require `ExcenterExists` for excenter geometry.**
  `Affine.Simplex.exsphere`, `excenter`, and `exradius` in
  `Mathlib/Geometry/Euclidean/Incenter.lean:346`, `:368`, and `:413` fabricate an arbitrary point
  and a zero-radius sphere when the excenter does not exist.  Put the existing validity predicate in
  the three public operations.

- [ ] **Make Newton iteration preserve derivative invertibility.**
  `Polynomial.newtonMap` in `Mathlib/Dynamics/Newton.lean:44` returns its input when the derivative
  value is not a unit, creating spurious fixed points.  Require unit evidence for a step and design
  iteration around propagation or explicit failure.  Do not expose the identity fallback as a
  Newton operation without matching literature.

- [ ] **Give the zero return-time generator a literature-supported mathematical name.**
  `Function.minimalPeriod` in `Mathlib/Dynamics/PeriodicPts/Defs.lean:245` is zero at a nonperiodic
  point, but this is not an arbitrary failure value: `isPeriodicPt_iff_minimalPeriod_dvd` at
  line 359 identifies it as the generator of all return times, including the submonoid `{0}` for a
  nonperiodic point.  The divisibility theorem shows that the total generator carries information,
  but not that it belongs in the public API.  Find literature using zero with this object and
  convention; otherwise keep the generator private and put `minimalPeriod` on periodic points.
  Likewise, `periodicOrbit` at line 401 uses the empty cycle to detect nonperiodicity.  Retain that
  total classifier publicly only with matching literature evidence; otherwise keep it private and
  expose only the actual orbit of a periodic point.

- [ ] **Use extended graph distance and girth until finiteness is proved.**
  `SimpleGraph.dist` in `Mathlib/Combinatorics/SimpleGraph/Metric.lean:206` maps unreachable pairs
  to zero, while `SimpleGraph.girth` in `Mathlib/Combinatorics/SimpleGraph/Girth.lean:115` maps an
  acyclic graph's infinite girth to zero.  Keep `edist`/`egirth` globally and require reachability or
  a cycle for natural-valued projections.

- [ ] **Replace the unbounded fallback in `SimpleGraph.cliqueNum`.**
  `Mathlib/Combinatorics/SimpleGraph/Clique.lean:726` takes a natural `sSup` without boundedness, so
  graphs with arbitrarily large finite cliques inherit the conditional-supremum junk value.  Choose
  and document an extended finite-clique invariant before exposing a checked natural projection.

- [ ] **Require `n ≠ 1` for `Nat.minFac`.**
  `Mathlib/Data/Nat/Prime/Defs.lean:218` returns one at one, although one has no prime factor.  Do not
  exclude zero: `minFac_zero` correctly identifies its least prime divisor as two.

- [ ] **Give `Nat.log` and `Nat.clog` their extremal domains.**
  `Mathlib/Data/Nat/Log.lean:62` and `:335` accept bases at most one and other inputs for which the
  advertised largest/least exponent characterization fails.  Encode the precise base and argument
  conditions.  Keep defaulting recursion private unless literature defines the same total arithmetic
  functions on those degenerate inputs.

- [ ] **Make `Nat.findGreatest` return evidence or explicit absence.**
  `Mathlib/Data/Nat/Find.lean:162` defines it as the largest bounded witness, or zero when none
  exists.  Thus zero can mean either an actual greatest witness when `P 0` holds or absence when it
  does not; the result alone does not distinguish the cases.  This is a primary mathematical
  workflow, not merely an internal search: `ruzsaSzemerediNumber` in
  `Mathlib/Combinatorics/Extremal/RuzsaSzemeredi.lean:50` and `mulRothNumber` in
  `Mathlib/Combinatorics/Additive/AP/Three/Defs.lean:262` are mathematical extrema defined through
  it, and their specification proofs explicitly supply a witness.  Make that existence evidence an
  input to a proof-carrying greatest-witness operation, migrate those consumers, and keep the
  defaulting recursion private unless literature supports this exact zero-sentinel convention.

- [ ] **Require eventual constancy for monotone-sequence limits.**
  `monotonicSequenceLimitIndex` and `monotonicSequenceLimit` in
  `Mathlib/Order/OrderIsoNat.lean:273` and `:278` assign a junk index/value to a monotone sequence
  that never stabilizes.  Take eventual constancy, with well-foundedness used only to synthesize it.

- [ ] **Put fundamental circuits and cocircuits on their admissible data.**
  `Matroid.fundCircuit` and `Matroid.fundCocircuit` in
  `Mathlib/Combinatorics/Matroid/Circuit.lean:211` and `:690` accept inadmissible data and then need
  not return circuits/cocircuits; documented invalid cases return singleton or inserted sets.  Bundle
  the independence, closure, base, and membership hypotheses already repeated by their valid-case
  theorem families.

- [ ] **Put bundle coordinate changes on chart overlaps.**
  `Bundle.Trivialization.coordChange` in
  `Mathlib/Topology/FiberBundle/Trivialization.lean:754` accepts every base point even though its
  identity, composition, and continuity theorems require membership in the relevant base sets; the
  proof-carrying `coordChangeHomeomorph` at line 795 is the existing strict substrate.  The analogous
  `coordChangeL` in `Mathlib/Topology/VectorBundle/Basic.lean:266` returns the identity outside the
  overlap.  Make the ordinary coordinate-change operations take overlap evidence or a point in the
  overlap.  Keep ambient representatives private, including technical trivialization inverses, and
  only when every exported statement proves that values outside the base set are irrelevant.

- [ ] **Identify the exact event contract for conditional probability.**
  `ProbabilityTheory.cond` in `Mathlib/Probability/ConditionalProbability.lean:76` exposes
  `(μ s)⁻¹ • μ.restrict s` as `μ[· | s]` for every set.  Positive finite mass alone makes the result
  a probability measure (`cond_isProbabilityMeasure_of_finite` at line 154), while concentration on
  the intended event is available under the weaker completion-stable condition
  `NullMeasurableSet s μ` (`ae_cond_mem₀` at line 196).  Do not impose `MeasurableSet s` as the
  exact domain.  Decide separately whether arbitrary non-null-measurable sets should mean
  conditioning on `toMeasurable μ s`; that public interpretation also requires matching literature.
  Otherwise expose conditioning only on the validated event domain.

- [ ] **Replace integration-facing `ContinuousMap.mkD` with an a.e.-continuous-family interface.**
  `ContinuousMap.mkD` in `Mathlib/Topology/ContinuousMap/Basic.lean:320` honestly takes an explicit
  fallback, so it is not a silent totalization; nevertheless it interprets every bare function as a
  continuous map by replacing a noncontinuous function wholesale.  The integration guide in
  `Mathlib/MeasureTheory/SpecificCodomains/ContinuousMap.lean:40` recommends this spelling even when
  every family member is continuous, chiefly to avoid dependent types.  Model the paper-level claim
  instead: an a.e.-continuous family determines an a.e.-class of `C(Y, E)`-valued maps, independent
  of the representative on the null set.  Carry a.e. continuity at that boundary and separately
  require the strong measurability and integrability used downstream; quotienting alone does not
  prove them.  If implementation still needs `mkD`, keep it private behind that boundary so its
  fallback cannot appear in public theorem statements.

- [ ] **Prevent impossible regularity requests from becoming zero operators.**
  `TestFunction.fderivCLM`, `lineDerivCLM`, and supported-map derivatives in
  `Mathlib/Analysis/Distribution/TestFunction.lean:510`, `:564` and
  `Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:379` return zero when the requested
  regularity inequality fails.  Put the inequality in the constructor and automate its proof.

- [ ] **Require a dense domain for `LinearPMap.adjoint`.**
  `Mathlib/Analysis/InnerProductSpace/LinearPMap.lean:152` returns a partial operator, but its
  `toFun` is zero when the original domain is not dense.  The output partiality does not encode this
  missing construction hypothesis; use dense-domain evidence or the adjoint relation.

- [ ] **Give completion extension its full existence and uniqueness contract.**
  `Mathlib/Topology/UniformSpace/Completion.lean:224` evaluates at an arbitrarily selected point
  when the function is not uniformly continuous.  Uniform continuity removes that branch but does
  not by itself make a continuous extension into the original codomain exist: the continuity
  theorem at line 242 also assumes `CompleteSpace β`, and uniqueness needs the relevant separation
  hypothesis.
  Use completeness as a convenient sufficient interface or carry exact pointwise limit
  existence/uniqueness; do not present uniform continuity alone as the mathematical domain.

- [ ] **Make vector-measure products and densities conditional constructions.**
  `VectorMeasure.prod` in `Mathlib/MeasureTheory/VectorMeasure/Prod.lean:52` chooses zero when no
  product exists, and `VectorMeasure.withDensity` in
  `Mathlib/MeasureTheory/VectorMeasure/WithDensityVec.lean:42` uses zero when integrability fails.
  Require `HasProd`/integrability at the ordinary boundary.

- [ ] **Define the intended domain of generalized `InformationTheory.klDiv`.**
  `Mathlib/InformationTheory/KullbackLeibler/Basic.lean:57` accepts arbitrary measures although its
  mass correction is justified for finite measures; for example, zero against an infinite-mass
  measure collapses to zero through `ν.real univ`.  Either restrict the public divergence to finite
  measures or specify and verify a literature-supported infinite-measure definition before
  migrating theorems.

- [ ] **Make `LinearMap.index` carry Fredholm-style finiteness.**
  `Mathlib/Algebra/Module/LinearMap/Index.lean:40` subtracts natural `finrank`s of kernel and
  cokernel without finite-rank hypotheses.  State the appropriate finiteness assumptions and audit
  the intended general-ring scope.

- [ ] **Define the intended module-level and vector-space Euler characteristics separately.**
  `GradedObject.eulerChar` and its complex wrapper in
  `Mathlib/Algebra/Homology/EulerCharacteristic.lean:118` inherit zero from `finsum` on infinite
  support and from `finrank` on infinite-rank terms.  The construction assumes only `[Ring R]`, so
  "finite-dimensional objects" is not its general domain: a module can have finite nonzero rank
  without being finite, and torsion modules can have genuine rank zero.  For the existing invariant,
  require finite support of the `finrank` summands rather than finite actual object support, and
  audit whether finite rank or a cardinal/extended rank is intended.  Give the usual
  finite-dimensional vector-space Euler characteristic its own precise interface.  Also correct the
  module overview's claim that every module not free of finite rank receives zero.

- [ ] **Require a finite residue field for elliptic local factors.**
  `WeierstrassCurve.localPolynomial` in
  `Mathlib/AlgebraicGeometry/EllipticCurve/LFunction.lean:43` permits an infinite residue field;
  `Nat.card` then makes its field size and point count zero.  Propagate finite-residue-field evidence
  through local power series and Euler factors.

- [ ] **Make analytic and meromorphic orders domain-bearing.**
  `analyticOrderAt`/`analyticOrderNatAt` in `Mathlib/Analysis/Analytic/Order.lean:47` and `:61`, and
  `meromorphicOrderAt` in `Mathlib/Analysis/Meromorphic/Order.lean:50`, return zero outside their
  analytic/meromorphic domains; the natural analytic order also collapses genuine infinite order.
  Require the germ hypothesis and retain infinity until finite order is proved.

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
  `Mathlib/RingTheory/UniqueFactorizationDomain/NormalizedFactors.lean:35` likewise return empty data
  at zero.  Use a nonzero carrier or explicit failure for finite lists/counts; keep units admissible
  with empty factorization.  `Associates.factors` returns `⊤` at zero
  (`Mathlib/RingTheory/UniqueFactorizationDomain/FactorSet.lean:223`), which is a useful internal
  extended-value precedent but not literature evidence for a public convention.

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

- [ ] **Make conditional expectations carry their measure-theoretic hypotheses.**
  `condExp` in `Mathlib/MeasureTheory/Function/ConditionalExpectation/Basic.lean:102` and
  `condLExp` in `Mathlib/MeasureTheory/Function/ConditionalLExpectation.lean:73` return zero when the
  sigma algebra is not subordinate or the restricted measure is not sigma-finite; `condExp`
  additionally returns zero when integrability fails.  Preserve `condLExp`'s genuine extended
  nonnegative values, bundle the sigma-algebra/measure evidence, and require integrability only for
  the finite Bochner-valued construction.

- [x] **Require measurable random variables for conditional distributions.**
  `ProbabilityTheory.condDistrib` now requires joint a.e. measurability of `fun a ↦ (X a, Y a)`,
  normally synthesized by `fun_prop`, while retaining the normal freedom to choose versions on null
  conditioning fibres.

- [x] **Require measurability in `Kernel.map`.**
  `Kernel.map` now takes a measurability proof, normally synthesized by `fun_prop`; the zero fallback
  and the separate `mapOfMeasurable` constructor were removed.

- [ ] **Require s-finiteness in kernel product constructors.**
  `Kernel.compProd` in
  `Mathlib/Probability/Kernel/Composition/CompProd.lean:69` returns zero when either kernel is not
  s-finite.  Promote s-finiteness to the construction boundary for `Kernel.prod` and
  `Kernel.compProd` and migrate their consumers.

- [ ] **Make Radon--Nikodym data conditional on decomposition existence.**
  `Measure.rnDeriv` and `Measure.singularPart` in
  `Mathlib/MeasureTheory/Measure/Decomposition/Lebesgue.lean:80` and `:73` return zero without
  `HaveLebesgueDecomposition μ ν`.  Require that evidence or return a bundled decomposition; apply
  the same review to signed and complex vector-measure wrappers.

- [ ] **Move continuous functional calculus to its checked core.**
  `cfc` and `cfcₙ` in
  `Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Unital.lean:307` and
  `Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/NonUnital.lean:215` return zero when
  the element predicate or continuity conditions fail (and,
  nonunital, when `f 0 ≠ 0`).  Make `cfcHom`/`cfcₙHom` the strict substrate and automate the
  real obligations at the primary interface.

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

- [ ] **[S] Distinguish finite product metric spaces from Euclidean space.**
  The instance for `Fin n → ℝ` is the finite Pi metric with sup distance, as documented and defined
  in `Mathlib/Topology/MetricSpace/Pseudo/Pi.lean:16` and `:30`.  Thus the distance between
  `![1, 0]` and `![0, 1]` is one.  The usual Euclidean metric is carried by
  `EuclideanSpace ℝ (Fin n)`, defined as `PiLp 2` in
  `Mathlib/Analysis/InnerProductSpace/PiL2.lean:114`, where the same distance is `√2`.  In metric or
  inner-product contexts, do not treat a bare Pi type as an unqualified Euclidean space, Euclidean
  ball, or orthonormal geometry.  It remains a faithful coordinate-vector representation of `ℝⁿ`
  when no norm or metric semantics are asserted.  Use `EuclideanSpace` for L2 geometry, or explicitly
  say that the product/sup metric is intended.  A future lint should inspect suspicious declarations
  and docstrings without rejecting genuine product-metric uses.

- [ ] **[S--M] Distinguish the zero-padded singular-value sequence from a finite singular-value
  family.**
  `LinearMap.singularValues` in
  `Mathlib/Analysis/InnerProductSpace/SingularValues.lean:94` is a countably infinite sequence whose
  finite-dimensional tail is zero.  The module documentation at lines 18--19 and 36--51 explicitly
  chooses this representation to avoid dependent indexing, but a source-code design choice does not
  establish a mathematical convention.  Find literature using the same infinite zero-padded
  sequence before retaining it publicly.  Otherwise keep it private and provide the
  finite/domain-dimension/rank-indexed family used by the target literature.  Audit downstream
  cardinality, positivity, product, and ordering statements for the intended index set.

- [ ] **[L] Distinguish zero-encoded element order from an extended order.**
  `orderOf` and `addOrderOf` in `Mathlib/GroupTheory/OrderOfElement.lean:178` encode infinite order as
  zero.  The encoding is lossless because every finite order is positive and
  `orderOf_eq_zero_iff` at line 211 characterizes the sentinel, but losslessness alone does not make
  zero the literature-standard mathematical value of infinite order.  Find literature using this
  exact convention before retaining the ordinary name; otherwise use an extended-valued invariant
  and require `IsOfFinOrder`/`IsOfFinAddOrder` for a natural-valued projection.  Keep the zero
  encoding private rather than exporting a second public order operation merely for implementation
  convenience.

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

- [ ] **[S] Remove the unused `Integrable[𝓐]` explicit-instance escape hatch.**
  `Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:64` expands the identifier-shaped form
  directly to `@Integrable _ _ _ _ 𝓐`, but the maintained Lean trees contain no consumer beyond the
  declaration itself.  Give the anonymous σ-algebra binder a stable name if explicit application is
  needed, use ordinary named-argument syntax, and add a negative syntax test before deleting the
  notation.

- [ ] **[S--M] Remove the `P[X]` expectation macro that competes with element lookup.**
  `Mathlib/Probability/Notation.lean:48`--`:53` expands arbitrary adjacent terms `P[X]` to an
  integral against the explicit measure `P` and warns that the grammar conflicts with Lean's
  `GetElem` notation.  Prefer the named integral API while retaining `P` explicitly.  Do not replace
  it mechanically with `𝔼[X]`: that notation uses the ambient `volume` measure and is equivalent
  only when `P` is that selected measure.  Add a regression test that an invalid list lookup is
  diagnosed as a lookup error rather than reconsidered as expectation syntax.

- [ ] **[S] Remove the exported Diophantine proof-DSL surface.**
  `Mathlib/NumberTheory/Dioph.lean:489`--`:631` exports `D∧`, `D∨`, `D∃`, `D+`, and related notation
  for named `Dioph` closure theorems, but every maintained use is confined to that file and `D≠` and
  `D/` have no consumer.  Prefer the named lemmas where they are at least as readable; if a compact
  spelling materially helps the long internal constructions, keep it file-local rather than as a
  public parser dialect.  Remove the unused forms and verify the elaborated logical grouping of the
  subtraction, remainder, division, and Pell constructions.

- [ ] **[M] Give `ordProj` and `ordCompl` searchable declaration heads.**
  `Mathlib/Data/Nat/Factorization/Defs.lean:326`--`:334` introduces only the notations
  `ordProj[p] n` and `ordCompl[p] n`, expanding to `p ^ n.factorization p` and
  `n / ordProj[p] n`; there is no declaration with either apparent identifier.  Introduce named
  `Nat` operations, migrate the roughly 37 notation occurrences across three maintained files, and
  coordinate their mathematical domains with the separate factorization backlog.  Delete the
  identifier-shaped bracket forms after migration; any genuinely conventional symbolic surface
  should be proposed and justified separately.

- [ ] **[M] Give pair affine span a searchable head without asserting nondegeneracy.**
  `Mathlib/LinearAlgebra/AffineSpace/AffineSubspace/Defs.lean:1075`--`:1077` defines
  `line[k, p₁, p₂]` only as notation for the affine span of a generated pair.  The 154 textual uses
  across 18 maintained files cannot search for or apply a declaration named by the apparent head.
  When `p₁ = p₂`, this affine span is a singleton, not a one-dimensional line.  Introduce a named
  pair-span operation whose contract preserves that degenerate case, and reserve an unqualified
  affine-line declaration for an interface carrying whatever nondegeneracy and scalar hypotheses
  its dimensional claim needs.  Make any retained notation expand through the accurately named
  operation; remove the bracket form only if downstream comparison supports that API decision.

- [ ] **[M] Make `RatFunc K` canonical over the colliding `K⟮X⟯` notation.**
  `Mathlib/FieldTheory/RatFunc/Defs.lean:71` uses the same `⟮...⟯` delimiters as the generated-field
  macro in `Mathlib/FieldTheory/IntermediateField/Adjoin/Defs.lean:529`.  With both scopes active,
  `K⟮X⟯` selects the rational-function type, so adjoining an element literally named `X` requires a
  type annotation; current workarounds include `F⟮(X : F⟮X⟯)⟯` in
  `Mathlib/NumberTheory/FunctionField.lean:207`.  Migrate the roughly 337 textual `⟮X⟯` matching
  lines across nine maintained files to the searchable `RatFunc K` head, checking each mixed nested
  use.  Retain `F⟮x₁, ..., xₙ⟯` for `IntermediateField.adjoin`: it exposes all generators, has a
  stable named expansion, and is materially clearer than spelling the generated finite set.

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

- [ ] **[M] Share tuple/curried implementations without presuming one public theorem name.**
  `Mathlib/Algebra/BigOperators/Group/Finset/Sigma.lean:51`--`:101` maintains four adjacent
  `prod_*`/`prod_*'` pairs whose primed proofs are direct applications of the tuple-function
  versions; `@[to_additive]` generates the corresponding sum families.  The pattern continues in
  `Mathlib/Data/Fintype/BigOperators.lean:267`--`:293`, while
  `Mathlib/Algebra/BigOperators/Expect.lean:258`--`:270` proves `expect_product` and
  `expect_product'` separately, and
  `Mathlib/Topology/Algebra/InfiniteSum/Constructions.lean:162`--`:172` gives both
  `Multipliable.tprod_prod'` and `Multipliable.tprod_prod_uncurry` together with their additive
  versions.  Reuse one proof or generate exact transports where possible, but retain multiple public
  views when they materially improve theorem search, rewrite orientation, elaboration, or
  automation.  Correct docstrings that currently call a curried argument "uncurried."  Classify
  `prod_sigma`/`prod_sigma'` separately because the `Sigma` value may be the genuine dependent
  indexing domain rather than a presentation tuple.

- [ ] **[M] Audit bare bridge families for generated proofs and useful orientations.**
  `Set.image_prod`, `Set.image_uncurry_prod`, and `Set.image2_curry` in
  `Mathlib/Data/Set/NAry.lean:73`--`:85` state one image computation through three spellings.
  `Mathlib/Data/Finset/NAry.lean:276`--`:281` gives both directions definitionally, and
  `Mathlib/Order/Filter/NAry.lean:53`--`:59` and `:159`--`:166` chains four manually named views of
  the same `map`/`map₂` bridge.  Audit the similarly mechanical
  `uniformContinuous₂_curry` bridge in `Mathlib/Topology/UniformSpace/Basic.lean:923`--`:936`,
  `Primrec₂.uncurry`/`Primrec₂.curry` in
  `Mathlib/Computability/Primrec/Basic.lean:325`--`:388`, and the paired pointwise-algebra
  simplification lemmas in `Mathlib/Algebra/Group/Pi/Lemmas.lean:480`--`:518` and
  `Mathlib/Algebra/Notation/Pi/Basic.lean:121`--`:129`.  Select an implementation normal form where
  these are ordinary multiargument functions, but determine public names, rewrite directions, and
  `[simp]` attributes from real consumers rather than theorem equivalence alone.  Generate
  mechanical proofs when they reduce maintenance without degrading discovery.  Do not
  remove `Primrec₂` itself merely because its implementation encodes two arguments by a product,
  and do not merge `Option.map₂_curry` with `Option.map_uncurry`: independent optional arguments
  and one optional pair are different semantic inputs.

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
- [x] **Witness choice alone is not a defect.**  `LinearIndependent.repr` in
  `Mathlib/LinearAlgebra/LinearIndependent/Defs.lean:462` is the positive control: its input carries
  both linear independence and span membership and the implementation is the inverse of a proved
  linear equivalence.  Continue to flag reachable invalid branches or names asserting unsupported
  uniqueness.  `Function.invFun`, `Function.extend`, and `LinearMap.leftInverse` remain separate
  audit candidates: first distinguish a legitimate chosen preimage or representative from a name or
  theorem that falsely asserts inverse laws.
- [x] **An explicit default does not justify a public mathematical operation.**  A technical
  representative constructor may remain only privately behind a proved boundary that makes its
  fallback unreachable or proves representative independence.  The integration-facing
  `ContinuousMap.mkD` entry above remains a candidate until its proposed a.e.-class interface is
  validated against real consumers.
- [x] **Conditional expectation and probability brackets are conventional secondary surfaces.**
  `μ[f | 𝓐]`, `μ[|s]`, and `μ[t | s]` have stable named expansions, preserve nesting, and elaborate
  correctly when both scopes are active.  Keep the notation; the construction contracts of `condExp`
  and `ProbabilityTheory.cond` remain separate audit candidates.  In particular, do not assume that
  ordinary measurability is the exact event domain when null measurability suffices.
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
