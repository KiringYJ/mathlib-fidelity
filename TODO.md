# Mathematical fidelity and API hygiene backlog

This backlog tracks unresolved audit candidates, planned paper formalizations and Palomar
submissions, and implementation work for adopted policies in [FORK_DESIGN.md](FORK_DESIGN.md).
[CHANGELOG.md](CHANGELOG.md) records significant completed changes.

An audit candidate is a hypothesis to investigate. Its diagnosis and proposed replacement must
pass the fidelity gate below. The accepted-design sections track implementation of recorded designs.
Imperative wording in a candidate heading names the suspected problem.

Mathematical fidelity is not the same as partiality or proof-carrying syntax.  A total operation may
be a genuine extended invariant, an order-theoretic operation, or a choice operator whose input
carries existence evidence, whose theorems prove the specifying property, and whose specification
determines a unique value.  When the specification determines its object only up to an
equivalence, such as almost-everywhere equality, the public object is the equivalence class, not a
chosen representative (`FORK_DESIGN.md`).  A no-witness branch is still a fallback governed by the
scoped completion and foundational dependency rule below, unless it occurs only in a private witness
for a Prop-valued existence statement. Conversely, adding a proof
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
- **L**: a cross-module API with notation, instances, or many downstream consumers.
- **XL**: foundational hierarchy or ubiquitous notation, requiring substantial design validation.

Every accepted migration completes its selected scope in one delivery, regardless of effort bucket.
Experiments and incremental edits are internal work, not transitional API deliveries. An L migration
may finish while a genuinely independent XL problem in its existing substrate remains a separate
TODO, provided its own domain, specification, proofs, and consumer migration are complete. Identify
the lower-level declarations and obligation, and prove valid-domain use or independence from any
lower-level fallback. Do not reclassify unfinished parts of the selected API as XL to defer them.

Before promoting an unchecked candidate to an implementation task:

1. state the intended object by a specifying or universal property, not by the current
   implementation or proposed carrier;
2. determine its exact domain and separate necessary conditions from convenient sufficient
   hypotheses supplied by typeclasses or automation;
3. classify the current behavior as an independently specified total object, choice of a unique
   value, chosen representative of an equivalence class, checked projection, or fallback.
   Require an independent total object's specifying properties to determine its value at every
   input, including degenerate cases. Record the exact mathematical source for those properties.
   A value assigned solely to make a partial operation total is a fallback regardless of its use
   in other libraries. Replace a chosen representative by its class and remove fallbacks from
   the permanent public interface.
4. test positive, negative, degenerate, characteristic-sensitive, and nonunique examples so that a
   strict facade does not exclude valid mathematics or manufacture canonicity;
5. audit whether the proposed name and notation communicate that exact object without inviting a
   standard but different reading, then choose among a relation, extended-valued invariant,
   canonical value, equivalence class, subtype, proof argument, or explicit partiality type; and
6. validate the candidate in representative consumers and record it as accepted, reframed,
   rejected, or still unknown before committing to its replacement. These experiments are internal
   design evidence, not a separate prototype delivery or a substitute for a completed migration.

For an accepted migration, replace the selected operation and its affected callers completely.
Delete its fallback and retired interface rather than retaining private helpers, compatibility
aliases, a dual API, or a transitional layer. Prove agreement on the valid domain without retaining
the old operation as a compatibility surface. If an independent existing lower-level interface
requires a total value, such as a set function defined on every set, it may remain a separate
foundational TODO. Keep any necessary residual branch anonymous at its construction site, prove
unreachability or independence, and name the lower-level interface and consumers in the TODO. The
selected API must already be faithful; do not claim that this also removes the lower-level problem.
A private witness used only inside a Prop-valued existence proof, to which no public definition
unfolds, is not an operational compatibility layer. Audit statements that exploit fallback branches,
add negative tests for the actual boundary, and run affected checks at the final source state.

The complete-migration contract and independent foundational dependency boundary in `FORK_DESIGN.md`
are canonical. A TODO can track separate foundational work but cannot discharge a missing in-scope
proof, consumer migration, or removal. A literature-supported total object is reviewed on its own
mathematics; it is not a renamed extension of the partial operation.

The official-Lean and operator-fidelity boundary in `FORK_DESIGN.md` is adopted. Ban unfaithful
operators in maintained mathematical statements and definition semantics, including private and
inherited declarations, without banning legitimate carriers such as core `Rat` or `Nat`. Remove
replaceable uses from fork-controlled proofs and proof-producing automation too. Unavoidable
dependencies owned by the official toolchain may remain proof-only, with the actual declarations
and faithful boundary recorded; do not patch Lean to eliminate them. Aliases, wrappers, hidden casts,
and instance data cannot conceal an excluded semantic dependency. The migration entries below
track outstanding work for individual operator families.

## Paper formalizations and Palomar submissions

These unchecked items record intended Lean formalization and Palomar submission projects.
For papers awaiting formalization, audit the source statements and hypotheses, prerequisite APIs,
and overlap with existing declarations before selecting exact theorem coverage and destination modules.

- [ ] **Formalize Walter Rudin, *Injective Polynomial Maps Are Automorphisms*.**
  *The American Mathematical Monthly* **102**(6) (1995), 540-543.
  [DOI: 10.1080/00029890.1995.12004615](https://doi.org/10.1080/00029890.1995.12004615).
  The publisher's online publication date, 18 April 2018, is distinct from the original journal year.
  Palomar submission: planned after the formalization is complete.

- [ ] **Formalize Walter Schachermayer, *On some classical measure-theoretic theorems for
  non-sigma-complete Boolean algebras*.**
  *Dissertationes Mathematicae (Rozprawy Matematyczne)* **214** (1982).
  [Bibliographic record and full text](https://pldml.icm.edu.pl/pldml/element/bwmeta1.element.zamlynska-46047466-7a42-41f0-b7cf-c4e008ff3e05).
  Palomar submission: planned after the formalization is complete.

- [ ] **Formalize Paolo Aniello, Sonia L'Innocente, Stefano Mancini, Vincenzo Parisi, Ilaria Svampa,
  and Andreas Winter, *Characterising the Haar measure on the p-adic rotation groups via inverse
  limits of measure spaces*.**
  *Expositiones Mathematicae* **43**(2) (2025), article 125592.
  [DOI: 10.1016/j.exmath.2024.125592](https://doi.org/10.1016/j.exmath.2024.125592);
  [arXiv:2401.14298](https://arxiv.org/abs/2401.14298).
  Palomar submission: planned after the formalization is complete.

- [ ] **Submit D. A. Overdijk, F. H. Simons, and J. G. F. Thiemann, *A comment on unions of rings*,
  to Palomar.**
  *Indagationes Mathematicae (Proceedings)* **82**(4) (1979), 439-441.
  [DOI: 10.1016/1385-7258(79)90045-3](https://doi.org/10.1016/1385-7258(79)90045-3).
  Formalization is complete; Palomar submission is pending. The existing development is in
  [Mathlib/MeasureTheory/SetRing.lean](Mathlib/MeasureTheory/SetRing.lean), including
  `MeasureTheory.IsSetSigmaRing.exists_eq_iUnion` and
  `MeasureTheory.IsSetSigmaRing.eventually_constant_of_monotone`.

## Fork CI rollout

- [ ] **Validate the first published hosted runs and cold-build capacity.**
  Inspect `Fidelity CI`, `Fidelity proof checks`, and the portable workflow checks
  on the published workflow revision. Confirm Linux and Windows cache-test execution,
  PR merge-SHA reporting, actual cache restore/save behavior, and the full command
  chain. Record any concrete capacity failure before selecting runner or sharding
  changes. Local syntax/tests do not certify hosted execution, full library
  success, or the separate proof-status admission contract below.
- [ ] **Enforce the Archive import boundary in Fidelity CI.** Check the
  resolved import closure of `Mathlib` and every `Mathlib.*` module for
  `Archive` and `Archive.*`. Report an offending import path. Verify direct
  and transitive violations and the permitted imports from `Archive` to
  `Mathlib`. See the
  [placement policy](FORK_DESIGN.md#mathematical-scope-and-placement).

## Conjectures and proof status -- accepted design, pending implementation

The [conjecture and proof-status contract](FORK_DESIGN.md#conjectures-and-proof-status) is adopted.
These unchecked items track implementation of that decision; they are not hypotheses about whether
the inherited `def`-based whole-statement design should be retained. Genuine conjectures and results
awaiting formalization share one Lean mechanism and differ only in epistemic metadata. Implement
and validate the registry, dependency collector, and admission gate before migrating library roots
or publishing status labels. The interface spellings below are proposed, and recording this backlog
does not authorize their implementation in a documentation task.

- [ ] **Register both epistemic kinds as single theorem declarations with an entire-proof placeholder.**
  Add the proposed `@[conjecture]` registry using the existing Lean environment/attribute substrate.
  Record Genuine conjecture versus Awaiting formalization with source/statement evidence as root
  metadata. Use exactly the same theorem type, entire-proof placeholder, dependency/axiom checks,
  and CI behavior for both kinds; an informal proof does not discharge a Lean placeholder.
  Validate that registration identifies a theorem with a complete mathematical type with no direct
  holes, whose dependencies satisfy the admission gate, and that each open root owns only its
  designated whole-proof `by sorry` placeholder.
  Reject registered `def`/`axiom` substitutes and partial proofs with nested holes. Check bodies
  after elaboration finishes, including asynchronous values. A completed proof keeps the same
  declaration and statement; derive its status from remaining dependencies rather than keeping a
  permanent Conjecture label. Acceptance fixtures must cover valid quantified roots, malformed
  registration, holes in types, synthetic holes, and completion using either no unresolved roots or
  another unresolved root of either epistemic kind. Test that changing only the kind leaves the
  proof term, dependency set, and formal status unchanged.

- [ ] **Collect declaration dependencies and placeholder ownership as structured data.**
  Reuse or factor the traversal in `Mathlib/Util/PrintSorries.lean`, with
  `MathlibTest/Util/PrintSorries.lean` as existing traversal evidence. Its `collectSorries` returns
  rendered `MessageData` and shares declaration/sorry deduplication state across roots; do not parse
  that output or treat `#print axioms` reporting `sorryAx` as named conjecture attribution.
  Retain per-root edges, owning declarations and occurrences, named conjecture sets, and witness
  paths through types and values of theorem/definition/opaque helpers. Preserve ownership even for
  identical sorry expressions, and audit reachable private/generated declarations rather than
  inheriting the diagnostic blacklist. Capture source locations for queries; `PrintSorries.lean`
  currently records source positions as unimplemented. Define and test the admitted module scope:
  an imported environment includes its imports but cannot cover modules absent from that root.
  Acceptance covers direct/transitive and multi-root dependencies, shared helpers, imported/private
  helpers, type dependencies, repeated placeholders, and a proof that has ordinary hypotheses but
  uses no unresolved root. Replacing a root proof must invalidate affected cached classifications and
  recompute the whole dependent chain.

- [ ] **Enforce the three-status admission gate and an explicit trusted axiom base.**
  Run the ownership/axiom audit on the final environments for all admitted library targets.
  Admit only Conjecture, Conditional, and Unconditional; every other local or reachable proof gap,
  synthetic sorry, elaboration failure, or unapproved axiom is a CI error. A theorem that uses RH
  and also contains its own `sorry` must fail rather than receive a Conditional label.
  Review the axiom allowlist, including standard logical axioms and any evaluation trust, and
  make unapproved dependencies a hard failure. The current `assert_no_sorry` in
  `Mathlib/Util/AssertNoSorry.lean` rejects transitive `sorryAx`; it is not a named-root gate.
  Reconcile warning handling in `.github/workflows/fidelity-ci.yml` (`lake build --wfail`)
  with the narrow registered-root exception without suppressing unrelated diagnostics.
  The inactive upstream snapshots in `.github/upstream-workflows/build_template.yml`,
  `.github/upstream-workflows/daily.yml`, and `scripts/lake-build-with-retry.sh` retain
  upstream behavior; the archived nanoda configuration has
  `unpermitted_axiom_hard_error: false`. Neither that snapshot nor the active bundled
  kernel replay establishes this contract. Audit `Wanted/` `proof_wanted` goal metadata separately from proved
  results: its private `ProofWanted P` wrappers are neither proofs of `P` nor `sorryAx` roots.
  The admission gate excludes guarded negative fixtures in `MathlibTest/` and `FidelityTest/`.
  Unowned proof placeholders reached through private library helpers still fail the gate.
  Acceptance requires positive
  three-status fixtures and negative tests for unregistered, hidden/imported, nested, type-level, synthetic,
  and extra-local placeholders plus unapproved axioms. Do not publish an admitted index after a
  failed or incomplete audit.

- [ ] **Migrate the inherited Riemann hypothesis and audit other conjecture interfaces.**
  `RiemannHypothesis` in `Mathlib/NumberTheory/LSeries/RiemannZeta.lean` is currently a
  `@[wikidata Q205966] def ... : Prop`. Its exact statement is
  `∀ (s : ℂ) (_ : riemannZeta s = 0) (_ : ¬∃ n : ℕ, s = -2 * (n + 1)) (_ : s ≠ 1), s.re = 1 / 2`.
  Once the registry and gate are ready, replace the proposition definition with one registered
  theorem of Genuine conjecture kind using that same quantified statement and entire-proof
  placeholder; preserve the mathematical exclusions and Wikidata attribution, and apply the
  deliberate naming policy.
  Remove the old public proposition alias rather than retaining it beside a second proof theorem.
  The 2026-10-11 tracked-source scan found only this declaration and no direct consumers in
  `Mathlib/`, `MathlibTest/`, `Archive/`, `Counterexamples/`, or `Wanted/`; recheck at migration.
  The codebase-wide inventory below covers both epistemic kinds and actual consumers. Migrate
  actual `RH → P` or `hRH` interfaces to ordinary conclusions whose proofs use the registered
  conjecture constant. Do not invent such consumers or rewrite ordinary mathematical hypotheses.
  Acceptance requires exact statement correspondence, an open-root status, direct/transitive
  downstream status fixtures, absence of the obsolete public alias and conjecture-antecedent
  interfaces in the migrated family, relevant builds/linters, and final-state downstream checks.
  Completing this API migration does not prove RH.

- [ ] **Expose proof status in Lean, the editor, generated documentation, and search.**
  Add a query provisionally spelled `#status T` and a build-generated status index, for example
  JSON, from the same admitted environment and reviewed trust base. Display the three statuses,
  named unresolved roots with their epistemic kinds/source evidence, dependency paths, and source
  links. Provide an unconditional-only filter, root-based search, and reverse lookup of dependent
  results; author-maintained metadata belongs only on registered roots. Keep declarations in subject
  modules with stable
  mathematical names. Acceptance requires agreement among query/editor/docs/search output and the
  CI classifier, plus regeneration after a root is proved: descendants become Unconditional only
  when no unresolved root of either epistemic kind remains. An epistemic-only metadata change must
  not change formal status. Labels describe the current formal proof, not logically minimal
  hypotheses. Multiple proof records for one statement are a possible later extension, not a
  reason to duplicate public theorem APIs in this migration.

### Codebase-wide migration inventory (2026-10-11)

The scan covered all 9,432 tracked files: 9,203 Lean files and 229 other text files, with no
nonignored untracked source files. The Lean scope includes `Mathlib/`, `MathlibTest/`, `Archive/`,
`Counterexamples/`, `Wanted/`, tooling, documentation examples, and generated import roots.
Keyword/status hits were supplemented by declaration and explicit/inferred Prop-return inventories,
then checked against their source context and actual consumers in three disjoint review lanes.
Dependency checkouts and build artifacts are not intake targets. This is a source census and a
reviewed lexical candidate inventory, not an elaborated-environment proof of semantic exhaustiveness.
Recheck source correspondence and current epistemic evidence at migration; the scan does not prove
every source statement or admit it merely because it appears in this list.

All eligible unresolved roots below use the same theorem-with-sorry/registry/DAG/CI mechanism.
Genuine conjecture versus Awaiting formalization is epistemic metadata only. Existing complete
proofs stay complete; do not introduce a placeholder dependency into a proved special case merely
to simplify the interface migration.

- [ ] **Migrate the FLT whole-statement alias and its actual public interfaces.**
  `FermatLastTheorem` in `Mathlib/NumberTheory/FLT/Basic.lean:64` is the global proposition
  `∀ n ≥ 3, FermatLastTheoremFor n`. The module identifies it as the established Wiles/Taylor-Wiles
  theorem, while this checkout has no complete proof of that global statement. Register the
  direct theorem statement with epistemic kind Awaiting formalization until its formal proof is
  supplied. Preserve the exponent bound, the nonzero natural-number operands, and source evidence.
  Retain `FermatLastTheoremWith`, `FermatLastTheoremFor`, `FermatLastTheoremWith'`, and
  `FermatLastTheoremForThreeGen` as reusable parameterized properties/descent auxiliaries; some
  parameter choices are false. Keep the existing exponent-three and exponent-four proofs
  (`Mathlib/NumberTheory/FLT/Three.lean:749`, `Mathlib/NumberTheory/FLT/Four.lean:267`)
  independent of the unresolved global root.
  Audit `FermatLastTheorem.of_odd_primes` in `Mathlib/NumberTheory/FLT/Four.lean:276`: it is a proved reduction from
  an explicit odd-prime-family premise, not a complete proof of FLT. Reconcile its public interface
  under the new whole-root policy while preserving the valid reduction and ordinary predicate
  transport/equivalence lemmas. The other global consumer is the Euler implication below.
  Check catalogue references in `docs/100.yaml:141` and `docs/1000.yaml:53`.
  Acceptance: one direct registered theorem, source-exact statement and epistemic provenance,
  deliberate consumer/catalogue migration, removal of the old whole-statement alias, and unchanged
  unconditional status of already proved subcases.

- [ ] **Migrate Graham's distinguished theorem family without changing its formula.**
  `Nat.GrahamConjecture` in `Mathlib/NumberTheory/MaricaSchoenheim.lean:34` is a `def : Prop`
  with parameters `n : ℕ`, `f : ℕ → ℕ` and statement
  `n ≠ 0 → StrictMonoOn f (Set.Iio n) → ∃ i < n, ∃ j < n, (f i).gcd (f j) * n ≤ f i`.
  Its docstring explicitly says the conjecture is now a theorem in the literature. Use Awaiting
  formalization for the full registered theorem family; ordinary parameters do not make this
  distinguished named statement a generic property to retain as a separate whole-statement alias.
  Migrate the actual consumer `Nat.grahamConjecture_of_squarefree` at line 38 to its directly
  stated squarefree result and keep its existing complete proof independent of the unresolved
  general root. No other source consumer was found. Preserve the exact quantifiers and inequality;
  do not add a positivity hypothesis mechanically when the definition does not have one.
  Acceptance: source correspondence, one registered family, removal of the distinguished alias,
  and the squarefree theorem still checked without an unresolved-root dependency.

- [ ] **Separate the refuted Euler alias from the LPS statement-domain audit.**
  `Counterexamples/EulerSumOfPowers.lean:37-45` has the `abbrev` family
  `Counterexample.SumOfPowersConjectureWith`, `SumOfPowersConjectureFor`, and the universal
  `SumOfPowersConjecture`. The theorems `sumOfPowersConjectureFor_five_false` (line 97) and
  `sumOfPowersConjectureFor_four_false` (line 113) refute instances of that universal claim.
  A scratch Lean check derives `¬ Counterexample.SumOfPowersConjecture` from the latter.
  Never turn the refuted universal into an affirmative registered placeholder of either kind.
  Replace its whole-statement alias interface with a directly stated refutation; retain useful
  exponent/semiring predicates, the proved small-exponent cases, and their refutation/transport
  lemmas. Reconcile `fermatLastTheorem_of_sumOfPowersConjecture` (line 55), whose antecedent is
  the refuted universal statement, rather than using it as a conditional proof route to FLT.
  Keep generic parameterized implications at lines 48, 59, 79, 86, 130, and 150 as genuine
  predicate comparisons where justified, with their assumptions explicit.
  `Counterexample.LanderParkinSelfridgeConjecture` (line 145) is currently the parameterized
  implication `ExistsEqualSumsOfLikePowersFor R k m n → k ≤ m + n` over an arbitrary semiring.
  A second scratch Lean check proves `¬ LanderParkinSelfridgeConjecture ℕ 1 0 0`, witnessed by
  two empty lists. Do not universalize this family unchanged. Audit the cited primary statement,
  arithmetic domain, exponent/length restrictions, positivity, disjointness, and any primitive
  conditions before selecting an exact genuine-conjecture root; keep ordinary existence predicates
  separate. Acceptance: exact source/domain correspondence, no affirmative refuted root, preserved
  existing checked refutations, and a regression for the empty-sum boundary.

- [ ] **Migrate all 34 Wanted goals through reviewed statement and epistemic-kind correspondence.**
  The 18 `Wanted/` source modules contain 34 `proof_wanted` entries. Batteries currently emits a
  private `def ... : ProofWanted P := ⟨⟩` for each bodyless entry: these are goal metadata, not
  proofs of `P`, axioms, or `sorryAx` roots. They do not contaminate surrounding proved theorems.
  The evidence lives in `Batteries/Util/ProofWanted.lean` in the configured dependency; inspect
  the pinned implementation during migration rather than changing or importing that dependency.
  Replace selected goal wrappers with actual registered theorem declarations in their subject
  modules, each with a complete audited type and a whole-proof placeholder of the appropriate
  epistemic kind. Do not merely tag a `ProofWanted P` wrapper as a proved or conditional result.
  The inventory below is complete for this source snapshot; declaration spellings retain their
  source namespace context, which must be preserved during migration.

  | Source under `Wanted/` | Goal declarations | Epistemic evidence / required review |
  | --- | --- | --- |
  | `Analysis/Convex/Cone/Basic.lean` | `ConvexCone.isOpen_hull` | Ordinary formalization goal; audit the API/domain limitation in its TODO. |
  | `Analysis/Real/Pi/Chudnovsky.lean` | `chudnovskySum_eq_pi_inv` | Source presents Chudnovsky's formula; Awaiting formalization candidate. |
  | `CategoryTheory/Limits/Shapes/Countable.lean` | `CategoryTheory.Limits.IsCofiltered.preorder_of_cofiltered`; `CategoryTheory.Limits.IsCofiltered.preorder_of_cofiltered_countable`; `CategoryTheory.Limits.IsCofiltered.hasCofilteredCountableLimits_of_hasSequentialLimits`; `CategoryTheory.Limits.IsCofiltered.hasCountableLimits_of_hasFiniteLimits_and_hasSequentialLimits`; `CategoryTheory.Limits.IsCofiltered.hasCountableColimits_of_hasFiniteColimits_and_hasSequentialColimits` | Five ordinary formalization goals; audit quantifiers, size and category assumptions. |
  | `Combinatorics/SimpleGraph/StronglyRegular.lean` | `SimpleGraph.conway_99` | Source marks Conway's 99-graph existence problem open: Genuine conjecture candidate; verify current source/status before admission. |
  | `Computability/TuringMachine/Computable.lean` | `Turing.TM2ComputableInPolyTime.comp` | Ordinary composition/formalization goal; audit complexity assumptions. |
  | `Data/EReal/Operations.lean` | `EReal.recENNReal_neg_coe_ennreal` | Ordinary formalization goal. |
  | `Geometry/Euclidean/Volume/Measure.lean` | `MeasureTheory.Measure.addHaarScalarFactor_hausdorffMeasure_eq` | Ordinary formalization goal; preserve normalization and dimension. |
  | `Geometry/Manifold/PoincareConjecture.lean` | `ContinuousMap.HomotopyEquiv.nonempty_homeomorph_sphere`; `SimplyConnectedSpace.nonempty_homeomorph_sphere_three`; `SimplyConnectedSpace.nonempty_sdiffeomorph_sphere_three`; `exists_homeomorph_isEmpty_diffeomorph_sphere_seven`; `exists_open_nonempty_homeomorph_isEmpty_diffeomorph_euclideanSpace_four` | Five source-attributed established statements: Awaiting formalization candidates; preserve topological/smooth distinctions and all manifold hypotheses. |
  | `Geometry/Manifold/SmoothEmbedding.lean` | `Manifold.IsSmoothEmbedding.comp`; `Manifold.Diffeomorph.isSmoothEmbedding` | Two ordinary formalization goals. |
  | `GroupTheory/GroupAction/Jordan.lean` | `IsPreprimitive.is_two_pretransitive'`; `is_two_preprimitive_strong_jordan`; `Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isCycle_mem` | Three formalization goals; check the attributed Jordan statements and exact action hypotheses. |
  | `Order/KrullDimension.lean` | `Order.height_of_linearOrder`; `Order.coheight_of_linearOrder` | Two ordinary formalization goals. |
  | `Probability/Combinatorics/BinomialRandomGraph/Defs.lean` | `SimpleGraph.binomialRandom_map_ncard_edgeSet_singleton` | Source requests a restatement; validate it before assigning an epistemic kind. |
  | `Probability/Distributions/Binomial.lean` | `ProbabilityTheory.variance_of_hasLaw_binomial` | Ordinary formalization goal; preserve distribution and parameter assumptions. The former `condVar_of_hasLaw_binomial`, `Var[X; P | m] = P[X | m] * P[1 - X | m]`, was removed as false for `n ≥ 2`: for `m = ⊥` and `Bin(2, 1/2)` the left side is `1/2` and the right side is `1 * 0`; for `n = 1` it is `condVar_of_ae_eq_zero_or_one` in `Mathlib/Probability/Distributions/TwoValued.lean`. |
  | `RingTheory/Congruence/Basic.lean` | `RingCon.comap_ringConGen_equiv` | Ordinary formalization goal with a missing-API note. |
  | `RingTheory/Etale/Descent.lean` | `Algebra.FormallySmooth.of_formallySmooth_tensorProduct_of_faithfullyFlat` | Source cites Raynaud-Gruson/Stacks; audit exact descent hypotheses. |
  | `RingTheory/KrullDimension/Basic.lean` | `MvPolynomial.fin_ringKrullDim_eq_add_of_isNoetherianRing` | Ordinary formalization goal. |
  | `RingTheory/SimpleModule/Basic.lean` | `LinearMap.isSemisimpleModule_of_injective`; `LinearMap.isSemisimpleModule_of_surjective` | Two ordinary formalization goals with API-generalization notes. |
  | `RingTheory/SimpleModule/WedderburnArtin.lean` | `IsSemiprimaryRing.mulOpposite`; `isSemiprimaryRing_mulOpposite_iff`; `IsArtinianRing.isNoetherianRing_iff_isArtinianRing_mulOpposite` | Three ordinary symmetry/formalization goals. |

  The six named/source-established candidates and 27 ordinary formalization goals are not
  automatically assigned Genuine conjecture because their Lean proof is missing. Assign Awaiting
  formalization only with the reviewed mathematical evidence; diagnose malformed or unsupported
  source statements before admission. Complete statement correspondence and ownership checks apply
  equally to both kinds. Reconcile `Wanted.lean`, goal-module imports, `Mathlib/Init.lean`'s
  proof-wanted tooling import, and the CI/index scope deliberately; preserve
  `MathlibTest/BasicFiles/Init.lean`'s `please_prove_this : True` smoke fixture as a test.
  Acceptance: all 34 goals have an explicit reviewed disposition and declaration/source mapping,
  every admitted root uses the common mechanism, no goal wrapper is counted as a proof of its
  statement, no unowned local holes are admitted, and both epistemic kinds pass identical Lean,
  dependency, and CI behavior tests. A metadata-only kind change must not change `D(T)` or status.

- [ ] **Reconcile the smooth Poincare property with exact scoped root statements.**
  `ContinuousMap.HomotopyEquiv.NonemptyDiffeomorphSphere` in
  `Mathlib/Geometry/Manifold/PoincareConjecture.lean:41` is a manifold/dimension-indexed property.
  The source explicitly describes different truth/status by dimension. Retain the genuine
  parameterized property; do not assert it for every dimension. Review only exact distinguished
  statements with their dimensions, signs, and quantifiers before registering either epistemic
  kind. The five existing goal statements to migrate are listed in the Wanted table; they are
  not interchangeable with this smooth property. No other Lean consumer of the property was found.
  Acceptance: precise predicate-versus-statement correspondence, existing topological/smooth
  hypotheses preserved, and no fabricated universal root or duplicate whole-statement alias.

Reviewed exclusions: `Matroid.InvariantCardinalRank` is an ordinary object property with a proved
finitary instance, and `Matrix.IsHadamard` is a matrix predicate; keep their generic assumptions.
Robbins and `Counterexample.aharoni_korman_false` are already proved results. CH/GCH, Kaplansky,
Weinstein, Duffin-Schaeffer and other reference-only hits create no additional declaration migration
in this checkout. External-only catalogue entries (such as Catalan/modularity statements in
`docs/1000.yaml` and reference repositories in `UPSTREAMS.md`) are discovery evidence, not new
local code or an authorized intake task. Deliberate test-suite axiom/opaque/sorry fixtures are
not production conjecture roots; distinguish goal metadata and test scaffolding from result proofs.

## Priority-independent elaboration

The [design policy](FORK_DESIGN.md#priority-independent-mathematical-semantics) is adopted.
Enforcement and coverage are pending foundational work. Implementation requires an explicit task
and uses the official Lean toolchain.

- [ ] **Audit instance and coercion coherence.** Use
  [`OverlappingInstances`](Mathlib/Tactic/Linter/OverlappingInstances.lean) as a starting point for
  local diamonds. Inventory overlapping global candidates and inherited projections in the
  algebraic and order hierarchies, including actions, modules, and algebras. Check whether candidate
  premises can hold together and compare the supplied data by definitional equality. Audit coercion
  chains and elaborator or notation priority where they can change mathematical meaning. Repair
  confirmed conflicts by unifying coherent paths or requiring explicit structures and maps.
- [ ] **Check defaulting at elaboration time.** Track how numerals, overloaded operations, and output
  parameters get their types, including defaults introduced by outer elaborators or generated code.
  [`OperatorPolicy`](Mathlib/Lean/Elab/OperatorPolicy.lean) illustrates interception of selected
  commands. Default instances have their own registry, and a finished term can hide the fact that
  fallback was used. Establish which entry points can enforce the rule and report cases where
  uniqueness cannot be verified. A successful ordinary instance search does not certify uniqueness.
- [ ] **Verify and enforce the covered scope.** Test distinct data at the same class goal,
  propositionally equal but definitionally distinct data, definitionally equal diamonds, and
  proof-irrelevant choices. Test underconstrained numeral and operator defaults, context-determined
  inference, conflicting coercions or notation, and explicit disambiguation. Reorder priorities,
  declarations, and imports with the candidate set fixed and check elaborated statements and data
  definitions. Make violations and unresolved cases fail CI in the covered scope. Inventory
  uncovered entry points before making any repository-wide enforcement claim.

## S -- bounded audit candidates

- [ ] **Put `Height.mulHeight` on nonzero tuples.**
  `Height.mulHeight x` in `Mathlib/NumberTheory/Height/Basic.lean:233` is the product of the maxima
  of the absolute values over the tuple `x` for `x ≠ 0` and `1` for the zero tuple, which the module
  overview calls a convenient junk value that 'allows to avoid the condition `x ≠ 0` in most of the
  results' (`mulHeight_zero`, line 244); `logHeight` (line 272) is its logarithm.  The height is a
  function of a point of projective space, and `Projectivization.mulHeight` in
  `Mathlib/NumberTheory/Height/Projectivization.lean` already takes nonzero representatives.  The
  tuple heights are used in `Height/Basic.lean`, `EllipticCurve.lean`, `MvPolynomial.lean`,
  `Northcott.lean`, `NumberField.lean`, and `Projectivization.lean`.  Decide whether the tuple
  height takes `x ≠ 0`, with the projective version as the public surface, and which results lose
  their hypothesis-free form.  The height `mulHeight₁ x` of a field element is defined at `x = 0`
  without a branch and is not affected.

- [ ] **Audit the junk subgroup for the empty upper set of Archimedean classes.**
  `MulArchimedeanClass.subgroup s` in `Mathlib/Algebra/Order/Archimedean/Class.lean:610` (additively
  `ArchimedeanClass.addSubgroup`) turns an upper set `s` of classes into the subgroup of elements
  whose class lies in `s`; for the empty upper set `s = ⊤` that carrier is empty, and the docstring
  assigns the junk value `⊥` (`subgroup_eq_bot`, line 631).  `ballSubgroup c`, the subgroup of
  `UpperSet.Ioi c`, inherits it at the class `⊤` of the identity (line 663, `ballSubgroup_top` at
  line 682), where the open ball is empty.  The strict form already exists on the finite classes:
  `FiniteMulArchimedeanClass.subgroup` (line 865) adds `⊤` to the upper set and needs no branch.
  `FiniteArchimedeanClass.ball` in `Mathlib/Algebra/Order/Module/Archimedean.lean:67` repeats the
  sentence about `c = ⊤` although its argument is a finite class, so that docstring may be stale.
  The only other consumer is `Mathlib/Algebra/Order/Module/HahnEmbedding.lean`, which uses the
  finite-class `ball` and `closedBall`. Decide whether the unrestricted constructions are needed.
  The subgroup with the stated carrier requires `s ≠ ⊤`, and `ballSubgroup` consequently requires
  `c ≠ ⊤`. If the intended object is the subgroup generated by the ball, specify generation in its
  public interface. The least subgroup containing the empty ball is `⊥`.

- [ ] **Give `Measure.tilted` its exact domain.**
  `Measure.tilted μ f` in `Mathlib/MeasureTheory/Measure/Tilted.lean:42` is `μ.withDensity` of
  `x ↦ ENNReal.ofReal (exp (f x) / ∫ x, exp (f x) ∂μ)`.  When `exp ∘ f` is not integrable the
  Bochner integral is `0`, the real quotient by `0` is `0`, and the result is the zero measure
  (`tilted_of_not_integrable`, line 46; `tilted_of_not_aemeasurable`, line 51), as it is for `μ = 0`
  (`tilted_zero_measure`, line 57); the docstring states the fallback ('Otherwise it is 0').  The
  intended object is the probability measure with density proportional to `exp (f x)`, whose exact
  domain is `Integrable (fun x ↦ exp (f x)) μ` with `μ ≠ 0` (`isProbabilityMeasure_tilted`, line
  126), but the instance `isZeroOrProbabilityMeasure_tilted` (line 138) and
  `tilted_apply_eq_ofReal_integral` (line 118) hold for every `f` through the fallback.  The other
  consumers are `Mathlib/MeasureTheory/Measure/LogLikelihoodRatio.lean`,
  `Mathlib/Probability/Moments/Tilted.lean`, and `Mathlib/Probability/Moments/SubGaussian.lean`.
  Decide whether the ordinary operation takes integrability and `NeZero μ` as proof arguments, or
  whether the unnormalized `withDensity` measure is the primary object and normalization takes the
  positivity and finiteness of the mass, as for `FiniteMeasure.normalize`.

- [ ] **Require measurability in `SimpleFunc.restrict`.**
  `SimpleFunc.restrict f s` in `Mathlib/MeasureTheory/Function/SimpleFunc.lean:751` is
  `piecewise s hs f 0` for a measurable set `s` and the zero function otherwise
  (`restrict_of_not_measurable`, line 754), although a simple function is restricted to a set only
  through its indicator (`coe_restrict`, line 759).  The strict substrate
  `SimpleFunc.piecewise s hs f 0` already exists.  The consumers supply measurable sets: the file
  itself (`restrict_lintegral`, `restrict_const_lintegral`),
  `Mathlib/MeasureTheory/Function/StronglyMeasurable/Basic.lean` (lines 259 to 291 and 426),
  `Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean`, and
  `Mathlib/MeasureTheory/Integral/Lebesgue/Add.lean`.  Decide between taking `hs` as an argument of
  `restrict`, as `Measure.map` takes its measurability, and retiring `restrict` in favour of
  `piecewise`; `map_restrict_of_zero`, `mem_image_of_mem_range_restrict`, and `restrict_mono` then
  lose a case split.

- [ ] **Replace the exported σ-finite exhaustion sets by existence statements.**
  `Measure.sigmaFiniteSetWRT μ ν` in
  `Mathlib/MeasureTheory/Measure/Decomposition/Exhaustion.lean:67` chooses a measurable `s` with
  `μ.restrict s` σ-finite and `μ t = ∞` for every `t ⊆ sᶜ` with `ν t ≠ 0`, and is `∅` when no such
  set exists, which the module overview says happens only if `ν` is not s-finite.  Two sets with the
  property differ by a `ν`-null set (paper argument: the part of one outside the other is a
  countable union of sets of finite `μ`-measure inside the complement of the other), so the
  specification determines an almost-everywhere class of sets and the value is a `Classical.choose`
  representative of it.  `Measure.sigmaFiniteSet` (line 315) is its diagonal case, and
  `AEFinStronglyMeasurable.sigmaFiniteSet`
  (`Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean:977`) chooses a set
  from an existence proof in the same way.  The exhaustion lemmas are stated under `SFinite ν` or
  `IsFiniteMeasure ν`.  The consumers use the sets as witnesses:
  `Mathlib/MeasureTheory/Function/AEEqOfIntegral.lean` and `AEEqOfLIntegral.lean` for the second,
  and `Mathlib/MeasureTheory/Measure/SeparableMeasure.lean`, `WithDensity.lean`, and
  `WithDensityFinite.lean` for the first.  Decide whether the exhaustion lemmas can be stated as
  existence statements with the sets as private witnesses, as the equivalence-class rule of
  `FORK_DESIGN.md` asks, and coordinate with the item on chosen almost-everywhere representatives in
  the L bucket.

- [ ] **Require probability factors in `Measure.infinitePi`.**
  `Measure.infinitePi μ` in `Mathlib/Probability/ProductMeasure.lean:469` is defined for every
  family of measures by an `if` and is `0` unless every `μ i` is a probability measure; the
  docstring says that the `if` lets it 'be manipulated without carrying a proof that the measures
  are probability measures'.  The intended object is the unique measure that gives cylinders the
  finite product measures (`isProjectiveLimit_infinitePi`, `eq_infinitePi`), and the lemmas about it
  assume `[∀ i, IsProbabilityMeasure (μ i)]`, so no theorem uses the `0` branch.  `infinitePiNat` in
  the same file (line 114) already takes the instance.  The consumers are
  `Mathlib/Probability/Independence/InfinitePi.lean`, `Mathlib/Probability/HasLawExists.lean`,
  `Mathlib/Probability/Distributions/SetBernoulli.lean`, and
  `Mathlib/Probability/Combinatorics/BinomialRandomGraph/Defs.lean`.  Decide whether the ordinary
  operation takes the instance as an argument, which removes the `if`, and whether the exact domain
  is wider than probability factors, for example finitely many σ-finite factors, before choosing the
  typeclass.

- [ ] **Keep construction devices of the covering and Haar theorems out of the public API.**
  Several public definitions are scaffolding whose values off the intended inputs are garbage by
  their own documentation or are chosen elements.  `VitaliFamily.limRatio` and `limRatioMeas` in
  `Mathlib/MeasureTheory/Covering/Differentiation.lean:92` and `:416` carry the docstring 'Do *not*
  use this definition: it is only a temporary device' (`limRatio` is `limUnder` of the ratio,
  `limRatioMeas` an `AEMeasurable.mk` representative of it).  `Besicovitch.TauPackage.index` and
  `lastStep` in `Mathlib/MeasureTheory/Covering/Besicovitch.lean:239` and `:278` choose by
  `Classical.epsilon` and return garbage once no point is left.  `haar.index` and `haar.chaar` in
  `Mathlib/MeasureTheory/Measure/Haar/Basic.lean:94` and `:351` are the covering number, which is
  `0` when no finite family covers, and an arbitrary element of an intersection of closures that can
  differ from the Haar measure of the compact set.  `toSphereBallBound` in
  `Mathlib/MeasureTheory/Constructions/HaarToSphere.lean:203` is `1` outside `n ≠ 0 ∧ 0 < ε`, which
  makes `toSphereBallBound_pos` unconditional.  Each is used only in its own file.  The public
  results are existence statements (`exist_disjoint_covering_families`, `ae_tendsto_rnDeriv`, the
  Haar measure and its uniqueness, the two `toSphere` bounds), so the devices could be private
  witnesses; `haarContent` and `haarMeasure` unfold to `chaar`, whose independence of the choice
  rests on Haar uniqueness.  Decide per device whether it becomes private, is replaced by an
  existence statement, or is kept as a documented object with its specifying property.

- [ ] **Restate theorems that hold only because two fallback values coincide.**
  Each statement below is unconditional because both sides are fallback values at the exceptional
  inputs; they are instances of the `deriv`, Bochner `integral`, and `tsum` fallbacks audited in the
  XL bucket.  `deriv_klFun`, `rightDeriv_klFun`, and `leftDeriv_klFun`
  (`Mathlib/InformationTheory/KullbackLeibler/KLFun.lean:99`, `:119`, `:128`; all `@[simp]`) equate
  the derivatives of `klFun` with `log x` also at `x = 0`, where `klFun` is not differentiable, so
  the left side is the default `0`, and `log 0 = 0`; `hasDerivAt_klFun` (line 89) needs `x ≠ 0`, and
  no other file uses the three lemmas.  The `integral_comp_smul` family
  (`Mathlib/MeasureTheory/Measure/Haar/NormedSpace.lean:93`, `:116`, `:123`, `:130`) holds for every
  `f` and `R`: for `R ≠ 0` the Bochner zero of a nonintegrable `f` is transported through the
  equivalence `x ↦ R • x`, and at `R = 0` in positive dimension both sides vanish because `0⁻¹ = 0`
  and `ENNReal.toReal ∞ = 0` on the infinite Haar measure; `setIntegral_comp_smul` (line 134)
  requires `R ≠ 0`, and the one consumer is
  `Mathlib/Analysis/Calculus/BumpFunction/FiniteDimension.lean:306`.  `integral_sum_dirac`
  (`Mathlib/MeasureTheory/Integral/Bochner/SumMeasure.lean:149`) equates the integral against a sum
  of weighted Dirac masses with the `tsum` of the weighted values for every `f`, through the zero of
  the Bochner integral and the zero of `tsum` on nonsummable families, and `integral_poissonMeasure`
  and `integral_map_cast_poissonMeasure`
  (`Mathlib/Probability/Distributions/Poisson/Basic.lean:123`, `:129`) and
  `integral_geometricMeasure` (`Mathlib/Probability/Distributions/Geometric.lean:135`) repeat it;
  their docstrings say that the integral and the sum are 'both defined to be zero' otherwise.  The
  strict forms are `integral_sum_dirac_eq_tsum` (line 168), `integral_poissonMeasure'`,
  `integral_map_cast_poissonMeasure'`, and `integral_geometricMeasure'`, which take summability or
  integrability. For each unconditional statement, check whether the defining properties of the
  operations determine both sides on the exceptional inputs and imply the equality there. Where
  the equality depends on coinciding fallbacks, migrate consumers to statements of the actual
  domain and remove the unconditional form. Check `charFun_map_cast_poissonMeasure`
  (`Poisson/Basic.lean:142`) and the corollaries inside `Poisson/Basic.lean` and `Geometric.lean`.

- [ ] **Decide the domain of `Matrix.ToLieAlgebra`.**
  `Matrix.ToLieAlgebra R CM` in `Mathlib/Algebra/Lie/SerreConstruction.lean:145` is the quotient of
  the free Lie algebra by the Serre relations of an arbitrary integer matrix, and its docstring says
  that its value for non-Cartan matrices should be regarded as junk.  The construction presents a
  Lie algebra for every matrix, so the question is the intended object: the Serre presentation of
  any integer matrix, which needs a name and a docstring that say so, or the algebra attached to a
  Cartan or generalized Cartan matrix, which needs evidence as an argument.  The consumers are the
  abbreviations `LieAlgebra.e₆`, `e₇`, `e₈`, `f₄`, and `g₂` and the classical series
  `CartanMatrix.aₙ`, `bₙ`, `cₙ`, and `dₙ` in the same file; no other file uses it.

- [ ] **Classify the ratio of a dilation with no pair at positive finite distance.**
  `Dilation.ratio f` in `Mathlib/Topology/MetricSpace/Dilation.lean:135` is the `r` with
  `edist (f x) (f y) = r * edist x y` when some pair of points is at nonzero finite distance, where
  `r` is unique (`ratio_unique`), and `1` when every distance is `0` or `⊤` (`ratio_of_trivial`,
  `ratio_of_subsingleton`), where every positive `r` satisfies the identity and the docstring says
  that 'we choose one'.  Besides making `ratio` total, the value `1` is what makes
  `Dilation.ratioHom` (line 357) and `DilationEquiv.ratioHom` monoid homomorphisms.  The consumers
  are `Mathlib/Topology/MetricSpace/DilationEquiv.lean`, `Congruence.lean`, `Similarity.lean`, and
  `Mathlib/Analysis/Normed/Affine/AddTorsor.lean`. A total ratio on these spaces requires an
  independent specification that singles out its value. Otherwise expose `HasRatio f r` or
  restrict the ratio to spaces with a pair at positive finite distance, and restate `ratioHom`
  on the resulting domain.

- [ ] **Classify the junk values of `simplicialEvalσ`.**
  `simplicialEvalσ L` in
  `Mathlib/AlgebraicTopology/SimplexCategory/GeneratorsRelations/NormalForms.lean:218` is the
  `ℕ`-valued lift of the order map of a composite of degeneracies; its docstring says that it is
  correct only for an admissible list `L` and in-bounds arguments, and that other values 'are junk
  values'.  `simplicialEvalσ_of_isAdmissible` (line 235) proves the correct values on the valid
  domain, and the definition has no use outside the file.  This is probably an internal
  computational lift of the kind screened out by the fidelity audit. Decide whether
  to keep it as an internal helper, private or documented only on the admissible domain, or to
  record the exclusion.

- [ ] **Classify the large-`ε` values of `triangleRemovalBound`.**
  `SimpleGraph.triangleRemovalBound ε` in
  `Mathlib/Combinatorics/SimpleGraph/Triangle/Removal.lean:41` is an explicit constant meant for
  `0 < ε ≤ 1`; its docstring calls its values for `ε ≥ 1` junk, chosen positive so that
  `triangleRemovalBound_pos` holds for every `ε > 0`, and the `positivity` extension at line 178
  exploits this.  `triangleRemovalBound_le` (line 59) states the `ε ≤ 1` hypothesis it needs, while
  `FarFromTriangleFree.le_card_cliqueFinset` (line 137) and `triangle_removal` (line 161) are stated
  for every `ε`.  `cornersTheoremBound` in `Mathlib/Combinatorics/Additive/Corner/Roth.lean:74` is
  the only consumer outside the file.  Decide whether the value for `ε ≥ 1` is a legitimate explicit
  constant for those statements, which would be recorded by a proof that they hold there, or whether
  `ε` should be bounded in the definition.

- [ ] **Classify the zero value of generator-valued invariants.**
  `Monoid.exponent G` and `AddMonoid.exponent G` in `Mathlib/GroupTheory/Exponent.lean:74` are the
  least positive `n` with `g ^ n = 1` for all `g`, and `0` 'by convention' when there is none
  (`exponent_eq_zero_iff`, line 125).  `annIdealGenerator 𝕜 a` in
  `Mathlib/LinearAlgebra/AnnihilatingPolynomial.lean:78` is the monic generator of the annihilating
  ideal of `a` and `0` when that ideal is zero (`annIdealGenerator_eq_zero_iff`).
  `RingOfIntegers.exponent θ` in `Mathlib/NumberTheory/NumberField/Ideal/KummerDedekind.lean:65` is
  the `absNorm` of the contraction to `ℤ` of the conductor of `ℤ[θ]`, its nonnegative generator, and
  `0` when the contraction is zero, in which case every prime divides it, so the hypothesis
  `¬ p ∣ exponent θ` of `not_dvd_exponent_iff` and `ZModXQuotSpanEquivQuotSpan` excludes `θ`.  Each
  may be a genuine total invariant, the normalized generator of an ideal of `ℤ` or `𝕜[X]`, uniquely
  determined in every case including the zero ideal.  Record the specifying property and a source
  for each, as the fidelity gate requires, or restate it on the domain where the ideal is nonzero.
  `Monoid.exponent` has about twenty consumer files in `GroupTheory/`, `RingTheory/RootsOfUnity/`,
  and `NumberTheory/`; `annIdealGenerator` has none outside its file, and `RingOfIntegers.exponent`
  only that file's theorems.

- [ ] **Replace `FractionalIdeal.divMod` by the existence statement it chooses from.**
  `FractionalIdeal.divMod c b a` in `Mathlib/RingTheory/DedekindDomain/Factorization.lean:705`
  chooses an `x` with `a + spanSingleton x * b = c` when `a ≤ c`, `a ≠ 0`, and `b ≠ 0`, and is `0`
  otherwise (`divMod_zero_left`, `divMod_zero_right`, `zero_divMod`, and `divMod_zero_of_not_le`,
  lines 718 to 730); the docstring says 'an arbitrary `x`'.  Such an `x` is not unique in general,
  and the existence is already the public lemma `IsDedekindDomain.exists_add_spanSingleton_mul_eq`
  (line 670).  The only consumer is `FractionalIdeal.quotientEquiv` in the same file (line 738),
  through `divMod_spec`.  Decide whether to restate `quotientEquiv` with an obtained witness, or to
  give `divMod` the three hypotheses as arguments.

- [ ] **Require positive order in `HahnSeries.SummableFamily.powers`.**
  `powers x` in `Mathlib/RingTheory/HahnSeries/Summable.lean:720` is the family `n ↦ x ^ n` when
  `0 < x.orderTop` and the family of powers of `0` otherwise, which its docstring calls a junk value
  given by pretending `x = 0` (`powers_of_not_orderTop_pos`, line 740; `powers_of_orderTop_pos`,
  line 736).  The hypothesis `0 < x.orderTop` is sufficient for the powers to be summable but is not
  shown to be necessary: over a ring with nilpotents, such as `ℤ/4`, the constant `2` has
  `orderTop 0` and a finite family of powers (paper argument), so the exact domain is the
  summability of the powers.  The junk reaches `powerSeriesFamily`
  (`Mathlib/RingTheory/HahnSeries/HEval.lean:51`) and `PowerSeries.heval x` (line 167), which is an
  algebra homomorphism for every `x` and equals `f ↦ f.constantCoeff • 1` when `x` has nonpositive
  order (`powerSeriesFamily_of_not_orderTop_pos`, line 54), whereas `heval_X` (line 199) needs
  positive order and the docstring of `heval` speaks of a positive order element `x`.
  `Mathlib/RingTheory/HahnSeries/Cardinal.lean` is the other consumer.  Decide whether `powers` and
  `heval` take summability, or the positive order that implies it, as an argument.

## M -- subsystem audit candidates

- [ ] **Give covariant derivatives their domain of differentiable sections.**
  `IsCovariantDerivativeOn` in
  `Mathlib/Geometry/Manifold/VectorBundle/CovariantDerivative/Basic.lean:92` constrains a function
  on all sections only at sections that are differentiable at the point, and the bundled
  `CovariantDerivative` (line 366) stores that total function, so its extensionality compares values
  at sections that are not differentiable.  `leviCivitaAux` in
  `Mathlib/Geometry/Manifold/VectorBundle/CovariantDerivative/LeviCivita.lean:326` is `0` unless `Y`
  is `MDiffAt` at `x`; its strict core `leviCivitaAuxOfMDiffAt` (line 309) takes the
  differentiability proof, and the module overview records that `leviCivitaConnection` is unique
  only up to its value on nondifferentiable fields.  The four files of the directory (`Basic`,
  `Metric`, `Torsion`, `LeviCivita`) are the only consumers.  Decide whether a covariant derivative
  is a function on differentiable sections, a germ-level or tensorial object, or the current total
  function with a documented equivalence, and keep the zero branch out of the public interface of
  the Levi-Civita connection.

- [ ] **Give the covariance operators of a measure their second-moment domain.**
  `StrongDual.toLpₗ` and `StrongDual.toLp`
  (`Mathlib/Probability/Moments/CovarianceBilinDual.lean:59`, `:134`),
  `uncenteredCovarianceBilinDual` and `covarianceBilinDual` (`:170`, `:230`), `covarianceBilin`
  (`Mathlib/Probability/Moments/CovarianceBilin.lean:50`), and `covarianceOperator` (`:203`) are
  defined for every measure and are `0` unless `MemLp id p μ` holds (`toLpₗ`, `toLp`) or
  `MemLp id 2 μ` holds (the covariance forms).  The zero lemmas are `toLpₗ_of_not_memLp`,
  `toLp_of_not_memLp`, `uncenteredCovarianceBilinDual_of_not_memLp`, and
  `covarianceBilinDual_of_not_memLp'` and `covarianceBilinDual_of_not_memLp` (lines 73, 153, 184,
  283, and 291 of `CovarianceBilinDual.lean`), `covarianceBilin_of_not_memLp` (line 63 of
  `CovarianceBilin.lean`), and `covarianceOperator_of_not_memLp` (line 212).  The centered forms
  subtract the totalized mean `∫ x, x ∂μ`, which is `0` when `id` is not integrable, and
  `memLp_id_of_self_sub_integral` (line 234) identifies the centered and uncentered conditions
  through that convention, as a comment in its proof says.  The consumers are
  `Mathlib/Probability/Distributions/Gaussian/CharFun.lean`, `Gaussian/Multivariate.lean`,
  `Gaussian/HasGaussianLaw/Independence.lean`, `Mathlib/Probability/BrownianMotion/Basic.lean`, and
  `FidelityTest/Probability/MultivariateGaussianStrict.lean`, which supply `IsGaussian.memLp_two_id` or an
  equivalent.  Decide whether the covariance takes `MemLp id 2 μ` as an argument or class, how the
  mean enters the centered form without the totalized integral, and whether `StrongDual.toLp` is
  stated only on measures with `MemLp id p μ`.

- [ ] **Give the completion scalar action and algebraic structures their exact domains.**
  The scalar action on `UniformSpace.Completion X`
  in `Mathlib/Topology/Algebra/UniformMulAction.lean` is an instance for
  `[UniformContinuousConstSMul M X]`. By
  `Completion.cauchyContinuous_iff_exists_continuous_extension`, `c • ·` extends continuously
  exactly when it is Cauchy continuous. The `AddMonoid`,
  `SubNegMonoid`, `AddGroup`, and `AddCommGroup` instances on the completion in
  `Mathlib/Topology/Algebra/GroupCompletion.lean` keep `[IsUniformAddGroup α]`, and
  `UniformSpace.Completion.ring` in `Mathlib/Topology/Algebra/UniformRing.lean` and the field
  structure built on it keep their hypotheses.  The axioms are closed conditions in continuous
  operations on a separated space, so they plausibly hold under Cauchy continuity of the operations
  alone; this is not verified in Lean.  `IsUniformAddGroup (Completion α)` needs uniform continuity,
  and the `nsmul` and `zsmul` fields, which come from the scalar actions of `ℕ` and `ℤ` and so from
  `UniformContinuousConstSMul`, need a decision.  The completion of a multiplicative uniform group
  has a multiplication but no `One`, `Inv`, `Div`, or group structure, since
  `Mathlib/Topology/Algebra/GroupCompletion.lean` builds only the additive structure, so
  `CauchyContinuousInv` and `CauchyContinuousDiv` have no consumer yet; the multiplicative
  counterpart of that structure is not built.  Finally, the four operation instances spell out
  `IsDenseInducing.extend` and carry `@[nolint unusedArguments]`, since only the theorems about
  them use their class argument; a named extension of a Cauchy continuous map, parallel to
  `Completion.extension`, would take the evidence as an argument and remove both.

- [ ] **Require measurability in `VectorMeasure.map` and `VectorMeasure.restrict`.**
  `VectorMeasure.map v f` in `Mathlib/MeasureTheory/VectorMeasure/Operations.lean:187` is `0` unless
  `f` is measurable (`map_not_measurable`, line 199), and `VectorMeasure.restrict v i` (line 295) is
  `0` unless `i` is measurable (`restrict_not_measurable`, line 309).  A vector measure is
  determined by its values on measurable sets and is `0` on the rest by its structure, so unlike
  `Measure.restrict` there is no outer measure to supply a value, and the exact domains are
  `Measurable f` and `MeasurableSet i`.  The fallback reaches the order `v ≤[i] w` of
  `Mathlib/MeasureTheory/VectorMeasure/Order.lean`, which is notation for
  `v.restrict i ≤ w.restrict i` and therefore holds for every nonmeasurable `i`
  (`zero_le_restrict_not_measurable` and `restrict_le_zero_of_not_measurable`, lines 194 and 197),
  so that `measurable_of_not_zero_le_restrict` (line 200) and
  `exists_pos_measure_of_not_restrict_le_zero` (line 221) must recover measurability from the
  failure of the relation.  The consumers of `restrict` are about ten files under
  `Mathlib/MeasureTheory/VectorMeasure/`: the order, integral, set-integral, variation,
  `WithDensityVec`, Hahn, and Jordan files; `map` is used in `Integral.lean`,
  `Variation/Basic.lean`, and `Relations.lean`.  Decide whether both operations take the proof as an
  argument, with a `fun_prop` discharger as for `Measure.map`, and whether `v ≤[i] w` is stated for
  measurable `i` only.

- [ ] **Determine the radius-zero domain of the value-distribution functions.**
  `ValueDistribution.proximity`, `logCounting`, and `characteristic` in
  `Mathlib/Analysis/Complex/ValueDistribution/` use signed real radii. At negative radii the values
  agree with those at `|r|` by `proximity_even`, `logCounting_even`, and `characteristic_even`.
  The current `proximity` and `characteristic` require `r = 0 → (f 0 : WithTop E) ≠ a`.
  `logCounting_eval_zero` still gives `0` at radius zero. A single nonzero central atom contributes
  a nonzero multiple of `log r` at positive radii, so its counting function has no finite limit as
  `r` tends to zero from above. Determine when the counting specification gives a finite value at
  zero and expose that domain. Migrate the zero-radius consumers, including
  `characteristic_sub_characteristic_zero_at_zero` in `FirstMainTheorem.lean`, which already
  requires `f 0 ≠ 0`.
  Separately, `continuous_proximity_top` takes a continuous meromorphic function, that is, an entire
  function; the proximity function for the poles of every meromorphic function is plausibly
  continuous on `r ≠ 0`, by dominated convergence at the logarithmic singularities of the integrand,
  but this is not proved.

- [ ] **Give `covolume` its domain and independence hypotheses.**
  `covolume G α ν` and `addCovolume` in `Mathlib/MeasureTheory/Group/FundamentalDomain.lean:685` are
  `ν s` for a fundamental domain `s` chosen by `Classical.choose` when `HasFundamentalDomain G α ν`
  holds and `0` otherwise (the docstring: 'or `0` if none exists').  Independence of the chosen
  domain is proved under further hypotheses, those of `IsFundamentalDomain.covolume_eq_volume` (line
  701): `[Countable G] [MeasurableConstSMul G α] [SMulInvariantMeasure G α ν]`; no independence
  statement is recorded for other actions.  `ZLattice.covolume`
  (`Mathlib/Algebra/Module/ZLattice/Covolume.lean:72`) composes `addCovolume` with `ENNReal.toReal`,
  so an infinite covolume also becomes `0`.  The Haar quotient theory uses `covolume Γ.op G ν`
  (`Mathlib/MeasureTheory/Measure/Haar/Quotient.lean`, lines 190 and 231),
  `Mathlib/MeasureTheory/Integral/IntervalIntegral/Periodic.lean:85` uses `covolume_eq_volume`, and
  the regulator, discriminant, and ideal-counting files of `NumberTheory/NumberField/` reach it
  through `ZLattice.covolume`.  Decide whether the covolume is an extended invariant defined through
  the quotient measure, or takes a fundamental domain and the independence hypotheses as arguments,
  and what `ZLattice.covolume` becomes for a lattice, where finiteness is a theorem.

- [ ] **Decide the off-domain values of additive contents and their construction helpers.**
  `AddContent G C` in `Mathlib/MeasureTheory/Measure/AddContent.lean:76` stores a function on every
  `Set α` that is additive only on `C`, and `AddContent.ext` (line 99) compares all sets, so two
  contents that agree on `C` are different.  Its constructors assign the values outside `C` by
  branches.  `AddContent.onIocAux f` (line 370, behind `AddContent.onIoc`, line 394) is `f v - f u`
  for a chosen `(u, v)` with `u ≤ v` and `s = Ioc u v`, and `0` for every other set.  The private
  `AddContent.supClosureFun` (line 222, the function of `AddContent.supClosure`) is the sum of `m`
  over a chosen finite disjoint decomposition into members of `C`, and `0` for other sets.
  `projectiveFamilyFun P` (`Mathlib/MeasureTheory/Constructions/ProjectiveFamilyContent.lean:71`) is
  `P I S` for the chosen cylinder representation `(I, S)` and `0` off the measurable cylinders; the
  representation comes from the exported `Classical.choose` projections `measurableCylinders.finset`
  and `measurableCylinders.set` (`Mathlib/MeasureTheory/Constructions/Cylinders.lean:294`, `:300`),
  and the closed-compact analogues
  (`Mathlib/MeasureTheory/Constructions/ClosedCompactCylinders.lean:53`, `:60`) have no use outside
  their file.  The values on the domain are shown independent of the choice under hypotheses
  (`sum_addContent_eq_of_sUnion_eq` for a semiring, line 189; `projectiveFamilyFun_congr` for an
  `IsProjectiveMeasureFamily`, line 76).  Carathéodory's construction already treats values off `C`
  explicitly (`AddContent.extend`, line 465, and the hypothesis `m_top` of `ofFunction_eq`).  The
  consumers are `Mathlib/MeasureTheory/OuterMeasure/OfAddContent.lean`,
  `Mathlib/MeasureTheory/VectorMeasure/AddContent.lean`, `VectorMeasure/BoundedVariation.lean`,
  `Mathlib/Probability/Kernel/IonescuTulcea/Traj.lean`, and
  `Mathlib/Probability/ProductMeasure.lean`.  For a generic interface that needs a total set
  function, `FORK_DESIGN.md` asks that each branch stay anonymous at its construction site with a
  proof of independence, and that `TODO.md` record the interface change that would remove it.
  Decide whether that change is a content defined on the subtype `C`, and whether the chosen
  cylinder representations become private witnesses.

- [ ] **Replace the chosen limit process of a filtered process by its class.**
  `Filtration.limitProcess f ℱ μ` in `Mathlib/Probability/Process/Filtration.lean:459` is a
  `Classical.choose` of a `⨆ n, ℱ n`-strongly measurable `g` to which `f n` converges `μ`-almost
  everywhere, and `0` when there is none.  For a Hausdorff target two such `g` agree almost
  everywhere, so the specification determines an almost-everywhere class and the value is a chosen
  representative of it together with a no-witness fallback; the definition itself assumes only
  `[Zero E] [TopologicalSpace E]`.  The consumers are
  `Mathlib/Probability/Martingale/Convergence.lean` (`Submartingale.ae_tendsto_limitProcess`,
  `memLp_limitProcess`, `tendsto_eLpNorm_one_limitProcess`,
  `ae_tendsto_limitProcess_of_uniformIntegrable`, `Martingale.isCondExp_limitProcess`, and the proof
  of `Integrable.tendsto_ae_condExp`) and `Mathlib/Probability/Kernel/Disintegration/Density.lean`
  (`density_ae_eq_limitProcess` and the `densityProcess` convergence lemmas); the proof of
  `ae_tendsto_limitProcess` splits on the `dite`.  Decide whether the limit is the class of its
  versions, with the convergence theorems stated for any version as for conditional kernels, or an
  existence statement, which is what the martingale convergence theorem asserts, and whether the
  target needs a `T2Space` hypothesis for the uniqueness.

- [ ] **Give `stoppedValue` its finite stopping times.**
  `stoppedValue u τ` in `Mathlib/Probability/Process/Stopping.lean:818` is
  `fun ω ↦ u (τ ω).untopA ω` for a stopping time `τ : Ω → WithTop ι`, where `WithTop.untopA`
  (`Mathlib/Order/WithBot.lean:270`) is `untopD (Classical.arbitrary ι)`, so on `{τ = ⊤}` the value
  is `u (Classical.arbitrary ι) ω`, an arbitrary index.  `stoppedValue_stoppedProcess` (line 893)
  states the branch with `Classical.arbitrary ι`, whereas `stoppedValue_stoppedProcess_apply` and
  `stoppedValue_stoppedProcess_ae_eq` (lines 901 and 905) assume `σ ω ≠ ⊤` pointwise or almost
  everywhere.  `stoppedProcess` (line 854) is not affected at a finite index, because `min i (τ ω)`
  is never `⊤`.  The consumers of `stoppedValue` are `Mathlib/Probability/Martingale/Basic.lean`,
  `OptionalSampling.lean`, `OptionalStopping.lean`, `Upcrossing.lean`, and
  `Mathlib/Probability/Process/HittingTime.lean`; `untopA` is also used in `HittingTime.lean`,
  `Martingale/BorelCantelli.lean`, `Mathlib/Topology/Order/WithTop.lean`, and
  `Mathlib/MeasureTheory/Constructions/BorelSpace/WithTop.lean`.  Decide whether the stopped value
  is defined on `{τ < ⊤}`, as a dependent function or through a stopping time with finiteness
  evidence, whether `{τ = ⊤}` is handled by a separately specified limit value (compare the
  limit-process item above), and which theorems then need `τ ≠ ⊤` almost everywhere.

## L -- cross-module audit candidates

- [ ] **Put matroid closure on subsets of the ground set.**
  `Matroid.closure` in `Mathlib/Combinatorics/Matroid/Closure.lean:135` deliberately extends closure
  to every `Set α` by replacing `X` with `X ∩ M.E`; the module describes off-ground inputs as junk,
  and the resulting operation is not extensive on all `Set α`.  Reuse `Matroid.subtypeClosure` at
  line 116 to make the ordinary closure domain-bearing, or prototype an equally faithful proof-last
  interface. Remove the off-ground fallback unless literature establishes it as an independent
  closure operation. The current surface has roughly 258 `M.closure` matching lines across
  nine maintained files, so migrate the closure theorem family and its rank, minor, circuit, and loop
  consumers in the same complete migration.

- [ ] **Require integrality for `minpoly`.**
  `Mathlib/FieldTheory/Minpoly/Basic.lean:41` assigns polynomial zero to a nonintegral element;
  `minpoly.aeval` at line 89 then states unconditionally that every element is a root of its minimal
  polynomial. Put `IsIntegral` in the ordinary construction and theorem family, migrate its
  consumers, and remove the nonintegral zero branch without a private compatibility bridge.

- [ ] **Replace finite separable/inseparable degree projections outside their domains.**
  `Field.finSepDegree` in `Mathlib/FieldTheory/SeparableDegree.lean:141` uses `Nat.card` even for a
  nonalgebraic extension, and `Field.finInsepDegree` in
  `Mathlib/FieldTheory/SeparableClosure.lean:281` inherits `finrank`'s infinite-to-zero behavior.
  Require the correct algebraicity/finite-degree evidence or expose cardinal-valued invariants.

- [ ] **Make rational-function evaluation reject poles.**
  `RatFunc.eval` in `Mathlib/FieldTheory/RatFunc/AsPolynomial.lean:143` evaluates a pole to zero and
  consequently fails ring laws there.  Require regularity/denominator nonzeroness at the point, while
  respecting reduced-rational-function rather than source-expression semantics.

- [ ] **Give `Polynomial.cyclotomic` the domain `n ≠ 0`.**
  `Polynomial.cyclotomic 0 R` is `1` by an explicit case of the definition in
  `Mathlib/RingTheory/Polynomial/Cyclotomic/Basic.lean` (`cyclotomic_zero`).  The defining relations
  do not determine it: `X ^ 0 - 1 = 0`, while the product over `Nat.divisors 0 = ∅` is `1`, and the
  roots of `1` are not the primitive `0`-th roots of unity.  The polynomial is used in 28 files,
  where lemmas such as `cyclotomic.monic` and `degree_cyclotomic` hold at `0` only through this
  value. Give it `[NeZero n]` and restate those families, as for `cyclotomic'`. Any separate
  construction at `n = 0` needs defining properties that determine its polynomial there.

- [ ] **Put finite factorization data on nonzero inputs.**
  `Nat.factorization` in `Mathlib/Data/Nat/Factorization/Defs.lean:50` gives zero multiplicities at
  zero, and `Nat.primeFactors` in `Mathlib/Data/Nat/PrimeFin.lean:37` gives the empty set although
  every prime divides zero.  The generic `factorization` and `normalizedFactors` in
  `Mathlib/RingTheory/UniqueFactorizationDomain/Finsupp.lean:32` and
  `Mathlib/RingTheory/UniqueFactorizationDomain/NormalizedFactors.lean:35` likewise return empty
  data at zero.  Use a nonzero carrier or explicit failure for finite lists/counts; keep units
  admissible with empty factorization. `Associates.factors` returns `⊤` at zero
  (`Mathlib/RingTheory/UniqueFactorizationDomain/FactorSet.lean:223`). For a public extended
  factorization, derive the value at zero from its defining properties. `Nat.ordProj` and
  `Nat.ordCompl` in `Mathlib/Data/Nat/Factorization/Defs.lean` inherit the finite fallback, with
  `ordProj 0 p = 1` and `ordCompl 0 p = 0`; their lemmas without a nonzero hypothesis, such as
  `Nat.ordProj_pos` and `Nat.factorization_ordCompl`, hold at `0` through it and move with this
  migration.

- [ ] **Migrate natural cardinalities away from infinity-to-zero.**
  `Nat.card` in `Mathlib/SetTheory/Cardinal/Finite.lean:41` and `Set.ncard` in
  `Mathlib/Data/Set/Card.lean:613` return zero on infinite inputs.  Require `Finite α`/`s.Finite` for
  natural values and use `ENat.card`/`Set.encard` globally.

- [ ] **Make lossy extended-value conversions checked and remove their zero fallbacks.**
  `ENat.toNat` (`Mathlib/Data/ENat/Basic.lean:118`), `Cardinal.toNat`
  (`Mathlib/SetTheory/Cardinal/ToNat.lean:31`), and `ENNReal.toNNReal`/`toReal`
  (`Mathlib/Basic/ENNReal/Basic.lean:225`) send infinity to zero.  Provide proof-bearing finite
  conversions and remove the replaced infinity-to-zero maps; a more explicit public name does not
  prevent their accidental use as genuine conversions.
  `Measure.real` (`Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean:102`) is `(μ s).toReal`, and
  its docstring says that it maps infinite measure sets to zero; the projection `μ.real s` occurs in
  over a hundred files, so the finite-measure and finite-set cases (`IsFiniteMeasure`, `μ s ≠ ∞`)
  must be expressed in the conversion and its consumers in the same migration.

- [ ] **Separate chosen preimages from true inverses and true extensions.**
  `Function.invFun` in `Mathlib/Logic/Function/Basic.lean:526` picks an arbitrary element outside
  the range and a chosen preimage for noninjective maps.  Use equivalences/bijections for inverse
  functions.  A chosen-preimage construction may remain public only as a separately sourced
  mathematical choice operator, not as an inverse fallback.
  `Function.extend` in the same file at line 835 explicitly takes an outside-range fallback, but
  explicitness alone does not make it a faithful extension.  Without `g.FactorsThrough f` it chooses
  one representative's `g`-value for a fiber and cannot agree with every original `g`-value on that
  fiber.  Require `FactorsThrough` for
  the ordinary extension name. Remove the unrestricted chosen-representative construction unless
  literature establishes that choice operation as an independent mathematical object; private
  witnesses used only in existence proofs remain legitimate.
  `MeasurableEmbedding.invFun` (`Mathlib/MeasureTheory/SigmaAlgebra/Embedding.lean:793`) is a
  measurable left inverse of a measurable embedding: it inverts `equivRange` on the range and takes
  `Nonempty.some` off it.  Its one consumer, `exists_measurable_map_eq_unitInterval` in
  `Mathlib/Probability/Kernel/Representation.lean` (line 114), needs only a measurable left inverse
  of `sigmoid ∘ embeddingReal Y`, so an existence statement for measurable embeddings of nonempty
  types would replace the exported choice; `embeddingReal`
  (`Mathlib/MeasureTheory/Constructions/Polish/EmbeddingReal.lean:58`) is itself a
  `Classical.choose` projection with the same question.

  `LinearIndependent.repr` in `Mathlib/LinearAlgebra/LinearIndependent/Defs.lean` is a positive
  control. Linear independence and span membership certify that the inverse of the linear
  equivalence specifies a unique value. For actual-domain consumers, preserve the agreement
  proofs used by `integral_unitInterval_deriv_eq_sub`, `integral_subtype_uIcc_eq_sub_of_hasDerivAt`,
  and `Convex.norm_image_sub_le_of_norm_hasDerivWithin_le` when they extend functions to enter
  ambient theorems. Audit the ambient functions required by `OpenPartialHomeomorph` as well,
  including the principal-interval tangent and `univUnitBall.invFun`, whose inverse formula is used
  on the target open unit ball.

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
  The primed predecessors remain beside them: `Ideal.ramificationIdx'`
  (`Mathlib/NumberTheory/RamificationInertia/Ramification.lean:71`) is `sSup {n | map f p ≤ P ^ n}`
  and is `0` when that set is unbounded, and `Ideal.inertiaDeg'`
  (`Mathlib/NumberTheory/RamificationInertia/Inertia.lean:69`, deprecated since 2026-08-14) is
  `finrank (R ⧸ p) (S ⧸ P)` when `comap f P = p` and `0` otherwise, so it carries the
  infinite-to-zero `finrank` convention in addition to its off-domain zero.  Retire them with their
  replacements instead of migrating their lemmas.

- [ ] **Put affine combinations on affine weights.**
  `Finset.affineCombination` in `Mathlib/LinearAlgebra/AffineSpace/Combination.lean:348` accepts
  arbitrary weights and chooses a base point; only weights summing to one give the intrinsic affine
  combination.  Use the affine-weight hyperplane or a sum-one proof.  A basepoint-dependent operation
  is public only if independently supported as a mathematical construction, not merely because it
  can be given a descriptive name.

- [ ] **Specify regularity for Lie-bracket evaluation.**
  `lieBracketWithin` and `lieBracket` in `Mathlib/Analysis/Calculus/VectorField.lean` and
  `mlieBracketWithin` and `mlieBracket` in `Mathlib/Geometry/Manifold/VectorField/LieBracket.lean`
  use the derivative projections to define their values on ambient fields. Determine the precise
  derivative data needed in the two field directions and carry it in the bracket evaluation.
  Transport that contract through chart changes, bracket algebra, and the regularity and Jacobi
  theorems. The related-field naturality theorems already have explicit differentiability
  hypotheses.

- [ ] **Audit and strictify local-frame/trivialization evaluation at its public boundary.**
  `IsLocalFrameOn.coeff` in `Mathlib/Geometry/Manifold/VectorBundle/LocalFrame.lean:186` returns
  zero outside the frame's set; pretrivializations/trivializations in
  `Mathlib/Topology/FiberBundle/Trivialization.lean:69` also expose chosen ambient values, and
  `Pretrivialization.symm` and `Trivialization.symm` in the same file take an arbitrarily chosen
  value outside the base set.  In `Mathlib/Topology/VectorBundle/Basic.lean` the fiberwise maps
  `Pretrivialization.linearMapAt` and `Pretrivialization.symmₗ`, `Trivialization.linearMapAt`,
  `Trivialization.symmₗ`, `Trivialization.continuousLinearMapAt`, and `Trivialization.symmL` are
  zero outside the base set; `ContinuousLinearMap.inCoordinates` in the same file and
  `ContinuousAlternatingMap.inCoordinates` in
  `Mathlib/Topology/VectorBundle/ContinuousAlternatingMap.lean` are built from them for points in
  different base sets.  Consumers such as `Bundle.Trivialization.contMDiffAt_symmL` in
  `Mathlib/Geometry/Manifold/VectorBundle/Hom.lean` state properties of these total maps.  Require
  base-set membership for ordinary coordinate/evaluation names.  Keep globally defined
  implementation representatives private and only behind proofs that their off-domain values cannot
  affect public results.

- [ ] **Audit the total coordinate-change surface of bundle cores and the tangent bundle.**
  `FiberBundleCore.coordChange` in `Mathlib/Topology/FiberBundle/Basic.lean` and
  `VectorBundleCore.coordChange` in `Mathlib/Topology/VectorBundle/Basic.lean` are total fields
  `ι → ι → B → …` whose laws hold on `baseSet i ∩ baseSet j`; the core documents them as encodings
  of maps on the overlap, and the evaluation formulas
  `FiberBundleCore.localTrivAsPartialEquiv_apply`, `FiberBundleCore.localTrivAt_snd`,
  `FiberBundleCore.localTriv_apply`, `FiberBundleCore.localTriv_symm_apply`,
  `VectorBundleCore.localTriv_apply`, and `VectorBundleCore.localTriv_symm_fst` state the
  unconditional formula, including values outside the source.  `tangentCoordChange` in
  `Mathlib/Geometry/Manifold/VectorBundle/Tangent.lean` is a public, named coordinate change defined
  as `(tangentBundleCore I M).coordChange` whose docstring says that it takes junk values outside
  the intersection of the chart sources; it is used in
  `Mathlib/Geometry/Manifold/MFDeriv/Tangent.lean` and the integral curve files.  Decide between a
  dependent field `∀ b ∈ baseSet i ∩ baseSet j, F →L[R] F` with a documented construction contract
  and a strict exported operation on the overlap, give `tangentCoordChange` the overlap evidence,
  and remove the selected coordinate API's total fallback. If a separate bundle foundation still
  requires total representatives, record that dependency precisely and prove independence from
  off-domain values under the foundational dependency rule.

- [ ] **Audit the choice-based `Filter.lim` projection and its theorem boundaries.**
  `Filter.lim` and `Filter.limUnder` in `Mathlib/Topology/Defs/Filter.lean:255` and `:260` use
  `Classical.epsilon` and choose a point satisfying the limit relation when one exists.  This is a
  choice projection, not by itself a false mathematical statement.  Inventory whether any public
  theorem omits convergence, separation, or nontrivial-filter hypotheses. A total object covering
  nonconvergent filters would require an independent mathematical specification of those values.
  Expose the canonical limit on its exact existence-and-uniqueness domain or use the limit relation.
  Remove the selected projection's fallback.
  Audit `IsDenseInducing.extend`/`extendFrom` under the same distinction between
  a chosen representative and a claimed canonical extension.
  Documented consumers of `limUnder` are `UpperHalfPlane.valueAtInfty`
  (`Mathlib/NumberTheory/ModularForms/QExpansion.lean:64`), whose docstring says 'an arbitrary
  choice of value if this limit is not well-defined', with `IsZeroAtImInfty.valueAtInfty_eq_zero`
  (line 66) as the existence-backed case and its modular-form consumers in `CuspFormSubmodule.lean`
  and `LFunction.lean`, and `Function.Periodic.cuspFunction`
  (`Mathlib/Analysis/Complex/Periodic.lean:119`), which is 'extended by a non-canonical choice of
  limit at 0' and underlies `UpperHalfPlane.cuspFunction` (`QExpansion.lean:79`) and `qExpansion`
  (line 162).

- [ ] **Give the measure pullback `Measure.comap` its exact domain.**
  `Measure.comapₗ` in `Mathlib/MeasureTheory/Measure/Comap.lean:44` is `0` unless `f` is injective
  and sends measurable sets to measurable sets, and `Measure.comap` at line 64 is `0` unless `f` is
  injective and sends measurable sets to `μ`-null-measurable sets (`comap_undef`, line 81);
  `FiniteMeasure.comap` in `Mathlib/MeasureTheory/Measure/FiniteMeasure.lean:857` inherits the
  fallback.  The module overview records that the zero value is a placeholder and that covering maps
  such as `ℝ → AddCircle 1` might later receive a meaningful pullback.  The intended object has
  `comap f μ s = μ (f '' s)` on measurable `s`; the stated conditions are sufficient for that set
  function to be countably additive, and no argument that they are necessary is recorded.  About two
  dozen files use the API by a textual count.  `Subtype.measureSpace`
  (`Mathlib/MeasureTheory/Measure/Restrict.lean:843`) takes
  `volume := Measure.comap Subtype.val volume`, which is the zero measure as soon as the subset is
  not null-measurable, and the volume of the unit interval
  (`Mathlib/MeasureTheory/Constructions/UnitInterval.lean:28`) and the invariant measure of `ℍ`
  (`Mathlib/Analysis/Complex/UpperHalfPlane/Measure.lean:45`) are built from pullbacks of ambient
  volumes.  `Measure.comap` and `MeasurableEmbedding.comap_apply` also serve `Kernel.comapRight`
  (`Mathlib/Probability/Kernel/Basic.lean`), `Mathlib/Probability/ConditionalProbability.lean`,
  `Mathlib/MeasureTheory/Measure/Regular.lean`,
  `Mathlib/MeasureTheory/Constructions/HaarToSphere.lean`,
  `Mathlib/Probability/Combinatorics/BinomialRandomGraph/Defs.lean`, and
  `Mathlib/Probability/Distributions/SetBernoulli.lean`.  Decide whether the ordinary operation
  takes injectivity and null-measurability of images as proof arguments supplied by a discharger, as
  `Measure.map` takes a.e. measurability, or is restricted to measurable embeddings with a separate
  null-measurable form; what `Subtype.measureSpace` becomes on subsets that are not null-measurable;
  whether a fiber-summing pullback for covering maps is a different operation; and how
  `FiniteMeasure.comap` and `comapₗ` follow.

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

- [ ] **Give `average` and `laverage` their exact domain.**
  `MeasureTheory.laverage` and `MeasureTheory.average` in
  `Mathlib/MeasureTheory/Integral/Average.lean:71` and `:279` are `∫⁻ x, f x ∂(μ univ)⁻¹ • μ` and
  `∫ x, f x ∂(μ univ)⁻¹ • μ`, with the notations `⨍⁻` and `⨍`.  The value is `0` for an infinite
  measure, because the scalar `(μ univ)⁻¹` is `0`, for the zero measure, and, for `average`, for a
  nonintegrable `f` or an incomplete target; the docstrings name the infinite-measure and
  nonintegrable cases.  The intended mean is `(μ.real univ)⁻¹ • ∫ f ∂μ` for a finite nonzero measure
  and an integrable `f`; for an infinite measure a limit of averages over exhausting sets is a
  different object. An independently defined extended mean needs a specification that determines
  its value at zero or infinite mass wherever either is in its domain. About forty files use the
  notation or the API by a textual count, among them `Mathlib/Analysis/Convex/Integral.lean`,
  `Mathlib/Analysis/Polynomial/MahlerMeasure.lean`,
  `Mathlib/MeasureTheory/Function/Intersectivity.lean`,
  `Mathlib/MeasureTheory/Integral/IntervalAverage.lean`,
  `Mathlib/MeasureTheory/Integral/CircleAverage.lean`, and
  `Mathlib/MeasureTheory/Covering/Differentiation.lean`. Determine the exact mass and integrability
  conditions of the ordinary mean and use the nonnegative integral specification for the
  `ℝ≥0∞`-valued `laverage`. Support routine cases such as probability measures and finite measures on
  intervals and circles. Propagate the resulting domains through the interval average and
  `circleAverage_eq_intervalAverage`.

- [ ] **Replace chosen almost-everywhere representatives elsewhere in measure theory by their
  classes.**
  `Measure.rnDeriv` in `Mathlib/MeasureTheory/Measure/Decomposition/Lebesgue.lean:80` chooses a
  representative from the Lebesgue decomposition, although it is determined only almost
  everywhere.  Audit it, its signed and vector-measure variants, and other public `Classical.choose`
  or `AEStronglyMeasurable.mk` representatives under the equivalence-class rule of
  `FORK_DESIGN.md`, coordinating with the Radon--Nikodym domain item below.  The conditional
  expectations `condExp` and `condLExp` already give the classes of their versions. `Kernel.density`
  is the `limsup` construction.

- [ ] **Construct conditional expectations on their whole domains.**
  `HasUniqueCondExp m μ f` in `Mathlib/MeasureTheory/Function/ConditionalExpectation/Basic.lean` is
  the exact domain of `condExp`, but its constructors cover only an integrable function with a
  version (`HasUniqueCondExp.of_isCondExp`) or with a σ-finite trim
  (`HasUniqueCondExp.of_integrable`).  `IsCondExp` also specifies the generalized conditional
  expectation of a function integrable on each set of a sequence in `m` exhausting the space, whose
  existence and uniqueness for a σ-finite `μ.trim hm` should follow by gluing versions on the sets
  of the sequence with `IsCondExp.restrict` and `IsCondExp.ae_eq`; record a primary source for that
  specification before relying on it.  The same extension decides `IsCondExp.memLp` and the `Lᵖ`
  bounds of `Real.lean` and `CondJensen.lean` for a function in `Lᵖ` but not in `L¹` on an infinite
  measure, where they fail without σ-finiteness (given `⊥` and an infinite measure, every constant
  is a version for a function in `L² \ L¹`), the conditional variance of
  `Mathlib/Probability/CondVar.lean` beyond `L¹ ∩ L²`, where `IsCondVar` holds for every constant
  given `⊥` for an `X` in `L¹` but not in `L²` and a faithful extension would take the Lebesgue
  conditional expectation `IsCondLExp` of the nonnegative `(X - g) ^ 2`, and the pull-out property
  of `PullOut.lean` with the global integrability of `g` replaced by integrability on the sets of
  `m`.  `HasUniqueCondExp.le_eventuallySigmaAlgebra` allows a sub-σ-algebra that is only
  null-measurable, but `IsCondExp.ae_eq` and the constructors take `m ≤ m₀`; extend them through the
  completion.  The constructors `HasUniqueCondLExp.of_sigmaFinite` and `of_aemeasurable` of
  `condLExp` in `Mathlib/MeasureTheory/Function/ConditionalLExpectation.lean` likewise need a
  σ-finite trim.

- [ ] **Remove σ-finiteness from countable additivity of conditional expectations.**
  `IsCondExp.tsum` in `Mathlib/MeasureTheory/Function/ConditionalExpectation/Basic.lean` and
  `IsCondExp.indicator_iUnion` in `Indicator.lean` take `[SigmaFinite (μ.trim hm)]`, which their
  conclusions do not need: each version of an integrable function vanishes outside a set of `m` on
  which `μ` is σ-finite (`exists_mem_sigmaFinite_trim_restrict`), the union of countably many such
  sets is another, and outside the union the sum of the versions vanishes, as do the integrals of
  the sum over the sets of `m`, by the summability of their norms.  The consumers in
  `Mathlib/Probability/Independence/Conditional.lean` and
  `Mathlib/MeasureTheory/VectorMeasure/AddContent.lean` have finite measures.

- [ ] **Remove the residual branch of the `L¹` conditional expectation construction.**
  `dominatedFinMeasAdditive_condExpInd` and `condExpL1CLM` in
  `Mathlib/MeasureTheory/Function/ConditionalExpectation/CondexpL1.lean` extend the strict
  `condExpInd`, defined on measurable sets of finite measure, by an anonymous `0` branch at their
  single construction site, because `L1.setToL1` takes a set function defined on every set; the
  result is independent of the branch (`L1.setToL1_congr_left'`).  A `setToL1` interface for set
  functions on measurable sets of finite measure would remove it.  It belongs with the `setToFun`
  totalization of the entry "Separate integrability from existence of a target-valued Bochner
  integral", on which the versions built through `condExpL1CLM` and `setToFun` also depend, as
  `condLExp` depends on `Measure.rnDeriv` (entry "Make Radon--Nikodym data conditional on
  decomposition existence").  `IsCondExp` takes `[CompleteSpace E]` as a sufficient condition for
  its Bochner integrals; an incomplete codomain is decided with the same Bochner entry.

- [ ] **Decide the definitions of supermartingales and submartingales without σ-finiteness.**
  `Supermartingale` and `Submartingale` in `Mathlib/Probability/Martingale/Basic.lean` require, for
  `i ≤ j`, a conditional expectation of `f j` given `ℱ i` at most, or at least, `f i`, which exists
  for a σ-finite filtration.  Without σ-finiteness the submartingales are not closed under `⊔`: for
  Lebesgue measure on `ℝ`, `ℱ 0 = ⊥` and `ℱ n` the Borel sets for `n ≥ 1`, `f = 0` and `g` with
  `g 0 = 0` and `g n = (Icc 0 1).indicator 1 - (Ioc 1 2).indicator 1` for `n ≥ 1` are martingales,
  but `(f ⊔ g) 1 = (Icc 0 1).indicator 1` has no conditional expectation given `⊥`, whose versions
  are integrable constants, that is `0`, of integral `0 ≠ 1`.  So `Submartingale.sup` and
  `Submartingale.pos` take `[SigmaFiniteFiltration μ ℱ]`, as do the constructors from one-step
  versions or set integrals, `submartingale_nat` and `submartingale_of_setIntegral_le`, for which it
  is necessary: for Lebesgue measure on `ℝ`, `ℱ 0 = ⊥`, and `ℱ n` generated by `Icc 0 1` for
  `n ≥ 1`, the process with `f 0 = f 1 = 0` and `f n = (Icc 0 1).indicator 1` for `n ≥ 2` has
  nonnegative one-step versions, but `f 2` has no conditional expectation given `⊥`.  The
  set-integral definition `∀ s ∈ ℱ i, ∫ x in s, f i x ∂μ ≤ ∫ x in s, f j x ∂μ` is equivalent under
  σ-finiteness (`submartingale_of_setIntegral_le`, `Submartingale.setIntegral_le`) and closed under
  `⊔` without it; decide which object is intended, against the literature on martingales for
  infinite measures.

- [ ] **Weaken the remaining hypotheses of the conditional expectation consumers.**
  These hypotheses are stronger than the statements need, by the paper arguments given.
  `IsCondExp.add` and `IsCondExp.sub` in `ConditionalExpectation/Basic.lean` take both summands
  integrable, while one integrable summand suffices, since the other summand is then integrable on
  each set where the sum is, and `IsCondExp.finsetSum` needs all summands but one; then
  `condVar_of_ae_eq_zero_or_one` in `Mathlib/Probability/Distributions/TwoValued.lean` would hold
  for every measure with `Integrable X μ` in place of `[IsFiniteMeasure μ]`.
  `Integrable.tendsto_ae_condExp`, `Integrable.tendsto_eLpNorm_condExp`, `tendsto_ae_condExp`, and
  `tendsto_eLpNorm_condExp` in `Mathlib/Probability/Martingale/Convergence.lean`, and
  `tendsto_sum_indicator_atTop_iff'` and `ae_mem_limsup_atTop_iff` in
  `Mathlib/Probability/Martingale/BorelCantelli.lean`, take a finite measure where σ-finiteness on
  `ℱ 0` should suffice: cover the space by sets of `ℱ 0` of finite measure, restrict the versions
  with `IsCondExp.restrict`, and combine the finite cases, with the tail bound
  `IsCondExp.setIntegral_norm_le` for the `L¹` statements.  Some σ-finiteness is needed: for
  `ℱ n = ⊥`, an infinite measure, and `s n = univ`, every constant is a version, the limsup is the
  whole space, and the sums of the versions `0` stay at `0`.  The three `SubsetOfNat` theorems of
  `Mathlib/Probability/Martingale/OptionalSampling.lean` take
  `[LocallyFiniteOrder ι] [OrderBot ι] [TopologicalSpace ι] [DiscreteTopology ι]` where countable
  ranges of the stopping times should suffice, through countable-range versions of
  `IsStoppingTime.measurableSet_le_stopping_time` and `measurableSet_inter_le` in
  `Mathlib/Probability/Process/Stopping.lean`; its `CountableRange` theorems need only
  `[PartialOrder ι]`.  `IsCondExp.of_tendsto` in `ConditionalExpectation/Basic.lean` takes the
  `m`-measurability `hgm` of the limit `g` and an integrable bound `bG` of the versions `G n`, which
  follow from its other hypotheses: `m`-strongly measurable versions of the `G n` converge on a set
  of `m` whose complement is null, so `exists_stronglyMeasurable_limit_of_tendsto_ae` for
  `μ.trim hm` gives an `m`-strongly measurable function almost everywhere equal to `g` (the
  library's `aestronglyMeasurable_of_tendsto_ae` is stated only for the ambient σ-algebra), and the
  `G n` vanish outside a set `t ∈ m` on which `μ` is σ-finite, a countable union of the sets of
  `exists_mem_sigmaFinite_trim_restrict`, and are bounded on `t` by a version of the conditional
  expectation of `bF` for `μ.restrict t`, by conditional Jensen for the norm and monotonicity.

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

- [ ] **Determine whether the exact weighting domain alone preserves s-finite kernels.**
  `Kernel.IsSFiniteKernel.withDensity` in `Mathlib/Probability/Kernel/WithDensity.lean` proves
  s-finiteness for jointly measurable densities, including infinite values.  Determine whether
  `[IsSFiniteKernel κ]` and `Measurable (fun a ↦ (κ a).withDensity (f a))` suffice without joint
  measurability of `f`, on arbitrary measurable spaces, or give a counterexample.  The existing
  proof uses joint measurability to weight each finite component and truncate each density.
  `Measure.withDensity.instSFinite` supplies s-finiteness of every fiber for arbitrary densities,
  but does not supply a measurable sequence of uniformly finite kernels.  The bounded audit
  established neither the general implication nor a counterexample; do not treat the sufficient
  joint-measurability hypothesis as necessary.

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
  whether `SFinite μ` is needed when `κ` is s-finite, before weakening the assumptions.  The
  Bochner-integral lemmas of `Mathlib/Probability/Kernel/Disintegration/Integral.lean` and the
  integrability statements of `Mathlib/Probability/Kernel/CondDistrib.lean` take an s-finite first
  marginal or law for this reason.

- [ ] **Extend the kernel Radon--Nikodym derivative beyond finite kernels.**
  `Kernel.rnDeriv`, `Kernel.singularPart`, and their lemmas in
  `Mathlib/Probability/Kernel/RadonNikodym.lean` assume finite kernels.  The posterior statements
  `rnDeriv_posterior_ae_prod`, `rnDeriv_posterior`, `rnDeriv_posterior_symm`,
  `posterior_eq_withDensity`, `posterior_eq_withDensity_of_countable`,
  `posterior_boolKernel_apply_false`, and `posterior_boolKernel_apply_true` in
  `Mathlib/Probability/Kernel/Posterior.lean` take the derivatives of a representative with respect
  to `Kernel.const _ μ` and of `κ` with respect to `Kernel.const _ (κ ∘ₘ μ)`, so they keep a finite
  prior and a finite kernel, and `Measure.AbsolutelyContinuous.kernel_of_compProd` in
  `Mathlib/Probability/Kernel/Composition/AbsolutelyContinuous.lean` assumes finite kernels for the
  same reason.  Determine the domain on which the derivative is defined, the statements that hold
  for s-finite or σ-finite kernels, and whether the posterior density formula holds for a σ-finite
  prior with a σ-finite law of the data.

- [ ] **State the almost-everywhere-invariant lemmas about conditional kernels for every
  representative.**
  The disintegration, the composition-products, and the measures and Lebesgue integrals of a
  representative of `Measure.condKernel`, `Kernel.condKernel`, `condDistrib`, `posterior`, and
  `condExpKernel` are stated for every representative, through `Measure.HasCompProd.congr` and
  `Kernel.HasCompProd.congr`.  Each representative agrees almost everywhere with a Markov one, and
  the following statements do not change under almost-everywhere modification of the representative
  but still take a Markov, finite, or s-finite one.  In
  `Mathlib/Probability/Kernel/CondDistrib.lean`:
  `AEStronglyMeasurable.ae_integrable_condDistrib_map_iff`,
  `AEStronglyMeasurable.integral_condDistrib_map`, `AEStronglyMeasurable.integral_condDistrib`,
  `aestronglyMeasurable_integral_condDistrib`, `map_mem_condDistrib_comp`,
  `Integrable.condDistrib_ae_map`, `Integrable.condDistrib_ae`,
  `Integrable.integral_norm_condDistrib_map`, `Integrable.integral_norm_condDistrib`,
  `Integrable.norm_integral_condDistrib_map`, `Integrable.norm_integral_condDistrib`,
  `Integrable.integral_condDistrib_map`, `Integrable.integral_condDistrib`,
  `isCondExp_condDistrib_real` (finite representatives), `isCondExp_prod_integral_condDistrib'`,
  `isCondExp_prod_integral_condDistrib₀`, `isCondExp_prod_integral_condDistrib`,
  `isCondExp_integral_condDistrib`, `isCondExp_integral_condDistrib'`, and
  `isCondExp_integral_condDistrib_id` (s-finite representatives).  In `Posterior.lean`:
  `posterior_prod_id_comp`, `parallelProd_posterior_comp_copy_comp`, `deterministic_comp_posterior`,
  `mem_posterior_posterior`, and `comp_mem_posterior_comp`, and the Radon--Nikodym statements in
  the preceding kernel-derivative task. In `Condexp.lean`, consider `isCondExp_condExpKernel_real`,
  `isCondExp_integral_condExpKernel`, and `IsCondExp.ae_eq_trim_integral_condExpKernel`.  In
  `Mathlib/Probability/Independence/ConditionalKernel.lean`:
  `condIndepFun_iff_compProd_map_prod_eq_compProd_prod_map_map`,
  `condIndepFun_iff_map_prod_eq_prod_map_map`, `condIndepFun_iff_map_prod_eq_prod_comp_trim`,
  `condIndepFun_iff_map_prod_eq_prod_condDistrib_prod_condDistrib`, and
  `condIndepFun_iff_prodMkRight_mem_condDistrib`.  The Bochner integrals of
  `Disintegration/Integral.lean` take an s-finite conditional kernel; for a measure with a σ-finite
  first marginal, every disintegration agrees almost everywhere with a Markov one.  State these
  lemmas for every representative, or, where a statement needs an s-finite representative, such as a
  product with it, on the domain of that construction; for the Bochner integrals, the outer
  integrand changes only on a null set when the representative does.

- [ ] **Determine whether conditional independence should extend beyond finite measures.**
  The notions of `Mathlib/Probability/Independence/Conditional.lean` require a finite measure, the
  domain of probability theory on which the conditional probabilities `μ⟦t | m'⟧` of all
  null-measurable sets exist.  For a σ-finite `μ.trim hm'`, every measurable set `t` still has a
  conditional probability, the Radon-Nikodym derivative of `μ (t ∩ ·)` on `m'`, which is `condLExp`
  of the indicator and is unique almost everywhere, so the specification extends canonically there.
  The class-only formulation that this entry's predecessor proposed would also have covered some
  measures whose trim is not σ-finite, such as counting measure on `ℝ` given the whole σ-algebra
  (`id_mem_condExpKernel_count` in `FidelityTest/Probability/Kernel/CondExpKernelStrict.lean`).  For `CondIndepSets` of
  families that do not contain `Set.univ`, sets of finite measure under a σ-finite trim would
  suffice; without a σ-finite trim a set of finite measure need not have a conditional probability:
  on `[0, 1] × Bool` with Lebesgue measure on the `false` copy and counting measure on the `true`
  copy, given the sets `A ×ˢ univ`, a density `h` of the `false` copy satisfies
  `h x * (0 + 1) = 0` on each `{x} ×ˢ univ`, so `h = 0` against the total mass `1`.  Decide the
  domain of each notion against these cases before generalizing.

- [ ] **Decide the domain of unconditional and kernel independence for sets that are not
  measurable.**
  `Kernel.IndepSets`, `Kernel.Indep`, `Kernel.IndepFun`, their families in
  `Mathlib/Probability/Independence/Kernel/`, and the unconditional notions built from them evaluate
  the measures of arbitrary sets, outer measures on sets that are not measurable, and admit
  σ-algebras that are not sub-σ-algebras and functions that are not measurable.  Conditional
  independence in `Mathlib/Probability/Independence/Conditional.lean` requires the
  null-measurability of the sets it compares, since their conditional probabilities exist only
  there, so given the trivial σ-algebra it no longer agrees with independence on data that is not
  null-measurable.  Decide whether outer-measure independence of such data is a legitimate total
  extension with a literature source, or whether the unconditional and kernel notions should carry
  null-measurability too, and migrate accordingly.

- [ ] **Give `HasSubgaussianMGF.fun_zero` its exact condition.**
  `HasSubgaussianMGF.fun_zero` and `HasSubgaussianMGF.zero` in
  `Mathlib/Probability/Moments/SubGaussian.lean` take `[IsZeroOrProbabilityMeasure μ]`, while the
  zero function is sub-Gaussian with parameter `0` exactly for a finite measure of total mass at
  most `1`, by the integrability and the moment-generating function at `t = 0`.  Decide between a
  class of sub-probability measures and an explicit hypothesis, keeping the `simp` use.

- [ ] **Determine whether the converse absolute-continuity lemma of the posterior needs an s-finite
  law of the data.**
  `absolutelyContinuous_of_posterior` and `absolutelyContinuous_posterior_iff` in
  `Mathlib/Probability/Kernel/Posterior.lean` take `[SFinite (κ ∘ₘ μ)]` for a finite kernel `κ`: the
  prior restricted to the set where `κ ω ≠ 0` then has the same joint law and posterior and is
  s-finite, and for an s-finite prior the proof compares the joint law with the product of the
  prior and `(κ ∘ₘ μ).toFinite`.  For a Markov kernel whose posterior exists the condition is that
  the prior is s-finite (`posterior_comp_self`).  `absolutelyContinuous_posterior` holds for every
  prior.  For every prior and every measurable `B` with `(κ ∘ₘ μ) B = 0`, `κ ω B = 0` for
  `μ`-almost every `ω`; the conclusion `∀ᵐ ω ∂μ, κ ω ≪ κ ∘ₘ μ` exchanges these quantifiers.
  Counting measure does not decide the question: with measurable singletons, the hypothesis `h_ac`
  holds for every kernel, and so does the conclusion, since `κ ω ≤ κ ∘ₘ count`.  The test case is a
  prior for which `κ ∘ₘ μ` is not s-finite, which depends on `κ`: for `κ = Kernel.id`, the measure
  on `ℝ` that vanishes on countable sets and is infinite on the other Borel sets is one, since it is
  not s-finite.  For that prior and every kernel, `(κ ∘ₘ μ) B` is `0` or `∞` according as countably
  or uncountably many `κ ω` charge `B`.  No proof or counterexample is known.

- [ ] **Formalize the domain characterization of conditional CDFs.**
  The paper argument characterizes `ProbabilityTheory.HasUniqueCondCDF ρ` by semifiniteness of `ρ.fst`
  and existence of densities of each ray measure `ρ.IicSnd x` with respect to `ρ.fst`. A positive
  marginal set with no subset of finite positive measure prevents uniqueness by allowing a shift
  and averaging of the conditional CDFs there. For s-finite `ρ` the proposed characterization
  reduces to σ-finiteness of `ρ.fst`. `Disintegration/CondCDF.lean` proves the σ-finite sufficient
  instance. [Counterexamples/CondCDF.lean](Counterexamples/CondCDF.lean) tests planar volume and
  the image of counting measure under `a ↦ (a, 0)`.

- [ ] **Determine the exact domain of fiberwise conditional-kernel constructions.**
  `Kernel.condKernelCDF` and `Kernel.condKernel` in
  `Mathlib/Probability/Kernel/Disintegration/StandardBorel.lean` still use `[IsFiniteKernel κ]`.
  Determine when the fiberwise conditional CDFs and disintegrations can be constructed measurably
  in the parameter. The measure-level result for a σ-finite first marginal supplies a separate
  sufficient condition for `Measure.condKernel`.

- [ ] **Replace the σ-finite first marginal by a semifinite one in the uniqueness of conditional
  kernels.**
  `Measure.IsCondKernel.ae_isProbabilityMeasure`, `Measure.IsCondKernel.ae_eq_apply`,
  `Measure.IsCondKernel.ae_eq`, `Measure.mem_condKernel_iff`, `Measure.IsCondKernel.mem_condKernel`,
  `Kernel.IsCondKernel.ae_isProbabilityMeasure`, `Kernel.IsCondKernel.ae_eq`, and
  `Kernel.IsCondKernel.sectR_mem_condKernel` in `Mathlib/Probability/Kernel/Disintegration/` take a
  σ-finite first marginal, respectively a σ-finite `Kernel.fst κ a`.  Among conditions on the first
  marginal, semifiniteness, that every set of positive measure contains one of finite positive
  measure, is exact for them.  It suffices: if a disintegration gave a set of positive measure mass
  above `1 + 1/n`, or below `1 - 1/n`, a subset of finite positive measure would contradict the
  disintegration identity on it, and the same comparison of set integrals over sets of finite
  measure gives the almost everywhere uniqueness.  It is necessary: if `B` has positive measure and
  every measurable subset has measure `0` or `∞`, then every integral over `B` is `0` or `∞`, so
  multiplying a Markov disintegration by `2` on `B` gives another one.  The library has no class of
  semifinite measures; add one and restate these lemmas, and their consumers, on it.

  A deferred paper characterization for `condExpJointLaw` in
  `Mathlib/Probability/Kernel/Condexp.lean` concerns `m = generateFrom {s}`. The proposed uniqueness
  domain requires each part `t` in `{s, sᶜ}` to have finite measure or satisfy
  `μ.restrict t = ∞ • P` for a zero-one probability measure `P`. The disintegration is constant
  on each part, and on an infinite part its uniqueness depends on the probability values determined
  by `μ (t ∩ B) = ∞ * P B`. The existing instance for finite `μ` covers current consumers.

- [ ] **Formalize the counterexamples recorded for the composition-product domain.**
  The docstrings of `Measure.hasCompProd_sum_left` and `Measure.hasCompProd_compProd` in
  `Mathlib/Probability/Kernel/Composition/` and the paper arguments below show that the
  domain fails for an uncountable sum of Dirac measures; that `μ.HasCompProd (κ ⊗ₖ η)` can fail
  without the domain of `(μ ⊗ₘ κ) ⊗ₘ η`; that the constant kernels of counting measure on `ℝ` and
  of Lebesgue measure on `[0, 1]` have a product against which the order of integration cannot be
  changed; and that the domain does not pass from counting measure to Lebesgue measure.  Each needs
  a set that is not Borel, which exists by counting with
  `SigmaAlgebra.cardinal_measurableSet_le_continuum`, or one that is not Lebesgue measurable;
  `Counterexamples/KernelCompProd.lean` is the precedent. Also formalize the following two cases.

  - `κ ×ₖ η` can exist while `(κ ∥ₖ η) ∘ₖ copy` is undefined. On `Bool`, take `κ true` to be
    Lebesgue measure and `η false` the sum of Dirac measures over a non-Lebesgue-measurable subset
    `T` of `[0, 1]`. Set the other fibers to zero. The parallel composition sees the indicator
    of `T` as the section measures of the diagonal.
  - `κ.HasCompProd η` can fail with either factor s-finite. With `ν` the sum of
    Dirac measures over a non-Borel `T ⊆ ℝ`, use `const ℝ ν` followed by the deterministic test
    of equality of the two coordinates, or `Kernel.id` followed by `const (ℝ × ℝ) ν`. Testing
    equality produces the nonmeasurable indicator of `T` in the section integrals.

  The docstring of `HasCondDistrib.comp_right` in `Mathlib/Probability/HasCondDistrib.lean`
  states that its domain
  hypothesis does not follow from `h`: for the identity `f` from the discrete σ-algebra to the
  Borel σ-algebra on `ℝ`, a set `T` that is not Borel, the composition-product `P` of the sum of
  `∞ • dirac t` over `t ∈ T` with `κ.comap f`, and `κ` constant at the sum of `dirac u` over
  `u ∉ T`, the measures of the sections of the diagonal have lower integral `0` and upper integral
  `∞` against the law of `f ∘ Z`.  The docstring of `Measure.HasCompProd.congr_sections` in
  `Mathlib/Probability/Kernel/Composition/MeasureCompProd/Defs.lean` states that agreement of the
  measures of the sections is strictly weaker than almost everywhere equality of the kernels: with
  the countable-cocountable σ-algebra on an uncountable type and a nonzero measure that vanishes on
  countable sets, every product-measurable set lies in the σ-algebra generated by countably many
  rectangles, so off a
  countable set the Dirac kernel and the constant kernel of the measure that is one on cocountable
  sets give its sections the same measure, while they differ at every point.

- [ ] **Make Radon--Nikodym data conditional on decomposition existence.**
  `Measure.rnDeriv` and `Measure.singularPart` in
  `Mathlib/MeasureTheory/Measure/Decomposition/Lebesgue.lean:80` and `:73` return zero without
  `HaveLebesgueDecomposition μ ν`.  Require that evidence or return a bundled decomposition; apply
  the same review to signed and complex vector-measure wrappers.  `IsCondCDF.ofReal_ae_eq_rnDeriv`
  and the private existence proof for `condCDF` take `rnDeriv` only of ray measures with respect to
  a σ-finite `ρ.fst`, where the decomposition exists, so they can supply the evidence.
  `ProbabilityTheory.pdf` (`Mathlib/Probability/Density.lean:130`) is `(map X ℙ hX).rnDeriv μ`, so
  it is `0` without a Lebesgue decomposition (`pdf_of_not_haveLebesgueDecomposition`, line 138),
  although `HasPDF` already carries the decomposition and the absolute continuity; its consumers are
  `Probability/Density.lean`, the `Probability/Distributions/` files for the beta, Cauchy,
  exponential, gamma, Gaussian, Pareto, and uniform laws, and `Probability/HasLaw.lean`.
  `SignedMeasure.rnDeriv` (`Mathlib/MeasureTheory/VectorMeasure/Decomposition/Lebesgue.lean:156`) is
  built from `Measure.rnDeriv` of the Jordan parts through `ENNReal.toReal`, and
  `ComplexMeasure.rnDeriv` (line 423) from `SignedMeasure.rnDeriv` of the real and imaginary parts,
  so they inherit both the missing-decomposition zero and the infinity-to-zero conversion.  For a
  countable parameter space, `Kernel.rnDerivAux` (`Mathlib/Probability/Kernel/RadonNikodym.lean:91`)
  is `((κ a).rnDeriv (η a) x).toReal`, and `Kernel.rnDeriv` and `Kernel.singularPart` (lines 227 and
  258) are built from it.

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
  integer poles. Use pole-excluding inputs or a meromorphic-function object. A separate total
  construction needs a specification that determines its values at the poles.

- [ ] **Determine the analytic-continuation domain of regularized hypergeometric evaluation.**
  `Complex.regularizedGaussHGFun` in
  `Mathlib/Analysis/SpecialFunctions/RegularizedHypergeometric.lean` takes summability in natural
  index order. Determine the continuation and branch choices beyond that convergence domain.
  [DLMF 16.2.5](https://dlmf.nist.gov/16.2.E5) gives the scaled coefficients. A continuation must
  agree with the series on its domain and specify the values it extends to.

- [ ] **Require normality for ordinal fixed-point enumerators.**
  `Ordinal.nfp` and `Ordinal.deriv` in `Mathlib/SetTheory/Ordinal/FixedPoint.lean:246` and `:325`
  accept arbitrary functions although their names promise fixed-point enumeration; several theorems
  depending on junk values are already deprecated.  Put normality/continuity evidence in the named
  interface and retain generic transfinite iteration under a distinct name.

- [ ] **Classify the no-successor branch of `ComplexShape.next` and `prev`.**
  `ComplexShape.next c i` in `Mathlib/Algebra/Homology/ComplexShape.lean:141`, with `prev` as its
  dual, is the index `j` with `c.Rel i j` when one exists, which is unique because the relation is
  functional (`next_eq`), and `i` itself otherwise (`next_eq_self'`); the docstring calls the first
  case an arbitrary choice and states the `i` branch.  The total projection supplies `xNext`,
  `xPrev`, `dFrom`, and `dTo` for every index of a homological complex, whose differential is zero
  at an index without a successor.  About thirty files use `c.next`, `c.prev`, or their lemmas by a
  textual count.  The value is determined where it exists, so the question is the no-successor
  branch: decide whether it is a checked technical device that can stay behind the `dFrom` and `dTo`
  API, or whether `next` and `prev` should take the relation as evidence or return an `Option`, and
  which theorems depend on `xNext` at an index with no successor.

## XL -- foundational work; implementation requires an explicit task

- [ ] **Expose the exact domain of extended nonnegative division.**
  **Accepted design, pending implementation.** Ordinary `ENNReal` division is the restriction
  of ordinary `EReal` division to nonnegative inputs. Elaborate `a / b` to `ENNReal.div a b h`,
  with `h` proving `b ≠ 0 ∧ (a ≠ ⊤ ∨ b ≠ ⊤)`. The signed quotient is nonnegative on this domain.
  Prove that `ENNReal.toEReal` preserves and reflects this domain and commutes with division
  there. State the bridge in a module that imports both APIs, and prove agreement with
  `Checked.div` for unit denominators.

  - Expose `ENNReal.extendedDiv a b h` as the maximal continuous extension of the positive
    finite quotient within `ENNReal`. Its proof obligation is
    `(a ≠ 0 ∨ b ≠ 0) ∧ (a ≠ ⊤ ∨ b ≠ ⊤)`. Use `a * b⁻¹` on this domain and define the
    ordinary quotient by restriction. In particular, `extendedDiv a 0` is `⊤` with evidence
    `a ≠ 0`, and `extendedDiv a ⊤` is `0` with evidence `a ≠ ⊤`.
    `ENNReal.Tendsto.div` gives continuity on this domain. For any positive finite `c`, the pairs
    `(c * t, t)` approach either excluded point as `t` approaches the corresponding endpoint,
    with quotient `c`. Hence neither point has a unique limiting value.
  - Expose `ENNReal.divInf a b = sInf {q | a ≤ b * q}` as a named total quotient, implemented
    by `a * b⁻¹` with the zero-absorbing product. Both excluded pairs have value zero.
    The ratio test `FormalMultilinearSeries.ofScalars_radius_eq_inv_of_tendsto_ENNReal` in
    `Mathlib/Analysis/Analytic/OfScalars.lean` uses this convention for eventually zero
    coefficients. See the lower product and reciprocal in
    [Valverde-Albacete and Peláez-Moreno, Theorem 1 and Example 2](https://www.mdpi.com/1099-4300/21/8/780).
  - Supply `IsQuantale ℝ≥0∞` from `ENNReal.mul_sSup` and `ENNReal.sSup_mul`. Use the existing
    `Quantale.leftMulResiduation b a` (`b ⇨ₗ a`) in `Mathlib/Algebra/Order/Quantale.lean` for
    `sSup {q | q * b ≤ a}`. Its adjunction holds for all operands and both excluded pairs have
    value `⊤`. For example, `div_le_radius_compContinuousLinearMap` in
    `Mathlib/Analysis/Analytic/ConvergenceRadius.lean` can give the exact infinite bound after
    precomposition by the zero map even for a series of radius zero. See
    [Bacci et al., Rational Lawvere Logic, §2 and Table 1](https://drops.dagstuhl.de/storage/00lipics/lipics-vol363-csl2026/html/LIPIcs.CSL.2026.3/LIPIcs.CSL.2026.3.html).

  A scratch Lean check using a local `IsQuantale` instance verified the endpoint values,
  agreement of the two total extensions exactly on the domain of `extendedDiv`, and continuity
  there.
  Implement the slash selection, proof discharge, and checked delaboration in
  `Mathlib/Lean/Elab/OperatorTree.lean`. Remove the ambient `DivInvMonoid` and `DivInvOneMonoid`
  instances in `Mathlib/Basic/ENNReal/{Basic,Inv}.lean` and provide reciprocal and integer powers
  independently of `Div`. Audit the affected callers for the intended division specification and
  update the ordinary division contract in `FORK_DESIGN.md` in the same migration. Check that
  ordinary `/` rejects every zero denominator and `(⊤, ⊤)`, while `extendedDiv` admits positive
  numerators over zero and rejects both indeterminate pairs. Verify the embedding law and check
  that instance inference cannot recover ambient `Div` or `HDiv` on `ENNReal`.

- [ ] **Expose the exact domain of signed extended-real division.**
  **Accepted design, pending implementation.** Put `E = [-∞, +∞]` with the order topology and view
  `ℝ` as its finite elements. Ordinary division on `EReal` is the maximal continuous extension
  of real division, with domain

  `D = (E × (ℝ \ {0})) ∪ (ℝ × {−∞, +∞})`.

  A finite nonzero denominator gives the usual signed quotient, including infinite numerators.
  A finite numerator divided by either infinity gives `0`, since the numerator stays bounded
  locally. For a nonzero limiting numerator, denominators approaching zero from opposite sides
  give opposite infinite limits. At `(0, 0)`, the finite pairs `(c * t, t)` give different limits
  for different `c` as `t` approaches zero from above. At each pair of infinities, the finite
  pairs `(s * c * t, r * t)` with the prescribed signs `s, r ∈ {−1, 1}` and `c > 0` approach the
  pair as `t` tends to `+∞`, with quotient `s * r * c`. Thus every excluded point has competing
  limits.

  Elaborate `a / b` to a proof-bearing `EReal.div a b h`, where `h` requires `b ≠ 0` and at least
  one of `a` and `b` to be finite. For finite nonzero `b`, reuse checked unit division and prove
  agreement on that domain using `EReal.isUnit_iff`. For an infinite denominator, return zero
  under the finite-numerator hypothesis. Migrate the existing division API and its automation in
  `Mathlib/Data/EReal/Inv.lean` and the slash selection in `Mathlib/Lean/Elab/OperatorTree.lean`.
  Prove agreement with real division and continuity on `D`, and identify the restriction of `D`
  under `ENNReal.toEReal` with the ordinary `ENNReal` division domain above. Check finite quotients,
  both signs of infinity in the numerator, and finite numerators over both infinities. Require
  rejection for every zero denominator and all four pairs of infinities.

- [ ] **Separate signed extended-real subtraction from nonnegative monus.**
  **Accepted design, pending implementation.** Give ordinary `EReal` subtraction the exact domain
  `(a ≠ ⊤ ∨ b ≠ ⊤) ∧ (a ≠ ⊥ ∨ b ≠ ⊥)` through a proof-bearing `EReal.sub a b h`
  and checked `a - b` notation. For any real `c`, the finite pair `(t + c, t)` has difference
  `c` as `t` tends to either signed infinity. Both pairs of equal infinities therefore lack a unique
  continuous extension. Retain the signed differences for finite operands, one infinite operand,
  and opposite infinities. In `Mathlib/Data/EReal/Operations.lean`, separate negation from the
  ambient total subtraction supplied by `SubNegZeroMonoid` and restrict `bot_sub`
  and `sub_top` to their checked domains.

  - Expose `ENNReal.monus a b` explicitly as the least `q` satisfying `a ≤ q + b`. It satisfies
    `ENNReal.monus a b ≤ q ↔ a ≤ q + b` for all inputs, so `ENNReal.monus ⊤ ⊤ = 0`.
    Reuse the specification proved by `ENNReal.sub_eq_sInf` in
    `Mathlib/Basic/ENNReal/Operations.lean` and the order law of `OrderedSub`. See
    [Bacci et al., Rational Lawvere Logic, §2 and Table 1](https://drops.dagstuhl.de/storage/00lipics/lipics-vol363-csl2026/html/LIPIcs.CSL.2026.3/LIPIcs.CSL.2026.3.html).
  - For a signed difference of `ENNReal` inputs, cast explicitly with `ENNReal.toEReal` and use
    `(a : EReal) - (b : EReal)`. The cast is an order embedding and sends `⊤` to `⊤`,
    so only the pair `(⊤, ⊤)` is excluded on these inputs. Adapt the existing
    `ENNReal.toEReal_sub` bridge to compare monus with checked subtraction when `b ≤ a` and
    `b ≠ ⊤`. Ordinary `-` on `ENNReal` itself is unavailable even for finite ordered inputs.

  Remove the ambient subtraction paths in `Mathlib/Basic/ENNReal/Basic.lean`, including inference
  through the `WithTop ℝ≥0` representation in `Mathlib/Algebra/Order/Sub/WithTop.lean`.
  Audit `Sub`, `HSub`, implicit coercions, elaboration, and delaboration. Migrate callers according
  to the required law, including the exact equality `measure_sdiff` and the monus inequality
  `le_measure_sdiff` in `Mathlib/MeasureTheory/Measure/Basic.lean`. Check rejection of both
  indeterminate `EReal` expressions and bare `ENNReal` subtraction, and check finite negative
  results, opposite infinities, explicit casts, and the total monus law.

- [ ] **Restrict inverse operations in additive ordered groups with top to additive units.**
  In `Mathlib/Algebra/Order/AddGroupWithTop.lean`, replace the `SubNegMonoid` parent and axioms
  involving ambient negation with `isAddUnit_of_ne_top : a ≠ ⊤ → IsAddUnit a`. Derive
  `isAddUnit_iff` from this field, absorption at `⊤`, and nontriviality. Derive finite-element
  regularity from units and use the group operations of `AddUnits`. The direct `neg_top` proof
  dependencies are `neg_eq_top`, `sub_top`, `add_neg_cancel_iff_ne_top`, and the proofs in
  `toSubtractionMonoid`. Remove the fallback laws and ambient inverse, group-style subtraction,
  and integer scalar instances. Give `WithTop.untop₀_neg` a finite-domain formulation if needed.

  - For `WithTop G`, extract a finite representative `g : G` and use `↑(-g)` as its inverse.
    Replace `ArchimedeanClass.instNeg` in `Mathlib/Algebra/Order/Ring/Archimedean.lean` with a
    unit construction on non-top classes. A nonzero representative `x` gives `u : Rˣ` with
    value `x` and inverse class `mk u.inv`. The two inverse equations follow from `mk_mul`,
    `u.val_inv`, `u.inv_val`, and `mk_one`. Identify the existing `FiniteArchimedeanClass R`
    with additive units where finite classes need a group API. Port `mk_inv`, `mk_div`, and
    `mk_zpow` using their existing unit hypotheses.
  - A finite subtrahend `b` makes `d + b = a` uniquely solvable for every `a`, including `⊤`.
    When `b = ⊤`, the equation has no solution for finite `a` and every `d` is a solution for
    `a = ⊤`. Preserve the independently specified `OrderedSub` in
    `Mathlib/Algebra/Order/Sub/WithTop.lean`. Integer scaling uses natural scaling for
    nonnegative scalars and requires a unit argument only for a negative scalar.
  - Keep the generic `Multiplicative`, `MinTropical`, and `MaxTropical` transports for valid
    input operations in `Mathlib/Algebra/Group/TypeTags/Basic.lean` and
    `Mathlib/Algebra/Tropical/Basic.lean`. Close the inherited `Inv` paths through `InvolutiveNeg`
    and `SubNegMonoid`, the direct `Div` path through `Sub`, and the tropical `Pow _ ℤ` path
    through `SMul ℤ`. The resulting `Pow _ ℤ` also enables `ZPow.ofPow`. Transport `IsAddUnit`
    to `IsUnit` and reuse `Checked.inv`, `Checked.div`, and `Checked.zpow`. On either tropical
    carrier the witness comes from `untrop x ≠ ⊤`, including when the carrier has no `Zero`. Build
    `isUnit_of_ne_zero` in `Mathlib/Algebra/Order/GroupWithZero/Canonical.lean` from the additive
    unit witness and preserve the ordered group-with-zero adapter.
  - Port `AddValuation.map_inv` and `map_div` using the image of the source unit. Check
    `StandardPart` through the valuation subring adapter and replace the use of ambient
    negation in `Hyperreal.archimedeanClassMk_epsilon_pos` using `mk (ω * ε) = 0` and
    `mk ω < 0`. In `Mathlib/Analysis/Meromorphic/`, retain translation of a possibly infinite
    order by the finite shift in `Order` and the nonzero denominator germ's finite order in
    `GermOrder`. Use the unit-locus hypotheses in the inverse, division, signed-power, and
    log-derivative theorems to prove finiteness where required. Recheck `NormalForm`,
    `TrailingCoefficient`, `Divisor`, `FactorizedRational`, `CanonicalDecomposition`,
    `LogCounting`, and the Weierstrass order formulas. At `TrailingCoefficientStrict`, use the
    existing finite-order hypothesis in place of the ambient `neg_eq_top` rewrite.
  - Verify that raw `Neg`, `Sub`, and `SMul ℤ` fail to synthesize on `WithTop ℤ` and
    `ArchimedeanClass ℝ`, and that raw `Inv`, `Div`, `Pow _ ℤ`, and `ZPow` fail on their
    multiplicative and tropical wrappers, including the ordered `Multiplicative Aᵒᵈ` adapter.
    Check genuine group instances, checked inversion of a finite element, division with a top
    numerator and finite denominator, rejection of a negative exponent at top, and the zero
    and positive exponent rules there. Scratch Lean checks established the two finite-unit
    constructions, the three wrapper transports, and top translated by a finite inverse.
    Full migration and downstream acceptance remain pending.

- [ ] **Separate natural monus from partial subtraction and predecessor.**
  Work on official Lean without replacing core `Nat` or changing its kernel/compiler primitives.
  Core `Nat.sub`, `Nat.pred`, division, and remainder remain imported and explicitly reachable.
  The selected migration must instead complete the fork's mathematical subtraction/predecessor
  interface, notation, elaboration, instances, statements, and semantic uses. An independently
  specified and audited monus may retain core `Nat.sub` as its implementation and support checked
  subtraction. Monus is retained mathematics; the retired interface is unrestricted ordinary
  subtraction. This does not permit wrapping an operator whose totalized semantics are selected for
  removal. Proof computations using faithful monus remain legitimate; remove replaceable uses of
  unfaithful operators and retain unavoidable toolchain dependencies only under the recorded proof
  boundary. Do not interpret removal of the ordinary fork surface as erasing or retyping Lean's
  existing builtin declarations, or defer required fork consumers to a toolchain task.
  `Nat.sub` returns zero when the subtrahend is larger, and `Nat.pred 0 = 0`; the current source
  calls these results garbage values in `Mathlib/Data/Nat/PSub.lean:15`.  Truncated subtraction is a
  legitimate monus operation with order-theoretic laws, but exposing it as ordinary `Nat.sub` and
  `a - b` makes it easy to read a theorem as partial or group subtraction while silently truncating
  outside `b ≤ a`.  Make `Nat.psub`/`Nat.ppred`, defined at lines 44 and 32, or proof-bearing
  wrappers the ordinary subtraction/predecessor boundary. Natural monus is the least `c` such that
  `a ≤ b + c`, which forces `c = 0` when `a ≤ b`. Use a name and notation that identify this
  order-theoretic operation. Remove the ordinary subtraction surface because it invites the wrong
  mathematical reading of monus.
  Audit and migrate
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
  The `sSup` of `Seminorm 𝕜 E` is such a case: `Seminorm.instSupSet`
  (`Mathlib/Analysis/Normed/Module/Seminorm/Basic.lean:488`), on which the
  `ConditionallyCompleteLattice` instance at line 583 is built, is the pointwise supremum when the
  set is pointwise bounded above and `⊥` otherwise, and `Seminorm.bddAbove_iff` (line 529)
  identifies pointwise boundedness with boundedness as seminorms.  The same pattern, with
  `sSup_of_not_bddAbove` stating the value `0`, holds for `GroupSeminorm`
  (`Mathlib/Analysis/Normed/Group/Seminorm.lean:268`) and `NonarchAddGroupSeminorm` (line 544).
  For `Mathlib/Analysis/Convex/Gauge.lean`, audit the use of the empty real infimum in `gauge_zero`,
  `gauge_zero'`, `gauge_empty`, `gauge_of_subset_zero`, and `gauge_closure_zero`. Finite-domain
  uses need a greatest-lower-bound certificate for the positive dilation set, with absorbency
  providing nonemptiness where applicable.

- [ ] **Replace `Module.finrank`'s infinite-to-zero convention.**
  `Module.finrank` in `Mathlib/LinearAlgebra/Dimension/Finrank.lean:62` is
  `Cardinal.toNat (Module.rank R M)` and occurs across roughly 179 maintained Lean files.
  Natural-valued rank needs finite-rank evidence; keep cardinal rank globally.  Migrate
  `AffineSubspace.finDim` (`Mathlib/LinearAlgebra/AffineSpace/Dimension.lean:51`) and other derived
  invariants without conflating finite rank with finite generation over general semirings.
  Two derived invariants state the zero case in their docstrings:
  `AlgebraicGeometry.Scheme.Hom.residueDegree` (`Mathlib/AlgebraicGeometry/ResidueField.lean:147`),
  the `finrank` of the residue field extension with 'a default value of zero when this degree is
  infinite', whose only consumer is `mapCoeff` in
  `Mathlib/AlgebraicGeometry/AlgebraicCycle/Basic.lean:56`, applied when the two weights agree; and
  `QuadraticForm.sigPos` and `sigNeg` (`Mathlib/LinearAlgebra/QuadraticForm/Signature.lean:65` and
  `:98`), which the docstrings define as `0` if `M` is infinite-dimensional, with no consumer
  outside the file.

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
  The inverse migration uses domain-coordinate derivative relations on units or on the actual
  locus of invertibility. Its computed inverse derivatives must be justified by the proved
  derivative and uniqueness at that point, with the required coordinate embedding/range
  hypotheses; they cannot use the projection's nondifferentiable or nonunique branch. The
  underlying projection redesign remains this separate foundational task.

- [ ] **Separate integrability from existence of a target-valued Bochner integral.**
  `MeasureTheory.integral` in `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:158` returns zero
  when the function is nonintegrable or the target is incomplete.  `CompleteSpace` is a standard
  sufficient condition for the general construction, but not an exact necessity for every
  individual function: an integrable simple function has a target-valued integral given by a finite
  sum even in an incomplete target.  Keep
  `Integrable` and target-valued existence distinct, audit theorems that use the fallback, and
  prototype an existence-certified integral before deciding whether notation or expectation APIs
  should change.  The lower Lebesgue integral is not part of this candidate.
  The fallback propagates to every integral derived from `MeasureTheory.integral`:
  `intervalIntegral` (`Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean:659`,
  `integral_undef` at line 711), `circleIntegral`
  (`Mathlib/MeasureTheory/Integral/CircleIntegral.lean:425`, `integral_undef` at line 486),
  `circleAverage` (`Mathlib/MeasureTheory/Integral/CircleAverage.lean:55`,
  `circleAverage.integral_undef` at line 64), `curveIntegral`
  (`Mathlib/MeasureTheory/Integral/CurveIntegral/Basic.lean:123`,
  `curveIntegral_of_not_completeSpace` at line 133), and `VectorMeasure.integral`
  (`Mathlib/MeasureTheory/VectorMeasure/Integral.lean:250`), which is `0` for a nonintegrable
  function or an incomplete target through `setToFun`
  (`Mathlib/MeasureTheory/Integral/SetToL1/Function.lean:42`).  The moment family inherits it too:
  `moment` and `centralMoment` (`Mathlib/Probability/Moments/Basic.lean:55`, `:62`), `mgf` and `cgf`
  (`:122`, `:127`; `mgf_undef` and `cgf_undef` at lines 176 and 179, with `cgf` adding `log 0 = 0`),
  and `complexMGF` (`Mathlib/Probability/Moments/ComplexMGF.lean:72`; `complexMGF_undef`, line 74).
  Decide for each whether the public operation takes the integrability, interval integrability, or
  circle integrability as evidence, or has another independently justified mathematical domain.
  An inherited base zero fallback alone does not justify the derived operation. If the base
  integral is a separately deferred foundational problem, prove that the selected operation uses
  it on its valid domain and record the dependency. Theorems that hold only because both sides
  are fallback values are listed in the S candidate on coinciding fallbacks.

- [ ] **Audit `tsum`/`tprod` choice projections against `HasSum`/`HasProd`.**
  `tsum` and `tprod` in `Mathlib/Topology/Algebra/InfiniteSum/Defs.lean:132` and `:142` return zero
  and one when `HasSum`/`HasProd` fails, with additional uniqueness concerns in nonseparated spaces.
  `HasSum`/`HasProd` are already the faithful relational cores, while `tsum`/`tprod` are total value
  projections. Identify theorem statements or consumers that actually exploit fallback or
  nonuniqueness. Expose `HasSum` and `HasProd` for relational statements, and require existence and
  uniqueness for convergence-based evaluation. An independent total operation needs a
  specification that determines its values even where convergence fails or gives multiple limits.
  Remove the zero and one fallbacks from the ordinary convergence-based projections.
  Coordinate the complete accepted scope with dependent series, power-series evaluation, and the
  separate `finsum`-based Euler-characteristic audit.
  `Units.oneSub` in `Mathlib/Analysis/SpecificLimits/Normed.lean` uses a geometric series as the
  inverse of `1 - t` under `‖t‖ < 1`. Here `summable_geometric_of_norm_lt_one` supplies convergence,
  the two multiplication laws certify the unit, and `hasSum_geom_series_inverse` supplies the
  relational sum. This construction must keep that proved summability boundary while `tsum` is
  audited separately; an arbitrary nonsummable series cannot become an inverse by its zero value.
  `Mathlib/NumberTheory/NumberField/DirichletDensity/Asymptotics.lean` proves convergence and
  denominator positivity on the right-hand germ at `1`. Audit the unrestricted real input of
  `NumberField.Set.primeIdealZetaSum` against its exact convergence domain.
  The sufficient condition `s > 1` is not the exact domain for every subset: finite sets converge
  for every real `s`. Preserve the established density relation and normalization theorems when
  selecting a domain-bearing projection.

- [ ] **Reassess public `finsum`/`finprod` totalization on infinite support.**
  The finite fold over the additive or multiplicative support determines the corresponding sum or
  product, including the empty fold. Require finite support for that operation and remove the
  zero or one fallback on infinite support. An independently defined infinite sum or product needs
  a specification that determines its values on its own domain. Audit `eulerChar` and other
  consumers against their defining mathematical properties.

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
  renames. For a separate total function, record the mathematical source and the defining laws
  that determine its value throughout its proposed domain, including degenerate cases. Remove
  unsupported fallback branches with the selected function's consumer migration. Preserve the
  useful algebraic and analytic theorem families on their valid domains.

- [ ] **Audit totalized operations and fallbacks across the library.**
  Start from the 2026-10-20 inventory in [Audit coverage and limits](#audit-coverage-and-limits).
  Review maintained mathematical declarations one by one, including inherited, private, and
  generated declarations. Inspect elaborated statements, definition bodies, and dependencies to
  find fallback behavior that lacks a source marker. Record the intended domain, specifying
  properties, fallback values where present, and the statements and callers that depend on them.

  Use the fidelity gate above to classify each candidate and record the audit coverage and
  dispositions. Group confirmed public fallbacks into coherent migrations, reusing existing
  operator-family TODOs where applicable. Complete the affected caller migrations under the
  [complete-migration contract](FORK_DESIGN.md#completion) and the
  [official Lean boundary](FORK_DESIGN.md#official-lean-and-operator-fidelity).

## Representation fidelity lint -- total objects whose representation changes the semantics

These are not undefined-operation-to-junk-value defects.  The represented object is mathematically
legitimate, but its inherited instances, indexing convention, or container shape can differ from
the standard object suggested by informal notation.  Keep this lint separate from strict-partiality
migrations: require names, types, documentation, and theorem statements to identify which object is
actually formalized, and provide a literature-supported facade when downstream mathematics uses
another standard representation.

- [ ] **[L] Distinguish zero-encoded element order from an extended order.**
  `orderOf` and `addOrderOf` in `Mathlib/GroupTheory/OrderOfElement.lean:178` encode infinite order as
  zero. `MulAction.period` and `AddAction.period` use the same encoding when only time zero returns.
  `orderOf_dvd_iff_pow_eq_one` and `pow_smul_eq_iff_period_dvd` determine the unique natural
  generator of the return times. For a group element `g` and subgroup `H`, the integer return
  times `{n : ℤ | g ^ n ∈ H}` form an ideal, whose nonnegative generator is `0` when the ideal is
  zero. For a group action, take `H` to be the stabilizer.
  [Delgado, Ventura, and Zakharov, *Relative order and spectrum in free and related groups*, Lemmas 2.5–2.6](https://arxiv.org/html/2105.03798#S2).

  Specify an extended order by the least positive return time when it exists and `⊤` otherwise.
  A natural-valued ordinary order needs `IsOfFinOrder` or `IsOfFinAddOrder`, and a positive period
  needs periodicity as in `Function.minimalPeriod`. If the natural generator is useful as a separate
  public object, identify it by its generator property and name. Keep a zero encoding used only for
  implementation private.

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
  proof. Remove retired presentation declarations rather than generating compatibility entries;
  use canonical declarations or inline transport at call sites. Preserve genuine Tonelli, Fubini,
  measurability, integrability, and change-of-order results; migrate consumers together and
  negative-scan only the hand-maintained duplicate proofs and any names the prototype actually retires.

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
  emit a checkable transport proof and report candidates rather than errors. Use the
  measure/integral pairs above and `Finset.prod_product_right`/`Finset.prod_product_right'`
  as positive controls. Negative controls include
  `ContinuousMap.uncurry` and `Homeomorph.curry` in
  `Mathlib/Topology/CompactOpen.lean:430`--`:471` and `:556`, the multilinear and continuous
  multilinear equivalences in `Mathlib/LinearAlgebra/Multilinear/Curry.lean` and
  `Mathlib/Analysis/Normed/Module/Multilinear/Curry.lean`, categorical closed-structure currying,
  and genuine product, tensor, direct-sum, finite-support, or dependent-sum domains.  Companion
  normalization lemmas for an admitted structured construction inherit that construction's
  exclusion.  Run the lint in audit mode over the inherited tree; consider a diff-scoped warning
  only after all positive and negative controls are classified without false equivalences.

### Visibility hygiene -- reusable facts kept as private helpers

These entries track elementary facts that several modules need but that exist only as private
helpers, so that each consumer keeps its own copy.  Making them public needs a naming and placement
decision; it changes no statement.

- [ ] **[S] Expose the private helpers of the conditional expectation consumers.**
  The bridges between versions and classes of conditional probabilities are private in
  `Mathlib/Probability/Independence/Conditional.lean` (`exists_isCondExp_indicator`,
  `isCondExp_of_condExp_eq`, `forall_isCondExp_mul_iff`, `forall_isCondExp_prod_iff`), and the
  σ-free comparison of two integrable functions through a common version is private in
  `Mathlib/Probability/Independence/ConditionalKernel.lean`
  (`isCondExp_iff_setIntegral_eq_of_isCondExp`); the conditional increments of a martingale are
  private in `Mathlib/Probability/Martingale/Centering.lean` (`Martingale.isCondExp_increment`, the
  converse of `martingale_of_isCondExp_sub_eq_zero_nat`); the strong measurability of
  `stoppedValue f τ` for the σ-algebra of a stopping time with countable range is inline in
  `Mathlib/Probability/Martingale/OptionalSampling.lean`; and the convexity of `‖·‖ ^ p` is inline
  in `IsCondExp.norm_rpow_le`.  Decide names and homes, together with the domain closures
  `HasCondVar.neg` and `HasCondVar.smul` in `Mathlib/Probability/CondVar.lean`, which would let
  `condVar_neg` and `condVar_smul` take one domain proof.  `Conditional.lean` has 1762 lines under
  `set_option linter.style.longFile 1900`; its germ characterizations could move to a new module.
  General measure theory also sits in the conditional expectation files and could move to its own
  homes: the `integrability` tactic and `exists_mem_sigmaFinite_trim_restrict` in
  `Mathlib/MeasureTheory/Function/ConditionalExpectation/Basic.lean`, and the private
  `ae_of_forall_mem_measure_lt_top_ae_restrict` in `CondJensen.lean`.

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

## Audit coverage and limits

Ordinary computational defaults, such as `getD`, `headI`, and parser defaults, are screened out
unless exposed as a checked mathematical inverse or part of a primary mathematical interface.

The 2026-09-11 pass searched the then-current source across 9,063 Lean files (about 1.93
million lines) in `Mathlib/`, `MathlibTest/`, `Archive/`, `Counterexamples/`, and `Wanted/`.
Candidate generation included explicit junk/arbitrary-value language, choice without witnesses,
lossy `.toNat`/`.toReal`/`.unzeroD` conversions, zero/one branches, conditional suprema/infima, `erw`
invocations, and failure lemmas for summability, integrability, differentiability, measurability,
and finiteness.
Selected public definitions were then inspected, but the scan did not prove that every proposed
replacement used the exact mathematical object or domain.

Those repository scans locate assigned values and candidate domain failures. To approve an
independently specified total mathematical object, record its defining properties, show how they
determine its value at each degenerate input, and identify the exact mathematical source.

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

A 2026-10-20 fallback inventory looked for documented fallback values rather than for lexical zero
branches.  It parsed all 8,543 `Mathlib/**/*.lean` files into declaration chunks and recorded, for
each chunk, docstring signals (wording such as junk, fallback, convention, arbitrary, defined as
`0`, otherwise `0`, and we set), name signals (`_undef`, `_of_not_`, `eq_zero_of_not`), and code
signals (an `else` or default branch returning `0`, `1`, `⊥`, `∅`, or `default`, and uses of `getD`,
`toReal`, `untop`, `Classical.choose`, `Classical.epsilon`, `Classical.arbitrary`,
`Function.invFun`, and `Function.extend`).  It also reviewed all 446 private definition-like
declarations outside `Mathlib/Tactic`, `Lean`, `Util`, `Testing`, and `Meta` (190 contain a branch
or choice token and 256 do not), and swept module overviews for statements of junk values.  The
inventory is complete for `MeasureTheory`, `Probability`, and `InformationTheory`, where every
flagged declaration was reviewed; elsewhere it records only public fallbacks that a docstring or
module overview documents, so an undocumented fallback outside those directories is not excluded.
The classes kept as separate deferred audits, namely `x / 0`, `Real.log 0`, `deriv`, `tsum`,
`toReal` and similar conversions, and `Nat.nth`, were not inventoried again.  The scan is lexical
and was not validated against the elaborated environment, and a lemma that holds only because two
fallback values coincide, without a textual marker, cannot be enumerated from source text; the
candidates above that name such lemmas come from docstrings and from proofs that unfold a fallback,
and the pass does not show that no others exist.  Each candidate it produced remains a hypothesis
under the fidelity gate.
