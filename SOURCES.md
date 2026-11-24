# Source Repository Registry

## Purpose and Status

This is the canonical registry for repositories considered as sources for this
curated downstream library. It records source identity, candidate recovery
priorities, provenance, and integration status. Listing a source grants no
authorization to add a Git remote, fetch, copy source, add a dependency, merge,
commit, or publish.

The word "source" is used here for any external repository from which material
might be learned, depended on, or integrated. The Git remote literally named
`upstream` is reserved for the mathlib baseline. Other source repositories use
distinct, stable remote names when a later task explicitly adds them.

## Repository Roles

### Destination

- Repository: `KiringYJ/mathlib-fidelity`
- Local remote: `origin`
- URL: `https://github.com/KiringYJ/mathlib-fidelity.git`
- Role: publication destination for this curated fork
- Push policy: push only with explicit authorization

### Active baseline source

- Repository: `leanprover-community/mathlib4`
- Local remote: `upstream`
- URL: `https://github.com/leanprover-community/mathlib4.git`
- Upstream development reference: `upstream/master`
- History relationship: shared ancestry through the mathlib `v4.34.0` rebase,
  with future merges extending the published Fidelity history
- Integration mode: batched merges of official stable mathlib release tags
  into local `main`, with API repair and final-state validation
- Reconciliation state: Git ancestry records the integrated releases. See the
  [maintenance procedure](AI_AGENT_PROJECT.md#mathlib-baseline-reconciliation-workflow).
- License evidence: the current source tree contains the Apache License 2.0 in
  `LICENSE`; recheck the exact source revision and any file-specific notices at
  each import boundary
- Status: active

### Official Lean toolchain dependency

- Repository: `leanprover/lean4`
- URL: `https://github.com/leanprover/lean4.git`
- Selected release: [`v4.34.0`](https://github.com/leanprover/lean4/releases/tag/v4.34.0),
  commit `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`. `lean-toolchain` is
  authoritative for the current official release selection.
- Integration mode: unchanged official compiler, kernel, standard libraries,
  and core metaprogramming infrastructure; no maintained toolchain fork
- Semantic boundary: retain legitimate core carriers, including `Rat`; exclude
  unfaithful operators from fork mathematical definitions and statements under
  `FORK_DESIGN.md`. Remove replaceable proof and automation uses too. Unavoidable
  official-toolchain-owned dependencies may remain proof-only with their
  declarations and faithful boundary recorded. The fork owns its operator APIs
  and semantic adapters, not a replacement Lean distribution.
- License evidence: the pinned source root `LICENSE` is Apache License 2.0;
  its rational and Grind source headers carry the same license.
  Preserve their existing authorship and all applicable distribution notices.
- Status: active official dependency. The
  [changelog](CHANGELOG.md#fidelity-changes) records the checked arithmetic
  migrations on this toolchain. See
  [operator-fidelity validation](.github/CI.md#operator-fidelity) for the
  audit scope.

## Candidate Sources

The 2026-11-24 review checked GitHub repository identities and default refs.
It screened the maintainer's public stars alongside the mathlib downstream
inventory and public formalization catalogues.
[GitHub Stars](https://github.com/KiringYJ?tab=stars),
[mathlib downstream inventory](scripts/downstream_repos.yml),
[Lean Reservoir](https://reservoir.lean-lang.org/),
[Palomar Registry](https://palomar-registry.org/).

The scope notes identify material to investigate and flag known review gaps.
Before promoting a candidate to `accepted`, record its full immutable source
commit and complete the intake record below, including proof, overlap,
provenance, and license checks. Maintainers schedule intake within the
available audit and migration capacity.

For a first Lean 4 intake audit, compare `add-combi` and `apap` together, then
select a self-contained slice of `DynamicalSystems`, `gibbs-measure`, or
`StacksCore`. Each has a concrete theory interface to compare with the
maintained library before estimating the port.

### Lean 3 preservation and reconstruction leads

The priorities below are provisional. Use the
[contribution guide](.github/CONTRIBUTING.md#recovery-modes) to assess maintained
descendants, compare theorem coverage, and choose a recovery mode.

#### Priority A -- port pilot and reconstruction candidates

- [adamtopaz/lean-acl-pairs](https://github.com/adamtopaz/lean-acl-pairs) (`master`).
  Bounded port pilot for alternating pairs and valuation rings. Check for a
  maintained Lean 4 descendant, audit the main and converse statements and
  their proofs, and compare them with the current valuation and linear-algebra
  APIs.
- [leanprover-community/lean-liquid](https://github.com/leanprover-community/lean-liquid) (`master`).
  Flagship reconstruction candidate for the Liquid Tensor Experiment. Map the
  blueprint and theorem dependencies, including `src/for_mathlib`, to current
  condensed and homological-algebra declarations. The acceptance target is an
  audited current theorem corresponding to the historical
  `liquid_tensor_experiment`.
- [leanprover-community/lean-perfectoid-spaces](https://github.com/leanprover-community/lean-perfectoid-spaces) (`master`).
  Compare the Huber, adic-space, and perfectoid-space layers declaration by
  declaration with current valuation, topology, and perfectoid infrastructure.
  Compare AINTLIB's Lean 4 adic-space development and the
  [current perfectoid modules](Mathlib/RingTheory/Perfectoid/) before defining
  a reconstruction scope.

#### Priority B -- theorem-level overlap audits

- [dagurtomas/lean-solid](https://github.com/dagurtomas/lean-solid) (`master`).
  Compare the fork-specific `src/solid/` declarations with `profiniteSolid`,
  solidification, and `CondensedMod.IsSolid`. Check the open solidity results
  and the general-ring boundary documented in
  [Mathlib.Condensed.Solid](Mathlib/Condensed/Solid.lean).
- [b-mehta/topos](https://github.com/b-mehta/topos) (`master`).
  Map named results on cartesian and locally cartesian closed categories,
  toposes, Lawvere--Tierney topologies, and sheafification to current category,
  site, Grothendieck-topology, and sheaf declarations.

#### Existing Lean 4 descendant

- [ianklatzco/flypitch](https://github.com/ianklatzco/flypitch) (`master`).
  Start with the `flypitch4` development and its validation records. Audit its
  trusted proof boundary and correspondence with the original Lean 3 source.

### Established mathlib-downstream leads

These Lean 4 libraries cover sustained developments in mathematics and formal
computer science. Compare their smallest reusable modules with the maintained
APIs before selecting a port.

| Candidate | Scope to investigate | Observed default ref |
| --- | --- | --- |
| [ImperialCollegeLondon/FLT](https://github.com/ImperialCollegeLondon/FLT) | Fermat's Last Theorem and supporting algebra, number theory, geometry, and representation theory | `main` |
| [leanprover-community/flt-regular](https://github.com/leanprover-community/flt-regular) | Fermat's Last Theorem for regular primes | `master` |
| [fpvandoorn/carleson](https://github.com/fpvandoorn/carleson) | Carleson operators on doubling metric-measure spaces | `master` |
| [teorth/pfr](https://github.com/teorth/pfr) | Polynomial Freiman--Ruzsa formalization | `master` |
| [leanprover-community/add-combi](https://github.com/leanprover-community/add-combi) | Balog--Szemerédi--Gowers and additive VC dimension. Compare finite convolution and additive energy with Mathlib and PFR. [Module inventory](https://github.com/leanprover-community/add-combi/blob/master/AddCombi.lean) | `master` |
| [YaelDillies/apap](https://github.com/YaelDillies/apap) | Kelley--Meka development. Audit discrete Fourier, finite `Lp`, and almost-periodicity lemmas against `add-combi` and PFR. [Module inventory](https://github.com/YaelDillies/apap/blob/master/APAP.lean) | `master` |
| [YaelDillies/cam-combi](https://github.com/YaelDillies/cam-combi) | Cambridge combinatorics developments. Compare LYM and graph-density lemmas with Mathlib, then audit the Littlewood--Offord and random-graph modules. [Module inventory](https://github.com/YaelDillies/cam-combi/blob/master/CamCombi.lean) | `master` |
| [AlexKontorovich/PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) | prime number theorem and analytic-number-theory infrastructure | `main` |
| [kbuzzard/ClassFieldTheory](https://github.com/kbuzzard/ClassFieldTheory) | class field theory | `main` |
| [n-yamaguchi-0729/ClassFieldTheory](https://github.com/n-yamaguchi-0729/ClassFieldTheory) | separate local and global class field theory development. Start with the finite abelian local Artin map and its norm-kernel theorem and compare the two class field theory APIs. [Theorem inventory](https://github.com/n-yamaguchi-0729/ClassFieldTheory#main-results) | `main` |
| [leanprover-community/sphere-eversion](https://github.com/leanprover-community/sphere-eversion) | existing Lean 4 port to audit for sphere eversion and differential topology | `master` |
| [thefundamentaltheor3m/Sphere-Packing-Lean](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean) | sphere packing in dimension eight | `main` |
| [emilyriehl/infinity-cosmos](https://github.com/emilyriehl/infinity-cosmos) | higher category theory and infinity-cosmoses | `main` |
| [teorth/equational_theories](https://github.com/teorth/equational_theories) | equational theories and universal algebra | `main` |
| [Paul-Lez/PersistentDecomp](https://github.com/Paul-Lez/PersistentDecomp) | decomposition of persistence modules | `master` |
| [RemyDegenne/brownian-motion](https://github.com/RemyDegenne/brownian-motion) | Brownian motion and stochastic-analysis infrastructure | `master` |
| [formal-applied-math/formal-mathfin](https://github.com/formal-applied-math/formal-mathfin) | stochastic calculus and mathematical finance. Compare the Itô integral and Girsanov interfaces with `brownian-motion`, and check the exact scope of reduced benchmark statements. [Coverage and proof status](https://github.com/formal-applied-math/formal-mathfin/blob/main/README.md) | `main` |
| [YaelDillies/gibbs-measure](https://github.com/YaelDillies/gibbs-measure) | Gibbs specifications and measures. Compare proper kernels, composition, and conditional expectation with `Mathlib/Probability/Kernel`, then audit a specification theorem. [Specification module](https://github.com/YaelDillies/gibbs-measure/blob/main/GibbsMeasure/Specification.lean) | `main` |
| [YijunYuan/HarderNarasimhan](https://github.com/YijunYuan/HarderNarasimhan) | Harder--Narasimhan games and filtrations. The earlier `paper` branch remains available | `master` |
| [YaelDillies/toric](https://github.com/YaelDillies/toric) | toric varieties | `master` |
| [Whysoserioushah/BrauerGroup](https://github.com/Whysoserioushah/BrauerGroup) | Brauer groups | `main` |
| [mcdoll/DispersiveEquations](https://github.com/mcdoll/DispersiveEquations) | nonlinear dispersive equations | `master` |
| [mcdoll/DynamicalSystems](https://github.com/mcdoll/DynamicalSystems) | Carathéodory ODE theory and LaSalle/Lyapunov stability. Compare solution and flow interfaces with `Mathlib/Analysis/ODE`, then audit one stability theorem. [Module inventory](https://github.com/mcdoll/DynamicalSystems/blob/main/DynamicalSystems.lean) | `main` |
| [Ivan-Sergeyev/seymour](https://github.com/Ivan-Sergeyev/seymour) | Seymour decomposition for regular matroids | `main` |
| [leanprover-community/physlib](https://github.com/leanprover-community/physlib) | physics-specific formalization library | `master` |
| [LionSR/QICLean](https://github.com/LionSR/QICLean) | quantum channels, entropy, and spectral theory, extracted from TNLean. Compare density matrices and completely positive maps with Physlib before selecting the channel lemmas. [Module inventory](https://github.com/LionSR/QICLean/blob/main/QICLean.lean) | `main` |
| [lecopivo/SciLean](https://github.com/lecopivo/SciLean) | scientific computing and applied-mathematics infrastructure | `master` |
| [girving/series](https://github.com/girving/series) | truncated power-series arithmetic. Compare coefficient and derivative specifications with Mathlib power series and audit the arithmetic supplied by [girving/interval](https://github.com/girving/interval). [Series operations](https://github.com/girving/series#readme) | `main` |
| [LeanMachineLearning/LML](https://github.com/LeanMachineLearning/LML) | Bregman divergence, subgradients, and KL data processing. Check `ForMathlib` modules against the analysis and information-theory APIs and `lean-stat-learning-theory`. [Module inventory](https://github.com/LeanMachineLearning/LML/blob/main/LeanMachineLearning.lean) | `main` |
| [vihdzp/combinatorial-games](https://github.com/vihdzp/combinatorial-games) | Grundy theory, Nim, and canonical forms. Compare terminating-game sums with `Prod.GameAdd` and check where loopy games need separate definitions. [Module inventory](https://github.com/vihdzp/combinatorial-games/blob/master/CombinatorialGames.lean) | `master` |
| [leanprover/cslib](https://github.com/leanprover/cslib) | computer science library. Compare finite-automaton language theorems with `Mathlib/Computability` and evaluate larger developments as downstream work. [Module inventory](https://github.com/leanprover/cslib/blob/main/Cslib.lean) | `main` |
| [Verified-zkEVM/ArkLib](https://github.com/Verified-zkEVM/ArkLib) | interactive oracle reductions, coding theory, and FRI. Compare Reed--Solomon code and distance APIs before auditing the [adaptive FRI transcript bound](https://github.com/Verified-zkEVM/ArkLib/blob/main/ArkLib/ProofSystem/Fri/Spec/AdaptiveSoundness.lean) | `main` |

### Paper-scale and specialty leads

| Candidate | Scope to investigate | Observed default ref |
| --- | --- | --- |
| [b-mehta/AharoniKorman](https://github.com/b-mehta/AharoniKorman) | counterexample to the Aharoni--Korman conjecture | `master` |
| [b-mehta/exponential-ramsey](https://github.com/b-mehta/exponential-ramsey) | exponential diagonal Ramsey upper bound | `main` |
| [b-mehta/ABC-Exceptions](https://github.com/b-mehta/ABC-Exceptions) | quantitative bounds for the abc exceptional set | `main` |
| [teorth/sendov](https://github.com/teorth/sendov) | Sendov and Phelps--Rodriguez statements and proofs | `master` |
| [alonamaloh/schoenflies-lean](https://github.com/alonamaloh/schoenflies-lean) | Jordan--Schoenflies theorem | `main` |
| [ARGO-LABORATORY/Wolstenholme_1862](https://github.com/ARGO-LABORATORY/Wolstenholme_1862) | Wolstenholme theorem | `main` |
| [0stellensatz/MassFormula](https://github.com/0stellensatz/MassFormula) | archived formalization of Serre mass formulas for totally ramified local-field extensions and supporting finiteness/convergence infrastructure | `master` |
| [ashvin-swaminathan/quartic-invariant](https://github.com/ashvin-swaminathan/quartic-invariant) | quartic invariant of odd-degree binary forms; distinguish paper claims, Lean statements, and computational verification | `main` |
| [karlesmarin/godsil-gutman-lean](https://github.com/karlesmarin/godsil-gutman-lean) | matching polynomials, graph spectra, determinants, and real-rootedness infrastructure; audit theorem inventory and `MathlibPR` overlap | `main` |
| [catskillsresearch/scott1964](https://github.com/catskillsresearch/scott1964) | Scott's measurement structures and linear inequalities; audit source correspondence, separately labelled modern extensions, and comparator proof-hole boundaries | `main` |
| [yawara/odd-order](https://github.com/yawara/odd-order) | Feit--Thompson odd-order theorem; independently audit the claimed proof boundary | `main` |
| [LionSR/TNLean](https://github.com/LionSR/TNLean) | tensor networks and the fundamental theorem of matrix product states, developed on QICLean | `main` |
| [a-dangelo/Lean-AG](https://github.com/a-dangelo/Lean-AG) | algebraic geometry, including scheme and Krull-dimension material | `main` |
| [mo271/FormalBook](https://github.com/mo271/FormalBook) | proofs from *Proofs from THE BOOK*, with proof-faithfulness as a comparison point | `main` |
| [sinhp/HoTTLean](https://github.com/sinhp/HoTTLean) | metatheory of HoTT and models of dependent type theory | `master` |
| [oliver-butterley/SpectralThm](https://github.com/oliver-butterley/SpectralThm) | spectral theorem for bounded normal operators | `main` |
| [FormalizedFormalLogic/Foundation](https://github.com/FormalizedFormalLogic/Foundation) | mathematical logic, including completeness and cut elimination | `master` |
| [YuanheZ/lean-stat-learning-theory](https://github.com/YuanheZ/lean-stat-learning-theory) | statistical learning theory and probability infrastructure | `main` |
| [lean-dojo/LeanMillenniumPrizeProblems](https://github.com/lean-dojo/LeanMillenniumPrizeProblems) | Millennium Problem statements and supporting infrastructure; do not treat the collection as proofs of the problems | `main` |
| [sven-manthe/A-formalization-of-Borel-determinacy-in-Lean](https://github.com/sven-manthe/A-formalization-of-Borel-determinacy-in-Lean) | Martin's Borel determinacy via Gale--Stewart games. Use the [author's list of upstreamed modules](https://github.com/sven-manthe/A-formalization-of-Borel-determinacy-in-Lean/blob/master/README.org) to identify the remaining proof and reusable prerequisites | `master` |
| [abenenson/rellich-kondrachov](https://github.com/abenenson/rellich-kondrachov) | compact Sobolev embedding on compact Riemannian manifolds. Audit the Euclidean `L²` compactness lemmas and then the manifold volume and Sobolev interfaces. [Theorem and build notes](https://github.com/abenenson/rellich-kondrachov#readme) | `main` |
| [math-xmum/Brouwer](https://github.com/math-xmum/Brouwer) | Scarf's lemma, simplex/product Brouwer, and finite mixed Nash equilibrium. Map the simplex and fixed-point APIs before choosing an Archive scope. [Proof outline](https://github.com/math-xmum/Brouwer#readme) | `main` |
| [harfe/fixed-point-theorems-lean4](https://github.com/harfe/fixed-point-theorems-lean4) | cubical Sperner and Brouwer plus Kakutani. Compare the Brouwer layer with `math-xmum/Brouwer` and audit the set-valued fixed-point result first. [Theorem inventory](https://github.com/harfe/fixed-point-theorems-lean4#readme) | `main` |
| [kim-em/KnuthClaudeLean](https://github.com/kim-em/KnuthClaudeLean) | Hamiltonian arc decomposition of the odd cube digraph. Compare with Mathlib's digraph definitions and check the [challenge statement](https://github.com/kim-em/KnuthClaudeLean/blob/master/Challenge.lean) for an Archive port | `master` |
| [vltanh/lean4-moving-sofa](https://github.com/vltanh/lean4-moving-sofa) | Baek's Gerver-sofa optimality and source-reported uniqueness and stability. Audit the area and motion definitions and the bridge to `formal-conjectures`. [Scope and verification](https://github.com/vltanh/lean4-moving-sofa#readme) | `main` |
| [vltanh/lean4-ambidextrous-sofa](https://github.com/vltanh/lean4-ambidextrous-sofa) | source-reported optimality and uniqueness of Romik's ambidextrous sofa. Audit the two-motion statement and reuse the ordinary-sofa infrastructure. [Challenge statement](https://github.com/vltanh/lean4-ambidextrous-sofa/blob/main/Challenge.lean) | `main` |
| [mathlib-initiative/sum_product](https://github.com/mathlib-initiative/sum_product) | real sum-product counterexample conditional on `MartinetTotallyRealTowers`. Audit that hypothesis and the number-field infrastructure via the [statement-to-declaration map](https://github.com/mathlib-initiative/sum_product/blob/main/formalization.yaml) | `main` |
| [felixpernegger/pibase-lean](https://github.com/felixpernegger/pibase-lean) | Lean formalizations of π-Base topology implications. Compare source definitions with Mathlib before selecting a theorem or counterexample. [Coverage dashboard](https://felixpernegger.github.io/pibase-lean/) | `master` |
| [platypii/integer-mult-bounds-lean](https://github.com/platypii/integer-mult-bounds-lean) | source-reported sub-`n log n` integer multiplication on `Turing.FinTM2`. Audit encodings, the time bound, and the trusted computational boundary. [Theorem scope](https://github.com/platypii/integer-mult-bounds-lean#readme) | `master` |
| [smmercuri/zeta](https://github.com/smmercuri/zeta) | finite-height zeta zero certification and simplicity. Start with the small-height kernel target and audit zero counting, interval bounds, and the generated certificates. [Main theorems](https://github.com/smmercuri/zeta/blob/main/Zeta/Main.lean) | `main` |
| [zksecurity/simple-rbr-fri](https://github.com/zksecurity/simple-rbr-fri) | simplified FRI round-by-round soundness and perfect completeness. Compare with ArkLib, preserving the unformalized instantiation lemma noted in the [README](https://github.com/zksecurity/simple-rbr-fri#status) | `main` |
| [Harry-Tech-Guide/Lean-4-Four-Color-Theorem-Formalization](https://github.com/Harry-Tech-Guide/Lean-4-Four-Color-Theorem-Formalization) | combinatorial Four Color Theorem over orientable hypermaps. Audit the bridge to planar graph coloring and the certified computation at the [Palomar-registered revision](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-20-000011&version=1) | `master` |

### Recent and AI-assisted leads

Claims made by these repositories require the same independent mathematical
and provenance review as any other source. Compilation, generated metadata, or
a repository's own clean-status label is not an admission verdict.

| Candidate | Scope to investigate | Observed default ref |
| --- | --- | --- |
| [merely-true/merely-true](https://github.com/merely-true/merely-true) | permissive AI-generated Lean library with automatic CI-based merging and no manual human review; independently audit statement and definition fidelity, provenance, maintenance stability, overlap, and reusable API before selecting material | `main` |
| [TauCetiProject/TauCeti](https://github.com/TauCetiProject/TauCeti) | AI-authored integrated Lean library directed by human roadmaps and adversarial AI review; independently audit definitions, statements, review evidence, attribution, overlap, and adaptation to this fork's design | `main` |
| [mattrobball/BridgelandStability](https://github.com/mattrobball/BridgelandStability) | AI-assisted Lean 4 formalization of Bridgeland stability conditions and claimed paper-result coverage; independently audit statement correspondence, trusted boundary, axioms, `sorry`s, and generated artifacts | `main` |
| [marcmorningstar/lean4-ergodic-theory](https://github.com/marcmorningstar/lean4-ergodic-theory) | self-described smooth ergodic theory centered on Oseledets, with entropy and Livšic developments; audit theorem coverage and current-library overlap | `main` |
| [will1491/RiemannDynamics](https://github.com/will1491/RiemannDynamics) | ongoing complex-dynamics, Riemann-surface, Teichmüller, and hyperbolic-geometry development; audit headline claims and vendored dependencies | `main` |
| [MerLeanProver/ACMaxConjecture](https://github.com/MerLeanProver/ACMaxConjecture) | claimed ACMAX graph-conjecture formalization; independently audit source correspondence, exports, comparator, and trusted boundary | `main` |
| [tadamcz/mean-value-problem](https://github.com/tadamcz/mean-value-problem) | AI-assisted claimed disproof of Smale's mean-value conjecture with `K = 1`; audit exact negation, witness, and comparator boundary | `main` |
| [tadamcz/erdos548](https://github.com/tadamcz/erdos548) | AI-assisted claimed proof of Erdős Problem 548; audit source statement, mathematical fidelity, comparator, and provenance | `main` |
| [tadamcz/erdos571](https://github.com/tadamcz/erdos571) | AI-assisted claimed proof of Erdős Problem 571; audit source statement, mathematical fidelity, comparator, and provenance | `main` |
| [Yuren-Tang/erdos-306](https://github.com/Yuren-Tang/erdos-306) | claimed proof of Erdős Problem 306 conditional on two named Rosser--Schoenfeld axioms; preserve and independently audit that boundary | `main` |
| [openai/NavierStokesAndEuler](https://github.com/openai/NavierStokesAndEuler) | Navier--Stokes and Euler statement/proof artifacts | `main` |
| [openai/ten-proofs](https://github.com/openai/ten-proofs) | collection of ten mathematics and theoretical-CS formalizations | `main` |
| [openai/cdc-lean](https://github.com/openai/cdc-lean) | cycle double cover formalization | `main` |
| [anthropics/formal-math](https://github.com/anthropics/formal-math) | collection of separately structured formal-mathematics projects | `main` |
| [anthropics/fermats-last-theorem](https://github.com/anthropics/fermats-last-theorem) | claimed Fermat's Last Theorem proof; independently verify the statement and trusted proof boundary | `main` |
| [openai/PrimeGaps186](https://github.com/openai/PrimeGaps186) | prime-gap formalization; preserve and verify any conditional axioms rather than presenting it as unconditional | `main` |
| [openai/LongGapsBetweenPrimes](https://github.com/openai/LongGapsBetweenPrimes) | long gaps between primes | `master` |
| [Vilin97/Autoformalization](https://github.com/Vilin97/Autoformalization) | separate Vlasov--Maxwell--Landau and Grothendieck-vanishing packages with their own toolchains and reports | `main` |
| [gotrevor/lean-gallery](https://github.com/gotrevor/lean-gallery) | curated formalization collection; independently verify each included module | `main` |
| [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures) | statement and scaffold corpus; use primarily as a discovery source unless proofs are separately established | `main` |
| [ImperialCollegeLondon/AnnalsChallenge](https://github.com/ImperialCollegeLondon/AnnalsChallenge) | formalized Annals theorem statements with proof obligations; catalogue rather than completed proof source | `main` |
| [AxiomMath/Stacks](https://github.com/AxiomMath/Stacks) | Stacks Project formalizations. Start with a reviewed `StacksCore` tag such as [0H7K, common field extensions](https://github.com/AxiomMath/Stacks/blob/main/StacksCore/RingTheory/Flat/FaithfullyFlat/Basic.lean), compare with Mathlib, and track the review status of `StacksFrontier` separately | `main` |
| [AxiomMath/ClusterAlgebras](https://github.com/AxiomMath/ClusterAlgebras) | formalization of results from Fomin--Williams--Zelevinsky. Start with the quiver and exchange-matrix mutation correspondence, and audit the hypotheses of the finite-type results separately. [Challenge statements](https://github.com/AxiomMath/ClusterAlgebras/blob/main/Challenge/Basic.lean) | `main` |
| [AxiomMath/CFSG](https://github.com/AxiomMath/CFSG) | source-reported classification of finite simple groups on TauCeti's list. Audit the exported statement and the dependency chain through generated certificates before scoping group-theory reuse. [Project and build notes](https://github.com/AxiomMath/CFSG#readme) | `main` |
| [AxiomMath/CFSGCorollary](https://github.com/AxiomMath/CFSGCorollary) | two-generation of finite simple groups. Audit generation lemmas for the individual families and distinguish the conditional theorem from the export using CFSG. [Exported statements](https://github.com/AxiomMath/CFSGCorollary#readme) | `main` |
| [CBirkbeck/AINTLIB](https://github.com/CBirkbeck/AINTLIB) | AI-reviewed library that permits `sorry`. Compare Huber rings and adic spectra with the Lean 3 perfectoid project and current valuation theory, then audit theorem dependencies individually. [Adic-space development](https://github.com/CBirkbeck/AINTLIB/tree/main/projects/AdicSpaces) | `main` |
| [leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis) | community cleanup of Alpöge's RH and Dirichlet GRH submission. Compare the published theorem roots, Comparator evidence, and analytic-number-theory overlap with PNT+. Reference-only pending license review. [Preserved submission](https://github.com/homeowmorphism/riemann-hypothesis-original) | `main` |
| [mccorvie/riemann-masullo](https://github.com/mccorvie/riemann-masullo) | Hecke L-function formalization and audit of Masullo's draft. Trace isolated reusable lemmas against the [errata](https://github.com/mccorvie/riemann-masullo/blob/main/ERRATA.md) and [open proof obligations](https://github.com/mccorvie/riemann-masullo/issues/7349) | `main` |
| [math-inc/strongpnt](https://github.com/math-inc/strongpnt) | strong PNT development. Compare the zero-free region, error term, and complex-analysis lemmas with PNT+ and Mathlib. Reference-only pending license review. [Zero-free-region module](https://github.com/math-inc/strongpnt/blob/main/StrongPNT/PNT4_ZeroFreeRegion.lean) | `main` |
| [tristanbuckmaster/navier-stokes](https://github.com/tristanbuckmaster/navier-stokes) | Alpöge--Buckmaster conditional blow-up results. The source leaves certificate data and its external computation outside the Lean package. Audit isolated PDE lemmas and retain the certificate hypotheses. Reference-only pending license review. [Formal statements and paper correspondence](https://github.com/tristanbuckmaster/navier-stokes/blob/main/lean/README.md) | `main` |
| [yang-mills-group/OpenAI-YM-20261028](https://github.com/yang-mills-group/OpenAI-YM-20261028) | pure four-dimensional Yang--Mills construction. Scope the exact `YangMills.jointExistence` predicate and dependency graph before choosing reusable analytic modules. [Independent assessment and comparator evidence](https://github.com/yang-mills-group/YM/blob/main/submissions/openai-20261028/evidence/README.md), [exposition and source map](https://github.com/hairer/humanise-yang-mills) | `main` |
| [andersonwu2000/Asterism-formalizations](https://github.com/andersonwu2000/Asterism-formalizations) | cocircular central-configuration classification and five-body finiteness. Assess as separate Archive candidates with per-package licenses, toolchains, and theorem statements. [Project inventory and licensing](https://github.com/andersonwu2000/Asterism-formalizations#readme) | `main` |

### Reformalization references

These sources support comparisons across proof assistants under the
[reformalization policy](.github/CONTRIBUTING.md#recovery-modes).

| Reference | Scope to investigate | Observed default ref |
| --- | --- | --- |
| [hol-light-family/Flyspeck](https://github.com/hol-light-family/Flyspeck) | maintained HOL Light Kepler proof. Map the [main theorem's archive and tame-graph assumptions](https://github.com/hol-light-family/Flyspeck/blob/main/text_formalization/general/the_kepler_conjecture.hl) and the [Isabelle classification](https://isa-afp.org/entries/Flyspeck-Tame.html). The [partial Lean development](https://github.com/lispc/kepler-conjecture-lean4) reports remaining `sorryAx` and native evaluation dependencies | `main` |
| [agda/cubical](https://github.com/agda/cubical) | [Cubical Agda computation of π₄(S³)](https://github.com/agda/cubical/blob/master/Cubical/Papers/Pi4S3-JournalVersion.agda). Assess the higher-inductive and cubical foundations before scoping a Lean reformalization | `master` |
| [rocq-community/fourcolor](https://github.com/rocq-community/fourcolor) | [Gonthier's plane-map Four Color Theorem](https://github.com/rocq-community/fourcolor/blob/master/theories/proof/fourcolor.v). Compare its map representation and certified computation with the Lean hypermap development above | `master` |

### Discovery feeds

These repositories are indexes or aggregates, not proof authorities. Use them
to find underlying projects, then resolve and audit the original repository and
revision before adding it as a candidate source.

| Feed | Use | Observed default ref |
| --- | --- | --- |
| [dzackgarza/formalization-corpus](https://github.com/dzackgarza/formalization-corpus) | searchable cross-repository formalization index for discovery and reuse checks | `main` |
| [LeanPool/lean-pool](https://github.com/LeanPool/lean-pool) | aggregate of formalization projects with source provenance. Follow each entry to its original source. The previous `Vilin97/lean-pool` entry now identifies a fork of this repository | `main` |
| [leanprover-community/LeanProject](https://github.com/leanprover-community/LeanProject) | template with a [catalogue of downstream projects](https://github.com/leanprover-community/LeanProject#selected-projects-using-this-template) | `main` |
| [leanprover/reservoir](https://github.com/leanprover/reservoir) | [public Lean package index](https://reservoir.lean-lang.org/) for locating package sources and releases | `master` |
| [PalomarRegistry/PalomarWeb](https://github.com/PalomarRegistry/PalomarWeb) | [Palomar Registry](https://palomar-registry.org/) entries point to pinned projects and review evidence. The [Palomar template](https://github.com/PalomarRegistry/PalomarTemplate) documents the `formalization.yaml` metadata | `main` |
| [openai/math](https://github.com/openai/math) | manuscripts and Lean artifacts. Use the [per-result formalization catalogue](https://github.com/openai/math/blob/main/lean/formalization.yaml) to locate statements and verification configurations | `main` |
| [pi-base/data](https://github.com/pi-base/data) | topology counterexamples and implication references. Compare the underlying definitions and cited proofs with `pibase-lean` | `main` |
| [isabelle-prover/mirror-afp-devel](https://github.com/isabelle-prover/mirror-afp-devel) | development mirror of the [Isabelle Archive of Formal Proofs](https://isa-afp.org/). Follow the selected entry's authorship, dependencies, and license for reformalization | `master` |

### Resolved discovery leads

- **Weil converse theorem.** The identified repository currently contains the
  template project and example. Revisit when theorem modules are published.
  [CBirkbeck/WeilConverse](https://github.com/CBirkbeck/WeilConverse).
- **Dirichlet nonvanishing.** The archived project records its upstreaming.
  `DirichletCharacter.LFunction_ne_zero_of_one_le_re` is in the maintained
  Mathlib tree. [Archived project](https://github.com/CBirkbeck/DirichletNonvanishing),
  [current theorem module](Mathlib/NumberTheory/LSeries/Nonvanishing.lean).
- **FRI soundness.** The original LeanProject link returned 404. The public
  blueprint for BCIKS20 Theorem 8.2 has template Lean files. ArkLib and
  `simple-rbr-fri` above provide substantive code at different scopes.
  [pitmonticone/FRISoundness](https://github.com/pitmonticone/FRISoundness).

## Required Intake Record

Promote a candidate to `accepted`, or add an active source, only after recording
all applicable fields:

```text
Source ID:
Repository owner/name:
Canonical URL:
Local remote name: none | <name>
Source revision:
Tracked refs:
History relationship: shared | unrelated | unknown
License and version:
License evidence at revision:
NOTICE / attribution obligations:
Third-party or per-file exceptions:
Intended mode: reference-only | dependency | cherry-pick | source-port
Mathematical scope:
In-tree destination modules (if applicable):
Proof status: verified | conditional | incomplete | unknown
Axioms / sorry / generated-code status:
Overlap and deduplication plan:
Provenance mapping:
Migration notes:
Verification:
Status: candidate | accepted | migrating | integrated | declined | paused
```

An `accepted` record means selected for integration; it does not mean the
source's current API is canonical. An `integrated` record requires completed
provenance, migration, and verification evidence.

The `migrating` status records work in progress, not an accepted transitional
API. Integration follows the complete-migration contract in `FORK_DESIGN.md`:
complete the selected scope without compatibility layers, and identify any
independently deferred foundational issues together with their proved boundaries.

## Intake Procedure

1. Identify the exact repository and immutable source revision.
2. Inspect the license at that revision, per-file headers, bundled third-party
   material, and any `NOTICE` or attribution requirements. If permission is
   absent, unclear, or incompatible, keep the source reference-only pending a
   separate license review.
3. Audit the mathematical statements, assumptions, proof dependencies, axioms,
   `sorry`s, generated artifacts, and fidelity to the cited mathematics.
4. Search the maintained tree and other candidates for equivalent declarations
   before importing another version of the same concept.
5. Choose the integration mode. For shared history, review coherent commits
   for selective cherry-pick or porting. For an independent history, select
   a reviewed source port or a Lake dependency on an independently versioned
   library. Reference-only entries record the source without importing code.
   Remote discovery alone grants no integration authority. For in-tree work,
   record the proposed destination modules and any split between `Mathlib/`
   and `Archive/` under the
   [placement policy](FORK_DESIGN.md#mathematical-scope-and-placement).
6. Record file- or declaration-level provenance and preserve applicable notices
   before editing the imported material.
7. Integrate accepted content in the recorded mode. For in-tree work, reuse
   the canonical mathematical API and follow the conventions for the selected
   destination.
8. Run mathematical and technical review at the final integrated state, then
   update the record to `integrated` only when the evidence is complete.

## License References

License compatibility must be decided for the exact source and distribution;
this checklist is not a complete legal determination.

- [Apache License 2.0, section 4](https://www.apache.org/licenses/LICENSE-2.0.html)
  states its redistribution conditions, including providing the license,
  marking modified files, retaining applicable notices, and carrying forward
  applicable `NOTICE` attribution.
- [GitHub's repository licensing documentation](https://docs.github.com/en/repositories/managing-your-repositorys-settings-and-features/customizing-your-repository/licensing-a-repository)
  explains that public visibility without a license does not grant general
  permission to reproduce, distribute, or create derivative works.
