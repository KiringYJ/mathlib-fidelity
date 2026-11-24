# Source Repository Registry

## Purpose and Status

This registry records external source identities, recovery priorities, and
intake provenance. Track migration scope, status, and completion criteria in
[GitHub Issues](https://github.com/KiringYJ/mathlib-fidelity/issues).

Adding remotes or dependencies, fetching source, copying material, merging,
committing, and publishing require separate authorization. The `upstream`
remote is reserved for the mathlib baseline. Additional remotes use distinct,
stable names.

## Repository Roles

### Destination

`origin` publishes this fork to
[KiringYJ/mathlib-fidelity](https://github.com/KiringYJ/mathlib-fidelity).

### Active baseline source

`upstream/master` tracks
[leanprover-community/mathlib4](https://github.com/leanprover-community/mathlib4).
The `v4.34.0` rebase established the shared baseline. Later stable release
merges are recorded in Git ancestry. The source root `LICENSE` is Apache 2.0.
Recheck the license and file notices at each import revision.
[Baseline reconciliation](AI_AGENT_PROJECT.md#mathlib-baseline-reconciliation-workflow)

### Official Lean toolchain dependency

[`lean-toolchain`](lean-toolchain) selects the official
[`leanprover/lean4` release `v4.34.0`](https://github.com/leanprover/lean4/releases/tag/v4.34.0)
at `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`. Its root license and rational
and Grind source headers use Apache 2.0. Preserve applicable notices and
authorship. See the
[toolchain boundary](FORK_DESIGN.md#official-lean-and-operator-fidelity),
[operator audit](.github/CI.md#operator-fidelity), and
[arithmetic changelog](CHANGELOG.md#fidelity-changes).

## Candidate Sources

Discovery sources include the [mathlib downstream inventory](scripts/downstream_repos.yml),
[Lean Reservoir](https://reservoir.lean-lang.org/), and the
[Palomar Registry](https://palomar-registry.org/).

Default refs are for discovery. Complete the [intake record](#required-intake-record)
at an immutable revision before accepting a candidate. Linked issues record
the scoped deliverable and any upstream readiness conditions. Continuously
developed sources such as TauCeti can supply successive, independently scoped
migrations.

### Lean 3 preservation and reconstruction leads

The priorities below are provisional. Use the
[contribution guide](.github/CONTRIBUTING.md#recovery-modes) to assess maintained
descendants, compare theorem coverage, and choose a recovery mode.

#### Priority A -- port pilot and reconstruction candidates

- [adamtopaz/lean-acl-pairs](https://github.com/adamtopaz/lean-acl-pairs) · [#117](https://github.com/KiringYJ/mathlib-fidelity/issues/117)
- [leanprover-community/lean-liquid](https://github.com/leanprover-community/lean-liquid) · [#115](https://github.com/KiringYJ/mathlib-fidelity/issues/115)
- [leanprover-community/lean-perfectoid-spaces](https://github.com/leanprover-community/lean-perfectoid-spaces) · [#137](https://github.com/KiringYJ/mathlib-fidelity/issues/137)

#### Priority B -- theorem-level overlap audits

- [dagurtomas/lean-solid](https://github.com/dagurtomas/lean-solid) · [#138](https://github.com/KiringYJ/mathlib-fidelity/issues/138)
- [b-mehta/topos](https://github.com/b-mehta/topos) · [#139](https://github.com/KiringYJ/mathlib-fidelity/issues/139)

#### Existing Lean 4 descendant

- [ianklatzco/flypitch](https://github.com/ianklatzco/flypitch) · [#133](https://github.com/KiringYJ/mathlib-fidelity/issues/133)

### Established mathlib-downstream leads

| Repository | Main issues |
| --- | --- |
| [ImperialCollegeLondon/FLT](https://github.com/ImperialCollegeLondon/FLT) | [#140](https://github.com/KiringYJ/mathlib-fidelity/issues/140) |
| [leanprover-community/flt-regular](https://github.com/leanprover-community/flt-regular) | [#121](https://github.com/KiringYJ/mathlib-fidelity/issues/121) |
| [fpvandoorn/carleson](https://github.com/fpvandoorn/carleson) | [#116](https://github.com/KiringYJ/mathlib-fidelity/issues/116) |
| [teorth/pfr](https://github.com/teorth/pfr) | [#122](https://github.com/KiringYJ/mathlib-fidelity/issues/122) |
| [YaelDillies/apap](https://github.com/YaelDillies/apap) | [#141](https://github.com/KiringYJ/mathlib-fidelity/issues/141) |
| [YaelDillies/cam-combi](https://github.com/YaelDillies/cam-combi) | [#149](https://github.com/KiringYJ/mathlib-fidelity/issues/149) |
| [AlexKontorovich/PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) | [#142](https://github.com/KiringYJ/mathlib-fidelity/issues/142) |
| [kbuzzard/ClassFieldTheory](https://github.com/kbuzzard/ClassFieldTheory) | [#143](https://github.com/KiringYJ/mathlib-fidelity/issues/143) |
| [n-yamaguchi-0729/ClassFieldTheory](https://github.com/n-yamaguchi-0729/ClassFieldTheory) | [#143](https://github.com/KiringYJ/mathlib-fidelity/issues/143) |
| [leanprover-community/sphere-eversion](https://github.com/leanprover-community/sphere-eversion) | [#119](https://github.com/KiringYJ/mathlib-fidelity/issues/119) |
| [thefundamentaltheor3m/Sphere-Packing-Lean](https://github.com/thefundamentaltheor3m/Sphere-Packing-Lean) | [#144](https://github.com/KiringYJ/mathlib-fidelity/issues/144) |
| [emilyriehl/infinity-cosmos](https://github.com/emilyriehl/infinity-cosmos) | [Chapter 1 #150](https://github.com/KiringYJ/mathlib-fidelity/issues/150) |
| [teorth/equational_theories](https://github.com/teorth/equational_theories) | [#148](https://github.com/KiringYJ/mathlib-fidelity/issues/148) |
| [Paul-Lez/PersistentDecomp](https://github.com/Paul-Lez/PersistentDecomp) | [#145](https://github.com/KiringYJ/mathlib-fidelity/issues/145) |
| [RemyDegenne/brownian-motion](https://github.com/RemyDegenne/brownian-motion) | [#146](https://github.com/KiringYJ/mathlib-fidelity/issues/146) |
| [YaelDillies/gibbs-measure](https://github.com/YaelDillies/gibbs-measure) | [#134](https://github.com/KiringYJ/mathlib-fidelity/issues/134) |
| [YijunYuan/HarderNarasimhan](https://github.com/YijunYuan/HarderNarasimhan) | [#126](https://github.com/KiringYJ/mathlib-fidelity/issues/126) |
| [Whysoserioushah/BrauerGroup](https://github.com/Whysoserioushah/BrauerGroup) | [#151](https://github.com/KiringYJ/mathlib-fidelity/issues/151) |
| [mcdoll/DispersiveEquations](https://github.com/mcdoll/DispersiveEquations) | [Schrödinger #152](https://github.com/KiringYJ/mathlib-fidelity/issues/152) |
| [Ivan-Sergeyev/seymour](https://github.com/Ivan-Sergeyev/seymour) | [#147](https://github.com/KiringYJ/mathlib-fidelity/issues/147) |
| [girving/series](https://github.com/girving/series) | [#153](https://github.com/KiringYJ/mathlib-fidelity/issues/153) |

| Candidate | Scope to investigate | Observed default ref |
| --- | --- | --- |
| [leanprover-community/add-combi](https://github.com/leanprover-community/add-combi) | Balog--Szemerédi--Gowers and additive VC dimension. Compare convolution and energy with PFR. [Modules](https://github.com/leanprover-community/add-combi/blob/master/AddCombi.lean) | `master` |
| [formal-applied-math/formal-mathfin](https://github.com/formal-applied-math/formal-mathfin) | Stochastic calculus and mathematical finance. Compare Itô and Girsanov APIs and check reduced benchmark statements. [Coverage](https://github.com/formal-applied-math/formal-mathfin/blob/main/README.md) | `main` |
| [matheconlib/matheconlib](https://github.com/matheconlib/matheconlib) | Microeconomic theory, including strategic and Bayesian games, mechanism design, auctions, choice, and matching. [Coverage](https://github.com/matheconlib/matheconlib#current-coverage) | `main` |
| [YaelDillies/toric](https://github.com/YaelDillies/toric) | toric varieties | `master` |
| [mcdoll/DynamicalSystems](https://github.com/mcdoll/DynamicalSystems) | Carathéodory ODEs and LaSalle/Lyapunov stability. Compare the flow API. [Modules](https://github.com/mcdoll/DynamicalSystems/blob/main/DynamicalSystems.lean) | `main` |
| [leanprover-community/physlib](https://github.com/leanprover-community/physlib) | physics-specific formalization library | `master` |
| [LionSR/QICLean](https://github.com/LionSR/QICLean) | TNLean's quantum-channel, entropy, and spectral library. Compare density matrices and completely positive maps with Physlib. [Modules](https://github.com/LionSR/QICLean/blob/main/QICLean.lean) | `main` |
| [lecopivo/SciLean](https://github.com/lecopivo/SciLean) | scientific computing and applied-mathematics infrastructure | `master` |
| [LeanMachineLearning/LML](https://github.com/LeanMachineLearning/LML) | Bregman divergence, subgradients, and KL data processing. Compare `ForMathlib` with Mathlib and `lean-stat-learning-theory`. [Modules](https://github.com/LeanMachineLearning/LML/blob/main/LeanMachineLearning.lean) | `main` |
| [vihdzp/combinatorial-games](https://github.com/vihdzp/combinatorial-games) | Grundy theory, Nim, canonical forms, and loopy games. Compare terminating-game sums with `Prod.GameAdd`. [Modules](https://github.com/vihdzp/combinatorial-games/blob/master/CombinatorialGames.lean) | `master` |
| [leanprover/cslib](https://github.com/leanprover/cslib) | Computer science library. Compare finite-automaton language results with `Mathlib/Computability`. [Modules](https://github.com/leanprover/cslib/blob/main/Cslib.lean) | `main` |
| [Verified-zkEVM/ArkLib](https://github.com/Verified-zkEVM/ArkLib) | Interactive oracle reductions, coding theory, and FRI. [Adaptive FRI bound](https://github.com/Verified-zkEVM/ArkLib/blob/main/ArkLib/ProofSystem/Fri/Spec/AdaptiveSoundness.lean) | `main` |

### Paper-scale and specialty leads

| Repository | Main issues |
| --- | --- |
| [b-mehta/exponential-ramsey](https://github.com/b-mehta/exponential-ramsey) | [#154](https://github.com/KiringYJ/mathlib-fidelity/issues/154) |
| [b-mehta/ABC-Exceptions](https://github.com/b-mehta/ABC-Exceptions) | [#155](https://github.com/KiringYJ/mathlib-fidelity/issues/155) |
| [teorth/sendov](https://github.com/teorth/sendov) | [#129](https://github.com/KiringYJ/mathlib-fidelity/issues/129) |
| [alonamaloh/schoenflies-lean](https://github.com/alonamaloh/schoenflies-lean) | [#128](https://github.com/KiringYJ/mathlib-fidelity/issues/128) |
| [ARGO-LABORATORY/Wolstenholme_1862](https://github.com/ARGO-LABORATORY/Wolstenholme_1862) | [#130](https://github.com/KiringYJ/mathlib-fidelity/issues/130) |
| [0stellensatz/MassFormula](https://github.com/0stellensatz/MassFormula) | [#118](https://github.com/KiringYJ/mathlib-fidelity/issues/118) |
| [ashvin-swaminathan/quartic-invariant](https://github.com/ashvin-swaminathan/quartic-invariant) | [#156](https://github.com/KiringYJ/mathlib-fidelity/issues/156) |
| [karlesmarin/godsil-gutman-lean](https://github.com/karlesmarin/godsil-gutman-lean) | [Papers I–II #157](https://github.com/KiringYJ/mathlib-fidelity/issues/157) |
| [catskillsresearch/scott1964](https://github.com/catskillsresearch/scott1964) | [#158](https://github.com/KiringYJ/mathlib-fidelity/issues/158) |
| [yawara/odd-order](https://github.com/yawara/odd-order) | [#159](https://github.com/KiringYJ/mathlib-fidelity/issues/159) |
| [LionSR/TNLean](https://github.com/LionSR/TNLean) | [FT-MPS #160](https://github.com/KiringYJ/mathlib-fidelity/issues/160) |
| [sinhp/HoTTLean](https://github.com/sinhp/HoTTLean) | [Groupoid model #161](https://github.com/KiringYJ/mathlib-fidelity/issues/161) |
| [oliver-butterley/SpectralThm](https://github.com/oliver-butterley/SpectralThm) | [#127](https://github.com/KiringYJ/mathlib-fidelity/issues/127) |
| [FormalizedFormalLogic/Foundation](https://github.com/FormalizedFormalLogic/Foundation) | [Incompleteness and provability #162](https://github.com/KiringYJ/mathlib-fidelity/issues/162) |
| [YuanheZ/lean-stat-learning-theory](https://github.com/YuanheZ/lean-stat-learning-theory) | [Published core #163](https://github.com/KiringYJ/mathlib-fidelity/issues/163) |
| [sven-manthe/A-formalization-of-Borel-determinacy-in-Lean](https://github.com/sven-manthe/A-formalization-of-Borel-determinacy-in-Lean) | [#120](https://github.com/KiringYJ/mathlib-fidelity/issues/120) |
| [abenenson/rellich-kondrachov](https://github.com/abenenson/rellich-kondrachov) | [#125](https://github.com/KiringYJ/mathlib-fidelity/issues/125) |
| [math-xmum/Brouwer](https://github.com/math-xmum/Brouwer) | [#123](https://github.com/KiringYJ/mathlib-fidelity/issues/123) |
| [harfe/fixed-point-theorems-lean4](https://github.com/harfe/fixed-point-theorems-lean4) | [#164](https://github.com/KiringYJ/mathlib-fidelity/issues/164) |
| [kim-em/KnuthClaudeLean](https://github.com/kim-em/KnuthClaudeLean) | [#113](https://github.com/KiringYJ/mathlib-fidelity/issues/113) |
| [vltanh/lean4-moving-sofa](https://github.com/vltanh/lean4-moving-sofa) | [#124](https://github.com/KiringYJ/mathlib-fidelity/issues/124) |
| [vltanh/lean4-ambidextrous-sofa](https://github.com/vltanh/lean4-ambidextrous-sofa) | [#124](https://github.com/KiringYJ/mathlib-fidelity/issues/124) |
| [mathlib-initiative/sum_product](https://github.com/mathlib-initiative/sum_product) | [#165](https://github.com/KiringYJ/mathlib-fidelity/issues/165) |
| [platypii/integer-mult-bounds-lean](https://github.com/platypii/integer-mult-bounds-lean) | [#166](https://github.com/KiringYJ/mathlib-fidelity/issues/166) |
| [smmercuri/zeta](https://github.com/smmercuri/zeta) | [Height 10011 #167](https://github.com/KiringYJ/mathlib-fidelity/issues/167) |
| [zksecurity/simple-rbr-fri](https://github.com/zksecurity/simple-rbr-fri) | [#168](https://github.com/KiringYJ/mathlib-fidelity/issues/168) |
| [Harry-Tech-Guide/Lean-4-Four-Color-Theorem-Formalization](https://github.com/Harry-Tech-Guide/Lean-4-Four-Color-Theorem-Formalization) | [#132](https://github.com/KiringYJ/mathlib-fidelity/issues/132) |
| [mo271/FormalBook](https://github.com/mo271/FormalBook) | [#198](https://github.com/KiringYJ/mathlib-fidelity/issues/198) |
| [lean-dojo/LeanMillenniumPrizeProblems](https://github.com/lean-dojo/LeanMillenniumPrizeProblems) | [#200](https://github.com/KiringYJ/mathlib-fidelity/issues/200) |

| Candidate | Scope to investigate | Observed default ref |
| --- | --- | --- |
| [a-dangelo/Lean-AG](https://github.com/a-dangelo/Lean-AG) | algebraic geometry, including scheme and Krull-dimension material | `main` |
| [felixpernegger/pibase-lean](https://github.com/felixpernegger/pibase-lean) | Lean formalizations of π-Base topology implications. Compare source definitions with Mathlib before selecting a theorem or counterexample. [Coverage dashboard](https://felixpernegger.github.io/pibase-lean/) | `master` |

### Recent and AI-assisted leads

Review source-reported claims under the ordinary [intake procedure](#intake-procedure).

| Repository | Main issues |
| --- | --- |
| [mattrobball/BridgelandStability](https://github.com/mattrobball/BridgelandStability) | [#169](https://github.com/KiringYJ/mathlib-fidelity/issues/169) |
| [marcmorningstar/lean4-ergodic-theory](https://github.com/marcmorningstar/lean4-ergodic-theory) | [Oseledets #170](https://github.com/KiringYJ/mathlib-fidelity/issues/170) |
| [will1491/RiemannDynamics](https://github.com/will1491/RiemannDynamics) | [#171](https://github.com/KiringYJ/mathlib-fidelity/issues/171) |
| [MerLeanProver/ACMaxConjecture](https://github.com/MerLeanProver/ACMaxConjecture) | [#172](https://github.com/KiringYJ/mathlib-fidelity/issues/172) |
| [tadamcz/mean-value-problem](https://github.com/tadamcz/mean-value-problem) | [#173](https://github.com/KiringYJ/mathlib-fidelity/issues/173) |
| [tadamcz/erdos548](https://github.com/tadamcz/erdos548) | [#174](https://github.com/KiringYJ/mathlib-fidelity/issues/174) |
| [tadamcz/erdos571](https://github.com/tadamcz/erdos571) | [#175](https://github.com/KiringYJ/mathlib-fidelity/issues/175) |
| [Yuren-Tang/erdos-306](https://github.com/Yuren-Tang/erdos-306) | [#176](https://github.com/KiringYJ/mathlib-fidelity/issues/176) |
| [openai/NavierStokesAndEuler](https://github.com/openai/NavierStokesAndEuler) | [Navier–Stokes #179](https://github.com/KiringYJ/mathlib-fidelity/issues/179) · [Euler #180](https://github.com/KiringYJ/mathlib-fidelity/issues/180) |
| [openai/ten-proofs](https://github.com/openai/ten-proofs) | [#193](https://github.com/KiringYJ/mathlib-fidelity/issues/193) |
| [openai/cdc-lean](https://github.com/openai/cdc-lean) | [#177](https://github.com/KiringYJ/mathlib-fidelity/issues/177) |
| [anthropics/formal-math](https://github.com/anthropics/formal-math) | [Zeta and Dirichlet zeros #194](https://github.com/KiringYJ/mathlib-fidelity/issues/194) · [3SUM and APSP #195](https://github.com/KiringYJ/mathlib-fidelity/issues/195) · [Counting and ETH #196](https://github.com/KiringYJ/mathlib-fidelity/issues/196) · [VP–VNP #197](https://github.com/KiringYJ/mathlib-fidelity/issues/197) |
| [anthropics/fermats-last-theorem](https://github.com/anthropics/fermats-last-theorem) | [#140](https://github.com/KiringYJ/mathlib-fidelity/issues/140) |
| [openai/PrimeGaps186](https://github.com/openai/PrimeGaps186) | [#178](https://github.com/KiringYJ/mathlib-fidelity/issues/178) |
| [openai/LongGapsBetweenPrimes](https://github.com/openai/LongGapsBetweenPrimes) | [#131](https://github.com/KiringYJ/mathlib-fidelity/issues/131) |
| [Vilin97/Autoformalization](https://github.com/Vilin97/Autoformalization) | [Landau #190](https://github.com/KiringYJ/mathlib-fidelity/issues/190) · [Vanishing #191](https://github.com/KiringYJ/mathlib-fidelity/issues/191) · [Splitting spheres #192](https://github.com/KiringYJ/mathlib-fidelity/issues/192) |
| [AxiomMath/Stacks](https://github.com/AxiomMath/Stacks) | [#114](https://github.com/KiringYJ/mathlib-fidelity/issues/114) |
| [AxiomMath/ClusterAlgebras](https://github.com/AxiomMath/ClusterAlgebras) | [#182](https://github.com/KiringYJ/mathlib-fidelity/issues/182) |
| [AxiomMath/CFSG](https://github.com/AxiomMath/CFSG) | [#183](https://github.com/KiringYJ/mathlib-fidelity/issues/183) |
| [AxiomMath/CFSGCorollary](https://github.com/AxiomMath/CFSGCorollary) | [#184](https://github.com/KiringYJ/mathlib-fidelity/issues/184) |
| [leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis) | [#185](https://github.com/KiringYJ/mathlib-fidelity/issues/185) |
| [mccorvie/riemann-masullo](https://github.com/mccorvie/riemann-masullo) | [Hecke foundations #186](https://github.com/KiringYJ/mathlib-fidelity/issues/186) |
| [math-inc/strongpnt](https://github.com/math-inc/strongpnt) | [#142](https://github.com/KiringYJ/mathlib-fidelity/issues/142) |
| [tristanbuckmaster/navier-stokes](https://github.com/tristanbuckmaster/navier-stokes) | [#181](https://github.com/KiringYJ/mathlib-fidelity/issues/181) |
| [yang-mills-group/OpenAI-YM-20261028](https://github.com/yang-mills-group/OpenAI-YM-20261028) | [#187](https://github.com/KiringYJ/mathlib-fidelity/issues/187) |
| [andersonwu2000/Asterism-formalizations](https://github.com/andersonwu2000/Asterism-formalizations) | [Five-body #188](https://github.com/KiringYJ/mathlib-fidelity/issues/188) · [Cocircular #189](https://github.com/KiringYJ/mathlib-fidelity/issues/189) |
| [gotrevor/lean-gallery](https://github.com/gotrevor/lean-gallery) | [#199](https://github.com/KiringYJ/mathlib-fidelity/issues/199) |
| [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures) | [#201](https://github.com/KiringYJ/mathlib-fidelity/issues/201) |
| [ImperialCollegeLondon/AnnalsChallenge](https://github.com/ImperialCollegeLondon/AnnalsChallenge) | [#202](https://github.com/KiringYJ/mathlib-fidelity/issues/202) |

| Candidate | Scope to investigate | Observed default ref |
| --- | --- | --- |
| [merely-true/merely-true](https://github.com/merely-true/merely-true) | AI-generated Lean library with CI-only merge decisions | `main` |
| [TauCetiProject/TauCeti](https://github.com/TauCetiProject/TauCeti) | Continuously developed Lean library with human roadmaps and AI implementation and review | `main` |
| [CBirkbeck/AINTLIB](https://github.com/CBirkbeck/AINTLIB) | AI-reviewed library permitting `sorry`. Compare its [adic spaces](https://github.com/CBirkbeck/AINTLIB/tree/main/projects/AdicSpaces) with Lean 3 perfectoid and current valuation theory. | `main` |

### Reformalization references

These sources support comparisons across proof assistants under the
[reformalization policy](.github/CONTRIBUTING.md#recovery-modes).

| Repository | Main issues |
| --- | --- |
| [hol-light-family/Flyspeck](https://github.com/hol-light-family/Flyspeck) | [#135](https://github.com/KiringYJ/mathlib-fidelity/issues/135) |
| [agda/cubical](https://github.com/agda/cubical) | [#136](https://github.com/KiringYJ/mathlib-fidelity/issues/136) |
| [rocq-community/fourcolor](https://github.com/rocq-community/fourcolor) | [Lean comparison #132](https://github.com/KiringYJ/mathlib-fidelity/issues/132) |

### Discovery feeds

Use these catalogues to locate original repositories and review evidence.

| Feed | Use | Observed default ref |
| --- | --- | --- |
| [dzackgarza/formalization-corpus](https://github.com/dzackgarza/formalization-corpus) | searchable cross-repository formalization index for discovery and reuse checks | `main` |
| [LeanPool/lean-pool](https://github.com/LeanPool/lean-pool) | provenance-indexed collection. The earlier `Vilin97/lean-pool` is now a fork. | `main` |
| [leanprover-community/LeanProject](https://github.com/leanprover-community/LeanProject) | template with a [catalogue of downstream projects](https://github.com/leanprover-community/LeanProject#selected-projects-using-this-template) | `main` |
| [leanprover/reservoir](https://github.com/leanprover/reservoir) | [public Lean package index](https://reservoir.lean-lang.org/) for locating package sources and releases | `master` |
| [PalomarRegistry/PalomarWeb](https://github.com/PalomarRegistry/PalomarWeb) | [Palomar Registry](https://palomar-registry.org/) entries point to pinned projects and review evidence. The [Palomar template](https://github.com/PalomarRegistry/PalomarTemplate) documents the `formalization.yaml` metadata | `main` |
| [openai/math](https://github.com/openai/math) | manuscripts and Lean artifacts. Use the [per-result formalization catalogue](https://github.com/openai/math/blob/main/lean/formalization.yaml) to locate statements and verification configurations | `main` |
| [pi-base/data](https://github.com/pi-base/data) | topology counterexamples and implication references. Compare the underlying definitions and cited proofs with `pibase-lean` | `main` |
| [isabelle-prover/mirror-afp-devel](https://github.com/isabelle-prover/mirror-afp-devel) | development mirror of the [Isabelle Archive of Formal Proofs](https://isa-afp.org/). Follow the selected entry's authorship, dependencies, and license for reformalization | `master` |

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

`accepted` records selection, `migrating` records work in progress, and
`integrated` requires completed provenance, migration, and verification. Apply
the [complete-migration contract](FORK_DESIGN.md#complete-migrations) and record
the proved boundaries of independently deferred foundational issues.

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

Decide license compatibility for the exact source and distribution.

- [Apache License 2.0, section 4](https://www.apache.org/licenses/LICENSE-2.0.html)
  states its redistribution conditions, including providing the license,
  marking modified files, retaining applicable notices, and carrying forward
  applicable `NOTICE` attribution.
- [GitHub's repository licensing documentation](https://docs.github.com/en/repositories/managing-your-repositorys-settings-and-features/customizing-your-repository/licensing-a-repository)
  explains that public visibility without a license does not grant general
  permission to reproduce, distribute, or create derivative works.
