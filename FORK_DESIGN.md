# Fidelity Design Charter

## Purpose

Fidelity is an independent downstream mathematical library built on mathlib.
It prioritizes mathematical fidelity, interoperability between theories, and
a public API that mathematicians can use in substantial formalizations.

This charter governs library-wide design decisions. The Lean definitions and
theorems specify the current API. Module docstrings explain its mathematical
meaning, design choices, and use. Regression tests and linters check the
behavior their coverage supports.

- [Contribution guide](.github/CONTRIBUTING.md) and
  [project maintenance guide](AI_AGENT_PROJECT.md) govern review, intake,
  reconciliation, and verification.
- [Changelog](CHANGELOG.md) records significant changes by release.
  [TODO](TODO.md) records outstanding work, including enforcement of adopted
  principles that still needs implementation.

## Coequal Design Goals

Mathematical fidelity determines the objects, their domains, and the
meaning of the statements. Choose a type-theoretically natural interface
that preserves those semantics, and make it usable through standard
notation, structure, and automation. Judge all three decisions in real
formalizations.

### Mathematical fidelity

- Give each partial operation its exact canonical domain. Use the largest
  domain on which the intended specification determines a unique value and
  extends the standard operation. Encode it in a type, a proof argument, or
  an explicit partiality type. Exclude arbitrary off-domain values.
- When there is no direct description of the domain, express existence and
  uniqueness of the specified object, with any hypotheses required to make
  the specification independent of library conventions. Provide convenient
  sufficient conditions through constructors, lemmas, instances, or tactics.
  State the specifying relation separately so callers working with an
  explicit solution can use it on its own.
- When the specification determines a class up to an equivalence, expose
  that class and the relation satisfied by its representatives. A witness
  chosen from the class may be used privately in a `Prop`-valued existence
  proof. Keep that choice out of the public API and its implementation of the
  class.
- Give any independently total operation its own mathematical specification
  and a name that expresses it. Require a mathematical source and laws
  determining its value at every input, including degenerate cases.
- Apply the same domain and canonicity requirements to notation, coercions,
  instances, defaults, and ambient structures. When the user must choose a
  construction, provide an explicit constructor or a deliberately selected
  local instance. Keep obligations visible in theorem statements and check
  the obligations of the original expression before simplification.
- Preserve domains, hypotheses, uniqueness, quotient structure, and
  naturality through bundled types and other abstractions. Require proved
  correspondences that preserve the relevant operations and laws. An
  objectwise equivalence alone leaves those obligations open.

### Interoperability between mathematical theories

Make useful structural relationships available across the library. Supply
the maps, constructions, equivalences, or universal properties that state
each relationship at the right level of generality. State their sources,
targets, and hypotheses. Prove the composition, naturality, and
compatibility laws that make the relationships usable together.

Reuse existing results directly, specialize a common theorem, or transfer
a theorem along a specified map. Distinguish definitional equality,
isomorphism, equivalence of categories, and weaker correspondences.
Expose noncanonical choices in the interface. Place a relationship in a
module that can import both theories and use representative formalizations
to test its reuse and import cost.

Generalize to recognizable mathematical abstractions when the statement
uses their structure and downstream proofs can reuse it. Require evidence
from independent uses when proposing a new abstraction. Keep useful
specializations that supply a natural statement or theorem-search entry
point. Supply routine closure lemmas and instances with the structures
they serve.

### API quality and quality of life

- Use conventional mathematical operations and proof steps at the public
  surface. Keep representation details behind proved interfaces. A thin
  mathematician-facing interface can reuse a generic core and its theorems.
- Bundle an invariant when it defines a stable object with useful closed
  operations. Express one-off obligations as proof arguments. Use explicit
  partial maps where domains and their composition are part of the
  mathematics. Expose exactly the closure supported by the object and prefer
  coercions from constrained objects to their ambient carriers.
- Distinguish ambient objects, propositions about them, and objects carrying
  a property. For a collection, use membership when the structure is
  explicit and membership is standard mathematical language. Retain a
  conventional predicate for ambient use or theorem search. Give each
  context one normal form and make the corresponding statements
  definitionally equal where possible.
- Give notation a searchable named declaration and a compositional meaning.
  Each operand should have a stable mathematical role under nesting. Prefer
  ordinary application, projection, or membership when it is equally clear.
  Pass configuration of an ordinary argument through the term structure.
  Use special syntax for conventional operators, literals, and binders
  where it clarifies the mathematics.
- State ordinary multiargument functions and their theorems in curried form.
  Use product and dependent pair domains when the tuple itself is the
  mathematical input. Reuse curry and uncurry transports for alternate
  presentations. Separate structured theorems need mathematical content
  such as preservation of continuity or measurability.
- Let automation infer routine evidence through local hypotheses, smart
  constructors, and closure lemmas. Give errors that identify the unmet
  mathematical obligation. Design tactics alongside the API and require
  inspectable proofs.
- Fix the mathematical contract before optimizing imports, elaboration, or
  proof plumbing. Use measured costs and real consumers to guide module
  boundaries and shared infrastructure.

#### Priority-independent mathematical semantics

The written expression, its explicit inputs, and the constraints supplied
by the active context must determine its mathematical types, operations,
and structures. With the available declarations and scopes fixed, require
all admissible implicit interpretations to be definitionally equal.
Priorities, declaration or import order, and search heuristics may affect
the cost of coherent search. Use defaults, including conventional ones,
only for data the written expression and context already determine. Proof
search can choose any proof of the same already determined proposition.

Require explicit disambiguation whenever the context leaves distinct
interpretations. Use a type annotation, a named operation or map, an
explicit structure argument, a bundled object, or a deliberately selected
local instance. A propositional equality can justify explicit transport
between interpretations.

The [elaboration audit](TODO.md#priority-independent-elaboration) tracks
enforcement and coverage on official Lean.

### Mathematical vocabulary first

Use established mathematical names where the literature supports them.
Otherwise follow mathlib's naming conventions. In a named family, reserve
the bare name for an established primary formulation and use consistent
variant suffixes for the others. Give coequal formulations consistent
suffixes. Record an established alternative name as an exact,
attribute-free alias to the canonical declaration.

Keep paper-local terminology, theorem numbers, and author credit in source
references. Require evidence of conventional usage for eponymous and other
named results. Mathematical objects and theorem statements determine the
public vocabulary. Internal class names and proof techniques belong in
implementation and exposition.

### Proofs are API tests

Test a design against mathematically sound, conceptually organized proofs
in real consumers. Diagnose unnecessary friction in representations,
hypotheses, normal forms, missing lemmas, elaboration, or automation.
Keep the intended statement and its domain while making the argument
expressible through the library's public mathematics.

Prove shared arguments once at a natural level of generality and derive
useful specializations. In choosing a proof, prefer the closest established
abstraction that explains the result, avoid unnecessary logical assumptions,
and favor stable public interfaces. Compare import, elaboration, and kernel
costs after these criteria are met. An alternative proof belongs in the
canonical API when it exposes reusable mathematics.

## Official Lean and Operator Fidelity

Use the official toolchain selected by `lean-toolchain`, including its
compiler, kernel, standard libraries, and metaprogramming infrastructure.
Keep legitimate core types and faithful operations on them.

For a selected operator migration, exclude the retired semantics from
mathematical statements and definition bodies, including predicates and
structure data. Audit elaborated dependencies through aliases, private and
inherited declarations, generated mathematical declarations, instances,
coercions, and notation. Check whether a body supplies mathematical data or
a proof even when both use the same tactic syntax. Source searches guide
the audit. The evidence comes from the elaborated declarations and their
dependencies.

Remove replaceable uses from fork-controlled proofs and proof-producing
automation. The narrow exception is a proof dependency owned by the
official toolchain whose removal would require changing that toolchain.
Record the actual declaration and explain why the proof establishes the
faithful statement without supplying excluded mathematical data. Determine
the ownership of generated proof helpers and apply the same boundary.
Proof admission and axiom review still inspect proof dependencies.

## Complete Migrations

Deliver the final design for the selected scope in one complete delivery.
Migrate definitions, statements, proofs, implicit entry points, automation,
documentation, and all affected consumers. Remove retired interfaces and
fallback machinery, including compatibility aliases, version switches, and
private transitional adapters. Independently meaningful constructions can
coexist with proved mathematical conversions.

Preserve useful theorem coverage on the correct domains. Validate the
complete final state, exercise accepted and rejected inputs, and verify
the removal of retired semantics. Experiments and focused checks inform
the final design during development. Completion requires every in-scope
proof, consumer migration, and removal. Follow the
[verification workflow](AI_AGENT_PROJECT.md#complete-migration-workflow).

### Independent foundational dependencies

A genuinely separate lower-level issue can remain in [TODO](TODO.md) when
the selected API already satisfies its full domain and specification.
Identify the underlying declarations, consumers, and remaining obligation.
Prove valid-domain use, unreachability, or independence from a lower-level
fallback. If an unchanged generic interface requires a total function,
keep the necessary off-domain branch anonymous at its construction site
under the same proof obligation. An issue blocking an in-scope proof or a
faithful public API is part of the selected migration.

## Conjectures and Proof Status

Distinguish the mathematical evidence for a claim from the status of its
stored Lean proof. The adopted design admits unresolved statements only as
registered whole-theorem roots. Record source correspondence and whether
each root is a genuine conjecture or a result awaiting formalization.

Derive proof status from actual transitive dependencies under an explicitly
reviewed axiom and evaluation-trust base. Require ownership of every
permitted placeholder and reject unowned gaps and unapproved trust.
Show the unresolved roots on which a proof depends. Keep ordinary
mathematical statements, names, and subject placement stable as proofs
change. Kernel checking validates the elaborated proposition under its
actual dependencies. Mathematical review establishes correspondence with
the intended result. See the [Lean proof validation guide](https://lean-lang.org/doc/reference/latest/ValidatingProofs/).

The registry, admission gate, status interface, and migration of existing
statements are [pending implementation](TODO.md#conjectures-and-proof-status----accepted-design-pending-implementation).

## Mathematical scope and placement

Welcome mathematics from every field, including specialized and unpublished
work. Apply the same standards for fidelity, proof status, provenance, and
licensing across the library. Evaluate a contribution through the mathematics
it supplies, its fit with existing theory, and the work required to integrate
and maintain it.

- `Mathlib/` holds canonical definitions, constructions, and reusable results
  of extensible theories. Specialized and research-level results belong here
  when they fit a theory, including before they acquire downstream users.
  Put generally useful material in its subject modules.
- `Archive/` holds standalone formalizations of particular results, problems,
  computations, classifications, or distinctive alternative proofs. Allow
  local interfaces suited to these developments and reuse canonical
  statements where available.

A development can span both locations. Keep the transitive import closure
of `Mathlib` and its modules free of `Archive` modules. Review any promotion
from the archive against the same mathematical and API standards as a new
contribution.

Admit external work through mathematical and technical review, licensing
review, and source recording. Bring in-tree material onto the canonical API
and preserve attribution and provenance through adaptation. See the
[contribution guide](.github/CONTRIBUTING.md#external-sources-and-provenance)
and [source registry](SOURCES.md).

## Relationship to Upstream

Reuse mathlib's implementations and theorems where they meet this charter.
Judge inherited, fork-written, and proposed interfaces by the same
mathematical and technical criteria, including evidence from downstream
use. Treat the amount of migration work as a scheduling consideration.

Fidelity develops its own public API and can change upstream compatibility
through a complete migration. Fork-only changes serve Fidelity. Reconciliation
and publication procedures belong in the
[project maintenance guide](AI_AGENT_PROJECT.md#mathlib-baseline-reconciliation-workflow).
