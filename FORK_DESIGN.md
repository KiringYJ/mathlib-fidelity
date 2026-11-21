# Fork Design Philosophy and Roadmap

## Status

This document records the personal fork's design contracts. Implementation
and verification status is tracked in [`TODO.md`](TODO.md).

The interface goals and complete-migration policy below are adopted. Every
accepted migration must deliver the final design across its selected scope in
one complete change, without compatibility stages or transitional layers.
Independent lower-level problems may remain tracked work under the dependency
boundary below.
Concrete API names, representations, and automation require source inspection
and validation in real consumers. The inverse and exact division migration is
complete within the [scope below](#total-inverse-migration-contract).

The conjecture and proof-status policy is also adopted, with two epistemic
kinds sharing one Lean mechanism. Its registry, admission gate, dependency
index, and migrations are pending work in `TODO.md`; recording them here does
not implement or authorize those changes.

The official-Lean and operator-fidelity boundary below applies to each
operator migration and its semantic dependency checks.

## Purpose

This fork is an independent downstream mathematical library built from
mathlib's implementation and theorem base. Its public mathematical language
should be faithful to the objects and domains used by mathematicians while
remaining pleasant to use in substantial formalizations.

The fork is not an upstream contribution staging area. Fork-only changes are
not designed, partitioned, or rewritten for submission to
`leanprover-community/mathlib4`. Upstream remains a valuable source of
implementations, theorems, and updates, but upstream compatibility or reviewer
preference does not override the design commitments in this document.

## Official Lean and Operator Fidelity

Use the official Lean toolchain selected by `lean-toolchain`. Do not maintain
a patched compiler, kernel, `Init`, `Std`, or core Lean metaprogramming library
for this fork. Future XL migrations must respect this boundary; encountering
a totalized toolchain operation does not authorize a toolchain fork or require
replacing every core type with a library-owned copy.

Ban mathematically unfaithful operators, not otherwise legitimate carriers.
Core `Rat` and `Nat` remain available. In particular, core `Rat` represents a
reduced integer numerator and nonzero natural denominator; the existence of
totalized inverse or division does not invalidate that data representation.
Classify each operator by the exact domain, specifying properties, name, and
notation required by Mathematical fidelity below. A genuinely total operation
such as monus is not excluded merely because it is total.

For every selected operator migration, apply the following boundary to all
maintained declarations, including inherited and private declarations and
generated mathematical APIs:

- Remove the unfaithful operator from elaborated statements and mathematical
  definition semantics. Inspect parameter and result types, hypotheses,
  conclusions, implicit arguments, non-proof bodies, structure data fields,
  instances, casts, coercions, notation, and defaults. Follow semantic
  dependencies through aliases and referenced definitions; visibility and
  opacity do not hide a forbidden operation.
- Retain faithful operations on the same carrier. For example, `Rat.normalize`
  already requires a nonzero denominator and can support checked fraction
  construction. A replacement must not delegate to the selected retired
  totalized operation behind a strict wrapper; the complete-migration and
  independently deferred foundation rules still apply.
  An independently specified and audited monus may retain core `Nat.sub` as
  its implementation and support checked subtraction: monus is retained
  mathematics, while unrestricted ordinary subtraction is the retired
  interface. Classify these mathematical roles before selecting forbidden
  dependencies. This does not permit wrapping an operator whose totalized
  semantics are themselves selected for removal.
- Remove uses of unfaithful operators from fork-controlled proofs and
  proof-producing automation wherever feasible. Prefer faithful operations
  and lemmas, and migrate replaceable helpers, coefficient computations,
  quotation adapters, and certificate construction within the selected scope.
  Proof irrelevance alone is not a reason to retain an avoidable use.
- Retain an unavoidable dependency owned by official Lean only within proof
  implementation when removing it would require modifying the toolchain.
  Identify the actual core declarations and prove that their use establishes
  the faithful elaborated proposition without exporting the excluded
  semantics. This is not permission to keep replaceable fork-owned uses,
  introduce a new totalized proof helper, or restore a retired mathematical API.
- A proposition or predicate definition is statement semantics:
  `def P : Prop := ...` is not a proof exemption. For `def h : P := ...` with
  `P : Prop`, the type must satisfy the semantic boundary and the proof body
  follows the proof-cleanup rule. A data-producing body written with `by`
  remains mathematical implementation. Likewise, instance law proofs and
  instance data fields must be inspected separately.

Imported presence and an unavoidable official-toolchain proof dependency do
not violate this policy. Audit generated proof auxiliaries by provenance and
keep proof-only constructions from becoming independently maintained
mathematical statements or value-producing implementations. A source grep,
carrier blacklist, import ban, or blanket transitive proof-dependency ban
cannot replace this distinction. The implementation and acceptance checks for
the selected migration must establish the boundary; this policy does not claim
that every inherited declaration has already been migrated.

Under the reviewed axiom base, kernel checking establishes that a proof has its
elaborated proposition as its type. The mathematical audit must establish that
the proposition and its defining semantics express the intended mathematics;
kernel checking does not perform that audit. See Lean's documentation on
[propositions](https://lean-lang.org/doc/reference/latest/The-Type-System/Propositions/)
and [proof validation](https://lean-lang.org/doc/reference/latest/ValidatingProofs/).
Retaining unavoidable toolchain dependencies inside proofs does not relax the
conjecture, proof-status, axiom, or evaluation-trust admission policy. Those
checks still inspect proof dependencies, separately from the semantic operator
audit and the cleanup of fork-controlled proof implementations.

## Complete Migrations

Every accepted migration in this fork goes directly to its final design in one
complete delivery. This applies to mathematical APIs, representations, naming,
notation, instances, automation, and source integrations, including foundational
changes such as inverse and division. Migration size and upstream compatibility
do not justify compromising mathematical fidelity, type-theoretic naturalness,
or quality of life.

- Cover the selected interface and all its affected consumers in the same change:
  definitions, proofs, implicit entry points, tactics, tests, generated imports,
  and documentation. Changing a type or contract includes every caller that
  needs that change; those callers cannot be deferred as another migration.
- Implement the selected design directly. Do not introduce or retain
  compatibility shims, deprecated aliases, dual old/new APIs, version switches,
  private transitional adapters, or renamed totalized fallbacks to bridge a
  migration. Update callers to the canonical interface and delete the replaced
  machinery.
- Do not deliver a prototype-only milestone, a partial subsystem migration, or
  a strict facade over the old implementation as completion of an accepted
  migration. Moving an in-scope consumer, proof obligation, or removal to
  `TODO.md` does not complete the work. An unresolved obligation of the selected
  interface keeps the migration incomplete.
- Investigation, small experiments, incremental edits, focused builds, and
  independent review are internal work within the same migration. They do not
  establish supported intermediate APIs or relax the final acceptance criteria.
  One delivery does not require one edit or one commit; logical commit discipline
  and authorization for commits and publication still apply.
- Validate the complete final source state and scan for every retired surface
  and in-scope implementation dependency. Preserve mathematical statements and
  useful theorem coverage on their correct domains; do not obtain a green build
  by dropping consumers, weakening specifications, adding proof holes, or
  disabling checks.

Mathematical equivalences and conversions between independently meaningful
objects remain legitimate parts of the final API. They are not permission to
retain a superseded interface for compatibility. A genuine total mathematical
object still requires the literature and specifying properties below; renaming
a fallback does not establish such an object.

### Independent foundational dependencies

A migration is complete within its selected mathematical and API scope; it need
not resolve every independent problem in the foundations it uses. In particular,
an L migration may finish while an XL problem in an existing lower-level API is
recorded in `TODO.md` for a future XL task. Effort labels help describe the
boundary; they do not by themselves justify deferring a required part of the
selected migration.

- Identify the lower-level declarations, the separate mathematical obligation,
  and the current consumers in a precise TODO entry. Report that dependency
  separately from completion of the selected migration.
- Prove that the selected API has its correct domain and specification while
  using the existing substrate. For a totalized substrate, prove valid-domain
  use, unreachability of invalid branches, or independence from their values.
  If an unchanged generic interface requires a total function, a necessary
  off-domain branch stays anonymous at its construction site, with the same
  proof and a TODO for the lower-level interface.
- Keep the selected API in its final form. Do not add old/new API pairs,
  compatibility aliases, reverse bridges, or a named transitional layer for
  the selected migration. A future foundational repair should replace its
  substrate without reviving the retired API.
- Defer only a genuinely separate foundational problem. If it prevents a
  faithful public contract or a required proof in the selected scope, that
  migration is still incomplete. Do not hide the gap by changing a label or
  claiming that the underlying totalization has already been removed.

## Coequal Design Goals

These goals do different jobs rather than forming a ranking. Mathematical
fidelity fixes the semantics: which object, on which exact domain, under which
hypotheses. Type-theoretic naturalness then fixes the API and interface that
present those semantics: among faithful encodings, choose the one most natural
in the type theory and in the existing library, judged by compiling real call
sites with each candidate. Quality of life is always required: within those two
decisions, make the interface as convenient as possible through instances,
closure lemmas, automation, and diagnostics, without changing the semantics or
the interface.

### Mathematical fidelity

- A public operation bearing an ordinary mathematical name should expose the
  domain on which that operation is mathematically defined. Encode the domain
  in an input type, a proof argument, or an explicit partiality type.
- Take that domain to be the exact domain on which the operation is
  canonical: the largest class of inputs on which its defining specification
  determines a unique value, without an arbitrary normalization, and agrees
  with the standard operation wherever the literature defines it. Do not
  shrink it to a convenient sufficient condition or to the narrower class for
  which a particular text names the operation; such classes belong in
  hypotheses, specializations, and documentation. For example,
  `ProbabilityTheory.cdf` takes every measure that is finite on each ray
  `Iic x`, where `x ↦ μ.real (Iic x)` is the unique generating Stieltjes
  function with limit 0 at -∞, although many texts define the cdf only for
  probability or finite measures. Stop where extending further would require
  an arbitrary choice, such as normalizing a locally finite measure at `0`.
- Do not silently extend a partial mathematical operation with a junk or
  arbitrary value while continuing to present it as the same operation.
- Delete the selected operation's invalid-domain fallback machinery, including
  private compatibility helpers. Making its old implementation private does
  not complete the migration. An existing lower-level interface that demands
  a total value may remain only under the independent-foundational-dependency
  requirements above, with a proved boundary and a precise TODO.
- When the exact domain depends on the input and has no closed form, state it
  as the existence and uniqueness of the specified object, as a proposition or
  class such as `HasUniqueCondExp m μ f` or `HasUniqueCondCDF ρ`, together
  with any condition that keeps the specification independent of a library
  convention, such as the null-measurability of the sets of `m` in
  `HasUniqueCondExp`, without which the restricted measures follow the
  outer-measure convention of `Measure.restrict`. Supply the convenient
  sufficient conditions, such as integrability with the σ-finiteness of a
  trimmed measure, as constructors, instances, and default tactics; they are
  theorem hypotheses, not the domain. State the specifying relation
  separately, such as `IsCondExp m μ f g` for a version `g` of the conditional
  expectation of `f`, so that definitions and theorems that only need a
  version, such as martingales, use the relation and do not inherit the
  operation's domain.
- When the defining specification determines an object only up to an
  equivalence, such as almost-everywhere equality, the canonical object is the
  equivalence class, not a chosen representative. Expose the class, for
  example as a germ along the almost-everywhere filter or an `AEEqFun`,
  together with membership of representatives and the relational
  specification. Do not export a representative chosen by `Classical.choose`,
  however it is named or documented: the habit of informal texts to fix "a
  version" does not make a choice canonical. Concrete representatives may
  appear only as private witnesses inside proofs of Prop-valued existence
  statements. Such a witness construction is a proof device, not an
  implementation bridge: no public definition unfolds to it.
- An independent total object needs its own mathematical specification that
  determines its value at every input, including degenerate cases. Record the
  exact mathematical source and the defining properties. A value assigned
  solely to make a partial operation total remains a fallback regardless of
  its use in other libraries.
- Keep domain and other semantic obligations machine-visible. A theorem that
  happens to hold on a totalized fallback branch must not use that accident to
  hide a missing hypothesis in its intended mathematical statement.
- Apply the same semantic contract to implicit entry points: global instances,
  ambient structures, coercions, notation, and defaults must not bypass an
  explicit API's domain or silently select a construction it requires users to
  choose. When the ordinary API requires uniqueness, automatically supplied
  ambient objects must respect that requirement too. A mathematically valid
  nonunique construction may remain available through an explicit constructor
  or a deliberately installed local instance; documenting a global convention
  alone does not resolve this interface mismatch. This is an interface policy,
  not a claim that choosing a nonunique construction is mathematically invalid.
- Replace the selected operation and its implementation together. Distinguish
  removal of its old machinery from reliance on an existing lower-level API:
  a proved use of a separately tracked foundational dependency can support a
  completed scoped migration, but does not establish removal of that dependency.

### API quality and quality of life

Faithfulness is not a license for proof plumbing to dominate the mathematics.
The library should retain real domain obligations while eliminating repetitive
manual work around them.

- Prefer standard mathematical concepts, notation, and proof decomposition at
  the public surface, which serves mathematicians and downstream formalizers
  first. Equivalent expressibility through implementation details is not an
  equivalent user interface. Judge an interface by whether its statements and
  operations faithfully represent the object; a mathematician can discover its
  declarations from standard concepts and terminology; its notation matches
  the canonical operations where that distinction carries meaning; common
  constructions compose without exposing representation details; and proof
  code shows the mathematical reason a step works rather than an equivalent
  library-specific decomposition.
- Choose the mathematically faithful and natural public interface before
  minimizing imports or dependency weight. A heavier import is not by itself an
  API defect when it supplies the standard abstraction that the statement
  actually uses. Measure build, elaboration, and maintenance costs only after
  fixing the mathematical contract. Resolve a genuine import cycle or a
  demonstrated unacceptable cost by refactoring module boundaries or extracting
  shared substrate, not by weakening the public mathematics or replacing it
  with an implementation proxy.
- Let smart constructors, local automation, and closure lemmas construct and
  propagate routine evidence. When the evidence cannot be established, fail
  with a domain-specific explanation; never fall back to a totalized operation
  in strict code.
- Check the domain obligations generated by the original expression before
  simplification. Rewriting `0 * (1 / x)` to `0`, for example, must not erase
  the obligation attached to the reciprocal in the source expression.
- Bundle a condition when it defines a stable mathematical object with useful
  closed operations. Keep one-off theorem conditions as hypotheses instead of
  proliferating increasingly specific dependent subtypes.
- Prefer one-way coercions from constrained objects to their ambient carriers.
  Use explicit or checked construction in the other direction, with stable
  coercion and rewriting normal forms.
- Design tactics together with the API. Proof automation should produce
  inspectable proof terms and make the mathematical reason for each step
  visible in the theorem interface.
- Test abstractions against real downstream formalizations before treating
  them as settled, and keep the motivating theorem, paper, or repeated proof
  pattern as evidence when deciding API boundaries. A facade is worthwhile
  when it restores a natural concept without creating a competing theorem
  ecosystem: a generic internal theorem may stay canonical internally while a
  thin mathematician-facing facade supplies the conceptual entry point. For
  set-system objects such as sigma-algebras and Dynkin systems, membership,
  inclusion, ordinary unions, generated structures, and the classical named
  proof principles should be available in forms that keep their mathematical
  distinctions.

#### Notation and compositional term structure

Notation is part of the public API, not merely a pretty-printing choice. Admit
it when it expresses a stable mathematical operation more clearly than
ordinary application and remains compositional: every visible operand has a
stable mathematical role, nested uses parse uniformly, and the form does not
depend on a custom elaborator consuming the surrounding application to recover
which declaration and arguments were intended.

- Keep a named declaration as the searchable, documented API head. Symbolic
  notation may be its conventional secondary surface, but users must be able to
  find, state, and inspect the same operation without first discovering a local
  parser rule.
- Prefer the bracket-free named application, membership, or projection whenever
  it is at least as clear as the custom form. Existing call-site volume or local
  familiarity does not justify retaining an otherwise inferior notation.
- Do not attach bespoke delimiters to an existing identifier to smuggle an
  ordinary, implicit, or instance argument into a form such as `P[c] x`. That
  shape resembles special Lean application syntax while actually being a local
  mini-language. Use ordinary application with named arguments, a projection,
  membership, or a distinct named relation or type whose term structure exposes
  the choice.
- Let automation infer implementation data that is uniquely determined by the
  visible mathematical operands. Do not use notation or elaborator search to
  hide a mathematically meaningful choice of topology, sigma-algebra, model,
  measure, or other ambient structure.
- Literal, binder, and conventional operator notation may remain when it adds a
  genuine compositional syntax rather than disguising ordinary application.
  Such notation still needs a stable named expansion and documentation.

The sigma-algebra interface is the boundary example. `MeasurableSet s` uses the
ambient sigma-algebra; `s ∈ 𝓐` exposes an explicit sigma-algebra; and
`MeasurableSet (𝓐 := 𝓐) s` retains the predicate head when elaboration
or theorem search specifically needs it. The former `MeasurableSet[𝓐] s`
escape hatch is deliberately not a fourth spelling.

#### Canonical multiargument functions and tuple presentation

Use the curried dependent-function type as the semantic normal form for an
ordinary multiargument function. The form
`(x : A) → (y : B x) → C x y` extends directly to dependent arguments;
forcing the same data into a one-argument tuple function instead requires a
dependent pair. In the nondependent case, `A → B → C` and `A × B → C`
are equivalent views of one function, not two mathematical APIs.

Classify the arguments by their mathematical role, not by a type isomorphism
alone. If the input is genuinely a point of a product, dependent sum, or
bundled pair, then the tuple is the mathematical domain rather than an
uncurried presentation of separate arguments.

- State definitions and theorems once in curried form when curry/uncurry is
  only computational transport. At a boundary that accepts a tuple function,
  use `↿f` for recursive uncurrying or `Function.uncurry f`; use
  `Function.curry g` in the other direction.
- Keep tuple-pattern syntax such as `fun (x, y) ↦ ...` available as a
  mathematician-facing presentation. Documentation should explain `↿f` in
  ordinary language as regarding the same multivariable function as a function
  of one tuple; users need not learn currying terminology to use the view.
- Do not add a parallel `foo_uncurry`, `foo_prod`, or similar theorem family
  merely because another spelling may help discovery. Prefer docstrings,
  generated documentation entries, editor support, normalization lemmas, or a
  small tactic that routes users to the canonical declaration. A documentation
  index may expose both spellings without adding a second kernel declaration.
- Update external-facing call sites to the canonical declaration or an inline
  transport. Do not generate compatibility declarations or maintain a legacy
  namespace to preserve a retired theorem spelling.

This rule applies only when the passage is beta/eta-equivalent presentation.
Separate curry or uncurry definitions and theorems are legitimate when the
passage carries mathematical content: for example, when bundled morphisms,
function-space topology, measurability, boundedness, or another structure adds
hypotheses or a nontrivial preservation statement. The compact-open interface
is a boundary example: `ContinuousMap.uncurry` and `Homeomorph.curry` require
local compactness assumptions, so they are not redundant spellings of the bare
function operations.

A prospective linter may flag a transported theorem when normalization reduces
its proof and statement to an existing declaration. Such a check must exclude
the structured cases above and report duplication evidence rather than infer
from an `_uncurry` suffix alone. The goal is one mathematical node with multiple
usable presentations, not multiple constants mistaken for independent facts.

#### Predicates, membership, and proof-carrying domains

Choose public syntax only after distinguishing the mathematical roles involved:

- `x : T` is an arbitrary object in an ambient type;
- `P x : Prop` asserts a property of that object; and
- `a : {x : T // P x}` is a first-class object whose property should persist
  through subsequent constructions.

For a `SetLike` structure that mathematicians regard as a collection,
membership is itself the carrier predicate applied to an object. Use `x ∈ C`
when the collection `C` is explicit and the relation is the standard
mathematical language. Retain an established named predicate when the relevant
structure is ambient, when the adjectival form is the conventional entry
point, or when theorem search and elaboration benefit from a recognizable
predicate head.

When both surfaces are public, make them definitionally equal when possible
and assign one normal form to each context. A transparent bridge may support
elaboration, but do not add a third notation or facade that merely restates the
same proposition. For sigma-algebras, the ambient proposition is
`MeasurableSet s`, explicit membership is `s ∈ 𝓐`, and a first-class measurable
set is `A : 𝓐`.

Promote a property to a proof-carrying domain only when it defines a stable
mathematical object with useful closed operations. Give that domain exactly the
closure its mathematics supports: finite Boolean closure does not imply
arbitrary closure, and countable closure should be exposed through operations
carrying the appropriate countability hypotheses rather than an unjustified
complete-lattice instance.

### Abstract but semantically exact

Faithfulness protects mathematical distinctions; it does not require a
set-theoretically literal implementation. Preserve domains, hypotheses,
partiality, canonical versus merely chosen data, quotient or equivalence-class
nature, uniqueness, and naturality when they are part of the intended object or
statement. Do not unfold a group into a carrier set and operations, a morphism
into graph data, or a quotient into representatives merely to look closer to a
foundation.

Bundled structures, morphisms, quotients, abstract types, and typeclass
interfaces are faithful when explicit, proved correspondences show that they
preserve the intended mathematical structure, distinctions, and operations.
An objectwise equivalence alone does not establish compatibility with the
relevant operations or naturality, and existence does not turn a chosen witness
into canonical data.

No single encoding is mandatory for partiality. Use a constrained input type
when the domain is itself a stable mathematical object, a proof argument when
the condition is local to one use, and an explicit partial-map object when its
domain and composition are part of the mathematics. Choose the interface that
keeps the semantic obligation visible without exporting incidental dependent
plumbing.

When reviewing a representation, ask first whether it creates a value,
proposition, or canonical choice that the mathematics does not provide. If it
does, repair the semantic boundary. If it merely hides a lower-level
set-theoretic construction while preserving the intended structure through a
proved interface, retain the abstraction. The target is abstract but
semantically exact, not convenience-driven totalization or
faithfulness-driven foundationalization.

### Mathematical vocabulary first; mathlib convention otherwise

A public declaration name is part of the library's mathematical language. The
existing mathlib4 naming convention remains the baseline; this fork does not
replace it with a new statement-to-name compiler. The fork makes one priority
explicit: established mathematical terminology outranks a paraphrase of the
formal statement. Where mathematical usage leaves the name open, follow the
ordinary mathlib4 convention and enforce it more consistently.

Apply the following priority order:

1. Use a registered standard mathematical name for a definition, theorem, or
   theorem family.
2. Use the owner namespace and a consistent family-variant suffix to
   distinguish standard formulations of the named result.
3. When no standard name exists, follow the current mathlib4 conventions for
   capitalization, namespace placement, conclusion-first descriptive names,
   `_of_` hypotheses, symbol vocabulary, and established short forms.
4. Record paper titles, theorem numbers, and textbook-local names only in
   documentation or source cross-reference metadata.

Do not coin an eponymous theorem label from the authors of a paper, its title,
or its bibliography key. A statement being proved by `Author` and `Coauthor`
does not establish "the Author--Coauthor theorem" as mathematical vocabulary.
Without independent evidence that such a name is conventional, use a
descriptive declaration name and write only that the result was proved by the
authors, with the paper in the references. In particular, author attribution
in prose must not be promoted to a bold theorem label or a named-result alias.
Remove unsupported coined labels when encountered; source attribution remains.

This is one rule for all mathematics, not a privilege reserved for a small list
of famous results. Eponymous names, descriptive names such as monotone
convergence, and symbolic names such as the π-λ theorem are treated alike when
they are established mathematical vocabulary. Fame, contributor preference,
and upstream precedent are not independent reasons to admit a name.

Maintain a versioned named-result terminology registry, not a registry of every
declaration. Each entry records the canonical ASCII spelling, mathematical
scope, independently authored citations, established alternative names, owner
namespace, and whether current usage identifies a primary formulation or a
family of coequal formulations. Ordinarily require two independent citable
mathematical sources; a single paper's label or one textbook's local terminology
remains source metadata. This confines the unavoidable human judgment to a
reviewable mathematical question: what do mathematicians call this result?

For a registered named theorem:

- If the literature has a clear primary formulation, that declaration receives
  the bare conventional name.
- Other standard formulations use the same conventional prefix followed by a
  consistent result-shape suffix.
- If there is no clear primary formulation, every formulation receives such a
  suffix; none is arbitrarily granted the bare name.
- An established alternative conventional name is a permanent exact alias to
  the canonical declaration. The alias is attribute-free and does not grow a
  parallel theorem family.

Normalize conventional names by one table: ASCII transliteration,
`snake_case`, punctuation removal, surname order, and standard abbreviations
are repository data rather than decisions repeated at each declaration.
Definitions use the same registry because introducing the conventional name of
a mathematical object is part of their purpose. Do not manufacture an
otherwise unnecessary named `Prop` merely to obtain the named-theorem rule.

For ordinary declarations without a registered mathematical name, retain
mathlib4's descriptive naming practice rather than attempting to serialize the
entire elaborated signature. A linter may enforce objective parts such as
casing, separators, registered vocabulary, namespace duplication, and the
shape of established theorem families. Semantic choices such as which
hypotheses a short name must mention remain review questions where mathlib4's
convention does not determine a unique answer.

For the π-λ theorem, mathematical usage therefore outranks the descriptive
fallback. The usual textbook membership formulation keeps
`SigmaAlgebra.DynkinSystem.pi_lambda`. The generated-structure equality should
share the conventional family prefix, for example
`SigmaAlgebra.DynkinSystem.pi_lambda_generateFrom_eq`, rather than remaining
discoverable only as `generateFrom_eq`. If a literature review instead found
the formulations genuinely coequal, both would receive consistent suffixes;
the registry would record that decision and its evidence.

Systematic repository-wide renaming is permitted only for the first priority:
declarations for results that already have an established mathematical name
but do not expose it consistently. That eligibility does not itself authorize a
migration; an actual audit and rename still require an explicit task,
dependency review, a complete consumer migration plan, and validation.

All inherited upstream declarations and existing fork declarations are
otherwise grandfathered. Adding or changing a proof, touching a file, moving a
module, or reconciling upstream does not create a rename obligation. A changed
public statement requires checking that its own name remains accurate, but it
does not enroll neighboring declarations in a naming cleanup. Ordinary
descriptive names may be improved when a focused API task includes them, but
they are not candidates for a mechanical mass normalization.

Enforcement is prospective and diff-scoped for new or deliberately renamed
fork declarations. The long-term target is a linter that validates the
objective mathlib4 rules and the named-result registry without attempting to
reject the inherited baseline or compute a unique semantic name for every
theorem.

### Proofs are API tests

Design and revise APIs from the proofs that actually use them. Begin with a
proof that is mathematically sound, faithful to the intended statement and its
domains, and conceptually well organized. If expressing that proof in Lean is
still complicated or tedious, treat the friction as an API design failure that
must be diagnosed, not as a normal cost to impose on downstream formalizers.
The defect may lie in the representation, theorem statements, normal forms,
missing conceptual lemmas or facades, coercions, elaboration, diagnostics, or
automation.

Do not rewrite a good mathematical proof into a library-internal decomposition
merely because the latter compiles. Adjust the API so the formal proof can
follow the mathematical argument. This principle never licenses a shorter proof
obtained by weakening the statement, hiding a hypothesis, erasing a domain
condition, or relying on totalized fallback semantics: ease of use counts only
after faithfulness has been preserved.

The intended standard is therefore not "strict but painful" or "convenient but
semantically loose." It is a faithful mathematical API whose routine
well-definedness work is handled by the library and whose genuine obligations
remain explicit.

Code quality requires new formalizations to maximize semantic coupling to the
existing library and to factor shared mechanisms at the most general natural
abstraction supported by real consumers. Here, coupling means using the same
canonical definitions, theorems, and proof infrastructure as related modules,
so that improvements propagate through one dependency path; it does not mean
introducing cyclic imports or leaking representation details. When two
developments share a proof engine, move that engine to their weakest natural
common abstraction and make the specialized results thin corollaries. Do not
retain a parallel private implementation merely because it follows one source
more literally.

Mathematical faithfulness constrains public definitions and names, domains,
hypotheses, conclusions, and theorem interfaces. It does not require proof
scripts or dependency graphs to imitate the source proof. Once the public
mathematics is faithful, prefer the proof with the greatest justified reuse,
coupling, and abstraction, even when its argument differs from the source.

When several proofs establish the same proposition, choose the canonical proof
by mathematical and architectural evidence rather than source length or raw
dependency counts:

1. Preserve the intended statement and make the mathematical explanation for
   the result visible in the dependency graph.
2. Reuse the closest conceptually appropriate established public abstraction.
   Do not unfold to definitions or reprove an established result merely to
   lower a dependency count, and do not invoke a remote classification theorem
   when a nearer structural result is the actual reason.
3. Avoid gratuitous logical strength, such as classical reasoning or choice
   when the intended statement and a usable proof do not need it. Treat
   `#print axioms` as a diagnostic, not an objective to optimize at the expense
   of the mathematical interface.
4. Prefer stable public APIs and proofs robust under refactoring over internal
   representations or broad, opaque automation searches.
5. Compare imports, elaboration and kernel cost, proof-term size, and
   readability after the preceding criteria are satisfied.

An alternative proof of the same proposition does not ordinarily justify a
duplicate public theorem. Retain the reusable intermediate theorem or
structure that the alternative proof exposes instead. Established
formulations, useful specializations, and exact aliases admitted by the naming
policy remain legitimate semantic entry points; historical or pedagogical
alternative proofs belong in exposition unless they add reusable mathematics.

Generality and abstraction are likewise evidence-driven. A proof using fewer
assumptions establishes a candidate generalization; it does not by itself show
that an ad hoc interface belongs in the public hierarchy. Generalize promptly
when the weaker setting is an established, recognizable mathematical
abstraction and the result remains usable. Otherwise wait for independent
downstream cases before adding new structure. Keep a specialization when it
provides a natural statement, namespace, or theorem-search entry point. The
goal is the most reusable natural theorem, not the weakest imaginable
assumptions or the highest possible abstraction level.

This evidence requirement governs new structure and weaker hypotheses. It does
not delay instances and closure lemmas that only propagate routine evidence
along standard implications, such as finiteness on rays implying local
finiteness; supply those together with the structure they serve.

### The existing design has no priority

Decide every design question by the rules of this document alone. The existing
implementation, whether inherited from upstream or written earlier in this
fork, has no priority over the design that these rules select, and the work
that changing it requires is never a reason to keep it. The number of proofs to
adapt, the files and consumers to migrate, the declarations to move or rename,
and the rebuild and verification time are scheduling concerns, not design
criteria. Compare the candidates as if none of them existed yet: by
mathematical fidelity, type-theoretic naturalness, quality of life, and the
architectural criteria of the preceding section, including placement in the
module whose subject a declaration belongs to and a single shared mechanism
instead of copies. Decline a reviewer's suggestion only for a reason grounded
in these rules; that a change would touch many proofs or rebuild the library is
not such a reason.

Rules that limit which declarations a task must change, such as the treatment
of existing names above, limit the scope of the task. They do not make the
existing form of a declaration preferable when a task decides its design.

## Conjectures and Proof Status

The fork adopts theorem-with-sorry roots and proof-dependency status.
This is the accepted design; the registry, analyzer, CI gate, and user
interfaces remain implementation work in
[`TODO.md`](TODO.md#conjectures-and-proof-status----accepted-design-pending-implementation).

### Epistemic kinds and a shared Lean interface

Each unresolved registered root has one of two epistemic kinds:

| Epistemic kind | Mathematical evidence |
| --- | --- |
| Genuine conjecture | The source presents the exact statement as a mathematical conjecture. |
| Awaiting formalization | The result has a mathematical proof or is established in the source, but its proof has not yet been formalized here. |

Both kinds have exactly the same Lean behavior: one ordinary theorem
declaration with the mathematical statement written directly in its type,
the same conjecture registry (provisionally `@[conjecture]`), and `by sorry`
as the placeholder for the entire proof. They use the same dependency
collector, placeholder-ownership checks, trusted axiom base, CI gate, and
proof-status computation. The kind is descriptive metadata, not a different
axiom, theorem type, proof mechanism, or exemption.

Record the source and statement correspondence supporting the epistemic
classification. An informal proof is evidence for Awaiting formalization; it
is not a Lean proof and does not remove the unresolved root. Changing only
the epistemic kind leaves the declaration, proof dependencies, and computed
formal status unchanged. In particular, an established mathematical theorem
may still be a dependency of a formally Conditional proof while its own
formal proof remains a registered placeholder.

Once a formal proof is supplied, replace the placeholder in the same
declaration, preserving its name and mathematical statement. Do not introduce
a separate `Prop` definition, a second proof declaration, or a named `axiom`
for either kind. A statement refuted by an existing theorem must not be
registered as an affirmative root of either kind; retain the refutation and
its historical source at their actual claim strength.

### Declaration and result interface

A result that uses a registered root states its ordinary mathematical
conclusion and uses the root's proof constant in its proof, directly or
through other declarations. Do not admit conjecture-antecedent metastatements
such as `RH → P`, or an `hRH` binder for the same antecedent, as the public
interface for these results. Ordinary mathematical hypotheses, parameters,
and implications remain part of their statements; they do not by themselves
make a result conditional. Conditionality is derived from proof dependencies,
not from an index of statement-level hypotheses.

Keep roots and dependent results in their mathematical subject modules.
Do not encode temporary proof status in a `Conditional/` directory or an
`_assuming_RH` name suffix. Authors maintain root identity, epistemic kind,
and source evidence; downstream conditional/unconditional labels are derived.

### Derived status and admission

Let `C_open` be all registered roots of either epistemic kind whose own
entire-proof placeholder remains unresolved. For a theorem `T`, let `D(T)`
be the members of `C_open` reachable through its transitive declaration
dependencies. Traverse the elaborated types and values of supporting
declarations as well as theorem proofs, so definitions, private helpers, and
opaque declarations cannot hide a dependency. An import alone is not a proof
dependency.

After admission checks pass, the formal proof statuses are exactly:

| Status | Meaning |
| --- | --- |
| Conjecture | A registered unresolved root of either epistemic kind with its permitted placeholder. Display the epistemic kind separately. |
| Conditional | A complete ordinary proof with `D(T)` nonempty. Show the actual root set and its epistemic kinds. |
| Unconditional | A complete ordinary proof with `D(T)` empty. |

Conjecture in this status vocabulary identifies the unresolved registry role;
only the epistemic metadata distinguishes a genuine mathematical conjecture
from an established result awaiting formalization. Unconditional is relative
to an explicitly reviewed trusted axiom base. Distinguish the standard Lean
logical axioms, any separately approved evaluation trust, registered root
placeholders, and unapproved axioms. A status describes the currently stored
formal proof; it does not establish an unresolved mathematical claim or
assert that its dependencies are logically necessary.

Incomplete/untrusted developments are rejected, not a fourth admitted status.
The CI gate must establish all of the following in the final elaborated
environment before producing an admitted status index:

- Every reachable `sorry` belongs to the designated entire-proof placeholder
  of a registered root of either epistemic kind. Registration does not excuse
  a partial proof containing additional holes.
- Declaration types contain no direct `sorry`/`admit` or synthetic holes.
  Traverse their dependencies under the same placeholder-ownership and
  trusted-axiom checks; legitimate uses of registered root constants
  contribute to `D(T)`.
- Ordinary theorem proofs and supporting definitions contain no local
  `sorry` or `admit`; indirect use of a valid root placeholder is allowed.
- Synthetic sorries, elaboration errors, unregistered placeholders, and
  unapproved axiom dependencies fail admission, including when reached through
  imported or private helpers.

Awaiting formalization admits a deliberately registered whole-statement
root; it does not turn arbitrary local proof gaps into acceptable results.
Audit placeholder ownership per declaration and occurrence; a shared
`sorryAx` dependency or deduplicated diagnostic output is insufficient.
Registry tagging or an epistemic label alone does not certify a proof.
Perform validation after theorem elaboration has completed, including
asynchronous theorem bodies.

When a root receives a complete formal proof, it leaves `C_open`; recompute
its status and every affected downstream status from that proof. If the new
proof still uses another unresolved root of either kind, it is Conditional on
the remaining roots. Only an empty unresolved dependency set makes it
Unconditional. The theorem names, statements, and subject placement stay
stable.

### User-visible evidence and migration

Provide a Lean/editor query, provisionally `#status T`, and generated
documentation and search labels. Expose formal status, root epistemic kinds
and source evidence, named unresolved dependencies, source links, and witness
paths. Support an unconditional-only filter and reverse queries for results
depending on a given root. Generate this information from the same validated
environment and reviewed trust base, for example as a build-generated JSON
index. Do not make readers inspect a proof DAG themselves or maintain a
second manual formal-status ledger.

The inherited `def RiemannHypothesis : Prop` in
`Mathlib/NumberTheory/LSeries/RiemannZeta.lean` is a migration target, not an
exemption from this design. Preserve its exact quantified zeta-zero statement
and exclusions while moving to the single registered theorem interface.
The same migration mechanism applies to inherited whole-statement aliases
for results awaiting formalization, including `FermatLastTheorem` and
`Nat.GrahamConjecture`; their mathematical status is recorded separately.

Migrate actual whole-root antecedent interfaces to ordinary conclusions and
proof dependencies, and remove obsolete whole-statement proposition aliases
rather than keeping them as parallel public APIs. Preserve ordinary
parameterized properties and their valid transport, equivalence, and
refutation lemmas. Apply the existing naming policy during the deliberate
migration. Recording this design does not implement the migration or the
proof-status infrastructure.

## Contributions, Curated Intake, and Canonicalization

This is a maintainer-curated library that accepts external pull requests which
follow the repository's mathematical, API, provenance, licensing, testing, and
review policies. Policy compliance makes a contribution eligible for review;
it does not guarantee merger. The maintainer may request revisions or decline a
contribution because of scope, duplication, maintenance cost, or conflict with
the fork's design direction.

The default branch is periodically rebased during upstream reconciliation.
Maintainers should batch those rewrites, avoid unnecessary merge-base churn
during active review, and may freeze reconciliation while a substantial pull
request is close to merger. Contributors own the mathematical content, original
implementation, and substantive review responses. Maintainers own integration
fallout caused solely by repository-driven upstream reconciliation or
fork-wide canonical API migrations, subject to the contributor granting branch
access when work must be pushed to the contributor's branch. The rebase and
force-update procedure for open pull requests is in `AI_AGENT_PROJECT.md`.

External formalizations may be proposed through a pull request or selected by
the maintainer from other repositories. A suggestion, public repository, or
valid result does not by itself create a review deadline or permanent backlog.
Intake may slow or stop when the available audit and migration capacity is
exhausted.

Project scale, popularity, and subject fashion are not admission criteria. A
small paper, a single theorem, or an obscure but reusable construction may be a
complete ingestion unit. Prefer preserving and integrating already formalized
mathematics over rebuilding it merely because it currently lives outside this
tree.

Evaluate candidate content separately from its current presentation. Admission
requires evidence for:

- a faithful, audited mathematical statement and either a complete proof under
  the conjecture and proof-status policy above or an explicitly registered
  unresolved root of either epistemic kind, with assumptions, axioms, generated
  material, and status explicit;
- a sufficiently identified source revision and provenance trail;
- permission to copy, modify, and redistribute every imported part;
- the absence of a materially equivalent canonical development, or a clear
  deduplication plan; and
- a technically credible route into the maintained library.

Naming, namespace layout, imports, abstraction level, proof locality, or use of
a noncanonical API are not by themselves reasons to discard valid mathematical
content. They are migration work owned by the maintainer. Once selected, a
development passes through mathematical audit, deduplication, faithful API
migration, repository-wide consistency work, and final verification before it
becomes canonical here. A raw external snapshot may be retained as evidence,
but it is not a second public API.

For an unfamiliar field, typechecking and general API taste do not establish
the right mathematical abstraction. Compare the source literature and other
formalizations, and obtain domain-appropriate review before canonicalizing the
interface. The policy is:

> Faithful mathematical content with an admissible proof status, provenance,
> and legal ingestibility determines eligibility for admission; repository
> consistency determines migration, not rejection. Actual admission remains a
> discretionary, evidence-based curatorial decision.

### Recovery modes for older formalizations

Classify recovery work by what must be preserved rather than calling every
project transfer a port:

- A **port** translates a development within the Lean ecosystem when its
  mathematical organization and principal abstractions remain suitable.
- A **reconstruction** rebuilds selected, audited theorem coverage on current
  foundations and APIs when the old architecture has been superseded. This is
  a mathematical rebase, not a Git-history rewrite.
- A **reformalization** reproduces mathematics from another prover or a
  materially different foundation and therefore requires a new trusted-boundary
  and foundation audit, not merely syntax translation.

For a reconstruction, the preservation invariant is an explicit mapping of
selected statements, hypotheses, constructions, and proof status to their
current counterparts. It is not the old directory tree, API, commit count, or
an unqualified promise to recover every theorem. Search for maintained
descendants and current-library overlap before starting; reuse sound modern
infrastructure and reprove only the unmatched mathematical layer. Completion
requires theorem-level correspondence evidence and end-to-end acceptance
targets, not a count of translated files.

Planning priorities and their still-open evidence gates live in
[`MIGRATION_BACKLOG.md`](MIGRATION_BACKLOG.md). Candidate presence there does
not admit a source or authorize intake.

## Source Repositories and Provenance

Many source repositories may feed one canonical editorial layer. Git supports
multiple named remotes, but a remote is only a local mechanism for discovering
and tracking refs. Adding or fetching a remote neither admits its content nor
authorizes a merge, copy, dependency, or push.

Choose an integration mode from the source relationship:

- For another fork with shared Git ancestry, inspect and selectively
  cherry-pick or port coherent commits.
- For an independent repository, do not merge unrelated histories merely to
  preserve its Git graph. Use a reviewed source port when the material is to
  become canonical here, or a Lake dependency when it should remain an
  independently versioned library.
- For reference-only candidates, record the source without importing code.

Every source and import must be recorded in `UPSTREAMS.md` with its exact
repository identity, revision, history relationship, license evidence,
integration mode, provenance, and status. Preserve applicable copyright,
license, attribution, and `NOTICE` material, and mark modified files as required
by the source license. A public GitHub repository without an explicit compatible
license is reference material only until permission is established; public
visibility is not an ingestion license.

Provenance must survive refactoring. Record which declarations or files came
from which source revision, what was rewritten, which mathematical or API
changes were made, and how the integrated result was verified. Do not replace
the original authorship record with the identity of the person performing the
migration.

## Relationship to Upstream

- `leanprover-community/mathlib4` is the baseline source currently tracked by
  the local remote named `upstream`; it is not the target audience for fork-only
  changes.
- `main` is a maintained Fidelity transformation stack over the latest
  reconciled `upstream/master`, replayed by rebase rather than merged. Keep its
  changes logically separated so the stack can be replayed and design
  decisions reviewed; this discipline serves the fork itself, not upstream pull
  requests. The branch model and reconciliation procedure are in
  `AI_AGENT_PROJECT.md`.
- Reuse upstream definitions and theorems when they are the design that the
  rules of this document select. The fork differs for a reason grounded in
  those rules, such as semantic or ergonomic friction exposed by actual
  formalization, not for novelty.
- Fork changes may deliberately break upstream API compatibility when a
  coherent migration establishes the interface that these rules select.
  Neither upstream compatibility nor the size of the migration is a reason to
  keep the inherited interface; evidence from downstream use, maintenance,
  performance, and verification bears on which interface the rules select, not
  on whether the inherited one is protected.
- Additional source repositories do not become alternate design authorities.
  Material becomes part of this library only through the same faithful,
  canonicalizing integration process.

## Total-Inverse Migration Contract

The inverse and exact division migration replaced the former totalized
interfaces and migrated their affected consumers in one delivery, including
the rational operators. Final verification was recorded on 2026-11-20 in the
[completed migration entry](TODO.md#xl----foundational-work-implementation-requires-an-explicit-task).
The requirements below define the scope and acceptance criteria of that migration.

### Inventory and mathematical contracts

Map the current hierarchy, notation, instances, rational casts and scalar
operations, characteristic-sensitive behavior, theorem dependencies,
simplifier rules, tactics, and analysis APIs that rely on total inverse or
division. Classify totalizations rather than searching and replacing blindly:

1. independently meaningful total mathematical objects supported by exact
   literature and specifying properties;
2. implementation extensions of the inverse/division interfaces being replaced,
   which must be removed with those interfaces;
3. totalizations that leak invalid-domain semantics through a public
   declaration, notation, coercion, instance, or mathematical name and must be
   removed.

Record the exact specification and domain of each operation. A nonzero
element of a field is a unit. Inversion in a general ring requires a unit,
and inversion of a finite square matrix over a commutative ring requires a
unit determinant.

### Euclidean quotient and remainder

For a chosen Euclidean division algorithm, the reconstruction identity
`b * q + r = a` determines the quotient `q` from the remainder `r` by
cancellation when `b ≠ 0`. The remainder decreases in the chosen well-founded
relation on that domain. Such a divisor can be a nonunit. At `b = 0` the
identity forces `r = a` and leaves `q` undetermined. Congruence modulo zero
is equality, so the remainder at zero has a specification independent of
any quotient value.

`EuclideanDomain.quotient a b hb` carries the nonzero proof. Ordinary `/`
in a generic Euclidean domain uses this quotient with routine proof search.
The remainder has its own law at zero. If the gcd is zero, the least common
multiple is zero by its divisibility specification. The nonzero-gcd branch
divides the product by the gcd.

`Field.toEuclideanDomain` explicitly supplies this structure for a field.
`Field.quotient_eq_div` gives agreement with checked exact division when
`b ≠ 0`. Field `/` syntax requires invertibility evidence even with the
Euclidean structure installed locally.

`Int.euclideanDomain` calls Lean's native integer algorithm on the checked
nonzero domain. Native `Int` and `Nat` division belong to the official Lean
toolchain and have a separate domain audit in [`TODO.md`](TODO.md).

### Final algebra and operational interface

- Separate the property that nonzero elements admit inverses from the operation
  on invertible elements. The ordinary field hierarchy must not supply an
  unconditional inverse or division operation on its ambient carrier.
- Reuse or adapt `IsField` for the property-level core and `Units` for the
  multiplicative carrier. Construct units directly from existence evidence;
  remove conversions that rebuild a totalized field as a compatibility route.
  Validate the concrete hierarchy and inference in real consumers.
- Reuse unit inversion, division, integer powers, extensionality, and coercions.
  Establish the equivalence with nonzero field elements without introducing a
  competing nonzero-carrier theorem ecosystem. Mixed division accepts an
  arbitrary ambient numerator and a unit denominator, as existing `divp` does.
- Supply checked construction, predictable coercions, rewrite lemmas, useful
  diagnostics, and denominator-clearing automation together with the API.
  Construction should find routine local evidence and propagate closure facts.
- Keep mathlib's established theorem names for statements about the faithful
  operations. The namespace that implements checked construction is not
  mathematical vocabulary, and goals display the operations with ordinary
  notation. Each fact has one canonical declaration at the exact generality
  of its content: the identity `a * a⁻¹ = 1` for a unit `a` is one theorem for
  monoids, groups with zero, and fields. Where the established name belongs to
  a retained group or division-monoid theorem about a total inverse, the
  partial-inverse theorem takes the `₀` suffix, as mathlib does for groups with
  zero.
- Do not request invertibility evidence that a term already carries. A theorem
  takes the evidence of each checked operation in its statement as an implicit
  argument unified from that term, unless a genuine hypothesis such as
  `0 < c` already implies it. Hypotheses with mathematical content, such as a
  sign condition or a nonzero numerator, remain explicit.
- Remove statements that hold only because of a value at an invalid
  denominator, such as `0⁻¹ = 0`, `a / 0 = 0`, and cancellation inequalities
  that exist only to absorb the zero case. Restate a statement whose earlier
  form omitted a needed domain condition on its correct domain.
- The inverse, quotient, and integer power of a function are the checked
  operations of the function monoid, defined exactly when every value is
  invertible. When a statement needs a quotient only at the points of a set,
  as in `∑ i ∈ s, f i / g i` or `MonovaryOn f⁻¹ g s` with `g` or `f` positive
  on `s`, index by the set itself, for example `∑ i : s, f i / g i`, and take
  the evidence from membership. Requiring invertibility at every point would
  shrink the statement to a convenient sufficient condition.
- A construction whose value is a quotient that can fail to exist, such as a
  convergent `A n / B n` of a generalized continued fraction, takes the
  invertibility of its denominator as an argument; evaluation that may meet
  a non-invertible denominator returns an explicit partiality type such as
  `Option`, and the identification of two such constructions is stated where
  both are defined.
- Account for negative powers, rational casts, and rational scalar operations.
  Nonnegative powers retain the whole ambient domain; negative powers require
  invertibility. These are algebraic powers: the monoid law `a ^ 0 = 1` is the
  empty-product case, including `0 ^ 0 = 1`; a positive power of zero is zero.
  An integer-exponent interface therefore requires invertibility only when
  the exponent is negative. This does not specify real-exponent powers or
  limits of the indeterminate form `0 ^ 0`.
  A unital ring homomorphism from all rationals into a field
  requires characteristic zero; in positive characteristic, evaluation of a
  rational requires its reduced denominator to remain nonzero. Checking a raw fraction expression
  must precede cancellation, even if its reduced rational value is admissible.
- Migrate notation, implicit instances, concrete field structures, simplifier
  rules, and tactics so that none can reintroduce the retired totalized
  operation. Removing a named function alone is insufficient.

### Rational foundation and proof infrastructure

Complete this migration on official Lean under the operator-fidelity boundary
above. Retain core `Rat` as a legitimate rational carrier; no independent
rational representation is required merely to exclude its unfaithful
operators. Keep faithful arithmetic and nonnegative powers after their
dependency audit. Construct checked fractions and reciprocals from valid data,
using the already checked `Rat.normalize` where appropriate.

The operation inventory must include `Rat.inv`, `Rat.div`, negative integer
powers, unchecked `mkRat` and `Rat.divInt`, and every notation, cast, instance,
or automation path that introduces them. Banning only the name `Rat.inv` is
insufficient. Fork mathematical definitions and statements must not depend on
the selected retired operations, directly or through a strict wrapper.

Remove their replaceable uses from fork-controlled proofs and proof engines
as well. Retain legitimate core-rational coefficient arithmetic; keep an
unavoidable unfaithful operation in official Lean proof infrastructure only
under the recorded proof boundary above. Do not patch core quotation or Grind
to remove it. Audit the fork's adapters and emitted terms instead. In
particular, a `Field.toGrindField` bridge must not restore unconditional `Inv`,
`Div`, or negative powers on the fork's mathematical field interface through
the instances of core `Lean.Grind.Field`.

### Required acceptance cases

Verify these behaviours in the completed implementation, using small internal
experiments where needed to settle the design:

- repeated multiplication, division, and inversion of nonzero objects do not
  ask users to resupply facts already carried by those objects;
- a local proof that a denominator is nonzero is found by checked construction;
- nonzeroness of a product is propagated, while nonzeroness of a sum is not
  invented;
- simplification cannot make an original denominator obligation disappear;
- different proofs of the same proposition do not create user-visible identity
  or rewriting friction;
- numerals are not assumed nonzero without the characteristic hypotheses needed
  in the ambient algebraic structure;
- mathematical declarations and operations cannot fall back to a legacy
  totalized `/` or inverse through any implicit or explicit fork interface;
- no mathematical definition, statement, notation, coercion, instance data
  field, delaborator, or private semantic helper retains a retired totalized
  operation; retaining the carrier `Rat` is not a violation;
- elaborated declarations and their semantic definition dependencies are
  independent of the selected retired operators, including uses hidden by
  aliases, wrappers, casts, and instance synthesis;
- replaceable proof and automation uses have been removed, while unavoidable
  official-toolchain proof dependencies have their ownership and faithful
  boundary recorded; imported presence alone is not a failure;
- error messages identify the failed mathematical obligation instead of exposing
  an undiagnosed coercion or instance-search failure;
- pretty-printing exposes only the faithful public operation and never
  normalizes a term back to a retired totalized form;
- nested fractions, function composition, and denominator clearing remain
  readable in a real downstream development.

Exercise a real algebraic consumer such as Cramer's rule, including solution
and uniqueness, and test both abstract property-only contexts and concrete
field contexts. Positive examples alone do not establish the domain boundary;
pin invalid-input failures to their actual mathematical obligations.

### Analysis within the same migration

A field's nonzero carrier is suited to multiplicative algebra but is not closed
under ambient addition and does not contain the ambient zero. It therefore
cannot simply replace the ambient vector-space domain. Differentiation,
continuity, integration, and other APIs for functions defined on open subsets
or local domains need their own design. Establish the appropriate open-set,
local-function, or chart interfaces and migrate affected analysis consumers in
the same delivery. A successful algebra experiment does not discharge these
obligations or justify leaving the old analysis implementation in place.

A function that is defined only on a local domain is a function on that domain,
read in coordinates: `f : D → F` with `coord : D → E`, where `coord` defaults to
the identity for an ambient function. Derivative relations take this form, and
so do convexity and concavity (`ConvexOn 𝕜 s f coord` for `s : Set D`), so that
`x ↦ x ^ n` with a negative exponent is convex on the positive cone as a
function on that cone, not through a total extension with arbitrary values
(user decision, 2026-10-25). Do not state such results by quantifying over
total extensions, and do not add a second predicate for partial functions.

### Completion

Inspect and migrate all in-scope definitions, theorems, casts, scalar actions,
matrix APIs, instances, notation, tactics, analysis consumers, tests, and
documentation. No old/new API pair or private compatibility layer may remain.
Run the full final-state build, test, lint, generated-import, and negative-scan
checks specified in `AI_AGENT_PROJECT.md`. Required inverse/division consumers
cannot be deferred to claim completion. Record genuinely independent lower-level
problems under the dependency boundary above, with the proofs needed to keep
the completed inverse/division interface faithful.

## Current Non-goals

- Treating this documentation update as authorization to implement the
  total-inverse migration or rename its hierarchy and consumers.
- Repairing every documented fallback now. The 2026-10-20 inventory of
  documented fallbacks is recorded as candidates in `TODO.md`; an audit of every
  totalization in the repository, declaration by declaration, remains out of
  scope.
- Preserving fork-only changes in a form suitable for an upstream pull request.
- Modifying or maintaining Lean's toolchain, banning the carrier `Rat`, or
  eliminating unavoidable official-toolchain dependencies from proof terms.
