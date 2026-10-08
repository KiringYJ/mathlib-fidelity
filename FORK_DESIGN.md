# Fork Design Philosophy and Roadmap

## Status

This document records the accepted direction of the personal fork. It is a
design contract, not a claim that the described APIs already exist.

The interface goals below are adopted. The hierarchy split, proposed roadmap
API names, representation, automation, and migration sequence are candidates
that require prototypes and downstream evaluation; they are not an implemented
or validated API. The total-inverse migration is deferred, and this document
does not authorize code changes. Begin that work only in a task that explicitly
requests it, after inspecting the then-current dependency graph and
establishing a small prototype.

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
- A total fallback is not a second permanent public API. It may exist only as
  a private transitional implementation bridge during a migration, with a
  stated removal condition. The public boundary must prove that its fallback
  is unreachable or that the result is independent of the chosen value.
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
  implementation bridge: no public definition unfolds to it, so it needs no
  removal condition.
- If mathematical literature defines a genuinely total object on the same
  inputs, including the degenerate cases, treat that as an independent
  mathematical object with its own specifying properties rather than as a
  retained extension of the partial operation. Record the exact source and
  convention; a renamed operation or source-code docstring is not evidence.
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
- Distinguish a strict public interface from a strict implementation. A proved
  bridge may initially reuse a totalized implementation on its valid domain,
  but only as private transitional machinery. Track and remove that dependency
  before declaring the migration complete.

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
- If an external compatibility boundary requires a named transported theorem,
  generate it mechanically as an attribute-free compatibility declaration or
  place it in a dedicated compatibility namespace. It must remain visibly
  derived and must not acquire its own theorem ecosystem.

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
dependency review, compatibility plan, and validation.

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

- a correct and faithful mathematical statement and proof, with assumptions,
  axioms, `sorry`s, generated material, and conditional status made explicit;
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

> Mathematical validity, provenance, and legal ingestibility determine
> eligibility for admission; repository consistency determines migration, not
> rejection. Actual admission remains a discretionary, evidence-based
> curatorial decision.

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

## Deferred Total-Inverse Roadmap

The names in this section, including `TotalizedField` and `NZ`, are working
prototype names, not candidate permanent public APIs. Any totalized structure
introduced by the prototype is private transitional machinery and must be
removed before the migration is complete.

### 0. Inventory before refactoring

Map the current hierarchy, notation, instances, rational casts and scalar
operations, characteristic-sensitive behavior, theorem dependencies,
simplifier rules, tactics, and analysis APIs that rely on total inverse or
division. Classify totalizations rather than searching and replacing blindly:

1. independently meaningful total mathematical objects supported by exact
   literature and specifying properties;
2. private implementation extensions that may exist only as transitional
   bridges with explicit removal conditions;
3. totalizations that leak invalid-domain semantics through a public
   declaration, notation, coercion, instance, or mathematical name and must be
   removed.

Record both interface and implementation status for each migrated area. A
strict statement proved through a validated bridge is progress, but it is not
evidence that all totalized dependencies have disappeared.

### 1. Build an isolated algebra prototype

Test the candidate architecture away from the production hierarchy before any
global rename:

- separate the property that nonzero elements admit inverses from the data of a
  chosen total inverse and division operation;
- evaluate reusing or adapting the role currently played by the `IsField`
  predicate. It already records a property-level existence claim, but it is not
  a strict operational API, and its conversions back to the current hierarchy
  construct totalized inverse data;
- isolate any required totalized implementation behind a private transitional
  adapter and a one-way bridge to the strict property, without an automatic
  bridge that recreates totalization in the reverse direction; record the
  adapter's consumers and removal condition;
- account for all data and laws carried by the current hierarchy, including
  rational casts and scalar operations, rather than treating the work as a
  rename of one inverse field;
- for fields, use one stable nonzero-carrier interface for multiplicative work,
  connected to existing units theory by proved equivalences rather than
  competing global instances;
- cover mixed operations explicitly: division may have an arbitrary ambient
  numerator while its denominator carries nonzero evidence;
- prototype checked construction, predictable coercions, extensionality,
  rewrite lemmas, and denominator-clearing tactics;
- isolate legacy notation and instances strongly enough that strict code cannot
  resolve an unproved division through the old totalized operation.

Outside a field-like setting, nonzero does not by itself imply invertible. Do
not export the prototype's nonzero-carrier operations under weaker assumptions
until their actual algebraic requirements have been established.

The prototype must include negative tests. It is not successful merely because
positive examples elaborate.

### 2. Prototype acceptance cases

At minimum, verify the following behaviours before considering a production
migration:

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
- strict code cannot fall back to a reachable legacy totalized `/` or inverse;
- no public declaration, notation, coercion, instance, or delaborator exposes
  a transitional totalized operation;
- error messages identify the failed mathematical obligation instead of exposing
  an undiagnosed coercion or instance-search failure;
- pretty-printing exposes only the faithful public operation and never
  normalizes a term back to a transitional totalized form;
- nested fractions, function composition, and denominator clearing remain
  readable in a real downstream development.

### 3. Migrate only after the prototype survives use

If a later task authorizes the migration and the prototype meets its acceptance
criteria, first preserve a compiling compatibility state, then weaken
dependencies module by module. A possible sequence is:

1. introduce the strict property and a private transitional adapter;
2. identify and instrument legacy consumers that still depend on totalized
   behavior without promoting that dependency to a new public requirement;
3. provide proved adapters on valid domains;
4. migrate coherent downstream slices to the strict API;
5. weaken module requirements only after checking that their statements and
   implementations no longer rely on totalized semantics;
6. add checks that prevent new unnecessary dependencies on the totalized layer;
7. remove every transitional totalized adapter and compatibility surface after
   its consumers and replacement paths are known; the migration is not complete
   while any remains.

Do not begin with a repository-wide mechanical rename that has not accounted
for casts, notation, tactics, instance coherence, performance, and downstream
breakage.

### 4. Treat analysis as a separate design boundary

A field's nonzero carrier is suited to multiplicative algebra but is not closed
under ambient addition and does not contain the ambient zero. It therefore
cannot simply replace the ambient vector-space domain. Differentiation,
continuity, integration, and other APIs for functions defined on open subsets
or local domains need their own design. Do not claim that a successful algebra
prototype solves the analysis migration. Establish the appropriate open-set,
local-function, or chart interfaces before porting analysis code.

## Current Non-goals

- Starting the total-inverse migration.
- Renaming `Field`, `DivisionRing`, `GroupWithZero`, or their consumers now.
- Introducing the provisional `NZ`, checked-division, or tactic APIs now.
- Auditing every existing totalization in the repository now.
- Preserving fork-only changes in a form suitable for an upstream pull request.
