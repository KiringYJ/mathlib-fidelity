<!-- Use a Conventional Commit title, for example: feat(scope): explain intent. -->

## Summary

<!-- Explain the problem, intended outcome, and scope. -->

## Mathematical and API fidelity

<!--
Describe the relevant mathematical objects, domains, hypotheses, and
conclusions. For a migration, describe the final canonical API, all affected
consumers, and removal of obsolete notation, instances, aliases, and private
compatibility machinery. Write "Not applicable" if the change has no
mathematical or API surface.
-->

## Sources and provenance

<!--
Identify exact sources, revisions, licensing, authorship, attribution, NOTICE
requirements, axioms, sorry declarations, generated artifacts, and overlap
when external material is involved. Write "No external material" otherwise.
-->

## Verification

<!-- List the exact commands run, their results, and any checks not run. -->

## Limitations and follow-up

<!--
State known gaps or write "None". For migrations, link independent foundational
TODO items and explain the proved boundary that permits their deferral.
Unfinished in-scope proofs, consumers, or removals mean the migration is
incomplete, not an accepted partial delivery.
-->

## Moving-base acknowledgement

<!--
The target branch `main` may be periodically rebased onto `upstream/master`.
Maintainers batch these reconciliations and may help resolve repository-driven
fallout when branch access is available. Enabling maintainer edits is optional;
review GitHub's workflow-secret warning before granting that access on a fork
containing GitHub Actions workflows.
-->

## Checklist

- [ ] I read `.github/CONTRIBUTING.md` and the linked fork policies.
- [ ] The PR targets `main` and contains one coherent change.
- [ ] Repository artifacts, commits, and this description are in English.
- [ ] Relevant source, license, provenance, and verification information is
      included.
- [ ] Any migration completes its selected scope without compatibility or
      transitional layers; remaining foundational dependencies have precise TODO
      entries and proved boundaries, and final-state checks cover the change.
- [ ] No credentials, private paths, generated noise, or unrelated changes are
      included.
