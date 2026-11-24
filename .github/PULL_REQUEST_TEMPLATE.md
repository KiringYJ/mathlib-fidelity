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
For operator migrations, explain removal of unfaithful operations from elaborated
statements and mathematical definitions, including hidden dependencies and
replaceable proof uses. Identify unavoidable official-toolchain proof dependencies
and their faithful boundary. Retain official Lean and legitimate carriers such as Rat.
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
State known gaps or write "None". For migrations, link issues for independent
foundational work and explain the proved boundary that permits deferral.
Unfinished in-scope proofs, consumers, or removals mean the migration is
incomplete, not an accepted partial delivery.
-->

## Checklist

- [ ] I read `.github/CONTRIBUTING.md` and the linked fork policies.
- [ ] The PR targets `main` and contains one coherent change.
- [ ] Repository artifacts, commits, and this description are in English.
- [ ] Relevant source, license, provenance, and verification information is
      included.
- [ ] The change meets the regression coverage policy in `.github/CONTRIBUTING.md`.
- [ ] Any migration completes its selected scope without compatibility or
      transitional layers. Issues for remaining foundational dependencies record
      their proved boundaries, and final-state checks cover the change.
- [ ] No credentials, private paths, generated noise, or unrelated changes are
      included.
