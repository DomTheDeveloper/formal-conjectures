# WOWII 145 Public Novelty and Priority Audit Certificate

**Candidate:** Written on the Wall II Graph Conjecture 145  
**Upstream repository:** `google-deepmind/formal-conjectures`  
**Solution branch:** `DomTheDeveloper:agent/solve-wowii-145-current`  
**Audit time:** July 21, 2026, 3:01 PM Pacific Time  
**Purpose:** Determine whether a competing Formal Conjectures pull request or an earlier publicly indexed solution was discoverable immediately before submission.

## Certified conclusion

1. **No competing open upstream pull request existed at the audit time.**
2. **No closed or merged upstream solution pull request was found** under the exact theorem name, aliases, file name, or distinctive invariant terms.
3. **No earlier publicly indexed mathematical or Lean solution was found** in the searched sources.
4. This is necessarily a certificate about public, accessible, indexed material. It cannot exclude private repositories, unpublished manuscripts, deleted material, or pages that were not indexed by the searched services.
5. Because the present proof is now public, the precise priority claim is that **no earlier or competing publicly discoverable solution was found immediately before publication of this proof**.

## A. Exhaustive open-PR enumeration

The complete open-pull-request listing of `google-deepmind/formal-conjectures` contained four pull requests at the audit time:

| PR | Subject | Changed files |
|---|---|---|
| [#4515](https://github.com/google-deepmind/formal-conjectures/pull/4515) | WOWII 100 proof | `FormalConjectures/WrittenOnTheWallII/GraphConjecture100.lean` |
| [#4497](https://github.com/google-deepmind/formal-conjectures/pull/4497) | WOWII 322 proof | `FormalConjectures/WrittenOnTheWallII/322.lean`; `FormalConjectures/WrittenOnTheWallII/GraphConjecture322.lean` |
| [#4496](https://github.com/google-deepmind/formal-conjectures/pull/4496) | WOWII 314 proof | `FormalConjectures/WrittenOnTheWallII/314.lean` |
| [#4443](https://github.com/google-deepmind/formal-conjectures/pull/4443) | WOWII 160 correction | `FormalConjectures/WrittenOnTheWallII/160.lean` |

None changes `FormalConjectures/WrittenOnTheWallII/GraphConjecture145.lean`. None claims to solve WOWII 145.

This is stronger than a title-only search: every open upstream pull request was enumerated and its changed filenames were inspected.

## B. All-state upstream PR and issue searches

The following exact or high-specificity terms were searched across open, closed, and merged pull requests and issues:

- `GraphConjecture145`
- `conjecture145`
- `WOWII 145`
- `Written on the Wall II Conjecture 145`
- `localIndependenceMin`
- `indepNeighborsCard`
- `eccSet G (maxEccentricityVertices G : Set α)`
- `largestInducedTreeSize`

The only relevant upstream pull request was [#3820](https://github.com/google-deepmind/formal-conjectures/pull/3820), which introduced the numbered WOWII conjecture files, including Conjecture 145, as a statement-formalization batch. It did not provide or claim a solution.

No earlier closed or merged solution pull request was found. Searches using the same aliases found no upstream issue claiming or recording a solution to WOWII 145.

## C. Global GitHub PR and code searches

Global searches for the exact theorem and file aliases found only:

- fork-internal verification PR [#59](https://github.com/DomTheDeveloper/formal-conjectures/pull/59);
- fork-internal verification PR [#60](https://github.com/DomTheDeveloper/formal-conjectures/pull/60);
- `crl` verification harness PR [#190](https://github.com/DomTheDeveloper/crl/pull/190);
- unrelated pull requests whose numeric identifier happened to be 145.

The three relevant PRs explicitly describe themselves as internal verification or audit harnesses, not upstream competing solution submissions.

GitHub code search for `GraphConjecture145` returned the canonical upstream conjecture file and an unrelated WOWII 146 build transcript mentioning the filename. A search combining `localIndependenceMin` and `largestInducedTreeSize` returned only the canonical upstream Conjecture 145 file before this proof became indexed.

No independent Lean proof repository was found.

## D. Broader web and literature search

Queries included:

- `"Written on the Wall II" "Conjecture 145" graph proof`
- `"WOWII 145" graph conjecture solution`
- `"GraphConjecture145" Lean proof`
- `"localIndependenceMin" "largestInducedTreeSize"`
- `"tree(G)" "ecc(B)" graph`
- `"ecc(B)" "lambda_min" graph conjecture`
- `"largest induced tree" "local independence" graph`
- `site:arxiv.org "Written on the Wall II" graph conjecture`

The relevant returned material consisted of the original Written on the Wall II source/status material and Formal Conjectures mirrors or generated indexes. No paper, preprint, blog post, repository, or independent proof matching Conjecture 145 was found.

## E. Statement-fidelity check

The upstream theorem was inspected directly before the solution branch was prepared. It was:

- tagged `@[category research open, AMS 5]`;
- stated with the original connectedness and positivity hypotheses;
- closed only by `sorry`;
- unchanged in mathematical content by this submission.

The linked Lean development proves the exact theorem. It is not:

- a correction to a mistranscribed invariant;
- a weakened special case;
- a result under stronger hypotheses;
- merely a formalization of a known cited theorem.

## Formal-proof and verification references

- [Immutable standalone Lean proof](https://github.com/DomTheDeveloper/crl/blob/2ee448baa80c98f0c8b9a0c1c3d9421200f99aa5/math/wowii145/WOW145/145.lean)
- [Standalone proof commit](https://github.com/DomTheDeveloper/crl/commit/2ee448baa80c98f0c8b9a0c1c3d9421200f99aa5)
- [Exact upstream submission commit before this certificate](https://github.com/DomTheDeveloper/formal-conjectures/commit/39297c37f51d2af2142af316f40d95f13c359e84)

The pinned Lean 4.27.0 build and direct theorem-file check passed. The terminal axiom audit reported only:

```text
[propext, Classical.choice, Quot.sound]
```

No `sorryAx`, `admit`, `native_decide`, or project-specific axiom occurs in the proved theorem.

## Defensible priority wording

> Immediately before submission, every open pull request in `google-deepmind/formal-conjectures` was enumerated and its changed filenames were inspected; none touched `GraphConjecture145.lean` or claimed WOWII 145. All-state pull-request and issue searches, global GitHub code and PR searches, and exact web and literature searches found no earlier or competing public solution. This is a time-stamped public negative-search certificate; it cannot exclude private, deleted, unpublished, or unindexed work.