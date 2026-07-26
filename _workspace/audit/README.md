# Open-problem audit

A systematic classification of every `@[category research open]` declaration in
`FormalConjectures/`. The goal is to separate three things that are easy to conflate:

1. **Mathematical status** — is the underlying problem actually open?
2. **Formalization faithfulness** — does the Lean statement mean what the source says?
3. **Actionability** — what is the fastest legitimate path to a kernel-verified proof?

> **Nothing in this audit is a proof.** No Lean file was modified and no build was run.
> Every "solved" or "solvable" entry is a *static-analysis claim* that must survive
> `lake --wfail build` and an axiom audit before it may be described as solved.
> See [Verification standards](#verification-standards).

## Status

| | |
|---|---|
| Declarations in scope | 1163 (across 622 files, `Util/` and `Subsets/` excluded) |
| Classified so far | see [INDEX.md](./INDEX.md) header |
| Adversarially verified | see the `verifier:*` flags in the per-directory reports |

Scope note: `FormalConjectures/Util/` matches `research open` only in attribute
documentation and linter tests, and `FormalConjectures/Subsets/` contains benchmark
*name lists* rather than statements. Both are excluded by design.

## Categories

Each declaration gets exactly one primary category, and optionally a secondary one.

| Cat | Name | Meaning |
|---|---|---|
| 0 | Already solved internally | Proved somewhere in this fork's ecosystem (merged/unmerged PR, branch, campaign directory, duplicate theorem) even though the canonical file still says `sorry`. |
| 1 | Already solved externally | The intended problem is settled outside this repo (published theorem, formal proof elsewhere, erdosproblems.com status). |
| 2 | Trivially or easily solvable | The current Lean theorem can very likely be closed quickly with existing tactics/Mathlib lemmas or a small witness. |
| 3 | False / refutable as stated | The formal statement is false — explicit counterexample, wrong recurrence, truncation artefact, missing hypothesis. |
| 4 | Vacuously true / accidentally weakened | Provable, but only because the formalization is weaker than intended (contradictory hypotheses, quantifier order, degenerate witness, `answer()` echo). |
| 5 | Solved mathematically, not yet formalized | A valid human proof exists; Lean translation is substantial work. |
| 6 | Computationally solvable with certificate | Finite computation plus a kernel-checkable certificate (SAT/LRAT, exhaustive search, exact LP, Gröbner). |
| 7 | Plausibly solvable with moderate formal work | Tractable with known techniques; several nontrivial lemmas. |
| 8 | Deep but approachable research problem | Genuinely open, with identifiable avenues and a stated key obstruction. |
| 9 | Major open problem / currently infeasible | Recognized hard open problem or needs a breakthrough. |
| 10 | Cannot classify without correction | Statement or source too ambiguous to evaluate; never classified as solved. |

Category 4 deserves emphasis: these are theorems a prover can "close" without doing the
intended mathematics. They are the repository's most damaging defect class, because a
green build looks like success. The most common instance found is the **`answer()` echo** —
a goal of the form `answer(sorry) = e` or `answer(sorry) ↔ P` where `e`/`P` is already in
scope, so `answer := e` closes it by `rfl`. That is a benchmark integrity problem, not a
solution.

## Audit fields

Per-directory reports (`ErdosProblems.md`, `Wikipedia.md`, …) carry, for every declaration:
repository file and theorem name, plain-English statement, original source, primary and
secondary category, whether the Lean statement matches the intended problem
(`yes`/`suspect`/`no` plus a note), known proof/counterexample/PR/literature status,
proposed next action, mathematical difficulty (1–10), Lean formalization difficulty (1–10),
compute requirement, confidence, and the supporting evidence.

## Method

1. **Inventory** — `data/extract_inventory.py` parses every `@[category research open]`
   attribute with its declaration, docstring, AMS codes, `answer()` usage, and module
   references into `data/inventory.json`.
2. **External ground truth** — `data/erdos_states.json` is today's authoritative status for
   all 1217 problems from [teorth/erdosproblems](https://github.com/teorth/erdosproblems).
   `data/erdos_mismatches.json` is the repo's own `scripts/check_erdos_status.py` output.
3. **Prior-work registers** — `data/pr_register.json` (all 262 PRs of this fork) and
   `data/campaign_register.json` (19 internal solving campaigns, see [CAMPAIGNS.md](./CAMPAIGNS.md)).
4. **Triage** — one agent per batch of ~24 declarations reads each Lean file in full
   (definitions above a theorem are where loopholes hide), reconstructs the intended
   problem, hunts for the defect classes below, consults the registers, and assigns a
   category with all audit fields.
5. **Adversarial verification** — every category 0–4 claim and every `match: no` claim is
   re-attacked by a second agent whose default stance is that the claim is wrong.
   Outcomes appear as `verifier:confirmed` / `verifier:revised` / `verifier:rejected`
   flags, with the triage category preserved when it was overridden.

Defect classes explicitly hunted: truncated `ℕ` subtraction; junk values from division by
zero; quantifier order and existential-witness scope; vacuous or contradictory hypotheses;
missing positivity/nonemptiness/distinctness/finiteness conditions; `Finset`/`Set`/`Type`
mismatches; off-by-one and indexing conventions; wrong constants; `answer()` encodings that
trivialize the question; definitions admitting degenerate objects.

## Verification standards

A formal solution may be called complete only when it:

- proves the canonical theorem, not an easier replacement;
- matches the intended definitions and quantifiers;
- compiles in the repository's pinned Lean and Mathlib versions;
- contains no `sorry` or `admit`;
- introduces no custom axioms;
- avoids `unsafe` and compiler-trust shortcuts;
- avoids `native_decide` unless explicitly permitted, with trust implications understood;
- uses a kernel-checkable certificate for substantial computation;
- passes a theorem-level axiom audit (`#print axioms`);
- has been checked against the original source problem;
- has a reproducible green CI build before being called upstream-ready.

This audit was produced in a container **without a Mathlib build cache**, so no claim here
has been compiled. Treat every `action` field as "do this, then verify the build".

## Workflow status

The ten categories are the *mathematical* classification and do not change as work
progresses. Track execution separately, per problem, in a `_workspace/<Problem>.md` note:

`not started` → `proof drafted` → `green in ProofPlaygrond` → `green in DTD Formal Conjectures`
→ `upstream PR opened` → `merged`

## Files

- [INDEX.md](./INDEX.md) — master table of every audited declaration.
- [PRIORITIES.md](./PRIORITIES.md) — ranked work queue.
- [CAMPAIGNS.md](./CAMPAIGNS.md) — internal solving campaigns and where their proofs live.
- `<Directory>.md` — full detail reports.
- `data/` — raw JSON and the scripts that produced it.
