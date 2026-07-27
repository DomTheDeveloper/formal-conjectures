# Google DeepMind PR Pipeline

This directory tracks each candidate through a strict, non-overlapping lifecycle.

## Stages

1. [`queue/`](queue/) — newly identified or untriaged work.
2. [`almost-ready/`](almost-ready/) — close enough to track for promotion, but missing at least one mathematical, semantic, proof, trust, CI, packaging, or current-main gate. An item may remain here indefinitely.
3. [`ready/`](ready/) — fully green and packaged for GDM, but no upstream PR has been opened.
4. [`open/`](open/) — an active pull request exists in `google-deepmind/formal-conjectures`.
5. [`merged/`](merged/) — the GDM pull request was merged. This is the final 100% state.
6. [`blocked/`](blocked/) — not currently close enough for the promotion pipeline because of a fundamental unresolved issue.

A record must live in exactly one lifecycle directory. Move the record forward when its status changes; do not duplicate it across stages.

## Almost-ready rule

Use `almost-ready/` whenever the project is plausibly within one or a few concentrated proof-engineering steps of `ready/`, including:

- a complete green proof that still needs a canonical wrapper or submission package;
- a clean package with red, pending, or stale CI;
- a nearly complete proof missing the final certificate or bridge;
- a formalization defect that must be corrected before the mathematical problem can be submitted.

`Almost-ready` is not a claim that completion is imminent. Some records may remain there permanently if the final blocker is never resolved.

## Ready promotion rule

An item may enter `ready/` only when all of the following are true:

1. The formal statement matches the intended mathematical problem.
2. The exact Lean theorem compiles under the repository's pinned toolchain.
3. The proof contains no `sorry`, `admit`, `native_decide`, unsafe declarations, custom axioms, or compiler-trust shortcuts.
4. The exact theorem axiom audit contains no `sorryAx`.
5. Focused validation is green in ProofPlaygrond and in `DomTheDeveloper/formal-conjectures`.
6. The proposed upstream patch is focused, clean, and accompanied by a copy-paste PR title and description.

Opening the upstream GDM PR moves the record from `ready/` to `open/`. A record moves from `open/` to `merged/` only after GitHub reports that the official GDM PR was merged.