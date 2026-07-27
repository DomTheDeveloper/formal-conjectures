# Google DeepMind PR Pipeline

This directory tracks each candidate through a strict, non-overlapping lifecycle.

## Stages

1. [`queue/`](queue/) — actionable work that is not yet GDM-ready.
2. [`ready/`](ready/) — fully green and packaged for GDM, but no upstream PR has been opened.
3. [`open/`](open/) — an active pull request exists in `google-deepmind/formal-conjectures`.
4. [`merged/`](merged/) — the GDM pull request was merged. This is the final 100% state.
5. [`blocked/`](blocked/) — unresolved mathematical, semantic, trust, or validation issue.

A record must live in exactly one lifecycle directory. Move the record forward when its status changes; do not duplicate it across stages.

## Ready promotion rule

An item may enter `ready/` only when all of the following are true:

1. The formal statement matches the intended mathematical problem.
2. The exact Lean theorem compiles under the repository's pinned toolchain.
3. The proof contains no `sorry`, `admit`, `native_decide`, unsafe declarations, custom axioms, or compiler-trust shortcuts.
4. The exact theorem axiom audit contains no `sorryAx`.
5. Focused validation is green in ProofPlaygrond and in `DomTheDeveloper/formal-conjectures`.
6. The proposed upstream patch is focused, clean, and accompanied by a copy-paste PR title and description.

Opening the upstream GDM PR moves the record from `ready/` to `open/`. A record moves from `open/` to `merged/` only after GitHub reports that the official GDM PR was merged.