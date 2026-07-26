# `_workspace` — solver working directory

Scratch space for **prose** about work in progress: what we are attacking, what has been
tried, what is blocked, and where a proof attempt currently stands. Nothing here is
compiled, imported, or published — `lake build` never looks at this directory.

Keeping this out of the Lean tree means a half-finished idea can be written down without
polluting `FormalConjectures/` with commented-out code or speculative `sorry`s.

## What goes here

- **Progress notes** on a specific problem: attack plan, key lemmas, dead ends, open sub-goals.
- **Design notes** that span several files (e.g. a definition we may want in
  `FormalConjecturesForMathlib/`).
- **Session hand-offs**: enough state that a later session can resume without re-deriving.
- **Survey / literature notes** gathered while formalising a statement.

## What does *not* go here

- Formalisations, definitions, or proofs. Those belong in `FormalConjectures/` or
  `FormalConjecturesForMathlib/`.
- Finished novelty/priority audits — those belong in `_certificates/`.
- Generated logs, build output, or large data dumps.

## File naming

One file per problem, named after the problem's home in the Lean tree so the two are easy
to pair up:

| Problem file | Workspace note |
|---|---|
| `FormalConjectures/ErdosProblems/10.lean` | `_workspace/ErdosProblems-10.md` |
| `FormalConjectures/WrittenOnTheWallII/145.lean` | `_workspace/WOWII-145.md` |
| `FormalConjectures/Arxiv/2147983/...` | `_workspace/Arxiv-2147983.md` |

Cross-cutting notes that are not about a single problem get a descriptive kebab-case name,
e.g. `_workspace/local-independence-api.md`.

Start from [`TEMPLATE.md`](./TEMPLATE.md).

## Status vocabulary

Use one of these in the `Status:` field so notes can be skimmed:

- `open` — not started beyond reading the statement.
- `attacking` — actively working; the note says what is currently being tried.
- `blocked` — stuck on a stated obstruction (missing Mathlib API, unclear statement, …).
- `proved` — proof compiles; the note records the route taken.
- `abandoned` — dropped; the note records why, so it is not retried blindly.

## Conventions

- Write LaTeX for mathematics (`$n$`, `$\sum_{i<n} i!$`), matching the docstring style in
  [`AGENTS.md`](../AGENTS.md).
- Link to the Lean declaration by path and name, e.g.
  `FormalConjectures/ErdosProblems/10.lean:42` — repo-relative paths stay clickable.
- Record dead ends explicitly. A failed approach with the reason it failed is the most
  valuable thing in a note.
- Keep notes append-oriented: add to the log rather than rewriting history, so the
  reasoning trail survives.
