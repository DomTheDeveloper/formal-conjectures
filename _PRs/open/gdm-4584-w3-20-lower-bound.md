# Green 14: W(3,20) lower bound

## Status

Open with Google DeepMind and green: [upstream PR #4584](https://github.com/google-deepmind/formal-conjectures/pull/4584).

## Canonical patch

- Source: `FormalConjectures/GreensOpenProblems/14.lean`
- Upstream head: `17de91fed457a7e3f67a824d5e8554b4e8537ac4`
- Shape: 1 commit, 1 file
- Title: `feat(GreensOpenProblems/14): mark W(3,20) lower bound solved`

## Verification

- Immutable proof artifact: `013a0f04de0057d2bd1034c7cc4caf10ac8dc2cf`
- Focused Lean audit: run `29996507187`
- GDM full Lean build: run `30017521895` — success
- GDM copyright check: run `30017522202` — success
- Exact theorem: `Green14.W 3 20 ≥ 389`
- No `sorryAx`, `Lean.ofReduceBool`, or `Lean.trustCompiler`
- Independent certificate hash: `46a69f46bc80c95fa688d06c0e39c9b29a8fc2c6dec4603b77886eb638c02044`

## State

Open upstream; awaiting review or merge. Move this record to `../merged/` only after the official PR is merged.