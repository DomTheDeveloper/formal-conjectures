# Erdős 100 nine-point Piepmeyer witness restoration

## Status

Queued — complete witness proof green, canonical declaration still admitted.

## Green proof

- Audit PR: #284
- Audit branch: `openai/audit-erdos100-piepmeyer`
- Immutable audit head: `ac6d0f804114149b70673549d2d8494eeab9195c`
- Historical proof blob: `db773dd78975db6da5aed05c05c6eff1a26112b5`
- Focused audit run: `30213263093`
- Exact axiom footprint: `[propext, Classical.choice, Quot.sound]`

Green theorem:

```lean
Erdos100.erdos_100_piepmeyer_kernel
```

It verifies an explicit `A : Finset ℝ²` satisfying:

```lean
A.card = 9 ∧ DistancesSeparated A ∧ diam (A : Set ℝ²) < 5
```

## Required canonical patch

Restore the body of `Erdos100.erdos_100_piepmeyer` from the immutable proof support and exact witness.

## Promotion gates

- explicit point coordinates and exact theorem statement preserved;
- proof support packaged according to repository proof-length policy;
- one focused Google-facing source patch;
- exact current-main build and axiom audit green;
- copy-paste upstream PR description prepared.
