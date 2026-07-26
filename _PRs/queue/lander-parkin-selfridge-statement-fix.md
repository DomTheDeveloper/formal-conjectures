# Lander–Parkin–Selfridge statement correction

## Status

Queued — not ready for Google DeepMind.

## Problem

The prose requires positive integers `k`, `n`, and `m`, but the Lean declaration quantifies over unrestricted naturals. Consequently `k = 1`, `n = 0`, and `m = 0` produce two equal empty sums and the false conclusion `1 ≤ 0`.

This is a formalization defect, not a counterexample to the mathematical Lander–Parkin–Selfridge conjecture.

## Required patch

Add explicit hypotheses equivalent to:

```lean
0 < k → 0 < n → 0 < m →
```

before the existing positivity, cross-distinctness, equality, and lower-bound hypotheses.

## Completion gates

- Confirm the corrected quantifier order and implication structure match the prose and standard formulation.
- Update the canonical source file rather than adding a standalone counterexample theorem.
- Add regression tests showing the empty-sum witness is excluded.
- Build the exact corrected module under the pinned Lean toolchain.
- Run the source and exact theorem axiom audits.
- Obtain a green build in `DomTheDeveloper/formal-conjectures`.
- Prepare a one-file, one-commit upstream patch and concise PR description.

## Existing audit

Draft PR #267 contains a green kernel-checked regression theorem exposing the current defect. It should be treated as evidence for the correction, not as a solved conjecture submission.
