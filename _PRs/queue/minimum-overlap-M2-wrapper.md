# Minimum-overlap `M(2)=1` wrapper replacement

## Status

Queued — proof theorem green, canonical declaration still admitted.

## Green proof

- Draft PR: #274
- Proof branch: `openai/prove-minimum-overlap-two`
- Immutable proof commit: `b7ed2e79b8626936752a4e789ea1de300b74cec2`
- Focused audit run: `30212008331`
- Exact axiom footprint: `[propext, Classical.choice, Quot.sound]`

Green theorem:

```lean
Erdos36.M_two_kernel : M 2 = 1
```

## Required canonical patch

Replace the body of `Erdos36.M_two` with a focused wrapper or formal-proof-backed declaration using the immutable green proof.

## Promotion gates

- exact theorem statement unchanged;
- one canonical file and one intentional commit;
- exact current-main build and axiom audit green;
- no `sorryAx`, native decision procedure, or compiler-trust shortcut;
- copy-paste upstream PR description prepared.
