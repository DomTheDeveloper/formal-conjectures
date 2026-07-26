# Two-color van der Waerden base-value wrappers

## Status

Queued — both proof theorems green, canonical declarations still admitted.

## Green proof

- Draft PR: #275
- Proof branch: `openai/prove-vdw-base-values`
- Immutable proof commit: `69ba9d07479dfaca6eee121ea91a0182849a4297`
- Focused audit run: `30212019209`
- Exact axiom footprint for both theorems:
  `[propext, Classical.choice, Quot.sound]`

Green theorems:

```lean
Erdos138.monoAPNumber_two_one_kernel : W 1 = 1
Erdos138.monoAPNumber_two_two_kernel : W 2 = 3
```

## Required canonical patch

Replace the bodies of:

```lean
Erdos138.monoAPNumber_two_one
Erdos138.monoAPNumber_two_two
```

with focused wrappers or formal-proof-backed declarations using the immutable green proof.

## Promotion gates

- exact intended statements unchanged;
- one canonical file and one intentional commit;
- exact current-main build and both axiom audits green;
- no proof holes or trust shortcuts;
- copy-paste upstream PR description prepared.
