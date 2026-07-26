# Erdős 1084 exact one-dimensional value restoration

## Status

Queued — exact theorem green, canonical declaration still admitted.

## Green proof

- Audit PR: #285
- Audit branch: `openai/audit-erdos1084-d1`
- Immutable audit head: `8bd9c48b60533cfbeb50c60d28e893a6c7ef3a9d`
- Historical proof blob: `771c6c62762fa9e970dd3d3c52e984d18db216d5`
- Focused audit run: `30213292071`
- Exact axiom footprint: `[propext, Classical.choice, Quot.sound]`

Green theorem:

```lean
Erdos1084.erdos_1084.variants.upper_d1_kernel : f 1 n = n - 1
```

The upper bound injects unit-distance pairs into nonminimum endpoints; the lower bound uses the integer-line witness `{0,1,…,n-1}`.

## Required canonical patch

Restore the body of `Erdos1084.erdos_1084.variants.upper_d1` from the immutable proof.

## Promotion gates

- exact theorem statement and current `f` definition unchanged;
- proof support packaged according to repository policy;
- one focused Google-facing source patch;
- exact current-main build and axiom audit green;
- copy-paste upstream PR description prepared.
