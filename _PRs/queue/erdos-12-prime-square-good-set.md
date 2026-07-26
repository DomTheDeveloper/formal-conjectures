# Erdős 12 prime-square good-set restoration

## Status

Queued — exact theorem green, canonical declaration still admitted.

## Green proof

- Audit PR: #289
- Audit branch: `openai/audit-erdos12-good-example`
- Immutable audit head: `b43b12d674de0c879c64b82176a64a231f1a73e3`
- Historical source blob: `551b4c3b82a0b446bdbe314ac487754fcc265d0a`
- Focused audit run: `30214058880`
- Exact axiom footprint: `[propext, Classical.choice, Quot.sound]`

Green theorem:

```lean
Erdos12.isGood_example_kernel
```

It proves that the set of squares of primes congruent to `3 mod 4` is infinite and satisfies the divisibility obstruction defining `IsGood`.

## Required canonical patch

Restore the body of `Erdos12.isGood_example` from the immutable proof and modernize the deprecated `ZMod` equivalence lemma.

## Promotion gates

- exact set and `IsGood` statement unchanged;
- deprecation warning removed without semantic changes;
- one focused Google-facing source patch;
- exact current-main build and axiom audit green;
- copy-paste upstream PR description prepared.
