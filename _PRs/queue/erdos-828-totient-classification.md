# Erdős 828 totient-divisibility classification restoration

## Status

Queued — exact theorem green, canonical declaration still admitted.

## Green proof

- Audit PR: #290
- Audit branch: `openai/audit-erdos828-phi-classification`
- Immutable audit head: `59604dd67b7a3c7d1eb7f328dac2dbe70cfbf10e`
- Historical source blob: `c1ebc4e74a2308c13aa72ce65fa3ea5a172c127e`
- Focused audit run: `30214195665`
- Exact axiom footprint: `[propext, Classical.choice, Quot.sound]`

Green theorem:

```lean
Erdos828.erdos_828.variants.phi_dvd_self_iff_pow2_pow3_kernel
```

It proves:

```lean
φ n ∣ n ↔ n ≤ 1 ∨ ∃ᵉ (a > 0) (b), n = 2 ^ a * 3 ^ b
```

## Required canonical patch

Restore the body of `Erdos828.erdos_828.variants.phi_dvd_self_iff_pow2_pow3` from the immutable proof.

## Promotion gates

- exact theorem statement and current totient definitions unchanged;
- one focused Google-facing source patch;
- exact current-main build and axiom audit green;
- no proof holes or trust shortcuts;
- copy-paste upstream PR description prepared.
