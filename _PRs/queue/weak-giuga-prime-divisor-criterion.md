# Weak Giuga prime-divisor criterion restoration

## Status

Queued — exact theorem green, canonical declaration still admitted.

## Green proof

- Audit PR: #283
- Audit branch: `openai/prove-weak-giuga-criterion`
- Immutable audit head: `f2ad674f64ac1980c74cac4404871ea7fff035b8`
- Focused audit run: `30213363291`
- Exact axiom footprint: `[propext, Classical.choice, Quot.sound]`

Green theorem:

```lean
AgohGiuga.isWeakGiuga_iff_prime_dvd_kernel
```

which proves, for composite `n`,

```lean
IsWeakGiuga n ↔ ∀ p ∈ n.primeFactors, p ∣ (n / p - 1)
```

## Required canonical patch

Restore the body of `AgohGiuga.isWeakGiuga_iff_prime_dvd` from the immutable proof, while cleaning the inherited deprecation and unused-simp warnings.

## Promotion gates

- exact statement unchanged;
- current-source style cleanup without changing the proof semantics;
- one canonical source file and one intentional commit;
- exact current-main build and axiom audit green;
- copy-paste upstream PR description prepared.
