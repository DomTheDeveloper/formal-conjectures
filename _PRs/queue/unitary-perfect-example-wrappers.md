# Unitary-perfect example wrapper replacements

## Status

Queued — proof module green, canonical declarations not yet replaced.

## Green proof

- Draft PR: #273
- Proof branch: `openai/prove-unitary-perfect-examples`
- Immutable proof commit: `e2b0f213c1afd4451bdc4f5be9ee0265e2c16870`
- Focused audit run: `30211997936`
- Axiom footprint for both exported theorems:
  `[propext, Classical.choice, Quot.sound]`

The green theorems are:

```lean
Erdos1052.isUnitaryPerfect_87360_kernel
Erdos1052.isUnitaryPerfect_146361946186458562560000_kernel
```

## Required canonical patch

Replace the stopped/admitted bodies of:

```lean
Erdos1052.isUnitaryPerfect_87360
Erdos1052.isUnitaryPerfect_146361946186458562560000
```

with focused wrappers or link-backed catalog declarations pointing to the immutable proof module.

## Promotion gates

- preserve the exact intended `IsUnitaryPerfect` statements;
- one canonical source file and one intentional commit;
- no unrelated support code in the Google-facing patch;
- exact current-main build and theorem axiom audit green;
- copy-paste upstream PR description prepared.
