# OEIS A080170 gcd/prime-power equivalence restoration

## Status

Queued — complete proof green, canonical declaration still admitted.

## Green proof

- Audit PR: #287
- Audit branch: `openai/audit-a80170-equivalence`
- Immutable audit head: `ca28a389683ebfa9154c55019aaa0b1fd2fdd21a`
- Historical proof commit: `0720658844d76a50d48e4baa152eef14d4462907`
- Historical source blob: `4985c414321be15ed18552834b7aa7c0d9644eb7`
- Focused audit run: `30213920030`
- Exact axiom footprint: `[propext, Classical.choice, Quot.sound]`

Green theorem:

```lean
OeisA80170.gcdCondition_iff_primePowerCondition
```

For every `k ≥ 2`, it proves:

```lean
GCDCondition k ↔ PrimePowerCondition (k + 1)
```

## Required canonical patch

Restore the complete proof development or package it through the repository's external `formal_proof` mechanism while replacing the admitted current body.

## Promotion gates

- exact current definitions and theorem statement preserved;
- complete proof source frozen immutably;
- Google-facing patch follows proof-length policy;
- exact current-main build and theorem axiom audit green;
- copy-paste upstream PR description prepared.
