# The `N = 6`, `D = 3` integer monochromatic-quantum-graph obstruction

This directory contains a Lean 4 proof that the perfect-matching equation
system `EqSystemN 6 3` has no solution over `ZMod 2` and therefore no solution
over the integers.  It also rules out integer solutions whose weights are
restricted to `{-1, 0, 1}`.

The proof reduces integer weights modulo two.  The three monochromatic
equations force the colour-zero diagonal support graph to have an odd number
of perfect matchings.  There are exactly 47 such support graphs up to the
`S_6` vertex action.  Each representative is reduced to a Boolean CNF, and a
Lean-reflected LRAT checker proves that all 47 CNFs are unsatisfiable.  The
orbit-classification and semantic bridges from the equation system to those
CNFs are also proved in Lean.

## Certificate bundle

The 47 compact LRAT certificates are distributed as the release asset
`quantum-graph-n6d3-clrat-v1.tar.zst`.  Run:

```sh
./QuantumGraphN6D3/setup_certificates.sh
```

The script downloads the versioned release asset, verifies its fixed SHA-256
digest, and extracts it into this directory's `certificates/` subdirectory.

## Verification

This proof branch is based on `google-deepmind/formal-conjectures` commit
`8f6e745798379104379da0b5c28c25315489890f`.  After downloading the
certificates, run from the repository root:

```sh
./QuantumGraphN6D3/verify.sh
```

The final theorems are:

```lean
QuantumGraphGlobal.no_eqSystem_zmod2
QuantumGraphGlobal.no_eqSystem_int
QuantumGraphGlobal.no_eqSystem_trinary_int
```

The axiom audit contains no `sorryAx`.  The LRAT certificates and finite orbit
tables are evaluated by Lean's native reflected machinery, so the audit lists
`Lean.ofReduceBool` and `Lean.trustCompiler` in addition to the usual logical
axioms.
