# Nonlinear Bézier–Bernstein Voronovskaja formula

## Status

Ready for a fresh Google DeepMind PR. The previous upstream PR #4525 closed unmerged after its head branch was reset; the exact repaired one-file package passed the fork's current-main audit in PR #259.

## Canonical patch

- Source: `FormalConjectures/Paper/VoronovskajaTypeFormula.lean`
- Submission head: `6ccfa31eff2bfdb1798a7797f9b41749727da800`
- Shape: 1 commit, 1 canonical file
- Immutable proof: `d56612263ca6756cd1753ae5a0dbd6f1ed246cf5`

## Verification

- DTD full Lean build: `30182971657` — success
- DTD copyright check: `30182971670` — success
- Exact main theorem and three variants audited
- Axiom footprint: `[propext, Classical.choice, Quot.sound]`
- No `sorryAx`, custom axiom, or compiler-trust shortcut in the linked proof chain

## Upstream PR title

`feat(Paper): solve the nonlinear Voronovskaja formula`

## Upstream PR description

Marks the nonlinear Bézier–Bernstein Voronovskaja problem solved with the explicit powered-Gaussian limit constant and the three existing variants. The complete Lean development is frozen at `d56612263ca6756cd1753ae5a0dbd6f1ed246cf5`; the one-file Google-facing patch and linked proof chain passed the pinned build and exact axiom audit.