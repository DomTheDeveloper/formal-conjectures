# Easily Solvable "Open" Problems in formal-conjectures

This document records statements in this repository tagged `@[category research open]`
(plus a couple of notable neighbors) that turn out to be **easily solvable as
formalized** — together with machine-checked Lean proofs and an assessment of
whether the *underlying informal problem* is truly open.

All Lean proofs live in this directory and compile against the repo's toolchain
(Lean 4.27.0, mathlib pinned by the repo's `lake-manifest.json`):

- [`Disproofs.lean`](./Disproofs.lean) — proofs of the *negations* of misformalized open statements
- [`Solutions.lean`](./Solutions.lean) — proofs of statements as-stated that are much easier than the cited mathematics

Axiom audits (`#print axioms`) for every theorem below were checked; each is
`sorry`-free unless explicitly noted.

---

## Methodology

Three passes over all **1,166 research-open statements (624 files)**:

1. **Automated tactic sweep.** Every research-open declaration without
   `answer(sorry)` in its statement had its proof `sorry` replaced by a battery
   (`omega`, `decide`, `norm_num`, `simp_all`, `positivity`, `grind`, `aesop`)
   with strict re-verification of any hit (exit code 0 + `#print axioms` clean).
   **Result: zero genuine hits.** (One false positive from a heartbeat-timeout
   elaboration stub — `Wikipedia/Agrawal.lean` — was rejected on strict
   verification.) The corpus is robust against trivial automation.
2. **Semantic audit.** Manual + multi-agent review of all files for
   junk-value exploits, vacuous hypotheses, quantifier slips, and statements
   weaker than the informal problem they cite, with adversarial verification
   of each candidate finding.
3. **Ground truth.** Every surviving candidate was proved in Lean and
   compiled; nothing below is "sketch only".

---

## Finding 1 — Moving sofa uniqueness (misformalized ⇒ disproved)

**Statement:** `MovingSofa.sofaConstant_eq_volume_iff_eq_gerversSofa`
(`FormalConjectures/Wikipedia/MovingSofa.lean`), tagged `research open`:

```lean
theorem sofaConstant_eq_volume_iff_eq_gerversSofa :
    ∀ s : Set ℝ², sofaConstant = volume s ↔ s = gerversSofa
```

**Status of the formal statement: FALSE — disproved in Lean.**
Volume cannot characterize a set up to *equality*: adding a single point to
Gerver's sofa (or deleting a point from `Set.univ`) is volume-preserving but
changes the set. In [`Disproofs.lean`](./Disproofs.lean) we prove the fully
general, **sorry-free** theorem

```lean
theorem not_volume_characterizes_any_set (g : Set ℝ²) :
    ¬ (∀ s : Set ℝ², sofaConstant = volume s ↔ s = g)
```

so *no* choice of target set can repair the statement — the fix must change its
shape (uniqueness up to rigid motion and null sets). The corollary
instantiating `g := gerversSofa` is also proved; it alone inherits `sorryAx`
because the repo's *definition* of Gerver's constants uses the sorried
existence theorem `ABφθSpec.existsUnique` (every theorem mentioning
`gerversSofa` does).

**Is the underlying problem truly open? Essentially resolved.** Baek's
[*Optimality of Gerver's Sofa*, arXiv:2411.19826](https://arxiv.org/abs/2411.19826)
(119 pp., Dec 2024) proves Gerver's sofa attains the maximum area and is the
unique maximizer **up to rigid motion** (Theorem 1.1.1). It is under review at
the Annals of Mathematics with positive early reception; the repo itself
already tags the optimality statement `research solved` citing [Ba24], while
this uniqueness variant kept the `research open` tag. So: the informal
uniqueness question is claimed-solved (pending peer review), and the formal
statement here is simply false as written.

---

## Finding 2 — "Infinitely many Steiner systems" via degenerate systems

**Statements:** `SteinerSystems.infinitely_many_steiner_t4` and
`infinitely_many_steiner_t5` (`FormalConjectures/Wikipedia/SteinerSystem.lean`),
tagged `research solved` and attributed to Keevash's landmark 2014 existence
theorem:

```lean
theorem infinitely_many_steiner_t5 :
    ∃ S : Set (Σ k n : ℕ, S(5, k, n)), S.Infinite
```

**Status of the formal statements: trivially TRUE — proved in Lean without any
combinatorics.** The repo's `SteinerSystem t k n` structure does not require
`t < k < n`, so the *degenerate* system on `n` points whose single block is
`Finset.univ` is an `S(t, n, n)` for every `n`: every `t`-subset lies in
exactly one block. The family `n ↦ S(t, n, n)` is injective, giving an
infinite set. Both statements are proved this way in
[`Solutions.lean`](./Solutions.lean) (sorry-free, ~20 lines total).

**Is the underlying problem truly open?** No — the *intended* statement
(infinitely many nondegenerate designs with `t = 4, 5`) is a celebrated
theorem (Keevash 2014, arXiv:1401.3665). The finding here is that the
formalization is vacuous as written: it needs a nondegeneracy hypothesis
(e.g. `t < k < n`) before it says anything about Keevash's theorem. Note the
genuinely open neighbor in the same file (`large_steiner_systems`, explicit
witness with `5 < t < 10`, `n < 200`) is *not* affected: its `n > k > t`
side conditions rule the degenerate systems out.

---

## Negative result — the other 1,100+ open statements

The full tactic sweep over every research-open declaration produced **no
genuine automated solves**, and the semantic audit confirmed that the heavily
reviewed formalizations (Kaplansky with `IsMulTorsionFree`, Chvátal with
`Nonempty α`, Carmichael totient with `m ≠ n`, Büchi with per-`M` test cases,
Hilbert–Smith with real manifold hypotheses, invariant subspace with
nontriviality baked into `ClosedInvariantSubspace`, …) correctly capture their
open problems. Where junk values exist (e.g. `girth = 0` on acyclic graphs in
the WrittenOnTheWallII files), they weaken the statement *safely* rather than
trivializing it.

*(This section will be extended as the multi-agent audit completes.)*
