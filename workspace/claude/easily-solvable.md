# Easily Solvable "Open" Problems in formal-conjectures

This document records statements in this repository tagged `@[category research open]`
(plus two notable neighbors) that turn out to be **easily solvable as
formalized** — together with machine-checked Lean proofs and an assessment of
whether the *underlying informal problem* is truly open.

All Lean proofs live in this directory and compile against the repo's toolchain
(Lean 4.27.0, mathlib pinned by `lake-manifest.json`):

| File | Contents |
|---|---|
| [`Disproofs.lean`](./Disproofs.lean) | negation of the moving-sofa uniqueness statement (fully general, sorry-free) |
| [`Erdos486.lean`](./Erdos486.lean) | resolution of Erdős 486 as formalized: RHS disproved (≈250 lines of harmonic analysis) |
| [`Erdos361_15.lean`](./Erdos361_15.lean) | Erdős 361 (contradictory hypothesis, ×3) and Erdős 15 (`Summable` misuse) |
| [`ReflexiveAnswers.lean`](./ReflexiveAnswers.lean) | 25 asymptotic-estimate statements solved by answer-self-instantiation |
| [`Solutions.lean`](./Solutions.lean) | degenerate-system proofs of the two Steiner-system statements |

**Total: 33 statements resolved** (31 tagged `research open`, 2 tagged
`research solved`), every proof verified `sorry`-free by `#print axioms`
(only `propext`, `Classical.choice`, `Quot.sound`), except where a `sorryAx`
enters through a *definition* in the repository itself (noted explicitly below).

---

## Methodology

Three passes over all **1,166 research-open statements (624 files)**:

1. **Automated tactic sweep.** Every research-open declaration without
   `answer(sorry)` in its statement had its proof `sorry` replaced by a battery
   (`omega`, `decide`, `norm_num`, `simp_all`, `positivity`, `grind`, `aesop`)
   with strict re-verification of any hit (exit code 0 + `#print axioms`
   clean). **Result: zero genuine hits** — the corpus is robust against
   trivial automation. (One false positive in `Wikipedia/Agrawal.lean` — a
   heartbeat-timeout elaboration stub — was rejected by strict verification.)
2. **Semantic audit.** Manual review plus a 13-agent parallel audit of all
   624 files, hunting junk-value exploits, vacuous hypotheses, quantifier
   slips, and statements weaker than the problems they cite, with an
   adversarial-skeptic pass over every candidate finding.
3. **Ground truth.** Every surviving candidate was proved in Lean and
   compiled. Nothing below is "sketch only".

---

## Finding 1 — Erdős Problem 486: resolved by `answer(False)` (the `n = 0` modulus bug)

**Statement** (`FormalConjectures/ErdosProblems/486.lean`, `research open`):

```lean
theorem erdos_486 : answer(sorry) ↔
    ∀ X : (n : ℕ) → Set (ZMod n), ∃ d, {m : ℕ | ∀ n, (m : ZMod n) ∉ X n}.HasLogDensity d
```

**Defect.** The family ranges over *all* moduli including `n = 0`, and
`ZMod 0 = ℤ` with the *injective* coercion `ℕ → ℤ`. So `X 0` alone can exclude
an arbitrary set of integers: taking `X 0 := (Nat.cast '' S)ᶜ` and
`X (n+1) := ∅` realizes `B = S` for **every** `S ⊆ ℕ`. The statement thus
asserts that every subset of ℕ has a logarithmic density — false.

**Proof** ([`Erdos486.lean`](./Erdos486.lean), sorry-free): the union of blocks
`[2^(4^j), 2^(2·4^j))` has log-density partial sums `≥ 0.45` at the top of each
block but `≤ 0.40` just before the next block, via mathlib's harmonic-sum
bounds (`log (n+1) ≤ harmonic n ≤ 1 + log n`), so no limit exists. Main
theorem: `Erdos486Resolution.erdos_486_rhs_false`. Hence `erdos_486` holds
with `answer(False)`.

**Is the underlying problem open?** The intended problem restricts the
congruence conditions to moduli `n < m` (see
[erdosproblems.com/486](https://www.erdosproblems.com/486)) — a genuinely
different and much subtler question. Notably, a 2026 proof claim by Shouqiao
Wang on the [problem's discussion thread](https://www.erdosproblems.com/forum/thread/486)
argues the answer to the *real* problem is also "no" (via congruence conditions
activated at increasing scales), but that construction is real mathematics —
nothing like the formalization's one-line `n = 0` carve-out. The formal
statement needs moduli `n ≥ 1` (and the `n < m` guard) to capture the problem.

---

## Finding 2 — Erdős Problem 361: contradictory hypothesis (×3 statements)

**Statements** (`FormalConjectures/ErdosProblems/361.lean`, all `research open`):
`erdos_361.bigO`, `erdos_361.bigTheta`, `erdos_361.smallO`, each with parameter
`(c : ℝ)` and hypothesis

```lean
hA : ∀ c n, A n = ((Finset.Icc 1 ⌊c * n⌋₊).powerset.filter
      (fun B ↦ n ≠ ∑ a ∈ B, a)).sup Finset.card
```

**Defect.** The inner binder `c` *shadows* the theorem's real parameter `c`
(and even elaborates at type `ℕ`, so the outer `c` is unused). The hypothesis
pins `A n` for every `c` simultaneously and is contradictory: `c = 1, n = 1`
forces `A 1 = 0` while `c = 3, n = 1` forces `A 1 = 3`. All three statements
are vacuously provable **with any answer whatsoever**.

**Proof** ([`Erdos361_15.lean`](./Erdos361_15.lean), sorry-free):
`erdos_361_hypothesis_inconsistent` is a one-line `decide`; the three
statements follow with the zero function as answer.

**Is the underlying problem open?** Yes —
[erdosproblems.com/361](https://www.erdosproblems.com/361) (largest subset of
`{1,…,⌊cn⌋}` with no subset summing to `n`) is open. The fix is
`hA : ∀ n, A n = …` using the theorem's own `c : ℝ`.

---

## Finding 3 — Erdős Problem 15: `Summable` ≠ "converges" — resolved by `answer(False)`

**Statement** (`FormalConjectures/ErdosProblems/15.lean`, `research open`):

```lean
theorem erdos_15 : answer(sorry) ↔
    Summable (fun k : ℕ => (-1 : ℚ) ^ (k + 1) * (k + 1) / (k.nth Nat.Prime))
```

**Defect.** The problem asks whether `∑ (-1)^n n/p_n` *converges* — i.e.
conditional convergence of the partial sums. Mathlib's `Summable` demands
*unconditional* convergence (of the net over finite subsets), which for
real/rational series forces absolute convergence. Since
`|(-1)^(k+1)(k+1)/p_k| ≥ 1/p_k` and `∑ 1/p` over primes diverges, the RHS is
plainly false — regardless of the deep open question.

**Proof** ([`Erdos361_15.lean`](./Erdos361_15.lean), sorry-free):
`erdos_15_rhs_false` — cast to ℝ along `Rat.castHom`, take absolute values
(`summable_abs_iff`), dominate the prime-indicator sum along `Nat.nth
Nat.Prime`, and contradict mathlib's `not_summable_one_div_on_primes`. Hence
`erdos_15` holds with `answer(False)`.

**Is the underlying problem open?** Very much so:
[erdosproblems.com/15](https://www.erdosproblems.com/15). Tao (2023) proved
the series converges *assuming* a strong Hardy–Littlewood prime-tuples
conjecture; unconditionally it is open, with numerics suggesting convergence
to ≈ −0.05216. The fix is to state convergence of partial sums:
`∃ L, Tendsto (fun N => ∑ k ∈ range N, …) atTop (𝓝 L)`.

---

## Finding 4 — The reflexive-answer degeneracy class (25 statements)

**Statements**: 25 `research open` asymptotic-estimate questions of the form

```lean
theorem … : f =O[l] (answer(sorry) : ℕ → ℝ)   -- or =Θ, or ~
```

across `ErdosProblems/142, 272, 321, 340, 357, 409, 422, 507, 539, 688, 789`
and `GreensOpenProblems/27, 37`.

**Defect.** `=O`, `=Θ` and `~` (`IsEquivalent`) are *reflexive*, and the
`answer( )` elaborator accepts any term of the right type — including the
function being estimated. So `answer := f` resolves each statement in one
line, with zero mathematical content. Two aggravating special cases:

- `ErdosProblems/422.lean` defines its function via `partial def f`, which is
  logically *opaque* in Lean: no defining equations exist, so no nontrivial
  growth bound could ever be proven about it — the self-referential answer is
  essentially the only provable one.
- `ErdosProblems/507.lean` (Heilbronn triangle problem) additionally defines
  `minTriangleArea` via mathlib's **signed** `triangle_area` under an `sInf`
  over all vertex orderings, so `minTriangleArea S = −(max area) ≤ 0` and the
  quantity `α` being "estimated" is identically `0` for `n ≥ 3` — the
  Heilbronn asymptotics are lost entirely (this also makes
  `erdos_507.lower`/`upper` refutable/trivially provable, resp.).

**Proof** ([`ReflexiveAnswers.lean`](./ReflexiveAnswers.lean), all 25
sorry-free): each original statement verbatim with `answer(sorry)` replaced by
its own left-hand side, closed by `isBigO_refl` / `isTheta_refl` /
`IsEquivalent.refl`.

**Are the underlying problems open?** Yes, all of them (they include the
Heilbronn triangle problem, Erdős's `f(n) = f(n−f(n−1))+f(n−f(n−2))`
recursion, Sidon-set growth questions, etc.). The finding is structural: the
`answer( )` form does not constrain asymptotic answers to closed forms, so
*any* `f REL answer( )` statement with a reflexive relation is formally
degenerate. A fix could require answers drawn from a concrete vocabulary of
elementary functions, or restate the questions as specific conjectured bounds
(as some files already do in their `variants`).

---

## Finding 5 — Moving sofa uniqueness (misformalized ⇒ disproved)

**Statement** (`FormalConjectures/Wikipedia/MovingSofa.lean`, `research open`):

```lean
theorem sofaConstant_eq_volume_iff_eq_gerversSofa :
    ∀ s : Set ℝ², sofaConstant = volume s ↔ s = gerversSofa
```

**Defect.** Volume cannot characterize a set up to *equality*: adding one
point to Gerver's sofa (or deleting one from `univ`) preserves volume but
changes the set.

**Proof** ([`Disproofs.lean`](./Disproofs.lean)): the fully general theorem
`not_volume_characterizes_any_set : ∀ g, ¬(∀ s, sofaConstant = volume s ↔ s = g)`
is **sorry-free** — so no target set can repair the statement; the fix must
change its shape (uniqueness up to rigid motion and null sets). The corollary
at `g := gerversSofa` inherits `sorryAx` only through the repo's *definition*
of Gerver's constants (`ABφθSpec.existsUnique` is sorried), as would any
theorem mentioning `gerversSofa`.

**Is the underlying problem open?** Essentially resolved: Baek's
[*Optimality of Gerver's Sofa*, arXiv:2411.19826](https://arxiv.org/abs/2411.19826)
proves Gerver's sofa attains the maximum area and is the unique maximizer up
to rigid motion (Thm 1.1.1); under review at Annals of Mathematics, named a
top-10 2025 breakthrough by Scientific American. The repo already tags the
optimality statement `research solved`; this uniqueness variant kept
`research open` but is false as written.

---

## Finding 6 (bonus, tagged `research solved`) — Steiner systems via degeneracy

**Statements** (`FormalConjectures/Wikipedia/SteinerSystem.lean`):
`infinitely_many_steiner_t4` and `infinitely_many_steiner_t5`, attributed to
Keevash's celebrated 2014 existence theorem.

**Defect.** The `SteinerSystem t k n` structure never requires `t < k < n`,
so the degenerate system on `n` points whose single block is `Finset.univ` is
an `S(t, n, n)` for every `n` — giving infinitely many Steiner systems with
no combinatorics at all.

**Proof** ([`Solutions.lean`](./Solutions.lean), sorry-free): degenerate
single-block systems + injectivity of `n ↦ ⟨n, n, _⟩`.

**Is the underlying problem open?** No — the intended statement is Keevash's
theorem (arXiv:1401.3665). But the formalization proves *itself* without it;
it needs a nondegeneracy hypothesis. The genuinely open neighbor in the same
file (`large_steiner_systems`, explicit witness with `5 < t < 10`, `n < 200`)
is *not* affected — its `n > k > t` fields exclude degenerate systems.

---

## Negative results (evidence the rest is robust)

- The **full tactic sweep** over all 1,166 research-open statements produced
  zero genuine automated solves.
- Formalizations checked by hand and found *correct* (their traps avoided):
  Kaplansky conjectures (`IsMulTorsionFree` present), Chvátal's conjecture
  (`Nonempty α` present), Carmichael totient (`m ≠ n` present), Büchi `M = 5`
  (per-`M` counterexamples in test lemmas), Hilbert–Smith (manifold
  hypotheses real), invariant subspace problem (nontriviality inside
  `ClosedInvariantSubspace`), Selfridge's Fermat-factor conjecture (distinct
  prime factor counts — monotone so far, genuinely open), Gilbreath, Agrawal,
  Brennan (`sSup` sets mathematically bounded), Green 24, moving-sofa
  optimality, RiemannZetaValues (coercion makes them "real and irrational" —
  correct), Erdős 1041 (connectivity hypotheses present).
- **Computational counterexample searches** (no hits, confirming openness):
  A56777 "members come from prime quadruples" (all 10 terms to 2×10⁷ check
  out), A63880 "terms ≡ 108 (mod 216)" (56,297 terms to 2×10⁷ all conform),
  A67720 "k+1 prime except k=8" (all terms to k ≈ 4.5×10³ conform).

---

*Produced with the repo's exact toolchain; each Lean file in this directory
can be checked with `lake env lean workspace/claude/<file>.lean` after
`lake exe cache get` (or the prebuilt cache) and `lake build
FormalConjectures.Util.ProblemImports`.*
