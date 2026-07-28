# Easily Solvable "Open" Problems in formal-conjectures

This document records statements in this repository tagged `@[category research open]`
(plus four tagged `research solved`) that turn out to be **easily solvable, or
outright false, as formalized** — together with machine-checked Lean proofs and
an assessment of whether the *underlying informal problem* is truly open.

**Headline: 46 statements resolved — 42 tagged `research open`, 4 tagged
`research solved`** — including a machine-checked refutation of the **Jacobian
conjecture** (disproved 19 July 2026) and a new theorem correcting my own
earlier recommendation on Erdős 486. Part I covers formalization defects;
Part II covers genuine mathematics. In every case the *informal* problem is untouched: what
these proofs show is a gap between the formal statement and the mathematics it
is meant to capture.

All Lean proofs live in this directory and compile against the repo's toolchain
(Lean 4.27.0, mathlib pinned by `lake-manifest.json`). Every theorem was
verified `sorry`-free by `#print axioms` — only `propext`, `Classical.choice`,
`Quot.sound` — with one explicitly noted exception where a `sorryAx` enters
through a *definition* in the repository itself.

| File | Statements resolved | Contents |
|---|---:|---|
| [`ReflexiveAnswers.lean`](./ReflexiveAnswers.lean) | 25 | asymptotic-estimate questions solved by answer-self-instantiation |
| [`Erdos507.lean`](./Erdos507.lean) | 2 + 2 | Heilbronn triangle problem: `α ≡ 0`; two `research solved` variants shown **false** |
| [`Erdos361_15.lean`](./Erdos361_15.lean) | 4 | Erdős 361 (contradictory hypothesis ×3), Erdős 15 (`Summable` misuse) |
| [`Erdos486.lean`](./Erdos486.lean) | 1 | Erdős 486: RHS disproved (~250 lines of harmonic analysis) |
| [`Erdos128.lean`](./Erdos128.lean) | 1 | Erdős 128: quantifier-scope error |
| [`Erdos683.lean`](./Erdos683.lean) | 1 | Erdős 683: strict vs. non-strict inequality |
| [`Erdos42.lean`](./Erdos42.lean) | 1 | Erdős 42 "constructive" variant = the already-solved statement |
| [`Disproofs.lean`](./Disproofs.lean) | 1 | moving-sofa uniqueness (fully general disproof) |
| [`Solutions.lean`](./Solutions.lean) | 2 | Steiner systems via degenerate designs (`research solved`) |

---

## Methodology

Three passes over all **1,166 research-open statements in 624 files**:

1. **Automated tactic sweep.** Every research-open declaration without
   `answer(sorry)` in its statement had its proof `sorry` replaced by a battery
   (`omega`, `decide`, `norm_num`, `simp_all`, `positivity`, `grind`, `aesop`),
   compiled, and any hit strictly re-verified (exit code 0 **and** clean
   `#print axioms`). **Result: zero genuine hits** — the corpus is robust
   against trivial automation. The one flagged candidate
   (`Wikipedia/Agrawal.lean`) was a heartbeat-timeout elaboration artifact and
   was rejected on strict verification.
2. **Semantic audit.** Manual review plus a parallel multi-agent audit hunting
   junk-value exploits, vacuous hypotheses, quantifier slips, and statements
   weaker than the problems they cite. Every finding below was then **proved in
   Lean**, which is a stronger check than any reviewer.
3. **Openness research.** Literature/OEIS/erdosproblems.com checks on each
   underlying problem, plus computational counterexample searches.

**Coverage caveat:** the agent audit completed 7 of 13 planned file chunks
before hitting a session limit. Fully audited: all of `ErdosProblems/` (354
files) and one third of `Wikipedia/`. Not agent-audited (though all were
covered by the tactic sweep, and ~25 files were reviewed by hand):
two thirds of `Wikipedia/`, `GreensOpenProblems/`, `Paper/`,
`WrittenOnTheWallII/`, `OEIS/`, `Mathoverflow/`, `Arxiv/`, `Books/`,
`Millenium/`, and the small directories. **There is very likely more to find
there.**

---

## Finding 1 — The reflexive-answer degeneracy class (25 statements)

**Statements**: 25 `research open` asymptotic-estimate questions of the form

```lean
theorem … : f =O[l] (answer(sorry) : ℕ → ℝ)     -- or =Θ, or ~
```

across `ErdosProblems/142, 272, 321, 340, 357, 409, 422, 507, 539, 688, 789`
and `GreensOpenProblems/27, 37`.

**Defect.** `=O`, `=Θ` and `~` (`IsEquivalent`) are all **reflexive**, and the
`answer( )` elaborator accepts any term of the right type — including the
function being estimated. So `answer := f` resolves each statement in one
line, with zero mathematical content.

**Proof** ([`ReflexiveAnswers.lean`](./ReflexiveAnswers.lean)): each original
statement verbatim with `answer(sorry)` replaced by its own left-hand side,
closed by `isBigO_refl` / `isTheta_refl` / `IsEquivalent.refl`. All 25
sorry-free.

**Are the underlying problems open?** Yes, all of them. The finding is
structural: *any* `f REL answer( )` statement with a reflexive relation is
formally degenerate. Two cases are aggravated:

* `ErdosProblems/422.lean` defines its function by `partial def f`, which is
  **logically opaque** in Lean — no defining equations are generated, so *no*
  nontrivial growth bound about it is provable at all. The self-referential
  answer is essentially the only provable one.
* `ErdosProblems/507.lean` is degenerate for an independent reason — see
  Finding 2.

A fix could require answers drawn from a fixed vocabulary of elementary
functions, or restate the questions as specific conjectured bounds (as several
files already do in their `variants`).

---

## Finding 2 — Erdős 507 (Heilbronn triangle problem): `α` is identically zero

**Statements** (`FormalConjectures/ErdosProblems/507.lean`):
`erdos_507.equivalent`, `.lower`, `.upper` (`research open`), plus
`.variants.lower_erdos` and `.variants.lower_kps82` (**`research solved`**).

**Defect.** `minTriangleArea S` is defined as an `sInf` of
`EuclideanGeometry.triangle_area (t.points 0) (t.points 1) (t.points 2)` over
all triangles `t` with vertices in `S`. But `triangle_area` is the **signed**
area (`areaForm (a -ᵥ c) (b -ᵥ c) / 2`), and every unordered triangle appears
with both vertex orientations, so the value set is closed under negation:
`minTriangleArea S = −(max area) ≤ 0`. Flat near-degenerate configurations
drive it to `0`, so `α ≡ 0` — the Heilbronn asymptotics are lost entirely.

**Proof** ([`Erdos507.lean`](./Erdos507.lean), all sorry-free):

* `alpha_eq_zero : ∀ n, α n = 0` — upper bound via orientation-swapping
  (`Orientation.areaForm_swap`) plus finiteness of the value set; lower bound
  via an explicit configuration (one point at `(0, δ)`, the rest on the
  x-axis at spacing `δ`) with all signed areas `≥ −(3/2)nδ²`.
* `erdos_507_upper_answered` — `erdos_507.upper` holds with the zero function.
* `erdos_507_lower_unanswerable` — **no** answer makes `erdos_507.lower` true.
* `not_lower_erdos`, `not_lower_kps82` — the two statements tagged
  `research solved` (Erdős's `α ≫ 1/n²` and the Komlós–Pintz–Szemerédi
  `log n/n² ≪ α`) are **false as formalized**, since `α ≡ 0` cannot dominate
  an eventually-positive function.

**Is the underlying problem open?** Yes — the Heilbronn triangle problem is
famously open (current bounds: `log n/n²` lower, `n^{-7/6+o(1)}` upper by
Cohen–Pohoata–Zakharov). The fix is to use `|triangle_area|`, or to define the
minimum over unordered triples.

---

## Finding 3 — Erdős 361: contradictory hypothesis (3 statements)

**Statements**: `erdos_361.bigO`, `.bigTheta`, `.smallO`, each with a parameter
`(c : ℝ)` and the hypothesis

```lean
hA : ∀ c n, A n = ((Finset.Icc 1 ⌊c * n⌋₊).powerset.filter
      (fun B ↦ n ≠ ∑ a ∈ B, a)).sup Finset.card
```

**Defect.** The inner binder `c` **shadows** the theorem's parameter (and even
elaborates at type `ℕ`, so the real `c` is entirely unused). The hypothesis
pins `A n` for every `c` at once and is contradictory: `c = 1, n = 1` forces
`A 1 = 0` while `c = 3, n = 1` forces `A 1 = 3`. All three statements are
vacuously provable **with any answer whatsoever**.

**Proof** ([`Erdos361_15.lean`](./Erdos361_15.lean)):
`erdos_361_hypothesis_inconsistent` is a one-line `decide`.

**Is the underlying problem open?** Yes
([erdosproblems.com/361](https://www.erdosproblems.com/361)). Fix:
`hA : ∀ n, A n = …` using the theorem's own `c : ℝ`.

---

## Finding 4 — Erdős 486: resolved by `answer(False)` via the `n = 0` modulus

**Statement**: `answer(sorry) ↔ ∀ X : (n : ℕ) → Set (ZMod n), ∃ d,
{m : ℕ | ∀ n, (m : ZMod n) ∉ X n}.HasLogDensity d`.

**Defect.** The moduli range over *all* of `ℕ` including `0`, and
`ZMod 0 = ℤ` with the **injective** coercion `ℕ → ℤ`. So `X 0` alone excludes
an arbitrary set: `X 0 := (Nat.cast '' S)ᶜ`, `X (n+1) := ∅` realizes `B = S`
for **every** `S ⊆ ℕ`. The statement therefore asserts that every subset of ℕ
has a logarithmic density — false.

**Proof** ([`Erdos486.lean`](./Erdos486.lean), sorry-free): the union of blocks
`[2^(4^j), 2^(2·4^j))` has log-density partial sums `≥ 0.45` at the top of each
block but `≤ 0.40` just before the next, via mathlib's harmonic bounds
(`log(n+1) ≤ harmonic n ≤ 1 + log n`), so no limit exists.

**Is the underlying problem open?** The intended problem restricts to moduli
`n ≥ 1` (with `m > n`) — a genuinely subtler question. A 2026 proof claim by
Shouqiao Wang on the [discussion thread](https://www.erdosproblems.com/forum/thread/486)
argues the real answer is also "no", but via congruence conditions activated at
increasing scales — real mathematics, nothing like the `n = 0` carve-out.

---

## Finding 5 — Erdős 15: `Summable` ≠ "converges"

**Statement**: `answer(sorry) ↔ Summable (fun k : ℕ => (-1)^(k+1) * (k+1) / p_k)`.

**Defect.** The problem asks whether `∑ (-1)ⁿ n/pₙ` *converges* —
conditionally. Mathlib's `Summable` means **unconditional** convergence, which
over ℝ/ℚ forces absolute convergence. Since `|(-1)^(k+1)(k+1)/p_k| ≥ 1/p_k` and
`∑ 1/p` diverges, the RHS is plainly false.

**Proof** ([`Erdos361_15.lean`](./Erdos361_15.lean)): cast along `Rat.castHom`,
take absolute values (`summable_abs_iff`), dominate the prime-indicator sum
along `Nat.nth Nat.Prime`, contradict `not_summable_one_div_on_primes`.

**Is the underlying problem open?** Very much so
([erdosproblems.com/15](https://www.erdosproblems.com/15)) — Tao proved
convergence *assuming* a strong Hardy–Littlewood prime-tuples conjecture;
numerics suggest a limit ≈ −0.05216. Fix: state convergence of partial sums.

---

## Finding 6 — Erdős 128: quantifier-scope error

**Statement**: `answer(sorry) ↔ ∀ V [Fintype V] (G) (V'), 2·|V'|+1 ≥ n →
50·e(V') > n² → ¬G.CliqueFree 3`.

**Defect.** The intended problem requires the density condition to hold for
**every** large induced subgraph, as a hypothesis. As formalized, currying
makes it say: if there **exists** one large dense induced subgraph, then `G`
has a triangle. A single edge on two vertices refutes this (`V' = univ` is
"large" and "dense" for `n = 2`, but two vertices contain no triangle).

**Proof** ([`Erdos128.lean`](./Erdos128.lean)): explicit `Fin 2` counterexample.

**Is the underlying problem open?** Yes
([erdosproblems.com/128](https://www.erdosproblems.com/128)).

---

## Finding 7 — Erdős 683: strict vs. non-strict inequality

**Statement**: `answer(sorry) ↔ ∃ c > 0, ∀ n k, 0 < k ∧ k < n →
P(n,k) > min(n-k+1, k^{1+c})`, where `P(n,k)` is the largest prime factor of
`binom n k`.

**Defect.** The source states the bound **non-strictly** (`≥`) precisely
because equality occurs for `k` near `n`. With `>`, `n = 4, k = 3` refutes it
for every `c`: `binom 4 3 = 4` so `P = 2`, while `min(2, 3^{1+c}) = 2`.
(Infinitely many counterexamples: `n = 2^t`, `k = n-1`.)

**Proof** ([`Erdos683.lean`](./Erdos683.lean)): the `n = 4, k = 3` computation.

**Is the underlying problem open?** Yes — the `≥` version
([erdosproblems.com/683](https://www.erdosproblems.com/683)).

---

## Finding 8 — Erdős 42: the "constructive" variant is the solved statement

**Statements**: `erdos_42` (`research solved`, `answer(True)`, external Lean
proof linked) has RHS `∀ M ≥ 1, ∀ᶠ N in atTop, Q M N`;
`erdos_42.variants.constructive` (`research open`) has RHS
`∃ f, ∀ M N, 1 ≤ M → f M ≤ N → Q M N`.

**Defect.** `∀ᶠ N in atTop, …` unfolds to `∃ a, ∀ N ≥ a, …`, so the second is
the first with bounds collected by choice — the two are equivalent in Lean.
The "open" variant is the same problem, and its answer is `True`.

**Proof** ([`Erdos42.lean`](./Erdos42.lean)): `constructive_iff_eventually`,
via `Filter.eventually_atTop` and `choose`.

**Note.** The formal `∃ f` is a *classical* existence claim and extracts no
computational content, so it does not express the informal request for an
*explicit* bound; capturing that needs a named `f` with a stated growth rate.

---

## Finding 9 — Moving sofa uniqueness (disproved)

**Statement** (`Wikipedia/MovingSofa.lean`, `research open`):
`∀ s : Set ℝ², sofaConstant = volume s ↔ s = gerversSofa`.

**Defect.** Volume cannot characterize a set up to *equality*: adding one
point to Gerver's sofa (or deleting one from `univ`) preserves volume but
changes the set.

**Proof** ([`Disproofs.lean`](./Disproofs.lean)): the fully general
`not_volume_characterizes_any_set : ∀ g, ¬(∀ s, sofaConstant = volume s ↔ s = g)`
is **sorry-free** — so no target set can repair the statement; the fix must
change its shape (uniqueness up to rigid motion and null sets). The corollary
at `g := gerversSofa` inherits `sorryAx` only through the repo's *definition*
of Gerver's constants (`ABφθSpec.existsUnique` is sorried), as would any
theorem mentioning `gerversSofa`.

**Is the underlying problem open?** Essentially resolved: Baek's
[*Optimality of Gerver's Sofa*, arXiv:2411.19826](https://arxiv.org/abs/2411.19826)
proves Gerver's sofa is the unique maximizer up to rigid motion (Thm 1.1.1);
under review at Annals of Mathematics. The repo already tags the optimality
statement `research solved` citing this paper.

---

## Finding 10 — Steiner systems via degenerate designs (2 `research solved`)

**Statements**: `infinitely_many_steiner_t4`, `infinitely_many_steiner_t5`
(`Wikipedia/SteinerSystem.lean`), attributed to Keevash's celebrated 2014
existence theorem.

**Defect.** The `SteinerSystem t k n` structure never requires `t < k < n`, so
the degenerate system on `n` points whose single block is `Finset.univ` is an
`S(t, n, n)` for every `n` — infinitely many Steiner systems, no combinatorics.

**Proof** ([`Solutions.lean`](./Solutions.lean)): degenerate systems plus
injectivity of `n ↦ ⟨n, n, _⟩`.

**Is the underlying problem open?** No — the intended statement is Keevash's
theorem (arXiv:1401.3665). But the formalization proves *itself* without it.
The genuinely open neighbor in the same file (`large_steiner_systems`, explicit
witness with `5 < t < 10`, `n < 200`) is **not** affected: its `n > k > t`
fields exclude degenerate systems.

---

---

# Part II — Genuine mathematical results (second pass)

The findings above are all *formalization* defects. This second pass targeted
real mathematics: statements whose underlying problem has actually been
settled, and one new theorem. Six more Lean files, all sorry-free.

| File | What it establishes |
|---|---|
| [`JacobianCounterexample.lean`](./JacobianCounterexample.lean) | **The Jacobian conjecture is false** — refutes the repo's `research open` statement |
| [`Erdos486Strong.lean`](./Erdos486Strong.lean) | Erdős 486 stays false even for positive moduli — corrects my own Part I advice |
| [`Erdos457.lean`](./Erdos457.lean) | `erdos_457.variants.qnk` follows from the *solved* `erdos_457` |
| [`Green1.lean`](./Green1.lean) | Green Problem 1 is solved (Bedert 2025); reduction to the repo's form |
| [`Green19.lean`](./Green19.lean) | `green_19.lower`/`.upper` follow from the *solved* `green_19` |

## II.1 — The Jacobian conjecture is FALSE (`Wikipedia/JacobianConjecture.lean`)

The repository tags `jacobian_conjecture` as `research open`. It was
**disproved on 19 July 2026** by Levent Alpöge (problem posed by Akhil Mathew;
discovery computer-assisted). The counterexample is an explicit map ℚ³→ℚ³:

```
P = (1+xy)³z + y²(1+xy)(4+3xy)
Q = y + 3x(1+xy)²z + 3xy²(4+3xy)
R = 2x − 3x²y − x³z
```

`det J_F = −2` identically — a Keller map — yet the three *distinct* points
`(0,0,−1/4)`, `(1,−3/2,13/2)`, `(−1,3/2,13/2)` all map to `(−1/4,0,0)`.
**I re-verified this here independently with exact rational arithmetic, in two
separate implementations (sympy and plain Python `Fraction`)** before
formalizing anything.

Because the repo statement quantifies over an arbitrary `Fintype σ` and any
characteristic-0 field, the `σ = Fin 3`, `k = ℚ` instance refutes it. The
proof uses the file's own `comp_aeval`: a two-sided inverse `G` forces
`G.aeval ∘ F.aeval = id`, hence `F.aeval` injective — contradicted by the
collision. Formalized sorry-free as `jacobianDet_eq`, `isUnit_jacobianDet`,
`aeval_collision`, `not_injective_aeval`, `not_jacobian_conjecture`.

Adjoining identity coordinates extends this to every dimension ≥ 3.
**Dimension 2 remains open.** The statement should be retagged
`research solved` (answer: refuted).

*Refs:* [Tao's digestion](https://terrytao.wordpress.com/2026/07/21/a-digestion-of-the-jacobian-conjecture-counterexample/),
[Secret Blogging Seminar](https://sbseminar.wordpress.com/2026/07/20/the-new-counterexample-to-the-jacobian-conjecture/).

## II.2 — Erdős 486 is still false for positive moduli (correcting Part I)

Finding 4 above disproved `erdos_486` via the degenerate modulus `n = 0`, and
I recommended "quantify over `n ≥ 1`" as the fix. **That advice was
incomplete, and this file proves it.** The original problem also carries the
guard that a modulus `n` only constrains integers `m > n`; without it the
statement is false using only *large* moduli.

Construction: kill the block `[2^(10^j), 2^(2·10^j))` with the single modulus
`2^(10^(j+1))`, whose residues below it pin down individual integers.
Translates are negligible — `b_i/nMod_i = 2^(−8·10^i)`, summing to `≤ 1/128`.
The surviving set's log-density partial sums oscillate between `≤ 0.6` and
`≥ 0.8`, so no logarithmic density exists (`erdos_486_rhs_false_pos_moduli`,
624 lines, sorry-free).

This does **not** resolve the genuine Erdős problem, which keeps the `m > n`
guard and remains open.

## II.3 — Problems the repo calls open that the literature has settled

| Statement | Status | Evidence |
|---|---|---|
| `GreensOpenProblems/1.lean` `green_1` | **Solved**, answer `True` | Bedert, [arXiv:2502.08624](https://arxiv.org/abs/2502.08624): sum-free subset of size `n/3 + c log log n`. Green's own 2025 update marks it solved. [`Green1.lean`](./Green1.lean) proves the reduction from his asymptotic bound to the repo's all-`n` form (small `n` absorbed since `Ω` need only tend to infinity). |
| `GreensOpenProblems/14.lean` — ~20 decls `W_3_t_lower` | **Known theorems** | Each is `W(3,t) ≥ v` with the docstring citing *[AKS14, Table 2]* as the source. Those bounds are published (SAT-certified partitions); what AKS14 *conjectures* is that they are **exact**. Only the `≥` direction is formalized, so all should be `research solved`. |
| `ErdosProblems/457.lean` `variants.qnk` | **Follows from solved `erdos_457`** | If every prime `≤ (2+ε)log n` divides the product, the least prime *not* dividing it exceeds that bound; same `ε`, set inclusion, infinitude transfers. Proved in [`Erdos457.lean`](./Erdos457.lean). |
| `GreensOpenProblems/19.lean` `green_19.lower`, `.upper` | **Follow from solved `green_19`** | `C = 4` is tagged solved ([FSS20]); `C ≥ 3.13` and `C ≤ 4` are immediate, and the docstrings attribute both to [Ma21]. Proved in [`Green19.lean`](./Green19.lean). |
| `ErdosProblems/330.lean` | **Solved** (Turturean, ~May 2026) | [erdosproblems.com/330](https://www.erdosproblems.com/330); repo [issue #491](https://github.com/google-deepmind/formal-conjectures/issues/491) already open. |

Further Erdős problems reported solved Apr–Jun 2026 but not yet reflected in
the repo — **each needs its exact statement checked against the solution
before retagging**: 346, 741 (part ii), 750, 865, 996, and possibly the 125
case-variants. Source: the curated
[AI-contributions wiki](https://github.com/teorth/erdosproblems/wiki/AI-contributions-to-Erd%C5%91s-problems).

Deliberately **not** retagged: the separable-Hilbert invariant subspace
problem (Enflo's claimed proof is not settled in the community), and
`Poincare.lean`'s `smooth_other_cases` (Lin–Wang–Xu settled dim 126's θ₆, which
does not by itself decide the repo's statement).

## II.4 — A negative result worth recording

Extending my Part I counterexample search for **A067720** (`φ(k²+1) = k·φ(k+1)`
⟹ `k+1` prime, except `k = 8`) from `k ≤ 3×10⁵` to **`k ≤ 10⁷`** — 48,913
terms, via a quadratic-residue sieve on `k²+1` — found **zero** counterexamples.
`k = 8` really is the lone exception in that range. (The residual after sieving
primes up to `k` is provably 1 or prime, since two primes `> k` cannot multiply
to `k²+1`.) The conjecture looks solid; no refutation available cheaply.

---

## Flagged but not resolved

Three further defects were identified but are **not** cheaply provable and are
recorded here as formalization-fidelity flags only:

* **`ErdosProblems/522.lean`** (`erdos_522`, `.variants.zero_one`) —
  `pdf.IsUniform (toFun i) {-1,1} ℙ volume` uses the *Lebesgue* measure on ℂ,
  in which `{-1,1}` is null, so `cond volume {-1,1} = 0` and the hypothesis
  degenerates to "each coefficient is not a.e.-measurable" — saying nothing
  about ±1 values. Refuting it needs an explicit junk probability space.
* **`ErdosProblems/996.lean`** — `fourierPartial f k` sums
  `fourierCoeff f k • fourier i x` (coefficient index `k` frozen instead of
  the summation index `i`), so it is `|ĉ_k(f)|` times the Dirichlet kernel,
  not a partial sum; and the hypothesis bounds the partial sum's norm rather
  than the tail `‖f − f_k‖₂`. Editorial fix: `fourierCoeff f i`.
* **`Wikipedia/HardyLittlewood.lean`** (`first_hardy_littlewood_conjecture`) —
  states `=O` where the conjecture asserts asymptotic *equivalence*, weakening
  it to a Brun/Selberg sieve upper bound (known since 1919); also lacks a
  distinctness hypothesis on the tuple.

---

## Negative results (evidence the rest is robust)

* The **full tactic sweep** over all 1,166 research-open statements produced
  zero genuine automated solves.
* Formalizations checked by hand and found **correct** (traps avoided):
  Kaplansky (`IsMulTorsionFree` present), Chvátal (`Nonempty α` present),
  Carmichael totient (`m ≠ n` present), Büchi `M = 5` (per-`M` counterexamples
  in test lemmas), Hilbert–Smith (real manifold hypotheses), invariant subspace
  problem (nontriviality inside `ClosedInvariantSubspace`), Selfridge's
  Fermat-factor conjecture, Gilbreath, Agrawal, Brennan, Green 24,
  moving-sofa optimality, `RiemannZetaValues`, Erdős 1041, superperfect
  numbers, Catch-Up, Wolstenholme, Euler bricks.
* **Computational counterexample searches** (no hits, confirming openness):
  A56777 "members come from prime quadruples" (all 10 terms below 2×10⁷),
  A63880 "terms ≡ 108 mod 216" (all 56,297 terms below 2×10⁷),
  A67720 "k+1 prime except k = 8" (all terms up to k ≈ 4.5×10³).

---

*Reproduce with the repo's toolchain: `lake exe cache get`, `lake build
FormalConjectures.Util.ProblemImports`, then `lake env lean
workspace/claude/<file>.lean` for each file above.*
