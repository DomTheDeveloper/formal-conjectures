# Erdős Problem 307 — coprime variant with 1 excluded

**Lean file:** `FormalConjectures/ErdosProblems/307.lean`
**Declaration:** `Erdos307.erdos_307.variants.coprime_one_notMem`
**Status:** attacking
**Category:** `research open`
**AMS:** 5, 11

## Statement

Are there finite sets $P, Q$ of pairwise coprime integers, each of size $> 1$, with
$1 \notin P \cup Q$, such that

$$\left(\sum_{p \in P} \frac1p\right)\left(\sum_{q \in Q} \frac1q\right) = 1\ ?$$

The file records that **no example is known**. The variant that permits $1$ is solved —
Cambie's $1 = (1 + \tfrac15)(\tfrac12 + \tfrac13)$ and $(1 + \tfrac1{41})(\tfrac12 + \tfrac13 + \tfrac17)$
are in the file as `variants.coprime`. Excluding $1$ is what makes it open: without it,
reaching a reciprocal sum above $1$ needs at least four elements
($\tfrac12+\tfrac13+\tfrac15+\tfrac17 = 1.176\ldots$).

## References

- [erdosproblems.com/307](https://www.erdosproblems.com/307)
- Barbeau, E. J., *Computer challenge corner: Problem 477: A brute force program.*

## The forced-product lemma

This is the useful outcome so far. It converts an unbounded two-sided search into an
exhaustive finite check for each $P$.

**Lemma.** Let $P$ be a finite set of pairwise coprime integers $\ge 2$, and write
$\sum_{p \in P} 1/p = N_P / D_P$ with $D_P = \prod P$ and $N_P = \sum_{p} D_P/p$.
Then $\gcd(N_P, D_P) = 1$.

*Proof.* Fix $d \in P$. Every term $D_P/p$ with $p \ne d$ is divisible by $d$, while the
term $D_P/d = \prod_{p \ne d} p$ is coprime to $d$ by pairwise coprimality. Hence
$N_P \equiv D_P/d \pmod d$ is invertible mod $d$, so $\gcd(N_P, d) = 1$ for every
$d \in P$, and therefore $\gcd(N_P, D_P) = 1$. $\square$

**Corollary.** If $(\sum 1/P)(\sum 1/Q) = 1$ with $P, Q$ pairwise coprime, then

$$\prod Q = N_P \qquad\text{and}\qquad \prod P = N_Q .$$

*Proof.* Both fractions are in lowest terms by the Lemma, so $N_P N_Q = D_P D_Q$. From
$\gcd(N_P, D_P) = 1$ we get $N_P \mid D_Q$, and from $\gcd(N_Q, D_Q) = 1$ we get
$N_Q \mid D_P$. Writing $D_Q = N_P k$ and $D_P = N_Q m$ and substituting gives $mk = 1$,
so $m = k = 1$. $\square$

**Why this matters for search.** $Q$ is not free: its product is *forced* to equal $N_P$.
Since the elements of $Q$ are pairwise coprime, each maximal prime power of $N_P$ lies
wholly inside a single element, so the admissible $Q$ are exactly the set partitions of
the prime-power factorisation of $N_P$. That is a Bell-number-sized check (typically
$\omega(N_P) \le 8$), so **for each $P$ the search over $Q$ is exhaustive, not sampled**.
The only incompleteness left is the enumeration of $P$.

Sanity check against the known $1$-permitting examples: $P = \{1,5\}$ gives $N_P = 6 = \prod\{2,3\}$;
$P = \{1,41\}$ gives $N_P = 42 = \prod\{2,3,7\}$. Both match.

## Search log

Scripts in the audit scratchpad (`search_erdos307*.py`); `search_erdos307_exact.py` is the
one implementing the corollary.

| Method | Bound | Result |
|---|---|---|
| Blind enumeration of both sides | elements ≤ 100, sizes ≤ 5 (3.08M sets) | none |
| Egyptian-fraction backtracking on $1/(\sum 1/P)$ | $P$ ≤ 80, size ≤ 4; $Q$ ≤ 6 terms, denominators ≤ 50000 | none |
| **Forced-product (exhaustive in $Q$)** | $\max P \le 60$, $\lvert P\rvert \le 4$ (60544 sets) | none |
| Forced-product | $\max P \le 150$, $\lvert P\rvert \le 5$ | running |

Near-miss from the blind pass, worth recording: $P=\{2,3,5,71,77\}$, $Q=\{2,5,7,13,43\}$
give a product of $6417711217/6417711300 \approx 0.9999999871$.

## Next steps

- [ ] Extend the forced-product search to $\lvert P \rvert \le 6$–$7$. Cost is dominated by
      enumerating $P$; the per-$P$ check is cheap.
- [ ] Derive a lower bound on $\lvert P \rvert + \lvert Q \rvert$ in the style of the
      `erdos_307.barrier` result for primes (Bonfioli 2026 proves ≥ 59 primes and
      $\prod P \ge 2\cdot10^{56}$). The corollary above may give a cheap barrier for the
      coprime case too: $\prod Q = N_P \approx D_P \sum 1/p$ ties the two sides tightly.
- [ ] The Lemma and Corollary are elementary and self-contained — they belong in Lean
      regardless of whether a witness is ever found, either as API in this file or in
      `FormalConjecturesForMathlib/`. That is a real, provable contribution to an open
      problem and needs no witness.

## Dead ends

- **Blind two-sided enumeration** — wasteful. The forced-product corollary makes it obsolete;
  do not repeat it.
- **Naive Mian–Chowla generation** (for the sibling problem `ErdosProblems/340`) timed out:
  the sequence grows like $n^3$, so term-by-term greedy generation is the wrong algorithm.

## Log

### 2026-07-27

- Ran three searches; no witness. Established the forced-product lemma and verified it
  against both known $1$-permitting examples.
- Nothing here is compiled: this container has no Mathlib build cache. The Lemma/Corollary
  are pen-and-paper proofs pending formalisation.
