#!/usr/bin/env python3
"""Erdos 307 coprime variant (1 excluded) — EXACT search via a forced-product lemma.

LEMMA. Let P be a finite set of pairwise-coprime integers >= 2 and write
    sum_{p in P} 1/p = N_P / D_P,  D_P = prod P,  N_P = sum_p (D_P / p).
Then gcd(N_P, D_P) = 1.
  Proof: for d in P, every term D_P/p with p != d is divisible by d, while the term
  D_P/d = prod_{p != d} p is coprime to d by pairwise coprimality. So N_P = D_P/d
  (mod d) is invertible mod d, giving gcd(N_P, d) = 1 for every d in P.

COROLLARY (the search constraint). If (sum 1/P)(sum 1/Q) = 1 with both P and Q
pairwise coprime, then writing the two sums in lowest terms as N_P/D_P and N_Q/D_Q,
    N_P * N_Q = D_P * D_Q.
Since gcd(N_P, D_P) = 1 we get N_P | D_Q, and gcd(N_Q, D_Q) = 1 gives N_Q | D_P;
substituting D_Q = N_P*k and D_P = N_Q*m yields m*k = 1, hence
    prod Q = N_P   and   prod P = N_Q.
So Q is NOT free: its product is forced to equal the numerator N_P. Because the
elements of Q are pairwise coprime, each maximal prime power of N_P must lie wholly
inside one element, so Q ranges exactly over the set partitions of the prime-power
factorisation of N_P. That is a Bell-number-sized check, not an unbounded search.

This makes the search EXHAUSTIVE for every P considered: if no partition of N_P works,
no Q whatsoever completes that P.
"""
import sys
from fractions import Fraction
from math import gcd
from sympy import factorint

NP_BOUND = int(sys.argv[1]) if len(sys.argv) > 1 else 200
SIZEP = int(sys.argv[2]) if len(sys.argv) > 2 else 5

found = []
checked = 0


def partitions(items):
    """All set partitions of `items` (list) — yields lists of blocks."""
    if not items:
        yield []
        return
    first, rest = items[0], items[1:]
    for p in partitions(rest):
        # first as its own block
        yield [[first]] + p
        # first joined to each existing block
        for i in range(len(p)):
            yield p[:i] + [[first] + p[i]] + p[i + 1:]


def try_P(P):
    """Exhaustively decide whether any Q completes this P."""
    global checked
    checked += 1
    D = 1
    for p in P:
        D *= p
    N = sum(D // p for p in P)
    # Q must satisfy prod Q = N, pairwise coprime => partition prime powers of N.
    pp = [q ** e for q, e in factorint(N).items()]
    if len(pp) < 2:            # need |Q| > 1, and each block product >= 2
        return None
    target = Fraction(D, N)    # required sum for Q
    for part in partitions(pp):
        if len(part) < 2:
            continue
        Q = []
        for block in part:
            v = 1
            for x in block:
                v *= x
            Q.append(v)
        if sum(Fraction(1, q) for q in Q) == target:
            return tuple(sorted(Q))
    return None


def dfs(start, chosen):
    if len(chosen) >= 2:
        Q = try_P(chosen)
        if Q is not None:
            P = tuple(chosen)
            found.append((P, Q))
            print(f"*** SOLUTION: P={P}  Q={Q}")
            sys.stdout.flush()
    if len(chosen) == SIZEP:
        return
    for x in range(start, NP_BOUND + 1):
        if all(gcd(x, c) == 1 for c in chosen):
            chosen.append(x)
            dfs(x + 1, chosen)
            chosen.pop()


dfs(2, [])
print(f"\nEXHAUSTIVE over |P| <= {SIZEP}, max(P) <= {NP_BOUND}: "
      f"{checked} candidate sets P, each checked against ALL admissible Q.")
print(f"solutions: {len(found)}")
