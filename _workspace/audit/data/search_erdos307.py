#!/usr/bin/env python3
"""Erdos 307 coprime variant with 1 excluded (FormalConjectures/ErdosProblems/307.lean).

Seek finite P, Q subset of {2,3,...}, each pairwise coprime, |P|,|Q| >= 2, with
    (sum_{p in P} 1/p) * (sum_{q in Q} 1/q) = 1.
The file records that no example is known. A witness is a one-line Lean proof.

Method: enumerate pairwise-coprime subsets, record the exact rational sum of
reciprocals in a dict {Fraction -> witness set}. A solution is any achieved sum a
whose reciprocal 1/a is also achieved.
"""
import sys
from fractions import Fraction
from math import gcd

N = int(sys.argv[1]) if len(sys.argv) > 1 else 60
MAXSIZE = int(sys.argv[2]) if len(sys.argv) > 2 else 5

sums = {}          # Fraction -> tuple(elements)
count = 0


def dfs(start, chosen, cursum):
    global count
    if len(chosen) >= 2:
        count += 1
        # keep the first witness found for each distinct sum
        if cursum not in sums:
            sums[cursum] = tuple(chosen)
    if len(chosen) == MAXSIZE:
        return
    for x in range(start, N + 1):
        if all(gcd(x, c) == 1 for c in chosen):
            chosen.append(x)
            dfs(x + 1, chosen, cursum + Fraction(1, x))
            chosen.pop()


dfs(2, [], Fraction(0))
print(f"N={N} maxsize={MAXSIZE}: {count} pairwise-coprime sets, {len(sums)} distinct sums")

hits = []
for a, P in sums.items():
    if a == 0:
        continue
    b = 1 / a
    if b in sums:
        Q = sums[b]
        if set(P).isdisjoint(Q) or True:      # P, Q need not be disjoint
            hits.append((P, Q, a, b))

if hits:
    print(f"\n*** {len(hits)} SOLUTION(S) FOUND ***")
    for P, Q, a, b in hits[:10]:
        print(f"    P={P} sum={a}   Q={Q} sum={b}   product={a*b}")
else:
    print(f"\nNo solution with all elements <= {N} and |P|,|Q| <= {MAXSIZE}.")
    # Near-miss via sorted scan (O(n log n)) rather than O(n^2).
    keys = sorted(sums)
    import bisect
    best = None
    for a in keys:
        if a == 0:
            continue
        b = 1 / a
        i = bisect.bisect_left(keys, b)
        for j in (i - 1, i):
            if 0 <= j < len(keys):
                d = abs(keys[j] - b)
                if best is None or d < best[0]:
                    best = (d, a, sums[a], keys[j], sums[keys[j]])
    if best:
        d, a, P, near, Q = best
        print(f"    closest near-miss: P={P} (sum {a}), Q={Q} (sum {near}), "
              f"product={a*near} ~ {float(a*near):.10f}")
