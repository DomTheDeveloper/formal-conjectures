#!/usr/bin/env python3
"""Erdos 307 coprime-variant search, reformulated as constrained Egyptian fractions.

We need pairwise-coprime P, Q subset of {2,3,...}, |P|,|Q| >= 2, with
    (sum 1/p)(sum 1/q) = 1,
i.e. sum_{q in Q} 1/q  =  1 / (sum_{p in P} 1/p)  exactly.

So: enumerate modest P, then ask whether the *exact rational* t = 1/(sum 1/P) admits
a representation as a sum of reciprocals of pairwise-coprime integers >= 2. That is a
targeted backtracking search, vastly better than blind enumeration of Q.
"""
import sys
from fractions import Fraction
from math import gcd

NP = int(sys.argv[1]) if len(sys.argv) > 1 else 60      # bound on elements of P
SIZEP = int(sys.argv[2]) if len(sys.argv) > 2 else 4    # max |P|
MAXQ = int(sys.argv[3]) if len(sys.argv) > 3 else 6     # max |Q|
QCAP = int(sys.argv[4]) if len(sys.argv) > 4 else 100000  # bound on elements of Q

found = []


def egyptian(target, start, chosen, slots):
    """Find pairwise-coprime denominators >= start summing (as 1/d) to exactly target."""
    if target == 0:
        return list(chosen) if len(chosen) >= 2 else None
    if slots == 0 or target < 0:
        return None
    # need 1/start*slots >= target  =>  start <= slots/target
    if Fraction(slots, start) < target:
        return None
    lo = max(start, (target.denominator + target.numerator - 1) // target.numerator)  # ceil(1/target)
    hi = int(Fraction(slots, target)) + 1
    for d in range(lo, min(hi, QCAP) + 1):
        if any(gcd(d, c) != 1 for c in chosen):
            continue
        r = target - Fraction(1, d)
        if r < 0:
            break
        chosen.append(d)
        res = egyptian(r, d + 1, chosen, slots - 1)
        if res is not None:
            return res
        chosen.pop()
    return None


def dfs_p(start, chosen, cursum):
    if len(chosen) >= 2:
        t = 1 / cursum                      # required sum for Q
        q = egyptian(t, 2, [], MAXQ)
        if q is not None:
            P = tuple(chosen)
            found.append((P, tuple(q), cursum, t))
            print(f"*** SOLUTION: P={P} (sum {cursum})  Q={tuple(q)} (sum {t})  product={cursum*t}")
            sys.stdout.flush()
    if len(chosen) == SIZEP:
        return
    for x in range(start, NP + 1):
        if all(gcd(x, c) == 1 for c in chosen):
            chosen.append(x)
            dfs_p(x + 1, chosen, cursum + Fraction(1, x))
            chosen.pop()


dfs_p(2, [], Fraction(0))
print(f"\ndone: |P| bound {NP}/size {SIZEP}, |Q| size {MAXQ} denominators <= {QCAP}")
print(f"solutions found: {len(found)}")
