#!/usr/bin/env python3
"""Erdos 340 variant: is 33 a difference of two Mian-Chowla (A005282) elements?

Greedy Sidon set: start with 1; repeatedly take the smallest integer that keeps
all pairwise differences distinct. A positive answer to '33 in A-A' is a one-line
Lean witness; a negative search result proves nothing (the problem is open).
"""
import sys

TARGET = 33
N_TERMS = int(sys.argv[1]) if len(sys.argv) > 1 else 3000

seq = [1]
diffs = set()          # all pairwise differences realised so far
seq_set = {1}
c = 1
while len(seq) < N_TERMS:
    c += 1
    new = []
    ok = True
    for a in seq:
        d = c - a
        if d in diffs or d in new:
            ok = False
            break
        new.append(d)
    if ok:
        seq.append(c)
        seq_set.add(c)
        diffs.update(new)

print(f"generated {len(seq)} terms; last = {seq[-1]}")
print(f"first 20: {seq[:20]}")

hits = [(a, b) for b in seq for a in (b - TARGET,) if a in seq_set]
if hits:
    a, b = hits[0]
    print(f"\n*** WITNESS FOUND: {b} - {a} = {TARGET} ***")
    print(f"    indices: a[{seq.index(a)}] = {a}, a[{seq.index(b)}] = {b}")
else:
    print(f"\nNo pair differing by {TARGET} among the first {len(seq)} terms.")

# Which small integers are NOT yet realised as differences? Confirms 33 is the
# smallest unknown, i.e. that the file's claim matches the computed sequence.
missing = [d for d in range(1, 120) if d not in diffs]
print(f"small integers not realised as differences (<120): {missing[:25]}")

# For context: consecutive gaps tell us how plausible a far-out hit is.
gaps = [seq[i + 1] - seq[i] for i in range(len(seq) - 1)]
small_gaps_after = [i for i, g in enumerate(gaps) if g <= TARGET]
print(f"last index with consecutive gap <= {TARGET}: "
      f"{small_gaps_after[-1] if small_gaps_after else None} "
      f"(term {seq[small_gaps_after[-1]] if small_gaps_after else None})")
print(f"min gap in last 100 terms: {min(gaps[-100:])}")
