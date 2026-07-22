#!/usr/bin/env python3
"""Enumerate the exact low-minimum-degree sequence remainder for WOWII 217.

This is diagnostic proof-development code.  It uses the repository's
Havel--Hakimi residue convention, checks graphicality independently, and
records the sequences not covered by the Hamilton-path form of Chvatal's
degree criterion after the minimum-degree >= 4 branch is removed.
"""

from __future__ import annotations

from itertools import combinations_with_replacement


def hh_step_desc(s: tuple[int, ...]) -> tuple[int, ...]:
    if not s:
        return ()
    d, *rest = s
    out = [max(0, x - 1) if i < d else x for i, x in enumerate(rest)]
    return tuple(sorted(out, reverse=True))


def residue(s: tuple[int, ...]) -> int:
    cur = tuple(sorted(s, reverse=True))
    while cur and cur[0] != 0:
        cur = hh_step_desc(cur)
    return len(cur)


def is_graphical(s: tuple[int, ...]) -> bool:
    cur = list(sorted(s, reverse=True))
    while cur:
        if cur[0] == 0:
            return True
        d = cur.pop(0)
        if d > len(cur):
            return False
        for i in range(d):
            cur[i] -= 1
            if cur[i] < 0:
                return False
        cur.sort(reverse=True)
    return True


def chvatal_path_holds(desc: tuple[int, ...]) -> bool:
    """Hamilton-path Chvatal condition, via adjoining one universal vertex.

    For ascending d_1 <= ... <= d_n, for every i < (n+1)/2:
      d_i < i  implies  d_{n+1-i} >= n-i,
    with one-based indexing.
    """
    asc = tuple(reversed(desc))
    n = len(asc)
    for i in range(1, (n + 1) // 2 + 1):
        if 2 * i >= n + 1:
            continue
        left = asc[i - 1]
        right = asc[n - i]
        if left < i and right < n - i:
            return False
    return True


def main() -> None:
    rows: list[tuple[int, tuple[int, ...]]] = []
    totals: dict[int, int] = {}
    for n in range(2, 15):
        max_degree = min(6, n - 1)
        count = 0
        # combinations_with_replacement is ascending; reverse for repository order.
        for asc in combinations_with_replacement(range(1, max_degree + 1), n):
            desc = tuple(reversed(asc))
            if sum(desc) % 2:
                continue
            if min(desc) >= 4:
                continue
            if not is_graphical(desc):
                continue
            if residue(desc) != 2:
                continue
            if chvatal_path_holds(desc):
                continue
            rows.append((n, desc))
            count += 1
        if count:
            totals[n] = count

    print("# C217 low-minimum-degree sequence remainder")
    print()
    print("Generated deterministically from descending positive graphical degree sequences")
    print("with maximum degree at most 6, Havel--Hakimi residue 2, minimum")
    print("degree at most 3, and failure of the Hamilton-path Chvatal criterion.")
    print()
    print(f"Total sequences: **{len(rows)}**")
    print()
    print("Counts by order:")
    for n, count in totals.items():
        print(f"- n={n}: {count}")
    print()
    for idx, (n, seq) in enumerate(rows, 1):
        print(f"{idx:02d}. n={n}: `{list(seq)}`")


if __name__ == "__main__":
    main()
