#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
from pathlib import Path


def progressions(n: int, length: int):
    for d in range(1, (n - 1) // (length - 1) + 1):
        for a in range(1, n - (length - 1) * d + 1):
            yield [a + j * d for j in range(length)]


def generate(n: int) -> list[list[int]]:
    # x_i = true means color 1.
    # Every 3-AP contains a true literal; every 20-AP contains a false literal.
    clauses = list(progressions(n, 3))
    clauses += [[-i for i in p] for p in progressions(n, 20)]
    return clauses


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, default=389)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    clauses = generate(args.n)
    with args.output.open("w", encoding="ascii", newline="\n") as out:
        out.write(f"p cnf {args.n} {len(clauses)}\n")
        for clause in clauses:
            out.write(" ".join(map(str, clause)) + " 0\n")

    data = args.output.read_bytes()
    print(f"variables={args.n}")
    print(f"clauses={len(clauses)}")
    print(f"three_ap_clauses={sum(len(c) == 3 for c in clauses)}")
    print(f"twenty_ap_clauses={sum(len(c) == 20 for c in clauses)}")
    print(f"md5={hashlib.md5(data).hexdigest()}")
    print(f"sha256={hashlib.sha256(data).hexdigest()}")

    if args.n == 389:
        assert len(clauses) == 41426
        assert sum(len(c) == 3 for c in clauses) == 37636
        assert sum(len(c) == 20 for c in clauses) == 3790


if __name__ == "__main__":
    main()
