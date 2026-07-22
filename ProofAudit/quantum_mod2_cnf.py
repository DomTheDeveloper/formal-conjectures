#!/usr/bin/env python3
"""Generate the exact mod-2 CNF for the N=6, D=3 quantum-graph equations.

Any integer solution reduces modulo 2 to a Boolean solution.  The three cases
exhaust the orbit of an active colour-1 perfect matching under the stabilizer
of the fixed active colour-0 matching.
"""

from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path

N = 6
D = 3
M0 = ((0, 1), (2, 3), (4, 5))
M1_CASES = {
    "same": ((0, 1), (2, 3), (4, 5)),
    "four_plus_two": ((0, 2), (1, 3), (4, 5)),
    "six_cycle": ((0, 2), (1, 4), (3, 5)),
}


def perfect_matchings(vertices: tuple[int, ...]):
    if not vertices:
        yield ()
        return
    u = vertices[0]
    for k in range(1, len(vertices)):
        v = vertices[k]
        rest = vertices[1:k] + vertices[k + 1 :]
        for matching in perfect_matchings(rest):
            yield ((u, v),) + matching


class CNF:
    def __init__(self) -> None:
        self.next_var = 1
        self.names: dict[int, str] = {}
        self.clauses: list[list[int]] = []

    def new_var(self, name: str) -> int:
        v = self.next_var
        self.next_var += 1
        self.names[v] = name
        return v

    def add(self, *lits: int) -> None:
        self.clauses.append(list(lits))

    def unit(self, lit: int) -> None:
        self.add(lit)

    def and3(self, a: int, b: int, c: int, name: str) -> int:
        t = self.new_var(name)
        self.add(-t, a)
        self.add(-t, b)
        self.add(-t, c)
        self.add(t, -a, -b, -c)
        return t

    def xor2(self, a: int, b: int, name: str) -> int:
        y = self.new_var(name)
        # y <-> a XOR b
        self.add(-a, -b, -y)
        self.add(a, b, -y)
        self.add(a, -b, y)
        self.add(-a, b, y)
        return y


def edge_key(u: int, v: int, i: int, j: int):
    assert u < v
    return (u, v, i, j)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--case", choices=sorted(M1_CASES), required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--metadata", type=Path, required=True)
    args = parser.parse_args()

    cnf = CNF()
    weights: dict[tuple[int, int, int, int], int] = {}
    for u in range(N):
        for v in range(u + 1, N):
            for i in range(D):
                for j in range(D):
                    key = edge_key(u, v, i, j)
                    weights[key] = cnf.new_var(f"w_{u}_{v}_{i}_{j}")

    matchings = list(perfect_matchings(tuple(range(N))))
    assert len(matchings) == 15

    # Symmetry breaking, justified as follows.  The monochromatic colour-0
    # equation has odd parity, so at least one perfect-matching monomial is 1.
    # Relabel vertices to make it M0.  The stabilizer of M0 has exactly three
    # orbits on perfect matchings, represented by M1_CASES.
    for u, v in M0:
        cnf.unit(weights[edge_key(u, v, 0, 0)])
    for u, v in M1_CASES[args.case]:
        cnf.unit(weights[edge_key(u, v, 1, 1)])

    for assignment_index, colors in enumerate(itertools.product(range(D), repeat=N)):
        monomials: list[int] = []
        for matching_index, matching in enumerate(matchings):
            factors = [weights[edge_key(u, v, colors[u], colors[v])] for u, v in matching]
            monomials.append(
                cnf.and3(
                    factors[0], factors[1], factors[2],
                    f"term_{assignment_index}_{matching_index}",
                )
            )
        parity = monomials[0]
        for k, term in enumerate(monomials[1:], start=1):
            parity = cnf.xor2(parity, term, f"xor_{assignment_index}_{k}")
        target = len(set(colors)) == 1
        cnf.unit(parity if target else -parity)

    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("w", encoding="utf-8") as out:
        out.write(f"p cnf {cnf.next_var - 1} {len(cnf.clauses)}\n")
        for clause in cnf.clauses:
            out.write(" ".join(map(str, clause)) + " 0\n")

    metadata = {
        "case": args.case,
        "vertices": N,
        "colors": D,
        "weight_variables": len(weights),
        "variables": cnf.next_var - 1,
        "clauses": len(cnf.clauses),
        "fixed_color0_matching": M0,
        "fixed_color1_matching": M1_CASES[args.case],
        "perfect_matchings": matchings,
        "variable_names": cnf.names,
    }
    args.metadata.write_text(json.dumps(metadata, indent=2), encoding="utf-8")
    print(json.dumps({k: metadata[k] for k in ("case", "variables", "clauses")}, indent=2))


if __name__ == "__main__":
    main()
