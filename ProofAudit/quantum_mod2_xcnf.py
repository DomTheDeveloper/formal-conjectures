#!/usr/bin/env python3
"""Generate CNF+XOR instances for the four residual K3,3 quantum cases.

The 3-input matching monomials are Tseitin encoded with ordinary CNF clauses.
Each perfect-matching parity equation is emitted as one native XOR clause,
which is consumed by CryptoMiniSat and certified through FRAT-XOR/XLRUP.
"""

from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path

import quantum_mod2_cnf as base


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--k33-pattern", choices=base.K33_PATTERNS, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--metadata", type=Path, required=True)
    args = parser.parse_args()

    case = "six_cycle"
    case2_index = 6
    color2_representatives = base.color2_orbit_representatives(case)
    fixed_color2 = color2_representatives[case2_index]

    cnf = base.CNF()
    weights: dict[tuple[int, int, int, int], int] = {}
    for u in range(base.N):
        for v in range(u + 1, base.N):
            for i in range(base.D):
                for j in range(base.D):
                    key = base.edge_key(u, v, i, j)
                    weights[key] = cnf.new_var(f"w_{u}_{v}_{i}_{j}")

    matchings = list(base.perfect_matchings(tuple(range(base.N))))
    assert len(matchings) == 15

    for u, v in base.M0:
        cnf.unit(weights[base.edge_key(u, v, 0, 0)])
    for u, v in base.M1_CASES[case]:
        cnf.unit(weights[base.edge_key(u, v, 1, 1)])
    for u, v in fixed_color2:
        cnf.unit(weights[base.edge_key(u, v, 2, 2)])

    residual_orbit = [
        base.edge_key(0, 2, 0, 0),
        base.edge_key(3, 5, 0, 0),
        base.edge_key(1, 4, 0, 0),
    ]
    for key, bit in zip(residual_orbit, args.k33_pattern, strict=True):
        variable = weights[key]
        cnf.unit(variable if bit == "1" else -variable)

    xor_constraints: list[tuple[list[int], bool]] = []
    for assignment_index, colors in enumerate(
        itertools.product(range(base.D), repeat=base.N)
    ):
        monomials: list[int] = []
        for matching_index, matching in enumerate(matchings):
            factors = [
                weights[base.edge_key(u, v, colors[u], colors[v])]
                for u, v in matching
            ]
            monomials.append(
                cnf.and3(
                    factors[0], factors[1], factors[2],
                    f"term_{assignment_index}_{matching_index}",
                )
            )
        target = len(set(colors)) == 1
        xor_constraints.append((monomials, target))

    args.output.parent.mkdir(parents=True, exist_ok=True)
    total_constraints = len(cnf.clauses) + len(xor_constraints)
    with args.output.open("w", encoding="utf-8") as out:
        out.write(f"p cnf {cnf.next_var - 1} {total_constraints}\n")
        for clause in cnf.clauses:
            out.write(" ".join(map(str, clause)) + " 0\n")
        for variables, rhs in xor_constraints:
            literals = list(variables)
            # CryptoMiniSat's extended DIMACS convention makes every XOR line
            # assert that the XOR of its *literals* is true. Negating one
            # literal flips the right-hand side.
            if not rhs:
                literals[0] = -literals[0]
            out.write("x " + " ".join(map(str, literals)) + " 0\n")

    metadata = {
        "case": case,
        "case2_index": case2_index,
        "k33_pattern": args.k33_pattern,
        "vertices": base.N,
        "colors": base.D,
        "weight_variables": len(weights),
        "variables": cnf.next_var - 1,
        "ordinary_clauses": len(cnf.clauses),
        "xor_clauses": len(xor_constraints),
        "constraints": total_constraints,
        "fixed_color0_matching": base.M0,
        "fixed_color1_matching": base.M1_CASES[case],
        "fixed_color2_matching": fixed_color2,
        "k33_residual_orbit": residual_orbit,
        "perfect_matchings": matchings,
        "variable_names": cnf.names,
    }
    args.metadata.write_text(json.dumps(metadata, indent=2), encoding="utf-8")
    print(json.dumps({
        key: metadata[key]
        for key in (
            "k33_pattern", "variables", "ordinary_clauses",
            "xor_clauses", "constraints",
        )
    }, indent=2))


if __name__ == "__main__":
    main()
