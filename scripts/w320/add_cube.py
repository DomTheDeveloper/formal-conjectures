#!/usr/bin/env python3
"""Append a complete assignment cube to a DIMACS CNF instance.

The selected variables are fixed by bits of ``--mask``.  Bit 0 controls the
first variable, bit 1 the second, and so on.  A set bit emits a positive unit
clause; a clear bit emits a negative unit clause.
"""

from __future__ import annotations

import argparse
from pathlib import Path


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--mask", type=int, required=True)
    parser.add_argument("--vars", type=int, nargs="+", required=True)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    if args.mask < 0 or args.mask >= (1 << len(args.vars)):
        raise ValueError("mask does not fit the selected variables")
    if len(set(args.vars)) != len(args.vars):
        raise ValueError("cube variables must be distinct")
    if any(variable <= 0 for variable in args.vars):
        raise ValueError("DIMACS variables are positive integers")

    lines = args.input.read_text(encoding="ascii").splitlines()
    header_index = next(
        (index for index, line in enumerate(lines) if line.startswith("p cnf ")),
        None,
    )
    if header_index is None:
        raise ValueError("missing DIMACS header")

    fields = lines[header_index].split()
    if len(fields) != 4:
        raise ValueError(f"invalid DIMACS header: {lines[header_index]!r}")
    variable_count = int(fields[2])
    clause_count = int(fields[3])
    if max(args.vars) > variable_count:
        raise ValueError("cube variable exceeds DIMACS variable count")

    units: list[str] = []
    assignments: list[str] = []
    for bit, variable in enumerate(args.vars):
        value = bool((args.mask >> bit) & 1)
        literal = variable if value else -variable
        units.append(f"{literal} 0")
        assignments.append(f"x{variable}={int(value)}")

    lines[header_index] = f"p cnf {variable_count} {clause_count + len(units)}"
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text("\n".join([*lines, *units, ""]), encoding="ascii")

    print(f"mask={args.mask}")
    print("assignments=" + ",".join(assignments))
    print(f"variables={variable_count}")
    print(f"clauses={clause_count + len(units)}")


if __name__ == "__main__":
    main()
