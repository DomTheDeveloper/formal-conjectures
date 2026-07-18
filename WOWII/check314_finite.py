#!/usr/bin/env python3
"""Independent finite cross-checks for the WOWII 314 C5 proof modules."""

from itertools import product


def adjacent(i: int, j: int) -> bool:
    return (i - j) % 5 in (1, 4)


def check_unique_neighborhood_patterns() -> None:
    accepted = []
    for bits in product((False, True), repeat=5):
        nonempty = any(bits)
        independent = all(
            not (bits[i] and bits[j])
            for i, j in product(range(5), repeat=2)
            if adjacent(i, j)
        )
        no_singleton = all(
            not bits[i] or any(j != i and bits[j] for j in range(5))
            for i in range(5)
        )
        if not (nonempty and independent and no_singleton):
            continue

        witnesses = [
            k for k in range(5)
            if all(bits[j] == adjacent(k, j) for j in range(5))
        ]
        assert len(witnesses) == 1, (bits, witnesses)
        accepted.append((bits, witnesses[0]))

    assert len(accepted) == 5, accepted


def check_missing_blowup_edge_patterns() -> None:
    oriented_edges = [(i, j) for i, j in product(range(5), repeat=2) if adjacent(i, j)]
    assert len(oriented_edges) == 10

    certificates = {}
    for i, j in oriented_edges:
        witnesses = []
        for a, b, d in product(range(5), repeat=3):
            valid = (
                adjacent(i, a)
                and adjacent(i, b)
                and adjacent(b, d)
                and adjacent(j, d)
                and not adjacent(a, b)
                and not adjacent(a, d)
                and not adjacent(j, a)
                and not adjacent(i, d)
                and not adjacent(j, b)
                and a != b
                and a != d
                and b != d
                and i != d
                and j != a
            )
            if valid:
                witnesses.append((a, b, d))
        assert witnesses, (i, j)
        certificates[(i, j)] = witnesses[0]

    assert len(certificates) == 10


def main() -> None:
    check_unique_neighborhood_patterns()
    check_missing_blowup_edge_patterns()
    print("C5 neighborhood patterns checked: 32")
    print("valid unique bag patterns: 5")
    print("oriented cycle-edge certificates: 10")
    print("missing finite cases: 0")


if __name__ == "__main__":
    main()
