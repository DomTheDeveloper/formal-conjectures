#!/usr/bin/env python3
"""Exact exhaustive audit for the most-unfair binary Litt-word theorem."""

from fractions import Fraction
from itertools import product
from math import sqrt
import argparse


def theta(u: tuple[int, ...], v: tuple[int, ...]) -> Fraction:
    n = len(u)
    return sum(
        (Fraction(1 << k, 1 << n) for k in range(1, n) if u[n-k:] == v[:k]),
        Fraction(0),
    )


def is_constant(w: tuple[int, ...]) -> bool:
    return all(x == w[0] for x in w)


def endpoint_flip_pair(a: tuple[int, ...], b: tuple[int, ...]) -> bool:
    if is_constant(a):
        a, b = b, a
    if not is_constant(b):
        return False
    differences = [i for i, (x, y) in enumerate(zip(a, b)) if x != y]
    return differences in ([0], [len(a) - 1])


def audit(n: int) -> None:
    words = list(product((0, 1), repeat=n))
    candidate = Fraction((1 << n) - 2, 1 << n)
    best_squared = Fraction(-1)
    maximizers: list[tuple[tuple[int, ...], tuple[int, ...]]] = []
    min_positive_d: Fraction | None = None

    for a_word in words:
        aa = theta(a_word, a_word)
        for b_word in words:
            if a_word == b_word:
                continue
            bb = theta(b_word, b_word)
            ab = theta(a_word, b_word)
            ba = theta(b_word, a_word)
            variance_factor = 1 + aa + bb - ab - ba
            assert variance_factor >= 0
            if variance_factor > 0 and (
                min_positive_d is None or variance_factor < min_positive_d
            ):
                min_positive_d = variance_factor

            delta = abs(aa - bb)
            score_squared = (
                Fraction(0)
                if variance_factor == 0
                else delta * delta / variance_factor
            )
            assert score_squared <= candidate * candidate, (
                n,
                a_word,
                b_word,
                score_squared,
                candidate * candidate,
            )
            if score_squared > best_squared:
                best_squared = score_squared
                maximizers = [(a_word, b_word)]
            elif score_squared == best_squared:
                maximizers.append((a_word, b_word))

    assert best_squared == candidate * candidate
    assert len(maximizers) == 8
    assert all(endpoint_flip_pair(a, b) for a, b in maximizers)
    print(
        f"n={n}: words={len(words)}, ordered pairs={len(words) * (len(words) - 1)}, "
        f"max={sqrt(float(best_squared)):.12g}, maximizers={len(maximizers)}, "
        f"min positive D={min_positive_d}"
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-length", type=int, default=10)
    args = parser.parse_args()
    if args.max_length < 2:
        raise SystemExit("--max-length must be at least 2")
    for n in range(2, args.max_length + 1):
        audit(n)


if __name__ == "__main__":
    main()
