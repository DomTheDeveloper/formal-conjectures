"""Independent exact valuation scan for OEIS A363411 and A363416."""

from argparse import ArgumentParser


def scan(d, exponent_per_block, component, slope_denominator, limit):
    modulus = 1 << (limit.bit_length() + 36)
    scale = 1 << exponent_per_block
    a, b = 1, 0
    largest = (-1, 0, 0)
    exceptions = 0

    for block in range(limit // 8 + 1):
        for offset in range(8):
            n = 8 * block + offset
            if 0 < n <= limit:
                residue = (a, b)[component] % modulus
                if residue == 0:
                    raise ArithmeticError(f"Increase the precision at index {n}")
                order = (residue & -residue).bit_length() - 1
                valuation = exponent_per_block * block + order
                numerator = abs(slope_denominator * valuation - n)
                if numerator > largest[0]:
                    largest = (numerator, n, valuation)
                # Compare absolute error against log2(n+2)+10 with integers.
                excess = numerator - 10 * slope_denominator
                if excess > 0 and 1 << excess > (n + 2) ** slope_denominator:
                    exceptions += 1

            k = n + 1
            a, b = a - d*k*b, b + k*a

        # The entire eight-factor block is coefficientwise divisible by scale.
        # Division therefore preserves the full precision of the input residues.
        assert a % scale == 0 and b % scale == 0
        a, b = (a // scale) % modulus, (b // scale) % modulus

    return largest, exceptions


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--limit", type=int, default=1_000_000)
    args = parser.parse_args()
    if args.limit < 1:
        parser.error("--limit must be positive")
    for seq, d, scale, coordinate, den in [
        ("A363411", 3, 4, 0, 2),
        ("A363416", 5, 2, 1, 4),
    ]:
        (num, n, val), exceptions = scan(d, scale, coordinate, den, args.limit)
        print(f"{seq}: max absolute error {num}/{den} at n={n}, "
              f"v2={val}; {exceptions} above log2(n+2)+10")
