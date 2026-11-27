"""Reproduce the modular certificates and prime lists with Python 3."""

from math import isqrt


def certificate(d, modulus, last):
    """Return (A(last), B(last), product of A(0)..A(last)) modulo modulus."""
    a, b, product = 1, 0, 1
    for k in range(1, last + 1):
        a, b = (a - d * k * b) % modulus, (b + k * a) % modulus
        product = product * a % modulus
    return a, b, product


def is_prime(n):
    return n >= 2 and all(n % k for k in range(2, isqrt(n) + 1))


def nondivisor_primes(d, bound):
    """For prime p, finite_test in RealPrimeLists.lean proves this criterion."""
    result = []
    for p in range(2, bound + 1):
        if is_prime(p):
            _, b, product = certificate(d, p, 2 * p)
            assert b == 0
            if product != 0:
                result.append(p)
    return result


def exact_imaginary_terms(d, bound):
    a, b = 1, 0
    for k in range(1, bound + 1):
        a, b = a - d * k * b, b + k * a
        yield k, b


if __name__ == "__main__":
    for n, expected in [(138, (2, 0, 20)), (139, (2, 0, 40))]:
        result = certificate(5, 139, n)
        assert result == expected
        print(f"d=5, p=139, n={n}: {result}")

    cases = [
        ("A363409", 2, 101, [2, 5, 13, 23, 29, 31, 47, 53, 61, 71, 101]),
        ("A363413", 4, 79, [2, 3, 11, 19, 23, 31, 47, 59, 67, 71, 79]),
        ("A363415", 5, 197, [5, 11, 13, 31, 53, 79, 97, 113, 137, 139, 157, 179, 193, 197]),
    ]
    for name, d, bound, expected in cases:
        result = nondivisor_primes(d, bound)
        assert result == expected
        print(f"{name}, primes through {bound}: {result}")

    for d in range(2, 10):
        for n, b in exact_imaginary_terms(d, 200):
            triangle = n * (n + 1) // 2
            assert b != 0 and (b - triangle) % (d * triangle) == 0
    print("Exact-integer triangular-factor checks passed for d = 2..9 and n = 1..200.")
