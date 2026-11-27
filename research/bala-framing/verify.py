"""Exact checks for cubic rows and iterated Apéry/Franel transforms. Python 3.10+."""

from functools import cache
from math import comb


@cache
def row(a, b, n, k):
    """Use (1-x^2)F' = ((A-B)-(A+B)x)F for F=(1+x)^A(1-x)^B."""
    A, B = a * n * k, b * n * k
    previous, current = 0, 1
    for j in range(k):
        numerator = (A - B) * current + (j - 1 - A - B) * previous
        following, remainder = divmod(numerator, j + 1)
        assert remainder == 0
        previous, current = current, following
    value, remainder = divmod(current, n)
    assert remainder == 0
    return value


def binomial(z, k):
    if z >= 0:
        return comb(z, k) if k <= z else 0
    return (-1) ** k * comb(k - z - 1, k)


def direct_row(a, b, n, k):
    value = sum(binomial(a*n*k, j) * binomial(b*n*k, k-j) * (-1)**(k-j)
                for j in range(k+1))
    quotient, remainder = divmod(value, n)
    assert remainder == 0
    return quotient


def apery2(k):
    return sum(comb(k, j)**2 * comb(k+j, j) for j in range(k+1))


def apery3(k):
    return sum((comb(k, j) * comb(k+j, j))**2 for j in range(k+1))


def franel(k):
    return sum(comb(k, j)**3 for j in range(k+1))


def exponential_coefficient(values, exponent, degree):
    """Coefficient of x^degree in exp(exponent * sum(a_j x^j/j))."""
    coefficients = [1]
    for h in range(1, degree+1):
        numerator = exponent * sum(values[j] * coefficients[h-j] for j in range(1, h+1))
        c, remainder = divmod(numerator, h)
        assert remainder == 0
        coefficients.append(c)
    return coefficients[-1]


def valuation(n, p):
    assert n != 0
    n = abs(n)
    exponent = 0
    while n % p == 0:
        n //= p
        exponent += 1
    return exponent


def check_rows():
    count = 0
    for a, b in ((1, -1), (-1, -2), (2, 3), (-3, 2), (0, -1), (-1, 0)):
        for n in (-25, -7, -5, -3, -1, 1, 2, 3, 5, 7, 9, 15, 25):
            for k in range(1, 13):
                assert row(a, b, n, k) == direct_row(a, b, n, k)
            for p, max_r in ((3, 4), (5, 3), (7, 3), (11, 2), (13, 2), (17, 2), (19, 2)):
                for m in (1, 2, p):
                    for r in range(1, max_r+1):
                        N = m * p**r
                        if N > 750:
                            continue
                        t = valuation(N, p)
                        exponent = 3*t + valuation(n, p) - int(p == 3)
                        assert (row(a,b,n,N) - row(a,b,n,N//p)) % p**exponent == 0
                        count += 1
    for n in range(1, 13):
        for k in range(1, 13):
            original = sum(2**j * comb(k,j) * comb(n*k-1,j-1) for j in range(1,k+1))
            assert original == row(1,-1,n,k)
    assert [row(1,-1,1,k) for k in range(1,8)] == [2,8,38,192,1002,5336,28814]
    assert [row(-1,-2,1,k) for k in range(1,8)] == [1,5,19,85,376,1715,7890]
    assert [row(-1,-2,-5,k) for k in range(1,8)] == [1,-7,46,-247,626,8642,-194480]
    for a,b,n,N,p,difference,v in (
        (1,-1,1,5,5,1000,3), (-1,-2,1,5,5,375,3),
        (1,-1,1,3,3,36,2), (-1,-2,1,3,3,18,2),
        (1,-1,5,10,5,5644536540000,4), (-1,-2,-5,5,5,625,4)):
        assert row(a,b,n,N) - row(a,b,n,N//p) == difference
        assert valuation(difference,p) == v
    return count


def check_iterations():
    bound, count = 90, 0
    for seed, first in ((apery2,[1,3,37,525]), (apery3,[1,5,123,3650]),
                        (franel,[1,2,18,182,1954])):
        values = [seed(k) for k in range(bound+1)]
        for i in range(1,5):
            values = [1]+[exponential_coefficient(values,k,k) for k in range(1,bound+1)]
            if i == 1:
                assert values[:len(first)] == first, (seed.__name__, values[:len(first)])
            if seed == franel:
                assert all(x % 2 == 0 for x in values[1:])
            for p in (2,3,5,7,11,13,17,19):
                if p == 2 and seed != franel:
                    continue
                for N in range(p,bound+1,p):
                    assert (values[N]-values[N//p]) % p**(2*valuation(N,p)) == 0
                    count += 1
    return count


if __name__ == "__main__":
    print(f"{check_rows()} cubic row congruences")
    print(f"{check_iterations()} iterated quadratic congruences")
