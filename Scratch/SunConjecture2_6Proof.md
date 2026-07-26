# Proof candidate for Zhi-Wei Sun's Conjecture 2.6

## Statement

For every integer `n > 4` and every `1 <= k <= n`, let `pi(x)` denote the
number of primes at most `x`. Then

```text
pi(k n)^(k+1) > pi((k+1)n)^k.
```

This is equivalent to the root form in Sun's paper.

## Main argument

Put

```text
x = k n,
A = pi(x),
B = pi(x+n),
d = B-A.
```

Assume first that `x >= 17`. The Rosser--Schoenfeld lower bound gives

```text
A > x / log x.
```

Because `x >= 5`, every prime in `(x,x+n]` is odd. Among `n` consecutive
integers there are at most `ceil(n/2)` odd integers, hence

```text
d <= ceil(n/2).
```

If `d=0`, the desired inequality is immediate from `A>1`. Otherwise,
`log(1+t)<t` for `t>0` gives

```text
k log(B/A)
  = k log(1+d/A)
  < k d/A
  < k ceil(n/2) log(x)/x
  = (ceil(n/2)/n) log x
  <= (3/5) log x.
```

The final inequality uses `n>=5`, for which

```text
ceil(n/2)/n <= 3/5.
```

It remains to compare `(3/5) log x` with `log A`. For every `x>1`, put
`t=log x>0`. The classical inequality

```text
log t <= t/e < (2/5)t
```

uses `e>5/2`. Therefore

```text
(3/5) log x
  < log x - log(log x)
  = log(x/log x)
  < log A.
```

Combining the inequalities gives

```text
k log(B/A) < log A,
```

so

```text
B^k < A^(k+1).
```

## Finite remainder

The only pairs with `n>=5`, `1<=k<=n`, and `kn<17` are the following.
The last column is `A^(k+1)-B^k`.

| n | k | A=pi(kn) | B=pi((k+1)n) | difference |
|---:|---:|---:|---:|---:|
| 5 | 1 | 3 | 4 | 5 |
| 5 | 2 | 4 | 6 | 28 |
| 5 | 3 | 6 | 8 | 784 |
| 6 | 1 | 3 | 5 | 4 |
| 6 | 2 | 5 | 7 | 76 |
| 7 | 1 | 4 | 6 | 10 |
| 7 | 2 | 6 | 8 | 152 |
| 8 | 1 | 4 | 6 | 10 |
| 8 | 2 | 6 | 9 | 135 |
| 9 | 1 | 4 | 7 | 9 |
| 10 | 1 | 4 | 8 | 8 |
| 11 | 1 | 5 | 8 | 17 |
| 12 | 1 | 5 | 9 | 16 |
| 13 | 1 | 6 | 9 | 27 |
| 14 | 1 | 6 | 9 | 27 |
| 15 | 1 | 6 | 10 | 26 |
| 16 | 1 | 6 | 11 | 25 |

All differences are positive.

## Verification status

This is a complete natural-language proof candidate, but it is **not yet being
claimed as Lean verified**. The remaining formalization task is to kernel-check:

1. the Rosser--Schoenfeld bound `pi(x) > x/log x` for `x>=17` or import a
   sorry-free formal proof of it;
2. the odd-integer interval count;
3. the logarithmic comparison;
4. the 17 exact finite cases.

## Sources

- Zhi-Wei Sun, *Problems on combinatorial properties of primes*, Conjecture 2.6:
  https://arxiv.org/abs/1402.6641
- J. Barkley Rosser and Lowell Schoenfeld, *Approximate formulas for some
  functions of prime numbers*, Illinois J. Math. 6 (1962), 64--94.
