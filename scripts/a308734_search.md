# OEIS A308734 bounded-exponent search

This note records reproducible computational evidence. It does **not** prove the unrestricted conjecture.

Compile the independent checker:

```sh
c++ -O3 -std=c++20 scripts/a308734_search.cpp -o /tmp/a308734_search
```

## Exact bounded searches

```sh
/tmp/a308734_search 1000000000 4
```

returns exactly six exceptions:

```text
580152487
690627031
727894543
730572295
750299695
906474175
```

Thus the tempting strengthening with `b,d <= 4` is false.

```sh
/tmp/a308734_search 1000000000 5
```

returns no exceptions. The checker enumerates all admissible restricted-square shifts and uses Fermat's exact two-square criterion for every residual.

## Explicit level-five witnesses

Each level-four exception has a representation using `d = 5`:

```text
580152487 = 1^2 + 3125^2 + 781^2 + 23870^2
690627031 = 2^2 + 3125^2 + 1831^2 + 26029^2
727894543 = 1^2 + 6250^2 + 589^2 + 26239^2
730572295 = 1^2 + 6250^2 + 13163^2 + 22765^2
750299695 = 1^2 + 6250^2 + 9115^2 + 25063^2
906474175 = 2^2 + 3125^2 + 8675^2 + 28661^2
```

Here `3125 = 5^5` and `6250 = 2 * 5^5`. All six integers are congruent to `7 mod 8`, agreeing with the structural reduction in `FormalConjectures/OEIS/308734Parity.lean` that forces the restricted powers of two to satisfy `a,c <= 1` in this residue class.

The six failures and six witnesses were also checked independently by direct trial factorization of each residual rather than by the sieve implementation in the C++ program.
