# Factoring the integer supplied by Dominic Dabish

The integer is
$$x=8193746205841170392658200302327406197
=7\cdot77621949530200343\cdot15079950701413453397.$$
All three factors are prime. The [Lean certificate](./PostedIntegerFactors.lean) verifies the multiplication, the elliptic-curve gcd, and primality. This record concerns the supplied integer. The [post by Tristan Lecourtois](https://x.com/tristanlecourt/status/2125763116017610869) gives the same integer and names a Weierstrass–Euler conjecture without specifying a proposition or a search algorithm. The method below reproduces the factorization.

## Derivation

Trial division by 7 returns quotient $N=1170535172263024341808314328903915171$ and remainder zero. Running Lenstra's elliptic-curve factorization method on $N$ gives a nontrivial gcd. In the run below the gcd operand was $552969141749355614110441482007206431$ and the gcd was $77621949530200343$. Exact division produced the other factor. This run is reproducible with SymPy 1.14.0.

```python
from math import gcd
from sympy.ntheory.ecm import ecm

x = 8193746205841170392658200302327406197
N, remainder = divmod(x, 7)
assert remainder == 0
found = sorted(ecm(N, B1=10_000, B2=1_000_000, max_curve=50, seed=1234))
p = gcd(N, 552969141749355614110441482007206431)
q, remainder = divmod(N, p)
assert remainder == 0
assert found == [p, q] == [77621949530200343, 15079950701413453397]
assert 7*p*q == x
print(7, p, q)
```

## Checking primality

The Lean proof applies Lucas's primality criterion recursively. For the prime $p=77621949530200343$ it uses $g=5$, and for $q=15079950701413453397$ it uses $g=2$. Their predecessors factor as
$$p-1=2\cdot161323\cdot240579302177,$$
$$q-1=2^2\cdot4057\cdot36781\cdot25264539697.$$
For each candidate $t$, the proof checks $g^{t-1}=1\bmod t$ and $g^{(t-1)/l}\ne1\bmod t$ for every prime divisor $l$ of $t-1$. This gives $g$ multiplicative order $t-1$ and forces $t$ to be prime. All prime divisors used in this test are checked recursively or by direct decision. Modular powers are evaluated by repeated squaring.

Use the repository's pinned Lean 4.33.1 toolchain and mathlib dependencies. From the repository root run the following.

```sh
lake exe cache get
lake env lean _certificates/posted-integer/PostedIntegerFactors.lean
```
