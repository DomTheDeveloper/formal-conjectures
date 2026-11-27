# Two 3-adic conjectures in OEIS A363412

Let $a(n)$ be the coefficient of $\sqrt{-3}$ in $\prod_{k=1}^n(1+k\sqrt{-3})$. The [FORMULA section of A363412](https://oeis.org/A363412) asks whether $3\nmid a(3m+1)$ and whether the valuations at $3m-1$ and $3m$ agree. Both follow from the exact formula
$$v_3(a(n))=v_3(n(n+1)/2)\qquad(n\ge1).$$
In particular $3\nmid a(3m+1)$ for $m\ge0$ and
$$v_3(a(3m-1))=v_3(a(3m))=1+v_3(m)\qquad(m\ge1).$$

**Earlier proofs.** The Omega Institute's trureturing project had already published Lean proofs of these two assertions, including the common valuation. This note gives a derivation from the general triangular-factor theorem. [Earlier proof records](https://www.trureturing.org/research/bala3634-valuations/) · [Their paired-valuation proof](https://www.trureturing.org/research/bala3634-paired-valuations/).

**Proof.** The previously [Lean-checked triangular-factor theorem](https://github.com/DomTheDeveloper/formal-conjectures/blob/1d1909cf4b4a24e6ae6f33284a1c46c038d8effd/_certificates/oeis-quadratic-products/QuadraticDivisors.lean) gives an integer $z$ with $a(n)=(n(n+1)/2)(1+3z)$ for each $n$. The last factor and 2 are units modulo 3. For $n=3m+1$, neither $n$ nor $n+1$ contains a factor of 3. For $n=3m-1$ and $n=3m$, the factor divisible by 3 in each product is precisely $3m$. This proves the two statements and the common-value formula. Index zero has $a(0)=0$ and is excluded from the valuation formula.

**Finite cross-check using the defining product.**

```python
def v3(x):
    assert x != 0
    count = 0
    while x % 3 == 0:
        count += 1
        x //= 3
    return count

a,b = 1,0
for n in range(1,3001):
    a,b = a-3*n*b,b+n*a
    assert v3(b) == v3(n*(n+1)//2)
    if n % 3 == 1:
        assert b % 3
    else:
        assert v3(b) == 1+v3((n+1)//3)
print("All three identities passed through index 3000.")
```
