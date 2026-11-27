# Exact split-prime valuations at prime-power indices in A363410

For every prime $p\equiv1,3\pmod8$ and every integer $j\ge1$, the coefficient $B_n$ of $\sqrt{-2}$ in $\prod_{k=1}^{n}(1+k\sqrt{-2})$ satisfies
$$v_p(B_{p^j})=v_p((p^j)!)=\frac{p^j-1}{p-1}.$$
In particular, the proposed slope in [OEIS A363410](https://oeis.org/A363410) holds with an exact formula at every positive power of 3. This gives explicit indices attaining the universal factorial lower bound. The pointwise limit over all indices remains open.

**Proof.** Choose $t\in\mathbb Z_p^\times$ with $t^2=-2$ (quadratic reciprocity and Hensel lifting). Write $x=1/t$, $n=p^j$. Evaluating at the two roots and dividing by $n!$ gives
$$\frac{2t B_n}{n!}=t^n\binom{n+x}{n}-(-t)^n\binom{n-x}{n}.$$
Here the binomial polynomial is the falling factorial divided by $n!$. It maps $\mathbb Z_p$ into $\mathbb Z_p$: approximate a $p$-adic integer by nonnegative ordinary integers and use continuity of this fixed polynomial over $\mathbb Q_p$.

For $y\in\mathbb Z_p$ with digits $y_i$, we have $\binom{y}{p^j}\equiv y_j\pmod p$. For nonnegative integers $y$, take the coefficient of $X^{p^j}$ in $(1+X)^y\equiv\prod_i(1+X^{p^i})^{y_i}\pmod p$. The lower digits have total degree at most $p^j-1$, so only the linear term of the $j$th factor contributes. Approximation by the nonnegative digit truncations proves the same for all $p$-adic $y$.

Since $x$ is a unit, the zeroth digit of $-x$ is $p-x_0$, and its digits at $j\ge1$ are $p-1-x_j$. Adding $p^j$ to either number adds one to its $j$th digit modulo $p$. Thus the two binomial coefficients in the display reduce to $1+x_j$ and $1+(p-1-x_j)$. As $n$ is odd, their contributions add, giving
$$2t B_n/n!\equiv t^n\big((1+x_j)+(1+p-1-x_j)\big)\equiv t^n\pmod p.$$
This residue is a unit. Legendre's factorial formula finishes the proof. In fact $t^{p^j}\equiv t\pmod p$, so $B_{p^j}/(p^j)!\equiv1/2\pmod p$, independent of the square root.

**Reproduction.** The independent check below computes the original integer recurrence modulo $p^{v+1}$, enough to verify the stronger unit congruence. It uses neither $p$-adic roots nor binomial coefficients.

```python
def check_power(p, j):
    n = p**j
    v = (n-1)//(p-1)
    power = p**v
    modulus = power*p
    a, b, unit_factorial = 1, 0, 1
    for k in range(1, n+1):
        a, b = (a-2*k*b) % modulus, (b+k*a) % modulus
        u = k
        while u % p == 0:
            u //= p
        unit_factorial = unit_factorial*u % p
    assert b % power == 0
    assert (2*(b//power)-unit_factorial) % p == 0
    assert b != 0

count = 0
for p in (3,11,17,19,41):
    j = 1
    while p**j <= 7000:
        check_power(p,j)
        count += 1
        j += 1
print("Checked the unit congruence at", count, "prime-power indices.")
```
