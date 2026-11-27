# The factorial lower bound is rarely attained in A363410

Let $B_n$ denote [A363410](https://oeis.org/A363410) and fix a prime $p\equiv1,3\pmod8$. For every fixed integer $H\ge0$ the set
$$\{n\ge1 : v_p(B_n)-v_p(n!)\le H\}$$
has natural density zero. Thus the excess above the factorial lower bound tends to infinity in natural density, even though it is [exactly zero at every index $p^j$ for $j\ge1$](https://github.com/DomTheDeveloper/formal-conjectures/blob/c798dd83cda2044ec70652568d6854e61e613b58/_certificates/oeis-quadratic-products/SplitPrimePowers.md).

**Proof.** Fix a root $t\in\mathbb Z_p^\times$ of $t^2=-2$. Factor the quadratic product in the two embeddings to obtain $U_n=\prod_{k=1}^n(1+kt)$ and $V_n=\prod_{k=1}^n(1-kt)$, with $2tB_n=U_n-V_n$. The roots as functions of $k$ are $r=-1/t$ and $r=1/t$, respectively. For either sign write $r_j$ for the least nonnegative representative of $r$ modulo $p^j$. It is nonzero because $r$ is a unit. Among $1,\ldots,n$ there are exactly $\lfloor n/p^j\rfloor+\mathbf 1_{n\bmod p^j\ge r_j}$ factors divisible by $p^j$. After subtracting Legendre's formula, the valuation of this product minus $v_p(n!)$ is exactly
$$\sum_{j\ge1}\mathbf 1_{n\bmod p^j\ge r_j}.$$
The sum is finite because every contributing factor divides its nonzero norm in the $p$-adic sense.

Write the digits of $r$ as $d_i$. Infinitely many $d_i$ are smaller than $p-1$. Otherwise $r$ would be an ordinary negative integer by summing an eventual tail of digits $p-1$. This is impossible because $2r^2=-1$. Select any $L$ such positions $i$. Whenever the $i$th digit of $n$ is $p-1$, it strictly exceeds $d_i$, so $n\bmod p^{i+1}>r_{i+1}$ and gives one distinct contribution to the sum. In a complete system of residues modulo $p^{1+\max i}$ these $L$ digit events are independent, each with frequency $1/p$. Their count has the binomial distribution with parameters $L,1/p$. The upper natural density of indices where the excess is at most $H$ is therefore at most
$$p^{-L}\sum_{k=0}^{\min(H,L)}\binom Lk(p-1)^{L-k}.$$
For fixed $H$ this tends to zero as $L\to\infty$. This proves the claim separately for both embedded products. Since $2t$ is a unit, the excess for $B_n$ is at least the smaller of their two excesses; the union of the two exceptional sets has density zero.

**Exact finite check.** This exhausts complete blocks and verifies the displayed per-level identity for both branches independently of the density argument.

```python
def check(p, levels):
    q = p
    t = next(k for k in range(p) if (k*k+2) % p == 0)
    for _ in range(1, levels):
        t = next(t+i*q for i in range(p) if ((t+i*q)**2+2) % (p*q) == 0)
        q *= p
    for sign in (1,-1):
        product_value = factorial_value = 0
        roots = [(p**j, pow(-sign*t,-1,p**j)) for j in range(1,levels+1)]
        for n in range(1,q+1):
            product_value += sum((1+sign*n*t) % m == 0 for m,r in roots)
            factorial_value += sum(n % m == 0 for m,r in roots)
            assert product_value-factorial_value == sum(n % m >= r for m,r in roots)

check(3,8)
check(11,4)
check(17,3)
print("Both split branches passed every index in three complete residue blocks.")
```
