# A density-one slope theorem for split primes of OEIS A363410

Let $A_n+B_n\sqrt{-2}=\prod_{k=1}^n(1+k\sqrt{-2})$. The entry [A363410](https://oeis.org/A363410) predicts $v_p(B_n)/n\to 1/(p-1)$ for primes $p\equiv1,3\pmod8$. Here is a partial solution with a quantitative exceptional-set bound. All logarithms in big-O estimates may be taken to any fixed base.

**Theorem.** Fix any such prime and any $\epsilon>0$. Among $1\le n\le N$ at most $O_{p,\epsilon}((\log(2N))^2)$ indices satisfy $|v_p(B_n)-n/(p-1)|\ge\epsilon n$. Moreover $v_p(B_n)\ge v_p(n!)$ at every positive index and the ordinary lower limit of $v_p(B_n)/n$ equals $1/(p-1)$. In particular at $p=3$ the predicted slope is $1/2$ in natural density. The theorem leaves open the possibility of an infinite sparse set of upward deviations.

### 1. Bound the two split valuations

Quadratic reciprocity gives a nonzero square root of $-2$ modulo $p$. Hensel lifting gives $t\in\mathbb Z_p^\times$ with $t^2=-2$, since $p$ is odd. Put $U_n=A_n+tB_n$ and $V_n=A_n-tB_n$. For each sign these products have valuation
$$s_n^\pm=\sum_{j\ge1}\#\{1\le k\le n:1\pm kt\equiv0\pmod{p^j}\}.$$
Each level selects exactly one residue class, hence each count is either $\lfloor n/p^j\rfloor$ or $\lceil n/p^j\rceil$. Further, a contribution requires $p^j\mid1+2k^2$, by taking the product with the conjugate factor. No level beyond $L=\lfloor\log_p(1+2n^2)\rfloor$ contributes. Legendre's formula gives
$$v_p(n!)\le s_n^\pm\le v_p(n!)+L,\qquad s_n^\pm=n/(p-1)+O_p(\log(2n)).$$
The last estimate follows by summing the floors in Legendre's formula. Since $2t$ is a unit, $B_n=(U_n-V_n)/(2t)$ has valuation at least $v_p(n!)$. The coefficient is nonzero for $n>0$ by [the triangular-factor theorem](https://github.com/DomTheDeveloper/formal-conjectures/blob/1d1909cf4b4a24e6ae6f33284a1c46c038d8effd/_certificates/oeis-quadratic-products/QuadraticDivisors.lean). Alternatively one can use $v_p(0)=+\infty$ throughout the spacing argument. If $v_p(B_n)>s_n^+$, then $A_n=U_n-tB_n$ has valuation exactly $s_n^+$.

### 2. Nearby exceptional indices force a short product to have a large divisor

Work on an integer interval $X\le n<m<2X$. For sufficiently large $X$ depending on $p,\epsilon$, the lower bound rules out downward deviations of size $\epsilon n$. Suppose both endpoints have upward deviations of this size. Write
$$C+D\sqrt{-2}=\prod_{k=n+1}^{m}(1+k\sqrt{-2}),\qquad h=m-n.$$
Then $B_m=A_nD+B_nC$. Both $B_m$ and $B_nC$ have valuation at least $n/(p-1)+\epsilon n$. At the first endpoint $v_p(A_n)=s_n^+\le n/(p-1)+O_p(\log(2X))$. Subtract and divide to obtain
$$v_p(D)\ge\epsilon X-O_p(\log(2X)).$$

To turn this divisibility into a size bound one needs $D\ne0$. Indeed the complex argument of the block modulo $2\pi$ is $h\pi/2-\delta$, where
$$0<\delta=\sum_{k=n+1}^m\arctan(1/(k\sqrt2)) < h/((n+1)\sqrt2)<1<\pi/2.$$
For either parity of $h$ the argument is not a multiple of $\pi$. Also $|D|\le\prod_{k=n+1}^m\sqrt{1+2k^2}\le (3X)^h$ for $X\ge1$. Consequently
$$h\log_p(3X)\ge\log_p|D|\ge v_p(D)\ge\epsilon X-O_p(\log(2X)).$$

### 3. Count the exceptions

For sufficiently large $X$ the right-hand side is at least $\epsilon X/2$. Consecutive exceptional indices in $[X,2X)$ are separated by at least $\epsilon X/(2\log_p(3X))$. At most $1+2\log_p(3X)/\epsilon$ fit in the interval. Summing over $X=1,2,4,\ldots$ through $N$ proves the bound. The factorial lower bound gives the asserted lower limit from below, and the complement of each exceptional set has density one, giving the reverse inequality.

### Verification and scope

This is a written mathematical proof. An exact finite check below also tests the endpoint identity, block nonvanishing and size bound, the two split valuations, and the divisibility inequality before asymptotic estimates. It runs with standard Python. It is independent of the earlier million-term experiment.

```python
from math import factorial

def vp(x, p):
    if x == 0:
        return float("inf")
    v = 0
    while x % p == 0:
        x //= p
        v += 1
    return v

def check(p, bound):
    t = next(a for a in range(1, p) if (a*a+2) % p == 0)
    q = p
    while q <= 1+2*bound**2:
        t = next(t+i*q for i in range(p) if ((t+i*q)**2+2) % (p*q) == 0)
        q *= p
    coords = [(1, 0)]
    sp = sm = 0
    for n in range(1, bound+1):
        a, b = coords[-1]
        a, b = a-2*n*b, b+n*a
        coords.append((a, b))
        sp += vp(1+n*t, p)
        sm += vp(1-n*t, p)
        base = vp(factorial(n), p)
        for s in (sp, sm):
            assert base <= s and p**(s-base) <= 1+2*n*n
        assert b and vp(b,p) >= base
        if vp(b,p) > sp:
            assert vp(a,p) == sp
    for n in range(1, bound):
        c, d = 1, 0
        a, b = coords[n]
        for m in range(n+1, min(2*n, bound)+1):
            c, d = c-2*m*d, d+m*c
            bm = coords[m][1]
            assert bm == a*d+b*c
            assert d and abs(d) <= (3*n)**(m-n)
            if a:
                assert vp(d,p) >= min(vp(b,p),vp(bm,p))-vp(a,p)

for prime in (3,11,17,19,41):
    check(prime, 256)
print("Passed exact checks for five split primes through 256.")
```
